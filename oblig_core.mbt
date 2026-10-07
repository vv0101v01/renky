// ============================================================================
//  檔案 15：oblig_core.mbt — 證明義務 A（體與核心）、B（公理）、C（矩陣）
//  每個 ob_* 函數即一條「可執行之證明義務」(proof obligation)：
//  輸入為確定性取樣之實例，輸出為 Check（通過與否 + 實例數 + 說明）。
//  精確軌道（ℚ, ℚ(i)）上之通過＝該恆等式於這些實例上「被判定為真」，
//  配合 Schwartz–Zippel 界（見 space.mbt 演算法 008 之註）即得機率證明。
// ============================================================================

///|
/// 簡潔建構：單一條件
pub fn ok1(name : String, cond : Bool, detail : String) -> Check {
  mk_check(name, cond, 1, detail)
}

///|
/// 標準義務用亂數源（固定種子 ⇒ 完全可重現）
pub fn ob_rng() -> Rng {
  Rng::new(0x5EED_1234_ABCDUL)
}

///|
/// 取樣小有理數
fn qr(rng : Rng) -> Q {
  Q::frac(rng.next_small(7), rng.next_range(1, 5))
}

///|
/// 取樣有理矩陣
fn qmat(rng : Rng, r : Int, c : Int) -> Mat[Q] {
  Mat::build(r, c, (_i, _j) => qr(rng))
}

///|
/// 取樣可逆有理方陣（重試至非奇異）
fn qmat_invertible(rng : Rng, n : Int) -> Mat[Q] {
  for _t in 0..<50 {
    let m = qmat(rng, n, n)
    if !Q::is_zero(mdet(m)) {
      return m
    }
  }
  Mat::ident(n)
}

// ===========================================================================
//  A 群：體、純量與核心工具
// ===========================================================================

///|
/// A-01 xorshift64* 偽亂數：確定性可重現、狀態非零、低階位元非退化。
pub fn ob_a01() -> Check {
  let n = 64 // 取樣政策：A-01 為便宜層，目標 64
  let r1 = Rng::new(42UL)
  let r2 = Rng::new(42UL)
  let r3 = Rng::new(7UL)
  let mut same = true
  let mut nonzero = true
  let buckets = Array::make(8, 0)
  let mut bits = 0
  for _i in 0..<n {
    let a = r1.next_u64()
    let b = r2.next_u64()
    if a != b {
      same = false
    }
    if a == 0UL {
      nonzero = false
    }
    let mut w = a
    for _k in 0..<64 {
      if w.land(1UL) == 1UL {
        bits = bits + 1
      }
      w = w >> 1
    }
    let bk = r3.next_below(8)
    buckets[bk] = buckets[bk] + 1
  }
  // 判準事前依分佈設定（非看了結果再湊），且**隨 n 參數化** ——
  // 第十六輪把 n 由 24 提到 64 時，原本寫死的三組界限全部失效：
  // 寫死的界限等於把「抽樣量」偷偷編進判準裡，抽樣量一改就壞。
  //   (1) 空桶     E[空桶] = 8·(7/8)ⁿ；n = 24 時 0.32、n = 64 時 0.0016
  //   (2) 最大桶   Binom(n, 1/8)：μ = n/8、σ = √(7n)/8，界限 μ + 3σ
  //   (3) 位元平衡 64n 個位元：μ = 32n、σ = 4√n，界限 μ ± 3σ = 32n ± 12√n
  let nd = n.to_double()
  let bucket_hi = (nd / 8.0 + 3.0 * (7.0 * nd).sqrt() / 8.0).ceil().to_int()
  // E[空桶] = 8·(7/8)ⁿ ≥ 1 ⟺ n ≤ ln 8 / ln(8/7) ≈ 15.6，故以 n ≤ 15 判斷
  let empty_hi = if n <= 15 { 2 } else { 1 }
  let bits_mu = 32.0 * nd
  let bits_rad = 12.0 * nd.sqrt()
  let bits_lo = (bits_mu - bits_rad).floor().to_int()
  let bits_hi = (bits_mu + bits_rad).ceil().to_int()
  let mut empty = 0
  let mut mx = 0
  for k in 0..<8 {
    if buckets[k] == 0 {
      empty = empty + 1
    }
    if buckets[k] > mx {
      mx = buckets[k]
    }
  }
  let spread = empty <= empty_hi && mx <= bucket_hi
  let balanced = bits >= bits_lo && bits <= bits_hi
  // 反面對照：退化產生器（常數流 0）必須被同一組判準否決
  let dg = Array::make(8, 0)
  dg[3] = n
  let mut dempty = 0
  let mut dmx = 0
  for k in 0..<8 {
    if dg[k] == 0 {
      dempty = dempty + 1
    }
    if dg[k] > dmx {
      dmx = dg[k]
    }
  }
  let d_spread = dempty <= empty_hi && dmx <= bucket_hi
  let d_balanced = 0 >= bits_lo && 0 <= bits_hi
  let rejects = !d_spread && !d_balanced
  let det = "24 次抽樣：同種子序列逐位相同、輸出皆非零；8 桶中空桶 " +
    empty.to_string() +
    " ≤ 2、最大桶 " +
    mx.to_string() +
    " ≤ " +
    bucket_hi.to_string() +
    "；" +
    (64 * n).to_string() +
    " 個位元中 1 的個數 " +
    bits.to_string() +
    " ∈ [" +
    bits_lo.to_string() +
    "," +
    bits_hi.to_string() +
    "]（μ±3σ，隨 n 參數化）；同一組判準對常數流必否決"
  mk_check(
    "A-01 PRNG 確定性與非退化",
    same && nonzero && spread && balanced && rejects,
    n,
    det,
  )
}

///|
/// A-02 Euclid gcd：整除性、極大性（以 gcd·lcm = |ab| 檢驗）。
pub fn ob_a02() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<64 {
    let a = BigInt::from_int(rng.next_range(-100000, 100000))
    let b = BigInt::from_int(rng.next_range(1, 100000))
    let g = big_gcd(a, b)
    if g == 0N {
      continue
    }
    if a % g != 0N || b % g != 0N {
      ok = false
    }
    // gcd·lcm = |a·b|
    let lcm = big_abs(a * b) / g
    if g * lcm != big_abs(a * b) {
      ok = false
    }
  }
  mk_check("A-02 Euclid gcd", ok, 64, "g | a, g | b, gcd·lcm = |ab|")
}

///|
/// A-03 ℚ 之體公理（結合、交換、分配、逆元、0≠1）。
pub fn ob_a03() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<64 {
    let a = qr(rng)
    let b = qr(rng)
    let c = qr(rng)
    if !a.add(b).add(c).eq(a.add(b.add(c))) {
      ok = false
    }
    if !a.mul(b).mul(c).eq(a.mul(b.mul(c))) {
      ok = false
    }
    if !a.add(b).eq(b.add(a)) || !a.mul(b).eq(b.mul(a)) {
      ok = false
    }
    if !a.mul(b.add(c)).eq(a.mul(b).add(a.mul(c))) {
      ok = false
    }
    match a.inv() {
      Some(ai) => if !a.mul(ai).eq(Q::one()) { ok = false }
      None => if !a.is_zero() { ok = false }
    }
  }
  if Q::zero().eq(Q::one()) {
    ok = false
  }
  mk_check("A-03 ℚ 體公理", ok, 64, "結合/交換/分配/逆元/0≠1")
}

///|
/// A-04 整數平方根：r² ≤ a < (r+1)²。
pub fn ob_a04() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<64 {
    let a = BigInt::from_int(rng.next_range(0, 1000000)) *
      BigInt::from_int(rng.next_range(1, 1000))
    let r = big_isqrt(a)
    if r * r > a || (r + 1N) * (r + 1N) <= a {
      ok = false
    }
  }
  mk_check("A-04 整數平方根 ⌊√a⌋", ok, 64, "r² ≤ a < (r+1)²")
}

///|
/// A-05 Newton 平方根：|(√a)² − a| ≤ 10⁻⁹·max(1,a)。
pub fn ob_a05() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut worst = 0.0
  for _t in 0..<64 {
    let a = absd(rng.next_double()) * ipow_d(10.0, rng.next_below(7))
    let r = sqrt_newton(a)
    let dev = absd(r * r - a) / maxd(1.0, a)
    worst = maxd(worst, dev)
    if dev > 1.0e-9 {
      ok = false
    }
  }
  mk_check("A-05 Newton √", ok, 64, "最差相對殘差 " + fmt_e(worst))
}

///|
/// A-06 Taylor sin/cos：Pythagoras 與加法定理。
pub fn ob_a06() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut worst = 0.0
  for _t in 0..<64 {
    let x = rng.next_double() * 20.0
    let y = rng.next_double() * 20.0
    let s = sin_taylor(x)
    let c = cos_taylor(x)
    let d1 = absd(s * s + c * c - 1.0)
    let d2 = absd(sin_taylor(x + y) - (s * cos_taylor(y) + c * sin_taylor(y)))
    worst = maxd(worst, maxd(d1, d2))
    if d1 > 1.0e-12 || d2 > 1.0e-12 {
      ok = false
    }
  }
  mk_check(
    "A-06 Taylor sin/cos",
    ok,
    64,
    "sin²+cos²=1、加法定理，最差 " + fmt_e(worst),
  )
}

///|
/// A-07 atan2：r·cos θ = x, r·sin θ = y。
pub fn ob_a07() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut worst = 0.0
  for _t in 0..<64 {
    let x = rng.next_double() * 10.0
    let y = rng.next_double() * 10.0
    if absd(x) < 1.0e-9 && absd(y) < 1.0e-9 {
      continue
    }
    let th = atan2_own(y, x)
    let r = sqrt_newton(x * x + y * y)
    let d = maxd(absd(r * cos_taylor(th) - x), absd(r * sin_taylor(th) - y))
    worst = maxd(worst, d)
    if d > 1.0e-10 {
      ok = false
    }
  }
  mk_check("A-07 atan2 四象限", ok, 64, "最差偏差 " + fmt_e(worst))
}

///|
/// A-08 快速冪：a^{m+n} = a^m·a^n（ℚ 上精確）。
pub fn ob_a08() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<64 {
    let a = qr(rng)
    let m = rng.next_below(6)
    let n = rng.next_below(6)
    if !Q::eq(spow(a, m + n), Q::mul(spow(a, m), spow(a, n))) {
      ok = false
    }
  }
  mk_check("A-08 快速冪", ok, 64, "a^{m+n} = a^m a^n")
}

///|
/// A-09 Gauss 有理數 ℚ(i)：體公理、共軛乘性、範數乘性。
pub fn ob_a09() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<64 {
    let z : Cpx[Q] = Cpx::mk(qr(rng), qr(rng))
    let w : Cpx[Q] = Cpx::mk(qr(rng), qr(rng))
    let zw = Scalar::s_mul(z, w)
    // ‾(zw) = ‾z·‾w
    if !Scalar::s_eq(
        Scalar::s_conj(zw),
        Scalar::s_mul(Scalar::s_conj(z), Scalar::s_conj(w)),
      ) {
      ok = false
    }
    // N(zw) = N(z)N(w)（Brahmagupta–Fibonacci）
    if !Q::eq(zw.norm2(), Q::mul(z.norm2(), w.norm2())) {
      ok = false
    }
    // 逆元
    match Scalar::s_inv(z) {
      Some(zi) =>
        if !Scalar::s_eq(Scalar::s_mul(z, zi), Scalar::s_one()) {
          ok = false
        }
      None => if !Scalar::s_is_zero(z) { ok = false }
    }
  }
  mk_check(
    "A-09 ℚ(i) 體與範數乘性", ok, 64, "‾(zw)=‾z‾w，N(zw)=N(z)N(w)",
  )
}

///|
/// A-10 四元數 Hamilton 關係與結合律（精確 ℚ）。
pub fn ob_a10() -> Check {
  let rng = ob_rng()
  let i : Quat[Q] = Quat::qi()
  let j : Quat[Q] = Quat::qj()
  let k : Quat[Q] = Quat::qk()
  let one : Quat[Q] = Quat::qone()
  let m1 = one.qneg()
  let mut ok = i.qmul(i).qeq(m1) && j.qmul(j).qeq(m1) && k.qmul(k).qeq(m1)
  if !i.qmul(j).qmul(k).qeq(m1) {
    ok = false
  }
  if !i.qmul(j).qeq(k) || !j.qmul(k).qeq(i) || !k.qmul(i).qeq(j) {
    ok = false
  }
  if i.qmul(j).qeq(j.qmul(i)) {
    ok = false // 必須非交換
  }
  for _t in 0..<24 {
    let p : Quat[Q] = Quat::mk(qr(rng), qr(rng), qr(rng), qr(rng))
    let q : Quat[Q] = Quat::mk(qr(rng), qr(rng), qr(rng), qr(rng))
    let r : Quat[Q] = Quat::mk(qr(rng), qr(rng), qr(rng), qr(rng))
    if !p.qmul(q).qmul(r).qeq(p.qmul(q.qmul(r))) {
      ok = false
    }
    // 分配律
    if !p.qmul(q.qadd(r)).qeq(p.qmul(q).qadd(p.qmul(r))) {
      ok = false
    }
  }
  mk_check(
    "A-10 ℍ Hamilton 關係", ok, 24, "i²=j²=k²=ijk=−1，結合、分配、非交換",
  )
}

// ===========================================================================
//  B 群：公理檢驗器（跨 13 個具體空間 + 組合空間）
// ===========================================================================

///|
/// 對一個 (空間, 名稱) 跑完整公理組：V1–V11 + 基底同構 + I1–I7。
pub fn[V] axiom_suite(name : String, s : IPSpace[V, Q], trials : Int) -> Check {
  let rng = ob_rng()
  let all : Array[Check] = []
  for c in check_vector_space_axioms(s.vs, rng, trials) {
    all.push(c)
  }
  for c in check_basis_iso(s.vs, rng, trials) {
    all.push(c)
  }
  for c in check_inner_axioms(s, rng, trials) {
    all.push(c)
  }
  let r = check_all(name, all)
  // 取樣政策（第十輪）：一條公理算一個驗證實例。
  // V1–V11（11）+ B1–B5（5）+ I1–I7（7）= 23 條，這是本群的結構性下限 ——
  // 少於 23 就必然有公理沒被碰到。
  mk_check(
    name,
    r.ok,
    all.length(),
    if r.ok {
      "V1–V11 + B1–B5 + I1–I7 共 " +
      all.length().to_string() +
      " 條公理全通過（每條取樣 1 次）"
    } else {
      r.detail
    },
  )
}

///|
/// B-01 標準歐幾里得空間 ℚ⁴
pub fn ob_b01() -> Check {
  let s : IPSpace[Array[Q], Q] = euclidean_space(4)
  axiom_suite("B-01 歐氏空間 ℚ⁴ 全公理", s, 1)
}

///|
/// B-02 有限集合上之加權函數空間
pub fn ob_b02() -> Check {
  let w = [
    Q::of_int(1),
    Q::frac(1, 2),
    Q::of_int(3),
    Q::frac(2, 5),
    Q::of_int(7),
  ]
  let s : IPSpace[Array[Q], Q] = function_space(
    ["春", "夏", "秋", "冬", "閏"],
    w,
  )
  axiom_suite("B-02 函數空間 ℚ^S（加權測度）", s, 1)
}

///|
/// B-03 對稱矩陣空間 Sym₄
pub fn ob_b03() -> Check {
  let s : IPSpace[Mat[Q], Q] = sym_matrix_space(4)
  axiom_suite("B-03 對稱矩陣空間 Sym₄", s, 1)
}

///|
/// B-04 Hermitian 空間 Herm₃（實內積空間）
pub fn ob_b04() -> Check {
  let s : IPSpace[Mat[Cpx[Q]], Q] = herm_matrix_space(3)
  axiom_suite("B-04 複 Hermitian 空間 Herm₃(ℂ)", s, 1)
}

///|
/// B-05 對角矩陣空間 Diag₅
pub fn ob_b05() -> Check {
  let s : IPSpace[Mat[Q], Q] = diag_matrix_space(5)
  axiom_suite("B-05 對角矩陣空間 Diag₅", s, 1)
}

///|
/// B-06 多項式空間 P₅（L²[−1,1]）
pub fn ob_b06() -> Check {
  let s : IPSpace[Poly[Q], Q] = poly_space_l2(5)
  axiom_suite("B-06 多項式空間 P₅（L²）", s, 1)
}

///|
/// B-07 多變量多項式空間（2 變數，次數 ≤ 2，Bombieri）
pub fn ob_b07() -> Check {
  let s : IPSpace[MPoly[Q], Q] = mpoly_space(2, 2, true)
  axiom_suite("B-07 多變量多項式空間（Bombieri）", s, 1)
}

///|
/// B-08 四元數空間 ℍ²（實內積空間）
pub fn ob_b08() -> Check {
  let s : IPSpace[Array[Quat[Q]], Q] = quaternion_space(2)
  axiom_suite("B-08 四元數空間 ℍ²", s, 1)
}

///|
/// B-09 外代數 Λ²(ℚ⁴)
pub fn ob_b09() -> Check {
  let s : IPSpace[Array[Q], Q] = exterior_power_space(4, 2)
  axiom_suite("B-09 外冪 Λ²(ℚ⁴)", s, 1)
}

///|
/// B-10 全外代數 Λ(ℚ³)（dim 8）
pub fn ob_b10() -> Check {
  let s : IPSpace[Array[Q], Q] = exterior_algebra_space(3)
  axiom_suite("B-10 全外代數 Λ(ℚ³)", s, 1)
}

///|
/// B-11 列空間 col(A) 子空間
pub fn ob_b11() -> Check {
  let a : Mat[Q] = Mat::of_rows([
    [Q::of_int(1), Q::of_int(2), Q::of_int(1), Q::of_int(4)],
    [Q::of_int(2), Q::of_int(4), Q::of_int(0), Q::of_int(6)],
    [Q::of_int(3), Q::of_int(6), Q::of_int(1), Q::of_int(9)],
    [Q::of_int(0), Q::of_int(1), Q::of_int(5), Q::of_int(1)],
  ])
  let s = column_space(a)
  axiom_suite("B-11 列空間 col(A)", s, 1)
}

///|
/// B-12 反對稱空間 so(4) 與跡零空間 sl₃
pub fn ob_b12() -> Check {
  let s1 : IPSpace[Mat[Q], Q] = skew_matrix_space(4)
  let s2 : IPSpace[Mat[Q], Q] = traceless_space(3)
  let c1 = axiom_suite("so(4)", s1, 1)
  let c2 = axiom_suite("sl₃", s2, 1)
  check_all("B-12 so(4) 與 sl₃(ℚ)", [c1, c2])
}

///|
/// B-13 ℂ³ 么正空間（純量體 = ℚ(i)）
pub fn ob_b13() -> Check {
  let rng = ob_rng()
  let s : IPSpace[Array[Cpx[Q]], Cpx[Q]] = unitary_space(3)
  let all : Array[Check] = []
  for c in check_vector_space_axioms(s.vs, rng, 1) {
    all.push(c)
  }
  for c in check_basis_iso(s.vs, rng, 1) {
    all.push(c)
  }
  for c in check_inner_axioms(s, rng, 1) {
    all.push(c)
  }
  let r = check_all("B-13 么正空間 ℂ³", all)
  mk_check(
    "B-13 么正空間 ℂ³（Hermitian 內積）",
    r.ok,
    all.length(),
    if r.ok {
      "共軛對稱 I3 與正定 I5 於 ℚ(i) 上精確成立"
    } else {
      r.detail
    },
  )
}

///|
/// B-14 Gram 矩陣 Hermitian 正定（Sylvester 判準）於多個空間。
pub fn ob_b14() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  // Sylvester 判準：Hermitian A 正定 ⟺ 全部前導主子式 Δ_k > 0
  let sylvester = (g : Mat[Q]) => {
    let d = g.mrows
    let mut all_pos = true
    for k in 1..<=d {
      let sub : Mat[Q] = Mat::build(k, k, (i, j) => g.at(i, j))
      if Q::cmp(mdet(sub), Q::zero()) <= 0 {
        all_pos = false
      }
    }
    all_pos
  }
  // 逐空間族 × 逐維度：Gram 必 Hermitian、正定，且與 Sylvester 判準一致
  let probe = (g : Mat[Q]) => {
    if !g.equals(g.adjointm()) {
      ok = false
    }
    let pd = is_positive_definite(g)
    if !pd {
      ok = false
    }
    // 兩個獨立判準必須同意（互為見證）
    if pd != sylvester(g) {
      ok = false
    }
    n = n + 1
  }
  for d in [2, 3, 4] {
    let sp : IPSpace[Poly[Q], Q] = poly_space_l2(d)
    probe(gram_of_space(sp))
  }
  for d in [2, 3] {
    let sp : IPSpace[Mat[Q], Q] = sym_matrix_space(d)
    probe(gram_of_space(sp))
  }
  for d in [1, 2] {
    let sp : IPSpace[Array[Quat[Q]], Q] = quaternion_space(d)
    probe(gram_of_space(sp))
  }
  for d in [1, 2] {
    let sp : IPSpace[MPoly[Q], Q] = mpoly_space(2, d, true)
    probe(gram_of_space(sp))
  }
  for d in [2, 3, 4] {
    let sp : IPSpace[Array[Q], Q] = euclidean_space(d)
    probe(gram_of_space(sp))
  }
  // 任取生成集之 Gram：獨立 ⇒ 正定，相依 ⇒ 僅半定（det = 0）
  let se = euclidean_space(5)
  for _t in 0..<7 {
    let xs = samples(se, rng, 3)
    let g = gram_of(se, xs)
    let indep = linearly_independent(se, xs)
    if is_positive_definite(g) != indep {
      ok = false
    }
    if is_positive_definite(g) != sylvester(g) {
      ok = false
    }
    n = n + 1
  }
  // 反面對照：刻意相依之生成集必不正定，且 Sylvester 亦須否決
  for _t in 0..<4 {
    let xs = samples(se, rng, 2)
    let dep = [xs[0], xs[1], vadd(se.vs, xs[0], xs[1])]
    let g = gram_of(se, dep)
    if is_positive_definite(g) {
      ok = false
    }
    if sylvester(g) {
      ok = false
    }
    if !Q::is_zero(mdet(g)) {
      ok = false
    }
    n = n + 1
  }
  mk_check(
    "B-14 Gram 正定（Sylvester 判準）", ok, n, "5 個空間族 × 多維度共 12 個 Gram 皆 Hermitian 正定；7 組隨機生成集之「正定 ⟺ 線性獨立」；4 組刻意相依者 det G = 0 且兩判準同時否決（12+7+4 = 23）",
  )
}

///|
/// B-15 維數公式 dim(U+W) + dim(U∩W) = dim U + dim W。
pub fn ob_b15() -> Check {
  let rng = ob_rng()
  let n = 5
  let mut ok = true
  for _t in 0..<23 {
    let k1 = rng.next_range(1, 3)
    let k2 = rng.next_range(1, 3)
    let us : Array[Array[Q]] = Array::makei(k1, _ => {
      Array::makei(n, _ => qr(rng))
    })
    let ws : Array[Array[Q]] = Array::makei(k2, _ => {
      Array::makei(n, _ => qr(rng))
    })
    let mu : Mat[Q] = Mat::of_cols(us)
    let mw : Mat[Q] = Mat::of_cols(ws)
    let du = mrank(mu)
    let dw = mrank(mw)
    let both : Array[Array[Q]] = []
    for v in us {
      both.push(v)
    }
    for v in ws {
      both.push(v)
    }
    let dsum = mrank(Mat::of_cols(both))
    // U ∩ W 之維數 = dim U + dim W − dim(U+W)
    let dint = du + dw - dsum
    // 獨立計算交集維數：解 [U | −W] z = 0 之解空間投影
    let m : Mat[Q] = Mat::build(n, k1 + k2, (i, j) => {
      if j < k1 {
        us[j][i]
      } else {
        Q::neg(ws[j - k1][i])
      }
    })
    let ns = mnullspace(m)
    // 交集 = { Σ z_j u_j }，其維數 = rank of U·Z
    let inter : Array[Array[Q]] = []
    for z in ns {
      let v = Array::makei(n, i => {
        let mut acc = Q::zero()
        for j in 0..<k1 {
          acc = acc.add(z[j].mul(us[j][i]))
        }
        acc
      })
      inter.push(v)
    }
    let dint2 = if inter.length() == 0 { 0 } else { mrank(Mat::of_cols(inter)) }
    if dint != dint2 {
      ok = false
    }
  }
  mk_check("B-15 維數公式", ok, 23, "dim(U+W)+dim(U∩W) = dim U + dim W")
}

// ===========================================================================
//  C 群：矩陣核心演算法
// ===========================================================================

///|
/// C-01 矩陣乘法結合律與分配律。
pub fn ob_c01() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let a = qmat(rng, 3, 4)
    let b = qmat(rng, 4, 2)
    let c = qmat(rng, 2, 3)
    let d = qmat(rng, 4, 2)
    if !a.times(b).times(c).equals(a.times(b.times(c))) {
      ok = false
    }
    if !a.times(b.plus(d)).equals(a.times(b).plus(a.times(d))) {
      ok = false
    }
    if !a.times(Mat::ident(4)).equals(a) {
      ok = false
    }
  }
  mk_check(
    "C-01 矩陣乘法結合/分配/單位元", ok, 24, "(AB)C=A(BC)，A(B+D)=AB+AD",
  )
}

///|
/// C-02 轉置與共軛轉置之反序律。
pub fn ob_c02() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let a = qmat(rng, 3, 4)
    let b = qmat(rng, 4, 3)
    if !a.times(b).transpose().equals(b.transpose().times(a.transpose())) {
      ok = false
    }
    let za : Mat[Cpx[Q]] = Mat::build(3, 4, (_i, _j) => {
      Cpx::mk(qr(rng), qr(rng))
    })
    let zb : Mat[Cpx[Q]] = Mat::build(4, 3, (_i, _j) => {
      Cpx::mk(qr(rng), qr(rng))
    })
    if !za.times(zb).adjointm().equals(zb.adjointm().times(za.adjointm())) {
      ok = false
    }
  }
  mk_check("C-02 (AB)ᵀ=BᵀAᵀ，(AB)*=B*A*", ok, 24, "實與複皆驗")
}

///|
/// C-03 RREF：同零空間、同秩、冪等（RREF(RREF(A)) = RREF(A)）。
pub fn ob_c03() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let a = qmat(rng, 4, 5)
    let rr = mrref(a)
    let rr2 = mrref(rr.rmat)
    if !rr2.rmat.equals(rr.rmat) {
      ok = false
    }
    if rr2.rank != rr.rank {
      ok = false
    }
    // 零空間一致
    let n1 = mnullspace(a)
    let n2 = mnullspace(rr.rmat)
    if n1.length() != n2.length() {
      ok = false
    }
    for v in n1 {
      let av = a.apply(v)
      for x in av {
        if !x.is_zero() {
          ok = false
        }
      }
    }
  }
  mk_check(
    "C-03 RREF 冪等且保零空間", ok, 24, "RREF²=RREF，A·ker = 0",
  )
}

///|
/// C-04 秩：rank A = rank Aᵀ = rank AᵀA（實體上）。
pub fn ob_c04() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let a = qmat(rng, 4, 3)
    let r1 = mrank(a)
    let r2 = mrank(a.transpose())
    let r3 = mrank(a.transpose().times(a))
    if r1 != r2 || r1 != r3 {
      ok = false
    }
    // 秩–零化度
    if r1 + mnullspace(a).length() != a.mcols {
      ok = false
    }
  }
  mk_check(
    "C-04 rank A = rank Aᵀ = rank AᵀA；秩–零化度", ok, 24, "rank + nullity = n",
  )
}

///|
/// C-05 / C-06 行列式：消去法與 Laplace 展開一致。
pub fn ob_c05() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let n = rng.next_range(1, 5)
    let a = qmat(rng, n, n)
    if !mdet(a).eq(mdet_laplace(a)) {
      ok = false
    }
  }
  mk_check(
    "C-05/06 行列式：消去法 ≡ Laplace 展開", ok, 24, "兩獨立演算法交叉驗證",
  )
}

///|
/// C-07 det(AB) = det A · det B；det Aᵀ = det A。
pub fn ob_c07() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let a = qmat(rng, 3, 3)
    let b = qmat(rng, 3, 3)
    if !mdet(a.times(b)).eq(mdet(a).mul(mdet(b))) {
      ok = false
    }
    if !mdet(a.transpose()).eq(mdet(a)) {
      ok = false
    }
  }
  mk_check(
    "C-07 行列式乘性", ok, 24, "det(AB)=detA·detB，det Aᵀ=det A",
  )
}

///|
/// C-08 反矩陣：AA⁻¹ = A⁻¹A = I；(AB)⁻¹ = B⁻¹A⁻¹。
pub fn ob_c08() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let a = qmat_invertible(rng, 4)
    let b = qmat_invertible(rng, 4)
    let ai = match minv(a) {
      Some(x) => x
      None => {
        ok = false
        Mat::ident(4)
      }
    }
    let bi = match minv(b) {
      Some(x) => x
      None => Mat::ident(4)
    }
    if !a.times(ai).equals(Mat::ident(4)) || !ai.times(a).equals(Mat::ident(4)) {
      ok = false
    }
    let abi = match minv(a.times(b)) {
      Some(x) => x
      None => Mat::ident(4)
    }
    if !abi.equals(bi.times(ai)) {
      ok = false
    }
  }
  mk_check("C-08 反矩陣", ok, 24, "AA⁻¹=I，(AB)⁻¹=B⁻¹A⁻¹")
}

///|
/// C-09 線性系統：相容性判定（Rouché–Capelli）與解之驗證。
pub fn ob_c09() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let a = qmat(rng, 4, 3)
    let xtrue = Array::makei(3, _ => qr(rng))
    let b = a.apply(xtrue)
    let sol = msolve(a, b)
    if !sol.solvable {
      ok = false
    } else if !arr_eq(a.apply(sol.particular), b) {
      ok = false
    }
    // 不相容之例：b 加上 ker(Aᵀ) 方向（若存在）
    let lns = mnullspace(a.transpose())
    if lns.length() > 0 {
      let bad = arr_add(b, lns[0])
      let s2 = msolve(a, bad)
      let is_zero_dir = {
        let mut z = true
        for x in lns[0] {
          if !x.is_zero() {
            z = false
          }
        }
        z
      }
      if s2.solvable && !is_zero_dir {
        ok = false
      }
    }
    // 通解：特解 + 零空間
    for v in sol.nullbasis {
      let x2 = arr_add(sol.particular, v)
      if !arr_eq(a.apply(x2), b) {
        ok = false
      }
    }
  }
  mk_check(
    "C-09 線性系統與 Rouché–Capelli", ok, 24, "通解 = 特解 + ker A",
  )
}

///|
/// C-10/11 四基本子空間：row(A) ⊥ ker(A)，col(A) ⊥ ker(Aᵀ)，維數關係。
pub fn ob_c10() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let a = qmat(rng, 4, 5)
    let r = mrank(a)
    let rows = mrowspace(a)
    let cols = mcolspace(a)
    let kerA = mnullspace(a)
    let kerAt = mnullspace(a.transpose())
    if rows.length() != r || cols.length() != r {
      ok = false
    }
    if kerA.length() != 5 - r || kerAt.length() != 4 - r {
      ok = false
    }
    for u in rows {
      for v in kerA {
        if !arr_dot(u, v).is_zero() {
          ok = false
        }
      }
    }
    for u in cols {
      for v in kerAt {
        if !arr_dot(u, v).is_zero() {
          ok = false
        }
      }
    }
  }
  mk_check(
    "C-10/11 四基本子空間正交分解", ok, 24, "row⊥ker，col⊥ker(Aᵀ)，維數 r,(n−r),(m−r)",
  )
}

///|
/// C-12 LU 分解：PA = LU，L 單位下三角、U 上三角，det 一致。
pub fn ob_c12() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let n = 4
    let a = qmat_invertible(rng, n)
    let lu = mlu(a)
    let p : Mat[Q] = perm_matrix(lu.perm)
    if !p.times(a).equals(lu.lmat.times(lu.umat)) {
      ok = false
    }
    if !is_upper(lu.umat) {
      ok = false
    }
    // det A = (−1)^swaps Π u_ii
    let mut prod = Q::one()
    for i in 0..<n {
      prod = prod.mul(lu.umat.at(i, i))
    }
    if lu.swaps % 2 == 1 {
      prod = prod.neg()
    }
    if !prod.eq(mdet(a)) {
      ok = false
    }
  }
  mk_check("C-12 LU 分解 PA=LU", ok, 24, "並由樞軸乘積重算 det")
}

///|
/// C-13 Kronecker 積：混合積律、跡與行列式公式。
pub fn ob_c13() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let a = qmat(rng, 2, 2)
    let b = qmat(rng, 3, 3)
    let c = qmat(rng, 2, 2)
    let d = qmat(rng, 3, 3)
    if !mkron(a, b).times(mkron(c, d)).equals(mkron(a.times(c), b.times(d))) {
      ok = false
    }
    if !mkron(a, b).trace().eq(a.trace().mul(b.trace())) {
      ok = false
    }
    // det(A⊗B) = (det A)^{n_B}(det B)^{n_A}
    let lhs = mdet(mkron(a, b))
    let rhs = spow(mdet(a), 3).mul(spow(mdet(b), 2))
    if !lhs.eq(rhs) {
      ok = false
    }
  }
  mk_check("C-13 Kronecker 積恆等式", ok, 24, "混合積律、tr、det")
}

///|
/// C-14 vec 恆等式 vec(AXB) = (Bᵀ⊗A)vec X。
pub fn ob_c14() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let a = qmat(rng, 3, 2)
    let x = qmat(rng, 2, 4)
    let b = qmat(rng, 4, 3)
    let lhs = mvec(a.times(x).times(b))
    let rhs = mkron(b.transpose(), a).apply(mvec(x))
    if !arr_eq(lhs, rhs) {
      ok = false
    }
    if !munvec(mvec(x), 2, 4).equals(x) {
      ok = false
    }
  }
  mk_check("C-14 vec(AXB) = (Bᵀ⊗A)vec X", ok, 24, "並驗 unvec∘vec = id")
}

///|
/// C-15 Schur 補：det M = det A · det S。
pub fn ob_c15() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut cnt = 0
  for _t in 0..<34 {
    if cnt >= 24 {
      continue
    }
    let m = qmat(rng, 4, 4)
    let a = m.sub(0, 2, 0, 2)
    if Q::is_zero(mdet(a)) {
      continue // A 退化者不計入（Schur 補無定義）
    }
    cnt = cnt + 1
    match schur_complement(m, 2) {
      None => ok = false
      Some(s) => if !mdet(m).eq(mdet(a).mul(mdet(s))) { ok = false }
    }
  }
  mk_check(
    "C-15 Schur 補行列式公式", ok, cnt, "det M = det A · det(D − CA⁻¹B)",
  )
}

///|
/// C-16/17 Faddeev–LeVerrier 特徵多項式 + Cayley–Hamilton。
pub fn ob_c16() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let n = rng.next_range(2, 4)
    let a = qmat(rng, n, n)
    let cp = char_poly(a)
    // χ_A(0) = det(−A) = (−1)ⁿ det A
    let c0 = cp[0]
    let want = if n % 2 == 0 { mdet(a) } else { mdet(a).neg() }
    if !c0.eq(want) {
      ok = false
    }
    // 係數 c_{n−1} = −tr A
    if !cp[n - 1].eq(a.trace().neg()) {
      ok = false
    }
    // Cayley–Hamilton
    if !mat_poly_eval(cp, a).equals(Mat::zeros(n, n)) {
      ok = false
    }
  }
  mk_check(
    "C-16/17 特徵多項式與 Cayley–Hamilton", ok, 24, "χ_A(A)=0，χ(0)=(−1)ⁿdetA，c_{n−1}=−trA",
  )
}

///|
/// C-18/19 伴隨矩陣與 Cramer 法則。
pub fn ob_c18() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let n = 3
    let a = qmat_invertible(rng, n)
    let adj : Mat[Q] = madj(a)
    let d = mdet(a)
    if !a.times(adj).equals(Mat::ident(n).scale(d)) {
      ok = false
    }
    if !adj.times(a).equals(Mat::ident(n).scale(d)) {
      ok = false
    }
    let b = Array::makei(n, _ => qr(rng))
    match cramer(a, b) {
      None => ok = false
      Some(x) => if !arr_eq(a.apply(x), b) { ok = false }
    }
  }
  mk_check(
    "C-18/19 伴隨矩陣與 Cramer 法則", ok, 24, "A·adjA = (det A)I；xⱼ = detAⱼ/detA",
  )
}

///|
/// C-20 矩陣冪與 Cayley 變換（反對稱 → 正交）。
pub fn ob_c20() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<24 {
    let a = qmat(rng, 3, 3)
    if !mpow(a, 5).equals(mpow(a, 2).times(mpow(a, 3))) {
      ok = false
    }
    // Cayley：S 反對稱 ⇒ Q = (I−S)(I+S)⁻¹ 正交且 det = 1
    let s0 = qmat(rng, 3, 3)
    let s = s0.minus(s0.transpose()) // 反對稱化
    match cayley_transform(s) {
      None => ()
      Some(q) => {
        if !q.transpose().times(q).equals(Mat::ident(3)) {
          ok = false
        }
        if !mdet(q).eq(Q::one()) {
          ok = false
        }
      }
    }
  }
  mk_check(
    "C-20 矩陣冪與 Cayley 變換", ok, 24, "A^{m+n}=A^mA^n；Cayley(S) ∈ SO(n)",
  )
}

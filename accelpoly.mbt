// ============================================================================
//  檔案 22：accelpoly.mbt — 加速層 Λ3：𝔽[x] 層（多項式純 CRT 篩選）
//
//  【定理 Λ3-1（𝔽[x] 之中國剩餘定理）】設 m₁,…,m_k ∈ 𝔽[x] 兩兩互素，
//     M = ∏mᵢ，則環同構 𝔽[x]/(M) ≅ ∏ 𝔽[x]/(mᵢ)。
//     證明：𝔽[x] 為主理想整環，CRT 於任意交換環對互質理想成立；
//           互素 ⇔ (mᵢ)+(mⱼ) = (1)。∎
//  【推論 Λ3-2（求值／插值即 CRT）】取 mᵢ = x − aᵢ（aᵢ 互異），則
//     𝔽[x]/(x−aᵢ) ≅ 𝔽（求值 f ↦ f(aᵢ)），故
//        𝔽[x]_{<d+1} ≅ 𝔽^{d+1},  f ↦ (f(a₀),…,f(a_d))
//     為線性同構（Vandermonde 可逆）；其逆即插值。
//     於是「多項式乘法 = 求值 → 逐點相乘 → 插值」，
//     把 O(d²) 次係數乘法換成 O(d²) 次「字乘法」，且中間量不膨脹。
//  【定理 Λ3-3（雙層 CRT）】整係數多項式運算可同時對
//     「係數」施 ℤ 之 CRT（模素數 p）、對「變數」施 𝔽[x] 之 CRT（求值點），
//     兩層獨立，合成後以 Hadamard／Cauchy 型界作對稱提升。
//
//  本層之三管：
//     A 管：單點求值篩（Schwartz–Zippel／DeMillo–Lipton–Zippel）。
//     B 管：求值–逐點–插值 + 係數 CRT 提升／有理重建。
//     C 管：整除性憑證（G | f ∧ G | g）、逐點值比對憑證。
// ============================================================================

///|
/// 𝔽p[x] 之求值–逐點–插值乘法（𝔽[x] 層之純 CRT）。
/// 【命題 Λ3-4】deg(fg) = deg f + deg g ≤ d，取 d+1 個互異點即可唯一還原。
pub fn fpp_mul_evalinterp(
  a : Array[Int64],
  b : Array[Int64],
  ctx : FpCtx,
) -> Array[Int64]? {
  let fa = fpp_norm(a)
  let fb = fpp_norm(b)
  if fa.length() == 0 || fb.length() == 0 {
    return Some([])
  }
  let d = fa.length() + fb.length() - 2
  let n = d + 1
  if n.to_int64() >= ctx.pmod {
    return None
  }
  let xs = Array::makei(n, i => i.to_int64())
  let ys = Array::makei(n, i => ctx.mul(
    fpp_eval(fa, xs[i], ctx),
    fpp_eval(fb, xs[i], ctx),
  ))
  fpp_interp(xs, ys, ctx)
}

// ---------------------------------------------------------------------------
//  基準路徑：ℤ[x] 之 schoolbook 卷積（受計量）
// ---------------------------------------------------------------------------

///|
pub fn zpoly_mul_school(
  a : Array[BigInt],
  b : Array[BigInt],
  c : Cost,
) -> Array[BigInt] {
  if a.length() == 0 || b.length() == 0 {
    return []
  }
  let out = Array::make(a.length() + b.length() - 1, 0N)
  for i in 0..<a.length() {
    if a[i] != 0N {
      for j in 0..<b.length() {
        out[i + j] = cz_add(c, out[i + j], cz_mul(c, a[i], b[j]))
      }
    }
  }
  out
}

///|
/// 乘積係數之先驗界：|（fg）_k| ≤ (min(deg f,deg g)+1)·‖f‖_∞·‖g‖_∞。
pub fn poly_prod_bound(a : Array[BigInt], b : Array[BigInt]) -> BigInt {
  let mut fa = 0N
  for v in a {
    let t = big_abs(v)
    if t > fa {
      fa = t
    }
  }
  let mut fb = 0N
  for v in b {
    let t = big_abs(v)
    if t > fb {
      fb = t
    }
  }
  let k = if a.length() < b.length() { a.length() } else { b.length() }
  BigInt::from_int(k) * fa * fb + 1N
}

///|
/// 𝔽p[x] 之乘法（自動選管）：長度足夠且 p 支援時走 NTT，否則 schoolbook。
/// 【命題 Λ3-4′】NTT 之成本約 3·n·log₂n + n，schoolbook 為 d₁d₂；
///   於 d ≳ 32 時 NTT 勝出，交叉點由本實作之計數器實測確定。
pub fn fpp_mul_auto(
  a : Array[Int64],
  b : Array[Int64],
  g : Int64,
  ctx : FpCtx,
) -> Array[Int64] {
  let la = fpp_norm(a).length()
  let lb = fpp_norm(b).length()
  let need = la + lb - 1
  if la == 0 || lb == 0 {
    return []
  }
  let mut sz = 1
  let mut lg = 0
  while sz < need {
    sz = sz * 2
    lg = lg + 1
  }
  // 成本比較：NTT ≈ 3·sz·lg + sz；schoolbook ≈ la·lb
  if 3 * sz * lg + sz < la * lb && (ctx.pmod - 1L) % sz.to_int64() == 0L {
    match fpp_mul_ntt(a, b, g, ctx) {
      Some(x) => return x
      None => ()
    }
  }
  fpp_mul(a, b, ctx)
}

///|
/// ℤ[x] 乘法之雙層 CRT：係數模 p（ℤ 之 CRT）× NTT 求值插值（𝔽[x] 之 CRT）。
pub fn zpoly_mul_crt(
  a : Array[BigInt],
  b : Array[BigInt],
  primes : Array[Int64],
  c : Cost,
) -> (Array[BigInt], Int) {
  if a.length() == 0 || b.length() == 0 {
    return ([], 0)
  }
  let len = a.length() + b.length() - 1
  let bound = poly_prod_bound(a, b)
  let need = primes_needed(bound, primes)
  let primes = ensure_primes(primes, need)
  let crts : Array[Crt] = Array::makei(len, _ => Crt::new())
  for t in 0..<need {
    let p = primes[t]
    let ctx = FpCtx::make(p)
    let pb = BigInt::from_int64(p)
    for v in a {
      c.wmul = c.wmul + big_words(v)
      c.bigops = c.bigops + 1L
    }
    for v in b {
      c.wmul = c.wmul + big_words(v)
      c.bigops = c.bigops + 1L
    }
    let fa = Array::makei(a.length(), i => normmod((a[i] % pb).to_int64(), p))
    let fb = Array::makei(b.length(), i => normmod((b[i] % pb).to_int64(), p))
    let prod = fpp_mul_auto(fa, fb, primitive_root(p), ctx)
    c.absorb_fp(ctx)
    for i in 0..<len {
      let v = if i < prod.length() { prod[i] } else { 0L }
      charge_crt_step(c, crts[i].modulus())
      crts[i].absorb(v, p)
    }
  }
  (Array::makei(len, i => crts[i].sym()), need)
}

// ---------------------------------------------------------------------------
//  A 管：多項式恆等式之求值篩
//  【定理 Λ3-5（Schwartz–Zippel，單變量版）】非零 f ∈ 𝔽p[x]，deg f = d，
//     則 Pr_{t ← 𝔽p}[f(t) = 0] ≤ d/p。
//     證明：非零多項式於體上至多 d 個根。∎
//     取 d ≤ 2·10³、p > 2³⁰ ⇒ 單點誤收機率 < 2·10⁻⁶；取 t 個獨立點 ⇒ ≤ (d/p)^t。
// ---------------------------------------------------------------------------

///|
/// 篩：驗證 f·g = h（整係數）是否可能成立。回傳 false ⇒ 必不成立。
pub fn screen_poly_mul(
  a : Array[BigInt],
  b : Array[BigInt],
  h : Array[BigInt],
  p : Int64,
  pts : Int,
  rng : Rng,
  c : Cost,
) -> Bool {
  let ctx = FpCtx::make(p)
  let pb = BigInt::from_int64(p)
  for v in a {
    c.wmul = c.wmul + big_words(v)
    c.bigops = c.bigops + 1L
  }
  for v in b {
    c.wmul = c.wmul + big_words(v)
    c.bigops = c.bigops + 1L
  }
  for v in h {
    c.wmul = c.wmul + big_words(v)
    c.bigops = c.bigops + 1L
  }
  let fa = Array::makei(a.length(), i => normmod((a[i] % pb).to_int64(), p))
  let fb = Array::makei(b.length(), i => normmod((b[i] % pb).to_int64(), p))
  let fh = Array::makei(h.length(), i => normmod((h[i] % pb).to_int64(), p))
  let mut okall = true
  for _k in 0..<pts {
    let t = normmod(rng.next_below(1000000).to_int64(), p)
    let va = fpp_eval(fa, t, ctx)
    let vb = fpp_eval(fb, t, ctx)
    let vh = fpp_eval(fh, t, ctx)
    if ctx.mul(va, vb) != vh {
      okall = false
      break
    }
  }
  c.absorb_fp(ctx)
  okall
}

// ---------------------------------------------------------------------------
//  由根造多項式：線性累積 vs 積樹（operand balancing）
//  【命題 Λ3-6】線性累積之第 k 步為 (k 次 × 1 次)，係數位元長度 Θ(k b)，
//     總成本 Θ(Σ k·(k b/64)) = Θ(n³b²/64²)（以字乘法計）。
//     積樹把乘法成對平衡，總成本 Θ(n²b²/64² · log n) 之常數顯著較小。
//     本實作以計數器實測比值。
// ---------------------------------------------------------------------------

///|
pub fn zpoly_from_roots_linear(roots : Array[BigInt], c : Cost) -> Array[BigInt] {
  let mut acc : Array[BigInt] = [1N]
  for r in roots {
    acc = zpoly_mul_school(acc, [-r, 1N], c)
  }
  acc
}

///|
pub fn zpoly_from_roots_tree(roots : Array[BigInt], c : Cost) -> Array[BigInt] {
  let n = roots.length()
  if n == 0 {
    return [1N]
  }
  let mut level : Array[Array[BigInt]] = []
  for r in roots {
    level.push([-r, 1N])
  }
  while level.length() > 1 {
    let next : Array[Array[BigInt]] = []
    let mut i = 0
    while i + 1 < level.length() {
      next.push(zpoly_mul_school(level[i], level[i + 1], c))
      i = i + 2
    }
    if i < level.length() {
      next.push(level[i])
    }
    level = next
  }
  level[0]
}

// ---------------------------------------------------------------------------
//  特徵多項式之「𝔽[x] 純 CRT」路徑
//  χ_A(x) = det(xI − A)。於 𝔽p 上取 n+1 個節點 tᵢ 計算 det(tᵢI − A)，
//  再以插值（即 𝔽[x] 之 CRT 逆映射）還原 χ_A mod p；最後對係數施 ℤ 之 CRT。
//  【命題 Λ3-7】χ_A 首一且 deg = n，故 n+1 個點即唯一決定。
// ---------------------------------------------------------------------------

///|
pub fn zcharpoly_interp(
  a : Array[Array[BigInt]],
  primes : Array[Int64],
  c : Cost,
) -> (Array[BigInt], Int) {
  let n = a.length()
  let bound = charpoly_bound(a)
  let need = primes_needed(bound, primes)
  let primes = ensure_primes(primes, need)
  let crts : Array[Crt] = Array::makei(n + 1, _ => Crt::new())
  for t in 0..<need {
    let p = primes[t]
    let ctx = FpCtx::make(p)
    charge_reduce_rows(c, a)
    let fa = fp_of_big(a, ctx)
    let xs = Array::makei(n + 1, i => i.to_int64())
    let ys = Array::makei(n + 1, k => {
      let m = FpMat::make(n, n)
      for i in 0..<n {
        for j in 0..<n {
          let v = if i == j {
            ctx.sub(xs[k], fa.get(i, j))
          } else {
            ctx.neg(fa.get(i, j))
          }
          m.set(i, j, v)
        }
      }
      fp_det_fast(m, ctx)
    })
    let cp = match fpp_interp(xs, ys, ctx) {
      Some(x) => x
      None => []
    }
    c.absorb_fp(ctx)
    for i in 0..<(n + 1) {
      let v = if i < cp.length() { cp[i] } else { 0L }
      charge_crt_step(c, crts[i].modulus())
      crts[i].absorb(v, p)
    }
  }
  (Array::makei(n + 1, i => crts[i].sym()), need)
}

///|
/// 基準路徑：ℚ 上之 Faddeev–LeVerrier（受計量）。
pub fn qcharpoly_faddeev(a : Mat[Q], c : Cost) -> Array[Q] {
  let n = a.mrows
  let coeffs = Array::makei(n + 1, _ => Q::zero())
  coeffs[n] = Q::one()
  let mut mk = Mat::build(n, n, (i, j) => if i == j { Q::one() } else { Q::zero() })
  for k in 1..<(n + 1) {
    let am = Mat::build(n, n, (i, j) => {
      let mut s = Q::zero()
      for t in 0..<n {
        s = cq_add(c, s, cq_mul(c, a.at(i, t), mk.at(t, j)))
      }
      s
    })
    let mut tr = Q::zero()
    for i in 0..<n {
      tr = cq_add(c, tr, am.at(i, i))
    }
    let ck = match cq_div(c, tr, Q::of_int(k)) {
      Some(x) => x.neg()
      None => Q::zero()
    }
    coeffs[n - k] = ck
    mk = Mat::build(n, n, (i, j) => if i == j {
      cq_add(c, am.at(i, j), ck)
    } else {
      am.at(i, j)
    })
  }
  coeffs
}

// ---------------------------------------------------------------------------
//  ℚ[x] 之受計量運算（基準路徑與憑證用）
// ---------------------------------------------------------------------------

///|
pub fn qpoly_norm(a : Array[Q]) -> Array[Q] {
  let mut n = a.length()
  while n > 0 && a[n - 1].is_zero() {
    n = n - 1
  }
  Array::makei(n, i => a[i])
}

///|
pub fn qpoly_mul(a : Array[Q], b : Array[Q], c : Cost) -> Array[Q] {
  if a.length() == 0 || b.length() == 0 {
    return []
  }
  let out = Array::make(a.length() + b.length() - 1, Q::zero())
  for i in 0..<a.length() {
    if !a[i].is_zero() {
      for j in 0..<b.length() {
        out[i + j] = cq_add(c, out[i + j], cq_mul(c, a[i], b[j]))
      }
    }
  }
  qpoly_norm(out)
}

///|
pub fn qpoly_divmod(
  a : Array[Q],
  b : Array[Q],
  c : Cost,
) -> (Array[Q], Array[Q])? {
  let bb = qpoly_norm(b)
  if bb.length() == 0 {
    return None
  }
  let lead = bb[bb.length() - 1]
  let r = Array::makei(a.length(), i => a[i])
  let db = bb.length() - 1
  let dq = r.length() - 1 - db
  if dq < 0 {
    return Some(([], qpoly_norm(r)))
  }
  let q = Array::make(dq + 1, Q::zero())
  for k = r.length() - 1; k >= db; k = k - 1 {
    let co = match cq_div(c, r[k], lead) {
      Some(x) => x
      None => Q::zero()
    }
    q[k - db] = co
    if !co.is_zero() {
      for j in 0..<bb.length() {
        r[k - db + j] = cq_sub(c, r[k - db + j], cq_mul(c, co, bb[j]))
      }
    }
  }
  (Some((qpoly_norm(q), qpoly_norm(r))))
}

///|
/// 基準路徑：ℚ[x] 之歐幾里得 gcd（係數膨脹之經典反例）。
pub fn qpoly_gcd_euclid(a : Array[Q], b : Array[Q], c : Cost) -> Array[Q] {
  let mut x = qpoly_norm(a)
  let mut y = qpoly_norm(b)
  while y.length() > 0 {
    match qpoly_divmod(x, y, c) {
      None => break
      Some((_q, r)) => {
        x = y
        y = r
      }
    }
  }
  if x.length() == 0 {
    return []
  }
  let lead = x[x.length() - 1]
  Array::makei(x.length(), i => match cq_div(c, x[i], lead) {
    Some(v) => v
    None => Q::zero()
  })
}

// ---------------------------------------------------------------------------
//  加速路徑：ℤ[x] 之 gcd —— mod p 篩 + 有理重建 + 整除性憑證
//  【引理 Λ3-8】設 p ∤ lc(f)·lc(g)。則 deg gcd_{𝔽p}(f̄,ḡ) ≥ deg gcd_ℚ(f,g)。
//     證明：令 G = gcd_ℚ(f,g) 之本原整係數表示，則 G | f 與 G | g 於 ℤ[x]
//           （Gauss 引理），約化後 Ḡ | f̄ 且 Ḡ | ḡ，且 deg Ḡ = deg G（lc 不消失）
//           ⇒ 𝔽p 上之 gcd 次數 ≥ deg G。∎
//  【定理 Λ3-9（無條件憑證）】若候選 G 滿足 deg G = min_p deg gcd_p，
//     且 G | f、G | g（於 ℚ[x] 中精確整除），則 G = gcd_ℚ(f,g)（首一化後）。
//     證明：整除性 ⇒ deg G ≤ deg gcd_ℚ；引理 ⇒ deg gcd_ℚ ≤ min_p deg gcd_p = deg G。
//           故 deg 相等；又 G 為公因式且次數達最大 ⇒ G 為 gcd（相差常數）。∎
//     此憑證不依賴「幸運素數」之機率論證，故為無條件正確。
// ---------------------------------------------------------------------------

///|
pub struct QGcdLift {
  gcd : Array[Q]
  degmin : Int
  used : Int
  certified : Bool
}

///|
pub fn zpoly_gcd_crt(
  f : Array[BigInt],
  g : Array[BigInt],
  primes : Array[Int64],
  c : Cost,
) -> QGcdLift? {
  if f.length() == 0 || g.length() == 0 {
    return None
  }
  let mut degmin = 1000000
  let mut crts : Array[Crt] = []
  let mut used = 0
  let mut prev : Array[Q]? = None
  let fq = Array::makei(f.length(), i => Q::make(f[i], 1N))
  let gq = Array::makei(g.length(), i => Q::make(g[i], 1N))
  for t in 0..<primes.length() {
    let p = primes[t]
    let ctx = FpCtx::make(p)
    let pb = BigInt::from_int64(p)
    for v in f {
      c.wmul = c.wmul + big_words(v)
      c.bigops = c.bigops + 1L
    }
    for v in g {
      c.wmul = c.wmul + big_words(v)
      c.bigops = c.bigops + 1L
    }
    let ff = fpp_norm(Array::makei(f.length(), i => normmod((f[i] % pb).to_int64(), p)))
    let gg = fpp_norm(Array::makei(g.length(), i => normmod((g[i] % pb).to_int64(), p)))
    if ff.length() != f.length() || gg.length() != g.length() {
      // p 整除首項係數 ⇒ 壞素數
      c.absorb_fp(ctx)
      continue
    }
    let d = fpp_gcd(ff, gg, ctx)
    c.absorb_fp(ctx)
    let dg = d.length() - 1
    if dg < 0 {
      continue
    }
    if dg < degmin {
      degmin = dg
      crts = Array::makei(dg + 1, _ => Crt::new())
      used = 0
      prev = None
    } else if dg > degmin {
      continue
    }
    for i in 0..<(degmin + 1) {
      charge_crt_step(c, crts[i].modulus())
      crts[i].absorb(d[i], p)
    }
    used = used + 1
    if used >= 2 {
      let m = crts[0].modulus()
      let flat = Array::makei(degmin + 1, i => crts[i].sym())
      match rat_recon_vec(flat, m) {
        None => continue
        Some(x) => {
          let stable = match prev {
            None => false
            Some(pv) => qvec_eq(pv, x)
          }
          prev = Some(x)
          if stable {
            let okf = match qpoly_divmod(fq, x, c) {
              Some((_q, r)) => r.length() == 0
              None => false
            }
            let okg = match qpoly_divmod(gq, x, c) {
              Some((_q, r)) => r.length() == 0
              None => false
            }
            return Some({ gcd: x, degmin, used, certified: okf && okg })
          }
        }
      }
    }
  }
  match prev {
    None => None
    Some(x) => Some({ gcd: x, degmin, used, certified: false })
  }
}

// ---------------------------------------------------------------------------
//  ℚ 上之插值：多模 + 有理重建 + 逐點憑證
//  【定理 Λ3-10】節點互異 ⇒ Vandermonde 可逆 ⇒ 插值多項式存在唯一。
//     C 管憑證：直接代回驗證 f(xᵢ) = yᵢ（i = 0..d），此即唯一性之見證。
// ---------------------------------------------------------------------------

///|
pub struct QInterpLift {
  poly : Array[Q]
  used : Int
  certified : Bool
}

///|
pub fn qinterp_crt(
  xs : Array[Q],
  ys : Array[Q],
  primes : Array[Int64],
  c : Cost,
) -> QInterpLift? {
  let n = xs.length()
  if n == 0 || ys.length() != n {
    return None
  }
  let (dx, xz) = qvec_clear_denom(xs)
  let (dy, yz) = qvec_clear_denom(ys)
  let crts : Array[Crt] = Array::makei(n, _ => Crt::new())
  let mut used = 0
  let mut prev : Array[Q]? = None
  for t in 0..<primes.length() {
    let p = primes[t]
    let ctx = FpCtx::make(p)
    let pb = BigInt::from_int64(p)
    let dxi = match ctx.inv(normmod((dx % pb).to_int64(), p)) {
      Some(v) => v
      None => continue
    }
    let dyi = match ctx.inv(normmod((dy % pb).to_int64(), p)) {
      Some(v) => v
      None => continue
    }
    for v in xz {
      c.wmul = c.wmul + big_words(v)
      c.bigops = c.bigops + 1L
    }
    for v in yz {
      c.wmul = c.wmul + big_words(v)
      c.bigops = c.bigops + 1L
    }
    let fx = Array::makei(n, i => ctx.mul(normmod((xz[i] % pb).to_int64(), p), dxi))
    let fy = Array::makei(n, i => ctx.mul(normmod((yz[i] % pb).to_int64(), p), dyi))
    let pl = match fpp_interp(fx, fy, ctx) {
      Some(v) => v
      None => {
        c.absorb_fp(ctx)
        continue
      }
    }
    c.absorb_fp(ctx)
    for i in 0..<n {
      let v = if i < pl.length() { pl[i] } else { 0L }
      charge_crt_step(c, crts[i].modulus())
      crts[i].absorb(v, p)
    }
    used = used + 1
    if used >= 2 {
      let m = crts[0].modulus()
      let flat = Array::makei(n, i => crts[i].sym())
      match rat_recon_vec(flat, m) {
        None => continue
        Some(x) => {
          let stable = match prev {
            None => false
            Some(pv) => qvec_eq(pv, x)
          }
          prev = Some(x)
          if stable {
            let mut okall = true
            for i in 0..<n {
              let mut acc = Q::zero()
              for k = x.length() - 1; k >= 0; k = k - 1 {
                acc = cq_add(c, cq_mul(c, acc, xs[i]), x[k])
              }
              if !acc.eq(ys[i]) {
                okall = false
              }
            }
            return Some({ poly: qpoly_norm(x), used, certified: okall })
          }
        }
      }
    }
  }
  match prev {
    None => None
    Some(x) => Some({ poly: qpoly_norm(x), used, certified: false })
  }
}

///|
/// 基準路徑：ℚ 上之 Lagrange 插值（受計量）。
pub fn qinterp_lagrange(xs : Array[Q], ys : Array[Q], c : Cost) -> Array[Q] {
  let n = xs.length()
  let out = Array::make(n, Q::zero())
  for i in 0..<n {
    // Lᵢ(x) = ∏_{j≠i} (x − xⱼ)/(xᵢ − xⱼ)
    let mut basis : Array[Q] = [Q::one()]
    let mut denom = Q::one()
    for j in 0..<n {
      if j != i {
        basis = qpoly_mul(basis, [xs[j].neg(), Q::one()], c)
        denom = cq_mul(c, denom, cq_sub(c, xs[i], xs[j]))
      }
    }
    let sc = match cq_div(c, ys[i], denom) {
      Some(v) => v
      None => Q::zero()
    }
    for k in 0..<basis.length() {
      out[k] = cq_add(c, out[k], cq_mul(c, basis[k], sc))
    }
  }
  qpoly_norm(out)
}

// ---------------------------------------------------------------------------
//  ℚ[x] 之乘法：清分母 → 多模 NTT → CRT 提升 → 還原分母
//  【命題 Λ3-11】設 f = F/d_f、g = G/d_g（F,G ∈ ℤ[x]），則 fg = (FG)/(d_f d_g)。
//     ℚ 上之直接卷積每次乘法都要做一次 gcd 正規化（歐幾里得，成本 Θ(w²)），
//     且分母逐步取 lcm 而膨脹；清分母後整個計算落在 ℤ，再落到 𝔽p。
// ---------------------------------------------------------------------------

///|
pub fn qpoly_mul_crt(
  a : Array[Q],
  b : Array[Q],
  primes : Array[Int64],
  c : Cost,
) -> (Array[Q], Int) {
  if a.length() == 0 || b.length() == 0 {
    return ([], 0)
  }
  let (da, az) = qvec_clear_denom(a)
  let (db, bz) = qvec_clear_denom(b)
  let (pz, np) = zpoly_mul_crt(az, bz, primes, c)
  let den = cz_mul(c, da, db)
  let out = Array::makei(pz.length(), i => cq_make(c, pz[i], den))
  (qpoly_norm(out), np)
}

// ===========================================================================
//  加速分派器（Dispatcher）：令「正向優化」成為可檢驗之性質
//
//  【定義 Λ3-12】分派器為一個只看「規模參數」(n, b, d, k) 而不看資料之
//     判定函數 δ；δ = true 時走加速管，否則走基準管。
//  【定理 Λ3-13（正向性）】若 δ 滿足
//        δ(params) = true ⇒ cost_fast(params) < cost_base(params)，
//     則「基準 ⊕ δ 分派」之成本逐點 ≤ 基準成本，即分派後之系統必為正向優化。
//     證明：δ 為真時取較小者，為假時取基準，逐點不劣。∎
//  本庫之義務 K-10 / L-10 / M-08 於一整片參數網格上實測驗證此蘊含式，
//  故「正向優化」不是宣稱而是被自證之性質。
//  【命題 Λ3-14（誠實之反例）】並非所有運算都該加速：
//     ℤ[x] 之「由根造多項式」以 schoolbook 算術而言，
//     積樹與多模 CRT 皆劣於線性累積（實測比值 < 1），分派器必須回答「不加速」。
// ===========================================================================

///|
/// 分派決策之結果。
pub struct AccelPlan {
  pname : String
  use_fast : Bool
  pred_base : Int64
  pred_fast : Int64
  why : String
}

///|
fn words_of_bits(b : Int) -> Int64 {
  let w = (b + 63) / 64
  if w < 1 {
    1L
  } else {
    w.to_int64()
  }
}

///|
/// 分派之安全邊際：預測增益須 ≥ 5/4 才切換（寧可少賺、不可虧損）。
/// 【命題 Λ3-13′】邊際令預測誤差 ≤ 25% 時仍保持 cost_fast < cost_base。
pub let accel_margin_num : Int64 = 5L

///|
pub let accel_margin_den : Int64 = 4L

///|
fn decide(name : String, base : Int64, fast : Int64, why : String) -> AccelPlan {
  {
    pname: name,
    use_fast: fast * accel_margin_num < base * accel_margin_den,
    pred_base: base,
    pred_fast: fast,
    why,
  }
}

///|
/// ℤ 行列式之分派（成本模型已以實測網格校準）。
///   基準（Bareiss）：(n³/3)·w²，w = 字數(0.6·n·(b+6))（中間子式之平均規模）。
///   加速（多模 CRT）：k·(n³/3 + 46n + n²·字數(b)) + 1.5·k²·0.48，
///     其中 46n 為每個樞軸一次 Fermat 求逆之成本，k = ⌈n(b+6)/31⌉。
pub fn plan_zdet(n : Int, bits : Int) -> AccelPlan {
  let nn = n.to_int64()
  let core = nn * nn * nn / 3L
  let w = words_of_bits(6 * n * (bits + 6) / 10)
  let pred_base = core * w * w
  let k = (n * (bits + 6) + 30) / 31
  let kk = k.to_int64()
  let pred_fast = kk * (core + 46L * nn + nn * nn * words_of_bits(bits)) +
    72L * kk * kk / 100L
  decide(
    "ℤ 行列式",
    pred_base,
    pred_fast,
    "Bareiss 中間量 ≈ " +
    (6 * n * (bits + 6) / 10).to_string() +
    " 位元（" +
    w.to_string() +
    " 字）；需 " +
    k.to_string() +
    " 個素數",
  )
}

///|
/// ℚ 線性解之分派：高斯消去第 k 步之分子與分母各約 k·b 位元，
///   且每次 ℚ 運算含一次 gcd（約 6 倍常數）。
pub fn plan_qsolve(n : Int, bits : Int) -> AccelPlan {
  let nn = n.to_int64()
  let core = nn * nn * nn / 3L
  let w = words_of_bits(3 * n * bits)
  let pred_base = core * w * w * 12L
  let k = (2 * n * (bits + 2) + 30) / 31
  let kk = k.to_int64()
  // fp_solve 為完全消去（≈ n³），另加每樞軸一次 Fermat 求逆（46n）、
  // 模約化（n²）、有理重建與事後憑證（以 1.4 倍經驗因子涵蓋）
  let pred_fast = 14L *
    (kk * (nn * nn * nn + 46L * nn + nn * nn) + 72L * kk * kk * nn / 100L) /
    10L
  decide(
    "ℚ 線性解",
    pred_base,
    pred_fast,
    "高斯消去中間量 ≈ " +
    (3 * n * bits).to_string() +
    " 位元；需 " +
    k.to_string() +
    " 個素數",
  )
}

///|
/// ℤ 伴隨矩陣之分派。
///
/// 為何需要獨立分派器（而不能沿用 plan_zdet）：
///   行列式之輸出為「1 個整數」，伴隨矩陣之輸出為「n² 個整數」。
///   多模路徑對每個輸出都要獨立做 Θ(k²) 之 CRT 累積，故 CRT 項帶 n² 因子；
///   行列式無此因子。這使伴隨矩陣在小 n 上淨虧，而行列式自 n=2 起即獲利。
///
/// 命題（交叉點）：以下模型在 bits = 64 時之預測與實測網格吻合 ——
///   n=5 ×0.33（實測 ×0.35）、n=8 ×1.70（實測 ×1.70）、n=11 ×5.21（實測 ×5.79），
///   交叉點 n ≈ 7。常數 619/100 由該三點校準。
///   基準為餘因子式 Bareiss：n² 個 (n−1) 階行列式，各 ((n−1)³/3)·w²。
pub fn plan_zadj(n : Int, bits : Int) -> AccelPlan {
  let nn = n.to_int64()
  let m = (n - 1).to_int64()
  let w = words_of_bits(6 * n * (bits + 6) / 10)
  // 基準：n² 個 (n−1) 階餘因子行列式（Bareiss）
  let pred_base = nn * nn * (m * m * m / 3L) * w * w
  let k = (n * (bits + 6) + 30) / 31
  let kk = k.to_int64()
  // 加速：k 個素數各一次 n³ 消去；CRT 項帶 n² 因子（n² 個輸出各自重建）
  let pred_fast = kk *
    (nn * nn * nn / 3L + 46L * nn + nn * nn * words_of_bits(bits)) +
    619L * nn * nn * kk * kk / 100L
  decide(
    "ℤ 伴隨矩陣",
    pred_base,
    pred_fast,
    "輸出 " +
    (n * n).to_string() +
    " 個整數（非 1 個）⇒ CRT 項帶 n² 因子；需 " +
    k.to_string() +
    " 個素數；交叉點 n ≈ 7",
  )
}

///|
/// ℤ[x] 乘法之分派：schoolbook 為 d²w²；
///   多模 NTT 為 k·(3·sz·lg + sz + 2d·字數(b)) + 1.44·d·k²（CRT 累積）。
pub fn plan_zpolymul(d : Int, bits : Int) -> AccelPlan {
  let dd = d.to_int64()
  let w = words_of_bits(bits)
  let pred_base = dd * dd * w * w
  let need = 2 * d - 1
  let mut sz = 1
  let mut lg = 0
  while sz < need {
    sz = sz * 2
    lg = lg + 1
  }
  let k = (2 * bits + 2 * 31 + 30) / 31
  let kk = k.to_int64()
  let szl = sz.to_int64()
  let pred_fast = kk * (3L * szl * lg.to_int64() + szl + 2L * dd * w) +
    144L * dd * kk * kk / 100L
  decide(
    "ℤ[x] 乘法",
    pred_base,
    pred_fast,
    "NTT 長度 " +
    sz.to_string() +
    "（lg=" +
    lg.to_string() +
    "）；需 " +
    k.to_string() +
    " 個素數",
  )
}

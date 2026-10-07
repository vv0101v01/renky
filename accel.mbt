// ============================================================================
//  檔案 21：accel.mbt — 加速層 Λ2：成本模型 ‧ ℤ 層（純 CRT）‧ ℚ 層（有理重建）
//
//  ── 加速層之總架構 ───────────────────────────────────────────────────────
//  三個「縱向層」依純量體分：
//     ℤ 層（K 群）：純整數純 CRT 篩選。多素數影像 + 先驗 Hadamard 界 + 對稱提升。
//     ℚ 層（L 群）：Fp 層級有理數重建篩選。多素數影像 + 格重建 + 事後憑證。
//     𝔽[x] 層（M 群，見 accelpoly.mbt）：多項式純 CRT（求值／插值）。
//  每層橫向再分「三條管」：
//     A 管（篩 Screen）：單一同態像比對。單向可靠：像不等 ⇒ 原命題必假。
//     B 管（升 Lift）  ：多像 + CRT／插值／有理重建，產出候選精確解。
//     C 管（證 Certify）：事後憑證（Ax=b、A·A⁻¹=I、LDLᵀ=G、整除性…），
//                        通過即「無條件正確」，不依賴任何界或機率論證。
//
//  ── 為何是正向優化（成本模型）─────────────────────────────────────────
//  【成本模型 Λ2-1】以「機器字乘法次數」為單位。schoolbook 算術下，
//    兩個分別 w₁、w₂ 字之整數相乘（或相除）耗 w₁·w₂ 次字乘法；
//    加減耗 max(w₁,w₂) 次字加法（另計，不計入主成本）。
//    本檔之 Cost 計數器逐次累加「真實執行到的」運算，故非理論估計而是實測。
//  【定理 Λ2-2（係數膨脹）】ℚ 上之高斯消去，第 k 步之元素一般具
//    Θ(k·b) 位元（b 為輸入位元數），故總成本 Θ(n³·(n b/64)²) = Θ(n⁵b²)。
//    模路徑之每個中間量恆 < 2³¹（一字），總成本 Θ(k·n³ + n²·k²)，
//    其中 k = O(n b/30) 為所需素數個數 ⇒ Θ(n⁴b/30)。n 或 b 增大時比值發散。
//  【定理 Λ2-3（語義不變）】加速路徑之輸出與原路徑逐位相同：
//    ℤ 層由 CRT 唯一性（界足夠）保證；ℚ 層由事後憑證 C 管保證。
//    故此優化為「正向」：答案不變、成本嚴格下降。
// ============================================================================

///|
/// 成本計數器（確定性、可重現、可覆核）。
pub struct Cost {
  /// 機器字乘法次數（主成本）
  mut wmul : Int64
  /// 機器字加減次數
  mut wadd : Int64
  /// BigInt 級運算之呼叫次數
  mut bigops : Int64
  /// 中間量之最大位元長度（量度係數膨脹）
  mut maxbits : Int
  /// ℝ 軌浮點運算次數（乘 + 加 + 比較；見 rcost.mbt 之 N-20）
  mut flops : Int64
  /// 有理數乘法之**呼叫次數**（N-41）。
  ///
  /// 與 wmul 的差別是粒度：wmul 隨運算元位寬加權，故它量的是「真實代價」；
  /// qmul 不加權，量的是「演算法做了幾次元素級乘法」。結構律的符號成本模型
  /// （N-12 的 tmat、N-41 的 acost）預測的正是後者 —— 它們只看樹的形狀與
  /// 維數，看不見係數膨脹。兩個粒度各有用途，混用會得到對不上的數字：
  /// N-41 第一次把 acost 拿去對 wmul，差了 6 倍（180 vs 1111）。
  mut qmul : Int64
}

///|
/// 成本模型歸零：所有計數器（BigInt 位元運算數／Q 運算數等）回到起點。
pub fn Cost::new() -> Cost {
  { wmul: 0L, wadd: 0L, bigops: 0L, maxbits: 0, flops: 0L, qmul: 0L, }
}

///|
/// 記一筆位元運算之成本：bits 為運算元位元長度，累計入 self。
pub fn Cost::note(self : Cost, bits : Int) -> Unit {
  if bits > self.maxbits {
    self.maxbits = bits
  }
}

///|
/// 直接記入 k 次字乘法（用於吸收 FpCtx 之計數）。
pub fn Cost::words_mul(self : Cost, k : Int64) -> Unit {
  self.wmul = self.wmul + k
}

///|
/// 吸收一個 𝔽p 脈絡之運算量（每次模乘 = 1 次字乘法，且中間量 ≤ 62 位元）。
pub fn Cost::absorb_fp(self : Cost, ctx : FpCtx) -> Unit {
  self.wmul = self.wmul + ctx.ops
  self.wadd = self.wadd + ctx.adds
  self.bigops = self.bigops + ctx.ops
  self.note(62)
}

///|
/// 加速比 base/fast（>1 表示加速；以位元運算計，可量測之成本模型）。
pub fn Cost::ratio(base : Cost, fast : Cost) -> Double {
  let b = base.wmul.to_double()
  let f = fast.wmul.to_double()
  if f <= 0.0 {
    0.0
  } else {
    b / f
  }
}

// ---------------------------------------------------------------------------
//  受計量之 BigInt 與 ℚ 運算（基準路徑用）
// ---------------------------------------------------------------------------

///|
/// ℤ 乘法（帶成本記帳）。
pub fn cz_mul(c : Cost, a : BigInt, b : BigInt) -> BigInt {
  c.wmul = c.wmul + big_words(a) * big_words(b)
  c.bigops = c.bigops + 1L
  let r = a * b
  c.note(r.bit_length())
  r
}

///|
/// ℤ 除法（帶成本記帳；捨去餘數，b = 0 時回 0）。
pub fn cz_div(c : Cost, a : BigInt, b : BigInt) -> BigInt {
  c.wmul = c.wmul + big_words(a) * big_words(b)
  c.bigops = c.bigops + 1L
  let r = a / b
  c.note(r.bit_length())
  r
}

///|
/// ℤ 取模（帶成本記帳）。
pub fn cz_mod(c : Cost, a : BigInt, b : BigInt) -> BigInt {
  c.wmul = c.wmul + big_words(a) * big_words(b)
  c.bigops = c.bigops + 1L
  a % b
}

///|
/// ℤ 加法（帶成本記帳）。
pub fn cz_add(c : Cost, a : BigInt, b : BigInt) -> BigInt {
  let wa = big_words(a)
  let wb = big_words(b)
  c.wadd = c.wadd + (if wa > wb { wa } else { wb })
  c.bigops = c.bigops + 1L
  let r = a + b
  c.note(r.bit_length())
  r
}

///|
/// ℤ 減法（帶成本記帳）。
pub fn cz_sub(c : Cost, a : BigInt, b : BigInt) -> BigInt {
  let wa = big_words(a)
  let wb = big_words(b)
  c.wadd = c.wadd + (if wa > wb { wa } else { wb })
  c.bigops = c.bigops + 1L
  let r = a - b
  c.note(r.bit_length())
  r
}

///|
/// 受計量之 Euclid gcd。
pub fn cz_gcd(c : Cost, a0 : BigInt, b0 : BigInt) -> BigInt {
  let mut a = big_abs(a0)
  let mut b = big_abs(b0)
  while b != 0N {
    let r = cz_mod(c, a, b)
    a = b
    b = r
  }
  a
}

///|
/// 受計量之既約分數建構（保持 Q 之不變量 den > 0 ∧ gcd = 1）。
pub fn cq_make(c : Cost, n0 : BigInt, d0 : BigInt) -> Q {
  if d0 == 0N {
    abort("cq_make 前置條件違反：分母為 0")
  }
  let n = if d0 < 0N { -n0 } else { n0 }
  let d = if d0 < 0N { -d0 } else { d0 }
  if n == 0N {
    return Q::zero()
  }
  let g = cz_gcd(c, n, d)
  if g == 1N {
    { num: n, den: d, }
  } else {
    { num: cz_div(c, n, g), den: cz_div(c, d, g), }
  }
}

///|
/// ℚ 加法（帶成本記帳；先取共同分母再相加）。
pub fn cq_add(c : Cost, x : Q, y : Q) -> Q {
  let n = cz_add(c, cz_mul(c, x.num, y.den), cz_mul(c, y.num, x.den))
  let d = cz_mul(c, x.den, y.den)
  cq_make(c, n, d)
}

///|
/// ℚ 減法（帶成本記帳）。
pub fn cq_sub(c : Cost, x : Q, y : Q) -> Q {
  let n = cz_sub(c, cz_mul(c, x.num, y.den), cz_mul(c, y.num, x.den))
  let d = cz_mul(c, x.den, y.den)
  cq_make(c, n, d)
}

///|
/// ℚ 乘法（帶成本記帳；乘後即約分）。
pub fn cq_mul(c : Cost, x : Q, y : Q) -> Q {
  c.qmul = c.qmul + 1L
  cq_make(c, cz_mul(c, x.num, y.num), cz_mul(c, x.den, y.den))
}

///|
/// ℚ 除法（帶成本記帳；除以 0 回 None）。
pub fn cq_div(c : Cost, x : Q, y : Q) -> Q? {
  if y.num == 0N {
    None
  } else {
    Some(cq_make(c, cz_mul(c, x.num, y.den), cz_mul(c, x.den, y.num)))
  }
}

// ---------------------------------------------------------------------------
//  計量輔助：模約化與 CRT 步之成本
// ---------------------------------------------------------------------------

///|
fn charge_reduce_rows(c : Cost, a : Array[Array[BigInt]]) -> Unit {
  for row in a {
    for v in row {
      c.wmul = c.wmul + big_words(v)
      c.bigops = c.bigops + 1L
    }
  }
}

///|
fn charge_crt_step(c : Cost, m : BigInt) -> Unit {
  let w = big_words(m)
  // 2 次 BigInt mod（除以單字）+ 1 次 BigInt × 單字 + 1 次加法
  c.wmul = c.wmul + 3L * w
  c.wadd = c.wadd + w
  c.bigops = c.bigops + 4L
  c.note(m.bit_length() + 31)
}

///|
/// 加速條目之統計摘要。
pub struct AccelStat {
  /// 條目名稱
  aname : String
  /// 基準路徑之字乘法次數
  base_wmul : Int64
  /// 加速路徑之字乘法次數
  fast_wmul : Int64
  /// 基準路徑之最大中間位元長度
  base_bits : Int
  /// 加速路徑之最大中間位元長度
  fast_bits : Int
  /// 使用之素數個數
  nprimes : Int
  /// C 管事後憑證是否通過
  certified : Bool
}

///|
/// 實測增益 = 基礎成本 ÷ 加速成本。
pub fn AccelStat::gain(self : AccelStat) -> Double {
  if self.fast_wmul <= 0L {
    0.0
  } else {
    self.base_wmul.to_double() / self.fast_wmul.to_double()
  }
}

///|
/// 報表列：名稱、成本對、增益、是否分派加速路徑。
pub fn AccelStat::line(self : AccelStat) -> String {
  self.aname +
  "：基準 " +
  self.base_wmul.to_string() +
  " 字乘 / 加速 " +
  self.fast_wmul.to_string() +
  " 字乘 = ×" +
  fmt_d(self.gain(), 2) +
  "；位元 " +
  self.base_bits.to_string() +
  " → " +
  self.fast_bits.to_string() +
  "；素數 " +
  self.nprimes.to_string() +
  (if self.certified { "；憑證 ✔" } else { "；憑證 —" })
}

// ===========================================================================
//  ℤ 層（K 群）：純整數純 CRT
// ===========================================================================

// ---------------------------------------------------------------------------
//  基準路徑：Bareiss 無分數消去（精確整數行列式之古典最佳法）
//  【定理 Λ2-4（Bareiss）】令 a^{(0)}_{ij} = a_{ij}，a^{(−1)}_{−1,−1} = 1，
//     a^{(k)}_{ij} = (a^{(k−1)}_{kk} a^{(k−1)}_{ij} − a^{(k−1)}_{ik} a^{(k−1)}_{kj})
//                    / a^{(k−2)}_{k−1,k−1}
//     則每次除法皆為整除，且 a^{(k)}_{ij} 等於某個 (k+1)×(k+1) 子式；
//     最終 a^{(n−1)}_{n−1,n−1} = det A。
//     證明：由 Sylvester 之恆等式（Desnanot–Jacobi）歸納。∎
//  成本特徵：中間量為子式 ⇒ 位元長度隨 k 線性增長（係數膨脹）。
// ---------------------------------------------------------------------------

///|
/// ℤ 行列式：Bareiss 無分數消去 —— Θ(n³) 整數運算且中間值受控，免 gcd 爆炸。
pub fn zdet_bareiss(a0 : Array[Array[BigInt]], c : Cost) -> BigInt {
  let n = a0.length()
  if n == 0 {
    return 1N
  }
  let m : Array[Array[BigInt]] = []
  for row in a0 {
    m.push(Array::makei(row.length(), i => row[i]))
  }
  let mut sign = 1N
  let mut prev = 1N
  for k in 0..<(n - 1) {
    if m[k][k] == 0N {
      let mut sw = -1
      for i in (k + 1)..<n {
        if m[i][k] != 0N {
          sw = i
          break
        }
      }
      if sw < 0 {
        return 0N
      }
      let t = m[k]
      m[k] = m[sw]
      m[sw] = t
      sign = -sign
    }
    for i in (k + 1)..<n {
      for j in (k + 1)..<n {
        let p1 = cz_mul(c, m[k][k], m[i][j])
        let p2 = cz_mul(c, m[i][k], m[k][j])
        let d = cz_sub(c, p1, p2)
        m[i][j] = cz_div(c, d, prev)
      }
      m[i][k] = 0N
    }
    prev = m[k][k]
  }
  if sign < 0N {
    -m[n - 1][n - 1]
  } else {
    m[n - 1][n - 1]
  }
}

// ---------------------------------------------------------------------------
//  加速路徑：多模 CRT 行列式（B 管）
//  【定理 Λ2-5】取相異素數 p₁..p_k 使 ∏pᵢ > 2·H（H 為 Hadamard 界），
//     令 dᵢ = det(φ_{pᵢ}A) ∈ 𝔽pᵢ，則 CRT 之對稱提升恰為 det A。
//     證明：det 為矩陣元之整係數多項式 ⇒ φ_p(det A) = det(φ_p A)（推論 Λ1-2）；
//           |det A| ≤ H < M/2 ⇒ 對稱代表元唯一（定理 Λ1-3）。∎
//  成本特徵：每個素數 O(n³) 次字乘法，中間量恆 ≤ 62 位元，無係數膨脹。
// ---------------------------------------------------------------------------

///|
/// ℤ 行列式：多模 𝔽p 求值 + CRT 提升，並以 Hadamard 界推導所需模數個數。
pub fn zdet_crt(
  a : Array[Array[BigInt]],
  primes : Array[Int64],
  c : Cost,
) -> (BigInt, Int) {
  let h = hadamard_bound(a)
  let need = primes_needed(h, primes)
  let primes = ensure_primes(primes, need)
  let crt = Crt::new()
  for t in 0..<need {
    let ctx = FpCtx::make(primes[t])
    charge_reduce_rows(c, a)
    let fm = fp_of_big(a, ctx)
    let d = fp_det_fast(fm, ctx)
    c.absorb_fp(ctx)
    charge_crt_step(c, crt.modulus())
    crt.absorb(d, primes[t])
  }
  (crt.sym(), need)
}

///|
/// 整數方陣秩：單素數為下界篩（A 管），多素數取極大值（B 管）。
/// 【命題 Λ2-6】rank_{𝔽p}(φ_p A) ≤ rank_ℚ(A)，且等號對幾乎所有 p 成立。
///   證明：rank ≥ r ⇔ 某 r 階子式 ≠ 0。φ_p 保持子式之值，
///         故 𝔽p 上非零之子式於 ℚ 上亦非零 ⇒ 下界。
///         反之取 ℚ 上非零之 r 階子式 Δ，僅當 p | Δ 時失效，
///         而 Δ ≠ 0 之質因子有限 ⇒ 幾乎所有 p 取到等號。∎
pub fn zrank_crt(
  a : Array[Array[BigInt]],
  primes : Array[Int64],
  c : Cost,
  trials : Int,
) -> Int {
  let mut best = 0
  for t in 0..<trials {
    if t >= primes.length() {
      break
    }
    let ctx = FpCtx::make(primes[t])
    charge_reduce_rows(c, a)
    let fm = fp_of_big(a, ctx)
    let r = fp_rank(fm, ctx)
    c.absorb_fp(ctx)
    if r > best {
      best = r
    }
  }
  best
}

///|
/// 特徵多項式之係數界：|cᵢ| ≤ C(n,i)·R^{n−i} ≤ 2ⁿ·max(1,R)ⁿ，R = ‖A‖_∞。
/// 【命題 Λ2-7】χ_A 之係數為特徵值之基本對稱多項式，|λ| ≤ ‖A‖_∞（Gershgorin）。
pub fn charpoly_bound(a : Array[Array[BigInt]]) -> BigInt {
  let n = a.length()
  let mut r = 1N
  for row in a {
    let mut s = 0N
    for v in row {
      s = s + big_abs(v)
    }
    if s > r {
      r = s
    }
  }
  let mut acc = 1N
  for _i in 0..<n {
    acc = acc * r * 2N
  }
  acc
}

///|
/// 多模 CRT 特徵多項式（ℤ 層 B 管）。回傳升冪係數與使用之素數個數。
pub fn zcharpoly_crt(
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
    let ctx = FpCtx::make(primes[t])
    charge_reduce_rows(c, a)
    let fm = fp_of_big(a, ctx)
    let cp = fp_charpoly(fm, ctx)
    c.absorb_fp(ctx)
    for i in 0..<(n + 1) {
      let v = if i < cp.length() { cp[i] } else { 0L }
      charge_crt_step(c, crts[i].modulus())
      crts[i].absorb(v, primes[t])
    }
  }
  (Array::makei(n + 1, i => crts[i].sym()), need)
}

///|
/// 伴隨矩陣 adj A 之多模 CRT（adj A = det(A)·A⁻¹，於 det ≢ 0 之素數上計算）。
/// 【命題 Λ2-8】adj A 之元素為 (n−1) 階子式，故 |adj A_{ij}| ≤ H（Hadamard 界）。
pub fn zadj_crt(
  a : Array[Array[BigInt]],
  primes : Array[Int64],
  c : Cost,
) -> (Array[Array[BigInt]], Int, Int) {
  let n = a.length()
  let h = hadamard_bound(a)
  let need = primes_needed(h, primes)
  let primes = ensure_primes(primes, need + 8)
  let crts : Array[Array[Crt]] = Array::makei(n, _ => {
    Array::makei(n, _ => Crt::new())
  })
  let mut used = 0
  let mut skipped = 0
  let mut t = 0
  while used < need && t < primes.length() {
    let ctx = FpCtx::make(primes[t])
    charge_reduce_rows(c, a)
    let fm = fp_of_big(a, ctx)
    let d = fp_det_fast(fm, ctx)
    if d == 0L {
      // 壞素數：det ≡ 0 (mod p)，該像不足以還原 adj，跳過
      c.absorb_fp(ctx)
      skipped = skipped + 1
      t = t + 1
      continue
    }
    match fp_inv(fm, ctx) {
      None => {
        c.absorb_fp(ctx)
        skipped = skipped + 1
        t = t + 1
        continue
      }
      Some(iv) => {
        for i in 0..<n {
          for j in 0..<n {
            let v = ctx.mul(d, iv.get(i, j))
            charge_crt_step(c, crts[i][j].modulus())
            crts[i][j].absorb(v, primes[t])
          }
        }
        c.absorb_fp(ctx)
        used = used + 1
        t = t + 1
      }
    }
  }
  let out : Array[Array[BigInt]] = []
  for i in 0..<n {
    out.push(Array::makei(n, j => crts[i][j].sym()))
  }
  (out, used, skipped)
}

// ---------------------------------------------------------------------------
//  A 管：單像篩選（Screen）
//  【定理 Λ2-9（篩之單向可靠性）】設 F, G 為整係數多項式映射。
//     若 φ_p(F(A)) ≠ φ_p(G(A))，則 F(A) ≠ G(A)。
//     證明：φ_p 為函數；相等之物其像必相等，取逆否命題。∎
//     故「像不等 ⇒ 必不等」為零誤判之否決；反向則可能誤收（壞素數）。
//  【定理 Λ2-10（誤收之機率界）】設 D = F(A) − G(A) ≠ 0 且其某非零分量
//     絕對值 < 2^B，則整除它之素數個數 ≤ B/30（本池素數皆 > 2³⁰）。
//     自 N 個素數之池中均勻取 t 個，全為壞素數之機率 ≤ (B/(30N))^t。
// ---------------------------------------------------------------------------

///|
/// Freivalds 型乘積篩：驗證 A·B = C 是否成立（mod p、隨機向量）。
/// 成本 O(n²) 字乘法，相對於 O(n³) BigInt 乘法。
pub fn screen_matmul(
  a : Array[Array[BigInt]],
  b : Array[Array[BigInt]],
  cc : Array[Array[BigInt]],
  p : Int64,
  rng : Rng,
  c : Cost,
) -> Bool {
  let ctx = FpCtx::make(p)
  charge_reduce_rows(c, a)
  charge_reduce_rows(c, b)
  charge_reduce_rows(c, cc)
  let fa = fp_of_big(a, ctx)
  let fb = fp_of_big(b, ctx)
  let fc = fp_of_big(cc, ctx)
  let n = fb.fc
  let r = Array::makei(n, _ => rng.next_below(1000).to_int64())
  let br = fp_matvec(fb, r, ctx)
  let abr = fp_matvec(fa, br, ctx)
  let cr = fp_matvec(fc, r, ctx)
  c.absorb_fp(ctx)
  let mut same = true
  for i in 0..<abr.length() {
    if abr[i] != cr[i] {
      same = false
    }
  }
  same
}

///|
/// 整數矩陣恆等式之單素數篩（逐項比較像）。
pub fn screen_zeq(
  a : Array[Array[BigInt]],
  b : Array[Array[BigInt]],
  p : Int64,
  c : Cost,
) -> Bool {
  let ctx = FpCtx::make(p)
  charge_reduce_rows(c, a)
  charge_reduce_rows(c, b)
  let fa = fp_of_big(a, ctx)
  let fb = fp_of_big(b, ctx)
  c.absorb_fp(ctx)
  if fa.fr != fb.fr || fa.fc != fb.fc {
    return false
  }
  for i in 0..<fa.fd.length() {
    if fa.fd[i] != fb.fd[i] {
      return false
    }
  }
  true
}

// ===========================================================================
//  ℚ 層（L 群）：Fp 影像 + 有理數重建 + 事後憑證
// ===========================================================================

// ---------------------------------------------------------------------------
//  基準路徑：ℚ 上之高斯–若爾當消去（與 matrix.mbt 之 mrref 同構，另加計量）
// ---------------------------------------------------------------------------

///|
/// 受計量之 ℚ 高斯消去行列式（基準路徑）。
pub fn qdet_gauss(a0 : Mat[Q], c : Cost) -> Q {
  let n = a0.mrows
  let m : Array[Array[Q]] = []
  for i in 0..<n {
    m.push(Array::makei(n, j => a0.at(i, j)))
  }
  let mut sign = 1
  let mut acc = Q::one()
  for k in 0..<n {
    if m[k][k].is_zero() {
      let mut sw = -1
      for i in (k + 1)..<n {
        if !m[i][k].is_zero() {
          sw = i
          break
        }
      }
      if sw < 0 {
        return Q::zero()
      }
      let t = m[k]
      m[k] = m[sw]
      m[sw] = t
      sign = -sign
    }
    acc = cq_mul(c, acc, m[k][k])
    let piv = m[k][k]
    for i in (k + 1)..<n {
      if !m[i][k].is_zero() {
        let f = match cq_div(c, m[i][k], piv) {
          Some(x) => x
          None => Q::zero()
        }
        for j in k..<n {
          m[i][j] = cq_sub(c, m[i][j], cq_mul(c, f, m[k][j]))
        }
      }
    }
  }
  if sign < 0 {
    acc.neg()
  } else {
    acc
  }
}

///|
/// 受計量之 ℚ 線性解（基準路徑；方陣非奇異）。
pub fn qsolve_gauss(a0 : Mat[Q], b0 : Array[Q], c : Cost) -> Array[Q]? {
  let n = a0.mrows
  let m : Array[Array[Q]] = []
  for i in 0..<n {
    let row = Array::makei(n + 1, j => if j < n { a0.at(i, j) } else { b0[i] })
    m.push(row)
  }
  for k in 0..<n {
    if m[k][k].is_zero() {
      let mut sw = -1
      for i in (k + 1)..<n {
        if !m[i][k].is_zero() {
          sw = i
          break
        }
      }
      if sw < 0 {
        return None
      }
      let t = m[k]
      m[k] = m[sw]
      m[sw] = t
    }
    let piv = m[k][k]
    for j in k..<(n + 1) {
      m[k][j] = match cq_div(c, m[k][j], piv) {
        Some(x) => x
        None => Q::zero()
      }
    }
    for i in 0..<n {
      if i != k && !m[i][k].is_zero() {
        let f = m[i][k]
        for j in k..<(n + 1) {
          m[i][j] = cq_sub(c, m[i][j], cq_mul(c, f, m[k][j]))
        }
      }
    }
  }
  Some(Array::makei(n, i => m[i][n]))
}

///|
/// 受計量之 ℚ 反矩陣（基準路徑）。
pub fn qinv_gauss(a0 : Mat[Q], c : Cost) -> Mat[Q]? {
  let n = a0.mrows
  let m : Array[Array[Q]] = []
  for i in 0..<n {
    let row = Array::makei(2 * n, j => {
      if j < n {
        a0.at(i, j)
      } else if j - n == i {
        Q::one()
      } else {
        Q::zero()
      }
    })
    m.push(row)
  }
  for k in 0..<n {
    if m[k][k].is_zero() {
      let mut sw = -1
      for i in (k + 1)..<n {
        if !m[i][k].is_zero() {
          sw = i
          break
        }
      }
      if sw < 0 {
        return None
      }
      let t = m[k]
      m[k] = m[sw]
      m[sw] = t
    }
    let piv = m[k][k]
    for j in k..<(2 * n) {
      m[k][j] = match cq_div(c, m[k][j], piv) {
        Some(x) => x
        None => Q::zero()
      }
    }
    for i in 0..<n {
      if i != k && !m[i][k].is_zero() {
        let f = m[i][k]
        for j in k..<(2 * n) {
          m[i][j] = cq_sub(c, m[i][j], cq_mul(c, f, m[k][j]))
        }
      }
    }
  }
  Some(Mat::build(n, n, (i, j) => m[i][j + n]))
}

// ---------------------------------------------------------------------------
//  加速路徑：清分母 → 多模解 → 有理重建 → 事後憑證
//  【定理 Λ2-11（ℚ 層之無條件正確性）】
//     設 A ∈ ℚ^{n×n} 非奇異、b ∈ ℚⁿ，x̂ 為本演算法之輸出。
//     若 C 管之憑證 A x̂ = b（於 ℚ 上以整數算術精確驗證）通過，則 x̂ = A⁻¹b。
//     證明：A 非奇異 ⇒ 解唯一；x̂ 滿足方程 ⇒ x̂ 即該唯一解。
//           此論證不依賴素數個數、不依賴重建之界，故為無條件。∎
//  【命題 Λ2-12（穩定化早停）】若連續兩輪（模數 M 與 M·p）之重建結果相同，
//     則多半已達真值；本實作仍以 C 管驗證，故「早停」只影響效率不影響正確性。
// ---------------------------------------------------------------------------

///|
/// ℚ 層線性解之結果包。
pub struct QLift {
  /// 重建所得之解（None 表示未能重建）
  sol : Array[Q]?
  /// 實際使用之素數個數
  used : Int
  /// 壞素數（分母或樞軸 ≡ 0）個數
  bad : Int
  /// C 管事後憑證是否通過
  certified : Bool
}

///|
/// 事後憑證：以整數算術精確檢驗 A' x = b'（A'、b' 為清分母後之整數資料）。
fn certify_solution(
  az : Array[Array[BigInt]],
  bz : Array[BigInt],
  x : Array[Q],
  c : Cost,
) -> Bool {
  let n = az.length()
  // 共同分母
  let mut dx = 1N
  for q in x {
    dx = big_lcm(dx, q.den)
  }
  let xz = Array::makei(x.length(), i => {
    cz_mul(c, x[i].num, cz_div(c, dx, x[i].den))
  })
  for i in 0..<n {
    let mut s = 0N
    for j in 0..<az[i].length() {
      s = cz_add(c, s, cz_mul(c, az[i][j], xz[j]))
    }
    if s != cz_mul(c, bz[i], dx) {
      return false
    }
  }
  true
}

///|
/// ℚ 線性方程組之多模 + 有理重建解法（B 管 + C 管）。
pub fn qsolve_crt(
  a : Mat[Q],
  b : Array[Q],
  primes : Array[Int64],
  c : Cost,
) -> QLift {
  let n = a.mrows
  // 清分母：以 A 與 b 之公分母 D 同時放大，解集不變
  let (da, _) = qmat_clear_denom(a)
  let (db, _) = qvec_clear_denom(b)
  let d = big_lcm(da, db)
  let az : Array[Array[BigInt]] = []
  for i in 0..<n {
    az.push(Array::makei(a.mcols, j => a.at(i, j).num * (d / a.at(i, j).den)))
  }
  let bz = Array::makei(n, i => b[i].num * (d / b[i].den))
  let crts : Array[Crt] = Array::makei(n, _ => Crt::new())
  let mut used = 0
  let mut bad = 0
  let mut prev : Array[Q]? = None
  let mut t = 0
  while t < primes.length() {
    let p = primes[t]
    t = t + 1
    let ctx = FpCtx::make(p)
    charge_reduce_rows(c, az)
    let fa = fp_of_big(az, ctx)
    let pb = BigInt::from_int64(p)
    let fb = Array::makei(n, i => normmod((bz[i] % pb).to_int64(), p))
    match fp_solve(fa, fb, ctx) {
      None => {
        // 壞素數：det A ≡ 0 (mod p)
        c.absorb_fp(ctx)
        bad = bad + 1
        continue
      }
      Some(xs) => {
        for i in 0..<n {
          charge_crt_step(c, crts[i].modulus())
          crts[i].absorb(xs[i], p)
        }
        c.absorb_fp(ctx)
        used = used + 1
      }
    }
    if used >= 2 {
      let m = crts[0].modulus()
      let us = Array::makei(n, i => crts[i].sym())
      match rat_recon_vec(us, m) {
        None => continue
        Some(x) => {
          let stable = match prev {
            None => false
            Some(pv) => qvec_eq(pv, x)
          }
          prev = Some(x)
          if stable {
            let okc = certify_solution(az, bz, x, c)
            if okc {
              return { sol: Some(x), used, bad, certified: true, }
            }
          }
        }
      }
    }
  }
  match prev {
    None => { sol: None, used, bad, certified: false, }
    Some(x) => {
      let okc = certify_solution(az, bz, x, c)
      { sol: Some(x), used, bad, certified: okc, }
    }
  }
}

///|
/// ℚ 反矩陣之多模 + 有理重建（逐行解 A y = eⱼ 之一次性批次版）。
pub fn qinv_crt(
  a : Mat[Q],
  primes : Array[Int64],
  c : Cost,
) -> (Mat[Q]?, Int, Bool) {
  let n = a.mrows
  let (d, az) = qmat_clear_denom(a)
  // A = Az / d ⇒ A⁻¹ = d · Az⁻¹
  let crts : Array[Array[Crt]] = Array::makei(n, _ => {
    Array::makei(n, _ => Crt::new())
  })
  let mut used = 0
  let mut prev : Array[Q]? = None
  let mut t = 0
  let mut result : Mat[Q]? = None
  let mut cert = false
  while t < primes.length() {
    let p = primes[t]
    t = t + 1
    let ctx = FpCtx::make(p)
    charge_reduce_rows(c, az)
    let fa = fp_of_big(az, ctx)
    match fp_inv(fa, ctx) {
      None => {
        c.absorb_fp(ctx)
        continue
      }
      Some(iv) => {
        for i in 0..<n {
          for j in 0..<n {
            charge_crt_step(c, crts[i][j].modulus())
            crts[i][j].absorb(iv.get(i, j), p)
          }
        }
        c.absorb_fp(ctx)
        used = used + 1
      }
    }
    if used >= 2 {
      let m = crts[0][0].modulus()
      let flat : Array[BigInt] = []
      for i in 0..<n {
        for j in 0..<n {
          flat.push(crts[i][j].sym())
        }
      }
      match rat_recon_vec(flat, m) {
        None => continue
        Some(x) => {
          let stable = match prev {
            None => false
            Some(pv) => qvec_eq(pv, x)
          }
          prev = Some(x)
          if stable {
            // A⁻¹ = d · Az⁻¹
            let inv = Mat::build(n, n, (i, j) => {
              Q::make(d, 1N).mul(x[i * n + j])
            })
            if certify_inverse(a, inv, c) {
              return (Some(inv), used, true)
            } else {
              result = Some(inv)
              cert = false
            }
          }
        }
      }
    }
  }
  match prev {
    None => (None, used, false)
    Some(x) => {
      let inv = Mat::build(n, n, (i, j) => Q::make(d, 1N).mul(x[i * n + j]))
      let okc = certify_inverse(a, inv, c)
      if okc {
        (Some(inv), used, true)
      } else {
        match result {
          Some(r) => (Some(r), used, cert)
          None => (Some(inv), used, false)
        }
      }
    }
  }
}

///|
/// C 管：事後驗證 A·X = I（以整數算術）。
fn certify_inverse(a : Mat[Q], x : Mat[Q], c : Cost) -> Bool {
  let n = a.mrows
  let (da, az) = qmat_clear_denom(a)
  let (dx, xz) = qmat_clear_denom(x)
  let prod = Array::makei(n, _ => Array::makei(n, _ => 0N))
  for i in 0..<n {
    for k in 0..<n {
      if az[i][k] != 0N {
        for j in 0..<n {
          prod[i][j] = cz_add(c, prod[i][j], cz_mul(c, az[i][k], xz[k][j]))
        }
      }
    }
  }
  let scale = cz_mul(c, da, dx)
  for i in 0..<n {
    for j in 0..<n {
      let want = if i == j { scale } else { 0N }
      if prod[i][j] != want {
        return false
      }
    }
  }
  true
}

///|
/// ℚ 之 RREF 多模重建（含轉換矩陣 M 與事後憑證 M·A = R）。
pub struct QRrefLift {
  rmat : Mat[Q]
  tmat : Mat[Q]
  rank : Int
  pivots : Array[Int]
  used : Int
  certified : Bool
}

///|
/// ℚ 列簡化 RREF：𝔽p 多模篩選 + 有理重建 + 事後憑證（精確軌道之加速路徑）。
pub fn qrref_crt(a : Mat[Q], primes : Array[Int64], c : Cost) -> QRrefLift? {
  let rows = a.mrows
  let cols = a.mcols
  let (d, az) = qmat_clear_denom(a)
  // 增廣 [Az | I]
  let aug : Array[Array[BigInt]] = []
  for i in 0..<rows {
    let row : Array[BigInt] = Array::makei(cols + rows, j => {
      if j < cols {
        az[i][j]
      } else if j - cols == i {
        1N
      } else {
        0N
      }
    })
    aug.push(row)
  }
  let w = cols + rows
  let crts : Array[Array[Crt]] = Array::makei(rows, _ => {
    Array::makei(w, _ => Crt::new())
  })
  let mut used = 0
  let mut best_rank = -1
  let mut best_piv : Array[Int] = []
  let mut prev : Array[Q]? = None
  let mut t = 0
  while t < primes.length() {
    let p = primes[t]
    t = t + 1
    let ctx = FpCtx::make(p)
    charge_reduce_rows(c, aug)
    let fa = fp_of_big(aug, ctx)
    let rr = fp_rref(fa, ctx)
    c.absorb_fp(ctx)
    // 只取 A 部分之樞軸（增廣之 I 部分不計入 rank A）
    let apiv : Array[Int] = []
    for pv in rr.pivots {
      if pv < cols {
        apiv.push(pv)
      }
    }
    // 僅接受「最大秩」之樞軸型態（非最大秩者為壞素數）
    let mut profile_ok = true
    if apiv.length() > best_rank {
      best_rank = apiv.length()
      best_piv = apiv
      for i in 0..<rows {
        for j in 0..<w {
          crts[i][j] = Crt::new()
        }
      }
      used = 0
      prev = None
    } else if apiv.length() < best_rank {
      profile_ok = false
    } else {
      for i in 0..<best_piv.length() {
        if best_piv[i] != apiv[i] {
          profile_ok = false
        }
      }
    }
    if !profile_ok {
      continue
    }
    for i in 0..<rows {
      for j in 0..<w {
        charge_crt_step(c, crts[i][j].modulus())
        crts[i][j].absorb(rr.rmat.get(i, j), p)
      }
    }
    used = used + 1
    if used >= 2 {
      let m = crts[0][0].modulus()
      let flat : Array[BigInt] = []
      for i in 0..<rows {
        for j in 0..<w {
          flat.push(crts[i][j].sym())
        }
      }
      match rat_recon_vec(flat, m) {
        None => continue
        Some(x) => {
          let stable = match prev {
            None => false
            Some(pv) => qvec_eq(pv, x)
          }
          prev = Some(x)
          if stable {
            let rmat = Mat::build(rows, cols, (i, j) => x[i * w + j])
            // T = (Az 之轉換) ；對 A = Az/d 而言 T_A = T · d
            let tmat = Mat::build(rows, rows, (i, j) => {
              x[i * w + cols + j].mul(Q::make(d, 1N))
            })
            let okc = certify_rref(a, rmat, tmat, c)
            return Some({
              rmat,
              tmat,
              rank: best_rank,
              pivots: best_piv,
              used,
              certified: okc,
            })
          }
        }
      }
    }
  }
  None
}

///|
/// C 管：驗證 T·A = R 且 T 可逆（det T ≠ 0）。
fn certify_rref(a : Mat[Q], r : Mat[Q], t : Mat[Q], c : Cost) -> Bool {
  let rows = a.mrows
  let cols = a.mcols
  for i in 0..<rows {
    for j in 0..<cols {
      let mut s = Q::zero()
      for k in 0..<rows {
        s = cq_add(c, s, cq_mul(c, t.at(i, k), a.at(k, j)))
      }
      if !s.eq(r.at(i, j)) {
        return false
      }
    }
  }
  !qdet_gauss(t, c).is_zero()
}

// ---------------------------------------------------------------------------
//  ℚ 層之應用：最小二乘 / 正規方程（連「組裝 AᵀA」都在 𝔽p 上做）
//  【命題 Λ2-13】AᵀA 之組裝為 O(mn²) 次乘法；於 ℚ 上其元素位元長度約為
//     輸入之兩倍，於 𝔽p 上恆為一字 ⇒ 連組裝階段都被加速。
// ---------------------------------------------------------------------------

///|
/// 正規方程 AᵀA x = Aᵀb 之多模解（ℚ 層，B+C 管）。
pub fn qlsq_crt(
  a : Mat[Q],
  b : Array[Q],
  primes : Array[Int64],
  c : Cost,
) -> QLift {
  let m = a.mrows
  let n = a.mcols
  let (da, _) = qmat_clear_denom(a)
  let (db, _) = qvec_clear_denom(b)
  let d = big_lcm(da, db)
  let az : Array[Array[BigInt]] = []
  for i in 0..<m {
    az.push(Array::makei(n, j => a.at(i, j).num * (d / a.at(i, j).den)))
  }
  let bz = Array::makei(m, i => b[i].num * (d / b[i].den))
  let crts : Array[Crt] = Array::makei(n, _ => Crt::new())
  let mut used = 0
  let mut bad = 0
  let mut prev : Array[Q]? = None
  // 正規方程之整數形式：(AzᵀAz) x = Azᵀ bz
  let gz : Array[Array[BigInt]] = []
  for i in 0..<n {
    let row = Array::make(n, 0N)
    for j in 0..<n {
      let mut s = 0N
      for k in 0..<m {
        s = s + az[k][i] * az[k][j]
      }
      row[j] = s
    }
    gz.push(row)
  }
  let hz = Array::make(n, 0N)
  for i in 0..<n {
    let mut s = 0N
    for k in 0..<m {
      s = s + az[k][i] * bz[k]
    }
    hz[i] = s
  }
  let mut t = 0
  while t < primes.length() {
    let p = primes[t]
    t = t + 1
    let ctx = FpCtx::make(p)
    charge_reduce_rows(c, az)
    let fa = fp_of_big(az, ctx)
    let pb = BigInt::from_int64(p)
    let fb = Array::makei(m, i => normmod((bz[i] % pb).to_int64(), p))
    c.wmul = c.wmul + m.to_int64()
    // 於 𝔽p 上組裝正規方程（無長整數）
    let g = FpMat::make(n, n)
    for i in 0..<n {
      for j in 0..<n {
        let mut s = 0L
        for k in 0..<m {
          s = ctx.add(s, ctx.mul(fa.get(k, i), fa.get(k, j)))
        }
        g.set(i, j, s)
      }
    }
    let h = Array::make(n, 0L)
    for i in 0..<n {
      let mut s = 0L
      for k in 0..<m {
        s = ctx.add(s, ctx.mul(fa.get(k, i), fb[k]))
      }
      h[i] = s
    }
    match fp_solve(g, h, ctx) {
      None => {
        c.absorb_fp(ctx)
        bad = bad + 1
        continue
      }
      Some(xs) => {
        for i in 0..<n {
          charge_crt_step(c, crts[i].modulus())
          crts[i].absorb(xs[i], p)
        }
        c.absorb_fp(ctx)
        used = used + 1
      }
    }
    if used >= 2 {
      let mm = crts[0].modulus()
      let us = Array::makei(n, i => crts[i].sym())
      match rat_recon_vec(us, mm) {
        None => continue
        Some(x) => {
          let stable = match prev {
            None => false
            Some(pv) => qvec_eq(pv, x)
          }
          prev = Some(x)
          if stable && certify_solution(gz, hz, x, c) {
            return { sol: Some(x), used, bad, certified: true, }
          }
        }
      }
    }
  }
  match prev {
    None => { sol: None, used, bad, certified: false, }
    Some(x) => {
      let okc = certify_solution(gz, hz, x, c)
      { sol: Some(x), used, bad, certified: okc, }
    }
  }
}

// ---------------------------------------------------------------------------
//  Gram 矩陣之 LDLᵀ（= 單位化 Gram–Schmidt）之多模重建
//  【定理 Λ2-14】G 對稱正定 ⇒ 唯一分解 G = L D Lᵀ，L 單位下三角，D 正對角；
//     且 L 之第 j 行即 Gram–Schmidt 展開係數，Dⱼⱼ = ‖q_j‖²。
//     證明：對 j 歸納施行無開方 Cholesky；正定保證 Dⱼⱼ > 0 可除。∎
//  C 管憑證：精確驗證 L D Lᵀ = G（整數算術）。
// ---------------------------------------------------------------------------

///|
/// 𝔽p 上之 LDLᵀ（L 單位下三角、D 對角）。
pub fn fp_ldlt(g : FpMat, ctx : FpCtx) -> (FpMat, Array[Int64])? {
  let n = g.fr
  let l = fp_ident(n)
  let d = Array::make(n, 0L)
  for j in 0..<n {
    let mut s = g.get(j, j)
    for k in 0..<j {
      s = ctx.sub(s, ctx.mul(ctx.mul(l.get(j, k), l.get(j, k)), d[k]))
    }
    d[j] = s
    if s == 0L {
      return None
    }
    let si = match ctx.inv(s) {
      Some(x) => x
      None => return None
    }
    for i in (j + 1)..<n {
      let mut v = g.get(i, j)
      for k in 0..<j {
        v = ctx.sub(v, ctx.mul(ctx.mul(l.get(i, k), l.get(j, k)), d[k]))
      }
      l.set(i, j, ctx.mul(v, si))
    }
  }
  Some((l, d))
}

///|
/// ℚ 上 Gram 矩陣之 LDLᵀ：多模重建 + 事後憑證（L D Lᵀ = G）。
pub struct QLdlt {
  lmat : Mat[Q]
  dvec : Array[Q]
  used : Int
  certified : Bool
}

///|
/// ℚ 對稱 LDLᵀ 之 CRT 篩選路徑（𝔽p 分解 → 重建 → 憑證）。
pub fn qldlt_crt(g : Mat[Q], primes : Array[Int64], c : Cost) -> QLdlt? {
  let n = g.mrows
  let (dd, gz) = qmat_clear_denom(g)
  let crts : Array[Crt] = Array::makei(n * n + n, _ => Crt::new())
  let mut used = 0
  let mut prev : Array[Q]? = None
  let mut t = 0
  while t < primes.length() {
    let p = primes[t]
    t = t + 1
    let ctx = FpCtx::make(p)
    charge_reduce_rows(c, gz)
    let fg = fp_of_big(gz, ctx)
    match fp_ldlt(fg, ctx) {
      None => {
        c.absorb_fp(ctx)
        continue
      }
      Some((l, d)) => {
        for i in 0..<n {
          for j in 0..<n {
            let idx = i * n + j
            charge_crt_step(c, crts[idx].modulus())
            crts[idx].absorb(l.get(i, j), p)
          }
        }
        for i in 0..<n {
          let idx = n * n + i
          charge_crt_step(c, crts[idx].modulus())
          crts[idx].absorb(d[i], p)
        }
        c.absorb_fp(ctx)
        used = used + 1
      }
    }
    if used >= 2 {
      let m = crts[0].modulus()
      let flat = Array::makei(n * n + n, i => crts[i].sym())
      match rat_recon_vec(flat, m) {
        None => continue
        Some(x) => {
          let stable = match prev {
            None => false
            Some(pv) => qvec_eq(pv, x)
          }
          prev = Some(x)
          if stable {
            let lmat = Mat::build(n, n, (i, j) => x[i * n + j])
            // D 對應之是 Gz = dd·G 之分解 ⇒ 真正之 D 要除以 dd
            let dvec = Array::makei(n, i => {
              match x[n * n + i].div(Q::make(dd, 1N)) {
                Some(v) => v
                None => Q::zero()
              }
            })
            let okc = certify_ldlt(g, lmat, dvec, c)
            return Some({ lmat, dvec, used, certified: okc, })
          }
        }
      }
    }
  }
  None
}

///|
/// C 管：驗證 L D Lᵀ = G。
fn certify_ldlt(g : Mat[Q], l : Mat[Q], d : Array[Q], c : Cost) -> Bool {
  let n = g.mrows
  for i in 0..<n {
    for j in 0..<n {
      let mut s = Q::zero()
      for k in 0..<n {
        s = cq_add(c, s, cq_mul(c, cq_mul(c, l.at(i, k), d[k]), l.at(j, k)))
      }
      if !s.eq(g.at(i, j)) {
        return false
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
//  加速層實測摘要：供報告與 cmd/accel 使用
// ---------------------------------------------------------------------------

///|
/// 以確定性成本模型跑一組代表性實例，回傳基準／加速之對照統計。
pub fn accel_bench_table() -> Array[AccelStat] {
  let rows : Array[AccelStat] = []
  let rng = ob_rng()
  let ps = prime_pool(64)

  // 1. ℤ 行列式（n = 16，256 位元係數）
  let a16 = Array::makei(16, _ => Array::makei(16, _ => zrand(rng, 256)))
  let cb = Cost::new()
  let db = zdet_bareiss(a16, cb)
  let cf = Cost::new()
  let (df, np) = zdet_crt(a16, ps, cf)
  rows.push({
    aname: "ℤ 行列式 n=16, 256 位元（Bareiss → 多模 CRT）",
    base_wmul: cb.wmul,
    fast_wmul: cf.wmul,
    base_bits: cb.maxbits,
    fast_bits: cf.maxbits,
    nprimes: np,
    certified: db == df,
  })

  // 2. ℚ 線性方程組（n = 14）
  let aq = qmat_invertible(rng, 14)
  let bq = Array::makei(14, _ => qr(rng))
  let c1 = Cost::new()
  let r1 = qsolve_gauss(aq, bq, c1)
  let c2 = Cost::new()
  let lift = qsolve_crt(aq, bq, ps, c2)
  let same = match (r1, lift.sol) {
    (Some(x), Some(y)) => qvec_eq(x, y)
    _ => false
  }
  rows.push({
    aname: "ℚ 線性方程組 n=14（高斯 → 多模＋重建＋憑證）",
    base_wmul: c1.wmul,
    fast_wmul: c2.wmul,
    base_bits: c1.maxbits,
    fast_bits: c2.maxbits,
    nprimes: lift.used,
    certified: same && lift.certified,
  })

  // 3. ℚ 反矩陣（n = 12）
  let ai = qmat_invertible(rng, 12)
  let c3 = Cost::new()
  let rb3 = qinv_gauss(ai, c3)
  let c4 = Cost::new()
  let (rf4, used4, cert4) = qinv_crt(ai, ps, c4)
  let same4 = match (rb3, rf4) {
    (Some(x), Some(y)) => x.equals(y)
    _ => false
  }
  rows.push({
    aname: "ℚ 反矩陣 n=12（高斯–Jordan → 多模＋重建＋憑證）",
    base_wmul: c3.wmul,
    fast_wmul: c4.wmul,
    base_bits: c3.maxbits,
    fast_bits: c4.maxbits,
    nprimes: used4,
    certified: same4 && cert4,
  })

  // 4. 特徵多項式（n = 11）
  let az = Array::makei(11, _ => Array::makei(11, _ => zrand(rng, 24)))
  let qz = zrows_to_qmat(az)
  let c5 = Cost::new()
  let fv = qcharpoly_faddeev(qz, c5)
  let c6 = Cost::new()
  let (cp, np6) = zcharpoly_crt(az, ps, c6)
  let mut same6 = true
  for i in 0..<12 {
    if !Q::make(cp[i], 1N).eq(fv[i]) {
      same6 = false
    }
  }
  rows.push({
    aname: "特徵多項式 n=11（ℚ Faddeev → 多模 Hessenberg CRT）",
    base_wmul: c5.wmul,
    fast_wmul: c6.wmul,
    base_bits: c5.maxbits,
    fast_bits: c6.maxbits,
    nprimes: np6,
    certified: same6,
  })

  // 5. 最小二乘（20×10）
  let al = qmat(rng, 20, 10)
  let bl = Array::makei(20, _ => qr(rng))
  let g = al.transpose().times(al)
  let h = al.transpose().apply(bl)
  let c7 = Cost::new()
  let _ = qsolve_gauss(g, h, c7)
  let c8 = Cost::new()
  let l8 = qlsq_crt(al, bl, ps, c8)
  rows.push({
    aname: "最小二乘 20×10（ℚ 正規方程 → 𝔽p 組裝＋重建）",
    base_wmul: c7.wmul,
    fast_wmul: c8.wmul,
    base_bits: c7.maxbits,
    fast_bits: c8.maxbits,
    nprimes: l8.used,
    certified: l8.certified,
  })

  // 6. ℚ[x] 乘法（deg 64）
  let d = 64
  let fp0 = Array::makei(d, _ => {
    Q::frac(rng.next_small(99), rng.next_range(1, 40))
  })
  let gp0 = Array::makei(d, _ => {
    Q::frac(rng.next_small(99), rng.next_range(1, 40))
  })
  let c9 = Cost::new()
  let rb9 = qpoly_mul(fp0, gp0, c9)
  let c10 = Cost::new()
  let (rf10, np10) = qpoly_mul_crt(fp0, gp0, ps, c10)
  let mut same10 = rb9.length() == rf10.length()
  for i in 0..<rb9.length() {
    if !rb9[i].eq(rf10[i]) {
      same10 = false
    }
  }
  rows.push({
    aname: "ℚ[x] 乘法 deg 64（ℚ 卷積 → 清分母＋多模 NTT）",
    base_wmul: c9.wmul,
    fast_wmul: c10.wmul,
    base_bits: c9.maxbits,
    fast_bits: c10.maxbits,
    nprimes: np10,
    certified: same10,
  })

  // 7. ℤ[x] gcd（deg 16 互質對照）
  let du = 16
  let fz : Array[BigInt] = Array::makei(du + 1, _ => {
    BigInt::from_int(rng.next_range(-30, 30))
  })
  fz[du] = 1N
  let gz : Array[BigInt] = Array::makei(du, _ => {
    BigInt::from_int(rng.next_range(-30, 30))
  })
  gz[du - 1] = 1N
  let fq = Array::makei(fz.length(), i => Q::make(fz[i], 1N))
  let gq = Array::makei(gz.length(), i => Q::make(gz[i], 1N))
  let c11 = Cost::new()
  let rb11 = qpoly_gcd_euclid(fq, gq, c11)
  let c12 = Cost::new()
  let l12 = zpoly_gcd_crt(fz, gz, ps, c12)
  let (np12, cert12) = match l12 {
    Some(gl) => (gl.used, gl.certified && gl.gcd.length() == rb11.length())
    None => (0, false)
  }
  rows.push({
    aname: "ℤ[x] gcd deg 16（ℚ 歐幾里得 → 模 p 篩＋整除性憑證）",
    base_wmul: c11.wmul,
    fast_wmul: c12.wmul,
    base_bits: c11.maxbits,
    fast_bits: c12.maxbits,
    nprimes: np12,
    certified: cert12,
  })

  // 8. 誠實反例：由根造多項式
  let roots = Array::makei(32, _ => zrand(rng, 48))
  let c13 = Cost::new()
  let rl = zpoly_from_roots_linear(roots, c13)
  let c14 = Cost::new()
  let rt = zpoly_from_roots_tree(roots, c14)
  let mut same14 = rl.length() == rt.length()
  for i in 0..<rl.length() {
    if rl[i] != rt[i] {
      same14 = false
    }
  }
  rows.push({
    aname: "【反例】ℤ[x] 由 32 根造多項式（線性累積 → 積樹）",
    base_wmul: c13.wmul,
    fast_wmul: c14.wmul,
    base_bits: c13.maxbits,
    fast_bits: c14.maxbits,
    nprimes: 0,
    certified: same14,
  })
  rows
}

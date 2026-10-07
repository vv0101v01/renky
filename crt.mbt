// ============================================================================
//  檔案 20：crt.mbt — 加速層 Λ1：中國剩餘定理、對稱提升、有理數重建
//
//  本檔把「許多個 𝔽p 上之答案」縫回「一個 ℤ 上之答案」或「一個 ℚ 上之答案」。
//  兩條縫法對應兩個不同之層：
//    ℤ 層（純整數純 CRT）：CRT ⊕ 對稱提升，先驗界為 Hadamard 界。
//    ℚ 層（Fp 層級有理數重建）：CRT ⊕ 擴充歐幾里得之格重建（Wang）。
//
//  【定理 Λ1-1（中國剩餘定理）】p₁,…,p_k 兩兩互素，M = ∏pᵢ，則環同構
//      ℤ/Mℤ ≅ ℤ/p₁ℤ × … × ℤ/p_kℤ,  x ↦ (x mod p₁, …, x mod p_k)。
//    證明：映射顯為環同態；核為 {x : ∀i, pᵢ | x} = Mℤ（互素 ⇒ lcm = ∏）；
//          兩側基數同為 M ⇒ 由第一同構定理得雙射。∎
//  【推論 Λ1-2（計算之可分解性）】凡「只用 +, −, ×」之演算法（行列式、
//    特徵多項式、伴隨矩陣、結式、卷積…）皆與約化 φ_p 交換：
//        φ_p(F(A)) = F(φ_p(A))。
//    故可逐素數平行計算，再以 CRT 縫合。證明：φ_p 為環同態，而 F 為
//    由 +, −, × 組成之多項式映射，環同態保持多項式映射。∎
//  【定理 Λ1-3（對稱提升之唯一性）】若 |x| < M/2 且 x ≡ u (mod M)，則
//    x 為 u 於 (−M/2, M/2] 中之唯一代表元。
//    證明：兩代表之差為 M 之倍數且絕對值 < M ⇒ 差為 0。∎
// ============================================================================

///|
/// 位元長度（|a| 之二進位長度；0 ↦ 0）。
pub fn big_bits(a : BigInt) -> Int {
  a.bit_length()
}

///|
/// 以 64 位元為一字計之字數（至少 1）。
pub fn big_words(a : BigInt) -> Int64 {
  let b = a.bit_length()
  let w = (b + 63) / 64
  if w < 1 {
    1L
  } else {
    w.to_int64()
  }
}

// ---------------------------------------------------------------------------
//  累進式 CRT（Garner 形式）
//  不變量：self.cval ∈ [0, self.cmod) 且對每個已吸收之 (rᵢ,pᵢ) 有
//          self.cval ≡ rᵢ (mod pᵢ)，self.cmod = ∏ pᵢ。
// ---------------------------------------------------------------------------

///|
pub struct Crt {
  mut cmod : BigInt
  mut cval : BigInt
  mut steps : Int
}

///|
pub fn Crt::new() -> Crt {
  { cmod: 1N, cval: 0N, steps: 0, }
}

///|
/// 吸收一組新的剩餘 (r mod p)；要求 gcd(p, cmod) = 1。
/// 公式：v' = v + m · ((r − v) · m⁻¹ mod p)，m' = m·p。
/// 【命題 Λ1-4】上式保持不變量：v' ≡ v (mod m) 且 v' ≡ r (mod p)。
///   證明：v' − v = m·t ⇒ v' ≡ v (mod m)；
///         v' ≡ v + m·(r−v)m⁻¹ ≡ v + (r−v) = r (mod p)。∎
pub fn Crt::absorb(self : Crt, r : Int64, p : Int64) -> Unit {
  let pb = BigInt::from_int64(p)
  let ctx = FpCtx::make(p)
  let mres = normmod((self.cmod % pb).to_int64(), p)
  let vres = normmod((self.cval % pb).to_int64(), p)
  let rr = normmod(r, p)
  match ctx.inv(mres) {
    None => return
    Some(minv) => {
      let diff = ctx.sub(rr, vres)
      let t = ctx.mul(diff, minv)
      self.cval = self.cval + self.cmod * BigInt::from_int64(t)
      self.cmod = self.cmod * pb
      self.steps = self.steps + 1
    }
  }
}

///|
/// 對稱代表元（置於 (−M/2, M/2]）。
pub fn Crt::sym(self : Crt) -> BigInt {
  let two_v = self.cval * 2N
  if two_v > self.cmod {
    self.cval - self.cmod
  } else {
    self.cval
  }
}

///|
/// 非負代表元。
pub fn Crt::value(self : Crt) -> BigInt {
  self.cval
}

///|
/// 目前之模數 M = ∏ pᵢ。
pub fn Crt::modulus(self : Crt) -> BigInt {
  self.cmod
}

// ---------------------------------------------------------------------------
//  Hadamard 界：決定「需要幾個素數」之先驗界
//  【定理 Λ1-5（Hadamard）】A ∈ ℝ^{n×n} ⇒ |det A| ≤ ∏ᵢ ‖aᵢ‖₂（列範數之積）。
//    證明：det A = det 之體積解釋 = 以列向量張成之平行多面體體積，
//          由 Gram–Schmidt 得各邊長不增：|det| = ∏‖a*ᵢ‖ ≤ ∏‖aᵢ‖。∎
//  【推論 Λ1-6】取 M = ∏pᵢ > 2·B（B 為 Hadamard 界），則對稱提升唯一且正確。
// ---------------------------------------------------------------------------

///|
/// 整數方陣之 Hadamard 界（上取整）。
pub fn hadamard_bound(a : Array[Array[BigInt]]) -> BigInt {
  let mut acc = 1N
  for row in a {
    let mut s = 0N
    for v in row {
      s = s + v * v
    }
    let r = big_isqrt(s) + 1N
    acc = acc * r
  }
  acc
}

///|
/// 確保素數池至少有 k 個素數（不足則重新生成；避免「池耗盡 ⇒ 提升不足 ⇒
/// 答案錯誤」之靜默失效）。
/// 【命題 Λ1-6′（安全性）】CRT 提升之正確性以 ∏pᵢ > 2B 為前提；
///   若池不足而仍輸出，則違反定理 Λ1-3 之前提，結果可能錯誤。
///   故所有提升型演算法皆須先呼叫本函數。
pub fn ensure_primes(primes : Array[Int64], k : Int) -> Array[Int64] {
  if primes.length() >= k {
    primes
  } else {
    prime_pool(k)
  }
}

///|
/// 由界 B 決定所需素數個數：最小 k 使 ∏ᵢ₌₁^k pᵢ > 2B。
/// 回傳值可能大於池長度；呼叫端須以 ensure_primes 補足。
pub fn primes_needed(b : BigInt, primes : Array[Int64]) -> Int {
  let target = b * 2N
  let mut m = 1N
  let mut k = 0
  // 池內素數皆 > 2³⁰，故以 2³⁰ 為保守下界估算池外之續增
  while m <= target {
    if k < primes.length() {
      m = m * BigInt::from_int64(primes[k])
    } else {
      m = m * 1073741824N
    }
    k = k + 1
  }
  k
}

// ---------------------------------------------------------------------------
//  有理數重建（rational reconstruction）
//  【定理 Λ1-7（Wang／唯一性）】設 M > 2ND，u ∈ ℤ/M。若存在 n/d 使
//      |n| ≤ N, 0 < d ≤ D, gcd(d,M)=1, n ≡ u·d (mod M)，
//    則該 n/d 唯一（作為既約分數），且可由對 (M,u) 之擴充歐幾里得
//    在第一個餘數 rᵢ ≤ N 處讀出：n = rᵢ, d = tᵢ。
//    證明（唯一性）：設 n₁/d₁, n₂/d₂ 皆滿足，則 n₁d₂ ≡ n₂d₁ (mod M)，
//      而 |n₁d₂ − n₂d₁| ≤ 2ND < M ⇒ n₁d₂ = n₂d₁ ⇒ 兩分數相等。
//    （存在性／可讀出性）歐幾里得餘數序列滿足 rᵢ = sᵢM + tᵢu，
//      且 |tᵢ|·rᵢ₋₁ < M；於 rᵢ ≤ N < rᵢ₋₁ 處即得 |tᵢ| < M/rᵢ₋₁ ≤ M/N ≤ 2D，
//      配合格之極小性論證得唯一候選。∎
//  【推論 Λ1-8（安全失敗）】若重建結果無法通過驗證 n ≡ u·d (mod M)
//    或超出界，則回 None —— 演算法「安全失敗」而非給出錯誤答案，
//    上層只需再加素數重試。
// ---------------------------------------------------------------------------

///|
/// 有界有理重建：於 |n| ≤ nb、0 < d ≤ db 中尋找 n/d ≡ u (mod m)。
pub fn rat_recon_bnd(u0 : BigInt, m : BigInt, nb : BigInt, db : BigInt) -> Q? {
  let mut u = u0 % m
  if u < 0N {
    u = u + m
  }
  if u == 0N {
    return Some(Q::zero())
  }
  let mut r0 = m
  let mut r1 = u
  let mut t0 = 0N
  let mut t1 = 1N
  while r1 > nb {
    if r1 == 0N {
      return None
    }
    let q = r0 / r1
    let r2 = r0 - q * r1
    let t2 = t0 - q * t1
    r0 = r1
    r1 = r2
    t0 = t1
    t1 = t2
  }
  if t1 == 0N {
    return None
  }
  let mut n = r1
  let mut d = t1
  if d < 0N {
    n = -n
    d = -d
  }
  if d > db {
    return None
  }
  if big_gcd(big_abs(n), d) != 1N {
    return None
  }
  if (n - u * d) % m != 0N {
    return None
  }
  Some(Q::make(n, d))
}

///|
/// 平衡界之有理重建：N = D = ⌊√((M−1)/2)⌋，滿足 2ND < M。
pub fn rat_recon(u : BigInt, m : BigInt) -> Q? {
  if m <= 1N {
    return None
  }
  let bound = big_isqrt((m - 1N) / 2N)
  rat_recon_bnd(u, m, bound, bound)
}

///|
/// 向量之逐座標有理重建（任一座標失敗則整體失敗）。
pub fn rat_recon_vec(us : Array[BigInt], m : BigInt) -> Array[Q]? {
  let out : Array[Q] = []
  for u in us {
    match rat_recon(u, m) {
      None => return None
      Some(q) => out.push(q)
    }
  }
  Some(out)
}

///|
/// 兩個有理向量是否逐座標相等（供「穩定化早停」判準）。
pub fn qvec_eq(a : Array[Q], b : Array[Q]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if !a[i].eq(b[i]) {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
//  ℚ ↔ ℤ 之清分母（把 ℚ 層問題化為 ℤ 層問題）
//  【命題 Λ1-9】設 A ∈ ℚ^{m×n}，D = lcm{分母}，則 DA ∈ ℤ^{m×n}；
//    且 Ax = b ⇔ (D_A A)x = D_A b 之解集相同（同乘非零純量）。
// ---------------------------------------------------------------------------

///|
pub fn big_lcm(a : BigInt, b : BigInt) -> BigInt {
  if a == 0N || b == 0N {
    return 0N
  }
  let g = big_gcd(big_abs(a), big_abs(b))
  big_abs(a) / g * big_abs(b)
}

///|
/// 矩陣之公分母與對應之整數矩陣。
pub fn qmat_clear_denom(a : Mat[Q]) -> (BigInt, Array[Array[BigInt]]) {
  let mut d = 1N
  for i in 0..<a.mrows {
    for j in 0..<a.mcols {
      d = big_lcm(d, a.at(i, j).den)
    }
  }
  let rows : Array[Array[BigInt]] = []
  for i in 0..<a.mrows {
    let row : Array[BigInt] = []
    for j in 0..<a.mcols {
      let q = a.at(i, j)
      row.push(q.num * (d / q.den))
    }
    rows.push(row)
  }
  (d, rows)
}

///|
/// 向量之公分母與對應之整數向量。
pub fn qvec_clear_denom(v : Array[Q]) -> (BigInt, Array[BigInt]) {
  let mut d = 1N
  for q in v {
    d = big_lcm(d, q.den)
  }
  let out : Array[BigInt] = []
  for q in v {
    out.push(q.num * (d / q.den))
  }
  (d, out)
}

///|
/// 整數列陣 → Mat[Q]（嵌入 ℤ ↪ ℚ）。
pub fn zrows_to_qmat(rows : Array[Array[BigInt]]) -> Mat[Q] {
  let r = rows.length()
  let c = if r == 0 { 0 } else { rows[0].length() }
  Mat::build(r, c, (i, j) => Q::make(rows[i][j], 1N))
}

///|
/// Mat[Q]（元素皆整數）→ 整數列陣。
pub fn qmat_to_zrows(a : Mat[Q]) -> Array[Array[BigInt]] {
  let rows : Array[Array[BigInt]] = []
  for i in 0..<a.mrows {
    let row : Array[BigInt] = []
    for j in 0..<a.mcols {
      row.push(a.at(i, j).num)
    }
    rows.push(row)
  }
  rows
}

///|
/// 整數矩陣乘法（供事後憑證；以 BigInt 直接計算）。
pub fn zrows_mul(
  a : Array[Array[BigInt]],
  b : Array[Array[BigInt]],
) -> Array[Array[BigInt]] {
  let n = a.length()
  let k = if n == 0 { 0 } else { a[0].length() }
  let m = if k == 0 { 0 } else { b[0].length() }
  let out : Array[Array[BigInt]] = []
  for i in 0..<n {
    let row = Array::make(m, 0N)
    for t in 0..<k {
      if a[i][t] != 0N {
        for j in 0..<m {
          row[j] = row[j] + a[i][t] * b[t][j]
        }
      }
    }
    out.push(row)
  }
  out
}

///|
/// 整數矩陣 × 整數向量。
pub fn zrows_mulvec(
  a : Array[Array[BigInt]],
  x : Array[BigInt],
) -> Array[BigInt] {
  let out : Array[BigInt] = []
  for row in a {
    let mut s = 0N
    for j in 0..<row.length() {
      s = s + row[j] * x[j]
    }
    out.push(s)
  }
  out
}

///|
/// 整數列陣之最大位元長度（量度「係數膨脹」）。
pub fn zrows_maxbits(a : Array[Array[BigInt]]) -> Int {
  let mut m = 0
  for row in a {
    for v in row {
      let b = big_bits(v)
      if b > m {
        m = b
      }
    }
  }
  m
}

///|
/// ℚ 矩陣之「資料位元寬」：max over entries of (bits(分子) + bits(分母))。
/// 供分派器估算基準路徑之係數膨脹規模。
pub fn qmat_bits(a : Mat[Q]) -> Int {
  let mut m = 1
  for i in 0..<a.mrows {
    for j in 0..<a.mcols {
      let q = a.at(i, j)
      let b = big_bits(q.num) + big_bits(q.den)
      if b > m {
        m = b
      }
    }
  }
  m
}

///|
/// 整數列陣之資料位元寬。
pub fn zrows_bits(a : Array[Array[BigInt]]) -> Int {
  let mut m = 1
  for row in a {
    for v in row {
      let b = big_bits(v)
      if b > m {
        m = b
      }
    }
  }
  m
}

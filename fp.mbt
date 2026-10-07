// ============================================================================
//  檔案 19：fp.mbt — 加速層 Λ0：素體 𝔽p 之原子層
//
//  本檔為三個加速層（ℤ 層／ℚ 層／𝔽[x] 層）共用之「機器字算術」底座。
//  全部運算之運算元恆 < 2³¹，故任意兩者之積 < 2⁶² 必不溢位 Int64：
//  這是「加速」之全部來源 —— 把無界長整數算術壓回單字算術。
//
//  【定義 Λ0-1】取素數 p < 2³¹，𝔽p = ℤ/pℤ 為含 p 個元素之體。
//  【命題 Λ0-1】p 為素數 ⇔ ℤ/pℤ 為體。
//     證明：p 素、0 < a < p ⇒ gcd(a,p)=1 ⇒ ∃u,v, ua+vp=1 ⇒ a⁻¹ = u mod p；
//           反之 p = ab（1<a,b<p）時 a 為零因子，非體。∎
//  【命題 Λ0-2（無溢位）】0 ≤ a,b < p < 2³¹ ⇒ 0 ≤ a·b < 2⁶² < 2⁶³−1。
//     證明：a·b ≤ (p−1)² < 2⁶²。Int64 可表至 2⁶³−1，故 a*b 之求值不溢位。∎
//  【定理 Λ0-3（Fermat 小定理）】p 素、a ≢ 0 ⇒ a^{p−1} ≡ 1，故 a⁻¹ = a^{p−2}。
//     證明：𝔽pˣ 為 p−1 階乘法群，由 Lagrange 定理元素階整除群階。∎
// ============================================================================

///|
/// 把任意 Int64 歸約到 [0, p)。
pub fn normmod(a : Int64, p : Int64) -> Int64 {
  let r = a % p
  if r < 0L {
    r + p
  } else {
    r
  }
}

///|
/// 𝔽p 之運算脈絡：持有模數，並累計「機器字乘法次數」作為成本模型之計量。
/// 成本計量只計乘法（schoolbook 模型下乘法為主導項），加減另計。
pub struct FpCtx {
  pmod : Int64
  mut ops : Int64
  mut adds : Int64
}

///|
pub fn FpCtx::make(p : Int64) -> FpCtx {
  { pmod: p, ops: 0L, adds: 0L, }
}

///|
/// 模乘（計 1 次字乘法）。前置條件 0 ≤ a,b < p < 2³¹。
pub fn FpCtx::mul(self : FpCtx, a : Int64, b : Int64) -> Int64 {
  self.ops = self.ops + 1L
  a * b % self.pmod
}

///|
pub fn FpCtx::add(self : FpCtx, a : Int64, b : Int64) -> Int64 {
  self.adds = self.adds + 1L
  let s = a + b
  if s >= self.pmod {
    s - self.pmod
  } else {
    s
  }
}

///|
pub fn FpCtx::sub(self : FpCtx, a : Int64, b : Int64) -> Int64 {
  self.adds = self.adds + 1L
  let s = a - b
  if s < 0L {
    s + self.pmod
  } else {
    s
  }
}

///|
pub fn FpCtx::neg(self : FpCtx, a : Int64) -> Int64 {
  if a == 0L {
    0L
  } else {
    self.pmod - a
  }
}

///|
/// 快速冪（平方–乘法），計入字乘法次數。
pub fn FpCtx::pow(self : FpCtx, a : Int64, e : Int64) -> Int64 {
  let mut r = 1L
  let mut b = normmod(a, self.pmod)
  let mut k = e
  while k > 0L {
    if k % 2L == 1L {
      r = self.mul(r, b)
    }
    b = self.mul(b, b)
    k = k / 2L
  }
  r
}

///|
/// 乘法逆元（Fermat）；a ≡ 0 時回 None。
pub fn FpCtx::inv(self : FpCtx, a : Int64) -> Int64? {
  let x = normmod(a, self.pmod)
  if x == 0L {
    None
  } else {
    Some(self.pow(x, self.pmod - 2L))
  }
}

// ---------------------------------------------------------------------------
//  素數判定與素數池
//  【定理 Λ0-4（Miller–Rabin 之確定性範圍）】
//    若 n < 3 215 031 751 且 n 通過底 {2,3,5,7} 之強偽素數檢驗，則 n 為素數。
//    （Jaeschke 1993 之窮舉結果；本實作另以試除法於義務 K-01 中獨立覆核。）
//  本檔所有素數 < 2³¹ = 2 147 483 648 < 3 215 031 751，故檢驗為確定性判定。
// ---------------------------------------------------------------------------

///|
/// 無模脈絡之快速冪（供素性判定；n < 2³¹ 故不溢位）。
fn powmod_raw(a : Int64, e : Int64, n : Int64) -> Int64 {
  let mut r = 1L
  let mut b = normmod(a, n)
  let mut k = e
  while k > 0L {
    if k % 2L == 1L {
      r = r * b % n
    }
    b = b * b % n
    k = k / 2L
  }
  r
}

///|
/// 確定性 Miller–Rabin（適用 n < 2³¹）。
pub fn is_prime_i64(n : Int64) -> Bool {
  if n < 2L {
    return false
  }
  let small = [2L, 3L, 5L, 7L, 11L, 13L, 17L, 19L, 23L, 29L, 31L, 37L]
  for q in small {
    if n % q == 0L {
      return n == q
    }
  }
  let mut d = n - 1L
  let mut s = 0
  while d % 2L == 0L {
    d = d / 2L
    s = s + 1
  }
  for a in [2L, 3L, 5L, 7L] {
    let mut x = powmod_raw(a, d, n)
    if x == 1L || x == n - 1L {
      continue
    }
    let mut witness = true
    for _i in 1..<s {
      x = x * x % n
      if x == n - 1L {
        witness = false
        break
      }
    }
    if witness {
      return false
    }
  }
  true
}

///|
/// 試除法素性判定（獨立於 Miller–Rabin 之覆核路徑；只用於義務自證）。
pub fn is_prime_trial(n : Int64) -> Bool {
  if n < 2L {
    return false
  }
  if n % 2L == 0L {
    return n == 2L
  }
  let mut d = 3L
  while d * d <= n {
    if n % d == 0L {
      return false
    }
    d = d + 2L
  }
  true
}

///|
/// 素數池：自 2³¹−1 往下取 k 個相異素數（確定性、可重現）。
/// 【命題 Λ0-5】池中任兩素數互素，故可直接施用中國剩餘定理。
pub fn prime_pool(k : Int) -> Array[Int64] {
  let ps : Array[Int64] = []
  let mut n = 2147483647L
  while ps.length() < k && n > 2000000000L {
    if is_prime_i64(n) {
      ps.push(n)
    }
    n = n - 2L
  }
  ps
}

// ---------------------------------------------------------------------------
//  𝔽p 上之矩陣
//  【定義 Λ0-2】FpMat = 列優先之 Int64 陣列，元素恆於 [0,p)。
//  所有演算法與 ℚ 上之版本同構（同一組列運算），差別僅在純量體。
// ---------------------------------------------------------------------------

///|
pub struct FpMat {
  fr : Int
  fc : Int
  fd : Array[Int64]
}

///|
pub fn FpMat::make(r : Int, c : Int) -> FpMat {
  { fr: r, fc: c, fd: Array::make(r * c, 0L), }
}

///|
pub fn FpMat::get(self : FpMat, i : Int, j : Int) -> Int64 {
  self.fd[i * self.fc + j]
}

///|
pub fn FpMat::set(self : FpMat, i : Int, j : Int, v : Int64) -> Unit {
  self.fd[i * self.fc + j] = v
}

///|
pub fn FpMat::copy(self : FpMat) -> FpMat {
  {
    fr: self.fr,
    fc: self.fc,
    fd: Array::makei(self.fd.length(), i => self.fd[i]),
  }
}

///|
pub fn fp_ident(n : Int) -> FpMat {
  let m = FpMat::make(n, n)
  for i in 0..<n {
    m.set(i, i, 1L)
  }
  m
}

///|
/// ℤ 矩陣（以 BigInt 列陣表示）之約化 φ_p：環同態 ℤ → 𝔽p 逐項施用。
pub fn fp_of_big(a : Array[Array[BigInt]], ctx : FpCtx) -> FpMat {
  let r = a.length()
  let c = if r == 0 { 0 } else { a[0].length() }
  let m = FpMat::make(r, c)
  let pb = BigInt::from_int64(ctx.pmod)
  for i in 0..<r {
    for j in 0..<c {
      m.set(i, j, normmod((a[i][j] % pb).to_int64(), ctx.pmod))
    }
  }
  m
}

///|
/// ℚ 矩陣之約化：分母 ≡ 0 (mod p) 時 p 為「壞素數」，回 None。
pub fn fp_of_q(a : Mat[Q], ctx : FpCtx) -> FpMat? {
  let m = FpMat::make(a.mrows, a.mcols)
  let pb = BigInt::from_int64(ctx.pmod)
  for i in 0..<a.mrows {
    for j in 0..<a.mcols {
      let q = a.at(i, j)
      let dn = normmod((q.den % pb).to_int64(), ctx.pmod)
      match ctx.inv(dn) {
        None => return None
        Some(di) => {
          let nu = normmod((q.num % pb).to_int64(), ctx.pmod)
          m.set(i, j, ctx.mul(nu, di))
        }
      }
    }
  }
  Some(m)
}

///|
/// ℚ 向量之約化。
pub fn fp_of_qvec(v : Array[Q], ctx : FpCtx) -> Array[Int64]? {
  let out = Array::make(v.length(), 0L)
  let pb = BigInt::from_int64(ctx.pmod)
  for i in 0..<v.length() {
    let dn = normmod((v[i].den % pb).to_int64(), ctx.pmod)
    match ctx.inv(dn) {
      None => return None
      Some(di) =>
        out[i] = ctx.mul(normmod((v[i].num % pb).to_int64(), ctx.pmod), di)
    }
  }
  Some(out)
}

///|
/// 矩陣乘法 mod p。
pub fn fp_matmul(a : FpMat, b : FpMat, ctx : FpCtx) -> FpMat {
  let m = FpMat::make(a.fr, b.fc)
  for i in 0..<a.fr {
    for j in 0..<b.fc {
      let mut s = 0L
      for k in 0..<a.fc {
        s = ctx.add(s, ctx.mul(a.get(i, k), b.get(k, j)))
      }
      m.set(i, j, s)
    }
  }
  m
}

///|
/// 矩陣 × 向量 mod p。
pub fn fp_matvec(a : FpMat, x : Array[Int64], ctx : FpCtx) -> Array[Int64] {
  let out = Array::make(a.fr, 0L)
  for i in 0..<a.fr {
    let mut s = 0L
    for k in 0..<a.fc {
      s = ctx.add(s, ctx.mul(a.get(i, k), x[k]))
    }
    out[i] = s
  }
  out
}

///|
/// 消去法之輸出包（與 ℚ 版 Rref 同構）。
pub struct FpRref {
  rmat : FpMat
  rank : Int
  pivots : Array[Int]
  det : Int64
}

///|
/// 𝔽p 上之高斯–若爾當消去（完全化簡列階梯形）。
/// 【命題 Λ0-6】列運算為可逆變換 ⇒ rank、解集、行相依結構皆不變；
///   方陣時 det = sign · ∏ 樞軸。
pub fn fp_rref(a0 : FpMat, ctx : FpCtx) -> FpRref {
  let a = a0.copy()
  let rows = a.fr
  let cols = a.fc
  let pivots : Array[Int] = []
  let mut r = 0
  let mut sign = 1L
  let mut prod = 1L
  for c in 0..<cols {
    if r >= rows {
      break
    }
    let mut best = -1
    for i in r..<rows {
      if a.get(i, c) != 0L {
        best = i
        break
      }
    }
    if best < 0 {
      continue
    }
    if best != r {
      for j in 0..<cols {
        let t = a.get(r, j)
        a.set(r, j, a.get(best, j))
        a.set(best, j, t)
      }
      sign = -sign
    }
    let pv = a.get(r, c)
    prod = ctx.mul(prod, pv)
    let piv = match ctx.inv(pv) {
      Some(x) => x
      None => 1L
    }
    for j in 0..<cols {
      a.set(r, j, ctx.mul(a.get(r, j), piv))
    }
    for i in 0..<rows {
      if i != r {
        let f = a.get(i, c)
        if f != 0L {
          for j in 0..<cols {
            a.set(i, j, ctx.sub(a.get(i, j), ctx.mul(f, a.get(r, j))))
          }
        }
      }
    }
    pivots.push(c)
    r = r + 1
  }
  let det = if rows != cols {
    0L
  } else if r < rows {
    0L
  } else if sign < 0L {
    ctx.neg(prod)
  } else {
    prod
  }
  { rmat: a, rank: r, pivots, det, }
}

///|
/// 行列式 mod p（完全消去版；供需要 RREF 之場合）。
pub fn fp_det(a : FpMat, ctx : FpCtx) -> Int64 {
  fp_rref(a, ctx).det
}

///|
/// 行列式 mod p（前向消去版，約 n³/3 次字乘法；加速層之主力）。
/// 【命題 Λ0-6′】只需上三角化即可讀出 det = sign·∏樞軸，
///   故不必施行 Gauss–Jordan 之回代（可省 2/3 之工作量）。
pub fn fp_det_fast(a0 : FpMat, ctx : FpCtx) -> Int64 {
  let a = a0.copy()
  let n = a.fr
  let mut sign = 1L
  let mut prod = 1L
  for k in 0..<n {
    let mut piv = -1
    for i in k..<n {
      if a.get(i, k) != 0L {
        piv = i
        break
      }
    }
    if piv < 0 {
      return 0L
    }
    if piv != k {
      for j in k..<n {
        let t = a.get(k, j)
        a.set(k, j, a.get(piv, j))
        a.set(piv, j, t)
      }
      sign = -sign
    }
    let pv = a.get(k, k)
    prod = ctx.mul(prod, pv)
    let pinv = match ctx.inv(pv) {
      Some(x) => x
      None => 1L
    }
    for i in (k + 1)..<n {
      let u = a.get(i, k)
      if u != 0L {
        let f = ctx.mul(u, pinv)
        for j in k..<n {
          a.set(i, j, ctx.sub(a.get(i, j), ctx.mul(f, a.get(k, j))))
        }
      }
    }
  }
  if sign < 0L {
    ctx.neg(prod)
  } else {
    prod
  }
}

///|
/// 批次求逆（Montgomery 技巧）：n 個逆元只需 1 次求逆 + 3n 次乘法。
/// 【定理 Λ0-11】令 Pᵢ = v₀⋯v_{i−1}，A = (∏v)⁻¹，則
///   vᵢ⁻¹ = A · (∏_{j>i} vⱼ) · Pᵢ，可由後向遞推一次掃描求得。
///   證明：A·∏_{j>i}vⱼ·Pᵢ = (∏v)⁻¹·(∏v)/vᵢ = vᵢ⁻¹。∎
///   成本：由 n 次 Fermat 冪（各約 46 次乘法）降為 1 次 + 3n 次乘法。
pub fn fp_batch_inv(v : Array[Int64], ctx : FpCtx) -> Array[Int64]? {
  let n = v.length()
  if n == 0 {
    return Some([])
  }
  let pre = Array::make(n, 1L)
  let mut acc = 1L
  for i in 0..<n {
    if v[i] == 0L {
      return None
    }
    pre[i] = acc
    acc = ctx.mul(acc, v[i])
  }
  let mut ainv = match ctx.inv(acc) {
    Some(x) => x
    None => return None
  }
  let out = Array::make(n, 0L)
  for i = n - 1; i >= 0; i = i - 1 {
    out[i] = ctx.mul(ainv, pre[i])
    ainv = ctx.mul(ainv, v[i])
  }
  Some(out)
}

///|
/// 秩 mod p。
/// 【命題 Λ0-7】rank_{𝔽p}(φ_p A) ≤ rank_ℚ(A)，等號對除有限多個 p 以外成立。
pub fn fp_rank(a : FpMat, ctx : FpCtx) -> Int {
  fp_rref(a, ctx).rank
}

///|
/// 方陣逆 mod p（奇異時 None）。
pub fn fp_inv(a : FpMat, ctx : FpCtx) -> FpMat? {
  let n = a.fr
  let aug = FpMat::make(n, 2 * n)
  for i in 0..<n {
    for j in 0..<n {
      aug.set(i, j, a.get(i, j))
    }
    aug.set(i, n + i, 1L)
  }
  let rr = fp_rref(aug, ctx)
  if rr.rank < n {
    return None
  }
  for i in 0..<n {
    if rr.pivots[i] != i {
      return None
    }
  }
  let inv = FpMat::make(n, n)
  for i in 0..<n {
    for j in 0..<n {
      inv.set(i, j, rr.rmat.get(i, n + j))
    }
  }
  Some(inv)
}

///|
/// 線性方程組 Ax = b mod p（A 方陣且非奇異時回唯一解）。
pub fn fp_solve(a : FpMat, b : Array[Int64], ctx : FpCtx) -> Array[Int64]? {
  let n = a.fr
  if a.fc != n || b.length() != n {
    return None
  }
  let aug = FpMat::make(n, n + 1)
  for i in 0..<n {
    for j in 0..<n {
      aug.set(i, j, a.get(i, j))
    }
    aug.set(i, n, b[i])
  }
  let rr = fp_rref(aug, ctx)
  if rr.rank < n {
    return None
  }
  for i in 0..<n {
    if rr.pivots[i] != i {
      return None
    }
  }
  Some(Array::makei(n, i => rr.rmat.get(i, n)))
}

// ---------------------------------------------------------------------------
//  Hessenberg 化簡與特徵多項式（Cohen, Algorithm 2.2.9）
//  【定義 Λ0-3】H 為上 Hessenberg：i > j+1 ⇒ H_{ij} = 0。
//  【定理 Λ0-8】任意 A 於體上相似於上 Hessenberg 矩陣 H，且 χ_A = χ_H。
//     證明：以列運算 R_i ← R_i − f R_m 消去第 m−1 行之下方元素，
//           並同時施以逆變換之行運算 C_m ← C_m + f C_i，
//           合成即相似變換 H = S⁻¹AS；相似保持特徵多項式。∎
//  【定理 Λ0-9（Hessenberg 遞迴）】設 p_m 為 H 之前 m 階主子陣之特徵多項式，
//     p_0 = 1，則
//       p_m(x) = (x − H_{m−1,m−1}) p_{m−1}(x)
//                − Σ_{i=1}^{m−1} H_{m−i−1,m−1} (∏_{j=1}^{i} H_{m−j,m−j−1}) p_{m−i−1}(x)
//     且 χ_H = p_n。證明：對最後一行作 Laplace 展開，次對角線之連乘積
//     恰為展開中唯一非零之路徑權重。∎
//  複雜度：O(n³) 次 𝔽p 乘法，全程不生成任何長整數。
// ---------------------------------------------------------------------------

///|
pub fn fp_hessenberg(a0 : FpMat, ctx : FpCtx) -> FpMat {
  let h = a0.copy()
  let n = h.fr
  for m in 1..<(n - 1) {
    let mut piv = -1
    for i in m..<n {
      if h.get(i, m - 1) != 0L {
        piv = i
        break
      }
    }
    if piv < 0 {
      continue
    }
    if piv != m {
      for j in 0..<n {
        let t = h.get(m, j)
        h.set(m, j, h.get(piv, j))
        h.set(piv, j, t)
      }
      for j in 0..<n {
        let t = h.get(j, m)
        h.set(j, m, h.get(j, piv))
        h.set(j, piv, t)
      }
    }
    let t = h.get(m, m - 1)
    let tinv = match ctx.inv(t) {
      Some(x) => x
      None => 1L
    }
    for i in (m + 1)..<n {
      let u = h.get(i, m - 1)
      if u != 0L {
        let f = ctx.mul(u, tinv)
        for j in 0..<n {
          h.set(i, j, ctx.sub(h.get(i, j), ctx.mul(f, h.get(m, j))))
        }
        for j in 0..<n {
          h.set(j, m, ctx.add(h.get(j, m), ctx.mul(f, h.get(j, i))))
        }
      }
    }
  }
  h
}

///|
/// χ_A(x) = det(xI − A) mod p，升冪係數，長度 n+1，首一。
pub fn fp_charpoly(a : FpMat, ctx : FpCtx) -> Array[Int64] {
  let n = a.fr
  if n == 0 {
    return [1L]
  }
  let h = fp_hessenberg(a, ctx)
  let polys : Array[Array[Int64]] = [[1L]]
  for m in 1..<(n + 1) {
    let pm1 = polys[m - 1]
    let pm = Array::make(m + 1, 0L)
    let hmm = h.get(m - 1, m - 1)
    for i in 0..<pm1.length() {
      pm[i + 1] = ctx.add(pm[i + 1], pm1[i])
      pm[i] = ctx.sub(pm[i], ctx.mul(hmm, pm1[i]))
    }
    let mut t = 1L
    for i in 1..<m {
      t = ctx.mul(t, h.get(m - i, m - i - 1))
      let coef = ctx.mul(t, h.get(m - i - 1, m - 1))
      if coef != 0L {
        let pk = polys[m - i - 1]
        for s in 0..<pk.length() {
          pm[s] = ctx.sub(pm[s], ctx.mul(coef, pk[s]))
        }
      }
    }
    polys.push(pm)
  }
  polys[n]
}

// ---------------------------------------------------------------------------
//  𝔽p[x]：多項式（升冪 Int64 陣列）
//  【定義 Λ0-4】𝔽p[x] 為歐幾里得整環，次數為歐幾里得函數。
// ---------------------------------------------------------------------------

///|
/// 去除高次之零係數（零多項式 ⇒ 空陣列）。
pub fn fpp_norm(a : Array[Int64]) -> Array[Int64] {
  let mut n = a.length()
  while n > 0 && a[n - 1] == 0L {
    n = n - 1
  }
  Array::makei(n, i => a[i])
}

///|
pub fn fpp_deg(a : Array[Int64]) -> Int {
  fpp_norm(a).length() - 1
}

///|
pub fn fpp_add(a : Array[Int64], b : Array[Int64], ctx : FpCtx) -> Array[Int64] {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  let out = Array::make(n, 0L)
  for i in 0..<n {
    let x = if i < a.length() { a[i] } else { 0L }
    let y = if i < b.length() { b[i] } else { 0L }
    out[i] = ctx.add(x, y)
  }
  fpp_norm(out)
}

///|
pub fn fpp_sub(a : Array[Int64], b : Array[Int64], ctx : FpCtx) -> Array[Int64] {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  let out = Array::make(n, 0L)
  for i in 0..<n {
    let x = if i < a.length() { a[i] } else { 0L }
    let y = if i < b.length() { b[i] } else { 0L }
    out[i] = ctx.sub(x, y)
  }
  fpp_norm(out)
}

///|
/// 卷積乘法：(fg)_k = Σ_{i+j=k} f_i g_j。
pub fn fpp_mul(a : Array[Int64], b : Array[Int64], ctx : FpCtx) -> Array[Int64] {
  if a.length() == 0 || b.length() == 0 {
    return []
  }
  let out = Array::make(a.length() + b.length() - 1, 0L)
  for i in 0..<a.length() {
    if a[i] != 0L {
      for j in 0..<b.length() {
        out[i + j] = ctx.add(out[i + j], ctx.mul(a[i], b[j]))
      }
    }
  }
  fpp_norm(out)
}

///|
pub fn fpp_scale(a : Array[Int64], c : Int64, ctx : FpCtx) -> Array[Int64] {
  fpp_norm(Array::makei(a.length(), i => ctx.mul(a[i], c)))
}

///|
/// Horner 求值：環同態 ev_t : 𝔽p[x] → 𝔽p。
pub fn fpp_eval(a : Array[Int64], t : Int64, ctx : FpCtx) -> Int64 {
  let mut acc = 0L
  for k = a.length() - 1; k >= 0; k = k - 1 {
    acc = ctx.add(ctx.mul(acc, t), a[k])
  }
  acc
}

///|
/// 帶餘除法 a = q·b + r，deg r < deg b（b ≠ 0）。
pub fn fpp_divmod(
  a : Array[Int64],
  b : Array[Int64],
  ctx : FpCtx,
) -> (Array[Int64], Array[Int64])? {
  let bb = fpp_norm(b)
  if bb.length() == 0 {
    return None
  }
  let lead = bb[bb.length() - 1]
  let linv = match ctx.inv(lead) {
    Some(x) => x
    None => return None
  }
  let r = Array::makei(a.length(), i => a[i])
  let db = bb.length() - 1
  let dq = r.length() - 1 - db
  if dq < 0 {
    return Some(([], fpp_norm(r)))
  }
  let q = Array::make(dq + 1, 0L)
  for k = r.length() - 1; k >= db; k = k - 1 {
    let c = ctx.mul(r[k], linv)
    q[k - db] = c
    if c != 0L {
      for j in 0..<bb.length() {
        r[k - db + j] = ctx.sub(r[k - db + j], ctx.mul(c, bb[j]))
      }
    }
  }
  Some((fpp_norm(q), fpp_norm(r)))
}

///|
/// 首一最大公因式（歐幾里得演算法）。
pub fn fpp_gcd(a : Array[Int64], b : Array[Int64], ctx : FpCtx) -> Array[Int64] {
  let mut x = fpp_norm(a)
  let mut y = fpp_norm(b)
  while y.length() > 0 {
    match fpp_divmod(x, y, ctx) {
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
  match ctx.inv(x[x.length() - 1]) {
    Some(u) => fpp_scale(x, u, ctx)
    None => x
  }
}

///|
/// 由根造首一多項式 ∏(x − rᵢ)（積樹之基礎情形即線性因式）。
pub fn fpp_from_roots(roots : Array[Int64], ctx : FpCtx) -> Array[Int64] {
  let mut acc : Array[Int64] = [1L]
  for r in roots {
    acc = fpp_mul(acc, [ctx.neg(normmod(r, ctx.pmod)), 1L], ctx)
  }
  acc
}

///|
/// Newton 形式之插值（𝔽[x] 之中國剩餘定理建構性證明）。
/// 【定理 Λ0-10】x₀,…,x_d 互異 ⇒ 𝔽[x]/∏(x−xᵢ) ≅ ∏ 𝔽[x]/(x−xᵢ) ≅ 𝔽^{d+1}，
///   故存在唯一 deg ≤ d 之 f 使 f(xᵢ) = yᵢ。
pub fn fpp_interp(
  xs : Array[Int64],
  ys : Array[Int64],
  ctx : FpCtx,
) -> Array[Int64]? {
  let n = xs.length()
  if n == 0 || ys.length() != n {
    return None
  }
  // Newton 差商（每一層以批次求逆攤銷模逆元之成本）
  let c = Array::makei(n, i => normmod(ys[i], ctx.pmod))
  let xn = Array::makei(n, i => normmod(xs[i], ctx.pmod))
  for j in 1..<n {
    let diffs = Array::makei(n - j, k => ctx.sub(xn[k + j], xn[k]))
    let invs = match fp_batch_inv(diffs, ctx) {
      Some(v) => v
      None => return None
    }
    for i = n - 1; i >= j; i = i - 1 {
      c[i] = ctx.mul(ctx.sub(c[i], c[i - 1]), invs[i - j])
    }
  }
  // Horner 展開回單項式基
  let out = Array::make(n, 0L)
  for k = n - 1; k >= 0; k = k - 1 {
    // out ← out·(x − x_k) + c_k
    for i = n - 1; i >= 1; i = i - 1 {
      out[i] = out[i - 1]
    }
    out[0] = 0L
    let xk = normmod(xs[k], ctx.pmod)
    for i in 0..<(n - 1) {
      out[i] = ctx.sub(out[i], ctx.mul(xk, out[i + 1]))
    }
    out[0] = ctx.add(out[0], c[k])
  }
  Some(fpp_norm(out))
}

// ---------------------------------------------------------------------------
//  數論變換 NTT：於 𝔽p 中以 2ᵏ 次單位根作求值／插值
//
//  【定義 Λ0-5】p 為素數且 2ᵏ | p−1 時，𝔽pˣ（循環群，階 p−1）含唯一
//     階為 2ᵏ 之子群；其生成元 ω = g^{(p−1)/2ᵏ} 稱為 2ᵏ 次本原單位根。
//  【定理 Λ0-12（NTT = 𝔽[x] 之 CRT）】設 n = 2ᵏ，ω 為 n 次本原單位根，則
//        𝔽p[x]/(xⁿ − 1) ≅ ∏_{i=0}^{n−1} 𝔽p[x]/(x − ωⁱ),
//     因 xⁿ − 1 = ∏(x − ωⁱ) 且各因式兩兩互素（ωⁱ 相異）。
//     該同構之矩陣即 Vandermonde 矩陣 (ω^{ij})，其逆為 n⁻¹(ω^{−ij})。
//     證明：Σ_{j} ω^{j(i−l)} = n·[i=l]（幾何級數；i≠l 時公比 ω^{i−l} ≠ 1
//           且 (ω^{i−l})ⁿ = 1 ⇒ 級數和為 0）。∎
//  【定理 Λ0-13（Cooley–Tukey）】上述變換可由分治於 O(n log n) 次乘法完成。
//     證明：按奇偶分拆 f = f_even(x²) + x·f_odd(x²)，而 (ω²) 為 n/2 次本原根，
//           遞迴 T(n) = 2T(n/2) + O(n)。∎
//  【推論 Λ0-14】多項式乘法於 𝔽p[x] 可於 O(n log n) 完成（求值→逐點→插值），
//     相對 schoolbook 之 O(n²)：此即「多項式純 CRT 篩選」之快速形式。
// ---------------------------------------------------------------------------

///|
/// NTT 友善素數池：p = c·2²⁰ + 1 < 2³¹（故可支援長度至 2²⁰ 之變換）。
pub fn ntt_prime_pool(k : Int) -> Array[Int64] {
  let ps : Array[Int64] = []
  let step = 1048576L
  let mut c = 2047L
  while c >= 1L && ps.length() < k {
    let p = c * step + 1L
    if p < 2147483648L && is_prime_i64(p) {
      ps.push(p)
    }
    c = c - 1L
  }
  ps
}

///|
/// 最小原根（p−1 之質因子以試除求得；本池之 p−1 = c·2²⁰，c < 2048 故極快）。
pub fn primitive_root(p : Int64) -> Int64 {
  let mut m = p - 1L
  let factors : Array[Int64] = []
  let mut d = 2L
  while d * d <= m {
    if m % d == 0L {
      factors.push(d)
      while m % d == 0L {
        m = m / d
      }
    }
    d = d + 1L
  }
  if m > 1L {
    factors.push(m)
  }
  let mut g = 2L
  while g < p {
    let mut good = true
    for q in factors {
      if powmod_raw(g, (p - 1L) / q, p) == 1L {
        good = false
        break
      }
    }
    if good {
      return g
    }
    g = g + 1L
  }
  2L
}

///|
/// 位元反轉置換之索引（純算術實作，不依賴位元運算）。
pub fn bitrev_index(i : Int, lg : Int) -> Int {
  let mut r = 0
  let mut x = i
  for _k in 0..<lg {
    r = r * 2 + x % 2
    x = x / 2
  }
  r
}

///|
/// 原地 NTT（length = 2^lg）。invert = true 時為逆變換（含 n⁻¹ 縮放）。
pub fn fp_ntt(
  a : Array[Int64],
  lg : Int,
  invert : Bool,
  g : Int64,
  ctx : FpCtx,
) -> Unit {
  let n = a.length()
  for i in 0..<n {
    let j = bitrev_index(i, lg)
    if i < j {
      let t = a[i]
      a[i] = a[j]
      a[j] = t
    }
  }
  let mut len = 2
  while len <= n {
    let e = (ctx.pmod - 1L) / len.to_int64()
    let mut w = ctx.pow(g, e)
    if invert {
      w = match ctx.inv(w) {
        Some(x) => x
        None => 1L
      }
    }
    let half = len / 2
    let mut i = 0
    while i < n {
      let mut wn = 1L
      for k in 0..<half {
        let u = a[i + k]
        let v = ctx.mul(a[i + k + half], wn)
        a[i + k] = ctx.add(u, v)
        a[i + k + half] = ctx.sub(u, v)
        wn = ctx.mul(wn, w)
      }
      i = i + len
    }
    len = len * 2
  }
  if invert {
    let ninv = match ctx.inv(n.to_int64()) {
      Some(x) => x
      None => 1L
    }
    for i in 0..<n {
      a[i] = ctx.mul(a[i], ninv)
    }
  }
}

///|
/// 以 NTT 作 𝔽p[x] 之乘法（長度不足 2 之冪或 p 不支援時回 None）。
pub fn fpp_mul_ntt(
  a : Array[Int64],
  b : Array[Int64],
  g : Int64,
  ctx : FpCtx,
) -> Array[Int64]? {
  let fa0 = fpp_norm(a)
  let fb0 = fpp_norm(b)
  if fa0.length() == 0 || fb0.length() == 0 {
    return Some([])
  }
  let need = fa0.length() + fb0.length() - 1
  let mut sz = 1
  let mut lg = 0
  while sz < need {
    sz = sz * 2
    lg = lg + 1
  }
  if (ctx.pmod - 1L) % sz.to_int64() != 0L {
    return None
  }
  let fa = Array::makei(sz, i => if i < fa0.length() { fa0[i] } else { 0L })
  let fb = Array::makei(sz, i => if i < fb0.length() { fb0[i] } else { 0L })
  fp_ntt(fa, lg, false, g, ctx)
  fp_ntt(fb, lg, false, g, ctx)
  for i in 0..<sz {
    fa[i] = ctx.mul(fa[i], fb[i])
  }
  fp_ntt(fa, lg, true, g, ctx)
  Some(fpp_norm(Array::makei(need, i => fa[i])))
}

///|
/// # 第七輪：以 L-05／L-08 為反例重構加速層
///
/// ## 兩個反例逼出來的東西
///
/// 先把兩條反例的主張量清楚（第七輪之前沒有任何義務量過它們）：
///
/// ```text
///   L-05 ℚ RREF 多模重建   比值 0.046 – 0.15，在整個 (n, 位元) 網格上都輸
///   L-08 Gram LDLᵀ 多模重建 比值 0.15 → 0.81 → 0.65，先升後降，從不越過 1
/// ```
///
/// 這比原目錄寫的「×0.15」「×0.6」強得多：原來的數字是單點，現在是整片。
/// 但把整片掃出來之後，真正的發現不是「這兩條確實該放棄」，而是**它們輸的
/// 理由跟演算法無關**。
///
/// ## 診斷：主成本是 Θ(ν·k²)，而 ν 是「要重建幾個數」
///
/// 多模路徑的字乘法花在三個地方：
///
/// ```text
///   k 趟模消去            Θ(k·n³)          每趟都是機器字，不膨脹
///   CRT 累積              Θ(ν·k²)          ν 個輸出各自 Garner，模數逐步變長
///   事後憑證              Θ(n³·w²)         一次，w 為輸出字寬
/// ```
///
/// 第二項幾乎總是主導。它帶著 **ν＝要重建的輸出個數**這個因子，而這正是
/// L-05 與 L-08 輸掉的地方：RREF 要重建 2n² 個有理數，LDLᵀ 要重建 n²+n 個。
/// 相對地，K-04（ℤ 行列式）只重建 **1** 個，所以它 ×4.4 地贏。
///
/// 第七輪先試了一條看起來很對的路 —— 把「逐素數穩定判定」換成
/// 「先驗 Hadamard 界、吃滿一次重建」。結果**更慢**（×0.68 – ×0.83，見
/// `qldlt_crt_ap`）：Hadamard 界是悲觀的，它要的素數比穩定判定實際用掉的
/// 多出兩三成，而主成本 Θ(ν·k²) 對 k 是平方的。這條失敗的嘗試留在庫裡，
/// 因為它正是「換 k 沒用、要換 ν」這個結論的反面證據。
///
/// ## 重構原則（由這兩條反例導出）
///
/// > **加速層的單位不該是「整個矩陣」，而該是「呼叫端真正要的那個量」。**
///
/// 照這條原則改寫兩條反例：
///
/// ```text
///   L-05 → 秩與樞軸    ν : 2n² → 0    模 p 消去直接給樞軸型態，完全不重建
///   L-08 → D 與 det    ν : n²+n → n   只重建 n 個整數前導主子式
/// ```
///
/// 兩者都不是「換個區域再量一次」，是把輸出換掉。換掉之後正確性靠什麼？
/// L-05′ 靠兩條精確的夾擠憑證，L-08′ 靠 Hadamard 界下的整數 CRT ——
/// 後者與 K-04 用的是同一條定理，而 K-04 是加速層贏最漂亮的條目之一。

///|
/// 【重構後】Gram 之 LDLᵀ 多模重建 —— 先驗 Hadamard 界，一次重建。
///
/// 與 `qldlt_crt` 的唯一差別是「什麼時候重建」：
/// 舊版每吃一個素數重建一次並比對上一輪；本版先算出需要幾個素數，
/// 吃滿之後只重建一次。輸出與憑證完全相同。
pub fn qldlt_crt_ap(g : Mat[Q], primes : Array[Int64], c : Cost) -> QLdlt? {
  let n = g.mrows
  let (dd, gz) = qmat_clear_denom(g)
  // 先驗界：L、D 之分子分母皆為 Gz 之子式，受 Hadamard 界 H 控制。
  // 有理重建需模數 M > 2·N²（N 為分子分母之共同界），故取 need(H²)。
  let h = hadamard_bound(gz)
  let need = primes_needed(h * h, primes)
  let ps = ensure_primes(primes, need + 4)
  let crts : Array[Crt] = Array::makei(n * n + n, _ => Crt::new())
  let mut used = 0
  let mut t = 0
  while t < ps.length() && used < need {
    let p = ps[t]
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
  }
  if used < need {
    return None
  }
  let m = crts[0].modulus()
  let flat = Array::makei(n * n + n, i => crts[i].sym())
  match rat_recon_vec(flat, m) {
    None => None
    Some(x) => {
      let lmat = Mat::build(n, n, (i, j) => x[i * n + j])
      let dvec = Array::makei(n, i => {
        match x[n * n + i].div(Q::make(dd, 1N)) {
          Some(v) => v
          None => Q::zero()
        }
      })
      let okc = certify_ldlt_pub(g, lmat, dvec, c)
      Some({ lmat, dvec, used, certified: okc, })
    }
  }
}

///|
/// C 管憑證（與 `certify_ldlt` 同式，開放給重構版使用）：驗 L·D·Lᵀ = G。
pub fn certify_ldlt_pub(g : Mat[Q], l : Mat[Q], d : Array[Q], c : Cost) -> Bool {
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

///|
/// 【重構後】ℚ 反矩陣之多模重建 —— 先驗界一次重建。
///
/// A⁻¹ 之每一項為 ±(餘因子)/det，分子分母同受 Hadamard 界控制。
pub fn qinv_crt_ap(
  a : Mat[Q],
  primes : Array[Int64],
  c : Cost,
) -> (Mat[Q]?, Int, Bool) {
  let n = a.mrows
  let (d, az) = qmat_clear_denom(a)
  let h = hadamard_bound(az)
  let need = primes_needed(h * h, primes)
  let ps = ensure_primes(primes, need + 4)
  let crts : Array[Array[Crt]] = Array::makei(n, _ => {
    Array::makei(n, _ => Crt::new())
  })
  let mut used = 0
  let mut t = 0
  while t < ps.length() && used < need {
    let p = ps[t]
    t = t + 1
    let ctx = FpCtx::make(p)
    charge_reduce_rows(c, az)
    let fa = fp_of_big(az, ctx)
    match fp_inv(fa, ctx) {
      None => {
        c.absorb_fp(ctx)
        continue
      }
      Some(fi) => {
        for i in 0..<n {
          for j in 0..<n {
            charge_crt_step(c, crts[i][j].modulus())
            crts[i][j].absorb(fi.get(i, j), p)
          }
        }
        c.absorb_fp(ctx)
        used = used + 1
      }
    }
  }
  if used < need {
    return (None, used, false)
  }
  let m = crts[0][0].modulus()
  let flat = Array::makei(n * n, k => crts[k / n][k % n].sym())
  match rat_recon_vec(flat, m) {
    None => (None, used, false)
    Some(x) => {
      // Az⁻¹ 之重建值；A = Az/d ⇒ A⁻¹ = d·Az⁻¹
      let dq = Q::make(d, 1N)
      let inv = Mat::build(n, n, (i, j) => x[i * n + j].mul(dq))
      let prod = qmul_cost(c, a, inv)
      let ok = prod.equals(Mat::ident(n))
      (Some(inv), used, ok)
    }
  }
}

// ---------------------------------------------------------------------------
//  第二個方向：改變輸出，而不是改變區域
// ---------------------------------------------------------------------------

///|
/// ## L-05 的另一條出路
///
/// 把 `qldlt_crt` 修好之後 L-08 就翻盤了，但 L-05 不會 —— RREF 的輸出就是
/// 2n² 個有理數，ν 擺在那裡，換重建策略只是把 k³ 降成 k²，省不掉 ν。
///
/// 真正的問題是**輸出選錯了**。呼叫端要 RREF 幾乎都不是為了那 2n² 個數，
/// 而是為了「秩是多少、樞軸在哪」。這兩樣東西可以完全不做重建：
/// 模 p 消去直接給出樞軸型態，而壞素數只會讓秩變小，故取數個素數中的
/// 最大秩即為真秩。
///
/// ## 無條件正確性如何取得（不靠機率）
///
/// 輸出的是候選樞軸集 S（|S| = r），用兩條精確檢查把它鎖死：
///
/// ```text
///   (下界) det(A[*, S] 之 r 個樞軸列) ≠ 0   ⇒ rank ≥ r
///   (上界) 每一個非樞軸行都落在樞軸行張成的空間裡 ⇒ rank ≤ r
/// ```
///
/// 兩條都是 ℚ 上的精確計算，合起來給出 rank = r 與「S 為一組樞軸」的
/// 無條件證明。成本是一次 r 階求逆加 (n−r) 次回代，而不是整個 n×2n 的
/// 有理數消去。
pub struct RankCert {
  /// 秩
  rcrank : Int
  /// 樞軸行
  rcpiv : Array[Int]
  /// 下界憑證通過（r 階子式非零）
  rclow : Bool
  /// 上界憑證通過（非樞軸行皆在張成空間內）
  rcup : Bool
  /// 使用之素數個數
  rcused : Int
}

///|
/// 【L-05′】模 p 篩出秩與樞軸，再以兩條精確憑證夾擠 —— ν 由 2n² 降到 0。
///
/// ## 三步
///
/// ```text
///   1  模 p 消去（nprime 個素數取最大秩）→ 候選秩 r、樞軸行 S、樞軸列 R
///      壞素數只會使秩變小，故最大值即真秩之候選。此步完全不重建。
///   2  下界：det A[R,S] ≠ 0 ⇒ rank ≥ r
///      以 zdet_crt 算（整數、ν = 1、Hadamard 先驗界）—— 正是 K-04 的結構，
///      也正是加速層贏得最漂亮的那一種。
///   3  上界：r = min(m,n) 時自動成立；否則逐個非樞軸行驗它落在 S 的張成裡
///      （共用一次 r 階精確求逆，再逐行比對）。
/// ```
///
/// 兩條憑證都在 ℚ 上精確計算，合起來是 rank = r 的無條件證明。
pub fn qrank_modp(
  a : Mat[Q],
  primes : Array[Int64],
  nprime : Int,
  c : Cost,
) -> RankCert {
  let m = a.mrows
  let n = a.mcols
  let (_, az) = qmat_clear_denom(a)
  let mut best : Array[Int] = []
  let mut brank = 0
  let mut used = 0
  let mut t = 0
  while t < primes.length() && used < nprime {
    let p = primes[t]
    t = t + 1
    let ctx = FpCtx::make(p)
    charge_reduce_rows(c, az)
    let fa = fp_of_big(az, ctx)
    let rr = fp_rref(fa, ctx)
    c.absorb_fp(ctx)
    used = used + 1
    if rr.rank > brank {
      brank = rr.rank
      best = rr.pivots
    }
  }
  if brank == 0 {
    return { rcrank: 0, rcpiv: [], rclow: true, rcup: true, rcused: used, }
  }
  // ── 樞軸列：對 A[*,S] 之轉置再做一次模 p 消去 ───────────
  let ctx0 = FpCtx::make(primes[0])
  let subz : Array[Array[BigInt]] = []
  for j in 0..<brank {
    subz.push(Array::makei(m, i => qmat_to_zrows(a)[i][best[j]]))
  }
  charge_reduce_rows(c, subz)
  let rrows = fp_rref(fp_of_big(subz, ctx0), ctx0)
  c.absorb_fp(ctx0)
  let rowsel = rrows.pivots
  if rowsel.length() < brank {
    return {
      rcrank: brank,
      rcpiv: best,
      rclow: false,
      rcup: false,
      rcused: used,
    }
  }
  // ── 下界：det A[R,S] ≠ 0（整數多模 CRT，ν = 1）──────────
  let bsub = Mat::build(brank, brank, (i, j) => a.at(rowsel[i], best[j]))
  let (_, bz) = qmat_clear_denom(bsub)
  let (dv, _) = zdet_crt(bz, primes, c)
  let low = dv != 0N
  // ── 上界：r = min(m,n) 時自動；否則逐個非樞軸行驗張成 ───
  let mut up = true
  let mn = if m < n { m } else { n }
  if brank < mn {
    match minv(bsub) {
      None => up = false
      Some(bi) => {
        let cols = Mat::build(m, brank, (i, j) => a.at(i, best[j]))
        for col in 0..<n {
          let mut ispiv = false
          for q in best {
            if q == col {
              ispiv = true
            }
          }
          if !ispiv {
            let rhs = Array::makei(brank, i => a.at(rowsel[i], col))
            let x = qmul_cost(c, bi, Mat::build(brank, 1, (i, _j) => rhs[i]))
            let got = qmul_cost(c, cols, x)
            for i in 0..<m {
              if !got.at(i, 0).eq(a.at(i, col)) {
                up = false
              }
            }
          }
        }
      }
    }
  }
  { rcrank: brank, rcpiv: best, rclow: low, rcup: up, rcused: used, }
}

///|
/// 【L-08′】只重建 n 個整數前導主子式 —— ν 由 n²+n 降到 n。
///
/// ## 算式
///
/// 設 Gz = dd·G 為清分母後之整數 Gram，Δⱼ 為其 j 階前導主子式。
/// 𝔽p 上一次無開方 Cholesky 給出 Dⱼ⁽ᵖ⁾，而 Δⱼ ≡ ∏_{i≤j} Dᵢ⁽ᵖ⁾ (mod p)，
/// 故**一趟模消去同時給出全部 n 個前導主子式**。
///
/// ```text
///   Dⱼ(G) = Δⱼ(G)/Δⱼ₋₁(G) = Δⱼ(Gz) / (dd · Δⱼ₋₁(Gz))
///   det G = Δₙ(Gz)/ddⁿ
///   G 正定 ⟺ 全部 Δⱼ > 0        （Sylvester 判準）
/// ```
///
/// ## 為什麼不需要事後憑證
///
/// Δⱼ 是**整數**，|Δⱼ| 受 j 階區塊之 Hadamard 界控制。取 ∏p > 2·max_j Hⱼ，
/// 對稱提升即**無條件**等於 Δⱼ —— 這與 K-04（ℤ 行列式）用的是同一條定理。
/// 有理重建才需要「猜對了沒」的事後檢查；整數 CRT 不需要。
pub struct QMinors {
  /// 前導主子式 Δ₁ … Δₙ（Gz 之，整數）
  qmdelta : Array[BigInt]
  /// D₁ … Dₙ（G 之，= Gram–Schmidt 之 ‖qⱼ‖²）
  qmd : Array[Q]
  /// det G
  qmdet : Q
  /// 是否正定（Sylvester）
  qmspd : Bool
  /// 使用之素數個數
  qmused : Int
}

///|
/// ℚ LDLᵀ：以主餘子式 Δⱼ 重建（L-05 反例之改寫路徑；先驗 Hadamard 界定模數）。
pub fn qldlt_minors_crt(
  g : Mat[Q],
  primes : Array[Int64],
  c : Cost,
) -> QMinors? {
  let n = g.mrows
  let (dd, gz) = qmat_clear_denom(g)
  // 先驗界：Δⱼ 受 Gz 之 Hadamard 界控制（j ≤ n，取整個矩陣之界即足）
  let h = hadamard_bound(gz)
  let need = primes_needed(h, primes)
  let ps = ensure_primes(primes, need + 4)
  let crts : Array[Crt] = Array::makei(n, _ => Crt::new())
  let mut used = 0
  let mut t = 0
  while t < ps.length() && used < need {
    let p = ps[t]
    t = t + 1
    let ctx = FpCtx::make(p)
    charge_reduce_rows(c, gz)
    let fg = fp_of_big(gz, ctx)
    match fp_ldlt(fg, ctx) {
      None => {
        c.absorb_fp(ctx)
        continue
      }
      Some((_, d)) => {
        let mut acc = 1L
        for j in 0..<n {
          acc = ctx.mul(acc, d[j])
          charge_crt_step(c, crts[j].modulus())
          crts[j].absorb(acc, p)
        }
        c.absorb_fp(ctx)
        used = used + 1
      }
    }
  }
  if used < need {
    return None
  }
  let delta = Array::makei(n, j => crts[j].sym())
  let ddq = Q::make(dd, 1N)
  let dvec : Array[Q] = []
  let mut spd = true
  for j in 0..<n {
    if delta[j] <= 0N {
      spd = false
    }
    let prev = if j == 0 { 1N } else { delta[j - 1] }
    // Dⱼ(G) = Δⱼ(Gz) / (dd · Δⱼ₋₁(Gz))
    match Q::make(delta[j], 1N).div(ddq.mul(Q::make(prev, 1N))) {
      Some(v) => dvec.push(v)
      None => return None
    }
  }
  // det G = Δₙ(Gz)/ddⁿ
  let mut den = 1N
  for _j in 0..<n {
    den = den * dd
  }
  let det = Q::make(delta[n - 1], den)
  Some({ qmdelta: delta, qmd: dvec, qmdet: det, qmspd: spd, qmused: used, })
}

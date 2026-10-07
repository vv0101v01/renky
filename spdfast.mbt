///|
/// # N-75 Sylvester 判準接上加速層
///
/// ## 問題：全庫最貴的那個迴圈，從來沒有呼叫過加速層
///
/// 第十輪量完逐群掛鐘之後，N 群佔全庫 97% 的時間。再往下剖一層，
/// 單一葉節點最貴的是 `comb14_stats()` —— **9.4 秒**，佔 N-60 的九成。
/// 它做的事只有一件：對 630 個格的 Gram 判定正定。
///
/// 而 `is_positive_definite` 是這樣寫的：
///
/// ```text
///   for k in 1..n:  Δ_k = mdet(A[0..k, 0..k]);  if Δ_k ≤ 0 → false
/// ```
///
/// n 次**獨立**的行列式，第 k 次是 Θ(k³)，合計 Θ(n⁴)；而且每一次 ℚ 乘法
/// 都要做一次 gcd。S²(ℍ³) 的 Gram 是 78×78，Σk³ ≈ 9.3 × 10⁶ 次帶 gcd 的
/// ℚ 運算 —— 那 9.4 秒就是這麼來的。
///
/// 荒謬的地方在於：**這條路徑的正確解法，第七輪就已經寫好了。**
/// L-08′（`qldlt_minors_crt`）的整句話就是「一趟消去給出全部 n 個前導主子式」，
/// 實測 ×2.00 → ×107.63 且隨 n 單調上升。加速層蓋了三輪，而全庫最大的
/// ℚ 消費者從來沒有接上去。這不是效能問題，是**接線問題**。
///
/// ## 定理 N-75-1（Bareiss 之對角線即前導主子式序列）
///
/// 設 A 為 n×n 整數方陣，Bareiss 無分數消去（不作列交換）之中間量
///
/// ```text
///   a^{(k)}_{ij} = (a^{(k−1)}_{kk}·a^{(k−1)}_{ij} − a^{(k−1)}_{ik}·a^{(k−1)}_{kj}) / a^{(k−2)}_{k−1,k−1}
/// ```
///
/// 滿足 a^{(k−1)}_{kk} = Δ_k（A 之 k 階前導主子式）。
///
/// 證明：由 Sylvester 之恆等式（Desnanot–Jacobi）歸納可得
/// a^{(k)}_{ij} = det A[{0..k}∪{i}, {0..k}∪{j}]；取 i = j = k 即得
/// a^{(k−1)}_{kk} = det A[0..k, 0..k] = Δ_k。∎
///
/// **推論**：一趟 Θ(n³) 消去同時給出全部 n 個前導主子式，
/// 不需要 n 次獨立的行列式。這把 Θ(n⁴) 降到 Θ(n³)。
///
/// ## 定理 N-75-2（清分母不改變 Sylvester 判定）
///
/// 設 G ∈ ℚ^{n×n}，dd > 0 為全體分母之 lcm，Gz = dd·G 為整數矩陣。則
///
/// ```text
///   Δ_k(G) = Δ_k(Gz) / dd^k        （行列式之 k 重齊次性）
/// ```
///
/// 因 dd > 0 ⇒ dd^k > 0 ⇒ sign Δ_k(G) = sign Δ_k(Gz)。故
/// 「G 正定」⟺「Gz 之全部前導主子式 > 0」。∎
///
/// 這一步之所以要緊：它把 ℚ 的 gcd 成本一次付清（清分母只做一次 Θ(n²)），
/// 之後全程整數運算，再也不做 gcd。
///
/// ## 不作列交換是對的，不是偷懶
///
/// `zdet_bareiss` 在遇到零樞軸時會換列（因為它要算 det，換列只差一個符號）。
/// Sylvester 判準**不可以**換列：Δ_k 是**前導**主子式，換列之後算的就不是
/// 同一串量了。而且不換列不會漏判 —— 若 Δ_k = 0，矩陣就已經不正定，
/// 可以當場回傳 false。零樞軸在這裡不是待處理的退化情形，是答案本身。

///|
/// 無列交換之 Bareiss：回傳前導主子式序列 Δ₁ … Δ_m，
/// 其中 m 為「在遇到零樞軸前能算到的階數」。
///
/// 若回傳長度 < n，表示 Δ_{m+1} = 0（矩陣奇異於該階）。
pub fn zminors_bareiss(a0 : Array[Array[BigInt]], c : Cost) -> Array[BigInt] {
  let n = a0.length()
  let out : Array[BigInt] = []
  if n == 0 {
    return out
  }
  let m : Array[Array[BigInt]] = []
  for row in a0 {
    m.push(Array::makei(row.length(), i => row[i]))
  }
  let mut prev = 1N
  for k in 0..<n {
    let piv = m[k][k]
    out.push(piv)
    if piv == 0N {
      return out // Δ_{k+1} = 0 ⇒ 到此為止
    }
    if k == n - 1 {
      break
    }
    for i in (k + 1)..<n {
      for j in (k + 1)..<n {
        let p1 = cz_mul(c, piv, m[i][j])
        let p2 = cz_mul(c, m[i][k], m[k][j])
        let d = cz_sub(c, p1, p2)
        m[i][j] = cz_div(c, d, prev)
      }
      m[i][k] = 0N
    }
    prev = piv
  }
  out
}

///|
/// Sylvester 判準之 Θ(n³) 整數版（計量）。
pub fn spd_bareiss_cost(g : Mat[Q], c : Cost) -> Bool {
  if g.mrows != g.mcols {
    return false
  }
  if !is_hermitian(g) {
    return false
  }
  let n = g.mrows
  if n == 0 {
    return true
  }
  let (_, gz) = qmat_clear_denom(g)
  let ds = zminors_bareiss(gz, c)
  if ds.length() != n {
    return false // 中途碰到零樞軸 ⇒ 某階 Δ = 0 ⇒ 不正定
  }
  for d in ds {
    if d <= 0N {
      return false
    }
  }
  true
}

///|
/// Sylvester 判準之 Θ(n³) 整數版。語意與 `is_positive_definite` 完全相同。
pub fn spd_bareiss(g : Mat[Q]) -> Bool {
  spd_bareiss_cost(g, Cost::new())
}

///|
/// 前導主子式序列（ℚ 版，Δ_k(G) = Δ_k(Gz)/dd^k）。
///
/// 供義務對帳用：不只比布林值，連 n 個數字都要逐個對。
pub fn qminors_bareiss(g : Mat[Q]) -> Array[Q] {
  let n = g.mrows
  let out : Array[Q] = []
  if n == 0 {
    return out
  }
  let (dd, gz) = qmat_clear_denom(g)
  let ds = zminors_bareiss(gz, Cost::new())
  let mut p = 1N
  for k in 0..<ds.length() {
    p = p * dd
    out.push(Q::make(ds[k], p))
    if ds[k] == 0N {
      break
    }
    ignore(k)
  }
  out
}

///|
/// 樸素 Sylvester（Θ(n⁴)，n 次獨立行列式）之計量孿生體 —— 基準路徑。
///
/// 與 `is_positive_definite` 逐步對應，差別只在每次 ℚ 乘法都記一筆。
pub fn spd_naive_cost(g : Mat[Q], c : Cost) -> Bool {
  if !is_hermitian(g) {
    return false
  }
  let n = g.mrows
  for k in 1..<(n + 1) {
    let sub = g.sub(0, k, 0, k)
    // 以清分母後之整數行列式計量（與 Bareiss 同幣別，才能比）
    let (dd, sz) = qmat_clear_denom(sub)
    let d = zdet_bareiss(sz, c)
    let _ = dd
    if d <= 0N {
      return false
    }
  }
  true
}

///|
/// 三路一致性之單點比對結果。
pub struct SpdCmp {
  /// 矩陣階
  scn : Int
  /// 樸素 Sylvester 之判定
  snaive : Bool
  /// Bareiss 之判定
  sbare : Bool
  /// 樸素路徑之字乘法數
  scost_naive : Int64
  /// Bareiss 之字乘法數
  scost_bare : Int64
}

///|
/// 對一個 Gram 同時跑兩路並計量。
pub fn spd_compare(g : Mat[Q]) -> SpdCmp {
  let c1 = Cost::new()
  let c2 = Cost::new()
  let a = spd_naive_cost(g, c1)
  let b = spd_bareiss_cost(g, c2)
  {
    scn: g.mrows,
    snaive: a,
    sbare: b,
    scost_naive: c1.wmul,
    scost_bare: c2.wmul,
  }
}

// ---------------------------------------------------------------------------
//  【第十八輪】正定判定之層間分派：把 L 層的 CRT 主子式接進 N 群
// ---------------------------------------------------------------------------

///|
/// 正定判定的交叉點（階數）。
///
/// ## 實測網格（35 × 45 普查表之 1,575 個 Gram，依階數分段）
///
/// ```text
///   階數區間      個數    Bareiss     CRT 主子式    比值
///   ( 0, 16]      1378     121 ms       122 ms     ×0.99
///   (16, 40]       142     248 ms       135 ms     ×1.84
///   (40, 80]        35     583 ms       240 ms     ×2.43
///   (80,  ∞)        20    2780 ms      1088 ms     ×2.55
/// ```
///
/// 交叉點在 n ≈ 16，與 L-08′ 的模型一致：Bareiss 保留**精確整數子式**，
/// 中間量隨階數成長到子式本身的位元數；CRT 把每個模下的消去壓在
/// 機器字內，代價是要跑 k 個素數再重建。小階時 k 個素數的固定成本
/// 蓋過收益，大階時中間量爆炸使 Bareiss 一面倒地輸。
///
/// 1,575 格上兩路判定結果**全部一致**（N-90 之義務逐格對帳）。
pub const SPD_CRT_MIN : Int = 17

///|
/// 成本模型所假設的輸入位元寬。
///
/// 註冊表的 Gram 元素都是小有理數（清分母後多在 16 位元內），
/// 故以 16 代入 `plan_spd`。這是一個**關於資料的假設**，寫在這裡
/// 而不是藏在呼叫點，因為換一批 Gram 就該重新檢視它。
pub const SPD_MODEL_BITS : Int = 16

///|
/// 正定判定之分派器：小階走不換列 Bareiss，大階走 L 層之 CRT 主子式。
///
/// 回傳 (是否正定, 是否走了 CRT 路徑)。第二個分量供義務統計覆蓋率，
/// 不是給呼叫端判斷用的 —— 兩條路徑同值是本分派器的前提，
/// 不是呼叫端要關心的事。
pub fn spd_dispatch_x(
  g : Mat[Q],
  primes : Array[Int64],
  c : Cost,
) -> (Bool, Bool) {
  // 【第二十輪】由寫死的交叉點改為成本模型 plan_spd。
  //
  // 第十八輪把交叉點寫成常數 17，並在當時就記下「換機器或換資料
  // 就要重量」。改成模型之後不只是比較漂亮 —— 它**更快**：
  // 1,575 格上常數版 1,963 ms、模型版 1,760 ms、全 Bareiss 4,880 ms，
  // 三路結果一致。模型快在它會在**損益兩平帶**拒絕切換（實測
  // n ≤ 16 時比值 ×0.99），而常數 17 會在那裡就切過去。
  // 模型只在 1,575 格中的 88 格判定走快路徑。
  if !plan_spd(g.mrows, SPD_MODEL_BITS).use_fast {
    return (spd_bareiss(g), false)
  }
  match qldlt_minors_crt(g, primes, c) {
    Some(m) => (m.qmspd, true)
    // CRT 路徑失敗（素數全壞）時退回 Bareiss —— 分派器不得因為
    // 快路徑不可用就改變答案
    None => (spd_bareiss(g), false)
  }
}

///|
/// 正定判定之分派器（只回答是否正定）。
pub fn spd_fast(g : Mat[Q]) -> Bool {
  spd_dispatch_x(g, prime_pool(48), Cost::new()).0
}

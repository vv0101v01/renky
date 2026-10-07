///|
/// # N-36 取樣分布修復
///
/// N-26 的發現：`rank/⊞/·` 在定律表上判為**成立**，而它是假的 ——
/// 反例 A = diag(1, −1)、B = [1] 給出 rank(A⊞B) = 1 ≠ 2 = rank A · rank B。
/// 假陽性的來源不是搜尋邏輯，是**取樣分布**：`rand_gram` 恆產生正定矩陣，
/// 正定矩陣恆滿秩，於是任何關於 rank 的錯誤規則都找不到反例。
///
/// 取樣分布因此不是實作細節。它決定了哪些律推不翻，和 Φ 集、⊙ 集一樣，
/// 是搜尋空間的一部分。本檔把它提為可替換的參數，並提供四種分布。

///|
/// 分布甲：正定（原本唯一的分布）。恆滿秩、恆可逆。
pub fn samp_gram(rng : Rng, n : Int) -> Mat[Q] {
  rand_gram(rng, n)
}

///|
/// 分布乙：不定對稱（可逆但有正有負的慣性）。
/// 讓「假設特徵值全正」的規則露出破綻。
pub fn samp_indef(rng : Rng, n : Int) -> Mat[Q] {
  rand_sym_q(rng, n)
}

///|
/// 分布丙：半正定但**降秩**（秩 ≤ n−1）。
/// 取 (n−1)×n 的隨機 M，令 G = MᵀM —— 秩至多 n−1，必不可逆。
/// 這是推翻 rank 類錯誤規則的關鍵分布。
pub fn samp_singular(rng : Rng, n : Int) -> Mat[Q] {
  if n <= 1 {
    return Mat::zeros(1, 1)
  }
  let m : Mat[Q] = Mat::build(n - 1, n, (_i, _j) => {
    Q::of_int(rng.next_below(7) - 3)
  })
  m.transpose().times(m)
}

///|
/// 標準混合樣本集：尺寸 × 分布的具體清單。
///
/// 設計上保留原本的兩組正定樣本（故舊有的全部結論不會因換分布而消失），
/// 再各加一組不定與一組降秩。四個樣本、每個候選都跑完 ——
/// **一條律要判成立，必須在每一種分布下都成立**。
///
/// 為何不用「全域輪替」把三種分布平均分給各候選：那樣每個候選只會看到
/// 其中兩種，於是推翻掉一批假陽性的同時又放進另一批。實測正是如此 ——
/// 輪替式混合推翻了 rank/⊞/·（對的），卻讓 inv/⊗/⊗ₛ、inv/⊕/⊗ₛ、
/// adj/⊕/⊗ₛ、det/⊕/^ 四條因為「兩側同時為 0」而空洞地成立（錯的）。
pub fn law_samples_mixed() -> Array[(Int, Int, (Rng, Int) -> Mat[Q])] {
  [
    (2, 2, samp_gram),
    (2, 3, samp_gram),
    (2, 3, samp_indef),
    (2, 3, samp_singular),
  ]
}

///|
/// 兩張定律表之逐條差異。回傳 (Φ, C, ⊙, 甲裁決, 乙裁決) 之清單。
pub fn law_diff(
  x : Array[LawCand],
  y : Array[LawCand],
) -> Array[(String, String, String, Bool, Bool)] {
  let out : Array[(String, String, String, Bool, Bool)] = []
  for i in 0..<x.length() {
    if i < y.length() && x[i].cholds != y[i].cholds {
      out.push((x[i].cphi, x[i].ccomb, x[i].crule, x[i].cholds, y[i].cholds))
    }
  }
  out
}

///|
/// 輪替式混合取樣器 —— **保留作為反例**（定理 198-3）。
///
/// 它把三種分布平均分給各候選，於是每個候選只看到其中兩種。
/// 結果是：推翻了 rank/⊞/·（對的），同時又讓四條 det 類規則因為
/// 「兩側同時為 0」而空洞地成立（錯的）。保留它，是因為「換一個分布」
/// 這個直覺解法會產生什麼後果，本身就是本條要記錄的結果。
let samp_turn : Array[Int] = [0]

///|
pub fn samp_mixed(rng : Rng, n : Int) -> Mat[Q] {
  let k = samp_turn[0] % 3
  samp_turn[0] = samp_turn[0] + 1
  match k {
    0 => samp_gram(rng, n)
    1 => samp_indef(rng, n)
    _ => samp_singular(rng, n)
  }
}

///|
pub fn samp_reset() -> Unit {
  samp_turn[0] = 0
}

///|
/// 修復後之定律表（共用快取，比照 N-35）。
///
/// `law_search_std` 保留原本的正定分布不動 —— N-26 的條目正是以那張表
/// 為證據，記錄「引擎產出了一個假陽性」這件事；把它改掉等於抹掉證據。
/// 本函式提供修復後的表，為下游（N-31 的合成器組裝）應採用者。
let law_fixed_cache : Array[Array[LawCand]] = []

///|
pub fn law_search_fixed(rng : Rng) -> Array[LawCand] {
  if law_fixed_cache.length() == 0 {
    law_fixed_cache.push(law_search_samples(rng, law_samples_mixed()))
  }
  law_fixed_cache[0]
}

///|
/// 定律表之指紋（N-44）。
///
/// 把裁決序列壓成一個可比對的字串。用途不是加密，是**版本控管**：
/// 定律表是本庫的核心產物，而它會隨 Φ 集、⊙ 集、取樣分布、甚至隨機種子
/// 而變。若沒有指紋，這些變動會悄悄發生而沒人察覺 —— 一個人改了取樣器、
/// 定律表少了兩條律、報告照樣產出、沒有任何東西失敗。
///
/// 指紋同時編碼「成立數」與「成立位置」：前者抓數量變化，後者抓
/// 「一進一出、總數不變」這種最難察覺的變動。
pub fn law_digest(tbl : Array[LawCand]) -> String {
  let mut holds = 0
  let mut acc = 0L
  for i in 0..<tbl.length() {
    if tbl[i].cholds {
      holds = holds + 1
      // 位置加權，使「一進一出」必定改變指紋
      acc = (acc * 131L + (i + 1).to_int64()) % 1000000007L
    }
  }
  tbl.length().to_string() + ":" + holds.to_string() + ":" + acc.to_string()
}

///|
/// `law_samples_mixed` 之分布標籤（與該函式並列維護）。
///
/// 為何需要它：N-45 的生成器要把「在哪些分布上測過」寫進條目，而分布是
/// 以函式值傳遞的、取不到名字。把標籤放在樣本清單旁邊，兩者一起改，
/// 比讓生成器硬寫一個字串安全。
pub fn law_samples_label() -> String {
  "正定 ×2／不定 ×1／降秩 ×1"
}

///|
/// `law_samples_mixed` 之尺寸對，供生成器寫進條目
pub fn law_samples_dims() -> String {
  let parts : Array[String] = []
  for s in law_samples_mixed() {
    let (n, m, _f) = s
    parts.push("(" + n.to_string() + "," + m.to_string() + ")")
  }
  parts.join("")
}

///|
/// # 第十三輪義務自證：N-83 … N-85
///
/// F-01（正交直和）與 F-02（張量積）的目錄欄位都寫「任意兩空間」，
/// 而原本的義務各只跑**一對**具體空間。本組把它們與註冊表的 45 個
/// 空間全面相乘：45 × 45 = 2025 個有序配對。

// ---------------------------------------------------------------------------

///|
/// 【N-83】F-01 正交直和 × 全部空間配對。
pub fn ob_n83() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let r = f_sum_scan(rng, 24)
  if r.q7pairs != 2025 {
    ok = false
  }
  // 全部判準皆須跑滿 2025 對 —— ⊕ 之維數至多 24，沒有任何一格需要略過
  if r.q7dim != 2025 ||
    r.q7det != 2025 ||
    r.q7detrun != 2025 ||
    r.q7tr != 2025 ||
    r.q7spd != 2025 ||
    r.q7spdrun != 2025 ||
    r.q7comm != 2025 {
    ok = false
  }
  // IPSpace 層亦跑滿：真的呼叫 direct_sum 造物件並抽查基底內積
  if r.q7ip != 2025 || r.q7iprun != 2025 {
    ok = false
  }
  if r.q7dmax != 24 || r.q7dsum != 18990 {
    ok = false
  }
  if r.q7digest != "2025:18990:891726422" {
    ok = false
  }
  // 原始 F-01 仍須通過（本條是擴充，不是取代）
  if !ob_f01().ok {
    ok = false
  }
  mk_check(
    "N-83 正交直和 × 全部空間配對",
    ok,
    r.q7inst,
    "F-01 的目錄欄位寫「任意兩空間」，而其義務只跑一對（poly_space_l2(2) ⊕ sym_matrix_space(2)）—— 全稱命題，單點證據。本條與註冊表 45 個空間全面相乘：45 × 45 = " +
    r.q7pairs.to_string() +
    " 個有序配對，維數和 " +
    r.q7dsum.to_string() +
    "，最大 " +
    r.q7dmax.to_string() +
    "。逐對驗七件事，全部 2025／2025：維數相加、Gram 為分塊對角、det = det·det、tr = tr + tr、正定 ⟺ 兩因子皆正定、交換律 P⊕Q ≅ Q⊕P（由區塊對調置換 σ(u) = u+d_B／u−d_A 具名見證）、以及 **IPSpace 層抽查** —— 真的呼叫 direct_sum 造出空間物件、每對抽 3 組基底對比對 ⟨eᵤ,e_v⟩ 與分塊對角的對應元。最後一項是唯一非平凡的：前六項以 qblock_diag 為模型，「Gram 是分塊對角」在那一層是定義而非定理；只有真的造出物件去問它的內積，才驗到了建構子的實作。⊕ 之維數至多 24，故 IPSpace 層也跑滿 2025 對，無一略過。指紋 " +
    r.q7digest +
    "。原 F-01 一併重跑並通過（本條是擴充，不是取代）。",
  )
}

// ---------------------------------------------------------------------------

///|
/// 【N-84】F-02 張量積 × 全部空間配對。
pub fn ob_n84() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let r = f_tensor_scan(rng, 36, 24)
  if r.q7pairs != 2025 {
    ok = false
  }
  // 全表判準（Θ(d) 或 Θ(d²)）
  if r.q7dim != 2025 || r.q7tr != 2025 || r.q7comm != 2025 {
    ok = false
  }
  // 受維數上限的判準：跑過的必須全對，且覆蓋率必須如實
  if r.q7detrun != 1495 || r.q7det != r.q7detrun {
    ok = false
  }
  if r.q7spdrun != 1495 || r.q7spd != r.q7spdrun {
    ok = false
  }
  if r.q7iprun != 1762 || r.q7ip != r.q7iprun {
    ok = false
  }
  if r.q7dmax != 144 || r.q7dsum != 44521 {
    ok = false
  }
  if r.q7digest != "2025:44521:751220003" {
    ok = false
  }
  // 快路徑之前提：註冊表的 sg 就是 gram_of_space(space())，
  // 且 tensor_space_g 與 tensor_space 回傳同一個空間
  let (nsp, gok, mrep, tok) = f_tensor_fastpath_check()
  if nsp != 45 || gok != 45 || mrep != 81 || tok != 81 {
    ok = false
  }
  if !ob_f02().ok {
    ok = false
  }
  mk_check(
    "N-84 張量積 × 全部空間配對",
    ok,
    r.q7inst,
    "F-02 的目錄欄位寫「任意兩空間」，而其義務只跑一對（poly_space_l2(2) ⊗ euclidean_space(2)）。本條與註冊表 45 個空間全面相乘：" +
    r.q7pairs.to_string() +
    " 個有序配對，維數和 " +
    r.q7dsum.to_string() +
    "，最大 " +
    r.q7dmax.to_string() +
    "（ℍ³ ⊗ ℍ³）。**全表判準**（2025／2025）：維數相乘、tr(A⊗B) = tr(A)·tr(B)、交換律 P⊗Q ≅ Q⊗P 由完美洗牌 σ(i·d_B+j) = j·d_A+i 具名見證 —— 見證以逐元指標映射檢查（PᵀG₁P = G₂ ⟺ G₁[u][v] = G₂[σu][σv]），省去物化置換陣與兩次 Θ(d³) 乘法，在 d = 144 時約差 72 倍。**受維數上限的判準**：det(A⊗B) = det(A)^{n_B}·det(B)^{n_A} 在 dim ≤ 24 的 " +
    r.q7detrun.to_string() +
    " 對（73.8%）直接計算比對、全中；正定之因子判定（譜為 {λᵢμⱼ}，故 A⊗B 正定 ⟺ A、B 皆正定）同樣在 " +
    r.q7spdrun.to_string() +
    " 對上與直接 Sylvester 計算核對、全中 —— 這條定理把 Θ((n_P·n_Q)³) 降為 Θ(n_P³ + n_Q³)，在 12 ⊗ 12 時約差 (144/24)³ ≈ 216 倍；**IPSpace 層抽查**（真的造 tensor_space 物件、每對抽 3 組基底對）在 dim ≤ 36 的 " +
    r.q7iprun.to_string() +
    " 對（87.0%）全中。超出上限者明確記為未驗，不計入通過。快路徑之前提另行驗證：tensor_space 內部對每個因子呼叫 gram_of_space（Θ(d³)），在 45 × 45 的表裡同一個因子被重算 45 次，故改用 tensor_space_g 由呼叫端傳入因子 Gram；其正當性要求 (a) 註冊表登記的 sg 確實等於 gram_of_space(space())，" +
    gok.to_string() +
    "／" +
    nsp.to_string() +
    " 成立，(b) 兩條路徑造出的張量空間逐元相同，在 9 族代表之 " +
    tok.to_string() +
    "／" +
    mrep.to_string() +
    " 對成立。指紋 " +
    r.q7digest +
    "。原 F-02 一併重跑並通過。",
  )
}

// ---------------------------------------------------------------------------

///|
/// 【N-85】⊕ 與 ⊗ 之分配律與結合律。
pub fn ob_n85() -> Check {
  let mut ok = true
  let l = f_law_scan(512)
  if l.l7triples != 729 {
    ok = false
  }
  // 分配律與兩條結合律皆須全成立
  if l.l7dist != 729 {
    ok = false
  }
  if l.l7assoc_run != 729 || l.l7assoc_sum != 729 || l.l7assoc_ten != 729 {
    ok = false
  }
  // 兩側對照：維數相容的三元組恰為 d_P = d_Q 者
  if l.l7wrongable != 261 {
    ok = false
  }
  if l.l7wrong + l.l7blind != l.l7wrongable {
    ok = false
  }
  // 盲點預測必須逐格相符，且兩端都要真的出現過
  if l.l7blindok != l.l7wrongable {
    ok = false
  }
  if l.l7wrong == 0 || l.l7blind == 0 {
    ok = false
  }
  mk_check(
    "N-85 直和與張量積之分配律與結合律",
    ok,
    l.l7triples * 3 + l.l7wrongable,
    "⊕ 與 ⊗ 必須互相配合，否則兩個建構子各自正確也拼不出一個張量範疇。在 9 族代表（座標／函數／矩陣／多項式／四元數／複結構／外代數／子空間／其他 各取維數最小者）之全部 " +
    l.l7triples.to_string() +
    " 個三元組上驗三條律。**分配律** P⊗(Q⊕R) ≅ (P⊗Q)⊕(P⊗R)：" +
    l.l7dist.to_string() +
    "／" +
    l.l7triples.to_string() +
    "，由具名指標映射見證 —— 左側 u = i·(d_Q+d_R)+k，k < d_Q 時落在第一塊 i·d_Q+k，否則落在第二塊 d_P·d_Q + i·d_R + (k−d_Q)。**結合律** (P⊕Q)⊕R = P⊕(Q⊕R) 與 (P⊗Q)⊗R = P⊗(Q⊗R)：各 " +
    l.l7assoc_sum.to_string() +
    "／" +
    l.l7assoc_ten.to_string() +
    " 全數成立，而且是**逐元相等**不是僅同構 —— 分塊對角與 Kronecker 在本庫的座標約定下都嚴格結合，連置換都不需要。這一點值得分開講：分配律要見證、結合律不要，兩者不是同一種「成立」。**兩側對照**：錯式 (P⊗Q)⊕(Q⊗R)（把第二塊的 P 誤寫成 Q）只在維數相容時才有意義，而相容 ⟺ d_P·d_R = d_Q·d_R ⟺ d_P = d_Q，實測恰為 " +
    l.l7wrongable.to_string() +
    " 個三元組。其中抓到 " +
    l.l7wrong.to_string() +
    "、分辨不出 " +
    l.l7blind.to_string() +
    "；而**盲點是可預測的** —— d_P = d_Q 時兩式只差 P⊗R ↔ Q⊗R，故相等 ⟺ G_P = G_Q。此預測與實測逐格相符 " +
    l.l7blindok.to_string() +
    "／" +
    l.l7wrongable.to_string() +
    "，且兩端（抓到、抓不到）都真的出現過，故這條對照既非恆真也非恆假。",
  )
}

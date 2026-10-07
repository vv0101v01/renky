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
  let r = f_tensor_scan(rng, 24)
  if r.q7pairs != 2025 {
    ok = false
  }
  // 全表判準（Θ(d) 或 Θ(d²)）
  if r.q7dim != 2025 || r.q7tr != 2025 || r.q7comm != 2025 {
    ok = false
  }
  // 【第十四輪】三項受限判準全部升到 2025/2025（§24.5 第 1、2 筆）
  if r.q7detrun != 2025 || r.q7det != r.q7detrun {
    ok = false
  }
  if r.q7spdrun != 2025 || r.q7spd != r.q7spdrun {
    ok = false
  }
  if r.q7iprun != 2025 || r.q7ip != r.q7iprun {
    ok = false
  }
  // ℚ 軌直接比對之子集仍須跑，用來證明模 p 與 LDL⊗ 兩條新路徑沒有說謊
  if r.q7detqrun != 1495 || r.q7detq != r.q7detqrun {
    ok = false
  }
  if r.q7spdqrun != 1495 || r.q7spdq != r.q7spdqrun {
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
    "（ℍ³ ⊗ ℍ³）。**第十四輪起全部七項判準皆為 2025／2025，無一略過**（第十三輪時 det 與正定只到 73.8%、IPSpace 層只到 87.0%）：維數相乘、tr(A⊗B) = tr(A)·tr(B)（左式以 Kronecker 結構逐對角元現算）、交換律由完美洗牌 σ(i·d_B+j) = j·d_A+i 以 Θ(d²) 逐元指標映射見證（兩側皆不物化）、行列式 det(A⊗B) = det(A)^{n_B}·det(B)^{n_A} 走**模 p** 路徑（Fp 上每元一個機器字，Θ(d³) 高斯消去全程無係數膨脹，故 144 階也能直接算；全表僅 0.2 秒）、正定走 **Kronecker LDLᵀ 證書**（定理 K-2：A⊗B = (L_A⊗L_B)(D_A⊗D_B)(L_A⊗L_B)ᵀ，而 L_A⊗L_B 仍為單位下三角，故右式即 A⊗B 之 LDLᵀ；成本 Θ(n_A³+n_B³) 而非 Θ((n_An_B)³)）、IPSpace 層抽查改用**惰性張量空間**（定理 K-1，內積不需要 Gram 先存在）。兩條新路徑都不許自說自話：ℚ 軌的直接計算仍在 dim ≤ 24 的 " +
    r.q7detqrun.to_string() +
    " 對上跑，det 與正定各自與模 p、LDL⊗ 的結論逐對帳，" +
    r.q7detq.to_string() +
    "／" +
    r.q7spdq.to_string() +
    " 全中 —— 一條只在自己的軌上自洽的捷徑，等於沒有驗。快路徑之另一前提（註冊表 sg = gram_of_space(space())）獨立驗證 " +
    gok.to_string() +
    "／" +
    nsp.to_string() +
    "，兩路張量空間逐元相同 " +
    tok.to_string() +
    "／" +
    mrep.to_string() +
    "。指紋 " +
    r.q7digest +
    "（與第十三輪一位元未變）。原 F-02 一併重跑並通過。",
  )
}

// ---------------------------------------------------------------------------

///|
/// 【N-85】⊕ 與 ⊗ 之分配律與結合律。
pub fn ob_n85() -> Check {
  let mut ok = true
  let l = f_law_scan(256)
  // 【第十四輪】Gram 層由 729（只有族代表）擴到 9477（三軸各自完整）
  if l.l7triples != 9477 {
    ok = false
  }
  if l.l7dist != 9477 {
    ok = false
  }
  // 【第十五輪】45³ 維數層掃描已移除（恆真之算術恆等式，訊號為 0）
  if l.l7dimtot != 0 || l.l7dimtri != 0 {
    ok = false
  }
  // 三軸各自完整：由掃描當場記錄，不是手寫布林式
  if l.l7axis0 != 45 || l.l7axis1 != 45 || l.l7axis2 != 45 {
    ok = false
  }
  // 結合律為單一算子之結構恆等式，仍在 9 族代表之 729 個三元組上
  if l.l7assoc_run != 729 || l.l7assoc_sum != 729 || l.l7assoc_ten != 729 {
    ok = false
  }
  // 兩側對照：維數相容的三元組恰為 d_P = d_Q 者
  if l.l7wrongable != 2259 {
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
    l.l7triples * 2 + l.l7assoc_run * 2 + l.l7wrongable,
    "⊕ 與 ⊗ 必須互相配合，否則兩個建構子各自正確也拼不出一個張量範疇。**第十四輪起 Gram 層由 729（只有 9 族代表）擴到 " +
    l.l7triples.to_string() +
    " 個三元組：三軸各自完整 —— 任一軸可取遍全部 45 個空間，其餘兩軸為族代表，故每一個空間都在每一個位置上出現過**（第十三輪時只在第一個位置），而且**這個條件由掃描當場記錄而非手寫布林式**：三個位置各自見過 " +
    l.l7axis0.to_string() +
    "／" +
    l.l7axis1.to_string() +
    "／" +
    l.l7axis2.to_string() +
    " 個空間，少一個就紅燈。第十四輪另跑的 45³ = 91,125 維數層掃描**已於第十五輪移除** —— dim P·(dim Q + dim R) = dim P·dim Q + dim P·dim R 是整數乘法的分配律，對任何三個正整數恆成立，跑 91,125 次只是把同一條算術恆等式抄 91,125 遍；它曾佔全庫實例數的 47.5% 而提供的訊號是 0。實例數不是覆蓋率。**分配律** P⊗(Q⊕R) ≅ (P⊗Q)⊕(P⊗R)：" +
    l.l7dist.to_string() +
    "／" +
    l.l7triples.to_string() +
    "，由具名指標映射見證（左側 u = i·(d_Q+d_R)+k，k < d_Q 時落在第一塊 i·d_Q+k，否則落在第二塊 d_P·d_Q + i·d_R + (k−d_Q)），且**兩側皆不物化** —— 每一元 O(1)，省去三趟 Θ(d²) 的配置與寫入。**結合律** (P⊕Q)⊕R = P⊕(Q⊕R) 與 (P⊗Q)⊗R = P⊗(Q⊗R)：各 " +
    l.l7assoc_sum.to_string() +
    "／" +
    l.l7assoc_ten.to_string() +
    "，逐元相等不是僅同構 —— 以 u = (i·n_B+j)·n_C+k 與 u = i·n_Bn_C+(j·n_C+k) 索引兩種括號法**給出同一個 u**，兩邊之元皆為 A[i][i']·B[j][j']·C[k][k']（命題 K-5）。結合律是單一算子的結構恆等式、與是哪些空間無關，故仍只在 9 族代表之 729 個三元組上跑；分配律混合兩個算子且對照有內容，才需要寬覆蓋。這一點值得分開講：分配律要見證、結合律不要，兩者不是同一種「成立」。**兩側對照**：錯式 (P⊗Q)⊕(Q⊗R)（把第二塊的 P 誤寫成 Q）只在維數相容時才有意義，而相容 ⟺ d_P·d_R = d_Q·d_R ⟺ d_P = d_Q，實測恰為 " +
    l.l7wrongable.to_string() +
    " 個三元組。其中抓到 " +
    l.l7wrong.to_string() +
    "、分辨不出 " +
    l.l7blind.to_string() +
    "；而**盲點是可預測的** —— d_P = d_Q 時兩式只差 P⊗R ↔ Q⊗R，故相等 ⟺ G_P = G_Q。此預測與實測逐格相符 " +
    l.l7blindok.to_string() +
    "／" +
    l.l7wrongable.to_string() +
    "，且兩端都真的出現過，故這條對照既非恆真也非恆假。全 45³ 於 Gram 層實測約需 89 秒，不跑，照實記。",
  )
}

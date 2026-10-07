///|
/// N-42 之義務：律之複合代數。
///
/// 本條是本庫第一條**關於律本身的律**（元層級）。它的危險也正在這裡 ——
/// 一條能從 15 條律印出 60 條律的規則，如果有錯，錯誤會被乘以四。
/// 故本義務的重心不是展示推導，而是把推導當成**待推翻的假說**：
/// 把推導集逐條實測，看它是否真的全部落在「成立」那一側；
/// 再以恆有定義的 adj 重新裁決那些證據有缺口的候選。
///
/// 分層（比照 N-35）：本義務跑推導集 60 條；
/// 5×8×3×3 = 360 條的全量普查（混淆表第三、四格）是一次性的，
/// 由 cmd/lawsearch 承接。兩者逐條可比 —— 每個候選的取樣種子由
/// 候選名雜湊決定，與它在枚舉中的位置無關。
pub fn ob_n42() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let tbl = law_search_fixed(rng)
  let ds = compose_derive(tbl)
  let xs = compose_scan_std(rng)
  let (dh, dn, uh, un) = compose_confusion(xs)
  let samples = law_samples_mixed()

  // ── 定理 201-1（複合定理之健全性）────────────────────────
  // 推導出的每一條複合律都必須經得起實測。dn 就是反例數，必須是 0。
  if dn != 0 {
    ok = false
  }
  if dh != ds.length() || xs.length() != 60 {
    ok = false
  }
  // 本義務只掃推導集，故後兩格恆為 0；全量普查見 cmd/lawsearch。
  if uh != 0 || un != 0 {
    ok = false
  }

  // ── 命題 201-2（生產力：15 → 60，零次矩陣運算）──────────
  let mut nhold = 0
  for t in tbl {
    if t.cholds {
      nhold = nhold + 1
    }
  }
  if nhold != 15 || ds.length() != 60 {
    ok = false
  }
  // 32 個相異的複合演算法，且沒有一個在原本的八元 Φ 集內
  let ncomp = compose_phi_count(xs, true)
  if ncomp != 32 {
    ok = false
  }
  for x in xs {
    if !(phi_by_name(x.xphi()) is None) {
      ok = false // Φ₂∘Φ₁ 竟然已經是註冊表裡的 Φ —— 那就不是新演算法
    }
  }
  // 推導集之指紋（沿用 N-44 之格式）
  let dig = compose_digest(xs)
  if dig != "60:60:469518071" {
    ok = false
  }

  // ── 命題 201-4（adj 不可作為內層，而引擎的沉默是對的）────
  // adj 之律為 adj(A⊗B) = (det A)^{m−1}(det B)^{n−1}(adj A ⊗ adj B)，
  // 規則 ⊗ₛ 不是組合子，故定理 201-1 接不上去。若此時複合律其實成立，
  // 這條定理就漏掉了一整類。實測三條純量規則，det∘adj/⊗/* 應全數推翻。
  let mut adj_inner_derived = 0
  for d in ds {
    let (_o, i, _c, _m, _r) = d
    if i == "adj" {
      adj_inner_derived = adj_inner_derived + 1
    }
  }
  if adj_inner_derived != 0 {
    ok = false
  }
  for r in ["·", "+", "^"] {
    match
      comp_check(
        "det",
        "adj",
        "⊗",
        r,
        samples,
        comp_rng_of("det", "adj", "⊗", r),
      ) {
      Some((v, _vac)) => if v.holds { ok = false }
      None => ok = false
    }
  }

  // ── 定理 201-5（⊥ 盲區：複合會放大取樣分布的失效）────────
  // N-36 為了推翻 rank 類假陽性，加入了一個降秩（奇異）樣本。但 qadj 與
  // qinv_gauss 在奇異輸入上回傳 ⊥，於是兩側同時為 ⊥ 而被判成相符 ——
  // 那個樣本對 inv 類與 adj 類候選毫無鑑別力。先量這個缺口有多大。
  let nvac = compose_vacuous_count(xs)
  if nvac != 24 {
    ok = false
  }
  // 對基礎定律表本身回頭稽核：15 條成立之律中有幾條帶空洞樣本
  let base_vac = law_vacuity_count(tbl, samples)
  if base_vac != 3 {
    ok = false
  }
  // 再以**恆有定義**的餘因子 adj 重新裁決四條「成立但推導不出」者
  // （它們由 cmd/lawsearch 的全量普查指認）。若只是 ⊥ 造成的假象，這裡會翻。
  // 兩次裁決共用同一組矩陣（種子由候選名決定），故翻轉可歸因於 adj 實作本身。
  let suspects : Array[(String, String, String, String)] = [
    ("rank", "inv", "⊞", "·"),
    ("rank", "adj", "⊗", "·"),
    ("rank", "adj", "⊕", "+"),
    ("rank", "adj", "⊞", "·"),
  ]
  let mut flips = 0
  let flipped : Array[String] = []
  for sp in suspects {
    let (o, i, cb, r) = sp
    let crng = comp_rng_of(o, i, cb, r)
    let before = match comp_check(o, i, cb, r, samples, crng) {
      Some((v, _vac)) => v.holds
      None => {
        ok = false
        false
      }
    }
    // 四條都必須在現行（det·inv 版）adj 下成立，否則嫌疑名單本身就過期了
    if !before {
      ok = false
    }
    match
      comp_check_with(
        phi_by_name_total,
        o,
        i,
        cb,
        r,
        samples,
        comp_rng_of(o, i, cb, r),
      ) {
      Some((v, _vac)) =>
        if v.holds != before {
          flips = flips + 1
          flipped.push(o + "∘" + i + "/" + cb + "/" + r)
        }
      None => ok = false
    }
  }
  // 恰有兩條翻轉：rank∘adj/⊗/· 與 rank∘adj/⊕/+
  if flips != 2 {
    ok = false
  }
  if flipped.length() == 2 &&
    (flipped[0] != "rank∘adj/⊗/·" || flipped[1] != "rank∘adj/⊕/+") {
    ok = false
  }

  // ── 命題 201-6（複合放大增益，而不是稀釋）────────────────
  // 直接路徑在 nm 階矩陣上跑兩次演算法，分解路徑在 n、m 階上各跑兩次。
  // 故複合律的增益應**高於**其任一構件單獨的增益。
  let g_cube = match law_find_gain(tbl, "cube", "⊗", "⊗") {
    Some(g) => g
    None => {
      ok = false
      0.0
    }
  }
  let g_cc = match comp_find(xs, "cube", "cube", "⊗", "⊗") {
    Some(x) => x.xgain
    None => {
      ok = false
      0.0
    }
  }
  if !(g_cc > g_cube * 1.3) {
    ok = false
  }

  // ── 命題 201-7（推導為純函式，且不可能做任何計費運算）────
  // 後半句由型別保證，不必量測：本庫所有計費算術（cq_mul、qdet_gauss…）
  // 都要求一個 Cost 引數，而 compose_derive 既不收 Cost 也不建 Cost。
  // 前半句要驗 —— 推導若不可重現，整張複合表就不可稽核。
  let ds2 = compose_derive(tbl)
  if ds2.length() != ds.length() {
    ok = false
  }
  for i in 0..<ds.length() {
    let (a1, b1, c1, d1, e1) = ds[i]
    let (a2, b2, c2, d2, e2) = ds2[i]
    if a1 != a2 || b1 != b2 || c1 != c2 || d1 != d2 || e1 != e2 {
      ok = false
    }
  }

  // ── 命題 201-8（共用快取）────────────────────────────────
  if comp_miss_count() != 1 {
    ok = false
  }
  let top = compose_top(xs, 3)
  let mut tops = ""
  for t in top {
    tops = tops +
      t.xphi() +
      "/" +
      t.xcomb +
      "/" +
      t.xrule +
      " ×" +
      fmt_d(t.xgain, 1) +
      "　"
  }
  mk_check(
    "N-42 律之複合代數",
    ok,
    xs.length() + ds.length() + suspects.length() * 2 + 3 + tbl.length() + 10,
    "複合定理：內層律之規則 ⊙₁ 若同時是組合子，則 Φ₂∘Φ₁ 自動有律、規則為 ⊙₂。判準是純語法的，推導階段零次矩陣運算（由型別保證：計費算術一律要求 Cost 引數，而 compose_derive 不收也不建 Cost）。修復後定律表 " +
    nhold.to_string() +
    " 條成立之律推出 " +
    ds.length().to_string() +
    " 條複合律、涵蓋 " +
    ncomp.to_string() +
    " 個相異的新演算法（無一在原八元 Φ 集內），推導集指紋 " +
    dig +
    "。逐條實測：導出且成立 " +
    dh.to_string() +
    "、導出但推翻 " +
    dn.to_string() +
    " —— 後者為 0 即健全性之證據。全量普查（360 條，cmd/lawsearch 一次性）另測得「未導出但成立」4 條、「未導出且推翻」296 條，故本定理充分而不必要。增益最高三條：" +
    tops +
    "複合放大增益（cube/⊗/⊗ 單律 ×" +
    fmt_d(g_cube, 1) +
    "，複合 cube∘cube ×" +
    fmt_d(g_cc, 1) +
    "），因為直接路徑要在 nm 階上跑兩次演算法。⚠️ 本條同時揭露一個既有盲區：qadj = det·inv 與 qinv_gauss 在奇異輸入上回傳 ⊥，兩側同時 ⊥ 會被裁決器判成相符，故 N-36 加入的降秩樣本對 inv 類與 adj 類候選毫無鑑別力 —— 推導集 60 條中有 " +
    nvac.to_string() +
    " 條帶此缺口，連基礎定律表的 15 條成立之律也有 " +
    base_vac.to_string() +
    " 條（inv/⊗/⊗、inv/⊕/⊕、adj/⊗/⊗ₛ）。以恆有定義的餘因子 adj 在**同一組矩陣**上重新裁決四條「未導出但成立」者，恰有兩條翻為推翻（rank∘adj/⊗/·、rank∘adj/⊕/+）—— 它們本來就是 ⊥ 造成的假象。",
  )
}

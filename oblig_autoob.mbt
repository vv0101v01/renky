///|
/// N-45 之義務：義務自動生成器。
///
/// 本條要驗的不是「生成器會不會跑」，而是三件更容易出錯的事：
///   (1) 生成物**真的能編譯、能跑、能通過** —— 不是一段漂亮的字串
///   (2) 生成器在產碼前**自己先量測** —— 門檻與對照規則都是測出來的
///   (3) **分工守得住** —— thm 與 proof 兩欄確實仍是佔位符
///
/// 第三點以計數實現：本義務去數佔位符出現幾次（目錄列中恰 2 次、
/// 義務函式中 0 次），分工一旦被改動，稽核當場失敗。
pub fn ob_n45() -> Check {
  let mut ok = true
  let spec = obl_demo_spec()

  // ── 命題 203-1（生成為純函式，且指紋釘死）──────────────
  // 生成器若不可重現，`moon run cmd/genoblig | diff - oblig_auto.mbt`
  // 這條稽核指令就沒有意義。
  let src = match gen_oblig_src(spec) {
    Some(s) => s
    None => {
      ok = false
      ""
    }
  }
  let src2 = match gen_oblig_src(spec) {
    Some(s) => s
    None => ""
  }
  if src != src2 {
    ok = false
  }
  let fp = str_hash64(src).to_string()
  if fp != "950416155811985155" {
    ok = false
  }

  // ── 命題 203-2（分工：thm 與 proof 只有佔位符）──────────
  let row = match gen_cat_row(spec) {
    Some(r) => r
    None => {
      ok = false
      ""
    }
  }
  let ph = obl_placeholder()
  // 目錄列裡佔位符恰出現兩次（thm 與 proof 各一），不多不少
  if str_count(row, ph) != 2 {
    ok = false
  }
  if !str_has(row, "thm: \"" + ph + "\"") {
    ok = false
  }
  if !str_has(row, "proof: \"" + ph + "\"") {
    ok = false
  }
  // 義務函式本體裡**不該**出現佔位符 —— 它是目錄列的事
  if str_has(src, ph) {
    ok = false
  }
  // 生成物必須自報身分，否則日後沒人知道這段是機器寫的
  if !str_has(src, "逐字自動產出") || !str_has(src, "由人補寫") {
    ok = false
  }

  // ── 命題 203-3（生成器自己先量測：對照規則是試出來的）────
  // 對照組若其實也成立，生成的義務就沒有鑑別力 —— 它會永遠通過。
  let cr = match pick_control_rule(spec) {
    Some(r) => r
    None => {
      ok = false
      ""
    }
  }
  if cr == spec.orule {
    ok = false
  }
  // 重新驗一次：真規則成立、對照規則被推翻
  match
    comp_check(
      spec.oouter,
      spec.oinner,
      spec.ocomb,
      spec.orule,
      law_samples_mixed(),
      comp_rng_of(spec.oouter, spec.oinner, spec.ocomb, spec.orule),
    ) {
    Some((v, vac)) => {
      if !v.holds {
        ok = false
      }
      // 選 det∘sq 的理由：det 與 sq 都是全函式，故無 ⊥ 證據缺口（N-42）
      if vac != 0 {
        ok = false
      }
    }
    None => ok = false
  }
  match
    comp_check(
      spec.oouter,
      spec.oinner,
      spec.ocomb,
      cr,
      law_samples_mixed(),
      comp_rng_of(spec.oouter, spec.oinner, spec.ocomb, cr),
    ) {
    Some((v, _vac)) => if v.holds { ok = false }
    None => ok = false
  }
  // 生成的原始碼裡必須真的帶著那條對照規則與一個門檻判斷
  if !str_has(src, "對照組") || !str_has(src, "if !(gain > ") {
    ok = false
  }

  // ── 命題 203-4（生成物是可執行的交付物，不是草稿）────────
  // 這一步沒有捷徑：直接把生成出來的義務跑一遍。
  // 它能被呼叫，本身就證明了它通過了編譯器。
  let auto = ob_n46()
  if !auto.ok || auto.trials != law_samples_mixed().length() * 2 {
    ok = false
  }

  // ── 命題 203-5（生成器會拒絕不該生成的東西）──────────────
  // 把規則換成一條被推翻的（det∘sq 配 ·），生成器必須回傳 None，
  // 而不是照樣吐出一段會失敗的義務。
  let bad : OblSpec = { ..spec, orule: "·", ocode: "N-XX", ofn: "ob_nxx", }
  if !(gen_oblig_src(bad) is None) {
    ok = false
  }
  if !(gen_cat_row(bad) is None) {
    ok = false
  }

  // ── 命題 203-6（生成的是骨架，不是一行轉呼叫）────────────
  // 若生成器只吐出 `comp_check(...)` 一行，自動化就沒有意義 ——
  // 真正的人工成本在於把量測攤開成可讀、可改、可覆核的程式碼。
  let nl = str_lines(src)
  if nl < 50 {
    ok = false
  }
  // 骨架必須自己做取樣、自己建成本計量器、自己比對、自己算增益
  for
    frag in [
      "law_samples_mixed()", "Cost::new()", "u.equals(v)", "base.to_double()", "mk_check(",
    ] {
    if !str_has(src, frag) {
      ok = false
    }
  }
  // ── 定理 203-7（ℝ 軌生成：分工相同，前置條件更嚴）──
  // ℝ 軌版生成器多做三件 ℚ 軌不需要的事：用容差而非逐位相等、用 flop
  // 而非字乘法、而且必須先確認外層 Φ 的前提沒有被違反、中間量沒有溢位。
  let rspec = obl_demo_spec_r()
  let rsrc = match gen_oblig_src_r(rspec) {
    Some(t) => t
    None => {
      ok = false
      ""
    }
  }
  let rrow = match gen_cat_row_r(rspec) {
    Some(t) => t
    None => {
      ok = false
      ""
    }
  }
  let rfp = str_hash64(rsrc).to_string()
  if rfp != "14763646889716929481" {
    ok = false
  }
  // 分工在 ℝ 軌一樣查：佔位符只在目錄列、恰兩次
  if str_count(rrow, ph) != 2 || str_has(rsrc, ph) {
    ok = false
  }
  // 生成物必須自報軌道，否則 flop 增益會被誤讀成字乘法增益
  if !str_has(rsrc, "ℝ 軌") || !str_has(rsrc, "不可") {
    ok = false
  }
  // 必須真的用容差而非 equals
  if !str_has(rsrc, "rdev(") || str_has(rsrc, ".equals(") {
    ok = false
  }
  // 生成物可執行且通過
  let rauto = ob_n49()
  if !rauto.ok || rauto.trials != rlaw_grid_std().length() * 2 {
    ok = false
  }
  // 拒絕：把內層換成 chol（前提會被違反），生成器必須回傳 None
  let rbad : OblSpec = {
    ..rspec,
    oinner: "chol",
    oouter: "eig",
    ocode: "N-XX",
    ofn: "ob_nxx",
  }
  if !(gen_oblig_src_r(rbad) is None) {
    ok = false
  }
  mk_check(
    "N-45 義務自動生成",
    ok,
    nl + str_lines(row) + str_lines(rsrc) + str_lines(rrow) + 24,
    "生成器由一條定律表列產出兩樣東西：一段可直接編譯的 ob_* 義務函式（" +
    nl.to_string() +
    " 行），與一列 catalogue.mbt 目錄列（" +
    str_lines(row).to_string() +
    " 行）。本輪實際生成的是 N-46（det∘sq / ⊗ / ^，來自 N-42 的複合定律表），產出物已入庫為 oblig_auto.mbt，可以 moon run cmd/genoblig | diff - oblig_auto.mbt 重現，指紋 " +
    fp +
    "。生成器在產碼**之前**先跑一次引擎：量出真實增益後取一半寫成門檻、並逐一試出一條確實會被推翻的對照規則（本例為以 " +
    cr +
    " 取代 " +
    spec.orule +
    "），故生成出來的義務帶著一個保證失敗的對照組，證明它有鑑別力。分工以計數固定：生成器產出骨架與可執行的量測，thm 與 proof 兩欄寫佔位符待補 —— 本義務會去數佔位符還在不在（目錄列中恰 2 次、義務函式中 0 次）。另驗生成器會拒絕不該生成的東西：把規則換成被推翻的 ·，gen_oblig_src 與 gen_cat_row 都回傳 None，而不是照樣吐出一段注定失敗的義務。ℝ 軌版（N-48 後擴充）生成 N-49（chol∘inv / ⊗ / ⊗，ℝ 軌複合表中有效裁決之增益冠軍），指紋 14763646889716929481，" +
    str_lines(rsrc).to_string() +
    " 行；它多做三件 ℚ 軌不需要的事 —— 用相對容差而非逐位相等、用 flop 而非字乘法（生成物自報軌道並標明不可並列）、並先確認外層 Φ 的前提未被違反且中間量未溢位。分工計數在 ℝ 軌一樣查（佔位符目錄列恰 2 次、義務函式 0 次），拒絕機制一樣有效（把內層換成 chol、外層換成 eig 後前提必被違反，生成器回傳 None）。",
  )
}

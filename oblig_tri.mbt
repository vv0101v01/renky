///|
/// N-59 之義務：空間註冊表擴充（35 → 45），前綴保持。
pub fn ob_n59() -> Check {
  let mut ok = true
  let (n, lo, hi, tot, dg) = sregx_stats()
  if n != 45 || lo != 2 || hi != 12 || tot != 211 {
    ok = false
  }
  if dg != "45:211:725278234" {
    ok = false
  }
  // 前綴保持：前 35 筆與 N-50 之表逐筆相同（名稱與 Gram）
  if !sregx_prefix_ok() {
    ok = false
  }
  // 新增 10 筆之名稱、族別、維數
  let neu = space_registry_new()
  if neu.length() != 10 {
    ok = false
  }
  let names = [
    "Sym₄", "Skew₅", "𝔰𝔩₃", "Herm₃", "P≤4 L²", "P≤4 Hilb", "ℚ[x,y,z]≤1",
    "ℍ³", "Λ²ℚ⁵", "ℝ(ℂ³)",
  ]
  let dims = [10, 10, 8, 9, 4, 4, 4, 12, 10, 6]
  for i in 0..<10 {
    if neu[i].sname != names[i] {
      ok = false
    }
    if neu[i].sdim != dims[i] {
      ok = false
    }
    // 每個新空間之 Gram 必須對稱正定（否則不是內積空間）
    if !is_positive_definite(neu[i].sg) {
      ok = false
    }
    if !neu[i].sg.equals(neu[i].sg.transpose()) {
      ok = false
    }
  }
  // 族別分散：新增的 10 筆落在 5 個族
  let fams : Array[String] = []
  for r in neu {
    let mut found = false
    for f in fams {
      if f == r.fam {
        found = true
      }
    }
    if !found {
      fams.push(r.fam)
    }
  }
  if fams.length() != 5 {
    ok = false
  }
  // 舊表之指紋必須原封不動（迴歸錨）
  if space_registry_digest() != "35:134:252394910" {
    ok = false
  }
  mk_check(
    "N-59 空間註冊表擴充 35 → 45",
    ok,
    n + neu.length() * 4 + 4,
    "N-50 的 35 個空間在 N-51／N-52 的義務裡留下三個釘死的指紋。直接把註冊表改成 45 筆會讓三條義務同時失效，而且失效的方式沒有資訊量 —— 只是數字變了。故本輪的擴充採**前綴保持**：space_registry_x() 的前 35 筆與 space_registry() 逐筆相同（名稱與 Gram 都比），後 10 筆是新的。舊指紋 35:134:252394910 因此繼續當迴歸錨點，而且多出一條可執行的檢查：擴充表限制回原表時必須逐筆重現。新增的 10 個空間刻意分散在 5 個族：矩陣 4（Sym₄ 維 10、Skew₅ 維 10、𝔰𝔩₃ 維 8、Herm₃ 維 9）、多項式 3（P≤4 L²、P≤4 Hilb、ℚ[x,y,z]≤1 各維 4）、四元數 1（ℍ³ 維 12）、外代數 1（Λ²ℚ⁵ 維 10）、複結構 1（ℝ(ℂ³) 維 6）。擴充後 " +
    n.to_string() +
    " 個空間，維數 " +
    lo.to_string() +
    " – " +
    hi.to_string() +
    "，總維 " +
    tot.to_string() +
    "，指紋 " +
    dg +
    "。每一個新空間都逐條驗 Gram 對稱且正定 —— 不是「建構子沒報錯」，是「它真的是一個內積空間」。選這 10 個不是為了湊數：Herm₃ 與 ℝ(ℂ³) 把複結構推到 3 維（原表只到 2 維），ℍ³ 是全表最高維（12），Skew₅ 與 Λ²ℚ⁵ 同為維 10 但 Gram 完全不同（一個來自 Frobenius 內積、一個來自子式配對），正好給構造子表一組容易混淆的對照。",
  )
}

///|
/// N-60 之義務：構造子表擴充（7 → 14），前綴保持。
pub fn ob_n60() -> Check {
  let mut ok = true
  if !comb14_prefix_ok() {
    ok = false
  }
  let cbs = comb14_registry()
  if cbs.length() != 14 {
    ok = false
  }
  let syms = [
    "⊗", "⊕", "*", "Λ²", "T", "U", "⊞", "H", "Λⁿ⁻¹", "S²", "**", "D",
    "U½", "Tᵀ",
  ]
  for i in 0..<14 {
    if cbs[i].csym != syms[i] {
      ok = false
    }
  }
  let (cells, lo, hi, tot, spd, dimok, dg) = comb14_stats()
  if cells != 630 || lo != 1 || hi != 78 || tot != 4510 {
    ok = false
  }
  // 每一格都必須是對稱正定（構造子保持內積結構）
  if spd != 630 {
    ok = false
  }
  // 每一格的維數都必須與宣告的維數公式相符
  if dimok != 630 {
    ok = false
  }
  if dg != "630:4510:665890815" {
    ok = false
  }
  // 雙對偶必須真的是恆等（Gram 逐元回到原樣）—— A1 的函子版
  let mut ddok = 0
  for r in space_registry_x() {
    let e = (cbs[10].capply)(r.leaf())
    if e.sgram().equals(r.sg) {
      ddok = ddok + 1
    }
  }
  if ddok != 45 {
    ok = false
  }
  // 舊表之 245 格指紋必須原封不動
  if comb7_digest() != "245:1306:695201586" {
    ok = false
  }
  mk_check(
    "N-60 構造子表擴充 7 → 14",
    ok,
    cells + 14 + 45,
    "同樣採前綴保持：comb14_registry() 的前 7 個與 comb7_registry() 逐個相同（符號相同，且 1…8 維上的維數公式逐點相同），舊的 245 格指紋 245:1306:695201586 繼續有效。新增 7 個仍然全是**建構子**（由空間造空間，且在 Gram 上是函子）：H = Hom(W₂,−) ≅ W₂*⊗−（維 2n）、Λⁿ⁻¹ 餘維一外冪（維 n，與 Λ² 不同，它在每個維度都有定義）、S² 對稱平方（維 n(n+1)/2，以選擇矩陣嵌進 V⊗V，再取 SᵀGS）、** 雙對偶（維 n）、D 倍化 V⊕V（維 2n）、U½ 半子空間（取前 ⌈n/2⌉ 個座標）、Tᵀ 轉置扭曲（與 T 用互為轉置的兩個單位三角陣）。14 × 45 = " +
    cells.to_string() +
    " 格，維數 " +
    lo.to_string() +
    " – " +
    hi.to_string() +
    "（最小的 1 來自 Λⁿ⁻¹ 與 U½ 作用於低維空間，最大的 78 來自 S² 作用於 ℍ³），總維 " +
    tot.to_string() +
    "，指紋 " +
    dg +
    "。兩條逐格檢查：全部 " +
    spd.to_string() +
    "/630 格的 Gram 對稱正定（構造子保持內積結構，這是「它們是建構子」的實質內容），全部 " +
    dimok.to_string() +
    "/630 格的實際維數與宣告的維數公式相符（公式不是註解，是被檢查的斷言）。另有一條專屬檢查：雙對偶 ** 必須在全部 45 個空間上使 Gram **逐元回到原樣**（" +
    ddok.to_string() +
    "/45）—— 這是 N-53 重寫規則 A1 的函子版，若有限維對偶的實作在某處漏了一次轉置，這條會當場抓到，而維數檢查不會。",
  )
}

///|
/// N-61 之義務：任意三表笛卡兒積普查引擎。
pub fn ob_n61() -> Check {
  let mut ok = true
  let ts = tri_tables()
  if ts.length() != 7 {
    ok = false
  }
  let sizes = [6, 45, 35, 14, 7, 23, 9]
  for i in 0..<7 {
    if ts[i].ttitems.length() != sizes[i] {
      ok = false
    }
  }
  let s0 = match tri_by_name("空間₀") {
    Some(t) => t
    None => ts[0]
  }
  let c0 = match tri_by_name("構造子₀") {
    Some(t) => t
    None => ts[0]
  }
  let sx = match tri_by_name("空間") {
    Some(t) => t
    None => ts[0]
  }
  let cx = match tri_by_name("構造子") {
    Some(t) => t
    None => ts[0]
  }
  let dg = match tri_by_name("D群") {
    Some(t) => t
    None => ts[0]
  }
  let bk = match tri_by_name("空間⊥") {
    Some(t) => t
    None => ts[0]
  }
  let lt = match tri_by_name("字母群") {
    Some(t) => t
    None => ts[0]
  }

  // ── 推廣必須重現特例（逐格、連雜湊順序）────────────────
  let repro = tri_product_memo(s0, c0, dg, 13, 12) // 【N-77】備忘
  if repro.tdigest != "419:419:674552611" {
    ok = false
  }
  if repro.tcov.0 != 35 || repro.tcov.1 != 7 || repro.tcov.2 != 23 {
    ok = false
  }
  let old = dcensus_stratum(13, 12)
  if repro.tdigest != old.digest {
    ok = false
  }
  if repro.tcells != old.cells || repro.tpass != old.pass {
    ok = false
  }

  // ── 擴充軸：45 × 14 × 23 之分層 ─────────────────────────
  let ext = tri_product_memo(sx, cx, dg, 17, 12) // 【N-77】備忘
  if ext.tdigest != "774:774:352759555" {
    ok = false
  }
  if ext.tcov.0 != 45 || ext.tcov.1 != 14 || ext.tcov.2 != 23 {
    ok = false
  }
  if ext.tmisses.length() != 0 || ext.tdmax != 12 {
    ok = false
  }

  // ── 擾動表上之普查：格值必須真的會分裂 ──────────────────
  let pert = tri_product_memo(bk, c0, dg, 1, 12) // 【N-77】備忘
  if pert.tdigest != "966:867:761159647" {
    ok = false
  }
  if pert.tcells != 966 || pert.tpass != 867 {
    ok = false
  }
  if pert.tpass >= pert.tcells {
    ok = false
  }

  // ── 逐軸敏感度：三軸皆非退化 ────────────────────────────
  let sa = tri_axis_sensitivity(bk, c0, dg, 12, 6)
  if sa.0.0 != 23 || sa.0.1 != 36 {
    ok = false
  }
  if sa.1.0 != 2 || sa.1.1 != 36 {
    ok = false
  }
  if sa.2.0 != 14 || sa.2.1 != 36 {
    ok = false
  }
  if !(sa.0.0 > 0 && sa.1.0 > 0 && sa.2.0 > 0) {
    ok = false
  }

  // ── 反向對照：字母群軸必須被判為完全退化 ────────────────
  let sb = tri_axis_sensitivity(bk, c0, lt, 12, 6)
  if sb.0.0 != 0 || sb.1.0 != 0 || sb.2.0 != 0 {
    ok = false
  }
  if sb.2.1 != 36 {
    ok = false
  }
  mk_check(
    "N-61 任意三表笛卡兒積普查引擎",
    ok,
    repro.tcells + ext.tcells + pert.tcells + 36 * 6,
    "N-52 的普查是寫死的：D 群 × 空間 × 構造子，三個迴圈巢在 dcensus_core 裡，換一組軸就要重寫引擎。本條把軸抽出來 —— 普查的輸入變成**任意三張表**，表項可以是空間、構造子、判準式，也可以是目錄裡的一條義務。格的求值是一個全函數：由 E³ 出發，三元組裡的空間項換掉基底、構造子項依序套用，得到一個 SpaceExpr；三元組裡最後一個判者決定格值，沒有判者就用預設判者 D-15。現有 " +
    ts.length().to_string() +
    " 張表：空間⊥ 6、空間 45、空間₀ 35、構造子 14、構造子₀ 7、D群 23、字母群 9。**推廣的正當性在於它必須能精確退回特例。** 以 (空間₀, 構造子₀, D群)、step 13、維數上限 12 相乘，必須逐格重現 N-52 的 " +
    repro.tdigest +
    " —— 不只格數與通過數，連 FNV 乘累積的雜湊順序都要一樣（義務同時拿 dcensus_stratum(13,12) 來對）。做不到這件事的推廣只是另一個東西。擴充軸上 (空間, 構造子, D群)、step 17：" +
    ext.tdigest +
    "，覆蓋 45/14/23，最高維 12，0 格推翻。**退化軸必須被量出來，不能被藏起來。** 若固定另兩軸、沿某軸掃過去格值全部相同，該軸對這組表就是退化的；一個 14,490 格的普查如果三軸全退化，實際上只是把同一個答案抄了 14,490 遍。這裡有個陷阱：在一個**正確**的函式庫上格值恆為真，逐軸敏感度必定量到 0/0 —— 不是軸退化，是沒有訊號。故本條備了擾動空間表（N-52 的三個壞 Gram ＋ 三個正常空間），格值才會分裂：" +
    pert.tcells.to_string() +
    " 格中 " +
    pert.tpass.to_string() +
    " 格成立、" +
    (pert.tcells - pert.tpass).to_string() +
    " 格被推翻。在這張表上逐軸量敏感度：空間軸 " +
    sa.0.0.to_string() +
    "/36 個切片有變動、構造子軸 " +
    sa.1.0.to_string() +
    "/36、演算法軸 " +
    sa.2.0.to_string() +
    "/36 —— 三軸皆非退化，且空間軸最強（擾動本來就放在那裡）。**反向對照。** 把第三軸換成字母群（目錄 A–N 各一條代表義務，它們根本不看空間），敏感度必須量到 " +
    sb.0.0.to_string() +
    "/" +
    sb.1.0.to_string() +
    "/" +
    sb.2.0.to_string() +
    " —— 三軸全退化。引擎要是量不出這個差別，它報的「非退化」就沒有意義。",
  )
}

///|
/// N-62 之義務：義務生成器 DSL 擴出第二種產出（普查式義務）。
pub fn ob_n62() -> Check {
  let mut ok = true

  // ── 防線一：決定性 ──────────────────────────────────────
  let s1 = gen_census_src(cen_demo_spec())
  let s2 = gen_census_src(cen_demo_spec())
  let src = match (s1, s2) {
    (Some(a), Some(b)) => {
      if a != b {
        ok = false
      }
      a
    }
    _ => {
      ok = false
      ""
    }
  }
  if src.length() < 400 {
    ok = false
  }

  // ── 防線二：量測忠實 ────────────────────────────────────
  // 產出字串裡的指紋，必須等於義務當場重跑一次所得的指紋。
  let ta = match tri_by_name("空間") {
    Some(t) => t
    None =>
      return mk_check(
        "N-62 義務生成器之普查式產出", false, 0, "表不存在",
      )
  }
  let tb = match tri_by_name("構造子") {
    Some(t) => t
    None =>
      return mk_check(
        "N-62 義務生成器之普查式產出", false, 0, "表不存在",
      )
  }
  let tc = match tri_by_name("D群") {
    Some(t) => t
    None =>
      return mk_check(
        "N-62 義務生成器之普查式產出", false, 0, "表不存在",
      )
  }
  let fresh = tri_product(ta, tb, tc, 17, 12) // 【N-77】刻意繞過備忘錄
  if !src.contains(fresh.tdigest) {
    ok = false
  }
  if !src.contains("r.tcells != " + fresh.tcells.to_string()) {
    ok = false
  }
  if !src.contains("r.tpass != " + fresh.tpass.to_string()) {
    ok = false
  }

  // ── 防線三：敗例忠實（雙向對照）────────────────────────
  // 餵一個必定有格被推翻的普查，產出必須如實寫出推翻格數。
  let csrc = match gen_census_src(cen_control_spec()) {
    Some(x) => x
    None => {
      ok = false
      ""
    }
  }
  let cta = match tri_by_name("空間⊥") {
    Some(t) => t
    None => ta
  }
  let ctb = match tri_by_name("構造子₀") {
    Some(t) => t
    None => tb
  }
  let cfresh = tri_product(cta, ctb, tc, 1, 12) // 【N-77】刻意繞過備忘錄
  let nmiss = cfresh.tcells - cfresh.tpass
  if nmiss <= 0 {
    ok = false
  }
  if !csrc.contains("r.tmisses.length() != " + nmiss.to_string()) {
    ok = false
  }
  // 對照組**不得**出現「全過」那一行；示範組必須出現
  if csrc.contains("r.tmisses.length() != 0 ") {
    ok = false
  }
  if !src.contains("r.tmisses.length() != 0") {
    ok = false
  }

  // ── 佔位符分工：義務 0 次、目錄列 2 次 ──────────────────
  let ph = obl_placeholder()
  if src.contains(ph) {
    ok = false
  }
  let row = match gen_census_row(cen_demo_spec()) {
    Some(x) => x
    None => {
      ok = false
      ""
    }
  }
  let nph = str_count(row, ph)
  if nph != 2 {
    ok = false
  }

  // ── 產出物確實編譯並通過 ────────────────────────────────
  // ob_n62g 就是上面那段字串的編譯結果（經 cmd/genoblig 寫入 oblig_auto.mbt）。
  let gen = ob_n62g()
  if !gen.ok {
    ok = false
  }
  if gen.trials != fresh.tcells {
    ok = false
  }
  mk_check(
    "N-62 義務生成器之普查式產出",
    ok,
    fresh.tcells + cfresh.tcells + 12,
    "N-45 的生成器只會寫一種義務：吃一條結構律 (Φ₂, Φ₁, C, ⊙)，吐「取樣 → 雙向對照 → 增益斷言」。第六、七輪長出來的新東西 —— 普查、逐軸敏感度、退化軸 —— 它一個也不會寫。本條把 DSL 擴出第二種產出：規格變成三張表加兩個旋鈕（分層步長、維數上限），生成器**先跑一次普查與一次逐軸敏感度量測**，再把量到的指紋、格數、通過數、三軸覆蓋、最高維、敏感度逐一釘進產出的程式碼。示範規格「空間 × 構造子 × D群，step 17，維數上限 12」產出 " +
    src.length().to_string() +
    " 字元的 MoonBit 原始碼，經 cmd/genoblig 寫入 oblig_auto.mbt 後編譯為 ob_n62g，本義務直接呼叫它並要求通過（" +
    gen.trials.to_string() +
    " 格）。**生成器最容易出的事是寫小說** —— 產出一段看起來很嚴謹、但斷言的是自己瞎編的數字的程式碼。三道防線全部可執行：(一) 決定性，同一規格生成兩次必須逐字元相同；(二) 量測忠實，產出字串裡的指紋 " +
    fresh.tdigest +
    " 必須等於本義務當場重跑一次所得的指紋，格數與通過數同理；(三) 敗例忠實，另餵一個必定有格被推翻的規格（擾動表 × 構造子₀ × D群，step 1），產出必須如實寫 `r.tmisses.length() != " +
    nmiss.to_string() +
    "`，而且**不得**出現示範組那一行「全過」的斷言。第三道是雙向對照：沒有它，一個「永遠產生 tmisses.length() != 0」的生成器可以通過前兩道。佔位符分工沿用 N-45：義務函式中 0 次、目錄列中恰 2 次（thm 與 proof 由人補寫），本義務逐一數過。",
  )
}

///|
/// 中端報表：重寫規則、範式、派工、ℝ 軌誤差。
fn main {
  println("# 中端報表 —— 規範化、派工與浮點效應")
  println("")
  println(
    "本檔由 `moon run cmd/midend` 產生。對應目錄條目 N-53／N-54／N-55。",
  )
  println("")
  println(
    "中端把 35 個載體各異的前端空間（N-50）與 7 個構造子（N-51）統一成",
  )
  println(
    "一棵 `SpaceExpr` 語法樹，在樹上做保語義的重寫（N-53），",
  )
  println("再按樹的形狀派工到特化求解器（N-54）；")
  println(
    "最後量一件 ℚ 軌問不出來的事：規範化在浮點下更準還是更不準（N-55）。",
  )
  println("")

  // ── 一 ──────────────────────────────────────────────────
  println("## 一、重寫規則表")
  println("")
  println("類 A 規則要求重寫前後 Gram **逐元相同**；終止測度")
  println(
    "μ = (對偶負重, 節點數, 左重) 取字典序，每條規則都要讓它嚴格下降。",
  )
  println("")
  println("| # | 規則 | 語料觸發 | Gram 不變 | 測度下降 |")
  println("|---|------|----------|-----------|----------|")
  let mut i = 0
  for r in @hilbert.rw_rule_check(@hilbert.ob_rng()) {
    i = i + 1
    println(
      "| " +
      i.to_string() +
      " | " +
      r.0 +
      " | " +
      yn(r.1) +
      " | " +
      yn(r.2) +
      " | " +
      yn(r.3) +
      " |",
    )
  }
  println("")
  let (n, sa, sb, cf, idm, nf, dec, c1, c2) = @hilbert.rw_scan(
    @hilbert.ob_rng(),
  )
  println(
    "語料 " +
    n.to_string() +
    " 式：類 A 健全 " +
    sa.to_string() +
    "、類 B 健全 " +
    sb.to_string() +
    "、合流 " +
    cf.to_string() +
    "、冪等 " +
    idm.to_string() +
    "、已是範式 " +
    nf.to_string() +
    "、測度不上升 " +
    dec.to_string() +
    "。",
  )
  println(
    "物化 Gram 之字乘法總計：直接 " +
    c1.to_string() +
    " → 範式 " +
    c2.to_string() +
    "（×" +
    @hilbert.fmt_d(c1.to_double() / c2.to_double(), 2) +
    "）。指紋 " +
    @hilbert.rw_digest(@hilbert.ob_rng()) +
    "。",
  )
  println("")

  // ── 二 ──────────────────────────────────────────────────
  println("## 二、語料範式表")
  println("")
  println(
    "前 16 式為刻意對準各條規則觸發形狀的手造式，其餘為 `rand_expr` 隨機生成。",
  )
  println("")
  println("| 原式 | 範式 | 維數 | 直接字乘 | 範式字乘 | 比值 |")
  println("|------|------|------|----------|----------|------|")
  for e in @hilbert.rw_corpus(@hilbert.ob_rng()) {
    let (d, nn, _) = @hilbert.rw_cost_pair(e)
    let rs = if nn == 0L {
      "（已免費）"
    } else {
      "×" + @hilbert.fmt_d(d.to_double() / nn.to_double(), 2)
    }
    println(
      "| `" +
      e.slabel() +
      "` | `" +
      @hilbert.normalize(e).slabel() +
      "` | " +
      e.sdim().to_string() +
      " | " +
      d.to_string() +
      " | " +
      nn.to_string() +
      " | " +
      rs +
      " |",
    )
  }
  println("")

  // ── 三 ──────────────────────────────────────────────────
  println("## 三、派工表（ℚ 軌成本）")
  println("")
  println(
    "通用路徑物化 nm×nm 的 Gram 再做 Gauss 消去；特化路徑照 IR 拆解，",
  )
  println(
    "只在葉子上才真正消去。外冪與 Kron 和無特化路徑，兩路成本必須完全相等。",
  )
  println("")
  let rep = @hilbert.spec_report(@hilbert.ob_rng())
  println("| 形狀 | 試驗數 | 通用字乘 | 特化字乘 | 比值 |")
  println("|------|--------|----------|----------|------|")
  for s in rep.shapes {
    let ratio = if s.3 == 0L { 1.0 } else { s.2.to_double() / s.3.to_double() }
    println(
      "| " +
      s.0 +
      " | " +
      s.1.to_string() +
      " | " +
      s.2.to_string() +
      " | " +
      s.3.to_string() +
      " | ×" +
      @hilbert.fmt_d(ratio, 2) +
      " |",
    )
  }
  println(
    "| **合計** | **" +
    rep.trials.to_string() +
    "** | **" +
    rep.dense.to_string() +
    "** | **" +
    rep.spec.to_string() +
    "** | **×" +
    @hilbert.fmt_d(rep.dense.to_double() / rep.spec.to_double(), 2) +
    "** |",
  )
  println("")
  println(
    "兩路輸出逐元相同 " +
    rep.same.to_string() +
    "/" +
    rep.trials.to_string() +
    "；特化較快 " +
    rep.win.to_string() +
    " 次、較慢 " +
    rep.lose.to_string() +
    " 次。",
  )
  println("")
  println(
    "派工判準之混淆表（走且贏／走但輸／不走但會贏／不走且不贏）：",
  )
  println("")
  println(
    "| 判準 | 走且贏 | 走但輸 | 不走但會贏 | 不走且不贏 |",
  )
  println("|------|--------|--------|------------|------------|")
  println(
    "| 結構判準 | " +
    rep.cs.0.to_string() +
    " | " +
    rep.cs.1.to_string() +
    " | " +
    rep.cs.2.to_string() +
    " | " +
    rep.cs.3.to_string() +
    " |",
  )
  println(
    "| 精煉判準 | " +
    rep.cr.0.to_string() +
    " | " +
    rep.cr.1.to_string() +
    " | " +
    rep.cr.2.to_string() +
    " | " +
    rep.cr.3.to_string() +
    " |",
  )
  println("")
  println(
    "唯一的敗例是 `T[葉子]` 於右端個數 k ≥ 2：特化要解三次 Θ(n³)，",
  )
  println(
    "通用只付一次求逆而求逆成本與 k 無關。精煉判準把這一格收掉。",
  )
  println("")

  // ── 四 ──────────────────────────────────────────────────
  println("## 四、ℝ 軌誤差表")
  println("")
  println(
    "真值取 ℚ 軌精確 Gram 轉成的浮點值；誤差為相對最大模偏差。",
  )
  println(
    "這張表問的是一個只有雙軌庫問得出來的問題：規範化在浮點下更準還是更不準。",
  )
  println("")
  println(
    "| 原式 | 維數 | 原式誤差 | 範式誤差 | 原式 flop | 範式 flop | 條件數 |",
  )
  println(
    "|------|------|----------|----------|-----------|-----------|--------|",
  )
  for e in @hilbert.spec_corpus(@hilbert.ob_rng()) {
    let (x, y, p, q, k) = @hilbert.rmid_cell(e)
    println(
      "| `" +
      e.slabel() +
      "` | " +
      e.sdim().to_string() +
      " | " +
      @hilbert.fmt_e(x) +
      " | " +
      @hilbert.fmt_e(y) +
      " | " +
      p.to_string() +
      " | " +
      q.to_string() +
      " | " +
      @hilbert.fmt_e(k) +
      " |",
    )
  }
  println("")
  let (m, bt, ws, ti, ea, eb, fa, fb, km) = @hilbert.rmid_scan(
    @hilbert.ob_rng(),
  )
  println(
    "語料 " +
    m.to_string() +
    " 式：規範化後較準 " +
    bt.to_string() +
    " 式、較不準 " +
    ws.to_string() +
    " 式、完全相同 " +
    ti.to_string() +
    " 式。",
  )
  println(
    "最差相對誤差 " +
    @hilbert.fmt_e(ea) +
    " → " +
    @hilbert.fmt_e(eb) +
    "；flop " +
    fa.to_string() +
    " → " +
    fb.to_string() +
    "；最大條件數 " +
    @hilbert.fmt_e(km) +
    "。",
  )
  println("")
  let (_, sv, sb2, db, es, ed, fs, fd) = @hilbert.rmid_solve_scan(
    @hilbert.ob_rng(),
  )
  println(
    "端到端解 G·x = b（真值取 ℚ 上精確解，" +
    sv.to_string() +
    " 式可解）：ℝ 特化較準 " +
    sb2.to_string() +
    " 式、ℝ 通用較準 " +
    db.to_string() +
    " 式；最差誤差 " +
    @hilbert.fmt_e(es) +
    " 對 " +
    @hilbert.fmt_e(ed) +
    "；flop " +
    fs.to_string() +
    " 對 " +
    fd.to_string() +
    "。",
  )
  println("")
  let (good, bad) = @hilbert.rmid_control(@hilbert.ob_rng())
  println(
    "鑑別力對照：正確範式對真值偏差 " +
    @hilbert.fmt_e(good) +
    "，故意寫錯的重寫 `(A⊗B)* → (A*)⊗B` 偏差 " +
    @hilbert.fmt_e(bad) +
    "，相差 " +
    @hilbert.fmt_e(bad / good) +
    " 倍。",
  )
  println("")
  appendix8()
  appendix9()
}

///|
fn yn(b : Bool) -> String {
  if b {
    "✔"
  } else {
    "✘"
  }
}

///|
/// 第八輪附錄：五個補起來的洞。
fn appendix8() -> Unit {
  println("")
  println("## 五、第八輪：五個補起來的洞（N-63 … N-67）")
  println("")
  println("### 5.1 ⊞ 的 k 元成本模型（N-63）")
  println("")
  println(
    "A ⊞ B = A⊗I_q + I_p⊗B **沒有乘法** —— 每個非零位置都是搬運。",
  )
  println(
    "搬運次數 f(p,q) = p²q + pq² = P·(p+q)，**看得見切法**；",
  )
  println("⊗ 的 P² 看不見。故 ⊞ 要自己的區間 DP。")
  println("")
  println(
    "| 維數 | ⊞-DP 樹 | 成本 | ⊗-DP 樹 | 在 ⊞ 模型下 | 左結合 |",
  )
  println("|------|---------|------|---------|-------------|--------|")
  for dims in [[2, 3, 4], [2, 2, 8], [2, 8, 2], [5, 2, 2, 3], [5, 2, 2, 9]] {
    let (ck, kt) = @hilbert.ks_dp(dims)
    let (_, ot) = @hilbert.assoc_dp(dims)
    let mut t = "| ["
    for x in dims {
      t = t + x.to_string() + " "
    }
    t = t + "] | " + kt.alabel() + " | " + ck.to_string()
    t = t +
      " | " +
      ot.alabel() +
      " | " +
      @hilbert.AssocTree::kscost(ot, dims).to_string()
    t = t +
      " | " +
      @hilbert.AssocTree::kscost(@hilbert.assoc_left(dims.length()), dims).to_string() +
      " |"
    println(t)
  }
  println("")
  println("窮舉搜尋（兩個 DP 的最佳樹何時不同）：")
  println("")
  println(
    "| 範圍 | 組數 | 樹不同 | 用 ⊗ 樹之最大損失 | cost⊞ ≤ cost⊗ |",
  )
  println("|------|------|--------|-------------------|----------------|")
  for cfg in [(2, 8, 4), (2, 10, 4), (2, 12, 4), (2, 20, 3), (2, 6, 5)] {
    let (tot, diff, worst, le) = @hilbert.ks_vs_kron_sweep(cfg.0, cfg.1, cfg.2)
    let mut t = "| k=" +
      cfg.2.to_string() +
      "，維 " +
      cfg.0.to_string() +
      "…" +
      cfg.1.to_string()
    t = t + " | " + tot.to_string() + " | " + diff.to_string()
    t = t +
      " | ×" +
      @hilbert.fmt_d(worst, 5) +
      " | " +
      le.to_string() +
      "/" +
      tot.to_string() +
      " |"
    println(t)
  }
  println("")
  println("### 5.2 類 B 帶置換進主流程（N-64）")
  println("")
  let rb = @hilbert.ob_rng()
  let (cn, snd, stb, mv) = @hilbert.canon_scan(rb)
  let mut b = "語料 " +
    cn.to_string() +
    " 式：逐元健全 " +
    snd.to_string()
  b = b +
    "、冪等 " +
    stb.to_string() +
    "、真的被交換過 " +
    mv.to_string() +
    " 式。"
  println(b)
  println(
    "約定 G(canon)[u][v] = G(原式)[p[u]][p[v]]；扭曲與子空間把子樹置換",
  )
  println("吸收進自己的矩陣（M′ = PᵀM），對外輸出恆等。")
  println("")
  println("### 5.3 子空間之特化路徑（N-65）")
  println("")
  let rs = @hilbert.ob_rng()
  let (sn, ssame, std, sts, swin, slose) = @hilbert.sub_scan(rs)
  let mut c = "語料 " +
    sn.to_string() +
    " 式，兩路逐元相同 " +
    ssame.to_string()
  c = c + "，通用 " + std.to_string() + " → 特化 " + sts.to_string()
  c = c +
    "（×" +
    @hilbert.fmt_d(std.to_double() / sts.to_double(), 3) +
    "），"
  c = c + swin.to_string() + " 勝 " + slose.to_string() + " 敗。"
  println(c)
  println("")
  println("### 5.4 N-40 接中端（N-66）")
  println("")
  println("| Φ | 合成出的修正因子 | ⊕ 守門 |")
  println("|---|------------------|--------|")
  let rr = @hilbert.ob_rng()
  let tbl = @hilbert.op_rule_table(rr)
  let rg = @hilbert.ob_rng()
  let gt = @hilbert.op_gate_table(rg)
  for i in 0..<tbl.length() {
    println(
      "| " +
      tbl[i].0 +
      " | " +
      tbl[i].1 +
      " | " +
      (if gt[i].1 { "通過" } else { "**不通過**" }) +
      " |",
    )
  }
  println("")
  let ro = @hilbert.ob_rng()
  let (_, _, _, s0, _, _, _) = @hilbert.op_scan(ro)
  let ro2 = @hilbert.ob_rng()
  let (_, _, _, pr, sg, otd, ots, ow) = @hilbert.op_scan_gated(ro2)
  let mut d = "未守門 " +
    s0.to_string() +
    "/" +
    pr.to_string() +
    " 逐元相同；"
  d = d + "守門後 " + sg.to_string() + "/" + pr.to_string() + "，"
  d = d + "成本 " + otd.to_string() + " → " + ots.to_string()
  d = d +
    "（×" +
    @hilbert.fmt_d(otd.to_double() / ots.to_double(), 3) +
    "），" +
    ow.to_string() +
    " 組較便宜。"
  println(d)
  println("")
  println(
    "出問題的不是機器合成的 ⊗ 規則，是手寫的 ⊕ 規則。",
  )
  println("")
  println("### 5.5 範式的結合接 N-41 的 DP（N-67）")
  println("")
  let rd = @hilbert.ob_rng()
  let (dn, _, dch, dsm, ddr, dta, dtd) = @hilbert.rw_dp_scan(rd)
  let mut e = "語料 " +
    dn.to_string() +
    " 式：DP 較便宜 " +
    dch.to_string()
  e = e + "、不變 " + dsm.to_string() + "、較貴 " + ddr.to_string()
  e = e + "；總成本 " + dta.to_string() + " → " + dtd.to_string() + "。"
  println(e)
  let ra = @hilbert.ob_rng()
  let (acnt, ad, aa, ap, afix) = @hilbert.rw_a10_regression(ra)
  let mut f = "A10 的成本回歸：變貴之式 " +
    acnt.to_string() +
    " 式，"
  f = f +
    "直接 " +
    ad.to_string() +
    " → 類 A " +
    aa.to_string() +
    " → 類 A+DP " +
    ap.to_string()
  f = f + "（修好：" + afix.to_string() + "）。"
  println(f)
  let rc = @hilbert.ob_rng()
  let (nch, tr, tdp, bst) = @hilbert.rw_chain_gain(rc)
  let mut g = "長鏈 " +
    nch.to_string() +
    " 條：右結合 " +
    tr.to_string() +
    " → DP " +
    tdp.to_string()
  g = g +
    "（×" +
    @hilbert.fmt_d(tr.to_double() / tdp.to_double(), 4) +
    "），最大單鏈 ×" +
    @hilbert.fmt_d(bst, 4) +
    "。"
  println(g)
  println("")
}

///|
/// 第九輪附錄：19.6 的七筆。
fn appendix9() -> Unit {
  println("")
  println("## 六、第九輪：§19.6 的七筆（N-68 … N-74）")
  println("")
  println("### 6.1 非建構子（N-68）")
  println("")
  println(
    "判準不是宣告，是量測：能不能當中端重寫規則，看它過不過",
  )
  println("類 A 的「Gram 逐元不變」。")
  println("")
  println(
    "| 非建構子 | 可用 | 保正定 | **保 Gram 逐元** | 維數公式相符 |",
  )
  println("|----------|------|--------|------------------|--------------|")
  for r in @hilbert.nonctor_scan() {
    let mut t = "| " + r.0 + " | " + r.1.to_string() + " | " + r.2.to_string()
    t = t + " | **" + r.3.to_string() + "** | " + r.4.to_string() + " |"
    println(t)
  }
  println("")
  println(
    "三者中只有完備化是中端合法的重寫 —— 有限維的完備化是恆等。",
  )
  println("")
  println("### 6.2 L-05″ 整數分解憑證（N-69）")
  println("")
  println("| 形狀 | 位元 | 基準 | N-58 | N-69 |")
  println("|------|------|------|------|------|")
  for cs in [(8, 5, 16), (10, 6, 16), (12, 7, 16), (8, 4, 32)] {
    let (b, a1, a2, _) = @hilbert.rank_cert_compare(cs.0, cs.1, cs.2)
    let mut t = "| " +
      cs.0.to_string() +
      "×" +
      cs.0.to_string() +
      " 秩" +
      cs.1.to_string()
    t = t + " | " + cs.2.to_string() + " | " + b.to_string()
    t = t +
      " | " +
      a1.to_string() +
      " (×" +
      @hilbert.fmt_d(b.to_double() / a1.to_double(), 2) +
      ")"
    t = t +
      " | " +
      a2.to_string() +
      " (×" +
      @hilbert.fmt_d(b.to_double() / a2.to_double(), 2) +
      ") |"
    println(t)
  }
  println("")
  println(
    "最後一列 N-58 是 ×0.94 —— **淨虧**。定理 217-4 寫「救不了秩虧多少」",
  )
  println("時只量了 16 位元那一行。")
  println("")
  println("### 6.3 N-56 之預測的檢驗（N-70）")
  println("")
  println(
    "| 管線 | n | 位元 | 逐素數穩定判定 | 先驗 Hadamard 界 | 比值 |",
  )
  println("|------|---|------|----------------|------------------|------|")
  for r in @hilbert.apriori_verdict_table() {
    let mut t = "| " + r.0 + " | " + r.1.to_string() + " | " + r.2.to_string()
    t = t + " | " + r.3.to_string() + " | " + r.4.to_string()
    t = t +
      " | ×" +
      @hilbert.fmt_d(r.3.to_double() / r.4.to_double(), 3) +
      " |"
    println(t)
  }
  println("")
  println(
    "12 格全部較慢，預測成立；且 k 小的管線受害遠重於 k 大的。",
  )
  println("")
  println("### 6.4 外冪與 Kron 和之特化路徑（N-71）")
  println("")
  let re = @hilbert.ob_rng()
  for r in @hilbert.ek_by_shape(re) {
    let mut t = r.0 +
      "：" +
      r.1.to_string() +
      " 式，通用 " +
      r.2.to_string()
    t = t +
      " → 特化 " +
      r.3.to_string() +
      "（×" +
      @hilbert.fmt_d(r.2.to_double() / r.3.to_double(), 3) +
      "）"
    println(t)
  }
  println("")
  println(
    "外冪用 C_k(G)⁻¹ = C_k(G⁻¹)；Kron 和轉成 Sylvester 方程，",
  )
  println(
    "可解性條件 spec(G_A) ∩ spec(−G_B) = ∅ 由兩個 Gram 皆正定免費取得。",
  )
  println("")
  println("### 6.5 一元構造子之算子層規則（N-72）")
  println("")
  println("| Φ ∘ 構造子 | 合成出的規則 |")
  println("|------------|--------------|")
  let ru = @hilbert.ob_rng()
  for r in @hilbert.uni_rule_table(ru) {
    println("| " + r.uphi + " ∘ " + r.uctor + " | " + r.describe() + " |")
  }
  let rk = @hilbert.ob_rng()
  let ak = @hilbert.uni_adj_ext_k2(rk)
  println("")
  println(
    "adj ∘ 外冪 放開 k 時找不到（指數 C(n−1,k−1)−k 非仿射）；",
  )
  println("把 k 釘死為 2 就找到 " + ak.describe() + "。")
  println("")
  println("### 6.6 N 元普查引擎（N-73）")
  println("")
  println("| 元數 | 格數 | 通過 | 最高維 | 指紋 |")
  println("|------|------|------|--------|------|")
  for s in @hilbert.nary_scan() {
    let mut t = "| " +
      s.0.to_string() +
      " | " +
      s.1.to_string() +
      " | " +
      s.2.to_string()
    t = t + " | " + s.3.to_string() + " | `" + s.4 + "` |"
    println(t)
  }
  println("")
  println("三元那一列必須逐格重現 N-61 的 `419:419:674552611`。")
  println("")
  println("### 6.7 成本比對式義務生成器（N-74）")
  println("")
  println(
    "生成器至此會寫三種義務：律式（N-45）、普查式（N-62）、成本比對式（本條）。",
  )
  println(
    "三種的防線相同：決定性、量測忠實、敗例忠實，加上產出物確實編譯並被呼叫。",
  )
  println("")
}

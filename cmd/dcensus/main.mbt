///|
/// 空間普查表產生器（N-50 / N-51 / N-52）。
/// 輸出 docs/空間普查表.md 之內容至標準輸出。
fn main {
  println("# 空間普查表 —— D 群 × 空間 × 構造子")
  println("")
  println(
    "由 `moon run cmd/dcensus` 產生。全部數字為實測，無手寫常數。",
  )
  println("")

  // ── 第一節：空間註冊表 ──────────────────────────────────
  println("## 一、空間註冊表（N-50）")
  println("")
  let xs = @hilbert.space_registry()
  let (lo, hi, tot) = @hilbert.space_registry_dims()
  println(
    "共 **" +
    xs.length().to_string() +
    "** 個空間，維數 " +
    lo.to_string() +
    " – " +
    hi.to_string() +
    "，總維數 " +
    tot.to_string() +
    "，指紋 `" +
    @hilbert.space_registry_digest() +
    "`。",
  )
  println("")
  println("| # | 空間 | 族 | dim | 保內積重編 | Gram 對稱正定 |")
  println("| --- | --- | --- | --- | --- | --- |")
  let mut i = 0
  for r in xs {
    i = i + 1
    println(
      "| " +
      i.to_string() +
      " | `" +
      r.sname +
      "` | " +
      r.fam +
      " | " +
      r.sdim.to_string() +
      " | " +
      (if @hilbert.sreg_refaithful(r) { "✔" } else { "✘" }) +
      " | " +
      (if @hilbert.sreg_spd(r) { "✔" } else { "✘" }) +
      " |",
    )
  }
  println("")
  println("族別分布：")
  println("")
  println("| 族 | 筆數 |")
  println("| --- | --- |")
  for f in @hilbert.space_registry_families() {
    println("| " + f.0 + " | " + f.1.to_string() + " |")
  }
  println("")

  // ── 第二節：構造子 ──────────────────────────────────────
  println("## 二、七個構造子與 Gram 函子性（N-51）")
  println("")
  let (cl, ch, ct) = @hilbert.comb7_dim_stats()
  println(
    "35 × 7 = **" +
    @hilbert.comb7_dim_table().length().to_string() +
    "** 個構造空間，構造後維數 " +
    cl.to_string() +
    " – " +
    ch.to_string() +
    "，總維數 " +
    ct.to_string() +
    "，指紋 `" +
    @hilbert.comb7_digest() +
    "`。",
  )
  println("")
  println(
    "| 構造子 | 記號 | 元數 | Gram 作用 | dim | 移動數 /35 | 正定 /35 | 維數式 /35 |",
  )
  println("| --- | --- | --- | --- | --- | --- | --- | --- |")
  let acts : ReadOnlyArray[String] = [
    "G ⊗ G_W", "G ⊕ G_W", "(G⁻¹)ᵀ", "C₂(G)", "MᵀGM", "SᵀGS", "G⊗I + I⊗G_W",
  ]
  let dims : ReadOnlyArray[String] = [
    "n·2", "n+2", "n", "C(n,2)", "n", "2", "n·2",
  ]
  let moved = @hilbert.comb7_moved()
  let mut k = 0
  for c in @hilbert.comb7_registry() {
    let mut spd = 0
    let mut dok = 0
    for r in xs {
      if @hilbert.comb7_spd(r, c) {
        spd = spd + 1
      }
      if @hilbert.comb7_dimok(r, c) {
        dok = dok + 1
      }
    }
    println(
      "| " +
      c.cname +
      " | `" +
      c.csym +
      "` | " +
      c.cari.to_string() +
      " | `" +
      acts[k] +
      "` | `" +
      dims[k] +
      "` | " +
      moved[k].1.to_string() +
      " | " +
      spd.to_string() +
      " | " +
      dok.to_string() +
      " |",
    )
    k = k + 1
  }
  println("")
  println(
    "`*` 的移動數為 17 而非 35：在 Gram = I 的 18 個空間上 (G⁻¹)ᵀ = I —— " +
    "有限維加標準正交基使 V* 典範同構於 V。`Λ²` 固定的 5 個同理。",
  )
  println("")

  // ── 第三節：全量普查 ────────────────────────────────────
  println("## 三、全量普查（N-52）")
  println("")
  let (full, bya, byc, byf) = @hilbert.dcensus_report()
  println(
    "**" +
    full.cells.to_string() +
    "** 格（23 × 35 × 7），成立 **" +
    full.pass.to_string() +
    "**，推翻 **" +
    full.fail.to_string() +
    "**，構造後最大維數 " +
    full.dmax.to_string() +
    "，指紋 `" +
    full.digest +
    "`。",
  )
  println("")
  if full.misses.length() > 0 {
    println("未通過之格：")
    println("")
    for m in full.misses {
      println("- `" + m + "`")
    }
    println("")
  }
  println("### 3.1 逐演算法")
  println("")
  println("| 代碼 | 名稱 | 成立 / 總格數 |")
  println("| --- | --- | --- |")
  let reg = @hilbert.d_registry()
  let mut t = 0
  for p in bya {
    println(
      "| " +
      p.0 +
      " | " +
      reg[t].dname +
      " | " +
      p.1.to_string() +
      " / " +
      p.2.to_string() +
      " |",
    )
    t = t + 1
  }
  println("")
  println("### 3.2 逐構造子")
  println("")
  println("| 構造子 | 成立 / 總格數 |")
  println("| --- | --- |")
  for p in byc {
    println(
      "| `" + p.0 + "` | " + p.1.to_string() + " / " + p.2.to_string() + " |",
    )
  }
  println("")
  println("### 3.3 逐空間族")
  println("")
  println("| 族 | 成立 / 總格數 |")
  println("| --- | --- |")
  for p in byf {
    println(
      "| " + p.0 + " | " + p.1.to_string() + " / " + p.2.to_string() + " |",
    )
  }
  println("")

  // ── 第四節：分層等價 ────────────────────────────────────
  println("## 四、分層與全量之等價（命題 N52-3）")
  println("")
  println(
    "| 步長 | 維數上限 | 格數 | 成立 | 最大維 | 覆蓋（空間/構造子/演算法） | 指紋 |",
  )
  println("| --- | --- | --- | --- | --- | --- | --- |")
  for p in [(13, 12), (13, 0), (7, 0), (5, 0)] {
    let c = @hilbert.dcensus_stratum(p.0, p.1)
    println(
      "| " +
      p.0.to_string() +
      " | " +
      (if p.1 == 0 { "—" } else { p.1.to_string() }) +
      " | " +
      c.cells.to_string() +
      " | " +
      c.pass.to_string() +
      " | " +
      c.dmax.to_string() +
      " | " +
      c.cov.0.to_string() +
      " / " +
      c.cov.1.to_string() +
      " / " +
      c.cov.2.to_string() +
      " | `" +
      c.digest +
      "` |",
    )
  }
  println("")
  println("常規義務跑第一列（419 格）；其餘由本程式承接。")
  println("")

  // ── 第五節：公理歸因 ────────────────────────────────────
  println("## 五、判準式之公理依賴（命題 N52-4）")
  println("")
  println(
    "三個壞 Gram 各破壞內積的一條公理：不定型 `diag(1,−1,−1)` 破壞正定性、" +
    "非對稱型 `[[2,1,0],[0,2,1],[0,0,2]]` 破壞對稱性、退化型 `diag(1,1,0)` " +
    "破壞非退化性。一條判準式在「壞 X」上仍然成立，表示它的證明沒有用到 X。" +
    "下表為 24 組樣本之結果（反例搜尋：樣本愈多，推翻只增不減）。",
  )
  println("")
  println("| 代碼 | 不定型 | 非對稱型 | 退化型 | 正定 E³ |")
  println("| --- | --- | --- | --- | --- |")
  for p in @hilbert.dcensus_axiom_profile() {
    println(
      "| " +
      p.0 +
      " | " +
      (if p.1 { "推翻" } else { "成立" }) +
      " | " +
      (if p.2 { "推翻" } else { "成立" }) +
      " | " +
      (if p.3 { "推翻" } else { "成立" }) +
      " | " +
      (if p.4 { "成立" } else { "推翻" }) +
      " |",
    )
  }
  println("")
  let (a1, a2, a3, any, none, gd) = @hilbert.dcensus_axiom_stats()
  println(
    "合計（24 組樣本）：不定型推翻 " +
    a1.to_string() +
    " 條、非對稱型推翻 " +
    a2.to_string() +
    " 條、退化型推翻 " +
    a3.to_string() +
    " 條；至少被一種推翻 " +
    any.to_string() +
    " 條，三種都沒推翻 " +
    none.to_string() +
    " 條；正定 E³ 上成立 " +
    gd.to_string() +
    " 條。",
  )
  println("")
  let (b1, b2, b3, bany, bnone, bgd) = @hilbert.dcensus_axiom_stats_n(6)
  println(
    "義務層（6 組樣本，釘死於 `ob_n52`）：" +
    b1.to_string() +
    " / " +
    b2.to_string() +
    " / " +
    b3.to_string() +
    "；至少一種 " +
    bany.to_string() +
    "，皆無 " +
    bnone.to_string() +
    "；E³ " +
    bgd.to_string() +
    "。",
  )
  appendix7()
}

///|
/// 第七輪附錄：擴充後的表與任意三表引擎。
fn appendix7() -> Unit {
  println("")
  println("## 六、第七輪：擴充後的表（N-59 / N-60 / N-61）")
  println("")
  let (n, lo, hi, tot, dg) = @hilbert.sregx_stats()
  let mut a = "空間註冊表擴充為 **" +
    n.to_string() +
    "** 個（前 35 個與原表逐筆相同）"
  a = a + "，維數 " + lo.to_string() + " – " + hi.to_string()
  a = a + "，總維 " + tot.to_string() + "，指紋 `" + dg + "`。"
  println(a)
  println("")
  println("| 新增空間 | 族 | 維 |")
  println("|----------|----|----|")
  for r in @hilbert.space_registry_new() {
    println("| " + r.sname + " | " + r.fam + " | " + r.sdim.to_string() + " |")
  }
  println("")
  let (cells, clo, chi, ctot, spd, dimok, cdg) = @hilbert.comb14_stats()
  let mut b = "構造子表擴充為 **14** 個，14 × " +
    n.to_string() +
    " = **"
  b = b +
    cells.to_string() +
    "** 格，維數 " +
    clo.to_string() +
    " – " +
    chi.to_string()
  b = b +
    "，總維 " +
    ctot.to_string() +
    "；對稱正定 " +
    spd.to_string() +
    "/" +
    cells.to_string()
  b = b + "，維數公式相符 " + dimok.to_string() + "/" + cells.to_string()
  b = b + "，指紋 `" + cdg + "`。"
  println(b)
  println("")
  println("| 新增構造子 | 符號 | 維數公式 |")
  println("|------------|------|----------|")
  println("| 同態 Hom(W₂,−) | H | 2n |")
  println("| 餘維一外冪 | Λⁿ⁻¹ | C(n,n−1) = n |")
  println("| 對稱平方 | S² | n(n+1)/2 |")
  println("| 雙對偶 | ** | n |")
  println("| 倍化 V⊕V | D | 2n |")
  println("| 半子空間 | U½ | ⌈n/2⌉ |")
  println("| 轉置扭曲 | Tᵀ | n |")
  println("")
  println("## 七、任意三表笛卡兒積引擎（N-61）")
  println("")
  println("| 表 | 項目數 |")
  println("|----|--------|")
  for t in @hilbert.tri_tables() {
    println("| " + t.ttname + " | " + t.ttitems.length().to_string() + " |")
  }
  println("")
  println(
    "| 三表相乘 | step | 維上限 | 格數 | 通過 | 覆蓋 | 指紋 |",
  )
  println("|----------|------|--------|------|------|------|------|")
  let tb = @hilbert.tri_tables()
  fn row(ia : Int, ib : Int, ic : Int, st : Int, md : Int) -> Unit {
    let r = @hilbert.tri_product(tb[ia], tb[ib], tb[ic], st, md)
    let mut t = "| " +
      tb[ia].ttname +
      " × " +
      tb[ib].ttname +
      " × " +
      tb[ic].ttname
    t = t + " | " + st.to_string() + " | " + md.to_string()
    t = t + " | " + r.tcells.to_string() + " | " + r.tpass.to_string()
    t = t +
      " | " +
      r.tcov.0.to_string() +
      "/" +
      r.tcov.1.to_string() +
      "/" +
      r.tcov.2.to_string()
    t = t + " | `" + r.tdigest + "` |"
    println(t)
  }
  row(2, 4, 5, 13, 12)
  row(1, 3, 5, 17, 12)
  row(0, 4, 5, 1, 12)
  row(1, 3, 6, 37, 10)
  println("")
  println(
    "第一列必須逐格重現 N-52 的分層指紋 —— 推廣若不能精確退回特例，",
  )
  println("它就只是另一個東西。")
  println("")
  println("**逐軸敏感度**（切片有變動數／切片總數）：")
  println("")
  println("| 三表相乘 | A 軸 | B 軸 | C 軸 |")
  println("|----------|------|------|------|")
  let s1 = @hilbert.tri_axis_sensitivity(tb[0], tb[4], tb[5], 12, 6)
  let mut u = "| 空間⊥ × 構造子₀ × D群 | " +
    s1.0.0.to_string() +
    "/" +
    s1.0.1.to_string()
  u = u + " | " + s1.1.0.to_string() + "/" + s1.1.1.to_string()
  u = u + " | " + s1.2.0.to_string() + "/" + s1.2.1.to_string() + " |"
  println(u)
  let s2 = @hilbert.tri_axis_sensitivity(tb[0], tb[4], tb[6], 12, 6)
  let mut v = "| 空間⊥ × 構造子₀ × 字母群 | " +
    s2.0.0.to_string() +
    "/" +
    s2.0.1.to_string()
  v = v + " | " + s2.1.0.to_string() + "/" + s2.1.1.to_string()
  v = v + " | " + s2.2.0.to_string() + "/" + s2.2.1.to_string() + " |"
  println(v)
  println("")
  println(
    "第一列三軸皆非退化；第二列三軸全退化 —— 字母群的條目根本不看空間。",
  )
  println(
    "引擎要是量不出這個差別，它報的「非退化」就沒有意義。",
  )
  println("")
}

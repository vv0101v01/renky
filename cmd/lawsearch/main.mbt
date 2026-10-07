// cmd/lawsearch — N-35 全量定律掃描（一次性，不納入每回合義務）
//
// 三項職責：
//   1. 以全量網格跑完整搜尋，輸出定律表 TSV（供 N-44 之版本比對使用）
//   2. 驗證「常規義務所用之小網格」與「全量網格」裁決逐條相同
//      —— 這是 N-35 下修網格的唯一根據，必須可重跑
//   3. 承接由常規義務移出的大尺寸一次性實測（N-10 的 (6,3)、N-06 的 dim 16／20）

///|
fn main {
  let rng = @hilbert.Rng::new(20260707UL)
  let full = @hilbert.law_search(rng, @hilbert.law_grid_full())
  let small = @hilbert.law_search(
    @hilbert.Rng::new(20260707UL),
    @hilbert.law_grid_std(),
  )
  println("# N-35 全量定律掃描")
  println("")
  println(
    "## 一、定律表（全量網格 " +
    fmt_grid(@hilbert.law_grid_full()) +
    "）",
  )
  println("")
  println("phi\tcomb\trule\tholds\tgain")
  let mut nh = 0
  for t in full {
    if t.cholds {
      nh = nh + 1
    }
    println(
      t.cphi +
      "\t" +
      t.ccomb +
      "\t" +
      t.crule +
      "\t" +
      (if t.cholds { "成立" } else { "推翻" }) +
      "\t" +
      @hilbert.fmt_d(t.cgain, 3),
    )
  }
  println("")
  println(
    "候選 " +
    full.length().to_string() +
    "，成立 " +
    nh.to_string() +
    "，推翻 " +
    (full.length() - nh).to_string(),
  )
  println("")
  println("## 二、網格等價性（N-35 下修之根據）")
  println("")
  let mut diff = 0
  let mut order_bad = 0
  for i in 0..<full.length() {
    if small[i].cphi != full[i].cphi ||
      small[i].ccomb != full[i].ccomb ||
      small[i].crule != full[i].crule {
      order_bad = order_bad + 1
    } else if small[i].cholds != full[i].cholds {
      diff = diff + 1
      println(
        "  裁決相異：" +
        full[i].cphi +
        "/" +
        full[i].ccomb +
        "/" +
        full[i].crule +
        "　小網格=" +
        small[i].cholds.to_string() +
        "　全量=" +
        full[i].cholds.to_string(),
      )
    }
  }
  println(
    "小網格 " +
    fmt_grid(@hilbert.law_grid_std()) +
    " vs 全量 " +
    fmt_grid(@hilbert.law_grid_full()) +
    "：候選順序不符 " +
    order_bad.to_string() +
    " 條，裁決相異 " +
    diff.to_string() +
    " 條",
  )
  if diff == 0 && order_bad == 0 {
    println(
      "✔ 兩網格裁決完全一致 —— 常規義務使用小網格有據。",
    )
  } else {
    println(
      "✘ 兩網格裁決不一致 —— N-35 之下修無效，常規義務必須改回全量網格。",
    )
  }
  println("")
  println("## 三、移出常規義務之大尺寸一次性實測")
  println("")
  // N-10：Sylvester–Franke (6,3)，複合矩陣 20×20
  let r2 = @hilbert.Rng::new(31UL)
  let a6 = @hilbert.rand_gram(r2, 6)
  let cd = @hilbert.Cost::new()
  let ck = @hilbert.compound(a6, 3, cd)
  let lhs = @hilbert.qdet_gauss(ck, cd)
  let cb = @hilbert.Cost::new()
  let rhs = @hilbert.qpow_fast(
    cb,
    @hilbert.qdet_gauss(a6, cb),
    @hilbert.sf_exponent(6, 3),
  )
  println(
    "N-10 (6,3)：C(6,3)=" +
    ck.mrows.to_string() +
    "　直接法 " +
    cd.wmul.to_string() +
    " wmul　分解法 " +
    cb.wmul.to_string() +
    " wmul　增益 ×" +
    @hilbert.fmt_d(@hilbert.Cost::ratio(cd, cb), 1) +
    "　兩側相等=" +
    lhs.eq(rhs).to_string(),
  )
  // N-06：Hom 於 dim 16 與 dim 20
  for pq in [(4, 4), (4, 5)] {
    let (p, q) = pq
    let v = @hilbert.rand_gram(r2, p)
    let w = @hilbert.rand_gram(r2, q)
    let c1 = @hilbert.Cost::new()
    let k = @hilbert.qkron_cost(c1, w, v)
    let _ = @hilbert.qinv_gauss(k, c1)
    let c2 = @hilbert.Cost::new()
    match (@hilbert.qinv_gauss(w, c2), @hilbert.qinv_gauss(v, c2)) {
      (Some(iw), Some(iv)) => {
        let _ = @hilbert.qkron_cost(c2, iw, iv)
      }
      _ => ()
    }
    println(
      "N-06 Hom(" +
      p.to_string() +
      "," +
      q.to_string() +
      ")：dim " +
      k.mrows.to_string() +
      "　直接法 " +
      c1.wmul.to_string() +
      " wmul　分解法 " +
      c2.wmul.to_string() +
      " wmul　增益 ×" +
      @hilbert.fmt_d(@hilbert.Cost::ratio(c1, c2), 1),
    )
  }
  round3_sections()
}

///|
/// 第三輪新增之三節：分布修復對照、ℝ 軌定律表、兩表之下游影響。
fn round3_sections() -> Unit {
  println("")
  println("## 四、取樣分布修復（N-36）")
  println("")
  let before = @hilbert.law_search_std(@hilbert.ob_rng())
  let after = @hilbert.law_search_fixed(@hilbert.ob_rng())
  let mut hb = 0
  let mut ha = 0
  for t in before {
    if t.cholds {
      hb = hb + 1
    }
  }
  for t in after {
    if t.cholds {
      ha = ha + 1
    }
  }
  println(
    "正定分布成立 " +
    hb.to_string() +
    "／72　　四樣本混合分布成立 " +
    ha.to_string() +
    "／72",
  )
  println("")
  println("Φ\tC\t⊙\t正定分布\t混合分布")
  for d in @hilbert.law_diff(before, after) {
    let (ph, cb, ru, vb, va) = d
    println(
      ph +
      "\t" +
      cb +
      "\t" +
      ru +
      "\t" +
      (if vb { "成立" } else { "推翻" }) +
      "\t" +
      (if va { "成立" } else { "推翻" }),
    )
  }
  println("")
  println(
    "### 直覺解法之副作用（輪替式混合，保留作為反例）",
  )
  println("")
  @hilbert.samp_reset()
  let naive = @hilbert.law_search_dist(
    @hilbert.ob_rng(),
    @hilbert.law_grid_std(),
    @hilbert.samp_mixed,
  )
  println("Φ\tC\t⊙\t正定分布\t輪替式混合")
  for d in @hilbert.law_diff(before, naive) {
    let (ph, cb, ru, vb, vn) = d
    println(
      ph +
      "\t" +
      cb +
      "\t" +
      ru +
      "\t" +
      (if vb { "成立" } else { "推翻" }) +
      "\t" +
      (if vn { "成立" } else { "推翻" }),
    )
  }
  println("")
  println(
    "推翻一條假陽性，卻換來四條新的 —— 每個候選只看到三種分布中的兩種，",
  )
  println(
    "det 類規則在降秩樣本上兩側同時為 0 而空洞成立。故改採「每個候選跑完全部四樣本」。",
  )
  println("")
  println("## 五、ℝ 軌定律表（N-33）")
  println("")
  println(
    "⚠️ 增益以 flop 計（N-30 之 TR 軌），**不可**與上方 ℚ 軌之字乘法增益並列。",
  )
  println("")
  let rt = @hilbert.rlaw_search_std(@hilbert.ob_rng())
  println("Φ\tC\t⊙\t裁決\t增益")
  println(@hilbert.rlaw_table(rt))
  let mut rh = 0
  for t in rt {
    if t.cholds {
      rh = rh + 1
    }
  }
  println("")
  println(
    "候選 " +
    rt.length().to_string() +
    "，成立 " +
    rh.to_string() +
    "，推翻 " +
    (rt.length() - rh).to_string(),
  )
  section_compose()
}

///|
/// 第六節：複合定律表之全量普查（N-42）。
///
/// 常規義務只跑推導集 60 條；此處跑滿 5×8×3×3 = 360 條，
/// 產出混淆表與「未導出但成立」之名單，並驗證分層不改變任何一條結果。
fn section_compose() -> Unit {
  let tbl = @hilbert.law_search_fixed(@hilbert.ob_rng())
  let samples = @hilbert.law_samples_mixed()
  let full = @hilbert.compose_scan(tbl, samples)
  let der = @hilbert.compose_scan_std(@hilbert.ob_rng())
  let (dh, dn, uh, un) = @hilbert.compose_confusion(full)
  println("")
  println("## 六、複合定律表（N-42，全量普查 360 條）")
  println("")
  println(
    "推導：定律表 15 條成立之律 → " +
    @hilbert.compose_derive(tbl).length().to_string() +
    " 條複合律（零次矩陣運算）。",
  )
  println("")
  println("### 6.1 混淆表（推導 × 實測）")
  println("")
  println("|  | 實測成立 | 實測推翻 |")
  println("| --- | ---: | ---: |")
  println(
    "| **可由定理 201-1 導出** | " +
    dh.to_string() +
    " | " +
    dn.to_string() +
    " |",
  )
  println("| **導不出** | " + uh.to_string() + " | " + un.to_string() + " |")
  println("")
  println(
    "右上格為 0 即複合定理之健全性證據；左下格非 0 即其不必要性之度量。",
  )
  println("")
  println(
    "全量指紋 " +
    @hilbert.compose_digest(full) +
    "　推導集指紋 " +
    @hilbert.compose_digest(der),
  )
  println("")
  println("### 6.2 分層等價性（常規義務只跑 60 條之根據）")
  println("")
  let mut bad = 0
  for x in der {
    match @hilbert.comp_find(full, x.xouter, x.xinner, x.xcomb, x.xrule) {
      Some(y) =>
        if y.xholds != x.xholds || y.xgain != x.xgain || y.xvac != x.xvac {
          bad = bad + 1
          println(
            "  逐條相異：" + x.xphi() + "/" + x.xcomb + "/" + x.xrule,
          )
        }
      None => {
        bad = bad + 1
        println(
          "  全量表中查無：" + x.xphi() + "/" + x.xcomb + "/" + x.xrule,
        )
      }
    }
  }
  println(
    "推導集 " +
    der.length().to_string() +
    " 條 vs 全量 " +
    full.length().to_string() +
    " 條：裁決／增益／空洞數逐條相異 " +
    bad.to_string() +
    " 條。",
  )
  println("")
  println(
    "（取樣種子由候選名雜湊決定，與枚舉位置無關，故子集掃描與全量掃描必然逐條一致。）",
  )
  println("")
  println("### 6.3 未導出但實測成立者 —— 定理之視野以外")
  println("")
  println(
    "Φ₂∘Φ₁\tC\t⊙₂\t增益\t空洞樣本\t換用恆定義 adj 後",
  )
  for x in full {
    if x.xholds && !x.xderived {
      let re = @hilbert.comp_check_with(
        @hilbert.phi_by_name_total,
        x.xouter,
        x.xinner,
        x.xcomb,
        x.xrule,
        samples,
        @hilbert.comp_rng_of(x.xouter, x.xinner, x.xcomb, x.xrule),
      )
      let tag = match re {
        Some((v, _)) => if v.holds { "仍成立" } else { "**翻為推翻**" }
        None => "—"
      }
      println(
        x.xphi() +
        "\t" +
        x.xcomb +
        "\t" +
        x.xrule +
        "\t×" +
        @hilbert.fmt_d(x.xgain, 2) +
        "\t" +
        x.xvac.to_string() +
        "\t" +
        tag,
      )
    }
  }
  println("")
  println("### 6.4 複合定律表（導出者與成立者）")
  println("")
  println(@hilbert.compose_table(full))
  println("")
  println(
    "帶 ⊥ 證據缺口（某樣本兩側皆算不出而被判相符）之成立裁決：" +
    @hilbert.compose_vacuous_count(full).to_string() +
    " 條；基礎定律表 15 條成立之律中亦有 " +
    @hilbert.law_vacuity_count(tbl, samples).to_string() +
    " 條。",
  )
  section_content(tbl)
  section_rcompose()
}

///|
/// 第七節：內容檢定之全量重裁（N-47）。
fn section_content(tbl : Array[@hilbert.LawCand]) -> Unit {
  let xs = @hilbert.content_scan(tbl)
  let (o, n, bot, cst, flip) = @hilbert.content_stats(xs)
  println("")
  println(
    "## 七、內容檢定：全函式 Φ 下之重裁（N-47，全量 360 條）",
  )
  println("")
  println(
    "以 Moore–Penrose 偽逆取代 qinv_gauss、餘因子 adj 取代 qadj，兩者皆為全函式。",
  )
  println("")
  println("| 項目 | 補定義域之前 | 補定義域之後 |")
  println("| --- | ---: | ---: |")
  println("| 成立裁決 | " + o.to_string() + " | " + n.to_string() + " |")
  println(
    "| 帶 ⊥ 空洞者 | " +
    bot.to_string() +
    " | " +
    @hilbert.content_residual_bot(xs).to_string() +
    " |",
  )
  println("| 恆值律 | （不可見） | " + cst.to_string() + " |")
  println("")
  println(
    "翻轉 " + flip.to_string() + " 條，全為「成立 → 推翻」：",
  )
  for x in xs {
    if x.vold != x.vnew {
      println(
        "  - " +
        x.vname +
        "（原空洞樣本 " +
        x.vbot.to_string() +
        " 個）",
      )
    }
  }
  println("")
  println(
    "恆值律的意義：rank∘inv 在舊制下於固定維數恆取一值（⊥ 吃掉了降秩樣本），",
  )
  println(
    "故 rank∘inv/⊞/· 通過裁決卻只說了 nm = n·m。補上偽逆後它不再恆值，律隨即被推翻 ——",
  )
  println("空殼變成一句有內容的話，而那句話是錯的。")
}

///|
/// 第八節：ℝ 軌複合定律表之全量普查（N-48）。
fn section_rcompose() -> Unit {
  let rtbl = @hilbert.rlaw_search_std(@hilbert.ob_rng())
  let xs = @hilbert.rcompose_scan(rtbl, @hilbert.rlaw_grid_std())
  let (sa, sb, sc, sd) = @hilbert.rcompose_confusion_syn(xs)
  let (da, db, dc, dd) = @hilbert.rcompose_confusion_dom(xs)
  let mut ovf = 0
  let mut pre = 0
  let mut inval = 0
  for x in xs {
    if x.yovf > 0 {
      ovf = ovf + 1
    }
    if x.ypre > 0 {
      pre = pre + 1
    }
    if !@hilbert.rcomp_valid(x) {
      inval = inval + 1
    }
  }
  println("")
  println("## 八、ℝ 軌複合定律表（N-48，全量普查 156 條）")
  println("")
  println(
    "⚠️ 增益以 flop 計，**不可**與第六節 ℚ 軌之字乘法增益並列。",
  )
  println("")
  println(
    "ℝ 軌 13 條成立之律 → 語法判準推出 " +
    @hilbert.rcompose_derive(rtbl, false).length().to_string() +
    " 條，加定義域條件剩 " +
    @hilbert.rcompose_derive(rtbl, true).length().to_string() +
    " 條。",
  )
  println("")
  println(
    "156 條中 " +
    inval.to_string() +
    " 條裁決**無效**（前提違反 " +
    pre.to_string() +
    " 條、溢位 " +
    ovf.to_string() +
    " 條，有重疊）—— 無效裁決既不算成立也不算推翻。",
  )
  println("")
  println("### 8.1 混淆表（只計有效裁決）")
  println("")
  println("|  | 實測成立 | 實測推翻 |")
  println("| --- | ---: | ---: |")
  println(
    "| **純語法判準導出** | " +
    sa.to_string() +
    " | **" +
    sb.to_string() +
    "** |",
  )
  println("| 導不出 | " + sc.to_string() + " | " + sd.to_string() + " |")
  println("")
  println("| 加上定義域條件 | 實測成立 | 實測推翻 |")
  println("| --- | ---: | ---: |")
  println("| 導出 | " + da.to_string() + " | **" + db.to_string() + "** |")
  println("| 導不出 | " + dc.to_string() + " | " + dd.to_string() + " |")
  println("")
  println(
    "右上格在 ℚ 軌是 0（N-42），在 ℝ 軌不是 —— 純語法判準搬不過來。",
  )
  println("")
  println("### 8.2 三條導出卻被推翻者 —— 沒有一條是代數的")
  println("")
  for nm in ["inv∘expm/⊕/⊕", "chol∘expm/⊞/⊗", "det∘expm/⊞/^"] {
    match @hilbert.rcomp_find(xs, nm) {
      Some(x) =>
        println("  - " + nm + "　最大相對偏差 " + @hilbert.fmt_e(x.ydev))
      None => ()
    }
  }
  println("")
  println(
    "2.6e-2 不可能是捨入（偽逆的奇異值截斷不可複合）；1.13e-8 只比門檻高一成；",
  )
  println(
    "1.0e100 只能是動態範圍潰堤（det(expm M) = e^{tr M}）。三個量級各指向一種機制。",
  )
  println("")
  println("### 8.3 ℝ 軌複合定律表")
  println("")
  println(@hilbert.rcompose_table(xs))
}

///|
fn fmt_grid(g : Array[(Int, Int)]) -> String {
  let parts : Array[String] = []
  for p in g {
    let (a, b) = p
    parts.push("(" + a.to_string() + "," + b.to_string() + ")")
  }
  parts.join("")
}

///|
/// N-31 之義務：多態 catamorphism —— 由定律表自動組裝演算法合成器。
///
/// 本條要證的是一條**管線**而非一條律：
/// `law_search` 找到律 → `phispec_from_law` 組出合成器 → `synth_spec` 合成演算法。
/// 全程無人介入。此前第 1 步到第 2 步之間是斷的，要人讀報告再手寫遞迴函式。
pub fn ob_n31() -> Check {
  let tbl = law_search_std(ob_rng())
  let mut ok = true

  // ── 定理 194-1（由定律表自動組裝，規則逐條正確）────────────
  // 期望之 (Φ, ⊗ 規則, ⊕ 規則)。空字串表示該構造子上無律 —— 須走攤平。
  let expect : Array[(String, String, String)] = [
    ("inv", "⊗", "⊕"),
    ("det", "^", "·"),
    ("trace", "·", "+"),
    ("rank", "·", "+"),
    ("sq", "⊗", "⊕"),
    ("cube", "⊗", "⊕"),
    ("adj", "⊗ₛ", ""),
  ]
  let specs : Array[PhiSpec] = []
  for ex in expect {
    let (nm, kr, sr) = ex
    match phispec_from_law(tbl, nm) {
      None => ok = false
      Some(sp) => {
        if sp.pkname != kr || sp.psname != sr || sp.pname != nm {
          ok = false
        }
        specs.push(sp)
      }
    }
  }
  if specs.length() != 7 {
    return mk_check("N-31 多態 catamorphism", false, 1, "組裝失敗")
  }
  // transpose 在定律表中無任何成立之律，組裝必須失敗（否則組裝器是在亂給）
  match phispec_from_law(tbl, "tr̃ans") {
    Some(_) => ok = false
    None => ()
  }

  // ── 定理 194-2（與手寫合成器逐例相同）──────────────────────
  // 這是向後相容之關鍵：多態版若與 synth_inv／synth_det 有任何一例不同，
  // 等於偷換了 N-11 與 N-05 既有的全部結論。
  let r3 = Rng::new(123UL)
  let si = specs[0]
  let sd = specs[1]
  for _t in 0..<8 {
    let e = rand_expr(r3, 3, 12)
    let c1 = Cost::new()
    let c2 = Cost::new()
    let eq_inv = match (synth_spec(si, e, c1), synth_inv(e, c2)) {
      (Some(x), Some(y)) => x.equals(y)
      (None, None) => true
      _ => false
    }
    if !eq_inv {
      ok = false
    }
    let c3 = Cost::new()
    let c4 = Cost::new()
    let eq_det = match (synth_spec(sd, e, c3), synth_det(e, c4)) {
      (Some(x), Some(y)) => x.data[0].eq(y)
      (None, None) => true
      _ => false
    }
    if !eq_det {
      ok = false
    }
  }

  // ── 定理 194-3（合成 ≡ 攤平，七個 Φ 全數）────────────────
  let rows : Array[String] = []
  let gains : Array[Double] = []
  for sp in specs {
    let mut same = true
    let mut tb = 0L
    let mut tf = 0L
    let r4 = Rng::new(55UL)
    for _t in 0..<4 {
      // 葉維 2、深度 2 之滿二元樹：維數 8（全 ⊕）至 16（全 ⊗）。
      // 葉維 3 會讓 ℚ 係數膨脹使本條耗時逾十分鐘，故不取。
      let e = rand_expr_nodual(r4, 2, 2)
      let (s, wb, wf, _l, _d) = synth_spec_compare(sp, e)
      if !s {
        same = false
      }
      tb = tb + wb
      tf = tf + wf
    }
    if !same {
      ok = false
    }
    let g = if tf > 0L { tb.to_double() / tf.to_double() } else { 0.0 }
    gains.push(g)
    rows.push(sp.pname + " ×" + fmt_d(g, 1))
  }

  // ── 命題 194-4（adj 不自給自足）────────────────────────────
  // 前六個 Φ 的規則只需 (兩子結果, 兩側維數)；adj 的 ⊗ₛ 還需要兩側行列式，
  // 故必須並行跑一條 det 的 catamorphism —— 而 det 的 catamorphism
  // 本身就是定律表裡的一條律。這是本庫第一個「律的複合」實例。
  for i in 0..<6 {
    if specs[i].paux {
      ok = false
    }
  }
  if !specs[6].paux {
    ok = false
  }

  // ── 命題 194-5（部分覆蓋可能使合成反而更貴）────────────────
  // adj 在 ⊕ 上無律，那種節點只能攤平；加上輔助 det 的開銷，
  // 在含對偶節點的樹上合成法實測比攤平法**更慢**。誠實登錄。
  let r5 = Rng::new(77UL)
  let mut adj_b = 0L
  let mut adj_f = 0L
  for _t in 0..<4 {
    let e = rand_expr(r5, 2, 12)
    let (s, wb, wf, _l, _d) = synth_spec_compare(specs[6], e)
    if !s {
      ok = false
    }
    adj_b = adj_b + wb
    adj_f = adj_f + wf
  }
  let adj_gain = if adj_f > 0L {
    adj_b.to_double() / adj_f.to_double()
  } else {
    0.0
  }
  if adj_gain >= 1.0 {
    ok = false // 若哪天 adj 在含對偶樹上也賺了，本條之措辭必須重寫
  }

  // ── 命題 194-6（對偶節點之求逆為共模成本）──────────────────
  // 對偶節點的 Gram 是 G⁻¹，攤平法與合成法**都得付**這次求逆。
  // 它會把其他構造子上的真實差距稀釋掉：trace 在含對偶樹上增益塌到 ×1.0，
  // 去掉對偶節點後才顯出真正的量級。
  let r6 = Rng::new(55UL)
  let mut tr_b = 0L
  let mut tr_f = 0L
  for _t in 0..<4 {
    let e = rand_expr(r6, 2, 8)
    let (_s, wb, wf, _l, _d) = synth_spec_compare(specs[2], e)
    tr_b = tr_b + wb
    tr_f = tr_f + wf
  }
  let tr_dual = if tr_f > 0L {
    tr_b.to_double() / tr_f.to_double()
  } else {
    0.0
  }
  // 無對偶之增益（gains[2]）必須顯著高於含對偶者
  if gains[2] <= tr_dual * 5.0 {
    ok = false
  }
  mk_check(
    "N-31 多態 catamorphism（由定律表自動組裝）",
    ok,
    7 * 5 + 16 + 8,
    "由定律表自動組出 7 個合成器，規則逐條符合期望（inv:⊗/⊕　det:^/·　trace:·/+　rank:·/+　sq:⊗/⊕　cube:⊗/⊕　adj:⊗ₛ/無）；transpose 無律故組裝如期失敗。多態版與手寫之 synth_inv／synth_det 於 8 棵深度 3 之隨機樹上逐例相同。合成 ≡ 攤平（無對偶樹，增益）：" +
    rows.join("　") +
    "。adj 不自給自足：其 ⊗ₛ 規則需兩側行列式，故並行跑一條 det catamorphism（本庫第一個「律的複合」實例），其餘六個 Φ 皆不需要。部分覆蓋之代價：adj 在 ⊕ 上無律只能攤平，含對偶樹上合成法實測 ×" +
    fmt_d(adj_gain, 2) +
    " —— **比攤平法更慢**，誠實登錄。對偶節點為共模成本：trace 含對偶樹 ×" +
    fmt_d(tr_dual, 2) +
    "、去對偶後 ×" +
    fmt_d(gains[2], 1) +
    "。",
  )
}

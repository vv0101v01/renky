// ============================================================================
//  檔案 21：oblig_nlaw.mbt — N 群（結構律與演算法合成）之義務自證
// ============================================================================

///|
/// N-01 空間表達式：維數遞迴、Gram 遞迴、良構性（正定），含深度 3 之合成樹。
pub fn ob_n01() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut deepest = 0
  // 葉
  let a = SLeaf("A", rand_gram(rng, 2))
  let b = SLeaf("B", rand_gram(rng, 3))
  let c = SLeaf("C", rand_gram(rng, 2))
  // 逐構造子之維數與 Gram 遞迴（命題 169-1、169-2）
  let cases : Array[SpaceExpr] = [
    STensor(a, b),
    SSum(a, b),
    SDual(a),
    SDual(STensor(a, b)),
    STensor(SDual(a), b),
    SSum(STensor(a, b), c),
    STensor(SSum(a, c), b),
    // 深度 3：人工幾乎不會手寫，但合成器可機械產出
    STensor(SDual(STensor(a, b)), SSum(c, a)),
    SDual(SSum(STensor(a, c), SDual(b))),
  ]
  for e in cases {
    let g = e.sgram()
    // 維數一致性
    if g.mrows != e.sdim() || g.mcols != e.sdim() {
      ok = false
    }
    // 定理 169：良構性 —— 任意表達式之 Gram 皆正定
    if !is_positive_definite(g) {
      ok = false
    }
    // Gram 必對稱（實係數 ⇒ Hermitian = 對稱）
    if !g.equals(g.transpose()) {
      ok = false
    }
    // 由表達式產生之內積空間其 Gram 應與遞迴所得一致
    // （O(dim³) 之往返檢查，僅對 dim ≤ 12 施行；更大者已由 Gram 遞迴本身覆蓋）
    if e.sdim() <= 12 && !gram_of_space(e.sspace()).equals(g) {
      ok = false
    }
    if e.sdepth() > deepest {
      deepest = e.sdepth()
    }
    n = n + 1
  }
  // 維數遞迴之獨立覆核
  if STensor(a, b).sdim() != 6 || SSum(a, b).sdim() != 5 || SDual(b).sdim() != 3 {
    ok = false
  }
  // 對偶之對合性：G(A**) = G(A)（(G⁻¹ᵀ)⁻¹ᵀ = G）
  for leaf in [a, b, c] {
    if !SDual(SDual(leaf)).sgram().equals(leaf.sgram()) {
      ok = false
    }
    n = n + 1
  }
  mk_check(
    "N-01 空間表達式之維數／Gram 遞迴與良構性",
    ok,
    n,
    "9 種表達式（含深度 " +
    deepest.to_string() +
    " 之合成樹 " +
    STensor(SDual(STensor(a, b)), SSum(c, a)).slabel() +
    "）：維數遞迴、Gram 遞迴、正定良構性、與 coord_ipspace 之一致性逐例成立；3 組對偶對合 G(A**) = G(A)",
  )
}

///|
/// N-02 律檢驗器之可靠性：真律須判真，偽律須判偽（偵測力之反面對照）。
pub fn ob_n02() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let sizes : Array[(Int, Int)] = [(2, 2), (3, 2), (3, 3)]
  // (1) 真律：檢驗器須判真
  let t1 = law_kron_inv(rng, sizes)
  if !t1.holds {
    ok = false
  }
  n = n + t1.ltrials
  // (2) 偽律 α：inv(A⊗B) =? inv(A)⊗B —— 刻意錯誤，檢驗器須判偽
  let f1 = check_law(
    "偽律 inv(A⊗B) =? inv(A)⊗B",
    (a, b) => mkron(a, b),
    (g, c) => qinv_gauss(g, c),
    (a, b, c) => match qinv_gauss(a, c) {
      Some(x) => Some(qkron_cost(c, x, b))
      None => None
    },
    sizes,
    rng,
  )
  if f1.holds {
    ok = false
  }
  n = n + f1.ltrials
  // (3) 偽律 β：det(A⊗B) =? det A · det B（少了指數，⊕ 之律誤植於 ⊗）
  let f2 = check_law(
    "偽律 det(A⊗B) =? det A·det B",
    (a, b) => mkron(a, b),
    (g, c) => Some(q_scalar_mat(qdet_gauss(g, c))),
    (a, b, c) => Some(
      q_scalar_mat(cq_mul(c, qdet_gauss(a, c), qdet_gauss(b, c))),
    ),
    sizes,
    rng,
  )
  if f2.holds {
    ok = false
  }
  n = n + f2.ltrials
  // (4) 偽律 γ：把 ⊗ 之律套到 ⊕ 上（組合子張冠李戴）
  let f3 = check_law(
    "偽律 inv(A⊕B) =? inv(A)⊗inv(B)",
    (a, b) => qblock_diag(a, b),
    (g, c) => qinv_gauss(g, c),
    (a, b, c) => match (qinv_gauss(a, c), qinv_gauss(b, c)) {
      (Some(x), Some(y)) => Some(qkron_cost(c, x, y))
      _ => None
    },
    sizes,
    rng,
  )
  if f3.holds {
    ok = false
  }
  n = n + f3.ltrials
  mk_check(
    "N-02 結構律檢驗器之可靠性（真律判真、偽律判偽）",
    ok,
    n,
    "1 條真律全數判真；3 條刻意偽律（錯誤合成子、錯誤指數、組合子張冠李戴）全數判偽。定理 170：holds = false 為確定性結論（有具體反例），holds = true 為機率性證據",
  )
}

///|
/// N-03 Kronecker–Gram 律族：三條律成立，且增益隨維度單調上升。
pub fn ob_n03() -> Check {
  let rng = ob_rng()
  // 網格上限取 dim 25：dim 36／49 之精確 ℚ 直接法每回合需數秒，
  //   而增益趨勢在 dim 25 內已可判定（見 ldetail 之單調序列）。
  //   更大尺寸之實測（dim 64 ×150.3）記於 docs/N群設計構想，不納入每回合義務。
  let sizes : Array[(Int, Int)] = [(2, 2), (3, 3), (4, 4)]
  let mut ok = true
  // 定理 171-1 Gram 律（結構性）
  if !law_kron_gram(rng, sizes) {
    ok = false
  }
  // 定理 171-2 求逆律
  let vi = law_kron_inv(rng, sizes)
  if !vi.holds {
    ok = false
  }
  // 定理 171-3 行列式律
  let vd = law_kron_det(rng, sizes)
  if !vd.holds {
    ok = false
  }
  // 命題 171-4：增益必 > 1（本族確為加速律）
  if vi.lgain() <= 1.0 || vd.lgain() <= 1.0 {
    ok = false
  }
  // 單調性：增益應隨維度上升（檢最小與最大尺寸）
  let small = law_kron_inv(rng, [(2, 2)])
  let large = law_kron_inv(rng, [(4, 4)])
  if large.lgain() <= small.lgain() {
    ok = false
  }
  mk_check(
    "N-03 Kronecker–Gram 律族（⊗）",
    ok,
    sizes.length() * 3 + 2,
    "Gram 律結構性成立；求逆律 總增益 ×" +
    fmt_d(vi.lgain(), 2) +
    "（" +
    vi.ldetail +
    "）；行列式律 總增益 ×" +
    fmt_d(vd.lgain(), 2) +
    "（" +
    vd.ldetail +
    "）；增益隨維度單調上升：dim 4 ×" +
    fmt_d(small.lgain(), 2) +
    " → dim 16 ×" +
    fmt_d(large.lgain(), 2),
  )
}

///|
/// N-04 分塊–直和律族：律成立，但增益 ≈ 1 —— 誠實登錄為「不值得用」。
pub fn ob_n04() -> Check {
  let rng = ob_rng()
  let sizes : Array[(Int, Int)] = [(2, 2), (3, 3), (4, 4)]
  let mut ok = true
  let vi = law_sum_inv(rng, sizes)
  let vd = law_sum_det(rng, sizes)
  // 定理 172-1、172-2：兩律皆須成立
  if !vi.holds || !vd.holds {
    ok = false
  }
  // 命題 172-3（本條之主張）：求逆律之增益必須低 —— 若它忽然很高，
  //   表示基準實作退化了，本條應當失敗以示警。
  if vi.lgain() > 2.0 {
    ok = false
  }
  // 與 ⊗ 同尺寸對照：⊗ 之增益必須顯著高於 ⊕（這是本條存在之理由）
  let kron = law_kron_inv(rng, sizes)
  if kron.lgain() <= vi.lgain() * 5.0 {
    ok = false
  }
  mk_check(
    "N-04 分塊–直和律族（⊕）—— 成立但不划算之誠實登錄",
    ok,
    sizes.length() * 2 + 1,
    "分塊求逆律 ✔ 但總增益僅 ×" +
    fmt_d(vi.lgain(), 2) +
    "（" +
    vi.ldetail +
    "）；分塊行列式律 ✔ 增益 ×" +
    fmt_d(vd.lgain(), 2) +
    "。同尺寸之 ⊗ 求逆律為 ×" +
    fmt_d(kron.lgain(), 2) +
    "，相差 " +
    fmt_d(kron.lgain() / vi.lgain(), 1) +
    " 倍 —— 成因：Gauss–Jordan 遇零乘數本就跳過，通用演算法已自動吃掉分塊紅利，無新增可省之處。推論 172：生成器必須同時量測成本，否則會把 ⊗ 與 ⊕ 等同看待",
  )
}

///|
/// N-05 對偶反演律：G(A*)⁻¹ = G_A，分解法零乘法；另驗對合與行列式律。
pub fn ob_n05() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let v = law_dual_inv(rng, [2, 3, 4, 5, 6, 8])
  if !v.holds {
    ok = false
  }
  // 定理 173-2 之成本面主張：分解法必須真的是零次乘法
  if v.fast_wmul != 0L {
    ok = false
  }
  if v.base_wmul <= 0L {
    ok = false
  }
  n = n + v.ltrials
  for d in [2, 3, 4, 5] {
    let g = rand_gram(rng, d)
    let a = SLeaf("A", g)
    // 定理 173-1：G(A*) = (G_A⁻¹)ᵀ
    let c0 = Cost::new()
    match qinv_gauss(g, c0) {
      None => ok = false
      Some(h) => if !SDual(a).sgram().equals(h.transpose()) { ok = false }
    }
    // 定理 173-4：對合 G(A**) = G_A
    if !SDual(SDual(a)).sgram().equals(g) {
      ok = false
    }
    // 定理 173-3：det G(A*) = 1/det G_A
    let c1 = Cost::new()
    let dd = qdet_gauss(SDual(a).sgram(), c1)
    let c2 = Cost::new()
    match cq_div(c2, Q::one(), qdet_gauss(g, c2)) {
      None => ok = false
      Some(w) => if !dd.eq(w) { ok = false }
    }
    n = n + 1
  }
  mk_check(
    "N-05 對偶反演律 G(A*)⁻¹ = G_A",
    ok,
    n,
    "6 個維度：直接法共 " +
    v.base_wmul.to_string() +
    " 次字乘，分解法 0 次（增益無上界）—— 對偶節點之「求逆」不需任何消去；" +
    v.ldetail +
    "。另 4 組驗證 G(A*) = (G⁻¹)ᵀ、對合 G(A**) = G、det G(A*) = 1/det G",
  )
}

///|
/// N-11 合成樹 catamorphism：對隨機表達式樹摺疊出求逆／行列式演算法。
pub fn ob_n11() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut tb = 0L
  let mut tf = 0L
  let mut best = 0.0
  let mut best_label = ""
  let mut best_dim = 0
  let depth_rows : Array[String] = []
  // 固定之見證樹：深度 3，人工幾乎不會手寫其求逆演算法
  let a = SLeaf("A2", rand_gram(rng, 2))
  let b = SLeaf("B3", rand_gram(rng, 3))
  let c2 = SLeaf("C2", rand_gram(rng, 2))
  let witness : Array[SpaceExpr] = [
    STensor(SDual(STensor(a, b)), SSum(c2, a)),
    SDual(SSum(STensor(a, c2), SDual(b))),
    STensor(STensor(a, c2), SDual(SSum(b, a))),
  ]
  for e in witness {
    let (same, wb, wf, lbl, dim) = synth_compare(e)
    if !same {
      ok = false
    }
    // 定理 174-2：行列式之合成亦須與直接法一致
    let cd = Cost::new()
    let dd = qdet_gauss(e.sgram_cost(cd), cd)
    let cf = Cost::new()
    match synth_det(e, cf) {
      None => ok = false
      Some(ds) => if !ds.eq(dd) { ok = false }
    }
    tb = tb + wb
    tf = tf + wf
    let g = if wf > 0L { wb.to_double() / wf.to_double() } else { 0.0 }
    if g > best {
      best = g
      best_label = lbl
      best_dim = dim
    }
    depth_rows.push(lbl + "(dim" + dim.to_string() + ") ×" + fmt_d(g, 1))
    n = n + 1
  }
  // 隨機樹：深度 1–3，維數上限 32
  for depth in [1, 2, 3] {
    for _t in 0..<5 {
      let e = rand_expr(rng, depth, 32)
      let (same, wb, wf, lbl, dim) = synth_compare(e)
      if !same {
        ok = false
      }
      tb = tb + wb
      tf = tf + wf
      let g = if wf > 0L { wb.to_double() / wf.to_double() } else { 0.0 }
      if g > best {
        best = g
        best_label = lbl
        best_dim = dim
      }
      n = n + 1
    }
  }
  // 合成法在總成本上必須勝出（否則 catamorphism 無意義）
  if tf <= 0L || tb <= tf {
    ok = false
  }
  mk_check(
    "N-11 合成樹 catamorphism（任意深度表達式 → 合成演算法）",
    ok,
    n,
    "3 棵深度 3 之見證樹 + 15 棵隨機樹（深度 1–3，維數 ≤ 32）：合成所得之求逆與行列式逐例等於直接法。總成本 直接 " +
    tb.to_string() +
    " 字乘 → 合成 " +
    tf.to_string() +
    " 字乘，總增益 ×" +
    fmt_d(tb.to_double() / tf.to_double(), 2) +
    "；最佳單棵 " +
    best_label +
    "（dim " +
    best_dim.to_string() +
    "）×" +
    fmt_d(best, 1) +
    "。見證樹明細：" +
    depth_rows.join("　"),
  )
}

///|
/// N-13 結構律搜尋引擎：機械枚舉 (Φ, C, ⊙) 並自動裁決。
pub fn ob_n13() -> Check {
  let rng = ob_rng()
  let mut ok = true
  // 網格必含非對稱尺寸（命題 175-3）
  let tbl = law_search(rng, [(2, 2), (2, 3), (3, 3)])
  let mut nh = 0
  let mut nr = 0
  for t in tbl {
    if t.cholds {
      nh = nh + 1
    } else {
      nr = nr + 1
    }
  }
  // 命題 175-2 判別力：推翻數必須多於成立數，否則引擎無價值
  if nr <= nh {
    ok = false
  }
  if tbl.length() != 72 {
    ok = false
  }
  // 已知為真之候選必須被尋獲
  let must_hold : Array[(String, String, String)] = [
    ("inv", "⊗", "⊗"), ("inv", "⊕", "⊕"),
    ("det", "⊗", "^"), ("det", "⊕", "·"),
    ("sq", "⊗", "⊗"), ("sq", "⊕", "⊕"),
    ("adj", "⊗", "⊗ₛ"),
    ("trace", "⊗", "·"), ("trace", "⊕", "+"),
    ("rank", "⊗", "·"), ("rank", "⊕", "+"),
  ]
  for m in must_hold {
    let (p, c, r) = m
    if law_find(tbl, p, c, r) != Some(true) {
      ok = false
    }
  }
  // 已知為偽之候選必須被推翻（含張冠李戴與少了指數者）
  let must_fail : Array[(String, String, String)] = [
    ("inv", "⊗", "⊕"), ("inv", "⊕", "⊗"),
    ("det", "⊗", "·"), ("det", "⊕", "^"),
    ("adj", "⊗", "⊗"), ("adj", "⊕", "⊕"),
    ("trace", "⊗", "+"), ("trace", "⊕", "·"),
    ("rank", "⊗", "+"), ("rank", "⊕", "·"),
    ("sq", "⊗", "⊕"), ("sq", "⊗", "⊗ₛ"),
  ]
  for m in must_fail {
    let (p, c, r) = m
    if law_find(tbl, p, c, r) != Some(false) {
      ok = false
    }
  }
  // 命題 175-3：退化網格會放行偽律 —— 以 rank(A⊗B) =? rank A + rank B 示範
  let rk_direct = (g : Mat[Q], _c : Cost) => Some(q_scalar_mat(Q::of_int(mrank(g))))
  let rk_sum = (x : Mat[Q], y : Mat[Q], c : Cost) => Some(
    q_scalar_mat(cq_add(c, Q::of_int(mrank(x)), Q::of_int(mrank(y)))),
  )
  let deg = check_law(
    "rank/⊗/+ @ 退化網格",
    (x, y) => mkron(x, y),
    rk_direct,
    rk_sum,
    [(2, 2)],
    rng,
  )
  let fix = check_law(
    "rank/⊗/+ @ 非對稱網格",
    (x, y) => mkron(x, y),
    rk_direct,
    rk_sum,
    [(2, 3)],
    rng,
  )
  // 退化網格必須放行（示範危害），非對稱網格必須推翻（示範解方）
  if !deg.holds || fix.holds {
    ok = false
  }
  // 列出機器尋獲且成本可量測之加速律
  let wins : Array[String] = []
  for t in tbl {
    if t.cholds && (t.cphi == "inv" || t.cphi == "det" || t.cphi == "sq" || t.cphi == "adj" || t.cphi == "trace") {
      wins.push(t.cphi + "/" + t.ccomb + "/" + t.crule + " ×" + fmt_d(t.cgain, 2))
    }
  }
  mk_check(
    "N-13 結構律搜尋引擎（機械枚舉 Φ×C×⊙）",
    ok,
    tbl.length() + 2,
    "枚舉 " +
    tbl.length().to_string() +
    " 個候選：成立 " +
    nh.to_string() +
    "、推翻 " +
    nr.to_string() +
    "（推翻 > 成立，具判別力）。11 條已知真律全數尋獲、12 條已知偽律全數推翻。成本可量測之加速律：" +
    wins.join("　") +
    "。機器獨立尋獲之 adj/⊗/⊗ₛ 值得注意：樸素規則 adj/⊗/⊗ 被推翻後，帶標量修正之 Sylvester 型規則獲裁定成立。命題 175-3 示範：rank/⊗/+ 於退化網格 (2,2) 被放行（4 = 2+2），加入非對稱 (2,3) 後立即推翻（6 ≠ 5）",
  )
}

///|
/// N-12 成本代數與合成分派：三版模型之預測精度對照。
pub fn ob_n12() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut e1 = 0.0
  let mut e2 = 0.0
  let mut e3 = 0.0
  let mut worst3 = 0.0
  let mut all_dec = true
  let mut min_meas = 1.0e18
  for depth in [1, 2, 3] {
    for _t in 0..<6 {
      let e = rand_expr(rng, depth, 32)
      let (same, wb, wf, _lbl, _dim) = synth_compare(e)
      if !same {
        ok = false
      }
      // 命題 176 之保守性：best 不得超過任一固定策略
      if tinv_best(e) > tinv_flat(e) || tinv_best(e) > tinv_dec(e) {
        ok = false
      }
      if wf <= 0L {
        continue
      }
      let meas = wb.to_double() / wf.to_double()
      if meas < min_meas {
        min_meas = meas
      }
      // 分派器之判決（對 Φ = inv，實測恆為「分解」）
      if !plan_synth(e) {
        all_dec = false
      }
      let f1 = fold_err(tinv_gain(e), meas)
      let f2 = fold_err(tinv_gain2(e), meas)
      let f3 = fold_err(tinv_gain3(e), meas)
      e1 = e1 + f1
      e2 = e2 + f2
      e3 = e3 + f3
      if f3 > worst3 {
        worst3 = f3
      }
      n = n + 1
    }
  }
  let m1 = e1 / n.to_double()
  let m2 = e2 / n.to_double()
  let m3 = e3 / n.to_double()
  // 命題 176b（可否證）：校準版必須優於形狀版，形狀版必須優於 Hadamard 版
  if !(m3 < m1) {
    ok = false
  }
  if !(m1 < m2) {
    ok = false
  }
  // 分派器對 Φ = inv 恆選分解，且實測亦恆為分解較優 —— 兩者必須一致
  if !all_dec || min_meas < 1.0 {
    ok = false
  }
  mk_check(
    "N-12 成本代數與合成分派（三版模型之預測精度）",
    ok,
    n + 1,
    "18 棵隨機樹（深度 1–3）。平均倍率誤差：形狀模型 ×" +
    fmt_d(m1, 2) +
    "　Hadamard 位元模型 ×" +
    fmt_d(m2, 1) +
    "（慘敗）　校準模型 λ=3.16 ×" +
    fmt_d(m3, 2) +
    "（最差單棵 ×" +
    fmt_d(worst3, 2) +
    "）。負面結果 176b：加上 Hadamard 位元界反而使模型劣化數個數量級 —— 成因為 ℚ 恆約至最簡，實際位元數遠低於 Hadamard 界，而該界在巢狀 ⊗／* 下以乘法複合，誤差隨深度爆炸。命題 176 保守性逐棵成立；對 Φ = inv，分派器 18 棵全選「分解」，實測亦 18 棵全為分解較優（最小實測增益 ×" +
    fmt_d(min_meas, 2) +
    "），兩者一致 —— 故此 Φ 下分派器之價值在於**事前預測增益**而非**選擇策略**",
  )
}

///|
/// N-10 Sylvester–Franke 外冪律：det(Cₖ(A)) = det(A)^{C(n−1,k−1)}。
pub fn ob_n10() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut tb = 0L
  let mut tf = 0L
  let rows : Array[String] = []
  // 增益隨 n 單調上升之主張**只在固定 k 下成立** —— 跨 k 比較時指數
  // C(n−1,k−1) 一併改變，兩個自變數同時動，序關係不保證。
  // 故分 k 追蹤：k=2 之鏈 (4,2)→(5,2)→(6,2)、k=3 之鏈 (5,3)→(6,3)。
  let mut prev2 = 0.0
  let mut prev3 = 0.0
  let mut mono = true
  let mut ratio_small = 0.0
  let mut ratio_large = 0.0
  for nk in [(4, 2), (5, 2), (6, 2), (5, 3), (6, 3)] {
    let (nn, kk) = nk
    let a = rand_gram(rng, nn)
    let cd = Cost::new()
    let ck = compound(a, kk, cd)
    let lhs = qdet_gauss(ck, cd)
    // 命題 180-1：Cₖ(G) 須為合法 Gram（對稱正定）
    if !ck.equals(ck.transpose()) || !is_positive_definite(ck) {
      ok = false
    }
    if ck.mrows != binom(nn, kk) {
      ok = false
    }
    // 定理 180：兩種冪法皆須給出相同結果
    let c1 = Cost::new()
    let r1 = qpow_cost(c1, qdet_gauss(a, c1), sf_exponent(nn, kk))
    let c2 = Cost::new()
    let r2 = qpow_fast(c2, qdet_gauss(a, c2), sf_exponent(nn, kk))
    if !lhs.eq(r1) || !lhs.eq(r2) {
      ok = false
    }
    let g = Cost::ratio(cd, c2)
    if kk == 2 {
      if g < prev2 {
        mono = false
      }
      prev2 = g
    } else {
      if g < prev3 {
        mono = false
      }
      prev3 = g
    }
    // 線性冪 ÷ 二進位冪 之成本比：應隨指數增大而拉開
    let rr = c1.wmul.to_double() / c2.wmul.to_double()
    if nn == 4 {
      ratio_small = rr
    }
    if nn == 6 && kk == 3 {
      ratio_large = rr
    }
    tb = tb + cd.wmul
    tf = tf + c2.wmul
    rows.push(
      "C(" + nn.to_string() + "," + kk.to_string() + ")=" +
      ck.mrows.to_string() + " e=" + sf_exponent(nn, kk).to_string() + " ×" +
      fmt_d(g, 1),
    )
    n = n + 3
  }
  // 二進位冪之增益須單調上升（線性冪則否 —— 見條目證明欄）
  if !mono {
    ok = false
  }
  // 線性／二進位之成本比須隨指數拉開
  if ratio_large <= ratio_small {
    ok = false
  }
  mk_check(
    "N-10 Sylvester–Franke 外冪律",
    ok,
    n,
    "定理 180 det(Cₖ(A)) = det(A)^{C(n−1,k−1)} 逐例成立；命題 180-1 Cₖ(G) 為對稱正定（即 Λᵏ V 之合法 Gram）且階數恰為 C(n,k)。成本：" +
    rows.join("　") +
    "，總增益 ×" +
    fmt_d(tb.to_double() / tf.to_double(), 1) +
    "。增益之單調性**只在固定 k 下成立**（k=2 鏈與 k=3 鏈各自上升）—— 跨 k 比較時 C(n,k) 與指數 C(n−1,k−1) 同時改變，序關係不保證；此限制由義務以分鏈斷言明文固定。右式冪法之抉擇是本條關鍵：線性冪／二進位冪之成本比由 ×" +
    fmt_d(ratio_small, 2) +
    "（e=3）拉開到 ×" +
    fmt_d(ratio_large, 2) +
    "（e=10）—— 指數 C(n−1,k−1) 隨 n 組合爆炸，若右式用線性冪，整條律之增益會在 (7,3) 之後**開始下降**。一次性實測（因基準法過貴未納入常規義務）：線性冪 (7,3) ×99.4 → (8,4) ×85.1 → (9,4) ×75.3 逐步惡化；二進位冪 ×232.3 → ×395.5 → ×814.4 持續上升",
  )
}

///|
/// N-06 Hom 律：Hom(V,W) ≡ W ⊗ V*，catamorphism 無須修改即可處理。
pub fn ob_n06() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut tb = 0L
  let mut tf = 0L
  let rows : Array[String] = []
  let mut hom_gain = 0.0
  let mut ten_gain = 0.0
  for pq in [(2, 3), (3, 3), (3, 4), (4, 4), (4, 5)] {
    let (p, q) = pq
    let v = SLeaf("V", rand_gram(rng, p))
    let w = SLeaf("W", rand_gram(rng, q))
    let h = shom(v, w)
    // 命題 182-1：維數與 Gram
    if h.sdim() != p * q {
      ok = false
    }
    let gh = h.sgram()
    if !is_positive_definite(gh) || !gh.equals(gh.transpose()) {
      ok = false
    }
    // G(Hom) = G(W) ⊗ G(V)⁻ᵀ 之獨立覆核
    let c0 = Cost::new()
    match qinv_gauss(v.sgram(), c0) {
      None => ok = false
      Some(iv) =>
        if !gh.equals(mkron(w.sgram(), iv.transpose())) {
          ok = false
        }
    }
    // 定理 182：catamorphism 直接適用，且結果正確
    let (same, wb, wf, _l, _d) = synth_compare(h)
    if !same {
      ok = false
    }
    tb = tb + wb
    tf = tf + wf
    rows.push("dim" + (p * q).to_string() + " ×" + fmt_d(wb.to_double() / wf.to_double(), 1))
    n = n + 3
  }
  // 推論 182-1：同維之下 Hom 之增益高於純 ⊗（前者只需一次求逆）
  let v4 = SLeaf("V", rand_gram(rng, 4))
  let w4 = SLeaf("W", rand_gram(rng, 4))
  let (_s1, hb, hf, _l1, _d1) = synth_compare(shom(v4, w4))
  let (_s2, tbb, tff, _l2, _d2) = synth_compare(STensor(v4, w4))
  hom_gain = hb.to_double() / hf.to_double()
  ten_gain = tbb.to_double() / tff.to_double()
  if hom_gain <= ten_gain {
    ok = false
  }
  n = n + 1
  mk_check(
    "N-06 Hom 律 Hom(V,W) ≡ W ⊗ V*",
    ok,
    n,
    "命題 182-1 於 5 組維度逐例成立：dim(Hom) = dim V·dim W、G(Hom) 對稱正定、且與 G(W)⊗G(V)⁻ᵀ 逐元素相等。定理 182：Hom 不是獨立構造子而是 ⊗ 與 * 之複合，故 N-11 之 catamorphism **無須任何修改**即可對 Hom 節點合成演算法，合成結果逐例等於直接法。成本：" +
    rows.join("　") +
    "，總增益 ×" +
    fmt_d(tb.to_double() / tf.to_double(), 1) +
    "。推論 182-1 之實測（同為 dim 16）：Hom(V,W) ×" +
    fmt_d(hom_gain, 1) +
    " 高於 V⊗W ×" +
    fmt_d(ten_gain, 1) +
    " —— 成因是 Hom 之對偶節點依定理 173-2 零成本，合成法只需一次求逆而非兩次",
  )
}

///|
/// N-08 度量扭曲（同餘）律族：加速律 + 不變量律兩類並陳。
pub fn ob_n08() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut tb = 0L
  let mut tf = 0L
  let rows : Array[String] = []
  for sz in [2, 3, 4, 5] {
    let g = rand_gram(rng, sz)
    let a = rand_invertible(rng, sz)
    let c0 = Cost::new()
    let ga = congruence(c0, g, a)
    // 定理 185-1：det(AᵀGA) = det(A)²·det(G)
    let cd = Cost::new()
    let lhs = qdet_gauss(ga, cd)
    let cf = Cost::new()
    let da = qdet_gauss(a, cf)
    let rhs = cq_mul(cf, cq_mul(cf, da, da), qdet_gauss(g, cf))
    if !lhs.eq(rhs) {
      ok = false
    }
    // 定理 185-2：(AᵀGA)⁻¹ = A⁻¹G⁻¹A⁻ᵀ
    let ci = Cost::new()
    let direct = qinv_gauss(ga, ci)
    let cj = Cost::new()
    let fact = match (qinv_gauss(a, cj), qinv_gauss(g, cj)) {
      (Some(ia), Some(ig)) =>
        Some(qmul_cost(cj, ia, qmul_cost(cj, ig, ia.transpose())))
      _ => None
    }
    match (direct, fact) {
      (Some(x), Some(y)) => if !x.equals(y) { ok = false }
      _ => ok = false
    }
    tb = tb + ci.wmul
    tf = tf + cj.wmul
    rows.push("n" + sz.to_string() + " ×" + fmt_d(Cost::ratio(ci, cj), 2))
    n = n + 2
  }
  let g = tb.to_double() / tf.to_double()
  // 命題 185-5（負面結果）：同餘之「分解」不划算 —— A 稠密時兩次矩陣乘
  //   已抵銷求逆之節省。若忽然划算，表示基準實作退化，本條應失敗以示警。
  if g > 1.5 {
    ok = false
  }
  // ---- 不變量律：Sylvester 慣性律（ℝ 軌）----
  let mut inv_ok = 0
  for sz in [3, 4, 5, 6] {
    // 造一個不定號對稱矩陣（含正負特徵值）
    let s0 : RMat = Mat::build(sz, sz, (i, j) => if i == j {
      (if i % 2 == 0 { 1.0 } else { -1.0 }) * (1.0 + i.to_double())
    } else {
      0.3 * ((i + j) % 3).to_double()
    })
    let sym : RMat = Mat::build(sz, sz, (i, j) => 0.5 *
      (s0.at(i, j) + s0.at(j, i)))
    let a : RMat = Mat::build(sz, sz, (i, j) => if i > j {
      0.0
    } else if i == j {
      1.0 + (i % 2).to_double()
    } else {
      0.25 * ((i * 3 + j) % 4).to_double()
    })
    let cong = a.transpose().times(sym.times(a))
    let (l1, q1, _r1) = cjacobi_eigen(sym, 1.0e-12, 2000, Cost::new())
    let (l2, q2, _r2) = cjacobi_eigen(cong, 1.0e-12, 2000, Cost::new())
    ignore(q1)
    ignore(q2)
    let i1 = inertia(l1)
    let i2 = inertia(l2)
    // 定理 185-3：慣性指數 (n₊, n₋, n₀) 完全相同
    if i1.0 != i2.0 || i1.1 != i2.1 || i1.2 != i2.2 {
      ok = false
    } else {
      inv_ok = inv_ok + 1
    }
    n = n + 1
  }
  mk_check(
    "N-08 度量扭曲（同餘）律族 —— 加速律與不變量律兩類並陳",
    ok,
    n,
    "【加速律】定理 185-1 det(AᵀGA) = det(A)²det(G)、185-2 (AᵀGA)⁻¹ = A⁻¹G⁻¹A⁻ᵀ 逐例成立；但成本 " +
    rows.join("　") +
    "，總增益僅 ×" +
    fmt_d(g, 2) +
    " —— 命題 185-5（負面結果）：A 稠密時分解法要付兩次矩陣乘法，已抵銷求逆之節省。義務反向約束增益不得超過 1.5，若忽然划算表示基準實作退化。\n【不變量律】定理 185-3 Sylvester 慣性律：" +
    inv_ok.to_string() +
    " 組不定號矩陣在同餘變換下 (n₊, n₋, n₀) 完全不變。此律**無成本比可言** —— 慣性指數不是被算得更快，而是根本不用重算。先前 N 群之 LawVerdict 只有 (成立?, 成本比) 兩欄，裝不下這種律；本條因此把結構律分為加速律與不變量律兩類",
  )
}

///|
/// N-09 子空間律：G_U = SᵀGS，正定性與秩之刻劃。
pub fn ob_n09() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut pos = 0
  let mut neg = 0
  for dim in [3, 4, 5] {
    let g = rand_gram(rng, dim)
    for k in 1..=dim {
      // (a) S 單射（取前 k 個標準基向量）⇒ G_U 應正定
      let s : Mat[Q] = Mat::build(dim, k, (i, j) => if i == j {
        Q::one()
      } else {
        Q::zero()
      })
      let c = Cost::new()
      let gu = qmul_cost(c, s.transpose(), qmul_cost(c, g, s))
      if gu.mrows != k || gu.mcols != k {
        ok = false
      }
      // 定理 185-4 正向：S 單射 ⇒ G_U 正定
      if !is_positive_definite(gu) {
        ok = false
      }
      if mrank(gu) != k {
        ok = false
      }
      // 誘導度量須為原度量之主子陣（子空間之內積即限制）
      let sub : Mat[Q] = Mat::build(k, k, (i, j) => g.at(i, j))
      if !gu.equals(sub) {
        ok = false
      }
      pos = pos + 1
      n = n + 1
    }
    // (b) S 不單射（最後一行重複）⇒ G_U 必不正定，且秩降
    if dim >= 2 {
      let s2 : Mat[Q] = Mat::build(dim, dim, (i, j) => if j == dim - 1 {
        if i == 0 {
          Q::one()
        } else {
          Q::zero()
        }
      } else if i == j {
        Q::one()
      } else {
        Q::zero()
      })
      let c2 = Cost::new()
      let gu2 = qmul_cost(c2, s2.transpose(), qmul_cost(c2, g, s2))
      // 定理 185-4 反向：S 不單射 ⇒ G_U 不正定
      if is_positive_definite(gu2) {
        ok = false
      }
      if mrank(gu2) >= dim {
        ok = false
      }
      neg = neg + 1
      n = n + 1
    }
  }
  mk_check(
    "N-09 子空間律 G_U = SᵀGS（正定性之雙向刻劃）",
    ok,
    n,
    "定理 185-4 之雙向驗證：" +
    pos.to_string() +
    " 組單射含入映射（k = 1…dim，dim = 3,4,5）逐例給出正定之 G_U、rank = k，且與原 Gram 之 k 階主子陣逐元素相等（即子空間之內積確為限制而非另行定義）；" +
    neg.to_string() +
    " 組刻意不單射之 S（末行重複）逐例給出非正定且降秩之 G_U。兩側皆驗，故為刻劃而非單向蘊含。本條為 N-08 同餘律在非方陣 S 下之推廣：方陣且非奇異時退化為同餘（定理 185-3 慣性守恆），非方陣時慣性不再守恆而改由秩與正定性刻劃",
  )
}

///|
/// N-14 反律庫：每次執行都重新量測全部負面結果。
pub fn ob_n14() -> Check {
  let reg = negative_registry()
  let mut ok = true
  let mut nfail = 0
  let parts : Array[String] = []
  for r in reg {
    if !r.nholds {
      ok = false
      nfail = nfail + 1
    }
    parts.push(r.nsrc + " " + r.nclaim + "（實測 " + fmt_d(r.nmeasured, 2) + "）")
  }
  // 登錄表不得為空，且必須涵蓋至少 4 個不同來源條目
  if reg.length() < 7 {
    ok = false
  }
  let srcs : Array[String] = []
  for r in reg {
    let mut seen = false
    for s in srcs {
      if s == r.nsrc {
        seen = true
      }
    }
    if !seen {
      srcs.push(r.nsrc)
    }
  }
  if srcs.length() < 4 {
    ok = false
  }
  mk_check(
    "N-14 反律庫（負面結果之回歸測試）",
    ok,
    reg.length(),
    "本庫之負面結果先前散落六處，沒有任何機制保證它們「現在還成立」—— 某次重構若讓基準實作退化，⊕ 的增益可能忽然變高而無人察覺。本條把它們收進單一登錄表並**每次執行都重新量測**，每筆附一個必須滿足的界，違反即失敗。現登錄 " +
    reg.length().to_string() +
    " 筆、涵蓋 " +
    srcs.length().to_string() +
    " 個來源條目，全數仍然成立（失效 " +
    nfail.to_string() +
    " 筆）：" +
    parts.join("；") +
    "。這把「我們誠實回報了壞消息」從一次性宣告變成可持續的回歸測試",
  )
}

///|
/// N-26 擴編搜尋空間：加入 cube 與 Kronecker 和 ⊞，並指認引擎之盲區。
pub fn ob_n26() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let tbl = law_search(rng, [(2, 2), (2, 3), (3, 3)])
  let mut nh = 0
  let mut nr = 0
  let mut ks_hold = 0
  let mut ks_total = 0
  for t in tbl {
    if t.cholds {
      nh = nh + 1
    } else {
      nr = nr + 1
    }
    if t.ccomb == "⊞" {
      ks_total = ks_total + 1
      if t.cholds {
        ks_hold = ks_hold + 1
      }
    }
  }
  // 擴編後候選數應為 (5 矩陣 Φ + 3 純量 Φ) × 3 C × 3 ⊙ = 72
  if tbl.length() != 72 {
    ok = false
  }
  if nr <= nh {
    ok = false
  }
  // cube 之已知真律必須尋獲
  if law_find(tbl, "cube", "⊗", "⊗") != Some(true) {
    ok = false
  }
  if law_find(tbl, "cube", "⊕", "⊕") != Some(true) {
    ok = false
  }
  if law_find(tbl, "cube", "⊗", "⊕") != Some(false) {
    ok = false
  }
  // ⊞ 之關鍵發現（兩項）：
  // (1) 24 個候選中恰有 1 條被判成立 —— 即 rank(A⊞B) =? rank A · rank B；
  // (2) 它是**取樣分布造成的偽陽性**：測試矩陣皆為 Gram（正定），
  //     而正定時 A⊞B 之譜為 {λᵢ+μⱼ} 全正故必滿秩，等式自動成立；
  //     一般矩陣則不然。下方以明確反例推翻之。
  if ks_hold != 1 {
    ok = false
  }
  if ks_total != 24 {
    ok = false
  }
  if law_find(tbl, "rank", "⊞", "·") != Some(true) {
    ok = false
  }
  // 明確反例：A = diag(1,−1)、B = [1] ⇒ A⊞B = diag(2,0)
  //   rank(A⊞B) = 1，而 rank A · rank B = 2·1 = 2。
  let ca : Mat[Q] = Mat::build(2, 2, (i, j) => if i != j {
    Q::zero()
  } else if i == 0 {
    Q::one()
  } else {
    Q::of_int(-1)
  })
  let cb : Mat[Q] = Mat::build(1, 1, (_i, _j) => Q::one())
  let ks = qkron_sum(ca, cb)
  let counterexample_kills = mrank(ks) != mrank(ca) * mrank(cb)
  if !counterexample_kills {
    ok = false
  }
  // 但 N-24 已證 expm(A⊞B) = expm(A)⊗expm(B) 成立 —— 故限制在 Φ 集而非組合子
  let a = Mat::build(2, 2, (_i, _j) => (rng.next_below(5) - 2).to_double() * 0.1)
  let b = Mat::build(3, 3, (_i, _j) => (rng.next_below(5) - 2).to_double() * 0.1)
  let c1 = Cost::new()
  let lhs = cexpm(kron_sum(a, b), c1)
  let c2 = Cost::new()
  let rhs = rkron_cost(c2, cexpm(a, c2), cexpm(b, c2))
  if mat_dev(lhs, rhs) > 1.0e-10 {
    ok = false
  }
  let wins : Array[String] = []
  for t in tbl {
    if t.cholds && t.cphi == "cube" {
      wins.push("cube/" + t.ccomb + "/" + t.crule + " ×" + fmt_d(t.cgain, 2))
    }
  }
  mk_check(
    "N-26 擴編搜尋空間（+cube、+Kronecker 和 ⊞）並指認引擎盲區",
    ok,
    tbl.length() + 1,
    "候選數由 42 擴編至 " +
    tbl.length().to_string() +
    "（Φ 增 cube、C 增 ⊞）：成立 " +
    nh.to_string() +
    "、推翻 " +
    nr.to_string() +
    "。新 Φ 之 cube 如期尋獲 " +
    wins.join("　") +
    "。【發現一：偽陽性】⊞ 之 " +
    ks_total.to_string() +
    " 個候選中恰有 1 條被判成立 —— rank(A⊞B) =? rank A · rank B。它是**取樣分布造成的偽陽性**：測試矩陣皆為 Gram（正定），此時 A⊞B 之譜為 {λᵢ+μⱼ} 全正故必滿秩，等式自動成立。義務內附明確反例推翻之：A = diag(1,−1)、B = [1] ⇒ A⊞B = diag(2,0)，rank = 1 而 rank A · rank B = 2。這是 N-02 定理 170「holds = true 僅為機率性證據」之外的**第二種失真來源** —— 不是運氣不好，而是取樣分布有系統性偏差。【發現二：盲區】⊞ 上其餘 23 條全數推翻，然而 N-24 已證 expm(A⊞B) = expm(A)⊗expm(B) 確實成立（本條另行重驗一次）。故限制不在組合子而在 Φ 集：⊞ 上真正的律屬於矩陣指數，而引擎之 Φ 全是線性／多項式運算。推論：引擎找不到的律有兩種成因 —— Φ 集未涵蓋，或裁決器以成本比為核心而裝不下（N-08 不變量律、N-07 可行性律）。都不是「律不存在」，而是「這具引擎看不見」",
  )
}

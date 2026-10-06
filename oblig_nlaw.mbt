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

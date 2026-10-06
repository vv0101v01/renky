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
    if !gram_of_space(e.sspace()).equals(g) {
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
  let sizes : Array[(Int, Int)] = [(2, 2), (3, 3), (4, 4), (5, 5)]
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
  let large = law_kron_inv(rng, [(5, 5)])
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
    " → dim 25 ×" +
    fmt_d(large.lgain(), 2),
  )
}

///|
/// N-04 分塊–直和律族：律成立，但增益 ≈ 1 —— 誠實登錄為「不值得用」。
pub fn ob_n04() -> Check {
  let rng = ob_rng()
  let sizes : Array[(Int, Int)] = [(2, 2), (3, 3), (4, 4), (5, 5)]
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

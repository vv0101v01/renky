// ============================================================================
//  檔案 20：nlaw.mbt — N 群骨架：結構律與演算法合成
//
//  本檔實作「演算法生成器」之核心機制。其出發點是一個觀察：
//
//    把既有演算法跑在組合空間上，得到的是既有演算法的「新實例」，不是新演算法。
//    真正會生出新演算法的，是演算法 Φ 與組合子 C 之間的「交換律」：
//
//              Φ( C(V, W) )  ≡  Φ(V) ⊙ Φ(W)
//              └─ 直接法 ─┘      └─── 分解法 ───┘
//
//    左式在 dim = dim V · dim W 上硬跑；右式在兩個小空間各跑一次再合成。
//    等式成立且右式便宜 ⇒ 這就是一條新的快速演算法。
//
//  關鍵設計原則（由 ⊕ 之實測反例導出）：
//    定律成立 ≠ 值得用。檢驗器必須「同時」驗證正確性與量測成本。
//    只驗正確性的生成器，會產出一大批真的但沒人需要的恆等式
//    —— 這正是 L-05／L-08 掛在加速層卻從未加速的同一種錯誤。
//
//  N-01 空間表達式與其求值
//  N-02 結構律之形式定義與自然性檢驗器（高階：吃演算法、吐判決）
//  N-03 Kronecker–Gram 律族（⊗）
//  N-04 分塊–直和律族（⊕，含「成立但不划算」之誠實登錄）
// ============================================================================

// ---------------------------------------------------------------------------
// 【演算法 169】空間表達式（N-01）
//
// 定義：空間表達式之文法
//     E ::= Leaf(name, G) | E ⊗ E | E ⊕ E | E*
//   其中 Leaf 攜帶該葉空間之 Gram 矩陣 G（正定對稱）。
//
// 命題 169-1（維數）：dim(A⊗B) = dim A · dim B；dim(A⊕B) = dim A + dim B；
//   dim(A*) = dim A。
//   證明：張量積之基底為 {bᵢ⊗cⱼ}（積基底），直和之基底為兩基底之不交併，
//   對偶空間與原空間同構（有限維）。∎
//
// 命題 169-2（Gram 之遞迴）：
//     G(A⊗B) = G(A) ⊗ G(B)      （Kronecker 積）
//     G(A⊕B) = diag(G(A), G(B)) （分塊對角）
//     G(A*)  = (G(A)⁻¹)ᵀ
//   證明：⊗ 之內積定義為 ⟨x₁⊗x₂, y₁⊗y₂⟩ = ⟨x₁,y₁⟩⟨x₂,y₂⟩，
//   取積基底即得 Kronecker 積。⊕ 為正交直和，跨分量內積為 0。
//   對偶空間以 Riesz 同構賦予內積，其 Gram 為原 Gram 之逆（再轉置）。∎
//
// 定理 169（良構性）：若所有葉之 G 正定，則任意表達式之 Gram 皆正定。
//   證明：對結構歸納。⊗：Kronecker 積之特徵值為 λᵢμⱼ，兩組皆正 ⇒ 全正。
//   ⊕：分塊對角之譜為兩分塊譜之併。*：正定矩陣之逆正定，轉置保持正定。∎
// ---------------------------------------------------------------------------

///|
/// 空間表達式（N-01）
pub enum SpaceExpr {
  /// 葉：名稱 + Gram 矩陣
  SLeaf(String, Mat[Q])
  /// 張量積 A ⊗ B
  STensor(SpaceExpr, SpaceExpr)
  /// 正交直和 A ⊕ B
  SSum(SpaceExpr, SpaceExpr)
  /// 對偶 A*
  SDual(SpaceExpr)
}

///|
/// 分塊對角 diag(A, B)
pub fn qblock_diag(a : Mat[Q], b : Mat[Q]) -> Mat[Q] {
  let ra = a.mrows
  let ca = a.mcols
  Mat::build(ra + b.mrows, ca + b.mcols, (i, j) => if i < ra && j < ca {
    a.at(i, j)
  } else if i >= ra && j >= ca {
    b.at(i - ra, j - ca)
  } else {
    Q::zero()
  })
}

///|
/// 維數（命題 169-1）
pub fn SpaceExpr::sdim(self : SpaceExpr) -> Int {
  match self {
    SLeaf(_, g) => g.mrows
    STensor(a, b) => a.sdim() * b.sdim()
    SSum(a, b) => a.sdim() + b.sdim()
    SDual(a) => a.sdim()
  }
}

///|
/// 表達式之 Gram 矩陣（命題 169-2）
pub fn SpaceExpr::sgram(self : SpaceExpr) -> Mat[Q] {
  match self {
    SLeaf(_, g) => g
    STensor(a, b) => mkron(a.sgram(), b.sgram())
    SSum(a, b) => qblock_diag(a.sgram(), b.sgram())
    SDual(a) => {
      let g = a.sgram()
      let c = Cost::new()
      match qinv_gauss(g, c) {
        Some(h) => h.transpose()
        // 定理 169 保證不可能到達此分支（正定 ⇒ 可逆）
        None => Mat::ident(g.mrows)
      }
    }
  }
}

///|
/// 可讀標籤
pub fn SpaceExpr::slabel(self : SpaceExpr) -> String {
  match self {
    SLeaf(nm, _) => nm
    STensor(a, b) => "(" + a.slabel() + "⊗" + b.slabel() + ")"
    SSum(a, b) => "(" + a.slabel() + "⊕" + b.slabel() + ")"
    SDual(a) => a.slabel() + "*"
  }
}

///|
/// 表達式之深度（合成樹之高度）
pub fn SpaceExpr::sdepth(self : SpaceExpr) -> Int {
  match self {
    SLeaf(_, _) => 0
    STensor(a, b) => 1 + maxi(a.sdepth(), b.sdepth())
    SSum(a, b) => 1 + maxi(a.sdepth(), b.sdepth())
    SDual(a) => 1 + a.sdepth()
  }
}

///|
/// 由表達式產生可直接使用之內積空間（座標表示）
pub fn SpaceExpr::sspace(self : SpaceExpr) -> IPSpace[Array[Q], Q] {
  coord_ipspace(self.slabel(), self.sdim(), Some(self.sgram()))
}

///|
/// 隨機正定 Gram：取可逆 M，G = MᵀM（必正定）
pub fn rand_gram(rng : Rng, n : Int) -> Mat[Q] {
  for _t in 0..<80 {
    let m : Mat[Q] = Mat::build(n, n, (_i, _j) => Q::frac(
      rng.next_small(5),
      rng.next_range(1, 4),
    ))
    if !Q::is_zero(mdet(m)) {
      return m.transpose().times(m)
    }
  }
  Mat::ident(n)
}

// ---------------------------------------------------------------------------
// 【演算法 170】結構律與自然性檢驗器（N-02）
//
// 定義（結構律）：一條結構律是一個四元組 (Φ, C, ⊙, 條件)，其斷言為
//     ∀ A, B 滿足條件：  Φ(C(A, B)) = Φ(A) ⊙ Φ(B)
//   其中 C 為組合子（作用於 Gram 矩陣），Φ 為演算法，⊙ 為合成子。
//
// 定義（判決）：LawVerdict 記錄四件事 ——
//   (i) 是否逐例成立；(ii) 試驗數；(iii) 直接法成本；(iv) 分解法成本。
//   成本以 Cost 確定性模型（字乘法次數）計量，與平台無關。
//
// 命題 170（為何必須同時量測成本）：
//   存在成立但無價值之結構律。實測：⊕ 之求逆律逐例成立，
//   但增益僅 ×1.1–1.2 —— 因為 Gauss–Jordan 遇零乘數本就跳過，
//   通用演算法已「不小心」吃掉分塊結構之紅利。
//   故「成立」不蘊含「值得用」，檢驗器必須回報兩者。∎
//
// 定理 170（檢驗器之可靠性，單向）：
//   若 check_law 回報 holds = false，則該律確實為偽（有具體反例）。
//   反之 holds = true 僅為機率性證據：律為偽而 t 次隨機試驗全部通過之
//   機率，依 Schwartz–Zippel 於取樣集 S 上受 (deg/|S|)^t 控制。
//   本檔預設 |S| ≥ 20、t ≥ 6，供快速篩選；確定性結論須另附代數證明
//   （N-03 之三條律皆已附，見下）。∎
// ---------------------------------------------------------------------------

///|
/// 一條結構律之判決
pub struct LawVerdict {
  /// 律之名稱
  lname : String
  /// 是否逐例成立
  holds : Bool
  /// 試驗數
  ltrials : Int
  /// 直接法之字乘法總數
  base_wmul : Int64
  /// 分解法之字乘法總數
  fast_wmul : Int64
  /// 逐尺寸之增益明細
  ldetail : String
}

///|
/// 增益 = 直接法成本 / 分解法成本
pub fn LawVerdict::lgain(self : LawVerdict) -> Double {
  if self.fast_wmul <= 0L {
    0.0
  } else {
    self.base_wmul.to_double() / self.fast_wmul.to_double()
  }
}

///|
/// 【高階】結構律檢驗器（N-02）
///
/// 參數皆為函式 —— 這是本檔之所以稱「高階」的原因：
///   comb   組合子 C：由兩個 Gram 造出合成空間之 Gram
///   direct 直接法 Φ：於合成矩陣上運行（成本記入 Cost）
///   fact   分解法 Φ(A) ⊙ Φ(B)：於兩個因子上各運行一次再合成
///
/// 回報「是否成立」與「成本比」兩者；缺一不可（命題 170）。
pub fn check_law(
  lname : String,
  comb : (Mat[Q], Mat[Q]) -> Mat[Q],
  direct : (Mat[Q], Cost) -> Mat[Q]?,
  fact : (Mat[Q], Mat[Q], Cost) -> Mat[Q]?,
  sizes : Array[(Int, Int)],
  rng : Rng,
) -> LawVerdict {
  let mut holds = true
  let mut tb = 0L
  let mut tf = 0L
  let parts : Array[String] = []
  for sz in sizes {
    let (n, m) = sz
    let a = rand_gram(rng, n)
    let b = rand_gram(rng, m)
    let cd = Cost::new()
    let lhs = direct(comb(a, b), cd)
    let cf = Cost::new()
    let rhs = fact(a, b, cf)
    let same = match (lhs, rhs) {
      (Some(x), Some(y)) => x.equals(y)
      (None, None) => true
      _ => false
    }
    if !same {
      holds = false
    }
    tb = tb + cd.wmul
    tf = tf + cf.wmul
    parts.push(
      n.to_string() +
      "×" +
      m.to_string() +
      "→dim" +
      (n * m).to_string() +
      " ×" +
      fmt_d(Cost::ratio(cd, cf), 2),
    )
  }
  {
    lname,
    holds,
    ltrials: sizes.length(),
    base_wmul: tb,
    fast_wmul: tf,
    ldetail: parts.join("　"),
  }
}

///|
/// 把純量包成 1×1 矩陣，使 det 類演算法可納入同一檢驗器
pub fn q_scalar_mat(x : Q) -> Mat[Q] {
  Mat::build(1, 1, (_i, _j) => x)
}

// ---------------------------------------------------------------------------
// 【演算法 171】Kronecker–Gram 律族（N-03）
//
// 設 A（n×n）、B（m×m）皆可逆。以下三律成立：
//
// 定理 171-1（Gram 律，結構性）：G(V⊗W) = G(V) ⊗ G(W)。
//   證明：⟨bᵢ⊗cₖ, bⱼ⊗c_l⟩ = ⟨bᵢ,bⱼ⟩⟨cₖ,c_l⟩ = G(V)_{ij} G(W)_{kl}，
//   而 Kronecker 積之 ((i,k),(j,l)) 元恰為此值。∎
//
// 定理 171-2（求逆律）：(A ⊗ B)⁻¹ = A⁻¹ ⊗ B⁻¹。
//   證明：(A⊗B)(A⁻¹⊗B⁻¹) = (AA⁻¹)⊗(BB⁻¹) = I_n ⊗ I_m = I_{nm}，
//   用到混合積性質 (A⊗B)(C⊗D) = (AC)⊗(BD)。由逆之唯一性得證。∎
//
// 定理 171-3（行列式律）：det(A ⊗ B) = (det A)^m · (det B)^n。
//   證明：A⊗B = (A⊗I_m)(I_n⊗B)。det(A⊗I_m) = (det A)^m（分塊化為 m 份），
//   det(I_n⊗B) = (det B)^n。相乘即得。∎
//
// 成本（命題 171-4）：直接法於 nm 階矩陣上為 Θ((nm)³)；
//   分解法為 Θ(n³ + m³) 加 Θ((nm)²) 之組裝。
//   故漸近增益為 Θ((nm)³ / (n³+m³))，當 n = m 時為 Θ(n³) —— 無上界。
//   實測（精確 ℚ，隨機非標準基底）：
//     求逆 dim 9 ×7.4、dim 25 ×37.9、dim 64 ×150.3
//     行列式 dim 9 ×9.5、dim 25 ×51.4、dim 64 ×148.5
// ---------------------------------------------------------------------------

///|
/// N-03 求逆律：inv(A⊗B) = inv(A)⊗inv(B)
pub fn law_kron_inv(rng : Rng, sizes : Array[(Int, Int)]) -> LawVerdict {
  check_law(
    "⊗ 求逆律 inv(A⊗B) = inv(A)⊗inv(B)",
    (a, b) => mkron(a, b),
    (g, c) => qinv_gauss(g, c),
    (a, b, c) => match (qinv_gauss(a, c), qinv_gauss(b, c)) {
      (Some(x), Some(y)) => Some(qkron_cost(c, x, y))
      _ => None
    },
    sizes,
    rng,
  )
}

///|
/// 計入成本之 Kronecker 組裝（分解法必須誠實計入組裝開銷）
pub fn qkron_cost(c : Cost, a : Mat[Q], b : Mat[Q]) -> Mat[Q] {
  let rb = b.mrows
  let cb = b.mcols
  Mat::build(a.mrows * rb, a.mcols * cb, (i, j) => cq_mul(
    c,
    a.at(i / rb, j / cb),
    b.at(i % rb, j % cb),
  ))
}

///|
/// N-03 行列式律：det(A⊗B) = det(A)^m · det(B)^n
pub fn law_kron_det(rng : Rng, sizes : Array[(Int, Int)]) -> LawVerdict {
  check_law(
    "⊗ 行列式律 det(A⊗B) = det(A)^m·det(B)^n",
    (a, b) => mkron(a, b),
    (g, c) => Some(q_scalar_mat(qdet_gauss(g, c))),
    (a, b, c) => {
      let n = a.mrows
      let m = b.mrows
      let da = qdet_gauss(a, c)
      let db = qdet_gauss(b, c)
      let mut acc = Q::one()
      for _k in 0..<m {
        acc = cq_mul(c, acc, da)
      }
      for _k in 0..<n {
        acc = cq_mul(c, acc, db)
      }
      Some(q_scalar_mat(acc))
    },
    sizes,
    rng,
  )
}

///|
/// N-03 Gram 律（結構性）：由表達式求得之 Gram 必等於 Kronecker 積
pub fn law_kron_gram(rng : Rng, sizes : Array[(Int, Int)]) -> Bool {
  let mut ok = true
  for sz in sizes {
    let (n, m) = sz
    let ga = rand_gram(rng, n)
    let gb = rand_gram(rng, m)
    let e = STensor(SLeaf("A", ga), SLeaf("B", gb))
    if !e.sgram().equals(mkron(ga, gb)) {
      ok = false
    }
    if e.sdim() != n * m {
      ok = false
    }
    // 定理 169：合成之 Gram 仍正定
    if !is_positive_definite(e.sgram()) {
      ok = false
    }
  }
  ok
}

// ---------------------------------------------------------------------------
// 【演算法 172】分塊–直和律族（N-04）—— 成立但不划算之誠實登錄
//
// 定理 172-1（分塊求逆律）：diag(A,B)⁻¹ = diag(A⁻¹, B⁻¹)。
//   證明：diag(A,B)·diag(A⁻¹,B⁻¹) = diag(AA⁻¹, BB⁻¹) = I。∎
// 定理 172-2（分塊行列式律）：det diag(A,B) = det A · det B。
//   證明：對第一分塊作 Laplace 展開，或由 LU 分解之分塊形式直接得出。∎
//
// 命題 172-3（負面結果，本條之主張）：
//   上述兩律雖成立，卻幾乎沒有價值 —— 實測增益僅 ×1.1～×1.2。
//   成因：Gauss–Jordan 於零乘數處本就跳過運算，
//   故通用演算法在分塊對角輸入上已自動退化為分塊演算法，
//   紅利早已被吃掉，顯式分解無新增可省之處。
//
// 推論 172（生成器之設計準則）：
//   結構律之價值 = 正確性 × 成本改善。只驗正確性的搜尋器
//   會把 ⊗（×150）與 ⊕（×1.1）等同看待，從而產出大量無用之「新演算法」。
//   故 check_law 強制同時回報兩者。此條與 M-08、L-05、L-08 同列負面結果庫。
// ---------------------------------------------------------------------------

///|
/// N-04 分塊求逆律：inv(diag(A,B)) = diag(inv A, inv B)
pub fn law_sum_inv(rng : Rng, sizes : Array[(Int, Int)]) -> LawVerdict {
  check_law(
    "⊕ 分塊求逆律 inv(A⊕B) = inv(A)⊕inv(B)",
    (a, b) => qblock_diag(a, b),
    (g, c) => qinv_gauss(g, c),
    (a, b, c) => match (qinv_gauss(a, c), qinv_gauss(b, c)) {
      (Some(x), Some(y)) => Some(qblock_diag(x, y))
      _ => None
    },
    sizes,
    rng,
  )
}

///|
/// N-04 分塊行列式律：det(A⊕B) = det A · det B
pub fn law_sum_det(rng : Rng, sizes : Array[(Int, Int)]) -> LawVerdict {
  check_law(
    "⊕ 分塊行列式律 det(A⊕B) = det A·det B",
    (a, b) => qblock_diag(a, b),
    (g, c) => Some(q_scalar_mat(qdet_gauss(g, c))),
    (a, b, c) => Some(
      q_scalar_mat(cq_mul(c, qdet_gauss(a, c), qdet_gauss(b, c))),
    ),
    sizes,
    rng,
  )
}

///|
/// 律表：把一組判決整理成可列印之表（供報告與反律庫使用）
pub fn law_table(vs : Array[LawVerdict]) -> String {
  let out : Array[String] = []
  out.push("| 結構律 | 成立 | 試驗 | 直接法字乘 | 分解法字乘 | 總增益 | 逐尺寸 |")
  out.push("| --- | :-: | --: | --: | --: | --: | --- |")
  for v in vs {
    out.push(
      "| " +
      v.lname +
      " | " +
      (if v.holds { "✔" } else { "✘" }) +
      " | " +
      v.ltrials.to_string() +
      " | " +
      v.base_wmul.to_string() +
      " | " +
      v.fast_wmul.to_string() +
      " | **×" +
      fmt_d(v.lgain(), 2) +
      "** | " +
      v.ldetail +
      " |",
    )
  }
  out.join("\n")
}

// ---------------------------------------------------------------------------
// 【演算法 173】對偶反演律（N-05）
//
// 定理 173-1（對偶之 Gram）：G(A*) = (G_A⁻¹)ᵀ。（已於命題 169-2 給出。）
//
// 定理 173-2（對偶反演律 —— 本條之核心）：
//     G(A*)⁻¹ = G_A
//   證明：G(A*)⁻¹ = ((G_A⁻¹)ᵀ)⁻¹ = ((G_A⁻¹)⁻¹)ᵀ = (G_A)ᵀ = G_A，
//   末步用到 Gram 矩陣之對稱性（實內積空間）。∎
//
//   推論（成本）：**對偶節點上之「求逆」不需要任何求逆運算。**
//   直接法須在 n 階矩陣上做一次 Θ(n³) 的 ℚ 高斯消去；
//   分解法直接回傳既有的 G_A，成本為 0 次乘法。
//   這是合成樹上唯一「增益無上界」的節點型態。
//
// 定理 173-3（對偶之行列式）：det G(A*) = 1 / det G_A。
//   證明：det((G_A⁻¹)ᵀ) = det(G_A⁻¹) = 1/det(G_A)。∎
//
// 定理 173-4（對合）：G(A**) = G_A，故 A** ≅ A 為等距同構。
//   證明：G(A**) = (G(A*)⁻¹)ᵀ = (G_A)ᵀ = G_A。∎
// ---------------------------------------------------------------------------

///|
/// 一元組合子之結構律檢驗器（對偶、實化、外冪等單參數構造子用）
pub fn check_law1(
  lname : String,
  comb : (Mat[Q]) -> Mat[Q],
  direct : (Mat[Q], Cost) -> Mat[Q]?,
  fact : (Mat[Q], Cost) -> Mat[Q]?,
  sizes : Array[Int],
  rng : Rng,
) -> LawVerdict {
  let mut holds = true
  let mut tb = 0L
  let mut tf = 0L
  let parts : Array[String] = []
  for n in sizes {
    let a = rand_gram(rng, n)
    let cd = Cost::new()
    let lhs = direct(comb(a), cd)
    let cf = Cost::new()
    let rhs = fact(a, cf)
    let same = match (lhs, rhs) {
      (Some(x), Some(y)) => x.equals(y)
      (None, None) => true
      _ => false
    }
    if !same {
      holds = false
    }
    tb = tb + cd.wmul
    tf = tf + cf.wmul
    let g = if cf.wmul == 0L && cd.wmul > 0L {
      "∞"
    } else {
      "×" + fmt_d(Cost::ratio(cd, cf), 2)
    }
    parts.push("dim" + n.to_string() + " " + g)
  }
  {
    lname,
    holds,
    ltrials: sizes.length(),
    base_wmul: tb,
    fast_wmul: tf,
    ldetail: parts.join("　"),
  }
}

///|
/// N-05 對偶反演律：G(A*)⁻¹ = G_A（分解法零乘法）
pub fn law_dual_inv(rng : Rng, sizes : Array[Int]) -> LawVerdict {
  check_law1(
    "* 對偶反演律 G(A*)⁻¹ = G_A",
    a => SDual(SLeaf("A", a)).sgram(),
    (g, c) => qinv_gauss(g, c),
    // 定理 173-2：直接回傳原 Gram，零次乘法
    (a, _c) => Some(a),
    sizes,
    rng,
  )
}

// ---------------------------------------------------------------------------
// 【演算法 174】合成樹求值器（N-11）—— catamorphism
//
// 這是整個 N 群的關鍵件：前面的 N-03／N-04／N-05 各自驗證「深度 1」之律，
// 而本條把它們**沿著任意深度的表達式樹摺疊**（fold / catamorphism），
// 從而對一棵事先未知的樹「合成」出一個演算法。
//
// 定義（合成子）：對 Φ = 求逆，合成規則為
//     synth(Leaf G)   = G⁻¹                       （基礎：真的做一次消去）
//     synth(A ⊗ B)    = synth(A) ⊗ synth(B)       （定理 171-2）
//     synth(A ⊕ B)    = diag(synth(A), synth(B))  （定理 172-1）
//     synth(A*)       = G_A                       （定理 173-2，零成本）
//
// 定理 174（合成之正確性）：對任意表達式 E，synth_inv(E) = (G_E)⁻¹。
//   證明：對 E 之結構歸納。
//   基礎：E = Leaf G，兩邊皆為 G⁻¹。
//   ⊗：G_E = G_A ⊗ G_B，由定理 171-2 得 (G_A⊗G_B)⁻¹ = G_A⁻¹⊗G_B⁻¹
//      = synth(A) ⊗ synth(B)（歸納假設）。
//   ⊕：G_E = diag(G_A, G_B)，由定理 172-1 同理。
//   *：G_E = (G_A⁻¹)ᵀ，由定理 173-2 得 G_E⁻¹ = G_A = synth(A*)。∎
//
// 定理 174-2（行列式之合成）：
//     synthdet(Leaf G) = det G
//     synthdet(A⊗B)    = synthdet(A)^{dim B} · synthdet(B)^{dim A}   （定理 171-3）
//     synthdet(A⊕B)    = synthdet(A) · synthdet(B)                   （定理 172-2）
//     synthdet(A*)     = 1 / synthdet(A)                             （定理 173-3）
//   且 synthdet(E) = det(G_E)。證明：同上之結構歸納。∎
//
// 命題 174-3（成本）：設樹 E 之葉為 {Lᵢ}，維數為 {nᵢ}。
//   直接法須先物化 n×n 之 Gram（n = dim E）再做 Θ(n³) 消去；
//   合成法只在葉上做 Σ Θ(nᵢ³)，其餘節點僅為組裝（⊕ 零乘法、* 零乘法、
//   ⊗ 為 Θ(輸出元素數) 次乘法）。由於 n 為葉維數之積與和的混合，
//   n³ 相對 Σnᵢ³ 可以任意大 —— 增益隨樹之深度與寬度複合成長。
// ---------------------------------------------------------------------------

///|
/// 計入成本之表達式 Gram（直接法必須誠實支付物化大 Gram 的代價）
pub fn SpaceExpr::sgram_cost(self : SpaceExpr, c : Cost) -> Mat[Q] {
  match self {
    SLeaf(_, g) => g
    STensor(a, b) => qkron_cost(c, a.sgram_cost(c), b.sgram_cost(c))
    SSum(a, b) => qblock_diag(a.sgram_cost(c), b.sgram_cost(c))
    SDual(a) => {
      let g = a.sgram_cost(c)
      match qinv_gauss(g, c) {
        Some(h) => h.transpose()
        None => Mat::ident(g.mrows)
      }
    }
  }
}

///|
/// 【合成】對任意表達式樹摺疊出「求逆」演算法（定理 174）
pub fn synth_inv(e : SpaceExpr, c : Cost) -> Mat[Q]? {
  match e {
    SLeaf(_, g) => qinv_gauss(g, c)
    STensor(a, b) =>
      match (synth_inv(a, c), synth_inv(b, c)) {
        (Some(x), Some(y)) => Some(qkron_cost(c, x, y))
        _ => None
      }
    SSum(a, b) =>
      match (synth_inv(a, c), synth_inv(b, c)) {
        (Some(x), Some(y)) => Some(qblock_diag(x, y))
        _ => None
      }
    // 定理 173-2：對偶節點之求逆 = 原 Gram，不需任何消去
    SDual(a) => Some(a.sgram_cost(c))
  }
}

///|
/// 【合成】對任意表達式樹摺疊出「行列式」演算法（定理 174-2）
pub fn synth_det(e : SpaceExpr, c : Cost) -> Q? {
  match e {
    SLeaf(_, g) => Some(qdet_gauss(g, c))
    STensor(a, b) => {
      let na = a.sdim()
      let nb = b.sdim()
      match (synth_det(a, c), synth_det(b, c)) {
        (Some(da), Some(db)) => {
          let mut acc = Q::one()
          for _k in 0..<nb {
            acc = cq_mul(c, acc, da)
          }
          for _k in 0..<na {
            acc = cq_mul(c, acc, db)
          }
          Some(acc)
        }
        _ => None
      }
    }
    SSum(a, b) =>
      match (synth_det(a, c), synth_det(b, c)) {
        (Some(da), Some(db)) => Some(cq_mul(c, da, db))
        _ => None
      }
    SDual(a) =>
      match synth_det(a, c) {
        Some(da) => cq_div(c, Q::one(), da)
        None => None
      }
  }
}

///|
/// 隨機表達式樹（維數受上限控制，避免組合爆炸把義務跑死）
pub fn rand_expr(rng : Rng, depth : Int, maxdim : Int) -> SpaceExpr {
  if depth <= 0 {
    let n = rng.next_range(2, 4)
    return SLeaf("L" + n.to_string(), rand_gram(rng, n))
  }
  for _try in 0..<12 {
    let k = rng.next_below(3)
    let a = rand_expr(rng, depth - 1, maxdim)
    let e = if k == 2 {
      SDual(a)
    } else {
      let b = rand_expr(rng, depth - 1, maxdim)
      if k == 0 {
        STensor(a, b)
      } else {
        SSum(a, b)
      }
    }
    if e.sdim() <= maxdim {
      return e
    }
  }
  let n = rng.next_range(2, 4)
  SLeaf("L" + n.to_string(), rand_gram(rng, n))
}

///|
/// 合成之一次評比：回傳 (正確?, 直接法字乘, 合成法字乘, 標籤, 維數)
pub fn synth_compare(e : SpaceExpr) -> (Bool, Int64, Int64, String, Int) {
  let cd = Cost::new()
  let direct = qinv_gauss(e.sgram_cost(cd), cd)
  let cf = Cost::new()
  let synth = synth_inv(e, cf)
  let same = match (direct, synth) {
    (Some(x), Some(y)) => x.equals(y)
    (None, None) => true
    _ => false
  }
  (same, cd.wmul, cf.wmul, e.slabel(), e.sdim())
}

// ---------------------------------------------------------------------------
// 【演算法 175】結構律搜尋引擎（N-13）
//
// 前面的 N-03／N-04／N-05 是「人先想到律，再叫檢驗器驗」。本條反過來：
// 機械枚舉 (演算法 Φ, 組合子 C, 合成規則 ⊙) 三元組，對每一組問
//     Φ(C(A,B)) =? Φ(A) ⊙ Φ(B)
// 由 N-02 之檢驗器裁決，自動產出定律表。
//
// 定理 175（搜尋之可靠性，承定理 170）：引擎輸出之「推翻」為確定性結論
//   （已持有具體反例）；「成立」為受 Schwartz–Zippel 控制之機率性證據。
//   故本引擎之正當用途是**縮小搜尋範圍**：把 |Φ|·|C|·|⊙| 個候選篩成少數
//   待證命題，再由人補上代數證明（N-03／N-04／N-05 即為已補證者）。
//
// 命題 175-2（判別力）：若引擎對全部候選皆回報成立，則它毫無價值。
//   故義務要求推翻數 > 成立數，且指定若干已知真／已知偽之候選必須各歸其位。
//
// 命題 175-3（網格之必要性 —— 本條最實用的發現）：
//   單一尺寸之網格會放行偽律。例：rank(A⊗B) =? rank A + rank B 在 (2,2) 上
//   給出 4 = 2+2 而通過，加入 (2,3) 後 6 ≠ 5 立刻被推翻。
//   故搜尋網格必須含非對稱尺寸，否則 n·m 與 n+m 在 n=m=2 處之巧合會汙染定律表。
// ---------------------------------------------------------------------------

///|
/// 計入成本之矩陣乘法
pub fn qmul_cost(c : Cost, a : Mat[Q], b : Mat[Q]) -> Mat[Q] {
  Mat::build(a.mrows, b.mcols, (i, j) => {
    let mut s = Q::zero()
    for k in 0..<a.mcols {
      s = cq_add(c, s, cq_mul(c, a.data[i * a.mcols + k], b.data[k * b.mcols + j]))
    }
    s
  })
}

///|
/// 計入成本之純量乘矩陣
pub fn qsmul_cost(c : Cost, s : Q, a : Mat[Q]) -> Mat[Q] {
  Mat::build(a.mrows, a.mcols, (i, j) => cq_mul(c, s, a.data[i * a.mcols + j]))
}

///|
/// 跡（加法不計乘法成本）
pub fn qtrace(c : Cost, a : Mat[Q]) -> Q {
  let mut s = Q::zero()
  for i in 0..<a.mrows {
    s = cq_add(c, s, a.data[i * a.mcols + i])
  }
  s
}

///|
/// 伴隨矩陣 adj(A) = det(A)·A⁻¹
pub fn qadj(c : Cost, a : Mat[Q]) -> Mat[Q]? {
  match qinv_gauss(a, c) {
    Some(h) => Some(qsmul_cost(c, qdet_gauss(a, c), h))
    None => None
  }
}

///|
/// q^k（計入成本）
pub fn qpow_cost(c : Cost, x : Q, k : Int) -> Q {
  let mut acc = Q::one()
  for _i in 0..<k {
    acc = cq_mul(c, acc, x)
  }
  acc
}

///|
/// 候選律之裁決紀錄
pub struct LawCand {
  cphi : String
  ccomb : String
  crule : String
  cholds : Bool
  cgain : Double
}

///|
/// 候選律之可讀名稱
pub fn LawCand::cname(self : LawCand) -> String {
  self.cphi + "(A " + self.ccomb + " B) =? " + self.cphi + "(A) " + self.crule + " " + self.cphi + "(B)"
}

///|
/// 【搜尋】枚舉 (Φ, C, ⊙) 三元組，自動產出定律表
pub fn law_search(rng : Rng, sizes : Array[(Int, Int)]) -> Array[LawCand] {
  // 矩陣值演算法 Φ
  let phis_mat : Array[(String, (Mat[Q], Cost) -> Mat[Q]?)] = [
    ("inv", (a, c) => qinv_gauss(a, c)),
    ("tr̃ans", (a, _c) => Some(a.transpose())),
    ("sq", (a, c) => Some(qmul_cost(c, a, a))),
    ("adj", (a, c) => qadj(c, a)),
  ]
  // 純量值演算法 Φ（包成 1×1）
  let phis_sca : Array[(String, (Mat[Q], Cost) -> Mat[Q]?)] = [
    ("det", (a, c) => Some(q_scalar_mat(qdet_gauss(a, c)))),
    ("trace", (a, c) => Some(q_scalar_mat(qtrace(c, a)))),
    ("rank", (a, _c) => Some(q_scalar_mat(Q::of_int(mrank(a))))),
  ]
  // 組合子 C
  let combs : Array[(String, (Mat[Q], Mat[Q]) -> Mat[Q])] = [
    ("⊗", (a, b) => mkron(a, b)),
    ("⊕", (a, b) => qblock_diag(a, b)),
  ]
  // 矩陣值合成規則 ⊙（含帶標量修正之 Kronecker）
  let rules_mat : Array[(String, (Mat[Q], Mat[Q], Mat[Q], Mat[Q], Cost) -> Mat[Q]?)] = [
    ("⊗", (x, y, _a, _b, c) => Some(qkron_cost(c, x, y))),
    ("⊕", (x, y, _a, _b, _c) => Some(qblock_diag(x, y))),
    // Sylvester 型：(det A)^{m-1}(det B)^{n-1}·(ΦA ⊗ ΦB)
    ("⊗ₛ", (x, y, a, b, c) => {
      let n = a.mrows
      let m = b.mrows
      let s = cq_mul(
        c,
        qpow_cost(c, qdet_gauss(a, c), m - 1),
        qpow_cost(c, qdet_gauss(b, c), n - 1),
      )
      Some(qsmul_cost(c, s, qkron_cost(c, x, y)))
    }),
  ]
  // 純量值合成規則 ⊙
  let rules_sca : Array[(String, (Mat[Q], Mat[Q], Mat[Q], Mat[Q], Cost) -> Mat[Q]?)] = [
    ("·", (x, y, _a, _b, c) => Some(q_scalar_mat(cq_mul(c, x.data[0], y.data[0])))),
    ("+", (x, y, _a, _b, c) => Some(q_scalar_mat(cq_add(c, x.data[0], y.data[0])))),
    // det 型：Φ(A)^{dim B} · Φ(B)^{dim A}
    ("^", (x, y, a, b, c) => Some(
      q_scalar_mat(
        cq_mul(
          c,
          qpow_cost(c, x.data[0], b.mrows),
          qpow_cost(c, y.data[0], a.mrows),
        ),
      ),
    )),
  ]
  let out : Array[LawCand] = []
  let groups : Array[
    (
      Array[(String, (Mat[Q], Cost) -> Mat[Q]?)],
      Array[(String, (Mat[Q], Mat[Q], Mat[Q], Mat[Q], Cost) -> Mat[Q]?)],
    ),
  ] = [(phis_mat, rules_mat), (phis_sca, rules_sca)]
  for grp in groups {
    let (phis, rules) = grp
    for ph in phis {
      let (pname, phi) = ph
      for cb in combs {
        let (cbname, comb) = cb
        for rl in rules {
          let (rname, rule) = rl
          let v = check_law(
            pname + " / " + cbname + " / " + rname,
            comb,
            phi,
            (a, b, c) => match (phi(a, c), phi(b, c)) {
              (Some(x), Some(y)) => rule(x, y, a, b, c)
              _ => None
            },
            sizes,
            rng,
          )
          out.push({
            cphi: pname,
            ccomb: cbname,
            crule: rname,
            cholds: v.holds,
            cgain: v.lgain(),
          })
        }
      }
    }
  }
  out
}

///|
/// 於定律表中查某候選之裁決
pub fn law_find(tbl : Array[LawCand], phi : String, comb : String, rule : String) -> Bool? {
  for t in tbl {
    if t.cphi == phi && t.ccomb == comb && t.crule == rule {
      return Some(t.cholds)
    }
  }
  None
}

// ---------------------------------------------------------------------------
// 【演算法 176】成本代數與合成分派（N-12）
//
// N-11 之 catamorphism 在每個節點一律選擇「分解」。這不一定對：
// N-13 之定律表顯示 ⊕ 節點之增益僅 ×1.1、而某些 Φ 的分解甚至更貴。
// 本條為表達式樹建立**符號成本代數** —— 不執行任何算術，只由樹的形狀
// 預測兩條路徑的字乘法數 —— 再據以在每個節點分派。
//
// 定義（物化成本）：mat(E) ≔ 物化 G_E 所需之字乘法數
//     mat(Leaf)  = 0                        （葉之 Gram 已在手上）
//     mat(A⊗B)   = mat A + mat B + (dimA·dimB)²
//     mat(A⊕B)   = mat A + mat B            （分塊置放，零乘法）
//     mat(A*)    = mat A + κ·(dimA)³        （須一次求逆）
//
// 定義（兩條路徑）：
//     flat(E) = mat(E) + κ·(dim E)³         （攤平：物化後直接消去）
//     dec(Leaf)  = κ·n³
//     dec(A⊗B)   = best(A) + best(B) + (dimA·dimB)²
//     dec(A⊕B)   = best(A) + best(B)
//     dec(A*)    = mat(A)                   （定理 173-2：零求逆）
//     best(E) = min(flat E, dec E)
//
// 分派規則：plan(E) = (dec E < flat E)。
//
// 命題 176（分派之保守性）：best 為逐節點取極小，故 best(E) ≤ flat(E) 恆成立，
//   亦即分派後之預測成本不劣於「一律攤平」；又 best(E) ≤ dec(E)，
//   故亦不劣於「一律分解」。分派器在預測層面上同時支配兩個固定策略。
// ---------------------------------------------------------------------------

///|
/// 高斯消去之字乘法校準常數（κ/100，見 N-12 之實測校準）
pub fn tkappa() -> Int64 {
  260L
}

///|
/// 符號成本：物化 G_E 之字乘法數（不執行任何算術）
pub fn tmat(e : SpaceExpr) -> Int64 {
  match e {
    SLeaf(_, _) => 0L
    STensor(a, b) => {
      let d = (a.sdim() * b.sdim()).to_int64()
      tmat(a) + tmat(b) + d * d
    }
    SSum(a, b) => tmat(a) + tmat(b)
    SDual(a) => {
      let n = a.sdim().to_int64()
      tmat(a) + tkappa() * n * n * n / 100L
    }
  }
}

///|
/// 符號成本：攤平路徑（物化後直接求逆）
pub fn tinv_flat(e : SpaceExpr) -> Int64 {
  let n = e.sdim().to_int64()
  tmat(e) + tkappa() * n * n * n / 100L
}

///|
/// 符號成本：分解路徑（逐節點取極小）
pub fn tinv_dec(e : SpaceExpr) -> Int64 {
  match e {
    SLeaf(_, g) => {
      let n = g.mrows.to_int64()
      tkappa() * n * n * n / 100L
    }
    STensor(a, b) => {
      let d = (a.sdim() * b.sdim()).to_int64()
      tinv_best(a) + tinv_best(b) + d * d
    }
    SSum(a, b) => tinv_best(a) + tinv_best(b)
    SDual(a) => tmat(a)
  }
}

///|
/// best(E) = min(flat E, dec E)
pub fn tinv_best(e : SpaceExpr) -> Int64 {
  let f = tinv_flat(e)
  let d = tinv_dec(e)
  if d < f {
    d
  } else {
    f
  }
}

///|
/// 分派器：於本節點是否應分解
pub fn plan_synth(e : SpaceExpr) -> Bool {
  tinv_dec(e) < tinv_flat(e)
}

///|
/// 預測增益（攤平 ÷ 分解）
pub fn tinv_gain(e : SpaceExpr) -> Double {
  let f = tinv_flat(e).to_double()
  let d = tinv_best(e).to_double()
  if d <= 0.0 {
    0.0
  } else {
    f / d
  }
}

// ---------------------------------------------------------------------------
// 【演算法 176b】位元感知成本代數（N-12 第二版）
//
// 第一版（176）只看樹的形狀，系統性低估分解路徑 —— 因為它把每次 ℚ 乘法
// 都當成 1 次字乘，忽略了有理數係數的膨脹。實測顯示：攤平路徑之預測尚可
// （誤差 ~1.1×），分解路徑卻被低估 5 倍以上，使預測增益高估 3–4 倍。
//
// 第二版補上 Hadamard 型位元界：
//   w(β) ≔ max(1, ⌈β/64⌉)                      （β 位元之數佔幾個機器字）
//   葉：β₀ = 實測之最大元素位元數（讀取資料，不執行演算法）
//   A⊗B 之組裝：(dA·dB)² 次乘法，每次 w(βA)·w(βB) 次字乘；輸出 βA + βB 位元
//   A⊕B 之組裝：0 次乘法；輸出 max(βA, βB) 位元
//   n×n 於 β 位元上求逆：由 Cramer 法則，逆元為 (餘因子)/(行列式)，
//     兩者皆受 Hadamard 界 ~n·β 控制；消去過程之中間量亦達此量級，
//     故成本 ≈ κ·n³·w(nβ)²，輸出 n·β 位元。
//
// 命題 176b：第二版之預測誤差應顯著小於第一版。此為可否證之主張 ——
//   義務實測兩版之幾何平均相對誤差並要求第二版較優，若不成立則本條失敗。
// ---------------------------------------------------------------------------

///|
/// β 位元之數佔幾個 64 位元字
pub fn wwords(b : Int64) -> Int64 {
  let w = (b + 63L) / 64L
  if w < 1L {
    1L
  } else {
    w
  }
}

///|
/// 有理數之位元數（分子分母取大者）
pub fn qbits(x : Q) -> Int64 {
  let a = x.num.bit_length().to_int64()
  let b = x.den.bit_length().to_int64()
  let m = if a > b { a } else { b }
  if m < 1L {
    1L
  } else {
    m
  }
}

///|
/// 矩陣元素之最大位元數
pub fn mat_bits(a : Mat[Q]) -> Int64 {
  let mut m = 1L
  for x in a.data {
    let b = qbits(x)
    if b > m {
      m = b
    }
  }
  m
}

///|
/// 位元感知：物化 G_E 之 (字乘法數, 輸出位元數)
pub fn tmat2(e : SpaceExpr) -> (Int64, Int64) {
  match e {
    SLeaf(_, g) => (0L, mat_bits(g))
    STensor(a, b) => {
      let (ca, ba) = tmat2(a)
      let (cb, bb) = tmat2(b)
      let d = (a.sdim() * b.sdim()).to_int64()
      (ca + cb + d * d * wwords(ba) * wwords(bb), ba + bb)
    }
    SSum(a, b) => {
      let (ca, ba) = tmat2(a)
      let (cb, bb) = tmat2(b)
      (ca + cb, if ba > bb { ba } else { bb })
    }
    SDual(a) => {
      let (ca, ba) = tmat2(a)
      let n = a.sdim().to_int64()
      let w = wwords(n * ba)
      (ca + tkappa() * n * n * n * w * w / 100L, n * ba)
    }
  }
}

///|
/// 位元感知：攤平路徑
pub fn tinv_flat2(e : SpaceExpr) -> Int64 {
  let (c, b) = tmat2(e)
  let n = e.sdim().to_int64()
  let w = wwords(n * b)
  c + tkappa() * n * n * n * w * w / 100L
}

///|
/// 位元感知：分解路徑之 (字乘法數, 輸出位元數)
pub fn tinv_dec2(e : SpaceExpr) -> (Int64, Int64) {
  match e {
    SLeaf(_, g) => {
      let n = g.mrows.to_int64()
      let b = mat_bits(g)
      let w = wwords(n * b)
      (tkappa() * n * n * n * w * w / 100L, n * b)
    }
    STensor(a, b) => {
      let (ca, ba) = tinv_best2(a)
      let (cb, bb) = tinv_best2(b)
      let d = (a.sdim() * b.sdim()).to_int64()
      (ca + cb + d * d * wwords(ba) * wwords(bb), ba + bb)
    }
    SSum(a, b) => {
      let (ca, ba) = tinv_best2(a)
      let (cb, bb) = tinv_best2(b)
      (ca + cb, if ba > bb { ba } else { bb })
    }
    // 定理 173-2：對偶節點之求逆 = 物化原 Gram
    SDual(a) => tmat2(a)
  }
}

///|
/// best₂(E)：逐節點取極小（回傳成本與輸出位元數）
pub fn tinv_best2(e : SpaceExpr) -> (Int64, Int64) {
  let (cd, bd) = tinv_dec2(e)
  let cf = tinv_flat2(e)
  if cd < cf {
    (cd, bd)
  } else {
    let (_c, b) = tmat2(e)
    (cf, e.sdim().to_int64() * b)
  }
}

///|
/// 第二版之預測增益
pub fn tinv_gain2(e : SpaceExpr) -> Double {
  let f = tinv_flat2(e).to_double()
  let (d, _b) = tinv_best2(e)
  if d <= 0.0.to_int64() {
    0.0
  } else {
    f / d.to_double()
  }
}

// ---------------------------------------------------------------------------
// 【演算法 176c】校準後之成本代數（N-12 第三版，實際採用者）
//
// 第二版（Hadamard 位元界）失敗之後，改採本庫 K/L/M 層既有之做法：
// 保留形狀模型，對被系統性低估的那條路徑乘上一個**實測校準常數**
// （與 plan_zadj 之 619/100 同類）。
//
// 實測（見義務）：形狀模型對攤平路徑低估約 ×3、對分解路徑低估約 ×10，
// 兩者之比約 3.2 —— 這正是預測增益被高估的倍數。故令
//     gain₃(E) ≔ flat(E) / (λ · best(E))，　λ = 316/100
//
// 命題 176c：λ 只改變增益之標度，不改變 flat 與 dec 之序關係在
//   λ = 1 時之判決 —— 故校準不影響命題 176 之保守性結論，只影響預測精度。
// ---------------------------------------------------------------------------

///|
/// 分解路徑之實測校準常數（λ/100）
pub fn tlambda() -> Int64 {
  316L
}

///|
/// 校準後之預測增益（第三版）
pub fn tinv_gain3(e : SpaceExpr) -> Double {
  let f = tinv_flat(e).to_double()
  let d = tinv_best(e).to_double() * tlambda().to_double() / 100.0
  if d <= 0.0 {
    0.0
  } else {
    f / d
  }
}

///|
/// 倍率誤差 max(p/m, m/p)：預測與實測相差幾倍
pub fn fold_err(pred : Double, meas : Double) -> Double {
  if pred <= 0.0 || meas <= 0.0 {
    0.0
  } else if pred > meas {
    pred / meas
  } else {
    meas / pred
  }
}

// ---------------------------------------------------------------------------
// 【演算法 180】複合矩陣與 Sylvester–Franke 定理（N-10）
//
// 【定義】A 之第 k 複合矩陣 Cₖ(A)：列與行皆以 {1..n} 之 k 元子集依字典序
//   索引，(I,J) 元為 A 之子式 det(A[I,J])。階數為 C(n,k)。
//
// 【命題 180-1】Cₖ(G) 即 Λᵏ V 之 Gram：
//   ⟨e_I, e_J⟩_{Λᵏ} = det(⟨e_i, e_j⟩)_{i∈I, j∈J}（Gram 行列式公式）。
//   故外冪空間之度量由複合矩陣給出，Λᵏ 成為 N 群之合法構造子。
//
// 【定理 180（Sylvester–Franke）】det(Cₖ(A)) = det(A)^{C(n−1, k−1)}。
//   證明要點：A ↦ Cₖ(A) 為乘法同態（Cauchy–Binet：Cₖ(AB) = Cₖ(A)Cₖ(B)），
//   故 det∘Cₖ 為 GL(n) 上之多項式特徵標，必為 det 之冪 det^e；
//   以 A = diag(t,1,…,1) 代入：Cₖ(A) 之對角元中含 t 者恰為「I ∋ 1」之子集，
//   共 C(n−1,k−1) 個，故 det Cₖ(A) = t^{C(n−1,k−1)} 而 det(A) = t，得 e = C(n−1,k−1)。∎
//
// 【成本】直接法須物化 Cₖ(A)（C(n,k)² 個 k 階子式）再做 C(n,k) 階消去；
//   分解法只做一次 n 階 det 再取冪。兩者差距隨 C(n,k) 爆炸性拉開。
// ---------------------------------------------------------------------------

///|
/// 第 k 複合矩陣 Cₖ(A)，階數 C(n,k)
pub fn compound(a : Mat[Q], k : Int, c : Cost) -> Mat[Q] {
  let n = a.mrows
  let ss = subsets_k(n, k)
  let m = ss.length()
  Mat::build(m, m, (i, j) => {
    let si = ss[i]
    let sj = ss[j]
    let sub = Mat::build(k, k, (r, s) => a.at(si[r], sj[s]))
    qdet_gauss(sub, c)
  })
}

///|
/// Sylvester–Franke 之指數 C(n−1, k−1)
pub fn sf_exponent(n : Int, k : Int) -> Int {
  binom(n - 1, k - 1)
}

///|
/// 二進位冪（平方–乘），用於 Sylvester–Franke 之右式
///
/// 【為何需要】線性冪 qpow_cost 對 x^e 做 e−1 次乘法，而累積量之位元數
///   隨步數線性成長，故成本 ≈ Σ_{i<e} i·b²/64² = Θ(e²b²)。
///   平方–乘只做 Θ(log e) 次乘法，成本由最後一次平方主導 ≈ Θ(e²b²/4)。
///   在 Sylvester–Franke 中指數為 C(n−1,k−1)，隨 n 組合爆炸，
///   此差異足以反轉整條律的划算與否 —— 見 N-10 之實測。
pub fn qpow_fast(c : Cost, x : Q, e : Int) -> Q {
  if e <= 0 {
    return Q::one()
  }
  let mut base = x
  let mut acc = Q::one()
  let mut k = e
  while k > 0 {
    if k % 2 == 1 {
      acc = cq_mul(c, acc, base)
    }
    k = k / 2
    if k > 0 {
      base = cq_mul(c, base, base)
    }
  }
  acc
}

// ---------------------------------------------------------------------------
// 【演算法 182】Hom 律（N-06）
//
// 【命題 182-1】Hom(V,W) ≅ W ⊗ V*（有限維），且此同構為等距：
//   以 Hilbert–Schmidt 內積賦予 Hom(V,W) 後，G(Hom) = G(W) ⊗ G(V)⁻ᵀ。
//
// 【定理 182】故 Hom 不是獨立構造子，而是 ⊗ 與 * 之複合：
//       SHom(V,W) ≡ STensor(W, SDual(V))
//   於是 N-11 之 catamorphism **無須任何修改**即可對 Hom 節點合成演算法，
//   且由定理 173-2（對偶節點零求逆），合成法只需一次求逆而非兩次。
//
// 【推論 182-1】同維之下，Hom(V,W) 之合成增益必高於 V⊗W：
//   前者 = inv(G_W) ⊗ G_V（一次求逆），後者 = inv(G_V) ⊗ inv(G_W)（兩次）。
// ---------------------------------------------------------------------------

///|
/// Hom(V,W) 之表達式：W ⊗ V*（定理 182）
pub fn shom(v : SpaceExpr, w : SpaceExpr) -> SpaceExpr {
  STensor(w, SDual(v))
}

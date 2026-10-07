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
  /// 外冪 Λᵏ：Gram 為複合矩陣 Cₖ(G)，維數 C(n,k)（N-10 命題 180-1 已證保正定）
  SExt(SpaceExpr, Int)
  /// 度量扭曲（同餘）：Gram 為 AᵀGA，A 為同階可逆方陣，維數不變（N-08）
  STwist(SpaceExpr, Mat[Q])
  /// 子空間限制：Gram 為 SᵀGS，S 為 n×m 滿列秩（m ≤ n），維數降為 m（N-09）
  SSub(SpaceExpr, Mat[Q])
  /// Kronecker 和 ⊞：Gram 為 A⊗I + I⊗B，譜為 {λᵢ+μⱼ} 故保正定（N-24）
  SKSum(SpaceExpr, SpaceExpr)
}

///|
/// 分塊對角 diag(A, B)
pub fn qblock_diag(a : Mat[Q], b : Mat[Q]) -> Mat[Q] {
  let ra = a.mrows
  let ca = a.mcols
  Mat::build(ra + b.mrows, ca + b.mcols, (i, j) => {
    if i < ra && j < ca {
      a.at(i, j)
    } else if i >= ra && j >= ca {
      b.at(i - ra, j - ca)
    } else {
      Q::zero()
    }
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
    SExt(a, k) => binom(a.sdim(), k)
    STwist(a, _) => a.sdim()
    SSub(_, sm) => sm.mcols
    SKSum(a, b) => a.sdim() * b.sdim()
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
    SExt(a, k) => {
      // 【N-79】按形狀派工：k = n−1 時有封閉式
      //   C_{n−1}(G)[p][q] = (−1)^{p+q}·det(G)·G⁻¹[n−1−p][n−1−q]
      // （Λ^{n−1}V ≅ V* ⊗ det V）。泛型 compound 物化 n² 個 (n−1) 階子式
      // ⇒ Θ(n⁵)；封閉式只做一次反矩陣與一次行列式 ⇒ Θ(n³)。
      // 兩路逐元相等已由 N-79 在全部 45 個空間上對帳。
      let g = a.sgram()
      // 封閉式之定義域比 compound 小：它要 G 可逆。擾動表 空間⊥ 內
      // 刻意放了奇異 Gram，故此處必須真的檢查，不能假設「Gram 都正定」。
      let fast = if k == g.mrows - 1 && k >= 1 {
        cf_codim1_opt(g, Cost::new())
      } else {
        None
      }
      match fast {
        Some(m) => m
        None => compound(g, k, Cost::new())
      }
    }
    STwist(a, m) => {
      let g = a.sgram()
      m.transpose().times(g).times(m)
    }
    SSub(a, sm) =>
      // 【N-75】按形狀派工：SSub(STensor(x,y), 對稱選擇矩陣) 有封閉式。
      // 只在逐元認出選擇矩陣時才走快路；認錯形狀會算出錯的 Gram，
      // 故判準是 is_sym_sel 的逐元比對，不是維數相符。
      match a {
        STensor(x, y) => {
          let n = x.sdim()
          if y.sdim() == n &&
            sm.mrows == n * n &&
            sm.mcols == n * (n + 1) / 2 &&
            is_sym_sel(sm, n) {
            spec_sym_sq_gram(x.sgram(), y.sgram())
          } else {
            let g = a.sgram()
            sm.transpose().times(g).times(sm)
          }
        }
        _ => {
          let g = a.sgram()
          sm.transpose().times(g).times(sm)
        }
      }
    SKSum(a, b) => qkron_sum(a.sgram(), b.sgram())
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
    SExt(a, k) => "Λ" + k.to_string() + a.slabel()
    STwist(a, _) => "T[" + a.slabel() + "]"
    SSub(a, _) => "U[" + a.slabel() + "]"
    SKSum(a, b) => "(" + a.slabel() + "⊞" + b.slabel() + ")"
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
    SExt(a, _) => 1 + a.sdepth()
    STwist(a, _) => 1 + a.sdepth()
    SSub(a, _) => 1 + a.sdepth()
    SKSum(a, b) => 1 + maxi(a.sdepth(), b.sdepth())
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
    let m : Mat[Q] = Mat::build(n, n, (_i, _j) => {
      Q::frac(rng.next_small(5), rng.next_range(1, 4))
    })
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
/// 計量軌道。
///
/// 本庫有兩套互不相通的成本計量器，而它們**完全互斥**（定理 193-1）：
/// 精確 ℚ 軌只記字乘法 `wmul`，ℝ 軌只記浮點運算 `flops`。
/// 任何跨軌的增益比較都沒有定義 —— 這不是精度問題，是量綱問題。
pub enum Track {
  /// 精確 ℚ／ℤ 軌：以機器字乘法計量
  TQ
  /// ℝ 軌：以浮點運算計量
  TR
}

///|
pub fn Track::tlabel(self : Track) -> String {
  match self {
    TQ => "精確 ℚ"
    TR => "ℝ 軌"
  }
}

///|
pub fn Track::tunit(self : Track) -> String {
  match self {
    TQ => "字乘法"
    TR => "flop"
  }
}

///|
pub fn Track::teq(self : Track, other : Track) -> Bool {
  match (self, other) {
    (TQ, TQ) => true
    (TR, TR) => true
    _ => false
  }
}

///|
/// 依軌道取出對應之計數器。用錯軌道會得到 0，而不是一個「比較小的數」——
/// 這正是定理 193-1 所要凸顯的：兩者不是同一個量的不同單位。
pub fn cost_by_track(c : Cost, t : Track) -> Int64 {
  match t {
    TQ => c.wmul
    TR => c.flops
  }
}

///|
/// 同軌增益。跨軌請勿使用 —— 無定義。
pub fn gain_by_track(base : Cost, fast : Cost, t : Track) -> Double {
  let b = cost_by_track(base, t).to_double()
  let f = cost_by_track(fast, t).to_double()
  if f <= 0.0 {
    0.0
  } else {
    b / f
  }
}

///|
pub struct LawVerdict {
  /// 律之名稱
  lname : String
  /// 是否逐例成立
  holds : Bool
  /// 試驗數
  ltrials : Int
  /// 直接法之字乘法總數
  base_cost : Int64
  /// 分解法之字乘法總數
  fast_cost : Int64
  /// 逐尺寸之增益明細
  ldetail : String
  /// 計量軌道（N-30）。增益只在同軌內可比。
  ltrack : Track
}

///|
/// 本判決之基準成本（依軌道取對應計數器）。
pub fn LawVerdict::cost(self : LawVerdict) -> Int64 {
  self.base_cost
}

///|
/// 本判決之計量單位名稱。
pub fn LawVerdict::unit(self : LawVerdict) -> String {
  self.ltrack.tunit()
}

///|
/// 增益 = 直接法成本 / 分解法成本
pub fn LawVerdict::lgain(self : LawVerdict) -> Double {
  if self.fast_cost <= 0L {
    0.0
  } else {
    self.base_cost.to_double() / self.fast_cost.to_double()
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
  check_law_dist(lname, comb, direct, fact, sizes, rng, rand_gram)
}

///|
/// 帶取樣分布的版本（N-36）。
///
/// 原 `check_law` 把取樣器寫死成 `rand_gram`（恆正定）。N-26 已證明這會
/// 製造假陽性：正定矩陣恆滿秩，於是任何關於 rank 的錯誤規則都無從被推翻。
/// 取樣分布不是實作細節，它決定了哪些律推不翻 —— 故提為參數。
pub fn check_law_dist(
  lname : String,
  comb : (Mat[Q], Mat[Q]) -> Mat[Q],
  direct : (Mat[Q], Cost) -> Mat[Q]?,
  fact : (Mat[Q], Mat[Q], Cost) -> Mat[Q]?,
  sizes : Array[(Int, Int)],
  rng : Rng,
  sampler : (Rng, Int) -> Mat[Q],
) -> LawVerdict {
  let sm : Array[(Int, Int, (Rng, Int) -> Mat[Q])] = []
  for sz in sizes {
    let (n, m) = sz
    sm.push((n, m, sampler))
  }
  check_law_samples(lname, comb, direct, fact, sm, rng)
}

///|
/// 最一般的版本：每個樣本各自帶自己的尺寸**與分布**（N-36）。
///
/// 為何要讓分布隨樣本而變，而不是整次搜尋用同一個分布：
/// 單一分布不論選哪個都會偏。正定分布讓 rank 類錯誤規則無從推翻（N-26）；
/// 而換成降秩分布之後，det 類規則又會因為兩側同時為 0 而**空洞地**成立
/// —— 實測這會憑空製造四條新的假陽性（inv/⊗/⊗ₛ、inv/⊕/⊗ₛ、
/// adj/⊕/⊗ₛ、det/⊕/^）。一條律要判成立，必須在**每一種**分布下都成立。
pub fn check_law_samples(
  lname : String,
  comb : (Mat[Q], Mat[Q]) -> Mat[Q],
  direct : (Mat[Q], Cost) -> Mat[Q]?,
  fact : (Mat[Q], Mat[Q], Cost) -> Mat[Q]?,
  samples : Array[(Int, Int, (Rng, Int) -> Mat[Q])],
  rng : Rng,
) -> LawVerdict {
  let (v, _vac) = check_law_samples_vac(lname, comb, direct, fact, samples, rng)
  v
}

///|
/// 同上，但額外回傳**空洞樣本數**（N-42）。
///
/// 空洞樣本 ≔ 兩側都算不出來（皆為 ⊥）的樣本。這種樣本會被判為「相符」，
/// 於是它對裁決**毫無鑑別力**，卻照樣計入試驗數。原本這件事不可見：
/// `qadj` 與 `qinv_gauss` 在奇異輸入上回傳 ⊥，而 N-36 刻意加入的降秩樣本
/// 正是奇異的 —— 換言之，N-36 為了推翻 rank 類假陽性而加的那個樣本，
/// 對 inv 類與 adj 類的候選完全沒有鑑別力，而舊介面看不出這件事。
///
/// 複合會**放大**這個盲區：內層 Φ 一旦在反例上回傳 ⊥，反例就到不了外層。
pub fn check_law_samples_vac(
  lname : String,
  comb : (Mat[Q], Mat[Q]) -> Mat[Q],
  direct : (Mat[Q], Cost) -> Mat[Q]?,
  fact : (Mat[Q], Mat[Q], Cost) -> Mat[Q]?,
  samples : Array[(Int, Int, (Rng, Int) -> Mat[Q])],
  rng : Rng,
) -> (LawVerdict, Int) {
  let mut vac = 0
  let mut holds = true
  let mut tb = 0L
  let mut tf = 0L
  let parts : Array[String] = []
  for sm0 in samples {
    let (n, m, sampler) = sm0
    let a = sampler(rng, n)
    let b = sampler(rng, m)
    let cd = Cost::new()
    let lhs = direct(comb(a, b), cd)
    let cf = Cost::new()
    let rhs = fact(a, b, cf)
    let same = match (lhs, rhs) {
      (Some(x), Some(y)) => x.equals(y)
      (None, None) => {
        vac = vac + 1
        true
      }
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
  (
    {
      lname,
      holds,
      ltrials: samples.length(),
      base_cost: tb,
      fast_cost: tf,
      ldetail: parts.join("　"),
      ltrack: TQ,
    },
    vac,
  )
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
    (a, b, c) => {
      match (qinv_gauss(a, c), qinv_gauss(b, c)) {
        (Some(x), Some(y)) => Some(qkron_cost(c, x, y))
        _ => None
      }
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
  Mat::build(a.mrows * rb, a.mcols * cb, (i, j) => {
    cq_mul(c, a.at(i / rb, j / cb), b.at(i % rb, j % cb))
  })
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
    (a, b, c) => {
      match (qinv_gauss(a, c), qinv_gauss(b, c)) {
        (Some(x), Some(y)) => Some(qblock_diag(x, y))
        _ => None
      }
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
    (a, b, c) => {
      Some(q_scalar_mat(cq_mul(c, qdet_gauss(a, c), qdet_gauss(b, c))))
    },
    sizes,
    rng,
  )
}

///|
/// 律表：把一組判決整理成可列印之表（供報告與反律庫使用）
pub fn law_table(vs : Array[LawVerdict]) -> String {
  let out : Array[String] = []
  out.push(
    "| 結構律 | 成立 | 試驗 | 直接法字乘 | 分解法字乘 | 總增益 | 逐尺寸 |",
  )
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
      v.base_cost.to_string() +
      " | " +
      v.fast_cost.to_string() +
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
    base_cost: tb,
    fast_cost: tf,
    ldetail: parts.join("　"),
    ltrack: TQ,
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
    SExt(a, k) => compound(a.sgram_cost(c), k, c)
    STwist(a, m) => {
      let g = a.sgram_cost(c)
      qmul_cost(c, qmul_cost(c, m.transpose(), g), m)
    }
    SSub(a, sm) => {
      let g = a.sgram_cost(c)
      qmul_cost(c, qmul_cost(c, sm.transpose(), g), sm)
    }
    SKSum(a, b) => qkron_sum(a.sgram_cost(c), b.sgram_cost(c))
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
    // N-32 新增之構造子在舊合成器上一律攤平 —— 舊合成器之行為維持不變，
    // 新構造子之律由 N-31 的多態合成器處理。
    other => qinv_gauss(other.sgram_cost(c), c)
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
    other => Some(qdet_gauss(other.sgram_cost(c), c))
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
      s = cq_add(
        c,
        s,
        cq_mul(c, a.data[i * a.mcols + k], b.data[k * b.mcols + j]),
      )
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
/// ℚ 之 Kronecker 和 A ⊞ B = A⊗I_m + I_n⊗B（N-24 引入之第三個組合子）
pub fn qkron_sum(a : Mat[Q], b : Mat[Q]) -> Mat[Q] {
  let n = a.mrows
  let m = b.mrows
  mkron(a, Mat::ident(m)).plus(mkron(Mat::ident(n), b))
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
  self.cphi +
  "(A " +
  self.ccomb +
  " B) =? " +
  self.cphi +
  "(A) " +
  self.crule +
  " " +
  self.cphi +
  "(B)"
}

///|
/// 【搜尋】枚舉 (Φ, C, ⊙) 三元組，自動產出定律表
pub fn law_search(rng : Rng, sizes : Array[(Int, Int)]) -> Array[LawCand] {
  law_search_dist(rng, sizes, rand_gram)
}

///|
/// 帶取樣分布的定律搜尋（N-36）。
pub fn law_search_dist(
  rng : Rng,
  sizes : Array[(Int, Int)],
  sampler : (Rng, Int) -> Mat[Q],
) -> Array[LawCand] {
  let sm : Array[(Int, Int, (Rng, Int) -> Mat[Q])] = []
  for sz in sizes {
    let (n, m) = sz
    sm.push((n, m, sampler))
  }
  law_search_samples(rng, sm)
}

///|
/// 以「尺寸 × 分布」樣本清單驅動的定律搜尋（N-36）。
pub fn phi_mat_registry() -> Array[(String, (Mat[Q], Cost) -> Mat[Q]?)] {
  [
    ("inv", (a, c) => qinv_gauss(a, c)),
    ("tr̃ans", (a, _c) => Some(a.transpose())),
    ("sq", (a, c) => Some(qmul_cost(c, a, a))),
    ("adj", (a, c) => qadj(c, a)),
    ("cube", (a, c) => Some(qmul_cost(c, a, qmul_cost(c, a, a)))),
  ]
}

///|
/// 純量值演算法 Φ（包成 1×1 矩陣，與矩陣值 Φ 共用同一檢驗器）
pub fn phi_sca_registry() -> Array[(String, (Mat[Q], Cost) -> Mat[Q]?)] {
  [
    ("det", (a, c) => Some(q_scalar_mat(qdet_gauss(a, c)))),
    ("trace", (a, c) => Some(q_scalar_mat(qtrace(c, a)))),
    ("rank", (a, _c) => Some(q_scalar_mat(Q::of_int(mrank(a))))),
  ]
}

///|
/// 組合子 C
pub fn comb_registry() -> Array[(String, (Mat[Q], Mat[Q]) -> Mat[Q])] {
  [
    ("⊗", (a, b) => mkron(a, b)),
    ("⊕", (a, b) => qblock_diag(a, b)),
    ("⊞", (a, b) => qkron_sum(a, b)),
  ]
}

///|
/// 矩陣值合成規則 ⊙（含帶標量修正之 Kronecker）
pub fn rule_mat_registry() -> Array[
  (String, (Mat[Q], Mat[Q], Mat[Q], Mat[Q], Cost) -> Mat[Q]?),
] {
  [
    ("⊗", (x, y, _a, _b, c) => Some(qkron_cost(c, x, y))),
    ("⊕", (x, y, _a, _b, _c) => Some(qblock_diag(x, y))),
    // Sylvester 型：(det A)^{m-1}(det B)^{n-1}·(ΦA ⊗ ΦB)
    (
      "⊗ₛ",
      (x, y, a, b, c) => {
        let n = a.mrows
        let m = b.mrows
        let s = cq_mul(
          c,
          qpow_cost(c, qdet_gauss(a, c), m - 1),
          qpow_cost(c, qdet_gauss(b, c), n - 1),
        )
        Some(qsmul_cost(c, s, qkron_cost(c, x, y)))
      },
    ),
  ]
}

///|
/// 純量值合成規則 ⊙
pub fn rule_sca_registry() -> Array[
  (String, (Mat[Q], Mat[Q], Mat[Q], Mat[Q], Cost) -> Mat[Q]?),
] {
  [
    (
      "·",
      (x, y, _a, _b, c) => Some(q_scalar_mat(cq_mul(c, x.data[0], y.data[0]))),
    ),
    (
      "+",
      (x, y, _a, _b, c) => Some(q_scalar_mat(cq_add(c, x.data[0], y.data[0]))),
    ),
    // det 型：Φ(A)^{dim B} · Φ(B)^{dim A}
    (
      "^",
      (x, y, a, b, c) => {
        Some(
          q_scalar_mat(
            cq_mul(
              c,
              qpow_cost(c, x.data[0], b.mrows),
              qpow_cost(c, y.data[0], a.mrows),
            ),
          ),
        )
      },
    ),
  ]
}

///|
/// 以「尺寸 × 分布」樣本清單驅動的定律搜尋（N-36）。
///
/// 搜尋空間的五張表（Φ 矩陣值／Φ 純量值／C／⊙ 矩陣值／⊙ 純量值）已於 N-42
/// 提為獨立的註冊表函式。理由不是美觀：複合器（compose.mbt）必須枚舉
/// **同一組** Φ 與 ⊙；若兩邊各抄一份，遲早分岔，而分岔的那一刻定律表與
/// 複合表會各說各話且無人察覺。
pub fn law_search_samples(
  rng : Rng,
  samples : Array[(Int, Int, (Rng, Int) -> Mat[Q])],
) -> Array[LawCand] {
  let phis_mat = phi_mat_registry()
  let phis_sca = phi_sca_registry()
  let combs = comb_registry()
  let rules_mat = rule_mat_registry()
  let rules_sca = rule_sca_registry()
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
          let v = check_law_samples(
            pname + " / " + cbname + " / " + rname,
            comb,
            phi,
            (a, b, c) => {
              match (phi(a, c), phi(b, c)) {
                (Some(x), Some(y)) => rule(x, y, a, b, c)
                _ => None
              }
            },
            samples,
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
/// 於定律表中查某候選之增益
pub fn law_find_gain(
  tbl : Array[LawCand],
  phi : String,
  comb : String,
  rule : String,
) -> Double? {
  for t in tbl {
    if t.cphi == phi && t.ccomb == comb && t.crule == rule {
      return Some(t.cgain)
    }
  }
  None
}

///|
/// 於定律表中查某候選之裁決
pub fn law_find(
  tbl : Array[LawCand],
  phi : String,
  comb : String,
  rule : String,
) -> Bool? {
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
    // N-32 新構造子之物化成本，與 sgram_cost 的實作逐一對應：
    //   Λᵏ：C(n,k)² 個 k×k 子式行列式
    SExt(a, k) => {
      let d = binom(a.sdim(), k).to_int64()
      let kk = k.to_int64()
      tmat(a) + d * d * tkappa() * kk * kk * kk / 100L
    }
    //   同餘：兩次 n×n 乘法
    STwist(a, _) => {
      let n = a.sdim().to_int64()
      tmat(a) + 2L * n * n * n
    }
    //   子空間：Sᵀ(GS)，n²m + nm²
    SSub(a, sm) => {
      let n = a.sdim().to_int64()
      let m = sm.mcols.to_int64()
      tmat(a) + n * n * m + n * m * m
    }
    //   ⊞：兩個 Kronecker 積再相加
    SKSum(a, b) => {
      let d = (a.sdim() * b.sdim()).to_int64()
      tmat(a) + tmat(b) + 2L * d * d
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
    // N-32 新構造子：符號成本模型尚未納入它們的分解律，
    // 故一律記為「物化後直接求逆」—— 這是保守估計（不會高估分解法之優勢）。
    other => {
      let d = other.sdim().to_int64()
      tmat(other) + tkappa() * d * d * d / 100L
    }
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
    SExt(a, k) => {
      let (ca, ba) = tmat2(a)
      let d = binom(a.sdim(), k).to_int64()
      let kk = k.to_int64()
      let w = wwords(ba)
      (ca + d * d * tkappa() * kk * kk * kk * w * w / 100L, kk * ba)
    }
    STwist(a, m) => {
      let (ca, ba) = tmat2(a)
      let n = a.sdim().to_int64()
      let bm = mat_bits(m)
      let w = wwords(ba)
      let wm = wwords(bm)
      (ca + 2L * n * n * n * w * wm, ba + 2L * bm)
    }
    SSub(a, sm) => {
      let (ca, ba) = tmat2(a)
      let n = a.sdim().to_int64()
      let mc = sm.mcols.to_int64()
      let bm = mat_bits(sm)
      let w = wwords(ba)
      let wm = wwords(bm)
      (ca + (n * n * mc + n * mc * mc) * w * wm, ba + 2L * bm)
    }
    SKSum(a, b) => {
      let (ca, ba) = tmat2(a)
      let (cb, bb) = tmat2(b)
      let d = (a.sdim() * b.sdim()).to_int64()
      let mx = if ba > bb { ba } else { bb }
      (ca + cb + 2L * d * d * wwords(ba) * wwords(bb), mx + 1L)
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
    // N-32 新構造子：同 tinv_dec，記為「物化後直接求逆」
    other => {
      let (c0, b0) = tmat2(other)
      let d = other.sdim().to_int64()
      let w = wwords(d * b0)
      (c0 + tkappa() * d * d * d * w * w / 100L, d * b0)
    }
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

// ---------------------------------------------------------------------------
// 【演算法 185】同餘律族（N-08 度量扭曲、N-09 子空間）
//
// 【定義】度量扭曲：G ↦ AᵀGA（A 非奇異）即同餘變換，對應基底變換。
//   子空間：S 為 n×k 含入映射（k ≤ n），誘導度量 G_U = SᵀGS。
//
// 【定理 185-1】det(AᵀGA) = det(A)²·det(G)。
// 【定理 185-2】(AᵀGA)⁻¹ = A⁻¹G⁻¹A⁻ᵀ。
// 【定理 185-3（Sylvester 慣性律）】A 非奇異時 inertia(AᵀGA) = inertia(G)。
// 【定理 185-4（子空間）】G_U = SᵀGS 正定 ⟺ S 單射（rank S = k）；
//   且 rank(SᵀGS) = rank(S) 當 G 正定。
//
// 【本族之特殊性 —— 一種新的「律」】
//   185-1／185-2 是**加速律**：有成本比可量。
//   185-3 卻是**不變量律**：它回報的不是「快多少」，而是「什麼被保持」。
//   先前 N 群的 LawVerdict 只有 (holds, 成本比) 兩個欄位，裝不下這種律。
//   本條因此把 N 群的律分成兩類，並說明為何成本比對不變量律無意義：
//   慣性指數沒有「分解法」可言 —— 它不是被算得更快，而是根本不用重算。
// ---------------------------------------------------------------------------

///|
/// 隨機非奇異上三角 ℚ 矩陣（det = 對角乘積 ≠ 0）
pub fn rand_invertible(rng : Rng, n : Int) -> Mat[Q] {
  Mat::build(n, n, (i, j) => {
    if i > j {
      Q::zero()
    } else if i == j {
      Q::of_int(rng.next_below(3) + 1)
    } else {
      Q::frac(rng.next_small(4), rng.next_range(1, 3))
    }
  })
}

///|
/// 同餘變換 AᵀGA（計入成本）
pub fn congruence(c : Cost, g : Mat[Q], a : Mat[Q]) -> Mat[Q] {
  qmul_cost(c, a.transpose(), qmul_cost(c, g, a))
}

// ---------------------------------------------------------------------------
// 【演算法 186】反律庫（N-14）
//
// 本庫之負面結果先前散落六處（N-04 ⊕ 不划算、N-08 同餘不划算、N-12 Hadamard
// 模型慘敗、N-13 之 29 條推翻、N-24 expm⊕ 低增益、N-10 線性冪反而惡化）。
// 散落的問題是：沒有任何機制保證它們「現在還成立」。
// 某次重構若讓基準實作退化，⊕ 的增益可能忽然變高，而沒有人會發現。
//
// 本條把它們收進單一登錄表，並且**每次執行都重新量測**：
// 每筆負面結果都附一個必須滿足的界，違反即失敗。
// 這把「我們誠實回報了壞消息」從一次性宣告變成可持續的回歸測試。
// ---------------------------------------------------------------------------

///|
/// 一筆負面結果之登錄
pub struct NegResult {
  nsrc : String
  nclaim : String
  nmeasured : Double
  nbound : Double
  nholds : Bool
}

///|
/// 【反律庫】逐筆重新量測，回傳登錄表
pub fn negative_registry() -> Array[NegResult] {
  let rng = ob_rng()
  let out : Array[NegResult] = []
  let sizes : Array[(Int, Int)] = [(2, 2), (3, 3), (4, 4)]
  // 1. ⊕ 求逆律成立但不划算（N-04）
  let vs = law_sum_inv(rng, sizes)
  out.push({
    nsrc: "N-04",
    nclaim: "⊕ 求逆律增益 ≈ 1（不划算）",
    nmeasured: vs.lgain(),
    nbound: 2.0,
    nholds: vs.holds && vs.lgain() < 2.0,
  })
  // 2. 同為 ⊗ 之增益必須遠高（對照組，確保上一筆不是基準退化造成的）
  let vk = law_kron_inv(rng, sizes)
  out.push({
    nsrc: "N-04",
    nclaim: "⊗ 增益 ÷ ⊕ 增益 ≥ 5（對照）",
    nmeasured: vk.lgain() / vs.lgain(),
    nbound: 5.0,
    nholds: vk.lgain() / vs.lgain() >= 5.0,
  })
  // 3. transpose 之 ⊗ 律成立但零收益（N-13 之 ×0.00 其實是計費假象，
  //    誠實計費後應恰為 ×1.00：兩側都只付一次 Kronecker 組裝）
  let a = rand_gram(rng, 4)
  let b = rand_gram(rng, 4)
  let cd = Cost::new()
  let _ld = qkron_cost(cd, a, b).transpose()
  let cf = Cost::new()
  let _lf = qkron_cost(cf, a.transpose(), b.transpose())
  let tr_ratio = Cost::ratio(cd, cf)
  out.push({
    nsrc: "N-13",
    nclaim: "transpose 之 ⊗ 律誠實計費後恰為 ×1（零收益）",
    nmeasured: tr_ratio,
    nbound: 1.05,
    nholds: tr_ratio < 1.05 && tr_ratio > 0.95,
  })
  // 4. Hadamard 位元模型劣於形狀模型（N-12）
  let mut e1 = 0.0
  let mut e2 = 0.0
  let mut cnt = 0
  for _t in 0..<6 {
    let e = rand_expr(rng, 2, 24)
    let (_s, wb, wf, _l, _d) = synth_compare(e)
    if wf <= 0L {
      continue
    }
    let meas = wb.to_double() / wf.to_double()
    e1 = e1 + fold_err(tinv_gain(e), meas)
    e2 = e2 + fold_err(tinv_gain2(e), meas)
    cnt = cnt + 1
  }
  let m1 = e1 / cnt.to_double()
  let m2 = e2 / cnt.to_double()
  out.push({
    nsrc: "N-12",
    nclaim: "Hadamard 位元模型之誤差大於形狀模型（更精密 ≠ 更準）",
    nmeasured: m2 / m1,
    nbound: 1.0,
    nholds: m2 > m1,
  })
  // 5. 搜尋引擎之推翻數必須多於成立數（N-13）
  // N-35：改用共用快取。此處網格與 law_grid_std() 相同，且本項只用
  //   「推翻數 > 成立數」這個與種子無關的計數，共用不改變結論。
  let tbl = law_search_std(rng)
  let mut nh = 0
  let mut nr = 0
  for t in tbl {
    if t.cholds {
      nh = nh + 1
    } else {
      nr = nr + 1
    }
  }
  out.push({
    nsrc: "N-13",
    nclaim: "搜尋引擎推翻數 > 成立數（具判別力）",
    nmeasured: nr.to_double() / nh.to_double(),
    nbound: 1.0,
    nholds: nr > nh,
  })
  // 6. 同餘分解不划算（N-08）
  let mut tb = 0L
  let mut tf = 0L
  for sz in [3, 4] {
    let g = rand_gram(rng, sz)
    let aa = rand_invertible(rng, sz)
    let c0 = Cost::new()
    let ga = congruence(c0, g, aa)
    let ci = Cost::new()
    let _x = qinv_gauss(ga, ci)
    let cj = Cost::new()
    match (qinv_gauss(aa, cj), qinv_gauss(g, cj)) {
      (Some(ia), Some(ig)) =>
        ignore(qmul_cost(cj, ia, qmul_cost(cj, ig, ia.transpose())))
      _ => ()
    }
    tb = tb + ci.wmul
    tf = tf + cj.wmul
  }
  let cg = tb.to_double() / tf.to_double()
  out.push({
    nsrc: "N-08",
    nclaim: "同餘分解不划算（增益 ≤ 1.5）",
    nmeasured: cg,
    nbound: 1.5,
    nholds: cg <= 1.5,
  })
  // 7. Sylvester–Franke 若用線性冪，增益會被右式拖累（N-10）
  let g7 = rand_gram(rng, 6)
  // N-35：原此處另建 C₃(g7)（20×20）並求其行列式，耗 492,444 字乘法，
  //   但本項之主張只比較 cl.wmul 與 cb.wmul 兩個冪法成本，該複合矩陣
  //   從未進入任何斷言 —— 純屬死碼，移除不改變本項之任何結論。
  let cl = Cost::new()
  let _r1 = qpow_cost(cl, qdet_gauss(g7, cl), sf_exponent(6, 3))
  let cb = Cost::new()
  let _r2 = qpow_fast(cb, qdet_gauss(g7, cb), sf_exponent(6, 3))
  let pow_ratio = cl.wmul.to_double() / cb.wmul.to_double()
  out.push({
    nsrc: "N-10",
    nclaim: "線性冪之成本高於二進位冪（右式會拖累整條律）",
    nmeasured: pow_ratio,
    nbound: 1.0,
    nholds: pow_ratio > 1.0,
  })
  out
}

// ---------------------------------------------------------------------------
// N-35：搜尋分層與效能整頓
// ---------------------------------------------------------------------------

///|
/// 標準搜尋網格。
///
/// 必含非對稱尺寸 (2,3)：命題 175-3 —— 若網格全為方形同尺寸，
/// `det/⊗/·`（少了指數的錯誤規則）會因 n = m 而僥倖通過。
pub fn law_grid_std() -> Array[(Int, Int)] {
  [(2, 2), (2, 3)]
}

///|
/// 全量網格，供 `cmd/lawsearch` 之一次性全掃描使用。
///
/// N-35 下修的根據：兩個網格對 72 個候選給出**逐條相同的裁決**（相異 0 條），
/// 此等價性由 `cmd/lawsearch` 每次全掃描時重新驗證。常規義務因此只需小網格。
pub fn law_grid_full() -> Array[(Int, Int)] {
  [(2, 2), (2, 3), (3, 3)]
}

///|
/// 搜尋結果之快取盒（長度 0 表示未算）。
///
/// N-13 與 N-26 原本各自以**完全相同的網格**跑一次完整搜尋（977 + 862 ms），
/// 第二次純屬重工。`ob_rng()` 為固定種子，兩次結果本就逐位元相同，
/// 共用不改變任何結論。
let law_cache : Array[Array[LawCand]] = []

///|
/// 實際跑過幾次完整搜尋（快取未命中次數）。供 N-35 自證去重確實生效。
let law_miss : Array[Int] = [0]

///|
/// 讀取快取未命中次數。
pub fn law_miss_count() -> Int {
  law_miss[0]
}

///|
/// 帶快取之標準搜尋（N-35）。
pub fn law_search_std(rng : Rng) -> Array[LawCand] {
  if law_cache.length() > 0 {
    return law_cache[0]
  }
  law_miss[0] = law_miss[0] + 1
  let t = law_search(rng, law_grid_std())
  law_cache.push(t)
  t
}

///|
/// 快取是否已命中過（供 N-35 義務自證「第二次確實沒有重跑」）。
pub fn law_cache_filled() -> Bool {
  law_cache.length() > 0
}

// ============================================================================
//  檔案 18：catalogue.mbt — 評審準則目錄（Evaluation-Criteria Catalogue）
//
//  每一條目 = 一條演算法 / 評審準則，並強制附帶：
//    定義 (deff) · 算式 (formula) · 命題或定理 (thm) · 證明要旨 (proof)
//    · 適用空間 (spaces) · 算術軌道 (track) · 可執行之義務自證 (run)
//
//  目錄條目數 ≥ 80（實際 168 條：A–J 基礎 140 條 + K/L/M 加速層 28 條），
//  全部可由 `moon run cmd/main` 逐條執行驗證。
// ============================================================================

///|
/// 一條評審準則 / 演算法之完整描述。
pub struct Algo {
  /// 條目編號（群組字母 + 序號）
  code : String
  /// 名稱（繁體中文）
  zh : String
  /// 類別
  cat : String
  /// 適用之空間或結構
  spaces : String
  /// 定義
  deff : String
  /// 算式
  formula : String
  /// 命題／定理
  thm : String
  /// 證明（要旨；完整論證見各原始碼檔案之區塊註解）
  proof : String
  /// 算術軌道：精確 ℚ／ℚ(i) 或 數值 ℝ
  track : String
  /// 義務自證（可執行）
  run : () -> Check
}

///|
/// 全部評審準則條目。
pub fn catalogue() -> Array[Algo] {
  let xs : Array[Algo] = []

  // ------------------------------------------------------------------
  // A 群：體、純量與核心工具（kernel.mbt / scalar.mbt / rational.mbt /
  //                          complex.mbt / quatspace.mbt）
  // ------------------------------------------------------------------
  xs.push({
    code: "A-01",
    zh: "確定性偽亂數產生器 xorshift64*",
    cat: "核心工具",
    spaces: "所有空間之取樣",
    deff: "狀態 s ∈ ℤ₂⁶⁴＼{0}，s ← s⊕(s≫12)，s ← s⊕(s≪25)，s ← s⊕(s≫27)，輸出 s·2685821657736338717。",
    formula: "x_{k+1} = T(x_k)，T 為 GF(2) 上之可逆線性變換再乘上奇數常數",
    thm: "命題：T 於 ℤ₂⁶⁴＼{0} 上為雙射，故序列不會落入 0；同種子產生相同序列（確定性可重現）。",
    proof: "三個 xorshift 皆為 GF(2)⁶⁴ 上之單位三角矩陣（對角為 1）故可逆；乘以奇數為 ℤ/2⁶⁴ 中之單位元，亦可逆。可逆變換之複合保持非零性。∎",
    track: "位元精確",
    run: ob_a01,
  })
  xs.push({
    code: "A-02",
    zh: "Euclid 最大公因數（BigInt）",
    cat: "核心工具",
    spaces: "ℚ 之正規化",
    deff: "gcd(a,0)=|a|；gcd(a,b)=gcd(b, a mod b)。",
    formula: "gcd(a,b)·lcm(a,b) = |ab|",
    thm: "定理：Euclid 演算法於有限步終止並回傳最大公因數。",
    proof: "|b| 嚴格遞減且非負 ⇒ 終止；由 (a,b) 與 (b, a mod b) 之公因數集合相同（因 a = qb + r）得正確性。∎",
    track: "精確 ℤ",
    run: ob_a02,
  })
  xs.push({
    code: "A-03",
    zh: "有理數體 ℚ（既約表示）",
    cat: "純量體",
    spaces: "全部精確軌道空間",
    deff: "Q = {p/q : p,q ∈ ℤ, q > 0, gcd(p,q)=1}，加法 p₁/q₁+p₂/q₂ = (p₁q₂+p₂q₁)/(q₁q₂) 後約分。",
    formula: "(F1)–(F9)：結合、交換、分配、單位元、逆元",
    thm: "定理：(ℚ,+,·) 為特徵 0 之有序體；本實作之正規化使相等判定 = 結構相等。",
    proof: "逐條驗證體公理（見 rational.mbt）；既約表示之唯一性由 gcd 與 q>0 保證，故 s_eq 可判定。∎",
    track: "精確 ℚ",
    run: ob_a03,
  })
  xs.push({
    code: "A-04",
    zh: "整數平方根 ⌊√a⌋（Newton 下取整）",
    cat: "核心工具",
    spaces: "ℚ 上之精確開方判定",
    deff: "r = max{ k ∈ ℕ : k² ≤ a }。",
    formula: "r² ≤ a < (r+1)²",
    thm: "命題：整數 Newton 迭代 x ← (x + a/x)/2 自 x₀ ≥ √a 起單調遞減收斂至 ⌊√a⌋。",
    proof: "AM–GM 給出 x_{k+1} ≥ √a；整數除法之下取整保證嚴格遞減直至不動點，於不動點處即滿足夾擠不等式。∎",
    track: "精確 ℤ",
    run: ob_a04,
  })
  xs.push({
    code: "A-05",
    zh: "Newton 法平方根（Double）",
    cat: "核心工具",
    spaces: "ℝ 軌道之範數",
    deff: "x_{k+1} = (x_k + a/x_k)/2，x₀ = max(1,a)。",
    formula: "|x̂² − a| ≤ 10⁻⁹·max(1,a)",
    thm: "定理：Newton 迭代對 f(x)=x²−a 為二次收斂；殘差憑證可事後檢查。",
    proof: "f 於 (0,∞) 上凸且 f′>0 ⇒ 自右側起單調遞減收斂；誤差 e_{k+1} = e_k²/(2x_k)。本實作直接驗證最終殘差。∎",
    track: "數值 ℝ",
    run: ob_a05,
  })
  xs.push({
    code: "A-06",
    zh: "Taylor 級數 sin / cos（含區間歸約）",
    cat: "核心工具",
    spaces: "DFT／旋轉角",
    deff: "先將 x 歸約至 [−π,π]，再取 sin x = Σ_{k≥0} (−1)^k x^{2k+1}/(2k+1)!。",
    formula: "sin²x + cos²x = 1；sin(x+y) = sin x cos y + cos x sin y",
    thm: "命題：截斷 N 項之誤差 ≤ |x|^{2N+1}/(2N+1)!；歸約後 |x| ≤ π 使誤差 < 10⁻¹⁶。",
    proof: "交錯級數餘項估計；加法定理由指數律 e^{i(x+y)} = e^{ix}e^{iy} 比較實虛部，於本實作以數值恆等式驗證。∎",
    track: "數值 ℝ",
    run: ob_a06,
  })
  xs.push({
    code: "A-07",
    zh: "四象限反正切 atan2",
    cat: "核心工具",
    spaces: "夾角計算",
    deff: "θ = atan2(y,x) ∈ (−π,π]，由級數 arctan + 象限修正組成。",
    formula: "r cos θ = x，r sin θ = y，r = √(x²+y²)",
    thm: "命題：atan2 為極座標映射之右逆（除原點外）。",
    proof: "以 |y/x| ≤ 1 之級數加上 arctan(t)+arctan(1/t)=π/2 之恆等式延拓；象限由 x,y 之符號決定。驗證以重建 (x,y) 之殘差為憑證。∎",
    track: "數值 ℝ",
    run: ob_a07,
  })
  xs.push({
    code: "A-08",
    zh: "快速冪（平方–乘法）",
    cat: "核心工具",
    spaces: "任意么半群",
    deff: "a^0 = 1；a^{2k} = (a^k)²；a^{2k+1} = a·(a^k)²。",
    formula: "a^{m+n} = a^m·a^n",
    thm: "命題：於任意么半群上正確，乘法次數 ≤ 2⌊log₂ n⌋。",
    proof: "對 n 之二進位長度歸納；指數律由結合律得。∎",
    track: "精確 ℚ",
    run: ob_a08,
  })
  xs.push({
    code: "A-09",
    zh: "複數體 ℚ(i)（Gauss 有理數）",
    cat: "純量體",
    spaces: "ℂⁿ、Hermitian 空間",
    deff: "z = a+bi，a,b ∈ ℚ；(a+bi)(c+di) = (ac−bd)+(ad+bc)i；N(z) = a²+b²。",
    formula: "z⁻¹ = ‾z/N(z)；N(zw) = N(z)N(w)",
    thm: "定理：ℚ(i) 為體；N 為乘法同態（Brahmagupta–Fibonacci 二平方恆等式）。",
    proof: "N(z) = z‾z，而共軛為環自同構 ⇒ N(zw) = zw‾z‾w = N(z)N(w)；z ≠ 0 ⇒ N(z) > 0 ⇒ 可逆。∎",
    track: "精確 ℚ(i)",
    run: ob_a09,
  })
  xs.push({
    code: "A-10",
    zh: "四元數代數 ℍ（Hamilton 乘法）",
    cat: "純量代數",
    spaces: "ℍⁿ、SO(3)",
    deff: "q = w+xi+yj+zk，i²=j²=k²=ijk=−1，乘法按分配律展開。",
    formula: "(w₁,v₁)(w₂,v₂) = (w₁w₂ − ⟨v₁,v₂⟩, w₁v₂ + w₂v₁ + v₁×v₂)",
    thm: "定理：ℍ 為 4 維實結合可除代數，非交換；其中心為 ℝ。",
    proof: "結合律由基元關係逐項驗證（本義務以隨機 ℚ 四元數三元組精確檢驗）；可除性由 q⁻¹ = ‾q/N(q) 與 N(q) > 0 (q≠0) 得。∎",
    track: "精確 ℚ",
    run: ob_a10,
  })

  // ------------------------------------------------------------------
  // B 群：空間公理檢驗（space.mbt 演算法 008–010 × 13 類空間）
  // ------------------------------------------------------------------
  xs.push({
    code: "B-01",
    zh: "標準歐幾里得空間 ℚ⁴ 之全公理",
    cat: "空間公理",
    spaces: "S1 𝔽ⁿ",
    deff: "V = ℚ⁴，逐分量加法與純量乘法，⟨x,y⟩ = Σ xᵢyᵢ。",
    formula: "V1–V8（向量空間）、V9–V11（推論）、B1–B5（基底同構）、I1–I7（內積）",
    thm: "定理：(ℚ⁴, +, ·, ⟨,⟩) 為 4 維內積空間，標準基為標準正交基。",
    proof: "逐分量化約至體公理；正定性由 Σxᵢ² = 0 ⟺ ∀i xᵢ=0（ℚ 為形式實體）。隨機實例檢驗附 Schwartz–Zippel 界。∎",
    track: "精確 ℚ",
    run: ob_b01,
  })
  xs.push({
    code: "B-02",
    zh: "有限集合上之加權函數空間 ℚ^S",
    cat: "空間公理",
    spaces: "S3 函數空間",
    deff: "V = {f : S → ℚ}，|S| = 5；⟨f,g⟩ = Σ_{s∈S} w(s) f(s)‾g(s)，w(s) > 0。",
    formula: "⟨f,g⟩_w = Σ w_s f_s ‾g_s；dim = |S|",
    thm: "定理：w 逐點為正 ⟺ ⟨,⟩_w 為內積；δ 函數族為正交基，‖δ_s‖² = w_s。",
    proof: "正定性：⟨f,f⟩ = Σ w_s|f_s|² = 0 且 w_s>0 ⇒ f ≡ 0。其餘公理逐點化約。∎",
    track: "精確 ℚ",
    run: ob_b02,
  })
  xs.push({
    code: "B-03",
    zh: "對稱矩陣空間 Sym₄ 之全公理",
    cat: "空間公理",
    spaces: "S6 Sym_n",
    deff: "Sym_n = {A ∈ M_n : Aᵀ = A}，⟨A,B⟩ = tr(AB*)（Frobenius）。",
    formula: "dim Sym_n = n(n+1)/2；基底 {E_ii} ∪ {E_ij+E_ji}",
    thm: "定理：Sym_n 為 M_n 之線性子空間且對 Frobenius 內積封閉；維數 n(n+1)/2。",
    proof: "對稱條件為線性方程組 ⇒ 子空間；上三角位置（含對角）之自由度計數給出維數；Frobenius 內積之限制仍正定。∎",
    track: "精確 ℚ",
    run: ob_b03,
  })
  xs.push({
    code: "B-04",
    zh: "複 Hermitian 矩陣空間 Herm₃(ℂ) 之全公理",
    cat: "空間公理",
    spaces: "S9 Herm_n",
    deff: "Herm_n = {A ∈ M_n(ℂ) : A* = A}，視為 ℝ-向量空間，⟨A,B⟩ = Re tr(AB*)。",
    formula: "dim_ℝ Herm_n = n²",
    thm: "定理：Herm_n 非 ℂ-子空間（iA 反 Hermitian），但為 n² 維實內積空間。",
    proof: "A*=A 為實線性（非複線性）條件；實維數 = n（對角實數）+ 2·n(n−1)/2（上三角複數）= n²。∎",
    track: "精確 ℚ(i)/ℚ",
    run: ob_b04,
  })
  xs.push({
    code: "B-05",
    zh: "對角矩陣空間 Diag₅ 之全公理",
    cat: "空間公理",
    spaces: "S8 Diag_n",
    deff: "Diag_n = {A : A_{ij} = 0 (i≠j)}，⟨A,B⟩ = tr(AB*)。",
    formula: "dim = n；Diag_n ≅ 𝔽ⁿ 為等距同構",
    thm: "定理：Diag_n 為交換子代數，且與 𝔽ⁿ 等距同構。",
    proof: "座標映射 A ↦ (a₁₁,…,a_nn) 為線性雙射且保內積，故為等距同構；乘法交換由逐分量乘積得。∎",
    track: "精確 ℚ",
    run: ob_b05,
  })
  xs.push({
    code: "B-06",
    zh: "多項式空間 P（L²[−1,1]）之全公理",
    cat: "空間公理",
    spaces: "S11 多項式空間",
    deff: "V = {p : deg p < n}，⟨p,q⟩ = ∫₋₁¹ p(x)‾q(x) dx，以精確有理矩 m_k = ∫x^k 計算。",
    formula: "⟨xⁱ,xʲ⟩ = (1+(−1)^{i+j})/(i+j+1)",
    thm: "定理：此為內積（正定性由連續函數之 L² 範數），Gram 矩陣正定。",
    proof: "⟨p,p⟩ = ∫p² ≥ 0，等號 ⟺ p ≡ 0（p 連續且為多項式，零點有限）。有理矩使計算精確無誤差。∎",
    track: "精確 ℚ",
    run: ob_b06,
  })
  xs.push({
    code: "B-07",
    zh: "多變量多項式空間（Bombieri 內積）之全公理",
    cat: "空間公理",
    spaces: "S14 多變量多項式",
    deff: "V = span{xᵅ : |α| ≤ d}（m 個變數），⟨xᵅ,xᵝ⟩ = δ_{αβ}·α!/|α|!（Bombieri 權重）。",
    formula: "⟨f,g⟩_B = Σ_α (α!/|α|!) f_α ‾g_α",
    thm: "定理：Bombieri 內積為內積，且於正交群 O(m) 之變數替換下不變（見 E-16）。",
    proof: "權重為正 ⇒ 正定；不變性為 Bombieri–Beauzamy–Dégot 定理，本專案以精確 ℚ 實例驗證。∎",
    track: "精確 ℚ",
    run: ob_b07,
  })
  xs.push({
    code: "B-08",
    zh: "四元數空間 ℍ² 之全公理",
    cat: "空間公理",
    spaces: "S16 ℍⁿ",
    deff: "V = ℍⁿ 視為 4n 維實向量空間，⟨p,q⟩ = Σᵢ Re(‾pᵢqᵢ)。",
    formula: "dim_ℝ ℍⁿ = 4n；⟨p,q⟩ = Σ (w_iw_i' + x_ix_i' + y_iy_i' + z_iz_i')",
    thm: "定理：ℍⁿ 配此內積等距同構於 ℝ^{4n}。",
    proof: "Re(‾pq) 於 ℍ ≅ ℝ⁴ 下即標準內積；取分量展開即得。∎",
    track: "精確 ℚ",
    run: ob_b08,
  })
  xs.push({
    code: "B-09",
    zh: "外冪 Λ²(ℚ⁴) 之全公理",
    cat: "空間公理",
    spaces: "S17 Λᵏ(𝔽ⁿ)",
    deff: "基底 {e_I : |I| = k}，⟨e_I,e_J⟩ = δ_{IJ}。",
    formula: "dim Λᵏ(𝔽ⁿ) = C(n,k)",
    thm: "定理：Λᵏ 為 C(n,k) 維內積空間，且與可分解元之 Gram 行列式公式相容（G-03）。",
    proof: "子集基底之唯一性給出維數；內積由基底正交性定義，正定顯然；相容性見定理 E2（exterior.mbt）。∎",
    track: "精確 ℚ",
    run: ob_b09,
  })
  xs.push({
    code: "B-10",
    zh: "全外代數 Λ(ℚ³) 之全公理",
    cat: "空間公理",
    spaces: "S18 Λ(𝔽ⁿ)",
    deff: "Λ(𝔽ⁿ) = ⊕_{k=0}^n Λᵏ(𝔽ⁿ)，以位元遮罩索引，dim = 2ⁿ。",
    formula: "⟨e_I,e_J⟩ = δ_{IJ}（分次正交）",
    thm: "定理：Λ(𝔽ⁿ) 為 2ⁿ 維分次結合代數兼內積空間，不同分次互相正交。",
    proof: "分次直和之正交性由基底定義；代數結構見 G-02。∎",
    track: "精確 ℚ",
    run: ob_b10,
  })
  xs.push({
    code: "B-11",
    zh: "列空間 col(A) 作為子空間之全公理",
    cat: "空間公理",
    spaces: "S4 列空間／子空間",
    deff: "col(A) = span{A 之各行}，以主元行為基底，承襲環繞空間之內積。",
    formula: "dim col(A) = rank A",
    thm: "定理：子空間承襲之型式仍為內積；主元行構成基底。",
    proof: "限制正定型式於子空間仍正定；RREF 之主元行線性獨立且張成同一列空間（演算法 013 之推論）。∎",
    track: "精確 ℚ",
    run: ob_b11,
  })
  xs.push({
    code: "B-12",
    zh: "反對稱空間 so(4) 與跡零空間 sl₃ 之全公理",
    cat: "空間公理",
    spaces: "S7 Skew_n、S10 sl_n",
    deff: "so(n) = {A : Aᵀ = −A}；sl_n = {A : tr A = 0}。",
    formula: "dim so(n) = n(n−1)/2；dim sl_n = n²−1",
    thm: "定理：兩者皆為 M_n 之子空間，且皆於李括號下封閉（李代數）。",
    proof: "線性條件 ⇒ 子空間；[A,B]ᵀ = −[A,B]（反對稱）與 tr[A,B] = 0（跡之循環性）。∎",
    track: "精確 ℚ",
    run: ob_b12,
  })
  xs.push({
    code: "B-13",
    zh: "么正空間 ℂ³（Hermitian 內積）之全公理",
    cat: "空間公理",
    spaces: "S2 ℂⁿ",
    deff: "V = ℚ(i)³，⟨x,y⟩ = Σ xᵢ‾yᵢ（第一變數線性、第二變數共軛線性）。",
    formula: "⟨y,x⟩ = ‾⟨x,y⟩；⟨x,x⟩ ∈ ℝ_{≥0}",
    thm: "定理：Hermitian 型式之共軛對稱使 ⟨x,x⟩ 必為實數，正定性於 ℚ(i) 上可判定。",
    proof: "⟨x,x⟩ = Σ|xᵢ|² = Σ(aᵢ²+bᵢ²) ∈ ℚ_{≥0}，等於 0 ⟺ x = 0。∎",
    track: "精確 ℚ(i)",
    run: ob_b13,
  })
  xs.push({
    code: "B-14",
    zh: "Gram 矩陣之 Hermitian 正定性（Sylvester 判準）",
    cat: "空間公理",
    spaces: "S11, S6, S16, S14",
    deff: "G_{ij} = ⟨bᵢ,bⱼ⟩；Sylvester：所有順序主子式 > 0 ⟺ 正定。",
    formula: "det G_k > 0, k = 1..n",
    thm: "定理：{bᵢ} 為基底 ⟺ Gram 正定；此即『內積空間之座標化』之充要條件。",
    proof: "x*Gx = ⟨Σxᵢbᵢ, Σxⱼbⱼ⟩ ≥ 0 且等號 ⟺ Σxᵢbᵢ = 0 ⟺ x = 0（基底）。Sylvester 判準由主子式歸納（LDL 分解之樞軸正性）。∎",
    track: "精確 ℚ",
    run: ob_b14,
  })
  xs.push({
    code: "B-15",
    zh: "維數公式 dim(U+W) + dim(U∩W) = dim U + dim W",
    cat: "空間公理",
    spaces: "子空間格",
    deff: "U+W = {u+w}；U∩W 由齊次系統 [U | −W]z = 0 之解空間投影而得。",
    formula: "dim(U+W) + dim(U∩W) = dim U + dim W",
    thm: "定理（Grassmann）：有限維子空間之維數公式。",
    proof: "取 U∩W 之基底延拓為 U 與 W 之基底，驗證三者之併為 U+W 之基底。本義務以兩個獨立演算法（秩計算 vs 零空間投影）交叉驗證。∎",
    track: "精確 ℚ",
    run: ob_b15,
  })

  // ------------------------------------------------------------------
  // C 群：矩陣核心演算法（matrix.mbt 演算法 011–030）
  // ------------------------------------------------------------------
  xs.push({
    code: "C-01",
    zh: "矩陣乘法與環結構",
    cat: "矩陣演算法",
    spaces: "M_{m×n}(𝔽)",
    deff: "(AB)_{ij} = Σ_k A_{ik}B_{kj}。",
    formula: "(AB)C = A(BC)；A(B+D) = AB+AD；AI = A",
    thm: "定理：M_n(𝔽) 為含單位元之結合環；乘法對應線性映射之複合。",
    proof: "結合律由求和次序交換（有限和）得；分配律由體之分配律逐項得。∎",
    track: "精確 ℚ",
    run: ob_c01,
  })
  xs.push({
    code: "C-02",
    zh: "轉置與共軛轉置之反序律",
    cat: "矩陣演算法",
    spaces: "M_{m×n}(𝔽), M(ℂ)",
    deff: "(Aᵀ)_{ij} = A_{ji}；(A*)_{ij} = ‾A_{ji}。",
    formula: "(AB)ᵀ = BᵀAᵀ；(AB)* = B*A*",
    thm: "命題：轉置為反自同構；共軛轉置為共軛線性反自同構。",
    proof: "((AB)ᵀ)_{ij} = Σ_k A_{jk}B_{ki} = Σ_k (Bᵀ)_{ik}(Aᵀ)_{kj}。共軛版本再用 ‾(zw)=‾z‾w。∎",
    track: "精確 ℚ/ℚ(i)",
    run: ob_c02,
  })
  xs.push({
    code: "C-03",
    zh: "Gauss–Jordan 消去與 RREF",
    cat: "矩陣演算法",
    spaces: "M_{m×n}(𝔽)",
    deff: "以初等列運算化為列化簡階梯形 R，主元為 1 且其所在行其餘元素為 0。",
    formula: "R = EA，E 可逆；ker A = ker R；row A = row R",
    thm: "定理：RREF 存在且唯一；rank = 主元數；RREF 為冪等運算。",
    proof: "三類初等列運算對應可逆矩陣；唯一性由主元位置與列空間決定。本義務驗證冪等性與零空間保持。∎",
    track: "精確 ℚ",
    run: ob_c03,
  })
  xs.push({
    code: "C-04",
    zh: "秩與秩–零化度定理",
    cat: "矩陣演算法",
    spaces: "M_{m×n}(𝔽)",
    deff: "rank A = RREF 之主元數；nullity = dim ker A。",
    formula: "rank A + nullity A = n；rank A = rank Aᵀ = rank AᵀA",
    thm: "定理（秩–零化度）：dim im T + dim ker T = dim V。",
    proof: "自由變數對應零空間基底、主元變數對應像空間基底；rank A = rank AᵀA 因 ker A = ker AᵀA（實體上 ‖Ax‖² = xᵀAᵀAx）。∎",
    track: "精確 ℚ",
    run: ob_c04,
  })
  xs.push({
    code: "C-05",
    zh: "行列式（消去法／樞軸乘積）",
    cat: "矩陣演算法",
    spaces: "M_n(𝔽)",
    deff: "det A = sign(σ)·Π 樞軸（由 LU/消去過程取得）。",
    formula: "det A = (−1)^{換列次數}·Π u_ii",
    thm: "定理：行列式為交錯多線性型式，由 det I = 1 唯一決定。",
    proof: "初等列運算對行列式之作用（換列變號、倍乘按比例、加倍數不變）；上三角矩陣之行列式為對角乘積。∎",
    track: "精確 ℚ",
    run: ob_c05,
  })
  xs.push({
    code: "C-06",
    zh: "行列式（Laplace 餘因子展開）",
    cat: "矩陣演算法",
    spaces: "M_n(𝔽)",
    deff: "det A = Σ_j (−1)^{i+j} a_{ij} M_{ij}（沿第 i 列展開）。",
    formula: "det A = Σ_{σ∈S_n} sgn(σ) Π aᵢ_{σ(i)}",
    thm: "定理：Laplace 展開與消去法結果相同（兩種獨立演算法之交叉驗證）。",
    proof: "兩者皆滿足交錯多線性與 det I = 1，由唯一性定理相等。本義務以隨機 ℚ 矩陣逐例驗證。∎",
    track: "精確 ℚ",
    run: ob_c05,
  })
  xs.push({
    code: "C-07",
    zh: "行列式之乘性",
    cat: "矩陣演算法",
    spaces: "M_n(𝔽)",
    deff: "det : M_n → 𝔽。",
    formula: "det(AB) = det A·det B；det Aᵀ = det A",
    thm: "定理：det 為么半群同態 (M_n,·) → (𝔽,·)；GL_n 為其核之補。",
    proof: "固定 B，A ↦ det(AB) 為 A 之交錯多線性型式，故等於 c·det A，取 A = I 得 c = det B。∎",
    track: "精確 ℚ",
    run: ob_c07,
  })
  xs.push({
    code: "C-08",
    zh: "反矩陣（Gauss–Jordan）",
    cat: "矩陣演算法",
    spaces: "GL_n(𝔽)",
    deff: "對 [A | I] 作 RREF，若左半為 I 則右半為 A⁻¹。",
    formula: "AA⁻¹ = A⁻¹A = I；(AB)⁻¹ = B⁻¹A⁻¹",
    thm: "定理：A 可逆 ⟺ rank A = n ⟺ det A ≠ 0。",
    proof: "RREF 之可逆列運算 E 滿足 EA = I ⇒ E = A⁻¹；反序律由結合律驗證。∎",
    track: "精確 ℚ",
    run: ob_c08,
  })
  xs.push({
    code: "C-09",
    zh: "線性方程組與 Rouché–Capelli 定理",
    cat: "矩陣演算法",
    spaces: "M_{m×n}(𝔽)",
    deff: "msolve(A,b) 回傳 (相容性, 特解, 零空間基底)。",
    formula: "Ax = b 相容 ⟺ rank A = rank[A|b]；通解 = 特解 + ker A",
    thm: "定理（Rouché–Capelli）：解集為仿射子空間，維數 = n − rank A。",
    proof: "增廣矩陣之 RREF 若出現 [0 … 0 | c], c≠0 則不相容；否則由自由變數參數化解集。∎",
    track: "精確 ℚ",
    run: ob_c09,
  })
  xs.push({
    code: "C-10",
    zh: "零空間與列／行空間基底",
    cat: "矩陣演算法",
    spaces: "四基本子空間",
    deff: "mnullspace／mcolspace／mrowspace 由 RREF 之自由變數與主元行構造。",
    formula: "dim ker A = n − r；dim col A = dim row A = r",
    thm: "定理：四基本子空間之維數為 r, n−r, r, m−r。",
    proof: "由 RREF 之結構直接讀出；基底之線性獨立性由主元位置保證。∎",
    track: "精確 ℚ",
    run: ob_c10,
  })
  xs.push({
    code: "C-11",
    zh: "四基本子空間之正交分解",
    cat: "矩陣演算法",
    spaces: "𝔽ⁿ = row A ⊕ ker A",
    deff: "row(A) ⊥ ker(A)，col(A) ⊥ ker(Aᵀ)。",
    formula: "𝔽ⁿ = row A ⊥⊕ ker A；𝔽^m = col A ⊥⊕ ker Aᵀ",
    thm: "定理（線性代數基本定理）：上述兩組為正交直和分解。",
    proof: "x ∈ ker A ⟺ 每一列與 x 內積為 0 ⟺ x ⊥ row A；維數相加為 n 故為直和。∎",
    track: "精確 ℚ",
    run: ob_c10,
  })
  xs.push({
    code: "C-12",
    zh: "LU 分解（部分樞軸）",
    cat: "矩陣演算法",
    spaces: "M_n(𝔽)",
    deff: "PA = LU，L 單位下三角，U 上三角，P 為置換。",
    formula: "det A = (−1)^{swaps}·Π u_ii",
    thm: "定理：任意方陣經列置換後存在 LU 分解；可逆時 L,U 唯一。",
    proof: "對行歸納消去；部分樞軸保證主元非零（若存在）。行列式公式由三角矩陣性質與置換符號得。∎",
    track: "精確 ℚ",
    run: ob_c12,
  })
  xs.push({
    code: "C-13",
    zh: "Kronecker 積與混合積律",
    cat: "矩陣演算法",
    spaces: "張量積空間",
    deff: "(A⊗B)_{(i,k),(j,l)} = A_{ij}B_{kl}。",
    formula: "(A⊗B)(C⊗D) = AC⊗BD；tr(A⊗B) = trA·trB；det(A⊗B) = (detA)^{n_B}(detB)^{n_A}",
    thm: "定理：⊗ 為雙線性、結合，且與乘法相容（函子性）。",
    proof: "混合積律由指標直接展開；det 公式由 A⊗B = (A⊗I)(I⊗B) 與相似變換之行列式乘性得。∎",
    track: "精確 ℚ",
    run: ob_c13,
  })
  xs.push({
    code: "C-14",
    zh: "vec 運算與 Sylvester 方程之線性化",
    cat: "矩陣演算法",
    spaces: "Hom 空間",
    deff: "vec(X) 為按行堆疊（column-stacking）。",
    formula: "vec(AXB) = (Bᵀ⊗A)vec X",
    thm: "定理：矩陣方程可線性化為 Kronecker 系統；unvec∘vec = id。",
    proof: "逐元素比較 (AXB)_{ij} = Σ_{k,l} A_{ik}X_{kl}B_{lj} 與 Kronecker 積之指標排列。∎",
    track: "精確 ℚ",
    run: ob_c14,
  })
  xs.push({
    code: "C-15",
    zh: "Schur 補與分塊行列式",
    cat: "矩陣演算法",
    spaces: "分塊矩陣",
    deff: "M = [[A,B],[C,D]]，S = D − CA⁻¹B。",
    formula: "det M = det A · det S",
    thm: "定理：A 可逆時分塊 LU 分解 M = [[I,0],[CA⁻¹,I]][[A,B],[0,S]]。",
    proof: "直接相乘驗證分解；取行列式並用三角分塊矩陣之行列式公式。∎",
    track: "精確 ℚ",
    run: ob_c15,
  })
  xs.push({
    code: "C-16",
    zh: "Faddeev–LeVerrier 特徵多項式",
    cat: "矩陣演算法",
    spaces: "M_n(𝔽)",
    deff: "遞推 M₀=0, M_k = A M_{k−1} + c_{n−k+1}I，c_{n−k} = −tr(A M_k)/k。",
    formula: "χ_A(λ) = det(λI − A) = λⁿ + c_{n−1}λ^{n−1} + … + c₀",
    thm: "定理：c_{n−1} = −tr A，c₀ = (−1)ⁿ det A，且演算法於任意特徵 0 體上正確。",
    proof: "由 Newton 恆等式連結冪和 tr(A^k) 與初等對稱多項式（特徵值之對稱函數）。∎",
    track: "精確 ℚ",
    run: ob_c16,
  })
  xs.push({
    code: "C-17",
    zh: "Cayley–Hamilton 定理",
    cat: "矩陣演算法",
    spaces: "M_n(𝔽)",
    deff: "將 χ_A 之係數代入矩陣多項式。",
    formula: "χ_A(A) = 0",
    thm: "定理：每個方陣滿足自身之特徵多項式。",
    proof: "由 adj(λI−A)(λI−A) = χ_A(λ)I 比較 λ 之冪次係數（多項式矩陣恆等式）。本義務逐例以精確 ℚ 驗證。∎",
    track: "精確 ℚ",
    run: ob_c16,
  })
  xs.push({
    code: "C-18",
    zh: "伴隨矩陣（古典 adjugate）",
    cat: "矩陣演算法",
    spaces: "M_n(𝔽)",
    deff: "adj(A)_{ij} = (−1)^{i+j} M_{ji}（餘因子轉置）。",
    formula: "A·adj A = adj A·A = (det A)·I",
    thm: "定理：A 可逆 ⟺ det A ≠ 0，且 A⁻¹ = adj A/det A。",
    proof: "Laplace 展開沿第 i 列給出對角項 det A；交錯展開（用另一列之餘因子）給出 0。∎",
    track: "精確 ℚ",
    run: ob_c18,
  })
  xs.push({
    code: "C-19",
    zh: "Cramer 法則",
    cat: "矩陣演算法",
    spaces: "GL_n(𝔽)",
    deff: "xⱼ = det(A_j)/det(A)，A_j 為以 b 取代第 j 行。",
    formula: "x = A⁻¹b = adj(A)b/det A",
    thm: "定理：方陣可逆時解唯一且由行列式商給出。",
    proof: "由 A·adj A = (det A)I 左乘 b；或由行列式之多線性展開 det(A_j)。∎",
    track: "精確 ℚ",
    run: ob_c18,
  })
  xs.push({
    code: "C-20",
    zh: "矩陣冪與 Cayley 變換",
    cat: "矩陣演算法",
    spaces: "SO(n)、so(n)",
    deff: "mpow 以平方–乘法計算；Cayley(S) = (I−S)(I+S)⁻¹。",
    formula: "A^{m+n} = A^mA^n；S = −Sᵀ ⇒ Q = Cayley(S) ∈ SO(n)",
    thm: "定理：Cayley 變換為 so(n) 至 SO(n)（不含特徵值 −1 者）之有理雙射。",
    proof: "QᵀQ = (I+S)⁻ᵀ(I−S)ᵀ(I−S)(I+S)⁻¹，利用 Sᵀ=−S 與 (I−S),(I+S) 可交換即得 I；det Q = 1 由連續性／直接計算。此變換為有理運算，故於 ℚ 上精確產生正交矩陣。∎",
    track: "精確 ℚ",
    run: ob_c20,
  })

  // ------------------------------------------------------------------
  // D 群：抽象內積空間演算法（ipalgo.mbt 演算法 061–080）
  // ------------------------------------------------------------------
  xs.push({
    code: "D-01",
    zh: "Gram–Schmidt 正交化（經典）",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "u₁ = x₁，u_k = x_k − Σ_{j<k} (⟨x_k,u_j⟩/⟨u_j,u_j⟩)u_j。",
    formula: "x_k = u_k + Σ_{j<k} r_{jk}u_j（抽象 QR 分解）",
    thm: "定理：span{u₁..u_k} = span{x₁..x_k} 且 uᵢ ⊥ uⱼ (i≠j)。",
    proof: "對 k 歸納：⟨u_k,u_j⟩ = ⟨x_k,u_j⟩ − ⟨x_k,u_j⟩ = 0；轉換矩陣為單位上三角故可逆。∎",
    track: "精確 ℚ",
    run: ob_d01,
  })
  xs.push({
    code: "D-02",
    zh: "改良 Gram–Schmidt（MGS）",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "逐步自剩餘向量扣除已算出之分量。",
    formula: "x_j ← x_j − (⟨x_j,u_k⟩/⟨u_k,u_k⟩)u_k（k 遞增）",
    thm: "定理：精確算術下 MGS ≡ CGS；浮點下正交性損失 O(εκ) 對 O(εκ²)（Björck 1967）。",
    proof: "代數上兩者為同一組遞推之不同結合次序，於精確體上相等（本義務逐項驗證）；數值差異見 H-24。∎",
    track: "精確 ℚ",
    run: ob_d02,
  })
  xs.push({
    code: "D-03",
    zh: "標準正交化與體之可開方性",
    cat: "內積演算法",
    spaces: "ℚⁿ vs ℝⁿ",
    deff: "e_k = u_k/‖u_k‖，需 √⟨u_k,u_k⟩ ∈ 𝔽。",
    formula: "⟨eᵢ,eⱼ⟩ = δᵢⱼ",
    thm: "定理：ℚ 非實閉體，標準正交基一般不存在（√2 ∉ ℚ）；ℝ 上恆存在。",
    proof: "若 ‖u‖² = 2 則 ‖u‖ ∉ ℚ（√2 無理）。故精確軌道只作正交化，正規化留給 ℝ 軌道。本義務同時驗證 ℚ 失敗與 ℝ 成功。∎",
    track: "精確 ℚ + 數值 ℝ",
    run: ob_d03,
  })
  xs.push({
    code: "D-04",
    zh: "Gram 行列式、k 維體積與 Hadamard 不等式",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "G(x₁..x_k)_{ij} = ⟨xᵢ,xⱼ⟩；vol_k = √det G。",
    formula: "0 ≤ det G ≤ Π‖xᵢ‖²；det G = 0 ⟺ 線性相依",
    thm: "定理：Gram 行列式為平行多面體體積平方；Hadamard 不等式為其上界。",
    proof: "G = B*B（B 為座標矩陣）⇒ det G = |det B|² ≥ 0；正交化後對角化給出 det G = Π‖uᵢ‖² ≤ Π‖xᵢ‖²（因 ‖uᵢ‖ ≤ ‖xᵢ‖）。∎",
    track: "精確 ℚ",
    run: ob_d04,
  })
  xs.push({
    code: "D-05",
    zh: "正交投影與最佳逼近定理",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "P_W x = Σcⱼwⱼ，c 解正規方程 Gc = b，b_i = ⟨x,wᵢ⟩。",
    formula: "⟨x − P_Wx, w⟩ = 0 ∀w ∈ W；‖x‖² = ‖P_Wx‖² + ‖x−P_Wx‖²",
    thm: "定理（最佳逼近）：存在唯一 w₀ ∈ W 使 ‖x−w₀‖ 最小，且其特徵為殘差 ⊥ W。",
    proof: "正交條件給出 Gram 系統（可逆）⇒ 唯一解；∀w, ‖x−w‖² = ‖x−w₀‖² + ‖w₀−w‖² ≥ ‖x−w₀‖²。∎",
    track: "精確 ℚ",
    run: ob_d05,
  })
  xs.push({
    code: "D-06",
    zh: "點到子空間之距離",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "d(x,W) = ‖x − P_Wx‖。",
    formula: "d(x,W)² = det G(w₁..w_k,x)/det G(w₁..w_k)",
    thm: "命題：d(x,W) = 0 ⟺ x ∈ W；W₁ ⊆ W₂ ⇒ d(x,W₂) ≤ d(x,W₁)。",
    proof: "由最佳逼近定理與投影之單調性（較大子空間之最小值不大於較小者）。∎",
    track: "精確 ℚ",
    run: ob_d06,
  })
  xs.push({
    code: "D-07",
    zh: "投影矩陣之代數特徵",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "[P]_{·j} = coord(P_W b_j)。",
    formula: "P² = P；P*G = GP；rank P = tr P = dim W",
    thm: "定理：P 為正交投影 ⟺ P 冪等且關於 G 自伴。",
    proof: "冪等性由 P_W|_W = id；自伴性由 ⟨Px,y⟩ = ⟨Px,Py⟩ = ⟨x,Py⟩。跡 = 秩因 P 之特徵值僅 0,1。∎",
    track: "精確 ℚ",
    run: ob_d07,
  })
  xs.push({
    code: "D-08",
    zh: "Riesz 表示定理",
    cat: "內積演算法",
    spaces: "任意有限維 IPSpace",
    deff: "由 φ 之對偶座標 c_i = φ(bᵢ) 解 ‾v = G⁻¹c。",
    formula: "φ(x) = ⟨x, v_φ⟩ ∀x；‖φ‖ = ‖v_φ‖",
    thm: "定理：φ ↦ v_φ 為 V* → V 之共軛線性等距雙射。",
    proof: "存在性由標準正交基 v_φ = Σ‾φ(eᵢ)eᵢ；唯一性由正定性。一般基底下化為 Gram 系統。∎",
    track: "精確 ℚ/ℚ(i)",
    run: ob_d08,
  })
  xs.push({
    code: "D-09",
    zh: "伴隨算子之矩陣公式",
    cat: "內積演算法",
    spaces: "IPSpace 之間的線性映射",
    deff: "T* 由 ⟨Tx,y⟩_W = ⟨x,T*y⟩_V 定義。",
    formula: "[T*] = G_V⁻¹ [T]* G_W",
    thm: "定理：有限維時伴隨存在且唯一；標準正交基下退化為共軛轉置。",
    proof: "⟨Tx,y⟩ = xᵀAᵀG_W‾y，⟨x,T*y⟩ = xᵀG_V‾B‾y，比較得 B = G_V⁻¹A*G_W。∎",
    track: "精確 ℚ/ℚ(i)",
    run: ob_d09,
  })
  xs.push({
    code: "D-10",
    zh: "Fourier 係數與合成",
    cat: "內積演算法",
    spaces: "具標準正交基之空間",
    deff: "ĉᵢ = ⟨x,eᵢ⟩；合成 Σĉᵢeᵢ。",
    formula: "x = Σᵢ ⟨x,eᵢ⟩ eᵢ",
    thm: "定理：標準正交基下座標即 Fourier 係數（抽象 Fourier 展開）。",
    proof: "對 x = Σaᵢeᵢ 取 ⟨·,eⱼ⟩ 得 aⱼ = ⟨x,eⱼ⟩。義務以 Cayley 變換造之有理正交基精確驗證。∎",
    track: "精確 ℚ",
    run: ob_d10,
  })
  xs.push({
    code: "D-11",
    zh: "Bessel 不等式",
    cat: "內積演算法",
    spaces: "具正交族之空間",
    deff: "對標準正交族 {e₁..e_k}（不必完備）。",
    formula: "Σᵢ|⟨x,eᵢ⟩|² ≤ ‖x‖²",
    thm: "定理（Bessel）：部分和不超過範數平方；差值 = 殘差範數平方。",
    proof: "0 ≤ ‖x − Σ⟨x,eᵢ⟩eᵢ‖² = ‖x‖² − Σ|⟨x,eᵢ⟩|²。∎",
    track: "精確 ℚ",
    run: ob_d11,
  })
  xs.push({
    code: "D-12",
    zh: "Parseval 恆等式",
    cat: "內積演算法",
    spaces: "具完備標準正交基之空間",
    deff: "{eᵢ} 為完備標準正交基。",
    formula: "‖x‖² = Σᵢ|⟨x,eᵢ⟩|²；⟨x,y⟩ = Σᵢ⟨x,eᵢ⟩‾⟨y,eᵢ⟩",
    thm: "定理：Bessel 取等號 ⟺ 基底完備。",
    proof: "完備 ⇒ 殘差為 0；反之若殘差恆為 0 則任何與全體 eᵢ 正交之向量必為 0。義務同時驗證真子集嚴格小於與完備基取等。∎",
    track: "精確 ℚ",
    run: ob_d11,
  })
  xs.push({
    code: "D-13",
    zh: "Cauchy–Schwarz 不等式（精確憑證）",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "鬆弛量 δ = ⟨x,x⟩⟨y,y⟩ − |⟨x,y⟩|²。",
    formula: "|⟨x,y⟩|² ≤ ⟨x,x⟩⟨y,y⟩，等號 ⟺ 線性相依",
    thm: "定理（Cauchy–Schwarz）：δ ≥ 0，且 δ = 0 ⟺ {x,y} 線性相依。",
    proof: "令 λ = ⟨x,y⟩/⟨y,y⟩，0 ≤ ⟨x−λy,x−λy⟩ = (⟨x,x⟩⟨y,y⟩−|⟨x,y⟩|²)/⟨y,y⟩。等號 ⟺ x = λy。δ 為體元素，於 ℚ 上可精確判定符號。∎",
    track: "精確 ℚ/ℚ(i)",
    run: ob_d13,
  })
  xs.push({
    code: "D-14",
    zh: "三角不等式（免開方之精確判定）",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "令 a=‖x‖², b=‖y‖², c=‖x+y‖²。",
    formula: "‖x+y‖ ≤ ‖x‖+‖y‖ ⟺ (c−a−b ≤ 0) ∨ ((c−a−b)² ≤ 4ab)",
    thm: "定理：三角不等式等價於上述有理判定式（避免在 ℚ 上開方）。",
    proof: "c ≤ a+b+2√(ab) ⟺ c−a−b ≤ 2√(ab)；若左式 ≤ 0 顯然成立，否則兩邊平方。∎",
    track: "精確 ℚ",
    run: ob_d14,
  })
  xs.push({
    code: "D-15",
    zh: "平行四邊形律",
    cat: "內積演算法",
    spaces: "P₅、ℚ⁵、Sym₃",
    deff: "缺陷量 = ‖x+y‖²+‖x−y‖² − 2‖x‖² − 2‖y‖²。",
    formula: "‖x+y‖² + ‖x−y‖² = 2‖x‖² + 2‖y‖²",
    thm: "定理（Jordan–von Neumann）：賦範空間之範數源自內積 ⟺ 滿足平行四邊形律。",
    proof: "展開內積直接得；逆向由極化恆等式構造內積並驗證雙線性。本義務於三個不同空間驗證缺陷恆為 0。∎",
    track: "精確 ℚ",
    run: ob_d15,
  })
  xs.push({
    code: "D-16",
    zh: "實極化恆等式",
    cat: "內積演算法",
    spaces: "實 IPSpace",
    deff: "由範數重建內積。",
    formula: "⟨x,y⟩ = (‖x+y‖² − ‖x−y‖²)/4",
    thm: "定理：實內積由範數唯一決定。",
    proof: "展開 ‖x±y‖² = ‖x‖²±2⟨x,y⟩+‖y‖² 相減。∎",
    track: "精確 ℚ",
    run: ob_d16,
  })
  xs.push({
    code: "D-17",
    zh: "複極化恆等式",
    cat: "內積演算法",
    spaces: "複 IPSpace",
    deff: "四項帶 i 權之組合。",
    formula: "⟨x,y⟩ = ¼Σ_{k=0}^{3} i^k‖x + i^k y‖²",
    thm: "定理：複內積由範數唯一決定（第一變數線性之慣例）。",
    proof: "逐項展開，利用 ⟨x,i^ky⟩ = ‾{i^k}⟨x,y⟩ 之共軛線性。∎",
    track: "精確 ℚ(i)",
    run: ob_d16,
  })
  xs.push({
    code: "D-18",
    zh: "畢氏定理與其逆",
    cat: "內積演算法",
    spaces: "實 IPSpace",
    deff: "x ⊥ y ⟺ ⟨x,y⟩ = 0。",
    formula: "x ⊥ y ⟺ ‖x+y‖² = ‖x‖² + ‖y‖²（實空間）",
    thm: "定理：實內積空間中畢氏定理之逆亦成立；複空間中僅得 Re⟨x,y⟩ = 0。",
    proof: "‖x+y‖² = ‖x‖²+2Re⟨x,y⟩+‖y‖²。義務同時以非正交對驗證逆命題之否定情形。∎",
    track: "精確 ℚ",
    run: ob_d18,
  })
  xs.push({
    code: "D-19",
    zh: "正交補與正交分解 V = W ⊕ W^⊥",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "W^⊥ = {x : ⟨x,w⟩ = 0 ∀w ∈ W}，由線性系統 M x = 0 之零空間求得。",
    formula: "dim W + dim W^⊥ = dim V；(W^⊥)^⊥ = W",
    thm: "定理：有限維內積空間之正交分解存在且唯一。",
    proof: "x = P_Wx + (x−P_Wx)；唯一性由 W ∩ W^⊥ = 0（正定性）。(W^⊥)^⊥ ⊇ W 與維數計數給出相等。∎",
    track: "精確 ℚ",
    run: ob_d19,
  })
  xs.push({
    code: "D-20",
    zh: "等距判定與 Gram 之基底變換律",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "T 等距 ⟺ [T]*G[T] = G；新基 b'_j = ΣS_{ij}bᵢ。",
    formula: "G' = S*GS；det G' = |det S|²det G",
    thm: "定理：保內積 ⟺ 保範數 ⟺ 矩陣滿足 T*GT = G ⟺ 把某組標準正交基映為標準正交基。",
    proof: "保範數 ⇒ 保內積由極化恆等式；矩陣條件由座標展開。變換律由 ⟨b'_i,b'_j⟩ 展開。∎",
    track: "精確 ℚ",
    run: ob_d20,
  })
  xs.push({
    code: "D-21",
    zh: "Householder 反射（抽象版）",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "H_v x = x − 2(⟨x,v⟩/⟨v,v⟩)v。",
    formula: "H_v² = I；H_v v = −v；H_v|_{v^⊥} = id；‖H_vx‖ = ‖x‖",
    thm: "定理：H_v 為等距、對合、自伴之反射，det H_v = −1（實空間）。",
    proof: "直接代入計算 ⟨H_vx,H_vx⟩ = ⟨x,x⟩；對合性由兩次代入；特徵值為 −1（重數 1）與 1（重數 n−1）。∎",
    track: "精確 ℚ",
    run: ob_d21,
  })
  xs.push({
    code: "D-22",
    zh: "最小二乘與正規方程",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "min_c ‖x − Σcⱼwⱼ‖。",
    formula: "Gc = b；殘差 r ⊥ span{wⱼ}；‖x‖² = ‖P_Wx‖² + ‖r‖²",
    thm: "定理：最小二乘解 ⟺ 正規方程之解 ⟺ 殘差正交。",
    proof: "由最佳逼近定理（D-05）；Gram 可逆時解唯一，否則取最小範數解。∎",
    track: "精確 ℚ",
    run: ob_d22,
  })
  xs.push({
    code: "D-23",
    zh: "夾角與餘弦相似度",
    cat: "內積演算法",
    spaces: "任意 IPSpace",
    deff: "cos θ = Re⟨x,y⟩/(‖x‖‖y‖)，θ = arccos(cos θ) ∈ [0,π]。",
    formula: "|cos θ| ≤ 1（Cauchy–Schwarz）；θ(x,x) = 0；θ(x,y) = θ(y,x)",
    thm: "命題：夾角良定義（由 Cauchy–Schwarz），且為對稱函數。",
    proof: "|Re⟨x,y⟩| ≤ |⟨x,y⟩| ≤ ‖x‖‖y‖；arccos 由 atan2 實作。∎",
    track: "數值 ℝ（量）",
    run: ob_d23,
  })

  // ------------------------------------------------------------------
  // E 群：具體空間之專屬定理
  // ------------------------------------------------------------------
  xs.push({
    code: "E-01",
    zh: "Legendre 多項式 = 單項式基之 Gram–Schmidt",
    cat: "多項式空間",
    spaces: "S11 P_n(L²[−1,1])",
    deff: "對 {1,x,…,x⁵} 作 GS；與遞推 (k+1)P_{k+1} = (2k+1)xP_k − kP_{k−1} 比較。",
    formula: "GS_k = P_k / lc(P_k)（首一化）",
    thm: "定理：L²[−1,1] 上單項式基之正交化恰給出 Legendre 多項式（至常數倍）。",
    proof: "兩者皆為首一且互相正交之次數遞增族，由 GS 之唯一性（上三角且對角為 1）得相等。精確 ℚ 逐係數驗證。∎",
    track: "精確 ℚ",
    run: ob_e01,
  })
  xs.push({
    code: "E-02",
    zh: "Legendre 正交性與範數",
    cat: "多項式空間",
    spaces: "S11",
    deff: "P_k 由三項遞推生成。",
    formula: "∫₋₁¹ P_kP_m dx = 2/(2k+1)·δ_{km}",
    thm: "定理：{P_k} 為 L²[−1,1] 之正交族，‖P_k‖² = 2/(2k+1)。",
    proof: "由 Rodrigues 公式與分部積分；本實作以精確有理積分逐對驗證（49 組）。∎",
    track: "精確 ℚ",
    run: ob_e02,
  })
  xs.push({
    code: "E-03",
    zh: "Chebyshev 合成律 T_m∘T_k = T_{mk}",
    cat: "多項式空間",
    spaces: "S11／多項式代數",
    deff: "T₀=1, T₁=x, T_{k+1} = 2xT_k − T_{k−1}。",
    formula: "T_m(T_k(x)) = T_{mk}(x)",
    thm: "定理：Chebyshev 多項式族於合成下構成乘法么半群同態 (ℕ,×) → (𝔽[x],∘)。",
    proof: "由 T_n(cos θ) = cos nθ 得 T_m(T_k(cos θ)) = cos(mkθ)；兩多項式於無窮多點相等故恆等。本義務以 𝔽[x] 中之精確係數相等驗證（非數值近似）。∎",
    track: "精確 ℚ",
    run: ob_e03,
  })
  xs.push({
    code: "E-04",
    zh: "Vandermonde 行列式公式",
    cat: "多項式空間",
    spaces: "S13 離散點值空間",
    deff: "V_{kj} = t_k^j。",
    formula: "det V = Π_{i<j}(t_j − t_i)",
    thm: "定理：節點相異 ⟺ V 可逆 ⟺ 插值問題唯一可解。",
    proof: "兩邊皆為 t 之多項式；t_i = t_j 時皆為 0 ⇒ 右式整除左式；比較次數 n(n−1)/2 與領導係數。∎",
    track: "精確 ℚ",
    run: ob_e04,
  })
  xs.push({
    code: "E-05",
    zh: "Lagrange 插值與唯一性",
    cat: "多項式空間",
    spaces: "S13",
    deff: "L(x) = Σ_i y_i Π_{j≠i}(x−t_j)/(t_i−t_j)。",
    formula: "L(t_k) = y_k；deg L < m",
    thm: "定理：給定 m 個相異節點，存在唯一次數 < m 之插值多項式。",
    proof: "存在性由基本多項式之構造；唯一性由差值多項式有 m 個根但次數 < m ⇒ 恆零。本義務並與 Vandermonde 線性系統之解交叉驗證。∎",
    track: "精確 ℚ",
    run: ob_e05,
  })
  xs.push({
    code: "E-06",
    zh: "微分算子之冪零性與 Heisenberg 關係",
    cat: "多項式空間",
    spaces: "S11 / 算子代數",
    deff: "D_{i,i+1} = i+1（微分）；X_{i+1,i} = 1（乘以 x，截斷）。",
    formula: "D^n = 0；χ_D(λ) = λⁿ；[D,X] = I（截斷子空間上）",
    thm: "定理：D 於 P_{<n} 上冪零，指數恰為 n；[D,X] = I 為 Heisenberg 代數關係。",
    proof: "D 降次 1 ⇒ Dⁿ = 0 且 D^{n−1}x^{n−1} = (n−1)! ≠ 0；χ_D = λⁿ 由上三角（嚴格）矩陣；[D,X]x^k = (k+1)x^k − kx^k = x^k。∎",
    track: "精確 ℚ",
    run: ob_e06,
  })
  xs.push({
    code: "E-07",
    zh: "Hilbert Gram 矩陣之正定性與病態性",
    cat: "多項式空間",
    spaces: "S12 P_n(L²[0,1])",
    deff: "G_{ij} = ∫₀¹x^{i+j}dx = 1/(i+j+1)。",
    formula: "κ₂(H₆) ≈ 1.5×10⁷",
    thm: "定理：Hilbert 矩陣正定但極度病態（κ₂ 隨 n 指數成長）。",
    proof: "正定性由 Gram 性質（單項式線性獨立）；病態性由 Cauchy 行列式公式 det H_n = Π… 迅速趨零，本義務以精確 ℚ 驗正定、以數值 SVD 量測 κ₂。∎",
    track: "精確 ℚ + 數值 ℝ",
    run: ob_e07,
  })
  xs.push({
    code: "E-08",
    zh: "離散點值內積 Gram = VᵀV",
    cat: "多項式空間",
    spaces: "S13",
    deff: "⟨p,q⟩ = Σ_k p(t_k)‾q(t_k)。",
    formula: "G = VᵀV（V 為 Vandermonde）",
    thm: "定理：節點數 ≥ dim 且相異 ⟺ G 正定（否則僅半定，為退化型式）。",
    proof: "G = VᵀV 恆半正定；正定 ⟺ ker V = 0 ⟺ rank V = dim ⟺ 節點足夠且相異。義務同時驗證退化情形被正確偵測。∎",
    track: "精確 ℚ",
    run: ob_e08,
  })
  xs.push({
    code: "E-09",
    zh: "M_n = Sym_n ⊥⊕ Skew_n",
    cat: "矩陣空間",
    spaces: "S5, S6, S7",
    deff: "A = (A+Aᵀ)/2 + (A−Aᵀ)/2。",
    formula: "dim: n² = n(n+1)/2 + n(n−1)/2；⟨S,K⟩_F = 0",
    thm: "定理：對稱與反對稱部分之分解為 Frobenius 內積下之正交直和。",
    proof: "⟨S,K⟩ = tr(SKᵀ) = −tr(SK) = −tr((SK)ᵀ) = −tr(KᵀSᵀ) = −tr(KS)… 得 ⟨S,K⟩ = 0；唯一性由直和。∎",
    track: "精確 ℚ",
    run: ob_e09,
  })
  xs.push({
    code: "E-10",
    zh: "Diag_n ≅ 𝔽ⁿ（等距同構）",
    cat: "矩陣空間",
    spaces: "S8",
    deff: "A ↦ (a₁₁,…,a_nn)。",
    formula: "⟨A,B⟩_F = Σᵢ aᵢ‾bᵢ",
    thm: "定理：對角矩陣空間與 𝔽ⁿ 等距同構，且為極大交換子代數。",
    proof: "線性雙射且保內積 ⇒ 等距同構；交換性由逐分量乘法。∎",
    track: "精確 ℚ",
    run: ob_e10,
  })
  xs.push({
    code: "E-11",
    zh: "Herm_n(ℂ) 之實內積結構與 M_n = Herm ⊕ i·Herm",
    cat: "矩陣空間",
    spaces: "S9",
    deff: "⟨A,B⟩ = Re tr(AB*)；H₁ = (M+M*)/2，H₂ = (M−M*)/(2i)。",
    formula: "M = H₁ + iH₂；dim_ℝ Herm_n = n²",
    thm: "定理：任意複方陣唯一分解為 Hermitian 與反 Hermitian 部分（Cartesian 分解）。",
    proof: "直接構造與唯一性（兩式相加相減）；tr(AB*) 於 A,B Hermitian 時為實數。∎",
    track: "精確 ℚ(i)",
    run: ob_e11,
  })
  xs.push({
    code: "E-12",
    zh: "sl_n = I^⊥（跡零空間）",
    cat: "矩陣空間",
    spaces: "S10",
    deff: "sl_n = {A : tr A = 0}。",
    formula: "⟨A,I⟩_F = tr A；dim sl_n = n²−1",
    thm: "定理：sl_n 為單位矩陣於 Frobenius 內積下之正交補，且為李代數。",
    proof: "tr A = ⟨A,I⟩_F ⇒ 跡零 ⟺ A ⊥ I；維數由線性泛函之核；[A,B] 之跡為 0（循環性）。∎",
    track: "精確 ℚ",
    run: ob_e12,
  })
  xs.push({
    code: "E-13",
    zh: "加權函數空間之 δ 基底與求值泛函",
    cat: "函數空間",
    spaces: "S3",
    deff: "δ_s(t) = [s = t]；ev_s(f) = f(s)。",
    formula: "⟨δᵢ,δⱼ⟩ = wᵢδᵢⱼ；Riesz(ev_k) = δ_k/w_k",
    thm: "定理：求值泛函之 Riesz 代表為加權 δ 函數（離散再生核）。",
    proof: "⟨f, δ_k/w_k⟩ = w_k·f(k)·(1/w_k) = f(k)。此即再生核 K(s,t) = δ_{st}/w_s。∎",
    track: "精確 ℚ",
    run: ob_e13,
  })
  xs.push({
    code: "E-14",
    zh: "列空間之投影矩陣 A(AᵀA)⁻¹Aᵀ",
    cat: "子空間",
    spaces: "S4",
    deff: "P = A(AᵀA)⁻¹Aᵀ（A 行滿秩）。",
    formula: "P² = P = Pᵀ；im P = col A；I − P 投影至 ker Aᵀ",
    thm: "定理：此閉式與抽象 Gram 投影（D-05）逐項相同。",
    proof: "正規方程 AᵀAc = Aᵀx 之解代回 Ac 即得；冪等與對稱直接計算。∎",
    track: "精確 ℚ",
    run: ob_e14,
  })
  xs.push({
    code: "E-15",
    zh: "多變量多項式求值為環同態",
    cat: "多變量多項式",
    spaces: "S14/S15",
    deff: "f = Σ_α c_α xᵅ，ev_ξ(f) = Σ c_α ξᵅ。",
    formula: "(f+g)(ξ) = f(ξ)+g(ξ)；(fg)(ξ) = f(ξ)g(ξ)；deg(fg) ≤ deg f + deg g",
    thm: "定理：ev_ξ : 𝔽[x₁..x_m] → 𝔽 為 𝔽-代數同態。",
    proof: "由多重指標卷積 (fg)_γ = Σ_{α+β=γ}f_αg_β 與指數律 ξ^{α+β} = ξᵅξᵝ。∎",
    track: "精確 ℚ",
    run: ob_e15,
  })
  xs.push({
    code: "E-16",
    zh: "Bombieri 內積之正交不變性",
    cat: "多變量多項式",
    spaces: "S14",
    deff: "⟨f,g⟩_B = Σ_α (α!/|α|!) f_α‾g_α；U ∈ O(m) 作用為變數替換 f ↦ f∘U。",
    formula: "⟨f∘U, g∘U⟩_B = ⟨f,g⟩_B",
    thm: "定理（Bombieri）：Bombieri 範數於正交變換下不變。",
    proof: "此內積可寫為 ⟨f,g⟩ = f(∂)‾g |₀ / d! 之微分型式，而 Laplace 型算子於 O(m) 下不變。本義務以有理正交矩陣（Cayley 變換）與精確 ℚ 係數逐例驗證。∎",
    track: "精確 ℚ",
    run: ob_e16,
  })

  // ------------------------------------------------------------------
  // F 群：空間組合子（combinators.mbt 演算法 054–060）
  // ------------------------------------------------------------------
  xs.push({
    code: "F-01",
    zh: "正交直和 P ⊕ Q",
    cat: "空間構造",
    spaces: "任意兩空間",
    deff: "載體 V₁×V₂，⟨(x₁,x₂),(y₁,y₂)⟩ = ⟨x₁,y₁⟩+⟨x₂,y₂⟩。",
    formula: "dim(P⊕Q) = dim P + dim Q；Gram = diag(G₁,G₂)",
    thm: "定理：直和之 Gram 為分塊對角，兩嵌入像互相正交。",
    proof: "內積逐分量定義 ⇒ 公理逐條相加成立；交叉項 ⟨(a,0),(0,d)⟩ = 0。∎",
    track: "精確 ℚ",
    run: ob_f01,
  })
  xs.push({
    code: "F-02",
    zh: "張量積 P ⊗ Q",
    cat: "空間構造",
    spaces: "任意兩空間",
    deff: "基底 {bᵢ⊗cⱼ}；⟨x₁⊗x₂,y₁⊗y₂⟩ = ⟨x₁,y₁⟩⟨x₂,y₂⟩。",
    formula: "Gram(P⊗Q) = G₁ ⊗ G₂（Kronecker 積）",
    thm: "定理：兩正定矩陣之 Kronecker 積正定，故張量積之型式確為內積。",
    proof: "G₁⊗G₂ 之特徵值為 λᵢμⱼ > 0；雙線性由座標外積定義；普遍性質由基底映射唯一延拓。∎",
    track: "精確 ℚ",
    run: ob_f02,
  })
  xs.push({
    code: "F-03",
    zh: "張量算子與部分跡",
    cat: "空間構造",
    spaces: "V⊗W 上之算子",
    deff: "(A⊗B) 作用於純張量；tr₂(M)_{ij} = Σ_k M_{(i,k),(j,k)}。",
    formula: "(A⊗B)(x⊗y) = Ax⊗By；tr₂(A⊗B) = tr(B)·A；tr(tr₂M) = tr M",
    thm: "定理：部分跡為唯一滿足 tr(tr₂(M)A) = tr(M(A⊗I)) 之線性映射。",
    proof: "於純張量上驗證後由線性延拓；唯一性由跡型式之非退化性。∎",
    track: "精確 ℚ",
    run: ob_f03,
  })
  xs.push({
    code: "F-04",
    zh: "對偶空間與雙對偶自然同構",
    cat: "空間構造",
    spaces: "任意 IPSpace",
    deff: "V* 以對偶座標 (φ(b₁),…,φ(b_n)) 表示，Gram(V*) = (G⁻¹)ᵀ。",
    formula: "b^i(bⱼ) = δ^i_j；Gram(V**) = G；⟨ev_v,ev_w⟩ = ⟨v,w⟩",
    thm: "定理：V ≅ V** 為自然（與基底無關）之等距同構；V ≅ V* 為共軛線性（Riesz）。",
    proof: "Riesz 傳遞給出 V* 之內積；兩次取逆轉置還原 G；自然性由 ev_v(φ) = φ(v) 之定義不涉及基底。∎",
    track: "精確 ℚ",
    run: ob_f04,
  })
  xs.push({
    code: "F-05",
    zh: "Hom(P,Q) ≅ Q ⊗ P*（Hilbert–Schmidt 內積）",
    cat: "空間構造",
    spaces: "線性映射空間",
    deff: "以矩陣座標表示，Gram = G_Q ⊗ G_{P*}。",
    formula: "dim Hom = dim P·dim Q；⟨A,B⟩_HS = tr(B*A)（標準正交基）",
    thm: "定理：Hom 空間之自然內積即 Hilbert–Schmidt（Frobenius）內積。",
    proof: "由張量積之內積與對偶空間之 Gram 計算；標準正交基時 G = I 退化為 tr(B*A)。∎",
    track: "精確 ℚ",
    run: ob_f05,
  })
  xs.push({
    code: "F-06",
    zh: "實化與複結構 J",
    cat: "空間構造",
    spaces: "ℂ-空間 → ℝ-空間",
    deff: "V_ℝ 基底 {b₁..b_n, ib₁..ib_n}，⟨x,y⟩_ℝ = Re⟨x,y⟩_ℂ；J = 乘以 i。",
    formula: "dim_ℝ = 2dim_ℂ；J² = −I；ω(x,y) = Im⟨x,y⟩_ℂ = ⟨x,Jy⟩_ℝ",
    thm: "定理：(V_ℝ, ⟨,⟩_ℝ, ω, J) 構成 Kähler 三元組（相容之度量、辛形式與複結構）。",
    proof: "Re 部分為實內積（正定且雙線性）；J 等距由 |i| = 1；ω 反對稱非退化由 Im 部分之性質。∎",
    track: "精確 ℚ(i)/ℚ",
    run: ob_f06,
  })
  xs.push({
    code: "F-07",
    zh: "內積扭曲 ⟨x,y⟩_A",
    cat: "空間構造",
    spaces: "同一向量空間、不同度量",
    deff: "⟨x,y⟩_A = Σ_{ij} A_{ij}xᵢ‾yⱼ。",
    formula: "A Hermitian 正定 ⟺ ⟨,⟩_A 為內積；A = LL* 時 L⁻¹ 為等距同構",
    thm: "定理：所有與給定線性結構相容之內積恰由正定 Hermitian 矩陣參數化。",
    proof: "⟨,⟩_A 之公理 ⟺ A 之 Hermitian 正定性（I3 ⟺ A* = A，I4/I5 ⟺ 正定）。義務亦驗證檢驗器對不定／非對稱 A 之否決能力（反例檢出）。∎",
    track: "精確 ℚ",
    run: ob_f07,
  })
  xs.push({
    code: "F-08",
    zh: "子空間構造（含相依生成集）",
    cat: "空間構造",
    spaces: "任意 IPSpace 之子空間",
    deff: "由生成集取 RREF 主元挑出基底，座標由解線性系統得。",
    formula: "dim = rank(生成集)；coord∘expand = id",
    thm: "定理：子空間承襲之型式仍為內積；主元挑選給出基底。",
    proof: "限制正定型式仍正定；主元行線性獨立且張成相同空間。∎",
    track: "精確 ℚ",
    run: ob_f08,
  })
  xs.push({
    code: "F-09",
    zh: "組合空間之演算法通行性（組合爆炸）",
    cat: "空間構造",
    spaces: "P⊗Q, Q⊗E, P*, (P⊗E)*, Hom(P,Q), P*⊗E*",
    deff: "對 6 個由構造子生成之空間，重跑公理檢驗 + 投影 + Cauchy–Schwarz。",
    formula: "(空間數) × (演算法數) 組對皆可運行",
    thm: "命題：抽象演算法只依賴 IPSpace 介面，故對任意組合空間自動適用。",
    proof: "ipalgo.mbt 中之函數僅呼叫 vs.add/smul/coord/expand 與 inner，不涉及具體載體；型別系統保證可組合性。本義務為該性質之執行證據。∎",
    track: "精確 ℚ",
    run: ob_f09,
  })

  // ------------------------------------------------------------------
  // G 群：外代數與行列式幾何（exterior.mbt 演算法 049–053）
  // ------------------------------------------------------------------
  xs.push({
    code: "G-01",
    zh: "楔積之反交換律",
    cat: "外代數",
    spaces: "Λᵖ×Λ^q → Λ^{p+q}",
    deff: "(Σa_Ie_I)∧(Σb_Je_J) = Σ_{I∩J=∅} ε(I,J)a_Ib_Je_{I∪J}。",
    formula: "α∧β = (−1)^{pq}β∧α；v∧v = 0",
    thm: "定理：楔積為分次反交換之結合乘法。",
    proof: "ε(I,J) = (−1)^{|{(i,j)∈I×J : i>j}|}，交換 I,J 產生 (−1)^{pq}；v∧v 之每項自我抵消。∎",
    track: "精確 ℚ",
    run: ob_g01,
  })
  xs.push({
    code: "G-02",
    zh: "外代數之結合律與分配律",
    cat: "外代數",
    spaces: "S18 Λ(𝔽ⁿ)",
    deff: "以位元遮罩索引之全外代數乘法。",
    formula: "(α∧β)∧γ = α∧(β∧γ)；α∧(β+γ) = α∧β + α∧γ",
    thm: "定理：Λ(𝔽ⁿ) 為 2ⁿ 維分次結合代數。",
    proof: "符號函數滿足 ε(I,J)ε(I∪J,K) = ε(J,K)ε(I,J∪K)（兩種合併次序之逆序數相同）。∎",
    track: "精確 ℚ",
    run: ob_g02,
  })
  xs.push({
    code: "G-03",
    zh: "Gram 行列式定理（Λᵏ 之內積）",
    cat: "外代數",
    spaces: "S17 Λᵏ(𝔽ⁿ)",
    deff: "⟨e_I,e_J⟩ = δ_{IJ} 誘導之內積。",
    formula: "⟨v₁∧…∧v_k, w₁∧…∧w_k⟩ = det(⟨vᵢ,wⱼ⟩)",
    thm: "定理（Cauchy–Binet 之內積形式）：可分解元之內積為 Gram 行列式。",
    proof: "由 Plücker 座標 (v₁∧…∧v_k)_I = det V[I,:] 與 Cauchy–Binet 公式 Σ_I det V[I,:]det W[I,:] = det(VᵀW)。∎",
    track: "精確 ℚ",
    run: ob_g03,
  })
  xs.push({
    code: "G-04",
    zh: "行列式之外代數定義",
    cat: "外代數",
    spaces: "Λⁿ(𝔽ⁿ) ≅ 𝔽",
    deff: "v₁∧…∧v_n ∈ Λⁿ（一維）。",
    formula: "v₁∧…∧v_n = det(V)·e_{1…n}",
    thm: "定理：行列式即 Λⁿ 上之唯一交錯多線性型式之係數；相依 ⟺ 楔積為 0。",
    proof: "Λⁿ 一維且楔積交錯多線性，取標準基得係數即 det。相依時某 vᵢ 為其餘之線性組合 ⇒ 展開後每項含重複因子 ⇒ 0。∎",
    track: "精確 ℚ",
    run: ob_g04,
  })
  xs.push({
    code: "G-05",
    zh: "Hodge 星算子之對合律",
    cat: "外代數",
    spaces: "Λᵏ ↔ Λ^{n−k}",
    deff: "⋆e_I = ε(I,Iᶜ)e_{Iᶜ}。",
    formula: "⋆⋆ = (−1)^{k(n−k)}·id",
    thm: "定理：⋆ 為 Λᵏ 與 Λ^{n−k} 間之等距同構，且平方為符號。",
    proof: "ε(I,Iᶜ)ε(Iᶜ,I) = (−1)^{k(n−k)}（交換兩塊之逆序數）。等距性由基底之雙射與符號為 ±1。∎",
    track: "精確 ℚ",
    run: ob_g05,
  })
  xs.push({
    code: "G-06",
    zh: "Hodge 星與內積之相容性",
    cat: "外代數",
    spaces: "Λᵏ(𝔽ⁿ)",
    deff: "vol = e_{1…n}。",
    formula: "α ∧ ⋆β = ⟨α,β⟩·vol",
    thm: "定理：此式可作為 Hodge 星之不依賴基底之定義。",
    proof: "於基底元上 e_I ∧ ⋆e_J = δ_{IJ}·ε(I,Iᶜ)²·vol = δ_{IJ}vol；雙線性延拓。∎",
    track: "精確 ℚ",
    run: ob_g06,
  })
  xs.push({
    code: "G-07",
    zh: "三維叉積之古典恆等式",
    cat: "外代數",
    spaces: "Λ²(𝔽³) ≅ 𝔽³",
    deff: "a×b = ⋆(a∧b)。",
    formula: "‖a×b‖² = ‖a‖²‖b‖² − ⟨a,b⟩²（Lagrange）；a×(b×c)+b×(c×a)+c×(a×b) = 0（Jacobi）；⟨a,b×c⟩ = det[a b c]",
    thm: "定理：(ℝ³,×) 為李代數 so(3)，且叉積為 Hodge 星與楔積之複合。",
    proof: "Lagrange 恆等式即 G-03 於 k=2 之特例；Jacobi 由 BAC–CAB 展開；三重積為 Λ³ 之係數。∎",
    track: "精確 ℚ",
    run: ob_g07,
  })
  xs.push({
    code: "G-08",
    zh: "廣義叉積（n−1 個向量之 Hodge 補）",
    cat: "外代數",
    spaces: "𝔽ⁿ",
    deff: "x = ⋆(v₁∧…∧v_{n−1})。",
    formula: "⟨x,vᵢ⟩ = 0 ∀i；‖x‖² = det Gram(v₁..v_{n−1})",
    thm: "定理：廣義叉積垂直於所有輸入向量，其長度為 (n−1) 維體積。",
    proof: "⟨x,vᵢ⟩·vol = vᵢ∧(v₁∧…∧v_{n−1}) = 0（重複因子）；長度由 G-03 與 ⋆ 之等距性。∎",
    track: "精確 ℚ",
    run: ob_g08,
  })
  xs.push({
    code: "G-09",
    zh: "Plücker 座標與 Plücker 關係",
    cat: "外代數",
    spaces: "Grassmann 流形 Gr(k,n)",
    deff: "p_I = det V[I,:]。",
    formula: "p₀₁p₂₃ − p₀₂p₁₃ + p₀₃p₁₂ = 0（k=2, n≥4）",
    thm: "定理：可分解 2-向量之座標滿足 Plücker 二次關係（Grassmann 流形之方程）。",
    proof: "等價於 ω∧ω = 0（ω 可分解）；展開 Λ⁴ 之係數即得上式。∎",
    track: "精確 ℚ",
    run: ob_g09,
  })

  // ------------------------------------------------------------------
  // H 群：數值線性代數（realmat.mbt 演算法 081–102）
  // ------------------------------------------------------------------
  xs.push({
    code: "H-01",
    zh: "Cholesky 分解",
    cat: "數值分解",
    spaces: "SPD 矩陣",
    deff: "A = LLᵀ，L 下三角且 l_ii > 0。",
    formula: "l_jj = √(a_jj − Σ_{k<j}l_jk²)；殘差 ‖A−LLᵀ‖_max ≤ ε",
    thm: "定理：A 對稱正定 ⟺ Cholesky 分解存在且唯一；演算法為後向穩定。",
    proof: "對 n 歸納（分塊消去）；正定性保證根號下為正。義務回報實測殘差 ≈ 10⁻¹⁵ 並驗證不定矩陣被否決。∎",
    track: "數值 ℝ",
    run: ob_h01,
  })
  xs.push({
    code: "H-02",
    zh: "LDLᵀ 分解與 Sylvester 慣性律",
    cat: "數值分解",
    spaces: "對稱矩陣",
    deff: "A = LDLᵀ，L 單位下三角，D 對角。",
    formula: "慣性 (p,z,m) 不隨合同變換改變",
    thm: "定理（Sylvester 慣性律）：對稱矩陣之正／零／負特徵值個數為合同不變量。",
    proof: "若 A = SBSᵀ（S 可逆）則二次型之最大正定子空間維數相同。義務以 LDL 之 D 符號計數與 Jacobi 譜之符號計數交叉驗證。∎",
    track: "數值 ℝ",
    run: ob_h02,
  })
  xs.push({
    code: "H-03",
    zh: "Householder QR 分解",
    cat: "數值分解",
    spaces: "M_{m×n}(ℝ)",
    deff: "以反射 H_k = I − 2vvᵀ/vᵀv 逐行消去。",
    formula: "A = QR；QᵀQ = I；R 上三角",
    thm: "定理：Householder QR 為後向穩定（‖ΔA‖ = O(ε‖A‖)），優於 Gram–Schmidt。",
    proof: "每步反射為精確正交矩陣，捨入誤差不放大；殘差憑證 ‖A−QR‖、‖QᵀQ−I‖ ≈ 10⁻¹⁵。∎",
    track: "數值 ℝ",
    run: ob_h03,
  })
  xs.push({
    code: "H-04",
    zh: "Givens 旋轉 QR 分解",
    cat: "數值分解",
    spaces: "M_{m×n}(ℝ)",
    deff: "以平面旋轉逐一消去次對角元素。",
    formula: "G(i,j,θ)ᵀA 消去 a_{ji}；A = QR",
    thm: "定理：Givens QR 與 Householder QR 之 R 至對角符號唯一（QR 分解之唯一性）。",
    proof: "滿秩時 R 之對角取正可唯一化；義務驗證兩法之 |R_ii| 一致。∎",
    track: "數值 ℝ",
    run: ob_h04,
  })
  xs.push({
    code: "H-05",
    zh: "Hessenberg 化簡",
    cat: "數值分解",
    spaces: "M_n(ℝ)",
    deff: "以 Householder 反射作正交相似變換。",
    formula: "QᵀAQ = H（h_{ij} = 0 當 i > j+1）",
    thm: "定理：任意方陣正交相似於上 Hessenberg 形；對稱時為三對角。",
    proof: "逐行以反射消去第 k 行第 k+2 以下元素，相似變換保持已完成之零結構。∎",
    track: "數值 ℝ",
    run: ob_h05,
  })
  xs.push({
    code: "H-06",
    zh: "Jacobi 特徵分解（譜定理）",
    cat: "數值特徵值",
    spaces: "對稱矩陣",
    deff: "反覆以平面旋轉消去最大非對角元。",
    formula: "A = VΛVᵀ；VᵀV = I；Av_k = λ_kv_k",
    thm: "定理（譜定理）：實對稱矩陣正交可對角化；Jacobi 法二次收斂。",
    proof: "每次旋轉使非對角 Frobenius 範數嚴格下降（off(A') = off(A) − 2a_{pq}²）。殘差憑證 ‖A−VΛVᵀ‖ ≈ 10⁻¹⁵。∎",
    track: "數值 ℝ",
    run: ob_h06,
  })
  xs.push({
    code: "H-07",
    zh: "無位移 QR 迭代",
    cat: "數值特徵值",
    spaces: "對稱矩陣",
    deff: "A_{k+1} = R_kQ_k，其中 A_k = Q_kR_k。",
    formula: "A_k → diag(λ)（模長相異時）",
    thm: "定理：QR 迭代之 A_k 皆正交相似於 A，且在特徵值模長相異時收斂至上三角。",
    proof: "A_{k+1} = Q_kᵀA_kQ_k 故相似；收斂性由冪法之推廣（子空間迭代）。義務與 Jacobi 之譜交叉驗證。∎",
    track: "數值 ℝ",
    run: ob_h07,
  })
  xs.push({
    code: "H-08",
    zh: "單邊 Jacobi SVD",
    cat: "數值分解",
    spaces: "M_{m×n}(ℝ)",
    deff: "對 A 之行作旋轉使其兩兩正交；行範數即奇異值（遞減排序）。",
    formula: "A = UΣVᵀ；σᵢ² = λᵢ(AᵀA)；σ₁ = ‖A‖₂",
    thm: "定理（SVD）：任意矩陣可分解為正交×對角×正交；奇異值唯一。",
    proof: "AᵀA 對稱半正定，取其譜分解即得 V 與 σ；U 由 Av/σ 定義並補成正交基。義務驗證殘差、正交性、排序與 σ²≡λ(AᵀA)。∎",
    track: "數值 ℝ",
    run: ob_h08,
  })
  xs.push({
    code: "H-09",
    zh: "Moore–Penrose 偽逆",
    cat: "數值分解",
    spaces: "M_{m×n}(ℝ)",
    deff: "A⁺ = VΣ⁺Uᵀ（σ > tol 者取倒數）。",
    formula: "AA⁺A = A；A⁺AA⁺ = A⁺；(AA⁺)ᵀ = AA⁺；(A⁺A)ᵀ = A⁺A",
    thm: "定理：滿足 Penrose 四條件之矩陣唯一；x = A⁺b 為最小範數最小二乘解。",
    proof: "由 SVD 逐條驗證；唯一性為標準論證。滿秩時 A⁺ = (AᵀA)⁻¹Aᵀ（義務一併驗證）。∎",
    track: "數值 ℝ",
    run: ob_h09,
  })
  xs.push({
    code: "H-10",
    zh: "極分解 A = UP",
    cat: "數值分解",
    spaces: "M_n(ℝ)",
    deff: "U = U_svd V_svdᵀ，P = V_svd Σ V_svdᵀ。",
    formula: "A = UP；UᵀU = I；P = Pᵀ ⪰ 0",
    thm: "定理：極分解存在；A 可逆時唯一，且 U 為最近之正交矩陣（Frobenius 意義）。",
    proof: "由 SVD 直接構造；最近性由 Fan–Hoffman 定理。義務驗證殘差與 P 之譜非負。∎",
    track: "數值 ℝ",
    run: ob_h10,
  })
  xs.push({
    code: "H-11",
    zh: "矩陣指數（縮放–平方 + Taylor）",
    cat: "矩陣函數",
    spaces: "M_n(ℝ)",
    deff: "e^A = (e^{A/2^s})^{2^s}，內層以 20 項 Taylor。",
    formula: "e^Ae^{−A} = I；det(e^A) = e^{tr A}；AB=BA ⇒ e^{A+B} = e^Ae^B",
    thm: "定理：矩陣指數之 Jacobi 公式 det(e^A) = e^{tr A}。",
    proof: "由 Jordan 形或 d/dt det(e^{tA}) = tr(A)det(e^{tA})；可換性條件下之加法律由級數重排。∎",
    track: "數值 ℝ",
    run: ob_h11,
  })
  xs.push({
    code: "H-12",
    zh: "對稱正定矩陣平方根",
    cat: "矩陣函數",
    spaces: "SPD 矩陣",
    deff: "√A = V diag(√λ) Vᵀ。",
    formula: "(√A)² = A；√A 對稱正定",
    thm: "定理：SPD 矩陣之正定平方根存在且唯一。",
    proof: "由譜分解構造；唯一性因任何正定平方根與 A 可交換故可同時對角化。∎",
    track: "數值 ℝ",
    run: ob_h12,
  })
  xs.push({
    code: "H-13",
    zh: "冪迭代與 Rayleigh 商",
    cat: "數值特徵值",
    spaces: "對稱矩陣",
    deff: "x ← Ax/‖Ax‖；R(x) = xᵀAx/xᵀx。",
    formula: "λ_min ≤ R(x) ≤ λ_max；收斂率 |λ₂/λ₁|^k",
    thm: "定理（Rayleigh 商界 / Courant–Fischer）：R 之值域恰為 [λ_min, λ_max]。",
    proof: "以譜分解展開 R(x) = Σλᵢcᵢ²/Σcᵢ² 為凸組合。冪迭代收斂由主特徵向量分量放大。∎",
    track: "數值 ℝ",
    run: ob_h13,
  })
  xs.push({
    code: "H-14",
    zh: "2-範數條件數 κ₂",
    cat: "數值分析",
    spaces: "M_n(ℝ)",
    deff: "κ₂(A) = σ_max/σ_min。",
    formula: "κ₂ ≥ 1；κ₂(Q) = 1（Q 正交）；相對誤差放大上界 κ₂",
    thm: "定理：線性系統之相對誤差 ‖δx‖/‖x‖ ≤ κ₂(A)·(‖δA‖/‖A‖ + ‖δb‖/‖b‖)。",
    proof: "由 ‖A‖₂ = σ_max、‖A⁻¹‖₂ = 1/σ_min 與擾動展開。義務驗證正交矩陣 κ₂=1 與 Hilbert 矩陣之病態。∎",
    track: "數值 ℝ",
    run: ob_h14,
  })
  xs.push({
    code: "H-15",
    zh: "共軛梯度法",
    cat: "迭代解法",
    spaces: "SPD 線性系統",
    deff: "以 A-共軛方向逐步最小化 ½xᵀAx − bᵀx。",
    formula: "精確算術下 ≤ n 步終止；‖x_k − x*‖_A ≤ 2((√κ−1)/(√κ+1))^k‖x₀−x*‖_A",
    thm: "定理：CG 於 Krylov 子空間中給出 A-範數最佳解，n 步後為精確解。",
    proof: "殘差構成正交族、方向構成 A-正交族 ⇒ 至多 n 個；最佳性由 Galerkin 條件。義務以恰 n 次迭代後之殘差為憑證。∎",
    track: "數值 ℝ",
    run: ob_h15,
  })
  xs.push({
    code: "H-16",
    zh: "Gauss–Seidel 迭代",
    cat: "迭代解法",
    spaces: "對角佔優／SPD 系統",
    deff: "x_i ← (b_i − Σ_{j<i}a_{ij}x_j − Σ_{j>i}a_{ij}x_j)/a_ii。",
    formula: "x^{(k+1)} = (D+L)⁻¹(b − Ux^{(k)})",
    thm: "定理：A 對稱正定或嚴格對角佔優 ⇒ Gauss–Seidel 收斂。",
    proof: "迭代矩陣 M = −(D+L)⁻¹U 之譜半徑 < 1（Householder–John 定理）。義務以殘差為憑證。∎",
    track: "數值 ℝ",
    run: ob_h16,
  })
  xs.push({
    code: "H-17",
    zh: "Lanczos 三對角化（完全再正交化）",
    cat: "Krylov 方法",
    spaces: "對稱矩陣",
    deff: "以 Krylov 子空間 K_k(A,q₁) 之正交基建構三對角 T。",
    formula: "QᵀAQ = T（三對角）；AQ = QT + β q_{k+1}e_kᵀ",
    thm: "定理：Lanczos 為對稱矩陣之 Arnoldi 特例；T 之特徵值為 Ritz 值。",
    proof: "對稱性使 Arnoldi 之 Hessenberg 退化為三對角；完全再正交化消除浮點正交性損失。殘差憑證 ‖QᵀAQ−T‖ ≈ 10⁻¹⁵。∎",
    track: "數值 ℝ",
    run: ob_h17,
  })
  xs.push({
    code: "H-18",
    zh: "Arnoldi 分解",
    cat: "Krylov 方法",
    spaces: "一般方陣",
    deff: "Gram–Schmidt 於 Krylov 序列 {v, Av, A²v, …}。",
    formula: "QᵀAQ = H（上 Hessenberg）",
    thm: "定理：Arnoldi 給出 Krylov 子空間上之正交投影算子矩陣。",
    proof: "逐步正交化保證 H 為上 Hessenberg；完整 k=n 時 Q 為正交方陣。∎",
    track: "數值 ℝ",
    run: ob_h18,
  })
  xs.push({
    code: "H-19",
    zh: "DFT 矩陣之么正性與循環矩陣對角化",
    cat: "變換家族",
    spaces: "ℂⁿ",
    deff: "F_{jk} = ω^{jk}/√n，ω = e^{−2πi/n}。",
    formula: "F*F = I；F C F* = diag(√n·Fc)",
    thm: "定理：所有循環矩陣由 DFT 同時對角化，故構成交換代數。",
    proof: "循環矩陣為位移算子 S 之多項式，而 S 之特徵向量為 Fourier 基。義務驗證非對角元為 0 且對角元等於 √n·Fc。∎",
    track: "數值 ℝ/ℂ",
    run: ob_h19,
  })
  xs.push({
    code: "H-20",
    zh: "快速 Fourier 變換（遞迴 radix-2）",
    cat: "變換家族",
    spaces: "ℂⁿ（n = 2^k）",
    deff: "分治：偶數項與奇數項之 DFT 再以旋轉因子合併。",
    formula: "fft(x) = √n·(F x)；Σ|x|² = (1/n)Σ|X|²（Parseval）",
    thm: "定理：FFT 與 DFT 矩陣乘法等價，複雜度 O(n log n)。",
    proof: "Danielson–Lanczos 引理；義務以 n = 2..32 逐例比對（最大偏差 ≈ 10⁻¹⁵）並驗 Parseval。∎",
    track: "數值 ℝ/ℂ",
    run: ob_h20,
  })
  xs.push({
    code: "H-21",
    zh: "Hadamard 矩陣與快速 Walsh–Hadamard 變換",
    cat: "變換家族",
    spaces: "ℝ^{2^k}",
    deff: "H_1 = [[1,1],[1,−1]]，H_{k+1} = H_k ⊗ H_1。",
    formula: "HᵀH = nI（整數精確）；FWHT ≡ H·x，複雜度 O(n log n)",
    thm: "定理：Sylvester 型 Hadamard 矩陣之列兩兩正交，元素皆 ±1。",
    proof: "由 Kronecker 積之混合積律歸納：(H_k⊗H_1)ᵀ(H_k⊗H_1) = (H_kᵀH_k)⊗(H_1ᵀH_1) = 2nI。整數運算故無捨入誤差（精確相等）。∎",
    track: "數值 ℝ（整數精確）",
    run: ob_h21,
  })
  xs.push({
    code: "H-22",
    zh: "Haar 小波正交基",
    cat: "變換家族",
    spaces: "ℝ^{2^k}",
    deff: "遞迴定義之尺度／小波列，再逐列規範化。",
    formula: "HHᵀ = I（規範化後）；各尺度之支撐互不重疊",
    thm: "定理：Haar 系統為 ℝ^{2^k} 之正交基（最早之小波基）。",
    proof: "不同尺度之小波支撐嵌套且平均為 0 ⇒ 正交；同尺度支撐不交 ⇒ 正交；計數 2^k 個 ⇒ 為基底。∎",
    track: "數值 ℝ",
    run: ob_h22,
  })
  xs.push({
    code: "H-23",
    zh: "譜不變量（跡、行列式、Frobenius 範數、譜半徑）",
    cat: "數值特徵值",
    spaces: "對稱矩陣",
    deff: "由 Jacobi 譜計算各不變量。",
    formula: "tr A = Σλ；det A = Πλ；‖A‖_F² = Σλ²；ρ(A) = max|λ|",
    thm: "定理：這些量為相似不變量（對稱時為正交相似不變量）。",
    proof: "由 A = VΛVᵀ 與跡之循環性、行列式乘性、Frobenius 範數之正交不變性。∎",
    track: "數值 ℝ",
    run: ob_h23,
  })
  xs.push({
    code: "H-24",
    zh: "CGS 與 MGS 之正交性損失對比（Björck 界）",
    cat: "數值分析",
    spaces: "病態 Hilbert 基底",
    deff: "以 9×9 Hilbert 矩陣之行為輸入，量測 max_{i≠j}|⟨uᵢ,uⱼ⟩|/(‖uᵢ‖‖uⱼ‖)。",
    formula: "CGS: O(εκ²)；MGS: O(εκ)",
    thm: "定理（Björck 1967）：MGS 之正交性損失與 κ 成正比，CGS 與 κ² 成正比。",
    proof: "誤差分析見 Björck；本義務以實測數據為證：κ₂ ≈ 2.9×10⁹ 時 CGS 損失 ≈ 4.8×10⁻⁶ 而 MGS ≈ 1.1×10⁻¹⁰（相差約 4 個數量級）。∎",
    track: "數值 ℝ",
    run: ob_h24,
  })
  xs.push({
    code: "H-25",
    zh: "ℝ 軌道之公理檢驗（相對 ε 判等）",
    cat: "數值分析",
    spaces: "ℝ⁴、P₅(ℝ)",
    deff: "Double 之 s_eq 採相對誤差 10⁻⁹（絕對下界 10⁻¹²）。",
    formula: "|a−b| ≤ 10⁻⁹·max(1,|a|,|b|)",
    thm: "命題：於此判等下 ℝ 軌道之公理檢驗結論與 ℚ 軌道一致（無偽陰性）。",
    proof: "浮點加乘之相對誤差 ≤ u ≈ 1.1×10⁻¹⁶，公理式之運算次數 O(n) ⇒ 累積誤差遠小於門檻。∎",
    track: "數值 ℝ",
    run: ob_h25,
  })

  // ------------------------------------------------------------------
  // I 群：四元數代數與旋轉群（quatspace.mbt 演算法 045–048）
  // ------------------------------------------------------------------
  xs.push({
    code: "I-01",
    zh: "Euler 四平方恆等式 N(pq) = N(p)N(q)",
    cat: "四元數",
    spaces: "ℍ",
    deff: "N(q) = w²+x²+y²+z² = q‾q。",
    formula: "N(pq) = N(p)N(q)",
    thm: "定理：範數為乘法同態 ℍ → ℝ_{≥0}；等價於 Euler 四平方恆等式。",
    proof: "N(pq) = pq‾(pq) = pq‾q‾p = N(q)p‾p = N(p)N(q)（用 ‾(pq)=‾q‾p 與 N(q) 為中心元素）。∎",
    track: "精確 ℚ",
    run: ob_i01,
  })
  xs.push({
    code: "I-02",
    zh: "共軛反自同構與乘法逆元",
    cat: "四元數",
    spaces: "ℍ",
    deff: "‾q = w − xi − yj − zk；q⁻¹ = ‾q/N(q)。",
    formula: "‾(pq) = ‾q‾p；q q⁻¹ = q⁻¹q = 1；Re q = (q+‾q)/2",
    thm: "定理：ℍ 為可除代數（非交換體）。",
    proof: "共軛於基元上反號並反序；逆元由 q‾q = N(q) ∈ ℝ＼{0}。∎",
    track: "精確 ℚ",
    run: ob_i02,
  })
  xs.push({
    code: "I-03",
    zh: "左乘矩陣表示 L_q",
    cat: "四元數",
    spaces: "ℍ ≅ ℝ⁴",
    deff: "L_q 為 x ↦ qx 於基底 {1,i,j,k} 下之矩陣。",
    formula: "L_{pq} = L_pL_q；L_qᵀL_q = N(q)I₄；det L_q = N(q)²",
    thm: "定理：q ↦ L_q 為 ℍ 至 M₄(ℝ) 之單射代數同態；單位四元數映至 SO(4) 之子群。",
    proof: "同態性由結合律；L_qᵀL_q = N(q)I 由 ⟨qx,qy⟩ = N(q)⟨x,y⟩；取行列式得 det²= N(q)⁴。∎",
    track: "精確 ℚ",
    run: ob_i03,
  })
  xs.push({
    code: "I-04",
    zh: "單位四元數 → SO(3)（Euler–Rodrigues）",
    cat: "四元數",
    spaces: "SU(2) → SO(3)",
    deff: "R(q)v = qv‾q（v 為純虛四元數），展開為 3×3 矩陣。",
    formula: "RᵀR = I；det R = 1",
    thm: "定理：N(q) = 1 ⇒ R(q) ∈ SO(3)。",
    proof: "共軛作用保持純虛子空間與範數 ⇒ 正交；連續性與 R(1) = I ⇒ det = 1。義務以精確有理單位四元數（如 (1,1,1,1)/2、(3,4,0,0)/5）驗證 RᵀR = I 與 det R = 1 於 ℚ 上精確成立。∎",
    track: "精確 ℚ",
    run: ob_i04,
  })
  xs.push({
    code: "I-05",
    zh: "SU(2) → SO(3) 之雙重覆蓋",
    cat: "四元數",
    spaces: "旋轉群",
    deff: "同態 φ(q) = R(q)。",
    formula: "R(pq) = R(p)R(q)；R(−q) = R(q)；ker φ = {±1}",
    thm: "定理：φ : SU(2) → SO(3) 為 2:1 之滿同態（萬有覆蓋）。",
    proof: "同態性由 (pq)v‾(pq) = p(qv‾q)‾p；核為中心元素 ±1。義務同時驗證 R 保內積與叉積（即 R ∈ SO(3) 之作用）。∎",
    track: "精確 ℚ",
    run: ob_i05,
  })
  xs.push({
    code: "I-06",
    zh: "ℍ ↪ M₂(ℂ) 之代數嵌入",
    cat: "四元數",
    spaces: "ℍ → M₂(ℂ)",
    deff: "q = w+xi+yj+zk ↦ [[w+xi, y+zi],[−y+zi, w−xi]]。",
    formula: "det = N(q)；‾q ↦ M*；單位四元數 ↦ SU(2)",
    thm: "定理：此映射為單射之實代數同態，像為 {M ∈ M₂(ℂ) : M = [[α,β],[−‾β,‾α]]}。",
    proof: "逐項驗證保加法與乘法；det = |α|²+|β|² = N(q)；共軛對應共軛轉置。∎",
    track: "精確 ℚ(i)",
    run: ob_i06,
  })
  xs.push({
    code: "I-07",
    zh: "ℍⁿ 作為 4n 維實內積空間",
    cat: "四元數",
    spaces: "S16",
    deff: "⟨p,q⟩ = Σᵢ Re(‾pᵢqᵢ)。",
    formula: "‖qx‖² = N(q)‖x‖²；右乘單位四元數為等距",
    thm: "定理：ℍⁿ 之實內積於左右乘單位四元數下不變（Sp(n)·Sp(1) 對稱性）。",
    proof: "由 N 之乘法性與 Re(‾(qa)(qb)) = N(q)Re(‾ab)。∎",
    track: "精確 ℚ",
    run: ob_i07,
  })

  // ------------------------------------------------------------------
  // J 群：多項式與組合核心
  // ------------------------------------------------------------------
  xs.push({
    code: "J-01",
    zh: "Horner 求值與求值同態",
    cat: "多項式代數",
    spaces: "𝔽[x]",
    deff: "p(t) = (…((c_n t + c_{n−1})t + c_{n−2})…)t + c₀。",
    formula: "Horner ≡ Σcᵢtⁱ；(pq)(t) = p(t)q(t)；(p∘q)(t) = p(q(t))",
    thm: "定理：Horner 法以 n 次乘法與 n 次加法求值，且 ev_t 為環同態。",
    proof: "對次數歸納；同態性由多項式乘法之卷積定義。∎",
    track: "精確 ℚ",
    run: ob_j01,
  })
  xs.push({
    code: "J-02",
    zh: "多項式乘法（卷積）與次數加法",
    cat: "多項式代數",
    spaces: "𝔽[x]",
    deff: "(pq)_k = Σ_{i+j=k} pᵢqⱼ。",
    formula: "deg(pq) = deg p + deg q（整環）",
    thm: "定理：𝔽[x] 為整環；乘法交換、結合、分配。",
    proof: "領導係數之乘積非零（體無零因子）⇒ 次數相加；其餘由卷積之代數性質。∎",
    track: "精確 ℚ",
    run: ob_j02,
  })
  xs.push({
    code: "J-03",
    zh: "由根造多項式與 Vieta 公式",
    cat: "多項式代數",
    spaces: "𝔽[x]",
    deff: "p(x) = Π(x − rᵢ)。",
    formula: "c_{k−1} = −Σrᵢ；c₀ = (−1)^kΠrᵢ",
    thm: "定理（Vieta）：係數為根之初等對稱多項式（帶交錯符號）。",
    proof: "展開乘積並按 x 之冪次收集；每一係數即對應階之初等對稱多項式。∎",
    track: "精確 ℚ",
    run: ob_j03,
  })
  xs.push({
    code: "J-04",
    zh: "形式微分與積分（Leibniz、鏈鎖法則）",
    cat: "多項式代數",
    spaces: "𝔽[x]",
    deff: "D(Σcᵢxⁱ) = Σ icᵢx^{i−1}；∫ 為其右逆（常數項取 0）。",
    formula: "(∫p)′ = p；(pq)′ = p′q + pq′；(p∘q)′ = (p′∘q)q′",
    thm: "定理：形式微分為 𝔽[x] 上之導子（derivation）。",
    proof: "線性由定義；Leibniz 於單項式上驗證後線性延拓；鏈鎖法則同理。特徵 0 時 D∘∫ = id。∎",
    track: "精確 ℚ",
    run: ob_j04,
  })
  xs.push({
    code: "J-05",
    zh: "多重指數列舉與 grlex 全序",
    cat: "組合核心",
    spaces: "S14/S15 之基底",
    deff: "monomials_upto(m,d) 以分次字典序列出 {α ∈ ℕ^m : |α| ≤ d}。",
    formula: "|{α : |α| ≤ d}| = C(m+d, d)",
    thm: "定理：星與條（stars and bars）計數；grlex 為良序之全序。",
    proof: "計數由組合恆等式 Σ_{k≤d}C(m+k−1,k) = C(m+d,d)；全序性由先比較次數再比較字典序。∎",
    track: "精確（組合）",
    run: ob_j05,
  })
  xs.push({
    code: "J-06",
    zh: "子集列舉與楔積符號函數",
    cat: "組合核心",
    spaces: "S17/S18 之基底",
    deff: "subsets_k(n,k) 以遞增字典序列出 k 元子集；ε(I,J) 為合併排序之逆序數符號。",
    formula: "|subsets_k(n,k)| = C(n,k)；Σ_k C(n,k) = 2ⁿ；ε(I,Iᶜ)ε(Iᶜ,I) = (−1)^{k(n−k)}",
    thm: "命題：符號函數與遮罩索引表一致，為外代數運算之正確性基礎。",
    proof: "逆序數之奇偶等於排列之符號；交換兩塊 I 與 Iᶜ 產生 k(n−k) 次對換。∎",
    track: "精確（組合）",
    run: ob_j06,
  })

  // ------------------------------------------------------------------
  // K 群：加速層 ℤ 管 —— 純整數純 CRT 篩選（fp.mbt / crt.mbt / accel.mbt）
  // ------------------------------------------------------------------
  xs.push({
    code: "K-01",
    zh: "多模原子層：素數池與確定性 Miller–Rabin",
    cat: "多模原子層",
    spaces: "加速層 Λ0（全層共用）",
    deff: "取 24 個素數 p ∈ (2³⁰, 2³¹)，於 𝔽p = ℤ/pℤ 上以 Int64 作算術；運算元 < 2³¹ ⇒ 積 < 2⁶² 不溢位。",
    formula: "a·b mod p；a⁻¹ = a^{p−2} mod p（Fermat）",
    thm: "定理：p 素 ⇔ ℤ/pℤ 為體；且 n < 3 215 031 751 時，底 {2,3,5,7} 之強偽素數檢驗為確定性素性判定。",
    proof: "體性：gcd(a,p)=1 ⇒ Bézout 給出逆元；反之 p=ab 時 a 為零因子。無溢位：(p−1)² < 2⁶² < 2⁶³−1。素性判定之確定性取自 Jaeschke 之窮舉結果，本庫另以試除法獨立覆核全池。∎",
    track: "多模 𝔽p",
    run: ob_k01,
  })
  xs.push({
    code: "K-02",
    zh: "中國剩餘定理：Garner 累進合併與對稱提升",
    cat: "CRT 提升",
    spaces: "加速層 Λ1（ℤ 層之縫合）",
    deff: "v′ = v + m·((r − v)·m⁻¹ mod p)，m′ = m·p；對稱代表元取於 (−M/2, M/2]。",
    formula: "ℤ/Mℤ ≅ ∏ ℤ/pᵢℤ，M = ∏pᵢ",
    thm: "定理（CRT）：pᵢ 兩兩互素時上述映射為環同構。推論：|x| < M/2 時對稱提升唯一還原 x。",
    proof: "環同態之核為 ∩(pᵢ) = (M)，兩側基數相同故為同構。合併步之不變量：v′ ≡ v (mod m) 且 v′ ≡ r (mod p)，由建構直接驗證。提升唯一性：兩代表之差為 M 之倍數且絕對值 < M ⇒ 為 0。本條另附「界不足即失效」之反例，證明界為必要而非充分性修飾。∎",
    track: "精確 ℤ（CRT）",
    run: ob_k02,
  })
  xs.push({
    code: "K-03",
    zh: "Hadamard 界與素數個數之先驗決定",
    cat: "CRT 提升",
    spaces: "ℤ 層之提升界",
    deff: "H(A) = ∏ᵢ ⌈√(Σⱼ aᵢⱼ²)⌉；取最小 k 使 ∏_{i<k} pᵢ > 2H。",
    formula: "|det A| ≤ ∏ᵢ ‖aᵢ‖₂",
    thm: "定理（Hadamard）：行列式之絕對值不超過列向量歐氏範數之積。推論：k 個素數即足以唯一決定 det A。",
    proof: "det 為列向量張成之平行多面體之有向體積；Gram–Schmidt 給出 |det| = ∏‖a*ᵢ‖ 而 ‖a*ᵢ‖ ≤ ‖aᵢ‖（投影不增長度）。配合定理 Λ1-3 即得提升唯一性。義務中逐例驗證 |det| ≤ H 與 ∏p > 2H。∎",
    track: "精確 ℤ（CRT）",
    run: ob_k03,
  })
  xs.push({
    code: "K-04",
    zh: "整數行列式之多模 CRT（對照 Bareiss）",
    cat: "ℤ 層加速",
    spaces: "ℤ^{n×n}（源自 C-05 行列式）",
    deff: "dᵢ = det(φ_{pᵢ}A) ∈ 𝔽pᵢ 以前向消去求得（≈n³/3 次字乘法），再 CRT 提升。",
    formula: "φ_p(det A) = det(φ_p A)；det A = CRT_sym(d₁,…,d_k)",
    thm: "定理：det 為矩陣元之整係數多項式，與環同態 φ_p 交換；故多模路徑之輸出與 Bareiss 無分數消去逐位相同。",
    proof: "環同態保持由 +,−,× 組成之多項式映射（推論 Λ1-2）；取 ∏p > 2·Hadamard 界後由對稱提升之唯一性得等式。基準路徑 Bareiss 之每個中間量為子式，位元長度隨步數線性增長（係數膨脹）；模路徑之中間量恆 ≤ 62 位元。∎",
    track: "精確 ℤ（CRT）",
    run: ob_k04,
  })
  xs.push({
    code: "K-05",
    zh: "整數矩陣秩之單素數下界篩與多素數確證",
    cat: "ℤ 層加速",
    spaces: "ℤ^{m×n}（源自 C-04 秩）",
    deff: "rank A ≔ max over primes of rank_{𝔽p}(φ_p A)。",
    formula: "rank_{𝔽p}(φ_p A) ≤ rank_ℚ(A)，等號對幾乎所有 p 成立",
    thm: "命題：模約化只會降秩不會升秩；取多個素數之極大值即得真秩（壞素數為整除某個非零極大子式者，個數有限）。",
    proof: "rank ≥ r ⇔ 存在非零 r 階子式 Δ。φ_p(Δ) ≠ 0 ⇒ Δ ≠ 0 給出下界；反向僅在 p | Δ 時失效，而 Δ ≠ 0 之質因子有限。義務以「指定秩之乘積矩陣 A = BC」逐例驗證等號與下界性。∎",
    track: "精確 ℤ（CRT）",
    run: ob_k05,
  })
  xs.push({
    code: "K-06",
    zh: "整數特徵多項式之多模 Hessenberg CRT",
    cat: "ℤ 層加速",
    spaces: "ℤ^{n×n}（源自 C-16 Faddeev–LeVerrier）",
    deff: "於 𝔽p 上先相似化為上 Hessenberg，再以 Cohen 之遞迴 O(n³) 求 χ_A mod p；逐係數 CRT 提升。",
    formula: "p_m(x) = (x − H_{m−1,m−1})p_{m−1}(x) − Σ_{i=1}^{m−1} H_{m−i−1,m−1}(∏_{j=1}^{i} H_{m−j,m−j−1}) p_{m−i−1}(x)",
    thm: "定理：相似變換保持特徵多項式；Hessenberg 遞迴給出 χ_H = p_n；係數界 |cᵢ| ≤ 2ⁿ‖A‖_∞ⁿ 決定所需素數個數。",
    proof: "消去之列運算與其逆之行運算合成為相似變換 S⁻¹AS；遞迴式由末行之 Laplace 展開得出，次對角線之連乘積恰為唯一非零路徑之權重。係數為特徵值之基本對稱多項式，由 Gershgorin 得 |λ| ≤ ‖A‖_∞。∎",
    track: "精確 ℤ（CRT）",
    run: ob_k06,
  })
  xs.push({
    code: "K-07",
    zh: "伴隨矩陣之多模 CRT（含 plan_zadj 門檻 n ≈ 7）",
    cat: "ℤ 層加速",
    spaces: "ℤ^{n×n}（源自 C-18 adjugate）",
    deff: "於 det ≢ 0 (mod p) 之素數上取 adj A ≡ det(A)·A⁻¹ (mod p)；det ≡ 0 之素數視為壞素數並跳過。",
    formula: "A·adj A = adj A·A = (det A)·I；|（adj A)_{ij}| ≤ H(A)",
    thm: "命題：adj A 之元素為 (n−1) 階餘因子，受同一 Hadamard 界控制；壞素數集合有限，跳過不影響正確性。\n定理（門檻必要性）：伴隨矩陣之輸出為 n² 個整數而非 1 個，故 CRT 重建項帶 n² 因子；實測 n=5 ×0.35、n=8 ×1.70、n=11 ×5.79，交叉點 n ≈ 7。無條件加速在 n < 7 時為淨虧，故須經 plan_zadj 分派。",
    proof: "餘因子為子式，Hadamard 界對子式亦成立（去一列一行只會縮小界）。det A ≠ 0 時只有有限多個 p 整除 det A，故可用之素數充裕。義務同時以 A·adj A = det(A)·I 作獨立覆核。∎",
    track: "精確 ℤ（CRT）",
    run: ob_k07,
  })
  xs.push({
    code: "K-08",
    zh: "Freivalds 乘積篩（A 管：單向可靠之否決）",
    cat: "篩選管線",
    spaces: "ℤ^{n×n}（源自 C-01 矩陣乘法／C-07 乘性）",
    deff: "取隨機 r ∈ 𝔽pⁿ，比較 A(Br) 與 (C)r 於 𝔽p 中是否相等；成本 O(n²) 字乘法。",
    formula: "AB = C ⇒ ∀p,r : φ_p(A)(φ_p(B)r) = φ_p(C)r（逆否即否決規則）",
    thm: "定理（單向可靠性）：若某素數某向量下像不等，則 AB ≠ C 必然成立（零誤否決）。反向誤收之機率 ≤ 1/p + （壞素數比例）。",
    proof: "φ_p 為環同態且矩陣乘法由 +,× 組成，故等式必被保持；取逆否命題得否決之零誤性。誤收：令 D = AB − C ≠ 0，則 Dr = 0 之 r 落在一個真子空間，機率 ≤ 1/p；再考慮 p | D 之壞素數有限。義務以 40 組真實例（零誤否決）與 40 個植入單點錯誤（全數捕捉）實測。∎",
    track: "多模 𝔽p",
    run: ob_k08,
  })
  xs.push({
    code: "K-09",
    zh: "Gram 行列式／k 維體積之 CRT 加速",
    cat: "ℤ 層加速",
    spaces: "ℤ^{m×k}（源自 D-04 Gram 行列式、G-03）",
    deff: "G = AᵀA（整數對稱半正定），det G 以多模 CRT 求得。",
    formula: "vol_k(a₁,…,a_k)² = det G；det G = 0 ⇔ 行向量相依",
    thm: "定理：Gram 行列式非負，且為 k 維平行多面體體積之平方；其退化等價於線性相依。",
    proof: "G = AᵀA ⇒ xᵀGx = ‖Ax‖² ≥ 0 故半正定、det ≥ 0。det G = 0 ⇔ ∃x≠0, Ax = 0 ⇔ 行相依。AᵀA 之元素為內積，位元長度約為輸入之兩倍，故此處係數膨脹尤其嚴重，加速增益明顯。∎",
    track: "精確 ℤ（CRT）",
    run: ob_k09,
  })
  xs.push({
    code: "K-10",
    zh: "ℤ 層分派器之正向性自證",
    cat: "分派策略",
    spaces: "加速層之總控",
    deff: "δ(n,b) = [pred_fast·5 < pred_base·4]；pred 由成本模型（schoolbook 字乘法）給出，含 25% 安全邊際。",
    formula: "δ = true ⇒ cost_fast < cost_base（逐點不劣）",
    thm: "定理：若分派器滿足上述蘊含式，則「基準 ⊕ δ」之系統成本逐點不高於基準，即必為正向優化。",
    proof: "δ 為真時取較小者、為假時取基準，逐點不劣（定理 Λ3-13）。本條於 3×3 之 (n, 位元) 參數網格上實測：所有答案與 Bareiss 一致，且分派器選擇加速之格點其實測增益皆 > 1，無反例。成本模型之參數（0.6·n·(b+6) 位元之中間量、每樞軸 46 次乘法之 Fermat 求逆、1.5k² 之 CRT 累積）皆以實測校準。∎",
    track: "多模 𝔽p",
    run: ob_k10,
  })

  // ------------------------------------------------------------------
  // L 群：加速層 ℚ 管 —— Fp 層級有理數重建篩選（accel.mbt）
  // ------------------------------------------------------------------
  xs.push({
    code: "L-01",
    zh: "有理數重建：格–歐幾里得與唯一性界",
    cat: "有理重建",
    spaces: "加速層 Λ1（ℚ 層之縫合）",
    deff: "對 (M,u) 作擴充歐幾里得，於第一個餘數 rᵢ ≤ N 處輸出 n/d = rᵢ/tᵢ；取 N = D = ⌊√((M−1)/2)⌋。",
    formula: "M > 2ND ⇒ 滿足 |n| ≤ N, 0 < d ≤ D, n ≡ u·d (mod M) 之既約分數唯一",
    thm: "定理（Wang）：上述條件下重建唯一且可由歐幾里得餘數序列讀出。推論：界不足時演算法安全失敗（回 None）而非輸出錯誤答案。",
    proof: "唯一性：兩組解給出 n₁d₂ ≡ n₂d₁ (mod M) 且 |n₁d₂ − n₂d₁| ≤ 2ND < M ⇒ 兩者相等。可讀出性：餘數序列滿足 rᵢ = sᵢM + tᵢu 且 |tᵢ|rᵢ₋₁ < M，於跨越 N 之處即得候選。本實作另以 n ≡ u·d (mod M) 與 gcd(n,d)=1 作輸出前之驗證，故不可能輸出未經檢核之值。∎",
    track: "精確 ℚ（重建+憑證）",
    run: ob_l01,
  })
  xs.push({
    code: "L-02",
    zh: "批次求逆（Montgomery 技巧）",
    cat: "多模原子層",
    spaces: "加速層 Λ0（ℚ 層與插值之熱點）",
    deff: "Pᵢ = v₀⋯v_{i−1}，A = (∏v)⁻¹；後向遞推 vᵢ⁻¹ = A·(∏_{j>i}vⱼ)·Pᵢ。",
    formula: "n 個逆元 = 1 次求逆 + 3n 次乘法",
    thm: "定理：上式確為 vᵢ 之逆；成本由 n 次 Fermat 冪（各約 46 次乘法）降為 O(n)。",
    proof: "直接計算 A·∏_{j>i}vⱼ·Pᵢ = (∏v)⁻¹·(∏v)/vᵢ = vᵢ⁻¹。義務驗證 480 個逆元與 Fermat 路徑逐一相同、v·v⁻¹ = 1，並實測 64 個逆元之乘法次數比（×15.4）。此優化使 Newton 插值之內層由 O(n²) 次求逆降為 O(n) 次。∎",
    track: "多模 𝔽p",
    run: ob_l02,
  })
  xs.push({
    code: "L-03",
    zh: "ℚ 線性方程組：多模解 + 有理重建 + 事後憑證",
    cat: "ℚ 層加速",
    spaces: "ℚ^{n×n}（源自 C-09 線性方程組、C-19 Cramer）",
    deff: "清分母得整數系統 A′x = b′；逐素數解 mod p、逐座標 CRT；重建穩定後以整數算術驗證 A′x̂ = b′。",
    formula: "x = A⁻¹b；憑證 A′x̂ − b′ = 0（精確）",
    thm: "定理（無條件正確性）：A 非奇異且憑證通過 ⇒ x̂ 即唯一解，與素數個數、重建界皆無關。",
    proof: "A 非奇異 ⇒ 解唯一；x̂ 滿足方程 ⇒ x̂ 為該解。故 C 管把「機率／界」論證轉為「確定性」論證：B 管只負責猜，C 管負責證。義務以高斯消去與函式庫 msolve 三路對照，並實測 n=14 之增益。∎",
    track: "精確 ℚ（重建+憑證）",
    run: ob_l03,
  })
  xs.push({
    code: "L-04",
    zh: "ℚ 反矩陣之多模重建與憑證 A·X = I",
    cat: "ℚ 層加速",
    spaces: "ℚ^{n×n}（源自 C-08 反矩陣）",
    deff: "A = A_z/d ⇒ A⁻¹ = d·A_z⁻¹；逐素數求 A_z⁻¹ mod p、逐元 CRT、有理重建，再以整數算術驗證 A·X = I。",
    formula: "A·X = I 之精確整數驗證：A_z·X_z = (d·d_X)·I",
    thm: "定理：憑證通過 ⇒ X = A⁻¹（逆元唯一）。",
    proof: "群中逆元唯一：若 AX = I 且 A 可逆，則 X = A⁻¹AX = A⁻¹。憑證以清分母後之整數乘法完成，成本 O(n³) 但運算元為已重建之小整數，遠低於消去過程中之膨脹中間量。∎",
    track: "精確 ℚ（重建+憑證）",
    run: ob_l04,
  })
  xs.push({
    code: "L-05",
    zh: "ℚ 之 RREF 多模重建 —— 誠實反例（實測 ×0.15，不應加速）",
    cat: "ℚ 層反例",
    spaces: "ℚ^{m×n}（源自 C-03 Gauss–Jordan）",
    deff: "對增廣 [A_z | I] 逐素數作 RREF，只取 A 部分之樞軸型態；取最大秩之型態作 CRT 與重建，輸出 (R, T)。",
    formula: "T·A = R，T 可逆；rank A = #{樞軸 < n}",
    thm: "定理（正確性）：RREF 唯一；模約化只會降秩，故取最大秩之樞軸型態即真型態；憑證 T·A = R ∧ det T ≠ 0 給出無條件正確性。\n定理（負面結果，本條之主張）：本路徑對 ℚ 直接消去為淨虧，且虧損隨 n 擴大 —— 實測 ×0.25／×0.22／×0.15（n=6/10/14）。故本條列為反例，不計入加速層。",
    proof: "正確性：RREF 之唯一性為標準結果（與樞軸選擇無關）。壞素數使某些樞軸消失而降秩，取極大值排除之。T 由增廣之單位塊承載列運算；增廣部分之額外樞軸只會對「A 部分為零列」之列作運算，不影響 A 部分，故截取前 n 行仍為 RREF(A)。∎\n負面結果之成因：CRT 加速之適用條件為「中間量 ≫ 輸出量」。RREF 之輸出為 m×n 個有理數，每個都需獨立之 Θ(k²) CRT 累積與 Θ(w²) 有理重建，合計 Θ(mn·k²)；而 ℚ 直接消去之中間係數膨脹並不比輸出更嚴重，故無膨脹可省。虧損隨 n 擴大即因 CRT 項之 mn 因子隨 n² 成長而消去項僅 n³ 成長。∎",
    track: "精確 ℚ（重建+憑證）",
    run: ob_l05,
  })
  xs.push({
    code: "L-06",
    zh: "正交投影係數之模重建（Gram 正規方程）",
    cat: "ℚ 層加速",
    spaces: "任意 IPSpace（源自 D-05 正交投影）",
    deff: "P_W x = Σcⱼwⱼ，c 解 Gc = b，G_{ij} = ⟨w_j, w_i⟩，b_i = ⟨x, w_i⟩；G c = b 以 ℚ 層加速管求解。",
    formula: "⟨x − P_Wx, w⟩ = 0 ∀w ∈ W",
    thm: "定理（最佳逼近）：殘差與子空間正交之條件等價於正規方程；加速後之係數仍使殘差精確正交。",
    proof: "正規方程由 ⟨x − Σcⱼwⱼ, wᵢ⟩ = 0 直接得出；Gram 矩陣在生成集獨立時可逆。義務不僅比對係數，更直接驗證殘差對每個生成向量之內積精確為 0 —— 此為投影性質之獨立見證，與重建路徑無關。∎",
    track: "精確 ℚ（重建+憑證）",
    run: ob_l06,
  })
  xs.push({
    code: "L-07",
    zh: "最小二乘：連 AᵀA 之組裝都在 𝔽p 上完成",
    cat: "ℚ 層加速",
    spaces: "ℚ^{m×n}（源自 D-22 正規方程）",
    deff: "於每個素數上直接以 𝔽p 算術組裝 G = AᵀA、h = Aᵀb 並求解，再 CRT + 重建；憑證以整數算術驗證 Gx̂ = h。",
    formula: "AᵀA x = Aᵀb；‖Ax̂ − b‖ 最小",
    thm: "命題：AᵀA 之元素位元長度約為輸入之兩倍，於 ℚ 上組裝本身即昂貴；移入 𝔽p 後組裝與求解同為單字運算。",
    proof: "正規方程由投影定理得出。加速之關鍵在於「組裝」亦被下放到 𝔽p：Gᵢⱼ = Σ_k a_{ki}a_{kj} 於 ℤ 上需 m 次大整數乘法，於 𝔽p 上為 m 次字乘法。義務比對精確解並驗證憑證，實測 20×10 之增益。∎",
    track: "精確 ℚ（重建+憑證）",
    run: ob_l07,
  })
  xs.push({
    code: "L-08",
    zh: "Gram 之 LDLᵀ 多模重建 —— 誠實反例（實測 ×0.6，不應加速）",
    cat: "ℚ 層反例",
    spaces: "任意 IPSpace（源自 D-01／D-02 Gram–Schmidt）",
    deff: "於 𝔽p 上作無開方 Cholesky G = LDLᵀ（L 單位下三角），CRT + 重建後以精確算術驗證 LDLᵀ = G。",
    formula: "G = L D Lᵀ；D_{jj} = ‖q_j‖²；det G = ∏ D_{jj}",
    thm: "定理（正確性）：對稱正定矩陣有唯一 LDLᵀ 分解，且 L 之第 j 行即 Gram–Schmidt 展開係數、D 為正交向量之範數平方。\n定理（負面結果，本條之主張）：本路徑永不獲利 —— 實測 ×0.45／×0.56／×0.62（n=6/10/14），比值收斂於約 0.6 而不越過 1。故本條列為反例，不計入加速層。",
    proof: "正確性：對 j 歸納施行無開方 Cholesky，正定性保證 D_{jj} > 0 可除。Gram–Schmidt 之遞迴 q_j = w_j − Σ_{k<j}(⟨w_j,q_k⟩/‖q_k‖²)q_k 與 LDLᵀ 之遞迴逐項對應。義務以函式庫 gram_schmidt 之 ‖q_i‖² 與 det G = ∏Dᵢ 雙重覆核。∎\n負面結果之成因：D_j 為前導主子式之比 D_j = Δ_j/Δ_{j−1}（Bareiss 型），其位元數受 Hadamard 界控制而與輸出同階 —— 即「中間量 ≈ 輸出量」，無係數爆炸可消。CRT 之固定開銷（k 個素數之模消去 + 重建）因此永遠無法被攤銷，比值收斂於一常數而非隨 n 發散。此與 L-05 合為「CRT 不適用條件」之二例。∎",
    track: "精確 ℚ（重建+憑證）",
    run: ob_l08,
  })
  xs.push({
    code: "L-09",
    zh: "對偶基底與 Riesz 表示之重建",
    cat: "ℚ 層加速",
    spaces: "任意 IPSpace（源自 D-08 Riesz、F-04 對偶空間）",
    deff: "對偶基底 wⁱ = Σ_j H_{ij} w_j，H = G⁻¹；以 ℚ 層加速管重建 G⁻¹。",
    formula: "⟨wⁱ, w_j⟩ = δ_{ij}；Riesz 向量 v 滿足 φ(x) = ⟨x, v⟩",
    thm: "定理：Gram 矩陣可逆時對偶基底存在唯一，且其 Gram 矩陣為 G⁻¹（之共軛轉置）。",
    proof: "由 ⟨Σ_j H_{ij}w_j, w_l⟩ = Σ_j H_{ij}G_{lj} = (H Gᵀ)_{il}，取 H = (G⁻¹)ᵀ 即得 δ。Riesz 表示為同一線性系統之特例。義務直接驗證 δ 關係（而非僅比對矩陣），故為性質層級之見證。∎",
    track: "精確 ℚ（重建+憑證）",
    run: ob_l09,
  })
  xs.push({
    code: "L-10",
    zh: "ℚ 層分派器之正向性與壞素數統計",
    cat: "分派策略",
    spaces: "加速層之總控",
    deff: "δ(n,b) 以 n³（完全消去）+ 46n（每樞軸一次 Fermat 求逆）+ 1.4 倍重建／憑證經驗因子估算，含 25% 邊際。",
    formula: "δ = true ⇒ cost_fast < cost_base；壞素數率 ≈ (deg)/(#pool)",
    thm: "定理：分派後之系統逐點不劣。命題：壞素數（det ≡ 0 mod p 或分母 ≡ 0）被安全跳過，不影響正確性只影響素數用量。",
    proof: "正向性同 K-10。壞素數之處理為「跳過並續取下一素數」，由於 det A ≠ 0 只有有限多個質因子，池內必有足夠多之好素數；而 C 管憑證確保即使統計假設失效也不會輸出錯誤答案。義務於 4 個規模上實測且統計壞素數次數。∎",
    track: "精確 ℚ（重建+憑證）",
    run: ob_l10,
  })

  // ------------------------------------------------------------------
  // M 群：加速層 𝔽[x] 管 —— 多項式純 CRT 篩選（accelpoly.mbt）
  // ------------------------------------------------------------------
  xs.push({
    code: "M-01",
    zh: "𝔽[x] 之中國剩餘定理：求值與插值互逆",
    cat: "𝔽[x] 層加速",
    spaces: "𝔽p[x]（源自 E-04 Vandermonde、E-05 Lagrange）",
    deff: "取互異節點 a₀..a_d，求值 f ↦ (f(a₀),…,f(a_d))；逆映射為 Newton 插值（內層以批次求逆攤銷）。",
    formula: "𝔽[x]/∏(x−aᵢ) ≅ ∏ 𝔽[x]/(x−aᵢ) ≅ 𝔽^{d+1}",
    thm: "定理：節點互異 ⇔ 模 (x−aᵢ) 兩兩互素 ⇔ Vandermonde 可逆 ⇔ 插值存在唯一。",
    proof: "𝔽[x] 為主理想整環，CRT 對互質理想成立；(x−aᵢ)+(x−aⱼ) = (1) ⇔ aᵢ ≠ aⱼ。義務驗證「插值∘求值 = 恆等」於 40 個實例，並以節點重複之退化例驗證前提失效時演算法正確失敗。∎",
    track: "精確 𝔽[x]（CRT）",
    run: ob_m01,
  })
  xs.push({
    code: "M-02",
    zh: "數論變換 NTT：2ᵏ 次單位根上之快速 CRT",
    cat: "𝔽[x] 層加速",
    spaces: "𝔽p[x]，p ≡ 1 (mod 2²⁰)",
    deff: "ω = g^{(p−1)/n}（n = 2ᵏ）；Cooley–Tukey 分治求值／插值，逆變換另乘 n⁻¹。",
    formula: "xⁿ − 1 = ∏_{i<n}(x − ωⁱ)；Σ_j ω^{j(i−l)} = n·[i = l]",
    thm: "定理：NTT 即以 2ᵏ 次單位根為節點之 𝔽[x]-CRT，可於 O(n log n) 完成；故多項式乘法為 O(n log n)。",
    proof: "𝔽pˣ 為 p−1 階循環群，2ᵏ | p−1 時存在唯一 2ᵏ 階子群，其生成元即本原單位根。正交關係由幾何級數得出，給出逆變換公式。分治：f = f_even(x²) + x·f_odd(x²) 而 ω² 為 n/2 次本原根，T(n) = 2T(n/2) + O(n)。義務驗證原根之階、正逆互逆、卷積定理，並實測 deg 256 之 ×4.01 增益。∎",
    track: "精確 𝔽[x]（CRT）",
    run: ob_m02,
  })
  xs.push({
    code: "M-03",
    zh: "ℤ[x] 乘法之雙層 CRT（係數 ℤ-CRT × 變數 𝔽[x]-CRT）",
    cat: "𝔽[x] 層加速",
    spaces: "ℤ[x]（源自 J-02 多項式乘法）",
    deff: "對係數施 ℤ 之 CRT（模素數 p），對變數施 𝔽[x] 之 CRT（NTT 求值／插值）；界 |（fg)_k| ≤ (min deg+1)‖f‖_∞‖g‖_∞。",
    formula: "(fg)_k = Σ_{i+j=k} f_i g_j；φ_p(fg) = φ_p(f)·φ_p(g)",
    thm: "定理：兩層 CRT 互相獨立，可任意複合；提升界由上述係數界給出。",
    proof: "係數層：φ_p 為環同態故與卷積交換；變數層：求值為環同態 𝔽p[x] → 𝔽p。兩者作用於不同之代數結構（係數環與多項式環）故可複合。係數界由三角不等式與項數計數得出。義務以 12 組逐係數比對與 deg 96 × 1024 位元之增益實測（×1.62）。∎",
    track: "精確 𝔽[x]（CRT）",
    run: ob_m03,
  })
  xs.push({
    code: "M-04",
    zh: "ℚ[x] 乘法：清分母 + 多模 NTT",
    cat: "𝔽[x] 層加速",
    spaces: "ℚ[x]（源自 J-02；對照 Poly::pmul）",
    deff: "f = F/d_f、g = G/d_g ⇒ fg = (FG)/(d_f d_g)；FG 以多模 NTT 求得。",
    formula: "deg(fg) = deg f + deg g；分母只需在最後約分一次",
    thm: "定理：ℚ 上之直接卷積每次乘法都要一次 gcd 正規化且分母逐步取 lcm 而膨脹；清分母後全部運算落在 ℤ 繼而落在 𝔽p。",
    proof: "ℚ 為 ℤ 之分式體，清分母為同構之重新標度。基準路徑之成本主項為 d² 次 gcd（歐幾里得，Θ(w²)）；加速路徑把 gcd 次數降為輸出長度之一次。義務以 ℚ 卷積與函式庫 Poly::pmul 三路對照，實測 deg 64 之 ×5.10 增益。∎",
    track: "精確 𝔽[x]（CRT）",
    run: ob_m04,
  })
  xs.push({
    code: "M-05",
    zh: "特徵多項式之 𝔽[x] 插值路徑",
    cat: "𝔽[x] 層加速",
    spaces: "ℤ^{n×n}（源自 C-16；對照 K-06 之 Hessenberg 路徑）",
    deff: "於 𝔽p 上對 n+1 個節點 t 計算 det(tI − A)，以插值還原 χ_A mod p，再對係數作 ℤ-CRT。",
    formula: "χ_A(x) = det(xI − A)，首一且 deg = n ⇒ n+1 點唯一決定",
    thm: "定理：行列式於每個節點之值決定整個特徵多項式；此為 𝔽[x]-CRT 之直接應用。",
    proof: "χ_A 為 n 次首一多項式，由 n+1 個互異點之值唯一決定（Vandermonde 可逆）。本路徑之成本為 (n+1)·O(n³)，高於 Hessenberg 之 O(n³)，但仍遠低於 ℚ 上之 Faddeev–LeVerrier（係數膨脹）。義務驗證兩條加速路徑與 char_poly 三路一致，並誠實報告兩者之相對成本。∎",
    track: "精確 𝔽[x]（CRT）",
    run: ob_m05,
  })
  xs.push({
    code: "M-06",
    zh: "ℤ[x] gcd：模 p 篩 + 重建 + 無條件整除性憑證",
    cat: "𝔽[x] 層加速",
    spaces: "ℤ[x]（係數膨脹之經典反例）",
    deff: "逐素數求 gcd_{𝔽p}，取最小次數者作 CRT 與有理重建，再以精確除法驗證 G | f ∧ G | g。",
    formula: "deg gcd_{𝔽p}(f̄,ḡ) ≥ deg gcd_ℚ(f,g)（p ∤ lc）",
    thm: "定理（無條件）：若候選 G 之次數等於各素數所得之最小次數且精確整除 f 與 g，則 G = gcd_ℚ(f,g)。",
    proof: "引理（Gauss）：G | f、G | g 於 ℤ[x] 成立，約化後 Ḡ 為公因式故 deg gcd_p ≥ deg G。若候選滿足整除性則 deg G ≤ deg gcd_ℚ ≤ min_p deg gcd_p = deg G，三者相等故 G 即 gcd。此論證完全不依賴「幸運素數」之機率敘述。義務實測 deg 16 互質對照之增益達 ×4615，印證 ℚ 上歐幾里得之係數膨脹（中間量 3176 位元 vs 93 位元）。∎",
    track: "精確 𝔽[x]（CRT）",
    run: ob_m06,
  })
  xs.push({
    code: "M-07",
    zh: "ℚ 插值之多模重建與逐點憑證",
    cat: "𝔽[x] 層加速",
    spaces: "ℚ[x]（源自 E-05 Lagrange 插值）",
    deff: "節點與值清分母後逐素數插值，係數 CRT + 有理重建；憑證為直接代回 f(xᵢ) = yᵢ。",
    formula: "f(xᵢ) = yᵢ，deg f ≤ d；唯一性由 Vandermonde 給出",
    thm: "定理：憑證通過即無條件正確（唯一性之見證）。",
    proof: "deg ≤ d 且於 d+1 點取值相同之兩多項式其差有 d+1 個根故為零。因此只要代回驗證成立，候選即為那個唯一之插值多項式。義務以 Lagrange 基準與函式庫 lagrange_interp 三路對照，20 節點實測 ×1.25。∎",
    track: "精確 𝔽[x]（CRT）",
    run: ob_m07,
  })
  xs.push({
    code: "M-08",
    zh: "𝔽[x] 層分派器與誠實反例（何時不該加速）",
    cat: "分派策略",
    spaces: "加速層之總控",
    deff: "δ(d,b) 以 NTT 成本 3·sz·lg + sz、係數約化 2d·w、CRT 累積 1.44·d·k² 估算，含 25% 邊際。",
    formula: "δ = true ⇒ cost_fast < cost_base；反例：積樹於 schoolbook 算術下劣於線性累積",
    thm: "定理：分派後逐點不劣。命題（誠實性）：並非所有「理論上更快」之結構都該採用 —— 由根造多項式之積樹在 schoolbook 乘法下反而更貴，分派器必須回答「不加速」。",
    proof: "積樹之優勢建立在「快速乘法」之前提上：以 schoolbook 計，平衡乘法 (m,w)×(m,w) 之成本 m²w² 高於偏斜乘法 (2m,2w)×(1,1)。本條以 32 根之實例實測（積樹 14364 字乘 > 線性 8624 字乘）並要求分派器正確拒絕，證明本庫之「正向優化」宣稱經過反向檢驗而非選擇性報喜。∎",
    track: "精確 𝔽[x]（CRT）",
    run: ob_m08,
  })
  xs
}

///|
/// 目錄執行結果之彙總。
pub struct Verdict {
  entries : Int
  passed : Int
  failed : Int
  instances : Int
  failures : Array[String]
}

///|
/// 執行全部義務並彙總。
pub fn run_catalogue() -> (Array[Check], Verdict) {
  let cat = catalogue()
  let results : Array[Check] = []
  let failures : Array[String] = []
  let mut passed = 0
  let mut instances = 0
  for a in cat {
    let c = (a.run)()
    results.push(c)
    instances = instances + c.trials
    if c.ok {
      passed = passed + 1
    } else {
      failures.push(a.code + " " + a.zh + "：" + c.detail)
    }
  }
  (
    results,
    {
      entries: cat.length(),
      passed,
      failed: cat.length() - passed,
      instances,
      failures,
    },
  )
}

///|
/// 依類別統計條目數。
pub fn category_counts() -> Array[(String, Int)] {
  let cat = catalogue()
  let names : Array[String] = []
  let counts : Array[Int] = []
  for a in cat {
    let mut found = -1
    for i in 0..<names.length() {
      if names[i] == a.cat {
        found = i
      }
    }
    if found < 0 {
      names.push(a.cat)
      counts.push(1)
    } else {
      counts[found] = counts[found] + 1
    }
  }
  Array::makei(names.length(), i => (names[i], counts[i]))
}

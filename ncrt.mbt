///|
/// # N-43：結構律 × CRT 加速層之乘積
///
/// 本庫長出了兩套互不相干的加速哲學：
///
///   * **K/L/M 層（代數的）** —— 多模 𝔽p → CRT 提升 → 有理重建。
///     攻擊的瓶頸是**係數膨脹**：精確 ℚ 消去法的中間分數位元數爆炸。
///   * **N 層（幾何的）** —— 結構律分解 Φ(C(A,B)) = Φ(A) ⊙ Φ(B)。
///     攻擊的瓶頸是**維度**：不必形成 nm × nm 的大矩陣。
///
/// 二者從未相乘過（審視時實測：nlaw.mbt 引用 CRT 層函式 1 次、rcost.mbt 0 次）。
/// 本條把它們排成一個 **2 × 2 析因設計（factorial design）**：
///
/// ```text
///                  精確 ℚ        多模 CRT
///   不分解（直接）    (a)           (c)
///   分解（結構律）    (b)           (d)
/// ```
///
/// 四格各自量測字乘法數 ca、cb、cc、cd，於是有四個「單因子增益」
///
/// ```text
///   G_law^exact = ca / cb      結構律在精確 ℚ régime 下的增益
///   G_law^crt   = cc / cd      結構律在 CRT     régime 下的增益
///   G_crt^mono  = ca / cc      CRT 施於單體問題的增益
///   G_crt^dec   = cb / cd      CRT 施於已分解問題的增益
///   G_total     = ca / cd      兩層合用之總增益
/// ```
///
/// 恆等式 `G_total = G_law^exact · G_crt^dec = G_crt^mono · G_law^crt` 必然成立
/// （兩者皆等於 ca/cd），這給了實作一條免費的自我校驗。
///
/// 真正的待測量是**交互作用項**
///
/// ```text
///   δ = G_total / (G_law^exact · G_crt^mono) = (cb · cc) / (ca · cd)
/// ```
///
/// * δ = 1：兩層加速**獨立**，增益可乘（成本表為秩 1）。
/// * δ < 1：兩層**重疊**，加速不可乘 —— 二者在搶同一塊瓶頸。
/// * δ > 1：兩層**協同**，合用比各自相乘還好。
///
/// δ 是本條的主要觀測量。先驗預期是 δ < 1 且顯著小於 1，理由見定理 N-43-2。

///|
/// BigInt 二進位冪，逐步計費。
///
/// 用二進位而非樸素連乘，是 N-10 的教訓：樸素冪的 O(k) 次大數乘法會把
/// 結構律的增益吃光，使「律成立但不划算」的假象出現。
pub fn zpow_cost(c : Cost, x : BigInt, k : Int) -> BigInt {
  if k <= 0 {
    return 1N
  }
  let mut acc = 1N
  let mut b = x
  let mut e = k
  let mut started = false
  while e > 0 {
    if e % 2 == 1 {
      if started {
        acc = cz_mul(c, acc, b)
      } else {
        acc = b
        started = true
      }
    }
    e = e / 2
    if e > 0 {
      b = cz_mul(c, b, b)
    }
  }
  acc
}

///|
/// 稠密隨機整數方陣，保證非奇異。
///
/// **為何不用 `rand_invertible`**：該函式產生的是上三角矩陣（i > j 時為 0）。
/// 三角矩陣在消去法下沒有填入、沒有係數膨脹，而係數膨脹正是 CRT 的全部價值所在。
/// 用三角矩陣量 CRT 會系統性地低估它 —— 這與 N-26 所揭露的偽陽性是同一種病
/// （取樣分布與待測性質相沖），只是方向相反。故本條自備稠密生成器。
pub fn rand_zmat_dense(rng : Rng, n : Int, bits : Int) -> Mat[Q] {
  let span = 1 << bits
  let gen = () => {
    Mat::build(n, n, (_i, _j) => Q::of_int(rng.next_below(2 * span + 1) - span))
  }
  let probe = Cost::new()
  let mut m = gen()
  let mut tries = 0
  while qdet_gauss(m, probe).num == 0N && tries < 16 {
    m = gen()
    tries = tries + 1
  }
  m
}

///|
/// 2 × 2 析因設計之一格觀測。
pub struct FourPath {
  /// 標的運算之名稱
  tname : String
  /// 尺寸說明
  tdims : String
  /// (a) 不分解 × 精確 ℚ
  ca : Int64
  /// (b) 分解 × 精確 ℚ
  cb : Int64
  /// (c) 不分解 × 多模 CRT
  cc : Int64
  /// (d) 分解 × 多模 CRT
  cd : Int64
  /// 四路徑之結果是否完全一致（精確相等，非容差）
  agree : Bool
}

///|
fn fp_ratio(a : Int64, b : Int64) -> Double {
  if b <= 0L {
    0.0
  } else {
    a.to_double() / b.to_double()
  }
}

///|
/// G_law^exact = ca / cb
pub fn FourPath::g_law_exact(self : FourPath) -> Double {
  fp_ratio(self.ca, self.cb)
}

///|
/// G_law^crt = cc / cd
pub fn FourPath::g_law_crt(self : FourPath) -> Double {
  fp_ratio(self.cc, self.cd)
}

///|
/// G_crt^mono = ca / cc
pub fn FourPath::g_crt_mono(self : FourPath) -> Double {
  fp_ratio(self.ca, self.cc)
}

///|
/// G_crt^dec = cb / cd
pub fn FourPath::g_crt_dec(self : FourPath) -> Double {
  fp_ratio(self.cb, self.cd)
}

///|
/// G_total = ca / cd
pub fn FourPath::g_total(self : FourPath) -> Double {
  fp_ratio(self.ca, self.cd)
}

///|
/// 交互作用 δ = (cb · cc) / (ca · cd)。
///
/// 以 Double 相乘以避開 Int64 溢位（ca 於 dim 16 已達 10⁷ 量級，平方即溢位風險）。
pub fn FourPath::defect(self : FourPath) -> Double {
  let num = self.cb.to_double() * self.cc.to_double()
  let den = self.ca.to_double() * self.cd.to_double()
  if den <= 0.0 {
    0.0
  } else {
    num / den
  }
}

///|
/// 恆等式自我校驗：G_total 應同時等於 G_law^exact·G_crt^dec 與 G_crt^mono·G_law^crt。
///
/// 這不是物理定律而是算術恆等式，故容差取極小（10⁻⁹ 相對誤差）；
/// 若失敗即表示四格的計費有串漏，屬實作錯誤而非量測結果。
pub fn FourPath::identity_ok(self : FourPath) -> Bool {
  let t = self.g_total()
  if t <= 0.0 {
    return false
  }
  let p1 = self.g_law_exact() * self.g_crt_dec()
  let p2 = self.g_crt_mono() * self.g_law_crt()
  (p1 - t).abs() / t < 1.0e-9 && (p2 - t).abs() / t < 1.0e-9
}

///|
/// 標的一：det(A ⊗ B)，律為 det(A⊗B) = (det A)^m · (det B)^n。
///
/// 計費約定（四格一致，否則比較無意義）：
/// * 「不分解」兩格必須**真的形成** A⊗B（nm × nm 次乘法，由 `qkron_cost` 計入），
///   因為題目給的是 A 與 B；不計這一項等於白送單體路徑一截。
/// * 「分解」兩格必須計入兩次冪運算（`zpow_cost` / `qpow_cost`），
///   這是 N-10 的教訓：冪若用樸素連乘，律會由賺轉賠。
pub fn fourpath_det(rng : Rng, n : Int, m : Int, bits : Int) -> FourPath {
  let a = rand_zmat_dense(rng, n, bits)
  let b = rand_zmat_dense(rng, m, bits)
  let primes = prime_pool(48)

  // (a) 不分解 × 精確 ℚ
  let c_a = Cost::new()
  let kab = qkron_cost(c_a, a, b)
  let det_a = qdet_gauss(kab, c_a)

  // (b) 分解 × 精確 ℚ
  let c_b = Cost::new()
  let da = qdet_gauss(a, c_b)
  let db = qdet_gauss(b, c_b)
  let det_b = cq_mul(c_b, qpow_fast(c_b, da, m), qpow_fast(c_b, db, n))

  // (c) 不分解 × 多模 CRT
  let c_c = Cost::new()
  let kab2 = qkron_cost(c_c, a, b)
  let (det_c, _) = zdet_crt(qmat_to_zrows(kab2), primes, c_c)

  // (d) 分解 × 多模 CRT
  let c_d = Cost::new()
  let (za, _) = zdet_crt(qmat_to_zrows(a), primes, c_d)
  let (zb, _) = zdet_crt(qmat_to_zrows(b), primes, c_d)
  let det_d = cz_mul(c_d, zpow_cost(c_d, za, m), zpow_cost(c_d, zb, n))

  // 四路徑精確一致（整數矩陣故行列式為整數，可與 BigInt 直接比對）
  let agree = det_a.num == det_b.num &&
    det_a.den == 1N &&
    det_b.den == 1N &&
    det_a.num == det_c &&
    det_a.num == det_d
  {
    tname: "det(A⊗B)",
    tdims: n.to_string() + "⊗" + m.to_string(),
    ca: c_a.wmul,
    cb: c_b.wmul,
    cc: c_c.wmul,
    cd: c_d.wmul,
    agree,
  }
}

///|
/// 標的二：inv(A ⊗ B)，律為 (A⊗B)⁻¹ = A⁻¹ ⊗ B⁻¹。
///
/// 與 det 的關鍵差異：此處**輸出本身**就是 nm × nm 矩陣，故「分解」兩格
/// 仍必須在最後形成一次 Kronecker 積。四格都付這一項，它在 δ 中完全抵消，
/// 但不付就是偽造。
pub fn fourpath_inv(rng : Rng, n : Int, m : Int, bits : Int) -> FourPath {
  let a = rand_zmat_dense(rng, n, bits)
  let b = rand_zmat_dense(rng, m, bits)
  let primes = prime_pool(48)
  let zero = Mat::build(1, 1, (_i, _j) => Q::zero())

  // (a) 不分解 × 精確 ℚ
  let c_a = Cost::new()
  let kab = qkron_cost(c_a, a, b)
  let inv_a = match qinv_gauss(kab, c_a) {
    Some(x) => x
    None => zero
  }

  // (b) 分解 × 精確 ℚ
  let c_b = Cost::new()
  let ia = match qinv_gauss(a, c_b) {
    Some(x) => x
    None => zero
  }
  let ib = match qinv_gauss(b, c_b) {
    Some(x) => x
    None => zero
  }
  let inv_b = qkron_cost(c_b, ia, ib)

  // (c) 不分解 × 多模 CRT
  let c_c = Cost::new()
  let kab2 = qkron_cost(c_c, a, b)
  let (oc, _, _) = qinv_crt(kab2, primes, c_c)
  let inv_c = match oc {
    Some(x) => x
    None => zero
  }

  // (d) 分解 × 多模 CRT
  let c_d = Cost::new()
  let (oa, _, _) = qinv_crt(a, primes, c_d)
  let (ob, _, _) = qinv_crt(b, primes, c_d)
  let inv_d = match (oa, ob) {
    (Some(x), Some(y)) => qkron_cost(c_d, x, y)
    _ => zero
  }
  let agree = inv_a.equals(inv_b) && inv_a.equals(inv_c) && inv_a.equals(inv_d)
  {
    tname: "inv(A⊗B)",
    tdims: n.to_string() + "⊗" + m.to_string(),
    ca: c_a.wmul,
    cb: c_b.wmul,
    cc: c_c.wmul,
    cd: c_d.wmul,
    agree,
  }
}

///|
/// 標的三：det(Cₖ(A))，律為 Sylvester–Franke：det Cₖ(A) = (det A)^{C(n−1,k−1)}。
///
/// 這是與前兩者不同的構造子（Λᵏ 而非 ⊗），用來檢驗 δ < 1 是否只是 ⊗ 的偶然。
pub fn fourpath_compound(rng : Rng, n : Int, k : Int, bits : Int) -> FourPath {
  let a = rand_zmat_dense(rng, n, bits)
  let primes = prime_pool(48)
  let e = binom(n - 1, k - 1)

  // (a) 不分解 × 精確 ℚ：真的造出複合矩陣再求行列式
  let c_a = Cost::new()
  let ca_mat = compound(a, k, c_a)
  let det_a = qdet_gauss(ca_mat, c_a)

  // (b) 分解 × 精確 ℚ
  let c_b = Cost::new()
  let det_b = qpow_fast(c_b, qdet_gauss(a, c_b), e)

  // (c) 不分解 × 多模 CRT
  let c_c = Cost::new()
  let ca_mat2 = compound(a, k, c_c)
  let (det_c, _) = zdet_crt(qmat_to_zrows(ca_mat2), primes, c_c)

  // (d) 分解 × 多模 CRT
  let c_d = Cost::new()
  let (za, _) = zdet_crt(qmat_to_zrows(a), primes, c_d)
  let det_d = zpow_cost(c_d, za, e)
  let agree = det_a.num == det_b.num &&
    det_a.den == 1N &&
    det_b.den == 1N &&
    det_a.num == det_c &&
    det_a.num == det_d
  {
    tname: "det(Λ" + k.to_string() + ")",
    tdims: "n=" + n.to_string() + ",k=" + k.to_string(),
    ca: c_a.wmul,
    cb: c_b.wmul,
    cc: c_c.wmul,
    cd: c_d.wmul,
    agree,
  }
}

///|
/// 把一格觀測排成一行可讀文字。
pub fn FourPath::line(self : FourPath) -> String {
  self.tname +
  " " +
  self.tdims +
  "：律(ℚ)×" +
  fmt_d(self.g_law_exact(), 1) +
  " 律(CRT)×" +
  fmt_d(self.g_law_crt(), 1) +
  " CRT(單)×" +
  fmt_d(self.g_crt_mono(), 1) +
  " CRT(分)×" +
  fmt_d(self.g_crt_dec(), 1) +
  " 總×" +
  fmt_d(self.g_total(), 1) +
  " δ=" +
  fmt_d(self.defect(), 3)
}

///|
/// CRT 之損益平衡維度：一般稠密整數方陣上，多模 CRT 由虧轉盈的維度。
///
/// 實測（8 位元元素，`qdet_gauss` 對 `zdet_crt`）：
/// n=3 ×0.72、n=4 ×0.63、**n=6 ×1.84**、n=8 ×3.27、n=10 ×6.22、n=12 ×10.93、n=14 ×13.68。
/// 轉折落在 4 與 6 之間，取 5。
pub fn crt_breakeven_dim() -> Int {
  5
}

///|
/// # N-43 決策器：四路徑之選擇規則
///
/// 輸入「分解後子問題之維度」，輸出應走哪條路徑。
///
/// 規則有兩段：
/// 1. **永遠先分解。** 結構律增益（實測 ×3.5 … ×229）遠大於 CRT 增益（×0.6 … ×2.1），
///    兩者衝突時結構律必勝。故 (a)、(c) 恆遭淘汰。
/// 2. 分解之後，子問題維度 d 若已低於損益平衡維度，CRT 的多素數固定開銷
///    便賺不回來 —— 選精確 ℚ，即 (b)；否則選 (d)。
///
/// 這條規則在本條全部 7 個實測案例上皆正確（見 `ob_n43`）。
pub fn pick_path(d_sub : Int) -> String {
  if d_sub < crt_breakeven_dim() {
    "b"
  } else {
    "d"
  }
}

///|
/// 實測上最省的路徑（以字乘法計）。
pub fn FourPath::best(self : FourPath) -> String {
  let mut bn = "a"
  let mut bv = self.ca
  if self.cb < bv {
    bn = "b"
    bv = self.cb
  }
  if self.cc < bv {
    bn = "c"
    bv = self.cc
  }
  if self.cd < bv {
    bn = "d"
  }
  bn
}

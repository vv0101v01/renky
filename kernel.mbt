// ============================================================================
//  axiom/hilbert — 公理化向量空間與有限維內積空間
//  檔案 00：kernel.mbt — 核心工具（偽亂數、初等超越函數、格式化）
//  零第三方依賴：本檔只用 MoonBit builtin（Int / Int64 / UInt64 / Double /
//  String / Array / BigInt）。連 sqrt、sin、cos 都自行實作並附誤差證明義務。
// ============================================================================

// ---------------------------------------------------------------------------
// 【演算法 001】xorshift64* 偽亂數產生器
//
// 定義：狀態 s ∈ 𝔽₂⁶⁴ \ {0}，轉移 T(s) = M₃M₂M₁ s（三個可逆線性映射），
//       輸出 out(s) = (T(s) · C) mod 2⁶⁴，C = 0x2545F4914F6CDD1D（奇數）。
// 命題 001：T 為 𝔽₂ 上之可逆線性變換，故狀態永不落入 0；乘以奇數 C 於
//       ℤ/2⁶⁴ 中可逆，故輸出為雙射之像，週期 2⁶⁴−1。
// 證明：x ↦ x ⊕ (x ≪ k) 之矩陣為單位下三角矩陣（行列式 1，於 𝔽₂ 可逆），
//       x ↦ x ⊕ (x ≫ k) 同理為單位上三角矩陣；三者之積可逆。C 為奇數
//       ⇒ gcd(C, 2⁶⁴)=1 ⇒ C 於環 ℤ/2⁶⁴ˣ 中可逆。∎
// 用途：所有「隨機實例上之恆等式檢驗」之取樣來源（見 Schwartz–Zippel 論證）。
// ---------------------------------------------------------------------------

///|
/// 偽亂數狀態（確定性、可重現；同一 seed 永遠給出同一串測試實例）。
pub struct Rng {
  mut state : UInt64
}

///|
/// 建構子：seed = 0 時改用黃金比例常數 ⌊2⁶⁴/φ⌋，保證狀態非零。
pub fn Rng::new(seed : UInt64) -> Rng {
  { state: if seed == 0UL { 0x9E3779B97F4A7C15UL } else { seed }, }
}

///|
/// 一步轉移並輸出 64 位元。
pub fn Rng::next_u64(self : Rng) -> UInt64 {
  let mut x = self.state
  x = x.lxor(x << 13)
  x = x.lxor(x >> 7)
  x = x.lxor(x << 17)
  self.state = x
  x * 0x2545F4914F6CDD1DUL
}

///|
/// 取 [0, bound) 之非負整數（bound ≤ 0 時回 0）。
pub fn Rng::next_below(self : Rng, bound : Int) -> Int {
  if bound <= 0 {
    return 0
  }
  let hi = (self.next_u64() >> 33).reinterpret_as_int64().to_int()
  let v = if hi < 0 { -hi } else { hi }
  v % bound
}

///|
/// 取 [lo, hi] 之整數（閉區間）。
pub fn Rng::next_range(self : Rng, lo : Int, hi : Int) -> Int {
  if hi <= lo {
    return lo
  }
  lo + self.next_below(hi - lo + 1)
}

///|
/// 取小整數 −k..k（用於造「小有理數」實例，令精確算術不爆長度）。
pub fn Rng::next_small(self : Rng, k : Int) -> Int {
  self.next_range(-k, k)
}

///|
/// 取 [-1, 1) 之雙精度浮點數（53 位元均勻）。
pub fn Rng::next_double(self : Rng) -> Double {
  let m = (self.next_u64() >> 11).reinterpret_as_int64() // 0 ≤ m < 2⁵³
  let u = m.to_double() / 9007199254740992.0 // u ∈ [0,1)
  2.0 * u - 1.0
}

// ---------------------------------------------------------------------------
// 【演算法 002】快速冪（平方‑乘法）
// 定義：pow(x, n) = x^n，n ∈ ℕ。
// 命題 002（迴圈不變量）：令迴圈變數 (acc, b, e)，不變量 I: acc · b^e = x^n。
// 證明：初始 acc=1, b=x, e=n ⇒ I 成立。每步若 e 為奇數則 acc ← acc·b, e ← e−1
//       （I 不變）；否則 b ← b², e ← e/2（I 不變，因 b^e = (b²)^{e/2}）。
//       e 嚴格遞減至 0 ⇒ 終止時 acc = x^n。∎  複雜度 Θ(log n) 次乘法。
// ---------------------------------------------------------------------------

///|
/// 雙精度快速冪（整數指數，支援負指數）。
pub fn ipow_d(x : Double, n : Int) -> Double {
  if n < 0 {
    return 1.0 / ipow_d(x, -n)
  }
  let mut acc = 1.0
  let mut b = x
  let mut e = n
  while e > 0 {
    if e % 2 == 1 {
      acc = acc * b
    }
    b = b * b
    e = e / 2
  }
  acc
}

///|
/// 整數快速冪（Int64，溢位由呼叫端負責；僅用於小型組合數）。
pub fn ipow_i(x : Int64, n : Int) -> Int64 {
  let mut acc = 1L
  let mut b = x
  let mut e = n
  while e > 0 {
    if e % 2 == 1 {
      acc = acc * b
    }
    b = b * b
    e = e / 2
  }
  acc
}

// ---------------------------------------------------------------------------
// 【演算法 003】Newton–Raphson 平方根（自行實作，不借 builtin sqrt）
// 定義：對 a ≥ 0 求 √a，迭代 x_{k+1} = (x_k + a/x_k)/2。
// 命題 003：若 x₀ > 0 則 (i) ∀k≥1, x_k ≥ √a；(ii) (x_k) 單調遞減；
//       (iii) 誤差平方收斂 e_{k+1} = e_k²/(2x_k)，其中 e_k = x_k − √a。
// 證明：(i) AM–GM：x_{k+1} = (x_k + a/x_k)/2 ≥ √(x_k · a/x_k) = √a。
//       (ii) k≥1 時 x_k ≥ √a ⇒ a/x_k ≤ x_k ⇒ x_{k+1} ≤ x_k。
//       (iii) 直接代入：x_{k+1} − √a = (x_k − √a)²/(2x_k)。
//       由 (i)(ii) 與單調有界定理，極限 L 滿足 L = (L + a/L)/2 ⇒ L² = a。∎
// 證明義務 003：∀ 取樣 a ∈ [0, 10⁶]，|sqrt_newton(a)² − a| ≤ 10⁻⁹·max(1,a)。
// ---------------------------------------------------------------------------

///|
/// 自製平方根：位元指數縮放 + 25 次 Newton 迭代（雙精度已達機器精度）。
pub fn sqrt_newton(a : Double) -> Double {
  if a < 0.0 {
    return 0.0 / 0.0 // NaN：√負數於 ℝ 無定義
  }
  if a == 0.0 {
    return 0.0
  }
  // ⚠️ 非有限輸入必須在此攔下。下方的縮放迴圈 `while v >= 4.0 { v = v / 4.0 }`
  // 對 a = +∞ **永不終止**（∞/4 = ∞）。此洞在 N-48 把 ℝ 軌送進複合器時才現形：
  // expm∘expm 之類的複合會把特徵值推到 e^(e^λ)，溢位成 +∞ 後餵給 sqrtm，
  // 整個程序當場掛死。對有限輸入本分支不改變任何行為。
  if a != a || a > 1.0e308 {
    return a
  }
  // 初值：以 2 的冪縮放到 [1,4)，再取 1.5 作初值（保證 x₀ > 0）
  let mut scale = 1.0
  let mut v = a
  while v >= 4.0 {
    v = v / 4.0
    scale = scale * 2.0
  }
  while v < 1.0 {
    v = v * 4.0
    scale = scale / 2.0
  }
  let mut x = 1.5
  for _i in 0..<25 {
    x = 0.5 * (x + v / x)
  }
  x * scale
}

///|
/// 絕對值（避免依賴 builtin 方法名，保持本模組語義自足）。
pub fn absd(x : Double) -> Double {
  if x < 0.0 {
    -x
  } else {
    x
  }
}

///|
/// 雙精度取大。
pub fn maxd(a : Double, b : Double) -> Double {
  if a > b {
    a
  } else {
    b
  }
}

///|
/// 雙精度取小。
pub fn mind(a : Double, b : Double) -> Double {
  if a < b {
    a
  } else {
    b
  }
}

///|
/// 圓周率 π（60 位十進位截斷至雙精度）。
pub let pi_const : Double = 3.14159265358979323846264338327950288419716939937510582097494

// ---------------------------------------------------------------------------
// 【演算法 004】Taylor 級數 sin / cos（含 2π 區間縮減）
// 定義：sin x = Σ_{k≥0} (−1)^k x^{2k+1}/(2k+1)!，cos x = Σ_{k≥0} (−1)^k x^{2k}/(2k)!
// 命題 004（截斷誤差）：交錯級數且 |x| ≤ π 時項絕對值單調遞減，
//       故截斷到第 N 項之誤差 ≤ |第 N+1 項| ≤ π^{2N+3}/(2N+3)!。
//       取 N = 17 ⇒ 誤差 < 10⁻¹⁶（低於雙精度 ulp）。
// 證明：Leibniz 交錯級數定理。區間縮減 x ← x − 2π⌊x/2π⌉ 保 |x| ≤ π，
//       並由 sin、cos 之 2π 週期性保持函數值不變。∎
// 證明義務 004：∀ 取樣 x，|sin²x + cos²x − 1| ≤ 10⁻¹² 且與加法定理相容。
// ---------------------------------------------------------------------------

///|
/// 把角度縮減到 [−π, π]。
fn reduce_angle(x : Double) -> Double {
  let two_pi = 2.0 * pi_const
  let k = (x / two_pi + (if x >= 0.0 { 0.5 } else { -0.5 })).to_int64()
  x - k.to_double() * two_pi
}

///|
/// 自製 sin（Taylor，18 項）。
pub fn sin_taylor(x0 : Double) -> Double {
  let x = reduce_angle(x0)
  let mut term = x
  let mut sum = x
  for k in 1..<18 {
    let d = (2 * k * (2 * k + 1)).to_double()
    term = -term * x * x / d
    sum = sum + term
  }
  sum
}

///|
/// 自製 cos（Taylor，18 項）。
pub fn cos_taylor(x0 : Double) -> Double {
  let x = reduce_angle(x0)
  let mut term = 1.0
  let mut sum = 1.0
  for k in 1..<18 {
    let d = ((2 * k - 1) * (2 * k)).to_double()
    term = -term * x * x / d
    sum = sum + term
  }
  sum
}

// ---------------------------------------------------------------------------
// 【演算法 005】atan2（反正切，四象限）—— Jacobi 旋轉角需要
// 定義：atan2(y,x) = 唯一 θ ∈ (−π, π] 使 (cos θ, sin θ) ∥ (x,y) 同向。
// 方法：先以 atan(t)（|t| ≤ 1 時用連分數/級數 + 兩次倍角縮減）再補象限。
// 命題 005：恆有 cos(atan2(y,x))·r = x 且 sin(atan2(y,x))·r = y，r = √(x²+y²)。
// ---------------------------------------------------------------------------

///|
/// |t| ≤ 1 之 atan：用 atan t = 2·atan( t / (1+√(1+t²)) ) 兩次縮減後展開級數。
fn atan_small(t : Double) -> Double {
  let u = t / (1.0 + sqrt_newton(1.0 + t * t))
  let w = u / (1.0 + sqrt_newton(1.0 + u * u))
  // |w| ≤ tan(π/16) < 0.2 ⇒ 級數 25 項誤差 < 10⁻¹⁸
  let mut term = w
  let mut sum = w
  for k in 1..<25 {
    term = -term * w * w
    sum = sum + term / (2 * k + 1).to_double()
  }
  4.0 * sum
}

///|
/// 四象限反正切。
pub fn atan2_own(y : Double, x : Double) -> Double {
  if x > 0.0 {
    if absd(y) <= x {
      atan_small(y / x)
    } else if y > 0.0 {
      pi_const / 2.0 - atan_small(x / y)
    } else {
      -pi_const / 2.0 - atan_small(x / y)
    }
  } else if x < 0.0 {
    if absd(y) <= -x {
      (if y >= 0.0 { pi_const } else { -pi_const }) + atan_small(y / x)
    } else if y > 0.0 {
      pi_const / 2.0 - atan_small(x / y)
    } else {
      -pi_const / 2.0 - atan_small(x / y)
    }
  } else if y > 0.0 {
    pi_const / 2.0
  } else if y < 0.0 {
    -pi_const / 2.0
  } else {
    0.0
  }
}

// ---------------------------------------------------------------------------
//  格式化工具（報表用；不影響數學內容）
// ---------------------------------------------------------------------------

///|
/// 定點格式化：四捨五入到 nd 位小數。
pub fn fmt_d(x : Double, nd : Int) -> String {
  if x != x {
    return "NaN"
  }
  let neg = x < 0.0
  let v = absd(x)
  if v > 1.0e15 {
    return if neg { "-huge" } else { "huge" }
  }
  let scale = ipow_d(10.0, nd)
  let r = (v * scale + 0.5).to_int64()
  let p = ipow_i(10L, nd)
  let ip = r / p
  let fp = r % p
  let mut frac = fp.to_string()
  while frac.length() < nd {
    frac = "0" + frac
  }
  let body = if nd == 0 { ip.to_string() } else { ip.to_string() + "." + frac }
  if neg && r != 0L {
    "-" + body
  } else {
    body
  }
}

///|
/// 科學記號（僅報表用）。
pub fn fmt_e(x : Double) -> String {
  if x == 0.0 {
    return "0"
  }
  let neg = x < 0.0
  let mut v = absd(x)
  let mut e = 0
  while v >= 10.0 {
    v = v / 10.0
    e = e + 1
  }
  while v < 1.0 {
    v = v * 10.0
    e = e - 1
  }
  (if neg { "-" } else { "" }) + fmt_d(v, 3) + "e" + e.to_string()
}

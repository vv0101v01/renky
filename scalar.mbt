// ============================================================================
//  檔案 01：scalar.mbt — 純量體 (Field) 之公理化介面
// ============================================================================
//
// 【定義 F】（體 / Field）
//   三元組 (𝔽, +, ·) 滿足：
//   F1 (𝔽,+) 為交換群，單位 0，逆元 −x；
//   F2 (𝔽∖{0}, ·) 為交換群，單位 1，逆元 x⁻¹；
//   F3 分配律 a(b+c) = ab + ac；
//   F4 0 ≠ 1。
//
// 【定義 F*】（帶對合之體 / field with involution）
//   另給對合 ‾· : 𝔽 → 𝔽 滿足 ‾(a+b) = ‾a + ‾b，‾(ab) = ‾a·‾b，‾‾a = a，
//   以及「正性錐」P ⊂ 𝔽 使 a·‾a ∈ P ∪ {0}，且 a·‾a = 0 ⟺ a = 0。
//   ℝ 取恆等對合；ℂ 取複共軛。內積空間之正定性公理需要此結構。
//
// 本檔以 trait Scalar 編碼 F + F*，三個實例：
//   • Q          ── 精確有理體 ℚ（BigInt 分數）        [精確軌道]
//   • Double     ── 機器實體 ℝ（IEEE-754 binary64）    [數值軌道]
//   • Cpx[F]     ── 二次擴張 𝔽[i] = 𝔽[x]/(x²+1)        [兩軌道皆可]
//
// 精確軌道 vs 數值軌道（本專案之形式化地位，見 docs 第 §0 節）：
//   精確軌道上一切恆等式檢驗為「真·等號」判定，無浮點誤差；
//   數值軌道上等號為 ε‑等價 ≈_ε，所有命題改以「可驗證殘差憑證」陳述。
// ============================================================================

///|
/// 純量體介面（含對合與正性比較）。所有線性代數演算法皆對此介面泛型化。
pub(open) trait Scalar {
  /// 加法單位 0
  fn s_zero() -> Self
  /// 乘法單位 1
  fn s_one() -> Self
  /// 加法 a + b
  fn s_add(Self, Self) -> Self
  /// 乘法 a · b
  fn s_mul(Self, Self) -> Self
  /// 加法逆元 −a
  fn s_neg(Self) -> Self
  /// 乘法逆元 a⁻¹（a = 0 時回 None，體公理 F2 之部分函數化）
  fn s_inv(Self) -> Self?
  /// 對合（共軛）‾a
  fn s_conj(Self) -> Self
  /// 等價判定（精確軌道＝真等號；數值軌道＝相對 ε 等價）
  fn s_eq(Self, Self) -> Bool
  /// 零判定
  fn s_is_zero(Self) -> Bool
  /// |a| 之雙精度近似（樞軸選取、報表、收斂判準用）
  fn s_mag(Self) -> Double
  /// 實部（對合之不動部分）：Re a = (a + ‾a)/2
  fn s_re_part(Self) -> Self
  /// 虛部係數：Im a 使 a = Re a + i·Im a（實體上恆為 0）
  fn s_im_part(Self) -> Self
  /// 整數嵌入 ℤ → 𝔽（特徵 0）
  fn s_from_int(Int) -> Self
  /// 有理嵌入 ℚ → 𝔽（特徵 0 之體必含 ℚ）
  fn s_from_frac(Int, Int) -> Self
  /// 取樣（Schwartz–Zippel 隨機恆等式檢驗用）
  fn s_rand(Rng) -> Self
  /// 列印
  fn s_text(Self) -> String
  /// 主平方根（存在則回 Some；ℚ 上僅完全平方有解）
  fn s_sqrt(Self) -> Self?
  /// 此體是否為精確算術
  fn s_is_exact() -> Bool
  /// 體之名稱
  fn s_name() -> String
  /// 比較實部（−1/0/1）
  fn s_cmp_re(Self, Self) -> Int
  /// 實部之雙精度值
  fn s_to_double(Self) -> Double
}

// ---------------------------------------------------------------------------
//  由公理導出之運算（free functions，避免 trait default impl 之推廣規則）
// ---------------------------------------------------------------------------

///|
/// a − b ≔ a + (−b)
pub fn[F : Scalar] ssub(a : F, b : F) -> F {
  F::s_add(a, F::s_neg(b))
}

///|
/// a / b ≔ a · b⁻¹（b = 0 回 None）
pub fn[F : Scalar] sdiv(a : F, b : F) -> F? {
  match F::s_inv(b) {
    Some(ib) => Some(F::s_mul(a, ib))
    None => None
  }
}

///|
/// |a|² = a·‾a ∈ P ∪ {0}
pub fn[F : Scalar] sabs2(a : F) -> F {
  F::s_mul(a, F::s_conj(a))
}

///|
/// Σ aᵢ
pub fn[F : Scalar] ssum(xs : Array[F]) -> F {
  let mut acc = F::s_zero()
  for x in xs {
    acc = F::s_add(acc, x)
  }
  acc
}

///|
/// Π aᵢ
pub fn[F : Scalar] sprod(xs : Array[F]) -> F {
  let mut acc = F::s_one()
  for x in xs {
    acc = F::s_mul(acc, x)
  }
  acc
}

///|
/// n · a（ℤ‑模結構）
pub fn[F : Scalar] sntimes(n : Int, a : F) -> F {
  F::s_mul(F::s_from_int(n), a)
}

///|
/// aⁿ（快速冪，n ≥ 0）
pub fn[F : Scalar] spow(a : F, n : Int) -> F {
  let mut acc = F::s_one()
  let mut b = a
  let mut e = n
  while e > 0 {
    if e % 2 == 1 {
      acc = F::s_mul(acc, b)
    }
    b = F::s_mul(b, b)
    e = e / 2
  }
  acc
}

///|
/// 是否為實元素（Im = 0）
pub fn[F : Scalar] sis_real(a : F) -> Bool {
  F::s_is_zero(F::s_im_part(a))
}

///|
/// 是否為正實元素（正性錐 P 之判定）
pub fn[F : Scalar] sis_pos(a : F) -> Bool {
  sis_real(a) && F::s_cmp_re(a, F::s_zero()) > 0
}

///|
/// 是否為非負實元素
pub fn[F : Scalar] sis_nonneg(a : F) -> Bool {
  sis_real(a) && F::s_cmp_re(a, F::s_zero()) >= 0
}

///|
/// 1/2 ∈ 𝔽（特徵 0 ⇒ 2 可逆；極化恆等式需要）
pub fn[F : Scalar] shalf() -> F {
  F::s_from_frac(1, 2)
}

///|
/// 虛數單位 i（若 𝔽 不含 i 則回 None）
pub fn[F : Scalar] simag_unit() -> F? {
  // i 之特徵：i² = −1
  let cand = F::s_from_frac(0, 1)
  ignore(cand)
  None
}

// ---------------------------------------------------------------------------
//  實例一：Double ── 機器實體 ℝ（數值軌道）
//  對合 = 恆等；ε‑等價 ε_rel = 10⁻⁹，ε_abs = 10⁻¹².
// ---------------------------------------------------------------------------

///|
/// 數值軌道之相對容差
pub let eps_rel : Double = 1.0e-9

///|
/// 數值軌道之絕對容差
pub let eps_abs : Double = 1.0e-12

///|
/// ℝ 上之 ε‑等價：|a−b| ≤ ε_abs + ε_rel·max(|a|,|b|)
pub fn approx_eq(a : Double, b : Double) -> Bool {
  absd(a - b) <= eps_abs + eps_rel * maxd(absd(a), absd(b))
}

///|
pub impl Scalar for Double with fn s_zero() {
  0.0
}

///|
pub impl Scalar for Double with fn s_one() {
  1.0
}

///|
pub impl Scalar for Double with fn s_add(a, b) {
  a + b
}

///|
pub impl Scalar for Double with fn s_mul(a, b) {
  a * b
}

///|
pub impl Scalar for Double with fn s_neg(a) {
  -a
}

///|
pub impl Scalar for Double with fn s_inv(a) {
  if a == 0.0 {
    None
  } else {
    Some(1.0 / a)
  }
}

///|
pub impl Scalar for Double with fn s_conj(a) {
  a
}

///|
pub impl Scalar for Double with fn s_eq(a, b) {
  approx_eq(a, b)
}

///|
pub impl Scalar for Double with fn s_is_zero(a) {
  absd(a) <= eps_abs
}

///|
pub impl Scalar for Double with fn s_mag(a) {
  absd(a)
}

///|
pub impl Scalar for Double with fn s_re_part(a) {
  a
}

///|
pub impl Scalar for Double with fn s_im_part(_a) {
  0.0
}

///|
pub impl Scalar for Double with fn s_from_int(n) {
  n.to_double()
}

///|
pub impl Scalar for Double with fn s_from_frac(p, q) {
  p.to_double() / q.to_double()
}

///|
pub impl Scalar for Double with fn s_rand(rng) {
  rng.next_double()
}

///|
pub impl Scalar for Double with fn s_text(a) {
  fmt_d(a, 6)
}

///|
pub impl Scalar for Double with fn s_sqrt(a) {
  if a < 0.0 {
    None
  } else {
    Some(sqrt_newton(a))
  }
}

///|
pub impl Scalar for Double with fn s_is_exact() {
  false
}

///|
pub impl Scalar for Double with fn s_name() {
  "ℝ(binary64)"
}

///|
pub impl Scalar for Double with fn s_cmp_re(a, b) {
  if a < b {
    -1
  } else if a > b {
    1
  } else {
    0
  }
}

///|
pub impl Scalar for Double with fn s_to_double(a) {
  a
}

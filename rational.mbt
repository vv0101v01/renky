// ============================================================================
//  檔案 02：rational.mbt — 精確有理體 ℚ（任意精度，BigInt 分數）
// ============================================================================
//
// 【定義 Q】ℚ ≔ (ℤ × ℤ_{>0}) / ~，(a,b) ~ (c,d) ⟺ ad = bc。
//   代表元正規化：d > 0 且 gcd(|n|, d) = 1 ⇒ 每個等價類唯一代表元。
// 【命題 Q1】正規化後「表示相等 ⟺ 數值相等」。
//   證明：若 n₁/d₁ = n₂/d₂ 且兩者皆既約、分母為正，則 n₁d₂ = n₂d₁；
//   由 gcd(n₁,d₁)=1 得 d₁ | d₂，對稱地 d₂ | d₁，故 d₁ = d₂（皆正），
//   再由消去律 n₁ = n₂。∎  ⇒ 本檔之 s_eq 為「真·等號」，無容差。
// 【命題 Q2】ℚ 為特徵 0 之體，恆等式檢驗在 ℚ 上為可判定（decidable）。
// ============================================================================

// ---------------------------------------------------------------------------
// 【演算法 006】Euclid 輾轉相除最大公因數（BigInt）
// 命題 006（不變量）：I: gcd(x, y) = gcd(|a|, |b|) 於迴圈中恆成立。
// 證明：gcd(x,y) = gcd(y, x mod y) 為 Euclid 引理；y 嚴格遞減且非負
//       ⇒ 良基遞降 ⇒ 終止；終止時 y = 0，gcd(x,0) = x。∎
// ---------------------------------------------------------------------------

///|
/// |a|
pub fn big_abs(a : BigInt) -> BigInt {
  if a < 0N {
    -a
  } else {
    a
  }
}

///|
/// sgn(a) ∈ {−1,0,1}
pub fn big_sign(a : BigInt) -> Int {
  if a > 0N {
    1
  } else if a < 0N {
    -1
  } else {
    0
  }
}

// ---------------------------------------------------------------------------
// 【演算法 006b】機器整數快路徑（small-value fast path）
//
// 動機（實測）：big_gcd 在小值上耗 2250 ns，而同演算法之 Int64 版僅 78 ns
//   （×29）。由於 Q::make 每次呼叫必做一次 gcd，而全庫之精確 ℚ 軌道
//   （A–J 群）幾乎每個運算都經過 Q::make，此處為全庫之單點瓶頸。
//
// 定義（守衛）：fits64(x) :⟺ bitlen(|x|) ≤ 62。
// 命題 006b-1（轉換忠實性）：fits64(x) ⇒ from_int64(to_int64(x)) = x。
//   證明：bitlen(|x|) ≤ 62 ⇒ |x| ≤ 2⁶² − 1 < 2⁶³ − 1 = Int64::max_value，
//   故 x 落於 Int64 可表示區間內，to_int64 為該區間上之單射且 from_int64
//   為其左逆。（bit_length 與正負號無關，已實測：bitlen(−7) = bitlen(7) = 3。）∎
// 命題 006b-2（取反安全性）：fits64(x) ⇒ −to_int64(x) 不溢位。
//   證明：|to_int64(x)| ≤ 2⁶² < 2⁶³ − 1。∎
// 命題 006b-3（結果仍在守衛內）：gcd 與約分皆不增大絕對值，
//   故快路徑之輸出必滿足 fits64，無須再次檢查。∎
// 定理 006b（語意保持）：快路徑與慢路徑在 fits64 成立時輸出相同之 Q。
//   證明：兩者皆計算「除以 gcd 後、分母取正」之既約表示，
//   而既約表示在 ℚ 中唯一（命題 008）。∎
// ---------------------------------------------------------------------------

///|
/// 守衛：|x| ≤ 2⁶² 時可無損轉為 Int64（見命題 006b-1）
fn fits64(x : BigInt) -> Bool {
  x.bit_length() <= 62
}

///|
/// Int64 上之 Euclid gcd（|a|,|b|）
fn gcd64(a : Int64, b : Int64) -> Int64 {
  let mut x = if a < 0L { -a } else { a }
  let mut y = if b < 0L { -b } else { b }
  while y != 0L {
    let t = x % y
    x = y
    y = t
  }
  x
}

///|
/// gcd(|a|,|b|)（Euclid；小值走 Int64 快路徑，見定理 006b）
pub fn big_gcd(a : BigInt, b : BigInt) -> BigInt {
  if fits64(a) && fits64(b) {
    return BigInt::from_int64(gcd64(a.to_int64(), b.to_int64()))
  }
  let mut x = big_abs(a)
  let mut y = big_abs(b)
  while y != 0N {
    let t = x % y
    x = y
    y = t
  }
  x
}

// ---------------------------------------------------------------------------
// 【演算法 007】整數平方根 ⌊√a⌋（Newton，BigInt）＋完全平方判定
// 命題 007：輸出 r 滿足 r² ≤ a < (r+1)²。
// 證明：整數 Newton 迭代 x ← (x + a/x)/2（向下取整除法）由 x₀ ≥ ⌊√a⌋ 開始
//       單調遞減且恆 ≥ ⌊√a⌋（AM–GM 於整數除法下之標準論證），
//       當 x_{k+1} ≥ x_k 時停機並回 x_k = ⌊√a⌋。∎
// ---------------------------------------------------------------------------

///|
/// ⌊√a⌋，a ≥ 0
pub fn big_isqrt(a : BigInt) -> BigInt {
  if a < 0N {
    return 0N
  }
  if a == 0N {
    return 0N
  }
  if a < 4N {
    return 1N
  }
  let bl = a.bit_length()
  let mut x : BigInt = 1N << (bl / 2 + 1)
  while true {
    let y = (x + a / x) >> 1
    if y >= x {
      break
    }
    x = y
  }
  x
}

///|
/// a 是否為完全平方；是則回 Some(√a)
pub fn big_sqrt_exact(a : BigInt) -> BigInt? {
  if a < 0N {
    return None
  }
  let r = big_isqrt(a)
  if r * r == a {
    Some(r)
  } else {
    None
  }
}

// ---------------------------------------------------------------------------
//  ℚ 之型別與運算
// ---------------------------------------------------------------------------

///|
/// 既約分數：不變量 den > 0 ∧ gcd(|num|, den) = 1。
pub struct Q {
  num : BigInt
  den : BigInt
}

///|
/// 正規化建構子（den = 0 為前置條件違反 ⇒ abort）。
pub fn Q::make(n : BigInt, d : BigInt) -> Q {
  // 快路徑：分子分母皆 ≤ 62 位元時全程以 Int64 運算（定理 006b）
  if fits64(n) && fits64(d) {
    let mut a = n.to_int64()
    let mut b = d.to_int64()
    if b == 0L {
      abort("Q::make 前置條件違反：分母為 0（ℚ 中 0 不可逆）")
    }
    if b < 0L {
      a = -a
      b = -b
    }
    if a == 0L {
      return { num: 0N, den: 1N }
    }
    let g = gcd64(a, b)
    return { num: BigInt::from_int64(a / g), den: BigInt::from_int64(b / g) }
  }
  if d == 0N {
    abort("Q::make 前置條件違反：分母為 0（ℚ 中 0 不可逆）")
  }
  let s = if d < 0N { -1N } else { 1N }
  let nn = n * s
  let dd = d * s
  let g = big_gcd(nn, dd)
  if g == 0N {
    { num: 0N, den: 1N, }
  } else {
    { num: nn / g, den: dd / g, }
  }
}

///|
/// ℤ → ℚ
pub fn Q::of_int(n : Int) -> Q {
  { num: BigInt::from_int(n), den: 1N, }
}

///|
/// p/q
pub fn Q::frac(p : Int, q : Int) -> Q {
  Q::make(BigInt::from_int(p), BigInt::from_int(q))
}

///|
pub fn Q::zero() -> Q {
  { num: 0N, den: 1N, }
}

///|
pub fn Q::one() -> Q {
  { num: 1N, den: 1N, }
}

///|
pub fn Q::add(self : Q, o : Q) -> Q {
  Q::make(self.num * o.den + o.num * self.den, self.den * o.den)
}

///|
pub fn Q::mul(self : Q, o : Q) -> Q {
  Q::make(self.num * o.num, self.den * o.den)
}

///|
pub fn Q::neg(self : Q) -> Q {
  { num: -self.num, den: self.den, }
}

///|
pub fn Q::sub(self : Q, o : Q) -> Q {
  self.add(o.neg())
}

///|
pub fn Q::inv(self : Q) -> Q? {
  if self.num == 0N {
    None
  } else {
    Some(Q::make(self.den, self.num))
  }
}

///|
pub fn Q::div(self : Q, o : Q) -> Q? {
  match o.inv() {
    Some(x) => Some(self.mul(x))
    None => None
  }
}

///|
/// 真·等號（由命題 Q1，比較代表元即可）
pub fn Q::eq(self : Q, o : Q) -> Bool {
  self.num == o.num && self.den == o.den
}

///|
/// 全序比較（ℚ 為有序體）
pub fn Q::cmp(self : Q, o : Q) -> Int {
  let l = self.num * o.den
  let r = o.num * self.den
  if l < r {
    -1
  } else if l > r {
    1
  } else {
    0
  }
}

///|
pub fn Q::is_zero(self : Q) -> Bool {
  self.num == 0N
}

///|
pub fn Q::abs(self : Q) -> Q {
  { num: big_abs(self.num), den: self.den, }
}

///|
pub fn Q::to_double(self : Q) -> Double {
  // 以長除法避免 BigInt → Double 溢位：取 18 位有效十進位
  let s = big_sign(self.num).to_double()
  let n = big_abs(self.num)
  let d = self.den
  let ip = n / d
  let rem = n % d
  let mut frac = 0.0
  let mut scale = 1.0
  let mut r = rem
  for _i in 0..<18 {
    r = r * 10N
    let digit = r / d
    r = r % d
    scale = scale / 10.0
    frac = frac + digit.to_int().to_double() * scale
    if r == 0N {
      break
    }
  }
  let ipd = if ip.bit_length() < 62 {
    ip.to_int64().to_double()
  } else {
    1.0e18
  }
  s * (ipd + frac)
}

///|
pub fn Q::text(self : Q) -> String {
  if self.den == 1N {
    self.num.to_string()
  } else {
    self.num.to_string() + "/" + self.den.to_string()
  }
}

///|
/// 精確平方根：僅當分子分母皆完全平方時存在於 ℚ（命題：ℚ 非實閉體）。
pub fn Q::sqrt_exact(self : Q) -> Q? {
  if self.num < 0N {
    return None
  }
  match (big_sqrt_exact(self.num), big_sqrt_exact(self.den)) {
    (Some(a), Some(b)) => Some({ num: a, den: b, })
    _ => None
  }
}

///|
pub impl Show for Q with fn output(self, logger) {
  logger.write_string(self.text())
}

///|
pub extend Q with Show::{to_string, output}

///|
pub impl Scalar for Q with fn s_zero() {
  Q::zero()
}

///|
pub impl Scalar for Q with fn s_one() {
  Q::one()
}

///|
pub impl Scalar for Q with fn s_add(a, b) {
  a.add(b)
}

///|
pub impl Scalar for Q with fn s_mul(a, b) {
  a.mul(b)
}

///|
pub impl Scalar for Q with fn s_neg(a) {
  a.neg()
}

///|
pub impl Scalar for Q with fn s_inv(a) {
  a.inv()
}

///|
pub impl Scalar for Q with fn s_conj(a) {
  a
}

///|
pub impl Scalar for Q with fn s_eq(a, b) {
  a.eq(b)
}

///|
pub impl Scalar for Q with fn s_is_zero(a) {
  a.is_zero()
}

///|
pub impl Scalar for Q with fn s_mag(a) {
  absd(a.to_double())
}

///|
pub impl Scalar for Q with fn s_re_part(a) {
  a
}

///|
pub impl Scalar for Q with fn s_im_part(_a) {
  Q::zero()
}

///|
pub impl Scalar for Q with fn s_from_int(n) {
  Q::of_int(n)
}

///|
pub impl Scalar for Q with fn s_from_frac(p, q) {
  Q::frac(p, q)
}

///|
pub impl Scalar for Q with fn s_rand(rng) {
  // 小有理數：分子 ∈ [−6,6]，分母 ∈ {1,2,3,4}
  Q::frac(rng.next_small(6), rng.next_range(1, 4))
}

///|
pub impl Scalar for Q with fn s_text(a) {
  a.text()
}

///|
pub impl Scalar for Q with fn s_sqrt(a) {
  a.sqrt_exact()
}

///|
pub impl Scalar for Q with fn s_is_exact() {
  true
}

///|
pub impl Scalar for Q with fn s_name() {
  "ℚ(BigInt)"
}

///|
pub impl Scalar for Q with fn s_cmp_re(a, b) {
  a.cmp(b)
}

///|
pub impl Scalar for Q with fn s_to_double(a) {
  a.to_double()
}

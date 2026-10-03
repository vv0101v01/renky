// ============================================================================
//  檔案 03：complex.mbt — 二次擴張 𝔽[i] = 𝔽[x]/(x²+1)
// ============================================================================
//
// 【定義 C】給定體 𝔽（char ≠ 2，且 −1 非平方），Cpx[𝔽] ≔ 𝔽[x]/(x²+1)。
//   以 (a,b) 表 a + bi。運算：
//     (a+bi) + (c+di) = (a+c) + (b+d)i
//     (a+bi)(c+di)    = (ac − bd) + (ad + bc)i
//     ‾(a+bi)         = a − bi                （Galois 對合 Gal(𝔽[i]/𝔽)）
//     (a+bi)⁻¹        = (a − bi)/(a² + b²)
// 【命題 C1】若 −1 於 𝔽 非平方，則 a² + b² = 0 ⟺ a = b = 0，故上式良定義，
//   Cpx[𝔽] 為體。證明：若 b ≠ 0 且 a²+b² = 0 ⇒ (a/b)² = −1，矛盾。∎
// 【命題 C2】N(z) = z‾z = a²+b² 為乘性範數：N(zw) = N(z)N(w)（Brahmagupta–Fibonacci
//   恆等式 (a²+b²)(c²+d²) = (ac−bd)² + (ad+bc)²）。此即 ℂ 上內積正定性之來源。
// 【實例】Cpx[Q] = ℚ(i)（Gauss 有理數，精確軌道）；Cpx[Double] = ℂ（數值軌道）。
// ============================================================================

///|
/// 複數 a + bi（係數取自任意 Scalar 體）
pub struct Cpx[F] {
  cre : F
  cim : F
}

///|
pub fn[F] Cpx::mk(re : F, im : F) -> Cpx[F] {
  { cre: re, cim: im, }
}

///|
/// 實嵌入 𝔽 ↪ 𝔽[i]
pub fn[F : Scalar] Cpx::of_real(re : F) -> Cpx[F] {
  { cre: re, cim: F::s_zero(), }
}

///|
/// 虛數單位 i
pub fn[F : Scalar] Cpx::imag_unit() -> Cpx[F] {
  { cre: F::s_zero(), cim: F::s_one(), }
}

///|
/// 由整數對 (p,q) 造 p + qi
pub fn[F : Scalar] Cpx::ints(p : Int, q : Int) -> Cpx[F] {
  { cre: F::s_from_int(p), cim: F::s_from_int(q), }
}

///|
/// 範數 N(z) = a² + b² ∈ 𝔽
pub fn[F : Scalar] Cpx::norm2(self : Cpx[F]) -> F {
  F::s_add(F::s_mul(self.cre, self.cre), F::s_mul(self.cim, self.cim))
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_zero() {
  { cre: F::s_zero(), cim: F::s_zero(), }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_one() {
  { cre: F::s_one(), cim: F::s_zero(), }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_add(a, b) {
  { cre: F::s_add(a.cre, b.cre), cim: F::s_add(a.cim, b.cim), }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_mul(a, b) {
  {
    cre: ssub(F::s_mul(a.cre, b.cre), F::s_mul(a.cim, b.cim)),
    cim: F::s_add(F::s_mul(a.cre, b.cim), F::s_mul(a.cim, b.cre)),
  }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_neg(a) {
  { cre: F::s_neg(a.cre), cim: F::s_neg(a.cim), }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_inv(a) {
  let n = a.norm2()
  match F::s_inv(n) {
    None => None
    Some(ni) =>
      Some({ cre: F::s_mul(a.cre, ni), cim: F::s_mul(F::s_neg(a.cim), ni), })
  }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_conj(a) {
  { cre: a.cre, cim: F::s_neg(a.cim), }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_eq(a, b) {
  F::s_eq(a.cre, b.cre) && F::s_eq(a.cim, b.cim)
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_is_zero(a) {
  F::s_is_zero(a.cre) && F::s_is_zero(a.cim)
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_mag(a) {
  let x = F::s_mag(a.cre)
  let y = F::s_mag(a.cim)
  sqrt_newton(x * x + y * y)
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_re_part(a) {
  { cre: a.cre, cim: F::s_zero(), }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_im_part(a) {
  { cre: a.cim, cim: F::s_zero(), }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_from_int(n) {
  { cre: F::s_from_int(n), cim: F::s_zero(), }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_from_frac(p, q) {
  { cre: F::s_from_frac(p, q), cim: F::s_zero(), }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_rand(rng) {
  { cre: F::s_rand(rng), cim: F::s_rand(rng), }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_text(a) {
  let r = F::s_text(a.cre)
  let i = F::s_text(a.cim)
  if F::s_is_zero(a.cim) {
    r
  } else if F::s_cmp_re(a.cim, F::s_zero()) < 0 {
    r + "-" + F::s_text(F::s_neg(a.cim)) + "i"
  } else {
    r + "+" + i + "i"
  }
}

///|
/// 僅對「實且非負」之元素給出平方根（內積範數所需之唯一情形）。
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_sqrt(a) {
  if !F::s_is_zero(a.cim) {
    return None
  }
  match F::s_sqrt(a.cre) {
    Some(r) => Some({ cre: r, cim: F::s_zero(), })
    None => None
  }
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_is_exact() {
  F::s_is_exact()
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_name() {
  F::s_name() + "[i]"
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_cmp_re(a, b) {
  F::s_cmp_re(a.cre, b.cre)
}

///|
pub impl[F : Scalar] Scalar for Cpx[F] with fn s_to_double(a) {
  F::s_to_double(a.cre)
}

///|
pub impl[F : Scalar] Show for Cpx[F] with fn output(self, logger) {
  logger.write_string(Scalar::s_text(self))
}

///|
pub extend Cpx with Show::{to_string, output}

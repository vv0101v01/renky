// ============================================================================
//  檔案 08：polyspace.mbt — 多項式空間 P_n(𝔽) 與其上之內積
//    S11 P_n = {deg < n}，L²[−1,1] 內積（精確有理矩）→ Legendre 正交基
//    S12 P_n，L²[0,1] 內積（Hilbert 矩陣，病態 Gram 之經典例）
//    S13 P_n，離散點值內積 ⟨p,q⟩ = Σ_k p(t_k)‾q(t_k)（Lagrange/Vandermonde）
// ============================================================================
//
// 【定義 P】P_n(𝔽) ≔ {a₀ + a₁x + … + a_{n−1}x^{n−1}}，dim = n，基底 {1,x,…,x^{n−1}}。
// 【命題 P1】L² 內積 ⟨p,q⟩ = ∫_{−1}^{1} p(x)‾q(x) dx 之 Gram 矩陣
//   G_{ij} = ∫x^{i+j} = (1+(−1)^{i+j})/(i+j+1) 為正定 ⇒ 的確是內積。
//   證明：⟨p,p⟩ = ∫|p|² ≥ 0；若 = 0 則 p 於 [−1,1] 上連續且平方積分為零 ⇒ p ≡ 0
//   （非零多項式至多 n−1 個根）。∎  本實作以精確有理數計算此積分，無數值誤差。
// 【命題 P2】點值內積（節點相異、個數 m ≥ n）正定：⟨p,p⟩ = Σ|p(t_k)|² = 0
//   ⇒ p 有 m ≥ n 個根 ⇒ p = 0（deg p < n）。等價地 Vandermonde 滿秩。
// ============================================================================

///|
/// 多項式（係數升冪：coef[k] 為 x^k 之係數）
pub struct Poly[F] {
  coef : Array[F]
}

///|
/// 由係數陣列造多項式（低次在前）。
pub fn[F] Poly::of(c : Array[F]) -> Poly[F] {
  { coef: c, }
}

///|
/// 零多項式（長度 n）
pub fn[F : Scalar] Poly::zeros(n : Int) -> Poly[F] {
  { coef: arr_zeros(n), }
}

///|
/// 單項式 x^k（長度 n）
pub fn[F : Scalar] Poly::mono(n : Int, k : Int) -> Poly[F] {
  { coef: Array::makei(n, i => if i == k { F::s_one() } else { F::s_zero() }), }
}

///|
/// 次數（全零回 −1）
pub fn[F : Scalar] Poly::degree(self : Poly[F]) -> Int {
  let mut d = -1
  for i in 0..<self.coef.length() {
    if !F::s_is_zero(self.coef[i]) {
      d = i
    }
  }
  d
}

///|
/// p + q（長度取大者）
pub fn[F : Scalar] Poly::padd(self : Poly[F], o : Poly[F]) -> Poly[F] {
  let n = if self.coef.length() > o.coef.length() {
    self.coef.length()
  } else {
    o.coef.length()
  }
  {
    coef: Array::makei(n, i => {
      let a = if i < self.coef.length() { self.coef[i] } else { F::s_zero() }
      let b = if i < o.coef.length() { o.coef[i] } else { F::s_zero() }
      F::s_add(a, b)
    }),
  }
}

///|
/// c·p
pub fn[F : Scalar] Poly::pscale(self : Poly[F], c : F) -> Poly[F] {
  { coef: Array::makei(self.coef.length(), i => F::s_mul(c, self.coef[i])), }
}

///|
/// −p
pub fn[F : Scalar] Poly::pneg(self : Poly[F]) -> Poly[F] {
  { coef: arr_neg(self.coef), }
}

///|
/// p − q
pub fn[F : Scalar] Poly::psub(self : Poly[F], o : Poly[F]) -> Poly[F] {
  self.padd(o.pneg())
}

// ---------------------------------------------------------------------------
// 【演算法 033】多項式乘法（卷積）(pq)_k = Σ_{i+j=k} p_i q_j
// 命題 033：deg(pq) = deg p + deg q（整環 ⇒ 首項係數乘積非零）；
//   𝔽[x] 為交換整環，乘法結合、分配。
// ---------------------------------------------------------------------------

///|
/// 多項式乘法（學校法；加速層另有 qpoly_mul）。
pub fn[F : Scalar] Poly::pmul(self : Poly[F], o : Poly[F]) -> Poly[F] {
  let n = self.coef.length()
  let m = o.coef.length()
  if n == 0 || m == 0 {
    return { coef: [], }
  }
  let out = arr_zeros(n + m - 1)
  for i in 0..<n {
    if !F::s_is_zero(self.coef[i]) {
      for j in 0..<m {
        out[i + j] = F::s_add(out[i + j], F::s_mul(self.coef[i], o.coef[j]))
      }
    }
  }
  { coef: out, }
}

// ---------------------------------------------------------------------------
// 【演算法 034】Horner 法求值 p(t) = (…((a_{n−1}t + a_{n−2})t + …)t + a₀
// 命題 034：Horner 用 n−1 次乘法與 n−1 次加法（最優，Ostrowski 定理），
//   且其迴圈不變量為 acc = Σ_{j≥k} a_j t^{j−k}。
// ---------------------------------------------------------------------------

///|
/// Horner 求值 p(t)。
pub fn[F : Scalar] Poly::eval(self : Poly[F], t : F) -> F {
  let mut acc = F::s_zero()
  for k = self.coef.length() - 1; k >= 0; k = k - 1 {
    acc = F::s_add(F::s_mul(acc, t), self.coef[k])
  } where {
    proof_invariant: k >= 0,
    proof_invariant: k < self.coef.length(),
    proof_reasoning: (
      #| k 每輪減 1，下界為 −1，故至多 self.coef.length() 輪後終止（Horner 求值）。
    ),
  }
  acc
}

///|
/// 合成 p∘q
pub fn[F : Scalar] Poly::compose(self : Poly[F], q : Poly[F]) -> Poly[F] {
  let mut acc = Poly::{ coef: [], }
  for k = self.coef.length() - 1; k >= 0; k = k - 1 {
    acc = acc.pmul(q).padd({ coef: [self.coef[k]], })
  } where {
    proof_invariant: k >= 0,
    proof_invariant: k < self.coef.length(),
    proof_reasoning: (
      #| k 每輪減 1，下界為 −1，故至多 self.coef.length() 輪後終止（合成由高次至常數項）。
    ),
  }
  acc
}

// ---------------------------------------------------------------------------
// 【演算法 035】形式微分 D 與積分 ∫
// 命題 035：D 為線性算子，ker D = 常數（char 0）；D(pq) = p'q + pq'（Leibniz）。
// ---------------------------------------------------------------------------

///|
/// 形式導數 p'(x)。
pub fn[F : Scalar] Poly::deriv(self : Poly[F]) -> Poly[F] {
  let n = self.coef.length()
  if n <= 1 {
    return { coef: [F::s_zero()], }
  }
  {
    coef: Array::makei(n - 1, i => {
      F::s_mul(F::s_from_int(i + 1), self.coef[i + 1])
    }),
  }
}

///|
/// 不定積分（常數項取 0）
pub fn[F : Scalar] Poly::integ(self : Poly[F]) -> Poly[F] {
  let n = self.coef.length()
  {
    coef: Array::makei(n + 1, i => {
      if i == 0 {
        F::s_zero()
      } else {
        F::s_mul(F::s_from_frac(1, i), self.coef[i - 1])
      }
    }),
  }
}

///|
/// 列印
pub fn[F : Scalar] Poly::text(self : Poly[F]) -> String {
  let mut s = ""
  let mut first = true
  for i in 0..<self.coef.length() {
    if !F::s_is_zero(self.coef[i]) {
      if !first {
        s = s + " + "
      }
      s = s + F::s_text(self.coef[i])
      if i == 1 {
        s = s + "x"
      } else if i > 1 {
        s = s + "x^" + i.to_string()
      }
      first = false
    }
  }
  if first {
    "0"
  } else {
    s
  }
}

///|
/// 相等
pub fn[F : Scalar] Poly::peq(self : Poly[F], o : Poly[F]) -> Bool {
  let n = if self.coef.length() > o.coef.length() {
    self.coef.length()
  } else {
    o.coef.length()
  }
  for i in 0..<n {
    let a = if i < self.coef.length() { self.coef[i] } else { F::s_zero() }
    let b = if i < o.coef.length() { o.coef[i] } else { F::s_zero() }
    if !F::s_eq(a, b) {
      return false
    }
  }
  true
}

///|
/// 補零／截斷到長度 n
pub fn[F : Scalar] Poly::resize(self : Poly[F], n : Int) -> Poly[F] {
  {
    coef: Array::makei(n, i => {
      if i < self.coef.length() {
        self.coef[i]
      } else {
        F::s_zero()
      }
    }),
  }
}

// ---------------------------------------------------------------------------
//  多項式向量空間（共用骨架）
// ---------------------------------------------------------------------------

///|
fn[F : Scalar] poly_vspace(name : String, n : Int) -> VSpace[Poly[F], F] {
  {
    vname: name,
    dim: n,
    zero: Poly::zeros(n),
    add: (a, b) => a.padd(b).resize(n),
    neg: a => a.pneg(),
    smul: (c, a) => a.pscale(c),
    veq: (a, b) => a.peq(b),
    basis: Array::makei(n, k => Poly::mono(n, k)),
    coord: a => a.resize(n).coef,
    expand: c => { coef: c.copy(), },
    vshow: a => a.text(),
    sample: rng => { coef: Array::makei(n, _ => F::s_rand(rng)), },
  }
}

///|
/// 【空間 S11】P_n 配 L²[−1,1]：⟨p,q⟩ = ∫_{−1}^{1} p‾q dx（精確有理矩）。
pub fn[F : Scalar] poly_space_l2(n : Int) -> IPSpace[Poly[F], F] {
  let vs = poly_vspace("P_" + n.to_string() + "，L²[−1,1]", n)
  // 矩 m_k = ∫_{−1}^{1} x^k dx
  //
  // 【第十六輪】預先建表。原寫法每一項都呼叫 s_from_frac(2, k+1)，
  // 而 ℚ 的 s_from_frac 帶一次 gcd 約分；一次內積有 n² 項，
  // 於是每次內積做 n² 次 gcd 去算同樣的 2n−1 個常數。
  // 建表後 gcd 總數由 n²·(呼叫次數) 降為 2n−1 次（一次性）。
  // 數值完全相同 —— 這是共用子式消去。
  let mtab : Array[F] = Array::makei(2 * n + 1, k => {
    if k % 2 == 1 {
      F::s_zero()
    } else {
      F::s_from_frac(2, k + 1)
    }
  })
  let moment = (k : Int) => {
    if k < mtab.length() {
      mtab[k]
    } else if k % 2 == 1 {
      F::s_zero()
    } else {
      F::s_from_frac(2, k + 1)
    }
  }
  {
    vs,
    ipname: "⟨p,q⟩ = ∫₋₁¹ p(x)‾q(x) dx",
    inner: (p, q) => {
      let mut acc = F::s_zero()
      for i in 0..<p.coef.length() {
        for j in 0..<q.coef.length() {
          acc = F::s_add(
            acc,
            F::s_mul(F::s_mul(p.coef[i], F::s_conj(q.coef[j])), moment(i + j)),
          )
        }
      }
      acc
    },
  }
}

///|
/// 【空間 S12】P_n 配 L²[0,1]：Gram = Hilbert 矩陣 H_{ij} = 1/(i+j+1)。
pub fn[F : Scalar] poly_space_hilbert(n : Int) -> IPSpace[Poly[F], F] {
  let vs = poly_vspace(
    "P_" + n.to_string() + "，L²[0,1]（Hilbert Gram）",
    n,
  )
  {
    vs,
    ipname: "⟨p,q⟩ = ∫₀¹ p(x)‾q(x) dx",
    inner: (p, q) => {
      let mut acc = F::s_zero()
      for i in 0..<p.coef.length() {
        for j in 0..<q.coef.length() {
          acc = F::s_add(
            acc,
            F::s_mul(
              F::s_mul(p.coef[i], F::s_conj(q.coef[j])),
              F::s_from_frac(1, i + j + 1),
            ),
          )
        }
      }
      acc
    },
  }
}

///|
/// 【空間 S13】P_n 配離散點值內積（節點相異且 m ≥ n）。
pub fn[F : Scalar] poly_space_nodes(
  n : Int,
  nodes : Array[F],
) -> IPSpace[Poly[F], F] {
  let vs = poly_vspace(
    "P_" +
    n.to_string() +
    "，離散點值（" +
    nodes.length().to_string() +
    " 節點）",
    n,
  )
  {
    vs,
    ipname: "⟨p,q⟩ = Σ_k p(t_k)‾q(t_k)",
    inner: (p, q) => {
      let mut acc = F::s_zero()
      for t in nodes {
        acc = F::s_add(acc, F::s_mul(p.eval(t), F::s_conj(q.eval(t))))
      }
      acc
    },
  }
}

// ---------------------------------------------------------------------------
// 【演算法 036】Vandermonde 矩陣與其行列式
// 命題 036：det V(t₁,…,t_n) = Π_{i<j}(t_j − t_i)。
// 證明：兩邊皆為 t 之多項式；當 t_i = t_j 時兩邊為 0 ⇒ 右式整除左式；
//   比較次數（n(n−1)/2）與領導係數即得。∎
// 推論：節點相異 ⟺ V 可逆 ⟺ 插值問題唯一可解。
// ---------------------------------------------------------------------------

///|
/// V_{kj} = t_k^j，k = 0..m−1，j = 0..n−1
pub fn[F : Scalar] vandermonde(nodes : Array[F], n : Int) -> Mat[F] {
  Mat::build(nodes.length(), n, (k, j) => spow(nodes[k], j))
}

///|
/// Π_{i<j}(t_j − t_i)
pub fn[F : Scalar] vandermonde_det_formula(nodes : Array[F]) -> F {
  let n = nodes.length()
  let mut acc = F::s_one()
  for i in 0..<n {
    for j in (i + 1)..<n {
      acc = F::s_mul(acc, ssub(nodes[j], nodes[i]))
    }
  }
  acc
}

// ---------------------------------------------------------------------------
// 【演算法 037】Lagrange 插值
// 定義：L(x) = Σ_k y_k ℓ_k(x)，ℓ_k(x) = Π_{j≠k}(x − t_j)/(t_k − t_j)。
// 命題 037：L 為唯一次數 < n 且 L(t_k) = y_k 之多項式。
// 證明：ℓ_k(t_j) = δ_{kj}（直接代入）；唯一性由 Vandermonde 可逆（命題 036）。∎
// ---------------------------------------------------------------------------

///|
/// Lagrange 插值：以節點值重建次數 < n 之多項式（Θ(n²)）。
pub fn[F : Scalar] lagrange_interp(
  nodes : Array[F],
  values : Array[F],
) -> Poly[F] {
  let n = nodes.length()
  let mut acc = Poly::{ coef: [F::s_zero()], }
  for k in 0..<n {
    // ℓ_k
    let mut num = Poly::{ coef: [F::s_one()], }
    let mut den = F::s_one()
    for j in 0..<n {
      if j != k {
        num = num.pmul({ coef: [F::s_neg(nodes[j]), F::s_one()], })
        den = F::s_mul(den, ssub(nodes[k], nodes[j]))
      }
    }
    let c = match F::s_inv(den) {
      Some(x) => F::s_mul(values[k], x)
      None => F::s_zero()
    }
    acc = acc.padd(num.pscale(c))
  }
  acc.resize(n)
}

// ---------------------------------------------------------------------------
// 【演算法 038】Legendre 多項式之三項遞推
//   (k+1)P_{k+1}(x) = (2k+1)x P_k(x) − k P_{k−1}(x)，P₀ = 1，P₁ = x。
// 命題 038（正交性）：∫_{−1}^{1} P_m P_k dx = 2/(2k+1) δ_{mk}。
// 命題 038'：對 P_n 之單項式基底施行 Gram–Schmidt（精確 ℚ）所得
//   正交基 g_k 與 P_k 平行：g_k = P_k / lc(P_k)（首一化）。
//   本實作以「GS 結果 × 領導係數 = 遞推結果」作為交叉證明義務。
// ---------------------------------------------------------------------------

///|
/// 回傳 P₀,…,P_{n−1}（每個長度 n）
pub fn[F : Scalar] legendre_rec(n : Int) -> Array[Poly[F]] {
  let out : Array[Poly[F]] = []
  if n <= 0 {
    return out
  }
  out.push(Poly::mono(n, 0))
  if n == 1 {
    return out
  }
  out.push(Poly::mono(n, 1))
  for k in 1..<(n - 1) {
    let xp = out[k].pmul({ coef: [F::s_zero(), F::s_one()], }).resize(n)
    let t1 = xp.pscale(F::s_from_int(2 * k + 1))
    let t2 = out[k - 1].pscale(F::s_from_int(k))
    let num = t1.psub(t2)
    out.push(num.pscale(F::s_from_frac(1, k + 1)).resize(n))
  }
  out
}

// ---------------------------------------------------------------------------
// 【演算法 039】Chebyshev 多項式 T_k 之遞推與合成律
//   T₀ = 1，T₁ = x，T_{k+1} = 2x T_k − T_{k−1}。
// 命題 039（合成律）：T_m ∘ T_k = T_{mk}（源自 cos(mθ)∘cos(kθ)）。
//   本實作以 𝔽[x] 中之精確多項式相等作為證明義務（非數值近似）。
// 命題 039'（離散正交）：於節點 t_j = cos((2j+1)π/(2m)) 上
//   Σ_j T_p(t_j)T_q(t_j) = 0（p ≠ q，p,q < m）。
// ---------------------------------------------------------------------------

///|
/// 回傳 T₀,…,T_{n−1}（每個長度 n）
pub fn[F : Scalar] chebyshev_rec(n : Int) -> Array[Poly[F]] {
  let out : Array[Poly[F]] = []
  if n <= 0 {
    return out
  }
  out.push(Poly::mono(n, 0))
  if n == 1 {
    return out
  }
  out.push(Poly::mono(n, 1))
  for k in 1..<(n - 1) {
    let xp = out[k].pmul({ coef: [F::s_zero(), F::s_from_int(2)], }).resize(n)
    out.push(xp.psub(out[k - 1]).resize(n))
  }
  out
}

// ---------------------------------------------------------------------------
// 【演算法 040】由根造多項式 Π(x − r_i)（Newton 恆等式之輔助）
// ---------------------------------------------------------------------------

///|
/// 由根造多項式 Π (x − rᵢ)（領一化，見 J 群）。
pub fn[F : Scalar] poly_from_roots(roots : Array[F]) -> Poly[F] {
  let mut acc = Poly::{ coef: [F::s_one()], }
  for r in roots {
    acc = acc.pmul({ coef: [F::s_neg(r), F::s_one()], })
  }
  acc
}

// ---------------------------------------------------------------------------
// 【演算法 041】微分算子之矩陣表示 D : P_n → P_n
// 命題 041：D 於單項式基底下之矩陣為 (D)_{i,i+1} = i+1，其餘 0；D 冪零：Dⁿ = 0。
// 推論：D 之特徵值全為 0，χ_D(λ) = λⁿ（可由 char_poly 交叉驗證）。
// ---------------------------------------------------------------------------

///|
/// 微分算子於單項式基之矩陣（超對角為 1..n）。
pub fn[F : Scalar] deriv_matrix(n : Int) -> Mat[F] {
  Mat::build(n, n, (i, j) => {
    if j == i + 1 {
      F::s_from_int(i + 1)
    } else {
      F::s_zero()
    }
  })
}

///|
/// 乘以 x 之算子（P_n → P_{n+1} 截斷至 P_n）
pub fn[F : Scalar] mulx_matrix(n : Int) -> Mat[F] {
  Mat::build(n, n, (i, j) => if i == j + 1 { F::s_one() } else { F::s_zero() })
}

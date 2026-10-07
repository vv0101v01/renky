// ============================================================================
//  檔案 16：oblig_space.mbt — 證明義務 D（抽象內積演算法）、E（具體空間）、
//  F（空間組合子）、G（外代數與行列式幾何）
// ============================================================================

///|
/// 標準測試舞台：ℚ 上之多項式空間（dim 5，即 deg ≤ 4，L²[−1,1] 內積）
/// 注意本函式庫之慣例：poly_space_*(n) 之 n 即「係數個數」= dim。
fn stage_poly() -> IPSpace[Poly[Q], Q] {
  poly_space_l2(5)
}

///|
/// 標準測試舞台：ℚ⁵ 歐氏空間
fn stage_euc() -> IPSpace[Array[Q], Q] {
  euclidean_space(5)
}

///|
/// 標準測試舞台：ℚ(i) 上之 ℂ³
fn stage_cpx() -> IPSpace[Array[Cpx[Q]], Cpx[Q]] {
  unitary_space(3)
}

///|
/// 取 k 個隨機向量
fn[V, F] samples(s : IPSpace[V, F], rng : Rng, k : Int) -> Array[V] {
  Array::makei(k, _ => (s.vs.sample)(rng))
}

///|
/// ℚ 上有理正交矩陣（Cayley 變換，保證 QᵀQ = I 精確成立）
fn rational_orthogonal(rng : Rng, n : Int) -> Mat[Q] {
  for _t in 0..<60 {
    let s0 = qmat(rng, n, n)
    let s = s0.minus(s0.transpose())
    match cayley_transform(s) {
      Some(q) => return q
      None => ()
    }
  }
  Mat::ident(n)
}

// ===========================================================================
//  D 群：抽象內積空間演算法（對任意 IPSpace 泛型）
// ===========================================================================

///|
/// D-01 經典 Gram–Schmidt：正交性 + span 保持 + 上三角 R（x_j = Σ R_ij u_i）。
pub fn ob_d01() -> Check {
  let rng = ob_rng()
  let s = stage_poly()
  let mut ok = true
  for _t in 0..<10 {
    let xs = samples(s, rng, 5)
    let g = gram_schmidt(s, xs)
    if !is_orthogonal_set(s, g.ortho) {
      ok = false
    }
    // x_j = Σ_i R_{ij} u_i
    for j in 0..<xs.length() {
      let c = Array::makei(g.ortho.length(), i => g.rmat.at(i, j))
      if !(s.vs.veq)(vlincomb(s.vs, c, g.ortho), xs[j]) {
        ok = false
      }
    }
    // span 相等：rank 一致
    let m1 : Mat[Q] = Mat::of_cols(xs.map(x => vcoord(s.vs, x)))
    let m2 : Mat[Q] = Mat::of_cols(g.ortho.map(x => vcoord(s.vs, x)))
    if mrank(m1) != mrank(m2) || mrank(m2) != g.ortho.length() {
      ok = false
    }
  }
  mk_check(
    "D-01 Gram–Schmidt 正交化", ok, 10, "uᵢ⊥uⱼ；x_j = ΣR_ij u_i；span 保持",
  )
}

///|
/// D-02 改良 Gram–Schmidt：精確算術下與 CGS 同構（張成同一旗 flag）。
pub fn ob_d02() -> Check {
  let rng = ob_rng()
  let s = stage_euc()
  let mut ok = true
  for _t in 0..<10 {
    let xs = samples(s, rng, 4)
    let a = gram_schmidt(s, xs)
    let b = modified_gram_schmidt(s, xs)
    if a.ortho.length() != b.ortho.length() {
      ok = false
    } else {
      for i in 0..<a.ortho.length() {
        if !(s.vs.veq)(a.ortho[i], b.ortho[i]) {
          ok = false
        }
      }
    }
    if !is_orthogonal_set(s, b.ortho) {
      ok = false
    }
  }
  mk_check(
    "D-02 改良 Gram–Schmidt", ok, 10, "精確算術下 MGS ≡ CGS（逐項相等）",
  )
}

///|
/// D-03 正規化：ℚ 上一般失敗（√∉ℚ），ℝ 上成功且得標準正交基。
pub fn ob_d03() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut q_success = 0
  let mut q_fail = 0
  // ℚ 中之完全平方判定：既約 p/q 為平方 ⟺ p ≥ 0 且 |p|、q 皆為完全平方
  let q_is_square = (x : Q) => {
    if Q::cmp(x, Q::zero()) < 0 {
      false
    } else {
      let rn = big_isqrt(x.num)
      let rd = big_isqrt(x.den)
      rn * rn == x.num && rd * rd == x.den
    }
  }
  let sq : IPSpace[Array[Q], Q] = euclidean_space(5)
  // (1) 刻劃定理：ℚ 上可標準正交化 ⟺ Gram–Schmidt 之各範數平方皆為 ℚ 中完全平方
  for _t in 0..<4 {
    let xs = samples(sq, rng, 3)
    if !linearly_independent(sq, xs) {
      continue
    }
    let gs = gram_schmidt(sq, xs)
    let mut all_sq = true
    for u in gs.ortho {
      if !q_is_square((sq.inner)(u, u)) {
        all_sq = false
      }
    }
    let got = orthonormalize(sq, xs)
    let succeeded = !(got is None)
    // 這是本條之主張：成功與否恰由「範數平方是否皆為完全平方」決定
    if succeeded != all_sq {
      ok = false
    }
    if succeeded {
      q_success = q_success + 1
      match got {
        Some(es) => if !is_orthonormal_set(sq, es) { ok = false }
        None => ()
      }
    } else {
      q_fail = q_fail + 1
    }
    n = n + 1
  }
  // (2) 肯定面：有理正交矩陣（Cayley 變換）之行必可於 ℚ 上標準正交化
  for _t in 0..<3 {
    let qm = rational_orthogonal(rng, 4)
    let se4 : IPSpace[Array[Q], Q] = euclidean_space(4)
    let cols : Array[Array[Q]] = Array::makei(4, j2 => qm.col(j2))
    // 同一刻劃定理之肯定面：此處 GS 範數平方皆為 1（完全平方），故必成功
    let gs4 = gram_schmidt(se4, cols)
    let mut all_sq4 = true
    for u in gs4.ortho {
      if !q_is_square((se4.inner)(u, u)) {
        all_sq4 = false
      }
    }
    let got4 = orthonormalize(se4, cols)
    let succeeded4 = !(got4 is None)
    if succeeded4 != all_sq4 {
      ok = false
    }
    if !succeeded4 {
      ok = false
    }
    q_success = q_success + 1
    match got4 {
      None => ()
      Some(es) => if !is_orthonormal_set(se4, es) { ok = false }
    }
    n = n + 1
  }
  // (3) ℝ 上恆可（正定性保證範數為正實數，開方封閉）
  let sr : IPSpace[Array[Double], Double] = euclidean_space(5)
  let rngr = ob_rng()
  for _t in 0..<3 {
    let ys = samples(sr, rngr, 3)
    match orthonormalize(sr, ys) {
      None => ok = false
      Some(es) => if !is_orthonormal_set(sr, es) { ok = false }
    }
    n = n + 1
  }
  mk_check(
    "D-03 標準正交化（體相依性）",
    ok,
    n,
    "刻劃定理「ℚ 上可標準正交化 ⟺ GS 各範數平方皆為 ℚ 中完全平方」雙向逐例驗證：否定面 " +
    q_fail.to_string() +
    " 組（隨機 ℚ 基底，範數平方非平方 ⇒ 失敗）、肯定面 " +
    q_success.to_string() +
    " 組（有理正交矩陣之行，範數平方 = 1 ⇒ 成功），無一例外；另 6 組 ℝ 上恆成功（開方封閉）",
  )
}

///|
/// D-04 Gram 行列式、k 維體積與 Hadamard 不等式 det G ≤ Π‖xᵢ‖²。
pub fn ob_d04() -> Check {
  let rng = ob_rng()
  let s = stage_euc()
  let mut ok = true
  for _t in 0..<10 {
    let xs = samples(s, rng, 3)
    let g = gram_det(s, xs)
    // 非負
    if Q::cmp(g, Q::zero()) < 0 {
      ok = false
    }
    // Hadamard
    let mut prod = Q::one()
    for x in xs {
      prod = prod.mul((s.inner)(x, x))
    }
    if Q::cmp(g, prod) > 0 {
      ok = false
    }
    // 體積 = √det G
    let v = volume_k(s, xs)
    if absd(v * v - Q::to_double(g)) > 1.0e-6 * maxd(1.0, Q::to_double(g)) {
      ok = false
    }
    // 線性相依 ⇒ det G = 0
    let dep = [xs[0], xs[1], vadd(s.vs, xs[0], xs[1])]
    if !Q::is_zero(gram_det(s, dep)) {
      ok = false
    }
    if linearly_independent(s, dep) {
      ok = false
    }
  }
  mk_check(
    "D-04 Gram 行列式／體積／Hadamard 不等式", ok, 10, "0 ≤ detG ≤ Π‖xᵢ‖²；相依 ⟺ detG=0",
  )
}

///|
/// D-05 正交投影：殘差 ⊥ W、冪等、最佳逼近（優於任意其他 w ∈ W）。
pub fn ob_d05() -> Check {
  let rng = ob_rng()
  let s = stage_poly()
  let mut ok = true
  for _t in 0..<10 {
    let ws = samples(s, rng, 2)
    let x = (s.vs.sample)(rng)
    let p = project_onto(s, ws, x)
    let r = vsub(s.vs, x, p)
    for w in ws {
      if !Q::is_zero((s.inner)(r, w)) {
        ok = false
      }
    }
    // 冪等
    if !(s.vs.veq)(project_onto(s, ws, p), p) {
      ok = false
    }
    // 最佳逼近
    let d0 = ip_norm(s, r)
    for _k in 0..<5 {
      let c = Array::makei(2, _ => qr(rng))
      let w2 = vlincomb(s.vs, c, ws)
      if ip_norm(s, vsub(s.vs, x, w2)) < d0 - 1.0e-12 {
        ok = false
      }
    }
    // 畢氏：‖x‖² = ‖P x‖² + ‖r‖²
    if !Q::eq((s.inner)(x, x), Q::add((s.inner)(p, p), (s.inner)(r, r))) {
      ok = false
    }
  }
  mk_check(
    "D-05 正交投影與最佳逼近定理", ok, 10, "r⊥W、P²=P、‖x−Px‖ 最小、畢氏分解",
  )
}

///|
/// D-06 到子空間之距離：d(x,W) = 0 ⟺ x ∈ W；單調性（W₁ ⊆ W₂ ⇒ d₂ ≤ d₁）。
pub fn ob_d06() -> Check {
  let rng = ob_rng()
  let s = stage_euc()
  let mut ok = true
  for _t in 0..<10 {
    let w1 = samples(s, rng, 2)
    let w2 = [w1[0], w1[1], (s.vs.sample)(rng)]
    let x = (s.vs.sample)(rng)
    let d1 = distance_to_subspace(s, w1, x)
    let d2 = distance_to_subspace(s, w2, x)
    if d2 > d1 + 1.0e-12 {
      ok = false
    }
    if distance_to_subspace(s, w1, w1[0]) > 1.0e-12 {
      ok = false
    }
  }
  mk_check(
    "D-06 子空間距離", ok, 10, "x∈W ⇒ d=0；W₁⊆W₂ ⇒ d(x,W₂) ≤ d(x,W₁)",
  )
}

///|
/// D-07 投影矩陣：P² = P、關於 G 自伴（P*G = GP）、rank P = dim W、tr P = dim W。
pub fn ob_d07() -> Check {
  let rng = ob_rng()
  let s = stage_poly()
  let g = gram_of_space(s)
  let mut ok = true
  for _t in 0..<10 {
    let ws = samples(s, rng, 2)
    if !linearly_independent(s, ws) {
      continue
    }
    let p = projection_matrix(s, ws)
    if !p.times(p).equals(p) {
      ok = false
    }
    if !p.adjointm().times(g).equals(g.times(p)) {
      ok = false
    }
    if mrank(p) != 2 {
      ok = false
    }
    if !p.trace().eq(Q::of_int(2)) {
      ok = false
    }
  }
  mk_check("D-07 投影矩陣 P²=P、P*G=GP", ok, 10, "rank P = tr P = dim W")
}

///|
/// D-08 Riesz 表示定理：φ(x) = ⟨x, v_φ⟩ 對所有 x 成立。
pub fn ob_d08() -> Check {
  let rng = ob_rng()
  let s = stage_poly()
  let mut ok = true
  let mut n = 0
  for _t in 0..<5 {
    n = n + 1
    let c = Array::makei(s.vs.dim, _ => qr(rng))
    let v = riesz_vector(s, c)
    for _k in 0..<4 {
      let x = (s.vs.sample)(rng)
      if !Q::eq(dual_eval(s, c, x), (s.inner)(x, v)) {
        ok = false
      }
    }
  }
  // 複空間版本（共軛線性）
  let sc = stage_cpx()
  for _t in 0..<5 {
    n = n + 1
    let c : Array[Cpx[Q]] = Array::makei(3, _ => Cpx::mk(qr(rng), qr(rng)))
    let v = riesz_vector(sc, c)
    for _k in 0..<3 {
      let x = (sc.vs.sample)(rng)
      if !Scalar::s_eq(dual_eval(sc, c, x), (sc.inner)(x, v)) {
        ok = false
      }
    }
  }
  mk_check(
    "D-08 Riesz 表示定理", ok, n, "φ(x)=⟨x,v_φ⟩；5 個實泛函（各 4 點）＋ 5 個複泛函（各 3 點）",
  )
}

///|
/// D-09 伴隨算子：⟨Tx, y⟩_W = ⟨x, T*y⟩_V。
pub fn ob_d09() -> Check {
  let rng = ob_rng()
  let p = stage_poly() // dim 5
  let q : IPSpace[Array[Q], Q] = euclidean_space(3)
  let mut ok = true
  let mut n = 0
  for _t in 0..<5 {
    n = n + 1
    let tmat = qmat(rng, 3, 5)
    let ast = adjoint_matrix(p, q, tmat)
    for _k in 0..<4 {
      let x = (p.vs.sample)(rng)
      let y = (q.vs.sample)(rng)
      let tx = (q.vs.expand)(tmat.apply(vcoord(p.vs, x)))
      let ty = (p.vs.expand)(ast.apply(vcoord(q.vs, y)))
      if !Q::eq((q.inner)(tx, y), (p.inner)(x, ty)) {
        ok = false
      }
    }
  }
  // 複情形：標準正交基下 [T*] = [T]*
  let sc = stage_cpx()
  for _t in 0..<5 {
    n = n + 1
    let tmat : Mat[Cpx[Q]] = Mat::build(3, 3, (_i, _j) => {
      Cpx::mk(qr(rng), qr(rng))
    })
    let ast = adjoint_matrix(sc, sc, tmat)
    if !ast.equals(tmat.adjointm()) {
      ok = false
    }
  }
  mk_check(
    "D-09 伴隨算子 [T*] = G_V⁻¹[T]*G_W", ok, n, "5 個 ℚ 算子驗 ⟨Tx,y⟩=⟨x,T*y⟩（各 4 組 x,y）＋ 5 個複算子驗 ONB 下退化為共軛轉置",
  )
}

///|
/// D-10 Fourier 展開：x = Σ⟨x,eᵢ⟩eᵢ（以有理正交矩陣造精確 ONB）。
pub fn ob_d10() -> Check {
  let rng = ob_rng()
  let n = 4
  let s : IPSpace[Array[Q], Q] = euclidean_space(n)
  let qm = rational_orthogonal(rng, n)
  let onb : Array[Array[Q]] = Array::makei(n, j => qm.col(j))
  let mut ok = is_orthonormal_set(s, onb)
  for _t in 0..<10 {
    let x = (s.vs.sample)(rng)
    let c = fourier_coeffs(s, onb, x)
    if !(s.vs.veq)(fourier_synthesis(s, onb, c), x) {
      ok = false
    }
  }
  mk_check(
    "D-10 Fourier 係數與重建", ok, 10, "有理正交基（Cayley）上 x = Σ⟨x,eᵢ⟩eᵢ 精確成立",
  )
}

///|
/// D-11/12 Bessel 不等式（真子集）與 Parseval 恆等式（完備基）。
pub fn ob_d11() -> Check {
  let rng = ob_rng()
  let n = 4
  let s : IPSpace[Array[Q], Q] = euclidean_space(n)
  let qm = rational_orthogonal(rng, n)
  let full : Array[Array[Q]] = Array::makei(n, j => qm.col(j))
  let part : Array[Array[Q]] = Array::makei(2, j => qm.col(j))
  let mut ok = true
  let mut strict = false
  for _t in 0..<10 {
    let x = (s.vs.sample)(rng)
    let (sp, nx) = bessel_pair(s, part, x)
    if sp > nx + 1.0e-9 {
      ok = false
    }
    if sp < nx - 1.0e-9 {
      strict = true
    }
    let (sf, nf) = bessel_pair(s, full, x)
    if absd(sf - nf) > 1.0e-9 * maxd(1.0, nf) {
      ok = false
    }
  }
  mk_check(
    "D-11/12 Bessel 不等式與 Parseval 恆等式",
    ok && strict,
    10,
    "真子集嚴格小於；完備基取等",
  )
}

///|
/// D-13 Cauchy–Schwarz：鬆弛量 δ ≥ 0，且 δ = 0 ⟺ 線性相依。
pub fn ob_d13() -> Check {
  let rng = ob_rng()
  let s = stage_poly()
  let mut ok = true
  let mut n = 0
  for _t in 0..<5 {
    n = n + 1
    let x = (s.vs.sample)(rng)
    let y = (s.vs.sample)(rng)
    let d = cauchy_schwarz_slack(s, x, y)
    if Q::cmp(d, Q::zero()) < 0 {
      ok = false
    }
    let indep = linearly_independent(s, [x, y])
    if indep && Q::is_zero(d) {
      ok = false
    }
    if !indep && !Q::is_zero(d) {
      ok = false
    }
    // 相依例必取等
    let c = qr(rng)
    let y2 = (s.vs.smul)(c, x)
    if !Q::is_zero(cauchy_schwarz_slack(s, x, y2)) {
      ok = false
    }
  }
  // 複空間
  let sc = stage_cpx()
  for _t in 0..<5 {
    n = n + 1
    let x = (sc.vs.sample)(rng)
    let y = (sc.vs.sample)(rng)
    let d = cauchy_schwarz_slack(sc, x, y)
    if Q::cmp(d.cre, Q::zero()) < 0 || !d.cim.is_zero() {
      ok = false
    }
  }
  mk_check(
    "D-13 Cauchy–Schwarz（精確憑證）", ok, n, "δ = ⟨x,x⟩⟨y,y⟩−|⟨x,y⟩|² ≥ 0，等號 ⟺ 相依；5 例 ℚ（含刻意相依之取等例）＋ 5 例複（δ 實且非負）",
  )
}

///|
/// D-14 三角不等式（ℚ 上免開方之精確判定）。
pub fn ob_d14() -> Check {
  let rng = ob_rng()
  let s = stage_poly()
  let mut ok = true
  for _t in 0..<10 {
    let x = (s.vs.sample)(rng)
    let y = (s.vs.sample)(rng)
    if !triangle_holds(s, x, y) {
      ok = false
    }
    // 數值交叉驗證
    let lhs = ip_norm(s, vadd(s.vs, x, y))
    let rhs = ip_norm(s, x) + ip_norm(s, y)
    if lhs > rhs + 1.0e-9 {
      ok = false
    }
  }
  mk_check(
    "D-14 三角不等式", ok, 10, "精確判定 (c−a−b ≤ 0) ∨ ((c−a−b)² ≤ 4ab)",
  )
}

///|
/// D-15 平行四邊形律：‖x+y‖²+‖x−y‖² = 2‖x‖²+2‖y‖²（內積空間之特徵）。
pub fn ob_d15() -> Check {
  let rng = ob_rng()
  let mut n = 0
  let spaces_ok = {
    let mut ok = true
    let s1 = stage_poly()
    let s2 = stage_euc()
    let s3 : IPSpace[Mat[Q], Q] = sym_matrix_space(3)
    for _t in 0..<4 {
      if n < 10 {
        n = n + 1
        if !Q::is_zero(
            parallelogram_defect(s1, (s1.vs.sample)(rng), (s1.vs.sample)(rng)),
          ) {
          ok = false
        }
      }
      if n < 10 {
        n = n + 1
        if !Q::is_zero(
            parallelogram_defect(s2, (s2.vs.sample)(rng), (s2.vs.sample)(rng)),
          ) {
          ok = false
        }
      }
      if n < 10 {
        n = n + 1
        if !Q::is_zero(
            parallelogram_defect(s3, (s3.vs.sample)(rng), (s3.vs.sample)(rng)),
          ) {
          ok = false
        }
      }
    }
    ok
  }
  mk_check(
    "D-15 平行四邊形律", spaces_ok, n, "P₅ / ℝⁿ / Sym₃ 三個空間輪流取樣共 10 例，恆等式皆精確為 0",
  )
}

///|
/// D-16/17 極化恆等式（實：4⟨x,y⟩ = ‖x+y‖²−‖x−y‖²；複：加虛部項）。
pub fn ob_d16() -> Check {
  let rng = ob_rng()
  let s = stage_poly()
  let mut ok = true
  let mut n = 0
  for _t in 0..<5 {
    n = n + 1
    let x = (s.vs.sample)(rng)
    let y = (s.vs.sample)(rng)
    if !Q::eq(polarization_real(s, x, y), (s.inner)(x, y)) {
      ok = false
    }
  }
  let sc = stage_cpx()
  for _t in 0..<5 {
    n = n + 1
    let x = (sc.vs.sample)(rng)
    let y = (sc.vs.sample)(rng)
    if !Scalar::s_eq(polarization_complex(sc, x, y), (sc.inner)(x, y)) {
      ok = false
    }
  }
  mk_check(
    "D-16/17 極化恆等式（實與複）", ok, n, "內積可由範數完全還原；5 例實極化 ＋ 5 例複極化",
  )
}

///|
/// D-18 畢氏定理：x ⊥ y ⇒ ‖x+y‖² = ‖x‖²+‖y‖²（並驗逆命題於實空間成立）。
pub fn ob_d18() -> Check {
  let rng = ob_rng()
  let s = stage_euc()
  let mut ok = true
  for _t in 0..<10 {
    let x = (s.vs.sample)(rng)
    let y0 = (s.vs.sample)(rng)
    // 以投影造正交對
    let y = vsub(s.vs, y0, project_onto(s, [x], y0))
    if !ip_orth(s, x, y) {
      ok = false
    }
    let lhs = (s.inner)(vadd(s.vs, x, y), vadd(s.vs, x, y))
    let rhs = Q::add((s.inner)(x, x), (s.inner)(y, y))
    if !Q::eq(lhs, rhs) {
      ok = false
    }
    // 非正交時失敗（逆命題，實空間）
    if !Q::is_zero((s.inner)(x, y0)) {
      let l2 = (s.inner)(vadd(s.vs, x, y0), vadd(s.vs, x, y0))
      let r2 = Q::add((s.inner)(x, x), (s.inner)(y0, y0))
      if Q::eq(l2, r2) {
        ok = false
      }
    }
  }
  mk_check(
    "D-18 畢氏定理（含逆命題）", ok, 10, "⟂ ⟺ ‖x+y‖²=‖x‖²+‖y‖²（實空間）",
  )
}

///|
/// D-19 正交補與正交分解 V = W ⊕ W^⊥，(W^⊥)^⊥ = W。
pub fn ob_d19() -> Check {
  let rng = ob_rng()
  let s = stage_poly() // dim 5
  let n = s.vs.dim
  let mut ok = true
  for _t in 0..<10 {
    let ws = samples(s, rng, 2)
    if !linearly_independent(s, ws) {
      continue
    }
    let wp = orthogonal_complement(s, ws)
    if wp.length() != n - 2 {
      ok = false
    }
    for w in ws {
      for u in wp {
        if !Q::is_zero((s.inner)(w, u)) {
          ok = false
        }
      }
    }
    // 分解唯一性：x = P_W x + P_{W⊥} x
    for _k in 0..<4 {
      let x = (s.vs.sample)(rng)
      let a = project_onto(s, ws, x)
      let b = project_onto(s, wp, x)
      if !(s.vs.veq)(vadd(s.vs, a, b), x) {
        ok = false
      }
    }
    // (W^⊥)^⊥ = W（維數 + 包含）
    let wpp = orthogonal_complement(s, wp)
    if wpp.length() != 2 {
      ok = false
    }
    for v in wpp {
      if distance_to_subspace(s, ws, v) > 1.0e-12 {
        ok = false
      }
    }
  }
  mk_check(
    "D-19 正交分解 V = W ⊕ W^⊥", ok, 10, "維數相加、交為 0、(W^⊥)^⊥ = W",
  )
}

///|
/// D-20 等距判定與 Gram 變換律 G' = S*GS。
pub fn ob_d20() -> Check {
  let rng = ob_rng()
  let s = stage_poly()
  let g = gram_of_space(s)
  let n = s.vs.dim
  let mut ok = true
  // 恆等為等距
  if !is_isometry(s, Mat::ident(n)) {
    ok = false
  }
  for _t in 0..<10 {
    // 任取可逆 S：G' = S*GS 應為新基底之 Gram
    let sm = qmat_invertible(rng, n)
    let g2 = gram_change_of_basis(g, sm)
    let newbasis : Array[Poly[Q]] = Array::makei(n, j => {
      (s.vs.expand)(sm.col(j))
    })
    if !gram_of(s, newbasis).equals(g2) {
      ok = false
    }
    // 一般 S 非等距
    if is_isometry(s, sm) && !g2.equals(g) {
      ok = false
    }
    // 由 Cholesky 型構造等距：在歐氏空間上有理正交矩陣即等距
    let se : IPSpace[Array[Q], Q] = euclidean_space(4)
    let qm = rational_orthogonal(rng, 4)
    if !is_isometry(se, qm) {
      ok = false
    }
  }
  mk_check(
    "D-20 等距與基底變換律", ok, 10, "G' = S*GS；正交矩陣為等距",
  )
}

///|
/// D-21 Householder 反射：等距、對合、把 v 映為 −v、固定 v^⊥。
pub fn ob_d21() -> Check {
  let rng = ob_rng()
  let s = stage_euc()
  let mut ok = true
  for _t in 0..<10 {
    let v = (s.vs.sample)(rng)
    if Q::is_zero((s.inner)(v, v)) {
      continue
    }
    let x = (s.vs.sample)(rng)
    let hx = householder(s, v, x)
    // 等距
    if !Q::eq((s.inner)(hx, hx), (s.inner)(x, x)) {
      ok = false
    }
    // 對合
    if !(s.vs.veq)(householder(s, v, hx), x) {
      ok = false
    }
    // H v = −v
    if !(s.vs.veq)(householder(s, v, v), (s.vs.neg)(v)) {
      ok = false
    }
    // 固定 v^⊥
    let w = vsub(s.vs, x, project_onto(s, [v], x))
    if !(s.vs.veq)(householder(s, v, w), w) {
      ok = false
    }
  }
  mk_check(
    "D-21 Householder 反射", ok, 10, "等距、H²=I、Hv=−v、H|_{v^⊥}=id",
  )
}

///|
/// D-22 最小二乘：正規方程、殘差正交、殘差範數最小。
pub fn ob_d22() -> Check {
  let rng = ob_rng()
  let s = stage_poly()
  let mut ok = true
  for _t in 0..<10 {
    let ws = samples(s, rng, 2)
    let x = (s.vs.sample)(rng)
    let (c, rn) = least_squares(s, ws, x)
    let r = vsub(s.vs, x, vlincomb(s.vs, c, ws))
    for w in ws {
      if !Q::is_zero((s.inner)(r, w)) {
        ok = false
      }
    }
    if absd(rn - ip_norm(s, r)) > 1.0e-12 {
      ok = false
    }
    // 正規方程 Gram·c = b
    let a : Mat[Q] = Mat::build(2, 2, (i, j) => (s.inner)(ws[j], ws[i]))
    let b : Array[Q] = Array::makei(2, i => (s.inner)(x, ws[i]))
    if !arr_eq(a.apply(c), b) {
      ok = false
    }
  }
  mk_check(
    "D-22 最小二乘與正規方程", ok, 10, "Gram·c = b，殘差 ⊥ span{wⱼ}",
  )
}

///|
/// D-23 夾角與餘弦相似度：cos ∈ [−1,1]、自身夾角 0、正交夾角 π/2。
pub fn ob_d23() -> Check {
  let rng = ob_rng()
  let s = stage_euc()
  let mut ok = true
  let pi = 4.0 * atan2_own(1.0, 1.0)
  for _t in 0..<10 {
    let x = (s.vs.sample)(rng)
    let y = (s.vs.sample)(rng)
    let c = cosine_similarity(s, x, y)
    if c > 1.0 + 1.0e-12 || c < -1.0 - 1.0e-12 {
      ok = false
    }
    if absd(angle_between(s, x, x)) > 1.0e-6 {
      ok = false
    }
    let yp = vsub(s.vs, y, project_onto(s, [x], y))
    if absd(angle_between(s, x, yp) - pi / 2.0) > 1.0e-7 {
      ok = false
    }
    // 對稱性
    if absd(angle_between(s, x, y) - angle_between(s, y, x)) > 1.0e-9 {
      ok = false
    }
  }
  mk_check(
    "D-23 夾角與餘弦相似度", ok, 10, "|cos| ≤ 1；θ(x,x)=0；θ(x,x^⊥)=π/2",
  )
}

// ===========================================================================
//  E 群：具體空間之專屬定理
// ===========================================================================

///|
/// E-01 Legendre：GS 正交化單項式基 ≡ 遞推公式（至正規化常數）。
pub fn ob_e01() -> Check {
  let dim = 10 // deg ≤ 9（取樣政策：E 群 10 例 ⇒ 10 個 Legendre 多項式）
  let s : IPSpace[Poly[Q], Q] = poly_space_l2(dim)
  let monos : Array[Poly[Q]] = Array::makei(dim, k => Poly::mono(dim, k))
  let g = gram_schmidt(s, monos)
  let leg : Array[Poly[Q]] = legendre_rec(dim)
  let mut ok = g.ortho.length() == dim
  if ok {
    for k in 0..<dim {
      // GS 之輸出為首一（monic）；Legendre 需除以首項係數
      let p = leg[k]
      let lead = p.coef[k]
      match Q::inv(lead) {
        None => ok = false
        Some(li) =>
          if !Poly::peq(g.ortho[k], p.pscale(li).resize(dim)) {
            ok = false
          }
      }
    }
  }
  mk_check(
    "E-01 Legendre 多項式 = GS(1,x,…,x⁵)", ok, dim, "首一化後逐項相等（精確 ℚ）",
  )
}

///|
/// E-02 Legendre 正交性與範數 ∫₋₁¹ PₖPₘ = 2/(2k+1)·δ。
pub fn ob_e02() -> Check {
  let dim = 7 // deg ≤ 6
  let s : IPSpace[Poly[Q], Q] = poly_space_l2(dim)
  let leg : Array[Poly[Q]] = legendre_rec(dim)
  let mut ok = true
  for k in 0..<dim {
    for m in 0..<dim {
      let v = (s.inner)(leg[k], leg[m])
      let want = if k == m { Q::frac(2, 2 * k + 1) } else { Q::zero() }
      if !Q::eq(v, want) {
        ok = false
      }
    }
  }
  mk_check(
    "E-02 Legendre 正交性",
    ok,
    dim * dim,
    "⟨Pₖ,Pₘ⟩ = 2/(2k+1)·δₖₘ",
  )
}

///|
/// E-03 Chebyshev 合成律 T_m ∘ T_k = T_{mk}。
pub fn ob_e03() -> Check {
  let dim = 13 // T₀..T₁₂
  let t : Array[Poly[Q]] = chebyshev_rec(dim)
  let mut ok = true
  let mut cnt = 0
  for m in 0..<5 {
    for k in 0..<5 {
      if m * k <= dim - 1 && cnt < 10 {
        cnt = cnt + 1
        let lhs = t[m].compose(t[k])
        let rhs = t[m * k]
        let d = maxi(lhs.coef.length(), rhs.coef.length())
        if !Poly::peq(lhs.resize(d), rhs.resize(d)) {
          ok = false
        }
      }
    }
  }
  // 三項遞推 T_{k+1} = 2x T_k − T_{k−1}
  for k in 1..<(dim - 1) {
    let x : Poly[Q] = Poly::of([Q::zero(), Q::of_int(2)])
    let rhs = x.pmul(t[k]).psub(t[k - 1])
    let d = maxi(rhs.coef.length(), t[k + 1].coef.length())
    if !Poly::peq(rhs.resize(d), t[k + 1].resize(d)) {
      ok = false
    }
  }
  mk_check("E-03 Chebyshev T_m∘T_k = T_{mk}", ok, cnt, "並驗三項遞推")
}

///|
/// E-04 Vandermonde 行列式 = Π_{i<j}(t_j − t_i)，以及其可逆性。
pub fn ob_e04() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<10 {
    let k = rng.next_range(2, 5)
    let nodes : Array[Q] = []
    let mut tries = 0
    while nodes.length() < k && tries < 100 {
      tries = tries + 1
      let c = qr(rng)
      let mut dup = false
      for x in nodes {
        if x.eq(c) {
          dup = true
        }
      }
      if !dup {
        nodes.push(c)
      }
    }
    if nodes.length() < k {
      continue
    }
    let v = vandermonde(nodes, k)
    if !mdet(v).eq(vandermonde_det_formula(nodes)) {
      ok = false
    }
    if Q::is_zero(mdet(v)) {
      ok = false
    }
  }
  mk_check(
    "E-04 Vandermonde 行列式公式", ok, 10, "det V = Π_{i<j}(t_j−t_i) ≠ 0（節點相異）",
  )
}

///|
/// E-05 Lagrange 插值：p(t_k) = y_k，且唯一（次數 < 節點數）。
pub fn ob_e05() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<10 {
    let k = 4
    let nodes : Array[Q] = [
      Q::of_int(-2),
      Q::frac(-1, 2),
      Q::of_int(1),
      Q::of_int(3),
    ]
    let ys : Array[Q] = Array::makei(k, _ => qr(rng))
    let p = lagrange_interp(nodes, ys)
    for i in 0..<k {
      if !p.eval(nodes[i]).eq(ys[i]) {
        ok = false
      }
    }
    // 唯一性：由 Vandermonde 系統之解唯一
    let v = vandermonde(nodes, k)
    match msolve(v, ys).solvable {
      false => ok = false
      true => {
        let c = msolve(v, ys).particular
        if !Poly::peq(Poly::of(c).resize(k), p.resize(k)) {
          ok = false
        }
      }
    }
  }
  mk_check(
    "E-05 Lagrange 插值與唯一性", ok, 10, "p(tᵢ)=yᵢ；與 Vandermonde 解一致",
  )
}

///|
/// E-06 微分算子 D 於 P_n 上冪零：D^{n+1} = 0，χ_D(λ) = λ^{n+1}；
/// 並驗 Heisenberg 關係 [D, X] = I 於截斷子空間上成立。
pub fn ob_e06() -> Check {
  let dim = 10 // P_{deg ≤ 9}（取樣政策：E 群 10 例）
  let d : Mat[Q] = deriv_matrix(dim)
  let x : Mat[Q] = mulx_matrix(dim)
  let mut ok = mpow(d, dim).equals(Mat::zeros(dim, dim))
  if mpow(d, dim - 1).equals(Mat::zeros(dim, dim)) {
    ok = false // 冪零指數恰為 dim
  }
  let cp = char_poly(d)
  for i in 0..<dim {
    if !cp[i].is_zero() {
      ok = false
    }
  }
  // [D,X] = I 於前 dim−1 個座標（最高次項被截斷）
  let comm = d.times(x).minus(x.times(d))
  for i in 0..<(dim - 1) {
    for j in 0..<(dim - 1) {
      let want = if i == j { Q::one() } else { Q::zero() }
      if !comm.at(i, j).eq(want) {
        ok = false
      }
    }
  }
  mk_check(
    "E-06 微分算子冪零與 Heisenberg 關係", ok, dim, "D^dim=0 且 D^{dim−1}≠0，χ_D=λ^dim，[D,X]=I",
  )
}

///|
/// E-07 Hilbert Gram 矩陣：G_{ij} = 1/(i+j+1)，正定、行列式為已知有理數、病態。
pub fn ob_e07() -> Check {
  let dim = 6
  let s : IPSpace[Poly[Q], Q] = poly_space_hilbert(dim)
  let g = gram_of_space(s)
  let mut ok = true
  for i in 0..<dim {
    for j in 0..<dim {
      if !g.at(i, j).eq(Q::frac(1, i + j + 1)) {
        ok = false
      }
    }
  }
  if !is_positive_definite(g) {
    ok = false
  }
  // 數值條件數極大（病態）：κ₂(H₆) > 10⁶
  let gd : RMat = Mat::build(dim, dim, (i, j) => Q::to_double(g.at(i, j)))
  let kappa = cond2(gd)
  if kappa < 1.0e6 {
    ok = false
  }
  mk_check(
    "E-07 Hilbert Gram 正定且病態",
    ok,
    dim * dim,
    "G_ij = 1/(i+j+1)；κ₂ ≈ " + fmt_e(kappa),
  )
}

///|
/// E-08 離散點值空間：Gram = VᵀV；節點數 ≥ dim 時正定，否則退化。
pub fn ob_e08() -> Check {
  let mut ok = true
  let mut n = 0
  let mut degen = 0
  let mut pdcnt = 0
  // 掃描：維度 dim × 節點數 m，驗證 G = VᵀV、rank G = min(m, dim)、
  //   以及「正定 ⟺ m ≥ dim」（節點互異時 Vandermonde 列滿秩）
  for dim in [2, 3, 4, 5] {
    for m in [dim - 2, dim - 1, dim, dim + 1, dim + 2] {
      if m < 1 || n >= 10 {
        continue
      }
      let nodes : Array[Q] = Array::makei(m, k => Q::of_int(k - m / 2))
      let s : IPSpace[Poly[Q], Q] = poly_space_nodes(dim, nodes)
      let g = gram_of_space(s)
      let v = vandermonde(nodes, dim)
      // 定理：⟨p,q⟩ = Σ p(xₖ)q(xₖ) ⇒ G = VᵀV
      if !g.equals(v.transpose().times(v)) {
        ok = false
      }
      // 定理：rank(VᵀV) = rank(V) = min(m, dim)（節點互異）
      let want_rank = if m < dim { m } else { dim }
      if mrank(g) != want_rank {
        ok = false
      }
      // 定理：正定 ⟺ 節點數 ≥ 維度
      let pd = is_positive_definite(g)
      if pd != (m >= dim) {
        ok = false
      }
      if pd {
        pdcnt = pdcnt + 1
      } else {
        degen = degen + 1
        if !Q::is_zero(mdet(g)) {
          ok = false
        }
      }
      n = n + 1
    }
  }
  mk_check(
    "E-08 離散點值內積 Gram = VᵀV",
    ok,
    n,
    "維度 2–5 × 節點數 dim−2…dim+2 共 " +
    n.to_string() +
    " 組：G = VᵀV 逐例成立；rank G = min(m, dim)；正定 " +
    pdcnt.to_string() +
    " 組、退化 " +
    degen.to_string() +
    " 組，且「正定 ⟺ 節點數 ≥ 維度」無一例外",
  )
}

///|
/// E-09 Sym ⊕ Skew = M_n（正交直和分解，Frobenius 內積）。
pub fn ob_e09() -> Check {
  let rng = ob_rng()
  let n = 4
  let full : IPSpace[Mat[Q], Q] = matrix_space(n, n)
  let sym : IPSpace[Mat[Q], Q] = sym_matrix_space(n)
  let skew : IPSpace[Mat[Q], Q] = skew_matrix_space(n)
  let mut ok = sym.vs.dim + skew.vs.dim == full.vs.dim
  if sym.vs.dim != n * (n + 1) / 2 || skew.vs.dim != n * (n - 1) / 2 {
    ok = false
  }
  for _t in 0..<10 {
    let a = (full.vs.sample)(rng)
    let half = Q::frac(1, 2)
    let ssym = a.plus(a.transpose()).scale(half)
    let sskw = a.minus(a.transpose()).scale(half)
    if !ssym.plus(sskw).equals(a) {
      ok = false
    }
    if !is_symmetric(ssym) || !is_skew(sskw) {
      ok = false
    }
    // 正交性 ⟨S, K⟩_F = 0
    if !(full.inner)(ssym, sskw).is_zero() {
      ok = false
    }
  }
  mk_check(
    "E-09 M_n = Sym_n ⊥ Skew_n", ok, 10, "維數 n(n+1)/2 + n(n−1)/2 = n²，且兩子空間正交",
  )
}

///|
/// E-10 對角矩陣空間 ≅ ℚⁿ（等距同構），且為 Sym 之子空間。
pub fn ob_e10() -> Check {
  let rng = ob_rng()
  let n = 5
  let dsp : IPSpace[Mat[Q], Q] = diag_matrix_space(n)
  let euc : IPSpace[Array[Q], Q] = euclidean_space(n)
  let mut ok = dsp.vs.dim == n
  for _t in 0..<10 {
    let a = (dsp.vs.sample)(rng)
    let b = (dsp.vs.sample)(rng)
    // 等距：⟨A,B⟩_F = ⟨diag A, diag B⟩
    let ca = vcoord(dsp.vs, a)
    let cb = vcoord(dsp.vs, b)
    if !(dsp.inner)(a, b).eq((euc.inner)(ca, cb)) {
      ok = false
    }
    // 對角矩陣交換
    if !a.times(b).equals(b.times(a)) {
      ok = false
    }
    if !is_symmetric(a) {
      ok = false
    }
  }
  mk_check(
    "E-10 Diag_n ≅ 𝔽ⁿ（等距同構）", ok, 10, "⟨A,B⟩_F = Σ aᵢbᵢ；對角陣交換",
  )
}

///|
/// E-11 Hermitian 空間：dim_ℝ Herm_n = n²，⟨A,B⟩ = Re tr(AB*) 為實內積，
/// 且 M_n(ℂ) = Herm_n ⊕ i·Herm_n。
pub fn ob_e11() -> Check {
  let rng = ob_rng()
  let n = 3
  let hsp : IPSpace[Mat[Cpx[Q]], Q] = herm_matrix_space(n)
  let mut ok = hsp.vs.dim == n * n
  for _t in 0..<10 {
    let a = (hsp.vs.sample)(rng)
    let b = (hsp.vs.sample)(rng)
    if !is_hermitian(a) || !is_hermitian(b) {
      ok = false
    }
    // 內積為實且等於 Re tr(AB*)
    let tr = a.times(b.adjointm()).trace()
    if !(hsp.inner)(a, b).eq(tr.cre) || !tr.cim.is_zero() {
      ok = false
    }
    // A Hermitian ⇒ iA 反 Hermitian；任意 M = H₁ + iH₂
    let m : Mat[Cpx[Q]] = Mat::build(n, n, (_i, _j) => Cpx::mk(qr(rng), qr(rng)))
    let half : Cpx[Q] = Cpx::mk(Q::frac(1, 2), Q::zero())
    let h1 = m.plus(m.adjointm()).scale(half)
    let ih : Cpx[Q] = Cpx::mk(Q::zero(), Q::frac(-1, 2))
    let h2 = m.minus(m.adjointm()).scale(ih)
    if !is_hermitian(h1) || !is_hermitian(h2) {
      ok = false
    }
    let iu : Cpx[Q] = Cpx::imag_unit()
    if !h1.plus(h2.scale(iu)).equals(m) {
      ok = false
    }
  }
  mk_check(
    "E-11 Herm_n(ℂ) 為實內積空間", ok, 10, "dim_ℝ = n²；⟨A,B⟩=Re tr(AB*)；M = H₁+iH₂",
  )
}

///|
/// E-12 sl_n：跡零空間 dim = n²−1，為 I 之正交補。
pub fn ob_e12() -> Check {
  let rng = ob_rng()
  let n = 3
  let sl : IPSpace[Mat[Q], Q] = traceless_space(n)
  let full : IPSpace[Mat[Q], Q] = matrix_space(n, n)
  let mut ok = sl.vs.dim == n * n - 1
  let idm : Mat[Q] = Mat::ident(n)
  for _t in 0..<10 {
    let a = (sl.vs.sample)(rng)
    if !a.trace().is_zero() {
      ok = false
    }
    // ⟨A, I⟩_F = tr A = 0 ⇒ sl_n = I^⊥
    if !(full.inner)(a, idm).is_zero() {
      ok = false
    }
    // 李括號封閉：[A,B] ∈ sl_n
    let b = (sl.vs.sample)(rng)
    let br = a.times(b).minus(b.times(a))
    if !br.trace().is_zero() {
      ok = false
    }
  }
  mk_check(
    "E-12 sl_n = I^⊥（跡零空間）", ok, 10, "dim = n²−1；[A,B] 封閉",
  )
}

///|
/// E-13 函數空間：δ 基底正交、權重即範數、求值為 Riesz 泛函。
pub fn ob_e13() -> Check {
  let rng = ob_rng()
  let w : Array[Q] = [Q::of_int(2), Q::frac(1, 3), Q::of_int(5), Q::one()]
  let s : IPSpace[Array[Q], Q] = function_space(["a", "b", "c", "d"], w)
  let mut ok = s.vs.dim == 4
  for i in 0..<4 {
    for j in 0..<4 {
      let v = (s.inner)(s.vs.basis[i], s.vs.basis[j])
      let want = if i == j { w[i] } else { Q::zero() }
      if !v.eq(want) {
        ok = false
      }
    }
  }
  // 求值泛函 ev_k(f) = f(k) 之 Riesz 代表 = δ_k / w_k
  for _t in 0..<10 {
    let f = (s.vs.sample)(rng)
    for k in 0..<4 {
      let rep = arr_scale(Q::inv(w[k]).unwrap_or(Q::zero()), s.vs.basis[k])
      if !(s.inner)(f, rep).eq(f[k]) {
        ok = false
      }
    }
  }
  mk_check(
    "E-13 加權函數空間 ℚ^S", ok, 10, "⟨δᵢ,δⱼ⟩=wᵢδᵢⱼ；ev_k 之 Riesz 代表 = δ_k/w_k",
  )
}

///|
/// E-14 列空間 col(A)：投影矩陣 A(AᵀA)⁻¹Aᵀ 與抽象投影一致。
pub fn ob_e14() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<10 {
    let a = qmat(rng, 5, 3)
    if mrank(a) != 3 {
      continue
    }
    let amb : IPSpace[Array[Q], Q] = euclidean_space(5)
    let cols : Array[Array[Q]] = Array::makei(3, j => a.col(j))
    let p1 = projection_matrix(amb, cols)
    let ata = a.transpose().times(a)
    let p2 = match minv(ata) {
      Some(x) => a.times(x).times(a.transpose())
      None => Mat::zeros(5, 5)
    }
    if !p1.equals(p2) {
      ok = false
    }
    // col(A) ⊥ ker(Aᵀ)
    for u in mnullspace(a.transpose()) {
      for j in 0..<3 {
        if !arr_dot(u, a.col(j)).is_zero() {
          ok = false
        }
      }
    }
  }
  mk_check(
    "E-14 列空間投影 P = A(AᵀA)⁻¹Aᵀ", ok, 10, "與抽象 Gram 投影逐項相等",
  )
}

///|
/// E-15 多變量多項式：求值為環同態 (fg)(ξ) = f(ξ)g(ξ)，次數加法。
pub fn ob_e15() -> Check {
  let rng = ob_rng()
  let m = 3
  let s : IPSpace[MPoly[Q], Q] = mpoly_space(m, 2, true)
  let mut ok = true
  for _t in 0..<10 {
    let f = (s.vs.sample)(rng)
    let g = (s.vs.sample)(rng)
    let x : Array[Q] = Array::makei(m, _ => qr(rng))
    let fg = f.mpmul(g)
    if !fg.mpeval(x).eq(f.mpeval(x).mul(g.mpeval(x))) {
      ok = false
    }
    if !f.mpadd(g).mpeval(x).eq(f.mpeval(x).add(g.mpeval(x))) {
      ok = false
    }
    if f.terms.length() > 0 && g.terms.length() > 0 && fg.terms.length() > 0 {
      if fg.mpdeg() > f.mpdeg() + g.mpdeg() {
        ok = false
      }
    }
  }
  mk_check(
    "E-10 多變量多項式求值同態", ok, 10, "(f+g)(ξ)=f+g，(fg)(ξ)=f·g，deg(fg) ≤ deg f+deg g",
  )
}

///|
/// E-16 Bombieri 內積之么正不變性：⟨f∘U, g∘U⟩ = ⟨f,g⟩（U 正交）。
pub fn ob_e16() -> Check {
  let rng = ob_rng()
  let m = 2
  let d = 2
  let s : IPSpace[MPoly[Q], Q] = mpoly_space(m, d, true)
  let mut ok = true
  for _t in 0..<10 {
    let u = rational_orthogonal(rng, m)
    let f = (s.vs.sample)(rng)
    let g = (s.vs.sample)(rng)
    let fu = mpoly_subst(f, u)
    let gu = mpoly_subst(g, u)
    if !(s.inner)(fu, gu).eq((s.inner)(f, g)) {
      ok = false
    }
  }
  mk_check(
    "E-16 Bombieri 內積之 O(m) 不變性", ok, 10, "⟨f∘U,g∘U⟩ = ⟨f,g⟩（U ∈ O(m)，精確 ℚ）",
  )
}

// ===========================================================================
//  F 群：空間組合子
// ===========================================================================

///|
/// F-01 直和：維數相加、內積分塊、兩分量正交、Gram 為分塊對角。
pub fn ob_f01() -> Check {
  let rng = ob_rng()
  let p : IPSpace[Poly[Q], Q] = poly_space_l2(2)
  let q : IPSpace[Mat[Q], Q] = sym_matrix_space(2)
  let ds = direct_sum(p, q)
  let mut ok = ds.vs.dim == p.vs.dim + q.vs.dim
  let g = gram_of_space(ds)
  let gp = gram_of_space(p)
  let gq = gram_of_space(q)
  for i in 0..<ds.vs.dim {
    for j in 0..<ds.vs.dim {
      let want = if i < p.vs.dim && j < p.vs.dim {
        gp.at(i, j)
      } else if i >= p.vs.dim && j >= p.vs.dim {
        gq.at(i - p.vs.dim, j - p.vs.dim)
      } else {
        Q::zero()
      }
      if !g.at(i, j).eq(want) {
        ok = false
      }
    }
  }
  for _t in 0..<10 {
    let a = (p.vs.sample)(rng)
    let b = (q.vs.sample)(rng)
    let c = (p.vs.sample)(rng)
    let d = (q.vs.sample)(rng)
    let lhs = (ds.inner)((a, b), (c, d))
    if !lhs.eq(Q::add((p.inner)(a, c), (q.inner)(b, d))) {
      ok = false
    }
    // V₁⊕0 ⊥ 0⊕V₂
    if !(ds.inner)((a, q.vs.zero), (p.vs.zero, d)).is_zero() {
      ok = false
    }
  }
  mk_check(
    "F-01 直和 P⊕Q", ok, 10, "dim 相加；Gram 分塊對角；分量互相正交",
  )
}

///|
/// F-02 張量積：Gram = G₁⊗G₂，⟨x₁⊗x₂, y₁⊗y₂⟩ = ⟨x₁,y₁⟩⟨x₂,y₂⟩，正定。
pub fn ob_f02() -> Check {
  let rng = ob_rng()
  let p : IPSpace[Poly[Q], Q] = poly_space_l2(2)
  let q : IPSpace[Array[Q], Q] = euclidean_space(2)
  let t = tensor_space(p, q)
  let mut ok = t.vs.dim == p.vs.dim * q.vs.dim
  if !gram_of_space(t).equals(mkron(gram_of_space(p), gram_of_space(q))) {
    ok = false
  }
  if !is_positive_definite(gram_of_space(t)) {
    ok = false
  }
  for _t in 0..<10 {
    let x1 = (p.vs.sample)(rng)
    let x2 = (q.vs.sample)(rng)
    let y1 = (p.vs.sample)(rng)
    let y2 = (q.vs.sample)(rng)
    let lhs = (t.inner)(tensor_pure(p, q, x1, x2), tensor_pure(p, q, y1, y2))
    if !lhs.eq(Q::mul((p.inner)(x1, y1), (q.inner)(x2, y2))) {
      ok = false
    }
    // 雙線性：(x+x')⊗y = x⊗y + x'⊗y
    let x3 = (p.vs.sample)(rng)
    let l = tensor_pure(p, q, vadd(p.vs, x1, x3), x2)
    let r = arr_add(tensor_pure(p, q, x1, x2), tensor_pure(p, q, x3, x2))
    if !arr_eq(l, r) {
      ok = false
    }
  }
  mk_check(
    "F-02 張量積 P⊗Q", ok, 10, "Gram = G₁⊗G₂（正定）；純張量內積乘性；雙線性",
  )
}

///|
/// F-03 張量算子與部分跡：(A⊗B)(x⊗y) = Ax⊗By；tr₂(A⊗B) = tr(B)·A。
pub fn ob_f03() -> Check {
  let rng = ob_rng()
  let d1 = 2
  let d2 = 3
  let mut ok = true
  for _t in 0..<10 {
    let a = qmat(rng, d1, d1)
    let b = qmat(rng, d2, d2)
    let x : Array[Q] = Array::makei(d1, _ => qr(rng))
    let y : Array[Q] = Array::makei(d2, _ => qr(rng))
    let xy : Array[Q] = Array::makei(d1 * d2, k => Q::mul(x[k / d2], y[k % d2]))
    let lhs = tensor_operator(a, b).apply(xy)
    let ax = a.apply(x)
    let by = b.apply(y)
    let rhs : Array[Q] = Array::makei(d1 * d2, k => {
      Q::mul(ax[k / d2], by[k % d2])
    })
    if !arr_eq(lhs, rhs) {
      ok = false
    }
    // 部分跡
    if !partial_trace2(mkron(a, b), d1, d2).equals(a.scale(b.trace())) {
      ok = false
    }
    // tr(tr₂(M)) = tr(M)
    let m = qmat(rng, d1 * d2, d1 * d2)
    if !partial_trace2(m, d1, d2).trace().eq(m.trace()) {
      ok = false
    }
  }
  mk_check(
    "F-03 張量算子與部分跡", ok, 10, "(A⊗B)(x⊗y)=Ax⊗By；tr₂(A⊗B)=tr(B)A；tr∘tr₂=tr",
  )
}

///|
/// F-04 對偶空間：Gram = (G⁻¹)ᵀ、對偶基底 b^i(bⱼ) = δ、dual(dual) 還原 G。
pub fn ob_f04() -> Check {
  let p : IPSpace[Poly[Q], Q] = poly_space_l2(3)
  let dp = dual_space(p)
  let g = gram_of_space(p)
  let h = gram_of_space(dp)
  let mut ok = dp.vs.dim == p.vs.dim
  match minv(g) {
    None => ok = false
    Some(gi) => if !h.equals(gi.transpose()) { ok = false }
  }
  // 對偶基底求值
  for i in 0..<p.vs.dim {
    for j in 0..<p.vs.dim {
      let want = if i == j { Q::one() } else { Q::zero() }
      if !dual_eval(p, vcoord(dp.vs, dp.vs.basis[i]), p.vs.basis[j]).eq(want) {
        ok = false
      }
    }
  }
  // 雙對偶：Gram(V**) = G
  let ddp = dual_space(dp)
  if !gram_of_space(ddp).equals(g) {
    ok = false
  }
  // 自然嵌入為等距：⟨v,w⟩_V = ⟨ev_v, ev_w⟩_{V**}
  let rng = ob_rng()
  for _t in 0..<10 {
    let v = (p.vs.sample)(rng)
    let w = (p.vs.sample)(rng)
    let ev = double_dual_embed(p, v)
    let ew = double_dual_embed(p, w)
    if !(ddp.inner)(ev, ew).eq((p.inner)(v, w)) {
      ok = false
    }
  }
  mk_check(
    "F-04 對偶空間與雙對偶自然同構", ok, 10, "Gram(V*)=(G⁻¹)ᵀ；b^i(bⱼ)=δ；V ≅ V** 等距",
  )
}

///|
/// F-05 Hom 空間：dim = dim V·dim W；matrix_of_map 與座標作用相容；
/// 標準正交基時內積退化為 Frobenius tr(B*A)。
pub fn ob_f05() -> Check {
  let rng = ob_rng()
  let p : IPSpace[Array[Q], Q] = euclidean_space(3)
  let q : IPSpace[Array[Q], Q] = euclidean_space(2)
  let hm = hom_space(p, q)
  let mut ok = hm.vs.dim == 6
  for _t in 0..<10 {
    let a = qmat(rng, 2, 3)
    let t : (Array[Q]) -> Array[Q] = v => a.apply(v)
    let rec = matrix_of_map(p, q, t)
    if !rec.equals(a) {
      ok = false
    }
    // Hom 內積 = Frobenius（標準正交基）
    let b = qmat(rng, 2, 3)
    let va = mvec(a)
    let vb = mvec(b)
    if !(hm.inner)(va, vb).eq(b.adjointm().times(a).trace()) {
      ok = false
    }
  }
  mk_check(
    "F-05 Hom(P,Q) ≅ Q⊗P*", ok, 10, "dim 相乘；[T] 重建；⟨A,B⟩ = tr(B*A)",
  )
}

///|
/// F-06 實化：dim 加倍、‖x‖ 不變、J² = −I、J 為等距、Im⟨x,y⟩ = ⟨x,Jy⟩_ℝ。
pub fn ob_f06() -> Check {
  let rng = ob_rng()
  let c : IPSpace[Array[Cpx[Q]], Cpx[Q]] = unitary_space(3)
  let r = realify(c)
  let j = complex_structure_matrix(c)
  let mut ok = r.vs.dim == 2 * c.vs.dim
  if !j.times(j).equals(Mat::ident(6).negm()) {
    ok = false
  }
  if !is_isometry(r, j) {
    ok = false
  }
  let iu : Cpx[Q] = Cpx::imag_unit()
  for _t in 0..<10 {
    let x = (c.vs.sample)(rng)
    let y = (c.vs.sample)(rng)
    // 範數不變
    if !(r.inner)(x, x).eq((c.inner)(x, x).cre) {
      ok = false
    }
    // ⟨x,y⟩_ℝ = Re⟨x,y⟩_ℂ
    if !(r.inner)(x, y).eq((c.inner)(x, y).cre) {
      ok = false
    }
    // 辛形式 ω(x,y) = Im⟨x,y⟩_ℂ = ⟨x, iy⟩_ℝ
    let iy = (c.vs.smul)(iu, y)
    if !(c.inner)(x, y).cim.eq((r.inner)(x, iy)) {
      ok = false
    }
    // J 於座標上即「乘以 i」
    let cx = vcoord(r.vs, x)
    let jx = j.apply(cx)
    if !arr_eq(jx, vcoord(r.vs, (c.vs.smul)(iu, x))) {
      ok = false
    }
  }
  mk_check(
    "F-06 實化與複結構 J", ok, 10, "dim ×2；J²=−I；J 等距；Im⟨x,y⟩=⟨x,Jy⟩_ℝ",
  )
}

///|
/// F-07 內積扭曲：A 正定 ⇒ ⟨,⟩_A 為內積；且 Gram 變為 A。
pub fn ob_f07() -> Check {
  let rng = ob_rng()
  let p : IPSpace[Array[Q], Q] = euclidean_space(3)
  // 造正定有理 A = BᵀB + I
  let b = qmat(rng, 3, 3)
  let a = b.transpose().times(b).plus(Mat::ident(3))
  let tw = retwist(p, a)
  let mut ok = is_positive_definite(a)
  if !gram_of_space(tw).equals(a) {
    ok = false
  }
  let all : Array[Check] = check_inner_axioms(tw, ob_rng(), 3)
  let r = check_all("twisted", all)
  if !r.ok {
    ok = false
  }
  // 反例檢出能力 (1)：不定號 A ⇒ I4（非負性）必被否決
  let bad1 : Mat[Q] = Mat::diagm([Q::one(), Q::of_int(-100), Q::one()])
  let rb1 = check_all(
    "indefinite",
    check_inner_axioms(retwist(p, bad1), ob_rng(), 3),
  )
  if rb1.ok {
    ok = false
  }
  // 反例檢出能力 (2)：非對稱 A ⇒ I3（Hermitian 對稱）必被否決
  let bad2 : Mat[Q] = Mat::of_rows([
    [Q::one(), Q::of_int(2), Q::zero()],
    [Q::zero(), Q::one(), Q::of_int(3)],
    [Q::zero(), Q::zero(), Q::one()],
  ])
  let rb2 = check_all(
    "asymmetric",
    check_inner_axioms(retwist(p, bad2), ob_rng(), 3),
  )
  if rb2.ok {
    ok = false
  }
  mk_check(
    "F-07 內積扭曲 ⟨x,y⟩_A",
    ok,
    all.length() + 1 + 2,
    "A 正定 ⇒ I1–I7 共 7 條通過，加 Gram(扭曲空間) = A 一條，加「不定號」「非對稱」兩組反例對照，合 10 例（每條公理 3 次抽樣）",
  )
}

///|
/// F-08 子空間構造：維數 = 生成集之秩；限制內積仍為內積；座標往返一致。
pub fn ob_f08() -> Check {
  let rng = ob_rng()
  let amb : IPSpace[Poly[Q], Q] = poly_space_l2(4)
  let mut ok = true
  for _t in 0..<10 {
    let gens = samples(amb, rng, 3)
    let extra = vadd(amb.vs, gens[0], gens[1]) // 刻意相依
    let all : Array[Poly[Q]] = [gens[0], gens[1], gens[2], extra]
    let sub = subspace_of("測試子空間", amb, all)
    let m : Mat[Q] = Mat::of_cols(all.map(x => vcoord(amb.vs, x)))
    if sub.vs.dim != mrank(m) {
      ok = false
    }
    for _k in 0..<4 {
      let v = (sub.vs.sample)(rng)
      let c = vcoord(sub.vs, v)
      if !(sub.vs.veq)((sub.vs.expand)(c), v) {
        ok = false
      }
    }
    if !is_positive_definite(gram_of_space(sub)) {
      ok = false
    }
  }
  mk_check(
    "F-08 子空間構造（含相依生成集）", ok, 10, "dim = rank；座標往返 id；限制 Gram 正定",
  )
}

///|
/// F-09 組合爆炸示範：對 6 個組合空間一次跑完整公理 + 投影 + CS。
pub fn ob_f09() -> Check {
  let rng = ob_rng()
  let p : IPSpace[Poly[Q], Q] = poly_space_l2(2)
  let q : IPSpace[Mat[Q], Q] = sym_matrix_space(2)
  let e : IPSpace[Array[Q], Q] = euclidean_space(2)
  let combos : Array[IPSpace[Array[Q], Q]] = [
    tensor_space(p, q),
    tensor_space(q, e),
    dual_space(p),
    dual_space(tensor_space(p, e)),
    hom_space(p, q),
    tensor_space(dual_space(p), dual_space(e)),
    tensor_space(e, e),
    dual_space(q),
    hom_space(e, p),
    tensor_space(p, dual_space(q)),
  ]
  let res : Array[Check] = []
  for s in combos {
    let cs : Array[Check] = []
    for c in check_vector_space_axioms(s.vs, rng, 3) {
      cs.push(c)
    }
    for c in check_inner_axioms(s, rng, 3) {
      cs.push(c)
    }
    // 投影與 Cauchy–Schwarz 於該組合空間上亦成立
    let xs = samples(s, rng, 2)
    let x = (s.vs.sample)(rng)
    let r = vsub(s.vs, x, project_onto(s, xs, x))
    let mut orth = true
    for w in xs {
      if !Q::is_zero((s.inner)(r, w)) {
        orth = false
      }
    }
    cs.push(ok1("投影殘差正交", orth, s.vs.vname))
    cs.push(
      ok1(
        "Cauchy–Schwarz",
        Q::cmp(cauchy_schwarz_slack(s, x, xs[0]), Q::zero()) >= 0,
        s.vs.vname,
      ),
    )
    res.push(check_all(s.vs.vname, cs))
  }
  let r = check_all("F-09", res)
  mk_check(
    "F-09 組合空間之公理與演算法通行性",
    r.ok,
    res.length(),
    "10 個組合空間，每個走完 V1–V11 + I1–I7 共 18 條公理（每條 3 次抽樣）再加投影殘差正交與 Cauchy–Schwarz；實測單位 = 組合空間",
  )
}

// ===========================================================================
//  G 群：外代數與行列式幾何
// ===========================================================================

///|
/// G-01 楔積反交換律 α∧β = (−1)^{pq} β∧α，以及 v∧v = 0。
pub fn ob_g01() -> Check {
  let rng = ob_rng()
  let n = 4
  let mut ok = true
  let mut cnt = 0
  for p in 1..<3 {
    for q in 1..<3 {
      if p + q > n {
        continue
      }
      for _t in 0..<8 {
        if cnt >= 5 {
          continue
        }
        cnt = cnt + 1
        let da = binom(n, p)
        let db = binom(n, q)
        let a : Array[Q] = Array::makei(da, _ => qr(rng))
        let b : Array[Q] = Array::makei(db, _ => qr(rng))
        let ab = wedge(n, p, q, a, b)
        let ba = wedge(n, q, p, b, a)
        let sgn = if p * q % 2 == 0 { ba } else { arr_neg(ba) }
        if !arr_eq(ab, sgn) {
          ok = false
        }
      }
    }
  }
  // v ∧ v = 0
  for _t in 0..<5 {
    cnt = cnt + 1
    let v : Array[Q] = Array::makei(n, _ => qr(rng))
    let vv = wedge(n, 1, 1, v, v)
    for x in vv {
      if !x.is_zero() {
        ok = false
      }
    }
  }
  mk_check(
    "G-01 楔積反交換律", ok, cnt, "5 例 α∧β = (−1)^{pq}β∧α（跨 (p,q) 雙度數）＋ 5 例 v∧v = 0",
  )
}

///|
/// G-02 結合律 (α∧β)∧γ = α∧(β∧γ)（於全外代數中驗證）。
pub fn ob_g02() -> Check {
  let rng = ob_rng()
  let n = 4
  let d = 1 << n
  let mut ok = true
  for _t in 0..<10 {
    let a : Array[Q] = Array::makei(d, _ => qr(rng))
    let b : Array[Q] = Array::makei(d, _ => qr(rng))
    let c : Array[Q] = Array::makei(d, _ => qr(rng))
    let l = wedge_full(n, wedge_full(n, a, b), c)
    let r = wedge_full(n, a, wedge_full(n, b, c))
    if !arr_eq(l, r) {
      ok = false
    }
    // 分配律
    let l2 = wedge_full(n, a, arr_add(b, c))
    let r2 = arr_add(wedge_full(n, a, b), wedge_full(n, a, c))
    if !arr_eq(l2, r2) {
      ok = false
    }
  }
  mk_check(
    "G-02 外代數結合律與分配律", ok, 10, "Λ(𝔽ⁿ) 為結合分次代數（dim = 2ⁿ）",
  )
}

///|
/// G-03 Gram 行列式定理：⟨v₁∧…∧v_k, w₁∧…∧w_k⟩ = det(⟨vᵢ,wⱼ⟩)。
pub fn ob_g03() -> Check {
  let rng = ob_rng()
  let n = 4
  let k = 2
  let s : IPSpace[Array[Q], Q] = exterior_power_space(n, k)
  let euc : IPSpace[Array[Q], Q] = euclidean_space(n)
  let mut ok = true
  for _t in 0..<10 {
    let vs : Array[Array[Q]] = Array::makei(k, _ => {
      Array::makei(n, _ => qr(rng))
    })
    let ws : Array[Array[Q]] = Array::makei(k, _ => {
      Array::makei(n, _ => qr(rng))
    })
    let a = wedge_vectors(n, vs)
    let b = wedge_vectors(n, ws)
    let lhs = (s.inner)(a, b)
    let g : Mat[Q] = Mat::build(k, k, (i, j) => (euc.inner)(vs[i], ws[j]))
    if !lhs.eq(mdet(g)) {
      ok = false
    }
  }
  mk_check(
    "G-03 Gram 行列式定理（Λᵏ 內積）", ok, 10, "⟨v₁∧…∧v_k, w₁∧…∧w_k⟩ = det⟨vᵢ,wⱼ⟩",
  )
}

///|
/// G-04 v₁∧…∧v_n = det(V)·e_{1…n}；相依 ⇒ 0。
pub fn ob_g04() -> Check {
  let rng = ob_rng()
  let n = 4
  let mut ok = true
  for _t in 0..<10 {
    let vs : Array[Array[Q]] = Array::makei(n, _ => {
      Array::makei(n, _ => qr(rng))
    })
    let w = wedge_vectors(n, vs)
    if w.length() != 1 {
      ok = false
    } else {
      let v : Mat[Q] = Mat::of_cols(vs)
      if !w[0].eq(mdet(v)) {
        ok = false
      }
    }
    // 相依 ⇒ 0
    let dep : Array[Array[Q]] = Array::makei(n, i => {
      if i == n - 1 {
        vs[0]
      } else {
        vs[i]
      }
    })
    let wd = wedge_vectors(n, dep)
    if !wd[0].is_zero() {
      ok = false
    }
  }
  mk_check(
    "G-04 行列式之外代數定義", ok, 10, "v₁∧…∧v_n = det(V)e_{1…n}；相依 ⇒ 0",
  )
}

///|
/// G-05 Hodge 星：⋆⋆ = (−1)^{k(n−k)}·id。
pub fn ob_g05() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut cnt = 0
  for n in 2..<6 {
    for k in 0..<(n + 1) {
      for _t in 0..<5 {
        if cnt >= 10 {
          continue
        }
        cnt = cnt + 1
        let d = binom(n, k)
        let a : Array[Q] = Array::makei(d, _ => qr(rng))
        let ss = hodge_star(n, n - k, hodge_star(n, k, a))
        let want = if k * (n - k) % 2 == 0 { a } else { arr_neg(a) }
        if !arr_eq(ss, want) {
          ok = false
        }
      }
    }
  }
  mk_check("G-05 Hodge 星對合律", ok, cnt, "⋆⋆ = (−1)^{k(n−k)}·id")
}

///|
/// G-06 α ∧ ⋆β = ⟨α,β⟩·e_{1…n}。
pub fn ob_g06() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut cnt = 0
  for n in 2..<5 {
    for k in 1..<n {
      let s : IPSpace[Array[Q], Q] = exterior_power_space(n, k)
      for _t in 0..<6 {
        if cnt >= 10 {
          continue
        }
        cnt = cnt + 1
        let d = binom(n, k)
        let a : Array[Q] = Array::makei(d, _ => qr(rng))
        let b : Array[Q] = Array::makei(d, _ => qr(rng))
        let w = wedge(n, k, n - k, a, hodge_star(n, k, b))
        if w.length() != 1 || !w[0].eq((s.inner)(a, b)) {
          ok = false
        }
      }
    }
  }
  mk_check(
    "G-06 α∧⋆β = ⟨α,β⟩vol", ok, cnt, "Hodge 星與內積之相容性",
  )
}

///|
/// G-07 三維叉積：Lagrange 恆等式、反交換、正交性、Jacobi 恆等式。
pub fn ob_g07() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<10 {
    let a : Array[Q] = Array::makei(3, _ => qr(rng))
    let b : Array[Q] = Array::makei(3, _ => qr(rng))
    let c : Array[Q] = Array::makei(3, _ => qr(rng))
    let ab = cross3(a, b)
    // 正交
    if !arr_dot(ab, a).is_zero() || !arr_dot(ab, b).is_zero() {
      ok = false
    }
    // 反交換
    if !arr_eq(ab, arr_neg(cross3(b, a))) {
      ok = false
    }
    // Lagrange：‖a×b‖² = ‖a‖²‖b‖² − ⟨a,b⟩²
    let lhs = arr_dot(ab, ab)
    let rhs = Q::sub(
      Q::mul(arr_dot(a, a), arr_dot(b, b)),
      Q::mul(arr_dot(a, b), arr_dot(a, b)),
    )
    if !lhs.eq(rhs) {
      ok = false
    }
    // Jacobi
    let j = arr_add(
      arr_add(cross3(a, cross3(b, c)), cross3(b, cross3(c, a))),
      cross3(c, cross3(a, b)),
    )
    for x in j {
      if !x.is_zero() {
        ok = false
      }
    }
    // 三重積 = det
    let tri = arr_dot(a, cross3(b, c))
    if !tri.eq(mdet(Mat::of_cols([a, b, c]))) {
      ok = false
    }
  }
  mk_check(
    "G-07 三維叉積（Lagrange/Jacobi/三重積）", ok, 10, "⋆(a∧b) 之全部古典恆等式",
  )
}

///|
/// G-08 廣義叉積：⟨x, vᵢ⟩ = 0，且 ‖x‖² = det Gram(v₁..v_{n−1})。
pub fn ob_g08() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut cnt = 0
  for n in 2..<6 {
    let euc : IPSpace[Array[Q], Q] = euclidean_space(n)
    for _t in 0..<6 {
      if cnt >= 10 {
        continue
      }
      cnt = cnt + 1
      let vs : Array[Array[Q]] = Array::makei(n - 1, _ => {
        Array::makei(n, _ => qr(rng))
      })
      let x = generalized_cross(n, vs)
      for v in vs {
        if !arr_dot(x, v).is_zero() {
          ok = false
        }
      }
      let g = gram_det(euc, vs)
      if !arr_dot(x, x).eq(g) {
        ok = false
      }
    }
  }
  mk_check(
    "G-08 廣義叉積", ok, cnt, "⟨x,vᵢ⟩=0；‖x‖² = det Gram = (n−1)體積²",
  )
}

///|
/// G-09 Plücker 座標 = k×k 子式；Λᵏ 之維數 = C(n,k)；可分解性。
pub fn ob_g09() -> Check {
  let rng = ob_rng()
  let n = 5
  let k = 2
  let lam : IPSpace[Array[Q], Q] = exterior_power_space(n, k)
  let mut ok = lam.vs.dim == binom(n, k)
  let ss = subsets_k(n, k)
  for _t in 0..<10 {
    let vs : Array[Array[Q]] = Array::makei(k, _ => {
      Array::makei(n, _ => qr(rng))
    })
    let w : Array[Q] = wedge_vectors(n, vs)
    for t in 0..<ss.length() {
      let rows = ss[t]
      let sub : Mat[Q] = Mat::build(k, k, (i, j) => vs[j][rows[i]])
      if !w[t].eq(mdet(sub)) {
        ok = false
      }
    }
    // 可分解 2-向量滿足 Plücker 關係 p01p23 − p02p13 + p03p12 = 0（n ≥ 4）
    let idx = (i : Int, j : Int) => {
      let mut r = -1
      for t in 0..<ss.length() {
        if ss[t][0] == i && ss[t][1] == j {
          r = t
        }
      }
      r
    }
    let pl = Q::add(
      Q::sub(
        Q::mul(w[idx(0, 1)], w[idx(2, 3)]),
        Q::mul(w[idx(0, 2)], w[idx(1, 3)]),
      ),
      Q::mul(w[idx(0, 3)], w[idx(1, 2)]),
    )
    if !pl.is_zero() {
      ok = false
    }
  }
  mk_check(
    "G-09 Plücker 座標與關係式", ok, 10, "(v₁∧v₂)_I = det V[I,:]；p₀₁p₂₃−p₀₂p₁₃+p₀₃p₁₂=0",
  )
}

///|
/// 小工具：整數最大值
fn maxi(a : Int, b : Int) -> Int {
  if a > b {
    a
  } else {
    b
  }
}

// ============================================================================
//  檔案 13：ipalgo.mbt — 抽象內積空間上之演算法（對任何 IPSpace 泛型化）
//  本檔之每個函數都只用內積公理 I1–I5 與向量空間公理 V1–V8，
//  因此對「歐氏空間／函數空間／矩陣空間／多項式空間／四元數空間／張量空間／
//  外代數／對偶空間／直和」等一切已建構之空間同樣適用 —— 這就是組合爆炸之來源：
//  (空間數 × 演算法數) 組對皆可運行。
// ============================================================================

// ---------------------------------------------------------------------------
// 【演算法 061】Gram–Schmidt 正交化（經典版，精確；不作正規化）
//   u₁ = x₁；u_k = x_k − Σ_{j<k} (⟨x_k,u_j⟩/⟨u_j,u_j⟩) u_j
// 命題 061：(i) span{u₁..u_k} = span{x₁..x_k} ∀k；(ii) uᵢ ⊥ uⱼ (i≠j)；
//   (iii) x_k = u_k + Σ_{j<k} r_{jk} u_j（上三角變換，即 QR 分解之抽象形式）。
// 證明（對 k 歸納）：u_k 之定義使 ⟨u_k,u_j⟩ = ⟨x_k,u_j⟩ − ⟨x_k,u_j⟩ = 0 (j<k)；
//   span 相等由可逆上三角變換得證（對角元為 1）。∎
// 退化處理：若 u_k = 0（x_k 線性相依）則跳過並記錄。
// ---------------------------------------------------------------------------

///|
/// Gram–Schmidt 之輸出
pub struct GSOut[V, F] {
  /// 正交向量組（不含零向量）
  ortho : Array[V]
  /// 係數矩陣 R（x_j = Σ_i R_{ij} u_i）
  rmat : Mat[F]
  /// 被判定為相依之索引
  dependent : Array[Int]
}

///|
/// 古典 Gram–Schmidt 正交化（精確軌道下無捨入，數值軌道見 modified 版）。
pub fn[V, F : Scalar] gram_schmidt(
  s : IPSpace[V, F],
  xs : Array[V],
) -> GSOut[V, F] {
  let vsp = s.vs
  let m = xs.length()
  let ortho : Array[V] = []
  let dependent : Array[Int] = []
  let rmat : Mat[F] = Mat::zeros(m, m)
  for k in 0..<m {
    let mut u = xs[k]
    for j in 0..<ortho.length() {
      let uj = ortho[j]
      let num = (s.inner)(xs[k], uj)
      let den = (s.inner)(uj, uj)
      match F::s_inv(den) {
        None => ()
        Some(di) => {
          let c = F::s_mul(num, di)
          rmat.put(j, k, c)
          u = vsub(vsp, u, (vsp.smul)(c, uj))
        }
      }
    }
    if F::s_is_zero((s.inner)(u, u)) {
      dependent.push(k)
    } else {
      rmat.put(ortho.length(), k, F::s_one())
      ortho.push(u)
    }
  }
  { ortho, rmat, dependent, }
}

// ---------------------------------------------------------------------------
// 【演算法 062】改良 Gram–Schmidt（MGS，數值穩定版）
//   對每個新向量「逐步」扣除已算出之分量（而非一次用原始 x_k）。
// 命題 062：於精確算術下 MGS 與 CGS 輸出相同；於浮點下 MGS 之正交性損失
//   為 O(ε·κ(A))，而 CGS 為 O(ε·κ(A)²)（Björck 1967）。
//   本實作以 Hilbert 矩陣型病態例子展示兩者差距（見 obligations）。
// ---------------------------------------------------------------------------

///|
/// 修改版 Gram–Schmidt：每步即投影，數值穩定性優於古典版。
pub fn[V, F : Scalar] modified_gram_schmidt(
  s : IPSpace[V, F],
  xs : Array[V],
) -> GSOut[V, F] {
  let vsp = s.vs
  let m = xs.length()
  let work : Array[V] = Array::makei(m, i => xs[i])
  let ortho : Array[V] = []
  let dependent : Array[Int] = []
  let rmat : Mat[F] = Mat::zeros(m, m)
  for k in 0..<m {
    let u = work[k]
    if F::s_is_zero((s.inner)(u, u)) {
      dependent.push(k)
      continue
    }
    let idx = ortho.length()
    rmat.put(idx, k, F::s_one())
    ortho.push(u)
    let den = (s.inner)(u, u)
    match F::s_inv(den) {
      None => ()
      Some(di) =>
        for j in (k + 1)..<m {
          let c = F::s_mul((s.inner)(work[j], u), di)
          rmat.put(idx, j, c)
          work[j] = vsub(vsp, work[j], (vsp.smul)(c, u))
        }
    }
  }
  { ortho, rmat, dependent, }
}

// ---------------------------------------------------------------------------
// 【演算法 063】正規化為標準正交基（需要 √⟨u,u⟩ ∈ 𝔽）
// 命題 063：ℚ 上一般不可行（√2 ∉ ℚ）—— 此即「精確軌道只作正交化、
//   數值軌道才作正規化」之結構性理由（ℚ 非實閉體）。
// ---------------------------------------------------------------------------

///|
/// 正交歸一化：回一組標準正交基底（含退化秩處理）。
pub fn[V, F : Scalar] orthonormalize(
  s : IPSpace[V, F],
  xs : Array[V],
) -> Array[V]? {
  let g = gram_schmidt(s, xs)
  let out : Array[V] = []
  for u in g.ortho {
    let n2 = (s.inner)(u, u)
    match F::s_sqrt(n2) {
      None => return None
      Some(nrm) =>
        match F::s_inv(nrm) {
          None => return None
          Some(inv) => out.push((s.vs.smul)(inv, u))
        }
    }
  }
  Some(out)
}

// ---------------------------------------------------------------------------
// 【演算法 064】Gram 行列式與 k 維體積
// 定理 064：vol_k(v₁,…,v_k)² = det Gram(v₁,…,v_k)（Gram 行列式公式）。
//   證明：由定理 E2（外代數）⟨v₁∧…∧v_k, v₁∧…∧v_k⟩ = det(⟨vᵢ,vⱼ⟩)，
//   而左邊依定義即體積平方。∎
// 推論：det Gram ≥ 0；= 0 ⟺ 線性相依（Gram 判別法）。
// ---------------------------------------------------------------------------

///|
/// det Gram(v₁..v_k)
pub fn[V, F : Scalar] gram_det(s : IPSpace[V, F], xs : Array[V]) -> F {
  mdet(gram_of(s, xs))
}

///|
/// k 維體積（雙精度）
pub fn[V, F : Scalar] volume_k(s : IPSpace[V, F], xs : Array[V]) -> Double {
  sqrt_newton(F::s_to_double(gram_det(s, xs)))
}

///|
/// 線性獨立判定（Gram 判別法；精確軌道為真·判定）
pub fn[V, F : Scalar] linearly_independent(
  s : IPSpace[V, F],
  xs : Array[V],
) -> Bool {
  !F::s_is_zero(gram_det(s, xs))
}

// ---------------------------------------------------------------------------
// 【演算法 065】正交投影 P_W x（解正規方程 Gram·c = b）
// 定理 065（最佳逼近定理）：W ⊆ V 有限維子空間，則 ∀x ∃!w₀ ∈ W 使
//   ‖x − w₀‖ = min_{w∈W} ‖x − w‖，且其特徵為 x − w₀ ⊥ W。
// 證明：取 W 之基 {wᵢ}，令 w₀ = Σcⱼwⱼ，正交條件 ⟨x−w₀, wᵢ⟩ = 0 給出
//   Gram 系統 Σⱼ ⟨wⱼ,wᵢ⟩cⱼ = ⟨x,wᵢ⟩，Gram 可逆（基底線性獨立）⇒ 唯一解。
//   最小性：∀w ∈ W，‖x−w‖² = ‖x−w₀‖² + ‖w₀−w‖² ≥ ‖x−w₀‖²（畢氏）。∎
// ---------------------------------------------------------------------------

///|
/// 投影係數 c（使 P_W x = Σ cⱼ wⱼ）
pub fn[V, F : Scalar] projection_coeffs(
  s : IPSpace[V, F],
  basis : Array[V],
  x : V,
) -> Array[F] {
  let k = basis.length()
  if k == 0 {
    return []
  }
  let a : Mat[F] = Mat::build(k, k, (i, j) => (s.inner)(basis[j], basis[i]))
  let b : Array[F] = Array::makei(k, i => (s.inner)(x, basis[i]))
  let sol = msolve(a, b)
  if sol.solvable {
    sol.particular
  } else {
    arr_zeros(k)
  }
}

///|
/// 正交投影 P_W x
pub fn[V, F : Scalar] project_onto(
  s : IPSpace[V, F],
  basis : Array[V],
  x : V,
) -> V {
  let c = projection_coeffs(s, basis, x)
  vlincomb(s.vs, c, basis)
}

///|
/// 到子空間之距離 d(x, W) = ‖x − P_W x‖
pub fn[V, F : Scalar] distance_to_subspace(
  s : IPSpace[V, F],
  basis : Array[V],
  x : V,
) -> Double {
  ip_norm(s, vsub(s.vs, x, project_onto(s, basis, x)))
}

///|
/// 投影算子之矩陣（於空間基底座標下）
pub fn[V, F : Scalar] projection_matrix(
  s : IPSpace[V, F],
  basis : Array[V],
) -> Mat[F] {
  let n = s.vs.dim
  let cols : Array[Array[F]] = Array::makei(n, j => {
    (s.vs.coord)(project_onto(s, basis, s.vs.basis[j]))
  })
  Mat::build(n, n, (i, j) => cols[j][i])
}

// ---------------------------------------------------------------------------
// 【演算法 066】Riesz 表示定理
// 定理 066：V 有限維內積空間，∀φ ∈ V* ∃!v_φ ∈ V 使 φ(x) = ⟨x,v_φ⟩ ∀x；
//   且 ‖φ‖_{V*} = ‖v_φ‖_V，映射 φ ↦ v_φ 為共軛線性等距雙射。
// 證明：取標準正交基 {eᵢ}，令 v_φ = Σ ‾φ(eᵢ) eᵢ，直接驗證；
//   唯一性：若 ⟨x,v⟩ = ⟨x,w⟩ ∀x 則 ⟨x,v−w⟩ = 0 取 x = v−w 得 v = w（正定性）。∎
// 一般基底之公式（本實作）：‾v = G⁻¹c，其中 c_i = φ(bᵢ)，G_{ij} = ⟨bᵢ,bⱼ⟩。
// ---------------------------------------------------------------------------

///|
/// 由泛函之對偶座標 c（c_i = φ(bᵢ)）求 Riesz 代表向量
pub fn[V, F : Scalar] riesz_vector(s : IPSpace[V, F], c : Array[F]) -> V {
  let n = s.vs.dim
  let g = gram_of_space(s)
  let sol = msolve(g, c)
  let x = sol.particular
  // v = conj(G⁻¹ c)
  let v = Array::makei(n, i => F::s_conj(x[i]))
  (s.vs.expand)(v)
}

// ---------------------------------------------------------------------------
// 【演算法 067】伴隨算子 T* （⟨Tx, y⟩_W = ⟨x, T*y⟩_V）
// 定理 067：有限維時 T* 存在且唯一，矩陣公式 [T*] = G_V⁻¹ [T]* G_W。
// 證明：⟨Tx,y⟩_W = (Ax)ᵀ G_W ‾y = xᵀ (Aᵀ G_W) ‾y；
//   ⟨x,T*y⟩_V = xᵀ G_V ‾(By) = xᵀ G_V ‾B ‾y。比較得 Aᵀ G_W = G_V ‾B
//   ⇒ B = ‾(G_V⁻¹ Aᵀ G_W) = G_V⁻¹ A* G_W（G 皆 Hermitian）。∎
// 推論：標準正交基下 [T*] = [T]*（共軛轉置）。
// ---------------------------------------------------------------------------

///|
/// 伴隨算子之矩陣 A*：滿足 ⟨Ax, y⟩ = ⟨x, A*y⟩。
pub fn[A, B, F : Scalar] adjoint_matrix(
  p : IPSpace[A, F],
  q : IPSpace[B, F],
  tmat : Mat[F],
) -> Mat[F] {
  let gv = gram_of_space(p)
  let gw = gram_of_space(q)
  let gvi = match minv(gv) {
    Some(x) => x
    None => Mat::ident(p.vs.dim)
  }
  gvi.times(tmat.adjointm()).times(gw)
}

// ---------------------------------------------------------------------------
// 【演算法 068】Fourier 係數與展開（標準正交基）
// 定理 068：{eᵢ} 標準正交基 ⇒ x = Σ ⟨x,eᵢ⟩ eᵢ。
// ---------------------------------------------------------------------------

///|
/// 傅立葉係數：對正交基底取內積 ⟨f, eᵢ⟩。
pub fn[V, F] fourier_coeffs(
  s : IPSpace[V, F],
  onb : Array[V],
  x : V,
) -> Array[F] {
  Array::makei(onb.length(), i => (s.inner)(x, onb[i]))
}

///|
/// 由係數重建 Σ cᵢ eᵢ
pub fn[V, F] fourier_synthesis(
  s : IPSpace[V, F],
  onb : Array[V],
  c : Array[F],
) -> V {
  vlincomb(s.vs, c, onb)
}

// ---------------------------------------------------------------------------
// 【演算法 069】Bessel 不等式與 Parseval 恆等式
// 定理 069（Bessel）：{e₁..e_k} 標準正交（不必完備）⇒ Σ|⟨x,eᵢ⟩|² ≤ ‖x‖²。
//   證明：0 ≤ ‖x − Σ⟨x,eᵢ⟩eᵢ‖² = ‖x‖² − Σ|⟨x,eᵢ⟩|²。∎
// 定理 069'（Parseval）：{eᵢ} 為完備標準正交基 ⟺ 上式取等號 ∀x；
//   且 ⟨x,y⟩ = Σ⟨x,eᵢ⟩‾⟨y,eᵢ⟩。
// ---------------------------------------------------------------------------

///|
/// 回傳 (Σ|⟨x,eᵢ⟩|², ‖x‖²) 之雙精度值
pub fn[V, F : Scalar] bessel_pair(
  s : IPSpace[V, F],
  onb : Array[V],
  x : V,
) -> (Double, Double) {
  let mut acc = 0.0
  for e in onb {
    let c = (s.inner)(x, e)
    let m = F::s_mag(c)
    acc = acc + m * m
  }
  (acc, F::s_to_double((s.inner)(x, x)))
}

// ---------------------------------------------------------------------------
// 【演算法 070】Cauchy–Schwarz 憑證（精確版）
// 定理 070：|⟨x,y⟩|² ≤ ⟨x,x⟩⟨y,y⟩，等號 ⟺ x,y 線性相依。
// 證明：若 y = 0 顯然。否則令 λ = ⟨x,y⟩/⟨y,y⟩，則
//   0 ≤ ⟨x−λy, x−λy⟩ = ⟨x,x⟩ − |⟨x,y⟩|²/⟨y,y⟩，兩邊乘 ⟨y,y⟩ > 0。∎
// 本實作回傳「鬆弛量」δ = ⟨x,x⟩⟨y,y⟩ − |⟨x,y⟩|² ∈ 𝔽（精確軌道上 δ ≥ 0 可判定）。
// ---------------------------------------------------------------------------

///|
/// Cauchy–Schwarz 餘裕 ‖x‖²‖y‖² − |⟨x,y⟩|²（≥ 0，義務 D-08 量此值）。
pub fn[V, F : Scalar] cauchy_schwarz_slack(
  s : IPSpace[V, F],
  x : V,
  y : V,
) -> F {
  let ip_xy = (s.inner)(x, y)
  ssub(
    F::s_mul((s.inner)(x, x), (s.inner)(y, y)),
    F::s_mul(ip_xy, F::s_conj(ip_xy)),
  )
}

// ---------------------------------------------------------------------------
// 【演算法 071】三角不等式之精確判定
// 定理 071：‖x+y‖ ≤ ‖x‖ + ‖y‖。
// 精確化：令 a = ‖x‖², b = ‖y‖², c = ‖x+y‖²（皆 ∈ ℚ）。
//   命題等價於 c ≤ a + b + 2√(ab)，再等價於
//   (c − a − b ≤ 0) ∨ ((c − a − b)² ≤ 4ab)。此式只含有理運算 ⇒ 可精確判定。
// ---------------------------------------------------------------------------

///|
/// 三角不等式檢定 ‖x + y‖ ≤ ‖x‖ + ‖y‖。
pub fn[V, F : Scalar] triangle_holds(s : IPSpace[V, F], x : V, y : V) -> Bool {
  let a = (s.inner)(x, x)
  let b = (s.inner)(y, y)
  let c = (s.inner)(vadd(s.vs, x, y), vadd(s.vs, x, y))
  let t = ssub(c, F::s_add(a, b))
  if F::s_cmp_re(t, F::s_zero()) <= 0 {
    return true
  }
  let lhs = F::s_mul(t, t)
  let rhs = F::s_mul(F::s_from_int(4), F::s_mul(a, b))
  F::s_cmp_re(lhs, rhs) <= 0
}

// ---------------------------------------------------------------------------
// 【演算法 072】平行四邊形律與極化恆等式
// 定理 072：‖x+y‖² + ‖x−y‖² = 2‖x‖² + 2‖y‖²（Jordan–von Neumann：
//   此式成立 ⟺ 範數來自某內積）。
// 定理 072'（極化）：
//   實：⟨x,y⟩ = ¼(‖x+y‖² − ‖x−y‖²)
//   複：⟨x,y⟩ = ¼Σ_{k=0}^{3} i^k ‖x + i^k y‖²
// ---------------------------------------------------------------------------

///|
/// 平行四邊形律之殘差（精確軌道上應為 0）
pub fn[V, F : Scalar] parallelogram_defect(
  s : IPSpace[V, F],
  x : V,
  y : V,
) -> F {
  let vsp = s.vs
  let p = vadd(vsp, x, y)
  let m = vsub(vsp, x, y)
  ssub(
    F::s_add((s.inner)(p, p), (s.inner)(m, m)),
    F::s_mul(F::s_from_int(2), F::s_add((s.inner)(x, x), (s.inner)(y, y))),
  )
}

///|
/// 實極化恆等式之右端 ¼(‖x+y‖²−‖x−y‖²)
pub fn[V, F : Scalar] polarization_real(s : IPSpace[V, F], x : V, y : V) -> F {
  let vsp = s.vs
  let p = vadd(vsp, x, y)
  let m = vsub(vsp, x, y)
  F::s_mul(F::s_from_frac(1, 4), ssub((s.inner)(p, p), (s.inner)(m, m)))
}

///|
/// 複極化恆等式之右端 ¼Σ i^k‖x+i^k y‖²（需要 𝔽 = 𝔽₀[i]）
pub fn[V, F : Scalar] polarization_complex(
  s : IPSpace[V, Cpx[F]],
  x : V,
  y : V,
) -> Cpx[F] {
  let vsp = s.vs
  let i_unit : Cpx[F] = Cpx::imag_unit()
  let powers : Array[Cpx[F]] = [
    Cpx::of_real(F::s_one()),
    i_unit,
    Cpx::of_real(F::s_neg(F::s_one())),
    Scalar::s_neg(i_unit),
  ]
  let mut acc : Cpx[F] = Cpx::of_real(F::s_zero())
  for k in 0..<4 {
    let z = vadd(vsp, x, (vsp.smul)(powers[k], y))
    acc = Scalar::s_add(acc, Scalar::s_mul(powers[k], (s.inner)(z, z)))
  }
  Scalar::s_mul(Cpx::of_real(F::s_from_frac(1, 4)), acc)
}

// ---------------------------------------------------------------------------
// 【演算法 073】畢氏定理 / 正交分解
// 定理 073：x ⊥ y ⇒ ‖x+y‖² = ‖x‖² + ‖y‖²（複空間中逆命題需 Re⟨x,y⟩ = 0）。
// 定理 073'：V = W ⊕ W^⊥（正交分解），且 (W^⊥)^⊥ = W。
// ---------------------------------------------------------------------------

///|
/// 正交補 W^⊥ 之基底（以環繞空間向量表示）
pub fn[V, F : Scalar] orthogonal_complement(
  s : IPSpace[V, F],
  ws : Array[V],
) -> Array[V] {
  let n = s.vs.dim
  let k = ws.length()
  // 條件：⟨x, wᵣ⟩ = 0 ∀r。以座標展開：Σ_i x_i ⟨bᵢ, wᵣ⟩ = 0
  let m : Mat[F] = Mat::build(k, n, (r, i) => (s.inner)(s.vs.basis[i], ws[r]))
  let ns = mnullspace(m)
  let out : Array[V] = []
  for v in ns {
    out.push((s.vs.expand)(v))
  }
  out
}

// ---------------------------------------------------------------------------
// 【演算法 074】等距／么正算子判定
// 定理 074：以下等價 (i) T 保內積；(ii) T 保範數；(iii) [T]*G[T] = G；
//   (iv) T 把某組（任一組）標準正交基映為標準正交基。
//   ((ii)⇒(i) 由極化恆等式。)
// ---------------------------------------------------------------------------

///|
/// 判定 T（以矩陣給出）是否為 (V,G) 上之等距
pub fn[V, F : Scalar] is_isometry(s : IPSpace[V, F], tmat : Mat[F]) -> Bool {
  let g = gram_of_space(s)
  tmat.adjointm().times(g).times(tmat).equals(g)
}

// ---------------------------------------------------------------------------
// 【演算法 075】基底變換與 Gram 之變換律
// 命題 075：新基 b'_j = Σ_i S_{ij} bᵢ ⇒ G' = S* G S；
//   且座標變換 c' = S⁻¹c。det G' = |det S|² det G（體積縮放）。
// ---------------------------------------------------------------------------

///|
/// Gram 矩陣之換基律 G' = Sᵀ G S（命題 D-15）。
pub fn[F : Scalar] gram_change_of_basis(g : Mat[F], s : Mat[F]) -> Mat[F] {
  s.adjointm().times(g).times(s)
}

// ---------------------------------------------------------------------------
// 【演算法 076】夾角與餘弦相似度
//   cos θ = Re⟨x,y⟩ / (‖x‖‖y‖) ∈ [−1,1]（由 Cauchy–Schwarz 保證）
// ---------------------------------------------------------------------------

///|
/// 餘弦相似度 ⟨x,y⟩ / (‖x‖‖y‖)。
pub fn[V, F : Scalar] cosine_similarity(
  s : IPSpace[V, F],
  x : V,
  y : V,
) -> Double {
  let nx = ip_norm(s, x)
  let ny = ip_norm(s, y)
  if nx == 0.0 || ny == 0.0 {
    return 0.0
  }
  F::s_to_double(F::s_re_part((s.inner)(x, y))) / (nx * ny)
}

///|
/// 夾角 θ = arccos(cos θ)（以 atan2 實作 arccos）
pub fn[V, F : Scalar] angle_between(s : IPSpace[V, F], x : V, y : V) -> Double {
  let c = mind(1.0, maxd(-1.0, cosine_similarity(s, x, y)))
  atan2_own(sqrt_newton(maxd(0.0, 1.0 - c * c)), c)
}

// ---------------------------------------------------------------------------
// 【演算法 077】Householder 反射（抽象版）
//   H_v x = x − 2(⟨x,v⟩/⟨v,v⟩)·v
// 命題 077：H_v 為等距、對合（H² = I）、自伴、det = −1（實空間）。
// ---------------------------------------------------------------------------

///|
/// Householder 反射 H = I − 2vv*/⟨v,v⟩（將 x 映至基向量方向）。
pub fn[V, F : Scalar] householder(s : IPSpace[V, F], v : V, x : V) -> V {
  let den = (s.inner)(v, v)
  match F::s_inv(den) {
    None => x
    Some(di) => {
      let c = F::s_mul(F::s_from_int(2), F::s_mul((s.inner)(x, v), di))
      vsub(s.vs, x, (s.vs.smul)(c, v))
    }
  }
}

// ---------------------------------------------------------------------------
// 【演算法 078】最小二乘（抽象正規方程）
// 定理 078：min_c ‖x − Σcⱼwⱼ‖ 之解滿足正規方程 Gram·c = b；
//   殘差 r = x − Σcⱼwⱼ ⊥ span{wⱼ}；且 ‖x‖² = ‖P_W x‖² + ‖r‖²。
// ---------------------------------------------------------------------------

///|
/// 回傳 (係數, 殘差範數)
pub fn[V, F : Scalar] least_squares(
  s : IPSpace[V, F],
  ws : Array[V],
  x : V,
) -> (Array[F], Double) {
  let c = projection_coeffs(s, ws, x)
  let r = vsub(s.vs, x, vlincomb(s.vs, c, ws))
  (c, ip_norm(s, r))
}

// ---------------------------------------------------------------------------
// 【演算法 079】Sylvester 判準：Hermitian 矩陣正定性（主子式）
// 定理 079：Hermitian A 正定 ⟺ 所有順序主子式 > 0。
// ---------------------------------------------------------------------------

///|
/// 正定判定：Sylvester 判準（所有順序主餘子式為正）。
pub fn[F : Scalar] is_positive_definite(a : Mat[F]) -> Bool {
  let n = a.mrows
  if !is_hermitian(a) {
    return false
  }
  for k in 1..<(n + 1) {
    let d = mdet(a.sub(0, k, 0, k))
    if !sis_pos(d) {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
// 【演算法 080】標準正交性檢驗
// ---------------------------------------------------------------------------

///|
/// 檢查 {vᵢ} 是否標準正交（⟨vᵢ,vⱼ⟩ = δᵢⱼ）
pub fn[V, F : Scalar] is_orthonormal_set(
  s : IPSpace[V, F],
  vs : Array[V],
) -> Bool {
  for i in 0..<vs.length() {
    for j in 0..<vs.length() {
      let v = (s.inner)(vs[i], vs[j])
      let want = if i == j { F::s_one() } else { F::s_zero() }
      if !F::s_eq(v, want) {
        return false
      }
    }
  }
  true
}

///|
/// 檢查 {vᵢ} 是否兩兩正交
pub fn[V, F : Scalar] is_orthogonal_set(
  s : IPSpace[V, F],
  vs : Array[V],
) -> Bool {
  for i in 0..<vs.length() {
    for j in 0..<vs.length() {
      if i != j && !F::s_is_zero((s.inner)(vs[i], vs[j])) {
        return false
      }
    }
  }
  true
}

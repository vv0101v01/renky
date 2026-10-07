// ============================================================================
//  檔案 06：vecspace.mbt — 座標空間 𝔽ⁿ、函數空間、加權／扭曲內積、子空間
// ============================================================================
//
// 【定理 FD】（有限維結構定理）任意 n 維 𝔽‑向量空間同構於 𝔽ⁿ；
//   任意 n 維內積空間同構（等距）於 (𝔽ⁿ, ⟨x,y⟩_G)，G = Gram(基底) 為正定
//   Hermitian 矩陣；更進一步（Gram–Schmidt）等距於標準 (𝔽ⁿ, ⟨·,·⟩_I)。
//   本檔實作 (𝔽ⁿ, ⟨·,·⟩_G) 之一般機器，其餘空間皆由它或由其它載體建構。
// ============================================================================

///|
/// 座標向量加法
pub fn[F : Scalar] arr_add(a : Array[F], b : Array[F]) -> Array[F] {
  Array::makei(a.length(), i => F::s_add(a[i], b[i]))
}

///|
/// 座標向量減法
pub fn[F : Scalar] arr_sub(a : Array[F], b : Array[F]) -> Array[F] {
  Array::makei(a.length(), i => ssub(a[i], b[i]))
}

///|
/// 座標向量取負
pub fn[F : Scalar] arr_neg(a : Array[F]) -> Array[F] {
  Array::makei(a.length(), i => F::s_neg(a[i]))
}

///|
/// 純量乘
pub fn[F : Scalar] arr_scale(c : F, a : Array[F]) -> Array[F] {
  Array::makei(a.length(), i => F::s_mul(c, a[i]))
}

///|
/// 標準內積 Σ aᵢ ‾bᵢ
pub fn[F : Scalar] arr_dot(a : Array[F], b : Array[F]) -> F {
  let mut acc = F::s_zero()
  for i in 0..<a.length() {
    acc = F::s_add(acc, F::s_mul(a[i], F::s_conj(b[i])))
  }
  acc
}

///|
/// 逐分量相等
pub fn[F : Scalar] arr_eq(a : Array[F], b : Array[F]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if !F::s_eq(a[i], b[i]) {
      return false
    }
  }
  true
}

///|
/// 零向量
pub fn[F : Scalar] arr_zeros(n : Int) -> Array[F] {
  Array::makei(n, _ => F::s_zero())
}

///|
/// 標準基向量 eᵢ
pub fn[F : Scalar] arr_e(n : Int, i : Int) -> Array[F] {
  Array::makei(n, k => if k == i { F::s_one() } else { F::s_zero() })
}

///|
/// 列印 (x₁, …, xₙ)
pub fn[F : Scalar] arr_text(a : Array[F]) -> String {
  let mut s = "("
  for i in 0..<a.length() {
    s = s + F::s_text(a[i])
    if i + 1 < a.length() {
      s = s + ", "
    }
  }
  s + ")"
}

// ---------------------------------------------------------------------------
// 【演算法 031】座標空間機器 (𝔽ⁿ, ⟨x,y⟩_G) ─ 一切「列向量型」空間之共同母體
//   ⟨x,y⟩_G ≔ Σ_{i,j} G_{ij} xᵢ ‾yⱼ，G = G* 正定。
//   G = I 時為標準歐幾里得／么正內積。
// 命題 031：⟨·,·⟩_G 滿足 I1–I5 ⟺ G Hermitian 正定。
//   證明：I1,I2 由雙線性顯然；I3 ⟺ G = G*；I4,I5 ⟺ x*Gx > 0 ∀x≠0。∎
// ---------------------------------------------------------------------------

///|
/// 一般座標向量空間（基底 = 標準基，座標映射 = 恆等）。
pub fn[F : Scalar] coord_vspace(name : String, n : Int) -> VSpace[Array[F], F] {
  {
    vname: name,
    dim: n,
    zero: arr_zeros(n),
    add: (a, b) => arr_add(a, b),
    neg: a => arr_neg(a),
    smul: (c, a) => arr_scale(c, a),
    veq: (a, b) => arr_eq(a, b),
    basis: Array::makei(n, i => arr_e(n, i)),
    coord: a => a.copy(),
    expand: c => c.copy(),
    vshow: a => arr_text(a),
    sample: rng => Array::makei(n, _ => F::s_rand(rng)),
  }
}

///|
/// 以 Gram 矩陣 G 扭曲之內積空間（G = None 表單位矩陣）。
pub fn[F : Scalar] coord_ipspace(
  name : String,
  n : Int,
  g : Mat[F]?,
) -> IPSpace[Array[F], F] {
  let vs = coord_vspace(name, n)
  match g {
    None =>
      {
        vs,
        ipname: "⟨x,y⟩ = Σ xᵢ‾yᵢ",
        inner: (a, b) => arr_dot(a, b),
      }
    Some(gm) =>
      {
        vs,
        ipname: "⟨x,y⟩_G = Σ G_ij xᵢ‾yⱼ",
        inner: (a, b) => {
          let mut acc = F::s_zero()
          for i in 0..<n {
            for j in 0..<n {
              acc = F::s_add(
                acc,
                F::s_mul(gm.at(i, j), F::s_mul(a[i], F::s_conj(b[j]))),
              )
            }
          }
          acc
        },
      }
  }
}

// ---------------------------------------------------------------------------
//  具體空間 1：標準歐幾里得空間 ℝⁿ / 一般 𝔽ⁿ
// ---------------------------------------------------------------------------

///|
/// 【空間 S1】標準歐幾里得空間 𝔽ⁿ，⟨x,y⟩ = Σ xᵢ‾yᵢ。
/// 於 F = Double 即 ℝⁿ；於 F = Q 即 ℚⁿ（精確歐氏空間）。
pub fn[F : Scalar] euclidean_space(n : Int) -> IPSpace[Array[F], F] {
  coord_ipspace(
    F::s_name() + "^" + n.to_string() + "（標準歐幾里得）",
    n,
    None,
  )
}

///|
/// 【空間 S2】複 Hermitian 座標空間 ℂⁿ，⟨x,y⟩ = Σ xᵢ‾yᵢ（第二變數共軛）。
pub fn[F : Scalar] unitary_space(n : Int) -> IPSpace[Array[Cpx[F]], Cpx[F]] {
  coord_ipspace("ℂ^" + n.to_string() + "（么正/Hermitian）", n, None)
}

// ---------------------------------------------------------------------------
//  具體空間 3：有限集合上之函數空間 𝔽^S（含加權測度）
// ---------------------------------------------------------------------------

///|
/// 【空間 S3】有限集合 S = {s₁,…,s_n} 上之函數空間 𝔽^S ≅ 𝔽ⁿ，
/// 配上測度 μ(sᵢ) = wᵢ > 0 之 L²(S,μ) 內積 ⟨f,g⟩ = Σ wᵢ f(sᵢ)‾g(sᵢ)。
/// 命題：wᵢ > 0 ∀i ⟺ 此型式正定（G = diag(w) 正定）。
/// 註：ℓ²(S) 即 w ≡ 1；期望值內積即 w = 機率質量。
pub fn[F : Scalar] function_space(
  labels : Array[String],
  weights : Array[F],
) -> IPSpace[Array[F], F] {
  let n = labels.length()
  let vs = VSpace::{
    vname: "𝔽^S，S = {" + labels.join(", ") + "}",
    dim: n,
    zero: arr_zeros(n),
    add: (a, b) => arr_add(a, b),
    neg: a => arr_neg(a),
    smul: (c, a) => arr_scale(c, a),
    veq: (a, b) => arr_eq(a, b),
    basis: Array::makei(n, i => arr_e(n, i)),
    coord: a => a.copy(),
    expand: c => c.copy(),
    vshow: a => {
      let mut s = "{"
      for i in 0..<n {
        s = s + labels[i] + "↦" + F::s_text(a[i])
        if i + 1 < n {
          s = s + ", "
        }
      }
      s + "}"
    },
    sample: rng => Array::makei(n, _ => F::s_rand(rng)),
  }
  {
    vs,
    ipname: "⟨f,g⟩ = Σ_s w(s)·f(s)‾g(s)",
    inner: (a, b) => {
      let mut acc = F::s_zero()
      for i in 0..<n {
        acc = F::s_add(
          acc,
          F::s_mul(weights[i], F::s_mul(a[i], F::s_conj(b[i]))),
        )
      }
      acc
    },
  }
}

///|
/// 均勻權重（計數測度）之函數空間
pub fn[F : Scalar] function_space_unit(
  labels : Array[String],
) -> IPSpace[Array[F], F] {
  function_space(labels, Array::makei(labels.length(), _ => F::s_one()))
}

// ---------------------------------------------------------------------------
// 【演算法 032】子空間建構：由生成集造出帶誘導內積之子空間
//   輸入：環繞內積空間 (W, ⟨·,·⟩)、生成向量 g₁,…,g_m ∈ W。
//   步驟：(1) 取座標矩陣 C（每行為 gⱼ 之座標）；(2) RREF 取主元行 ⇒ 基底 B；
//        (3) 子空間座標映射 = 解 C_B c = coord_W(v)（最小二乘/精確解）。
// 命題 032：主元行所對應之 gⱼ 構成 span{gⱼ} 之基底（演算法 020 之推論）；
//   誘導型式為子空間上之內積（正定性由限制保持）。
// 【空間 S4】列空間 col(A)：取 A 之各行為生成集即得。
// ---------------------------------------------------------------------------

///|
/// 由生成集造子空間（載體仍為環繞空間之向量；座標 = 在所選基底下之係數）。
pub fn[V, F : Scalar] subspace_of(
  name : String,
  amb : IPSpace[V, F],
  spanners : Array[V],
) -> IPSpace[V, F] {
  let ambdim = amb.vs.dim
  let m = spanners.length()
  // 座標矩陣：第 j 行為 spanners[j] 之環繞座標
  let cmat : Mat[F] = Mat::build(ambdim, m, (i, j) => {
    vcoord(amb.vs, spanners[j])[i]
  })
  let rr = mrref(cmat)
  let basis : Array[V] = []
  for p in rr.pivots {
    basis.push(spanners[p])
  }
  let k = basis.length()
  // 基底座標矩陣 B（ambdim × k），座標求解用
  let bmat : Mat[F] = Mat::build(ambdim, k, (i, j) => {
    vcoord(amb.vs, basis[j])[i]
  })
  let vs = VSpace::{
    vname: name,
    dim: k,
    zero: amb.vs.zero,
    add: amb.vs.add,
    neg: amb.vs.neg,
    smul: amb.vs.smul,
    veq: amb.vs.veq,
    basis,
    coord: v => {
      let sol = msolve(bmat, vcoord(amb.vs, v))
      if sol.solvable {
        sol.particular
      } else {
        arr_zeros(k)
      }
    },
    expand: c => vlincomb(amb.vs, c, basis),
    vshow: amb.vs.vshow,
    sample: rng => {
      let c = Array::makei(k, _ => F::s_rand(rng))
      vlincomb(amb.vs, c, basis)
    },
  }
  { vs, ipname: amb.ipname + "（限制於子空間）", inner: amb.inner, }
}

///|
/// 【空間 S4】矩陣 A 之列空間 col(A) ⊆ 𝔽^m（即「像空間」），帶標準內積。
pub fn[F : Scalar] column_space(a : Mat[F]) -> IPSpace[Array[F], F] {
  let amb : IPSpace[Array[F], F] = euclidean_space(a.mrows)
  let cols : Array[Array[F]] = Array::makei(a.mcols, j => a.col(j))
  subspace_of("col(A) ⊆ 𝔽^" + a.mrows.to_string(), amb, cols)
}

///|
/// A 之列空間（row space，作為 𝔽ⁿ 之子空間）
pub fn[F : Scalar] row_space(a : Mat[F]) -> IPSpace[Array[F], F] {
  let amb : IPSpace[Array[F], F] = euclidean_space(a.mcols)
  let rows : Array[Array[F]] = Array::makei(a.mrows, i => a.row(i))
  subspace_of("row(A) ⊆ 𝔽^" + a.mcols.to_string(), amb, rows)
}

///|
/// A 之零空間 ker(A)（作為 𝔽ⁿ 之子空間；A 滿秩時為零空間，dim = 0）
pub fn[F : Scalar] kernel_space(a : Mat[F]) -> IPSpace[Array[F], F] {
  let amb : IPSpace[Array[F], F] = euclidean_space(a.mcols)
  let ns = mnullspace(a)
  if ns.length() == 0 {
    // 零子空間：維數 0
    let vs = VSpace::{
      vname: "ker(A) = {0}",
      dim: 0,
      zero: arr_zeros(a.mcols),
      add: (x, y) => arr_add(x, y),
      neg: x => arr_neg(x),
      smul: (c, x) => arr_scale(c, x),
      veq: (x, y) => arr_eq(x, y),
      basis: [],
      coord: _ => [],
      expand: _ => arr_zeros(a.mcols),
      vshow: x => arr_text(x),
      sample: _ => arr_zeros(a.mcols),
    }
    return {
      vs,
      ipname: "⟨x,y⟩ = Σ xᵢ‾yᵢ",
      inner: (x, y) => arr_dot(x, y),
    }
  }
  subspace_of("ker(A) ⊆ 𝔽^" + a.mcols.to_string(), amb, ns)
}

// ============================================================================
//  檔案 12：combinators.mbt — 空間之組合子（construction functors）
//    C1 直和 P ⊕ Q           C2 張量積 P ⊗ Q        C3 對偶 P*
//    C4 Hom(P,Q) ≅ Q ⊗ P*    C5 實化 (ℂ‑空間 → ℝ‑空間)
//    C6 內積扭曲 ⟨·,·⟩_A      C7 外冪 Λᵏ（見 exterior.mbt）
//
//  這些組合子令「不同空間互相組合」成為一等公民：任意兩個已建構之內積空間
//  都可再組合，且組合結果自動滿足全部公理（證明見下，檢驗見 obligations）。
// ============================================================================

// ---------------------------------------------------------------------------
// 【演算法 054】空間之 Gram 矩陣 G_{ij} = ⟨bᵢ, bⱼ⟩
// 命題 054：G = G*（Hermitian）且正定；基底為標準正交 ⟺ G = I。
//   任意 x,y：⟨x,y⟩ = Σ_{ij} G_{ij} xᵢ‾yⱼ（座標公式）。
// ---------------------------------------------------------------------------

///|
/// 空間之 Gram 矩陣：對基底逐對取內積。
pub fn[V, F] gram_of_space(s : IPSpace[V, F]) -> Mat[F] {
  let n = s.vs.dim
  Mat::build(n, n, (i, j) => (s.inner)(s.vs.basis[i], s.vs.basis[j]))
}

///|
/// 一組向量之 Gram 矩陣
pub fn[V, F] gram_of(s : IPSpace[V, F], xs : Array[V]) -> Mat[F] {
  let n = xs.length()
  Mat::build(n, n, (i, j) => (s.inner)(xs[i], xs[j]))
}

// ---------------------------------------------------------------------------
// 【演算法 055】直和 P ⊕ Q（正交直和）
//   載體 V₁ × V₂，⟨(x₁,x₂),(y₁,y₂)⟩ = ⟨x₁,y₁⟩₁ + ⟨x₂,y₂⟩₂。
// 命題 055：公理 I1–I5 由兩分量逐條相加而成立；dim(P⊕Q) = dim P + dim Q；
//   且 V₁⊕0 ⊥ 0⊕V₂（故稱正交直和）。
// 定理（維數公式）：dim(U+W) + dim(U∩W) = dim U + dim W（內部直和之推廣）。
// ---------------------------------------------------------------------------

///|
/// 直和 V ⊕ W：維數相加，內積為正交和（⟨(a,b),(a',b')⟩ = ⟨a,a'⟩ + ⟨b,b'⟩）。
pub fn[A, B, F : Scalar] direct_sum(
  p : IPSpace[A, F],
  q : IPSpace[B, F],
) -> IPSpace[(A, B), F] {
  let d1 = p.vs.dim
  let d2 = q.vs.dim
  let basis : Array[(A, B)] = []
  for b in p.vs.basis {
    basis.push((b, q.vs.zero))
  }
  for b in q.vs.basis {
    basis.push((p.vs.zero, b))
  }
  let vs = VSpace::{
    vname: p.vs.vname + " ⊕ " + q.vs.vname,
    dim: d1 + d2,
    zero: (p.vs.zero, q.vs.zero),
    add: (x, y) => ((p.vs.add)(x.0, y.0), (q.vs.add)(x.1, y.1)),
    neg: x => ((p.vs.neg)(x.0), (q.vs.neg)(x.1)),
    smul: (c, x) => ((p.vs.smul)(c, x.0), (q.vs.smul)(c, x.1)),
    veq: (x, y) => (p.vs.veq)(x.0, y.0) && (q.vs.veq)(x.1, y.1),
    basis,
    coord: x => {
      let a = (p.vs.coord)(x.0)
      let b = (q.vs.coord)(x.1)
      Array::makei(d1 + d2, i => if i < d1 { a[i] } else { b[i - d1] })
    },
    expand: c => {
      (
        (p.vs.expand)(Array::makei(d1, i => c[i])),
        (q.vs.expand)(Array::makei(d2, i => c[d1 + i])),
      )
    },
    vshow: x => "(" + (p.vs.vshow)(x.0) + " ; " + (q.vs.vshow)(x.1) + ")",
    sample: rng => ((p.vs.sample)(rng), (q.vs.sample)(rng)),
  }
  {
    vs,
    ipname: "⟨(x₁,x₂),(y₁,y₂)⟩ = ⟨x₁,y₁⟩ + ⟨x₂,y₂⟩",
    inner: (x, y) => F::s_add((p.inner)(x.0, y.0), (q.inner)(x.1, y.1)),
  }
}

// ---------------------------------------------------------------------------
// 【演算法 056】張量積 P ⊗ Q
//   基底 {bᵢ ⊗ cⱼ}，dim = dim P · dim Q；
//   Gram(P⊗Q) = Gram(P) ⊗ Gram(Q)（Kronecker 積）。
// 命題 056：⟨x₁⊗x₂, y₁⊗y₂⟩ = ⟨x₁,y₁⟩⟨x₂,y₂⟩ 唯一決定 P⊗Q 上之內積，
//   且該形式正定（兩正定矩陣之 Kronecker 積正定：特徵值為兩譜之乘積）。
// 命題 056'（普遍性質）：對任意雙線性映射 β : V×W → Z 存在唯一線性
//   b : V⊗W → Z 使 β = b∘⊗。本實作以座標張量實現 ⊗。
// ---------------------------------------------------------------------------

///|
/// 張量積 V ⊗ W：內積 ⟨a⊗b, a'⊗b'⟩ = ⟨a,a'⟩·⟨b,b'⟩。
pub fn[A, B, F : Scalar] tensor_space(
  p : IPSpace[A, F],
  q : IPSpace[B, F],
) -> IPSpace[Array[F], F] {
  let d1 = p.vs.dim
  let d2 = q.vs.dim
  let g1 = gram_of_space(p)
  let g2 = gram_of_space(q)
  let g = mkron(g1, g2)
  let sp = coord_ipspace(p.vs.vname + " ⊗ " + q.vs.vname, d1 * d2, Some(g))
  {
    vs: sp.vs,
    ipname: "⟨x₁⊗x₂,y₁⊗y₂⟩ = ⟨x₁,y₁⟩⟨x₂,y₂⟩（Gram = G₁⊗G₂）",
    inner: sp.inner,
  }
}

///|
/// 張量積，因子 Gram 由呼叫端提供。
///
/// 【為何需要】`tensor_space(p,q)` 內部呼叫 `gram_of_space(p)` 與
/// `gram_of_space(q)`，而後者以 d² 次內積呼叫重建因子的 Gram（Θ(d³)）。
/// 在一張 45 × 45 的配對表裡，同一個因子的 Gram 會被重算 45 次 ——
/// 這是純粹的共用子式重複，與「張量積怎麼定義」無關。
///
/// 【定理】若 g1 = gram_of_space(p) 且 g2 = gram_of_space(q)，則
/// `tensor_space_g(p,q,g1,g2)` 與 `tensor_space(p,q)` 回傳**同一個**
/// 內積空間（維數相同、Gram 逐元相同、內積函數由同一個 coord_ipspace
/// 產生）。證明：`tensor_space` 的輸出只透過 g1、g2 依賴 p、q，
/// 其餘部分逐字相同。∎（N-84 之義務在 45 個空間上逐對核對）
pub fn[A, B, F : Scalar] tensor_space_g(
  p : IPSpace[A, F],
  q : IPSpace[B, F],
  g1 : Mat[F],
  g2 : Mat[F],
) -> IPSpace[Array[F], F] {
  let d1 = p.vs.dim
  let d2 = q.vs.dim
  let g = mkron(g1, g2)
  let sp = coord_ipspace(p.vs.vname + " ⊗ " + q.vs.vname, d1 * d2, Some(g))
  {
    vs: sp.vs,
    ipname: "⟨x₁⊗x₂,y₁⊗y₂⟩ = ⟨x₁,y₁⟩⟨x₂,y₂⟩（Gram = G₁⊗G₂）",
    inner: sp.inner,
  }
}

///|
/// 純張量 x ⊗ y 之座標（外積）
pub fn[A, B, F : Scalar] tensor_pure(
  p : IPSpace[A, F],
  q : IPSpace[B, F],
  x : A,
  y : B,
) -> Array[F] {
  let a = (p.vs.coord)(x)
  let b = (q.vs.coord)(y)
  let d2 = q.vs.dim
  Array::makei(a.length() * d2, k => F::s_mul(a[k / d2], b[k % d2]))
}

///|
/// 張量積上之算子 A ⊗ B（座標表示 = Kronecker 積）
pub fn[F : Scalar] tensor_operator(a : Mat[F], b : Mat[F]) -> Mat[F] {
  mkron(a, b)
}

///|
/// 部分跡 tr₂ : (V⊗W 上之算子) → (V 上之算子)
/// 命題：tr(tr₂(M)·A) = tr(M·(A⊗I))，且 tr₂(A⊗B) = tr(B)·A。
pub fn[F : Scalar] partial_trace2(m : Mat[F], d1 : Int, d2 : Int) -> Mat[F] {
  Mat::build(d1, d1, (i, j) => {
    let mut acc = F::s_zero()
    for k in 0..<d2 {
      acc = F::s_add(acc, m.at(i * d2 + k, j * d2 + k))
    }
    acc
  })
}

// ---------------------------------------------------------------------------
// 【演算法 057】對偶空間 P* = Hom(V, 𝔽)
//   以「對偶基底座標」表示泛函：φ ↦ (φ(b₁),…,φ(b_n))。
//   誘導內積（Riesz 傳遞）：Gram(V*) = (G⁻¹)ᵀ。
// 命題 057：dim V* = dim V；對偶基底 {b^i} 滿足 b^i(bⱼ) = δ^i_j；
//   自然映射 V → V**，v ↦ ev_v 為同構（有限維），且為等距。
// 定理（Riesz 表示定理）：∀φ ∈ V* ∃!v_φ ∈ V, φ(x) = ⟨x, v_φ⟩；
//   映射 φ ↦ v_φ 為共軛線性等距雙射。證明見 ipalgo.mbt 演算法 066。
// ---------------------------------------------------------------------------

///|
/// 對偶空間 V*：經 Riesz 表示實作，內積取對偶配對。
pub fn[V, F : Scalar] dual_space(p : IPSpace[V, F]) -> IPSpace[Array[F], F] {
  let n = p.vs.dim
  let g = gram_of_space(p)
  let gi = match minv(g) {
    Some(x) => x
    None => Mat::ident(n)
  }
  let h = gi.transpose()
  let sp = coord_ipspace("(" + p.vs.vname + ")*", n, Some(h))
  {
    vs: sp.vs,
    ipname: "⟨φ,ψ⟩_{V*}（Gram = (G⁻¹)ᵀ，Riesz 誘導）",
    inner: sp.inner,
  }
}

///|
/// 泛函求值 φ(v) = Σ cᵢ·(coord v)ᵢ
pub fn[V, F : Scalar] dual_eval(p : IPSpace[V, F], c : Array[F], v : V) -> F {
  let x = (p.vs.coord)(v)
  let mut acc = F::s_zero()
  for i in 0..<x.length() {
    acc = F::s_add(acc, F::s_mul(c[i], x[i]))
  }
  acc
}

///|
/// 自然嵌入 V → V**（座標上為恆等）
pub fn[V, F] double_dual_embed(p : IPSpace[V, F], v : V) -> Array[F] {
  (p.vs.coord)(v)
}

// ---------------------------------------------------------------------------
// 【演算法 058】Hom(P,Q) ≅ Q ⊗ P*（矩陣空間，Hilbert–Schmidt 內積）
//   以矩陣座標 (i,j) ↦ i·dim V + j 表示；
//   Gram(Hom) = Gram(Q) ⊗ Gram(P*)。
// 命題 058：dim Hom(V,W) = dim V · dim W；
//   標準正交基時退化為 ⟨A,B⟩ = tr(B*A)（Frobenius）。
// ---------------------------------------------------------------------------

///|
/// Hom(V, W)（以 W ⊗ V* 實現；Hilbert–Schmidt 內積 ⟨T,S⟩ = tr(S*T)）。
pub fn[A, B, F : Scalar] hom_space(
  p : IPSpace[A, F],
  q : IPSpace[B, F],
) -> IPSpace[Array[F], F] {
  let dp = dual_space(p)
  let t = tensor_space(q, dp)
  {
    vs: {
      vname: "Hom(" + p.vs.vname + " , " + q.vs.vname + ")",
      dim: t.vs.dim,
      zero: t.vs.zero,
      add: t.vs.add,
      neg: t.vs.neg,
      smul: t.vs.smul,
      veq: t.vs.veq,
      basis: t.vs.basis,
      coord: t.vs.coord,
      expand: t.vs.expand,
      vshow: t.vs.vshow,
      sample: t.vs.sample,
    },
    ipname: "⟨A,B⟩_HS（= tr(B*A)，標準正交基時）",
    inner: t.inner,
  }
}

///|
/// 線性映射之矩陣表示：T : V → W 於兩邊基底下之矩陣
pub fn[A, B, F] matrix_of_map(
  p : IPSpace[A, F],
  q : IPSpace[B, F],
  t : (A) -> B,
) -> Mat[F] {
  let n = p.vs.dim
  let m = q.vs.dim
  let cols : Array[Array[F]] = Array::makei(n, j => {
    (q.vs.coord)(t(p.vs.basis[j]))
  })
  Mat::build(m, n, (i, j) => cols[j][i])
}

// ---------------------------------------------------------------------------
// 【演算法 059】實化（restriction of scalars）：ℂ‑空間 → ℝ‑空間
//   V_ℝ 之基底 {b₁,…,b_n, i b₁,…, i b_n}，dim_ℝ = 2 dim_ℂ；
//   ⟨x,y⟩_ℝ ≔ Re⟨x,y⟩_ℂ。
// 命題 059：⟨·,·⟩_ℝ 為實內積；且 ‖x‖_ℝ = ‖x‖_ℂ（範數不變）；
//   Im⟨x,y⟩_ℂ = ⟨x, i y⟩_ℝ 給出辛形式 ω，(V_ℝ, ⟨,⟩_ℝ, ω, J) 為 Kähler 三元組。
// ---------------------------------------------------------------------------

///|
/// 實化：ℂ-內積空間視為 ℝ-內積空間（維數翻倍，實部內積）。
pub fn[V, F : Scalar] realify(p : IPSpace[V, Cpx[F]]) -> IPSpace[V, F] {
  let n = p.vs.dim
  let d = 2 * n
  let ic : Cpx[F] = Cpx::imag_unit()
  let basis : Array[V] = []
  for b in p.vs.basis {
    basis.push(b)
  }
  for b in p.vs.basis {
    basis.push((p.vs.smul)(ic, b))
  }
  let vs = VSpace::{
    vname: p.vs.vname + "（實化 dim_ℝ = " + d.to_string() + "）",
    dim: d,
    zero: p.vs.zero,
    add: p.vs.add,
    neg: p.vs.neg,
    smul: (c, x) => (p.vs.smul)(Cpx::of_real(c), x),
    veq: p.vs.veq,
    basis,
    coord: x => {
      let c = (p.vs.coord)(x)
      Array::makei(d, k => if k < n { c[k].cre } else { c[k - n].cim })
    },
    expand: r => {
      let c : Array[Cpx[F]] = Array::makei(n, i => Cpx::mk(r[i], r[n + i]))
      (p.vs.expand)(c)
    },
    vshow: p.vs.vshow,
    sample: p.vs.sample,
  }
  {
    vs,
    ipname: "⟨x,y⟩_ℝ = Re⟨x,y⟩_ℂ",
    inner: (x, y) => (p.inner)(x, y).cre,
  }
}

///|
/// 複結構算子 J（乘以 i）於實化空間座標下之矩陣；J² = −I。
pub fn[V, F : Scalar] complex_structure_matrix(
  p : IPSpace[V, Cpx[F]],
) -> Mat[F] {
  let n = p.vs.dim
  Mat::build(2 * n, 2 * n, (i, j) => {
    if i >= n && j == i - n {
      F::s_one()
    } else if i < n && j == i + n {
      F::s_neg(F::s_one())
    } else {
      F::s_zero()
    }
  })
}

// ---------------------------------------------------------------------------
// 【演算法 060】內積扭曲：同一向量空間，換一個正定 Gram A
//   ⟨x,y⟩_A ≔ Σ_{ij} A_{ij} xᵢ‾yⱼ（座標上）。
// 命題 060：A Hermitian 正定 ⟺ ⟨·,·⟩_A 為內積；
//   且恆等映射 (V,⟨,⟩_I) → (V,⟨,⟩_A) 為同構但一般非等距；
//   A = L L*（Cholesky）時 L⁻¹ 為等距同構。
// ---------------------------------------------------------------------------

///|
/// 內積扭曲：⟨x, y⟩_A = xᵀ A y（A 須正定，見 F6 之義務檢驗）。
pub fn[V, F : Scalar] retwist(p : IPSpace[V, F], a : Mat[F]) -> IPSpace[V, F] {
  let n = p.vs.dim
  {
    vs: p.vs,
    ipname: "⟨x,y⟩_A = Σ A_ij xᵢ‾yⱼ（扭曲內積）",
    inner: (x, y) => {
      let cx = (p.vs.coord)(x)
      let cy = (p.vs.coord)(y)
      let mut acc = F::s_zero()
      for i in 0..<n {
        for j in 0..<n {
          acc = F::s_add(
            acc,
            F::s_mul(a.at(i, j), F::s_mul(cx[i], F::s_conj(cy[j]))),
          )
        }
      }
      acc
    },
  }
}

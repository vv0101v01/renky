// ============================================================================
//  檔案 11：exterior.mbt — 外代數 Λ(𝔽ⁿ)、楔積、Hodge 星、Plücker 座標
//    S17 Λᵏ(𝔽ⁿ)，dim = C(n,k)，⟨e_I, e_J⟩ = δ_{IJ}
//    S18 全外代數 Λ(𝔽ⁿ) = ⊕ₖ Λᵏ，dim = 2ⁿ（分次正交直和）
// ============================================================================
//
// 【定義 E】Λᵏ V ≔ V^{⊗k}/⟨…⊗v⊗…⊗v⊗…⟩（交錯張量）。
//   以 V = 𝔽ⁿ 標準基 e₁..e_n 表之：基底 {e_I = e_{i₁}∧…∧e_{i_k} : I 遞增}，
//   dim Λᵏ = C(n,k)。
// 【命題 E1】楔積雙線性、結合，且 α∧β = (−1)^{pq} β∧α（α ∈ Λᵖ, β ∈ Λᵠ）。
// 【定理 E2】（Gram 行列式公式）
//   ⟨v₁∧…∧v_k, w₁∧…∧w_k⟩ = det(⟨vᵢ,wⱼ⟩)。
//   證明：兩邊皆對每個 vᵢ、wⱼ 多重線性且交錯，於基底向量上取值相同
//   （Cauchy–Binet 恆等式）。∎
//   推論：k 維平行多面體體積 vol = √det(Gram(v₁..v_k))（見演算法 062）。
// 【定理 E3】（Hodge 星）歐氏度量下 ⋆ : Λᵏ → Λ^{n−k} 由
//   α ∧ ⋆β = ⟨α,β⟩·e_{1..n} 唯一確定；且 ⋆⋆ = (−1)^{k(n−k)} id。
// 【推論 E4】n = 3 時 a × b ≔ ⋆(a ∧ b)，滿足 Lagrange 恆等式
//   ‖a×b‖² = ‖a‖²‖b‖² − ⟨a,b⟩²，且 a×b ⊥ a, b。
// 【命題 E5】v₁∧…∧v_n = det(V)·e_{1..n}（行列式之無座標定義）。
// ============================================================================

///|
/// 列舉 {0,…,n−1} 之遞增 k‑子集（字典序）
pub fn subsets_k(n : Int, k : Int) -> Array[Array[Int]] {
  let out : Array[Array[Int]] = []
  if k < 0 || k > n {
    return out
  }
  if k == 0 {
    out.push([])
    return out
  }
  let cur = Array::make(k, 0)
  fn rec(pos : Int, start : Int) -> Unit {
    if pos == k {
      out.push(cur.copy())
      return
    }
    for v in start..<n {
      cur[pos] = v
      rec(pos + 1, v + 1)
    }
  }

  rec(0, 0)
  out
}

///|
/// C(n,k)
pub fn binom(n : Int, k : Int) -> Int {
  if k < 0 || k > n {
    return 0
  }
  let mut acc = 1L
  for i in 0..<k {
    acc = acc * (n - i).to_int64() / (i + 1).to_int64()
  }
  acc.to_int()
}

///|
/// 子集 → 位元遮罩
pub fn mask_of(s : Array[Int]) -> Int {
  let mut m = 0
  for i in s {
    m = m | (1 << i)
  }
  m
}

///|
/// 由 (n,k) 之子集列表造「遮罩 → 索引」查表
pub fn subset_index_table(n : Int, k : Int) -> Array[Int] {
  let tbl = Array::make(1 << n, -1)
  let ss = subsets_k(n, k)
  for i in 0..<ss.length() {
    tbl[mask_of(ss[i])] = i
  }
  tbl
}

///|
/// 合併兩個遞增子集之符號：(−1)^{#{(i,j) ∈ I×J : i > j}}；相交回 0。
pub fn merge_sign(ii : Array[Int], jj : Array[Int]) -> Int {
  for a in ii {
    for b in jj {
      if a == b {
        return 0
      }
    }
  }
  let mut inv = 0
  for a in ii {
    for b in jj {
      if a > b {
        inv = inv + 1
      }
    }
  }
  if inv % 2 == 0 {
    1
  } else {
    -1
  }
}

///|
/// 子集之補集（遞增）
pub fn complement_of(n : Int, s : Array[Int]) -> Array[Int] {
  let m = mask_of(s)
  let out : Array[Int] = []
  for i in 0..<n {
    if (m & (1 << i)) == 0 {
      out.push(i)
    }
  }
  out
}

///|
/// 子集排序後之標籤 "e₁∧e₃"
pub fn subset_label(s : Array[Int]) -> String {
  if s.length() == 0 {
    return "1"
  }
  let mut t = ""
  for i in 0..<s.length() {
    t = t + "e" + (s[i] + 1).to_string()
    if i + 1 < s.length() {
      t = t + "∧"
    }
  }
  t
}

// ---------------------------------------------------------------------------
// 【演算法 049】楔積 Λᵖ × Λᵠ → Λ^{p+q}
//   (Σ a_I e_I) ∧ (Σ b_J e_J) = Σ_{I∩J=∅} ε(I,J) a_I b_J e_{I∪J}
// ---------------------------------------------------------------------------

///|
/// 楔積 Λᵖ × Λᵠ → Λᵖ⁺ᵠ；交錯性 α∧β = (−1)^{pq} β∧α（命題 E1）。
pub fn[F : Scalar] wedge(
  n : Int,
  p : Int,
  q : Int,
  a : Array[F],
  b : Array[F],
) -> Array[F] {
  let si = subsets_k(n, p)
  let sj = subsets_k(n, q)
  let sk = subsets_k(n, p + q)
  let tbl = subset_index_table(n, p + q)
  let out = arr_zeros(sk.length())
  for x in 0..<si.length() {
    if F::s_is_zero(a[x]) {
      continue
    }
    for y in 0..<sj.length() {
      if F::s_is_zero(b[y]) {
        continue
      }
      let sg = merge_sign(si[x], sj[y])
      if sg == 0 {
        continue
      }
      let m = mask_of(si[x]) | mask_of(sj[y])
      let idx = tbl[m]
      if idx >= 0 {
        let term = F::s_mul(a[x], b[y])
        let signed = if sg > 0 { term } else { F::s_neg(term) }
        out[idx] = F::s_add(out[idx], signed)
      }
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 【演算法 050】Hodge 星算子 ⋆ : Λᵏ → Λ^{n−k}
//   ⋆e_I = ε(I, Iᶜ)·e_{Iᶜ}
// ---------------------------------------------------------------------------

///|
/// Hodge 星算子 ⋆: Λᵏ → Λ^{n−k}（以基序與補集符號定之）。
pub fn[F : Scalar] hodge_star(n : Int, k : Int, a : Array[F]) -> Array[F] {
  let si = subsets_k(n, k)
  let sc = subsets_k(n, n - k)
  let tbl = subset_index_table(n, n - k)
  let out = arr_zeros(sc.length())
  for x in 0..<si.length() {
    let c = complement_of(n, si[x])
    let sg = merge_sign(si[x], c)
    let idx = tbl[mask_of(c)]
    if idx >= 0 {
      out[idx] = if sg > 0 { a[x] } else { F::s_neg(a[x]) }
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 【演算法 051】可分解 k‑向量 v₁∧…∧v_k 之 Plücker 座標（k×k 子式）
// 命題 051：(v₁∧…∧v_k)_I = det(V[I, :])，V 之第 i 行為 vᵢ。
// ---------------------------------------------------------------------------

///|
/// 向量楔積 v₁ ∧ … ∧ v_k ∈ Λᵏ（k 個向量之外積）。
pub fn[F : Scalar] wedge_vectors(n : Int, vs : Array[Array[F]]) -> Array[F] {
  let k = vs.length()
  let ss = subsets_k(n, k)
  Array::makei(ss.length(), t => {
    let rows = ss[t]
    let sub : Mat[F] = Mat::build(k, k, (i, j) => vs[j][rows[i]])
    mdet(sub)
  })
}

// ---------------------------------------------------------------------------
//  【空間 S17】Λᵏ(𝔽ⁿ) 之內積空間
// ---------------------------------------------------------------------------

///|
/// Λᵏ(𝔽ⁿ)，基底 {e_I}，⟨e_I,e_J⟩ = δ_{IJ}（由定理 E2 與標準內積相容）。
pub fn[F : Scalar] exterior_power_space(
  n : Int,
  k : Int,
) -> IPSpace[Array[F], F] {
  let ss = subsets_k(n, k)
  let d = ss.length()
  let vs = VSpace::{
    vname: "Λ^" + k.to_string() + "(" + F::s_name() + "^" + n.to_string() + ")",
    dim: d,
    zero: arr_zeros(d),
    add: (a, b) => arr_add(a, b),
    neg: a => arr_neg(a),
    smul: (c, a) => arr_scale(c, a),
    veq: (a, b) => arr_eq(a, b),
    basis: Array::makei(d, i => arr_e(d, i)),
    coord: a => a.copy(),
    expand: c => c.copy(),
    vshow: a => {
      let mut s = ""
      let mut first = true
      for i in 0..<d {
        if !F::s_is_zero(a[i]) {
          if !first {
            s = s + " + "
          }
          s = s + F::s_text(a[i]) + "·" + subset_label(ss[i])
          first = false
        }
      }
      if first {
        "0"
      } else {
        s
      }
    },
    sample: rng => Array::makei(d, _ => F::s_rand(rng)),
  }
  {
    vs,
    ipname: "⟨e_I,e_J⟩ = δ_IJ（= det Gram，定理 E2）",
    inner: (a, b) => arr_dot(a, b),
  }
}

///|
/// 【空間 S18】全外代數 Λ(𝔽ⁿ) = ⊕_{k=0}^{n} Λᵏ，dim = 2ⁿ。
/// 座標以位元遮罩索引（mask 之 popcount = 分次次數）。
pub fn[F : Scalar] exterior_algebra_space(n : Int) -> IPSpace[Array[F], F] {
  let d = 1 << n
  let labels : Array[String] = Array::makei(d, m => {
    let s : Array[Int] = []
    for i in 0..<n {
      if (m & (1 << i)) != 0 {
        s.push(i)
      }
    }
    subset_label(s)
  })
  let vs = VSpace::{
    vname: "Λ(" +
    F::s_name() +
    "^" +
    n.to_string() +
    ")，dim = 2^" +
    n.to_string(),
    dim: d,
    zero: arr_zeros(d),
    add: (a, b) => arr_add(a, b),
    neg: a => arr_neg(a),
    smul: (c, a) => arr_scale(c, a),
    veq: (a, b) => arr_eq(a, b),
    basis: Array::makei(d, i => arr_e(d, i)),
    coord: a => a.copy(),
    expand: c => c.copy(),
    vshow: a => {
      let mut s = ""
      let mut first = true
      for i in 0..<d {
        if !F::s_is_zero(a[i]) {
          if !first {
            s = s + " + "
          }
          s = s + F::s_text(a[i]) + "·" + labels[i]
          first = false
        }
      }
      if first {
        "0"
      } else {
        s
      }
    },
    sample: rng => Array::makei(d, _ => F::s_rand(rng)),
  }
  {
    vs,
    ipname: "⟨e_I,e_J⟩ = δ_IJ（分次正交）",
    inner: (a, b) => arr_dot(a, b),
  }
}

///|
/// 全外代數中之楔積（以遮罩索引）
pub fn[F : Scalar] wedge_full(n : Int, a : Array[F], b : Array[F]) -> Array[F] {
  let d = 1 << n
  let out = arr_zeros(d)
  for x in 0..<d {
    if F::s_is_zero(a[x]) {
      continue
    }
    for y in 0..<d {
      if F::s_is_zero(b[y]) {
        continue
      }
      if (x & y) != 0 {
        continue
      }
      let ix : Array[Int] = []
      let jy : Array[Int] = []
      for i in 0..<n {
        if (x & (1 << i)) != 0 {
          ix.push(i)
        }
        if (y & (1 << i)) != 0 {
          jy.push(i)
        }
      }
      let sg = merge_sign(ix, jy)
      let term = F::s_mul(a[x], b[y])
      let signed = if sg > 0 { term } else { F::s_neg(term) }
      out[x | y] = F::s_add(out[x | y], signed)
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 【演算法 052】三維叉積 a × b = ⋆(a ∧ b)
// ---------------------------------------------------------------------------

///|
/// ℝ³ 叉積：即楔積之 Riesz 對偶（⋆(a∧b)）。
pub fn[F : Scalar] cross3(a : Array[F], b : Array[F]) -> Array[F] {
  let w = wedge(3, 1, 1, a, b)
  hodge_star(3, 2, w)
}

// ---------------------------------------------------------------------------
// 【演算法 053】n 維「廣義叉積」：n−1 個向量之 Hodge 補
//   x = ⋆(v₁ ∧ … ∧ v_{n−1})，滿足 ⟨x, vᵢ⟩ = 0 且 ‖x‖ = (n−1)‑體積。
// ---------------------------------------------------------------------------

///|
/// 廣義叉積：n 個向量楔積後取 Hodge 對偶，得 ℝⁿ 之一向量。
pub fn[F : Scalar] generalized_cross(n : Int, vs : Array[Array[F]]) -> Array[F] {
  let w = wedge_vectors(n, vs)
  hodge_star(n, n - 1, w)
}

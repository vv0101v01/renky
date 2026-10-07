// ============================================================================
//  檔案 09：mpolyspace.mbt — 多變量多項式空間 𝔽[x₁,…,x_m]_{≤d}
//    S14 多變量多項式空間，Bombieri–Weyl（apolar）內積
//    S15 同上，但用單項式正交內積（係數內積）
// ============================================================================
//
// 【定義 MP】𝔽[x₁,…,x_m]_{≤d} ≔ span{x^α : |α| ≤ d}，
//   dim = C(m+d, d)（組合計數：把 d 顆球放進 m+1 個盒）。
// 【定義 BW】Bombieri–Weyl 內積：⟨x^α, x^β⟩ ≔ δ_{αβ}·α!/|α|!，α! = Παᵢ!。
// 【命題 BW1】正定（對角且對角元 > 0）⇒ 內積公理 I1–I5 全部滿足。
// 【命題 BW2】（么正不變性，Weyl）限制於 d 次齊次部分時，
//   ⟨·,·⟩_BW 於變數之么正替換下不變：⟨f∘U, g∘U⟩ = ⟨f,g⟩ ∀U ∈ U(m)。
//   這正是 Bombieri 範數在代數幾何／多項式系統數值解中成為標準之原因。
// 【命題 BW3】(f·g 之 BW 範數) 滿足 Bombieri 不等式 ‖fg‖ ≥ ‖f‖‖g‖·(…)，
//   本實作僅驗證 I1–I5 與么正不變性之有限實例。
// ============================================================================

///|
/// 單項（指數向量 + 係數）
pub struct Term[F] {
  expo : Array[Int]
  tc : F
}

///|
/// 多變量多項式（稀疏表示，指數向量按 graded-lex 排序且已合併）
pub struct MPoly[F] {
  nvars : Int
  terms : Array[Term[F]]
}

///|
/// graded-lex 比較：先比總次數，再字典序
pub fn grlex_cmp(a : Array[Int], b : Array[Int]) -> Int {
  let mut sa = 0
  let mut sb = 0
  for x in a {
    sa = sa + x
  }
  for x in b {
    sb = sb + x
  }
  if sa != sb {
    return if sa < sb { -1 } else { 1 }
  }
  for i in 0..<a.length() {
    if a[i] != b[i] {
      return if a[i] < b[i] { -1 } else { 1 }
    }
  }
  0
}

///|
/// 以插入排序整理並合併同類項（Θ(t²)，t = 項數；穩定且無第三方依賴）
pub fn[F : Scalar] mp_normalize(m : Int, ts : Array[Term[F]]) -> MPoly[F] {
  let sorted : Array[Term[F]] = []
  for t in ts {
    let mut pos = sorted.length()
    for i in 0..<sorted.length() {
      if grlex_cmp(t.expo, sorted[i].expo) < 0 {
        pos = i
        break
      }
    }
    sorted.insert(pos, t)
  }
  let out : Array[Term[F]] = []
  for t in sorted {
    if out.length() > 0 && grlex_cmp(out[out.length() - 1].expo, t.expo) == 0 {
      let last = out[out.length() - 1]
      out[out.length() - 1] = { expo: last.expo, tc: F::s_add(last.tc, t.tc), }
    } else {
      out.push(t)
    }
  }
  let kept : Array[Term[F]] = []
  for t in out {
    if !F::s_is_zero(t.tc) {
      kept.push(t)
    }
  }
  { nvars: m, terms: kept, }
}

///|
/// f + g
pub fn[F : Scalar] MPoly::mpadd(self : MPoly[F], o : MPoly[F]) -> MPoly[F] {
  let all : Array[Term[F]] = []
  for t in self.terms {
    all.push(t)
  }
  for t in o.terms {
    all.push(t)
  }
  mp_normalize(self.nvars, all)
}

///|
/// c·f
pub fn[F : Scalar] MPoly::mpscale(self : MPoly[F], c : F) -> MPoly[F] {
  let all : Array[Term[F]] = []
  for t in self.terms {
    all.push({ expo: t.expo, tc: F::s_mul(c, t.tc), })
  }
  mp_normalize(self.nvars, all)
}

///|
/// −f
pub fn[F : Scalar] MPoly::mpneg(self : MPoly[F]) -> MPoly[F] {
  self.mpscale(F::s_neg(F::s_one()))
}

// ---------------------------------------------------------------------------
// 【演算法 042】多變量多項式乘法（指數向量相加 + 合併）
// 命題 042：𝔽[x₁..x_m] 為交換整環；deg(fg) = deg f + deg g。
// ---------------------------------------------------------------------------

///|
/// 多變量多項式乘法（逐項相乘後合併同類項）。
pub fn[F : Scalar] MPoly::mpmul(self : MPoly[F], o : MPoly[F]) -> MPoly[F] {
  let all : Array[Term[F]] = []
  for a in self.terms {
    for b in o.terms {
      let e = Array::makei(self.nvars, i => a.expo[i] + b.expo[i])
      all.push({ expo: e, tc: F::s_mul(a.tc, b.tc), })
    }
  }
  mp_normalize(self.nvars, all)
}

// ---------------------------------------------------------------------------
// 【演算法 043】多變量求值 f(ξ) = Σ c_α Π ξᵢ^{αᵢ}
// ---------------------------------------------------------------------------

///|
/// 多變量求值：x 依變數序給值。
pub fn[F : Scalar] MPoly::mpeval(self : MPoly[F], x : Array[F]) -> F {
  let mut acc = F::s_zero()
  for t in self.terms {
    let mut p = t.tc
    for i in 0..<self.nvars {
      p = F::s_mul(p, spow(x[i], t.expo[i]))
    }
    acc = F::s_add(acc, p)
  }
  acc
}

///|
/// 總次數
pub fn[F] MPoly::mpdeg(self : MPoly[F]) -> Int {
  let mut d = -1
  for t in self.terms {
    let mut s = 0
    for e in t.expo {
      s = s + e
    }
    if s > d {
      d = s
    }
  }
  d
}

///|
/// 結構相等判定（含係數相等與項序正規化）。
pub fn[F : Scalar] MPoly::mpeq(self : MPoly[F], o : MPoly[F]) -> Bool {
  let a = mp_normalize(self.nvars, self.terms)
  let b = mp_normalize(o.nvars, o.terms)
  if a.terms.length() != b.terms.length() {
    return false
  }
  for i in 0..<a.terms.length() {
    if grlex_cmp(a.terms[i].expo, b.terms[i].expo) != 0 {
      return false
    }
    if !F::s_eq(a.terms[i].tc, b.terms[i].tc) {
      return false
    }
  }
  true
}

///|
/// 文字輸出（單項式列表形式）。
pub fn[F : Scalar] MPoly::text(self : MPoly[F]) -> String {
  if self.terms.length() == 0 {
    return "0"
  }
  let mut s = ""
  for k in 0..<self.terms.length() {
    let t = self.terms[k]
    if k > 0 {
      s = s + " + "
    }
    s = s + F::s_text(t.tc)
    for i in 0..<self.nvars {
      if t.expo[i] > 0 {
        s = s + "·x" + (i + 1).to_string()
        if t.expo[i] > 1 {
          s = s + "^" + t.expo[i].to_string()
        }
      }
    }
  }
  s
}

// ---------------------------------------------------------------------------
// 【演算法 044】列舉總次數 ≤ d 之單項式（graded-lex）
// 命題 044：|{α ∈ ℕ^m : |α| ≤ d}| = C(m+d, d)（星與條定理）。
// ---------------------------------------------------------------------------

///|
/// 次數 ≤ d 之 m 變數單項式指數表（遞迴枚舉，共 C(m+d, d) 個）。
pub fn monomials_upto(m : Int, d : Int) -> Array[Array[Int]] {
  let out : Array[Array[Int]] = []
  let cur = Array::make(m, 0)
  fn rec(pos : Int, left : Int) -> Unit {
    if pos == m {
      out.push(cur.copy())
      return
    }
    for e in 0..<(left + 1) {
      cur[pos] = e
      rec(pos + 1, left - e)
    }
    cur[pos] = 0
  }

  rec(0, d)
  // 依 graded-lex 排序（插入排序）
  let sorted : Array[Array[Int]] = []
  for a in out {
    let mut pos = sorted.length()
    for i in 0..<sorted.length() {
      if grlex_cmp(a, sorted[i]) < 0 {
        pos = i
        break
      }
    }
    sorted.insert(pos, a)
  }
  sorted
}

///|
/// n! （小 n）
pub fn fact_i(n : Int) -> Int64 {
  let mut acc = 1L
  for i in 1..<(n + 1) {
    acc = acc * i.to_int64()
  }
  acc
}

///|
/// 二項式係數 C(n,k)（Pascal 遞推，避免溢位）
pub fn binom_i(n : Int, k : Int) -> Int64 {
  if k < 0 || k > n {
    return 0L
  }
  let mut acc = 1L
  for i in 0..<k {
    acc = acc * (n - i).to_int64() / (i + 1).to_int64()
  }
  acc
}

///|
/// 【空間 S14/S15】多變量多項式空間。
/// bombieri = true  ⇒ ⟨x^α,x^β⟩ = δ_{αβ}·α!/|α|!（Bombieri–Weyl）
/// bombieri = false ⇒ ⟨x^α,x^β⟩ = δ_{αβ}（係數內積）
pub fn[F : Scalar] mpoly_space(
  m : Int,
  d : Int,
  bombieri : Bool,
) -> IPSpace[MPoly[F], F] {
  let monos = monomials_upto(m, d)
  let n = monos.length()
  let weight = Array::makei(n, k => {
    if !bombieri {
      return F::s_one()
    }
    let a = monos[k]
    let mut tot = 0
    let mut num = 1L
    for e in a {
      tot = tot + e
      num = num * fact_i(e)
    }
    let den = fact_i(tot)
    F::s_from_frac(num.to_int(), den.to_int())
  })
  let idx_of = (e : Array[Int]) => {
    let mut r = -1
    for i in 0..<n {
      if grlex_cmp(monos[i], e) == 0 {
        r = i
        break
      }
    }
    r
  }
  let expand_f = (c : Array[F]) => {
    let ts : Array[Term[F]] = []
    for i in 0..<n {
      if !F::s_is_zero(c[i]) {
        ts.push({ expo: monos[i].copy(), tc: c[i], })
      }
    }
    mp_normalize(m, ts)
  }
  let coord_f = (f : MPoly[F]) => {
    let c = arr_zeros(n)
    for t in f.terms {
      let i = idx_of(t.expo)
      if i >= 0 {
        c[i] = F::s_add(c[i], t.tc)
      }
    }
    c
  }
  let vs = VSpace::{
    vname: F::s_name() +
    "[x₁..x" +
    m.to_string() +
    "]_{≤" +
    d.to_string() +
    "}",
    dim: n,
    zero: { nvars: m, terms: [], },
    add: (a, b) => a.mpadd(b),
    neg: a => a.mpneg(),
    smul: (c, a) => a.mpscale(c),
    veq: (a, b) => a.mpeq(b),
    basis: Array::makei(n, i => {
      nvars: m,
      terms: [{ expo: monos[i].copy(), tc: F::s_one(), }],
    }),
    coord: f => coord_f(f),
    expand: c => expand_f(c),
    vshow: f => f.text(),
    sample: rng => expand_f(Array::makei(n, _ => F::s_rand(rng))),
  }
  {
    vs,
    ipname: if bombieri {
      "⟨x^α,x^β⟩ = δ_{αβ}·α!/|α|!（Bombieri–Weyl）"
    } else {
      "⟨x^α,x^β⟩ = δ_{αβ}（係數內積）"
    },
    inner: (f, g) => {
      let cf = coord_f(f)
      let cg = coord_f(g)
      let mut acc = F::s_zero()
      for i in 0..<n {
        acc = F::s_add(
          acc,
          F::s_mul(weight[i], F::s_mul(cf[i], F::s_conj(cg[i]))),
        )
      }
      acc
    },
  }
}

///|
/// 線性替換 f ↦ f∘A（A 為 m×m 矩陣，xᵢ ↦ Σ_j a_{ij} x_j）
/// 用於驗證 Bombieri 內積之么正不變性（命題 BW2）。
pub fn[F : Scalar] mpoly_subst(f : MPoly[F], a : Mat[F]) -> MPoly[F] {
  let m = f.nvars
  // 預先造出 yᵢ = Σ_j a_{ij} x_j
  let ys : Array[MPoly[F]] = Array::makei(m, i => {
    let ts : Array[Term[F]] = []
    for j in 0..<m {
      let e = Array::make(m, 0)
      e[j] = 1
      ts.push({ expo: e, tc: a.at(i, j), })
    }
    mp_normalize(m, ts)
  })
  let one : MPoly[F] = mp_normalize(m, [
    { expo: Array::make(m, 0), tc: F::s_one(), },
  ])
  let mut acc = MPoly::{ nvars: m, terms: [], }
  for t in f.terms {
    let mut p = one
    for i in 0..<m {
      for _k in 0..<t.expo[i] {
        p = p.mpmul(ys[i])
      }
    }
    acc = acc.mpadd(p.mpscale(t.tc))
  }
  acc
}

///| （隔離標記）本函式全專案未被呼叫，但依賴本套件私有內部，故留在原處。

///|
/// 由指數向量與係數造多項式（方便測試）
pub fn[F : Scalar] mpoly_of(
  m : Int,
  items : Array[(Array[Int], F)],
) -> MPoly[F] {
  let ts : Array[Term[F]] = []
  for it in items {
    ts.push({ expo: it.0, tc: it.1, })
  }
  mp_normalize(m, ts)
}

// ============================================================================
//  檔案 05：matrix.mbt — 體 𝔽 上之矩陣與精確線性代數演算法
// ============================================================================
//
// 【定義 M】M_{m×n}(𝔽) ≔ 𝔽^{m×n}，以列優先 (row-major) 一維陣列表示：
//   A[i][j] = a[i·n + j]。(M_{m×n}(𝔽), +, ·) 本身即 mn 維向量空間。
// 【命題 M1】矩陣乘法結合律 (AB)C = A(BC)，分配律，與轉置反序 (AB)ᵀ = BᵀAᵀ、
//   共軛轉置 (AB)* = B*A*。證明：逐元素展開 Σ_k Σ_l a_{ik}b_{kl}c_{lj} 之
//   求和次序交換（有限和，體之結合交換律）。∎
// ============================================================================

///|
/// m×n 矩陣（列優先）。
pub struct Mat[F] {
  mrows : Int
  mcols : Int
  data : Array[F]
}

///|
/// 由 (i,j) ↦ f(i,j) 造矩陣。
pub fn[F] Mat::build(r : Int, c : Int, f : (Int, Int) -> F) -> Mat[F] {
  { mrows: r, mcols: c, data: Array::makei(r * c, k => f(k / c, k % c)), }
}

///|
/// 零矩陣
pub fn[F : Scalar] Mat::zeros(r : Int, c : Int) -> Mat[F] {
  Mat::build(r, c, (_i, _j) => F::s_zero())
}

///|
/// 單位矩陣 I_n
pub fn[F : Scalar] Mat::ident(n : Int) -> Mat[F] {
  Mat::build(n, n, (i, j) => if i == j { F::s_one() } else { F::s_zero() })
}

///|
/// 由列陣列造矩陣
pub fn[F] Mat::of_rows(rows : Array[Array[F]]) -> Mat[F] {
  let r = rows.length()
  let c = if r == 0 { 0 } else { rows[0].length() }
  Mat::build(r, c, (i, j) => rows[i][j])
}

///|
/// 由行向量陣列造矩陣（每個 Array[F] 為一行）
pub fn[F] Mat::of_cols(cols : Array[Array[F]]) -> Mat[F] {
  let c = cols.length()
  let r = if c == 0 { 0 } else { cols[0].length() }
  Mat::build(r, c, (i, j) => cols[j][i])
}

///|
/// 對角矩陣 diag(d)
pub fn[F : Scalar] Mat::diagm(d : Array[F]) -> Mat[F] {
  let n = d.length()
  Mat::build(n, n, (i, j) => if i == j { d[i] } else { F::s_zero() })
}

///|
/// 讀元素 A[i][j]
pub fn[F] Mat::at(self : Mat[F], i : Int, j : Int) -> F {
  self.data[i * self.mcols + j]
}

///|
/// 寫元素 A[i][j] ← v
pub fn[F] Mat::put(self : Mat[F], i : Int, j : Int, v : F) -> Unit {
  self.data[i * self.mcols + j] = v
}

///|
/// 第 i 列
pub fn[F] Mat::row(self : Mat[F], i : Int) -> Array[F] {
  Array::makei(self.mcols, j => self.data[i * self.mcols + j])
}

///|
/// 第 j 行
pub fn[F] Mat::col(self : Mat[F], j : Int) -> Array[F] {
  Array::makei(self.mrows, i => self.data[i * self.mcols + j])
}

///|
/// 深拷貝
pub fn[F] Mat::clone(self : Mat[F]) -> Mat[F] {
  { mrows: self.mrows, mcols: self.mcols, data: self.data.copy(), }
}

///|
/// A + B
pub fn[F : Scalar] Mat::plus(self : Mat[F], o : Mat[F]) -> Mat[F] {
  Mat::build(self.mrows, self.mcols, (i, j) => {
    F::s_add(self.at(i, j), o.at(i, j))
  })
}

///|
/// A − B
pub fn[F : Scalar] Mat::minus(self : Mat[F], o : Mat[F]) -> Mat[F] {
  Mat::build(self.mrows, self.mcols, (i, j) => ssub(self.at(i, j), o.at(i, j)))
}

///|
/// −A
pub fn[F : Scalar] Mat::negm(self : Mat[F]) -> Mat[F] {
  Mat::build(self.mrows, self.mcols, (i, j) => F::s_neg(self.at(i, j)))
}

///|
/// c·A
pub fn[F : Scalar] Mat::scale(self : Mat[F], c : F) -> Mat[F] {
  Mat::build(self.mrows, self.mcols, (i, j) => F::s_mul(c, self.at(i, j)))
}

// ---------------------------------------------------------------------------
// 【演算法 011】矩陣乘法 C = AB，c_{ij} = Σ_k a_{ik} b_{kj}（Θ(mnp)）
// 命題 011：結合律與分配律；單位元 I。見命題 M1。
// ---------------------------------------------------------------------------

///|
/// A·B
pub fn[F : Scalar] Mat::times(self : Mat[F], o : Mat[F]) -> Mat[F] {
  let m = self.mrows
  let n = o.mcols
  let k = self.mcols
  Mat::build(m, n, (i, j) => {
    let mut acc = F::s_zero()
    for t in 0..<k {
      acc = F::s_add(acc, F::s_mul(self.at(i, t), o.at(t, j)))
    }
    acc
  })
}

///|
/// A·x（矩陣作用於行向量）
pub fn[F : Scalar] Mat::apply(self : Mat[F], x : Array[F]) -> Array[F] {
  Array::makei(self.mrows, i => {
    let mut acc = F::s_zero()
    for j in 0..<self.mcols {
      acc = F::s_add(acc, F::s_mul(self.at(i, j), x[j]))
    }
    acc
  })
}

// ---------------------------------------------------------------------------
// 【演算法 012】轉置 Aᵀ 與共軛轉置 A* = ‾Aᵀ
// 命題 012：(AB)* = B*A*；⟨Ax, y⟩ = ⟨x, A*y⟩（A* 為 A 之伴隨，見定理 T‑ADJ）。
// ---------------------------------------------------------------------------

///|
/// Aᵀ
pub fn[F] Mat::transpose(self : Mat[F]) -> Mat[F] {
  Mat::build(self.mcols, self.mrows, (i, j) => self.at(j, i))
}

///|
/// A* = ‾Aᵀ
pub fn[F : Scalar] Mat::adjointm(self : Mat[F]) -> Mat[F] {
  Mat::build(self.mcols, self.mrows, (i, j) => F::s_conj(self.at(j, i)))
}

///|
/// 逐元素共軛 ‾A
pub fn[F : Scalar] Mat::conjm(self : Mat[F]) -> Mat[F] {
  Mat::build(self.mrows, self.mcols, (i, j) => F::s_conj(self.at(i, j)))
}

///|
/// tr A = Σ a_{ii}
pub fn[F : Scalar] Mat::trace(self : Mat[F]) -> F {
  let n = if self.mrows < self.mcols { self.mrows } else { self.mcols }
  let mut acc = F::s_zero()
  for i in 0..<n {
    acc = F::s_add(acc, self.at(i, i))
  }
  acc
}

///|
/// 逐元素相等
pub fn[F : Scalar] Mat::equals(self : Mat[F], o : Mat[F]) -> Bool {
  if self.mrows != o.mrows || self.mcols != o.mcols {
    return false
  }
  for i in 0..<self.data.length() {
    if !F::s_eq(self.data[i], o.data[i]) {
      return false
    }
  }
  true
}

///|
/// 最大逐元素偏差 max|a_{ij} − b_{ij}|（數值軌道之殘差憑證）
pub fn[F : Scalar] Mat::max_dev(self : Mat[F], o : Mat[F]) -> Double {
  let mut m = 0.0
  for i in 0..<self.data.length() {
    m = maxd(m, F::s_mag(ssub(self.data[i], o.data[i])))
  }
  m
}

///|
/// Frobenius 範數平方 ‖A‖_F² = Σ|a_{ij}|²
pub fn[F : Scalar] Mat::frob2(self : Mat[F]) -> Double {
  let mut s = 0.0
  for x in self.data {
    let m = F::s_mag(x)
    s = s + m * m
  }
  s
}

///|
/// 列印
pub fn[F : Scalar] Mat::text(self : Mat[F]) -> String {
  let mut s = ""
  for i in 0..<self.mrows {
    s = s + "["
    for j in 0..<self.mcols {
      s = s + F::s_text(self.at(i, j))
      if j + 1 < self.mcols {
        s = s + ", "
      }
    }
    s = s + "]"
    if i + 1 < self.mrows {
      s = s + " "
    }
  }
  s
}

///|
/// 水平併接 [A | B]
pub fn[F] Mat::hcat(self : Mat[F], o : Mat[F]) -> Mat[F] {
  Mat::build(self.mrows, self.mcols + o.mcols, (i, j) => {
    if j < self.mcols {
      self.at(i, j)
    } else {
      o.at(i, j - self.mcols)
    }
  })
}

///|
/// 垂直併接 [A ; B]
pub fn[F] Mat::vcat(self : Mat[F], o : Mat[F]) -> Mat[F] {
  Mat::build(self.mrows + o.mrows, self.mcols, (i, j) => {
    if i < self.mrows {
      self.at(i, j)
    } else {
      o.at(i - self.mrows, j)
    }
  })
}

///|
/// 子矩陣 A[r0..r1) × [c0..c1)
pub fn[F] Mat::sub(
  self : Mat[F],
  r0 : Int,
  r1 : Int,
  c0 : Int,
  c1 : Int,
) -> Mat[F] {
  Mat::build(r1 - r0, c1 - c0, (i, j) => self.at(r0 + i, c0 + j))
}

///|
/// 刪去第 i 列第 j 行之子矩陣（餘子式用）
pub fn[F] Mat::minor_mat(self : Mat[F], di : Int, dj : Int) -> Mat[F] {
  Mat::build(self.mrows - 1, self.mcols - 1, (i, j) => {
    let si = if i < di { i } else { i + 1 }
    let sj = if j < dj { j } else { j + 1 }
    self.at(si, sj)
  })
}

// ---------------------------------------------------------------------------
// 【演算法 013】Gauss–Jordan 消去 → 列化簡階梯形 (RREF)
//
// 命題 013（正確性）：輸出 R 為 RREF 且存在可逆 E 使 R = EA；
//   列空間 row(A) = row(R)，零空間 ker(A) = ker(R)，rank = 主元數。
// 迴圈不變量 I(k)：處理完前 k 行後，(1) 前 r 列之主元位於遞增行且為 1；
//   (2) 主元所在行之其餘元素皆 0；(3) 已施行之列運算皆可逆（換列、乘非零純量、
//   加倍數）⇒ 存在可逆 E_k 使當前矩陣 = E_k A。
// 證明：三類初等列運算對應可逆初等矩陣，其積可逆；歸納 k。∎
// 樞軸策略：取 |a| 最大者（數值軌道之後向穩定性；精確軌道不影響結果）。
// ---------------------------------------------------------------------------

///|
/// RREF 之輸出包。
pub struct Rref[F] {
  /// 化簡列階梯形 R
  rmat : Mat[F]
  /// rank A
  rank : Int
  /// 主元所在之行索引
  pivots : Array[Int]
  /// 列運算所乘之純量積（det A = sign·pivprod，見演算法 015）
  pivprod : F
  /// 換列次數之奇偶
  sign : Int
}

///|
/// 高斯–若爾當消去。
pub fn[F : Scalar] mrref(m : Mat[F]) -> Rref[F] {
  let a = m.clone()
  let rows = a.mrows
  let cols = a.mcols
  let pivots : Array[Int] = []
  let mut r = 0
  let mut sign = 1
  let mut pivprod = F::s_one()
  for c in 0..<cols {
    if r >= rows {
      break
    }
    // 選樞軸：|a[i][c]| 最大且非零
    let mut best = -1
    let mut bestmag = 0.0
    for i in r..<rows {
      let v = a.at(i, c)
      if !F::s_is_zero(v) {
        let mg = F::s_mag(v)
        if best < 0 || mg > bestmag {
          best = i
          bestmag = mg
        }
      }
    }
    if best < 0 {
      continue
    }
    if best != r {
      for j in 0..<cols {
        let t = a.at(r, j)
        a.put(r, j, a.at(best, j))
        a.put(best, j, t)
      }
      sign = -sign
    }
    let p = a.at(r, c)
    pivprod = F::s_mul(pivprod, p)
    let pinv = match F::s_inv(p) {
      Some(x) => x
      None => F::s_one()
    }
    for j in 0..<cols {
      a.put(r, j, F::s_mul(pinv, a.at(r, j)))
    }
    for i in 0..<rows {
      if i != r {
        let f = a.at(i, c)
        if !F::s_is_zero(f) {
          for j in 0..<cols {
            a.put(i, j, ssub(a.at(i, j), F::s_mul(f, a.at(r, j))))
          }
        }
      }
    }
    pivots.push(c)
    r = r + 1
  }
  { rmat: a, rank: r, pivots, pivprod, sign, }
}

// ---------------------------------------------------------------------------
// 【演算法 014】秩 rank A
// 命題 014（秩–零化度定理）：rank A + dim ker A = n（行數）。
// 證明：RREF 中每個主元行對應一個領導變數，每個自由行對應一個零空間基向量；
//   兩者之和為行數，且兩組向量分別線性獨立並生成對應空間。∎
// ---------------------------------------------------------------------------

///|
/// 矩陣秩：消去法之非零列數（精確軌道上為真秩）。
pub fn[F : Scalar] mrank(m : Mat[F]) -> Int {
  mrref(m).rank
}

// ---------------------------------------------------------------------------
// 【演算法 015】行列式（消去法，Θ(n³)）
// 定義：det A = Σ_{σ∈S_n} sgn(σ) Π a_{i,σ(i)}（Leibniz）。
// 命題 015：det A = sign · Π(樞軸)，其中 sign 為換列次數之奇偶符號。
// 證明：det 為交錯多重線性形式；換列變號、列乘 c 則 det 乘 c、
//   列加他列倍數不變；RREF 過程把 A 化為 I（滿秩時），逆推即得。∎
// ---------------------------------------------------------------------------

///|
/// det A（非方陣回 0）
pub fn[F : Scalar] mdet(m : Mat[F]) -> F {
  if m.mrows != m.mcols {
    return F::s_zero()
  }
  let rr = mrref(m)
  if rr.rank < m.mrows {
    return F::s_zero()
  }
  let s = rr.pivprod
  if rr.sign < 0 {
    F::s_neg(s)
  } else {
    s
  }
}

// ---------------------------------------------------------------------------
// 【演算法 016】Laplace 餘因子展開求行列式（獨立交叉驗證用，Θ(n!)）
// 命題 016：det A = Σ_j (−1)^{i+j} a_{ij} M_{ij}（沿第 i 列展開）。
// 兩種演算法（015 與 016）之一致性即為「交叉驗證型證明義務」。
// ---------------------------------------------------------------------------

///|
/// 行列式：Laplace 展開（小尺寸對照用）。
pub fn[F : Scalar] mdet_laplace(m : Mat[F]) -> F {
  let n = m.mrows
  if n == 0 {
    return F::s_one()
  }
  if n == 1 {
    return m.at(0, 0)
  }
  if n == 2 {
    return ssub(
      F::s_mul(m.at(0, 0), m.at(1, 1)),
      F::s_mul(m.at(0, 1), m.at(1, 0)),
    )
  }
  let mut acc = F::s_zero()
  for j in 0..<n {
    let c = m.at(0, j)
    if !F::s_is_zero(c) {
      let sub = m.minor_mat(0, j)
      let d = F::s_mul(c, mdet_laplace(sub))
      acc = if j % 2 == 0 { F::s_add(acc, d) } else { ssub(acc, d) }
    }
  }
  acc
}

// ---------------------------------------------------------------------------
// 【演算法 017】反矩陣（Gauss–Jordan，[A|I] → [I|A⁻¹]）
// 命題 017：A 可逆 ⟺ rank A = n；此時 A⁻¹ 唯一且 AA⁻¹ = A⁻¹A = I。
// ---------------------------------------------------------------------------

///|
/// 反矩陣：高斯–若爾當；奇異時回 None（體公理 F2 之部分函數化）。
pub fn[F : Scalar] minv(m : Mat[F]) -> Mat[F]? {
  if m.mrows != m.mcols {
    return None
  }
  let n = m.mrows
  let aug = m.hcat(Mat::ident(n))
  let rr = mrref(aug)
  if rr.rank < n {
    return None
  }
  Some(rr.rmat.sub(0, n, n, 2 * n))
}

// ---------------------------------------------------------------------------
// 【演算法 018】線性方程組 Ax = b（通解 = 特解 + 零空間）
// 命題 018（Rouché–Capelli）：Ax = b 有解 ⟺ rank A = rank [A|b]。
// ---------------------------------------------------------------------------

///|
/// 線性系統之解集描述。
pub struct SolSet[F] {
  /// 是否相容
  solvable : Bool
  /// 特解（不相容時為零向量）
  particular : Array[F]
  /// 零空間基底（自由度）
  nullbasis : Array[Array[F]]
}

///|
/// 解 Ax = b
pub fn[F : Scalar] msolve(a : Mat[F], b : Array[F]) -> SolSet[F] {
  let m = a.mrows
  let n = a.mcols
  let aug = Mat::build(m, n + 1, (i, j) => if j < n { a.at(i, j) } else { b[i] })
  let rr = mrref(aug)
  // 不相容 ⟺ 存在主元落在最後一行
  for p in rr.pivots {
    if p == n {
      return {
        solvable: false,
        particular: Array::makei(n, _ => F::s_zero()),
        nullbasis: [],
      }
    }
  }
  let x = Array::makei(n, _ => F::s_zero())
  for k in 0..<rr.pivots.length() {
    x[rr.pivots[k]] = rr.rmat.at(k, n)
  }
  { solvable: true, particular: x, nullbasis: mnullspace(a), }
}

// ---------------------------------------------------------------------------
// 【演算法 019】零空間基底 ker A
// 命題 019：自由行 j 對應之向量 v^{(j)}（v_j = 1，主元分量 = −R[k][j]）
//   構成 ker A 之基底，故 dim ker A = n − rank A（秩–零化度定理）。
// ---------------------------------------------------------------------------

///|
/// 核空間基底：解 Ax = 0 之自由變數向量集。
pub fn[F : Scalar] mnullspace(a : Mat[F]) -> Array[Array[F]] {
  let n = a.mcols
  let rr = mrref(a)
  let is_pivot = Array::make(n, false)
  for p in rr.pivots {
    is_pivot[p] = true
  }
  let basis : Array[Array[F]] = []
  for j in 0..<n {
    if !is_pivot[j] {
      let v = Array::makei(n, _ => F::s_zero())
      v[j] = F::s_one()
      for k in 0..<rr.pivots.length() {
        v[rr.pivots[k]] = F::s_neg(rr.rmat.at(k, j))
      }
      basis.push(v)
    }
  }
  basis
}

// ---------------------------------------------------------------------------
// 【演算法 020】行空間 (column space / 像) 基底：主元行
// 命題 020：A 之主元行構成 im A 之基底；dim im A = rank A。
// 【演算法 021】列空間 (row space) 基底：RREF 之非零列
// 命題 021：row(A) = row(RREF(A))，非零列線性獨立。
//   推論（四基本子空間，Strang）：
//     im(A) ⊥ ker(Aᵀ) 於 𝔽^m，   row(A) ⊥ ker(A) 於 𝔽ⁿ，
//     dim im A = dim row A = rank A。
// ---------------------------------------------------------------------------

///|
/// 行空間基底（取原矩陣之主元行）
pub fn[F : Scalar] mcolspace(a : Mat[F]) -> Array[Array[F]] {
  let rr = mrref(a)
  let out : Array[Array[F]] = []
  for p in rr.pivots {
    out.push(a.col(p))
  }
  out
}

///|
/// 列空間基底（RREF 之非零列）
pub fn[F : Scalar] mrowspace(a : Mat[F]) -> Array[Array[F]] {
  let rr = mrref(a)
  let out : Array[Array[F]] = []
  for i in 0..<rr.rank {
    out.push(rr.rmat.row(i))
  }
  out
}

// ---------------------------------------------------------------------------
// 【演算法 022】LU 分解（部分樞軸：PA = LU）
// 命題 022：任意方陣存在置換 P 使 PA = LU，L 單位下三角、U 上三角。
// 證明：對 n 歸納；若第一行全零則 U 第一行為零、取 L 之第一行為 e₁；
//   否則選最大元換到 (1,1)，消去後對 (n−1)×(n−1) 子塊用歸納假設。∎
// 推論：det A = (−1)^{#swap} Π u_{ii}。
// ---------------------------------------------------------------------------

///|
/// LU 分解結果（PA = LU）
pub struct LU[F] {
  lmat : Mat[F]
  umat : Mat[F]
  perm : Array[Int]
  swaps : Int
  singular : Bool
}

///|
/// LU 分解（部分主元）：回 L、U 與置換。
pub fn[F : Scalar] mlu(a0 : Mat[F]) -> LU[F] {
  let n = a0.mrows
  let u = a0.clone()
  let l : Mat[F] = Mat::ident(n)
  let perm = Array::makei(n, i => i)
  let mut swaps = 0
  let mut singular = false
  for k in 0..<n {
    let mut best = -1
    let mut bm = 0.0
    for i in k..<n {
      let v = u.at(i, k)
      if !F::s_is_zero(v) {
        let mg = F::s_mag(v)
        if best < 0 || mg > bm {
          best = i
          bm = mg
        }
      }
    }
    if best < 0 {
      singular = true
      continue
    }
    if best != k {
      for j in 0..<n {
        let t = u.at(k, j)
        u.put(k, j, u.at(best, j))
        u.put(best, j, t)
      }
      for j in 0..<k {
        let t = l.at(k, j)
        l.put(k, j, l.at(best, j))
        l.put(best, j, t)
      }
      let t = perm[k]
      perm[k] = perm[best]
      perm[best] = t
      swaps = swaps + 1
    }
    let p = u.at(k, k)
    let pinv = match F::s_inv(p) {
      Some(x) => x
      None => F::s_one()
    }
    for i in (k + 1)..<n {
      let f = F::s_mul(u.at(i, k), pinv)
      l.put(i, k, f)
      if !F::s_is_zero(f) {
        for j in k..<n {
          u.put(i, j, ssub(u.at(i, j), F::s_mul(f, u.at(k, j))))
        }
      } else {
        u.put(i, k, F::s_zero())
      }
    }
  }
  { lmat: l, umat: u, perm, swaps, singular, }
}

///|
/// 置換矩陣 P（由 perm 造出，使 PA = LU）
pub fn[F : Scalar] perm_matrix(perm : Array[Int]) -> Mat[F] {
  let n = perm.length()
  Mat::build(n, n, (i, j) => if perm[i] == j { F::s_one() } else { F::s_zero() })
}

// ---------------------------------------------------------------------------
// 【演算法 023】Kronecker 積 A ⊗ B
// 定義：(A⊗B)_{(i,k),(j,l)} = a_{ij} b_{kl}，尺寸 (m_A m_B) × (n_A n_B)。
// 命題 023（混合積律）：(A⊗B)(C⊗D) = (AC)⊗(BD)；(A⊗B)* = A*⊗B*；
//   tr(A⊗B) = tr A · tr B；det(A⊗B) = (det A)^{n_B}(det B)^{n_A}。
// ---------------------------------------------------------------------------

///|
/// Kronecker 積 A ⊗ B（(i,k),(j,l) 按列優先展開）。
pub fn[F : Scalar] mkron(a : Mat[F], b : Mat[F]) -> Mat[F] {
  let rb = b.mrows
  let cb = b.mcols
  Mat::build(a.mrows * rb, a.mcols * cb, (i, j) => {
    F::s_mul(a.at(i / rb, j / cb), b.at(i % rb, j % cb))
  })
}

// ---------------------------------------------------------------------------
// 【演算法 024】vec 與 vec(AXB) = (Bᵀ ⊗ A) vec X
// 定義：vec X 為「行堆疊」（column-stacking）。
// 命題 024：vec(AXB) = (Bᵀ⊗A)vec X。證明：逐分量比較兩邊第 (i,l) 項
//   Σ_{j,k} a_{ij} x_{jk} b_{kl}。∎  此即張量積與線性映射之對應（見 tensor.mbt）。
// ---------------------------------------------------------------------------

///|
/// vec X（行堆疊）
pub fn[F] mvec(x : Mat[F]) -> Array[F] {
  let r = x.mrows
  let c = x.mcols
  Array::makei(r * c, k => x.at(k % r, k / r))
}

///|
/// vec 之逆
pub fn[F] munvec(v : Array[F], r : Int, c : Int) -> Mat[F] {
  Mat::build(r, c, (i, j) => v[j * r + i])
}

// ---------------------------------------------------------------------------
// 【演算法 025】Schur 補 S = D − C A⁻¹ B
// 命題 025：若 A 可逆，則 det M = det A · det S（M = [[A,B],[C,D]]），
//   且 M 可逆 ⟺ S 可逆。證明：分塊 LU
//   M = [[I,0],[CA⁻¹,I]]·[[A,0],[0,S]]·[[I,A⁻¹B],[0,I]]，取行列式。∎
// ---------------------------------------------------------------------------

///|
/// Schur 補 S = D − C A⁻¹ B（A 為左上 k × k 塊；A 奇異回 None）。
pub fn[F : Scalar] schur_complement(
  m : Mat[F],
  k : Int, // 左上塊尺寸
) -> Mat[F]? {
  let n = m.mrows
  let a = m.sub(0, k, 0, k)
  let b = m.sub(0, k, k, n)
  let c = m.sub(k, n, 0, k)
  let d = m.sub(k, n, k, n)
  match minv(a) {
    None => None
    Some(ai) => Some(d.minus(c.times(ai).times(b)))
  }
}

// ---------------------------------------------------------------------------
// 【演算法 026】Faddeev–LeVerrier：特徵多項式（精確，無需特徵值）
// 定義：χ_A(λ) = det(λI − A) = λⁿ + c_{n−1}λ^{n−1} + … + c₀。
// 遞迴：M₁ = I, c_{n−1} = −tr(A M₁)；
//       M_{k+1} = A M_k + c_{n−k} I, c_{n−k−1} = −tr(A M_{k+1})/(k+1)。
// 命題 026：上述遞迴給出 χ_A 之係數（Newton 恆等式 + 牛頓冪和）。
// 推論（Cayley–Hamilton）：χ_A(A) = 0。本實作以此作交叉證明義務。
// ---------------------------------------------------------------------------

///|
/// 回傳 [c₀, c₁, …, c_{n−1}, 1]（升冪係數，首一多項式）
pub fn[F : Scalar] char_poly(a : Mat[F]) -> Array[F] {
  let n = a.mrows
  let coeffs = Array::makei(n + 1, _ => F::s_zero())
  coeffs[n] = F::s_one()
  let mut mk : Mat[F] = Mat::ident(n)
  for k in 1..<(n + 1) {
    let am = a.times(mk)
    let tr = am.trace()
    let ck = match F::s_inv(F::s_from_int(k)) {
      Some(x) => F::s_neg(F::s_mul(tr, x))
      None => F::s_zero()
    }
    coeffs[n - k] = ck
    mk = am.plus(Mat::ident(n).scale(ck))
  }
  coeffs
}

///|
/// 代入矩陣求 p(A) = Σ cₖ Aᵏ（Horner）
pub fn[F : Scalar] mat_poly_eval(coeffs : Array[F], a : Mat[F]) -> Mat[F] {
  let n = a.mrows
  let mut acc : Mat[F] = Mat::zeros(n, n)
  for k = coeffs.length() - 1; k >= 0; k = k - 1 {
    acc = acc.times(a).plus(Mat::ident(n).scale(coeffs[k]))
  } where {
    proof_invariant: k >= 0,
    proof_invariant: k < coeffs.length(),
    proof_reasoning: (
      #| k 每輪減 1，下界為 −1，故至多 coeffs.length() 輪後終止（Horner 代入）。
    ),
  }
  acc
}

// ---------------------------------------------------------------------------
// 【演算法 027】伴隨矩陣 adj A 與 Cramer 法則
// 命題 027：A·adj(A) = adj(A)·A = (det A)·I；A 可逆時 A⁻¹ = adj(A)/det A。
// 命題 027'（Cramer）：Ax = b 之解 xⱼ = det(A_j)/det(A)，A_j 為以 b 換第 j 行。
// ---------------------------------------------------------------------------

///|
/// 古典伴隨（餘因子矩陣之轉置）
pub fn[F : Scalar] madj(a : Mat[F]) -> Mat[F] {
  let n = a.mrows
  if n == 1 {
    return Mat::build(1, 1, (_i, _j) => F::s_one())
  }
  Mat::build(n, n, (i, j) => {
    // adj(A)_{ij} = C_{ji} = (−1)^{i+j} M_{ji}
    let d = mdet(a.minor_mat(j, i))
    if (i + j) % 2 == 0 {
      d
    } else {
      F::s_neg(d)
    }
  })
}

///|
/// Cramer 法則（A 須可逆）
pub fn[F : Scalar] cramer(a : Mat[F], b : Array[F]) -> Array[F]? {
  let n = a.mrows
  let d = mdet(a)
  if F::s_is_zero(d) {
    return None
  }
  let di = match F::s_inv(d) {
    Some(x) => x
    None => return None
  }
  Some(
    Array::makei(n, j => {
      let aj = Mat::build(n, n, (r, c) => if c == j { b[r] } else { a.at(r, c) })
      F::s_mul(mdet(aj), di)
    }),
  )
}

// ---------------------------------------------------------------------------
// 【演算法 028】矩陣冪 Aᵏ（快速冪）與多項式 p(A)
// 命題 028：A^{k+l} = A^k A^l；若 χ_A(A) = 0 則 A^n 可由低次冪線性表出。
// ---------------------------------------------------------------------------

///|
/// 矩陣冪 Aᵏ（平方乘法，Θ(log k) 次乘法）。
pub fn[F : Scalar] mpow(a : Mat[F], k : Int) -> Mat[F] {
  let n = a.mrows
  let mut acc : Mat[F] = Mat::ident(n)
  let mut b = a
  let mut e = k
  while e > 0 {
    if e % 2 == 1 {
      acc = acc.times(b)
    }
    b = b.times(b)
    e = e / 2
  }
  acc
}

// ---------------------------------------------------------------------------
// 【演算法 029】對稱性判定：對稱 / 反對稱 / Hermitian / 么正 / 正交 / 正規
// ---------------------------------------------------------------------------

///|
/// A = Aᵀ ?
pub fn[F : Scalar] is_symmetric(a : Mat[F]) -> Bool {
  a.equals(a.transpose())
}

///|
/// A = −Aᵀ ?
pub fn[F : Scalar] is_skew(a : Mat[F]) -> Bool {
  a.equals(a.transpose().negm())
}

///|
/// A = A* ?
pub fn[F : Scalar] is_hermitian(a : Mat[F]) -> Bool {
  a.equals(a.adjointm())
}

///|
/// A*A = I ?（實體上即正交）
pub fn[F : Scalar] is_unitary(a : Mat[F]) -> Bool {
  a.adjointm().times(a).equals(Mat::ident(a.mcols))
}

///|
/// AA* = A*A ?
pub fn[F : Scalar] is_normal(a : Mat[F]) -> Bool {
  a.times(a.adjointm()).equals(a.adjointm().times(a))
}

///|
/// 上三角？
pub fn[F : Scalar] is_upper(a : Mat[F]) -> Bool {
  for i in 0..<a.mrows {
    for j in 0..<a.mcols {
      if i > j && !F::s_is_zero(a.at(i, j)) {
        return false
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// 【演算法 030】Cayley 變換 C(S) = (I − S)(I + S)⁻¹
// 命題 030：S 反對稱 ⇒ C(S) 正交且 det C(S) = 1（I+S 恆可逆，因
//   S 反對稱之特徵值為純虛數，−1 不是特徵值）。
//   逆變換 S = (I − Q)(I + Q)⁻¹。
// ---------------------------------------------------------------------------

///|
/// Cayley 變換 (I − S)(I + S)⁻¹（I + S 不可逆時回 None）。
pub fn[F : Scalar] cayley_transform(s : Mat[F]) -> Mat[F]? {
  let n = s.mrows
  let i = Mat::ident(n)
  match minv(i.plus(s)) {
    None => None
    Some(inv) => Some(i.minus(s).times(inv))
  }
}

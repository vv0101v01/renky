///|
/// # N-93 … N-107 結構矩陣族
///
/// 十五條新演算法，共同主題是：**矩陣帶著結構時，通用演算法是浪費的**。
/// 每一條都給出 (1) 結構的定義、(2) 利用結構的封閉式或快速路徑、
/// (3) 與通用路徑逐元相同的證明、(4) 一個兩側對照。
///
/// 這一族刻意接在第十七～二十輪的傅立葉線上：循環矩陣是 Toeplitz 的
/// 特例，而 Toeplitz 的快速乘法正是靠嵌進一個兩倍大的循環矩陣。

// ---------------------------------------------------------------------------
//  Toeplitz / Hankel
// ---------------------------------------------------------------------------

///|
/// Toeplitz 矩陣：T[i][j] = t[(n−1) + i − j]，t 長度 2n−1。
///
/// 約定 t 的索引 0 … 2n−2 對應對角線 −(n−1) … (n−1)，
/// 故 t[n−1] 為主對角線。
pub fn[F] toeplitz(t : Array[F], n : Int) -> Mat[F] {
  Mat::build(n, n, (i, j) => t[n - 1 + i - j])
}

///|
/// Hankel 矩陣：H[i][j] = h[i + j]，h 長度 2n−1。
pub fn[F] hankel(h : Array[F], n : Int) -> Mat[F] {
  Mat::build(n, n, (i, j) => h[i + j])
}

///|
/// 反轉置換 J[i][j] = δ_{i, n−1−j}。
pub fn[F : Scalar] rev_perm(n : Int) -> Mat[F] {
  Mat::build(n, n, (i, j) => {
    if i == n - 1 - j {
      F::s_one()
    } else {
      F::s_zero()
    }
  })
}

///|
/// ## 定理 S-1（Toeplitz 之循環嵌入）
///
/// n 階 Toeplitz T 可嵌入 2n 階循環矩陣 C：取循環符號
///
/// ```text
///   c[k] = t[n−1+k]        0 ≤ k ≤ n−1      （T 的下三角帶，含主對角）
///   c[n] = 任意（取 0）
///   c[k] = t[k−n−1]        n+1 ≤ k ≤ 2n−1   （T 的上三角帶）
/// ```
///
/// 則 C 的左上 n × n 子陣恰為 T，故
/// **T·x = (C·[x; 0]) 的前 n 個分量**。
///
/// 用處：循環矩陣可用 FFT 在 Θ(n log n) 內乘向量（N-91），
/// 於是 Toeplitz 也可以 —— 而直接法是 Θ(n²)。
/// 這是「把結構嵌進一個更大但更規則的結構」這個手法的樣板。
pub fn[F : Scalar] toeplitz_circ_symbol(t : Array[F], n : Int) -> Array[F] {
  Array::makei(2 * n, k => {
    if k < n {
      t[n - 1 + k]
    } else if k == n {
      F::s_zero()
    } else {
      t[k - n - 1]
    }
  })
}

///|
/// 以循環嵌入計算 T·x（不呼叫 FFT，純驗結構；成本仍 Θ(n²) 但走的是
/// 2n 階循環矩陣的路徑，用來證明嵌入正確）。
pub fn[F : Scalar] toeplitz_mul_via_circ(
  t : Array[F],
  n : Int,
  x : Array[F],
) -> Array[F] {
  let c = toeplitz_circ_symbol(t, n)
  let big : Mat[F] = circ_mat(c)
  let xx : Array[F] = Array::makei(2 * n, i => {
    if i < n {
      x[i]
    } else {
      F::s_zero()
    }
  })
  let y = big.apply(xx)
  Array::makei(n, i => y[i])
}

// ---------------------------------------------------------------------------
//  低秩更新
// ---------------------------------------------------------------------------

///|
/// ## 定理 S-3（Sherman–Morrison）
///
/// A 可逆、1 + vᵀA⁻¹u ≠ 0 時
///
/// ```text
///   (A + u vᵀ)⁻¹ = A⁻¹ − (A⁻¹u)(vᵀA⁻¹) / (1 + vᵀA⁻¹u)
/// ```
///
/// 成本：已知 A⁻¹ 時右式只要兩次矩陣向量積與一次外積，Θ(n²)；
/// 左式重新求逆是 Θ(n³)。
///
/// 回傳 None 表示分母為零（此時 A + uvᵀ 確實奇異）。
pub fn sherman_morrison(ainv : Mat[Q], u : Array[Q], v : Array[Q]) -> Mat[Q]? {
  let n = ainv.mrows
  let au : Array[Q] = Array::makei(n, i => {
    let mut s = Q::zero()
    for k in 0..<n {
      s = s.add(ainv.at(i, k).mul(u[k]))
    }
    s
  })
  let va : Array[Q] = Array::makei(n, j => {
    let mut s = Q::zero()
    for k in 0..<n {
      s = s.add(v[k].mul(ainv.at(k, j)))
    }
    s
  })
  let mut den = Q::one()
  for k in 0..<n {
    den = den.add(v[k].mul(au[k]))
  }
  let dinv = match den.inv() {
    Some(v) => v
    None => return None
  }
  Some(
    Mat::build(n, n, (i, j) => ainv.at(i, j).sub(au[i].mul(va[j]).mul(dinv))),
  )
}

///|
/// ## 定理 S-4（Woodbury，秩 k）
///
/// ```text
///   (A + UCVᵀ)⁻¹ = A⁻¹ − A⁻¹U (C⁻¹ + VᵀA⁻¹U)⁻¹ VᵀA⁻¹
/// ```
///
/// 成本：中間只需反一個 k × k 矩陣，故 k ≪ n 時由 Θ(n³) 降為 Θ(n²k + k³)。
pub fn woodbury(
  ainv : Mat[Q],
  u : Mat[Q],
  cinv : Mat[Q],
  v : Mat[Q],
  cost : Cost,
) -> Mat[Q]? {
  let au = ainv.times(u)
  let va = v.transpose().times(ainv)
  let mid = cinv.plus(va.times(u))
  match qinv_gauss(mid, cost) {
    None => None
    Some(mi) => Some(ainv.minus(au.times(mi).times(va)))
  }
}

// ---------------------------------------------------------------------------
//  分塊結構
// ---------------------------------------------------------------------------

///|
/// 取子陣 M[r0..r0+nr][c0..c0+nc]。
pub fn[F] submat(m : Mat[F], r0 : Int, c0 : Int, nr : Int, nc : Int) -> Mat[F] {
  Mat::build(nr, nc, (i, j) => m.at(r0 + i, c0 + j))
}

///|
/// 由四塊拼回。
pub fn[F] blocks4(a : Mat[F], b : Mat[F], c : Mat[F], d : Mat[F]) -> Mat[F] {
  let p = a.mrows
  let q = a.mcols
  Mat::build(p + c.mrows, q + b.mcols, (i, j) => {
    if i < p && j < q {
      a.at(i, j)
    } else if i < p {
      b.at(i, j - q)
    } else if j < q {
      c.at(i - p, j)
    } else {
      d.at(i - p, j - q)
    }
  })
}

///|
/// ## 定理 S-5（Schur 補與分塊行列式）
///
/// M = [[A, B], [C, D]]、A 可逆時，Schur 補 S = D − C A⁻¹ B 滿足
///
/// ```text
///   det M = det A · det S
/// ```
///
/// 本庫已有 `schur_complement(m, k)`（matrix.mbt），本族直接沿用 ——
/// **既有的就不重寫**。N-97 驗的是它與分塊行列式公式的關係，
/// 以及 p、q 懸殊時的成本差距。

///|
/// ## 定理 S-6（分塊三角之行列式與求解）
///
/// M = [[A, B], [0, D]] ⇒ det M = det A · det D，
/// 且 M x = [f; g] 可由 D y₂ = g、A y₁ = f − B y₂ 兩步回代解出。
pub fn block_upper_solve(
  a : Mat[Q],
  b : Mat[Q],
  d : Mat[Q],
  f : Array[Q],
  g : Array[Q],
  cost : Cost,
) -> Array[Q]? {
  let p = a.mrows
  let q = d.mrows
  match qsolve_gauss(d, g, cost) {
    None => None
    Some(y2) => {
      let by : Array[Q] = Array::makei(p, i => {
        let mut s = Q::zero()
        for k in 0..<q {
          s = s.add(b.at(i, k).mul(y2[k]))
        }
        s
      })
      let rhs : Array[Q] = Array::makei(p, i => f[i].sub(by[i]))
      match qsolve_gauss(a, rhs, cost) {
        None => None
        Some(y1) =>
          Some(Array::makei(p + q, i => if i < p { y1[i] } else { y2[i - p] }))
      }
    }
  }
}

// ---------------------------------------------------------------------------
//  Kronecker 與 Sylvester
// ---------------------------------------------------------------------------

///|
/// ## 定理 S-7（Kronecker 線性系統之分離求解）
///
/// (A ⊗ B) x = c，把 x、c 列優先重塑為 n_A × n_B 矩陣 X、C，則
///
/// ```text
///   (A ⊗ B)x = c  ⟺  A · X · Bᵀ = C  ⟺  X = A⁻¹ · C · B⁻ᵀ
/// ```
///
/// 成本：直接解 n_An_B 階系統是 Θ((n_An_B)³)；
/// 分離解只要兩次小反矩陣與兩次乘法，Θ(n_A³ + n_B³ + n_An_B(n_A+n_B))。
/// n_A = n_B = 12 時 144³ ≈ 3.0M 對 約 7k，差三個數量級。
pub fn kron_solve(
  a : Mat[Q],
  b : Mat[Q],
  c : Array[Q],
  cost : Cost,
) -> Array[Q]? {
  let na = a.mrows
  let nb = b.mrows
  match (qinv_gauss(a, cost), qinv_gauss(b, cost)) {
    (Some(ai), Some(bi)) => {
      let cm : Mat[Q] = Mat::build(na, nb, (i, j) => c[i * nb + j])
      let x = ai.times(cm).times(bi.transpose())
      Some(Array::makei(na * nb, u => x.at(u / nb, u % nb)))
    }
    _ => None
  }
}

///|
/// ## 定理 S-8（Sylvester 方程之 Kronecker 化）
///
/// A X + X B = C（A 為 m×m、B 為 n×n、X、C 為 m×n）等價於
///
/// ```text
///   (I_n ⊗ A + Bᵀ ⊗ I_m) · vec_row(X) = vec_row(C)
/// ```
///
/// 其中 vec_row 為列優先展平。可解 ⟺ spec(A) ∩ spec(−B) = ∅。
pub fn sylvester_matrix(a : Mat[Q], b : Mat[Q]) -> Mat[Q] {
  let m = a.mrows
  let n = b.mrows
  // 列優先：索引 u = i·n + j 對應 X[i][j]
  // (AX)[i][j] = Σ_k A[i][k] X[k][j]  → 係數在 (u, k·n+j)
  // (XB)[i][j] = Σ_k X[i][k] B[k][j]  → 係數在 (u, i·n+k)
  Mat::build(m * n, m * n, (u, v) => {
    let i = u / n
    let j = u % n
    let p = v / n
    let q = v % n
    let mut s = Q::zero()
    if q == j {
      s = s.add(a.at(i, p))
    }
    if p == i {
      s = s.add(b.at(q, j))
    }
    s
  })
}

// ---------------------------------------------------------------------------
//  特徵值定位
// ---------------------------------------------------------------------------

///|
/// ## 定理 S-9（Gershgorin 圓盤）
///
/// A 之每個特徵值落在某個圓盤 D_i = {z : |z − A[i][i]| ≤ R_i}，
/// R_i = Σ_{j≠i} |A[i][j]|。
///
/// 推論（本庫用得到的形式）：對稱實矩陣之特徵值全落在
/// [min_i(a_ii − R_i), max_i(a_ii + R_i)]；若所有 a_ii − R_i > 0
/// 則 A **嚴格對角佔優且正定** —— 一個 Θ(n²) 的正定充分條件，
/// 比 Θ(n³) 的 Sylvester 便宜一個數量級（但只是充分，不是必要）。
///
/// 回傳 (下界, 上界, 是否對角佔優)。
pub fn gershgorin_bounds(a : Mat[Q]) -> (Q, Q, Bool) {
  let n = a.mrows
  let mut lo = Q::zero()
  let mut hi = Q::zero()
  let mut dom = true
  for i in 0..<n {
    let mut r = Q::zero()
    for j in 0..<n {
      if j != i {
        r = r.add(a.at(i, j).abs())
      }
    }
    let l = a.at(i, i).sub(r)
    let h = a.at(i, i).add(r)
    if i == 0 || l.cmp(lo) < 0 {
      lo = l
    }
    if i == 0 || h.cmp(hi) > 0 {
      hi = h
    }
    if l.cmp(Q::zero()) <= 0 {
      dom = false
    }
  }
  (lo, hi, dom)
}

// ---------------------------------------------------------------------------
//  Cauchy / Vandermonde
// ---------------------------------------------------------------------------

///|
/// Cauchy 矩陣 C[i][j] = 1/(x_i + y_j)。
pub fn cauchy_mat(x : Array[Q], y : Array[Q]) -> Mat[Q]? {
  let n = x.length()
  let m = y.length()
  for i in 0..<n {
    for j in 0..<m {
      if x[i].add(y[j]).is_zero() {
        return None
      }
    }
  }
  Some(
    Mat::build(n, m, (i, j) => {
      match x[i].add(y[j]).inv() {
        Some(v) => v
        None => Q::zero()
      }
    }),
  )
}

///|
/// ## 定理 S-11（Cauchy 行列式之封閉式）
///
/// ```text
///   det C = Π_{i<j} (x_j − x_i)(y_j − y_i) / Π_{i,j} (x_i + y_j)
/// ```
///
/// 成本：Θ(n²) 對通用消去的 Θ(n³)。
pub fn cauchy_det(x : Array[Q], y : Array[Q]) -> Q? {
  let n = x.length()
  if y.length() != n {
    return None
  }
  let mut num = Q::one()
  for i in 0..<n {
    for j in (i + 1)..<n {
      num = num.mul(x[j].sub(x[i])).mul(y[j].sub(y[i]))
    }
  }
  let mut den = Q::one()
  for i in 0..<n {
    for j in 0..<n {
      let s = x[i].add(y[j])
      if s.is_zero() {
        return None
      }
      den = den.mul(s)
    }
  }
  match den.inv() {
    Some(v) => Some(num.mul(v))
    None => None
  }
}

///|
/// ## 定理 S-12（Vandermonde 行列式）
///
/// det V = Π_{i<j}(x_j − x_i)，Θ(n²) 對通用消去的 Θ(n³)。
///
/// 本庫已有 `vandermonde(nodes, n)` 與 `vandermonde_det_formula(nodes)`
/// （polyspace.mbt），本族沿用；N-102 驗的是封閉式與 `mdet` 一致、
/// 以及由它導出的「節點相異 ⟺ 可逆」。

// ---------------------------------------------------------------------------
//  帶狀 / 置換 / 低秩
// ---------------------------------------------------------------------------

///|
/// 矩陣之帶寬（上下皆計）：max |i − j| 使 A[i][j] ≠ 0。
pub fn band_width(a : Mat[Q]) -> Int {
  let mut w = 0
  for i in 0..<a.mrows {
    for j in 0..<a.mcols {
      if !a.at(i, j).is_zero() {
        let d = if i > j { i - j } else { j - i }
        if d > w {
          w = d
        }
      }
    }
  }
  w
}

///|
/// 造一個帶寬為 w 的對稱正定帶狀矩陣。
pub fn band_spd(n : Int, w : Int, rng : Rng) -> Mat[Q] {
  let b : Mat[Q] = Mat::build(n, n, (i, j) => {
    let d = if i > j { i - j } else { j - i }
    if d <= w {
      qr(rng)
    } else {
      Q::zero()
    }
  })
  // BᵀB 會把帶寬加倍；改用 對稱化 + 對角佔優 以保持帶寬 w
  let s : Mat[Q] = Mat::build(n, n, (i, j) => {
    if i <= j {
      b.at(i, j)
    } else {
      b.at(j, i)
    }
  })
  Mat::build(n, n, (i, j) => {
    if i == j {
      let mut r = Q::zero()
      for k in 0..<n {
        if k != i {
          r = r.add(s.at(i, k).abs())
        }
      }
      r.add(Q::one())
    } else {
      s.at(i, j)
    }
  })
}

///|
/// 低秩精確分解：由 k 個列向量與 k 個行向量造秩 ≤ k 之矩陣。
pub fn low_rank(u : Mat[Q], v : Mat[Q]) -> Mat[Q] {
  u.times(v.transpose())
}

///|
/// 置換矩陣沿用 midend2.mbt 之 `perm_mat`（P[p[u]][u] = 1）。

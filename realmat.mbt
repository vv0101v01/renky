// ============================================================================
//  檔案 14：realmat.mbt — 數值軌道（ℝ = binary64）之矩陣分解與迭代演算法
//  ★ 所有命題於此軌道改以「a posteriori 殘差憑證」陳述：
//     演算法回傳之物件 X 滿足 ‖F(X)‖ ≤ ε_cert，ε_cert 於義務中明示。
//     這是數值分析意義下之「可驗證證明」（verified computation）。
// ============================================================================

///|
/// 數值矩陣之別名
pub type RMat = Mat[Double]

///|
/// 複數矩陣（數值軌道）
pub type CMat = Mat[Cpx[Double]]

// ---------------------------------------------------------------------------
// 【演算法 081】Cholesky 分解 A = L Lᵀ（對稱正定）
// 定理 081：A 對稱正定 ⟺ 存在唯一下三角 L（對角 > 0）使 A = LLᵀ。
// 證明（存在性，歸納）：A = [[a₁₁, bᵀ],[b, C]]，a₁₁ > 0，
//   取 l₁₁ = √a₁₁，l = b/l₁₁，則 C − l lᵀ 仍對稱正定（Schur 補，命題 025），
//   對其用歸納假設。唯一性由對角正性與逐列求解之確定性得出。∎
// 憑證：‖A − LLᵀ‖_max ≤ ε。
// ---------------------------------------------------------------------------

///|
pub fn cholesky(a : RMat) -> RMat? {
  let n = a.mrows
  let l : RMat = Mat::zeros(n, n)
  for j in 0..<n {
    let mut s = a.at(j, j)
    for k in 0..<j {
      s = s - l.at(j, k) * l.at(j, k)
    }
    if s <= 0.0 {
      return None
    }
    let ljj = sqrt_newton(s)
    l.put(j, j, ljj)
    for i in (j + 1)..<n {
      let mut t = a.at(i, j)
      for k in 0..<j {
        t = t - l.at(i, k) * l.at(j, k)
      }
      l.put(i, j, t / ljj)
    }
  }
  Some(l)
}

// ---------------------------------------------------------------------------
// 【演算法 082】LDLᵀ 分解與 Sylvester 慣性定律
// 定理 082（Sylvester 慣性定律）：對稱 A 之慣性 (n₊,n₀,n₋) 於合同變換
//   A ↦ SᵀAS（S 可逆）下不變。LDLᵀ 給出之 D 對角號數即慣性。
// ---------------------------------------------------------------------------

///|
/// 回傳 (L, D 對角)；失敗（需要樞軸置換）時回 None
pub fn ldlt(a : RMat) -> (RMat, Array[Double])? {
  let n = a.mrows
  let l : RMat = Mat::ident(n)
  let d = Array::make(n, 0.0)
  for j in 0..<n {
    let mut s = a.at(j, j)
    for k in 0..<j {
      s = s - l.at(j, k) * l.at(j, k) * d[k]
    }
    d[j] = s
    if absd(s) < 1.0e-14 {
      return None
    }
    for i in (j + 1)..<n {
      let mut t = a.at(i, j)
      for k in 0..<j {
        t = t - l.at(i, k) * l.at(j, k) * d[k]
      }
      l.put(i, j, t / s)
    }
  }
  Some((l, d))
}

///|
/// 慣性 (正, 零, 負)
pub fn inertia(d : Array[Double]) -> (Int, Int, Int) {
  let mut p = 0
  let mut z = 0
  let mut m = 0
  for x in d {
    if x > 1.0e-12 {
      p = p + 1
    } else if x < -1.0e-12 {
      m = m + 1
    } else {
      z = z + 1
    }
  }
  (p, z, m)
}

// ---------------------------------------------------------------------------
// 【演算法 083】Householder QR 分解 A = QR
// 定理 083：任意 A ∈ ℝ^{m×n} 存在正交 Q 與上三角 R 使 A = QR。
// 構造：H_k = I − 2 v vᵀ/(vᵀv) 逐行消去下三角元素；Q = H₁…H_n。
// 命題：H 為對稱正交對合矩陣（H² = I，det H = −1），
//   故 Q 正交；數值上後向穩定（Wilkinson）。
// 憑證：‖A − QR‖_max ≤ ε 且 ‖QᵀQ − I‖_max ≤ ε。
// ---------------------------------------------------------------------------

///|
pub fn qr_householder(a0 : RMat) -> (RMat, RMat) {
  let m = a0.mrows
  let n = a0.mcols
  let r = a0.clone()
  let q : RMat = Mat::ident(m)
  let kmax = if m - 1 < n { m - 1 } else { n }
  for k in 0..<kmax {
    // v = x ± ‖x‖e₁
    let mut nrm = 0.0
    for i in k..<m {
      nrm = nrm + r.at(i, k) * r.at(i, k)
    }
    nrm = sqrt_newton(nrm)
    if nrm < 1.0e-300 {
      continue
    }
    let alpha = if r.at(k, k) >= 0.0 { -nrm } else { nrm }
    let v = Array::make(m, 0.0)
    for i in k..<m {
      v[i] = r.at(i, k)
    }
    v[k] = v[k] - alpha
    let mut vtv = 0.0
    for i in k..<m {
      vtv = vtv + v[i] * v[i]
    }
    if vtv < 1.0e-300 {
      continue
    }
    // R ← H R
    for j in 0..<n {
      let mut s = 0.0
      for i in k..<m {
        s = s + v[i] * r.at(i, j)
      }
      let f = 2.0 * s / vtv
      for i in k..<m {
        r.put(i, j, r.at(i, j) - f * v[i])
      }
    }
    // Q ← Q H
    for i in 0..<m {
      let mut s = 0.0
      for j in k..<m {
        s = s + q.at(i, j) * v[j]
      }
      let f = 2.0 * s / vtv
      for j in k..<m {
        q.put(i, j, q.at(i, j) - f * v[j])
      }
    }
  }
  (q, r)
}

// ---------------------------------------------------------------------------
// 【演算法 084】Givens 旋轉 QR
// 定義：G(i,k,θ) 為平面旋轉；選 θ 使 (G A)_{ik} = 0。
// 命題 084：Givens 與 Householder 給出之 R 於正負號外唯一（QR 唯一性：
//   A 滿秩且要求 R 對角 > 0 時 QR 分解唯一）。
// ---------------------------------------------------------------------------

///|
pub fn qr_givens(a0 : RMat) -> (RMat, RMat) {
  let m = a0.mrows
  let n = a0.mcols
  let r = a0.clone()
  let q : RMat = Mat::ident(m)
  for j in 0..<n {
    for i = m - 1; i > j; i = i - 1 {
      let aa = r.at(i - 1, j)
      let bb = r.at(i, j)
      if absd(bb) < 1.0e-300 {
        continue
      }
      let h = sqrt_newton(aa * aa + bb * bb)
      let c = aa / h
      let s = -bb / h
      for k in 0..<n {
        let x = r.at(i - 1, k)
        let y = r.at(i, k)
        r.put(i - 1, k, c * x - s * y)
        r.put(i, k, s * x + c * y)
      }
      for k in 0..<m {
        let x = q.at(k, i - 1)
        let y = q.at(k, i)
        q.put(k, i - 1, c * x - s * y)
        q.put(k, i, s * x + c * y)
      }
    }
  }
  (q, r)
}

// ---------------------------------------------------------------------------
// 【演算法 085】Hessenberg 化約 A = Q H Qᵀ
// 命題 085：任意方陣可用 Householder 相似變換化為上 Hessenberg 形；
//   對稱矩陣則化為三對角形（此為 QR 迭代之預處理，複雜度 O(n³)）。
// ---------------------------------------------------------------------------

///|
pub fn hessenberg(a0 : RMat) -> (RMat, RMat) {
  let n = a0.mrows
  let h = a0.clone()
  let q : RMat = Mat::ident(n)
  for k in 0..<(n - 2) {
    let mut nrm = 0.0
    for i in (k + 1)..<n {
      nrm = nrm + h.at(i, k) * h.at(i, k)
    }
    nrm = sqrt_newton(nrm)
    if nrm < 1.0e-300 {
      continue
    }
    let alpha = if h.at(k + 1, k) >= 0.0 { -nrm } else { nrm }
    let v = Array::make(n, 0.0)
    for i in (k + 1)..<n {
      v[i] = h.at(i, k)
    }
    v[k + 1] = v[k + 1] - alpha
    let mut vtv = 0.0
    for i in (k + 1)..<n {
      vtv = vtv + v[i] * v[i]
    }
    if vtv < 1.0e-300 {
      continue
    }
    // H ← P H P，P = I − 2vvᵀ/vᵀv
    for j in 0..<n {
      let mut s = 0.0
      for i in (k + 1)..<n {
        s = s + v[i] * h.at(i, j)
      }
      let f = 2.0 * s / vtv
      for i in (k + 1)..<n {
        h.put(i, j, h.at(i, j) - f * v[i])
      }
    }
    for i in 0..<n {
      let mut s = 0.0
      for j in (k + 1)..<n {
        s = s + h.at(i, j) * v[j]
      }
      let f = 2.0 * s / vtv
      for j in (k + 1)..<n {
        h.put(i, j, h.at(i, j) - f * v[j])
      }
    }
    for i in 0..<n {
      let mut s = 0.0
      for j in (k + 1)..<n {
        s = s + q.at(i, j) * v[j]
      }
      let f = 2.0 * s / vtv
      for j in (k + 1)..<n {
        q.put(i, j, q.at(i, j) - f * v[j])
      }
    }
  }
  (q, h)
}

// ---------------------------------------------------------------------------
// 【演算法 086】Jacobi 對稱特徵值演算法
// 定理 086（譜定理，實對稱）：A = Aᵀ ⇒ ∃ 正交 Q 使 QᵀAQ = diag(λ).
// Jacobi：反覆以平面旋轉消去最大非對角元，off(A) = Σ_{i≠j}a_{ij}² 嚴格遞減：
//   每步 off(A') = off(A) − 2a_{pq}² ⇒ 線性收斂（實際為二次收斂）。
// 憑證：‖QᵀAQ − Λ‖_max ≤ ε 且 ‖QᵀQ − I‖_max ≤ ε。
// ---------------------------------------------------------------------------

///|
/// 回傳 (特徵值, 特徵向量矩陣 Q（各行為特徵向量）)
pub fn jacobi_eigen(a0 : RMat, sweeps : Int) -> (Array[Double], RMat) {
  let n = a0.mrows
  let b = a0.clone()
  let v : RMat = Mat::ident(n)
  for _s in 0..<sweeps {
    // 找最大非對角元
    let mut p = 0
    let mut q = 1
    let mut best = -1.0
    for i in 0..<n {
      for j in (i + 1)..<n {
        let m = absd(b.at(i, j))
        if m > best {
          best = m
          p = i
          q = j
        }
      }
    }
    if n < 2 || best < 1.0e-15 {
      break
    }
    let app = b.at(p, p)
    let aqq = b.at(q, q)
    let apq = b.at(p, q)
    let theta = 0.5 * atan2_own(2.0 * apq, app - aqq)
    let c = cos_taylor(theta)
    let s = sin_taylor(theta)
    // B ← JᵀBJ
    for k in 0..<n {
      let bkp = b.at(k, p)
      let bkq = b.at(k, q)
      b.put(k, p, c * bkp + s * bkq)
      b.put(k, q, -s * bkp + c * bkq)
    }
    for k in 0..<n {
      let bpk = b.at(p, k)
      let bqk = b.at(q, k)
      b.put(p, k, c * bpk + s * bqk)
      b.put(q, k, -s * bpk + c * bqk)
    }
    for k in 0..<n {
      let vkp = v.at(k, p)
      let vkq = v.at(k, q)
      v.put(k, p, c * vkp + s * vkq)
      v.put(k, q, -s * vkp + c * vkq)
    }
  }
  let lam = Array::makei(n, i => b.at(i, i))
  (lam, v)
}

// ---------------------------------------------------------------------------
// 【演算法 087】無位移 QR 迭代（特徵值）
// 定理 087：A₀ = A，A_{k+1} = R_k Q_k（A_k = Q_k R_k）⇒ A_k 正交相似於 A，
//   且在特徵值模長互異時 A_k 收斂到（分塊）上三角（Schur 形）。
// ---------------------------------------------------------------------------

///|
pub fn qr_iteration(a0 : RMat, iters : Int) -> RMat {
  let mut a = a0.clone()
  for _k in 0..<iters {
    let (q, r) = qr_householder(a)
    a = r.times(q)
  }
  a
}

// ---------------------------------------------------------------------------
// 【演算法 088】單邊 Jacobi SVD：A = U Σ Vᵀ
// 定理 088（奇異值分解）：∀A ∈ ℝ^{m×n} ∃ 正交 U, V 與非負對角 Σ 使 A = UΣVᵀ。
//   證明：AᵀA 對稱半正定 ⇒ 譜定理給 V 與 σᵢ² = λᵢ；取 uᵢ = Avᵢ/σᵢ（σᵢ>0）
//   並補成正交基。∎
// 單邊 Jacobi：對 A 之行兩兩作旋轉使其正交，收斂後行範數即奇異值。
// ---------------------------------------------------------------------------

///|
/// 回傳 (U, σ, V)，A ≈ U diag(σ) Vᵀ（U : m×n，V : n×n）
pub fn svd_jacobi(a0 : RMat, sweeps : Int) -> (RMat, Array[Double], RMat) {
  let m = a0.mrows
  let n = a0.mcols
  let u = a0.clone()
  let v : RMat = Mat::ident(n)
  for _s in 0..<sweeps {
    let mut off = 0.0
    for i in 0..<n {
      for j in (i + 1)..<n {
        let mut alpha = 0.0
        let mut beta = 0.0
        let mut gamma = 0.0
        for k in 0..<m {
          alpha = alpha + u.at(k, i) * u.at(k, i)
          beta = beta + u.at(k, j) * u.at(k, j)
          gamma = gamma + u.at(k, i) * u.at(k, j)
        }
        off = off + absd(gamma)
        if absd(gamma) < 1.0e-15 {
          continue
        }
        let zeta = (beta - alpha) / (2.0 * gamma)
        let t = (if zeta >= 0.0 { 1.0 } else { -1.0 }) /
          (absd(zeta) + sqrt_newton(1.0 + zeta * zeta))
        let c = 1.0 / sqrt_newton(1.0 + t * t)
        let s = c * t
        for k in 0..<m {
          let x = u.at(k, i)
          let y = u.at(k, j)
          u.put(k, i, c * x - s * y)
          u.put(k, j, s * x + c * y)
        }
        for k in 0..<n {
          let x = v.at(k, i)
          let y = v.at(k, j)
          v.put(k, i, c * x - s * y)
          v.put(k, j, s * x + c * y)
        }
      }
    }
    if off < 1.0e-15 {
      break
    }
  }
  let sig = Array::make(n, 0.0)
  for j in 0..<n {
    let mut s = 0.0
    for i in 0..<m {
      s = s + u.at(i, j) * u.at(i, j)
    }
    sig[j] = sqrt_newton(s)
    if sig[j] > 1.0e-300 {
      for i in 0..<m {
        u.put(i, j, u.at(i, j) / sig[j])
      }
    }
  }
  // 依慣例將奇異值遞減排序（同時置換 U、V 之對應行），
  // 使 σ₁ = ‖A‖₂、σ_min 控制 κ₂ = σ₁/σ_n。
  for p in 1..<n {
    let key = sig[p]
    let ucol = Array::makei(m, i => u.at(i, p))
    let vcol = Array::makei(n, i => v.at(i, p))
    let mut q = p - 1
    while q >= 0 && sig[q] < key {
      sig[q + 1] = sig[q]
      for i in 0..<m {
        u.put(i, q + 1, u.at(i, q))
      }
      for i in 0..<n {
        v.put(i, q + 1, v.at(i, q))
      }
      q = q - 1
    }
    sig[q + 1] = key
    for i in 0..<m {
      u.put(i, q + 1, ucol[i])
    }
    for i in 0..<n {
      v.put(i, q + 1, vcol[i])
    }
  }
  (u, sig, v)
}

// ---------------------------------------------------------------------------
// 【演算法 089】Moore–Penrose 偽逆 A⁺ = V Σ⁺ Uᵀ
// 定理 089：A⁺ 為唯一滿足 Penrose 四條件之矩陣：
//   (1) AA⁺A = A  (2) A⁺AA⁺ = A⁺  (3) (AA⁺)ᵀ = AA⁺  (4) (A⁺A)ᵀ = A⁺A。
// 推論：min‖Ax−b‖ 之最小範數解為 x = A⁺b。
// ---------------------------------------------------------------------------

///|
pub fn pinv(a : RMat, tol : Double) -> RMat {
  let (u, s, v) = svd_jacobi(a, 60)
  let n = a.mcols
  let m = a.mrows
  let smax = {
    let mut mx = 0.0
    for x in s {
      mx = maxd(mx, x)
    }
    mx
  }
  let thr = tol * maxd(1.0, smax)
  let sp : RMat = Mat::build(n, m, (i, j) => {
    ignore(i)
    ignore(j)
    0.0
  })
  // A⁺ = V Σ⁺ Uᵀ
  for k in 0..<n {
    if s[k] > thr {
      for i in 0..<n {
        for j in 0..<m {
          sp.put(i, j, sp.at(i, j) + v.at(i, k) * u.at(j, k) / s[k])
        }
      }
    }
  }
  sp
}

// ---------------------------------------------------------------------------
// 【演算法 090】極分解 A = U P（U 正交，P 對稱半正定）
// 定理 090：A = UP，P = (AᵀA)^{1/2}；A 可逆時唯一；
//   U 為「最接近 A 之正交矩陣」（Frobenius 意義下，Fan–Hoffman 定理）。
// ---------------------------------------------------------------------------

///|
pub fn polar_decomposition(a : RMat) -> (RMat, RMat) {
  let (u, s, v) = svd_jacobi(a, 60)
  let n = a.mcols
  // U_polar = U Vᵀ，P = V Σ Vᵀ
  let up = u.times(v.transpose())
  let p : RMat = Mat::build(n, n, (i, j) => {
    let mut acc = 0.0
    for k in 0..<n {
      acc = acc + v.at(i, k) * s[k] * v.at(j, k)
    }
    acc
  })
  (up, p)
}

// ---------------------------------------------------------------------------
// 【演算法 091】矩陣指數 e^A（縮放‑平方 + Taylor）
// 定理 091：e^A ≔ Σ Aᵏ/k! 絕對收斂；e^{A+B} = e^A e^B（AB = BA）；
//   det(e^A) = e^{tr A}（Jacobi 公式）；(e^A)⁻¹ = e^{−A}。
// 縮放‑平方：e^A = (e^{A/2^s})^{2^s}，取 s 使 ‖A/2^s‖ ≤ 1/2。
// ---------------------------------------------------------------------------

///|
pub fn expm(a : RMat) -> RMat {
  let n = a.mrows
  let mut nrm = 0.0
  for i in 0..<n {
    let mut rs = 0.0
    for j in 0..<n {
      rs = rs + absd(a.at(i, j))
    }
    nrm = maxd(nrm, rs)
  }
  let mut s = 0
  let mut scale = 1.0
  while nrm * scale > 0.5 {
    scale = scale / 2.0
    s = s + 1
  }
  let b = a.scale(scale)
  // Taylor 到 20 階
  let mut term : RMat = Mat::ident(n)
  let mut acc : RMat = Mat::ident(n)
  for k in 1..<21 {
    term = term.times(b).scale(1.0 / k.to_double())
    acc = acc.plus(term)
  }
  for _i in 0..<s {
    acc = acc.times(acc)
  }
  acc
}

// ---------------------------------------------------------------------------
// 【演算法 092】對稱正定矩陣之平方根 A^{1/2}（譜方法）
// 定理 092：A 對稱半正定 ⇒ 存在唯一對稱半正定 S 使 S² = A。
// ---------------------------------------------------------------------------

///|
pub fn sqrtm_spd(a : RMat) -> RMat {
  let n = a.mrows
  let (lam, q) = jacobi_eigen(a, 200)
  Mat::build(n, n, (i, j) => {
    let mut acc = 0.0
    for k in 0..<n {
      acc = acc + q.at(i, k) * sqrt_newton(maxd(0.0, lam[k])) * q.at(j, k)
    }
    acc
  })
}

// ---------------------------------------------------------------------------
// 【演算法 093】冪迭代（最大模特徵值）
// 定理 093：|λ₁| > |λ₂| 且 x₀ 於 v₁ 方向分量非零 ⇒ Aᵏx₀/‖Aᵏx₀‖ → ±v₁，
//   收斂率 O(|λ₂/λ₁|ᵏ)。Rayleigh 商 ρ(x) = xᵀAx/xᵀx → λ₁。
// ---------------------------------------------------------------------------

///|
pub fn power_iteration(a : RMat, iters : Int) -> (Double, Array[Double]) {
  let n = a.mrows
  let mut x = Array::makei(n, i => 1.0 / (i + 1).to_double())
  for _k in 0..<iters {
    let y = a.apply(x)
    let mut nrm = 0.0
    for v in y {
      nrm = nrm + v * v
    }
    nrm = sqrt_newton(nrm)
    if nrm < 1.0e-300 {
      break
    }
    x = Array::makei(n, i => y[i] / nrm)
  }
  (rayleigh_quotient(a, x), x)
}

///|
/// Rayleigh 商 ρ(x) = ⟨Ax,x⟩/⟨x,x⟩
pub fn rayleigh_quotient(a : RMat, x : Array[Double]) -> Double {
  let y = a.apply(x)
  let mut num = 0.0
  let mut den = 0.0
  for i in 0..<x.length() {
    num = num + y[i] * x[i]
    den = den + x[i] * x[i]
  }
  if den == 0.0 {
    0.0
  } else {
    num / den
  }
}

// ---------------------------------------------------------------------------
// 【演算法 094】共軛梯度法（對稱正定線性系統）
// 定理 094：CG 於精確算術下至多 n 步收斂；
//   誤差估計 ‖x_k − x*‖_A ≤ 2((√κ−1)/(√κ+1))ᵏ ‖x₀ − x*‖_A。
// 不變量：r_k ⊥ span{r₀..r_{k−1}}，p_k 關於 A 共軛（pᵢᵀApⱼ = 0, i≠j）。
// ---------------------------------------------------------------------------

///|
pub fn conjugate_gradient(
  a : RMat,
  b : Array[Double],
  iters : Int,
) -> Array[Double] {
  let n = b.length()
  let x = Array::make(n, 0.0)
  let r = Array::makei(n, i => b[i])
  let p = Array::makei(n, i => b[i])
  let mut rs = 0.0
  for v in r {
    rs = rs + v * v
  }
  for _k in 0..<iters {
    if rs < 1.0e-28 {
      break
    }
    let ap = a.apply(p)
    let mut pap = 0.0
    for i in 0..<n {
      pap = pap + p[i] * ap[i]
    }
    if absd(pap) < 1.0e-300 {
      break
    }
    let alpha = rs / pap
    for i in 0..<n {
      x[i] = x[i] + alpha * p[i]
      r[i] = r[i] - alpha * ap[i]
    }
    let mut rs2 = 0.0
    for v in r {
      rs2 = rs2 + v * v
    }
    let beta = rs2 / rs
    for i in 0..<n {
      p[i] = r[i] + beta * p[i]
    }
    rs = rs2
  }
  x
}

// ---------------------------------------------------------------------------
// 【演算法 095】Lanczos 三對角化（對稱）
// 定理 095：QᵀAQ = T 三對角，Q 之行為 Krylov 空間 K_k(A,v) 之標準正交基。
// 【演算法 096】Arnoldi 迭代（一般方陣）：QᵀAQ = H 上 Hessenberg。
// ---------------------------------------------------------------------------

///|
/// 回傳 (Q, T)：QᵀAQ = T（k 步）
pub fn lanczos(a : RMat, k : Int) -> (RMat, RMat) {
  let n = a.mrows
  let qcols : Array[Array[Double]] = []
  let mut v = Array::makei(n, i => {
    1.0 / sqrt_newton(n.to_double()) * (if i % 2 == 0 { 1.0 } else { -1.0 })
  })
  let mut nrm = 0.0
  for x in v {
    nrm = nrm + x * x
  }
  nrm = sqrt_newton(nrm)
  v = Array::makei(n, i => v[i] / nrm)
  let alphas : Array[Double] = []
  let betas : Array[Double] = []
  let mut vprev = Array::make(n, 0.0)
  let mut beta = 0.0
  for j in 0..<k {
    qcols.push(v)
    let w = a.apply(v)
    let mut alpha = 0.0
    for i in 0..<n {
      alpha = alpha + w[i] * v[i]
    }
    alphas.push(alpha)
    let w2 = Array::makei(n, i => w[i] - alpha * v[i] - beta * vprev[i])
    // 完全再正交化（數值穩定）
    for qc in qcols {
      let mut s = 0.0
      for i in 0..<n {
        s = s + w2[i] * qc[i]
      }
      for i in 0..<n {
        w2[i] = w2[i] - s * qc[i]
      }
    }
    let mut nb = 0.0
    for x in w2 {
      nb = nb + x * x
    }
    nb = sqrt_newton(nb)
    if j + 1 < k {
      betas.push(nb)
    }
    if nb < 1.0e-14 {
      break
    }
    vprev = v
    beta = nb
    v = Array::makei(n, i => w2[i] / nb)
  }
  let kk = qcols.length()
  let q : RMat = Mat::build(n, kk, (i, j) => qcols[j][i])
  let t : RMat = Mat::build(kk, kk, (i, j) => {
    if i == j {
      alphas[i]
    } else if i + 1 == j && i < betas.length() {
      betas[i]
    } else if j + 1 == i && j < betas.length() {
      betas[j]
    } else {
      0.0
    }
  })
  (q, t)
}

///|
/// Arnoldi：回傳 (Q (n×k), H (k×k))
pub fn arnoldi(a : RMat, k : Int) -> (RMat, RMat) {
  let n = a.mrows
  let qcols : Array[Array[Double]] = []
  let mut v = Array::makei(n, i => 1.0 / (i + 1).to_double())
  let mut nrm = 0.0
  for x in v {
    nrm = nrm + x * x
  }
  nrm = sqrt_newton(nrm)
  v = Array::makei(n, i => v[i] / nrm)
  qcols.push(v)
  let h : RMat = Mat::zeros(k, k)
  for j in 0..<k {
    let w = a.apply(qcols[j])
    for i in 0..<(j + 1) {
      let mut s = 0.0
      for t in 0..<n {
        s = s + w[t] * qcols[i][t]
      }
      h.put(i, j, s)
      for t in 0..<n {
        w[t] = w[t] - s * qcols[i][t]
      }
    }
    let mut nb = 0.0
    for x in w {
      nb = nb + x * x
    }
    nb = sqrt_newton(nb)
    if j + 1 < k {
      h.put(j + 1, j, nb)
      if nb < 1.0e-14 {
        break
      }
      qcols.push(Array::makei(n, t => w[t] / nb))
    }
  }
  let kk = qcols.length()
  let q : RMat = Mat::build(n, kk, (i, j) => qcols[j][i])
  (q, h)
}

// ---------------------------------------------------------------------------
// 【演算法 097】條件數 κ₂(A) = σ_max/σ_min
// 命題 097：相對誤差放大上界 ‖δx‖/‖x‖ ≤ κ(A)·‖δb‖/‖b‖。
//   Hilbert 矩陣之 κ 隨維數指數成長（本專案以 P_n 之 Gram 矩陣展示）。
// ---------------------------------------------------------------------------

///|
pub fn cond2(a : RMat) -> Double {
  let (_u, s, _v) = svd_jacobi(a, 60)
  let mut mx = 0.0
  let mut mn = 1.0e308
  for x in s {
    mx = maxd(mx, x)
    mn = mind(mn, x)
  }
  if mn < 1.0e-300 {
    1.0e308
  } else {
    mx / mn
  }
}

///|
/// 譜半徑（對稱矩陣用 Jacobi；一般矩陣用 QR 迭代之對角）
pub fn spectral_radius_sym(a : RMat) -> Double {
  let (lam, _q) = jacobi_eigen(a, 200)
  let mut mx = 0.0
  for x in lam {
    mx = maxd(mx, absd(x))
  }
  mx
}

// ---------------------------------------------------------------------------
// 【演算法 098】離散傅立葉變換（么正 DFT 矩陣）
//   F_{jk} = ω^{jk}/√n，ω = e^{−2πi/n}。
// 定理 098：F 么正（F*F = I）；循環矩陣 C 滿足 C = F* diag(F̂c) F（對角化）。
// ---------------------------------------------------------------------------

///|
pub fn dft_matrix(n : Int) -> CMat {
  let inv_sqrt = 1.0 / sqrt_newton(n.to_double())
  Mat::build(n, n, (j, k) => {
    let ang = -2.0 * pi_const * (j * k % n).to_double() / n.to_double()
    Cpx::mk(cos_taylor(ang) * inv_sqrt, sin_taylor(ang) * inv_sqrt)
  })
}

///|
/// 循環矩陣 C（第一行為 c，C_{jk} = c_{(j−k) mod n}）
pub fn circulant(c : Array[Double]) -> RMat {
  let n = c.length()
  Mat::build(n, n, (j, k) => c[((j - k) % n + n) % n])
}

///|
/// 實矩陣嵌入複矩陣
pub fn to_complex(a : RMat) -> CMat {
  Mat::build(a.mrows, a.mcols, (i, j) => Cpx::mk(a.at(i, j), 0.0))
}

// ---------------------------------------------------------------------------
// 【演算法 099】Cooley–Tukey 快速傅立葉變換（radix‑2，就地）
// 定理 099：FFT 以 Θ(n log n) 計算 DFT；與 DFT 矩陣乘法結果相同（憑證比對）。
// ---------------------------------------------------------------------------

///|
pub fn fft(x : Array[Cpx[Double]]) -> Array[Cpx[Double]] {
  let n = x.length()
  if n == 1 {
    return [x[0]]
  }
  let even = Array::makei(n / 2, i => x[2 * i])
  let odd = Array::makei(n / 2, i => x[2 * i + 1])
  let fe = fft(even)
  let fo = fft(odd)
  let out : Array[Cpx[Double]] = Array::makei(n, _ => Cpx::mk(0.0, 0.0))
  for k in 0..<(n / 2) {
    let ang = -2.0 * pi_const * k.to_double() / n.to_double()
    let w : Cpx[Double] = Cpx::mk(cos_taylor(ang), sin_taylor(ang))
    let t = Scalar::s_mul(w, fo[k])
    out[k] = Scalar::s_add(fe[k], t)
    out[k + n / 2] = ssub(fe[k], t)
  }
  out
}

// ---------------------------------------------------------------------------
// 【演算法 100】Sylvester–Hadamard 矩陣與快速 Walsh–Hadamard 變換
// 定義：H₁ = [1]，H_{2m} = [[H_m, H_m],[H_m, −H_m]]。
// 定理 100：H_nᵀH_n = n·I（故 H/√n 正交）；FWHT 以 Θ(n log n) 完成，
//   且給出 ℝ^{2^k} 上一組精確（整數！）正交基 —— 精確軌道亦可驗證。
// ---------------------------------------------------------------------------

///|
pub fn hadamard_matrix(k : Int) -> RMat {
  let mut h : RMat = Mat::ident(1)
  for _i in 0..<k {
    let m = h.mrows
    let nh : RMat = Mat::build(2 * m, 2 * m, (i, j) => {
      let s = if i >= m && j >= m { -1.0 } else { 1.0 }
      s * h.at(i % m, j % m)
    })
    h = nh
  }
  h
}

///|
/// 快速 Walsh–Hadamard 變換（就地蝶形）
pub fn fwht(x0 : Array[Double]) -> Array[Double] {
  let x = x0.copy()
  let n = x.length()
  let mut len = 1
  while len < n {
    let mut i = 0
    while i < n {
      for j in i..<(i + len) {
        let a = x[j]
        let b = x[j + len]
        x[j] = a + b
        x[j + len] = a - b
      }
      i = i + 2 * len
    }
    len = len * 2
  }
  x
}

// ---------------------------------------------------------------------------
// 【演算法 101】Haar 小波正交基（n = 2^k）
// 定理 101：Haar 矩陣之列構成 ℝⁿ 之正交基（規範化後為標準正交基），
//   且為多解析度分析（MRA）之最簡例：V_j = V_{j−1} ⊕ W_{j−1}。
// ---------------------------------------------------------------------------

///|
/// 未規範化之 Haar 矩陣（各列正交）
pub fn haar_matrix(k : Int) -> RMat {
  let n = 1 << k
  let h : RMat = Mat::zeros(n, n)
  for j in 0..<n {
    h.put(0, j, 1.0)
  }
  let mut row = 1
  for level in 0..<k {
    let blocks = 1 << level
    let width = n / blocks
    for b in 0..<blocks {
      let start = b * width
      for j in 0..<(width / 2) {
        h.put(row, start + j, 1.0)
        h.put(row, start + width / 2 + j, -1.0)
      }
      row = row + 1
      if row >= n {
        break
      }
    }
  }
  h
}

///|
/// 把矩陣之各列規範化（用於由正交基造標準正交基）
pub fn normalize_rows(a : RMat) -> RMat {
  let m = a.mrows
  let n = a.mcols
  Mat::build(m, n, (i, j) => {
    let mut s = 0.0
    for t in 0..<n {
      s = s + a.at(i, t) * a.at(i, t)
    }
    let nr = sqrt_newton(s)
    if nr < 1.0e-300 {
      0.0
    } else {
      a.at(i, j) / nr
    }
  })
}

// ---------------------------------------------------------------------------
// 【演算法 102】Jacobi / Gauss–Seidel 迭代解法
// 定理 102：A 嚴格對角佔優 ⇒ 兩者皆收斂（譜半徑 ρ(M⁻¹N) < 1）。
// ---------------------------------------------------------------------------

///|
pub fn gauss_seidel(a : RMat, b : Array[Double], iters : Int) -> Array[Double] {
  let n = b.length()
  let x = Array::make(n, 0.0)
  for _k in 0..<iters {
    for i in 0..<n {
      let mut s = b[i]
      for j in 0..<n {
        if j != i {
          s = s - a.at(i, j) * x[j]
        }
      }
      let d = a.at(i, i)
      if absd(d) > 1.0e-300 {
        x[i] = s / d
      }
    }
  }
  x
}

///|
/// 向量 2‑範數
pub fn vnorm2(x : Array[Double]) -> Double {
  let mut s = 0.0
  for v in x {
    s = s + v * v
  }
  sqrt_newton(s)
}

///|
/// 向量最大範數偏差
pub fn vmax_dev(x : Array[Double], y : Array[Double]) -> Double {
  let mut m = 0.0
  for i in 0..<x.length() {
    m = maxd(m, absd(x[i] - y[i]))
  }
  m
}

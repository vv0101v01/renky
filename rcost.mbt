// ============================================================================
//  檔案 22：rcost.mbt — ℝ 軌浮點成本計量器與受計量之演算法孿生體（N-20）
// ============================================================================
//
// 【問題】本庫之成本模型 Cost 只計 BigInt 字乘（wmul），對 ℚ／ℤ 軌有效，
//   對 Double 毫無意義。於是最昂貴、最值得套結構律的演算法 —— Jacobi 特徵
//   分解、SVD、Cholesky、pinv、expm —— 全部無法納入 N 群之量測紀律。
//
// 【做法】不改動既有 realmat.mbt（那會波及 176 條義務），改為另建
//   **受計量之孿生體**：逐行鏡射原演算法，但在每個算術位置累計 flops。
//
// 【定理 177（孿生體之忠實性）】取 tol = 1e-15、maxrot = R，則受計量孿生體
//   與 jacobi_eigen(·, R) 執行**完全相同之運算序列**（兩者之迴圈上界與
//   跳出條件逐字相同），故輸出浮點位元級相同，其 flop 計數即原演算法之計數。
//   此為**可否證之主張**：義務對隨機輸入逐例比對兩者輸出之**精確相等**
//   （偏差必須恰為 0，非「在容差內」），不符即失敗。
//   —— 這是「自行插裝的計量器可信」這件事唯一誠實的證明方式。
//
// 【計量約定】flops ≔ 乘法 + 加減法 + 絕對值／比較。
//   把搜尋與比較計入是刻意的：古典 Jacobi 每次旋轉之主元搜尋為 Θ(n²)，
//   而旋轉本身僅 Θ(n)，若只計乘加會嚴重低估大矩陣之成本。
// ============================================================================

///|
/// 記一筆 k 次浮點運算
pub fn cflop(c : Cost, k : Int64) -> Unit {
  c.flops = c.flops + k
}

///|
/// flop 比（基準 ÷ 快速）
pub fn flop_ratio(base : Cost, fast : Cost) -> Double {
  if fast.flops <= 0L {
    0.0
  } else {
    base.flops.to_double() / fast.flops.to_double()
  }
}

///|
/// 【演算法 177】受計量之 Jacobi 特徵分解（realmat.mbt jacobi_eigen 之孿生體）
///
/// 與原版之唯一差異：以收斂門檻 tol 取代固定 sweeps 數，並回報實際旋轉次數。
/// 固定 sweeps 之比較並不公平 —— 大矩陣需要更多旋轉才收斂，
/// 若對直接法與分解法給相同 sweeps，等於偷偷替直接法打折。
pub fn cjacobi_eigen(
  a0 : RMat,
  tol : Double,
  maxrot : Int,
  c : Cost,
) -> (Array[Double], RMat, Int) {
  let n = a0.mrows
  let b = a0.clone()
  let v : RMat = Mat::ident(n)
  let mut rots = 0
  for _s in 0..<maxrot {
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
    // 主元搜尋：每對 (i,j) 一次絕對值 + 一次比較
    cflop(c, (n * (n - 1) / 2).to_int64() * 2L)
    if n < 2 || best < tol {
      break
    }
    let app = b.at(p, p)
    let aqq = b.at(q, q)
    let apq = b.at(p, q)
    let theta = 0.5 * atan2_own(2.0 * apq, app - aqq)
    let cs = cos_taylor(theta)
    let sn = sin_taylor(theta)
    cflop(c, 4L)
    for k in 0..<n {
      let bkp = b.at(k, p)
      let bkq = b.at(k, q)
      b.put(k, p, cs * bkp + sn * bkq)
      b.put(k, q, -sn * bkp + cs * bkq)
    }
    for k in 0..<n {
      let bpk = b.at(p, k)
      let bqk = b.at(q, k)
      b.put(p, k, cs * bpk + sn * bqk)
      b.put(q, k, -sn * bpk + cs * bqk)
    }
    for k in 0..<n {
      let vkp = v.at(k, p)
      let vkq = v.at(k, q)
      v.put(k, p, cs * vkp + sn * vkq)
      v.put(k, q, -sn * vkp + cs * vkq)
    }
    // 三組迴圈各 n 次，每次 2 輸出 × (2 乘 + 1 加) = 6 flops
    cflop(c, 18L * n.to_int64())
    rots = rots + 1
  }
  let lam = Array::makei(n, i => b.at(i, i))
  (lam, v, rots)
}

///|
/// 受計量之 Kronecker 積（Double）
pub fn rkron_cost(c : Cost, a : RMat, b : RMat) -> RMat {
  let m = b.mrows
  let p = b.mcols
  cflop(c, (a.mrows * a.mcols * m * p).to_int64())
  Mat::build(a.mrows * m, a.mcols * p, (i, j) => {
    a.at(i / m, j / p) * b.at(i % m, j % p)
  })
}

///|
/// 分塊對角（Double，零 flop）
pub fn rblock_diag(a : RMat, b : RMat) -> RMat {
  let ra = a.mrows
  let ca = a.mcols
  Mat::build(ra + b.mrows, ca + b.mcols, (i, j) => {
    if i < ra && j < ca {
      a.at(i, j)
    } else if i >= ra && j >= ca {
      b.at(i - ra, j - ca)
    } else {
      0.0
    }
  })
}

///|
/// 隨機實對稱正定矩陣 G = MᵀM + nI
pub fn rand_spd(rng : Rng, n : Int) -> RMat {
  let m : RMat = Mat::build(n, n, (_i, _j) => {
    rng.next_below(9).to_double() - 4.0
  })
  let g : RMat = Mat::build(n, n, (i, j) => {
    let mut s = 0.0
    for k in 0..<n {
      s = s + m.at(k, i) * m.at(k, j)
    }
    if i == j {
      s + n.to_double()
    } else {
      s
    }
  })
  g
}

///|
/// 兩組實數（排序後）之最大偏差
pub fn spec_dev(x0 : Array[Double], y0 : Array[Double]) -> Double {
  if x0.length() != y0.length() {
    return 1.0e30
  }
  let x = x0.copy()
  let y = y0.copy()
  sort_doubles(x)
  sort_doubles(y)
  let mut d = 0.0
  for i in 0..<x.length() {
    let e = absd(x[i] - y[i])
    if e > d {
      d = e
    }
  }
  d
}

// ---------------------------------------------------------------------------
// 【演算法 179】受計量之 Cholesky 與單邊 Jacobi SVD（N-22 之量測基礎）
//
// 與演算法 177 同一原則：逐行鏡射 realmat.mbt 之原版，只加 flop 計數。
// 忠實性同由義務以「輸出恰好相等」驗證。
// ---------------------------------------------------------------------------

///|
/// 受計量之 Cholesky（realmat.mbt cholesky 之孿生體）
pub fn ccholesky(a : RMat, c : Cost) -> RMat? {
  let n = a.mrows
  let l : RMat = Mat::zeros(n, n)
  for j in 0..<n {
    let mut s = a.at(j, j)
    for k in 0..<j {
      s = s - l.at(j, k) * l.at(j, k)
    }
    cflop(c, 2L * j.to_int64())
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
      cflop(c, 2L * j.to_int64() + 1L)
    }
  }
  Some(l)
}

///|
/// 受計量之單邊 Jacobi SVD（realmat.mbt svd_jacobi 之孿生體）
pub fn csvd_jacobi(
  a0 : RMat,
  sweeps : Int,
  c : Cost,
) -> (RMat, Array[Double], RMat) {
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
        // 三個內積，每個 m 次乘 + m 次加
        cflop(c, 6L * m.to_int64())
        off = off + absd(gamma)
        if absd(gamma) < 1.0e-15 {
          continue
        }
        let zeta = (beta - alpha) / (2.0 * gamma)
        let t = (if zeta >= 0.0 { 1.0 } else { -1.0 }) /
          (absd(zeta) + sqrt_newton(1.0 + zeta * zeta))
        let cc = 1.0 / sqrt_newton(1.0 + t * t)
        let s = cc * t
        cflop(c, 8L)
        for k in 0..<m {
          let x = u.at(k, i)
          let y = u.at(k, j)
          u.put(k, i, cc * x - s * y)
          u.put(k, j, s * x + cc * y)
        }
        for k in 0..<n {
          let x = v.at(k, i)
          let y = v.at(k, j)
          v.put(k, i, cc * x - s * y)
          v.put(k, j, s * x + cc * y)
        }
        cflop(c, 6L * (m + n).to_int64())
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
    cflop(c, 2L * m.to_int64())
    sig[j] = sqrt_newton(s)
    if sig[j] > 1.0e-300 {
      for i in 0..<m {
        u.put(i, j, u.at(i, j) / sig[j])
      }
      cflop(c, m.to_int64())
    }
  }
  // 依慣例將奇異值遞減排序（同時置換 U、V 之對應行）——
  // 此步不可省：省略後 U、V 之行序與原版不同，偽逆之累加次序隨之改變，
  // 浮點結果會在 1e-17 量級上分歧，孿生體即不再忠實。
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
// 【演算法 181】Kronecker 矩陣–向量積（不物化大矩陣）—— 快速變換之本體
//
// 【定義】給定因子 A₁,…,A_k（階 n₁,…,n_k），令 N = Πnᵢ。
//   直接法：物化 A₁⊗…⊗A_k（N² 元）再做矩陣向量積，成本 Θ(N²)。
//   模積法：逐一沿第 i 模作用 Aᵢ，成本 Σᵢ N·nᵢ。
//
// 【定理 181】兩法結果相同。
//   證：Kronecker 積可分解為 A₁⊗…⊗A_k = Π_i (I_{L_i} ⊗ Aᵢ ⊗ I_{R_i})，
//   其中 L_i = Π_{j<i} n_j、R_i = Π_{j>i} n_j（各因子作用於不同模，彼此交換）。
//   沿第 i 模之作用即左乘 (I ⊗ Aᵢ ⊗ I)，依序施行即得全積。∎
//
// 【推論 181-1（快速變換即結構律）】取 Aᵢ = H₂ = [[1,1],[1,−1]] 全體相同，
//   則 A₁⊗…⊗A_k = H_{2ᵏ}（Sylvester–Hadamard），而模積法即 FWHT 之蝶形。
//   成本 Σ N·2 = 2kN 對 N²，增益 N/(2k) = 2ᵏ/(2k)。
//   **故 FWHT 不是一個獨立演算法，而是本定理在 Kronecker 樹上的實例；
//   其 Θ(N log N) 相對 Θ(N²) 之優勢，就是結構律增益本身。**
//   同理 Cooley–Tukey 之 DFT_{nm} = P(DFT_n⊗I_m)T(I_n⊗DFT_m)Q 亦為本定理之實例
//   （多一個扭轉因子 T，因 DFT 之分解含置換與旋轉）。
// ---------------------------------------------------------------------------

///|
/// 受計量之稠密矩陣–向量積
pub fn cmatvec(c : Cost, a : RMat, x : Array[Double]) -> Array[Double] {
  let m = a.mrows
  let n = a.mcols
  cflop(c, 2L * (m * n).to_int64())
  Array::makei(m, i => {
    let mut s = 0.0
    for j in 0..<n {
      s = s + a.at(i, j) * x[j]
    }
    s
  })
}

///|
/// 【演算法 181】模積法：施行 A₁⊗…⊗A_k 於 x，全程不物化大矩陣
pub fn kron_matvec(
  c : Cost,
  factors : Array[RMat],
  x0 : Array[Double],
) -> Array[Double] {
  let k = factors.length()
  let mut total = 1
  for f in factors {
    total = total * f.mrows
  }
  let mut y = x0.copy()
  let mut left = 1
  for i in 0..<k {
    let a = factors[i]
    let n = a.mrows
    let right = total / (left * n)
    let z = Array::make(total, 0.0)
    for l in 0..<left {
      for r in 0..<right {
        for p in 0..<n {
          let mut s = 0.0
          for t in 0..<n {
            s = s + a.at(p, t) * y[(l * n + t) * right + r]
          }
          z[(l * n + p) * right + r] = s
        }
      }
    }
    // 本模之成本：left·right·n² 次乘 + 同數加
    cflop(c, 2L * (left * right * n * n).to_int64())
    y = z
    left = left * n
  }
  y
}

///|
/// 受計量之 FWHT（realmat.mbt fwht 之孿生體）
pub fn cfwht(x0 : Array[Double], c : Cost) -> Array[Double] {
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
    cflop(c, n.to_int64())
    len = len * 2
  }
  x
}

///|
/// H₂ = [[1,1],[1,−1]]
pub fn h2() -> RMat {
  Mat::build(2, 2, (i, j) => if i == 1 && j == 1 { -1.0 } else { 1.0 })
}

///|
/// 兩向量之最大偏差
pub fn vec_dev(x : Array[Double], y : Array[Double]) -> Double {
  if x.length() != y.length() {
    return 1.0e30
  }
  let mut d = 0.0
  for i in 0..<x.length() {
    let e = absd(x[i] - y[i])
    if e > d {
      d = e
    }
  }
  d
}

// ---------------------------------------------------------------------------
// 【演算法 183】受計量之 pinv / expm / sqrtm_spd（N-23、N-24 之量測基礎）
// 同 177／179 之原則：逐行鏡射原版，只加 flop 計數；忠實性由義務驗證。
// ---------------------------------------------------------------------------

///|
/// 受計量之 Moore–Penrose 偽逆
pub fn cpinv(a : RMat, tol : Double, c : Cost) -> RMat {
  let (u, s, v) = csvd_jacobi(a, 60, c)
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
  let sp : RMat = Mat::zeros(n, m)
  for k in 0..<n {
    if s[k] > thr {
      for i in 0..<n {
        for j in 0..<m {
          sp.put(i, j, sp.at(i, j) + v.at(i, k) * u.at(j, k) / s[k])
        }
      }
      cflop(c, 3L * (n * m).to_int64())
    }
  }
  sp
}

///|
/// 受計量之矩陣指數（縮放–平方 + 20 階 Taylor）
pub fn cexpm(a : RMat, c : Cost) -> RMat {
  let n = a.mrows
  let mut nrm = 0.0
  for i in 0..<n {
    let mut rs = 0.0
    for j in 0..<n {
      rs = rs + absd(a.at(i, j))
    }
    nrm = maxd(nrm, rs)
  }
  cflop(c, (n * n).to_int64())
  let mut s = 0
  let mut scale = 1.0
  while nrm * scale > 0.5 {
    scale = scale / 2.0
    s = s + 1
  }
  let b = a.scale(scale)
  let mut term : RMat = Mat::ident(n)
  let mut acc : RMat = Mat::ident(n)
  for k in 1..<21 {
    term = term.times(b).scale(1.0 / k.to_double())
    acc = acc.plus(term)
    // 一次 n³ 矩陣乘 + n² 縮放 + n² 加
    cflop(c, 2L * (n * n * n).to_int64() + 2L * (n * n).to_int64())
  }
  for _i in 0..<s {
    acc = acc.times(acc)
    cflop(c, 2L * (n * n * n).to_int64())
  }
  acc
}

///|
/// 受計量之對稱正定方根
pub fn csqrtm_spd(a : RMat, c : Cost) -> RMat {
  let n = a.mrows
  let (lam, q, _r) = cjacobi_eigen(a, 1.0e-12, 3000, c)
  cflop(c, 2L * (n * n * n).to_int64())
  Mat::build(n, n, (i, j) => {
    let mut acc = 0.0
    for k in 0..<n {
      acc = acc + q.at(i, k) * sqrt_newton(maxd(0.0, lam[k])) * q.at(j, k)
    }
    acc
  })
}

///|
/// 兩矩陣之最大元素偏差
pub fn mat_dev(x : RMat, y : RMat) -> Double {
  if x.mrows != y.mrows || x.mcols != y.mcols {
    return 1.0e30
  }
  let mut d = 0.0
  for i in 0..<x.mrows {
    for j in 0..<x.mcols {
      let e = absd(x.at(i, j) - y.at(i, j))
      if e > d {
        d = e
      }
    }
  }
  d
}

///|
/// Kronecker 和 A ⊞ B = A⊗I_m + I_n⊗B（N-24 之新組合子）
pub fn kron_sum(a : RMat, b : RMat) -> RMat {
  let n = a.mrows
  let m = b.mrows
  mkron(a, Mat::ident(m)).plus(mkron(Mat::ident(n), b))
}

// ---------------------------------------------------------------------------
// 【演算法 187】實化律（N-07）
//
// 【定義】ℂⁿ 視為 ℝ^{2n}：z = x + iy ↦ (x, y)。Hermitian 矩陣 H = P + iQ
//   （P = Re H 對稱、Q = Im H 反對稱）之實化為
//       ℜ(H) = [[P, −Q], [Q, P]]   （2n×2n 實對稱矩陣）
//
// 【定理 187-1】ℜ 為 ℝ-代數同態：ℜ(HK) = ℜ(H)ℜ(K)、ℜ(H+K) = ℜ(H)+ℜ(K)。
// 【定理 187-2】H Hermitian ⟺ ℜ(H) 實對稱；H 正定 ⟺ ℜ(H) 正定。
// 【定理 187-3（譜倍增）】spec_ℝ(ℜ(H)) = spec_ℂ(H)，每個特徵值重數加倍。
//   證：若 Hz = λz（λ ∈ ℝ，H Hermitian），z = x+iy，則 ℜ(H) 作用於
//   (x,y) 與 (−y,x) 皆得 λ 倍，兩者實線性獨立，故每個 λ 至少重數 2；
//   計維數 2n = Σ 2·(重數) 知恰為 2。∎
// 【定理 187-4】det ℜ(H) = |det H|²；H Hermitian 時 det H ∈ ℝ，故 = (det H)²。
// ---------------------------------------------------------------------------

///|
/// 複 Hermitian 矩陣之實化 ℜ(H) = [[P,−Q],[Q,P]]
pub fn realify_mat(h : CMat) -> RMat {
  let n = h.mrows
  Mat::build(2 * n, 2 * n, (i, j) => {
    let bi = i / n
    let bj = j / n
    let z = h.at(i % n, j % n)
    if bi == 0 && bj == 0 {
      z.cre
    } else if bi == 0 && bj == 1 {
      -z.cim
    } else if bi == 1 && bj == 0 {
      z.cim
    } else {
      z.cre
    }
  })
}

///|
/// 隨機 Hermitian 正定複矩陣 H = M*M + nI
pub fn rand_herm_pd(rng : Rng, n : Int) -> CMat {
  let m : CMat = Mat::build(n, n, (_i, _j) => {
    Cpx::mk(
      (rng.next_below(7) - 3).to_double(),
      (rng.next_below(7) - 3).to_double(),
    )
  })
  Mat::build(n, n, (i, j) => {
    let mut sr = 0.0
    let mut si = 0.0
    for k in 0..<n {
      // (conj m_ki) * m_kj
      let u = m.at(k, i)
      let v = m.at(k, j)
      sr = sr + u.cre * v.cre + u.cim * v.cim
      si = si + u.cre * v.cim - u.cim * v.cre
    }
    if i == j {
      Cpx::mk(sr + n.to_double(), 0.0)
    } else {
      Cpx::mk(sr, si)
    }
  })
}

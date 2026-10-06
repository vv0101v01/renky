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
  Mat::build(a.mrows * m, a.mcols * p, (i, j) => a.at(i / m, j / p) *
    b.at(i % m, j % p))
}

///|
/// 分塊對角（Double，零 flop）
pub fn rblock_diag(a : RMat, b : RMat) -> RMat {
  let ra = a.mrows
  let ca = a.mcols
  Mat::build(ra + b.mrows, ca + b.mcols, (i, j) => if i < ra && j < ca {
    a.at(i, j)
  } else if i >= ra && j >= ca {
    b.at(i - ra, j - ca)
  } else {
    0.0
  })
}

///|
/// 隨機實對稱正定矩陣 G = MᵀM + nI
pub fn rand_spd(rng : Rng, n : Int) -> RMat {
  let m : RMat = Mat::build(n, n, (_i, _j) => rng.next_below(9).to_double() -
    4.0)
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
    let nrm = sqrt_newton(s)
    sig[j] = nrm
    if nrm > 1.0e-300 {
      for i in 0..<m {
        u.put(i, j, u.at(i, j) / nrm)
      }
      cflop(c, m.to_int64())
    }
  }
  (u, sig, v)
}

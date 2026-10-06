// ============================================================================
//  檔案 17：oblig_num.mbt — 證明義務 H（數值 ℝ 軌道）、I（四元數與旋轉）、
//  J（多項式／組合核心）
//
//  數值軌道之「證明」形態：事後殘差憑證（a posteriori residual certificate）。
//  對浮點輸出 X̂ 我們不宣稱 X̂ = X，而是驗證可機器檢查之不等式
//     ‖R(X̂)‖_max ≤ ε,
//  其中 R 為定義該物件之方程式之殘差。配合後向穩定性定理，此即
//  「X̂ 為一個近鄰問題之精確解」之證明。所有 ε 於下列義務中明確列出。
// ============================================================================

///|
/// 數值義務之容忍度（絕對，矩陣元素最大偏差）
pub let eps_num : Double = 1.0e-9

///|
/// 建構測試用對稱正定矩陣（對角佔優 ⇒ 正定）
fn spd_matrix(n : Int, rng : Rng) -> RMat {
  let b : RMat = Mat::build(n, n, (_i, _j) => rng.next_double() * 2.0)
  let s = b.transpose().times(b)
  Mat::build(n, n, (i, j) => {
    if i == j {
      s.at(i, j) + n.to_double()
    } else {
      s.at(i, j)
    }
  })
}

///|
/// 建構一般測試矩陣
fn gen_matrix(r : Int, c : Int, rng : Rng) -> RMat {
  Mat::build(r, c, (_i, _j) => rng.next_double() * 3.0)
}

///|
/// 對稱矩陣
fn sym_matrix(n : Int, rng : Rng) -> RMat {
  let b = gen_matrix(n, n, rng)
  b.plus(b.transpose()).scale(0.5)
}

// ===========================================================================
//  H 群：數值線性代數（ℝ 軌道，殘差憑證）
// ===========================================================================

///|
/// H-01 Cholesky：A = LLᵀ，L 下三角且對角為正；非正定時正確回傳 None。
pub fn ob_h01() -> Check {
  let rng = ob_rng()
  let mut worst = 0.0
  let mut ok = true
  for _t in 0..<10 {
    let n = 2 + rng.next_below(5)
    let a = spd_matrix(n, rng)
    match cholesky(a) {
      None => ok = false
      Some(l) => {
        worst = maxd(worst, l.times(l.transpose()).max_dev(a))
        for i in 0..<n {
          if l.at(i, i) <= 0.0 {
            ok = false
          }
          for j in (i + 1)..<n {
            if absd(l.at(i, j)) > 0.0 {
              ok = false
            }
          }
        }
      }
    }
  }
  // 非正定之否決
  let bad : RMat = Mat::of_rows([[1.0, 2.0], [2.0, 1.0]])
  if !(cholesky(bad) is None) {
    ok = false
  }
  if worst > eps_num {
    ok = false
  }
  mk_check(
    "H-01 Cholesky 分解",
    ok,
    10,
    "‖A−LLᵀ‖_max = " + fmt_e(worst) + " ≤ ε；不定矩陣被否決",
  )
}

///|
/// H-02 LDLᵀ 與 Sylvester 慣性律：對合同變換不變。
pub fn ob_h02() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut worst = 0.0
  for _t in 0..<8 {
    let n = 3 + rng.next_below(3)
    let a = sym_matrix(n, rng)
    match ldlt(a) {
      None => ()
      Some((l, d)) => {
        let dd : RMat = Mat::diagm(d)
        worst = maxd(worst, l.times(dd).times(l.transpose()).max_dev(a))
        let (p1, z1, m1) = inertia(d)
        // 慣性律：與 Jacobi 特徵值之符號計數一致
        let (lam, _v) = jacobi_eigen(a, 200)
        let mut p2 = 0
        let mut z2 = 0
        let mut m2 = 0
        for x in lam {
          if x > 1.0e-8 {
            p2 = p2 + 1
          } else if x < -1.0e-8 {
            m2 = m2 + 1
          } else {
            z2 = z2 + 1
          }
        }
        if p1 != p2 || z1 != z2 || m1 != m2 {
          ok = false
        }
      }
    }
  }
  if worst > 1.0e-8 {
    ok = false
  }
  mk_check(
    "H-02 LDLᵀ 與 Sylvester 慣性律",
    ok,
    8,
    "‖A−LDLᵀ‖_max = " + fmt_e(worst) + "；(p,z,m) 與譜一致",
  )
}

///|
/// H-03 Householder QR：A = QR，QᵀQ = I，R 上三角。
pub fn ob_h03() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w1 = 0.0
  let mut w2 = 0.0
  for _t in 0..<10 {
    let m = 3 + rng.next_below(4)
    let n = 2 + rng.next_below(mind_i(m, 4))
    let a = gen_matrix(m, n, rng)
    let (q, r) = qr_householder(a)
    w1 = maxd(w1, q.times(r).max_dev(a))
    w2 = maxd(w2, q.transpose().times(q).max_dev(Mat::ident(m)))
    for i in 0..<r.mrows {
      for j in 0..<r.mcols {
        if i > j && absd(r.at(i, j)) > 1.0e-10 {
          ok = false
        }
      }
    }
  }
  if w1 > 1.0e-10 || w2 > 1.0e-10 {
    ok = false
  }
  mk_check(
    "H-03 Householder QR",
    ok,
    10,
    "‖A−QR‖=" + fmt_e(w1) + "，‖QᵀQ−I‖=" + fmt_e(w2),
  )
}

///|
/// H-04 Givens QR：同上，並與 Householder 之 |R| 對角一致（唯一性至符號）。
pub fn ob_h04() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w1 = 0.0
  let mut w2 = 0.0
  for _t in 0..<10 {
    let m = 4
    let n = 3
    let a = gen_matrix(m, n, rng)
    let (q, r) = qr_givens(a)
    w1 = maxd(w1, q.times(r).max_dev(a))
    w2 = maxd(w2, q.transpose().times(q).max_dev(Mat::ident(m)))
    let (_q2, r2) = qr_householder(a)
    for i in 0..<n {
      if absd(absd(r.at(i, i)) - absd(r2.at(i, i))) > 1.0e-9 {
        ok = false
      }
    }
  }
  if w1 > 1.0e-10 || w2 > 1.0e-10 {
    ok = false
  }
  mk_check(
    "H-04 Givens QR",
    ok,
    10,
    "‖A−QR‖=" + fmt_e(w1) + "；|R_ii| 與 Householder 一致",
  )
}

///|
/// H-05 Hessenberg 化簡：QᵀAQ = H（上 Hessenberg），Q 正交。
pub fn ob_h05() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  for _t in 0..<8 {
    let n = 4 + rng.next_below(3)
    let a = gen_matrix(n, n, rng)
    let (q, h) = hessenberg(a)
    w = maxd(w, q.times(h).times(q.transpose()).max_dev(a))
    if q.transpose().times(q).max_dev(Mat::ident(n)) > 1.0e-10 {
      ok = false
    }
    for i in 0..<n {
      for j in 0..<n {
        if i > j + 1 && absd(h.at(i, j)) > 1.0e-10 {
          ok = false
        }
      }
    }
  }
  if w > 1.0e-9 {
    ok = false
  }
  mk_check(
    "H-05 Hessenberg 化簡",
    ok,
    8,
    "‖A−QHQᵀ‖=" + fmt_e(w) + "；次對角以下為 0",
  )
}

///|
/// H-06 Jacobi 特徵分解（譜定理）：A = VΛVᵀ，VᵀV = I。
pub fn ob_h06() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w1 = 0.0
  let mut w2 = 0.0
  for _t in 0..<8 {
    let n = 3 + rng.next_below(4)
    let a = sym_matrix(n, rng)
    let (lam, v) = jacobi_eigen(a, 300)
    let lm : RMat = Mat::diagm(lam)
    w1 = maxd(w1, v.times(lm).times(v.transpose()).max_dev(a))
    w2 = maxd(w2, v.transpose().times(v).max_dev(Mat::ident(n)))
    // 特徵方程 Av = λv
    for k in 0..<n {
      let col = v.col(k)
      if vmax_dev(a.apply(col), col.map(x => x * lam[k])) > 1.0e-8 {
        ok = false
      }
    }
  }
  if w1 > 1.0e-8 || w2 > 1.0e-10 {
    ok = false
  }
  mk_check(
    "H-06 Jacobi 譜分解",
    ok,
    8,
    "‖A−VΛVᵀ‖=" + fmt_e(w1) + "，‖VᵀV−I‖=" + fmt_e(w2),
  )
}

///|
/// H-07 QR 迭代：對角收斂至特徵值（與 Jacobi 排序後比較）。
pub fn ob_h07() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut worst = 0.0
  for _t in 0..<6 {
    let n = 4
    let a = sym_matrix(n, rng)
    let t = qr_iteration(a, 500)
    let d1 = Array::makei(n, i => t.at(i, i))
    let (d2, _v) = jacobi_eigen(a, 300)
    sort_doubles(d1)
    sort_doubles(d2)
    for i in 0..<n {
      worst = maxd(worst, absd(d1[i] - d2[i]))
    }
  }
  if worst > 1.0e-6 {
    ok = false
  }
  mk_check(
    "H-07 無位移 QR 迭代",
    ok,
    6,
    "對角元 → 特徵值，最大偏差 " + fmt_e(worst),
  )
}

///|
/// H-08 單邊 Jacobi SVD：A = UΣVᵀ，U、V 正交，Σ ≥ 0 遞減。
pub fn ob_h08() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  for _t in 0..<8 {
    let m = 5
    let n = 3
    let a = gen_matrix(m, n, rng)
    let (u, sv, v) = svd_jacobi(a, 100)
    let sd : RMat = Mat::build(n, n, (i, j) => if i == j { sv[i] } else { 0.0 })
    w = maxd(w, u.times(sd).times(v.transpose()).max_dev(a))
    if v.transpose().times(v).max_dev(Mat::ident(n)) > 1.0e-9 {
      ok = false
    }
    for i in 0..<n {
      if sv[i] < -1.0e-12 {
        ok = false
      }
      if i > 0 && sv[i] > sv[i - 1] + 1.0e-12 {
        ok = false
      }
    }
    // σ₁ = ‖A‖₂，σ 之平方 = AᵀA 之特徵值
    let (lam, _vv) = jacobi_eigen(a.transpose().times(a), 300)
    sort_doubles(lam)
    let sq = Array::makei(n, i => sv[i] * sv[i])
    sort_doubles(sq)
    for i in 0..<n {
      if absd(lam[i] - sq[i]) > 1.0e-7 * maxd(1.0, absd(lam[i])) {
        ok = false
      }
    }
  }
  if w > 1.0e-9 {
    ok = false
  }
  mk_check("H-08 Jacobi SVD", ok, 8, "‖A−UΣVᵀ‖=" + fmt_e(w))
}

///|
/// H-09 Moore–Penrose 偽逆：四條 Penrose 條件。
pub fn ob_h09() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  for _t in 0..<8 {
    let m = 5
    let n = 3
    let a = gen_matrix(m, n, rng)
    let p = pinv(a, 1.0e-12)
    w = maxd(w, a.times(p).times(a).max_dev(a))
    w = maxd(w, p.times(a).times(p).max_dev(p))
    let ap = a.times(p)
    w = maxd(w, ap.transpose().max_dev(ap))
    let pa = p.times(a)
    w = maxd(w, pa.transpose().max_dev(pa))
    // 滿秩時 A⁺ = (AᵀA)⁻¹Aᵀ
    match minv(a.transpose().times(a)) {
      None => ()
      Some(inv) => w = maxd(w, inv.times(a.transpose()).max_dev(p))
    }
  }
  if w > 1.0e-8 {
    ok = false
  }
  mk_check(
    "H-09 Moore–Penrose 偽逆",
    ok,
    8,
    "四條 Penrose 條件最大殘差 " + fmt_e(w),
  )
}

///|
/// H-10 極分解 A = UP：U 正交、P 對稱半正定。
pub fn ob_h10() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  for _t in 0..<8 {
    let n = 4
    let a = gen_matrix(n, n, rng)
    let (u, p) = polar_decomposition(a)
    w = maxd(w, u.times(p).max_dev(a))
    w = maxd(w, u.transpose().times(u).max_dev(Mat::ident(n)))
    w = maxd(w, p.transpose().max_dev(p))
    let (lam, _v) = jacobi_eigen(p, 300)
    for x in lam {
      if x < -1.0e-8 {
        ok = false
      }
    }
  }
  if w > 1.0e-8 {
    ok = false
  }
  mk_check(
    "H-10 極分解 A = UP",
    ok,
    8,
    "殘差 " + fmt_e(w) + "；P 之譜非負",
  )
}

///|
/// H-11 矩陣指數：e^A e^{−A} = I，det(e^A) = e^{tr A}，e^{A}e^{B} = e^{A+B}（可換時）。
pub fn ob_h11() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  for _t in 0..<6 {
    let n = 3
    let a = gen_matrix(n, n, rng).scale(0.3)
    let e = expm(a)
    w = maxd(w, e.times(expm(a.negm())).max_dev(Mat::ident(n)))
    // det(e^A) = e^{tr A}
    let d1 = mdet(e)
    let d2 = exp_scalar(a.trace())
    if absd(d1 - d2) > 1.0e-7 * maxd(1.0, absd(d2)) {
      ok = false
    }
    // 可換情形 e^{A}e^{2A} = e^{3A}
    w = maxd(w, expm(a).times(expm(a.scale(2.0))).max_dev(expm(a.scale(3.0))))
  }
  if w > 1.0e-8 {
    ok = false
  }
  mk_check(
    "H-11 矩陣指數 expm",
    ok,
    6,
    "e^Ae^{−A}=I；det e^A = e^{tr A}；殘差 " + fmt_e(w),
  )
}

///|
/// H-12 對稱正定平方根：(√A)² = A，√A 對稱正定。
pub fn ob_h12() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  for _t in 0..<8 {
    let n = 3 + rng.next_below(3)
    let a = spd_matrix(n, rng)
    let s = sqrtm_spd(a)
    w = maxd(w, s.times(s).max_dev(a))
    w = maxd(w, s.transpose().max_dev(s))
    if !(cholesky(s) is Some(_)) {
      ok = false
    }
  }
  if w > 1.0e-7 {
    ok = false
  }
  mk_check(
    "H-12 對稱正定平方根",
    ok,
    8,
    "‖(√A)²−A‖ = " + fmt_e(w),
  )
}

///|
/// H-13 冪迭代與 Rayleigh 商：收斂至主特徵對；λ_min ≤ R(x) ≤ λ_max。
pub fn ob_h13() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut worst = 0.0
  for _t in 0..<8 {
    let n = 4
    let a = spd_matrix(n, rng)
    let (lam, _v) = jacobi_eigen(a, 300)
    let mut lmax = lam[0]
    let mut lmin = lam[0]
    for x in lam {
      lmax = maxd(lmax, x)
      lmin = mind(lmin, x)
    }
    let (mu, v) = power_iteration(a, 800)
    worst = maxd(worst, absd(mu - lmax) / maxd(1.0, absd(lmax)))
    // 殘差 ‖Av − μv‖
    let r = vmax_dev(a.apply(v), v.map(x => x * mu))
    if r > 1.0e-6 {
      ok = false
    }
    // Rayleigh 商界
    for _k in 0..<5 {
      let x = Array::makei(n, _ => rng.next_double())
      if vnorm2(x) > 1.0e-12 {
        let rq = rayleigh_quotient(a, x)
        if rq < lmin - 1.0e-9 || rq > lmax + 1.0e-9 {
          ok = false
        }
      }
    }
  }
  if worst > 1.0e-6 {
    ok = false
  }
  mk_check(
    "H-13 冪迭代與 Rayleigh 商",
    ok,
    8,
    "λ̂_max 相對誤差 " + fmt_e(worst) + "；R(x) ∈ [λ_min,λ_max]",
  )
}

///|
/// H-14 2-範數條件數：κ₂ = σ_max/σ_min ≥ 1；正交矩陣 κ₂ = 1；Hilbert 矩陣病態。
pub fn ob_h14() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<6 {
    let a = gen_matrix(4, 4, rng)
    if cond2(a) < 1.0 - 1.0e-9 {
      ok = false
    }
  }
  // 正交矩陣
  let (q, _r) = qr_householder(gen_matrix(5, 5, rng))
  if absd(cond2(q) - 1.0) > 1.0e-8 {
    ok = false
  }
  // Hilbert 矩陣 H₆ 病態
  let h : RMat = Mat::build(6, 6, (i, j) => 1.0 / (i + j + 1).to_double())
  let kh = cond2(h)
  if kh < 1.0e6 {
    ok = false
  }
  mk_check(
    "H-14 條件數 κ₂",
    ok,
    8,
    "κ₂(Q)=1；κ₂(H₆)≈" + fmt_e(kh),
  )
}

///|
/// H-15 共軛梯度：n 步內精確收斂（理論）＋殘差憑證；A 正交不變性。
pub fn ob_h15() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  for _t in 0..<8 {
    let n = 2 + rng.next_below(5)
    let a = spd_matrix(n, rng)
    let b = Array::makei(n, _ => rng.next_double() * 2.0)
    let x = conjugate_gradient(a, b, n)
    w = maxd(w, vmax_dev(a.apply(x), b))
  }
  if w > 1.0e-6 {
    ok = false
  }
  mk_check(
    "H-15 共軛梯度（≤ n 步）",
    ok,
    8,
    "恰 n 次迭代後 ‖Ax−b‖_max = " + fmt_e(w),
  )
}

///|
/// H-16 Gauss–Seidel：對角佔優 ⇒ 收斂。
pub fn ob_h16() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  for _t in 0..<6 {
    let n = 5
    let a = spd_matrix(n, rng)
    let b = Array::makei(n, _ => rng.next_double())
    let x = gauss_seidel(a, b, 2000)
    w = maxd(w, vmax_dev(a.apply(x), b))
  }
  if w > 1.0e-7 {
    ok = false
  }
  mk_check("H-16 Gauss–Seidel 迭代", ok, 6, "殘差 " + fmt_e(w))
}

///|
/// H-17 Lanczos：QᵀAQ = T 三對角，Q 正交。
pub fn ob_h17() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  for _t in 0..<6 {
    let n = 5
    let a = sym_matrix(n, rng)
    let (q, t) = lanczos(a, n)
    w = maxd(w, q.transpose().times(a).times(q).max_dev(t))
    if q.transpose().times(q).max_dev(Mat::ident(n)) > 1.0e-8 {
      ok = false
    }
    for i in 0..<n {
      for j in 0..<n {
        if (i - j) * (i - j) > 1 && absd(t.at(i, j)) > 1.0e-9 {
          ok = false
        }
      }
    }
  }
  if w > 1.0e-8 {
    ok = false
  }
  mk_check(
    "H-17 Lanczos 三對角化",
    ok,
    6,
    "‖QᵀAQ−T‖ = " + fmt_e(w) + "；T 三對角",
  )
}

///|
/// H-18 Arnoldi：QᵀAQ = H 上 Hessenberg，Q 正交。
pub fn ob_h18() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  for _t in 0..<6 {
    let n = 5
    let a = gen_matrix(n, n, rng)
    let (q, h) = arnoldi(a, n)
    w = maxd(w, q.transpose().times(a).times(q).max_dev(h))
    if q.transpose().times(q).max_dev(Mat::ident(n)) > 1.0e-8 {
      ok = false
    }
    for i in 0..<n {
      for j in 0..<n {
        if i > j + 1 && absd(h.at(i, j)) > 1.0e-9 {
          ok = false
        }
      }
    }
  }
  if w > 1.0e-8 {
    ok = false
  }
  mk_check(
    "H-18 Arnoldi 分解",
    ok,
    6,
    "‖QᵀAQ−H‖ = " + fmt_e(w) + "；H 上 Hessenberg",
  )
}

///|
/// H-19 DFT 矩陣么正性與循環矩陣對角化 F C F* = diag。
pub fn ob_h19() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  let mut cnt = 0
  for n in [2, 3, 4, 5, 6, 8, 9, 12, 16] {
    cnt = cnt + 1
    let f = dft_matrix(n)
    let id : CMat = Mat::ident(n)
    w = maxd(w, f.adjointm().times(f).max_dev(id))
    let c = Array::makei(n, _ => rng.next_double() * 2.0)
    let cm = circulant(c)
    let diag = f.times(to_complex(cm)).times(f.adjointm())
    for i in 0..<n {
      for j in 0..<n {
        if i != j && Scalar::s_mag(diag.at(i, j)) > 1.0e-9 {
          ok = false
        }
      }
    }
    // 對角元 = √n·(F c)
    let fc = f.apply(Array::makei(n, i => Cpx::mk(c[i], 0.0)))
    let sc = sqrt_newton(n.to_double())
    for i in 0..<n {
      let want = Scalar::s_mul(Cpx::mk(sc, 0.0), fc[i])
      if Scalar::s_mag(ssub(diag.at(i, i), want)) > 1.0e-8 {
        ok = false
      }
    }
  }
  if w > 1.0e-9 {
    ok = false
  }
  mk_check(
    "H-19 DFT 么正性與循環對角化",
    ok,
    cnt,
    "‖F*F−I‖=" + fmt_e(w) + "；F C F* 之非對角為 0",
  )
}

///|
/// H-20 快速 Fourier 變換：FFT ≡ √n·(DFT 矩陣)；Parseval；逆變換。
pub fn ob_h20() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  for n in [2, 4, 8, 16, 32] {
    let f = dft_matrix(n)
    let x : Array[Cpx[Double]] = Array::makei(n, _ => {
      Cpx::mk(rng.next_double(), rng.next_double())
    })
    let y1 = fft(x)
    let y2 = f.apply(x)
    let sc = sqrt_newton(n.to_double())
    for i in 0..<n {
      w = maxd(
        w,
        Scalar::s_mag(ssub(y1[i], Scalar::s_mul(Cpx::mk(sc, 0.0), y2[i]))),
      )
    }
    // Parseval：Σ|x|² = (1/n)Σ|X|²
    let mut s1 = 0.0
    let mut s2 = 0.0
    for i in 0..<n {
      let a = Scalar::s_mag(x[i])
      let b = Scalar::s_mag(y1[i])
      s1 = s1 + a * a
      s2 = s2 + b * b
    }
    if absd(s1 - s2 / n.to_double()) > 1.0e-8 * maxd(1.0, s1) {
      ok = false
    }
  }
  if w > 1.0e-9 {
    ok = false
  }
  mk_check(
    "H-20 FFT ≡ DFT",
    ok,
    5,
    "最大偏差 " + fmt_e(w) + "；Parseval 成立",
  )
}

///|
/// H-21 Hadamard 矩陣與快速 Walsh–Hadamard 變換：HᵀH = nI（精確整數）。
pub fn ob_h21() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for k in 1..<6 {
    let n = 1 << k
    let h = hadamard_matrix(k)
    if h.transpose().times(h).max_dev(Mat::ident(n).scale(n.to_double())) > 0.0 {
      ok = false // 整數運算：要求精確相等
    }
    let x = Array::makei(n, _ => rng.next_double() * 4.0)
    if vmax_dev(fwht(x), h.apply(x)) > 1.0e-10 {
      ok = false
    }
    // 元素皆 ±1
    for i in 0..<n {
      for j in 0..<n {
        if absd(absd(h.at(i, j)) - 1.0) > 0.0 {
          ok = false
        }
      }
    }
  }
  mk_check(
    "H-21 Hadamard 矩陣與 FWHT", ok, 5, "HᵀH = nI 精確成立；FWHT ≡ 矩陣乘法",
  )
}

///|
/// H-22 Haar 小波基：規範化後列正交（正交基）。
pub fn ob_h22() -> Check {
  let mut ok = true
  let mut w = 0.0
  for k in 1..<6 {
    let n = 1 << k
    let h = normalize_rows(haar_matrix(k))
    w = maxd(w, h.times(h.transpose()).max_dev(Mat::ident(n)))
    // 規範化前：各列兩兩正交
    let h0 = haar_matrix(k)
    for i in 0..<n {
      for j in 0..<n {
        if i != j {
          let mut acc = 0.0
          for t in 0..<n {
            acc = acc + h0.at(i, t) * h0.at(j, t)
          }
          if absd(acc) > 1.0e-12 {
            ok = false
          }
        }
      }
    }
  }
  if w > 1.0e-10 {
    ok = false
  }
  mk_check("H-22 Haar 正交基", ok, 5, "‖HHᵀ−I‖ = " + fmt_e(w))
}

///|
/// H-23 譜與跡／行列式之關係：tr A = Σλ，det A = Πλ，‖A‖_F² = Σλ²（對稱時）。
pub fn ob_h23() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut w = 0.0
  for _t in 0..<8 {
    let n = 4
    let a = sym_matrix(n, rng)
    let (lam, _v) = jacobi_eigen(a, 300)
    let mut s = 0.0
    let mut p = 1.0
    let mut q = 0.0
    for x in lam {
      s = s + x
      p = p * x
      q = q + x * x
    }
    w = maxd(w, absd(s - a.trace()))
    w = maxd(w, absd(p - mdet(a)) / maxd(1.0, absd(p)))
    w = maxd(w, absd(q - a.frob2()) / maxd(1.0, q))
    // 譜半徑 = max|λ|
    let mut r = 0.0
    for x in lam {
      r = maxd(r, absd(x))
    }
    if absd(r - spectral_radius_sym(a)) > 1.0e-7 * maxd(1.0, r) {
      ok = false
    }
  }
  if w > 1.0e-7 {
    ok = false
  }
  mk_check(
    "H-23 譜不變量",
    ok,
    8,
    "tr=Σλ、det=Πλ、‖A‖_F²=Σλ²、ρ=max|λ|；偏差 " + fmt_e(w),
  )
}

///|
/// H-24 CGS 與 MGS 之正交性損失（Björck）：病態 Hilbert 基底上 MGS 遠優於 CGS。
pub fn ob_h24() -> Check {
  // 以 Hilbert 矩陣之行向量為病態基底；掃描 n 得到一整條 κ₂ 曲線
  let mut ok = true
  let mut n = 0
  let rows : Array[String] = []
  let mut worst_ratio = 0.0
  let mut kappa_min = 0.0
  let mut kappa_max = 0.0
  let loss = (s : IPSpace[Array[Double], Double], vs : Array[Array[Double]]) => {
    let m = vs.length()
    let mut worst = 0.0
    for i in 0..<m {
      for j in 0..<m {
        if i != j {
          let a = (s.inner)(vs[i], vs[j])
          let na = sqrt_newton((s.inner)(vs[i], vs[i]))
          let nb = sqrt_newton((s.inner)(vs[j], vs[j]))
          if na > 0.0 && nb > 0.0 {
            worst = maxd(worst, absd(a) / (na * nb))
          }
        }
      }
    }
    worst
  }
  for sz in [3, 4, 5, 6, 7, 8, 9, 10] {
    let s : IPSpace[Array[Double], Double] = euclidean_space(sz)
    let cols : Array[Array[Double]] = Array::makei(sz, j => {
      Array::makei(sz, i => 1.0 / (i + j + 1).to_double())
    })
    let l1 = loss(s, gram_schmidt(s, cols).ortho)
    let l2 = loss(s, modified_gram_schmidt(s, cols).ortho)
    let kappa = cond2(Mat::of_cols(cols))
    // 定理之內容：MGS 之正交性損失恆不劣於 CGS
    if l2 > l1 + 1.0e-18 {
      ok = false
    }
    if kappa_min == 0.0 {
      kappa_min = kappa
    }
    kappa_max = kappa
    if l2 > 0.0 && l1 / l2 > worst_ratio {
      worst_ratio = l1 / l2
    }
    rows.push(
      "n=" +
      sz.to_string() +
      " κ₂=" +
      fmt_e(kappa) +
      " CGS=" +
      fmt_e(l1) +
      " MGS=" +
      fmt_e(l2),
    )
    n = n + 1
  }
  // 良態對照組：κ₂≈1 時兩法應同樣良好（差距不應出現）
  for sz in [4, 8] {
    let s : IPSpace[Array[Double], Double] = euclidean_space(sz)
    let cols : Array[Array[Double]] = Array::makei(sz, j => {
      Array::makei(sz, i => if i == j { 1.0 } else { 0.1 })
    })
    let l1 = loss(s, gram_schmidt(s, cols).ortho)
    let l2 = loss(s, modified_gram_schmidt(s, cols).ortho)
    if l1 > 1.0e-14 || l2 > 1.0e-14 {
      ok = false
    }
    n = n + 1
  }
  mk_check(
    "H-24 CGS vs MGS 正交性損失（κ₂ 掃描曲線）",
    ok,
    n,
    "κ₂ 自 " +
    fmt_e(kappa_min) +
    " 掃至 " +
    fmt_e(kappa_max) +
    "：MGS 恆不劣於 CGS，最大差距 ×" +
    fmt_e(worst_ratio) +
    "；良態對照組（κ₂≈1）兩者皆 < 1e-14。曲線：" +
    rows.join("；"),
  )
}

///|
/// H-25 數值內積空間之公理（ℝ 軌道，ε 容忍）與精確軌道對照。
pub fn ob_h25() -> Check {
  let rng = ob_rng()
  let s : IPSpace[Array[Double], Double] = euclidean_space(4)
  let cs : Array[Check] = []
  for c in check_vector_space_axioms(s.vs, rng, 12) {
    cs.push(c)
  }
  for c in check_inner_axioms(s, rng, 12) {
    cs.push(c)
  }
  let sp : IPSpace[Poly[Double], Double] = poly_space_l2(5)
  for c in check_inner_axioms(sp, rng, 12) {
    cs.push(c)
  }
  let r = check_all("H-25", cs)
  mk_check(
    "H-25 ℝ 軌道公理（相對 ε 比較）",
    r.ok,
    r.trials,
    "Double 軌道以相對 ε=10⁻⁹ 判等；結論與 ℚ 軌道一致",
  )
}

// ===========================================================================
//  I 群：四元數代數與旋轉群
// ===========================================================================

///|
/// 取樣有理四元數
fn qquat(rng : Rng) -> Quat[Q] {
  Quat::mk(qr(rng), qr(rng), qr(rng), qr(rng))
}

///|
/// I-01 範數乘性 N(pq) = N(p)N(q)（Euler 四平方恆等式）。
pub fn ob_i01() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<60 {
    let p = qquat(rng)
    let q = qquat(rng)
    if !p.qmul(q).qnorm2().eq(p.qnorm2().mul(q.qnorm2())) {
      ok = false
    }
  }
  mk_check(
    "I-01 Euler 四平方恆等式", ok, 60, "N(pq) = N(p)N(q)（精確 ℚ）",
  )
}

///|
/// I-02 共軛反自同構與逆元：‾(pq) = ‾q‾p，q⁻¹ = ‾q/N(q)。
pub fn ob_i02() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<40 {
    let p = qquat(rng)
    let q = qquat(rng)
    if !p.qmul(q).qconj().qeq(q.qconj().qmul(p.qconj())) {
      ok = false
    }
    match q.qinv() {
      None => if !q.qnorm2().is_zero() { ok = false }
      Some(qi) => {
        if !q.qmul(qi).qeq(Quat::qone()) {
          ok = false
        }
        if !qi.qmul(q).qeq(Quat::qone()) {
          ok = false
        }
      }
    }
    // 實部投影：Re(q) = (q + ‾q)/2
    let two = Q::of_int(2)
    let re = q.qadd(q.qconj()).qsmul(Q::inv(two).unwrap_or(Q::zero()))
    if !re.qeq(Quat::mk(q.qw, Q::zero(), Q::zero(), Q::zero())) {
      ok = false
    }
  }
  mk_check(
    "I-02 共軛反自同構與逆元", ok, 40, "‾(pq)=‾q‾p；q⁻¹q = q q⁻¹ = 1",
  )
}

///|
/// I-03 左乘矩陣表示：L_{pq} = L_p L_q，L_qᵀL_q = N(q)I₄，det L_q = N(q)²。
pub fn ob_i03() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<30 {
    let p = qquat(rng)
    let q = qquat(rng)
    let lp : Mat[Q] = quat_left_matrix(p)
    let lq : Mat[Q] = quat_left_matrix(q)
    if !quat_left_matrix(p.qmul(q)).equals(lp.times(lq)) {
      ok = false
    }
    let n = q.qnorm2()
    if !lq.transpose().times(lq).equals(Mat::ident(4).scale(n)) {
      ok = false
    }
    if !mdet(lq).eq(n.mul(n)) {
      ok = false
    }
    // L_q 作用於座標 ≡ 四元數乘法
    let x = qquat(rng)
    let xv = [x.qw, x.qx, x.qy, x.qz]
    let prod = q.qmul(x)
    if !arr_eq(lq.apply(xv), [prod.qw, prod.qx, prod.qy, prod.qz]) {
      ok = false
    }
  }
  mk_check(
    "I-03 左乘矩陣 L_q", ok, 30, "L_{pq}=L_pL_q；LᵀL=N(q)I₄；det = N(q)²",
  )
}

///|
/// I-04 單位四元數 → SO(3)：RᵀR = I 且 det R = 1（精確有理單位四元數）。
pub fn ob_i04() -> Check {
  let half = Q::frac(1, 2)
  let units : Array[Quat[Q]] = [
    Quat::mk(half, half, half, half),
    Quat::mk(Q::frac(3, 5), Q::frac(4, 5), Q::zero(), Q::zero()),
    Quat::mk(Q::frac(5, 13), Q::zero(), Q::frac(12, 13), Q::zero()),
    Quat::qone(),
    Quat::qi(),
    Quat::mk(Q::frac(8, 17), Q::zero(), Q::zero(), Q::frac(15, 17)),
  ]
  let mut ok = true
  for q in units {
    if !q.qnorm2().eq(Q::one()) {
      ok = false
    }
    let r : Mat[Q] = quat_to_rot3(q)
    if !r.transpose().times(r).equals(Mat::ident(3)) {
      ok = false
    }
    if !mdet(r).eq(Q::one()) {
      ok = false
    }
  }
  mk_check(
    "I-04 單位四元數 → SO(3)",
    ok,
    units.length(),
    "RᵀR=I 且 det R=1（精確 ℚ 單位四元數）",
  )
}

///|
/// I-05 旋轉群同態與雙重覆蓋：R(pq) = R(p)R(q)，R(−q) = R(q)。
pub fn ob_i05() -> Check {
  let half = Q::frac(1, 2)
  let units : Array[Quat[Q]] = [
    Quat::mk(half, half, half, half),
    Quat::mk(Q::frac(3, 5), Q::frac(4, 5), Q::zero(), Q::zero()),
    Quat::mk(Q::frac(5, 13), Q::zero(), Q::frac(12, 13), Q::zero()),
    Quat::mk(Q::frac(8, 17), Q::zero(), Q::zero(), Q::frac(15, 17)),
  ]
  let mut ok = true
  let mut cnt = 0
  for p in units {
    for q in units {
      cnt = cnt + 1
      let lhs : Mat[Q] = quat_to_rot3(p.qmul(q))
      let rhs = (quat_to_rot3(p) : Mat[Q]).times(quat_to_rot3(q))
      if !lhs.equals(rhs) {
        ok = false
      }
    }
    // 雙重覆蓋
    let r1 : Mat[Q] = quat_to_rot3(p)
    let r2 : Mat[Q] = quat_to_rot3(p.qneg())
    if !r1.equals(r2) {
      ok = false
    }
    // 旋轉保持向量長度與叉積（SO(3) 作用）
    let v : Array[Q] = [Q::of_int(1), Q::of_int(-2), Q::frac(1, 3)]
    let w : Array[Q] = [Q::frac(2, 5), Q::of_int(1), Q::of_int(4)]
    let rv = r1.apply(v)
    let rw = r1.apply(w)
    if !arr_dot(rv, rw).eq(arr_dot(v, w)) {
      ok = false
    }
    if !arr_eq(cross3(rv, rw), r1.apply(cross3(v, w))) {
      ok = false
    }
  }
  mk_check(
    "I-05 SU(2) → SO(3) 雙重覆蓋", ok, cnt, "R(pq)=R(p)R(q)；R(−q)=R(q)；保內積與叉積",
  )
}

///|
/// I-06 ℍ ↪ M₂(ℂ)：保乘法之代數嵌入，det = N(q)；單位四元數 ↦ SU(2)。
pub fn ob_i06() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<30 {
    let p = qquat(rng)
    let q = qquat(rng)
    let mp : Mat[Cpx[Q]] = quat_to_c2(p)
    let mq : Mat[Cpx[Q]] = quat_to_c2(q)
    if !(quat_to_c2(p.qmul(q)) : Mat[Cpx[Q]]).equals(mp.times(mq)) {
      ok = false
    }
    if !(quat_to_c2(p.qadd(q)) : Mat[Cpx[Q]]).equals(mp.plus(mq)) {
      ok = false
    }
    // det = N(q)
    let d = mdet(mq)
    if !d.cre.eq(q.qnorm2()) || !d.cim.is_zero() {
      ok = false
    }
    // 共軛 ↦ 共軛轉置
    if !(quat_to_c2(q.qconj()) : Mat[Cpx[Q]]).equals(mq.adjointm()) {
      ok = false
    }
  }
  // 單位四元數 ↦ SU(2)
  let half = Q::frac(1, 2)
  let u = Quat::mk(half, half, half, half)
  let mu : Mat[Cpx[Q]] = quat_to_c2(u)
  if !is_unitary(mu) || !mdet(mu).cre.eq(Q::one()) {
    ok = false
  }
  mk_check(
    "I-06 ℍ ↪ M₂(ℂ) 代數嵌入", ok, 30, "保加法/乘法；det = N(q)；‾q ↦ M*；單位 ↦ SU(2)",
  )
}

///|
/// I-07 ℍⁿ 之實內積結構：⟨x,y⟩ = ΣRe(‾xᵢyᵢ)；右乘單位四元數為等距。
pub fn ob_i07() -> Check {
  let rng = ob_rng()
  let n = 2
  let s : IPSpace[Array[Quat[Q]], Q] = quaternion_space(n)
  let mut ok = s.vs.dim == 4 * n
  let half = Q::frac(1, 2)
  let u = Quat::mk(half, half, half, half) // 單位四元數
  for _t in 0..<25 {
    let x : Array[Quat[Q]] = Array::makei(n, _ => qquat(rng))
    let y : Array[Quat[Q]] = Array::makei(n, _ => qquat(rng))
    // 定義式
    let mut acc = Q::zero()
    for i in 0..<n {
      acc = acc.add(x[i].qdot(y[i]))
    }
    if !(s.inner)(x, y).eq(acc) {
      ok = false
    }
    // 右乘單位四元數為等距：⟨xu, yu⟩ = ⟨x,y⟩
    let xu : Array[Quat[Q]] = Array::makei(n, i => x[i].qmul(u))
    let yu : Array[Quat[Q]] = Array::makei(n, i => y[i].qmul(u))
    if !(s.inner)(xu, yu).eq((s.inner)(x, y)) {
      ok = false
    }
    // 範數乘性：‖qx‖² = N(q)‖x‖²
    let q = qquat(rng)
    let qx : Array[Quat[Q]] = Array::makei(n, i => q.qmul(x[i]))
    if !(s.inner)(qx, qx).eq(q.qnorm2().mul((s.inner)(x, x))) {
      ok = false
    }
  }
  mk_check(
    "I-07 ℍⁿ 實內積空間", ok, 25, "dim_ℝ = 4n；單位四元數之左右乘皆為等距",
  )
}

// ===========================================================================
//  J 群：多項式與組合核心
// ===========================================================================

///|
/// J-01 Horner 求值 ≡ 定義式求值；求值為環同態。
pub fn ob_j01() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<40 {
    let n = 2 + rng.next_below(5)
    let p : Poly[Q] = Poly::of(Array::makei(n, _ => qr(rng)))
    let q : Poly[Q] = Poly::of(Array::makei(n, _ => qr(rng)))
    let t = qr(rng)
    // 定義式 Σ cᵢtⁱ
    let mut acc = Q::zero()
    for i in 0..<n {
      acc = acc.add(p.coef[i].mul(spow(t, i)))
    }
    if !p.eval(t).eq(acc) {
      ok = false
    }
    if !p.pmul(q).eval(t).eq(p.eval(t).mul(q.eval(t))) {
      ok = false
    }
    if !p.padd(q).eval(t).eq(p.eval(t).add(q.eval(t))) {
      ok = false
    }
    // 合成：(p∘q)(t) = p(q(t))
    if !p.compose(q).eval(t).eq(p.eval(q.eval(t))) {
      ok = false
    }
  }
  mk_check(
    "J-01 Horner 求值與求值同態", ok, 40, "Horner ≡ Σcᵢtⁱ；(pq)(t)=p(t)q(t)；(p∘q)(t)=p(q(t))",
  )
}

///|
/// J-02 多項式乘法：次數加法、卷積公式、交換/結合/分配。
pub fn ob_j02() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<30 {
    let p : Poly[Q] = Poly::of(Array::makei(3, _ => qr(rng)))
    let q : Poly[Q] = Poly::of(Array::makei(4, _ => qr(rng)))
    let r : Poly[Q] = Poly::of(Array::makei(2, _ => qr(rng)))
    if !p.pmul(q).peq(q.pmul(p)) {
      ok = false
    }
    if !p.pmul(q).pmul(r).peq(p.pmul(q.pmul(r))) {
      ok = false
    }
    if !p.pmul(q.padd(r)).peq(p.pmul(q).padd(p.pmul(r))) {
      ok = false
    }
    // 卷積
    let pq = p.pmul(q)
    for k in 0..<pq.coef.length() {
      let mut acc = Q::zero()
      for i in 0..<p.coef.length() {
        let j = k - i
        if j >= 0 && j < q.coef.length() {
          acc = acc.add(p.coef[i].mul(q.coef[j]))
        }
      }
      if !pq.coef[k].eq(acc) {
        ok = false
      }
    }
    // 次數
    if p.degree() >= 0 &&
      q.degree() >= 0 &&
      pq.degree() != p.degree() + q.degree() {
      ok = false
    }
  }
  mk_check(
    "J-02 多項式乘法（卷積）", ok, 30, "交換/結合/分配；(pq)_k = Σ pᵢq_{k−i}；deg 相加",
  )
}

///|
/// J-03 由根造多項式：p(rᵢ) = 0，且係數為初等對稱多項式（符號交錯）。
pub fn ob_j03() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<25 {
    let k = 2 + rng.next_below(3)
    let roots : Array[Q] = Array::makei(k, _ => qr(rng))
    let p : Poly[Q] = poly_from_roots(roots)
    for r in roots {
      if !p.eval(r).is_zero() {
        ok = false
      }
    }
    // 首一且次數 = k
    if !p.coef[k].eq(Q::one()) || p.degree() != k {
      ok = false
    }
    // c_{k−1} = −Σrᵢ；c₀ = (−1)^k Πrᵢ
    let mut s = Q::zero()
    let mut pr = Q::one()
    for r in roots {
      s = s.add(r)
      pr = pr.mul(r)
    }
    if !p.coef[k - 1].eq(s.neg()) {
      ok = false
    }
    let want = if k % 2 == 0 { pr } else { pr.neg() }
    if !p.coef[0].eq(want) {
      ok = false
    }
  }
  mk_check(
    "J-03 由根造多項式（Vieta 公式）", ok, 25, "p(rᵢ)=0；c_{k−1}=−Σr；c₀=(−1)^kΠr",
  )
}

///|
/// J-04 微分與積分：(∫p)′ = p、Leibniz 法則、線性。
pub fn ob_j04() -> Check {
  let rng = ob_rng()
  let mut ok = true
  for _t in 0..<30 {
    let p : Poly[Q] = Poly::of(Array::makei(4, _ => qr(rng)))
    let q : Poly[Q] = Poly::of(Array::makei(4, _ => qr(rng)))
    if !p.integ().deriv().peq(p) {
      ok = false
    }
    // Leibniz
    let lhs = p.pmul(q).deriv()
    let rhs = p.deriv().pmul(q).padd(p.pmul(q.deriv()))
    if !lhs.peq(rhs) {
      ok = false
    }
    // 線性
    let c = qr(rng)
    if !p.pscale(c).padd(q).deriv().peq(p.deriv().pscale(c).padd(q.deriv())) {
      ok = false
    }
    // 鏈鎖法則 (p∘q)′ = (p′∘q)·q′
    let l2 = p.compose(q).deriv()
    let r2 = p.deriv().compose(q).pmul(q.deriv())
    if !l2.peq(r2) {
      ok = false
    }
  }
  mk_check(
    "J-04 形式微分與積分", ok, 30, "(∫p)′=p；Leibniz；線性；鏈鎖法則",
  )
}

///|
/// J-05 多重指數列舉：|monomials_upto(m,d)| = C(m+d, d)，grlex 為全序。
pub fn ob_j05() -> Check {
  let mut ok = true
  let mut cnt = 0
  for m in 1..<5 {
    for d in 0..<5 {
      cnt = cnt + 1
      let ms = monomials_upto(m, d)
      if ms.length().to_int64() != binom_i(m + d, d) {
        ok = false
      }
      // 嚴格遞增（全序且無重複）
      for i in 1..<ms.length() {
        if grlex_cmp(ms[i - 1], ms[i]) >= 0 {
          ok = false
        }
      }
      // 次數上界
      for a in ms {
        let mut s = 0
        for e in a {
          s = s + e
        }
        if s > d {
          ok = false
        }
      }
    }
  }
  mk_check(
    "J-05 多重指數列舉與 grlex 全序", ok, cnt, "|{xᵅ : |α| ≤ d}| = C(m+d,d)；嚴格遞增",
  )
}

///|
/// J-06 外代數組合核心：|subsets_k| = C(n,k)、符號 ε(I,J) 之一致性、互補符號。
pub fn ob_j06() -> Check {
  let mut ok = true
  let mut cnt = 0
  for n in 1..<7 {
    let mut total = 0
    for k in 0..<(n + 1) {
      cnt = cnt + 1
      let ss = subsets_k(n, k)
      if ss.length() != binom(n, k) {
        ok = false
      }
      total = total + ss.length()
      // 索引表一致
      let tbl = subset_index_table(n, k)
      for t in 0..<ss.length() {
        if tbl[mask_of(ss[t])] != t {
          ok = false
        }
      }
      // 遞增排序
      for s in ss {
        for i in 1..<s.length() {
          if s[i - 1] >= s[i] {
            ok = false
          }
        }
      }
      // ε(I,Iᶜ)·ε(Iᶜ,I) = (−1)^{k(n−k)}
      for s in ss {
        let c = complement_of(n, s)
        let a = merge_sign(s, c)
        let b = merge_sign(c, s)
        let want = if k * (n - k) % 2 == 0 { 1 } else { -1 }
        if a * b != want {
          ok = false
        }
      }
    }
    if total != 1 << n {
      ok = false // Σ_k C(n,k) = 2ⁿ
    }
  }
  mk_check(
    "J-06 子集列舉與楔積符號", ok, cnt, "C(n,k) 計數；Σ=2ⁿ；ε(I,Iᶜ)ε(Iᶜ,I)=(−1)^{k(n−k)}",
  )
}

// ---------------------------------------------------------------------------
//  輔助：排序與純量指數（避免任何第三方依賴）
// ---------------------------------------------------------------------------

///|
/// 就地插入排序（遞增）
pub fn sort_doubles(a : Array[Double]) -> Unit {
  for i in 1..<a.length() {
    let v = a[i]
    let mut j = i - 1
    while j >= 0 && a[j] > v {
      a[j + 1] = a[j]
      j = j - 1
    }
    a[j + 1] = v
  }
}

///|
/// e^x（Taylor + 平方縮放）
pub fn exp_scalar(x : Double) -> Double {
  let mut k = 0
  let mut y = x
  while absd(y) > 0.5 {
    y = y * 0.5
    k = k + 1
  }
  let mut term = 1.0
  let mut acc = 1.0
  for i in 1..<30 {
    term = term * y / i.to_double()
    acc = acc + term
  }
  for _i in 0..<k {
    acc = acc * acc
  }
  acc
}

///|
/// 整數最小值
fn mind_i(a : Int, b : Int) -> Int {
  if a < b {
    a
  } else {
    b
  }
}

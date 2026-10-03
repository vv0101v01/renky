///|
/// 數值軌道煙霧測試：每條都附殘差憑證。
fn spd_example(n : Int) -> RMat {
  Mat::build(n, n, (i, j) => {
    if i == j {
      (n + 2).to_double()
    } else {
      1.0 / (1 + i + j).to_double()
    }
  })
}

///|
test "數值分解之殘差憑證" {
  let n = 5
  let a = spd_example(n)
  // Cholesky
  let l = match cholesky(a) {
    Some(x) => x
    None => abort("非正定")
  }
  let dev1 = l.times(l.transpose()).max_dev(a)
  assert_true(dev1 < 1.0e-12)
  // LDLᵀ
  let (ld, d) = match ldlt(a) {
    Some(x) => x
    None => abort("LDL 失敗")
  }
  let dd : RMat = Mat::diagm(d)
  assert_true(ld.times(dd).times(ld.transpose()).max_dev(a) < 1.0e-12)
  let (p, z, m) = inertia(d)
  assert_true(p == n && z == 0 && m == 0)
  // QR Householder
  let b : RMat = Mat::build(6, 4, (i, j) => {
    (1 + i * j % 7).to_double() - 2.0 * (i % 3).to_double()
  })
  let (q, r) = qr_householder(b)
  assert_true(q.times(r).max_dev(b) < 1.0e-10)
  assert_true(q.transpose().times(q).max_dev(Mat::ident(6)) < 1.0e-10)
  assert_true(is_upper_numeric(r))
  // QR Givens
  let (q2, r2) = qr_givens(b)
  assert_true(q2.times(r2).max_dev(b) < 1.0e-10)
  assert_true(q2.transpose().times(q2).max_dev(Mat::ident(6)) < 1.0e-10)
  // Hessenberg
  let c : RMat = Mat::build(5, 5, (i, j) => {
    ((i * 3 + j * 7) % 11).to_double() - 4.0
  })
  let (qh, h) = hessenberg(c)
  assert_true(qh.times(h).times(qh.transpose()).max_dev(c) < 1.0e-9)
  // Jacobi 特徵值
  let (lam, v) = jacobi_eigen(a, 300)
  assert_true(v.transpose().times(v).max_dev(Mat::ident(n)) < 1.0e-10)
  let lamd : RMat = Mat::diagm(lam)
  assert_true(v.times(lamd).times(v.transpose()).max_dev(a) < 1.0e-9)
  // 跡 / 行列式 與特徵值之關係
  let mut sum = 0.0
  let mut prod = 1.0
  for x in lam {
    sum = sum + x
    prod = prod * x
  }
  assert_true(absd(sum - a.trace()) < 1.0e-9)
  assert_true(absd(prod - mdet(a)) < 1.0e-7)
  // SVD
  let (u, s, vv) = svd_jacobi(b, 80)
  let sd : RMat = Mat::build(4, 4, (i, j) => if i == j { s[i] } else { 0.0 })
  assert_true(u.times(sd).times(vv.transpose()).max_dev(b) < 1.0e-9)
  // 偽逆之 Penrose 四條件
  let ap = pinv(b, 1.0e-12)
  assert_true(b.times(ap).times(b).max_dev(b) < 1.0e-8)
  assert_true(ap.times(b).times(ap).max_dev(ap) < 1.0e-8)
  let bap = b.times(ap)
  assert_true(bap.transpose().max_dev(bap) < 1.0e-8)
  let apb = ap.times(b)
  assert_true(apb.transpose().max_dev(apb) < 1.0e-8)
  // 極分解
  let (up, pp) = polar_decomposition(b)
  assert_true(up.times(pp).max_dev(b) < 1.0e-9)
  assert_true(pp.transpose().max_dev(pp) < 1.0e-9)
  // expm：det(e^A) = e^{tr A}
  let sm : RMat = Mat::build(3, 3, (i, j) => {
    0.1 * (i + 2 * j).to_double() - 0.25
  })
  let e = expm(sm)
  let einv = expm(sm.negm())
  assert_true(e.times(einv).max_dev(Mat::ident(3)) < 1.0e-10)
  // sqrtm
  let sq = sqrtm_spd(a)
  assert_true(sq.times(sq).max_dev(a) < 1.0e-8)
  // 冪迭代 vs Jacobi 最大特徵值
  let (lmax, _vv) = power_iteration(a, 500)
  let mut mx = 0.0
  for x in lam {
    mx = maxd(mx, x)
  }
  assert_true(absd(lmax - mx) < 1.0e-6)
  // CG
  let rhs = Array::makei(n, i => (i + 1).to_double())
  let xcg = conjugate_gradient(a, rhs, 200)
  assert_true(vmax_dev(a.apply(xcg), rhs) < 1.0e-9)
  // Gauss–Seidel（對角佔優）
  let xgs = gauss_seidel(a, rhs, 500)
  assert_true(vmax_dev(a.apply(xgs), rhs) < 1.0e-8)
  // Lanczos：QᵀAQ = T
  let (ql, t) = lanczos(a, n)
  assert_true(ql.transpose().times(a).times(ql).max_dev(t) < 1.0e-8)
  // Arnoldi：QᵀAQ = H
  let (qa, hh) = arnoldi(c, 5)
  assert_true(qa.transpose().times(c).times(qa).max_dev(hh) < 1.0e-8)
}

///|
fn is_upper_numeric(r : RMat) -> Bool {
  for i in 0..<r.mrows {
    for j in 0..<r.mcols {
      if i > j && absd(r.at(i, j)) > 1.0e-10 {
        return false
      }
    }
  }
  true
}

///|
test "變換家族：DFT / FFT / Hadamard / Haar" {
  // DFT 么正性
  let n = 8
  let f = dft_matrix(n)
  let id : CMat = Mat::ident(n)
  assert_true(f.adjointm().times(f).max_dev(id) < 1.0e-10)
  // FFT 與 DFT 矩陣一致（FFT 未規範化 ⇒ 乘 1/√n 比較）
  let x : Array[Cpx[Double]] = Array::makei(n, i => {
    Cpx::mk((i + 1).to_double(), (i % 3).to_double() - 1.0)
  })
  let y1 = fft(x)
  let y2 = f.apply(x)
  let sc = sqrt_newton(n.to_double())
  let mut dev = 0.0
  for i in 0..<n {
    let a = y1[i]
    let b = Scalar::s_mul(Cpx::mk(sc, 0.0), y2[i])
    dev = maxd(dev, Scalar::s_mag(ssub(a, b)))
  }
  assert_true(dev < 1.0e-9)
  // 循環矩陣由 DFT 對角化：F C F* = diag
  let c = circulant([1.0, 2.0, 0.5, -1.0, 0.0, 3.0, 1.5, -2.0])
  let fc = f.times(to_complex(c)).times(f.adjointm())
  let mut offdiag = 0.0
  for i in 0..<n {
    for j in 0..<n {
      if i != j {
        offdiag = maxd(offdiag, Scalar::s_mag(fc.at(i, j)))
      }
    }
  }
  assert_true(offdiag < 1.0e-9)
  // Hadamard：HᵀH = nI
  let h = hadamard_matrix(3)
  assert_true(
    h.transpose().times(h).max_dev(Mat::ident(8).scale(8.0)) < 1.0e-12,
  )
  // FWHT 與矩陣乘法一致
  let xr = [1.0, -2.0, 3.0, 0.5, 2.0, -1.0, 0.0, 4.0]
  let w1 = fwht(xr)
  let w2 = h.apply(xr)
  assert_true(vmax_dev(w1, w2) < 1.0e-12)
  // Haar：列正交
  let hm = normalize_rows(haar_matrix(3))
  assert_true(hm.times(hm.transpose()).max_dev(Mat::ident(8)) < 1.0e-12)
}

///|
/// # 第九輪加速層：兩筆欠條
///
/// ## 一、L-05′ 的上界憑證太貴（N-69）
///
/// N-58 的秩憑證在方陣滿秩時 ×81.9，秩虧時掉到 ×1.08 —— 因為上界憑證要做
/// 一次 r 階**精確有理求逆**再逐行驗張成，係數膨脹全在那裡。
///
/// 便宜的做法是把分母清掉：設 B = A[R,S]（r×r）、d = det B，則
///
/// ```text
///   rank A = r  ⟺  d·A = A[*,S] · adj(B) · A[R,*]
/// ```
///
/// 這是秩-r 分解恆等式的**整數版** —— adj(B) 與 det(B) 都是整數，
/// 兩次矩陣乘法也都在整數上，全程沒有一個分數。而 adj 正是 K-07 的多模
/// CRT 管線（ν = r²、Hadamard 先驗界），n ≥ 7 時它自己就贏 ×1.7 以上。
///
/// ## 二、N-56 的預測該被檢驗（N-70）
///
/// N-56 診斷主成本是 Θ(ν·k²)，並由此**預測**「砍 k 沒用」。那條預測只在
/// LDLᵀ 上量過。ℚ 層還有三條管線用逐素數穩定判定（qsolve_crt、qinv_crt、
/// qrref_crt），它們的 ν 與 k 都比 LDLᵀ 小得多 —— 預測在那裡也成立嗎？
/// 一條沒有被檢驗過的預測不算結果。

// ---------------------------------------------------------------------------
//  N-69 整數版上界憑證
// ---------------------------------------------------------------------------

///|
/// 整數秩-r 分解憑證：驗 d·Az = Az[*,S]·adj(B)·Az[R,*]。
///
/// 全程整數：Az 為清分母後之整數矩陣，B = Az[R,S]，d = det B，adj(B) 為伴隨。
/// 回傳 (憑證是否通過, 使用之素數個數)。
pub fn rank_factor_cert(
  az : Array[Array[BigInt]],
  rowsel : Array[Int],
  colsel : Array[Int],
  primes : Array[Int64],
  c : Cost,
) -> (Bool, Int) {
  let m = az.length()
  let n = az[0].length()
  let r = colsel.length()
  if rowsel.length() != r {
    return (false, 0)
  }
  // B = Az[R, S]
  let b : Array[Array[BigInt]] = []
  for i in 0..<r {
    b.push(Array::makei(r, j => az[rowsel[i]][colsel[j]]))
  }
  // adj(B) 與 det(B)：多模 CRT（K-07 的管線）
  let (adjb, _, _) = zadj_crt(b, primes, c)
  let (d, np) = zdet_crt(b, primes, c)
  if d == 0N {
    return (false, np)
  }
  // L = Az[*, S]（m×r）、R = Az[R, *]（r×n）
  let lmat : Array[Array[BigInt]] = []
  for i in 0..<m {
    lmat.push(Array::makei(r, j => az[i][colsel[j]]))
  }
  let rmat : Array[Array[BigInt]] = []
  for i in 0..<r {
    rmat.push(Array::makei(n, j => az[rowsel[i]][j]))
  }
  // T = L · adj(B)（m×r）
  let t = zrows_mul(lmat, adjb)
  charge_zrows_mul(c, lmat, adjb)
  // U = T · R（m×n）
  let u = zrows_mul(t, rmat)
  charge_zrows_mul(c, t, rmat)
  // 驗 d·Az = U
  for i in 0..<m {
    for j in 0..<n {
      if d * az[i][j] != u[i][j] {
        return (false, np)
      }
    }
  }
  (true, np)
}

///|
/// 整數矩陣乘法之計費（schoolbook，逐對位寬加權）。
fn charge_zrows_mul(
  c : Cost,
  a : Array[Array[BigInt]],
  b : Array[Array[BigInt]],
) -> Unit {
  let m = a.length()
  if m == 0 {
    return
  }
  let k = b.length()
  if k == 0 {
    return
  }
  let n = b[0].length()
  for i in 0..<m {
    for t in 0..<k {
      let wa = big_words(a[i][t])
      for j in 0..<n {
        c.wmul = c.wmul + wa * big_words(b[t][j])
      }
    }
  }
  c.note(zrows_maxbits(a) + zrows_maxbits(b))
}

///|
/// 【L-05″】用整數分解憑證取代有理求逆的秩判定。
pub fn qrank_modp2(
  a : Mat[Q],
  primes : Array[Int64],
  nprime : Int,
  c : Cost,
) -> RankCert {
  let m = a.mrows
  let n = a.mcols
  let az = qmat_to_zrows(a)
  let (_, azc) = qmat_clear_denom(a)
  let _ = az
  let mut best : Array[Int] = []
  let mut brank = 0
  let mut used = 0
  let mut t = 0
  while t < primes.length() && used < nprime {
    let p = primes[t]
    t = t + 1
    let ctx = FpCtx::make(p)
    charge_reduce_rows(c, azc)
    let fa = fp_of_big(azc, ctx)
    let rr = fp_rref(fa, ctx)
    c.absorb_fp(ctx)
    used = used + 1
    if rr.rank > brank {
      brank = rr.rank
      best = rr.pivots
    }
  }
  if brank == 0 {
    return { rcrank: 0, rcpiv: [], rclow: true, rcup: true, rcused: used, }
  }
  // 樞軸列：對 Az[*,S] 之轉置再做一次模 p 消去
  let ctx0 = FpCtx::make(primes[0])
  let subz : Array[Array[BigInt]] = []
  for j in 0..<brank {
    subz.push(Array::makei(m, i => azc[i][best[j]]))
  }
  charge_reduce_rows(c, subz)
  let rrows = fp_rref(fp_of_big(subz, ctx0), ctx0)
  c.absorb_fp(ctx0)
  let rowsel = rrows.pivots
  if rowsel.length() < brank {
    return {
      rcrank: brank,
      rcpiv: best,
      rclow: false,
      rcup: false,
      rcused: used,
    }
  }
  // 整數分解憑證一次給出上下界：d ≠ 0 ⇒ rank ≥ r；恆等式成立 ⇒ rank ≤ r
  let (certok, _) = rank_factor_cert(azc, rowsel, best, primes, c)
  let mn = if m < n { m } else { n }
  let _ = mn
  { rcrank: brank, rcpiv: best, rclow: certok, rcup: certok, rcused: used, }
}

///|
/// 兩版秩憑證之對照（秩虧長方形）。
/// 回傳 (基準字乘, N-58 版, N-69 版, 三者秩一致?)。
pub fn rank_cert_compare(
  m : Int,
  r : Int,
  bits : Int,
) -> (Int64, Int64, Int64, Bool) {
  let ps = acc_pool()
  let rng = ob_rng()
  let b1 = qmat_bitwidth(rng, m, r, bits)
  let b2 = qmat_bitwidth(rng, r, m, bits)
  let a = b1.times(b2)
  let cb = Cost::new()
  let (_, rk, _) = qrref_gauss(a, cb)
  let c1 = Cost::new()
  let x1 = qrank_modp(a, ps, 3, c1)
  let c2 = Cost::new()
  let x2 = qrank_modp2(a, ps, 3, c2)
  let ok = x1.rcrank == rk &&
    x2.rcrank == rk &&
    x1.rclow &&
    x1.rcup &&
    x2.rclow &&
    x2.rcup
  (cb.wmul, c1.wmul, c2.wmul, ok)
}

///|
/// 秩虧網格掃描。
/// 回傳 (格數, 全部正確?, N-58 總成本, N-69 總成本, N-69 較便宜數)。
pub fn rank_cert_scan() -> (Int, Bool, Int64, Int64, Int) {
  let cases : Array[(Int, Int, Int)] = [
    (8, 5, 16),
    (10, 6, 16),
    (12, 7, 16),
    (8, 4, 32),
  ]
  let mut allok = true
  let mut t1 = 0L
  let mut t2 = 0L
  let mut win = 0
  for cs in cases {
    let (_, a, b, ok) = rank_cert_compare(cs.0, cs.1, cs.2)
    if !ok {
      allok = false
    }
    t1 = t1 + a
    t2 = t2 + b
    if b < a {
      win = win + 1
    }
  }
  (cases.length(), allok, t1, t2, win)
}

///|
/// 兩側對照：把樞軸行換掉一個，整數憑證必須失敗。
pub fn rank_cert_control() -> Bool {
  let ps = acc_pool()
  let rng = ob_rng()
  let b1 = qmat_bitwidth(rng, 8, 5, 16)
  let b2 = qmat_bitwidth(rng, 5, 8, 16)
  let a = b1.times(b2)
  let (_, azc) = qmat_clear_denom(a)
  let good = qrank_modp2(a, ps, 3, Cost::new())
  if !good.rclow || good.rcrank != 5 {
    return false
  }
  // 少一個樞軸行 ⇒ 分解恆等式不該成立
  let fewer = Array::makei(4, i => good.rcpiv[i])
  let rows = Array::makei(4, i => i)
  let (bad, _) = rank_factor_cert(azc, rows, fewer, ps, Cost::new())
  !bad
}

// ---------------------------------------------------------------------------
//  N-70 檢驗 N-56 的預測
// ---------------------------------------------------------------------------

///|
/// 【重構版】ℚ 線性解之多模重建 —— 先驗界一次重建。
pub fn qsolve_crt_ap(
  a : Mat[Q],
  b : Array[Q],
  primes : Array[Int64],
  c : Cost,
) -> QLift {
  let n = a.mrows
  let (da, _) = qmat_clear_denom(a)
  let (db, _) = qvec_clear_denom(b)
  let d = big_lcm(da, db)
  let az : Array[Array[BigInt]] = []
  for i in 0..<n {
    az.push(Array::makei(n, j => a.at(i, j).num * (d / a.at(i, j).den)))
  }
  let bz = Array::makei(n, i => b[i].num * (d / b[i].den))
  let h = hadamard_bound(az)
  let need = primes_needed(h * h, primes)
  let ps = ensure_primes(primes, need + 4)
  let crts : Array[Crt] = Array::makei(n, _ => Crt::new())
  let mut used = 0
  let mut bad = 0
  let mut t = 0
  while t < ps.length() && used < need {
    let p = ps[t]
    t = t + 1
    let ctx = FpCtx::make(p)
    charge_reduce_rows(c, az)
    let fa = fp_of_big(az, ctx)
    let pb = BigInt::from_int64(p)
    let fb = Array::makei(n, i => normmod((bz[i] % pb).to_int64(), p))
    match fp_solve(fa, fb, ctx) {
      None => {
        bad = bad + 1
        c.absorb_fp(ctx)
        continue
      }
      Some(x) => {
        for i in 0..<n {
          charge_crt_step(c, crts[i].modulus())
          crts[i].absorb(x[i], p)
        }
        c.absorb_fp(ctx)
        used = used + 1
      }
    }
  }
  if used < need {
    return { sol: None, used, bad, certified: false, }
  }
  let m = crts[0].modulus()
  let flat = Array::makei(n, i => crts[i].sym())
  match rat_recon_vec(flat, m) {
    None => { sol: None, used, bad, certified: false, }
    Some(x) => {
      // 事後憑證：A·x = b（精確）
      let mut okc = true
      for i in 0..<n {
        let mut s = Q::zero()
        for j in 0..<n {
          s = cq_add(c, s, cq_mul(c, a.at(i, j), x[j]))
        }
        if !s.eq(b[i]) {
          okc = false
        }
      }
      { sol: Some(x), used, bad, certified: okc, }
    }
  }
}

///|
/// 檢驗 N-56 的預測：三條 ℚ 管線上「先驗界一次重建」對「逐素數穩定判定」。
///
/// 回傳 [(管線名, n, 位元, 穩定判定字乘, 先驗界字乘, 兩版輸出相同?)]。
pub fn apriori_verdict_table() -> Array[(String, Int, Int, Int64, Int64, Bool)] {
  let ps = acc_pool()
  let out : Array[(String, Int, Int, Int64, Int64, Bool)] = []
  for cs in [(4, 8), (6, 8), (4, 16), (6, 16)] {
    let n = cs.0
    let bits = cs.1
    // ── ℚ 反矩陣 ──
    let r1 = ob_rng()
    let a = qmat_bitwidth(r1, n, n, bits)
    let c1 = Cost::new()
    let (x1, _, k1) = qinv_crt(a, ps, c1)
    let c2 = Cost::new()
    let (x2, _, k2) = qinv_crt_ap(a, ps, c2)
    let same1 = match (x1, x2) {
      (Some(u), Some(v)) => u.equals(v) && k1 && k2
      _ => false
    }
    out.push(("ℚ 反矩陣", n, bits, c1.wmul, c2.wmul, same1))
    // ── ℚ 線性解 ──
    let r2 = ob_rng()
    let a2 = qmat_bitwidth(r2, n, n, bits)
    let bv = Array::makei(n, _ => Q::s_rand(r2))
    let c3 = Cost::new()
    let s1 = qsolve_crt(a2, bv, ps, c3)
    let c4 = Cost::new()
    let s2 = qsolve_crt_ap(a2, bv, ps, c4)
    let same2 = match (s1.sol, s2.sol) {
      (Some(u), Some(v)) => qvec_eq(u, v) && s1.certified && s2.certified
      _ => false
    }
    out.push(("ℚ 線性解", n, bits, c3.wmul, c4.wmul, same2))
    // ── Gram LDLᵀ（N-56 量過的那一條，當對照）──
    let r3 = ob_rng()
    let g = qgram_bitwidth(r3, n, bits)
    let c5 = Cost::new()
    let l1 = qldlt_crt(g, ps, c5)
    let c6 = Cost::new()
    let l2 = qldlt_crt_ap(g, ps, c6)
    let same3 = match (l1, l2) {
      (Some(u), Some(v)) => u.lmat.equals(v.lmat) && u.certified && v.certified
      _ => false
    }
    out.push(("Gram LDLᵀ", n, bits, c5.wmul, c6.wmul, same3))
  }
  out
}

///|
/// 預測之裁決。
///
/// 回傳 (格數, 兩版輸出全同?, 先驗界較慢之格數, 先驗界較快之格數,
///        最大變慢比, 最大變快比)。
pub fn apriori_verdict() -> (Int, Bool, Int, Int, Double, Double) {
  let tbl = apriori_verdict_table()
  let mut allsame = true
  let mut slower = 0
  let mut faster = 0
  let mut wslow = 1.0
  let mut wfast = 1.0
  for r in tbl {
    let (_, _, _, a, b, same) = r
    if !same {
      allsame = false
    }
    if b > a {
      slower = slower + 1
      let x = b.to_double() / a.to_double()
      if x > wslow {
        wslow = x
      }
    } else if b < a {
      faster = faster + 1
      let x = a.to_double() / b.to_double()
      if x > wfast {
        wfast = x
      }
    }
  }
  (tbl.length(), allsame, slower, faster, wslow, wfast)
}

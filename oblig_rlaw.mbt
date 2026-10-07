// ============================================================================
//  檔案 23：oblig_rlaw.mbt — ℝ 軌結構律（N-20、N-21）之義務自證
// ============================================================================

///|
/// N-20 ℝ 軌 flop 計量器：孿生體忠實性 + 成本標度律。
pub fn ob_n20() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut maxdev = 0.0
  let rows : Array[String] = []
  // 定理 177：孿生體與原版須**精確相等**（偏差恰為 0）
  for sz in [2, 3, 4, 5, 6, 8] {
    let a = rand_spd(rng, sz)
    let r = 60
    let c = Cost::new()
    let (l1, _v1, _rt) = cjacobi_eigen(a, 1.0e-15, r, c)
    let (l2, _v2) = jacobi_eigen(a, r)
    let d = spec_dev(l1, l2)
    if d != 0.0 {
      ok = false
    }
    if d > maxdev {
      maxdev = d
    }
    n = n + 1
  }
  // 成本標度：flops 須隨 n 嚴格遞增，且 n 加倍時增幅超過 ×4（優於 Θ(n²)）
  let mut prev = 0L
  let mut f4 = 0L
  let mut f8 = 0L
  for sz in [2, 3, 4, 5, 6, 8] {
    let a = rand_spd(rng, sz)
    let c = Cost::new()
    let (_l, _v, rt) = cjacobi_eigen(a, 1.0e-10, 3000, c)
    if c.flops <= prev {
      ok = false
    }
    prev = c.flops
    if sz == 4 {
      f4 = c.flops
    }
    if sz == 8 {
      f8 = c.flops
    }
    rows.push(
      "n" +
      sz.to_string() +
      " " +
      c.flops.to_string() +
      "f/" +
      rt.to_string() +
      "轉",
    )
    n = n + 1
  }
  // n: 4 → 8 之成本成長須超過 ×4（古典 Jacobi 為 Θ(n⁴)：旋轉數 Θ(n²) × 每轉 Θ(n²)）
  if f8.to_double() <= f4.to_double() * 4.0 {
    ok = false
  }
  mk_check(
    "N-20 ℝ 軌 flop 計量器與孿生體忠實性",
    ok,
    n,
    "定理 177：6 組尺寸上受計量孿生體與 realmat.mbt 原版 jacobi_eigen 之輸出偏差恰為 " +
    fmt_d(maxdev, 1) +
    "（精確相等，非容差內相等），故 flop 計數可信。成本標度：" +
    rows.join("　") +
    "；n 由 4 至 8 成本成長 ×" +
    fmt_d(f8.to_double() / f4.to_double(), 1) +
    "，遠超 ×4 —— 符合古典 Jacobi 之 Θ(n⁴)（旋轉數 Θ(n²) × 每轉主元搜尋 Θ(n²)）。計量約定含主元搜尋之比較，刻意不只計乘加，否則大矩陣成本將被嚴重低估",
  )
}

///|
/// N-21 譜律族：spec(A⊗B) = {λᵢμⱼ}、spec(A⊕B) = spec A ⊎ spec B，及其成本。
pub fn ob_n21() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut tb = 0L
  let mut tf = 0L
  let mut maxdev = 0.0
  let rows : Array[String] = []
  // ---- ⊗ 譜律 ----
  for sz in [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6)] {
    let (p, q) = sz
    let a = rand_spd(rng, p)
    let b = rand_spd(rng, q)
    let cd = Cost::new()
    let (ld, _vd, _r0) = cjacobi_eigen(mkron(a, b), 1.0e-10, 3000, cd)
    let cf = Cost::new()
    let (la, va, _r1) = cjacobi_eigen(a, 1.0e-10, 3000, cf)
    let (lb, vb, _r2) = cjacobi_eigen(b, 1.0e-10, 3000, cf)
    let prod = Array::makei(p * q, i => la[i / q] * lb[i % q])
    cflop(cf, (p * q).to_int64())
    // 定理 178-1：spec(A⊗B) = {λᵢ·μⱼ}
    let d = spec_dev(ld, prod)
    if d > 1.0e-8 {
      ok = false
    }
    if d > maxdev {
      maxdev = d
    }
    // 定理 178-2：特徵向量為 vᵢ ⊗ wⱼ —— 驗 (A⊗B)(vᵢ⊗wⱼ) = λᵢμⱼ(vᵢ⊗wⱼ)
    let vk = rkron_cost(cf, va, vb)
    let lhs = mkron(a, b).times(vk)
    let mut vdev = 0.0
    for col in 0..<(p * q) {
      let lam = la[col / q] * lb[col % q]
      for row in 0..<(p * q) {
        let e = absd(lhs.at(row, col) - lam * vk.at(row, col))
        if e > vdev {
          vdev = e
        }
      }
    }
    if vdev > 1.0e-6 {
      ok = false
    }
    tb = tb + cd.flops
    tf = tf + cf.flops
    rows.push(
      "dim" + (p * q).to_string() + " ×" + fmt_d(flop_ratio(cd, cf), 1),
    )
    n = n + 2
  }
  // ---- ⊕ 譜律（定理 178-3）：spec(A⊕B) = spec A ⊎ spec B ----
  let mut sum_gain = 0.0
  for sz in [(3, 3), (4, 4)] {
    let (p, q) = sz
    let a = rand_spd(rng, p)
    let b = rand_spd(rng, q)
    let cd = Cost::new()
    let (ld, _vd, _r0) = cjacobi_eigen(rblock_diag(a, b), 1.0e-10, 3000, cd)
    let cf = Cost::new()
    let (la, _va, _r1) = cjacobi_eigen(a, 1.0e-10, 3000, cf)
    let (lb, _vb, _r2) = cjacobi_eigen(b, 1.0e-10, 3000, cf)
    let un = Array::makei(p + q, i => if i < p { la[i] } else { lb[i - p] })
    if spec_dev(ld, un) > 1.0e-8 {
      ok = false
    }
    sum_gain = flop_ratio(cd, cf)
    n = n + 1
  }
  // ---- 譜半徑與條件數（定理 178-4、178-5）----
  for sz in [(2, 3), (3, 3)] {
    let (p, q) = sz
    let a = rand_spd(rng, p)
    let b = rand_spd(rng, q)
    let c0 = Cost::new()
    let (lk, _v, _r) = cjacobi_eigen(mkron(a, b), 1.0e-10, 3000, c0)
    let (la, _v1, _r1) = cjacobi_eigen(a, 1.0e-10, 3000, c0)
    let (lb, _v2, _r2) = cjacobi_eigen(b, 1.0e-10, 3000, c0)
    let sk = lk.copy()
    let sa = la.copy()
    let sb = lb.copy()
    sort_doubles(sk)
    sort_doubles(sa)
    sort_doubles(sb)
    let rho = sk[sk.length() - 1]
    let rho2 = sa[sa.length() - 1] * sb[sb.length() - 1]
    if absd(rho - rho2) > 1.0e-7 * rho {
      ok = false
    }
    // κ₂(A⊗B) = κ₂(A)·κ₂(B)（SPD 時 κ₂ = λmax/λmin）
    let k1 = rho / sk[0]
    let k2 = sa[sa.length() - 1] / sa[0] * (sb[sb.length() - 1] / sb[0])
    if absd(k1 - k2) > 1.0e-6 * k1 {
      ok = false
    }
    n = n + 2
  }
  // ---- dim 64：不只是快，而是「算得出 vs 算不出」----
  // 給直接法與分解法相同之旋轉預算，比較兩者在預算內達到的精度。
  let budget = 4000
  let a8 = rand_spd(rng, 8)
  let b8 = rand_spd(rng, 8)
  let c64 = Cost::new()
  let (l64, _v64, r64) = cjacobi_eigen(mkron(a8, b8), 1.0e-10, budget, c64)
  let cs = Cost::new()
  let (la8, _u1, ra8) = cjacobi_eigen(a8, 1.0e-10, budget, cs)
  let (lb8, _u2, rb8) = cjacobi_eigen(b8, 1.0e-10, budget, cs)
  let p64 = Array::makei(64, i => la8[i / 8] * lb8[i % 8])
  cflop(cs, 64L)
  // 以「真值」為基準：分解法之譜（兩個 8×8 皆已收斂）
  let dev64 = spec_dev(l64, p64)
  // 直接法必須耗盡預算仍未收斂；分解法必須在預算內收斂
  let direct_stuck = r64 >= budget
  let sub_converged = ra8 < budget && rb8 < budget
  if !direct_stuck || !sub_converged {
    ok = false
  }
  if dev64 < 1.0e-4 {
    ok = false
  }
  n = n + 1
  let g = if tf > 0L { tb.to_double() / tf.to_double() } else { 0.0 }
  // 增益須隨維度上升且總增益顯著
  if g <= 10.0 {
    ok = false
  }
  mk_check(
    "N-21 譜律族（⊗ 與 ⊕ 之特徵分解）",
    ok,
    n,
    "定理 178-1 spec(A⊗B) = {λᵢμⱼ} 與 178-2 特徵向量 vᵢ⊗wⱼ 逐例成立（最大譜偏差 " +
    fmt_e(maxdev) +
    "）。成本（flop 計量）：" +
    rows.join("　") +
    "，總增益 ×" +
    fmt_d(g, 1) +
    "。定理 178-3 spec(A⊕B) = spec A ⊎ spec B 成立，但增益僅 ×" +
    fmt_d(sum_gain, 2) +
    " —— 與 N-04 同一現象（Jacobi 於分塊對角上本就只在塊內旋轉）。定理 178-4 ρ(A⊗B) = ρ(A)ρ(B)、178-5 κ₂(A⊗B) = κ₂(A)κ₂(B) 亦成立。本族為全庫增益最高之結構律：直接法於 nm 階上旋轉數 Θ((nm)²)、每轉 Θ((nm)²)，合計 Θ((nm)⁴)，分解法僅 Θ(n⁴+m⁴)。【dim 64 之質變】給定相同 " +
    budget.to_string() +
    " 次旋轉預算：直接法耗盡預算仍未收斂（用滿 " +
    r64.to_string() +
    " 轉、" +
    c64.flops.to_string() +
    " flops，譜偏差 " +
    fmt_e(dev64) +
    "），兩個 8×8 子問題各以 " +
    ra8.to_string() +
    "／" +
    rb8.to_string() +
    " 轉收斂（共 " +
    cs.flops.to_string() +
    " flops）。此時結構律給的已不是加速，而是「在給定預算下算得出 vs 算不出」",
  )
}

///|
/// N-22 分解律族：Cholesky 與 SVD 在 ⊗ 下之行為。
pub fn ob_n22() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  // ---- 孿生體忠實性（定理 177 推廣至演算法 179）----
  for sz in [3, 5, 6] {
    let a = rand_spd(rng, sz)
    let c = Cost::new()
    let mut d = 0.0
    match (ccholesky(a, c), cholesky(a)) {
      (Some(x), Some(y)) =>
        for i in 0..<sz {
          for j in 0..<sz {
            let e = absd(x.at(i, j) - y.at(i, j))
            if e > d {
              d = e
            }
          }
        }
      _ => d = 1.0e30
    }
    if d != 0.0 {
      ok = false
    }
    let c2 = Cost::new()
    let (u1, s1, v1) = csvd_jacobi(a, 40, c2)
    let (u2, s2, v2) = svd_jacobi(a, 40)
    // 不可只比對譜（spec_dev 會排序，看不出行序差異）——
    // U、V 亦須逐元素相同，否則孿生體對下游（如 pinv）並不忠實。
    if spec_dev(s1, s2) != 0.0 ||
      mat_dev(u1, u2) != 0.0 ||
      mat_dev(v1, v2) != 0.0 {
      ok = false
    }
    n = n + 2
  }
  // ---- 定理 179-1：chol(A⊗B) = chol(A) ⊗ chol(B) ----
  let mut tbc = 0L
  let mut tfc = 0L
  let mut devc = 0.0
  let rowc : Array[String] = []
  for sz in [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6)] {
    let (p, q) = sz
    let a = rand_spd(rng, p)
    let b = rand_spd(rng, q)
    let cd = Cost::new()
    let ld = ccholesky(mkron(a, b), cd)
    let cf = Cost::new()
    let la = ccholesky(a, cf)
    let lb = ccholesky(b, cf)
    match (ld, la, lb) {
      (Some(x), Some(y), Some(z)) => {
        let k = rkron_cost(cf, y, z)
        for i in 0..<x.mrows {
          for j in 0..<x.mcols {
            let e = absd(x.at(i, j) - k.at(i, j))
            if e > devc {
              devc = e
            }
          }
        }
      }
      _ => ok = false
    }
    tbc = tbc + cd.flops
    tfc = tfc + cf.flops
    rowc.push(
      "dim" + (p * q).to_string() + " ×" + fmt_d(flop_ratio(cd, cf), 1),
    )
    n = n + 1
  }
  if devc > 1.0e-10 {
    ok = false
  }
  // ---- 定理 179-2：σ(A⊗B) = {σᵢ·τⱼ} ----
  let mut tbs = 0L
  let mut tfs = 0L
  let mut devs = 0.0
  let rows : Array[String] = []
  for sz in [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6)] {
    let (p, q) = sz
    let a = rand_spd(rng, p)
    let b = rand_spd(rng, q)
    let cd = Cost::new()
    let (_u, sd, _v) = csvd_jacobi(mkron(a, b), 60, cd)
    let cf = Cost::new()
    let (_ua, sa, _va) = csvd_jacobi(a, 60, cf)
    let (_ub, sb, _vb) = csvd_jacobi(b, 60, cf)
    let prod = Array::makei(p * q, i => sa[i / q] * sb[i % q])
    cflop(cf, (p * q).to_int64())
    let d = spec_dev(sd, prod)
    if d > devs {
      devs = d
    }
    tbs = tbs + cd.flops
    tfs = tfs + cf.flops
    rows.push(
      "dim" + (p * q).to_string() + " ×" + fmt_d(flop_ratio(cd, cf), 1),
    )
    n = n + 1
  }
  if devs > 1.0e-8 {
    ok = false
  }
  let gc = tbc.to_double() / tfc.to_double()
  let gs = tbs.to_double() / tfs.to_double()
  // SVD 之增益必須顯著高於 Cholesky（組裝成本佔比不同）
  if gs <= gc {
    ok = false
  }
  mk_check(
    "N-22 分解律族（Cholesky 與 SVD 於 ⊗ 下）",
    ok,
    n,
    "孿生體忠實性：ccholesky／csvd_jacobi 與 realmat.mbt 原版輸出偏差恰為 0（3 組尺寸）。定理 179-1 chol(A⊗B) = chol(A)⊗chol(B) 逐例成立（最大偏差 " +
    fmt_e(devc) +
    "），" +
    rowc.join("　") +
    "，總增益 ×" +
    fmt_d(gc, 1) +
    "。定理 179-2 σ(A⊗B) = {σᵢτⱼ} 逐例成立（最大偏差 " +
    fmt_e(devs) +
    "），" +
    rows.join("　") +
    "，總增益 ×" +
    fmt_d(gs, 1) +
    "。兩者增益相差 " +
    fmt_d(gs / gc, 1) +
    " 倍，成因為組裝成本佔比：Cholesky 本體僅 Θ(N³/3)，而 Kronecker 組裝為 Θ(N²)，小尺寸時組裝吃掉大半紅利；SVD 本體為 Θ(N³·掃描數) 故組裝可忽略。此即「結構律之增益取決於本體與組裝之比」之具體例證",
  )
}

///|
/// N-25 快速變換即結構律：FWHT 與 Hadamard 矩陣皆為 Kronecker 樹之實例。
pub fn ob_n25() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let rows : Array[String] = []
  let mut g_mode = 0.0
  let mut g_fwht = 0.0
  let mut maxdev = 0.0
  for k in [2, 3, 4, 5, 6, 7, 8] {
    let nn = 1 << k
    let h = hadamard_matrix(k)
    // 推論 181-1 之結構面：H_{2ᵏ} = H₂ ⊗ H_{2ᵏ⁻¹}（精確相等）
    if !mkron(h2(), hadamard_matrix(k - 1)).equals(h) {
      ok = false
    }
    let x = Array::makei(nn, _i => (rng.next_below(9) - 4).to_double())
    let cd = Cost::new()
    let yd = cmatvec(cd, h, x)
    let factors : Array[RMat] = Array::makei(k, _i => h2())
    let cf = Cost::new()
    let yf = kron_matvec(cf, factors, x)
    let cw = Cost::new()
    let yw = cfwht(x, cw)
    // 定理 181：模積法與稠密法結果相同；且既有 fwht 亦相同
    let d1 = vec_dev(yd, yf)
    let d2 = vec_dev(yd, yw)
    if d1 != 0.0 || d2 != 0.0 {
      ok = false
    }
    if d1 > maxdev {
      maxdev = d1
    }
    if k == 8 {
      g_mode = flop_ratio(cd, cf)
      g_fwht = flop_ratio(cd, cw)
    }
    rows.push("N" + nn.to_string() + " ×" + fmt_d(flop_ratio(cd, cf), 1))
    n = n + 3
  }
  // 增益須為 N/(2k)（模積法之理論值）
  let predicted = 256.0 / 16.0
  if absd(g_mode - predicted) > 0.5 {
    ok = false
  }
  // FWHT 蝶形須再快一截（H₂ 之元為 ±1，省去乘法）
  if g_fwht <= g_mode {
    ok = false
  }
  // 非同構因子之一般情形：A(2)⊗B(3)⊗C(2)
  let a = Mat::build(2, 2, (i, j) => {
    (rng.next_below(7) - 3).to_double() + (if i == j { 4.0 } else { 0.0 })
  })
  let b = Mat::build(3, 3, (i, j) => {
    (rng.next_below(7) - 3).to_double() + (if i == j { 4.0 } else { 0.0 })
  })
  let c3 = Mat::build(2, 2, (i, j) => {
    (rng.next_below(7) - 3).to_double() + (if i == j { 4.0 } else { 0.0 })
  })
  let big = mkron(mkron(a, b), c3)
  let x12 = Array::makei(12, _i => (rng.next_below(9) - 4).to_double())
  let cdd = Cost::new()
  let y1 = cmatvec(cdd, big, x12)
  let cff = Cost::new()
  let y2 = kron_matvec(cff, [a, b, c3], x12)
  if vec_dev(y1, y2) > 1.0e-10 {
    ok = false
  }
  n = n + 1
  mk_check(
    "N-25 快速變換即結構律（FWHT／Hadamard 為 Kronecker 樹之實例）",
    ok,
    n,
    "7 組尺寸逐例成立且偏差恰為 " +
    fmt_d(maxdev, 1) +
    "：(1) H_{2ᵏ} = H₂ ⊗ H_{2ᵏ⁻¹} 精確相等 —— realmat.mbt 之 hadamard_matrix 本身就是 Kronecker 遞迴；(2) 定理 181 模積法與稠密矩陣向量積結果相同；(3) **既有之 fwht 輸出與兩者皆精確相同**。成本：" +
    rows.join("　") +
    "。k=8（N=256）時模積法 ×" +
    fmt_d(g_mode, 1) +
    "（恰為理論值 N/(2k) = 16），FWHT 蝶形再快一截達 ×" +
    fmt_d(g_fwht, 1) +
    "（H₂ 之元為 ±1，連乘法都省去）。結論：FWHT 不是一個獨立演算法，而是定理 181 在 Kronecker 樹上的實例，其 Θ(N log N) 相對 Θ(N²) 之優勢**就是結構律增益本身**。另驗非同構因子 A₂⊗B₃⊗C₂ 之一般情形亦成立",
  )
}

///|
/// N-23 偽逆與投影律：pinv(A⊗B) = pinv(A)⊗pinv(B)、P_{V⊗W} = P_V⊗P_W。
pub fn ob_n23() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut tb = 0L
  let mut tf = 0L
  let mut dev = 0.0
  let mut pdev = 0.0
  let rows : Array[String] = []
  let gains : Array[Double] = []
  let mut twin_dev = 0.0
  // 孿生體忠實性（含 U、V 之行序）
  for sz in [3, 4] {
    let a = rand_spd(rng, sz)
    let c = Cost::new()
    let d = mat_dev(cpinv(a, 1.0e-10, c), pinv(a, 1.0e-10))
    if d != 0.0 {
      ok = false
    }
    if d > twin_dev {
      twin_dev = d
    }
    n = n + 1
  }
  for sz in [(2, 2), (3, 3), (4, 4), (5, 5)] {
    let (p, q) = sz
    let a = rand_spd(rng, p)
    let b = rand_spd(rng, q)
    let cd = Cost::new()
    let pd = cpinv(mkron(a, b), 1.0e-10, cd)
    let cf = Cost::new()
    let pa = cpinv(a, 1.0e-10, cf)
    let pb = cpinv(b, 1.0e-10, cf)
    let k = rkron_cost(cf, pa, pb)
    let d = mat_dev(pd, k)
    if d > 1.0e-10 {
      ok = false
    }
    if d > dev {
      dev = d
    }
    // 投影律：P = A·pinv(A)，且 P_{A⊗B} = P_A ⊗ P_B
    let pja = a.times(pa)
    let pjb = b.times(pb)
    let pjk = mkron(a, b).times(pd)
    let e = mat_dev(pjk, mkron(pja, pjb))
    if e > 1.0e-9 {
      ok = false
    }
    if e > pdev {
      pdev = e
    }
    tb = tb + cd.flops
    tf = tf + cf.flops
    gains.push(flop_ratio(cd, cf))
    rows.push(
      "dim" + (p * q).to_string() + " ×" + fmt_d(flop_ratio(cd, cf), 1),
    )
    n = n + 2
  }
  let g = tb.to_double() / tf.to_double()
  if g <= 5.0 {
    ok = false
  }
  // 掃描數是否隨尺寸單調 —— 由實測決定，不預先斷言
  let mut mono = true
  let mut prev = 0.0
  for r in gains {
    if r < prev {
      mono = false
    }
    prev = r
  }
  mk_check(
    "N-23 偽逆與投影律（⊗）",
    ok,
    n,
    "孿生體 cpinv 與原版 pinv 輸出偏差恰為 " +
    fmt_d(twin_dev, 1) +
    "。定理 183-1 pinv(A⊗B) = pinv(A)⊗pinv(B) 逐例成立（最大偏差 " +
    fmt_e(dev) +
    "）；定理 183-2 投影子 P_{A⊗B} = P_A ⊗ P_B（最大偏差 " +
    fmt_e(pdev) +
    "）。成本：" +
    rows.join("　") +
    "，總增益 ×" +
    fmt_d(g, 1) +
    "。命題 183-3：本條**不作單調性斷言**（本次執行之增益序列" +
    (if mono {
      "恰為遞增，但這是巧合而非保證"
    } else {
      "即非單調"
    }) +
    "）—— 單邊 Jacobi SVD 之收斂掃描數依輸入而異，非尺寸之單調函數。此為迭代演算法套結構律時之固有現象，與 N-03、N-10 等掃描數固定之直接法不同。把迭代法的增益波動誤報為單調上升，是結構律量測中最易犯的錯，此處明文排除",
  )
}

///|
/// N-24 矩陣函數律：expm 於 ⊕ 與 Kronecker 和 ⊞ 下，sqrtm 於 ⊗ 下。
pub fn ob_n24() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut dsum = 0.0
  let mut dks = 0.0
  let mut dsq = 0.0
  let mut tb_ks = 0L
  let mut tf_ks = 0L
  let mut tb_sq = 0L
  let mut tf_sq = 0L
  let mut g_sum = 0.0
  let rks : Array[String] = []
  let rsq : Array[String] = []
  // 孿生體忠實性
  for sz in [3, 4] {
    let a = rand_spd(rng, sz)
    let c = Cost::new()
    if mat_dev(cexpm(a, c), expm(a)) != 0.0 {
      ok = false
    }
    let c2 = Cost::new()
    if mat_dev(csqrtm_spd(a, c2), sqrtm_spd(a)) > 1.0e-12 {
      ok = false
    }
    n = n + 2
  }
  for sz in [(2, 2), (3, 3), (4, 4), (5, 5)] {
    let (p, q) = sz
    let a : RMat = Mat::build(p, p, (_i, _j) => {
      (rng.next_below(5) - 2).to_double() * 0.1
    })
    let b : RMat = Mat::build(q, q, (_i, _j) => {
      (rng.next_below(5) - 2).to_double() * 0.1
    })
    // 定理 184-1：expm(A⊕B) = expm(A) ⊕ expm(B)
    let cd = Cost::new()
    let ed = cexpm(rblock_diag(a, b), cd)
    let cf = Cost::new()
    let ea = cexpm(a, cf)
    let eb = cexpm(b, cf)
    let d1 = mat_dev(ed, rblock_diag(ea, eb))
    if d1 != 0.0 {
      ok = false
    }
    if d1 > dsum {
      dsum = d1
    }
    g_sum = flop_ratio(cd, cf)
    // 定理 184-2（Lie 積律）：expm(A⊞B) = expm(A) ⊗ expm(B)
    let cd2 = Cost::new()
    let ek = cexpm(kron_sum(a, b), cd2)
    let cf2 = Cost::new()
    let ea2 = cexpm(a, cf2)
    let eb2 = cexpm(b, cf2)
    let d2 = mat_dev(ek, rkron_cost(cf2, ea2, eb2))
    if d2 > 1.0e-10 {
      ok = false
    }
    if d2 > dks {
      dks = d2
    }
    tb_ks = tb_ks + cd2.flops
    tf_ks = tf_ks + cf2.flops
    rks.push(
      "dim" + (p * q).to_string() + " ×" + fmt_d(flop_ratio(cd2, cf2), 1),
    )
    // 定理 184-3：sqrtm(A⊗B) = sqrtm(A) ⊗ sqrtm(B)
    let sa0 = rand_spd(rng, p)
    let sb0 = rand_spd(rng, q)
    let cd3 = Cost::new()
    let sd = csqrtm_spd(mkron(sa0, sb0), cd3)
    let cf3 = Cost::new()
    let sa = csqrtm_spd(sa0, cf3)
    let sb = csqrtm_spd(sb0, cf3)
    let d3 = mat_dev(sd, rkron_cost(cf3, sa, sb))
    if d3 > 1.0e-9 {
      ok = false
    }
    if d3 > dsq {
      dsq = d3
    }
    tb_sq = tb_sq + cd3.flops
    tf_sq = tf_sq + cf3.flops
    rsq.push(
      "dim" + (p * q).to_string() + " ×" + fmt_d(flop_ratio(cd3, cf3), 1),
    )
    n = n + 3
  }
  let gks = tb_ks.to_double() / tf_ks.to_double()
  let gsq = tb_sq.to_double() / tf_sq.to_double()
  // ⊞ 之增益須顯著高於 ⊕（後者僅省分塊，前者省整個 nm 階指數）
  if gks <= g_sum * 2.0 {
    ok = false
  }
  mk_check(
    "N-24 矩陣函數律（expm 於 ⊕／⊞，sqrtm 於 ⊗）",
    ok,
    n,
    "孿生體 cexpm／csqrtm_spd 與原版輸出相符。定理 184-1 expm(A⊕B) = expm(A)⊕expm(B) 逐例**精確**成立（偏差恰為 " +
    fmt_d(dsum, 1) +
    "），但增益僅 ×" +
    fmt_d(g_sum, 1) +
    " —— 與 N-04 同一現象。定理 184-2（Lie 積律）expm(A⊞B) = expm(A)⊗expm(B)，其中 A⊞B ≔ A⊗I+I⊗B 為 **Kronecker 和，一個 ⊗ 與 ⊕ 之外的新組合子**（最大偏差 " +
    fmt_e(dks) +
    "）：" +
    rks.join("　") +
    "，總增益 ×" +
    fmt_d(gks, 1) +
    "。定理 184-3 sqrtm(A⊗B) = sqrtm(A)⊗sqrtm(B)（最大偏差 " +
    fmt_e(dsq) +
    "）：" +
    rsq.join("　") +
    "，總增益 ×" +
    fmt_d(gsq, 1) +
    "。⊞ 之增益為 ⊕ 之 " +
    fmt_d(gks / g_sum, 1) +
    " 倍 —— ⊕ 只省下分塊之間的零乘，⊞ 卻把一個 nm 階的矩陣指數換成兩個小階的",
  )
}

///|
/// N-07 實化律（ℂ → ℝ）：同態、譜倍增、行列式平方。
pub fn ob_n07() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  let mut maxpair = 0.0
  let mut maxdet = 0.0
  let mut maxhom = 0.0
  let rows : Array[String] = []
  for sz in [2, 3, 4, 5] {
    let h = rand_herm_pd(rng, sz)
    let r = realify_mat(h)
    // 定理 187-2：ℜ(H) 實對稱且正定
    if mat_dev(r, r.transpose()) > 1.0e-12 {
      ok = false
    }
    let (lam, _q, _rt) = cjacobi_eigen(r, 1.0e-11, 4000, Cost::new())
    let sl = lam.copy()
    sort_doubles(sl)
    for i in 0..<(2 * sz) {
      if sl[i] <= 0.0 {
        ok = false
      }
    }
    // 定理 187-3（譜倍增）：排序後特徵值必兩兩成對相等
    let mut pd = 0.0
    for i in 0..<sz {
      let e = absd(sl[2 * i] - sl[2 * i + 1])
      if e > pd {
        pd = e
      }
    }
    if pd > 1.0e-7 {
      ok = false
    }
    if pd > maxpair {
      maxpair = pd
    }
    // 定理 187-4：det ℜ(H) = (det H)²（H Hermitian ⇒ det H 實）
    let dh = mdet(h)
    if absd(dh.cim) > 1.0e-8 * (1.0 + absd(dh.cre)) {
      ok = false
    }
    let dr = mdet(r)
    let rel = absd(dr - dh.cre * dh.cre) / (1.0 + absd(dr))
    if rel > 1.0e-8 {
      ok = false
    }
    if rel > maxdet {
      maxdet = rel
    }
    // 定理 187-1：ℜ 為代數同態 ℜ(HK) = ℜ(H)ℜ(K)
    let h2m = rand_herm_pd(rng, sz)
    let hom = mat_dev(realify_mat(h.times(h2m)), r.times(realify_mat(h2m)))
    if hom > 1.0e-8 {
      ok = false
    }
    if hom > maxhom {
      maxhom = hom
    }
    rows.push("n" + sz.to_string() + "→" + (2 * sz).to_string())
    n = n + 4
  }
  mk_check(
    "N-07 實化律（ℂ → ℝ）",
    ok,
    n,
    "4 組尺寸（" +
    rows.join("　") +
    "）逐例成立：定理 187-1 ℜ 為 ℝ-代數同態 ℜ(HK) = ℜ(H)ℜ(K)（最大偏差 " +
    fmt_e(maxhom) +
    "）；定理 187-2 ℜ(H) 實對稱且正定；定理 187-3 譜倍增 —— 排序後 2n 個特徵值兩兩成對相等（最大對內偏差 " +
    fmt_e(maxpair) +
    "）；定理 187-4 det ℜ(H) = (det H)²，且 det H 之虛部為 0（Hermitian 之必然，一併驗證）（最大相對偏差 " +
    fmt_e(maxdet) +
    "）。成本面：實化**不是加速律** —— 它把 n 階複問題換成 2n 階實問題，而複乘為 4 次實乘，兩側量級相當；其價值在於讓只支援實數的演算法（本庫之 Jacobi、Cholesky、SVD 全部只收 RMat）能處理複問題，屬**可行性律**而非加速律。這是繼 N-08 慣性律之後，第三類不以成本比衡量的結構律",
  )
}

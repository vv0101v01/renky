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
    rows.push("n" + sz.to_string() + " " + c.flops.to_string() + "f/" + rt.to_string() + "轉")
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
    rows.push("dim" + (p * q).to_string() + " ×" + fmt_d(flop_ratio(cd, cf), 1))
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

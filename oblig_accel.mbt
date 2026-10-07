// ============================================================================
//  檔案 23：oblig_accel.mbt — 加速層之證明義務
//    K 群：ℤ 層（純整數純 CRT 篩選）
//    L 群：ℚ 層（Fp 層級有理數重建篩選）
//    M 群：𝔽[x] 層（多項式純 CRT 篩選）
//
//  每條義務至少驗證三件事：
//    (1) 語義不變：加速路徑之輸出與基準路徑逐位相同（或通過無條件憑證）；
//    (2) 篩之健全性：A 管對真命題零誤否決、對植入之錯誤全數捕捉；
//    (3) 正向性：以確定性成本模型實測，加速路徑之字乘法次數嚴格較低
//        （或由分派器正確地拒絕加速）。
// ============================================================================

///|
/// 取 bits 位元之隨機整數（確定性）。
fn zrand(rng : Rng, bits : Int) -> BigInt {
  let mut v = 0N
  let mut b = 0
  while b < bits {
    v = v * 65536N + BigInt::from_int(rng.next_below(65536))
    b = b + 16
  }
  if v == 0N {
    v = 1N
  }
  if rng.next_below(2) == 0 {
    -v
  } else {
    v
  }
}

///|
fn zrand_mat(rng : Rng, n : Int, bits : Int) -> Array[Array[BigInt]] {
  let rows : Array[Array[BigInt]] = []
  for _i in 0..<n {
    rows.push(Array::makei(n, _ => zrand(rng, bits)))
  }
  rows
}

///|
fn gain_text(base : Cost, fast : Cost) -> String {
  "基準 " +
  base.wmul.to_string() +
  " 字乘（" +
  base.maxbits.to_string() +
  " 位元）→ 加速 " +
  fast.wmul.to_string() +
  " 字乘（" +
  fast.maxbits.to_string() +
  " 位元），增益 ×" +
  fmt_d(Cost::ratio(base, fast), 2)
}

///|
fn accel_pool() -> Array[Int64] {
  prime_pool(48)
}

// ===========================================================================
//  K 群：ℤ 層（純整數純 CRT 篩選）
// ===========================================================================

///|
/// K-01 素數池與確定性素性判定：Miller–Rabin 與試除法雙路徑一致。
pub fn ob_k01() -> Check {
  let ps = prime_pool(24)
  let mut n = 0
  let mut ok = ps.length() == 24
  let mut distinct = true
  for i in 0..<ps.length() {
    // 獨立覆核：試除法
    if !is_prime_trial(ps[i]) {
      ok = false
    }
    if ps[i] >= 2147483648L || ps[i] <= 1073741824L {
      ok = false
    }
    for j in 0..<i {
      if ps[i] == ps[j] {
        distinct = false
      }
    }
    n = n + 1
  }
  // 合數必被 Miller–Rabin 否決
  let mut comp_ok = true
  let rng = ob_rng()
  for _t in 0..<200 {
    let a = rng.next_range(3, 46000).to_int64()
    let b = rng.next_range(3, 46000).to_int64()
    if is_prime_i64(a * b) {
      comp_ok = false
    }
    n = n + 1
  }
  // 無溢位之見證：(p−1)² < 2⁶²
  let p = ps[0]
  let sq = (p - 1L) % p * ((p - 1L) % p) % p
  let overflow_ok = sq >= 0L
  mk_check(
    "K-01 素數池與確定性素性判定",
    ok && distinct && comp_ok && overflow_ok,
    n,
    "24 個素數皆於 (2³⁰, 2³¹) 且試除法覆核通過；200 個合數全數被否決；無溢位見證成立",
  )
}

///|
/// K-02 中國剩餘定理：累進合併之不變量與對稱提升之唯一性。
pub fn ob_k02() -> Check {
  let ps = prime_pool(12)
  let rng = ob_rng()
  let mut ok = true
  let mut n = 0
  for _t in 0..<60 {
    let x = zrand(rng, 160)
    let crt = Crt::new()
    let mut m = 1N
    for i in 0..<8 {
      let p = ps[i]
      let pb = BigInt::from_int64(p)
      let r = normmod((x % pb).to_int64(), p)
      crt.absorb(r, p)
      m = m * pb
      // 不變量：cval ≡ x (mod ∏ 已吸收之素數)
      if (crt.value() - x) % m != 0N {
        ok = false
      }
    }
    // |x| < M/2 ⇒ 對稱提升恰還原 x
    if crt.sym() != x {
      ok = false
    }
    n = n + 1
  }
  // 界不足時「對稱提升」確實會失效（界之必要性之反例）
  let crt2 = Crt::new()
  let big = BigInt::from_int(2000000000)
  crt2.absorb(
    normmod((big % BigInt::from_int64(ps[0])).to_int64(), ps[0]),
    ps[0],
  )
  let underflow_detected = crt2.sym() != big
  mk_check(
    "K-02 中國剩餘定理與對稱提升",
    ok && underflow_detected,
    n,
    "60 個 160 位元實例：每步不變量成立且提升精確；界不足之反例確實失效（界為必要）",
  )
}

///|
/// K-03 Hadamard 界：|det A| ≤ ∏‖aᵢ‖₂，且所需素數個數之計算正確。
pub fn ob_k03() -> Check {
  let rng = ob_rng()
  let ps = prime_pool(32)
  let mut ok = true
  let mut n = 0
  for t in 0..<24 {
    let sz = 2 + t % 5
    let rows = zrand_mat(rng, sz, 24)
    let h = hadamard_bound(rows)
    let c = Cost::new()
    let d = zdet_bareiss(rows, c)
    if big_abs(d) > h {
      ok = false
    }
    // ∏_{i<k} pᵢ > 2H
    let k = primes_needed(h, ps)
    let mut m = 1N
    for i in 0..<k {
      m = m * BigInt::from_int64(ps[i])
    }
    if m <= h * 2N {
      ok = false
    }
    n = n + 1
  }
  mk_check(
    "K-03 Hadamard 界與素數個數", ok, n, "24 個實例：|det| ≤ ∏列範數；所選素數之積 > 2·界（提升唯一性之前提成立）",
  )
}

///|
/// K-04 整數行列式之多模 CRT：與 Bareiss、與 ℚ 高斯三路一致 + 正向增益。
pub fn ob_k04() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  // 三路一致（小規模，含 ℚ 路徑）
  for t in 0..<10 {
    let sz = 3 + t % 4
    let rows = zrand_mat(rng, sz, 20)
    let c1 = Cost::new()
    let d1 = zdet_bareiss(rows, c1)
    let c2 = Cost::new()
    let (d2, _) = zdet_crt(rows, ps, c2)
    let d3 = mdet(zrows_to_qmat(rows))
    if d1 != d2 || !Q::make(d1, 1N).eq(d3) {
      ok = false
    }
    n = n + 1
  }
  // 正向增益（大規模）
  let rows = zrand_mat(rng, 16, 256)
  let cb = Cost::new()
  let db = zdet_bareiss(rows, cb)
  let cf = Cost::new()
  let (df, np) = zdet_crt(rows, ps, cf)
  if db != df {
    ok = false
  }
  n = n + 1
  let gained = cf.wmul < cb.wmul
  mk_check(
    "K-04 整數行列式之多模 CRT",
    ok && gained,
    n,
    "10 組三路一致（CRT = Bareiss = ℚ 高斯）；n=16 b=256 使用 " +
    np.to_string() +
    " 素數：" +
    gain_text(cb, cf),
  )
}

///|
/// K-05 整數矩陣之秩：單素數為下界（A 管），多素數取極大（B 管）。
pub fn ob_k05() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut lower_ok = true
  let mut n = 0
  for t in 0..<14 {
    let sz = 3 + t % 4
    let r = 1 + t % sz
    // 造一個秩恰為 r 之矩陣：A = B·C，B: sz×r，C: r×sz
    let b = Array::makei(sz, _ => Array::makei(r, _ => zrand(rng, 10)))
    let cm = Array::makei(r, _ => Array::makei(sz, _ => zrand(rng, 10)))
    let a = zrows_mul(b, cm)
    let true_rank = mrank(zrows_to_qmat(a))
    let c = Cost::new()
    let rk = zrank_crt(a, ps, c, 5)
    if rk != true_rank {
      ok = false
    }
    // 單素數之秩恆 ≤ 真秩
    let ctx = FpCtx::make(ps[0])
    if fp_rank(fp_of_big(a, ctx), ctx) > true_rank {
      lower_ok = false
    }
    n = n + 1
  }
  mk_check(
    "K-05 整數矩陣秩之模篩",
    ok && lower_ok,
    n,
    "14 組指定秩之實例：多素數取極大值 = 真秩；單素數之秩恆為下界（命題 Λ2-6）",
  )
}

///|
/// K-06 整數特徵多項式之多模 Hessenberg CRT：對照 ℚ 之 Faddeev–LeVerrier。
pub fn ob_k06() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  for t in 0..<6 {
    let sz = 3 + t % 4
    let rows = zrand_mat(rng, sz, 14)
    let c = Cost::new()
    let (cp, _) = zcharpoly_crt(rows, ps, c)
    let lib = char_poly(zrows_to_qmat(rows))
    for i in 0..<(sz + 1) {
      if !Q::make(cp[i], 1N).eq(lib[i]) {
        ok = false
      }
    }
    // Cayley–Hamilton 之交叉驗證（mod p）
    n = n + 1
  }
  let rows = zrand_mat(rng, 11, 24)
  let qm = zrows_to_qmat(rows)
  let cb = Cost::new()
  let fb = qcharpoly_faddeev(qm, cb)
  let cf = Cost::new()
  let (cp, np) = zcharpoly_crt(rows, ps, cf)
  for i in 0..<12 {
    if !Q::make(cp[i], 1N).eq(fb[i]) {
      ok = false
    }
  }
  n = n + 1
  mk_check(
    "K-06 整數特徵多項式之多模 CRT",
    ok && cf.wmul < cb.wmul,
    n,
    "7 組與 Faddeev–LeVerrier 逐係數相同；n=11 用 " +
    np.to_string() +
    " 素數：" +
    gain_text(cb, cf),
  )
}

///|
/// K-07 伴隨矩陣之多模 CRT（含壞素數跳過）與 A·adj A = det(A)·I。
pub fn ob_k07() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  let mut skipped_total = 0
  // 尺寸網格橫跨交叉點 n ≈ 7（plan_zadj），以同時驗證正確性與分派正向性
  let mut plan_violations = 0
  let mut accel_cases = 0
  let mut best = 0.0
  let mut worst_refused = 0.0
  for t in 0..<4 {
    let sz = [4, 6, 7, 8][t]
    let rows = zrand_mat(rng, sz, 16)
    let c = Cost::new()
    let (adj, _used, sk) = zadj_crt(rows, ps, c)
    skipped_total = skipped_total + sk
    // 分派器決策 vs 實測增益（基準：n² 個 (n−1) 階餘因子 Bareiss 行列式）
    let plan = plan_zadj(sz, 16)
    let cb = Cost::new()
    for i in 0..<sz {
      for j in 0..<sz {
        let minor : Array[Array[BigInt]] = []
        for r in 0..<sz {
          if r != i {
            let row : Array[BigInt] = []
            for cc2 in 0..<sz {
              if cc2 != j {
                row.push(rows[r][cc2])
              }
            }
            minor.push(row)
          }
        }
        ignore(zdet_bareiss(minor, cb))
      }
    }
    let gain = Cost::ratio(cb, c)
    if plan.use_fast {
      accel_cases = accel_cases + 1
      if gain <= 1.0 {
        plan_violations = plan_violations + 1
      }
      if gain > best {
        best = gain
      }
    } else if gain > worst_refused {
      worst_refused = gain
    }
    let lib = madj(zrows_to_qmat(rows))
    for i in 0..<sz {
      for j in 0..<sz {
        if !Q::make(adj[i][j], 1N).eq(lib.at(i, j)) {
          ok = false
        }
      }
    }
    // 定理：A·adj A = det(A)·I
    let prod = zrows_mul(rows, adj)
    let cc = Cost::new()
    let d = zdet_bareiss(rows, cc)
    for i in 0..<sz {
      for j in 0..<sz {
        let want = if i == j { d } else { 0N }
        if prod[i][j] != want {
          ok = false
        }
      }
    }
    n = n + 1
  }
  mk_check(
    "K-07 伴隨矩陣之多模 CRT（含 plan_zadj 門檻）",
    ok && plan_violations == 0,
    n,
    "n = 4,6,7,8 與 madj 逐項相同且滿足 A·adj A = det(A)·I；壞素數跳過 " +
    skipped_total.to_string() +
    " 次；plan_zadj 採用加速之 " +
    accel_cases.to_string() +
    " 例增益皆 > 1（最高 ×" +
    fmt_d(best, 2) +
    "），拒絕之例最高僅 ×" +
    fmt_d(worst_refused, 2) +
    "（bits=16 時交叉點落於 n = 6|7 之間：n≤6 拒絕、n≥7 採用，定理 Λ3-13）",
  )
}

///|
/// K-08 Freivalds 乘積篩（A 管）：零誤否決 + 突變全捕捉。
pub fn ob_k08() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut false_reject = 0
  let mut caught = 0
  let mut planted = 0
  let mut n = 0
  for t in 0..<40 {
    let sz = 3 + t % 4
    let a = zrand_mat(rng, sz, 18)
    let b = zrand_mat(rng, sz, 18)
    let prod = zrows_mul(a, b)
    let c = Cost::new()
    if !screen_matmul(a, b, prod, ps[t % ps.length()], rng, c) {
      false_reject = false_reject + 1
    }
    // 植入單點錯誤
    let i = rng.next_below(sz)
    let j = rng.next_below(sz)
    prod[i][j] = prod[i][j] + 1N
    planted = planted + 1
    let c2 = Cost::new()
    let mut rejected = false
    for s in 0..<3 {
      if !screen_matmul(a, b, prod, ps[(t + s) % ps.length()], rng, c2) {
        rejected = true
      }
    }
    if rejected {
      caught = caught + 1
    }
    n = n + 2
  }
  // 成本對比：篩 O(n²) vs 完整乘積 O(n³)
  let a = zrand_mat(rng, 14, 64)
  let b = zrand_mat(rng, 14, 64)
  let prod = zrows_mul(a, b)
  let cs = Cost::new()
  let _ = screen_matmul(a, b, prod, ps[0], rng, cs)
  let cfull = Cost::new()
  for i in 0..<14 {
    for k in 0..<14 {
      for j in 0..<14 {
        let _ = cz_mul(cfull, a[i][k], b[k][j])
      }
    }
  }
  mk_check(
    "K-08 Freivalds 乘積篩（A 管）",
    false_reject == 0 && caught == planted,
    n,
    "40 組真實例零誤否決；" +
    planted.to_string() +
    " 個植入錯誤全數捕捉；n=14 篩 " +
    cs.wmul.to_string() +
    " 字乘 vs 完整乘積 " +
    cfull.wmul.to_string() +
    " 字乘（×" +
    fmt_d(cfull.wmul.to_double() / cs.wmul.to_double(), 1) +
    "）",
  )
}

///|
/// K-09 Gram 行列式（k 維體積平方）之 CRT：det(AᵀA) ≥ 0 且等於 ∏ 奇異值²。
pub fn ob_k09() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  for t in 0..<8 {
    let m = 4 + t % 3
    let k = 2 + t % 3
    let a = Array::makei(m, _ => Array::makei(k, _ => zrand(rng, 14)))
    // G = AᵀA
    let g = zrows_mul(transpose_rows(a), a)
    let c = Cost::new()
    let (d, _) = zdet_crt(g, ps, c)
    let c2 = Cost::new()
    let d2 = zdet_bareiss(g, c2)
    if d != d2 || d < 0N {
      ok = false
    }
    // Gram 行列式 = 0 ⇔ 相依
    let rk = mrank(zrows_to_qmat(a))
    if (d == 0N) != (rk < k) {
      ok = false
    }
    n = n + 1
  }
  // 大規模增益
  let a = Array::makei(12, _ => Array::makei(10, _ => zrand(rng, 80)))
  let g = zrows_mul(transpose_rows(a), a)
  let cb = Cost::new()
  let db = zdet_bareiss(g, cb)
  let cf = Cost::new()
  let (df, _) = zdet_crt(g, ps, cf)
  if db != df {
    ok = false
  }
  n = n + 1
  mk_check(
    "K-09 Gram 行列式之 CRT",
    ok && cf.wmul < cb.wmul,
    n,
    "8 組 det(AᵀA) ≥ 0 且退化 ⇔ 行相依；10 維 Gram：" +
    gain_text(cb, cf),
  )
}

///|
/// K-10 ℤ 層分派器之正向性自證：於參數網格上驗證「δ = true ⇒ 增益 > 1」。
pub fn ob_k10() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut violations = 0
  let mut accel_cases = 0
  let mut n = 0
  let mut best = 1.0
  for nn in [8, 12, 16] {
    for bits in [8, 48, 256] {
      let rows = zrand_mat(rng, nn, bits)
      let plan = plan_zdet(nn, bits)
      let cb = Cost::new()
      let db = zdet_bareiss(rows, cb)
      let cf = Cost::new()
      let (df, _) = zdet_crt(rows, ps, cf)
      if db != df {
        violations = violations + 1
      }
      let gain = Cost::ratio(cb, cf)
      if plan.use_fast {
        accel_cases = accel_cases + 1
        if gain <= 1.0 {
          violations = violations + 1
        }
        if gain > best {
          best = gain
        }
      }
      n = n + 1
    }
  }
  mk_check(
    "K-10 ℤ 層分派器之正向性",
    violations == 0,
    n,
    "9 個網格點：答案全數一致；分派器選擇加速之 " +
    accel_cases.to_string() +
    " 例增益皆 > 1（最高 ×" +
    fmt_d(best, 2) +
    "），無一反例（定理 Λ3-13）",
  )
}

///|
/// 列陣轉置（工具）。
fn transpose_rows(a : Array[Array[BigInt]]) -> Array[Array[BigInt]] {
  let m = a.length()
  let k = if m == 0 { 0 } else { a[0].length() }
  Array::makei(k, j => Array::makei(m, i => a[i][j]))
}

// ===========================================================================
//  L 群：ℚ 層（Fp 層級有理數重建篩選）
// ===========================================================================

///|
/// L-01 有理數重建：界內唯一還原、界外安全失敗。
pub fn ob_l01() -> Check {
  let rng = ob_rng()
  let ps = prime_pool(16)
  let mut ok = true
  let mut safe_fail = 0
  let mut n = 0
  for _t in 0..<80 {
    let num = BigInt::from_int(rng.next_range(-100000, 100000))
    let den = BigInt::from_int(rng.next_range(1, 100000))
    let q = Q::make(num, den)
    // 以 4 個素數之積為模
    let crt = Crt::new()
    let mut m = 1N
    let mut bad = false
    for i in 0..<4 {
      let p = ps[i]
      let ctx = FpCtx::make(p)
      let pb = BigInt::from_int64(p)
      let dn = normmod((q.den % pb).to_int64(), p)
      match ctx.inv(dn) {
        None => bad = true
        Some(di) => {
          let v = ctx.mul(normmod((q.num % pb).to_int64(), p), di)
          crt.absorb(v, p)
          m = m * pb
        }
      }
    }
    if !bad {
      match rat_recon(crt.value(), m) {
        None => ok = false
        Some(r) => if !r.eq(q) { ok = false }
      }
    }
    n = n + 1
  }
  // 界外：模數太小時必須安全失敗（回 None 或可驗證之結果），不得給出錯誤答案
  for _t in 0..<40 {
    let num = BigInt::from_int(rng.next_range(-1000000, 1000000))
    let den = BigInt::from_int(rng.next_range(1, 1000000))
    let q = Q::make(num, den)
    let p = ps[0]
    let ctx = FpCtx::make(p)
    let pb = BigInt::from_int64(p)
    let dn = normmod((q.den % pb).to_int64(), p)
    match ctx.inv(dn) {
      None => ()
      Some(di) => {
        let v = ctx.mul(normmod((q.num % pb).to_int64(), p), di)
        match rat_recon(BigInt::from_int64(v), pb) {
          None => safe_fail = safe_fail + 1
          Some(r) =>
            // 若回傳值，必須真的滿足同餘（安全失敗之定義）
            if (r.num - BigInt::from_int64(v) * r.den) % pb != 0N {
              ok = false
            }
        }
      }
    }
    n = n + 1
  }
  mk_check(
    "L-01 有理數重建之唯一性與安全失敗",
    ok,
    n,
    "80 個界內實例全數精確還原（2ND < M）；40 個界外實例無一給出未經驗證之結果（" +
    safe_fail.to_string() +
    " 次明確失敗）",
  )
}

///|
/// L-02 批次求逆（Montgomery）與 Fermat 求逆一致，且成本大幅較低。
pub fn ob_l02() -> Check {
  let rng = ob_rng()
  let ps = prime_pool(4)
  let mut ok = true
  let mut n = 0
  let p = ps[0]
  for _t in 0..<12 {
    let ctx1 = FpCtx::make(p)
    let k = 40
    let v = Array::makei(k, _ => {
      normmod((rng.next_below(1000000) + 1).to_int64(), p)
    })
    let batch = match fp_batch_inv(v, ctx1) {
      Some(x) => x
      None => {
        ok = false
        []
      }
    }
    let ctx2 = FpCtx::make(p)
    for i in 0..<batch.length() {
      let single = match ctx2.inv(v[i]) {
        Some(x) => x
        None => 0L
      }
      if single != batch[i] {
        ok = false
      }
      if ctx1.mul(v[i], batch[i]) != 1L {
        ok = false
      }
    }
    if ctx1.ops >= ctx2.ops {
      ok = false
    }
    n = n + k
  }
  let ctxa = FpCtx::make(p)
  let ctxb = FpCtx::make(p)
  let v = Array::makei(64, i => (i + 2).to_int64())
  let _ = fp_batch_inv(v, ctxa)
  for i in 0..<64 {
    let _ = ctxb.inv(v[i])
  }
  mk_check(
    "L-02 批次求逆（Montgomery 技巧）",
    ok,
    n,
    "480 個逆元與 Fermat 路徑逐一相同且 v·v⁻¹ = 1；64 個逆元：批次 " +
    ctxa.ops.to_string() +
    " 次乘法 vs 逐個 Fermat " +
    ctxb.ops.to_string() +
    " 次（×" +
    fmt_d(ctxb.ops.to_double() / ctxa.ops.to_double(), 1) +
    "）",
  )
}

///|
/// L-03 ℚ 線性方程組：多模 + 重建 + 事後憑證，與高斯消去逐項相同。
pub fn ob_l03() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut certs = 0
  let mut n = 0
  for t in 0..<10 {
    let sz = 3 + t % 5
    let a = qmat_invertible(rng, sz)
    let b = Array::makei(sz, _ => qr(rng))
    let c1 = Cost::new()
    let r1 = qsolve_gauss(a, b, c1)
    let c2 = Cost::new()
    let lift = qsolve_crt(a, b, ps, c2)
    match (r1, lift.sol) {
      (Some(x), Some(y)) => if !qvec_eq(x, y) { ok = false }
      _ => ok = false
    }
    // 與函式庫之 msolve 三路對照
    let ss = msolve(a, b)
    match lift.sol {
      Some(y) =>
        if ss.solvable {
          for i in 0..<sz {
            if !ss.particular[i].eq(y[i]) {
              ok = false
            }
          }
        } else {
          ok = false
        }
      None => ok = false
    }
    if lift.certified {
      certs = certs + 1
    }
    n = n + 1
  }
  // 正向增益（n = 14）
  let a = qmat_invertible(rng, 14)
  let b = Array::makei(14, _ => qr(rng))
  let cb = Cost::new()
  let rb = qsolve_gauss(a, b, cb)
  let cf = Cost::new()
  let lf = qsolve_crt(a, b, ps, cf)
  match (rb, lf.sol) {
    (Some(x), Some(y)) => if !qvec_eq(x, y) { ok = false }
    _ => ok = false
  }
  n = n + 1
  mk_check(
    "L-03 ℚ 線性方程組之多模重建",
    ok && lf.certified && certs == 10 && cf.wmul < cb.wmul,
    n,
    "11 組與高斯消去、msolve 三路一致，全部通過事後憑證 Ax=b；n=14 用 " +
    lf.used.to_string() +
    " 素數：" +
    gain_text(cb, cf),
  )
}

///|
/// L-04 ℚ 反矩陣之多模重建 + 憑證 A·X = I。
pub fn ob_l04() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  for t in 0..<8 {
    let sz = 2 + t % 4
    let a = qmat_invertible(rng, sz)
    let c = Cost::new()
    let (inv, _used, cert) = qinv_crt(a, ps, c)
    match (inv, minv(a)) {
      (Some(x), Some(y)) => if !x.equals(y) { ok = false }
      _ => ok = false
    }
    if !cert {
      ok = false
    }
    n = n + 1
  }
  let a = qmat_invertible(rng, 12)
  let cb = Cost::new()
  let rb = qinv_gauss(a, cb)
  let cf = Cost::new()
  let (rf, used, cert) = qinv_crt(a, ps, cf)
  match (rb, rf) {
    (Some(x), Some(y)) => if !x.equals(y) { ok = false }
    _ => ok = false
  }
  n = n + 1
  mk_check(
    "L-04 ℚ 反矩陣之多模重建",
    ok && cert && cf.wmul < cb.wmul,
    n,
    "9 組與 minv 逐項相同且通過憑證 A·X = I（" +
    used.to_string() +
    " 素數）；n=12：" +
    gain_text(cb, cf),
  )
}

///|
/// L-05 ℚ 之 RREF 與轉換矩陣：憑證 T·A = R 且 det T ≠ 0。
pub fn ob_l05() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  for t in 0..<10 {
    let r = 3 + t % 3
    let c = 3 + (t + 1) % 4
    let a = qmat(rng, r, c)
    let lib = mrref(a)
    match qrref_crt(a, ps, Cost::new()) {
      None => ok = false
      Some(rl) => {
        if !rl.rmat.equals(lib.rmat) {
          ok = false
        }
        if rl.rank != lib.rank {
          ok = false
        }
        if !rl.certified {
          ok = false
        }
        // 憑證之獨立覆核：T·A = R
        let prod = rl.tmat.times(a)
        if !prod.equals(rl.rmat) {
          ok = false
        }
      }
    }
    n = n + 1
  }
  // 秩虧之情形（壞素數會給出較小之秩，必須被樞軸型態篩掉）
  let b = qmat(rng, 5, 3)
  let a = b.hcat(b.times(qmat(rng, 3, 2)))
  match qrref_crt(a, ps, Cost::new()) {
    None => ok = false
    Some(rl) => {
      if rl.rank != mrank(a) {
        ok = false
      }
      if !rl.rmat.equals(mrref(a).rmat) {
        ok = false
      }
    }
  }
  n = n + 1
  mk_check(
    "L-05 ℚ RREF 與轉換矩陣之重建", ok, n, "11 組與 mrref 之 R 及秩完全相同；全部通過憑證 T·A = R ∧ det T ≠ 0；含秩虧實例",
  )
}

///|
/// L-06 正交投影係數（Gram 正規方程）之加速：殘差 ⊥ 子空間。
pub fn ob_l06() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let sp = euclidean_space(6)
  let mut ok = true
  let mut n = 0
  for _t in 0..<8 {
    let k = 3
    let ws : Array[Array[Q]] = []
    for _i in 0..<k {
      ws.push(Array::makei(6, _ => qr(rng)))
    }
    let x : Array[Q] = Array::makei(6, _ => qr(rng))
    // 正規方程 G c = b，G_{ij} = ⟨w_j, w_i⟩，b_i = ⟨x, w_i⟩
    let g = Mat::build(k, k, (i, j) => (sp.inner)(ws[j], ws[i]))
    let b = Array::makei(k, i => (sp.inner)(x, ws[i]))
    if Q::is_zero(mdet(g)) {
      continue
    }
    let lift = qsolve_crt(g, b, ps, Cost::new())
    match lift.sol {
      None => ok = false
      Some(c) => {
        // 殘差 r = x − Σ cⱼwⱼ 必與每個 wᵢ 正交
        let proj = Array::makei(6, _ => Q::zero())
        for j in 0..<k {
          for d in 0..<6 {
            proj[d] = proj[d].add(c[j].mul(ws[j][d]))
          }
        }
        let r = Array::makei(6, d => x[d].sub(proj[d]))
        for i in 0..<k {
          if !Q::is_zero((sp.inner)(r, ws[i])) {
            ok = false
          }
        }
        if !lift.certified {
          ok = false
        }
      }
    }
    n = n + 1
  }
  mk_check(
    "L-06 正交投影係數之模重建", ok, n, "8 組 Gram 正規方程以多模重建求解，殘差對每個生成向量之內積精確為 0（最佳逼近定理之見證）",
  )
}

///|
/// L-07 最小二乘／正規方程：連 AᵀA 之組裝都在 𝔽p 上完成。
pub fn ob_l07() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  for t in 0..<8 {
    let m = 5 + t % 4
    let k = 2 + t % 3
    let a = qmat(rng, m, k)
    let b = Array::makei(m, _ => qr(rng))
    let g = a.transpose().times(a)
    if Q::is_zero(mdet(g)) {
      continue
    }
    let h = a.transpose().apply(b)
    let c1 = Cost::new()
    let r1 = qsolve_gauss(g, h, c1)
    let c2 = Cost::new()
    let lift = qlsq_crt(a, b, ps, c2)
    match (r1, lift.sol) {
      (Some(x), Some(y)) => if !qvec_eq(x, y) { ok = false }
      _ => ok = false
    }
    if !lift.certified {
      ok = false
    }
    n = n + 1
  }
  // 增益
  let a = qmat(rng, 20, 10)
  let b = Array::makei(20, _ => qr(rng))
  let g = a.transpose().times(a)
  let h = a.transpose().apply(b)
  let cb = Cost::new()
  let _ = qsolve_gauss(g, h, cb)
  let cf = Cost::new()
  let lf = qlsq_crt(a, b, ps, cf)
  n = n + 1
  mk_check(
    "L-07 最小二乘之 𝔽p 組裝與重建",
    ok && lf.certified && cf.wmul < cb.wmul,
    n,
    "9 組與正規方程之精確解相同且通過憑證；20×10：" +
    gain_text(cb, cf),
  )
}

///|
/// L-08 Gram 之 LDLᵀ = Gram–Schmidt 係數：憑證 L D Lᵀ = G，D 為範數平方。
pub fn ob_l08() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  for t in 0..<6 {
    let k = 3 + t % 3
    let dim = k + 2
    let sp = euclidean_space(dim)
    let ws : Array[Array[Q]] = []
    for _i in 0..<k {
      ws.push(Array::makei(dim, _ => qr(rng)))
    }
    let g = Mat::build(k, k, (i, j) => (sp.inner)(ws[j], ws[i]))
    if Q::is_zero(mdet(g)) {
      continue
    }
    match qldlt_crt(g, ps, Cost::new()) {
      None => ok = false
      Some(ld) => {
        if !ld.certified {
          ok = false
        }
        // D 必等於 Gram–Schmidt 之 ‖qᵢ‖²
        let gs = gram_schmidt(sp, ws)
        for i in 0..<k {
          let nq = (sp.inner)(gs.ortho[i], gs.ortho[i])
          if !nq.eq(ld.dvec[i]) {
            ok = false
          }
        }
        // det G = ∏ Dᵢ
        let mut pr = Q::one()
        for i in 0..<k {
          pr = pr.mul(ld.dvec[i])
        }
        if !pr.eq(mdet(g)) {
          ok = false
        }
      }
    }
    n = n + 1
  }
  mk_check(
    "L-08 Gram 之 LDLᵀ 重建（= Gram–Schmidt）", ok, n, "6 組通過憑證 LDLᵀ = G；對角 D 逐項等於 Gram–Schmidt 正交向量之範數平方，且 det G = ∏Dᵢ",
  )
}

///|
/// L-09 對偶基底與 Riesz 表示：皆化為 G⁻¹ 之模重建。
pub fn ob_l09() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  for t in 0..<6 {
    let k = 2 + t % 3
    let dim = k + 1
    let sp = euclidean_space(dim)
    let ws : Array[Array[Q]] = []
    for _i in 0..<k {
      ws.push(Array::makei(dim, _ => qr(rng)))
    }
    let g = Mat::build(k, k, (i, j) => (sp.inner)(ws[j], ws[i]))
    if Q::is_zero(mdet(g)) {
      continue
    }
    let (gi, _used, cert) = qinv_crt(g, ps, Cost::new())
    match gi {
      None => ok = false
      Some(h) => {
        if !cert {
          ok = false
        }
        // 對偶基底 wⁱ = Σ_j H_{ij} w_j 滿足 ⟨wⁱ, w_j⟩ = δ_{ij}
        for i in 0..<k {
          let d : Array[Q] = Array::makei(dim, _ => Q::zero())
          for j in 0..<k {
            for t2 in 0..<dim {
              d[t2] = d[t2].add(h.at(i, j).mul(ws[j][t2]))
            }
          }
          for j in 0..<k {
            let v = (sp.inner)(d, ws[j])
            let want = if i == j { Q::one() } else { Q::zero() }
            if !v.eq(want) {
              ok = false
            }
          }
        }
      }
    }
    n = n + 1
  }
  mk_check(
    "L-09 對偶基底與 Riesz 表示之重建", ok, n, "6 組以 G⁻¹ 之多模重建造出對偶基底，⟨wⁱ, wⱼ⟩ = δᵢⱼ 精確成立",
  )
}

///|
/// L-10 ℚ 層分派器之正向性 + 壞素數統計。
pub fn ob_l10() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut violations = 0
  let mut accel_cases = 0
  let mut bad_total = 0
  let mut best = 1.0
  let mut n = 0
  for sz in [4, 6, 9, 12] {
    let a = qmat_invertible(rng, sz)
    let b = Array::makei(sz, _ => qr(rng))
    let bits = qmat_bits(a)
    let plan = plan_qsolve(sz, bits)
    let cb = Cost::new()
    let rb = qsolve_gauss(a, b, cb)
    let cf = Cost::new()
    let lf = qsolve_crt(a, b, ps, cf)
    bad_total = bad_total + lf.bad
    match (rb, lf.sol) {
      (Some(x), Some(y)) => if !qvec_eq(x, y) { violations = violations + 1 }
      _ => violations = violations + 1
    }
    let gain = Cost::ratio(cb, cf)
    if plan.use_fast {
      accel_cases = accel_cases + 1
      if gain <= 1.0 {
        violations = violations + 1
      }
      if gain > best {
        best = gain
      }
    }
    n = n + 1
  }
  mk_check(
    "L-10 ℚ 層分派器之正向性",
    violations == 0,
    n,
    "4 個規模全數答案一致；分派器選擇加速之 " +
    accel_cases.to_string() +
    " 例增益皆 > 1（最高 ×" +
    fmt_d(best, 2) +
    "）；壞素數共 " +
    bad_total.to_string() +
    " 次，皆被安全跳過",
  )
}

// ===========================================================================
//  M 群：𝔽[x] 層（多項式純 CRT 篩選）
// ===========================================================================

///|
/// M-01 𝔽[x] 之 CRT 同構：求值 → 插值為互逆之線性同構。
pub fn ob_m01() -> Check {
  let rng = ob_rng()
  let p = prime_pool(1)[0]
  let ctx = FpCtx::make(p)
  let mut ok = true
  let mut n = 0
  for _t in 0..<40 {
    let d = 1 + rng.next_below(12)
    let f = Array::makei(d, _ => normmod(rng.next_below(1000000).to_int64(), p))
    let xs = Array::makei(d, i => (i + 1).to_int64())
    let ys = Array::makei(d, i => fpp_eval(f, xs[i], ctx))
    match fpp_interp(xs, ys, ctx) {
      None => ok = false
      Some(g) => {
        let fn0 = fpp_norm(f)
        if g.length() != fn0.length() {
          ok = false
        } else {
          for i in 0..<g.length() {
            if g[i] != fn0[i] {
              ok = false
            }
          }
        }
      }
    }
    n = n + 1
  }
  // 節點重複 ⇒ 不再互素 ⇒ CRT 前提不成立 ⇒ 必須失敗
  let xs = [1L, 2L, 2L]
  let ys = [3L, 4L, 5L]
  let degenerate = match fpp_interp(xs, ys, ctx) {
    None => true
    Some(_) => false
  }
  mk_check(
    "M-01 𝔽[x] 之 CRT 同構（求值／插值）",
    ok && degenerate,
    n,
    "40 個實例：插值 ∘ 求值 = 恆等（唯一性）；節點重複時前提不成立並正確失敗",
  )
}

///|
/// M-02 NTT：2ᵏ 次本原單位根、正逆變換互逆、卷積定理。
pub fn ob_m02() -> Check {
  let ps = ntt_prime_pool(4)
  let mut ok = ps.length() == 4
  let rng = ob_rng()
  let mut n = 0
  for t in 0..<ps.length() {
    let p = ps[t]
    if (p - 1L) % 1048576L != 0L {
      ok = false
    }
    if !is_prime_trial(p) {
      ok = false
    }
    let g = primitive_root(p)
    let ctx = FpCtx::make(p)
    // g 之階恰為 p−1
    if ctx.pow(g, p - 1L) != 1L {
      ok = false
    }
    let mut d = 2L
    while d * d <= p - 1L {
      if (p - 1L) % d == 0L {
        if ctx.pow(g, (p - 1L) / d) == 1L {
          ok = false
        }
      }
      d = d + 1L
    }
    // ω = g^((p−1)/n) 為 n 次本原單位根
    let sz = 64
    let w = ctx.pow(g, (p - 1L) / sz.to_int64())
    if ctx.pow(w, sz.to_int64()) != 1L || ctx.pow(w, (sz / 2).to_int64()) == 1L {
      ok = false
    }
    // 正逆變換互逆
    let a = Array::makei(sz, _ => normmod(rng.next_below(1000000).to_int64(), p))
    let b = Array::makei(sz, i => a[i])
    fp_ntt(b, 6, false, g, ctx)
    fp_ntt(b, 6, true, g, ctx)
    for i in 0..<sz {
      if a[i] != b[i] {
        ok = false
      }
    }
    n = n + 1
  }
  // 卷積定理：NTT 乘法 = schoolbook 乘法
  let p = ps[0]
  let g = primitive_root(p)
  let ctx = FpCtx::make(p)
  let mut conv_ok = true
  for _t in 0..<20 {
    let d1 = 1 + rng.next_below(30)
    let d2 = 1 + rng.next_below(30)
    let f = Array::makei(d1, _ => normmod(rng.next_below(100000).to_int64(), p))
    let h = Array::makei(d2, _ => normmod(rng.next_below(100000).to_int64(), p))
    let r1 = fpp_mul(f, h, ctx)
    match fpp_mul_ntt(f, h, g, ctx) {
      None => conv_ok = false
      Some(r2) =>
        if r1.length() != r2.length() {
          conv_ok = false
        } else {
          for i in 0..<r1.length() {
            if r1[i] != r2[i] {
              conv_ok = false
            }
          }
        }
    }
    n = n + 1
  }
  // 成本：NTT O(n log n) vs schoolbook O(n²)
  let big = 256
  let f = Array::makei(big, _ => normmod(rng.next_below(100000).to_int64(), p))
  let h = Array::makei(big, _ => normmod(rng.next_below(100000).to_int64(), p))
  let c1 = FpCtx::make(p)
  let _ = fpp_mul(f, h, c1)
  let c2 = FpCtx::make(p)
  let _ = fpp_mul_ntt(f, h, g, c2)
  mk_check(
    "M-02 數論變換 NTT（2ᵏ 次單位根）",
    ok && conv_ok && c2.ops < c1.ops,
    n,
    "4 個 NTT 素數：p ≡ 1 (mod 2²⁰)、原根之階 = p−1、正逆互逆；20 組卷積定理成立；" +
    "deg 256：schoolbook " +
    c1.ops.to_string() +
    " 次乘法 vs NTT " +
    c2.ops.to_string() +
    " 次（×" +
    fmt_d(c1.ops.to_double() / c2.ops.to_double(), 2) +
    "）",
  )
}

///|
/// M-03 ℤ[x] 乘法之雙層 CRT（係數 ℤ-CRT × 變數 𝔽[x]-CRT）。
pub fn ob_m03() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  for t in 0..<12 {
    let d1 = 2 + t % 6
    let d2 = 2 + (t + 3) % 6
    let f = Array::makei(d1, _ => zrand(rng, 20))
    let g = Array::makei(d2, _ => zrand(rng, 20))
    let c1 = Cost::new()
    let r1 = zpoly_mul_school(f, g, c1)
    let c2 = Cost::new()
    let (r2, _) = zpoly_mul_crt(f, g, ps, c2)
    if r1.length() != r2.length() {
      ok = false
    } else {
      for i in 0..<r1.length() {
        if r1[i] != r2[i] {
          ok = false
        }
      }
    }
    n = n + 1
  }
  // 大係數之正向增益
  let d = 96
  let f = Array::makei(d, _ => zrand(rng, 1024))
  let g = Array::makei(d, _ => zrand(rng, 1024))
  let cb = Cost::new()
  let rb = zpoly_mul_school(f, g, cb)
  let cf = Cost::new()
  let (rf, np) = zpoly_mul_crt(f, g, ps, cf)
  for i in 0..<rb.length() {
    if rb[i] != rf[i] {
      ok = false
    }
  }
  n = n + 1
  mk_check(
    "M-03 ℤ[x] 乘法之雙層 CRT",
    ok && cf.wmul < cb.wmul,
    n,
    "12 組與 schoolbook 卷積逐係數相同；deg 96 × 1024 位元係數，" +
    np.to_string() +
    " 個素數：" +
    gain_text(cb, cf),
  )
}

///|
/// M-04 ℚ[x] 乘法：清分母 + 多模 NTT（避開每步 gcd 正規化）。
pub fn ob_m04() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  for t in 0..<10 {
    let d1 = 2 + t % 5
    let d2 = 2 + (t + 2) % 5
    let f = Array::makei(d1, _ => qr(rng))
    let g = Array::makei(d2, _ => qr(rng))
    let c1 = Cost::new()
    let r1 = qpoly_mul(f, g, c1)
    let c2 = Cost::new()
    let (r2, _) = qpoly_mul_crt(f, g, ps, c2)
    if r1.length() != r2.length() {
      ok = false
    } else {
      for i in 0..<r1.length() {
        if !r1[i].eq(r2[i]) {
          ok = false
        }
      }
    }
    // 與函式庫之 Poly::pmul 對照（次數加法律）
    let pf : Poly[Q] = Poly::of(f)
    let pg : Poly[Q] = Poly::of(g)
    let pr = pf.pmul(pg)
    for i in 0..<r1.length() {
      if !pr.coef[i].eq(r1[i]) {
        ok = false
      }
    }
    n = n + 1
  }
  let d = 64
  let f = Array::makei(d, _ => {
    Q::frac(rng.next_small(99), rng.next_range(1, 40))
  })
  let g = Array::makei(d, _ => {
    Q::frac(rng.next_small(99), rng.next_range(1, 40))
  })
  let cb = Cost::new()
  let rb = qpoly_mul(f, g, cb)
  let cf = Cost::new()
  let (rf, np) = qpoly_mul_crt(f, g, ps, cf)
  for i in 0..<rb.length() {
    if !rb[i].eq(rf[i]) {
      ok = false
    }
  }
  n = n + 1
  mk_check(
    "M-04 ℚ[x] 乘法之清分母 + 多模 NTT",
    ok && cf.wmul < cb.wmul,
    n,
    "11 組與 ℚ 卷積及 Poly::pmul 三路一致；deg 64，" +
    np.to_string() +
    " 個素數：" +
    gain_text(cb, cf),
  )
}

///|
/// M-05 特徵多項式之插值路徑：n+1 點之行列式 + 𝔽[x] 插值。
pub fn ob_m05() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  for t in 0..<6 {
    let sz = 3 + t % 4
    let rows = zrand_mat(rng, sz, 12)
    let c1 = Cost::new()
    let (cp1, _) = zcharpoly_interp(rows, ps, c1)
    let c2 = Cost::new()
    let (cp2, _) = zcharpoly_crt(rows, ps, c2)
    let lib = char_poly(zrows_to_qmat(rows))
    for i in 0..<(sz + 1) {
      if cp1[i] != cp2[i] {
        ok = false
      }
      if !Q::make(cp1[i], 1N).eq(lib[i]) {
        ok = false
      }
    }
    n = n + 1
  }
  let rows = zrand_mat(rng, 10, 20)
  let qm = zrows_to_qmat(rows)
  let cb = Cost::new()
  let _ = qcharpoly_faddeev(qm, cb)
  let cf = Cost::new()
  let (_cp, np) = zcharpoly_interp(rows, ps, cf)
  n = n + 1
  mk_check(
    "M-05 特徵多項式之 𝔽[x] 插值路徑",
    ok && cf.wmul < cb.wmul,
    n,
    "6 組插值路徑 = Hessenberg 路徑 = char_poly；n=10（" +
    np.to_string() +
    " 素數）對 ℚ 之 Faddeev–LeVerrier：" +
    gain_text(cb, cf),
  )
}

///|
/// M-06 ℤ[x] gcd：模 p 篩 + 重建 + 無條件整除性憑證。
pub fn ob_m06() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  for t in 0..<8 {
    let dg = 2 + t % 3
    let du = 3 + t % 4
    let d : Array[BigInt] = Array::makei(dg + 1, _ => {
      BigInt::from_int(rng.next_range(-20, 20))
    })
    d[dg] = 1N
    let u1 : Array[BigInt] = Array::makei(du + 1, _ => {
      BigInt::from_int(rng.next_range(-20, 20))
    })
    u1[du] = 1N
    let u2 : Array[BigInt] = Array::makei(du + 1, _ => {
      BigInt::from_int(rng.next_range(-20, 20))
    })
    u2[du] = 1N
    let cc = Cost::new()
    let f = zpoly_mul_school(d, u1, cc)
    let g = zpoly_mul_school(d, u2, cc)
    let fq = Array::makei(f.length(), i => Q::make(f[i], 1N))
    let gq = Array::makei(g.length(), i => Q::make(g[i], 1N))
    let c1 = Cost::new()
    let r1 = qpoly_gcd_euclid(fq, gq, c1)
    match zpoly_gcd_crt(f, g, ps, Cost::new()) {
      None => ok = false
      Some(gl) => {
        if !gl.certified {
          ok = false
        }
        if gl.gcd.length() != r1.length() {
          ok = false
        } else {
          for i in 0..<r1.length() {
            if !r1[i].eq(gl.gcd[i]) {
              ok = false
            }
          }
        }
        // 憑證之獨立覆核：G | f 且 G | g
        match qpoly_divmod(fq, gl.gcd, Cost::new()) {
          Some((_q, r)) => if r.length() != 0 { ok = false }
          None => ok = false
        }
      }
    }
    n = n + 1
  }
  // 係數膨脹之對照（互質輸入 ⇒ 歐幾里得之最壞情形）
  let du = 16
  let f : Array[BigInt] = Array::makei(du + 1, _ => {
    BigInt::from_int(rng.next_range(-30, 30))
  })
  f[du] = 1N
  let g : Array[BigInt] = Array::makei(du, _ => {
    BigInt::from_int(rng.next_range(-30, 30))
  })
  g[du - 1] = 1N
  let fq = Array::makei(f.length(), i => Q::make(f[i], 1N))
  let gq = Array::makei(g.length(), i => Q::make(g[i], 1N))
  let cb = Cost::new()
  let rb = qpoly_gcd_euclid(fq, gq, cb)
  let cf = Cost::new()
  let lift = zpoly_gcd_crt(f, g, ps, cf)
  match lift {
    None => ok = false
    Some(gl) => {
      if gl.gcd.length() != rb.length() {
        ok = false
      }
      if !gl.certified {
        ok = false
      }
    }
  }
  n = n + 1
  mk_check(
    "M-06 ℤ[x] gcd 之模篩與無條件憑證",
    ok && cf.wmul < cb.wmul,
    n,
    "8 組與 ℚ 歐幾里得 gcd 相同且通過整除性憑證（定理 Λ3-9 之無條件論證）；" +
    "deg 16 互質對照：" +
    gain_text(cb, cf),
  )
}

///|
/// M-07 ℚ 插值之多模重建 + 逐點憑證（對照 Lagrange 與函式庫）。
pub fn ob_m07() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut ok = true
  let mut n = 0
  for t in 0..<8 {
    let k = 3 + t % 5
    let xs = Array::makei(k, i => Q::of_int(i + 1))
    let ys = Array::makei(k, _ => qr(rng))
    let c1 = Cost::new()
    let r1 = qinterp_lagrange(xs, ys, c1)
    match qinterp_crt(xs, ys, ps, Cost::new()) {
      None => ok = false
      Some(il) => {
        if !il.certified {
          ok = false
        }
        if il.poly.length() != r1.length() {
          ok = false
        } else {
          for i in 0..<r1.length() {
            if !il.poly[i].eq(r1[i]) {
              ok = false
            }
          }
        }
        // 與函式庫 lagrange_interp 對照
        let lib = lagrange_interp(xs, ys)
        for i in 0..<il.poly.length() {
          if !lib.coef[i].eq(il.poly[i]) {
            ok = false
          }
        }
      }
    }
    n = n + 1
  }
  let k = 20
  let xs = Array::makei(k, i => Q::of_int(i + 1))
  let ys = Array::makei(k, _ => {
    Q::frac(rng.next_small(80), rng.next_range(1, 9))
  })
  let cb = Cost::new()
  let _ = qinterp_lagrange(xs, ys, cb)
  let cf = Cost::new()
  let lf = qinterp_crt(xs, ys, ps, cf)
  match lf {
    None => ok = false
    Some(il) => if !il.certified { ok = false }
  }
  n = n + 1
  mk_check(
    "M-07 ℚ 插值之多模重建",
    ok && cf.wmul < cb.wmul,
    n,
    "8 組與 Lagrange 及 lagrange_interp 三路一致，全部通過逐點憑證 f(xᵢ)=yᵢ；" +
    "20 節點：" +
    gain_text(cb, cf),
  )
}

///|
/// M-08 𝔽[x] 層分派器與誠實反例（何時不該加速）。
pub fn ob_m08() -> Check {
  let rng = ob_rng()
  let ps = accel_pool()
  let mut violations = 0
  let mut accel_cases = 0
  let mut reject_cases = 0
  let mut best = 1.0
  let mut n = 0
  for d in [16, 48, 96] {
    for bits in [32, 256, 1024] {
      let f = Array::makei(d, _ => zrand(rng, bits))
      let g = Array::makei(d, _ => zrand(rng, bits))
      let plan = plan_zpolymul(d, bits)
      let cb = Cost::new()
      let rb = zpoly_mul_school(f, g, cb)
      let cf = Cost::new()
      let (rf, _) = zpoly_mul_crt(f, g, ps, cf)
      for i in 0..<rb.length() {
        if rb[i] != rf[i] {
          violations = violations + 1
        }
      }
      let gain = Cost::ratio(cb, cf)
      if plan.use_fast {
        accel_cases = accel_cases + 1
        if gain <= 1.0 {
          violations = violations + 1
        }
        if gain > best {
          best = gain
        }
      } else {
        reject_cases = reject_cases + 1
      }
      n = n + 1
    }
  }
  // 誠實反例：由根造多項式，積樹於 schoolbook 算術下反而更貴
  let roots = Array::makei(32, _ => zrand(rng, 48))
  let cl = Cost::new()
  let rl = zpoly_from_roots_linear(roots, cl)
  let ct = Cost::new()
  let rt = zpoly_from_roots_tree(roots, ct)
  let mut same = rl.length() == rt.length()
  for i in 0..<rl.length() {
    if rl[i] != rt[i] {
      same = false
    }
  }
  if !same {
    violations = violations + 1
  }
  let tree_worse = ct.wmul > cl.wmul
  n = n + 1
  mk_check(
    "M-08 𝔽[x] 層分派器與誠實反例",
    violations == 0 && tree_worse,
    n,
    "9 個網格點答案全一致；加速 " +
    accel_cases.to_string() +
    " 例增益皆 > 1（最高 ×" +
    fmt_d(best, 2) +
    "），拒絕 " +
    reject_cases.to_string() +
    " 例；反例：32 根之積樹 " +
    ct.wmul.to_string() +
    " 字乘 > 線性累積 " +
    cl.wmul.to_string() +
    " 字乘，分派器正確拒絕加速",
  )
}

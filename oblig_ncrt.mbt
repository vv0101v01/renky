///|
/// N-43 之義務：結構律 × CRT 加速層之 2 × 2 析因量測。
///
/// 本義務刻意包含一條**對本庫第四輪計劃書之預測的推翻**（命題 191-4）。
pub fn ob_n43() -> Check {
  let rng = ob_rng()
  let mut ok = true

  // ── ⊗ 族：子問題維度皆 < 5 ────────────────────────────────
  let kron : Array[(FourPath, Int)] = [
    (fourpath_det(rng, 2, 3, 8), 3),
    (fourpath_det(rng, 3, 3, 8), 3),
    (fourpath_det(rng, 3, 4, 8), 4),
    (fourpath_inv(rng, 2, 3, 8), 3),
    (fourpath_inv(rng, 3, 3, 8), 3),
  ]
  // ── Λᵏ 族：子問題維度 = n ≥ 5 ─────────────────────────────
  let lam : Array[(FourPath, Int)] = [
    (fourpath_compound(rng, 5, 2, 8), 5),
    (fourpath_compound(rng, 6, 3, 8), 6),
  ]
  let all : Array[(FourPath, Int)] = []
  for x in kron {
    all.push(x)
  }
  for x in lam {
    all.push(x)
  }

  // 定理 191-1（四路徑一致 + 析因恆等式）
  // 一致性取精確相等而非容差 —— 本軌為精確 ℚ，容不得「幾乎相等」。
  for pr in all {
    let (r, _) = pr
    if !r.agree || !r.identity_ok() {
      ok = false
    }
  }

  // 定理 191-2（結構律恆壓倒 CRT）
  // 每一案例中，結構律之增益必須大於 CRT 之增益 —— 這是「永遠先分解」的根據。
  for pr in all {
    let (r, _) = pr
    if r.g_law_exact() <= r.g_crt_mono() {
      ok = false
    }
  }

  // 命題 191-3（加速不可乘：δ 顯著偏離 1）
  // 以 inv 族為代表 —— 其 CRT 在單體問題上確實獲益（G_crt^mono > 1），
  // 分解後卻轉為虧損，排擠效應最強。
  let inv33 = kron[4].0
  if inv33.g_crt_mono() <= 1.0 || inv33.g_crt_dec() >= 1.0 {
    ok = false
  }
  if inv33.defect() >= 0.7 {
    ok = false
  }

  // 命題 191-4（計劃書之預測被推翻）
  // 第四輪計劃書預期路徑 (d)（先分解、每塊 CRT）最快。⊗ 族全部 5 例皆非如此：
  // 最快的是 (b)（先分解、精確 ℚ）。
  let mut kron_b = 0
  for pr in kron {
    let (r, _) = pr
    if r.best() == "b" {
      kron_b = kron_b + 1
    }
  }
  if kron_b != 5 {
    ok = false
  }
  // 而 Λᵏ 族 2 例確實是 (d) 最快 —— 故這不是「(d) 永遠輸」，是有條件的反轉。
  let mut lam_d = 0
  for pr in lam {
    let (r, _) = pr
    if r.best() == "d" {
      lam_d = lam_d + 1
    }
  }
  if lam_d != 2 {
    ok = false
  }

  // 定理 191-5（決策規則之正確性）
  // pick_path 僅看「分解後子問題維度」一個數，必須重現全部 7 例之實測最佳路徑。
  let mut rule_hit = 0
  for pr in all {
    let (r, dsub) = pr
    if pick_path(dsub) == r.best() {
      rule_hit = rule_hit + 1
    }
  }
  if rule_hit != all.length() {
    ok = false
  }

  // 定理 191-6（機制：結構已壓住係數膨脹，CRT 無餅可搶）
  // 同維度 12、同元素位寬下比較 A⊗B 與一般稠密矩陣。
  let primes = prime_pool(48)
  let a = rand_zmat_dense(rng, 3, 8)
  let b = rand_zmat_dense(rng, 4, 8)
  let ck = Cost::new()
  let kab = qkron_cost(ck, a, b)
  let ck1 = Cost::new()
  let _ = qdet_gauss(kab, ck1)
  let ck2 = Cost::new()
  let _ = zdet_crt(qmat_to_zrows(kab), primes, ck2)
  let gen = rand_zmat_dense(rng, 12, 16)
  let cg1 = Cost::new()
  let _ = qdet_gauss(gen, cg1)
  let cg2 = Cost::new()
  let _ = zdet_crt(qmat_to_zrows(gen), primes, cg2)
  let kron_bits = ck1.maxbits
  let gen_bits = cg1.maxbits
  let kron_crt = fp_ratio(ck1.wmul, ck2.wmul)
  let gen_crt = fp_ratio(cg1.wmul, cg2.wmul)
  // (i) 同維同位寬，Kronecker 之中間係數顯著較短
  if kron_bits * 2 >= gen_bits * 3 {
    ok = false
  }
  // (ii) 精確 ℚ 消去成本相差一個量級以上
  if ck1.wmul * 10L >= cg1.wmul {
    ok = false
  }
  // (iii) 且 CRT 增益隨之塌陷：Kronecker 上幾乎無利，一般稠密上大賺
  if kron_crt >= 2.0 || gen_crt <= 10.0 {
    ok = false
  }
  let mut detail = "四路徑精確一致且析因恆等式成立；"
  for pr in all {
    let (r, _) = pr
    detail = detail +
      r.tname +
      r.tdims +
      " δ=" +
      fmt_d(r.defect(), 2) +
      "/最佳(" +
      r.best() +
      ") "
  }
  detail = detail +
    "｜決策規則 " +
    rule_hit.to_string() +
    "/" +
    all.length().to_string() +
    " 正確；機制：dim12 同位寬下 A⊗B 之 ℚ 消去 " +
    ck1.wmul.to_string() +
    " wmul／中間 " +
    kron_bits.to_string() +
    " 位元／CRT ×" +
    fmt_d(kron_crt, 2) +
    "，一般稠密 " +
    cg1.wmul.to_string() +
    " wmul／" +
    gen_bits.to_string() +
    " 位元／CRT ×" +
    fmt_d(gen_crt, 2)
  mk_check(
    "N-43 結構律 × CRT 之 2×2 析因",
    ok,
    all.length() * 4 + 10,
    detail,
  )
}

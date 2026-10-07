///|
/// N-56 之義務：兩條反例的主張，第一次變成可執行的。
pub fn ob_n56() -> Check {
  let mut ok = true

  // ── 反例網格 ────────────────────────────────────────────
  let (tot, cok, g5, g8, win) = acc_scan_counter()
  if tot != 8 || cok != 8 {
    ok = false
  }
  // 八格全輸 —— 這才是「反例」該有的樣子
  if win != 0 {
    ok = false
  }
  if !(g5 > 0.070 && g5 < 0.080) {
    ok = false
  }
  if !(g8 > 0.740 && g8 < 0.750) {
    ok = false
  }

  // ── 逐格：ν 與 k 必須如實記錄 ───────────────────────────
  let cells : Array[AccCell] = []
  for s in acc_grid_small() {
    cells.push(acc_cell_l05(s.0, s.1))
    cells.push(acc_cell_l08(s.0, s.1))
  }
  if cells.length() != 8 {
    ok = false
  }
  let nus = [18, 12, 50, 30, 18, 12, 50, 30]
  for i in 0..<8 {
    if cells[i].acnu != nus[i] {
      ok = false
    }
    if !cells[i].acok {
      ok = false
    }
    if cells[i].gain() >= 1.0 {
      ok = false
    }
  }

  // ── 失敗的嘗試：先驗 Hadamard 界反而更慢 ────────────────
  let (s1, a1, same1) = acc_apriori_cell(3, 8)
  let (s2, a2, same2) = acc_apriori_cell(5, 16)
  if !(same1 && same2) {
    ok = false
  }
  // 兩格都是「新版比舊版貴」——這條反面證據是本條的重點之一
  if !(a1 > s1 && a2 > s2) {
    ok = false
  }
  if s1 != 10304L || a1 != 13801L {
    ok = false
  }
  if s2 != 2581501L || a2 != 3333061L {
    ok = false
  }

  // ── ν 是主因子之直接證據 ────────────────────────────────
  let (nu1, nu2, f1, f2, ratio) = acc_nu_evidence(5, 16)
  if nu1 != 30 || nu2 != 5 {
    ok = false
  }
  if f1 != 2581501L || f2 != 90590L {
    ok = false
  }
  if !(ratio > 28.0 && ratio < 29.0) {
    ok = false
  }
  mk_check(
    "N-56 加速層反例之全網格量測與診斷",
    ok,
    tot * 4 + 12,
    "L-05 與 L-08 在目錄裡寫著「實測 ×0.15」「實測 ×0.6」，但翻開 ob_l05 與 ob_l08 會發現：它們只驗了正確性，從來沒有量過那兩個比值。那兩個數字是離線量一次寫進目錄的，沒有任何可執行的東西盯著它 —— 一條以負面結果為主張的條目，它的主張不在義務裡。本條先把這個洞補起來：新寫受 Cost 計量的基準路徑 qrref_gauss 與 qldlt_gauss（ℚ 上的 Gauss–Jordan 與無開方 Cholesky，逐次有理運算計費，含 gcd 約分），於是兩條反例的比值變成每次 moon test 都重量一遍的數字。小網格 " +
    tot.to_string() +
    " 格（n ∈ {3,5} × 位元 ∈ {8,16}）全部兩路一致（" +
    cok.to_string() +
    "/8，含憑證），且 " +
    win.to_string() +
    " 格勝出 —— 八格全輸。L-05 最好的一格只有 ×" +
    fmt_d(g5, 4) +
    "，L-08 最好的一格 ×" +
    fmt_d(g8, 4) +
    "。更大的網格（見 cmd/accel）顯示 L-05 的比值隨位元下降而非上升（0.15 → 0.046），L-08 的比值先升後降（0.15 → 0.81 → 0.65），兩者都不存在會翻盤的區域。這比原目錄的單點數字強得多：原來說的是「我在某處量到 ×0.15」，現在說的是「整片都輸，而且輸的方式有形狀」。**診斷。** 多模路徑的字乘法花在三處：k 趟模消去 Θ(k·n³)、CRT 累積 Θ(ν·k²)、事後憑證 Θ(n³·w²)；其中 ν 是「要重建幾個輸出」。L-05 要重建 2n² 個有理數、L-08 要 n²+n 個，而贏得最漂亮的 K-04（ℤ 行列式）只要重建 **1** 個。**一條失敗的嘗試（本條刻意保留）。** 既然 CRT 累積是 Θ(ν·k²)，直覺是去砍 k：把「逐素數穩定判定」換成「先驗 Hadamard 界、吃滿一次重建」。實測反而更慢 —— n=3/8 位元 " +
    s1.to_string() +
    " → " +
    a1.to_string() +
    "，n=5/16 位元 " +
    s2.to_string() +
    " → " +
    a2.to_string() +
    "（兩版輸出逐位相同）。Hadamard 界是悲觀的，它要的素數比穩定判定實際用掉的多兩三成，而主成本對 k 是平方的。這條反面證據留在庫裡（qldlt_crt_ap），因為它正是「換 k 沒用」的證明。**ν 才是那個因子。** 同一個問題（n=5、16 位元）、同一組素數，只把要重建的東西從 n²+n = " +
    nu1.to_string() +
    " 個有理數改成 n = " +
    nu2.to_string() +
    " 個整數，加速路徑的字乘法由 " +
    f1.to_string() +
    " 降到 " +
    f2.to_string() +
    "，×" +
    fmt_d(ratio, 2) +
    "。由此導出第七輪的重構原則：**加速層的單位不該是「整個矩陣」，而該是「呼叫端真正要的那個量」。** N-57 與 N-58 照這條原則各改寫一條反例。",
  )
}

///|
/// N-57 之義務：L-08′ —— 只重建 n 個整數前導主子式。
pub fn ob_n57() -> Check {
  let mut ok = true
  let cells = [
    acc_cell_l08p(3, 8),
    acc_cell_l08p(5, 8),
    acc_cell_l08p(5, 16),
    acc_cell_l08p(7, 16),
  ]
  // 全部正確：D 逐項等於 qldlt_gauss 之 D，∏D = det G，Sylvester 判定正定
  for c in cells {
    if !c.acok {
      ok = false
    }
    if c.acnu != c.acn {
      ok = false
    }
    if c.gain() <= 1.0 {
      ok = false
    }
  }
  if cells[0].acbase != 4636L || cells[0].acfast != 2321L {
    ok = false
  }
  if cells[1].acbase != 97561L || cells[1].acfast != 15335L {
    ok = false
  }
  if cells[2].acbase != 1922344L || cells[2].acfast != 90590L {
    ok = false
  }
  if cells[3].acbase != 31307296L || cells[3].acfast != 701582L {
    ok = false
  }
  // 增益隨 n 單調上升 —— 這是「ν 砍掉一個 n 因子」的指紋
  let gs = [cells[0].gain(), cells[1].gain(), cells[2].gain(), cells[3].gain()]
  if !(gs[0] < gs[1] && gs[1] < gs[2] && gs[2] < gs[3]) {
    ok = false
  }
  if !(gs[0] > 1.9 && gs[0] < 2.1) {
    ok = false
  }
  if !(gs[3] > 44.0 && gs[3] < 45.0) {
    ok = false
  }

  // ── 雙向對照：非正定之 Gram 必須被 Sylvester 判出來 ─────
  let rng = ob_rng()
  let bad = Mat::build(3, 3, (i, j) => {
    if i == j {
      if i == 1 {
        Q::of_int(-1)
      } else {
        Q::of_int(1)
      }
    } else {
      Q::zero()
    }
  })
  let _ = rng
  let spd_detected = match qldlt_minors_crt(bad, acc_pool(), Cost::new()) {
    Some(w) => !w.qmspd && w.qmdet.eq(Q::of_int(-1))
    None => false
  }
  if !spd_detected {
    ok = false
  }
  mk_check(
    "N-57 L-08′ 前導主子式之整數 CRT",
    ok,
    cells.length() * 6 + 4,
    "依 N-56 的重構原則改寫 L-08：呼叫端要 LDLᵀ，幾乎都不是為了 L 的那 n² 個有理數，而是為了 D（= Gram–Schmidt 的 ‖qⱼ‖²）、det G、以及「正不正定」。這三樣全部由前導主子式決定，而前導主子式是**整數**。算式：設 Gz = dd·G 為清分母後之整數 Gram，Δⱼ 為其 j 階前導主子式，則 𝔽p 上一次無開方 Cholesky 給出 Dⱼ⁽ᵖ⁾ 且 Δⱼ ≡ ∏_{i≤j} Dᵢ⁽ᵖ⁾ (mod p) —— **一趟模消去同時給出全部 n 個前導主子式**。再由 Dⱼ(G) = Δⱼ(Gz)/(dd·Δⱼ₋₁(Gz))、det G = Δₙ(Gz)/ddⁿ、以及 Sylvester 判準「全部 Δⱼ > 0 ⟺ 正定」還原三樣輸出。ν 由 n²+n 降到 n。**為什麼不需要事後憑證。** Δⱼ 是整數，|Δⱼ| 受 Hadamard 界控制，取 ∏p > 2H 時對稱提升**無條件**等於 Δⱼ —— 這與 K-04（ℤ 行列式，加速層贏最漂亮的條目之一）用的是同一條定理。有理重建才需要「猜對了沒」的事後檢查，整數 CRT 不需要。實測（基準為受計量的 qldlt_gauss，兩路 D 逐項相同、∏D = det G 精確相等）：n=3/8 位元 " +
    cells[0].acbase.to_string() +
    " → " +
    cells[0].acfast.to_string() +
    "（×" +
    fmt_d(gs[0], 2) +
    "）、n=5/8 位元 ×" +
    fmt_d(gs[1], 2) +
    "、n=5/16 位元 ×" +
    fmt_d(gs[2], 2) +
    "、n=7/16 位元 ×" +
    fmt_d(gs[3], 2) +
    "。義務要求增益**隨 n 單調上升** —— 這是「ν 砍掉一個 n 因子」留下的指紋，若只是常數倍的實作改良，增益會持平而不會爬升。更大的網格上 n=11/16 位元達 ×107.6（見 cmd/accel）。**雙向對照。** 只驗「算得快又對」分不出「Sylvester 判準真的在判」與「它永遠回答正定」。義務另餵一個非正定的 diag(1,−1,1)：必須判為非正定，且 det 必須精確等於 −1。原 L-08 的結論（「永不獲利，比值收斂於約 0.6」）對**那個輸出**仍然成立；本條換的是輸出，不是區域。",
  )
}

///|
/// N-58 之義務：L-05′ —— 秩與樞軸之模篩 + 夾擠憑證。
pub fn ob_n58() -> Check {
  let mut ok = true
  let a1 = acc_cell_l05p(5, 8)
  let a2 = acc_cell_l05p(7, 16)
  let a3 = acc_cell_l05p(9, 16)
  for c in [a1, a2, a3] {
    if !c.acok {
      ok = false
    }
    if c.gain() <= 1.0 {
      ok = false
    }
  }
  if a1.acbase != 10271L || a1.acfast != 8016L {
    ok = false
  }
  if a2.acbase != 2141754L || a2.acfast != 143096L {
    ok = false
  }
  if a3.acbase != 18985331L || a3.acfast != 529149L {
    ok = false
  }
  let g1 = a1.gain()
  let g3 = a3.gain()
  if !(g1 > 1.2 && g1 < 1.4) {
    ok = false
  }
  if !(g3 > 35.0 && g3 < 37.0) {
    ok = false
  }

  // ── 誠實邊界：秩虧長方形時上界憑證不再免費 ──────────────
  let d1 = acc_cell_l05p_def(8, 5, 16)
  if !d1.acok {
    ok = false
  }
  let gd = d1.gain()
  if !(gd > 1.0 && gd < 1.2) {
    ok = false
  }
  if d1.acbase != 14388878L || d1.acfast != 13307818L {
    ok = false
  }

  // ── 雙向對照：秩虧矩陣之秩必須被正確判出（不是固定回 n）─
  let rng = ob_rng()
  let b1 = qmat_bitwidth(rng, 6, 3, 8)
  let b2 = qmat_bitwidth(rng, 3, 6, 8)
  let aa = b1.times(b2)
  let rc = qrank_modp(aa, acc_pool(), 3, Cost::new())
  if rc.rcrank != 3 || !rc.rclow || !rc.rcup {
    ok = false
  }
  if rc.rcrank != mrank(aa) {
    ok = false
  }
  mk_check(
    "N-58 L-05′ 秩與樞軸之模篩與夾擠憑證",
    ok,
    24,
    "依同一條原則改寫 L-05。RREF 的輸出是 2n² 個有理數，ν 擺在那裡，換重建策略只能把 k³ 降成 k²，省不掉 ν —— 所以 L-05 不能靠「修重建」救，只能靠「換輸出」。呼叫端要 RREF，絕大多數時候要的是「秩是多少、樞軸在哪」。這兩樣可以完全不重建：模 p 消去直接給出樞軸型態，而壞素數只會使秩變小，故數個素數中的最大秩即真秩之候選。**無條件正確性怎麼來（不靠機率）。** 輸出候選樞軸行 S（|S| = r）與樞軸列 R，再用兩條精確憑證夾擠：下界 det A[R,S] ≠ 0 ⇒ rank ≥ r，以 zdet_crt 計算（整數、ν = 1、Hadamard 先驗界 —— 正是 K-04 的結構）；上界在 r = min(m,n) 時自動成立（秩不可能超過 min(m,n)），否則逐個非樞軸行驗它落在 S 的張成裡（共用一次 r 階精確求逆）。兩條合起來是 rank = r 的無條件證明。實測（基準為受計量的 qrref_gauss）：n=5/8 位元 " +
    a1.acbase.to_string() +
    " → " +
    a1.acfast.to_string() +
    "（×" +
    fmt_d(g1, 2) +
    "）、n=7/16 位元 ×" +
    fmt_d(a2.gain(), 2) +
    "、n=9/16 位元 ×" +
    fmt_d(g3, 2) +
    "；更大的網格上 n=9/32 位元達 ×81.9。**誠實邊界（本條最該被記住的一行）。** 上面全是方陣滿秩，上界憑證免費。換成秩虧的長方形（8×8、秩 5、16 位元），上界憑證要做一次 5 階精確求逆加 3 個非樞軸行的張成驗證，增益掉到 ×" +
    fmt_d(gd, 2) +
    "（" +
    d1.acbase.to_string() +
    " → " +
    d1.acfast.to_string() +
    "）。也就是說：這條重構救得了「秩滿不滿」，救不了「秩虧多少」—— 後者的上界憑證本身就幾乎是一次完整的 ℚ 消去。**雙向對照。** 只驗「方陣回答 n」分不出「真的在算秩」與「永遠回答行數」。義務另餵一個 6×6、秩 3 的乘積矩陣：秩必須判為 3，兩條憑證都要通過，且與 mrank 相符。",
  )
}

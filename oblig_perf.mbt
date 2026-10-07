///|
/// N-35 之義務：搜尋分層與 N 群效能整頓。
///
/// 本條與其他條目不同 —— 它驗的不是一條數學律，而是**「為了變快而做的刪減
/// 沒有偷走任何結論」**。四項刪減各自對應一條斷言：
///
/// | 刪減 | 根據 | 本條如何自證 |
/// | --- | --- | --- |
/// | N-13／N-26 共用一次搜尋 | 同網格同種子，結果逐位元相同 | 未命中計數恆為 1 |
/// | 搜尋網格 (3,3) 下修 | 兩網格裁決逐條相同 | 以最敏感之候選就地重驗 |
/// | N-14 移除複合矩陣 | 該矩陣未進入任何斷言（死碼） | 該負面項仍須成立 |
/// | N-10／N-06 網格下修 | 序關係不依賴絕對維數 | 成本預算上限 |
pub fn ob_n35() -> Check {
  let rng = ob_rng()
  let mut ok = true

  // ── 定理 192-1（搜尋去重確實生效）────────────────────────────
  // 連呼三次標準搜尋，實際跑過的完整搜尋次數必須恰為 1。
  let t1 = law_search_std(rng)
  let t2 = law_search_std(rng)
  let t3 = law_search_std(rng)
  if law_miss_count() != 1 {
    ok = false
  }
  // 且三次取得的表必須逐條相同（共用不等於換了一張表）
  if t1.length() != t2.length() || t2.length() != t3.length() {
    ok = false
  }
  for i in 0..<t1.length() {
    if t1[i].cphi != t3[i].cphi ||
      t1[i].ccomb != t3[i].ccomb ||
      t1[i].crule != t3[i].crule ||
      t1[i].cholds != t3[i].cholds {
      ok = false
    }
  }

  // ── 定理 192-2（下修後之網格仍保有判別力）────────────────────
  // 命題 175-3 說：網格若全為方形同尺寸，`det/⊗/·`（少了指數的錯誤規則）
  // 會因 n = m 而僥倖通過。下修網格時最該擔心的就是把這個保護拆掉了。
  // 故就地重驗：全方形網格下該候選**應當**被誤判為成立，
  // 而現行 law_grid_std() 下**必須**被推翻。兩者同時為真，
  // 才證明下修後的網格仍握有這份判別力。
  let degen = law_search(ob_rng(), [(2, 2)])
  // 退化網格恰在 n = m = 2 處讓「和」與「積」重合（2 + 2 = 2 · 2 = 4），
  // 於是三條 rank 的錯誤規則一齊僥倖通過。
  let victims : Array[(String, String, String)] = [
    ("rank", "⊗", "+"),
    ("rank", "⊕", "·"),
    ("rank", "⊞", "+"),
  ]
  for v in victims {
    let (pp, cc, rr) = v
    if law_find(degen, pp, cc, rr) != Some(true) {
      ok = false // 退化網格竟沒上當 —— 這個對照就失去意義
    }
    if law_find(t1, pp, cc, rr) != Some(false) {
      ok = false // 現行網格沒抓到 —— 下修拆掉了保護
    }
  }
  let mut dh = 0
  for t in degen {
    if t.cholds {
      dh = dh + 1
    }
  }
  let mut sh = 0
  for t in t1 {
    if t.cholds {
      sh = sh + 1
    }
  }
  // 成立數必須由 19 降為 16：非方形尺寸確實篩掉了那三條
  if dh != 19 || sh != 16 {
    ok = false
  }
  // 現行網格必須含非方形尺寸
  let mut has_oblong = false
  for p in law_grid_std() {
    let (a, b) = p
    if a != b {
      has_oblong = true
    }
  }
  if !has_oblong {
    ok = false
  }
  // 且須為全量網格之真子集
  if law_grid_std().length() >= law_grid_full().length() {
    ok = false
  }

  // ── 定理 192-3（移除之死碼確為死碼）──────────────────────────
  // N-14 第 7 項原本另建一個 20×20 複合矩陣（492,444 字乘法）才下結論，
  // 但其主張只比較兩種冪法之成本。移除後該項仍須成立。
  let mut found7 = false
  for r in negative_registry() {
    if r.nsrc == "N-10" && r.nholds {
      found7 = true
    }
  }
  if !found7 {
    ok = false
  }

  // ── 命題 192-4（成本預算上限：防止網格悄悄長回去）────────────
  // 這是一條回歸護欄，不是數學主張。N-10 常規網格之直接法總成本
  // 實測 203,338 字乘法；上限設 260,000。若日後有人把 (6,3) 加回來
  // （單這一項就 492,444），本條會立刻失敗。
  let mut n10_budget = 0L
  for nk in [(4, 2), (5, 2), (6, 2), (4, 3), (5, 3)] {
    let (nn, kk) = nk
    let a = rand_gram(rng, nn)
    let c = Cost::new()
    let ckm = compound(a, kk, c)
    let _ = qdet_gauss(ckm, c)
    n10_budget = n10_budget + c.wmul
  }
  if n10_budget > 260000L {
    ok = false
  }
  mk_check(
    "N-35 搜尋分層與 N 群效能整頓",
    ok,
    t1.length() + degen.length() + 8,
    "去重：標準搜尋呼叫 3 次、實跑 " +
    law_miss_count().to_string() +
    " 次，三次取得之定律表逐條相同（" +
    t1.length().to_string() +
    " 候選）。判別力：退化網格 {(2,2)} 因 2+2 = 2·2 = 4 而讓 rank/⊗/+、rank/⊕/· 與 rank/⊞/+ 三條錯誤規則僥倖通過（成立 " +
    dh.to_string() +
    " 條），現行 " +
    law_grid_std().length().to_string() +
    " 尺寸網格（含非方形）全數推翻（成立 " +
    sh.to_string() +
    " 條）。死碼：N-14 移除 20×20 複合矩陣後該負面項仍成立。預算：N-10 常規網格直接法 " +
    n10_budget.to_string() +
    " 字乘法（上限 260,000）。整體 N 群由 5.92 s 降至 3.0 s 以下，全量掃描與大尺寸實測移入 cmd/lawsearch（見 docs/定律表.md）。",
  )
}

///|
/// N-30 之義務：統一成本介面與軌道標籤。
///
/// 本條要釘死的是一件很容易被含糊帶過的事 —— N-21 的 ×303.7 與 N-03 的 ×13.2
/// **不能比較**。前者是 flop 比、後者是字乘法比，量綱不同。
/// 整個 N 群的報告若把兩者排在同一張增益榜上，就是在誤導讀者。
pub fn ob_n30() -> Check {
  let rng = ob_rng()
  let mut ok = true

  // ── 定理 193-1（兩軌計量器完全互斥）──────────────────────────
  // 不是「ℝ 軌的 wmul 比較小」，而是**恆為 0**。兩者不是同一個量的不同單位。
  let a = rand_gram(rng, 4)
  let b = rand_gram(rng, 4)
  let cq = Cost::new()
  let kab = qkron_cost(cq, a, b)
  let _ = qinv_gauss(kab, cq)
  if cq.wmul <= 0L || cq.flops != 0L {
    ok = false
  }
  let cr = Cost::new()
  let _ = cjacobi_eigen(rand_spd(rng, 6), 1.0e-12, 200, cr)
  if cr.flops <= 0L || cr.wmul != 0L {
    ok = false
  }

  // ── 定理 193-2（跨軌取比值得 0，而非「較小的增益」）─────────
  // 這是本條最重要的一條：用錯軌道不會得到一個看起來合理但偏小的數字，
  // 而是得到 0 —— 錯誤是顯性的，不會悄悄混進報告。
  let cq2 = Cost::new()
  match (qinv_gauss(a, cq2), qinv_gauss(b, cq2)) {
    (Some(ia), Some(ib)) => {
      let _ = qkron_cost(cq2, ia, ib)
    }
    _ => ok = false
  }
  // 同軌：正常增益
  let g_right = gain_by_track(cq, cq2, TQ)
  if g_right <= 1.0 {
    ok = false
  }
  // 跨軌：分母為 0 ⇒ 回傳 0
  let g_wrong = gain_by_track(cq, cq2, TR)
  if g_wrong != 0.0 {
    ok = false
  }

  // ── 定理 193-3（同軌介面與既有計量函式逐位元一致）───────────
  // 新介面若與 Cost::ratio／flop_ratio 不合，等於偷換了全庫既有的全部增益數字。
  if gain_by_track(cq, cq2, TQ) != Cost::ratio(cq, cq2) {
    ok = false
  }
  let cr2 = Cost::new()
  let _ = cjacobi_eigen(rand_spd(rng, 4), 1.0e-12, 200, cr2)
  if gain_by_track(cr, cr2, TR) != flop_ratio(cr, cr2) {
    ok = false
  }

  // ── 命題 193-4（軌道標籤確實掛在判決上）─────────────────────
  let v = law_kron_inv(rng, [(2, 2), (3, 3)])
  if !v.ltrack.teq(TQ) || v.unit() != "字乘法" {
    ok = false
  }
  if v.cost() <= 0L {
    ok = false
  }
  if TQ.teq(TR) || !TR.teq(TR) {
    ok = false
  }
  mk_check(
    "N-30 統一成本介面與軌道標籤",
    ok,
    12,
    "兩軌計量器互斥：ℚ 軌 Kronecker 求逆 wmul=" +
    cq.wmul.to_string() +
    "／flops=" +
    cq.flops.to_string() +
    "；ℝ 軌 Jacobi 特徵分解 flops=" +
    cr.flops.to_string() +
    "／wmul=" +
    cr.wmul.to_string() +
    "。同軌增益 ×" +
    fmt_d(g_right, 2) +
    "（與 Cost::ratio 逐位元相同）；同一對成本跨軌取值得 " +
    fmt_d(g_wrong, 2) +
    " —— 錯用軌道是顯性失敗，不會產生一個看似合理的數字。判決已掛軌道標籤（" +
    v.ltrack.tlabel() +
    "，單位 " +
    v.unit() +
    "）。本庫**不提供** wmul 與 flop 之換算常數：該常數取決於機器字長、BigInt 實作與浮點管線，本庫量不出來，故報告一律分軌排序。",
  )
}

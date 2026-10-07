///|
/// N-48 之義務：ℝ 軌進入複合器。
///
/// 本條把 N-42 的複合定理搬到 ℝ 軌，而搬運過程本身就是結論：
/// **ℚ 軌的判準照搬過來是不健全的**。ℚ 軌每個 Φ 都是 ℚ^{n×n} → ℚ^{n×n}，
/// Φ₂ 一定吃得下 Φ₁ 的輸出；ℝ 軌的 Φ 幾乎都只在 SPD 上有定義。
pub fn ob_n48() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let tbl = rlaw_search_std(rng)
  let dsyn = rcompose_derive(tbl, false)
  let ddom = rcompose_derive(tbl, true)
  let xs = rcompose_scan_std(rng)

  // ── 命題 206-0（推導規模）──────────────────────────────
  // ℝ 軌 13 條成立之律，純語法判準推出 44 條；加上定義域條件剩 33 條。
  let mut nhold = 0
  for t in tbl {
    if t.cholds {
      nhold = nhold + 1
    }
  }
  if nhold != 13 || dsyn.length() != 44 || ddom.length() != 33 {
    ok = false
  }
  if xs.length() != 44 {
    ok = false
  }

  // ── 定理 206-1（ℚ 軌的純語法判準在 ℝ 軌**不健全**）──────
  // N-42 於 ℚ 軌量到「導出但推翻 = 0」。同一判準搬到 ℝ 軌不再是 0。
  let (sa, sb, _sc, _sd) = rcompose_confusion_syn(xs)
  if sb != 3 {
    ok = false // 導出但推翻必須真的是 3，否則本條的主張不成立
  }
  if sa != 32 {
    ok = false
  }

  // ── 定理 206-2（量出來的前提檢查勝過人寫的保 SPD 表）────
  // 做法一（人寫）：要求內層保 SPD —— chol 輸出下三角，故被擋。
  // 做法二（量測）：逐樣本檢查 Φ₁ 的輸出是否滿足 Φ₂ 的前提（對稱性）。
  // 兩者各自的代價必須量出來，不能用講的。
  let mut invalid = 0
  let mut pre_bad = 0
  let mut ovf_bad = 0
  for x in xs {
    if !rcomp_valid(x) {
      invalid = invalid + 1
    }
    if x.ypre > 0 {
      pre_bad = pre_bad + 1
    }
    if x.yovf > 0 {
      ovf_bad = ovf_bad + 1
    }
  }
  if invalid != 9 {
    ok = false
  }
  // 人寫的表**過嚴**：它擋掉的 chol 內層中，有三條其實有效且成立。
  // 理由是 inv（偽逆）與 expm 本來就不要求對稱輸入。
  let overstrict : Array[String] = []
  for x in xs {
    if x.ysyn && !x.ydom && x.yholds && rcomp_valid(x) {
      overstrict.push(x.yname())
    }
  }
  if overstrict.length() != 3 {
    ok = false
  }
  // 人寫的表**不足**：它擋不住 expm 內層造成的三條失敗（見定理 206-3）。
  let (_da, db, _dc, _dd) = rcompose_confusion_dom(xs)
  if db != 3 {
    ok = false
  }
  // 而量測版把人寫表該抓的全抓到了：語法導出、定義域條件擋下、
  // 卻仍被判為有效且推翻者 —— 一條都沒有。
  for x in xs {
    if x.ysyn && !x.ydom && !x.yholds && rcomp_valid(x) {
      ok = false
    }
  }

  // ── 定理 206-3（三條失敗沒有一條是代數的）──────────────
  // 偏差的量級就是分類的依據，故三條都要點名並釘住量級。
  let d1 = match rcomp_find(xs, "inv∘expm/⊕/⊕") {
    Some(x) => x.ydev
    None => {
      ok = false
      0.0
    }
  }
  let d2 = match rcomp_find(xs, "chol∘expm/⊞/⊗") {
    Some(x) => x.ydev
    None => {
      ok = false
      0.0
    }
  }
  let d3 = match rcomp_find(xs, "det∘expm/⊞/^") {
    Some(x) => x.ydev
    None => {
      ok = false
      0.0
    }
  }
  // (1) 偽逆的奇異值截斷不可複合：整體與分塊看到的尺度不同，截斷點就不同
  if !(d1 > 1.0e-4 && d1 < 1.0) {
    ok = false
  }
  // (2) 只差一點點 —— 容差在此是承重的，不是形式
  if !(d2 > 1.0e-8 && d2 < 1.0e-7) {
    ok = false
  }
  // (3) 浮點動態範圍潰堤：det(expm(M)) = e^{tr M}，指數一大就沒有有效位數
  if !(d3 > 1.0e50) {
    ok = false
  }

  // ── 命題 206-4（容差此處是承重的，與 N-33 不同）────────
  // N-33 量到相對偏差 ≈ 1.4e-15，離門檻 1e-8 有七個數量級。
  // 複合之後最壞的成立者只剩 1.5e-9，而最接近的推翻者是 1.13e-8。
  let mut worst_hold = 0.0
  for x in xs {
    if x.yholds && rcomp_valid(x) && x.ydev > worst_hold {
      worst_hold = x.ydev
    }
  }
  if !(worst_hold > 1.0e-10 && worst_hold < 1.0e-8) {
    ok = false
  }
  let margin = 1.0e-8 / worst_hold

  // ── 命題 206-5（溢位必須記為未裁決，而非推翻）──────────
  // 並驗證 sqrt_newton 的無窮迴圈已補：此洞正是被本條逼出來的 ——
  // expm∘expm 把特徵值推到 e^(e^λ) 溢位成 +∞，餵給 sqrtm 後
  // `while v >= 4.0 { v = v / 4.0 }` 永不終止。
  let inf = 1.0 / 0.0
  let nan = 0.0 / 0.0
  if sqrt_newton(inf) != inf {
    ok = false
  }
  if sqrt_newton(nan) == sqrt_newton(nan) {
    ok = false // NaN 必須傳遞（NaN ≠ NaN）
  }
  if sqrt_newton(16.0) != 4.0 {
    ok = false // 有限輸入之行為不得改變
  }
  if ovf_bad < 1 {
    ok = false // 溢位必須真的發生過，否則上面那段是空話
  }

  // ── 命題 206-6（增益：ℝ 軌複合之數量級）────────────────
  let top = rcompose_top(xs, 3)
  let mut tops = ""
  for t in top {
    tops = tops + t.yname() + " ×" + fmt_d(t.ygain, 1) + "　"
  }
  if top.length() != 3 || top[0].ygain < 20.0 {
    ok = false
  }
  if rcomp_miss_count() != 1 {
    ok = false
  }
  mk_check(
    "N-48 ℝ 軌進入複合器",
    ok,
    xs.length() * rlaw_grid_std().length() + dsyn.length() + ddom.length() + 20,
    "把 N-42 的複合定理搬到 ℝ 軌，搬運過程本身就是結論。ℚ 軌每個 Φ 都是 ℚ^{n×n} → ℚ^{n×n}，Φ₂ 一定吃得下 Φ₁ 的輸出；ℝ 軌的 Φ 幾乎只在 SPD 上有定義（chol 要 SPD 且輸出下三角、sqrtm／eig 要對稱、det 走 Cholesky），故純語法判準不再充分。ℝ 軌 " +
    nhold.to_string() +
    " 條成立之律，語法判準推出 " +
    dsyn.length().to_string() +
    " 條，加定義域條件剩 " +
    ddom.length().to_string() +
    " 條。⚠️ 定理 206-1：同一判準在 ℚ 軌量到「導出但推翻 = 0」，在 ℝ 軌是 **" +
    sb.to_string() +
    "**（有效裁決中 " +
    sa.to_string() +
    " 條成立）—— 判準不健全。定理 206-2：人寫的「內層須保 SPD」表**既過嚴又不足** —— 過嚴之處是它擋掉 " +
    overstrict.length().to_string() +
    " 條其實有效且成立的律（inv∘chol/⊗/⊗、inv∘chol/⊕/⊕、expm∘chol/⊕/⊕；因偽逆與 expm 本來就不要求對稱輸入），不足之處是它擋不住 expm 內層的 3 條失敗。改以**逐樣本量測** Φ₁ 的輸出是否滿足 Φ₂ 的前提後，被語法導出、被定義域條件擋下、卻仍有效且推翻者一條都沒有 —— 量測版把人寫表該抓的全抓到了，且不誤傷。44 條推導中 " +
    invalid.to_string() +
    " 條裁決無效（前提違反 " +
    pre_bad.to_string() +
    " 條、溢位 " +
    ovf_bad.to_string() +
    " 條），無效裁決既不算成立也不算推翻。⚠️ 定理 206-3：剩下的 3 條失敗**沒有一條是代數的** —— inv∘expm/⊕/⊕ 偏差 " +
    fmt_e(d1) +
    "（偽逆的奇異值截斷不可複合：整體與分塊看到的尺度不同，截斷點就不同）、chol∘expm/⊞/⊗ 偏差 " +
    fmt_e(d2) +
    "（只比門檻高一成）、det∘expm/⊞/^ 偏差 " +
    fmt_e(d3) +
    "（det(expm M) = e^{tr M}，指數一大就沒有有效位數）。命題 206-4：容差在此是**承重的** —— N-33 的相對偏差離門檻有七個數量級，複合後最壞的成立者只剩 " +
    fmt_e(worst_hold) +
    "，餘裕僅 " +
    fmt_d(margin, 1) +
    " 倍。命題 206-5：溢位記為未裁決而非推翻；本條並補掉一個無窮迴圈 —— expm∘expm 把特徵值推到 e^(e^λ) 溢位成 +∞，餵給 sqrt_newton 後其縮放迴圈 while v >= 4.0 { v = v/4.0 } 永不終止（∞/4 = ∞），這個洞是 ℝ 軌進複合器才踩出來的。增益最高三條：" +
    tops +
    "⚠️ 以 flop 計，**不可**與 ℚ 軌之字乘法增益並列。",
  )
}

///|
/// N-33 之義務：ℝ 軌進入搜尋引擎。
///
/// 驗收標準（第三輪計劃所訂）：搜尋引擎必須**自行重新尋獲**手寫律庫
/// N-21…N-24 的核心結論。若引擎找不到人已經證出來的律，
/// 「自動尋找結構律」這句話就只對便宜的 ℚ 半邊成立。
pub fn ob_n33() -> Check {
  let tbl = rlaw_search_std(ob_rng())
  let mut ok = true
  if tbl.length() != 39 {
    ok = false
  }

  // ── 定理 196-1（引擎重新尋獲手寫律庫之核心）────────────────
  // 左欄為引擎找到的候選，右欄為本庫既有之手寫條目。
  let must_hold : Array[(String, String, String, String)] = [
    ("eig", "⊗", "λᵢμⱼ", "N-21 譜律"),
    ("eig", "⊞", "λᵢ+μⱼ", "N-24 Kronecker 和譜律"),
    ("eig", "⊕", "λ∪μ", "直和譜併"),
    ("chol", "⊗", "⊗", "N-22 Cholesky"),
    ("sqrtm", "⊗", "⊗", "N-24 矩陣平方根"),
    ("expm", "⊞", "⊗", "N-24 expm(A⊞B) = expm A ⊗ expm B"),
    ("inv", "⊗", "⊗", "N-03 之 ℝ 軌對應"),
    ("det", "⊗", "^", "det 冪律之 ℝ 軌對應"),
  ]
  let found : Array[String] = []
  for mh in must_hold {
    let (p, c, r, src) = mh
    match law_find(tbl, p, c, r) {
      Some(true) => {
        let mut g = 0.0
        for t in tbl {
          if t.cphi == p && t.ccomb == c && t.crule == r {
            g = t.cgain
          }
        }
        found.push(src + " ×" + fmt_d(g, 1))
      }
      _ => ok = false
    }
  }

  // ── 定理 196-2（似是而非者須被推翻）────────────────────────
  // 這些是「看起來很像」的錯配：若引擎照單全收，它就不是在尋找律，
  // 而是在生成一張任何東西都成立的表。
  let must_fail : Array[(String, String, String)] = [
    ("expm", "⊗", "⊗"), // exp(A⊗B) ≠ exp A ⊗ exp B
    ("eig", "⊗", "λᵢ+μⱼ"), // 把 ⊞ 的譜律錯配到 ⊗
    ("eig", "⊞", "λᵢμⱼ"), // 把 ⊗ 的譜律錯配到 ⊞
    ("det", "⊞", "·"),
    ("chol", "⊞", "⊗"),
    ("inv", "⊞", "⊗"),
    ("sqrtm", "⊞", "⊗"),
    ("inv", "⊗", "⊕"),
  ]
  for mf in must_fail {
    let (p, c, r) = mf
    if law_find(tbl, p, c, r) != Some(false) {
      ok = false
    }
  }

  // ── 定理 196-3（絕對偏差會系統性冤枉大值的真律）────────────
  // 本庫既有的 mat_dev 是絕對最大偏差。expm 的元素量級為 e^λ，
  // 以絕對 1e-8 裁決必然失敗 —— 而該律是真的。
  let rng = ob_rng()
  let a = rand_spd(rng, 2)
  let b = rand_spd(rng, 3)
  let cc = Cost::new()
  let lhs = cexpm(kron_sum(a, b), cc)
  let rhs = rkron_cost(cc, cexpm(a, cc), cexpm(b, cc))
  let d_abs = mat_dev(lhs, rhs)
  let d_rel = rdev(lhs, rhs, false)
  if d_abs <= 1.0e-8 {
    ok = false // 若絕對偏差也過得了，本條之論點不成立
  }
  if d_rel > 1.0e-8 {
    ok = false // 相對偏差必須過
  }

  // ── 命題 196-5（譜之比較須排序，而排序本身削弱證據）────────
  // 特徵值是重集，Jacobi 吐出的次序與 λᵢμⱼ 的生成次序不同，
  // 不排序就會把真律判成假。但排序也意味著：任何只是把譜重新排列的
  // 錯誤 Φ 都能過關。這是重集語意無法迴避的代價。
  // 掃若干組尺寸，統計「不排序就會被判成假」的比例。
  // 單取一組是不夠的：兩譜恰好同序時，不排序也會通過
  // （本條初版就取到 (2,3) 這種巧合，於是例證落空、義務當場失敗）。
  let mut need_sort = 0
  let mut worst_unsorted = 0.0
  let mut worst_sorted = 0.0
  let mut worst_rel = 0.0
  let pairs : Array[(Int, Int)] = [
    (2, 2),
    (3, 2),
    (4, 2),
    (2, 3),
    (3, 3),
    (4, 3),
  ]
  for pr0 in pairs {
    let (pn, pm) = pr0
    let c2 = Cost::new()
    let aa = rand_spd(rng, pn)
    let bb = rand_spd(rng, pm)
    let (la, _qa, _ra) = cjacobi_eigen(aa, 1.0e-12, 3000, c2)
    let (lb, _qb, _rb) = cjacobi_eigen(bb, 1.0e-12, 3000, c2)
    let (lk, _qk, _rk) = cjacobi_eigen(
      rkron_cost(c2, aa, bb),
      1.0e-12,
      3000,
      c2,
    )
    let prod : Array[Double] = []
    for i in 0..<la.length() {
      for j in 0..<lb.length() {
        prod.push(la[i] * lb[j])
      }
    }
    let mut uns = 0.0
    for i in 0..<lk.length() {
      let e = absd(lk[i] - prod[i])
      if e > uns {
        uns = e
      }
    }
    let srt = spec_dev(lk, prod)
    // 命題 196-4 用：同一條真律在引擎所用之相對度量下的偏差
    let rel = rdev(rcolumn(lk), rcolumn(prod), true)
    if rel > worst_rel {
      worst_rel = rel
    }
    if uns > 1.0e-8 {
      need_sort = need_sort + 1
    }
    if uns > worst_unsorted {
      worst_unsorted = uns
    }
    if srt > worst_sorted {
      worst_sorted = srt
    }
  }
  // 至少要有一組真的需要排序，否則「排序是必要的」無從談起
  if need_sort < 1 {
    ok = false
  }
  // 排序後則必須全數通過
  if worst_sorted > 1.0e-8 {
    ok = false
  }

  // ── 命題 196-4（裁決對「度量」敏感，對「容差」不敏感）──────
  // 本條原本想說的是「ℝ 軌的成立只是在某個容差下成立，收緊容差就會翻盤」。
  // 實測否定了這個說法：所有成立之律的相對偏差都落在 1e-15 量級，
  // 距離 1e-8 的容差有七個數量級的餘裕，容差在 1e-8 與 1e-12 之間
  // 怎麼調都不會改變任何一條裁決。
  //
  // 真正敏感的是**度量的選擇**（定理 196-3）：絕對與相對之間的差距達
  // 1.153e8 vs 4.076e-15，二十三個數量級。結論因此要反過來寫 ——
  // ℝ 軌裁決的脆弱點不在那個旋鈕，而在旋鈕量的是什麼。
  //
  // 餘裕會隨尺寸與條件數縮小：N-21 記載 dim 64 的直接 Jacobi 跑完
  // 4000 次旋轉仍未收斂。本斷言只對本引擎的小網格成立。
  if worst_rel > 1.0e-12 {
    ok = false
  }

  // ── 命題 196-6（引擎找到律，但找不到律的漸近價值）──────────
  // 同一條譜律：引擎在 dim ≤ 6 的搜尋網格上量到 ×12.1，
  // N-21 在 dim 36 上量到 ×303.7。律是同一條，增益卻差 25 倍 ——
  // 增益是尺寸的函數，搜尋網格必須小才跑得動，於是引擎系統性低估價值。
  let mut g_small = 0.0
  for t in tbl {
    if t.cphi == "eig" && t.ccomb == "⊗" && t.crule == "λᵢμⱼ" {
      g_small = t.cgain
    }
  }
  // 同一條律在較大尺寸上重測
  let a4 = rand_spd(rng, 4)
  let b4 = rand_spd(rng, 4)
  let cd = Cost::new()
  let (lw, _q1, _r1) = cjacobi_eigen(rkron_cost(cd, a4, b4), 1.0e-12, 3000, cd)
  let cf = Cost::new()
  let (l1, _q2, _r2) = cjacobi_eigen(a4, 1.0e-12, 3000, cf)
  let (l2, _q3, _r3) = cjacobi_eigen(b4, 1.0e-12, 3000, cf)
  let pr : Array[Double] = []
  for i in 0..<l1.length() {
    for j in 0..<l2.length() {
      pr.push(l1[i] * l2[j])
    }
  }
  cflop(cf, pr.length().to_int64())
  if spec_dev(lw, pr) > 1.0e-8 {
    ok = false
  }
  let g_big = flop_ratio(cd, cf)
  if g_big <= g_small {
    ok = false // 增益必須隨尺寸上升，否則本命題之論點不成立
  }
  mk_check(
    "N-33 ℝ 軌進入搜尋引擎",
    ok,
    tbl.length() + must_hold.length() + must_fail.length() + 8,
    "候選 39（Φ 6 × C 3 × ⊙ 依型別），成立 13、推翻 26。引擎自行重新尋獲手寫律庫之核心：" +
    found.join("　") +
    "；8 條似是而非之錯配全數推翻。偏差度量之偏誤（實測）：expm(A⊞B) = expm A ⊗ expm B 以**絕對**偏差裁決為 " +
    fmt_e(d_abs) +
    " ⇒ 推翻（冤枉），改**相對**偏差為 " +
    fmt_e(d_rel) +
    " ⇒ 成立。裁決對度量敏感、對容差不敏感：全部成立之律的相對偏差最大僅 " +
    fmt_e(worst_rel) +
    "，距 1e-8 容差有七個數量級餘裕，容差怎麼調都不翻盤 —— 脆弱點不在旋鈕，而在旋鈕量的是什麼。惟 ℝ 軌之「成立」終究是容差下的成立，證據強度仍弱於 ℚ 軌的逐位元相等。譜須排序：6 組尺寸中 " +
    need_sort.to_string() +
    " 組不排序即被判成假（最大未排序偏差 " +
    fmt_e(worst_unsorted) +
    "），排序後最大偏差降至 " +
    fmt_e(worst_sorted) +
    " —— 排序是重集語意的必要代價，但也讓任何只重排譜的錯誤 Φ 得以過關。增益是尺寸的函數：同一條譜律，引擎在 dim ≤ 6 網格上 ×" +
    fmt_d(g_small, 1) +
    "、dim 16 上 ×" +
    fmt_d(g_big, 1) +
    "、N-21 在 dim 36 上 ×303.7 —— 搜尋網格必須小才跑得動，故引擎系統性低估律的價值。",
  )
}

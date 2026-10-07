///|
/// 迴歸測試：整份評審準則目錄之義務必須全數通過。
test "評審準則目錄：全部義務自證通過" {
  let (results, v) = run_catalogue()
  for f in v.failures {
    println("✘ " + f)
  }
  println(
    "目錄條目 " +
    v.entries.to_string() +
    "，通過 " +
    v.passed.to_string() +
    "，失敗 " +
    v.failed.to_string() +
    "，驗證實例 " +
    v.instances.to_string(),
  )
  assert_eq(results.length(), v.entries)
  assert_true(v.entries > 80) // 題目要求：評審準則演算法多於 80 條
  assert_eq(v.failed, 0)

  // 取樣政策對帳（第十輪）—— 不另外跑一遍目錄，直接用上面已有的結果。
  // 政策寫在 policy.mbt，這裡是它的執行面：受管轄條目之實測取樣量
  // 必須恰等於 max(目標, 已登記下限)。偏離即測試失敗，無從靜悄悄累積。
  let cat = catalogue()
  let viol : Array[String] = []
  let mut governed = 0
  for i in 0..<cat.length() {
    let code = cat[i].code
    if trial_governed(code) {
      governed = governed + 1
      let want = trial_policy(code)
      if results[i].trials != want {
        viol.push(
          code +
          " 實測 " +
          results[i].trials.to_string() +
          " ≠ 政策 " +
          want.to_string(),
        )
      }
    }
  }
  for s in viol {
    println("✘ 取樣政策 " + s)
  }
  println(
    "取樣政策：受管轄 " +
    governed.to_string() +
    " 條，違反 " +
    viol.length().to_string() +
    " 條",
  )
  assert_eq(viol.length(), 0)
  assert_eq(governed, 134)
}

///|
/// 目錄之完整性：每條目之各欄位皆非空，且編號不重複。
test "評審準則目錄：欄位完整且編號唯一" {
  let cat = catalogue()
  let seen : Array[String] = []
  for a in cat {
    assert_true(a.code != "")
    assert_true(a.zh != "")
    assert_true(a.cat != "")
    assert_true(a.spaces != "")
    assert_true(a.deff != "")
    assert_true(a.formula != "")
    assert_true(a.thm != "")
    assert_true(a.proof != "")
    assert_true(a.track != "")
    for s in seen {
      assert_true(s != a.code)
    }
    seen.push(a.code)
  }
  assert_eq(seen.length(), cat.length())
}

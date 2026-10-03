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

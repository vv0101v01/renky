///|
/// N-44 之義務：定律表作為受版本控管的產物。
///
/// 定律表是本庫的核心產物，而它會隨 Φ 集、⊙ 集、取樣分布與隨機種子而變。
/// 沒有指紋的話，這些變動會悄悄發生：有人改了取樣器、定律表少了兩條律、
/// 報告照樣產出、沒有任何東西失敗。本條把三張表的指紋釘成常數。
pub fn ob_n44() -> Check {
  let mut ok = true
  let q_pd = law_search_std(ob_rng())
  let q_fix = law_search_fixed(ob_rng())
  let r_tbl = rlaw_search_std(ob_rng())
  let d1 = law_digest(q_pd)
  let d2 = law_digest(q_fix)
  let d3 = law_digest(r_tbl)

  // ── 定理 200-1（三張表之指紋釘為常數）────────────────────
  // 任何對 Φ 集、⊙ 集、取樣分布或種子的改動都會讓這裡失敗，
  // 迫使改動者去看 docs/定律表.md 的差異並更新此處。
  if d1 != "72:16:269201920" {
    ok = false
  }
  if d2 != "72:15:857016814" {
    ok = false
  }
  if d3 != "39:13:494275188" {
    ok = false
  }

  // ── 定理 200-2（指紋對「一進一出」敏感）──────────────────
  // 只記成立數的指紋抓不到「推翻一條、成立另一條」這種總數不變的變動。
  // 構造該情形並確認指紋確實改變。
  let tampered : Array[LawCand] = []
  let mut flipped_on = false
  let mut flipped_off = false
  for t in q_pd {
    if t.cholds && !flipped_off {
      flipped_off = true
      tampered.push({ ..t, cholds: false, })
    } else if !t.cholds && !flipped_on {
      flipped_on = true
      tampered.push({ ..t, cholds: true, })
    } else {
      tampered.push(t)
    }
  }
  let mut th = 0
  for t in tampered {
    if t.cholds {
      th = th + 1
    }
  }
  // 成立數不變，但指紋必須變
  if th != 16 {
    ok = false
  }
  if law_digest(tampered) == d1 {
    ok = false
  }

  // ── 定理 200-3（兩張 ℚ 表之差異恰為 N-36 所修復的那一條）──
  let diff = law_diff(q_pd, q_fix)
  if diff.length() != 1 {
    ok = false
  }

  // ── 命題 200-4（全量掃描與常規義務不得分岔）──────────────
  // docs/定律表.md 由 cmd/lawsearch 產出，而本條在義務內重算同樣三張表。
  // 兩者若用不同的入口，報告與義務就可能各說各話。此處確認三張表
  // 都走 *_std／*_fixed 這組共用快取入口（未命中計數恆為 1）。
  if law_miss_count() != 1 || rlaw_miss_count() != 1 {
    ok = false
  }
  mk_check(
    "N-44 定律表之版本指紋",
    ok,
    q_pd.length() + q_fix.length() + r_tbl.length() + 6,
    "三張定律表之指紋已釘為常數：ℚ 正定 " +
    d1 +
    "、ℚ 修復後 " +
    d2 +
    "、ℝ 軌 " +
    d3 +
    "（格式為 候選數:成立數:位置加權校驗和）。任何對 Φ 集、⊙ 集、取樣分布或隨機種子的改動都會讓本條失敗，迫使改動者去看 docs/定律表.md 的差異並更新此處。指紋同時編碼成立數與成立位置：實測把一條成立翻為推翻、另一條推翻翻為成立（總數仍為 16）後指紋確實改變 —— 只記數量的指紋會漏掉這種最難察覺的變動。兩張 ℚ 表之差異恰 1 條，即 N-36 所修復者。三張表皆走共用快取入口，全庫各處與 cmd/lawsearch 讀到的是同一張表。",
  )
}

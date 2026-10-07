///|
/// N-41 之義務：k 元律與最佳結合順序。
///
/// 四件事要驗：
///   (1) 符號成本模型與實測**逐位相等**（而且單位要對）
///   (2) k = 2 時 k 元裁決器與現行二元裁決器**逐例相同**
///   (3) 區間 DP 確實最佳 —— 並給出左／右／平衡／貪婪各自輸掉的具體例子
///   (4) 組裝項對矩陣值 Φ 不會被分解消掉，因而是增益的天花板
pub fn ob_n41() -> Check {
  let mut ok = true

  // ── 命題 202-1（符號預測 = 實測，單位是有理數乘法次數）──
  // 第一次做這件事時把 acost 拿去對 Cost.wmul，差了六倍（180 vs 1111）。
  // 原因不是模型錯，是粒度混用：wmul 隨運算元位寬加權，符號模型只看形狀。
  // 故本庫為 Cost 增設 qmul（元素級乘法次數），這一層才對得起來。
  let dims3 = [2, 3, 2]
  let rng = ob_rng()
  let parts3 : Array[Mat[Q]] = []
  for d in dims3 {
    parts3.push(rand_gram(rng, d))
  }
  let trees3 = [assoc_left(3), assoc_right(3), assoc_balanced(3)]
  let wmuls : Array[Int64] = []
  for t in trees3 {
    let c = Cost::new()
    let _g = chain_build("⊗", t, parts3, c)
    if t.acost(dims3) != c.qmul {
      ok = false
    }
    // 同時確認「對 wmul 必然對不上」—— 這個陷阱要留在義務裡，不然會再踩
    if t.acost(dims3) == c.wmul {
      ok = false
    }
    if t.anodes() != 2 {
      ok = false
    }
    wmuls.push(c.wmul)
  }
  // 附帶發現：qmul 相同而 wmul 不同（1111 vs 1108）—— 符號模型預測得了
  // 運算次數，預測不了係數膨脹。這正是 N-43 所說「CRT 的獲益是膨脹的函數」
  // 之同一件事，從另一側看到。
  if wmuls.length() == 3 && wmuls[0] == wmuls[1] {
    ok = false
  }

  // ── 命題 202-2（k = 2 退化為現行二元裁決器，逐例相同）──
  // 比的不只是裁決，是對定律表全部 72 個候選 × 4 個樣本，兩條路徑的
  // 輸出是否一致。只比裁決的話，兩邊同樣錯也會「通過」。
  let degen = karity_degenerate_diff(law_samples_mixed())
  if degen != 0 {
    ok = false
  }

  // ── 定理 202-3（區間 DP 之最佳性，及三個具體敗例）────────
  // C(i,j) = P(i,j)² + min_t [C(i,t) + C(t+1,j)]。
  // 注意 P(i,j)² 與切點無關 —— 這是本問題與矩陣鏈乘法的差別。
  let grid : Array[Array[Int]] = [
    [2, 2, 2, 2],
    [5, 2, 2, 5],
    [2, 5, 5, 2],
    [2, 2, 3, 2, 2],
    [3, 2, 2, 2, 3],
    [2, 3, 4, 5],
    [4, 2, 3, 2, 4],
  ]
  let mut beats_lr = 0
  let mut greedy_loses = 0
  let mut bal_loses = 0
  for dv in grid {
    let k = dv.length()
    let (dpc, dpt) = assoc_dp(dv)
    let lc = assoc_left(k).acost(dv)
    let rc = assoc_right(k).acost(dv)
    let bc = assoc_balanced(k).acost(dv)
    let gc = assoc_greedy(dv).acost(dv)
    // 最佳性：DP 不得輸給任何一個固定策略
    if dpc > lc || dpc > rc || dpc > bc || dpc > gc {
      ok = false
    }
    // DP 回傳的樹，其成本必須等於 DP 回傳的數字（樹與值不得分岔）
    if dpt.acost(dv) != dpc || dpt.anodes() != k - 1 {
      ok = false
    }
    if dpc < lc && dpc < rc {
      beats_lr = beats_lr + 1
    }
    if gc > dpc {
      greedy_loses = greedy_loses + 1
    }
    if bc > dpc {
      bal_loses = bal_loses + 1
    }
  }
  // 三個敗例都必須真的出現，否則這條 DP 是在解一個不存在的問題
  if beats_lr < 1 || greedy_loses < 1 || bal_loses < 1 {
    ok = false
  }
  // 點名三個具體例子，釘死
  let (dp4, _t4) = assoc_dp([2, 2, 2, 2])
  if dp4 != 288L || assoc_left(4).acost([2, 2, 2, 2]) != 336L {
    ok = false
  }
  let (dp5, _t5) = assoc_dp([5, 2, 2, 5])
  if dp5 != 10200L || assoc_greedy([5, 2, 2, 5]).acost([5, 2, 2, 5]) != 10416L {
    ok = false
  }
  let (dp6, _t6) = assoc_dp([3, 2, 2, 2, 3])
  if dp6 != 5380L || assoc_balanced(5).acost([3, 2, 2, 2, 3]) != 5400L {
    ok = false
  }

  // ── 命題 202-4（組裝項是矩陣值 Φ 的增益天花板）──────────
  // 矩陣值 Φ 配 ⊗ 規則時，分解路徑的輸出端仍要組一條**維數完全相同**的
  // Kronecker 鏈，故組裝項在兩條路徑上同時出現、不會被分解消掉。
  // 純量值 Φ 則根本不組鏈 —— 這是分解帶來的第二層節省。
  let dims4 = [2, 2, 2, 2]
  let (_c4, best4) = assoc_dp(dims4)
  let parts4 : Array[Mat[Q]] = []
  let rng4 = ob_rng()
  for d in dims4 {
    parts4.push(rand_gram(rng4, d))
  }
  let mut mat_side = 0
  let mut sca_side = 0
  for pr in [("inv", "⊗"), ("sq", "⊗"), ("cube", "⊗"), ("tr̃ans", "⊗")] {
    let (ph, rl) = pr
    match check_law_k(ph, "⊗", rl, parts4, best4) {
      Some(v) => {
        if !v.kholds {
          ok = false
        }
        // 分解路徑的元素級乘法數不得少於組裝 —— 組裝整條都還在裡面
        if v.kqfast < v.kqasm {
          ok = false
        }
        mat_side = mat_side + 1
      }
      None => ok = false
    }
  }
  for pr in [("det", "^"), ("trace", "·"), ("rank", "·")] {
    let (ph, rl) = pr
    match check_law_k(ph, "⊗", rl, parts4, best4) {
      Some(v) => {
        if !v.kholds {
          ok = false
        }
        // 純量值 Φ：分解路徑完全不組鏈，故其元素級乘法數**嚴格少於**組裝量
        // （實測 det 35、trace 3、rank 3，對比組裝 288）
        if v.kqfast >= v.kqasm {
          ok = false
        }
        sca_side = sca_side + 1
      }
      None => ok = false
    }
  }
  if mat_side != 4 || sca_side != 3 {
    ok = false
  }

  // ── 命題 202-5（k 增長時，純量值 Φ 的增益成長快於矩陣值）
  // 因為前者沒有組裝天花板。以 inv（矩陣值）對 det（純量值）量 k = 2→4。
  let g = (ph : String, rl : String, dv : Array[Int]) => {
    let (_cc, tr) = assoc_dp(dv)
    let r2 = ob_rng()
    let ps : Array[Mat[Q]] = []
    for d in dv {
      ps.push(rand_gram(r2, d))
    }
    match check_law_k(ph, "⊗", rl, ps, tr) {
      Some(v) => v.kgain()
      None => 0.0
    }
  }
  let inv2 = g("inv", "⊗", [2, 2])
  let inv4 = g("inv", "⊗", [2, 2, 2, 2])
  let det2 = g("det", "^", [2, 2])
  let det4 = g("det", "^", [2, 2, 2, 2])
  if !(inv4 > inv2 && det4 > det2) {
    ok = false
  }
  if !(det4 / det2 > inv4 / inv2) {
    ok = false
  }
  mk_check(
    "N-41 k 元律與最佳結合順序",
    ok,
    degen_trials() + grid.length() * 6 + 7 + 4 + 9,
    "k 元裁決器 check_law_k 把律由二元推廣到任意 k，並把**結合順序**提為顯式參數。符號成本模型 acost(樹,維數) = Σ 內部節點 (區間維數積)² 與實測之有理數乘法次數逐位相等（dims (2,3,2) 三棵樹皆為 180）。⚠️ 單位陷阱已寫入義務：同一式對 Cost.wmul 差六倍（180 vs 1111），因為 wmul 隨運算元位寬加權而符號模型只看形狀 —— 本庫為此在 Cost 增設 qmul 粒度。附帶：三棵樹 qmul 相同而 wmul 不同（1111 vs 1108），可見符號模型預測得了運算次數、預測不了係數膨脹。退化性：k = 2 時對定律表全部 72 個候選 × 4 樣本，k 元路徑與二元路徑逐例相同（相異 " +
    degen.to_string() +
    " 例）。最佳結合順序為區間 DP：C(i,j) = P(i,j)² + min_t[C(i,t)+C(t+1,j)]，其中 P(i,j)² 與切點無關 —— 這正是它與矩陣鏈乘法的差別，DP 實際上是在選「哪些區間會出現」。七組維數向量上 DP 不輸任一固定策略，且三個敗例都真的出現：(2,2,2,2) DP 288 < 左=右 336；(5,2,2,5) 貪婪 10416 > DP 10200（局部最便宜 ≠ 整體最便宜）；(3,2,2,2,3) 平衡 5400 > DP 5380（平衡樹並非最佳）。⚠️ 本條最重要的是一個負面結果：矩陣值 Φ 配 ⊗ 規則時，分解路徑的輸出端仍須組一條維數完全相同的 Kronecker 鏈，組裝項在兩條路徑上同時出現、不會被分解消掉，於是增益上界降為 Θ(N) —— 而 N-03 宣告的 Θ(N³/Σnᵢ³) 是忽略組裝得到的。純量值 Φ 沒有這個天花板（分解路徑根本不組鏈），故 k 增長時增益成長明顯較快：k 2→4，inv ×" +
    fmt_d(inv2, 1) +
    "→×" +
    fmt_d(inv4, 1) +
    "，det ×" +
    fmt_d(det2, 1) +
    "→×" +
    fmt_d(det4, 1) +
    "。侷限：mrank 與 transpose 在本庫未計費，故 rank 與 tr̃ans 的數字只反映組裝之有無，不含演算法本身。",
  )
}

///|
/// 退化性檢查之試驗數（72 候選 × 4 樣本）
fn degen_trials() -> Int {
  72 * law_samples_mixed().length()
}

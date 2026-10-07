///|
/// # N-63 ⊞ 的 k 元成本模型
///
/// ## 欠了三輪的那一條
///
/// N-41 給了 ⊗ 鏈的成本模型與區間 DP：
///
/// ```text
///   cost_⊗(樹) = Σ_{內部節點 v} P(v)²      P(v) = 該區間之維數積
/// ```
///
/// 這個模型有一個很舒服的性質 —— **組裝一段區間的代價只取決於該區間的維數積，
/// 與它內部怎麼切無關**（p×p 與 q×q 的 Kronecker 積恰需 (pq)² 次乘法）。
/// 正因如此，區間 DP 的狀態只需要 (i, j)。
///
/// ⊞（Kronecker 和）一直沒有自己的模型。更糟的是 `qkron_sum` **根本不計量** ——
/// 它用 `mkron`（未計費）而不是 `qkron_cost`，於是 `chain_build` 走 ⊞ 分支時
/// Cost 完全不動。一條沒有成本的運算在成本模型裡是隱形的。
///
/// ## 關鍵差別：⊞ 的組裝成本與切法有關
///
/// A ⊞ B = A⊗I_q + I_p⊗B。這個東西**沒有乘法**：
///
/// ```text
///   C[(i,k),(j,l)] = A[i][j]·δ_{kl} + δ_{ij}·B[k][l]
/// ```
///
/// 每一個非零位置都是「把 A 或 B 的某一項搬過去」，對角位置再加一次。
/// 搬運次數 = p²q（來自 A⊗I）+ pq²（來自 I⊗B）：
///
/// ```text
///   f(p, q) = p²q + pq² = P·(p + q)        P = pq
/// ```
///
/// **這個數字不只取決於 P，還取決於 p 與 q 怎麼分。** ⊗ 的 P² 看不見切法，
/// ⊞ 的 P(p+q) 看得見。於是 ⊞ 不能沿用 N-41 的 DP，它要自己的：
///
/// ```text
///   C⊞(i,j) = min_{i ≤ t < j} [ C⊞(i,t) + C⊞(t+1,j) + P(i,j)·(P(i,t) + P(t+1,j)) ]
/// ```
///
/// 狀態仍是 (i, j)，但轉移裡多了一項依賴切點 t 的成本。
///
/// ## 兩種實作，兩個量綱
///
/// 現行的 `qkron_sum` 是稠密的：造兩個 (pq)×(pq) 的 Kronecker 積再相加，
/// 代價 2(pq)² 次**乘法**。稀疏感知版本代價 P(p+q) 次**搬運／加法**，乘法為零。
/// 兩者量綱不同（wmul vs wadd），不能直接比 —— 本條分別量，並列出比值。

///|
/// 受計量之稀疏感知 Kronecker 和。
///
/// 不造中間的兩個 Kronecker 積；直接把 A 與 B 的項搬到該去的位置，
/// 對角位置相加。計費記在 `wadd`（搬運／加法），乘法為零 ——
/// 這正是 ⊞ 的實質：它不乘東西。
pub fn qkron_sum_cost(c : Cost, a : Mat[Q], b : Mat[Q]) -> Mat[Q] {
  let p = a.mrows
  let q = b.mrows
  let n = p * q
  let out = Mat::build(n, n, (_i, _j) => Q::zero())
  // A ⊗ I_q：p² 個區塊，每區塊對角 q 項
  for i in 0..<p {
    for j in 0..<p {
      let v = a.at(i, j)
      for k in 0..<q {
        out.put(i * q + k, j * q + k, v)
        c.wadd = c.wadd + 1L
      }
    }
  }
  // I_p ⊗ B：p 個對角區塊，每區塊 q² 項（與上一步在對角位置重疊，故相加）
  for i in 0..<p {
    for k in 0..<q {
      for l in 0..<q {
        let r = i * q + k
        let s = i * q + l
        out.put(r, s, out.at(r, s).add(b.at(k, l)))
        c.wadd = c.wadd + 1L
      }
    }
  }
  out
}

///|
/// 稠密版（現行 `qkron_sum` 的計量版本）：造兩個 Kronecker 積再相加。
/// 計費記在 `wmul`，共 2(pq)² 次。
pub fn qkron_sum_dense_cost(c : Cost, a : Mat[Q], b : Mat[Q]) -> Mat[Q] {
  let p = a.mrows
  let q = b.mrows
  let x = qkron_cost(c, a, Mat::ident(q))
  let y = qkron_cost(c, Mat::ident(p), b)
  x.plus(y)
}

///|
/// ⊞ 之組裝成本模型：f(p, q) = P·(p + q)，P = pq。
pub fn ks_pair_cost(p : Int64, q : Int64) -> Int64 {
  p * q * (p + q)
}

///|
/// 一棵結合樹在 ⊞ 下的總組裝成本。
pub fn AssocTree::kscost(self : AssocTree, dims : Array[Int]) -> Int64 {
  match self {
    ALeaf(_) => 0L
    ANode(l, r) => {
      let pl = l.aprod(dims)
      let pr = r.aprod(dims)
      l.kscost(dims) + r.kscost(dims) + ks_pair_cost(pl, pr)
    }
  }
}

///|
/// ⊞ 專屬的區間 DP。轉移項依賴切點，故不能沿用 `assoc_dp`。
pub fn ks_dp(dims : Array[Int]) -> (Int64, AssocTree) {
  let k = dims.length()
  if k == 1 {
    return (0L, ALeaf(0))
  }
  let pre : Array[Array[Int64]] = Array::makei(k, _ => Array::make(k, 1L))
  for i in 0..<k {
    let mut acc = 1L
    for j in i..<k {
      acc = acc * dims[j].to_int64()
      pre[i][j] = acc
    }
  }
  let best : Array[Array[Int64]] = Array::makei(k, _ => Array::make(k, 0L))
  let tree : Array[Array[AssocTree]] = Array::makei(k, _ => {
    Array::make(k, ALeaf(0))
  })
  for i in 0..<k {
    tree[i][i] = ALeaf(i)
  }
  for len in 2..<=k {
    for i in 0..<=(k - len) {
      let j = i + len - 1
      let mut bc = -1L
      let mut bt : AssocTree = ALeaf(i)
      for t in i..<j {
        let c = best[i][t] +
          best[t + 1][j] +
          ks_pair_cost(pre[i][t], pre[t + 1][j])
        if bc < 0L || c < bc {
          bc = c
          bt = ANode(tree[i][t], tree[t + 1][j])
        }
      }
      best[i][j] = bc
      tree[i][j] = bt
    }
  }
  (best[0][k - 1], tree[0][k - 1])
}

///|
/// 以給定結合樹組一條 ⊞ 鏈（稀疏感知、受計量）。
pub fn ks_chain_build(t : AssocTree, parts : Array[Mat[Q]], c : Cost) -> Mat[Q] {
  match t {
    ALeaf(i) => parts[i]
    ANode(l, r) => {
      let a = ks_chain_build(l, parts, c)
      let b = ks_chain_build(r, parts, c)
      qkron_sum_cost(c, a, b)
    }
  }
}

///|
/// 模型對帳：對一組維數與一棵樹，比對模型預測與實測 `wadd`。
/// 回傳 (模型, 實測, 是否相等)。
pub fn ks_model_check(
  dims : Array[Int],
  t : AssocTree,
  rng : Rng,
) -> (Int64, Int64, Bool) {
  let parts : Array[Mat[Q]] = []
  for d in dims {
    parts.push(rand_gram(rng, d))
  }
  let c = Cost::new()
  let _ = ks_chain_build(t, parts, c)
  let m = t.kscost(dims)
  (m, c.wadd, m == c.wadd)
}

///|
/// ⊞ 鏈之結合順序掃描。
///
/// 回傳 (維數組數, 模型全部對帳成功?, ⊞-DP 與 ⊗-DP 樹不同之組數,
///        用錯樹的最大成本損失比, ⊞-DP 相對左結合之最大增益)。
pub fn ks_assoc_scan(rng : Rng) -> (Int, Bool, Int, Double, Double) {
  let cases : Array[Array[Int]] = [
    [2, 2, 2],
    [2, 3, 4],
    [4, 3, 2],
    [2, 8, 2],
    [8, 2, 2],
    [2, 2, 8],
    [2, 3, 2, 3],
    [5, 2, 2, 3],
    [2, 2, 2, 2],
    [3, 2, 4, 2],
    [2, 6, 2, 2],
    [2, 2, 3, 5],
  ]
  let mut allok = true
  let mut ndiff = 0
  let mut worst = 1.0
  let mut bestgain = 1.0
  for dims in cases {
    let (_, kt) = ks_dp(dims)
    let (_, ot) = assoc_dp(dims)
    let ck = kt.kscost(dims)
    let co = ot.kscost(dims)
    if kt.alabel() != ot.alabel() {
      ndiff = ndiff + 1
    }
    if ck > 0L {
      let r = co.to_double() / ck.to_double()
      if r > worst {
        worst = r
      }
    }
    let cl = assoc_left(dims.length()).kscost(dims)
    if ck > 0L {
      let g = cl.to_double() / ck.to_double()
      if g > bestgain {
        bestgain = g
      }
    }
    let (_, _, okm) = ks_model_check(dims, kt, rng)
    if !okm {
      allok = false
    }
  }
  (cases.length(), allok, ndiff, worst, bestgain)
}

///|
/// 稀疏感知與稠密兩種實作之對照（同一條鏈、同一棵樹）。
/// 回傳 (稀疏 wadd, 稠密 wmul, 兩者輸出是否逐元相同)。
pub fn ks_sparse_vs_dense(dims : Array[Int], rng : Rng) -> (Int64, Int64, Bool) {
  let parts : Array[Mat[Q]] = []
  for d in dims {
    parts.push(rand_gram(rng, d))
  }
  let (_, t) = ks_dp(dims)
  let c1 = Cost::new()
  let a = ks_chain_build(t, parts, c1)
  let c2 = Cost::new()
  fn dense(u : AssocTree) -> Mat[Q] {
    match u {
      ALeaf(i) => parts[i]
      ANode(l, r) => qkron_sum_dense_cost(c2, dense(l), dense(r))
    }
  }

  let b = dense(t)
  (c1.wadd, c2.wmul, a.equals(b))
}

///|
/// ⊞ 的 k 元結合律：任何結合樹組出來的矩陣都相同。
/// 回傳 (檢查的樹數, 全部相同?)。
pub fn ks_assoc_law(dims : Array[Int], rng : Rng) -> (Int, Bool) {
  let parts : Array[Mat[Q]] = []
  for d in dims {
    parts.push(rand_gram(rng, d))
  }
  let k = dims.length()
  let trees = [
    assoc_left(k),
    assoc_right(k),
    assoc_balanced(k),
    ks_dp(dims).1,
    assoc_dp(dims).1,
  ]
  let ref_ = ks_chain_build(trees[0], parts, Cost::new())
  let mut same = true
  for t in trees {
    if !ks_chain_build(t, parts, Cost::new()).equals(ref_) {
      same = false
    }
  }
  (trees.length(), same)
}

///|
/// 指紋。
pub fn ks_digest(rng : Rng) -> String {
  let (n, ok, nd, worst, gain) = ks_assoc_scan(rng)
  n.to_string() +
  ":" +
  (if ok { "1" } else { "0" }) +
  ":" +
  nd.to_string() +
  ":" +
  fmt_d(worst, 4) +
  ":" +
  fmt_d(gain, 4)
}

///|
/// 窮舉搜尋：⊞-DP 與 ⊗-DP 的最佳樹是否曾經不同。
///
/// 回傳 (檢查組數, 樹不同之組數, 用 ⊗ 樹時相對 ⊞ 最佳之最大損失比,
///        cost⊞ ≤ cost⊗ 成立之組數)。
pub fn ks_vs_kron_sweep(lo : Int, hi : Int, k : Int) -> (Int, Int, Double, Int) {
  let mut tot = 0
  let mut diff = 0
  let mut worst = 1.0
  let mut le = 0
  let idx = Array::make(k, lo)
  let mut go = true
  while go {
    let dims = Array::makei(k, i => idx[i])
    let (ck, kt) = ks_dp(dims)
    let (_, ot) = assoc_dp(dims)
    tot = tot + 1
    if kt.alabel() != ot.alabel() {
      diff = diff + 1
      if ck > 0L {
        let r = ot.kscost(dims).to_double() / ck.to_double()
        if r > worst {
          worst = r
        }
      }
    }
    // 命題：對每一棵樹，cost⊞(T) ≤ cost⊗(T)
    if kt.kscost(dims) <= kt.acost(dims) {
      le = le + 1
    }
    // 進位
    let mut p = k - 1
    go = false
    while p >= 0 {
      idx[p] = idx[p] + 1
      if idx[p] <= hi {
        go = true
        break
      }
      idx[p] = lo
      p = p - 1
    }
  }
  (tot, diff, worst, le)
}

///|
/// 等號條件之檢查：cost⊞(T) = cost⊗(T) ⟺ 每個內部節點都切成 2 與 2。
/// 回傳 (k=2 且 dims=[2,2] 時是否相等, k=3 且 dims=[2,2,2] 時是否嚴格小於)。
pub fn ks_equality_case() -> (Bool, Bool) {
  let t2 = assoc_left(2)
  let d2 = [2, 2]
  let eq = t2.kscost(d2) == t2.acost(d2)
  let t3 = assoc_left(3)
  let d3 = [2, 2, 2]
  let lt = t3.kscost(d3) < t3.acost(d3)
  (eq, lt)
}

///|
/// 找出 ⊞-DP 與 ⊗-DP 相異之具名反例（回傳維數、兩棵樹之標籤、兩個成本）。
pub fn ks_named_counterexample(
  lo : Int,
  hi : Int,
  k : Int,
) -> (Array[Int], String, String, Int64, Int64)? {
  let idx = Array::make(k, lo)
  let mut go = true
  let mut bestr = 1.0
  let mut out : (Array[Int], String, String, Int64, Int64)? = None
  while go {
    let dims = Array::makei(k, i => idx[i])
    let (ck, kt) = ks_dp(dims)
    let (_, ot) = assoc_dp(dims)
    if kt.alabel() != ot.alabel() && ck > 0L {
      let co = ot.kscost(dims)
      let r = co.to_double() / ck.to_double()
      if r > bestr {
        bestr = r
        out = Some((dims, kt.alabel(), ot.alabel(), ck, co))
      }
    }
    let mut p = k - 1
    go = false
    while p >= 0 {
      idx[p] = idx[p] + 1
      if idx[p] <= hi {
        go = true
        break
      }
      idx[p] = lo
      p = p - 1
    }
  }
  out
}

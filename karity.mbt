///|
/// # N-41 k 元律與最佳結合順序
///
/// ## 現況的侷限
///
/// 定律表上每一條律都是二元的：`Φ(C(A,B)) = Φ(A) ⊙ Φ(B)`。
/// 但真正用得上結構律的場合幾乎都是 k 元的 —— FWHT 是 log₂N 個 2×2 因子的
/// Kronecker 鏈（N-25），張量網路是任意長度的鏈。把 k 元鏈當成「反覆套用
/// 二元律」雖然算得出來，卻把一個真實的選擇藏了起來：**結合順序**。
///
/// ## 兩個結合順序，不是一個
///
/// ```text
///   直接路徑：  Φ( A₁ ⊗ A₂ ⊗ … ⊗ A_k )     ← 鏈要先組裝，組裝有順序
///   分解路徑：  Φ(A₁) ⊙ Φ(A₂) ⊙ … ⊙ Φ(A_k) ← 若 ⊙ 是 ⊗，輸出端也要組裝
/// ```
///
/// 關鍵觀察（命題 202-3）：組裝一段區間的代價**只取決於該區間的維數積**，
/// 與它內部怎麼切無關 —— 因為 p×p 與 q×q 的 Kronecker 積恰需 (pq)² 次乘法。
/// 於是
/// ```text
///   cost(樹) = Σ_{內部節點 v} (Π_{i ∈ v} nᵢ)²
/// ```
/// 這是一個**區間動態規劃**（與矩陣鏈乘法同型但成本函數不同）：
/// ```text
///   C(i,j) = P(i,j)² + min_{i ≤ t < j} [ C(i,t) + C(t+1,j) ]
/// ```
///
/// ## 本條的負面結果（最值得記住的一段）
///
/// 對**矩陣值** Φ（inv、sq、cube、tr̃ans），分解路徑的輸出端仍要組一條
/// 同樣維數的 Kronecker 鏈。組裝項在兩條路徑上**完全相同**，於是它
/// 不會被分解消掉，反而成為增益的天花板：
/// ```text
///   增益 = (組裝 + κN³) / (組裝 + κΣnᵢ³) ≤ (組裝 + κN³) / 組裝 ≈ Θ(N)
/// ```
/// 而 N-03 當初宣告的漸近增益是 Θ(N³/Σnᵢ³) —— 那是**忽略組裝**得到的數字。
///
/// 對**純量值** Φ（det、trace、rank）則沒有這個天花板：分解路徑根本不組鏈。
/// 換句話說，「最佳結合順序」這個問題對純量值 Φ **根本不存在** ——
/// 這是分解帶來的第二層節省，過去沒有被計量過。

///|
/// 結合樹。葉為因子索引。
pub enum AssocTree {
  ALeaf(Int)
  ANode(AssocTree, AssocTree)
}

///|
/// 子樹涵蓋之維數積
pub fn AssocTree::aprod(self : AssocTree, dims : Array[Int]) -> Int64 {
  match self {
    ALeaf(i) => dims[i].to_int64()
    ANode(l, r) => l.aprod(dims) * r.aprod(dims)
  }
}

///|
/// 【算式】組裝成本之符號預測：Σ 內部節點 (區間維數積)²。
///
/// 此式不執行任何矩陣運算，只看樹的形狀與維數向量。
/// 命題 202-1 要求它與實測之**有理數乘法次數**（Cost.qmul）逐位相等。
///
/// ⚠️ 單位要對：第一次把它拿去對 `Cost.wmul` 差了六倍（180 vs 1111），
/// 因為 wmul 隨運算元位寬加權、量的是真實代價，而符號模型只看樹的形狀、
/// 量的是元素級乘法次數。這不是模型錯，是把兩種粒度混用。
pub fn AssocTree::acost(self : AssocTree, dims : Array[Int]) -> Int64 {
  match self {
    ALeaf(_) => 0L
    ANode(l, r) => {
      let pl = l.aprod(dims)
      let pr = r.aprod(dims)
      l.acost(dims) + r.acost(dims) + pl * pl * pr * pr
    }
  }
}

///|
/// 樹之括號寫法
pub fn AssocTree::alabel(self : AssocTree) -> String {
  match self {
    ALeaf(i) => i.to_string()
    ANode(l, r) => "(" + l.alabel() + "⊗" + r.alabel() + ")"
  }
}

///|
/// 內部節點數（= k − 1，用於檢查樹之良構）
pub fn AssocTree::anodes(self : AssocTree) -> Int {
  match self {
    ALeaf(_) => 0
    ANode(l, r) => 1 + l.anodes() + r.anodes()
  }
}

///|
/// 左結合 ((A₁⊗A₂)⊗A₃)⊗…
pub fn assoc_left(k : Int) -> AssocTree {
  let mut t : AssocTree = ALeaf(0)
  for i in 1..<k {
    t = ANode(t, ALeaf(i))
  }
  t
}

///|
/// 右結合 A₁⊗(A₂⊗(A₃⊗…))
pub fn assoc_right(k : Int) -> AssocTree {
  let mut t : AssocTree = ALeaf(k - 1)
  for j in 0..<(k - 1) {
    t = ANode(ALeaf(k - 2 - j), t)
  }
  t
}

///|
/// 平衡樹（對半切）
pub fn assoc_balanced(k : Int) -> AssocTree {
  assoc_bal_rec(0, k)
}

///|
fn assoc_bal_rec(lo : Int, hi : Int) -> AssocTree {
  if hi - lo <= 1 {
    ALeaf(lo)
  } else {
    let mid = (lo + hi) / 2
    ANode(assoc_bal_rec(lo, mid), assoc_bal_rec(mid, hi))
  }
}

///|
/// 貪婪：每次合併**當下最便宜的相鄰對**。
///
/// 這是最自然的啟發式，而命題 202-4 證明它會輸 —— 本條保留它正是為了
/// 展示「局部最便宜」與「整體最便宜」在此問題上確實分岔。
pub fn assoc_greedy(dims : Array[Int]) -> AssocTree {
  let k = dims.length()
  if k == 1 {
    return ALeaf(0)
  }
  let ts : Array[AssocTree] = []
  let ps : Array[Int64] = []
  for i in 0..<k {
    ts.push(ALeaf(i))
    ps.push(dims[i].to_int64())
  }
  while ts.length() > 1 {
    let mut best = 0
    let mut bestc = -1L
    for i in 0..<(ts.length() - 1) {
      let c = ps[i] * ps[i] * ps[i + 1] * ps[i + 1]
      if bestc < 0L || c < bestc {
        bestc = c
        best = i
      }
    }
    let merged = ANode(ts[best], ts[best + 1])
    let mp = ps[best] * ps[best + 1]
    let nts : Array[AssocTree] = []
    let nps : Array[Int64] = []
    for i in 0..<ts.length() {
      if i == best {
        nts.push(merged)
        nps.push(mp)
      } else if i == best + 1 {
        continue
      } else {
        nts.push(ts[i])
        nps.push(ps[i])
      }
    }
    ts.clear()
    ps.clear()
    for t in nts {
      ts.push(t)
    }
    for p in nps {
      ps.push(p)
    }
  }
  ts[0]
}

///|
/// 【演算法 202】最佳結合順序之區間動態規劃。
///
/// C(i,j) = P(i,j)² + min_{i ≤ t < j} [ C(i,t) + C(t+1,j) ]
///
/// 時間 Θ(k³)、空間 Θ(k²)。注意 P(i,j)² 這一項**與切點無關**，
/// 這正是本問題與矩陣鏈乘法的差別：那裡的合併代價是 pᵢ·p_t·p_j，
/// 隨切點而變；這裡只隨區間而變。於是 DP 其實是在選「哪些區間會出現」。
pub fn assoc_dp(dims : Array[Int]) -> (Int64, AssocTree) {
  let k = dims.length()
  if k == 1 {
    return (0L, ALeaf(0))
  }
  // pre[i][j] = Π dims[i..j]
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
      let p = pre[i][j]
      let mut bc = -1L
      let mut bt : AssocTree = ALeaf(i)
      for t in i..<j {
        let c = best[i][t] + best[t + 1][j]
        if bc < 0L || c < bc {
          bc = c
          bt = ANode(tree[i][t], tree[t + 1][j])
        }
      }
      best[i][j] = bc + p * p
      tree[i][j] = bt
    }
  }
  (best[0][k - 1], tree[0][k - 1])
}

// ---------------------------------------------------------------------------
// k 元鏈之組裝與 k 元規則
// ---------------------------------------------------------------------------

///|
/// 依結合樹組裝 k 元鏈。
///
/// ⊗ 走 `qkron_cost`（計費）；⊕ 與 ⊞ 走註冊表之組合子（不計費，
/// 因為分塊置放與 Kronecker 和在本庫的成本模型裡不花字乘法）。
///
/// ⚠️ 與二元裁決器的約定差異，必須講明：`check_law_samples` 在直接路徑上
/// **不**計 C(A,B) 的組裝成本（它呼叫 `direct(comb(a,b), cd)`，comb 在
/// Cost 之外），卻計入分解路徑的 `qkron_cost`。那是偏袒直接路徑的保守約定。
/// 本條改為兩邊都計 —— 因為 k 元的重點正是組裝順序，不計就沒得談。
/// 方向上這會**降低**所測增益，不會灌水。
pub fn chain_build(
  comb : String,
  t : AssocTree,
  parts : Array[Mat[Q]],
  c : Cost,
) -> Mat[Q] {
  match t {
    ALeaf(i) => parts[i]
    ANode(l, r) => {
      let a = chain_build(comb, l, parts, c)
      let b = chain_build(comb, r, parts, c)
      if comb == "⊗" {
        qkron_cost(c, a, b)
      } else if comb == "⊕" {
        qblock_diag(a, b)
      } else {
        qkron_sum(a, b)
      }
    }
  }
}

///|
/// k 元合成規則：引數為 (Φx, Φy, dim x 之源, dim y 之源, det x 之源, det y 之源, cost)。
///
/// 與二元註冊表的差別只有一個：維數與行列式以**數值**傳入，而不是靠
/// 重新物化運算元去讀 `.mrows`。這是 k 元化的必要條件 —— 鏈的中間結果
/// 不應該被物化，否則分解就失去意義。命題 202-2 驗證兩者在 k = 2 時
/// 給出**逐元相同**的矩陣。
pub fn krule_registry() -> Array[
  (String, (Mat[Q], Mat[Q], Int, Int, Q, Q, Cost) -> Mat[Q]?),
] {
  [
    ("⊗", (x, y, _n, _m, _dx, _dy, c) => Some(qkron_cost(c, x, y))),
    ("⊕", (x, y, _n, _m, _dx, _dy, _c) => Some(qblock_diag(x, y))),
    (
      "⊗ₛ",
      (x, y, n, m, dx, dy, c) => {
        let s = cq_mul(c, qpow_cost(c, dx, m - 1), qpow_cost(c, dy, n - 1))
        Some(qsmul_cost(c, s, qkron_cost(c, x, y)))
      },
    ),
    (
      "·",
      (x, y, _n, _m, _dx, _dy, c) => {
        Some(q_scalar_mat(cq_mul(c, x.data[0], y.data[0])))
      },
    ),
    (
      "+",
      (x, y, _n, _m, _dx, _dy, c) => {
        Some(q_scalar_mat(cq_add(c, x.data[0], y.data[0])))
      },
    ),
    (
      "^",
      (x, y, n, m, _dx, _dy, c) => {
        Some(
          q_scalar_mat(
            cq_mul(c, qpow_cost(c, x.data[0], m), qpow_cost(c, y.data[0], n)),
          ),
        )
      },
    ),
  ]
}

///|
/// 依名取 K 群（加速層）之律函式。
pub fn krule_by_name(
  name : String,
) -> ((Mat[Q], Mat[Q], Int, Int, Q, Q, Cost) -> Mat[Q]?)? {
  for p in krule_registry() {
    let (n, f) = p
    if n == name {
      return Some(f)
    }
  }
  None
}

///|
/// 只有 ⊗ₛ 需要運算元的行列式。其餘規則不需要，就不該為它付錢。
pub fn krule_needs_det(name : String) -> Bool {
  name == "⊗ₛ"
}

///|
/// 依結合樹摺疊 k 元規則。回傳 (Φ 值, 該子樹之維數, 該子樹之行列式)。
pub fn fold_krule(
  comb : String,
  rule : (Mat[Q], Mat[Q], Int, Int, Q, Q, Cost) -> Mat[Q]?,
  need_det : Bool,
  t : AssocTree,
  phis : Array[Mat[Q]?],
  parts : Array[Mat[Q]],
  c : Cost,
) -> (Mat[Q]?, Int, Q) {
  match t {
    ALeaf(i) =>
      (
        phis[i],
        parts[i].mrows,
        if need_det {
          qdet_gauss(parts[i], c)
        } else {
          Q::one()
        },
      )
    ANode(l, r) => {
      let (xl, nl, dl) = fold_krule(comb, rule, need_det, l, phis, parts, c)
      let (xr, nr, dr) = fold_krule(comb, rule, need_det, r, phis, parts, c)
      let n = if comb == "⊕" { nl + nr } else { nl * nr }
      let d = if need_det {
        if comb == "⊗" {
          cq_mul(c, qpow_fast(c, dl, nr), qpow_fast(c, dr, nl))
        } else {
          cq_mul(c, dl, dr)
        }
      } else {
        Q::one()
      }
      match (xl, xr) {
        (Some(a), Some(b)) => (rule(a, b, nl, nr, dl, dr, c), n, d)
        _ => (None, n, d)
      }
    }
  }
}

///|
/// k 元裁決之結果
pub struct KVerdict {
  /// 是否成立
  kholds : Bool
  /// 直接路徑字乘法（含鏈組裝）
  kbase : Int64
  /// 分解路徑字乘法（含輸出端組裝）
  kfast : Int64
  /// 直接路徑中「純組裝」所佔之字乘法 —— 增益天花板之來源
  kasm : Int64
  /// 直接路徑組裝之有理數乘法次數（與 acost 之符號預測對帳用）
  kqasm : Int64
  /// 分解路徑之有理數乘法次數 —— 用來看輸出端是否仍要組一條同樣的鏈
  kqfast : Int64
}

///|
/// 律之實測增益 = 基礎成本 ÷ 加速成本。
pub fn KVerdict::kgain(self : KVerdict) -> Double {
  if self.kfast <= 0L {
    0.0
  } else {
    self.kbase.to_double() / self.kfast.to_double()
  }
}

///|
/// 【演算法】k 元律之裁決器。
///
/// k = 2 時與 `check_law_samples` 的單一樣本完全同義（命題 202-2 以逐元
/// 比對驗證），k > 2 時給出二元裁決器表達不出的東西。
pub fn check_law_k(
  phi : String,
  comb : String,
  rule : String,
  parts : Array[Mat[Q]],
  tree : AssocTree,
) -> KVerdict? {
  let pf = phi_by_name(phi)
  let rf = krule_by_name(rule)
  match (pf, rf) {
    (Some(f), Some(r)) => {
      let dims : Array[Int] = []
      for p in parts {
        dims.push(p.mrows)
      }
      // 直接路徑：組鏈（計費）再施以 Φ
      let cd = Cost::new()
      let g = chain_build(comb, tree, parts, cd)
      let asmcost = cd.wmul
      let qasm = cd.qmul
      let lhs = f(g, cd)
      // 分解路徑：各別施以 Φ，再依同一棵樹摺疊規則
      let cf = Cost::new()
      let phis : Array[Mat[Q]?] = []
      for p in parts {
        phis.push(f(p, cf))
      }
      let (rhs, _n, _d) = fold_krule(
        comb,
        r,
        krule_needs_det(rule),
        tree,
        phis,
        parts,
        cf,
      )
      let holds = match (lhs, rhs) {
        (Some(x), Some(y)) => x.equals(y)
        (None, None) => true
        _ => false
      }
      Some({
        kholds: holds,
        kbase: cd.wmul,
        kfast: cf.wmul,
        kasm: asmcost,
        kqasm: qasm,
        kqfast: cf.qmul,
      })
    }
    _ => None
  }
}

///|
/// 一條 k 元律之掃描結果
pub struct KLaw {
  kname : String
  kk : Int
  kverd : Bool
  kg : Double
  kasmfrac : Double
}

///|
/// 【演算法】k 元定律掃描：固定一組因子，對 (Φ, ⊙) 全掃。
///
/// 只掃 C = ⊗ —— ⊕ 的 k 元鏈是分塊對角，組裝零成本，結合順序無意義；
/// ⊞ 的 k 元鏈需要另一套成本模型（Σ 與 ⊗ 混用），本輪不處理。
/// 不處理的理由寫在這裡，而不是讓它悄悄缺席。
pub fn klaw_scan(dims : Array[Int], rng : Rng, tree : AssocTree) -> Array[KLaw] {
  let parts : Array[Mat[Q]] = []
  for d in dims {
    parts.push(rand_gram(rng, d))
  }
  let out : Array[KLaw] = []
  let pairs : Array[(String, String)] = [
    ("inv", "⊗"),
    ("sq", "⊗"),
    ("cube", "⊗"),
    ("tr̃ans", "⊗"),
    ("adj", "⊗ₛ"),
    ("det", "^"),
    ("trace", "·"),
    ("rank", "·"),
  ]
  for pr in pairs {
    let (ph, rl) = pr
    match check_law_k(ph, "⊗", rl, parts, tree) {
      Some(v) =>
        out.push({
          kname: ph + " / ⊗^" + dims.length().to_string() + " / " + rl,
          kk: dims.length(),
          kverd: v.kholds,
          kg: v.kgain(),
          kasmfrac: if v.kbase <= 0L {
            0.0
          } else {
            v.kasm.to_double() / v.kbase.to_double()
          },
        })
      None => ()
    }
  }
  out
}

///|
/// k = 2 退化性檢查（命題 202-2）。
///
/// 對定律表的全部 72 個候選，逐一比較二元路徑與 k 元路徑的**輸出矩陣**
/// （不是只比裁決 —— 裁決相同可能只是兩邊同樣錯）。回傳不一致的條數。
pub fn karity_degenerate_diff(
  samples : Array[(Int, Int, (Rng, Int) -> Mat[Q])],
) -> Int {
  let mut bad = 0
  let combs = comb_registry()
  let groups : Array[
    (
      Array[(String, (Mat[Q], Cost) -> Mat[Q]?)],
      Array[(String, (Mat[Q], Mat[Q], Mat[Q], Mat[Q], Cost) -> Mat[Q]?)],
    ),
  ] = [
    (phi_mat_registry(), rule_mat_registry()),
    (phi_sca_registry(), rule_sca_registry()),
  ]
  for grp in groups {
    let (phis, rules) = grp
    for ph in phis {
      let (pname, phi) = ph
      for cb in combs {
        let (cname, comb) = cb
        for rl in rules {
          let (rname, rule) = rl
          let rng = comp_rng_of(pname, "k2", cname, rname)
          for sm in samples {
            let (n, m, sampler) = sm
            let a = sampler(rng, n)
            let b = sampler(rng, m)
            // 二元路徑
            let c1 = Cost::new()
            let bin_l = phi(comb(a, b), c1)
            let bin_r = match (phi(a, c1), phi(b, c1)) {
              (Some(x), Some(y)) => rule(x, y, a, b, c1)
              _ => None
            }
            // k 元路徑（k = 2，樹只有一個內部節點）
            let c2 = Cost::new()
            let kv = check_law_k(
              pname,
              cname,
              rname,
              [a, b],
              ANode(ALeaf(0), ALeaf(1)),
            )
            ignore(c2)
            let bin_holds = match (bin_l, bin_r) {
              (Some(x), Some(y)) => x.equals(y)
              (None, None) => true
              _ => false
            }
            match kv {
              Some(v) => if v.kholds != bin_holds { bad = bad + 1 }
              None => bad = bad + 1
            }
          }
        }
      }
    }
  }
  bad
}

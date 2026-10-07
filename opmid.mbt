///|
/// # N-66 N-40 接中端：讓規則合成器供應中端的規則
///
/// ## 中端原本只會重寫空間
///
/// N-53 的重寫系統處理的是 `SpaceExpr` —— 它把 `(A⊗B)*` 改寫成 `A*⊗B*`，
/// 把 `T[T[A,M],N]` 融合成 `T[A,MN]`。十條類 A 規則**全部是手寫的**。
///
/// 而 N-40 的規則合成器產出的是另一種東西：
///
/// ```text
///   Φ(A ⊗ B) = (det A)^{p(n,m)} · (det B)^{q(n,m)} · (Φ(A) ⊗ Φ(B))
/// ```
///
/// 這不是空間層的重寫，是**算子層**的重寫 —— 它說的是「對組合空間做 Φ」
/// 可以拆成「分別做 Φ 再組合」。中端一直沒有這一層，於是 N-40 找到的規則
/// 只能被 N-45 包成義務，進不了求值管線。
///
/// ## 本條補的東西：類 C 規則與 Φ 樹
///
/// ```text
///   OpLeaf(Φ, 葉)        直接算 Φ(G(葉))
///   OpKron(l, r, p, q)   Φ(A⊗B) → (det A)^p (det B)^q · (Φ(A) ⊗ Φ(B))
///   OpSum(l, r)          Φ(A⊕B) → Φ(A) ⊕ Φ(B)
/// ```
///
/// **指數 (p, q) 不是人填的，是 `synth_rule_kron` 在執行期量出來的。**
/// 這正是「N-40 接中端」的實質內容：中端的規則表第一次有一部分不是手寫的。

///|
/// 算子層之重寫結果。
pub enum OpTree {
  OpLeaf(SpaceExpr)
  OpKron(OpTree, OpTree, Int, Int)
  OpSum(OpTree, OpTree)
}

///|
/// 標籤（用於比對與除錯）。
pub fn OpTree::oplabel(self : OpTree) -> String {
  match self {
    OpLeaf(e) => e.slabel()
    OpKron(l, r, p, q) =>
      "(" +
      l.oplabel() +
      "⊗" +
      r.oplabel() +
      ")·d^" +
      p.to_string() +
      "," +
      q.to_string()
    OpSum(l, r) => "(" + l.oplabel() + "⊕" + r.oplabel() + ")"
  }
}

///|
/// 把 Φ(e) 重寫成 Φ 樹。⊗ 用合成器給的 (p, q)，⊕ 用區塊對角。
/// 其餘節點不拆（當成葉）。
pub fn op_rewrite(e : SpaceExpr, r : SynthRule) -> OpTree {
  match e {
    STensor(a, b) => {
      let n = a.sdim()
      let m = b.sdim()
      let p = r.sp0 + r.sp1 * n + r.sp2 * m
      let q = r.sq0 + r.sq1 * n + r.sq2 * m
      OpKron(op_rewrite(a, r), op_rewrite(b, r), p, q)
    }
    SSum(a, b) => OpSum(op_rewrite(a, r), op_rewrite(b, r))
    _ => OpLeaf(e)
  }
}

///|
/// 求值 Φ 樹。
pub fn op_eval(
  t : OpTree,
  phi : (Mat[Q], Cost) -> Mat[Q]?,
  c : Cost,
) -> Mat[Q]? {
  match t {
    OpLeaf(e) => phi(e.sgram_cost(c), c)
    OpSum(l, r) =>
      match (op_eval(l, phi, c), op_eval(r, phi, c)) {
        (Some(x), Some(y)) => Some(qblock_diag(x, y))
        _ => None
      }
    OpKron(l, r, p, q) =>
      match (op_eval(l, phi, c), op_eval(r, phi, c)) {
        (Some(x), Some(y)) => {
          let k = qkron_cost(c, x, y)
          if p == 0 && q == 0 {
            Some(k)
          } else {
            let da = qdet_gauss(op_gram(l, c), c)
            let db = qdet_gauss(op_gram(r, c), c)
            let s = cq_mul(c, qpow_fast(c, da, p), qpow_fast(c, db, q))
            Some(qsmul_cost(c, s, k))
          }
        }
        _ => None
      }
  }
}

///|
/// Φ 樹對應之底空間 Gram（修正項要用到 det）。
fn op_gram(t : OpTree, c : Cost) -> Mat[Q] {
  match t {
    OpLeaf(e) => e.sgram_cost(c)
    OpSum(l, r) => qblock_diag(op_gram(l, c), op_gram(r, c))
    OpKron(l, r, _, _) => qkron_cost(c, op_gram(l, c), op_gram(r, c))
  }
}

///|
/// 直接路徑：物化 G(e) 再施加 Φ。
pub fn op_direct(
  e : SpaceExpr,
  phi : (Mat[Q], Cost) -> Mat[Q]?,
  c : Cost,
) -> Mat[Q]? {
  phi(e.sgram_cost(c), c)
}

///|
/// 一條算子層規則之量測：(兩路逐元相同?, 直接成本, 重寫後成本)。
pub fn op_compare(
  e : SpaceExpr,
  phi : (Mat[Q], Cost) -> Mat[Q]?,
  r : SynthRule,
) -> (Bool, Int64, Int64) {
  let c1 = Cost::new()
  let d = op_direct(e, phi, c1)
  let c2 = Cost::new()
  let s = op_eval(op_rewrite(e, r), phi, c2)
  let same = match (d, s) {
    (Some(x), Some(y)) => x.equals(y)
    (None, None) => true
    _ => false
  }
  (same, c1.wmul, c2.wmul)
}

///|
/// 算子層語料：只含 ⊗ 與 ⊕ 的樹（這是類 C 規則覆蓋的範圍）。
pub fn op_corpus(rng : Rng) -> Array[SpaceExpr] {
  fn leaf(nm : String, d : Int) -> SpaceExpr {
    SLeaf(nm, rand_gram(rng, d))
  }

  [
    STensor(leaf("A", 2), leaf("B", 3)),
    STensor(leaf("C", 3), leaf("D", 3)),
    STensor(leaf("E", 2), STensor(leaf("F", 2), leaf("G", 3))),
    SSum(STensor(leaf("H", 2), leaf("I", 3)), leaf("J", 3)),
    STensor(SSum(leaf("K", 2), leaf("L", 2)), leaf("M", 3)),
    STensor(leaf("N", 4), leaf("O", 2)),
    SSum(
      STensor(leaf("P", 2), leaf("Q", 2)),
      STensor(leaf("R", 2), leaf("S", 2)),
    ),
    STensor(STensor(leaf("T", 2), leaf("U", 2)), leaf("V", 2)),
  ]
}

///|
/// 掃描：對每個矩陣值 Φ 先用 N-40 合成規則，再把規則接進中端求值。
///
/// 回傳 (Φ 個數, 合成成功數, 語料數, 逐元相同數, 直接總成本, 重寫總成本,
///        重寫較便宜之 (Φ, 式) 數)。
pub fn op_scan(rng : Rng) -> (Int, Int, Int, Int, Int64, Int64, Int) {
  let phis = phi_mat_registry()
  let corpus = op_corpus(rng)
  let mut synth = 0
  let mut same = 0
  let mut td = 0L
  let mut ts = 0L
  let mut win = 0
  for pr in phis {
    let (_, phi) = pr
    match synth_rule_kron(phi, rng) {
      None => ()
      Some(r) => {
        synth = synth + 1
        for e in corpus {
          let (ok, a, b) = op_compare(e, phi, r)
          if ok {
            same = same + 1
          }
          td = td + a
          ts = ts + b
          if b < a {
            win = win + 1
          }
        }
      }
    }
  }
  (phis.length(), synth, corpus.length(), same, td, ts, win)
}

///|
/// 合成出來的指數表（供報表與義務逐條比對）。
pub fn op_rule_table(rng : Rng) -> Array[(String, String)] {
  let out : Array[(String, String)] = []
  for pr in phi_mat_registry() {
    let (nm, phi) = pr
    match synth_rule_kron(phi, rng) {
      None => out.push((nm, "—"))
      Some(r) => out.push((nm, r.describe()))
    }
  }
  out
}

///|
/// 兩側對照：把合成出來的指數動一格，恆等式必須垮掉。
///
/// 回傳 (檢查的 Φ 數, 被推翻的 Φ 數)。
pub fn op_control(rng : Rng) -> (Int, Int) {
  let corpus = op_corpus(rng)
  let mut tot = 0
  let mut broken = 0
  for pr in phi_mat_registry() {
    let (_, phi) = pr
    match synth_rule_kron(phi, rng) {
      None => ()
      Some(r) => {
        tot = tot + 1
        let bad = {
          sp0: r.sp0 + 1,
          sp1: r.sp1,
          sp2: r.sp2,
          sq0: r.sq0,
          sq1: r.sq1,
          sq2: r.sq2,
        }
        let mut anyfail = false
        for e in corpus {
          let (ok, _, _) = op_compare(e, phi, bad)
          if !ok {
            anyfail = true
          }
        }
        if anyfail {
          broken = broken + 1
        }
      }
    }
  }
  (tot, broken)
}

///|
/// 中端的規則表裡有多少是機器供應的。
/// 回傳 (類 A 手寫規則數, 類 B 手寫規則數, 類 C 機器合成規則數)。
pub fn op_rule_provenance(rng : Rng) -> (Int, Int, Int) {
  let mut c = 0
  for pr in phi_mat_registry() {
    let (_, phi) = pr
    if synth_rule_kron(phi, rng) is Some(_) {
      c = c + 1
    }
  }
  (rw_registry_a().length(), rw_registry_b().length(), c)
}

///|
/// 指紋。
pub fn op_digest(rng : Rng) -> String {
  let (np, ns, nc, same, td, ts, win) = op_scan(rng)
  np.to_string() +
  ":" +
  ns.to_string() +
  ":" +
  nc.to_string() +
  ":" +
  same.to_string() +
  ":" +
  td.to_string() +
  ":" +
  ts.to_string() +
  ":" +
  win.to_string()
}

///|
/// ## 守門：手寫的那條規則才是錯的
///
/// 第一次把 N-40 接上中端時，40 個 (Φ, 式) 組合有 **3 個對不上**。
/// 出問題的不是機器合成的 ⊗ 規則，是**手寫的 ⊕ 規則**：
///
/// ```text
///   adj(A ⊕ B) = det(B)·adj(A) ⊕ det(A)·adj(B)      ≠ adj(A) ⊕ adj(B)
/// ```
///
/// 區塊對角看起來太像恆等式，以致於它被當成「對所有 Φ 都成立」寫死在規則裡。
/// 修法不是去補一條 adj 專用的 ⊕ 規則，而是**加一道守門**：
/// 對每個 Φ 先在小實例上測 Φ(A⊕B) = Φ(A)⊕Φ(B) 是否成立，不成立就不拆 ⊕。
/// 守門本身也是量出來的，不是人判斷的。
pub fn op_sum_valid(phi : (Mat[Q], Cost) -> Mat[Q]?, rng : Rng) -> Bool {
  for t in 0..<4 {
    let a = rand_gram(rng, 2 + t % 2)
    let b = rand_gram(rng, 2 + (t + 1) % 2)
    let c = Cost::new()
    let lhs = phi(qblock_diag(a, b), c)
    let rhs = match (phi(a, c), phi(b, c)) {
      (Some(x), Some(y)) => Some(qblock_diag(x, y))
      _ => None
    }
    let same = match (lhs, rhs) {
      (Some(x), Some(y)) => x.equals(y)
      (None, None) => true
      _ => false
    }
    if !same {
      return false
    }
  }
  true
}

///|
/// 帶守門的重寫：⊕ 只在守門通過時才拆。
pub fn op_rewrite_gated(e : SpaceExpr, r : SynthRule, sumok : Bool) -> OpTree {
  match e {
    STensor(a, b) => {
      let n = a.sdim()
      let m = b.sdim()
      let p = r.sp0 + r.sp1 * n + r.sp2 * m
      let q = r.sq0 + r.sq1 * n + r.sq2 * m
      OpKron(op_rewrite_gated(a, r, sumok), op_rewrite_gated(b, r, sumok), p, q)
    }
    SSum(a, b) =>
      if sumok {
        OpSum(op_rewrite_gated(a, r, sumok), op_rewrite_gated(b, r, sumok))
      } else {
        OpLeaf(e)
      }
    _ => OpLeaf(e)
  }
}

///|
/// 帶守門的量測。
pub fn op_compare_gated(
  e : SpaceExpr,
  phi : (Mat[Q], Cost) -> Mat[Q]?,
  r : SynthRule,
  sumok : Bool,
) -> (Bool, Int64, Int64) {
  let c1 = Cost::new()
  let d = op_direct(e, phi, c1)
  let c2 = Cost::new()
  let s = op_eval(op_rewrite_gated(e, r, sumok), phi, c2)
  let same = match (d, s) {
    (Some(x), Some(y)) => x.equals(y)
    (None, None) => true
    _ => false
  }
  (same, c1.wmul, c2.wmul)
}

///|
/// 帶守門的掃描。
///
/// 回傳 (Φ 數, 合成成功數, ⊕ 守門通過之 Φ 數, (Φ,式) 組合數, 逐元相同數,
///        直接總成本, 重寫總成本, 重寫較便宜數)。
pub fn op_scan_gated(rng : Rng) -> (Int, Int, Int, Int, Int, Int64, Int64, Int) {
  let phis = phi_mat_registry()
  let corpus = op_corpus(rng)
  let mut synth = 0
  let mut gated = 0
  let mut pairs = 0
  let mut same = 0
  let mut td = 0L
  let mut ts = 0L
  let mut win = 0
  for pr in phis {
    let (_, phi) = pr
    match synth_rule_kron(phi, rng) {
      None => ()
      Some(r) => {
        synth = synth + 1
        let sumok = op_sum_valid(phi, rng)
        if sumok {
          gated = gated + 1
        }
        for e in corpus {
          let (ok, a, b) = op_compare_gated(e, phi, r, sumok)
          pairs = pairs + 1
          if ok {
            same = same + 1
          }
          td = td + a
          ts = ts + b
          if b < a {
            win = win + 1
          }
        }
      }
    }
  }
  (phis.length(), synth, gated, pairs, same, td, ts, win)
}

///|
/// 守門逐 Φ 的結果（供報表）。
pub fn op_gate_table(rng : Rng) -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  for pr in phi_mat_registry() {
    let (nm, phi) = pr
    out.push((nm, op_sum_valid(phi, rng)))
  }
  out
}

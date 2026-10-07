///|
/// # 第八輪中端：類 B 進主流程，結合順序交給 DP
///
/// ## 兩個一直掛著的洞
///
/// 1. **類 B 不在主流程裡。** `rw_registry_b()` 寫好了（⊕ 與 ⊗ 的交換律正規序），
///    `canonicalize` 也接了，但沒有任何下游用它 —— 因為交換律**不保 Gram
///    逐元相同**，只保到一個置換相似。`rw_sound_b` 於是只驗 det 與 trace，
///    而派工路徑（N-54）與 ℝ 軌（N-55）都要求逐元相同，用不了。
///
/// 2. **範式的結合順序是約定而非最佳化。** A10「右結合正規序」只搬括號，
///    它存在的理由是合流，不是成本 —— N-53 唯一一式變貴的就是它。
///
/// 兩個洞的解法其實是同一句話：**把被丟掉的資訊帶上**。
/// 類 B 丟掉的是置換，帶上它就能逐元驗證、也能在求解後還原；
/// A10 丟掉的是成本，接上 N-41 的區間 DP 就能把它選對。

// ---------------------------------------------------------------------------
//  一、類 B 帶著置換走
// ---------------------------------------------------------------------------

///|
/// 置換之語意約定（全檔一致）：
///
/// ```text
///   p 滿足   G(canon)[u][v] = G(原式)[p[u]][p[v]]
/// ```
///
/// 等價地 G(canon) = Pᵀ·G(原式)·P，其中 P[p[u]][u] = 1。
pub fn perm_ident(n : Int) -> Array[Int] {
  Array::makei(n, i => i)
}

///|
/// 由置換造矩陣 P（P[p[u]][u] = 1）。
pub fn perm_mat(p : Array[Int]) -> Mat[Q] {
  let n = p.length()
  Mat::build(n, n, (i, u) => if i == p[u] { Q::one() } else { Q::zero() })
}

///|
/// 依置換重排矩陣之列：(Pᵀ·M)[u][j] = M[p[u]][j]。
pub fn perm_rows(p : Array[Int], m : Mat[Q]) -> Mat[Q] {
  Mat::build(p.length(), m.mcols, (u, j) => m.at(p[u], j))
}

///|
/// 還原：由 canon 空間之解回到原式之解，X[p[u]][j] = Y[u][j]。
pub fn perm_unrows(p : Array[Int], y : Mat[Q]) -> Mat[Q] {
  let n = p.length()
  let out = Mat::build(n, y.mcols, (_i, _j) => Q::zero())
  for u in 0..<n {
    for j in 0..<y.mcols {
      out.put(p[u], j, y.at(u, j))
    }
  }
  out
}

///|
/// 類 A + 類 B 的規範化，**帶著置換見證**。
///
/// 遞迴進 ⊗ / ⊕ / ⊞ / 對偶；扭曲與子空間會把子樹的置換**吸收進它們自己的
/// 矩陣**（M' = PᵀM 使 M'ᵀG(ca)M' = MᵀG(a)M），故這兩個節點對外輸出恆等置換。
/// 外冪不遞迴（k-子集的誘導置換另案處理），視為原子。
pub fn canon_perm(e : SpaceExpr) -> (SpaceExpr, Array[Int]) {
  match e {
    SLeaf(_, g) => (e, perm_ident(g.mrows))
    SDual(a) => {
      let (ca, pa) = canon_perm(a)
      // G(A*) = G(A)⁻¹；置換相似在求逆下不變，故置換原樣傳出
      (SDual(ca), pa)
    }
    STensor(a, b) => {
      let (ca, pa) = canon_perm(a)
      let (cb, pb) = canon_perm(b)
      let na = pa.length()
      let nb = pb.length()
      if ca.slabel() > cb.slabel() {
        // 交換：結果索引 u = j·na + i 對應原索引 pa[i]·nb + pb[j]
        let p = Array::makei(na * nb, u => pa[u % na] * nb + pb[u / na])
        (STensor(cb, ca), p)
      } else {
        let p = Array::makei(na * nb, u => pa[u / nb] * nb + pb[u % nb])
        (STensor(ca, cb), p)
      }
    }
    SKSum(a, b) => {
      let (ca, pa) = canon_perm(a)
      let (cb, pb) = canon_perm(b)
      let na = pa.length()
      let nb = pb.length()
      if ca.slabel() > cb.slabel() {
        let p = Array::makei(na * nb, u => pa[u % na] * nb + pb[u / na])
        (SKSum(cb, ca), p)
      } else {
        let p = Array::makei(na * nb, u => pa[u / nb] * nb + pb[u % nb])
        (SKSum(ca, cb), p)
      }
    }
    SSum(a, b) => {
      let (ca, pa) = canon_perm(a)
      let (cb, pb) = canon_perm(b)
      let na = pa.length()
      let nb = pb.length()
      if ca.slabel() > cb.slabel() {
        let p = Array::makei(na + nb, u => {
          if u < nb {
            na + pb[u]
          } else {
            pa[u - nb]
          }
        })
        (SSum(cb, ca), p)
      } else {
        let p = Array::makei(na + nb, u => {
          if u < na {
            pa[u]
          } else {
            na + pb[u - na]
          }
        })
        (SSum(ca, cb), p)
      }
    }
    STwist(a, m) => {
      let (ca, pa) = canon_perm(a)
      (STwist(ca, perm_rows(pa, m)), perm_ident(m.mcols))
    }
    SSub(a, s) => {
      let (ca, pa) = canon_perm(a)
      (SSub(ca, perm_rows(pa, s)), perm_ident(s.mcols))
    }
    SExt(_, _) => (e, perm_ident(e.sdim()))
  }
}

///|
/// 類 B 之**逐元**健全性（比 `rw_sound_b` 的 det+trace 強得多）：
/// G(canon)[u][v] = G(原式)[p[u]][p[v]] 對每一對 (u,v) 成立。
pub fn canon_sound(e : SpaceExpr) -> Bool {
  let (c, p) = canon_perm(e)
  if c.sdim() != e.sdim() {
    return false
  }
  let g = e.sgram()
  let h = c.sgram()
  let n = h.mrows
  if p.length() != n {
    return false
  }
  for u in 0..<n {
    for v in 0..<n {
      if !h.at(u, v).eq(g.at(p[u], p[v])) {
        return false
      }
    }
  }
  true
}

///|
/// 規範化之冪等性與合流性（標籤層級）。
pub fn canon_stable(e : SpaceExpr) -> Bool {
  let (c, _) = canon_perm(e)
  let (c2, p2) = canon_perm(c)
  if c2.slabel() != c.slabel() {
    return false
  }
  // 已規範之式再規範，置換必為恆等
  for u in 0..<p2.length() {
    if p2[u] != u {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
//  二、結合順序交給 N-41 的區間 DP
// ---------------------------------------------------------------------------

///|
/// 攤平一條 ⊗ 鏈（任意結合方式）成因子陣列。
pub fn rw_flatten_tensor(e : SpaceExpr) -> Array[SpaceExpr] {
  let out : Array[SpaceExpr] = []
  fn go(x : SpaceExpr) -> Unit {
    match x {
      STensor(a, b) => {
        go(a)
        go(b)
      }
      _ => out.push(x)
    }
  }

  go(e)
  out
}

///|
/// 依結合樹重建 ⊗ 鏈。
pub fn rw_rebuild_tensor(t : AssocTree, parts : Array[SpaceExpr]) -> SpaceExpr {
  match t {
    ALeaf(i) => parts[i]
    ANode(l, r) =>
      STensor(rw_rebuild_tensor(l, parts), rw_rebuild_tensor(r, parts))
  }
}

///|
/// 【接上 N-41】成本最佳的範式：先跑類 A 範式，再把每一條 ⊗ 鏈攤平、
/// 以 `assoc_dp` 求最佳結合樹、重建。
///
/// 為什麼這不會破壞健全性：Kronecker 積**嚴格結合**，
/// (A⊗B)⊗C 與 A⊗(B⊗C) 的 Gram 逐元相同，故重新結合屬於類 A。
///
/// 為什麼這不會破壞合流性：DP 的輸出是維數序列的確定性函數，
/// 攤平後因子的順序不變，故同一式必得同一棵樹。
pub fn normalize_dp(e : SpaceExpr) -> SpaceExpr {
  fn go(x : SpaceExpr) -> SpaceExpr {
    match x {
      STensor(_, _) => {
        let parts = rw_flatten_tensor(x)
        let sub = Array::makei(parts.length(), i => go(parts[i]))
        if sub.length() < 3 {
          // 兩個因子只有一種結合方式
          let mut acc = sub[0]
          for i in 1..<sub.length() {
            acc = STensor(acc, sub[i])
          }
          acc
        } else {
          let dims = Array::makei(sub.length(), i => sub[i].sdim())
          let (_, t) = assoc_dp(dims)
          rw_rebuild_tensor(t, sub)
        }
      }
      SSum(a, b) => SSum(go(a), go(b))
      SKSum(a, b) => SKSum(go(a), go(b))
      SDual(a) => SDual(go(a))
      SExt(a, k) => SExt(go(a), k)
      STwist(a, m) => STwist(go(a), m)
      SSub(a, s) => SSub(go(a), s)
      SLeaf(_, _) => x
    }
  }

  go(normalize(e))
}

///|
/// 範式之三路成本比較：直接、類 A 範式、類 A 範式 + DP 結合。
/// 回傳 (直接, 範式, 範式+DP, 三者 Gram 是否逐元相同)。
pub fn rw_cost_triple(e : SpaceExpr) -> (Int64, Int64, Int64, Bool) {
  let c1 = Cost::new()
  let g1 = e.sgram_cost(c1)
  let n = normalize(e)
  let c2 = Cost::new()
  let g2 = n.sgram_cost(c2)
  let d = normalize_dp(e)
  let c3 = Cost::new()
  let g3 = d.sgram_cost(c3)
  (c1.wmul, c2.wmul, c3.wmul, g1.equals(g2) && g1.equals(g3))
}

///|
/// 語料掃描：DP 結合相對純類 A 範式的效果。
/// 回傳 (語料數, 全部 Gram 相同?, DP 較便宜數, 相同數, DP 較貴數,
///        類 A 總成本, DP 總成本)。
pub fn rw_dp_scan(rng : Rng) -> (Int, Bool, Int, Int, Int, Int64, Int64) {
  let corpus = rw_corpus(rng)
  let mut allsame = true
  let mut cheaper = 0
  let mut same = 0
  let mut dearer = 0
  let mut ta = 0L
  let mut td = 0L
  for e in corpus {
    let (_, a, d, ok) = rw_cost_triple(e)
    if !ok {
      allsame = false
    }
    ta = ta + a
    td = td + d
    if d < a {
      cheaper = cheaper + 1
    } else if d == a {
      same = same + 1
    } else {
      dearer = dearer + 1
    }
  }
  (corpus.length(), allsame, cheaper, same, dearer, ta, td)
}

///|
/// A10 的成本回歸：掃語料找出「類 A 範式比直接物化還貴」的式子，
/// 回報接上 DP 之後它們怎麼了。
///
/// N-53 的 `rw_cost_profile` 量到 34 便宜／5 不變／**1 變貴**，
/// 那一式就是 A10 右結合正規序造成的。
/// 回傳 (變貴式數, 直接, 類 A, 類 A+DP, DP 是否修好)。
pub fn rw_a10_regression(rng : Rng) -> (Int, Int64, Int64, Int64, Bool) {
  let corpus = rw_corpus(rng)
  let mut cnt = 0
  let mut bd = 0L
  let mut ba = 0L
  let mut bp = 0L
  for e in corpus {
    let (d, a, pp, _) = rw_cost_triple(e)
    if a > d {
      cnt = cnt + 1
      if a - d > ba - bd {
        bd = d
        ba = a
        bp = pp
      }
    }
  }
  (cnt, bd, ba, bp, bp <= bd)
}

///|
/// 長鏈上 DP 的真正價值：A10 產生的是右結合，DP 產生的是最佳結合。
///
/// 回傳 (鏈數, 右結合總成本, DP 總成本, 最大單鏈增益)。
pub fn rw_chain_gain(rng : Rng) -> (Int, Int64, Int64, Double) {
  let cases : Array[Array[Int]] = [
    [2, 2, 5],
    [5, 2, 2],
    [2, 5, 2, 2],
    [2, 2, 2, 5],
    [4, 2, 3, 2],
    [2, 3, 2, 4],
    [5, 2, 2, 2, 2],
    [2, 2, 2, 2, 5],
  ]
  let mut tr = 0L
  let mut td = 0L
  let mut best = 1.0
  for dims in cases {
    let parts : Array[SpaceExpr] = []
    for i in 0..<dims.length() {
      parts.push(SLeaf("L" + i.to_string(), rand_gram(rng, dims[i])))
    }
    let k = dims.length()
    let er = rw_rebuild_tensor(assoc_right(k), parts)
    let (_, t) = assoc_dp(dims)
    let ed = rw_rebuild_tensor(t, parts)
    let c1 = Cost::new()
    let g1 = er.sgram_cost(c1)
    let c2 = Cost::new()
    let g2 = ed.sgram_cost(c2)
    // 兩種結合必須給出逐元相同的 Gram（Kronecker 嚴格結合）
    if !g1.equals(g2) {
      return (0, 0L, 0L, 0.0)
    }
    tr = tr + c1.wmul
    td = td + c2.wmul
    if c2.wmul > 0L {
      let r = c1.wmul.to_double() / c2.wmul.to_double()
      if r > best {
        best = r
      }
    }
  }
  (cases.length(), tr, td, best)
}

///|
/// 類 B 之語料掃描（逐元健全性 + 冪等）。
/// 回傳 (語料數, 逐元健全數, 冪等數, 被交換過的式數)。
pub fn canon_scan(rng : Rng) -> (Int, Int, Int, Int) {
  let corpus = rw_corpus(rng)
  let mut snd = 0
  let mut stb = 0
  let mut moved = 0
  for e in corpus {
    if canon_sound(e) {
      snd = snd + 1
    }
    if canon_stable(e) {
      stb = stb + 1
    }
    let (c, _) = canon_perm(e)
    if c.slabel() != e.slabel() {
      moved = moved + 1
    }
  }
  (corpus.length(), snd, stb, moved)
}

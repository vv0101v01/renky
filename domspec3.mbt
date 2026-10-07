///|
/// # 第九輪派工：外冪與 Kron 和的特化路徑
///
/// ## 它們是最後兩個「沒有路徑」的形狀
///
/// N-54 以來，外冪與 Kron 和一直被當成兩側對照 —— 沒有特化路徑的形狀，
/// 兩條路線的成本必須**完全相等**。這個對照很好用，但它同時意味著：
/// 這兩個形狀的求解一直是物化 Gram 再 Gauss 求逆，而它們的 Gram 恰好是
/// 全庫**最大**的（Λ²(ℍ³) 是 66 維，⊞ 把維數相乘）。
///
/// ## 外冪：Cauchy–Binet 給了一個免費的答案
///
/// ```text
///   C_k(A·B) = C_k(A)·C_k(B)        （Cauchy–Binet）
///   ⇒ C_k(G)·C_k(G⁻¹) = C_k(I) = I
///   ⇒ C_k(G)⁻¹ = C_k(G⁻¹)
/// ```
///
/// 於是「解一個 C(n,k) 階的方程」變成「解一個 n 階的方程，再造一次複合矩陣」。
/// n = 8、k = 2 時那是 8 階對 28 階之差。
///
/// ## Kron 和：它是一個 Sylvester 方程
///
/// 以本庫的張量索引約定（(i,k) ↦ i·m + k），
///
/// ```text
///   (G_A ⊗ I + I ⊗ G_B)·vec(X) = vec(G_A·X + X·G_B)
/// ```
///
/// 所以 ⊞ 的求解就是 Sylvester 方程 `G_A·X + X·G_B = C`。
/// 精確有理解法用特徵多項式（Faddeev）：設 p(t) = det(tI − G_A) = Σ aₖ tᵏ，
///
/// ```text
///   X = −p(−G_B)⁻¹ · Σ_{k=1}^{n} aₖ Σ_{j=0}^{k-1} G_A^j · C · (−G_B)^{k-1-j}
/// ```
///
/// 可解性條件是 spec(G_A) ∩ spec(−G_B) = ∅ —— 而兩個 Gram 都是正定的，
/// 一個譜全正、一個譜全負，**條件自動成立**。正定假設在這裡不是技術細節，
/// 它正好是這條路徑能用的理由。

///|
/// 【新路徑】外冪之特化求解：C_k(G)⁻¹ = C_k(G⁻¹)。
pub fn spec_ext_solve(
  a : SpaceExpr,
  k : Int,
  rhs : Mat[Q],
  c : Cost,
) -> Mat[Q]? {
  // 先在底空間上求逆（遞迴走特化路徑），再造複合矩陣
  let n = a.sdim()
  match spec_solve_mat2(a, Mat::ident(n), c) {
    None => None
    Some(gi) => {
      let ck = compound(gi, k, c)
      Some(qmul_cost(c, ck, rhs))
    }
  }
}

///|
/// 精確有理 Sylvester 求解：A·X + X·B = C，以特徵多項式（Faddeev）消元。
///
/// 回傳 None 表示 p(−B) 不可逆（spec(A) ∩ spec(−B) ≠ ∅）。
pub fn sylvester_solve(
  a : Mat[Q],
  b : Mat[Q],
  cm : Mat[Q],
  c : Cost,
) -> Mat[Q]? {
  let n = a.mrows
  let m = b.mrows
  let p = qcharpoly_faddeev(a, c)
  // negB = −B 的冪次表
  let negb = Mat::build(m, m, (i, j) => b.at(i, j).neg())
  let bp : Array[Mat[Q]] = [Mat::ident(m)]
  for i in 1..<(n + 1) {
    bp.push(qmul_cost(c, bp[i - 1], negb))
  }
  // A 的冪次表
  let ap : Array[Mat[Q]] = [Mat::ident(n)]
  for i in 1..<(n + 1) {
    ap.push(qmul_cost(c, ap[i - 1], a))
  }
  // S = Σ_{k=1}^{n} a_k Σ_{j=0}^{k-1} A^j · C · (−B)^{k-1-j}
  let s = Mat::build(n, m, (_i, _j) => Q::zero())
  for kk in 1..<(n + 1) {
    let ak = p[kk]
    if Q::is_zero(ak) {
      continue
    }
    for j in 0..<kk {
      let t1 = qmul_cost(c, ap[j], cm)
      let t2 = qmul_cost(c, t1, bp[kk - 1 - j])
      for i in 0..<n {
        for l in 0..<m {
          s.put(i, l, s.at(i, l).add(ak.mul(t2.at(i, l))))
        }
      }
    }
  }
  // p(−B) = Σ a_k (−B)^k
  let pb = Mat::build(m, m, (_i, _j) => Q::zero())
  for kk in 0..<(n + 1) {
    let ak = p[kk]
    if Q::is_zero(ak) {
      continue
    }
    for i in 0..<m {
      for l in 0..<m {
        pb.put(i, l, pb.at(i, l).add(ak.mul(bp[kk].at(i, l))))
      }
    }
  }
  match qinv_gauss(pb, c) {
    None => None
    Some(pbi) => {
      let x = qmul_cost(c, s, pbi)
      Some(Mat::build(n, m, (i, j) => x.at(i, j).neg()))
    }
  }
}

///|
/// 【新路徑】Kron 和之特化求解：轉成 Sylvester 方程。
pub fn spec_ksum_solve(
  a : SpaceExpr,
  b : SpaceExpr,
  rhs : Mat[Q],
  c : Cost,
) -> Mat[Q]? {
  let n = a.sdim()
  let m = b.sdim()
  let ga = a.sgram_cost(c)
  let gb = b.sgram_cost(c)
  let k = rhs.mcols
  let cols : Array[Mat[Q]] = []
  for j in 0..<k {
    let cm = Mat::build(n, m, (i, l) => rhs.at(i * m + l, j))
    match sylvester_solve(ga, gb, cm, c) {
      None => return None
      Some(x) => cols.push(x)
    }
  }
  Some(Mat::build(n * m, k, (p, j) => cols[j].at(p / m, p % m)))
}

///|
/// 第三代派工器：葉／張量／直和／對偶／扭曲／子空間／外冪／Kron 和全有路徑。
pub fn spec_solve_mat3(e : SpaceExpr, rhs : Mat[Q], c : Cost) -> Mat[Q]? {
  match e {
    SExt(a, k) => spec_ext_solve(a, k, rhs, c)
    SKSum(a, b) => spec_ksum_solve(a, b, rhs, c)
    SSub(a, s) => spec_sub_solve(a, s, rhs, c)
    SSum(a, b) => {
      let na = a.sdim()
      let nb = b.sdim()
      let k = rhs.mcols
      let ra = Mat::build(na, k, (i, j) => rhs.at(i, j))
      let rb = Mat::build(nb, k, (i, j) => rhs.at(na + i, j))
      match (spec_solve_mat3(a, ra, c), spec_solve_mat3(b, rb, c)) {
        (Some(xa), Some(xb)) =>
          Some(
            Mat::build(na + nb, k, (i, j) => {
              if i < na {
                xa.at(i, j)
              } else {
                xb.at(i - na, j)
              }
            }),
          )
        _ => None
      }
    }
    STensor(a, b) => {
      let n = a.sdim()
      let m = b.sdim()
      let k = rhs.mcols
      let cols : Array[Mat[Q]] = []
      for j in 0..<k {
        let r = Mat::build(n, m, (i, l) => rhs.at(i * m + l, j))
        match spec_solve_mat3(a, r, c) {
          None => return None
          Some(y) =>
            match spec_solve_mat3(b, y.transpose(), c) {
              None => return None
              Some(xt) => cols.push(xt.transpose())
            }
        }
      }
      Some(Mat::build(n * m, k, (p, j) => cols[j].at(p / m, p % m)))
    }
    _ => spec_solve_mat2(e, rhs, c)
  }
}

///|
/// 三代派工器至此對每一種形狀都有路徑。
pub fn spec_has_path3(_e : SpaceExpr) -> Bool {
  true
}

///|
/// 外冪與 Kron 和之語料。
pub fn ek_corpus(rng : Rng) -> Array[SpaceExpr] {
  fn leaf(nm : String, d : Int) -> SpaceExpr {
    SLeaf(nm, rand_gram(rng, d))
  }

  [
    SExt(leaf("A", 4), 2),
    SExt(leaf("B", 5), 2),
    SExt(leaf("C", 6), 2),
    SExt(leaf("D", 5), 3),
    SExt(STensor(leaf("E", 2), leaf("F", 3)), 2),
    SExt(SSum(leaf("G", 3), leaf("H", 2)), 2),
    SKSum(leaf("I", 3), leaf("J", 3)),
    SKSum(leaf("K", 4), leaf("L", 3)),
    SKSum(leaf("M", 2), leaf("N", 5)),
    SKSum(leaf("O", 4), leaf("P", 4)),
    SKSum(leaf("Q", 5), leaf("R", 2)),
    SKSum(STensor(leaf("S", 2), leaf("T", 2)), leaf("U", 3)),
  ]
}

///|
/// 掃描：外冪與 Kron 和之兩路對照。
///
/// 回傳 (語料數, 逐元相同數, 通用總成本, 特化總成本, 勝, 敗)。
pub fn ek_scan(rng : Rng) -> (Int, Int, Int64, Int64, Int, Int) {
  let corpus = ek_corpus(rng)
  let mut same = 0
  let mut td = 0L
  let mut ts = 0L
  let mut win = 0
  let mut lose = 0
  for e in corpus {
    let n = e.sdim()
    let rhs = Mat::build(n, 2, (_i, _j) => Scalar::s_rand(rng))
    let c1 = Cost::new()
    let d = dense_solve_mat(e, rhs, c1)
    let c2 = Cost::new()
    let s = spec_solve_mat3(e, rhs, c2)
    match (d, s) {
      (Some(x), Some(y)) => if x.equals(y) { same = same + 1 }
      _ => ()
    }
    td = td + c1.wmul
    ts = ts + c2.wmul
    if c2.wmul < c1.wmul {
      win = win + 1
    } else if c2.wmul > c1.wmul {
      lose = lose + 1
    }
  }
  (corpus.length(), same, td, ts, win, lose)
}

///|
/// 逐形狀統計。回傳 [(形狀, 式數, 通用, 特化)]。
pub fn ek_by_shape(rng : Rng) -> Array[(String, Int, Int64, Int64)] {
  let corpus = ek_corpus(rng)
  let names = ["外冪", "Kron 和"]
  let out : Array[(String, Int, Int64, Int64)] = []
  for nm in names {
    let mut cnt = 0
    let mut td = 0L
    let mut ts = 0L
    for e in corpus {
      if spec_shape(e) == nm {
        let n = e.sdim()
        let rhs = Mat::build(n, 2, (_i, _j) => Scalar::s_rand(rng))
        let c1 = Cost::new()
        let _ = dense_solve_mat(e, rhs, c1)
        let c2 = Cost::new()
        let _ = spec_solve_mat3(e, rhs, c2)
        cnt = cnt + 1
        td = td + c1.wmul
        ts = ts + c2.wmul
      }
    }
    out.push((nm, cnt, td, ts))
  }
  out
}

///|
/// Cauchy–Binet 之直接覆核：C_k(G)·C_k(G⁻¹) = I。
pub fn ext_cauchy_binet(rng : Rng) -> (Int, Int) {
  let mut tot = 0
  let mut ok = 0
  for cfg in [(4, 2), (5, 2), (5, 3), (6, 2)] {
    let g = rand_gram(rng, cfg.0)
    tot = tot + 1
    match qinv_gauss(g, Cost::new()) {
      None => ()
      Some(gi) => {
        let a = compound(g, cfg.1, Cost::new())
        let b = compound(gi, cfg.1, Cost::new())
        if a.times(b).equals(Mat::ident(a.mrows)) {
          ok = ok + 1
        }
      }
    }
  }
  (tot, ok)
}

///|
/// Sylvester 之直接覆核：G_A·X + X·G_B 必須回到 C。
pub fn ksum_sylvester_check(rng : Rng) -> (Int, Int) {
  let mut tot = 0
  let mut ok = 0
  for cfg in [(3, 3), (4, 3), (2, 5), (4, 4)] {
    let ga = rand_gram(rng, cfg.0)
    let gb = rand_gram(rng, cfg.1)
    let cm = Mat::build(cfg.0, cfg.1, (_i, _j) => Scalar::s_rand(rng))
    tot = tot + 1
    match sylvester_solve(ga, gb, cm, Cost::new()) {
      None => ()
      Some(x) => {
        let lhs = ga.times(x).plus(x.times(gb))
        if lhs.equals(cm) {
          ok = ok + 1
        }
      }
    }
  }
  (tot, ok)
}

///|
/// 兩側對照：既然每個形狀都有路徑了，對照改成「故意用錯的恆等式」。
///
/// 外冪：用 C_k(G)⁻¹ ≟ C_k(G)（少取一次逆）—— 必須對不上。
/// Kron 和：用 G_A·X + X·G_B ≟ C 的錯誤符號版 —— 必須對不上。
/// 回傳 (檢查數, 被推翻數)。
pub fn ek_control(rng : Rng) -> (Int, Int) {
  let mut tot = 0
  let mut caught = 0
  // 外冪：錯版不取逆
  for cfg in [(4, 2), (5, 2)] {
    let g = rand_gram(rng, cfg.0)
    let e = SExt(SLeaf("X", g), cfg.1)
    let n = e.sdim()
    let rhs = Mat::build(n, 1, (_i, _j) => Scalar::s_rand(rng))
    let truth = dense_solve_mat(e, rhs, Cost::new())
    let wrong = compound(g, cfg.1, Cost::new()).times(rhs)
    tot = tot + 1
    match truth {
      Some(t) => if !t.equals(wrong) { caught = caught + 1 }
      None => ()
    }
  }
  // Kron 和：錯版把 + 寫成 −
  for cfg in [(3, 3), (4, 3)] {
    let ga = rand_gram(rng, cfg.0)
    let gb = rand_gram(rng, cfg.1)
    let cm = Mat::build(cfg.0, cfg.1, (_i, _j) => Scalar::s_rand(rng))
    tot = tot + 1
    let negb = Mat::build(cfg.1, cfg.1, (i, j) => gb.at(i, j).neg())
    match
      (
        sylvester_solve(ga, gb, cm, Cost::new()),
        sylvester_solve(ga, negb, cm, Cost::new()),
      ) {
      (Some(x), Some(y)) => if !x.equals(y) { caught = caught + 1 }
      _ => caught = caught + 1
    }
  }
  (tot, caught)
}

///|
/// 指紋。
pub fn ek_digest(rng : Rng) -> String {
  let (n, same, td, ts, win, lose) = ek_scan(rng)
  n.to_string() +
  ":" +
  same.to_string() +
  ":" +
  td.to_string() +
  ":" +
  ts.to_string() +
  ":" +
  win.to_string() +
  ":" +
  lose.to_string()
}

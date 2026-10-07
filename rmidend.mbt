///|
/// # N-55 ℝ 軌進中端 —— 規範化在浮點下還成不成立
///
/// ## 問題
///
/// N-53 的 10 條重寫規則是**精確**的：在 ℚ 上，重寫前後的 Gram 逐元相同。
/// 但後端真正要跑的往往是 ℝ 軌（Cholesky、特徵值、expm 都只在 ℝ 上有）。
/// 到了 IEEE-754 binary64，「逐元相同」立刻不成立：
///
/// ```text
///   (A⊗B)*  ：先造 nm×nm 的 Kronecker 積，再求一次 nm 階逆
///   A*⊗B*   ：各求一次 n 階與 m 階逆，再造 Kronecker 積
/// ```
///
/// 兩條路線在 ℝ 上是**不同的算術序列**，捨入誤差不同。於是出現一個
/// 在 ℚ 軌不存在的問題：規範化到底讓答案更準，還是更不準？
///
/// ## 本條能問出這個問題的理由
///
/// 因為本庫同時有精確軌。同一個 SpaceExpr 在 ℚ 上算一次得到**真值**，
/// 在 ℝ 上沿兩條路線各算一次，兩個偏差都可以對著真值量。
/// 沒有精確軌的數值庫只能互相比較兩個近似值，分不出誰靠近真值。
///
/// ## 定義（ℝ 軌的結構化求值）
///
/// `rsgram(e)` 完全照 IR 遞迴，但每一步都在 Float64 上做：
/// 葉子轉浮點、⊗ 走 Kronecker、⊕ 走分塊、* 走數值求逆、
/// Λᵏ 走浮點複合矩陣、T/U 走 MᵀGM、⊞ 走 Kronecker 和。

///|
/// 精確 Gram 轉浮點（真值的浮點表示）。
pub fn rq_mat(m : Mat[Q]) -> RMat {
  Mat::build(m.mrows, m.mcols, (i, j) => m.at(i, j).to_double())
}

///|
/// 浮點第 k 複合矩陣（Λᵏ 之 Gram）。
pub fn rcompound(a : RMat, k : Int, c : Cost) -> RMat {
  let n = a.mrows
  let ss = subsets_k(n, k)
  let m = ss.length()
  cflop(c, (m * m * k * k * k).to_int64())
  Mat::build(m, m, (i, j) => {
    let si = ss[i]
    let sj = ss[j]
    mdet(Mat::build(k, k, (r, s) => a.at(si[r], sj[s])))
  })
}

///|
/// ℝ 軌的結構化 Gram 求值：照 IR 遞迴，全程 Float64。
pub fn rsgram(e : SpaceExpr, c : Cost) -> RMat {
  match e {
    SLeaf(_, g) => rq_mat(g)
    STensor(a, b) => rkron_cost(c, rsgram(a, c), rsgram(b, c))
    SSum(a, b) => rblock_diag(rsgram(a, c), rsgram(b, c))
    SDual(a) => {
      let g = rsgram(a, c)
      cflop(c, (g.mrows * g.mrows * g.mrows).to_int64())
      match minv(g) {
        Some(h) => h.transpose()
        None => Mat::ident(g.mrows)
      }
    }
    SExt(a, k) => rcompound(rsgram(a, c), k, c)
    STwist(a, m) => {
      let g = rsgram(a, c)
      let mm = rq_mat(m)
      let n = g.mrows
      cflop(c, (2 * n * n * n).to_int64())
      mm.transpose().times(g).times(mm)
    }
    SSub(a, sm) => {
      let g = rsgram(a, c)
      let mm = rq_mat(sm)
      let n = g.mrows
      cflop(c, (2 * n * n * mm.mcols).to_int64())
      mm.transpose().times(g).times(mm)
    }
    SKSum(a, b) => kron_sum(rsgram(a, c), rsgram(b, c))
  }
}

///|
/// 相對偏差：‖X − Y‖_max / max(1, ‖Y‖_max)。
pub fn rrel_dev(x : RMat, y : RMat) -> Double {
  if x.mrows != y.mrows || x.mcols != y.mcols {
    return 1.0
  }
  let mut d = 0.0
  let mut s = 1.0
  for i in 0..<x.mrows {
    for j in 0..<x.mcols {
      let a = x.at(i, j) - y.at(i, j)
      let aa = if a < 0.0 { -a } else { a }
      if aa > d {
        d = aa
      }
      let b = y.at(i, j)
      let bb = if b < 0.0 { -b } else { b }
      if bb > s {
        s = bb
      }
    }
  }
  d / s
}

///|
/// 一式之量測：(原式相對誤差, 範式相對誤差, 原式 flops, 範式 flops, 真值條件數)。
/// 真值由 ℚ 軌給出（精確 Gram 轉浮點）。
pub fn rmid_cell(e : SpaceExpr) -> (Double, Double, Int64, Int64, Double) {
  let truth = rq_mat(e.sgram())
  let c1 = Cost::new()
  let ra = rsgram(e, c1)
  let ne = normalize(e)
  let c2 = Cost::new()
  let rb = rsgram(ne, c2)
  let k = cond2(truth)
  (rrel_dev(ra, truth), rrel_dev(rb, truth), c1.flops, c2.flops, k)
}

///|
/// ℝ 軌掃描。回傳
/// (式數, 範式較準數, 範式較不準數, 相同數, 原式最大誤差, 範式最大誤差,
///  原式 flops, 範式 flops, 最大條件數)。
pub fn rmid_scan(
  rng : Rng,
) -> (Int, Int, Int, Int, Double, Double, Int64, Int64, Double) {
  let xs = spec_corpus(rng)
  let mut better = 0
  let mut worse = 0
  let mut tie = 0
  let mut ea = 0.0
  let mut eb = 0.0
  let mut fa : Int64 = 0
  let mut fb : Int64 = 0
  let mut kmax = 0.0
  for e in xs {
    let (x, y, p, q, k) = rmid_cell(e)
    if y < x {
      better = better + 1
    } else if y > x {
      worse = worse + 1
    } else {
      tie = tie + 1
    }
    if x > ea {
      ea = x
    }
    if y > eb {
      eb = y
    }
    fa = fa + p
    fb = fb + q
    if k > kmax {
      kmax = k
    }
  }
  (xs.length(), better, worse, tie, ea, eb, fa, fb, kmax)
}

///|
/// ℝ 軌的特化求解器（N-54 之浮點對應）。
pub fn rspec_solve(e : SpaceExpr, rhs : RMat, c : Cost) -> RMat? {
  match e {
    SLeaf(_, g) => rleaf_solve(rq_mat(g), rhs, c)
    SSum(a, b) => {
      let na = a.sdim()
      let nb = b.sdim()
      let k = rhs.mcols
      let ra = Mat::build(na, k, (i, j) => rhs.at(i, j))
      let rb = Mat::build(nb, k, (i, j) => rhs.at(na + i, j))
      match (rspec_solve(a, ra, c), rspec_solve(b, rb, c)) {
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
      let cols : Array[RMat] = []
      for j in 0..<k {
        let r = Mat::build(n, m, (i, l) => rhs.at(i * m + l, j))
        match rspec_solve(a, r, c) {
          None => return None
          Some(y) =>
            match rspec_solve(b, y.transpose(), c) {
              None => return None
              Some(xt) => cols.push(xt.transpose())
            }
        }
      }
      Some(Mat::build(n * m, k, (p, j) => cols[j].at(p / m, p % m)))
    }
    SDual(a) => {
      let ga = rsgram(a, c)
      cflop(c, (ga.mrows * ga.mrows * rhs.mcols).to_int64())
      Some(ga.times(rhs))
    }
    STwist(a, m) => {
      let mm = rq_mat(m)
      match rleaf_solve(mm.transpose(), rhs, c) {
        None => None
        Some(z) =>
          match rspec_solve(a, z, c) {
            None => None
            Some(y) => rleaf_solve(mm, y, c)
          }
      }
    }
    other => {
      let g = rsgram(other, c)
      cflop(c, (g.mrows * g.mrows * g.mrows).to_int64())
      match minv(g) {
        Some(gi) => Some(gi.times(rhs))
        None => None
      }
    }
  }
}

///|
/// 浮點葉子求解：一次求逆後相乘。
fn rleaf_solve(g : RMat, rhs : RMat, c : Cost) -> RMat? {
  cflop(c, (g.mrows * g.mrows * g.mrows).to_int64())
  match minv(g) {
    Some(gi) => Some(gi.times(rhs))
    None => None
  }
}

///|
/// ℝ 軌通用路徑：物化整個 Gram 再求逆。
pub fn rdense_solve(e : SpaceExpr, rhs : RMat, c : Cost) -> RMat? {
  let g = rsgram(e, c)
  cflop(c, (g.mrows * g.mrows * g.mrows).to_int64())
  match minv(g) {
    Some(gi) => Some(gi.times(rhs))
    None => None
  }
}

///|
/// 端到端：以 ℚ 軌的精確解為真值，量兩條 ℝ 路線的偏差。
/// 回傳 (式數, 可解數, 特化較準數, 通用較準數, 特化最大誤差, 通用最大誤差,
///       特化 flops, 通用 flops)。
pub fn rmid_solve_scan(
  rng : Rng,
) -> (Int, Int, Int, Int, Double, Double, Int64, Int64) {
  let xs = spec_corpus(rng)
  let mut solv = 0
  let mut sbet = 0
  let mut dbet = 0
  let mut es = 0.0
  let mut ed = 0.0
  let mut fs : Int64 = 0
  let mut fd : Int64 = 0
  for e in xs {
    let n = e.sdim()
    let bq : Array[Q] = Array::makei(n, _ => Scalar::s_rand(rng))
    let g = e.sgram()
    match qsolve_gauss(g, bq, Cost::new()) {
      None => ()
      Some(xq) => {
        solv = solv + 1
        let truth = Mat::build(n, 1, (i, _j) => xq[i].to_double())
        let rhs = Mat::build(n, 1, (i, _j) => bq[i].to_double())
        let cs = Cost::new()
        let cd = Cost::new()
        let a = rspec_solve(e, rhs, cs)
        let b = rdense_solve(e, rhs, cd)
        fs = fs + cs.flops
        fd = fd + cd.flops
        let da = match a {
          Some(x) => rrel_dev(x, truth)
          None => 1.0
        }
        let db = match b {
          Some(x) => rrel_dev(x, truth)
          None => 1.0
        }
        if da < db {
          sbet = sbet + 1
        } else if db < da {
          dbet = dbet + 1
        }
        if da > es {
          es = da
        }
        if db > ed {
          ed = db
        }
      }
    }
  }
  (xs.length(), solv, sbet, dbet, es, ed, fs, fd)
}

///|
/// 鑑別力對照：把一條規則改成**錯的**（(A⊗B)* → A*⊗Bᵀ*），
/// 看誤差量測是否抓得到。回傳 (正確範式誤差, 錯誤範式誤差)。
pub fn rmid_control(rng : Rng) -> (Double, Double) {
  let a : SpaceExpr = SLeaf("A", rand_gram(rng, 3))
  let b : SpaceExpr = SLeaf("B", rand_gram(rng, 3))
  let e : SpaceExpr = SDual(STensor(a, b))
  let truth = rq_mat(e.sgram())
  let good = rsgram(normalize(e), Cost::new())
  // 錯誤規則：對偶只穿過左側
  let bad : SpaceExpr = STensor(SDual(a), b)
  let badg = rsgram(bad, Cost::new())
  (rrel_dev(good, truth), rrel_dev(badg, truth))
}

///|
/// 指紋。
pub fn rmid_digest(rng : Rng) -> String {
  let (n, bt, ws, ti, _, _, fa, fb, _) = rmid_scan(rng)
  n.to_string() +
  ":" +
  bt.to_string() +
  ":" +
  ws.to_string() +
  ":" +
  ti.to_string() +
  ":" +
  fa.to_string() +
  ":" +
  fb.to_string()
}

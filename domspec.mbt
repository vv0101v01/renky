///|
/// # N-54 專屬領域化 —— 由中端 IR 派工到特化演算法
///
/// ## 定義（領域化 / domain specialization）
///
/// 通用求解器只看得到一個矩陣：它把 `SpaceExpr` 物化成 nm×nm 的 Gram，
/// 再做 Gauss 消去，Θ((nm)³)。但 IR 裡寫著這個 Gram 是怎麼來的 ——
/// 它是 A⊗B、是 A⊕B、是 A*、是 T[A,M]。領域化就是**不物化**，
/// 按 IR 的形狀把問題拆開，在葉子上才真正做 Gauss。
///
/// ```text
///   前端 IPSpace  →  中端 SpaceExpr  →  後端 spec_solve
///   （N-50 重編）     （N-53 規範化）     （本條：按形狀派工）
/// ```
///
/// ## 定義（結構化求解 G(e)·X = B）
///
/// ```text
///   葉子 L        ：Gauss 消去（Θ(n³) 一次，多個右端共用一次求逆）
///   A ⊗ B         ：G = A⊗B，向量重排成矩陣 R（n×m）後
///                   A·Y = R（m 個右端），B·Xᵀ = Yᵀ（n 個右端）
///                   —— 根據 (A⊗B)·vec(X) = vec(A·X·Bᵀ)，B 對稱故 Bᵀ = B
///   A ⊕ B         ：右端依分塊切開，兩邊各自遞迴
///   A*            ：G(A*) = (G(A)⁻¹)ᵀ = G(A)⁻¹（G 對稱）
///                   故解 = G(A)·B —— 一次矩陣乘法，完全不必求逆
///   T[A,M]        ：MᵀG(A)M·X = B ⟺ Mᵀ·Z = B，G(A)·Y = Z，M·X = Y
///   其餘（Λᵏ、U、⊞）：退回通用路徑（物化 + Gauss）
/// ```
///
/// ## 與 N-53 的接點
///
/// 原式 `(A⊗B)*` 落在「對偶」分支：得先把 A⊗B 物化成 nm×nm 再乘。
/// 經 N-53 規範化成 `A*⊗B*` 之後，落在「張量」分支，兩側各自是一次
/// 小小的對偶（矩陣乘法）。規範化不是美觀問題，它直接換掉後端走哪條路。

///|
/// IR 形狀分類（派工用）。
pub fn spec_shape(e : SpaceExpr) -> String {
  match e {
    SLeaf(_, _) => "葉"
    STensor(_, _) => "張量"
    SSum(_, _) => "直和"
    SDual(_) => "對偶"
    STwist(_, _) => "扭曲"
    SSub(_, _) => "子空間"
    SExt(_, _) => "外冪"
    SKSum(_, _) => "Kron 和"
  }
}

///|
/// 該形狀是否有特化路徑（其餘退回通用）。
pub fn spec_has_path(e : SpaceExpr) -> Bool {
  match e {
    SLeaf(_, _) => true
    STensor(_, _) => true
    SSum(_, _) => true
    SDual(_) => true
    STwist(_, _) => true
    _ => false
  }
}

///|
/// 通用路徑：物化 Gram 後 Gauss 求逆，再乘上右端。
pub fn dense_solve_mat(e : SpaceExpr, rhs : Mat[Q], c : Cost) -> Mat[Q]? {
  let g = e.sgram_cost(c)
  match qinv_gauss(g, c) {
    Some(gi) => Some(qmul_cost(c, gi, rhs))
    None => None
  }
}

///|
/// 葉子求解：單一右端用 Gauss 回代，多個右端共用一次求逆。
fn spec_leaf_solve(g : Mat[Q], rhs : Mat[Q], c : Cost) -> Mat[Q]? {
  if rhs.mcols == 1 {
    let b : Array[Q] = Array::makei(rhs.mrows, i => rhs.at(i, 0))
    match qsolve_gauss(g, b, c) {
      Some(x) => Some(Mat::build(x.length(), 1, (i, _j) => x[i]))
      None => None
    }
  } else {
    match qinv_gauss(g, c) {
      Some(gi) => Some(qmul_cost(c, gi, rhs))
      None => None
    }
  }
}

///|
/// 【特化求解器】按 IR 形狀解 G(e)·X = RHS。
pub fn spec_solve_mat(e : SpaceExpr, rhs : Mat[Q], c : Cost) -> Mat[Q]? {
  match e {
    SLeaf(_, g) => spec_leaf_solve(g, rhs, c)
    SSum(a, b) => {
      let na = a.sdim()
      let nb = b.sdim()
      let k = rhs.mcols
      let ra = Mat::build(na, k, (i, j) => rhs.at(i, j))
      let rb = Mat::build(nb, k, (i, j) => rhs.at(na + i, j))
      match (spec_solve_mat(a, ra, c), spec_solve_mat(b, rb, c)) {
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
        // 重排：R[i][l] = rhs[i*m + l][j]
        let r = Mat::build(n, m, (i, l) => rhs.at(i * m + l, j))
        match spec_solve_mat(a, r, c) {
          None => return None
          Some(y) =>
            match spec_solve_mat(b, y.transpose(), c) {
              None => return None
              Some(xt) => cols.push(xt.transpose())
            }
        }
      }
      Some(Mat::build(n * m, k, (p, j) => cols[j].at(p / m, p % m)))
    }
    SDual(a) => {
      // G(A*) = (G(A)⁻¹)ᵀ，而 G(A) 對稱 ⇒ G(A*) = G(A)⁻¹，故解 = G(A)·RHS
      let ga = a.sgram_cost(c)
      Some(qmul_cost(c, ga, rhs))
    }
    STwist(a, m) => {
      let mt = m.transpose()
      match spec_leaf_solve(mt, rhs, c) {
        None => None
        Some(z) =>
          match spec_solve_mat(a, z, c) {
            None => None
            Some(y) => spec_leaf_solve(m, y, c)
          }
      }
    }
    other => dense_solve_mat(other, rhs, c)
  }
}

///|
/// 一次評比：回傳 (兩路一致?, 通用字乘, 特化字乘)。
pub fn spec_compare(e : SpaceExpr, rhs : Mat[Q]) -> (Bool, Int64, Int64) {
  let c1 = Cost::new()
  let a = dense_solve_mat(e, rhs, c1)
  let c2 = Cost::new()
  let b = spec_solve_mat(e, rhs, c2)
  let same = match (a, b) {
    (Some(x), Some(y)) => x.equals(y)
    (None, None) => true
    _ => false
  }
  (same, c1.wmul, c2.wmul)
}

///|
/// 以 Riesz 表示為例的端到端比對：
/// 泛函座標 c ↦ Riesz 向量 v，通用路徑用 `riesz_vector`（走 ⟦e⟧），
/// 特化路徑用 `spec_solve_mat`。兩者必須逐元相同。
pub fn spec_riesz_agrees(e : SpaceExpr, phi : Array[Q]) -> Bool {
  let sp = e.sspace()
  let generic = riesz_vector(sp, phi)
  let rhs = Mat::build(phi.length(), 1, (i, _j) => phi[i])
  match spec_solve_mat(e, rhs, Cost::new()) {
    None => false
    Some(x) => {
      let got : Array[Q] = Array::makei(x.mrows, i => x.at(i, 0))
      arr_eq(got, generic)
    }
  }
}

///|
/// 測試語料：深度受控的張量／直和／對偶／扭曲組合，外加 N-53 的語料。
pub fn spec_corpus(rng : Rng) -> Array[SpaceExpr] {
  let l2 : SpaceExpr = SLeaf("P", rand_gram(rng, 2))
  let m2 : SpaceExpr = SLeaf("Q", rand_gram(rng, 2))
  let l3 : SpaceExpr = SLeaf("R", rand_gram(rng, 3))
  let m = comb_unitri(2)
  let out : Array[SpaceExpr] = [
    STensor(l2, m2),
    STensor(l2, l3),
    STensor(l3, STensor(l2, m2)),
    STensor(STensor(l2, m2), l3),
    SSum(l2, l3),
    SSum(STensor(l2, m2), l3),
    SDual(l3),
    SDual(STensor(l2, l3)),
    STensor(SDual(l2), SDual(l3)),
    STwist(l2, m),
    STwist(STensor(l2, m2), comb_unitri(4)),
    STensor(STensor(l2, m2), STensor(l2, m2)),
    SSum(SSum(l2, m2), SSum(l2, l3)),
    SDual(SSum(l2, l3)),
    SExt(l3, 2),
    SKSum(l2, m2),
  ]
  for _t in 0..<8 {
    out.push(rand_expr(rng, 3, 14))
  }
  out
}

///|
/// 一次掃描產出全部統計（通用對照很貴，只跑一遍）。
pub struct SpecReport {
  trials : Int
  same : Int
  haspath : Int
  dense : Int64
  spec : Int64
  win : Int
  lose : Int
  shapes : Array[(String, Int, Int64, Int64)]
  cs : (Int, Int, Int, Int)
  cr : (Int, Int, Int, Int)
}

///|
/// 對語料每式各取 1 與 3 個右端，兩路各跑一次並記錄全部統計。
pub fn spec_report(rng : Rng) -> SpecReport {
  let xs = spec_corpus(rng)
  let mut same = 0
  let mut haspath = 0
  let mut c1 : Int64 = 0
  let mut c2 : Int64 = 0
  let mut win = 0
  let mut lose = 0
  let mut trials = 0
  let shapes : Array[(String, Int, Int64, Int64)] = []
  let mut a0 = 0
  let mut a1 = 0
  let mut a2 = 0
  let mut a3 = 0
  let mut b0 = 0
  let mut b1 = 0
  let mut b2 = 0
  let mut b3 = 0
  for e in xs {
    if spec_has_path(e) {
      haspath = haspath + 1
    }
    for k in [1, 3] {
      let n = e.sdim()
      let rhs = Mat::build(n, k, (_i, _j) => Scalar::s_rand(rng))
      let (okk, d, sv) = spec_compare(e, rhs)
      trials = trials + 1
      if okk {
        same = same + 1
      }
      c1 = c1 + d
      c2 = c2 + sv
      let wins = sv < d
      if wins {
        win = win + 1
      } else if sv > d {
        lose = lose + 1
      }
      let sh = spec_shape(e)
      let mut found = -1
      for t in 0..<shapes.length() {
        if shapes[t].0 == sh {
          found = t
        }
      }
      if found < 0 {
        shapes.push((sh, 1, d, sv))
      } else {
        shapes[found] = (
          sh,
          shapes[found].1 + 1,
          shapes[found].2 + d,
          shapes[found].3 + sv,
        )
      }
      if spec_should(e) {
        if wins {
          a0 = a0 + 1
        } else {
          a1 = a1 + 1
        }
      } else if wins {
        a2 = a2 + 1
      } else {
        a3 = a3 + 1
      }
      if spec_should_k(e, k) {
        if wins {
          b0 = b0 + 1
        } else {
          b1 = b1 + 1
        }
      } else if wins {
        b2 = b2 + 1
      } else {
        b3 = b3 + 1
      }
    }
  }
  {
    trials,
    same,
    haspath,
    dense: c1,
    spec: c2,
    win,
    lose,
    shapes,
    cs: (a0, a1, a2, a3),
    cr: (b0, b1, b2, b3),
  }
}

///|
/// 掃描摘要：(試驗數, 一致數, 有特化路徑之式數, 通用總成本, 特化總成本, 勝, 敗)。
pub fn spec_scan(rng : Rng) -> (Int, Int, Int, Int64, Int64, Int, Int) {
  let r = spec_report(rng)
  (r.trials, r.same, r.haspath, r.dense, r.spec, r.win, r.lose)
}

///|
/// 規範化對派工的影響（N-53 → N-54 的接點）：
/// 同一式，量「原式特化」與「規範化後特化」的成本。
/// 回傳 (式數, 規範化後更便宜之數, 原式總成本, 規範後總成本, 一致數)。
pub fn spec_norm_effect(rng : Rng) -> (Int, Int, Int64, Int64, Int) {
  let xs = spec_corpus(rng)
  let mut better = 0
  let mut c1 : Int64 = 0
  let mut c2 : Int64 = 0
  let mut same = 0
  for e in xs {
    let n = e.sdim()
    let rhs = Mat::build(n, 1, (_i, _j) => Scalar::s_rand(rng))
    let ca = Cost::new()
    let ra = spec_solve_mat(e, rhs, ca)
    let ne = normalize(e)
    let cb = Cost::new()
    let rb = spec_solve_mat(ne, rhs, cb)
    c1 = c1 + ca.wmul
    c2 = c2 + cb.wmul
    if cb.wmul < ca.wmul {
      better = better + 1
    }
    match (ra, rb) {
      (Some(x), Some(y)) => if x.equals(y) { same = same + 1 }
      (None, None) => same = same + 1
      _ => ()
    }
  }
  (xs.length(), better, c1, c2, same)
}

///|
/// 派工判準：特化路徑是否**應該**走。本庫的判準是結構性的 ——
/// 有特化路徑且該式不是葉子就走。
pub fn spec_should(e : SpaceExpr) -> Bool {
  match e {
    SLeaf(_, _) => false
    _ => spec_has_path(e)
  }
}

///|
/// 精煉判準：把實測找到的唯一一個誤判收進來。
///
/// 命題 N54-4（扭曲於葉子上不划算，且與右端個數有關）：
/// `T[葉子, M]` 的特化路徑要解三次 Θ(n³)（Mᵀ、G、M），
/// 通用路徑只付一次求逆加兩次矩陣乘法，而求逆的成本與右端個數無關。
/// 右端個數 k ≥ 2 時通用路徑攤銷得更好 —— 實測 T[P]（n = 2, k = 3）
/// 通用 412 對特化 563。
pub fn spec_should_k(e : SpaceExpr, k : Int) -> Bool {
  match e {
    SLeaf(_, _) => false
    STwist(a, _) =>
      match a {
        SLeaf(_, _) => k < 2
        _ => true
      }
    other => spec_has_path(other)
  }
}

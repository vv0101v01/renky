///|
/// # 第八輪派工：SSub 的特化路徑
///
/// ## 為什麼 SSub 原本沒有路徑
///
/// N-54 的派工表對葉、張量、直和、對偶、扭曲都有特化解法，
/// 對外冪、Kron 和、**子空間**則退回通用路徑（物化 Gram 再 Gauss 求逆）。
/// 當時外冪與 Kron 和還被拿來當「兩側對照」—— 沒有路徑的形狀，
/// 兩條路線的成本必須**完全相等**，差一分錢就代表派工出錯。
///
/// 子空間留在那一側其實是個漏洞。G(U[A,S]) = Sᵀ·G(A)·S 的維數是 k = S 的行數，
/// 通常**遠小於** A 的維數 n（U½ 砍一半，S² 把 n 嵌進 n²）。通用路徑卻要先把
/// n×n 的 G(A) 整個物化出來 —— 而 G(A) 可能是一條張量鏈，物化它正是 N-53
/// 想避免的事。
///
/// ## 關鍵：要的不是 G(A)，是 G(A)·S
///
/// ```text
///   G(U[A,S])·X = B        G = Sᵀ·G(A)·S  （k×k）
///   ─────────────────────────────────────────────────
///   通用：物化 G(A) → n² 項，兩次 n×n×k 乘法，再 k 階求逆
///   特化：只要 W = G(A)·S（n×k），M = Sᵀ·W（k×k），再 k 階求逆
/// ```
///
/// 而 `G(A)·S` 可以**遞迴地**算出來而不物化 G(A) —— 這需要一個與
/// `spec_solve_mat`（施加 G⁻¹）對偶的運算：**施加 G**。本檔先補上它。

///|
/// 施加 Gram：回傳 G(e)·X，盡可能不物化 G(e)。
///
/// 這是 `spec_solve_mat` 的對偶。注意對偶節點上兩者互換：
/// G(A*) = G(A)⁻¹，所以「對 A* 施加 G」就是「對 A 解 G」。
pub fn spec_gram_apply(e : SpaceExpr, x : Mat[Q], c : Cost) -> Mat[Q]? {
  match e {
    SLeaf(_, g) => Some(qmul_cost(c, g, x))
    SSum(a, b) => {
      let na = a.sdim()
      let nb = b.sdim()
      let k = x.mcols
      let xa = Mat::build(na, k, (i, j) => x.at(i, j))
      let xb = Mat::build(nb, k, (i, j) => x.at(na + i, j))
      match (spec_gram_apply(a, xa, c), spec_gram_apply(b, xb, c)) {
        (Some(ya), Some(yb)) =>
          Some(
            Mat::build(na + nb, k, (i, j) => {
              if i < na {
                ya.at(i, j)
              } else {
                yb.at(i - na, j)
              }
            }),
          )
        _ => None
      }
    }
    STensor(a, b) => {
      // (G_a ⊗ G_b)·vec(X) = vec(G_a · X · G_bᵀ)，G_b 對稱 ⇒ = vec(G_a·X·G_b)
      let n = a.sdim()
      let m = b.sdim()
      let k = x.mcols
      let cols : Array[Mat[Q]] = []
      for j in 0..<k {
        let r = Mat::build(n, m, (i, l) => x.at(i * m + l, j))
        match spec_gram_apply(a, r, c) {
          None => return None
          Some(y) =>
            match spec_gram_apply(b, y.transpose(), c) {
              None => return None
              Some(zt) => cols.push(zt.transpose())
            }
        }
      }
      Some(Mat::build(n * m, k, (p, j) => cols[j].at(p / m, p % m)))
    }
    SDual(a) =>
      // G(A*) = G(A)⁻¹ ⇒ 施加 G(A*) = 對 A 解 G
      spec_solve_mat(a, x, c)
    STwist(a, m) => {
      let mx = qmul_cost(c, m, x)
      match spec_gram_apply(a, mx, c) {
        None => None
        Some(y) => Some(qmul_cost(c, m.transpose(), y))
      }
    }
    SSub(a, s) => {
      let sx = qmul_cost(c, s, x)
      match spec_gram_apply(a, sx, c) {
        None => None
        Some(y) => Some(qmul_cost(c, s.transpose(), y))
      }
    }
    other => {
      let g = other.sgram_cost(c)
      Some(qmul_cost(c, g, x))
    }
  }
}

///|
/// 【新路徑】子空間之特化求解：G(U[A,S])·X = B。
///
/// 只算 W = G(A)·S（遞迴施加，不物化 G(A)），再 M = Sᵀ·W（k×k），最後 k 階求解。
pub fn spec_sub_solve(
  a : SpaceExpr,
  s : Mat[Q],
  rhs : Mat[Q],
  c : Cost,
) -> Mat[Q]? {
  match spec_gram_apply(a, s, c) {
    None => None
    Some(w) => {
      let m = qmul_cost(c, s.transpose(), w)
      spec_leaf_solve(m, rhs, c)
    }
  }
}

///|
/// 加上子空間路徑之後的派工器（與 `spec_solve_mat` 的差別只在 SSub 分支）。
pub fn spec_solve_mat2(e : SpaceExpr, rhs : Mat[Q], c : Cost) -> Mat[Q]? {
  match e {
    SSub(a, s) => spec_sub_solve(a, s, rhs, c)
    SSum(a, b) => {
      let na = a.sdim()
      let nb = b.sdim()
      let k = rhs.mcols
      let ra = Mat::build(na, k, (i, j) => rhs.at(i, j))
      let rb = Mat::build(nb, k, (i, j) => rhs.at(na + i, j))
      match (spec_solve_mat2(a, ra, c), spec_solve_mat2(b, rb, c)) {
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
        match spec_solve_mat2(a, r, c) {
          None => return None
          Some(y) =>
            match spec_solve_mat2(b, y.transpose(), c) {
              None => return None
              Some(xt) => cols.push(xt.transpose())
            }
        }
      }
      Some(Mat::build(n * m, k, (p, j) => cols[j].at(p / m, p % m)))
    }
    _ => spec_solve_mat(e, rhs, c)
  }
}

///|
/// 子空間路徑是否適用（S 必須有完整的行秩，由正定性自動保證）。
pub fn spec_has_path2(e : SpaceExpr) -> Bool {
  match e {
    SSub(_, _) => true
    _ => spec_has_path(e)
  }
}

///|
/// 子空間語料：把各種底座套上兩種嵌入矩陣。
pub fn sub_corpus(rng : Rng) -> Array[SpaceExpr] {
  let xs : Array[SpaceExpr] = []
  fn leaf(nm : String, d : Int) -> SpaceExpr {
    SLeaf(nm, rand_gram(rng, d))
  }

  let bases : Array[SpaceExpr] = [
    leaf("A", 6),
    STensor(leaf("B", 3), leaf("C", 4)),
    SSum(leaf("D", 4), leaf("E", 4)),
    SDual(STensor(leaf("F", 3), leaf("G", 3))),
    STensor(leaf("H", 2), STensor(leaf("I", 3), leaf("J", 2))),
    STwist(STensor(leaf("K", 3), leaf("L", 3)), comb_unitri(9)),
    SSum(STensor(leaf("M", 2), leaf("N", 3)), leaf("O", 3)),
    SDual(SSum(leaf("P", 4), leaf("Q", 4))),
  ]
  for b in bases {
    let n = b.sdim()
    xs.push(SSub(b, comb_half_sel(n)))
    // 第二種嵌入：取偶數座標
    let k = (n + 1) / 2
    let s = Mat::build(n, k, (i, j) => {
      if i == 2 * j {
        Q::one()
      } else {
        Q::zero()
      }
    })
    xs.push(SSub(b, s))
  }
  xs
}

///|
/// 子空間路徑之量測。
///
/// 回傳 (語料數, 兩路逐元相同數, 通用總成本, 特化總成本, 特化較便宜數, 較貴數)。
pub fn sub_scan(rng : Rng) -> (Int, Int, Int64, Int64, Int, Int) {
  let corpus = sub_corpus(rng)
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
    let s = spec_solve_mat2(e, rhs, c2)
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
/// 兩側對照：**沒有**特化路徑的形狀，兩條路線的成本必須完全相等。
///
/// 加上 SSub 之後，剩下沒有路徑的是外冪與 Kron 和。
/// 回傳 (檢查式數, 成本完全相等之式數)。
pub fn sub_control(rng : Rng) -> (Int, Int) {
  let xs : Array[SpaceExpr] = [
    SExt(SLeaf("A", rand_gram(rng, 4)), 2),
    SExt(SLeaf("B", rand_gram(rng, 5)), 2),
    SKSum(SLeaf("C", rand_gram(rng, 3)), SLeaf("D", rand_gram(rng, 3))),
    SKSum(SLeaf("E", rand_gram(rng, 2)), SLeaf("F", rand_gram(rng, 4))),
  ]
  let mut eq = 0
  for e in xs {
    let n = e.sdim()
    let rhs = Mat::build(n, 2, (_i, _j) => Scalar::s_rand(rng))
    let c1 = Cost::new()
    let _ = dense_solve_mat(e, rhs, c1)
    let c2 = Cost::new()
    let _ = spec_solve_mat2(e, rhs, c2)
    if c1.wmul == c2.wmul {
      eq = eq + 1
    }
  }
  (xs.length(), eq)
}

///|
/// 施加 Gram 之獨立覆核：spec_gram_apply(e, X) 必須逐元等於 G(e)·X。
pub fn gram_apply_check(rng : Rng) -> (Int, Int) {
  let corpus = spec_corpus(rng)
  let mut ok = 0
  for e in corpus {
    let n = e.sdim()
    let x = Mat::build(n, 2, (_i, _j) => Scalar::s_rand(rng))
    let truth = e.sgram().times(x)
    match spec_gram_apply(e, x, Cost::new()) {
      Some(y) => if y.equals(truth) { ok = ok + 1 }
      None => ()
    }
  }
  (corpus.length(), ok)
}

///|
/// # N-31 多態 catamorphism —— 真正的演算法合成器
///
/// ## 問題
///
/// 原本的合成器把「要合成哪個演算法」寫死在函式名裡：`synth_inv`、`synth_det`。
/// 每多一個 Φ 就要多寫一個遞迴函式，而 N 群已經證出律的 Φ 有九個以上。
/// 更要命的是 N-13 的搜尋引擎找到一條律之後，**沒有任何機制把它交給合成器**
/// —— 人要讀報告、再去手寫一個 `synth_xxx`。這條管線是斷的。
///
/// ## 做法
///
/// 搜尋引擎其實已經解掉了表示法問題：它把矩陣值與純量值的 Φ 統一成
/// `Mat[Q]?`，純量包成 1 × 1（`q_scalar_mat`）。本檔沿用同一個約定，
/// 於是 `PhiSpec` 可以**直接吃搜尋引擎自己的 Φ 表與規則表**，不需要翻譯層。
///
/// ```text
///   law_search  ──定律表──>  phispec_from_law  ──PhiSpec──>  synth_spec
///   （找到律）                （組裝合成器）                  （合成演算法）
/// ```
///
/// ## 發現：不是每個 Φ 都自給自足
///
/// 六個 Φ（inv、det、trace、rank、sq、cube）的合成規則只需要
/// 「兩個子結果 + 兩側維數」。但 **adj 不行** —— 它的規則
/// `adj(A⊗B) = (det A)^{m−1}(det B)^{n−1}(adj A ⊗ adj B)`
/// 需要兩側的**行列式**，而行列式不是 adj 自己算得出來的。
///
/// 這迫使合成器支援**輔助 catamorphism**：合成 adj 時同時跑一條 det 的
/// catamorphism。而 det 的 catamorphism 本身就是一條已發現的律。
/// 換句話說，**adj 的合成演算法是由兩條律複合而成的** —— 這是本庫第一個
/// 「律的複合」實例（第四輪 N-42 要系統化處理的正是這件事）。

///|
/// 一個 Φ 的完整合成規格。
///
/// 欄位之多是刻意的：它把「這個 Φ 在每種節點上需要什麼」全部攤開。
/// 想用更少的欄位，就得假設所有 Φ 的需求相同 —— 而 adj 證明了那不成立。
pub struct PhiSpec {
  /// Φ 之名稱（須與定律表中的 cphi 一致）
  pname : String
  /// 葉節點：直接在 Gram 上算。同時也是「攤平法」的基準。
  pleaf : (Mat[Q], Cost) -> Mat[Q]?
  /// ⊗ 節點所用之合成規則名（定律表中的 crule）；"" 表示此構造子上無律
  pkname : String
  /// ⊗ 節點：(Φ(A), Φ(B), dim A, dim B, det A, det B, cost)。
  /// None 表示定律表在此構造子上沒有可用之律 —— 該節點改走攤平。
  pkron : ((Mat[Q], Mat[Q], Int, Int, Q, Q, Cost) -> Mat[Q]?)?
  /// ⊕ 節點所用之合成規則名；"" 表示無律
  psname : String
  /// ⊕ 節點：同上，None 表示攤平
  psum : ((Mat[Q], Mat[Q], Int, Int, Q, Q, Cost) -> Mat[Q]?)?
  /// 對偶節點是否需要子樹之 Φ 值（det 需要；inv 不需要 —— 它只要子樹的 Gram）
  pdual_phi : Bool
  /// 對偶節點：(子樹, Φ(子樹)（若 pdual_phi）, cost)
  pdual : (SpaceExpr, Mat[Q]?, Cost) -> Mat[Q]?
  /// 是否需要並行跑一條 det 的 catamorphism（adj 需要）
  paux : Bool
  /// Λᵏ 節點之規則名；"" 表示無律（攤平）
  pxname : String
  /// Λᵏ 節點：(Φ(子樹), k, dim 子樹, det 子樹, cost)
  pext : ((Mat[Q], Int, Int, Q, Cost) -> Mat[Q]?)?
  /// 同餘節點之規則名；"" 表示無律（攤平）
  ptname : String
  /// 同餘節點：(Φ(子樹), 扭曲矩陣 A, dim 子樹, det 子樹, cost)
  ptwist : ((Mat[Q], Mat[Q], Int, Q, Cost) -> Mat[Q]?)?
}

///|
/// 多態 catamorphism。
///
/// 回傳 (Φ 值, 輔助行列式)。輔助行列式只在 `paux` 為真時真的計算；
/// 否則固定為 1，不付任何成本。
pub fn synth_spec_aux(spec : PhiSpec, e : SpaceExpr, c : Cost) -> (Mat[Q]?, Q) {
  match e {
    SLeaf(_, g) => {
      let v = (spec.pleaf)(g, c)
      let d = if spec.paux { qdet_gauss(g, c) } else { Q::one() }
      (v, d)
    }
    STensor(a, b) =>
      match spec.pkron {
        // 此構造子上無律：攤平本節點（先求整個子樹之 Gram，再直接施以 Φ）。
        // 這不是失敗，而是 N-12 分派器所說的「該攤就攤」。
        None => {
          let g = e.sgram_cost(c)
          let d = if spec.paux { qdet_gauss(g, c) } else { Q::one() }
          ((spec.pleaf)(g, c), d)
        }
        Some(kf) => {
          let (xa, da) = synth_spec_aux(spec, a, c)
          let (xb, db) = synth_spec_aux(spec, b, c)
          let na = a.sdim()
          let nb = b.sdim()
          // det(A⊗B) = (det A)^{dim B}·(det B)^{dim A} —— 輔助律本身即 N-13 所尋獲
          let d = if spec.paux {
            cq_mul(c, qpow_fast(c, da, nb), qpow_fast(c, db, na))
          } else {
            Q::one()
          }
          match (xa, xb) {
            (Some(x), Some(y)) => (kf(x, y, na, nb, da, db, c), d)
            _ => (None, d)
          }
        }
      }
    SSum(a, b) =>
      match spec.psum {
        None => {
          let g = e.sgram_cost(c)
          let d = if spec.paux { qdet_gauss(g, c) } else { Q::one() }
          ((spec.pleaf)(g, c), d)
        }
        Some(sf) => {
          let (xa, da) = synth_spec_aux(spec, a, c)
          let (xb, db) = synth_spec_aux(spec, b, c)
          let na = a.sdim()
          let nb = b.sdim()
          let d = if spec.paux { cq_mul(c, da, db) } else { Q::one() }
          match (xa, xb) {
            (Some(x), Some(y)) => (sf(x, y, na, nb, da, db, c), d)
            _ => (None, d)
          }
        }
      }
    // ── N-32 新構造子 ─────────────────────────────────────
    SExt(a, k) =>
      match spec.pext {
        None => {
          let g = e.sgram_cost(c)
          let d = if spec.paux { qdet_gauss(g, c) } else { Q::one() }
          ((spec.pleaf)(g, c), d)
        }
        Some(xf) => {
          let (xa, da) = synth_spec_aux(spec, a, c)
          let n = a.sdim()
          // Sylvester–Franke：det Cₖ(G) = det(G)^{C(n−1,k−1)}
          let d = if spec.paux {
            qpow_fast(c, da, sf_exponent(n, k))
          } else {
            Q::one()
          }
          match xa {
            Some(x) => (xf(x, k, n, da, c), d)
            None => (None, d)
          }
        }
      }
    STwist(a, m) =>
      match spec.ptwist {
        None => {
          let g = e.sgram_cost(c)
          let d = if spec.paux { qdet_gauss(g, c) } else { Q::one() }
          ((spec.pleaf)(g, c), d)
        }
        Some(tf) => {
          let (xa, da) = synth_spec_aux(spec, a, c)
          let n = a.sdim()
          // det(AᵀGA) = det(A)²·det(G)
          let d = if spec.paux {
            let dm = qdet_gauss(m, c)
            cq_mul(c, cq_mul(c, dm, dm), da)
          } else {
            Q::one()
          }
          match xa {
            Some(x) => (tf(x, m, n, da, c), d)
            None => (None, d)
          }
        }
      }
    // 子空間與 ⊞ 於精確 ℚ 軌無一般之分解律（S 非方陣時 det 無乘積律；
    // A⊞B 之行列式為 ∏(λᵢ+μⱼ)，不是有理運算）—— 一律攤平。
    SSub(_, _) | SKSum(_, _) => {
      let g = e.sgram_cost(c)
      let d = if spec.paux { qdet_gauss(g, c) } else { Q::one() }
      ((spec.pleaf)(g, c), d)
    }
    SDual(a) => {
      let (xa, da) = if spec.pdual_phi {
        synth_spec_aux(spec, a, c)
      } else if spec.paux {
        let (_, dd) = synth_spec_aux(spec, a, c)
        (None, dd)
      } else {
        (None, Q::one())
      }
      // det(A*) = 1 / det(A)。da 為 Gram 之行列式，Gram 正定故恆非零；
      // 仍以 match 處理 None，不以 unwrap 掩蓋。
      let d = if spec.paux {
        match cq_div(c, Q::one(), da) {
          Some(x) => x
          None => Q::one()
        }
      } else {
        Q::one()
      }
      ((spec.pdual)(a, xa, c), d)
    }
  }
}

///|
/// 多態 catamorphism（只取 Φ 值）。
pub fn synth_spec(spec : PhiSpec, e : SpaceExpr, c : Cost) -> Mat[Q]? {
  let (v, _) = synth_spec_aux(spec, e, c)
  v
}

///|
/// 攤平法：先把整棵樹的 Gram 算出來，再直接施以 Φ。這是合成法的對照基準。
pub fn synth_flat(spec : PhiSpec, e : SpaceExpr, c : Cost) -> Mat[Q]? {
  (spec.pleaf)(e.sgram_cost(c), c)
}

// ---------------------------------------------------------------------------
// 葉演算法登記簿與規則登記簿 —— 兩張表即為「搜尋引擎 → 合成器」之接線
// ---------------------------------------------------------------------------

///|
/// 由 Φ 之名稱取出葉上算法。名稱與 `law_search` 之 Φ 表一致。
pub fn phi_leaf_of(name : String) -> ((Mat[Q], Cost) -> Mat[Q]?)? {
  match name {
    "inv" => Some((a, c) => qinv_gauss(a, c))
    "sq" => Some((a, c) => Some(qmul_cost(c, a, a)))
    "cube" => Some((a, c) => Some(qmul_cost(c, a, qmul_cost(c, a, a))))
    "adj" => Some((a, c) => qadj(c, a))
    "det" => Some((a, c) => Some(q_scalar_mat(qdet_gauss(a, c))))
    "trace" => Some((a, c) => Some(q_scalar_mat(qtrace(c, a))))
    "rank" => Some((a, _c) => Some(q_scalar_mat(Q::of_int(mrank(a)))))
    _ => None
  }
}

///|
/// 由規則之名稱取出合成函式。名稱與 `law_search` 之 ⊙ 表一致。
///
/// 六條規則涵蓋定律表中全部出現過的 ⊙。
pub fn rule_of(
  name : String,
) -> ((Mat[Q], Mat[Q], Int, Int, Q, Q, Cost) -> Mat[Q]?)? {
  match name {
    "⊗" => Some((x, y, _na, _nb, _da, _db, c) => Some(qkron_cost(c, x, y)))
    "⊕" => Some((x, y, _na, _nb, _da, _db, _c) => Some(qblock_diag(x, y)))
    // Sylvester 型：需要兩側行列式 —— 這就是 adj 不自給自足的地方
    "⊗ₛ" =>
      Some((x, y, na, nb, da, db, c) => {
        let s = cq_mul(c, qpow_fast(c, da, nb - 1), qpow_fast(c, db, na - 1))
        Some(qsmul_cost(c, s, qkron_cost(c, x, y)))
      })
    "·" =>
      Some((x, y, _na, _nb, _da, _db, c) => {
        Some(q_scalar_mat(cq_mul(c, x.data[0], y.data[0])))
      })
    "+" =>
      Some((x, y, _na, _nb, _da, _db, c) => {
        Some(q_scalar_mat(cq_add(c, x.data[0], y.data[0])))
      })
    // det 型：Φ(A)^{dim B} · Φ(B)^{dim A}
    "^" =>
      Some((x, y, na, nb, _da, _db, c) => {
        Some(
          q_scalar_mat(
            cq_mul(c, qpow_fast(c, x.data[0], nb), qpow_fast(c, y.data[0], na)),
          ),
        )
      })
    _ => None
  }
}

///|
/// 對偶節點之規則。只有少數 Φ 在對偶上有律；其餘一律攤平。
fn dual_of(name : String) -> (Bool, (SpaceExpr, Mat[Q]?, Cost) -> Mat[Q]?) {
  match name {
    // 定理 173-2：G(A*)⁻¹ = G_A，右式零次消去
    "inv" => (false, (a, _x, c) => Some(a.sgram_cost(c)))
    // det(A*) = 1 / det(A)
    "det" =>
      (
        true,
        (_a, x, c) => {
          match x {
            Some(m) =>
              match cq_div(c, Q::one(), m.data[0]) {
                Some(r) => Some(q_scalar_mat(r))
                None => None
              }
            None => None
          }
        },
      )
    // Gram 為正定故必滿秩：rank(A*) = dim A，零成本
    "rank" => (false, (a, _x, _c) => Some(q_scalar_mat(Q::of_int(a.sdim()))))
    // 其餘無律：攤平（先求對偶之 Gram，再直接施以 Φ）
    _ =>
      (
        false,
        (a, _x, c) => {
          match phi_leaf_of(name) {
            Some(f) => {
              let g = a.sgram_cost(c)
              match qinv_gauss(g, c) {
                Some(gi) => f(gi, c)
                None => None
              }
            }
            None => None
          }
        },
      )
  }
}

///|
/// **本檔的重點：由定律表自動組裝一個合成器。**
///
/// 給定 Φ 之名稱，到定律表裡查它在 ⊗ 與 ⊕ 上各自成立的規則，
/// 組出 `PhiSpec`。全程不需要人讀報告、不需要人手寫遞迴函式。
///
/// 回傳 None 的情形：Φ 不在登記簿裡，或它在 ⊗／⊕ 上都找不到成立的律。
pub fn phispec_from_law(tbl : Array[LawCand], phi : String) -> PhiSpec? {
  let leaf = match phi_leaf_of(phi) {
    Some(f) => f
    None => return None
  }
  // 掃定律表，找出此 Φ 在 ⊗ 與 ⊕ 上成立的規則
  let mut kname = ""
  let mut sname = ""
  for t in tbl {
    if t.cphi == phi && t.cholds {
      if t.ccomb == "⊗" && kname == "" {
        kname = t.crule
      }
      if t.ccomb == "⊕" && sname == "" {
        sname = t.crule
      }
    }
  }
  // 部分覆蓋是常態而非例外：adj 在 ⊗ 上有律（⊗ₛ）、在 ⊕ 上沒有。
  // 兩個構造子都沒律才算組裝失敗；只缺一個就讓那種節點走攤平。
  if kname == "" && sname == "" {
    return None
  }
  let kf = if kname == "" { None } else { rule_of(kname) }
  let sf = if sname == "" { None } else { rule_of(sname) }
  let (dphi, df) = dual_of(phi)
  let (xn, xf) = ext_of(phi)
  let (tn, tf2) = twist_of(phi)
  Some({
    pxname: xn,
    pext: xf,
    ptname: tn,
    ptwist: tf2,
    pname: phi,
    pleaf: leaf,
    pkname: kname,
    pkron: kf,
    psname: sname,
    psum: sf,
    pdual_phi: dphi,
    pdual: df,
    // ⊗ₛ 是唯一需要輔助行列式的規則
    paux: kname == "⊗ₛ" || sname == "⊗ₛ",
  })
}

///|
/// 合成法 vs 攤平法之對照（同軌，精確 ℚ）。
///
/// 回傳 (兩法結果相同, 攤平成本, 合成成本, 表達式標籤, 維數)。
pub fn synth_spec_compare(
  spec : PhiSpec,
  e : SpaceExpr,
) -> (Bool, Int64, Int64, String, Int) {
  let cd = Cost::new()
  let flat = synth_flat(spec, e, cd)
  let cf = Cost::new()
  let syn = synth_spec(spec, e, cf)
  let same = match (flat, syn) {
    (Some(x), Some(y)) => x.equals(y)
    (None, None) => true
    _ => false
  }
  (same, cd.wmul, cf.wmul, e.slabel(), e.sdim())
}

///|
/// 隨機表達式樹，不含對偶節點，**形狀受控**。
///
/// 為何不沿用 `rand_expr` 的「超過維數上限就退回葉」策略：那個策略在上限偏小時
/// 會讓整棵樹塌成單一葉子，於是合成法與攤平法走同一條路、增益恆為 ×1.0 ——
/// 量到的不是「律沒用」，而是「根本沒有樹」。本函式改為固定深度的滿二元樹，
/// 以葉維數控制規模：深度 d、葉維 k 時，維數介於 k·2^d（全為 ⊕）與 k^{2^d}（全為 ⊗）之間。
///
/// 對偶節點另行排除：對偶之 Gram 為 G⁻¹，攤平法與合成法**都得付**這次求逆，
/// 它是共模訊號，會把其他構造子上的真實差距稀釋掉（命題 194-6）。
pub fn rand_expr_nodual(rng : Rng, depth : Int, leafdim : Int) -> SpaceExpr {
  if depth <= 0 {
    return SLeaf("L", rand_gram(rng, leafdim))
  }
  let l = rand_expr_nodual(rng, depth - 1, leafdim)
  let r = rand_expr_nodual(rng, depth - 1, leafdim)
  if rng.next_below(2) == 0 {
    STensor(l, r)
  } else {
    SSum(l, r)
  }
}

// ---------------------------------------------------------------------------
// N-32：新構造子之規則登記簿
//
// ⚠️ 來源與 ⊗／⊕ 不同，必須說清楚：
//   ⊗ 與 ⊕ 的規則是**由 N-13 的搜尋引擎尋獲**，經定律表傳給組裝器；
//   Λᵏ 與同餘的規則是**人證出來的**（N-10 Sylvester–Franke、N-08 同餘），
//   這裡只是把它們登記起來供組裝器取用。
// 原因是搜尋引擎的組合子集目前只有 {⊗, ⊕, ⊞}，看不見 Λᵏ 與同餘。
// 把這兩個構造子放進搜尋空間是 N-33 之後的工作；在那之前，本登記簿是
// 「已證之律」與「自動組裝」之間誠實的接縫。
// ---------------------------------------------------------------------------

///|
/// Λᵏ 節點之規則。
fn ext_of(name : String) -> (String, ((Mat[Q], Int, Int, Q, Cost) -> Mat[Q]?)?) {
  match name {
    // Cₖ(G)⁻¹ = Cₖ(G⁻¹)：複合矩陣與求逆可交換
    "inv" => ("Cₖ∘inv", Some((x, k, _n, _d, c) => Some(compound(x, k, c))))
    // Sylvester–Franke：det Cₖ(G) = det(G)^{C(n−1,k−1)}（N-10，實測 ×92）
    "det" =>
      (
        "^C(n−1,k−1)",
        Some((x, k, n, _d, c) => {
          Some(q_scalar_mat(qpow_fast(c, x.data[0], sf_exponent(n, k))))
        }),
      )
    // Gram 正定 ⇒ Cₖ(G) 正定 ⇒ 滿秩：rank = C(n,k)，零成本
    "rank" =>
      (
        "C(n,k)",
        Some((_x, k, n, _d, _c) => Some(q_scalar_mat(Q::of_int(binom(n, k))))),
      )
    _ => ("", None)
  }
}

///|
/// 同餘節點之規則。
fn twist_of(
  name : String,
) -> (String, ((Mat[Q], Mat[Q], Int, Q, Cost) -> Mat[Q]?)?) {
  match name {
    // (AᵀGA)⁻¹ = A⁻¹G⁻¹A⁻ᵀ
    "inv" =>
      (
        "A⁻¹·Φ·A⁻ᵀ",
        Some((x, m, _n, _d, c) => {
          match qinv_gauss(m, c) {
            Some(mi) => Some(qmul_cost(c, qmul_cost(c, mi, x), mi.transpose()))
            None => None
          }
        }),
      )
    // det(AᵀGA) = det(A)²·det(G)
    "det" =>
      (
        "det(A)²·Φ",
        Some((x, m, _n, _d, c) => {
          let dm = qdet_gauss(m, c)
          Some(q_scalar_mat(cq_mul(c, cq_mul(c, dm, dm), x.data[0])))
        }),
      )
    // A 可逆 ⇒ 同餘保秩：rank = n，零成本
    "rank" =>
      ("n", Some((_x, _m, n, _d, _c) => Some(q_scalar_mat(Q::of_int(n)))))
    _ => ("", None)
  }
}

///|
/// n × m 滿列秩矩陣（m ≤ n），供 SSub 使用：取可逆方陣之前 m 行。
pub fn rand_tall(rng : Rng, n : Int, m : Int) -> Mat[Q] {
  let full = rand_invertible(rng, n)
  Mat::build(n, m, (i, j) => full.at(i, j))
}

///|
/// 擴編後之隨機表達式樹：八個構造子全上場。
///
/// 維數控制：Λᵏ 固定取 k = 2（C(n,2) = n(n−1)/2），子空間固定降一維。
/// 深度 2、葉維 2 時維數上界約 16，與 N-31 同量級。
pub fn rand_expr_ext(rng : Rng, depth : Int, leafdim : Int) -> SpaceExpr {
  if depth <= 0 {
    return SLeaf("L", rand_gram(rng, leafdim))
  }
  let sub = rand_expr_ext(rng, depth - 1, leafdim)
  let n = sub.sdim()
  match rng.next_below(7) {
    0 => STensor(sub, rand_expr_ext(rng, depth - 1, leafdim))
    1 => SSum(sub, rand_expr_ext(rng, depth - 1, leafdim))
    2 => SDual(sub)
    3 => if n >= 3 { SExt(sub, 2) } else { sub }
    4 => STwist(sub, rand_invertible(rng, n))
    5 => if n >= 2 { SSub(sub, rand_tall(rng, n, n - 1)) } else { sub }
    _ => SKSum(sub, rand_expr_ext(rng, depth - 1, leafdim))
  }
}

///|
/// 深度 ≤ d 之表達式樹型態數（葉視為單一型態）。
///
/// `T(0) = 1`，`T(d) = 1 + nbin·T(d−1)² + nun·T(d−1)`。
/// 用來量化「構造子擴編」對搜尋空間的實際影響。
pub fn shape_count(d : Int, nbin : Int, nun : Int) -> Int64 {
  let mut t = 1L
  for _i in 0..<d {
    t = 1L + nbin.to_int64() * t * t + nun.to_int64() * t
  }
  t
}

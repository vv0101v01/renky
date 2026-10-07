///|
/// # N-53 中端規範化 —— 空間表達式的重寫系統
///
/// ## 定義（中端）
///
/// `SpaceExpr` 是本庫的空間中間表示（IR）：葉子是具體空間，內部節點是
/// 7 個構造子。N-50 的座標化重編把前端（載體各異的 `IPSpace[V,F]`）降到
/// 這個 IR；本條在 IR 上做**重寫**，N-54 再把 IR 降到特化的演算法。
///
/// ```text
///   前端              中端                     後端
///   IPSpace[V,F]  →  SpaceExpr（IR）      →   演算法
///   （35 個空間）     規範化 / 重寫             特化派工（N-54）
/// ```
///
/// ## 定義（重寫規則與兩個類別）
///
/// 一條重寫規則是 `e → e'`，且 ⟦e⟧ ≅ ⟦e'⟧。按它對 Gram 的作用分兩類：
///
/// ```text
///   類 A（Gram 逐元不變）：  G(e') = G(e)
///   類 B（置換同餘）：       G(e') = PᵀG(e)P，P 為置換矩陣
/// ```
///
/// 類 A 可以無條件套用：它換掉的只是**算法**，不是空間。類 B 換了基底的
/// 排序，空間仍同構（置換矩陣是等距），但 Gram 的元素位置會動，故與已釘死
/// 的指紋不相容 —— 本庫把它分出來，只在明文要求規範序時才套。
///
/// ## 規則表（類 A，10 條）
///
/// ```text
///   A1  (A*)*            → A                     對偶對合
///   A2  (A⊗B)*           → A* ⊗ B*               對偶穿過張量
///   A3  (A⊕B)*           → A* ⊕ B*               對偶穿過直和
///   A4  T[T[A,M],N]      → T[A, M·N]             扭曲融合
///   A5  U[U[A,S],T]      → U[A, S·T]             嵌入融合
///   A6  T[U[A,S],M]      → U[A, S·M]             扭曲吸收進嵌入
///   A7  (T[A,M])*        → T[A*, (M⁻¹)ᵀ]         對偶穿過扭曲（需 M 可逆）
///   A8  T[A,I] → A，U[A,I] → A                   單位扭曲／嵌入消去
///   A9  Λ¹A              → A                     一階外冪消去
///   A10 (A⊗B)⊗C → A⊗(B⊗C)，(A⊕B)⊕C → A⊕(B⊕C)     右結合正規序
/// ```
///
/// A10 之所以是類 A 而不是類 B：Kronecker 積與分塊對角皆嚴格結合，
/// 兩側算出的矩陣**逐元相同**，不只是同構。

///|
/// 一條重寫規則。
pub struct RwRule {
  rname : String
  /// 0 = 類 A（Gram 逐元不變），1 = 類 B（置換同餘）
  rkind : Int
  /// 於**根節點**嘗試一步；不適用回 None
  rstep : (SpaceExpr) -> SpaceExpr?
}

///|
/// 矩陣是否為單位矩陣。
pub fn rw_is_ident(m : Mat[Q]) -> Bool {
  if m.mrows != m.mcols {
    return false
  }
  m.equals(Mat::ident(m.mrows))
}

///|
/// 【註冊表】類 A 重寫規則。
pub fn rw_registry_a() -> Array[RwRule] {
  [
    {
      rname: "A1 對偶對合 (A*)* → A",
      rkind: 0,
      rstep: e => {
        match e {
          SDual(SDual(a)) => Some(a)
          _ => None
        }
      },
    },
    {
      rname: "A2 對偶穿過張量 (A⊗B)* → A*⊗B*",
      rkind: 0,
      rstep: e => {
        match e {
          SDual(STensor(a, b)) => Some(STensor(SDual(a), SDual(b)))
          _ => None
        }
      },
    },
    {
      rname: "A3 對偶穿過直和 (A⊕B)* → A*⊕B*",
      rkind: 0,
      rstep: e => {
        match e {
          SDual(SSum(a, b)) => Some(SSum(SDual(a), SDual(b)))
          _ => None
        }
      },
    },
    {
      rname: "A4 扭曲融合 T[T[A,M],N] → T[A,MN]",
      rkind: 0,
      rstep: e => {
        match e {
          STwist(STwist(a, m), n) => Some(STwist(a, m.times(n)))
          _ => None
        }
      },
    },
    {
      rname: "A5 嵌入融合 U[U[A,S],T] → U[A,ST]",
      rkind: 0,
      rstep: e => {
        match e {
          SSub(SSub(a, s), t) => Some(SSub(a, s.times(t)))
          _ => None
        }
      },
    },
    {
      rname: "A6 扭曲吸收 T[U[A,S],M] → U[A,SM]",
      rkind: 0,
      rstep: e => {
        match e {
          STwist(SSub(a, s), m) => Some(SSub(a, s.times(m)))
          _ => None
        }
      },
    },
    {
      rname: "A7 對偶穿過扭曲 (T[A,M])* → T[A*,(M⁻¹)ᵀ]",
      rkind: 0,
      rstep: e => {
        match e {
          SDual(STwist(a, m)) =>
            match minv(m) {
              Some(mi) => Some(STwist(SDual(a), mi.transpose()))
              None => None
            }
          _ => None
        }
      },
    },
    {
      rname: "A8 單位扭曲／嵌入消去",
      rkind: 0,
      rstep: e => {
        match e {
          STwist(a, m) => if rw_is_ident(m) { Some(a) } else { None }
          SSub(a, s) => if rw_is_ident(s) { Some(a) } else { None }
          _ => None
        }
      },
    },
    {
      rname: "A9 一階外冪消去 Λ¹A → A",
      rkind: 0,
      rstep: e => {
        match e {
          SExt(a, 1) => Some(a)
          _ => None
        }
      },
    },
    {
      rname: "A10 右結合正規序",
      rkind: 0,
      rstep: e => {
        match e {
          STensor(STensor(a, b), c) => Some(STensor(a, STensor(b, c)))
          SSum(SSum(a, b), c) => Some(SSum(a, SSum(b, c)))
          _ => None
        }
      },
    },
  ]
}

///|
/// 【註冊表】類 B 重寫規則（置換同餘，改變基底排序）。
pub fn rw_registry_b() -> Array[RwRule] {
  [
    {
      rname: "B1 直和交換律正規序（依標籤排序）",
      rkind: 1,
      rstep: e => {
        match e {
          SSum(a, b) =>
            if a.slabel() > b.slabel() {
              Some(SSum(b, a))
            } else {
              None
            }
          _ => None
        }
      },
    },
    {
      rname: "B2 張量交換律正規序（依標籤排序）",
      rkind: 1,
      rstep: e => {
        match e {
          STensor(a, b) =>
            if a.slabel() > b.slabel() {
              Some(STensor(b, a))
            } else {
              None
            }
          _ => None
        }
      },
    },
  ]
}

// ---------------------------------------------------------------------------
//  重寫引擎
// ---------------------------------------------------------------------------

///|
/// 以給定規則集對根節點嘗試一步；回傳 (新式, 規則名)。
pub fn rw_step_root(
  e : SpaceExpr,
  rules : Array[RwRule],
) -> (SpaceExpr, String)? {
  for r in rules {
    match (r.rstep)(e) {
      Some(x) => return Some((x, r.rname))
      None => ()
    }
  }
  None
}

///|
/// 最內層優先（innermost / 由下而上）一步。
pub fn rw_step_in(e : SpaceExpr, rules : Array[RwRule]) -> SpaceExpr? {
  // 先試子樹
  let sub : SpaceExpr? = match e {
    SLeaf(_, _) => None
    STensor(a, b) =>
      match rw_step_in(a, rules) {
        Some(x) => Some(STensor(x, b))
        None =>
          match rw_step_in(b, rules) {
            Some(y) => Some(STensor(a, y))
            None => None
          }
      }
    SSum(a, b) =>
      match rw_step_in(a, rules) {
        Some(x) => Some(SSum(x, b))
        None =>
          match rw_step_in(b, rules) {
            Some(y) => Some(SSum(a, y))
            None => None
          }
      }
    SKSum(a, b) =>
      match rw_step_in(a, rules) {
        Some(x) => Some(SKSum(x, b))
        None =>
          match rw_step_in(b, rules) {
            Some(y) => Some(SKSum(a, y))
            None => None
          }
      }
    SDual(a) =>
      match rw_step_in(a, rules) {
        Some(x) => Some(SDual(x))
        None => None
      }
    SExt(a, k) =>
      match rw_step_in(a, rules) {
        Some(x) => Some(SExt(x, k))
        None => None
      }
    STwist(a, m) =>
      match rw_step_in(a, rules) {
        Some(x) => Some(STwist(x, m))
        None => None
      }
    SSub(a, s) =>
      match rw_step_in(a, rules) {
        Some(x) => Some(SSub(x, s))
        None => None
      }
  }
  match sub {
    Some(x) => Some(x)
    None =>
      match rw_step_root(e, rules) {
        Some((x, _)) => Some(x)
        None => None
      }
  }
}

///|
/// 最外層優先（outermost / 由上而下）一步。
pub fn rw_step_out(e : SpaceExpr, rules : Array[RwRule]) -> SpaceExpr? {
  match rw_step_root(e, rules) {
    Some((x, _)) => return Some(x)
    None => ()
  }
  match e {
    SLeaf(_, _) => None
    STensor(a, b) =>
      match rw_step_out(a, rules) {
        Some(x) => Some(STensor(x, b))
        None =>
          match rw_step_out(b, rules) {
            Some(y) => Some(STensor(a, y))
            None => None
          }
      }
    SSum(a, b) =>
      match rw_step_out(a, rules) {
        Some(x) => Some(SSum(x, b))
        None =>
          match rw_step_out(b, rules) {
            Some(y) => Some(SSum(a, y))
            None => None
          }
      }
    SKSum(a, b) =>
      match rw_step_out(a, rules) {
        Some(x) => Some(SKSum(x, b))
        None =>
          match rw_step_out(b, rules) {
            Some(y) => Some(SKSum(a, y))
            None => None
          }
      }
    SDual(a) =>
      match rw_step_out(a, rules) {
        Some(x) => Some(SDual(x))
        None => None
      }
    SExt(a, k) =>
      match rw_step_out(a, rules) {
        Some(x) => Some(SExt(x, k))
        None => None
      }
    STwist(a, m) =>
      match rw_step_out(a, rules) {
        Some(x) => Some(STwist(x, m))
        None => None
      }
    SSub(a, s) =>
      match rw_step_out(a, rules) {
        Some(x) => Some(SSub(x, s))
        None => None
      }
  }
}

///|
/// 反覆重寫至範式（最多 `fuel` 步）。`inner = true` 用最內層優先。
pub fn rw_normalize(
  e : SpaceExpr,
  rules : Array[RwRule],
  inner : Bool,
  fuel : Int,
) -> (SpaceExpr, Int) {
  let mut cur = e
  let mut n = 0
  for _t in 0..<fuel {
    let nx = if inner {
      rw_step_in(cur, rules)
    } else {
      rw_step_out(cur, rules)
    }
    match nx {
      Some(x) => {
        cur = x
        n = n + 1
      }
      None => return (cur, n)
    }
  }
  (cur, n)
}

///|
/// 標準範式：只用類 A，最內層優先，燃料 200。
pub fn normalize(e : SpaceExpr) -> SpaceExpr {
  rw_normalize(e, rw_registry_a(), true, 200).0
}

///|
/// 規範形：類 A + 類 B（明文要求規範序時才用）。
pub fn canonicalize(e : SpaceExpr) -> SpaceExpr {
  let both : Array[RwRule] = []
  for r in rw_registry_a() {
    both.push(r)
  }
  for r in rw_registry_b() {
    both.push(r)
  }
  rw_normalize(e, both, true, 400).0
}

// ---------------------------------------------------------------------------
//  終止性測度
// ---------------------------------------------------------------------------

///|
/// 節點數。
pub fn rw_size(e : SpaceExpr) -> Int {
  match e {
    SLeaf(_, _) => 1
    STensor(a, b) => 1 + rw_size(a) + rw_size(b)
    SSum(a, b) => 1 + rw_size(a) + rw_size(b)
    SKSum(a, b) => 1 + rw_size(a) + rw_size(b)
    SDual(a) => 1 + rw_size(a)
    SExt(a, _) => 1 + rw_size(a)
    STwist(a, _) => 1 + rw_size(a)
    SSub(a, _) => 1 + rw_size(a)
  }
}

///|
/// 對偶負重：Σ_{每個 SDual 節點} (其子樹之節點數)。
/// A1／A2／A3／A7 都嚴格降低它（把對偶往葉子推）。
pub fn rw_dualw(e : SpaceExpr) -> Int {
  match e {
    SLeaf(_, _) => 0
    STensor(a, b) => rw_dualw(a) + rw_dualw(b)
    SSum(a, b) => rw_dualw(a) + rw_dualw(b)
    SKSum(a, b) => rw_dualw(a) + rw_dualw(b)
    SDual(a) => rw_size(a) + rw_dualw(a)
    SExt(a, _) => rw_dualw(a)
    STwist(a, _) => rw_dualw(a)
    SSub(a, _) => rw_dualw(a)
  }
}

///|
/// 左重：Σ_{每個二元節點} (其左子樹之節點數)。A10 嚴格降低它。
pub fn rw_leftw(e : SpaceExpr) -> Int {
  match e {
    SLeaf(_, _) => 0
    STensor(a, b) => rw_size(a) + rw_leftw(a) + rw_leftw(b)
    SSum(a, b) => rw_size(a) + rw_leftw(a) + rw_leftw(b)
    SKSum(a, b) => rw_size(a) + rw_leftw(a) + rw_leftw(b)
    SDual(a) => rw_leftw(a)
    SExt(a, _) => rw_leftw(a)
    STwist(a, _) => rw_leftw(a)
    SSub(a, _) => rw_leftw(a)
  }
}

///|
/// 終止測度 μ(e) = (對偶負重, 節點數, 左重)，字典序。
///
/// 定理 N53-2（終止性）：每條類 A 規則都使 μ 嚴格下降。
///   A1 A2 A3 A7 降第一欄（把對偶往下推／消去，對偶子樹變小）；
///   A4 A5 A6 A8 A9 第一欄不升、第二欄降（節點變少）；
///   A10 前兩欄不變、第三欄降（右結合）。
/// μ 取值於 ℕ³ 之字典序（良基），故重寫必終止。
pub fn rw_measure(e : SpaceExpr) -> (Int, Int, Int) {
  (rw_dualw(e), rw_size(e), rw_leftw(e))
}

///|
/// 字典序嚴格小於。
pub fn rw_mlt(x : (Int, Int, Int), y : (Int, Int, Int)) -> Bool {
  if x.0 != y.0 {
    return x.0 < y.0
  }
  if x.1 != y.1 {
    return x.1 < y.1
  }
  x.2 < y.2
}

// ---------------------------------------------------------------------------
//  健全性與效益
// ---------------------------------------------------------------------------

///|
/// 類 A 之健全性：Gram 逐元相同。
pub fn rw_sound_a(e : SpaceExpr) -> Bool {
  let n = normalize(e)
  if n.sdim() != e.sdim() {
    return false
  }
  n.sgram().equals(e.sgram())
}

///|
/// 類 B 之健全性：維數、行列式、跡相同（置換同餘之不變量）。
pub fn rw_sound_b(e : SpaceExpr) -> Bool {
  let c = canonicalize(e)
  if c.sdim() != e.sdim() {
    return false
  }
  let g1 = e.sgram()
  let g2 = c.sgram()
  Q::eq(mdet(g1), mdet(g2)) && Q::eq(g1.trace(), g2.trace())
}

///|
/// 效益：規範化前後物化 Gram 的字乘法次數。
/// 回傳 (直接, 規範化後, 兩者 Gram 是否相同)。
pub fn rw_cost_pair(e : SpaceExpr) -> (Int64, Int64, Bool) {
  let c1 = Cost::new()
  let g1 = e.sgram_cost(c1)
  let n = normalize(e)
  let c2 = Cost::new()
  let g2 = n.sgram_cost(c2)
  (c1.wmul, c2.wmul, g1.equals(g2))
}

///|
/// 合流性實測：最內層優先與最外層優先之範式是否相同（標籤與 Gram 皆比）。
pub fn rw_confluent(e : SpaceExpr) -> Bool {
  let ra = rw_registry_a()
  let a = rw_normalize(e, ra, true, 400).0
  let b = rw_normalize(e, ra, false, 400).0
  a.slabel() == b.slabel() && a.sgram().equals(b.sgram())
}

///|
/// 冪等性：normalize(normalize(e)) 之標籤與 normalize(e) 相同。
pub fn rw_idempotent(e : SpaceExpr) -> Bool {
  let a = normalize(e)
  normalize(a).slabel() == a.slabel()
}

///|
/// 範式性：範式上再也套不出任何類 A 規則。
pub fn rw_is_normal(e : SpaceExpr) -> Bool {
  rw_step_in(e, rw_registry_a()) is None
}

// ---------------------------------------------------------------------------
//  測試語料
// ---------------------------------------------------------------------------

///|
/// 中端測試語料：刻意把每條規則的觸發形狀都放進去，
/// 外加由 `rand_expr` 生成的隨機樹。
pub fn rw_corpus(rng : Rng) -> Array[SpaceExpr] {
  let g2 = rand_gram(rng, 2)
  let g3 = rand_gram(rng, 3)
  let a : SpaceExpr = SLeaf("A2", g2)
  let b : SpaceExpr = SLeaf("B3", g3)
  let c : SpaceExpr = SLeaf("C2", rand_gram(rng, 2))
  let m = comb_unitri(2)
  let n2 : Mat[Q] = Mat::build(2, 2, (i, j) => {
    if i == j {
      Q::of_int(2)
    } else if i == 0 {
      Q::one()
    } else {
      Q::zero()
    }
  })
  let s = comb_embed(3, 2)
  let out : Array[SpaceExpr] = [
    SDual(SDual(a)), // A1
    SDual(STensor(a, b)), // A2
    SDual(SSum(a, b)), // A3
    STwist(STwist(a, m), n2), // A4
    SSub(SSub(b, s), comb_unitri(2)), // A5
    STwist(SSub(b, s), m), // A6
    SDual(STwist(a, m)), // A7
    STwist(a, Mat::ident(2)), // A8
    SExt(a, 1), // A9
    STensor(STensor(a, c), b), // A10
    SSum(SSum(a, c), b), // A10
    SDual(STensor(STensor(a, c), b)), // A2 + A10
    SDual(SDual(SDual(STensor(a, b)))), // A1 + A2
    SDual(SSum(STensor(a, b), SDual(c))), // A3 + A2 + A1
    SExt(SDual(SDual(a)), 2),
    SKSum(SDual(SDual(a)), b),
  ]
  for _t in 0..<24 {
    out.push(rand_expr(rng, 3, 24))
  }
  out
}

///|
/// 中端總表：對語料逐條量測，回傳
/// (條數, 健全 A, 健全 B, 合流, 冪等, 範式, 測度下降, 直接總成本, 規範後總成本)。
pub fn rw_scan(rng : Rng) -> (Int, Int, Int, Int, Int, Int, Int, Int64, Int64) {
  let xs = rw_corpus(rng)
  let mut sa = 0
  let mut sb = 0
  let mut cf = 0
  let mut idm = 0
  let mut nf = 0
  let mut dec = 0
  let mut c1 : Int64 = 0
  let mut c2 : Int64 = 0
  for e in xs {
    if rw_sound_a(e) {
      sa = sa + 1
    }
    if rw_sound_b(e) {
      sb = sb + 1
    }
    if rw_confluent(e) {
      cf = cf + 1
    }
    if rw_idempotent(e) {
      idm = idm + 1
    }
    if rw_is_normal(normalize(e)) {
      nf = nf + 1
    }
    // 測度：範式之 μ 不大於原式之 μ，且有重寫發生時嚴格下降
    let m0 = rw_measure(e)
    let m1 = rw_measure(normalize(e))
    if rw_mlt(m1, m0) || (m1.0 == m0.0 && m1.1 == m0.1 && m1.2 == m0.2) {
      dec = dec + 1
    }
    let (d, nn, _) = rw_cost_pair(e)
    c1 = c1 + d
    c2 = c2 + nn
  }
  (xs.length(), sa, sb, cf, idm, nf, dec, c1, c2)
}

///|
/// 逐規則之單步驗證：每條規則在其觸發形狀上，
/// (Gram 是否逐元不變, 測度是否嚴格下降)。
pub fn rw_rule_check(rng : Rng) -> Array[(String, Bool, Bool, Bool)] {
  let xs = rw_corpus(rng)
  let out : Array[(String, Bool, Bool, Bool)] = []
  for r in rw_registry_a() {
    let mut fired = false
    let mut gram_ok = true
    let mut meas_ok = true
    for e in xs {
      // 在語料的每個子位置上嘗試該條規則（只看根節點觸發者）
      match (r.rstep)(e) {
        Some(x) => {
          fired = true
          if !x.sgram().equals(e.sgram()) {
            gram_ok = false
          }
          if !rw_mlt(rw_measure(x), rw_measure(e)) {
            meas_ok = false
          }
        }
        None => ()
      }
    }
    out.push((r.rname, fired, gram_ok, meas_ok))
  }
  out
}

///|
/// 中端指紋：語料條數、範式標籤之雜湊、總成本。
pub fn rw_digest(rng : Rng) -> String {
  let xs = rw_corpus(rng)
  let mut h : UInt64 = 0xcbf2_9ce4_8422_2325UL
  for e in xs {
    h = (h ^ str_hash64(normalize(e).slabel())) * 0x1000_0000_01b3UL
  }
  xs.length().to_string() + ":" + (h % 1000000007UL).to_string()
}

///|
/// 範式與原式的逐式成本比較：(變便宜, 不變, 變貴)。
///
/// 命題 N53-5（A10 不是為了成本而設）：右結合正規序只搬括號，不消節點，
/// 它存在的理由是合流 —— 沒有它，⊗ 的不同結合方式會停在不同的範式上。
/// 單看成本它甚至可能略微變貴；聚合效益由 A1–A9 提供。
pub fn rw_cost_profile(rng : Rng) -> (Int, Int, Int) {
  let mut cheap = 0
  let mut same = 0
  let mut dear = 0
  for e in rw_corpus(rng) {
    let (d, n, _) = rw_cost_pair(e)
    if n < d {
      cheap = cheap + 1
    } else if n == d {
      same = same + 1
    } else {
      dear = dear + 1
    }
  }
  (cheap, same, dear)
}

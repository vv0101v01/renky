///|
/// # 第九輪：一元構造子的算子層規則
///
/// ## 類 C 原本只走二元
///
/// N-66 把 N-40 的合成器接進中端，但合成器只會處理 `Φ(A ⊗ B)`，
/// 再加一條手寫的 `Φ(A ⊕ B)`。對偶、扭曲、外冪這三個一元構造子
/// 一條規則也沒有 —— 而它們恰好是 IR 裡最常出現的。
///
/// ## 要找的規則長什麼樣
///
/// ```text
///   Φ(U(G)) = det(G)^{e} · U′(Φ(G))
/// ```
///
/// 一元構造子 U、它在算子那一側的對應 U′、以及一個純量修正 det(G)^e。
/// 和 N-40 一樣，**e 不是人填的**：合成器先在幾個尺寸上量出 e，
/// 再擬合成 n（與外冪的 k）的仿射函數，最後用保留樣本驗證。
///
/// ## 三條預期與一條意外
///
/// 手推會給出：對偶對每個 Φ 都通勤（U′ = 對偶，e = 0）；
/// 扭曲只對轉置通勤（inv 要改用 M⁻ᵀ）；外冪由 Cauchy–Binet 對
/// inv／sq／cube／轉置通勤。意外在 adj 遇上外冪 ——
/// `adj(C_k(G)) = det(G)^{C(n−1,k−1)}·C_k(G⁻¹)` 而
/// `C_k(adj G) = det(G)^{k}·C_k(G⁻¹)`，兩者差一個 `det(G)^{C(n−1,k−1)−k}`。
/// 這個指數不是常數，它隨 n 與 k 變 —— 正好是合成器該去量的東西。

///|
/// 一元算子層規則。
pub struct UniRule {
  /// 構造子名稱
  uctor : String
  /// Φ 名稱
  uphi : String
  /// 是否找得到規則
  uholds : Bool
  /// 算子側對應之構造子（"同"／"轉置逆"／"—"）
  udual : String
  /// 修正指數 e = ue0 + ue1·n + ue2·k
  ue0 : Int
  ue1 : Int
  ue2 : Int
}

///|
pub fn UniRule::describe(self : UniRule) -> String {
  if !self.uholds {
    "—"
  } else {
    let e = self.ue0 + 0 * self.ue1
    let _ = e
    let mut s = ""
    if self.ue0 != 0 || self.ue1 != 0 || self.ue2 != 0 {
      s = "det(G)^{"
      let mut first = true
      let terms : Array[(Int, String)] = [
        (self.ue1, "n"),
        (self.ue2, "k"),
        (self.ue0, ""),
      ]
      for t in terms {
        let (co, sym) = t
        if co != 0 {
          let mag = if co < 0 { -co } else { co }
          let body = if sym == "" {
            mag.to_string()
          } else if mag == 1 {
            sym
          } else {
            mag.to_string() + sym
          }
          if first {
            s = s + (if co < 0 { "−" } else { "" }) + body
            first = false
          } else {
            s = s + (if co < 0 { " − " } else { " + " }) + body
          }
        }
      }
      s = s + "}·"
    }
    s + self.udual
  }
}

///|
/// 支援負指數的冪：`qpow_fast` 對 e ≤ 0 一律回傳 1，
/// 用它去解指數會把 e = −8 誤判成成立。本函式先取逆再冪。
pub fn qpow_int(c : Cost, x : Q, e : Int) -> Q? {
  if e == 0 {
    return Some(Q::one())
  }
  if e > 0 {
    return Some(qpow_fast(c, x, e))
  }
  match Q::one().div(x) {
    None => None
    Some(xi) => Some(qpow_fast(c, xi, -e))
  }
}

///|
/// 找出整數 e 使 d^e = s。
///
/// 搜尋順序由 0 向外展開 —— 若存在多個解（例如 d = 1 時每個 e 都成立），
/// 取絕對值最小的那個，避免擬合到邊界值。
pub fn solve_exponent(d : Q, s : Q) -> Int? {
  if Q::is_zero(d) {
    return None
  }
  for a in 0..<=8 {
    for sg in [1, -1] {
      let e = a * sg
      if a == 0 && sg == -1 {
        continue
      }
      match qpow_int(Cost::new(), d, e) {
        Some(v) => if v.eq(s) { return Some(e) }
        None => ()
      }
    }
  }
  None
}

///|
/// 兩點擬合 e = e0 + e1·n（`fit_affine` 在第二座標固定時是奇異的）。
pub fn fit_affine_n(pts : Array[(Int, Int)]) -> (Int, Int)? {
  if pts.length() < 2 {
    return None
  }
  let (n0, v0) = pts[0]
  let (n1, v1) = pts[1]
  if n0 == n1 {
    return None
  }
  let dv = v1 - v0
  let dn = n1 - n0
  if dv % dn != 0 {
    return None
  }
  let e1 = dv / dn
  let e0 = v0 - e1 * n0
  for pt in pts {
    if e0 + e1 * pt.0 != pt.1 {
      return None
    }
  }
  Some((e0, e1))
}

///|
/// 在一個具體尺寸上量出 (Φ, 構造子) 的修正指數。
/// 回傳 None 表示沒有這種形式的規則。
pub fn measure_uni(
  phi : (Mat[Q], Cost) -> Mat[Q]?,
  ctor : String,
  dualside : String,
  n : Int,
  k : Int,
  rng : Rng,
) -> Int? {
  let g = rand_gram(rng, n)
  let c = Cost::new()
  // 左邊：Φ(U(G))
  let ug = match ctor {
    "對偶" =>
      match qinv_gauss(g, c) {
        Some(x) => x
        None => return None
      }
    "外冪" => compound(g, k, c)
    _ => {
      let m = comb_unitri(n)
      m.transpose().times(g).times(m)
    }
  }
  let lhs = match phi(ug, c) {
    Some(x) => x
    None => return None
  }
  // 右邊：U′(Φ(G))
  let pg = match phi(g, c) {
    Some(x) => x
    None => return None
  }
  let rhs = match ctor {
    "對偶" =>
      match qinv_gauss(pg, c) {
        Some(x) => x
        None => return None
      }
    "外冪" => compound(pg, k, c)
    _ => {
      let m = comb_unitri(n)
      let mm = if dualside == "轉置逆" {
        match qinv_gauss(m.transpose(), c) {
          Some(x) => x
          None => return None
        }
      } else {
        m
      }
      mm.transpose().times(pg).times(mm)
    }
  }
  if lhs.mrows != rhs.mrows || lhs.mcols != rhs.mcols {
    return None
  }
  match scalar_between(lhs, rhs) {
    None => None
    Some(s) => solve_exponent(qdet_gauss(g, c), s)
  }
}

///|
/// 合成一條一元規則：先擬合、再用保留樣本驗證。
///
/// 外冪的修正指數可能同時依賴 n 與 k，故用三點 (n,k) 仿射擬合；
/// 對偶與扭曲只依賴 n，用兩點 n 擬合（`fit_affine` 在 k 固定時奇異）。
pub fn synth_rule_uni(
  phiname : String,
  phi : (Mat[Q], Cost) -> Mat[Q]?,
  ctor : String,
  dualside : String,
  kfix : Int,
  rng : Rng,
) -> UniRule {
  let none : UniRule = {
    uctor: ctor,
    uphi: phiname,
    uholds: false,
    udual: "—",
    ue0: 0,
    ue1: 0,
    ue2: 0,
  }
  if ctor == "外冪" && kfix == 0 {
    // 三點 (n,k) 仿射擬合，兩點保留
    let fit : Array[(Int, Int)] = [(4, 2), (5, 2), (5, 3)]
    let hold : Array[(Int, Int)] = [(6, 2), (6, 3)]
    let pts : Array[(Int, Int, Int)] = []
    for sz in fit {
      match measure_uni(phi, ctor, dualside, sz.0, sz.1, rng) {
        None => return none
        Some(e) => pts.push((sz.0, sz.1, e))
      }
    }
    let co = match fit_affine(pts) {
      None => return none
      Some(x) => x
    }
    let (e0, e1, e2) = co
    for sz in hold {
      match measure_uni(phi, ctor, dualside, sz.0, sz.1, rng) {
        None => return none
        Some(e) => if e0 + e1 * sz.0 + e2 * sz.1 != e { return none }
      }
    }
    return {
      uctor: ctor,
      uphi: phiname,
      uholds: true,
      udual: dualside,
      ue0: e0,
      ue1: e1,
      ue2: e2,
    }
  }
  // 兩點 n 擬合（k 固定）
  let kk = if ctor == "外冪" { kfix } else { 1 }
  let fit : Array[Int] = if ctor == "外冪" { [4, 5] } else { [3, 4] }
  let hold : Array[Int] = if ctor == "外冪" { [6, 7] } else { [5, 6] }
  let pts : Array[(Int, Int)] = []
  for n in fit {
    match measure_uni(phi, ctor, dualside, n, kk, rng) {
      None => return none
      Some(e) => pts.push((n, e))
    }
  }
  let co = match fit_affine_n(pts) {
    None => return none
    Some(x) => x
  }
  let (e0, e1) = co
  for n in hold {
    match measure_uni(phi, ctor, dualside, n, kk, rng) {
      None => return none
      Some(e) => if e0 + e1 * n != e { return none }
    }
  }
  {
    uctor: ctor,
    uphi: phiname,
    uholds: true,
    udual: dualside,
    ue0: e0,
    ue1: e1,
    ue2: 0,
  }
}

///|
/// 一元規則表：每個 Φ × 每個一元構造子（扭曲試兩種算子側對應）。
pub fn uni_rule_table(rng : Rng) -> Array[UniRule] {
  let out : Array[UniRule] = []
  for pr in phi_mat_registry() {
    let (nm, phi) = pr
    out.push(synth_rule_uni(nm, phi, "對偶", "同", 0, rng))
    out.push(synth_rule_uni(nm, phi, "外冪", "同", 0, rng))
    // 扭曲：先試「同」，不成再試「轉置逆」
    let a = synth_rule_uni(nm, phi, "扭曲", "同", 0, rng)
    if a.uholds {
      out.push(a)
    } else {
      out.push(synth_rule_uni(nm, phi, "扭曲", "轉置逆", 0, rng))
    }
  }
  out
}

///|
/// 用一條一元規則求值 Φ(U(G))，回傳 (結果, 是否走了規則)。
pub fn uni_apply(
  r : UniRule,
  phi : (Mat[Q], Cost) -> Mat[Q]?,
  g : Mat[Q],
  k : Int,
  c : Cost,
) -> Mat[Q]? {
  if !r.uholds {
    return None
  }
  let n = g.mrows
  let pg = match phi(g, c) {
    Some(x) => x
    None => return None
  }
  let base = match r.uctor {
    "對偶" =>
      match qinv_gauss(pg, c) {
        Some(x) => x
        None => return None
      }
    "外冪" => compound(pg, k, c)
    _ => {
      let m = comb_unitri(n)
      let mm = if r.udual == "轉置逆" {
        match qinv_gauss(m.transpose(), c) {
          Some(x) => x
          None => return None
        }
      } else {
        m
      }
      qmul_cost(c, qmul_cost(c, mm.transpose(), pg), mm)
    }
  }
  let e = r.ue0 + r.ue1 * n + r.ue2 * k
  if e == 0 {
    Some(base)
  } else {
    let d = qdet_gauss(g, c)
    match qpow_int(c, d, e) {
      None => None
      Some(f) => Some(qsmul_cost(c, f, base))
    }
  }
}

///|
/// 直接路徑：先造 U(G) 再施加 Φ。
pub fn uni_direct(
  ctor : String,
  phi : (Mat[Q], Cost) -> Mat[Q]?,
  g : Mat[Q],
  k : Int,
  c : Cost,
) -> Mat[Q]? {
  let n = g.mrows
  let ug = match ctor {
    "對偶" =>
      match qinv_gauss(g, c) {
        Some(x) => x
        None => return None
      }
    "外冪" => compound(g, k, c)
    _ => {
      let m = comb_unitri(n)
      qmul_cost(c, qmul_cost(c, m.transpose(), g), m)
    }
  }
  phi(ug, c)
}

///|
/// 掃描：規則數、逐元相同數、成本對照。
///
/// 回傳 (檢查的 (Φ,構造子) 對數, 有規則數, 檢查實例數, 逐元相同數,
///        直接總成本, 走規則總成本, 走規則較便宜數)。
pub fn uni_scan(rng : Rng) -> (Int, Int, Int, Int, Int64, Int64, Int) {
  let tbl = uni_rule_table(rng)
  let phis = phi_mat_registry()
  let sizes : Array[(Int, Int)] = [(4, 2), (5, 2), (5, 3), (6, 2)]
  let mut holds = 0
  let mut inst = 0
  let mut same = 0
  let mut td = 0L
  let mut ts = 0L
  let mut win = 0
  for r in tbl {
    if !r.uholds {
      continue
    }
    holds = holds + 1
    let mut phi : ((Mat[Q], Cost) -> Mat[Q]?)? = None
    for pr in phis {
      if pr.0 == r.uphi {
        phi = Some(pr.1)
      }
    }
    match phi {
      None => ()
      Some(f) =>
        for sz in sizes {
          let g = rand_gram(rng, sz.0)
          let c1 = Cost::new()
          let d = uni_direct(r.uctor, f, g, sz.1, c1)
          let c2 = Cost::new()
          let s = uni_apply(r, f, g, sz.1, c2)
          inst = inst + 1
          match (d, s) {
            (Some(x), Some(y)) => if x.equals(y) { same = same + 1 }
            _ => ()
          }
          td = td + c1.wmul
          ts = ts + c2.wmul
          if c2.wmul < c1.wmul {
            win = win + 1
          }
        }
    }
  }
  (tbl.length(), holds, inst, same, td, ts, win)
}

///|
/// 兩側對照：把修正指數動一格，恆等式必須垮掉。
/// 回傳 (有規則數, 被推翻數)。
pub fn uni_control(rng : Rng) -> (Int, Int) {
  let tbl = uni_rule_table(rng)
  let phis = phi_mat_registry()
  let mut tot = 0
  let mut broken = 0
  for r in tbl {
    if !r.uholds {
      continue
    }
    tot = tot + 1
    let bad = {
      uctor: r.uctor,
      uphi: r.uphi,
      uholds: true,
      udual: r.udual,
      ue0: r.ue0 + 1,
      ue1: r.ue1,
      ue2: r.ue2,
    }
    let mut phi : ((Mat[Q], Cost) -> Mat[Q]?)? = None
    for pr in phis {
      if pr.0 == r.uphi {
        phi = Some(pr.1)
      }
    }
    match phi {
      None => ()
      Some(f) => {
        let g = rand_gram(rng, 5)
        let d = uni_direct(r.uctor, f, g, 2, Cost::new())
        let w = uni_apply(bad, f, g, 2, Cost::new())
        match (d, w) {
          (Some(x), Some(y)) => if !x.equals(y) { broken = broken + 1 }
          _ => broken = broken + 1
        }
      }
    }
  }
  (tot, broken)
}

///|
/// 指紋。
pub fn uni_digest(rng : Rng) -> String {
  let (n, h, i, s, td, ts, w) = uni_scan(rng)
  n.to_string() +
  ":" +
  h.to_string() +
  ":" +
  i.to_string() +
  ":" +
  s.to_string() +
  ":" +
  td.to_string() +
  ":" +
  ts.to_string() +
  ":" +
  w.to_string()
}

///|
/// 【假設類不夠寬的具名案例】adj ∘ 外冪。
///
/// 手推給出 adj(C_k(G)) = det(G)^{C(n−1,k−1)}·C_k(G⁻¹) 而
/// C_k(adj G) = det(G)^{k}·C_k(G⁻¹)，故修正指數為 C(n−1,k−1) − k。
/// 這個東西對 k = 2 是 n − 3（仿射），對 k = 3 是 (n−1)(n−2)/2 − 3（二次）。
/// 合成器的假設類只有仿射，所以放開 k 時它找不到規則；
/// **把 k 釘死在 2 就找得到**。這不是合成器壞了，是假設類不夠寬。
pub fn uni_adj_ext_k2(rng : Rng) -> UniRule {
  let mut phi : ((Mat[Q], Cost) -> Mat[Q]?)? = None
  for pr in phi_mat_registry() {
    if pr.0 == "adj" {
      phi = Some(pr.1)
    }
  }
  match phi {
    None =>
      {
        uctor: "外冪",
        uphi: "adj",
        uholds: false,
        udual: "—",
        ue0: 0,
        ue1: 0,
        ue2: 0,
      }
    Some(f) => synth_rule_uni("adj", f, "外冪", "同", 2, rng)
  }
}

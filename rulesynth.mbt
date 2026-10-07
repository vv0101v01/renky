///|
/// # N-40 規則合成 —— 由「選規則」改為「解出規則」
///
/// ## 動機
///
/// N-13 的引擎對 Sylvester 型的律
/// `adj(A⊗B) = (det A)^{m−1}(det B)^{n−1}(adj A ⊗ adj B)`
/// 所做的是**選**：候選係數 `(det A)^{m−1}(det B)^{n−1}` 登錄在 `rules_mat`
/// 內，引擎枚舉註冊表並裁決哪一條通過檢驗。
///
/// 本條改為**解**：給一個帶自由參數的待定式，由量測值解出參數。
/// 一族待定式即涵蓋該族全部係數，不需為每個係數各登錄一條規則。
///
/// ## 做法
///
/// 給定一個待定式（ansatz）
///
/// ```text
///     Φ(A ⊗ B) = (det A)^p · (det B)^q · (Φ(A) ⊗ Φ(B))
/// ```
///
/// 其中 `p`、`q` 是**未知的**、關於兩側維數的仿射函數
/// `p(n,m) = c₀ + c₁n + c₂m`。引擎的工作是把 `c₀, c₁, c₂` **解出來**：
///
/// 1. 對每組樣本量出標量 `s`，使 `Φ(A⊗B) = s · (Φ(A) ⊗ Φ(B))`（精確 ℚ）。
/// 2. 在小整數範圍內精確求出 `(p, q)` 使 `(det A)^p (det B)^q = s`。
/// 3. 由三組 `(n, m, p)` 解一個 3×3 的**精確 ℚ 線性系統**得 `c₀, c₁, c₂`。
/// 4. 在保留樣本上驗證。
///
/// 全程沒有任何一處寫過 `m − 1` 或 `n − 1`。這些係數是解出來的。

///|
/// 一條被合成出來的規則。
pub struct SynthRule {
  /// p(n,m) = sp0 + sp1·n + sp2·m
  sp0 : Int
  sp1 : Int
  sp2 : Int
  /// q(n,m) = sq0 + sq1·n + sq2·m
  sq0 : Int
  sq1 : Int
  sq2 : Int
}

///|
/// 以人看得懂的方式寫出 a + b·n + c·m。
fn affine_str(a : Int, b : Int, c : Int) -> String {
  let mut out = ""
  let mut first = true
  let terms : Array[(Int, String)] = [(b, "n"), (c, "m"), (a, "")]
  for t in terms {
    let (coef, sym) = t
    if coef != 0 {
      let mag = if coef < 0 { -coef } else { coef }
      let body = if sym == "" {
        mag.to_string()
      } else if mag == 1 {
        sym
      } else {
        mag.to_string() + sym
      }
      if first {
        out = (if coef < 0 { "−" } else { "" }) + body
        first = false
      } else {
        out = out + (if coef < 0 { " − " } else { " + " }) + body
      }
    }
  }
  if first {
    "0"
  } else {
    out
  }
}

///|
/// 規則之單行文字描述（Φ 名、指數 p(n,m)、q(n,m)）。
pub fn SynthRule::describe(self : SynthRule) -> String {
  "(det A)^{" +
  affine_str(self.sp0, self.sp1, self.sp2) +
  "}·(det B)^{" +
  affine_str(self.sq0, self.sq1, self.sq2) +
  "}"
}

///|
/// 本規則是否為恆等修正（p ≡ q ≡ 0），亦即樸素的 Φ(A)⊗Φ(B)。
pub fn SynthRule::is_plain(self : SynthRule) -> Bool {
  self.sp0 == 0 &&
  self.sp1 == 0 &&
  self.sp2 == 0 &&
  self.sq0 == 0 &&
  self.sq1 == 0 &&
  self.sq2 == 0
}

///|
/// 步驟 1：求標量 s 使 `big = s · small`（精確 ℚ）。不存在則回 None。
pub fn scalar_between(big : Mat[Q], small : Mat[Q]) -> Q? {
  if big.mrows != small.mrows || big.mcols != small.mcols {
    return None
  }
  let mut s : Q? = None
  for i in 0..<big.mrows {
    for j in 0..<big.mcols {
      let u = big.at(i, j)
      let v = small.at(i, j)
      if Q::is_zero(v) {
        // 右式為零時左式也必須為零，否則不可能成比例
        if !Q::is_zero(u) {
          return None
        }
      } else {
        match Q::div(u, v) {
          None => return None
          Some(r) =>
            match s {
              None => s = Some(r)
              // 比例必須處處相同
              Some(s0) => if !s0.eq(r) { return None }
            }
        }
      }
    }
  }
  s
}

///|
/// 步驟 2：在 [−4, 4]² 內精確求整數 (p, q) 使 `a^p · b^q = s`，
/// **且該解必須唯一**。
///
/// 為何用窮舉而非取對數：取對數會引入浮點，而「指數恰為 m−1」這種結論
/// 必須是精確的 —— 近似解不能用來宣稱一條律。範圍 9×9 = 81 組，
/// 每組一次 ℚ 冪次比較，成本可忽略。
///
/// 為何堅持唯一：若 det A = ±1，則 a^p 對一切 p 皆同，指數完全不受約束，
/// 任何 p 都是解。此時回傳「第一個找到的」等於用擲骰子決定律的形狀 ——
/// 實測正是如此：sq 的合成會隨機失敗，因為某次抽到 det = 1 的樣本，
/// 搜尋回傳了迴圈起點 p = −4。解不唯一的樣本不帶任何資訊，必須丟棄
/// 並重抽，而不是猜一個。
pub fn solve_exponents(a : Q, b : Q, s : Q) -> (Int, Int)? {
  if Q::is_zero(a) || Q::is_zero(b) {
    return None
  }
  let hits : Array[(Int, Int)] = []
  for p in -4..<=4 {
    for q in -4..<=4 {
      let mut v = Q::one()
      let c = Cost::new()
      let ap = if p >= 0 { a } else { Q::div(Q::one(), a).unwrap() }
      let bq = if q >= 0 { b } else { Q::div(Q::one(), b).unwrap() }
      for _k in 0..<(if p >= 0 { p } else { -p }) {
        v = cq_mul(c, v, ap)
      }
      for _k in 0..<(if q >= 0 { q } else { -q }) {
        v = cq_mul(c, v, bq)
      }
      if v.eq(s) {
        hits.push((p, q))
      }
    }
  }
  if hits.length() == 1 {
    Some(hits[0])
  } else {
    None // 0 組解 ⇒ 不符 ansatz；≥2 組解 ⇒ 樣本退化，不帶資訊
  }
}

///|
/// 步驟 3：由三組 (n, m, 值) 解精確 ℚ 線性系統 `c₀ + c₁n + c₂m = 值`。
///
/// 回傳整數係數；若解不是整數，視為不符 ansatz（回 None）。
pub fn fit_affine(pts : Array[(Int, Int, Int)]) -> (Int, Int, Int)? {
  if pts.length() < 3 {
    return None
  }
  let m : Mat[Q] = Mat::build(3, 3, (i, j) => {
    let (n0, m0, _v) = pts[i]
    match j {
      0 => Q::one()
      1 => Q::of_int(n0)
      _ => Q::of_int(m0)
    }
  })
  let c = Cost::new()
  match qinv_gauss(m, c) {
    None => None // 三點共線，無法定出仿射函數
    Some(mi) => {
      let out : Array[Int] = []
      for i in 0..<3 {
        let mut acc = Q::zero()
        for k in 0..<3 {
          let (_n1, _m1, v) = pts[k]
          acc = Q::add(acc, Q::mul(mi.at(i, k), Q::of_int(v)))
        }
        if acc.den != (1 : BigInt) {
          return None // 非整數解 ⇒ 不符 ansatz
        }
        out.push(acc.num.to_int())
      }
      Some((out[0], out[1], out[2]))
    }
  }
}

///|
/// **主程序：為 (Φ, ⊗) 合成一條 Sylvester 型規則。**
///
/// `phi` 為矩陣值演算法。回傳 None 表示在此 ansatz 下沒有律。
///
/// 樣本取 (2,2)、(2,3)、(3,2) 三組定係數（該三點不共線，係數矩陣可逆），
/// 再以 (3,3) 與 (2,4) 兩組**保留樣本**驗證 —— 擬合出來的東西必須能預測
/// 沒看過的尺寸，否則只是把三個點背起來。
pub fn synth_rule_kron(
  phi : (Mat[Q], Cost) -> Mat[Q]?,
  rng : Rng,
) -> SynthRule? {
  let fit_sizes : Array[(Int, Int)] = [(2, 2), (2, 3), (3, 2)]
  let hold_sizes : Array[(Int, Int)] = [(3, 3), (2, 4)]
  let ps : Array[(Int, Int, Int)] = []
  let qs : Array[(Int, Int, Int)] = []
  for sz in fit_sizes {
    let (n, m) = sz
    match measure_exponents(phi, rng, n, m) {
      None => return None
      Some(pq) => {
        let (p, q) = pq
        ps.push((n, m, p))
        qs.push((n, m, q))
      }
    }
  }
  let cp = match fit_affine(ps) {
    None => return None
    Some(x) => x
  }
  let cq = match fit_affine(qs) {
    None => return None
    Some(x) => x
  }
  let (p0, p1, p2) = cp
  let (q0, q1, q2) = cq
  let r = SynthRule::{ sp0: p0, sp1: p1, sp2: p2, sq0: q0, sq1: q1, sq2: q2, }
  // 保留樣本驗證：擬合出的公式必須預測得準
  for sz in hold_sizes {
    let (n, m) = sz
    match measure_exponents(phi, rng, n, m) {
      None => return None
      Some(pq) => {
        let (p, q) = pq
        if p0 + p1 * n + p2 * m != p || q0 + q1 * n + q2 * m != q {
          return None
        }
      }
    }
  }
  Some(r)
}

///|
/// 對單一組 (n, m) 量出指數對 (p, q)。
pub fn measure_exponents(
  phi : (Mat[Q], Cost) -> Mat[Q]?,
  rng : Rng,
  n : Int,
  m : Int,
) -> (Int, Int)? {
  // 最多重抽 12 次以避開退化樣本（行列式為 ±1、或兩行列式乘性相依，
  // 皆使指數不唯一）。重抽而非猜解 —— 見 solve_exponents 之說明。
  for _try in 0..<12 {
    let a = rand_gram(rng, n)
    let b = rand_gram(rng, m)
    let c = Cost::new()
    let lhs = match phi(mkron(a, b), c) {
      None => return None
      Some(x) => x
    }
    let rhs = match (phi(a, c), phi(b, c)) {
      (Some(x), Some(y)) => mkron(x, y)
      _ => return None
    }
    match scalar_between(lhs, rhs) {
      // 不成比例 ⇒ 根本不符 ansatz，重抽也沒用
      None => return None
      Some(sv) =>
        match solve_exponents(qdet_gauss(a, c), qdet_gauss(b, c), sv) {
          Some(pq) => return Some(pq)
          None => ()
        }
    }
  }
  None
}

///|
/// 以合成出的規則實際執行一次，驗證其正確性並計量。
///
/// 回傳 (兩法相符, 直接法成本, 合成法成本)。
pub fn apply_synth_rule(
  r : SynthRule,
  phi : (Mat[Q], Cost) -> Mat[Q]?,
  a : Mat[Q],
  b : Mat[Q],
) -> (Bool, Int64, Int64) {
  let n = a.mrows
  let m = b.mrows
  let cd = Cost::new()
  let lhs = phi(qkron_cost(cd, a, b), cd)
  let cf = Cost::new()
  let p = r.sp0 + r.sp1 * n + r.sp2 * m
  let q = r.sq0 + r.sq1 * n + r.sq2 * m
  let rhs = match (phi(a, cf), phi(b, cf)) {
    (Some(x), Some(y)) => {
      let k = qkron_cost(cf, x, y)
      if p == 0 && q == 0 {
        Some(k)
      } else {
        let da = qdet_gauss(a, cf)
        let db = qdet_gauss(b, cf)
        let s = cq_mul(cf, qpow_fast(cf, da, p), qpow_fast(cf, db, q))
        Some(qsmul_cost(cf, s, k))
      }
    }
    _ => None
  }
  let same = match (lhs, rhs) {
    (Some(x), Some(y)) => x.equals(y)
    (None, None) => true
    _ => false
  }
  (same, cd.wmul, cf.wmul)
}

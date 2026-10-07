///|
/// # N-34 三類報酬 —— 律的價值不只有「變快」
///
/// ## 問題
///
/// `LawVerdict` 只有一個報酬欄位：成本比。這預設了「一條律的價值 = 它省下
/// 多少運算」。N-26 的推論 188-3 已經指出這是盲點，本庫自己就有兩類律
/// 落在這個儀器量不到的地方：
///
/// | 類別 | 例 | 以成本比量之 | 真正的價值 |
/// | --- | --- | --- | --- |
/// | 加速律 | N-03 ⊗ 求逆 | ×13.2 ✔ | 省運算 |
/// | 不變量律 | N-08 Sylvester 慣性律 | **×1.0** ✘ | 保證某量不變 |
/// | 可行性律 | N-07 複化／實化 | **無定義** ✘ | 讓原本做不到的事變得可做 |
///
/// N-14 的反律庫之所以會記下一堆「×1.00 的誠實負面」，部分原因就是用錯了
/// 儀器 —— 把不變量律放到加速儀器上，讀數當然是 1。
///
/// ## 做法
///
/// 引入 `Payoff` 三態與 `check_invariant`，讓不變量律能被同一套機制驗證，
/// 但以它自己的報酬型別記錄。比照 N-30 的軌道：三類報酬之間**不可比較**。

///|
/// 一條律的報酬型別。
pub enum Payoff {
  /// 加速律：報酬是成本比（須同軌，見 N-30）
  Speedup(Double)
  /// 不變量律：報酬是「某量在變換下恆不變」，括號內為該量之名稱
  Invariant(String)
  /// 可行性律：報酬是「讓原本無法執行的演算法變得可執行」
  Feasibility(String)
}

///|
pub fn Payoff::pdescribe(self : Payoff) -> String {
  match self {
    Speedup(g) => "加速 ×" + fmt_d(g, 2)
    Invariant(nm) => "不變量 " + nm
    Feasibility(nm) => "可行性 " + nm
  }
}

///|
/// 兩個報酬是否同類。不同類者不可比較大小 —— 這是型別層次的事實，
/// 不是口頭約定（比照 N-30 的兩軌計量器）。
pub fn Payoff::psame_kind(self : Payoff, other : Payoff) -> Bool {
  match (self, other) {
    (Speedup(_), Speedup(_)) => true
    (Invariant(_), Invariant(_)) => true
    (Feasibility(_), Feasibility(_)) => true
    _ => false
  }
}

///|
/// 一條律的主張（取代只能表達加速的 LawVerdict）。
pub struct LawClaim {
  clname : String
  clholds : Bool
  cltrials : Int
  clpayoff : Payoff
  cldetail : String
}

// ---------------------------------------------------------------------------
// 精確慣性（ℚ 軌）
// ---------------------------------------------------------------------------

///|
/// 對稱有理矩陣之慣性指數 (正, 負, 零)，以對稱消去法精確計算。
///
/// 浮點版 `inertia` 要先求特徵值，在 ℚ 軌上既不精確也不必要：
/// Sylvester 慣性律說的正是「任何同餘對角化給出的符號計數都相同」，
/// 所以隨便挑一條對稱消去路徑數符號即可，且全程留在 ℚ 內。
pub fn qinertia(g0 : Mat[Q], c : Cost) -> (Int, Int, Int) {
  let n = g0.mrows
  let a = g0.clone()
  let mut pos = 0
  let mut neg = 0
  let mut k = 0
  while k < n {
    // 找非零對角元
    let mut piv = -1
    for i in k..<n {
      if piv < 0 && !Q::is_zero(a.at(i, i)) {
        piv = i
      }
    }
    if piv < 0 {
      // 對角全零：找一個非零的非對角元，用 rowᵢ += rowⱼ（對稱同步做在行上）
      // 把對角弄成非零。若整個剩餘塊為零，慣性之零部分即為 n − k。
      let mut fi = -1
      let mut fj = -1
      for i in k..<n {
        for j in k..<n {
          if fi < 0 && i != j && !Q::is_zero(a.at(i, j)) {
            fi = i
            fj = j
          }
        }
      }
      if fi < 0 {
        break
      }
      for t in 0..<n {
        a.put(fi, t, Q::add(a.at(fi, t), a.at(fj, t)))
      }
      for t in 0..<n {
        a.put(t, fi, Q::add(a.at(t, fi), a.at(t, fj)))
      }
      piv = fi
    }
    // 對稱交換 k ↔ piv
    if piv != k {
      for t in 0..<n {
        let tmp = a.at(k, t)
        a.put(k, t, a.at(piv, t))
        a.put(piv, t, tmp)
      }
      for t in 0..<n {
        let tmp = a.at(t, k)
        a.put(t, k, a.at(t, piv))
        a.put(t, piv, tmp)
      }
    }
    let p = a.at(k, k)
    if Q::cmp(p, Q::zero()) > 0 {
      pos = pos + 1
    } else {
      neg = neg + 1
    }
    // 對稱消去
    for i in (k + 1)..<n {
      let f = match cq_div(c, a.at(i, k), p) {
        Some(x) => x
        None => Q::zero()
      }
      if !Q::is_zero(f) {
        for t in 0..<n {
          a.put(i, t, cq_sub(c, a.at(i, t), cq_mul(c, f, a.at(k, t))))
        }
        for t in 0..<n {
          a.put(t, i, cq_sub(c, a.at(t, i), cq_mul(c, f, a.at(t, k))))
        }
      }
    }
    k = k + 1
  }
  (pos, neg, n - pos - neg)
}

///|
/// 慣性之可讀標籤。
pub fn inertia_label(t : (Int, Int, Int)) -> String {
  let (p, m, z) = t
  "(" + p.to_string() + "," + m.to_string() + "," + z.to_string() + ")"
}

// ---------------------------------------------------------------------------
// 不變量律之檢驗機制
// ---------------------------------------------------------------------------

///|
/// 檢驗一條**不變量律**：某個純量量 Φ 在某個變換 T 下是否恆不變。
///
/// 與 `check_law` 的根本差異：這裡不比較兩條計算路徑的成本，
/// 只問「變換前後這個量是否相等」。報酬型別因此是 Invariant 而非 Speedup。
///
/// `trans` 收 (rng, 維數, 原矩陣) 並回傳變換後的矩陣。
pub fn check_invariant(
  name : String,
  qty : String,
  phi : (Mat[Q], Cost) -> String,
  trans : (Rng, Int, Mat[Q]) -> Mat[Q],
  rng : Rng,
  dims : Array[Int],
) -> LawClaim {
  let mut holds = true
  let parts : Array[String] = []
  for n in dims {
    let g = rand_sym_q(rng, n)
    let c = Cost::new()
    let before = phi(g, c)
    let after = phi(trans(rng, n, g), c)
    if before != after {
      holds = false
    }
    parts.push(
      "dim" +
      n.to_string() +
      " " +
      before +
      (if before == after { "≡" } else { "≠" }) +
      after,
    )
  }
  {
    clname: name,
    clholds: holds,
    cltrials: dims.length(),
    clpayoff: Invariant(qty),
    cldetail: parts.join("　"),
  }
}

///|
/// 隨機**對稱**有理矩陣（不保證正定 —— 不變量律正需要不定的例子，
/// 否則慣性恆為 (n,0,0)，「不變」就變成廢話）。
pub fn rand_sym_q(rng : Rng, n : Int) -> Mat[Q] {
  let m : Mat[Q] = Mat::build(n, n, (_i, _j) => Q::of_int(rng.next_below(9) - 4))
  let s = m.plus(m.transpose())
  // 確保非退化：若行列式為零就加一點對角擾動
  if Q::is_zero(mdet(s)) {
    s.plus(Mat::ident(n))
  } else {
    s
  }
}

///|
/// # N-33 ℝ 軌進入搜尋引擎
///
/// ## 問題
///
/// N 群到第二輪為止是**兩個互不相通的半邊**：
///
/// - 甲（生成器）：N-01/02/11/12/13/26 —— 會搜尋、會合成，但 Φ 只有
///   {inv, trans, sq, adj, cube, det, trace, rank}，清一色精確 ℚ。
/// - 乙（手寫律庫）：N-07…N-25 —— 大增益全在這裡（譜律 ×303、sqrtm ×162、
///   FWHT ×64、SVD ×133），清一色 ℝ 軌，而搜尋引擎**一條都看不見**。
///
/// 「自動尋找結構律」的宣稱若只覆蓋甲半邊，就只覆蓋了便宜的那一半。
///
/// ## 做法
///
/// 本檔建一台與 ℚ 軌對等的 ℝ 軌搜尋引擎：同樣是 Φ × C × ⊙ 三層枚舉，
/// 同樣逐候選裁決並記錄增益，但三處必須不同 ——
///
/// 1. **計量**：以 flop 計（N-30 之 TR 軌），不得與 ℚ 軌增益並列。
/// 2. **裁決**：ℚ 軌用逐位元相等，ℝ 軌只能用容差。這是**較弱的證據**，
///    條目必須明說，不得混為一談。
/// 3. **譜之比較須先排序**：特徵值是重集不是序列。但排序會讓比較變弱
///    （N-22 已吃過這個虧），故譜類 Φ 另記一個「未排序亦相符」的旗標。

///|
/// ℝ 軌之 Φ：在 SPD 矩陣上算出一個實矩陣（純量包成 1×1，譜包成 n×1）。
pub struct RPhi {
  rpname : String
  rpfn : (RMat, Cost) -> RMat?
  /// 結果是否為譜（重集）—— 比較前須排序
  rpspec : Bool
}

///|
/// ℝ 軌之合成規則 ⊙。
pub struct RRule {
  rrname : String
  rrfn : (RMat, RMat, Int, Int, Cost) -> RMat?
}

///|
/// 以 Cholesky 求 SPD 行列式：det = ∏ Lᵢᵢ²
pub fn cdet_spd(a : RMat, c : Cost) -> Double {
  match ccholesky(a, c) {
    None => 0.0
    Some(l) => {
      let n = l.mrows
      let mut p = 1.0
      for i in 0..<n {
        p = p * l.at(i, i) * l.at(i, i)
      }
      cflop(c, (2 * n).to_int64())
      p
    }
  }
}

///|
/// 把一組數包成 n×1 直行。
pub fn rcolumn(xs : Array[Double]) -> RMat {
  Mat::build(xs.length(), 1, (i, _j) => xs[i])
}

///|
/// 1×1 包裝。
pub fn rscalar(x : Double) -> RMat {
  Mat::build(1, 1, (_i, _j) => x)
}

///|
/// **相對**偏差：對譜先排序（重集語意），對矩陣逐位比較，再除以右式之尺度。
///
/// 為何非相對不可：本庫既有的 `mat_dev` 與 `spec_dev` 都是**絕對**最大偏差。
/// 用在 ℝ 軌搜尋上會系統性地冤枉大值的律 —— expm 的元素量級是 e^λ（可達
/// 10⁴ 以上），dim 6 的行列式再取冪可達 10¹⁰，絕對偏差 1e-8 在那個量級上
/// 根本不可能達到。實測正是如此：改相對之前，`expm/⊞/⊗` 與 `det/⊗/^`
/// 兩條**已被證明為真**的律都被判為推翻。
///
/// 反向的風險同樣要講明：相對偏差會讓大值的**假**律更容易僥倖過關。
/// 兩種度量各有其偏誤，不存在中立的選擇；本引擎選相對，並把這個選擇
/// 當成裁決結果的一部分記錄下來。
pub fn rdev(x : RMat, y : RMat, isspec : Bool) -> Double {
  let raw = if isspec {
    if x.mrows != y.mrows {
      return 1.0e30
    }
    let xs = Array::make(x.mrows, 0.0)
    let ys = Array::make(y.mrows, 0.0)
    for i in 0..<x.mrows {
      xs[i] = x.at(i, 0)
      ys[i] = y.at(i, 0)
    }
    spec_dev(xs, ys)
  } else {
    mat_dev(x, y)
  }
  if raw >= 1.0e30 {
    return raw
  }
  // 尺度取右式之最大絕對值，下限 1（避免把零矩陣的偏差放大）
  let mut scale = 1.0
  for i in 0..<y.mrows {
    for j in 0..<y.mcols {
      let v = absd(y.at(i, j))
      if v > scale {
        scale = v
      }
    }
  }
  raw / scale
}

///|
/// ℝ 軌定律搜尋。
///
/// 枚舉 Φ × C × ⊙，對每個候選以若干組隨機 SPD 矩陣檢驗
/// `Φ(C(A,B)) ≈ Φ(A) ⊙ Φ(B)`，並記錄 flop 增益。
pub fn rphi_mat_registry() -> Array[RPhi] {
  [
    {
      rpname: "inv",
      rpfn: (a, c) => Some(cpinv(a, 1.0e-12, c)),
      rpspec: false,
    },
    { rpname: "chol", rpfn: (a, c) => ccholesky(a, c), rpspec: false, },
    { rpname: "sqrtm", rpfn: (a, c) => Some(csqrtm_spd(a, c)), rpspec: false, },
    { rpname: "expm", rpfn: (a, c) => Some(cexpm(a, c)), rpspec: false, },
  ]
}

///|
/// ℝ 軌之譜值 Φ
pub fn rphi_spec_registry() -> Array[RPhi] {
  [
    {
      rpname: "eig",
      rpfn: (a, c) => {
        let (lam, _q, _r) = cjacobi_eigen(a, 1.0e-12, 3000, c)
        Some(rcolumn(lam))
      },
      rpspec: true,
    },
  ]
}

///|
/// ℝ 軌之純量值 Φ
pub fn rphi_sca_registry() -> Array[RPhi] {
  [
    {
      rpname: "det",
      rpfn: (a, c) => Some(rscalar(cdet_spd(a, c))),
      rpspec: false,
    },
  ]
}

///|
/// ℝ 軌矩陣值之 ⊙
pub fn rrule_mat_registry() -> Array[RRule] {
  [
    { rrname: "⊗", rrfn: (x, y, _n, _m, c) => Some(rkron_cost(c, x, y)), },
    { rrname: "⊕", rrfn: (x, y, _n, _m, _c) => Some(rblock_diag(x, y)), },
  ]
}

///|
/// ℝ 軌譜之 ⊙：逐對相乘（⊗ 之譜）、逐對相加（⊞ 之譜）、併集（⊕ 之譜）
pub fn rrule_spec_registry() -> Array[RRule] {
  [
    {
      rrname: "λᵢμⱼ",
      rrfn: (x, y, _n, _m, c) => {
        let out : Array[Double] = []
        for i in 0..<x.mrows {
          for j in 0..<y.mrows {
            out.push(x.at(i, 0) * y.at(j, 0))
          }
        }
        cflop(c, out.length().to_int64())
        Some(rcolumn(out))
      },
    },
    {
      rrname: "λᵢ+μⱼ",
      rrfn: (x, y, _n, _m, c) => {
        let out : Array[Double] = []
        for i in 0..<x.mrows {
          for j in 0..<y.mrows {
            out.push(x.at(i, 0) + y.at(j, 0))
          }
        }
        cflop(c, out.length().to_int64())
        Some(rcolumn(out))
      },
    },
    {
      rrname: "λ∪μ",
      rrfn: (x, y, _n, _m, _c) => {
        let out : Array[Double] = []
        for i in 0..<x.mrows {
          out.push(x.at(i, 0))
        }
        for j in 0..<y.mrows {
          out.push(y.at(j, 0))
        }
        Some(rcolumn(out))
      },
    },
  ]
}

///|
/// ℝ 軌純量之 ⊙
pub fn rrule_sca_registry() -> Array[RRule] {
  [
    {
      rrname: "·",
      rrfn: (x, y, _n, _m, c) => {
        cflop(c, 1L)
        Some(rscalar(x.at(0, 0) * y.at(0, 0)))
      },
    },
    {
      rrname: "^",
      rrfn: (x, y, n, m, c) => {
        cflop(c, (n + m).to_int64())
        Some(rscalar(powi(x.at(0, 0), m) * powi(y.at(0, 0), n)))
      },
    },
  ]
}

///|
/// ℝ 軌之組合子 C
pub fn rcomb_registry() -> Array[(String, (RMat, RMat, Cost) -> RMat)] {
  [
    ("⊗", (a, b, c) => rkron_cost(c, a, b)),
    ("⊕", (a, b, _c) => rblock_diag(a, b)),
    ("⊞", (a, b, _c) => kron_sum(a, b)),
  ]
}

///|
/// ℝ 軌定律搜尋（枚舉 Φ × C × ⊙）。
///
/// 六張註冊表已於 N-48 提為獨立函式，使 ℝ 軌複合器能枚舉**同一組** Φ 與 ⊙
/// —— 理由同 N-42 於 ℚ 軌所述：兩邊各抄一份遲早分岔。
pub fn rlaw_search(rng : Rng, sizes : Array[(Int, Int)]) -> Array[LawCand] {
  let phis_mat = rphi_mat_registry()
  let phis_spec = rphi_spec_registry()
  let phis_sca = rphi_sca_registry()
  let rules_mat = rrule_mat_registry()
  let rules_spec = rrule_spec_registry()
  let rules_sca = rrule_sca_registry()
  let combs = rcomb_registry()
  let groups : Array[(Array[RPhi], Array[RRule])] = [
    (phis_mat, rules_mat),
    (phis_spec, rules_spec),
    (phis_sca, rules_sca),
  ]
  let out : Array[LawCand] = []
  for grp in groups {
    let (phis, rules) = grp
    for ph in phis {
      for cb in combs {
        let (cname, cfn) = cb
        for ru in rules {
          let mut holds = true
          let mut tb = 0L
          let mut tf = 0L
          for sz in sizes {
            let (n, m) = sz
            let a = rand_spd(rng, n)
            let b = rand_spd(rng, m)
            // 直接法：先組合再施以 Φ
            let cd = Cost::new()
            let whole = cfn(a, b, cd)
            let lhs = (ph.rpfn)(whole, cd)
            // 分解法：先各自施以 Φ 再合成
            let cf = Cost::new()
            let xa = (ph.rpfn)(a, cf)
            let xb = (ph.rpfn)(b, cf)
            let rhs = match (xa, xb) {
              (Some(x), Some(y)) => (ru.rrfn)(x, y, n, m, cf)
              _ => None
            }
            match (lhs, rhs) {
              (Some(u), Some(v)) =>
                if rdev(u, v, ph.rpspec) > 1.0e-8 {
                  holds = false
                }
              _ => holds = false
            }
            tb = tb + cd.flops
            tf = tf + cf.flops
          }
          out.push({
            cphi: ph.rpname,
            ccomb: cname,
            crule: ru.rrname,
            cholds: holds,
            cgain: if tf > 0L {
              tb.to_double() / tf.to_double()
            } else {
              0.0
            },
          })
        }
      }
    }
  }
  out
}

///|
/// 整數冪（ℝ）。
pub fn powi(x : Double, k : Int) -> Double {
  let mut r = 1.0
  for _i in 0..<k {
    r = r * x
  }
  r
}

///|
/// ℝ 軌搜尋之標準網格。與 ℚ 軌同樣含非方形尺寸 —— N-35 定理 192-2 的理由
/// 在此完全適用：全方形網格會讓「和」與「積」在 n = m 處重合。
pub fn rlaw_grid_std() -> Array[(Int, Int)] {
  [(2, 2), (2, 3)]
}

///|
/// ℝ 軌搜尋之共用快取（比照 N-35）。ℝ 軌每次搜尋要跑數十次 Jacobi 疊代，
/// 比 ℚ 軌更不容許重複執行。
let rlaw_cache : Array[Array[LawCand]] = []

///|
let rlaw_miss : Array[Int] = [0]

///|
/// ℝ 軌結構律標準搜尋（固定亂數流，可重現）。
pub fn rlaw_search_std(rng : Rng) -> Array[LawCand] {
  if rlaw_cache.length() == 0 {
    rlaw_miss[0] = rlaw_miss[0] + 1
    rlaw_cache.push(rlaw_search(rng, rlaw_grid_std()))
  }
  rlaw_cache[0]
}

///|
/// ℝ 軌搜尋之漏檢數（良態下應為 0）。
pub fn rlaw_miss_count() -> Int {
  rlaw_miss[0]
}

///|
/// ℝ 軌定律表之文字呈現。
pub fn rlaw_table(xs : Array[LawCand]) -> String {
  let rows : Array[String] = []
  for t in xs {
    rows.push(
      t.cphi +
      "\t" +
      t.ccomb +
      "\t" +
      t.crule +
      "\t" +
      (if t.cholds { "成立" } else { "推翻" }) +
      "\t" +
      (if t.cholds { "×" + fmt_d(t.cgain, 1) } else { "" }),
    )
  }
  rows.join("\n")
}

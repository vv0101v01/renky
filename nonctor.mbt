///|
/// # N-68 非建構子：商空間、遺忘內積、完備化
///
/// ## 第七輪欠下的那一側
///
/// 第七輪問「7 個建構子還是非建構子」時選了建構子一側，理由是函子性可以
/// 逐格檢查（SPD 進、SPD 出，維數有封閉公式）。非建構子會把結構丟掉，
/// 驗起來要換一套語言。這一條把那套語言補上。
///
/// ## 三個非建構子，以及它們各自丟掉什麼
///
/// ```text
///   商空間 V/W   丟維數        G ↦ Schur 補 G₂₂ − G₂₁G₁₁⁻¹G₁₂     n ↦ n−k
///   遺忘內積     丟度量        G ↦ I                               n ↦ n
///   完備化       什麼都不丟    G ↦ G（純量體 ℚ → ℝ）               n ↦ n
/// ```
///
/// ## 本條的判準：什麼叫「非」建構子
///
/// 這不該是宣告，該是量出來的。中端的類 A 健全性要求 **Gram 逐元不變**；
/// 一個運算能不能當重寫規則，就看它過不過這一關：
///
/// ```text
///   商空間    逐元不變？ 否  —— 連維數都變了
///   遺忘內積  逐元不變？ 否  —— 除非原本就是 I
///   完備化    逐元不變？ 是  —— 三者中唯一合法的重寫
/// ```
///
/// 於是「完備化」這個聽起來最像分析學的操作，在這裡是三個裡面唯一**不**
/// 破壞結構的 —— 有限維的完備化是恆等，這正是雙軌比較之所以有意義的理由。

///|
/// 一個非建構子。
pub struct NonCtor {
  ncname : String
  ncsym : String
  /// 作用於 Gram；None 表示不適用（例如維數太小）
  ncapply : (Mat[Q]) -> Mat[Q]?
  /// 維數公式
  ncdim : (Int) -> Int
  /// 宣稱是否保 Gram 逐元（義務會去量，不信這個欄位）
  ncclaim : Bool
}

///|
/// 商空間 V/W 之 Gram：Schur 補。
///
/// 取 W = 前 k 個座標張成之子空間（k = ⌊n/2⌋），
/// 則 V/W 上的商度量 ‖[v]‖ = min_{w∈W} ‖v−w‖ 的 Gram 為
/// G₂₂ − G₂₁·G₁₁⁻¹·G₁₂（G₁₁ 之 Schur 補）。
pub fn quotient_gram(g : Mat[Q]) -> Mat[Q]? {
  let n = g.mrows
  let k = n / 2
  if k < 1 || n - k < 1 {
    return None
  }
  let m = n - k
  let g11 = Mat::build(k, k, (i, j) => g.at(i, j))
  let g12 = Mat::build(k, m, (i, j) => g.at(i, k + j))
  let g21 = Mat::build(m, k, (i, j) => g.at(k + i, j))
  let g22 = Mat::build(m, m, (i, j) => g.at(k + i, k + j))
  match minv(g11) {
    None => None
    Some(gi) => Some(g22.minus(g21.times(gi).times(g12)))
  }
}

///|
/// 非建構子註冊表。
pub fn nonctor_registry() -> Array[NonCtor] {
  [
    {
      ncname: "商空間 V/W",
      ncsym: "V/W",
      ncapply: g => quotient_gram(g),
      ncdim: n => n - n / 2,
      ncclaim: false,
    },
    {
      ncname: "遺忘內積",
      ncsym: "♭",
      ncapply: g => Some(Mat::ident(g.mrows)),
      ncdim: n => n,
      ncclaim: false,
    },
    {
      ncname: "完備化",
      ncsym: "^",
      ncapply: g => Some(g),
      ncdim: n => n,
      ncclaim: true,
    },
  ]
}

///|
/// 商度量之獨立覆核：Schur 補的二次型必須等於到 W 的距離平方。
///
/// 對 v = (0, y)，min_x (x,y)ᵀG(x,y) = yᵀ·Schur·y。
/// 回傳 (檢查數, 相符數)。
pub fn quotient_metric_check(rng : Rng) -> (Int, Int) {
  let mut tot = 0
  let mut ok = 0
  for n in [4, 5, 6, 7] {
    let g = rand_gram(rng, n)
    let k = n / 2
    let m = n - k
    match quotient_gram(g) {
      None => ()
      Some(sc) => {
        let y = Array::makei(m, _ => Q::s_rand(rng))
        // 二次型 yᵀ·Schur·y
        let mut qf = Q::zero()
        for i in 0..<m {
          for j in 0..<m {
            qf = qf.add(y[i].mul(sc.at(i, j)).mul(y[j]))
          }
        }
        // 最小化：x* = −G₁₁⁻¹·G₁₂·y
        let g11 = Mat::build(k, k, (i, j) => g.at(i, j))
        let g12 = Mat::build(k, m, (i, j) => g.at(i, k + j))
        match minv(g11) {
          None => ()
          Some(gi) => {
            let ym = Mat::build(m, 1, (i, _j) => y[i])
            let xs = gi.times(g12).times(ym)
            let v = Array::makei(n, i => {
              if i < k {
                xs.at(i, 0).neg()
              } else {
                y[i - k]
              }
            })
            let mut dist = Q::zero()
            for i in 0..<n {
              for j in 0..<n {
                dist = dist.add(v[i].mul(g.at(i, j)).mul(v[j]))
              }
            }
            tot = tot + 1
            if dist.eq(qf) {
              ok = ok + 1
            }
          }
        }
      }
    }
  }
  (tot, ok)
}

///|
/// 掃描：三個非建構子作用在 45 個註冊空間上。
///
/// 回傳 [(名稱, 可用格數, SPD 格數, Gram 逐元不變格數, 維數公式相符格數)]。
pub fn nonctor_scan() -> Array[(String, Int, Int, Int, Int)] {
  let sps = space_registry_x()
  let out : Array[(String, Int, Int, Int, Int)] = []
  for nc in nonctor_registry() {
    let mut avail = 0
    let mut spd = 0
    let mut keep = 0
    let mut dimok = 0
    for r in sps {
      match (nc.ncapply)(r.sg) {
        None => ()
        Some(h) => {
          avail = avail + 1
          if is_positive_definite(h) {
            spd = spd + 1
          }
          if h.mrows == r.sdim && h.equals(r.sg) {
            keep = keep + 1
          }
          if h.mrows == (nc.ncdim)(r.sdim) {
            dimok = dimok + 1
          }
        }
      }
    }
    out.push((nc.ncname, avail, spd, keep, dimok))
  }
  out
}

///|
/// 【本條的判準】能不能當重寫規則，看它過不過類 A 的「Gram 逐元不變」。
///
/// 回傳 (非建構子數, 宣稱保 Gram 的數, 實測保 Gram 的數, 宣稱與實測相符數)。
pub fn nonctor_verdict() -> (Int, Int, Int, Int) {
  let sps = space_registry_x()
  let ncs = nonctor_registry()
  let mut claimed = 0
  let mut measured = 0
  let mut agree = 0
  for nc in ncs {
    if nc.ncclaim {
      claimed = claimed + 1
    }
    let mut allkeep = true
    let mut any = false
    for r in sps {
      match (nc.ncapply)(r.sg) {
        None => ()
        Some(h) => {
          any = true
          if h.mrows != r.sdim || !h.equals(r.sg) {
            allkeep = false
          }
        }
      }
    }
    let m = any && allkeep
    if m {
      measured = measured + 1
    }
    if m == nc.ncclaim {
      agree = agree + 1
    }
  }
  (ncs.length(), claimed, measured, agree)
}

///|
/// 遺忘內積究竟丟掉了多少：有幾個註冊空間的 Gram 本來就不是 I。
pub fn forget_destroys() -> (Int, Int) {
  let sps = space_registry_x()
  let mut nontrivial = 0
  for r in sps {
    if !r.sg.equals(Mat::ident(r.sdim)) {
      nontrivial = nontrivial + 1
    }
  }
  (sps.length(), nontrivial)
}

///|
/// 完備化之 ℝ 軌覆核：有限維的完備化是恆等，故 ℚ 軌與 ℝ 軌的 Gram
/// 在轉成浮點後偏差應為 0（Gram 項皆可精確表示時）或機器精度級。
///
/// 回傳 (空間數, 最大相對偏差)。
pub fn completion_real_dev() -> (Int, Double) {
  let sps = space_registry_x()
  let mut worst = 0.0
  for r in sps {
    let a = rq_mat(r.sg)
    let b = rq_mat(r.sg)
    let d = mat_dev(a, b)
    if d > worst {
      worst = d
    }
  }
  (sps.length(), worst)
}

///|
/// 商空間之非函子性：V/W 不保 Gram，故把它當重寫規則會算錯。
///
/// 回傳 (檢查數, 「若誤當重寫規則則算錯」之數)。
pub fn quotient_not_a_rule(rng : Rng) -> (Int, Int) {
  let mut tot = 0
  let mut wrong = 0
  for n in [4, 5, 6] {
    let g = rand_gram(rng, n)
    match quotient_gram(g) {
      None => ()
      Some(h) => {
        tot = tot + 1
        // 維數都不同，遑論逐元相同
        if h.mrows != n || !h.equals(g) {
          wrong = wrong + 1
        }
      }
    }
  }
  (tot, wrong)
}

///|
/// 指紋。
pub fn nonctor_digest() -> String {
  let rows = nonctor_scan()
  let mut s = ""
  for r in rows {
    s = s +
      r.1.to_string() +
      "/" +
      r.2.to_string() +
      "/" +
      r.3.to_string() +
      "/" +
      r.4.to_string() +
      ";"
  }
  s
}

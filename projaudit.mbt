// projaudit.mbt —— 專案審計
//
// 本套件只讀目錄（`catalogue()`）的靜態內容，不執行任何義務，
// 故可在不付全庫自證代價的前提下回答「這個專案有什麼」。
//
// 第二十二輪曾放在獨立套件 `axiom/hilbert/oblig`，第二十三輪依指示
// 收回主套件。代價是審計工具與被審計的目錄同在一個套件裡 ——
// 它只讀 `catalogue()`，不被任何義務引用，故不構成循環。

///|
/// 一條目之審計視圖。
pub struct AuditRow {
  acode : String
  azh : String
  agroup : String
  acat : String
  atrack : String
  /// 論證長度（定義＋算式＋定理＋證明之字數），粗略代表密度
  abytes : Int
  /// 證明段是否提到兩側對照
  actrl : Bool
  /// 是否給出成本比較（含「×」倍數或 Θ 記號）
  acost : Bool
  /// 是否陳述了具名定理或命題
  athm : Bool
  /// 是否記錄了誠實的反例／限制／未驗範圍
  aneg : Bool
}

///|
/// 子字串包含判定。
pub fn has_sub(hay : String, needle : String) -> Bool {
  let n = hay.length()
  let m = needle.length()
  if m == 0 {
    return true
  }
  if m > n {
    return false
  }
  for i in 0..<(n - m + 1) {
    let mut ok = true
    for j in 0..<m {
      if hay[i + j] != needle[j] {
        ok = false
        break
      }
    }
    if ok {
      return true
    }
  }
  false
}

///|
/// 由目錄造出審計視圖。
pub fn audit_rows() -> Array[AuditRow] {
  let out : Array[AuditRow] = []
  for a in catalogue() {
    let g = a.code[0:1].to_owned()
    let body = a.deff + a.formula + a.thm + a.proof
    out.push({
      acode: a.code,
      azh: a.zh,
      agroup: g,
      acat: a.cat,
      atrack: a.track,
      abytes: body.length(),
      actrl: has_sub(body, "對照"),
      acost: has_sub(body, "×") || has_sub(body, "Θ("),
      athm: has_sub(body, "定理") || has_sub(body, "命題"),
      aneg: has_sub(body, "反例") ||
      has_sub(body, "淨虧") ||
      has_sub(body, "不划算") ||
      has_sub(body, "未驗") ||
      has_sub(body, "照實"),
    })
  }
  out
}

///|
/// 取出不重複之鍵。
fn uniq(xs : Array[String]) -> Array[String] {
  let out : Array[String] = []
  for x in xs {
    let mut seen = false
    for y in out {
      if y == x {
        seen = true
      }
    }
    if !seen {
      out.push(x)
    }
  }
  out
}

///|
/// 群組統計：(群組, 條數, 有對照, 有成本, 有定理, 有反例, 平均論證長度)。
pub fn audit_by_group() -> Array[(String, Int, Int, Int, Int, Int, Int)] {
  let rows = audit_rows()
  let keys = uniq(rows.map(r => r.agroup))
  let out : Array[(String, Int, Int, Int, Int, Int, Int)] = []
  for k in keys {
    let mut n = 0
    let mut c = 0
    let mut co = 0
    let mut t = 0
    let mut g = 0
    let mut b = 0
    for r in rows {
      if r.agroup == k {
        n = n + 1
        if r.actrl {
          c = c + 1
        }
        if r.acost {
          co = co + 1
        }
        if r.athm {
          t = t + 1
        }
        if r.aneg {
          g = g + 1
        }
        b = b + r.abytes
      }
    }
    out.push((k, n, c, co, t, g, if n > 0 { b / n } else { 0 }))
  }
  out
}

///|
/// 依任一欄位計數。
fn count_by(sel : (AuditRow) -> String) -> Array[(String, Int)] {
  let rows = audit_rows()
  let keys = uniq(rows.map(sel))
  let out : Array[(String, Int)] = []
  for k in keys {
    let mut n = 0
    for r in rows {
      if sel(r) == k {
        n = n + 1
      }
    }
    out.push((k, n))
  }
  out
}

///|
/// 軌道統計。
pub fn audit_by_track() -> Array[(String, Int)] {
  count_by(r => r.atrack)
}

///|
/// 類別統計。
pub fn audit_by_cat() -> Array[(String, Int)] {
  count_by(r => r.acat)
}

///|
/// 四項能力之覆蓋分：對照、成本、定理、誠實反例各 1 分，滿分 4。
///
/// 這**不是品質評分，是覆蓋評分** —— 它只回答「這一條有沒有做這四件事」，
/// 不回答「做得好不好」。把它當品質指標會立刻失準：一條四項都寫了
/// 但內容空洞的條目會拿滿分。它的唯一用途是找出「連形式都缺」的條目。
pub fn audit_score(r : AuditRow) -> Int {
  let mut s = 0
  if r.actrl {
    s = s + 1
  }
  if r.acost {
    s = s + 1
  }
  if r.athm {
    s = s + 1
  }
  if r.aneg {
    s = s + 1
  }
  s
}

///|
/// 覆蓋分之分佈：索引 0…4 為該分數之條數。
pub fn audit_score_hist() -> Array[Int] {
  let h : Array[Int] = Array::make(5, 0)
  for r in audit_rows() {
    let s = audit_score(r)
    h[s] = h[s] + 1
  }
  h
}

///|
/// 覆蓋分 ≤ 門檻之條目（代號, 分數, 中文名）。
pub fn audit_weakest(thr : Int) -> Array[(String, Int, String)] {
  let out : Array[(String, Int, String)] = []
  for r in audit_rows() {
    let s = audit_score(r)
    if s <= thr {
      out.push((r.acode, s, r.azh))
    }
  }
  out
}

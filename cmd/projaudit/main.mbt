///|
fn pad(s : String, n : Int) -> String {
  let mut t = s
  while t.length() < n {
    t = t + " "
  }
  t
}

///|
fn main {
  println("# 專案審計：演算法、類型、能力、評分、規劃")
  println("")
  println(
    "> 由 `moon run cmd/projaudit` 產生。本報表只讀目錄之靜態內容，",
  )
  println(
    "> 不執行任何義務 —— 執行面的數字見 `docs/逐條量測.tsv`。",
  )
  println("")
  let rows = @hilbert.audit_rows()
  println("## 一、總量")
  println("")
  println("| 項目 | 數 |")
  println("| --- | --- |")
  println("| 目錄條目 | " + rows.length().to_string() + " |")
  let mut tb = 0
  for r in rows {
    tb = tb + r.abytes
  }
  println(
    "| 論證總字數（定義＋算式＋定理＋證明） | " +
    tb.to_string() +
    " |",
  )
  println("| 平均每條 | " + (tb / rows.length()).to_string() + " |")
  println("")
  println("## 二、依群組")
  println("")
  println(
    "| 群 | 條數 | 有對照 | 有成本 | 有定理 | 有反例／限制 | 平均字數 |",
  )
  println("| --- | ---: | ---: | ---: | ---: | ---: | ---: |")
  for g in @hilbert.audit_by_group() {
    println(
      "| " +
      g.0 +
      " | " +
      g.1.to_string() +
      " | " +
      g.2.to_string() +
      " | " +
      g.3.to_string() +
      " | " +
      g.4.to_string() +
      " | " +
      g.5.to_string() +
      " | " +
      g.6.to_string() +
      " |",
    )
  }
  println("")
  println("## 三、依軌道")
  println("")
  println("| 軌道 | 條數 |")
  println("| --- | ---: |")
  for t in @hilbert.audit_by_track() {
    println("| " + t.0 + " | " + t.1.to_string() + " |")
  }
  println("")
  println("## 四、依類別")
  println("")
  println("| 類別 | 條數 |")
  println("| --- | ---: |")
  for c in @hilbert.audit_by_cat() {
    println("| " + c.0 + " | " + c.1.to_string() + " |")
  }
  println("")
  println("## 五、覆蓋分佈")
  println("")
  println(
    "> 覆蓋分 = 對照 + 成本 + 定理 + 反例，各 1 分，滿分 4。",
  )
  println(
    "> **這是覆蓋評分不是品質評分** —— 它只問「有沒有做這四件事」，",
  )
  println(
    "> 不問「做得好不好」。四項都寫了但內容空洞的條目一樣拿滿分。",
  )
  println("> 它唯一的用途是找出連形式都缺的條目。")
  println("")
  let h = @hilbert.audit_score_hist()
  println("| 分數 | 條數 |")
  println("| ---: | ---: |")
  for i in 0..<5 {
    println("| " + i.to_string() + " | " + h[i].to_string() + " |")
  }
  println("")
  let weak = @hilbert.audit_weakest(1)
  println(
    "## 六、覆蓋分 ≤ 1 之條目（" +
    weak.length().to_string() +
    " 條）",
  )
  println("")
  if weak.length() == 0 {
    println("（無）")
  } else {
    println("| 代號 | 分 | 名稱 |")
    println("| --- | ---: | --- |")
    for w in weak {
      println("| " + pad(w.0, 5) + " | " + w.1.to_string() + " | " + w.2 + " |")
    }
  }
}

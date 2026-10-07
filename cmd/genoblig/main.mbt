// cmd/genoblig — N-45 義務自動生成器之進入點。
//
// 用法：
//   moon run cmd/genoblig > oblig_auto.mbt
//
// 產出的檔案可直接編譯並納入目錄。thm 與 proof 兩欄不在此處 ——
// 它們在 catalogue.mbt 的對應列，由人補寫。檔尾附上目錄列之模板
// （含佔位符），貼入 catalogue.mbt 後補證明即可。

///|
fn main {
  // 【第二十一輪】規格由 DSL 編譯而來，不再手寫結構。
  // DSL 原始碼見 @hilbert.dsl_law_source()；編譯器見 dsl.mbt。
  let spec = @hilbert.dsl_demo_spec()
  match @hilbert.gen_oblig_src(spec) {
    Some(src) => println(src)
    None =>
      println(
        "// 生成失敗：該律不成立、或找不到會被推翻的對照規則",
      )
  }
  println("")
  println(
    "// ─────────────────────────────────────────────────────────────",
  )
  println(
    "// 目錄列模板（請貼入 catalogue.mbt，並把兩個佔位符換成人寫的證明）",
  )
  println("//")
  match @hilbert.gen_cat_row(spec) {
    Some(row) =>
      for line in row.split("\n") {
        println("// " + line.to_owned())
      }
    None => println("// 目錄列生成失敗")
  }
  println("")
  let rspec = @hilbert.obl_demo_spec_r()
  match @hilbert.gen_oblig_src_r(rspec) {
    Some(src) => println(src)
    None =>
      println(
        "// ℝ 軌生成失敗：該律不成立、前提被違反、溢位、或規則不在生成器之表達範圍內",
      )
  }
  println("")
  println(
    "// ─────────────────────────────────────────────────────────────",
  )
  println(
    "// ℝ 軌目錄列模板（請貼入 catalogue.mbt，並把兩個佔位符換成人寫的證明）",
  )
  println("//")
  match @hilbert.gen_cat_row_r(rspec) {
    Some(row) =>
      for line in row.split("\n") {
        println("// " + line.to_owned())
      }
    None => println("// ℝ 軌目錄列生成失敗")
  }
  println("")
  println(
    "// ─────────────────────────────────────────────────────────────",
  )
  println("// N-62：普查式義務（DSL 第二種產出）")
  println("")
  match @hilbert.gen_census_src(@hilbert.cen_demo_spec()) {
    Some(src) => println(src)
    None => println("// 普查式生成失敗：表不存在或普查為空")
  }
  println("")
  println(
    "// ─────────────────────────────────────────────────────────────",
  )
  println("// 普查式目錄列模板")
  println("//")
  match @hilbert.gen_census_row(@hilbert.cen_demo_spec()) {
    Some(row) =>
      for line in row.split("\n") {
        println("// " + line.to_owned())
      }
    None => println("// 普查式目錄列生成失敗")
  }
  println("")
  println(
    "// ─────────────────────────────────────────────────────────────",
  )
  println("// N-74：成本比對式義務（DSL 第三種產出）")
  println("")
  match @hilbert.gen_compare_src(@hilbert.cmp_demo_spec()) {
    Some(src) => println(src)
    None =>
      println(
        "// 成本比對式生成失敗：掃描器不存在或語料為空",
      )
  }
  println("")
  println(
    "// ─────────────────────────────────────────────────────────────",
  )
  println("// 成本比對式目錄列模板")
  println("//")
  match @hilbert.gen_compare_row(@hilbert.cmp_demo_spec()) {
    Some(row) =>
      for line in row.split("\n") {
        println("// " + line.to_owned())
      }
    None => println("// 成本比對式目錄列生成失敗")
  }
}

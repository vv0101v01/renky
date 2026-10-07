// ============================================================================
//  cmd/main — 評審準則目錄之執行器
//  用法：
//    moon run cmd/main                    逐條執行全部義務（預設）
//    moon run cmd/main -- --only K        僅執行編號以 K 起首之條目（前綴，可用逗號分隔）
//    HILBERT_ONLY=K moon run cmd/main     同上（環境變數）
//    moon run cmd/main -- --help          印用法
//  逐條執行目錄中之「義務自證」，列印結果表與總結。
//  前綴過濾僅影響「執行哪些條目」，不改變任何條目之判準與實例數。
// ============================================================================

///|
/// 顯示寬度：僅 CJK／全形區段計 2 欄，數學符號（ℚ, √, ⊥, ✔）與框線計 1 欄。
fn dwidth(s : String) -> Int {
  let mut w = 0
  for c in s {
    let v = c.to_int()
    let wide = (v >= 0x1100 && v <= 0x115F) ||
      (v >= 0x2E80 && v <= 0x303E) ||
      (v >= 0x3041 && v <= 0x33FF) ||
      (v >= 0x3400 && v <= 0x4DBF) ||
      (v >= 0x4E00 && v <= 0x9FFF) ||
      (v >= 0xA000 && v <= 0xA4CF) ||
      (v >= 0xAC00 && v <= 0xD7A3) ||
      (v >= 0xF900 && v <= 0xFAFF) ||
      (v >= 0xFE30 && v <= 0xFE4F) ||
      (v >= 0xFF00 && v <= 0xFF60) ||
      (v >= 0xFFE0 && v <= 0xFFE6)
    w = w + (if wide { 2 } else { 1 })
  }
  w
}

///|
/// 取字串首字元
fn first_char(s : String) -> Char {
  for c in s {
    return c
  }
  'Z'
}

///|
/// 由條目編號之字母取得群組標題
fn group_title(code : String) -> String {
  let g = first_char(code)
  if g == 'A' {
    "A 群 · 體、純量與核心工具"
  } else if g == 'B' {
    "B 群 · 空間公理檢驗（具體空間）"
  } else if g == 'C' {
    "C 群 · 矩陣核心演算法"
  } else if g == 'D' {
    "D 群 · 抽象內積空間演算法（對任意空間泛型）"
  } else if g == 'E' {
    "E 群 · 具體空間之專屬定理"
  } else if g == 'F' {
    "F 群 · 空間構造子（組合爆炸）"
  } else if g == 'G' {
    "G 群 · 外代數與行列式幾何"
  } else if g == 'H' {
    "H 群 · 數值線性代數（ℝ 軌道．殘差憑證）"
  } else if g == 'I' {
    "I 群 · 四元數代數與旋轉群"
  } else if g == 'J' {
    "J 群 · 多項式與組合核心"
  } else if g == 'K' {
    "K 群 · 加速層 ℤ 管（純整數純 CRT 篩選）"
  } else if g == 'L' {
    "L 群 · 加速層 ℚ 管（Fp 層級有理數重建篩選）"
  } else {
    "M 群 · 加速層 𝔽[x] 管（多項式純 CRT 篩選）"
  }
}

///|
/// 右側補空白至指定顯示寬度
fn padw(s : String, n : Int) -> String {
  let w = dwidth(s)
  if w >= n {
    s
  } else {
    s + " ".repeat(n - w)
  }
}

///|
fn line(ch : String, n : Int) -> String {
  ch.repeat(n)
}

///|
fn maxi0(a : Int, b : Int) -> Int {
  if a > b {
    a
  } else {
    b
  }
}

///|
/// 解析選用之前綴過濾。命令列 `--only A,B` 優先，其次環境變數 `HILBERT_ONLY`。
/// 回空陣列表「不過濾」。
fn parse_only(argv : Array[String]) -> Array[String] {
  let out : Array[String] = []
  let mut spec : String? = None
  let mut i = 1
  while i < argv.length() {
    if argv[i] == "--only" {
      if i + 1 >= argv.length() {
        abort(
          "--only 需要一個前綴引數，例如：moon run cmd/main -- --only K",
        )
      }
      spec = Some(argv[i + 1])
      i = i + 2
    } else {
      i = i + 1
    }
  }
  match spec {
    Some(_) => ()
    None =>
      match @env.get_env_var("HILBERT_ONLY") {
        Some(e) => spec = Some(e)
        None => ()
      }
  }
  match spec {
    Some(s) =>
      for p in s.split(",") {
        let q = p.to_owned()
        if q != "" {
          out.push(q)
        }
      }
    None => ()
  }
  out
}

///|
/// 以逗號連接前綴（僅供訊息列印）
fn join_prefs(xs : Array[String]) -> String {
  let mut u = ""
  for i in 0..<xs.length() {
    if i > 0 {
      u = u + ","
    }
    u = u + xs[i]
  }
  u
}

///|
/// 條目編號是否符合任一前綴
fn code_in(prefixes : Array[String], code : String) -> Bool {
  let mut hit = false
  for p in prefixes {
    if code.has_prefix(p) {
      hit = true
    }
  }
  hit
}

///|
fn main {
  let argv = @env.args()
  let mut k = 1
  while k < argv.length() {
    if argv[k] == "--help" || argv[k] == "-h" {
      println("用法：moon run cmd/main [-- --only <前綴>[,...]]")
      println(
        "  --only K         僅執行編號以 K 起首之條目（如 K、N-7、N-8；逗號可分隔多個）",
      )
      println("  HILBERT_ONLY=K   等價於 --only K（環境變數）")
      println("  不給引數即逐條執行全部條目。")
      return
    }
    k = k + 1
  }
  let prefixes = parse_only(argv)
  let all = @hilbert.catalogue()
  let cat = if prefixes.length() == 0 {
    all
  } else {
    all.filter(a => code_in(prefixes, a.code))
  }
  if prefixes.length() > 0 && cat.length() == 0 {
    abort(
      "前綴「" +
      join_prefs(prefixes) +
      "」不匹配任何條目（全目錄 " +
      all.length().to_string() +
      " 條）。",
    )
  }
  println("")
  println(line("═", 100))
  println(
    "  公理化向量空間與有限維內積空間 — 評審準則目錄與義務自證",
  )
  println(
    "  axiom/hilbert v0.1.2 ·  MoonBit · 零第三方依賴（僅使用 core/builtin）",
  )
  if prefixes.length() > 0 {
    println(
      "  模式：僅執行前綴「" +
      join_prefs(prefixes) +
      "」之條目（" +
      cat.length().to_string() +
      "／" +
      all.length().to_string() +
      " 條）",
    )
  }
  println(line("═", 100))
  println("")

  // ---- 類別統計 ----
  println("【一】條目分佈")
  println(line("─", 100))
  let cc = @hilbert.category_counts()
  let mut row = "  "
  let mut k = 0
  for p in cc {
    row = row + padw(p.0 + " " + p.1.to_string() + " 條", 24)
    k = k + 1
    if k % 4 == 0 {
      println(row)
      row = "  "
    }
  }
  if row != "  " {
    println(row)
  }
  println("")
  println(
    "  目錄條目總數：" +
    all.length().to_string() +
    " 條（要求 > 80 條）",
  )
  if prefixes.length() > 0 {
    println(
      "  本次執行    ：" +
      cat.length().to_string() +
      " 條（前綴 " +
      join_prefs(prefixes) +
      "）",
    )
  }
  println("")

  // ---- 逐條執行 ----
  println("【二】逐條義務自證")
  println(line("─", 100))
  println(
    "  " +
    padw("編號", 7) +
    padw("名稱", 46) +
    padw("軌道", 20) +
    padw("實例", 7) +
    "判定",
  )
  println(line("─", 100))
  let mut passed = 0
  let mut instances = 0
  let failures : Array[String] = []
  let mut group = ""
  for a in cat {
    let g = group_title(a.code)
    if g != group {
      group = g
      println("")
      println("  ── " + g + " " + line("─", maxi0(2, 86 - dwidth(g))))
    }
    let c = (a.run)()
    instances = instances + c.trials
    if c.ok {
      passed = passed + 1
    } else {
      failures.push(a.code + " " + a.zh + "：" + c.detail)
    }
    println(
      "  " +
      padw(a.code, 7) +
      padw(a.zh, 46) +
      padw(a.track, 20) +
      padw(c.trials.to_string(), 7) +
      (if c.ok { "通過 ✔" } else { "失敗 ✘" }),
    )
  }
  println(line("─", 100))
  println("")

  // ---- 總結 ----
  println("【三】總結")
  println(line("─", 100))
  println("  條目總數        ：" + cat.length().to_string())
  println("  通過            ：" + passed.to_string())
  println("  失敗            ：" + (cat.length() - passed).to_string())
  println("  驗證實例總數    ：" + instances.to_string())
  println(
    "  精確軌道之意義  ：ℚ／ℚ(i) 上之算術無捨入誤差，恆等式判定為「真」即代數恆等式於該實例成立；",
  )
  println(
    "                    配合 Schwartz–Zippel 界，隨機實例全通過而命題為假之機率 < 10⁻³⁴。",
  )
  println(
    "  數值軌道之意義  ：回報事後殘差憑證 ‖R(X̂)‖ ≤ ε（ε 於各條目中列出），",
  )
  println(
    "                    依後向穩定性即「X̂ 為一個近鄰問題之精確解」。",
  )
  if failures.length() > 0 {
    println("")
    println("  未通過條目：")
    for f in failures {
      println("    ✘ " + f)
    }
  } else {
    println("")
    println(
      "  ✔ 全部義務通過：" +
      passed.to_string() +
      "/" +
      cat.length().to_string() +
      "，無未決條目。",
    )
  }
  println(line("═", 100))
  println("")
}

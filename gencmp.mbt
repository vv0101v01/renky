///|
/// # N-74 義務生成器第三種產出：成本比對式義務
///
/// N-62 讓生成器會寫普查式義務。但第八、九輪真正多出來的那一類 ——
/// N-65、N-67、N-71 那種「兩條路線、逐元相同、比成本」的義務 ——
/// 仍然一條一條手打。本條把那個模板也交給生成器。
///
/// ## 模板的骨架
///
/// ```text
///   語料 n 式 → 兩路各跑一次 → 逐元相同數 → 兩邊總成本 → 勝／敗數
///   生成器在產碼前先跑一次掃描，把上面五個數字釘進斷言
/// ```
///
/// 三道防線與 N-62 相同，第三道（敗例忠實）在這裡尤其要緊：
/// 比對式掃描**本來就會有敗例**（N-71 的外冪與 Kron 和就有 2 式較貴），
/// 一個只會寫 `lose != 0` 的生成器在這裡會直接產出一條永遠失敗的義務。

///|
/// 可被生成的比對掃描之規格。
pub struct CmpSpec {
  /// 目錄代號
  mscode : String
  /// 義務函式名
  msfn : String
  /// 掃描器名稱（須在 cmp_registry 內）
  msscan : String
  /// 中文標題
  mszh : String
}

///|
/// 比對掃描註冊表：名稱 → 回傳 (語料數, 逐元相同數, 通用成本, 特化成本, 勝, 敗)。
pub fn cmp_registry() -> Array[
  (String, () -> (Int, Int, Int64, Int64, Int, Int)),
] {
  [
    ("子空間", () => sub_scan(ob_rng())),
    ("外冪與 Kron 和", () => ek_scan(ob_rng())),
  ]
}

///|
/// 依名取出量測登記表之比較函式（回 (n, m, base, fast, …) 之量測函式）。
pub fn cmp_by_name(nm : String) -> (() -> (Int, Int, Int64, Int64, Int, Int))? {
  for e in cmp_registry() {
    if e.0 == nm {
      return Some(e.1)
    }
  }
  None
}

///|
/// 示範規格（全勝的掃描）。
pub fn cmp_demo_spec() -> CmpSpec {
  {
    mscode: "N-74g",
    msfn: "ob_n74g",
    msscan: "子空間",
    mszh: "子空間特化路徑之成本比對（生成）",
  }
}

///|
/// 對照規格（有敗例的掃描）。
pub fn cmp_control_spec() -> CmpSpec {
  {
    mscode: "N-74c",
    msfn: "ob_n74c",
    msscan: "外冪與 Kron 和",
    mszh: "外冪與 Kron 和特化路徑之成本比對（對照）",
  }
}

///|
/// 【DSL 第三種產出】由規格生成一條成本比對式義務之 MoonBit 原始碼。
pub fn gen_compare_src(spec : CmpSpec) -> String? {
  let f = match cmp_by_name(spec.msscan) {
    Some(x) => x
    None => return None
  }
  let (n, same, td, ts, win, lose) = f()
  if n == 0 {
    return None
  }
  let q = (x : String) => "\"" + x + "\""
  let ratio = td.to_double() / ts.to_double()
  let mut b = "///|\n"
  b = b +
    "/// ⚙️ 本函式由 `gen_compare_src`（N-74）**逐字自動產出**，請勿手改。\n"
  b = b +
    "/// 掃描器：" +
    spec.msscan +
    "。下列數字由生成器在產碼前當場量出。\n"
  b = b + "pub fn " + spec.msfn + "() -> Check {\n"
  b = b + "  let mut ok = true\n"
  b = b + "  match cmp_by_name(" + q(spec.msscan) + ") {\n"
  b = b + "    None => ok = false\n"
  b = b + "    Some(f) => {\n"
  b = b + "      let (n, same, td, ts, win, lose) = f()\n"
  b = b + "      if n != " + n.to_string() + " {\n        ok = false\n      }\n"
  // 逐元相同必須是全部 —— 這是比對式義務的前提，不是結論
  b = b + "      if same != n {\n        ok = false\n      }\n"
  b = b +
    "      if same != " +
    same.to_string() +
    " {\n        ok = false\n      }\n"
  b = b +
    "      if td != " +
    td.to_string() +
    "L || ts != " +
    ts.to_string() +
    "L {\n        ok = false\n      }\n"
  b = b +
    "      if win != " +
    win.to_string() +
    " {\n        ok = false\n      }\n"
  // 敗例忠實：如實寫出敗例數
  b = b +
    "      if lose != " +
    lose.to_string() +
    " {\n        ok = false\n      }\n"
  // 特化整體必須較便宜（這是「特化」兩個字的實質內容）
  b = b + "      if ts >= td {\n        ok = false\n      }\n"
  b = b + "      ignore(ok)\n"
  b = b + "    }\n"
  b = b + "  }\n"
  let detail = "掃描器 " +
    spec.msscan +
    "：語料 " +
    n.to_string() +
    " 式，兩路逐元相同 " +
    same.to_string() +
    "/" +
    n.to_string() +
    "（這是前提不是結論 —— 不相同的話成本比較沒有意義），" +
    "通用總成本 " +
    td.to_string() +
    "、特化總成本 " +
    ts.to_string() +
    "（×" +
    fmt_d(ratio, 3) +
    "），特化較便宜 " +
    win.to_string() +
    " 式、較貴 " +
    lose.to_string() +
    " 式。以上數字由生成器在產碼前當場量出並逐一釘入斷言；" +
    "敗例數 " +
    lose.to_string() +
    " 是如實寫下的，不是一律寫 0。"
  b = b +
    "  mk_check(\n    " +
    q(spec.mscode + " " + spec.mszh) +
    ",\n    ok,\n    " +
    (n * 2).to_string() +
    ",\n    " +
    q(detail) +
    ",\n  )\n}\n"
  Some(b)
}

///|
/// 對應之目錄列模板（thm 與 proof 留佔位符）。
pub fn gen_compare_row(spec : CmpSpec) -> String? {
  let f = match cmp_by_name(spec.msscan) {
    Some(x) => x
    None => return None
  }
  let (n, same, td, ts, win, lose) = f()
  let q = (x : String) => "\"" + x + "\""
  let ph = obl_placeholder()
  Some(
    "  xs.push({\n    code: " +
    q(spec.mscode) +
    ",\n    zh: " +
    q(spec.mszh) +
    ",\n    cat: \"中端\",\n    spaces: " +
    q(spec.msscan) +
    ",\n    deff: " +
    q(
      "兩條路線對同一語料逐式求解，先驗逐元相同，再比字乘法總成本。",
    ) +
    ",\n    formula: " +
    q(
      "增益 = 通用總成本 / 特化總成本 = " +
      td.to_string() +
      " / " +
      ts.to_string(),
    ) +
    ",\n    thm: " +
    q(
      "實測語料 " +
      n.to_string() +
      " 式，逐元相同 " +
      same.to_string() +
      "，勝 " +
      win.to_string() +
      " 敗 " +
      lose.to_string() +
      "。" +
      ph,
    ) +
    ",\n    proof: " +
    q(ph) +
    ",\n    track: \"精確 ℚ\",\n    run: " +
    spec.msfn +
    ",\n  })\n",
  )
}

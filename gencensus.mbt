///|
/// # N-62 義務生成器 DSL 之擴充：普查式義務
///
/// ## 生成器原本只會寫一種義務
///
/// N-45 的 `gen_oblig_src` 吃的是一條結構律 (Φ₂, Φ₁, C, ⊙)，吐的是
/// 「取樣 → 雙向對照 → 增益斷言」那一種義務。第六、七輪長出來的新東西
/// ——普查、逐軸敏感度、退化軸——它一個也不會寫。
///
/// 本條把 DSL 擴出第二種產出：**普查式義務**。規格變成三張表加兩個旋鈕，
/// 生成器先跑一次普查，再把量到的指紋、覆蓋、敏感度逐一釘進產出的程式碼。
///
/// ## 生成器不得寫小說
///
/// 這是生成器最容易出事的地方：它可以產出一段「看起來很嚴謹」但斷言的是
/// 自己瞎編的數字的程式碼。防線有三道，全部可執行：
///
/// ```text
///   1  決定性    —— 同一規格生成兩次，必須逐字元相同
///   2  量測忠實  —— 產出的字串裡的指紋，必須等於義務當場重跑一次的指紋
///   3  敗例忠實  —— 餵一個會被推翻的普查，產出必須如實寫 pass < cells，
///                   不能永遠寫 pass == cells
/// ```
///
/// 第三道是雙向對照。沒有它，一個「永遠產生 `tpass == tcells`」的生成器
/// 可以通過前兩道。

///|
/// 普查式義務之規格。
pub struct CenSpec {
  /// 目錄代號
  cscode : String
  /// 義務函式名
  csfn : String
  /// 三張表之名稱
  csa : String
  csb : String
  csc : String
  /// 分層步長
  csstep : Int
  /// 維數上限（0 = 不設限）
  csmax : Int
  /// 中文標題
  cszh : String
}

///|
/// 示範規格：擴充軸上的分層普查。
pub fn cen_demo_spec() -> CenSpec {
  {
    cscode: "N-62g",
    csfn: "ob_n62g",
    csa: "空間",
    csb: "構造子",
    csc: "D群",
    csstep: 17,
    csmax: 12,
    cszh: "擴充軸分層普查（45 × 14 × 23，step 17，維數上限 12）",
  }
}

///|
/// 對照規格：擾動表上的普查（必定有格被推翻）。
pub fn cen_control_spec() -> CenSpec {
  {
    cscode: "N-62c",
    csfn: "ob_n62c",
    csa: "空間⊥",
    csb: "構造子₀",
    csc: "D群",
    csstep: 1,
    csmax: 12,
    cszh: "擾動表普查（對照組）",
  }
}

///|
/// 取三張表；任一不存在即回傳 None。
fn cen_tables(spec : CenSpec) -> (TriTable, TriTable, TriTable)? {
  match (tri_by_name(spec.csa), tri_by_name(spec.csb), tri_by_name(spec.csc)) {
    (Some(a), Some(b), Some(c)) => Some((a, b, c))
    _ => None
  }
}

///|
/// 【DSL 新產出】由規格生成一條普查式義務之 MoonBit 原始碼。
///
/// 生成器在產碼**之前**先跑一次普查與一次逐軸敏感度量測，
/// 產出的每一個數字都來自那次量測。
pub fn gen_census_src(spec : CenSpec) -> String? {
  let ts = match cen_tables(spec) {
    Some(t) => t
    None => return None
  }
  let (ta, tb, tc) = ts
  let r = tri_product_memo(ta, tb, tc, spec.csstep, spec.csmax) // 【N-77】
  if r.tcells == 0 {
    return None
  }
  let s = tri_axis_sensitivity(ta, tb, tc, spec.csmax, 4)
  let q = (x : String) => "\"" + x + "\""
  let hdr = "///|\n" +
    "/// ⚙️ 本函式由 `gen_census_src`（N-62）**逐字自動產出**，請勿手改。\n" +
    "/// 規格：" +
    spec.csa +
    " × " +
    spec.csb +
    " × " +
    spec.csc +
    "，step " +
    spec.csstep.to_string() +
    "，維數上限 " +
    spec.csmax.to_string() +
    "。\n" +
    "/// 下列每一個數字都由生成器在產碼前當場量出，不是人寫的。\n"
  let mut b = hdr + "pub fn " + spec.csfn + "() -> Check {\n"
  b = b + "  let mut ok = true\n"
  b = b + "  let ta = tri_by_name(" + q(spec.csa) + ")\n"
  b = b + "  let tb = tri_by_name(" + q(spec.csb) + ")\n"
  b = b + "  let tc = tri_by_name(" + q(spec.csc) + ")\n"
  b = b + "  match (ta, tb, tc) {\n"
  b = b + "    (Some(a), Some(bb), Some(c)) => {\n"
  b = b +
    "      let r = tri_product(a, bb, c, " +
    spec.csstep.to_string() +
    ", " +
    spec.csmax.to_string() +
    ")\n"
  b = b +
    "      if r.tdigest != " +
    q(r.tdigest) +
    " {\n        ok = false\n      }\n"
  b = b +
    "      if r.tcells != " +
    r.tcells.to_string() +
    " || r.tpass != " +
    r.tpass.to_string() +
    " {\n        ok = false\n      }\n"
  b = b +
    "      if r.tcov.0 != " +
    r.tcov.0.to_string() +
    " || r.tcov.1 != " +
    r.tcov.1.to_string() +
    " || r.tcov.2 != " +
    r.tcov.2.to_string() +
    " {\n        ok = false\n      }\n"
  b = b +
    "      if r.tdmax != " +
    r.tdmax.to_string() +
    " {\n        ok = false\n      }\n"
  // 敗例忠實：如實寫出推翻格數，而不是一律寫「全過」
  if r.tpass == r.tcells {
    b = b + "      if r.tmisses.length() != 0 {\n        ok = false\n      }\n"
  } else {
    b = b +
      "      if r.tmisses.length() != " +
      (r.tcells - r.tpass).to_string() +
      " {\n        ok = false\n      }\n"
  }
  b = b +
    "      let sv = tri_axis_sensitivity(a, bb, c, " +
    spec.csmax.to_string() +
    ", 4)\n"
  b = b +
    "      if sv.0.0 != " +
    s.0.0.to_string() +
    " || sv.0.1 != " +
    s.0.1.to_string() +
    " {\n        ok = false\n      }\n"
  b = b +
    "      if sv.1.0 != " +
    s.1.0.to_string() +
    " || sv.1.1 != " +
    s.1.1.to_string() +
    " {\n        ok = false\n      }\n"
  b = b +
    "      if sv.2.0 != " +
    s.2.0.to_string() +
    " || sv.2.1 != " +
    s.2.1.to_string() +
    " {\n        ok = false\n      }\n"
  b = b + "      ignore(ok)\n"
  b = b + "    }\n"
  b = b + "    _ => ok = false\n"
  b = b + "  }\n"
  let detail = "規格 " +
    spec.csa +
    " × " +
    spec.csb +
    " × " +
    spec.csc +
    "（step " +
    spec.csstep.to_string() +
    "，維數上限 " +
    spec.csmax.to_string() +
    "）：" +
    r.tcells.to_string() +
    " 格，" +
    r.tpass.to_string() +
    " 格成立、" +
    (r.tcells - r.tpass).to_string() +
    " 格推翻，覆蓋 " +
    r.tcov.0.to_string() +
    "/" +
    r.tcov.1.to_string() +
    "/" +
    r.tcov.2.to_string() +
    "，最高維 " +
    r.tdmax.to_string() +
    "，指紋 " +
    r.tdigest +
    "。逐軸敏感度（切片有變動數／切片總數）：A 軸 " +
    s.0.0.to_string() +
    "/" +
    s.0.1.to_string() +
    "、B 軸 " +
    s.1.0.to_string() +
    "/" +
    s.1.1.to_string() +
    "、C 軸 " +
    s.2.0.to_string() +
    "/" +
    s.2.1.to_string() +
    "。以上數字由生成器在產碼前當場量出並逐一釘入斷言。"
  b = b +
    "  mk_check(\n    " +
    q(spec.cscode + " " + spec.cszh) +
    ",\n    ok,\n    " +
    r.tcells.to_string() +
    ",\n    " +
    q(detail) +
    ",\n  )\n}\n"
  Some(b)
}

///|
/// 【DSL 新產出】對應之目錄列模板（thm 與 proof 留佔位符，由人補寫）。
pub fn gen_census_row(spec : CenSpec) -> String? {
  let ts = match cen_tables(spec) {
    Some(t) => t
    None => return None
  }
  let (ta, tb, tc) = ts
  let r = tri_product_memo(ta, tb, tc, spec.csstep, spec.csmax) // 【N-77】
  let q = (x : String) => "\"" + x + "\""
  let ph = obl_placeholder()
  Some(
    "  xs.push({\n    code: " +
    q(spec.cscode) +
    ",\n    zh: " +
    q(spec.cszh) +
    ",\n    cat: \"中端\",\n    spaces: " +
    q(spec.csa + " × " + spec.csb + " × " + spec.csc) +
    ",\n    deff: " +
    q(
      "三表笛卡兒積之分層普查；格鍵為 判者@構造子[空間]，種子取自 str_hash64(格鍵)。",
    ) +
    ",\n    formula: " +
    q(
      "|普查| = |" +
      spec.csa +
      "| × |" +
      spec.csb +
      "| × |" +
      spec.csc +
      "|，分層條件 (i + 2j + 3k) mod " +
      spec.csstep.to_string() +
      " = 0",
    ) +
    ",\n    thm: " +
    q(
      "實測 " +
      r.tcells.to_string() +
      " 格，" +
      r.tpass.to_string() +
      " 格成立，指紋 " +
      r.tdigest +
      "。" +
      ph,
    ) +
    ",\n    proof: " +
    q(ph) +
    ",\n    track: \"精確 ℚ\",\n    run: " +
    spec.csfn +
    ",\n  })\n",
  )
}

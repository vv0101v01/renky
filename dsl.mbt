///|
/// # N-92 義務 DSL 之編譯器：詞法、語法、檢查、生成
///
/// ## 在此之前只有一半
///
/// 第七輪起本庫有一個「義務 DSL」—— 但它其實只是一個結構：
///
/// ```moonbit nocheck
///   OblSpec::{ ocode: "N-46", ofn: "ob_n46", oouter: "det", … }
/// ```
///
/// 使用者得用 MoonBit 把結構寫出來，再交給 `gen_oblig_src` 吐出義務原始碼。
/// 那是一個**生成器**，不是一個**語言** —— 它沒有表層語法、沒有詞法、
/// 沒有語法錯誤、也沒有錯誤訊息。寫錯欄位名時編譯器會抱怨 MoonBit 的
/// 型別，而不是抱怨 DSL 的拼字。
///
/// 本條把缺的那一半補上：**表層語法 → 詞法 → 語法 → 檢查 → 生成**，
/// 五個階段各自可測。
///
/// ## 表層語法
///
/// ```text
///   program := law*
///   law     := "law" IDENT "{" entry* "}"
///   entry   := IDENT "=" value
///   value   := IDENT | STRING
/// ```
///
/// 實例：
///
/// ```text
///   // 井號與雙斜線皆為註解，到行尾
///   law N-46 {
///     fn    = ob_n46
///     zh    = "自動生成之義務：det∘sq 於 ⊗ 下之複合律"
///     outer = det
///     inner = sq            # 一元律可省略此行
///     comb  = ⊗
///     rule  = ^
///     track = Q
///   }
/// ```
///
/// ## 語法補強（相對於原本的結構寫法）
///
/// ```text
///   註解          // 與 # 兩種，到行尾
///   欄位任意順序   不必照結構宣告的次序
///   選擇性欄位     inner 省略即表示一元律（原本要寫 oinner: ""）
///   值的兩種寫法   裸識別字或帶引號字串；含空白者必須加引號
///   非 ASCII       ⊗、∘、ℚ、中文一律視為識別字字元
///   錯誤定位       每個錯誤帶行:列，而不是只說「parse error」
/// ```
///
/// ## 定理 D-1（生成相容）
///
/// 對本庫既有的每一個 `OblSpec`，
/// `dsl_compile(dsl_print(spec))` 回傳的規格與原規格逐欄相同，
/// 因而 `gen_oblig_src` 之輸出**逐位元組相同**。
///
/// 這一條是整個編譯器唯一有意義的驗收：它保證換成語言之後，
/// 既有的 `oblig_auto.mbt` 一個位元都不會變（N-45 的雜湊因此仍然成立）。
///
/// ## 定理 D-2（印出—剖析往返）
///
/// `dsl_parse(dsl_print(spec)) = spec`，對任何合法規格成立。
///
/// ## 命題 D-3（錯誤要被拒絕，而且要說在哪裡）
///
/// 下列七類輸入各自被拒絕，且錯誤位置落在出錯的那一行：
/// 缺右大括號、缺等號、未知欄位、重複欄位、缺必要欄位、
/// 代號格式錯、未閉合字串。
///
/// **一個只會接受正確輸入的剖析器不算剖析器。**

///|
/// 來源位置（1 起算）。
pub struct DslPos {
  dline : Int
  dcol : Int
}

///|
/// 位置之可讀形式 `行:列`。
pub fn DslPos::show(self : DslPos) -> String {
  self.dline.to_string() + ":" + self.dcol.to_string()
}

///|
/// 詞法單元。
pub enum DslTok {
  TLaw
  TIdent(String)
  TStr(String)
  TLBrace
  TRBrace
  TEq
  TEof
}

///|
/// 帶位置的詞法單元。
pub struct DslToken {
  tk : DslTok
  tpos : DslPos
}

///|
/// 編譯錯誤。
pub struct DslErr {
  emsg : String
  epos : DslPos
}

///|
/// 錯誤之可讀形式。
pub fn DslErr::show(self : DslErr) -> String {
  self.epos.show() + " " + self.emsg
}

///|
/// 是否為空白。
fn dsl_is_space(c : Int) -> Bool {
  c == 32 || c == 9 || c == 10 || c == 13
}

///|
/// 是否為標點（自成一個單元）。
fn dsl_is_punct(c : Int) -> Bool {
  c == 123 || c == 125 || c == 61
}

///|
/// 詞法分析。
///
/// 非 ASCII（碼位 ≥ 128）一律視為識別字字元，故 ⊗、∘、ℚ 與中文
/// 都可以直接當識別字或值使用 —— 這是本庫的記號需要的。
pub fn dsl_lex(src : String) -> (Array[DslToken], Array[DslErr]) {
  let toks : Array[DslToken] = []
  let errs : Array[DslErr] = []
  let n = src.length()
  let mut i = 0
  let mut line = 1
  let mut col = 1
  fn adv(k : Int) -> Unit {
    for _t in 0..<k {
      if i < n && src[i].to_int() == 10 {
        line = line + 1
        col = 1
      } else {
        col = col + 1
      }
      i = i + 1
    }
  }

  while i < n {
    let c = src[i].to_int()
    if dsl_is_space(c) {
      adv(1)
      continue
    }
    // 註解：// 或 #，到行尾
    if c == 35 || (c == 47 && i + 1 < n && src[i + 1].to_int() == 47) {
      while i < n && src[i].to_int() != 10 {
        adv(1)
      }
      continue
    }
    let p = DslPos::{ dline: line, dcol: col, }
    if c == 123 {
      toks.push({ tk: TLBrace, tpos: p, })
      adv(1)
      continue
    }
    if c == 125 {
      toks.push({ tk: TRBrace, tpos: p, })
      adv(1)
      continue
    }
    if c == 61 {
      toks.push({ tk: TEq, tpos: p, })
      adv(1)
      continue
    }
    // 字串字面值
    if c == 34 {
      adv(1)
      let buf = StringBuilder()
      let mut closed = false
      while i < n {
        let d = src[i].to_int()
        if d == 34 {
          adv(1)
          closed = true
          break
        }
        if d == 10 {
          break
        }
        buf.write_string(src[i:i + 1].to_owned())
        adv(1)
      }
      if closed {
        toks.push({ tk: TStr(buf.to_string()), tpos: p, })
      } else {
        errs.push({ emsg: "字串未閉合（缺右引號）", epos: p, })
      }
      continue
    }
    // 識別字
    let buf = StringBuilder()
    while i < n {
      let d = src[i].to_int()
      if dsl_is_space(d) || dsl_is_punct(d) || d == 34 || d == 35 {
        break
      }
      if d == 47 && i + 1 < n && src[i + 1].to_int() == 47 {
        break
      }
      buf.write_string(src[i:i + 1].to_owned())
      adv(1)
    }
    let w = buf.to_string()
    if w == "law" {
      toks.push({ tk: TLaw, tpos: p, })
    } else {
      toks.push({ tk: TIdent(w), tpos: p, })
    }
  }
  toks.push({ tk: TEof, tpos: { dline: line, dcol: col, }, })
  (toks, errs)
}

///|
/// 剖析後的一條律（欄位尚未檢查）。
pub struct DslLaw {
  lcode : String
  lkeys : Array[String]
  lvals : Array[String]
  lpos : Array[DslPos]
  lat : DslPos
}

///|
/// 語法分析：program := law*。
///
/// 遇錯時跳到下一個 `law` 重新同步，使一次編譯能回報多個錯誤
/// 而不是只報第一個。
pub fn dsl_parse(toks : Array[DslToken]) -> (Array[DslLaw], Array[DslErr]) {
  let laws : Array[DslLaw] = []
  let errs : Array[DslErr] = []
  let mut i = 0
  fn peek() -> DslToken {
    toks[i]
  }

  fn sync() -> Unit {
    while i < toks.length() - 1 {
      match toks[i].tk {
        TLaw => return
        _ => i = i + 1
      }
    }
  }

  while i < toks.length() {
    match peek().tk {
      TEof => break
      TLaw => {
        let at = peek().tpos
        i = i + 1
        // 代號
        let code = match peek().tk {
          TIdent(s) => {
            i = i + 1
            s
          }
          _ => {
            errs.push({
              emsg: "law 之後應為代號（如 N-46）",
              epos: peek().tpos,
            })
            sync()
            continue
          }
        }
        match peek().tk {
          TLBrace => i = i + 1
          _ => {
            errs.push({ emsg: "代號之後應為 {", epos: peek().tpos, })
            sync()
            continue
          }
        }
        let keys : Array[String] = []
        let vals : Array[String] = []
        let poss : Array[DslPos] = []
        let mut closed = false
        while i < toks.length() {
          match peek().tk {
            TRBrace => {
              i = i + 1
              closed = true
              break
            }
            TEof => break
            TIdent(k) => {
              let kp = peek().tpos
              i = i + 1
              match peek().tk {
                TEq => i = i + 1
                _ => {
                  errs.push({
                    emsg: "欄位 " + k + " 之後應為 =",
                    epos: peek().tpos,
                  })
                  sync()
                  break
                }
              }
              match peek().tk {
                TIdent(v) => {
                  i = i + 1
                  keys.push(k)
                  vals.push(v)
                  poss.push(kp)
                }
                TStr(v) => {
                  i = i + 1
                  keys.push(k)
                  vals.push(v)
                  poss.push(kp)
                }
                _ => {
                  errs.push({ emsg: "= 之後應為值", epos: peek().tpos, })
                  sync()
                  break
                }
              }
            }
            _ => {
              errs.push({
                emsg: "律之內應為「欄位 = 值」",
                epos: peek().tpos,
              })
              sync()
              break
            }
          }
        }
        if closed {
          laws.push({
            lcode: code,
            lkeys: keys,
            lvals: vals,
            lpos: poss,
            lat: at,
          })
        } else {
          errs.push({ emsg: "律 " + code + " 缺右大括號 }", epos: at, })
        }
      }
      _ => {
        errs.push({ emsg: "頂層只允許 law 宣告", epos: peek().tpos, })
        sync()
      }
    }
  }
  (laws, errs)
}

///|
/// 合法欄位名。
pub fn dsl_fields() -> Array[String] {
  ["fn", "zh", "outer", "inner", "comb", "rule", "track"]
}

///|
/// 必要欄位（`inner` 為選擇性）。
pub fn dsl_required() -> Array[String] {
  ["fn", "zh", "outer", "comb", "rule", "track"]
}

///|
/// 語意檢查：未知欄位、重複欄位、缺必要欄位、代號與函式名之形狀。
pub fn dsl_check(laws : Array[DslLaw]) -> Array[DslErr] {
  let errs : Array[DslErr] = []
  for l in laws {
    // 代號形狀 N-数字
    let c = l.lcode
    let okcode = c.length() >= 3 &&
      c[0].to_int() == 78 &&
      c[1].to_int() == 45 &&
      (() => {
        let mut d = true
        for t in 2..<c.length() {
          let x = c[t].to_int()
          if x < 48 || x > 57 {
            d = false
          }
        }
        d
      })()
    if !okcode {
      errs.push({
        emsg: "代號 " + c + " 不符 N-<數字> 之形式",
        epos: l.lat,
      })
    }
    for t in 0..<l.lkeys.length() {
      let k = l.lkeys[t]
      let mut known = false
      for f in dsl_fields() {
        if f == k {
          known = true
        }
      }
      if !known {
        errs.push({ emsg: "未知欄位 " + k, epos: l.lpos[t], })
      }
      let mut dup = 0
      for u in 0..<l.lkeys.length() {
        if l.lkeys[u] == k {
          dup = dup + 1
        }
      }
      if dup > 1 && t == 0 {

      }
    }
    // 重複欄位（只報第二次出現者）
    for t in 0..<l.lkeys.length() {
      for u in 0..<t {
        if l.lkeys[u] == l.lkeys[t] {
          errs.push({
            emsg: "欄位 " + l.lkeys[t] + " 重複",
            epos: l.lpos[t],
          })
        }
      }
    }
    for r in dsl_required() {
      let mut has = false
      for k in l.lkeys {
        if k == r {
          has = true
        }
      }
      if !has {
        errs.push({ emsg: "缺必要欄位 " + r, epos: l.lat, })
      }
    }
    // 函式名須以 ob_ 開頭
    for t in 0..<l.lkeys.length() {
      if l.lkeys[t] == "fn" {
        let v = l.lvals[t]
        if v.length() < 3 ||
          v[0].to_int() != 111 ||
          v[1].to_int() != 98 ||
          v[2].to_int() != 95 {
          errs.push({
            emsg: "函式名 " + v + " 應以 ob_ 開頭",
            epos: l.lpos[t],
          })
        }
      }
    }
  }
  errs
}

///|
/// 取欄位值（不存在時回空字串）。
pub fn dsl_get(l : DslLaw, k : String) -> String {
  for t in 0..<l.lkeys.length() {
    if l.lkeys[t] == k {
      return l.lvals[t]
    }
  }
  ""
}

///|
/// 由檢查通過的律造出 `OblSpec`。
pub fn dsl_to_spec(l : DslLaw) -> OblSpec {
  {
    ocode: l.lcode,
    ofn: dsl_get(l, "fn"),
    oouter: dsl_get(l, "outer"),
    oinner: dsl_get(l, "inner"),
    ocomb: dsl_get(l, "comb"),
    orule: dsl_get(l, "rule"),
    ozh: dsl_get(l, "zh"),
    otrack: dsl_get(l, "track"),
  }
}

///|
/// 值是否需要加引號（含空白或為空）。
fn dsl_needs_quote(v : String) -> Bool {
  if v.length() == 0 {
    return true
  }
  for i in 0..<v.length() {
    let c = v[i].to_int()
    if dsl_is_space(c) || dsl_is_punct(c) || c == 34 || c == 35 {
      return true
    }
  }
  false
}

///|
/// 印出規格之標準表層形式（`dsl_parse` 之逆，見定理 D-2）。
pub fn dsl_print(spec : OblSpec) -> String {
  let q = (v : String) => if dsl_needs_quote(v) { "\"" + v + "\"" } else { v }
  let b = StringBuilder()
  b.write_string("law " + spec.ocode + " {\n")
  b.write_string("  fn    = " + q(spec.ofn) + "\n")
  b.write_string("  zh    = " + q(spec.ozh) + "\n")
  b.write_string("  outer = " + q(spec.oouter) + "\n")
  if spec.oinner != "" {
    b.write_string("  inner = " + q(spec.oinner) + "\n")
  }
  b.write_string("  comb  = " + q(spec.ocomb) + "\n")
  b.write_string("  rule  = " + q(spec.orule) + "\n")
  b.write_string("  track = " + q(spec.otrack) + "\n")
  b.write_string("}\n")
  b.to_string()
}

///|
/// 完整編譯：原始碼 → 規格陣列 ＋ 錯誤陣列。
///
/// 有任何錯誤時仍回傳已成功剖析的規格，讓呼叫端自行決定是否採用；
/// 但 `cmd/genoblig` 一律要求錯誤為空。
pub fn dsl_compile(src : String) -> (Array[OblSpec], Array[DslErr]) {
  let (toks, lerr) = dsl_lex(src)
  let (laws, perr) = dsl_parse(toks)
  let cerr = dsl_check(laws)
  let errs : Array[DslErr] = []
  for e in lerr {
    errs.push(e)
  }
  for e in perr {
    errs.push(e)
  }
  for e in cerr {
    errs.push(e)
  }
  let specs : Array[OblSpec] = []
  if errs.length() == 0 {
    for l in laws {
      specs.push(dsl_to_spec(l))
    }
  }
  (specs, errs)
}

///|
/// 兩個規格是否逐欄相同。
pub fn dsl_spec_eq(a : OblSpec, b : OblSpec) -> Bool {
  a.ocode == b.ocode &&
  a.ofn == b.ofn &&
  a.oouter == b.oouter &&
  a.oinner == b.oinner &&
  a.ocomb == b.ocomb &&
  a.orule == b.orule &&
  a.ozh == b.ozh &&
  a.otrack == b.otrack
}

// ---------------------------------------------------------------------------
//  DSL 作為生成器的真正來源
// ---------------------------------------------------------------------------

///|
/// ℚ 軌示範律之 DSL 原始碼。
///
/// 這份文字**就是** `cmd/genoblig` 的輸入 —— 不是文件裡的範例。
/// 編譯器若壞了，`oblig_auto.mbt` 會當場變成另一個檔案，而 N-45
/// 釘死的雜湊會失敗。把語言接進產品路徑，才算是一個編譯器；
/// 放在旁邊當示範的那叫範例。
pub fn dsl_law_source() -> String {
  "// axiom/hilbert 義務 DSL —— cmd/genoblig 之輸入\n" +
  "//\n" +
  "// 語法： law <代號> { 欄位 = 值 … }\n" +
  "// 欄位： fn zh outer inner comb rule track（inner 可省略，表一元律）\n" +
  "\n" +
  "law N-46 {\n" +
  "  fn    = ob_n46\n" +
  "  zh    = \"自動生成之義務：det∘sq 於 ⊗ 下之複合律\"\n" +
  "  outer = det\n" +
  "  inner = sq\n" +
  "  comb  = ⊗\n" +
  "  rule  = ^\n" +
  "  track = Q\n" +
  "}\n"
}

///|
/// 由 DSL 原始碼編譯出的示範規格。
///
/// 編譯失敗時退回手寫規格 —— 退路存在是為了讓 `cmd/genoblig` 不會
/// 因為 DSL 的疏失而產生殘缺輸出；而「退路從未被用到」這件事
/// 由 N-92 的義務以 `dsl_compile` 之錯誤數為 0 釘死。
pub fn dsl_demo_spec() -> OblSpec {
  let (specs, errs) = dsl_compile(dsl_law_source())
  if errs.length() == 0 && specs.length() == 1 {
    specs[0]
  } else {
    obl_demo_spec()
  }
}

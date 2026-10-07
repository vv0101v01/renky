///|
/// # N-45 義務自動生成
///
/// ## 最後一道人工關卡
///
/// 第三、四輪把管線接到了「引擎找到律 → 合成器自動組出演算法」。
/// 但**從一條律到一條目錄條目**仍然全靠手打：一段 `ob_*` 函式、
/// 一列 `catalogue.mbt`，每條六十行上下。目錄已經兩百條，
/// 這道關卡是生成器與交付物之間唯一還沒自動化的地方。
///
/// ## 分工（以可執行檢查固定，而非以註解約定）
///
/// ```text
///   生成器寫：deff（含量測結果）、formula（算式）、
///             ob_* 函式（取樣、雙向對照、空洞樣本計數、增益斷言、對照組）
///   後續補入：thm（定理敘述）、proof（代數證明）
/// ```
///
/// 生成器在 thm 與 proof 兩欄寫一個顯眼的佔位符，`ob_n45` 去數它出現
/// 幾次（目錄列中恰 2 次、義務函式中 0 次），故此分工一旦被改動，
/// 稽核當場失敗。
///
/// ## 生成器自己也要量測
///
/// 生成的義務裡有兩個數字不能瞎寫：增益門檻、以及對照組該用哪條錯規則。
/// 生成器在產碼**之前**先跑一次搜尋引擎：量出真實增益後取一半作為門檻，
/// 並逐一試出一條「確實會被推翻」的對照規則。於是生成出來的義務不是
/// 空殼 —— 它帶著一個保證會失敗的對照組，證明它真的有鑑別力。

///|
/// 一條待生成之義務的規格
pub struct OblSpec {
  /// 目錄代號，如 "N-46"
  ocode : String
  /// 義務函式名，如 "ob_n46"
  ofn : String
  /// 外層 Φ₂
  oouter : String
  /// 內層 Φ₁；空字串表示這是一條單一 Φ 的律
  oinner : String
  /// 組合子 C
  ocomb : String
  /// 規則 ⊙
  orule : String
  /// 中文標題
  ozh : String
  /// 軌道："Q"（精確 ℚ，字乘法）或 "R"（ℝ，flop + 容差）
  otrack : String
}

///|
/// 佔位符 —— 人必須補上的欄位。`ob_n45` 會確認它還在。
pub fn obl_placeholder() -> String {
  "⟨此欄為代數證明，機器不產出；須由人補寫⟩"
}

///|
/// 把一個字串包成 MoonBit 原始碼中的字串字面量
fn srcq(s : String) -> String {
  "\"" + s + "\""
}

///|
/// Φ 之原始碼：由名稱產出一段計算 `Mat[Q]?` 的 MoonBit 運算式。
///
/// `arg` 必須是一個簡單變數名（sq／cube 會重複使用它）。
pub fn phi_src(name : String, arg : String, cost : String) -> String? {
  if name == "inv" {
    Some("qinv_gauss(" + arg + ", " + cost + ")")
  } else if name == "tr̃ans" {
    Some("Some(" + arg + ".transpose())")
  } else if name == "sq" {
    Some("Some(qmul_cost(" + cost + ", " + arg + ", " + arg + "))")
  } else if name == "adj" {
    Some("qadj(" + cost + ", " + arg + ")")
  } else if name == "cube" {
    Some(
      "Some(qmul_cost(" +
      cost +
      ", " +
      arg +
      ", qmul_cost(" +
      cost +
      ", " +
      arg +
      ", " +
      arg +
      ")))",
    )
  } else if name == "det" {
    Some("Some(q_scalar_mat(qdet_gauss(" + arg + ", " + cost + ")))")
  } else if name == "trace" {
    Some("Some(q_scalar_mat(qtrace(" + cost + ", " + arg + ")))")
  } else if name == "rank" {
    Some("Some(q_scalar_mat(Q::of_int(mrank(" + arg + "))))")
  } else {
    None
  }
}

///|
/// 組合子之原始碼
pub fn comb_src(name : String, a : String, b : String) -> String? {
  if name == "⊗" {
    Some("mkron(" + a + ", " + b + ")")
  } else if name == "⊕" {
    Some("qblock_diag(" + a + ", " + b + ")")
  } else if name == "⊞" {
    Some("qkron_sum(" + a + ", " + b + ")")
  } else {
    None
  }
}

///|
/// 規則之原始碼。`ax`、`by` 為**該規則之運算元**（帶維數與行列式修正者會讀）。
pub fn rule_src(
  name : String,
  x : String,
  y : String,
  ax : String,
  by : String,
  cost : String,
) -> String? {
  if name == "⊗" {
    Some("Some(qkron_cost(" + cost + ", " + x + ", " + y + "))")
  } else if name == "⊕" {
    Some("Some(qblock_diag(" + x + ", " + y + "))")
  } else if name == "⊗ₛ" {
    Some(
      "Some(qsmul_cost(" +
      cost +
      ", cq_mul(" +
      cost +
      ", qpow_cost(" +
      cost +
      ", qdet_gauss(" +
      ax +
      ", " +
      cost +
      "), " +
      by +
      ".mrows - 1), qpow_cost(" +
      cost +
      ", qdet_gauss(" +
      by +
      ", " +
      cost +
      "), " +
      ax +
      ".mrows - 1)), qkron_cost(" +
      cost +
      ", " +
      x +
      ", " +
      y +
      ")))",
    )
  } else if name == "·" {
    Some(
      "Some(q_scalar_mat(cq_mul(" +
      cost +
      ", " +
      x +
      ".data[0], " +
      y +
      ".data[0])))",
    )
  } else if name == "+" {
    Some(
      "Some(q_scalar_mat(cq_add(" +
      cost +
      ", " +
      x +
      ".data[0], " +
      y +
      ".data[0])))",
    )
  } else if name == "^" {
    Some(
      "Some(q_scalar_mat(cq_mul(" +
      cost +
      ", qpow_cost(" +
      cost +
      ", " +
      x +
      ".data[0], " +
      by +
      ".mrows), qpow_cost(" +
      cost +
      ", " +
      y +
      ".data[0], " +
      ax +
      ".mrows))))",
    )
  } else {
    None
  }
}

///|
/// 把 Φ₂∘Φ₁ 施於 `arg`（內層為空則退化為單一 Φ）
fn compose_src(
  spec : OblSpec,
  arg : String,
  tmp : String,
  cost : String,
) -> String? {
  if spec.oinner == "" {
    phi_src(spec.oouter, arg, cost)
  } else {
    match (phi_src(spec.oinner, arg, cost), phi_src(spec.oouter, tmp, cost)) {
      (Some(a), Some(b)) =>
        Some(
          "match " +
          a +
          " { Some(" +
          tmp +
          ") => " +
          b +
          "\n        None => None }",
        )
      _ => None
    }
  }
}

///|
/// 【演算法】挑一條**確實會被推翻**的對照規則。
///
/// 生成器在產碼之前先跑引擎：逐一試過同類的其他規則，取第一條被推翻者。
/// 若每一條都成立，回傳 None —— 那表示這條律沒有鑑別力，不該被生成。
pub fn pick_control_rule(spec : OblSpec) -> String? {
  let rules = if phi_is_scalar(spec.oouter) {
    ["·", "+", "^"]
  } else {
    ["⊗", "⊕", "⊗ₛ"]
  }
  for r in rules {
    if r == spec.orule {
      continue
    }
    let inner = if spec.oinner == "" { spec.oouter } else { spec.oinner }
    let v = if spec.oinner == "" {
      comp_check(
        spec.oouter,
        spec.oouter,
        spec.ocomb,
        r,
        law_samples_mixed(),
        comp_rng_of(spec.oouter, inner, spec.ocomb, r),
      )
    } else {
      comp_check(
        spec.oouter,
        spec.oinner,
        spec.ocomb,
        r,
        law_samples_mixed(),
        comp_rng_of(spec.oouter, inner, spec.ocomb, r),
      )
    }
    match v {
      Some((vd, _vac)) => if !vd.holds { return Some(r) }
      None => ()
    }
  }
  None
}

///|
/// 完整量測：(成立, 增益, 空洞樣本數, 直接路徑字乘法, 分解路徑字乘法)。
///
/// 生成器寫進條目的每一個數字都來自這裡 —— 條目裡不該出現任何
/// 「大約」「顯著」之類沒有來源的詞。
pub fn obl_measure_full(spec : OblSpec) -> (Bool, Double, Int, Int64, Int64)? {
  let inner = if spec.oinner == "" { spec.oouter } else { spec.oinner }
  match
    comp_check(
      spec.oouter,
      inner,
      spec.ocomb,
      spec.orule,
      law_samples_mixed(),
      comp_rng_of(spec.oouter, inner, spec.ocomb, spec.orule),
    ) {
    Some((v, vac)) => Some((v.holds, v.lgain(), vac, v.base_cost, v.fast_cost))
    None => None
  }
}

///|
/// 【演算法 203】由一條律產出一段**可直接編譯**的義務函式原始碼。
///
/// 產出的內容：取樣迴圈、直接路徑、分解路徑、逐樣本比對、空洞樣本計數、
/// 成本累計、增益斷言（門檻 = 實測增益之半）、對照組（一條保證被推翻的
/// 錯規則）、以及填好數字的 `mk_check`。
///
/// **不產出**：thm 與 proof。那兩欄在目錄列裡是佔位符。
pub fn gen_oblig_src(spec : OblSpec) -> String? {
  let name = if spec.oinner == "" {
    spec.oouter
  } else {
    spec.oouter + "∘" + spec.oinner
  }
  let inner = if spec.oinner == "" { spec.oouter } else { spec.oinner }
  let ctrl = pick_control_rule(spec)
  let meas = obl_measure_full(spec)
  match (ctrl, meas) {
    (Some(cr), Some((holds, gain, vac, bcost, fcost))) => {
      if !holds {
        return None
      }
      let thr = fmt_d(gain * 0.5, 2)
      let cmb = match comb_src(spec.ocomb, "a", "b") {
        Some(t) => t
        None => return None
      }
      let lhs = match compose_src(spec, "g", "t0", "cd") {
        Some(t) => t
        None => return None
      }
      // 分解路徑之本體。內層 Φ 只算一次 —— 它既是外層 Φ 的輸入，
      // 又是 ⊙ 的運算元（⊗ₛ 與 ^ 會讀它的維數與行列式）。
      let opa = if spec.oinner == "" { "a" } else { "ia" }
      let opb = if spec.oinner == "" { "b" } else { "ib" }
      let rl = match rule_src(spec.orule, "xa", "xb", opa, opb, "cf") {
        Some(t) => t
        None => return None
      }
      let rlc = match rule_src(cr, "xa", "xb", opa, opb, "cc") {
        Some(t) => t
        None => return None
      }
      let oa = match phi_src(spec.oouter, opa, "cf") {
        Some(t) => t
        None => return None
      }
      let ob = match phi_src(spec.oouter, opb, "cf") {
        Some(t) => t
        None => return None
      }
      let mkcore = (ind : String) => {
        ind +
        "(Some(xa), Some(xb)) => {\n" +
        ind +
        "  rhs = " +
        rl +
        "\n" +
        ind +
        "  wrong = " +
        rlc +
        "\n" +
        ind +
        "}\n" +
        ind +
        "_ => ()\n"
      }
      let body = if spec.oinner == "" {
        "    match (" + oa + ", " + ob + ") {\n" + mkcore("      ") + "    }\n"
      } else {
        let ia = match phi_src(spec.oinner, "a", "cf") {
          Some(t) => t
          None => return None
        }
        let ib = match phi_src(spec.oinner, "b", "cf") {
          Some(t) => t
          None => return None
        }
        "    match (" +
        ia +
        ", " +
        ib +
        ") {\n" +
        "      (Some(ia), Some(ib)) =>\n" +
        "        match (" +
        oa +
        ", " +
        ob +
        ") {\n" +
        mkcore("          ") +
        "        }\n" +
        "      _ => ()\n" +
        "    }\n"
      }
      let s = "///|\n" +
        "/// ⚙️ 本函式由 `gen_oblig_src`（N-45）**逐字自動產出**，請勿手改。\n" +
        "/// 重現方式：`moon run cmd/genoblig | diff - oblig_auto.mbt`，應無差異。\n" +
        "///\n" +
        "/// 機器產出的是骨架與可執行的量測；thm 與 proof 兩欄不在此處，\n" +
        "/// 它們在 catalogue.mbt 的 " +
        spec.ocode +
        " 列，由人補寫。\n" +
        "pub fn " +
        spec.ofn +
        "() -> Check {\n" +
        "  let mut ok = true\n" +
        "  let mut vac = 0\n" +
        "  let mut agree = 0\n" +
        "  let mut ctrl_same = 0\n" +
        "  let mut base = 0L\n" +
        "  let mut fast = 0L\n" +
        "  let samples = law_samples_mixed()\n" +
        "  let rng = comp_rng_of(" +
        srcq(spec.oouter) +
        ", " +
        srcq(inner) +
        ", " +
        srcq(spec.ocomb) +
        ", " +
        srcq(spec.orule) +
        ")\n" +
        "  for sm in samples {\n" +
        "    let (n, m, sampler) = sm\n" +
        "    let a = sampler(rng, n)\n" +
        "    let b = sampler(rng, m)\n" +
        "    // 直接路徑：先組 " +
        spec.ocomb +
        "，再在 nm 階上施以 " +
        name +
        "\n" +
        "    let cd = Cost::new()\n" +
        "    let g = " +
        cmb +
        "\n" +
        "    let lhs = " +
        lhs +
        "\n" +
        "    // 分解路徑：兩側各自施以 " +
        name +
        "，再以 " +
        spec.orule +
        " 合成\n" +
        "    // 對照組 cc：把 " +
        spec.orule +
        " 換成 " +
        cr +
        "，必須被推翻 —— 否則本義務沒有鑑別力\n" +
        "    let cf = Cost::new()\n" +
        "    let cc = Cost::new()\n" +
        "    let mut rhs : Mat[Q]? = None\n" +
        "    let mut wrong : Mat[Q]? = None\n" +
        body +
        "    match (lhs, rhs) {\n" +
        "      (Some(u), Some(v)) =>\n" +
        "        if u.equals(v) {\n" +
        "          agree = agree + 1\n" +
        "        } else {\n" +
        "          ok = false\n" +
        "        }\n" +
        "      (None, None) => {\n" +
        "        vac = vac + 1\n" +
        "        agree = agree + 1\n" +
        "      }\n" +
        "      _ => ok = false\n" +
        "    }\n" +
        "    match (lhs, wrong) {\n" +
        "      (Some(u), Some(v)) => if u.equals(v) { ctrl_same = ctrl_same + 1 }\n" +
        "      (None, None) => ctrl_same = ctrl_same + 1\n" +
        "      _ => ()\n" +
        "    }\n" +
        "    base = base + cd.wmul\n" +
        "    fast = fast + cf.wmul\n" +
        "    ignore(cc)\n" +
        "  }\n" +
        "  if agree != samples.length() {\n" +
        "    ok = false\n" +
        "  }\n" +
        "  if ctrl_same == samples.length() {\n" +
        "    ok = false\n" +
        "  }\n" +
        "  let gain = if fast <= 0L {\n    0.0\n  } else {\n    base.to_double() / fast.to_double()\n  }\n" +
        "  // 門檻 = 生成時實測增益（×" +
        fmt_d(gain, 2) +
        "）之半，留一倍餘裕\n" +
        "  if !(gain > " +
        thr +
        ") {\n" +
        "    ok = false\n" +
        "  }\n" +
        "  mk_check(\n" +
        "    " +
        srcq(spec.ocode + " " + spec.ozh) +
        ",\n" +
        "    ok,\n" +
        "    samples.length() * 2,\n" +
        "    " +
        srcq(
          "律 " +
          name +
          "(A " +
          spec.ocomb +
          " B) = " +
          name +
          "(A) " +
          spec.orule +
          " " +
          name +
          "(B)：於尺寸 " +
          law_samples_dims() +
          "、分布 " +
          law_samples_label() +
          " 之 " +
          law_samples_mixed().length().to_string() +
          " 組樣本上逐元相符，空洞樣本 " +
          vac.to_string() +
          " 個。成本實測：直接路徑 " +
          bcost.to_string() +
          " 次字乘法、分解路徑 " +
          fcost.to_string() +
          " 次，增益 ×" +
          fmt_d(gain, 2) +
          "；義務門檻設為 ×" +
          thr +
          "（實測之半）。對照組以 " +
          cr +
          " 取代 " +
          spec.orule +
          " 後被推翻，故本義務有鑑別力。⚙️ 本義務函式由 gen_oblig_src 自動產出；thm 與 proof 欄由人補寫。",
        ) +
        ",\n" +
        "  )\n" +
        "}"
      Some(s)
    }
    _ => None
  }
}

///|
/// 【演算法】由一條律產出 `catalogue.mbt` 的目錄列。
///
/// deff 與 formula 由模板填充；**thm 與 proof 只寫佔位符**。
pub fn gen_cat_row(spec : OblSpec) -> String? {
  let name = if spec.oinner == "" {
    spec.oouter
  } else {
    spec.oouter + "∘" + spec.oinner
  }
  let cr = match pick_control_rule(spec) {
    Some(r) => r
    None => "—"
  }
  match obl_measure_full(spec) {
    Some((holds, gain, vac, bcost, fcost)) => {
      if !holds {
        return None
      }
      Some(
        "  xs.push({\n" +
        "    code: " +
        srcq(spec.ocode) +
        ",\n" +
        "    zh: " +
        srcq(spec.ozh) +
        ",\n" +
        "    cat: " +
        srcq("結構律") +
        ",\n" +
        "    spaces: " +
        srcq("組合子 " + spec.ocomb + " 下之複合演算法 " + name) +
        ",\n" +
        "    deff: " +
        srcq(
          "本列由 N-45 之生成器自 N-42 的複合定律表產出。律的來源是推導而非搜尋：" +
          name +
          " 不在搜尋引擎的 Φ 集內，它是由內層律（" +
          spec.oinner +
          " 於 " +
          spec.ocomb +
          " 下，其規則同時是一個組合子）與外層律（" +
          spec.oouter +
          "）依複合定理（定理 201-1）接起來的，推導階段零次矩陣運算。以下每個數字都是量出來的：於尺寸 " +
          law_samples_dims() +
          "、分布 " +
          law_samples_label() +
          " 之 " +
          law_samples_mixed().length().to_string() +
          " 組樣本上兩條路徑逐元相符；直接路徑 " +
          bcost.to_string() +
          " 次字乘法、分解路徑 " +
          fcost.to_string() +
          " 次，增益 ×" +
          fmt_d(gain, 2) +
          "；空洞樣本（兩側皆 ⊥ 而被判相符者）" +
          vac.to_string() +
          " 個；對照組以 " +
          cr +
          " 取代 " +
          spec.orule +
          " 後被推翻。",
        ) +
        ",\n" +
        "    formula: " +
        srcq(
          name +
          "(A " +
          spec.ocomb +
          " B) = " +
          name +
          "(A) " +
          spec.orule +
          " " +
          name +
          "(B)",
        ) +
        ",\n" +
        "    thm: " +
        srcq(obl_placeholder()) +
        ",\n" +
        "    proof: " +
        srcq(obl_placeholder()) +
        ",\n" +
        "    track: " +
        srcq("精確 ℚ") +
        ",\n" +
        "    run: " +
        spec.ofn +
        ",\n" +
        "  })\n",
      )
    }
    None => None
  }
}

///|
/// 本輪實際生成的那一條：det∘sq / ⊗ / ^（N-46）。
///
/// 選它的理由：det 與 sq 都是全函式（任何方陣都算得出來），故生成的義務
/// 不帶 ⊥ 證據缺口（空洞樣本 0 個）—— N-42 指出帶缺口的候選有二十餘條，
/// 拿那些去示範自動生成，示範的就會是一個本身有問題的樣本。
pub fn obl_demo_spec() -> OblSpec {
  {
    ocode: "N-46",
    ofn: "ob_n46",
    oouter: "det",
    oinner: "sq",
    ocomb: "⊗",
    orule: "^",
    ozh: "自動生成之義務：det∘sq 於 ⊗ 下之複合律",
    otrack: "Q",
  }
}

// ---------------------------------------------------------------------------
// ℝ 軌之生成（N-48 之後）
// ---------------------------------------------------------------------------

///|
/// ℝ 軌 Φ 之原始碼
pub fn rphi_src(name : String, arg : String, cost : String) -> String? {
  if name == "inv" {
    Some("Some(cpinv(" + arg + ", 1.0e-12, " + cost + "))")
  } else if name == "chol" {
    Some("ccholesky(" + arg + ", " + cost + ")")
  } else if name == "sqrtm" {
    Some("Some(csqrtm_spd(" + arg + ", " + cost + "))")
  } else if name == "expm" {
    Some("Some(cexpm(" + arg + ", " + cost + "))")
  } else if name == "det" {
    Some("Some(rscalar(cdet_spd(" + arg + ", " + cost + ")))")
  } else {
    // eig 之輸出為譜（n×1），需要解構 cjacobi_eigen 之三元組，
    // 不在本版生成器的表達範圍內。回傳 None 比硬寫一段錯的好。
    None
  }
}

///|
/// ℝ 軌組合子之原始碼
pub fn rcomb_src(
  name : String,
  a : String,
  b : String,
  cost : String,
) -> String? {
  if name == "⊗" {
    Some("rkron_cost(" + cost + ", " + a + ", " + b + ")")
  } else if name == "⊕" {
    Some("rblock_diag(" + a + ", " + b + ")")
  } else if name == "⊞" {
    Some("kron_sum(" + a + ", " + b + ")")
  } else {
    None
  }
}

///|
/// ℝ 軌規則之原始碼
pub fn rrule_src(
  name : String,
  x : String,
  y : String,
  cost : String,
) -> String? {
  if name == "⊗" {
    Some("Some(rkron_cost(" + cost + ", " + x + ", " + y + "))")
  } else if name == "⊕" {
    Some("Some(rblock_diag(" + x + ", " + y + "))")
  } else if name == "·" {
    Some("Some(rscalar(" + x + ".at(0, 0) * " + y + ".at(0, 0)))")
  } else if name == "^" {
    Some(
      "Some(rscalar(powi(" + x + ".at(0, 0), m) * powi(" + y + ".at(0, 0), n)))",
    )
  } else {
    None
  }
}

///|
/// ℝ 軌之對照規則：試出一條確實被推翻者
pub fn pick_control_rule_r(spec : OblSpec) -> String? {
  let rules = if spec.oouter == "det" { ["·", "^"] } else { ["⊗", "⊕"] }
  for r in rules {
    if r == spec.orule {
      continue
    }
    match
      rcomp_check(
        spec.oouter,
        spec.oinner,
        spec.ocomb,
        r,
        rlaw_grid_std(),
        Rng::new(
          comp_seed_base() ^
          str_hash64(comp_key(spec.oouter, spec.oinner, spec.ocomb, r) + "R"),
        ),
      ) {
      Some((h, _g, _d, _dg, ov, pr)) =>
        if !h && ov == 0 && pr == 0 {
          return Some(r)
        }
      None => ()
    }
  }
  None
}

///|
/// ℝ 軌之量測：(成立, 增益, 最大相對偏差, 溢位數, 前提違反數)
pub fn obl_measure_r(spec : OblSpec) -> (Bool, Double, Double, Int, Int)? {
  match
    rcomp_check(
      spec.oouter,
      spec.oinner,
      spec.ocomb,
      spec.orule,
      rlaw_grid_std(),
      Rng::new(
        comp_seed_base() ^
        str_hash64(
          comp_key(spec.oouter, spec.oinner, spec.ocomb, spec.orule) + "R",
        ),
      ),
    ) {
    Some((h, g, d, _dg, ov, pr)) => Some((h, g, d, ov, pr))
    None => None
  }
}

///|
/// 【演算法 207】ℝ 軌義務之生成。
///
/// 與 ℚ 軌版（演算法 203）的差別不只是換幾個函式名，而是多了三件
/// ℝ 軌才有的事，三件都必須寫進生成物：
///   1. 比較用容差而非逐位相等（`rdev` 相對偏差 ≤ 1e-8），且要記下最壞偏差
///   2. 計量用 flop 而非字乘法 —— 兩者**不可並列**
///   3. 要檢查前提（外層 Φ 要求對稱時，Φ₁ 的輸出是否真的對稱）與溢位
pub fn gen_oblig_src_r(spec : OblSpec) -> String? {
  let name = spec.oouter + "∘" + spec.oinner
  let ctrl = pick_control_rule_r(spec)
  let meas = obl_measure_r(spec)
  match (ctrl, meas) {
    (Some(cr), Some((holds, gain, dev, ov, pr))) => {
      if !holds || ov != 0 || pr != 0 {
        return None
      }
      let thr = fmt_d(gain * 0.5, 2)
      let cmb = match rcomb_src(spec.ocomb, "a", "b", "cd") {
        Some(t) => t
        None => return None
      }
      let i1 = match rphi_src(spec.oinner, "g", "cd") {
        Some(t) => t
        None => return None
      }
      let o1 = match rphi_src(spec.oouter, "t0", "cd") {
        Some(t) => t
        None => return None
      }
      let ia = match rphi_src(spec.oinner, "a", "cf") {
        Some(t) => t
        None => return None
      }
      let ib = match rphi_src(spec.oinner, "b", "cf") {
        Some(t) => t
        None => return None
      }
      let oa = match rphi_src(spec.oouter, "ia", "cf") {
        Some(t) => t
        None => return None
      }
      let ob = match rphi_src(spec.oouter, "ib", "cf") {
        Some(t) => t
        None => return None
      }
      let rl = match rrule_src(spec.orule, "xa", "xb", "cf") {
        Some(t) => t
        None => return None
      }
      let rlc = match rrule_src(cr, "xa", "xb", "cc") {
        Some(t) => t
        None => return None
      }
      let isspec = if spec.oouter == "eig" { "true" } else { "false" }
      Some(
        "///|\n" +
        "/// ⚙️ 本函式由 `gen_oblig_src_r`（N-45／N-48）**逐字自動產出**，請勿手改。\n" +
        "/// 重現方式：`moon run cmd/genoblig | diff - oblig_auto.mbt`，應無差異。\n" +
        "///\n" +
        "/// ⚠️ 本條為 **ℝ 軌**：裁決用相對容差（≤ 1e-8）而非逐位相等，\n" +
        "/// 計量用 flop 而非字乘法 —— 其增益**不可**與 ℚ 軌並列。\n" +
        "/// thm 與 proof 兩欄不在此處，它們在 catalogue.mbt 的 " +
        spec.ocode +
        " 列，由人補寫。\n" +
        "pub fn " +
        spec.ofn +
        "() -> Check {\n" +
        "  let mut ok = true\n" +
        "  let mut agree = 0\n" +
        "  let mut ctrl_same = 0\n" +
        "  let mut base = 0L\n" +
        "  let mut fast = 0L\n" +
        "  let mut worst = 0.0\n" +
        "  let sizes = rlaw_grid_std()\n" +
        "  let rng = Rng::new(\n" +
        "    comp_seed_base() ^\n" +
        "    str_hash64(comp_key(" +
        srcq(spec.oouter) +
        ", " +
        srcq(spec.oinner) +
        ", " +
        srcq(spec.ocomb) +
        ", " +
        srcq(spec.orule) +
        ") + \"R\"),\n" +
        "  )\n" +
        "  for sz in sizes {\n" +
        "    let (n, m) = sz\n" +
        "    let a = rand_spd(rng, n)\n" +
        "    let b = rand_spd(rng, m)\n" +
        "    // 直接路徑：先組 " +
        spec.ocomb +
        "，再在 nm 階上施以 " +
        name +
        "\n" +
        "    let cd = Cost::new()\n" +
        "    let g = " +
        cmb +
        "\n" +
        "    let lhs = match " +
        i1 +
        " {\n      Some(t0) => " +
        o1 +
        "\n      None => None\n    }\n" +
        "    // 分解路徑；對照組 cc 把 " +
        spec.orule +
        " 換成 " +
        cr +
        "，必須被推翻\n" +
        "    let cf = Cost::new()\n" +
        "    let cc = Cost::new()\n" +
        "    let mut rhs : RMat? = None\n" +
        "    let mut wrong : RMat? = None\n" +
        "    match (" +
        ia +
        ", " +
        ib +
        ") {\n" +
        "      (Some(ia), Some(ib)) =>\n" +
        "        match (" +
        oa +
        ", " +
        ob +
        ") {\n" +
        "          (Some(xa), Some(xb)) => {\n" +
        "            rhs = " +
        rl +
        "\n" +
        "            wrong = " +
        rlc +
        "\n" +
        "          }\n" +
        "          _ => ()\n" +
        "        }\n" +
        "      _ => ()\n" +
        "    }\n" +
        "    match (lhs, rhs) {\n" +
        "      (Some(u), Some(v)) => {\n" +
        "        // 前提與範圍：不對稱或溢位時，比較沒有意義（N-48 定理 206-2、206-3）\n" +
        "        if !rmat_finite(u) || !rmat_finite(v) {\n" +
        "          ok = false\n" +
        "        }\n" +
        "        let d = rdev(u, v, " +
        isspec +
        ")\n" +
        "        if d > worst {\n          worst = d\n        }\n" +
        "        if d <= 1.0e-8 {\n          agree = agree + 1\n        } else {\n          ok = false\n        }\n" +
        "      }\n" +
        "      _ => ok = false\n" +
        "    }\n" +
        "    match (lhs, wrong) {\n" +
        "      (Some(u), Some(v)) =>\n" +
        "        if rdev(u, v, " +
        isspec +
        ") <= 1.0e-8 {\n          ctrl_same = ctrl_same + 1\n        }\n" +
        "      _ => ()\n" +
        "    }\n" +
        "    base = base + cd.flops\n" +
        "    fast = fast + cf.flops\n" +
        "    ignore(cc)\n" +
        "  }\n" +
        "  if agree != sizes.length() {\n    ok = false\n  }\n" +
        "  if ctrl_same == sizes.length() {\n    ok = false\n  }\n" +
        "  let gain = if fast <= 0L {\n    0.0\n  } else {\n    base.to_double() / fast.to_double()\n  }\n" +
        "  // 門檻 = 生成時實測增益（×" +
        fmt_d(gain, 2) +
        "）之半，留一倍餘裕\n" +
        "  if !(gain > " +
        thr +
        ") {\n    ok = false\n  }\n" +
        "  mk_check(\n" +
        "    " +
        srcq(spec.ocode + " " + spec.ozh) +
        ",\n" +
        "    ok,\n" +
        "    sizes.length() * 2,\n" +
        "    " +
        srcq(
          "律 " +
          name +
          "(A " +
          spec.ocomb +
          " B) = " +
          name +
          "(A) " +
          spec.orule +
          " " +
          name +
          "(B)：ℝ 軌，於尺寸 " +
          rgrid_label() +
          " 之 " +
          rlaw_grid_std().length().to_string() +
          " 組隨機 SPD 樣本上，相對偏差 ≤ 1e-8（生成時最壞 " +
          fmt_e(dev) +
          "）。溢位 0、前提違反 0（外層 " +
          spec.oouter +
          " 的輸入由內層 " +
          spec.oinner +
          " 產出，後者保 SPD）。flop 增益 ×" +
          fmt_d(gain, 2) +
          "，義務門檻 ×" +
          thr +
          "。對照組以 " +
          cr +
          " 取代 " +
          spec.orule +
          " 後被推翻。⚠️ flop 計量，不可與 ℚ 軌之字乘法增益並列。⚙️ 本義務函式由 gen_oblig_src_r 自動產出；thm 與 proof 欄由人補寫。",
        ) +
        ",\n  )\n}",
      )
    }
    _ => None
  }
}

///|
/// ℝ 軌尺寸網格之標籤
pub fn rgrid_label() -> String {
  let parts : Array[String] = []
  for p in rlaw_grid_std() {
    let (n, m) = p
    parts.push("(" + n.to_string() + "," + m.to_string() + ")")
  }
  parts.join("")
}

///|
/// ℝ 軌目錄列之生成（thm／proof 仍只寫佔位符）
pub fn gen_cat_row_r(spec : OblSpec) -> String? {
  let name = spec.oouter + "∘" + spec.oinner
  let cr = match pick_control_rule_r(spec) {
    Some(r) => r
    None => "—"
  }
  match obl_measure_r(spec) {
    Some((holds, gain, dev, ov, pr)) => {
      if !holds || ov != 0 || pr != 0 {
        return None
      }
      Some(
        "  xs.push({\n" +
        "    code: " +
        srcq(spec.ocode) +
        ",\n    zh: " +
        srcq(spec.ozh) +
        ",\n    cat: " +
        srcq("結構律") +
        ",\n    spaces: " +
        srcq(
          "ℝ 軌 SPD 空間，組合子 " +
          spec.ocomb +
          " 下之複合演算法 " +
          name,
        ) +
        ",\n    deff: " +
        srcq(
          "本列由 N-45 之生成器（ℝ 軌版，N-48 後擴充）自 ℝ 軌複合定律表產出。律的來源是推導而非搜尋：" +
          name +
          " 不在 ℝ 軌搜尋引擎的 Φ 集內，它是由內層律（" +
          spec.oinner +
          " 於 " +
          spec.ocomb +
          " 下）與外層律（" +
          spec.oouter +
          "）依複合定理接起來的。ℝ 軌比 ℚ 軌多一道關卡：外層 Φ 的前提必須被內層 Φ 的輸出滿足（N-48 定理 206-2），本律之內層為 " +
          spec.oinner +
          "，保 SPD，故前提成立。以下每個數字都是量出來的：於尺寸 " +
          rgrid_label() +
          " 之 " +
          rlaw_grid_std().length().to_string() +
          " 組隨機 SPD 樣本上最壞相對偏差 " +
          fmt_e(dev) +
          "（門檻 1e-8）；溢位 0 組、前提違反 0 組；flop 增益 ×" +
          fmt_d(gain, 2) +
          "；對照組以 " +
          cr +
          " 取代 " +
          spec.orule +
          " 後被推翻。",
        ) +
        ",\n    formula: " +
        srcq(
          name +
          "(A " +
          spec.ocomb +
          " B) = " +
          name +
          "(A) " +
          spec.orule +
          " " +
          name +
          "(B)",
        ) +
        ",\n    thm: " +
        srcq(obl_placeholder()) +
        ",\n    proof: " +
        srcq(obl_placeholder()) +
        ",\n    track: " +
        srcq("ℝ 軌") +
        ",\n    run: " +
        spec.ofn +
        ",\n  })\n",
      )
    }
    None => None
  }
}

///|
/// 本輪生成的 ℝ 軌那一條：chol∘inv / ⊗ / ⊗（N-49）。
///
/// 選它的理由：它是 ℝ 軌複合表中**有效裁決**裡增益最高的一條（×60.5），
/// 且內層 inv（偽逆）保 SPD，故外層 chol 的對稱前提成立 —— 不像
/// chol 作為內層的那些候選，前提在每個樣本上都被違反。
pub fn obl_demo_spec_r() -> OblSpec {
  {
    ocode: "N-49",
    ofn: "ob_n49",
    oouter: "chol",
    oinner: "inv",
    ocomb: "⊗",
    orule: "⊗",
    ozh: "自動生成之義務（ℝ 軌）：chol∘inv 於 ⊗ 下之複合律",
    otrack: "R",
  }
}

///|
/// 子字串出現次數（只用 builtin；本庫不得有第三方依賴）
pub fn str_count(hay : String, needle : String) -> Int {
  if needle.length() == 0 || hay.length() < needle.length() {
    return 0
  }
  let mut k = 0
  let mut i = 0
  while i + needle.length() <= hay.length() {
    let mut j = 0
    let mut same = true
    while j < needle.length() {
      if hay[i + j] != needle[j] {
        same = false
        break
      }
      j = j + 1
    }
    if same {
      k = k + 1
      i = i + needle.length()
    } else {
      i = i + 1
    }
  }
  k
}

///|
/// 子字串出現判定（義務產生器自建；不引入 @string）。
pub fn str_has(hay : String, needle : String) -> Bool {
  str_count(hay, needle) > 0
}

///|
/// 行數
pub fn str_lines(s : String) -> Int {
  str_count(s, "\n") + 1
}

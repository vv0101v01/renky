///|
/// # N-47 內容檢定 —— 把「通過但什麼都沒說」的裁決消掉
///
/// ## 兩種空殼
///
/// N-42 查出裁決器會放行兩類沒有內容的「成立」：
///
/// 1. **⊥ 空洞**：`qinv_gauss` 在奇異輸入回傳 ⊥、`qadj = det·inv` 跟著回傳 ⊥。
///    裁決器遇到「兩側皆 ⊥」判為相符。於是 N-36 刻意加入的降秩樣本，
///    對 inv 類與 adj 類候選**毫無鑑別力** —— 推導集 60 條中有 24 條如此。
///
/// 2. **恆值律**：`rank∘inv` 在其定義域上恆等於 nm。恆值函數滿足**任何**
///    維數相符的乘法規則，於是 `rank∘inv(A ⊞ B) = rank∘inv(A) · rank∘inv(B)`
///    通過裁決 —— 但它說的只是 nm = n·m，與 A、B 無關。
///
/// 兩者其實是**同一件事的兩面**：⊥ 把 Φ 的變化藏起來，Φ 看起來就成了常數。
///
/// ## 本條的做法：補上缺的那一半定義域，再量一次
///
/// 不是把空殼標記起來就算，而是**把它們改成有內容的**：
///
/// - `qinv_gauss` → `qpinv`：精確 ℚ 的 Moore–Penrose 偽逆，**全函式**。
/// - `qadj` → `qadj_cof`（N-42 已備）：餘因子伴隨矩陣，**全函式**。
///
/// 補完之後 ⊥ 空洞歸零，而恆值律會自己現形 —— `rank∘pinv` 不再是常數
/// （降秩樣本上它等於 r < n），於是那條律**由「成立」翻為「推翻」**。
/// 空殼變成了一句有內容的話：它是錯的。
///
/// ## 要講明的代價
///
/// 偽逆比求逆貴（秩分解 + 兩次 r 階求逆 + 四次矩陣乘法），`qadj_cof` 為
/// Θ(n⁵) 而 `qadj` 為 Θ(n³)。本庫不把原函式換掉 —— 那會改動 N-13／N-36／
/// N-44 已釘死的指紋。全函式層另起一套查表器，兩套裁決並陳。

///|
/// 【演算法 205】精確 ℚ 之 Moore–Penrose 偽逆（全函式）。
///
/// 以秩分解 A = C·F 實作（C 取 A 的主元行、F 取 RREF 的前 r 列）：
/// ```text
///   A⁺ = Fᵀ (F Fᵀ)⁻¹ (Cᵀ C)⁻¹ Cᵀ
/// ```
/// C 為滿行秩、F 為滿列秩，故 CᵀC 與 FFᵀ 皆為正定的 r 階方陣、必可逆。
/// A = 0 時 r = 0，直接回傳零矩陣。
///
/// 與 `qinv_gauss` 的關係：A 可逆時 A⁺ = A⁻¹（此時 r = n、C = A、F = I）。
/// 差別只在**奇異輸入**：`qinv_gauss` 回傳 ⊥，本函式照樣給出答案。
///
/// ⚠️ 成本計量之界線：`mrref` 未經成本插裝（與 `mrank` 同），故本函式的
/// 計量只含四次矩陣乘法與兩次 r 階求逆，**低估**了真實代價。方向上這會
/// 低估直接路徑（它在 nm 階上跑一次），因而**低估增益**，不會灌水。
pub fn qpinv(c : Cost, a : Mat[Q]) -> Mat[Q] {
  let n = a.mrows
  let m = a.mcols
  let rr = mrref(a)
  let r = rr.rank
  if r == 0 {
    return Mat::zeros(m, n)
  }
  let cmat = Mat::build(n, r, (i, j) => a.at(i, rr.pivots[j]))
  let fmat = Mat::build(r, m, (i, j) => rr.rmat.at(i, j))
  let ct = cmat.transpose()
  let ft = fmat.transpose()
  let ctc = qmul_cost(c, ct, cmat)
  let fft = qmul_cost(c, fmat, ft)
  match (qinv_gauss(ctc, c), qinv_gauss(fft, c)) {
    (Some(ic), Some(jf)) =>
      qmul_cost(c, qmul_cost(c, ft, jf), qmul_cost(c, ic, ct))
    _ => Mat::zeros(m, n)
  }
}

///|
/// Penrose 四條件之檢驗（精確 ℚ，故這是**判定**而非估計）。
///
/// 回傳四個布林：A A⁺ A = A、A⁺ A A⁺ = A⁺、(A A⁺)ᵀ = A A⁺、(A⁺ A)ᵀ = A⁺ A。
/// 四者同時成立即唯一確定 A⁺ —— 故這組檢驗不只是「看起來對」，
/// 它配上 Moore–Penrose 唯一性定理就是一個完整的正確性證明。
pub fn qpinv_penrose(a : Mat[Q]) -> (Bool, Bool, Bool, Bool) {
  let c = Cost::new()
  let p = qpinv(c, a)
  let ap = qmul_cost(c, a, p)
  let pa = qmul_cost(c, p, a)
  (
    qmul_cost(c, ap, a).equals(a),
    qmul_cost(c, pa, p).equals(p),
    ap.transpose().equals(ap),
    pa.transpose().equals(pa),
  )
}

///|
/// 全函式版之 Φ 查表器：inv → 偽逆、adj → 餘因子伴隨，其餘不變。
///
/// 與 N-42 的 `phi_by_name_total`（只換 adj）刻意分開：那一個已被 N-42 的
/// 義務用來釘死「恰兩條翻轉」的結論，換掉它會改動已交付的量測。
pub fn phi_by_name_full(name : String) -> ((Mat[Q], Cost) -> Mat[Q]?)? {
  if name == "inv" {
    return Some((a, c) => Some(qpinv(c, a)))
  }
  if name == "adj" {
    return Some((a, c) => Some(qadj_cof(c, a)))
  }
  phi_by_name(name)
}

// ---------------------------------------------------------------------------
// 內容檢定
// ---------------------------------------------------------------------------

///|
/// 內容檢定之結果
pub struct Content {
  /// 於所測維數上，Φ 取到幾個相異值
  cdistinct : Int
  /// 有幾個樣本算不出來（⊥）
  cbot : Int
}

///|
/// Φ 是否為恆值（於固定維數上，對三種分布取樣皆得同一值）。
///
/// 關鍵在「⊥ 不算一個值」：`rank∘inv` 在降秩樣本上是 ⊥，剩下的全是 n，
/// 看起來就是常數。補上偽逆之後它在降秩樣本上給出 r < n，常數性當場破功。
/// 這就是為什麼**補定義域**與**檢內容**必須一起做。
pub fn phi_content(
  lookup : (String) -> ((Mat[Q], Cost) -> Mat[Q]?)?,
  outer : String,
  inner : String,
  dims : Array[Int],
  rng : Rng,
) -> Content {
  let samplers : Array[(Rng, Int) -> Mat[Q]] = [
    samp_gram, samp_indef, samp_singular,
  ]
  let vals : Array[Mat[Q]] = []
  let mut bot = 0
  let f1 = lookup(inner)
  let f2 = lookup(outer)
  match (f1, f2) {
    (Some(g1), Some(g2)) =>
      for d in dims {
        for s in samplers {
          let c = Cost::new()
          let a = s(rng, d)
          let v = if inner == outer && inner == "" {
            None
          } else {
            match g1(a, c) {
              Some(t) => g2(t, c)
              None => None
            }
          }
          match v {
            Some(x) => {
              let mut dup = false
              for y in vals {
                if y.mrows == x.mrows && y.mcols == x.mcols && y.equals(x) {
                  dup = true
                }
              }
              if !dup {
                vals.push(x)
              }
            }
            None => bot = bot + 1
          }
        }
      }
    _ => ()
  }
  { cdistinct: vals.length(), cbot: bot, }
}

///|
/// 一條複合律之內容判定：Φ₂∘Φ₁ 於**每一個**所測維數上都只取一個值 ⇒ 恆值律。
///
/// 為何要逐維數看：Φ 可以「隨維數變、但同維數內不變」—— 那正是恆值律的
/// 典型樣貌（rank∘inv = nm 隨 n、m 變）。若把不同維數的值混在一起數，
/// 恆值律會被誤判為有內容。
pub fn comp_is_constant(
  lookup : (String) -> ((Mat[Q], Cost) -> Mat[Q]?)?,
  outer : String,
  inner : String,
  rng : Rng,
) -> Bool {
  for d in [2, 3] {
    let ct = phi_content(lookup, outer, inner, [d], rng)
    if ct.cdistinct > 1 {
      return false
    }
  }
  true
}

///|
/// 一條複合律在「全函式 + 內容」雙重檢定下的最終裁決
pub struct Verdict47 {
  vname : String
  /// 原裁決（現行 Φ，含 ⊥）
  vold : Bool
  /// 全函式 Φ 下之裁決
  vnew : Bool
  /// 原裁決之空洞樣本數
  vbot : Int
  /// 全函式裁決之空洞樣本數 —— 本條的核心斷言是它恆為 0
  vbotn : Int
  /// 全函式下是否仍為恆值律
  vconst : Bool
}

///|
/// 【演算法】全函式重裁 + 內容檢定。
///
/// 對 N-42 的 360 個複合候選逐一重跑，回報四件事：原裁決、全函式裁決、
/// 原裁決的空洞樣本數、以及全函式下是否仍為恆值。
pub fn content_scan(tbl : Array[LawCand]) -> Array[Verdict47] {
  content_scan_sel(tbl, false)
}

///|
/// N-42 之全量普查指認出的四條「未導出但成立」者。
///
/// 常規義務只重裁「推導集 ∪ 這四條」= 64 個候選；360 條全量重裁由
/// cmd/lawsearch 承接（比照 N-35、N-42 之分層）。取樣種子由候選名決定，
/// 故子集與全量對同一條律必然給出相同結果。
pub fn content_suspects() -> Array[(String, String, String, String)] {
  [
    ("rank", "inv", "⊞", "·"),
    ("rank", "adj", "⊗", "·"),
    ("rank", "adj", "⊕", "+"),
    ("rank", "adj", "⊞", "·"),
  ]
}

///|
fn in_suspects(o : String, i : String, c : String, r : String) -> Bool {
  for s in content_suspects() {
    let (a, b, d, e) = s
    if a == o && b == i && d == c && e == r {
      return true
    }
  }
  false
}

///|
/// 內容律（Λᵏ 與 det 之相容性）掃描；subset 控制是否用小子集。
pub fn content_scan_sel(
  tbl : Array[LawCand],
  subset : Bool,
) -> Array[Verdict47] {
  let samples = law_samples_mixed()
  let out : Array[Verdict47] = []
  let inners = phi_mat_registry()
  let outers_m = phi_mat_registry()
  let outers_s = phi_sca_registry()
  let rules_m = rule_mat_registry()
  let rules_s = rule_sca_registry()
  let combs = comb_registry()
  let ds = compose_derive(tbl)
  for inp in inners {
    let (iname, _if) = inp
    let groups : Array[
      (
        Array[(String, (Mat[Q], Cost) -> Mat[Q]?)],
        Array[(String, (Mat[Q], Mat[Q], Mat[Q], Mat[Q], Cost) -> Mat[Q]?)],
      ),
    ] = [(outers_m, rules_m), (outers_s, rules_s)]
    for grp in groups {
      let (os, rs) = grp
      for op in os {
        let (oname, _of) = op
        for cp in combs {
          let (cname, _cf) = cp
          for rp in rs {
            let (rname, _rf) = rp
            if subset &&
              comp_derived(ds, oname, iname, cname, rname) is None &&
              !in_suspects(oname, iname, cname, rname) {
              continue
            }
            let k = comp_key(oname, iname, cname, rname)
            let old = comp_check(
              oname,
              iname,
              cname,
              rname,
              samples,
              comp_rng_of(oname, iname, cname, rname),
            )
            let neu = comp_check_with(
              phi_by_name_full,
              oname,
              iname,
              cname,
              rname,
              samples,
              comp_rng_of(oname, iname, cname, rname),
            )
            match (old, neu) {
              (Some((vo, bo)), Some((vn, bn))) =>
                out.push({
                  vname: k,
                  vold: vo.holds,
                  vnew: vn.holds,
                  vbot: bo,
                  vbotn: bn,
                  vconst: if vn.holds {
                    comp_is_constant(
                      phi_by_name_full,
                      oname,
                      iname,
                      comp_rng_of(oname, iname, cname, rname),
                    )
                  } else {
                    false
                  },
                })
              _ => ()
            }
          }
        }
      }
    }
  }
  out
}

///|
/// 統計：(原成立, 全函式成立, 原成立但帶 ⊥ 空洞, 全函式下仍為恆值, 翻轉數)
pub fn content_stats(xs : Array[Verdict47]) -> (Int, Int, Int, Int, Int) {
  let mut o = 0
  let mut n = 0
  let mut bot = 0
  let mut cst = 0
  let mut flip = 0
  for x in xs {
    if x.vold {
      o = o + 1
      if x.vbot > 0 {
        bot = bot + 1
      }
    }
    if x.vnew {
      n = n + 1
      if x.vconst {
        cst = cst + 1
      }
    }
    if x.vold != x.vnew {
      flip = flip + 1
    }
  }
  (o, n, bot, cst, flip)
}

///|
/// 全函式重裁後**仍帶空洞樣本**之候選數 —— 本條核心斷言：恆為 0。
pub fn content_residual_bot(xs : Array[Verdict47]) -> Int {
  let mut k = 0
  for x in xs {
    if x.vbotn > 0 {
      k = k + 1
    }
  }
  k
}

// ---------------------------------------------------------------------------
// 共用快取
// ---------------------------------------------------------------------------

///|
let cont_cache : Array[Array[Verdict47]] = []

///|
let cont_miss : Array[Int] = [0]

///|
/// 內容律掃描之漏檢數（良態下應為 0，義務 H-25 檢此計數器）。
pub fn cont_miss_count() -> Int {
  cont_miss[0]
}

///|
/// 內容律標準掃描（固定亂數流，可重現）。
pub fn content_scan_std(rng : Rng) -> Array[Verdict47] {
  if cont_cache.length() == 0 {
    cont_miss[0] = cont_miss[0] + 1
    cont_cache.push(content_scan_sel(law_search_fixed(rng), true))
  }
  cont_cache[0]
}

///|
/// 可讀輸出（供 cmd/lawsearch）
pub fn content_table(xs : Array[Verdict47]) -> String {
  let lines : Array[String] = []
  lines.push("複合律\t原裁決\t空洞\t全函式裁決\t恆值？")
  for x in xs {
    if !x.vold && !x.vnew {
      continue
    }
    lines.push(
      x.vname +
      "\t" +
      (if x.vold { "成立" } else { "推翻" }) +
      "\t" +
      x.vbot.to_string() +
      "\t" +
      (if x.vnew { "成立" } else { "**推翻**" }) +
      "\t" +
      (if x.vconst { "恆值" } else { "有內容" }),
    )
  }
  lines.join("\n")
}

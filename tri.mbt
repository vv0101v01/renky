///|
/// # N-61 任意三表笛卡兒積普查引擎
///
/// ## 從「寫死的三軸」到「任何三張表」
///
/// N-52 的普查是寫死的：D 群 × 空間 × 構造子。那三個迴圈巢在
/// `dcensus_core` 裡，換一組軸就要重寫一次引擎。本條把軸抽出來：
/// 普查的輸入變成**任意三張表**，表的內容可以是空間、構造子、判準式，
/// 也可以是目錄裡的一條義務。
///
/// ## 定義（格的求值）
///
/// 一個格是三元組 (x, y, z)，各取自表 A、B、C。求值分兩步：
///
/// ```text
///   物件化：由 E³ 出發，三元組裡的 TiSpace 換掉基底空間，
///           TiComb 依序套用構造子 —— 得到一個 SpaceExpr
///   裁決  ：三元組裡最後一個判者（TiAlgo 或 TiOblig）決定格值；
///           若三元組裡沒有判者，用預設判者 D-15
/// ```
///
/// 這是一個**全函數**：任何三張表都能相乘，不需要為每組軸寫特例。
///
/// ## 定義（退化軸）
///
/// 若固定另外兩軸、沿某軸掃過去格值全部相同，稱該軸對該格**退化**。
/// 退化不是錯誤 —— 把目錄的字母群當成一張表時，它的條目本來就與空間無關。
/// 但退化必須被**量出來並列出**，否則「我做了一個 23×45×14 的普查」
/// 可能實際上只是把同一個答案抄了 14,490 遍。`tri_axis_sensitivity`
/// 逐軸量這件事。
///
/// ## 推廣之正當性：必須重現特例
///
/// 一個推廣如果不能精確退回它所推廣的東西，就只是另一個東西。
/// 本引擎以 (空間₀, 構造子₀, D 群) 三表相乘、step = 1、不設維數上限時，
/// 必須逐格重現 N-52 的指紋 `5635:5635:386251483` —— 連雜湊的乘累積順序
/// 都要一樣。這條檢查寫在義務裡。

///|
/// 可參與互乘的表項。
pub enum TriItem {
  /// 一個註冊空間
  TiSpace(SpaceRec)
  /// 一個構造子
  TiComb(CombRec)
  /// 一條 D 群判準式
  TiAlgo(DAlgo)
  /// 目錄中的一條義務（與空間無關之判者）
  TiOblig(String, () -> Check)
}

///|
/// 表項之標籤（用於組成格鍵）。
pub fn tri_label(it : TriItem) -> String {
  match it {
    TiSpace(r) => r.sname
    TiComb(c) => c.csym
    TiAlgo(a) => a.dcode
    TiOblig(code, _) => code
  }
}

///|
/// 一張表。
pub struct TriTable {
  ttname : String
  ttitems : Array[TriItem]
}

///|
/// 空間表（45）、空間表₀（35，迴歸錨）、構造子表（14）、構造子表₀（7）、
/// D 群表（23）、字母群表（A–N 各一條代表）。
pub fn tri_tables() -> Array[TriTable] {
  let sp : Array[TriItem] = []
  for r in space_registry_x() {
    sp.push(TiSpace(r))
  }
  let sp0 : Array[TriItem] = []
  for r in space_registry() {
    sp0.push(TiSpace(r))
  }
  let cb : Array[TriItem] = []
  for c in comb14_registry() {
    cb.push(TiComb(c))
  }
  let cb0 : Array[TriItem] = []
  for c in comb7_registry() {
    cb0.push(TiComb(c))
  }
  let al : Array[TriItem] = []
  for a in d_registry() {
    al.push(TiAlgo(a))
  }
  [
    { ttname: "空間⊥", ttitems: tri_broken_items(), },
    { ttname: "空間", ttitems: sp, },
    { ttname: "空間₀", ttitems: sp0, },
    { ttname: "構造子", ttitems: cb, },
    { ttname: "構造子₀", ttitems: cb0, },
    { ttname: "D群", ttitems: al, },
    { ttname: "字母群", ttitems: tri_letter_items(), },
  ]
}

///|
/// 擾動空間表：3 個各破壞一條內積公理的 Gram ＋ 3 個正常空間。
///
/// 為什麼需要這張表：在一個正確的函式庫上，普查格的值**恆為真**，
/// 於是逐軸敏感度量出來必定是 0/0 —— 不是因為軸退化，是因為沒有訊號。
/// 要量「哪一軸真的有作用」，必須讓格值有機會不同。這張表把 N-52 的
/// 三個壞 Gram 放進空間軸，格值才會分裂，敏感度才量得出東西。
pub fn tri_broken_items() -> Array[TriItem] {
  let xs : Array[TriItem] = []
  let names : ReadOnlyArray[String] = ["不定型", "非對稱型", "退化型"]
  for k in 0..<3 {
    let g = gram_of_space(dc_broken(k))
    xs.push(TiSpace({ sname: names[k], fam: "擾動", sdim: g.mrows, sg: g, }))
  }
  for r in space_registry() {
    if r.sname == "E³" || r.sname == "Sym₂" || r.sname == "ℍ¹" {
      xs.push(TiSpace(r))
    }
  }
  xs
}

///|
/// 字母群表：目錄 A–N 各取一條代表義務。
pub fn tri_letter_items() -> Array[TriItem] {
  [
    TiOblig("A-02", ob_a02),
    TiOblig("B-01", ob_b01),
    TiOblig("C-01", ob_c01),
    TiOblig("D-15", ob_d15),
    TiOblig("E-01", ob_e01),
    TiOblig("F-01", ob_f01),
    TiOblig("G-01", ob_g01),
    TiOblig("I-01", ob_i01),
    TiOblig("J-01", ob_j01),
  ]
}

///|
/// 依名稱取表。
pub fn tri_by_name(nm : String) -> TriTable? {
  for t in tri_tables() {
    if t.ttname == nm {
      return Some(t)
    }
  }
  None
}

///|
/// 普查結果。
pub struct TriCensus {
  tcells : Int
  tpass : Int
  tdmax : Int
  /// 逐軸實際覆蓋之項目數
  tcov : (Int, Int, Int)
  tmisses : Array[String]
  tdigest : String
}

///|
/// 把一個三元組物件化成 SpaceExpr，並取出判者。
fn tri_build(
  xs : Array[TriItem],
) -> (SpaceExpr, String, (IPSpace[Array[Q], Q], Rng) -> Bool) {
  let mut base : SpaceExpr = SLeaf("E³", Mat::ident(3))
  for it in xs {
    match it {
      TiSpace(r) => base = r.leaf()
      _ => ()
    }
  }
  for it in xs {
    match it {
      TiComb(c) => base = (c.capply)(base)
      _ => ()
    }
  }
  let mut code = "D-15"
  let mut judge : (IPSpace[Array[Q], Q], Rng) -> Bool = (sp, rg) => {
    dc_default_judge(sp, rg)
  }
  for it in xs {
    match it {
      TiAlgo(a) => {
        code = a.dcode
        judge = a.drun
      }
      TiOblig(c2, f) => {
        code = c2
        judge = (_sp, _rg) => f().ok
      }
      _ => ()
    }
  }
  (base, code, judge)
}

///|
/// 預設判者：D-15（平行四邊形恆等式，O(n²)，最便宜的那一條）。
pub fn dc_default_judge(sp : IPSpace[Array[Q], Q], rg : Rng) -> Bool {
  for a in d_registry() {
    if a.dcode == "D-15" {
      return (a.drun)(sp, rg)
    }
  }
  true
}

///|
/// 任意三表之笛卡兒積普查。
///
/// 迭代順序為 外 = A、中 = B、內 = C；格鍵為 `判者@構造子符號[空間名]`，
/// 與 N-52 之 `dcell_key` 完全一致（這是重現特例的前提）。
pub fn tri_product(
  ta : TriTable,
  tb : TriTable,
  tc : TriTable,
  step : Int,
  maxdim : Int,
) -> TriCensus {
  let na = ta.ttitems.length()
  let nb = tb.ttitems.length()
  let nc = tc.ttitems.length()
  let cova : Array[Bool] = Array::make(na, false)
  let covb : Array[Bool] = Array::make(nb, false)
  let covc : Array[Bool] = Array::make(nc, false)
  let misses : Array[String] = []
  let mut cells = 0
  let mut pass = 0
  let mut dmax = 0
  let mut h : UInt64 = 0xcbf2_9ce4_8422_2325UL
  for ia in 0..<na {
    for ib in 0..<nb {
      // 先建一次空間（內層迴圈共用），並檢查維數上限
      let (expr, _, _) = tri_build([ta.ttitems[ia], tb.ttitems[ib]])
      let d = expr.sdim()
      if maxdim > 0 && d > maxdim {
        continue
      }
      let mut any = false
      for ic in 0..<nc {
        if (ia + 2 * ib + 3 * ic) % step == 0 {
          any = true
        }
      }
      if !any {
        continue
      }
      if d > dmax {
        dmax = d
      }
      let sp = expr.sspace()
      let csym = tri_comb_label([ta.ttitems[ia], tb.ttitems[ib]])
      let snm = tri_space_label([ta.ttitems[ia], tb.ttitems[ib]])
      for ic in 0..<nc {
        if (ia + 2 * ib + 3 * ic) % step != 0 {
          continue
        }
        let (_, code, judge) = tri_build([
          ta.ttitems[ia],
          tb.ttitems[ib],
          tc.ttitems[ic],
        ])
        let key = dcell_key(code, csym, snm)
        let ok = judge(sp, dcell_rng(key))
        cells = cells + 1
        cova[ia] = true
        covb[ib] = true
        covc[ic] = true
        if ok {
          pass = pass + 1
        } else {
          misses.push(key)
        }
        h = (h ^ str_hash64(key + (if ok { "+" } else { "-" }))) *
          0x1000_0000_01b3UL
      }
    }
  }
  fn count(bs : Array[Bool]) -> Int {
    let mut k = 0
    for b in bs {
      if b {
        k = k + 1
      }
    }
    k
  }

  {
    tcells: cells,
    tpass: pass,
    tdmax: dmax,
    tcov: (count(cova), count(covb), count(covc)),
    tmisses: misses,
    tdigest: cells.to_string() +
    ":" +
    pass.to_string() +
    ":" +
    (h % 1000000007UL).to_string(),
  }
}

///|
/// 三元組中構造子之符號（無則為 "·"）。
fn tri_comb_label(xs : Array[TriItem]) -> String {
  let mut s = ""
  for it in xs {
    match it {
      TiComb(c) => s = s + c.csym
      _ => ()
    }
  }
  if s == "" {
    "·"
  } else {
    s
  }
}

///|
/// 三元組中空間之名稱（無則為 "E³"）。
fn tri_space_label(xs : Array[TriItem]) -> String {
  let mut s = "E³"
  for it in xs {
    match it {
      TiSpace(r) => s = r.sname
      _ => ()
    }
  }
  s
}

///|
/// 逐軸敏感度：固定另兩軸、沿該軸掃，數有幾個切片的格值不全相同。
/// 回傳 ((A 軸變動切片數, A 軸切片總數), (B…), (C…))。
/// 某軸的變動切片數為 0 即表示該軸在這組表下**退化**。
pub fn tri_axis_sensitivity(
  ta : TriTable,
  tb : TriTable,
  tc : TriTable,
  maxdim : Int,
  limit : Int,
) -> ((Int, Int), (Int, Int), (Int, Int)) {
  let na = if ta.ttitems.length() < limit { ta.ttitems.length() } else { limit }
  let nb = if tb.ttitems.length() < limit { tb.ttitems.length() } else { limit }
  let nc = if tc.ttitems.length() < limit { tc.ttitems.length() } else { limit }
  fn evalc(ia : Int, ib : Int, ic : Int) -> Bool? {
    let (expr, code, judge) = tri_build([
      ta.ttitems[ia],
      tb.ttitems[ib],
      tc.ttitems[ic],
    ])
    let d = expr.sdim()
    if maxdim > 0 && d > maxdim {
      return None
    }
    let csym = tri_comb_label([ta.ttitems[ia], tb.ttitems[ib]])
    let snm = tri_space_label([ta.ttitems[ia], tb.ttitems[ib]])
    let key = dcell_key(code, csym, snm)
    Some(judge(expr.sspace(), dcell_rng(key)))
  }

  fn sweep(axis : Int) -> (Int, Int) {
    let mut vary = 0
    let mut tot = 0
    let o1 = if axis == 0 { nb } else { na }
    let o2 = if axis == 2 { nb } else { nc }
    for u in 0..<o1 {
      for v in 0..<o2 {
        let vals : Array[Bool] = []
        let len = if axis == 0 { na } else if axis == 1 { nb } else { nc }
        for w in 0..<len {
          let ia = if axis == 0 { w } else { u }
          let ib = if axis == 1 { w } else if axis == 0 { u } else { v }
          let ic = if axis == 2 { w } else { v }
          match evalc(ia, ib, ic) {
            Some(b) => vals.push(b)
            None => ()
          }
        }
        if vals.length() >= 2 {
          tot = tot + 1
          let mut diff = false
          for b in vals {
            if b != vals[0] {
              diff = true
            }
          }
          if diff {
            vary = vary + 1
          }
        }
      }
    }
    (vary, tot)
  }

  (sweep(0), sweep(1), sweep(2))
}

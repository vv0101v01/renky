///|
/// # N-42 律之複合代數 —— 關於律本身的律
///
/// ## 現況的侷限
///
/// 定律表的每一列都是孤立的：`Φ(C(A,B)) = Φ(A) ⊙ Φ(B)`。
/// 但實際演算法幾乎都是複合的 —— `inv(adj(·))`、`det(sq(·))`、`trace(inv(·))`。
/// 搜尋引擎對這些一無所知，因為它的 Φ 集是一張**固定的八元清單**。
/// 要讓它認得 `det∘inv`，唯一的辦法是把 `det∘inv` 當成第九個 Φ 塞進清單
/// 再重跑一次全搜尋 —— 而複合的數量是 Φ 集的平方，這條路走不遠。
///
/// ## 本條的做法：不搜尋，用推導
///
/// 定理 201-1（複合律）：
/// ```text
///   若 Φ₁(C(A,B)) = Φ₁(A) ⊙₁ Φ₁(B)            （內層律）
///   且 Φ₂(X ⊙₁ Y) = Φ₂(X) ⊙₂ Φ₂(Y)            （外層律，組合子恰為 ⊙₁）
///   則 (Φ₂∘Φ₁)(C(A,B)) = (Φ₂∘Φ₁)(A) ⊙₂ (Φ₂∘Φ₁)(B)
/// ```
/// 證明：
/// ```text
///   (Φ₂∘Φ₁)(C(A,B)) = Φ₂(Φ₁(C(A,B)))
///                   = Φ₂(Φ₁(A) ⊙₁ Φ₁(B))        （內層律）
///                   = Φ₂(Φ₁(A)) ⊙₂ Φ₂(Φ₁(B))    （外層律，取 X=Φ₁A, Y=Φ₁B）
///                   = (Φ₂∘Φ₁)(A) ⊙₂ (Φ₂∘Φ₁)(B)  ∎
/// ```
///
/// **可複合的判準因此是純語法的**：內層律的**規則** ⊙₁ 必須同時是一個
/// **組合子**。本庫的 ⊙ 集與 C 集恰有兩個共同元素（⊗ 與 ⊕），
/// 於是這條定理可以在定律表上機械地跑完，不做任何矩陣運算。
///
/// ## 這條定理買到什麼
///
/// 定律表 15 條成立之律 ⇒ 推導出一批複合律，而每一條都是**新的演算法**
/// （Φ₂∘Φ₁ 不在原本的八元 Φ 集裡）。代價為零次矩陣運算。
///
/// ## 這條定理買不到什麼（本條目最該被盯住的一段）
///
/// 推導是**充分不必要**的。而且它的前提有一個**證據缺口**：
/// 外層律是在 `samp_gram`／`samp_indef`／`samp_singular` 抽出的矩陣上
/// 被驗證的，但複合時它被套用在 **Φ₁ 的像**上 —— 那是完全不同的分布。
/// 數學上的蘊含沒有問題（定理對**所有** X、Y 成立才叫律）；
/// 有問題的是**我們憑什麼相信外層律是律** —— 那份信心來自取樣，
/// 而取樣沒有覆蓋 Φ₁ 的像。
///
/// 故本檔不只推導，還把**全部** 5×8×3×3 = 360 個複合候選實測一遍，
/// 做成一張 2×2 混淆表。推導集落在「導出且成立」那一格，是**實測結果**，
/// 不是定理的推論。

///|
/// 一條複合律候選。
pub struct CompLaw {
  /// 外層 Φ₂
  xouter : String
  /// 內層 Φ₁
  xinner : String
  /// 組合子 C
  xcomb : String
  /// 外層規則 ⊙₂
  xrule : String
  /// 中間規則 ⊙₁（僅當可推導時非空；它既是內層律之規則、又是外層律之組合子）
  xmid : String
  /// 是否由定理 201-1 導出
  xderived : Bool
  /// 實測裁決
  xholds : Bool
  /// 實測增益（字乘法比）
  xgain : Double
  /// 空洞樣本數：兩側皆 ⊥ 而被判為相符者。>0 表示這條裁決的證據有缺口。
  xvac : Int
}

///|
/// 複合律之可讀名稱
pub fn CompLaw::xname(self : CompLaw) -> String {
  self.xouter +
  "∘" +
  self.xinner +
  "(A " +
  self.xcomb +
  " B) =? …" +
  self.xrule +
  "…"
}

///|
/// 複合演算法之符號名（Φ₂∘Φ₁）
pub fn CompLaw::xphi(self : CompLaw) -> String {
  self.xouter + "∘" + self.xinner
}

// ---------------------------------------------------------------------------
// 註冊表查詢 —— 一律走 nlaw.mbt 的五張註冊表，不另抄一份
// ---------------------------------------------------------------------------

///|
/// 依名稱取 Φ。矩陣值優先，再找純量值。
pub fn phi_by_name(name : String) -> ((Mat[Q], Cost) -> Mat[Q]?)? {
  for p in phi_mat_registry() {
    let (n, f) = p
    if n == name {
      return Some(f)
    }
  }
  for p in phi_sca_registry() {
    let (n, f) = p
    if n == name {
      return Some(f)
    }
  }
  None
}

///|
/// Φ 是否為純量值（其輸出為 1×1）
pub fn phi_is_scalar(name : String) -> Bool {
  for p in phi_sca_registry() {
    let (n, _f) = p
    if n == name {
      return true
    }
  }
  false
}

///|
/// 依名稱取組合子 C
pub fn comb_by_name(name : String) -> ((Mat[Q], Mat[Q]) -> Mat[Q])? {
  for p in comb_registry() {
    let (n, f) = p
    if n == name {
      return Some(f)
    }
  }
  None
}

///|
/// 依名稱取規則 ⊙
pub fn rule_by_name(
  name : String,
) -> ((Mat[Q], Mat[Q], Mat[Q], Mat[Q], Cost) -> Mat[Q]?)? {
  for p in rule_mat_registry() {
    let (n, f) = p
    if n == name {
      return Some(f)
    }
  }
  for p in rule_sca_registry() {
    let (n, f) = p
    if n == name {
      return Some(f)
    }
  }
  None
}

///|
/// 一個規則名是否同時是組合子名 —— 定理 201-1 之語法判準
pub fn rule_is_comb(name : String) -> Bool {
  !(comb_by_name(name) is None)
}

// ---------------------------------------------------------------------------
// 每個候選一個固定種子 —— 使分層掃描與全量掃描逐條可比
// ---------------------------------------------------------------------------

///|
/// FNV-1a 64 位元字串雜湊（只用 builtin，無第三方依賴）
pub fn str_hash64(s : String) -> UInt64 {
  let mut h = 14695981039346656037UL
  for i in 0..<s.length() {
    h = (h ^ s[i].to_int().to_uint64()) * 1099511628211UL
  }
  h
}

///|
/// 複合掃描之基底種子（固定常數，使任何一次掃描都可獨立重現）
pub fn comp_seed_base() -> UInt64 {
  0x4C41_5753_434F_4D50UL
}

///|
/// 候選之鍵
pub fn comp_key(
  outer : String,
  inner : String,
  comb : String,
  rule : String,
) -> String {
  outer + "∘" + inner + "/" + comb + "/" + rule
}

///|
/// 候選專屬之亂數器。
///
/// 為何不沿用「整次掃描共用一個 Rng」的舊寫法（`law_search_samples` 即是）：
/// 共用 Rng 會讓每個候選拿到的矩陣**取決於它在枚舉中的位置**。於是
/// （一）只掃推導集的 60 條與掃全部 360 條時，同一條律拿到的樣本不同，
/// 兩份報告的增益對不起來；（二）用不同的 adj 實作重新裁決時，樣本也會
/// 跟著變，翻轉就無法歸因於 adj 本身。改為「候選名雜湊 ⊕ 固定基底」之後，
/// 同一條候選在任何掃描、任何子集、任何 Φ 實作下都拿到**同一組矩陣**。
pub fn comp_rng_of(
  outer : String,
  inner : String,
  comb : String,
  rule : String,
) -> Rng {
  Rng::new(comp_seed_base() ^ str_hash64(comp_key(outer, inner, comb, rule)))
}

// ---------------------------------------------------------------------------
// 推導：零次矩陣運算
// ---------------------------------------------------------------------------

///|
/// 【演算法】由定律表推導複合律。
///
/// 掃描所有成立列對 (內層, 外層)，當內層之規則恰為外層之組合子時輸出一條
/// 複合律。全程只比對字串，**不做任何矩陣運算**。
///
/// 回傳 (外層, 內層, 組合子, 中間規則, 外層規則)。
pub fn compose_derive(
  tbl : Array[LawCand],
) -> Array[(String, String, String, String, String)] {
  let out : Array[(String, String, String, String, String)] = []
  for r1 in tbl {
    if !r1.cholds {
      continue
    }
    // 判準：內層律之規則必須同時是組合子，否則第二步接不上
    if !rule_is_comb(r1.crule) {
      continue
    }
    for r2 in tbl {
      if !r2.cholds {
        continue
      }
      if r2.ccomb != r1.crule {
        continue
      }
      out.push((r2.cphi, r1.cphi, r1.ccomb, r1.crule, r2.crule))
    }
  }
  out
}

///|
/// 推導集中是否含某條複合律
pub fn comp_derived(
  ds : Array[(String, String, String, String, String)],
  outer : String,
  inner : String,
  comb : String,
  rule : String,
) -> String? {
  for d in ds {
    let (o, i, c, mid, r) = d
    if o == outer && i == inner && c == comb && r == rule {
      return Some(mid)
    }
  }
  None
}

// ---------------------------------------------------------------------------
// 實測：把推導當成待檢驗的假說，而不是結論
// ---------------------------------------------------------------------------

///|
/// 【演算法】複合律之裁決器。
///
/// 直接路徑：Φ₂(Φ₁(C(A,B)))        —— 在 nm 階矩陣上跑兩次演算法
/// 分解路徑：Φ₂(Φ₁(A)) ⊙₂ Φ₂(Φ₁(B)) —— 在 n、m 階上各跑兩次，再組裝
///
/// 要點（易錯處）：⊙₂ 之第三、四引數必須是**外層律的運算元**，
/// 也就是 Φ₁(A) 與 Φ₁(B)，而不是 A 與 B。帶維數或行列式修正的規則
/// （⊗ₛ、^）會讀這兩個引數；傳錯就會驗出一張假的定律表。
pub fn comp_check(
  outer : String,
  inner : String,
  comb : String,
  rule : String,
  samples : Array[(Int, Int, (Rng, Int) -> Mat[Q])],
  rng : Rng,
) -> (LawVerdict, Int)? {
  comp_check_with(phi_by_name, outer, inner, comb, rule, samples, rng)
}

///|
/// 同上，但 Φ 之查表器可替換 —— 用於以**恆有定義的**餘因子 adj
/// 重新裁決那些被 ⊥ 遮蔽的候選（定理 201-5）。
pub fn comp_check_with(
  lookup : (String) -> ((Mat[Q], Cost) -> Mat[Q]?)?,
  outer : String,
  inner : String,
  comb : String,
  rule : String,
  samples : Array[(Int, Int, (Rng, Int) -> Mat[Q])],
  rng : Rng,
) -> (LawVerdict, Int)? {
  let p1 = lookup(inner)
  let p2 = lookup(outer)
  let cb = comb_by_name(comb)
  let rl = rule_by_name(rule)
  match (p1, p2, cb, rl) {
    (Some(f1), Some(f2), Some(cf), Some(rf)) => {
      let direct = (g : Mat[Q], c : Cost) => {
        match f1(g, c) {
          Some(x) => f2(x, c)
          None => None
        }
      }
      let fact = (a : Mat[Q], b : Mat[Q], c : Cost) => {
        match (f1(a, c), f1(b, c)) {
          (Some(xa), Some(xb)) =>
            match (f2(xa, c), f2(xb, c)) {
              // ⊙₂ 之運算元是 Φ₁(A)、Φ₁(B)
              (Some(ya), Some(yb)) => rf(ya, yb, xa, xb, c)
              _ => None
            }
          _ => None
        }
      }
      Some(
        check_law_samples_vac(
          outer + "∘" + inner + " / " + comb + " / " + rule,
          cf,
          direct,
          fact,
          samples,
          rng,
        ),
      )
    }
    _ => None
  }
}

///|
/// 【演算法】複合空間之全量掃描。
///
/// 內層只取矩陣值 Φ（5 個）—— 純量值 Φ 的輸出是 1×1，外層在 1×1 上
/// 無論什麼規則幾乎都成立，那是退化證據不是律。所幸這件事不必特別排除：
/// 純量值 Φ 的規則是 ·、+、^，三者都不是組合子，定理 201-1 的語法判準
/// **自動**擋掉了它們。此處仍只掃矩陣值內層，是為了讓混淆表的分母乾淨。
///
/// 外層取全部 8 個 Φ，規則依外層之值域分派（矩陣值配 ⊗/⊕/⊗ₛ，
/// 純量值配 ·/+/^）。候選數 = 5 × 8 × 3 × 3 = 360。
pub fn compose_scan(
  tbl : Array[LawCand],
  samples : Array[(Int, Int, (Rng, Int) -> Mat[Q])],
) -> Array[CompLaw] {
  compose_scan_sel(tbl, samples, false)
}

///|
/// 只實測**推導集**之掃描（60 條而非 360 條）。
///
/// 分層的理由與 N-35 相同：健全性（導出者是否都成立）是每回合都該驗的，
/// 而「有多少律落在推導視野之外」是一次性的普查，放在 cmd/lawsearch。
/// 兩者共用同一份掃描碼，只差在候選是否過濾 —— 不另寫一條路徑。
pub fn compose_scan_derived(
  tbl : Array[LawCand],
  samples : Array[(Int, Int, (Rng, Int) -> Mat[Q])],
) -> Array[CompLaw] {
  compose_scan_sel(tbl, samples, true)
}

///|
/// 複合律掃描（選定樣本子集）：吃 (內圈, 外圈) 規則對，吐複合律與其檢定結果。
pub fn compose_scan_sel(
  tbl : Array[LawCand],
  samples : Array[(Int, Int, (Rng, Int) -> Mat[Q])],
  derived_only : Bool,
) -> Array[CompLaw] {
  let ds = compose_derive(tbl)
  let out : Array[CompLaw] = []
  let inners = phi_mat_registry()
  let outers_m = phi_mat_registry()
  let outers_s = phi_sca_registry()
  let rules_m = rule_mat_registry()
  let rules_s = rule_sca_registry()
  let combs = comb_registry()
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
            let pre = comp_derived(ds, oname, iname, cname, rname)
            if derived_only && pre is None {
              continue
            }
            let crng = comp_rng_of(oname, iname, cname, rname)
            match comp_check(oname, iname, cname, rname, samples, crng) {
              Some((v, vac)) => {
                let mid = comp_derived(ds, oname, iname, cname, rname)
                out.push({
                  xouter: oname,
                  xinner: iname,
                  xcomb: cname,
                  xrule: rname,
                  xmid: match mid {
                    Some(m) => m
                    None => ""
                  },
                  xderived: !(mid is None),
                  xholds: v.holds,
                  xgain: v.lgain(),
                  xvac: vac,
                })
              }
              None => ()
            }
          }
        }
      }
    }
  }
  out
}

///|
/// 混淆表：(導出且成立, 導出但推翻, 未導出但成立, 未導出且推翻)。
///
/// 第二格是**可證偽的核心**：定理 201-1 若為真，它必須是 0。
/// 第三格是定理的**不必要性**之度量：有多少律在定理的視野之外。
pub fn compose_confusion(xs : Array[CompLaw]) -> (Int, Int, Int, Int) {
  let mut dh = 0
  let mut dn = 0
  let mut uh = 0
  let mut un = 0
  for x in xs {
    if x.xderived && x.xholds {
      dh = dh + 1
    } else if x.xderived && !x.xholds {
      dn = dn + 1
    } else if !x.xderived && x.xholds {
      uh = uh + 1
    } else {
      un = un + 1
    }
  }
  (dh, dn, uh, un)
}

///|
/// 相異複合演算法之個數（Φ₂∘Φ₁ 之不同符號數，於成立之複合律中計）
pub fn compose_phi_count(xs : Array[CompLaw], derived_only : Bool) -> Int {
  let seen : Array[String] = []
  for x in xs {
    if derived_only && !x.xderived {
      continue
    }
    if !x.xholds {
      continue
    }
    let k = x.xphi()
    let mut dup = false
    for s in seen {
      if s == k {
        dup = true
      }
    }
    if !dup {
      seen.push(k)
    }
  }
  seen.length()
}

///|
/// 增益最高之 k 條（成立者），依增益遞減
pub fn compose_top(xs : Array[CompLaw], k : Int) -> Array[CompLaw] {
  let ok : Array[CompLaw] = []
  for x in xs {
    if x.xholds {
      ok.push(x)
    }
  }
  // 選擇排序（條目數小，不值得引入更複雜者）
  let out : Array[CompLaw] = []
  let used : Array[Bool] = Array::make(ok.length(), false)
  let mut t = 0
  while t < k && t < ok.length() {
    let mut best = -1
    for i in 0..<ok.length() {
      if !used[i] && (best < 0 || ok[i].xgain > ok[best].xgain) {
        best = i
      }
    }
    if best < 0 {
      break
    }
    used[best] = true
    out.push(ok[best])
    t = t + 1
  }
  out
}

///|
/// 複合表之指紋（沿用 N-44 之格式與權重）
pub fn compose_digest(xs : Array[CompLaw]) -> String {
  let mut holds = 0
  let mut acc = 0L
  for i in 0..<xs.length() {
    if xs[i].xholds {
      holds = holds + 1
      acc = (acc * 131L + (i + 1).to_int64()) % 1000000007L
    }
  }
  xs.length().to_string() + ":" + holds.to_string() + ":" + acc.to_string()
}

// ---------------------------------------------------------------------------
// 共用快取（比照 N-35 之規矩：全庫只掃一次）
// ---------------------------------------------------------------------------

///|
let comp_cache : Array[Array[CompLaw]] = []

///|
let comp_miss : Array[Int] = [0]

///|
/// 掃描未命中次數 —— 應恆為 1
pub fn comp_miss_count() -> Int {
  comp_miss[0]
}

///|
/// 標準複合掃描：以修復後之定律表（N-36）為前提、以同一組混合樣本實測。
pub fn compose_scan_std(rng : Rng) -> Array[CompLaw] {
  if comp_cache.length() == 0 {
    comp_miss[0] = comp_miss[0] + 1
    comp_cache.push(
      compose_scan_derived(law_search_fixed(rng), law_samples_mixed()),
    )
  }
  comp_cache[0]
}

///|
/// 複合表之可讀輸出（供 cmd/lawsearch 寫入 docs/定律表.md）
pub fn compose_table(xs : Array[CompLaw]) -> String {
  let lines : Array[String] = []
  lines.push("Φ₂∘Φ₁\tC\t⊙₂\t⊙₁(中間)\t導出\t實測\t增益")
  for x in xs {
    if !x.xholds && !x.xderived {
      continue
    }
    lines.push(
      x.xphi() +
      "\t" +
      x.xcomb +
      "\t" +
      x.xrule +
      "\t" +
      (if x.xmid == "" { "—" } else { x.xmid }) +
      "\t" +
      (if x.xderived { "是" } else { "否" }) +
      "\t" +
      (if x.xholds { "成立" } else { "推翻" }) +
      "\t×" +
      fmt_d(x.xgain, 2),
    )
  }
  lines.join("\n")
}

// ---------------------------------------------------------------------------
// ⊥ 盲區：恆有定義的餘因子伴隨矩陣
// ---------------------------------------------------------------------------

///|
/// 刪去第 r 列、第 cc 行之子矩陣
pub fn qminor(a : Mat[Q], r : Int, cc : Int) -> Mat[Q] {
  let n = a.mrows
  let m = a.mcols
  Mat::build(n - 1, m - 1, (i, j) => {
    a.at(if i < r { i } else { i + 1 }, if j < cc { j } else { j + 1 })
  })
}

///|
/// 【演算法】餘因子伴隨矩陣 adj(M)_{ij} = (−1)^{i+j} det(M 刪去第 j 列第 i 行)。
///
/// 與庫中既有的 `qadj`（= det·inv）**數學上等價於可逆情形**，但關鍵差別是
/// 它在**奇異**輸入上仍有定義 —— 而 `qadj` 回傳 ⊥。
///
/// 為何不直接把 `qadj` 換掉：`qadj` 是 N-13 以降整個定律表的輸入，
/// 換掉它會改動 N-13／N-36／N-44 的既有裁決與已釘死的指紋。本庫的規矩是
/// **量測後報告，不是悄悄修掉**。故此處新增一個總函式版本，只用於
/// 重新裁決那些被 ⊥ 遮蔽的候選，並把翻轉結果寫進條目。
///
/// 成本：n² 個 (n−1) 階行列式，為 Θ(n⁵)；`qadj` 只要一次求逆 Θ(n³)。
/// 這就是當初選 det·inv 的理由，也是這個盲區的來源 —— 它是一個
/// **效能決策造成的正確性缺口**。
pub fn qadj_cof(c : Cost, a : Mat[Q]) -> Mat[Q] {
  let n = a.mrows
  if n <= 1 {
    return Mat::build(1, 1, (_i, _j) => Q::one())
  }
  Mat::build(n, n, (i, j) => {
    let d = qdet_gauss(qminor(a, j, i), c)
    if (i + j) % 2 == 0 {
      d
    } else {
      cq_sub(c, Q::zero(), d)
    }
  })
}

///|
/// Φ 查表器之總函式版本：adj 改用餘因子法，其餘不變。
pub fn phi_by_name_total(name : String) -> ((Mat[Q], Cost) -> Mat[Q]?)? {
  if name == "adj" {
    return Some((a, c) => Some(qadj_cof(c, a)))
  }
  phi_by_name(name)
}

///|
/// 帶 ⊥ 證據缺口之候選數（成立且至少有一個空洞樣本者）
pub fn compose_vacuous_count(xs : Array[CompLaw]) -> Int {
  let mut k = 0
  for x in xs {
    if x.xholds && x.xvac > 0 {
      k = k + 1
    }
  }
  k
}

///|
/// 於掃描結果中查一條複合律
pub fn comp_find(
  xs : Array[CompLaw],
  outer : String,
  inner : String,
  comb : String,
  rule : String,
) -> CompLaw? {
  for x in xs {
    if x.xouter == outer &&
      x.xinner == inner &&
      x.xcomb == comb &&
      x.xrule == rule {
      return Some(x)
    }
  }
  None
}

///|
/// 基礎定律表中「成立、但至少有一個空洞樣本」之律數（N-42 對 N-13／N-36 之回頭檢查）。
///
/// 這是對既有結論的一次回頭稽核：定律表上寫著「成立」的律，有幾條其實
/// 是在某個樣本上兩側都算不出來、而被記成相符的？
pub fn law_vacuity_count(
  tbl : Array[LawCand],
  samples : Array[(Int, Int, (Rng, Int) -> Mat[Q])],
) -> Int {
  let mut k = 0
  for t in tbl {
    if !t.cholds {
      continue
    }
    match (phi_by_name(t.cphi), comb_by_name(t.ccomb), rule_by_name(t.crule)) {
      (Some(f), Some(cf), Some(rf)) => {
        let (_v, vac) = check_law_samples_vac(
          t.cphi,
          cf,
          f,
          (a, b, c) => {
            match (f(a, c), f(b, c)) {
              (Some(x), Some(y)) => rf(x, y, a, b, c)
              _ => None
            }
          },
          samples,
          comp_rng_of(t.cphi, t.cphi, t.ccomb, t.crule),
        )
        if vac > 0 {
          k = k + 1
        }
      }
      _ => ()
    }
  }
  k
}

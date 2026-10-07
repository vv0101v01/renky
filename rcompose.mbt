///|
/// # N-48 ℝ 軌進入複合器
///
/// ## 為什麼不能把 N-42 照抄過來
///
/// ℚ 軌的複合定理有一個**沒有被說出口的前提**：那裡每個 Φ 都是
/// `ℚ^{n×n} → ℚ^{n×n}`，定義域與值域同型，所以 Φ₂ 一定吃得下 Φ₁ 的輸出。
/// ℝ 軌不是這樣 —— 這裡的 Φ 幾乎都**只在 SPD 上有定義**：
///
/// ```text
///   ccholesky   需要 SPD      輸出下三角（不對稱！）
///   csqrtm_spd  需要 SPD      輸出 SPD
///   cjacobi_eigen 需要對稱    輸出譜
///   cdet_spd    需要 SPD（經 Cholesky）
///   cexpm       任意對稱      輸出 SPD
///   cpinv       任意          輸出同型
/// ```
///
/// 於是純語法的判準（「內層律的規則同時是組合子」）**不再充分**。
/// 必須補上一條**定義域條件**：
///
/// ```text
///   定理 206-1（ℝ 軌複合定理）
///   若 Φ₁(C(A,B)) = Φ₁A ⊙₁ Φ₁B 於 SPD 上成立，
///      ⊙₁ 同時是一個組合子，
///      且 Φ₁(SPD) ⊆ dom(Φ₂)，            ← ℚ 軌不需要這一條
///   則 (Φ₂∘Φ₁)(C(A,B)) = (Φ₂∘Φ₁)A ⊙₂ (Φ₂∘Φ₁)B。
/// ```
///
/// `chol` 是唯一不保 SPD 的 Φ（輸出下三角、不對稱），故它不得作為內層。
///
/// ## ℝ 軌的 ⊥ 不是 ⊥，是 0.0 —— 更危險
///
/// N-47 在 ℚ 軌處理的是「兩側皆 ⊥ 被判相符」。ℝ 軌沒有 ⊥：
/// `cdet_spd` 內部呼叫 `ccholesky`，失敗時回傳 **0.0**。於是
/// `det∘chol` 兩側同時為 0，而 `0 = 0^m · 0^n` 照樣成立 ——
/// 一個**合法數值**偽裝成答案，比 ⊥ 更難察覺，因為裁決器沒有任何理由起疑。
///
/// 故本檔除了定義域條件，另帶一個**退化輸出檢定**：兩側皆為零則記為退化，
/// 退化樣本不計入鑑別力。

///|
/// 依名稱取 ℝ 軌 Φ
pub fn rphi_by_name(name : String) -> RPhi? {
  for g in [rphi_mat_registry(), rphi_spec_registry(), rphi_sca_registry()] {
    for p in g {
      if p.rpname == name {
        return Some(p)
      }
    }
  }
  None
}

///|
/// 依名稱取 ℝ 軌 ⊙
pub fn rrule_by_name(name : String) -> RRule? {
  for g in [rrule_mat_registry(), rrule_spec_registry(), rrule_sca_registry()] {
    for r in g {
      if r.rrname == name {
        return Some(r)
      }
    }
  }
  None
}

///|
/// 依名稱取 ℝ 軌組合子
pub fn rcomb_by_name(name : String) -> ((RMat, RMat, Cost) -> RMat)? {
  for c in rcomb_registry() {
    let (n, f) = c
    if n == name {
      return Some(f)
    }
  }
  None
}

///|
/// ⊙ 是否同時是組合子（複合定理之語法判準）
pub fn rrule_is_comb(name : String) -> Bool {
  !(rcomb_by_name(name) is None)
}

///|
/// 【定義域條件】Φ 是否把 SPD 映到 SPD。
///
/// 這張表是**人寫的**，而且必須是人寫的 —— 它陳述的是各演算法的
/// 數學定義域，不是量出來的性質。但它的**後果**全部可以量：義務會驗證
/// 「被這張表擋下來的推導，確實有一部分是錯的」。
///
/// - `inv`（此處為 Moore–Penrose 偽逆）：SPD 之偽逆即逆，仍 SPD ✓
/// - `sqrtm`：SPD 之主平方根仍 SPD ✓
/// - `expm`：對稱矩陣之指數為 SPD ✓
/// - `chol`：輸出下三角，**不對稱** ✗
pub fn rphi_preserves_spd(name : String) -> Bool {
  name == "inv" || name == "sqrtm" || name == "expm"
}

///|
/// 【前提條件】Φ 是否要求輸入**對稱**。
///
/// `ccholesky`、`csqrtm_spd`（內部走 Jacobi）、`cjacobi_eigen`、`cdet_spd`
/// （內部走 Cholesky）都假設對稱；`cpinv` 與 `cexpm` 不假設。
///
/// 這張表同樣是人寫的（它陳述各演算法的前提），但本檔**不信任它就算了**
/// —— 裁決器會在每個樣本上實際量 Φ₁ 的輸出是否對稱，把前提被違反的裁決
/// 標為「不可信」。理由見定理 206-3：前提被違反時兩條路徑往往算出
/// **同一個錯的東西**，於是律「成立」—— 那是 ℝ 軌版的空洞。
pub fn rphi_needs_sym(name : String) -> Bool {
  name == "chol" || name == "sqrtm" || name == "eig" || name == "det"
}

///|
/// 矩陣是否（近似）對稱
pub fn rmat_is_sym(x : RMat, tol : Double) -> Bool {
  if x.mrows != x.mcols {
    return false
  }
  for i in 0..<x.mrows {
    for j in 0..<i {
      let d = absd(x.at(i, j) - x.at(j, i))
      let s = maxd(1.0, maxd(absd(x.at(i, j)), absd(x.at(j, i))))
      if d / s > tol {
        return false
      }
    }
  }
  true
}

///|
/// 一條 ℝ 軌複合律
pub struct RCompLaw {
  youter : String
  yinner : String
  ycomb : String
  yrule : String
  /// 中間規則（可推導時非空）
  ymid : String
  /// 純語法判準是否導出
  ysyn : Bool
  /// 加上定義域條件後是否導出
  ydom : Bool
  /// 實測裁決
  yholds : Bool
  /// flop 增益
  ygain : Double
  /// 最大相對偏差
  ydev : Double
  /// 退化樣本數（兩側皆為零）
  ydegen : Int
  /// 溢位樣本數（中間量超出 double 之表示範圍）—— 此時裁決無意義
  yovf : Int
  /// 前提違反樣本數（外層 Φ 要求對稱，而 Φ₁ 的輸出不對稱）
  ypre : Int
}

///|
pub fn RCompLaw::yname(self : RCompLaw) -> String {
  self.youter + "∘" + self.yinner + "/" + self.ycomb + "/" + self.yrule
}

///|
/// 矩陣之元素是否全為有限值。
///
/// ℝ 軌複合的第一個障礙不是數學，是**表示範圍**：expm∘expm 會把特徵值
/// 推到 e^(e^λ)，λ ≈ 25 就溢位。溢位之後兩條路徑都在算 ∞，比較毫無意義 ——
/// 必須當成「未裁決」而不是「成立」或「推翻」。
pub fn rmat_finite(x : RMat) -> Bool {
  for i in 0..<x.mrows {
    for j in 0..<x.mcols {
      let v = x.at(i, j)
      if v != v || absd(v) > 1.0e300 {
        return false
      }
    }
  }
  true
}

///|
/// 矩陣是否（近似）為零 —— ℝ 軌退化輸出之判準
pub fn rmat_is_zero(x : RMat, tol : Double) -> Bool {
  for i in 0..<x.mrows {
    for j in 0..<x.mcols {
      if absd(x.at(i, j)) > tol {
        return false
      }
    }
  }
  true
}

///|
/// 【演算法】ℝ 軌複合律之推導。
///
/// `domain` 為真時套用定義域條件（內層必須保 SPD）；為假時只用純語法判準。
/// 兩者都算出來，才量得出定義域條件擋掉了什麼。
pub fn rcompose_derive(
  tbl : Array[LawCand],
  domain : Bool,
) -> Array[(String, String, String, String, String)] {
  let out : Array[(String, String, String, String, String)] = []
  for r1 in tbl {
    if !r1.cholds || !rrule_is_comb(r1.crule) {
      continue
    }
    if domain && !rphi_preserves_spd(r1.cphi) {
      continue
    }
    for r2 in tbl {
      if !r2.cholds || r2.ccomb != r1.crule {
        continue
      }
      out.push((r2.cphi, r1.cphi, r1.ccomb, r1.crule, r2.crule))
    }
  }
  out
}

///|
fn rcomp_derived(
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

///|
/// 【演算法】ℝ 軌複合律之裁決器。
///
/// 直接路徑 Φ₂(Φ₁(C(A,B)))；分解路徑 Φ₂(Φ₁A) ⊙₂ Φ₂(Φ₁B)。
/// 以 flop 計量（N-30 之 TR 軌），以相對偏差 `rdev` 裁決（N-33 之選擇），
/// 譜之比較先排序。另計退化樣本：兩側皆為零者不具鑑別力。
pub fn rcomp_check(
  outer : String,
  inner : String,
  comb : String,
  rule : String,
  sizes : Array[(Int, Int)],
  rng : Rng,
) -> (Bool, Double, Double, Int, Int, Int)? {
  match
    (
      rphi_by_name(inner),
      rphi_by_name(outer),
      rcomb_by_name(comb),
      rrule_by_name(rule),
    ) {
    (Some(p1), Some(p2), Some(cf), Some(rl)) => {
      let mut holds = true
      let mut tb = 0L
      let mut tf = 0L
      let mut worst = 0.0
      let mut degen = 0
      let mut ovf = 0
      let mut pre = 0
      let needsym = rphi_needs_sym(outer)
      // Φ₁ 之輸出若已溢位，就不要再餵給 Φ₂ —— 那不是在量律，是在量 ∞。
      // 同時量 Φ₁ 的輸出是否滿足 Φ₂ 的前提（對稱性）。
      let step = (x : RMat, c : Cost) => {
        match (p1.rpfn)(x, c) {
          Some(t) =>
            if rmat_finite(t) {
              if needsym && !rmat_is_sym(t, 1.0e-9) {
                pre = pre + 1
              }
              match (p2.rpfn)(t, c) {
                Some(u) => if rmat_finite(u) { Some(u) } else { None }
                None => None
              }
            } else {
              None
            }
          None => None
        }
      }
      for sz in sizes {
        let (n, m) = sz
        let a = rand_spd(rng, n)
        let b = rand_spd(rng, m)
        let cd = Cost::new()
        let whole = cf(a, b, cd)
        let lhs = step(whole, cd)
        let cfo = Cost::new()
        let xa = step(a, cfo)
        let xb = step(b, cfo)
        let rhs = match (xa, xb) {
          (Some(x), Some(y)) => (rl.rrfn)(x, y, n, m, cfo)
          _ => None
        }
        match (lhs, rhs) {
          (Some(u), Some(v)) =>
            if !rmat_finite(u) || !rmat_finite(v) {
              ovf = ovf + 1
            } else {
              let d = rdev(u, v, p2.rpspec)
              if d > worst {
                worst = d
              }
              if d > 1.0e-8 {
                holds = false
              }
              if rmat_is_zero(u, 1.0e-12) && rmat_is_zero(v, 1.0e-12) {
                degen = degen + 1
              }
            }
          _ => ovf = ovf + 1
        }
        tb = tb + cd.flops
        tf = tf + cfo.flops
      }
      Some(
        (
          holds,
          if tf > 0L {
            tb.to_double() / tf.to_double()
          } else {
            0.0
          },
          worst,
          degen,
          ovf,
          pre,
        ),
      )
    }
    _ => None
  }
}

///|
/// 【演算法】ℝ 軌複合空間之全量掃描。
///
/// 內層只取矩陣值 Φ（inv、chol、sqrtm、expm）—— 譜值與純量值 Φ 的輸出
/// 不是方陣，接不上外層；而它們的規則本來就不是組合子，語法判準已擋掉。
/// 候選數 = 4 內層 × 39（= 外層 × C × ⊙ 之全組合）= 156。
pub fn rcompose_scan(
  tbl : Array[LawCand],
  sizes : Array[(Int, Int)],
) -> Array[RCompLaw] {
  rcompose_scan_sel(tbl, sizes, false)
}

///|
/// 只掃語法推導集（44 條而非 156 條）。分層理由同 N-35／N-42／N-47。
pub fn rcompose_scan_sel(
  tbl : Array[LawCand],
  sizes : Array[(Int, Int)],
  derived_only : Bool,
) -> Array[RCompLaw] {
  let dsyn = rcompose_derive(tbl, false)
  let ddom = rcompose_derive(tbl, true)
  let out : Array[RCompLaw] = []
  let groups : Array[(Array[RPhi], Array[RRule])] = [
    (rphi_mat_registry(), rrule_mat_registry()),
    (rphi_spec_registry(), rrule_spec_registry()),
    (rphi_sca_registry(), rrule_sca_registry()),
  ]
  for inp in rphi_mat_registry() {
    for grp in groups {
      let (os, rs) = grp
      for op in os {
        for cp in rcomb_registry() {
          let (cname, _cf) = cp
          for rp in rs {
            if derived_only &&
              rcomp_derived(dsyn, op.rpname, inp.rpname, cname, rp.rrname)
              is None {
              continue
            }
            match
              rcomp_check(
                op.rpname,
                inp.rpname,
                cname,
                rp.rrname,
                sizes,
                Rng::new(
                  comp_seed_base() ^
                  str_hash64(
                    comp_key(op.rpname, inp.rpname, cname, rp.rrname) + "R",
                  ),
                ),
              ) {
              Some((h, g, d, dg, ov, pr)) => {
                let mid = rcomp_derived(
                  dsyn,
                  op.rpname,
                  inp.rpname,
                  cname,
                  rp.rrname,
                )
                out.push({
                  youter: op.rpname,
                  yinner: inp.rpname,
                  ycomb: cname,
                  yrule: rp.rrname,
                  ymid: match mid {
                    Some(x) => x
                    None => ""
                  },
                  ysyn: !(mid is None),
                  ydom: !(rcomp_derived(
                    ddom,
                    op.rpname,
                    inp.rpname,
                    cname,
                    rp.rrname,
                  )
                  is None),
                  yholds: h,
                  ygain: g,
                  ydev: d,
                  ydegen: dg,
                  yovf: ov,
                  ypre: pr,
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
/// 一條裁決是否**有效**：沒有溢位、沒有前提違反。
///
/// 無效的裁決既不算成立也不算推翻 —— 它只是沒有資訊。把它們算進混淆表
/// 會同時污染兩格：溢位的被記成「推翻」，前提違反的被記成「成立」。
pub fn rcomp_valid(x : RCompLaw) -> Bool {
  x.yovf == 0 && x.ypre == 0
}

///|
/// 混淆表（以**純語法**判準為準，只計有效裁決）
pub fn rcompose_confusion_syn(xs : Array[RCompLaw]) -> (Int, Int, Int, Int) {
  let mut a = 0
  let mut b = 0
  let mut c = 0
  let mut d = 0
  for x in xs {
    if !rcomp_valid(x) {
      continue
    }
    if x.ysyn && x.yholds {
      a = a + 1
    } else if x.ysyn && !x.yholds {
      b = b + 1
    } else if !x.ysyn && x.yholds {
      c = c + 1
    } else {
      d = d + 1
    }
  }
  (a, b, c, d)
}

///|
/// 混淆表（加上**定義域條件**後）
pub fn rcompose_confusion_dom(xs : Array[RCompLaw]) -> (Int, Int, Int, Int) {
  let mut a = 0
  let mut b = 0
  let mut c = 0
  let mut d = 0
  for x in xs {
    if !rcomp_valid(x) {
      continue
    }
    if x.ydom && x.yholds {
      a = a + 1
    } else if x.ydom && !x.yholds {
      b = b + 1
    } else if !x.ydom && x.yholds {
      c = c + 1
    } else {
      d = d + 1
    }
  }
  (a, b, c, d)
}

///|
/// 帶退化樣本（兩側皆零）之成立裁決數 —— ℝ 軌版的「沒有內容」
pub fn rcompose_degen_count(xs : Array[RCompLaw]) -> Int {
  let mut k = 0
  for x in xs {
    if x.yholds && x.ydegen > 0 {
      k = k + 1
    }
  }
  k
}

///|
pub fn rcomp_find(xs : Array[RCompLaw], name : String) -> RCompLaw? {
  for x in xs {
    if x.yname() == name {
      return Some(x)
    }
  }
  None
}

///|
/// 增益最高之 k 條（成立、無退化樣本者）
pub fn rcompose_top(xs : Array[RCompLaw], k : Int) -> Array[RCompLaw] {
  let ok : Array[RCompLaw] = []
  for x in xs {
    if x.yholds && x.ydegen == 0 && rcomp_valid(x) {
      ok.push(x)
    }
  }
  let out : Array[RCompLaw] = []
  let used : Array[Bool] = Array::make(ok.length(), false)
  let mut t = 0
  while t < k && t < ok.length() {
    let mut best = -1
    for i in 0..<ok.length() {
      if !used[i] && (best < 0 || ok[i].ygain > ok[best].ygain) {
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

// ---------------------------------------------------------------------------
// 共用快取
// ---------------------------------------------------------------------------

///|
let rcomp_cache : Array[Array[RCompLaw]] = []

///|
let rcomp_miss : Array[Int] = [0]

///|
pub fn rcomp_miss_count() -> Int {
  rcomp_miss[0]
}

///|
pub fn rcompose_scan_std(rng : Rng) -> Array[RCompLaw] {
  if rcomp_cache.length() == 0 {
    rcomp_miss[0] = rcomp_miss[0] + 1
    rcomp_cache.push(
      rcompose_scan_sel(rlaw_search_std(rng), rlaw_grid_std(), true),
    )
  }
  rcomp_cache[0]
}

///|
/// 可讀輸出
pub fn rcompose_table(xs : Array[RCompLaw]) -> String {
  let lines : Array[String] = []
  lines.push(
    "Φ₂∘Φ₁\tC\t⊙₂\t語法導出\t定義域導出\t裁決\t增益\t最大相對偏差\t退化\t溢位\t前提違反",
  )
  for x in xs {
    if !x.yholds && !x.ysyn {
      continue
    }
    lines.push(
      x.youter +
      "∘" +
      x.yinner +
      "\t" +
      x.ycomb +
      "\t" +
      x.yrule +
      "\t" +
      (if x.ysyn { "是" } else { "否" }) +
      "\t" +
      (if x.ydom { "是" } else { "否" }) +
      "\t" +
      (if !rcomp_valid(x) {
        "**無效**"
      } else if x.yholds {
        "成立"
      } else {
        "推翻"
      }) +
      "\t×" +
      fmt_d(x.ygain, 2) +
      "\t" +
      fmt_e(x.ydev) +
      "\t" +
      x.ydegen.to_string() +
      "\t" +
      x.yovf.to_string() +
      "\t" +
      x.ypre.to_string(),
    )
  }
  lines.join("\n")
}

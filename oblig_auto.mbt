///|
/// ⚙️ 本函式由 `gen_oblig_src`（N-45）**逐字自動產出**，請勿手改。
/// 重現方式：`moon run cmd/genoblig | diff - oblig_auto.mbt`，應無差異。
///
/// 機器產出的是骨架與可執行的量測；thm 與 proof 兩欄不在此處，
/// 它們在 catalogue.mbt 的 N-46 列，由人補寫。
pub fn ob_n46() -> Check {
  let mut ok = true
  let mut vac = 0
  let mut agree = 0
  let mut ctrl_same = 0
  let mut base = 0L
  let mut fast = 0L
  let samples = law_samples_mixed()
  let rng = comp_rng_of("det", "sq", "⊗", "^")
  for sm in samples {
    let (n, m, sampler) = sm
    let a = sampler(rng, n)
    let b = sampler(rng, m)
    // 直接路徑：先組 ⊗，再在 nm 階上施以 det∘sq
    let cd = Cost::new()
    let g = mkron(a, b)
    let lhs = match Some(qmul_cost(cd, g, g)) { Some(t0) => Some(q_scalar_mat(qdet_gauss(t0, cd)))
        None => None }
    // 分解路徑：兩側各自施以 det∘sq，再以 ^ 合成
    // 對照組 cc：把 ^ 換成 ·，必須被推翻 —— 否則本義務沒有鑑別力
    let cf = Cost::new()
    let cc = Cost::new()
    let mut rhs : Mat[Q]? = None
    let mut wrong : Mat[Q]? = None
    match (Some(qmul_cost(cf, a, a)), Some(qmul_cost(cf, b, b))) {
      (Some(ia), Some(ib)) =>
        match (Some(q_scalar_mat(qdet_gauss(ia, cf))), Some(q_scalar_mat(qdet_gauss(ib, cf)))) {
          (Some(xa), Some(xb)) => {
            rhs = Some(q_scalar_mat(cq_mul(cf, qpow_cost(cf, xa.data[0], ib.mrows), qpow_cost(cf, xb.data[0], ia.mrows))))
            wrong = Some(q_scalar_mat(cq_mul(cc, xa.data[0], xb.data[0])))
          }
          _ => ()
        }
      _ => ()
    }
    match (lhs, rhs) {
      (Some(u), Some(v)) =>
        if u.equals(v) {
          agree = agree + 1
        } else {
          ok = false
        }
      (None, None) => {
        vac = vac + 1
        agree = agree + 1
      }
      _ => ok = false
    }
    match (lhs, wrong) {
      (Some(u), Some(v)) => if u.equals(v) { ctrl_same = ctrl_same + 1 }
      (None, None) => ctrl_same = ctrl_same + 1
      _ => ()
    }
    base = base + cd.wmul
    fast = fast + cf.wmul
    ignore(cc)
  }
  if agree != samples.length() {
    ok = false
  }
  if ctrl_same == samples.length() {
    ok = false
  }
  let gain = if fast <= 0L {
    0.0
  } else {
    base.to_double() / fast.to_double()
  }
  // 門檻 = 生成時實測增益（×5.68）之半，留一倍餘裕
  if !(gain > 2.84) {
    ok = false
  }
  mk_check(
    "N-46 自動生成之義務：det∘sq 於 ⊗ 下之複合律",
    ok,
    samples.length() * 2,
    "律 det∘sq(A ⊗ B) = det∘sq(A) ^ det∘sq(B)：於尺寸 (2,2)(2,3)(2,3)(2,3)、分布 正定 ×2／不定 ×1／降秩 ×1 之 4 組樣本上逐元相符，空洞樣本 0 個。成本實測：直接路徑 10146 次字乘法、分解路徑 1786 次，增益 ×5.68；義務門檻設為 ×2.84（實測之半）。對照組以 · 取代 ^ 後被推翻，故本義務有鑑別力。⚙️ 本義務函式由 gen_oblig_src 自動產出；thm 與 proof 欄由人補寫。",
  )
}

// ─────────────────────────────────────────────────────────────
// 目錄列模板（請貼入 catalogue.mbt，並把兩個佔位符換成人寫的證明）
//
//   xs.push({
//     code: "N-46",
//     zh: "自動生成之義務：det∘sq 於 ⊗ 下之複合律",
//     cat: "結構律",
//     spaces: "組合子 ⊗ 下之複合演算法 det∘sq",
//     deff: "本列由 N-45 之生成器自 N-42 的複合定律表產出。律的來源是推導而非搜尋：det∘sq 不在搜尋引擎的 Φ 集內，它是由內層律（sq 於 ⊗ 下，其規則同時是一個組合子）與外層律（det）依複合定理（定理 201-1）接起來的，推導階段零次矩陣運算。以下每個數字都是量出來的：於尺寸 (2,2)(2,3)(2,3)(2,3)、分布 正定 ×2／不定 ×1／降秩 ×1 之 4 組樣本上兩條路徑逐元相符；直接路徑 10146 次字乘法、分解路徑 1786 次，增益 ×5.68；空洞樣本（兩側皆 ⊥ 而被判相符者）0 個；對照組以 · 取代 ^ 後被推翻。",
//     formula: "det∘sq(A ⊗ B) = det∘sq(A) ^ det∘sq(B)",
//     thm: "⟨此欄為代數證明，機器不產出；須由人補寫⟩",
//     proof: "⟨此欄為代數證明，機器不產出；須由人補寫⟩",
//     track: "精確 ℚ",
//     run: ob_n46,
//   })
// 

///|
/// ⚙️ 本函式由 `gen_oblig_src_r`（N-45／N-48）**逐字自動產出**，請勿手改。
/// 重現方式：`moon run cmd/genoblig | diff - oblig_auto.mbt`，應無差異。
///
/// ⚠️ 本條為 **ℝ 軌**：裁決用相對容差（≤ 1e-8）而非逐位相等，
/// 計量用 flop 而非字乘法 —— 其增益**不可**與 ℚ 軌並列。
/// thm 與 proof 兩欄不在此處，它們在 catalogue.mbt 的 N-49 列，由人補寫。
pub fn ob_n49() -> Check {
  let mut ok = true
  let mut agree = 0
  let mut ctrl_same = 0
  let mut base = 0L
  let mut fast = 0L
  let mut worst = 0.0
  let sizes = rlaw_grid_std()
  let rng = Rng::new(
    comp_seed_base() ^
    str_hash64(comp_key("chol", "inv", "⊗", "⊗") + "R"),
  )
  for sz in sizes {
    let (n, m) = sz
    let a = rand_spd(rng, n)
    let b = rand_spd(rng, m)
    // 直接路徑：先組 ⊗，再在 nm 階上施以 chol∘inv
    let cd = Cost::new()
    let g = rkron_cost(cd, a, b)
    let lhs = match Some(cpinv(g, 1.0e-12, cd)) {
      Some(t0) => ccholesky(t0, cd)
      None => None
    }
    // 分解路徑；對照組 cc 把 ⊗ 換成 ⊕，必須被推翻
    let cf = Cost::new()
    let cc = Cost::new()
    let mut rhs : RMat? = None
    let mut wrong : RMat? = None
    match (Some(cpinv(a, 1.0e-12, cf)), Some(cpinv(b, 1.0e-12, cf))) {
      (Some(ia), Some(ib)) =>
        match (ccholesky(ia, cf), ccholesky(ib, cf)) {
          (Some(xa), Some(xb)) => {
            rhs = Some(rkron_cost(cf, xa, xb))
            wrong = Some(rblock_diag(xa, xb))
          }
          _ => ()
        }
      _ => ()
    }
    match (lhs, rhs) {
      (Some(u), Some(v)) => {
        // 前提與範圍：不對稱或溢位時，比較沒有意義（N-48 定理 206-2、206-3）
        if !rmat_finite(u) || !rmat_finite(v) {
          ok = false
        }
        let d = rdev(u, v, false)
        if d > worst {
          worst = d
        }
        if d <= 1.0e-8 {
          agree = agree + 1
        } else {
          ok = false
        }
      }
      _ => ok = false
    }
    match (lhs, wrong) {
      (Some(u), Some(v)) =>
        if rdev(u, v, false) <= 1.0e-8 {
          ctrl_same = ctrl_same + 1
        }
      _ => ()
    }
    base = base + cd.flops
    fast = fast + cf.flops
    ignore(cc)
  }
  if agree != sizes.length() {
    ok = false
  }
  if ctrl_same == sizes.length() {
    ok = false
  }
  let gain = if fast <= 0L {
    0.0
  } else {
    base.to_double() / fast.to_double()
  }
  // 門檻 = 生成時實測增益（×60.52）之半，留一倍餘裕
  if !(gain > 30.26) {
    ok = false
  }
  mk_check(
    "N-49 自動生成之義務（ℝ 軌）：chol∘inv 於 ⊗ 下之複合律",
    ok,
    sizes.length() * 2,
    "律 chol∘inv(A ⊗ B) = chol∘inv(A) ⊗ chol∘inv(B)：ℝ 軌，於尺寸 (2,2)(2,3) 之 2 組隨機 SPD 樣本上，相對偏差 ≤ 1e-8（生成時最壞 1.481e-16）。溢位 0、前提違反 0（外層 chol 的輸入由內層 inv 產出，後者保 SPD）。flop 增益 ×60.52，義務門檻 ×30.26。對照組以 ⊕ 取代 ⊗ 後被推翻。⚠️ flop 計量，不可與 ℚ 軌之字乘法增益並列。⚙️ 本義務函式由 gen_oblig_src_r 自動產出；thm 與 proof 欄由人補寫。",
  )
}

// ─────────────────────────────────────────────────────────────
// ℝ 軌目錄列模板（請貼入 catalogue.mbt，並把兩個佔位符換成人寫的證明）
//
//   xs.push({
//     code: "N-49",
//     zh: "自動生成之義務（ℝ 軌）：chol∘inv 於 ⊗ 下之複合律",
//     cat: "結構律",
//     spaces: "ℝ 軌 SPD 空間，組合子 ⊗ 下之複合演算法 chol∘inv",
//     deff: "本列由 N-45 之生成器（ℝ 軌版，N-48 後擴充）自 ℝ 軌複合定律表產出。律的來源是推導而非搜尋：chol∘inv 不在 ℝ 軌搜尋引擎的 Φ 集內，它是由內層律（inv 於 ⊗ 下）與外層律（chol）依複合定理接起來的。ℝ 軌比 ℚ 軌多一道關卡：外層 Φ 的前提必須被內層 Φ 的輸出滿足（N-48 定理 206-2），本律之內層為 inv，保 SPD，故前提成立。以下每個數字都是量出來的：於尺寸 (2,2)(2,3) 之 2 組隨機 SPD 樣本上最壞相對偏差 1.481e-16（門檻 1e-8）；溢位 0 組、前提違反 0 組；flop 增益 ×60.52；對照組以 ⊕ 取代 ⊗ 後被推翻。",
//     formula: "chol∘inv(A ⊗ B) = chol∘inv(A) ⊗ chol∘inv(B)",
//     thm: "⟨此欄為代數證明，機器不產出；須由人補寫⟩",
//     proof: "⟨此欄為代數證明，機器不產出；須由人補寫⟩",
//     track: "ℝ 軌",
//     run: ob_n49,
//   })
// 

// ─────────────────────────────────────────────────────────────
// N-62：普查式義務（DSL 第二種產出）

///|
/// ⚙️ 本函式由 `gen_census_src`（N-62）**逐字自動產出**，請勿手改。
/// 規格：空間 × 構造子 × D群，step 17，維數上限 12。
/// 下列每一個數字都由生成器在產碼前當場量出，不是人寫的。
pub fn ob_n62g() -> Check {
  let mut ok = true
  let ta = tri_by_name("空間")
  let tb = tri_by_name("構造子")
  let tc = tri_by_name("D群")
  match (ta, tb, tc) {
    (Some(a), Some(bb), Some(c)) => {
      let r = tri_product(a, bb, c, 17, 12)
      if r.tdigest != "774:774:352759555" {
        ok = false
      }
      if r.tcells != 774 || r.tpass != 774 {
        ok = false
      }
      if r.tcov.0 != 45 || r.tcov.1 != 14 || r.tcov.2 != 23 {
        ok = false
      }
      if r.tdmax != 12 {
        ok = false
      }
      if r.tmisses.length() != 0 {
        ok = false
      }
      let sv = tri_axis_sensitivity(a, bb, c, 12, 4)
      if sv.0.0 != 0 || sv.0.1 != 16 {
        ok = false
      }
      if sv.1.0 != 0 || sv.1.1 != 16 {
        ok = false
      }
      if sv.2.0 != 0 || sv.2.1 != 16 {
        ok = false
      }
      ignore(ok)
    }
    _ => ok = false
  }
  mk_check(
    "N-62g 擴充軸分層普查（45 × 14 × 23，step 17，維數上限 12）",
    ok,
    774,
    "規格 空間 × 構造子 × D群（step 17，維數上限 12）：774 格，774 格成立、0 格推翻，覆蓋 45/14/23，最高維 12，指紋 774:774:352759555。逐軸敏感度（切片有變動數／切片總數）：A 軸 0/16、B 軸 0/16、C 軸 0/16。以上數字由生成器在產碼前當場量出並逐一釘入斷言。",
  )
}


// ─────────────────────────────────────────────────────────────
// 普查式目錄列模板
//
//   xs.push({
//     code: "N-62g",
//     zh: "擴充軸分層普查（45 × 14 × 23，step 17，維數上限 12）",
//     cat: "中端",
//     spaces: "空間 × 構造子 × D群",
//     deff: "三表笛卡兒積之分層普查；格鍵為 判者@構造子[空間]，種子取自 str_hash64(格鍵)。",
//     formula: "|普查| = |空間| × |構造子| × |D群|，分層條件 (i + 2j + 3k) mod 17 = 0",
//     thm: "實測 774 格，774 格成立，指紋 774:774:352759555。⟨此欄為代數證明，機器不產出；須由人補寫⟩",
//     proof: "⟨此欄為代數證明，機器不產出；須由人補寫⟩",
//     track: "精確 ℚ",
//     run: ob_n62g,
//   })
// 

// ─────────────────────────────────────────────────────────────
// N-74：成本比對式義務（DSL 第三種產出）

///|
/// ⚙️ 本函式由 `gen_compare_src`（N-74）**逐字自動產出**，請勿手改。
/// 掃描器：子空間。下列數字由生成器在產碼前當場量出。
pub fn ob_n74g() -> Check {
  let mut ok = true
  match cmp_by_name("子空間") {
    None => ok = false
    Some(f) => {
      let (n, same, td, ts, win, lose) = f()
      if n != 16 {
        ok = false
      }
      if same != n {
        ok = false
      }
      if same != 16 {
        ok = false
      }
      if td != 211868L || ts != 156576L {
        ok = false
      }
      if win != 14 {
        ok = false
      }
      if lose != 0 {
        ok = false
      }
      if ts >= td {
        ok = false
      }
      ignore(ok)
    }
  }
  mk_check(
    "N-74g 子空間特化路徑之成本比對（生成）",
    ok,
    32,
    "掃描器 子空間：語料 16 式，兩路逐元相同 16/16（這是前提不是結論 —— 不相同的話成本比較沒有意義），通用總成本 211868、特化總成本 156576（×1.353），特化較便宜 14 式、較貴 0 式。以上數字由生成器在產碼前當場量出並逐一釘入斷言；敗例數 0 是如實寫下的，不是一律寫 0。",
  )
}


// ─────────────────────────────────────────────────────────────
// 成本比對式目錄列模板
//
//   xs.push({
//     code: "N-74g",
//     zh: "子空間特化路徑之成本比對（生成）",
//     cat: "中端",
//     spaces: "子空間",
//     deff: "兩條路線對同一語料逐式求解，先驗逐元相同，再比字乘法總成本。",
//     formula: "增益 = 通用總成本 / 特化總成本 = 211868 / 156576",
//     thm: "實測語料 16 式，逐元相同 16，勝 14 敗 0。⟨此欄為代數證明，機器不產出；須由人補寫⟩",
//     proof: "⟨此欄為代數證明，機器不產出；須由人補寫⟩",
//     track: "精確 ℚ",
//     run: ob_n74g,
//   })
// 

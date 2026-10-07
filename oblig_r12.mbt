///|
/// # 第十二輪義務自證：N-78 … N-82
///
/// 全部 45 個註冊空間（9 族，涵蓋題目要求之 12 類）乘上使用者指定的
/// 7 個構造子 —— 同態 Hom(W₂,−)、餘維一外冪、對稱平方、雙對偶、
/// 倍化 V⊕V、半子空間、轉置扭曲 —— 共 315 個相異的有限維內積空間。

// ---------------------------------------------------------------------------

///|
/// 【N-78】七構造子之封閉式 Gram 總表。
///
/// 對每個構造子獨立推導一條封閉式，與 `SpaceExpr::sgram()` 的泛型
/// 遞迴路徑逐元對帳。兩條路徑數學上同值、程式上無共用碼。
///
/// 兩側對照不只報「抓到幾格」，而是**預測盲點**：對每個構造子給出一條
/// 只看 G 的代數性質，宣告「此格分辨不出錯式 ⟺ G 具此性質」，
/// 再逐格與實測對帳。故錯誤會被抓到，而「哪裡抓不到、為什麼」也被釘死。
pub fn ob_n78() -> Check {
  let mut ok = true
  let sps = space_registry_x()
  let cbs = comb7_new()
  let gw = comb_partner().sgram()
  let c = Cost::new()
  let mut cells = 0
  let mut ncf = 0
  let mut nctl = 0
  let mut nblind = 0
  let mut nhs = 0
  let mut nhsc = 0
  let perc : Array[Int] = Array::makei(7, _ => 0)
  for ci, cb in cbs {
    for s in sps {
      let g = s.sg
      let gg = ((cb.capply)(s.leaf()) : SpaceExpr).sgram()
      cells = cells + 1
      // (1) 封閉式逐元等於泛型路徑
      let cf = c7_closed(ci, gw, g, c)
      if cf.mrows == gg.mrows && cf.equals(gg) {
        ncf = ncf + 1
      }
      // (2) 盲點預測 = 實測
      let po = c7_poison(ci, gw, g, c)
      let blind = po.mrows == gg.mrows && po.equals(gg)
      if blind {
        nblind = nblind + 1
        perc[ci] = perc[ci] + 1
      }
      if blind == c7_blind_pred(ci, g, c) {
        nctl = nctl + 1
      }
    }
  }
  if cells != 315 || ncf != 315 || nctl != 315 {
    ok = false
  }
  // (3) 同態之第三路徑：由 ⟨f,g⟩ = tr(f* g) 實際組裝基映射的 Gram。
  //     這證明 Kronecker 式 G_W⁻¹ ⊗ G_V 裡的「對偶」沒有寫反 ——
  //     只比 cf_hom 與 sgram 兩路，兩邊都可能同時寫反而對不出來。
  for s in sps {
    if s.sdim <= 6 {
      nhs = nhs + 1
      if hs_gram_ref(gw, s.sg, c).equals(cf_hom(gw, s.sg, c)) {
        nhsc = nhsc + 1
      }
    }
  }
  if nhs != 38 || nhsc != nhs {
    ok = false
  }
  // (4) 盲點之分佈必須與理論一致：H、S²、Tᵀ 永不盲（錯式與真式恆異）。
  if perc[0] != 0 || perc[2] != 0 || perc[6] != 0 {
    ok = false
  }
  // (5) 而會盲的三個必須真的盲過 —— 否則「預測」只是恆真。
  if perc[3] == 0 || perc[4] == 0 || perc[5] == 0 || perc[1] == 0 {
    ok = false
  }
  mk_check(
    "N-78 七構造子之封閉式 Gram 總表",
    ok,
    cells + nhs,
    "45 空間 × 7 構造子 = " +
    cells.to_string() +
    " 格：封閉式與泛型 sgram 逐元一致 " +
    ncf.to_string() +
    "／" +
    cells.to_string() +
    "。兩側對照改為**盲點預測**：對每個構造子以一條只看 G 的代數性質宣告「此格分辨不出錯式 ⟺ G 具此性質」（H/S²/Tᵀ 永不盲；Λⁿ⁻¹ ⟺ G⁻¹ 為 Hodge 對合之不動點；** ⟺ G = I；D ⟺ G = λI；U½ ⟺ 前後 ⌈n/2⌉ 階主子陣相同），預測與實測逐格相符 " +
    nctl.to_string() +
    "／" +
    cells.to_string() +
    "，其中實測為盲者 " +
    nblind.to_string() +
    " 格（分佈 H" +
    perc[0].to_string() +
    " Λⁿ⁻¹" +
    perc[1].to_string() +
    " S²" +
    perc[2].to_string() +
    " **" +
    perc[3].to_string() +
    " D" +
    perc[4].to_string() +
    " U½" +
    perc[5].to_string() +
    " Tᵀ" +
    perc[6].to_string() +
    "）。同態另走第三路徑：由 ⟨f,g⟩ = tr(f*g) 逐對組裝基映射矩陣、以 f* = G_W⁻¹fᵀG_V 取伴隨，在 " +
    nhs.to_string() +
    " 個 dim ≤ 6 的空間上與 Kronecker 式一致 " +
    nhsc.to_string() +
    " 格，據此排除「兩路同時把對偶寫反」。",
  )
}

// ---------------------------------------------------------------------------

///|
/// 【N-79】餘維一外冪即對偶扭轉：Λ^{n−1}V ≅ V* ⊗ det V。
///
/// ```text
///   C_{n−1}(G)[p][q] = (−1)^{p+q} · det(G) · G⁻¹[n−1−p][n−1−q]
/// ```
///
/// 泛型 `compound` 物化 n² 個 (n−1) 階子式 ⇒ Θ(n⁵)；
/// 封閉式只做一次反矩陣與一次行列式 ⇒ Θ(n³)。
pub fn ob_n79() -> Check {
  let mut ok = true
  let sps = space_registry_x()
  let c = Cost::new()
  let mut n = 0
  let mut same = 0
  let mut sf = 0
  let mut wrongcaught = 0
  let mut wrongable = 0
  let mut cn : Int64 = 0
  let mut cf : Int64 = 0
  for s in sps {
    let d = s.sdim
    if d < 2 {
      continue
    }
    n = n + 1
    let g = s.sg
    // (1) 封閉式 vs 泛型 compound，逐元
    let ca = Cost::new()
    let dense = compound(g, d - 1, ca)
    let cb = Cost::new()
    let fast = cf_codim1(g, cb)
    cn = cn + ca.wmul
    cf = cf + cb.wmul
    if dense.equals(fast) {
      same = same + 1
    }
    // (2) Sylvester–Franke 獨立交叉驗證：det(C_k(G)) = det(G)^{C(n−1,k−1)}
    //     k = n−1 ⇒ 指數 C(n−1, n−2) = n−1
    let lhs = mdet(fast)
    let rhs = qpow_fast(c, mdet(g), sf_exponent(d, d - 1))
    if lhs.eq(rhs) && sf_exponent(d, d - 1) == d - 1 {
      sf = sf + 1
    }
    // (3) 兩側對照：漏掉 Hodge 符號與指標反轉者，在非盲格必須被抓到
    let gi = match qinv_gauss(g, c) {
      Some(h) => h
      None => g
    }
    if !c7_hodge_fixed(gi) {
      wrongable = wrongable + 1
      if !cfw_codim1(g, c).equals(fast) {
        wrongcaught = wrongcaught + 1
      }
    }
  }
  if n != 45 || same != n || sf != n {
    ok = false
  }
  if wrongable != 19 || wrongcaught != wrongable {
    ok = false
  }
  // (4) 增益。註冊表的 45 個 Gram 多為單位陣或對角陣，compound 的
  //     高斯消去遇零樞軸即短路，故在**這批資料上**字乘法只差 ×2 左右 ——
  //     Θ(n⁵) → Θ(n³) 是漸進命題，稀疏輸入看不出來。
  //     故另在稠密正定 G = AᵀA + nI 上量尺度行為，並要求比值隨 n 單調上升。
  let ratio = cn.to_double() / maxd(1.0, cf.to_double())
  let rrng = ob_rng()
  let rats : Array[Double] = []
  for m in [3, 4, 5, 6, 7, 8, 9, 10] {
    let aa = Mat::build(m, m, (_, _) => qr(rrng))
    let gg = aa.transpose().times(aa).plus(Mat::ident(m).scale(Q::of_int(m)))
    let ca2 = Cost::new()
    let _ = compound(gg, m - 1, ca2)
    let cb2 = Cost::new()
    let _ = cf_codim1(gg, cb2)
    rats.push(ca2.wmul.to_double() / maxd(1.0, cb2.wmul.to_double()))
  }
  let mut mono = true
  for i in 1..<rats.length() {
    if rats[i] < rats[i - 1] {
      mono = false
    }
  }
  if !mono || rats[rats.length() - 1] < 5.0 {
    ok = false
  }
  // 小 n 時封閉式反而較慢（要做一次完整反矩陣），這是真的，照實記
  let crossover = rats[0] < 1.0
  // (5) **前提之負面對照。** 封閉式由 adj(G) = det(G)·G⁻¹ 導出，故定義域比
  //     它要取代的 compound 小 —— compound 直接算子式，奇異矩陣照樣有定義。
  //     派工若假設「Gram 都正定所以都可逆」就會在擾動表上算出錯的 Gram。
  //     這不是假想：接線的第一版就是這樣寫的，被 N-61／N-73 的 空間⊥ 抓到。
  let mut nsing = 0
  let mut nsingok = 0
  let mut nasym = 0
  let mut nasymok = 0
  for it in tri_broken_items() {
    match it {
      TiSpace(r) => {
        let bg = r.sg
        let m = bg.mrows
        if m < 2 {
          continue
        }
        let dense = compound(bg, m - 1, c)
        let viaexpr = (SExt(SLeaf(r.sname, bg), m - 1) : SpaceExpr).sgram()
        if Q::is_zero(mdet(bg)) {
          // 奇異：封閉式必須明確拒絕，派工必須退回 compound
          nsing = nsing + 1
          if cf_codim1_opt(bg, c) is None && viaexpr.equals(dense) {
            nsingok = nsingok + 1
          }
        } else if !bg.equals(bg.transpose()) {
          // 不對稱但可逆：封閉式**會被採用**，故它本身必須正確。
          // 指標順序 G⁻¹[n−1−q][n−1−p] 不可依賴對稱性化簡成 [n−1−p][n−1−q]。
          nasym = nasym + 1
          if cf_codim1(bg, c).equals(dense) && viaexpr.equals(dense) {
            nasymok = nasymok + 1
          }
        }
      }
      _ => ()
    }
  }
  if nsing == 0 || nsingok != nsing {
    ok = false
  }
  if nasym == 0 || nasymok != nasym {
    ok = false
  }
  // (6) 接線確認：註冊表指紋未因接線而改變。
  let dg = comb7_digest()
  if dg != "245:1306:695201586" {
    ok = false
  }
  mk_check(
    "N-79 餘維一外冪即對偶扭轉",
    ok,
    n * 3,
    "定理：以字典序排列之 (n−1)-子集中第 p 個恰為「略去指標 n−1−p」，配合餘因子式 adj(G)[j][i] = (−1)^{i+j}det(G[{i}ᶜ,{j}ᶜ]) 與 adj(G) = det(G)·G⁻¹，得 C_{n−1}(G)[p][q] = (−1)^{p+q}det(G)·G⁻¹[n−1−p][n−1−q]，即 Λ^{n−1}V ≅ V*⊗det V。在全部 " +
    n.to_string() +
    " 個空間上與泛型 compound 逐元相等 " +
    same.to_string() +
    " 格；另以 Sylvester–Franke det(C_{n−1}(G)) = det(G)^{n−1} 獨立交叉驗證 " +
    sf.to_string() +
    " 格（指數由 sf_exponent(n,n−1) 算出並核對等於 n−1）。兩側對照（漏掉符號與反轉的 det·G⁻¹）在 " +
    wrongable.to_string() +
    " 個可辨格全數抓到；其餘 " +
    (45 - wrongable).to_string() +
    " 格之 G⁻¹ 為 Hodge 對合之不動點，理論上即不可辨，已由 N-78 逐格預測。成本：註冊表 45 個 Gram 上 compound 字乘法 " +
    cn.to_string() +
    " → 封閉式 " +
    cf.to_string() +
    "（×" +
    fmt_d(ratio, 2) +
    "）—— 只有 ×2，是因為這批 Gram 多為單位陣或對角陣，compound 的高斯消去遇零樞軸即短路；Θ(n⁵) → Θ(n³) 是漸進命題，稀疏輸入本來就看不出來。改在稠密正定 G = AᵀA + mI 上量尺度行為，m = 3…10 之比值為 " +
    fmt_d(rats[0], 2) +
    "／" +
    fmt_d(rats[1], 2) +
    "／" +
    fmt_d(rats[2], 2) +
    "／" +
    fmt_d(rats[3], 2) +
    "／" +
    fmt_d(rats[4], 2) +
    "／" +
    fmt_d(rats[5], 2) +
    "／" +
    fmt_d(rats[6], 2) +
    "／" +
    fmt_d(rats[7], 2) +
    "，單調上升且 m = 10 時 ≥ 5（兩者皆為判準，非敘述）。m = 3 時封閉式反而**較慢**（" +
    (if crossover { "已測得，比值 < 1" } else { "未測得" }) +
    "）—— 它要做一次完整反矩陣，而 3 階的 2×2 子式幾乎不花錢；交叉點在 m = 4。**前提之負面對照**：封閉式由 adj(G) = det(G)·G⁻¹ 導出，定義域比 compound 小（compound 直接算子式，奇異矩陣照樣有定義）；在擾動表 空間⊥ 的 " +
    nsing.to_string() +
    " 個奇異 Gram 上，cf_codim1_opt 必須明確拒絕、而 sgram() 之派工必須退回 compound 且逐元相同，" +
    nsingok.to_string() +
    "／" +
    nsing.to_string() +
    " 成立。**對稱性之負面對照**：由 adj(G)[j][i] 的指標順序，封閉式取的是 G⁻¹[n−1−q][n−1−p]；G 對稱時它與 G⁻¹[n−1−p][n−1−q] 相同，不對稱時不同，故不可依賴對稱性化簡 —— 在擾動表的 " +
    nasym.to_string() +
    " 個不對稱但可逆的 Gram 上逐元核對 " +
    nasymok.to_string() +
    " 格。這兩條前提（可逆、不依賴對稱）都不是事後補的禮貌話：接線的第一版兩條都違反，而 45 個正定對稱的註冊 Gram **全部通過** —— 是 N-61／N-73 的擾動表 空間⊥ 把它們抓出來的。一個只在良性輸入上驗證的封閉式，會把自己的定義域誤認成全域。已接入 sgram() 之 SExt 臂（k = n−1 且 G 可逆時派工），comb7 指紋 " +
    dg +
    " 未變。",
  )
}

// ---------------------------------------------------------------------------

///|
/// 【N-80】雙對偶即恆等函子，與 315 個自然性方塊。
pub fn ob_n80() -> Check {
  let mut ok = true
  let sps = space_registry_x()
  let c = Cost::new()
  // (1) Gram 層面：V** 之 Gram 逐元等於 V 之 Gram（不只同構）
  let mut n = 0
  let mut idn = 0
  let mut single = 0
  let mut singleable = 0
  for s in sps {
    n = n + 1
    let g = s.sg
    let dd = ((comb7_new()[3].capply)(s.leaf()) : SpaceExpr).sgram()
    if dd.equals(g) {
      idn = idn + 1
    }
    // 兩側對照：只作用一次對偶者，在 G ≠ I 的格必須被抓到
    if !c7_is_ident(g) {
      singleable = singleable + 1
      if !cfw_bidual(g, c).equals(g) {
        single = single + 1
      }
    }
  }
  if n != 45 || idn != 45 {
    ok = false
  }
  if singleable != 23 || single != singleable {
    ok = false
  }
  // (2) 自然性方塊 C(V**) = C(V)**，且兩者皆 = C(V)
  let (eq, tot, tri) = c7_naturality()
  if tot != 315 || eq != 315 || tri != 315 {
    ok = false
  }
  mk_check(
    "N-80 雙對偶即恆等函子",
    ok,
    n + tot,
    "G 對稱正定 ⇒ G⁻¹ 對稱 ⇒ ((G⁻¹)ᵀ)⁻¹ᵀ = G，故 ** 在 Gram 層面是**嚴格的**恆等函子而非僅自然同構：全部 " +
    n.to_string() +
    " 個空間逐元相等 " +
    idn.to_string() +
    " 格。兩側對照（只作用一次對偶，得 (G⁻¹)ᵀ）在 " +
    singleable.to_string() +
    " 個 G ≠ I 的格全數抓到；其餘 22 格之 G = I，此時 G⁻¹ = G 故理論上不可辨，已由 N-78 逐格預測。自然性方塊 C(V**) = C(V)** 在 7 構造子 × 45 空間 = " +
    tot.to_string() +
    " 格成立 " +
    eq.to_string() +
    " 格；更強地，C(V**)、C(V)**、C(V) 三者同時逐元相等 " +
    tri.to_string() +
    " 格 —— 若只驗左右兩式相等，兩邊同時錯成同一個東西仍會通過，故第三式不可省。",
  )
}

// ---------------------------------------------------------------------------

///|
/// 【N-81】315 格深度交叉普查。
///
/// 在本輪之前，這 315 格只被檢查維數與正定（`comb14_stats`）——
/// 一個算錯的 Gram 只要維數對、仍然正定，就能完整通過。
/// 本條把每格補成七項。
pub fn ob_n81() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let r = c7_scan(rng)
  if r.r7cells != 315 {
    ok = false
  }
  if r.r7sym != 315 ||
    r.r7dim != 315 ||
    r.r7spd != 315 ||
    r.r7cf != 315 ||
    r.r7ctl != 315 ||
    r.r7cs != 315 ||
    r.r7rz != 315 {
    ok = false
  }
  if r.r7inst != 2205 {
    ok = false
  }
  // 覆蓋必須真的到達大維數格，否則「深度」只是小格的深度
  if r.r7dmax != 78 || r.r7dsum != 2327 {
    ok = false
  }
  // 指紋：格數、維數總和、以及 (構造子, 空間, 維數) 之 FNV 疊合
  if r.r7digest != "315:2327:721925835" {
    ok = false
  }
  // 七族皆須出現（涵蓋題目列出的全部空間類別）
  let fams : Map[String, Int] = Map([])
  for row in r.r7rows {
    fams[row.k7c] = fams.get(row.k7c).unwrap_or(0) + 1
  }
  if fams.length() != 7 {
    ok = false
  }
  for _, v in fams {
    if v != 45 {
      ok = false
    }
  }
  mk_check(
    "N-81 全部空間 × 七構造子之深度交叉普查",
    ok,
    r.r7inst,
    "45 個註冊空間（9 族，涵蓋題目所列全部 12 類：函數空間、對稱矩陣、Hermite、歐氏、列空間、多項式、多元多項式、對角矩陣、對偶、張量、外代數、四元數 ℍⁿ）× 7 個構造子（同態 Hom(W₂,−)、餘維一外冪、對稱平方、雙對偶、倍化 V⊕V、半子空間、轉置扭曲）= " +
    r.r7cells.to_string() +
    " 個相異的有限維內積空間，每格七項檢查共 " +
    r.r7inst.to_string() +
    " 個實例：Gram 對稱 " +
    r.r7sym.to_string() +
    "、維數公式（cdim 與 sdim 雙路）" +
    r.r7dim.to_string() +
    "、正定（Θ(d³) 整數 Sylvester）" +
    r.r7spd.to_string() +
    "、封閉式逐元一致 " +
    r.r7cf.to_string() +
    "、盲點預測相符 " +
    r.r7ctl.to_string() +
    "（其中實測為盲 " +
    r.r7blind.to_string() +
    " 格）、Cauchy–Schwarz（各 2 組隨機 ℚ 向量）" +
    r.r7cs.to_string() +
    "、Riesz 表示（解 Gx = b 後驗 xᵀGy = bᵀy）" +
    r.r7rz.to_string() +
    "，全部 315／315。最大維數 " +
    r.r7dmax.to_string() +
    "（S²[ℍ³]），維數總和 " +
    r.r7dsum.to_string() +
    "；大格不降級 —— 七項皆為 Θ(d²) 或 Θ(d³) 整數運算，無 ℚ 分解。指紋 " +
    r.r7digest +
    "。對照本輪之前：同樣 315 格只驗維數與正定，算錯的 Gram 只要維數對且仍正定即可完整通過。",
  )
}

// ---------------------------------------------------------------------------

///|
/// 【N-82】七構造子之交換圖。
///
/// 三個層級：維數相同 ⊋ 置換等距 ⊋ Gram 逐元相同。
pub fn ob_n82() -> Check {
  let mut ok = true
  let ps = c7_commute(40)
  if ps.length() != 49 {
    ok = false
  }
  let mut neq = 0
  let mut niso = 0
  let mut nne = 0
  let mut nskip = 0
  let mut ndim = 0
  for p in ps {
    neq = neq + p.p7eq
    niso = niso + p.p7iso
    nne = nne + p.p7ne
    nskip = nskip + p.p7skip
    ndim = ndim + p.p7dim
  }
  if ndim != neq + niso + nne + nskip {
    ok = false
  }
  // (1) ** 與任何構造子皆可交換，且是最強的那個層級（Gram 逐元相同）
  let mut starrows = 0
  for p in ps {
    if p.p7a == "**" || p.p7b == "**" {
      starrows = starrows + 1
      if p.p7dim != 45 || p.p7eq + p.p7skip != 45 || p.p7ne != 0 || p.p7iso != 0 {
        ok = false
      }
    }
  }
  if starrows != 13 {
    ok = false
  }
  // (2) H 與 D：維數恆同、Gram 恆異、而辮子置換恆為見證。
  //     這正是「自然同構 ≠ 同一個矩陣」的具體反例。
  let mut hd = 0
  for p in ps {
    if (p.p7a == "H" && p.p7b == "D") || (p.p7a == "D" && p.p7b == "H") {
      hd = hd + 1
      if p.p7dim != 45 || p.p7eq != 0 || p.p7iso != 44 || p.p7ne != 0 {
        ok = false
      }
    }
  }
  if hd != 2 {
    ok = false
  }
  // (3) 三個層級必須真的是嚴格包含 —— 否則這張表沒有內容
  if niso == 0 || nne == 0 {
    ok = false
  }
  if neq != 956 || niso != 88 || nne != 794 || nskip != 59 {
    ok = false
  }
  mk_check(
    "N-82 七構造子之交換圖",
    ok,
    ndim,
    "7 × 7 = 49 個有序構造子對，各在 45 個空間上比較 C₁C₂V 與 C₂C₁V，分三個層級量測：維數相同（" +
    ndim.to_string() +
    " 格）⊋ 置換等距（∃ 具名置換 P 使 PᵀG₁P = G₂）⊋ Gram 逐元相同。結果：逐元相同 " +
    neq.to_string() +
    "、置換等距但不逐元相同 " +
    niso.to_string() +
    "、未見證 " +
    nne.to_string() +
    "、因維數 > 40 而略過 " +
    nskip.to_string() +
    "（略過者誠實記為未驗，不計入通過）。兩個關鍵讀數：其一，** 與全部 7 個構造子在**最強層級**交換（13 個含 ** 的對全部逐元相同），這與 N-80 的恆等函子結論互為獨立佐證；其二，H 與 D 同為「與固定二維空間作張量」，維數恆相同（45／45）而 Gram **恆不同**（0 格逐元相同），由完美洗牌 Shuffle(2,2)⊗Iₙ 見證為等距（44／44 可算格）—— 這是「自然同構」與「同一個矩陣」不可混為一談的具體反例，也是本表分三層而非一層的理由。未見證之 " +
    nne.to_string() +
    " 格只表示本庫尚未給出具名置換，不表示不同構。",
  )
}

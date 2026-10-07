///|
/// # N-78…N-82 之掃描引擎
///
/// 全部 45 個空間 × 7 個構造子 = 315 格，每格七項檢查；
/// 再加 315 個自然性方塊與 7×7×45 = 2205 格交換圖。

// ---------------------------------------------------------------------------
//  盲點判準
//
//  兩側對照若只報「抓到幾格」，它會隨著註冊表成長而悄悄退化：
//  新加進來的空間若恰好讓錯式與真式重合，計數會下降而沒有人知道為什麼。
//  故本庫改為**預測**：對每個構造子給出一條只看 G 的代數性質，
//  宣告「此格分辨不出錯式 ⟺ G 具此性質」，再逐格與實測對帳。
//  這樣一來，不但錯誤會被抓到，連「哪裡抓不到、為什麼」都被釘死。
// ---------------------------------------------------------------------------

///|
/// G 是否為單位陣。
pub fn c7_is_ident(g : Mat[Q]) -> Bool {
  g.equals(Mat::ident(g.mrows))
}

///|
/// G 是否為純量陣 λI。
pub fn c7_is_scalar(g : Mat[Q]) -> Bool {
  g.equals(Mat::ident(g.mrows).scale(g.at(0, 0)))
}

///|
/// X 是否為 Hodge 對合 σ(X)[p][q] = (−1)^{p+q}·X[n−1−p][n−1−q] 之不動點。
///
/// 【命題】錯式 2（det·G⁻¹，漏掉符號與反轉）與真式 C_{n−1}(G) 相等
/// ⟺ G⁻¹ 為 σ 之不動點。由 N78-2 之封閉式兩邊相減即得。
pub fn c7_hodge_fixed(x : Mat[Q]) -> Bool {
  let n = x.mrows
  Mat::build(n, n, (p, q) => {
    let v = x.at(n - 1 - p, n - 1 - q)
    if (p + q) % 2 == 1 {
      v.neg()
    } else {
      v
    }
  }).equals(x)
}

///|
/// G 之前 ⌈n/2⌉ 階主子陣是否等於後 ⌈n/2⌉ 階主子陣。
pub fn c7_half_blind(g : Mat[Q]) -> Bool {
  let n = g.mrows
  let k = (n + 1) / 2
  cf_half(g).equals(Mat::build(k, k, (i, j) => g.at(n - k + i, n - k + j)))
}

///|
/// 第 ci 個構造子在 G 上的盲點預測。
pub fn c7_blind_pred(ci : Int, g : Mat[Q], c : Cost) -> Bool {
  match ci {
    // H：G_W⁻¹ ⊗ G vs G_W ⊗ G，因 G_W ≠ G_W⁻¹ 固定成立，永不盲
    0 => false
    1 => {
      let gi = match qinv_gauss(g, c) {
        Some(h) => h
        None => g
      }
      c7_hodge_fixed(gi)
    }
    // S²：錯式漏掉交叉項，而交叉項含 G 之對角元（正定 ⇒ 為正），永不盲
    2 => false
    3 => c7_is_ident(g)
    4 => c7_is_scalar(g)
    5 => c7_half_blind(g)
    // Tᵀ：MᵀGM vs MGMᵀ，M 為非對稱么單三角，永不盲
    _ => false
  }
}

///|
/// 第 ci 個構造子之封閉式。
pub fn c7_closed(ci : Int, gw : Mat[Q], g : Mat[Q], c : Cost) -> Mat[Q] {
  match ci {
    0 => cf_hom(gw, g, c)
    1 => cf_codim1(g, c)
    2 => spec_sym_sq_gram(g, g)
    3 => cf_bidual(g)
    4 => cf_double(g)
    5 => cf_half(g)
    _ => cf_twist_t(g)
  }
}

///|
/// 第 ci 個構造子之「看起來很合理但錯」的對照式。
pub fn c7_poison(ci : Int, gw : Mat[Q], g : Mat[Q], c : Cost) -> Mat[Q] {
  match ci {
    0 => cfw_hom(gw, g)
    1 => cfw_codim1(g, c)
    2 => wrong_sym_sq_gram(g, g)
    3 => cfw_bidual(g, c)
    4 => cfw_double(g)
    5 => cfw_half(g)
    _ => cfw_twist_t(g)
  }
}

// ---------------------------------------------------------------------------
//  315 格深度普查
// ---------------------------------------------------------------------------

///|
/// 一格之結果。
pub struct C7Cell {
  k7c : String
  k7s : String
  k7d : Int
  /// Gram 對稱
  k7sym : Bool
  /// 維數公式
  k7dim : Bool
  /// 正定
  k7spd : Bool
  /// 封閉式與泛型路徑逐元一致
  k7cf : Bool
  /// 盲點預測 = 實測
  k7ctl : Bool
  /// 實測是否為盲點（統計用，非判準）
  k7blind : Bool
  /// Cauchy–Schwarz（2 組隨機向量）
  k7cs : Bool
  /// Riesz 表示存在且正確
  k7rz : Bool
}

///|
/// 全表結果。
pub struct C7Report {
  r7cells : Int
  r7sym : Int
  r7dim : Int
  r7spd : Int
  r7cf : Int
  r7ctl : Int
  r7blind : Int
  r7cs : Int
  r7rz : Int
  /// 檢查實例總數（= 格數 × 7）
  r7inst : Int
  r7dmax : Int
  r7dsum : Int
  r7digest : String
  r7rows : Array[C7Cell]
}

///|
/// 【N-81】315 格深度交叉普查。
///
/// 每格七項：對稱、維數、正定、封閉式、盲點預測、Cauchy–Schwarz、Riesz。
/// 大維數格不降級 —— 七項全部是 Θ(d²) 或 Θ(d³) 整數，無 ℚ 分解。
pub fn c7_scan(rng : Rng) -> C7Report {
  let sps = space_registry_x()
  let cbs = comb7_new()
  let gw = comb_partner().sgram()
  let c = Cost::new()
  let rows : Array[C7Cell] = []
  let mut nsym = 0
  let mut ndim = 0
  let mut nspd = 0
  let mut ncf = 0
  let mut nctl = 0
  let mut nblind = 0
  let mut ncs = 0
  let mut nrz = 0
  let mut dmax = 0
  let mut dsum = 0
  let mut h = 0UL
  for ci, cb in cbs {
    for s in sps {
      let g = s.sg
      let e = (cb.capply)(s.leaf())
      let gg = e.sgram()
      let d = gg.mrows
      dsum = dsum + d
      if d > dmax {
        dmax = d
      }
      // (1) 對稱
      let a_sym = gg.equals(gg.transpose())
      // (2) 維數公式
      let a_dim = (cb.cdim)(s.sdim) == d && e.sdim() == d
      // (3) 正定（Θ(d³) 整數 Sylvester）
      // 【第十八輪】接 L 層分派
      let a_spd = spd_fast(gg)
      // (4) 封閉式逐元一致
      let cf = c7_closed(ci, gw, g, c)
      let a_cf = cf.mrows == d && cf.equals(gg)
      // (5) 盲點預測 = 實測
      let po = c7_poison(ci, gw, g, c)
      let blind = po.mrows == d && po.equals(gg)
      let a_ctl = blind == c7_blind_pred(ci, g, c)
      // (6) Cauchy–Schwarz：⟨x,y⟩² ≤ ⟨x,x⟩⟨y,y⟩
      let mut a_cs = true
      for _t in 0..<2 {
        let x : Array[Q] = Array::makei(d, _ => qr(rng))
        let y : Array[Q] = Array::makei(d, _ => qr(rng))
        let xy = qbil(gg, x, y)
        if xy.mul(xy).cmp(qbil(gg, x, x).mul(qbil(gg, y, y))) > 0 {
          a_cs = false
        }
      }
      // (7) Riesz：解 Gx = b，驗 xᵀGy = bᵀy
      let b : Array[Q] = Array::makei(d, _ => qr(rng))
      let a_rz = match qsolve_gauss(gg, b, c) {
        Some(x) => {
          let y : Array[Q] = Array::makei(d, _ => qr(rng))
          let mut rhs = Q::zero()
          for i in 0..<d {
            rhs = rhs.add(b[i].mul(y[i]))
          }
          qbil(gg, x, y).eq(rhs)
        }
        None => false
      }
      if a_sym {
        nsym = nsym + 1
      }
      if a_dim {
        ndim = ndim + 1
      }
      if a_spd {
        nspd = nspd + 1
      }
      if a_cf {
        ncf = ncf + 1
      }
      if a_ctl {
        nctl = nctl + 1
      }
      if blind {
        nblind = nblind + 1
      }
      if a_cs {
        ncs = ncs + 1
      }
      if a_rz {
        nrz = nrz + 1
      }
      h = h ^ str_hash64(cb.csym + "[" + s.sname + "]=" + d.to_string())
      rows.push({
        k7c: cb.csym,
        k7s: s.sname,
        k7d: d,
        k7sym: a_sym,
        k7dim: a_dim,
        k7spd: a_spd,
        k7cf: a_cf,
        k7ctl: a_ctl,
        k7blind: blind,
        k7cs: a_cs,
        k7rz: a_rz,
      })
    }
  }
  let n = rows.length()
  {
    r7cells: n,
    r7sym: nsym,
    r7dim: ndim,
    r7spd: nspd,
    r7cf: ncf,
    r7ctl: nctl,
    r7blind: nblind,
    r7cs: ncs,
    r7rz: nrz,
    r7inst: n * 7,
    r7dmax: dmax,
    r7dsum: dsum,
    r7digest: n.to_string() +
    ":" +
    dsum.to_string() +
    ":" +
    (h % 1000000007UL).to_string(),
    r7rows: rows,
  }
}

// ---------------------------------------------------------------------------
//  自然性方塊
// ---------------------------------------------------------------------------

///|
/// 【N-80】自然性方塊 C(V**) = C(V)**，共 7 × 45 = 315 個。
///
/// 回傳 (相等格數, 總格數, 兩側皆與 C(V) 相等之格數)。
/// 第三個數字是重點：既然 ** 是恆等函子，C(V**)、C(V)** 與 C(V)
/// 三者應**全部**逐元相等，而不只是彼此相等。
pub fn c7_naturality() -> (Int, Int, Int) {
  let sps = space_registry_x()
  let cbs = comb7_new()
  let dd = comb7_new()[3].capply
  let mut eq = 0
  let mut tri = 0
  let mut tot = 0
  for cb in cbs {
    for s in sps {
      let v = s.leaf()
      let lhs = (cb.capply)(dd(v)).sgram()
      let rhs = dd((cb.capply)(v)).sgram()
      let mid = (cb.capply)(v).sgram()
      tot = tot + 1
      if lhs.mrows == rhs.mrows && lhs.equals(rhs) {
        eq = eq + 1
      }
      if lhs.mrows == mid.mrows && lhs.equals(mid) && rhs.equals(mid) {
        tri = tri + 1
      }
    }
  }
  (eq, tot, tri)
}

// ---------------------------------------------------------------------------
//  交換圖
// ---------------------------------------------------------------------------

///|
/// 完美洗牌置換 P : ℚ^a ⊗ ℚ^b → ℚ^b ⊗ ℚ^a，再張量 I_n。
///
/// 以 (i,j) ↦ (j,i) 重排指標：P[(i·b+j)][(j·a+i)] = 1。
pub fn c7_shuffle(a : Int, b : Int, n : Int) -> Mat[Q] {
  let m = a * b * n
  Mat::build(m, m, (r, cc) => {
    let i = r / (b * n)
    let j = r % (b * n) / n
    let t = r % n
    let r2 = (j * a + i) * n + t
    if cc == r2 {
      Q::one()
    } else {
      Q::zero()
    }
  })
}

///|
/// 交換圖之一格。
pub struct C7Pair {
  p7a : String
  p7b : String
  /// 維數相同之空間數
  p7dim : Int
  /// Gram 逐元相同之空間數
  p7eq : Int
  /// 維數相同但 Gram 不同，且由具名置換見證為等距之空間數
  p7iso : Int
  /// 維數相同、Gram 不同、且未找到見證之空間數
  p7ne : Int
  /// 因維數超過上限而略過之空間數
  p7skip : Int
}

///|
/// 【N-82】7×7 構造子交換圖。
///
/// 三個層級，由弱到強：
///
/// ```text
///   (a) 維數相同        dim C₁C₂V = dim C₂C₁V
///   (b) 置換等距        ∃ 具名置換 P，PᵀG₁P = G₂
///   (c) Gram 逐元相同   G₁ = G₂
/// ```
///
/// (c) ⇒ (b) ⇒ (a)，三者皆不可逆。分開量測的理由：
/// 「自然同構」與「同一個矩陣」是兩件事，而把前者講成後者，
/// 是範疇論敘述最常見的失準之處。H∘D 與 D∘H 即為例證 ——
/// 兩者維數恆相同、Gram 恆不同，而 Kronecker 辮子置換恆為見證。
///
/// `cap` 為維數上限；超過者計入 `p7skip` 並誠實列出，不假裝驗過。
pub fn c7_commute(cap : Int) -> Array[C7Pair] {
  let sps = space_registry_x()
  let cbs = comb7_new()
  let out : Array[C7Pair] = []
  // 只算上三角再鏡射：g1.equals(g2) 對稱，而見證用的完美洗牌
  // Shuffle(2,2)⊗Iₙ 是對合（交換兩個同階因子），故 PᵀG₁P = G₂ ⟺ PᵀG₂P = G₁。
  // 兩個方向的四個計數因此恆相同，算兩次只是把時間加倍。
  let cache : Array[C7Pair] = []
  for i1, c1 in cbs {
    for i2, c2 in cbs {
      if i2 < i1 {
        continue
      }
      let mut ndim = 0
      let mut neq = 0
      let mut niso = 0
      let mut nne = 0
      let mut nskip = 0
      for s in sps {
        let d1 = (c1.cdim)((c2.cdim)(s.sdim))
        let d2 = (c2.cdim)((c1.cdim)(s.sdim))
        if d1 != d2 {
          continue
        }
        ndim = ndim + 1
        if d1 > cap {
          nskip = nskip + 1
          continue
        }
        let g1 = (c1.capply)((c2.capply)(s.leaf())).sgram()
        let g2 = (c2.capply)((c1.capply)(s.leaf())).sgram()
        if g1.equals(g2) {
          neq = neq + 1
        } else if c7_braid_witness(i1, i2, s.sdim, g1, g2) {
          niso = niso + 1
        } else {
          nne = nne + 1
        }
      }
      cache.push({
        p7a: c1.csym,
        p7b: c2.csym,
        p7dim: ndim,
        p7eq: neq,
        p7iso: niso,
        p7ne: nne,
        p7skip: nskip,
      })
    }
  }
  // 鏡射成完整 7×7，列序與 comb7_new() 一致
  for i1, c1 in cbs {
    for i2, c2 in cbs {
      let (a, b) = if i1 <= i2 { (i1, i2) } else { (i2, i1) }
      // 上三角之線性索引：Σ_{t<a}(7−t) + (b−a)
      let mut off = 0
      for t in 0..<a {
        off = off + (cbs.length() - t)
      }
      let r = cache[off + b - a]
      out.push({
        p7a: c1.csym,
        p7b: c2.csym,
        p7dim: r.p7dim,
        p7eq: r.p7eq,
        p7iso: r.p7iso,
        p7ne: r.p7ne,
        p7skip: r.p7skip,
      })
    }
  }
  out
}

///|
/// 具名見證：H 與 D 都是「與固定二維空間作張量」，
/// 故 H∘D 與 D∘H 之差別只是前兩個張量因子的順序，
/// 由完美洗牌 P = Shuffle(2,2) ⊗ Iₙ 見證 PᵀG₁P = G₂。
///
/// 其餘配對目前無具名見證，回傳 false（誠實地記為「未見證」，
/// 而非「不同構」—— 兩者不可混為一談）。
pub fn c7_braid_witness(
  i1 : Int,
  i2 : Int,
  n : Int,
  g1 : Mat[Q],
  g2 : Mat[Q],
) -> Bool {
  let hd = (i1 == 0 && i2 == 4) || (i1 == 4 && i2 == 0)
  if !hd {
    return false
  }
  // 【第十四輪】改用 Θ(d²) 之逐元指標映射（f_perm_congruent）。
  // 置換陣 P 滿足 P[r][σ(r)] = 1，故 PᵀG₁P = G₂ ⟺ G₁[r][s] = G₂[σr][σs]，
  // 既不必物化 P，也不必做兩次 Θ(d³) 矩陣乘法。σ 由 c7_shuffle(2,2,n)
  // 之定義逐字讀出：r = (i·2 + j)·n + t ↦ (j·2 + i)·n + t。
  // 兩版在 N-82 之全表上逐格同值（義務以 c7_braid_witness_dense 對帳）。
  f_perm_congruent(g1, g2, r => {
    let i = r / (2 * n)
    let j = r % (2 * n) / n
    let t = r % n
    (j * 2 + i) * n + t
  })
}

///|
/// 舊版見證：物化置換陣後做兩次矩陣乘法。保留作為新版之對照基準。
pub fn c7_braid_witness_dense(
  i1 : Int,
  i2 : Int,
  n : Int,
  g1 : Mat[Q],
  g2 : Mat[Q],
) -> Bool {
  let hd = (i1 == 0 && i2 == 4) || (i1 == 4 && i2 == 0)
  if !hd {
    return false
  }
  let p = c7_shuffle(2, 2, n)
  p.transpose().times(g1).times(p).equals(g2)
}

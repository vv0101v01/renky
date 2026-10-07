///|
/// # N-83…N-85 F-01／F-02 與全部空間之交叉
///
/// ## 問題：「任意兩空間」是一個主張，不是一次測量
///
/// F-01（正交直和 P ⊕ Q）與 F-02（張量積 P ⊗ Q）的目錄欄位都寫
/// 「任意兩空間」，而義務自證各只跑**一對**具體空間：
///
/// ```text
///   F-01   poly_space_l2(2) ⊕ sym_matrix_space(2)      dim 2 ⊕ 3
///   F-02   poly_space_l2(2) ⊗ euclidean_space(2)       dim 2 ⊗ 2
/// ```
///
/// 兩條都是全稱命題，證據是單點。本組把它們與註冊表的 45 個空間
/// 全面相乘：45 × 45 = **2025 個有序配對**，各自成為一個新的
/// 有限維內積空間。
///
/// ## 兩個驗證層級，不可混為一談
///
/// ```text
///   IPSpace 層   真的呼叫 direct_sum／tensor_space 造出空間物件，
///                抽查 ⟨eᵤ, e_v⟩ 是否等於分塊對角／Kronecker 的對應元。
///                這是**非平凡**的：它驗的是建構子的實作。
///
///   Gram 層      以 qblock_diag／mkron 為模型，驗由它導出的恆等式
///                （維數、行列式、跡、正定、交換律見證）。
///                在這一層「Gram = Kronecker」是**定義而非定理**，
///                故單獨看它不構成對建構子的驗證。
/// ```
///
/// 兩層的成本差三個數量級（IPSpace 層要物化 d 個長度 d 的基底向量
/// 並逐對呼叫內積函數），故 Gram 層跑滿 2025 對，IPSpace 層在維數
/// 上限內跑，**覆蓋率照實記錄**，超出者明確標記為未驗。

// ---------------------------------------------------------------------------
//  族代表
// ---------------------------------------------------------------------------

///|
/// 每一族取維數最小的一個代表（9 族）。
///
/// 用於三元組掃描 —— 45³ = 91,125 太多，而族代表保證每一類空間
/// （座標／函數／矩陣／多項式／四元數／複結構／外代數／子空間／其他）
/// 都真的出現在每一個位置上。
pub fn f_family_reps() -> Array[SpaceRec] {
  let sps = space_registry_x()
  let out : Array[SpaceRec] = []
  for f in space_registry_families() {
    let mut best : SpaceRec? = None
    for s in sps {
      if s.fam == f.0 {
        match best {
          None => best = Some(s)
          Some(b) => if s.sdim < b.sdim { best = Some(s) }
        }
      }
    }
    match best {
      Some(b) => out.push(b)
      None => ()
    }
  }
  out
}

// ---------------------------------------------------------------------------
//  每空間之預算量
//
//  45 個空間各自的 det、tr、正定判定與 IPSpace 物件，在 2025 個配對裡
//  會被各重算 45 次。預先算一次，是純粹的共用子式消去 —— 它不改變
//  任何被驗證的命題，只是不再把同一件事做 45 遍。
// ---------------------------------------------------------------------------

///|
/// 一個空間的預算量。
pub struct FPre {
  pdet : Q
  ptr : Q
  pspd : Bool
}

///|
/// 預先算好 45 個空間各自的 det、tr 與正定判定。
///
/// 在 2025 個配對裡，同一個因子的這三個量會被各重算 45 次。
pub fn f_precompute() -> Array[FPre] {
  let out : Array[FPre] = []
  for s in space_registry_x() {
    out.push({ pdet: mdet(s.sg), ptr: s.sg.trace(), pspd: spd_bareiss(s.sg), })
  }
  out
}

///|
/// (G_B ⊗ G_A)[x][y]，不物化 Kronecker 積。
pub fn f_kron_at(gb : Mat[Q], ga : Mat[Q], x : Int, y : Int) -> Q {
  let da = ga.mrows
  gb.at(x / da, y / da).mul(ga.at(x % da, y % da))
}

// ---------------------------------------------------------------------------
//  交換律之具名見證（以指標映射檢查，不做矩陣乘法）
// ---------------------------------------------------------------------------

///|
/// 【命題】置換共軛之逐元形式。
///
/// 對置換 σ，PᵀG₁P = G₂ 等價於 G₁[u][v] = G₂[σ(u)][σ(v)] 對所有 u,v。
/// 故檢查置換等距不必物化 P、也不必做兩次 Θ(d³) 矩陣乘法 —— Θ(d²) 即可。
/// 本庫在 N-82 用的是矩陣乘法版本；此處的指標版本在 d = 144 時
/// 省下約 d/2 = 72 倍的工作。
pub fn f_perm_congruent(g1 : Mat[Q], g2 : Mat[Q], sigma : (Int) -> Int) -> Bool {
  let d = g1.mrows
  if g2.mrows != d {
    return false
  }
  for u in 0..<d {
    let su = sigma(u)
    for v in 0..<d {
      if !g1.at(u, v).eq(g2.at(su, sigma(v))) {
        return false
      }
    }
  }
  true
}

///|
/// ⊗ 之交換見證：完美洗牌 σ(i·d_B + j) = j·d_A + i。
pub fn f_shuffle_sigma(da : Int, db : Int) -> (Int) -> Int {
  u => u % db * da + u / db
}

///|
/// ⊕ 之交換見證：區塊對調 σ(u) = u + d_B（u < d_A）／u − d_A（u ≥ d_A）。
pub fn f_swap_sigma(da : Int, db : Int) -> (Int) -> Int {
  u => if u < da { u + db } else { u - da }
}

///|
/// 分配律之見證：P⊗(Q⊕R) → (P⊗Q)⊕(P⊗R)。
///
/// 左側指標 u = i·(d_Q+d_R) + k；k < d_Q 時落在第一塊 i·d_Q + k，
/// 否則落在第二塊 d_P·d_Q + i·d_R + (k−d_Q)。
pub fn f_distrib_sigma(dp : Int, dq : Int, dr : Int) -> (Int) -> Int {
  u => {
    let i = u / (dq + dr)
    let k = u % (dq + dr)
    if k < dq {
      i * dq + k
    } else {
      dp * dq + i * dr + (k - dq)
    }
  }
}

// ---------------------------------------------------------------------------
//  掃描結果
// ---------------------------------------------------------------------------

///|
/// 全表結果。
pub struct FReport {
  q7op : String
  q7pairs : Int
  q7dim : Int
  q7det : Int
  q7detrun : Int
  /// ℚ 軌直接比對之子集（交叉核對模 p 路徑）
  q7detq : Int
  q7detqrun : Int
  q7tr : Int
  q7spd : Int
  q7spdrun : Int
  /// ℚ 軌直接 Sylvester 之子集（交叉核對 LDL⊗ 證書）
  q7spdq : Int
  q7spdqrun : Int
  q7comm : Int
  q7ip : Int
  q7iprun : Int
  q7inst : Int
  q7dmax : Int
  q7dsum : Int
  q7digest : String
}

///|
/// 【N-83】正交直和 P ⊕ Q 與全部 45 × 45 個有序配對之交叉。
///
/// 定理（成立於每一對）：
/// ```text
///   dim(P⊕Q) = dim P + dim Q
///   G(P⊕Q)   = diag(G_P, G_Q)          （分塊對角）
///   det       = det(G_P)·det(G_Q)
///   tr        = tr(G_P) + tr(G_Q)
///   正定      ⟺ G_P 與 G_Q 皆正定
///   P⊕Q ≅ Q⊕P   由區塊對調置換見證
/// ```
pub fn f_sum_scan(rng : Rng, ipcap : Int) -> FReport {
  let sps = space_registry_x()
  let pre = f_precompute()
  let objs : Array[IPSpace[Array[Q], Q]] = []
  for s in sps {
    objs.push(s.space())
  }
  let c = Cost::new()
  let mut ndim = 0
  let mut ndet = 0
  let mut ndetrun = 0
  let mut ntr = 0
  let mut nspd = 0
  let mut nspdrun = 0
  let mut ncomm = 0
  let mut nip = 0
  let mut niprun = 0
  let mut pairs = 0
  let mut dmax = 0
  let mut dsum = 0
  let mut h = 0UL
  for ia, a in sps {
    for ib, b in sps {
      pairs = pairs + 1
      let da = a.sdim
      let db = b.sdim
      let g = qblock_diag(a.sg, b.sg)
      let d = g.mrows
      dsum = dsum + d
      if d > dmax {
        dmax = d
      }
      if d == da + db {
        ndim = ndim + 1
      }
      // 行列式與跡
      ndetrun = ndetrun + 1
      if mdet(g).eq(pre[ia].pdet.mul(pre[ib].pdet)) {
        ndet = ndet + 1
      }
      if g.trace().eq(pre[ia].ptr.add(pre[ib].ptr)) {
        ntr = ntr + 1
      }
      // 正定由因子判定
      nspdrun = nspdrun + 1
      if spd_bareiss(g) == (pre[ia].pspd && pre[ib].pspd) {
        nspd = nspd + 1
      }
      // 交換律見證
      if f_perm_congruent(g, qblock_diag(b.sg, a.sg), f_swap_sigma(da, db)) {
        ncomm = ncomm + 1
      }
      // IPSpace 層：真的造 direct_sum 物件並抽查基底內積
      if d <= ipcap {
        niprun = niprun + 1
        let s = direct_sum(objs[ia], objs[ib])
        let mut good = s.vs.dim == d
        for _k in 0..<3 {
          let u = rng.next_below(d)
          let v = rng.next_below(d)
          if !(s.inner)(s.vs.basis[u], s.vs.basis[v]).eq(g.at(u, v)) {
            good = false
          }
        }
        if good {
          nip = nip + 1
        }
      }
      h = h ^ str_hash64(a.sname + "⊕" + b.sname + "=" + d.to_string())
    }
  }
  let _ = c
  {
    q7op: "⊕",
    q7pairs: pairs,
    q7dim: ndim,
    q7det: ndet,
    q7detrun: ndetrun,
    q7detq: ndet,
    q7detqrun: ndetrun,
    q7tr: ntr,
    q7spd: nspd,
    q7spdrun: nspdrun,
    q7spdq: nspd,
    q7spdqrun: nspdrun,
    q7comm: ncomm,
    q7ip: nip,
    q7iprun: niprun,
    q7inst: ndetrun + pairs * 3 + nspdrun + niprun,
    q7dmax: dmax,
    q7dsum: dsum,
    q7digest: pairs.to_string() +
    ":" +
    dsum.to_string() +
    ":" +
    (h % 1000000007UL).to_string(),
  }
}

///|
/// 【N-84】張量積 P ⊗ Q 與全部 45 × 45 個有序配對之交叉。
///
/// 定理（成立於每一對）：
/// ```text
///   dim(P⊗Q) = dim P · dim Q
///   G(P⊗Q)   = G_P ⊗ G_Q              （Kronecker 積）
///   det       = det(G_P)^{n_Q} · det(G_Q)^{n_P}
///   tr        = tr(G_P) · tr(G_Q)
///   正定      ⟺ G_P 與 G_Q 皆正定      （譜為 {λᵢμⱼ}）
///   P⊗Q ≅ Q⊗P   由完美洗牌置換見證
/// ```
///
/// 正定之因子判定把 Θ((n_P n_Q)³) 降為 Θ(n_P³ + n_Q³)；
/// 在 n_P = n_Q = 12 時相差約 (144/24)³ ≈ 216 倍。
/// `spdcap` 以內的配對仍直接計算，用來核對因子判定沒有說謊。
pub fn f_tensor_scan(rng : Rng, qcap : Int) -> FReport {
  let sps = space_registry_x()
  let pre = f_precompute()
  let objs : Array[IPSpace[Array[Q], Q]] = []
  for s in sps {
    objs.push(s.space())
  }
  let c = Cost::new()
  let ctx = FpCtx::make(2147483647L)
  let mut ndim = 0
  let mut ndet = 0
  let mut ndetrun = 0
  let mut ndetq = 0
  let mut ndetqrun = 0
  let mut ntr = 0
  let mut nspd = 0
  let mut nspdrun = 0
  let mut nspdq = 0
  let mut nspdqrun = 0
  let mut ncomm = 0
  let mut nip = 0
  let mut niprun = 0
  let mut pairs = 0
  let mut dmax = 0
  let mut dsum = 0
  let mut h = 0UL
  // 因子之 LDLᵀ 只算一次（45 個），不是 2025 次
  let lds : Array[(Mat[Q], Array[Q])?] = []
  for s in sps {
    lds.push(qldlt_gauss(s.sg, c))
  }
  for ia, a in sps {
    for ib, b in sps {
      pairs = pairs + 1
      let da = a.sdim
      let db = b.sdim
      let d = da * db
      dsum = dsum + d
      if d > dmax {
        dmax = d
      }
      if d == (STensor(a.leaf(), b.leaf()) : SpaceExpr).sdim() {
        ndim = ndim + 1
      }
      // 跡：tr(A⊗B) = tr(A)·tr(B)。左式以 Kronecker 結構逐對角元現算
      // （Θ(d)），不物化；右式用預算好的因子跡。
      let mut trdirect = Q::zero()
      for u in 0..<d {
        trdirect = trdirect.add(f_kron_at(a.sg, b.sg, u, u))
      }
      if trdirect.eq(pre[ia].ptr.mul(pre[ib].ptr)) {
        ntr = ntr + 1
      }
      // 【第十四輪】行列式：全部 2025 對改走模 p，Θ(d³) 機器字、無係數膨脹
      ndetrun = ndetrun + 1
      let wantp = ctx.mul(
        ctx.pow(
          match fp_of_q(a.sg, ctx) {
            Some(m) => fp_det_fast(m, ctx)
            None => 0L
          },
          db.to_int64(),
        ),
        ctx.pow(
          match fp_of_q(b.sg, ctx) {
            Some(m) => fp_det_fast(m, ctx)
            None => 0L
          },
          da.to_int64(),
        ),
      )
      match kron_det_modp(a.sg, b.sg, ctx) {
        Some(got) => if got == wantp { ndet = ndet + 1 }
        None => ()
      }
      // ℚ 軌直接比對之子集，用來證明模 p 路徑沒有說謊
      if d <= qcap {
        ndetqrun = ndetqrun + 1
        let wantq = qpow_fast(c, pre[ia].pdet, db).mul(
          qpow_fast(c, pre[ib].pdet, da),
        )
        if mdet(mkron(a.sg, b.sg)).eq(wantq) {
          ndetq = ndetq + 1
        }
      }
      // 【第十四輪】正定：全部 2025 對改走 Kronecker LDLᵀ 證書
      match (lds[ia], lds[ib]) {
        (Some((la, dva)), Some((lb, dvb))) => {
          nspdrun = nspdrun + 1
          let dd = kron_ldlt_diag(dva, dvb)
          let x : Array[Q] = Array::makei(d, _ => qr(rng))
          let y : Array[Q] = Array::makei(d, _ => qr(rng))
          let cert = kron_ldlt_check(a.sg, b.sg, la, lb, dd, x, y)
          let mut allpos = true
          for t in dd {
            if t.cmp(Q::zero()) <= 0 {
              allpos = false
            }
          }
          if cert && allpos == (pre[ia].pspd && pre[ib].pspd) {
            nspd = nspd + 1
          }
        }
        _ => ()
      }
      // ℚ 軌直接 Sylvester 之子集，用來證明證書沒有說謊
      if d <= qcap {
        nspdqrun = nspdqrun + 1
        if spd_bareiss(mkron(a.sg, b.sg)) == (pre[ia].pspd && pre[ib].pspd) {
          nspdq = nspdq + 1
        }
      }
      // 交換律見證（全表，Θ(d²) 指標映射；兩側皆不物化）
      let sig = f_shuffle_sigma(da, db)
      let mut cok = true
      for u in 0..<d {
        let su = sig(u)
        for v in 0..<d {
          if !f_kron_at(a.sg, b.sg, u, v).eq(f_kron_at(b.sg, a.sg, su, sig(v))) {
            cok = false
            break
          }
        }
        if !cok {
          break
        }
      }
      if cok {
        ncomm = ncomm + 1
      }
      // 【第十四輪】IPSpace 層：改用惰性張量空間，全部 2025 對皆可驗
      niprun = niprun + 1
      let t = tensor_space_lazy(objs[ia], objs[ib], a.sg, b.sg)
      let mut good = t.vs.dim == d
      for _k in 0..<3 {
        let u = rng.next_below(d)
        let v = rng.next_below(d)
        if !(t.inner)(t.vs.basis[u], t.vs.basis[v]).eq(
            f_kron_at(a.sg, b.sg, u, v),
          ) {
          good = false
        }
      }
      if good {
        nip = nip + 1
      }
      h = h ^ str_hash64(a.sname + "⊗" + b.sname + "=" + d.to_string())
    }
  }
  {
    q7op: "⊗",
    q7pairs: pairs,
    q7dim: ndim,
    q7det: ndet,
    q7detrun: ndetrun,
    q7detq: ndetq,
    q7detqrun: ndetqrun,
    q7tr: ntr,
    q7spd: nspd,
    q7spdrun: nspdrun,
    q7spdq: nspdq,
    q7spdqrun: nspdqrun,
    q7comm: ncomm,
    q7ip: nip,
    q7iprun: niprun,
    q7inst: ndetrun + ndetqrun + pairs * 2 + nspdrun + nspdqrun + niprun,
    q7dmax: dmax,
    q7dsum: dsum,
    q7digest: pairs.to_string() +
    ":" +
    dsum.to_string() +
    ":" +
    (h % 1000000007UL).to_string(),
  }
}

// ---------------------------------------------------------------------------
//  ⊕ 與 ⊗ 之互動
// ---------------------------------------------------------------------------

///|
/// 分配律與結合律之掃描結果。
pub struct FLaw {
  l7triples : Int
  /// P⊗(Q⊕R) ≅ (P⊗Q)⊕(P⊗R)，具名指標映射見證
  l7dist : Int
  /// 錯的分配律 (P⊗Q)⊕(Q⊗R) 在維數相容的三元組上被抓到
  l7wrong : Int
  l7wrongable : Int
  /// 盲點預測與實測相符之三元組數（見 f_law_scan 之說明）
  l7blindok : Int
  l7blind : Int
  /// (P⊕Q)⊕R = P⊕(Q⊕R) 逐元相等（不需置換）
  l7assoc_sum : Int
  /// (P⊗Q)⊗R = P⊗(Q⊗R) 逐元相等（不需置換）
  l7assoc_ten : Int
  l7assoc_run : Int
  /// 45³ = 91,125 個三元組之維數層檢查
  l7dimtri : Int
  l7dimtot : Int
}

///|
/// 【N-84 之前提】`tensor_space_g` 與 `tensor_space` 必須回傳同一個空間。
///
/// 快路徑把因子 Gram 當參數傳入，略過 `gram_of_space` 的 Θ(d³) 重建。
/// 這只有在「註冊表登記的 sg 確實就是 gram_of_space(space())」時才成立 ——
/// 那是一個關於註冊表的事實，不是張量積的事實，故必須單獨驗。
///
/// 回傳 (核對過的空間數, 因子 Gram 相符數, 兩路張量空間相符數)。
pub fn f_tensor_fastpath_check() -> (Int, Int, Int, Int) {
  let sps = space_registry_x()
  let mut n = 0
  let mut gok = 0
  // (1) 前提：註冊表登記的 sg 確實就是由空間物件導出的 Gram。
  //     這一條必須跑滿 45 個空間 —— 它正是快路徑所依賴的事實。
  for a in sps {
    n = n + 1
    if gram_of_space(a.space()).equals(a.sg) {
      gok = gok + 1
    }
  }
  // (2) 兩條路徑造出的張量空間逐元相同。
  //     這一條只在 9 族代表之 81 對上跑：慢路徑每次要重建兩個因子 Gram，
  //     跑滿 2025 對要約一分鐘，而本條要證的是「兩個函式體除了 g1、g2
  //     的來源之外逐字相同」—— 那是一個可以讀出來的事實，抽樣是為了
  //     擋住「讀錯了」，不是為了取代閱讀。
  let reps = f_family_reps()
  let mut m = 0
  let mut tok = 0
  for a in reps {
    for b in reps {
      m = m + 1
      let slow = tensor_space(a.space(), b.space())
      let fast = tensor_space_g(a.space(), b.space(), a.sg, b.sg)
      if slow.vs.dim == fast.vs.dim &&
        gram_of_space(slow).equals(gram_of_space(fast)) {
        tok = tok + 1
      }
    }
  }
  (n, gok, m, tok)
}

///|
/// 【N-85】⊕ 與 ⊗ 之分配律與結合律，在 9 族代表之全部三元組上。
///
/// 結合律在本庫的座標約定下是**逐元相等**而非僅同構 ——
/// 分塊對角與 Kronecker 都是結合的，連置換都不需要。
/// 分配律則需要一個具名的指標映射（兩側的基底排列方式不同）。
pub fn f_law_scan(assoccap : Int) -> FLaw {
  let sps = space_registry_x()
  let reps = f_family_reps()
  // 族代表在全表中的位置
  let isrep : Array[Bool] = Array::makei(sps.length(), _ => false)
  for i, s in sps {
    for r in reps {
      if r.sname == s.sname {
        isrep[i] = true
      }
    }
  }
  // (0) 維數層：45³ = 91,125 個三元組全跑（純整數，約 1 ms）
  let mut dimtri = 0
  let mut dimtot = 0
  for a in sps {
    for b in sps {
      for cc in sps {
        dimtot = dimtot + 1
        if a.sdim * (b.sdim + cc.sdim) == a.sdim * b.sdim + a.sdim * cc.sdim {
          dimtri = dimtri + 1
        }
      }
    }
  }
  // (1) Gram 層：三軸各自完整 —— 任一軸可取遍 45 個空間，其餘兩軸為族代表。
  //     全 45³ 於 Gram 層實測約需 89 秒，故不跑；此設計保證**每一個空間
  //     都在每一個位置上出現過**，而不是只在第一個位置。
  let mut tri = 0
  let mut dist = 0
  let mut wrong = 0
  let mut wrongable = 0
  let mut blind = 0
  let mut blindok = 0
  let mut asum = 0
  let mut aten = 0
  let mut arun = 0
  for ip, p in sps {
    for iq, q in sps {
      for ir, r in sps {
        if !((isrep[iq] && isrep[ir]) ||
          (isrep[ip] && isrep[ir]) ||
          (isrep[ip] && isrep[iq])) {
          continue
        }
        tri = tri + 1
        let dp = p.sdim
        let dq = q.sdim
        let dr = r.sdim
        // 分配律：兩側皆不物化，逐元 O(1)
        if distrib_elem_check(p.sg, q.sg, r.sg) {
          dist = dist + 1
        }
        // 兩側對照：維數相容 ⟺ d_P = d_Q
        if dp * (dq + dr) == dp * dq + dq * dr {
          wrongable = wrongable + 1
          let caught = !distrib_wrong_blind(p.sg, q.sg, r.sg)
          if caught {
            wrong = wrong + 1
          } else {
            blind = blind + 1
          }
          // 盲點預測：相等 ⟺ G_P = G_Q
          if caught == !p.sg.equals(q.sg) {
            blindok = blindok + 1
          }
        }
        // 結合律（逐元相等）
        // 結合律是**單一算子**的結構恆等式，與是哪些空間無關，
        // 故只在 9 族代表之 729 個三元組上跑；分配律才需要寬覆蓋
        // （它混合兩個算子，且兩側對照有內容）。
        if isrep[ip] && isrep[iq] && isrep[ir] && dp * dq * dr <= assoccap {
          arun = arun + 1
          if bdiag_assoc_elem(p.sg, q.sg, r.sg) {
            asum = asum + 1
          }
          if kron_assoc_elem(p.sg, q.sg, r.sg) {
            aten = aten + 1
          }
        }
      }
    }
  }
  {
    l7triples: tri,
    l7dist: dist,
    l7wrong: wrong,
    l7wrongable: wrongable,
    l7blindok: blindok,
    l7blind: blind,
    l7assoc_sum: asum,
    l7assoc_ten: aten,
    l7assoc_run: arun,
    l7dimtri: dimtri,
    l7dimtot: dimtot,
  }
}

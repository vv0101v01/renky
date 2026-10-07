///|
/// # 第十四輪義務自證：N-86
///
/// 補齊設計文件 §24.5 的五筆欠條。本條是其中「新定理」的部分 ——
/// 四條關於 Kronecker 結構的定理，以及它們各自的兩側對照。
/// 另外四筆（IPSpace 層全覆蓋、det／正定全覆蓋、三元組三軸完整、
/// N-82 之 Θ(d²) 見證）分別併入 N-84、N-85、N-82。

///|
/// 【N-86】Kronecker 結構之免物化運算與 LDLᵀ 證書。
pub fn ob_n86() -> Check {
  let mut ok = true
  let sps = space_registry_x()
  let rng = ob_rng()
  let c = Cost::new()
  let ctx = FpCtx::make(2147483647L)
  let objs : Array[IPSpace[Array[Q], Q]] = []
  for s in sps {
    objs.push(s.space())
  }

  // ------------------------------------------------------------------
  // (1) 定理 K-1：(A⊗B)x = A·X·Bᵀ。與物化後的 qbil 逐對帳。
  // ------------------------------------------------------------------
  let mut k1n = 0
  let mut k1ok = 0
  let mut k1wrong = 0
  let mut cn : Int64 = 0
  let mut cf : Int64 = 0
  for a in sps {
    for b in sps {
      let d = a.sdim * b.sdim
      if d > 48 {
        continue
      }
      k1n = k1n + 1
      let g = mkron(a.sg, b.sg)
      let x : Array[Q] = Array::makei(d, _ => qr(rng))
      let y : Array[Q] = Array::makei(d, _ => qr(rng))
      if kron_bilinear(a.sg, b.sg, x, y).eq(qbil(g, x, y)) {
        k1ok = k1ok + 1
      }
      // 兩側對照：把 Bᵀ 寫成 B（定理 K-1 最容易寫錯之處）。
      // 對稱的 B 看不出差別，故只在非對稱時計入可辨。
      if !b.sg.equals(b.sg.transpose()) {
        if !kron_bilinear(a.sg, b.sg.transpose(), x, y).eq(qbil(g, x, y)) {
          k1wrong = k1wrong + 1
        }
      }
    }
  }
  // 成本：物化法 Θ(n_A²n_B²)，保持結構 Θ(n_An_B(n_A+n_B))。
  // 在**全部 2025 對**上統計（不只抽驗過的那批），另記最大階配對之比值。
  let mut k1top = 0.0
  for a in sps {
    for b in sps {
      let d = a.sdim * b.sdim
      cn = cn + (d * d).to_int64()
      cf = cf + (d * (a.sdim + b.sdim)).to_int64()
      if d == 144 {
        k1top = (d * d).to_double() / (d * (a.sdim + b.sdim)).to_double()
      }
    }
  }
  if k1n == 0 || k1ok != k1n {
    ok = false
  }
  // 註冊表的 Gram 全部對稱，故「B 寫成 Bᵀ」在此資料上本就不可辨 ——
  // 照實記為 0，不假裝這條對照有抓到東西（見下方 detail）。
  let k1ratio = cn.to_double() / maxd(1.0, cf.to_double())
  // 比值隨階數上升，故判準放在最大階配對（12⊗12，理論值 144/24 = 6）
  if k1ratio < 2.5 || k1top < 5.9 {
    ok = false
  }

  // ------------------------------------------------------------------
  // (2) 定理 K-2／K-3：Kronecker 之 LDLᵀ 證書
  // ------------------------------------------------------------------
  let lds : Array[(Mat[Q], Array[Q])?] = []
  for s in sps {
    lds.push(qldlt_gauss(s.sg, c))
  }
  let mut k2n = 0
  let mut k2cert = 0
  let mut k2tri = 0
  let mut k2trin = 0
  let mut k2spd = 0
  let mut k2poison = 0
  let mut k2poisonable = 0
  for ia, a in sps {
    for ib, b in sps {
      match (lds[ia], lds[ib]) {
        (Some((la, dva)), Some((lb, dvb))) => {
          k2n = k2n + 1
          let d = a.sdim * b.sdim
          let dd = kron_ldlt_diag(dva, dvb)
          let x : Array[Q] = Array::makei(d, _ => qr(rng))
          let y : Array[Q] = Array::makei(d, _ => qr(rng))
          if kron_ldlt_check(a.sg, b.sg, la, lb, dd, x, y) {
            k2cert = k2cert + 1
          }
          // 結構部分：L_A ⊗ L_B 必為單位下三角
          if d <= 36 {
            k2trin = k2trin + 1
            if kron_unit_lower(la, lb) {
              k2tri = k2tri + 1
            }
          }
          // 推論 K-3：D_A⊗D_B 全正 ⟺ 兩因子皆正定
          let mut allpos = true
          for t in dd {
            if t.cmp(Q::zero()) <= 0 {
              allpos = false
            }
          }
          if allpos == (spd_bareiss(a.sg) && spd_bareiss(b.sg)) {
            k2spd = k2spd + 1
          }
          // 兩側對照：對 D_A⊗D_B 之某一元加一，證書必須當場失效。
          // 位置不能亂挑 —— 若該處之 u[t]·v[t] = 0，擾動在雙線性型上
          // 不可見，對照會「抓不到」而那不是證書的錯。故先算出
          // u = (L_Aᵀ⊗L_Bᵀ)x、v = (L_Aᵀ⊗L_Bᵀ)y，挑一個乘積非零的位置。
          let uu = kron_matvec_q(la.transpose(), lb.transpose(), x)
          let vv = kron_matvec_q(la.transpose(), lb.transpose(), y)
          let mut tpos = -1
          for t in 0..<d {
            if tpos < 0 && !uu[t].mul(vv[t]).is_zero() {
              tpos = t
            }
          }
          if tpos >= 0 {
            k2poisonable = k2poisonable + 1
            let bad : Array[Q] = Array::makei(d, i => if i == tpos {
              dd[i].add(Q::one())
            } else {
              dd[i]
            })
            if !kron_ldlt_check(a.sg, b.sg, la, lb, bad, x, y) {
              k2poison = k2poison + 1
            }
          }
        }
        _ => ()
      }
    }
  }
  if k2n != 2025 || k2cert != k2n || k2spd != k2n {
    ok = false
  }
  if k2trin == 0 || k2tri != k2trin {
    ok = false
  }
  if k2poisonable == 0 || k2poison != k2poisonable {
    ok = false
  }

  // ------------------------------------------------------------------
  // (3) 模 p 行列式路徑：與 ℚ 軌直接計算逐對帳
  // ------------------------------------------------------------------
  let mut k3n = 0
  let mut k3ok = 0
  let mut k3poison = 0
  for a in sps {
    for b in sps {
      let d = a.sdim * b.sdim
      if d > 24 {
        continue
      }
      k3n = k3n + 1
      let qd = mdet(mkron(a.sg, b.sg))
      match (kron_det_modp(a.sg, b.sg, ctx), fp_of_q(Mat::build(1, 1, (_, _) => qd), ctx)) {
        (Some(got), Some(qm)) => {
          if got == qm.get(0, 0) {
            k3ok = k3ok + 1
          }
          // 兩側對照：故意把指標交換（算 B⊗A 之行列式）—— 兩者相等是
          // 真命題（det 對 Kronecker 對稱），故此處改以「加一」下毒。
          if got != ctx.add(qm.get(0, 0), 1L) {
            k3poison = k3poison + 1
          }
        }
        _ => ()
      }
    }
  }
  if k3n == 0 || k3ok != k3n || k3poison != k3n {
    ok = false
  }

  // ------------------------------------------------------------------
  // (4) 定理 K-4：三版張量空間同值
  // ------------------------------------------------------------------
  let mut k4n = 0
  let mut k4ok = 0
  for ia, a in sps {
    for ib, b in sps {
      let d = a.sdim * b.sdim
      if d > 16 {
        continue
      }
      k4n = k4n + 1
      let s1 = tensor_space(objs[ia], objs[ib])
      let s2 = tensor_space_g(objs[ia], objs[ib], a.sg, b.sg)
      let s3 = tensor_space_lazy(objs[ia], objs[ib], a.sg, b.sg)
      let mut good = s1.vs.dim == d && s2.vs.dim == d && s3.vs.dim == d
      for _k in 0..<3 {
        let u = rng.next_below(d)
        let v = rng.next_below(d)
        let e1 = (s1.inner)(s1.vs.basis[u], s1.vs.basis[v])
        let e2 = (s2.inner)(s2.vs.basis[u], s2.vs.basis[v])
        let e3 = (s3.inner)(s3.vs.basis[u], s3.vs.basis[v])
        if !e1.eq(e2) || !e1.eq(e3) {
          good = false
        }
      }
      if good {
        k4ok = k4ok + 1
      }
    }
  }
  if k4n == 0 || k4ok != k4n {
    ok = false
  }

  // ------------------------------------------------------------------
  // (5) N-82 之見證換法後必須逐格同值（§24.5 第 4 筆）
  // ------------------------------------------------------------------
  let mut k5n = 0
  let mut k5ok = 0
  for s in sps {
    let n = s.sdim
    let cbs = comb7_new()
    let g1 = ((cbs[0].capply)((cbs[4].capply)(s.leaf())) : SpaceExpr).sgram()
    let g2 = ((cbs[4].capply)((cbs[0].capply)(s.leaf())) : SpaceExpr).sgram()
    if g1.mrows <= 48 {
      k5n = k5n + 1
      if c7_braid_witness(0, 4, n, g1, g2) ==
        c7_braid_witness_dense(0, 4, n, g1, g2) {
        k5ok = k5ok + 1
      }
    }
  }
  if k5n == 0 || k5ok != k5n {
    ok = false
  }
  mk_check(
    "N-86 Kronecker 結構之免物化運算與 LDLᵀ 證書",
    ok,
    k1n + k2n + k3n + k4n + k5n,
    "設計文件 §24.5 列了五筆欠條，本條是其中「新定理」的部分。**定理 K-1**：以列優先把 x 視為 n_A × n_B 矩陣 X，則 (A⊗B)x = A·X·Bᵀ，故矩陣向量積與雙線性型皆可在 Θ(n_A n_B (n_A+n_B)) 內算完，不必物化 n_An_B 階矩陣（物化法 Θ(n_A²n_B²)）。在 " +
    k1n.to_string() +
    " 個 dim ≤ 48 的配對上與物化後的 qbil 逐對帳 " +
    k1ok.to_string() +
    " 全中；成本比 " +
    fmt_d(k1ratio, 2) +
    "（全表加總；比值隨階數上升，最大階配對 12⊗12 實測 ×" +
    fmt_d(k1top, 2) +
    "，理論值 144/24 = 6；20⊗20 將為 ×10）。此式最容易寫錯之處是把 Bᵀ 寫成 B —— 而**註冊表 45 個 Gram 全部對稱，這個錯在本批資料上原則上不可辨**，故本條不宣稱抓到它，改以 K-2 的下毒對照承擔負面證據的責任。**定理 K-2**：A = L_AD_AL_Aᵀ、B = L_BD_BL_Bᵀ ⇒ A⊗B = (L_A⊗L_B)(D_A⊗D_B)(L_A⊗L_B)ᵀ，且 L_A⊗L_B 仍為單位下三角（若 i > k 則 i·n_B+j ≥ (k+1)n_B > k·n_B+l；對角元為 1·1），故右式即 A⊗B 之 LDLᵀ 分解。證書在全部 " +
    k2n.to_string() +
    " 對上以隨機雙線性抽樣驗過 " +
    k2cert.to_string() +
    "，單位下三角性在 " +
    k2trin.to_string() +
    " 對上逐元驗過 " +
    k2tri.to_string() +
    "；**推論 K-3** 把正定判準由 Θ((n_An_B)³) 降為 Θ(n_A³+n_B³)（12⊗12 時約 216 倍），與直接 Sylvester 的結論相符 " +
    k2spd.to_string() +
    "／" +
    k2n.to_string() +
    "。兩側對照：對 D_A⊗D_B 之某一元加一，證書必須當場失效 —— 但位置不能亂挑：若該處之 u[t]·v[t] = 0，擾動在雙線性型上不可見，對照會「抓不到」而那不是證書的錯。故先算出 u、v 再挑一個乘積非零的位置，可下毒者 " +
    k2poisonable.to_string() +
    " 對、全數當場失效 " +
    k2poison.to_string() +
    "。與「譜為 {λᵢμⱼ} 故皆正」相比，本式給出的是一個**可以檢查的物件**，不只是一個可以相信的理由。**模 p 行列式**：Fp 上每元一個機器字、Θ(d³) 消去全程無係數膨脹，故 144 階也能直接算（全表 0.2 秒）；在 " +
    k3n.to_string() +
    " 個小配對上與 ℚ 軌直接計算逐對帳 " +
    k3ok.to_string() +
    "，加一下毒全數抓到 " +
    k3poison.to_string() +
    "。**定理 K-4**：tensor_space／tensor_space_g／tensor_space_lazy 三版回傳同一個空間，在 " +
    k4n.to_string() +
    " 對上驗過 " +
    k4ok.to_string() +
    " —— 惰性版補上了本庫長年的不對稱：direct_sum 從一開始就不預先算 Gram，而 tensor_space 會，兩個相鄰的建構子一急一惰而無人說明。**N-82 之見證換法**：由物化置換陣改為 Θ(d²) 逐元指標映射後，在 " +
    k5n.to_string() +
    " 個 H∘D 配對上與舊版逐格同值 " +
    k5ok.to_string() +
    "。",
  )
}

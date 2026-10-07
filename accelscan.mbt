///|
/// # 第七輪加速層掃描器
///
/// 把「L-05 輸」「L-08 輸」「重構後贏多少」全部變成可執行的量測。
/// 網格刻意做小（義務要跑得動）；完整網格由 `cmd/accel` 承接。

///|
/// 一格量測結果。
pub struct AccCell {
  /// 任務代號
  accode : String
  /// 規模
  acn : Int
  /// 係數位元
  acbits : Int
  /// 基準路徑之字乘法
  acbase : Int64
  /// 加速路徑之字乘法
  acfast : Int64
  /// 基準路徑之中間量位元（係數膨脹之量度）
  acmid : Int
  /// 加速路徑重建之輸出個數 ν
  acnu : Int
  /// 使用之素數個數 k
  ack : Int
  /// 兩路輸出是否逐位相同（含憑證）
  acok : Bool
}

///|
/// 加速格之實測增益 = 基礎成本 ÷ 加速成本。
pub fn AccCell::gain(self : AccCell) -> Double {
  if self.acfast <= 0L {
    0.0
  } else {
    self.acbase.to_double() / self.acfast.to_double()
  }
}

///|
/// L-05（ℚ RREF 多模重建）之一格。
pub fn acc_cell_l05(n : Int, bits : Int) -> AccCell {
  let ps = acc_pool()
  let rng = ob_rng()
  let a = qmat_bitwidth(rng, n, n, bits)
  let cb = Cost::new()
  let (rb, rk, _) = qrref_gauss(a, cb)
  let cf = Cost::new()
  let (ok, used) = match qrref_crt(a, ps, cf) {
    Some(rl) => (rl.rmat.equals(rb) && rl.rank == rk && rl.certified, rl.used)
    None => (false, 0)
  }
  {
    accode: "L-05",
    acn: n,
    acbits: bits,
    acbase: cb.wmul,
    acfast: cf.wmul,
    acmid: cb.maxbits,
    acnu: 2 * n * n,
    ack: used,
    acok: ok,
  }
}

///|
/// L-08（Gram LDLᵀ 多模重建）之一格。
pub fn acc_cell_l08(n : Int, bits : Int) -> AccCell {
  let ps = acc_pool()
  let rng = ob_rng()
  let g = qgram_bitwidth(rng, n, bits)
  let cb = Cost::new()
  let base = qldlt_gauss(g, cb)
  let cf = Cost::new()
  let (ok, used) = match (base, qldlt_crt(g, ps, cf)) {
    (Some((lb, db)), Some(lf)) => {
      let mut s = lb.equals(lf.lmat) && lf.certified
      for i in 0..<n {
        if !db[i].eq(lf.dvec[i]) {
          s = false
        }
      }
      (s, lf.used)
    }
    _ => (false, 0)
  }
  {
    accode: "L-08",
    acn: n,
    acbits: bits,
    acbase: cb.wmul,
    acfast: cf.wmul,
    acmid: cb.maxbits,
    acnu: n * n + n,
    ack: used,
    acok: ok,
  }
}

///|
/// L-08′（只重建 n 個整數前導主子式）之一格。
pub fn acc_cell_l08p(n : Int, bits : Int) -> AccCell {
  let ps = acc_pool()
  let rng = ob_rng()
  let g = qgram_bitwidth(rng, n, bits)
  let cb = Cost::new()
  let base = qldlt_gauss(g, cb)
  let cf = Cost::new()
  let (ok, used) = match (base, qldlt_minors_crt(g, ps, cf)) {
    (Some((_, db)), Some(w)) => {
      let mut s = w.qmspd
      let mut pr = Q::one()
      for i in 0..<n {
        if !db[i].eq(w.qmd[i]) {
          s = false
        }
        pr = pr.mul(db[i])
      }
      if !pr.eq(w.qmdet) {
        s = false
      }
      (s, w.qmused)
    }
    _ => (false, 0)
  }
  {
    accode: "L-08′",
    acn: n,
    acbits: bits,
    acbase: cb.wmul,
    acfast: cf.wmul,
    acmid: cb.maxbits,
    acnu: n,
    ack: used,
    acok: ok,
  }
}

///|
/// L-05′（秩與樞軸之模篩 + 夾擠憑證）之一格，方陣滿秩。
pub fn acc_cell_l05p(n : Int, bits : Int) -> AccCell {
  let ps = acc_pool()
  let rng = ob_rng()
  let a = qmat_bitwidth(rng, n, n, bits)
  let cb = Cost::new()
  let (_, rk, pv) = qrref_gauss(a, cb)
  let cf = Cost::new()
  let rc = qrank_modp(a, ps, 3, cf)
  let ok = rc.rcrank == rk &&
    rc.rclow &&
    rc.rcup &&
    rc.rcpiv.length() == pv.length()
  {
    accode: "L-05′",
    acn: n,
    acbits: bits,
    acbase: cb.wmul,
    acfast: cf.wmul,
    acmid: cb.maxbits,
    acnu: 1,
    ack: rc.rcused,
    acok: ok,
  }
}

///|
/// L-05′ 之秩虧長方形一格：m×m 矩陣，秩為 r。
pub fn acc_cell_l05p_def(m : Int, r : Int, bits : Int) -> AccCell {
  let ps = acc_pool()
  let rng = ob_rng()
  let b1 = qmat_bitwidth(rng, m, r, bits)
  let b2 = qmat_bitwidth(rng, r, m, bits)
  let a = b1.times(b2)
  let cb = Cost::new()
  let (_, rk, pv) = qrref_gauss(a, cb)
  let cf = Cost::new()
  let rc = qrank_modp(a, ps, 3, cf)
  let ok = rc.rcrank == rk &&
    rc.rclow &&
    rc.rcup &&
    rc.rcpiv.length() == pv.length()
  {
    accode: "L-05′虧",
    acn: m,
    acbits: bits,
    acbase: cb.wmul,
    acfast: cf.wmul,
    acmid: cb.maxbits,
    acnu: 1,
    ack: rc.rcused,
    acok: ok,
  }
}

///|
/// 「先驗 Hadamard 界、一次重建」與「逐素數穩定判定」之對照（一格）。
/// 回傳 (舊版字乘, 新版字乘, 兩版輸出相同?)。
pub fn acc_apriori_cell(n : Int, bits : Int) -> (Int64, Int64, Bool) {
  let ps = acc_pool()
  let rng = ob_rng()
  let g = qgram_bitwidth(rng, n, bits)
  let c1 = Cost::new()
  let old = qldlt_crt(g, ps, c1)
  let c2 = Cost::new()
  let neu = qldlt_crt_ap(g, ps, c2)
  let same = match (old, neu) {
    (Some(o), Some(w)) => o.lmat.equals(w.lmat) && o.certified && w.certified
    _ => false
  }
  (c1.wmul, c2.wmul, same)
}

///|
/// 義務用之小網格。
pub fn acc_grid_small() -> Array[(Int, Int)] {
  [(3, 8), (5, 8), (3, 16), (5, 16)]
}

///|
/// 反例網格掃描：L-05 與 L-08 各跑小網格。
/// 回傳 (格數, 全部正確數, L-05 最大比值, L-08 最大比值, 贏的格數)。
pub fn acc_scan_counter() -> (Int, Int, Double, Double, Int) {
  let mut tot = 0
  let mut ok = 0
  let mut g5 = 0.0
  let mut g8 = 0.0
  let mut win = 0
  for s in acc_grid_small() {
    for cell in [acc_cell_l05(s.0, s.1), acc_cell_l08(s.0, s.1)] {
      tot = tot + 1
      if cell.acok {
        ok = ok + 1
      }
      let g = cell.gain()
      if g > 1.0 {
        win = win + 1
      }
      if cell.accode == "L-05" && g > g5 {
        g5 = g
      }
      if cell.accode == "L-08" && g > g8 {
        g8 = g
      }
    }
  }
  (tot, ok, g5, g8, win)
}

///|
/// ν 是主因子之直接證據：同一個問題、同一組素數，只改「重建幾個數」。
/// 回傳 (ν_舊, ν_新, 字乘_舊, 字乘_新, 增益比)。
pub fn acc_nu_evidence(n : Int, bits : Int) -> (Int, Int, Int64, Int64, Double) {
  let a = acc_cell_l08(n, bits)
  let b = acc_cell_l08p(n, bits)
  (
    a.acnu,
    b.acnu,
    a.acfast,
    b.acfast,
    a.acfast.to_double() / b.acfast.to_double(),
  )
}

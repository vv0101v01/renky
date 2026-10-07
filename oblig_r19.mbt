///|
/// # 第十九輪義務自證：N-90
///
/// 有限維希爾伯特空間的張量積 × 循環算子 × 伴隨映射 ×
/// 雙向快速傅立葉變換 × 線性性質 × 卷積。

///|
/// 【N-90】張量積上的雙向快速傅立葉變換：線性、卷積、伴隨。
pub fn ob_n90() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let mut inst = 0

  // ------------------------------------------------------------------
  // A. ℚ(i) 軌：張量積上的雙向變換、線性、卷積、伴隨
  //    m, n ∈ {2,4} ⇒ 維數 4、8、16 —— 全部只用 ω = i
  // ------------------------------------------------------------------
  let pairs = [(2, 2), (2, 4), (4, 2), (4, 4)]
  let mut np = 0
  let mut abi = 0
  let mut alin = 0
  let mut aconv = 0
  let mut acaught = 0
  let mut acirc = 0
  let mut adiag = 0
  let mut ahat = 0
  let mut aadj = 0
  let mut aadjw = 0
  let mut akeep = 0
  let mut dmax = 0
  for mn in pairs {
    let m = mn.0
    let n = mn.1
    match (cpx_dft(m), cpx_dft(n)) {
      (Some(fm), Some(fn_)) => {
        np = np + 1
        let d = m * n
        if d > dmax {
          dmax = d
        }
        inst = inst + 8
        let rc = () => Cpx::mk(qr(rng), qr(rng))
        let x : Array[Cpx[Q]] = Array::makei(d, _ => rc())
        let y : Array[Cpx[Q]] = Array::makei(d, _ => rc())
        // (1) 雙向：F⁻¹F = FF⁻¹ = I，兩個方向都要驗
        let r1 = tidft(fm, fn_, tdft(fm, fn_, x))
        let r2 = tdft(fm, fn_, tidft(fm, fn_, x))
        let mut bi = true
        for i in 0..<d {
          if !Scalar::s_eq(r1[i], x[i]) || !Scalar::s_eq(r2[i], x[i]) {
            bi = false
          }
        }
        if bi {
          abi = abi + 1
        }
        // (2) 線性：F(αx + βy) = αF(x) + βF(y)
        let al = rc()
        let be = rc()
        let fx = tdft(fm, fn_, x)
        let fy = tdft(fm, fn_, y)
        let comb : Array[Cpx[Q]] = Array::makei(d, i => {
          Scalar::s_add(Scalar::s_mul(al, x[i]), Scalar::s_mul(be, y[i]))
        })
        let fl = tdft(fm, fn_, comb)
        let mut lin = true
        for i in 0..<d {
          let w = Scalar::s_add(
            Scalar::s_mul(al, fx[i]),
            Scalar::s_mul(be, fy[i]),
          )
          if !Scalar::s_eq(fl[i], w) {
            lin = false
          }
        }
        // 逆變換亦線性
        let gx = tidft(fm, fn_, x)
        let gy = tidft(fm, fn_, y)
        let gl = tidft(fm, fn_, comb)
        for i in 0..<d {
          let w = Scalar::s_add(
            Scalar::s_mul(al, gx[i]),
            Scalar::s_mul(be, gy[i]),
          )
          if !Scalar::s_eq(gl[i], w) {
            lin = false
          }
        }
        if lin {
          alin = alin + 1
        }
        // (3) 卷積定理：F(a ⊛ b) = F(a) ⊙ F(b)
        let pp = hadamard_vec(fx, fy)
        let cv = tdft(fm, fn_, conv2(x, y, m, n))
        let mut cok = true
        for i in 0..<d {
          if !Scalar::s_eq(cv[i], pp[i]) {
            cok = false
          }
        }
        if cok {
          aconv = aconv + 1
        }
        // 兩側對照：改用**非循環**（線性截斷）卷積，定理必須失效
        let cvl = tdft(fm, fn_, conv2_linear(x, y, m, n))
        let mut caught = false
        for i in 0..<d {
          if !Scalar::s_eq(cvl[i], pp[i]) {
            caught = true
          }
        }
        if caught {
          acaught = acaught + 1
        }
        // (4) 二維循環算子：C(s)·x = s ⊛ x
        let s : Array[Cpx[Q]] = Array::makei(d, _ => rc())
        let cs : Mat[Cpx[Q]] = circ2_mat(s, m, n)
        let lhs = cs.apply(x)
        let rhs = conv2(s, x, m, n)
        let mut cc = true
        for i in 0..<d {
          if !Scalar::s_eq(lhs[i], rhs[i]) {
            cc = false
          }
        }
        if cc {
          acirc = acirc + 1
        }
        // (5) Φ(C) = (1/d)F*CF 對角，且對角元為**共軛核**變換 F*s
        let f = mkron(fm, fn_)
        let iv : Cpx[Q] = Cpx::of_real(Q::frac(1, d))
        let phi = f.adjointm().times(cs).times(f).scale(iv)
        if is_diagonal(phi) {
          adiag = adiag + 1
        }
        let sh = tdft_conj(fm, fn_, s)
        let mut hok = true
        for i in 0..<d {
          if !Scalar::s_eq(phi.at(i, i), sh[i]) {
            hok = false
          }
        }
        if hok {
          ahat = ahat + 1
        }
        // (6) 伴隨在張量積上分解 (A⊗B)* = A*⊗B*
        let aa : Mat[Cpx[Q]] = Mat::build(m, m, (_, _) => rc())
        let bb : Mat[Cpx[Q]] = Mat::build(n, n, (_, _) => rc())
        if mkron(aa, bb).adjointm().equals(mkron(aa.adjointm(), bb.adjointm())) {
          aadj = aadj + 1
        }
        // 對照：第二因子只轉置不共軛
        if !mkron(aa, bb)
          .adjointm()
          .equals(mkron(aa.adjointm(), bb.transpose())) {
          aadjw = aadjw + 1
        }
        // (7) Φ 保伴隨
        if f
          .adjointm()
          .times(cs.adjointm())
          .times(f)
          .scale(iv)
          .equals(phi.adjointm()) {
          akeep = akeep + 1
        }
      }
      _ => ok = false
    }
  }
  if np != 4 || dmax != 16 {
    ok = false
  }
  if abi != np ||
    alin != np ||
    aconv != np ||
    acaught != np ||
    acirc != np ||
    adiag != np ||
    ahat != np ||
    aadj != np ||
    aadjw != np ||
    akeep != np {
    ok = false
  }

  // ------------------------------------------------------------------
  // B. 𝔽p 軌：radix-2 快速變換與其成本
  // ------------------------------------------------------------------
  let mut nf = 0
  let mut fsame = 0
  let ratios : Array[Double] = []
  for k in [2, 3, 4, 5, 6, 7] {
    let n = 1 << k
    match fp_ctx_for(n) {
      None => ok = false
      Some(ctx) =>
        match fp_root_of_unity(n, ctx) {
          None => ok = false
          Some(w) => {
            nf = nf + 1
            inst = inst + 1
            let x : Array[Int64] = Array::makei(n, _ => {
              rng.next_below(1000).to_int64()
            })
            let (fa, bf) = fft_radix2(x, w, ctx)
            let (fb, mul) = dft_direct_fp(x, w, ctx)
            let mut same = true
            for i in 0..<n {
              if fa[i] != fb[i] {
                same = false
              }
            }
            if same {
              fsame = fsame + 1
            }
            ratios.push(mul.to_double() / maxd(1.0, bf.to_double()))
          }
        }
    }
  }
  if nf != 6 || fsame != nf {
    ok = false
  }
  // 比值須隨 n 單調上升（快速演算法之定義性質）
  let mut mono = true
  for i in 1..<ratios.length() {
    if ratios[i] <= ratios[i - 1] {
      mono = false
    }
  }
  if !mono || ratios[ratios.length() - 1] < 30.0 {
    ok = false
  }

  // ------------------------------------------------------------------
  // C. Good–Thomas：互質時 F_{mn} 為 F_m ⊗ F_n 之置換共軛
  // ------------------------------------------------------------------
  let mut ng = 0
  let mut gok = 0
  let mut gneq = 0
  let mut nco = 0
  for mn in [(2, 3), (3, 4), (3, 5), (4, 5), (5, 6)] {
    let m = mn.0
    let n = mn.1
    let d = m * n
    match fp_ctx_for(d) {
      None => ok = false
      Some(ctx) =>
        match fp_root_of_unity(d, ctx) {
          None => ok = false
          Some(wd) => {
            ng = ng + 1
            inst = inst + 2
            let fm = fp_dft(m, ctx.pow(wd, n.to_int64()), ctx)
            let fnn = fp_dft(n, ctx.pow(wd, m.to_int64()), ctx)
            let fd = fp_dft(d, wd, ctx)
            let (im, om) = good_thomas_maps(m, n)
            let mut g1 = true
            let mut g2 = true
            for t in 0..<d {
              for u in 0..<d {
                let tens = ctx.mul(fm.get(t / n, u / n), fnn.get(t % n, u % n))
                if fd.get(im[t], om[u]) != tens {
                  g1 = false
                }
                if fd.get(t, u) != tens {
                  g2 = false
                }
              }
            }
            if g1 {
              gok = gok + 1
            }
            // 未置換即相等者應為 0 —— 這是 T-2 的兩側對照
            if !g2 {
              gneq = gneq + 1
            }
          }
        }
    }
  }
  // 不互質者必須回報無 Good–Thomas
  for mn in [(2, 2), (2, 4), (4, 6)] {
    let (im, _) = good_thomas_maps(mn.0, mn.1)
    if im.length() == 0 {
      nco = nco + 1
    }
  }
  if ng != 5 || gok != ng || gneq != ng || nco != 3 {
    ok = false
  }
  mk_check(
    "N-90 張量積上的雙向快速傅立葉變換：線性、卷積、伴隨",
    ok,
    inst,
    "N-89 把傅里葉級數、循環算子、伴隨與對角矩陣空間接成一條鏈，但只做一維。本條把底下的空間換成**張量積** ℓ²(ℤ/m) ⊗ ℓ²(ℤ/n) ≅ ℓ²(ℤ/m × ℤ/n)，補上四件在一維看不出來的事。**(1) 張量積的單位根只需要因子的單位根**：F_m ⊗ F_n 只用到 ω_m 與 ω_n，**不需要 mn 次單位根**。這不是技術細節 —— ℚ(i) 的單位根群恰為 {±1,±i}，N-89 因此卡在 n ≤ 4，而 4⊗4 的張量 DFT 作用在 **16 維**空間上用到的仍只有 i。維數上去了，需要的體沒變。實測 " +
    np.to_string() +
    " 組 (m,n) ∈ {2,4}²，最大維數 " +
    dmax.to_string() +
    "。**(2) 雙向**：F⁻¹F = FF⁻¹ = I 兩個方向各驗（只驗一邊不能排除 F 不是滿射），" +
    abi.to_string() +
    "／" +
    np.to_string() +
    "。**(3) 線性**：F(αx+βy) = αF(x)+βF(y)，正變換與逆變換各驗 " +
    alin.to_string() +
    " —— 線性是「變換」這個詞的全部內容，卻最少被驗，因為它看起來太顯然；任何在變換裡做了與輸入相關的分支都會破壞它。**(4) 二維卷積定理** F(a⊛b) = F(a)⊙F(b) " +
    aconv.to_string() +
    "，兩側對照改用非循環（線性截斷）卷積，定理全數失效 " +
    acaught.to_string() +
    "。**(5) 二維循環算子**：C(s)·x = s⊛x " +
    acirc.to_string() +
    "，Φ(C) = (1/d)F*CF 對角 " +
    adiag.to_string() +
    "，對角元 " +
    ahat.to_string() +
    "。**對角元用的是共軛核 F*s，不是 Fs** —— 推導 (C(s)F)[i][k] = ω^{ik}Σ_t s[t]ω^{−tk} 即見；而 **n = 2 分辨不出這件事**（ω₂ = ω₂⁻¹ = −1），本條第一版正是在 2⊗2 通過、在 2⊗4 與 4⊗4 失敗才發現寫反，與「ℚ 的共軛是恆等所以剛好對」是同一類陷阱：最小的例子往往正好是看不出區別的那個。**(6) 伴隨分解** (A⊗B)* = A*⊗B* " +
    aadj.to_string() +
    "，第二因子只轉置不共軛者全數被抓 " +
    aadjw.to_string() +
    "；Φ 保伴隨 " +
    akeep.to_string() +
    "。**(7) 快速**：𝔽p 上 radix-2 Cooley–Tukey 在 n = 4…128 共 " +
    nf.to_string() +
    " 個尺寸上與直接矩陣求值逐元相同 " +
    fsame.to_string() +
    "，蝶形次數對直接乘法次數之比值 ×" +
    fmt_d(ratios[0], 2) +
    " → ×" +
    fmt_d(ratios[ratios.length() - 1], 2) +
    " 單調上升（單調性與末項 ≥ 30 皆為判準）。而**張量結構本身就是快速演算法**：以 K-1 計算 (F_m⊗F_n)x 不物化 mn 階矩陣，Θ(m²n²) → Θ(mn(m+n))，16⊗16 時 65,536 → 8,192（×8）。Cooley–Tukey 把長度 mn 的變換拆成 m 個長度 n 加 n 個長度 m，而那個拆法就是「把 ℤ/mn 看成 ℤ/m × ℤ/n」—— 快速不是技巧，是張量結構的直接後果。**(8) Good–Thomas**：gcd(m,n) = 1 時 F_{mn} 為 F_m⊗F_n 之置換共軛，需 ω_m = ω_d^n、ω_n = ω_d^m，輸入用 CRT 重建映射、輸出用 Ruritanian 映射（**兩個映射不同**，用同一個去排列列與行會得到看起來很像但不相等的矩陣）。5 組互質 " +
    gok.to_string() +
    "／" +
    ng.to_string() +
    " 置換後相符，且**未置換時全部不相等** " +
    gneq.to_string() +
    " —— 這是 T-2 的兩側對照：把「多維 DFT」與「長度 mn 的一維 DFT」當成同一件事是本題最常見的錯。不互質之 3 組如實回報無 Good–Thomas " +
    nco.to_string() +
    "。",
  )
}

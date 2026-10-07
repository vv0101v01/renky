///|
/// # 第十七輪義務自證：N-89
///
/// 傅里葉級數 × 循環算子 × 伴隨映射 × 對角矩陣空間。

///|
/// 【N-89】傅里葉級數、循環算子、伴隨映射與對角矩陣空間之合流。
pub fn ob_n89() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let mut inst = 0

  // ------------------------------------------------------------------
  // A. ℚ 軌（任意 n）：卷積定理與伴隨符號 —— 兩者都不需要單位根
  // ------------------------------------------------------------------
  let mut nq = 0
  let mut aconv = 0
  let mut aadj = 0
  let mut acomm = 0
  for n in [2, 3, 4, 5, 6, 7, 8] {
    for _t in 0..<3 {
      nq = nq + 1
      inst = inst + 3
      let a : Array[Q] = Array::makei(n, _ => qr(rng))
      let b : Array[Q] = Array::makei(n, _ => qr(rng))
      let ca : Mat[Q] = circ_mat(a)
      let cb : Mat[Q] = circ_mat(b)
      // 定理 FS-2：C(a)C(b) = C(a ⊛ b)
      if ca.times(cb).equals(circ_mat(cyc_conv(a, b))) {
        aconv = aconv + 1
      }
      // 定理 FS-3：C(a)* = C(aᴿ)
      if ca.adjointm().equals(circ_mat(symbol_adj(a))) {
        aadj = aadj + 1
      }
      // 推論：Circ(n) 交換
      if ca.times(cb).equals(cb.times(ca)) {
        acomm = acomm + 1
      }
    }
  }
  if nq != 21 || aconv != nq || aadj != nq || acomm != nq {
    ok = false
  }

  // ------------------------------------------------------------------
  // B. ℚ(i) 軌（n ∈ {2,4}）：完整的 Φ —— 對角化、同態、保伴隨、等距
  //    以及 ℓ²(ℤ/n) 上的特徵正交性與 Parseval
  // ------------------------------------------------------------------
  let mut nc = 0
  let mut bunit = 0
  let mut bdiag = 0
  let mut bhom = 0
  let mut badj = 0
  let mut biso = 0
  let mut biso_bad = 0
  let mut borth = 0
  let mut bpars = 0
  let mut bbasis = 0
  for n in [2, 4] {
    match cpx_dft(n) {
      None => ok = false
      Some(f) => {
        nc = nc + 1
        inst = inst + 8
        let zero : Cpx[Q] = Cpx::of_real(Q::zero())
        let nn : Cpx[Q] = Cpx::of_real(Q::of_int(n))
        let id : Mat[Cpx[Q]] = Mat::ident(n)
        // (a) F*F = nI
        if f.adjointm().times(f).equals(id.scale(nn)) {
          bunit = bunit + 1
        }
        let a : Array[Cpx[Q]] = Array::makei(n, _ => Cpx::mk(qr(rng), qr(rng)))
        let b : Array[Cpx[Q]] = Array::makei(n, _ => Cpx::mk(qr(rng), qr(rng)))
        let ca : Mat[Cpx[Q]] = circ_mat(a)
        let cb : Mat[Cpx[Q]] = circ_mat(b)
        let pa = cpx_phi(f, ca)
        let pb = cpx_phi(f, cb)
        // (c) 像落在 Diag(n)
        if is_diagonal(pa) && is_diagonal(pb) {
          bdiag = bdiag + 1
        }
        // (d) 代數同態
        if cpx_phi(f, ca.times(cb)).equals(pa.times(pb)) {
          bhom = bhom + 1
        }
        // (e) 保伴隨 Φ(C*) = Φ(C)*
        if cpx_phi(f, ca.adjointm()).equals(pa.adjointm()) {
          badj = badj + 1
        }
        // (f) 嚴格等距；同時驗「1/n 尺度」那個**錯版**必須不成立
        let lhs = frob_inner(pa, pb)
        let rhs = frob_inner(ca, cb)
        if Scalar::s_eq(lhs, rhs) {
          biso = biso + 1
        }
        if !Scalar::s_eq(lhs, Scalar::s_mul(Cpx::of_real(Q::frac(1, n)), rhs)) {
          biso_bad = biso_bad + 1
        }
        // 定理 FS-1：特徵 χ_k = F 之第 k 行，⟨χ_k,χ_l⟩ = n·δ_{kl}
        let chi : Array[Array[Cpx[Q]]] = Array::makei(n, k => {
          Array::makei(n, j => f.at(j, k))
        })
        let ip = (x : Array[Cpx[Q]], y : Array[Cpx[Q]]) => {
          let mut acc : Cpx[Q] = zero
          for t in 0..<n {
            acc = Scalar::s_add(acc, Scalar::s_mul(x[t], Scalar::s_conj(y[t])))
          }
          acc
        }
        let mut orth = true
        for k in 0..<n {
          for l in 0..<n {
            let want = if k == l { nn } else { zero }
            if !Scalar::s_eq(ip(chi[k], chi[l]), want) {
              orth = false
            }
          }
        }
        if orth {
          borth = borth + 1
        }
        // Parseval：Σ_k |f̂(k)|² = n·Σ_j |f(j)|²
        let fv : Array[Cpx[Q]] = Array::makei(n, _ => Cpx::mk(qr(rng), qr(rng)))
        let mut pl = Q::zero()
        for k in 0..<n {
          pl = pl.add(Cpx::norm2(ip(fv, chi[k])))
        }
        let mut pr = Q::zero()
        for j in 0..<n {
          pr = pr.add(Cpx::norm2(fv[j]))
        }
        if pl.eq(pr.mul(Q::of_int(n))) {
          bpars = bpars + 1
        }
        // Φ(S^k) 構成 Diag(n) 之基底：把 n 條對角線排成矩陣，須可逆
        let sh : Mat[Cpx[Q]] = cyc_shift(n)
        let rows : Array[Mat[Cpx[Q]]] = []
        let mut p : Mat[Cpx[Q]] = Mat::ident(n)
        for _k in 0..<n {
          rows.push(cpx_phi(f, p))
          p = p.times(sh)
        }
        let dm : Mat[Cpx[Q]] = Mat::build(n, n, (k, j) => rows[k].at(j, j))
        if !Scalar::s_is_zero(mdet(dm)) {
          bbasis = bbasis + 1
        }
      }
    }
  }
  if nc != 2 {
    ok = false
  }
  if bunit != nc ||
    bdiag != nc ||
    bhom != nc ||
    badj != nc ||
    biso != nc ||
    biso_bad != nc ||
    borth != nc ||
    bpars != nc ||
    bbasis != nc {
    ok = false
  }

  // ------------------------------------------------------------------
  // C. 𝔽p 軌（一般 n）：ℚ(i) 只有 n ∈ {1,2,4}，一般 n 換係數體
  // ------------------------------------------------------------------
  let mut nfp = 0
  let mut cunit = 0
  let mut cdiag = 0
  for n in [2, 3, 4, 5, 6, 7, 8, 9, 10, 12] {
    match fp_ctx_for(n) {
      None => ok = false
      Some(ctx) =>
        match fp_root_of_unity(n, ctx) {
          None => ok = false
          Some(w) => {
            nfp = nfp + 1
            inst = inst + 2
            let f = fp_dft(n, w, ctx)
            let fi = fp_idft(n, w, ctx)
            // F(ω)·F(ω⁻¹) = n·I
            let ff = fp_matmul(f, fi, ctx)
            let mut un = true
            for i in 0..<n {
              for j in 0..<n {
                let want = if i == j {
                  normmod(n.to_int64(), ctx.pmod)
                } else {
                  0L
                }
                if ff.get(i, j) != want {
                  un = false
                }
              }
            }
            if un {
              cunit = cunit + 1
            }
            // 循環矩陣被對角化
            let av : Array[Int64] = Array::makei(n, _ => {
              rng.next_below(1000).to_int64()
            })
            let d = fp_matmul(fp_matmul(fi, fp_circ(av, ctx), ctx), f, ctx)
            let mut dg = true
            for i in 0..<n {
              for j in 0..<n {
                if i != j && d.get(i, j) != 0L {
                  dg = false
                }
              }
            }
            if dg {
              cdiag = cdiag + 1
            }
          }
        }
    }
  }
  if nfp != 10 || cunit != nfp || cdiag != nfp {
    ok = false
  }

  // ------------------------------------------------------------------
  // D. 兩側對照
  // ------------------------------------------------------------------
  // (1) 非循環矩陣經 Φ 不是對角的 —— 擋掉「DFT 能對角化任何矩陣」
  let mut d1n = 0
  let mut d1c = 0
  for n in [2, 4] {
    match cpx_dft(n) {
      None => ()
      Some(f) =>
        for _t in 0..<6 {
          let m : Mat[Cpx[Q]] = Mat::build(n, n, (_, _) => {
            Cpx::mk(qr(rng), qr(rng))
          })
          if !is_circulant(m) {
            d1n = d1n + 1
            inst = inst + 1
            if !is_diagonal(cpx_phi(f, m)) {
              d1c = d1c + 1
            }
          }
        }
    }
  }
  if d1n == 0 || d1c != d1n {
    ok = false
  }
  // (2) 伴隨符號漏掉指標反轉（aᵂ[k] = conj(a[k])）。
  //     盲點可預測：兩式相等 ⟺ a[(−k) mod n] = a[k]（符號回文）。
  //     隨機符號幾乎不回文，故另外餵入刻意回文的符號，確保對照兩端都出現。
  let mut d2n = 0
  let mut d2caught = 0
  let mut d2blind = 0
  let mut d2pred = 0
  for n in [3, 4, 5, 6, 7, 8] {
    for t in 0..<8 {
      d2n = d2n + 1
      inst = inst + 1
      // t < 2 時造回文符號（盲端），其餘隨機（可辨端）
      let a : Array[Q] = if t < 2 {
        let h : Array[Q] = Array::makei(n, _ => qr(rng))
        Array::makei(n, k => if k <= n - k % n { h[k] } else { h[(n - k) % n] })
      } else {
        Array::makei(n, _ => qr(rng))
      }
      let right : Mat[Q] = circ_mat(symbol_adj(a))
      let wrong : Mat[Q] = circ_mat(symbol_adj_wrong(a))
      let caught = !right.equals(wrong)
      if caught {
        d2caught = d2caught + 1
      } else {
        d2blind = d2blind + 1
      }
      let mut pal = true
      for k in 0..<n {
        if !a[(n - k) % n].eq(a[k]) {
          pal = false
        }
      }
      if caught == !pal {
        d2pred = d2pred + 1
      }
    }
  }
  if d2pred != d2n || d2caught == 0 || d2blind == 0 {
    ok = false
  }
  mk_check(
    "N-89 傅里葉級數 × 循環算子 × 伴隨映射 × 對角矩陣空間",
    ok,
    inst,
    "把四個本來分開的物件接成一條鏈：ℓ²(ℤ/n) 上的傅里葉級數、循環移位算子 S 與循環代數 Circ(n)、伴隨映射 C ↦ C*、以及對角矩陣空間 Diag(n)。核心是 Φ(C) = (1/n)·F*CF 同時為**代數同構、保伴隨、嚴格等距**，故 Circ(n) 與 Diag(n) 作為 n 維內積空間同構。本庫既有的 H-19 已在**數值軌**驗過「DFT 么正、循環矩陣可對角化」；本條不重複那件事，而是補上內積空間層、伴隨層，並且**全程精確算術**。**ℚ 軌（n = 2…8，" +
    nq.to_string() +
    " 組）**：卷積定理 C(a)C(b) = C(a⊛b) " +
    aconv.to_string() +
    "、伴隨符號 C(a)* = C(aᴿ) " +
    aadj.to_string() +
    "、Circ 交換性 " +
    acomm.to_string() +
    " —— 這三條**不需要單位根**，故一般 n 在 ℚ 上就能精確驗。**ℚ(i) 軌（n ∈ {2,4}）**：F*F = nI " +
    bunit.to_string() +
    "、Φ 之像落在 Diag(n) " +
    bdiag.to_string() +
    "、代數同態 " +
    bhom.to_string() +
    "、保伴隨 Φ(C*) = Φ(C)* " +
    badj.to_string() +
    "、嚴格等距 ⟨Φ(A),Φ(B)⟩ = ⟨A,B⟩ " +
    biso.to_string() +
    "、特徵正交 ⟨χ_k,χ_l⟩ = n·δ " +
    borth.to_string() +
    "、Parseval Σ|f̂|² = n·Σ|f|² " +
    bpars.to_string() +
    "、Φ(S^k) 構成 Diag(n) 之基底（n 條對角線排成之矩陣可逆）" +
    bbasis.to_string() +
    "，各 ／" +
    nc.to_string() +
    "。**ℚ(i) 只有 n ∈ {1,2,4}**，因為 ℚ(i) 的單位根群恰為 {±1,±i}；一般 n 需要分圓體 ℚ(ζ_n)，本庫沒有，故**換係數體**而不是假裝覆蓋：**𝔽p 軌（n = 2…12 共 " +
    nfp.to_string() +
    " 個，取 p ≡ 1 mod n 之原根冪）**驗 F(ω)F(ω⁻¹) = nI " +
    cunit.to_string() +
    "、循環矩陣被對角化 " +
    cdiag.to_string() +
    "。**兩側對照**：(1) 非循環矩陣經 Φ 必不對角，" +
    d1n.to_string() +
    " 個全數抓到 " +
    d1c.to_string() +
    " —— 擋掉「DFT 能對角化任何矩陣」這個常見誤解；(2) 伴隨符號漏掉指標反轉（寫成 conj(a[k])）在 " +
    d2n.to_string() +
    " 組中抓到 " +
    d2caught.to_string() +
    "、分辨不出 " +
    d2blind.to_string() +
    "，而**盲點可預測** —— 兩式相等 ⟺ 符號回文 a[(−k) mod n] = a[k]，預測與實測逐格相符 " +
    d2pred.to_string() +
    "；隨機符號幾乎不回文，故另行餵入刻意回文者，確保對照兩端都真的出現。另記一處算錯：定理 FS-4(f) 初稿寫成「等距差一個 1/n 尺度」，只算了一次 FF* = nI 而漏掉跡之循環性那一次；義務同時驗「無尺度」與「1/n 尺度」兩式，實測前者成立後者不成立（" +
    biso_bad.to_string() +
    "／" +
    nc.to_string() +
    " 否決），錯的那一版因此留在紀錄裡。",
  )
}

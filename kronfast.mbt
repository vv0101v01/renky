///|
/// # Kronecker 結構之免物化運算（N-86…N-88 之基礎）
///
/// ## 動機
///
/// 在 45 × 45 的張量配對表裡，A ⊗ B 的階數可達 144，而所有需要它的
/// 運算 —— 內積、雙線性型、矩陣向量積 —— 都不需要那個 144 × 144 的矩陣
/// 真的存在。只要保持 Kronecker 結構，成本從 Θ(n_A²n_B²) 降到
/// Θ(n_A n_B (n_A + n_B))。
///
/// ```text
///   n_A = n_B = 12   物化後 20,736   保持結構 3,456    ×6.0
///   n_A = n_B = 20   物化後 160,000  保持結構 16,000   ×10.0
/// ```
///
/// 這是本庫第七輪就立下的那條原則的又一次應用：
/// **加速的單位是呼叫端需要的那個量，不是整個矩陣。**

///|
/// (A ⊗ B)·x，不物化 A ⊗ B。
///
/// ## 定理 K-1
///
/// 以列優先把 x 視為 n_A × n_B 矩陣 X（X[i][j] = x[i·n_B + j]），則
///
/// ```text
///   ((A ⊗ B)x)[i·n_B + l] = Σ_k Σ_j A[i][k]·B[l][j]·X[k][j]
///                         = (A · X · Bᵀ)[i][l]
/// ```
///
/// 證明：(A⊗B)[i·n_B+l][k·n_B+j] = A[i][k]·B[l][j]，代入矩陣向量積之
/// 定義並按 (k,j) 分組即得。∎
///
/// 成本：先算 X·Bᵀ（Θ(n_A n_B²)）再左乘 A（Θ(n_A² n_B)），
/// 合計 Θ(n_A n_B (n_A + n_B))；物化法為 Θ(n_A² n_B²)。
pub fn kron_matvec_q(a : Mat[Q], b : Mat[Q], x : Array[Q]) -> Array[Q] {
  let na = a.mrows
  let nb = b.mrows
  // T = X · Bᵀ ：T[k][l] = Σ_j X[k][j]·B[l][j]
  let t : Array[Array[Q]] = Array::makei(na, _ => {
    Array::makei(nb, _ => Q::zero())
  })
  for k in 0..<na {
    for l in 0..<nb {
      let mut acc = Q::zero()
      for j in 0..<nb {
        let xv = x[k * nb + j]
        if !xv.is_zero() {
          acc = acc.add(xv.mul(b.at(l, j)))
        }
      }
      t[k][l] = acc
    }
  }
  // out[i·nb + l] = Σ_k A[i][k]·T[k][l]
  let out : Array[Q] = Array::makei(na * nb, _ => Q::zero())
  for i in 0..<na {
    for k in 0..<na {
      let aik = a.at(i, k)
      if !aik.is_zero() {
        for l in 0..<nb {
          out[i * nb + l] = out[i * nb + l].add(aik.mul(t[k][l]))
        }
      }
    }
  }
  out
}

///|
/// xᵀ(A ⊗ B)y，不物化 A ⊗ B。
///
/// 由定理 K-1 直接得：先算 (A⊗B)y 再與 x 內積。
pub fn kron_bilinear(a : Mat[Q], b : Mat[Q], x : Array[Q], y : Array[Q]) -> Q {
  let v = kron_matvec_q(a, b, y)
  let mut acc = Q::zero()
  for i in 0..<v.length() {
    acc = acc.add(x[i].mul(v[i]))
  }
  acc
}

///|
/// 分塊對角 (A ⊕ B) 之雙線性型，不物化。
pub fn bdiag_bilinear(a : Mat[Q], b : Mat[Q], x : Array[Q], y : Array[Q]) -> Q {
  let na = a.mrows
  let nb = b.mrows
  let mut acc = Q::zero()
  for i in 0..<na {
    for j in 0..<na {
      acc = acc.add(x[i].mul(a.at(i, j)).mul(y[j]))
    }
  }
  for i in 0..<nb {
    for j in 0..<nb {
      acc = acc.add(x[na + i].mul(b.at(i, j)).mul(y[na + j]))
    }
  }
  acc
}

// ---------------------------------------------------------------------------
//  Kronecker 之 LDLᵀ 證書
// ---------------------------------------------------------------------------

///|
/// ## 定理 K-2（Kronecker 積之 LDLᵀ 為因子 LDLᵀ 之 Kronecker 積）
///
/// 設 A = L_A D_A L_Aᵀ、B = L_B D_B L_Bᵀ 為單位下三角 LDLᵀ 分解，則
///
/// ```text
///   A ⊗ B = (L_A ⊗ L_B)·(D_A ⊗ D_B)·(L_A ⊗ L_B)ᵀ
/// ```
///
/// 且 **L_A ⊗ L_B 仍為單位下三角**，故右式即 A ⊗ B 之 LDLᵀ 分解
/// （對稱正定矩陣之 LDLᵀ 唯一）。
///
/// 證明（下三角性）：(L_A⊗L_B)[i·n_B+j][k·n_B+l] = L_A[i][k]·L_B[j][l]，
/// 非零要求 i ≥ k 且 j ≥ l。若 i > k 則 i·n_B+j ≥ (k+1)·n_B > k·n_B+l
/// （因 l ≤ n_B−1）；若 i = k 則需 j ≥ l。兩情形皆有列指標 ≥ 行指標。
/// 對角元為 L_A[i][i]·L_B[j][j] = 1·1 = 1。
/// 主體等式由混合積 (A⊗B)(C⊗D) = (AC)⊗(BD) 連用兩次並配合
/// (L⊗M)ᵀ = Lᵀ⊗Mᵀ 即得。∎
///
/// ## 推論 K-3（正定之 Θ(n_A³ + n_B³) 判準，附構造性證書）
///
/// A ⊗ B 正定 ⟺ D_A ⊗ D_B 全正 ⟺ (D_A 全正 ∧ D_B 全正) 或
/// (D_A 全負 ∧ D_B 全負)。對稱正定之因子而言即「兩者皆正定」。
///
/// 與「譜為 {λᵢμⱼ} 故皆正」相比，本式給出的是一個**可以檢查的物件**
/// （L 與 D），不只是一個可以相信的理由。
///
/// 回傳 D_A ⊗ D_B（列優先：索引 i·n_B + j 對應 D_A[i]·D_B[j]）。
pub fn kron_ldlt_diag(da : Array[Q], db : Array[Q]) -> Array[Q] {
  let na = da.length()
  let nb = db.length()
  Array::makei(na * nb, u => da[u / nb].mul(db[u % nb]))
}

///|
/// 以 Kronecker LDLᵀ 證書驗證 xᵀ(A⊗B)y = xᵀ(L D Lᵀ)y，不物化任何 n_An_B 階矩陣。
///
/// 左式以定理 K-1 算；右式先算 u = (L_Aᵀ ⊗ L_Bᵀ)x、v = (L_Aᵀ ⊗ L_Bᵀ)y，
/// 再取 Σ_t D[t]·u[t]·v[t]。兩側皆 Θ(n_A n_B (n_A + n_B))。
pub fn kron_ldlt_check(
  a : Mat[Q],
  b : Mat[Q],
  la : Mat[Q],
  lb : Mat[Q],
  dd : Array[Q],
  x : Array[Q],
  y : Array[Q],
) -> Bool {
  let lhs = kron_bilinear(a, b, x, y)
  let u = kron_matvec_q(la.transpose(), lb.transpose(), x)
  let v = kron_matvec_q(la.transpose(), lb.transpose(), y)
  let mut rhs = Q::zero()
  for t in 0..<dd.length() {
    rhs = rhs.add(dd[t].mul(u[t]).mul(v[t]))
  }
  lhs.eq(rhs)
}

///|
/// L_A ⊗ L_B 是否為單位下三角（定理 K-2 之結構部分，逐元檢查）。
pub fn kron_unit_lower(la : Mat[Q], lb : Mat[Q]) -> Bool {
  let na = la.mrows
  let nb = lb.mrows
  for u in 0..<(na * nb) {
    for v in 0..<(na * nb) {
      let e = la.at(u / nb, v / nb).mul(lb.at(u % nb, v % nb))
      if u == v {
        if !e.eq(Q::one()) {
          return false
        }
      } else if u < v && !e.is_zero() {
        return false
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
//  模 p 之行列式對帳
// ---------------------------------------------------------------------------

///|
/// A ⊗ B 之模 p 行列式，直接在 Fp 上物化（Int64，無大數）後求值。
///
/// ## 為何可以物化
///
/// 本庫忌諱物化 n_An_B 階的 **ℚ** 矩陣，是因為 ℚ 元素帶 gcd 與大數；
/// 在 Fp 上每個元素是一個機器字，144² = 20,736 個 Int64 微不足道，
/// 而 Θ(n³) 的高斯消去全程不產生係數膨脹。
/// 故「大配對的行列式無法獨立對帳」只在 ℚ 軌成立，換軌即可。
pub fn kron_det_modp(a : Mat[Q], b : Mat[Q], ctx : FpCtx) -> Int64? {
  let fa = match fp_of_q(a, ctx) {
    Some(m) => m
    None => return None
  }
  let fb = match fp_of_q(b, ctx) {
    Some(m) => m
    None => return None
  }
  let nb = b.mrows
  let n = a.mrows * nb
  let m = FpMat::make(n, n)
  for u in 0..<n {
    for v in 0..<n {
      m.set(u, v, ctx.mul(fa.get(u / nb, v / nb), fb.get(u % nb, v % nb)))
    }
  }
  Some(fp_det_fast(m, ctx))
}

// ---------------------------------------------------------------------------
//  惰性張量空間
// ---------------------------------------------------------------------------

///|
/// 張量積空間（ℚ 軌），**不物化** G_P ⊗ G_Q。
///
/// ## 與既有兩版的關係
///
/// ```text
///   tensor_space(p,q)          對每個因子呼叫 gram_of_space（Θ(d³)），
///                              再物化 Kronecker 積（Θ(d_P²d_Q²)）
///   tensor_space_g(p,q,g1,g2)  省掉 gram_of_space，仍物化 Kronecker 積
///   tensor_space_lazy(...)     兩者都省；內積改以定理 K-1 現算，
///                              單次 Θ(d_P d_Q (d_P + d_Q))
/// ```
///
/// 這補上了本庫一個長年的不對稱：`direct_sum` 從一開始就是惰性的
/// （它不預先算 Gram），而 `tensor_space` 是急性的，兩個相鄰的建構子
/// 一急一惰，沒有任何註解說明為什麼。現在三者的內積都不需要
/// 先有一個 Gram 矩陣存在。
///
/// ## 定理 K-4（三版同值）
///
/// 對 g1 = gram_of_space(p)、g2 = gram_of_space(q)，三者回傳的空間
/// 維數相同、基底相同、且內積函數在所有輸入上取值相同。
/// 內積之相等即定理 K-1；其餘部分逐字相同。∎
///
/// 注意：本版僅適用於 ℚ 軌（`kron_bilinear` 不取共軛）。
/// 複數軌請續用 `tensor_space`。
pub fn tensor_space_lazy(
  p : IPSpace[Array[Q], Q],
  q : IPSpace[Array[Q], Q],
  g1 : Mat[Q],
  g2 : Mat[Q],
) -> IPSpace[Array[Q], Q] {
  let d1 = p.vs.dim
  let d2 = q.vs.dim
  let base : IPSpace[Array[Q], Q] = coord_ipspace(
    p.vs.vname + " ⊗ " + q.vs.vname,
    d1 * d2,
    None,
  )
  {
    vs: base.vs,
    ipname: "⟨x₁⊗x₂,y₁⊗y₂⟩ = ⟨x₁,y₁⟩⟨x₂,y₂⟩（保持 Kronecker 結構，不物化 Gram）",
    inner: (x, y) => kron_bilinear(g1, g2, x, y),
  }
}

///|
/// 分配律 P⊗(Q⊕R) ≅ (P⊗Q)⊕(P⊗R) 之逐元檢查，**兩側皆不物化**。
///
/// 左式 (P⊗M)[u][v] = P[u/d_M][v/d_M]·M[u%d_M][v%d_M]，其中 M = Q⊕R
/// 之元可由 (i,j) 直接判斷落在哪一塊；右式 blockdiag(P⊗Q, P⊗R)[σu][σv]
/// 同理。故每一元 O(1)，全式 Θ(d²) 而常數極小 —— 相較「先造三個矩陣
/// 再比」省去三趟 Θ(d²) 的配置與寫入。
pub fn distrib_elem_check(p : Mat[Q], q : Mat[Q], r : Mat[Q]) -> Bool {
  let dp = p.mrows
  let dq = q.mrows
  let dr = r.mrows
  let dm = dq + dr
  let d = dp * dm
  let npq = dp * dq
  // M = Q ⊕ R 之取元
  let mat = (i : Int, j : Int) => {
    if i < dq && j < dq {
      q.at(i, j)
    } else if i >= dq && j >= dq {
      r.at(i - dq, j - dq)
    } else {
      Q::zero()
    }
  }
  // σ：左式指標 → 右式指標
  let sg = f_distrib_sigma(dp, dq, dr)
  // 右式 blockdiag(P⊗Q, P⊗R) 之取元
  let rhs = (x : Int, y : Int) => {
    if x < npq && y < npq {
      p.at(x / dq, y / dq).mul(q.at(x % dq, y % dq))
    } else if x >= npq && y >= npq {
      let a = x - npq
      let b = y - npq
      p.at(a / dr, b / dr).mul(r.at(a % dr, b % dr))
    } else {
      Q::zero()
    }
  }
  for u in 0..<d {
    let su = sg(u)
    for v in 0..<d {
      if !p.at(u / dm, v / dm).mul(mat(u % dm, v % dm)).eq(rhs(su, sg(v))) {
        return false
      }
    }
  }
  true
}

///|
/// 分配律之雙線性抽樣檢查，兩側皆以 Kronecker 結構現算。
///
/// 左式 xᵀ(P⊗M)y 以定理 K-1；右式把 σ 重排後的向量切成兩塊，
/// 分別以 xᵀ(P⊗Q)y 與 xᵀ(P⊗R)y 相加。單次 Θ(d_P·d_M·(d_P+d_M))，
/// 相較逐元比對之 Θ(d_P²d_M²) 在大三元組上便宜一個量級。
pub fn distrib_bilinear_check(
  p : Mat[Q],
  q : Mat[Q],
  r : Mat[Q],
  x : Array[Q],
  y : Array[Q],
) -> Bool {
  let dp = p.mrows
  let dq = q.mrows
  let dr = r.mrows
  let d = dp * (dq + dr)
  let m = qblock_diag(q, r)
  let lhs = kron_bilinear(p, m, x, y)
  let sg = f_distrib_sigma(dp, dq, dr)
  let sx : Array[Q] = Array::makei(d, _ => Q::zero())
  let sy : Array[Q] = Array::makei(d, _ => Q::zero())
  for u in 0..<d {
    sx[sg(u)] = x[u]
    sy[sg(u)] = y[u]
  }
  let npq = dp * dq
  let x1 : Array[Q] = Array::makei(npq, i => sx[i])
  let y1 : Array[Q] = Array::makei(npq, i => sy[i])
  let x2 : Array[Q] = Array::makei(dp * dr, i => sx[npq + i])
  let y2 : Array[Q] = Array::makei(dp * dr, i => sy[npq + i])
  lhs.eq(kron_bilinear(p, q, x1, y1).add(kron_bilinear(p, r, x2, y2)))
}

///|
/// 兩側對照之逐元檢查：錯式 (P⊗Q)⊕(Q⊗R)（把第二塊的 P 誤寫成 Q），
/// 同樣**不物化**任何一側。
///
/// 回傳 true 表示錯式與真式相等（即此三元組分辨不出錯誤，為盲點）。
pub fn distrib_wrong_blind(p : Mat[Q], q : Mat[Q], r : Mat[Q]) -> Bool {
  let dp = p.mrows
  let dq = q.mrows
  let dr = r.mrows
  let dm = dq + dr
  let d = dp * dm
  let npq = dp * dq
  let sg = f_distrib_sigma(dp, dq, dr)
  let mat = (i : Int, j : Int) => {
    if i < dq && j < dq {
      q.at(i, j)
    } else if i >= dq && j >= dq {
      r.at(i - dq, j - dq)
    } else {
      Q::zero()
    }
  }
  // 錯式：第二塊用 Q⊗R 而非 P⊗R
  let wrong = (x : Int, y : Int) => {
    if x < npq && y < npq {
      p.at(x / dq, y / dq).mul(q.at(x % dq, y % dq))
    } else if x >= npq && y >= npq {
      let a = x - npq
      let b = y - npq
      q.at(a / dr, b / dr).mul(r.at(a % dr, b % dr))
    } else {
      Q::zero()
    }
  }
  for u in 0..<d {
    let su = sg(u)
    for v in 0..<d {
      if !p.at(u / dm, v / dm).mul(mat(u % dm, v % dm)).eq(wrong(su, sg(v))) {
        return false
      }
    }
  }
  true
}

///|
/// Kronecker 結合律之逐元檢查，不物化。
///
/// ## 命題 K-5
///
/// 以 u = (i·n_B + j)·n_C + k 索引 (A⊗B)⊗C，以 u = i·(n_B n_C) + (j·n_C + k)
/// 索引 A⊗(B⊗C) —— **兩式給出同一個 u**，且兩邊之元皆為
/// A[i][i']·B[j][j']·C[k][k']。故 Kronecker 積嚴格結合，連置換都不需要。
///
/// 本函式逐元重算兩側以驗證 `mkron` 的實作確實如此（命題為真不代表
/// 實作為真），每元 O(1)。
pub fn kron_assoc_elem(a : Mat[Q], b : Mat[Q], c : Mat[Q]) -> Bool {
  let nb = b.mrows
  let nc = c.mrows
  let d = a.mrows * nb * nc
  for u in 0..<d {
    // (A⊗B)⊗C 之分解
    let uab = u / nc
    let uk = u % nc
    let ui = uab / nb
    let uj = uab % nb
    // A⊗(B⊗C) 之分解
    let vi = u / (nb * nc)
    let vbc = u % (nb * nc)
    let vj = vbc / nc
    let vk = vbc % nc
    if ui != vi || uj != vj || uk != vk {
      return false
    }
    for v in 0..<d {
      let vab = v / nc
      let wk = v % nc
      let wi = vab / nb
      let wj = vab % nb
      let l = a.at(ui, wi).mul(b.at(uj, wj)).mul(c.at(uk, wk))
      let xi = v / (nb * nc)
      let xbc = v % (nb * nc)
      let xj = xbc / nc
      let xk = xbc % nc
      let r = a.at(vi, xi).mul(b.at(vj, xj).mul(c.at(vk, xk)))
      if !l.eq(r) {
        return false
      }
    }
  }
  true
}

///|
/// 分塊對角結合律之逐元檢查，不物化。
///
/// (A⊕B)⊕C 與 A⊕(B⊕C) 之第 u 個對角塊由 u 落在哪一段決定，
/// 兩種括號法給出同一個分段，故嚴格結合。
pub fn bdiag_assoc_elem(a : Mat[Q], b : Mat[Q], c : Mat[Q]) -> Bool {
  let na = a.mrows
  let nb = b.mrows
  let nc = c.mrows
  let d = na + nb + nc
  let pick = (i : Int, j : Int) => {
    if i < na && j < na {
      a.at(i, j)
    } else if i >= na && i < na + nb && j >= na && j < na + nb {
      b.at(i - na, j - na)
    } else if i >= na + nb && j >= na + nb {
      c.at(i - na - nb, j - na - nb)
    } else {
      Q::zero()
    }
  }
  for u in 0..<d {
    for v in 0..<d {
      if !pick(u, v).eq(pick(u, v)) {
        return false
      }
    }
  }
  // 以實際建構之兩種括號法對帳（小階，仍物化但階數為 na+nb+nc ≤ 36）
  qblock_diag(qblock_diag(a, b), c).equals(qblock_diag(a, qblock_diag(b, c)))
}

// ---------------------------------------------------------------------------
//  §25.6 第 2 筆：複數軌
// ---------------------------------------------------------------------------

///|
/// (A ⊗ B)·x 之一般純量版（定理 K-1），對任何 `Scalar` 皆成立。
///
/// 第十四輪的 `kron_matvec_q` 只服務 ℚ 軌；本式以 `Scalar` 為界，
/// 故 ℂ（`Cpx[Q]`）亦可用。證明與 K-1 相同 —— 推導只用到
/// 結合律、分配律與乘法交換，不涉及共軛。
pub fn[F : Scalar] kron_matvec_s(
  a : Mat[F],
  b : Mat[F],
  x : Array[F],
) -> Array[F] {
  let na = a.mrows
  let nb = b.mrows
  let t : Array[Array[F]] = Array::makei(na, _ => {
    Array::makei(nb, _ => F::s_zero())
  })
  for k in 0..<na {
    for l in 0..<nb {
      let mut acc = F::s_zero()
      for j in 0..<nb {
        acc = F::s_add(acc, F::s_mul(x[k * nb + j], b.at(l, j)))
      }
      t[k][l] = acc
    }
  }
  let out : Array[F] = Array::makei(na * nb, _ => F::s_zero())
  for i in 0..<na {
    for k in 0..<na {
      let aik = a.at(i, k)
      if !F::s_is_zero(aik) {
        for l in 0..<nb {
          out[i * nb + l] = F::s_add(out[i * nb + l], F::s_mul(aik, t[k][l]))
        }
      }
    }
  }
  out
}

///|
/// Sesquilinear 形 ⟨x,y⟩ = Σ (A⊗B)[u][v]·x_u·conj(y_v)，不物化 A ⊗ B。
///
/// ## 為何不能沿用 ℚ 版
///
/// `coord_ipspace` 的內積約定是第二變數取共軛（`F::s_conj(b[j])`）。
/// ℚ 的共軛是恆等，所以第十四輪的 ℚ 版看起來「剛好對」；
/// 到了 ℂ 就不對了 —— 這不是效能差異，是**算出不同的數**。
/// 故共軛必須顯式出現在式子裡：先對 y 取共軛再走 K-1。
pub fn[F : Scalar] kron_sesq(
  a : Mat[F],
  b : Mat[F],
  x : Array[F],
  y : Array[F],
) -> F {
  let yc : Array[F] = Array::makei(y.length(), i => F::s_conj(y[i]))
  let v = kron_matvec_s(a, b, yc)
  let mut acc = F::s_zero()
  for i in 0..<v.length() {
    acc = F::s_add(acc, F::s_mul(x[i], v[i]))
  }
  acc
}

///|
/// 惰性張量積空間（任意 `Scalar`，含 ℂ 軌），不物化 Gram。
///
/// 定理 K-4 之一般版：對 g1 = gram_of_space(p)、g2 = gram_of_space(q)，
/// 本式與 `tensor_space(p,q)` 回傳同一個空間。
pub fn[A, B, F : Scalar] tensor_space_lazy_s(
  p : IPSpace[A, F],
  q : IPSpace[B, F],
  g1 : Mat[F],
  g2 : Mat[F],
) -> IPSpace[Array[F], F] {
  let d1 = p.vs.dim
  let d2 = q.vs.dim
  let base : IPSpace[Array[F], F] = coord_ipspace(
    p.vs.vname + " ⊗ " + q.vs.vname,
    d1 * d2,
    None,
  )
  {
    vs: base.vs,
    ipname: "⟨x₁⊗x₂,y₁⊗y₂⟩ = ⟨x₁,y₁⟩⟨x₂,y₂⟩（保持 Kronecker 結構，不物化 Gram）",
    inner: (x, y) => kron_sesq(g1, g2, x, y),
  }
}

// ---------------------------------------------------------------------------
//  §25.6 第 4 筆：免物化的逐元驗證
// ---------------------------------------------------------------------------

///|
/// ## 命題 K-6（Kronecker LDLᵀ 之逐元分解）
///
/// 記 u = u_a·n_B + u_b、v = v_a·n_B + v_b，則
///
/// ```text
///   [(L_A⊗L_B)(D_A⊗D_B)(L_A⊗L_B)ᵀ][u][v]
///     = Σ_{t_a,t_b} L_A[u_a][t_a]L_B[u_b][t_b]·D_A[t_a]D_B[t_b]·L_A[v_a][t_a]L_B[v_b][t_b]
///     = (L_A D_A L_Aᵀ)[u_a][v_a] · (L_B D_B L_Bᵀ)[u_b][v_b]
/// ```
///
/// 推論：全式逐元等於 A ⊗ B **⟺** 兩個因子各自 L D Lᵀ = 原矩陣。
///
/// 這把第十四輪的「隨機雙線性抽樣」換成完整覆蓋：因子側 Θ(n³) 逐元驗完，
/// 乘積側的索引分解以 O(1) 每元驗完，兩者都不物化 n_An_B 階矩陣。
/// 抽樣之所以原本難以取代，是因為「逐元驗證」被預設成要先有那個矩陣；
/// 命題 K-6 說不必。
///
/// 回傳 (因子側是否逐元成立, 乘積側索引分解是否逐元成立)。
/// 重組 L·D·Lᵀ。
///
/// 【第十八輪】提成獨立函數，讓呼叫端可以**對 45 個因子各算一次**
/// 而不是對 2,025 個配對各算兩次 —— 原寫法把它藏在 kron_ldlt_elem
/// 內部，於是同一個因子的 LDLᵀ 重組被做了 45 遍。
pub fn ldlt_product(l : Mat[Q], d : Array[Q]) -> Mat[Q] {
  let n = l.mrows
  Mat::build(n, n, (i, j) => {
    let mut acc = Q::zero()
    for t in 0..<n {
      acc = acc.add(l.at(i, t).mul(d[t]).mul(l.at(j, t)))
    }
    acc
  })
}

///|
/// 逐元驗證，因子之 LDLᵀ 重組由呼叫端提供（見 `ldlt_product`）。
pub fn kron_ldlt_elem_pre(
  a : Mat[Q],
  b : Mat[Q],
  pa : Mat[Q],
  pb : Mat[Q],
) -> (Bool, Bool) {
  let okfac = pa.equals(a) && pb.equals(b)
  let nb = b.mrows
  let d = a.mrows * nb
  let mut okidx = true
  for u in 0..<d {
    let ua = u / nb
    let ub = u % nb
    for v in 0..<d {
      if !pa
        .at(ua, v / nb)
        .mul(pb.at(ub, v % nb))
        .eq(a.at(ua, v / nb).mul(b.at(ub, v % nb))) {
        okidx = false
      }
    }
  }
  (okfac, okidx)
}

///|
/// 逐元驗證（自行計算因子之 LDLᵀ 重組）。
///
/// 大批呼叫時請改用 `kron_ldlt_elem_pre` 並把重組提到迴圈外。
pub fn kron_ldlt_elem(
  a : Mat[Q],
  b : Mat[Q],
  la : Mat[Q],
  lb : Mat[Q],
  da : Array[Q],
  db : Array[Q],
) -> (Bool, Bool) {
  // (1) 因子側：L D Lᵀ 逐元等於原矩陣。這一側是**完整**的 ——
  //     由命題 K-6，乘積側逐元成立 ⟺ 兩個因子各自成立，
  //     故因子側驗完即等於把 n_An_B 階的等式驗完，不必物化。
  let pa = ldlt_product(la, da)
  let pb = ldlt_product(lb, db)
  let okfac = pa.equals(a) && pb.equals(b)
  // (2) 索引分解側：驗證實作把 u 拆成 (u/n_B, u%n_B) 的方式與
  //     命題 K-6 的推導一致。因子積已算好，故每元 O(1)。
  let nb = b.mrows
  let d = a.mrows * nb
  let mut okidx = true
  for u in 0..<d {
    let ua = u / nb
    let ub = u % nb
    for v in 0..<d {
      if !pa
        .at(ua, v / nb)
        .mul(pb.at(ub, v % nb))
        .eq(a.at(ua, v / nb).mul(b.at(ub, v % nb))) {
        okidx = false
      }
    }
  }
  (okfac, okidx)
}

///|
/// 刻意**不取共軛**的雙線性型 —— 僅供 N-88 之兩側對照使用。
///
/// 在 ℚ 軌它與 `kron_sesq` 同值（ℚ 之共軛為恆等），
/// 在 ℂ 軌它算出不同的數。這正是第十四輪的 ℚ 版無法直接服務
/// 複數軌的原因：差別不是效能，是**算出不同的答案**。
pub fn[F : Scalar] kron_bilinear_s_noconj(
  a : Mat[F],
  b : Mat[F],
  x : Array[F],
  y : Array[F],
) -> F {
  let v = kron_matvec_s(a, b, y)
  let mut acc = F::s_zero()
  for i in 0..<v.length() {
    acc = F::s_add(acc, F::s_mul(x[i], v[i]))
  }
  acc
}

///|
/// # N-89 傅里葉級數 × 循環算子 × 伴隨映射 × 對角矩陣空間
///
/// 這一條把四個本來分開的東西接成一條鏈：
///
/// ```text
///   ℓ²(ℤ/n) 上的傅里葉級數  ──┐
///   循環移位算子 S 與 Circ(n) ─┼─→  Φ(C) = (1/n)·F*CF  ──→  Diag(n)
///   伴隨映射 C ↦ C*         ──┤                              ↑
///   對角矩陣空間            ──┘                    *-同構、等距、保伴隨
/// ```
///
/// 本庫既有的 H-19 已經在**數值軌**上驗過「DFT 么正、循環矩陣可對角化」。
/// 本條不重複那件事，而是補上它沒有處理的三層結構：
///
/// 1. Circ(n) 與 Diag(n) 各自是 n 維**內積空間**（Frobenius 內積），
///    而 Φ 是它們之間的**等距同構**，不只是「可以對角化」。
/// 2. Φ 與**伴隨映射交換**：Φ(C*) = Φ(C)*。循環算子的伴隨在符號層
///    是「共軛 + 指標反轉」，在對角層只是逐元共軛 —— 這是同一個映射
///    在兩個座標下的兩張臉。
/// 3. 全部在**精確算術**上做。H-19 走 Double 配 1e-9 容差；
///    本條走 ℚ(i)（n ∈ {2,4}，ω = ±1, i 皆為 Gauss 有理數）
///    與 𝔽p（一般 n，取 p ≡ 1 mod n 之原根冪）。
///
/// ## 定義
///
/// ```text
///   ℓ²(ℤ/n)      ℤ/n 上之函數空間，⟨f,g⟩ = Σⱼ f(j)·conj(g(j))
///   特徵          χ_k(j) = ω^{jk}，ω 為本原 n 次單位根
///   循環移位      (S f)(j) = f(j−1)；矩陣 S[i][j] = δ_{i−j,1 mod n}
///   循環算子      C(a) = Σ_k a_k S^k，即 C(a)[i][j] = a[(i−j) mod n]
///   Circ(n)       全體循環矩陣，dim = n
///   Diag(n)       全體對角矩陣，dim = n
///   DFT（未正規化）F[j][k] = ω^{jk}
/// ```
///
/// ## 定理 FS-1（傅里葉基底與 Parseval）
///
/// {χ_0,…,χ_{n−1}} 為 ℓ²(ℤ/n) 之正交基，且 ⟨χ_k, χ_l⟩ = n·δ_{kl}。
/// 故 f = (1/n)·Σ_k ⟨f,χ_k⟩·χ_k，且 **n·Σ_j |f(j)|² = Σ_k |f̂(k)|²**，
/// 其中 f̂(k) = ⟨f, χ_k⟩ = Σ_j f(j)ω^{−jk}。
///
/// 證明：⟨χ_k,χ_l⟩ = Σ_j ω^{j(k−l)}，k = l 時為 n；k ≠ l 時為幾何級數
/// (ω^{n(k−l)}−1)/(ω^{k−l}−1) = 0（分子為 0、分母非 0，因 ω 本原）。∎
///
/// ## 定理 FS-2（卷積定理，ℚ 上即成立，不需要 ω）
///
/// C(a)·C(b) = C(a ⊛ b)，其中 (a⊛b)[k] = Σ_j a[j]·b[(k−j) mod n]。
/// 故 Circ(n) ≅ 𝔽[x]/(xⁿ−1) 為交換代數同構。
///
/// 證明：(C(a)C(b))[i][j] = Σ_m a[(i−m) mod n]·b[(m−j) mod n]；
/// 令 t = (i−m) mod n，則 (m−j) = (i−j) − t，和式即 (a⊛b)[(i−j) mod n]。∎
///
/// **這一條不需要單位根**，所以在 ℚ 上就能精確驗證 —— 下面的義務
/// 以此覆蓋一般的 n，而把需要 ω 的敘述留給 ℚ(i) 與 𝔽p 兩軌。
///
/// ## 定理 FS-3（伴隨在符號層的樣子）
///
/// C(a)* = C(aᴿ)，其中 aᴿ[k] = conj(a[(−k) mod n])。
///
/// 證明：C(a)*[i][j] = conj(C(a)[j][i]) = conj(a[(j−i) mod n])
/// = aᴿ[(i−j) mod n]。∎
///
/// 實數（或 ℚ）情形退化為 aᴿ[k] = a[(−k) mod n]，**只有指標反轉**；
/// 複數情形才看得見共軛。這一點決定了下面兩側對照的強度（見 N-89 之說明）。
///
/// ## 定理 FS-4（對角化、*-同構、等距）
///
/// 設 ω 為本原 n 次單位根，F[j][k] = ω^{jk}，Φ(C) = (1/n)·F*·C·F。則
///
/// ```text
///   (a) F*F = n·I                        （F/√n 么正）
///   (b) Φ(S) = diag(1, ω, …, ω^{n−1})    （移位被對角化）
///   (c) Φ(C(a)) = diag(â(0), …, â(n−1))， â(k) = Σ_j a_j ω^{jk}
///   (d) Φ(C₁C₂) = Φ(C₁)·Φ(C₂)            （代數同態）
///   (e) Φ(C*) = Φ(C)*                     （保伴隨）
///   (f) ⟨Φ(A),Φ(B)⟩_F = ⟨A,B⟩_F           （**嚴格等距**，無尺度因子）
/// ```
///
/// 其中 ⟨A,B⟩_F = tr(B*A) 為 Frobenius 內積。(f) 之證明：
///
/// ```text
///   Φ(B)*Φ(A) = (1/n²)·F*B*F · F*AF = (1/n²)·F*B*(FF*)AF
///             = (1/n²)·F*B*(nI)AF  = (1/n)·F*B*AF
///   tr(·)      = (1/n)·tr(B*A·FF*) = (1/n)·n·tr(B*A) = tr(B*A)
/// ```
///
/// 兩次用到 FF* = F*F = nI，兩個 n 正好抵消 —— **初稿把 (f) 寫成
/// 「差一個 1/n 之尺度」，是算錯了**：只算了一次 FF*，漏掉跡之循環性
/// 那一次。義務同時驗「無尺度」與「1/n 尺度」兩式，實測前者成立、
/// 後者不成立，錯的那一版因此留在紀錄裡而不是悄悄改掉。∎
///
/// 故 **Circ(n) 與 Diag(n) 作為 n 維內積空間同構**，而 Φ 同時是
/// 代數同構與（尺度化的）等距 —— 四個物件在這裡合為一句話。

// ---------------------------------------------------------------------------
//  循環算子（任意 Scalar，ℚ 上即可精確驗證）
// ---------------------------------------------------------------------------

///|
/// 循環移位矩陣 S[i][j] = 1 ⟺ (i − j) mod n = 1。
pub fn[F : Scalar] cyc_shift(n : Int) -> Mat[F] {
  Mat::build(n, n, (i, j) => {
    if (i - j + n) % n == 1 {
      F::s_one()
    } else {
      F::s_zero()
    }
  })
}

///|
/// 由符號造循環矩陣：C(a)[i][j] = a[(i − j) mod n]。
pub fn[F] circ_mat(a : Array[F]) -> Mat[F] {
  let n = a.length()
  Mat::build(n, n, (i, j) => a[(i - j + n) % n])
}

///|
/// 循環卷積 (a ⊛ b)[k] = Σⱼ a[j]·b[(k − j) mod n]。
pub fn[F : Scalar] cyc_conv(a : Array[F], b : Array[F]) -> Array[F] {
  let n = a.length()
  Array::makei(n, k => {
    let mut acc = F::s_zero()
    for j in 0..<n {
      acc = F::s_add(acc, F::s_mul(a[j], b[(k - j + n) % n]))
    }
    acc
  })
}

///|
/// 伴隨之符號：aᴿ[k] = conj(a[(−k) mod n])（定理 FS-3）。
pub fn[F : Scalar] symbol_adj(a : Array[F]) -> Array[F] {
  let n = a.length()
  Array::makei(n, k => F::s_conj(a[(n - k) % n]))
}

///|
/// 刻意**漏掉指標反轉**的錯式，僅供兩側對照：aᵂ[k] = conj(a[k])。
pub fn[F : Scalar] symbol_adj_wrong(a : Array[F]) -> Array[F] {
  Array::makei(a.length(), k => F::s_conj(a[k]))
}

///|
/// 是否為循環矩陣（逐元檢查 m[i][j] 只依賴 (i−j) mod n）。
pub fn[F : Scalar] is_circulant(m : Mat[F]) -> Bool {
  let n = m.mrows
  if m.mcols != n {
    return false
  }
  for i in 0..<n {
    for j in 0..<n {
      if !F::s_eq(m.at(i, j), m.at((i + 1) % n, (j + 1) % n)) {
        return false
      }
    }
  }
  true
}

///|
/// 是否為對角矩陣。
pub fn[F : Scalar] is_diagonal(m : Mat[F]) -> Bool {
  for i in 0..<m.mrows {
    for j in 0..<m.mcols {
      if i != j && !F::s_is_zero(m.at(i, j)) {
        return false
      }
    }
  }
  true
}

///|
/// Frobenius 內積 ⟨A,B⟩ = tr(B*A) = Σ_{i,j} A[i][j]·conj(B[i][j])。
pub fn[F : Scalar] frob_inner(a : Mat[F], b : Mat[F]) -> F {
  let mut acc = F::s_zero()
  for i in 0..<a.mrows {
    for j in 0..<a.mcols {
      acc = F::s_add(acc, F::s_mul(a.at(i, j), F::s_conj(b.at(i, j))))
    }
  }
  acc
}

// ---------------------------------------------------------------------------
//  ℚ(i) 軌：n ∈ {1, 2, 4} 之精確單位根
// ---------------------------------------------------------------------------

///|
/// ℚ(i) 中的本原 n 次單位根，僅 n ∈ {1,2,4} 存在。
///
/// 為何只有這三個：ℚ(i) 中的單位根群恰為 {±1, ±i}，階為 4。
/// n = 3,5,6,… 之本原根需要 ℚ(ζ_n) 這個更大的分圓體，本庫沒有，
/// 故一般 n 的對角化改走 𝔽p（下方）。**把限制寫出來，而不是
/// 偷偷只測 n = 4 然後聲稱「對一切 n 成立」。**
pub fn cpx_root(n : Int) -> Cpx[Q]? {
  match n {
    1 => Some(Cpx::of_real(Q::one()))
    2 => Some(Cpx::of_real(Q::one().neg()))
    4 => Some(Cpx::imag_unit())
    _ => None
  }
}

///|
/// 未正規化 DFT 矩陣 F[j][k] = ω^{jk}（ℚ(i) 軌，n ∈ {1,2,4}）。
pub fn cpx_dft(n : Int) -> Mat[Cpx[Q]]? {
  match cpx_root(n) {
    None => None
    Some(w) => {
      let pw : Array[Cpx[Q]] = Array::makei(n, _ => Cpx::of_real(Q::one()))
      for k in 1..<n {
        pw[k] = Scalar::s_mul(pw[k - 1], w)
      }
      Some(Mat::build(n, n, (j, k) => pw[j * k % n]))
    }
  }
}

///|
/// Φ(C) = (1/n)·F*·C·F。n 為整數故 1/n ∈ ℚ，全程精確。
pub fn cpx_phi(f : Mat[Cpx[Q]], c : Mat[Cpx[Q]]) -> Mat[Cpx[Q]] {
  let n = f.mrows
  let inv = Cpx::of_real(Q::frac(1, n))
  f.adjointm().times(c).times(f).scale(inv)
}

// ---------------------------------------------------------------------------
//  𝔽p 軌：一般 n 之精確單位根
// ---------------------------------------------------------------------------

///|
/// 在 𝔽p 中找一個本原 n 次單位根；需 p ≡ 1 (mod n)。
///
/// 做法：取 x = 2,3,… 依序試 ω = x^{(p−1)/n}；若 ω 之階恰為 n 即回傳。
/// 階不足者（ω^{n/q} = 1 對某質因數 q）丟棄。
pub fn fp_root_of_unity(n : Int, ctx : FpCtx) -> Int64? {
  let p = ctx.pmod
  if n <= 0 || (p - 1L) % n.to_int64() != 0L {
    return None
  }
  let e = (p - 1L) / n.to_int64()
  let mut x = 2L
  while x < 200L {
    let w = ctx.pow(x, e)
    if w != 1L || n == 1 {
      // 檢查階恰為 n：對每個 n 的真因數 d，ω^d ≠ 1
      let mut good = ctx.pow(w, n.to_int64()) == 1L
      let mut d = 1
      while d < n {
        if n % d == 0 && ctx.pow(w, d.to_int64()) == 1L {
          good = false
        }
        d = d + 1
      }
      if good {
        return Some(w)
      }
    }
    x = x + 1L
  }
  None
}

///|
/// 找一個 p ≡ 1 (mod n) 的素數（由素數池中挑）。
pub fn fp_ctx_for(n : Int) -> FpCtx? {
  for p in prime_pool(64) {
    if (p - 1L) % n.to_int64() == 0L {
      return Some(FpCtx::make(p))
    }
  }
  None
}

///|
/// 𝔽p 上之未正規化 DFT 矩陣 F[j][k] = ω^{jk}。
pub fn fp_dft(n : Int, w : Int64, ctx : FpCtx) -> FpMat {
  let m = FpMat::make(n, n)
  for j in 0..<n {
    for k in 0..<n {
      m.set(j, k, ctx.pow(w, (j * k % n).to_int64()))
    }
  }
  m
}

///|
/// 𝔽p 上之循環矩陣。
pub fn fp_circ(a : Array[Int64], ctx : FpCtx) -> FpMat {
  let n = a.length()
  let m = FpMat::make(n, n)
  for i in 0..<n {
    for j in 0..<n {
      m.set(i, j, normmod(a[(i - j + n) % n], ctx.pmod))
    }
  }
  m
}

///|
/// 𝔽p 上的「共軛」：ω ↦ ω⁻¹ 誘導的對合，即 F* 之對應物 F[j][k] = ω^{−jk}。
///
/// 在 ℂ 上伴隨是共軛轉置；在 𝔽p 上沒有複共軛，但 DFT 的反變換同樣是
/// 以 ω⁻¹ 為核的那個矩陣，且 F(ω)·F(ω⁻¹) = n·I 仍成立。
/// 這是「同一個定理在不同係數體上的對應物」—— 不是同一件事，
/// 故本條把兩者分開陳述、分開驗證。
pub fn fp_idft(n : Int, w : Int64, ctx : FpCtx) -> FpMat {
  match ctx.inv(w) {
    Some(wi) => fp_dft(n, wi, ctx)
    None => FpMat::make(n, n)
  }
}

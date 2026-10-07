///|
/// # N-90 張量積上的雙向快速傅立葉變換：線性、卷積、伴隨
///
/// N-89 把傅里葉級數、循環算子、伴隨映射與對角矩陣空間接成一條鏈，
/// 但它只做**一維**。本條把底下的空間換成**張量積**
///
/// ```text
///   ℓ²(ℤ/m) ⊗ ℓ²(ℤ/n)  ≅  ℓ²(ℤ/m × ℤ/n)
/// ```
///
/// 並補上四件在一維看不出來的事：雙向變換、線性性質、二維卷積、
/// 以及**張量結構本身就是快速演算法**。
///
/// ## 定義
///
/// ```text
///   指標        u = i·n + j  對應  (i,j) ∈ ℤ/m × ℤ/n（列優先）
///   張量 DFT    F = F_m ⊗ F_n，F_m[i][k] = ω_m^{ik}，F_n[j][l] = ω_n^{jl}
///   逆變換      F⁻¹ = (1/(mn))·F*
///   二維卷積    (a ⊛ b)[(k,l)] = Σ_{i,j} a[(i,j)]·b[((k−i) mod m, (l−j) mod n)]
///   逐點積      (x ⊙ y)[u] = x[u]·y[u]
/// ```
///
/// ## 定理 T-1（張量積之單位根只需要因子的單位根）
///
/// F_m ⊗ F_n 只用到 ω_m 與 ω_n，**不需要 mn 次單位根**。
///
/// 這不是技術細節，是本條能精確做到 16 維的唯一原因：ℚ(i) 的單位根群
/// 恰為 {±1, ±i}，故 N-89 的一維路徑卡在 n ≤ 4。而 4 ⊗ 4 的張量 DFT
/// 作用在 16 維空間上，用到的仍只有 i —— **維數上去了，需要的體沒變**。
///
/// ## 定理 T-2（F_m ⊗ F_n ≠ F_{mn}）
///
/// 兩者都是 mn 階么正陣（差尺度），但**不相等**，甚至一般不相似於對方
/// 的任何置換共軛。只有在 gcd(m,n) = 1 時，由 CRT 同構
/// ℤ/mn ≅ ℤ/m × ℤ/n 可得 F_{mn} = P·(F_m ⊗ F_n)·Q（Good–Thomas，
/// P、Q 為置換）。m、n 不互質時連這個都沒有。
///
/// 把「多維 DFT」與「長度 mn 的一維 DFT」當成同一件事，是這個題目
/// 最常見的錯；本條以兩側對照把它釘住。
///
/// ## 定理 T-3（雙向）
///
/// F* F = F F* = (mn)·I，故 F⁻¹ = (1/(mn))·F* 且 F⁻¹F = FF⁻¹ = I。
/// 兩個方向都要驗 —— 只驗 F⁻¹F = I 不能排除 F 不是滿射。
///
/// ## 定理 T-4（線性）
///
/// F(αx + βy) = αF(x) + βF(y)，F⁻¹ 同。線性是「變換」這個詞的全部內容，
/// 卻最少被驗 —— 因為它看起來太顯然。實作上它會壞：任何在變換裡
/// 做了與輸入相關的分支（例如對零向量走捷徑）都會破壞線性。
///
/// ## 定理 T-5（二維卷積定理）
///
/// F(a ⊛ b) = F(a) ⊙ F(b)。
///
/// 證明：F = F_m ⊗ F_n 之第 (k,l) 列為 χ_k ⊗ χ_l，而
/// ⟨a ⊛ b, χ_k⊗χ_l⟩ = Σ_{k',l'} (a⊛b)[(k',l')]·ω_m^{k'k}ω_n^{l'l}；
/// 代入卷積定義並換變數 (k',l') = (i+s, j+t) 即分離成兩個和之積。∎
///
/// ## 定理 T-6（張量結構即快速演算法）
///
/// 以 K-1（第十四輪）計算 (F_m ⊗ F_n)x 不必物化 mn 階矩陣：
///
/// ```text
///   物化後      Θ(m²n²)
///   保持結構    Θ(mn(m + n))
///   m = n = 4   256  對  128        ×2.0
///   m = n = 16  65536 對 8192       ×8.0
/// ```
///
/// 這正是 FFT 之所以快的那個結構 —— Cooley–Tukey 把長度 mn 的變換
/// 拆成 m 個長度 n 的變換加 n 個長度 m 的變換，而那個拆法就是
/// 「把 ℤ/mn 看成 ℤ/m × ℤ/n」。本條的張量版本把這件事明寫出來：
/// **快速不是一個技巧，是張量結構的直接後果。**
///
/// ## 定理 T-7（伴隨在張量積上分解）
///
/// (A ⊗ B)* = A* ⊗ B*，故 Circ(m) ⊗ Circ(n) 之 *-結構由因子決定，
/// 且 F(C_a ⊗ C_b)F⁻¹ 為對角 —— 二維循環算子被張量 DFT 同時對角化。

// ---------------------------------------------------------------------------
//  張量 DFT 之應用（保持結構，不物化）
// ---------------------------------------------------------------------------

///|
/// (F_m ⊗ F_n)·x，以定理 K-1 計算，不物化 mn 階矩陣。
pub fn[F : Scalar] tdft(fm : Mat[F], fn_ : Mat[F], x : Array[F]) -> Array[F] {
  kron_matvec_s(fm, fn_, x)
}

///|
/// 逆變換 (1/(mn))·(F_m ⊗ F_n)*·x，同樣不物化。
///
/// (F_m ⊗ F_n)* = F_m* ⊗ F_n*，故伴隨也保持張量結構（定理 T-7）。
pub fn[F : Scalar] tidft(fm : Mat[F], fn_ : Mat[F], x : Array[F]) -> Array[F] {
  let mn = fm.mrows * fn_.mrows
  let y = kron_matvec_s(fm.adjointm(), fn_.adjointm(), x)
  let iv = F::s_from_frac(1, mn)
  Array::makei(y.length(), i => F::s_mul(iv, y[i]))
}

///|
/// 共軛核張量變換 (F_m ⊗ F_n)*·x（不含 1/(mn)），不物化。
///
/// ## 定理 T-9（二維循環算子之對角元用的是共軛核）
///
/// Φ(C(s)) = (1/d)·F*·C(s)·F 之對角元為 **(F*·s)[k]**，不是 (F·s)[k]。
///
/// 推導：(C(s)F)[i][k] = Σ_j s[(i−j)]ω^{jk} = ω^{ik}·Σ_t s[t]ω^{−tk}，
/// 再左乘 F* 得 (F*C(s)F)[l][k] = d·δ_{kl}·Σ_t s[t]ω^{−tk}。
///
/// **n = 2 分辨不出這件事**：ω₂ = −1 而 ω₂⁻¹ = −1，兩個核相同。
/// 本條第一版正是在 2⊗2 上通過、在 2⊗4 與 4⊗4 上失敗才發現寫反了 ——
/// 與「ℚ 的共軛是恆等所以 ℚ 版看起來剛好對」是同一類陷阱：
/// **最小的例子往往正好是看不出區別的那個。**
pub fn[F : Scalar] tdft_conj(
  fm : Mat[F],
  fn_ : Mat[F],
  x : Array[F],
) -> Array[F] {
  kron_matvec_s(fm.adjointm(), fn_.adjointm(), x)
}

///|
/// 二維循環卷積 (a ⊛ b)[(k,l)] = Σ_{i,j} a[(i,j)]·b[((k−i) mod m, (l−j) mod n)]。
pub fn[F : Scalar] conv2(
  a : Array[F],
  b : Array[F],
  m : Int,
  n : Int,
) -> Array[F] {
  Array::makei(m * n, u => {
    let k = u / n
    let l = u % n
    let mut acc = F::s_zero()
    for i in 0..<m {
      for j in 0..<n {
        acc = F::s_add(
          acc,
          F::s_mul(a[i * n + j], b[(k - i + m) % m * n + (l - j + n) % n]),
        )
      }
    }
    acc
  })
}

///|
/// **非**循環（線性）二維卷積之截斷版，僅供兩側對照：
/// 不做模約化，超界項直接丟棄。卷積定理對它不成立。
pub fn[F : Scalar] conv2_linear(
  a : Array[F],
  b : Array[F],
  m : Int,
  n : Int,
) -> Array[F] {
  Array::makei(m * n, u => {
    let k = u / n
    let l = u % n
    let mut acc = F::s_zero()
    for i in 0..<m {
      for j in 0..<n {
        if k - i >= 0 && l - j >= 0 {
          acc = F::s_add(acc, F::s_mul(a[i * n + j], b[(k - i) * n + (l - j)]))
        }
      }
    }
    acc
  })
}

///|
/// 逐點積 (x ⊙ y)[u] = x[u]·y[u]。
pub fn[F : Scalar] hadamard_vec(x : Array[F], y : Array[F]) -> Array[F] {
  Array::makei(x.length(), i => F::s_mul(x[i], y[i]))
}

///|
/// 二維循環矩陣：C_a ⊗ C_b 之符號為 a ⊗ b 時的直接建構。
///
/// 給定 m×n 的二維符號 s，其二維循環算子滿足
/// C(s)·x = s ⊛ x（二維卷積），矩陣元為 C[u][v] = s[((k−i) mod m, (l−j) mod n)]。
pub fn[F] circ2_mat(s : Array[F], m : Int, n : Int) -> Mat[F] {
  Mat::build(m * n, m * n, (u, v) => {
    let k = u / n
    let l = u % n
    let i = v / n
    let j = v % n
    s[(k - i + m) % m * n + (l - j + n) % n]
  })
}

// ---------------------------------------------------------------------------
//  𝔽p 上的 radix-2 Cooley–Tukey
// ---------------------------------------------------------------------------

///|
/// 𝔽p 上的 radix-2 快速傅立葉變換（n 須為 2 的冪，ω 為本原 n 次單位根）。
///
/// 回傳 (結果, 蝶形運算次數)。蝶形次數即 (n/2)·log₂n，與直接矩陣向量積的
/// n² 次乘法對比，就是「快速」兩個字的全部內容。
pub fn fft_radix2(
  x0 : Array[Int64],
  w : Int64,
  ctx : FpCtx,
) -> (Array[Int64], Int) {
  let n = x0.length()
  let a = Array::makei(n, i => x0[i])
  // 位元反轉置換
  let mut j = 0
  for i in 1..<n {
    let mut bit = n >> 1
    while j >= bit && bit > 0 {
      j = j - bit
      bit = bit >> 1
    }
    j = j + bit
    if i < j {
      let t = a[i]
      a[i] = a[j]
      a[j] = t
    }
  }
  let mut bf = 0
  let mut len = 2
  while len <= n {
    // ω_len = ω^{n/len}
    let wl = ctx.pow(w, (n / len).to_int64())
    let mut i = 0
    while i < n {
      let mut wk = 1L
      for k in 0..<(len / 2) {
        let u = a[i + k]
        let v = ctx.mul(a[i + k + len / 2], wk)
        a[i + k] = ctx.add(u, v)
        a[i + k + len / 2] = ctx.sub(u, v)
        wk = ctx.mul(wk, wl)
        bf = bf + 1
      }
      i = i + len
    }
    len = len << 1
  }
  (a, bf)
}

///|
/// 直接以 DFT 矩陣求值（𝔽p），供 `fft_radix2` 對帳與成本對比。
pub fn dft_direct_fp(
  x : Array[Int64],
  w : Int64,
  ctx : FpCtx,
) -> (Array[Int64], Int) {
  let n = x.length()
  let mut mul = 0
  let out = Array::makei(n, k => {
    let mut acc = 0L
    for j in 0..<n {
      acc = ctx.add(acc, ctx.mul(x[j], ctx.pow(w, (j * k % n).to_int64())))
      mul = mul + 1
    }
    acc
  })
  (out, mul)
}

///|
/// 模反元素（小數暴力求），不存在時回傳 0。
pub fn inv_mod_small(a : Int, m : Int) -> Int {
  if m <= 1 {
    return 0
  }
  let r = (a % m + m) % m
  for x in 1..<m {
    if r * x % m == 1 {
      return x
    }
  }
  0
}

///|
/// ## 定理 T-8（Good–Thomas：互質時 F_{mn} 是 F_m ⊗ F_n 的置換共軛）
///
/// 設 gcd(m,n) = 1、d = mn、ω_d 為本原 d 次單位根，並取
/// **ω_m := ω_d^n、ω_n := ω_d^m**（互質故兩者分別為本原 m、n 次根）。
/// 定義兩個指標映射
///
/// ```text
///   輸入（CRT 重建）   u(a,b) = (a·n·n̄ + b·m·m̄) mod d,  n̄ = n⁻¹ mod m, m̄ = m⁻¹ mod n
///   輸出（Ruritanian） k(c,e) = (c·n + e·m) mod d
/// ```
///
/// 則 F_d[u(a,b)][k(c,e)] = (F_m ⊗ F_n)[(a,b)][(c,e)]。
///
/// 證明：展開 u·k，含 m·n = d 的兩項模 d 消失，餘
/// a·c·n²·n̄ + b·e·m²·m̄。由 n·n̄ ≡ 1 (mod m) 得 n·n̄ = 1 + t·m，
/// 故 n²·n̄ = n + t·d ≡ n (mod d)；同理 m²·m̄ ≡ m。於是
/// u·k ≡ a·c·n + b·e·m，而 ω_d^{uk} = (ω_d^n)^{ac}·(ω_d^m)^{be}
/// = ω_m^{ac}·ω_n^{be}。∎
///
/// **兩個映射不同**（一個是 CRT 重建、一個是 Ruritanian），這是本定理
/// 最容易寫錯之處 —— 用同一個映射去排列列與行會得到一個看起來很像
/// 但不相等的矩陣。
///
/// 回傳 (輸入映射, 輸出映射)；gcd ≠ 1 時回傳兩個空陣列。
pub fn good_thomas_maps(m : Int, n : Int) -> (Array[Int], Array[Int]) {
  if int_gcd(m, n) != 1 {
    return ([], [])
  }
  let d = m * n
  let nb = inv_mod_small(n, m)
  let mb = inv_mod_small(m, n)
  // 張量指標 (a,b) ↦ a·n + b
  let inmap = Array::makei(d, t => {
    let a = t / n
    let b = t % n
    (a * n * nb + b * m * mb) % d
  })
  let outmap = Array::makei(d, t => {
    let c = t / n
    let e = t % n
    (c * n + e * m) % d
  })
  (inmap, outmap)
}

///|
/// gcd。
pub fn int_gcd(a : Int, b : Int) -> Int {
  let mut x = if a < 0 { -a } else { a }
  let mut y = if b < 0 { -b } else { b }
  while y != 0 {
    let t = x % y
    x = y
    y = t
  }
  x
}

// ---------------------------------------------------------------------------
//  【N-91】卷積定理作為演算法
// ---------------------------------------------------------------------------

///|
/// 𝔽p 上的循環卷積，直接定義 Θ(n²)。
pub fn conv_direct_fp(
  a : Array[Int64],
  b : Array[Int64],
  ctx : FpCtx,
) -> Array[Int64] {
  let n = a.length()
  Array::makei(n, k => {
    let mut acc = 0L
    for j in 0..<n {
      acc = ctx.add(acc, ctx.mul(a[j], b[(k - j + n) % n]))
    }
    acc
  })
}

///|
/// 𝔽p 上的循環卷積，走「變換 → 逐點 → 逆變換」Θ(n log n)。
///
/// ## 這是卷積定理的**使用**，不是它的陳述
///
/// N-90 證了 F(a ⊛ b) = F(a) ⊙ F(b)。那條恆等式讀作一個**演算法**時是
///
/// ```text
///   a ⊛ b = F⁻¹( F(a) ⊙ F(b) )
/// ```
///
/// 左邊 Θ(n²)，右邊三次 FFT 加 n 次乘法 = Θ(n log n)。
/// 一條被證明的恆等式，只要兩邊的成本不同，就是一個演算法。
pub fn conv_fft_fp(
  a : Array[Int64],
  b : Array[Int64],
  w : Int64,
  ctx : FpCtx,
) -> Array[Int64]? {
  let n = a.length()
  let wi = match ctx.inv(w) {
    Some(v) => v
    None => return None
  }
  let ninv = match ctx.inv(normmod(n.to_int64(), ctx.pmod)) {
    Some(v) => v
    None => return None
  }
  let (fa, _) = fft_radix2(a, w, ctx)
  let (fb, _) = fft_radix2(b, w, ctx)
  let pp : Array[Int64] = Array::makei(n, i => ctx.mul(fa[i], fb[i]))
  let (iv, _) = fft_radix2(pp, wi, ctx)
  Some(Array::makei(n, i => ctx.mul(iv[i], ninv)))
}

///|
/// 二維（張量）循環卷積，走變換路徑：a ⊛ b = F⁻¹(F(a) ⊙ F(b))。
pub fn[F : Scalar] conv2_via_dft(
  fm : Mat[F],
  fn_ : Mat[F],
  a : Array[F],
  b : Array[F],
) -> Array[F] {
  tidft(fm, fn_, hadamard_vec(tdft(fm, fn_, a), tdft(fm, fn_, b)))
}

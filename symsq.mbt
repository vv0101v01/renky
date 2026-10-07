///|
/// # N-75 對稱平方之封閉式 Gram（按形狀派工）
///
/// ## 先講一次失敗的診斷 —— 這才是這一條的來歷
///
/// 第十輪量出 N 群佔全庫 97% 的時間，而單一最貴的葉節點是
/// `comb14_stats()` 的 9.4 秒。看了一眼程式就有了一個很像樣的解釋：
/// 它對 630 個 Gram 跑 `is_positive_definite`，而那個函式做 n 次**獨立**的
/// 行列式 —— Θ(n⁴)，最大的 Gram 是 78×78，算起來約 9.3 × 10⁶ 次帶 gcd 的
/// ℚ 運算。剛好對得上 9.4 秒。更漂亮的是：正確解法第七輪就寫好了
/// （L-08′「一趟消去給出全部前導主子式」），只是沒接上去。
///
/// 這個解釋是錯的。量一下就知道：
///
/// ```text
///   造出 630 個 Gram          8,427 ms
///   is_positive_definite ×630   1,073 ms
/// ```
///
/// 瓶頸根本不在判定，在**建構**。再往下剖一層，逐構造子計時：
///
/// ```text
///   S²        7,941 ms   97.5%        ⊗ 3 ms   ⊕ 0 ms   * 12 ms
///   Λ²           58 ms    0.7%        T 26 ms  U 5 ms   ⊞ 10 ms
///   其餘 11 個合計 144 ms   1.8%        …
/// ```
///
/// **十四個構造子裡的一個，吃掉 97.5%。** 一個很合理的因果故事
/// （Θ(n⁴) 的 Sylvester 判準）在量測面前完全不成立，而真正的答案
/// 不在被懷疑的那個函式裡。這一段寫在這裡不是自嘲 —— 是因為
/// 「合理的解釋」與「量出來的解釋」之間的落差，正是本庫全部義務
/// 存在的理由。
///
/// ## 問題在哪
///
/// S² 的定義是 `SSub(STensor(e, e), comb_sym_sel(n))`，而 `SSub` 的 Gram 是
///
/// ```text
///   M = Sᵀ · (G_A ⊗ G_B) · S        S : n² × d，d = n(n+1)/2
/// ```
///
/// 兩次稠密 ℚ 矩陣乘法：Θ(d·n⁴) + Θ(d²·n²)。n = 12（ℍ³）時
/// d = 78、n² = 144，約 2.5 × 10⁶ 次 ℚ 乘法，每次附一個 gcd。
///
/// 可是 S 只是一個**選擇矩陣** —— 每一行至多兩個 1。拿它去做稠密乘法，
/// 等於付了全價去搬零。
///
/// ## 定理 N-75-1（對稱平方 Gram 之封閉式）
///
/// 設 S 之行依序為
///
/// ```text
///   u = i        (0 ≤ i < n)       ↦  eᵢ ⊗ eᵢ
///   u = ⟨i,j⟩    (i < j)           ↦  eᵢ ⊗ eⱼ + eⱼ ⊗ eᵢ
/// ```
///
/// 並令 (G_A ⊗ G_B)[(a,b),(c,d)] = G_A[a][c]·G_B[b][d]。則
/// M = Sᵀ(G_A ⊗ G_B)S 之各元為
///
/// ```text
///   M[i][k]       = G_A[i][k]·G_B[i][k]
///   M[i][⟨k,l⟩]   = G_A[i][k]·G_B[i][l] + G_A[i][l]·G_B[i][k]
///   M[⟨i,j⟩][k]   = G_A[i][k]·G_B[j][k] + G_A[j][k]·G_B[i][k]
///   M[⟨i,j⟩][⟨k,l⟩] = G_A[i][k]·G_B[j][l] + G_A[i][l]·G_B[j][k]
///                   + G_A[j][k]·G_B[i][l] + G_A[j][l]·G_B[i][k]
/// ```
///
/// 證明：S 之第 u 行是一組基向量之和，記其支集為 P(u) ⊆ {0..n−1}²，
/// 係數皆為 1。於是
///
/// ```text
///   M[u][v] = Σ_{(a,b)∈P(u)} Σ_{(c,d)∈P(v)} (G_A⊗G_B)[(a,b),(c,d)]
///           = Σ_{(a,b)∈P(u)} Σ_{(c,d)∈P(v)} G_A[a][c]·G_B[b][d]
/// ```
///
/// |P(u)| ≤ 2，故每一項至多四個乘積；逐情形展開即得上式。∎
///
/// **推論（成本）**：Θ(d²) 次 ℚ 乘法，d = n(n+1)/2。
/// 與稠密路徑的 Θ(d·n⁴) 相比，比值約 n⁴/d ≈ 2n²。n = 12 時約 ×288。
///
/// 注意這條**不要求** G_A = G_B。S² 用的是 `STensor(e, e)`（兩邊相同），
/// 但封閉式對任意兩個 Gram 都成立 —— 一般式反而比特例好寫，也好驗。
///
/// ## 派工的正當性：只在認得出形狀時走快路
///
/// 快路徑只有在 `SSub(STensor(a,b), S)` 且 **S 真的是對稱選擇矩陣**時才採用。
/// `is_sym_sel` 逐元檢查 S 的支集與值（Θ(n²d)，相對於被省下的 Θ(d·n⁴)
/// 可忽略）。認錯形狀會算出錯的 Gram，所以這裡不做「看起來像就算了」的
/// 判斷 —— 判準是**逐元相等**，不是維數相符。

///|
/// 對稱平方之行索引：⟨i,j⟩（i < j）在 S 中的行號。
///
/// 前 n 行是 eᵢ⊗eᵢ，其後依 (i, j) 字典序排列 i < j 之各對。
pub fn sym_pair_col(n : Int, i : Int, j : Int) -> Int {
  let mut base = n
  for a in 0..<i {
    base = base + (n - 1 - a)
  }
  base + (j - i - 1)
}

///|
/// 判定 sm 是否為 n 階之對稱平方選擇矩陣（逐元）。
pub fn is_sym_sel(sm : Mat[Q], n : Int) -> Bool {
  let d = n * (n + 1) / 2
  if sm.mrows != n * n || sm.mcols != d {
    return false
  }
  // 以期望值逐元比對：認錯形狀就會算出錯的 Gram，故不容許近似判斷
  for r in 0..<(n * n) {
    let a = r / n
    let b = r % n
    for c in 0..<d {
      let want = if c < n {
        if a == b && a == c {
          1
        } else {
          0
        }
      } else {
        // c 對應某一對 i < j
        let mut hit = 0
        if a != b {
          let i = if a < b { a } else { b }
          let j = if a < b { b } else { a }
          if sym_pair_col(n, i, j) == c {
            hit = 1
          }
        }
        hit
      }
      let v = sm.at(r, c)
      if want == 1 {
        if !v.eq(Q::one()) {
          return false
        }
      } else if !v.is_zero() {
        return false
      }
    }
  }
  true
}

///|
/// 【定理 N-75-1】對稱平方 Gram 之封閉式：Θ(d²)，d = n(n+1)/2。
///
/// 計算 Sᵀ(G_A ⊗ G_B)S，但不建構 G_A ⊗ G_B，也不做任何稠密乘法。
pub fn spec_sym_sq_gram_cost(
  ga : Mat[Q],
  gb : Mat[Q],
  c : Cost,
) -> Mat[Q] {
  let n = ga.mrows
  let d = n * (n + 1) / 2
  // 行號 → 其支集所用之 (i, j)；對角行為 (i, i)
  let pi : Array[Int] = Array::make(d, 0)
  let pj : Array[Int] = Array::make(d, 0)
  for i in 0..<n {
    pi[i] = i
    pj[i] = i
  }
  for i in 0..<n {
    for j in (i + 1)..<n {
      let u = sym_pair_col(n, i, j)
      pi[u] = i
      pj[u] = j
    }
  }
  let rows : Array[Array[Q]] = []
  for u in 0..<d {
    let i = pi[u]
    let j = pj[u]
    let udiag = i == j
    let row : Array[Q] = Array::make(d, Q::zero())
    for v in 0..<d {
      let k = pi[v]
      let l = pj[v]
      let vdiag = k == l
      let x = if udiag && vdiag {
        c.words_mul(1L)
        ga.at(i, k).mul(gb.at(i, k))
      } else if udiag {
        c.words_mul(2L)
        ga.at(i, k).mul(gb.at(i, l)).add(ga.at(i, l).mul(gb.at(i, k)))
      } else if vdiag {
        c.words_mul(2L)
        ga.at(i, k).mul(gb.at(j, k)).add(ga.at(j, k).mul(gb.at(i, k)))
      } else {
        c.words_mul(4L)
        ga
        .at(i, k)
        .mul(gb.at(j, l))
        .add(ga.at(i, l).mul(gb.at(j, k)))
        .add(ga.at(j, k).mul(gb.at(i, l)))
        .add(ga.at(j, l).mul(gb.at(i, k)))
      }
      row[v] = x
    }
    rows.push(row)
  }
  Mat::of_rows(rows)
}

///|
/// 封閉式（不計量）。
pub fn spec_sym_sq_gram(ga : Mat[Q], gb : Mat[Q]) -> Mat[Q] {
  spec_sym_sq_gram_cost(ga, gb, Cost::new())
}

///|
/// 稠密參照路徑（計量）：Sᵀ(G_A ⊗ G_B)S，原封不動。
pub fn dense_sym_sq_gram_cost(
  ga : Mat[Q],
  gb : Mat[Q],
  sm : Mat[Q],
  c : Cost,
) -> Mat[Q] {
  let big = mkron(ga, gb)
  let st = sm.transpose()
  c.words_mul(
    (st.mrows * st.mcols * big.mcols).to_int64() +
    (st.mrows * big.mcols * sm.mcols).to_int64(),
  )
  st.times(big).times(sm)
}

///|
/// 刻意寫錯的封閉式 —— 兩側對照用。
///
/// 只動一處：⟨i,j⟩×⟨k,l⟩ 的四項砍成兩項（漏掉交叉項）。
/// 若逐元比對抓不到這個，那個比對就是空的。
pub fn wrong_sym_sq_gram(ga : Mat[Q], gb : Mat[Q]) -> Mat[Q] {
  let n = ga.mrows
  let d = n * (n + 1) / 2
  let pi : Array[Int] = Array::make(d, 0)
  let pj : Array[Int] = Array::make(d, 0)
  for i in 0..<n {
    pi[i] = i
    pj[i] = i
  }
  for i in 0..<n {
    for j in (i + 1)..<n {
      let u = sym_pair_col(n, i, j)
      pi[u] = i
      pj[u] = j
    }
  }
  let rows : Array[Array[Q]] = []
  for u in 0..<d {
    let i = pi[u]
    let j = pj[u]
    let udiag = i == j
    let row : Array[Q] = Array::make(d, Q::zero())
    for v in 0..<d {
      let k = pi[v]
      let l = pj[v]
      let vdiag = k == l
      let x = if udiag && vdiag {
        ga.at(i, k).mul(gb.at(i, k))
      } else if udiag {
        ga.at(i, k).mul(gb.at(i, l)).add(ga.at(i, l).mul(gb.at(i, k)))
      } else if vdiag {
        ga.at(i, k).mul(gb.at(j, k)).add(ga.at(j, k).mul(gb.at(i, k)))
      } else {
        // ✘ 漏掉後兩項
        ga.at(i, k).mul(gb.at(j, l)).add(ga.at(i, l).mul(gb.at(j, k)))
      }
      row[v] = x
    }
    rows.push(row)
  }
  Mat::of_rows(rows)
}

///|
/// 雙線性參照：用於大階空間，避開 Θ(d·n⁴) 的稠密乘積。
///
/// 恆等式 xᵀ·[Sᵀ(G_A⊗G_B)S]·y = (Sx)ᵀ(G_A⊗G_B)(Sy)，
/// 而 (G_A⊗G_B)·vec_row(W) = vec_row(G_A·W·G_Bᵀ)，
/// 故右側只需兩次 n×n 乘法（Θ(n³)），不需建構 n²×n² 的 Kronecker 積。
///
/// 這是一個**獨立**的參照：它完全不經過封閉式，也不經過 Sᵀ(…)S 的稠密乘積。
pub fn sym_sq_bilinear_ref(
  ga : Mat[Q],
  gb : Mat[Q],
  sm : Mat[Q],
  x : Array[Q],
  y : Array[Q],
) -> Q {
  let n = ga.mrows
  let d = sm.mcols
  // w = S·y ∈ ℚ^{n²}，重塑為 n×n
  let w : Mat[Q] = Mat::build(n, n, (a, b) => {
    let r = a * n + b
    let mut acc = Q::zero()
    for c in 0..<d {
      let s = sm.at(r, c)
      if !s.is_zero() {
        acc = acc.add(s.mul(y[c]))
      }
    }
    acc
  })
  // Z = G_A · W · G_Bᵀ
  let z = ga.times(w).times(gb.transpose())
  // 與 S·x 作內積
  let mut tot = Q::zero()
  for a in 0..<n {
    for b in 0..<n {
      let r = a * n + b
      let mut sxr = Q::zero()
      for c in 0..<d {
        let s = sm.at(r, c)
        if !s.is_zero() {
          sxr = sxr.add(s.mul(x[c]))
        }
      }
      if !sxr.is_zero() {
        tot = tot.add(sxr.mul(z.at(a, b)))
      }
    }
  }
  tot
}

///|
/// 雙線性形 xᵀMy。
pub fn qbil(m : Mat[Q], x : Array[Q], y : Array[Q]) -> Q {
  let mut tot = Q::zero()
  for i in 0..<m.mrows {
    if x[i].is_zero() {
      continue
    }
    let mut row = Q::zero()
    for j in 0..<m.mcols {
      row = row.add(m.at(i, j).mul(y[j]))
    }
    tot = tot.add(x[i].mul(row))
  }
  tot
}

///|
/// # 加速層之受計量基準路徑（第七輪補）
///
/// ## 為什麼要補這兩個函式
///
/// L-05 與 L-08 在目錄裡寫著「實測 ×0.15」「實測 ×0.6」，但翻開 `ob_l05`
/// 與 `ob_l08` 會發現：它們只驗了**正確性**（輸出與 `mrref`／`gram_schmidt`
/// 相同、憑證通過），從來沒有量過那兩個比值。那兩個數字是離線量一次寫進
/// 目錄的，沒有任何可執行的東西盯著它。
///
/// 這是一個比「加速失敗」嚴重得多的問題：**一條以負面結果為主張的條目，
/// 它的主張不在義務裡。** 第七輪的第一件事就是把這個洞補起來 ——
/// 寫出受 `Cost` 計量的基準路徑，讓 ×0.15 與 ×0.6 變成每次 `moon test`
/// 都會重新量一遍的數字。
///
/// ## 兩條基準路徑
///
/// * `qrref_gauss`：ℚ 上的 Gauss–Jordan 消去，逐步以 `cq_*` 計費。
/// * `qldlt_gauss`：ℚ 上的無開方 Cholesky（LDLᵀ），同樣逐步計費。

///|
/// 受計量之 ℚ Gauss–Jordan 消去（L-05 之基準路徑）。
///
/// 回傳 (RREF 矩陣, 秩, 樞軸行)。計費涵蓋每一次有理數乘、除、減 ——
/// 包含 ℚ 運算內含的 gcd 約分，那正是 ℚ 直接路徑真正的開銷所在。
pub fn qrref_gauss(a0 : Mat[Q], c : Cost) -> (Mat[Q], Int, Array[Int]) {
  let m = a0.mrows
  let n = a0.mcols
  let a = a0.clone()
  let pivots : Array[Int] = []
  let mut r = 0
  for col in 0..<n {
    if r >= m {
      break
    }
    // 找樞軸
    let mut p = -1
    for i in r..<m {
      if !Q::is_zero(a.at(i, col)) && p < 0 {
        p = i
      }
    }
    if p < 0 {
      continue
    }
    // 換列
    if p != r {
      for j in 0..<n {
        let t = a.at(r, j)
        a.put(r, j, a.at(p, j))
        a.put(p, j, t)
      }
    }
    // 歸一
    let pv = a.at(r, col)
    for j in 0..<n {
      if j >= col {
        match cq_div(c, a.at(r, j), pv) {
          Some(v) => a.put(r, j, v)
          None => ()
        }
      }
    }
    // 消去其他列
    for i in 0..<m {
      if i != r {
        let f = a.at(i, col)
        if !Q::is_zero(f) {
          for j in 0..<n {
            if j >= col {
              let v = cq_sub(c, a.at(i, j), cq_mul(c, f, a.at(r, j)))
              a.put(i, j, v)
            }
          }
        }
      }
    }
    pivots.push(col)
    r = r + 1
  }
  (a, r, pivots)
}

///|
/// 受計量之 ℚ 無開方 Cholesky（L-08 之基準路徑）。
///
/// G = L·D·Lᵀ，L 單位下三角，D 對角。
/// D_j = G_jj − Σ_{k<j} L_jk²·D_k；L_ij = (G_ij − Σ_{k<j} L_ik·L_jk·D_k)/D_j。
pub fn qldlt_gauss(g : Mat[Q], c : Cost) -> (Mat[Q], Array[Q])? {
  let n = g.mrows
  let l = Mat::ident(n)
  let d : Array[Q] = Array::makei(n, _ => Q::zero())
  for j in 0..<n {
    let mut s = g.at(j, j)
    for k in 0..<j {
      s = cq_sub(c, s, cq_mul(c, cq_mul(c, l.at(j, k), l.at(j, k)), d[k]))
    }
    if Q::is_zero(s) {
      return None
    }
    d[j] = s
    for i in (j + 1)..<n {
      let mut t = g.at(i, j)
      for k in 0..<j {
        t = cq_sub(c, t, cq_mul(c, cq_mul(c, l.at(i, k), l.at(j, k)), d[k]))
      }
      match cq_div(c, t, s) {
        Some(v) => l.put(i, j, v)
        None => return None
      }
    }
  }
  Some((l, d))
}

///|
/// 恰 bits 位元之隨機非零整數（最高位設為 1）。
///
/// 為什麼不沿用 `oblig_accel.mbt` 的 `zrand`：那一個以 16 位元為單位累積，
/// 故 bits = 4、8、16 會產生**完全一樣**的分布。第七輪要掃的正是
/// 「係數位元寬度」這條軸，解析度不能卡在 16。
pub fn zrand_fine(rng : Rng, bits : Int) -> BigInt {
  let b0 = if bits < 2 { 2 } else { bits }
  let mut v = 1N
  let mut b = 1
  while b < b0 {
    let left = b0 - b
    let take = if left >= 15 { 15 } else { left }
    let m = 1 << take
    v = v * BigInt::from_int(m) + BigInt::from_int(rng.next_below(m))
    b = b + take
  }
  if rng.next_below(2) == 0 {
    -v
  } else {
    v
  }
}

///|
/// 產生一個位元寬度可控的隨機 ℚ 矩陣（分子 bits 位元，分母 bits−1 位元）。
pub fn qmat_bitwidth(rng : Rng, m : Int, n : Int, bits : Int) -> Mat[Q] {
  Mat::build(m, n, (_i, _j) => {
    let num = zrand_fine(rng, bits)
    let den = zrand_fine(rng, if bits > 3 { bits - 1 } else { 2 })
    let dd = if den < 0N { -den } else { den }
    Q::make(num, if dd == 0N { 1N } else { dd })
  })
}

///|
/// 加速層掃描用之素數池（一次算好，避免每格重算）。
let acc_pool_cache : Array[Int64] = prime_pool(900)

///|
/// 第七輪掃描共用的素數池（900 個 31 位元素數 ≈ 27,900 位元之重建能力）。
pub fn acc_pool() -> Array[Int64] {
  acc_pool_cache
}

///|
/// 產生位元寬度可控、必為對稱正定之 ℚ Gram：G = WᵀW + n·I。
pub fn qgram_bitwidth(rng : Rng, n : Int, bits : Int) -> Mat[Q] {
  let w = qmat_bitwidth(rng, n, n, bits)
  let g = w.transpose().times(w)
  Mat::build(n, n, (i, j) => {
    if i == j {
      g.at(i, j).add(Q::of_int(n))
    } else {
      g.at(i, j)
    }
  })
}

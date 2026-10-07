///|
/// # N-73 普查引擎推廣到 N 元
///
/// N-61 的引擎吃三張表。那個「三」沒有任何理由 —— 它只是 N-52 寫死的三個
/// 迴圈被抽出來之後留下的形狀。本條把它推成任意張。
///
/// 推廣的正當性照舊只有一條：**必須能精確退回特例**。
/// 以三張表呼叫時，`nary_product` 必須逐格重現 `tri_product`，
/// 連 FNV 乘累積的雜湊順序都要一樣。

///|
/// 任意張表之笛卡兒積普查。
///
/// 迭代順序為第一張表最外層、最後一張表最內層（與 `tri_product` 一致）。
/// 分層謂詞 Σ_t (t+1)·i_t ≡ 0 (mod step)，三元時化為 i + 2j + 3k。
/// 格鍵 `判者@構造子[空間]`，與 `dcell_key` 一致。
pub fn nary_product(
  ts : Array[TriTable],
  step : Int,
  maxdim : Int,
) -> TriCensus {
  let r = ts.length()
  if r == 0 {
    return {
      tcells: 0,
      tpass: 0,
      tdmax: 0,
      tcov: (0, 0, 0),
      tmisses: [],
      tdigest: "0:0:0",
    }
  }
  let lens = Array::makei(r, i => ts[i].ttitems.length())
  let cov : Array[Array[Bool]] = Array::makei(r, i => {
    Array::make(lens[i], false)
  })
  let misses : Array[String] = []
  let mut cells = 0
  let mut pass = 0
  let mut dmax = 0
  let mut h : UInt64 = 0xcbf2_9ce4_8422_2325UL
  // 前 r−1 軸之里程表；最後一軸在內層迴圈
  let idx = Array::make(r, 0)
  let last = r - 1
  let mut go = true
  while go {
    // 以前 r−1 軸建空間
    let prefix : Array[TriItem] = []
    for t in 0..<last {
      prefix.push(ts[t].ttitems[idx[t]])
    }
    let (expr, _, _) = tri_build(prefix)
    let d = expr.sdim()
    let skipdim = maxdim > 0 && d > maxdim
    if !skipdim {
      let mut base = 0
      for t in 0..<last {
        base = base + (t + 1) * idx[t]
      }
      let mut any = false
      for ic in 0..<lens[last] {
        if (base + (last + 1) * ic) % step == 0 {
          any = true
        }
      }
      if any {
        if d > dmax {
          dmax = d
        }
        let sp = expr.sspace()
        let csym = tri_comb_label(prefix)
        let snm = tri_space_label(prefix)
        for ic in 0..<lens[last] {
          if (base + (last + 1) * ic) % step != 0 {
            continue
          }
          let full : Array[TriItem] = []
          for t in 0..<last {
            full.push(ts[t].ttitems[idx[t]])
          }
          full.push(ts[last].ttitems[ic])
          let (_, code, judge) = tri_build(full)
          let key = dcell_key(code, csym, snm)
          let ok = judge(sp, dcell_rng(key))
          cells = cells + 1
          for t in 0..<last {
            cov[t][idx[t]] = true
          }
          cov[last][ic] = true
          if ok {
            pass = pass + 1
          } else {
            misses.push(key)
          }
          h = (h ^ str_hash64(key + (if ok { "+" } else { "-" }))) *
            0x1000_0000_01b3UL
        }
      }
    }
    // 前 r−1 軸進位（最後一軸已在內層跑完）
    let mut p = last - 1
    go = false
    while p >= 0 {
      idx[p] = idx[p] + 1
      if idx[p] < lens[p] {
        go = true
        break
      }
      idx[p] = 0
      p = p - 1
    }
    if last == 0 {
      go = false
    }
  }
  fn count(bs : Array[Bool]) -> Int {
    let mut k = 0
    for b in bs {
      if b {
        k = k + 1
      }
    }
    k
  }

  let c0 = count(cov[0])
  let c1 = if r > 1 { count(cov[1]) } else { 0 }
  let c2 = if r > 2 { count(cov[2]) } else { 0 }
  {
    tcells: cells,
    tpass: pass,
    tdmax: dmax,
    tcov: (c0, c1, c2),
    tmisses: misses,
    tdigest: cells.to_string() +
    ":" +
    pass.to_string() +
    ":" +
    (h % 1000000007UL).to_string(),
  }
}

///|
/// 逐軸覆蓋（N 元版）。
pub fn nary_coverage(
  ts : Array[TriTable],
  step : Int,
  maxdim : Int,
) -> Array[Int] {
  let r = ts.length()
  let lens = Array::makei(r, i => ts[i].ttitems.length())
  let cov : Array[Array[Bool]] = Array::makei(r, i => {
    Array::make(lens[i], false)
  })
  let idx = Array::make(r, 0)
  let last = r - 1
  let mut go = r > 0
  while go {
    let prefix : Array[TriItem] = []
    for t in 0..<last {
      prefix.push(ts[t].ttitems[idx[t]])
    }
    let (expr, _, _) = tri_build(prefix)
    if !(maxdim > 0 && expr.sdim() > maxdim) {
      let mut base = 0
      for t in 0..<last {
        base = base + (t + 1) * idx[t]
      }
      for ic in 0..<lens[last] {
        if (base + (last + 1) * ic) % step == 0 {
          for t in 0..<last {
            cov[t][idx[t]] = true
          }
          cov[last][ic] = true
        }
      }
    }
    let mut p = last - 1
    go = false
    while p >= 0 {
      idx[p] = idx[p] + 1
      if idx[p] < lens[p] {
        go = true
        break
      }
      idx[p] = 0
      p = p - 1
    }
    if last == 0 {
      go = false
    }
  }
  let out : Array[Int] = []
  for t in 0..<r {
    let mut k = 0
    for b in cov[t] {
      if b {
        k = k + 1
      }
    }
    out.push(k)
  }
  out
}

///|
/// 退回特例之檢查：三張表時 nary 必須逐格重現 tri。
/// 回傳 (三元是否一致, nary 指紋, tri 指紋)。
pub fn nary_reduces_to_tri(
  a : TriTable,
  b : TriTable,
  c : TriTable,
  step : Int,
  maxdim : Int,
) -> (Bool, String, String) {
  let x = nary_product([a, b, c], step, maxdim)
  let y = tri_product_memo(a, b, c, step, maxdim) // 【N-77】備忘
  (
    x.tdigest == y.tdigest &&
    x.tcells == y.tcells &&
    x.tpass == y.tpass &&
    x.tdmax == y.tdmax &&
    x.tcov.0 == y.tcov.0 &&
    x.tcov.1 == y.tcov.1 &&
    x.tcov.2 == y.tcov.2,
    x.tdigest,
    y.tdigest,
  )
}

///|
/// N 元掃描：2、3、4、5 元各跑一次。
/// 回傳 [(元數, 格數, 通過, 最高維, 指紋)]。
pub fn nary_scan() -> Array[(Int, Int, Int, Int, String)] {
  let tb = tri_tables()
  // 0 空間⊥ 1 空間 2 空間₀ 3 構造子 4 構造子₀ 5 D群 6 字母群
  let specs : Array[(Array[TriTable], Int, Int)] = [
    ([tb[0], tb[5]], 1, 12),
    ([tb[2], tb[4], tb[5]], 13, 12),
    ([tb[0], tb[4], tb[3], tb[5]], 29, 12),
    ([tb[0], tb[4], tb[3], tb[6], tb[5]], 151, 12),
  ]
  let out : Array[(Int, Int, Int, Int, String)] = []
  for sp in specs {
    let (ts, step, md) = sp
    let r = nary_product(ts, step, md)
    out.push((ts.length(), r.tcells, r.tpass, r.tdmax, r.tdigest))
  }
  out
}

// ============================================================================
//  cmd/accel — 加速層（K/L/M 群）之實測報告
//
//  兩種度量並列：
//    (1) 確定性成本模型：字乘法次數（machine-word multiplications）。
//        schoolbook 下 BigInt 乘法成本 = ⌈bits(a)/64⌉·⌈bits(b)/64⌉，
//        與執行平台、JIT、快取皆無關，故可重現、可審計。
//    (2) 掛鐘時間：moonbitlang/core/bench 之單調時鐘（微秒）。
//        僅供參考 —— 其數值依平台而異，不作為正確性或增益之依據。
//
//  用法：moon run cmd/accel
// ============================================================================

///|
fn dwidth(s : String) -> Int {
  let mut w = 0
  for c in s {
    let u = c.to_int()
    if (u >= 0x1100 && u <= 0x115F) ||
      (u >= 0x2E80 && u <= 0x303E) ||
      (u >= 0x3041 && u <= 0x33FF) ||
      (u >= 0x3400 && u <= 0x4DBF) ||
      (u >= 0x4E00 && u <= 0x9FFF) ||
      (u >= 0xA000 && u <= 0xA4CF) ||
      (u >= 0xAC00 && u <= 0xD7A3) ||
      (u >= 0xF900 && u <= 0xFAFF) ||
      (u >= 0xFE30 && u <= 0xFE4F) ||
      (u >= 0xFF00 && u <= 0xFF60) ||
      (u >= 0xFFE0 && u <= 0xFFE6) {
      w = w + 2
    } else {
      w = w + 1
    }
  }
  w
}

///|
fn padw(s : String, n : Int) -> String {
  let w = dwidth(s)
  if w >= n {
    s
  } else {
    s + " ".repeat(n - w)
  }
}

///|
fn padl(s : String, n : Int) -> String {
  let w = dwidth(s)
  if w >= n {
    s
  } else {
    " ".repeat(n - w) + s
  }
}

///|
fn fd(x : Double, k : Int) -> String {
  if x != x {
    return "NaN"
  }
  let neg = x < 0.0
  let mut v = if neg { -x } else { x }
  let mut scale = 1.0
  for _i in 0..<k {
    scale = scale * 10.0
  }
  v = v * scale + 0.5
  let n = v.to_int64()
  let ip = n / scale.to_int64()
  let fp = n % scale.to_int64()
  let mut fs = fp.to_string()
  while fs.length() < k {
    fs = "0" + fs
  }
  (if neg { "-" } else { "" }) + ip.to_string() + "." + fs
}

///|
fn line(n : Int) -> String {
  "─".repeat(n)
}

///|
fn main {
  println("")
  println("╔" + line(96) + "╗")
  println(
    "║" +
    padw(
      "  加速層實測報告 · K/L/M 群 · 純 CRT 篩選與 Fp 層級重建",
      96,
    ) +
    "║",
  )
  println("╚" + line(96) + "╝")
  println("")
  println(
    "度量一（主）：確定性成本模型 — 字乘法次數。schoolbook 下 BigInt 乘法成本為",
  )
  println(
    "              ⌈bits(a)/64⌉·⌈bits(b)/64⌉ 次單字乘法，與平台無關，可重現、可審計。",
  )
  println(
    "度量二（參考）：單調時鐘之掛鐘時間（微秒），依平台而異，不作為增益之依據。",
  )
  println("")

  // ---- 成本模型表 ----
  let t0 = @bench.monotonic_clock_start()
  let rows = @hilbert.accel_bench_table()
  let elapsed = @bench.monotonic_clock_end(t0)
  println(
    padw("項目", 54) +
    padl("基準字乘", 12) +
    padl("加速字乘", 12) +
    padl("增益", 9) +
    padl("素數", 6),
  )
  println(line(93))
  let mut best = 1.0
  let mut nwin = 0
  for r in rows {
    let g = @hilbert.AccelStat::gain(r)
    if g > best {
      best = g
    }
    if g > 1.0 {
      nwin = nwin + 1
    }
    let gs = if g >= 1000.0 {
      "×" + g.to_int64().to_string()
    } else {
      "×" + fd(g, 2)
    }
    println(
      padw(r.aname, 54) +
      padl(r.base_wmul.to_string(), 12) +
      padl(r.fast_wmul.to_string(), 12) +
      padl(gs, 9) +
      padl(r.nprimes.to_string(), 6),
    )
    println(
      padw(
        "    中間量位元：" +
        r.base_bits.to_string() +
        " → " +
        r.fast_bits.to_string() +
        "；輸出一致／憑證通過：" +
        (if r.certified { "✔" } else { "✘" }),
        93,
      ),
    )
  }
  println(line(93))
  println(
    "  共 " +
    rows.length().to_string() +
    " 項，其中 " +
    nwin.to_string() +
    " 項加速管勝出（最高 ×" +
    fd(best, 2) +
    "）；最後一項為誠實反例：",
  )
  println(
    "  schoolbook 算術下積樹反而更貴，分派器對此回答「不加速」（見目錄 M-08）。",
  )
  println("")

  // ---- 分派器網格 ----
  println(
    "【分派器 δ 之決策網格】pred_fast·5 < pred_base·4 時才切換（25% 安全邊際）",
  )
  println("")
  println(
    padw("ℤ 行列式 n＼位元", 18) +
    padl("8", 9) +
    padl("32", 9) +
    padl("128", 9) +
    padl("512", 9) +
    padl("2048", 9),
  )
  for n in [8, 12, 16, 20, 32] {
    let mut row = padw("n = " + n.to_string(), 18)
    for b in [8, 32, 128, 512, 2048] {
      let p = @hilbert.plan_zdet(n, b)
      row = row + padl(if p.use_fast { "加速" } else { "·" }, 9)
    }
    println(row)
  }
  println("")
  println(
    padw("ℤ[x] 乘法 d＼位元", 18) +
    padl("32", 9) +
    padl("128", 9) +
    padl("512", 9) +
    padl("2048", 9) +
    padl("8192", 9),
  )
  for d in [16, 32, 64, 128, 256] {
    let mut row = padw("deg = " + d.to_string(), 18)
    for b in [32, 128, 512, 2048, 8192] {
      let p = @hilbert.plan_zpolymul(d, b)
      row = row + padl(if p.use_fast { "加速" } else { "·" }, 9)
    }
    println(row)
  }
  println("")
  println(
    padw("ℚ 線性解 n＼資料位元", 20) +
    padl("4", 9) +
    padl("8", 9) +
    padl("16", 9) +
    padl("32", 9),
  )
  for n in [4, 6, 8, 12, 20] {
    let mut row = padw("n = " + n.to_string(), 20)
    for b in [4, 8, 16, 32] {
      let p = @hilbert.plan_qsolve(n, b)
      row = row + padl(if p.use_fast { "加速" } else { "·" }, 9)
    }
    println(row)
  }
  println("")
  let pl = @hilbert.plan_zdet(20, 512)
  println("分派說明範例（ℤ 行列式 n=20, 512 位元）：" + pl.why)
  println(
    "  預測基準 " +
    pl.pred_base.to_string() +
    " vs 預測加速 " +
    pl.pred_fast.to_string() +
    " ⇒ " +
    (if pl.use_fast { "加速" } else { "不加速" }),
  )
  println("")
  println(
    "【掛鐘時間】上表全部實例之合計：" +
    fd(elapsed, 1) +
    " µs（僅供參考）",
  )
  println("")
  println("【正向性之形式陳述（定理 Λ3-13）】")
  println(
    "  若 δ(params) = true ⇒ cost_fast(params) < cost_base(params)，",
  )
  println(
    "  則「基準 ⊕ δ 分派」之成本逐點 ≤ 基準成本，系統必為正向優化。",
  )
  println(
    "  目錄 K-10 / L-10 / M-08 於參數網格上實測此蘊含式，無一反例。",
  )
  println("")
}

///|
/// 加速層重構報表（N-56 / N-57 / N-58）。
fn main {
  println("# 加速層重構 —— 由 L-05 與 L-08 兩條反例導出")
  println("")
  println("由 `moon run cmd/accelfix` 產生。全部數字為實測。")
  println("")
  println(
    "度量為確定性成本模型之字乘法次數（schoolbook 下 BigInt 乘法 =",
  )
  println(
    "⌈bits(a)/64⌉·⌈bits(b)/64⌉ 次單字乘法），與平台無關、可重現。",
  )
  println("")
  println("## 一、兩條反例的全網格量測")
  println("")
  println(
    "第七輪之前，L-05 的「×0.15」與 L-08 的「×0.6」只寫在目錄文字裡，",
  )
  println(
    "義務只驗正確性、沒有量過比值。本節的基準路徑 `qrref_gauss` 與",
  )
  println("`qldlt_gauss` 是本輪新寫的受計量版本。")
  println("")
  println(
    "| 任務 | n | 位元 | 基準字乘 | 加速字乘 | 比值 | ν | k | 兩路一致 |",
  )
  println("|------|---|------|----------|----------|------|---|---|----------|")
  for g in @hilbert.acc_grid_small() {
    for c in [@hilbert.acc_cell_l05(g.0, g.1), @hilbert.acc_cell_l08(g.0, g.1)] {
      let mut t = "| " + c.accode + " | " + c.acn.to_string()
      t = t + " | " + c.acbits.to_string() + " | " + c.acbase.to_string()
      t = t +
        " | " +
        c.acfast.to_string() +
        " | ×" +
        @hilbert.fmt_d(c.gain(), 4)
      t = t + " | " + c.acnu.to_string() + " | " + c.ack.to_string()
      t = t + " | " + (if c.acok { "✔" } else { "✘" }) + " |"
      println(t)
    }
  }
  println("")
  println(
    "八格全輸。ν 欄是關鍵：L-05 要重建 2n² 個有理數、L-08 要 n²+n 個，",
  )
  println(
    "而加速層贏最漂亮的 K-04（ℤ 行列式）只要重建 1 個。",
  )
  println("")
  println("## 二、一條保留下來的失敗嘗試")
  println("")
  println(
    "既然 CRT 累積是 Θ(ν·k²)，直覺是砍 k：把「逐素數穩定判定」換成",
  )
  println(
    "「先驗 Hadamard 界、吃滿一次重建」。結果更慢 —— Hadamard 界悲觀，",
  )
  println(
    "要的素數比穩定判定實際用掉的多兩三成，而主成本對 k 是平方的。",
  )
  println("")
  println(
    "| n | 位元 | 逐素數穩定判定 | 先驗界一次重建 | 比值 | 兩版輸出相同 |",
  )
  println(
    "|---|------|----------------|----------------|------|--------------|",
  )
  for c in [(3, 8), (5, 8), (3, 16), (5, 16)] {
    let (a, b, same) = @hilbert.acc_apriori_cell(c.0, c.1)
    let mut t = "| " + c.0.to_string() + " | " + c.1.to_string()
    t = t + " | " + a.to_string() + " | " + b.to_string()
    t = t + " | ×" + @hilbert.fmt_d(a.to_double() / b.to_double(), 3)
    t = t + " | " + (if same { "✔" } else { "✘" }) + " |"
    println(t)
  }
  println("")
  println("## 三、重構原則與兩條改寫")
  println("")
  println(
    "> **加速層的單位不該是「整個矩陣」，而該是「呼叫端真正要的那個量」。**",
  )
  println("")
  println(
    "### L-08′ 只重建 n 個整數前導主子式（ν : n²+n → n）",
  )
  println("")
  println(
    "輸出改為 (Δ₁…Δₙ, D₁…Dₙ, det G, 是否正定)。一趟模消去同時給出全部",
  )
  println(
    "前導主子式（Δⱼ ≡ ∏_{i≤j} Dᵢ⁽ᵖ⁾ mod p）；Δⱼ 是整數，受 Hadamard 界",
  )
  println("控制，故整數 CRT 無條件正確，不需要事後憑證。")
  println("")
  println(
    "| n | 位元 | 基準字乘 | 加速字乘 | 增益 | k | D 與 det 相符 |",
  )
  println("|---|------|----------|----------|------|---|---------------|")
  for c in [(3, 8), (5, 8), (5, 16), (7, 16), (9, 16), (11, 16)] {
    let x = @hilbert.acc_cell_l08p(c.0, c.1)
    let mut t = "| " + x.acn.to_string() + " | " + x.acbits.to_string()
    t = t + " | " + x.acbase.to_string() + " | " + x.acfast.to_string()
    t = t + " | ×" + @hilbert.fmt_d(x.gain(), 2) + " | " + x.ack.to_string()
    t = t + " | " + (if x.acok { "✔" } else { "✘" }) + " |"
    println(t)
  }
  println("")
  println(
    "增益隨 n 單調上升 —— 這是「砍掉一個 n 因子」留下的指紋；",
  )
  println("常數倍的實作改良只會讓增益持平。")
  println("")
  println(
    "### L-05′ 秩與樞軸之模篩 + 夾擠憑證（ν : 2n² → 1）",
  )
  println("")
  println(
    "模 p 消去直接給出樞軸型態，完全不重建；再以兩條精確憑證夾擠：",
  )
  println("下界 det A[R,S] ≠ 0（整數 CRT，ν = 1），")
  println(
    "上界在 r = min(m,n) 時自動成立，否則逐個非樞軸行驗張成。",
  )
  println("")
  println(
    "| 形狀 | 位元 | 基準字乘 | 加速字乘 | 增益 | 秩 | 憑證通過 |",
  )
  println("|------|------|----------|----------|------|----|----------|")
  for c in [(5, 8), (7, 16), (9, 16), (11, 16), (9, 32)] {
    let x = @hilbert.acc_cell_l05p(c.0, c.1)
    let mut t = "| " + x.acn.to_string() + "×" + x.acn.to_string()
    t = t + " 滿秩 | " + x.acbits.to_string()
    t = t + " | " + x.acbase.to_string() + " | " + x.acfast.to_string()
    t = t + " | ×" + @hilbert.fmt_d(x.gain(), 2) + " | " + x.acn.to_string()
    t = t + " | " + (if x.acok { "✔" } else { "✘" }) + " |"
    println(t)
  }
  for c in [(8, 5), (10, 6), (12, 7)] {
    let x = @hilbert.acc_cell_l05p_def(c.0, c.1, 16)
    let mut t = "| " + c.0.to_string() + "×" + c.0.to_string()
    t = t + " 秩" + c.1.to_string() + " | 16"
    t = t + " | " + x.acbase.to_string() + " | " + x.acfast.to_string()
    t = t + " | ×" + @hilbert.fmt_d(x.gain(), 2) + " | " + c.1.to_string()
    t = t + " | " + (if x.acok { "✔" } else { "✘" }) + " |"
    println(t)
  }
  println("")
  println(
    "**誠實邊界。** 方陣滿秩的大增益來自「上界憑證免費」。一換成秩虧，",
  )
  println(
    "上界憑證要做一次 r 階精確求逆加 (n−r) 次張成驗證，增益掉到 ×1.1 上下。",
  )
  println(
    "這條重構救得了「秩滿不滿」，救不了「秩虧多少」。",
  )
  println("")
}

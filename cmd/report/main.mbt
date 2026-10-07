// ============================================================================
//  cmd/report — 以 Markdown 輸出完整評審報告（含每條目之定義／算式／定理／
//  證明／義務自證結果）。
//  用法：moon run cmd/report > docs/評審報告.md
// ============================================================================

///|
fn h(level : Int, text : String) -> Unit {
  println("#".repeat(level) + " " + text)
  println("")
}

///|
fn p(text : String) -> Unit {
  println(text)
  println("")
}

///|
fn group_name(code : String) -> String {
  let mut g = 'Z'
  for c in code {
    g = c
    break
  }
  if g == 'A' {
    "A 群 · 體、純量與核心工具"
  } else if g == 'B' {
    "B 群 · 空間公理檢驗（具體空間）"
  } else if g == 'C' {
    "C 群 · 矩陣核心演算法"
  } else if g == 'D' {
    "D 群 · 抽象內積空間演算法"
  } else if g == 'E' {
    "E 群 · 具體空間之專屬定理"
  } else if g == 'F' {
    "F 群 · 空間構造子（組合爆炸）"
  } else if g == 'G' {
    "G 群 · 外代數與行列式幾何"
  } else if g == 'H' {
    "H 群 · 數值線性代數（ℝ 軌道．殘差憑證）"
  } else if g == 'I' {
    "I 群 · 四元數代數與旋轉群"
  } else if g == 'J' {
    "J 群 · 多項式與組合核心"
  } else if g == 'K' {
    "K 群 · 加速層 ℤ 管（純整數純 CRT 篩選）"
  } else if g == 'L' {
    "L 群 · 加速層 ℚ 管（Fp 層級有理數重建篩選）"
  } else {
    "M 群 · 加速層 𝔽[x] 管（多項式純 CRT 篩選）"
  }
}

///|
fn main {
  let cat = @hilbert.catalogue()
  let results : Array[@hilbert.Check] = []
  let mut passed = 0
  let mut instances = 0
  for a in cat {
    let c = (a.run)()
    results.push(c)
    instances = instances + c.trials
    if c.ok {
      passed = passed + 1
    }
  }

  // ---------------------------------------------------------------- 標題
  h(1, "公理化向量空間與有限維內積空間（MoonBit 實作）")
  p(
    "**模組**：`axiom/hilbert` v0.1.2　**語言**：MoonBit　**第三方依賴**：無（僅使用編譯器自帶之 core/builtin）",
  )
  p(
    "**評審準則條目**：" +
    cat.length().to_string() +
    " 條（要求 > 80 條）　**全部通過**：" +
    passed.to_string() +
    "/" +
    cat.length().to_string() +
    "　**驗證實例總數**：" +
    instances.to_string(),
  )
  p(
    "本文件由程式自動產生：`moon run cmd/report`。每一條目之「義務自證」皆於產生報告時實際執行，表中之判定與實例數為該次執行之真實輸出。",
  )

  // ---------------------------------------------------------------- 方法論
  h(2, "一、設計原則與證明方法論")
  h(3, "1.1 零第三方依賴")
  p(
    "`moon.mod` 之依賴區為空，函式庫本體之 import 區亦為空；連 `@math` 亦未使用 —— `sqrt`／`sin`／`cos`／`atan2`／`exp` 全部自行以 Newton 迭代與 Taylor 級數實作（kernel.mbt），有理數、複數、四元數之算術亦全部自建。",
  )
  h(3, "1.2 兩條算術軌道")
  println("| 軌道 | 純量體 | 判等 | 證明形態 |")
  println("| --- | --- | --- | --- |")
  println(
    "| 精確軌道 | ℚ（BigInt 既約分數）、ℚ(i)、ℚ 上之四元數 | 結構相等（無誤差） | 代數恆等式於隨機實例上**精確**成立 |",
  )
  println(
    "| 數值軌道 | Double | 相對 ε = 10⁻⁹ | 事後殘差憑證 ‖R(X̂)‖ ≤ ε（後向穩定性） |",
  )
  println("")
  h(3, "1.3 「義務自證」之形式化地位")
  p(
    "每條準則都附一個可執行之 *proof obligation*。於精確軌道上，公理與恆等式皆為座標與純量之多項式映射（次數 ≤ 2 或 ≤ 3）。若某恆等式不成立，其差為非零多項式 P；於取樣集 S ⊂ ℚ（|S| ≥ 52 個小有理數）隨機取值時，由 **Schwartz–Zippel 引理**：",
  )
  p("> Pr[P(ξ) = 0] ≤ deg P / |S| ≤ 2/52 < 0.04，")
  p(
    "故 t 次獨立實例全通過而命題為假之機率 ≤ 0.04^t（t = 24 時 < 10⁻³⁴）。於數值軌道上，我們不宣稱 X̂ = X，而是驗證可機器檢查之殘差不等式，配合後向穩定性定理即得「X̂ 為一個近鄰問題之精確解」。",
  )
  p(
    "此外，每一條目之原始碼區塊註解中載有**定義／命題／定理／證明**（紙上證明），報告之對應欄位為其摘要；程式只負責把「證明之可檢查推論」逐例驗證，兩者互補。",
  )

  // ---------------------------------------------------------------- 空間清單
  h(2, "二、空間清單")
  p(
    "**18 種具體空間建構**（涵蓋題目所列全部空間；皆附完整公理檢驗，見 B 群）：",
  )
  println("| 代號 | 空間 | 維數 | 內積 |")
  println("| --- | --- | --- | --- |")
  println("| S1 | 標準歐氏空間 𝔽ⁿ | n | Σ xᵢ‾yᵢ |")
  println("| S2 | 么正空間 ℂⁿ | n | Σ xᵢ‾yᵢ（Hermitian） |")
  println(
    "| S3 | 有限集合上之函數空間 𝔽^S（加權） | \\|S\\| | Σ w_s f(s)‾g(s) |",
  )
  println(
    "| S4 | 子空間／列空間 col(A)／列空間 row(A)／核 ker(A) | rank 或 n−rank | 承襲環繞空間 |",
  )
  println("| S5 | 矩陣空間 M_{m×n} | mn | tr(AB\\*) |")
  println("| S6 | 對稱矩陣空間 Sym_n | n(n+1)/2 | tr(AB\\*) |")
  println("| S7 | 反對稱空間 Skew_n = so(n) | n(n−1)/2 | tr(AB\\*) |")
  println("| S8 | 對角矩陣空間 Diag_n | n | tr(AB\\*) |")
  println(
    "| S9 | 複 Hermitian 空間 Herm_n(ℂ)（實內積空間） | n² | Re tr(AB\\*) |",
  )
  println("| S10 | 跡零空間 sl_n | n²−1 | tr(AB\\*) |")
  println(
    "| S11 | 多項式空間 P（L²[−1,1]） | n | ∫₋₁¹ p‾q dx |",
  )
  println(
    "| S12 | 多項式空間 P（L²[0,1]，Hilbert Gram） | n | ∫₀¹ p‾q dx |",
  )
  println(
    "| S13 | 多項式空間 P（離散點值） | n | Σ_k p(t_k)‾q(t_k) |",
  )
  println(
    "| S14 | 多變量多項式空間（Bombieri 內積） | C(m+d,d) | Σ (α!/\\|α\\|!) f_α‾g_α |",
  )
  println(
    "| S15 | 多變量多項式空間（係數內積） | C(m+d,d) | Σ f_α‾g_α |",
  )
  println(
    "| S16 | 四元數空間 ℍⁿ（實內積空間） | 4n | Σ Re(‾pᵢqᵢ) |",
  )
  println("| S17 | 外冪 Λᵏ(𝔽ⁿ) | C(n,k) | ⟨e_I,e_J⟩ = δ_IJ |")
  println("| S18 | 全外代數 Λ(𝔽ⁿ) | 2ⁿ | 分次正交 |")
  println("")
  p(
    "**7 類空間構造子**（可任意巢狀組合，見 F 群）：直和 `⊕`、張量積 `⊗`、對偶 `V*`、`Hom(V,W)`、實化（ℂ→ℝ）、內積扭曲（換度量）、子空間。",
  )
  p(
    "組合爆炸：D 群之 23 條抽象演算法只依賴 `IPSpace` 介面，故可施加於上述任一空間與任一組合空間之上 —— 條目 F-09 即以 6 個組合空間（P⊗Q、Q⊗E、P\\*、(P⊗E)\\*、Hom(P,Q)、P\\*⊗E\\*）重跑公理與演算法作為執行證據。",
  )

  // ---------------------------------------------------------------- 總表
  h(2, "三、評審準則目錄（總表）")
  println(
    "| 編號 | 名稱 | 類別 | 適用空間 | 軌道 | 實例 | 判定 |",
  )
  println("| --- | --- | --- | --- | --- | --- | --- |")
  for i in 0..<cat.length() {
    let a = cat[i]
    let c = results[i]
    println(
      "| " +
      a.code +
      " | " +
      a.zh +
      " | " +
      a.cat +
      " | " +
      a.spaces +
      " | " +
      a.track +
      " | " +
      c.trials.to_string() +
      " | " +
      (if c.ok { "✔ 通過" } else { "✘ 失敗" }) +
      " |",
    )
  }
  println("")

  // ---------------------------------------------------------------- 詳述
  h(
    2, "四、逐條詳述（定義 · 算式 · 命題／定理 · 證明 · 義務自證）",
  )
  let mut group = ""
  for i in 0..<cat.length() {
    let a = cat[i]
    let c = results[i]
    let g = group_name(a.code)
    if g != group {
      group = g
      h(3, g)
    }
    h(4, a.code + "　" + a.zh)
    println(
      "- **類別**：" +
      a.cat +
      "　　**適用空間**：" +
      a.spaces +
      "　　**軌道**：" +
      a.track,
    )
    println("- **定義**：" + a.deff)
    println("- **算式**：" + a.formula)
    println("- **命題／定理**：" + a.thm)
    println("- **證明**：" + a.proof)
    println(
      "- **義務自證**：" +
      (if c.ok { "✔ 通過" } else { "✘ 失敗" }) +
      "　（實例數 " +
      c.trials.to_string() +
      "）　" +
      c.detail,
    )
    println("")
  }

  // ---------------------------------------------------------------- 加速層
  h(2, "五、加速層實測（K／L／M 群）")
  p(
    "加速層把 A–J 之精確演算法重新實作於「多模 𝔽p → 中國剩餘定理提升 → 有理重建 → 事後憑證」之管線上。其正當性不靠經驗，而靠三段論證：",
  )
  println(
    "1. **語義不變**：環同態 φ_p 與多項式映射交換（推論 Λ1-2），故模路徑算的就是同一個代數量；",
  )
  println(
    "2. **提升唯一**：∏p > 2·（Hadamard／係數）界時對稱提升唯一（定理 Λ1-3）、2ND < M 時有理重建唯一（定理 Λ1-5）；",
  )
  println(
    "3. **無條件憑證**：C 管以精確算術驗證 Ax = b、AX = I、TA = R、G \\| f ∧ G \\| g、f(xᵢ) = yᵢ 等，",
  )
  println(
    "   憑證通過即正確，與素數個數、重建界、機率假設皆無關 —— 機率只影響效率，不影響正確性。",
  )
  println("")
  h(3, "5.1 成本模型")
  p(
    "本報告之增益以**確定性成本模型**計量，而非掛鐘時間：schoolbook 下一次 BigInt 乘法／除法計 ⌈bits(a)/64⌉·⌈bits(b)/64⌉ 次單字乘法，𝔽p 之一次模乘計 1 次。此度量與平台、JIT、快取無關，可重現、可審計。掛鐘時間另見 `moon run cmd/accel`。",
  )
  h(3, "5.2 實測對照表")
  println(
    "| 項目 | 基準字乘 | 加速字乘 | 增益 | 中間量位元（基準→加速） | 素數 | 輸出一致／憑證 |",
  )
  println("| --- | --- | --- | --- | --- | --- | --- |")
  let bench = @hilbert.accel_bench_table()
  for r in bench {
    let g = @hilbert.AccelStat::gain(r)
    let gs = if g >= 1000.0 {
      "×" + g.to_int64().to_string()
    } else {
      "×" + @hilbert.fmt_d(g, 2)
    }
    println(
      "| " +
      r.aname +
      " | " +
      r.base_wmul.to_string() +
      " | " +
      r.fast_wmul.to_string() +
      " | **" +
      gs +
      "** | " +
      r.base_bits.to_string() +
      " → " +
      r.fast_bits.to_string() +
      " | " +
      r.nprimes.to_string() +
      " | " +
      (if r.certified { "✔" } else { "✘" }) +
      " |",
    )
  }
  println("")
  p(
    "最後一列為**誠實反例**：以 schoolbook 乘法計，由根造多項式之積樹反而比線性累積更貴（平衡乘法 m²w² > 偏斜乘法），分派器對此必須回答「不加速」。本庫不以選擇性報喜建立「正向優化」之宣稱。",
  )
  h(3, "5.3 分派器與正向性定理")
  p(
    "**定理 Λ3-13（正向性）**：若判定函數 δ 滿足 δ(params) = true ⇒ cost_fast(params) < cost_base(params)，則「基準 ⊕ δ 分派」之成本逐點 ≤ 基準成本，故分派後之系統必為正向優化。證明：δ 為真時取較小者，為假時取基準，逐點不劣。∎",
  )
  p(
    "δ 只看規模參數 (n, b, d) 而不看資料，成本模型之參數（Bareiss 中間量 ≈ 0.6·n·(b+6) 位元、每樞軸一次 Fermat 求逆 46 次乘法、CRT 累積 1.5k²、NTT 3·sz·log sz）皆以實測網格校準，並加 25% 安全邊際（pred_fast·5 < pred_base·4）才切換。目錄 **K-10／L-10／M-08** 於參數網格上逐點實測此蘊含式，無一反例。",
  )
  println("| ℤ 行列式 n＼位元 | 8 | 32 | 128 | 512 | 2048 |")
  println("| --- | --- | --- | --- | --- | --- |")
  for n in [8, 12, 16, 20, 32] {
    let mut row = "| n = " + n.to_string() + " |"
    for b in [8, 32, 128, 512, 2048] {
      row = row +
        (if @hilbert.plan_zdet(n, b).use_fast {
          " **加速** |"
        } else {
          " · |"
        })
    }
    println(row)
  }
  println("")
  println("| ℤ[x] 乘法 deg＼位元 | 32 | 128 | 512 | 2048 | 8192 |")
  println("| --- | --- | --- | --- | --- | --- |")
  for d in [16, 32, 64, 128, 256] {
    let mut row = "| deg = " + d.to_string() + " |"
    for b in [32, 128, 512, 2048, 8192] {
      row = row +
        (if @hilbert.plan_zpolymul(d, b).use_fast {
          " **加速** |"
        } else {
          " · |"
        })
    }
    println(row)
  }
  println("")
  h(3, "5.4 三層 CRT 之統一視角")
  p(
    "本層之三個群分別對應三種「CRT 同構」，形式完全平行：",
  )
  println("| 層 | 同構 | 求值 | 插值／提升 | 群 |")
  println("| --- | --- | --- | --- | --- |")
  println(
    "| ℤ | ℤ/Mℤ ≅ ∏ ℤ/pᵢℤ | 取餘數 x mod pᵢ | Garner 累進 + 對稱提升 | K |",
  )
  println(
    "| ℚ | ℚ ↪ ℤ/Mℤ（分母可逆時） | n·d⁻¹ mod M | 格–歐幾里得有理重建 | L |",
  )
  println(
    "| 𝔽[x] | 𝔽[x]/∏(x−aᵢ) ≅ ∏ 𝔽[x]/(x−aᵢ) | 求值 f(aᵢ) | Newton／NTT 逆變換 | M |",
  )
  println("")
  p(
    "三者可任意複合：目錄 M-03（ℤ[x] 乘法）同時用上係數層之 ℤ-CRT 與變數層之 𝔽[x]-CRT；M-04（ℚ[x] 乘法）再疊一層清分母。這正是「不同空間建構互相結合」在計算層面的體現。",
  )

  // ---------------------------------------------------------------- 結論
  h(2, "六、總結")
  println("| 項目 | 數值 |")
  println("| --- | --- |")
  println("| 評審準則條目 | " + cat.length().to_string() + " |")
  println("| 通過 | " + passed.to_string() + " |")
  println("| 失敗 | " + (cat.length() - passed).to_string() + " |")
  println("| 驗證實例總數 | " + instances.to_string() + " |")
  println("| 具體空間 | 18（S1–S18） |")
  println("| 空間構造子 | 7 |")
  println("| 第三方依賴 | 0 |")
  println("")
  h(3, "6.1 類別分佈")
  println("| 類別 | 條目數 |")
  println("| --- | --- |")
  for pr in @hilbert.category_counts() {
    println("| " + pr.0 + " | " + pr.1.to_string() + " |")
  }
  println("")
  h(3, "6.2 原始碼檔案")
  println("| 檔案 | 內容 |")
  println("| --- | --- |")
  println(
    "| `kernel.mbt` | PRNG、自製 sqrt/sin/cos/atan2、格式化工具 |",
  )
  println(
    "| `scalar.mbt` | `Scalar` 純量體抽象介面（trait）與 Double 實作 |",
  )
  println("| `rational.mbt` | BigInt 有理數體 ℚ（既約表示） |")
  println("| `complex.mbt` | 泛型複數 Cpx[F]（ℚ(i)、ℂ） |")
  println(
    "| `space.mbt` | `VSpace`／`IPSpace` 結構、公理檢驗器（V1–V11, B1–B5, I1–I7） |",
  )
  println(
    "| `matrix.mbt` | 矩陣核心：RREF、det、inv、LU、Kronecker、特徵多項式等（演算法 011–030） |",
  )
  println(
    "| `vecspace.mbt` | 座標空間、函數空間、子空間／列空間（S1–S4） |",
  )
  println("| `matspace.mbt` | 矩陣類空間 S5–S10 |")
  println(
    "| `polyspace.mbt` | 多項式空間 S11–S13 與 Legendre／Chebyshev／Vandermonde |",
  )
  println(
    "| `mpolyspace.mbt` | 多變量多項式空間 S14–S15（Bombieri 內積） |",
  )
  println("| `quatspace.mbt` | 四元數代數與 ℍⁿ（S16） |")
  println(
    "| `exterior.mbt` | 外代數 Λᵏ／Λ（S17–S18）、Hodge 星、叉積 |",
  )
  println(
    "| `combinators.mbt` | 空間構造子：⊕、⊗、對偶、Hom、實化、扭曲 |",
  )
  println(
    "| `ipalgo.mbt` | 抽象內積空間演算法（演算法 061–080） |",
  )
  println(
    "| `realmat.mbt` | 數值 ℝ 軌道：Cholesky/QR/SVD/特徵值/Krylov/FFT 等（演算法 081–102） |",
  )
  println(
    "| `fp.mbt` | 加速層 Λ0：𝔽p 原子層（Miller–Rabin、Montgomery 批次求逆、前向消去行列式、NTT） |",
  )
  println(
    "| `crt.mbt` | 加速層 Λ1：Garner 累進 CRT、對稱提升、有理重建、Hadamard／係數界 |",
  )
  println(
    "| `accel.mbt` | 加速層 Λ2：ℤ／ℚ 之加速演算法與 C 管憑證、成本模型、實測摘要 |",
  )
  println(
    "| `accelpoly.mbt` | 加速層 Λ3：𝔽[x] 管（求值插值、NTT 乘法、gcd 模篩、插值重建）與分派器 |",
  )
  println(
    "| `oblig_core.mbt`／`oblig_space.mbt`／`oblig_num.mbt`／`oblig_accel.mbt` | 全部可執行之證明義務 |",
  )
  println(
    "| `catalogue.mbt` | 本評審準則目錄（定義／算式／定理／證明／義務） |",
  )
  println("| `cmd/main`／`cmd/report` | 執行器與本報告產生器 |")
  println("")
  p(
    "執行方式：`moon check`（型別檢查）→ `moon test`（單元測試）→ `moon run cmd/main`（逐條義務自證）→ `moon run cmd/report`（產生本報告）。",
  )
}

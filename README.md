# axiom/hilbert — 公理化向量空間與有限維內積空間（MoonBit）

以 **MoonBit** 從零（**零第三方依賴**）建構之向量空間／有限維內積空間函式庫：
18 種具體空間建構 × 7 種空間構造子 × **172 條評審準則演算法**，每一條都附
**定義 · 算式 · 命題／定理 · 證明 · 可執行之義務自證**。

```
條目總數 172（題目要求 > 80）　　通過 172／172　　驗證實例 11,529　　6.1 s
基礎層 A–J 140 條　　加速層 K/L/M 28 條（純 CRT 篩選 · Fp 層級有理重建）
結構律 N 群 4 條（演算法合成：吃演算法、吐演算法）
```

## 快速開始

```bash
moon check            # 型別檢查（0 error, 0 warning）
moon test             # 單元測試（含整份目錄之迴歸測試）
moon run cmd/main     # 逐條執行 172 條義務自證，列印結果表
moon run cmd/accel    # 加速層實測：成本模型對照表 + 分派器決策網格
moon run cmd/audit    # 逐條目掛鐘量測（TSV，供評估報告使用）
moon run cmd/report > docs/評審報告.md   # 產生完整 Markdown 評審報告
```

完整報告：[`docs/評審報告.md`](docs/評審報告.md)　|　
品質稽核：[`docs/演算法評估與汰弱留強建議.md`](docs/演算法評估與汰弱留強建議.md)　|　
生成器設計：[`docs/N群設計構想—結構律與演算法合成.md`](docs/N群設計構想—結構律與演算法合成.md)

> **稽核結論摘要**：原 168 條平均 70.6/100。查出 2 條掛在加速層卻從未加速的敗筆
> （L-05 ×0.15、L-08 ×0.6）、16 條重複計數、47 個無人呼叫的 `pub fn`。
> 獨立演算法實數為 **149 條**（仍為要求的 1.86 倍）。詳見稽核報告。
>
> **稽核後已執行**：(1) 查出並修掉全庫單點瓶頸 —— `Q::make` 的 BigInt gcd
> （Int64 快路徑，ℚ 運算 ×4.7～×5.9）；(2) 補 `plan_zadj` 門檻（交叉點 n≈7）；
> (3) L-05／L-08 改列誠實反例；(4) 五條最弱義務補強（1→10、2→24、2→19、3→9、4→30 實例），
> 其中兩條升格為刻劃定理；(5) 新增 N 群演算法合成器。

## 為何「零依賴」

`moon.mod` 之依賴區為空，函式庫本體（root `moon.pkg`）之 import 區亦為空，
連 `@math` 都未使用。（唯一例外：`cmd/accel` 這支**執行檔**為了量掛鐘時間而 import
`moonbitlang/core/bench` —— 那是編譯器自帶之標準庫而非第三方套件，且函式庫本體與
全部 172 條義務自證皆不依賴它。）

| 需求 | 自建實作 |
| --- | --- |
| `sqrt` | Newton 迭代（`kernel.mbt`），附殘差憑證 |
| `sin` / `cos` | 區間歸約 + Taylor 級數 |
| `atan2` | 級數 + 象限修正 |
| `exp` | 縮放–平方 + Taylor |
| 有理數 ℚ | BigInt 既約分數（`rational.mbt`） |
| 複數 ℚ(i)／ℂ | 泛型 `Cpx[F]`（`complex.mbt`） |
| 四元數 ℍ | `Quat[F]`（`quatspace.mbt`） |
| 亂數 | xorshift64\*（確定性、可重現） |

## 兩條算術軌道

| 軌道 | 純量體 | 判等 | 證明形態 |
| --- | --- | --- | --- |
| 精確 | ℚ、ℚ(i)、ℚ 上四元數 | 結構相等（無捨入） | 恆等式於隨機實例**精確**成立；配合 Schwartz–Zippel 界，偽通過機率 < 10⁻³⁴ |
| 數值 | `Double` | 相對 ε = 10⁻⁹ | 事後殘差憑證 ‖R(X̂)‖ ≤ ε，依後向穩定性即「近鄰問題之精確解」 |

## 空間清單

**具體空間 S1–S18**：歐氏空間 𝔽ⁿ · 么正空間 ℂⁿ · 有限集合上之函數空間（加權）·
子空間／列空間 col(A)／列空間 row(A)／核 ker(A) · 矩陣空間 M\_{m×n} · 對稱矩陣 Sym\_n ·
反對稱 so(n) · 對角矩陣 Diag\_n · 複 Hermitian Herm\_n(ℂ) · 跡零 sl\_n ·
多項式空間（L²[−1,1]／L²[0,1]／離散點值）· 多變量多項式（Bombieri／係數內積）·
四元數空間 ℍⁿ · 外冪 Λᵏ(𝔽ⁿ) · 全外代數 Λ(𝔽ⁿ)。

**空間構造子**：直和 `⊕`、張量積 `⊗`、對偶 `V*`、`Hom(V,W)`、實化（ℂ→ℝ）、
內積扭曲（換度量）、子空間 —— 可任意巢狀組合，抽象演算法自動適用（條目 F-09）。

## 目錄分群

| 群 | 內容 | 條目數 |
| --- | --- | --- |
| A | 體、純量與核心工具 | 10 |
| B | 空間公理檢驗（V1–V11 · B1–B5 · I1–I7） | 15 |
| C | 矩陣核心演算法 | 20 |
| D | 抽象內積空間演算法（對任意空間泛型） | 23 |
| E | 具體空間之專屬定理 | 16 |
| F | 空間構造子（組合爆炸） | 9 |
| G | 外代數與行列式幾何 | 9 |
| H | 數值線性代數（殘差憑證） | 25 |
| I | 四元數代數與旋轉群 | 7 |
| J | 多項式與組合核心 | 6 |
| K | 加速層 ℤ 管（純整數純 CRT 篩選） | 10 |
| L | 加速層 ℚ 管（Fp 層級有理數重建篩選） | 10 |
| M | 加速層 𝔽[x] 管（多項式純 CRT 篩選） | 8 |

## 加速層（K／L／M 群）

把 A–J 之精確演算法重寫到「多模 𝔽p → CRT 提升 → 有理重建 → **事後憑證**」之管線上。
正確性不靠機率論證：B 管（多模）負責*猜*，C 管（憑證）負責*證* —— 以精確算術驗證
`Ax = b`、`AX = I`、`TA = R`、`G | f ∧ G | g`、`f(xᵢ) = yᵢ`，憑證通過即無條件正確。

| 項目 | 基準 | 加速 | 增益 |
| --- | --- | --- | --- |
| ℤ 行列式 n=16（256 位元係數） | Bareiss 無分數消去 | 多模 CRT | **×4.4** |
| ℚ 線性方程組 n=14 | 高斯消去 | 多模＋重建＋憑證 | **×7.6** |
| ℚ 反矩陣 n=12 | 高斯–Jordan | 多模＋重建＋憑證 | **×8.7** |
| 特徵多項式 n=11 | ℚ Faddeev–LeVerrier | 多模 Hessenberg CRT | **×9.8** |
| 最小二乘 20×10 | ℚ 正規方程 | 𝔽p 組裝＋重建 | **×9.2** |
| ℚ[x] 乘法 deg 64 | ℚ 卷積（每步 gcd） | 清分母＋多模 NTT | **×5.3** |
| ℤ[x] gcd deg 16 | ℚ 歐幾里得 | 模 p 篩＋整除性憑證 | **×4084** |
| 【反例】由 32 根造多項式 | 線性累積 | 積樹 | ×0.60 ✘ |

增益以**確定性成本模型**計量（schoolbook 下 BigInt 乘法 = ⌈bits(a)/64⌉·⌈bits(b)/64⌉
次單字乘法），與平台無關、可重現、可審計；掛鐘時間另見 `moon run cmd/accel`。

最後一列是**誠實反例**：schoolbook 算術下積樹比線性累積更貴，分派器對此回答「不加速」。
**定理 Λ3-13（正向性）**：若判定函數 δ 滿足 `δ = true ⇒ cost_fast < cost_base`，
則「基準 ⊕ δ 分派」之成本逐點不劣於基準。目錄 **K-10／L-10／M-08** 在參數網格上
逐點實測此蘊含式，無一反例 —— 「正向優化」因此是被自證之性質，而非宣稱。

## 原始碼地圖

| 檔案 | 內容 |
| --- | --- |
| `kernel.mbt` | PRNG、自製 sqrt/sin/cos/atan2、格式化 |
| `scalar.mbt` | `Scalar` 純量體 trait（ℚ／ℚ(i)／Double 共用介面） |
| `rational.mbt` · `complex.mbt` | ℚ（BigInt）與泛型複數 |
| `space.mbt` | `VSpace`／`IPSpace` 與公理檢驗器 |
| `matrix.mbt` | RREF、det、inv、LU、Kronecker、特徵多項式、Cayley–Hamilton |
| `vecspace.mbt` · `matspace.mbt` · `polyspace.mbt` · `mpolyspace.mbt` · `quatspace.mbt` · `exterior.mbt` | 具體空間 S1–S18 |
| `combinators.mbt` | 空間構造子 |
| `ipalgo.mbt` | 抽象內積空間演算法（GS／投影／Riesz／伴隨／Fourier／最小二乘…） |
| `realmat.mbt` | 數值軌道：Cholesky／QR／SVD／Jacobi／CG／Lanczos／Arnoldi／FFT／Haar |
| `fp.mbt` | 加速層 Λ0：𝔽p 原子層（Miller–Rabin、Montgomery 批次求逆、NTT） |
| `crt.mbt` | 加速層 Λ1：Garner CRT、對稱提升、有理重建、Hadamard／係數界 |
| `accel.mbt` · `accelpoly.mbt` | 加速層 Λ2／Λ3：ℤ／ℚ／𝔽[x] 管、C 管憑證、成本模型、分派器 |
| `oblig_core.mbt` · `oblig_space.mbt` · `oblig_num.mbt` · `oblig_accel.mbt` · `oblig_nlaw.mbt` | 172 條可執行證明義務 |
| `nlaw.mbt` | **N 群：結構律與演算法合成** —— 空間表達式 AST、高階律檢驗器、Kronecker 律族、誠實反例庫 |
| `catalogue.mbt` | 評審準則目錄（定義／算式／定理／證明／義務） |
| `cmd/main` · `cmd/report` · `cmd/accel` · `cmd/audit` | 執行器、報告產生器、加速層實測、逐條稽核量測 |

## 授權

Apache-2.0

# AGENTS.md — 專案慣例（給貢獻者與自動化代理）

> 本檔是本庫的**行為契約**。違反者 CI 會直接紅燈（見 §6）。
> 語言：文件、註解、報表一律繁體中文；程式碼識別字沿用既有風格。

---

## 1. 版號：不另立版號

- 本專案**只用分支名 `v0.1.2` 標識版本**。所謂「第十二輪」「第十三輪」只是該分支上的
  commit 序列，**不是**版號，不得寫成 `v0.1.3`、`v1.2.0` 之類。
- `moon.mod` 的 `version`、`cmd/report` 的報表頭、`cmd/main` 的標題列、
  所有 `docs/` 之版本字樣一律為 `0.1.2`／`v0.1.2`。
- 新增變更直接 commit 到 `v0.1.2`；`main` 由維護者決定何時快進。

## 2. 警告政策（`moon.mod` 是唯一開關處）

- 六類選擇性警告**常開**，現況皆為 0，不得回退：
  `missing_doc`、`unqualified_record`、`prefer_readonly_array`、
  `missing_invariant`、`missing_reasoning`、`unnecessary_annotation`。
- **結構字面值定案寫法**：`let vs = VSpace::{ … }`
  —— 以前綴表型別，**不再**重複 `let` 之型別標註。
  寫 `: VSpace[…]` 會觸發 E0073；省掉前綴會觸發 E0084。兩者互斥，唯此寫法兩全。
- impl 之方法掛載一律以顯式 `extend` 宣告（`rational.mbt`／`complex.mbt` 為範例）；
  本庫一律以 `Trait::method` 呼叫（`Scalar::s_add(a, b)`），不靠隱式方法推廣。
- 迴圈若被要求補 proof 標註，`proof_invariant` 必須寫**真命題**（上下界、索引界、值域），
  `proof_reasoning` 寫**具體終止或保持理由**；不得以空話充數。

## 3. 生成物：不得手改、不得格式化

- `oblig_auto.mbt` 由 `moon run cmd/genoblig` 產生，**逐位元組可重現**（N-45 之義務）。
- 修改後必須 `moon run cmd/genoblig | diff - oblig_auto.mbt` 為空。
- 它是 `moon fmt` 的唯一例外（生成器輸出尚未正則化）。其餘 `.mbt` 一律 fmt 乾淨。

## 4. 抽樣政策與指紋

- 受管轄條目之次數與下限登記見 `policy.mbt`；`cmd/audit` 第 8 欄 policy 為對帳依據，
  **違反必須為 0**（現況：受管轄 134 條、違反 0 條）。
- 既有條目之指紋**一位元不得變**，除非該輪明示為演算法修訂；
  任何重構都應維持「目錄條目數／實例數／政策對帳」三項不變或如實上升。
- 量測數字一律由程式在產碼前當場量出並釘入斷言；**不得手寫常數充數**。

## 5. 誠實原則

- 加速層若無實際增益，**如實列為反例**（如 L-05 ×0.15、L-08 ×0.6、
  由根造多項式之積樹 ×0.60），不得美化成「已優化」。
- 驗證失敗若為求解器逾時，必須與「命題為假」分開陳述。

## 6. 閘門（本機與 CI 一致）

```bash
moon check --target all --deny-warn                        # 1 型別（預設提示）
moon check --target all --warn-list "+all" --deny-warn     # 2 嚴格提示（全部）
moon test                                                  # 3 目錄迴歸（6/6）+ 目錄與政策對帳
moon run cmd/genoblig | diff - oblig_auto.mbt              # 4 生成器可重現（N-45）
moon run cmd/main | grep -q "全部義務通過"                  # 5 全庫自證判準
moon run cmd/report | diff - docs/評審報告.md               # 6 報表與文件一致
moon check --fmt                                           # 7 格式（僅 oblig_auto.mbt 例外）
moon info && git diff --exit-code -- '*.mbti'              # 8 公共介面漂移
```

另加 `.github/workflows/toolchain-drift.yml` 每日以最新工具鏈探測閘門 1–2。

## 7. 開發迴路

```bash
moon run cmd/main -- --only K        # 只跑 K 群（秒級）
moon run cmd/main -- --only N-8      # 只跑 N-8x
HILBERT_ONLY=K,L moon run cmd/main   # 或以環境變數指定多前綴
moon run cmd/main -- --help          # 用法
```

全庫自證約 2 分鐘；日常迭代請用 `--only`，完整跑留給 CI 與發版。

## 8. 新增一條義務的流程

1. 於 `catalogue.mbt` 掛入條目（編號沿用群組前綴：A–M、N-xx）。
2. 於 `oblig_*.mbt` 寫義務自證；量測值由程式當場算出並釘入 `detail`。
3. 若屬受管轄條目，於 `policy.mbt` 登記 target／floor。
4. 更新 `README.md` 之數字、`docs/評審報告.md`（由 `cmd/report` 產生）、必要時 `docs/` 各表。
5. 依 §6 跑齊閘門；`genoblig` 若受影響則重生 `oblig_auto.mbt`。

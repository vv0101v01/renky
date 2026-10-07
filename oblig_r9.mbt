///|
/// N-68 之義務：非建構子。
pub fn ob_n68() -> Check {
  let mut ok = true
  let rows = nonctor_scan()
  if rows.length() != 3 {
    ok = false
  }
  // 商空間：45 可用、45 SPD、0 保 Gram、45 維數相符
  if rows[0].1 != 45 || rows[0].2 != 45 || rows[0].3 != 0 || rows[0].4 != 45 {
    ok = false
  }
  // 遺忘內積：45/45/22/45
  if rows[1].1 != 45 || rows[1].2 != 45 || rows[1].3 != 22 || rows[1].4 != 45 {
    ok = false
  }
  // 完備化：45/45/45/45
  if rows[2].1 != 45 || rows[2].2 != 45 || rows[2].3 != 45 || rows[2].4 != 45 {
    ok = false
  }

  // ── 判準：宣稱保 Gram 與實測保 Gram 必須一致 ───────────
  let (nn, claimed, measured, agree) = nonctor_verdict()
  if nn != 3 || claimed != 1 || measured != 1 || agree != 3 {
    ok = false
  }

  // ── 商度量之獨立覆核：Schur 補 = 到 W 的距離平方 ────────
  let r0 = ob_rng()
  let (qt, qok) = quotient_metric_check(r0)
  if qt != 4 || qok != 4 {
    ok = false
  }

  // ── 遺忘內積究竟丟掉多少 ────────────────────────────────
  let (ft, fnt) = forget_destroys()
  if ft != 45 || fnt != 23 {
    ok = false
  }
  // 22 保 Gram + 23 非平凡 = 45，兩個數字必須互補
  if rows[1].3 + fnt != ft {
    ok = false
  }

  // ── 完備化在有限維是恆等 ────────────────────────────────
  let (ct, dev) = completion_real_dev()
  if ct != 45 || dev != 0.0 {
    ok = false
  }

  // ── 兩側對照：商空間不可能被誤當成重寫規則 ──────────────
  let r1 = ob_rng()
  let (nt, nw) = quotient_not_a_rule(r1)
  if nt != 3 || nw != 3 {
    ok = false
  }
  mk_check(
    "N-68 非建構子：商空間、遺忘內積、完備化",
    ok,
    45 * 3 + qt + nt + 8,
    "第七輪問「7 個建構子還是非建構子」時選了建構子一側，理由是函子性可以逐格檢查（SPD 進、SPD 出、維數有封閉公式）。非建構子會把結構丟掉，驗起來要換一套語言 —— 這一條把那套語言補上。三個非建構子各丟掉不同的東西：**商空間 V/W** 丟維數（取 W = 前 ⌊n/2⌋ 個座標，商度量 ‖[v]‖ = min_{w∈W}‖v−w‖ 的 Gram 是 Schur 補 G₂₂ − G₂₁G₁₁⁻¹G₁₂）；**遺忘內積** 丟度量（G ↦ I）；**完備化** 什麼都不丟（有限維已完備，G ↦ G，只有純量體由 ℚ 走向 ℝ）。**本條的判準不是宣告，是量出來的。** 一個運算能不能當中端的重寫規則，就看它過不過類 A 的「Gram 逐元不變」這一關。三個非建構子在 45 個註冊空間上逐一量：商空間 0/45 保 Gram（連維數都變了）、遺忘內積 22/45、完備化 45/45。註冊表裡宣稱保 Gram 的恰 1 個，實測保 Gram 的也恰 1 個，兩者逐條相符 3/3 —— 若有人把 ncclaim 寫錯，這條會當場失敗。於是「完備化」這個聽起來最像分析學的操作，在三者中是**唯一不破壞結構**的，而它正是雙軌比較之所以有意義的理由。**遺忘內積那個 22 值得看一眼。** 45 個註冊空間裡有 23 個的 Gram 不是單位陣，22 個是；22 + 23 = 45，義務逐一核對這個互補關係。也就是說「遺忘內積」在半數空間上根本沒丟掉東西 —— 它丟掉的量，恰好等於註冊表裡有多少空間帶著非平凡的度量。**商度量要獨立覆核。** Schur 補是算出來的，但「它就是商度量的 Gram」是一條命題：對 v = (0,y)，min_x (x,y)ᵀG(x,y) = yᵀ·Schur·y。義務用最小化點 x* = −G₁₁⁻¹G₁₂y 代回去，逐式比對 4/4。順帶確認 Schur 補保正定（SPD 的 Schur 補仍 SPD），45/45。",
  )
}

///|
/// N-69 之義務：L-05″ 整數分解憑證。
pub fn ob_n69() -> Check {
  let mut ok = true
  let (n, allok, t1, t2, win) = rank_cert_scan()
  if n != 4 || !allok {
    ok = false
  }
  if t1 != 379578838L || t2 != 17004117L {
    ok = false
  }
  if win != 4 {
    ok = false
  }

  // ── 逐格：N-58 與 N-69 的增益 ──────────────────────────
  let (b1, a1, c1, k1) = rank_cert_compare(8, 5, 16)
  if b1 != 14388878L || a1 != 13307818L || c1 != 966320L || !k1 {
    ok = false
  }
  let (b2, a2, c2, k2) = rank_cert_compare(12, 7, 16)
  if b2 != 316784929L || a2 != 268662614L || c2 != 10616836L || !k2 {
    ok = false
  }
  // 32 位元那一格：N-58 其實是**淨虧**（×0.94），N-69 是 ×18.96
  let (b3, a3, c3, k3) = rank_cert_compare(8, 4, 32)
  if b3 != 32675327L || a3 != 34605960L || c3 != 1723550L || !k3 {
    ok = false
  }
  if a3 <= b3 {
    ok = false
  }
  if c3 >= b3 {
    ok = false
  }

  // ── 兩側對照：少一個樞軸行，分解恆等式必須不成立 ────────
  if !rank_cert_control() {
    ok = false
  }
  mk_check(
    "N-69 L-05″ 秩之整數分解憑證",
    ok,
    n * 6 + 12,
    "N-58 的秩憑證在方陣滿秩時 ×81.9，秩虧時掉到 ×1.08 —— 定理 217-4 把這條邊界寫了下來，並說「本條救得了秩滿不滿，救不了秩虧多少」。貴在哪裡很清楚：上界憑證要做一次 r 階**精確有理求逆**再逐行驗張成，係數膨脹全在那裡。**便宜的做法是把分母清掉。** 設 B = A[R,S]（r×r）、d = det B，則 rank A = r ⟺ d·A = A[*,S]·adj(B)·A[R,*]。這是秩-r 分解恆等式的整數版：adj(B) 與 det(B) 都是整數，兩次矩陣乘法也都在整數上，全程沒有一個分數。而 adj 正是 K-07 的多模 CRT 管線（ν = r²、Hadamard 先驗界），n ≥ 7 時它自己就贏 ×1.7 以上。這條恆等式同時給出上下界 —— d ≠ 0 給 rank ≥ r，恆等式成立給 rank ≤ r —— 所以原本要分兩步做的事變成一步。實測（秩虧長方形，基準為受計量的 qrref_gauss）：8×8 秩 5 之 ×1.08 → **×14.89**；12×12 秩 7 之 ×1.18 → **×29.84**；合計 379,578,838 → 17,004,117（×22.3），4/4 格 N-69 較便宜。**有一格特別值得看。** 8×8 秩 4、32 位元：N-58 的憑證是 34,605,960 字乘，而基準只要 32,675,327 —— 也就是 ×0.94，**淨虧**。定理 217-4 說「救不了秩虧多少」還算客氣，在這一格它其實是負的。N-69 在同一格是 1,723,550（×18.96）。義務把這個 a3 > b3 與 c3 < b3 的關係釘死，將來誰改動任一路徑都會被擋下。**兩側對照。** 把樞軸行少取一個再驗分解恆等式 —— 必須不成立。若照樣成立，表示這條憑證對樞軸的選擇不敏感，那它就證不了「秩恰好是 r」。",
  )
}

///|
/// N-70 之義務：檢驗 N-56 的預測。
pub fn ob_n70() -> Check {
  let mut ok = true
  let (n, allsame, slower, faster, wslow, wfast) = apriori_verdict()
  if n != 12 || !allsame {
    ok = false
  }
  // 預測：先驗界在每一格都不會比較快
  if slower != 12 || faster != 0 {
    ok = false
  }
  if !(wslow > 57.0 && wslow < 58.0) {
    ok = false
  }
  if !(wfast > 0.999 && wfast < 1.001) {
    ok = false
  }

  // ── 逐格：三條管線的受害程度不同 ────────────────────────
  let tbl = apriori_verdict_table()
  if tbl.length() != 12 {
    ok = false
  }
  let mut invworst = 1.0
  let mut ldltworst = 1.0
  for r in tbl {
    let (nm, _, _, a, b, same) = r
    if !same {
      ok = false
    }
    let x = b.to_double() / a.to_double()
    if nm == "ℚ 反矩陣" && x > invworst {
      invworst = x
    }
    if nm == "Gram LDLᵀ" && x > ldltworst {
      ldltworst = x
    }
  }
  // 反矩陣受害遠比 LDLᵀ 嚴重 —— ν 小、k 小的管線更怕悲觀的先驗界
  if !(invworst > 50.0) {
    ok = false
  }
  if !(ldltworst > 1.2 && ldltworst < 1.5) {
    ok = false
  }
  if invworst <= ldltworst {
    ok = false
  }
  mk_check(
    "N-70 N-56 之預測的檢驗：砍 k 在三條管線上都沒用",
    ok,
    n * 3 + 10,
    "N-56 診斷多模路徑的主成本是 Θ(ν·k²)，並由此**預測**「砍 k 沒用」—— 把逐素數穩定判定換成先驗 Hadamard 界反而更慢，因為界是悲觀的、而成本對 k 是平方的。那條預測當時只在 LDLᵀ 一條管線上量過（×0.747、×0.775），其餘三條（qsolve_crt、qinv_crt、qrref_crt）的 ν 與 k 都小得多。**一條沒有被檢驗過的預測不算結果。** 本條補寫 qsolve_crt_ap，連同既有的 qinv_crt_ap、qldlt_crt_ap，在 (n, 位元) ∈ {4,6} × {8,16} 的網格上三條管線各跑一次，兩版輸出逐元相同 12/12（含事後憑證）。裁決：先驗界在 **12/12 格都較慢**，0 格較快，最壞一格慢 ×" +
    fmt_d(wslow, 2) +
    "。預測成立。**而且受害程度的分布本身就是診斷的佐證。** Gram LDLᵀ 最壞只慢 ×" +
    fmt_d(ldltworst, 3) +
    "，ℚ 反矩陣最壞慢 ×" +
    fmt_d(invworst, 2) +
    " —— 差了一個數量級。機制很直接：先驗界要的素數個數與真正需要的差一個常數比例，而那個比例在 k 本來就大的管線（LDLᵀ，k 可達數十）上被攤薄，在 k 本來就小的管線（反矩陣，n=4、8 位元時 k 只有個位數）上則是成倍的浪費，再被平方放大。義務把「反矩陣的受害 > LDLᵀ 的受害」這個序關係也釘死 —— 它不是附帶觀察，它是 Θ(ν·k²) 這個模型的可證偽推論。",
  )
}

///|
/// N-71 之義務：外冪與 Kron 和之特化路徑。
pub fn ob_n71() -> Check {
  let mut ok = true

  // ── 兩條恆等式先獨立覆核 ────────────────────────────────
  let r0 = ob_rng()
  let (ct, cok) = ext_cauchy_binet(r0)
  if ct != 4 || cok != 4 {
    ok = false
  }
  let r1 = ob_rng()
  let (st, sok) = ksum_sylvester_check(r1)
  if st != 4 || sok != 4 {
    ok = false
  }

  // ── 掃描 ────────────────────────────────────────────────
  let rng = ob_rng()
  let (n, same, td, ts, win, lose) = ek_scan(rng)
  if n != 12 || same != 12 {
    ok = false
  }
  if td != 8876158L || ts != 1228814L {
    ok = false
  }
  if win != 10 || lose != 2 {
    ok = false
  }

  // ── 逐形狀 ──────────────────────────────────────────────
  let r2 = ob_rng()
  let shapes = ek_by_shape(r2)
  if shapes.length() != 2 {
    ok = false
  }
  if shapes[0].1 != 6 || shapes[0].2 != 1029296L || shapes[0].3 != 282491L {
    ok = false
  }
  if shapes[1].1 != 6 || shapes[1].2 != 7846862L || shapes[1].3 != 946323L {
    ok = false
  }

  // ── 派工表至此全滿 ──────────────────────────────────────
  let r3 = ob_rng()
  let probe = SExt(SLeaf("A", rand_gram(r3, 5)), 2)
  if spec_has_path2(probe) {
    ok = false
  }
  if !spec_has_path3(probe) {
    ok = false
  }

  // ── 兩側對照：故意寫錯的恆等式必須被抓到 ────────────────
  let r4 = ob_rng()
  let (et, ec) = ek_control(r4)
  if et != 4 || ec != 4 {
    ok = false
  }
  mk_check(
    "N-71 外冪與 Kron 和之特化求解路徑",
    ok,
    n * 4 + ct + st + et + 8,
    "從 N-54 起，外冪與 Kron 和一直被當成兩側對照 —— 沒有特化路徑的形狀，兩條路線的成本必須完全相等。這個對照很好用，但它同時意味著這兩個形狀一直走物化 Gram 再 Gauss 求逆，而它們的 Gram 恰好是全庫最大的（Λ² 把 n 變成 C(n,2)，⊞ 把維數相乘）。**外冪：Cauchy–Binet 給了一個免費的答案。** C_k(A·B) = C_k(A)·C_k(B) ⇒ C_k(G)·C_k(G⁻¹) = C_k(I) = I ⇒ **C_k(G)⁻¹ = C_k(G⁻¹)**。於是「解一個 C(n,k) 階的方程」變成「解一個 n 階的方程，再造一次複合矩陣」。**Kron 和：它根本是一個 Sylvester 方程。** 以本庫的張量索引約定，(G_A ⊗ I + I ⊗ G_B)·vec(X) = vec(G_A·X + X·G_B)，所以 ⊞ 的求解就是 G_A·X + X·G_B = C。精確有理解法用特徵多項式：X = −p(−G_B)⁻¹·Σ_{k=1}^{n} aₖ Σ_{j=0}^{k−1} G_A^j·C·(−G_B)^{k−1−j}，其中 p 為 G_A 的特徵多項式。可解性條件是 spec(G_A) ∩ spec(−G_B) = ∅ —— 而兩個 Gram 都正定，一個譜全正、一個譜全負，**條件自動成立**。正定假設在這裡不是技術細節，它正好是這條路徑能用的理由。兩條恆等式都先獨立覆核（Cauchy–Binet 4/4、Sylvester 回代 4/4）才拿去用。實測：語料 12 式兩路逐元相同 12/12，成本 " +
    td.to_string() +
    " → " +
    ts.to_string() +
    "（×" +
    fmt_d(td.to_double() / ts.to_double(), 3) +
    "），10 勝 2 敗。逐形狀：外冪 ×" +
    fmt_d(shapes[0].2.to_double() / shapes[0].3.to_double(), 3) +
    "、Kron 和 ×" +
    fmt_d(shapes[1].2.to_double() / shapes[1].3.to_double(), 3) +
    "。**兩側對照必須換一種做法。** 既然每個形狀都有路徑了，「無路徑者成本相等」這個對照就沒有了。改成注入錯誤的恆等式：外冪用 C_k(G) 當作 C_k(G)⁻¹（少取一次逆），Kron 和把 G_B 的符號寫反 —— 四個都必須被抓到。派工表至此對八種形狀全有路徑（spec_has_path3 恆真），義務直接檢查同一式在 spec_has_path2 下為假、在 spec_has_path3 下為真。",
  )
}

///|
/// N-72 之義務：一元構造子的算子層規則。
pub fn ob_n72() -> Check {
  let mut ok = true
  let r0 = ob_rng()
  let tbl = uni_rule_table(r0)
  if tbl.length() != 15 {
    ok = false
  }
  // 逐條核對：對偶 5/5 成立、外冪 4/5（adj 失敗）、扭曲 3/5
  let mut dual = 0
  let mut ext = 0
  let mut tw = 0
  let mut adjext = true
  for r in tbl {
    if r.uholds {
      if r.uctor == "對偶" {
        dual = dual + 1
      }
      if r.uctor == "外冪" {
        ext = ext + 1
      }
      if r.uctor == "扭曲" {
        tw = tw + 1
      }
    }
    if r.uctor == "外冪" && r.uphi == "adj" && r.uholds {
      adjext = false
    }
    // 對偶對每個 Φ 都通勤，且不需要純量修正
    if r.uctor == "對偶" {
      if !r.uholds || r.udual != "同" || r.ue0 != 0 || r.ue1 != 0 || r.ue2 != 0 {
        ok = false
      }
    }
  }
  if dual != 5 || ext != 4 || tw != 3 {
    ok = false
  }
  if !adjext {
    ok = false
  }

  // ── 具名限制：adj ∘ 外冪 在 k 釘死為 2 時找得到 ─────────
  let rk = ob_rng()
  let a = uni_adj_ext_k2(rk)
  if !a.uholds {
    ok = false
  }
  if a.ue0 != -3 || a.ue1 != 1 || a.ue2 != 0 {
    ok = false
  }

  // ── 掃描 ────────────────────────────────────────────────
  let r1 = ob_rng()
  let (pairs, holds, inst, same, td, ts, win) = uni_scan(r1)
  if pairs != 15 || holds != 12 || inst != 48 {
    ok = false
  }
  if same != 48 {
    ok = false
  }
  if td != 2431049L || ts != 1506607L {
    ok = false
  }
  if win != 17 {
    ok = false
  }

  // ── 兩側對照：修正指數動一格，全部必須垮掉 ──────────────
  let r2 = ob_rng()
  let (ct, cb) = uni_control(r2)
  if ct != 12 || cb != 12 {
    ok = false
  }
  mk_check(
    "N-72 一元構造子之算子層規則",
    ok,
    inst * 2 + pairs + ct + 8,
    "N-66 把 N-40 的合成器接進中端，但合成器只會處理 Φ(A⊗B)，再加一條手寫的 Φ(A⊕B)。對偶、扭曲、外冪這三個一元構造子一條規則也沒有 —— 而它們恰好是 IR 裡最常出現的。要找的規則形狀是 **Φ(U(G)) = det(G)^e·U′(Φ(G))**：一元構造子 U、它在算子那一側的對應 U′、以及一個純量修正。和 N-40 一樣，e 不是人填的 —— 合成器先在幾個尺寸上量出 e，擬合成 n（與外冪的 k）的仿射函數，再用保留樣本驗證。**合成結果恰好等於手推。** 對偶 5/5 通勤（U′ = 對偶，e = 0）；外冪 4/5（inv、tr̃ans、sq、cube 由 Cauchy–Binet 通勤，e = 0）；扭曲 3/5 —— tr̃ans 用 U′ = 同，而 inv 與 adj 要改用 **M⁻ᵀ**（因為 (MᵀGM)⁻¹ = M⁻¹G⁻¹M⁻ᵀ），sq 與 cube 根本不通勤。合成器是自己試出「同」不行再試「轉置逆」的，沒有人告訴它。**一個具名的限制，而且錯不在合成器。** adj ∘ 外冪 放開 k 時找不到規則。手推可知修正指數是 C(n−1,k−1) − k：k=2 時是 n−3（仿射），k=3 時是 (n−1)(n−2)/2 − 3（二次）。合成器的假設類只有仿射，所以放開 k 時保留樣本會推翻它。**把 k 釘死在 2 就找得到，而且找到的正是 det(G)^{n−3}。** 這不是合成器壞了，是假設類不夠寬 —— 義務同時釘死「放開 k 找不到」與「k=2 找得到 e = n−3」兩件事，將來誰把假設類擴成二次，第一條會失敗並要求重寫這一段。實測：15 對 (Φ, 構造子) 中 12 對有規則，48 個實例逐元相同 48/48，成本 " +
    td.to_string() +
    " → " +
    ts.to_string() +
    "（×" +
    fmt_d(td.to_double() / ts.to_double(), 3) +
    "），17/48 走規則較便宜。**兩側對照。** 把修正指數動一格，12 條規則必須全部垮掉 —— 若有哪條照樣成立，表示那個指數根本沒被用到。這一關第一次跑時是 0/12 通過，原因是 qpow_fast 對 e ≤ 0 一律回傳 1，於是 solve_exponent 把 e = −8 誤判成成立；補上支援負指數的 qpow_int、並把搜尋順序改成由 0 向外展開之後才正確。",
  )
}

///|
/// N-73 之義務：N 元普查引擎。
pub fn ob_n73() -> Check {
  let mut ok = true
  let tb = tri_tables()

  // ── 推廣必須精確退回三元 ────────────────────────────────
  let (eq, nd, td) = nary_reduces_to_tri(tb[2], tb[4], tb[5], 13, 12)
  if !eq {
    ok = false
  }
  if nd != "419:419:674552611" || td != "419:419:674552611" {
    ok = false
  }
  let (eq2, _, _) = nary_reduces_to_tri(tb[0], tb[4], tb[5], 1, 12)
  if !eq2 {
    ok = false
  }

  // ── 2、3、4、5 元各跑一次 ──────────────────────────────
  let rows = nary_scan()
  if rows.length() != 4 {
    ok = false
  }
  let arity = [2, 3, 4, 5]
  let cells = [138, 419, 424, 615]
  let pass = [123, 419, 380, 570]
  for i in 0..<4 {
    if rows[i].0 != arity[i] || rows[i].1 != cells[i] || rows[i].2 != pass[i] {
      ok = false
    }
  }
  if rows[1].4 != "419:419:674552611" {
    ok = false
  }
  // 含擾動表的那幾元必須真的有格被推翻
  if rows[0].2 >= rows[0].1 {
    ok = false
  }
  if rows[2].2 >= rows[2].1 {
    ok = false
  }
  if rows[3].2 >= rows[3].1 {
    ok = false
  }
  // 不含擾動表的三元必須全過
  if rows[1].2 != rows[1].1 {
    ok = false
  }

  // ── 逐軸覆蓋（四元）────────────────────────────────────
  let cv = nary_coverage([tb[0], tb[4], tb[3], tb[5]], 29, 12)
  if cv.length() != 4 {
    ok = false
  }
  if cv[0] != 6 || cv[1] != 7 || cv[2] != 14 || cv[3] != 23 {
    ok = false
  }
  mk_check(
    "N-73 普查引擎推廣到 N 元",
    ok,
    cells[0] + cells[1] + cells[2] + cells[3] + 16,
    "N-61 的引擎吃三張表。那個「三」沒有任何理由 —— 它只是 N-52 寫死的三個迴圈被抽出來之後留下的形狀。本條把它推成任意張：里程表走前 r−1 軸，最後一軸在內層；分層謂詞由 (i + 2j + 3k) mod step 推廣為 Σ_t (t+1)·i_t mod step；格鍵與雜湊累積方式不變。**推廣的正當性照舊只有一條：必須能精確退回特例。** 以三張表呼叫 nary_product，必須逐格重現 tri_product —— 格數、通過數、三軸覆蓋、最高維、以及 FNV 乘累積的指紋 " +
    nd +
    " 全部相同。義務拿兩組三元規格去對（一組全過、一組含擾動表因而有推翻），兩組都必須相同。順帶一提，三元時 Σ_t (t+1)·i_t = i + 2j + 3k，分層謂詞**恰好**化為 N-52 原本寫死的那一個 —— 這不是巧合，是推廣時刻意挑的係數。實測 2、3、4、5 元各一次：2 元 138 格（123 過）、3 元 419 格（全過）、4 元 424 格（380 過）、5 元 615 格（570 過）。四元的逐軸覆蓋 6/7/14/23。義務另外釘死一個結構性質：**含擾動表的元數必須有格被推翻，不含的必須全過** —— 這擋掉「引擎其實沒在跑判者、一律回答通過」這種失敗模式，而那是推廣時最容易寫出來的 bug（里程表寫錯一格，內層迴圈就空轉）。",
  )
}

///|
/// N-74 之義務：成本比對式義務生成器。
pub fn ob_n74() -> Check {
  let mut ok = true

  // ── 防線一：決定性 ──────────────────────────────────────
  let s1 = gen_compare_src(cmp_demo_spec())
  let s2 = gen_compare_src(cmp_demo_spec())
  let src = match (s1, s2) {
    (Some(a), Some(b)) => {
      if a != b {
        ok = false
      }
      a
    }
    _ => {
      ok = false
      ""
    }
  }
  if src.length() < 500 {
    ok = false
  }

  // ── 防線二：量測忠實 ────────────────────────────────────
  let f = match cmp_by_name("子空間") {
    Some(x) => x
    None => {
      ok = false
      () => (0, 0, 0L, 0L, 0, 0)
    }
  }
  let (n, same, td, ts, win, lose) = f()
  if !src.contains("n != " + n.to_string()) {
    ok = false
  }
  if !src.contains("td != " + td.to_string() + "L") {
    ok = false
  }
  if !src.contains("ts != " + ts.to_string() + "L") {
    ok = false
  }
  if !src.contains("win != " + win.to_string()) {
    ok = false
  }
  if same != n {
    ok = false
  }

  // ── 防線三：敗例忠實 ────────────────────────────────────
  let csrc = match gen_compare_src(cmp_control_spec()) {
    Some(x) => x
    None => {
      ok = false
      ""
    }
  }
  let g = match cmp_by_name("外冪與 Kron 和") {
    Some(x) => x
    None => {
      ok = false
      () => (0, 0, 0L, 0L, 0, 0)
    }
  }
  let (_, _, _, _, _, clos) = g()
  if clos <= 0 {
    ok = false
  }
  if !csrc.contains("lose != " + clos.to_string()) {
    ok = false
  }
  // 示範組敗例為 0，對照組不為 0 —— 兩者產出必須不同
  if lose != 0 {
    ok = false
  }
  if !src.contains("lose != 0") {
    ok = false
  }
  if csrc.contains("lose != 0") {
    ok = false
  }

  // ── 佔位符分工：義務 0 次、目錄列 2 次 ──────────────────
  let ph = obl_placeholder()
  if src.contains(ph) {
    ok = false
  }
  let row = match gen_compare_row(cmp_demo_spec()) {
    Some(x) => x
    None => {
      ok = false
      ""
    }
  }
  if str_count(row, ph) != 2 {
    ok = false
  }

  // ── 產出物確實編譯並通過 ────────────────────────────────
  let gen = ob_n74g()
  if !gen.ok {
    ok = false
  }
  if gen.trials != n * 2 {
    ok = false
  }
  mk_check(
    "N-74 義務生成器之成本比對式產出",
    ok,
    n * 4 + 16,
    "N-62 讓生成器會寫普查式義務。但第八、九輪真正多出來的那一類 —— N-65、N-67、N-71 那種「兩條路線、逐元相同、比成本」的義務 —— 仍然一條一條手打。本條把那個模板也交給生成器：規格指定一個比對掃描器，生成器先跑一次掃描，把語料數、逐元相同數、兩邊總成本、勝數、**敗數**釘進產出的程式碼。模板裡有兩條不是從量測來的斷言，而是這一類義務的**前提**：`same == n`（兩路不逐元相同的話，成本比較沒有意義）與 `ts < td`（否則它就不叫特化）。**第三道防線在這裡尤其要緊。** 比對式掃描本來就會有敗例 —— N-71 的外冪與 Kron 和就有 2 式較貴 —— 所以一個只會寫 `lose != 0` 的生成器在那裡會直接產出一條永遠失敗的義務。義務同時餵兩個規格：示範規格（子空間，" +
    lose.to_string() +
    " 敗）產出必須含 `lose != 0`，對照規格（外冪與 Kron 和，" +
    clos.to_string() +
    " 敗）產出必須含 `lose != " +
    clos.to_string() +
    "` 且**不得**含 `lose != 0`。兩個規格的產出必須不同，否則「如實寫下量到的東西」只是巧合。示範規格之產出經 cmd/genoblig 寫入 oblig_auto.mbt、編譯為 ob_n74g，本義務直接呼叫並要求通過（" +
    gen.trials.to_string() +
    " 個實例）。至此生成器會寫三種義務：N-45 的律式、N-62 的普查式、本條的成本比對式。",
  )
}

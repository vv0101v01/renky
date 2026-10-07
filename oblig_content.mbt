///|
/// N-47 之義務：內容檢定。
///
/// N-42 查出兩類「通過但什麼都沒說」的裁決：⊥ 空洞與恆值律。本條不是把
/// 它們標記起來了事，而是**補上缺的那一半定義域再量一次** —— 看空殼會
/// 變成什麼。答案是：變成一句有內容的話，而那句話是錯的。
pub fn ob_n47() -> Check {
  let mut ok = true
  let rng = ob_rng()

  // ── 定理 205-1（qpinv 之正確性：Penrose 四條件，精確 ℚ）────
  // 四條件同時成立即由 Moore–Penrose 唯一性定理確定 A⁺，故這不是
  // 「看起來對」，是一個完整的正確性判定。
  let mut pen = 0
  for d in [1, 2, 3, 4] {
    for s in [samp_gram, samp_indef, samp_singular] {
      let a = s(rng, d)
      let (p1, p2, p3, p4) = qpinv_penrose(a)
      if !(p1 && p2 && p3 && p4) {
        ok = false
      }
      pen = pen + 4
    }
  }
  // 零矩陣：r = 0 之邊界
  let z = Mat::zeros(3, 3)
  let (z1, z2, z3, z4) = qpinv_penrose(z)
  if !(z1 && z2 && z3 && z4) {
    ok = false
  }
  if !qpinv(Cost::new(), z).equals(Mat::zeros(3, 3)) {
    ok = false
  }
  // 可逆時 A⁺ = A⁻¹（否則「補定義域」就不是補，是換了一個函式）
  let c0 = Cost::new()
  for d in [2, 3, 4] {
    let a = samp_gram(rng, d)
    match qinv_gauss(a, c0) {
      Some(iv) => if !qpinv(c0, a).equals(iv) { ok = false }
      None => ok = false
    }
  }

  // ── 命題 205-2（⊥ 空洞歸零）──────────────────────────────
  let xs = content_scan_std(rng)
  let (o, n, bot, cst, flip) = content_stats(xs)
  if xs.length() != 64 {
    ok = false
  }
  // 補定義域之前：28 條成立裁決帶空洞樣本（問題確實存在）
  if bot != 28 {
    ok = false
  }
  // 補定義域之後：一條都不剩
  if content_residual_bot(xs) != 0 {
    ok = false
  }

  // ── 定理 205-3（恆值律現形並翻轉）────────────────────────
  // rank∘inv 在舊制下恆為 nm（⊥ 把降秩樣本吃掉了），故 rank∘inv/⊞/·
  // 通過裁決卻只說了 nm = n·m。換上偽逆後 rank∘pinv 在降秩樣本上等於
  // r < n，恆值性當場破功，而那條律隨即被推翻。
  if !comp_is_constant(phi_by_name, "rank", "inv", rng) {
    ok = false // 舊制下它**必須**是恆值，否則本條的前提不成立
  }
  if comp_is_constant(phi_by_name_full, "rank", "inv", rng) {
    ok = false // 新制下它**必須**不再是恆值
  }
  if o != 64 || n != 61 || flip != 3 {
    ok = false
  }
  let flipped : Array[String] = []
  for x in xs {
    if x.vold != x.vnew {
      if !x.vold {
        ok = false // 翻轉必須全是「成立 → 推翻」，不得有反向
      }
      flipped.push(x.vname)
    }
  }
  if flipped.length() == 3 &&
    (
      flipped[0] != "rank∘inv/⊞/·" ||
      flipped[1] != "rank∘adj/⊗/·" ||
      flipped[2] != "rank∘adj/⊕/+"
    ) {
    ok = false
  }

  // ── 命題 205-4（殘餘恆值為 0：活下來的 61 條都有內容）────
  if cst != 0 {
    ok = false
  }

  // ── 定理 205-5（N-42 之健全性在更嚴格的制度下仍然成立）──
  // 這是本條對 N-42 最有價值的一次覆核：把 ⊥ 補掉、把恆值剔掉之後，
  // 推導出的 60 條複合律**一條都沒倒**。若倒了，複合定理就不只是
  // 「充分不必要」，而是「在某些定義域上根本不對」。
  let ds = compose_derive(law_search_fixed(rng))
  let mut der_hold = 0
  for x in xs {
    let mut isder = false
    for d in ds {
      let (oo, ii, cc, _mm, rr) = d
      if comp_key(oo, ii, cc, rr) == x.vname {
        isder = true
      }
    }
    if isder && x.vnew {
      der_hold = der_hold + 1
    }
  }
  if der_hold != 60 || ds.length() != 60 {
    ok = false
  }

  // ── 命題 205-6（代價要講明：偽逆比求逆貴）──────────────
  // 補定義域不是免費的。同一條律在兩種制度下的增益必須都記下來，
  // 否則讀者會以為正確性是白來的。
  let cinv = Cost::new()
  let cpin = Cost::new()
  let a6 = samp_gram(rng, 6)
  let _ = qinv_gauss(a6, cinv)
  let _ = qpinv(cpin, a6)
  if cpin.qmul <= cinv.qmul {
    ok = false // 偽逆必須真的比較貴，否則上面的「代價」一節是空話
  }
  let ratio = if cinv.qmul > 0L {
    cpin.qmul.to_double() / cinv.qmul.to_double()
  } else {
    0.0
  }
  if cont_miss_count() != 1 {
    ok = false
  }
  mk_check(
    "N-47 內容檢定",
    ok,
    pen + xs.length() * 2 + ds.length() + 20,
    "N-42 查出裁決器會放行兩類空殼：⊥ 空洞（qinv_gauss／qadj 在奇異輸入回傳 ⊥，兩側同時 ⊥ 被判相符）與恆值律（rank∘inv 在其定義域上恆為 nm，恆值函數滿足任何維數相符的規則）。兩者是同一件事的兩面 —— ⊥ 把 Φ 的變化藏起來，Φ 看起來就成了常數。本條補上缺的那一半定義域：新增精確 ℚ 的 Moore–Penrose 偽逆 qpinv（秩分解 A = CF，A⁺ = Fᵀ(FFᵀ)⁻¹(CᵀC)⁻¹Cᵀ），配合 N-42 的餘因子 adj，兩者皆為全函式。正確性以 Penrose 四條件判定（精確 ℚ，配唯一性定理即完整證明），13 組矩陣 × 4 條件全通過，含零矩陣邊界；可逆時 A⁺ = A⁻¹ 亦經驗證。結果：帶 ⊥ 空洞的成立裁決由 " +
    bot.to_string() +
    " 條降為 " +
    content_residual_bot(xs).to_string() +
    " 條；成立數由 " +
    o.to_string() +
    " 降為 " +
    n.to_string() +
    "，恰 3 條翻轉且全為「成立→推翻」：rank∘inv/⊞/·、rank∘adj/⊗/·、rank∘adj/⊕/+。其中 rank∘inv/⊞/· 正是 N-42 點名的恆值律 —— 義務同時驗證它在舊制下確為恆值、在新制下不再是恆值，空殼於是變成一句有內容的話，而那句話是錯的。活下來的 " +
    n.to_string() +
    " 條殘餘恆值 0 條。最有價值的一項覆核：把 ⊥ 補掉、恆值剔掉之後，N-42 推導的 " +
    der_hold.to_string() +
    " 條複合律**一條都沒倒**，複合定理的健全性在更嚴格的制度下仍然成立。⚠️ 代價：6 階矩陣上偽逆的有理乘法次數為求逆的 " +
    fmt_d(ratio, 1) +
    " 倍，qadj_cof 為 Θ(n⁵) 而 qadj 為 Θ(n³)；且 mrref 未經成本插裝，故 qpinv 的計量**低估**真實代價（方向上低估直接路徑、低估增益，不灌水）。原函式一律不動 —— 換掉會改動 N-13／N-36／N-44 已釘死的指紋，本庫的規矩是量測後並陳，不是悄悄修掉。",
  )
}

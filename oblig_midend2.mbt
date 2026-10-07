///|
/// N-63 之義務：⊞ 的 k 元成本模型。
pub fn ob_n63() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let (n, model_ok, ndiff, worst, gain) = ks_assoc_scan(rng)
  if n != 12 || !model_ok || ndiff != 0 {
    ok = false
  }
  if !(worst > 0.999 && worst < 1.001) {
    ok = false
  }
  if !(gain > 2.02 && gain < 2.03) {
    ok = false
  }

  // ── 模型與計量逐式對帳（這是「成本模型」三個字的實質內容）──
  let r2 = ob_rng()
  let mut mok = 0
  let cases : Array[Array[Int]] = [[2, 3, 4], [2, 2, 8], [5, 2, 2, 3]]
  for dims in cases {
    let (_, t) = ks_dp(dims)
    let (m, meas, same) = ks_model_check(dims, t, r2)
    if same && m == meas {
      mok = mok + 1
    }
  }
  if mok != 3 {
    ok = false
  }

  // ── 命題：cost⊞(T) ≤ cost⊗(T)，等號 ⟺ 每個內部節點都是 2 與 2 ──
  let (eq22, lt222) = ks_equality_case()
  if !eq22 || !lt222 {
    ok = false
  }

  // ── 窮舉：兩個 DP 的最佳樹何時不同 ────────────────────
  let (t1, d1, w1, l1) = ks_vs_kron_sweep(2, 8, 4)
  if t1 != 2401 || d1 != 0 || l1 != 2401 {
    ok = false
  }
  if !(w1 > 0.999 && w1 < 1.001) {
    ok = false
  }
  let (t2, d2, w2, l2) = ks_vs_kron_sweep(2, 12, 4)
  if t2 != 14641 || d2 != 6 || l2 != 14641 {
    ok = false
  }
  if !(w2 > 1.0203 && w2 < 1.0204) {
    ok = false
  }
  let (t3, d3, _, l3) = ks_vs_kron_sweep(2, 20, 3)
  if t3 != 6859 || d3 != 0 || l3 != 6859 {
    ok = false
  }

  // ── 具名反例 ────────────────────────────────────────────
  let ce = ks_named_counterexample(2, 12, 4)
  let cetxt = match ce {
    None => {
      ok = false
      ""
    }
    Some((d, kl, ol, ck, co)) => {
      if d.length() != 4 || d[0] != 5 || d[1] != 2 || d[2] != 2 || d[3] != 9 {
        ok = false
      }
      if ck != 5308L || co != 5416L {
        ok = false
      }
      if kl == ol {
        ok = false
      }
      "dims [5,2,2,9]：⊞-DP 選 " +
      kl +
      "（" +
      ck.to_string() +
      "），⊗-DP 選 " +
      ol +
      "（在 ⊞ 模型下 " +
      co.to_string() +
      "）"
    }
  }

  // ── 稀疏感知 vs 稠密、以及 k 元結合律 ───────────────────
  let r3 = ob_rng()
  let (sp, de, agree) = ks_sparse_vs_dense([2, 3, 4], r3)
  if sp != 270L || de != 3017L || !agree {
    ok = false
  }
  let r4 = ob_rng()
  let (nt, al) = ks_assoc_law([2, 3, 4], r4)
  if nt != 5 || !al {
    ok = false
  }
  mk_check(
    "N-63 ⊞ 的 k 元成本模型",
    ok,
    t1 + t2 + t3 + n * 4 + 20,
    "N-41 給了 ⊗ 鏈的成本模型 cost(樹) = Σ_{內部節點 v} P(v)²，這個模型有個很舒服的性質：**組裝一段區間的代價只取決於該區間的維數積，與它內部怎麼切無關**（p×p 與 q×q 的 Kronecker 積恰需 (pq)² 次乘法），所以區間 DP 的狀態只要 (i,j)。⊞ 從第五輪欠到現在沒有模型，更糟的是 qkron_sum **根本不計量** —— 它用未計費的 mkron，於是 chain_build 走 ⊞ 分支時 Cost 完全不動。一條沒有成本的運算在成本模型裡是隱形的。**本條先問 ⊞ 的組裝到底在做什麼。** A ⊞ B = A⊗I_q + I_p⊗B，逐項看是 C[(i,k),(j,l)] = A[i][j]·δ_{kl} + δ_{ij}·B[k][l] —— **沒有乘法**，每個非零位置都是把 A 或 B 的某一項搬過去，對角位置再加一次。搬運次數 p²q + pq² = P·(p+q)。這個數字**不只取決於 P，還取決於 p 與 q 怎麼分**；⊗ 的 P² 看不見切法，⊞ 的 P(p+q) 看得見。所以 ⊞ 不能沿用 N-41 的 DP，轉移式裡多了一項依賴切點的成本。模型與計量在 3 組維數上逐式對帳相符（量綱是 wadd 不是 wmul —— ⊞ 不乘東西）。**一條可證的不等式。** 把 cost⊞ 改寫成邊和 Σ_{邊(v,u)} P(v)·P(u)，再用「兩個子區間的維數積都 ≥ 2 ⇒ p+q ≤ pq」即得 cost⊞(T) ≤ cost⊗(T) 對**每一棵**樹成立，等號 ⟺ 每個內部節點都切成 2 與 2（(p−1)(q−1)=1）。窮舉的 " +
    (t1 + t2 + t3).to_string() +
    " 組維數全部滿足。**兩個 DP 的最佳樹幾乎總是同一棵，但不是總是。** k=4、維數 2…8 的 2,401 組：0 組不同。維數 2…12 的 14,641 組：**6 組不同**，用 ⊗ 樹的最大損失 ×" +
    fmt_d(w2, 5) +
    "。k=3、維數 2…20 的 6,859 組：0 組不同。具名反例 —— " +
    cetxt +
    "。這個結果兩邊都說得通：⊞ 確實需要自己的 DP（否則那 6 組會選錯），而 N-41 現成的 DP 是一個誤差 2% 以內的好近似。**稀疏與稠密差多少。** 同一條鏈 [2,3,4]：稀疏感知 270 次搬運／加法、零乘法；現行的稠密實作 3,017 次乘法。兩者輸出逐元相同。最後驗 ⊞ 的 k 元結合律：左結合、右結合、平衡、⊞-DP、⊗-DP 五棵樹組出來的矩陣完全相同。",
  )
}

///|
/// N-64 之義務：類 B 帶著置換進主流程。
pub fn ob_n64() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let (n, snd, stb, moved) = canon_scan(rng)
  if n != 40 || snd != 40 || stb != 40 {
    ok = false
  }
  // 語料裡必須真的有式子被交換過，否則「健全」是空話
  if moved != 21 {
    ok = false
  }

  // ── 具名案例：⊗ 與 ⊕ 的交換都要逐元對得上 ──────────────
  let r2 = ob_rng()
  let a = SLeaf("Z", rand_gram(r2, 3))
  let b = SLeaf("A", rand_gram(r2, 2))
  let t = STensor(a, b)
  let (ct, pt) = canon_perm(t)
  if ct.slabel() != STensor(b, a).slabel() {
    ok = false
  }
  if !canon_sound(t) {
    ok = false
  }
  let s = SSum(a, b)
  let (cs, _) = canon_perm(s)
  if cs.slabel() != SSum(b, a).slabel() {
    ok = false
  }
  if !canon_sound(s) {
    ok = false
  }
  // 置換不是恆等（否則沒搬東西）
  let mut nontriv = false
  for u in 0..<pt.length() {
    if pt[u] != u {
      nontriv = true
    }
  }
  if !nontriv {
    ok = false
  }

  // ── 置換可用：解完再還原，必須等於直接解 ────────────────
  let r3 = ob_rng()
  let mut solved = 0
  let mut tot = 0
  for
    e in [
      STensor(SLeaf("Z", rand_gram(r3, 3)), SLeaf("A", rand_gram(r3, 2))),
      SSum(SLeaf("Y", rand_gram(r3, 3)), SLeaf("B", rand_gram(r3, 2))),
      STensor(SDual(SLeaf("W", rand_gram(r3, 2))), SLeaf("C", rand_gram(r3, 3))),
      SSum(
        STensor(SLeaf("V", rand_gram(r3, 2)), SLeaf("D", rand_gram(r3, 2))),
        SLeaf("E", rand_gram(r3, 3)),
      ),
    ] {
    tot = tot + 1
    let nn = e.sdim()
    let rhs = Mat::build(nn, 2, (_i, _j) => Scalar::s_rand(r3))
    let direct = dense_solve_mat(e, rhs, Cost::new())
    let (c, p) = canon_perm(e)
    let got = match spec_solve_mat2(c, perm_rows(p, rhs), Cost::new()) {
      Some(y) => Some(perm_unrows(p, y))
      None => None
    }
    match (direct, got) {
      (Some(x), Some(y)) => if x.equals(y) { solved = solved + 1 }
      _ => ()
    }
  }
  if solved != tot {
    ok = false
  }

  // ── 兩側對照：故意用錯的置換，還原必須失敗 ──────────────
  let r4 = ob_rng()
  let e2 = STensor(SLeaf("Z", rand_gram(r4, 3)), SLeaf("A", rand_gram(r4, 2)))
  let rhs2 = Mat::build(6, 1, (_i, _j) => Scalar::s_rand(r4))
  let (c2, p2) = canon_perm(e2)
  let bad = Array::makei(p2.length(), i => p2[(i + 1) % p2.length()])
  let truth = dense_solve_mat(e2, rhs2, Cost::new())
  let wrong = match spec_solve_mat2(c2, perm_rows(bad, rhs2), Cost::new()) {
    Some(y) => Some(perm_unrows(bad, y))
    None => None
  }
  let caught = match (truth, wrong) {
    (Some(x), Some(y)) => !x.equals(y)
    _ => true
  }
  if !caught {
    ok = false
  }
  mk_check(
    "N-64 類 B 交換律帶著置換進主流程",
    ok,
    n * 3 + tot * 4 + 8,
    "rw_registry_b()（⊕ 與 ⊗ 的交換律正規序）從第六輪就寫好了，canonicalize 也接了，但沒有任何下游用它。原因很具體：交換律**不保 Gram 逐元相同**，只保到一個置換相似，於是 rw_sound_b 只敢驗 det 與 trace，而派工路徑（N-54）與 ℝ 軌（N-55）都要求逐元相同 —— 用不了。**解法是把被丟掉的資訊帶上。** canon_perm 在規範化的同時產出置換見證 p，約定 G(canon)[u][v] = G(原式)[p[u]][p[v]]。遞迴規則：⊗ 與 ⊞ 交換時索引 u = j·na+i 對應 pa[i]·nb+pb[j]；⊕ 交換時前後兩段互換；對偶直接把置換傳出去（置換相似在求逆下不變）；**扭曲與子空間把子樹的置換吸收進自己的矩陣**（M′ = PᵀM 使 M′ᵀG(ca)M′ = MᵀG(a)M），故這兩個節點對外輸出恆等置換；外冪不遞迴（k-子集的誘導置換另案），視為原子。**於是健全性可以逐元驗了。** 語料 40 式全部通過逐元檢查（而不是 det+trace），全部冪等（已規範之式再規範，置換必為恆等），其中 " +
    moved.to_string() +
    " 式真的被交換過 —— 沒有這個數字，「40/40 健全」可能只是「40 式都沒動」。**置換不只是見證，它讓類 B 真的能用。** 義務拿 4 個式子走完整條路：規範化 → 把右端依 p 重排 → 在規範形上用特化求解器 → 把解依 p 還原，結果必須逐元等於直接在原式上求解。**兩側對照。** 把置換旋轉一格再做同一件事，還原的結果必須**不**等於真值 —— 若還是相等，表示那個置換根本沒被用到，整條路徑是假的。",
  )
}

///|
/// N-65 之義務：SSub 的特化路徑。
pub fn ob_n65() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let (n, same, td, ts, win, lose) = sub_scan(rng)
  if n != 16 || same != 16 {
    ok = false
  }
  if td != 211868L || ts != 156576L {
    ok = false
  }
  if win != 14 || lose != 0 {
    ok = false
  }

  // ── 施加 Gram 的獨立覆核 ────────────────────────────────
  let r2 = ob_rng()
  let (gn, gok) = gram_apply_check(r2)
  if gn != 24 || gok != 24 {
    ok = false
  }

  // ── 兩側對照：仍然沒有路徑的形狀，成本必須完全相等 ──────
  let r3 = ob_rng()
  let (cn, eq) = sub_control(r3)
  if cn != 4 || eq != 4 {
    ok = false
  }

  // ── 派工表的變化：SSub 由「無路徑」變成「有路徑」────────
  let r4 = ob_rng()
  let probe = SSub(
    STensor(SLeaf("A", rand_gram(r4, 3)), SLeaf("B", rand_gram(r4, 4))),
    comb_half_sel(12),
  )
  if spec_has_path(probe) {
    ok = false
  }
  if !spec_has_path2(probe) {
    ok = false
  }
  let gain = td.to_double() / ts.to_double()
  mk_check(
    "N-65 子空間之特化求解路徑",
    ok,
    n * 3 + gn + cn + 4,
    "N-54 的派工表對葉、張量、直和、對偶、扭曲都有特化解法，對外冪、Kron 和、**子空間**退回通用路徑。當時外冪與 Kron 和被拿來當兩側對照（沒有路徑的形狀，兩條路線的成本必須完全相等），子空間跟著留在那一側 —— 那是個漏洞。G(U[A,S]) = Sᵀ·G(A)·S 的維數 k 通常**遠小於** A 的維數 n（U½ 砍一半，S² 把 n 嵌進 n²），通用路徑卻要先把 n×n 的 G(A) 整個物化出來，而 G(A) 可能是一條張量鏈 —— 物化它正是 N-53 想避免的事。**關鍵是：要的不是 G(A)，是 G(A)·S。** 於是本條先補一個與 spec_solve_mat（施加 G⁻¹）對偶的運算：spec_gram_apply（施加 G），遞迴地算 G(e)·X 而不物化 G(e)。對偶節點上兩者互換 —— G(A*) = G(A)⁻¹，所以「對 A* 施加 G」就是「對 A 解 G」，這個對稱性讓兩個函式互相定義。施加器先獨立覆核：" +
    gok.to_string() +
    "/" +
    gn.to_string() +
    " 式的 spec_gram_apply(e,X) 逐元等於物化後的 G(e)·X。**子空間路徑**：W = G(A)·S（n×k，遞迴施加）→ M = Sᵀ·W（k×k）→ k 階求解。語料 16 式（8 種底座 × 2 種嵌入矩陣）兩路逐元相同 16/16，成本 " +
    td.to_string() +
    " → " +
    ts.to_string() +
    "（×" +
    fmt_d(gain, 3) +
    "），" +
    win.to_string() +
    " 式較便宜、" +
    lose.to_string() +
    " 式較貴（其餘持平 —— 底座是葉時兩條路本來就一樣）。**兩側對照照舊，只是縮小了。** 剩下沒有特化路徑的是外冪與 Kron 和：這 4 式的兩路成本必須**完全相等**，差一分錢就代表派工出錯。義務另外直接檢查派工判準本身：同一個 SSub 式在 spec_has_path 下為假、在 spec_has_path2 下為真。",
  )
}

///|
/// N-66 之義務：N-40 接中端（算子層規則與守門）。
pub fn ob_n66() -> Check {
  let mut ok = true

  // ── 未守門：手寫的 ⊕ 規則會出事 ────────────────────────
  let r0 = ob_rng()
  let (np0, ns0, nc0, same0, _, _, _) = op_scan(r0)
  if np0 != 5 || ns0 != 5 || nc0 != 8 {
    ok = false
  }
  // 40 組裡恰有 3 組對不上 —— 這個數字本身就是本條的發現
  if same0 != 37 {
    ok = false
  }

  // ── 守門後 ──────────────────────────────────────────────
  let rng = ob_rng()
  let (np, ns, ng, pairs, same, td, ts, win) = op_scan_gated(rng)
  if np != 5 || ns != 5 || ng != 4 {
    ok = false
  }
  if pairs != 40 || same != 40 {
    ok = false
  }
  if td != 655522L || ts != 101194L {
    ok = false
  }
  if win != 30 {
    ok = false
  }

  // ── 守門逐 Φ：只有 adj 不能拆 ⊕ ────────────────────────
  let r2 = ob_rng()
  let gates = op_gate_table(r2)
  if gates.length() != 5 {
    ok = false
  }
  for g in gates {
    let (nm, v) = g
    if nm == "adj" && v {
      ok = false
    }
    if nm != "adj" && !v {
      ok = false
    }
  }

  // ── 機器合成的指數表 ────────────────────────────────────
  let r3 = ob_rng()
  let tbl = op_rule_table(r3)
  let mut adjrule = ""
  for e in tbl {
    let (nm, d) = e
    if nm == "adj" {
      adjrule = d
    }
  }
  if adjrule != "(det A)^{m − 1}·(det B)^{n − 1}" {
    ok = false
  }

  // ── 兩側對照：指數動一格，恆等式必須垮掉 ────────────────
  let r4 = ob_rng()
  let (ct, cb) = op_control(r4)
  if ct != 5 || cb != 5 {
    ok = false
  }

  // ── 規則來源統計 ────────────────────────────────────────
  let r5 = ob_rng()
  let (pa, pb, pc) = op_rule_provenance(r5)
  if pa != 10 || pb != 2 || pc != 5 {
    ok = false
  }
  mk_check(
    "N-66 N-40 接中端：算子層規則由合成器供應",
    ok,
    pairs * 2 + 5 * 4 + 10,
    "N-53 的重寫系統處理的是 SpaceExpr —— 把 (A⊗B)* 改寫成 A*⊗B*、把 T[T[A,M],N] 融合成 T[A,MN]。十條類 A 規則**全部是手寫的**。而 N-40 的規則合成器產出的是另一種東西：Φ(A⊗B) = (det A)^{p(n,m)}·(det B)^{q(n,m)}·(Φ(A)⊗Φ(B))。這不是空間層的重寫，是**算子層**的 —— 它說的是「對組合空間做 Φ」可以拆成「分別做 Φ 再組合」。中端一直沒有這一層，N-40 找到的規則只能被 N-45 包成義務，進不了求值管線。本條補上類 C 規則與 Φ 樹（OpLeaf／OpKron(p,q)／OpSum），而**指數 (p,q) 不是人填的，是 synth_rule_kron 在執行期量出來的**。合成結果：inv、tr̃ans、sq、cube 四個 Φ 的修正指數全為 0（樸素分解即可），adj 的是 " +
    adjrule +
    " —— 這條正是 N-03 時代手推過的公式，現在由機器量出來。**接上去的第一次，40 組 (Φ, 式) 有 3 組對不上。** 出問題的不是機器合成的 ⊗ 規則，是**手寫的 ⊕ 規則**：adj(A⊕B) = det(B)·adj(A) ⊕ det(A)·adj(B)，不等於 adj(A)⊕adj(B)。區塊對角看起來太像恆等式，以致於它被當成「對所有 Φ 都成立」寫死在規則裡。這一筆值得記住：**自動合成的那一半是對的，手寫的那一半是錯的。** 修法不是補一條 adj 專用的 ⊕ 規則，而是加一道守門 —— 對每個 Φ 先在小實例上測 Φ(A⊕B) = Φ(A)⊕Φ(B)，不成立就不拆 ⊕。守門本身也是量出來的：5 個 Φ 裡恰好 adj 一個不通過。守門後 40/40 逐元相同，成本 " +
    td.to_string() +
    " → " +
    ts.to_string() +
    "（×" +
    fmt_d(td.to_double() / ts.to_double(), 3) +
    "），" +
    win.to_string() +
    "/40 組較便宜。**兩側對照。** 把合成出來的指數動一格（p₀+1），5 個 Φ 的恆等式必須**全部**垮掉 —— 若有哪個照樣成立，表示那個指數根本沒被用到。中端的規則來源統計現在是：類 A 手寫 " +
    pa.to_string() +
    " 條、類 B 手寫 " +
    pb.to_string() +
    " 條、類 C **機器合成 " +
    pc.to_string() +
    " 條**。",
  )
}

///|
/// N-67 之義務：範式的結合順序接 N-41 的 k 元 DP。
pub fn ob_n67() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let (n, allsame, cheaper, same, dearer, ta, td) = rw_dp_scan(rng)
  if n != 40 || !allsame {
    ok = false
  }
  if cheaper != 2 || same != 38 || dearer != 0 {
    ok = false
  }
  if ta != 72008L || td != 71588L {
    ok = false
  }

  // ── A10 的成本回歸被修好了 ──────────────────────────────
  let r2 = ob_rng()
  let (cnt, d, a, p, fixed) = rw_a10_regression(r2)
  if cnt != 1 {
    ok = false
  }
  if d != 1074L || a != 1108L || p != 1074L {
    ok = false
  }
  if !fixed {
    ok = false
  }

  // ── 長鏈上 DP 的真正價值 ────────────────────────────────
  let r3 = ob_rng()
  let (nc, tr, tdp, best) = rw_chain_gain(r3)
  if nc != 8 {
    ok = false
  }
  if tr != 229946L || tdp != 194819L {
    ok = false
  }
  if !(best > 1.41 && best < 1.43) {
    ok = false
  }

  // ── 合流與冪等必須不被破壞 ──────────────────────────────
  let r4 = ob_rng()
  let corpus = rw_corpus(r4)
  let mut idem = 0
  for e in corpus {
    let x = normalize_dp(e)
    if normalize_dp(x).slabel() == x.slabel() {
      idem = idem + 1
    }
  }
  if idem != corpus.length() {
    ok = false
  }
  mk_check(
    "N-67 範式的結合順序接上 N-41 的 k 元 DP",
    ok,
    n * 4 + nc * 2 + corpus.length() + 6,
    "A10「右結合正規序」是 N-53 十條類 A 規則裡最特別的一條：它只搬括號，不消節點，存在的理由是**合流**而不是成本。代價也寫在那裡 —— N-53 的逐式側寫是 34 便宜／5 不變／**1 變貴**，那一式就是 A10 造成的（((A⊗C)⊗B) → (A⊗(C⊗B))，1,074 → 1,108）。當時的說法是「A10 為合流而設，非為成本」，也就是把問題記下來而不解決。**本條解決它。** Kronecker 積嚴格結合 —— (A⊗B)⊗C 與 A⊗(B⊗C) 的 Gram **逐元相同** —— 所以重新結合屬於類 A，不需要置換也不損失任何東西。於是範式的最後一步改成：把每一條 ⊗ 鏈攤平，用 N-41 的區間 DP 求成本最佳的結合樹，再重建。合流性不受影響，因為 DP 的輸出是維數序列的確定性函數，而攤平後因子的順序不變，同一式必得同一棵樹（義務逐式驗冪等 " +
    idem.to_string() +
    "/" +
    corpus.length().to_string() +
    "）。**那一式被修好了。** 掃語料找「類 A 範式比直接物化還貴」的式子：恰好 1 式（與 N-53 量到的 1 式一致），直接 1,074 → 類 A 1,108 → 類 A+DP **1,074**。DP 把它帶回了直接物化的成本，也就是 A10 的代價歸零。**整體效果很小，而且應該很小。** 40 式語料上只有 2 式變便宜、38 式不變、0 式變貴，總成本 72,008 → 71,588（×1.006）—— 因為隨機語料裡的 ⊗ 鏈大多只有兩個因子，而兩個因子只有一種結合方式。這個數字誠實地說明了 DP 在這裡的作用：它不是加速器，是**把一個已知的退化修掉**。**DP 真正值錢的地方在長鏈上。** 另備 8 條長度 3–5 的鏈：右結合（A10 的輸出）總成本 " +
    tr.to_string() +
    "，DP 總成本 " +
    tdp.to_string() +
    "（×" +
    fmt_d(tr.to_double() / tdp.to_double(), 4) +
    "），最大單鏈增益 ×" +
    fmt_d(best, 4) +
    "。兩種結合的 Gram 逐元相同，這是重新結合合法的前提，義務逐條驗。",
  )
}

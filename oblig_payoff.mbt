///|
/// N-34 之義務：三類報酬 —— 律的價值不只有「變快」。
pub fn ob_n34() -> Check {
  let rng = ob_rng()
  let mut ok = true

  // ── 定理 197-1（Sylvester 慣性律，精確 ℚ 驗證）──────────────
  // 以對稱消去法在 ℚ 內精確數符號，不經浮點特徵值。
  // 負對照不可少：det 與 trace 在同餘下**會**改變，若它們也「不變」，
  // 代表隨機變換矩陣太溫和（例如恆等），整條檢驗就是空的。
  let iner = check_invariant(
    "Sylvester 慣性律",
    "慣性指數 (n₊,n₋,n₀)",
    (g, c) => inertia_label(qinertia(g, c)),
    (r, n, g) => congruence(Cost::new(), g, rand_invertible(r, n)),
    rng,
    [2, 3, 4, 5, 6],
  )
  if !iner.clholds {
    ok = false
  }
  if !iner.clpayoff.psame_kind(Invariant("x")) {
    ok = false
  }
  // 負對照
  let dt = check_invariant(
    "det 於同餘下（應改變）",
    "det",
    (g, c) => qdet_gauss(g, c).to_string(),
    (r, n, g) => congruence(Cost::new(), g, rand_invertible(r, n)),
    rng,
    [3, 4, 5],
  )
  let tr = check_invariant(
    "trace 於同餘下（應改變）",
    "trace",
    (g, c) => qtrace(c, g).to_string(),
    (r, n, g) => congruence(Cost::new(), g, rand_invertible(r, n)),
    rng,
    [3, 4, 5],
  )
  if dt.clholds || tr.clholds {
    ok = false
  }
  // 且樣本必須真的不定（若全是正定，慣性恆為 (n,0,0)，「不變」就是廢話）
  let mut indefinite = 0
  for n in [3, 4, 5, 6] {
    let (p, m, _z) = qinertia(rand_sym_q(rng, n), Cost::new())
    if p > 0 && m > 0 {
      indefinite = indefinite + 1
    }
  }
  if indefinite < 3 {
    ok = false
  }

  // ── 定理 197-2（同一條律，報酬型別隨查詢而異）──────────────
  // (甲) 查詢「sig(AᵀGA)」：律省下形成 AᵀGA 並對更大數字消去的工夫 ⇒ 加速律。
  let mut gb = 0L
  let mut gf = 0L
  for n in [4, 5, 6] {
    let g = rand_sym_q(rng, n)
    let a = rand_invertible(rng, n)
    let cd = Cost::new()
    let ga = congruence(cd, g, a)
    let s1 = qinertia(ga, cd)
    let cf = Cost::new()
    let s2 = qinertia(g, cf)
    if inertia_label(s1) != inertia_label(s2) {
      ok = false
    }
    gb = gb + cd.wmul
    gf = gf + cf.wmul
  }
  let g_speed = if gf > 0L { gb.to_double() / gf.to_double() } else { 0.0 }
  if g_speed <= 1.0 {
    ok = false
  }

  // (乙) 查詢「G₁ 與 G₂ 是否同餘」：沒有「比較慢的替代法」。
  // 對照組是隨機搜尋可逆 A 並檢驗 AᵀG₁A = G₂ —— 可逆矩陣有無窮多個，
  // 命中是測度零事件。實測其成功次數為 0，而慣性律每次都給出答案。
  let n0 = 3
  let g1 = rand_sym_q(rng, n0)
  let a0 = rand_invertible(rng, n0)
  let g2 = congruence(Cost::new(), g1, a0) // 確實同餘
  let mut hits = 0
  for _t in 0..<400 {
    let a = rand_invertible(rng, n0)
    if congruence(Cost::new(), g1, a).equals(g2) {
      hits = hits + 1
    }
  }
  let dec1 = inertia_label(qinertia(g1, Cost::new()))
  let dec2 = inertia_label(qinertia(g2, Cost::new()))
  if dec1 != dec2 {
    ok = false
  }
  if hits != 0 {
    ok = false // 若隨機搜尋真的命中了，本對照失效，措辭須重寫
  }

  // ── 定理 197-3（可行性律：複 Hermitian 之實化）──────────────
  // ℝ 軌的 Jacobi 只接受實對稱矩陣 —— 複 Hermitian 根本餵不進去，
  // 這不是「比較慢」，是型別層次的不可行。實化之後才可行，
  // 且其譜為原 Hermitian 譜之二重。報酬不是比值。
  let h = rand_herm_pd(rng, 3)
  let hr = realify_mat(h)
  let cr = Cost::new()
  let (lam, _q, _r) = cjacobi_eigen(hr, 1.0e-12, 3000, cr)
  if hr.mrows != 6 {
    ok = false
  }
  // 譜須成對：排序後第 2i 與第 2i+1 相等
  let ls = lam.copy()
  sort_doubles(ls)
  let mut paired = true
  for i in 0..<3 {
    if absd(ls[2 * i] - ls[2 * i + 1]) > 1.0e-8 * (1.0 + absd(ls[2 * i])) {
      paired = false
    }
  }
  if !paired {
    ok = false
  }
  let feas : Payoff = Feasibility(
    "複 Hermitian → 實對稱（維數加倍）",
  )
  if feas.psame_kind(Speedup(1.0)) || feas.psame_kind(Invariant("x")) {
    ok = false
  }

  // ── 命題 197-4（三類報酬互不可比）──────────────────────────
  let ps : Array[Payoff] = [
    Speedup(g_speed),
    Invariant("慣性指數"),
    Feasibility("實化"),
  ]
  for i in 0..<3 {
    for j in 0..<3 {
      if ps[i].psame_kind(ps[j]) != (i == j) {
        ok = false
      }
    }
  }
  mk_check(
    "N-34 三類報酬（加速／不變量／可行性）",
    ok,
    iner.cltrials + dt.cltrials + tr.cltrials + 3 + 400 + 9,
    "Sylvester 慣性律於 5 組維數精確成立（" +
    iner.cldetail +
    "），樣本確為不定（" +
    indefinite.to_string() +
    "/4 組同時有正負慣性）；負對照 det 與 trace 於同餘下皆改變。同一條律之報酬型別隨查詢而異：查詢「sig(AᵀGA)」時它是加速律，實測 ×" +
    fmt_d(g_speed, 2) +
    "（省下形成 AᵀGA 並對更大數字消去）；查詢「G₁ 與 G₂ 是否同餘」時它是可行性律 —— 對照組隨機搜尋可逆 A 四百次命中 " +
    hits.to_string() +
    " 次（可逆矩陣無窮多，命中為測度零事件），而慣性律一次就判定 " +
    dec1 +
    " ≡ " +
    dec2 +
    "。可行性律：複 Hermitian 餵不進實 Jacobi（型別層次不可行，非「較慢」），實化為 6×6 實對稱後可行，且譜恰為原譜之二重。三類報酬兩兩不同類，不可比較大小。",
  )
}

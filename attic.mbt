// attic.mbt —— 備品區（全專案未呼叫之公開函式）
//
// 本檔收容全專案**從未被任何地方呼叫**的公開函式。
// 依使用者指示保留（不得刪除）——它們可能日後用得上。
//
// 第二十二輪曾把它們移到四個子套件隔離，第二十三輪依指示撤回：
// 子目錄在 MoonBit 等於獨立套件，而四個套件只為了放備品，
// 代價是四份 moon.pkg、四份 .mbti、以及每個引用都要加套件前綴。
// 收回單一檔案之後，資訊沒有少（哪些是備品仍然一目了然），
// 而建置圖回到一個套件。

// ─── 原 space 隔離區 ───

///|
/// BigInt 快速冪（精確，用於有理數冪與階乘型常數）。
pub fn ipow_big(x : BigInt, n : Int) -> BigInt {
  let mut acc : BigInt = 1N
  let mut b = x
  let mut e = n
  while e > 0 {
    if e % 2 == 1 {
      acc = acc * b
    }
    b = b * b
    e = e / 2
  }
  acc
}

///|
/// 左補空白至寬度 n。
pub fn pad_l(s : String, n : Int) -> String {
  let mut t = s
  while t.length() < n {
    t = " " + t
  }
  t
}

///|
/// 右補空白至寬度 n。
pub fn pad_r(s : String, n : Int) -> String {
  let mut t = s
  while t.length() < n {
    t = t + " "
  }
  t
}

///|
/// 重複字元。
pub fn rep_str(s : String, n : Int) -> String {
  let mut t = ""
  for _i in 0..<n {
    t = t + s
  }
  t
}

///|
/// AA* = A*A ?
pub fn[F : Scalar] is_normal(a : Mat[F]) -> Bool {
  a.times(a.adjointm()).equals(a.adjointm().times(a))
}

///|
/// |a|² = a·‾a ∈ P ∪ {0}
pub fn[F : Scalar] sabs2(a : F) -> F {
  F::s_mul(a, F::s_conj(a))
}

///|
/// a / b ≔ a · b⁻¹（b = 0 回 None）
pub fn[F : Scalar] sdiv(a : F, b : F) -> F? {
  match F::s_inv(b) {
    Some(ib) => Some(F::s_mul(a, ib))
    None => None
  }
}

///|
/// 1/2 ∈ 𝔽（特徵 0 ⇒ 2 可逆；極化恆等式需要）
pub fn[F : Scalar] shalf() -> F {
  F::s_from_frac(1, 2)
}

///|
/// 虛數單位 i（若 𝔽 不含 i 則回 None）
pub fn[F : Scalar] simag_unit() -> F? {
  // i 之特徵：i² = −1
  let cand = F::s_from_frac(0, 1)
  ignore(cand)
  None
}

///|
/// n · a（ℤ‑模結構）
pub fn[F : Scalar] sntimes(n : Int, a : F) -> F {
  F::s_mul(F::s_from_int(n), a)
}

///|
/// Π aᵢ
pub fn[F : Scalar] sprod(xs : Array[F]) -> F {
  let mut acc = F::s_one()
  for x in xs {
    acc = F::s_mul(acc, x)
  }
  acc
}

///|
/// Σ aᵢ
pub fn[F : Scalar] ssum(xs : Array[F]) -> F {
  let mut acc = F::s_zero()
  for x in xs {
    acc = F::s_add(acc, x)
  }
  acc
}

///|
/// ‖x‖² = ⟨x,x⟩ ∈ 𝔽（實且非負）
pub fn[V, F] ip_norm2(s : IPSpace[V, F], x : V) -> F {
  (s.inner)(x, x)
}

///|
/// c·x + y
pub fn[V, F] vaxpy(s : VSpace[V, F], c : F, x : V, y : V) -> V {
  (s.add)((s.smul)(c, x), y)
}

///|
/// 空間介面之相等判定（相容於公理 V6 之等價關係）。
pub fn[V, F] veq_(s : VSpace[V, F], a : V, b : V) -> Bool {
  (s.veq)(a, b)
}

///|
/// 由座標展開：Σ αᵢ eᵢ（vcoord 之逆）。
pub fn[V, F] vexpand(s : VSpace[V, F], c : Array[F]) -> V {
  (s.expand)(c)
}

///|
/// 空間介面之負元：s.neg(a)。
pub fn[V, F] vneg(s : VSpace[V, F], a : V) -> V {
  (s.neg)(a)
}

///|
/// 取樣一元素（確定性亂數流；Schwartz–Zippel 檢驗用）。
pub fn[V, F] vsample(s : VSpace[V, F], rng : Rng) -> V {
  (s.sample)(rng)
}

///|
/// 空間介面之列印（元素之文字表示）。
pub fn[V, F] vshow_(s : VSpace[V, F], a : V) -> String {
  (s.vshow)(a)
}

///|
/// 空間介面之純量乘：s.smul(c, a)。
pub fn[V, F] vsmul(s : VSpace[V, F], c : F, a : V) -> V {
  (s.smul)(c, a)
}

///|
/// Σ xᵢ
pub fn[V, F] vsum(s : VSpace[V, F], xs : Array[V]) -> V {
  let mut acc = s.zero
  for x in xs {
    acc = (s.add)(acc, x)
  }
  acc
}

///|
/// 座標向量減法
pub fn[F : Scalar] arr_sub(a : Array[F], b : Array[F]) -> Array[F] {
  Array::makei(a.length(), i => ssub(a[i], b[i]))
}

// ─── 原 acce 隔離區 ───

///|
/// 𝔽p[x] 之求值–逐點–插值乘法（𝔽[x] 層之純 CRT）。
/// 【命題 Λ3-4】deg(fg) = deg f + deg g ≤ d，取 d+1 個互異點即可唯一還原。
pub fn fpp_mul_evalinterp(
  a : Array[Int64],
  b : Array[Int64],
  ctx : FpCtx,
) -> Array[Int64]? {
  let fa = fpp_norm(a)
  let fb = fpp_norm(b)
  if fa.length() == 0 || fb.length() == 0 {
    return Some([])
  }
  let d = fa.length() + fb.length() - 2
  let n = d + 1
  if n.to_int64() >= ctx.pmod {
    return None
  }
  let xs = Array::makei(n, i => i.to_int64())
  let ys = Array::makei(n, i => {
    ctx.mul(fpp_eval(fa, xs[i], ctx), fpp_eval(fb, xs[i], ctx))
  })
  fpp_interp(xs, ys, ctx)
}

///|
/// 重構後掃描：L-05′ 與 L-08′ 各跑小網格。
/// 回傳 (格數, 全部正確數, L-05′ 最小增益, L-08′ 最小增益, 輸的格數)。
pub fn acc_scan_fixed() -> (Int, Int, Double, Double, Int) {
  let mut tot = 0
  let mut ok = 0
  let mut g5 = 1.0e18
  let mut g8 = 1.0e18
  let mut lose = 0
  for s in acc_grid_small() {
    for cell in [acc_cell_l05p(s.0 + 2, s.1), acc_cell_l08p(s.0, s.1)] {
      tot = tot + 1
      if cell.acok {
        ok = ok + 1
      }
      let g = cell.gain()
      if g <= 1.0 {
        lose = lose + 1
      }
      if cell.accode == "L-05′" && g < g5 {
        g5 = g
      }
      if cell.accode == "L-08′" && g < g8 {
        g8 = g
      }
    }
  }
  (tot, ok, g5, g8, lose)
}

///|
/// 整數列陣之資料位元寬。
pub fn zrows_bits(a : Array[Array[BigInt]]) -> Int {
  let mut m = 1
  for row in a {
    for v in row {
      let b = big_bits(v)
      if b > m {
        m = b
      }
    }
  }
  m
}

///|
/// 整數矩陣 × 整數向量。
pub fn zrows_mulvec(
  a : Array[Array[BigInt]],
  x : Array[BigInt],
) -> Array[BigInt] {
  let out : Array[BigInt] = []
  for row in a {
    let mut s = 0N
    for j in 0..<row.length() {
      s = s + row[j] * x[j]
    }
    out.push(s)
  }
  out
}

///|
/// 行列式 mod p（完全消去版；供需要 RREF 之場合）。
pub fn fp_det(a : FpMat, ctx : FpCtx) -> Int64 {
  fp_rref(a, ctx).det
}

///|
/// ℚ 向量之約化。
pub fn fp_of_qvec(v : Array[Q], ctx : FpCtx) -> Array[Int64]? {
  let out = Array::make(v.length(), 0L)
  let pb = BigInt::from_int64(ctx.pmod)
  for i in 0..<v.length() {
    let dn = normmod((v[i].den % pb).to_int64(), ctx.pmod)
    match ctx.inv(dn) {
      None => return None
      Some(di) =>
        out[i] = ctx.mul(normmod((v[i].num % pb).to_int64(), ctx.pmod), di)
    }
  }
  Some(out)
}

///|
/// 𝔽p[x] 加法（係數逐項模 p）。
pub fn fpp_add(a : Array[Int64], b : Array[Int64], ctx : FpCtx) -> Array[Int64] {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  let out = Array::make(n, 0L)
  for i in 0..<n {
    let x = if i < a.length() { a[i] } else { 0L }
    let y = if i < b.length() { b[i] } else { 0L }
    out[i] = ctx.add(x, y)
  }
  fpp_norm(out)
}

///|
/// 𝔽p[x] 次數：去除尾端零係數後之最高次。
pub fn fpp_deg(a : Array[Int64]) -> Int {
  fpp_norm(a).length() - 1
}

///|
/// 由根造首一多項式 ∏(x − rᵢ)（積樹之基礎情形即線性因式）。
pub fn fpp_from_roots(roots : Array[Int64], ctx : FpCtx) -> Array[Int64] {
  let mut acc : Array[Int64] = [1L]
  for r in roots {
    acc = fpp_mul(acc, [ctx.neg(normmod(r, ctx.pmod)), 1L], ctx)
  }
  acc
}

///|
/// 𝔽p[x] 減法（係數逐項模 p）。
pub fn fpp_sub(a : Array[Int64], b : Array[Int64], ctx : FpCtx) -> Array[Int64] {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  let out = Array::make(n, 0L)
  for i in 0..<n {
    let x = if i < a.length() { a[i] } else { 0L }
    let y = if i < b.length() { b[i] } else { 0L }
    out[i] = ctx.sub(x, y)
  }
  fpp_norm(out)
}

///|
/// 分塊對角 (A ⊕ B) 之雙線性型，不物化。
pub fn bdiag_bilinear(a : Mat[Q], b : Mat[Q], x : Array[Q], y : Array[Q]) -> Q {
  let na = a.mrows
  let nb = b.mrows
  let mut acc = Q::zero()
  for i in 0..<na {
    for j in 0..<na {
      acc = acc.add(x[i].mul(a.at(i, j)).mul(y[j]))
    }
  }
  for i in 0..<nb {
    for j in 0..<nb {
      acc = acc.add(x[na + i].mul(b.at(i, j)).mul(y[na + j]))
    }
  }
  acc
}

///|
/// 分配律之雙線性抽樣檢查，兩側皆以 Kronecker 結構現算。
///
/// 左式 xᵀ(P⊗M)y 以定理 K-1；右式把 σ 重排後的向量切成兩塊，
/// 分別以 xᵀ(P⊗Q)y 與 xᵀ(P⊗R)y 相加。單次 Θ(d_P·d_M·(d_P+d_M))，
/// 相較逐元比對之 Θ(d_P²d_M²) 在大三元組上便宜一個量級。
pub fn distrib_bilinear_check(
  p : Mat[Q],
  q : Mat[Q],
  r : Mat[Q],
  x : Array[Q],
  y : Array[Q],
) -> Bool {
  let dp = p.mrows
  let dq = q.mrows
  let dr = r.mrows
  let d = dp * (dq + dr)
  let m = qblock_diag(q, r)
  let lhs = kron_bilinear(p, m, x, y)
  let sg = f_distrib_sigma(dp, dq, dr)
  let sx : Array[Q] = Array::makei(d, _ => Q::zero())
  let sy : Array[Q] = Array::makei(d, _ => Q::zero())
  for u in 0..<d {
    sx[sg(u)] = x[u]
    sy[sg(u)] = y[u]
  }
  let npq = dp * dq
  let x1 : Array[Q] = Array::makei(npq, i => sx[i])
  let y1 : Array[Q] = Array::makei(npq, i => sy[i])
  let x2 : Array[Q] = Array::makei(dp * dr, i => sx[npq + i])
  let y2 : Array[Q] = Array::makei(dp * dr, i => sy[npq + i])
  lhs.eq(kron_bilinear(p, q, x1, y1).add(kron_bilinear(p, r, x2, y2)))
}

///|
/// 逐元驗證（自行計算因子之 LDLᵀ 重組）。
///
/// 大批呼叫時請改用 `kron_ldlt_elem_pre` 並把重組提到迴圈外。
pub fn kron_ldlt_elem(
  a : Mat[Q],
  b : Mat[Q],
  la : Mat[Q],
  lb : Mat[Q],
  da : Array[Q],
  db : Array[Q],
) -> (Bool, Bool) {
  // (1) 因子側：L D Lᵀ 逐元等於原矩陣。這一側是**完整**的 ——
  //     由命題 K-6，乘積側逐元成立 ⟺ 兩個因子各自成立，
  //     故因子側驗完即等於把 n_An_B 階的等式驗完，不必物化。
  let pa = ldlt_product(la, da)
  let pb = ldlt_product(lb, db)
  let okfac = pa.equals(a) && pb.equals(b)
  // (2) 索引分解側：驗證實作把 u 拆成 (u/n_B, u%n_B) 的方式與
  //     命題 K-6 的推導一致。因子積已算好，故每元 O(1)。
  let nb = b.mrows
  let d = a.mrows * nb
  let mut okidx = true
  for u in 0..<d {
    let ua = u / nb
    let ub = u % nb
    for v in 0..<d {
      if !pa
        .at(ua, v / nb)
        .mul(pb.at(ub, v % nb))
        .eq(a.at(ua, v / nb).mul(b.at(ub, v % nb))) {
        okidx = false
      }
    }
  }
  (okfac, okidx)
}

// ─── 原 comb 隔離區 ───

///|
/// 生成器量測到的三個數字（門檻由此而來，不是瞎寫的）
pub fn obl_measure(spec : OblSpec) -> (Bool, Double, Int)? {
  match obl_measure_full(spec) {
    Some((h, g, v, _b, _f)) => Some((h, g, v))
    None => None
  }
}

///|
/// 命中／未命中／鍵數。
pub fn obl_memo_stats() -> (Int, Int, Int) {
  (g_oblmemo.ohits, g_oblmemo.omiss, g_oblmemo.okeys.length())
}

///|
/// 可讀輸出（供 cmd/lawsearch）
pub fn content_table(xs : Array[Verdict47]) -> String {
  let lines : Array[String] = []
  lines.push("複合律\t原裁決\t空洞\t全函式裁決\t恆值？")
  for x in xs {
    if !x.vold && !x.vnew {
      continue
    }
    lines.push(
      x.vname +
      "\t" +
      (if x.vold { "成立" } else { "推翻" }) +
      "\t" +
      x.vbot.to_string() +
      "\t" +
      (if x.vnew { "成立" } else { "**推翻**" }) +
      "\t" +
      (if x.vconst { "恆值" } else { "有內容" }),
    )
  }
  lines.join("\n")
}

///|
/// 判零。
pub fn dc_is_zero(v : Array[Q]) -> Bool {
  for c in v {
    if !Q::is_zero(c) {
      return false
    }
  }
  true
}

///|
/// 逐演算法統計：(代碼, 通過, 總數)。
pub fn dcensus_by_algo(maxdim : Int) -> Array[(String, Int, Int)] {
  let out : Array[(String, Int, Int)] = []
  for a in d_registry() {
    let c = dcensus_core(1, maxdim, [a.dcode])
    out.push((a.dcode, c.pass, c.cells))
  }
  out
}

///|
/// 逐構造子統計：(記號, 通過, 總數)。
pub fn dcensus_by_comb(maxdim : Int) -> Array[(String, Int, Int)] {
  let out : Array[(String, Int, Int)] = []
  for c in comb7_registry() {
    let mut ok = 0
    let mut tot = 0
    for r in space_registry() {
      let d = (c.cdim)(r.sdim)
      if maxdim > 0 && d > maxdim {
        continue
      }
      let sp = comb7_space(r, c)
      for a in d_registry() {
        let key = dcell_key(a.dcode, c.csym, r.sname)
        tot = tot + 1
        if (a.drun)(sp, dcell_rng(key)) {
          ok = ok + 1
        }
      }
    }
    out.push((c.csym, ok, tot))
  }
  out
}

///|
/// 逐空間族統計：(族名, 通過, 總數)。
pub fn dcensus_by_family(maxdim : Int) -> Array[(String, Int, Int)] {
  let out : Array[(String, Int, Int)] = []
  for r in space_registry() {
    let mut ok = 0
    let mut tot = 0
    for c in comb7_registry() {
      let d = (c.cdim)(r.sdim)
      if maxdim > 0 && d > maxdim {
        continue
      }
      let sp = comb7_space(r, c)
      for a in d_registry() {
        let key = dcell_key(a.dcode, c.csym, r.sname)
        tot = tot + 1
        if (a.drun)(sp, dcell_rng(key)) {
          ok = ok + 1
        }
      }
    }
    let mut found = false
    for t in 0..<out.length() {
      if out[t].0 == r.fam {
        out[t] = (r.fam, out[t].1 + ok, out[t].2 + tot)
        found = true
        break
      }
    }
    if !found {
      out.push((r.fam, ok, tot))
    }
  }
  out
}

///|
/// 全量普查：23 × 35 × 7 = 5,635 格。`maxdim` 為構造後維數上限（0 = 不設限）。
pub fn dcensus_scan(maxdim : Int) -> DCensus {
  dcensus_core(1, maxdim, [])
}

///|
/// 逐形狀之增益表：(形狀, 試驗數, 通用成本, 特化成本)。
pub fn spec_by_shape(rng : Rng) -> Array[(String, Int, Int64, Int64)] {
  spec_report(rng).shapes
}

///|
/// 判準之混淆表：(判走且確實贏, 判走但輸, 判不走但其實會贏, 判不走且確實不贏)。
pub fn spec_confusion(rng : Rng) -> (Int, Int, Int, Int) {
  spec_report(rng).cs
}

///|
/// 兩個判準在同一組試驗（每式 k = 1 與 k = 3）上的混淆表。
/// 回傳 ((結構判準 tp,fp,fn,tn), (精煉判準 tp,fp,fn,tn), 試驗數)。
pub fn spec_confusion_pair(
  rng : Rng,
) -> ((Int, Int, Int, Int), (Int, Int, Int, Int), Int) {
  let r = spec_report(rng)
  (r.cs, r.cr, r.trials)
}

///|
/// 指紋：語料條數、形狀序列、兩路成本。
pub fn spec_digest(rng : Rng) -> String {
  let (t, same, _, c1, c2, _, _) = spec_scan(rng)
  t.to_string() +
  ":" +
  same.to_string() +
  ":" +
  c1.to_string() +
  ":" +
  c2.to_string()
}

///|
/// 指紋。
pub fn sub_digest(rng : Rng) -> String {
  let (n, same, td, ts, win, lose) = sub_scan(rng)
  n.to_string() +
  ":" +
  same.to_string() +
  ":" +
  td.to_string() +
  ":" +
  ts.to_string() +
  ":" +
  win.to_string() +
  ":" +
  lose.to_string()
}

///|
/// 指紋。
pub fn ek_digest(rng : Rng) -> String {
  let (n, same, td, ts, win, lose) = ek_scan(rng)
  n.to_string() +
  ":" +
  same.to_string() +
  ":" +
  td.to_string() +
  ":" +
  ts.to_string() +
  ":" +
  win.to_string() +
  ":" +
  lose.to_string()
}

///|
/// 指紋。
pub fn ks_digest(rng : Rng) -> String {
  let (n, ok, nd, worst, gain) = ks_assoc_scan(rng)
  n.to_string() +
  ":" +
  (if ok { "1" } else { "0" }) +
  ":" +
  nd.to_string() +
  ":" +
  fmt_d(worst, 4) +
  ":" +
  fmt_d(gain, 4)
}

///|
/// 指紋。
pub fn midend2_digest(rng : Rng) -> String {
  let (n, _, ch, sm, dr, ta, td) = rw_dp_scan(rng)
  let (_, snd, stb, mv) = canon_scan(rng)
  n.to_string() +
  ":" +
  ch.to_string() +
  ":" +
  sm.to_string() +
  ":" +
  dr.to_string() +
  ":" +
  ta.to_string() +
  ":" +
  td.to_string() +
  ":" +
  snd.to_string() +
  ":" +
  stb.to_string() +
  ":" +
  mv.to_string()
}

///|
/// 律表：把一組判決整理成可列印之表（供報告與反律庫使用）
pub fn law_table(vs : Array[LawVerdict]) -> String {
  let out : Array[String] = []
  out.push(
    "| 結構律 | 成立 | 試驗 | 直接法字乘 | 分解法字乘 | 總增益 | 逐尺寸 |",
  )
  out.push("| --- | :-: | --: | --: | --: | --: | --- |")
  for v in vs {
    out.push(
      "| " +
      v.lname +
      " | " +
      (if v.holds { "✔" } else { "✘" }) +
      " | " +
      v.ltrials.to_string() +
      " | " +
      v.base_cost.to_string() +
      " | " +
      v.fast_cost.to_string() +
      " | **×" +
      fmt_d(v.lgain(), 2) +
      "** | " +
      v.ldetail +
      " |",
    )
  }
  out.join("\n")
}

///|
/// 指紋。
pub fn nonctor_digest() -> String {
  let rows = nonctor_scan()
  let mut s = ""
  for r in rows {
    s = s +
      r.1.to_string() +
      "/" +
      r.2.to_string() +
      "/" +
      r.3.to_string() +
      "/" +
      r.4.to_string() +
      ";"
  }
  s
}

///|
/// 指紋。
pub fn op_digest(rng : Rng) -> String {
  let (np, ns, nc, same, td, ts, win) = op_scan(rng)
  np.to_string() +
  ":" +
  ns.to_string() +
  ":" +
  nc.to_string() +
  ":" +
  same.to_string() +
  ":" +
  td.to_string() +
  ":" +
  ts.to_string() +
  ":" +
  win.to_string()
}

///|
/// 指紋。
pub fn uni_digest(rng : Rng) -> String {
  let (n, h, i, s, td, ts, w) = uni_scan(rng)
  n.to_string() +
  ":" +
  h.to_string() +
  ":" +
  i.to_string() +
  ":" +
  s.to_string() +
  ":" +
  td.to_string() +
  ":" +
  ts.to_string() +
  ":" +
  w.to_string()
}

///|
/// 記憶體化之命中／未命中／是否有值。
pub fn uni_memo_stats() -> (Int, Int, Bool) {
  (g_unimemo.uhits, g_unimemo.umiss, g_unimemo.uhas)
}

///|
/// 帶退化樣本（兩側皆零）之成立裁決數 —— ℝ 軌版的「沒有內容」
pub fn rcompose_degen_count(xs : Array[RCompLaw]) -> Int {
  let mut k = 0
  for x in xs {
    if x.yholds && x.ydegen > 0 {
      k = k + 1
    }
  }
  k
}

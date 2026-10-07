///|
/// N-53 之義務：中端規範化。
///
/// 重寫系統要驗四件事，缺一不可：
///   (1) 健全 —— 重寫後的空間與原空間相同（類 A 連 Gram 都逐元相同）
///   (2) 終止 —— 有良基測度嚴格下降，不會無限改寫
///   (3) 合流 —— 不同的改寫順序得到同一個範式
///   (4) 有效益 —— 範式真的比較便宜，否則規範化只是搬字過紙
pub fn ob_n53() -> Check {
  let mut ok = true

  // ── 逐規則：Gram 逐元不變 ∧ 測度嚴格下降 ────────────────
  let rules = rw_rule_check(ob_rng())
  if rules.length() != 10 {
    ok = false
  }
  let mut fired = 0
  for r in rules {
    if r.1 {
      fired = fired + 1
    }
    // 只要有觸發，就必須既保 Gram 又降測度
    if r.1 && !(r.2 && r.3) {
      ok = false
    }
  }
  // 語料必須真的把 10 條規則全部觸發過 —— 否則「全部正確」是空的
  if fired != 10 {
    ok = false
  }

  // ── 語料掃描 ────────────────────────────────────────────
  let (n, sa, sb, cf, idm, nf, dec, c1, c2) = rw_scan(ob_rng())
  if n != 40 {
    ok = false
  }
  // 定理 N53-1 健全性（類 A：Gram 逐元相同）
  if sa != 40 {
    ok = false
  }
  // 類 B：置換同餘之不變量（維數、行列式、跡）
  if sb != 40 {
    ok = false
  }
  // 命題 N53-3 合流（最內層優先 vs 最外層優先）
  if cf != 40 {
    ok = false
  }
  // 冪等 ∧ 範式上再也套不出規則
  if idm != 40 || nf != 40 {
    ok = false
  }
  // 定理 N53-2 終止測度不上升
  if dec != 40 {
    ok = false
  }
  // 效益：範式必須真的便宜（否則規範化沒有後端意義）
  if c1 != 463858L || c2 != 72008L {
    ok = false
  }
  if c2 >= c1 {
    ok = false
  }

  // ── 逐式成本側寫：聚合變便宜，但不保證每一式都變便宜 ────
  let (cheap, csame, dear) = rw_cost_profile(ob_rng())
  if cheap + csame + dear != 40 {
    ok = false
  }
  if cheap != 34 || csame != 5 || dear != 1 {
    ok = false
  }

  // ── 指紋（釘死範式之形狀序列）───────────────────────────
  let dg = rw_digest(ob_rng())
  if dg != "40:546600202" {
    ok = false
  }

  // ── 單例示範：(A⊗B)* 於 dim 16 ─────────────────────────
  let rng = ob_rng()
  let a : SpaceExpr = SLeaf("A", rand_gram(rng, 4))
  let b : SpaceExpr = SLeaf("B", rand_gram(rng, 4))
  let e : SpaceExpr = SDual(STensor(a, b))
  let (dd, nn, samegram) = rw_cost_pair(e)
  if e.sdim() != 16 {
    ok = false
  }
  if normalize(e).slabel() != "(A*⊗B*)" {
    ok = false
  }
  if !samegram {
    ok = false
  }
  if dd != 148002L || nn != 10841L {
    ok = false
  }
  let gain = dd.to_double() / nn.to_double()

  // ── 反向對照：故意放一條錯規則，健全性必須抓到 ──────────
  // (A⊗B)* → A*⊕B*（把張量寫成直和）維數就不對了。
  let wrong : Array[RwRule] = [
    {
      rname: "錯規則",
      rkind: 0,
      rstep: x => {
        match x {
          SDual(STensor(p, q)) => Some(SSum(SDual(p), SDual(q)))
          _ => None
        }
      },
    },
  ]
  let (we, _) = rw_normalize(e, wrong, true, 10)
  if we.sdim() == e.sdim() {
    ok = false
  }
  if we.sgram().equals(e.sgram()) {
    ok = false
  }
  mk_check(
    "N-53 中端規範化",
    ok,
    n * 6 + rules.length() * 2 + 8,
    "SpaceExpr 是本庫的空間中間表示：N-50 的座標化重編把載體各異的前端降到這個 IR，本條在 IR 上做重寫。重寫規則按它對 Gram 的作用分兩類 —— 類 A 使 Gram 逐元不變（換掉的是算法，不是空間），類 B 為置換同餘（換了基底排序，空間仍同構但 Gram 元素位置會動，故與已釘死的指紋不相容，分開收）。類 A 共 10 條：對偶對合 (A*)* → A、對偶穿過張量 (A⊗B)* → A*⊗B*、對偶穿過直和、扭曲融合 T[T[A,M],N] → T[A,MN]、嵌入融合、扭曲吸收進嵌入、對偶穿過扭曲 (T[A,M])* → T[A*,(M⁻¹)ᵀ]、單位扭曲／嵌入消去、Λ¹A → A、以及 ⊗ 與 ⊕ 的右結合正規序。義務對 " +
    rules.length().to_string() +
    " 條逐條驗兩件事且要求 " +
    fired.to_string() +
    "/10 全部被語料觸發過：套用後 Gram 逐元不變、且終止測度 μ = (對偶負重, 節點數, 左重) 字典序嚴格下降。語料 " +
    n.to_string() +
    " 式（16 式刻意對準每條規則的觸發形狀，24 式由 rand_expr 隨機生成）：類 A 健全 " +
    sa.to_string() +
    "/40（Gram 逐元相同）、類 B 健全 " +
    sb.to_string() +
    "/40（維數、行列式、跡三個置換同餘不變量相同）、合流 " +
    cf.to_string() +
    "/40（最內層優先與最外層優先得到同一範式，標籤與 Gram 都比）、冪等 " +
    idm.to_string() +
    "/40、範式上確實再也套不出規則 " +
    nf.to_string() +
    "/40、測度不上升 " +
    dec.to_string() +
    "/40。效益（逐式側寫）：變便宜 " +
    cheap.to_string() +
    " 式、不變 " +
    csame.to_string() +
    " 式、變貴 " +
    dear.to_string() +
    " 式 —— 那唯一變貴的一式是 A10 右結合正規序（((A⊗C)⊗B) → (A⊗(C⊗B))，1074 → 1108）。A10 只搬括號、不消節點，它存在的理由是合流而不是成本：沒有它，⊗ 的不同結合方式會停在不同的範式上；聚合效益由 A1–A9 提供。語料物化 Gram 之字乘法總數由 " +
    c1.to_string() +
    " 降為 " +
    c2.to_string() +
    "，×" +
    fmt_d(c1.to_double() / c2.to_double(), 2) +
    "。單例示範 (A⊗B)* 於 dim 16：直接路徑要先造 16×16 的 Kronecker 積再求逆，" +
    dd.to_string() +
    " 次字乘法；範式 (A*⊗B*) 只需兩次 4×4 求逆加一次 Kronecker，" +
    nn.to_string() +
    " 次，×" +
    fmt_d(gain, 2) +
    "，且兩者的 Gram 逐元相同。鑑別力：故意放一條錯規則 (A⊗B)* → A*⊕B*，健全性檢查當場抓出（維數由 16 變 8、Gram 不同）—— 若健全性只比對「有沒有跑完」，這條錯規則會靜靜通過。指紋 " +
    dg +
    "。",
  )
}

///|
/// N-54 之義務：專屬領域化。
///
/// 要驗三件事：
///   (1) 特化路徑與通用路徑**逐元相同** —— 快而錯沒有意義
///   (2) 特化真的比較快，而且慢的那些要指名
///   (3) 派工判準有混淆表，不是「我覺得應該走特化」
pub fn ob_n54() -> Check {
  let mut ok = true

  // ── 一次掃描產出一致性、增益、逐形狀與兩份混淆表 ────────
  let r = spec_report(ob_rng())
  if r.trials != 48 {
    ok = false
  }
  // 兩路必須逐元相同 —— 一例不同就是換了一個函式，不是加速
  if r.same != 48 {
    ok = false
  }
  if r.haspath != 22 {
    ok = false
  }
  if r.dense != 867577L || r.spec != 226531L {
    ok = false
  }
  if r.win != 43 || r.lose != 1 {
    ok = false
  }

  // ── 逐形狀 ──────────────────────────────────────────────
  if r.shapes.length() != 6 {
    ok = false
  }
  let mut nopath = 0
  for s in r.shapes {
    if s.0 == "外冪" || s.0 == "Kron 和" {
      // 無特化路徑者：兩路走同一條程式路徑，成本必須完全相等
      nopath = nopath + 1
      if s.2 != s.3 {
        ok = false
      }
    } else if s.3 >= s.2 {
      ok = false
    }
  }
  if nopath != 2 {
    ok = false
  }
  let names = ["張量", "直和", "對偶", "扭曲", "外冪", "Kron 和"]
  for t in 0..<6 {
    if r.shapes[t].0 != names[t] {
      ok = false
    }
  }

  // ── 派工判準之混淆表（結構判準 vs 精煉判準）─────────────
  if r.cs.0 != 43 || r.cs.1 != 1 || r.cs.2 != 0 || r.cs.3 != 4 {
    ok = false
  }
  if r.cr.0 != 43 || r.cr.1 != 0 || r.cr.2 != 0 || r.cr.3 != 5 {
    ok = false
  }

  // ── 規範化 → 領域化之接點 ───────────────────────────────
  let (ne, better, r1, r2, agree) = spec_norm_effect(ob_rng())
  if ne != 24 || agree != 24 {
    ok = false
  }
  if better != 11 {
    ok = false
  }
  if r1 != 82245L || r2 != 33149L {
    ok = false
  }

  // ── 端到端：Riesz 表示（D-08）走特化路徑 ────────────────
  let rng = ob_rng()
  let mut rok = 0
  let mut rtot = 0
  for e in spec_corpus(rng) {
    let phi : Array[Q] = Array::makei(e.sdim(), _ => Q::s_rand(rng))
    rtot = rtot + 1
    if spec_riesz_agrees(e, phi) {
      rok = rok + 1
    }
  }
  if rok != 24 || rtot != 24 {
    ok = false
  }
  mk_check(
    "N-54 專屬領域化",
    ok,
    r.trials * 2 + r.shapes.length() + ne + rtot,
    "通用求解器只看得到一個矩陣：它把 SpaceExpr 物化成 nm×nm 的 Gram 再做 Gauss 消去，Θ((nm)³)。但 IR 裡寫著這個 Gram 是怎麼來的。領域化就是不物化，按 IR 的形狀把 G(e)·X = B 拆開：葉子做 Gauss（多個右端共用一次求逆）；A⊗B 用 (A⊗B)·vec(X) = vec(A·X·Bᵀ)，把一次 (nm)³ 換成 m 次 n³ 加 n 次 m³；A⊕B 依分塊切右端；A* 最省 —— G(A*) = (G(A)⁻¹)ᵀ 而 G(A) 對稱，故解就是 G(A)·B，一次矩陣乘法，完全不必求逆；T[A,M] 拆成 Mᵀ·Z = B、G(A)·Y = Z、M·X = Y。Λᵏ、U、⊞ 無特化路徑，退回通用。實測 " +
    r.trials.to_string() +
    " 次試驗（24 式 × 右端個數 1 與 3）：兩路輸出逐元相同 " +
    r.same.to_string() +
    "/48（快而錯沒有意義，故這一條是前提不是附註），通用字乘法總計 " +
    r.dense.to_string() +
    " 對特化 " +
    r.spec.to_string() +
    "，×" +
    fmt_d(r.dense.to_double() / r.spec.to_double(), 2) +
    "；特化較快 " +
    r.win.to_string() +
    " 次、較慢 " +
    r.lose.to_string() +
    " 次。逐形狀（6 類全列，試驗數 " +
    r.shapes[0].1.to_string() +
    "/" +
    r.shapes[1].1.to_string() +
    "/" +
    r.shapes[2].1.to_string() +
    "/" +
    r.shapes[3].1.to_string() +
    "/" +
    r.shapes[4].1.to_string() +
    "/" +
    r.shapes[5].1.to_string() +
    "）：張量 ×" +
    fmt_d(r.shapes[0].2.to_double() / r.shapes[0].3.to_double(), 2) +
    "、直和 ×" +
    fmt_d(r.shapes[1].2.to_double() / r.shapes[1].3.to_double(), 2) +
    "、對偶 ×" +
    fmt_d(r.shapes[2].2.to_double() / r.shapes[2].3.to_double(), 2) +
    "、扭曲 ×" +
    fmt_d(r.shapes[3].2.to_double() / r.shapes[3].3.to_double(), 2) +
    "；外冪與 Kron 和無特化路徑，義務要求它們的兩路成本**完全相等**（退回同一條路，差一分錢都代表派工出錯）。唯一的敗例已指名：T[葉子] 於右端個數 k = 3 時通用 412 對特化 563 —— 特化要解三次 Θ(n³)，通用只付一次求逆而求逆的成本與 k 無關，k ≥ 2 時通用攤銷得更好。故本條給兩個判準並陳混淆表：結構判準（有特化路徑且非葉子就走）為 " +
    r.cs.0.to_string() +
    "/" +
    r.cs.1.to_string() +
    "/" +
    r.cs.2.to_string() +
    "/" +
    r.cs.3.to_string() +
    "（走且贏／走但輸／不走但會贏／不走且不贏），精煉判準（T[葉子] 於 k ≥ 2 不走）為 " +
    r.cr.0.to_string() +
    "/" +
    r.cr.1.to_string() +
    "/" +
    r.cr.2.to_string() +
    "/" +
    r.cr.3.to_string() +
    "。與 N-53 的接點是本條最值得記的一筆：原式 (A⊗B)* 落在對偶分支，得先把 A⊗B 物化；規範化成 A*⊗B* 之後落在張量分支，兩側各自是一次小小的矩陣乘法。整個語料上規範化使 " +
    better.to_string() +
    "/24 式變便宜，特化成本由 " +
    r1.to_string() +
    " 降為 " +
    r2.to_string() +
    "（×" +
    fmt_d(r1.to_double() / r2.to_double(), 2) +
    "），而 " +
    agree.to_string() +
    "/24 式兩路結果相同 —— 規範化不是美觀問題，它直接換掉後端走哪條路。端到端驗證取 D-08 Riesz 表示：泛函座標 φ ↦ Riesz 向量，通用路徑走 ⟦e⟧ 上的 riesz_vector，特化路徑走 spec_solve，" +
    rok.to_string() +
    "/" +
    rtot.to_string() +
    " 逐元相同。",
  )
}

///|
/// N-55 之義務：ℝ 軌進中端。
///
/// 中端的重寫規則在 ℚ 上是恆等式；到了 Float64 就只是「代數上相等」。
/// 本條把這件事量出來，而且量得出來的唯一理由是本庫有精確軌可當真值。
pub fn ob_n55() -> Check {
  let mut ok = true

  // ── Gram 求值：原式 vs 範式，對著 ℚ 真值量 ──────────────
  let (n, bt, ws, ti, ea, eb, fa, fb, km) = rmid_scan(ob_rng())
  if n != 24 {
    ok = false
  }
  if bt + ws + ti != 24 {
    ok = false
  }
  // 關鍵結論：沒有任何一式因規範化而變差
  if ws != 0 {
    ok = false
  }
  if bt != 8 || ti != 16 {
    ok = false
  }
  if fa != 9557L || fb != 1925L {
    ok = false
  }
  if fb >= fa {
    ok = false
  }
  // 誤差以量級帶釘死（浮點值本身不逐位比）
  if !(ea > 1.0e-10 && ea < 1.0e-7) {
    ok = false
  }
  if !(eb < 1.0e-13) {
    ok = false
  }
  if eb >= ea {
    ok = false
  }
  if !(km > 1.0e9 && km < 1.0e11) {
    ok = false
  }

  // ── 求解：以 ℚ 精確解為真值，量兩條 ℝ 路線 ──────────────
  let (m, sv, sb, db, es, ed, fs, fd) = rmid_solve_scan(ob_rng())
  if m != 24 || sv != 24 {
    ok = false
  }
  if sb != 17 || db != 2 {
    ok = false
  }
  if fs != 3992L || fd != 27838L {
    ok = false
  }
  if fs >= fd {
    ok = false
  }
  if !(es < 1.0e-7 && ed < 1.0e-7) {
    ok = false
  }
  if es >= ed {
    ok = false
  }

  // ── 鑑別力：故意用錯規則，誤差量測必須抓到 ──────────────
  let (good, bad) = rmid_control(ob_rng())
  if !(good < 1.0e-14) {
    ok = false
  }
  if !(bad > 1.0) {
    ok = false
  }
  if bad / good < 1.0e12 {
    ok = false
  }

  // ── 指紋 ────────────────────────────────────────────────
  if rmid_digest(ob_rng()) != "24:8:0:16:9557:1925" {
    ok = false
  }
  mk_check(
    "N-55 ℝ 軌進中端",
    ok,
    n * 5 + m * 4 + 6,
    "N-53 的 10 條重寫規則在 ℚ 上是恆等式：重寫前後 Gram 逐元相同。但後端真正要跑的多半在 ℝ 軌（Cholesky、特徵值、expm 只在 ℝ 上有），到了 IEEE-754 binary64，「逐元相同」立刻不成立 —— (A⊗B)* 要先造 nm×nm 的 Kronecker 積再求一次 nm 階逆，A*⊗B* 是兩次小逆再做 Kronecker，兩者是不同的算術序列，捨入誤差不同。於是冒出一個在 ℚ 軌根本不存在的問題：規範化讓答案更準還是更不準？本庫問得出這個問題，是因為同一個 SpaceExpr 可以在 ℚ 上算出**真值**；只有近似軌的數值庫只能拿兩個近似值互比，分不出誰靠近真值。量測（語料 " +
    n.to_string() +
    " 式，誤差為相對最大模偏差）：規範化後較準 " +
    bt.to_string() +
    " 式、較不準 " +
    ws.to_string() +
    " 式、完全相同 " +
    ti.to_string() +
    " 式 —— **沒有一式變差**。最差相對誤差由原式的 " +
    fmt_e(ea) +
    " 降到範式的 " +
    fmt_e(eb) +
    "（約 " +
    fmt_e(ea / eb) +
    " 倍），同時 flop 由 " +
    fa.to_string() +
    " 降到 " +
    fb.to_string() +
    "（×" +
    fmt_d(fa.to_double() / fb.to_double(), 2) +
    "）。更便宜與更準在這裡不是兩件事而是同一件：原式那條路要對一個條件數高達 " +
    fmt_e(km) +
    " 的大矩陣求逆，範式只對兩個小矩陣各求一次。端到端解 G·x = b（" +
    sv.to_string() +
    "/" +
    m.to_string() +
    " 式可解，真值取 ℚ 上的精確解）：特化路徑較準 " +
    sb.to_string() +
    " 式、通用路徑較準 " +
    db.to_string() +
    " 式，最差誤差 " +
    fmt_e(es) +
    " 對 " +
    fmt_e(ed) +
    "，flop " +
    fs.to_string() +
    " 對 " +
    fd.to_string() +
    "（×" +
    fmt_d(fd.to_double() / fs.to_double(), 2) +
    "）。鑑別力：只報「誤差很小」分不出「規則正確」與「量測不靈」。義務另跑一條**故意錯**的重寫 (A⊗B)* → (A*)⊗B（對偶只穿過左側），正確範式對真值的偏差是 " +
    fmt_e(good) +
    "，錯誤重寫是 " +
    fmt_e(bad) +
    " —— 相差 " +
    fmt_e(bad / good) +
    " 倍，誤差量測在這個尺度上毫無模糊空間。指紋 " +
    rmid_digest(ob_rng()) +
    "。",
  )
}

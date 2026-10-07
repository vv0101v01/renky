///|
/// N-32 之義務：SpaceExpr 擴編 —— 構造子由 4 個增為 8 個。
///
/// 使用者最初要求的是「把不同空間構造彼此組合」。原表達式樹只認得
/// ⊗、⊕、* 三個算子（加上葉共 4 個構造子），而本庫已經證出律的構造子
/// 遠不止於此。本條補上 Λᵏ 外冪、同餘扭曲、子空間限制、Kronecker 和 ⊞。
pub fn ob_n32() -> Check {
  let tbl = law_search_std(ob_rng())
  let rng = ob_rng()
  let mut ok = true

  // ── 定理 195-1（四個新構造子皆保 Gram 性）──────────────────
  // 每一個都必須：維數與 sdim() 相符、Gram 對稱、Gram 正定，
  // 且 sgram() 與 sgram_cost() 給出同一個矩陣（後者是計費版，不得走樣）。
  let base = SLeaf("L", rand_gram(rng, 4))
  let probes : Array[(String, SpaceExpr)] = [
    ("Λ²", SExt(base, 2)),
    ("Λ³", SExt(base, 3)),
    ("同餘", STwist(base, rand_invertible(rng, 4))),
    ("子空間", SSub(base, rand_tall(rng, 4, 3))),
    ("⊞", SKSum(base, SLeaf("M", rand_gram(rng, 3)))),
  ]
  let dims : Array[String] = []
  for pr in probes {
    let (nm, e) = pr
    let g = e.sgram()
    if g.mrows != e.sdim() || g.mcols != e.sdim() {
      ok = false
    }
    if !g.equals(g.transpose()) || !is_positive_definite(g) {
      ok = false
    }
    let c = Cost::new()
    if !g.equals(e.sgram_cost(c)) {
      ok = false
    }
    dims.push(nm + "→dim" + e.sdim().to_string())
  }
  // 維數公式須與理論一致
  if SExt(base, 2).sdim() != binom(4, 2) || SExt(base, 3).sdim() != binom(4, 3) {
    ok = false
  }
  if SSub(base, rand_tall(rng, 4, 3)).sdim() != 3 {
    ok = false
  }
  if SKSum(base, SLeaf("M", rand_gram(rng, 3))).sdim() != 12 {
    ok = false
  }

  // ── 定理 195-2（合成 ≡ 攤平，擴編樹上）────────────────────
  let rows : Array[String] = []
  for phi in ["inv", "det", "rank", "trace"] {
    match phispec_from_law(tbl, phi) {
      None => ok = false
      Some(sp) => {
        let r = Rng::new(91UL)
        let mut tb = 0L
        let mut tf = 0L
        for _t in 0..<8 {
          let e = rand_expr_ext(r, 2, 2)
          let (s, wb, wf, _l, _d) = synth_spec_compare(sp, e)
          if !s {
            ok = false
          }
          tb = tb + wb
          tf = tf + wf
        }
        rows.push(phi + " ×" + fmt_d(tb.to_double() / tf.to_double(), 2))
      }
    }
  }

  // ── 定理 195-3（Sylvester–Franke 進入通用合成器）──────────
  // N-10 的律原本只活在它自己那條手寫義務裡；擴編後，任何含 Λᵏ 節點的
  // 表達式樹在合成 det 時都會自動用上它，且增益隨維數上升。
  let sf_gains : Array[Double] = []
  let sf_rows : Array[String] = []
  match phispec_from_law(tbl, "det") {
    None => ok = false
    Some(sp) => {
      let r = Rng::new(5UL)
      for n in [4, 5, 6] {
        let e = SExt(SLeaf("L", rand_gram(r, n)), 2)
        let (s, wb, wf, _l, d) = synth_spec_compare(sp, e)
        if !s {
          ok = false
        }
        let g = wb.to_double() / wf.to_double()
        sf_gains.push(g)
        sf_rows.push(
          "Λ²(dim" +
          n.to_string() +
          ")→" +
          d.to_string() +
          " ×" +
          fmt_d(g, 1),
        )
      }
      if sp.pxname != "^C(n−1,k−1)" {
        ok = false
      }
    }
  }
  // 增益須隨維數單調上升
  for i in 1..<sf_gains.length() {
    if sf_gains[i] <= sf_gains[i - 1] {
      ok = false
    }
  }
  if sf_gains[0] <= 1.0 {
    ok = false
  }

  // ── 命題 195-4（trace 於新構造子上無律 —— 誠實負面）────────
  match phispec_from_law(tbl, "trace") {
    None => ok = false
    Some(sp) => if sp.pxname != "" || sp.ptname != "" { ok = false }
  }
  // 而 inv／det／rank 三者在兩個新構造子上都有律
  for phi in ["inv", "det", "rank"] {
    match phispec_from_law(tbl, phi) {
      None => ok = false
      Some(sp) => if sp.pxname == "" || sp.ptname == "" { ok = false }
    }
  }

  // ── 命題 195-5（搜尋空間之實際擴張）────────────────────────
  // 舊：二元 {⊗,⊕} 2 個、一元 {*} 1 個。新：二元 {⊗,⊕,⊞} 3 個、
  // 一元 {*,Λᵏ,同餘,子空間} 4 個。
  let old2 = shape_count(2, 2, 1)
  let new2 = shape_count(2, 3, 4)
  let old3 = shape_count(3, 2, 1)
  let new3 = shape_count(3, 3, 4)
  if new2 <= old2 * 5L || new3 <= old3 * 50L {
    ok = false
  }
  mk_check(
    "N-32 SpaceExpr 擴編（構造子 4 → 8）",
    ok,
    probes.length() * 4 + 4 * 8 + 3 + 6,
    "四個新構造子皆保 Gram 性（對稱、正定、維數相符、sgram ≡ sgram_cost）：" +
    dims.join("　") +
    "。合成 ≡ 攤平（擴編樹，深度 2）：" +
    rows.join("　") +
    "。Sylvester–Franke 已進入通用合成器（此前只活在 N-10 自己那條手寫義務裡）：" +
    sf_rows.join("　") +
    "，增益隨維數單調上升。trace 於 Λᵏ 與同餘上無律，如期無增益 —— 誠實登錄。搜尋空間：深度 2 之型態數由 " +
    old2.to_string() +
    " 增為 " +
    new2.to_string() +
    "，深度 3 由 " +
    old3.to_string() +
    " 增為 " +
    new3.to_string() +
    "。",
  )
}

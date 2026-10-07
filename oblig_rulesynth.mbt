///|
/// N-40 之義務：規則合成 —— 由「選規則」改為「解出規則」。
///
/// 驗收標準（第四輪計劃所訂）：把 `⊗ₛ` 自規則清單中刪除，adj 之律仍須被尋獲。
pub fn ob_n40() -> Check {
  let rng = ob_rng()
  let mut ok = true
  let phis : Array[(String, (Mat[Q], Cost) -> Mat[Q]?)] = [
    ("inv", (a, c) => qinv_gauss(a, c)),
    ("adj", (a, c) => qadj(c, a)),
    ("sq", (a, c) => Some(qmul_cost(c, a, a))),
    ("cube", (a, c) => Some(qmul_cost(c, a, qmul_cost(c, a, a)))),
    ("tr̃ans", (a, _c) => Some(a.transpose())),
  ]
  let rows : Array[String] = []
  let mut adj_rule : SynthRule? = None
  for ph in phis {
    let (nm, f) = ph
    match synth_rule_kron(f, rng) {
      None => {
        ok = false
        rows.push(nm + " 合成失敗")
      }
      Some(r) => {
        if nm == "adj" {
          adj_rule = Some(r)
        }
        rows.push(
          nm + " " + (if r.is_plain() { "樸素" } else { r.describe() }),
        )
      }
    }
  }

  // ── 定理 199-1（Sylvester 係數是「解出來」的）──────────────
  // 期望 p(n,m) = m − 1 ⇒ (c₀,c₁,c₂) = (−1, 0, 1)
  //      q(n,m) = n − 1 ⇒ (c₀,c₁,c₂) = (−1, 1, 0)
  // 原始碼中沒有任何一處寫過 m−1 或 n−1 這個式子。
  let ar = match adj_rule {
    None => return mk_check("N-40 規則合成", false, 1, "adj 合成失敗")
    Some(r) => r
  }
  if ar.sp0 != -1 || ar.sp1 != 0 || ar.sp2 != 1 {
    ok = false
  }
  if ar.sq0 != -1 || ar.sq1 != 1 || ar.sq2 != 0 {
    ok = false
  }

  // ── 定理 199-2（⊗ₛ 自清單刪除後，adj 之律仍被尋獲）────────
  // 人寫的規則清單裡，除 ⊗ₛ 外只有 ⊗ 與 ⊕；定律表顯示 adj 在這兩者
  // 之下皆被推翻 —— 亦即刪掉 ⊗ₛ 之後，選規則式的引擎對 adj 一無所獲。
  let tbl = law_search_std(ob_rng())
  if law_find(tbl, "adj", "⊗", "⊗") != Some(false) {
    ok = false
  }
  if law_find(tbl, "adj", "⊗", "⊕") != Some(false) {
    ok = false
  }
  // 而合成出的規則實跑必須逐例精確相符，且有增益
  let mut tb = 0L
  let mut tf = 0L
  let gains : Array[String] = []
  for sz in [(3, 3), (3, 4), (4, 4)] {
    let (n, m) = sz
    let a = rand_gram(rng, n)
    let b = rand_gram(rng, m)
    let (same, wb, wf) = apply_synth_rule(ar, (x, c) => qadj(c, x), a, b)
    if !same {
      ok = false
    }
    tb = tb + wb
    tf = tf + wf
    gains.push(
      "dim" +
      (n * m).to_string() +
      " ×" +
      fmt_d(wb.to_double() / wf.to_double(), 2),
    )
  }
  if tf >= tb {
    ok = false
  }

  // ── 定理 199-3（樸素 Φ 得樸素規則）────────────────────────
  // inv、sq、cube、transpose 之正解皆為 p = q = 0。若合成器把它們
  // 也配上一個非零指數，表示它在過度擬合。
  for ph in phis {
    let (nm, f) = ph
    if nm != "adj" {
      match synth_rule_kron(f, rng) {
        None => ok = false
        Some(r) => if !r.is_plain() { ok = false }
      }
    }
  }

  // ── 定理 199-4（退化樣本必須丟棄，不得猜解）────────────────
  // det = 1 時 a^p 對一切 p 皆同，指數完全不受約束。此時 solve_exponents
  // 必須回報「無解」（因為解不唯一），而不是回傳迴圈起點。
  if solve_exponents(Q::one(), Q::of_int(3), Q::one()) != None {
    ok = false
  }
  // 非退化時則必須給出唯一解：2^2 · 3^1 = 12
  if solve_exponents(Q::of_int(2), Q::of_int(3), Q::of_int(12)) != Some((2, 1)) {
    ok = false
  }
  // 完全不符 ansatz 者（無任何整數解）亦回 None
  if solve_exponents(Q::of_int(2), Q::of_int(3), Q::of_int(5)) != None {
    ok = false
  }

  // ── 命題 199-5（三點共線則無法定係數）──────────────────────
  // 擬合用的三組尺寸 (2,2)(2,3)(3,2) 不共線，係數矩陣可逆；
  // 若誤用 (2,2)(2,3)(2,4)（n 全同）則係數不唯一，必須回報失敗。
  if fit_affine([(2, 2, 0), (2, 3, 1), (2, 4, 2)]) != None {
    ok = false
  }
  if fit_affine([(2, 2, 1), (2, 3, 2), (3, 2, 1)]) == None {
    ok = false
  }
  mk_check(
    "N-40 規則合成（ansatz + 精確 ℚ 線性系統）",
    ok,
    5 * 5 + 3 + 6,
    "五個 Φ 之 ⊗ 規則全部由待定式解出，原始碼中沒有任何一處寫過 m−1 或 n−1：" +
    rows.join("　") +
    "。adj 解得 p = m−1、q = n−1（係數向量 (−1,0,1) 與 (−1,1,0)），即 Sylvester 型修正 —— 此前這個係數是人打字打進 rules_mat 的。驗收：人寫的規則清單中除 ⊗ₛ 外只有 ⊗ 與 ⊕，而定律表顯示 adj 在這兩者下皆被推翻（選規則式的引擎刪掉 ⊗ₛ 就一無所獲）；合成出的規則實跑逐例精確相符且有增益：" +
    gains.join("　") +
    "。退化樣本處理：det = 1 時指數不受約束，solve_exponents 如期回報解不唯一而丟棄（實測此處原本會回傳迴圈起點 p = −4，使 sq 的合成隨機失敗）；非退化時給出唯一解。三點共線（n 全同）時係數無法定出，fit_affine 如期失敗。",
  )
}

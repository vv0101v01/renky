///|
/// N-36 之義務：取樣分布修復。
///
/// 驗收標準（第三輪計劃所訂）：`rank/⊞/·` 必須由「成立」翻為「推翻」。
pub fn ob_n36() -> Check {
  let mut ok = true
  let before = law_search_std(ob_rng())
  let after = law_search_fixed(ob_rng())
  if before.length() != 72 || after.length() != 72 {
    ok = false
  }

  // ── 定理 198-1（指名之假陽性被推翻）────────────────────────
  if law_find(before, "rank", "⊞", "·") != Some(true) {
    ok = false // 修復前必須是成立的，否則無事可修
  }
  if law_find(after, "rank", "⊞", "·") != Some(false) {
    ok = false // 驗收標準
  }

  // ── 定理 198-2（其餘裁決一條不動）──────────────────────────
  // 修復若順手改掉別的裁決，就不是修復而是換一張表。
  let diff = law_diff(before, after)
  if diff.length() != 1 {
    ok = false
  }
  let mut hb = 0
  let mut ha = 0
  for t in before {
    if t.cholds {
      hb = hb + 1
    }
  }
  for t in after {
    if t.cholds {
      ha = ha + 1
    }
  }
  if hb != 16 || ha != 15 {
    ok = false
  }

  // ── 定理 198-3（單一分布不論選哪個都會偏）──────────────────
  // 直覺解法是「把正定分布換成混合分布」。實測顯示那會同時製造新的
  // 假陽性：輪替式混合讓每個候選只看到三種分布中的兩種，於是 det 類
  // 規則在降秩樣本上兩側同時為 0，空洞地成立。
  samp_reset()
  let naive = law_search_dist(ob_rng(), law_grid_std(), samp_mixed)
  let ndiff = law_diff(before, naive)
  let mut new_fp = 0
  let mut fixed_one = 0
  for d in ndiff {
    let (_p, _c, _r, vb, vn) = d
    if !vb && vn {
      new_fp = new_fp + 1 // 修復前推翻、修復後成立 ⇒ 新的假陽性
    }
    if vb && !vn {
      fixed_one = fixed_one + 1
    }
  }
  if new_fp < 1 {
    ok = false // 若輪替式混合其實沒有副作用，本條之論點不成立
  }
  if fixed_one != 1 {
    ok = false
  }

  // ── 定理 198-4（手工反例與引擎裁決一致）────────────────────
  // N-26 給出的反例：A = diag(1, −1)、B = [1]。
  // A⊞B = diag(2, 0)，rank = 1，而 rank A · rank B = 2 · 1 = 2。
  let a : Mat[Q] = Mat::build(2, 2, (i, j) => {
    if i != j {
      Q::zero()
    } else if i == 0 {
      Q::one()
    } else {
      Q::of_int(-1)
    }
  })
  let b : Mat[Q] = Mat::build(1, 1, (_i, _j) => Q::one())
  let ks = qkron_sum(a, b)
  if mrank(ks) != 1 || mrank(a) * mrank(b) != 2 {
    ok = false
  }

  // ── 命題 198-5（假陽性之成因：正定 ⇒ 恆滿秩）───────────────
  // 正定取樣下 rank 恆等於維數，於是 rank(A⊞B) = nm 與
  // rank(A)·rank(B) = n·m 逐例相等 —— 相等來自建構，不是來自律。
  // 降秩取樣下兩者立刻分離。
  let rng = ob_rng()
  let mut pd_full = 0
  let mut sing_deficient = 0
  for n in [2, 3, 4] {
    if mrank(samp_gram(rng, n)) == n {
      pd_full = pd_full + 1
    }
    if mrank(samp_singular(rng, n)) < n {
      sing_deficient = sing_deficient + 1
    }
  }
  if pd_full != 3 || sing_deficient != 3 {
    ok = false
  }

  // ── 命題 198-6（修復不影響下游合成器）──────────────────────
  // N-31 的組裝器只讀 ⊗ 與 ⊕ 兩個構造子的規則，而差異僅在 ⊞ 一條，
  // 故七個合成器由新舊兩表組出來必須完全一致。
  for phi in ["inv", "det", "trace", "rank", "sq", "cube", "adj"] {
    match (phispec_from_law(before, phi), phispec_from_law(after, phi)) {
      (Some(x), Some(y)) =>
        if x.pkname != y.pkname || x.psname != y.psname {
          ok = false
        }
      _ => ok = false
    }
  }
  let (dp, dc, dr, _vb0, _va0) = diff[0]
  mk_check(
    "N-36 取樣分布修復",
    ok,
    before.length() + after.length() + naive.length() + 12,
    "修復前（正定分布）成立 " +
    hb.to_string() +
    "／72，修復後（四樣本混合：正定 ×2、不定 ×1、降秩 ×1）成立 " +
    ha.to_string() +
    "／72，逐條差異恰 1 條：" +
    dp +
    "/" +
    dc +
    "/" +
    dr +
    " 由成立翻為推翻 —— 即 N-26 指認之假陽性，驗收標準達成，其餘 15 條真律一條不動。成因：正定矩陣恆滿秩（實測 3/3），故 rank(A⊞B) = nm 與 rank(A)·rank(B) = n·m 逐例相等，相等來自建構而非來自律；降秩取樣（實測 3/3 確為降秩）立刻把兩者分開。手工反例 A = diag(1,−1)、B = [1] 給出 rank(A⊞B) = 1 ≠ 2 = rank A · rank B，與引擎裁決一致。**但換分布本身也會引入偏誤**：直覺做法「把正定換成輪替式混合」雖然同樣推翻了該假陽性，卻另外製造了 " +
    new_fp.to_string() +
    " 條新假陽性 —— 每個候選只看到三種分布中的兩種，det 類規則在降秩樣本上兩側同時為 0 而空洞成立。故本條採「每個候選跑完全部四個樣本」，一條律要判成立必須在每一種分布下都成立。修復不影響下游：七個合成器由新舊兩表組出之規則完全一致（差異僅在 ⊞，而組裝器只讀 ⊗ 與 ⊕）。",
  )
}

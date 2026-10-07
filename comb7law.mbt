///|
/// # N-78…N-82 七構造子之封閉式 Gram 與全域交叉普查
///
/// ## 問題
///
/// 本庫的空間註冊表有 45 個葉子（9 族，涵蓋題目要求的全部 12 類空間），
/// 而第七輪新增的 7 個構造子
///
/// ```text
///   H      同態        Hom(W₂, −) ≅ W₂* ⊗ −        dim ↦ 2n
///   Λⁿ⁻¹   餘維一外冪  Λ^{n−1}(−)                    dim ↦ n
///   S²     對稱平方    Sym²(−)                       dim ↦ n(n+1)/2
///   **     雙對偶      (−)**                         dim ↦ n
///   D      倍化        (−) ⊕ (−)                     dim ↦ 2n
///   U½     半子空間    前 ⌈n/2⌉ 個座標之子空間       dim ↦ ⌈n/2⌉
///   Tᵀ     轉置扭曲    Mᵀ(−)M，M = unitri(n)ᵀ        dim ↦ n
/// ```
///
/// 逐一作用其上得 45 × 7 = **315 個相異的有限維內積空間**。
///
/// 在第十一輪之前，這 315 格只被檢查兩件事：維數公式相符、Gram 正定
/// （`comb14_stats`）。這是**覆蓋廣而驗證淺** —— 一個算錯的 Gram 只要
/// 維數對、仍然正定，就能完整通過。本輪把每一格補成
///
/// ```text
///   (1) Gram 對稱          (2) 維數公式       (3) 正定（Θ(n³) 整數 Sylvester）
///   (4) 封閉式逐元一致      (5) 兩側對照       (6) Cauchy–Schwarz
///   (7) Riesz 表示可解且表示正確
/// ```
///
/// 其中 (4) 是關鍵：為每一個構造子獨立推導一條**封閉式**，與
/// `SpaceExpr::sgram()` 的泛型遞迴路徑逐元對帳。兩條路徑在數學上同值
/// 但在程式上無共用碼，故一致即為交叉驗證。
///
/// ## 七條封閉式（定理 N78-1 … N78-7）
///
/// 記 V 之 Gram 為 G（n×n 對稱正定），W₂ 之 Gram 為 G_W = [[2,1],[1,2]]。
///
/// **N78-1（同態 / Hilbert–Schmidt）**：Hom(W,V) 之自然內積為
/// ⟨f,g⟩ = tr(f* ∘ g)。在基 {E_{ij} : w_i ↦ v_j} 下
///
/// ```text
///   ⟨E_{ij}, E_{kl}⟩ = (G_W⁻¹)[i][k] · G_V[j][l]
/// ```
///
/// 即 Gram = G_W⁻¹ ⊗ G_V。證明：f* 由 ⟨f w, v⟩_V = ⟨w, f* v⟩_W 定義，
/// 以矩陣表示 f* = G_W⁻¹ fᵀ G_V；代入 tr(f* g) 並取 f = E_{ij}、g = E_{kl}
/// 得上式。注意 W 側出現的是 **G_W⁻¹** 而非 G_W —— 這正是 Hom(W,−) ≅ W*⊗−
/// 中那個對偶的痕跡，也是本式最容易寫錯之處（兩側對照即針對此點）。
///
/// **N78-2（餘維一外冪即對偶扭轉）**：Λ^{n−1}V ≅ V* ⊗ det V，具體地
///
/// ```text
///   C_{n−1}(G)[p][q] = (−1)^{p+q} · det(G) · G⁻¹[n−1−p][n−1−q]
/// ```
///
/// 證明：以字典序排列的 (n−1)-子集中，第 p 個恰為「略去指標 n−1−p」，
/// 故 C_{n−1}(G)[p][q] = det(G[{i}ᶜ, {j}ᶜ])，其中 i = n−1−p、j = n−1−q。
/// 由餘因子公式 adj(G)[j][i] = (−1)^{i+j} det(G[{i}ᶜ,{j}ᶜ]) 與
/// adj(G) = det(G)·G⁻¹，並用 G 對稱（故 G⁻¹ 對稱）消去指標順序，
/// 再以 (−1)^{2(n−1)−p−q} = (−1)^{p+q} 化簡即得。∎
///
/// 成本：泛型路徑 `compound(G, n−1)` 物化 n² 個 (n−1) 階子式，
/// 每個 Θ(n³) ⇒ Θ(n⁵)；封閉式只做一次反矩陣與一次行列式 ⇒ Θ(n³)。
///
/// **N78-3（對稱平方）**：見 N-75（`spec_sym_sq_gram`），Θ(d·n⁴) → Θ(d²)。
///
/// **N78-4（雙對偶即恆等函子）**：G 對稱正定 ⇒ G⁻¹ 對稱 ⇒
/// ((G⁻¹)ᵀ)⁻¹ᵀ = (G⁻¹)⁻¹ = G，**逐元相等而非僅同構**。
/// 故 ** 在 Gram 層面是嚴格的恆等函子，Θ(n³) → Θ(1)。
///
/// **N78-5（倍化）**：V⊕V 之 Gram 為分塊對角 diag(G,G) = I₂ ⊗ G。
/// 注意 I₂⊗G ≠ G⊗I₂（除非 G 為純量陣）—— 指標順序即兩側對照之著力點。
///
/// **N78-6（半子空間）**：S 為 n×⌈n/2⌉ 之座標嵌入 ⇒ SᵀGS 恰為 G 之
/// **前** ⌈n/2⌉ 階主子陣（不是後 ⌈n/2⌉ 階），Θ(n²·k) → Θ(k²) 複製。
///
/// **N78-7（轉置扭曲）**：M = unitri(n)ᵀ 滿足 M[i][j] = 1 ⟺ i = j 或 i = j+1。
/// 故
///
/// ```text
///   (MᵀGM)[p][q] = Σ_{i ∈ {p,p+1}∩[0,n)} Σ_{j ∈ {q,q+1}∩[0,n)} G[i][j]
/// ```
///
/// 即一個 2×2 方框和，每元至多 4 次加法、**零次乘法**，
/// Θ(n³) 兩次稠密乘法 → Θ(n²) 純加法。

// ---------------------------------------------------------------------------
//  七條封閉式
// ---------------------------------------------------------------------------

///|
/// 【N78-1】同態 Hom(W,V) 之 Gram = G_W⁻¹ ⊗ G_V。
pub fn cf_hom(gw : Mat[Q], g : Mat[Q], c : Cost) -> Mat[Q] {
  let wi = match qinv_gauss(gw, c) {
    Some(h) => h
    None => Mat::ident(gw.mrows)
  }
  mkron(wi, g)
}

///|
/// 【N78-1 之獨立參照】由 Hilbert–Schmidt 內積 ⟨f,g⟩ = tr(f* g) 直接組裝。
///
/// 不走 Kronecker：對每一對基映射 E_{ij}、E_{kl}，實際造出矩陣、
/// 以 f* = G_W⁻¹ fᵀ G_V 算出伴隨、再取跡。這是一條與 `cf_hom` 完全
/// 無共用碼的第三路徑，故可用來證明 Kronecker 式本身沒寫反。
pub fn hs_gram_ref(gw : Mat[Q], g : Mat[Q], c : Cost) -> Mat[Q] {
  let w = gw.mrows
  let n = g.mrows
  let wi = match qinv_gauss(gw, c) {
    Some(h) => h
    None => Mat::ident(w)
  }
  // 基映射 E_{ij} : W → V，矩陣為 n×w，第 (j,i) 元為 1
  let emat = (i : Int, j : Int) => Mat::build(n, w, (r, s) => if r == j && s == i {
    Q::one()
  } else {
    Q::zero()
  })
  Mat::build(w * n, w * n, (u, v) => {
    let i = u / n
    let j = u % n
    let k = v / n
    let l = v % n
    let f = emat(i, j)
    let gg = emat(k, l)
    // f* = G_W⁻¹ fᵀ G_V  （w×n）
    let fstar = wi.times(f.transpose()).times(g)
    fstar.times(gg).trace()
  })
}

///|
/// 【N78-2】餘維一外冪之封閉式：(−1)^{p+q}·det(G)·G⁻¹[n−1−p][n−1−q]。
///
/// ## 前提：G 必須可逆
///
/// 封閉式由 adj(G) = det(G)·G⁻¹ 導出，而泛型 `compound` 沒有這個前提 ——
/// 它直接算子式，奇異矩陣照樣有定義。故**封閉式的定義域比它要取代的
/// 那條路徑小**，派工時必須先檢查，不能假設「Gram 都是正定的所以都可逆」：
/// N-52／N-61 的擾動表 `空間⊥` 裡就有刻意造出來的奇異 Gram。
///
/// 回傳 `None` 表示 G 奇異，呼叫端應退回 `compound`。
pub fn cf_codim1_opt(g : Mat[Q], c : Cost) -> Mat[Q]? {
  let n = g.mrows
  if n <= 1 {
    return Some(Mat::build(1, 1, (_, _) => Q::one()))
  }
  match qinv_gauss(g, c) {
    None => None
    Some(gi) => {
      let dt = mdet(g)
      Some(
        // 指標順序：adj(G)[j][i] = (−1)^{i+j}det(G[{i}ᶜ,{j}ᶜ])，而
        // adj(G) = det(G)·G⁻¹，故取的是 G⁻¹[j][i] 即 gi.at(n−1−q, n−1−p)。
        // G 對稱時兩者相同，**不對稱時不同** —— 擾動表 空間⊥ 內的
        // 「非對稱型」正是為此而存在，不可依賴對稱性化簡。
        Mat::build(n, n, (p, q) => {
          let v = dt.mul(gi.at(n - 1 - q, n - 1 - p))
          if (p + q) % 2 == 1 {
            v.neg()
          } else {
            v
          }
        }),
      )
    }
  }
}

///|
/// 可逆前提下的封閉式；奇異時退回 `compound`（保持全函數）。
pub fn cf_codim1(g : Mat[Q], c : Cost) -> Mat[Q] {
  match cf_codim1_opt(g, c) {
    Some(m) => m
    None => compound(g, g.mrows - 1, c)
  }
}

///|
/// 【N78-4】雙對偶之封閉式：恆等。
pub fn cf_bidual(g : Mat[Q]) -> Mat[Q] {
  g
}

///|
/// 【N78-5】倍化之封閉式：I₂ ⊗ G（分塊對角）。
pub fn cf_double(g : Mat[Q]) -> Mat[Q] {
  let n = g.mrows
  Mat::build(2 * n, 2 * n, (i, j) => if i / n == j / n {
    g.at(i % n, j % n)
  } else {
    Q::zero()
  })
}

///|
/// 【N78-6】半子空間之封閉式：前 ⌈n/2⌉ 階主子陣。
pub fn cf_half(g : Mat[Q]) -> Mat[Q] {
  let k = (g.mrows + 1) / 2
  Mat::build(k, k, (i, j) => g.at(i, j))
}

///|
/// 【N78-7】轉置扭曲之封閉式：2×2 方框和，零乘法。
pub fn cf_twist_t(g : Mat[Q]) -> Mat[Q] {
  let n = g.mrows
  Mat::build(n, n, (p, q) => {
    let mut acc = Q::zero()
    for i in p..<(p + 2) {
      if i < n {
        for j in q..<(q + 2) {
          if j < n {
            acc = acc.add(g.at(i, j))
          }
        }
      }
    }
    acc
  })
}

// ---------------------------------------------------------------------------
//  七個「看起來很合理、但是錯的」對照式
//
//  每一條都是真的會有人寫出來的錯：忘記對偶、忘記 Hodge 符號、
//  張量指標順序寫反、取錯主子陣、轉置放錯邊。
//  兩側對照之價值在於它們**不是隨機擾動** —— 隨機擾動只測得出比較器，
//  測不出公式。
// ---------------------------------------------------------------------------

///|
/// 錯式 1：G_W ⊗ G（忘了 Hom(W,−) 裡的 W 是對偶地出現）。
pub fn cfw_hom(gw : Mat[Q], g : Mat[Q]) -> Mat[Q] {
  mkron(gw, g)
}

///|
/// 錯式 2：det(G)·G⁻¹（忘了 Hodge 的符號與指標反轉）。
pub fn cfw_codim1(g : Mat[Q], c : Cost) -> Mat[Q] {
  let n = g.mrows
  let dt = mdet(g)
  let gi = match qinv_gauss(g, c) {
    Some(h) => h
    None => Mat::ident(n)
  }
  Mat::build(n, n, (p, q) => dt.mul(gi.at(p, q)))
}

///|
/// 錯式 4：(G⁻¹)ᵀ（只作用一次對偶）。
pub fn cfw_bidual(g : Mat[Q], c : Cost) -> Mat[Q] {
  match qinv_gauss(g, c) {
    Some(h) => h.transpose()
    None => Mat::ident(g.mrows)
  }
}

///|
/// 錯式 5：G ⊗ I₂（張量指標順序寫反）。
pub fn cfw_double(g : Mat[Q]) -> Mat[Q] {
  mkron(g, Mat::ident(2))
}

///|
/// 錯式 6：**後** ⌈n/2⌉ 階主子陣（取錯一端）。
pub fn cfw_half(g : Mat[Q]) -> Mat[Q] {
  let n = g.mrows
  let k = (n + 1) / 2
  Mat::build(k, k, (i, j) => g.at(n - k + i, n - k + j))
}

///|
/// 錯式 7：MGMᵀ（轉置放錯邊）。
pub fn cfw_twist_t(g : Mat[Q]) -> Mat[Q] {
  let m = comb_unitri(g.mrows).transpose()
  m.times(g).times(m.transpose())
}

///|
/// # N-51 構造子註冊表（7 個）與 Gram 函子性
///
/// ## 定義（構造子）
///
/// 一個構造子是有限維內積空間範疇上的自函子 C，其在座標像上的作用
/// 完全由 Gram 決定。本庫的 `SpaceExpr` 有 7 個非葉構造子，逐一對應：
///
/// ```text
///   C        記號   G(C S)                         dim(C S)
///   ------   ----   ----------------------------   -----------
///   張量     ⊗      G ⊗ G_W     （Kronecker 積）    n·w
///   直和     ⊕      G ⊕ G_W     （分塊對角）        n+w
///   對偶     *      (G⁻¹)ᵀ      （Riesz 誘導）       n
///   外冪     Λᵏ     Cₖ(G)       （第 k 複合矩陣）    C(n,k)
///   扭曲     T      MᵀG M       （M 可逆）           n
///   子空間   U      SᵀG S       （S 行滿秩，n×u）    u
///   Kron 和  ⊞      G⊗I + I⊗G_W                     n·w
/// ```
///
/// 定理 N51-1（封閉性 / 自函子性）：上列七式皆把對稱正定矩陣送到對稱
/// 正定矩陣，故 C 確實是「有限維 ℚ-內積空間」這個類上的自映射。
///
/// 證明：⊗ —— G, H ≻ 0 之特徵值皆正，G⊗H 之特徵值為 {λᵢμⱼ} 皆正，
/// 對稱性由 (G⊗H)ᵀ = Gᵀ⊗Hᵀ。⊕ —— 分塊對角之譜為兩譜之併。
/// * —— G ≻ 0 ⇒ G⁻¹ ≻ 0，轉置保持之。Λᵏ —— Cₖ(G) 之特徵值為 G 之
/// 特徵值的 k 元乘積 Π_{i∈S} λᵢ（Cauchy–Binet），皆正。
/// T、U —— x ≠ 0 ⇒ Mx ≠ 0（M 可逆）或 Sx ≠ 0（S 行滿秩），
/// 故 xᵀMᵀGMx = (Mx)ᵀG(Mx) > 0。⊞ —— 特徵值為 {λᵢ+μⱼ} 皆正。∎
///
/// 定理 N51-2（維數函子性）：上表右欄之維數公式對一切輸入成立，
/// 且與 `SpaceExpr::sdim` 之遞迴定義一致。
///
/// 推論（組合爆炸）：35 個葉子 × 7 個構造子 = 245 個相異空間，
/// 每一個都是合法的有限維內積空間，故 D 群 23 條演算法在其上全部有定義。
/// 新增一個葉子使格數加 7，新增一個構造子使格數加 35；兩表皆開放。

///|
/// 一筆構造子。
pub struct CombRec {
  cname : String
  csym : String
  /// 元數：1 = 一元，2 = 與固定夥伴 W 配對
  cari : Int
  /// 作用於表達式
  capply : (SpaceExpr) -> SpaceExpr
  /// 維數公式（給定輸入維數）
  cdim : (Int) -> Int
}

///|
/// 固定夥伴空間 W：維數 2，Gram [[2,1],[1,2]]（正定，非單位，
/// 故 ⊗／⊕／⊞ 不會退化成「只是把維數變大」）。
pub fn comb_partner() -> SpaceExpr {
  let d : ReadOnlyArray[ReadOnlyArray[Int]] = [[2, 1], [1, 2]]
  SLeaf("W₂", Mat::build(2, 2, (i, j) => Q::of_int(d[i][j])))
}

///|
/// n×n 么單上三角生成矩陣（det = 1，必可逆）。
pub fn comb_unitri(n : Int) -> Mat[Q] {
  Mat::build(n, n, (i, j) => {
    if i == j || j == i + 1 {
      Q::one()
    } else {
      Q::zero()
    }
  })
}

///|
/// n×k 行滿秩嵌入（取么單上三角之前 k 行）。
pub fn comb_embed(n : Int, k : Int) -> Mat[Q] {
  let m = comb_unitri(n)
  Mat::build(n, k, (i, j) => m.at(i, j))
}

///|
/// 【註冊表】7 個構造子。
pub fn comb7_registry() -> Array[CombRec] {
  let w = comb_partner()
  [
    {
      cname: "張量",
      csym: "⊗",
      cari: 2,
      capply: e => STensor(e, w),
      cdim: n => n * 2,
    },
    {
      cname: "直和",
      csym: "⊕",
      cari: 2,
      capply: e => SSum(e, w),
      cdim: n => n + 2,
    },
    {
      cname: "對偶",
      csym: "*",
      cari: 1,
      capply: e => SDual(e),
      cdim: n => n,
    },
    {
      cname: "外冪",
      csym: "Λ²",
      cari: 1,
      capply: e => SExt(e, 2),
      cdim: n => binom(n, 2),
    },
    {
      cname: "扭曲",
      csym: "T",
      cari: 1,
      capply: e => STwist(e, comb_unitri(e.sdim())),
      cdim: n => n,
    },
    {
      cname: "子空間",
      csym: "U",
      cari: 1,
      capply: e => SSub(e, comb_embed(e.sdim(), 2)),
      cdim: _ => 2,
    },
    {
      cname: "Kron 和",
      csym: "⊞",
      cari: 2,
      capply: e => SKSum(e, w),
      cdim: n => n * 2,
    },
  ]
}

///|
/// 構造子作用後之座標空間（即 ⟦C(S)⟧）。
pub fn comb7_space(r : SpaceRec, c : CombRec) -> IPSpace[Array[Q], Q] {
  (c.capply)(r.leaf()).sspace()
}

///|
/// 構造子作用後之 Gram。
pub fn comb7_gram(r : SpaceRec, c : CombRec) -> Mat[Q] {
  (c.capply)(r.leaf()).sgram()
}

///|
/// 格鍵：空間 ⊕ 構造子，用於決定取樣種子（與枚舉順序無關）。
pub fn comb7_key(r : SpaceRec, c : CombRec) -> String {
  c.csym + "[" + r.sname + "]"
}

///|
/// 定理 N51-1 之逐格檢查：C(S) 之 Gram 對稱正定。
pub fn comb7_spd(r : SpaceRec, c : CombRec) -> Bool {
  let g = comb7_gram(r, c)
  if g.mrows != g.mcols || g.mrows == 0 {
    return false
  }
  for i in 0..<g.mrows {
    for j in 0..<g.mcols {
      if !Q::eq(g.at(i, j), g.at(j, i)) {
        return false
      }
    }
  }
  spd_bareiss(g) // 【N-76】Θ(n³) 整數 Sylvester，語意與 is_positive_definite 相同
}

///|
/// 定理 N51-2 之逐格檢查：維數公式 ≡ sdim 遞迴 ≡ 實際 Gram 階數。
pub fn comb7_dimok(r : SpaceRec, c : CombRec) -> Bool {
  let e = (c.capply)(r.leaf())
  let predicted = (c.cdim)(r.sdim)
  e.sdim() == predicted && comb7_gram(r, c).mrows == predicted
}

///|
/// 全部 35 × 7 格之維數表（報表用）。
pub fn comb7_dim_table() -> Array[(String, Int)] {
  let out : Array[(String, Int)] = []
  for r in space_registry() {
    for c in comb7_registry() {
      out.push((comb7_key(r, c), (c.cdim)(r.sdim)))
    }
  }
  out
}

///|
/// 構造後維數之 (最小, 最大, 總和)。
pub fn comb7_dim_stats() -> (Int, Int, Int) {
  let mut lo = 999999
  let mut hi = 0
  let mut tot = 0
  for p in comb7_dim_table() {
    if p.1 < lo {
      lo = p.1
    }
    if p.1 > hi {
      hi = p.1
    }
    tot = tot + p.1
  }
  (lo, hi, tot)
}

///|
/// 構造子表之指紋：格數、總維數、鍵與維數之雜湊。
pub fn comb7_digest() -> String {
  let t = comb7_dim_table()
  let mut h : UInt64 = 0xcbf2_9ce4_8422_2325UL
  let mut tot = 0
  for p in t {
    tot = tot + p.1
    h = (h ^ str_hash64(p.0 + "#" + p.1.to_string())) * 0x1000_0000_01b3UL
  }
  t.length().to_string() +
  ":" +
  tot.to_string() +
  ":" +
  (h % 1000000007UL).to_string()
}

///|
/// N-50 之義務：空間註冊表與座標化重編。
///
/// 要驗三件事：
///   (1) 註冊表確實有 35 筆，且每一筆的 Gram 是**從真實建構的空間取出**的
///   (2) 重編保內積 —— 原空間與座標像 ⟦S⟧ 的 Gram 逐元相同
///   (3) 每個 Gram 對稱正定 —— 否則 ⟦S⟧ 不是內積空間，後面的普查就是空的
pub fn ob_n50() -> Check {
  let mut ok = true
  let xs = space_registry()

  // ── 定義（註冊表規模）────────────────────────────────────
  if xs.length() != 35 {
    ok = false
  }

  // ── 命題 N50-1（重編保內積）＋ 正定性 ───────────────────
  let mut faithful = 0
  let mut spd = 0
  let mut dimok = 0
  for r in xs {
    if sreg_refaithful(r) {
      faithful = faithful + 1
    }
    if sreg_spd(r) {
      spd = spd + 1
    }
    if r.sg.mrows == r.sdim && r.sg.mcols == r.sdim && r.sdim >= 2 {
      dimok = dimok + 1
    }
  }
  if faithful != 35 || spd != 35 || dimok != 35 {
    ok = false
  }

  // ── 名稱必須互異（否則格鍵會碰撞，普查的指紋就沒有意義）──
  let mut dup = 0
  for i in 0..<xs.length() {
    for j in (i + 1)..<xs.length() {
      if xs[i].sname == xs[j].sname {
        dup = dup + 1
      }
    }
  }
  if dup != 0 {
    ok = false
  }

  // ── 族別覆蓋：9 族，且筆數加總為 35 ─────────────────────
  let fams = space_registry_families()
  let mut famsum = 0
  for f in fams {
    famsum = famsum + f.1
  }
  if fams.length() != 9 || famsum != 35 {
    ok = false
  }

  // ── 維數統計與指紋（釘死）────────────────────────────────
  let (lo, hi, tot) = space_registry_dims()
  if lo != 2 || hi != 8 || tot != 134 {
    ok = false
  }
  let dg = space_registry_digest()
  if dg != "35:134:252394910" {
    ok = false
  }

  // ── 命題 N50-2（MᵀM 正定）之直接斷言 ─────────────────────
  let tw = sreg_twist3()
  if !is_positive_definite(tw) {
    ok = false
  }
  if !tw.equals(tw.transpose()) {
    ok = false
  }
  // 扭曲必須真的扭曲：Gram ≠ I，否則 T 構造子退化成恆等
  if tw.equals(Mat::ident(3)) {
    ok = false
  }
  mk_check(
    "N-50 空間註冊表與座標化重編",
    ok,
    xs.length() * 3 + fams.length() + 6,
    "本庫的空間以字典傳遞法實作，載體隨族而異（Array[Q]、Mat[Q]、Poly[Q]、MPoly[Q]、Array[Quat[Q]]、Mat[Cpx[Q]]），載體不同就不能放進同一個陣列，也就不能被同一組演算法逐一掃過。本條把每個空間重編為它的座標像：取基底算 Gram G_ij = ⟨bᵢ,bⱼ⟩，⟦S⟧ = (ℚⁿ, ⟨x,y⟩_G)。座標映射是保內積的線性同構，故任何只透過 dim／basis／coord／expand／inner 存取空間的演算法在 S 與 ⟦S⟧ 上輸出相同 —— D 群 23 條全部屬此類。註冊表 " +
    xs.length().to_string() +
    " 筆、" +
    fams.length().to_string() +
    " 族（座標 4、函數 2、矩陣 10、多項式 6、四元數 2、複結構 1、外代數 4、子空間 3、其他 3），維數 " +
    lo.to_string() +
    " 至 " +
    hi.to_string() +
    "、總計 " +
    tot.to_string() +
    "。每一筆的 Gram 都由實際建構的空間以 gram_of_space 取出，不是打字打進來的：義務重建全部 35 個空間並逐元比對，保真 " +
    faithful.to_string() +
    "/35、對稱正定 " +
    spd.to_string() +
    "/35、名稱互異（碰撞 " +
    dup.to_string() +
    " 組，碰撞會使普查格鍵與指紋失效）。指紋 " +
    dg +
    " 釘死，一進一出改變前兩欄、單一 Gram 元素改動改變第三欄。附帶修正：retwist 直接以其引數為 Gram，故引數必須正定 —— 扭曲葉子改用 A = MᵀM（M 么單三角，det = 1），命題 N50-2 於義務中直接斷言 A 正定、對稱、且 ≠ I。",
  )
}

///|
/// N-51 之義務：7 個構造子與 Gram 函子性。
///
/// 要驗的是**封閉性**：構造子把內積空間送到內積空間。這不是形式問題 ——
/// 若某個構造子吐出非正定的 Gram，⟦C(S)⟧ 就不是內積空間，D 群在其上的
/// 每一格都沒有意義。
pub fn ob_n51() -> Check {
  let mut ok = true
  let spaces = space_registry()
  let combs = comb7_registry()
  if combs.length() != 7 {
    ok = false
  }

  // ── 定理 N51-1（自函子性：Gram 保持對稱正定）────────────
  // ── 定理 N51-2（維數公式 ≡ sdim 遞迴 ≡ Gram 階數）───────
  let mut cells = 0
  let mut spd = 0
  let mut dimok = 0
  let mut dmax = 0
  let mut dmin = 999999
  for r in spaces {
    for c in combs {
      cells = cells + 1
      if comb7_spd(r, c) {
        spd = spd + 1
      }
      if comb7_dimok(r, c) {
        dimok = dimok + 1
      }
      let d = (c.cdim)(r.sdim)
      if d > dmax {
        dmax = d
      }
      if d < dmin {
        dmin = d
      }
    }
  }
  if cells != 245 || spd != 245 || dimok != 245 {
    ok = false
  }
  if dmin != 1 || dmax != 28 {
    ok = false
  }

  // ── 記號互異（格鍵唯一性）────────────────────────────────
  let mut dup = 0
  for i in 0..<combs.length() {
    for j in (i + 1)..<combs.length() {
      if combs[i].csym == combs[j].csym {
        dup = dup + 1
      }
    }
  }
  if dup != 0 {
    ok = false
  }

  // ── 構造子必須真的改變空間（否則 7 個裡有冗員）──────────
  // 逐構造子數「它在 35 個空間中改變了幾個」。移動數 0 即冗員。
  // 實測 (⊗,⊕,*,Λ²,T,U,⊞) = (35,35,17,30,35,35,35)：* 在 18 個
  // Gram = I 的空間上給回原空間（有限維、標準正交基 ⇒ V* 典範同構於 V），
  // Λ² 在 5 個「維數 3 且 Gram = I」的空間上同理 —— 兩者皆為定理，
  // 不是冗員；義務記錄實測向量並要求每個構造子至少移動 1 個空間。
  let mv = comb7_moved()
  let want = [35, 35, 17, 30, 35, 35, 35]
  if mv.length() != 7 {
    ok = false
  }
  let mut moved = 0
  for t in 0..<mv.length() {
    if mv[t].1 != want[t] {
      ok = false
    }
    if mv[t].1 >= 1 {
      moved = moved + 1
    }
  }
  if moved != 7 {
    ok = false
  }

  // ── 指紋（釘死）─────────────────────────────────────────
  let dg = comb7_digest()
  if dg != "245:1306:695201586" {
    ok = false
  }
  let (cl, ch, ct) = comb7_dim_stats()
  if cl != 1 || ch != 28 || ct != 1306 {
    ok = false
  }
  mk_check(
    "N-51 七個構造子與 Gram 函子性",
    ok,
    cells * 2 + combs.length() * 2 + 4,
    "SpaceExpr 的 7 個非葉構造子逐一給出 Gram 上的作用：⊗ 為 Kronecker 積 G⊗G_W、⊕ 為分塊對角、* 為 (G⁻¹)ᵀ、Λ² 為第二複合矩陣 C₂(G)、T 為 MᵀGM、U 為 SᵀGS、⊞ 為 G⊗I + I⊗G_W。定理 N51-1 斷言七式皆把對稱正定送到對稱正定（⊗ 與 ⊞ 由特徵值 λᵢμⱼ、λᵢ+μⱼ 皆正；Λᵏ 由 Cauchy–Binet 得 C_k(G) 之特徵值為 λ 的 k 元乘積；T、U 由 M 可逆、S 行滿秩得 (Mx)ᵀG(Mx) > 0），故它們確實是有限維 ℚ-內積空間這個類上的自函子 —— 這正是「構造可以無限疊下去」的根據。義務對 35 × 7 = " +
    cells.to_string() +
    " 格逐一實算：對稱正定 " +
    spd.to_string() +
    "/245，維數公式與 sdim 遞迴與實際 Gram 階數三者相符 " +
    dimok.to_string() +
    "/245，構造後維數由 " +
    cl.to_string() +
    "（Λ² 作用於 2 維空間，C(2,2) = 1）至 " +
    ch.to_string() +
    "（Λ² 作用於 ℍ²，C(8,2) = 28），總計 " +
    ct.to_string() +
    "。另驗七個構造子無冗員：逐構造子數出它在 35 個空間中改變了幾個（維數或 Gram 至少一者不同），實測 (⊗,⊕,*,Λ²,T,U,⊞) = (35,35,17,30,35,35,35)，全部 " +
    moved.to_string() +
    "/7 至少移動一個空間。* 只移動 17 個不是缺陷而是定理：在 Gram = I 的 18 個空間上，有限維加標準正交基使 V* 典範同構於 V，(G⁻¹)ᵀ = I；Λ² 固定的 5 個同理（維數 3 且 Gram = I 時 C₂(I) = I）。記號互異（碰撞 " +
    dup.to_string() +
    " 組）。指紋 " +
    dg +
    "。組合爆炸在此是可量的：新增一個葉子使格數加 7，新增一個構造子使格數加 35，兩表皆為開放註冊表。",
  )
}

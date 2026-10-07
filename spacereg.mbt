///|
/// # N-50 空間註冊表與座標化重編（中端第一層）
///
/// ## 定義（座標化重編 coordinate re-compilation）
///
/// 本庫的空間以字典傳遞法實作：`IPSpace[V, F]` 之載體 `V` 隨族而異
/// （`Array[Q]`、`Mat[Q]`、`Poly[Q]`、`MPoly[Q]`、`Array[Quat[Q]]`、
/// `Mat[Cpx[Q]]` …）。載體不同，空間就不能放進同一個陣列，也就不能
/// 被同一組演算法逐一掃過。
///
/// 重編把每個空間映到它的**座標像**：取其基底 b₁,…,b_n，令
///
/// ```text
///     G_{ij} = ⟨bᵢ, bⱼ⟩  ∈ Mat[Q]        （Gram 矩陣）
///     ⟦S⟧   = (ℚⁿ, ⟨x,y⟩_G = yᵀ G x)     （座標空間）
/// ```
///
/// 命題 N50-1（重編保內積）：座標映射 C : V → ℚⁿ 是線性同構，且
/// ⟨x, y⟩_V = ⟨C x, C y⟩_G。故 ⟦S⟧ ≅ S 作為內積空間。
///
/// 推論：任何只透過 `vs.dim`／`vs.basis`／`vs.coord`／`vs.expand`／`inner`
/// 存取空間的演算法，在 S 與 ⟦S⟧ 上輸出相同（至座標同構）。D 群 23 條
/// 全部屬此類，故可一次掃過全部 35 個空間。
///
/// ## 註冊表
///
/// 35 個空間，橫跨 7 族。每一筆的 Gram **由實際建構的空間取出**
/// （`gram_of_space`），不是打字打進來的 —— `ob_n50` 會重建每個空間
/// 並逐元比對。

///|
/// 一筆註冊空間：名稱、族、維數、Gram。
pub struct SpaceRec {
  sname : String
  fam : String
  sdim : Int
  sg : Mat[Q]
}

///|
/// 由註冊筆造出可直接使用的座標內積空間 ⟦S⟧。
pub fn SpaceRec::space(self : SpaceRec) -> IPSpace[Array[Q], Q] {
  coord_ipspace(self.sname, self.sdim, Some(self.sg))
}

///|
/// 由註冊筆造出結構律引擎用的葉子。
pub fn SpaceRec::leaf(self : SpaceRec) -> SpaceExpr {
  SLeaf(self.sname, self.sg)
}

///|
/// 子空間／列空間用的固定秩 2 矩陣 A（4×3，c₃ = c₁ + c₂）。
pub fn sreg_mat_a() -> Mat[Q] {
  let d : ReadOnlyArray[ReadOnlyArray[Int]] = [
    [1, 0, 1],
    [0, 1, 1],
    [1, 1, 2],
    [2, 1, 3],
  ]
  Mat::build(4, 3, (i, j) => Q::of_int(d[i][j]))
}

///|
/// 零空間用的固定 2×5 秩 2 矩陣 B（ker 維數 3）。
pub fn sreg_mat_b() -> Mat[Q] {
  let d : ReadOnlyArray[ReadOnlyArray[Int]] = [[1, 0, 1, 2, 0], [0, 1, 1, 0, 2]]
  Mat::build(2, 5, (i, j) => Q::of_int(d[i][j]))
}

///|
/// 扭曲用的生成矩陣 M（么單三角，det = 1，必可逆）。
pub fn sreg_twist_gen() -> Mat[Q] {
  let d : ReadOnlyArray[ReadOnlyArray[Int]] = [[1, 1, 0], [0, 1, 1], [0, 0, 1]]
  Mat::build(3, 3, (i, j) => Q::of_int(d[i][j]))
}

///|
/// 扭曲用的 Gram A = MᵀM。
///
/// 命題 N50-2：M 可逆 ⇒ MᵀM 對稱正定。證明：對稱顯然；
/// 對 x ≠ 0，xᵀMᵀMx = ‖Mx‖² > 0，因 M 可逆故 Mx ≠ 0。∎
/// `retwist` 直接以其引數為 Gram，故引數必須正定 —— 本函式保證之。
pub fn sreg_twist3() -> Mat[Q] {
  let m = sreg_twist_gen()
  m.transpose().times(m)
}

///|
/// 【註冊表】35 個有限維內積空間，全部重編為 ℚ 上的 Gram。
///
/// 族：座標／函數（6）、矩陣（10）、多項式（6）、四元數與複結構（3）、
/// 外代數（4）、子空間（3）、其他（3）。
pub fn space_registry() -> Array[SpaceRec] {
  let xs : Array[SpaceRec] = []
  fn add(nm : String, fam : String, g : Mat[Q]) -> Unit {
    xs.push({ sname: nm, fam, sdim: g.mrows, sg: g, })
  }

  // ── 族 1：座標空間與有限集上的函數空間（6）────────────────
  let e2 : IPSpace[Array[Q], Q] = euclidean_space(2)
  add("E²", "座標", gram_of_space(e2))
  let e3 : IPSpace[Array[Q], Q] = euclidean_space(3)
  add("E³", "座標", gram_of_space(e3))
  let e4 : IPSpace[Array[Q], Q] = euclidean_space(4)
  add("E⁴", "座標", gram_of_space(e4))
  let e5 : IPSpace[Array[Q], Q] = euclidean_space(5)
  add("E⁵", "座標", gram_of_space(e5))
  let f3 : IPSpace[Array[Q], Q] = function_space_unit(["a", "b", "c"])
  add("ℚ^{a,b,c}", "函數", gram_of_space(f3))
  let fw : IPSpace[Array[Q], Q] = function_space(["p", "q", "r", "s"], [
    Q::of_int(1),
    Q::of_int(2),
    Q::of_int(3),
    Q::of_int(1),
  ])
  add("ℚ^{p,q,r,s}_w", "函數", gram_of_space(fw))

  // ── 族 2：矩陣空間（10）──────────────────────────────────
  let m22 : IPSpace[Mat[Q], Q] = matrix_space(2, 2)
  add("M₂ₓ₂", "矩陣", gram_of_space(m22))
  let m23 : IPSpace[Mat[Q], Q] = matrix_space(2, 3)
  add("M₂ₓ₃", "矩陣", gram_of_space(m23))
  let sy2 : IPSpace[Mat[Q], Q] = sym_matrix_space(2)
  add("Sym₂", "矩陣", gram_of_space(sy2))
  let sy3 : IPSpace[Mat[Q], Q] = sym_matrix_space(3)
  add("Sym₃", "矩陣", gram_of_space(sy3))
  let sk3 : IPSpace[Mat[Q], Q] = skew_matrix_space(3)
  add("Skew₃", "矩陣", gram_of_space(sk3))
  let sk4 : IPSpace[Mat[Q], Q] = skew_matrix_space(4)
  add("Skew₄", "矩陣", gram_of_space(sk4))
  let dg3 : IPSpace[Mat[Q], Q] = diag_matrix_space(3)
  add("Diag₃", "矩陣", gram_of_space(dg3))
  let dg5 : IPSpace[Mat[Q], Q] = diag_matrix_space(5)
  add("Diag₅", "矩陣", gram_of_space(dg5))
  let tl2 : IPSpace[Mat[Q], Q] = traceless_space(2)
  add("𝔰𝔩₂", "矩陣", gram_of_space(tl2))
  let hm2 : IPSpace[Mat[Cpx[Q]], Q] = herm_matrix_space(2)
  add("Herm₂", "矩陣", gram_of_space(hm2))

  // ── 族 3：多項式空間（6）────────────────────────────────
  let p2 : IPSpace[Poly[Q], Q] = poly_space_l2(2)
  add("P≤2 L²", "多項式", gram_of_space(p2))
  let p3 : IPSpace[Poly[Q], Q] = poly_space_l2(3)
  add("P≤3 L²", "多項式", gram_of_space(p3))
  let h2 : IPSpace[Poly[Q], Q] = poly_space_hilbert(2)
  add("P≤2 Hilb", "多項式", gram_of_space(h2))
  let h3 : IPSpace[Poly[Q], Q] = poly_space_hilbert(3)
  add("P≤3 Hilb", "多項式", gram_of_space(h3))
  let mp1 : IPSpace[MPoly[Q], Q] = mpoly_space(2, 1, false)
  add("ℚ[x,y]≤1", "多項式", gram_of_space(mp1))
  let mp2 : IPSpace[MPoly[Q], Q] = mpoly_space(2, 2, true)
  add("ℚ[x,y]≤2 Bomb", "多項式", gram_of_space(mp2))

  // ── 族 4：四元數與複結構（3）────────────────────────────
  let q1 : IPSpace[Array[Quat[Q]], Q] = quaternion_space(1)
  add("ℍ¹", "四元數", gram_of_space(q1))
  let q2 : IPSpace[Array[Quat[Q]], Q] = quaternion_space(2)
  add("ℍ²", "四元數", gram_of_space(q2))
  let u2 : IPSpace[Array[Cpx[Q]], Cpx[Q]] = unitary_space(2)
  add("ℝ(ℂ²)", "複結構", gram_of_space(realify(u2)))

  // ── 族 5：外代數（4）────────────────────────────────────
  let x32 : IPSpace[Array[Q], Q] = exterior_power_space(3, 2)
  add("Λ²ℚ³", "外代數", gram_of_space(x32))
  let x42 : IPSpace[Array[Q], Q] = exterior_power_space(4, 2)
  add("Λ²ℚ⁴", "外代數", gram_of_space(x42))
  let x43 : IPSpace[Array[Q], Q] = exterior_power_space(4, 3)
  add("Λ³ℚ⁴", "外代數", gram_of_space(x43))
  let xa2 : IPSpace[Array[Q], Q] = exterior_algebra_space(2)
  add("Λ•ℚ²", "外代數", gram_of_space(xa2))

  // ── 族 6：子空間（3）────────────────────────────────────
  let a = sreg_mat_a()
  let cs : IPSpace[Array[Q], Q] = column_space(a)
  add("col(A)", "子空間", gram_of_space(cs))
  let rs : IPSpace[Array[Q], Q] = row_space(a)
  add("row(A)", "子空間", gram_of_space(rs))
  let ks : IPSpace[Array[Q], Q] = kernel_space(sreg_mat_b())
  add("ker(B)", "子空間", gram_of_space(ks))

  // ── 族 7：其他（3）──────────────────────────────────────
  let tw : IPSpace[Array[Q], Q] = retwist(e3, sreg_twist3())
  add("T[E³]", "其他", gram_of_space(tw))
  let m32 : IPSpace[Mat[Q], Q] = matrix_space(3, 2)
  add("M₃ₓ₂", "其他", gram_of_space(m32))
  let f2 : IPSpace[Array[Q], Q] = function_space(["u", "v"], [
    Q::of_int(2),
    Q::of_int(3),
  ])
  add("ℚ^{u,v}_w", "其他", gram_of_space(f2))
  xs
}

///|
/// 註冊表之指紋：筆數、總維數、Gram 全元素之雜湊。
/// 一進一出會改變第一與第二欄；單一元素改動會改變第三欄。
pub fn space_registry_digest() -> String {
  let xs = space_registry()
  let mut dimsum = 0
  let mut h : UInt64 = 0xcbf2_9ce4_8422_2325UL
  for r in xs {
    dimsum = dimsum + r.sdim
    for i in 0..<r.sg.mrows {
      for j in 0..<r.sg.mcols {
        let v = r.sg.at(i, j)
        h = (h ^ str_hash64(Q::text(v))) * 0x1000_0000_01b3UL
      }
    }
  }
  xs.length().to_string() +
  ":" +
  dimsum.to_string() +
  ":" +
  (h % 1000000007UL).to_string()
}

///|
/// 維數分布（報表用）：最小、最大、總和。
pub fn space_registry_dims() -> (Int, Int, Int) {
  let xs = space_registry()
  let mut lo = 9999
  let mut hi = 0
  let mut tot = 0
  for r in xs {
    if r.sdim < lo {
      lo = r.sdim
    }
    if r.sdim > hi {
      hi = r.sdim
    }
    tot = tot + r.sdim
  }
  (lo, hi, tot)
}

///|
/// 族別統計：回傳 (族名, 筆數) 之陣列，順序同註冊表首次出現順序。
pub fn space_registry_families() -> Array[(String, Int)] {
  let out : Array[(String, Int)] = []
  for r in space_registry() {
    let mut found = false
    for k in 0..<out.length() {
      if out[k].0 == r.fam {
        out[k] = (r.fam, out[k].1 + 1)
        found = true
        break
      }
    }
    if !found {
      out.push((r.fam, 1))
    }
  }
  out
}

///|
/// 重編保真度：對同一個空間，比對「原空間之 Gram」與「⟦S⟧ 之 Gram」。
/// 兩者相等即命題 N50-1 在該筆上成立。
pub fn sreg_refaithful(r : SpaceRec) -> Bool {
  let sp = r.space()
  if sp.vs.dim != r.sdim {
    return false
  }
  let g2 = gram_of_space(sp)
  if g2.mrows != r.sg.mrows || g2.mcols != r.sg.mcols {
    return false
  }
  for i in 0..<g2.mrows {
    for j in 0..<g2.mcols {
      if !Q::eq(g2.at(i, j), r.sg.at(i, j)) {
        return false
      }
    }
  }
  true
}

///|
/// Gram 必須對稱正定（有限維實內積空間之充要條件）。
pub fn sreg_spd(r : SpaceRec) -> Bool {
  let g = r.sg
  if g.mrows != g.mcols || g.mrows != r.sdim {
    return false
  }
  for i in 0..<g.mrows {
    for j in 0..<g.mcols {
      if !Q::eq(g.at(i, j), g.at(j, i)) {
        return false
      }
    }
  }
  is_positive_definite(g)
}

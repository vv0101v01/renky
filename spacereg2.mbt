///|
/// # 第七輪：註冊表擴充（35 → 45 空間，7 → 14 構造子）
///
/// ## 為什麼是「附加」而不是「改掉」
///
/// N-50／N-51／N-52 的義務裡釘死了三個指紋：`35:134:252394910`、
/// `245:1306:695201586`、`5635:5635:386251483`。直接把 `space_registry()`
/// 改成 45 筆會讓三條義務同時失效，而且失效的方式沒有資訊量 —— 只是數字變了。
///
/// 所以擴充採**前綴保持**：`space_registry_x()` 的前 35 筆與
/// `space_registry()` 逐筆相同，後 10 筆是新的；`comb14_registry()` 的前 7 個
/// 與 `comb7_registry()` 逐個相同。於是舊指紋繼續當迴歸錨點，而且多了一條
/// 可執行的檢查：**擴充表限制回原表時必須重現舊指紋**。

///|
/// 第七輪新增之 10 個空間（族別刻意分散）。
pub fn space_registry_new() -> Array[SpaceRec] {
  let xs : Array[SpaceRec] = []
  fn add(nm : String, fam : String, g : Mat[Q]) -> Unit {
    xs.push({ sname: nm, fam, sdim: g.mrows, sg: g, })
  }

  // 矩陣族（4）
  let sy4 : IPSpace[Mat[Q], Q] = sym_matrix_space(4)
  add("Sym₄", "矩陣", gram_of_space(sy4))
  let sk5 : IPSpace[Mat[Q], Q] = skew_matrix_space(5)
  add("Skew₅", "矩陣", gram_of_space(sk5))
  let tl3 : IPSpace[Mat[Q], Q] = traceless_space(3)
  add("𝔰𝔩₃", "矩陣", gram_of_space(tl3))
  let hm3 : IPSpace[Mat[Cpx[Q]], Q] = herm_matrix_space(3)
  add("Herm₃", "矩陣", gram_of_space(hm3))

  // 多項式族（3）
  let p4 : IPSpace[Poly[Q], Q] = poly_space_l2(4)
  add("P≤4 L²", "多項式", gram_of_space(p4))
  let h4 : IPSpace[Poly[Q], Q] = poly_space_hilbert(4)
  add("P≤4 Hilb", "多項式", gram_of_space(h4))
  let mp3 : IPSpace[MPoly[Q], Q] = mpoly_space(3, 1, false)
  add("ℚ[x,y,z]≤1", "多項式", gram_of_space(mp3))

  // 四元數族（1）
  let q3 : IPSpace[Array[Quat[Q]], Q] = quaternion_space(3)
  add("ℍ³", "四元數", gram_of_space(q3))

  // 外代數族（1）
  let x52 : IPSpace[Array[Q], Q] = exterior_power_space(5, 2)
  add("Λ²ℚ⁵", "外代數", gram_of_space(x52))

  // 複結構族（1）
  let u3 : IPSpace[Array[Cpx[Q]], Cpx[Q]] = unitary_space(3)
  add("ℝ(ℂ³)", "複結構", gram_of_space(realify(u3)))
  xs
}

///|
/// 擴充後之空間註冊表：前 35 筆與 `space_registry()` 逐筆相同。
pub fn space_registry_x() -> Array[SpaceRec] {
  let xs : Array[SpaceRec] = []
  for r in space_registry() {
    xs.push(r)
  }
  for r in space_registry_new() {
    xs.push(r)
  }
  xs
}

///|
/// 對稱平方之選擇矩陣 S : Sym²(ℚⁿ) ↪ ℚⁿ ⊗ ℚⁿ。
///
/// 行依序為 eᵢ⊗eᵢ（i = 0…n−1）與 eᵢ⊗eⱼ + eⱼ⊗eᵢ（i < j），
/// 共 n(n+1)/2 行，皆線性獨立，故 SᵀGS 在 G 正定時仍正定。
pub fn comb_sym_sel(n : Int) -> Mat[Q] {
  let cols : Array[Array[Q]] = []
  for i in 0..<n {
    let v : Array[Q] = Array::makei(n * n, _ => Q::zero())
    v[i * n + i] = Q::one()
    cols.push(v)
  }
  for i in 0..<n {
    for j in (i + 1)..<n {
      let v : Array[Q] = Array::makei(n * n, _ => Q::zero())
      v[i * n + j] = Q::one()
      v[j * n + i] = Q::one()
      cols.push(v)
    }
  }
  Mat::build(n * n, cols.length(), (r, c) => cols[c][r])
}

///|
/// 取前 ⌈n/2⌉ 個座標之嵌入矩陣（n × ⌈n/2⌉）。
pub fn comb_half_sel(n : Int) -> Mat[Q] {
  let k = (n + 1) / 2
  Mat::build(n, k, (i, j) => if i == j { Q::one() } else { Q::zero() })
}

///|
/// 第七輪新增之 7 個構造子（全部仍是建構子：由空間造空間，且為函子）。
pub fn comb7_new() -> Array[CombRec] {
  [
    // C8 Hom(W₂, −) ≅ W₂* ⊗ −
    {
      cname: "同態",
      csym: "H",
      cari: 2,
      capply: e => STensor(SDual(comb_partner()), e),
      cdim: n => 2 * n,
    },
    // C9 餘維一外冪 Λⁿ⁻¹（維數恆為 n，與 Λ² 不同）
    {
      cname: "餘維一外冪",
      csym: "Λⁿ⁻¹",
      cari: 1,
      capply: e => SExt(e, e.sdim() - 1),
      cdim: n => binom(n, n - 1),
    },
    // C10 對稱平方 S²
    {
      cname: "對稱平方",
      csym: "S²",
      cari: 1,
      capply: e => SSub(STensor(e, e), comb_sym_sel(e.sdim())),
      cdim: n => n * (n + 1) / 2,
    },
    // C11 雙對偶（Gram 應回到原樣 —— 這是 A1 的函子版）
    {
      cname: "雙對偶",
      csym: "**",
      cari: 1,
      capply: e => SDual(SDual(e)),
      cdim: n => n,
    },
    // C12 倍化 V ⊕ V
    {
      cname: "倍化",
      csym: "D",
      cari: 1,
      capply: e => SSum(e, e),
      cdim: n => 2 * n,
    },
    // C13 半子空間（取前 ⌈n/2⌉ 個座標）
    {
      cname: "半子空間",
      csym: "U½",
      cari: 1,
      capply: e => SSub(e, comb_half_sel(e.sdim())),
      cdim: n => (n + 1) / 2,
    },
    // C14 轉置扭曲（與 T 用的是互為轉置的兩個單位三角陣）
    {
      cname: "轉置扭曲",
      csym: "Tᵀ",
      cari: 1,
      capply: e => STwist(e, comb_unitri(e.sdim()).transpose()),
      cdim: n => n,
    },
  ]
}

///|
/// 擴充後之構造子表：前 7 個與 `comb7_registry()` 逐個相同。
pub fn comb14_registry() -> Array[CombRec] {
  let xs : Array[CombRec] = []
  for c in comb7_registry() {
    xs.push(c)
  }
  for c in comb7_new() {
    xs.push(c)
  }
  xs
}

///|
/// 擴充表之統計：(空間數, 維數下界, 維數上界, 維數總和, 指紋)。
pub fn sregx_stats() -> (Int, Int, Int, Int, String) {
  let xs = space_registry_x()
  let mut lo = 1000000
  let mut hi = 0
  let mut tot = 0
  let mut h = 0UL
  for r in xs {
    if r.sdim < lo {
      lo = r.sdim
    }
    if r.sdim > hi {
      hi = r.sdim
    }
    tot = tot + r.sdim
    h = h ^ str_hash64(r.sname + "#" + r.sg.text())
  }
  let dg = xs.length().to_string() +
    ":" +
    tot.to_string() +
    ":" +
    (h % 1000000007UL).to_string()
  (xs.length(), lo, hi, tot, dg)
}

///|
/// 前綴保持之檢查：擴充表之前 35 筆必須與原表逐筆相同（名稱與 Gram）。
pub fn sregx_prefix_ok() -> Bool {
  let base = space_registry()
  let ext = space_registry_x()
  if ext.length() != base.length() + 10 {
    return false
  }
  for i in 0..<base.length() {
    if ext[i].sname != base[i].sname {
      return false
    }
    if !ext[i].sg.equals(base[i].sg) {
      return false
    }
  }
  true
}

///|
/// 構造子表之前綴保持檢查（比對符號與 14 個維數公式值）。
pub fn comb14_prefix_ok() -> Bool {
  let base = comb7_registry()
  let ext = comb14_registry()
  if ext.length() != 14 {
    return false
  }
  for i in 0..<base.length() {
    if ext[i].csym != base[i].csym {
      return false
    }
    for n in 1..<9 {
      if (ext[i].cdim)(n) != (base[i].cdim)(n) {
        return false
      }
    }
  }
  true
}

///|
/// 14 × 45 之維數表統計：(格數, 維數下界, 上界, 總和, SPD 格數, 維數公式相符數, 指紋)。
pub fn comb14_stats() -> (Int, Int, Int, Int, Int, Int, String) {
  let sps = space_registry_x()
  let cbs = comb14_registry()
  let mut lo = 1000000
  let mut hi = 0
  let mut tot = 0
  let mut spd = 0
  let mut dimok = 0
  let mut cells = 0
  let mut h = 0UL
  for s in sps {
    for c in cbs {
      let e = (c.capply)(s.leaf())
      let d = e.sdim()
      cells = cells + 1
      if d < lo {
        lo = d
      }
      if d > hi {
        hi = d
      }
      tot = tot + d
      if (c.cdim)(s.sdim) == d {
        dimok = dimok + 1
      }
      if spd_bareiss(e.sgram()) {
        // 【N-76】Θ(n³) 整數 Sylvester；N-76 之義務逐格對帳兩路一致
        spd = spd + 1
      }
      h = h ^ str_hash64(c.csym + "[" + s.sname + "]=" + d.to_string())
    }
  }
  let dg = cells.to_string() +
    ":" +
    tot.to_string() +
    ":" +
    (h % 1000000007UL).to_string()
  (cells, lo, hi, tot, spd, dimok, dg)
}

///|
/// # N-87 第十五輪新增之 21 個構造子
///
/// 本庫原有 14 個構造子（⊗ ⊕ * Λ² T U ⊞ ＋ H Λⁿ⁻¹ S² ** D U½ Tᵀ）。
/// 本輪再加 21 個，合計 **35 個**，與 45 個註冊空間相乘得 1,575 格。
///
/// ## 設計約束
///
/// 全部仍是**建構子**（由空間造空間的自函子），不是非建構子 ——
/// 這是第七輪定下的範圍決定。每一個都必須：
///
/// ```text
///   (1) 把對稱正定 Gram 送到對稱正定 Gram（封閉性）
///   (2) 有一條只用輸入維數的維數公式（與 sdim 之遞迴定義相符）
///   (3) 在註冊表最小維數 2 上仍有定義（不得產生 0 維空間）
/// ```
///
/// 第 (3) 條比看起來重要：Λ³ 在 n = 2 時 C(2,3) = 0，
/// 一個 0 維的「內積空間」會讓下游的正定判定、Riesz 解、
/// Cauchy–Schwarz 全部落入未定義分支而**靜默通過**。
/// 故凡階數型構造子一律夾到合法範圍（Λ^min(3,n)、Λ^max(1,n−2)），
/// 並在維數公式裡如實寫出夾值。
///
/// ## 21 個構造子
///
/// ```text
///   族      記號     作用                      dim           Gram
///   ----    -----    ----------------------    ----------    --------------------
///   張量    ⊗W₃      V ⊗ W₃                    3n            G ⊗ G_{W₃}
///           T²       V ⊗ V                     n²            G ⊗ G
///           End      V ⊗ V*                    n²            G ⊗ (G⁻¹)ᵀ
///           W₂⊗      W₂ ⊗ V                    2n            G_{W₂} ⊗ G
///   直和    ⊕W₂      V ⊕ W₂                    n+2           diag(G, G_{W₂})
///           3D       V ⊕ V ⊕ V                 3n            diag(G,G,G)
///           ⊕*       V ⊕ V*                    2n            diag(G, (G⁻¹)ᵀ)
///           ⊞W₃      V ⊞ W₃                    3n            G⊗I₃ + I_n⊗G_{W₃}
///   外冪    Λ³       Λ^min(3,n) V              C(n,min(3,n)) C_k(G)
///           Λ²*      Λ²(V*)                    C(n,2)        C₂((G⁻¹)ᵀ)
///           Λⁿ⁻²     Λ^max(1,n−2) V            C(n,max(1,n−2))
///   對稱    S²*      S²(V*)                    n(n+1)/2
///           (S²)*    (S² V)*                   n(n+1)/2
///           Λ⊕S      Λ²V ⊕ S²V                 n²            diag(C₂(G), S²)
///   子空間  U¼       前 ⌈n/4⌉ 座標              ⌈n/4⌉
///           U^c      後 ⌈n/2⌉ 座標              ⌈n/2⌉
///           Uodd     奇指標座標                 ⌊n/2⌋
///           U₂       前 min(n,2) 座標           min(n,2)
///   扭曲    Trev     反轉置換扭曲 PᵀGP          n
///           Tdg      diag(1..n) 扭曲            n
///           T³       以 G 自身扭曲 → G³         n
/// ```
///
/// ## 定理 C21-1（封閉性）
///
/// 上列 21 式皆把對稱正定送到對稱正定。
///
/// 證明：⊗、⊕、⊞、Λᵏ、* 五類之封閉性已由定理 N51-1 證出，
/// 而 ⊗W₃／T²／End／W₂⊗／⊕W₂／3D／⊕*／⊞W₃／Λ³／Λ²*／Λⁿ⁻²／S²*／
/// (S²)*／Λ⊕S 皆為此五類之有限複合，故封閉。
/// 子空間四式之選擇矩陣 S 皆為座標嵌入（行滿秩），
/// x ≠ 0 ⇒ Sx ≠ 0 故 xᵀSᵀGSx > 0。
/// 扭曲三式：Trev 之 P 為置換陣（可逆）；Tdg 之 D = diag(1..n) 可逆；
/// T³ 之扭曲矩陣為 G 本身，G 正定故可逆，且 GᵀGG = G³ 對稱，
/// 其譜為 {λᵢ³} 皆正。∎
///
/// ## 命題 C21-2（Λ⊕S 之維數恆等）
///
/// dim(Λ²V ⊕ S²V) = n(n−1)/2 + n(n+1)/2 = n² = dim(V⊗V)。
/// 此非巧合：特徵 ≠ 2 時 V⊗V = Λ²V ⊕ S²V。
/// 本庫把兩者都列為構造子，正是為了讓這條分解在普查表上
/// 以「兩個不同構造子給出相同維數」的形式被量到（見 N-87 之對帳）。

///|
/// 固定夥伴空間 W₃：維數 3，Gram 為對稱正定且非純量。
pub fn comb_partner3() -> SpaceExpr {
  let d : ReadOnlyArray[ReadOnlyArray[Int]] = [[3, 1, 0], [1, 3, 1], [0, 1, 3]]
  SLeaf("W₃", Mat::build(3, 3, (i, j) => Q::of_int(d[i][j])))
}

///|
/// n × k 座標嵌入：取第 lo, lo+1, …, lo+k−1 個座標。
pub fn comb_sel_range(n : Int, lo : Int, k : Int) -> Mat[Q] {
  Mat::build(n, k, (i, j) => if i == lo + j { Q::one() } else { Q::zero() })
}

///|
/// n × ⌊n/2⌋ 座標嵌入：取奇指標 1, 3, 5, …
pub fn comb_sel_odd(n : Int) -> Mat[Q] {
  let k = n / 2
  Mat::build(n, k, (i, j) => if i == 2 * j + 1 { Q::one() } else { Q::zero() })
}

///|
/// n × n 反轉置換陣 P[i][j] = δ_{i, n−1−j}。
pub fn comb_rev_perm(n : Int) -> Mat[Q] {
  Mat::build(n, n, (i, j) => if i == n - 1 - j { Q::one() } else { Q::zero() })
}

///|
/// n × n 對角陣 diag(1, 2, …, n)。
pub fn comb_diag_scale(n : Int) -> Mat[Q] {
  Mat::build(n, n, (i, j) => if i == j { Q::of_int(i + 1) } else { Q::zero() })
}

///|
/// 夾到合法外冪階數：1 ≤ k ≤ n。
pub fn comb_clamp_k(n : Int, k : Int) -> Int {
  if k < 1 {
    1
  } else if k > n {
    n
  } else {
    k
  }
}

///|
/// 【註冊表】第十五輪新增之 21 個構造子。
pub fn comb21_new() -> Array[CombRec] {
  let w2 = comb_partner()
  let w3 = comb_partner3()
  [
    // ---- 張量族 ----
    {
      cname: "張量W₃",
      csym: "⊗W₃",
      cari: 2,
      capply: e => STensor(e, w3),
      cdim: n => 3 * n,
    },
    {
      cname: "張量平方",
      csym: "T²",
      cari: 1,
      capply: e => STensor(e, e),
      cdim: n => n * n,
    },
    {
      cname: "自同態",
      csym: "End",
      cari: 1,
      capply: e => STensor(e, SDual(e)),
      cdim: n => n * n,
    },
    {
      cname: "左張量W₂",
      csym: "W₂⊗",
      cari: 2,
      capply: e => STensor(w2, e),
      cdim: n => 2 * n,
    },
    // ---- 直和族 ----
    {
      cname: "直和W₂",
      csym: "⊕W₂",
      cari: 2,
      capply: e => SSum(e, w2),
      cdim: n => n + 2,
    },
    {
      cname: "三倍化",
      csym: "3D",
      cari: 1,
      capply: e => SSum(e, SSum(e, e)),
      cdim: n => 3 * n,
    },
    {
      cname: "自對偶和",
      csym: "⊕*",
      cari: 1,
      capply: e => SSum(e, SDual(e)),
      cdim: n => 2 * n,
    },
    {
      cname: "Kron和W₃",
      csym: "⊞W₃",
      cari: 2,
      capply: e => SKSum(e, w3),
      cdim: n => 3 * n,
    },
    // ---- 外冪族 ----
    {
      cname: "三次外冪",
      csym: "Λ³",
      cari: 1,
      capply: e => SExt(e, comb_clamp_k(e.sdim(), 3)),
      cdim: n => binom(n, comb_clamp_k(n, 3)),
    },
    {
      cname: "對偶二次外冪",
      csym: "Λ²*",
      cari: 1,
      capply: e => SExt(SDual(e), comb_clamp_k(e.sdim(), 2)),
      cdim: n => binom(n, comb_clamp_k(n, 2)),
    },
    {
      cname: "餘維二外冪",
      csym: "Λⁿ⁻²",
      cari: 1,
      capply: e => SExt(e, comb_clamp_k(e.sdim(), e.sdim() - 2)),
      cdim: n => binom(n, comb_clamp_k(n, n - 2)),
    },
    // ---- 對稱族 ----
    {
      cname: "對偶對稱平方",
      csym: "S²*",
      cari: 1,
      capply: e => SSub(STensor(SDual(e), SDual(e)), comb_sym_sel(e.sdim())),
      cdim: n => n * (n + 1) / 2,
    },
    {
      cname: "對稱平方之對偶",
      csym: "(S²)*",
      cari: 1,
      capply: e => SDual(SSub(STensor(e, e), comb_sym_sel(e.sdim()))),
      cdim: n => n * (n + 1) / 2,
    },
    {
      cname: "外加對稱",
      csym: "Λ⊕S",
      cari: 1,
      capply: e => {
        SSum(
          SExt(e, comb_clamp_k(e.sdim(), 2)),
          SSub(STensor(e, e), comb_sym_sel(e.sdim())),
        )
      },
      cdim: n => binom(n, comb_clamp_k(n, 2)) + n * (n + 1) / 2,
    },
    // ---- 子空間族 ----
    {
      cname: "四分之一子空間",
      csym: "U¼",
      cari: 1,
      capply: e => SSub(e, comb_sel_range(e.sdim(), 0, (e.sdim() + 3) / 4)),
      cdim: n => (n + 3) / 4,
    },
    {
      cname: "後半子空間",
      csym: "U^c",
      cari: 1,
      capply: e => {
        SSub(
          e,
          comb_sel_range(
            e.sdim(),
            e.sdim() - (e.sdim() + 1) / 2,
            (e.sdim() + 1) / 2,
          ),
        )
      },
      cdim: n => (n + 1) / 2,
    },
    {
      cname: "奇指標子空間",
      csym: "Uodd",
      cari: 1,
      capply: e => SSub(e, comb_sel_odd(e.sdim())),
      cdim: n => n / 2,
    },
    {
      cname: "前二子空間",
      csym: "U₂",
      cari: 1,
      capply: e => {
        SSub(
          e,
          comb_sel_range(e.sdim(), 0, if e.sdim() < 2 { e.sdim() } else { 2 }),
        )
      },
      cdim: n => if n < 2 { n } else { 2 },
    },
    // ---- 扭曲族 ----
    {
      cname: "反轉扭曲",
      csym: "Trev",
      cari: 1,
      capply: e => STwist(e, comb_rev_perm(e.sdim())),
      cdim: n => n,
    },
    {
      cname: "對角扭曲",
      csym: "Tdg",
      cari: 1,
      capply: e => STwist(e, comb_diag_scale(e.sdim())),
      cdim: n => n,
    },
    {
      cname: "自度量扭曲",
      csym: "T³",
      cari: 1,
      capply: e => STwist(e, e.sgram()),
      cdim: n => n,
    },
  ]
}

///|
/// 【註冊表】35 個構造子 = 原 14 ＋ 新 21。
pub fn comb35_registry() -> Array[CombRec] {
  let xs : Array[CombRec] = []
  for c in comb14_registry() {
    xs.push(c)
  }
  for c in comb21_new() {
    xs.push(c)
  }
  xs
}

///|
/// 35 構造子 × 45 空間之深度普查結果。
pub struct C21Report {
  w5cells : Int
  w5sym : Int
  w5dim : Int
  w5spd : Int
  w5nonzero : Int
  w5cs : Int
  w5rz : Int
  w5rzrun : Int
  w5inst : Int
  w5dmax : Int
  w5dsum : Int
  w5digest : String
}

///|
/// 【N-87】全部 35 個構造子 × 45 個空間 = 1,575 格之深度普查。
///
/// 每格六項：Gram 對稱、維數公式（cdim 與 sdim 雙路）、正定、
/// 非退化（維數 ≥ 1）、Cauchy–Schwarz、Riesz 表示。
///
/// Riesz 需解 Gx = b（Θ(d³) 之 ℚ 消去），在 d = 220 時係數膨脹嚴重，
/// 故設維數上限；跑過的格數如實回報，未跑者不計入通過。
/// 其餘五項全格皆跑 —— 它們都是 Θ(d²) 或 Θ(d³) 整數運算。
pub fn c21_scan(rng : Rng, rzcap : Int) -> C21Report {
  let sps = space_registry_x()
  let cbs = comb35_registry()
  let c = Cost::new()
  let mut cells = 0
  let mut nsym = 0
  let mut ndim = 0
  let mut nspd = 0
  let mut nnz = 0
  let mut ncs = 0
  let mut nrz = 0
  let mut nrzrun = 0
  let mut dmax = 0
  let mut dsum = 0
  let mut h = 0UL
  for cb in cbs {
    for s in sps {
      let e = (cb.capply)(s.leaf())
      let g = e.sgram()
      let d = g.mrows
      cells = cells + 1
      dsum = dsum + d
      if d > dmax {
        dmax = d
      }
      // (1) 非退化 —— 0 維「內積空間」會讓下游檢查全部靜默通過
      if d >= 1 {
        nnz = nnz + 1
      }
      // (2) 對稱
      if g.equals(g.transpose()) {
        nsym = nsym + 1
      }
      // (3) 維數公式雙路
      if (cb.cdim)(s.sdim) == d && e.sdim() == d {
        ndim = ndim + 1
      }
      // (4) 正定
      // 【第十八輪】接 L 層分派：階數 ≥ 17 走 CRT 主子式
      if spd_fast(g) {
        nspd = nspd + 1
      }
      // (5) Cauchy–Schwarz
      let x : Array[Q] = Array::makei(d, _ => qr(rng))
      let y : Array[Q] = Array::makei(d, _ => qr(rng))
      let xy = qbil(g, x, y)
      if xy.mul(xy).cmp(qbil(g, x, x).mul(qbil(g, y, y))) <= 0 {
        ncs = ncs + 1
      }
      // (6) Riesz
      if d <= rzcap {
        nrzrun = nrzrun + 1
        let b : Array[Q] = Array::makei(d, _ => qr(rng))
        match qsolve_gauss(g, b, c) {
          Some(xv) => {
            let yv : Array[Q] = Array::makei(d, _ => qr(rng))
            let mut rhs = Q::zero()
            for i in 0..<d {
              rhs = rhs.add(b[i].mul(yv[i]))
            }
            if qbil(g, xv, yv).eq(rhs) {
              nrz = nrz + 1
            }
          }
          None => ()
        }
      }
      h = h ^ str_hash64(cb.csym + "[" + s.sname + "]=" + d.to_string())
    }
  }
  {
    w5cells: cells,
    w5sym: nsym,
    w5dim: ndim,
    w5spd: nspd,
    w5nonzero: nnz,
    w5cs: ncs,
    w5rz: nrz,
    w5rzrun: nrzrun,
    w5inst: cells * 5 + nrzrun,
    w5dmax: dmax,
    w5dsum: dsum,
    w5digest: cells.to_string() +
    ":" +
    dsum.to_string() +
    ":" +
    (h % 1000000007UL).to_string(),
  }
}

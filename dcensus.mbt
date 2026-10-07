///|
/// # N-52 D 群 × 空間 × 構造子 全量普查
///
/// ## 定義（普查格）
///
/// 一個普查格是三元組 (A, S, C)：A 為 D 群的一條內積演算法，S 為
/// 註冊空間（N-50，35 個），C 為構造子（N-51，7 個）。該格的值是
/// 「A 之判準式在 ⟦C(S)⟧ 上是否逐例成立」。
///
/// ```text
///       23 條演算法 × 35 個空間 × 7 個構造子 = 5,635 格
/// ```
///
/// ## 定義（判準式）
///
/// 每條 D 群演算法都附一條**可在 ℚ 上精確判定**的恆等式或不等式，
/// 即該條目的定理本身。判準式不是「程式沒有崩潰」，而是定理的結論：
/// 例如 D-07 的判準式是 P² = P ∧ GP = PᵀG，D-15 的判準式是
/// 平行四邊形缺陷恰為 0。
///
/// 命題 N52-1（ℚ 上不需要容差）：全部 35 個空間之 Gram 皆為 ℚ 上的
/// 對稱正定矩陣（N-50），7 個構造子保持此性質（定理 N51-1），故
/// ⟦C(S)⟧ 的內積是 ℚ-值的，判準式可用逐位相等判定。唯一的例外是
/// D-03（可開方性）與 D-23（夾角），前者判定的正是「ℚ 不對開方封閉」
/// 這件事，後者的輸出本來就落在 ℝ。
///
/// 命題 N52-2（取樣種子與枚舉順序無關）：每格的亂數種子取自
/// `str_hash64(格鍵)`，格鍵 = 演算法碼 ⊕ 構造子記號 ⊕ 空間名。
/// 故分層掃描與全量掃描對同一格給出相同裁決（同 N-42 命題 201-3a）。

///|
/// 一條 D 群演算法：代碼、名稱、判準式。
pub struct DAlgo {
  dcode : String
  dname : String
  /// 判準式：於給定空間上取樣並精確判定
  drun : (IPSpace[Array[Q], Q], Rng) -> Bool
}

// ---------------------------------------------------------------------------
//  取樣與小工具
// ---------------------------------------------------------------------------

///|
/// 取一個非零樣本（最多重抽 12 次；全零則回傳第一個基向量）。
pub fn dc_vec(sp : IPSpace[Array[Q], Q], rng : Rng) -> Array[Q] {
  for _t in 0..<12 {
    let v = (sp.vs.sample)(rng)
    let mut nz = false
    for c in v {
      if !Q::is_zero(c) {
        nz = true
      }
    }
    if nz {
      return v
    }
  }
  sp.vs.basis[0]
}

///|
/// 取 k 個非零樣本。
pub fn dc_vecs(
  sp : IPSpace[Array[Q], Q],
  rng : Rng,
  k : Int,
) -> Array[Array[Q]] {
  Array::makei(k, _ => dc_vec(sp, rng))
}

///|
/// 內積簡寫。
pub fn dc_ip(sp : IPSpace[Array[Q], Q], x : Array[Q], y : Array[Q]) -> Q {
  (sp.inner)(x, y)
}

///|
/// 判零。
pub fn dc_is_zero(v : Array[Q]) -> Bool {
  for c in v {
    if !Q::is_zero(c) {
      return false
    }
  }
  true
}

///|
/// 正交集之截斷長度：min(dim, 6)。用於 Fourier／Bessel／Parseval 三條，
/// 使成本在 28 維的格上仍然有界；k = dim 時即為完整正交基。
pub fn dc_onb_k(sp : IPSpace[Array[Q], Q]) -> Int {
  let n = sp.vs.dim
  if n < 6 {
    n
  } else {
    6
  }
}

///|
/// 由前 k 個基向量 Gram–Schmidt 得到的正交集（不含零向量）。
pub fn dc_ortho_set(sp : IPSpace[Array[Q], Q]) -> Array[Array[Q]] {
  let k = dc_onb_k(sp)
  let bs : Array[Array[Q]] = Array::makei(k, i => sp.vs.basis[i])
  gram_schmidt(sp, bs).ortho
}

///|
/// 非正規化 Fourier 係數 ⟨x,eᵢ⟩ / ⟨eᵢ,eᵢ⟩（ℚ 不對開方封閉，故用此形式）。
pub fn dc_fcoef(
  sp : IPSpace[Array[Q], Q],
  es : Array[Array[Q]],
  x : Array[Q],
) -> Array[Q] {
  Array::makei(es.length(), i => {
    let d = dc_ip(sp, es[i], es[i])
    match Q::div(dc_ip(sp, x, es[i]), d) {
      Some(v) => v
      None => Q::zero()
    }
  })
}

///|
/// 複化：同一個 Gram 看成 ℂ 上的 Hermitian 形式。
pub fn dc_cplx(sp : IPSpace[Array[Q], Q]) -> IPSpace[Array[Cpx[Q]], Cpx[Q]] {
  let n = sp.vs.dim
  let g = gram_of_space(sp)
  let gc : Mat[Cpx[Q]] = Mat::build(n, n, (i, j) => Cpx::of_real(g.at(i, j)))
  coord_ipspace("ℂ⊗" + sp.vs.vname, n, Some(gc))
}

// ---------------------------------------------------------------------------
//  【註冊表】D 群 23 條演算法之判準式
// ---------------------------------------------------------------------------

///|
/// D 群 23 條，逐條附上可在 ℚ 上精確判定的判準式。
pub fn d_registry() -> Array[DAlgo] {
  [
    // D-01 ── 古典 Gram–Schmidt：輸出兩兩正交，且 x_j = Σ R_ij u_i
    {
      dcode: "D-01",
      dname: "Gram–Schmidt 正交化（經典）",
      drun: (sp, rng) => {
        let xs = dc_vecs(sp, rng, 3)
        let g = gram_schmidt(sp, xs)
        let us = g.ortho
        for i in 0..<us.length() {
          for j in 0..<us.length() {
            if i != j && !Q::is_zero(dc_ip(sp, us[i], us[j])) {
              return false
            }
          }
        }
        for j in 0..<xs.length() {
          let cs : Array[Q] = Array::makei(us.length(), i => g.rmat.at(i, j))
          if !arr_eq(vlincomb(sp.vs, cs, us), xs[j]) {
            return false
          }
        }
        true
      },
    },
    // D-02 ── 改良 Gram–Schmidt：ℚ 上與古典版逐元相同
    {
      dcode: "D-02",
      dname: "改良 Gram–Schmidt（MGS）",
      drun: (sp, rng) => {
        let xs = dc_vecs(sp, rng, 3)
        let a = gram_schmidt(sp, xs).ortho
        let b = modified_gram_schmidt(sp, xs).ortho
        if a.length() != b.length() {
          return false
        }
        for i in 0..<a.length() {
          if !arr_eq(a[i], b[i]) {
            return false
          }
        }
        true
      },
    },
    // D-03 ── 標準正交化成功 ⟺ 每個正交向量之範數平方在 ℚ 中可開方
    {
      dcode: "D-03",
      dname: "標準正交化與體之可開方性",
      drun: (sp, rng) => {
        let xs = dc_vecs(sp, rng, 3)
        let us = gram_schmidt(sp, xs).ortho
        let mut expect = us.length() > 0
        for u in us {
          match Q::sqrt_exact(dc_ip(sp, u, u)) {
            None => expect = false
            Some(_) => ()
          }
        }
        match orthonormalize(sp, xs) {
          None => !expect
          Some(os) => {
            if !expect {
              return false
            }
            for i in 0..<os.length() {
              for j in 0..<os.length() {
                let v = dc_ip(sp, os[i], os[j])
                let want = if i == j { Q::one() } else { Q::zero() }
                if !Q::eq(v, want) {
                  return false
                }
              }
            }
            true
          }
        }
      },
    },
    // D-04 ── Gram 行列式非負，且滿足 Hadamard 不等式
    {
      dcode: "D-04",
      dname: "Gram 行列式、k 維體積與 Hadamard 不等式",
      drun: (sp, rng) => {
        let xs = dc_vecs(sp, rng, 3)
        let d = gram_det(sp, xs)
        if Q::cmp(d, Q::zero()) < 0 {
          return false
        }
        let mut prod = Q::one()
        for x in xs {
          prod = Q::mul(prod, dc_ip(sp, x, x))
        }
        Q::cmp(d, prod) <= 0
      },
    },
    // D-05 ── 最佳逼近：殘差與子空間正交
    {
      dcode: "D-05",
      dname: "正交投影與最佳逼近定理",
      drun: (sp, rng) => {
        let ws = dc_vecs(sp, rng, 2)
        let x = dc_vec(sp, rng)
        let p = project_onto(sp, ws, x)
        let r = vsub(sp.vs, x, p)
        for w in ws {
          if !Q::is_zero(dc_ip(sp, r, w)) {
            return false
          }
        }
        true
      },
    },
    // D-06 ── 距離：‖x‖² = ‖Px‖² + ‖x−Px‖²（畢氏分解）
    {
      dcode: "D-06",
      dname: "點到子空間之距離",
      drun: (sp, rng) => {
        let ws = dc_vecs(sp, rng, 2)
        let x = dc_vec(sp, rng)
        let p = project_onto(sp, ws, x)
        let r = vsub(sp.vs, x, p)
        Q::eq(dc_ip(sp, x, x), Q::add(dc_ip(sp, p, p), dc_ip(sp, r, r)))
      },
    },
    // D-07 ── 投影矩陣之代數特徵：P² = P 且 GP = PᵀG（G-自伴）
    {
      dcode: "D-07",
      dname: "投影矩陣之代數特徵",
      drun: (sp, rng) => {
        let ws = dc_vecs(sp, rng, 2)
        let p = projection_matrix(sp, ws)
        if !p.times(p).equals(p) {
          return false
        }
        let g = gram_of_space(sp)
        g.times(p).equals(p.transpose().times(g))
      },
    },
    // D-08 ── Riesz：φ(bᵢ) = ⟨bᵢ, v_φ⟩ 逐基向量相符
    {
      dcode: "D-08",
      dname: "Riesz 表示定理",
      drun: (sp, rng) => {
        let n = sp.vs.dim
        let c : Array[Q] = Array::makei(n, _ => Scalar::s_rand(rng))
        let v = riesz_vector(sp, c)
        for i in 0..<n {
          if !Q::eq(dc_ip(sp, sp.vs.basis[i], v), c[i]) {
            return false
          }
        }
        true
      },
    },
    // D-09 ── 伴隨算子：⟨Tx, y⟩ = ⟨x, T*y⟩
    {
      dcode: "D-09",
      dname: "伴隨算子之矩陣公式",
      drun: (sp, rng) => {
        let n = sp.vs.dim
        let t : Mat[Q] = Mat::build(n, n, (_i, _j) => Scalar::s_rand(rng))
        let ta = adjoint_matrix(sp, sp, t)
        for _trial in 0..<2 {
          let x = dc_vec(sp, rng)
          let y = dc_vec(sp, rng)
          let lhs = dc_ip(sp, t.apply(x), y)
          let rhs = dc_ip(sp, x, ta.apply(y))
          if !Q::eq(lhs, rhs) {
            return false
          }
        }
        true
      },
    },
    // D-10 ── Fourier 合成 ≡ 正交投影（非正規化形式）
    {
      dcode: "D-10",
      dname: "Fourier 係數與合成",
      drun: (sp, rng) => {
        let es = dc_ortho_set(sp)
        if es.length() == 0 {
          return false
        }
        let x = dc_vec(sp, rng)
        let cs = dc_fcoef(sp, es, x)
        arr_eq(vlincomb(sp.vs, cs, es), project_onto(sp, es, x))
      },
    },
    // D-11 ── Bessel：部分和 ≤ ⟨x,x⟩
    {
      dcode: "D-11",
      dname: "Bessel 不等式",
      drun: (sp, rng) => {
        let es = dc_ortho_set(sp)
        let x = dc_vec(sp, rng)
        let cs = dc_fcoef(sp, es, x)
        let mut acc = Q::zero()
        for i in 0..<es.length() {
          acc = Q::add(
            acc,
            Q::mul(Q::mul(cs[i], cs[i]), dc_ip(sp, es[i], es[i])),
          )
        }
        Q::cmp(acc, dc_ip(sp, x, x)) <= 0
      },
    },
    // D-12 ── Parseval：和 = ‖Px‖²；且正交集滿秩時 = ‖x‖²
    {
      dcode: "D-12",
      dname: "Parseval 恆等式",
      drun: (sp, rng) => {
        let es = dc_ortho_set(sp)
        let x = dc_vec(sp, rng)
        let cs = dc_fcoef(sp, es, x)
        let mut acc = Q::zero()
        for i in 0..<es.length() {
          acc = Q::add(
            acc,
            Q::mul(Q::mul(cs[i], cs[i]), dc_ip(sp, es[i], es[i])),
          )
        }
        let p = project_onto(sp, es, x)
        if !Q::eq(acc, dc_ip(sp, p, p)) {
          return false
        }
        if es.length() == sp.vs.dim {
          return Q::eq(acc, dc_ip(sp, x, x))
        }
        true
      },
    },
    // D-13 ── Cauchy–Schwarz：鬆弛量 ≥ 0，且線性相依時恰為 0
    {
      dcode: "D-13",
      dname: "Cauchy–Schwarz 不等式（精確憑證）",
      drun: (sp, rng) => {
        let x = dc_vec(sp, rng)
        let y = dc_vec(sp, rng)
        if Q::cmp(cauchy_schwarz_slack(sp, x, y), Q::zero()) < 0 {
          return false
        }
        let y2 = (sp.vs.smul)(Q::frac(3, 2), x)
        Q::is_zero(cauchy_schwarz_slack(sp, x, y2))
      },
    },
    // D-14 ── 三角不等式（免開方之精確判定）
    {
      dcode: "D-14",
      dname: "三角不等式（免開方之精確判定）",
      drun: (sp, rng) => {
        let x = dc_vec(sp, rng)
        let y = dc_vec(sp, rng)
        triangle_holds(sp, x, y)
      },
    },
    // D-15 ── 平行四邊形律：缺陷恰為 0
    {
      dcode: "D-15",
      dname: "平行四邊形律",
      drun: (sp, rng) => {
        let x = dc_vec(sp, rng)
        let y = dc_vec(sp, rng)
        Q::is_zero(parallelogram_defect(sp, x, y))
      },
    },
    // D-16 ── 實極化恆等式
    {
      dcode: "D-16",
      dname: "實極化恆等式",
      drun: (sp, rng) => {
        let x = dc_vec(sp, rng)
        let y = dc_vec(sp, rng)
        Q::eq(polarization_real(sp, x, y), dc_ip(sp, x, y))
      },
    },
    // D-17 ── 複極化恆等式（於同一 Gram 之複化上）
    {
      dcode: "D-17",
      dname: "複極化恆等式",
      drun: (sp, rng) => {
        let cs = dc_cplx(sp)
        let x = (cs.vs.sample)(rng)
        let y = (cs.vs.sample)(rng)
        Scalar::s_eq(polarization_complex(cs, x, y), (cs.inner)(x, y))
      },
    },
    // D-18 ── 畢氏定理與其逆
    {
      dcode: "D-18",
      dname: "畢氏定理與其逆",
      drun: (sp, rng) => {
        let x = dc_vec(sp, rng)
        let y = dc_vec(sp, rng)
        let yp = vsub(sp.vs, y, project_onto(sp, [x], y))
        let s = vadd(sp.vs, x, yp)
        if !Q::eq(dc_ip(sp, s, s), Q::add(dc_ip(sp, x, x), dc_ip(sp, yp, yp))) {
          return false
        }
        // 逆：‖x+y‖² = ‖x‖² + ‖y‖² ⟹ ⟨x,y⟩ = 0（實內積）
        let t = vadd(sp.vs, x, y)
        let pyth = Q::eq(
          dc_ip(sp, t, t),
          Q::add(dc_ip(sp, x, x), dc_ip(sp, y, y)),
        )
        pyth == Q::is_zero(dc_ip(sp, x, y))
      },
    },
    // D-19 ── 正交補：維數互補，且逐對正交
    {
      dcode: "D-19",
      dname: "正交補與正交分解 V = W ⊕ W^⊥",
      drun: (sp, rng) => {
        let ws = dc_vecs(sp, rng, 2)
        let rank = gram_schmidt(sp, ws).ortho.length()
        let perp = orthogonal_complement(sp, ws)
        if rank + perp.length() != sp.vs.dim {
          return false
        }
        for w in ws {
          for u in perp {
            if !Q::is_zero(dc_ip(sp, w, u)) {
              return false
            }
          }
        }
        true
      },
    },
    // D-20 ── 等距判定 ⟺ 基底變換後 Gram 不變
    {
      dcode: "D-20",
      dname: "等距判定與 Gram 之基底變換律",
      drun: (sp, _rng) => {
        let n = sp.vs.dim
        let g = gram_of_space(sp)
        let id : Mat[Q] = Mat::ident(n)
        if !is_isometry(sp, id) {
          return false
        }
        if !gram_change_of_basis(g, id).equals(g) {
          return false
        }
        let s = comb_unitri(n)
        is_isometry(sp, s) == gram_change_of_basis(g, s).equals(g)
      },
    },
    // D-21 ── Householder 反射：H v = −v 且保內積
    {
      dcode: "D-21",
      dname: "Householder 反射（抽象版）",
      drun: (sp, rng) => {
        let v = dc_vec(sp, rng)
        if Q::is_zero(dc_ip(sp, v, v)) {
          return false
        }
        if !arr_eq(householder(sp, v, v), (sp.vs.smul)(Q::of_int(-1), v)) {
          return false
        }
        let x = dc_vec(sp, rng)
        let y = dc_vec(sp, rng)
        Q::eq(
          dc_ip(sp, householder(sp, v, x), householder(sp, v, y)),
          dc_ip(sp, x, y),
        )
      },
    },
    // D-22 ── 最小二乘：正規方程 Gc = b 精確成立，殘差正交
    {
      dcode: "D-22",
      dname: "最小二乘與正規方程",
      drun: (sp, rng) => {
        let ws = dc_vecs(sp, rng, 2)
        let x = dc_vec(sp, rng)
        let (c, _) = least_squares(sp, ws, x)
        let k = ws.length()
        for i in 0..<k {
          let mut lhs = Q::zero()
          for j in 0..<k {
            lhs = Q::add(lhs, Q::mul(dc_ip(sp, ws[j], ws[i]), c[j]))
          }
          if !Q::eq(lhs, dc_ip(sp, x, ws[i])) {
            return false
          }
        }
        let r = vsub(sp.vs, x, vlincomb(sp.vs, c, ws))
        for w in ws {
          if !Q::is_zero(dc_ip(sp, r, w)) {
            return false
          }
        }
        true
      },
    },
    // D-23 ── 夾角與餘弦相似度：|cos| ≤ 1（ℝ 量，含浮點容差）
    {
      dcode: "D-23",
      dname: "夾角與餘弦相似度",
      drun: (sp, rng) => {
        let x = dc_vec(sp, rng)
        let y = dc_vec(sp, rng)
        let c = cosine_similarity(sp, x, y)
        if c < -1.0 - 1.0e-9 || c > 1.0 + 1.0e-9 {
          return false
        }
        let a = angle_between(sp, x, y)
        a >= -1.0e-9 && a <= 3.1415926535897932 + 1.0e-9
      },
    },
  ]
}

// ---------------------------------------------------------------------------
//  普查
// ---------------------------------------------------------------------------

///|
/// 普查結果。
pub struct DCensus {
  cells : Int
  pass : Int
  fail : Int
  dmax : Int
  /// 實際覆蓋到的 (空間數, 構造子數, 演算法數)
  cov : (Int, Int, Int)
  misses : Array[String]
  digest : String
}

///|
/// 每格的取樣種子（只由格鍵決定，與枚舉順序無關 —— 命題 N52-2）。
pub fn dcell_rng(key : String) -> Rng {
  Rng::new(0xD0_CE_11_5EEDUL ^ str_hash64(key))
}

///|
/// 格鍵。
pub fn dcell_key(acode : String, csym : String, sname : String) -> String {
  acode + "@" + csym + "[" + sname + "]"
}

///|
/// 計算布林陣列中為真者之個數。
pub fn dc_count(xs : Array[Bool]) -> Int {
  let mut n = 0
  for x in xs {
    if x {
      n = n + 1
    }
  }
  n
}

///|
/// 普查核心。三個旋鈕：
///   `step`   —— 分層步長，格 (i,j,k) 取 (i + 2j + 3k) mod step == 0；1 為全量
///   `maxdim` —— 構造後維數上限，0 為不設限
///   `codes`  —— 演算法代碼白名單，空陣列為全部
///
/// 命題 N52-2 保證三個旋鈕不影響任一格的裁決：種子只由格鍵決定。
pub fn dcensus_core(step : Int, maxdim : Int, codes : Array[String]) -> DCensus {
  let all = d_registry()
  let algos : Array[DAlgo] = if codes.length() == 0 {
    all
  } else {
    let sel : Array[DAlgo] = []
    for a in all {
      for c in codes {
        if a.dcode == c {
          sel.push(a)
        }
      }
    }
    sel
  }
  let spaces = space_registry()
  let combs = comb7_registry()
  let misses : Array[String] = []
  let cs : Array[Bool] = Array::make(spaces.length(), false)
  let cc : Array[Bool] = Array::make(combs.length(), false)
  let ca : Array[Bool] = Array::make(algos.length(), false)
  let mut cells = 0
  let mut pass = 0
  let mut dmax = 0
  let mut h : UInt64 = 0xcbf2_9ce4_8422_2325UL
  for si in 0..<spaces.length() {
    for ci in 0..<combs.length() {
      let r = spaces[si]
      let c = combs[ci]
      let d = (c.cdim)(r.sdim)
      if maxdim > 0 && d > maxdim {
        continue
      }
      let mut any = false
      for ai in 0..<algos.length() {
        if (si + 2 * ci + 3 * ai) % step == 0 {
          any = true
        }
      }
      if !any {
        continue
      }
      if d > dmax {
        dmax = d
      }
      let sp = comb7_space(r, c)
      for ai in 0..<algos.length() {
        if (si + 2 * ci + 3 * ai) % step != 0 {
          continue
        }
        let a = algos[ai]
        let key = dcell_key(a.dcode, c.csym, r.sname)
        let ok = (a.drun)(sp, dcell_rng(key))
        cells = cells + 1
        cs[si] = true
        cc[ci] = true
        ca[ai] = true
        if ok {
          pass = pass + 1
        } else {
          misses.push(key)
        }
        h = (h ^ str_hash64(key + (if ok { "+" } else { "-" }))) *
          0x1000_0000_01b3UL
      }
    }
  }
  {
    cells,
    pass,
    fail: cells - pass,
    dmax,
    cov: (dc_count(cs), dc_count(cc), dc_count(ca)),
    misses,
    digest: cells.to_string() +
    ":" +
    pass.to_string() +
    ":" +
    (h % 1000000007UL).to_string(),
  }
}

///|
/// 全量普查：23 × 35 × 7 = 5,635 格。`maxdim` 為構造後維數上限（0 = 不設限）。
pub fn dcensus_scan(maxdim : Int) -> DCensus {
  dcensus_core(1, maxdim, [])
}

///|
/// 分層抽樣（義務用）。
///
/// 命題 N52-3（分層仍覆蓋全表）：步長 step 與表長互質時，固定 i 後
/// 2j + 3k 走遍 mod step 的全部剩餘類，故每個空間、每個構造子、每條
/// 演算法都至少被取到一次。`DCensus.cov` 回傳實際覆蓋度，供義務直接斷言，
/// 不靠上述論證。
pub fn dcensus_stratum(step : Int, maxdim : Int) -> DCensus {
  dcensus_core(step, maxdim, [])
}

///|
/// 只跑指定演算法子集。
pub fn dcensus_subset(codes : Array[String], maxdim : Int) -> DCensus {
  dcensus_core(1, maxdim, codes)
}

///|
/// 逐演算法統計：(代碼, 通過, 總數)。
pub fn dcensus_by_algo(maxdim : Int) -> Array[(String, Int, Int)] {
  let out : Array[(String, Int, Int)] = []
  for a in d_registry() {
    let c = dcensus_core(1, maxdim, [a.dcode])
    out.push((a.dcode, c.pass, c.cells))
  }
  out
}

///|
/// 逐構造子統計：(記號, 通過, 總數)。
pub fn dcensus_by_comb(maxdim : Int) -> Array[(String, Int, Int)] {
  let out : Array[(String, Int, Int)] = []
  for c in comb7_registry() {
    let mut ok = 0
    let mut tot = 0
    for r in space_registry() {
      let d = (c.cdim)(r.sdim)
      if maxdim > 0 && d > maxdim {
        continue
      }
      let sp = comb7_space(r, c)
      for a in d_registry() {
        let key = dcell_key(a.dcode, c.csym, r.sname)
        tot = tot + 1
        if (a.drun)(sp, dcell_rng(key)) {
          ok = ok + 1
        }
      }
    }
    out.push((c.csym, ok, tot))
  }
  out
}

///|
/// 逐空間族統計：(族名, 通過, 總數)。
pub fn dcensus_by_family(maxdim : Int) -> Array[(String, Int, Int)] {
  let out : Array[(String, Int, Int)] = []
  for r in space_registry() {
    let mut ok = 0
    let mut tot = 0
    for c in comb7_registry() {
      let d = (c.cdim)(r.sdim)
      if maxdim > 0 && d > maxdim {
        continue
      }
      let sp = comb7_space(r, c)
      for a in d_registry() {
        let key = dcell_key(a.dcode, c.csym, r.sname)
        tot = tot + 1
        if (a.drun)(sp, dcell_rng(key)) {
          ok = ok + 1
        }
      }
    }
    let mut found = false
    for t in 0..<out.length() {
      if out[t].0 == r.fam {
        out[t] = (r.fam, out[t].1 + ok, out[t].2 + tot)
        found = true
        break
      }
    }
    if !found {
      out.push((r.fam, ok, tot))
    }
  }
  out
}

// ---------------------------------------------------------------------------
//  公理歸因：每條判準式實際用到內積的哪一條公理
// ---------------------------------------------------------------------------

///|
/// 三個「壞 Gram」：各破壞內積公理之一。
///   不定型 diag(1,−1,−1)  —— 對稱、非退化，但**不正定**
///   非對稱型 [[2,1,0],[0,2,1],[0,0,2]] —— 正對角、非退化，但**不對稱**
///   退化型 diag(1,1,0)    —— 對稱、半正定，但**退化**
pub fn dc_broken(kind : Int) -> IPSpace[Array[Q], Q] {
  if kind == 0 {
    let g : Mat[Q] = Mat::build(3, 3, (i, j) => {
      if i != j {
        Q::zero()
      } else if i == 0 {
        Q::of_int(1)
      } else {
        Q::of_int(-1)
      }
    })
    coord_ipspace("不定型 diag(1,−1,−1)", 3, Some(g))
  } else if kind == 1 {
    let d : ReadOnlyArray[ReadOnlyArray[Int]] = [
      [2, 1, 0],
      [0, 2, 1],
      [0, 0, 2],
    ]
    coord_ipspace(
      "非對稱型",
      3,
      Some(Mat::build(3, 3, (i, j) => Q::of_int(d[i][j]))),
    )
  } else {
    let g : Mat[Q] = Mat::build(3, 3, (i, j) => {
      if i == j && i < 2 {
        Q::one()
      } else {
        Q::zero()
      }
    })
    coord_ipspace("退化型 diag(1,1,0)", 3, Some(g))
  }
}

///|
/// 公理歸因表：對每條 D 群判準式，記錄它在三種壞 Gram 上是否被推翻。
/// 回傳 (代碼, 不定型被推翻, 非對稱型被推翻, 退化型被推翻, 正定型成立)。
///
/// 命題 N52-4（判準式之公理依賴可被量出來）：一條判準式若在「壞 X」上
/// 仍然成立，表示它的證明沒有用到公理 X。逐條量測即得 23 條判準式對
/// 正定性／對稱性／非退化性三條公理的依賴圖 —— 這同時是普查的鑑別力
/// 證據：恆真的判準式在三種壞 Gram 上都不會倒。
pub fn dcensus_axiom_profile_n(
  nsamp : Int,
) -> Array[(String, Bool, Bool, Bool, Bool)] {
  let good : IPSpace[Array[Q], Q] = coord_ipspace("E³", 3, None)
  let out : Array[(String, Bool, Bool, Bool, Bool)] = []
  for a in d_registry() {
    let mut f0 = false
    let mut f1 = false
    let mut f2 = false
    let mut g = true
    for s in 1..<(nsamp + 1) {
      let seed = s.to_uint64()
      if !(a.drun)(dc_broken(0), Rng::new(0xBAD0UL * seed + 7UL)) {
        f0 = true
      }
      if !(a.drun)(dc_broken(1), Rng::new(0xBAD1UL * seed + 11UL)) {
        f1 = true
      }
      if !(a.drun)(dc_broken(2), Rng::new(0xBAD2UL * seed + 13UL)) {
        f2 = true
      }
      if !(a.drun)(good, Rng::new(0x600DUL * seed + 17UL)) {
        g = false
      }
    }
    out.push((a.dcode, f0, f1, f2, g))
  }
  out
}

///|
/// 公理歸因之統計：(不定型推翻數, 非對稱型推翻數, 退化型推翻數,
/// 至少被一種推翻之數, 三種都沒推翻之數, 正定型成立數)。
pub fn dcensus_axiom_stats_n(nsamp : Int) -> (Int, Int, Int, Int, Int, Int) {
  let mut a = 0
  let mut b = 0
  let mut c = 0
  let mut any = 0
  let mut none = 0
  let mut g = 0
  for p in dcensus_axiom_profile_n(nsamp) {
    if p.1 {
      a = a + 1
    }
    if p.2 {
      b = b + 1
    }
    if p.3 {
      c = c + 1
    }
    if p.1 || p.2 || p.3 {
      any = any + 1
    } else {
      none = none + 1
    }
    if p.4 {
      g = g + 1
    }
  }
  (a, b, c, any, none, g)
}

///|
/// 逐構造子之「移動數」：該構造子在 35 個空間中，有幾個被它真的改變了
/// （維數或 Gram 至少一者不同）。移動數為 0 即為冗員。
pub fn comb7_moved() -> Array[(String, Int)] {
  let out : Array[(String, Int)] = []
  for c in comb7_registry() {
    let mut mv = 0
    for r in space_registry() {
      let g = comb7_gram(r, c)
      if g.mrows != r.sdim || !g.equals(r.sg) {
        mv = mv + 1
      }
    }
    out.push((c.csym, mv))
  }
  out
}

///|
/// 報表用：24 組樣本之公理歸因表。
pub fn dcensus_axiom_profile() -> Array[(String, Bool, Bool, Bool, Bool)] {
  dcensus_axiom_profile_n(24)
}

///|
/// 報表用：24 組樣本之公理歸因統計。
pub fn dcensus_axiom_stats() -> (Int, Int, Int, Int, Int, Int) {
  dcensus_axiom_stats_n(24)
}

///|
/// 一趟掃完全量，同時回傳總表與三個分項（逐演算法／逐構造子／逐空間族）。
/// 分項各自再掃一次等於把同一件事做四遍 —— 本函式只掃一遍。
pub fn dcensus_report() -> (
  DCensus,
  Array[(String, Int, Int)],
  Array[(String, Int, Int)],
  Array[(String, Int, Int)],
) {
  let algos = d_registry()
  let spaces = space_registry()
  let combs = comb7_registry()
  let na = algos.length()
  let nc = combs.length()
  let aok : Array[Int] = Array::make(na, 0)
  let atot : Array[Int] = Array::make(na, 0)
  let cok : Array[Int] = Array::make(nc, 0)
  let ctot : Array[Int] = Array::make(nc, 0)
  let fams : Array[String] = []
  let fok : Array[Int] = []
  let ftot : Array[Int] = []
  let misses : Array[String] = []
  let mut cells = 0
  let mut pass = 0
  let mut dmax = 0
  let mut h : UInt64 = 0xcbf2_9ce4_8422_2325UL
  for si in 0..<spaces.length() {
    let r = spaces[si]
    let mut fi = -1
    for t in 0..<fams.length() {
      if fams[t] == r.fam {
        fi = t
      }
    }
    if fi < 0 {
      fams.push(r.fam)
      fok.push(0)
      ftot.push(0)
      fi = fams.length() - 1
    }
    for ci in 0..<nc {
      let c = combs[ci]
      let d = (c.cdim)(r.sdim)
      if d > dmax {
        dmax = d
      }
      let sp = comb7_space(r, c)
      for ai in 0..<na {
        let a = algos[ai]
        let key = dcell_key(a.dcode, c.csym, r.sname)
        let ok = (a.drun)(sp, dcell_rng(key))
        cells = cells + 1
        atot[ai] = atot[ai] + 1
        ctot[ci] = ctot[ci] + 1
        ftot[fi] = ftot[fi] + 1
        if ok {
          pass = pass + 1
          aok[ai] = aok[ai] + 1
          cok[ci] = cok[ci] + 1
          fok[fi] = fok[fi] + 1
        } else {
          misses.push(key)
        }
        h = (h ^ str_hash64(key + (if ok { "+" } else { "-" }))) *
          0x1000_0000_01b3UL
      }
    }
  }
  let cen = DCensus::{
    cells,
    pass,
    fail: cells - pass,
    dmax,
    cov: (spaces.length(), nc, na),
    misses,
    digest: cells.to_string() +
    ":" +
    pass.to_string() +
    ":" +
    (h % 1000000007UL).to_string(),
  }
  (
    cen,
    Array::makei(na, i => (algos[i].dcode, aok[i], atot[i])),
    Array::makei(nc, i => (combs[i].csym, cok[i], ctot[i])),
    Array::makei(fams.length(), i => (fams[i], fok[i], ftot[i])),
  )
}

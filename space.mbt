// ============================================================================
//  檔案 04：space.mbt — 向量空間與有限維內積空間之公理化介面
// ============================================================================
//
// 【公理系 V】（體 𝔽 上之向量空間）
//   集合 V 連同 + : V×V→V、· : 𝔽×V→V，滿足
//     V1 結合律      (u+v)+w = u+(v+w)
//     V2 交換律      u+v = v+u
//     V3 零元        ∃0 ∀v, v+0 = v
//     V4 加法逆元    ∀v ∃(−v), v+(−v) = 0
//     V5 純量單位    1·v = v
//     V6 純量結合    (αβ)·v = α·(β·v)
//     V7 向量分配    α·(u+v) = α·u + α·v
//     V8 純量分配    (α+β)·v = α·v + β·v
//   （封閉性由型別系統保證：add : (V,V)→V 之型別即為封閉性之證明。）
//
// 【推論 V9】0·v = 0_V。證明：0·v = (0+0)·v = 0·v + 0·v，兩邊加 −(0·v)。∎
// 【推論 V10】(−1)·v = −v。證明：v + (−1)v = (1 + (−1))v = 0·v = 0_V。∎
// 【推論 V11】α·0_V = 0_V。證明：α·0 = α·(0+0) = α·0 + α·0。∎
//
// 【定義 B】（基底與座標同構）
//   B = (b₁,…,b_n) 為基底 ⟺ 線性映射 E : 𝔽ⁿ → V, E(c) = Σ cᵢbᵢ 為雙射。
//   其逆 C = E⁻¹ 稱座標映射。有限維 ⇔ 存在這樣的 n，n = dim V。
//   本實作把 (basis, expand = E, coord = C) 直接放入結構，
//   並以「C∘E = id_{𝔽ⁿ} ∧ E∘C = id_V」作為可執行之證明義務（見 obligations）。
//
// 【公理系 I】（內積；約定：第一變數線性、第二變數共軛線性）
//     I1 ⟨x+y, z⟩ = ⟨x,z⟩ + ⟨y,z⟩
//     I2 ⟨α x, y⟩ = α⟨x,y⟩
//     I3 ⟨y, x⟩ = ‾⟨x,y⟩                  （Hermitian 對稱；實體上即對稱）
//     I4 ⟨x,x⟩ ∈ P ∪ {0}（實且非負）
//     I5 ⟨x,x⟩ = 0 ⟺ x = 0               （正定）
//   推論 I6 ⟨x, y+z⟩ = ⟨x,y⟩ + ⟨x,z⟩，I7 ⟨x, αy⟩ = ‾α⟨x,y⟩（由 I1–I3 導出）。
// ============================================================================

///|
/// 向量空間（字典傳遞法 / dictionary passing：空間是一等公民，可被組合）。
pub struct VSpace[V, F] {
  /// 空間名稱（報表用）
  vname : String
  /// 維數 dim_𝔽 V
  dim : Int
  /// 零向量
  zero : V
  /// 加法
  add : (V, V) -> V
  /// 加法逆元
  neg : (V) -> V
  /// 純量乘法
  smul : (F, V) -> V
  /// 向量等價判定
  veq : (V, V) -> Bool
  /// 基底 (b₁,…,b_n)
  basis : Array[V]
  /// 座標映射 C : V → 𝔽ⁿ
  coord : (V) -> Array[F]
  /// 展開映射 E : 𝔽ⁿ → V
  expand : (Array[F]) -> V
  /// 列印
  vshow : (V) -> String
  /// 取樣
  sample : (Rng) -> V
}

///|
/// 有限維內積空間 = 向量空間 + 內積形式。
pub struct IPSpace[V, F] {
  /// 底層向量空間
  vs : VSpace[V, F]
  /// 內積之名稱／公式
  ipname : String
  /// ⟨·,·⟩：第一變數線性、第二變數共軛線性
  inner : (V, V) -> F
}

// ---------------------------------------------------------------------------
//  由公理導出之向量運算
// ---------------------------------------------------------------------------

///|
/// 空間介面之加法：s.add(a, b)（公理 V1）。
pub fn[V, F] vadd(s : VSpace[V, F], a : V, b : V) -> V {
  (s.add)(a, b)
}

///|
/// a − b ≔ a + (−b)
pub fn[V, F] vsub(s : VSpace[V, F], a : V, b : V) -> V {
  (s.add)(a, (s.neg)(b))
}

///|
/// 取座標：元素在其基底下之係數 αᵢ。
pub fn[V, F] vcoord(s : VSpace[V, F], a : V) -> Array[F] {
  (s.coord)(a)
}

///|
/// 線性組合 Σ cᵢ·xᵢ（長度取 min）
pub fn[V, F] vlincomb(s : VSpace[V, F], cs : Array[F], xs : Array[V]) -> V {
  let n = if cs.length() < xs.length() { cs.length() } else { xs.length() }
  let mut acc = s.zero
  for i in 0..<n {
    acc = (s.add)(acc, (s.smul)(cs[i], xs[i]))
  }
  acc
}

///|
/// 內積 ⟨x,y⟩
pub fn[V, F] ip(s : IPSpace[V, F], x : V, y : V) -> F {
  (s.inner)(x, y)
}

///|
/// ‖x‖ 之雙精度值（√⟨x,x⟩）
pub fn[V, F : Scalar] ip_norm(s : IPSpace[V, F], x : V) -> Double {
  sqrt_newton(F::s_to_double((s.inner)(x, x)))
}

///|
/// 正交判定 ⟨x,y⟩ = 0
pub fn[V, F : Scalar] ip_orth(s : IPSpace[V, F], x : V, y : V) -> Bool {
  F::s_is_zero((s.inner)(x, y))
}

// ---------------------------------------------------------------------------
//  檢驗結果型別
// ---------------------------------------------------------------------------

///|
/// 一條證明義務之檢驗結果。
pub struct Check {
  /// 義務編號／名稱
  cname : String
  /// 是否通過
  ok : Bool
  /// 測試實例數
  trials : Int
  /// 反例或補充說明
  detail : String
}

///|
/// 造一筆檢定結果 Check（名稱、成敗、實例數、細節）。
pub fn mk_check(
  name : String,
  ok : Bool,
  trials : Int,
  detail : String,
) -> Check {
  { cname: name, ok, trials, detail, }
}

///|
/// 合併多條檢驗（全部通過才通過）。
pub fn check_all(name : String, cs : Array[Check]) -> Check {
  let mut ok = true
  let mut trials = 0
  let mut bad = ""
  for c in cs {
    trials = trials + c.trials
    if !c.ok {
      ok = false
      if bad == "" {
        bad = c.cname + ": " + c.detail
      }
    }
  }
  { cname: name, ok, trials, detail: if ok { "全部通過" } else { bad }, }
}

// ---------------------------------------------------------------------------
// 【演算法 008】向量空間公理檢驗器（V1–V8 + 推論 V9–V11）
//
// 形式化地位（Schwartz–Zippel）：V1–V8 於固定維數 n 下，兩邊皆為座標與純量之
// 多項式映射（次數 ≤ 2）。若恆等式不成立，則其差為非零多項式 P，次數 d ≤ 2，
// 於有限取樣集 S ⊂ ℚ（|S| ≥ 13·4 = 52 個小有理數）隨機取值時
//   Pr[P(ξ)=0] ≤ d/|S| ≤ 2/52 < 0.04，
// 故 t 次獨立試驗全通過而命題為假之機率 ≤ 0.04^t（t = 24 ⇒ < 10⁻³⁴）。
// 於精確軌道（ℚ, ℚ(i)）此論證嚴格成立，因為算術無捨入誤差。
// ---------------------------------------------------------------------------

///|
/// 檢驗向量空間八條公理（+ 三條推論），回傳 11 條檢驗結果。
pub fn[V, F : Scalar] check_vector_space_axioms(
  s : VSpace[V, F],
  rng : Rng,
  trials : Int,
) -> Array[Check] {
  let res : Array[Check] = []
  let mut ok1 = true
  let mut ok2 = true
  let mut ok3 = true
  let mut ok4 = true
  let mut ok5 = true
  let mut ok6 = true
  let mut ok7 = true
  let mut ok8 = true
  let mut ok9 = true
  let mut ok10 = true
  let mut ok11 = true
  for _t in 0..<trials {
    let u = (s.sample)(rng)
    let v = (s.sample)(rng)
    let w = (s.sample)(rng)
    let a = F::s_rand(rng)
    let b = F::s_rand(rng)
    // V1 結合律
    if !(s.veq)((s.add)((s.add)(u, v), w), (s.add)(u, (s.add)(v, w))) {
      ok1 = false
    }
    // V2 交換律
    if !(s.veq)((s.add)(u, v), (s.add)(v, u)) {
      ok2 = false
    }
    // V3 零元
    if !(s.veq)((s.add)(u, s.zero), u) {
      ok3 = false
    }
    // V4 逆元
    if !(s.veq)((s.add)(u, (s.neg)(u)), s.zero) {
      ok4 = false
    }
    // V5 純量單位
    if !(s.veq)((s.smul)(F::s_one(), u), u) {
      ok5 = false
    }
    // V6 純量結合
    if !(s.veq)((s.smul)(F::s_mul(a, b), u), (s.smul)(a, (s.smul)(b, u))) {
      ok6 = false
    }
    // V7 向量分配
    if !(s.veq)(
        (s.smul)(a, (s.add)(u, v)),
        (s.add)((s.smul)(a, u), (s.smul)(a, v)),
      ) {
      ok7 = false
    }
    // V8 純量分配
    if !(s.veq)(
        (s.smul)(F::s_add(a, b), u),
        (s.add)((s.smul)(a, u), (s.smul)(b, u)),
      ) {
      ok8 = false
    }
    // V9 0·v = 0
    if !(s.veq)((s.smul)(F::s_zero(), u), s.zero) {
      ok9 = false
    }
    // V10 (−1)·v = −v
    if !(s.veq)((s.smul)(F::s_neg(F::s_one()), u), (s.neg)(u)) {
      ok10 = false
    }
    // V11 α·0 = 0
    if !(s.veq)((s.smul)(a, s.zero), s.zero) {
      ok11 = false
    }
  }
  res.push(mk_check("V1 加法結合律", ok1, trials, "(u+v)+w = u+(v+w)"))
  res.push(mk_check("V2 加法交換律", ok2, trials, "u+v = v+u"))
  res.push(mk_check("V3 零元", ok3, trials, "v+0 = v"))
  res.push(mk_check("V4 加法逆元", ok4, trials, "v+(−v) = 0"))
  res.push(mk_check("V5 純量單位", ok5, trials, "1·v = v"))
  res.push(mk_check("V6 純量結合律", ok6, trials, "(αβ)v = α(βv)"))
  res.push(mk_check("V7 向量分配律", ok7, trials, "α(u+v) = αu+αv"))
  res.push(mk_check("V8 純量分配律", ok8, trials, "(α+β)v = αv+βv"))
  res.push(mk_check("V9 推論 0·v=0", ok9, trials, "由 V8 導出"))
  res.push(
    mk_check("V10 推論 (−1)v=−v", ok10, trials, "由 V5,V8,V9 導出"),
  )
  res.push(mk_check("V11 推論 α·0=0", ok11, trials, "由 V7 導出"))
  res
}

// ---------------------------------------------------------------------------
// 【演算法 009】基底／座標同構檢驗器
// 命題：若 C∘E = id_{𝔽ⁿ} 且 E∘C = id_V，則 B 為基底且 dim V = n。
// 證明：E 為線性滿射（有右逆 C）兼單射（有左逆 C）⇒ 同構 ⇒ B = E(標準基) 為基底。∎
// ---------------------------------------------------------------------------

///|
/// 檢驗 (basis, coord, expand) 構成座標同構 𝔽ⁿ ≅ V。
pub fn[V, F : Scalar] check_basis_iso(
  s : VSpace[V, F],
  rng : Rng,
  trials : Int,
) -> Array[Check] {
  let res : Array[Check] = []
  let n = s.dim
  let mut okA = true // E∘C = id_V
  let mut okB = true // C∘E = id_{𝔽ⁿ}
  let mut okC = true // C 為線性
  let okD = s.basis.length() == n // 基底長度 = dim
  for _t in 0..<trials {
    let v = (s.sample)(rng)
    let w = (s.sample)(rng)
    let a = F::s_rand(rng)
    if !(s.veq)((s.expand)((s.coord)(v)), v) {
      okA = false
    }
    let c : Array[F] = Array::makei(n, _ => F::s_rand(rng))
    let cc = (s.coord)((s.expand)(c))
    for i in 0..<n {
      if !F::s_eq(cc[i], c[i]) {
        okB = false
      }
    }
    let lhs = (s.coord)((s.add)((s.smul)(a, v), w))
    let cv = (s.coord)(v)
    let cw = (s.coord)(w)
    for i in 0..<n {
      if !F::s_eq(lhs[i], F::s_add(F::s_mul(a, cv[i]), cw[i])) {
        okC = false
      }
    }
  }
  // 基底向量之座標須為標準基 eᵢ
  let mut okE = true
  for i in 0..<s.basis.length() {
    let ci = (s.coord)(s.basis[i])
    for j in 0..<n {
      let expect = if i == j { F::s_one() } else { F::s_zero() }
      if !F::s_eq(ci[j], expect) {
        okE = false
      }
    }
  }
  res.push(mk_check("B1 E∘C = id_V", okA, trials, "展開∘座標 = 恆等"))
  res.push(
    mk_check("B2 C∘E = id_𝔽ⁿ", okB, trials, "座標∘展開 = 恆等"),
  )
  res.push(
    mk_check("B3 座標映射線性", okC, trials, "C(αv+w)=αC(v)+C(w)"),
  )
  res.push(
    mk_check("B4 #basis = dim", okD, 1, "基底長度 = " + n.to_string()),
  )
  res.push(mk_check("B5 C(bᵢ) = eᵢ", okE, s.basis.length(), "基底自洽"))
  res
}

// ---------------------------------------------------------------------------
// 【演算法 010】內積公理檢驗器（I1–I5 + 推論 I6–I7）
// ---------------------------------------------------------------------------

///|
/// 檢驗內積五條公理與兩條推論。
pub fn[V, F : Scalar] check_inner_axioms(
  s : IPSpace[V, F],
  rng : Rng,
  trials : Int,
) -> Array[Check] {
  let vs = s.vs
  let res : Array[Check] = []
  let mut ok1 = true
  let mut ok2 = true
  let mut ok3 = true
  let mut ok4 = true
  let mut ok5 = true
  let mut ok6 = true
  let mut ok7 = true
  for _t in 0..<trials {
    let x = (vs.sample)(rng)
    let y = (vs.sample)(rng)
    let z = (vs.sample)(rng)
    let a = F::s_rand(rng)
    // I1 第一變數可加
    if !F::s_eq(
        (s.inner)((vs.add)(x, y), z),
        F::s_add((s.inner)(x, z), (s.inner)(y, z)),
      ) {
      ok1 = false
    }
    // I2 第一變數齊次
    if !F::s_eq((s.inner)((vs.smul)(a, x), y), F::s_mul(a, (s.inner)(x, y))) {
      ok2 = false
    }
    // I3 Hermitian 對稱
    if !F::s_eq((s.inner)(y, x), F::s_conj((s.inner)(x, y))) {
      ok3 = false
    }
    // I4 ⟨x,x⟩ 實且非負
    let q = (s.inner)(x, x)
    if !sis_nonneg(q) {
      ok4 = false
    }
    // I5 正定：⟨x,x⟩ = 0 ⟺ x = 0
    let zero_q = F::s_is_zero(q)
    let zero_v = (vs.veq)(x, vs.zero)
    if zero_q != zero_v {
      ok5 = false
    }
    // I6 第二變數可加（推論）
    if !F::s_eq(
        (s.inner)(x, (vs.add)(y, z)),
        F::s_add((s.inner)(x, y), (s.inner)(x, z)),
      ) {
      ok6 = false
    }
    // I7 第二變數共軛齊次（推論）
    if !F::s_eq(
        (s.inner)(x, (vs.smul)(a, y)),
        F::s_mul(F::s_conj(a), (s.inner)(x, y)),
      ) {
      ok7 = false
    }
  }
  // ⟨0,0⟩ = 0 之特例
  let okz = F::s_is_zero((s.inner)(vs.zero, vs.zero))
  res.push(
    mk_check(
      "I1 第一變數可加", ok1, trials, "⟨x+y,z⟩=⟨x,z⟩+⟨y,z⟩",
    ),
  )
  res.push(
    mk_check("I2 第一變數齊次", ok2, trials, "⟨αx,y⟩=α⟨x,y⟩"),
  )
  res.push(
    mk_check("I3 Hermitian 對稱", ok3, trials, "⟨y,x⟩=‾⟨x,y⟩"),
  )
  res.push(mk_check("I4 ⟨x,x⟩ 非負實", ok4, trials, "正性錐"))
  res.push(mk_check("I5 正定", ok5 && okz, trials, "⟨x,x⟩=0 ⟺ x=0"))
  res.push(mk_check("I6 第二變數可加", ok6, trials, "由 I1,I3 導出"))
  res.push(
    mk_check("I7 第二變數共軛齊次", ok7, trials, "由 I2,I3 導出"),
  )
  res
}

///| （隔離標記）本函式全專案未被呼叫，但依賴本套件私有內部，故留在原處。

///|
/// d(x,y) = ‖x−y‖
pub fn[V, F : Scalar] ip_dist(s : IPSpace[V, F], x : V, y : V) -> Double {
  ip_norm(s, vsub(s.vs, x, y))
}

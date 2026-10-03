// ============================================================================
//  檔案 10：quatspace.mbt — 四元數代數 ℍ 與 ℍⁿ 作為實內積空間
//    S16 ℍⁿ（dim_ℝ = 4n），⟨p,q⟩ = Σᵢ Re(‾pᵢ qᵢ)
// ============================================================================
//
// 【定義 H】ℍ ≔ {w + xi + yj + zk : w,x,y,z ∈ ℝ}，乘法由
//   i² = j² = k² = ijk = −1 生成（Hamilton 關係），為 4 維實結合可除代數。
// 【命題 H1】ℍ 非交換（ij = k 而 ji = −k），但結合。
// 【命題 H2】‾(pq) = ‾q·‾p（反自同構）。
// 【命題 H3】N(q) = q‾q = w²+x²+y²+z² ∈ ℝ≥0 為乘性範數：N(pq) = N(p)N(q)。
//   推論（Euler 四平方恆等式）：兩個四平方和之積仍為四平方和。
// 【命題 H4】⟨p,q⟩ ≔ Re(‾p q) 為 ℝ⁴ 上之標準歐氏內積；
//   ℍ 上左乘 L_q 滿足 ‖qv‖ = ‖q‖‖v‖，故 |q| = 1 時 L_q ∈ O(4)。
// 【定理 H5】（Euler–Rodrigues / 雙重覆蓋 Spin(3) → SO(3)）
//   單位四元數 q 之共軛作用 v ↦ q v ‾q 限制於純虛四元數 ≅ ℝ³ 上
//   給出旋轉 R(q) ∈ SO(3)，且 R(q₁q₂) = R(q₁)R(q₂)、R(−q) = R(q)。
// 【命題 H6】ℍ ≅ {[[α, β], [−‾β, ‾α]] : α,β ∈ ℂ} ⊂ M₂(ℂ)（代數同構）。
// ============================================================================

///|
/// 四元數 w + xi + yj + zk
pub struct Quat[F] {
  qw : F
  qx : F
  qy : F
  qz : F
}

///|
pub fn[F] Quat::mk(w : F, x : F, y : F, z : F) -> Quat[F] {
  { qw: w, qx: x, qy: y, qz: z, }
}

///|
pub fn[F : Scalar] Quat::qzero() -> Quat[F] {
  { qw: F::s_zero(), qx: F::s_zero(), qy: F::s_zero(), qz: F::s_zero(), }
}

///|
pub fn[F : Scalar] Quat::qone() -> Quat[F] {
  { qw: F::s_one(), qx: F::s_zero(), qy: F::s_zero(), qz: F::s_zero(), }
}

///|
pub fn[F : Scalar] Quat::qi() -> Quat[F] {
  { qw: F::s_zero(), qx: F::s_one(), qy: F::s_zero(), qz: F::s_zero(), }
}

///|
pub fn[F : Scalar] Quat::qj() -> Quat[F] {
  { qw: F::s_zero(), qx: F::s_zero(), qy: F::s_one(), qz: F::s_zero(), }
}

///|
pub fn[F : Scalar] Quat::qk() -> Quat[F] {
  { qw: F::s_zero(), qx: F::s_zero(), qy: F::s_zero(), qz: F::s_one(), }
}

///|
pub fn[F : Scalar] Quat::qadd(self : Quat[F], o : Quat[F]) -> Quat[F] {
  {
    qw: F::s_add(self.qw, o.qw),
    qx: F::s_add(self.qx, o.qx),
    qy: F::s_add(self.qy, o.qy),
    qz: F::s_add(self.qz, o.qz),
  }
}

///|
pub fn[F : Scalar] Quat::qneg(self : Quat[F]) -> Quat[F] {
  {
    qw: F::s_neg(self.qw),
    qx: F::s_neg(self.qx),
    qy: F::s_neg(self.qy),
    qz: F::s_neg(self.qz),
  }
}

///|
pub fn[F : Scalar] Quat::qsub(self : Quat[F], o : Quat[F]) -> Quat[F] {
  self.qadd(o.qneg())
}

///|
/// 實純量乘 c·q
pub fn[F : Scalar] Quat::qsmul(self : Quat[F], c : F) -> Quat[F] {
  {
    qw: F::s_mul(c, self.qw),
    qx: F::s_mul(c, self.qx),
    qy: F::s_mul(c, self.qy),
    qz: F::s_mul(c, self.qz),
  }
}

// ---------------------------------------------------------------------------
// 【演算法 045】Hamilton 乘積
//   (w₁,v₁)(w₂,v₂) = (w₁w₂ − v₁·v₂,  w₁v₂ + w₂v₁ + v₁×v₂)
// ---------------------------------------------------------------------------

///|
pub fn[F : Scalar] Quat::qmul(self : Quat[F], o : Quat[F]) -> Quat[F] {
  let a = self
  let b = o
  {
    qw: ssub(
      ssub(
        ssub(F::s_mul(a.qw, b.qw), F::s_mul(a.qx, b.qx)),
        F::s_mul(a.qy, b.qy),
      ),
      F::s_mul(a.qz, b.qz),
    ),
    qx: F::s_add(
      ssub(
        F::s_add(F::s_mul(a.qw, b.qx), F::s_mul(a.qx, b.qw)),
        F::s_mul(a.qz, b.qy),
      ),
      F::s_mul(a.qy, b.qz),
    ),
    qy: F::s_add(
      ssub(
        F::s_add(F::s_mul(a.qw, b.qy), F::s_mul(a.qy, b.qw)),
        F::s_mul(a.qx, b.qz),
      ),
      F::s_mul(a.qz, b.qx),
    ),
    qz: F::s_add(
      ssub(
        F::s_add(F::s_mul(a.qw, b.qz), F::s_mul(a.qz, b.qw)),
        F::s_mul(a.qy, b.qx),
      ),
      F::s_mul(a.qx, b.qy),
    ),
  }
}

///|
/// ‾q = w − xi − yj − zk
pub fn[F : Scalar] Quat::qconj(self : Quat[F]) -> Quat[F] {
  {
    qw: self.qw,
    qx: F::s_neg(self.qx),
    qy: F::s_neg(self.qy),
    qz: F::s_neg(self.qz),
  }
}

///|
/// N(q) = w²+x²+y²+z²
pub fn[F : Scalar] Quat::qnorm2(self : Quat[F]) -> F {
  F::s_add(
    F::s_add(F::s_mul(self.qw, self.qw), F::s_mul(self.qx, self.qx)),
    F::s_add(F::s_mul(self.qy, self.qy), F::s_mul(self.qz, self.qz)),
  )
}

///|
/// q⁻¹ = ‾q/N(q)
pub fn[F : Scalar] Quat::qinv(self : Quat[F]) -> Quat[F]? {
  match F::s_inv(self.qnorm2()) {
    None => None
    Some(ni) => Some(self.qconj().qsmul(ni))
  }
}

///|
/// 實內積 ⟨p,q⟩ = Re(‾p q) = w₁w₂+x₁x₂+y₁y₂+z₁z₂
pub fn[F : Scalar] Quat::qdot(self : Quat[F], o : Quat[F]) -> F {
  F::s_add(
    F::s_add(F::s_mul(self.qw, o.qw), F::s_mul(self.qx, o.qx)),
    F::s_add(F::s_mul(self.qy, o.qy), F::s_mul(self.qz, o.qz)),
  )
}

///|
pub fn[F : Scalar] Quat::qeq(self : Quat[F], o : Quat[F]) -> Bool {
  F::s_eq(self.qw, o.qw) &&
  F::s_eq(self.qx, o.qx) &&
  F::s_eq(self.qy, o.qy) &&
  F::s_eq(self.qz, o.qz)
}

///|
pub fn[F : Scalar] Quat::text(self : Quat[F]) -> String {
  F::s_text(self.qw) +
  "+" +
  F::s_text(self.qx) +
  "i+" +
  F::s_text(self.qy) +
  "j+" +
  F::s_text(self.qz) +
  "k"
}

// ---------------------------------------------------------------------------
// 【演算法 046】左乘矩陣 L_q（ℍ ≅ ℝ⁴ 上之線性算子）
// 命題 046：L_{pq} = L_p L_q；L_q ᵀ L_q = N(q) I₄；det L_q = N(q)²。
// ---------------------------------------------------------------------------

///|
pub fn[F : Scalar] quat_left_matrix(q : Quat[F]) -> Mat[F] {
  let w = q.qw
  let x = q.qx
  let y = q.qy
  let z = q.qz
  let nw = F::s_neg(w)
  let nx = F::s_neg(x)
  let ny = F::s_neg(y)
  let nz = F::s_neg(z)
  ignore(nw)
  Mat::of_rows([[w, nx, ny, nz], [x, w, nz, y], [y, z, w, nx], [z, ny, x, w]])
}

// ---------------------------------------------------------------------------
// 【演算法 047】單位四元數 → SO(3) 旋轉矩陣（Euler–Rodrigues）
// ---------------------------------------------------------------------------

///|
pub fn[F : Scalar] quat_to_rot3(q : Quat[F]) -> Mat[F] {
  let two = F::s_from_int(2)
  let w = q.qw
  let x = q.qx
  let y = q.qy
  let z = q.qz
  let one = F::s_one()
  let xx = F::s_mul(x, x)
  let yy = F::s_mul(y, y)
  let zz = F::s_mul(z, z)
  let xy = F::s_mul(x, y)
  let xz = F::s_mul(x, z)
  let yz = F::s_mul(y, z)
  let wx = F::s_mul(w, x)
  let wy = F::s_mul(w, y)
  let wz = F::s_mul(w, z)
  Mat::of_rows([
    [
      ssub(one, F::s_mul(two, F::s_add(yy, zz))),
      F::s_mul(two, ssub(xy, wz)),
      F::s_mul(two, F::s_add(xz, wy)),
    ],
    [
      F::s_mul(two, F::s_add(xy, wz)),
      ssub(one, F::s_mul(two, F::s_add(xx, zz))),
      F::s_mul(two, ssub(yz, wx)),
    ],
    [
      F::s_mul(two, ssub(xz, wy)),
      F::s_mul(two, F::s_add(yz, wx)),
      ssub(one, F::s_mul(two, F::s_add(xx, yy))),
    ],
  ])
}

// ---------------------------------------------------------------------------
// 【演算法 048】ℍ → M₂(ℂ) 之代數嵌入
//   q = w+xi+yj+zk ↦ [[w+xi, y+zi], [−y+zi, w−xi]]
// 命題 048：此映射保加法、保乘法、保 1，且 det = N(q)（故為單射）。
// ---------------------------------------------------------------------------

///|
pub fn[F : Scalar] quat_to_c2(q : Quat[F]) -> Mat[Cpx[F]] {
  let a : Cpx[F] = Cpx::mk(q.qw, q.qx)
  let b : Cpx[F] = Cpx::mk(q.qy, q.qz)
  let nb : Cpx[F] = Cpx::mk(F::s_neg(q.qy), q.qz)
  let ac : Cpx[F] = Cpx::mk(q.qw, F::s_neg(q.qx))
  Mat::of_rows([[a, b], [nb, ac]])
}

// ---------------------------------------------------------------------------
//  【空間 S16】ℍⁿ 作為 4n 維實內積空間
// ---------------------------------------------------------------------------

///|
/// ℍⁿ，⟨p,q⟩ = Σᵢ Re(‾pᵢ qᵢ)（實內積；純量體為 F，非 ℍ）
pub fn[F : Scalar] quaternion_space(n : Int) -> IPSpace[Array[Quat[F]], F] {
  let d = 4 * n
  let zero : Array[Quat[F]] = Array::makei(n, _ => Quat::qzero())
  let basis : Array[Array[Quat[F]]] = Array::makei(d, k => {
    let i = k / 4
    let c = k % 4
    Array::makei(n, t => {
      if t != i {
        Quat::qzero()
      } else if c == 0 {
        Quat::qone()
      } else if c == 1 {
        Quat::qi()
      } else if c == 2 {
        Quat::qj()
      } else {
        Quat::qk()
      }
    })
  })
  let coord_f = (v : Array[Quat[F]]) => {
    Array::makei(d, k => {
      let i = k / 4
      let c = k % 4
      if c == 0 {
        v[i].qw
      } else if c == 1 {
        v[i].qx
      } else if c == 2 {
        v[i].qy
      } else {
        v[i].qz
      }
    })
  }
  let expand_f = (c : Array[F]) => {
    Array::makei(n, i => {
      Quat::mk(c[4 * i], c[4 * i + 1], c[4 * i + 2], c[4 * i + 3])
    })
  }
  let vs : VSpace[Array[Quat[F]], F] = {
    vname: "ℍ^" +
    n.to_string() +
    "（" +
    F::s_name() +
    "‑內積空間，dim = " +
    d.to_string() +
    "）",
    dim: d,
    zero,
    add: (a, b) => Array::makei(n, i => a[i].qadd(b[i])),
    neg: a => Array::makei(n, i => a[i].qneg()),
    smul: (c, a) => Array::makei(n, i => a[i].qsmul(c)),
    veq: (a, b) => {
      for i in 0..<n {
        if !a[i].qeq(b[i]) {
          return false
        }
      }
      true
    },
    basis,
    coord: v => coord_f(v),
    expand: c => expand_f(c),
    vshow: v => {
      let mut s = "("
      for i in 0..<n {
        s = s + v[i].text()
        if i + 1 < n {
          s = s + "; "
        }
      }
      s + ")"
    },
    sample: rng => expand_f(Array::makei(d, _ => F::s_rand(rng))),
  }
  {
    vs,
    ipname: "⟨p,q⟩ = Σᵢ Re(‾pᵢ qᵢ)",
    inner: (a, b) => {
      let mut acc = F::s_zero()
      for i in 0..<n {
        acc = F::s_add(acc, a[i].qdot(b[i]))
      }
      acc
    },
  }
}

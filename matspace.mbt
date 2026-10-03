// ============================================================================
//  檔案 07：matspace.mbt — 矩陣類內積空間
//    S5  全矩陣空間 M_{m×n}(𝔽)        dim = mn
//    S6  對稱矩陣空間 Sym_n(𝔽)         dim = n(n+1)/2
//    S7  反對稱矩陣空間 Skew_n(𝔽)      dim = n(n−1)/2
//    S8  對角矩陣空間 Diag_n(𝔽)        dim = n
//    S9  複 Hermitian 空間 Herm_n(ℂ)   作為「實」內積空間，dim_ℝ = n²
//    S10 跡零子空間 sl_n(𝔽)            dim = n²−1
//
// 【定義 HS】（Hilbert–Schmidt / Frobenius 內積）⟨A,B⟩ ≔ tr(B*A) = Σ_{ij} a_{ij}‾b_{ij}。
// 【命題 HS1】此為內積：I1,I2 顯然；I3 tr(A*B) = ‾tr(B*A)；
//   I4/I5 ⟨A,A⟩ = Σ|a_{ij}|² ≥ 0，等號 ⟺ A = 0。∎
// 【命題 HS2】⟨AX,Y⟩ = ⟨X,A*Y⟩，即左乘算子 L_A 之伴隨為 L_{A*}；
//   並有 ⟨UAV, UBV⟩ = ⟨A,B⟩（U,V 么正）⇒ Frobenius 內積為么正不變量。
// 【命題 HS3】Sym_n ⊥ Skew_n 且 M_n = Sym_n ⊕ Skew_n（char ≠ 2）：
//   A = (A+Aᵀ)/2 + (A−Aᵀ)/2，且 ⟨S,K⟩ = tr(KᵀS) = −tr(KS) = ... = 0。
// 【命題 HS4】Herm_n(ℂ) 不是 ℂ‑向量空間（iA 反 Hermitian），但為 n² 維
//   ℝ‑向量空間，⟨A,B⟩_ℝ = Re tr(AB*) 為其實內積。
// ============================================================================

///|
/// 【空間 S5】全矩陣空間 M_{m×n}(𝔽)，Frobenius 內積。
pub fn[F : Scalar] matrix_space(m : Int, n : Int) -> IPSpace[Mat[F], F] {
  let d = m * n
  let basis : Array[Mat[F]] = Array::makei(d, k => {
    Mat::build(m, n, (i, j) => {
      if i * n + j == k {
        F::s_one()
      } else {
        F::s_zero()
      }
    })
  })
  let vs : VSpace[Mat[F], F] = {
    vname: "M_{" +
    m.to_string() +
    "×" +
    n.to_string() +
    "}(" +
    F::s_name() +
    ")",
    dim: d,
    zero: Mat::zeros(m, n),
    add: (a, b) => a.plus(b),
    neg: a => a.negm(),
    smul: (c, a) => a.scale(c),
    veq: (a, b) => a.equals(b),
    basis,
    coord: a => a.data.copy(),
    expand: c => Mat::build(m, n, (i, j) => c[i * n + j]),
    vshow: a => a.text(),
    sample: rng => Mat::build(m, n, (_i, _j) => F::s_rand(rng)),
  }
  {
    vs,
    ipname: "⟨A,B⟩ = tr(B*A) = Σ a_ij ‾b_ij",
    inner: (a, b) => {
      let mut acc = F::s_zero()
      for k in 0..<d {
        acc = F::s_add(acc, F::s_mul(a.data[k], F::s_conj(b.data[k])))
      }
      acc
    },
  }
}

///|
/// 對稱矩陣之基底索引：(i,j) with i ≤ j，順序 (0,0),(0,1),…,(0,n−1),(1,1),…
fn sym_pairs(n : Int) -> Array[(Int, Int)] {
  let out : Array[(Int, Int)] = []
  for i in 0..<n {
    for j in i..<n {
      out.push((i, j))
    }
  }
  out
}

///|
/// 【空間 S6】對稱矩陣空間 Sym_n(𝔽) = {A : Aᵀ = A}，dim = n(n+1)/2，
/// 基底 {E_ii} ∪ {E_ij + E_ji : i<j}，Frobenius 內積。
pub fn[F : Scalar] sym_matrix_space(n : Int) -> IPSpace[Mat[F], F] {
  let pairs = sym_pairs(n)
  let d = pairs.length()
  let basis : Array[Mat[F]] = Array::makei(d, k => {
    let (i, j) = pairs[k]
    Mat::build(n, n, (r, c) => {
      if (r == i && c == j) || (r == j && c == i) {
        F::s_one()
      } else {
        F::s_zero()
      }
    })
  })
  let vs : VSpace[Mat[F], F] = {
    vname: "Sym_" + n.to_string() + "(" + F::s_name() + ")",
    dim: d,
    zero: Mat::zeros(n, n),
    add: (a, b) => a.plus(b),
    neg: a => a.negm(),
    smul: (c, a) => a.scale(c),
    veq: (a, b) => a.equals(b),
    basis,
    coord: a => {
      Array::makei(d, k => {
        let (i, j) = pairs[k]
        a.at(i, j)
      })
    },
    expand: c => {
      let m : Mat[F] = Mat::zeros(n, n)
      for k in 0..<d {
        let (i, j) = pairs[k]
        m.put(i, j, c[k])
        m.put(j, i, c[k])
      }
      m
    },
    vshow: a => a.text(),
    sample: rng => {
      let m : Mat[F] = Mat::zeros(n, n)
      for p in pairs {
        let (i, j) = p
        let v = F::s_rand(rng)
        m.put(i, j, v)
        m.put(j, i, v)
      }
      m
    },
  }
  {
    vs,
    ipname: "⟨A,B⟩ = tr(BᵀA)",
    inner: (a, b) => {
      let mut acc = F::s_zero()
      for k in 0..<a.data.length() {
        acc = F::s_add(acc, F::s_mul(a.data[k], F::s_conj(b.data[k])))
      }
      acc
    },
  }
}

///|
/// 【空間 S7】反對稱矩陣空間 Skew_n(𝔽)，dim = n(n−1)/2，
/// 基底 {E_ij − E_ji : i<j}（= Lie 代數 so(n)）。
pub fn[F : Scalar] skew_matrix_space(n : Int) -> IPSpace[Mat[F], F] {
  let pairs : Array[(Int, Int)] = []
  for i in 0..<n {
    for j in (i + 1)..<n {
      pairs.push((i, j))
    }
  }
  let d = pairs.length()
  let basis : Array[Mat[F]] = Array::makei(d, k => {
    let (i, j) = pairs[k]
    Mat::build(n, n, (r, c) => {
      if r == i && c == j {
        F::s_one()
      } else if r == j && c == i {
        F::s_neg(F::s_one())
      } else {
        F::s_zero()
      }
    })
  })
  let vs : VSpace[Mat[F], F] = {
    vname: "Skew_" + n.to_string() + " = so(" + n.to_string() + ")",
    dim: d,
    zero: Mat::zeros(n, n),
    add: (a, b) => a.plus(b),
    neg: a => a.negm(),
    smul: (c, a) => a.scale(c),
    veq: (a, b) => a.equals(b),
    basis,
    coord: a => {
      Array::makei(d, k => {
        let (i, j) = pairs[k]
        a.at(i, j)
      })
    },
    expand: c => {
      let m : Mat[F] = Mat::zeros(n, n)
      for k in 0..<d {
        let (i, j) = pairs[k]
        m.put(i, j, c[k])
        m.put(j, i, F::s_neg(c[k]))
      }
      m
    },
    vshow: a => a.text(),
    sample: rng => {
      let m : Mat[F] = Mat::zeros(n, n)
      for p in pairs {
        let (i, j) = p
        let v = F::s_rand(rng)
        m.put(i, j, v)
        m.put(j, i, F::s_neg(v))
      }
      m
    },
  }
  {
    vs,
    ipname: "⟨A,B⟩ = tr(BᵀA)",
    inner: (a, b) => {
      let mut acc = F::s_zero()
      for k in 0..<a.data.length() {
        acc = F::s_add(acc, F::s_mul(a.data[k], F::s_conj(b.data[k])))
      }
      acc
    },
  }
}

///|
/// 【空間 S8】對角矩陣空間 Diag_n(𝔽) ≅ 𝔽ⁿ（交換代數），dim = n。
pub fn[F : Scalar] diag_matrix_space(n : Int) -> IPSpace[Mat[F], F] {
  let basis : Array[Mat[F]] = Array::makei(n, k => {
    Mat::build(n, n, (i, j) => {
      if i == j && i == k {
        F::s_one()
      } else {
        F::s_zero()
      }
    })
  })
  let vs : VSpace[Mat[F], F] = {
    vname: "Diag_" + n.to_string() + "(" + F::s_name() + ")",
    dim: n,
    zero: Mat::zeros(n, n),
    add: (a, b) => a.plus(b),
    neg: a => a.negm(),
    smul: (c, a) => a.scale(c),
    veq: (a, b) => a.equals(b),
    basis,
    coord: a => Array::makei(n, i => a.at(i, i)),
    expand: c => Mat::diagm(c),
    vshow: a => "diag" + arr_text(Array::makei(n, i => a.at(i, i))),
    sample: rng => Mat::diagm(Array::makei(n, _ => F::s_rand(rng))),
  }
  {
    vs,
    ipname: "⟨A,B⟩ = Σ aᵢᵢ‾bᵢᵢ",
    inner: (a, b) => {
      let mut acc = F::s_zero()
      for i in 0..<n {
        acc = F::s_add(acc, F::s_mul(a.at(i, i), F::s_conj(b.at(i, i))))
      }
      acc
    },
  }
}

///|
/// 【空間 S10】跡零矩陣 sl_n(𝔽) = {A : tr A = 0}，dim = n²−1（Lie 代數）。
pub fn[F : Scalar] traceless_space(n : Int) -> IPSpace[Mat[F], F] {
  // 基底：所有 E_ij (i≠j) 與 E_ii − E_{i+1,i+1} (i < n−1)
  let basis : Array[Mat[F]] = []
  let idx : Array[(Int, Int)] = []
  for i in 0..<n {
    for j in 0..<n {
      if i != j {
        basis.push(
          Mat::build(n, n, (r, c) => {
            if r == i && c == j {
              F::s_one()
            } else {
              F::s_zero()
            }
          }),
        )
        idx.push((i, j))
      }
    }
  }
  for i in 0..<(n - 1) {
    basis.push(
      Mat::build(n, n, (r, c) => {
        if r == c && r == i {
          F::s_one()
        } else if r == c && r == i + 1 {
          F::s_neg(F::s_one())
        } else {
          F::s_zero()
        }
      }),
    )
  }
  let d = basis.length()
  let off = idx.length()
  let vs : VSpace[Mat[F], F] = {
    vname: "sl_" + n.to_string() + "(" + F::s_name() + ")（跡零）",
    dim: d,
    zero: Mat::zeros(n, n),
    add: (a, b) => a.plus(b),
    neg: a => a.negm(),
    smul: (c, a) => a.scale(c),
    veq: (a, b) => a.equals(b),
    basis,
    coord: a => {
      Array::makei(d, k => {
        if k < off {
          let (i, j) = idx[k]
          a.at(i, j)
        } else {
          // 對角部分：c_i = Σ_{t ≤ i} a_tt（由 tr A = 0 可解出）
          let i = k - off
          let mut acc = F::s_zero()
          for t in 0..<(i + 1) {
            acc = F::s_add(acc, a.at(t, t))
          }
          acc
        }
      })
    },
    expand: c => {
      let m : Mat[F] = Mat::zeros(n, n)
      for k in 0..<off {
        let (i, j) = idx[k]
        m.put(i, j, c[k])
      }
      for i in 0..<(n - 1) {
        let v = c[off + i]
        m.put(i, i, F::s_add(m.at(i, i), v))
        m.put(i + 1, i + 1, ssub(m.at(i + 1, i + 1), v))
      }
      m
    },
    vshow: a => a.text(),
    sample: rng => {
      let m : Mat[F] = Mat::zeros(n, n)
      for k in 0..<off {
        let (i, j) = idx[k]
        m.put(i, j, F::s_rand(rng))
      }
      let mut s = F::s_zero()
      for i in 0..<(n - 1) {
        let v = F::s_rand(rng)
        m.put(i, i, v)
        s = F::s_add(s, v)
      }
      m.put(n - 1, n - 1, F::s_neg(s))
      m
    },
  }
  {
    vs,
    ipname: "⟨A,B⟩ = tr(B*A)",
    inner: (a, b) => {
      let mut acc = F::s_zero()
      for k in 0..<a.data.length() {
        acc = F::s_add(acc, F::s_mul(a.data[k], F::s_conj(b.data[k])))
      }
      acc
    },
  }
}

// ---------------------------------------------------------------------------
//  S9：複 Hermitian 矩陣空間（實內積空間）
// ---------------------------------------------------------------------------

///|
/// 【空間 S9】Herm_n(ℂ) = {A ∈ M_n(ℂ) : A* = A}，視為 ℝ‑（或 ℚ‑）向量空間。
/// 基底：{E_ii} ∪ {E_ij+E_ji}_{i<j} ∪ {i(E_ij−E_ji)}_{i<j}，dim_ℝ = n²。
/// 實內積：⟨A,B⟩ = Re tr(AB*) = Σ_{i,j} (Re a_ij Re b_ij + Im a_ij Im b_ij)。
/// 命題 S9：此內積正定；且 ⟨A,A⟩ = Σ|a_ij|² = ‖A‖_F²；
///   Herm_n 上之譜定理保證存在么正 U 使 U*AU 為實對角。
pub fn[F : Scalar] herm_matrix_space(n : Int) -> IPSpace[Mat[Cpx[F]], F] {
  let offpairs : Array[(Int, Int)] = []
  for i in 0..<n {
    for j in (i + 1)..<n {
      offpairs.push((i, j))
    }
  }
  let np = offpairs.length()
  let d = n + 2 * np
  let zero_c : Cpx[F] = Cpx::of_real(F::s_zero())
  let one_c : Cpx[F] = Cpx::of_real(F::s_one())
  let i_c : Cpx[F] = Cpx::imag_unit()
  let basis : Array[Mat[Cpx[F]]] = []
  for k in 0..<n {
    basis.push(
      Mat::build(n, n, (r, c) => if r == k && c == k { one_c } else { zero_c }),
    )
  }
  for p in offpairs {
    let (i, j) = p
    basis.push(
      Mat::build(n, n, (r, c) => {
        if (r == i && c == j) || (r == j && c == i) {
          one_c
        } else {
          zero_c
        }
      }),
    )
  }
  for p in offpairs {
    let (i, j) = p
    basis.push(
      Mat::build(n, n, (r, c) => {
        if r == i && c == j {
          i_c
        } else if r == j && c == i {
          Scalar::s_neg(i_c)
        } else {
          zero_c
        }
      }),
    )
  }
  let mk_from_coords = (co : Array[F]) => {
    let m : Mat[Cpx[F]] = Mat::build(n, n, (_r, _c) => zero_c)
    for k in 0..<n {
      m.put(k, k, Cpx::of_real(co[k]))
    }
    for t in 0..<np {
      let (i, j) = offpairs[t]
      let x = co[n + t]
      let y = co[n + np + t]
      m.put(i, j, Cpx::mk(x, y))
      m.put(j, i, Cpx::mk(x, F::s_neg(y)))
    }
    m
  }
  let vs : VSpace[Mat[Cpx[F]], F] = {
    vname: "Herm_" +
    n.to_string() +
    "(ℂ) 作為 " +
    F::s_name() +
    "‑向量空間",
    dim: d,
    zero: Mat::build(n, n, (_r, _c) => zero_c),
    add: (a, b) => a.plus(b),
    neg: a => a.negm(),
    smul: (c, a) => a.scale(Cpx::of_real(c)),
    veq: (a, b) => a.equals(b),
    basis,
    coord: a => {
      Array::makei(d, k => {
        if k < n {
          a.at(k, k).cre
        } else if k < n + np {
          let (i, j) = offpairs[k - n]
          a.at(i, j).cre
        } else {
          let (i, j) = offpairs[k - n - np]
          a.at(i, j).cim
        }
      })
    },
    expand: co => mk_from_coords(co),
    vshow: a => a.text(),
    sample: rng => mk_from_coords(Array::makei(d, _ => F::s_rand(rng))),
  }
  {
    vs,
    ipname: "⟨A,B⟩_ℝ = Re tr(AB*) = Σ (Re a Re b + Im a Im b)",
    inner: (a, b) => {
      let mut acc = F::s_zero()
      for k in 0..<a.data.length() {
        let x = a.data[k]
        let y = b.data[k]
        acc = F::s_add(
          acc,
          F::s_add(F::s_mul(x.cre, y.cre), F::s_mul(x.cim, y.cim)),
        )
      }
      acc
    },
  }
}

///|
/// 白箱煙霧測試：確認已建構之空間滿足公理（精確軌道 ℚ）。
test "空間公理（ℚ 精確軌道）" {
  let rng = Rng::new(20261003UL)
  let spaces : Array[Check] = []
  let e3 : IPSpace[Array[Q], Q] = euclidean_space(3)
  spaces.push(check_all("ℝ³(ℚ)", check_vector_space_axioms(e3.vs, rng, 8)))
  spaces.push(check_all("ℝ³(ℚ) 內積", check_inner_axioms(e3, rng, 8)))
  spaces.push(check_all("ℝ³(ℚ) 基底", check_basis_iso(e3.vs, rng, 5)))
  let fs : IPSpace[Array[Q], Q] = function_space(["a", "b", "c", "d"], [
    Q::of_int(1),
    Q::of_int(2),
    Q::frac(1, 3),
    Q::of_int(5),
  ])
  spaces.push(check_all("函數空間", check_inner_axioms(fs, rng, 8)))
  spaces.push(check_all("函數空間基底", check_basis_iso(fs.vs, rng, 5)))
  let sy : IPSpace[Mat[Q], Q] = sym_matrix_space(3)
  spaces.push(check_all("Sym₃", check_vector_space_axioms(sy.vs, rng, 6)))
  spaces.push(check_all("Sym₃ 內積", check_inner_axioms(sy, rng, 6)))
  spaces.push(check_all("Sym₃ 基底", check_basis_iso(sy.vs, rng, 5)))
  let sk : IPSpace[Mat[Q], Q] = skew_matrix_space(4)
  spaces.push(check_all("Skew₄ 基底", check_basis_iso(sk.vs, rng, 5)))
  let dg : IPSpace[Mat[Q], Q] = diag_matrix_space(4)
  spaces.push(check_all("Diag₄ 內積", check_inner_axioms(dg, rng, 6)))
  let sl : IPSpace[Mat[Q], Q] = traceless_space(3)
  spaces.push(check_all("sl₃ 基底", check_basis_iso(sl.vs, rng, 5)))
  spaces.push(check_all("sl₃ 內積", check_inner_axioms(sl, rng, 6)))
  let hm : IPSpace[Mat[Cpx[Q]], Q] = herm_matrix_space(3)
  spaces.push(
    check_all("Herm₃ 公理", check_vector_space_axioms(hm.vs, rng, 6)),
  )
  spaces.push(check_all("Herm₃ 內積", check_inner_axioms(hm, rng, 6)))
  spaces.push(check_all("Herm₃ 基底", check_basis_iso(hm.vs, rng, 5)))
  let un : IPSpace[Array[Cpx[Q]], Cpx[Q]] = unitary_space(3)
  spaces.push(check_all("ℂ³ 內積", check_inner_axioms(un, rng, 8)))
  let a : Mat[Q] = Mat::of_rows([
    [Q::of_int(1), Q::of_int(2), Q::of_int(3)],
    [Q::of_int(2), Q::of_int(4), Q::of_int(7)],
    [Q::of_int(0), Q::of_int(0), Q::of_int(1)],
  ])
  let cs = column_space(a)
  spaces.push(mk_check("col(A) dim=2", cs.vs.dim == 2, 1, "rank = 2"))
  spaces.push(check_all("col(A) 基底", check_basis_iso(cs.vs, rng, 5)))
  spaces.push(check_all("col(A) 內積", check_inner_axioms(cs, rng, 5)))
  let ks = kernel_space(a)
  spaces.push(mk_check("ker(A) dim=1", ks.vs.dim == 1, 1, "n − rank = 1"))
  let mut bad = ""
  for c in spaces {
    if !c.ok {
      bad = bad + c.cname + " ✗ " + c.detail + "; "
    }
  }
  assert_eq(bad, "")
}

///|
test "矩陣演算法自洽（ℚ）" {
  let a : Mat[Q] = Mat::of_rows([
    [Q::of_int(2), Q::of_int(1), Q::of_int(0)],
    [Q::of_int(1), Q::of_int(3), Q::of_int(1)],
    [Q::of_int(0), Q::of_int(1), Q::of_int(4)],
  ])
  // det 兩法一致
  assert_true(Q::eq(mdet(a), mdet_laplace(a)))
  // A·A⁻¹ = I
  let ai = match minv(a) {
    Some(x) => x
    None => abort("不可逆")
  }
  assert_true(a.times(ai).equals(Mat::ident(3)))
  // adj(A)·A = det(A)·I
  let adj : Mat[Q] = madj(a)
  assert_true(adj.times(a).equals(Mat::ident(3).scale(mdet(a))))
  // Cayley–Hamilton
  let cp = char_poly(a)
  assert_true(mat_poly_eval(cp, a).equals(Mat::zeros(3, 3)))
  // LU: PA = LU
  let lu = mlu(a)
  let p : Mat[Q] = perm_matrix(lu.perm)
  assert_true(p.times(a).equals(lu.lmat.times(lu.umat)))
  // Cramer = msolve
  let b = [Q::of_int(1), Q::of_int(2), Q::of_int(3)]
  let x1 = match cramer(a, b) {
    Some(x) => x
    None => abort("奇異")
  }
  let x2 = msolve(a, b).particular
  assert_true(arr_eq(x1, x2))
  assert_true(arr_eq(a.apply(x1), b))
  // Kronecker 混合積律
  let b2 : Mat[Q] = Mat::of_rows([
    [Q::of_int(0), Q::of_int(1)],
    [Q::of_int(1), Q::of_int(1)],
  ])
  let c2 : Mat[Q] = Mat::of_rows([
    [Q::of_int(2), Q::of_int(0)],
    [Q::of_int(1), Q::of_int(3)],
  ])
  assert_true(
    mkron(b2, c2).times(mkron(c2, b2)).equals(mkron(b2.times(c2), c2.times(b2))),
  )
  // vec(AXB) = (Bᵀ⊗A)vec X
  let x : Mat[Q] = Mat::of_rows([
    [Q::of_int(1), Q::of_int(2)],
    [Q::of_int(3), Q::of_int(4)],
  ])
  let lhs = mvec(b2.times(x).times(c2))
  let rhs = mkron(c2.transpose(), b2).apply(mvec(x))
  assert_true(arr_eq(lhs, rhs))
}

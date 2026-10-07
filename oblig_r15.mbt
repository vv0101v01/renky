///|
/// # 第十五輪義務自證：N-87 / N-88
///
/// N-87 —— 新增 21 個構造子（合計 35 個），35 × 45 = 1,575 格深度普查。
/// N-88 —— 設計文件 §25.6 之五筆欠條（第 1、5 筆併入 N-85）。

///|
/// 【N-87】21 個新構造子與 35 × 45 之深度普查。
pub fn ob_n87() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let sps = space_registry_x()
  let newc = comb21_new()
  let allc = comb35_registry()
  if newc.length() != 21 || allc.length() != 35 {
    ok = false
  }
  // 記號互異 —— 記號是普查格鍵的一部分，碰撞會使指紋失去意義
  let seen : Map[String, Int] = Map([])
  for c in allc {
    seen[c.csym] = seen.get(c.csym).unwrap_or(0) + 1
  }
  if seen.length() != 35 {
    ok = false
  }
  // 深度普查
  let r = c21_scan(rng, 256)
  if r.w5cells != 1575 {
    ok = false
  }
  if r.w5sym != 1575 ||
    r.w5dim != 1575 ||
    r.w5spd != 1575 ||
    r.w5nonzero != 1575 ||
    r.w5cs != 1575 {
    ok = false
  }
  if r.w5rzrun != 1575 || r.w5rz != r.w5rzrun {
    ok = false
  }
  if r.w5dmax != 220 || r.w5dsum != 15873 {
    ok = false
  }
  if r.w5digest != "1575:15873:259595807" {
    ok = false
  }
  // 【命題 C21-2】dim(Λ²V ⊕ S²V) = n² = dim(V⊗V)，逐個空間核對。
  // 兩個**不同的構造子**在每個空間上給出相同維數，不是巧合：
  // 特徵 ≠ 2 時 V⊗V = Λ²V ⊕ S²V。
  let mut ls = 0
  let mut lsn = 0
  for s in sps {
    let n = s.sdim
    let mut dls = 0
    let mut dt2 = 0
    for c in newc {
      if c.csym == "Λ⊕S" {
        dls = (c.cdim)(n)
      }
      if c.csym == "T²" {
        dt2 = (c.cdim)(n)
      }
    }
    lsn = lsn + 1
    if dls == dt2 && dls == n * n {
      ls = ls + 1
    }
  }
  if lsn != 45 || ls != lsn {
    ok = false
  }
  // 【退化防線】凡階數型構造子在 n = 2 時仍須給出 ≥ 1 維。
  // Λ³ 在 n = 2 時 C(2,3) = 0 —— 一個 0 維的「內積空間」會讓下游的
  // 正定判定、Riesz、Cauchy–Schwarz 全部落入未定義分支而靜默通過。
  let mut clampn = 0
  let mut clampok = 0
  for c in newc {
    if c.csym == "Λ³" || c.csym == "Λⁿ⁻²" || c.csym == "Λ²*" {
      for n in 2..<13 {
        clampn = clampn + 1
        if (c.cdim)(n) >= 1 {
          clampok = clampok + 1
        }
      }
    }
  }
  if clampn != 33 || clampok != clampn {
    ok = false
  }
  // 既有 14 構造子之指紋不得因擴表而改變
  let (cells14, _, _, _, _, _, dg14) = comb14_stats()
  if cells14 != 630 || dg14 != "630:4510:665890815" {
    ok = false
  }
  mk_check(
    "N-87 二十一個新構造子與 35 × 45 深度普查",
    ok,
    r.w5inst + lsn + clampn,
    "本庫原有 14 個構造子，本輪再加 21 個（張量族 ⊗W₃／T²／End／W₂⊗，直和族 ⊕W₂／3D／⊕*／⊞W₃，外冪族 Λ³／Λ²*／Λⁿ⁻²，對稱族 S²*／(S²)*／Λ⊕S，子空間族 U¼／U^c／Uodd／U₂，扭曲族 Trev／Tdg／T³），合計 **35 個**，與 45 個註冊空間相乘得 " +
    r.w5cells.to_string() +
    " 格。全部仍是建構子（由空間造空間的自函子），不是非建構子。每格六項、共 " +
    r.w5inst.to_string() +
    " 個實例，全部 1575／1575：Gram 對稱、維數公式（cdim 與 sdim 雙路）、正定（Θ(d³) 整數 Sylvester）、**非退化**、Cauchy–Schwarz、Riesz 表示（解 Gx = b 後驗 xᵀGy = bᵀy，上限 256 故全格皆跑）。最大維數 " +
    r.w5dmax.to_string() +
    "（Λ³[ℍ³]），維數總和 " +
    r.w5dsum.to_string() +
    "，指紋 " +
    r.w5digest +
    "。**非退化那一項不是湊數的**：Λ³ 在 n = 2 時 C(2,3) = 0，而一個 0 維的「內積空間」會讓下游的正定判定、Riesz、Cauchy–Schwarz 全部落入未定義分支而**靜默通過** —— 比算錯更難發現。故凡階數型構造子一律夾到合法範圍（Λ^min(3,n)、Λ^max(1,n−2)），並在維數公式裡如實寫出夾值；夾值之有效性在 n = 2…12 上逐一核對 " +
    clampok.to_string() +
    "／" +
    clampn.to_string() +
    "。另驗命題 C21-2：dim(Λ²V ⊕ S²V) = n² = dim(V⊗V) 在 " +
    ls.to_string() +
    "／" +
    lsn.to_string() +
    " 個空間上成立 —— 兩個不同構造子在每個空間給出相同維數不是巧合，而是特徵 ≠ 2 時 V⊗V = Λ²V ⊕ S²V 的痕跡，本庫把兩者都列為構造子正是為了讓這條分解在普查表上被量到。35 個記號互異（碰撞會使指紋失去意義），既有 14 構造子之指紋 " +
    dg14 +
    " 一位元未變。",
  )
}

///|
/// 【N-88】設計文件 §25.6 之欠條清償。
pub fn ob_n88() -> Check {
  let mut ok = true
  let sps = space_registry_x()
  let rng = ob_rng()
  let c = Cost::new()

  // ---- 第 2 筆：複數軌 ----
  // kron_bilinear 不取共軛，故第十四輪的惰性張量空間只服務 ℚ 軌。
  // 本輪以 Scalar 為界重寫（kron_sesq），ℂ 亦可用。
  let mut cn = 0
  let mut csame = 0
  let mut cdiff = 0
  for m in [2, 3] {
    for k in [2, 3] {
      let p : IPSpace[Array[Cpx[Q]], Cpx[Q]] = unitary_space(m)
      let q : IPSpace[Array[Cpx[Q]], Cpx[Q]] = unitary_space(k)
      let g1 = gram_of_space(p)
      let g2 = gram_of_space(q)
      let slow = tensor_space(p, q)
      let fast = tensor_space_lazy_s(p, q, g1, g2)
      let d = m * k
      cn = cn + 1
      let mut good = slow.vs.dim == fast.vs.dim
      let mut sawdiff = false
      for _t in 0..<6 {
        let x : Array[Cpx[Q]] = Array::makei(d, _ => Cpx::mk(qr(rng), qr(rng)))
        let y : Array[Cpx[Q]] = Array::makei(d, _ => Cpx::mk(qr(rng), qr(rng)))
        let a = (slow.inner)(x, y)
        if !Cpx::s_eq(a, (fast.inner)(x, y)) {
          good = false
        }
        // 兩側對照：不取共軛者在 ℂ 上必須算出**不同的數**
        if !Cpx::s_eq(a, kron_bilinear_s_noconj(g1, g2, x, y)) {
          sawdiff = true
        }
      }
      if good {
        csame = csame + 1
      }
      if sawdiff {
        cdiff = cdiff + 1
      }
    }
  }
  if cn != 4 || csame != cn || cdiff != cn {
    ok = false
  }

  // ---- 第 3 筆：K-1 之兩側對照改用自造的非對稱矩陣 ----
  // 註冊表 45 個 Gram 全部對稱，B ↔ Bᵀ 在那批資料上結構性不可辨。
  // 對照不必用註冊表的矩陣 —— 這一點第十四輪沒想到。
  let mut an = 0
  let mut aok = 0
  let mut acaught = 0
  for m in [2, 3, 4, 5, 6] {
    for _t in 0..<4 {
      an = an + 1
      let aa = Mat::build(m, m, (_, _) => qr(rng))
      let ga = aa.transpose().times(aa).plus(Mat::ident(m).scale(Q::of_int(m)))
      // 刻意非對稱且可逆（上三角，對角為 m+1）
      let bb = Mat::build(m, m, (i, j) => {
        if i == j {
          Q::of_int(m + 1)
        } else if i < j {
          Q::of_int(i + 2)
        } else {
          Q::zero()
        }
      })
      let d = m * m
      let x : Array[Q] = Array::makei(d, _ => qr(rng))
      let y : Array[Q] = Array::makei(d, _ => qr(rng))
      let truth = qbil(mkron(ga, bb), x, y)
      if kron_bilinear(ga, bb, x, y).eq(truth) {
        aok = aok + 1
      }
      if !kron_bilinear(ga, bb.transpose(), x, y).eq(truth) {
        acaught = acaught + 1
      }
    }
  }
  if an != 20 || aok != an || acaught != an {
    ok = false
  }

  // ---- 第 4 筆：免物化的逐元驗證（取代隨機雙線性抽樣）----
  let mut en = 0
  let mut efac = 0
  let mut eidx = 0
  for a in sps {
    for b in sps {
      match (qldlt_gauss(a.sg, c), qldlt_gauss(b.sg, c)) {
        (Some((la, da)), Some((lb, db))) => {
          en = en + 1
          let (okf, oki) = kron_ldlt_elem(a.sg, b.sg, la, lb, da, db)
          if okf {
            efac = efac + 1
          }
          if oki {
            eidx = eidx + 1
          }
        }
        _ => ()
      }
    }
  }
  if en != 2025 || efac != en || eidx != en {
    ok = false
  }
  mk_check(
    "N-88 §25.6 欠條清償：複數軌、對照可辨性、免物化逐元驗證",
    ok,
    cn * 6 + an * 2 + en * 2,
    "設計文件 §25.6 列了五筆欠條。第 1 筆（三元組 Gram 層 9,477／91,125）由使用者裁示**不再跑 45³** —— 連第十四輪加的 45³ 維數層掃描也一併移除（見 N-85）；第 5 筆（三軸完整條件是手寫布林式）改由掃描當場記錄並斷言，亦在 N-85。本條清償其餘三筆。**第 2 筆（複數軌）**：第十四輪的 kron_bilinear 不取共軛，故惰性張量空間只服務 ℚ 軌 —— 而 coord_ipspace 的內積約定是第二變數取共軛，ℚ 的共軛是恆等所以「剛好對」，到了 ℂ 就**算出不同的數**，這不是效能差異。本輪以 Scalar 為界重寫（kron_sesq，共軛顯式出現在式子裡），在 " +
    cn.to_string() +
    " 組 unitary_space(m) ⊗ unitary_space(k) 上與急性版逐樣本相同 " +
    csame.to_string() +
    "；兩側對照（刻意不取共軛者）在 ℂ 上全數算出不同的數 " +
    cdiff.to_string() +
    "／" +
    cn.to_string() +
    " —— 這條對照在 ℚ 軌是恆假的，只有換到 ℂ 才有內容。**第 3 筆（K-1 之對照不可辨）**：註冊表 45 個 Gram 全部對稱，B ↔ Bᵀ 在那批資料上結構性分辨不出來，第十四輪因此照實記為「不宣稱抓到」。本輪的修法不是往註冊表加非對稱空間（那會動到多條指紋），而是**對照根本不必用註冊表的矩陣** —— 自造 " +
    an.to_string() +
    " 組非對稱且可逆的 B，K-1 正確 " +
    aok.to_string() +
    "、錯式全數被抓 " +
    acaught.to_string() +
    "。**第 4 筆（LDL⊗ 只做隨機抽樣）**：抽樣之所以原本難以取代，是因為「逐元驗證」被預設成要先有那個 n_An_B 階矩陣。命題 K-6 說不必 —— [(L_A⊗L_B)(D_A⊗D_B)(L_A⊗L_B)ᵀ][u][v] = (L_AD_AL_Aᵀ)[u_a][v_a]·(L_BD_BL_Bᵀ)[u_b][v_b]，故乘積側逐元成立 ⟺ 兩個因子各自 LDLᵀ = 原矩陣。因子側在全部 " +
    en.to_string() +
    " 對上逐元驗完 " +
    efac.to_string() +
    "，索引分解側（驗實作把 u 拆成 (u/n_B, u%n_B) 的方式與推導一致）每元 O(1) 亦全數驗完 " +
    eidx.to_string() +
    " —— 隨機抽樣由此換成**完整覆蓋**，而且仍不物化任何 n_An_B 階矩陣。",
  )
}

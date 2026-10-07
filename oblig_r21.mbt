///|
/// # 第二十一輪義務自證：N-92（DSL 編譯器）與 N-93…N-107（結構矩陣族）

///|
/// 本輪共用的正定測試矩陣 AᵀA + nI。
fn r21_spd(n : Int, rng : Rng) -> Mat[Q] {
  let b : Mat[Q] = Mat::build(n, n, (_, _) => qr(rng))
  b.transpose().times(b).plus(Mat::ident(n).scale(Q::of_int(n)))
}

///|
/// **非對稱**但可逆的測試矩陣（嚴格對角佔優，故必可逆）。
///
/// ## 為什麼需要這個
///
/// N-97／N-99／N-100 的兩側對照都與**轉置**有關：Schur 補的 B、C 顛倒、
/// Kronecker 解的 B⁻¹ 對 B⁻ᵀ、Sylvester 的 B⊗I 對 Bᵀ⊗I。
/// 若測試矩陣對稱，這三個錯式全都恰好等於正確式 —— 對照變成恆真。
///
/// 本輪第一版正是用 `r21_spd`（對稱）寫的，三條同時「通過得太漂亮」
/// 而被判定失敗（對照一次都沒抓到）。這與第十九輪 N-90 的
/// 「ω₂ = ω₂⁻¹ 所以 2⊗2 分辨不出共軛核」是同一個陷阱，
/// 而本庫已經記過兩次仍再犯一次：**預設的測試資料太對稱**。
fn r21_nonsym(n : Int, rng : Rng) -> Mat[Q] {
  let b : Mat[Q] = Mat::build(n, n, (i, j) => {
    if i == j {
      Q::zero()
    } else {
      qr(rng).add(Q::of_int(i - j))
    }
  })
  Mat::build(n, n, (i, j) => {
    if i == j {
      let mut r = Q::zero()
      for k in 0..<n {
        if k != i {
          r = r.add(b.at(i, k).abs())
        }
      }
      r.add(Q::of_int(i + 2))
    } else {
      b.at(i, j)
    }
  })
}

// ===========================================================================
//  N-92 義務 DSL 之編譯器
// ===========================================================================

///|
/// 【N-92】義務 DSL 之編譯器：詞法、語法、檢查、生成。
pub fn ob_n92() -> Check {
  let mut ok = true
  // (1) 生成相容：DSL 編譯出的規格與手寫規格逐欄相同，
  //     且 gen_oblig_src 之輸出逐位元組相同
  let hand = obl_demo_spec()
  let (specs, errs) = dsl_compile(dsl_law_source())
  if errs.length() != 0 || specs.length() != 1 {
    ok = false
  }
  let mut fieldeq = false
  let mut byteeq = false
  let mut srclen = 0
  if specs.length() == 1 {
    fieldeq = dsl_spec_eq(hand, specs[0])
    match (gen_oblig_src(hand), gen_oblig_src(specs[0])) {
      (Some(a), Some(b)) => {
        byteeq = a == b
        srclen = a.length()
      }
      _ => ok = false
    }
  }
  if !fieldeq || !byteeq {
    ok = false
  }
  // (2) 印出—剖析往返
  let (rt, rterr) = dsl_compile(dsl_print(hand))
  let roundtrip = rterr.length() == 0 &&
    rt.length() == 1 &&
    dsl_spec_eq(hand, rt[0])
  if !roundtrip {
    ok = false
  }
  // (3) 語法補強：註解、欄位亂序、省略 inner、引號值
  let enhanced = "# 井號註解\n" +
    "law N-99 {\n" +
    "  track = Q   // 行尾註解\n" +
    "  rule  = ^\n" +
    "  comb  = ⊗\n" +
    "  outer = det\n" +
    "  zh    = \"一元律：inner 省略\"\n" +
    "  fn    = ob_n99x\n" +
    "}\n"
  let (en, enerr) = dsl_compile(enhanced)
  let synok = enerr.length() == 0 &&
    en.length() == 1 &&
    en[0].oinner == "" &&
    en[0].ocomb == "⊗" &&
    en[0].ozh == "一元律：inner 省略"
  if !synok {
    ok = false
  }
  // (4) 錯誤案例：七類都要被拒絕，且位置落在出錯那一行
  let bad : Array[(String, String, Int)] = [
    ("缺右大括號", "law N-01 {\n  fn = ob_a\n", 1),
    ("缺等號", "law N-01 {\n  fn ob_a\n}\n", 2),
    (
      "未知欄位", "law N-01 {\n  fnx = x\n  fn = ob_a\n  zh = z\n  outer = d\n  comb = c\n  rule = r\n  track = Q\n}\n",
      2,
    ),
    (
      "重複欄位", "law N-01 {\n  fn = ob_a\n  fn = ob_b\n  zh = z\n  outer = d\n  comb = c\n  rule = r\n  track = Q\n}\n",
      3,
    ),
    ("缺必要欄位", "law N-01 {\n  fn = ob_a\n}\n", 1),
    (
      "代號格式錯", "law X-01 {\n  fn = ob_a\n  zh = z\n  outer = d\n  comb = c\n  rule = r\n  track = Q\n}\n",
      1,
    ),
    ("字串未閉合", "law N-01 {\n  zh = \"abc\n}\n", 2),
  ]
  let mut nbad = 0
  let mut caught = 0
  let mut located = 0
  for b in bad {
    nbad = nbad + 1
    let (sp, er) = dsl_compile(b.1)
    if er.length() > 0 && sp.length() == 0 {
      caught = caught + 1
      if er[0].epos.dline == b.2 {
        located = located + 1
      }
    }
  }
  if nbad != 7 || caught != nbad || located != nbad {
    ok = false
  }
  // (5) 正例必須**不**報錯 —— 否則上一項只是「什麼都拒絕」
  let (okspec, okerr) = dsl_compile(dsl_law_source())
  if okerr.length() != 0 || okspec.length() != 1 {
    ok = false
  }
  mk_check(
    "N-92 義務 DSL 之編譯器：詞法、語法、檢查、生成",
    ok,
    4 + nbad + 3,
    "第七輪起本庫有一個「義務 DSL」，但它其實只是一個結構：使用者用 MoonBit 把 `OblSpec` 寫出來，再交給 gen_oblig_src 吐出原始碼。那是一個**生成器**，不是一個**語言** —— 沒有表層語法、沒有詞法、沒有語法錯誤、也沒有錯誤訊息；寫錯欄位名時抱怨的是 MoonBit 的型別，不是 DSL 的拼字。本條把缺的那一半補上：**表層語法 → 詞法 → 語法 → 檢查 → 生成**，五個階段各自可測。文法為 `law <代號> { 欄位 = 值 … }`。**語法補強**（相對於原本的結構寫法）：`//` 與 `#` 兩種註解、欄位任意順序、`inner` 可省略表一元律、值可裸寫或加引號、非 ASCII（⊗ ∘ ℚ 中文）一律視為識別字字元、每個錯誤帶行:列。**生成相容（定理 D-1）**：DSL 編譯出的規格與手寫規格逐欄相同，且 gen_oblig_src 之輸出**逐位元組相同**（" +
    srclen.to_string() +
    " 字元）—— 這是整個編譯器唯一有意義的驗收，它保證換成語言之後 `oblig_auto.mbt` 一個位元都不會變，N-45 釘死的雜湊因此仍然成立。**印出—剖析往返（定理 D-2）**：dsl_parse(dsl_print(spec)) = spec。**而且它已經接在產品路徑上** —— `cmd/genoblig` 現在吃的是 `dsl_law_source()` 這份 DSL 文字，不是手寫結構；編譯器若壞了，往返閘門會當場紅燈。把語言接進產品路徑才算是編譯器，放在旁邊當示範的那叫範例。**命題 D-3（錯誤要被拒絕，而且要說在哪裡）**：缺右大括號、缺等號、未知欄位、重複欄位、缺必要欄位、代號格式錯、字串未閉合共 " +
    nbad.to_string() +
    " 類，全數被拒 " +
    caught.to_string() +
    "，且首個錯誤的行號全部落在出錯那一行 " +
    located.to_string() +
    "。另驗正例不報錯 —— 否則「全都拒絕」也能通過前一項。一個只會接受正確輸入的剖析器不算剖析器；一個什麼都拒絕的也不算。",
  )
}

// ===========================================================================
//  N-93 … N-107 結構矩陣族
// ===========================================================================

///|
/// 【N-93】Toeplitz 矩陣之循環嵌入。
pub fn ob_n93() -> Check {
  let rng = ob_rng()
  let mut n = 0
  let mut same = 0
  let mut caught = 0
  for k in [2, 3, 4, 5, 6, 7] {
    for _t in 0..<4 {
      n = n + 1
      let t : Array[Q] = Array::makei(2 * k - 1, _ => qr(rng))
      let tm : Mat[Q] = toeplitz(t, k)
      let x : Array[Q] = Array::makei(k, _ => qr(rng))
      let d = tm.apply(x)
      let e = toeplitz_mul_via_circ(t, k, x)
      let mut s = true
      for i in 0..<k {
        if !d[i].eq(e[i]) {
          s = false
        }
      }
      if s {
        same = same + 1
      }
      // 對照：不補零（把 x 重複一次）必須算錯
      let c = toeplitz_circ_symbol(t, k)
      let big : Mat[Q] = circ_mat(c)
      let xx : Array[Q] = Array::makei(2 * k, i => x[i % k])
      let y = big.apply(xx)
      let mut diff = false
      for i in 0..<k {
        if !y[i].eq(d[i]) {
          diff = true
        }
      }
      if diff {
        caught = caught + 1
      }
    }
  }
  mk_check(
    "N-93 Toeplitz 矩陣之循環嵌入",
    n == 24 && same == n && caught == n,
    n * 2,
    "Toeplitz T（n 階，由 2n−1 條對角線決定）可嵌入 2n 階循環矩陣 C：取符號 c[k] = t[n−1+k]（k < n）、c[n] = 0、c[k] = t[k−n−1]（k > n），則 C 的左上 n × n 塊恰為 T，故 **T·x = (C·[x;0]) 的前 n 個分量**。在 " +
    n.to_string() +
    " 組（n = 2…7）上逐元相同 " +
    same.to_string() +
    "。用處：循環矩陣可用 FFT 在 Θ(n log n) 內乘向量（N-91），於是 Toeplitz 也可以，而直接法是 Θ(n²)。這是「把結構嵌進一個更大但更規則的結構」這個手法的樣板 —— 代價是階數加倍，收益是換到一個有快速變換的類。**兩側對照**：零填充不是裝飾。把 [x;0] 改成 [x;x]，循環摺疊會把下半段的貢獻繞回前 n 個分量，" +
    caught.to_string() +
    "／" +
    n.to_string() +
    " 全數算錯。",
  )
}

///|
/// 【N-94】Hankel 與 Toeplitz 之反轉對應。
pub fn ob_n94() -> Check {
  let rng = ob_rng()
  let mut n = 0
  let mut same = 0
  let mut caught = 0
  for k in [2, 3, 4, 5, 6] {
    for _t in 0..<4 {
      n = n + 1
      let h : Array[Q] = Array::makei(2 * k - 1, _ => qr(rng))
      let hm : Mat[Q] = hankel(h, k)
      let j : Mat[Q] = rev_perm(k)
      // H·J 為 Toeplitz：(HJ)[i][j] = h[i + (k−1−j)]
      let hj = hm.times(j)
      let t : Array[Q] = Array::makei(2 * k - 1, u => h[u])
      let tm : Mat[Q] = toeplitz(t, k)
      if hj.equals(tm) {
        same = same + 1
      }
      // 對照：左乘 J 而非右乘 —— 得到的是另一個矩陣
      if !j.times(hm).equals(tm) || k == 1 {
        caught = caught + 1
      }
    }
  }
  mk_check(
    "N-94 Hankel 與 Toeplitz 之反轉對應",
    n == 20 && same == n && caught == n,
    n * 2,
    "Hankel H[i][j] = h[i+j]（沿反對角線為常數）與 Toeplitz T[i][j] = t[n−1+i−j]（沿對角線為常數）差一個行反轉：**H·J = T**，其中 J[i][j] = δ_{i,n−1−j}。證明：(HJ)[i][j] = H[i][n−1−j] = h[i+n−1−j] = t[n−1+i−j]。在 " +
    n.to_string() +
    " 組上逐元相同 " +
    same.to_string() +
    "。推論：Hankel 的一切快速演算法都可以由 Toeplitz 的借來 —— 右乘一個置換是 Θ(n²) 的重排，不改變漸進成本。**兩側對照**：**左**乘 J 不行（" +
    caught.to_string() +
    "／" +
    n.to_string() +
    " 全數不等）。J·H 反的是列不是行，得到的是另一個 Hankel 而不是 Toeplitz；兩個置換長得一樣，作用的那一側不同。",
  )
}

///|
/// 【N-95】Sherman–Morrison 秩一更新。
pub fn ob_n95() -> Check {
  let rng = ob_rng()
  let c = Cost::new()
  let mut n = 0
  let mut same = 0
  let mut caught = 0
  for k in [2, 3, 4, 5, 6] {
    for _t in 0..<3 {
      let a = r21_spd(k, rng)
      let u : Array[Q] = Array::makei(k, _ => qr(rng))
      let v : Array[Q] = Array::makei(k, _ => qr(rng))
      match qinv_gauss(a, c) {
        None => ()
        Some(ai) => {
          let upd : Mat[Q] = Mat::build(k, k, (i, j) => {
            a.at(i, j).add(u[i].mul(v[j]))
          })
          match (sherman_morrison(ai, u, v), qinv_gauss(upd, c)) {
            (Some(sm), Some(dir)) => {
              n = n + 1
              if sm.equals(dir) {
                same = same + 1
              }
              // 對照：分母寫成 1 − vᵀA⁻¹u（符號錯）
              let au : Array[Q] = Array::makei(k, i => {
                let mut s = Q::zero()
                for t2 in 0..<k {
                  s = s.add(ai.at(i, t2).mul(u[t2]))
                }
                s
              })
              let va : Array[Q] = Array::makei(k, j => {
                let mut s = Q::zero()
                for t2 in 0..<k {
                  s = s.add(v[t2].mul(ai.at(t2, j)))
                }
                s
              })
              let mut den = Q::one()
              for t2 in 0..<k {
                den = den.sub(v[t2].mul(au[t2]))
              }
              match den.inv() {
                Some(di) => {
                  let bad : Mat[Q] = Mat::build(k, k, (i, j) => {
                    ai.at(i, j).sub(au[i].mul(va[j]).mul(di))
                  })
                  if !bad.equals(dir) {
                    caught = caught + 1
                  }
                }
                None => caught = caught + 1
              }
            }
            _ => ()
          }
        }
      }
    }
  }
  mk_check(
    "N-95 Sherman–Morrison 秩一更新",
    n >= 12 && same == n && caught == n,
    n * 2,
    "(A + uvᵀ)⁻¹ = A⁻¹ − (A⁻¹u)(vᵀA⁻¹)／(1 + vᵀA⁻¹u)。已知 A⁻¹ 時右式只要兩次矩陣向量積與一次外積，**Θ(n²)**；左式重新求逆是 Θ(n³)。在 " +
    n.to_string() +
    " 組上與直接求逆逐元相同 " +
    same.to_string() +
    "。**兩側對照**：分母的符號寫成 1 − vᵀA⁻¹u（這是這條公式最常見的手誤，因為右式的分子帶一個減號），" +
    caught.to_string() +
    "／" +
    n.to_string() +
    " 全數被抓。",
  )
}

///|
/// 【N-96】Woodbury 秩 k 更新。
pub fn ob_n96() -> Check {
  let rng = ob_rng()
  let c = Cost::new()
  let mut n = 0
  let mut same = 0
  let mut caught = 0
  for nk in [(4, 1), (4, 2), (5, 2), (6, 2), (6, 3)] {
    let nn = nk.0
    let kk = nk.1
    for _t in 0..<3 {
      let a = r21_spd(nn, rng)
      let u : Mat[Q] = Mat::build(nn, kk, (_, _) => qr(rng))
      let v : Mat[Q] = Mat::build(nn, kk, (_, _) => qr(rng))
      let cm = r21_spd(kk, rng)
      match (qinv_gauss(a, c), qinv_gauss(cm, c)) {
        (Some(ai), Some(ci)) => {
          let upd = a.plus(u.times(cm).times(v.transpose()))
          match (woodbury(ai, u, ci, v, c), qinv_gauss(upd, c)) {
            (Some(w), Some(dir)) => {
              n = n + 1
              if w.equals(dir) {
                same = same + 1
              }
              // 對照：中間項漏掉 C⁻¹
              match qinv_gauss(v.transpose().times(ai).times(u), c) {
                Some(mi) => {
                  let bad = ai.minus(
                    ai.times(u).times(mi).times(v.transpose().times(ai)),
                  )
                  if !bad.equals(dir) {
                    caught = caught + 1
                  }
                }
                None => caught = caught + 1
              }
            }
            _ => ()
          }
        }
        _ => ()
      }
    }
  }
  mk_check(
    "N-96 Woodbury 秩 k 更新",
    n >= 12 && same == n && caught == n,
    n * 2,
    "(A + UCVᵀ)⁻¹ = A⁻¹ − A⁻¹U(C⁻¹ + VᵀA⁻¹U)⁻¹VᵀA⁻¹。中間只需反一個 **k × k** 矩陣，故 k ≪ n 時由 Θ(n³) 降為 Θ(n²k + k³)；k = 1 時退化為 Sherman–Morrison（N-95）。在 " +
    n.to_string() +
    " 組（n = 4…6、k = 1…3）上與直接求逆逐元相同 " +
    same.to_string() +
    "。**兩側對照**：中間項漏掉 C⁻¹（寫成 (VᵀA⁻¹U)⁻¹），" +
    caught.to_string() +
    "／" +
    n.to_string() +
    " 全數被抓 —— 這一項在 C = I 時恰好消失，所以用單位矩陣當 C 測試是看不出來的；本條的 C 刻意取隨機正定陣。",
  )
}

///|
/// 【N-97】Schur 補與分塊行列式。
pub fn ob_n97() -> Check {
  let rng = ob_rng()
  let mut n = 0
  let mut same = 0
  let mut caught = 0
  for pq in [(1, 2), (2, 2), (2, 3), (3, 3), (3, 2)] {
    let p = pq.0
    let q = pq.1
    for _t in 0..<3 {
      // 非對稱 M —— 對稱時 B = Cᵀ，下面的對照會恆真
      let m = r21_nonsym(p + q, rng)
      let a = submat(m, 0, 0, p, p)
      match schur_complement(m, p) {
        None => ()
        Some(s) => {
          n = n + 1
          // det M = det A · det S
          if mdet(m).eq(mdet(a).mul(mdet(s))) {
            same = same + 1
          }
          // 對照：Schur 補寫成 D − B A⁻¹ C（B、C 顛倒）
          let b = submat(m, 0, p, p, q)
          let cc = submat(m, p, 0, q, p)
          let d = submat(m, p, p, q, q)
          match qinv_gauss(a, Cost::new()) {
            Some(ai) => {
              let bad = d.minus(b.transpose().times(ai).times(cc.transpose()))
              if !mdet(m).eq(mdet(a).mul(mdet(bad))) {
                caught = caught + 1
              }
            }
            None => ()
          }
        }
      }
    }
  }
  mk_check(
    "N-97 Schur 補與分塊行列式",
    n >= 12 && same == n && caught == n,
    n * 2,
    "M = [[A,B],[C,D]]、A 可逆時，Schur 補 S = D − CA⁻¹B 滿足 **det M = det A · det S**（由分塊 LU M = [[I,0],[CA⁻¹,I]]·[[A,0],[0,S]]·[[I,A⁻¹B],[0,I]] 取行列式）。在 " +
    n.to_string() +
    " 組（p、q = 1…3）上成立 " +
    same.to_string() +
    "。成本：det M 直接算是 Θ((p+q)³)；分塊式是 Θ(p³ + p²q + q³)，p、q 懸殊時差距明顯。本條沿用 matrix.mbt 既有的 `schur_complement` —— **既有的就不重寫**。**兩側對照**：把 S 寫成 D − BᵀA⁻¹Cᵀ（B、C 顛倒），行列式恆等式隨即失效 " +
    caught.to_string() +
    "／" +
    n.to_string() +
    "。**測試矩陣刻意取非對稱**：M 對稱時 B = Cᵀ，這個錯式恰好等於正確式，對照會恆真 —— 本條第一版正是這樣寫的，三條相關條目同時「通過得太漂亮」而被判失敗。",
  )
}

///|
/// 【N-98】分塊上三角之求解與行列式。
pub fn ob_n98() -> Check {
  let rng = ob_rng()
  let c = Cost::new()
  let mut n = 0
  let mut same = 0
  let mut dsame = 0
  for pq in [(2, 2), (2, 3), (3, 2), (3, 3), (4, 2)] {
    let p = pq.0
    let q = pq.1
    for _t in 0..<3 {
      let a = r21_spd(p, rng)
      let d = r21_spd(q, rng)
      let b : Mat[Q] = Mat::build(p, q, (_, _) => qr(rng))
      let z : Mat[Q] = Mat::zeros(q, p)
      let m = blocks4(a, b, z, d)
      let f : Array[Q] = Array::makei(p, _ => qr(rng))
      let g : Array[Q] = Array::makei(q, _ => qr(rng))
      let rhs : Array[Q] = Array::makei(p + q, i => {
        if i < p {
          f[i]
        } else {
          g[i - p]
        }
      })
      match (block_upper_solve(a, b, d, f, g, c), qsolve_gauss(m, rhs, c)) {
        (Some(x), Some(y)) => {
          n = n + 1
          let mut s = true
          for i in 0..<(p + q) {
            if !x[i].eq(y[i]) {
              s = false
            }
          }
          if s {
            same = same + 1
          }
          if mdet(m).eq(mdet(a).mul(mdet(d))) {
            dsame = dsame + 1
          }
        }
        _ => ()
      }
    }
  }
  mk_check(
    "N-98 分塊上三角之求解與行列式",
    n >= 12 && same == n && dsame == n,
    n * 2,
    "M = [[A,B],[0,D]] ⇒ **det M = det A · det D**，且 Mx = [f;g] 可由 Dy₂ = g、Ay₁ = f − By₂ 兩步回代解出。在 " +
    n.to_string() +
    " 組上與直接求解逐元相同 " +
    same.to_string() +
    "、行列式恆等 " +
    dsame.to_string() +
    "。成本：Θ(p³ + q³ + pq) 對 Θ((p+q)³) —— p = q 時約省 4 倍。這是 N-97 的特例（C = 0 時 S = D），但值得單列，因為回代這件事是 Schur 補公式看不出來的：分塊三角不必算 A⁻¹，只要解兩個小系統。",
  )
}

///|
/// 【N-99】Kronecker 線性系統之分離求解。
pub fn ob_n99() -> Check {
  let rng = ob_rng()
  let c = Cost::new()
  let mut n = 0
  let mut same = 0
  let mut caught = 0
  let mut cbase : Int64 = 0
  let mut cfast : Int64 = 0
  for mn in [(2, 3), (3, 3), (3, 4), (4, 4), (4, 5)] {
    let m = mn.0
    let k = mn.1
    for _t in 0..<3 {
      let a = r21_spd(m, rng)
      // B 取非對稱 —— 對稱時 B⁻¹ = B⁻ᵀ，下面的轉置對照會恆真
      let b = r21_nonsym(k, rng)
      let rhs : Array[Q] = Array::makei(m * k, _ => qr(rng))
      match (kron_solve(a, b, rhs, c), qsolve_gauss(mkron(a, b), rhs, c)) {
        (Some(x), Some(y)) => {
          n = n + 1
          let mut s = true
          for i in 0..<(m * k) {
            if !x[i].eq(y[i]) {
              s = false
            }
          }
          if s {
            same = same + 1
          }
          cbase = cbase + (m * k * (m * k) * (m * k)).to_int64()
          cfast = cfast + (m * m * m + k * k * k + m * k * (m + k)).to_int64()
          // 對照：忘了轉置（X = A⁻¹ C B⁻¹ 而非 A⁻¹ C B⁻ᵀ）
          match (qinv_gauss(a, c), qinv_gauss(b, c)) {
            (Some(ai), Some(bi)) => {
              let cm : Mat[Q] = Mat::build(m, k, (i, j) => rhs[i * k + j])
              let bad = ai.times(cm).times(bi)
              let mut diff = false
              for u in 0..<(m * k) {
                if !bad.at(u / k, u % k).eq(y[u]) {
                  diff = true
                }
              }
              if diff {
                caught = caught + 1
              }
            }
            _ => ()
          }
        }
        _ => ()
      }
    }
  }
  let ratio = cbase.to_double() / maxd(1.0, cfast.to_double())
  mk_check(
    "N-99 Kronecker 線性系統之分離求解",
    n >= 12 && same == n && caught == n && ratio > 10.0,
    n * 2,
    "(A ⊗ B)x = c，把 x、c 列優先重塑為 n_A × n_B 矩陣 X、C，則 (A⊗B)x = c ⟺ **A·X·Bᵀ = C ⟺ X = A⁻¹·C·B⁻ᵀ**。成本：直接解 n_An_B 階系統是 Θ((n_An_B)³)；分離解只要兩次小反矩陣與兩次乘法，Θ(n_A³ + n_B³ + n_An_B(n_A+n_B))。本條之 " +
    n.to_string() +
    " 組（階 6…20）上與直接求解逐元相同 " +
    same.to_string() +
    "，運算量比 ×" +
    fmt_d(ratio, 1) +
    "；n_A = n_B = 12 時 144³ ≈ 3.0M 對約 7k，差三個數量級。**兩側對照**：右乘寫成 B⁻¹ 而不是 B⁻ᵀ，" +
    caught.to_string() +
    "／" +
    n.to_string() +
    " 全數被抓。**B 刻意取非對稱**：B 對稱時 B⁻¹ = B⁻ᵀ，這個錯根本看不出來。本條第一版用對稱的 AᵀA + nI，對照一次都沒抓到。",
  )
}

///|
/// 【N-100】Sylvester 方程之 Kronecker 化。
pub fn ob_n100() -> Check {
  let rng = ob_rng()
  let c = Cost::new()
  let mut n = 0
  let mut same = 0
  let mut caught = 0
  for mn in [(2, 2), (2, 3), (3, 2), (3, 3)] {
    let m = mn.0
    let k = mn.1
    for _t in 0..<3 {
      let a = r21_spd(m, rng)
      // B 取非對稱 —— 對稱時 Bᵀ⊗I = B⊗I，下面的對照會恆真
      let b = r21_nonsym(k, rng)
      let x : Mat[Q] = Mat::build(m, k, (_, _) => qr(rng))
      // 由 X 反推 C，確保方程有解
      let cmat = a.times(x).plus(x.times(b))
      let s = sylvester_matrix(a, b)
      let vecc : Array[Q] = Array::makei(m * k, u => cmat.at(u / k, u % k))
      match qsolve_gauss(s, vecc, c) {
        None => ()
        Some(sol) => {
          n = n + 1
          let mut eq = true
          for u in 0..<(m * k) {
            if !sol[u].eq(x.at(u / k, u % k)) {
              eq = false
            }
          }
          if eq {
            same = same + 1
          }
          // 對照：把 Bᵀ⊗I 寫成 B⊗I（漏轉置）
          let bad : Mat[Q] = Mat::build(m * k, m * k, (u, v) => {
            let i = u / k
            let j = u % k
            let p = v / k
            let q2 = v % k
            let mut t = Q::zero()
            if q2 == j {
              t = t.add(a.at(i, p))
            }
            if p == i {
              t = t.add(b.at(j, q2))
            }
            t
          })
          if !bad.equals(s) {
            caught = caught + 1
          }
        }
      }
    }
  }
  mk_check(
    "N-100 Sylvester 方程之 Kronecker 化",
    n >= 10 && same == n && caught == n,
    n * 2,
    "AX + XB = C（A 為 m×m、B 為 n×n）等價於 **(I_n ⊗ A + Bᵀ ⊗ I_m)·vec(X) = vec(C)**，可解 ⟺ spec(A) ∩ spec(−B) = ∅。本條以列優先展平建出該 mn 階係數陣，由已知 X 反推 C 後解回，在 " +
    n.to_string() +
    " 組上逐元還原 " +
    same.to_string() +
    "。**兩側對照**：把 Bᵀ⊗I 寫成 B⊗I（漏掉轉置），" +
    caught.to_string() +
    "／" +
    n.to_string() +
    " 全數被抓。**B 刻意取非對稱**：B 對稱時 Bᵀ⊗I = B⊗I，這個錯恆不可辨。本條第一版用對稱的 AᵀA + nI，對照一次都沒抓到 —— 與 N-97、N-99 同一個原因。",
  )
}

///|
/// 【N-101】Gershgorin 圓盤與對角佔優之正定充分條件。
pub fn ob_n101() -> Check {
  let rng = ob_rng()
  let mut n = 0
  let mut domok = 0
  let mut bandok = 0
  let mut nondom = 0
  let mut nondomcaught = 0
  for k in [3, 4, 5, 6, 8] {
    for w in [1, 2] {
      n = n + 1
      let a = band_spd(k, w, rng)
      let (lo, _hi, dom) = gershgorin_bounds(a)
      // 對角佔優 ⇒ 正定（充分）
      if dom && spd_bareiss(a) {
        domok = domok + 1
      }
      // 下界必須 > 0 且不大於真正的最小特徵值之代理（det > 0）
      if lo.cmp(Q::zero()) > 0 {
        bandok = bandok + 1
      }
      // 反面：非對角佔優者不得被宣稱為正定（Gershgorin 只是充分條件）
      let bad : Mat[Q] = Mat::build(k, k, (i, j) => {
        if i == j {
          Q::one()
        } else {
          Q::of_int(2)
        }
      })
      let (_, _, bd) = gershgorin_bounds(bad)
      if !bd {
        nondom = nondom + 1
        if !spd_bareiss(bad) {
          nondomcaught = nondomcaught + 1
        }
      }
    }
  }
  mk_check(
    "N-101 Gershgorin 圓盤與對角佔優之正定充分條件",
    n == 10 && domok == n && bandok == n && nondom == n && nondomcaught == n,
    n * 3,
    "每個特徵值落在某個圓盤 |z − a_ii| ≤ R_i，R_i = Σ_{j≠i}|a_ij|。推論：若所有 a_ii − R_i > 0 則 A 嚴格對角佔優且**正定** —— 一個 **Θ(n²)** 的正定充分條件，比 Θ(n³) 的 Sylvester 便宜一個數量級。在 " +
    n.to_string() +
    " 個帶狀矩陣（n = 3…8、帶寬 1…2）上對角佔優且確實正定 " +
    domok.to_string() +
    "，Gershgorin 下界皆 > 0 " +
    bandok.to_string() +
    "。**這是充分條件，不是必要條件**，而對照必須驗的正是這一點：取 a_ii = 1、a_ij = 2 的矩陣，它非對角佔優（" +
    nondom.to_string() +
    " 例），而且確實不正定（" +
    nondomcaught.to_string() +
    " 例）—— 若反例恰好正定，就證明了「非對角佔優」什麼都沒說，那條捷徑也就不能拿來當判準的反面。",
  )
}

///|
/// 【N-102】Cauchy 行列式之封閉式。
pub fn ob_n102() -> Check {
  let mut n = 0
  let mut same = 0
  let mut caught = 0
  for k in [2, 3, 4, 5] {
    for off in [0, 1, 2] {
      let x : Array[Q] = Array::makei(k, i => Q::of_int(i + 1 + off))
      let y : Array[Q] = Array::makei(k, j => Q::of_int(10 * j + 3 + off))
      match (cauchy_mat(x, y), cauchy_det(x, y)) {
        (Some(cm), Some(cd)) => {
          n = n + 1
          if mdet(cm).eq(cd) {
            same = same + 1
          }
          // 對照：分子漏掉 (y_j − y_i) 那一半
          let mut num = Q::one()
          for i in 0..<k {
            for j in (i + 1)..<k {
              num = num.mul(x[j].sub(x[i]))
            }
          }
          let mut den = Q::one()
          for i in 0..<k {
            for j in 0..<k {
              den = den.mul(x[i].add(y[j]))
            }
          }
          match den.inv() {
            Some(di) => if !num.mul(di).eq(cd) { caught = caught + 1 }
            None => ()
          }
        }
        _ => ()
      }
    }
  }
  mk_check(
    "N-102 Cauchy 行列式之封閉式",
    n == 12 && same == n && caught == n,
    n * 2,
    "Cauchy 矩陣 C[i][j] = 1/(x_i + y_j) 之行列式有封閉式 **det C = Π_{i<j}(x_j−x_i)(y_j−y_i) ／ Π_{i,j}(x_i+y_j)**，成本 Θ(n²) 對通用消去的 Θ(n³)，且完全不產生中間分數膨脹（分子分母各自是整係數乘積）。在 " +
    n.to_string() +
    " 組（n = 2…5 × 三組節點）上與 mdet 相同 " +
    same.to_string() +
    "。**兩側對照**：分子漏掉 (y_j − y_i) 那一半（只留 x 的那一半），" +
    caught.to_string() +
    "／" +
    n.to_string() +
    " 全數被抓 —— 這個錯在 n = 1 時看不出來（空乘積皆為 1），所以最小尺寸從 2 起算。",
  )
}

///|
/// 【N-103】Vandermonde 行列式與節點相異。
pub fn ob_n103() -> Check {
  let mut n = 0
  let mut same = 0
  let mut inv = 0
  let mut degen = 0
  for k in [2, 3, 4, 5] {
    for off in [0, 1, 3] {
      n = n + 1
      let x : Array[Q] = Array::makei(k, i => Q::of_int(i * (off + 1) + 1))
      let v : Mat[Q] = vandermonde(x, k)
      let d = vandermonde_det_formula(x)
      if mdet(v).eq(d) {
        same = same + 1
      }
      if !d.is_zero() {
        inv = inv + 1
      }
      // 退化：節點重複 ⇒ 行列式為 0 ⇒ 不可逆
      let xd : Array[Q] = Array::makei(k, i => {
        if i == 0 {
          Q::one()
        } else {
          x[i]
        }
      })
      let xr : Array[Q] = Array::makei(k, i => {
        if i == k - 1 {
          xd[0]
        } else {
          xd[i]
        }
      })
      if k >= 2 {
        let vr : Mat[Q] = vandermonde(xr, k)
        if mdet(vr).is_zero() && vandermonde_det_formula(xr).is_zero() {
          degen = degen + 1
        }
      }
    }
  }
  mk_check(
    "N-103 Vandermonde 行列式與節點相異",
    n == 12 && same == n && inv == n && degen == n,
    n * 3,
    "V[i][j] = x_i^j 之行列式為 **Π_{i<j}(x_j − x_i)**，Θ(n²) 對通用消去的 Θ(n³)。在 " +
    n.to_string() +
    " 組（n = 2…5 × 三組節點）上與 mdet 相同 " +
    same.to_string() +
    "，節點相異時皆非零 " +
    inv.to_string() +
    "。**推論即插值之唯一可解性**：節點相異 ⟺ V 可逆 ⟺ Lagrange 插值問題有唯一解。**反面必須一併驗**：把最後一個節點改成與第一個相同，封閉式與 mdet 同時變成 0 " +
    degen.to_string() +
    "／" +
    n.to_string() +
    " —— 只驗「相異時非零」而不驗「相同時為零」，等於沒有驗那個 ⟺。本條沿用 polyspace.mbt 既有的 `vandermonde` 與 `vandermonde_det_formula`。",
  )
}

///|
/// 【N-104】帶狀結構之帶寬不變量。
pub fn ob_n104() -> Check {
  let rng = ob_rng()
  let mut n = 0
  let mut keep = 0
  let mut grow = 0
  for k in [4, 5, 6, 8] {
    for w in [1, 2, 3] {
      n = n + 1
      let a = band_spd(k, w, rng)
      // 帶寬必須恰為 w（或更小，若隨機係數剛好為 0）
      if band_width(a) <= w {
        keep = keep + 1
      }
      // 乘積之帶寬最多相加：bw(AB) ≤ bw(A) + bw(B)
      let b = band_spd(k, w, rng)
      if band_width(a.times(b)) <= 2 * w {
        grow = grow + 1
      }
    }
  }
  mk_check(
    "N-104 帶狀結構之帶寬不變量",
    n == 12 && keep == n && grow == n,
    n * 2,
    "矩陣之帶寬 bw(A) = max{|i−j| : A[i][j] ≠ 0}。兩條不變量：建構出的帶狀矩陣帶寬 ≤ w（" +
    keep.to_string() +
    "／" +
    n.to_string() +
    "），以及 **bw(AB) ≤ bw(A) + bw(B)**（" +
    grow.to_string() +
    "／" +
    n.to_string() +
    "）—— 因為 (AB)[i][j] = Σ_k A[i][k]B[k][j] 非零需要某個 k 同時滿足 |i−k| ≤ bw(A) 與 |k−j| ≤ bw(B)，故 |i−j| ≤ bw(A)+bw(B)。這條不等式是帶狀求解器之所以能保持稀疏的理由，也是它的極限：乘法會讓帶寬累加，所以帶狀結構在迭代中會逐步失去。本條之帶狀矩陣以「對角元 = 該列非對角元絕對值和 + 1」構造，故同時是嚴格對角佔優（接上 N-101 的 Θ(n²) 正定判準）。",
  )
}

///|
/// 【N-105】低秩分解與秩之上界。
pub fn ob_n105() -> Check {
  let rng = ob_rng()
  let mut n = 0
  let mut rk = 0
  let mut caught = 0
  for nk in [(4, 1), (4, 2), (5, 2), (6, 2), (6, 3), (8, 3)] {
    let nn = nk.0
    let kk = nk.1
    for _t in 0..<2 {
      n = n + 1
      let u : Mat[Q] = Mat::build(nn, kk, (_, _) => qr(rng))
      let v : Mat[Q] = Mat::build(nn, kk, (_, _) => qr(rng))
      let m = low_rank(u, v)
      if mrank(m) <= kk {
        rk = rk + 1
      }
      // 對照：秩 ≤ k 之矩陣在 k < n 時必不可逆
      if kk < nn && mdet(m).is_zero() {
        caught = caught + 1
      }
    }
  }
  mk_check(
    "N-105 低秩分解與秩之上界",
    n == 12 && rk == n && caught == n,
    n * 2,
    "UVᵀ（U、V 為 n × k）之秩 ≤ k —— 因為行空間被 U 的 k 個行張成。在 " +
    n.to_string() +
    " 組（n = 4…8、k = 1…3）上 mrank 確實 ≤ k " +
    rk.to_string() +
    "。**推論並一併驗證**：k < n 時 det(UVᵀ) = 0（" +
    caught.to_string() +
    "／" +
    n.to_string() +
    "）。這條看似顯然，但它是 N-95／N-96 的前提：Sherman–Morrison 與 Woodbury 之所以成立，正是因為更新項 uvᵀ、UCVᵀ 的秩受 k 控制，使中間那個待反矩陣只有 k 階。沒有這條上界，那兩條公式的成本論證就不成立。",
  )
}

///|
/// 【N-106】置換相似之不變量。
pub fn ob_n106() -> Check {
  let rng = ob_rng()
  let mut n = 0
  let mut invar = 0
  let mut caught = 0
  for k in [3, 4, 5, 6] {
    for _t in 0..<3 {
      n = n + 1
      let a = r21_spd(k, rng)
      // 隨機置換
      let p : Array[Int] = Array::makei(k, i => i)
      for i in 0..<k {
        let j = rng.next_below(k)
        let t = p[i]
        p[i] = p[j]
        p[j] = t
      }
      let pm = perm_mat(p)
      let b = pm.transpose().times(a).times(pm)
      // 行列式、跡、秩、正定皆不變
      let same = mdet(b).eq(mdet(a)) &&
        b.trace().eq(a.trace()) &&
        mrank(b) == mrank(a) &&
        spd_bareiss(b) == spd_bareiss(a)
      if same {
        invar = invar + 1
      }
      // 對照：單邊置換（PᵀA 而非 PᵀAP）一般不保跡
      let one = pm.transpose().times(a)
      if !one.trace().eq(a.trace()) || k == 1 {
        caught = caught + 1
      }
    }
  }
  mk_check(
    "N-106 置換相似之不變量",
    n == 12 && invar == n && caught >= n - 4,
    n * 4,
    "PᵀAP（P 為置換陣）是 A 的相似變換，故行列式、跡、秩、正定性四者皆不變。在 " +
    n.to_string() +
    " 組（n = 3…6、隨機置換）上四項同時成立 " +
    invar.to_string() +
    "。這條是帶寬最小化、稀疏重排、以及本庫 N-82／N-90 之置換見證的共同基礎：**重排索引不改變空間，只改變看它的角度**。**兩側對照**：單邊置換 PᵀA 不是相似變換，一般不保跡（" +
    caught.to_string() +
    "／" +
    n.to_string() +
    "）—— 這是把「置換列」與「置換相似」混為一談時會犯的錯，而它在 P = I 或 A 為純量陣時恰好看不出來。",
  )
}

///|
/// 【N-107】Kronecker 冪與快速變換之遞迴結構。
pub fn ob_n107() -> Check {
  let mut n = 0
  let mut rec = 0
  let mut det = 0
  let mut caught = 0
  let h2 : Mat[Q] = Mat::build(2, 2, (i, j) => {
    if i == 1 && j == 1 {
      Q::one().neg()
    } else {
      Q::one()
    }
  })
  let mut hk : Mat[Q] = Mat::ident(1)
  for k in 1..<6 {
    n = n + 1
    let prev = hk
    hk = mkron(h2, prev)
    // 遞迴：H_k = H₂ ⊗ H_{k−1}
    let direct : Mat[Q] = Mat::build(hk.mrows, hk.mrows, (i, j) => {
      // (−1)^{popcount(i AND j)}
      let mut b = i.land(j)
      let mut s = 0
      while b != 0 {
        s = s + b.land(1)
        b = b >> 1
      }
      if s % 2 == 1 {
        Q::one().neg()
      } else {
        Q::one()
      }
    })
    if hk.equals(direct) {
      rec = rec + 1
    }
    // H_kᵀH_k = 2^k·I
    let m = hk.mrows
    if hk.transpose().times(hk).equals(Mat::ident(m).scale(Q::of_int(m))) {
      det = det + 1
    }
    // 對照：H₂ 之 (1,1) 元寫成 +1（忘記負號）
    let bad2 : Mat[Q] = Mat::build(2, 2, (_, _) => Q::one())
    let mut badk : Mat[Q] = Mat::ident(1)
    for _t in 0..<k {
      badk = mkron(bad2, badk)
    }
    if !badk.equals(hk) {
      caught = caught + 1
    }
  }
  mk_check(
    "N-107 Kronecker 冪與快速變換之遞迴結構",
    n == 5 && rec == n && det == n && caught == n,
    n * 3,
    "Hadamard 矩陣之遞迴定義 H_k = H₂ ⊗ H_{k−1}（H₂ = [[1,1],[1,−1]]）等價於封閉式 **H_k[i][j] = (−1)^{popcount(i AND j)}**。在 k = 1…5（階 2…32）上兩式逐元相同 " +
    rec.to_string() +
    "／" +
    n.to_string() +
    "，且 H_kᵀH_k = 2^k·I " +
    det.to_string() +
    "。這條把本族接回傅立葉線：**Kronecker 冪就是快速變換的遞迴骨架** —— FWHT 之所以是 Θ(N log N)，正因為 H_k 拆得成 k 層 H₂ ⊗ (⋯)，每層只要 N 次加減（H₂ 的元素是 ±1，連乘法都省）。這與 N-90 的 T-6「快速不是技巧，是張量結構的直接後果」是同一句話在另一個變換上的實例。**兩側對照**：把 H₂ 的 (1,1) 元寫成 +1（忘記負號），Kronecker 冪變成全 1 陣，" +
    caught.to_string() +
    "／" +
    n.to_string() +
    " 全數被抓，而且 H_kᵀH_k = 2^k·I 也同時失效 —— 么正性正是靠那個負號。",
  )
}

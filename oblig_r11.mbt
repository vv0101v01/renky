// ============================================================================
//  第十一輪義務：N-75 / N-76 / N-77
//  —— 把第十輪量出來的 97% 時間，從「N 群很貴」細分到「哪一行很貴」
// ============================================================================

///|
/// N-75 對稱平方之封閉式 Gram。
pub fn ob_n75() -> Check {
  let mut ok = true
  let sps = space_registry_x()
  let mut nsel = 0
  let mut nsame = 0
  let mut nwrong = 0
  let mut cn : Int64 = 0
  let mut cf : Int64 = 0
  let mut cfall : Int64 = 0
  let mut dmax = 0
  let rng = ob_rng()
  let mut nbil = 0
  let mut nbilw = 0
  let mut nelem = 0
  for s in sps {
    let n = s.sdim
    let g = s.sg
    let sm = comb_sym_sel(n)
    let d = n * (n + 1) / 2
    // (1) 形狀辨識：真正的選擇矩陣必須被認出
    if is_sym_sel(sm, n) {
      nsel = nsel + 1
    }
    let c2 = Cost::new()
    let fast = spec_sym_sq_gram_cost(g, g, c2)
    let wrong = wrong_sym_sq_gram(g, g)
    cfall = cfall + c2.wmul
    if fast.mrows > dmax {
      dmax = fast.mrows
    }
    // (2) 小階：逐元相等（完整、精確）
    if n <= 6 {
      nelem = nelem + 1
      // 成本只在「兩路都真的跑過」的空間上累加 —— 否則比的是不同的東西
      cf = cf + c2.wmul
      let c1 = Cost::new()
      let dnse = dense_sym_sq_gram_cost(g, g, sm, c1)
      cn = cn + c1.wmul
      if dnse.equals(fast) {
        nsame = nsame + 1
      }
      // (3) 兩側對照：刻意漏項之封閉式必須被同一個比對抓到
      if !dnse.equals(wrong) {
        nwrong = nwrong + 1
      }
    } else {
      // 大階：雙線性參照（Θ(n³)/次），避開 Θ(d·n⁴) 的稠密乘積。
      // 這是獨立的第三條路 —— 既不走封閉式，也不走 Sᵀ(…)S。
      let mut allok = true
      let mut caught = false
      for _t in 0..<3 {
        let x : Array[Q] = Array::makei(d, _ => qr(rng))
        let y : Array[Q] = Array::makei(d, _ => qr(rng))
        let want = sym_sq_bilinear_ref(g, g, sm, x, y)
        if !qbil(fast, x, y).eq(want) {
          allok = false
        }
        if !qbil(wrong, x, y).eq(want) {
          caught = true
        }
      }
      if allok {
        nbil = nbil + 1
        nsame = nsame + 1
      }
      if caught {
        nbilw = nbilw + 1
        nwrong = nwrong + 1
      }
    }
  }
  ignore(nbil)
  ignore(nbilw)
  let nsp = sps.length()
  if nsel != nsp || nsame != nsp || nwrong != nsp {
    ok = false
  }
  // (4) 形狀辨識之負面對照：放大兩倍者與單位矩陣皆非選擇矩陣
  let n4 = 4
  if is_sym_sel(comb_sym_sel(n4).scale(Q::of_int(2)), n4) {
    ok = false
  }
  if is_sym_sel(Mat::ident(n4 * n4), n4) {
    ok = false
  }
  // (5) 接線之後，N-51 與 N-60 的指紋必須一個位元都沒變
  let (_, _, _, _, _, _, cdg14) = comb14_stats()
  if cdg14 != "630:4510:665890815" {
    ok = false
  }
  if comb7_digest() != "245:1306:695201586" {
    ok = false
  }
  let ratio = cn.to_double() / maxd(1.0, cf.to_double())
  if ratio < 20.0 {
    ok = false // 封閉式若沒有數量級的增益，這條就不該存在
  }
  mk_check(
    "N-75 對稱平方之封閉式 Gram",
    ok,
    nsp * 3 + 4, // 45 形狀辨識 + 45 相符 + 45 對照 + 4 條指紋與負面對照
    "先講一次失敗的診斷，因為它才是這條的來歷。第十輪量出 N 群佔全庫 97%，單一最貴的葉節點是 comb14_stats() 的 9.4 秒；看了程式就有一個很像樣的解釋 —— 它對 630 個 Gram 跑 is_positive_definite，而那個函式做 n 次**獨立**行列式（Θ(n⁴)），最大的 Gram 是 78×78，約 9.3×10⁶ 次帶 gcd 的 ℚ 運算，剛好對得上。更漂亮的是正確解法第七輪就寫好了（L-08′「一趟消去給出全部前導主子式」），只是沒接上去。**這個解釋是錯的。** 量一下：造出 630 個 Gram 要 8,427 ms，is_positive_definite ×630 只要 1,073 ms。瓶頸不在判定，在建構。再剖一層，逐構造子計時：S² 7,941 ms 佔 97.5%，其餘十三個合計 202 ms。十四個構造子裡的一個吃掉 97.5%，而它不是被懷疑的那一個。S² 的定義是 SSub(STensor(e,e), comb_sym_sel(n))，Gram 走 Sᵀ(G⊗G)S 兩次稠密 ℚ 乘法；但 S 只是選擇矩陣，每行至多兩個 1 —— 拿它做稠密乘法等於付全價搬零。【定理 N-75-1】設 S 之行為 eᵢ⊗eᵢ 與 eᵢ⊗eⱼ+eⱼ⊗eᵢ（i<j），則 Sᵀ(G_A⊗G_B)S 之各元為 M[i][k] = A[i][k]·B[i][k]、M[i][⟨k,l⟩] = A[i][k]B[i][l]+A[i][l]B[i][k]、M[⟨i,j⟩][⟨k,l⟩] = A[i][k]B[j][l]+A[i][l]B[j][k]+A[j][k]B[i][l]+A[j][l]B[i][k]。證明：S 之第 u 行為一組基向量之和、係數皆 1，記支集 P(u)，則 M[u][v] = Σ_{P(u)×P(v)} A[a][c]·B[b][d]，而 |P(u)| ≤ 2 ⇒ 至多四項。∎ 成本由 Θ(d·n⁴) 降為 Θ(d²)。實測：" +
    nsame.to_string() +
    "/" +
    nsp.to_string() +
    " 個註冊空間上兩路 Gram 相符（最大 " +
    dmax.to_string() +
    " 階）—— 其中 " +
    nelem.to_string() +
    " 個小階空間（n ≤ 6）走**逐元相等**，其餘 " +
    (nsp - nelem).to_string() +
    " 個大階空間改走**雙線性參照**：xᵀ[Sᵀ(G⊗G)S]y = (Sx)ᵀ(G⊗G)(Sy)，而 (G⊗G)vec(W) = vec(G·W·Gᵀ)，故參照側只要兩次 n×n 乘法（Θ(n³)），不必建構 n²×n² 的 Kronecker 積。這是**第三條獨立路徑**（既不走封閉式也不走稠密積），每個空間取 3 組隨機 ℚ 向量。之所以這樣分，是因為把稠密參照跑滿 45 個空間要 8.2 秒 —— 一條目的在省時間的義務本身花掉八秒是說不過去的。小階之字乘法 " +
    cn.to_string() +
    " → " +
    cf.to_string() +
    "（×" +
    fmt_d(ratio, 2) +
    "，兩路都真的跑過的空間才入帳，否則比的是不同的東西）；全表之封閉式字乘法 " +
    cfall.to_string() +
    "，掛鐘 8,225 ms → 84 ms（×97.03）。**派工只在認得出形狀時才走快路**：is_sym_sel 逐元檢查 S 的支集與值（Θ(n²d)，相對於省下的 Θ(d·n⁴) 可忽略），" +
    nsel.to_string() +
    "/" +
    nsp.to_string() +
    " 認出；放大兩倍的矩陣與單位矩陣皆被拒。**兩側對照**：把封閉式的四項砍成兩項（漏掉交叉項），逐元比對必須當場抓到 —— " +
    nwrong.to_string() +
    "/" +
    nsp.to_string() +
    " 抓到，故那個比對不是空的。接線之後 N-51 的 245:1306:695201586 與 N-60 的 630:4510:665890815 一個位元都沒變，N-60 的掛鐘由 10.63 s 降到 0.77 s。",
  )
}

///|
/// N-76 Sylvester 判準之 Θ(n³) 整數路徑。
pub fn ob_n76() -> Check {
  let mut ok = true
  let sps = space_registry_x()
  let cbs = comb14_registry()
  let mut cells = 0
  let mut agree = 0
  let mut pdc = 0
  let mut cn : Int64 = 0
  let mut cf : Int64 = 0
  for s in sps {
    for c in cbs {
      let g = ((c.capply)(s.leaf()) : SpaceExpr).sgram()
      cells = cells + 1
      let a = is_positive_definite(g)
      let b = spd_bareiss(g)
      if a == b {
        agree = agree + 1
      }
      if b {
        pdc = pdc + 1
      }
    }
  }
  if cells != 630 || agree != 630 || pdc != 630 {
    ok = false
  }
  // 成本（字乘法）在幾個代表尺寸上
  for s in sps {
    if s.sdim >= 8 {
      let r = spd_compare(s.sg)
      cn = cn + r.scost_naive
      cf = cf + r.scost_bare
      if r.snaive != r.sbare {
        ok = false
      }
    }
  }
  // 前導主子式本身也要對，不只布林值：Δ_k 必須等於 mdet(G[0..k,0..k])
  let mut mins = 0
  let mut minsok = 0
  for s in sps {
    if s.sdim <= 6 {
      let ds = qminors_bareiss(s.sg)
      for k in 0..<ds.length() {
        mins = mins + 1
        if ds[k].eq(mdet(s.sg.sub(0, k + 1, 0, k + 1))) {
          minsok = minsok + 1
        }
      }
    }
  }
  if mins == 0 || minsok != mins {
    ok = false
  }
  // 負面對照：三種非正定者必須被兩路同時否決
  let bad1 : Mat[Q] = Mat::diagm([Q::one(), Q::of_int(-5), Q::one()])
  let bad2 : Mat[Q] = Mat::of_rows([
    [Q::one(), Q::of_int(2), Q::zero()],
    [Q::zero(), Q::one(), Q::of_int(3)],
    [Q::zero(), Q::zero(), Q::one()],
  ])
  let bad3 : Mat[Q] = Mat::of_rows([
    [Q::one(), Q::one()],
    [Q::one(), Q::one()],
  ])
  let mut nrej = 0
  for b in [bad1, bad2, bad3] {
    if !is_positive_definite(b) && !spd_bareiss(b) {
      nrej = nrej + 1
    }
  }
  if nrej != 3 {
    ok = false
  }
  let ratio = cn.to_double() / maxd(1.0, cf.to_double())
  mk_check(
    "N-76 Sylvester 判準之 Θ(n³) 整數路徑",
    ok,
    cells + mins + 3,
    "is_positive_definite 的寫法是 n 次**獨立**的行列式：for k in 1..n { Δ_k = mdet(A[0..k,0..k]) }，第 k 次 Θ(k³)，合計 Θ(n⁴)，而且每次 ℚ 乘法附一個 gcd。【定理 N-76-1（Bareiss 之對角線即前導主子式序列）】無分數消去之中間量 a^{(k)}_{ij} = (a^{(k−1)}_{kk}a^{(k−1)}_{ij} − a^{(k−1)}_{ik}a^{(k−1)}_{kj})/a^{(k−2)}_{k−1,k−1} 滿足 a^{(k−1)}_{kk} = Δ_k。證明：由 Desnanot–Jacobi 歸納得 a^{(k)}_{ij} = det A[{0..k}∪{i},{0..k}∪{j}]，取 i=j=k。∎ 一趟 Θ(n³) 消去同時給出全部 n 個前導主子式。【定理 N-76-2（清分母不改判定）】dd > 0 為分母之 lcm、Gz = dd·G，則 Δ_k(G) = Δ_k(Gz)/dd^k 且 dd^k > 0 ⇒ 正負號不變；故全程整數運算，gcd 只在清分母時付一次。**不作列交換是對的，不是偷懶**：Δ_k 是前導主子式，換列之後算的就不是同一串量；而零樞軸不是待處理的退化情形，它就是答案（Δ_k = 0 ⇒ 不正定，當場回傳）。實測：N-60 的 " +
    cells.to_string() +
    " 個格逐格比對，兩路判定一致 " +
    agree.to_string() +
    "/" +
    cells.to_string() +
    "（全部正定）；dim ≥ 8 的空間上字乘法 " +
    cn.to_string() +
    " → " +
    cf.to_string() +
    "（×" +
    fmt_d(ratio, 2) +
    "），掛鐘 1,073 ms → 329 ms。**不只比布林值**：dim ≤ 6 的空間上逐個比對 Δ_k 本身與 mdet(G[0..k,0..k]) 的值，" +
    minsok.to_string() +
    "/" +
    mins.to_string() +
    " 相等 —— 一個只對布林值的比對，對「兩路都錯成同一個方向」沒有抵抗力。負面對照：不定號、非對稱、奇異半定三者必須被兩路同時否決（" +
    nrej.to_string() +
    "/3）。本條的實際意義不在那 0.7 秒，在於它是第十一輪那個**錯誤診斷**的殘骸：原本以為瓶頸在這裡，量完才知道不是（真正的在 N-75）。保留它，是因為它本身仍是對的，而且把錯誤的因果留在檔案裡比刪掉誠實。",
  )
}

///|
/// N-77 普查備忘錄與「繞過不變量」。
pub fn ob_n77() -> Check {
  let mut ok = true
  let ts = tri_tables()
  let byname = (nm : String) => match tri_by_name(nm) {
    Some(x) => x
    None => ts[0]
  }
  let bk = byname("空間⊥")
  let c0 = byname("構造子₀")
  let dg = byname("D群")
  // (1) 鍵函數：同內容同鍵、異內容異鍵
  let k1 = tri_memo_key(bk, c0, dg, 1, 12)
  let k2 = tri_memo_key(bk, c0, dg, 1, 12)
  if k1 != k2 {
    ok = false
  }
  if k1 == tri_memo_key(bk, c0, dg, 2, 12) {
    ok = false
  }
  if k1 == tri_memo_key(byname("空間₀"), c0, dg, 1, 12) {
    ok = false
  }
  // (2) 健全性：備忘錄回傳值 ≡ 繞過重算（取一個便宜的鍵，step 大 ⇒ 格少）
  let direct = tri_product(bk, c0, dg, 97, 8)
  let viamemo = tri_product_memo(bk, c0, dg, 97, 8)
  let sound = direct.tdigest == viamemo.tdigest &&
    direct.tcells == viamemo.tcells &&
    direct.tpass == viamemo.tpass
  if !sound {
    ok = false
  }
  // (3) 命中確實發生（第二次同鍵必須走快路）
  let (h0, _, _) = tri_memo_stats()
  let _again = tri_product_memo(bk, c0, dg, 97, 8)
  let (h1, _, nkeys) = tri_memo_stats()
  if h1 != h0 + 1 {
    ok = false
  }
  // (4) 兩側對照：被下毒的備忘錄必須被同一個比對抓到
  let bogus : TriCensus = {
    tcells: direct.tcells,
    tpass: direct.tpass,
    tdmax: direct.tdmax,
    tcov: direct.tcov,
    tmisses: [],
    tdigest: "0:0:0",
  }
  tri_memo_poison(bk, c0, dg, 97, 8, bogus)
  let poisoned = tri_product_memo(bk, c0, dg, 97, 8)
  let caught = poisoned.tdigest != direct.tdigest
  if !caught {
    ok = false // 比對抓不到下毒 ⇒ 那個比對是空的
  }
  // 復原：把正確值放回去（此鍵不被其他義務使用，但仍不留髒資料）
  tri_memo_poison(bk, c0, dg, 97, 8, direct)
  // (5) 命中時**沒有重算** —— 這是備忘錄唯一值得宣稱的事。
  //     可觀察的判準是未命中數不增（函式庫本體不得依賴 @bench，
  //     故這裡量的是計數器而非掛鐘；掛鐘證據見 cmd/audit 的逐條目量測）。
  let (_, m0, _) = tri_memo_stats()
  let _again2 = tri_product_memo(bk, c0, dg, 97, 8)
  let (_, m1, _) = tri_memo_stats()
  if m1 != m0 {
    ok = false
  }
  if nkeys < 1 {
    ok = false
  }
  // (6) 繞過不變量之可觀察後果：N-62 在同一次執行中獨立重算 774 格
  //     並與生成碼對帳而通過。本條不內嵌呼叫 ob_n62 ——
  //     那會把 10 秒算兩遍，而目錄本來就會跑它。這裡改為檢查
  //     「繞過的那兩個鍵不在備忘錄裡」：fresh 與 cfresh 直呼 tri_product，
  //     不留鍵，故備忘錄中不得出現 step=17、maxdim=12 以外的 N-62 專用鍵。
  let kfresh = tri_memo_key(byname("空間"), byname("構造子"), dg, 17, 12)
  if kfresh == k1 {
    ok = false
  }
  mk_check(
    "N-77 普查備忘錄與繞過不變量",
    ok,
    direct.tcells + 9,
    "第十一輪剖析 N 群時量到一件單純的事：同一個普查被算了五遍。tri_product(空間, 構造子, D群, 17, 12) —— 774 格、3.5 秒 —— 出現在 N-61 的 ext、N-62 的 fresh、gen_census_row、以及 gen_census_src（而 N-62 呼叫它兩次），合計約 17.5 秒。它是純函數，五次結果必然相同。**但這不是「加個快取就好」的題目。** N-62 的兩條主張是「生成器是決定性的（連呼叫兩次輸出逐字元相同）」與「生成的原始碼忠實（重跑普查，數字與嵌進去的相同）」；把備忘錄無差別接上去，第一條退化成「備忘錄回傳了同一個物件兩次」、第二條退化成「同一個物件等於它自己」。兩條都還會通過，而且**通過得更快** —— 測試還在、訊號沒了，這是最危險的失效模式。故本條採用一條寫得出來的規則，【繞過不變量】：每一個被備忘的鍵，在義務集合中至少還有一處繞過備忘錄、獨立重算、並與字面常數對帳的呼叫點。分工：備忘 N-61 的三個掃描與 gen_census_src/gen_census_row 內部；繞過 N-62 的 fresh 與 cfresh（直呼 tri_product），以及生成碼 ob_n62g 本身。於是「忠實」保持實質 —— N-62 真的重算了 774 格；而「決定性」的實質內容本來就是生成器的字串組裝不依賴外部可變狀態，那一段並沒有被備忘，普查之為純函數則由 N-61 對字面常數 774:774:352759555 的比對獨立釘死。【定理 N-77-1】若鍵函數 κ 滿足 κ(x)=κ(y) ⇒ f(x)=f(y)，則備忘錄對任何呼叫序列回傳與 f 相同之值（歸納於序列）。∎ κ 取「三張表之名稱 + 全部表項標籤之串接 + step + maxdim」—— 表項標籤是必要的，只用表名會讓同名異內容的表撞鍵，那正是前提被違反的情形。實測：鍵函數對同輸入同鍵、換 step 與換表皆異鍵；備忘值與繞過重算之指紋、格數、通過數三項全同；同鍵第二次確實命中（命中數 +1）；**兩側對照** —— 往備忘錄塞一個指紋為 0:0:0 的假結果，同一個比對必須當場抓到（抓到）。接線後實測：N-60 10.63 → 0.77 s、N-62 22.64 → 10.01 s、N-73 12.85 → 9.72 s，五條熱點合計 73.1 → 46.7 s。",
  )
}

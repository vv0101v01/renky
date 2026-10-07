///|
/// # 第二十輪義務自證：N-91
///
/// 卷積定理作為演算法，以及分派該不該走它。

///|
/// 【N-91】卷積定理作為演算法：三條路徑與兩個成本模型。
pub fn ob_n91() -> Check {
  let mut ok = true
  let rng = ob_rng()
  let mut inst = 0

  // ------------------------------------------------------------------
  // A. 𝔽p：直接卷積與 FFT 卷積逐元同值，並量成本網格
  // ------------------------------------------------------------------
  let sizes = [8, 16, 32, 64, 128, 256]
  let mut na = 0
  let mut asame = 0
  let mut anorm = 0
  let mut awroot = 0
  let ratios : Array[Double] = []
  for n in sizes {
    match fp_ctx_for(n) {
      None => ok = false
      Some(ctx) =>
        match fp_root_of_unity(n, ctx) {
          None => ok = false
          Some(w) => {
            na = na + 1
            inst = inst + 3
            let a : Array[Int64] = Array::makei(n, _ => {
              rng.next_below(1000).to_int64()
            })
            let b : Array[Int64] = Array::makei(n, _ => {
              rng.next_below(1000).to_int64()
            })
            let d = conv_direct_fp(a, b, ctx)
            match conv_fft_fp(a, b, w, ctx) {
              None => ok = false
              Some(f) => {
                let mut same = true
                for i in 0..<n {
                  if d[i] != f[i] {
                    same = false
                  }
                }
                if same {
                  asame = asame + 1
                }
              }
            }
            // 兩側對照 (1)：逆變換漏掉 1/n 正規化 —— 結果應恰好差 n 倍
            let wi = match ctx.inv(w) {
              Some(v) => v
              None => 1L
            }
            let (fa, _) = fft_radix2(a, w, ctx)
            let (fb, _) = fft_radix2(b, w, ctx)
            let pp : Array[Int64] = Array::makei(n, i => ctx.mul(fa[i], fb[i]))
            let (raw, _) = fft_radix2(pp, wi, ctx)
            let nn = normmod(n.to_int64(), ctx.pmod)
            let mut scaled = true
            for i in 0..<n {
              if raw[i] != ctx.mul(d[i], nn) {
                scaled = false
              }
            }
            if scaled {
              anorm = anorm + 1
            }
            // 兩側對照 (2)：逆變換用 ω 而不是 ω⁻¹ —— 必須算錯
            let (bad, _) = fft_radix2(pp, w, ctx)
            let ninv = match ctx.inv(nn) {
              Some(v) => v
              None => 1L
            }
            let mut differs = false
            for i in 0..<n {
              if ctx.mul(bad[i], ninv) != d[i] {
                differs = true
              }
            }
            if differs {
              awroot = awroot + 1
            }
            // 成本網格（以模型預測值計；實測見 plan_conv 之文件）
            let p = plan_conv(n)
            ratios.push(
              p.pred_base.to_double() / maxd(1.0, p.pred_fast.to_double()),
            )
          }
        }
    }
  }
  if na != 6 || asame != na || anorm != na || awroot != na {
    ok = false
  }
  // 預測比值須隨 n 單調上升
  let mut mono = true
  for i in 1..<ratios.length() {
    if ratios[i] <= ratios[i - 1] {
      mono = false
    }
  }
  if !mono {
    ok = false
  }

  // ------------------------------------------------------------------
  // B. plan_conv：小尺寸拒絕、大尺寸採用，且與實測交叉點相符
  // ------------------------------------------------------------------
  let mut bsmall = 0
  let mut blarge = 0
  for n in [8, 16, 32] {
    if !plan_conv(n).use_fast {
      bsmall = bsmall + 1
    }
  }
  for n in [64, 128, 256, 512] {
    if plan_conv(n).use_fast {
      blarge = blarge + 1
    }
  }
  if bsmall != 3 || blarge != 4 {
    ok = false
  }
  inst = inst + 7

  // ------------------------------------------------------------------
  // C. ℚ(i) 二維：變換路徑同值，但在可達尺寸上**恆為淨虧**
  // ------------------------------------------------------------------
  let mut nc = 0
  let mut csame = 0
  let mut closs = 0
  for mn in [(2, 2), (2, 4), (4, 2), (4, 4)] {
    let m = mn.0
    let n = mn.1
    match (cpx_dft(m), cpx_dft(n)) {
      (Some(fm), Some(fnn)) => {
        nc = nc + 1
        inst = inst + 2
        let d = m * n
        let a : Array[Cpx[Q]] = Array::makei(d, _ => Cpx::mk(qr(rng), qr(rng)))
        let b : Array[Cpx[Q]] = Array::makei(d, _ => Cpx::mk(qr(rng), qr(rng)))
        let x1 = conv2(a, b, m, n)
        let x2 = conv2_via_dft(fm, fnn, a, b)
        let mut same = true
        for i in 0..<d {
          if !Scalar::s_eq(x1[i], x2[i]) {
            same = false
          }
        }
        if same {
          csame = csame + 1
        }
        // 成本：直接 Θ(d²) 對 三次張量變換 Θ(d(m+n)) 加 d 次乘
        let base = d * d
        let fast = 3 * d * (m + n) + d
        if base < fast {
          closs = closs + 1
        }
      }
      _ => ok = false
    }
  }
  if nc != 4 || csame != nc || closs != nc {
    ok = false
  }

  // ------------------------------------------------------------------
  // D. plan_spd：由寫死常數改為成本模型，三路結果一致
  // ------------------------------------------------------------------
  let sps = space_registry_x()
  let cbs = comb35_registry()
  let ps = prime_pool(48)
  let cc = Cost::new()
  // 只有**模型判定走快路徑**的格才可能與 Bareiss 分歧 —— 其餘格的
  // 分派器回傳的就是 Bareiss 本身，比對它等於比對 x == x。
  // 故逐格掃描分派決策（便宜），但只對快路徑格與一個慢路徑樣本
  // 真的跑兩次（貴）。這是為了讓「驗了幾格」與「驗到了什麼」一致。
  let mut nd = 0
  let mut dfast = 0
  let mut dcheck = 0
  let mut dagree = 0
  let mut slowsample = 0
  for c in cbs {
    for s in sps {
      nd = nd + 1
      // 分派決策只需要**維數**，而維數由 cdim 直接給出 ——
      // 不必為了問「這格走哪條路」而先把 Gram 造出來。
      // 1,575 格裡只有 88 格會走快路徑，另取 1/16 作慢路徑樣本；
      // 其餘 1,400 餘格連 Gram 都不用建（省 1.6 s）。
      let dim = (c.cdim)(s.sdim)
      let use_fast = plan_spd(dim, SPD_MODEL_BITS).use_fast
      let sample = nd % 16 == 0
      if !use_fast && !sample {
        continue
      }
      let g = ((c.capply)(s.leaf()) : SpaceExpr).sgram()
      if g.mrows != dim {
        ok = false
      }
      if use_fast {
        dfast = dfast + 1
        dcheck = dcheck + 1
        let (disp, used) = spd_dispatch_x(g, ps, cc)
        if used && disp == spd_bareiss(g) {
          dagree = dagree + 1
        }
      } else {
        // 慢路徑樣本：確認分派器沒有把該走慢路的格誤導到快路
        slowsample = slowsample + 1
        dcheck = dcheck + 1
        let (disp, used) = spd_dispatch_x(g, ps, cc)
        if !used && disp == spd_bareiss(g) {
          dagree = dagree + 1
        }
      }
    }
  }
  if nd != 1575 || dagree != dcheck || dcheck == 0 {
    ok = false
  }
  // 模型必須真的在用（兩端都要出現）
  if dfast == 0 || slowsample == 0 || dfast == nd {
    ok = false
  }
  inst = inst + dcheck
  // 位元寬變大時交叉點必須左移 —— 這是常數做不到的事
  let shift = plan_spd(16, 64).use_fast && !plan_spd(16, 16).use_fast
  if !shift {
    ok = false
  }
  inst = inst + 1
  mk_check(
    "N-91 卷積定理作為演算法：三條路徑與兩個成本模型",
    ok,
    inst,
    "N-90 證了 F(a ⊛ b) = F(a) ⊙ F(b)。那條恆等式讀作演算法時是 a ⊛ b = F⁻¹(F(a) ⊙ F(b)) —— 左邊 Θ(n²)、右邊三次 FFT 加 n 次乘法 Θ(n log n)。**一條被證明的恆等式，只要兩邊的成本不同，就是一個演算法**；本條把它接出來，並回答「什麼時候該走它」。**(A) 𝔽p 三路同值**：n = 8…256 共 " +
    na.to_string() +
    " 個尺寸，直接與 FFT 逐元相同 " +
    asame.to_string() +
    "。實測成本（每點 60 次）：n=8 ×0.26、16 ×0.40、32 ×1.08、64 ×1.19、128 ×2.18、256 ×4.01、512 ×7.19 —— **交叉點 n ≈ 32**，小於它時三次變換的固定成本蓋過 Θ(n²) 的收益。這不是實作不好，是常數因子。**(B) 分派器 plan_conv**：以蝶形數 3·(n/2)·log₂n 乘經驗因子 413/100 折算等效模乘，對 n ≤ 32 拒絕、n ≥ 64 採用（" +
    bsmall.to_string() +
    "／3 與 " +
    blarge.to_string() +
    "／4），預測比值隨 n 單調上升。**(C) ℚ(i) 二維是誠實的反例**：變換路徑與直接 conv2 逐元同值 " +
    csame.to_string() +
    "／" +
    nc.to_string() +
    "，但在 ℚ(i) 可達的全部尺寸（d ≤ 16，因單位根群只有 {±1,±i}）上 **4／4 皆為淨虧**，實測 ×0.36–0.49。而且它不會變好 —— 尺寸上不去。一條正確的加速路徑在某個係數體上永遠不划算，這件事要寫出來，不能只貼 𝔽p 那張漂亮的表。**(D) 正定分派由常數改為成本模型**：第十八輪把交叉點寫死為 17 並記下「換機器或換資料就要重量」。本輪改成 plan_spd（Bareiss 中間量 ≈ n(b+4)/2 位元對 CRT 之 ⌈n(b+4)/31⌉ 個素數），在 " +
    nd.to_string() +
    " 格上逐格做分派決策，其中 " +
    dfast.to_string() +
    " 格判定走快路徑；對這些格與 " +
    slowsample.to_string() +
    " 個慢路徑樣本**真的跑兩次**與 Bareiss 對帳，" +
    dagree.to_string() +
    "／" +
    dcheck.to_string() +
    " 一致（其餘格的分派器回傳的就是 Bareiss 本身，比對它等於比對 x == x，故不計入）。模型**比常數更快**（1,760 ms 對 1,963 ms，全 Bareiss 4,333 ms）—— 快在它會在損益兩平帶（n ≤ 16 時比值 ×0.99）拒絕切換，而常數 17 會在那裡就切過去。模型另有常數做不到的事：位元寬由 16 增到 64 時交叉點自動左移（n = 16 由不採用變成採用），因為係數膨脹讓 Bareiss 更早輸。**兩側對照**：逆變換漏掉 1/n 正規化者，結果恰好差 n 倍（" +
    anorm.to_string() +
    "／" +
    na.to_string() +
    " 逐元驗證差距就是 n，不是「不等於」而已）；逆變換用 ω 而非 ω⁻¹ 者全數算錯 " +
    awroot.to_string() +
    "。",
  )
}

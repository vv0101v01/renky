///|
/// N-52 之義務：D 群 × 空間 × 構造子 全量普查。
///
/// 要驗的不是「普查跑得完」，而是三件事：
///   (1) 每一格的判準式是**該條目的定理本身**，不是「程式沒崩潰」
///   (2) 判準式有鑑別力 —— 故意弄壞的空間必須被抓出來
///   (3) 分層與全量一致 —— 種子只由格鍵決定，與枚舉順序、旋鈕無關
pub fn ob_n52() -> Check {
  let mut ok = true
  let algos = d_registry()
  if algos.length() != 23 {
    ok = false
  }

  // 代碼互異且恰為 D-01 … D-23
  let mut dup = 0
  for i in 0..<algos.length() {
    for j in (i + 1)..<algos.length() {
      if algos[i].dcode == algos[j].dcode {
        dup = dup + 1
      }
    }
  }
  if dup != 0 {
    ok = false
  }

  // ── 分層普查（義務層）──────────────────────────────────
  // 步長 13、構造後維數上限 12。全量 5,635 格由 cmd/dcensus 承接。
  let st = dcensus_stratum(13, 12)
  if st.cells != 419 || st.pass != 419 || st.fail != 0 {
    ok = false
  }
  // 命題 N52-3：分層仍覆蓋全表（實際覆蓋度，不靠論證）
  if st.cov.0 != 35 || st.cov.1 != 7 || st.cov.2 != 23 {
    ok = false
  }
  if st.digest != "419:419:674552611" {
    ok = false
  }

  // ── 命題 N52-2（旋鈕不改變裁決）─────────────────────────
  // 同一組格在兩種旋鈕下必須給出完全相同的結果。取 D-15 單條，
  // 一次以子集掃描、一次以全量掃描後比對該條之統計。
  let sub = dcensus_subset(["D-15"], 12)
  let mut sub_ref_cells = 0
  let mut sub_ref_pass = 0
  for r in space_registry() {
    for c in comb7_registry() {
      if (c.cdim)(r.sdim) > 12 {
        continue
      }
      let key = dcell_key("D-15", c.csym, r.sname)
      let sp = comb7_space(r, c)
      sub_ref_cells = sub_ref_cells + 1
      for a in algos {
        if a.dcode == "D-15" && (a.drun)(sp, dcell_rng(key)) {
          sub_ref_pass = sub_ref_pass + 1
        }
      }
    }
  }
  if sub.cells != sub_ref_cells || sub.pass != sub_ref_pass {
    ok = false
  }
  if sub.fail != 0 {
    ok = false
  }

  // ── 鑑別力：公理歸因（命題 N52-4）──────────────────────
  // 三個壞 Gram 各破壞一條內積公理：不定型破壞正定性、非對稱型破壞
  // 對稱性、退化型破壞非退化性。一條判準式在「壞 X」上仍然成立，
  // 表示它的證明沒有用到公理 X。逐條量測即得依賴圖，同時是鑑別力證據。
  // 義務跑 6 組樣本；cmd/dcensus 跑 24 組（樣本愈多，推翻愈多 —— 這是
  // 反例搜尋，不是估計，故兩組數字都要記下來各自屬於哪個樣本量）。
  let (fi, fn_, fd, any, none, gd) = dcensus_axiom_stats_n(6)
  if fi != 3 || fn_ != 11 || fd != 3 {
    ok = false
  }
  if any != 16 || none != 7 {
    ok = false
  }
  // 正定型上 23 條必須全部成立 —— 否則上面的推翻可能只是判準式恆假
  if gd != 23 {
    ok = false
  }
  // 逐條指名，不是只看總數：恆真的判準式會讓總數對、指名錯
  let prof = dcensus_axiom_profile_n(6)
  let mut named = 0
  for p in prof {
    let expect_i = p.0 == "D-04" || p.0 == "D-13" || p.0 == "D-14"
    let expect_d = p.0 == "D-01" || p.0 == "D-08" || p.0 == "D-09"
    let expect_n = p.0 == "D-01" ||
      p.0 == "D-02" ||
      p.0 == "D-06" ||
      p.0 == "D-07" ||
      p.0 == "D-10" ||
      p.0 == "D-11" ||
      p.0 == "D-12" ||
      p.0 == "D-16" ||
      p.0 == "D-18" ||
      p.0 == "D-19" ||
      p.0 == "D-21"
    if p.1 == expect_i && p.2 == expect_n && p.3 == expect_d {
      named = named + 1
    }
  }
  if named != 23 {
    ok = false
  }

  mk_check(
    "N-52 D 群 × 空間 × 構造子 全量普查",
    ok,
    st.cells + sub.cells + sub_ref_cells + 23 * 24,
    "普查格是三元組 (A, S, C)：A 為 D 群 23 條內積演算法之一，S 為 35 個註冊空間之一（N-50），C 為 7 個構造子之一（N-51），共 23 × 35 × 7 = 5,635 格。每格的值是「A 的判準式在 ⟦C(S)⟧ 上是否逐例成立」，而判準式就是該條目的定理結論本身，不是「程式沒有崩潰」—— 例如 D-15 判 P² = P ∧ GP = PᵀG，D-15 判平行四邊形缺陷恰為 0，D-22 判正規方程 Gc = b 精確成立且殘差與子空間正交。全量實測：5,635 格全數成立，0 格推翻，構造後維數最高 28（Λ² 作用於 ℍ²），指紋 5635:5635:386251483，由 cmd/dcensus 一次性承接。常規義務跑分層層：步長 13、構造後維數上限 12，共 " +
    st.cells.to_string() +
    " 格全數成立，指紋 " +
    st.digest +
    "，實際覆蓋 " +
    st.cov.0.to_string() +
    " 個空間 / " +
    st.cov.1.to_string() +
    " 個構造子 / " +
    st.cov.2.to_string() +
    " 條演算法（覆蓋度是數出來的，不是由互質性論證出來的）。分層與全量一致之根據同 N-42 命題 201-3a：每格的亂數種子取自 str_hash64(格鍵)，與枚舉順序與三個旋鈕皆無關；義務另以 D-15 單條做子集／全量對照，" +
    sub.cells.to_string() +
    " 格逐格相符。鑑別力以公理歸因自證（命題 N52-4）：準備三個壞 Gram，各破壞內積的一條公理 —— 不定型 diag(1,−1,−1) 破壞正定性、非對稱型 [[2,1,0],[0,2,1],[0,0,2]] 破壞對稱性、退化型 diag(1,1,0) 破壞非退化性 —— 再把 23 條判準式各跑 6 組樣本。實測被推翻者（義務層 6 組樣本）：不定型 " +
    fi.to_string() +
    " 條（D-04 Gram 行列式非負、D-13 Cauchy–Schwarz 鬆弛量非負、D-14 三角不等式，即陳述中用到正定性者）、非對稱型 " +
    fn_.to_string() +
    " 條（D-01 D-02 D-06 D-07 D-10 D-11 D-12 D-16 D-18 D-19 D-21，即正交性與自伴性相關者）、退化型 " +
    fd.to_string() +
    " 條（D-01 D-08 D-09，即需要 Gram 可逆者）。至少被一種推翻 " +
    any.to_string() +
    "/23，三種都沒推翻 " +
    none.to_string() +
    "/23（D-03 D-05 D-14 D-15 D-17 D-20 D-22 —— 在 6 組樣本內未被這三種破壞擊倒）。樣本量加到 24 組（cmd/dcensus）時推翻數升為 8／13／3，至少被一種推翻 17 條、三種都沒推翻 6 條（D-03 D-05 D-15 D-17 D-20 D-22）—— 這是反例搜尋不是估計，樣本愈多推翻只增不減，故兩組數字必須各自註明樣本量。換回正定的 E³，23 條全部成立 " +
    gd.to_string() +
    "/23。義務不只核總數，還逐條核指名（不定型與退化型的名單各自逐條比對，23/23 相符）—— 只核總數的話，一條恆假的判準式可以把總數湊對。只驗推翻分不出「判準嚴格」與「判準恆假」，只驗成立分不出「判準正確」與「判準恆真」，兩側加指名才構成約束。ℚ 上不需要容差：35 個空間的 Gram 皆為 ℚ 上對稱正定矩陣，7 個構造子保持此性質（定理 N51-1），故判準式用逐位相等判定；兩個例外是 D-03（判定的正是「ℚ 不對開方封閉」）與 D-23（夾角本來就落在 ℝ，用 1e-9 容差）。Fourier／Bessel／Parseval 三條採非正規化形式 ⟨x,eᵢ⟩/⟨eᵢ,eᵢ⟩，原因同上 —— ℚ 上一般取不到單位長度的正交基。",
  )
}

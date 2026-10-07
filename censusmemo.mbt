///|
/// # N-77 普查備忘錄（memoisation），以及它為什麼會讓義務變成恆真
///
/// ## 量出來的重複
///
/// 第十一輪剖析 N 群時發現一件單純的事：同一個普查被算了好幾遍。
/// `tri_product(空間, 構造子, D群, 17, 12)` —— 774 格、3.5 秒 —— 出現在
///
/// ```text
///   oblig_tri.mbt:213   N-61 的 ext（與字面常數 774:774:352759555 對帳）
///   oblig_tri.mbt:338   N-62 的 fresh（與生成原始碼中嵌入的數字對帳）
///   gencensus.mbt:97    gen_census_row
///   gencensus.mbt:245   gen_census_src ——  而 N-62 呼叫它兩次
/// ```
///
/// 五次，約 17.5 秒。`tri_product` 是純函數（表是決定性建出來的，
/// 格鍵決定亂數種子），所以這五次的結果必然相同。
///
/// ## 陷阱：備忘錄會讓「決定性」這類義務變成恆真
///
/// 這不是一個「加個快取就好」的題目。N-62 的兩條主張分別是
///
/// ```text
///   (1) 生成器是決定性的   —— 連呼叫兩次，輸出逐字元相同
///   (2) 生成的原始碼忠實   —— 重跑普查，數字與嵌進去的那些相同
/// ```
///
/// 若把備忘錄無差別地接上去，(1) 退化成「備忘錄回傳了同一個物件兩次」、
/// (2) 退化成「同一個物件等於它自己」。兩條義務都還會通過，
/// 而且**通過得更快** —— 這正是最危險的失效模式：測試還在、訊號沒了。
///
/// ## 定義（繞過不變量）
///
/// 本條採用的規則，寫成可檢查的形式：
///
/// ```text
///   每一個被備忘的鍵，在義務集合中至少還有一處「繞過備忘錄、
///   獨立重算、並與字面常數對帳」的呼叫點。
/// ```
///
/// 具體分工：
///
/// ```text
///   備忘    N-61 的三個掃描、gen_census_src / gen_census_row 內部
///   繞過    N-62 的 fresh 與 cfresh（直接呼叫 tri_product）
/// ```
///
/// 於是 (2) 保持實質：N-62 真的重算了一次 774 格，拿去對生成碼裡的數字。
/// 而 (1) 的實質內容本來就不是「普查是純函數」（那由 N-61 對字面常數的
/// 比對獨立釘死），而是「生成器的字串組裝不依賴外部可變狀態」——
/// 字串組裝那一段並沒有被備忘。
///
/// ## 定理 N-77-1（備忘錄之健全性）
///
/// 若鍵函數 κ 滿足「κ(x) = κ(y) ⇒ f(x) = f(y)」，則以 κ 為鍵的備忘錄
/// 對 f 之任何呼叫序列皆回傳與 f 相同之值。
///
/// 證明：歸納於呼叫序列。未命中時直接呼叫 f，值正確；命中時回傳的是
/// 先前某次以同鍵存入之 f(y)，而由前提 f(y) = f(x)。∎
///
/// 本條之 κ 取「三張表之名稱 + 表項標籤之串接 + step + maxdim」。
/// 表項標籤串接是必要的：只用表名會讓「同名但內容不同的表」撞鍵，
/// 那正是 κ 的前提被違反的情形。
///
/// ## 兩側對照
///
/// 健全性不能只靠上面那段證明 —— 證明管的是演算法，不是這份實作。
/// `tri_memo_poison` 刻意往備忘錄塞一個錯的結果；
/// 義務要求「繞過重算 vs 備忘錄回傳」的比對**必須當場抓到**。
/// 抓不到，就表示那個比對是空的。

///|
/// 備忘錄本體。
pub struct TriMemo {
  mkeys : Array[String]
  mvals : Array[TriCensus]
  mut mhits : Int
  mut mmiss : Int
}

///|
/// 全域單例。
let g_trimemo : TriMemo = { mkeys: [], mvals: [], mhits: 0, mmiss: 0, }

///|
/// 一張表之內容摘要（名稱 + 全部表項標籤）。
pub fn tri_table_tag(t : TriTable) -> String {
  let mut s = t.ttname + "#" + t.ttitems.length().to_string() + "["
  for it in t.ttitems {
    s = s + tri_label(it) + ","
  }
  s + "]"
}

///|
/// 鍵函數 κ。
pub fn tri_memo_key(
  ta : TriTable,
  tb : TriTable,
  tc : TriTable,
  step : Int,
  maxdim : Int,
) -> String {
  tri_table_tag(ta) +
  "|" +
  tri_table_tag(tb) +
  "|" +
  tri_table_tag(tc) +
  "|s" +
  step.to_string() +
  "|d" +
  maxdim.to_string()
}

///|
/// 帶備忘錄之普查。語意與 `tri_product` 完全相同（定理 N-77-1）。
pub fn tri_product_memo(
  ta : TriTable,
  tb : TriTable,
  tc : TriTable,
  step : Int,
  maxdim : Int,
) -> TriCensus {
  let k = tri_memo_key(ta, tb, tc, step, maxdim)
  for i in 0..<g_trimemo.mkeys.length() {
    if g_trimemo.mkeys[i] == k {
      g_trimemo.mhits = g_trimemo.mhits + 1
      return g_trimemo.mvals[i]
    }
  }
  let v = tri_product(ta, tb, tc, step, maxdim)
  g_trimemo.mmiss = g_trimemo.mmiss + 1
  g_trimemo.mkeys.push(k)
  g_trimemo.mvals.push(v)
  v
}

///|
/// （命中數, 未命中數, 已存鍵數）
pub fn tri_memo_stats() -> (Int, Int, Int) {
  (g_trimemo.mhits, g_trimemo.mmiss, g_trimemo.mkeys.length())
}

///|
/// 清空備忘錄（義務中用來做可重複的量測）。
pub fn tri_memo_reset() -> Unit {
  g_trimemo.mkeys.clear()
  g_trimemo.mvals.clear()
  g_trimemo.mhits = 0
  g_trimemo.mmiss = 0
}

///|
/// 兩側對照用：刻意往備忘錄塞一個錯的結果。
///
/// 存在於產品程式碼中是刻意的 —— 對照若只活在測試檔裡，
/// 下一個重構的人不會知道那條比對是靠什麼撐住的。
pub fn tri_memo_poison(
  ta : TriTable,
  tb : TriTable,
  tc : TriTable,
  step : Int,
  maxdim : Int,
  bogus : TriCensus,
) -> Unit {
  let k = tri_memo_key(ta, tb, tc, step, maxdim)
  for i in 0..<g_trimemo.mkeys.length() {
    if g_trimemo.mkeys[i] == k {
      g_trimemo.mvals[i] = bogus
      return
    }
  }
  g_trimemo.mkeys.push(k)
  g_trimemo.mvals.push(bogus)
}

// cmd/audit — 逐條目量測（TSV 輸出，供評估報告使用）
// 欄位：code / zh / cat / track / instances / ok / usec

///|
fn main {
  let cat = @hilbert.catalogue()
  println("code\tzh\tcat\ttrack\tinstances\tok\tusec")
  for a in cat {
    let t0 = @bench.monotonic_clock_start()
    let c = (a.run)()
    let us = @bench.monotonic_clock_end(t0)
    println(
      a.code +
      "\t" +
      a.zh +
      "\t" +
      a.cat +
      "\t" +
      a.track +
      "\t" +
      c.trials.to_string() +
      "\t" +
      (if c.ok { "1" } else { "0" }) +
      "\t" +
      us.to_int64().to_string(),
    )
  }
}

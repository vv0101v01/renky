// cmd/audit — 逐條目量測（TSV 輸出，供評估報告使用）
// 欄位：code / zh / cat / track / instances / ok / usec

///|
fn main {
  let cat = @hilbert.catalogue()
  println("code\tzh\tcat\ttrack\tinstances\tok\tusec\tpolicy\ttier")
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
      us.to_int64().to_string() +
      "\t" +
      (if @hilbert.trial_governed(a.code) {
        let want = @hilbert.trial_policy(a.code)
        if c.trials == want {
          "ok:" + want.to_string()
        } else {
          "VIOLATION want=" + want.to_string()
        }
      } else {
        "-"
      }) +
      "\t" +
      // 【第十六輪】成本層別對帳：登記的層別必須與實測每實例成本相符。
      // 層別表是常數，而成本會變；沒有這一欄，表會悄悄腐壞。
      (if @hilbert.trial_governed(a.code) && c.trials > 0 {
        let per = us / 1000.0 / c.trials.to_double()
        let t = @hilbert.trial_tier(a.code)
        if @hilbert.trial_tier_ok(a.code, per) {
          "t" + t.to_string()
        } else {
          "TIERDRIFT t" + t.to_string() + " 實測=" + @hilbert.fmt_d(per, 3)
        }
      } else {
        "-"
      }),
    )
  }
}

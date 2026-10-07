// 零第三方依賴 (zero third-party dependencies).
// 本模組只使用 MoonBit 編譯器自帶之 core/builtin 原生型別，
// 沒有任何 `import` 條目 —— 連 @math 都不用（sqrt/sin/cos 自行實作）。

name = "axiom/hilbert"

version = "0.1.2"

readme = "README.md"

repository = ""

license = "Apache-2.0"

keywords = [
  "linear-algebra",
  "inner-product-space",
  "formal-verification",
  "exterior-algebra",
  "quaternion",
]

preferred_target = "wasm"

// 警告政策：
// 1. impl 之方法掛載一律以顯式 extend 宣告（見 rational.mbt / complex.mbt）；
//    本專案一律以 Trait::method 明確呼叫，故該處以 #deprecated 標記推廣。
// 2. 下列六類選擇性警告一律常開（現況皆為 0，做為迴歸門檻）：
//    missing_doc、unqualified_record、prefer_readonly_array、
//    missing_invariant、missing_reasoning、unnecessary_annotation。
//    其中後兩條互相牽制之寫法已定案：結構字面值一律以 T::{…} 顯式前綴表達型別，
//    而不再重複 let 之型別標註（`let vs = VSpace::{…}`），故兩條同時成立。

warnings = "+missing_doc+unqualified_record+prefer_readonly_array+missing_invariant+missing_reasoning+unnecessary_annotation"

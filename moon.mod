// 零第三方依賴 (zero third-party dependencies).
// 本模組只使用 MoonBit 編譯器自帶之 core/builtin 原生型別，
// 沒有任何 `import` 條目 —— 連 @math 都不用（sqrt/sin/cos 自行實作）。

name = "axiom/hilbert"

version = "1.1.0"

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

// 只關閉「trait impl 自動推廣為方法」之提示：本專案一律以 Trait::method 明確呼叫。

warnings = "-implicit_impl_as_method"

description = "公理化向量空間與有限維內積空間：18 種具體空間建構 + 7 類空間構造子 + 168 條衍生演算法 + 168 條自證義務（含 28 條純 CRT 加速層，附正向性自證）"

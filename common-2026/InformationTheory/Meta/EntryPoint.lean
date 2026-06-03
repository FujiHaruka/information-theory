/-
  InformationTheory/Meta/EntryPoint.lean — orphan detection 用 tag attribute

  `@[entry_point]` で declaration をマークすると、`scripts/FindOrphans.lean`
  が BFS root として扱う。`InformationTheory.*` 名前空間配下で、いずれの entry point
  からも transitively reachable でない declaration は orphan として報告される。

  `@[simp]` / `@[ext]` / `instance` 属性持ちは検出器側で自動的に root 扱いに
  なるので、明示的に `@[entry_point]` を付ける必要はない。
-/
import Lean

open Lean

namespace InformationTheory.Meta

initialize entryPointAttr : TagAttribute ←
  registerTagAttribute `entry_point
    "marks a top-level declaration as an orphan-detection BFS root"

end InformationTheory.Meta

/-
  The `@[entry_point]` tag attribute for orphan detection.

  Marking a declaration with `@[entry_point]` makes `scripts/FindOrphans.lean` treat it as
  a BFS root. Any declaration under the `InformationTheory.*` namespace that is not
  transitively reachable from some entry point is reported as an orphan.

  Declarations carrying `@[simp]` / `@[ext]` / `instance` are treated as roots automatically
  by the detector, so they need no explicit `@[entry_point]`.
-/
import Lean

open Lean

namespace InformationTheory.Meta

initialize entryPointAttr : TagAttribute ←
  registerTagAttribute `entry_point
    "marks a top-level declaration as an orphan-detection BFS root"

end InformationTheory.Meta

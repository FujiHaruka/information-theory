/-
  scripts/SorryAudit.lean — sorry 影響範囲監査 (aggregate)

  `Common2026/*.lean` (Draft/ 含む) の全 thm / def を `Lean.collectAxioms` で走査し、
  `sorryAx` への推移的依存を 3 分類して count する。

  ## 出力

    sorry-free       : 推移的に sorry に依存しない (完全に証明された)
    own sorry        : 宣言自身の body / type に sorry を持つ
    transitive only  : 自身は sorry なし、依存先に sorry を持つ宣言あり

  ## 実行

    lake env lean scripts/SorryAudit.lean

  Per-module 内訳は `scripts/SorryAuditPerModule.lean`。
-/
import Lean
import Common2026

open Lean

namespace Common2026.SorryAudit

structure Counts where
  envTotal         : Nat := 0  -- env.constants 全 visit 数 (Mathlib 込み)
  inCommon2026     : Nat := 0  -- そのうち Common2026/*.lean で定義
  internalFiltered : Nat := 0  -- そのうち isInternal で除外
  thmCount         : Nat := 0  -- そのうち theorem / lemma
  defCount         : Nat := 0  -- そのうち def / abbrev
  otherKind        : Nat := 0  -- ctor / rec / inductive / axiom 等
  sorryFree        : Nat := 0
  ownSorry         : Nat := 0
  transOnly        : Nat := 0
  deriving Inhabited

/-- declaration の **body / type 自体** に `sorryAx` が直接出現するか。 -/
def hasOwnSorry (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo v)    => v.value.hasSorry || v.type.hasSorry
  | some (.defnInfo v)   => v.value.hasSorry || v.type.hasSorry
  | some (.opaqueInfo v) => v.value.hasSorry || v.type.hasSorry
  | some (.axiomInfo v)  => v.type.hasSorry
  | _                    => false

/-- `Common2026/*.lean` で定義された declaration を `getModuleIdxFor?` 経由で識別。
    namespace prefix は project 全体で統一されていない (`InformationTheory.*` / `MACCode` 等
    多数) ため、module path で filter する。 -/
def audit : MetaM Counts := do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let prefix' : Name := `Common2026
  let mut c : Counts := {}
  for (n, info) in env.constants.toList do
    c := { c with envTotal := c.envTotal + 1 }
    -- declaration が `Common2026/*.lean` で定義されたか
    let some modIdx := env.getModuleIdxFor? n | continue
    let modName := moduleNames[modIdx.toNat]!
    unless prefix'.isPrefixOf modName do continue
    c := { c with inCommon2026 := c.inCommon2026 + 1 }
    if n.isInternal then
      c := { c with internalFiltered := c.internalFiltered + 1 }
      continue
    let kind : Option Bool :=
      match info with
      | .thmInfo _  => some true
      | .defnInfo _ => some false
      | _           => none
    match kind with
    | some true  => c := { c with thmCount := c.thmCount + 1 }
    | some false => c := { c with defCount := c.defCount + 1 }
    | none       => c := { c with otherKind := c.otherKind + 1 }; continue
    let axs ← Lean.collectAxioms n
    let dependsOnSorry := axs.contains ``sorryAx
    if dependsOnSorry then
      if hasOwnSorry env n then
        c := { c with ownSorry := c.ownSorry + 1 }
      else
        c := { c with transOnly := c.transOnly + 1 }
    else
      c := { c with sorryFree := c.sorryFree + 1 }
  return c

end Common2026.SorryAudit

open Common2026.SorryAudit in
#eval! show MetaM Unit from do
  let c ← audit
  let total := c.thmCount + c.defCount
  IO.println s!"==== Common2026 sorry audit ===="
  IO.println s!"env.constants total                : {c.envTotal}"
  IO.println s!"  defined in Common2026/*.lean     : {c.inCommon2026}"
  IO.println s!"    internal (auto-gen) excluded   : {c.internalFiltered}"
  IO.println s!"    theorems                       : {c.thmCount}"
  IO.println s!"    definitions                    : {c.defCount}"
  IO.println s!"    other (ctor/rec/ind/ax)        : {c.otherKind}"
  IO.println s!""
  IO.println s!"Audited (thm + def, non-internal)  : {total}"
  IO.println s!"  ✓ sorry-free (transitively clean): {c.sorryFree}"
  IO.println s!"  ✗ has own sorry                  : {c.ownSorry}"
  IO.println s!"  ⚠ transitively contaminated only : {c.transOnly}"
  IO.println s!""
  if total > 0 then
    let pct := (c.sorryFree * 10000) / total
    IO.println s!"  sorry-free ratio: {pct / 100}.{pct % 100 / 10}{pct % 10}%"

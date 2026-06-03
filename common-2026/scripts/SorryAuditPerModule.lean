/-
  scripts/SorryAuditPerModule.lean — per-module sorry 内訳

  `SorryAudit.lean` の集計版を **module 単位** に分解して出力する。InformationTheory/Draft/
  への file 移動候補リストを得るための入力。

  ## 出力

    PER-MODULE TABLE  Module                              total clean own trans
    MOVE LIST         InformationTheory/Draft/ へ移すべき module path 一覧
                      (own > 0 または trans > 0 のもの)
    KEEP LIST         main 側に残す module path (clean のみ)

  ## 実行

    lake env lean scripts/SorryAuditPerModule.lean
-/
import Lean
import InformationTheory

open Lean

namespace Tooling.SorryAuditPerModule

structure ModCounts where
  clean : Nat := 0
  own   : Nat := 0
  trans : Nat := 0
  deriving Inhabited

def hasOwnSorry (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo v)    => v.value.hasSorry || v.type.hasSorry
  | some (.defnInfo v)   => v.value.hasSorry || v.type.hasSorry
  | some (.opaqueInfo v) => v.value.hasSorry || v.type.hasSorry
  | some (.axiomInfo v)  => v.type.hasSorry
  | _                    => false

def audit : MetaM (Std.HashMap Name ModCounts) := do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let prefix' : Name := `InformationTheory
  let mut acc : Std.HashMap Name ModCounts := {}
  for (n, info) in env.constants.toList do
    let some modIdx := env.getModuleIdxFor? n | continue
    let modName := moduleNames[modIdx.toNat]!
    unless prefix'.isPrefixOf modName do continue
    if n.isInternal then continue
    -- only count thm + def (skip ctor / rec / inductive / axiom etc.)
    match info with
    | .thmInfo _ | .defnInfo _ => pure ()
    | _ => continue
    let axs ← Lean.collectAxioms n
    let cur := acc.getD modName {}
    let next :=
      if axs.contains ``sorryAx then
        if hasOwnSorry env n then { cur with own := cur.own + 1 }
        else { cur with trans := cur.trans + 1 }
      else { cur with clean := cur.clean + 1 }
    acc := acc.insert modName next
  return acc

/-- `InformationTheory.Foo.Bar` → `InformationTheory/Foo/Bar.lean` -/
def moduleToPath (n : Name) : String :=
  n.toString.replace "." "/" ++ ".lean"

end Tooling.SorryAuditPerModule

open Tooling.SorryAuditPerModule in
#eval! show MetaM Unit from do
  let acc ← audit
  -- sort by module name (lex)
  let rows := acc.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let mut totalClean := 0
  let mut totalOwn := 0
  let mut totalTrans := 0
  let mut moveList : Array Name := #[]
  let mut keepList : Array Name := #[]
  IO.println s!"==== Per-module sorry breakdown ===="
  IO.println s!"{"Module".rightpad 70} {"total".rightpad 6} {"clean".rightpad 6} {"own".rightpad 5} {"trans".rightpad 6}"
  for (modName, c) in rows do
    let total := c.clean + c.own + c.trans
    if total = 0 then continue
    totalClean := totalClean + c.clean
    totalOwn   := totalOwn + c.own
    totalTrans := totalTrans + c.trans
    let modStr := modName.toString.rightpad 70
    IO.println s!"{modStr} {toString total |>.rightpad 6} {toString c.clean |>.rightpad 6} {toString c.own |>.rightpad 5} {toString c.trans |>.rightpad 6}"
    if c.own > 0 || c.trans > 0 then
      moveList := moveList.push modName
    else
      keepList := keepList.push modName
  IO.println s!""
  IO.println s!"==== Totals ===="
  IO.println s!"clean / own / trans  =  {totalClean} / {totalOwn} / {totalTrans}"
  IO.println s!"modules total        =  {rows.size}"
  IO.println s!"modules to MOVE      =  {moveList.size}"
  IO.println s!"modules to KEEP      =  {keepList.size}"
  IO.println s!""
  IO.println s!"==== MOVE LIST (file paths) ===="
  for modName in moveList do
    IO.println (moduleToPath modName)
  IO.println s!""
  IO.println s!"==== KEEP LIST (file paths) ===="
  for modName in keepList do
    IO.println (moduleToPath modName)

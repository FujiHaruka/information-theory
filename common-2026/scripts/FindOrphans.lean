/-
  scripts/FindOrphans.lean — entry-point reachability orphan detector

  `@[entry_point]` (`Common2026/Meta/EntryPoint.lean`) と `instance` 属性が
  付いた `Common2026.*` declaration を BFS root として、Expr 内の定数参照を
  辿って transitively reachable な集合を求める。`Common2026.*` 配下の
  declaration のうち、いずれの root からも到達不能なものを orphan として
  module 単位でグループ化して列挙する。

  ## 前提

  - **import 方向**: Common2026 → Mathlib → Lean core (Mathlib / Lean core
    から Common2026 への逆参照は構造上ありえない)。これにより BFS は
    Common2026 → Common2026 edge だけを追えば良く、Mathlib refs はそのまま
    捨てて構わない。
  - **root 自動判定**: `instance` 属性持ちは typeclass resolution で名前
    参照されないため自動的に root 扱い (false positive 回避)。
  - **未対応 (v1)**: `@[simp]` / `@[ext]` lemma で名前直接呼び出しされない
    ものは orphan 判定されうる。実出力を見て次版で root 拡張。
  - **既知の noise**: structure / inductive の auto-generated projection
    (`Foo.field1` 等) も BFS で見つからなければ orphan として出る。実用上は
    module 単位の絞り込みで人間が判断する。

  ## 実行

    lake env lean scripts/FindOrphans.lean
-/
import Lean
import Common2026
import Common2026.Meta.EntryPoint

open Lean

namespace Common2026.FindOrphans

/-- declaration が `Common2026/*.lean` で定義されたか (SorryAudit 流儀)。 -/
def isInCommon2026 (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some idx =>
    let modName := env.allImportedModuleNames[idx.toNat]!
    (`Common2026 : Name).isPrefixOf modName

/-- declaration の type / body Expr に直接出現する定数名集合。 -/
def refsOf (env : Environment) (n : Name) : NameSet :=
  let collect (e : Expr) (acc : NameSet) : NameSet :=
    e.foldConsts acc (fun m s => s.insert m)
  match env.find? n with
  | some (.thmInfo v)    => collect v.value (collect v.type {})
  | some (.defnInfo v)   => collect v.value (collect v.type {})
  | some (.opaqueInfo v) => collect v.value (collect v.type {})
  | some (.axiomInfo v)  => collect v.type {}
  | some (.ctorInfo v)   => collect v.type {}
  | some (.inductInfo v) => collect v.type {}
  | some (.recInfo v)    => collect v.type {}
  | some (.quotInfo v)   => collect v.type {}
  | none                 => {}

/-- BFS root 判定: `@[entry_point]` タグか `instance` 属性。 -/
def isRoot (env : Environment) (n : Name) : Bool :=
  Common2026.Meta.entryPointAttr.hasTag env n
  || Lean.Meta.isInstanceCore env n

/-- declaration の所属モジュール名 (orphan として表示する用)。 -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | none     => `unknown
  | some idx => env.allImportedModuleNames[idx.toNat]!

structure Report where
  totalCommon  : Nat := 0
  rootCount    : Nat := 0
  visitedCount : Nat := 0
  orphans      : Array Name := #[]
  deriving Inhabited

/-- メイン: Common2026.* 配下の decl を列挙し、root から BFS、orphan を集める。 -/
def run : MetaM Report := do
  let env ← getEnv
  -- Step 1: Common2026 配下の非 internal decl を列挙、roots を識別
  let mut commonNames : Array Name := #[]
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    unless isInCommon2026 env n do continue
    if n.isInternal then continue
    commonNames := commonNames.push n
    if isRoot env n then
      roots := roots.push n
  -- Step 2: BFS (Common2026 → Common2026 edge のみ追う)
  let mut visited : NameSet := {}
  let mut queue : Array Name := #[]
  for r in roots do
    visited := visited.insert r
    queue := queue.push r
  while h : queue.size > 0 do
    let n := queue[queue.size - 1]
    queue := queue.pop
    for ref in (refsOf env n).toList do
      if ! visited.contains ref && isInCommon2026 env ref then
        visited := visited.insert ref
        queue := queue.push ref
  -- Step 3: orphan = Common2026 ∖ visited
  let orphans := commonNames.filter (fun n => ! visited.contains n)
  return {
    totalCommon  := commonNames.size
    rootCount    := roots.size
    visitedCount := visited.size
    orphans      := orphans
  }

/-- module 名 → orphan decl 名 の Array Mapping を作る (module 単位で表示用)。 -/
def groupByModule (env : Environment) (orphans : Array Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for n in orphans do
    let modName := moduleOf env n
    let cur := m.getD modName #[]
    m := m.insert modName (cur.push n)
  return m

end Common2026.FindOrphans

open Common2026.FindOrphans in
#eval! show MetaM Unit from do
  let env ← getEnv
  let r ← run
  IO.println "==== Common2026 orphan detection ===="
  IO.println s!"Common2026 declarations (non-internal): {r.totalCommon}"
  IO.println s!"Roots (@[entry_point] or instance)    : {r.rootCount}"
  IO.println s!"Reachable from roots                  : {r.visitedCount}"
  IO.println s!"Orphans (unreachable)                 : {r.orphans.size}"
  IO.println ""
  -- module 単位でグループ化して表示
  let grouped := groupByModule env r.orphans
  let modSorted := grouped.toList.toArray.qsort
    (fun a b => a.1.toString < b.1.toString)
  for (modName, names) in modSorted do
    IO.println s!"--- {modName} ({names.size}) ---"
    let nameSorted := names.qsort (fun a b => a.toString < b.toString)
    for n in nameSorted do
      IO.println s!"  {n}"
    IO.println ""

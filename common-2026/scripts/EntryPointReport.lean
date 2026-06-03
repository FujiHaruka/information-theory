/-
  scripts/EntryPointReport.lean — 証明済み主定理カタログ

  `@[entry_point]` (`Common2026/Meta/EntryPoint.lean`) でマークされた
  `Common2026.*` 配下の主定理を列挙し、**proven**（sorry に依存しない）と
  **staged**（推移閉包に `sorryAx` を含む）に分けて module 単位でレポートする。

  `@[entry_point]` は orphan 検出の BFS root マーカーであって「証明完成」を
  主張するタグではない（CLAUDE.md「Definition of Done」）。本スクリプトは
  その root 集合を sorry 依存の有無で二分し、「証明済み主定理一覧」を作る。

  ## 判定方法（sorry 伝播の固定点）

  Mathlib は sorry-free なので、`sorryAx` への依存は必ず `Common2026.*`
  declaration を経由する。各 Common2026 decl について
    - 自身の body/type が `sorryAx` を直接参照するか（= 直接 sorry）
    - どの Common2026 decl を参照するか（伝播辺）
  を集め、直接 sorry 集合から逆辺を BFS して「sorry に到達する」decl 全体
  （tainted）を求める。entry_point のうち tainted を staged、残りを proven
  とする。`collectAxioms` を decl 毎に呼ぶより 1 パスで安い。

  ## 実行

    lake env lean scripts/EntryPointReport.lean
-/
import Lean
import Common2026
import Common2026.Meta.EntryPoint

open Lean

namespace Common2026.EntryPointReport

/-- declaration が `Common2026/*.lean` で定義されたか（FindOrphans 流儀）。 -/
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

/-- declaration の所属モジュール名。 -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | none     => `unknown
  | some idx => env.allImportedModuleNames[idx.toNat]!

/-- declaration が `theorem`/`lemma` か（def / structure 等と区別する用）。 -/
def isThm (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _                 => false

structure Report where
  total       : Nat := 0
  provenCount : Nat := 0
  stagedCount : Nat := 0
  proven      : Array Name := #[]
  staged      : Array Name := #[]
  deriving Inhabited

/-- メイン: entry_point を列挙し、sorry 伝播の固定点で proven / staged に二分。 -/
def run : MetaM Report := do
  let env ← getEnv
  let sorryName : Name := `sorryAx
  -- Step 1: Common2026 decl を走査し、entry_point / 直接 sorry / 逆辺を収集
  let mut entryPoints : Array Name := #[]
  let mut directSorry : Array Name := #[]
  let mut revAdj : Std.HashMap Name (Array Name) := {}
  for (n, _) in env.constants.toList do
    unless isInCommon2026 env n do continue
    if n.isInternal then continue
    if Common2026.Meta.entryPointAttr.hasTag env n then
      entryPoints := entryPoints.push n
    let refs := refsOf env n
    if refs.contains sorryName then
      directSorry := directSorry.push n
    for r in refs.toList do
      if isInCommon2026 env r && ! r.isInternal then
        let cur := revAdj.getD r #[]
        revAdj := revAdj.insert r (cur.push n)
  -- Step 2: 直接 sorry 集合から逆辺を BFS して tainted（sorry 到達）を確定
  let mut tainted : NameSet := {}
  let mut queue : Array Name := #[]
  for n in directSorry do
    unless tainted.contains n do
      tainted := tainted.insert n
      queue := queue.push n
  while h : queue.size > 0 do
    let m := queue[queue.size - 1]
    queue := queue.pop
    for n in (revAdj.getD m #[]) do
      unless tainted.contains n do
        tainted := tainted.insert n
        queue := queue.push n
  -- Step 3: entry_point を二分
  let (staged, proven) := entryPoints.partition (fun n => tainted.contains n)
  return {
    total       := entryPoints.size
    provenCount := proven.size
    stagedCount := staged.size
    proven      := proven
    staged      := staged
  }

/-- module 名 → decl 名 Array の mapping。 -/
def groupByModule (env : Environment) (names : Array Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for n in names do
    let modName := moduleOf env n
    let cur := m.getD modName #[]
    m := m.insert modName (cur.push n)
  return m

/-- module グループを名前順にソートして行に展開（kind 注記付き）。 -/
def renderGroups (env : Environment) (names : Array Name) : Array String := Id.run do
  let grouped := groupByModule env names
  let modSorted := grouped.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let mut lines : Array String := #[]
  for (modName, ds) in modSorted do
    lines := lines.push s!"--- {modName} ({ds.size}) ---"
    let dsSorted := ds.qsort (fun a b => a.toString < b.toString)
    for n in dsSorted do
      let kind := if isThm env n then "" else "  [def]"
      lines := lines.push s!"  {n}{kind}"
    lines := lines.push ""
  return lines

end Common2026.EntryPointReport

/-- 詳細レポートの出力先（project root からの相対 path）。 -/
def reportPath : System.FilePath := "scripts/entry-points-report.txt"

open Common2026.EntryPointReport in
#eval! show MetaM Unit from do
  let env ← getEnv
  let r ← run
  IO.println "==== Common2026 main-theorem catalogue (@[entry_point]) ===="
  IO.println s!"Entry points (主定理マーク)  : {r.total}"
  IO.println s!"  proven (sorry-free)       : {r.provenCount}"
  IO.println s!"  staged (uses sorryAx)     : {r.stagedCount}"
  IO.println s!"Detailed report             : {reportPath}"
  let mut lines : Array String := #[]
  lines := lines.push "==== Common2026 証明済み主定理一覧 (@[entry_point], sorry-free) ===="
  lines := lines.push s!"Entry points total : {r.total}"
  lines := lines.push s!"  proven           : {r.provenCount}"
  lines := lines.push s!"  staged           : {r.stagedCount}"
  lines := lines.push ""
  lines := lines.push "==================== PROVEN (sorry-free) ===================="
  lines := lines.push ""
  lines := lines ++ renderGroups env r.proven
  lines := lines.push "==================== STAGED (uses sorryAx) =================="
  lines := lines.push "（@[entry_point] だが推移閉包に sorry を含む = 未完成の主定理）"
  lines := lines.push ""
  lines := lines ++ renderGroups env r.staged
  IO.FS.writeFile reportPath (String.intercalate "\n" lines.toList ++ "\n")

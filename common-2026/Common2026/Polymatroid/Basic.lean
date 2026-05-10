import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Real.Basic

/-!
# Polymatroid

A polymatroid is a finite ground set together with a real-valued rank
function on its subsets satisfying three axioms (empty, monotone, submodular).

Mathlib does not (yet) carry a set-function `Polymatroid` / `Submodular`
structure (Matroid rank exists at `ℕ∞`-value, see
`Mathlib.Combinatorics.Matroid.Rank.ENat`); this file introduces the
`ℝ`-valued set-function version, mirroring the field style of
`Mathlib.Combinatorics.Matroid.Basic`.

The canonical example is the joint entropy of a finite collection of
random variables (`InformationTheory.Shannon.entropyPolymatroid` in
`Common2026/Shannon/Polymatroid.lean`).
-/

namespace Combinatorics

/-- A polymatroid is a finite ground set `ι` together with a real-valued
rank function on `Finset ι` satisfying:

* `rank ∅ = 0`               — the empty set has rank 0,
* `Monotone rank`             — rank is monotone in the subset relation,
* submodularity               — `rank (S ∪ T) + rank (S ∩ T) ≤ rank S + rank T`.

The ground set type `ι` only needs `[DecidableEq ι]` (for `Finset` union /
intersection); finiteness of `ι` itself is not required. -/
structure Polymatroid (ι : Type*) [DecidableEq ι] where
  /-- The real-valued rank function on subsets of the ground set. -/
  rank : Finset ι → ℝ
  /-- The rank of the empty set is zero. -/
  rank_empty : rank ∅ = 0
  /-- The rank function is monotone in the subset relation. -/
  rank_mono : Monotone rank
  /-- The rank function is submodular. -/
  rank_submodular :
    ∀ S T : Finset ι, rank (S ∪ T) + rank (S ∩ T) ≤ rank S + rank T

attribute [ext] Polymatroid

end Combinatorics

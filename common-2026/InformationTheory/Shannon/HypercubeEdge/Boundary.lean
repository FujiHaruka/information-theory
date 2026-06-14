import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LoomisWhitney

/-!
# Boolean hypercube edge-boundary bound

The edge boundary of a subset of the Boolean cube `Fin n → Bool`, defined combinatorially
via directed coordinate-flip pairs, together with an edge-isoperimetric lower bound obtained
from Loomis–Whitney and AM-GM.

## Main definitions

* `flipCoord i x` — flip the `i`-th coordinate of `x : Fin n → Bool`,
  i.e. `Function.update x i (!x i)`.
* `edgeBoundaryCount A` — the number of pairs `(x, i)` with `x ∈ A` and `flipCoord i x ∉ A`,
  in bijection with the unordered edges of the cube having exactly one endpoint in `A`.
* `internalEdgePairCount A` — the number of pairs `(x, i)` with `x ∈ A` and `flipCoord i x ∈ A`;
  it counts each unordered internal edge twice.

## Main statements

* `edge_total_count` — `edgeBoundaryCount A + internalEdgePairCount A = n * A.card`.
* `internal_pair_count_eq_projection_sum` —
  `internalEdgePairCount A + 2 * ∑ i, (projectionExcept i A).card = 2 * (n * A.card)`.
* `edgeBoundary_count_eq` —
  `edgeBoundaryCount A + n * A.card = 2 * ∑ i, (projectionExcept i A).card`.
* `sum_projection_card_ge_amgm` —
  `(n : ℝ) * (A.card)^((n-1)/n) ≤ ∑ i, ((projectionExcept i A).card : ℝ)`, from Loomis–Whitney
  and AM-GM.
* `edgeBoundary_ge_AMGM` — for nonempty `A`,
  `2 * n * (A.card)^((n-1)/n) ≤ edgeBoundaryCount A + n * A.card`, the additive form of
  `|∂_e A| ≥ 2n · |A|^{(n-1)/n} − n · |A|`.

## Implementation notes

The definitions avoid `SimpleGraph` and `Sym2`, working with naive combinatorial pairs to
sidestep the `SimpleGraph.edgeBoundary` API. Counting identities are stated additively to
avoid natural-number subtraction.
-/

namespace InformationTheory.Shannon

open Finset
open scoped BigOperators

/-! ## Coordinate flip and edge counts -/

/-- Flip the `i`-th coordinate of `x : Fin n → Bool`. -/
def flipCoord {n : ℕ} (i : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  Function.update x i (!x i)

@[simp] lemma flipCoord_apply_same {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    flipCoord i x i = !x i := by
  unfold flipCoord; simp

lemma flipCoord_apply_other {n : ℕ} (i : Fin n) (x : Fin n → Bool)
    {j : Fin n} (h : j ≠ i) :
    flipCoord i x j = x j := by
  unfold flipCoord; rw [Function.update_of_ne h]

@[simp] lemma flipCoord_flipCoord {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    flipCoord i (flipCoord i x) = x := by
  funext j
  by_cases h : j = i
  · subst h
    simp [flipCoord]
  · rw [flipCoord_apply_other i _ h, flipCoord_apply_other i x h]

/-- The number of pairs `(x, i)` with `x ∈ A` and `flipCoord i x ∉ A`, in bijection with the
cube edges having exactly one endpoint in `A`. -/
def edgeBoundaryCount {n : ℕ} (A : Finset (Fin n → Bool)) : ℕ :=
  (Finset.univ.filter
    (fun p : (Fin n → Bool) × Fin n => p.1 ∈ A ∧ flipCoord p.2 p.1 ∉ A)).card

/-- The number of pairs `(x, i)` with `x ∈ A` and `flipCoord i x ∈ A`, counting each internal
edge twice. -/
@[entry_point]
def internalEdgePairCount {n : ℕ} (A : Finset (Fin n → Bool)) : ℕ :=
  (Finset.univ.filter
    (fun p : (Fin n → Bool) × Fin n => p.1 ∈ A ∧ flipCoord p.2 p.1 ∈ A)).card

/-! ## Counting identities -/

/-- The pairs `(x, i)` with `x ∈ A` number `n * A.card`, split disjointly by whether
`flipCoord i x ∈ A`: `edgeBoundaryCount A + internalEdgePairCount A = n * A.card`. -/
@[entry_point]
theorem edge_total_count {n : ℕ} (A : Finset (Fin n → Bool)) :
    edgeBoundaryCount A + internalEdgePairCount A = n * A.card := by
  classical
  -- The two sets are disjoint (predicate negation) and union = {p : p.1 ∈ A}.
  set S : Finset ((Fin n → Bool) × Fin n) :=
    Finset.univ.filter (fun p => p.1 ∈ A) with hS_def
  -- edgeBoundaryCount A + internalEdgePairCount A = S.card
  have hsplit : edgeBoundaryCount A + internalEdgePairCount A = S.card := by
    unfold edgeBoundaryCount internalEdgePairCount
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp only [hS_def, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
      · intro hp
        by_cases h : flipCoord p.2 p.1 ∈ A
        · right; exact ⟨hp, h⟩
        · left; exact ⟨hp, h⟩
    · rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
      exact hp1.2 hp2.2
  -- S.card = n * A.card
  have hS_card : S.card = n * A.card := by
    have h1 : S = A ×ˢ (Finset.univ : Finset (Fin n)) := by
      ext p
      simp [hS_def, Finset.mem_product]
    rw [h1, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    ring
  rw [hsplit, hS_card]

/-! ## Projection identity

For each direction `i`, every fibre of `projectionExcept i A` is covered once or twice in `A`;
double-counting these coverages relates `∑ i, (projectionExcept i A).card` to `A.card` and the
edge boundary count, stated additively to avoid natural-number subtraction. -/

/-- `flipCoord i x ∈ A ↔ Function.update x i (!x i) ∈ A`, the definitional unfolding of
`flipCoord`. -/
@[entry_point]
lemma flipCoord_mem_iff {n : ℕ} (A : Finset (Fin n → Bool)) (x : Fin n → Bool)
    (i : Fin n) :
    flipCoord i x ∈ A ↔ Function.update x i (!x i) ∈ A := Iff.rfl

/-- The projection `(Fin n → Bool) → ({j // j ≠ i} → Bool)` dropping coordinate `i`. -/
def projMap {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    {j : Fin n // j ≠ i} → Bool := fun j => x j.val

/-- Extend a projection by the bit `b` at coordinate `i`. -/
def extension {n : ℕ} (i : Fin n) (b : Bool)
    (y : {j : Fin n // j ≠ i} → Bool) : Fin n → Bool :=
  fun j => if h : j = i then b else y ⟨j, h⟩

@[simp] lemma extension_apply_eq {n : ℕ} (i : Fin n) (b : Bool)
    (y : {j : Fin n // j ≠ i} → Bool) :
    extension i b y i = b := by
  unfold extension; simp

lemma extension_apply_ne {n : ℕ} (i : Fin n) (b : Bool)
    (y : {j : Fin n // j ≠ i} → Bool) {j : Fin n} (h : j ≠ i) :
    extension i b y j = y ⟨j, h⟩ := by
  unfold extension; rw [dif_neg h]

@[simp] lemma projMap_extension {n : ℕ} (i : Fin n) (b : Bool)
    (y : {j : Fin n // j ≠ i} → Bool) :
    projMap i (extension i b y) = y := by
  funext ⟨j, hj⟩
  show extension i b y j = y ⟨j, hj⟩
  rw [extension_apply_ne i b y hj]

lemma projectionExcept_eq_image {n : ℕ} (i : Fin n) (A : Finset (Fin n → Bool)) :
    projectionExcept i A = A.image (projMap i) := rfl

/-- `flipCoord i x` equals the extension of `projMap i x` by the flipped bit `!x i`. -/
lemma extension_projMap_flip {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    extension i (!x i) (projMap i x) = flipCoord i x := by
  funext j
  by_cases h : j = i
  · subst h; simp [flipCoord]
  · rw [extension_apply_ne i (!x i) (projMap i x) h, flipCoord_apply_other i x h]
    rfl

/-- `projMap i x = y ↔ x = extension i (x i) y`. -/
lemma projMap_eq_iff {n : ℕ} (i : Fin n) (x : Fin n → Bool)
    (y : {j : Fin n // j ≠ i} → Bool) :
    projMap i x = y ↔ x = extension i (x i) y := by
  constructor
  · intro h
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [extension_apply_ne i (x i) y hj]
      have := congrFun h ⟨j, hj⟩
      exact this
  · intro h
    rw [h]; exact projMap_extension i (x i) y

/-- The boundary contribution in direction `i`: elements `x ∈ A` with `flipCoord i x ∉ A`. -/
def boundaryDirSet {n : ℕ} (A : Finset (Fin n → Bool)) (i : Fin n) :
    Finset (Fin n → Bool) :=
  A.filter (fun x => flipCoord i x ∉ A)

lemma fiber_projMap_eq_union {n : ℕ} (A : Finset (Fin n → Bool)) (i : Fin n)
    (y : {j : Fin n // j ≠ i} → Bool) :
    A.filter (fun x => projMap i x = y) =
      ((({extension i false y} : Finset _).filter (· ∈ A)) ∪
       (({extension i true y} : Finset _).filter (· ∈ A))) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro ⟨hxA, hpx⟩
    have hxext : x = extension i (x i) y := (projMap_eq_iff i x y).mp hpx
    cases hb : x i with
    | false =>
      left
      exact ⟨by rw [hxext, hb], hxA⟩
    | true =>
      right
      exact ⟨by rw [hxext, hb], hxA⟩
  · rintro (⟨rfl, hxA⟩ | ⟨rfl, hxA⟩) <;>
    exact ⟨hxA, by simp⟩

lemma boundaryDirSet_fiber_projMap_eq_union {n : ℕ} (A : Finset (Fin n → Bool))
    (i : Fin n) (y : {j : Fin n // j ≠ i} → Bool) :
    (boundaryDirSet A i).filter (fun x => projMap i x = y) =
      ((({extension i false y} : Finset _).filter
          (fun x => x ∈ A ∧ extension i true y ∉ A)) ∪
       (({extension i true y} : Finset _).filter
          (fun x => x ∈ A ∧ extension i false y ∉ A))) := by
  classical
  ext x
  simp only [boundaryDirSet, Finset.mem_filter,
    Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hxA, hflip⟩, hpx⟩
    have hxext : x = extension i (x i) y := (projMap_eq_iff i x y).mp hpx
    cases hb : x i with
    | false =>
      left
      have hfliprw : flipCoord i x = extension i true y := by
        rw [← extension_projMap_flip i x, hpx, hb]
        rfl
      refine ⟨by rw [hxext, hb], hxA, ?_⟩
      rw [← hfliprw]; exact hflip
    | true =>
      right
      have hfliprw : flipCoord i x = extension i false y := by
        rw [← extension_projMap_flip i x, hpx, hb]
        rfl
      refine ⟨by rw [hxext, hb], hxA, ?_⟩
      rw [← hfliprw]; exact hflip
  · rintro (⟨rfl, hxA, hext1⟩ | ⟨rfl, hxA, hext0⟩)
    · refine ⟨⟨hxA, ?_⟩, ?_⟩
      · have : flipCoord i (extension i false y) = extension i true y := by
          funext j
          by_cases hj : j = i
          · subst hj; simp [flipCoord]
          · rw [flipCoord_apply_other i _ hj,
              extension_apply_ne i false y hj,
              extension_apply_ne i true y hj]
        rw [this]; exact hext1
      · simp
    · refine ⟨⟨hxA, ?_⟩, ?_⟩
      · have : flipCoord i (extension i true y) = extension i false y := by
          funext j
          by_cases hj : j = i
          · subst hj; simp [flipCoord]
          · rw [flipCoord_apply_other i _ hj,
              extension_apply_ne i true y hj,
              extension_apply_ne i false y hj]
        rw [this]; exact hext0
      · simp

lemma extension_false_ne_extension_true {n : ℕ} (i : Fin n)
    (y : {j : Fin n // j ≠ i} → Bool) :
    extension i false y ≠ extension i true y := by
  intro h
  have := congrFun h i
  simp at this

lemma extension_mem_of_mem_projectionExcept {n : ℕ} (A : Finset (Fin n → Bool))
    (i : Fin n) (y : {j : Fin n // j ≠ i} → Bool) (hy : y ∈ projectionExcept i A) :
    extension i false y ∈ A ∨ extension i true y ∈ A := by
  classical
  rw [projectionExcept_eq_image, Finset.mem_image] at hy
  obtain ⟨x, hxA, hxy⟩ := hy
  have hxext : x = extension i (x i) y := (projMap_eq_iff i x y).mp hxy
  cases hb : x i with
  | false =>
    left
    rw [hxext, hb] at hxA
    exact hxA
  | true =>
    right
    rw [hxext, hb] at hxA
    exact hxA

lemma two_eq_fiber_card_add_boundaryDirSet_fiber_card {n : ℕ}
    (A : Finset (Fin n → Bool)) (i : Fin n) (y : {j : Fin n // j ≠ i} → Bool)
    (hy : y ∈ projectionExcept i A) :
    2 = (A.filter (fun x => projMap i x = y)).card +
        ((boundaryDirSet A i).filter (fun x => projMap i x = y)).card := by
  classical
  have h_ext_ne : extension i false y ≠ extension i true y :=
    extension_false_ne_extension_true i y
  have h_y_in_A : extension i false y ∈ A ∨ extension i true y ∈ A :=
    extension_mem_of_mem_projectionExcept A i y hy
  rw [fiber_projMap_eq_union, boundaryDirSet_fiber_projMap_eq_union]
  rcases h_y_in_A with h0 | h1
  · -- h0 : extension i false y ∈ A
    by_cases h1 : extension i true y ∈ A
    · -- both in A: A.filter card = 2, bdir.filter card = 0
      rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · rw [show ({extension i false y} : Finset (Fin n → Bool)).filter (· ∈ A)
              = {extension i false y} from by
              apply Finset.filter_eq_self.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]; exact h0,
          show ({extension i true y} : Finset (Fin n → Bool)).filter (· ∈ A)
              = {extension i true y} from by
              apply Finset.filter_eq_self.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]; exact h1,
          show ({extension i false y} : Finset (Fin n → Bool)).filter
              (fun x => x ∈ A ∧ extension i true y ∉ A) = ∅ from by
              apply Finset.filter_eq_empty_iff.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]
              rintro ⟨_, h⟩; exact h h1,
          show ({extension i true y} : Finset (Fin n → Bool)).filter
              (fun x => x ∈ A ∧ extension i false y ∉ A) = ∅ from by
              apply Finset.filter_eq_empty_iff.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]
              rintro ⟨_, h⟩; exact h h0]
        simp [Finset.card_singleton]
      · apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_singleton]
        exact h_ext_ne
      · apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_singleton]
        exact h_ext_ne
    · -- only h0 in A: A.filter = {ext0}, bdir.filter = {ext0}
      rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · rw [show ({extension i false y} : Finset (Fin n → Bool)).filter (· ∈ A)
              = {extension i false y} from by
              apply Finset.filter_eq_self.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]; exact h0,
          show ({extension i true y} : Finset (Fin n → Bool)).filter (· ∈ A) = ∅ from by
              apply Finset.filter_eq_empty_iff.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]; exact h1,
          show ({extension i false y} : Finset (Fin n → Bool)).filter
              (fun x => x ∈ A ∧ extension i true y ∉ A) = {extension i false y} from by
              apply Finset.filter_eq_self.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]
              exact ⟨h0, h1⟩,
          show ({extension i true y} : Finset (Fin n → Bool)).filter
              (fun x => x ∈ A ∧ extension i false y ∉ A) = ∅ from by
              apply Finset.filter_eq_empty_iff.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]
              rintro ⟨h, _⟩; exact h1 h]
        simp [Finset.card_singleton]
      · apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_singleton]
        exact h_ext_ne
      · apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_singleton]
        exact h_ext_ne
  · -- h1 : extension i true y ∈ A
    by_cases h0 : extension i false y ∈ A
    · -- both in A: same as previous "both" case
      rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · rw [show ({extension i false y} : Finset (Fin n → Bool)).filter (· ∈ A)
              = {extension i false y} from by
              apply Finset.filter_eq_self.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]; exact h0,
          show ({extension i true y} : Finset (Fin n → Bool)).filter (· ∈ A)
              = {extension i true y} from by
              apply Finset.filter_eq_self.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]; exact h1,
          show ({extension i false y} : Finset (Fin n → Bool)).filter
              (fun x => x ∈ A ∧ extension i true y ∉ A) = ∅ from by
              apply Finset.filter_eq_empty_iff.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]
              rintro ⟨_, h⟩; exact h h1,
          show ({extension i true y} : Finset (Fin n → Bool)).filter
              (fun x => x ∈ A ∧ extension i false y ∉ A) = ∅ from by
              apply Finset.filter_eq_empty_iff.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]
              rintro ⟨_, h⟩; exact h h0]
        simp [Finset.card_singleton]
      · apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_singleton]
        exact h_ext_ne
      · apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_singleton]
        exact h_ext_ne
    · -- only h1 in A
      rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · rw [show ({extension i false y} : Finset (Fin n → Bool)).filter (· ∈ A) = ∅ from by
              apply Finset.filter_eq_empty_iff.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]; exact h0,
          show ({extension i true y} : Finset (Fin n → Bool)).filter (· ∈ A)
              = {extension i true y} from by
              apply Finset.filter_eq_self.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]; exact h1,
          show ({extension i false y} : Finset (Fin n → Bool)).filter
              (fun x => x ∈ A ∧ extension i true y ∉ A) = ∅ from by
              apply Finset.filter_eq_empty_iff.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]
              rintro ⟨h, _⟩; exact h0 h,
          show ({extension i true y} : Finset (Fin n → Bool)).filter
              (fun x => x ∈ A ∧ extension i false y ∉ A) = {extension i true y} from by
              apply Finset.filter_eq_self.mpr
              intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]
              exact ⟨h1, h0⟩]
        simp [Finset.card_singleton]
      · apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_singleton]
        exact h_ext_ne
      · apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_singleton]
        exact h_ext_ne

lemma boundaryPairCount_eq_boundaryDirSet_card {n : ℕ} (A : Finset (Fin n → Bool))
    (i : Fin n) :
    (Finset.univ.filter
        (fun p : (Fin n → Bool) × Fin n =>
          p.1 ∈ A ∧ flipCoord p.2 p.1 ∉ A ∧ p.2 = i)).card
      = (boundaryDirSet A i).card := by
  classical
  refine Finset.card_nbij' (fun (p : (Fin n → Bool) × Fin n) => p.1)
    (fun x => (x, i)) ?_ ?_ ?_ ?_
  · -- MapsTo: pair set → bdir
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    rw [Finset.mem_coe, boundaryDirSet, Finset.mem_filter]
    obtain ⟨_, hp1, hpflip, hp2⟩ := hp
    rw [← hp2]
    exact ⟨hp1, hpflip⟩
  · -- MapsTo: bdir → pair set
    intro x hx
    rw [Finset.mem_coe, boundaryDirSet, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hx.1, hx.2, rfl⟩
  · -- LeftInv: (p.1, i) = p when p.2 = i
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    have hp2 : p.2 = i := hp.2.2.2
    show (p.1, i) = p
    rw [← hp2]
  · intro x _; rfl

lemma two_mul_projectionExcept_card_eq {n : ℕ} (A : Finset (Fin n → Bool))
    (i : Fin n) :
    2 * (projectionExcept i A).card
      = A.card +
        (Finset.univ.filter
          (fun p : (Fin n → Bool) × Fin n =>
            p.1 ∈ A ∧ flipCoord p.2 p.1 ∉ A ∧ p.2 = i)).card := by
  classical
  rw [boundaryPairCount_eq_boundaryDirSet_card]
  -- Now: 2 * (projectionExcept i A).card = A.card + (boundaryDirSet A i).card.
  have hMapsTo : (A : Set (Fin n → Bool)).MapsTo (projMap i)
      (projectionExcept i A : Set _) := by
    intro x hxA
    rw [projectionExcept_eq_image]
    exact Finset.mem_image_of_mem _ hxA
  have h_A_sum : A.card
      = ∑ y ∈ projectionExcept i A, (A.filter (fun x => projMap i x = y)).card :=
    Finset.card_eq_sum_card_fiberwise hMapsTo
  have hMapsTo_bdir : (boundaryDirSet A i : Set (Fin n → Bool)).MapsTo (projMap i)
      (projectionExcept i A : Set _) := by
    intro x hxbdir
    rw [boundaryDirSet, Finset.coe_filter] at hxbdir
    exact hMapsTo hxbdir.1
  have h_bdir_sum : (boundaryDirSet A i).card
      = ∑ y ∈ projectionExcept i A,
          ((boundaryDirSet A i).filter (fun x => projMap i x = y)).card :=
    Finset.card_eq_sum_card_fiberwise hMapsTo_bdir
  have h_sum_2 :
      ∑ _y ∈ projectionExcept i A, (2 : ℕ)
        = ∑ y ∈ projectionExcept i A,
            ((A.filter (fun x => projMap i x = y)).card +
             ((boundaryDirSet A i).filter (fun x => projMap i x = y)).card) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact two_eq_fiber_card_add_boundaryDirSet_fiber_card A i y hy
  rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm, Finset.sum_add_distrib,
    ← h_A_sum, ← h_bdir_sum] at h_sum_2
  linarith

/-- `2 * ∑ i, (projectionExcept i A).card = n * A.card + edgeBoundaryCount A`, obtained by
classifying each projection fibre as singly or doubly covered in `A`. -/
theorem two_sum_projection_eq {n : ℕ} (A : Finset (Fin n → Bool)) :
    2 * ∑ i : Fin n, (projectionExcept i A).card
      = n * A.card + edgeBoundaryCount A := by
  classical
  -- Per-direction identity 2 * |projectionExcept i A| = |A| + (direction-i boundary pairs).
  have h_per_i : ∀ i : Fin n,
      2 * (projectionExcept i A).card
        = A.card +
          (Finset.univ.filter
            (fun p : (Fin n → Bool) × Fin n =>
              p.1 ∈ A ∧ flipCoord p.2 p.1 ∉ A ∧ p.2 = i)).card :=
    fun i => two_mul_projectionExcept_card_eq A i
  -- Sum h_per_i over i:
  have h_sum :
      ∑ i : Fin n, 2 * (projectionExcept i A).card
        = ∑ i : Fin n, (A.card + (Finset.univ.filter
            (fun p : (Fin n → Bool) × Fin n =>
              p.1 ∈ A ∧ flipCoord p.2 p.1 ∉ A ∧ p.2 = i)).card) := by
    apply Finset.sum_congr rfl
    intro i _; exact h_per_i i
  rw [← Finset.mul_sum] at h_sum
  rw [h_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  congr 1
  -- Remaining: Σ_i #{(x, j) : x ∈ A, flipCoord j x ∉ A, j = i} = edgeBoundaryCount A.
  -- This is a partition of the boundary set by the second coordinate.
  unfold edgeBoundaryCount
  -- Use Finset.card_eq_sum_card_fiberwise (or rewrite manually).
  symm
  rw [show (Finset.univ.filter
        (fun p : (Fin n → Bool) × Fin n =>
          p.1 ∈ A ∧ flipCoord p.2 p.1 ∉ A)).card
      = ∑ i : Fin n, ((Finset.univ.filter
          (fun p : (Fin n → Bool) × Fin n =>
            p.1 ∈ A ∧ flipCoord p.2 p.1 ∉ A)).filter (fun p => p.2 = i)).card from ?_]
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · -- card = Σ_i #(filter p.2 = i)
    rw [← Finset.card_eq_sum_card_fiberwise (f := fun p : (Fin n → Bool) × Fin n => p.2)
        (t := Finset.univ)]
    intro p _
    exact Finset.mem_univ _

/-- The internal edge pair count in projection-sum form:
`internalEdgePairCount A + 2 * ∑ i, (projectionExcept i A).card = 2 * (n * A.card)`. -/
@[entry_point]
theorem internal_pair_count_eq_projection_sum {n : ℕ}
    (A : Finset (Fin n → Bool)) :
    internalEdgePairCount A + 2 * ∑ i : Fin n, (projectionExcept i A).card
      = 2 * (n * A.card) := by
  have h1 := edge_total_count A
  have h2 := two_sum_projection_eq A
  omega

/-- The edge boundary in projection-sum form:
`edgeBoundaryCount A + n * A.card = 2 * ∑ i, (projectionExcept i A).card`. -/
theorem edgeBoundary_count_eq {n : ℕ} (A : Finset (Fin n → Bool)) :
    edgeBoundaryCount A + n * A.card
      = 2 * ∑ i : Fin n, (projectionExcept i A).card := by
  have := two_sum_projection_eq A
  omega

/-! ## Loomis–Whitney and AM-GM corollary -/

/-- `(n : ℝ) * (A.card)^((n-1)/n) ≤ ∑ i, ((projectionExcept i A).card : ℝ)`, combining the
Loomis–Whitney bound `∏ i, (projectionExcept i A).card ≥ A.card^(n-1)` with AM-GM. -/
@[entry_point]
theorem sum_projection_card_ge_amgm {n : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Finset (Fin n → α)} (hA : A.Nonempty) :
    (n : ℝ) * ((A.card : ℝ) ^ (n - 1 : ℕ)) ^ ((n : ℝ)⁻¹)
      ≤ ∑ i : Fin n, ((projectionExcept i A).card : ℝ) := by
  classical
  -- Three cases: n = 0 trivial (both sides 0); n ≥ 1 use LW + AM-GM.
  by_cases hn : n = 0
  · subst hn; simp
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos_R.ne'
  -- LW: A.card ^ (n-1) ≤ ∏ i, (projectionExcept i A).card.
  have h_LW : (A.card : ℝ) ^ (n - 1) ≤ ∏ i : Fin n, ((projectionExcept i A).card : ℝ) := by
    have h := loomis_whitney (A := A) hA
    have h2 := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at h2
    exact h2
  have h_proj_nn : ∀ i : Fin n, 0 ≤ ((projectionExcept i A).card : ℝ) := fun i => by
    exact_mod_cast Nat.zero_le _
  have h_A_nn : (0 : ℝ) ≤ A.card := by exact_mod_cast Nat.zero_le _
  have h_A_pow_nn : (0 : ℝ) ≤ (A.card : ℝ) ^ (n - 1) := pow_nonneg h_A_nn _
  -- AM-GM: ∏ z_i ^ (1/n) ≤ ∑ (1/n) * z_i
  have h_one_div_nn : (0 : ℝ) ≤ 1 / n := by positivity
  have h_w_sum : ∑ _i : Fin n, ((1 : ℝ) / n) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have h_GM_AM :=
    Real.geom_mean_le_arith_mean_weighted (s := (Finset.univ : Finset (Fin n)))
      (w := fun _ => (1 : ℝ) / n)
      (z := fun i => ((projectionExcept i A).card : ℝ))
      (fun _ _ => h_one_div_nn) h_w_sum (fun i _ => h_proj_nn i)
  -- ∏ z_i ^ (1/n) = (∏ z_i) ^ (1/n)
  have h_prod_rpow :
      ∏ i : Fin n, ((projectionExcept i A).card : ℝ) ^ ((1 : ℝ) / n)
        = (∏ i : Fin n, ((projectionExcept i A).card : ℝ)) ^ ((1 : ℝ) / n) :=
    Real.finsetProd_rpow Finset.univ _ (fun i _ => h_proj_nn i) _
  rw [h_prod_rpow] at h_GM_AM
  -- ∑ (1/n) * z_i = (1/n) * ∑ z_i
  rw [← Finset.mul_sum] at h_GM_AM
  -- LW + monotone rpow: (A.card^{n-1})^{1/n} ≤ (∏ z_i)^{1/n}
  have h_LW_rpow :
      ((A.card : ℝ) ^ (n - 1)) ^ ((1 : ℝ) / n)
        ≤ (∏ i : Fin n, ((projectionExcept i A).card : ℝ)) ^ ((1 : ℝ) / n) := by
    apply Real.rpow_le_rpow h_A_pow_nn h_LW h_one_div_nn
  -- Combine: (A.card^{n-1})^{1/n} ≤ (1/n) * ∑ z_i
  have h_combined :
      ((A.card : ℝ) ^ (n - 1)) ^ ((1 : ℝ) / n)
        ≤ (1 / n) * ∑ i : Fin n, ((projectionExcept i A).card : ℝ) :=
    h_LW_rpow.trans h_GM_AM
  -- Multiply both sides by n
  have h_final :
      (n : ℝ) * ((A.card : ℝ) ^ (n - 1)) ^ ((1 : ℝ) / n)
        ≤ ∑ i : Fin n, ((projectionExcept i A).card : ℝ) := by
    have := mul_le_mul_of_nonneg_left h_combined hn_pos_R.le
    rw [show (n : ℝ) * ((1 : ℝ) / n * ∑ i, ((projectionExcept i A).card : ℝ))
          = ((n : ℝ) * (1 / n)) * ∑ i, ((projectionExcept i A).card : ℝ) from by ring,
        show ((n : ℝ) * (1 / n)) = 1 from by field_simp] at this
    linarith
  -- Bridge (1/n) vs (n)⁻¹
  rw [show ((1 : ℝ) / n) = (n : ℝ)⁻¹ from by rw [one_div]] at h_final
  exact h_final

/-- The edge-isoperimetric lower bound: for nonempty `A ⊆ Fin n → Bool`,
`2 * n * (A.card)^((n-1)/n) ≤ edgeBoundaryCount A + n * A.card`, the additive form of
`|∂_e A| ≥ 2n · |A|^{(n-1)/n} − n · |A|`. -/
@[entry_point]
theorem edgeBoundary_ge_AMGM {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    2 * (n : ℝ) * ((A.card : ℝ) ^ (n - 1 : ℕ)) ^ ((n : ℝ)⁻¹)
      ≤ (edgeBoundaryCount A : ℝ) + n * A.card := by
  classical
  -- ℝ-cast counting identity
  have h_eq := edgeBoundary_count_eq A
  have h_eq_R : (edgeBoundaryCount A : ℝ) + n * A.card
      = 2 * ∑ i : Fin n, ((projectionExcept i A).card : ℝ) := by
    have := congrArg (Nat.cast : ℕ → ℝ) h_eq
    push_cast at this
    linarith
  -- AM-GM lower bound on the sum
  have h_AM := sum_projection_card_ge_amgm hA
  -- Combine
  have h_two : 2 * ((n : ℝ) * ((A.card : ℝ) ^ (n - 1 : ℕ)) ^ ((n : ℝ)⁻¹))
      ≤ 2 * ∑ i : Fin n, ((projectionExcept i A).card : ℝ) := by
    have h2pos : (0 : ℝ) ≤ 2 := by norm_num
    exact mul_le_mul_of_nonneg_left h_AM h2pos
  rw [h_eq_R]
  linarith

end InformationTheory.Shannon

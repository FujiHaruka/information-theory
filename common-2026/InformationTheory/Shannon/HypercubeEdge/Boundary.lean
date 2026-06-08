import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LoomisWhitney

/-!
# Boolean hypercube edge-boundary bound (B-2')

Boolean cube `Fin n → Bool` 上の edge boundary を **directed coordinate-flip pair** で
組合せ的に定義し, Loomis–Whitney と AM-GM の合わせ技で edge-isoperimetric 型下界を
publish する。

## 主定義

* `flipCoord i x` — `x : Fin n → Bool` の `i` 番目成分を反転。`Function.update x i (!x i)`.
* `edgeBoundaryCount A` — `(x, i)` 対 (`x ∈ A`, `flipCoord i x ∉ A`) の数。
  Boolean cube の unordered edge `{x, flipCoord i x}` で片端点だけ `A` に入るものに 1 対 1 対応。
* `internalEdgePairCount A` — `(x, i)` 対 (`x ∈ A`, `flipCoord i x ∈ A`) の数。
  unordered internal edge を両端から 2 度 counts するため、`internal edges × 2` に等しい。

## 主補題・主定理

* `edge_total_count` — `edgeBoundaryCount A + internalEdgePairCount A = n * A.card`。
  各 `x ∈ A` と `i : Fin n` で `flipCoord i x` は `A` に入るか入らないか, 二択 disjoint。
* `internal_pair_count_eq_projection_sum` —
  `internalEdgePairCount A = 2 * (n * A.card - Σ_i (projectionExcept i A).card)`。
* `edgeBoundary_count_eq` —
  `edgeBoundaryCount A + n * A.card = 2 * Σ_i (projectionExcept i A).card`。
  上の 2 補題の差から、減算を ℕ で回避するため和の形で書く。
* `sum_projection_card_ge_amgm` —
  `(n : ℝ) * (A.card : ℝ)^((n-1)/n) ≤ Σ_i ((projectionExcept i A).card : ℝ)`。
  Loomis–Whitney (`loomis_whitney`) + AM-GM の corollary。
* `edgeBoundary_ge_AMGM` — 主結果。`A.Nonempty` のもとで:
  `2 * (n : ℝ) * (A.card : ℝ)^((n-1)/n) ≤ (edgeBoundaryCount A : ℝ) + n * A.card`。
  これは `|∂_e A| ≥ 2n |A|^{(n-1)/n} - n |A|` の Lean 表示 (整数差回避のため和の形)。

`SimpleGraph` 構造を持ち込まず, `Sym2` も使わない素朴な組合せ定義に絞り,
Mathlib 上流側の `SimpleGraph.edgeBoundary` API gap を回避する。
entropy-sharp 形 `|∂_e A| ≥ |A|(n - log₂|A|)` は B-2'' deferred で別 PR。
-/

namespace InformationTheory.Shannon

open Finset
open scoped BigOperators

/-! ## Phase A — coord flip + edge counts -/

/-- `x : Fin n → Bool` の `i` 番目成分を反転。 -/
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

/-- `(x, i)` 対で `x ∈ A`, `flipCoord i x ∉ A` を満たすものの数。
Boolean cube 上の edge `{x, flipCoord i x}` で片端点だけ `A` に入るものに対応 (各 edge 1 対 1)。 -/
def edgeBoundaryCount {n : ℕ} (A : Finset (Fin n → Bool)) : ℕ :=
  (Finset.univ.filter
    (fun p : (Fin n → Bool) × Fin n => p.1 ∈ A ∧ flipCoord p.2 p.1 ∉ A)).card

/-- `(x, i)` 対で `x ∈ A`, `flipCoord i x ∈ A` を満たすものの数。
unordered internal edge を両端で 2 度 counts。 -/
@[entry_point]
def internalEdgePairCount {n : ℕ} (A : Finset (Fin n → Bool)) : ℕ :=
  (Finset.univ.filter
    (fun p : (Fin n → Bool) × Fin n => p.1 ∈ A ∧ flipCoord p.2 p.1 ∈ A)).card

/-! ## Phase A — counting identities -/

/-- `(x, i)` 対全体のうち `x ∈ A` のものは `n * A.card` 個。
さらに `flipCoord i x ∈ A` か否かで disjoint 分割される。 -/
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

/-! ## Phase A — projection identity

各 `i : Fin n` で `projectionExcept i A` の元 `y` ごとに preimage size を分類:
`y` の Boolean cube preimage の中で `A` に属するものは 1 個 (singly covered) か
2 個 (doubly covered)。 doubly covered fibre の数を `D_i`, singly covered の数を
`S_i` とすると:

* `|projectionExcept i A| = D_i + S_i`
* `|A| = 2 D_i + S_i`
* 上 2 式から `D_i = |A| - |projectionExcept i A|`.

direction `i` での `internalEdgePairCount` への寄与は `2 D_i`
(各 doubly covered fibre は両端 `x` で counts), 一方 `edgeBoundaryCount` への寄与は
`S_i = 2 |projectionExcept i A| - |A|`。直接 ℕ 上で証明すると差や減算が絡むので,
**double-counting 形** で `Σ_i 2 |projectionExcept i A| = n * A.card + edgeBoundaryCount A`
の和の形に publish する。 -/

/-- 各 `(x, i)` 対 (`x ∈ A`) について `flipCoord i x ∈ A ↔ x.update i (!x i) ∈ A`。
これは `flipCoord` の def-unfold だが counts の中で再利用するため明示。 -/
@[entry_point]
lemma flipCoord_mem_iff {n : ℕ} (A : Finset (Fin n → Bool)) (x : Fin n → Bool)
    (i : Fin n) :
    flipCoord i x ∈ A ↔ Function.update x i (!x i) ∈ A := Iff.rfl

/-- direction `i` の projection map `(Fin n → Bool) → ({j // j ≠ i} → Bool)`。 -/
def projMap {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    {j : Fin n // j ≠ i} → Bool := fun j => x j.val

/-- projection を bit `b` で extend した元。`b = false/true` で extension0/extension1。 -/
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

/-- `projectionExcept i A` の元は `A.image (projMap i)` と同じ。 -/
lemma projectionExcept_eq_image {n : ℕ} (i : Fin n) (A : Finset (Fin n → Bool)) :
    projectionExcept i A = A.image (projMap i) := rfl

/-- `flipCoord i x` は `projMap i x` の `!x i` 拡張に等しい。 -/
lemma extension_projMap_flip {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    extension i (!x i) (projMap i x) = flipCoord i x := by
  funext j
  by_cases h : j = i
  · subst h; simp [flipCoord]
  · rw [extension_apply_ne i (!x i) (projMap i x) h, flipCoord_apply_other i x h]
    rfl

/-- 任意 `y` に対し `projMap i x = y ↔ x = extension i (x i) y`。 -/
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

/-- direction `i` の boundary 寄与: `x ∈ A` で `flipCoord i x ∉ A`。 -/
def boundaryDirSet {n : ℕ} (A : Finset (Fin n → Bool)) (i : Fin n) :
    Finset (Fin n → Bool) :=
  A.filter (fun x => flipCoord i x ∉ A)

/-- direction `i` ごとの (`x ∈ A`, `flipCoord i x ∈ A`) と (`x ∈ A`, `flipCoord i x ∉ A`)
の counts を `projectionExcept` の cardinality に bridge する補題。

`Σ_i 2 * (projectionExcept i A).card = n * A.card + edgeBoundaryCount A`
の形で publish (ℕ 上、減算を回避)。

証明戦略: `A × Fin n` を `(x, i) ↦ (projectionExcept i x, i)` で `(projectionExcept i A) × Fin n`
側に集計し, fiber size を分類。具体的には, 各 `y ∈ projectionExcept i A` の preimage
(in `A` along coord `i`) は size 1 か 2。preimage size = 2 のとき "internal" 寄与 `(x, i)` が
2 回 counts、`flipCoord i x ∈ A` も 2 回。preimage size = 1 のとき "boundary" 寄与 `(x, i)` が
1 回, `flipCoord i x ∉ A`。

両 case で `(preimage size) + (2 - preimage size) = 2` が `Σ` で `2 |projectionExcept i A|` を出す。
-/
theorem two_sum_projection_eq {n : ℕ} (A : Finset (Fin n → Bool)) :
    2 * ∑ i : Fin n, (projectionExcept i A).card
      = n * A.card + edgeBoundaryCount A := by
  classical
  -- Strategy: define for each i, a sum decomposition over (projectionExcept i A) using
  --   2 = (preimage size) + (2 - preimage size).
  -- We don't need an explicit "D_i" variable; instead double-count via the bijection:
  -- {(x, i) : x ∈ A} ≃ Σ_i {y ∈ projectionExcept i A} × {fiber of y in A}.
  -- A cleaner combinatorial route:
  -- For each i, define
  --   f_i : A → projectionExcept i A, f_i x := projection of x.
  -- The fiber over y has size c_i(y) ∈ {1, 2}.
  -- So 2 * (projectionExcept i A).card = Σ_{y ∈ proj} 2 = Σ_y [c_i(y) + (2 - c_i(y))].
  -- Σ_y c_i(y) = (A → proj fiber sum) = A.card.
  -- Σ_y (2 - c_i(y)) = #{y : c_i(y) = 1} = (boundary direction-i pair count).
  -- The latter equals #{x ∈ A : flipCoord i x ∉ A} (each singly-covered y gives 1 such x).
  -- Then sum over i.
  -- direction-i boundary count, intrinsically defined.
  have h_per_i : ∀ i : Fin n,
      2 * (projectionExcept i A).card
        = A.card +
          (Finset.univ.filter
            (fun p : (Fin n → Bool) × Fin n =>
              p.1 ∈ A ∧ flipCoord p.2 p.1 ∉ A ∧ p.2 = i)).card := by
    intro i
    classical
    set proj : Finset ({j : Fin n // j ≠ i} → Bool) := projectionExcept i A
      with hproj_def
    set bdir : Finset (Fin n → Bool) := boundaryDirSet A i with hbdir_def
    -- The pair count {(x, j) : x ∈ A, flipCoord j x ∉ A, j = i} equals bdir.card,
    -- via the bijection (x, i) ↔ x.
    have h_pair_eq_bdir :
        (Finset.univ.filter
            (fun p : (Fin n → Bool) × Fin n =>
              p.1 ∈ A ∧ flipCoord p.2 p.1 ∉ A ∧ p.2 = i)).card = bdir.card := by
      refine Finset.card_nbij' (fun (p : (Fin n → Bool) × Fin n) => p.1)
        (fun x => (x, i)) ?_ ?_ ?_ ?_
      · -- MapsTo: pair set → bdir
        intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        rw [hbdir_def, Finset.mem_coe, boundaryDirSet, Finset.mem_filter]
        obtain ⟨_, hp1, hpflip, hp2⟩ := hp
        rw [← hp2]
        exact ⟨hp1, hpflip⟩
      · -- MapsTo: bdir → pair set
        intro x hx
        rw [hbdir_def, Finset.mem_coe, boundaryDirSet, Finset.mem_filter] at hx
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hx.1, hx.2, rfl⟩
      · -- LeftInv: (p.1, i) = p when p.2 = i
        intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        have hp2 : p.2 = i := hp.2.2.2
        show (p.1, i) = p
        rw [← hp2]
      · intro x _; rfl
    rw [h_pair_eq_bdir]
    -- Now: 2 * proj.card = A.card + bdir.card.
    -- Define fibre count function over proj.
    -- For each y ∈ proj, fibre y := A.filter (projMap i x = y) ⊆ {ext i false y, ext i true y}.
    -- A.card = Σ_y (A.filter (projMap i x = y)).card (by card_eq_sum_card_fiberwise).
    -- 2 * proj.card = Σ_y 2.
    -- Show: Σ_y 2 = Σ_y (fibre_size_y) + Σ_y (2 - fibre_size_y)
    --             = A.card + #{y : fibre_size_y = 1} ; and #{y : fibre size 1} = bdir.card.
    --
    -- Use Finset.card_eq_sum_card_fiberwise:
    have hMapsTo : (A : Set (Fin n → Bool)).MapsTo (projMap i) (proj : Set _) := by
      intro x hxA
      rw [hproj_def, projectionExcept_eq_image]
      exact Finset.mem_image_of_mem _ hxA
    have h_A_sum : A.card = ∑ y ∈ proj, (A.filter (fun x => projMap i x = y)).card :=
      Finset.card_eq_sum_card_fiberwise hMapsTo
    -- Similarly for bdir.
    have hMapsTo_bdir : (bdir : Set (Fin n → Bool)).MapsTo (projMap i) (proj : Set _) := by
      intro x hxbdir
      rw [hbdir_def, boundaryDirSet, Finset.coe_filter] at hxbdir
      exact hMapsTo hxbdir.1
    have h_bdir_sum : bdir.card
        = ∑ y ∈ proj, (bdir.filter (fun x => projMap i x = y)).card :=
      Finset.card_eq_sum_card_fiberwise hMapsTo_bdir
    -- Per-y comparison: 2 = (A.filter ... = y).card + (bdir.filter ... = y).card
    have h_per_y : ∀ y ∈ proj,
        2 = (A.filter (fun x => projMap i x = y)).card +
            (bdir.filter (fun x => projMap i x = y)).card := by
      intro y hy
      -- y ∈ proj means ∃ x ∈ A, projMap i x = y; both ext i false y, ext i true y are
      -- candidates for being in A; at least one is in A; bdir filter counts the
      -- "singly-covered" case.
      -- Define a0 := ext i false y ∈ A, a1 := ext i true y ∈ A.
      -- (A.filter ...).card = (if a0 then 1 else 0) + (if a1 then 1 else 0). ∈ {1, 2}
      -- (bdir.filter ...).card = (if a0 ∧ ¬a1 then 1 else 0) + (if a1 ∧ ¬a0 then 1 else 0). ∈ {0, 1}
      -- 2 = sum check:
      --   both in A: A.filter card = 2, bdir.filter card = 0, sum = 2 ✓
      --   only ext0 in A: A.filter card = 1, bdir.filter card = 1, sum = 2 ✓
      --   only ext1 in A: same.
      --   neither: impossible (y ∈ proj ⟹ at least one).
      have h_filter_A : A.filter (fun x => projMap i x = y)
          ⊆ ({extension i false y, extension i true y} : Finset (Fin n → Bool)) := by
        intro x hx
        simp only [Finset.mem_filter] at hx
        have hxext : x = extension i (x i) y := (projMap_eq_iff i x y).mp hx.2
        simp only [Finset.mem_insert, Finset.mem_singleton]
        cases hb : x i with
        | false => left; rw [hxext, hb]
        | true => right; rw [hxext, hb]
      -- We need a precise equality, not just ⊆. Use:
      -- A.filter ... = (singleton if ext i false y ∉ A else {ext0}) ∪ similar for ext1.
      have h_filter_A_eq : A.filter (fun x => projMap i x = y) =
          ((({extension i false y} : Finset _).filter (· ∈ A)) ∪
           (({extension i true y} : Finset _).filter (· ∈ A))) := by
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
      have h_filter_bdir_eq : bdir.filter (fun x => projMap i x = y) =
          ((({extension i false y} : Finset _).filter
              (fun x => x ∈ A ∧ extension i true y ∉ A)) ∪
           (({extension i true y} : Finset _).filter
              (fun x => x ∈ A ∧ extension i false y ∉ A))) := by
        ext x
        simp only [hbdir_def, boundaryDirSet, Finset.mem_filter,
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
      -- Now compute cards in both equations and case-split on membership.
      have h_ext_ne : extension i false y ≠ extension i true y := by
        intro h
        have := congrFun h i
        simp at this
      -- y ∈ proj: at least one extension is in A.
      have h_y_in_A : extension i false y ∈ A ∨ extension i true y ∈ A := by
        rw [hproj_def, projectionExcept_eq_image, Finset.mem_image] at hy
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
      -- Case-split on membership.
      rw [h_filter_A_eq, h_filter_bdir_eq]
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
          · -- disjointness of singleton-filter sets
            apply Finset.disjoint_filter_filter
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
          · -- disjointness of singleton-filter sets
            apply Finset.disjoint_filter_filter
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
          · -- disjointness of singleton-filter sets
            apply Finset.disjoint_filter_filter
            rw [Finset.disjoint_singleton]
            exact h_ext_ne
          · apply Finset.disjoint_filter_filter
            rw [Finset.disjoint_singleton]
            exact h_ext_ne
    -- Sum the h_per_y equation:
    have h_sum_2 :
        ∑ _y ∈ proj, (2 : ℕ)
          = ∑ y ∈ proj, ((A.filter (fun x => projMap i x = y)).card +
                          (bdir.filter (fun x => projMap i x = y)).card) := by
      apply Finset.sum_congr rfl
      intro y hy; exact h_per_y y hy
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm, Finset.sum_add_distrib,
      ← h_A_sum, ← h_bdir_sum] at h_sum_2
    -- 2 * proj.card = A.card + bdir.card
    linarith
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

/-- 内部 edge pair count を projection 和の形で書き直す。
`edge_total_count` から `internalEdgePairCount = n*A.card - edgeBoundaryCount` だが
ℕ 引算は不便なので, `two_sum_projection_eq` と組み合わせて

`internalEdgePairCount A + 2 * Σ_i (projectionExcept i A).card = 2 * (n * A.card)`

の形で publish。 -/
@[entry_point]
theorem internal_pair_count_eq_projection_sum {n : ℕ}
    (A : Finset (Fin n → Bool)) :
    internalEdgePairCount A + 2 * ∑ i : Fin n, (projectionExcept i A).card
      = 2 * (n * A.card) := by
  have h1 := edge_total_count A
  have h2 := two_sum_projection_eq A
  omega

/-- Edge boundary を projection 和の形で publish (ℕ 上, 減算を `+` で回避)。 -/
theorem edgeBoundary_count_eq {n : ℕ} (A : Finset (Fin n → Bool)) :
    edgeBoundaryCount A + n * A.card
      = 2 * ∑ i : Fin n, (projectionExcept i A).card := by
  have := two_sum_projection_eq A
  omega

/-! ## Phase B — Loomis–Whitney + AM-GM corollary -/

/-- AM-GM on positive reals: `(∏ x_i)^(1/n) ≤ (Σ x_i)/n` ⟹ `n · (∏)^(1/n) ≤ Σ x_i`。
ここでは `x_i := (projectionExcept i A).card : ℝ`、`∏ x_i ≥ |A|^{n-1}` (LW) を組み合わせ,
`Σ x_i ≥ n · |A|^{(n-1)/n}` を出す。 -/
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

/-- B-2' 主結果 (Han-Bregman 流 edge isoperimetric, AM-GM 形)。
nonempty `A ⊆ Fin n → Bool` で:
`2 * n * |A|^{(n-1)/n} ≤ |∂_e A| + n * |A|` (ℝ 上, 減算回避)。

等価形: `|∂_e A| ≥ 2n · |A|^{(n-1)/n} - n · |A|`。

証明: `edgeBoundary_count_eq` + `sum_projection_card_ge_amgm`. -/
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

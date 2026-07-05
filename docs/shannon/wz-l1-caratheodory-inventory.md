# WZ L1 — Carathéodory support-reduction Mathlib inventory

> Focused API inventory for the Wyner–Ziv auxiliary-cardinality bound (the `@residual(plan:wz-auxiliary-cardinality-bound)` L1 endpoint gap). Docs-only; no Lean was compiled and no `.lean` was touched. All `file:line` are against the vendored Mathlib under `.lake/packages/mathlib/`. loogle queries run against `.lake/build/loogle.index`.

## One-line summary

**Every ingredient of the support-reduction (Carathéodory in `ℝ^d`, explicit-weight extraction, the `d+1` cardinality bound, and reindexing to `Fin K`) already exists in Mathlib — existing-ratio ~100%.** There is **no Mathlib gap**: the L1 lemma is plumbing (chain three existing lemmas + a zero-padding reindex), not a wall. The Fenchel–Eggleston `d`-point strengthening is genuinely absent (loogle `Found 0`), but bare Carathéodory (`d+1`) is what the WZ bound needs, so this is not a blocker.

## The reduction need (as posed)

Given a finite index `Fin k`, weights `w : Fin k → ℝ` with `w u ≥ 0` and `∑ u, w u = 1`, and vectors `v : Fin k → (Fin d → ℝ)` (in the WZ application `d = Fintype.card α + 1`), with mixture `∑ u, w u • v u = target`. We want new weights supported on at most `K = d+1` indices whose mixture still equals `target`, i.e. a `w' : Fin K → ℝ`, `w' ≥ 0`, `∑ w' = 1`, `z' : Fin K → (Fin d → ℝ)` with each `z' j ∈ range v`, and `∑ j, w' j • z' j = target`. This is exactly Carathéodory: a point of `convexHull ℝ (range v) ⊆ ℝ^d` is a convex combination of at most `finrank ℝ (Fin d → ℝ) + 1 = d + 1` points of `range v`. A linear/affine objective `L` transports through the reduction because `∑ w' j • (L (z' j)) = L (∑ w' j • z' j) = L target` by `map_sum`/`map_smul`.

---

## Q1 — Carathéodory with the affine-independent support (the `d+1` engine)

The Carathéodory file does **not** state the bound as `card ≤ finrank + 1` directly; it states it via `AffineIndependent`, and the numeric bound comes from a separate affine-independence cardinality lemma (Q5-adjacent). Ambient context for both lemmas (`Mathlib/Analysis/Convex/Caratheodory.lean:48`): `variable {𝕜 : Type*} {E : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]`, `variable {s : Set E}`.

| lemma | file:line | verbatim signature (incl. `[...]`) | conclusion form (verbatim) |
|---|---|---|---|
| `convexHull_eq_union` | `Mathlib/Analysis/Convex/Caratheodory.lean:149` | `theorem convexHull_eq_union : convexHull 𝕜 s = ...` (ambient TCs above) | `convexHull 𝕜 s = ⋃ (t : Finset E) (_ : ↑t ⊆ s) (_ : AffineIndependent 𝕜 ((↑) : t → E)), convexHull 𝕜 ↑t` |
| `eq_pos_convex_span_of_mem_convexHull` | `Mathlib/Analysis/Convex/Caratheodory.lean:162` | `theorem eq_pos_convex_span_of_mem_convexHull {x : E} (hx : x ∈ convexHull 𝕜 s) :` (ambient TCs above) | `∃ (ι : Sort (u + 1)) (_ : Fintype ι), ∃ (z : ι → E) (w : ι → 𝕜), Set.range z ⊆ s ∧ AffineIndependent 𝕜 z ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • z i = x` |
| `Caratheodory.minCardFinsetOfMemConvexHull` | `Mathlib/Analysis/Convex/Caratheodory.lean:107` | `noncomputable def minCardFinsetOfMemConvexHull (hx : x ∈ convexHull 𝕜 s) : Finset E` | returns the minimum-cardinality representing `Finset` (helpers `..._subseteq`:113, `mem_...`:116, `..._nonempty`:120, `affineIndependent_...`:128) |
| `Caratheodory.mem_convexHull_erase` | `Mathlib/Analysis/Convex/Caratheodory.lean:55` | `theorem mem_convexHull_erase [DecidableEq E] {t : Finset E} (h : ¬AffineIndependent 𝕜 ((↑) : t → E)) {x : E} (m : x ∈ convexHull 𝕜 (↑t : Set E)) :` | `∃ y : (↑t : Set E), x ∈ convexHull 𝕜 (↑(t.erase y) : Set E)` |

**Important:** the exact cardinality expression `finrank + 1` is **not** written in Caratheodory.lean. `convexHull_eq_union` / `eq_pos_convex_span_of_mem_convexHull` only give **affine independence** of the support. The `d+1` count is obtained by feeding that `AffineIndependent` witness to `AffineIndependent.card_le_finrank_succ` (Q5) and then `Submodule.finrank_le` + `Module.finrank_fintype_fun_eq_card`.

---

## Q2 — Explicit-weights forms (`Finset.mem_convexHull` / `convexHull_eq`)

Ambient context for all rows (`Mathlib/Analysis/Convex/Combination.lean:39` + `:186`): `{R R' E F ι ι' α : Type*} [Field R] [AddCommGroup E] [Module R E]` and `[LinearOrder R] [IsStrictOrderedRing R]` (the `α`/`PosSMulMono`/`IsOrderedAddMonoid` TCs in scope are not used by these particular lemmas). For `R = ℝ`, `E = Fin d → ℝ` all instances resolve automatically.

| lemma | file:line | verbatim signature | conclusion form (verbatim) |
|---|---|---|---|
| `Finset.mem_convexHull` | `Mathlib/Analysis/Convex/Combination.lean:410` | `theorem Finset.mem_convexHull {s : Finset E} {x : E} :` | `x ∈ convexHull R (s : Set E) ↔ ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ s.centerMass w id = x` |
| `Finset.mem_convexHull'` | `Mathlib/Analysis/Convex/Combination.lean:415` | `lemma Finset.mem_convexHull' {s : Finset E} {x : E} :` | `x ∈ convexHull R (s : Set E) ↔ ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ ∑ y ∈ s, w y • y = x` |
| `Finset.convexHull_eq` | `Mathlib/Analysis/Convex/Combination.lean:389` | `theorem Finset.convexHull_eq (s : Finset E) :` | `convexHull R ↑s = { x : E \| ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ s.centerMass w id = x }` |
| `convexHull_eq` | `Mathlib/Analysis/Convex/Combination.lean:342` | `theorem convexHull_eq (s : Set E) :` | `convexHull R s = { x : E \| ∃ (ι : Type) (t : Finset ι) (w : ι → R) (z : ι → E), (∀ i ∈ t, 0 ≤ w i) ∧ ∑ i ∈ t, w i = 1 ∧ (∀ i ∈ t, z i ∈ s) ∧ t.centerMass w z = x }` |

`Finset.mem_convexHull'` (the `∑ y ∈ s, w y • y = x` form) is the cleanest bridge: fed the `Finset t` from `convexHull_eq_union`, it returns weights `w : E → ℝ` on the vectors directly, no `centerMass` unfold needed.

---

## Q3 — `Finset.centerMass` API + transport of a linear/affine objective

Ambient context: `Mathlib/Analysis/Convex/Combination.lean:39` (`[Field R] [AddCommGroup E] [Module R E]`, plus `[LinearOrder R] [IsStrictOrderedRing R]` for the `_mem_convexHull` rows).

| lemma | file:line | verbatim signature | conclusion form (verbatim) |
|---|---|---|---|
| `Finset.centerMass` (def) | `Mathlib/Analysis/Convex/Combination.lean:44` | `def Finset.centerMass (t : Finset ι) (w : ι → R) (z : ι → E) : E :=` | `(∑ i ∈ t, w i)⁻¹ • ∑ i ∈ t, w i • z i` |
| `Finset.centerMass_eq_of_sum_1` | `Mathlib/Analysis/Convex/Combination.lean:82` | `theorem Finset.centerMass_eq_of_sum_1 (hw : ∑ i ∈ t, w i = 1) :` | `t.centerMass w z = ∑ i ∈ t, w i • z i` |
| `Finset.centerMass_mem_convexHull` | `Mathlib/Analysis/Convex/Combination.lean:253` | `theorem Finset.centerMass_mem_convexHull (t : Finset ι) {w : ι → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hws : 0 < ∑ i ∈ t, w i) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) :` | `t.centerMass w z ∈ convexHull R s` |
| `mem_convexHull_of_exists_fintype` | `Mathlib/Analysis/Convex/Combination.lean:367` | `lemma mem_convexHull_of_exists_fintype {s : Set E} {x : E} [Fintype ι] (w : ι → R) (z : ι → E) (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1) (hz : ∀ i, z i ∈ s) (hx : ∑ i, w i • z i = x) :` | `x ∈ convexHull R s` |
| `mem_convexHull_iff_exists_fintype` | `Mathlib/Analysis/Convex/Combination.lean:378` | `lemma mem_convexHull_iff_exists_fintype {s : Set E} {x : E} :` | `x ∈ convexHull R s ↔ ∃ (ι : Type) (_ : Fintype ι) (w : ι → R) (z : ι → E), (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = x` |
| `affineCombination_eq_centerMass` | `Mathlib/Analysis/Convex/Combination.lean:277` | `theorem affineCombination_eq_centerMass {ι : Type*} {t : Finset ι} {p : ι → E} {w : ι → R} (hw₂ : ∑ i ∈ t, w i = 1) :` | `t.affineCombination R p w = centerMass t w p` |
| `Finset.map_affineCombination` | `Mathlib/LinearAlgebra/AffineSpace/Combination.lean:572` | `theorem map_affineCombination {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (p : ι → P) (w : ι → k) (hw : s.sum w = 1) (f : P →ᵃ[k] P₂) :` | `f (s.affineCombination k p w) = s.affineCombination k (f ∘ p) w` |

**Objective transport (Q3 core answer).** There is **no dedicated `centerMass_map` / `LinearMap.map_centerMass`** lemma (loogle: `Found one declaration mentioning LinearMap and Finset.centerMass` = `Polynomial.eq_centerMass_of_eval_derivative_eq_zero`, unrelated; `Found 0` for AffineMap × centerMass). Two clean routes instead, no gap:
- **Linear objective (the WZ case — a coordinate projection / linear functional `L`):** once weights sum to `1`, the mixture is `∑ w j • z j` (via `centerMass_eq_of_sum_1`); then `L (∑ w j • z j) = ∑ w j • L (z j)` is just `map_sum` + `map_smul` (`LinearMap.map_sum`, `LinearMap.map_smul`). No centerMass-specific lemma required.
- **Affine objective:** `affineCombination_eq_centerMass` (weights sum to 1) + `Finset.map_affineCombination` gives `f (t.centerMass w p) = t.centerMass w (f ∘ p)` for `f : P →ᵃ[k] P₂`.

---

## Q4 — Fintype-indexed forms already used in-project

`InformationTheory/Shannon/MultipleAccess/TimeSharingConverse.lean:42` (`mem_convexHull_iff_exists_fintype`) and `:79` (`mem_convexHull_of_exists_fintype`) already consume the Q3 rows above (verbatim signatures there). Note both use an **arbitrary `Type` index with `[Fintype ι]`**, so they compose directly with a reindex to `Fin K` (Q7). `mem_convexHull_of_exists_fintype` (`:367`) is the natural **entry** step: it turns the given WZ data `(w, v, hw0, hw1, ∑ = target)` into `target ∈ convexHull ℝ (Set.range v)` in one call (with `z := v`, `s := Set.range v`, `hz := fun i => Set.mem_range_self i`).

---

## Q5 — Ambient `finrank` (fixes the numeric card bound) + the affine-independence engine

| lemma | file:line | verbatim signature | conclusion form (verbatim) |
|---|---|---|---|
| `Module.finrank_fintype_fun_eq_card` | `Mathlib/LinearAlgebra/Dimension/Constructions.lean:324` | `theorem Module.finrank_fintype_fun_eq_card : finrank R (η → R) = Fintype.card η` (context: `[Semiring R] [StrongRankCondition R] [Fintype η]`) | `finrank R (η → R) = Fintype.card η` |
| `Module.finrank_pi` | `Mathlib/LinearAlgebra/Dimension/Constructions.lean:291` | `theorem Module.finrank_pi {ι : Type v} [Fintype ι] : finrank R (ι → R) = Fintype.card ι` (context: `[Semiring R] [StrongRankCondition R]`) | `finrank R (ι → R) = Fintype.card ι` |
| `Module.finrank_fin_fun` | `Mathlib/LinearAlgebra/Dimension/Constructions.lean:328` | `theorem Module.finrank_fin_fun {n : ℕ} : finrank R (Fin n → R) = n` (context: `[Semiring R] [StrongRankCondition R]`) | `finrank R (Fin n → R) = n` |
| `finrank_euclideanSpace` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean:199` | `@[simp] theorem finrank_euclideanSpace : Module.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι` (context: `[RCLike 𝕜] [Fintype ι]`) | `Module.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι` |
| `finrank_euclideanSpace_fin` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean:204` | `theorem finrank_euclideanSpace_fin {n : ℕ} : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n` (context: `[RCLike 𝕜]`) | `Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n` |
| `AffineIndependent.card_le_finrank_succ` | `Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:245` | `lemma AffineIndependent.card_le_finrank_succ [Fintype ι] {p : ι → P} (hp : AffineIndependent k p) :` (context `:41,:46`: `variable (k : Type*) {V P : Type*} {ι : Type*}` `[DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]`) | `Fintype.card ι ≤ Module.finrank k (vectorSpan k (Set.range p)) + 1` |
| `Submodule.finrank_le` | `Mathlib/LinearAlgebra/Dimension/Constructions.lean:404` | `theorem Submodule.finrank_le [Module.Finite R M] (s : Submodule R M) :` | `finrank R s ≤ finrank R M` |

**Numeric prediction (verbatim-confirmed against the code above).** `card_le_finrank_succ` bounds by `finrank k (vectorSpan k (Set.range p)) + 1`, i.e. the dimension of the **span of the support**, NOT the ambient dimension. Chain with `Submodule.finrank_le` (span ≤ ambient) + `Module.finrank_fin_fun`/`Module.finrank_fintype_fun_eq_card` to reach the ambient `d`:
- ambient `E = Fin d → ℝ` ⟹ `finrank ℝ E = d` (`Module.finrank_fin_fun`), so the affine-independent support has `card ≤ d + 1`.
- with `d = Fintype.card α + 1`, the reduced support has **at most `Fintype.card α + 2` points**, so `K = Fintype.card α + 2` (this is the WZ auxiliary-alphabet cardinality the L1 lemma should target).
- `vectorSpan`/`Submodule.finrank_le` requires `[Module.Finite R M]`; `Fin d → ℝ` is finite-dimensional, so this resolves. `card_le_finrank_succ` needs the ambient a `DivisionRing`-module affine space — `ℝ`-vector space qualifies.

---

## Q6 — Fenchel–Eggleston / connected-set strengthening (`d` points): ABSENT

Bare Carathéodory gives `d+1`; the Fenchel–Eggleston refinement (a **connected** compact set needs only `d` points) is what a textbook "support lemma" cites, but the WZ bound only needs `d+1`, so its absence is not a blocker.

Confirmations (all authoritative negatives):
- `IsConnected, convexHull, Finset.card` → **`Found 0 declarations`**.
- `IsConnected, convexHull, Module.finrank` → **`Found 0 declarations`**.
- `grep -rli "fenchel\|eggleston" Mathlib/Analysis/` → no file; the only `eggleston` hit in all of Mathlib is `Mathlib/FieldTheory/PrimitiveElement.lean` (unrelated — an author name in a comment).

There is no shared-sorry-lemma consolidation to recommend here: the L1 lemma does not need Fenchel–Eggleston at all, so no `@residual(wall:...)` is warranted for the support reduction. (If a *tight* `d`-point auxiliary bound is ever desired, that WOULD be a genuine Mathlib gap and a self-build; flagged as honest input, not a wall for the current L1 target.)

---

## Q7 — Reindexing a bounded-card support to `Fin K` (with zero padding)

| lemma / def | file:line | verbatim signature | note |
|---|---|---|---|
| `Finset.equivFinOfCardEq` | `Mathlib/Data/Fintype/EquivFin.lean:325` | `noncomputable def Finset.equivFinOfCardEq {s : Finset α} {n : ℕ} (h : #s = n) : s ≃ Fin n` | exact-count reindex of a `Finset` support |
| `Finset.equivFin` | `Mathlib/Data/Fintype/EquivFin.lean:320` | `noncomputable def Finset.equivFin (s : Finset α) : s ≃ Fin #s` | reindex to `Fin #s` |
| `Fintype.equivFinOfCardEq` | `Mathlib/Data/Fintype/EquivFin.lean:124` | `noncomputable def equivFinOfCardEq {n : ℕ} (h : Fintype.card α = n) : α ≃ Fin n` | reindex the `Sort`-index `ι` from `eq_pos_convex_span_of_mem_convexHull` |
| `Fin.castLEEmb` | `Mathlib/Data/Fin/Embedding.lean:77` | `def castLEEmb (h : n ≤ m) : Fin n ↪ Fin m` | embed `Fin (#t)` into `Fin K` (`K = d+1`) to **pad** the unused slots with weight `0` |
| `Fintype.card_coe` | `Mathlib/Data/Fintype/Card.lean` (`Fintype.card ↥s = #s`) | `theorem Fintype.card_coe (s : Finset α) : Fintype.card ↥s = #s` | bridges `Fintype.card ↥t` (needed by `card_le_finrank_succ`) with `#t` (needed by `equivFinOfCardEq`) |

Reindex recipe (no gap): let `m = #t ≤ K = d+1`. Use `Finset.equivFinOfCardEq rfl : ↥t ≃ Fin m`, then `Fin.castLEEmb (h : m ≤ K) : Fin m ↪ Fin K`. Define `w' : Fin K → ℝ` = the pushed-forward weight on the image and `0` elsewhere; `z' : Fin K → (Fin d → ℝ)` = the vector on the image and any dummy (e.g. `0`) elsewhere. Zero weight on padding preserves `∑ w' = 1` and `∑ w' j • z' j = target`. (Padding drops affine-independence and strict positivity, but neither is needed in the final kernel — only `w' ≥ 0`, `∑ = 1`, `∑ w' • z' = target`.)

---

## Key-preconditions box (precondition-accident guards)

- `AffineIndependent.card_le_finrank_succ` yields `finrank (vectorSpan (range p)) + 1`, **not ambient `+1`** — you MUST chain `Submodule.finrank_le` to reach `d + 1`. Skipping this leaves a `vectorSpan` finrank that does not reduce.
- `Submodule.finrank_le` requires `[Module.Finite R M]` on the **ambient** (holds for `Fin d → ℝ`; would fail for an infinite-dim ambient).
- `card_le_finrank_succ` is over a `[DivisionRing k]`-module `AffineSpace`; `ℝ^d` qualifies, but the affine-independent family must be `Fintype`-indexed (`[Fintype ι]`). From the Finset route use `Fintype.card_coe` to convert `Fintype.card ↥t` ↔ `#t`.
- `Finset.mem_convexHull` returns `centerMass w id = x`; if you want the `∑ w y • y = x` shape directly, use `Finset.mem_convexHull'` (avoids a manual `centerMass_eq_of_sum_1` rewrite).
- `mem_convexHull_of_exists_fintype` needs `[Fintype ι]` and the tuple `(hw₀ pointwise, hw₁ sum = 1, hz range, hx ∑ = x)` — the WZ hypotheses map onto it verbatim with `z := v`, `s := Set.range v`.
- The convex-hull explicit-weight lemmas carry `[Field R] [LinearOrder R] [IsStrictOrderedRing R]` — all discharged automatically for `R = ℝ`; no `EuclideanSpace`/inner-product structure is needed (plain `Fin d → ℝ` suffices), so **do not** reach for `EuclideanSpace` unless a metric is separately required.

---

## Elements that need self-building

None are Mathlib gaps; all are short plumbing over existing lemmas (priority order):

1. **The chained `d+1` numeric bound** (~10–20 lines): `card_le_finrank_succ` → `Submodule.finrank_le` → `Module.finrank_fin_fun`, plus `Fintype.card_coe` bookkeeping. Pitfall: the `vectorSpan` vs. ambient finrank confusion above.
2. **The zero-padding reindex `↥t → Fin K`** (~20–40 lines): `Finset.equivFinOfCardEq` + `Fin.castLEEmb`, define padded `w'`/`z'`, re-prove `∑ w' = 1` and `∑ w' • z' = target` by summing over the embedding image (`Finset.sum_map` / `Fintype.sum_eq_sum_compl_add`). Pitfall: keeping `w' ≥ 0` and the mixture equality through the pad.
3. **Objective transport** (~5 lines): `map_sum`/`map_smul` for the linear WZ objective (no dedicated lemma), or `affineCombination_eq_centerMass` + `Finset.map_affineCombination` if the objective is affine.

Effort sense: a self-contained pure-convex-geometry lemma (target `∈ convexHull` → reduced `Fin K` weights) is estimable at **~80–150 lines**, comparable to the existing `convexHull_mem_of_le` gateway in `TimeSharingConverse.lean` (~65 lines). No wall.

---

## Assessment

- **Single best entry point:** the **Finset route** — `convexHull_eq_union` (`Caratheodory.lean:149`) to get an affine-independent `Finset t ⊆ range v` with `target ∈ convexHull ℝ ↑t`, then `Finset.mem_convexHull'` (`Combination.lean:415`) for the explicit weights `w : (Fin d → ℝ) → ℝ` with `∑ y ∈ t, w y • y = target`. Preface with `mem_convexHull_of_exists_fintype` (`Combination.lean:367`) to establish `target ∈ convexHull ℝ (range v)`. This route is preferred over `eq_pos_convex_span_of_mem_convexHull` because a genuine `Finset` support reindexes to `Fin K` most directly (`Finset.equivFinOfCardEq`), whereas the `eq_pos_...` route hands back a `Sort (u+1)` index needing `Fintype.equivFinOfCardEq`. Both are viable and gap-free; use `eq_pos_...` if strict positivity of the pre-pad weights is wanted.
- **Exact card bound for `d = Fintype.card α + 1`:** the affine-independent support has `card ≤ finrank ℝ (Fin d → ℝ) + 1 = d + 1 = Fintype.card α + 2`. Set the WZ auxiliary alphabet to **`K = Fintype.card α + 2`** (`= d + 1`). This is bare Carathéodory; the `d`-point (Fenchel–Eggleston) improvement is unavailable but unnecessary.
- **Weight extraction cleanliness:** clean. `Finset.mem_convexHull'` gives the weights in exactly the `∑ w y • y = x` shape; the only bridge work is (a) chaining two finrank inequalities for the numeric bound and (b) the zero-padding reindex. No re-shaping bridge lemma is missing from Mathlib.
- **Gap flag (honest input, not a wall):** the ONLY thing Mathlib does not provide is the tight Fenchel–Eggleston `d`-point support lemma (Q6, loogle `Found 0`). It is irrelevant to the L1 target. If a future tight-cardinality WZ bound needs it, that would be a genuine self-build/gap — but for `wz-auxiliary-cardinality-bound` as posed, **there is no Mathlib wall**: L1 is discharge-by-plumbing.

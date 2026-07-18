# Mathlib inventory — complete eigen-HilbertBasis for `tsum_prolateEigenvalues_eq`

> Parent plan: [`shannon-hartley-phase2-spectral-plan.md`](shannon-hartley-phase2-spectral-plan.md).
> Target sorry: `InformationTheory/Shannon/TimeBandLimiting.lean:2796`,
> `@residual(plan:shannon-hartley-phase2-spectral-plan)` (off the Shannon-Hartley converse path;
> the main theorem `contAwgn_eq_shannonHartley` is already proof-done — this is the R1 bonus `∑λ=2WT`).
> This inventory covers ONLY the four buckets A–D requested. It does not re-verify the four confirmed
> assets (compact-op spectral theorem, compact-op finite eigenspace, in-project compactness/symmetry,
> the trace identity, the finite per-threshold eigenbasis) — those are ground truth per the brief.

## One-line summary

**The primitives exist at ~85%: every atomic lemma the route needs is in Mathlib, but the Bucket A
crux — collating an `OrthogonalFamily` of per-eigenspace Hilbert bases into ONE `HilbertBasis` of the
infinite-dimensional `E` — is NOT a single Mathlib lemma (`OrthogonalFamily`↔`HilbertBasis` = Found 0,
`IsHilbertSum`↔`HilbertBasis` = Found 0). It must be hand-built from `mkOfOrthogonalEqBot` +
`orthonormal_sigma_orthonormal` + `dense_span`, ~5 ordered building blocks. Bucket B (eigenvalue-set
countability) is a Found-0 that turns out NOT to block: index over all `μ : ℂ` with empty fibers and
let `orthonormal_countable`/`Summable.countable_support` supply countability for free. Bucket C (layer
cake `lintegral_eq_lintegral_meas_lt` + `lintegral_count`) and Bucket D (`inner_smul_left` +
`Complex.conj_ofReal`) are fully stocked. No new `wall:` slug — this is plumbing onto existing assets.**

The single most dangerous finding: **the compact-op spectral theorem indexes eigenspaces over ALL
`μ : ℂ`, not over the real spectrum**; `⟪A e, e⟫.re = μ` (Bucket D) is only valid where the eigenspace
is nonzero, which self-adjointness forces to real `μ` (`conj_eigenvalue_eq_self`). Feed the collated
family over `μ : ℂ` and never assume `μ` real without the eigenspace-nonempty witness.

---

## Main theorem final form (restated)

```lean
-- TimeBandLimiting.lean:2796
theorem tsum_prolateEigenvalues_eq (T W : ℝ) (hT : 0 ≤ T) (hW : 0 < W) :
    ∑' n, prolateEigenvalues T W n = 2 * W * T
```
where (verbatim, in-project):
- `E : Type := Lp ℂ 2 (volume : Measure ℝ)`   (`TimeBandLimiting.lean:141`; complete + separable)
- `prolateEnd (T W : ℝ) : Module.End ℂ E := timeBandLimitingOp T W`  (`:1428`, the `A`)
- `prolateCount (T W c : ℝ) : ℕ := Module.finrank ℂ (prolateEigenspaceSup T W c)`  (`:1553`)
- `prolateEigenvalues (T W : ℝ) (n : ℕ) : ℝ := sInf {c : ℝ | 0 < c ∧ prolateCount T W c ≤ n}` (`:1597`)

Proof strategy (6–10 lines of pseudo-Lean):
```
-- Bucket A: build one HilbertBasis of E out of the eigenspaces of A
let V μ := Module.End.eigenspace (prolateEnd T W) μ                        -- μ : ℂ
have hof := (timeBandLimitingOp_isSymmetric T W).orthogonalFamily_eigenspaces  -- OrthogonalFamily
choose bμ := fun μ => exists_hilbertBasis ℂ (V μ)                          -- HilbertBasis of each eigenspace
let v : (Σ μ, κ μ) → E := fun ⟨μ,k⟩ => ↑(bμ μ k)                           -- collated family
have hon := hof.orthonormal_sigma_orthonormal (fun μ => (bμ μ).orthonormal) -- Orthonormal v
have htot : (span ℂ (range v))ᗮ = ⊥ := ... -- from orthogonalComplement_iSup_eigenspaces_eq_bot + dense_span
let b : HilbertBasis (Σ μ, κ μ) ℂ E := HilbertBasis.mkOfOrthogonalEqBot hon htot
-- Bucket D: each ⟪A(b i), b i⟫.re = its eigenvalue μ(i)
-- feed b to the confirmed trace identity  →  ∑' i, μ(i) = 2WT
have htr := tsum_inner_timeBandLimitingOp_eq T W hT hW b                    -- = 2WT
-- Bucket C: bridge ∑' i, μ(i)  =  ∑' n, prolateEigenvalues n   (equal super-level counts)
--   both = ∫⁻ t in Ioi 0, prolateCount T W t   via layer cake (lintegral_eq_lintegral_meas_lt) + lintegral_count
```

---

## A. `OrthogonalFamily` → `HilbertBasis` collation  (the crux)

**No ready-made collation lemma exists.** Two decisive Found-0s:
- `./loogle "OrthogonalFamily, HilbertBasis"` → `Found 0 declarations`.
- `./loogle "IsHilbertSum, HilbertBasis"` → `Found 0 declarations`.

`./loogle "DirectSum.IsInternal, OrthonormalBasis"` → 6 hits, but `collectedOrthonormalBasis` is the
only collation and it produces an **`OrthonormalBasis` (finite-index / finite-dim only)**, not a
`HilbertBasis`, so it cannot cover the infinite-dimensional kernel eigenspace. The only `HilbertBasis`
constructors in `l2Space.lean` are `mk`, `mkOfOrthogonalEqBot`, `toHilbertBasis [Fintype ι]`,
`reindex` — none takes an orthogonal family. **⟹ hand-build required.**

Ordered building blocks (all verbatim below):

| # | concept | Mathlib API | file:line | status | handling |
|---|---|---|---|---|---|
| A1 | eigenspaces are an OrthogonalFamily | `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` | `Mathlib/Analysis/InnerProductSpace/Spectrum.lean:101` | ✅ exists | supplies `hof`; works for infinite-dim E |
| A2 | ON basis of each eigenspace (uniform, no dim split) | `exists_hilbertBasis` | `Mathlib/Analysis/InnerProductSpace/l2Space.lean:566` | ✅ exists | `HilbertBasis (κ μ) ℂ (V μ)` per μ; needs `[CompleteSpace (V μ)]` (A5) |
| A3 | collate ON families over Σ into one Orthonormal | `OrthogonalFamily.orthonormal_sigma_orthonormal` | `Mathlib/Analysis/InnerProductSpace/Subspace.lean:153` | ✅ exists | supplies `hon` |
| A4 | totality → glue into HilbertBasis | `HilbertBasis.mkOfOrthogonalEqBot` | `l2Space.lean:528` | ✅ exists | final constructor; hyp = `htot` |
| A4' | span density of each eigenbasis (for `htot`) | `HilbertBasis.dense_span` | `l2Space.lean:444` | ✅ exists | `(span ℂ (range bμ))ᗮ = (V μ)ᗮ` bridge |
| A5 | each eigenspace is complete (closed) | `ContinuousLinearMap.isClosed_ker` + `IsClosed.completeSpace_coe` | `.../ContinuousLinearMap/Basic.lean` | ✅ exists | `V μ = ker(A − μ)` closed ⟹ complete, uniformly ∀μ |
| A6 | (alt, reference only) internal Hilbert sum | `IsHilbertSum.mkInternal` | `l2Space.lean:283` | ✅ exists | gives `E ≃ₗᵢ lp G 2`, NOT a HilbertBasis — dead end for us |
| A7 | (alt, finite-dim only) collect ON bases | `DirectSum.IsInternal.collectedOrthonormalBasis` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean:1014` | ✅ exists | finite-dim; unusable for the kernel |

### Verbatim signatures — Bucket A

**A1 · `orthogonalFamily_eigenspaces`** — `Spectrum.lean:101`, namespace `LinearMap.IsSymmetric`.
Context: `variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E}`. **No `[CompleteSpace]`/`[FiniteDimensional]`** — valid for our infinite-dim E.
```lean
theorem orthogonalFamily_eigenspaces (hT : T.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun μ => eigenspace T μ) fun μ => (eigenspace T μ).subtypeₗᵢ
```
Sibling over the eigenvalue subtype (`Spectrum.lean:111`):
```lean
theorem orthogonalFamily_eigenspaces' (hT : T.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun μ : Eigenvalues T => eigenspace T μ) fun μ => (eigenspace T μ).subtypeₗᵢ
```
Provide `hT` from confirmed `timeBandLimitingOp_isSymmetric T W : (prolateEnd T W).IsSymmetric` (`:1430`).

**A2 · `exists_hilbertBasis`** — `l2Space.lean:566`, `_root_`.
Context: `variable {ι 𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]` + `variable [CompleteSpace E]` (`:505`) + `variable (𝕜 E)` (`:563`).
```lean
theorem exists_hilbertBasis : ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w → E)
```
Applied per eigenspace: `exists_hilbertBasis ℂ (V μ)` with `[CompleteSpace (V μ)]` from A5. The index
`κ μ = w : Set (V μ)`. Uniform over all μ — no finite/infinite case split needed for CONSTRUCTION.
(Alternative: `Orthonormal.exists_hilbertBasis_extension {s : Set E} (hs : Orthonormal 𝕜 ((↑) : s → E)) : ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), s ⊆ w ∧ ⇑b = ((↑) : w → E)` — `l2Space.lean:554`.)

**A3 · `orthonormal_sigma_orthonormal`** — `Subspace.lean:153`, namespace `OrthogonalFamily`.
Context: `variable {𝕜 E : Type*} [RCLike 𝕜]` … `[SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)] {V : ∀ i, G i →ₗᵢ[𝕜] E} (hV : OrthogonalFamily 𝕜 G V)`.
```lean
theorem orthonormal_sigma_orthonormal {α : ι → Type*} {v_family : ∀ i, α i → G i}
    (hv_family : ∀ i, Orthonormal 𝕜 (v_family i)) :
    Orthonormal 𝕜 fun a : Σ i, α i => V a.1 (v_family a.1 a.2)
```
With `V μ = (eigenspace T μ).subtypeₗᵢ` and `v_family μ = ⇑(bμ μ)`, the conclusion is exactly
`Orthonormal ℂ (fun a : Σ μ, κ μ => ↑(bμ a.1 a.2))` = orthonormality of the collated `v`.
(Single-vector cousin `Orthonormal.orthogonalFamily` at `Subspace.lean:88`.)

**A4 · `mkOfOrthogonalEqBot`** — `l2Space.lean:528`, namespace `HilbertBasis`.
Context: file-level `{ι 𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]` + `variable [CompleteSpace E]` (`:505`) + `variable {v : ι → E} (hv : Orthonormal 𝕜 v)` (`:508`).
```lean
protected def mkOfOrthogonalEqBot (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) : HilbertBasis ι 𝕜 E
```
`@[simp] coe_mkOfOrthogonalEqBot (hsp) : ⇑(HilbertBasis.mkOfOrthogonalEqBot hv hsp) = v` (`:533`) —
so `b i = v i` definitionally after glue (needed for Bucket D per-vector eigenvalue extraction).
The **only** hypotheses: `hv : Orthonormal 𝕜 v` (from A3) and `hsp : (span 𝕜 (Set.range v))ᗮ = ⊥`.
(Sibling `HilbertBasis.mk (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure)` at `:512` — a
density-form alternative if the `⊥`-form plumbing is awkward.)

**A4' · `dense_span`** — `l2Space.lean:444`, namespace `HilbertBasis`.
```lean
@[simp] protected theorem dense_span (b : HilbertBasis ι 𝕜 E) :
    (span 𝕜 (Set.range b)).topologicalClosure = ⊤
```
Used inside each eigenspace to get `(span ℂ (range (↑ ∘ bμ)))ᗮ = (V μ)ᗮ`, then `htot`.

---

## B. Countability / indexing of the eigenvalue set

`./loogle "Module.End.HasEigenvalue, Countable"` → **`Found 0 declarations`**. Mathlib has **no**
"the eigenvalue set of a compact operator is countable" lemma.

**This Found-0 does NOT block.** Two sidesteps, both stocked:

| concept | Mathlib API | file:line | status | handling |
|---|---|---|---|---|
| index over all μ, empty fibers elsewhere | `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` (indexed `μ : 𝕜`) | `Spectrum.lean:101` | ✅ exists | eigenspace = ⊥ ⟹ `κ μ` empty; the Σ-collation and `mkOfOrthogonalEqBot` never need the μ-set enumerated |
| glued basis has countable index for free | `orthonormal_countable` (in-project) | `TimeBandLimiting.lean:2188` | ✅ exists | `[SeparableSpace H]`; `E` is separable ⟹ any HilbertBasis of `E` (incl. the collated one) is auto-`Countable` — reused inside the trace identity already |
| summable family ⟹ countable support | `Summable.countable_support` | `Mathlib/Topology/Algebra/InfiniteSum/Group.lean` | ✅ exists | for re-indexing `∑' (μ:ℝ) mult(μ)•μ` support to work in Bucket C |
| eigenvalue subtype (if a typed index is wanted) | `Module.End.Eigenvalues T = {μ // eigenspace T μ ≠ ⊥}` | `Mathlib/LinearAlgebra/Eigenspace/Basic.lean` | ✅ exists | `orthogonalFamily_eigenspaces'` variant already uses it |

Verbatim (in-project, needed to justify the auto-countability):
```lean
-- TimeBandLimiting.lean:2188
theorem orthonormal_countable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] {ι : Type*} {v : ι → H} (hv : Orthonormal ℂ v) : Countable ι
```
The confirmed trace identity `tsum_inner_timeBandLimitingOp_eq` already applies this (`:2256`), so E's
`SeparableSpace` instance is in scope — the collated Σ-index inherits `Countable` when fed to it.

---

## C. Layer cake / distribution-function equality of tsums

The multiplicity bridge `∑' i, μ(i) = ∑' n, prolateEigenvalues n`: both nonneg families share the same
super-level counts `#{· | value > t} = prolateCount T W t` for every `t > 0`. Route: push each `∑'`
through counting-measure to a Lebesgue integral, then layer-cake to `∫⁻ t in Ioi 0, (# super-level set)`,
then equate the integrands. All primitives exist; **no** direct "equal super-level counts ⟹ equal
tsums" lemma exists (searched — see bottom), so the equation itself is hand-built from these:

| concept | Mathlib API | file:line | status | handling |
|---|---|---|---|---|
| `∑' = ∫⁻ · ∂count` (needs measurable) | `MeasureTheory.lintegral_count'` | `Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean:85` | ✅ exists | put `⊤ : MeasurableSpace` on the Σ-index ⟹ every `f` measurable |
| `∑' = ∫⁻ · ∂count` (singleton class) | `MeasureTheory.lintegral_count` | `Countable.lean:90` | ✅ exists | for the ℕ-side (`MeasurableSingletonClass ℕ` ✓) |
| layer cake, `>` form | `MeasureTheory.lintegral_eq_lintegral_meas_lt` | `Mathlib/MeasureTheory/Integral/Layercake.lean:496` | ✅ exists | the workhorse; `{a | t < f a}` matches super-level sets |
| layer cake, `≥` form | `MeasureTheory.lintegral_eq_lintegral_meas_le` | `Layercake.lean:445` | ✅ exists | backup (`{a | t ≤ f a}`) |
| countable lintegral (μ-weighted) | `MeasureTheory.lintegral_countable'` | `Countable.lean:121` | ✅ exists | `[Countable α] [MeasurableSingletonClass α]` alt |

### Verbatim signatures — Bucket C

**`lintegral_count`** — `Countable.lean:90`; context `variable {α : Type*} [MeasurableSpace α]`, `open Measure` (`count` = `Measure.count`).
```lean
theorem lintegral_count [MeasurableSingletonClass α] (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂count = ∑' a, f a
```
**`lintegral_count'`** — `Countable.lean:85` (no singleton-class; needs measurability):
```lean
theorem lintegral_count' {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂count = ∑' a, f a
```
**`lintegral_eq_lintegral_meas_lt`** — `Layercake.lean:496`; context `variable {α : Type*} [MeasurableSpace α] {f : α → ℝ}`.
```lean
theorem lintegral_eq_lintegral_meas_lt (μ : Measure α)
    (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ∫⁻ t in Ioi 0, μ {a : α | t < f a}
```
**`lintegral_eq_lintegral_meas_le`** — `Layercake.lean:445`:
```lean
theorem lintegral_eq_lintegral_meas_le (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a}
```
Application shape: with `μ := Measure.count`, `f := prolateEigenvalues T W` (ℕ-side) and
`f := the eigenvalue-of-index function` (Σ-side), each `∑' = ∫⁻ ofReal f ∂count = ∫⁻ t in Ioi 0, count {· | t < f}`.
The two integrands agree because both `count`-cardinalities equal `(prolateCount T W t : ℝ≥0∞)`
(finite super-level sets for a compact positive operator). **Those two counting-function identities are
the genuine self-build (see below).**

---

## D. Eigenvector inner-product simplification `⟪A e, e⟫.re = μ`

Recall the confirmed trace identity conclusion (`TimeBandLimiting.lean:2253`):
`∑' i, (inner ℂ (timeBandLimitingOp T W (b i)) (b i)).re = 2 * W * T` — it is the `.re` of the ℂ inner
product. For a glued basis vector `b i = ↑(bμ μ k)`, a unit eigenvector with `A (b i) = (μ:ℂ) • b i`:

| concept | Mathlib API | file:line | status | verbatim conclusion |
|---|---|---|---|---|
| `x ∈ eigenspace ↔ A x = μ • x` | `Module.End.mem_eigenspace_iff` | `Mathlib/LinearAlgebra/Eigenspace/Basic.lean:445` | ✅ | `x ∈ eigenspace f μ ↔ f x = μ • x` |
| pull scalar out (left slot, conj) | `inner_smul_left` | `Mathlib/Analysis/InnerProductSpace/Basic.lean:105` | ✅ | `⟪r • x, y⟫ = r† * ⟪x, y⟫` (`r†` = `starRingEnd _ r`) |
| pull scalar out (right slot) | `inner_smul_right` | `Basic.lean:115` | ✅ | `⟪x, r • y⟫ = r * ⟪x, y⟫` |
| conj of real coercion (**pitfall**) | `Complex.conj_ofReal` | `Mathlib/Data/Complex/Basic.lean:475` | ✅ | `conj (r : ℂ) = r` |
| real part of real coercion | `Complex.ofReal_re` | `Data/Complex/Basic.lean:88` | ✅ | `Complex.re (r : ℂ) = r` |

One-liner shape: `A(b i) = ((μ:ℝ):ℂ) • b i` (`mem_eigenspace_iff`) ⟹
`⟪A(b i), b i⟫ = conj (μ:ℂ) * ⟪b i, b i⟫ = (μ:ℂ) * 1 = (μ:ℂ)` (`inner_smul_left` + `Complex.conj_ofReal`
+ orthonormal unit `⟪e,e⟫ = 1`) ⟹ `.re = μ` (`Complex.ofReal_re`).

**⚠️ RCLike.ofReal vs Complex.ofReal coercion pitfall** (memory `reference_rclike_complex_ofreal_coe`):
`inner ℂ` is `RCLike`-typed, so `inner_smul_left` yields `starRingEnd ℂ` / `RCLike.conj`, while
`(μ:ℂ)` from `mem_eigenspace_iff` is `Complex.ofReal`. `RCLike.ofReal` and `Complex.ofReal` are defeq
but NOT syntactically equal ⟹ `ring`/`rfl` can fail. Bridge with `norm_cast` (NOT `push_cast`), or take
`Complex.re` via `congrArg Complex.re` / `exact_mod_cast`. `Complex.conj_ofReal` is the clean rewrite.
Where `μ` is only known complex (before the self-adjoint reality argument), guard with
`conj_eigenvalue_eq_self` (`Spectrum.lean:94`, confirmed in-file) that a nonzero eigenspace forces
`conj μ = μ`, i.e. `μ` real.

---

## Key-preconditions box (accident-prone hypotheses)

- **`mkOfOrthogonalEqBot` (A4)** needs *exactly two* inputs: `hv : Orthonormal ℂ v` and
  `hsp : (span ℂ (Set.range v))ᗮ = ⊥`. No completeness/finiteness on the index. `[CompleteSpace E]` is
  the only ambient class (E = Lp is complete ✓). The output `b` satisfies `⇑b = v` by
  `coe_mkOfOrthogonalEqBot`, so per-vector reasoning (Bucket D) sees the raw eigenvectors.
- **`orthonormal_sigma_orthonormal` (A3)** needs the `V` in `hof` to be the `subtypeₗᵢ` family — this
  is precisely the shape `orthogonalFamily_eigenspaces` returns. Do not swap in a different isometry.
- **`exists_hilbertBasis` per eigenspace (A2)** needs `[CompleteSpace (eigenspace ...)]`. Discharge it
  uniformly ∀μ via `V μ = ker(A − μ•1)` closed (`ContinuousLinearMap.isClosed_ker`) ⟹
  `IsClosed.completeSpace_coe`. This avoids the finite (`finite_dimensional_eigenspace`, μ≠0) vs
  infinite (kernel) dimension split at construction time.
- **Compact-op spectral theorem (confirmed asset, `Spectrum.lean:443`)** concludes
  `(⨆ μ, eigenspace (T : Module.End ℂ E) μ)ᗮ = ⊥` over `μ : ℂ` — the iSup is over ALL of ℂ, matching
  the collated family's index. Its hyps `IsCompactOperator T` + `T.IsSymmetric` are the confirmed
  in-project `timeBandLimitingOp_isCompact` / `_isSymmetric`.
- **Layer cake (C)** needs `0 ≤ᵐ[μ] f` and `AEMeasurable f μ`. Under `Measure.count` with `⊤`
  σ-algebra both are trivial (`prolateEigenvalues ≥ 0` is in-project `prolateEigenvalues_nonneg`; every
  function is measurable). Watch the `ENNReal.ofReal` wrapper: the LHS is `∫⁻ ofReal (f ·)`, so the
  bridge to `∑' n, prolateEigenvalues n` (a real tsum) passes through `ENNReal.ofReal`/`toReal` exactly
  as `tsum_inner_timeBandLimitingOp_eq` already does at `:2292` (`ENNReal.tsum_toReal_eq`).
- **`sInf ∅` phantom (parent-plan §BIINF-PHANTOM / §⨅-binder hazard)**: `prolateEigenvalues` is
  `sInf {c | 0 < c ∧ …}`; the counting-function identity `#{n | t < prolateEigenvalues n} = prolateCount t`
  must not silently evaluate a `sInf ∅ = 0` junk branch. The set is nonempty
  (`prolateEigenvalues_setOf_nonempty`, `:1600`) — keep that lemma threaded.

---

## Elements that need self-building (priority order)

1. **The Σ-collation glue → `HilbertBasis` (Bucket A crux).** No Mathlib lemma; assemble A1–A5.
   - Recommended: `mkOfOrthogonalEqBot` on `v := fun ⟨μ,k⟩ => ↑(bμ μ k)`.
   - Effort: ~80–150 lines. The hard sub-lemma is `htot : (span ℂ (range v))ᗮ = ⊥`, via
     `(span ℂ (range v))ᗮ = (⨆ μ, eigenspace ... μ)ᗮ = ⊥`. The `≤` direction uses per-μ
     `(span ℂ (range (↑∘bμ)))ᗮ = (V μ)ᗮ` from `dense_span` (orthogonal insensitive to closure) +
     `Submodule.iInf_orthogonal`; the `≥` direction is `span ≤ ⨆ eigenspace` ⟹ orthogonal flips.
   - Pitfall: `range v = ⋃_μ range(↑∘bμ)`; needs `Submodule.span_iUnion` + `Set.range_sigma`-style
     unfolding. Keep the coercion `↑(bμ μ k) : E` vs `(bμ μ k) : V μ` straight.
2. **Counting-function identity, Σ-side: `count {i | t < μ(i)} = prolateCount T W t` (∀ t>0).**
   The number of collated eigenvectors with eigenvalue > t = Σ of multiplicities = `finrank (⨆_{μ>t} eigenspace μ)` = `prolateCount`. Effort ~40–80 lines. Pitfall: relate the HilbertBasis
   cardinality of a finite-dim eigenspace to its `finrank` (`HilbertBasis` of a fin-dim space has
   `Fintype` index of size `finrank`).
3. **Counting-function identity, ℕ-side: `count {n | t < prolateEigenvalues n} = prolateCount T W t`.**
   The generalized-inverse ↔ counting-function identity for `prolateEigenvalues = sInf{c | prolateCount c ≤ n}`.
   Effort ~40–80 lines of monotone-sInf real analysis. Pitfall: the `sInf ∅` phantom (guard with
   nonemptiness), and `prolateCount` antitone (`prolateCount_antitone`, `:1563`) is the engine.
4. **The two-count layer-cake assembly (Bucket C).** Wire 2+3 through `lintegral_count(')` +
   `lintegral_eq_lintegral_meas_lt` + `ENNReal.ofReal/toReal`. Effort ~40 lines; mostly mirroring the
   existing `tsum_inner_timeBandLimitingOp_eq` ENNReal bookkeeping.
5. **Per-vector eigenvalue extraction (Bucket D).** `⟪A(b i), b i⟫.re = μ(i)`. Effort ~15 lines; the
   RCLike/Complex `ofReal` coercion is the only friction.

Total sense: ~220–370 lines, all plumbing — **no missing theory**. This matches the independently
audited (2026-07-17) `plan:` classification already on the docstring.

---

## Mathlib walls (`@residual(wall:…)` targets)

**None.** Every atom is present; the two Found-0s are not walls:

- `./loogle "OrthogonalFamily, HilbertBasis"` → `Found 0 declarations` — a *missing convenience
  collation*, not missing theory. Closable by hand from `mkOfOrthogonalEqBot` + `orthonormal_sigma_orthonormal`
  + `dense_span` (all present). Template lemma named, self-build estimated (item 1). **Not a wall.**
- `./loogle "IsHilbertSum, HilbertBasis"` → `Found 0 declarations` — same category (no bridge from the
  `IsHilbertSum` predicate to the `HilbertBasis` structure). We route around it via `mkOfOrthogonalEqBot`;
  `IsHilbertSum` is not on the critical path. **Not a wall.**
- `./loogle "Module.End.HasEigenvalue, Countable"` → `Found 0 declarations` — eigenvalue-set
  countability. **Does not block** (Bucket B sidestep). **Not a wall.**
- No direct "two nonneg families with equal super-level cardinalities have equal tsums" lemma
  (searched via the `tsum`/`Measure.count` family — 6 hits, none is this statement). Hand-built via the
  layer-cake route in Bucket C. **Not a wall.**

Recommendation: keep the single `@residual(plan:shannon-hartley-phase2-spectral-plan)` on
`tsum_prolateEigenvalues_eq`. **Do not mint a `wall:` slug.** Only if the counting-function identity
(item 3) turns out to expose a genuine Mathlib gap in generalized-inverse/distribution-function
lemmas should a new slug be minted at that point (parent plan honesty-constraint line, `:165`). No
shared-sorry-lemma consolidation is warranted — this is a single isolated off-path sorry.

---

## Distance to the parent-plan retreat lines

- **Does it touch a retreat line? No trigger.** The parent plan's Shannon-Hartley main theorem
  (`contAwgn_eq_shannonHartley`) is already proof-done sorryAx-free + audit-OK; `tsum_prolateEigenvalues_eq`
  is explicitly an **off-path bonus** (`plan.md:34-35`), not gating any retreat.
- The parent's active honesty constraints that this route must respect (all satisfiable):
  - **No load-bearing hypothesis bundling** (`plan.md:167`): the eigenbasis / counting identities must
    be *proved*, never bundled into a `*Hypothesis` predicate and passed in. The plan achieves the whole
    route from confirmed assets, so bundling is unnecessary and forbidden.
  - **No `sorry` in def bodies** (`plan.md:169`): `prolateEigenvalues`/`prolateCount` stay real defs;
    the sorry lives only in the `tsum_prolateEigenvalues_eq` proof body (already the case).
  - **`sInf ∅` phantom discipline** (`plan.md:48` §⨅-binder hazard): the counting-function identity
    must route through `prolateEigenvalues_setOf_nonempty`, never a degenerate empty-index branch.
- **Proposed degenerate fallback (new retreat line), if item 1 or 3 stalls beyond budget:** leave
  `tsum_prolateEigenvalues_eq` as `sorry + @residual(plan:shannon-hartley-phase2-spectral-plan)` (its
  current honest state) — no hypothesis bundling, no `≠ 0`/`True` slot. Because the main theorem is
  already closed, parking this bonus indefinitely costs nothing downstream. If a genuine gap surfaces in
  the counting-function step, mint a fresh `wall:` slug *there* (not on the whole theorem) per
  `plan.md:165`. **Retreat exit = the existing sorry; no new bundling.**

---

## Starting skeleton

`InformationTheory/Shannon/TimeBandLimiting.lean` already imports everything (the trace identity and
spectral assets live in-file). A self-contained eigenbasis section would open with:

```lean
-- (imports already present in TimeBandLimiting.lean; no new import needed —
--  Spectrum.lean / l2Space.lean / Subspace.lean / Layercake.lean / Lebesgue.Countable
--  arrive transitively via the existing Mathlib.Analysis.InnerProductSpace.* and
--  Mathlib.MeasureTheory.Integral.* imports used by tsum_inner_timeBandLimitingOp_eq.)

open MeasureTheory Module.End Submodule in
section ProlateEigenbasis
variable (T W : ℝ) (hT : 0 ≤ T) (hW : 0 < W)

/-- Per-eigenspace completeness, uniform in `μ` (kernel and nonzero eigenvalues alike). -/
theorem prolate_eigenspace_completeSpace (μ : ℂ) :
    CompleteSpace (Module.End.eigenspace (prolateEnd T W) μ) := by
  sorry  -- ker(A − μ) closed via ContinuousLinearMap.isClosed_ker → IsClosed.completeSpace_coe

/-- Complete eigen-HilbertBasis of `A = timeBandLimitingOp T W`, indexed by
`Σ μ : ℂ, (per-eigenspace basis index)`.  Collation of `exists_hilbertBasis` over each eigenspace,
glued by `mkOfOrthogonalEqBot` using the compact-op spectral theorem for totality. -/
noncomputable def prolateEigenbasis :
    HilbertBasis (Σ μ : ℂ, {w : Set (Module.End.eigenspace (prolateEnd T W) μ) // True}) ℂ E := by
  sorry  -- A1 orthogonalFamily_eigenspaces + A2 exists_hilbertBasis + A3 orthonormal_sigma_orthonormal
         --  + A4' dense_span + orthogonalComplement_iSup_eigenspaces_eq_bot → A4 mkOfOrthogonalEqBot

/-- Every `prolateEigenbasis` vector is a unit eigenvector; `⟪A e, e⟫.re` is its (real) eigenvalue. -/
theorem prolateEigenbasis_inner_re_eq (i) :
    (inner ℂ (timeBandLimitingOp T W (prolateEigenbasis T W i)) (prolateEigenbasis T W i)).re
      = prolateEigenbasisEigenvalue T W i := by
  sorry  -- Bucket D: mem_eigenspace_iff + inner_smul_left + Complex.conj_ofReal + Complex.ofReal_re

-- target (already in-file at :2796); the section discharges its sorry:
-- theorem tsum_prolateEigenvalues_eq (T W : ℝ) (hT : 0 ≤ T) (hW : 0 < W) :
--     ∑' n, prolateEigenvalues T W n = 2 * W * T := by
--   have htr := tsum_inner_timeBandLimitingOp_eq T W hT hW (prolateEigenbasis T W)   -- = 2WT
--   -- rewrite htr via prolateEigenbasis_inner_re_eq → ∑' i, eigenvalue(i) = 2WT
--   -- Bucket C: ∑' i, eigenvalue(i) = ∑' n, prolateEigenvalues n  (equal super-level counts)
--   sorry

end ProlateEigenbasis
```

---

## Route feasibility (Bucket A verdict)

**The collation is NOT a single Mathlib lemma away — it is a hand-built glue.** Two decisive Found-0s
(`OrthogonalFamily, HilbertBasis` and `IsHilbertSum, HilbertBasis`) confirm no ready-made
`OrthogonalFamily → HilbertBasis` collation, and the only existing collation
(`DirectSum.IsInternal.collectedOrthonormalBasis`) is finite-dimensional and outputs an
`OrthonormalBasis`, so it cannot cover the infinite-dimensional kernel eigenspace. The hand-build is,
in order:

1. `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` — `OrthogonalFamily` of the eigenspaces (from
   in-project `timeBandLimitingOp_isSymmetric`).
2. `exists_hilbertBasis ℂ (eigenspace … μ)` per μ, uniform (needs `[CompleteSpace (eigenspace)]` via
   `ContinuousLinearMap.isClosed_ker` + `IsClosed.completeSpace_coe`).
3. `OrthogonalFamily.orthonormal_sigma_orthonormal` — collate into `Orthonormal ℂ (fun a : Σμ,κμ => ↑(bμ a.1 a.2))`.
4. Totality `(span ℂ (range v))ᗮ = ⊥` — from confirmed
   `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` + `HilbertBasis.dense_span` +
   `Submodule.iInf_orthogonal` (orthogonal insensitive to closure per-eigenspace).
5. `HilbertBasis.mkOfOrthogonalEqBot` — glue (steps 3 + 4 are exactly its two hypotheses).

The result is a `HilbertBasis (Σ μ, κ μ) ℂ E` consumable as-is by
`tsum_inner_timeBandLimitingOp_eq`. Buckets B, C, D require no missing theory. Overall: feasible,
~220–370 lines, zero new walls.

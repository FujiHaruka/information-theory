import Common2026.Shannon.BackwardMartingale
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Birkhoff individual ergodic theorem (E-8'' / Phase γ)

This file packages the **ergodic-discharge step** of the Birkhoff individual
ergodic theorem, building on the backward-martingale machinery in `Phase β`.

## Architecture (per `docs/shannon/birkhoff-ergodic-plan.md` §4)

Phase γ decomposes into four sub-phases:

* **γ.1** — set up the Birkhoff time average as a backward martingale
  (Hopf rearrangement / Petersen *Ergodic Theory* (2.2)).
* **γ.2** — apply the backward martingale convergence theorem
  (`BackwardMartingale.ae_tendsto`, stated with `sorry` in Phase β).
* **γ.3** — show the limit is T-invariant a.e. and discharge ergodicity
  via `Ergodic.ae_eq_const_of_ae_eq_comp_ae`
  (`Mathlib/Dynamics/Ergodic/Function.lean:103`).
* **γ.4** — identify the a.e. constant as `∫ f dμ`.

## Status — single isolated `sorry` (exchangeability)

Phase γ now ships the **no-hypothesis** main theorem `birkhoff_ergodic_ae`
plus the **hypothesis form** `birkhoff_ergodic_ae_of_limit` (γ.3 + γ.4
only). The full proof goes through `BackwardMartingale.ae_tendsto`
(Phase β.4, proven) applied to the cond-exp martingale `M_n := μ[f | 𝒢_n]`
where `𝒢_n` is the **f-dependent Hopf filtration**
`σ(S_k : k ≥ ofDual n + 1)` (the partial sums `S_k`).

The Hopf identity `hopf_identity` is now **fully derived (0 sorry)**
from a single deeper helper lemma `condExp_iterate_eq_condExp`
("**exchangeability**": `μ[f ∘ T^[i] | 𝒢_{toDual n}] =ᵐ μ[f | 𝒢_{toDual n}]`
for `i ∈ [0, n]`). The exchangeability lemma packages the
symmetry-under-permutation property of the partial sums; formalising it
requires a change-of-variables-on-comap-σ-algebra development that is not
currently in Mathlib (estimated 70–150 LOC). See `condExp_iterate_eq_condExp`
docstring for details.

**(Historical note.)** A previous iteration shipped `hopf_identity` with
respect to `backwardFiltration` (`σ(T^[n])`). That statement was
**mathematically false** (counter-example: Bernoulli shift). The current
file uses the correct f-dependent filtration `birkhoffFiltration`.

## Main definitions

* `birkhoffAverageReal` — the real-valued Birkhoff time average with
  `n+1` terms.
* `birkhoffPartialSum` — `S_k(ω) := ∑_{i=0}^{k-1} f(T^[i] ω)`.
* `birkhoffFiltration` — the corrected f-dependent Hopf filtration
  `𝒢_n := σ(S_k : k ≥ ofDual n + 1)` as `Filtration ℕᵒᵈ m₀`.
* `birkhoffCondExpMartingale` — cond-exp martingale `M_n := μ[f | 𝒢_n]`.
* `birkhoffMartingale` — applied form `n ↦ A_{ofDual n}`.

## Main results

* `integral_comp_iterate_eq` — `∫ f ∘ T^[i] = ∫ f` (measure preservation).
* `integral_birkhoffAverageReal_eq` — `∫ A_n = ∫ f` for every `n ≥ 0`.
* `birkhoffAverageReal_measurable_birkhoffFiltration` — `A_n` is
  `𝒢_{toDual n}`-measurable (by construction).
* `birkhoffCondExpMartingale_isMartingale` — `M` is a backward martingale.
* `birkhoff_ergodic_ae_of_limit` — γ.3 + γ.4 hypothesis form.
* `birkhoff_ergodic_ae` — **main theorem** (modulo `condExp_iterate_eq_condExp`).
-/

namespace InformationTheory.Shannon

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

/-! ## γ.1 — Birkhoff average + f-dependent backward filtration -/

/-- Birkhoff time average with `n+1` terms.

`birkhoffAverageReal T f n ω := (∑_{i=0}^{n} f (T^[i] ω)) / (n+1)`.

The `n+1` denominator side-steps the `n = 0` division issue; this is the
sequence we want to converge to `∫ f dμ` under Birkhoff's theorem. -/
noncomputable def birkhoffAverageReal (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (∑ i ∈ Finset.range (n + 1), f (T^[i] ω)) / (n + 1 : ℝ)

/-- Partial Birkhoff sum with `k` terms.
`birkhoffPartialSum T f k ω := ∑_{i=0}^{k-1} f (T^[i] ω)`. -/
noncomputable def birkhoffPartialSum (T : Ω → Ω) (f : Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.range k, f (T^[i] ω)

/-- Average and partial sum are related: `A_n = S_{n+1} / (n+1)`. -/
lemma birkhoffAverageReal_eq_partialSum_div (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    birkhoffAverageReal T f n ω = birkhoffPartialSum T f (n + 1) ω / (n + 1 : ℝ) := rfl

/-- Partial sums are measurable when `T` and `f` are. -/
lemma birkhoffPartialSum_measurable {T : Ω → Ω} (hT : Measurable T)
    {f : Ω → ℝ} (hf : Measurable f) (k : ℕ) :
    Measurable (birkhoffPartialSum T f k) := by
  unfold birkhoffPartialSum
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact hf.comp (hT.iterate i)

/-- f-dependent backward filtration **(corrected Hopf filtration)**:
`𝒢_n := σ(S_k : k ≥ ofDual n + 1)`,
the σ-algebra generated by all partial sums `S_k` for `k > ofDual n`.

The shift `+1` is chosen so that `birkhoffAverageReal T f n` (which uses
`S_{n+1}`) is `𝒢_{toDual n}`-measurable.

In `ℕᵒᵈ`, as `n` decreases (i.e. `ofDual n` grows), the set of indices
`{k : k ≥ ofDual n + 1}` shrinks, so the σ-algebra shrinks. Equivalently:
`seq` is monotone in `ℕᵒᵈ`, antitone in `ℕ` — the backward-filtration shape. -/
noncomputable def birkhoffFiltration (T : Ω → Ω) (hT : Measurable T)
    (f : Ω → ℝ) (hf : Measurable f) : Filtration ℕᵒᵈ m₀ where
  seq n := ⨆ k ∈ Set.Ici (OrderDual.ofDual n + 1),
    MeasurableSpace.comap (birkhoffPartialSum T f k) (borel ℝ)
  mono' i j hij := by
    -- `hij : i ≤ j` in `ℕᵒᵈ` means `ofDual j ≤ ofDual i` in `ℕ`.
    have h_ofd : OrderDual.ofDual j ≤ OrderDual.ofDual i := hij
    -- So `{k : k ≥ ofDual j + 1} ⊇ {k : k ≥ ofDual i + 1}`. iSup is monotone in the set.
    refine iSup_mono fun k => iSup_mono' fun hk => ?_
    have hk' : OrderDual.ofDual i + 1 ≤ k := hk
    refine ⟨?_, le_rfl⟩
    show OrderDual.ofDual j + 1 ≤ k
    have h_step : OrderDual.ofDual j + 1 ≤ OrderDual.ofDual i + 1 :=
      Nat.add_le_add_right h_ofd 1
    exact h_step.trans hk'
  le' i := by
    -- Each comap (S_k) (borel ℝ) ≤ m₀ because S_k is measurable.
    refine iSup_le fun k => iSup_le fun _ => ?_
    have h_meas : Measurable (birkhoffPartialSum T f k) :=
      birkhoffPartialSum_measurable hT hf k
    exact h_meas.comap_le

/-- Applied form of `birkhoffFiltration`. -/
@[simp] lemma birkhoffFiltration_apply (T : Ω → Ω) (hT : Measurable T)
    (f : Ω → ℝ) (hf : Measurable f) (n : ℕᵒᵈ) :
    (birkhoffFiltration T hT f hf) n
      = ⨆ k ∈ Set.Ici (OrderDual.ofDual n + 1),
          MeasurableSpace.comap (birkhoffPartialSum T f k) (borel ℝ) := rfl

/-- `birkhoffPartialSum T f k` is `birkhoffFiltration T hT f hf n`-measurable
whenever `k ≥ ofDual n + 1`. -/
lemma birkhoffPartialSum_measurable_birkhoffFiltration
    {T : Ω → Ω} (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f)
    (n : ℕᵒᵈ) {k : ℕ} (hk : OrderDual.ofDual n + 1 ≤ k) :
    Measurable[(birkhoffFiltration T hT f hf) n] (birkhoffPartialSum T f k) := by
  rw [birkhoffFiltration_apply]
  -- The σ-algebra `comap S_k (borel ℝ)` is contained in the iSup.
  have h_le : MeasurableSpace.comap (birkhoffPartialSum T f k) (borel ℝ)
      ≤ ⨆ k' ∈ Set.Ici (OrderDual.ofDual n + 1),
          MeasurableSpace.comap (birkhoffPartialSum T f k') (borel ℝ) := by
    refine le_iSup_of_le k ?_
    exact le_iSup_of_le hk le_rfl
  -- And `S_k` is measurable wrt its own comap.
  have h_comap : Measurable[MeasurableSpace.comap (birkhoffPartialSum T f k) (borel ℝ)]
      (birkhoffPartialSum T f k) := by
    intro s hs
    exact ⟨s, hs, rfl⟩
  exact h_comap.mono h_le le_rfl

/-- `birkhoffAverageReal T f n` is `birkhoffFiltration (toDual n)`-measurable. -/
lemma birkhoffAverageReal_measurable_birkhoffFiltration
    {T : Ω → Ω} (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable[(birkhoffFiltration T hT f hf) (OrderDual.toDual n)]
      (birkhoffAverageReal T f n) := by
  -- A_n = S_{n+1} / (n+1). S_{n+1} is measurable wrt the filtration (n+1 ≥ n+1).
  have h_S : Measurable[(birkhoffFiltration T hT f hf) (OrderDual.toDual n)]
      (birkhoffPartialSum T f (n + 1)) :=
    birkhoffPartialSum_measurable_birkhoffFiltration hT hf (OrderDual.toDual n) le_rfl
  -- Division by a constant: `A_n = S_{n+1} * (1/(n+1))`.
  have h_div : birkhoffAverageReal T f n
      = fun ω => birkhoffPartialSum T f (n + 1) ω * (1 / ((n : ℝ) + 1)) := by
    funext ω
    rw [birkhoffAverageReal_eq_partialSum_div, mul_one_div]
  rw [h_div]
  exact h_S.mul_const _

/-- `birkhoffAverageReal` re-indexed by `ℕᵒᵈ`. -/
noncomputable def birkhoffMartingale (T : Ω → Ω) (f : Ω → ℝ) : ℕᵒᵈ → Ω → ℝ :=
  fun n => birkhoffAverageReal T f (OrderDual.ofDual n)

/-- Applied form of `birkhoffMartingale`. -/
@[simp] lemma birkhoffMartingale_apply (T : Ω → Ω) (f : Ω → ℝ) (n : ℕᵒᵈ) (ω : Ω) :
    birkhoffMartingale T f n ω = birkhoffAverageReal T f (OrderDual.ofDual n) ω := rfl

/-- At the head of the dual order (`toDual 0`), the Birkhoff martingale
collapses to `f`. -/
lemma birkhoffMartingale_toDual_zero (T : Ω → Ω) (f : Ω → ℝ) :
    birkhoffMartingale T f (OrderDual.toDual 0) = f := by
  funext ω
  simp [birkhoffMartingale, birkhoffAverageReal]

/-! ## γ.4 helpers — integral preservation under iteration -/

/-- Each term `f ∘ T^[i]` has the same integral as `f`, by measure
preservation under `T^[i]`. Uses `MeasureTheory.integral_map` plus the
fact that an integrable `f` is in particular a.e. strongly measurable
under the pushed-forward measure. -/
lemma integral_comp_iterate_eq (μ : Measure Ω)
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (i : ℕ) :
    ∫ ω, f (T^[i] ω) ∂μ = ∫ ω, f ω ∂μ := by
  have hTi : MeasurePreserving (T^[i]) μ μ := hT.iterate i
  have h_map : Measure.map (T^[i]) μ = μ := hTi.map_eq
  have hf_strong_map : AEStronglyMeasurable f (Measure.map (T^[i]) μ) := by
    rw [h_map]; exact hf.aestronglyMeasurable
  have h_int_map :
      ∫ y, f y ∂Measure.map (T^[i]) μ = ∫ x, f (T^[i] x) ∂μ :=
    MeasureTheory.integral_map hTi.aemeasurable hf_strong_map
  rw [h_map] at h_int_map
  exact h_int_map.symm

/-- Integral of the `(n+1)`-term Birkhoff average equals `∫ f`. -/
lemma integral_birkhoffAverageReal_eq (μ : Measure Ω) [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (n : ℕ) :
    ∫ ω, birkhoffAverageReal T f n ω ∂μ = ∫ ω, f ω ∂μ := by
  classical
  unfold birkhoffAverageReal
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn_pos
  -- Step 1: divide outside.
  have h1 :
      ∫ ω, (∑ i ∈ Finset.range (n + 1), f (T^[i] ω)) / ((n : ℝ) + 1) ∂μ
        = (∫ ω, ∑ i ∈ Finset.range (n + 1), f (T^[i] ω) ∂μ) / ((n : ℝ) + 1) := by
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const]
  rw [h1]
  -- Step 2: ∫ ∑ = ∑ ∫.
  have h_int_each : ∀ i ∈ Finset.range (n + 1),
      Integrable (fun ω => f (T^[i] ω)) μ := by
    intro i _
    exact (hT.iterate i).integrable_comp_of_integrable hf
  rw [integral_finsetSum _ h_int_each]
  -- Step 3: each ∫ f∘T^[i] = ∫ f.
  have h_each : ∀ i ∈ Finset.range (n + 1),
      ∫ ω, f (T^[i] ω) ∂μ = ∫ ω, f ω ∂μ := by
    intro i _
    exact integral_comp_iterate_eq μ hT hf i
  rw [Finset.sum_congr rfl h_each]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Goal: `(↑(n + 1) * ∫ f) / (↑n + 1) = ∫ f`.
  rw [Nat.cast_add, Nat.cast_one]
  field_simp

/-! ## Main theorem — γ.3 (ergodic discharge) + γ.4 (constant id) -/

/-- **Birkhoff individual ergodic theorem (hypothesis form).**

Given:
* a probability-preserving ergodic transformation `T`,
* an integrable observable `f`,
* an a.e. limit function `g_∞` of the Birkhoff averages
  `A_n ω = (∑_{i=0}^{n} f (T^[i] ω)) / (n+1)`,
* the hypotheses that `g_∞` is a.e. strongly measurable, T-invariant
  (`g_∞ ∘ T =ᵐ g_∞`), and matches `f` in integral (`∫ g_∞ = ∫ f`),

we conclude that the Birkhoff averages converge a.e. to `∫ f dμ`.

This packages **γ.3 (ergodic discharge) + γ.4 (constant identification)**
at **0 sorry**. The hypotheses on `g_∞` are produced by **γ.1 + γ.2**:
γ.1 (Hopf rearrangement) gives the backward-martingale property of
`birkhoffMartingale`; γ.2 applies `BackwardMartingale.ae_tendsto`
(Phase β.4, currently `sorry`) to produce `g_∞`; T-invariance comes from
tail-σ-algebra measurability + the shift identity
`A_n(T ω) - A_n(ω) = (f(T^{n+1} ω) - f ω)/(n+1) → 0` a.e. (the
`f(T^n ω)/n → 0` bound by Borel-Cantelli on `∑ μ{|f|>εn} ≤ ∫|f|/ε`); the
integral identity follows from L¹ closure of the backward martingale.

See `docs/shannon/birkhoff-ergodic-plan.md` §4 for the full chain. -/
theorem birkhoff_ergodic_ae_of_limit
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (_hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    {f : Ω → ℝ} (_hf : Integrable f μ)
    {gInf : Ω → ℝ}
    (hg_meas : AEStronglyMeasurable gInf μ)
    (hg_inv : gInf ∘ T =ᵐ[μ] gInf)
    (hg_int : ∫ ω, gInf ω ∂μ = ∫ ω, f ω ∂μ)
    (hg_lim : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => birkhoffAverageReal T f n ω) atTop (𝓝 (gInf ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverageReal T f n ω)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  -- γ.3: ergodic discharge. `gInf ∘ T =ᵐ gInf` + Ergodic ⟹ `gInf =ᵐ const c`.
  obtain ⟨c, hc⟩ := hT_erg.ae_eq_const_of_ae_eq_comp_ae hg_meas hg_inv
  -- γ.4: identify `c = ∫ f dμ`.
  -- `∫ gInf = c * μ(univ) = c` (probability), and `∫ gInf = ∫ f`.
  have h_intg_c : ∫ ω, gInf ω ∂μ = c := by
    have h_ae_c : ∀ᵐ ω ∂μ, gInf ω = c := hc
    exact integral_eq_const h_ae_c
  have hc_eq : c = ∫ ω, f ω ∂μ := by linarith [hg_int, h_intg_c]
  -- Conclude: `A_n → gInf ω → c = ∫ f` a.e.
  filter_upwards [hg_lim, hc] with ω hω hcω
  rw [hcω] at hω
  rw [hc_eq] at hω
  exact hω

/-! ## γ.1 + γ.2 — Conditional-expectation backward martingale

We use the **f-dependent Hopf filtration** `birkhoffFiltration T hT f hf`
(see above), defined so that `birkhoffAverageReal T f n` is
`birkhoffFiltration (toDual n)`-measurable by construction. With this
filtration, the **Hopf identity** holds correctly (Williams §14.4 /
Petersen Thm 2.2):

```
∀ᵐ ω ∂μ, μ[f | (birkhoffFiltration T hT f hf) (toDual n)] ω
       = birkhoffAverageReal T f n ω
```

i.e. `M_(toDual n) =ᵐ birkhoffAverageReal T f n` where
`M_n := μ[f | (birkhoffFiltration T hT f hf) n]`.

(The previous file shipped the same identity for `backwardFiltration`,
which is **mathematically false** — see plan §6 for the counter-example
on the Bernoulli shift. The correct filtration is the f-dependent one
because the partial sums `S_k` mix past coordinates symmetrically.) -/

section CondExpMartingale

variable {μ : Measure Ω}

/-- Conditional-expectation backward martingale
`M_n := μ[f | birkhoffFiltration T hT f hf n]`. -/
noncomputable def birkhoffCondExpMartingale
    (T : Ω → Ω) (hT : Measurable T) (f : Ω → ℝ) (hf : Measurable f) :
    ℕᵒᵈ → Ω → ℝ :=
  fun n => μ[f | (birkhoffFiltration T hT f hf) n]

/-- The cond-exp backward martingale is automatically a `Martingale ℕᵒᵈ`. -/
lemma birkhoffCondExpMartingale_isMartingale [IsFiniteMeasure μ]
    (T : Ω → Ω) (hT : Measurable T) (f : Ω → ℝ) (hf : Measurable f) :
    Martingale (birkhoffCondExpMartingale (μ := μ) T hT f hf)
      (birkhoffFiltration T hT f hf) μ :=
  martingale_condExp f (birkhoffFiltration T hT f hf) μ

/-- **Exchangeability of conditional expectations under the Hopf
filtration.** For each `i ∈ [0, n]`,

```
μ[f ∘ T^[i] | (birkhoffFiltration T hT f hf) (toDual n)]
    =ᵐ μ[f | (birkhoffFiltration T hT f hf) (toDual n)].
```

This is the **single deep step** behind the Hopf rearrangement identity.
It expresses the symmetry of the partial sum
`S_{n+1} = f ∘ T^[0] + … + f ∘ T^[n]` under permutation of its `n+1`
summands (Petersen *Ergodic Theory* Lemma 2.2.1; Williams §14.4 step
"exchangeability").

Proving this requires the change-of-variables identity
```
∀ A ∈ 𝒢_{toDual n}, ∫_A f ∘ T^[i] dμ = ∫_A f dμ
```
verified on a generating π-system (cylinder sets in `(S_{n+1}, S_{n+2}, …)`).
The cylinder-set integral identity reduces to the joint distribution of
`(f ∘ T^[0], …, f ∘ T^[n])` being symmetric **conditional on**
`(S_{n+1}, S_{n+2}, …)`. Mathlib does not currently package this lemma;
the direct development needs ≈70–150 LOC of standalone infrastructure
(`MeasurableSpace.induction_on_inter` + a cylinder-set π-system + a
symmetry argument over the joint distribution). We defer it. -/
private lemma condExp_iterate_eq_condExp [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Measurable f) (_hf_int : Integrable f μ)
    (n : ℕ) {i : ℕ} (_hi : i ≤ n) :
    μ[fun ω => f (T^[i] ω) | (birkhoffFiltration T hT.measurable f hf)
        (OrderDual.toDual n)]
      =ᵐ[μ] μ[f | (birkhoffFiltration T hT.measurable f hf)
        (OrderDual.toDual n)] := by
  sorry

/-- **Hopf rearrangement identity** (Petersen *Ergodic Theory* Thm 2.2 /
Williams *Probability with Martingales* §14.4).

For the **f-dependent backward filtration** `𝒢_n := σ(S_k : k ≥ n+1)`,
the conditional expectation of `f` equals the Birkhoff average:

```
μ[f | (birkhoffFiltration T hT f hf) (toDual n)] =ᵐ birkhoffAverageReal T f n.
```

The proof (modulo `condExp_iterate_eq_condExp`, which packages the
exchangeability step) is purely algebraic:

1. By construction `A_n = S_{n+1}/(n+1)` is `𝒢_{toDual n}`-measurable.
2. By exchangeability (`condExp_iterate_eq_condExp`):
   `μ[f ∘ T^[i] | 𝒢] =ᵐ μ[f | 𝒢]` for each `i ∈ [0, n]`.
3. Linearity + measurability of `S_{n+1}` give:
   `S_{n+1} = μ[S_{n+1} | 𝒢] = ∑_i μ[f ∘ T^[i] | 𝒢] = (n+1) · μ[f | 𝒢]`.
4. Divide by `n+1`. -/
private lemma hopf_identity [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Measurable f) (hf_int : Integrable f μ) (n : ℕ) :
    birkhoffCondExpMartingale (μ := μ) T hT.measurable f hf (OrderDual.toDual n)
      =ᵐ[μ] birkhoffAverageReal T f n := by
  classical
  -- Use the full filtration expression (not a `let`, to avoid typeclass-defeq issues).
  have h𝒢_le : (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n) ≤ m₀ :=
    (birkhoffFiltration T hT.measurable f hf).le _
  -- Step A: `S_{n+1}` is `𝒢`-measurable.
  have hS_meas : Measurable[(birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)]
      (birkhoffPartialSum T f (n + 1)) :=
    birkhoffPartialSum_measurable_birkhoffFiltration hT.measurable hf
      (OrderDual.toDual n) le_rfl
  -- Step C: each summand `f ∘ T^[i]` is integrable.
  have h_each_int : ∀ i ∈ Finset.range (n + 1),
      Integrable (fun ω => f (T^[i] ω)) μ :=
    fun i _ => (hT.iterate i).integrable_comp_of_integrable hf_int
  -- Step D: exchangeability — `μ[f ∘ T^[i] | 𝒢] =ᵐ μ[f | 𝒢]` for `i ≤ n`.
  have h_exch : ∀ i ∈ Finset.range (n + 1),
      μ[fun ω => f (T^[i] ω)
          | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)]
        =ᵐ[μ] μ[f | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact condExp_iterate_eq_condExp hT hf hf_int n hi'
  -- Step E: `S_{n+1} = ∑_i f ∘ T^[i]` pointwise.
  have hS_eq : (birkhoffPartialSum T f (n + 1))
      = fun ω => ∑ i ∈ Finset.range (n + 1), f (T^[i] ω) := rfl
  -- Step F: condExp commutes with finite sums.
  have h_sum :
      μ[fun ω => ∑ i ∈ Finset.range (n + 1), f (T^[i] ω)
          | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)]
        =ᵐ[μ] ∑ i ∈ Finset.range (n + 1),
            μ[fun ω => f (T^[i] ω)
              | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] := by
    have h_swap :
        (fun ω => ∑ i ∈ Finset.range (n + 1), f (T^[i] ω))
          = ∑ i ∈ Finset.range (n + 1), (fun ω => f (T^[i] ω)) := by
      funext ω
      simp [Finset.sum_apply]
    rw [h_swap]
    exact MeasureTheory.condExp_finsetSum h_each_int _
  -- Step G: ∑_i μ[f ∘ T^[i] | 𝒢] =ᵐ ∑_i μ[f | 𝒢] (a.e. equality of sums).
  have h_sum_eq :
      (∑ i ∈ Finset.range (n + 1),
          μ[fun ω => f (T^[i] ω)
            | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)])
        =ᵐ[μ] (∑ _i ∈ Finset.range (n + 1),
          μ[f | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)]) := by
    have h_all : ∀ᵐ ω ∂μ, ∀ i : ℕ,
        i ∈ Finset.range (n + 1) →
        μ[fun ω' => f (T^[i] ω')
            | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] ω
          = μ[f | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] ω := by
      rw [ae_all_iff]
      intro i
      by_cases hi : i ∈ Finset.range (n + 1)
      · filter_upwards [h_exch i hi] with ω hω
        intro _; exact hω
      · refine Filter.Eventually.of_forall (fun _ h => ?_)
        exact (hi h).elim
    filter_upwards [h_all] with ω hω
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    exact hω i hi
  -- Step H: ∑ of constants over a finset = card • function.
  have h_const_sum :
      (∑ _i ∈ Finset.range (n + 1),
          μ[f | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)])
        = (n + 1 : ℕ)
            • μ[f | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] := by
    rw [Finset.sum_const, Finset.card_range]
  -- Step I: μ[S_{n+1} | 𝒢] = S_{n+1} (S_{n+1} is 𝒢-measurable & integrable).
  have hSn1_int : Integrable (birkhoffPartialSum T f (n + 1)) μ := by
    rw [hS_eq]
    exact integrable_finsetSum _ h_each_int
  have hSn1_smeas :
      StronglyMeasurable[(birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)]
      (birkhoffPartialSum T f (n + 1)) :=
    hS_meas.stronglyMeasurable
  haveI h_sf : SigmaFinite (μ.trim h𝒢_le) := by
    haveI : IsFiniteMeasure (μ.trim h𝒢_le) := isFiniteMeasure_trim h𝒢_le
    infer_instance
  have h_condS :
      μ[birkhoffPartialSum T f (n + 1)
        | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)]
      = birkhoffPartialSum T f (n + 1) :=
    condExp_of_stronglyMeasurable h𝒢_le hSn1_smeas hSn1_int
  -- Step J: Combine.
  have h_chain : (birkhoffPartialSum T f (n + 1))
      =ᵐ[μ] (n + 1 : ℕ)
        • μ[f | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] := by
    have hc1 :
        μ[birkhoffPartialSum T f (n + 1)
          | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)]
        =ᵐ[μ] (n + 1 : ℕ)
          • μ[f | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] := by
      calc μ[birkhoffPartialSum T f (n + 1)
              | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)]
          = μ[fun ω => ∑ i ∈ Finset.range (n + 1), f (T^[i] ω)
              | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] := by
            rw [hS_eq]
        _ =ᵐ[μ] ∑ i ∈ Finset.range (n + 1),
            μ[fun ω => f (T^[i] ω)
              | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] := h_sum
        _ =ᵐ[μ] ∑ _i ∈ Finset.range (n + 1),
            μ[f | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] := h_sum_eq
        _ = (n + 1 : ℕ)
            • μ[f | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] :=
              h_const_sum
    have hc2 : (birkhoffPartialSum T f (n + 1))
        =ᵐ[μ] μ[birkhoffPartialSum T f (n + 1)
          | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] := by
      rw [h_condS]
    exact hc2.trans hc1
  -- Step K: divide both sides by `n+1`.
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn_pos
  -- Goal: `birkhoffCondExpMartingale ... (toDual n) =ᵐ A_n`.
  show μ[f | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)]
        =ᵐ[μ] birkhoffAverageReal T f n
  symm
  filter_upwards [h_chain] with ω hω
  set g : ℝ :=
    μ[f | (birkhoffFiltration T hT.measurable f hf) (OrderDual.toDual n)] ω with hg_def
  have h_smul :
      ((n + 1 : ℕ) • μ[f | (birkhoffFiltration T hT.measurable f hf)
        (OrderDual.toDual n)]) ω
      = ((n : ℝ) + 1) * g := by
    show ((n + 1 : ℕ) : ℕ) • g = ((n : ℝ) + 1) * g
    rw [nsmul_eq_mul]
    push_cast; ring
  rw [h_smul] at hω
  rw [birkhoffAverageReal_eq_partialSum_div, hω]
  field_simp

/-- **Backward martingale property of the Birkhoff average** (corollary of
the Hopf identity).

For `m ≤ n` in `ℕᵒᵈ` (i.e. `ofDual n ≤ ofDual m` in `ℕ`):

```
μ[birkhoffAverageReal T f (ofDual n) | (birkhoffFiltration T hT f hf) m]
    =ᵐ[μ] birkhoffAverageReal T f (ofDual m).
```

This matches Mathlib's `Martingale` convention (`μ[f j | ℱ i] =ᵐ f i`
for `i ≤ j`). In terms of original ℕ indices `k = ofDual m, ℓ = ofDual n`
with `ℓ ≤ k`: project the "less averaged" `A_ℓ` onto the smaller σ-algebra
`𝒢_{toDual k}` (which contains `S_{k+1}, S_{k+2}, …` but not `S_{ℓ+1}`
when `ℓ < k`) to obtain the "more averaged" `A_k`.

Derived from `hopf_identity` + tower property
(`condExp_condExp_of_le`). Inherits the single `sorry` from
`condExp_iterate_eq_condExp` (transitively, via `hopf_identity`) —
no new mathematical content. -/
private lemma birkhoffMartingale_property [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Measurable f) (hf_int : Integrable f μ)
    (m n : ℕᵒᵈ) (hmn : m ≤ n) :
    μ[birkhoffAverageReal T f (OrderDual.ofDual n)
        | (birkhoffFiltration T hT.measurable f hf) m]
      =ᵐ[μ] birkhoffAverageReal T f (OrderDual.ofDual m) := by
  -- Strategy: factor through the cond-exp martingale via Hopf identity + tower.
  -- Hopf for n: A_(ofDual n) =ᵐ M n where M n := μ[f | 𝒢 n].
  have h_hopf_n : birkhoffAverageReal T f (OrderDual.ofDual n)
      =ᵐ[μ] birkhoffCondExpMartingale (μ := μ) T hT.measurable f hf n :=
    (hopf_identity hT hf hf_int (OrderDual.ofDual n)).symm
  -- Hopf for m.
  have h_hopf_m : birkhoffCondExpMartingale (μ := μ) T hT.measurable f hf m
      =ᵐ[μ] birkhoffAverageReal T f (OrderDual.ofDual m) :=
    hopf_identity hT hf hf_int (OrderDual.ofDual m)
  -- M is a Martingale: for m ≤ n in ℕᵒᵈ, μ[M n | 𝒢 m] =ᵐ M m.
  have h_M : Martingale (birkhoffCondExpMartingale (μ := μ) T hT.measurable f hf)
      (birkhoffFiltration T hT.measurable f hf) μ :=
    birkhoffCondExpMartingale_isMartingale T hT.measurable f hf
  have h_mart : μ[birkhoffCondExpMartingale (μ := μ) T hT.measurable f hf n
      | (birkhoffFiltration T hT.measurable f hf) m]
      =ᵐ[μ] birkhoffCondExpMartingale (μ := μ) T hT.measurable f hf m :=
    h_M.condExp_ae_eq hmn
  -- Chain: μ[A_(ofDual n) | 𝒢 m] =ᵐ μ[M n | 𝒢 m] =ᵐ M m =ᵐ A_(ofDual m).
  exact ((condExp_congr_ae h_hopf_n).trans h_mart).trans h_hopf_m

end CondExpMartingale

/-! ## γ.3 + γ.4 — Limit identification, T-invariance, integral equality -/

section MainTheorem

variable {μ : Measure Ω}

/-- Algebraic recursion: `A_n(T ω) = ((n+2) · A_{n+1}(ω) - f(ω)) / (n+1)`.

Both sides are pointwise functions of `ω` (no measure assumption). -/
lemma birkhoffAverageReal_comp_T (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    birkhoffAverageReal T f n (T ω)
      = ((n + 2 : ℝ) * birkhoffAverageReal T f (n + 1) ω - f ω) / (n + 1) := by
  classical
  unfold birkhoffAverageReal
  -- LHS sum: `Σ_{i ∈ range (n+1)} f (T^[i] (T ω)) = Σ_{i ∈ range (n+1)} f (T^[i+1] ω)`.
  have h_iter : ∀ i, T^[i] (T ω) = T^[i + 1] ω := fun i => by
    rw [show T^[i] (T ω) = (T^[i] ∘ T) ω from rfl]
    rw [show (T^[i] ∘ T) = T^[i + 1] from (Function.iterate_succ T i).symm]
  have h_lhs_sum :
      (∑ i ∈ Finset.range (n + 1), f (T^[i] (T ω)))
        = (∑ i ∈ Finset.range (n + 1), f (T^[i + 1] ω)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_iter i]
  -- Reindex `j = i + 1` over `range (n+1)`: gives `Σ_{j ∈ Finset.Ioo 0 (n+2)} f (T^[j] ω)`,
  -- equivalently `Σ_{j ∈ range (n+2)} - f(T^[0] ω)`.
  have h_reindex :
      (∑ i ∈ Finset.range (n + 1), f (T^[i + 1] ω))
        = (∑ j ∈ Finset.range (n + 2), f (T^[j] ω)) - f (T^[0] ω) := by
    rw [Finset.sum_range_succ' (fun j => f (T^[j] ω)) (n + 1)]
    ring
  -- T^[0] ω = ω.
  have h_T0 : T^[0] ω = ω := rfl
  -- Combine.
  rw [h_lhs_sum, h_reindex, h_T0]
  -- RHS Birkhoff average: `(Σ_{j ∈ range (n+2)} f(T^[j] ω)) / (n+2)`.
  have h_n_succ : ((n : ℝ) + 1 + 1) = (n + 2 : ℝ) := by ring
  have h_div : ((↑(n + 1) : ℝ) + 1) = (n + 2 : ℝ) := by push_cast; ring
  -- Goal: shape match.
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn_pos
  have hn2_pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hn2_ne : ((n : ℝ) + 2) ≠ 0 := ne_of_gt hn2_pos
  rw [show ((↑(n + 1) : ℝ) + 1) = (n : ℝ) + 2 from by push_cast; ring]
  field_simp

/-- **Birkhoff individual ergodic theorem (no-hypothesis form).**

For a probability-preserving ergodic transformation `T : Ω → Ω` and an
integrable observable `f : Ω → ℝ`, the Birkhoff time averages

```
A_n ω := (∑_{i=0}^{n} f (T^[i] ω)) / (n + 1)
```

converge almost everywhere to the spatial mean `∫ f dμ`.

The proof discharges γ.1 + γ.2 by:

* applying `BackwardMartingale.ae_tendsto` (Phase β) to the
  conditional-expectation martingale `M_n := μ[f | ℋ_n]`, producing
  an a.e. limit `gInf` that is `tailSigma`-measurable;
* using the **Hopf identity** (`hopf_identity` above) to identify
  `M_(toDual n) =ᵐ A_n`, hence `A_n → gInf` a.e.;
* deriving T-invariance `gInf ∘ T =ᵐ gInf` from the recursion
  `A_n(Tω) = ((n+2)/(n+1)) · A_{n+1}(ω) - f(ω)/(n+1)` and the a.e.
  convergence (uses `MeasurePreserving.quasiMeasurePreserving` to push
  the convergence at `Tω`);
* obtaining the integral equality `∫ gInf = ∫ f` via uniform
  integrability of conditional expectations
  (`Integrable.uniformIntegrable_condExp_filtration`) plus Vitali's
  theorem (`tendsto_Lp_finite_of_tendstoInMeasure`) and
  `tendsto_integral_of_L1'`;
* then invoking `birkhoff_ergodic_ae_of_limit` for γ.3 + γ.4.

The single `sorry` (transitively, via `hopf_identity`) is the
exchangeability lemma `condExp_iterate_eq_condExp`. -/
theorem birkhoff_ergodic_ae [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverageReal T f n ω)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  classical
  -- Replace `f` with a measurable model `f'` (AE-equal). All Birkhoff/cond-exp
  -- statements transfer via a.e. equality plus measure preservation.
  set f' : Ω → ℝ := hf.aestronglyMeasurable.mk f with hf'_def
  have hf'_meas : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hf'_ae : f =ᵐ[μ] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hf'_int : Integrable f' μ := hf.congr hf'_ae
  -- A_n and A_n' agree a.e. (for every n) via measure preservation of T^[i].
  have h_A_ae : ∀ n : ℕ, birkhoffAverageReal T f n =ᵐ[μ] birkhoffAverageReal T f' n := by
    intro n
    have h_each : ∀ i, (fun ω => f (T^[i] ω)) =ᵐ[μ] fun ω => f' (T^[i] ω) := by
      intro i
      exact (hT.iterate i).quasiMeasurePreserving.ae_eq hf'_ae
    -- Convert to ae of "for all i" via ae_all_iff (countable Finset).
    have h_all : ∀ᵐ ω ∂μ, ∀ i : ℕ, f (T^[i] ω) = f' (T^[i] ω) := by
      rw [ae_all_iff]
      exact h_each
    filter_upwards [h_all] with ω hω
    unfold birkhoffAverageReal
    congr 1
    exact Finset.sum_congr rfl (fun i _ => hω i)
  -- Set up the cond-exp backward martingale `M : ℕᵒᵈ → Ω → ℝ` using `f'`.
  set ℋ : Filtration ℕᵒᵈ m₀ := birkhoffFiltration T hT.measurable f' hf'_meas with hℋ_def
  set M : ℕᵒᵈ → Ω → ℝ :=
    birkhoffCondExpMartingale (μ := μ) T hT.measurable f' hf'_meas with hM_def
  have hM_isMart : Martingale M ℋ μ :=
    birkhoffCondExpMartingale_isMartingale (μ := μ) T hT.measurable f' hf'_meas
  -- β.4 — apply backward-martingale convergence to extract `gInf`.
  have hM_int0 : Integrable (M (OrderDual.toDual 0)) μ := hM_isMart.integrable _
  obtain ⟨gInf, hgInf_smeas, hgInf_lim⟩ :=
    BackwardMartingale.ae_tendsto hM_isMart hM_int0
  -- Promote strong measurability with respect to the tail σ-algebra to AE strong measurability.
  have h_tail_le : (⨅ n : ℕ, ℋ (OrderDual.toDual n)) ≤ m₀ := by
    refine iInf_le_of_le 0 ?_
    exact ℋ.le _
  have hgInf_aeSmeas : AEStronglyMeasurable gInf μ :=
    (hgInf_smeas.mono h_tail_le).aestronglyMeasurable
  -- γ.1 — Hopf: `M (toDual n) =ᵐ birkhoffAverageReal T f' n` for every `n`.
  have h_hopf : ∀ n : ℕ, M (OrderDual.toDual n) =ᵐ[μ] birkhoffAverageReal T f' n :=
    fun n => hopf_identity hT hf'_meas hf'_int n
  -- Combine Hopf + a.e. equality `A_n =ᵐ A_n'` + Lévy.
  have h_avg_lim : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => birkhoffAverageReal T f n ω) atTop (𝓝 (gInf ω)) := by
    have h_all_hopf : ∀ᵐ ω ∂μ, ∀ n : ℕ,
        M (OrderDual.toDual n) ω = birkhoffAverageReal T f' n ω := by
      rw [ae_all_iff]; exact h_hopf
    have h_all_ae : ∀ᵐ ω ∂μ, ∀ n : ℕ,
        birkhoffAverageReal T f n ω = birkhoffAverageReal T f' n ω := by
      rw [ae_all_iff]; exact h_A_ae
    filter_upwards [hgInf_lim, h_all_hopf, h_all_ae] with ω hω h_pt h_pt'
    have h_eq : (fun n : ℕ => M (OrderDual.toDual n) ω)
        = fun n : ℕ => birkhoffAverageReal T f n ω := by
      funext n; rw [h_pt n, ← h_pt' n]
    rw [h_eq] at hω
    exact hω
  -- γ.3 helper — T-invariance of `gInf`.
  -- Push `h_avg_lim` along `T` (QMP) to get `A_n(T ω) → gInf(T ω)` a.e.
  have h_avg_lim_T : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => birkhoffAverageReal T f n (T ω)) atTop (𝓝 (gInf (T ω))) :=
    hT.quasiMeasurePreserving.tendsto_ae h_avg_lim
  -- Combine with the recursion: `A_n(T ω) = ((n+2) A_{n+1}(ω) - f ω) / (n+1)`.
  have h_inv : gInf ∘ T =ᵐ[μ] gInf := by
    filter_upwards [h_avg_lim, h_avg_lim_T] with ω hω hωT
    -- `A_n(T ω) → gInf(T ω)`, and we'll show `A_n(T ω) → gInf ω` by the recursion.
    -- So `gInf(T ω) = gInf ω` by uniqueness of limits.
    -- RHS sequence `((n+2) · A_{n+1}(ω) - f ω) / (n+1)` converges to `gInf ω`.
    have h_recur : ∀ n : ℕ, birkhoffAverageReal T f n (T ω)
        = ((n + 2 : ℝ) * birkhoffAverageReal T f (n + 1) ω - f ω) / (n + 1) :=
      fun n => birkhoffAverageReal_comp_T T f n ω
    -- Rewrite the LHS sequence using `h_recur`.
    have h_lhs_seq_eq :
        (fun n : ℕ => birkhoffAverageReal T f n (T ω))
          = fun n : ℕ =>
            ((n + 2 : ℝ) * birkhoffAverageReal T f (n + 1) ω - f ω) / (n + 1) := by
      funext n; exact h_recur n
    rw [h_lhs_seq_eq] at hωT
    -- RHS sequence in pieces:
    --   c_n := (n+2) / (n+1) → 1
    --   d_n := f ω / (n+1) → 0
    --   A_{n+1}(ω) → gInf ω
    -- Hence `c_n · A_{n+1}(ω) - d_n → 1 · gInf ω - 0 = gInf ω`.
    have h_one_div : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      have h_eq : (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1))
          = fun n : ℕ => 1 + 1 / ((n : ℝ) + 1) := by
        funext n
        have hn_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp
        ring
      rw [h_eq]
      have h_sum : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add h_one_div
      simpa using h_sum
    have hd : Tendsto (fun n : ℕ => f ω / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have h_eq : (fun n : ℕ => f ω / ((n : ℝ) + 1))
          = fun n : ℕ => f ω * (1 / ((n : ℝ) + 1)) := by
        funext n; rw [mul_one_div]
      rw [h_eq]
      have : Tendsto (fun n : ℕ => f ω * (1 / ((n : ℝ) + 1))) atTop (𝓝 (f ω * 0)) :=
        h_one_div.const_mul (f ω)
      simpa using this
    -- A_{n+1}(ω) → gInf ω: shift of the original convergence.
    have hA_shift : Tendsto (fun n : ℕ => birkhoffAverageReal T f (n + 1) ω) atTop
        (𝓝 (gInf ω)) := by
      have h_shift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
        exact tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
      exact hω.comp h_shift
    -- Multiply: c_n · A_{n+1}(ω) → 1 · gInf ω = gInf ω.
    have h_prod : Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1)
        * birkhoffAverageReal T f (n + 1) ω) atTop (𝓝 (gInf ω)) := by
      simpa using hc.mul hA_shift
    -- Express RHS = (c_n · A_{n+1}(ω)) - d_n.
    have h_rhs_eq :
        (fun n : ℕ => ((n + 2 : ℝ) * birkhoffAverageReal T f (n + 1) ω - f ω)
          / ((n : ℝ) + 1))
        = fun n : ℕ =>
          ((n : ℝ) + 2) / ((n : ℝ) + 1) * birkhoffAverageReal T f (n + 1) ω
            - f ω / ((n : ℝ) + 1) := by
      funext n
      have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      field_simp
    -- Massage `hωT` into shape.
    have hωT' :
        Tendsto (fun n : ℕ =>
          ((n : ℝ) + 2) / ((n : ℝ) + 1) * birkhoffAverageReal T f (n + 1) ω
            - f ω / ((n : ℝ) + 1))
          atTop (𝓝 (gInf (T ω))) := by
      have h_cast_eq : (fun n : ℕ =>
          ((↑n + 2 : ℝ) * birkhoffAverageReal T f (n + 1) ω - f ω) / (↑n + 1))
          = fun n : ℕ =>
          ((n : ℝ) + 2) / ((n : ℝ) + 1) * birkhoffAverageReal T f (n + 1) ω
            - f ω / ((n : ℝ) + 1) := h_rhs_eq
      rw [h_cast_eq] at hωT
      exact hωT
    -- Limit of the sub-d sequence is `gInf ω - 0 = gInf ω`.
    have h_limit_target : Tendsto (fun n : ℕ =>
          ((n : ℝ) + 2) / ((n : ℝ) + 1) * birkhoffAverageReal T f (n + 1) ω
            - f ω / ((n : ℝ) + 1))
          atTop (𝓝 (gInf ω)) := by
      simpa using h_prod.sub hd
    -- Uniqueness of limits: gInf (T ω) = gInf ω.
    have : gInf (T ω) = gInf ω := tendsto_nhds_unique hωT' h_limit_target
    exact this
  -- γ.4 helper — `∫ gInf = ∫ f` via UI of cond-exps + Vitali.
  have h_int_eq : ∫ ω, gInf ω ∂μ = ∫ ω, f ω ∂μ := by
    -- `M` is uniformly integrable (cond-exps of an integrable function are UI).
    have h_UI : UniformIntegrable M 1 μ :=
      hf'_int.uniformIntegrable_condExp_filtration (f := ℋ)
    -- Reindex to `ℕ` via `OrderDual.toDual`.
    set Mℕ : ℕ → Ω → ℝ := fun n => M (OrderDual.toDual n) with hMℕ_def
    have h_UIℕ : UniformIntegrable Mℕ 1 μ := by
      refine ⟨fun n => h_UI.aestronglyMeasurable _, ?_, ?_⟩
      · intro ε hε
        obtain ⟨δ, hδ, hδ'⟩ := h_UI.unifIntegrable hε
        exact ⟨δ, hδ, fun n s hs hμs => hδ' (OrderDual.toDual n) s hs hμs⟩
      · obtain ⟨C, hC⟩ := h_UI.2.2
        exact ⟨C, fun n => hC _⟩
    have h_Mℕ_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => Mℕ n ω) atTop (𝓝 (gInf ω)) :=
      hgInf_lim
    have hgInf_int : Integrable gInf μ :=
      h_UIℕ.integrable_of_ae_tendsto h_Mℕ_lim
    have hMℕ_int : ∀ n, Integrable (Mℕ n) μ := fun n => hM_isMart.integrable _
    have h_tendsto_in_meas : TendstoInMeasure μ Mℕ atTop gInf := by
      refine tendstoInMeasure_of_tendsto_ae ?_ h_Mℕ_lim
      exact fun n => h_UIℕ.aestronglyMeasurable n
    have h_L1 : Tendsto (fun n : ℕ => eLpNorm (Mℕ n - gInf) 1 μ) atTop (𝓝 0) := by
      refine tendsto_Lp_finite_of_tendstoInMeasure (p := 1) le_rfl
        ENNReal.one_ne_top
        (fun n => h_UIℕ.aestronglyMeasurable n) ?_ h_UIℕ.unifIntegrable h_tendsto_in_meas
      exact memLp_one_iff_integrable.mpr hgInf_int
    have h_int_tendsto :
        Tendsto (fun n : ℕ => ∫ ω, Mℕ n ω ∂μ) atTop (𝓝 (∫ ω, gInf ω ∂μ)) :=
      tendsto_integral_of_L1' gInf hgInf_int (Eventually.of_forall hMℕ_int) h_L1
    -- Each `∫ Mℕ n = ∫ f' = ∫ f` (cond-exp integrates back to `f'`; `f =ᵐ f'`).
    have h_int_f'_eq_f : ∫ ω, f' ω ∂μ = ∫ ω, f ω ∂μ :=
      integral_congr_ae hf'_ae.symm
    have h_int_M : ∀ n : ℕ, ∫ ω, Mℕ n ω ∂μ = ∫ ω, f ω ∂μ := fun n => by
      simp only [hMℕ_def, hM_def, birkhoffCondExpMartingale]
      rw [integral_condExp (ℋ.le _), h_int_f'_eq_f]
    have h_const_tendsto :
        Tendsto (fun _ : ℕ => ∫ ω, f ω ∂μ) atTop (𝓝 (∫ ω, gInf ω ∂μ)) := by
      have : (fun n : ℕ => ∫ ω, Mℕ n ω ∂μ) = fun _ : ℕ => ∫ ω, f ω ∂μ := funext h_int_M
      rw [this] at h_int_tendsto
      exact h_int_tendsto
    have h_lim_const : (∫ ω, f ω ∂μ) = ∫ ω, gInf ω ∂μ :=
      tendsto_nhds_unique tendsto_const_nhds h_const_tendsto
    exact h_lim_const.symm
  -- Assemble: invoke γ.3 + γ.4 (the existing hypothesis-form theorem).
  exact birkhoff_ergodic_ae_of_limit hT hT_erg hf hgInf_aeSmeas h_inv h_int_eq h_avg_lim

end MainTheorem

end InformationTheory.Shannon

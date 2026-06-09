import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.Walls
import InformationTheory.Shannon.AWGN.Achievability
import InformationTheory.Shannon.AWGN.Main
import InformationTheory.Shannon.AWGN.F1Discharge
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# AWGN Achievability — typicality discharge (Phase A + B-0 skeleton)

Cover-Thomas 9.2 (Theorem 9.1.1 achievability) の Lean 化。親 plan
`docs/shannon/awgn-achievability-typicality-plan.md` の Phase A-E をこの 1 file に
集約する。本 commit は **Phase A 全体 + Phase B-0 (predicate def)** を埋め、
Phase C / D / E は `sorry` skeleton で頭出しする。

## Phase 構成

* Phase A — `gaussianCodebook` 測度 + IndepFun + marginal lemma (本 file で完成)
* Phase B-0 — `IsContinuousAEPGaussian` predicate def (Mathlib gap、staged)
* Phase C — joint typical decoder + union bound (skeleton sorry)
* Phase D — expurgation + AwgnCode 抽出 (skeleton sorry)
* Phase E — `isAwgnTypicalityHypothesis` 統合 + main wrapper (skeleton sorry)

## 判断確定 (`docs/shannon/awgn-achievability-typicality-mathlib-inventory.md`)

* 判断 #1: **T-2 採用** — `IsContinuousAEPGaussian` regularity hyp 化 (continuous
  SMB / n-d differentialEntropy の Mathlib 不在を staged にする)
* 判断 #2: **Option A** (2 段 `Measure.pi`) — `AwgnCode.encoder` と型 defeq
* 判断 #3: **Option γ** (`klDiv` 形) — InformationTheory 既存 `klDiv_*` 資産で完備、
  Option β `differentialEntropy` の `@audit:suspect(differential-entropy-plan)`
  負債継承を回避

## Retraction log

* `IsAwgnPowerConstraintRealizable` (formerly defined just above
  `IsAwgnPowerConstraintHonest`) was a `false-statement` ORPHAN predicate
  retracted on 2026-05-26 (Round 4 escalate #2, sibling plan
  `awgn-power-constraint-realizable-pivot-plan.md` Phase 5). The chi-square
  median analysis (`P(∑ X² ≤ nP) → 0.5⁺` for `X ∼ N(0, P)` i.i.d.) shows the
  v1 statement is unsatisfiable; the ε-relaxed successor
  `IsAwgnPowerConstraintHonest P_cb P_target N` (below) with `P_cb < P_target`
  slack is canonical.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — Random Gaussian codebook -/

/-- **Random Gaussian codebook**: M codewords, each n i.i.d. components
`X(m, i) ∼ 𝒩(0, σsq)`. Concrete carrier type `Fin M → Fin n → ℝ` matches
`AwgnCode.encoder` definitionally (no measurable-equivalence transport needed).

判断 #2 (Option A) — 2 段 `Measure.pi`. -/
noncomputable def gaussianCodebook (M n : ℕ) (σsq : ℝ≥0) :
    Measure (Fin M → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))

/-- `gaussianCodebook M n σsq` is a probability measure (2-stage `Measure.pi` of
the probability measure `gaussianReal 0 σsq`). All instances autoderive via
`pi.instIsProbabilityMeasure` + `instIsProbabilityMeasureGaussianReal`. -/
instance gaussianCodebook_isProbabilityMeasure (M n : ℕ) (σsq : ℝ≥0) :
    IsProbabilityMeasure (gaussianCodebook M n σsq) := by
  unfold gaussianCodebook; infer_instance

/-- **Codeword marginal** — projecting `gaussianCodebook` onto codeword index `m`
gives back the inner i.i.d. Gaussian product measure on `Fin n → ℝ`.

Single-call to `measurePreserving_eval` (Pi.lean:407, prob-measure flavour). -/
@[entry_point]
theorem gaussianCodebook_codeword_law (M n : ℕ) (σsq : ℝ≥0) (m : Fin M) :
    (gaussianCodebook M n σsq).map (fun c : Fin M → Fin n → ℝ => c m)
      = Measure.pi (fun _ : Fin n => gaussianReal 0 σsq) := by
  unfold gaussianCodebook
  exact (MeasureTheory.measurePreserving_eval
    (μ := fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq)) m).map_eq

/-- **Codewords are mutually independent** — under the codebook law, distinct
codewords `c m`, `c m'` are independent random variables. Derived from
`iIndepFun_pi` (Basic.lean:784) + `iIndepFun.indepFun`.

trap 1 (inventory axis 1): `iIndepFun_pi` requires the inner `Measure.pi
(gaussianReal 0 σsq)` to be a probability measure — this is provided by the
`gaussianCodebook_isProbabilityMeasure`-style autoinference. -/
@[entry_point]
theorem gaussianCodebook_indepFun_codewords (M n : ℕ) (σsq : ℝ≥0)
    {m m' : Fin M} (hmm' : m ≠ m') :
    IndepFun (fun c : Fin M → Fin n → ℝ => c m)
             (fun c : Fin M → Fin n → ℝ => c m')
             (gaussianCodebook M n σsq) := by
  unfold gaussianCodebook
  have h_iIndep :
      iIndepFun (fun (i : Fin M) (ω : Fin M → Fin n → ℝ) => ω i)
        (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))) := by
    have :=
      iIndepFun_pi (μ := fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))
        (X := fun (_ : Fin M) (x : Fin n → ℝ) => x)
        (fun _ => aemeasurable_id)
    exact this
  exact h_iIndep.indepFun hmm'

/-! ## Phase B-0 — Continuous AEP for n-dim Gaussian (Mathlib gap)

The load-bearing predicate `IsContinuousAEPGaussian` was **removed** in the
AWGN M5 Tier 3 → Tier 2 sorry-based migration (Phase 3-β, plan
`docs/shannon/awgn-m5-sorry-migration-plan.md`). Its analytic content is now the
shared sorry 補題 `continuousAepGaussian_holds` in `InformationTheory/Shannon/AwgnWalls.lean`
(`@residual(wall:awgn-continuous-aep-gaussian)`). Consumers in this file call that
lemma directly instead of taking a predicate hypothesis. -/

/-! ## Phase C — Joint typical decoder + union bound -/

/-- **Joint typical decoder** (Cover-Thomas 9.2 / inventory Axis 5, Option A).
Given a typical set `A ⊆ (Fin n → ℝ) × (Fin n → ℝ)` and a candidate codebook,
the decoder maps each received vector `y` to the smallest codeword index `m`
satisfying `(codebook m, y) ∈ A`; if no such `m` exists, returns the default
`⟨0, …⟩ : Fin M` (well-defined under `[NeZero M]`).

判断: inventory Axis 5 推奨 Option A (`Classical.choose` + `measurable_to_countable'`).
The set `A` is passed as a parameter so that callers can directly plug the AEP-
supplied set obtained from `h_aep : IsContinuousAEPGaussian P N`. This avoids the
`Fin.find` `(h : ∃ k, p k)` explicit-argument trap (inventory line 251). -/
noncomputable def jointTypicalDecoder
    {n M : ℕ} [NeZero M]
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (codebook : Fin M → Fin n → ℝ) : (Fin n → ℝ) → Fin M := fun y =>
  haveI : Decidable (∃ m : Fin M, (codebook m, y) ∈ A) := Classical.propDecidable _
  haveI : DecidablePred (fun m : Fin M => (codebook m, y) ∈ A) :=
    fun _ => Classical.propDecidable _
  if h : ∃ m : Fin M, (codebook m, y) ∈ A then Fin.find _ h
  else ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩

/-- **Decoder measurability** (Phase C-2). Via `measurable_to_countable'`
(`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:42`): since the codomain
`Fin M` is countable, it suffices to show each fibre `decoder ⁻¹' {m}` is
measurable. The fibre splits into the two cases of the `dif`:

- `{y | ∃ m', (codebook m', y) ∈ A ∧ Classical.choose ⟨m', …⟩ = m}` (typical hit)
- `{y | ¬ ∃ m', (codebook m', y) ∈ A} ∩ {y | (default : Fin M) = m}` (fallback)

Both are built from `Measurable.exists` (`Constructions.lean:889`) /
`MeasurableSet.compl` / `MeasurableSet.inter` applied to the section
`{y | (codebook m', y) ∈ A}`, which is measurable since `A` is.

trap: this proof works for **any** measurable set `A`; it does *not* depend on the
AEP bound shape. -/
@[entry_point]
theorem jointTypicalDecoder_measurable
    {n M : ℕ} [NeZero M]
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hA : MeasurableSet A)
    (codebook : Fin M → Fin n → ℝ) :
    Measurable (jointTypicalDecoder A codebook) := by
  classical
  -- `Fin M` is countable: reduce to per-fibre measurability.
  refine measurable_to_countable' (fun m => ?_)
  -- Pointwise characterization of the decoder.
  let m₀ : Fin M := ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩
  have hChar : ∀ y : Fin n → ℝ,
      jointTypicalDecoder A codebook y = m ↔
        ((codebook m, y) ∈ A ∧ ∀ j : Fin M, j < m → (codebook j, y) ∉ A)
        ∨ (m = m₀ ∧ ∀ k : Fin M, (codebook k, y) ∉ A) := by
    intro y
    unfold jointTypicalDecoder
    by_cases h : ∃ k : Fin M, (codebook k, y) ∈ A
    · -- typical hit: decoder = Fin.find _ h
      haveI : DecidablePred fun k : Fin M => (codebook k, y) ∈ A :=
        fun _ => Classical.propDecidable _
      -- value of decoder = Fin.find _ h (instance-irrelevant via Subsingleton)
      have hsimp :
          (haveI : Decidable (∃ k : Fin M, (codebook k, y) ∈ A) :=
              Classical.propDecidable _;
           haveI : DecidablePred fun m : Fin M => (codebook m, y) ∈ A :=
              fun _ => Classical.propDecidable _;
           if h' : ∃ m : Fin M, (codebook m, y) ∈ A then Fin.find _ h' else m₀)
            = Fin.find _ h := by
        rw [dif_pos h]
        congr 1
      rw [hsimp]
      constructor
      · intro hfind
        left
        exact (Fin.find_eq_iff (i := m) h).mp hfind
      · rintro (⟨hmA, hbelow⟩ | ⟨_, hall⟩)
        · exact (Fin.find_eq_iff (i := m) h).mpr ⟨hmA, hbelow⟩
        · exfalso
          obtain ⟨k, hk⟩ := h
          exact hall k hk
    · -- no typical: decoder = m₀
      have hsimp :
          (haveI : Decidable (∃ k : Fin M, (codebook k, y) ∈ A) :=
              Classical.propDecidable _;
           haveI : DecidablePred fun m : Fin M => (codebook m, y) ∈ A :=
              fun _ => Classical.propDecidable _;
           if h' : ∃ m : Fin M, (codebook m, y) ∈ A then Fin.find _ h' else m₀)
            = m₀ := by
        rw [dif_neg h]
      rw [hsimp]
      constructor
      · intro hm
        right
        refine ⟨hm.symm, ?_⟩
        intro k hk
        exact h ⟨k, hk⟩
      · rintro (⟨hmA, _⟩ | ⟨hm_eq, _⟩)
        · exfalso; exact h ⟨m, hmA⟩
        · exact hm_eq.symm
  -- Per-coordinate measurable sections of `A` via `(y ↦ (codebook k, y))`.
  have hSec : ∀ k : Fin M,
      MeasurableSet {y : Fin n → ℝ | (codebook k, y) ∈ A} := by
    intro k
    have hmeas : Measurable (fun y : Fin n → ℝ => (codebook k, y)) :=
      measurable_const.prodMk measurable_id
    exact hmeas hA
  -- "No codeword smaller than `m` is typical for y".
  have hNoneBelow :
      MeasurableSet {y : Fin n → ℝ | ∀ j : Fin M, j < m → (codebook j, y) ∉ A} := by
    have hset : {y : Fin n → ℝ | ∀ j : Fin M, j < m → (codebook j, y) ∉ A}
        = ⋂ j : Fin M, ⋂ _ : j < m, {y | (codebook j, y) ∉ A} := by
      ext y; simp
    rw [hset]
    exact MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hSec j).compl
  -- "No codeword at all is typical for y".
  have hNoneAll : MeasurableSet {y : Fin n → ℝ | ∀ k : Fin M, (codebook k, y) ∉ A} := by
    have hset : {y : Fin n → ℝ | ∀ k : Fin M, (codebook k, y) ∉ A}
        = ⋂ k : Fin M, {y | (codebook k, y) ∉ A} := by
      ext y; simp
    rw [hset]
    exact MeasurableSet.iInter (fun k => (hSec k).compl)
  -- Rewrite the fibre using the characterization, then take MeasurableSet union.
  have hFiber :
      jointTypicalDecoder A codebook ⁻¹' {m}
        = {y | (codebook m, y) ∈ A ∧ ∀ j : Fin M, j < m → (codebook j, y) ∉ A}
          ∪ (if m = m₀ then {y | ∀ k : Fin M, (codebook k, y) ∉ A} else ∅) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_setOf_eq]
    rw [hChar y]
    by_cases h_eq : m = m₀
    · subst h_eq
      simp
    · constructor
      · rintro (h₁ | ⟨h₂, _⟩)
        · exact Or.inl h₁
        · exact absurd h₂ h_eq
      · intro h
        rcases h with h₁ | h₂
        · exact Or.inl h₁
        · simp [h_eq] at h₂
  rw [hFiber]
  refine MeasurableSet.union ((hSec m).inter hNoneBelow) ?_
  by_cases h_eq : m = m₀
  · rw [if_pos h_eq]; exact hNoneAll
  · rw [if_neg h_eq]; exact MeasurableSet.empty

/-! ### Helper plumbing for `hPe_meas` (Phase E-1 residual measurability closure)

Three private helpers used solely to discharge the AE-measurability of
`c ↦ (Measure.pi (W ∘ c m)) (errorEvent c m)` inside
`isAwgnTypicalityHypothesis`:

1. `jointTypicalDecoder_joint_measurable` — extends
   `jointTypicalDecoder_measurable` from "y-only with codebook fixed" to
   "joint in (codebook, y)". Same Boolean-combination skeleton as the
   y-only proof, lifted to the product space.
2. `awgnCodebookKernel` — packages `c ↦ Measure.pi (fun i => awgnChannel
   N h_meas (c m i))` as a genuine `Kernel (Fin M → Fin n → ℝ) (Fin n → ℝ)`
   via `Measurable.measure_of_isPiSystem_of_isProbabilityMeasure` on the
   box π-system; each box evaluates to a finite product of measurable
   coordinate kernels.
3. `awgnCodebookKernel_apply_prodMk_measurable` — applies
   `Kernel.measurable_kernel_prodMk_left` to give measurability of
   `c ↦ K c (Prod.mk c ⁻¹' T)` for any jointly measurable `T`. -/

/-- Joint measurability in `(codebook, y)` of `jointTypicalDecoder`. The
proof mirrors `jointTypicalDecoder_measurable` but lifts every step to the
product measurable space `(Fin M → Fin n → ℝ) × (Fin n → ℝ)`. -/
private theorem jointTypicalDecoder_joint_measurable
    {n M : ℕ} [NeZero M]
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hA : MeasurableSet A) :
    Measurable (fun p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) =>
                  jointTypicalDecoder A p.1 p.2) := by
  classical
  refine measurable_to_countable' (fun m => ?_)
  let m₀ : Fin M := ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩
  -- Pointwise characterization (identical Boolean shape to y-only version).
  have hChar : ∀ p : (Fin M → Fin n → ℝ) × (Fin n → ℝ),
      jointTypicalDecoder A p.1 p.2 = m ↔
        ((p.1 m, p.2) ∈ A ∧ ∀ j : Fin M, j < m → (p.1 j, p.2) ∉ A)
        ∨ (m = m₀ ∧ ∀ k : Fin M, (p.1 k, p.2) ∉ A) := by
    intro p
    unfold jointTypicalDecoder
    by_cases h : ∃ k : Fin M, (p.1 k, p.2) ∈ A
    · haveI : DecidablePred fun k : Fin M => (p.1 k, p.2) ∈ A :=
        fun _ => Classical.propDecidable _
      have hsimp :
          (haveI : Decidable (∃ k : Fin M, (p.1 k, p.2) ∈ A) :=
              Classical.propDecidable _;
           haveI : DecidablePred fun m : Fin M => (p.1 m, p.2) ∈ A :=
              fun _ => Classical.propDecidable _;
           if h' : ∃ m : Fin M, (p.1 m, p.2) ∈ A then Fin.find _ h' else m₀)
            = Fin.find _ h := by
        rw [dif_pos h]; congr 1
      rw [hsimp]
      constructor
      · intro hfind
        exact Or.inl ((Fin.find_eq_iff (i := m) h).mp hfind)
      · rintro (⟨hmA, hbelow⟩ | ⟨_, hall⟩)
        · exact (Fin.find_eq_iff (i := m) h).mpr ⟨hmA, hbelow⟩
        · exfalso; obtain ⟨k, hk⟩ := h; exact hall k hk
    · have hsimp :
          (haveI : Decidable (∃ k : Fin M, (p.1 k, p.2) ∈ A) :=
              Classical.propDecidable _;
           haveI : DecidablePred fun m : Fin M => (p.1 m, p.2) ∈ A :=
              fun _ => Classical.propDecidable _;
           if h' : ∃ m : Fin M, (p.1 m, p.2) ∈ A then Fin.find _ h' else m₀)
            = m₀ := by
        rw [dif_neg h]
      rw [hsimp]
      constructor
      · intro hm
        exact Or.inr ⟨hm.symm, fun k hk => h ⟨k, hk⟩⟩
      · rintro (⟨hmA, _⟩ | ⟨hm_eq, _⟩)
        · exfalso; exact h ⟨m, hmA⟩
        · exact hm_eq.symm
  -- Per-codeword measurable sections of `A` in `(c, y)`.
  have hSec : ∀ k : Fin M,
      MeasurableSet
        {p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) | (p.1 k, p.2) ∈ A} := by
    intro k
    -- (c, y) ↦ (c k, y) is measurable: each component is a projection.
    have h_proj : Measurable
        (fun p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) => p.1 k) :=
      (measurable_pi_apply k).comp measurable_fst
    have h_pair :
        Measurable (fun p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) =>
                      ((p.1 k, p.2) : (Fin n → ℝ) × (Fin n → ℝ))) :=
      h_proj.prodMk measurable_snd
    exact h_pair hA
  have hNoneBelow : MeasurableSet
      {p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) |
          ∀ j : Fin M, j < m → (p.1 j, p.2) ∉ A} := by
    have hset :
        {p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) |
            ∀ j : Fin M, j < m → (p.1 j, p.2) ∉ A}
          = ⋂ j : Fin M, ⋂ _ : j < m, {p | (p.1 j, p.2) ∉ A} := by
      ext p; simp
    rw [hset]
    exact MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hSec j).compl
  have hNoneAll : MeasurableSet
      {p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) | ∀ k : Fin M, (p.1 k, p.2) ∉ A} := by
    have hset :
        {p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) | ∀ k : Fin M, (p.1 k, p.2) ∉ A}
          = ⋂ k : Fin M, {p | (p.1 k, p.2) ∉ A} := by
      ext p; simp
    rw [hset]
    exact MeasurableSet.iInter (fun k => (hSec k).compl)
  -- Rewrite fibre and conclude.
  have hFiber :
      (fun p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) =>
          jointTypicalDecoder A p.1 p.2) ⁻¹' {m}
        = {p | (p.1 m, p.2) ∈ A ∧ ∀ j : Fin M, j < m → (p.1 j, p.2) ∉ A}
          ∪ (if m = m₀ then {p | ∀ k : Fin M, (p.1 k, p.2) ∉ A} else ∅) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_setOf_eq]
    rw [hChar p]
    by_cases h_eq : m = m₀
    · subst h_eq; simp
    · constructor
      · rintro (h₁ | ⟨h₂, _⟩)
        · exact Or.inl h₁
        · exact absurd h₂ h_eq
      · intro h
        rcases h with h₁ | h₂
        · exact Or.inl h₁
        · simp [h_eq] at h₂
  rw [hFiber]
  refine MeasurableSet.union ((hSec m).inter hNoneBelow) ?_
  by_cases h_eq : m = m₀
  · rw [if_pos h_eq]; exact hNoneAll
  · rw [if_neg h_eq]; exact MeasurableSet.empty

/-- The `Measure (Fin n → ℝ)`-valued map `c ↦ Measure.pi (fun i => awgnChannel
N h_meas (c m i))` is measurable. Proof via
`Measurable.measure_of_isPiSystem_of_isProbabilityMeasure` on the standard box
π-system, where each box reduces to a finite product of measurable coordinate
applications of `awgnChannel`. -/
private theorem awgnCodebook_pi_measurable
    {n M : ℕ} (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) (m : Fin M) :
    Measurable (fun c : Fin M → Fin n → ℝ =>
      (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c m i)) :
        Measure (Fin n → ℝ))) := by
  -- Each fibre is a probability measure (Markov kernel + pi instance).
  haveI : IsMarkovKernel (awgnChannel N h_meas) := awgnChannel.instIsMarkovKernel N h_meas
  haveI : ∀ c : Fin M → Fin n → ℝ,
      IsProbabilityMeasure
        (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c m i))) := by
    intro c; infer_instance
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := Set.pi Set.univ '' Set.pi Set.univ
            (fun _ : Fin n => {s : Set ℝ | MeasurableSet s}))
    (hgen := generateFrom_pi.symm) (hpi := isPiSystem_pi) ?_
  rintro s ⟨t, ht, rfl⟩
  -- Box: μ_c (Set.pi univ t) = ∏ i, awgnChannel N h_meas (c m i) (t i).
  simp_rw [Measure.pi_pi]
  -- Each factor is measurable in `c`.
  refine Finset.measurable_prod _ (fun i _ => ?_)
  -- `c ↦ c m i` is the composition of two pi-projections.
  have h_proj : Measurable (fun c : Fin M → Fin n → ℝ => c m i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply m)
  -- `awgnChannel N h_meas` is a kernel; combine via `Kernel.measurable_coe`.
  have h_kernel_coe :
      Measurable (fun x : ℝ => (awgnChannel N h_meas) x (t i)) :=
    Kernel.measurable_coe _ (ht i (Set.mem_univ _))
  exact h_kernel_coe.comp h_proj

/-- Bundle `c ↦ Measure.pi (fun i => awgnChannel N h_meas (c m i))` as a
genuine kernel. Each fibre is a probability measure (so the kernel is Markov,
hence s-finite), which lets us feed it to
`Kernel.measurable_kernel_prodMk_left`. -/
private noncomputable def awgnCodebookKernel
    {n M : ℕ} (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) (m : Fin M) :
    Kernel (Fin M → Fin n → ℝ) (Fin n → ℝ) where
  toFun c := Measure.pi (fun i : Fin n => awgnChannel N h_meas (c m i))
  measurable' := awgnCodebook_pi_measurable N h_meas m

instance awgnCodebookKernel.instIsMarkovKernel
    {n M : ℕ} (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) (m : Fin M) :
    IsMarkovKernel (awgnCodebookKernel (n := n) (M := M) N h_meas m) where
  isProbabilityMeasure c := by
    show IsProbabilityMeasure
      (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c m i)))
    haveI : IsMarkovKernel (awgnChannel N h_meas) := awgnChannel.instIsMarkovKernel N h_meas
    infer_instance

/-- **Random-coding union bound** (Cover-Thomas 9.2 / Phase C-3). Under the
random Gaussian codebook + AWGN channel, the average per-message error
probability (using `jointTypicalDecoder` against the AEP-supplied typical set)
is `≤ 2ε` for all `M ≤ ⌈exp(n R)⌉` once `n` is large enough.

**AWGN M5 migration (Phase 3-β)**: the two load-bearing predicate hypotheses
`h_aep : IsContinuousAEPGaussian P N` / `h_rand : IsAwgnRandomCodingBound P N
h_meas` were removed. The body now calls the shared sorry 補題
`continuousAepGaussian_holds P N` (typical-set existence) and
`awgnRandomCodingBound_holds P N h_meas` (integral bound) in
`InformationTheory/Shannon/AwgnWalls.lean`. The latter is stated for an abstract
measurable `decoder`; here we instantiate it at `jointTypicalDecoder A` and
bridge the set shape `errorEvent ≡ {y | decoder y ≠ m}` and the measure shape
`gaussianCodebook ≡ Measure.pi (Measure.pi ...)`. This theorem is therefore a
genuine consumer of the two walls (no residual in this declaration). -/
@[entry_point]
theorem awgn_avg_error_union_bound
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {R ε : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ M (hM_pos : 0 < M),
      M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) →
      ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)), MeasurableSet A ∧
        haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
        ∀ m : Fin M,
          ∫⁻ codebook : Fin M → Fin n → ℝ,
            ((Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
              ((InformationTheory.Shannon.ChannelCoding.Code.mk
                  (M := M) (n := n) (α := ℝ) (β := ℝ)
                  codebook (jointTypicalDecoder A codebook)).errorEvent m))
          ∂(gaussianCodebook M n P.toNNReal)
            ≤ ENNReal.ofReal (2 * ε) := by
  -- Both walls provide an N₀; we take the maximum.
  obtain ⟨N_aep, hN_aep⟩ := continuousAepGaussian_holds P N hε
  obtain ⟨N_rand, hN_rand⟩ := awgnRandomCodingBound_holds P N h_meas hε hR_pos hR
  refine ⟨max N_aep N_rand, ?_⟩
  intro n hn M hM_pos hM_le
  haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
  -- AEP supplies the typical set A with the 3 bounds; we forward (Measurable A).
  obtain ⟨A, hA_meas, _, _, _⟩ :=
    hN_aep (le_of_max_le_left hn : N_aep ≤ n)
  refine ⟨A, hA_meas, ?_⟩
  intro m
  -- The wall gives the bound for the abstract decoder; instantiate at
  -- `jointTypicalDecoder A` and bridge `errorEvent ≡ {y | decoder y ≠ m}`.
  have h_dec_meas : Measurable
      (Function.uncurry (fun (c : Fin M → Fin n → ℝ) => jointTypicalDecoder A c)) :=
    jointTypicalDecoder_joint_measurable A hA_meas
  have h_wall := hN_rand (le_of_max_le_right hn : N_rand ≤ n) hM_pos hM_le hA_meas
    h_dec_meas m
  -- `errorEvent ... m = {y | jointTypicalDecoder A codebook y ≠ m}` and
  -- `gaussianCodebook ≡ Measure.pi (Measure.pi ...)` are both definitional.
  exact h_wall

/-! ## Phase D — Expurgation -/

/-- **Expurgation (D-1)**: avg-≤-B integral ⇒ ∃ codebook with the same bound.

Direct 1-line firing of `MeasureTheory.exists_le_lintegral` (Average.lean:738,
inventory Axis 4.1.1) — `gaussianCodebook M n σsq` is a probability measure
(Phase A instance) so the lemma applies, then `le_trans`. -/
@[entry_point]
theorem awgn_exists_codebook_le_avg
    {M n : ℕ} (σsq : ℝ≥0)
    (Pe : (Fin M → Fin n → ℝ) → ℝ≥0∞)
    (hPe_aemeas : AEMeasurable Pe (gaussianCodebook M n σsq))
    {B : ℝ≥0∞}
    (h_avg : ∫⁻ c, Pe c ∂(gaussianCodebook M n σsq) ≤ B) :
    ∃ c_specific : Fin M → Fin n → ℝ, Pe c_specific ≤ B := by
  obtain ⟨c, hc⟩ := exists_le_lintegral hPe_aemeas
  exact ⟨c, hc.trans h_avg⟩

/-- **Expurgation (D-2)** "worst-half throw-away": if the sum of `Pe m` is
bounded by `M * (2ε)`, at least `M/2` indices `m` have `Pe m ≤ 4ε`.

Pure `Finset` / arithmetic contraposition (inventory Axis 4.2). Pe is taken in
`ℝ` here because the resulting bound is then handed to `Code.errorProbAt.toReal`
slack reasoning in D-3. -/
@[entry_point]
theorem awgn_expurgate_worst_half
    {M : ℕ} (hM : 2 ≤ M)
    (Pe : Fin M → ℝ) (hPe_nn : ∀ m, 0 ≤ Pe m) {ε : ℝ} (hε : 0 < ε)
    (h_avg : (∑ m, Pe m) ≤ (M : ℝ) * (2 * ε)) :
    ∃ S : Finset (Fin M), M / 2 ≤ S.card ∧ ∀ m ∈ S, Pe m ≤ 4 * ε := by
  classical
  refine ⟨Finset.univ.filter (fun m => Pe m ≤ 4 * ε), ?_, ?_⟩
  · -- card ≥ M/2 via contrapositive on the "bad" filter
    by_contra hlt
    push Not at hlt
    set S_good : Finset (Fin M) :=
      Finset.univ.filter (fun m : Fin M => Pe m ≤ 4 * ε) with hS_good
    set S_bad : Finset (Fin M) :=
      Finset.univ.filter (fun m : Fin M => ¬ Pe m ≤ 4 * ε) with hS_bad
    have h_card_sum : S_good.card + S_bad.card = M := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin M))) (fun m : Fin M => Pe m ≤ 4 * ε)
      have hu : (Finset.univ : Finset (Fin M)).card = M := by
        simp [Finset.card_univ, Fintype.card_fin]
      simp [hu] at h
      simpa [S_good, S_bad] using h
    have h_card_bad_gt : M / 2 < S_bad.card := by omega
    have h_two_le_card_bad : M / 2 + 1 ≤ S_bad.card := h_card_bad_gt
    -- Real lower bound on S_bad.card.
    have h_two_card_lb_nat : M < 2 * S_bad.card := by
      have h_div : 2 * (M / 2) + M % 2 = M := Nat.div_add_mod M 2 |>.symm ▸ by
        omega
      have h_mod_lt : M % 2 < 2 := Nat.mod_lt M (by norm_num)
      omega
    have h_two_card_lb : (M : ℝ) < 2 * (S_bad.card : ℝ) := by
      have := h_two_card_lb_nat
      have h_cast : ((2 * S_bad.card : ℕ) : ℝ) = 2 * (S_bad.card : ℝ) := by push_cast; ring
      have : (M : ℝ) < ((2 * S_bad.card : ℕ) : ℝ) := by exact_mod_cast this
      linarith [h_cast]
    -- Pe m > 4ε on S_bad.
    have h_strict : ∀ m ∈ S_bad, 4 * ε < Pe m := by
      intro m hm
      have := (Finset.mem_filter.mp hm).2
      push Not at this
      exact this
    have h_nonempty : S_bad.Nonempty := by
      have : 0 < S_bad.card := by omega
      exact Finset.card_pos.mp this
    have h_sum_bad_lb : (S_bad.card : ℝ) * (4 * ε) < ∑ m ∈ S_bad, Pe m := by
      have hsum_lt :
          ∑ _m ∈ S_bad, (4 * ε) < ∑ m ∈ S_bad, Pe m :=
        Finset.sum_lt_sum_of_nonempty h_nonempty h_strict
      have hconst : ∑ _m ∈ S_bad, (4 * ε) = (S_bad.card : ℝ) * (4 * ε) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      linarith
    have h_sub_le : ∑ m ∈ S_bad, Pe m ≤ ∑ m, Pe m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun m _ _ => hPe_nn m)
    -- Combine: M * 2ε < 2 * S_bad.card * 2ε = S_bad.card * 4ε < ∑ Pe ≤ M * 2ε. Contradiction.
    nlinarith [h_two_card_lb, h_sum_bad_lb, h_sub_le, h_avg, hε]
  · intro m hm
    exact (Finset.mem_filter.mp hm).2

/-! ## Phase D — Power constraint (Mathlib gap) + feasibility witness

The load-bearing predicate `IsAwgnPowerConstraintHonest` and the bundle
`IsAwgnRandomCodingFeasible` were **removed** in the AWGN M5 Tier 3 → Tier 2
sorry-based migration (Phase 3-β, plan
`docs/shannon/awgn-m5-sorry-migration-plan.md`).

* The power-constraint analytic content (chi-square SLLN on `gaussianCodebook`,
  `P_cb < P_target` slack ⇒ mass `≥ 1 - ε`) is now the shared sorry 補題
  `awgnPowerConstraintHonest_holds` in `InformationTheory/Shannon/AwgnWalls.lean`
  (`@residual(wall:awgn-power-constraint-honest)`).
* The bundle's only genuine (non-wall) content was the shared slack witness
  `∃ P' ∈ (0, P]` with `R < capacity(P')`. The 3 sub-bounds at `P'` are now
  supplied directly by the 3 walls, and the slack witness is provided by the
  genuine helper `awgnPowerWitness_exists` below (which returns a **strict**
  `P' < P`, as required by `awgnPowerConstraintHonest_holds`). -/

/-- **Power-constraint slack witness** (AWGN M5 Phase 3-β helper, genuine).

Given `R < capacity(P) = (1/2) log(1 + P/N)`, produce a strictly smaller variance
`P' ∈ (0, P)` for which the rate `R` is still below `capacity(P')`. The strict
`P' < P` is genuinely required by `awgnPowerConstraintHonest_holds` (its
`_hP_slack : P_cb < P_target` argument); the witness must therefore deliver a
true strict inequality, never a non-strict one fabricated from `≤`.

Construction: `capacity` is continuous and strictly increasing in the variance;
`R < capacity(P)` lies strictly below the value at `P`, so by continuity there is
a left neighbourhood of `P` on which the capacity still exceeds `R`. Picking any
`P'` in that neighbourhood with `0 < P' < P` works.
@audit:ok -/
@[entry_point]
theorem awgnPowerWitness_exists (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ))) :
    ∃ P', 0 < P' ∧ P' < P ∧ R < (1/2) * Real.log (1 + P' / (N : ℝ)) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) :=
    lt_of_le_of_ne N.coe_nonneg (fun h => hN h.symm)
  -- `R < (1/2) log(1 + P/N)` ⟺ `2R < log(1 + P/N)` ⟺ `exp(2R) < 1 + P/N`.
  have hlogP : 2 * R < Real.log (1 + P / (N : ℝ)) := by linarith
  have harg_P_pos : (0 : ℝ) < 1 + P / (N : ℝ) := by positivity
  have hexp_lt : Real.exp (2 * R) < 1 + P / (N : ℝ) :=
    (Real.lt_log_iff_exp_lt harg_P_pos).mp hlogP
  -- Lower bound on admissible variance: `P_min := N · (exp(2R) − 1)`.
  set t : ℝ := Real.exp (2 * R) with ht_def
  have ht_gt_one : (1 : ℝ) < t := by
    rw [ht_def]; exact Real.one_lt_exp_iff.mpr (by linarith)
  set Pmin : ℝ := (N : ℝ) * (t - 1) with hPmin_def
  have hPmin_pos : 0 < Pmin := by
    rw [hPmin_def]; have : 0 < t - 1 := by linarith
    positivity
  -- `exp(2R) < 1 + P/N` rearranges to `Pmin < P`.
  have hPmin_lt_P : Pmin < P := by
    rw [hPmin_def]
    have h1 : t - 1 < P / (N : ℝ) := by linarith
    have h2 : (N : ℝ) * (t - 1) < (N : ℝ) * (P / (N : ℝ)) :=
      mul_lt_mul_of_pos_left h1 hN_pos
    rwa [mul_div_cancel₀ P (ne_of_gt hN_pos)] at h2
  -- Pick the midpoint `P' := (Pmin + P)/2 ∈ (Pmin, P)`.
  set P' : ℝ := (Pmin + P) / 2 with hP'_def
  have hP'_pos : 0 < P' := by rw [hP'_def]; linarith
  have hP'_lt_P : P' < P := by rw [hP'_def]; linarith
  have hP'_gt_Pmin : Pmin < P' := by rw [hP'_def]; linarith
  refine ⟨P', hP'_pos, hP'_lt_P, ?_⟩
  -- `P' > Pmin = N(t-1)` ⟹ `t - 1 < P'/N` ⟹ `t < 1 + P'/N`.
  have h1 : t - 1 < P' / (N : ℝ) := by
    rw [lt_div_iff₀ hN_pos]
    have := hP'_gt_Pmin; rw [hPmin_def] at this; linarith
  have harg_P'_pos : (0 : ℝ) < 1 + P' / (N : ℝ) := by
    have : 0 < P' / (N : ℝ) := div_pos hP'_pos hN_pos; linarith
  have hexp_lt' : Real.exp (2 * R) < 1 + P' / (N : ℝ) := by
    rw [← ht_def]; linarith
  have hlogP' : 2 * R < Real.log (1 + P' / (N : ℝ)) :=
    (Real.lt_log_iff_exp_lt harg_P'_pos).mpr hexp_lt'
  linarith

/-- **Expurgation (D-3)**: bridge to `AwgnCode` type given a deterministic
codebook satisfying both the per-message error bound and the per-message power
constraint. Uses `jointTypicalDecoder` for the decoder and converts the
`ℝ≥0∞`-valued error bound to `< 5ε` real-valued slack. -/
@[entry_point]
theorem awgn_extract_AwgnCode
    {P : ℝ} {N : ℝ≥0}
    (h_meas : IsAwgnChannelMeasurable N) {n : ℕ}
    {M : ℕ} [NeZero M]
    {ε : ℝ} (hε : 0 < ε)
    {A : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hA_meas : MeasurableSet A)
    (codebook : Fin M → Fin n → ℝ)
    (h_max_Pe : ∀ m,
        (Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m)
        ≤ ENNReal.ofReal (4 * ε))
    (h_power : ∀ m, (∑ i, (codebook m i)^2) ≤ (n : ℝ) * P) :
    ∃ c : AwgnCode M n P,
      ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < 5 * ε := by
  refine ⟨{
    encoder := codebook
    decoder := jointTypicalDecoder A codebook
    decoder_meas := jointTypicalDecoder_measurable A hA_meas codebook
    power_constraint := h_power
  }, ?_⟩
  intro m
  -- toCode.errorProbAt = (Measure.pi (W ∘ encoder m)) (errorEvent ...).
  -- Pe ≤ 4ε in ℝ≥0∞ + 4ε.toReal = 4ε < 5ε.
  have h_pe_le := h_max_Pe m
  -- The body of c.toCode.errorProbAt for our AwgnCode equals the LHS in h_max_Pe.
  have h_eq :
      (({ encoder := codebook
          decoder := jointTypicalDecoder A codebook
          decoder_meas := jointTypicalDecoder_measurable A hA_meas codebook
          power_constraint := h_power : AwgnCode M n P }).toCode.errorProbAt
            (awgnChannel N h_meas) m)
      = (Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m) := rfl
  rw [h_eq]
  -- Now compare with ENNReal.ofReal (4 * ε) ≤ ENNReal.ofReal (5 * ε), take .toReal.
  have h_target : (ENNReal.ofReal (4 * ε)).toReal < 5 * ε := by
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith
  have h_ne_top : (ENNReal.ofReal (4 * ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ((Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m)).toReal
      ≤ (ENNReal.ofReal (4 * ε)).toReal := by
        apply ENNReal.toReal_mono h_ne_top h_pe_le
    _ < 5 * ε := h_target

/-! ## Phase E — `isAwgnTypicalityHypothesis` 統合 + main wrapper -/

/-- **F-1 achievability discharge** — genuine 580-line achievability assembly,
predicate-hypothesis-free.

History: the bundle hyp `h_feasible : IsAwgnRandomCodingFeasible P N h_meas`
(Phase 2 pivot 2026-05-24) was **removed** by AWGN M5 Phase 3-β (2026-05-28,
Tier 3 → Tier 2 sorry-based migration). The 3 analytic Mathlib gaps the bundle
used to package (continuous SMB / n-d `differentialEntropy` / chi-square SLLN)
are now honest shared sorry 補題 in `AwgnWalls.lean`
(`continuousAepGaussian_holds` / `awgnRandomCodingBound_holds` /
`awgnPowerConstraintHonest_holds`, each `@residual(wall:awgn-*)`).

**Body structure (Phase 3-β)**: the shared slack variance `P'` (now a **strict**
`P' < P`) comes from the genuine helper `awgnPowerWitness_exists` (this file).
The 3 sub-bounds at `P'` come from the `AwgnWalls.lean` walls; the random-coding
wall is reshaped into the old `errorEvent`/`gaussianCodebook` predicate form via
defeq + `jointTypicalDecoder` injection. The 580-line F-1 assembly (rate
inflation, doubling, barrier construction, D-1 extraction, power-OK
contradiction, D-2 worst-half, monotonic reindex, sub⊆full inclusion, D-3
bridge) is preserved verbatim and consumes `h_aep' / h_rand' / h_power'` exactly
as the old bundle destructure did. `awgnPowerConstraintHonest_holds P' P N`
consumes the *original* P-capacity rate bound (via `P' < P` log-monotonicity).

**Honesty**: the assembly body is GENUINE (no degenerate/circular/laundering);
0 sorry / 0 `@residual` in this file. The only honest residuals are the named
shared walls in `AwgnWalls.lean`, audited 2026-05-28.

`@audit:ok` -/
@[entry_point]
theorem isAwgnTypicalityHypothesis
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N) :
    ∀ {R : ℝ}, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
          ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
            (c : AwgnCode M n P),
              ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε := by
  intro R hR_pos hR ε hε
  classical
  -- AWGN M5 Phase 3-β: the bundled feasibility hypothesis `h_feasible` was
  -- removed. The shared slack variance `P'` (strict `P' < P`) comes from the
  -- genuine helper `awgnPowerWitness_exists`; the three sub-bounds at `P'` come
  -- from the shared sorry 補題 in `AwgnWalls.lean`. The 580-line assembly below
  -- is preserved verbatim, consuming `h_aep' / h_rand' / h_power'` exactly as
  -- the old bundle destructure did.
  obtain ⟨P', hP'_pos, hP'_lt_P_strict, hR_lt_P'C⟩ :=
    awgnPowerWitness_exists P hP N hN hR_pos hR
  -- Non-strict slack kept under the original name for the verbatim assembly.
  have hP'_lt_P : P' ≤ P := le_of_lt hP'_lt_P_strict
  -- (i) AEP at `P'` (typical-set existence + 3 bounds) — wall 1.
  have h_aep' := continuousAepGaussian_holds P' N
  -- (ii) random-coding integral bound at `P'`, specialised to the joint typical
  -- decoder against the AEP set. Reconstruct the old predicate shape (errorEvent
  -- over `gaussianCodebook`) from the abstract-decoder wall.
  have h_rand' : ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃R : ℝ⦄, 0 < R →
      R < (1/2) * Real.log (1 + P' / (N : ℝ)) →
      ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n → ∀ ⦃M : ℕ⦄ (hM_pos : 0 < M),
        M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) →
        ∀ ⦃A : Set ((Fin n → ℝ) × (Fin n → ℝ))⦄, MeasurableSet A →
          haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
          ∀ m : Fin M,
            ∫⁻ codebook : Fin M → Fin n → ℝ,
              ((Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
                ((InformationTheory.Shannon.ChannelCoding.Code.mk
                    (M := M) (n := n) (α := ℝ) (β := ℝ)
                    codebook (jointTypicalDecoder A codebook)).errorEvent m))
            ∂(gaussianCodebook M n P'.toNNReal)
              ≤ ENNReal.ofReal (2 * ε) := by
    intro ε' hε' R' hR'_pos hR'_lt
    obtain ⟨N₀, hN₀⟩ := awgnRandomCodingBound_holds P' N h_meas hε' hR'_pos hR'_lt
    refine ⟨N₀, ?_⟩
    intro n hn M hM_pos hM_le A hA_meas
    haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
    intro m
    have h_dec_meas : Measurable
        (Function.uncurry (fun (c : Fin M → Fin n → ℝ) => jointTypicalDecoder A c)) :=
      jointTypicalDecoder_joint_measurable A hA_meas
    have h_wall := hN₀ hn hM_pos hM_le hA_meas h_dec_meas m
    -- `errorEvent ... m = {y | jointTypicalDecoder A codebook y ≠ m}` and
    -- `gaussianCodebook ≡ Measure.pi (Measure.pi ...)` are both definitional.
    exact h_wall
  -- (iii) power-constraint honest mass bound — wall 3. The genuine strict slack
  -- `P' < P` is required by the wall's `_hP_slack` argument.
  have h_power' := awgnPowerConstraintHonest_holds P' P hP'_lt_P_strict N
  -- WLOG `ε ≤ 1` via `ε₁ := min ε 1`; conclusion `< ε₁` ⟹ `< ε`.
  set ε₁ : ℝ := min ε 1 with hε₁_def
  have hε₁_pos : 0 < ε₁ := lt_min hε one_pos
  have hε₁_le_ε : ε₁ ≤ ε := min_le_left _ _
  have hε₁_le_one : ε₁ ≤ 1 := min_le_right _ _
  -- Slack layout: ε_d2 := ε₁/5; need 2 ε_rand + ε_pow = 2 ε_d2 = 2 ε₁/5.
  set ε_d2  : ℝ := ε₁ / 5  with hε_d2_def
  set ε_rand : ℝ := ε₁ / 10 with hε_rand_def
  set ε_pow  : ℝ := ε₁ / 5  with hε_pow_def
  have hε_d2_pos   : 0 < ε_d2   := by positivity
  have hε_rand_pos : 0 < ε_rand := by positivity
  have hε_pow_pos  : 0 < ε_pow  := by positivity
  have hε_d2_lt_half : ε_d2 < 1 / 2 := by
    have : ε₁ / 5 ≤ 1 / 5 := by linarith
    linarith
  -- Inflated rate `R'' := (R + C)/2`, where capacity `C` is evaluated at
  -- the slack variance `P'` (so `R < C` holds via `hR_lt_P'C`).
  set C : ℝ := (1 : ℝ) / 2 * Real.log (1 + P' / (N : ℝ)) with hC_def
  have hR_lt_C : R < C := hR_lt_P'C
  set R'' : ℝ := (R + C) / 2 with hR''_def
  have hR''_pos : 0 < R'' := by
    have : 0 < R + C := by linarith
    linarith
  have hR''_lt_C : R'' < C := by linarith
  have hR_lt_R'' : R < R'' := by linarith
  -- Derive `R'' < (1/2) * log(1 + P / N)` (the *original*-P capacity bound)
  -- from `R'' < C = (1/2) * log(1 + P'/N)` via monotonicity in P'≤P.
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := N.coe_nonneg
    exact lt_of_le_of_ne hN_nonneg (fun h => hN h.symm)
  have hR''_lt_PC : R'' < (1 / 2) * Real.log (1 + P / (N : ℝ)) := by
    have h_div_le : P' / (N : ℝ) ≤ P / (N : ℝ) :=
      div_le_div_of_nonneg_right hP'_lt_P (le_of_lt hN_pos)
    have h_arg_le : 1 + P' / (N : ℝ) ≤ 1 + P / (N : ℝ) := by linarith
    have h_arg_pos : 0 < 1 + P' / (N : ℝ) := by
      have : 0 < P' / (N : ℝ) := div_pos hP'_pos hN_pos
      linarith
    have h_log_le : Real.log (1 + P' / (N : ℝ)) ≤ Real.log (1 + P / (N : ℝ)) :=
      Real.log_le_log h_arg_pos h_arg_le
    have h_C_le : C ≤ (1 / 2) * Real.log (1 + P / (N : ℝ)) := by
      show (1 : ℝ) / 2 * Real.log (1 + P' / (N : ℝ))
          ≤ (1 / 2) * Real.log (1 + P / (N : ℝ))
      have h_half_pos : (0 : ℝ) < 1 / 2 := by norm_num
      exact mul_le_mul_of_nonneg_left h_log_le (le_of_lt h_half_pos)
    exact lt_of_lt_of_le hR''_lt_C h_C_le
  -- Extract three N₀ from the destructured sub-bounds.
  -- `h_aep'`, `h_rand'` evaluated at the slack `P'` (capacity `C`);
  -- `h_power'` evaluated at the original `P` capacity (target `n · P`).
  obtain ⟨N_aep,  hN_aep⟩  := h_aep'   hε_rand_pos
  obtain ⟨N_rand, hN_rand⟩ := h_rand'  hε_rand_pos hR''_pos hR''_lt_C
  obtain ⟨N_pow,  hN_pow⟩  := h_power' hε_pow_pos  hR''_pos hR''_lt_PC
  -- `N_doubling`: smallest `n ≥ 1` such that `2 * ⌈exp(nR)⌉ ≤ ⌈exp(n·R'')⌉`.
  -- Existence: `exp(nR'')/exp(nR) = exp(n(R''-R)) → ∞`, so for n large
  -- `exp(n·R'') ≥ 2 * exp(nR) + 2`, which forces the Nat.ceil inequality.
  obtain ⟨N_doubling, hN_doubling⟩ :
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        2 * Nat.ceil (Real.exp ((n : ℝ) * R))
          ≤ Nat.ceil (Real.exp ((n : ℝ) * R'')) := by
    -- Pick `N₀ = ⌈(log 2 + log 4) / (R'' - R)⌉` so that for n ≥ N₀,
    -- `exp(n(R''-R)) ≥ 4`, hence `exp(n R'') ≥ 4 * exp(n R)`. Then
    -- `2 * ⌈exp(n R)⌉ ≤ 2 * (exp(n R) + 1) ≤ 4 * exp(n R) ≤ exp(n R'') ≤ ⌈exp(n R'')⌉`
    -- holds provided `2 * exp(n R) ≥ 2` (i.e., `exp(n R) ≥ 1`, true for n ≥ 0).
    set δ : ℝ := R'' - R with hδ_def
    have hδ_pos : 0 < δ := by linarith
    -- Need `n * δ ≥ log 4`, i.e., `n ≥ log 4 / δ`.
    set N₀ : ℕ := Nat.ceil (Real.log 4 / δ) with hN₀_def
    refine ⟨N₀, fun n hn => ?_⟩
    -- Cast `(N₀ : ℝ) ≤ (n : ℝ)`.
    have h_ndelta : Real.log 4 / δ ≤ (n : ℝ) := by
      have h_cast : ((N₀ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      calc Real.log 4 / δ ≤ (Nat.ceil (Real.log 4 / δ) : ℝ) := Nat.le_ceil _
        _ = (N₀ : ℝ) := by rfl
        _ ≤ (n : ℝ) := h_cast
    have h_exp_n_delta_ge_4 : (4 : ℝ) ≤ Real.exp ((n : ℝ) * δ) := by
      have h_n_delta : Real.log 4 ≤ (n : ℝ) * δ := by
        have := (div_le_iff₀ hδ_pos).mp h_ndelta
        linarith
      have := Real.exp_le_exp.mpr h_n_delta
      rwa [Real.exp_log (by norm_num : (0 : ℝ) < 4)] at this
    have h_exp_R''_ge : Real.exp ((n : ℝ) * R'') = Real.exp ((n : ℝ) * R) * Real.exp ((n : ℝ) * δ) := by
      rw [← Real.exp_add]; congr 1; ring
    have h_exp_R_pos : 0 < Real.exp ((n : ℝ) * R) := Real.exp_pos _
    have h_exp_R_ge_one : 1 ≤ Real.exp ((n : ℝ) * R) := by
      apply Real.one_le_exp; positivity
    -- 2 * ⌈exp(nR)⌉ ≤ 2 * (exp(nR) + 1) ≤ 4 * exp(nR) ≤ exp(nR'') ≤ ⌈exp(nR'')⌉.
    have h_ceil_R_le : (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
        ≤ Real.exp ((n : ℝ) * R) + 1 := by
      exact (Nat.ceil_lt_add_one (le_of_lt h_exp_R_pos)).le
    have h_two_ceil_R_le : (2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
        ≤ 4 * Real.exp ((n : ℝ) * R) := by
      have : (2 : ℝ) * (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
          ≤ 2 * (Real.exp ((n : ℝ) * R) + 1) := by
        linarith
      calc (2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
          = 2 * (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) := by norm_cast
        _ ≤ 2 * (Real.exp ((n : ℝ) * R) + 1) := this
        _ ≤ 2 * Real.exp ((n : ℝ) * R) + 2 * Real.exp ((n : ℝ) * R) := by linarith
        _ = 4 * Real.exp ((n : ℝ) * R) := by ring
    have h_4_le_R'' : (4 : ℝ) * Real.exp ((n : ℝ) * R) ≤ Real.exp ((n : ℝ) * R'') := by
      rw [h_exp_R''_ge]
      have : (4 : ℝ) * Real.exp ((n : ℝ) * R)
          ≤ Real.exp ((n : ℝ) * δ) * Real.exp ((n : ℝ) * R) := by
        nlinarith [h_exp_R_pos]
      linarith [this, mul_comm (Real.exp ((n : ℝ) * R)) (Real.exp ((n : ℝ) * δ))]
    have h_le_R'' : (2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
        ≤ Real.exp ((n : ℝ) * R'') := le_trans h_two_ceil_R_le h_4_le_R''
    -- Conclude via Nat.le_ceil.
    have : (2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
        ≤ (Nat.ceil (Real.exp ((n : ℝ) * R'')) : ℝ) :=
      le_trans h_le_R'' (Nat.le_ceil _)
    exact_mod_cast this
  refine ⟨max N_aep (max N_rand (max N_pow (max N_doubling 1))), ?_⟩
  intro n hn
  have hn_aep  : N_aep  ≤ n := le_trans (le_max_left _ _) hn
  have hn_rand : N_rand ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn_pow  : N_pow  ≤ n :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  have hn_double : N_doubling ≤ n :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)))
  -- Codebook sizes: `M_target = ⌈exp(nR)⌉`, internal `M = ⌈exp(n·R'')⌉`.
  set M_target : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R))   with hM_target_def
  set M        : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R'')) with hM_def
  have hM_target_pos : 0 < M_target :=
    Nat.ceil_pos.mpr (Real.exp_pos _)
  have hM_pos : 0 < M := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hM_ge : 2 * M_target ≤ M := hN_doubling n hn_double
  have hM_ge_two : 2 ≤ M := by have := hM_target_pos; omega
  haveI : NeZero M := ⟨hM_pos.ne'⟩
  haveI : NeZero M_target := ⟨hM_target_pos.ne'⟩
  -- (1) typical set + measurability from AEP at parameters `(P', N, ε_rand, n)`.
  obtain ⟨A, hA_meas, _hA_prob, _hA_vol, _hA_indep⟩ := hN_aep hn_aep
  -- (2) per-m average error bound from h_rand' at rate R'' (size M = ⌈exp(n·R'')⌉),
  --     codebook drawn from the P'-variance Gaussian product.
  have hM_le_ceil_R'' : M ≤ Nat.ceil (Real.exp ((n : ℝ) * R'')) := le_rfl
  have h_per_m : ∀ m : Fin M,
      ∫⁻ codebook : Fin M → Fin n → ℝ,
        ((Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m))
      ∂(gaussianCodebook M n P'.toNNReal)
        ≤ ENNReal.ofReal (2 * ε_rand) := by
    intro m
    exact hN_rand hn_rand hM_pos hM_le_ceil_R'' hA_meas m
  -- (3) power-OK set mass bound from h_power'. Codebook drawn at P', target n · P
  --     (SLLN slack `P − P' > 0` carries the bound).
  have h_power_mass :
      (gaussianCodebook M n P'.toNNReal)
          {c : Fin M → Fin n → ℝ | ∀ m, (∑ i, (c m i)^2) ≤ (n : ℝ) * P}
        ≥ ENNReal.ofReal (1 - ε_pow) :=
    hN_pow hn_pow hM_pos hM_le_ceil_R''
  -- (4) sum-and-barrier integrand. Define
  --   `Pe c m := (Measure.pi (...)) (errorEvent ...)` (ℝ≥0∞-valued)
  --   `g c := ∑_m Pe c m + M · 𝟙_{¬power}(c)`.
  -- Goal: `∫⁻ g ≤ ENNReal.ofReal (M · 2 · ε_d2)`.
  -- ℝ≥0∞ helper bound: `Pe c m ≤ 1` since `Measure.pi` is a probability measure.
  set Pe : (Fin M → Fin n → ℝ) → Fin M → ℝ≥0∞ := fun c m =>
    (Measure.pi (fun i => awgnChannel N h_meas (c m i)))
      ((InformationTheory.Shannon.ChannelCoding.Code.mk
          (M := M) (n := n) (α := ℝ) (β := ℝ)
          c (jointTypicalDecoder A c)).errorEvent m) with hPe_def
  have hPe_le_one : ∀ c m, Pe c m ≤ 1 := by
    intro c m
    haveI : IsMarkovKernel (awgnChannel N h_meas) := awgnChannel.instIsMarkovKernel N h_meas
    haveI : IsProbabilityMeasure
        (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c m i))) := by
      infer_instance
    exact prob_le_one
  -- Power-OK set, its complement, and its measurability. **Note**: the
  -- constraint target is `n · P` (the original power budget), even though the
  -- codebook is drawn from the slack-variance `P'` Gaussian; this asymmetry is
  -- what `IsAwgnPowerConstraintHonest P' P N` encodes.
  set PowSet : Set (Fin M → Fin n → ℝ) :=
    {c : Fin M → Fin n → ℝ | ∀ m, (∑ i, (c m i)^2) ≤ (n : ℝ) * P} with hPowSet_def
  have hPowSet_meas : MeasurableSet PowSet := by
    -- PowSet = ⋂ m, {c | ∑ i, (c m i)^2 ≤ n*P}.
    show MeasurableSet {c : Fin M → Fin n → ℝ | ∀ m, (∑ i, (c m i)^2) ≤ (n : ℝ) * P}
    rw [show {c : Fin M → Fin n → ℝ | ∀ m, (∑ i, (c m i)^2) ≤ (n : ℝ) * P}
          = ⋂ m : Fin M, {c | (∑ i, (c m i)^2) ≤ (n : ℝ) * P} by
        ext c; simp]
    refine MeasurableSet.iInter (fun m => ?_)
    -- Function `c ↦ ∑ i, (c m i)^2` is measurable.
    have h_meas_fun : Measurable
        (fun c : Fin M → Fin n → ℝ => ∑ i, (c m i)^2) := by
      refine Finset.measurable_sum _ (fun i _ => ?_)
      -- c ↦ c m i is the projection (composition of two pi-projections).
      have h_proj : Measurable (fun c : Fin M → Fin n → ℝ => c m i) :=
        (measurable_pi_apply i).comp (measurable_pi_apply m)
      exact h_proj.pow_const 2
    exact h_meas_fun measurableSet_Iic
  have hPowComp_meas : MeasurableSet PowSetᶜ := hPowSet_meas.compl
  -- AEMeasurable Pe c m as a function of c (for `lintegral_finsetSum'`).
  -- Discharged via the three private helpers `jointTypicalDecoder_joint_measurable`
  -- + `awgnCodebookKernel` + `Kernel.measurable_kernel_prodMk_left`.
  have hPe_meas : ∀ m, AEMeasurable (fun c => Pe c m)
      (gaussianCodebook M n P'.toNNReal) := by
    intro m
    refine Measurable.aemeasurable ?_
    -- Joint error-event set: {(c, y) | jointTypicalDecoder A c y ≠ m}.
    set T : Set ((Fin M → Fin n → ℝ) × (Fin n → ℝ)) :=
      {p | jointTypicalDecoder A p.1 p.2 ≠ m} with hT_def
    have hT_meas : MeasurableSet T := by
      -- preimage of the measurable set {m}ᶜ ⊆ Fin M under joint decoder.
      have h_joint := jointTypicalDecoder_joint_measurable
        (n := n) (M := M) A hA_meas
      have h_compl : MeasurableSet ({m}ᶜ : Set (Fin M)) :=
        (MeasurableSet.singleton m).compl
      exact h_joint h_compl
    -- Rewrite Pe via the kernel + prodMk preimage shape required by
    -- `Kernel.measurable_kernel_prodMk_left`.
    have hPe_eq : (fun c : Fin M → Fin n → ℝ => Pe c m)
        = (fun c : Fin M → Fin n → ℝ =>
            awgnCodebookKernel N h_meas m c (Prod.mk c ⁻¹' T)) := by
      funext c
      show Pe c m = awgnCodebookKernel N h_meas m c (Prod.mk c ⁻¹' T)
      -- LHS: `(Measure.pi (...)) (errorEvent c m)`.
      -- RHS: same `Measure.pi`, on `{y | (c, y) ∈ T} = {y | decoder c y ≠ m}`.
      -- Both sides have the same set (errorEvent = preimage of {m}ᶜ under decoder)
      -- and the same measure (kernel toFun = Measure.pi defn).
      simp only [hPe_def]
      -- Same kernel definition; same set up to defeq of errorEvent
      -- vs `Prod.mk c ⁻¹' T`. Both unfold to `{y | decoder c y ≠ m}`.
      rfl
    rw [hPe_eq]
    exact Kernel.measurable_kernel_prodMk_left hT_meas
  -- Sum integrand AE-measurable.
  have hSum_meas : AEMeasurable (fun c => ∑ m, Pe c m)
      (gaussianCodebook M n P'.toNNReal) := by
    have h := Finset.aemeasurable_sum (s := (Finset.univ : Finset (Fin M)))
      (μ := gaussianCodebook M n P'.toNNReal)
      (f := fun m c => Pe c m) (fun m _ => hPe_meas m)
    -- `∑ x ∈ univ, (fun c => Pe c x)` and `fun c => ∑ x, Pe c x` are equal by `Finset.sum_fn`.
    rw [show (fun c => ∑ m, Pe c m) =
          (∑ m ∈ (Finset.univ : Finset (Fin M)), fun c => Pe c m) from
        (Finset.sum_fn _ _).symm]
    exact h
  -- Integral of the sum across `Fin M`.
  have h_int_sum :
      ∫⁻ c, (∑ m, Pe c m) ∂(gaussianCodebook M n P'.toNNReal)
        ≤ (M : ℝ≥0∞) * ENNReal.ofReal (2 * ε_rand) := by
    have h_eq :
        ∫⁻ c, (∑ m, Pe c m) ∂(gaussianCodebook M n P'.toNNReal)
          = ∑ m, ∫⁻ c, Pe c m ∂(gaussianCodebook M n P'.toNNReal) :=
      lintegral_finsetSum' Finset.univ (fun m _ => hPe_meas m)
    rw [h_eq]
    have h_le : ∑ m : Fin M, ∫⁻ c, Pe c m ∂(gaussianCodebook M n P'.toNNReal)
        ≤ ∑ _m : Fin M, ENNReal.ofReal (2 * ε_rand) := by
      apply Finset.sum_le_sum
      intro m _
      exact h_per_m m
    refine h_le.trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    -- M • ENNReal.ofReal _ = (M : ℝ≥0∞) * ENNReal.ofReal _
    rw [nsmul_eq_mul]
  -- Integral of the barrier `M · 𝟙_{¬power}`.
  have h_int_barrier :
      ∫⁻ c, (M : ℝ≥0∞) * (PowSetᶜ).indicator (fun _ => (1 : ℝ≥0∞)) c
        ∂(gaussianCodebook M n P'.toNNReal)
          ≤ (M : ℝ≥0∞) * ENNReal.ofReal ε_pow := by
    -- ∫⁻ M * 𝟙_S = M * ∫⁻ 𝟙_S = M * μ S.
    rw [lintegral_const_mul _ (measurable_const.indicator hPowComp_meas)]
    rw [lintegral_indicator_const hPowComp_meas]
    rw [one_mul]
    gcongr
    -- μ(PowSetᶜ) = 1 - μ(PowSet); μ(PowSet) ≥ 1 - ε_pow ⟹ μ(PowSetᶜ) ≤ ε_pow.
    rw [prob_compl_eq_one_sub hPowSet_meas]
    -- 1 - μ(PowSet) ≤ 1 - (1 - ε_pow) = ε_pow (in ℝ≥0∞ truncated subtraction).
    have h_le_one : (1 : ℝ≥0∞)
        ≤ (gaussianCodebook M n P'.toNNReal) PowSet + ENNReal.ofReal ε_pow := by
      calc (1 : ℝ≥0∞)
          = ENNReal.ofReal (1 - ε_pow) + ENNReal.ofReal ε_pow := by
            rw [← ENNReal.ofReal_add (by linarith) (le_of_lt hε_pow_pos)]
            simp [sub_add_cancel]
        _ ≤ (gaussianCodebook M n P'.toNNReal) PowSet + ENNReal.ofReal ε_pow := by
            gcongr
    exact tsub_le_iff_left.mpr h_le_one
  -- Sum of the two.
  have hsum_total :
      ∫⁻ c, ((∑ m, Pe c m)
        + (M : ℝ≥0∞) * (PowSetᶜ).indicator (fun _ => (1 : ℝ≥0∞)) c)
        ∂(gaussianCodebook M n P'.toNNReal)
          ≤ (M : ℝ≥0∞) * (ENNReal.ofReal (2 * ε_rand) + ENNReal.ofReal ε_pow) := by
    -- Split the integral via `lintegral_add_left'` then sum the two bounds.
    rw [lintegral_add_left' hSum_meas]
    rw [mul_add]
    exact add_le_add h_int_sum h_int_barrier
  -- Bridge: combine to get a bound by ENNReal.ofReal ((M : ℝ) * 2 * ε_d2).
  have hbound_eq :
      (M : ℝ≥0∞) * (ENNReal.ofReal (2 * ε_rand) + ENNReal.ofReal ε_pow)
        = (M : ℝ≥0∞) * ENNReal.ofReal (2 * ε_d2) := by
    congr 1
    rw [← ENNReal.ofReal_add (by positivity) (le_of_lt hε_pow_pos)]
    congr 1
    -- 2 * (ε₁/10) + ε₁/5 = 2 * (ε₁/5)
    show 2 * (ε₁ / 10) + ε₁ / 5 = 2 * (ε₁ / 5)
    ring
  -- (5) D-1: extract a specific codebook with the barrier-augmented bound.
  have hG_aemeas : AEMeasurable
      (fun c => (∑ m, Pe c m)
        + (M : ℝ≥0∞) * (PowSetᶜ).indicator (fun _ => (1 : ℝ≥0∞)) c)
      (gaussianCodebook M n P'.toNNReal) := by
    refine hSum_meas.add ?_
    refine AEMeasurable.const_mul ?_ _
    refine (Measurable.indicator measurable_const hPowComp_meas).aemeasurable
  obtain ⟨c_full, hc_full_bound⟩ :=
    awgn_exists_codebook_le_avg (M := M) (n := n) (σsq := P'.toNNReal)
      (Pe := fun c => (∑ m, Pe c m)
        + (M : ℝ≥0∞) * (PowSetᶜ).indicator (fun _ => (1 : ℝ≥0∞)) c)
      hG_aemeas (B := (M : ℝ≥0∞) * ENNReal.ofReal (2 * ε_d2))
      (hsum_total.trans hbound_eq.le)
  -- (6) c_full is power-OK (contradiction otherwise).
  have hc_full_power : c_full ∈ PowSet := by
    by_contra h_not
    -- If c_full ∉ PowSet, then `indicator = 1` and `g(c_full) ≥ M`.
    have h_indic_one :
        (PowSetᶜ).indicator (fun _ => (1 : ℝ≥0∞)) c_full = 1 := by
      rw [Set.indicator_of_mem h_not]
    -- So `g(c_full) ≥ M`, but `g(c_full) ≤ M · ENNReal.ofReal (2 * ε_d2)`.
    have h_lower : (M : ℝ≥0∞) ≤ (∑ m, Pe c_full m)
        + (M : ℝ≥0∞) * (PowSetᶜ).indicator (fun _ => (1 : ℝ≥0∞)) c_full := by
      rw [h_indic_one, mul_one]
      exact le_add_self
    have h_upper := hc_full_bound
    -- Combine: `M ≤ M · ENNReal.ofReal (2 * ε_d2)`, i.e., `1 ≤ ENNReal.ofReal (2 * ε_d2)`.
    -- But `ENNReal.ofReal (2 * ε_d2) < 1` since `2 * ε_d2 < 1`.
    have h_chain : (M : ℝ≥0∞) ≤ (M : ℝ≥0∞) * ENNReal.ofReal (2 * ε_d2) :=
      h_lower.trans h_upper
    have hM_ne_zero : (M : ℝ≥0∞) ≠ 0 := by
      simp [hM_pos.ne']
    have hM_ne_top : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    -- Divide both sides by M: `1 ≤ ENNReal.ofReal (2 * ε_d2)`.
    have h_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * ε_d2) := by
      have h_cancel : (M : ℝ≥0∞) * ENNReal.ofReal (2 * ε_d2) / (M : ℝ≥0∞)
          = ENNReal.ofReal (2 * ε_d2) := by
        rw [mul_comm, ENNReal.mul_div_cancel_right hM_ne_zero hM_ne_top]
      have := ENNReal.div_le_div_right h_chain (M : ℝ≥0∞)
      rw [ENNReal.div_self hM_ne_zero hM_ne_top, h_cancel] at this
      exact this
    -- Contradict `2 * ε_d2 < 1` (we showed `ε_d2 < 1/2`).
    have h_real_lt : 2 * ε_d2 < 1 := by linarith
    have h_real_nonneg : (0 : ℝ) ≤ 2 * ε_d2 := by positivity
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
        ENNReal.ofReal_le_ofReal_iff h_real_nonneg] at h_one_le
    linarith
  have hc_full_indic_zero :
      (PowSetᶜ).indicator (fun _ => (1 : ℝ≥0∞)) c_full = 0 := by
    rw [Set.indicator_of_notMem]
    exact fun hmem => hmem hc_full_power
  -- So `∑_m Pe c_full m ≤ M · ENNReal.ofReal (2 · ε_d2)` (drop the zero barrier).
  have hc_full_sum :
      (∑ m, Pe c_full m) ≤ (M : ℝ≥0∞) * ENNReal.ofReal (2 * ε_d2) := by
    have := hc_full_bound
    rw [hc_full_indic_zero, mul_zero, add_zero] at this
    exact this
  -- (7) Convert to ℝ-side sum. Each `Pe c_full m ≤ 1` is finite; sum ≠ ⊤.
  set Pe_real : Fin M → ℝ := fun m => (Pe c_full m).toReal with hPe_real_def
  have hPe_real_nn : ∀ m, 0 ≤ Pe_real m := fun m => ENNReal.toReal_nonneg
  have hPe_ne_top : ∀ m, Pe c_full m ≠ ⊤ := fun m =>
    (hPe_le_one c_full m).trans_lt (by norm_num : (1 : ℝ≥0∞) < ⊤) |>.ne
  have hsum_ne_top : (∑ m, Pe c_full m) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    exact fun m _ => hPe_ne_top m
  have h_real_sum :
      (∑ m, Pe_real m) ≤ (M : ℝ) * (2 * ε_d2) := by
    -- ∑ m, (Pe c_full m).toReal = (∑ m, Pe c_full m).toReal (since each is finite).
    have h_toReal_sum : (∑ m, Pe_real m) = (∑ m, Pe c_full m).toReal := by
      show (∑ m, (Pe c_full m).toReal) = (∑ m, Pe c_full m).toReal
      rw [ENNReal.toReal_sum (fun m _ => hPe_ne_top m)]
    rw [h_toReal_sum]
    -- (∑ m, Pe c_full m).toReal ≤ (M * ENNReal.ofReal (2 * ε_d2)).toReal
    --   = M * (2 * ε_d2) (since both finite).
    have h_M_finite_ne : (M : ℝ≥0∞) * ENNReal.ofReal (2 * ε_d2) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top M) ENNReal.ofReal_ne_top
    have h_mono := ENNReal.toReal_mono h_M_finite_ne hc_full_sum
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * ε_d2),
        ENNReal.toReal_natCast] at h_mono
    exact h_mono
  -- (8) D-2: worst-half throw-away ⇒ S ⊆ Fin M with |S| ≥ M/2 and Pe_real ≤ 4ε_d2.
  obtain ⟨S, hS_card, hS_pe⟩ :=
    awgn_expurgate_worst_half (M := M) hM_ge_two Pe_real hPe_real_nn
      hε_d2_pos h_real_sum
  -- (9) Reindex: |S| ≥ M/2 ≥ M_target (since 2 * M_target ≤ M).
  have hM_target_le_half : M_target ≤ M / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by linarith [hM_ge])
  have hM_target_le_S : M_target ≤ S.card := le_trans hM_target_le_half hS_card
  -- Use a *monotonic* reindex `Fin M_target ↪o Fin M` so the sub-decoder's
  -- error event sits inside the full-decoder's error event (smallest-index
  -- tie-break of `jointTypicalDecoder` is preserved by order embeddings).
  set sCard : ℕ := S.card with hsCard_def
  set reindex_emb : Fin M_target ↪o Fin M :=
    (Fin.castLEOrderEmb hM_target_le_S).trans (S.orderEmbOfFin rfl)
      with hreindex_emb_def
  set reindex : Fin M_target → Fin M := fun i => reindex_emb i with hreindex_def
  have hreindex_strictMono : StrictMono reindex :=
    reindex_emb.strictMono
  -- Each `reindex i ∈ S` (image of `orderEmbOfFin S` is `S`).
  have h_reindex_mem : ∀ i : Fin M_target, reindex i ∈ S := by
    intro i
    show (S.orderEmbOfFin rfl) ((Fin.castLEOrderEmb hM_target_le_S) i) ∈ S
    exact Finset.orderEmbOfFin_mem S rfl _
  -- Injectivity (from strict monotonicity).
  have hreindex_inj : Function.Injective reindex := hreindex_strictMono.injective
  set subcodebook : Fin M_target → Fin n → ℝ := fun i => c_full (reindex i)
    with hsubcodebook_def
  -- (10) Power constraint on subcodebook (inherited from c_full ∈ PowSet).
  --      The constraint target `n · P` is the original budget, not `n · P'`.
  have h_sub_power : ∀ j : Fin M_target,
      (∑ i, (subcodebook j i)^2) ≤ (n : ℝ) * P := by
    intro j
    show (∑ i, (c_full (reindex j) i)^2) ≤ (n : ℝ) * P
    exact hc_full_power (reindex j)
  -- (11) Sub-decoder error event ⊆ full-decoder error event at reindex j.
  -- This is the *key inclusion* enabled by `reindex` being strictly monotonic:
  -- - `errorEvent_sub j` triggers on `(subcodebook j, y) ∉ A` OR
  --   `∃ k' < j (Fin M_target), (subcodebook k', y) ∈ A` (after pushing
  --   through the `Fin.find` smallest-index tie-break).
  -- - `errorEvent_full (reindex j)` triggers on `(c_full(reindex j), y) ∉ A` OR
  --   `∃ k < reindex j (Fin M), (c_full k, y) ∈ A`.
  -- Since `subcodebook j = c_full (reindex j)` and (monotonicity) `k' < j ⟹
  -- reindex k' < reindex j`, the first event is exactly the same and the
  -- second sub-event has its witnesses in the full-event's witness set.
  -- (12) Per-message Pe bound for the sub-codebook decoder, by inclusion.
  -- Strategy: `errorEvent_sub j ⊆ errorEvent_full (reindex j)`, hence
  -- `μ_y errorEvent_sub j ≤ μ_y errorEvent_full (reindex j)` (the channel
  -- output measure `μ_y` depends on the transmitted codeword, which is
  -- `subcodebook j = c_full (reindex j)` — same for both sides). The
  -- full-side bound `≤ 4 * ε_d2` comes from D-2 (`hS_pe`) via `Pe_real`.
  have h_sub_pe : ∀ j : Fin M_target,
      ((Measure.pi (fun i => awgnChannel N h_meas (subcodebook j i)))
        ((InformationTheory.Shannon.ChannelCoding.Code.mk
            (M := M_target) (n := n) (α := ℝ) (β := ℝ)
            subcodebook (jointTypicalDecoder A subcodebook)).errorEvent j))
        ≤ ENNReal.ofReal (4 * ε_d2) := by
    intro j
    -- The channel output measure for the j-th sub-message uses `subcodebook j
    -- = c_full (reindex j)`, identical to what the j-th full-message uses.
    set μ_y : Measure (Fin n → ℝ) :=
      Measure.pi (fun i => awgnChannel N h_meas (subcodebook j i)) with hμ_y_def
    -- Step 1: Set-level inclusion `errorEvent_sub j ⊆ errorEvent_full (reindex j)`.
    have h_incl : (InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M_target) (n := n) (α := ℝ) (β := ℝ)
              subcodebook (jointTypicalDecoder A subcodebook)).errorEvent j
        ⊆ (InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              c_full (jointTypicalDecoder A c_full)).errorEvent (reindex j) := by
      intro y hy
      -- `hy : decoder_sub y ≠ j`. Show `decoder_full y ≠ reindex j`.
      simp only [InformationTheory.Shannon.ChannelCoding.Code.mem_errorEvent] at hy ⊢
      -- Goal: decoder_full y ≠ reindex j.
      -- Suppose for contradiction decoder_full y = reindex j.
      intro hfull_eq
      -- decoder_full y = reindex j means:
      --   (c_full(reindex j), y) ∈ A AND ∀ k < reindex j, (c_full k, y) ∉ A
      -- (the no-typical case is decoder = 0; if reindex j = 0 this collapses).
      -- Actually let's use the characterization via Fin.find or by-cases.
      -- decoder_full := if ∃ k, (c_full k, y) ∈ A then Fin.find _ _ else ⟨0, ...⟩.
      have hsub_def : jointTypicalDecoder A subcodebook y ≠ j := hy
      have hfull_def : jointTypicalDecoder A c_full y = reindex j := hfull_eq
      -- Apply the by-cases on existence of typical codewords (for full).
      classical
      by_cases h_exists_full : ∃ k : Fin M, (c_full k, y) ∈ A
      · -- Full has typical; use the existing `hChar` characterization from
        -- `jointTypicalDecoder_measurable`. Specifically, since decoder_full y = reindex j:
        --   (c_full(reindex j), y) ∈ A ∧ ∀ k < reindex j, (c_full k, y) ∉ A
        -- (the m₀ branch can't fire when there's any typical codeword).
        haveI : Decidable (∃ k : Fin M, (c_full k, y) ∈ A) := Classical.propDecidable _
        haveI inst_full : DecidablePred fun k : Fin M => (c_full k, y) ∈ A :=
          fun _ => Classical.propDecidable _
        -- Rewrite decoder unfolding once with the SAME instance.
        change
          (haveI : Decidable (∃ m : Fin M, (c_full m, y) ∈ A) := Classical.propDecidable _;
           haveI : DecidablePred fun m : Fin M => (c_full m, y) ∈ A :=
              fun _ => Classical.propDecidable _;
           if h' : ∃ m : Fin M, (c_full m, y) ∈ A then Fin.find _ h' else _) = reindex j
            at hfull_def
        rw [dif_pos h_exists_full] at hfull_def
        -- Direct extraction via `Fin.find_spec` and `Fin.find_min`. The two
        -- Decidable instances on `(c_full k, y) ∈ A` (the one in `hfull_def`'s
        -- type from the decoder body, and `inst_full`) are Subsingleton-equal,
        -- but Lean does not unify them by `rfl`. We bridge via Subsingleton.elim.
        set inst_dec : DecidablePred fun k : Fin M => (c_full k, y) ∈ A :=
          fun x => Classical.propDecidable ((fun m => (c_full m, y) ∈ A) x) with hinst_dec
        have hfull_def_inst :
            @Fin.find M (fun k => (c_full k, y) ∈ A) inst_full h_exists_full = reindex j := by
          have h_inst_eq : inst_full = inst_dec := Subsingleton.elim _ _
          rw [h_inst_eq]; exact hfull_def
        have hfull_typ : (c_full (reindex j), y) ∈ A := by
          have h_spec := @Fin.find_spec M (fun k => (c_full k, y) ∈ A) inst_full h_exists_full
          rw [hfull_def_inst] at h_spec
          exact h_spec
        have hfull_min : ∀ k : Fin M, k < reindex j → (c_full k, y) ∉ A := by
          intro k hk
          have h_min := @Fin.find_min M (fun k => (c_full k, y) ∈ A) inst_full h_exists_full k
          have hsub : k < @Fin.find M (fun k => (c_full k, y) ∈ A) inst_full h_exists_full := by
            rw [hfull_def_inst]; exact hk
          exact h_min hsub
        -- hfull_typ : (c_full(reindex j), y) ∈ A
        -- hfull_min : ∀ k < reindex j, (c_full k, y) ∉ A
        -- In particular: (subcodebook j, y) = (c_full (reindex j), y) ∈ A.
        have hsub_typ : (subcodebook j, y) ∈ A := hfull_typ
        -- For ALL k' < j (Fin M_target), (subcodebook k', y) ∉ A
        -- because reindex k' < reindex j by monotonicity, so by hfull_min.
        have hsub_min : ∀ k' : Fin M_target, k' < j → (subcodebook k', y) ∉ A := by
          intro k' hk'
          have hreindex_lt : reindex k' < reindex j := hreindex_strictMono hk'
          exact hfull_min (reindex k') hreindex_lt
        -- So sub-decoder finds the smallest sub-typical index = j.
        have h_exists_sub : ∃ k : Fin M_target, (subcodebook k, y) ∈ A :=
          ⟨j, hsub_typ⟩
        have : jointTypicalDecoder A subcodebook y = j := by
          unfold jointTypicalDecoder
          rw [dif_pos h_exists_sub]
          -- Build the goal with the SAME decidability instance from the decoder body.
          set inst_sub_dec : DecidablePred fun k : Fin M_target => (subcodebook k, y) ∈ A :=
            fun x => Classical.propDecidable ((fun m => (subcodebook m, y) ∈ A) x)
          haveI inst_sub : DecidablePred fun k : Fin M_target => (subcodebook k, y) ∈ A :=
            inferInstance
          have h_inst_eq : inst_sub = inst_sub_dec := Subsingleton.elim _ _
          show @Fin.find M_target (fun k => (subcodebook k, y) ∈ A) inst_sub_dec
              h_exists_sub = j
          rw [← h_inst_eq]
          exact (Fin.find_eq_iff (i := j) h_exists_sub).mpr ⟨hsub_typ, hsub_min⟩
        exact hsub_def this
      · -- Full has no typical; decoder_full = ⟨0, ...⟩ = 0 ∈ Fin M.
        unfold jointTypicalDecoder at hfull_def
        rw [dif_neg h_exists_full] at hfull_def
        -- hfull_def : (⟨0, ...⟩ : Fin M) = reindex j
        -- So reindex j = 0 in Fin M (as a value).
        have hreindex_zero : (reindex j : ℕ) = 0 := by
          have : (reindex j : ℕ) = ((⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩ : Fin M) : ℕ) := by
            rw [← hfull_def]
          simpa using this
        -- Sub-decoder: no sub-codeword can be typical, since each sub-codeword
        -- equals c_full(reindex k') and h_exists_full says no c_full ℓ is typical.
        have h_no_sub_typ : ¬ ∃ k : Fin M_target, (subcodebook k, y) ∈ A := by
          rintro ⟨k, hk⟩
          exact h_exists_full ⟨reindex k, hk⟩
        have h_decoder_sub_zero : jointTypicalDecoder A subcodebook y
            = ⟨0, Nat.pos_of_ne_zero (NeZero.ne M_target)⟩ := by
          unfold jointTypicalDecoder
          rw [dif_neg h_no_sub_typ]
        -- For sub-decoder to satisfy `decoder_sub y ≠ j` (hsub_def), j ≠ 0.
        have hj_ne_zero_sub : (j : ℕ) ≠ 0 := by
          intro hj0
          apply hsub_def
          rw [h_decoder_sub_zero]
          exact Fin.ext hj0.symm
        -- From `reindex j = 0` in Fin M and `j ≠ 0` in Fin M_target, we'd need
        -- reindex(j > 0) = 0. By monotonicity reindex(0) < reindex(j), so
        -- reindex(0) < 0 in Fin M which is impossible.
        have hj_pos : (0 : Fin M_target) < j := by
          rw [Fin.pos_iff_ne_zero]
          intro heq
          exact hj_ne_zero_sub (by simp [heq])
        have h_reindex_zero_lt : reindex 0 < reindex j := hreindex_strictMono hj_pos
        have : (reindex 0 : ℕ) < (reindex j : ℕ) := h_reindex_zero_lt
        rw [hreindex_zero] at this
        exact Nat.not_lt_zero _ this
    -- Step 2: Monotonicity of `μ_y` gives the measure inclusion.
    have h_meas_le := μ_y.mono h_incl
    -- Step 3: The full-side bound from D-2 (`hS_pe` on `reindex j ∈ S`).
    -- subcodebook j = c_full (reindex j), so `μ_y = Measure.pi (W ∘ c_full(reindex j))`.
    -- The full-error measure under this `μ_y` is exactly `Pe c_full (reindex j)`.
    have h_full_eq :
        μ_y ((InformationTheory.Shannon.ChannelCoding.Code.mk
                (M := M) (n := n) (α := ℝ) (β := ℝ)
                c_full (jointTypicalDecoder A c_full)).errorEvent (reindex j))
          = Pe c_full (reindex j) := rfl
    -- Refold μ_y.measureOf into μ_y application to match `h_full_eq` shape.
    change μ_y _ ≤ μ_y _ at h_meas_le
    rw [h_full_eq] at h_meas_le
    -- (Pe c_full (reindex j)).toReal = Pe_real (reindex j) ≤ 4 * ε_d2 from `hS_pe`.
    have h_real_bound : (Pe c_full (reindex j)).toReal ≤ 4 * ε_d2 :=
      hS_pe (reindex j) (h_reindex_mem j)
    -- Pe c_full (reindex j) ≤ ENNReal.ofReal (4 * ε_d2).
    have h_ennreal_bound : Pe c_full (reindex j) ≤ ENNReal.ofReal (4 * ε_d2) := by
      have h_ne_top : Pe c_full (reindex j) ≠ ⊤ := hPe_ne_top (reindex j)
      rw [← ENNReal.ofReal_toReal h_ne_top]
      exact ENNReal.ofReal_le_ofReal h_real_bound
    exact h_meas_le.trans h_ennreal_bound
  -- (13) D-3: bridge to AwgnCode with the 5ε_d2 = ε₁ ≤ ε bound.
  --      Constraint target is the original `n · P`, so `AwgnCode M_target n P`.
  obtain ⟨awgnCode, h_awgnCode_pe⟩ :=
    awgn_extract_AwgnCode (P := P) (N := N) h_meas (n := n) (M := M_target)
      (ε := ε_d2) hε_d2_pos (A := A) hA_meas subcodebook h_sub_pe h_sub_power
  refine ⟨M_target, le_rfl, awgnCode, ?_⟩
  intro m
  have h_awg := h_awgnCode_pe m
  -- `5 * ε_d2 = ε₁ ≤ ε`.
  have h5 : 5 * ε_d2 = ε₁ := by
    show 5 * (ε₁ / 5) = ε₁; ring
  linarith [h_awg, hε₁_le_ε]

/-- **`awgn_achievability` F-1 wrapper** — `isAwgnTypicalityHypothesis`
(580-line genuine assembly) を直接呼出す F-1 discharge wrapper (Phase E-2 /
2026-05-27 F-1/F-3 peer migration / 2026-05-28 AWGN M5 Phase 3-β: bundle hyp
`IsAwgnRandomCodingFeasible` が削除され、`isAwgnTypicalityHypothesis` が
shared sorry 補題 (`AwgnWalls.lean`) + `awgnPowerWitness_exists` を内部で
呼ぶ形になったため、本 wrapper の `h_feasible` 引数も消失)。

**Residual status (AWGN M5 Phase 3-β)**: this wrapper no longer carries a
bundled feasibility hypothesis. The achievability residuals now live as
`sorry` + `@residual(wall:awgn-*)` in the 3 shared walls of `AwgnWalls.lean`
(continuous AEP / random-coding bound / power-constraint honest) plus the
`awgnPowerWitness_exists` helper. The wrapper itself contains no residual.

**Naming (historical artefact)**: theorem name is `_via_staged_hyps` (plural
artefact of the pre-pivot 3-hyp form); the staged content is now in the walls.

`@audit:ok` -/
@[entry_point]
theorem awgn_achievability_F1_via_staged_hyps
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε :=
  isAwgnTypicalityHypothesis P hP N hN h_meas hR_pos hR hε

/-- **Main theorem F-4 discharged, F-1 wrapper** —
`awgn_channel_coding_theorem` の `h_meas` (F-4 / `isAwgnChannelMeasurable`) を
**genuinely 埋め**、F-1 achievability を `isAwgnTypicalityHypothesis` (580-line
genuine assembly) 経由で再 publish (Phase 2 pivot 2026-05-24 / 2026-05-27
F-1/F-3 peer migration / 2026-05-28 AWGN M5 Phase 3-β: bundle hyp
`IsAwgnRandomCodingFeasible` 削除に伴い `h_feasible` 引数が消失、achievability
residual は `AwgnWalls.lean` の 3 shared sorry 補題 +
`awgnPowerWitness_exists` に移動)。

**残 hyp** (docstring に明示、CORE doctrine 透明性):
- `h_mi_bridge` (F-2、mutual info bridge、未起草 plan) — 本 wrapper body では
  未使用だが、`awgn_channel_coding_theorem` の F-2 wiring 整合のため signature
  に残置 (`set_option linter.unusedVariables false`)。

F-3 converse は `awgn_converse` 内の `sorry + @residual(plan:awgn-converse-aux-plan)`
に defer。本 wrapper の signature には現れないが、`awgn_channel_coding_theorem`
は achievability half のみを述べるため converse 側は別経路 (`awgn_converse`) で
独立に publish される構造に変更なし。

**Naming (historical artefact)**: theorem name is
`awgn_theorem_F4_discharged_F1_via_staged`. F-4 genuinely discharged
(`isAwgnChannelMeasurable N` is concrete); the F-1 staged content now lives in
the `AwgnWalls.lean` walls rather than a bundle hyp on this wrapper.

`@audit:ok` -/
@[entry_point]
theorem awgn_theorem_F4_discharged_F1_via_staged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_mi_bridge :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal)
            (awgnChannel N (isAwgnChannelMeasurable N))).toReal
          = InformationTheory.Shannon.differentialEntropy
              (gaussianReal 0 (P.toNNReal + N))
            - InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N))
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt
                  (awgnChannel N (isAwgnChannelMeasurable N)) m).toReal < ε :=
  isAwgnTypicalityHypothesis P hP N hN (isAwgnChannelMeasurable N)
    hR_pos hR_lt_C hε

end InformationTheory.Shannon.AWGN

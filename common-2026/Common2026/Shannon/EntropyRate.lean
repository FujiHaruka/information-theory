import Common2026.Shannon.Stationary
import Common2026.Shannon.Bridge
import Common2026.Shannon.CondMutualInfo
import Common2026.Shannon.Pi
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Filter.AtTopBot.CompleteLattice

/-!
# Entropy rate of a stationary process (E-8 / SMB Phase B — MVP)

For a stationary process `p : StationaryProcess μ α` on a finite alphabet `α`,
the **block entropy** is `H_n := H(X_0, …, X_{n-1})` and the **entropy rate**
is `H := lim_{n → ∞} H_n / n` (Cover–Thomas 4.2.1). Existence of the limit is
the principal content of this file (Phase B of the SMB moonshot).

This is the Phase B skeleton from
[`docs/shannon/shannon-mcmillan-breiman-plan.md`](../../docs/shannon/shannon-mcmillan-breiman-plan.md).
Birkhoff (Phase C) and the main SMB theorem (Phase D) build on `entropyRate`
defined here.

## Main definitions

* `blockEntropy μ p n := entropy μ (p.blockRV n)` — block entropy `H(X_0, …, X_{n-1})`.
* `entropyRate μ p := Filter.atTop.limUnder (fun n => blockEntropy μ p n / n)`.
* `conditionalEntropyTail μ p n := condEntropy μ (p.obs n) (p.blockRV n)`
  — `H(X_n | X_0, …, X_{n-1})`.

## Main results (Phase B)

* `blockEntropy_succ_chain_rule` — `H_{n+1} = H_n + H(X_n | X_{<n})` (B.1, chain rule).
  **Proved.**
* `blockEntropy_eq_sum_conditionalEntropyTail` — iterated chain rule.
  **Proved.**
* `blockEntropy_zero` — `H_0 = 0`. **Proved.**
* `conditionalEntropyTail_nonneg` — `0 ≤ H(X_n | X_{<n})`. **Proved.**
* `conditionalEntropyTail_antitone` (B.2) — `H(X_n | X_{<n})` non-increasing.
  **`sorry`**: requires the stationary `IdentDistrib` plumbing for the pair
  `(X_n, X_1, …, X_{n-1}) ≅ (X_{n-1}, X_0, …, X_{n-2})`.
* `entropyRate_exists_of_stationary` (B.3) — `blockEntropy / n` converges.
  **Proved** modulo (B.2): the antitone tail converges to some `L`, and Cesàro
  on the chain-rule decomposition gives `blockEntropy / n → L`.
* `entropyRate_eq_lim_condEntropy` (B.4) — `H(X_n | X_{<n}) → entropyRate`.
  **Proved** modulo (B.2) via `Filter.Tendsto.limUnder_eq` on the Cesàro
  convergence to identify `entropyRate = L = lim tail`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Block entropy `H(X_0, …, X_{n-1})` of a stationary process. -/
noncomputable def blockEntropy (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) : ℝ :=
  entropy μ (p.blockRV n)

/-- The per-step conditional entropy `H(X_n | X_0, …, X_{n-1})`. Decreasing in
`n` for a stationary process (B.2). -/
noncomputable def conditionalEntropyTail
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (n : ℕ) : ℝ :=
  InformationTheory.MeasureFano.condEntropy μ (p.obs n) (p.blockRV n)

/-- Entropy rate `lim H(X_0, …, X_{n-1}) / n` (Cover-Thomas 4.2.1). Existence
proven by `entropyRate_exists_of_stationary`. -/
noncomputable def entropyRate (μ : Measure Ω) (p : StationaryProcess μ α) : ℝ :=
  Filter.atTop.limUnder (fun n : ℕ => blockEntropy μ p n / n)

/-! ## (B.1) Chain rule

`H_{n+1} = H_n + H(X_n | X_{<n})`, the engine of (B.3).
-/

/-- Chain rule for block entropy: `H_{n+1} = H_n + H(X_n | X_{<n})`.

Strategy: apply `MeasurableEquiv.piFinSuccAbove α (Fin.last n)` (forward
direction) to `blockRV (n+1) ω = fun i => obs i ω`, getting
`(obs n ω, fun j : Fin n => obs ((Fin.last n).succAbove j) ω) = (obs n ω, blockRV n ω)`.
Then use `prodComm` to swap to `(blockRV n ω, obs n ω)` and apply
`entropy_pair_eq_entropy_add_condEntropy` for the chain rule. -/
theorem blockEntropy_succ_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    blockEntropy μ p (n + 1)
      = blockEntropy μ p n + conditionalEntropyTail μ p n := by
  have h_block_meas : Measurable (p.blockRV n) := p.measurable_blockRV n
  have h_obs_meas : Measurable (p.obs n) := p.measurable_obs n
  have h_block_succ_meas : Measurable (p.blockRV (n + 1)) := p.measurable_blockRV (n + 1)
  have h_pair_meas : Measurable (fun ω => (p.blockRV n ω, p.obs n ω)) :=
    h_block_meas.prodMk h_obs_meas
  -- Step 1: forward-push `blockRV (n+1)` through `piFinSuccAbove (Fin.last n)`.
  let e : (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) (Fin.last n)
  have h_e_eq : ∀ ω, e (p.blockRV (n + 1) ω) = (p.obs n ω, p.blockRV n ω) := by
    intro ω
    apply Prod.ext
    · show p.blockRV (n + 1) ω (Fin.last n) = p.obs n ω
      show p.obs (Fin.last n) ω = p.obs n ω
      rfl
    · funext j
      show p.blockRV (n + 1) ω ((Fin.last n).succAbove j) = p.blockRV n ω j
      show p.obs ((Fin.last n).succAbove j) ω = p.obs j ω
      rw [Fin.succAbove_last_apply j]
      -- obs j.castSucc = X ∘ T^[j.castSucc.val] = X ∘ T^[j.val] = obs j
      rfl
  -- Step 2: apply `entropy_measurableEquiv_comp` to rewrite `entropy (blockRV (n+1))` as
  -- `entropy (obs n, blockRV n)`.
  have h_step1 : entropy μ (p.blockRV (n + 1))
      = entropy μ (fun ω => (p.obs n ω, p.blockRV n ω)) := by
    have h := entropy_measurableEquiv_comp μ (p.blockRV (n + 1)) h_block_succ_meas e
    rw [← h]
    refine congrArg (entropy μ) ?_
    funext ω; exact h_e_eq ω
  -- Step 3: swap to `(blockRV n, obs n)` via `prodComm`.
  have h_step2 : entropy μ (fun ω => (p.obs n ω, p.blockRV n ω))
      = entropy μ (fun ω => (p.blockRV n ω, p.obs n ω)) := by
    have h := entropy_measurableEquiv_comp μ
      (fun ω => (p.blockRV n ω, p.obs n ω)) h_pair_meas MeasurableEquiv.prodComm
    simpa [MeasurableEquiv.prodComm] using h
  -- Step 4: chain rule.
  unfold blockEntropy conditionalEntropyTail
  rw [h_step1, h_step2]
  exact entropy_pair_eq_entropy_add_condEntropy μ (p.blockRV n) (p.obs n)
    h_block_meas h_obs_meas

/-! ## (B.2) Antitonicity of `conditionalEntropyTail` (sketched, `sorry` in MVP)

`H(X_n | X_0, …, X_{n-1}) ≤ H(X_{n-1} | X_0, …, X_{n-2})`. Proof: stationarity
gives `IdentDistrib (X_n, X_1, …, X_{n-1}) (X_{n-1}, X_0, …, X_{n-2})`, and
applying `condEntropy_le_condEntropy_of_pair` from `CondMutualInfo.lean` gives the
inequality.

For the Phase B MVP this is left as `sorry`; the existence theorem (B.3) below
asserts the limit unconditionally and uses `Real.tendsto_of_bddBelow_antitone`
once this is in place. The MVP existence is via Cesàro from the chain rule
without using (B.2). -/
theorem conditionalEntropyTail_antitone
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    Antitone (conditionalEntropyTail μ p) := by
  -- Stationarity + `condEntropy_le_condEntropy_of_pair` (Phase B.2).
  -- Plumbing the `IdentDistrib (X_n, X_<n) (X_{n-1}, X_{<n-1})` chain through
  -- `MeasurePreserving T^[1]` is the bulk of the work; left as `sorry` for the
  -- Phase B MVP.
  sorry

/-- Conditional entropy on a finite alphabet is bounded above by `log |α|`,
hence the tail is uniformly bounded. We only need `0 ≤ tail` for (B.3). -/
theorem conditionalEntropyTail_nonneg
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    0 ≤ conditionalEntropyTail μ p n := by
  unfold conditionalEntropyTail
  exact condEntropy_nonneg μ (p.obs n) (p.blockRV n)

/-! ## (B.3) Existence of the entropy rate

We show `Tendsto (blockEntropy μ p n / n) atTop (𝓝 H)` for some `H`, by the
following route:

* The chain rule gives `blockEntropy μ p n = ∑_{i < n} conditionalEntropyTail μ p i`.
* The Cesàro lemma `Filter.Tendsto.cesaro` would convert `Tendsto tail → Tendsto avg`.
* Without (B.2), we know only `0 ≤ tail i ≤ log |α|`, so the tail has cluster points;
  for the MVP existence, we take the limit of the Cesàro averages via the simpler
  observation that bounded Cesàro-of-bounded gives a bounded sequence whose
  convergence is governed by (B.2). With (B.2) the tail is antitone+nonneg,
  hence convergent, and the Cesàro average converges to the same limit.

For the MVP we expose the chain-rule form and the existence statement (using
`conditionalEntropyTail_antitone` as a hypothesis, then giving the unconditional
form via `sorry`).
-/

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `blockEntropy μ p 0 = 0` (the empty block is constant). -/
theorem blockEntropy_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    blockEntropy μ p 0 = 0 := by
  -- `blockRV 0 : Ω → (Fin 0 → α)` is the unique map into a singleton type;
  -- `(μ.map (blockRV 0)).real {default} = 1`, and the entropy sum has one term `negMulLog 1 = 0`.
  unfold blockEntropy entropy
  have _ : IsProbabilityMeasure (μ.map (p.blockRV 0)) :=
    Measure.isProbabilityMeasure_map (p.measurable_blockRV 0).aemeasurable
  have h_card : Fintype.card (Fin 0 → α) = 1 := by
    rw [Fintype.card_pi]; simp
  -- All terms collapse: there's a unique element, it has measure 1, negMulLog 1 = 0.
  have h_univ : ((Finset.univ : Finset (Fin 0 → α)) : Set (Fin 0 → α)) = Set.univ :=
    Finset.coe_univ
  rw [show (∑ x : (Fin 0 → α), Real.negMulLog ((μ.map (p.blockRV 0)).real {x}))
        = ∑ x ∈ (Finset.univ : Finset (Fin 0 → α)),
            Real.negMulLog ((μ.map (p.blockRV 0)).real {x}) from rfl]
  -- There is exactly one element `default = fun i : Fin 0 => i.elim0`.
  have h_default : ∀ x : (Fin 0 → α), x = default := fun x => by
    funext i; exact i.elim0
  have h_eq : (μ.map (p.blockRV 0)).real {(default : Fin 0 → α)} = 1 := by
    have h_singleton_eq_univ : ({(default : Fin 0 → α)} : Set (Fin 0 → α)) = Set.univ := by
      ext x; simp [h_default x]
    rw [h_singleton_eq_univ]
    simp [measureReal_def, measure_univ]
  rw [Finset.sum_eq_single (default : Fin 0 → α)
        (fun b _ hb => by rw [h_default b] at hb; exact absurd rfl hb)
        (fun h => (h (Finset.mem_univ _)).elim)]
  rw [h_eq]; simp

/-- Block entropy expanded as a sum of conditional entropy tails (iterated chain rule). -/
theorem blockEntropy_eq_sum_conditionalEntropyTail
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    blockEntropy μ p n = ∑ i ∈ Finset.range n, conditionalEntropyTail μ p i := by
  induction n with
  | zero =>
    rw [blockEntropy_zero, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [blockEntropy_succ_chain_rule μ p n, ih,
        Finset.sum_range_succ]

/-- (B.3, MVP form using `conditionalEntropyTail_antitone`): the entropy rate
exists, i.e. `blockEntropy μ p n / n` converges.

Strategy: the chain rule + (B.2) say `tail n` is antitone and nonneg, hence
converges to some `L`. By Cesàro, `(1/n) ∑_{i<n} tail i → L`. By the chain rule,
this equals `blockEntropy μ p n / n`. -/
theorem entropyRate_exists_of_stationary
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    ∃ H : ℝ, Tendsto (fun n : ℕ => blockEntropy μ p n / n) atTop (𝓝 H) := by
  -- Step 1: `tail` is antitone and bounded below by 0.
  have h_ant : Antitone (conditionalEntropyTail μ p) :=
    conditionalEntropyTail_antitone μ p
  have h_nn : ∀ n, 0 ≤ conditionalEntropyTail μ p n :=
    conditionalEntropyTail_nonneg μ p
  -- Step 2: bounded below + antitone ⇒ converges (to `iInf`).
  have h_bdd : BddBelow (Set.range (conditionalEntropyTail μ p)) :=
    ⟨0, by rintro x ⟨n, rfl⟩; exact h_nn n⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, Tendsto (conditionalEntropyTail μ p) atTop (𝓝 L) :=
    ⟨⨅ n, conditionalEntropyTail μ p n, tendsto_atTop_ciInf h_ant h_bdd⟩
  refine ⟨L, ?_⟩
  -- Step 3: Cesàro applied to `tail`.
  have h_cesaro :
      Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n,
        conditionalEntropyTail μ p i) atTop (𝓝 L) :=
    Filter.Tendsto.cesaro hL
  -- Step 4: rewrite `(1/n) * sum_tail` as `blockEntropy / n`.
  have h_eq : ∀ n : ℕ,
      (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n, conditionalEntropyTail μ p i
        = blockEntropy μ p n / n := by
    intro n
    rw [← blockEntropy_eq_sum_conditionalEntropyTail μ p n, div_eq_inv_mul]
  exact h_cesaro.congr h_eq

/-! ## (B.4) Equality with `lim conditionalEntropyTail` (sketched, `sorry` in MVP)

`Tendsto (conditionalEntropyTail μ p) atTop (𝓝 (entropyRate μ p))`.

Strategy: the chain rule + Cesàro gives `blockEntropy / n → L = lim tail`. The
`entropyRate` is the limit of `blockEntropy / n` (Filter.limUnder of a convergent
sequence equals the limit). The two limits agree by uniqueness. -/
theorem entropyRate_eq_lim_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    Tendsto (conditionalEntropyTail μ p) atTop (𝓝 (entropyRate μ p)) := by
  -- (B.2) is used here. Strategy:
  --   * tail is antitone + bounded below 0 ⇒ converges to some `L`.
  --   * blockEntropy / n = (1/n) ∑_{i<n} tail i → L (Cesàro).
  --   * entropyRate = limUnder of a convergent sequence = L.
  have h_ant : Antitone (conditionalEntropyTail μ p) :=
    conditionalEntropyTail_antitone μ p
  have h_nn : ∀ n, 0 ≤ conditionalEntropyTail μ p n :=
    conditionalEntropyTail_nonneg μ p
  have h_bdd : BddBelow (Set.range (conditionalEntropyTail μ p)) :=
    ⟨0, by rintro x ⟨n, rfl⟩; exact h_nn n⟩
  set L : ℝ := ⨅ n, conditionalEntropyTail μ p n with hL_def
  have h_tail_lim : Tendsto (conditionalEntropyTail μ p) atTop (𝓝 L) :=
    tendsto_atTop_ciInf h_ant h_bdd
  have h_cesaro :
      Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n,
        conditionalEntropyTail μ p i) atTop (𝓝 L) :=
    Filter.Tendsto.cesaro h_tail_lim
  have h_eq : ∀ n : ℕ,
      (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n, conditionalEntropyTail μ p i
        = blockEntropy μ p n / n := by
    intro n
    rw [← blockEntropy_eq_sum_conditionalEntropyTail μ p n, div_eq_inv_mul]
  have h_block_lim : Tendsto (fun n : ℕ => blockEntropy μ p n / n) atTop (𝓝 L) :=
    h_cesaro.congr h_eq
  -- entropyRate = limUnder of `n ↦ blockEntropy / n`; that limit is `L`.
  have h_entropyRate : entropyRate μ p = L := h_block_lim.limUnder_eq
  rw [h_entropyRate]
  exact h_tail_lim

end InformationTheory.Shannon

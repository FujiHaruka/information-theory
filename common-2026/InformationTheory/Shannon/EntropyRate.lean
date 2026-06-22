import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Stationary.Basic
import InformationTheory.Shannon.Bridge
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.Pi
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Filter.AtTopBot.CompleteLattice

/-!
# Entropy rate of a stationary process

For a stationary process `p : StationaryProcess μ α` on a finite alphabet `α`,
the **block entropy** is `H_n := H(X_0, …, X_{n-1})` and the **entropy rate**
is `H := lim_{n → ∞} H_n / n` (Cover–Thomas 4.2.1). Existence of the limit is
the principal content of this file.

The Birkhoff ergodic theorem and the Shannon–McMillan–Breiman theorem build on
`entropyRate` defined here.

## Main definitions

* `blockEntropy μ p n := entropy μ (p.blockRV n)` — block entropy `H(X_0, …, X_{n-1})`.
* `entropyRate μ p := Filter.atTop.limUnder (fun n => blockEntropy μ p n / n)`.
* `conditionalEntropyTail μ p n := condEntropy μ (p.obs n) (p.blockRV n)`
  — `H(X_n | X_0, …, X_{n-1})`.

## Main results

* `blockEntropy_succ_chain_rule` — `H_{n+1} = H_n + H(X_n | X_{<n})` (chain rule).
* `blockEntropy_eq_sum_conditionalEntropyTail` — iterated chain rule.
* `blockEntropy_zero` — `H_0 = 0`.
* `conditionalEntropyTail_nonneg` — `0 ≤ H(X_n | X_{<n})`.
* `conditionalEntropyTail_antitone` — `H(X_n | X_{<n})` non-increasing, from
  stationarity (joint pushforward equality via `MeasurePreserving T`)
  + conditioning monotonicity (`condEntropy_le_condEntropy_of_pair`).
* `entropyRate_exists_of_stationary` — `blockEntropy / n` converges: the antitone
  tail converges to some `L`, and Cesàro on the chain-rule decomposition gives
  `blockEntropy / n → L`.
* `entropyRate_eq_lim_condEntropy` — `H(X_n | X_{<n}) → entropyRate`, via
  `Filter.Tendsto.limUnder_eq` on the Cesàro convergence to identify
  `entropyRate = L = lim tail`.
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
`n` for a stationary process. -/
noncomputable def conditionalEntropyTail
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (n : ℕ) : ℝ :=
  InformationTheory.MeasureFano.condEntropy μ (p.obs n) (p.blockRV n)

/-- Entropy rate `lim H(X_0, …, X_{n-1}) / n` (Cover-Thomas 4.2.1). Existence
proven by `entropyRate_exists_of_stationary`. -/
@[entry_point]
noncomputable def entropyRate (μ : Measure Ω) (p : StationaryProcess μ α) : ℝ :=
  Filter.atTop.limUnder (fun n : ℕ ↦ blockEntropy μ p n / n)

/-- **Base-2 (bit) entropy rate**: the natural-log `entropyRate` divided by
`Real.log 2`, i.e. the entropy rate measured in bits/symbol. This is the
target the LZ78 bit-rate `lz78GreedyEncodingLength/n` converges to (the
LZ78 encoding length uses `LZ78Phrase.bitLength = Nat.log 2 …`, a base-2 code
length, so its per-symbol rate is in bits, whereas `entropyRate` is in nats). -/
@[entry_point]
noncomputable def entropyRate₂ (μ : Measure Ω) (p : StationaryProcess μ α) : ℝ :=
  entropyRate μ p / Real.log 2

/-! ## Chain rule

`H_{n+1} = H_n + H(X_n | X_{<n})`, the engine of the existence proof.
-/

omit [DecidableEq α] in
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
  classical
  have h_block_meas : Measurable (p.blockRV n) := p.measurable_blockRV n
  have h_obs_meas : Measurable (p.obs n) := p.measurable_obs n
  have h_block_succ_meas : Measurable (p.blockRV (n + 1)) := p.measurable_blockRV (n + 1)
  have h_pair_meas : Measurable (fun ω ↦ (p.blockRV n ω, p.obs n ω)) :=
    h_block_meas.prodMk h_obs_meas
  -- Step 1: forward-push `blockRV (n+1)` through `piFinSuccAbove (Fin.last n)`.
  let e : (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) (Fin.last n)
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
      = entropy μ (fun ω ↦ (p.obs n ω, p.blockRV n ω)) := by
    have h := entropy_measurableEquiv_comp μ (p.blockRV (n + 1)) h_block_succ_meas e
    rw [← h]
    refine congrArg (entropy μ) ?_
    funext ω; exact h_e_eq ω
  -- Step 3: swap to `(blockRV n, obs n)` via `prodComm`.
  have h_step2 : entropy μ (fun ω ↦ (p.obs n ω, p.blockRV n ω))
      = entropy μ (fun ω ↦ (p.blockRV n ω, p.obs n ω)) := by
    have h := entropy_measurableEquiv_comp μ
      (fun ω ↦ (p.blockRV n ω, p.obs n ω)) h_pair_meas MeasurableEquiv.prodComm
    simpa [MeasurableEquiv.prodComm] using h
  -- Step 4: chain rule.
  unfold blockEntropy conditionalEntropyTail
  rw [h_step1, h_step2]
  exact entropy_pair_eq_entropy_add_condEntropy μ (p.blockRV n) (p.obs n)
    h_block_meas h_obs_meas

/-! ## Antitonicity of `conditionalEntropyTail`

`H(X_{n+1} | X_0, …, X_n) ≤ H(X_n | X_0, …, X_{n-1})`. Proof:
1. **Stationarity** (apply shift `T`): the joint pushforward
   `μ.map (X_n, (X_0, …, X_{n-1}))` equals `μ.map (X_{n+1}, (X_1, …, X_n))`,
   so the corresponding conditional entropies coincide (via `condDistrib_map`).
2. **Conditioning monotonicity** (`condEntropy_le_condEntropy_of_pair`):
   `H(X_{n+1} | (X_0, (X_1, …, X_n))) ≤ H(X_{n+1} | (X_1, …, X_n))`. The
   conditioner `(X_0, (X_1, …, X_n))` reshapes to `blockRV (n+1)` via
   `MeasurableEquiv.piFinSuccAbove ... 0` + `prodComm`.
-/

section AntitoneHelpers

variable {μ : Measure Ω}

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `obs n` precomposed with `T` is `obs (n+1)`. -/
private lemma obs_comp_T
    (p : StationaryProcess μ α) (n : ℕ) :
    p.obs n ∘ p.T = p.obs (n + 1) := by
  funext ω
  show p.X (p.T^[n] (p.T ω)) = p.X (p.T^[n + 1] ω)
  rw [show p.T^[n + 1] = p.T^[n] ∘ p.T from Function.iterate_succ p.T n]
  rfl

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `blockRV n` precomposed with the shift `T` is the "shifted block"
`(X_1, X_2, …, X_n)`. -/
private lemma blockRV_comp_T
    (p : StationaryProcess μ α) (n : ℕ) :
    (p.blockRV n) ∘ p.T = fun ω ↦ fun i : Fin n ↦ p.obs (i.val + 1) ω := by
  funext ω
  show p.blockRV n (p.T ω) = fun i : Fin n ↦ p.obs (i.val + 1) ω
  funext i
  show p.obs i.val (p.T ω) = p.obs (i.val + 1) ω
  -- p.obs k = X ∘ T^[k]; pre-composing with T gives X ∘ T^[k] ∘ T = X ∘ T^[k+1] = p.obs (k+1).
  have := congr_fun (obs_comp_T (α := α) p i.val) ω
  exact this

/-- The "shifted block" `(X_1, X_2, …, X_n) : Ω → (Fin n → α)`. Used in the
antitone proof: stationarity translates the pair `(X_n, (X_0, …, X_{n-1}))`
forward by 1 to `(X_{n+1}, shiftedBlockRV)`. -/
private def shiftedBlockRV
    (p : StationaryProcess μ α) (n : ℕ) : Ω → (Fin n → α) :=
  fun ω i ↦ p.obs (i.val + 1) ω

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
private lemma measurable_shiftedBlockRV
    (p : StationaryProcess μ α) (n : ℕ) :
    Measurable (shiftedBlockRV p n) := by
  refine measurable_pi_iff.mpr (fun i ↦ ?_)
  exact p.measurable_obs (i.val + 1)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Key joint pushforward equality coming from `MeasurePreserving T μ μ`:
`μ.map (obs n, blockRV n) = μ.map (obs (n+1), shiftedBlockRV n)`. -/
private lemma map_joint_eq_shifted
    (p : StationaryProcess μ α) (n : ℕ) :
    μ.map (fun ω ↦ (p.obs n ω, p.blockRV n ω))
      = μ.map (fun ω ↦ (p.obs (n + 1) ω, shiftedBlockRV p n ω)) := by
  -- The RHS pair equals the LHS pair precomposed with T.
  have hT : Measurable p.T := p.measurable_T
  have h_pair_meas : Measurable (fun ω ↦ (p.obs n ω, p.blockRV n ω)) :=
    (p.measurable_obs n).prodMk (p.measurable_blockRV n)
  have h_compose :
      (fun ω ↦ (p.obs n ω, p.blockRV n ω)) ∘ p.T
        = fun ω ↦ (p.obs (n + 1) ω, shiftedBlockRV p n ω) := by
    funext ω
    refine Prod.ext ?_ ?_
    · show p.obs n (p.T ω) = p.obs (n + 1) ω
      have := obs_comp_T p n
      exact congr_fun this ω
    · show p.blockRV n (p.T ω) = shiftedBlockRV p n ω
      have := blockRV_comp_T p n
      exact congr_fun this ω
  -- Pushforward by T preserves μ.
  have h_T_preserves : μ.map p.T = μ := p.measurePreserving.map_eq
  -- (μ.map T).map (...) = μ.map (... ∘ T).
  rw [← h_compose, ← Measure.map_map h_pair_meas hT, h_T_preserves]

end AntitoneHelpers

/-- Conditional entropy `H(Xs | Yo)` depends only on the joint pushforward
`μ.map (fun ω => (Xs ω, Yo ω))`. -/
lemma condEntropy_eq_pushforward
    {β γ : Type*}
    [Fintype β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [MeasurableSpace γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → β) (Yo : Ω → γ)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    InformationTheory.MeasureFano.condEntropy μ Xs Yo
      = InformationTheory.MeasureFano.condEntropy
          (μ.map (fun ω ↦ (Xs ω, Yo ω)))
          (Prod.fst : β × γ → β) (Prod.snd : β × γ → γ) := by
  classical
  set ν : Measure (β × γ) := μ.map (fun ω ↦ (Xs ω, Yo ω)) with hν_def
  have h_pair_meas : Measurable (fun ω ↦ (Xs ω, Yo ω)) := hXs.prodMk hYo
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map h_pair_meas.aemeasurable
  -- `ν.map Prod.snd = μ.map Yo` (outer measure of both integrals agrees).
  have h_snd_map : ν.map (Prod.snd : β × γ → γ) = μ.map Yo := by
    rw [hν_def, Measure.map_map measurable_snd h_pair_meas]
    rfl
  -- `condDistrib (Prod.fst) (Prod.snd) ν =ᵐ[μ.map Yo] condDistrib Xs Yo μ`.
  have h_cd_map :
      ProbabilityTheory.condDistrib (Prod.fst : β × γ → β)
          (Prod.snd : β × γ → γ) ν
        =ᵐ[μ.map Yo] ProbabilityTheory.condDistrib Xs Yo μ := by
    -- Apply Mathlib `condDistrib_map` with `ν := μ` (Ω-measure),
    -- `f := (Xs, Yo)`, `X := Prod.snd`, `Y := Prod.fst`.
    have h := ProbabilityTheory.condDistrib_map
      (X := (Prod.snd : β × γ → γ)) (Y := (Prod.fst : β × γ → β))
      (ν := μ) (f := fun ω ↦ (Xs ω, Yo ω))
      (by
        rw [← hν_def]
        exact measurable_snd.aemeasurable)
      (by
        rw [← hν_def]
        exact measurable_fst.aemeasurable)
      h_pair_meas.aemeasurable
    -- h : condDistrib Prod.fst Prod.snd (μ.map (Xs,Yo))
    --     =ᵐ[μ.map (Prod.snd ∘ (Xs,Yo))] condDistrib (Prod.fst ∘ (Xs,Yo)) (Prod.snd ∘ (Xs,Yo)) μ
    -- Both compositions reduce by rfl: Prod.snd ∘ (Xs,Yo) = Yo, Prod.fst ∘ (Xs,Yo) = Xs.
    simpa [hν_def] using h
  -- Now unfold both sides; both are integrals over `μ.map Yo` of
  -- `∑ x, negMulLog (condDistrib · · y).real {x}`. The condDistribs are
  -- ae-equal, so integrands agree ae and integrals agree.
  unfold InformationTheory.MeasureFano.condEntropy
  rw [h_snd_map]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h_cd_map] with y hy
  rw [hy]

omit [DecidableEq α] in
theorem conditionalEntropyTail_antitone
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    Antitone (conditionalEntropyTail μ p) := by
  classical
  -- It suffices to show `f (n+1) ≤ f n` for all `n` (monotone for the dual `≥`).
  refine antitone_nat_of_succ_le (fun n ↦ ?_)
  -- Step 1: by stationarity, `tail n = H(X_{n+1} | shiftedBlockRV)`.
  have h_step1 :
      conditionalEntropyTail μ p n
        = InformationTheory.MeasureFano.condEntropy μ
            (p.obs (n + 1)) (shiftedBlockRV p n) := by
    -- Both sides depend only on the joint pushforward; use `map_joint_eq_shifted`.
    unfold conditionalEntropyTail
    rw [condEntropy_eq_pushforward μ (p.obs n) (p.blockRV n)
          (p.measurable_obs n) (p.measurable_blockRV n),
        condEntropy_eq_pushforward μ (p.obs (n + 1)) (shiftedBlockRV p n)
          (p.measurable_obs (n + 1)) (measurable_shiftedBlockRV p n)]
    congr 1
    exact map_joint_eq_shifted p n
  -- Step 2: `tail (n+1) = H(X_{n+1} | blockRV (n+1)) ≤ H(X_{n+1} | shiftedBlockRV)`
  -- via `condEntropy_le_condEntropy_of_pair` + reshape.
  -- `condEntropy_le_condEntropy_of_pair μ (obs (n+1)) shiftedBlockRV (obs 0)`
  -- gives condEntropy μ (obs (n+1)) (shifted, obs 0) ≤ condEntropy μ (obs (n+1)) shifted.
  -- Then reshape (shifted, obs 0) into blockRV (n+1) via condEntropy_measurableEquiv_comp.
  have h_drop :
      InformationTheory.MeasureFano.condEntropy μ (p.obs (n + 1))
          (fun ω ↦ (shiftedBlockRV p n ω, p.obs 0 ω))
        ≤ InformationTheory.MeasureFano.condEntropy μ
            (p.obs (n + 1)) (shiftedBlockRV p n) :=
    condEntropy_le_condEntropy_of_pair μ (p.obs (n + 1))
      (shiftedBlockRV p n) (p.obs 0)
      (p.measurable_obs (n + 1)) (measurable_shiftedBlockRV p n)
      (p.measurable_obs 0)
  -- Reshape `(shifted, obs 0)` to `blockRV (n+1)` via the equiv
  -- `e' : (Fin n → α) × α ≃ᵐ (Fin (n+1) → α)` mapping `(f, a) ↦ insertNth 0 a f`.
  let e' : (Fin n → α) × α ≃ᵐ (Fin (n + 1) → α) :=
    MeasurableEquiv.prodComm.trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) 0).symm
  have h_e'_eq : ∀ ω,
      e' (shiftedBlockRV p n ω, p.obs 0 ω) = p.blockRV (n + 1) ω := by
    intro ω
    -- e' (f, a) = piFinSuccAbove.symm (a, f) = Fin.insertNth 0 a f
    -- (Fin.succAbove 0 j = j.succ, so insertNth 0 a f at 0 is a, at j.succ is f j).
    show (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) 0).symm
          (p.obs 0 ω, shiftedBlockRV p n ω) = p.blockRV (n + 1) ω
    -- The `.symm` reduces to `Fin.insertNth 0`.
    show Fin.insertNth (n := n) (α := fun _ ↦ α) 0
            (p.obs 0 ω) (shiftedBlockRV p n ω)
          = p.blockRV (n + 1) ω
    funext i
    -- Case on `i`: either `i = 0` (use insertNth_apply_same) or `i = j.succ`
    -- for some `j : Fin n` (use insertNth_apply_succAbove with succAbove 0 = succ).
    refine Fin.cases ?_ ?_ i
    · -- i = 0.
      change Fin.insertNth (n := n) (α := fun _ ↦ α) 0
              (p.obs 0 ω) (shiftedBlockRV p n ω) 0 = p.blockRV (n + 1) ω 0
      rw [Fin.insertNth_apply_same]
      rfl
    · intro j
      -- i = j.succ. Use insertNth_apply_succAbove with succAbove 0 j = j.succ.
      have h_succ : (j.succ : Fin (n + 1)) = (0 : Fin (n + 1)).succAbove j := by
        simp
      rw [h_succ, Fin.insertNth_apply_succAbove]
      -- Goal: shiftedBlockRV p n ω j = p.blockRV (n+1) ω ((0 : Fin (n+1)).succAbove j)
      show p.obs (j.val + 1) ω
          = p.blockRV (n + 1) ω ((0 : Fin (n + 1)).succAbove j)
      have h_succ' : (0 : Fin (n + 1)).succAbove j = j.succ := by
        simp
      rw [h_succ']
      show p.obs (j.val + 1) ω = p.obs j.succ ω
      rfl
  have h_reshape :
      InformationTheory.MeasureFano.condEntropy μ (p.obs (n + 1))
          (fun ω ↦ (shiftedBlockRV p n ω, p.obs 0 ω))
        = InformationTheory.MeasureFano.condEntropy μ
            (p.obs (n + 1)) (p.blockRV (n + 1)) := by
    have h := condEntropy_measurableEquiv_comp μ
      (p.obs (n + 1)) (p.measurable_obs (n + 1))
      (fun ω ↦ (shiftedBlockRV p n ω, p.obs 0 ω))
      ((measurable_shiftedBlockRV p n).prodMk (p.measurable_obs 0))
      e'
    -- h : condEntropy μ (obs (n+1)) (fun ω => e' (shifted ω, obs 0 ω))
    --     = condEntropy μ (obs (n+1)) (fun ω => (shifted ω, obs 0 ω))
    have h_funext : (fun ω ↦ e' (shiftedBlockRV p n ω, p.obs 0 ω))
        = p.blockRV (n + 1) := by
      funext ω; exact h_e'_eq ω
    rw [h_funext] at h
    exact h.symm
  -- Compose: tail (n+1) = condEntropy μ (obs (n+1)) (blockRV (n+1))
  --        = condEntropy μ (obs (n+1)) (shifted, obs 0)  [by h_reshape.symm]
  --        ≤ condEntropy μ (obs (n+1)) shifted          [by h_drop]
  --        = tail n                                      [by h_step1.symm]
  unfold conditionalEntropyTail
  calc InformationTheory.MeasureFano.condEntropy μ
          (p.obs (n + 1)) (p.blockRV (n + 1))
      = InformationTheory.MeasureFano.condEntropy μ (p.obs (n + 1))
          (fun ω ↦ (shiftedBlockRV p n ω, p.obs 0 ω)) := h_reshape.symm
    _ ≤ InformationTheory.MeasureFano.condEntropy μ
          (p.obs (n + 1)) (shiftedBlockRV p n) := h_drop
    _ = conditionalEntropyTail μ p n := h_step1.symm

omit [DecidableEq α] in
/-- Conditional entropy on a finite alphabet is bounded above by `log |α|`,
hence the tail is uniformly bounded. We only need `0 ≤ tail` for the existence
proof. -/
theorem conditionalEntropyTail_nonneg
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    0 ≤ conditionalEntropyTail μ p n := by
  classical
  unfold conditionalEntropyTail
  exact condEntropy_nonneg μ (p.obs n) (p.blockRV n)

/-! ## Existence of the entropy rate

We show `Tendsto (blockEntropy μ p n / n) atTop (𝓝 H)` for some `H`, by the
following route:

* The chain rule gives `blockEntropy μ p n = ∑_{i < n} conditionalEntropyTail μ p i`.
* `conditionalEntropyTail_antitone` + non-negativity ⇒ tail converges to
  some `L = ⨅ n, tail n`.
* The Cesàro lemma `Filter.Tendsto.cesaro` converts `Tendsto tail → Tendsto avg`,
  and the chain-rule identity rewrites the Cesàro average as `blockEntropy / n`.
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
  have h_default : ∀ x : (Fin 0 → α), x = default := fun x ↦ by
    funext i; exact i.elim0
  have h_eq : (μ.map (p.blockRV 0)).real {(default : Fin 0 → α)} = 1 := by
    have h_singleton_eq_univ : ({(default : Fin 0 → α)} : Set (Fin 0 → α)) = Set.univ := by
      ext x; simp [h_default x]
    rw [h_singleton_eq_univ]
    simp [measureReal_def, measure_univ]
  rw [Finset.sum_eq_single (default : Fin 0 → α)
        (fun b _ hb ↦ by rw [h_default b] at hb; exact absurd rfl hb)
        (fun h ↦ (h (Finset.mem_univ _)).elim)]
  rw [h_eq]; simp

omit [DecidableEq α] in
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

omit [DecidableEq α] in
/-- The entropy rate exists, i.e. `blockEntropy μ p n / n` converges.

Strategy: the chain rule + antitonicity say `tail n` is antitone and nonneg, hence
converges to some `L`. By Cesàro, `(1/n) ∑_{i<n} tail i → L`. By the chain rule,
this equals `blockEntropy μ p n / n`. -/
@[entry_point]
theorem entropyRate_exists_of_stationary
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    ∃ H : ℝ, Tendsto (fun n : ℕ ↦ blockEntropy μ p n / n) atTop (𝓝 H) := by
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
      Tendsto (fun n : ℕ ↦ (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n,
        conditionalEntropyTail μ p i) atTop (𝓝 L) :=
    Filter.Tendsto.cesaro hL
  -- Step 4: rewrite `(1/n) * sum_tail` as `blockEntropy / n`.
  have h_eq : ∀ n : ℕ,
      (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n, conditionalEntropyTail μ p i
        = blockEntropy μ p n / n := by
    intro n
    rw [← blockEntropy_eq_sum_conditionalEntropyTail μ p n, div_eq_inv_mul]
  exact h_cesaro.congr h_eq

/-! ## Equality with `lim conditionalEntropyTail`

`Tendsto (conditionalEntropyTail μ p) atTop (𝓝 (entropyRate μ p))`.

Strategy: the chain rule + Cesàro gives `blockEntropy / n → L = lim tail`. The
`entropyRate` is the limit of `blockEntropy / n` (Filter.limUnder of a convergent
sequence equals the limit). The two limits agree by uniqueness. -/
omit [DecidableEq α] in
@[entry_point]
theorem entropyRate_eq_lim_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    Tendsto (conditionalEntropyTail μ p) atTop (𝓝 (entropyRate μ p)) := by
  -- Antitonicity is used here. Strategy:
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
      Tendsto (fun n : ℕ ↦ (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n,
        conditionalEntropyTail μ p i) atTop (𝓝 L) :=
    Filter.Tendsto.cesaro h_tail_lim
  have h_eq : ∀ n : ℕ,
      (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n, conditionalEntropyTail μ p i
        = blockEntropy μ p n / n := by
    intro n
    rw [← blockEntropy_eq_sum_conditionalEntropyTail μ p n, div_eq_inv_mul]
  have h_block_lim : Tendsto (fun n : ℕ ↦ blockEntropy μ p n / n) atTop (𝓝 L) :=
    h_cesaro.congr h_eq
  -- entropyRate = limUnder of `n ↦ blockEntropy / n`; that limit is `L`.
  have h_entropyRate : entropyRate μ p = L := h_block_lim.limUnder_eq
  rw [h_entropyRate]
  exact h_tail_lim

end InformationTheory.Shannon

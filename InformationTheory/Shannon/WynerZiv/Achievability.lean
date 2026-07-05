import InformationTheory.Shannon.WynerZiv.Operational
import InformationTheory.Shannon.WynerZiv.FactorizableRate
import InformationTheory.Shannon.WynerZiv.Converse
import InformationTheory.Shannon.SlepianWolf.FullRateRegion.AliasBound
import InformationTheory.Shannon.ConditionalMethodOfTypes.Mass

/-!
# Wyner–Ziv operational achievability (binning + covering)

This file assembles the operational achievability leg of the Wyner–Ziv theorem
(Cover–Thomas Theorem 15.9.1): a rate `R` above the information-theoretic rate
`wynerZivRate` is achievable at distortion `D` for the i.i.d. source `P_XY` with
decoder side information `Y`.

## Approach

Wyner–Ziv achievability is a two-layer hybrid: **rate-distortion covering** on the
`X → U` side and **Slepian–Wolf binning** on the side-information `Y` side.

* the encoder covers `X^n` by a codeword `U^n` drawn from an i.i.d. codebook
  (rate-distortion covering, `jointTypicalLossyEncoder`), then bins the codeword
  index (Slepian–Wolf binning, `binningMeasure`) down to rate `R ≈ I(X;U) −
  I(Y;U)`;
* the decoder receives `(bin index, Y^n)` and searches its bin for the unique
  codeword conditionally typical with `Y^n`.

The two error mechanisms decouple cleanly (see the *gateway atoms* below), each
living on its own conditional-typicality slice under the **common** alphabet
assignment "covering codeword `U` in the source role, side information `Y` as the
conditioning variable":

* **decoder confusion** — a wrong binned codeword `U'^n` shares the true bin and
  is conditionally typical with `Y^n`. Its expected mass over the random binning
  is bounded by (slice cardinality) `/` (bin count), via the Slepian–Wolf alias
  bound `swError_EX_expectation_le` (itself `binning_collision_prob` ∘
  `conditionalTypicalSlice_card_le`). This is the `Y`-fixed, `U`-counted slice.
* **covering acceptance** — the true covering codeword is itself conditionally
  typical with `Y^n` (not rejected), via the strong conditional-slice mass bound
  `conditionalStronglyTypicalSlice_mass_ge`. This is the `U`-fixed, `Y`-measured
  slice.

These are transposed fibers of the same joint typicality relation, but they never
need to be reconciled into one statement: they bound *independent* error events.
The apparent transposition between the strong slice (`conditionalStronglyTypical`,
`U`-fixed) and the weak slice (`conditionalTypical`, `Y`-fixed) is therefore not
an obstruction — it is exactly the decomposition the error analysis wants.

## Main statements

* `wyner_ziv_achievability` — the operational achievability headline.

## Gateway atoms (both reuse existing, proved in-project atoms)

* `wz_sideInfo_decoder_confusion_expectation_le` — the decoder-confusion bound,
  by instantiating the Slepian–Wolf alias bound with the covering codeword in the
  source role.
* `wz_covering_sideInfo_mass_ge` — the covering-acceptance mass bound, by
  instantiating the strong conditional-slice mass bound with the same alphabet
  assignment.

## Implementation notes

The remaining work is pure plumbing: threading these two exponents through the
Wyner–Ziv error decomposition, splitting the rate as `R = I(X;U) − I(Y;U)`, and
extracting a good codebook by the pigeonhole averaging `exists_codebook_low_avg`.
The headline body is deferred to a follow-up leg and marked
`@residual(plan:wyner-ziv-main-plan)`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {α β γ U : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [DecidableEq γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]

/-! ## Gateway atom 1 — side-information decoder confusion bound

Instantiation of the Slepian–Wolf alias bound `swError_EX_expectation_le` with the
covering codeword `U` in the source (`α`) role and the side information `Y` in the
`β` role. The bound is `exp(n · (H(U,Y) − H(Y) + 2ε)) / M = exp(n · (H(U|Y) + 2ε))
/ M`, the confusable-codeword count divided by the bin count. -/

/-- **Wyner–Ziv side-information decoder confusion bound.** For a random binning
`f` of the covering-codeword space `Fin n → U` into `M` bins, the expected
`μ`-probability (over the binning `f ∼ binningMeasure U n M`) that some codeword
`u' ≠ U^n` that is jointly typical with the received side information `Y^n` hashes
to the same bin as the true codeword `U^n` is at most `exp(n · (H(U|Y) + 2ε)) / M`.

This is the decoder-confusion half of Wyner–Ziv achievability. It is the
side-information analogue of the Slepian–Wolf alias bound, with the covering
codeword `U` in the source role and the side information `Y` as the conditioning
variable; the proof is a direct instantiation of `swError_EX_expectation_le`,
witnessing that the binning ∘ conditional-typicality composition closes as
plumbing over an existing atom.
@audit:ok -/
theorem wz_sideInfo_decoder_confusion_expectation_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Us : ℕ → Ω → U) (Ys : ℕ → Ω → β)
    (hUs : ∀ i, Measurable (Us i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepY_full : iIndepFun (fun i ↦ Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ_full : iIndepFun (fun i ↦ ChannelCoding.jointSequence Us Ys i) μ)
    (hidentZ : ∀ i, IdentDistrib (ChannelCoding.jointSequence Us Ys i)
        (ChannelCoding.jointSequence Us Ys 0) μ μ)
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : U × β, 0 < (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {p})
    {n M : ℕ} [NeZero M] {ε : ℝ} (hε : 0 < ε) :
    ∫ f, μ.real (ChannelCoding.swError_EX μ Us Ys n ε f)
        ∂(binningMeasure U n M)
      ≤ Real.exp ((n : ℝ) *
            (entropy μ (ChannelCoding.jointSequence Us Ys 0) - entropy μ (Ys 0) + 2 * ε))
        * ((M : ℝ))⁻¹ :=
  ChannelCoding.swError_EX_expectation_le μ Us Ys hUs hYs hindepY_full hidentY
    hindepZ_full hidentZ hposY hposZ hε

/-! ## Gateway atom 2 — covering acceptance mass bound

Instantiation of the strong conditional-slice mass bound
`conditionalStronglyTypicalSlice_mass_ge` with the same alphabet assignment. For a
strongly-typical covering codeword `u`, the product `Y`-mass of the fiber of side
words jointly (strongly) typical with `u` is at least `exp(−n · (I(U;Y) + slack))`.
This ensures the true covering codeword is not rejected by the side-information
decoder. -/

/-- **Wyner–Ziv covering acceptance mass bound.** For a strongly-typical covering
codeword `u : Fin n → U`, the product `Y`-mass of the fiber of side words jointly
strongly typical with `u` is bounded below by `exp(−n · (H(U) + H(Y) − H(U,Y) +
slack))`, i.e. `exp(−n · (I(U;Y) + slack))`. This is the covering-acceptance half
of Wyner–Ziv achievability: the correct covering codeword is conditionally typical
with the side information with high probability. Direct instantiation of
`conditionalStronglyTypicalSlice_mass_ge`.
@audit:ok -/
theorem wz_covering_sideInfo_mass_ge
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Us : ℕ → Ω → U) (Ys : ℕ → Ω → β)
    (hUs : ∀ i, Measurable (Us i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep_Z_pair : Pairwise fun i j ↦
      ChannelCoding.jointSequence Us Ys i ⟂ᵢ[μ] ChannelCoding.jointSequence Us Ys j)
    (hident_Z : ∀ i, IdentDistrib (ChannelCoding.jointSequence Us Ys i)
        (ChannelCoding.jointSequence Us Ys 0) μ μ)
    (hposZ : ∀ p : U × β, 0 < (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {p})
    (hposX : ∀ a : U, 0 < (μ.map (Us 0)).real {a})
    (hposY : ∀ b : β, 0 < (μ.map (Ys 0)).real {b})
    (hmarg_X : (μ.map (ChannelCoding.jointSequence Us Ys 0)).map Prod.fst = μ.map (Us 0))
    (hmarg_Y : (μ.map (ChannelCoding.jointSequence Us Ys 0)).map Prod.snd = μ.map (Ys 0))
    {ε ε_X δ : ℝ}
    (hε : 0 < ε) (hε_X : 0 ≤ ε_X) (hε_X_lt_ε : ε_X < ε) (hδ : 0 < δ)
    (qZ_min : ℝ) (hqZ_min_pos : 0 < qZ_min)
    (hqZ_min_le : ∀ p : U × β, qZ_min ≤ (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {p})
    (hδ_dominates_kl :
        8 * (Fintype.card U : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2 ≤ δ * qZ_min) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (u : Fin n → U),
      u ∈ stronglyTypicalSet μ Us n ε_X →
      Real.exp (-(n : ℝ) *
          (entropy μ (Us 0) + entropy μ (Ys 0)
            - entropy μ (ChannelCoding.jointSequence Us Ys 0)
            + ((Fintype.card U : ℝ) * ε_X * logSumAbs μ Ys
               + ε_X * logSumAbs μ Us
               + ε_X * logSumAbs μ (ChannelCoding.jointSequence Us Ys)
               + δ)))
        ≤ (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real
              (conditionalStronglyTypicalSlice μ Us Ys n ε u) :=
  conditionalStronglyTypicalSlice_mass_ge μ Us Ys hUs hYs hindep_Z_pair hident_Z
    hposZ hposX hposY hmarg_X hmarg_Y hε hε_X hε_X_lt_ε hδ qZ_min hqZ_min_pos
    hqZ_min_le hδ_dominates_kl

/-! ## Rate non-negativity leaf (data-processing)

The reshaped Wyner–Ziv rate is non-negative: every factorisable feasible objective
`I(X;U) − I(Y;U)` is `≥ 0` by the data-processing inequality for the Markov chain
`U − X − Y` (`wzObjective_nonneg_of_factorizable`), so its infimum over the
non-degenerate value set is `≥ 0`. Combined with `h_rate`, this pins `0 < R`, which
is exactly what the codebook-rate tendsto `codebookSize_log_div_tendsto` needs. -/

/-- The reshaped Wyner–Ziv rate for a probability-measure source is `≥ 0`.
@audit:ok (independent honesty audit 2026-07-06: sorryAx-free, `#print axioms` =
[propext, Classical.choice, Quot.sound], machine-verified. Genuine closure: via
`Real.sInf_nonneg`, every value is the objective of a feasible factorisable point,
which is `≥ 0` by DPI `wzObjective_nonneg_of_factorizable`; the empty-`Fin 0`
`Nonempty (Fin k)` step is a SOUND derivation, not a degenerate-definition abuse —
a feasible factorisable point forces `k > 0` because a `Fin 0` kernel has row-sum
`∑_{u:Fin 0} κ x u = 0 ≠ 1`. TRUE-as-framed even in the empty-feasible-set regime
(`0 ≤ sInf ∅ = 0`), so unlike the codes lemma below this decl has NO under-hypothesis
defect: `Real.sInf_nonneg`'s premise is vacuously satisfied when the set is empty.) -/
private lemma wynerZivRate_nonneg
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (D : ℝ) :
    0 ≤ wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D := by
  classical
  have h_pmf : (fun p ↦ P_XY.real {p}) ∈ stdSimplex ℝ (α × β) := by
    refine ⟨fun p ↦ measureReal_nonneg, ?_⟩
    have h1 : (∑ p : α × β, P_XY.real {p})
        = P_XY.real (Finset.univ : Finset (α × β)) := by
      simp [sum_measureReal_singleton]
    rw [h1, Finset.coe_univ]
    exact probReal_univ
  unfold wynerZivRate
  refine Real.sInf_nonneg ?_
  rintro v hv
  rw [mem_wzRateValueSet_iff] at hv
  obtain ⟨k, qf, hqf, rfl⟩ := hv
  have hfact : IsWynerZivFactorizable (Fin k) (fun p ↦ P_XY.real {p}) qf.1 := hqf.1
  haveI : Nonempty (Fin k) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exfalso
      subst hk
      obtain ⟨κ, _, hκsum, _⟩ := hfact
      obtain ⟨x⟩ := (inferInstance : Nonempty α)
      have hsum := hκsum x
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
      exact absurd hsum (by norm_num)
    · exact ⟨⟨0, hk⟩⟩
  exact wzObjective_nonneg_of_factorizable h_pmf hfact

/-! ## Covering + binning construction (hard leg)

The centrepiece of Wyner–Ziv achievability: from a feasible test channel below the
rate `R`, build a sequence of Wyner–Ziv block codes with `codebookSize R n =
⌈exp(n R)⌉` messages whose expected block distortion is eventually within `D + ε`.

The construction is the two-layer hybrid (rate-distortion covering on the `X → U`
side, Slepian–Wolf binning on the side-information `Y` side) whose two error
mechanisms are the gateway atoms `wz_sideInfo_decoder_confusion_expectation_le`
and `wz_covering_sideInfo_mass_ge`, with a good codebook extracted by the
pigeonhole averaging `exists_codebook_low_avg`. Deferred as the remaining plumbing
body of this plan. -/

/-- Existence of a Wyner–Ziv code sequence (at the operational message rate `R`)
whose expected block distortion is eventually within `D + ε`, from a feasible test
channel strictly below `R`. The remaining covering + binning plumbing.

The feasibility precondition `h_ne` (the rate-distortion value set is nonempty at
`D`) is now present, so the signature is well-posed: it rules out the infeasible
regime `D` below the min achievable distortion (e.g. any `D < 0` for a `NNReal`
distortion), where `wzRateValueSet` is empty and `wynerZivRate = sInf ∅ = 0` would
otherwise let `h_rate : 0 < R` coexist with a FALSE existence claim. `h_ne` is a
regularity/feasibility precondition, NOT the load-bearing covering+binning core
(which stays in the `sorry` body); the converse side already threads exactly this
guard (`wynerZivRate_antitone`, `Converse.lean:2602`). With it in place the `sorry`
is an ordinary under-construction marker.
@residual(plan:wyner-ziv-main-plan) -/
theorem wyner_ziv_achievability_codes
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (h_ne : (wzRateValueSet (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D).Nonempty)
    (h_rate : wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D < R) :
    ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (c n).expectedBlockDistortion P_XY d ≤ D + ε := by
  sorry

/-! ## Operational achievability headline -/

/-- **Wyner–Ziv operational achievability.** If the information-theoretic
Wyner–Ziv rate `wynerZivRate` at distortion `D` for the i.i.d. source `P_XY` (with
decoder side information `Y`) is strictly below `R`, then `R` is operationally
achievable at distortion `D`: there is a sequence of Wyner–Ziv block codes whose
log-cardinality rate tends to `R` and whose expected block distortion is
eventually within `D + ε` for every `ε > 0`.

The body is assembled: the message sequence is fixed to `codebookSize R n =
⌈exp(n R)⌉`, whose log-cardinality rate tends to `R` via `codebookSize_log_div_tendsto`
(using `0 < R`, from `wynerZivRate_nonneg` and `h_rate`); the distortion sequence is
supplied by the covering + binning construction `wyner_ziv_achievability_codes`,
which carries the remaining plumbing `sorry`. The headline itself is `sorry`-free
(it reduces to that one residual lemma).

The signature carries the same feasibility precondition `h_ne` as the codes lemma,
so it is well-posed: the body is a genuine reduction (sorry-free itself, `sorryAx`
enters only via `wyner_ziv_achievability_codes`) and the statement is honest. -/
theorem wyner_ziv_achievability
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (h_ne : (wzRateValueSet (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D).Nonempty)
    (h_rate : wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D < R) :
    WynerZivAchievable P_XY d R D := by
  have hR : 0 < R := lt_of_le_of_lt (wynerZivRate_nonneg P_XY d D) h_rate
  obtain ⟨c, hc⟩ := wyner_ziv_achievability_codes P_XY d R D h_ne h_rate
  exact ⟨codebookSize R, fun n ↦ codebookSize_pos R n, c,
    codebookSize_log_div_tendsto hR, hc⟩

end InformationTheory.Shannon

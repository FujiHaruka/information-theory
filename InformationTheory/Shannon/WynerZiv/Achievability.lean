import InformationTheory.Shannon.WynerZiv.Operational
import InformationTheory.Shannon.WynerZiv.FactorizableRate
import InformationTheory.Shannon.WynerZiv.Converse
import InformationTheory.Shannon.SlepianWolf.FullRateRegion.AliasBound
import InformationTheory.Shannon.ConditionalMethodOfTypes.Mass
import InformationTheory.Shannon.RateDistortion.AchievabilityStrongTypicality

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

/-- **Witness extraction (Step 0).** From the feasibility guard `h_ne` and the
rate strict inequality `h_rate`, extract a concrete finite auxiliary alphabet
`Fin k`, a factorisable test channel `qf` feasible at distortion `D`, whose
Wyner–Ziv objective `I(X;U) − I(Y;U)` is strictly below `R`.

This is `exists_lt_of_csInf_lt` on the infimum-of-values definition of
`wynerZivRate` (`= sInf (wzRateValueSet …)`), with the resulting value unpacked
by `mem_wzRateValueSet_iff` into a feasible factorisable point.
@audit:ok (independent honesty audit 2026-07-06: sorryAx-free, `#print axioms` =
[propext, Classical.choice, Quot.sound], machine-verified. Genuine witness
extraction, not degenerate: `exists_lt_of_csInf_lt` requires `h_ne` (value set
nonempty) so the `sInf < R` is realised by an actual value, and
`mem_wzRateValueSet_iff` unpacks it into a factorisable feasible point `(k, qf)`
with objective `< R` — no vacuous/`sInf ∅` shortcut.) -/
private lemma wz_testChannel_of_rate_lt
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (h_ne : (wzRateValueSet (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D).Nonempty)
    (h_rate : wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D < R) :
    ∃ (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ)),
      qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D
        ∧ wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 < R := by
  unfold wynerZivRate at h_rate
  obtain ⟨v, hv_mem, hv_lt⟩ := exists_lt_of_csInf_lt h_ne h_rate
  rw [mem_wzRateValueSet_iff] at hv_mem
  obtain ⟨k, qf, hqf, hval⟩ := hv_mem
  refine ⟨k, qf, hqf, ?_⟩
  rw [hval]; exact hv_lt

/-! ### Leaf atoms for the covering + binning construction

The following helper lemmas are the small, fully-proved atoms that the heavy
covering+binning core (`wz_goodCode_exists_of_testChannel`) consumes: a
`Nonempty (Fin k)` extractor from feasibility (P0), a full-support kernel
perturbation (P1), and a public `exp(n c)/codebookSize R n → 0` decay adapter
(P2, re-proved locally because the Slepian–Wolf original is `private`). -/

/-- **Nonempty auxiliary alphabet (Step 0 leaf).** A Wyner–Ziv factorisable
joint over a source pmf on `α × β` forces a nonempty covering alphabet `Fin k`:
the row-stochastic kernel condition `∑_{u : Fin k} κ x u = 1` is impossible for
`k = 0` (the empty sum is `0 ≠ 1`), using `Nonempty α` to pick a row `x`. -/
private lemma wz_nonempty_of_factorizable
    {P : α × β → ℝ} {k : ℕ} {q : α × β × Fin k → ℝ}
    (hfact : IsWynerZivFactorizable (Fin k) P q) :
    Nonempty (Fin k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exfalso
    subst hk
    obtain ⟨κ, _, hκsum, _⟩ := hfact
    obtain ⟨x⟩ := (inferInstance : Nonempty α)
    have hsum := hκsum x
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact absurd hsum (by norm_num)
  · exact ⟨⟨0, hk⟩⟩

/-- **Full-support kernel perturbation (Step 1 leaf).** From a feasible
factorisable test channel `qf` (row-stochastic kernel, distortion `≤ D`) whose
Wyner–Ziv objective is strictly below `R`, and any slack `δ > 0`, produce a
perturbed factorisable channel `q'` with a *strictly positive kernel* `κ'`
(full support), whose objective is still `< R` and whose distortion is `≤ D + δ`.

The perturbation is `q' := (1 - τ) • qf.1 + τ • q_unif` with `q_unif` the
uniform-kernel factorisable joint and `τ ∈ (0, 1]` small: convex combination
preserves factorisability (`IsWynerZivFactorizable_convex_combination`) and
distortion feasibility (`WynerZivFactorizableConstraint_convex_combination`),
the kernel `κ' = (1 - τ) κ + τ/k ≥ τ/k > 0` gains full support, and continuity
of the objective (`continuous_wzObjective`) keeps it `< R` for small `τ`.

Note this yields full support of the *kernel*, hence full support of the
`(X, U)` joint marginal `wzMarginalXU q'` only on `{x | 0 < P_X x}` (see the
construction lemma's stall note): `wzMarginalXU q' (x,u) = κ'(x,u)·P_X(x)`. -/
private lemma wz_fullKernelSupport_perturbation
    (P : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    {k : ℕ} {qf : (α × β × Fin k → ℝ) × (Fin k × β → γ)}
    (hfact : IsWynerZivFactorizable (Fin k) P qf.1)
    (hdist : wzExpectedDistortion (Fin k) d qf.1 qf.2 ≤ D)
    {R : ℝ} (hobj : wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 < R)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (q' : α × β × Fin k → ℝ) (κ' : α → Fin k → ℝ),
      (∀ x y u, q' (x, y, u) = κ' x u * P (x, y))
      ∧ (∀ x u, 0 < κ' x u)
      ∧ (∀ x, ∑ u, κ' x u = 1)
      ∧ IsWynerZivFactorizable (Fin k) P q'
      ∧ (wzMutualInfoXU (Fin k) q' - wzMutualInfoYU (Fin k) q' < R)
      ∧ wzExpectedDistortion (Fin k) d q' qf.2 ≤ D + δ := by
  -- Nonempty covering alphabet ⇒ `0 < k`, so the uniform kernel `1/k` is well-defined.
  have hne : Nonempty (Fin k) := wz_nonempty_of_factorizable hfact
  have hkpos : 0 < k := Fin.pos_iff_nonempty.mpr hne
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  -- Extract the row-stochastic kernel of `qf.1`.
  obtain ⟨κ, hκnn, hκsum, hκeq⟩ := hfact
  -- Uniform kernel and its factorisable joint `qu (x,y,u) = (1/k) · P(x,y)`.
  set qu : α × β × Fin k → ℝ := fun p ↦ (k : ℝ)⁻¹ * P (p.1, p.2.1) with hqu
  have huniform_sum : (∑ _u : Fin k, (k : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hkR.ne'
  have hfact_qu : IsWynerZivFactorizable (Fin k) P qu := by
    refine ⟨fun _ _ ↦ (k : ℝ)⁻¹, fun _ _ ↦ (inv_nonneg.mpr hkR.le), fun _ ↦ huniform_sum,
      fun x y u ↦ ?_⟩
    rfl
  -- Feasibility memberships at thresholds `D` and `Du`.
  set Du : ℝ := wzExpectedDistortion (Fin k) d qu qf.2 with hDudef
  have hmem_qf : (qf.1, qf.2) ∈ WynerZivFactorizableConstraint (Fin k) P d D :=
    ⟨⟨κ, hκnn, hκsum, hκeq⟩, hdist⟩
  have hmem_qu : (qu, qf.2) ∈ WynerZivFactorizableConstraint (Fin k) P d Du :=
    ⟨hfact_qu, le_refl _⟩
  -- The perturbation path `τ ↦ (1-τ)·qf.1 + τ·qu`.
  set pert : ℝ → (α × β × Fin k → ℝ) := fun τ ↦ (1 - τ) • qf.1 + τ • qu with hpert
  have hpert_cont : Continuous pert :=
    ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  -- Objective is continuous along the path, `< R` at `τ = 0` (where `pert 0 = qf.1`).
  set F : (α × β × Fin k → ℝ) → ℝ :=
    fun q ↦ wzMutualInfoXU (Fin k) q - wzMutualInfoYU (Fin k) q with hF
  have hFcont : Continuous F := continuous_wzObjective (Fin k)
  have hpert0 : pert 0 = qf.1 := by
    simp only [hpert, sub_zero, one_smul, zero_smul, add_zero]
  have hFpert0_lt : F (pert 0) < R := by rw [hpert0]; exact hobj
  have hgcont : Continuous (fun τ ↦ F (pert τ)) := hFcont.comp hpert_cont
  -- Neighbourhood of `0` on which the objective stays `< R`.
  obtain ⟨ρ, hρpos, hρ⟩ :=
    Metric.continuousAt_iff.mp hgcont.continuousAt (R - F (pert 0)) (by linarith)
  -- Distortion slack control constant.
  set C : ℝ := |Du - D| + 1 with hCdef
  have hCpos : 0 < C := by positivity
  -- Choose `τ` small: below `ρ` (objective), `≤ 1` (convex weight), `≤ δ/C` (distortion).
  set τ : ℝ := min (ρ / 2) (min 1 (δ / C)) with hτdef
  have hτpos : 0 < τ :=
    lt_min (by linarith) (lt_min one_pos (div_pos hδ hCpos))
  have hτle1 : τ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hτltρ : τ < ρ := (min_le_left _ _).trans_lt (by linarith)
  have hτleδC : τ ≤ δ / C := (min_le_right _ _).trans (min_le_right _ _)
  have hτ0 : (0 : ℝ) ≤ 1 - τ := by linarith
  -- Objective bound at the chosen `τ`.
  have hdτ : dist τ (0 : ℝ) < ρ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hτpos]; exact hτltρ
  have hFpertτ : F (pert τ) < R := by
    have h := hρ hdτ
    rw [Real.dist_eq] at h
    have h2 : F (pert τ) - F (pert 0) ≤ |F (pert τ) - F (pert 0)| := le_abs_self _
    linarith
  -- Distortion bound at the chosen `τ` via the convex-combination feasibility.
  have hmem_τ : (pert τ, qf.2) ∈
      WynerZivFactorizableConstraint (Fin k) P d ((1 - τ) * D + τ * Du) :=
    WynerZivFactorizableConstraint_convex_combination (Fin k) P d qf.2
      hmem_qf hmem_qu hτ0 hτpos.le (by ring)
  have hDuDC : Du - D ≤ C := le_trans (le_abs_self _) (by rw [hCdef]; linarith)
  have hτC : τ * C ≤ δ := by
    have h := mul_le_mul_of_nonneg_right hτleδC hCpos.le
    rwa [div_mul_cancel₀ δ hCpos.ne'] at h
  have hτDuD : τ * (Du - D) ≤ δ :=
    (mul_le_mul_of_nonneg_left hDuDC hτpos.le).trans hτC
  have hdistτ : wzExpectedDistortion (Fin k) d (pert τ) qf.2 ≤ D + δ := by
    calc wzExpectedDistortion (Fin k) d (pert τ) qf.2
        ≤ (1 - τ) * D + τ * Du := hmem_τ.2
      _ = D + τ * (Du - D) := by ring
      _ ≤ D + δ := by linarith
  -- Assemble the perturbed channel with its explicit full-support kernel.
  refine ⟨pert τ, fun x u ↦ (1 - τ) * κ x u + τ * (k : ℝ)⁻¹, ?_, ?_, ?_, ?_, hFpertτ, hdistτ⟩
  · -- factorisation identity
    intro x y u
    simp only [hpert, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hqu, hκeq x y u]
    ring
  · -- strict kernel positivity
    intro x u
    have h1 : 0 ≤ (1 - τ) * κ x u := mul_nonneg hτ0 (hκnn x u)
    have h2 : 0 < τ * (k : ℝ)⁻¹ := mul_pos hτpos (inv_pos.mpr hkR)
    linarith
  · -- row-sum `1`
    intro x
    have : (∑ u, ((1 - τ) * κ x u + τ * (k : ℝ)⁻¹))
        = (1 - τ) * (∑ u, κ x u) + τ * (∑ _u : Fin k, (k : ℝ)⁻¹) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [this, hκsum x, huniform_sum]; ring
  · -- `IsWynerZivFactorizable` witness
    refine ⟨fun x u ↦ (1 - τ) * κ x u + τ * (k : ℝ)⁻¹, fun x u ↦ ?_, fun x ↦ ?_, fun x y u ↦ ?_⟩
    · have h1 : 0 ≤ (1 - τ) * κ x u := mul_nonneg hτ0 (hκnn x u)
      have h2 : 0 ≤ τ * (k : ℝ)⁻¹ := (mul_pos hτpos (inv_pos.mpr hkR)).le
      linarith
    · have : (∑ u, ((1 - τ) * κ x u + τ * (k : ℝ)⁻¹))
          = (1 - τ) * (∑ u, κ x u) + τ * (∑ _u : Fin k, (k : ℝ)⁻¹) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [this, hκsum x, huniform_sum]; ring
    · simp only [hpert, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hqu, hκeq x y u]
      ring

/-- **Message-count decay adapter (Step 6 leaf).** For `c < R`, the ratio
`exp(n c) / codebookSize R n → 0` as `n → ∞`. This is the E2 decoder-confusion
decay term (collision mass over the bin count). Re-proved locally here because
the Slepian–Wolf original `tendsto_exp_mul_codebookSize_inv` is `private` to
`PairBound.lean`; the proof is a `squeeze_zero` against `exp(n (c − R))` using
`(codebookSize R n)⁻¹ ≤ exp(−n R)` from `Nat.le_ceil`. -/
private lemma wz_tendsto_exp_mul_codebookSize_inv {c R : ℝ} (hcR : c < R) :
    Filter.Tendsto
      (fun n : ℕ ↦ Real.exp ((n : ℝ) * c) * ((codebookSize R n : ℝ))⁻¹)
      Filter.atTop (𝓝 0) := by
  -- `(codebookSize R n)⁻¹ ≤ exp(-n R)` from `exp(n R) ≤ ⌈exp(n R)⌉`.
  have h_inv_le : ∀ n : ℕ,
      ((codebookSize R n : ℝ))⁻¹ ≤ Real.exp (-(n : ℝ) * R) := by
    intro n
    have hpos : (0 : ℝ) < Real.exp ((n : ℝ) * R) := Real.exp_pos _
    have hle : Real.exp ((n : ℝ) * R) ≤ (codebookSize R n : ℝ) := by
      unfold codebookSize
      exact Nat.le_ceil _
    calc ((codebookSize R n : ℝ))⁻¹
        ≤ (Real.exp ((n : ℝ) * R))⁻¹ := inv_anti₀ hpos hle
      _ = Real.exp (-(n : ℝ) * R) := by rw [← Real.exp_neg]; ring_nf
  -- Upper bound by `exp(n (c - R)) → 0`, then squeeze.
  have hub : Filter.Tendsto
      (fun n : ℕ ↦ Real.exp ((n : ℝ) * (c - R))) Filter.atTop (𝓝 0) := by
    have hRc : 0 < R - c := sub_pos.mpr hcR
    have htend : Filter.Tendsto
        (fun n : ℕ ↦ (n : ℝ) * (R - c)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_mul_const hRc tendsto_natCast_atTop_atTop
    have hcomp := Real.tendsto_exp_neg_atTop_nhds_zero.comp htend
    refine hcomp.congr (fun n ↦ ?_)
    simp only [Function.comp_apply]
    rw [show (n : ℝ) * (c - R) = -((n : ℝ) * (R - c)) by ring]
  refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) hub
  · exact mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr (by positivity))
  · calc Real.exp ((n : ℝ) * c) * ((codebookSize R n : ℝ))⁻¹
        ≤ Real.exp ((n : ℝ) * c) * Real.exp (-(n : ℝ) * R) :=
          mul_le_mul_of_nonneg_left (h_inv_le n) (Real.exp_pos _).le
      _ = Real.exp ((n : ℝ) * (c - R)) := by rw [← Real.exp_add]; ring_nf

/-! ### Covering + binning construction skeleton (S1/S2/C/BD/E)

The monolithic covering+binning body of `wz_goodCode_exists_of_testChannel` is
decomposed into an ordered chain of sub-lemmas. The pure-regularity leaf
`wz_restrictedCoveringJoint_pos` (S1) is proved here; the heavy covering /
source-support / binning-decoder / diagonalization steps
(`wz_covering_lossyCode_exists`, `wz_expectedBlockDistortion_source_agree`,
`wz_perDelta_codes_exist`, `wz_diagonalize_slack`) are laid as `sorry`-bodied atoms
`@residual(plan:wyner-ziv-main-plan)` for follow-up legs. Full support of the
covering source stays proof-internal (restricted to the subtype `{x // 0 < P_X x}`),
never a signature hypothesis. -/

/-- **(S1) Restricted covering joint, full support (leaf).** From a strictly
positive row-stochastic kernel `κ'` and the source marginal `P_X x = ∑_y P_XY(x,y)`,
the `(X, U)` joint `κ'(x, u) · P_X(x)` restricted to the support subtype
`α' := {x // 0 < P_X x}` is a strictly positive pmf on `α' × Fin k`:

* `α'` is nonempty (a probability measure cannot have every row of `P_X` vanish);
* the joint is strictly positive on `α' × Fin k` (both factors are positive there);
* it lies in the standard simplex (row-sums collapse to `∑_{x' : α'} P_X(x'.1) = 1`,
  the zero atoms of `P_X` contributing nothing).

This is the global-full-support source the rate-distortion covering theorem
`rate_distortion_achievability` hard-requires (`hqStar_pos`), obtained on the
restricted alphabet because factorisability forces `P_X`'s zero atoms into the
joint regardless of `κ'`.
@audit:ok (independent honesty audit 2026-07-06: genuine leaf, sorry-free with no
hidden residual; `#print axioms` = `[propext, Classical.choice, Quot.sound]`) -/
private lemma wz_restrictedCoveringJoint_pos
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (hκ'pos : ∀ x u, 0 < κ' x u) (hκ'sum : ∀ x, ∑ u, κ' x u = 1) :
    Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}
      ∧ (∀ p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k,
            0 < κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
      ∧ (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k ↦
            κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
          ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k) := by
  -- The X-marginal `P_X x = ∑_y P_XY(x,y)` is non-negative and totals `1`.
  have hPnn : ∀ x : α, 0 ≤ ∑ y, P_XY.real {(x, y)} :=
    fun x ↦ Finset.sum_nonneg fun y _ ↦ measureReal_nonneg
  have htot : (∑ x : α, ∑ y : β, P_XY.real {(x, y)}) = 1 := by
    have h1 : (∑ p : α × β, P_XY.real {p}) = 1 := by
      have h2 : (∑ p : α × β, P_XY.real {p})
          = P_XY.real (Finset.univ : Finset (α × β)) := by
        simp [sum_measureReal_singleton]
      rw [h2, Finset.coe_univ]; exact probReal_univ
    rw [← h1, Fintype.sum_prod_type]
  -- Nonemptiness: not every row can vanish, else the total would be `0`.
  have hne : Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}} := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hall : ∀ x : α, (∑ y, P_XY.real {(x, y)}) = 0 := by
      intro x
      by_contra hx
      exact h.false ⟨x, lt_of_le_of_ne (hPnn x) (Ne.symm hx)⟩
    have hz : (∑ x : α, ∑ y : β, P_XY.real {(x, y)}) = 0 :=
      Finset.sum_eq_zero fun x _ ↦ hall x
    rw [htot] at hz
    exact one_ne_zero hz
  -- Positivity of the restricted joint on `α' × Fin k`.
  have hpos : ∀ p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k,
      0 < κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)} :=
    fun p ↦ mul_pos (hκ'pos p.1.1 p.2) p.1.2
  refine ⟨hne, hpos, fun p ↦ (hpos p).le, ?_⟩
  -- Row-sums: `∑_{(x',u)} κ'(x'.1,u)·P_X(x'.1) = ∑_{x' : α'} P_X(x'.1) = 1`.
  simp only [Fintype.sum_prod_type]
  trans (∑ x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}, ∑ y, P_XY.real {(x'.1, y)})
  · refine Finset.sum_congr rfl fun x' _ ↦ ?_
    rw [← Finset.sum_mul, hκ'sum x'.1, one_mul]
  · rw [← Finset.sum_subtype (Finset.univ.filter (fun x ↦ 0 < ∑ y, P_XY.real {(x, y)}))
          (fun x ↦ by simp) (fun x ↦ ∑ y, P_XY.real {(x, y)})]
    rw [Finset.sum_subset (Finset.filter_subset _ _)
          (fun x _ hx ↦ le_antisymm (not_lt.mp (by simpa using hx)) (hPnn x))]
    exact htot

/-- **(S2) Source-support block-distortion reconciliation.** Two Wyner–Ziv codes
that decode identically on every source sequence hitting only support atoms of
`P_X` have equal expected block distortion, because `Measure.pi P_XY` assigns zero
mass to sequences reaching a zero atom of `P_X`. This is the null-set transport that
lets a code built on the support subtype `α' := {x // 0 < P_X x}` extend to a code
on the full alphabet `α` without changing its distortion.

`hagree` is a genuine agreement precondition (not a bundled covering bound); the
conclusion is the measure-level distortion equality only. -/
private lemma wz_expectedBlockDistortion_source_agree
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) {M n : ℕ} (c₁ c₂ : WynerZivCode M n α β γ)
    (hagree : ∀ (x : Fin n → α) (y : Fin n → β),
        (∀ i, 0 < ∑ y', P_XY.real {(x i, y')}) →
          c₁.decoder (c₁.encoder x, y) = c₂.decoder (c₂.encoder x, y)) :
    c₁.expectedBlockDistortion P_XY d = c₂.expectedBlockDistortion P_XY d := by
  classical
  -- The full-support source event holds `Measure.pi P_XY`-a.e.: a sequence hitting a
  -- zero atom of the `X`-marginal `P_X` lies in a null coordinate cylinder.
  have hfull : ∀ᵐ p ∂(Measure.pi (fun _ : Fin n ↦ P_XY)),
      ∀ i, 0 < ∑ y', P_XY.real {((p i).1, y')} := by
    rw [ae_all_iff]
    intro i
    -- The `i`-th coordinate marginal of the product source is `P_XY`.
    have hmp : MeasurePreserving (Function.eval i)
        (Measure.pi (fun _ : Fin n ↦ P_XY)) P_XY :=
      measurePreserving_eval (fun _ : Fin n ↦ P_XY) i
    rw [ae_iff]
    -- The bad set is the coordinate-`i` preimage of a bad first-marginal set.
    have hset : {p : Fin n → α × β | ¬ 0 < ∑ y', P_XY.real {((p i).1, y')}}
        = Function.eval i ⁻¹'
            {q : α × β | ¬ 0 < ∑ y', P_XY.real {(q.1, y')}} := rfl
    rw [hset, hmp.measure_preimage ((Set.toFinite _).measurableSet.nullMeasurableSet)]
    -- The first-marginal bad set is `P_XY`-null: each of its atoms is a zero atom of `P_X`.
    have hreal : P_XY.real {q : α × β | ¬ 0 < ∑ y', P_XY.real {(q.1, y')}} = 0 := by
      have hfin : ({q : α × β | ¬ 0 < ∑ y', P_XY.real {(q.1, y')}}).Finite :=
        Set.toFinite _
      rw [← hfin.coe_toFinset, ← sum_measureReal_singleton]
      refine Finset.sum_eq_zero fun q hq => ?_
      rw [hfin.mem_toFinset] at hq
      have hq' : ¬ 0 < ∑ y', P_XY.real {(q.1, y')} := hq
      have hsum_zero : ∑ y', P_XY.real {(q.1, y')} = 0 :=
        le_antisymm (not_lt.mp hq') (Finset.sum_nonneg fun y' _ => measureReal_nonneg)
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun y' _ => measureReal_nonneg)).mp hsum_zero q.2 (Finset.mem_univ q.2)
    exact (measureReal_eq_zero_iff (measure_ne_top P_XY _)).mp hreal
  -- On that full-support event the two codes decode identically, so the integrands agree a.e.
  unfold WynerZivCode.expectedBlockDistortion
  refine integral_congr_ae ?_
  filter_upwards [hfull] with p hp
  rw [hagree (fun i ↦ (p i).1) (fun i ↦ (p i).2) hp]

open ChannelCoding in
/-- Strong-typicality ⟹ distortion-typicality bridge for the `rdAmbient` source.
A joint strongly typical pair `(x, y)` (within `ε_join`) is entropy-typical on all
three axes and its empirical block distortion is within `δ_typ` of the expected
distortion, provided the three axis slacks fit under `ε_dist` and the aggregate
distortion drift fits under `δ_typ`. Used to discharge the covering theorem's
`h_jts_subset_dts` premise. -/
private lemma wz_jointStronglyTypical_mem_distortionTypical
    {k : ℕ} [Nonempty (Fin k)] {α' : Type*} [Fintype α'] [DecidableEq α'] [Nonempty α']
    [MeasurableSpace α'] [MeasurableSingletonClass α']
    (qStar : α' × Fin k → ℝ) (hmem : qStar ∈ stdSimplex ℝ (α' × Fin k))
    (d' : DistortionFn α' (Fin k)) {ε_join ε_dist δ_typ : ℝ} (hej_nn : 0 ≤ ε_join)
    (hbX : (Fintype.card (Fin k) : ℝ) * ε_join
        * logSumAbs (rdAmbient qStar) iidXs < ε_dist)
    (hbY : (Fintype.card α' : ℝ) * ε_join
        * logSumAbs (rdAmbient qStar) iidYs < ε_dist)
    (hbJ : ε_join * logSumAbs (rdAmbient qStar) (jointSequence iidXs iidYs) < ε_dist)
    (hdist : ε_join * ∑ p : α' × Fin k, ((d' p.1 p.2 : NNReal) : ℝ) ≤ δ_typ)
    {n : ℕ} (hn : 0 < n) (x : Fin n → α') (y : Fin n → Fin k)
    (hxy : (x, y) ∈ jointStronglyTypicalSet (rdAmbient qStar) iidXs iidYs n ε_join) :
    (x, y) ∈ distortionTypicalSet (rdAmbient qStar) iidXs iidYs d' n ε_dist δ_typ := by
  haveI hμprob : IsProbabilityMeasure (rdAmbient qStar) :=
    rdAmbient_isProbabilityMeasure qStar hmem
  have hmarg_X : ((rdAmbient qStar).map (jointSequence iidXs iidYs 0)).map Prod.fst
      = (rdAmbient qStar).map (iidXs 0) := by
    rw [rdAmbient_map_jointSequence qStar hmem, rdAmbient_map_iidXs qStar hmem]
  have hmarg_Y : ((rdAmbient qStar).map (jointSequence iidXs iidYs 0)).map Prod.snd
      = (rdAmbient qStar).map (iidYs 0) := by
    rw [rdAmbient_map_jointSequence qStar hmem, rdAmbient_map_iidYs qStar hmem]
  refine ⟨?_, ?_⟩
  · rw [mem_jointlyTypicalSet_iff]
    refine ⟨?_, ?_, ?_⟩
    · have hxs : x ∈ stronglyTypicalSet (rdAmbient qStar) iidXs n
          ((Fintype.card (Fin k) : ℝ) * ε_join) :=
        jointStronglyTypicalSet_implies_X_stronglyTypical (rdAmbient qStar)
          iidXs iidYs measurable_iidXs measurable_iidYs hmarg_X hn hej_nn x y hxy
      exact stronglyTypicalSet_subset_typicalSet (rdAmbient qStar) iidXs
        measurable_iidXs hn hbX hxs
    · have hys : y ∈ stronglyTypicalSet (rdAmbient qStar) iidYs n
          ((Fintype.card α' : ℝ) * ε_join) :=
        jointStronglyTypicalSet_implies_Y_stronglyTypical (rdAmbient qStar)
          iidXs iidYs measurable_iidXs measurable_iidYs hmarg_Y hn hej_nn x y hxy
      exact stronglyTypicalSet_subset_typicalSet (rdAmbient qStar) iidYs
        measurable_iidYs hn hbY hys
    · have hzs : (fun i ↦ (x i, y i)) ∈ stronglyTypicalSet (rdAmbient qStar)
          (jointSequence iidXs iidYs) n ε_join := hxy
      exact stronglyTypicalSet_subset_typicalSet (rdAmbient qStar)
        (jointSequence iidXs iidYs)
        (fun i ↦ measurable_jointSequence iidXs iidYs measurable_iidXs measurable_iidYs i)
        hn hbJ hzs
  · show blockDistortion d' n x y
        ≤ expectedJointDistortion (rdAmbient qStar) (iidXs 0) (iidYs 0) d' + δ_typ
    rw [expectedJointDistortion_rdAmbient qStar hmem d']
    set z : Fin n → α' × Fin k := fun i ↦ (x i, y i) with hz_def
    set g : α' × Fin k → ℝ := fun p ↦ ((d' p.1 p.2 : NNReal) : ℝ) with hg_def
    have hz_typ : ∀ p, |(typeCount z p : ℝ) / n - qStar p| ≤ ε_join := by
      intro p
      have hzmem : z ∈ stronglyTypicalSet (rdAmbient qStar)
          (jointSequence iidXs iidYs) n ε_join := hxy
      rw [mem_stronglyTypicalSet_iff] at hzmem
      have hlaw : ((rdAmbient qStar).map (jointSequence iidXs iidYs 0)).real {p}
          = qStar p := by
        rw [rdAmbient_map_jointSequence qStar hmem]
        exact pmfToMeasure_real_singleton hmem p
      rw [← hlaw]; exact hzmem p
    have hbd : blockDistortion d' n x y
        = (1 / (n : ℝ)) * ∑ p, (typeCount z p : ℝ) * g p := by
      unfold blockDistortion
      congr 1
      show ∑ i, g (z i) = ∑ p, (typeCount z p : ℝ) * g p
      have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          z i ∈ (Finset.univ : Finset (α' × Fin k)) := fun i _ ↦ Finset.mem_univ _
      have h := Finset.sum_fiberwise_of_maps_to'
        (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset (α' × Fin k))) h_maps g
      rw [← h]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    have h_edp : expectedDistortionPmf d' qStar = ∑ p, qStar p * g p := by
      unfold expectedDistortionPmf
      rw [Fintype.sum_prod_type]
    rw [hbd, h_edp, Finset.mul_sum]
    have hkey : ∀ p, (1 / (n : ℝ)) * ((typeCount z p : ℝ) * g p) - qStar p * g p
        ≤ ε_join * g p := by
      intro p
      have hg : 0 ≤ g p := NNReal.coe_nonneg _
      have hrw : (1 / (n : ℝ)) * ((typeCount z p : ℝ) * g p) - qStar p * g p
          = ((typeCount z p : ℝ) / n - qStar p) * g p := by ring
      rw [hrw]
      calc ((typeCount z p : ℝ) / n - qStar p) * g p
          ≤ |(typeCount z p : ℝ) / n - qStar p| * g p :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hg
        _ ≤ ε_join * g p := mul_le_mul_of_nonneg_right (hz_typ p) hg
    have hstep : ∑ p, (1 / (n : ℝ)) * ((typeCount z p : ℝ) * g p)
        - ∑ p, qStar p * g p ≤ ε_join * ∑ p, g p := by
      rw [← Finset.sum_sub_distrib]
      calc ∑ p, ((1 / (n : ℝ)) * ((typeCount z p : ℝ) * g p) - qStar p * g p)
          ≤ ∑ p, ε_join * g p := Finset.sum_le_sum fun p _ ↦ hkey p
        _ = ε_join * ∑ p, g p := by rw [← Finset.mul_sum]
    linarith [hstep, hdist]

set_option maxHeartbeats 800000 in
open ChannelCoding in
/-- **(C) Rate-distortion covering layer.** For a strictly positive joint pmf
`qStar` on `α' × Fin k` with `mutualInfoPmf qStar < R₁` and a proxy distortion `d'`
feasible at `D`, the rate-distortion achievability theorem yields, for all large
block lengths `n`, a lossy code with `≥ ⌈exp(n R₁)⌉` codewords whose expected block
distortion (under the `rdAmbient`-pushed source) is within `D + ε'`.

The full support `hpos` is a regularity precondition (the covering theorem's
`hqStar_pos`); the rate-distortion slack quintet (`ε_X … δ_typ`, `qZ_min`) is
constructed in the body, not exposed. The reconciliation between the covering proxy
`d'` (X↔U) and the Wyner–Ziv distortion (X↔γ) stays load-bearing in the body / (BD),
never bundled into a predicate. -/
private lemma wz_covering_lossyCode_exists
    {k : ℕ} [Nonempty (Fin k)] {α' : Type*} [Fintype α'] [DecidableEq α']
    [Nonempty α'] [MeasurableSpace α'] [MeasurableSingletonClass α']
    (qStar : α' × Fin k → ℝ) (hpos : ∀ p, 0 < qStar p)
    (hmem : qStar ∈ stdSimplex ℝ (α' × Fin k)) (d' : DistortionFn α' (Fin k))
    {R₁ D : ℝ} (hI : mutualInfoPmf qStar < R₁)
    (hfeas : expectedDistortionPmf d' qStar ≤ D) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : ℕ, Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M ∧
      ∃ c : LossyCode M n α' (Fin k),
        c.expectedBlockDistortion ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) d' ≤ D + ε' := by
  classical
  haveI hμprob : IsProbabilityMeasure (rdAmbient qStar) :=
    rdAmbient_isProbabilityMeasure qStar hmem
  -- The feasible pmf lies in the rate-distortion constraint set with `P_X := marginalFst qStar`.
  have hmemRD : qStar ∈ RDConstraint (marginalFst qStar) d' D := ⟨hmem, rfl, hfeas⟩
  -- Nonnegative constants from the ambient log-sum and the distortion table.
  set Lx : ℝ := logSumAbs (rdAmbient qStar) iidXs with hLx_def
  set Ly : ℝ := logSumAbs (rdAmbient qStar) iidYs with hLy_def
  set Lj : ℝ := logSumAbs (rdAmbient qStar) (jointSequence iidXs iidYs) with hLj_def
  have hLx_nn : 0 ≤ Lx := logSumAbs_nonneg _ _
  have hLy_nn : 0 ≤ Ly := logSumAbs_nonneg _ _
  have hLj_nn : 0 ≤ Lj := logSumAbs_nonneg _ _
  set Sd : ℝ := ∑ p : α' × Fin k, ((d' p.1 p.2 : NNReal) : ℝ) with hSd_def
  have hSd_nn : 0 ≤ Sd := Finset.sum_nonneg fun p _ => NNReal.coe_nonneg _
  set cA : ℝ := (Fintype.card α' : ℝ) with hcA_def
  set cB : ℝ := (Fintype.card (Fin k) : ℝ) with hcB_def
  have hcA_pos : 0 < cA := by rw [hcA_def]; exact_mod_cast Fintype.card_pos
  have hcB_pos : 0 < cB := by rw [hcB_def]; exact_mod_cast Fintype.card_pos
  -- Minimal singleton mass, positive by full support.
  set qZ_min : ℝ := Finset.univ.inf' Finset.univ_nonempty qStar with hqZ_def
  have hqZ_pos : 0 < qZ_min := by
    rw [hqZ_def, Finset.lt_inf'_iff]; exact fun p _ => hpos p
  have hqZ_le : ∀ p : α' × Fin k,
      qZ_min ≤ (pmfToMeasure (α := α' × Fin k) qStar).real {p} := by
    intro p
    rw [pmfToMeasure_real_singleton hmem p, hqZ_def]
    exact Finset.inf'_le _ (Finset.mem_univ p)
  -- Rate gap and its linear/quadratic coefficients.
  set gap : ℝ := R₁ - mutualInfoPmf qStar with hgap_def
  have hgap_pos : 0 < gap := by rw [hgap_def]; linarith
  clear_value gap
  set Cc : ℝ := cA * Ly + Lx + Lj with hCc_def
  have hCc_nn : 0 ≤ Cc := by
    rw [hCc_def]; have : 0 ≤ cA * Ly := mul_nonneg hcA_pos.le hLy_nn; linarith
  clear_value Cc
  set Kk : ℝ := 8 * cA * cB / qZ_min with hKk_def
  have hKk_nn : 0 ≤ Kk := by
    rw [hKk_def]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcA_pos.le) hcB_pos.le) hqZ_pos.le
  -- The slack quintet: choose everything small against the rate gap and `ε'`.
  have hden1 : 0 < 2 * (Cc + Kk + 1) := by nlinarith [hCc_nn, hKk_nn]
  have hden2 : 0 < 2 * (Sd + 1) := by nlinarith [hSd_nn]
  set ε_join : ℝ :=
    min 1 (min (gap / (2 * (Cc + Kk + 1))) (ε' / (2 * (Sd + 1)))) with hej_def
  have hej_pos : 0 < ε_join := by
    rw [hej_def]
    exact lt_min one_pos (lt_min (div_pos hgap_pos hden1) (div_pos hε' hden2))
  have hej_le1 : ε_join ≤ 1 := by rw [hej_def]; exact min_le_left _ _
  have hej_le_gap : ε_join ≤ gap / (2 * (Cc + Kk + 1)) := by
    rw [hej_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hej_le_eps : ε_join ≤ ε' / (2 * (Sd + 1)) := by
    rw [hej_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  clear_value Kk ε_join
  set ε_X : ℝ := ε_join / 2 with hex_def
  have hex_pos : 0 < ε_X := by rw [hex_def]; linarith
  have hex_lt_ej : ε_X < ε_join := by rw [hex_def]; linarith
  have hex_le1 : ε_X ≤ 1 := by rw [hex_def]; linarith
  clear_value ε_X
  set δ_typ : ℝ := ε' / 2 with hdtyp_def
  have hdtyp_nn : 0 ≤ δ_typ := by rw [hdtyp_def]; linarith
  set ε_dist : ℝ := cB * ε_join * Lx + cA * ε_join * Ly + ε_join * Lj + 1 with hed_def
  have hed_pos : 0 < ε_dist := by
    rw [hed_def]
    have h1 : 0 ≤ cB * ε_join * Lx := by
      exact mul_nonneg (mul_nonneg hcB_pos.le hej_pos.le) hLx_nn
    have h2 : 0 ≤ cA * ε_join * Ly := by
      exact mul_nonneg (mul_nonneg hcA_pos.le hej_pos.le) hLy_nn
    have h3 : 0 ≤ ε_join * Lj := mul_nonneg hej_pos.le hLj_nn
    linarith
  set δ_kl : ℝ := Kk * ε_X ^ 2 with hdkl_def
  have hdkl_pos : 0 < δ_kl := by
    rw [hdkl_def, hKk_def]
    have hnum : 0 < 8 * cA * cB :=
      mul_pos (mul_pos (by norm_num) hcA_pos) hcB_pos
    positivity
  -- Numeric obligations of the covering theorem.
  have h_rategap : mutualInfoPmf qStar
      + (cA * ε_X * Ly + ε_X * Lx + ε_X * Lj + δ_kl) < R₁ := by
    have hlin : cA * ε_X * Ly + ε_X * Lx + ε_X * Lj = ε_X * Cc := by
      rw [hCc_def]; ring
    have hdkl_le : δ_kl ≤ Kk * ε_X := by
      rw [hdkl_def]; nlinarith [hKk_nn, hex_pos.le, hex_le1]
    have hεX_le : ε_X * (2 * (Cc + Kk + 1)) ≤ gap :=
      (le_div_iff₀ hden1).mp (le_trans hex_lt_ej.le hej_le_gap)
    have hkey : ε_X * Cc + δ_kl < gap := by
      nlinarith [hdkl_le, hεX_le, hex_pos, hCc_nn, hKk_nn]
    rw [hlin]
    linarith [hkey, hgap_def]
  have h_slack : expectedDistortionPmf d' qStar + δ_typ ≤ D + ε' / 2 := by
    rw [hdtyp_def]; linarith
  have h_distslack : ε_join * Sd ≤ δ_typ := by
    rw [hdtyp_def]
    have h1 : ε_join * (2 * (Sd + 1)) ≤ ε' := (le_div_iff₀ hden2).mp hej_le_eps
    nlinarith [hej_pos.le, hSd_nn, h1]
  have h_dominates : 8 * cA * cB * ε_X ^ 2 ≤ δ_kl * qZ_min := by
    have hne : qZ_min ≠ 0 := ne_of_gt hqZ_pos
    have hKq : Kk * qZ_min = 8 * cA * cB := by
      rw [hKk_def]; exact div_mul_cancel₀ _ hne
    have heq : δ_kl * qZ_min = 8 * cA * cB * ε_X ^ 2 := by
      rw [hdkl_def, mul_right_comm, hKq]
    exact le_of_eq heq.symm
  -- Strong-typicality ⟹ distortion-typicality bridge: the three axis slacks fit
  -- under `ε_dist` and the distortion drift under `δ_typ`, then delegate.
  have hbX : (Fintype.card (Fin k) : ℝ) * ε_join * Lx < ε_dist := by
    rw [hed_def]
    have h2 : 0 ≤ cA * ε_join * Ly := mul_nonneg (mul_nonneg hcA_pos.le hej_pos.le) hLy_nn
    have h3 : 0 ≤ ε_join * Lj := mul_nonneg hej_pos.le hLj_nn
    nlinarith [h2, h3]
  have hbY : (Fintype.card α' : ℝ) * ε_join * Ly < ε_dist := by
    rw [hed_def]
    have h1 : 0 ≤ cB * ε_join * Lx := mul_nonneg (mul_nonneg hcB_pos.le hej_pos.le) hLx_nn
    have h3 : 0 ≤ ε_join * Lj := mul_nonneg hej_pos.le hLj_nn
    nlinarith [h1, h3]
  have hbJ : ε_join * Lj < ε_dist := by
    rw [hed_def]
    have h1 : 0 ≤ cB * ε_join * Lx := mul_nonneg (mul_nonneg hcB_pos.le hej_pos.le) hLx_nn
    have h2 : 0 ≤ cA * ε_join * Ly := mul_nonneg (mul_nonneg hcA_pos.le hej_pos.le) hLy_nn
    nlinarith [h1, h2]
  have h_jts : ∀ {n : ℕ}, 0 < n → ∀ (x : Fin n → α') (y : Fin n → Fin k),
      (x, y) ∈ jointStronglyTypicalSet (rdAmbient qStar) iidXs iidYs n ε_join →
      (x, y) ∈ distortionTypicalSet (rdAmbient qStar) iidXs iidYs d' n ε_dist δ_typ :=
    fun {n} hn x y hxy =>
      wz_jointStronglyTypical_mem_distortionTypical qStar hmem d' hej_pos.le
        hbX hbY hbJ h_distslack hn x y hxy
  -- Apply the rate-distortion covering theorem and repackage its conclusion.
  clear_value ε_dist δ_kl δ_typ qZ_min
  obtain ⟨N, hN⟩ := rate_distortion_achievability (marginalFst qStar) d'
    qStar hmemRD hpos hI hε' ε_X ε_join ε_dist δ_kl δ_typ
    hex_pos hej_pos hed_pos hdkl_pos hdtyp_nn hex_lt_ej h_rategap h_slack
    h_distslack (fun {n} hn x y hxy => h_jts hn x y hxy) qZ_min hqZ_pos hqZ_le
    h_dominates
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, hM_lb, c, hc⟩ := hN n hn
  exact ⟨M, hM_lb, c, hc⟩

/-- **Covering-distortion reconciliation identity (Step 1–2 core).** The covering
proxy distortion `d'` on the source-support subtype `α' := {x // 0 < P_X x}`,
defined as the `Y`-conditional expectation
`d'(⟨x, _⟩, u) := ∑_y (P_XY(x,y) / P_X x) · d(x, f(u, y))`, reconciles with the
Wyner–Ziv distortion functional: for the restricted `(X, U)`-joint
`qStar(⟨x, _⟩, u) := κ'(x, u) · P_X x`, the pmf-form expected distortion of `d'`
equals the Wyner–Ziv expected distortion of the factorisable joint
`q'(x, y, u) := κ'(x, u) · P_XY(x, y)` under the reconstruction `f`.

The identity is the load-bearing bridge that lets the rate-distortion covering
theorem (which measures distortion `X ↔ U` via `d'`) discharge the Wyner–Ziv
feasibility (`X ↔ γ` via `f`). It holds because `P_X x · (P_XY(x,y) / P_X x) =
P_XY(x,y)` on the support (where `P_X x > 0`), and the zero atoms of `P_X`
contribute nothing on either side (`q'` vanishes there since every `P_XY(x,y) = 0`
when `P_X x = 0`).
@audit:ok -/
private lemma wz_coveringDistortion_reconcile
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) {k : ℕ}
    (κ' : α → Fin k → ℝ) (f : Fin k × β → γ) :
    expectedDistortionPmf
        (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (u : Fin k) =>
          Real.toNNReal (∑ y : β, (P_XY.real {(x'.1, y)} / ∑ y' : β, P_XY.real {(x'.1, y')})
              * ((d x'.1 (f (u, y)) : NNReal) : ℝ)))
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k =>
          κ' p.1.1 p.2 * ∑ y : β, P_XY.real {(p.1.1, y)})
      = wzExpectedDistortion (Fin k) (fun a b ↦ (d a b : ℝ))
          (fun p : α × β × Fin k => κ' p.1 p.2.2 * P_XY.real {(p.1, p.2.1)}) f := by
  classical
  -- The full-alphabet per-source-symbol inner double sum.
  set G : α → ℝ := fun x =>
    ∑ y : β, ∑ u : Fin k, κ' x u * P_XY.real {(x, y)} * ((d x (f (u, y)) : NNReal) : ℝ)
    with hG
  have hPnn : ∀ x : α, 0 ≤ ∑ y, P_XY.real {(x, y)} :=
    fun x => Finset.sum_nonneg fun y _ => measureReal_nonneg
  -- RHS = ∑ x : α, G x.
  have hRHS : wzExpectedDistortion (Fin k) (fun a b ↦ (d a b : ℝ))
      (fun p : α × β × Fin k => κ' p.1 p.2.2 * P_XY.real {(p.1, p.2.1)}) f
      = ∑ x : α, G x := by
    unfold wzExpectedDistortion
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
  -- LHS = ∑ a : α', G a.1.
  have hLHS : expectedDistortionPmf
      (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (u : Fin k) =>
        Real.toNNReal (∑ y : β, (P_XY.real {(x'.1, y)} / ∑ y' : β, P_XY.real {(x'.1, y')})
            * ((d x'.1 (f (u, y)) : NNReal) : ℝ)))
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k =>
        κ' p.1.1 p.2 * ∑ y : β, P_XY.real {(p.1.1, y)})
      = ∑ a : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}, G a.1 := by
    unfold expectedDistortionPmf
    refine Finset.sum_congr rfl fun a _ => ?_
    have hPxpos : 0 < ∑ y : β, P_XY.real {(a.1, y)} := a.2
    have hPxne : (∑ y : β, P_XY.real {(a.1, y)}) ≠ 0 := ne_of_gt hPxpos
    simp only [hG]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Real.coe_toNNReal _
      (Finset.sum_nonneg fun y _ =>
        mul_nonneg (div_nonneg measureReal_nonneg hPxpos.le) (NNReal.coe_nonneg _))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    field_simp
  -- Extend the support-subtype sum back to the full alphabet (zero atoms of `P_X`
  -- contribute nothing: `q'` vanishes there).
  have hGzero : ∀ x : α, (∑ y, P_XY.real {(x, y)}) = 0 → G x = 0 := by
    intro x hx
    simp only [hG]
    refine Finset.sum_eq_zero fun y _ => ?_
    have hxy : P_XY.real {(x, y)} = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun y' _ => measureReal_nonneg)).mp hx y
        (Finset.mem_univ y)
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [hxy]; ring
  have hext : (∑ a : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}, G a.1) = ∑ x : α, G x := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun x => 0 < ∑ y, P_XY.real {(x, y)}))
          (fun x => by simp) G]
    exact Finset.sum_subset (Finset.filter_subset _ _)
      (fun x _ hx => hGzero x (le_antisymm (not_lt.mp (by simpa using hx)) (hPnn x)))
  rw [hLHS, hext, hRHS]

open ChannelCoding in
/-- **(Steps 1–2) Covering LossyCode family from a feasible test channel.**
Perturbs the feasible factorisable test channel `qf` to a full-support kernel
`κ'` (Step 1, `wz_fullKernelSupport_perturbation`), restricts the covering source
to the support subtype `α' := {x // 0 < P_X x}`, and produces the rate-distortion
covering LossyCode family (Step 2, `wz_covering_lossyCode_exists`) for the proxy
distortion `d'` (the `Y`-conditional expectation of `d ∘ qf.2`).

The output packages, for downstream binning (Steps 3–7), the perturbed full-support
factorisable joint `q'` (with kernel `κ'`), the restricted covering joint `qStar`,
the covering proxy `d'`, the Wyner–Ziv objective margin `< R`, and — for every
covering rate `R₁` strictly above the covering mutual information
`mutualInfoPmf qStar` — the covering LossyCode family with block distortion within
`(D + δ) + ε'`. The covering-distortion feasibility `expectedDistortionPmf d' qStar
≤ D + δ` is the reconciliation identity (`wz_coveringDistortion_reconcile`) applied
to the perturbation's distortion bound. All conclusions are genuinely constructed;
the only preconditions are feasibility (`hqf`), the objective margin (`hobj`), and
the slack `δ`.
@audit:ok -/
private lemma wz_coveringFamily_of_testChannel
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
    (hobj : wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 < R)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (q' : α × β × Fin k → ℝ) (κ' : α → Fin k → ℝ)
      (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
      (d' : DistortionFn {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)),
        (∀ x y u, q' (x, y, u) = κ' x u * P_XY.real {(x, y)})
        ∧ (∀ x u, 0 < κ' x u)
        ∧ (∀ x, ∑ u, κ' x u = 1)
        ∧ (wzMutualInfoXU (Fin k) q' - wzMutualInfoYU (Fin k) q' < R)
        ∧ (∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
        ∧ (∀ p, 0 < qStar p)
        ∧ qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k)
        ∧ expectedDistortionPmf d' qStar ≤ D + δ
        ∧ (∀ R₁ : ℝ, mutualInfoPmf qStar < R₁ → ∀ ε' : ℝ, 0 < ε' →
            ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : ℕ,
              Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M ∧
              ∃ c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k),
                c.expectedBlockDistortion
                    ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) d'
                  ≤ (D + δ) + ε') := by
  classical
  -- Step 1: perturb the feasible test channel to a full-support kernel `κ'`.
  rw [mem_WynerZivFactorizableConstraint_iff] at hqf
  obtain ⟨hfact, hdist⟩ := hqf
  haveI : Nonempty (Fin k) := wz_nonempty_of_factorizable hfact
  obtain ⟨q', κ', hq'eq, hκ'pos, hκ'sum, _hfact', hobj', hdist'⟩ :=
    wz_fullKernelSupport_perturbation (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D
      hfact hdist hobj hδ
  -- Restricted covering joint (S1): full support + simplex on the source-support subtype.
  obtain ⟨hne, hqStar_pos, hqStar_mem⟩ :=
    wz_restrictedCoveringJoint_pos P_XY κ' hκ'pos hκ'sum
  haveI : Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}} := hne
  -- The perturbed joint, packaged as a clean pointwise identity.
  have hq'clean : ∀ p : α × β × Fin k, q' p = κ' p.1 p.2.2 * P_XY.real {(p.1, p.2.1)} :=
    fun p => hq'eq p.1 p.2.1 p.2.2
  have hconv :
      (fun p : α × β × Fin k => κ' p.1 p.2.2 * P_XY.real {(p.1, p.2.1)}) = q' := by
    funext p; exact (hq'clean p).symm
  -- Covering-distortion feasibility via the reconciliation identity (Step 1–2 core).
  have hfeas : expectedDistortionPmf
      (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (u : Fin k) =>
        Real.toNNReal (∑ y : β, (P_XY.real {(x'.1, y)} / ∑ y' : β, P_XY.real {(x'.1, y')})
            * ((d x'.1 (qf.2 (u, y)) : NNReal) : ℝ)))
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k =>
        κ' p.1.1 p.2 * ∑ y : β, P_XY.real {(p.1.1, y)}) ≤ D + δ := by
    rw [wz_coveringDistortion_reconcile P_XY d κ' qf.2, hconv]
    exact hdist'
  -- Step 2: assemble the covering LossyCode family from the covering theorem (C).
  refine ⟨q', κ',
    (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k =>
      κ' p.1.1 p.2 * ∑ y : β, P_XY.real {(p.1.1, y)}),
    (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (u : Fin k) =>
      Real.toNNReal (∑ y : β, (P_XY.real {(x'.1, y)} / ∑ y' : β, P_XY.real {(x'.1, y')})
          * ((d x'.1 (qf.2 (u, y)) : NNReal) : ℝ))),
    hq'eq, hκ'pos, hκ'sum, hobj', fun _ => rfl, hqStar_pos, hqStar_mem, hfeas, ?_⟩
  intro R₁ hI ε' hε'
  exact wz_covering_lossyCode_exists
    (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k =>
      κ' p.1.1 p.2 * ∑ y : β, P_XY.real {(p.1.1, y)})
    hqStar_pos hqStar_mem
    (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (u : Fin k) =>
      Real.toNNReal (∑ y : β, (P_XY.real {(x'.1, y)} / ∑ y' : β, P_XY.real {(x'.1, y')})
          * ((d x'.1 (qf.2 (u, y)) : NNReal) : ℝ)))
    hI hfeas hε'

/-! ### Steps 3–7 decomposition (binning / decoder / error exponents / squeeze)

The covering data of Steps 1–2 (`wz_coveringFamily_of_testChannel`) is consumed by
the binning + decoder leg. This leg is decomposed into:

* **S3** `wzCodeOfCoveringBinning` — the Wyner–Ziv code assembled from a covering
  codebook, a binning of the covering index, and a bin/side-information decoder
  (pure def).
* **S4** `wzBinTypicalDecoder` (+ uniqueness `wzBinTypicalDecoder_eq_of_unique`) —
  the bin-restricted conditional-typicality decoder, searching a bin's covering
  **codebook members** for the one jointly typical with `Y^n` (pure def + the
  decoder equation under a unique witness), mirroring Slepian–Wolf
  `swJointTypicalDecoder` / `swJointTypicalDecoder_eq_of_unique`.
* **S5a** `wz_covering_failure_prob_le` — covering-failure exponent (E1).
* **S5b** `wz_codebook_confusion_expectation_le` — codebook-restricted decoder
  confusion exponent (E2, the crux).
* **S6** `wz_perDelta_covering_binning` — the capstone consuming the covering data
  and producing the per-slack code family (binning + decoder + error exponents +
  derandomize + squeeze + source extension).
* **S7** `wzLiftSupportCode` — the source-extension lift `α' → α` (pure def), used
  together with the sorry-free `wz_expectedBlockDistortion_source_agree`.
-/

/-- **(S3) Wyner–Ziv code from a covering codebook + binning + bin decoder.**
The encoder covers the source with the covering codebook (`c₁.encoder`) and bins
the covering index (`f`). The decoder reconstructs `γ^n` letterwise via `rec`
(the test-channel decoder `qf.2 : Fin k × β → γ`) from the bin decoder's word
`dec (m, y) : Fin n → Fin k` and the side information `y`. Pure assembly; the
covering codebook `c₁`, the binning `f`, the reconstruction map `rec` and the bin
decoder `dec` are all supplied. -/
def wzCodeOfCoveringBinning {α' : Type*} [MeasurableSpace α'] {k M M₁ n : ℕ}
    (c₁ : LossyCode M₁ n α' (Fin k)) (f : Fin M₁ → Fin M)
    (rec : Fin k × β → γ)
    (dec : Fin M × (Fin n → β) → (Fin n → Fin k)) :
    WynerZivCode M n α' β γ where
  encoder := fun x ↦ f (c₁.encoder x)
  decoder := fun my ↦ fun i ↦ rec (dec my i, my.2 i)

/-- **(S4) Bin/side-information conditional-typicality decoder.** Given a bin `m`
and side information `y`, search the bin's covering **codebook members**
`{c₁.decoder m' | f m' = m}` for the unique word jointly typical with `y`, returning
that `Fin n → Fin k` word (falling back to an arbitrary word if none exists or the
witness is not unique). The search ranges over codebook members only (indexed by the
covering index `m'`), not over all `Fin n → Fin k` words — this restriction is what
makes the decoder-confusion event (S5b) achievable at the Wyner–Ziv rate. Mirror of
Slepian–Wolf `swJointTypicalDecoder`. -/
noncomputable def wzBinTypicalDecoder {α' : Type*} [MeasurableSpace α']
    {Ω : Type*} [MeasurableSpace Ω] {k M M₁ n : ℕ} [Nonempty (Fin k)]
    (μ : Measure Ω) (Us : ℕ → Ω → Fin k) (Ys : ℕ → Ω → β) (ε : ℝ)
    (c₁ : LossyCode M₁ n α' (Fin k)) (f : Fin M₁ → Fin M) :
    Fin M × (Fin n → β) → (Fin n → Fin k) := fun my ↦
  haveI : Decidable (∃! u : Fin n → Fin k,
      (∃ m' : Fin M₁, f m' = my.1 ∧ c₁.decoder m' = u)
        ∧ (u, my.2) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε) :=
    Classical.propDecidable _
  if h : ∃! u : Fin n → Fin k,
      (∃ m' : Fin M₁, f m' = my.1 ∧ c₁.decoder m' = u)
        ∧ (u, my.2) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε
    then Classical.choose h.exists
    else Classical.arbitrary _

/-- If the covering codeword `c₁.decoder m₁` is jointly typical with `y` and is the
unique bin-`f m₁` codebook member so typical, then `wzBinTypicalDecoder` recovers it.
Mirror of `swJointTypicalDecoder_eq_of_unique`. -/
lemma wzBinTypicalDecoder_eq_of_unique {α' : Type*} [MeasurableSpace α']
    {Ω : Type*} [MeasurableSpace Ω] {k M M₁ n : ℕ} [Nonempty (Fin k)]
    (μ : Measure Ω) (Us : ℕ → Ω → Fin k) (Ys : ℕ → Ω → β) (ε : ℝ)
    (c₁ : LossyCode M₁ n α' (Fin k)) (f : Fin M₁ → Fin M)
    {m₁ : Fin M₁} {y : Fin n → β}
    (htrue : (c₁.decoder m₁, y) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε)
    (hunique : ∀ u : Fin n → Fin k,
        (∃ m' : Fin M₁, f m' = f m₁ ∧ c₁.decoder m' = u) →
        (u, y) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε →
        u = c₁.decoder m₁) :
    wzBinTypicalDecoder μ Us Ys ε c₁ f (f m₁, y) = c₁.decoder m₁ := by
  have hExUnique : ∃! u : Fin n → Fin k,
      (∃ m' : Fin M₁, f m' = f m₁ ∧ c₁.decoder m' = u)
        ∧ (u, y) ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε := by
    refine ⟨c₁.decoder m₁, ⟨⟨m₁, rfl, rfl⟩, htrue⟩, ?_⟩
    intro u hu
    exact hunique u hu.1 hu.2
  unfold wzBinTypicalDecoder
  rw [dif_pos hExUnique]
  have hch_spec :
      (∃ m' : Fin M₁, f m' = f m₁
          ∧ c₁.decoder m' = Classical.choose hExUnique.exists)
        ∧ (Classical.choose hExUnique.exists, y)
            ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε :=
    Classical.choose_spec hExUnique.exists
  exact hunique (Classical.choose hExUnique.exists) hch_spec.1 hch_spec.2

/-- **(S5a) Covering-failure exponent (E1).** The codebook-averaged probability
that a strongly-typical source `x` finds **no** covering codeword jointly typical
with it decays doubly-exponentially: `∫ x, (1 − p_typ x)^{M₁} ≤ exp(−M₁ · exp(−n(I +
δ)))`, where `p_typ x` is the per-codeword conditional-typicality mass (bounded below
by `exp(−n(I + δ))` via `wz_covering_sideInfo_mass_ge`), passed here as `hmass`.

`hmass` is the per-source covering-acceptance mass lower bound `exp(−n(I+δ)) ≤ p_typ x`.
With it, `(1−p)^M₁ ≤ e^{−M₁ p} ≤ e^{−M₁·exp(−n(I+δ))}` pointwise (`p_typ x ∈ [0,1]`,
`p ≥ exp(−n(I+δ))`), then integrate over the probability measure `P_X`. The pointwise
`p_typ x ≤ 1` holds even without measurability of `Us 0`: `μ.map (Us 0)` is a
sub-probability measure (`Measure.isFiniteMeasure_map` + `map` mass `≤ 1`), so its
product `Measure.pi` is a sub-probability measure (`Measure.pi_univ`), and the mass of
any set is `≤ 1`. The `(1−t)^M ≤ e^{−Mt}` step reuses `one_sub_pow_le_exp_neg_mul`.
@audit:ok (leg-17, sorryAx-free: `#print axioms` = `[propext, Classical.choice,
Quot.sound]`, orchestrator-verified after independent signature audit confirmed the
`hmass`-corrected statement non-vacuous). -/
lemma wz_covering_failure_prob_le {α' : Type*}
    [Fintype α'] [DecidableEq α'] [Nonempty α']
    [MeasurableSpace α'] [MeasurableSingletonClass α']
    {Ω : Type*} [MeasurableSpace Ω] {k n M₁ : ℕ} [Nonempty (Fin k)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α') (Us : ℕ → Ω → Fin k) (ε : ℝ)
    (P_X : Measure (Fin n → α')) [IsProbabilityMeasure P_X]
    (I δ : ℝ)
    (hmass : ∀ x : Fin n → α', Real.exp (-(n : ℝ) * (I + δ)) ≤
        (Measure.pi fun _ : Fin n ↦ μ.map (Us 0)).real
          {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) :
    ∫ x, (1 - (Measure.pi fun _ : Fin n ↦ μ.map (Us 0)).real
              {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁ ∂P_X
      ≤ Real.exp (-(M₁ : ℝ) * Real.exp (-(n : ℝ) * (I + δ))) := by
  set ν : Measure (Fin n → Fin k) := Measure.pi fun _ : Fin n ↦ μ.map (Us 0) with hν
  -- The map of the probability measure `μ` is a finite (sub-probability) measure,
  -- irrespective of whether `Us 0` is measurable.
  haveI hfin : IsFiniteMeasure (μ.map (Us 0)) := Measure.isFiniteMeasure_map μ (Us 0)
  have hfac : (μ.map (Us 0)) Set.univ ≤ 1 := by
    by_cases hae : AEMeasurable (Us 0) μ
    · rw [Measure.map_apply_of_aemeasurable hae MeasurableSet.univ]; simp
    · rw [Measure.map_of_not_aemeasurable hae]; simp
  -- Hence the product measure `ν` is a sub-probability measure.
  have hν_univ : ν Set.univ ≤ 1 := by
    rw [hν, Measure.pi_univ]
    exact Finset.prod_le_one' (fun _ _ ↦ hfac)
  -- The per-source covering mass lies in `[0, 1]`.
  have h1 : ∀ x : Fin n → α',
      ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε} ≤ 1 := by
    intro x
    have hle : ν {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε} ≤ 1 :=
      le_trans (measure_mono (Set.subset_univ _)) hν_univ
    calc ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}
        = (ν {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}).toReal := rfl
      _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) hle
      _ = 1 := by simp
  -- Pointwise doubly-exponential bound to the constant right-hand side.
  have hbound : ∀ x : Fin n → α',
      (1 - ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁
        ≤ Real.exp (-(M₁ : ℝ) * Real.exp (-(n : ℝ) * (I + δ))) := by
    intro x
    have h0 : 0 ≤ ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε} :=
      measureReal_nonneg
    have step1 :
        (1 - ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁
          ≤ Real.exp (-(M₁ : ℝ) *
              ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) :=
      one_sub_pow_le_exp_neg_mul M₁ h0 (h1 x)
    have step2 :
        Real.exp (-(M₁ : ℝ) *
            ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε})
          ≤ Real.exp (-(M₁ : ℝ) * Real.exp (-(n : ℝ) * (I + δ))) := by
      apply Real.exp_le_exp.mpr
      have hM₁ : (0 : ℝ) ≤ (M₁ : ℝ) := Nat.cast_nonneg _
      nlinarith [hmass x, hM₁]
    exact le_trans step1 step2
  -- Integrability of the (bounded, finitely-supported-domain) integrand.
  have h_int : Integrable (fun x : Fin n → α' ↦
      (1 - ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁) P_X := by
    have h_meas : Measurable (fun x : Fin n → α' ↦
        (1 - ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁) :=
      measurable_of_finite _
    refine Integrable.mono' (g := fun _ ↦
        Real.exp (-(M₁ : ℝ) * Real.exp (-(n : ℝ) * (I + δ))))
      (integrable_const _) h_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x ↦ ?_)
    have hpow_nn : 0 ≤ (1 -
        ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁ :=
      pow_nonneg (by linarith [h1 x]) M₁
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nn]
    exact hbound x
  calc ∫ x, (1 - ν.real {u | (x, u) ∈ ChannelCoding.jointlyTypicalSet μ Xs Us n ε}) ^ M₁ ∂P_X
      ≤ ∫ _x : Fin n → α',
          Real.exp (-(M₁ : ℝ) * Real.exp (-(n : ℝ) * (I + δ))) ∂P_X :=
        integral_mono h_int (integrable_const _) hbound
    _ = Real.exp (-(M₁ : ℝ) * Real.exp (-(n : ℝ) * (I + δ))) := by
        rw [integral_const]; simp

/-- **(S5b) Codebook-restricted decoder confusion exponent (E2, the crux).** The
binning-averaged probability that some **codebook member** `c₁.decoder m'` other than
the true covering codeword shares the true bin and is jointly typical with `Y^n` is at
most `M₁ · exp(−n · I(U;Y)) · M⁻¹`.

**Crux — what a later leg must build.** Gateway atom
`wz_sideInfo_decoder_confusion_expectation_le` bins **all** `u`-sequences (giving the
count `exp(n·H(U|Y))`), which forces the achievable rate down to `H(U|Y)` — too weak
for Wyner–Ziv. This bound instead restricts the confusable set to the **covering
codebook** (`M₁ = ⌈exp(n·I(X;U))⌉` members), so the alias count is `M₁` rather than
`exp(n·H(U|Y))`. With `M = ⌈exp(n·R)⌉` bins, the bound is
`M₁ · exp(−n·I(U;Y)) / M ≈ exp(n·(I(X;U) − I(U;Y) − R))`, which vanishes precisely
when `R > I(X;U) − I(Y;U)` — the Wyner–Ziv rate. A later leg must prove this by an AEP
union bound over the (random) covering codebook members that are independent of `Y^n`,
NOT by instantiating the all-sequences gateway atom.

signature corrected leg-17: mass-bound + collision hypotheses added; conclusion now
non-vacuously follows. `hmass` is the per-codeword joint-typicality mass UPPER bound
`μ{codeword m' typical with Y^n} ≤ exp(−n·I_YU)` (the AEP bound for a covering codeword
independent of `Y^n`); `hcollision` is the binning-collision property
`binMeas{f | f m' = f m} = M⁻¹` for distinct indices, mirroring `binning_collision_prob`.
The codebook-restricted union over `m' : Fin M₁` stays in the CONCLUSION/body (NOT a
hypothesis — the E2 crux per finding #10 is the codebook restriction of the count): swap
the order of integration, bound the per-`ω` `binMeas`-slice by union bound + `hcollision`
as `M⁻¹ · #{m' typical}`, integrate over `μ`, then apply `hmass` to each of the `M₁`
codewords to get `M⁻¹ · M₁ · exp(−n·I_YU)`. The old signature's degenerate refutation
(`I_YU → +∞` with positive typical mass) is now excluded: `hmass` would force
`μ{typical} ≤ exp(−n·I_YU) → 0`, contradicting positive mass. Regularity preconditions
`hYs`/`htrueIdx` (measurability of the side-information block RV and of the covering
index) are added for the Tonelli swap; both are discharged by S6, which supplies
measurable i.i.d. RVs and a measurable covering index. -/
lemma wz_codebook_confusion_expectation_le {α' : Type*} [MeasurableSpace α']
    {Ω : Type*} [MeasurableSpace Ω] {k n M M₁ : ℕ} [Nonempty (Fin k)] [NeZero M]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Us : ℕ → Ω → Fin k) (Ys : ℕ → Ω → β) (ε : ℝ)
    (c₁ : LossyCode M₁ n α' (Fin k)) (trueIdx : Ω → Fin M₁)
    (hYs : ∀ i, Measurable (Ys i)) (htrueIdx : Measurable trueIdx)
    (binMeas : Measure (Fin M₁ → Fin M)) [IsProbabilityMeasure binMeas]
    (I_YU : ℝ)
    (hmass : ∀ m' : Fin M₁,
        μ.real {ω | (c₁.decoder m', jointRV Ys n ω)
            ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε}
          ≤ Real.exp (-(n : ℝ) * I_YU))
    (hcollision : ∀ m' m : Fin M₁, m' ≠ m →
        binMeas.real {f | f m' = f m} = (M : ℝ)⁻¹) :
    ∫ f, μ.real {ω | ∃ m' : Fin M₁,
            m' ≠ trueIdx ω
          ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω)
              ∈ ChannelCoding.jointlyTypicalSet μ Us Ys n ε}
        ∂binMeas
      ≤ (M₁ : ℝ) * Real.exp (-(n : ℝ) * I_YU) * ((M : ℝ))⁻¹ := by
  classical
  haveI : MeasurableSingletonClass (Fin M₁ → Fin M) := Pi.instMeasurableSingletonClass
  set jts : Set ((Fin n → Fin k) × (Fin n → β)) :=
    ChannelCoding.jointlyTypicalSet μ Us Ys n ε with hjts_def
  have hjts_meas : MeasurableSet jts :=
    ChannelCoding.measurableSet_jointlyTypicalSet μ Us Ys n ε
  -- Measurability of the per-codeword typicality set in `ω`.
  have hC_meas : ∀ m' : Fin M₁,
      MeasurableSet {ω | (c₁.decoder m', jointRV Ys n ω) ∈ jts} := by
    intro m'
    have hmap : Measurable (fun ω => (c₁.decoder m', jointRV Ys n ω)) :=
      measurable_const.prodMk (measurable_jointRV Ys hYs n)
    exact hmap hjts_meas
  -- Measurability of the per-`(f, m')` confusion set in `ω`.
  have hbad_meas : ∀ (f : Fin M₁ → Fin M) (m' : Fin M₁),
      MeasurableSet {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
        ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} := by
    intro f m'
    have hA : MeasurableSet {ω | m' ≠ trueIdx ω} := by
      have hpre : {ω | m' ≠ trueIdx ω} = (trueIdx ⁻¹' {m'})ᶜ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage,
          Set.mem_singleton_iff]
        exact ne_comm
      rw [hpre]; exact (htrueIdx (measurableSet_singleton m')).compl
    have hB : MeasurableSet {ω | f m' = f (trueIdx ω)} :=
      htrueIdx ((Set.toFinite {m₀ : Fin M₁ | f m' = f m₀}).measurableSet)
    exact hA.inter (hB.inter (hC_meas m'))
  -- Step D: the per-`m'` integral bound `∫ f, μ.real (confusion set) ≤ exp(−n·I_YU)·M⁻¹`.
  have hD : ∀ m' : Fin M₁,
      ∫ f, μ.real {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂binMeas
        ≤ Real.exp (-(n : ℝ) * I_YU) * ((M : ℝ))⁻¹ := by
    intro m'
    have h_nn : 0 ≤ᵐ[binMeas] fun f => μ.real {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
        ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} :=
      Filter.Eventually.of_forall fun _ => measureReal_nonneg
    have h_aesm : AEStronglyMeasurable
        (fun f => μ.real {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}) binMeas :=
      (measurable_of_finite _).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae h_nn h_aesm,
      ChannelCoding.lintegral_ofReal_measureReal_eq_lintegral_measure μ binMeas
        (fun f => {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts})]
    -- Tonelli swap over `binMeas ⊗ μ`.
    have hE_meas : MeasurableSet {q : (Fin M₁ → Fin M) × Ω |
        q.2 ∈ {ω | m' ≠ trueIdx ω ∧ q.1 m' = q.1 (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}} := by
      have h_decomp : {q : (Fin M₁ → Fin M) × Ω |
          q.2 ∈ {ω | m' ≠ trueIdx ω ∧ q.1 m' = q.1 (trueIdx ω)
            ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}}
          = ⋃ f₀ : Fin M₁ → Fin M, ({f₀} : Set (Fin M₁ → Fin M)) ×ˢ
            {ω | m' ≠ trueIdx ω ∧ f₀ m' = f₀ (trueIdx ω)
              ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} := by
        ext ⟨g, ω⟩; simp
      rw [h_decomp]
      exact MeasurableSet.iUnion fun f₀ =>
        (measurableSet_singleton f₀).prod (hbad_meas f₀ m')
    rw [ChannelCoding.lintegral_measure_swap_of_prod_measurableSet binMeas μ
      (fun f => {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
        ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}) hE_meas]
    simp only [Set.mem_setOf_eq]
    -- Per-`ω` inner bound: the `binMeas`-slice is `≤ M⁻¹` on the typical set, else `0`.
    have h_inner : ∀ ω : Ω,
        binMeas {f | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}
          ≤ ENNReal.ofReal ((M : ℝ)⁻¹) *
              Set.indicator {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts} 1 ω := by
      intro ω
      by_cases htyp : (c₁.decoder m', jointRV Ys n ω) ∈ jts
      · by_cases hidx : m' = trueIdx ω
        · have hempty : {f : Fin M₁ → Fin M | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
              ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} = ∅ := by
            ext f
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            rintro ⟨hne, -, -⟩
            exact hne hidx
          rw [hempty]; simp
        · have hset : {f : Fin M₁ → Fin M | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
              ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}
              = {f | f m' = f (trueIdx ω)} := by
            ext f
            simp only [Set.mem_setOf_eq]
            exact ⟨fun h => h.2.1, fun h => ⟨hidx, h, htyp⟩⟩
          rw [hset]
          have hmem : ω ∈ {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts} := htyp
          rw [Set.indicator_of_mem hmem]
          simp only [Pi.one_apply, mul_one]
          rw [← ofReal_measureReal (measure_ne_top binMeas {f | f m' = f (trueIdx ω)}),
            hcollision m' (trueIdx ω) hidx]
      · have hempty : {f : Fin M₁ → Fin M | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
            ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} = ∅ := by
          ext f
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨-, -, htyp'⟩
          exact htyp htyp'
        rw [hempty]; simp
    have hind_meas : Measurable
        (Set.indicator {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts} (1 : Ω → ℝ≥0∞)) :=
      measurable_const.indicator (hC_meas m')
    have h_lint_le :
        ∫⁻ ω, binMeas {f | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
            ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂μ
          ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * I_YU) * (M : ℝ)⁻¹) := by
      calc ∫⁻ ω, binMeas {f | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
              ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂μ
          ≤ ∫⁻ ω, ENNReal.ofReal ((M : ℝ)⁻¹) *
              Set.indicator {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts} 1 ω ∂μ :=
            lintegral_mono h_inner
        _ = ENNReal.ofReal ((M : ℝ)⁻¹) *
              ∫⁻ ω, Set.indicator {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts} 1 ω ∂μ :=
            lintegral_const_mul _ hind_meas
        _ = ENNReal.ofReal ((M : ℝ)⁻¹) *
              μ {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts} := by
            rw [lintegral_indicator_one (hC_meas m')]
        _ ≤ ENNReal.ofReal ((M : ℝ)⁻¹) *
              ENNReal.ofReal (Real.exp (-(n : ℝ) * I_YU)) := by
            gcongr
            calc μ {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts}
                = ENNReal.ofReal (μ.real {ω' | (c₁.decoder m', jointRV Ys n ω') ∈ jts}) :=
                  (ofReal_measureReal (measure_ne_top μ _)).symm
              _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * I_YU)) :=
                  ENNReal.ofReal_le_ofReal (hmass m')
        _ = ENNReal.ofReal (Real.exp (-(n : ℝ) * I_YU) * (M : ℝ)⁻¹) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    calc (∫⁻ ω, binMeas {f | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
            ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂μ).toReal
        ≤ (ENNReal.ofReal (Real.exp (-(n : ℝ) * I_YU) * (M : ℝ)⁻¹)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h_lint_le
      _ = Real.exp (-(n : ℝ) * I_YU) * (M : ℝ)⁻¹ :=
          ENNReal.toReal_ofReal (by positivity)
  -- Union bound over the codebook members at each hash `f`, then integrate the sum.
  have hUnion : ∀ f : Fin M₁ → Fin M,
      {ω | ∃ m' : Fin M₁, m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}
        = ⋃ m' ∈ (Finset.univ : Finset (Fin M₁)),
            {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
              ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} := by
    intro f; ext ω; simp
  have hStepA : ∀ f : Fin M₁ → Fin M,
      μ.real {ω | ∃ m' : Fin M₁, m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}
        ≤ ∑ m' : Fin M₁, μ.real {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
            ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} := by
    intro f
    rw [hUnion f]
    exact measureReal_biUnion_finset_le Finset.univ _
  have hInt_outer : Integrable (fun f => μ.real {ω | ∃ m' : Fin M₁, m' ≠ trueIdx ω
      ∧ f m' = f (trueIdx ω) ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}) binMeas :=
    Integrable.of_finite
  have hInt_sum : Integrable (fun f => ∑ m' : Fin M₁, μ.real {ω | m' ≠ trueIdx ω
      ∧ f m' = f (trueIdx ω) ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts}) binMeas :=
    Integrable.of_finite
  calc ∫ f, μ.real {ω | ∃ m' : Fin M₁, m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂binMeas
      ≤ ∫ f, ∑ m' : Fin M₁, μ.real {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂binMeas :=
        integral_mono hInt_outer hInt_sum hStepA
    _ = ∑ m' : Fin M₁, ∫ f, μ.real {ω | m' ≠ trueIdx ω ∧ f m' = f (trueIdx ω)
          ∧ (c₁.decoder m', jointRV Ys n ω) ∈ jts} ∂binMeas :=
        integral_finsetSum Finset.univ fun _ _ => Integrable.of_finite
    _ ≤ ∑ _m' : Fin M₁, Real.exp (-(n : ℝ) * I_YU) * ((M : ℝ))⁻¹ :=
        Finset.sum_le_sum fun m' _ => hD m'
    _ = (M₁ : ℝ) * Real.exp (-(n : ℝ) * I_YU) * ((M : ℝ))⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **(S7) Source-extension lift `α' → α`.** Lift a Wyner–Ziv code over the source
support subtype `α' := {x // 0 < P_X x}` to a code over the full alphabet `α`, using
the default support element `x₀` for out-of-support coordinates (which have zero
`Measure.pi P_XY`-mass, so the lift preserves expected block distortion via
`wz_expectedBlockDistortion_source_agree`). The decoder is unchanged (it does not
touch `α`). Pure def. -/
noncomputable def wzLiftSupportCode
    (P_XY : Measure (α × β)) {M n : ℕ}
    (x₀ : {x : α // 0 < ∑ y, P_XY.real {(x, y)}})
    (cSupp : WynerZivCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} β γ) :
    WynerZivCode M n α β γ where
  encoder := fun x ↦ cSupp.encoder (fun i ↦
    haveI := Classical.propDecidable (0 < ∑ y, P_XY.real {(x i, y)})
    if h : 0 < ∑ y, P_XY.real {(x i, y)} then ⟨x i, h⟩ else x₀)
  decoder := cSupp.decoder

/-- **(S6) Covering + binning capstone (Steps 3–7).** Consuming the Step 1–2 covering
data (the full-support factorisable joint `q'` with kernel `κ'`, the restricted
covering joint `qStar`, the covering proxy distortion `d'`, the covering feasibility
`hfeas`, and the covering `LossyCode` family `hcov`), assemble the per-slack Wyner–Ziv
code family at the operational rate `R`: bin the covering index down to
`codebookSize R n` messages, decode by the bin conditional-typicality search (S3/S4),
bound the covering-failure (S5a) and codebook-restricted decoder-confusion (S5b) error
events, extract a good deterministic codebook + binning by double derandomization
(`exists_codebook_low_avg` / `exists_pair_le_of_binning_integral_le`), squeeze the
residual distortion excess to `0` (`source_avg_distortion_le_simpler`,
`ceil_exp_mul_exp_neg_tendsto_atTop`), and extend the covering code `α' → α`
(`wzLiftSupportCode` + `wz_expectedBlockDistortion_source_agree`).

All hypotheses are genuine covering data / regularity produced by Steps 1–2 — the
covering `LossyCode` family, the distortion feasibility, positivity and simplex
membership. No error-probability or decoder-correctness claim is a hypothesis (those
are derived in the body via S5a/S5b). The body is stubbed for a later leg.

Independent honesty audit 2026-07-06: honest residual — signature PASSES the
core-reconstruction test. Granting the 13 hypotheses (`q'`/`κ'`/`qStar`/`d'` witnesses +
factorisation/positivity/simplex/feasibility, and `hcov` = the Step 1–2 covering
`LossyCode` family) does NOT hand you the binned WZ-code achievability: the binning, the
bin-decoder, and the confusion-error exponent remain the body's own (currently `sorry`)
work — none is smuggled into a hypothesis. `hobj'` is the rate objective (precondition,
not the conclusion); `hcov` is the separately-established rate-distortion covering result,
not a bundling of S6's own claim. Classification `plan` (in-project binning composition,
not a Mathlib gap) is correct.
@residual(plan:wyner-ziv-main-plan) -/
lemma wz_perDelta_covering_binning
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (δ : ℝ) (hδ : 0 < δ)
    (q' : α × β × Fin k → ℝ) (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (d' : DistortionFn {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k))
    (hfact_eq : ∀ x y u, q' (x, y, u) = κ' x u * P_XY.real {(x, y)})
    (hκ'pos : ∀ x u, 0 < κ' x u)
    (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (hobj' : wzMutualInfoXU (Fin k) q' - wzMutualInfoYU (Fin k) q' < R)
    (hqStar_eq : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
    (hqStar_pos : ∀ p, 0 < qStar p)
    (hqStar_mem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    (hfeas : expectedDistortionPmf d' qStar ≤ D + δ)
    (hcov : ∀ R₁ : ℝ, mutualInfoPmf qStar < R₁ → ∀ ε' : ℝ, 0 < ε' →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : ℕ,
          Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M ∧
          ∃ c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k),
            c.expectedBlockDistortion
                ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) d'
              ≤ (D + δ) + ε') :
    ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ᶠ n in Filter.atTop, (c n).expectedBlockDistortion P_XY d ≤ D + δ := by
  -- @residual(plan:wyner-ziv-main-plan)
  sorry

/-- **(BD) Per-slack Wyner–Ziv code family.** From a feasible factorisable test
channel `qf` (auxiliary `Fin k`, distortion `≤ D`, Wyner–Ziv objective `< R`), for
every slack `δ > 0` there is a sequence of Wyner–Ziv block codes at the operational
rate `R` (`codebookSize R n` messages) whose expected block distortion is eventually
within `D + δ`.

This is the heavy covering+binning assembly for a fixed slack: internally it
perturbs `qf` to full support (`wz_fullKernelSupport_perturbation`), restricts the
covering source to `α' := {x // 0 < P_X x}` and supplies the covering joint
(`wz_restrictedCoveringJoint_pos` → `wz_covering_lossyCode_exists`), extends back to
`α`, bins the covering index and decodes by a bin conditional-typicality search.

The body is a reduction: Steps 1–2 (`wz_coveringFamily_of_testChannel`) supply the
covering data, and the capstone `wz_perDelta_covering_binning` (S6) consumes it to
build the code family (Steps 3–7: binning + decoder `wzCodeOfCoveringBinning` /
`wzBinTypicalDecoder`, the error exponents `wz_covering_failure_prob_le` /
`wz_codebook_confusion_expectation_le`, derandomize, squeeze, and the source
extension `wzLiftSupportCode`). The preconditions are feasibility/objective only
(`hqf`/`hobj`); the residual `sorry` lives in the S5/S6 sub-lemmas, not here.

Independent honesty audit 2026-07-06: genuine reduction — the body has no `sorry` of its
own; it `obtain`s the covering data from `wz_coveringFamily_of_testChannel` (Steps 1–2) and
`exact`s the S6 capstone `wz_perDelta_covering_binning`. Not an opaque re-sorry, not
bundling: `hqf`/`hobj` are feasibility/objective preconditions and the transitive residual
lives in S6 (and, once wired, S5a/S5b). Honest residual (inherited).
@residual(plan:wyner-ziv-main-plan) -/
private lemma wz_perDelta_codes_exist
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
    (hobj : wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 < R) :
    ∀ δ : ℝ, 0 < δ → ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ᶠ n in Filter.atTop, (c n).expectedBlockDistortion P_XY d ≤ D + δ := by
  intro δ hδ
  -- Steps 1–2 (covering-distortion reconciliation + covering LossyCode family):
  -- perturb `qf` to full support, restrict to the source support `α'`, and produce
  -- the covering LossyCode family at any rate `R₁ > mutualInfoPmf qStar`, with the
  -- covering proxy `d'` reconciled against the Wyner–Ziv distortion (feasibility
  -- `expectedDistortionPmf d' qStar ≤ D + δ`).
  obtain ⟨q', κ', qStar, d', hfact_eq, hκ'pos, hκ'sum, hobj', hqStar_eq,
      hqStar_pos, hqStar_mem, hfeas, hcov⟩ :=
    wz_coveringFamily_of_testChannel P_XY d R D k qf hqf hobj δ hδ
  -- Steps 3–7 (binning / decoder / error exponents / derandomize / squeeze / source
  -- extension) are packaged in the capstone `wz_perDelta_covering_binning` (S6),
  -- which consumes the covering data obtained above:
  --   3. binning: hash the covering index to `codebookSize R n` messages; the rate
  --      split `R₁ = I(X;U)`, net `R = I(X;U) − I(Y;U)`, against `hobj'`.
  --   4. decoder: bin conditional-typicality search (`wzBinTypicalDecoder`, S4),
  --      reconstruct `γ^n` letterwise via `qf.2` (`wzCodeOfCoveringBinning`, S3).
  --   5. error exponents: E1 covering failure (`wz_covering_failure_prob_le`, S5a);
  --      E2 codebook-restricted decoder confusion
  --      (`wz_codebook_confusion_expectation_le`, S5b, the crux).
  --   6. good deterministic codebook + binning by double derandomization.
  --   7. squeeze + source extension `α' → α` (`wzLiftSupportCode`, S7 /
  --      `wz_expectedBlockDistortion_source_agree`).
  exact wz_perDelta_covering_binning P_XY d R D k qf δ hδ q' κ' qStar d'
    hfact_eq hκ'pos hκ'sum hobj' hqStar_eq hqStar_pos hqStar_mem hfeas hcov

/-- **(E) Slack diagonalization.** A family of Wyner–Ziv code sequences, one per
slack `δ > 0`, each eventually within `D + δ`, diagonalises to a single Wyner–Ziv
code sequence that is eventually within `D + ε` for *every* `ε > 0`.

This is a general diagonalization over the slack parameter: choosing `δ_m =
1/(m+1)`, extracting a per-`m` code sequence `C m` with an eventual threshold
`N m`, dominating those thresholds by a diverging schedule `Ñ m ≥ max(N₀ … N_m, m)`,
and diagonalising by `c n := C (idx n) n` where `idx n = Nat.findGreatest (Ñ · ≤ n)
n` selects the largest admissible slack level. Since `idx n → ∞` (as `Ñ` diverges),
the diagonal sequence's eventual bound reaches every `ε`. The hypothesis is the
per-slack achievability family (the output of the covering+binning assembly
`wz_perDelta_codes_exist`); the diagonalization argument is the (sorry-free) body. -/
private lemma wz_diagonalize_slack
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (hfam : ∀ δ : ℝ, 0 < δ → ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ᶠ n in Filter.atTop, (c n).expectedBlockDistortion P_XY d ≤ D + δ) :
    ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (c n).expectedBlockDistortion P_XY d ≤ D + ε := by
  -- Extract a per-slack code sequence `C m` for the slack `δ_m = 1/(m+1)`,
  -- together with an eventual threshold `N m` beyond which its distortion is
  -- within `D + 1/(m+1)`.
  have hδpos : ∀ m : ℕ, (0 : ℝ) < 1 / (m + 1) := fun m => by positivity
  choose C hC using fun m : ℕ => hfam (1 / (m + 1)) (hδpos m)
  choose N hN using fun m => Filter.eventually_atTop.mp (hC m)
  -- A monotone-in-effect threshold schedule dominating every `N m` and diverging:
  -- `Ñ m ≥ N m` (so `hN` applies) and `Ñ m ≥ m` (so `Ñ m → ∞`).
  set Ñ : ℕ → ℕ := fun m => (Finset.range (m + 1)).sup N + m with hÑdef
  have hÑ_ge_N : ∀ m, N m ≤ Ñ m := fun m =>
    le_trans (Finset.le_sup (Finset.self_mem_range_succ m)) (Nat.le_add_right _ _)
  have hÑ_ge_self : ∀ m, m ≤ Ñ m := fun m => Nat.le_add_left _ _
  -- Diagonal code `c n := C (idx n) n`, where `idx n` is the largest `j ≤ n` with
  -- `Ñ j ≤ n`; the diagonal is well-typed since `C (idx n) n : WynerZivCode …`.
  refine ⟨fun n => C (Nat.findGreatest (fun j => Ñ j ≤ n) n) n, ?_⟩
  intro ε hε
  -- Pick `m` with `1/(m+1) < ε` (Archimedean), and show the eventual bound holds
  -- from `n ≥ Ñ m` onward.
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  rw [Filter.eventually_atTop]
  refine ⟨Ñ m, fun n hn => ?_⟩
  show (C (Nat.findGreatest (fun j => Ñ j ≤ n) n) n).expectedBlockDistortion P_XY d ≤ D + ε
  -- `hn : Ñ m ≤ n` witnesses `P m` for `P j := Ñ j ≤ n`; also `m ≤ n`.
  have hmn : m ≤ n := le_trans (hÑ_ge_self m) hn
  -- The selected index is `≥ m` and satisfies its own threshold `Ñ (idx n) ≤ n`.
  have hjge : m ≤ Nat.findGreatest (fun j => Ñ j ≤ n) n := Nat.le_findGreatest hmn hn
  have hjspec : Ñ (Nat.findGreatest (fun j => Ñ j ≤ n) n) ≤ n :=
    Nat.findGreatest_spec (P := fun j => Ñ j ≤ n) hmn hn
  have hNle : N (Nat.findGreatest (fun j => Ñ j ≤ n) n) ≤ n :=
    le_trans (hÑ_ge_N _) hjspec
  -- Apply the per-slack eventual bound at the selected index.
  have hdist := hN (Nat.findGreatest (fun j => Ñ j ≤ n) n) n hNle
  -- `1/(idx n + 1) ≤ 1/(m+1) < ε` since `idx n ≥ m`.
  have hmono : (1 : ℝ) / ((Nat.findGreatest (fun j => Ñ j ≤ n) n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
    apply one_div_le_one_div_of_le
    · positivity
    · have : (m : ℝ) ≤ (Nat.findGreatest (fun j => Ñ j ≤ n) n : ℝ) := by exact_mod_cast hjge
      linarith
  linarith [hdist, hmono, hm]

/-- **Covering + binning construction (Steps 1–5, the hard leg).** From a
feasible factorisable test channel `qf` at auxiliary alphabet `Fin k` whose
Wyner–Ziv objective `I(X;U) − I(Y;U)` is strictly below `R`, build a sequence of
Wyner–Ziv block codes at the operational message rate `R` (`codebookSize R n =
⌈exp(n R)⌉` messages) whose expected block distortion is eventually within
`D + ε` for every `ε > 0`.

The construction is the two-layer hybrid: rate-distortion covering `X → U`
(`jointTypicalLossyEncoder` over the codebook alphabet `U = Fin k`) fused with
Slepian–Wolf binning of the covering index (`binningMeasure`), decoded by a
conditional-typicality slice search (`conditionalTypicalSlice`). The three error
exponents — covering failure (E1, `encoder_failure_prob_le_exp_neg_M_avg`),
decoder confusion (E2, `wz_sideInfo_decoder_confusion_expectation_le`) and
covering acceptance (E3, `wz_covering_sideInfo_mass_ge`) — are threaded through
the rate split `R = I(X;U) − I(Y;U)`, with a good deterministic codebook
extracted by the pigeonhole averaging `exists_codebook_low_avg` and the residual
distortion excess squeezed to `0` by `ceil_exp_mul_exp_neg_tendsto_atTop`.

The test channel `qf` is a feasibility/regularity hypothesis (a single-letter
pmf feasible at `D`, objective below `R`), NOT the load-bearing covering+binning
core; the whole construction stays in the `sorry` body.

**Full-support (source-support) note — the leg-14 stall map.** The covering half
`rate_distortion_achievability` (`AchievabilityStrongTypicality.lean:184`) demands
`hqStar_pos : ∀ p, 0 < qStar p` on the `(X,U)` joint `qStar = wzMarginalXU (Fin k)
qf.1`. This is **not** obtainable by kernel perturbation alone: factorisability
forces `qStar (x,u) = κ(x,u) · P_X(x)` (with `P_X(x) = ∑_y P_XY(x,y)`), which
vanishes at every zero atom of `P_X` regardless of `κ`. So of the options
(a) covering tolerates support-only positivity, (b) restrict the source alphabet
to `supp(P_X)` upstream, (c) genuine obstruction, the resolution is **(b)**: the
RD covering theorem hard-requires positivity over its *whole* alphabet, so the
construction must instantiate its source alphabet `α` with the subtype
`{x // 0 < P_X x}` (the block distortion is measured under `Measure.pi P_X`, which
gives zero mass to sequences hitting a zero atom, so restricting to `supp(P_X)` is
WLOG). The leaf lemma `wz_fullKernelSupport_perturbation` supplies the *kernel*
full support `0 < κ' x u` (hence full `(X,U)`-joint support on `supp(P_X)` and the
objective/distortion slack); the remaining move is the support-subtype transport,
deferred to the construction sub-lemmas.

The body is now a `sorry`-free reduction: `wz_perDelta_codes_exist` builds, for each
slack `δ > 0`, a code sequence eventually within `D + δ` (the covering + binning
assembly), and `wz_diagonalize_slack` (now proved sorry-free) diagonalises those into
a single sequence within `D + ε` for every `ε`. The residual `sorry +
@residual(plan:wyner-ziv-main-plan)` lives in `wz_perDelta_codes_exist` (and the
covering / source-support atoms it consumes, `wz_covering_lossyCode_exists` /
`wz_expectedBlockDistortion_source_agree`), not here. -/
private lemma wz_goodCode_exists_of_testChannel
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
    (hobj : wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 < R) :
    ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (c n).expectedBlockDistortion P_XY d ≤ D + ε :=
  wz_diagonalize_slack P_XY d R D
    (wz_perDelta_codes_exist P_XY d R D k qf hqf hobj)

/-- Existence of a Wyner–Ziv code sequence (at the operational message rate `R`)
whose expected block distortion is eventually within `D + ε`.

The body is now a genuine reduction (sorry-free itself): `wz_testChannel_of_rate_lt`
extracts a feasible factorisable test channel below `R` from the feasibility guard
`h_ne` and `h_rate`, and `wz_goodCode_exists_of_testChannel` builds the code
sequence from it. `sorryAx` enters only via that construction lemma, whose covering
+ binning body is the remaining plumbing.

The feasibility precondition `h_ne` (the rate-distortion value set is nonempty at
`D`) makes the signature well-posed: it rules out the infeasible regime `D` below
the min achievable distortion (e.g. any `D < 0` for a `NNReal` distortion), where
`wzRateValueSet` is empty and `wynerZivRate = sInf ∅ = 0` would otherwise let
`h_rate : 0 < R` coexist with a FALSE existence claim. `h_ne` is a
regularity/feasibility precondition, NOT the load-bearing covering+binning core
(which stays in the construction lemma's `sorry` body); the converse side already
threads exactly this guard (`wynerZivRate_antitone`, `Converse.lean:2602`).
@residual(plan:wyner-ziv-main-plan) -/
theorem wyner_ziv_achievability_codes
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (h_ne : (wzRateValueSet (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D).Nonempty)
    (h_rate : wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D < R) :
    ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (c n).expectedBlockDistortion P_XY d ≤ D + ε := by
  obtain ⟨k, qf, hqf, hobj⟩ := wz_testChannel_of_rate_lt P_XY d R D h_ne h_rate
  exact wz_goodCode_exists_of_testChannel P_XY d R D k qf hqf hobj

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
enters only via `wyner_ziv_achievability_codes`) and the statement is honest.
@residual(plan:wyner-ziv-main-plan) -/
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

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
deferred with this body.
@residual(plan:wyner-ziv-main-plan) -/
private lemma wz_goodCode_exists_of_testChannel
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
    (hobj : wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 < R) :
    ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (c n).expectedBlockDistortion P_XY d ≤ D + ε := by
  sorry

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

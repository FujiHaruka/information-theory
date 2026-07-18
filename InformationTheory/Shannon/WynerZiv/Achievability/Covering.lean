import InformationTheory.Shannon.WynerZiv.Operational
import InformationTheory.Shannon.WynerZiv.FactorizableRate
import InformationTheory.Shannon.WynerZiv.Converse
import InformationTheory.Shannon.SlepianWolf.FullRateRegion.AliasBound
import InformationTheory.Shannon.ConditionalMethodOfTypes.Mass
import InformationTheory.Shannon.RateDistortion.AchievabilityStrongTypicality

/-!
# Wyner–Ziv achievability — covering + binning construction
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
lemma wynerZivRate_nonneg
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
lemma wz_testChannel_of_rate_lt
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
lemma wz_nonempty_of_factorizable
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
lemma wz_fullKernelSupport_perturbation
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
lemma wz_tendsto_exp_mul_codebookSize_inv {c R : ℝ} (hcR : c < R) :
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
`wz_restrictedCoveringJoint_pos` (S1) is proved here; the covering / source-support /
diagonalization steps (`wz_covering_lossyCode_exists`, `wz_expectedBlockDistortion_source_agree`,
`wz_diagonalize_slack`) and the per-`n` binning+covering assembly
`wz_perN_covering_binning_code` (D3) are all closed sorry-free. Full support of the
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
lemma wz_restrictedCoveringJoint_pos
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
lemma wz_expectedBlockDistortion_source_agree
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
lemma wz_jointStronglyTypical_mem_distortionTypical
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
lemma wz_covering_lossyCode_exists
    {k : ℕ} [Nonempty (Fin k)] {α' : Type*} [Fintype α'] [DecidableEq α']
    [Nonempty α'] [MeasurableSpace α'] [MeasurableSingletonClass α']
    (qStar : α' × Fin k → ℝ) (hpos : ∀ p, 0 < qStar p)
    (hmem : qStar ∈ stdSimplex ℝ (α' × Fin k)) (d' : DistortionFn α' (Fin k))
    {R₁ D : ℝ} (hI : mutualInfoPmf qStar < R₁)
    (hfeas : expectedDistortionPmf d' qStar ≤ D) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : ℕ, Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M ∧
      (M : ℝ) ≤ Real.exp ((n : ℝ) * R₁) + 1 ∧
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
  obtain ⟨M, hM_lb, hM_ub, c, hc⟩ := hN n hn
  exact ⟨M, hM_lb, hM_ub, c, hc⟩

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
lemma wz_coveringDistortion_reconcile
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

/-- The `(U, Y)`-marginal joint pmf feeding the side-information ambient, restricted to the
positive-`Y`-marginal subtype. For a full-support covering kernel `κ'` and the source law
`P_XY`, the value at `(u, y)` is `∑ₓ κ'(x, u) · P_XY{(x, y)}`, the `Y`-side analogue of the
covering pmf `qStar` (which lives on the positive-`X`-marginal subtype). -/
noncomputable def wzSideInfoMarginal (P_XY : Measure (α × β)) {k : ℕ} (κ' : α → Fin k → ℝ) :
    Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}} → ℝ :=
  fun p ↦ ∑ x, κ' x p.1 * P_XY.real {(x, p.2.1)}

lemma wzSideInfoMarginal_pos
    (P_XY : Measure (α × β)) {k : ℕ} (κ' : α → Fin k → ℝ)
    (hκ'pos : ∀ x u, 0 < κ' x u) :
    ∀ p, 0 < wzSideInfoMarginal P_XY κ' p := by
  intro p
  have hpos_sum : 0 < ∑ x, P_XY.real {(x, p.2.1)} := p.2.2
  show 0 < ∑ x, κ' x p.1 * P_XY.real {(x, p.2.1)}
  refine Finset.sum_pos' (fun x _ ↦ mul_nonneg (hκ'pos x p.1).le measureReal_nonneg) ?_
  by_contra h
  push_neg at h
  refine absurd hpos_sum (not_lt.mpr ?_)
  refine le_of_eq (Finset.sum_eq_zero fun x _ ↦ ?_)
  by_contra hx
  exact absurd (mul_pos (hκ'pos x p.1)
    (lt_of_le_of_ne measureReal_nonneg (Ne.symm hx))) (not_lt.mpr (h x (Finset.mem_univ x)))

lemma wzSideInfoMarginal_sum_eq_one
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY] {k : ℕ} (κ' : α → Fin k → ℝ)
    (hκ'sum : ∀ x, ∑ u, κ' x u = 1) :
    ∑ p, wzSideInfoMarginal P_XY κ' p = 1 := by
  classical
  -- The `Y`-marginal at `x`, summed over the positive-`Y`-marginal subtype, equals the
  -- full `Y`-marginal (the excluded `y` carry zero mass).
  have hsubtype : ∀ x : α,
      ∑ ys : {y : β // 0 < ∑ x', P_XY.real {(x', y)}}, P_XY.real {(x, ys.1)}
        = ∑ y : β, P_XY.real {(x, y)} := by
    intro x
    letI : DecidablePred (fun y : β => 0 < ∑ x', P_XY.real {(x', y)}) :=
      Classical.decPred _
    rw [← Finset.sum_subtype
        (Finset.univ.filter (fun y : β => 0 < ∑ x', P_XY.real {(x', y)}))
        (fun y => by simp) (fun y => P_XY.real {(x, y)})]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro y _ hy
    rw [Finset.mem_filter] at hy
    push_neg at hy
    have hle : ∑ x', P_XY.real {(x', y)} ≤ 0 := hy (Finset.mem_univ y)
    have hz : ∑ x', P_XY.real {(x', y)} = 0 :=
      le_antisymm hle (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ measureReal_nonneg)).mp hz x
      (Finset.mem_univ x)
  -- Total mass over `α × β` is `1`.
  have hsum1 : ∑ p : α × β, P_XY.real {p} = 1 := by
    have h1 : (∑ p : α × β, P_XY.real {p}) = P_XY.real (Finset.univ : Finset (α × β)) := by
      simp [sum_measureReal_singleton]
    rw [h1, Finset.coe_univ, probReal_univ]
  show ∑ p : Fin k × {y : β // 0 < ∑ x', P_XY.real {(x', y)}},
      ∑ x, κ' x p.1 * P_XY.real {(x, p.2.1)} = 1
  rw [Fintype.sum_prod_type]
  have hstep : ∀ u : Fin k,
      ∑ ys : {y : β // 0 < ∑ x', P_XY.real {(x', y)}}, ∑ x, κ' x u * P_XY.real {(x, ys.1)}
        = ∑ x, κ' x u * ∑ y : β, P_XY.real {(x, y)} := by
    intro u
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    rw [← Finset.mul_sum, hsubtype x]
  simp_rw [hstep]
  rw [Finset.sum_comm]
  have hstep2 : ∀ x : α,
      ∑ u : Fin k, κ' x u * ∑ y : β, P_XY.real {(x, y)} = ∑ y : β, P_XY.real {(x, y)} := by
    intro x
    rw [← Finset.sum_mul, hκ'sum x, one_mul]
  simp_rw [hstep2]
  rw [Fintype.sum_prod_type] at hsum1
  exact hsum1

lemma wzSideInfoMarginal_mem_stdSimplex
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY] {k : ℕ} (κ' : α → Fin k → ℝ)
    (hκ'pos : ∀ x u, 0 < κ' x u) (hκ'sum : ∀ x, ∑ u, κ' x u = 1) :
    wzSideInfoMarginal P_XY κ'
      ∈ stdSimplex ℝ (Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) :=
  ⟨fun p ↦ (wzSideInfoMarginal_pos P_XY κ' hκ'pos p).le,
    wzSideInfoMarginal_sum_eq_one P_XY κ' hκ'sum⟩

lemma wzSideInfoMarginal_subtype_nonempty
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY] :
    Nonempty {y : β // 0 < ∑ x, P_XY.real {(x, y)}} := by
  have hsum1 : ∑ p : α × β, P_XY.real {p} = 1 := by
    have h1 : (∑ p : α × β, P_XY.real {p}) = P_XY.real (Finset.univ : Finset (α × β)) := by
      simp [sum_measureReal_singleton]
    rw [h1, Finset.coe_univ, probReal_univ]
  obtain ⟨x₀, y₀, hxy⟩ : ∃ x y, 0 < P_XY.real {(x, y)} := by
    by_contra h
    push_neg at h
    have hzero : ∑ p : α × β, P_XY.real {p} = 0 :=
      Finset.sum_eq_zero fun p _ ↦ le_antisymm (h p.1 p.2) measureReal_nonneg
    rw [hsum1] at hzero
    exact one_ne_zero hzero
  refine ⟨⟨y₀, ?_⟩⟩
  calc (0 : ℝ) < P_XY.real {(x₀, y₀)} := hxy
    _ ≤ ∑ x, P_XY.real {(x, y₀)} :=
        Finset.single_le_sum (f := fun x => P_XY.real {(x, y₀)})
          (fun x _ ↦ measureReal_nonneg) (Finset.mem_univ x₀)

/-- **Covering-acceptance failure event (C2).** For a covering `LossyCode` `c` on the
source-support subtype `α' := {x // 0 < P_X x}`, the set of block source–side pairs
`p : Fin n → α' × β` whose true covering codeword `c.decoder (c.encoder x)` is *not*
jointly (strongly) typical, at radius `ε`, with the side information `y` in the
side-information ambient `rdAmbient (wzSideInfoMarginal P_XY κ')`. This is the covering
half of the Wyner–Ziv error event `E2`: acceptance failure of the correct covering word
(`wzBinTypicalDecoder_eq_of_unique` requires this joint typicality to recover it), so
`C2 ⊆ E2`. Pure event set (data), used to state the covering-acceptance-failure mass
bound threaded from the covering construction to `wz_exists_binning_E2_bound` (A3). -/
def wzCoveringAcceptFailSet (P_XY : Measure (α × β)) {k : ℕ}
    (κ' : α → Fin k → ℝ) {M n : ℕ}
    (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)) (ε : ℝ) :
    Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
  { p | (c.decoder (c.encoder (fun j ↦ (p j).1)), fun i ↦ (p i).2)
      ∉ ChannelCoding.jointlyTypicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
          ChannelCoding.iidXs
          (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
            ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))
          n ε }

/-- The source–side covering pmf `(x', y) ↦ P_XY{(x'.1, y)}` (on the source-support subtype)
is a probability vector: its values are nonnegative measures and they total `1` (the zero-`P_X`
atoms carry no mass, so the subtype sum equals the full joint mass). Used to supply the
`IsProbabilityMeasure` instance for the correlated-joint source measure `Measure.pi (pmfToMeasure …)`. -/
lemma wz_QXY_mem_stdSimplex
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY] :
    (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})
      ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) := by
  classical
  refine ⟨fun _ ↦ measureReal_nonneg, ?_⟩
  have hPnn : ∀ x : α, 0 ≤ ∑ y, P_XY.real {(x, y)} :=
    fun x ↦ Finset.sum_nonneg fun y _ ↦ measureReal_nonneg
  have htot : (∑ x : α, ∑ y : β, P_XY.real {(x, y)}) = 1 := by
    have h1 : (∑ p : α × β, P_XY.real {p}) = 1 := by
      have h2 : (∑ p : α × β, P_XY.real {p}) = P_XY.real (Finset.univ : Finset (α × β)) := by
        simp [sum_measureReal_singleton]
      rw [h2, Finset.coe_univ]; exact probReal_univ
    rw [← h1, Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x ↦ 0 < ∑ y, P_XY.real {(x, y)}))
        (fun x ↦ by simp) (fun x ↦ ∑ y, P_XY.real {(x, y)})]
  rw [Finset.sum_subset (Finset.filter_subset _ _)
        (fun x _ hx ↦ le_antisymm (not_lt.mp (by simpa using hx)) (hPnn x))]
  exact htot



/-! ### (Hoisted for Atom G) Markov-core chain + its regularity helpers.
Relocated verbatim from after `wyner_ziv_achievability_codes` to here so the covering
atom `wz_coveringFamily_of_testChannel` (below) can consume the leaf
`wz_covering_chosenWord_sideInfo_typical`. Pure relocation — no signature or proof change. -/

section LegAAmbientRegularity

variable {A B : Type*}
  [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [DecidableEq B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

lemma rdAmbient_iIndepFun_iidXs (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) :
    iIndepFun (fun i : ℕ ↦ ChannelCoding.iidXs (α := A) (β := B) i) (rdAmbient q) := by
  haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure (α := A × B) q) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure hq
  exact iidAmbientJoint_iIndepFun_iidXs (ChannelCoding.pmfToMeasure (α := A × B) q)

lemma rdAmbient_iIndepFun_iidYs (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) :
    iIndepFun (fun i : ℕ ↦ ChannelCoding.iidYs (α := A) (β := B) i) (rdAmbient q) := by
  haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure (α := A × B) q) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure hq
  exact iIndepFun_infinitePi
    (P := fun _ : ℕ ↦ ChannelCoding.pmfToMeasure (α := A × B) q)
    (X := fun _ : ℕ ↦ (Prod.snd : A × B → B))
    (fun _ ↦ measurable_snd)

lemma rdAmbient_iIndepFun_jointSequence (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) :
    iIndepFun
      (fun i : ℕ ↦ ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs i)
      (rdAmbient q) := by
  haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure (α := A × B) q) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure hq
  exact iidAmbientJoint_iIndepFun_joint (ChannelCoding.pmfToMeasure (α := A × B) q)

lemma rdAmbient_pairwise_indep_jointSequence (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) :
    Pairwise fun i j ↦
      ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs i
        ⟂ᵢ[rdAmbient q]
      ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs j := by
  intro i j hij
  exact (rdAmbient_iIndepFun_jointSequence q hq).indepFun hij

lemma rdAmbient_identDistrib_iidXs (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) (i : ℕ) :
    IdentDistrib (ChannelCoding.iidXs (α := A) (β := B) i) (ChannelCoding.iidXs 0)
      (rdAmbient q) (rdAmbient q) := by
  haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure (α := A × B) q) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure hq
  exact iidAmbientJoint_identDistrib_iidXs (ChannelCoding.pmfToMeasure (α := A × B) q) i

lemma rdAmbient_identDistrib_iidYs (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) (i : ℕ) :
    IdentDistrib (ChannelCoding.iidYs (α := A) (β := B) i) (ChannelCoding.iidYs 0)
      (rdAmbient q) (rdAmbient q) where
  aemeasurable_fst := (ChannelCoding.measurable_iidYs i).aemeasurable
  aemeasurable_snd := (ChannelCoding.measurable_iidYs 0).aemeasurable
  map_eq := by
    haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure (α := A × B) q) :=
      ChannelCoding.pmfToMeasure_isProbabilityMeasure hq
    show Measure.map (ChannelCoding.iidYs (α := A) (β := B) i)
          (iidAmbientJointMeasure (ChannelCoding.pmfToMeasure (α := A × B) q))
        = Measure.map (ChannelCoding.iidYs (α := A) (β := B) 0)
          (iidAmbientJointMeasure (ChannelCoding.pmfToMeasure (α := A × B) q))
    rw [iidAmbientJoint_map_iidYs, iidAmbientJoint_map_iidYs]

lemma rdAmbient_identDistrib_jointSequence
    (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) (i : ℕ) :
    IdentDistrib
      (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs i)
      (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0)
      (rdAmbient q) (rdAmbient q) := by
  haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure (α := A × B) q) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure hq
  exact iidAmbientJoint_identDistrib_joint (ChannelCoding.pmfToMeasure (α := A × B) q) i

lemma rdAmbient_iidXs_real_singleton_pos
    (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) (hpos : ∀ p : A × B, 0 < q p) (x : A) :
    0 < ((rdAmbient q).map (ChannelCoding.iidXs (α := A) (β := B) 0)).real {x} := by
  haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure (α := A × B) q) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure hq
  exact iidAmbientJoint_iidXs_real_singleton_pos (ChannelCoding.pmfToMeasure (α := A × B) q)
    (fun p ↦ pmfToMeasure_real_singleton_pos hq hpos p) x

lemma rdAmbient_iidYs_real_singleton_pos
    (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) (hpos : ∀ p : A × B, 0 < q p) (y : B) :
    0 < ((rdAmbient q).map (ChannelCoding.iidYs (α := A) (β := B) 0)).real {y} := by
  haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure (α := A × B) q) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure hq
  exact iidAmbientJoint_iidYs_real_singleton_pos (ChannelCoding.pmfToMeasure (α := A × B) q)
    (fun p ↦ pmfToMeasure_real_singleton_pos hq hpos p) y

lemma rdAmbient_jointSequence_real_singleton_pos
    (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) (hpos : ∀ p : A × B, 0 < q p) (p : A × B) :
    0 < ((rdAmbient q).map
          (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0)).real {p} := by
  haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure (α := A × B) q) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure hq
  exact iidAmbientJoint_joint_real_singleton_pos (ChannelCoding.pmfToMeasure (α := A × B) q)
    (fun p ↦ pmfToMeasure_real_singleton_pos hq hpos p) p

lemma rdAmbient_map_fst_jointSequence (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) :
    ((rdAmbient q).map
          (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0)).map Prod.fst
      = (rdAmbient q).map (ChannelCoding.iidXs (α := A) (β := B) 0) := by
  rw [rdAmbient_map_jointSequence q hq, rdAmbient_map_iidXs q hq]

lemma rdAmbient_map_snd_jointSequence (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) :
    ((rdAmbient q).map
          (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0)).map Prod.snd
      = (rdAmbient q).map (ChannelCoding.iidYs (α := A) (β := B) 0) := by
  rw [rdAmbient_map_jointSequence q hq, rdAmbient_map_iidYs q hq]

/-- The `n`-fold pair-sequence law of `rdAmbient q` is the product of the pmf `q`: the joint
`(X, Y)`-sequence `jointRV (jointSequence iidXs iidYs) n` pushes `rdAmbient q` to
`Measure.pi (pmfToMeasure q)`. The iid-to-product identity for the pair sequence (the
`jointSequence` analogue of `wz_ambient_jointRV_iidYs_eq_pi`). -/
lemma rdAmbient_map_jointRV_jointSequence_eq_pi
    (q : A × B → ℝ) (hq : q ∈ stdSimplex ℝ (A × B)) (n : ℕ) :
    (rdAmbient q).map
        (jointRV (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n)
      = Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure (α := A × B) q) := by
  haveI : IsProbabilityMeasure (rdAmbient q) := rdAmbient_isProbabilityMeasure q hq
  have hindep_full :
      iIndepFun
        (fun i : ℕ ↦ ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs i)
        (rdAmbient q) := rdAmbient_iIndepFun_jointSequence q hq
  have hident : ∀ i : ℕ, IdentDistrib
      (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs i)
      (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0)
      (rdAmbient q) (rdAmbient q) := rdAmbient_identDistrib_jointSequence q hq
  have hindep_fin :
      iIndepFun
        (fun i : Fin n ↦ ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs i.val)
        (rdAmbient q) := hindep_full.precomp Fin.val_injective
  have hmap_eq : ∀ i : Fin n, (rdAmbient q).map
      (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs i.val)
        = (rdAmbient q).map
            (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0) :=
    fun i ↦ (hident i.val).map_eq
  have hpi := (iIndepFun_iff_map_fun_eq_pi_map
      (μ := rdAmbient q)
      (fun i : Fin n ↦ (ChannelCoding.measurable_jointSequence _ _
        (fun i ↦ ChannelCoding.measurable_iidXs i)
        (fun i ↦ ChannelCoding.measurable_iidYs i) i.val).aemeasurable)).mp hindep_fin
  calc (rdAmbient q).map
          (jointRV (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n)
      = (rdAmbient q).map
          (fun ω i ↦
            ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs i.val ω) := rfl
    _ = Measure.pi (fun i : Fin n ↦ (rdAmbient q).map
          (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs i.val)) := hpi
    _ = Measure.pi (fun _ : Fin n ↦ (rdAmbient q).map
          (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0)) := by
        congr 1; funext i; exact hmap_eq i
    _ = Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure (α := A × B) q) := by
        congr 1; funext i; exact rdAmbient_map_jointSequence q hq

end LegAAmbientRegularity

/-- Per-atom mass is preserved by pushing forward along an injective (measurable) alphabet map:
`(μ.map (g ∘ X)).real {g a} = (μ.map X).real {a}`. -/
lemma wz_map_injective_real_singleton {Ω γ₀ δ₀ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace γ₀] [MeasurableSingletonClass γ₀]
    [MeasurableSpace δ₀] [MeasurableSingletonClass δ₀]
    (μ : Measure Ω) (X : Ω → γ₀) (hX : Measurable X)
    (g : γ₀ → δ₀) (hg : Function.Injective g) (hgmeas : Measurable g) (a : γ₀) :
    (μ.map (fun ω ↦ g (X ω))).real {g a} = (μ.map X).real {a} := by
  have hgX : Measurable (fun ω ↦ g (X ω)) := hgmeas.comp hX
  rw [map_measureReal_apply hgX (MeasurableSet.singleton (g a)),
      map_measureReal_apply hX (MeasurableSet.singleton a)]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
  exact ⟨fun h ↦ hg h, fun h ↦ by rw [h]⟩

/-- Shannon entropy is invariant under an injective (measurable) relabeling of the alphabet. -/
lemma wz_entropy_map_injective {Ω γ₀ δ₀ : Type*} [MeasurableSpace Ω]
    [Fintype γ₀] [DecidableEq γ₀] [Nonempty γ₀] [MeasurableSpace γ₀] [MeasurableSingletonClass γ₀]
    [Fintype δ₀] [DecidableEq δ₀] [Nonempty δ₀] [MeasurableSpace δ₀] [MeasurableSingletonClass δ₀]
    (μ : Measure Ω) (X : Ω → γ₀) (hX : Measurable X)
    (g : γ₀ → δ₀) (hg : Function.Injective g) (hgmeas : Measurable g) :
    entropy μ (fun ω ↦ g (X ω)) = entropy μ X := by
  classical
  have hgX : Measurable (fun ω ↦ g (X ω)) := hgmeas.comp hX
  unfold entropy
  rw [show (∑ a, Real.negMulLog ((μ.map X).real {a}))
        = ∑ a, Real.negMulLog ((μ.map (fun ω ↦ g (X ω))).real {g a}) from
      Finset.sum_congr rfl
        (fun a _ ↦ by rw [wz_map_injective_real_singleton μ X hX g hg hgmeas a]),
      ← Finset.sum_image (s := (Finset.univ : Finset γ₀))
        (f := fun d ↦ Real.negMulLog ((μ.map (fun ω ↦ g (X ω))).real {d}))
        (fun a _ b _ h ↦ hg h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro d _ hd
  have hpre : (fun ω ↦ g (X ω)) ⁻¹' {d} = (∅ : Set Ω) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hgd
    exact hd (Finset.mem_image.mpr ⟨X ω, Finset.mem_univ _, hgd⟩)
  rw [map_measureReal_apply hgX (MeasurableSet.singleton d), hpre,
      measureReal_empty, Real.negMulLog_zero]

/-- The Wyner–Ziv source per-coordinate pmf `p ↦ P_XY{(p.1.1, p.2)}` on `α' × β` is a pmf. -/
lemma wz_sourcePmf_mem_stdSimplex
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}] :
    (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})
      ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) := by
  classical
  refine ⟨fun p ↦ measureReal_nonneg, ?_⟩
  have hsum1 : ∑ p : α × β, P_XY.real {p} = 1 := by
    have h1 : (∑ p : α × β, P_XY.real {p}) = P_XY.real (Finset.univ : Finset (α × β)) := by
      simp [sum_measureReal_singleton]
    rw [h1, Finset.coe_univ, probReal_univ]
  show ∑ p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β, P_XY.real {(p.1.1, p.2)} = 1
  rw [Fintype.sum_prod_type]
  have hsub_total :
      (∑ x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}, ∑ y : β, P_XY.real {(x'.1, y)})
        = ∑ x : α, ∑ y : β, P_XY.real {(x, y)} := by
    letI : DecidablePred (fun x : α => 0 < ∑ y, P_XY.real {(x, y)}) := Classical.decPred _
    rw [← Finset.sum_subtype (Finset.univ.filter (fun x : α => 0 < ∑ y, P_XY.real {(x, y)}))
        (fun x => by simp) (fun x => ∑ y : β, P_XY.real {(x, y)})]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x _ hx
    rw [Finset.mem_filter] at hx
    push_neg at hx
    exact le_antisymm (hx (Finset.mem_univ x)) (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)
  rw [Fintype.sum_prod_type] at hsum1
  rw [hsub_total]
  exact hsum1

/-- The `Y`-marginal (over full `β`) of the source per-coordinate measure equals the full
`Y`-marginal of `P_XY`: `((pmfToMeasure source).map Prod.snd).real {y} = ∑ x, P_XY{(x, y)}`. -/
private lemma wz_source_snd_marginal
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}] (y : β) :
    ((ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})).map
        Prod.snd).real {y}
      = ∑ x, P_XY.real {(x, y)} := by
  classical
  rw [pmfToMeasure_map_snd_real_singleton (wz_sourcePmf_mem_stdSimplex P_XY) y]
  simp only [marginalSnd]
  show (∑ x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}, P_XY.real {(x'.1, y)})
      = ∑ x : α, P_XY.real {(x, y)}
  letI : DecidablePred (fun x : α => 0 < ∑ y, P_XY.real {(x, y)}) := Classical.decPred _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : α => 0 < ∑ y, P_XY.real {(x, y)}))
      (fun x => by simp) (fun x => P_XY.real {(x, y)})]
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro x _ hx
  rw [Finset.mem_filter] at hx
  push_neg at hx
  have hle : ∑ y', P_XY.real {(x, y')} ≤ 0 := hx (Finset.mem_univ x)
  have hz : ∑ y', P_XY.real {(x, y')} = 0 :=
    le_antisymm hle (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ measureReal_nonneg)).mp hz y (Finset.mem_univ y)

/-- The `β'`-`Y`-marginal of the side-information ambient equals the full `Y`-marginal of `P_XY`
at the subtype value: `((rdAmbient wsm).map (iidYs 0)).real {y'} = ∑ x, P_XY{(x, y'.1)}`. -/
private lemma wz_ambient_snd_marginal
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)] (κ' : α → Fin k → ℝ)
    (hκ'pos : ∀ x u, 0 < κ' x u) (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (y' : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) :
    ((rdAmbient (wzSideInfoMarginal P_XY κ')).map
        (ChannelCoding.iidYs (α := Fin k) 0)).real {y'}
      = ∑ x, P_XY.real {(x, y'.1)} := by
  classical
  haveI : Nonempty {y : β // 0 < ∑ x, P_XY.real {(x, y)}} := ⟨y'⟩
  have hq := wzSideInfoMarginal_mem_stdSimplex P_XY κ' hκ'pos hκ'sum
  rw [rdAmbient_map_iidYs (wzSideInfoMarginal P_XY κ') hq,
      pmfToMeasure_map_snd_real_singleton hq y']
  simp only [marginalSnd, wzSideInfoMarginal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  rw [← Finset.sum_mul, hκ'sum x, one_mul]

/-- Side-information-law agreement: the source's full-`β` `Y`-law equals the `β`-image (under the
subtype coercion) of the ambient's `β'`-`Y`-law. -/
lemma wz_source_snd_eq_ambient_snd_map
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}]
    {k : ℕ} [Nonempty (Fin k)] (κ' : α → Fin k → ℝ)
    (hκ'pos : ∀ x u, 0 < κ' x u) (hκ'sum : ∀ x, ∑ u, κ' x u = 1) :
    (ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})).map
        Prod.snd
      = ((rdAmbient (wzSideInfoMarginal P_XY κ')).map
          (ChannelCoding.iidYs (α := Fin k) 0)).map Subtype.val := by
  classical
  haveI : Nonempty {y : β // 0 < ∑ x, P_XY.real {(x, y)}} :=
    wzSideInfoMarginal_subtype_nonempty P_XY
  haveI : IsProbabilityMeasure (ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure (wz_sourcePmf_mem_stdSimplex P_XY)
  haveI : IsProbabilityMeasure (rdAmbient (wzSideInfoMarginal P_XY κ')) :=
    rdAmbient_isProbabilityMeasure _ (wzSideInfoMarginal_mem_stdSimplex P_XY κ' hκ'pos hκ'sum)
  apply Measure.ext_of_singleton
  intro y
  have hreal : ((ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})).map
        Prod.snd).real {y}
      = (((rdAmbient (wzSideInfoMarginal P_XY κ')).map
          (ChannelCoding.iidYs (α := Fin k) 0)).map Subtype.val).real {y} := by
    rw [wz_source_snd_marginal P_XY y,
        map_measureReal_apply measurable_subtype_coe (MeasurableSet.singleton y)]
    by_cases hy : 0 < ∑ x, P_XY.real {(x, y)}
    · have hpre : (Subtype.val ⁻¹' {y} : Set {y : β // 0 < ∑ x, P_XY.real {(x, y)}})
          = {(⟨y, hy⟩ : {y : β // 0 < ∑ x, P_XY.real {(x, y)}})} := by
        ext y'
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
      rw [hpre, wz_ambient_snd_marginal P_XY κ' hκ'pos hκ'sum ⟨y, hy⟩]
    · have hpre : (Subtype.val ⁻¹' {y} : Set {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) = ∅ := by
        ext y'
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro hval
        exact hy (hval ▸ y'.2)
      rw [hpre, measureReal_empty]
      exact le_antisymm (not_lt.mp hy) (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)
  have hL := measure_ne_top ((ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})).map
      Prod.snd) {y}
  have hR := measure_ne_top (((rdAmbient (wzSideInfoMarginal P_XY κ')).map
      (ChannelCoding.iidYs (α := Fin k) 0)).map Subtype.val) {y}
  rw [← ENNReal.ofReal_toReal hL, ← ENNReal.ofReal_toReal hR]
  exact congrArg ENNReal.ofReal hreal

/-- The `n`-fold side-information law of the ambient factorises as the product of its
single-letter `β'`-`Y`-marginal. -/
lemma wz_ambient_jointRV_iidYs_eq_pi
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)] (κ' : α → Fin k → ℝ)
    (hκ'pos : ∀ x u, 0 < κ' x u) (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (n : ℕ) :
    (rdAmbient (wzSideInfoMarginal P_XY κ')).map (jointRV (ChannelCoding.iidYs (α := Fin k)) n)
      = Measure.pi (fun _ : Fin n ↦
          (rdAmbient (wzSideInfoMarginal P_XY κ')).map (ChannelCoding.iidYs (α := Fin k) 0)) := by
  haveI : Nonempty {y : β // 0 < ∑ x, P_XY.real {(x, y)}} :=
    wzSideInfoMarginal_subtype_nonempty P_XY
  have hq := wzSideInfoMarginal_mem_stdSimplex P_XY κ' hκ'pos hκ'sum
  haveI : IsProbabilityMeasure (rdAmbient (wzSideInfoMarginal P_XY κ')) :=
    rdAmbient_isProbabilityMeasure _ hq
  have hindep_full :
      iIndepFun (fun i : ℕ ↦ ChannelCoding.iidYs (α := Fin k) i)
        (rdAmbient (wzSideInfoMarginal P_XY κ')) :=
    rdAmbient_iIndepFun_iidYs (wzSideInfoMarginal P_XY κ') hq
  have hident : ∀ i : ℕ, IdentDistrib (ChannelCoding.iidYs (α := Fin k) i)
      (ChannelCoding.iidYs (α := Fin k) 0)
      (rdAmbient (wzSideInfoMarginal P_XY κ')) (rdAmbient (wzSideInfoMarginal P_XY κ')) :=
    rdAmbient_identDistrib_iidYs (wzSideInfoMarginal P_XY κ') hq
  have hindep_fin :
      iIndepFun (fun i : Fin n ↦ ChannelCoding.iidYs (α := Fin k) i.val)
        (rdAmbient (wzSideInfoMarginal P_XY κ')) :=
    hindep_full.precomp Fin.val_injective
  have hmap_eq : ∀ i : Fin n, (rdAmbient (wzSideInfoMarginal P_XY κ')).map
      (ChannelCoding.iidYs (α := Fin k) i.val)
        = (rdAmbient (wzSideInfoMarginal P_XY κ')).map (ChannelCoding.iidYs (α := Fin k) 0) :=
    fun i ↦ (hident i.val).map_eq
  have hpi := (iIndepFun_iff_map_fun_eq_pi_map
      (μ := rdAmbient (wzSideInfoMarginal P_XY κ'))
      (fun i : Fin n ↦ (ChannelCoding.measurable_iidYs (α := Fin k) i.val).aemeasurable)).mp
      hindep_fin
  calc (rdAmbient (wzSideInfoMarginal P_XY κ')).map
          (jointRV (ChannelCoding.iidYs (α := Fin k)) n)
      = (rdAmbient (wzSideInfoMarginal P_XY κ')).map
          (fun ω i ↦ ChannelCoding.iidYs (α := Fin k) i.val ω) := rfl
    _ = Measure.pi (fun i : Fin n ↦ (rdAmbient (wzSideInfoMarginal P_XY κ')).map
          (ChannelCoding.iidYs (α := Fin k) i.val)) := hpi
    _ = Measure.pi (fun _ : Fin n ↦ (rdAmbient (wzSideInfoMarginal P_XY κ')).map
          (ChannelCoding.iidYs (α := Fin k) 0)) := by
        congr 1; funext i; exact hmap_eq i

end InformationTheory.Shannon

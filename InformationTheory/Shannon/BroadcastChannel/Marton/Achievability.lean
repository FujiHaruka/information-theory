import InformationTheory.Shannon.BroadcastChannel.Achievability.Assembly
import InformationTheory.Shannon.BroadcastChannel.Marton.Basic
import InformationTheory.Shannon.BroadcastChannel.Marton.ErrorAnalysis
import InformationTheory.Shannon.BroadcastChannel.Marton.MarkovCore

/-!
# Marton's inner bound — achievability

The three-tier random-coding ensemble of `Marton.ErrorAnalysis` is assembled here into a single
broadcast code.  A rate pair strictly inside Marton's region is first split into subcodebook rates
by `exists_martonRateSplit`; the covering lemma then makes the encoder's selection succeed with
high probability, the conditional AEP of `Marton.MarkovCore` bounds the transmitted-pair term of
each receiver, and the alias estimate bounds every other message row.  A pigeonhole over the
ensemble turns the averaged bound into one deterministic code.

Three radii are nested rather than shared: the decoders test weak joint typicality at radius `ε`,
the transmitted blocks are pinned at `martonStrongRadius`, and the encoder selects a pair pinned at
`martonCoveringRadius`, the smallest of the three.  The two receivers induce unrelated covering
radii, so the selection runs at their minimum and is reopened to either one by
`jointStronglyTypicalSet_mono_radius`.

## Main statements

* `marton_achievability` — a rate pair satisfying the three strict Marton inequalities is
  achievable over a general two-receiver broadcast channel.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.MAC
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [DecidableEq V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [DecidableEq V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-! ### Generic finite-sum plumbing -/

/-- Reading the outer two tiers of a three-tier weighted average as one product tier. -/
private lemma sum_prodTier_eq {κ₁ κ₂ κX : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype κX]
    (w₁ : κ₁ → ℝ) (w₂ : κ₂ → ℝ) (wX : κ₁ → κ₂ → κX → ℝ) (f : κ₁ → κ₂ → κX → ℝ) :
    ∑ c : κ₁ × κ₂, w₁ c.1 * w₂ c.2 * ∑ cX : κX, wX c.1 c.2 cX * f c.1 c.2 cX
      = ∑ c₁ : κ₁, w₁ c₁ * ∑ c₂ : κ₂, w₂ c₂ * ∑ cX : κX, wX c₁ c₂ cX * f c₁ c₂ cX := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c₁ _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c₂ _ ↦ by ring

private lemma sum_three_tier_add {κ₁ κ₂ κX : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype κX]
    (w₁ : κ₁ → ℝ) (w₂ : κ₂ → ℝ) (wX : κ₁ → κ₂ → κX → ℝ) (f g : κ₁ → κ₂ → κX → ℝ) :
    ∑ c₁ : κ₁, w₁ c₁ * ∑ c₂ : κ₂, w₂ c₂
        * ∑ cX : κX, wX c₁ c₂ cX * (f c₁ c₂ cX + g c₁ c₂ cX)
      = (∑ c₁ : κ₁, w₁ c₁ * ∑ c₂ : κ₂, w₂ c₂ * ∑ cX : κX, wX c₁ c₂ cX * f c₁ c₂ cX)
        + ∑ c₁ : κ₁, w₁ c₁ * ∑ c₂ : κ₂, w₂ c₂ * ∑ cX : κX, wX c₁ c₂ cX * g c₁ c₂ cX := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c₁ _ ↦ ?_
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c₂ _ ↦ ?_
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun cX _ ↦ by ring

/-- A two-factor weighted average of a payoff dominated by a constant off a bad set. -/
private lemma sum_pair_le_add_prodReal {A B : Type*}
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ₁ : Measure A) [IsProbabilityMeasure μ₁] (μ₂ : Measure B) [IsProbabilityMeasure μ₂]
    (S : Set (A × B)) (F : A → B → ℝ) {t : ℝ}
    (hF : ∀ a b, F a b ≤ t + S.indicator (fun _ ↦ (1 : ℝ)) (a, b)) :
    ∑ a : A, μ₁.real {a} * ∑ b : B, μ₂.real {b} * F a b ≤ t + (μ₁.prod μ₂).real S := by
  classical
  have hslice : ∀ a : A, ∑ b : B, μ₂.real {b} * S.indicator (fun _ ↦ (1 : ℝ)) (a, b)
      = μ₂.real {b | (a, b) ∈ S} := by
    intro a
    rw [measureReal_eq_sum_ite μ₂ {b | (a, b) ∈ S}]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    by_cases hb : (a, b) ∈ S <;> simp [hb, Set.mem_setOf_eq]
  have hstep : ∀ a : A, ∑ b : B, μ₂.real {b} * (t + S.indicator (fun _ ↦ (1 : ℝ)) (a, b))
      = t + μ₂.real {b | (a, b) ∈ S} := by
    intro a
    rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) ↦
      (by ring : μ₂.real {b} * (t + S.indicator (fun _ ↦ (1 : ℝ)) (a, b))
        = μ₂.real {b} * t + μ₂.real {b} * S.indicator (fun _ ↦ (1 : ℝ)) (a, b)),
      Finset.sum_add_distrib, ← Finset.sum_mul, sum_measureReal_singleton_univ_eq_one, one_mul,
      hslice a]
  calc ∑ a : A, μ₁.real {a} * ∑ b : B, μ₂.real {b} * F a b
      ≤ ∑ a : A, μ₁.real {a}
          * ∑ b : B, μ₂.real {b} * (t + S.indicator (fun _ ↦ (1 : ℝ)) (a, b)) := by
        refine Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
        exact Finset.sum_le_sum fun b _ ↦ mul_le_mul_of_nonneg_left (hF a b) measureReal_nonneg
    _ = ∑ a : A, μ₁.real {a} * (t + μ₂.real {b | (a, b) ∈ S}) :=
        Finset.sum_congr rfl fun a _ ↦ by rw [hstep a]
    _ = t + (μ₁.prod μ₂).real S := by
        rw [mac_prodReal_eq_slice_sum μ₁ μ₂ S,
          Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) ↦
            (by ring : μ₁.real {a} * (t + μ₂.real {b | (a, b) ∈ S})
              = μ₁.real {a} * t + μ₁.real {a} * μ₂.real {b | (a, b) ∈ S}),
          Finset.sum_add_distrib, ← Finset.sum_mul, sum_measureReal_singleton_univ_eq_one, one_mul]

/-! ### Aggregating one receiver's Bonferroni decomposition over the ensemble -/

/-- Fold a per-message decomposition into a transmitted-pair term and an alias family into a
closed-form bound on the two-tier weighted ensemble average. -/
private lemma marton_two_tier_aggregate {κU κX ι : Type*} [Fintype κU] [Fintype κX]
    {M₁ M₂ : ℕ}
    (wU : κU → ℝ) (wX : κU → κX → ℝ)
    (hwU : ∀ cU, 0 ≤ wU cU) (hwX : ∀ cU cX, 0 ≤ wX cU cX)
    (P : κU → κX → ℝ)
    (E0 : Fin M₁ × Fin M₂ → κU → κX → ℝ)
    (Ea : Fin M₁ × Fin M₂ → ι → κU → κX → ℝ)
    (s : Fin M₁ × Fin M₂ → Finset ι)
    {A e k : ℝ} (he : 0 ≤ e) (hk : ∀ m, ((s m).card : ℝ) ≤ k)
    {Minv : ℝ} (hMinv : 0 ≤ Minv) (hMinvM : Minv * ((M₁ * M₂ : ℕ) : ℝ) = 1)
    (hP : ∀ cU cX, P cU cX ≤ Minv * ∑ m : Fin M₁ × Fin M₂,
        (E0 m cU cX + ∑ q ∈ s m, Ea m q cU cX))
    (hE0 : ∀ m, ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * E0 m cU cX ≤ A)
    (hEa : ∀ m, ∀ q ∈ s m, ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Ea m q cU cX ≤ e) :
    ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * P cU cX ≤ A + k * e := by
  classical
  refine le_trans (bc_weighted_two_tier_mono wU wX hwU hwX _ _ hP) ?_
  have hdist : ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * (Minv * ∑ m : Fin M₁ × Fin M₂,
        (E0 m cU cX + ∑ q ∈ s m, Ea m q cU cX))
      = Minv * ∑ m : Fin M₁ × Fin M₂,
          ((∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * E0 m cU cX)
            + ∑ q ∈ s m, ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Ea m q cU cX) := by
    rw [bc_weighted_two_tier_const_mul wU wX Minv]
    congr 1
    rw [bc_weighted_two_tier_sum_index (Finset.univ : Finset (Fin M₁ × Fin M₂)) wU wX
      (fun m cU cX ↦ E0 m cU cX + ∑ q ∈ s m, Ea m q cU cX)]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [bc_weighted_two_tier_add wU wX,
      bc_weighted_two_tier_sum_index (s m) wU wX (fun q cU cX ↦ Ea m q cU cX)]
  rw [hdist]
  have hbound : ∀ m : Fin M₁ × Fin M₂,
      ((∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * E0 m cU cX)
        + ∑ q ∈ s m, ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Ea m q cU cX)
      ≤ A + k * e := by
    intro m
    have hw : ∑ q ∈ s m, ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Ea m q cU cX ≤ k * e := by
      calc ∑ q ∈ s m, ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Ea m q cU cX
          ≤ ∑ _q ∈ s m, e := Finset.sum_le_sum (hEa m)
        _ = ((s m).card : ℝ) * e := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ k * e := mul_le_mul_of_nonneg_right (hk m) he
    linarith [hE0 m]
  calc Minv * ∑ m : Fin M₁ × Fin M₂,
          ((∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * E0 m cU cX)
            + ∑ q ∈ s m, ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Ea m q cU cX)
      ≤ Minv * ∑ _m : Fin M₁ × Fin M₂, (A + k * e) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ ↦ hbound m) hMinv
    _ = A + k * e := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, hMinvM, one_mul]

/-- The three-tier reading of `marton_two_tier_aggregate`, with the two auxiliary tiers kept
apart so that the ensemble bounds of `Marton.ErrorAnalysis` apply as stated. -/
private lemma marton_three_tier_aggregate {κ₁ κ₂ κX ι : Type*}
    [Fintype κ₁] [Fintype κ₂] [Fintype κX] {M₁ M₂ : ℕ}
    (w₁ : κ₁ → ℝ) (w₂ : κ₂ → ℝ) (wX : κ₁ → κ₂ → κX → ℝ)
    (hw₁ : ∀ c, 0 ≤ w₁ c) (hw₂ : ∀ c, 0 ≤ w₂ c) (hwX : ∀ c₁ c₂ cX, 0 ≤ wX c₁ c₂ cX)
    (P : κ₁ → κ₂ → κX → ℝ)
    (E0 : Fin M₁ × Fin M₂ → κ₁ → κ₂ → κX → ℝ)
    (Ea : Fin M₁ × Fin M₂ → ι → κ₁ → κ₂ → κX → ℝ)
    (s : Fin M₁ × Fin M₂ → Finset ι)
    {A e k : ℝ} (he : 0 ≤ e) (hk : ∀ m, ((s m).card : ℝ) ≤ k)
    {Minv : ℝ} (hMinv : 0 ≤ Minv) (hMinvM : Minv * ((M₁ * M₂ : ℕ) : ℝ) = 1)
    (hP : ∀ c₁ c₂ cX, P c₁ c₂ cX ≤ Minv * ∑ m : Fin M₁ × Fin M₂,
        (E0 m c₁ c₂ cX + ∑ q ∈ s m, Ea m q c₁ c₂ cX))
    (hE0 : ∀ m, ∑ c₁ : κ₁, w₁ c₁ * ∑ c₂ : κ₂, w₂ c₂ * ∑ cX : κX, wX c₁ c₂ cX * E0 m c₁ c₂ cX ≤ A)
    (hEa : ∀ m, ∀ q ∈ s m,
      ∑ c₁ : κ₁, w₁ c₁ * ∑ c₂ : κ₂, w₂ c₂ * ∑ cX : κX, wX c₁ c₂ cX * Ea m q c₁ c₂ cX ≤ e) :
    ∑ c₁ : κ₁, w₁ c₁ * ∑ c₂ : κ₂, w₂ c₂ * ∑ cX : κX, wX c₁ c₂ cX * P c₁ c₂ cX
      ≤ A + k * e := by
  rw [← sum_prodTier_eq w₁ w₂ wX P]
  refine marton_two_tier_aggregate (κU := κ₁ × κ₂) (fun c ↦ w₁ c.1 * w₂ c.2)
    (fun c cX ↦ wX c.1 c.2 cX)
    (fun c ↦ mul_nonneg (hw₁ c.1) (hw₂ c.2)) (fun c cX ↦ hwX c.1 c.2 cX)
    (fun c cX ↦ P c.1 c.2 cX) (fun m c cX ↦ E0 m c.1 c.2 cX) (fun m q c cX ↦ Ea m q c.1 c.2 cX)
    s he hk hMinv hMinvM (fun c cX ↦ hP c.1 c.2 cX) ?_ ?_
  · intro m
    show ∑ c : κ₁ × κ₂, w₁ c.1 * w₂ c.2 * ∑ cX : κX, wX c.1 c.2 cX * E0 m c.1 c.2 cX ≤ A
    rw [sum_prodTier_eq w₁ w₂ wX (E0 m)]
    exact hE0 m
  · intro m q hq
    show ∑ c : κ₁ × κ₂, w₁ c.1 * w₂ c.2 * ∑ cX : κX, wX c.1 c.2 cX * Ea m q c.1 c.2 cX ≤ e
    rw [sum_prodTier_eq w₁ w₂ wX (Ea m q)]
    exact hEa m q hq

/-! ### The transmitted-pair term over the ensemble -/

/-- The auxiliary pair the encoder transmits is jointly strongly typical whenever the two
transmitted rows contain such a pair at all. -/
private lemma martonSelectRow_mem
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂)
    {M₁' M₂' n : ℕ} (hM₁' : 0 < M₁') (hM₂' : 0 < M₂') {ε_cov : ℝ}
    (r₁ : Fin M₁' → (Fin n → V₁)) (r₂ : Fin M₂' → (Fin n → V₂))
    (h : ∃ l : Fin M₁' × Fin M₂', (r₁ l.1, r₂ l.2) ∈
      jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε_cov) :
    (r₁ (martonSelectRow pV K W hM₁' hM₂' ε_cov r₁ r₂).1,
        r₂ (martonSelectRow pV K W hM₁' hM₂' ε_cov r₁ r₂).2) ∈
      jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε_cov := by
  unfold martonSelectRow
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- Marginalizing the input tier of the ensemble at the transmitted message pair. -/
private lemma marton_inputTier_marginal
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂)
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁' : 0 < M₁') (hM₂' : 0 < M₂') {ε_cov : ℝ}
    (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂)
    (m : Fin M₁ × Fin M₂) (g : (Fin n → α) → ℝ) :
    ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
        (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX} * g (cX m)
      = ∑ x : Fin n → α,
          (Measure.pi fun l : Fin n ↦ K (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m l,
            martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m l)).real {x} * g x := by
  have hmp : (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).map (Function.eval m)
      = Measure.pi fun l : Fin n ↦ K (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m l,
          martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m l) :=
    (measurePreserving_eval (fun m' : Fin M₁ × Fin M₂ ↦
      Measure.pi fun l : Fin n ↦
        K (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m' l,
          martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m' l)) m).map_eq
  have h1 := sum_weighted_map (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂)
    (Function.eval m) (measurable_pi_apply m) g
  rw [hmp] at h1
  exact h1

/-- Marginalizing an auxiliary tier of the ensemble to the single row it is read through. -/
private lemma marton_subcodebook_row_marginal
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
    (p : Measure V) [IsProbabilityMeasure p] {M M' n : ℕ} (i : Fin M)
    (f : (Fin M' → (Fin n → V)) → ℝ) (hf : ∀ r, 0 ≤ f r) :
    ∑ c : MartonSubcodebook M M' n V, (martonSubcodebookMeasure p M M' n).real {c} * f (c i)
      = ∑ r : Fin M' → (Fin n → V), (codebookMeasure p M' n).real {r} * f r := by
  haveI : MeasurableSingletonClass (Fin n → V) := Pi.instMeasurableSingletonClass
  have h := codebook_marginal_one (Measure.pi fun _ : Fin n ↦ p) M M' i f hf
  rw [martonSubcodebookMeasure, h]
  rfl

/-- Receiver-1 transmitted-pair term over the ensemble: the covering failure probability plus the
conditional-AEP tolerance. -/
private lemma marton_ensemble_E0₁_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁' : 0 < M₁') (hM₂' : 0 < M₂')
    {ε ε_cov tol η : ℝ} (htol : 0 ≤ tol)
    (hmono : ε_cov ≤ martonCoveringRadius pV K W ε)
    (hsel : ∀ (v₁ : Fin n → V₁) (v₂ : Fin n → V₂),
      (v₁, v₂) ∈ jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n
          (martonCoveringRadius pV K W ε) →
      ∑ x : Fin n → α, (Measure.pi fun i ↦ K (v₁ i, v₂ i)).real {x}
          * (Measure.pi fun i ↦ W (x i)).real
              { y : Fin n → β₁ × β₂ | (v₁, fun i ↦ (y i).1) ∉
                  jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε }
        ≤ tol)
    (hcover : ((codebookMeasure (pV.map Prod.fst) M₁' n).prod
          (codebookMeasure (pV.map Prod.snd) M₂' n)).real
        { c | ∀ i j, (c.1 i, c.2 j) ∉
          jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε_cov } ≤ η)
    (m : Fin M₁ × Fin M₂) :
    ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
        (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
          * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
              (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                * ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
                    (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
                      * (Measure.pi fun i ↦ W (cX m i)).real
                          { y : Fin n → β₁ × β₂ |
                            (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).1) ∉
                              jointlyTypicalSet (martonAmbientMeasure pV K W)
                                martonV₁s martonY₁s n ε }
      ≤ tol + η := by
  classical
  haveI : IsProbabilityMeasure (pV.map (Prod.fst : V₁ × V₂ → V₁)) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (pV.map (Prod.snd : V₁ × V₂ → V₂)) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  haveI : MeasurableSingletonClass (Fin M₁' → (Fin n → V₁)) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Fin M₂' → (Fin n → V₂)) := Pi.instMeasurableSingletonClass
  set Bad : Set ((Fin M₁' → (Fin n → V₁)) × (Fin M₂' → (Fin n → V₂))) :=
    { c | ∀ i j, (c.1 i, c.2 j) ∉
      jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε_cov }
    with hBad_def
  -- The transmitted-pair term reads the ensemble only through the two transmitted rows.
  set Ψ : (Fin M₁' → (Fin n → V₁)) → (Fin M₂' → (Fin n → V₂)) → ℝ := fun r₁ r₂ ↦
    ∑ x : Fin n → α,
      (Measure.pi fun l : Fin n ↦
          K (r₁ (martonSelectRow pV K W hM₁' hM₂' ε_cov r₁ r₂).1 l,
            r₂ (martonSelectRow pV K W hM₁' hM₂' ε_cov r₁ r₂).2 l)).real {x}
        * (Measure.pi fun i ↦ W (x i)).real
            { y : Fin n → β₁ × β₂ |
              (r₁ (martonSelectRow pV K W hM₁' hM₂' ε_cov r₁ r₂).1, fun i ↦ (y i).1) ∉
                jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε }
    with hΨ_def
  have hΨ_nonneg : ∀ r₁ r₂, 0 ≤ Ψ r₁ r₂ := by
    intro r₁ r₂
    simp only [hΨ_def]
    exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg
  have step1 : ∀ (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂),
      (∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
          (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
            * (Measure.pi fun i ↦ W (cX m i)).real
                { y : Fin n → β₁ × β₂ |
                  (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).1) ∉
                    jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε })
        = Ψ (c₁ m.1) (c₂ m.2) := by
    intro c₁ c₂
    have h := marton_inputTier_marginal pV K W hM₁' hM₂' (ε_cov := ε_cov) c₁ c₂ m
      (fun x ↦ (Measure.pi fun i ↦ W (x i)).real
        { y : Fin n → β₁ × β₂ |
          (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).1) ∉
            jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε })
    simp only [hΨ_def]
    exact h
  have step2 : ∀ r₁ : Fin M₁' → (Fin n → V₁),
      (∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
          (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂} * Ψ r₁ (c₂ m.2))
        = ∑ r₂ : Fin M₂' → (Fin n → V₂),
            (codebookMeasure (pV.map Prod.snd) M₂' n).real {r₂} * Ψ r₁ r₂ :=
    fun r₁ ↦ marton_subcodebook_row_marginal (pV.map Prod.snd) m.2 (Ψ r₁) (hΨ_nonneg r₁)
  have step3 := marton_subcodebook_row_marginal (pV.map Prod.fst) (M := M₁) (M' := M₁') (n := n) m.1
    (fun r₁ ↦ ∑ r₂ : Fin M₂' → (Fin n → V₂),
      (codebookMeasure (pV.map Prod.snd) M₂' n).real {r₂} * Ψ r₁ r₂)
    (fun r₁ ↦ Finset.sum_nonneg fun _ _ ↦ mul_nonneg measureReal_nonneg (hΨ_nonneg r₁ _))
  -- Whatever the two rows are, the encoder either selects a pinned pair or the rows carry none.
  have step4 : ∀ r₁ r₂, Ψ r₁ r₂ ≤ tol + Bad.indicator (fun _ ↦ (1 : ℝ)) (r₁, r₂) := by
    intro r₁ r₂
    by_cases hex : ∃ l : Fin M₁' × Fin M₂', (r₁ l.1, r₂ l.2) ∈
        jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε_cov
    · have hnotbad : (r₁, r₂) ∉ Bad := by
        obtain ⟨l, hl⟩ := hex
        intro hb
        simp only [hBad_def, Set.mem_setOf_eq] at hb
        exact hb l.1 l.2 hl
      rw [Set.indicator_of_notMem hnotbad, add_zero]
      have hmem := jointStronglyTypicalSet_mono_radius (martonAmbientMeasure pV K W)
        martonV₁s martonV₂s n hmono (martonSelectRow_mem pV K W hM₁' hM₂' r₁ r₂ hex)
      simp only [hΨ_def]
      exact hsel _ _ hmem
    · have hbad : (r₁, r₂) ∈ Bad := by
        simp only [hBad_def, Set.mem_setOf_eq]
        exact fun i j hl ↦ hex ⟨(i, j), hl⟩
      rw [Set.indicator_of_mem hbad]
      have hbnd : ∀ x : Fin n → α, (Measure.pi fun i ↦ W (x i)).real
          { y : Fin n → β₁ × β₂ | (r₁ (martonSelectRow pV K W hM₁' hM₂' ε_cov r₁ r₂).1,
              fun i ↦ (y i).1) ∉
            jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε } ≤ 1 := by
        intro x
        haveI : IsProbabilityMeasure (Measure.pi fun i ↦ W (x i)) := inferInstance
        exact le_of_le_of_eq (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))
          probReal_univ
      have hle1 : Ψ r₁ r₂ ≤ 1 := by
        simp only [hΨ_def]
        refine le_of_le_of_eq (Finset.sum_le_sum fun x _ ↦
          mul_le_mul_of_nonneg_left (hbnd x) measureReal_nonneg) ?_
        rw [← Finset.sum_mul, sum_measureReal_singleton_univ_eq_one, one_mul]
      linarith
  calc ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
          (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
            * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
                (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                  * ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
                      (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
                        * (Measure.pi fun i ↦ W (cX m i)).real
                            { y : Fin n → β₁ × β₂ |
                              (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).1) ∉
                                jointlyTypicalSet (martonAmbientMeasure pV K W)
                                  martonV₁s martonY₁s n ε }
      = ∑ r₁ : Fin M₁' → (Fin n → V₁), (codebookMeasure (pV.map Prod.fst) M₁' n).real {r₁}
          * ∑ r₂ : Fin M₂' → (Fin n → V₂),
              (codebookMeasure (pV.map Prod.snd) M₂' n).real {r₂} * Ψ r₁ r₂ := by
        rw [← step3]
        refine Finset.sum_congr rfl fun c₁ _ ↦ ?_
        rw [← step2 (c₁ m.1)]
        congr 1
        exact Finset.sum_congr rfl fun c₂ _ ↦ by rw [step1 c₁ c₂]
    _ ≤ tol + (((codebookMeasure (pV.map Prod.fst) M₁' n).prod
          (codebookMeasure (pV.map Prod.snd) M₂' n)).real Bad) :=
        sum_pair_le_add_prodReal _ _ Bad Ψ step4
    _ ≤ tol + η := by linarith [hcover]

/-- Receiver-2 transmitted-pair term over the ensemble, the mirror of
`marton_ensemble_E0₁_le`. -/
private lemma marton_ensemble_E0₂_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁' : 0 < M₁') (hM₂' : 0 < M₂')
    {ε ε_cov tol η : ℝ} (htol : 0 ≤ tol)
    (hmono : ε_cov ≤ martonCoveringRadius₂ pV K W ε)
    (hsel : ∀ (v₁ : Fin n → V₁) (v₂ : Fin n → V₂),
      (v₁, v₂) ∈ jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n
          (martonCoveringRadius₂ pV K W ε) →
      ∑ x : Fin n → α, (Measure.pi fun i ↦ K (v₁ i, v₂ i)).real {x}
          * (Measure.pi fun i ↦ W (x i)).real
              { y : Fin n → β₁ × β₂ | (v₂, fun i ↦ (y i).2) ∉
                  jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε }
        ≤ tol)
    (hcover : ((codebookMeasure (pV.map Prod.fst) M₁' n).prod
          (codebookMeasure (pV.map Prod.snd) M₂' n)).real
        { c | ∀ i j, (c.1 i, c.2 j) ∉
          jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε_cov } ≤ η)
    (m : Fin M₁ × Fin M₂) :
    ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
        (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
          * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
              (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                * ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
                    (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
                      * (Measure.pi fun i ↦ W (cX m i)).real
                          { y : Fin n → β₁ × β₂ |
                            (martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).2) ∉
                              jointlyTypicalSet (martonAmbientMeasure pV K W)
                                martonV₂s martonY₂s n ε }
      ≤ tol + η := by
  classical
  haveI : IsProbabilityMeasure (pV.map (Prod.fst : V₁ × V₂ → V₁)) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (pV.map (Prod.snd : V₁ × V₂ → V₂)) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  haveI : MeasurableSingletonClass (Fin M₁' → (Fin n → V₁)) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Fin M₂' → (Fin n → V₂)) := Pi.instMeasurableSingletonClass
  set Bad : Set ((Fin M₁' → (Fin n → V₁)) × (Fin M₂' → (Fin n → V₂))) :=
    { c | ∀ i j, (c.1 i, c.2 j) ∉
      jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε_cov }
    with hBad_def
  set Ψ : (Fin M₁' → (Fin n → V₁)) → (Fin M₂' → (Fin n → V₂)) → ℝ := fun r₁ r₂ ↦
    ∑ x : Fin n → α,
      (Measure.pi fun l : Fin n ↦
          K (r₁ (martonSelectRow pV K W hM₁' hM₂' ε_cov r₁ r₂).1 l,
            r₂ (martonSelectRow pV K W hM₁' hM₂' ε_cov r₁ r₂).2 l)).real {x}
        * (Measure.pi fun i ↦ W (x i)).real
            { y : Fin n → β₁ × β₂ |
              (r₂ (martonSelectRow pV K W hM₁' hM₂' ε_cov r₁ r₂).2, fun i ↦ (y i).2) ∉
                jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε }
    with hΨ_def
  have hΨ_nonneg : ∀ r₁ r₂, 0 ≤ Ψ r₁ r₂ := by
    intro r₁ r₂
    simp only [hΨ_def]
    exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg
  have step1 : ∀ (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂),
      (∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
          (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
            * (Measure.pi fun i ↦ W (cX m i)).real
                { y : Fin n → β₁ × β₂ |
                  (martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).2) ∉
                    jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε })
        = Ψ (c₁ m.1) (c₂ m.2) := by
    intro c₁ c₂
    have h := marton_inputTier_marginal pV K W hM₁' hM₂' (ε_cov := ε_cov) c₁ c₂ m
      (fun x ↦ (Measure.pi fun i ↦ W (x i)).real
        { y : Fin n → β₁ × β₂ |
          (martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).2) ∉
            jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε })
    simp only [hΨ_def]
    exact h
  have step2 : ∀ r₁ : Fin M₁' → (Fin n → V₁),
      (∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
          (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂} * Ψ r₁ (c₂ m.2))
        = ∑ r₂ : Fin M₂' → (Fin n → V₂),
            (codebookMeasure (pV.map Prod.snd) M₂' n).real {r₂} * Ψ r₁ r₂ :=
    fun r₁ ↦ marton_subcodebook_row_marginal (pV.map Prod.snd) m.2 (Ψ r₁) (hΨ_nonneg r₁)
  have step3 := marton_subcodebook_row_marginal (pV.map Prod.fst) (M := M₁) (M' := M₁') (n := n) m.1
    (fun r₁ ↦ ∑ r₂ : Fin M₂' → (Fin n → V₂),
      (codebookMeasure (pV.map Prod.snd) M₂' n).real {r₂} * Ψ r₁ r₂)
    (fun r₁ ↦ Finset.sum_nonneg fun _ _ ↦ mul_nonneg measureReal_nonneg (hΨ_nonneg r₁ _))
  have step4 : ∀ r₁ r₂, Ψ r₁ r₂ ≤ tol + Bad.indicator (fun _ ↦ (1 : ℝ)) (r₁, r₂) := by
    intro r₁ r₂
    by_cases hex : ∃ l : Fin M₁' × Fin M₂', (r₁ l.1, r₂ l.2) ∈
        jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε_cov
    · have hnotbad : (r₁, r₂) ∉ Bad := by
        obtain ⟨l, hl⟩ := hex
        intro hb
        simp only [hBad_def, Set.mem_setOf_eq] at hb
        exact hb l.1 l.2 hl
      rw [Set.indicator_of_notMem hnotbad, add_zero]
      have hmem := jointStronglyTypicalSet_mono_radius (martonAmbientMeasure pV K W)
        martonV₁s martonV₂s n hmono (martonSelectRow_mem pV K W hM₁' hM₂' r₁ r₂ hex)
      simp only [hΨ_def]
      exact hsel _ _ hmem
    · have hbad : (r₁, r₂) ∈ Bad := by
        simp only [hBad_def, Set.mem_setOf_eq]
        exact fun i j hl ↦ hex ⟨(i, j), hl⟩
      rw [Set.indicator_of_mem hbad]
      have hbnd : ∀ x : Fin n → α, (Measure.pi fun i ↦ W (x i)).real
          { y : Fin n → β₁ × β₂ | (r₂ (martonSelectRow pV K W hM₁' hM₂' ε_cov r₁ r₂).2,
              fun i ↦ (y i).2) ∉
            jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε } ≤ 1 := by
        intro x
        haveI : IsProbabilityMeasure (Measure.pi fun i ↦ W (x i)) := inferInstance
        exact le_of_le_of_eq (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))
          probReal_univ
      have hle1 : Ψ r₁ r₂ ≤ 1 := by
        simp only [hΨ_def]
        refine le_of_le_of_eq (Finset.sum_le_sum fun x _ ↦
          mul_le_mul_of_nonneg_left (hbnd x) measureReal_nonneg) ?_
        rw [← Finset.sum_mul, sum_measureReal_singleton_univ_eq_one, one_mul]
      linarith
  calc ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
          (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
            * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
                (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                  * ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
                      (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
                        * (Measure.pi fun i ↦ W (cX m i)).real
                            { y : Fin n → β₁ × β₂ |
                              (martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).2) ∉
                                jointlyTypicalSet (martonAmbientMeasure pV K W)
                                  martonV₂s martonY₂s n ε }
      = ∑ r₁ : Fin M₁' → (Fin n → V₁), (codebookMeasure (pV.map Prod.fst) M₁' n).real {r₁}
          * ∑ r₂ : Fin M₂' → (Fin n → V₂),
              (codebookMeasure (pV.map Prod.snd) M₂' n).real {r₂} * Ψ r₁ r₂ := by
        rw [← step3]
        refine Finset.sum_congr rfl fun c₁ _ ↦ ?_
        rw [← step2 (c₁ m.1)]
        congr 1
        exact Finset.sum_congr rfl fun c₂ _ ↦ by rw [step1 c₁ c₂]
    _ ≤ tol + (((codebookMeasure (pV.map Prod.fst) M₁' n).prod
          (codebookMeasure (pV.map Prod.snd) M₂' n)).real Bad) :=
        sum_pair_le_add_prodReal _ _ Bad Ψ step4
    _ ≤ tol + η := by linarith [hcover]

/-! ### Per-receiver ensemble averages -/

private lemma marton_random_codebook_average₁_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₁' : 0 < M₁') (hM₂' : 0 < M₂')
    {ε ε_cov tol η : ℝ} (htol : 0 ≤ tol)
    (hmono : ε_cov ≤ martonCoveringRadius pV K W ε)
    (hsel : ∀ (v₁ : Fin n → V₁) (v₂ : Fin n → V₂),
      (v₁, v₂) ∈ jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n
          (martonCoveringRadius pV K W ε) →
      ∑ x : Fin n → α, (Measure.pi fun i ↦ K (v₁ i, v₂ i)).real {x}
          * (Measure.pi fun i ↦ W (x i)).real
              { y : Fin n → β₁ × β₂ | (v₁, fun i ↦ (y i).1) ∉
                  jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε }
        ≤ tol)
    (hcover : ((codebookMeasure (pV.map Prod.fst) M₁' n).prod
          (codebookMeasure (pV.map Prod.snd) M₂' n)).real
        { c | ∀ i j, (c.1 i, c.2 j) ∉
          jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε_cov } ≤ η) :
    ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
        (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
          * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
              (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                * ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
                    (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
                      * ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₁
                          W).toReal
      ≤ (tol + η)
        + ((M₁ : ℝ) - 1) * (M₁' : ℝ) * Real.exp (-(n : ℝ) * (martonInfo₁ pV K W - 3 * ε)) := by
  classical
  have hcard : ∀ m : Fin M₁ × Fin M₂,
      ((((Finset.univ : Finset (Fin M₁)).erase m.1) ×ˢ
        (Finset.univ : Finset (Fin M₁'))).card : ℝ) ≤ ((M₁ : ℝ) - 1) * (M₁' : ℝ) := by
    intro m
    refine le_of_eq ?_
    rw [Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Finset.card_univ, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul, Nat.cast_sub hM₁,
      Nat.cast_one]
  have hMinv : (0 : ℝ) ≤ ((M₁ * M₂ : ℕ) : ℝ)⁻¹ := by positivity
  have hMinvM : ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ((M₁ * M₂ : ℕ) : ℝ) = 1 :=
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.mul_pos hM₁ hM₂).ne')
  exact marton_three_tier_aggregate (A := tol + η)
    (e := Real.exp (-(n : ℝ) * (martonInfo₁ pV K W - 3 * ε)))
    (k := ((M₁ : ℝ) - 1) * (M₁' : ℝ)) (Minv := ((M₁ * M₂ : ℕ) : ℝ)⁻¹)
    (fun c₁ ↦ (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁})
    (fun c₂ ↦ (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂})
    (fun c₁ c₂ cX ↦ (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX})
    (fun _ ↦ measureReal_nonneg) (fun _ ↦ measureReal_nonneg) (fun _ _ _ ↦ measureReal_nonneg)
    (fun c₁ c₂ cX ↦ ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₁ W).toReal)
    (fun m c₁ c₂ cX ↦ (Measure.pi fun i ↦ W (cX m i)).real
      { y : Fin n → β₁ × β₂ |
        (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).1) ∉
          jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε })
    (fun m q c₁ _c₂ cX ↦ (Measure.pi fun i ↦ W (cX m i)).real
      { y : Fin n → β₁ × β₂ |
        (c₁ q.1 q.2, fun i ↦ (y i).1) ∈
          jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε })
    (fun m ↦ ((Finset.univ : Finset (Fin M₁)).erase m.1) ×ˢ (Finset.univ : Finset (Fin M₁')))
    (Real.exp_nonneg _) hcard hMinv hMinvM
    (fun c₁ c₂ cX ↦ marton_averageErrorProb₁_toReal_le pV K W hM₁ hM₂ hM₁' hM₂' c₁ c₂ cX)
    (fun m ↦ marton_ensemble_E0₁_le pV K W hM₁' hM₂' htol hmono hsel hcover m)
    (fun m q hq ↦ marton_random_codebook_alias₁_le pV K W hpV hK hW hM₁' hM₂' m q
      (Finset.mem_erase.mp (Finset.mem_product.mp hq).1).1)

private lemma marton_random_codebook_average₂_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₁' : 0 < M₁') (hM₂' : 0 < M₂')
    {ε ε_cov tol η : ℝ} (htol : 0 ≤ tol)
    (hmono : ε_cov ≤ martonCoveringRadius₂ pV K W ε)
    (hsel : ∀ (v₁ : Fin n → V₁) (v₂ : Fin n → V₂),
      (v₁, v₂) ∈ jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n
          (martonCoveringRadius₂ pV K W ε) →
      ∑ x : Fin n → α, (Measure.pi fun i ↦ K (v₁ i, v₂ i)).real {x}
          * (Measure.pi fun i ↦ W (x i)).real
              { y : Fin n → β₁ × β₂ | (v₂, fun i ↦ (y i).2) ∉
                  jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε }
        ≤ tol)
    (hcover : ((codebookMeasure (pV.map Prod.fst) M₁' n).prod
          (codebookMeasure (pV.map Prod.snd) M₂' n)).real
        { c | ∀ i j, (c.1 i, c.2 j) ∉
          jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε_cov } ≤ η) :
    ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
        (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
          * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
              (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                * ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
                    (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
                      * ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₂
                          W).toReal
      ≤ (tol + η)
        + ((M₂ : ℝ) - 1) * (M₂' : ℝ) * Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε)) := by
  classical
  have hcard : ∀ m : Fin M₁ × Fin M₂,
      ((((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
        (Finset.univ : Finset (Fin M₂'))).card : ℝ) ≤ ((M₂ : ℝ) - 1) * (M₂' : ℝ) := by
    intro m
    refine le_of_eq ?_
    rw [Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Finset.card_univ, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul, Nat.cast_sub hM₂,
      Nat.cast_one]
  have hMinv : (0 : ℝ) ≤ ((M₁ * M₂ : ℕ) : ℝ)⁻¹ := by positivity
  have hMinvM : ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ((M₁ * M₂ : ℕ) : ℝ) = 1 :=
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.mul_pos hM₁ hM₂).ne')
  exact marton_three_tier_aggregate (A := tol + η)
    (e := Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε)))
    (k := ((M₂ : ℝ) - 1) * (M₂' : ℝ)) (Minv := ((M₁ * M₂ : ℕ) : ℝ)⁻¹)
    (fun c₁ ↦ (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁})
    (fun c₂ ↦ (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂})
    (fun c₁ c₂ cX ↦ (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX})
    (fun _ ↦ measureReal_nonneg) (fun _ ↦ measureReal_nonneg) (fun _ _ _ ↦ measureReal_nonneg)
    (fun c₁ c₂ cX ↦ ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₂ W).toReal)
    (fun m c₁ c₂ cX ↦ (Measure.pi fun i ↦ W (cX m i)).real
      { y : Fin n → β₁ × β₂ |
        (martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).2) ∉
          jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε })
    (fun m q _c₁ c₂ cX ↦ (Measure.pi fun i ↦ W (cX m i)).real
      { y : Fin n → β₁ × β₂ |
        (c₂ q.1 q.2, fun i ↦ (y i).2) ∈
          jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε })
    (fun m ↦ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ (Finset.univ : Finset (Fin M₂')))
    (Real.exp_nonneg _) hcard hMinv hMinvM
    (fun c₁ c₂ cX ↦ marton_averageErrorProb₂_toReal_le pV K W hM₁ hM₂ hM₁' hM₂' c₁ c₂ cX)
    (fun m ↦ marton_ensemble_E0₂_le pV K W hM₁' hM₂' htol hmono hsel hcover m)
    (fun m q hq ↦ marton_random_codebook_alias₂_le pV K W hpV hK hW hM₁' hM₂' m q
      (Finset.mem_erase.mp (Finset.mem_product.mp hq).1).1)

/-! ### From the ensemble to one code -/

/-- The three-tier reading of `bc_two_tier_pigeonhole`: the outer two tiers are bundled into one
product tier weighted by the product of their laws. -/
private lemma marton_three_tier_pigeonhole {κ₁ κ₂ κX : Type*}
    [Fintype κ₁] [Fintype κ₂] [Fintype κX]
    (w₁ : κ₁ → ℝ) (w₂ : κ₂ → ℝ) (wX : κ₁ → κ₂ → κX → ℝ) (val : κ₁ → κ₂ → κX → ℝ)
    (hw₁ : ∀ c, 0 ≤ w₁ c) (hw₂ : ∀ c, 0 ≤ w₂ c) (hwX : ∀ c₁ c₂ cX, 0 ≤ wX c₁ c₂ cX)
    (hw₁sum : ∑ c : κ₁, w₁ c = 1) (hw₂sum : ∑ c : κ₂, w₂ c = 1)
    (hwXsum : ∀ c₁ c₂, ∑ cX : κX, wX c₁ c₂ cX = 1)
    (B : ℝ)
    (h_avg : ∑ c₁ : κ₁, w₁ c₁ * ∑ c₂ : κ₂, w₂ c₂ * ∑ cX : κX, wX c₁ c₂ cX * val c₁ c₂ cX ≤ B) :
    ∃ (c₁ : κ₁) (c₂ : κ₂) (cX : κX), val c₁ c₂ cX ≤ B := by
  rw [← sum_prodTier_eq w₁ w₂ wX val] at h_avg
  have hwUsum : ∑ c : κ₁ × κ₂, w₁ c.1 * w₂ c.2 = 1 := by
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun c₁ (_ : c₁ ∈ Finset.univ) ↦
      (by rw [← Finset.mul_sum, hw₂sum, mul_one] : ∑ c₂ : κ₂, w₁ c₁ * w₂ c₂ = w₁ c₁)]
    exact hw₁sum
  obtain ⟨cU, cX, h⟩ := bc_two_tier_pigeonhole (κU := κ₁ × κ₂)
    (fun c ↦ w₁ c.1 * w₂ c.2) (fun c cX ↦ wX c.1 c.2 cX) (fun c cX ↦ val c.1 c.2 cX)
    (fun c ↦ mul_nonneg (hw₁ c.1) (hw₂ c.2)) (fun c cX ↦ hwX c.1 c.2 cX)
    hwUsum (fun c ↦ hwXsum c.1 c.2) B h_avg
  exact ⟨cU.1, cU.2, cX, h⟩

private lemma marton_exists_codebook_le_avg
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₁' : 0 < M₁') (hM₂' : 0 < M₂')
    {ε ε_cov B : ℝ}
    (h_avg : ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
        (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
          * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
              (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                * ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
                    (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
                      * (((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₁
                            W).toReal
                        + ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₂
                            W).toReal) ≤ B) :
    ∃ (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂)
      (cX : Fin M₁ × Fin M₂ → (Fin n → α)),
      ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₁ W).toReal
        + ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₂ W).toReal ≤ B := by
  classical
  haveI : IsProbabilityMeasure (pV.map (Prod.fst : V₁ × V₂ → V₁)) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (pV.map (Prod.snd : V₁ × V₂ → V₂)) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  haveI : MeasurableSingletonClass (MartonSubcodebook M₁ M₁' n V₁) :=
    Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (MartonSubcodebook M₂ M₂' n V₂) :=
    Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Fin M₁ × Fin M₂ → (Fin n → α)) :=
    Pi.instMeasurableSingletonClass
  exact marton_three_tier_pigeonhole
    (fun c₁ ↦ (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁})
    (fun c₂ ↦ (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂})
    (fun c₁ c₂ cX ↦ (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX})
    (fun c₁ c₂ cX ↦
      ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₁ W).toReal
        + ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₂ W).toReal)
    (fun _ ↦ measureReal_nonneg) (fun _ ↦ measureReal_nonneg) (fun _ _ _ ↦ measureReal_nonneg)
    (sum_measureReal_singleton_univ_eq_one _) (sum_measureReal_singleton_univ_eq_one _)
    (fun _ _ ↦ sum_measureReal_singleton_univ_eq_one _) B h_avg

/-! ### Headline -/

/-- Achievability of Marton's inner bound for a two-receiver broadcast channel with private
messages.  For auxiliary variables with joint law `pV`, an input kernel `K` and a channel `W`, a
rate pair obeying the three strict inequalities

* `R₁ < I(V₁; Y₁)`,
* `R₂ < I(V₂; Y₂)`,
* `R₁ + R₂ < I(V₁; Y₁) + I(V₂; Y₂) − I(V₁; V₂)`

is achievable: at every large enough block length there is a `BroadcastCode` whose two average
error probabilities are both below any prescribed `ε'`.

The input is a general kernel `K : Kernel (V₁ × V₂) α` rather than a deterministic map
`x = f(v₁, v₂)`, so the textbook statement for a deterministic input is not a direct corollary:
a deterministic kernel puts no mass on inputs off its image and therefore violates the
full-support hypothesis `hK` that every typicality estimate in this development requires.  The
rate region is the same either way.

The hypotheses `hpV`, `hK` and `hW` are full-support regularity preconditions, shared with
`marton_strong_mutual_covering` and with `bc_achievability`, and carry no part of the coding
argument.  No positivity of the rates is assumed: a nonpositive rate only asks for a single
message, `⌈exp (n R)⌉₊ = 1`, which the construction supplies as well.

No typicality radius appears in the statement, and the construction uses three nested ones rather
than a single shared one: the two decoders test weak joint typicality at a radius `ε`, the
transmitted blocks are pinned at the strictly smaller `martonStrongRadius`, and the encoder
selects a pair pinned at the smaller `martonCoveringRadius` again.

@audit:ok -/
@[entry_point]
theorem marton_achievability
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {R₁ R₂ : ℝ}
    (hR₁lt : R₁ < martonInfo₁ pV K W) (hR₂lt : R₂ < martonInfo₂ pV K W)
    (hRsum : R₁ + R₂ < martonInfo₁ pV K W + martonInfo₂ pV K W - martonInfoV₁V₂ pV K W)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M₁ M₂ : ℕ) (_hM₁ : ⌈Real.exp ((n : ℝ) * R₁)⌉₊ ≤ M₁)
        (_hM₂ : ⌈Real.exp ((n : ℝ) * R₂)⌉₊ ≤ M₂)
        (c : BroadcastCode M₁ M₂ n α β₁ β₂),
        (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε' := by
  classical
  obtain ⟨R₁', R₂', hR₁'pos, hR₂'pos, hcovR, hdec₁, hdec₂⟩ :=
    exists_martonRateSplit hR₁lt hR₂lt hRsum
  -- The decoding radius, sized by the slack the two decoding constraints leave.
  set ε : ℝ := min ((martonInfo₁ pV K W - R₁ - R₁') / 6)
    ((martonInfo₂ pV K W - R₂ - R₂') / 6) with hε_def
  have hεA : ε ≤ (martonInfo₁ pV K W - R₁ - R₁') / 6 := min_le_left _ _
  have hεB : ε ≤ (martonInfo₂ pV K W - R₂ - R₂') / 6 := min_le_right _ _
  have hε_pos : 0 < ε := lt_min (by linarith) (by linarith)
  have hgap₁ : 0 < martonInfo₁ pV K W - (R₁' + R₁) - 3 * ε := by linarith
  have hgap₂ : 0 < martonInfo₂ pV K W - (R₂' + R₂) - 3 * ε := by linarith
  have hCnn : 0 ≤ martonCoveringBandConst pV K W := martonCoveringBandConst_nonneg pV K W
  -- The selection radius: small enough for the covering rates and below both covering radii.
  set ε_cov : ℝ :=
    min (min (min ((R₁' + R₂' - martonInfoV₁V₂ pV K W)
          / (2 * (martonCoveringBandConst pV K W + 3)))
        (R₁' / (2 * (4 * martonCoveringBandConst pV K W + 6))))
      (R₂' / (2 * (4 * martonCoveringBandConst pV K W + 6))))
      (min (martonCoveringRadius pV K W ε) (martonCoveringRadius₂ pV K W ε)) with hεcov_def
  have hcovA : ε_cov ≤ (R₁' + R₂' - martonInfoV₁V₂ pV K W)
      / (2 * (martonCoveringBandConst pV K W + 3)) :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hcovB : ε_cov ≤ R₁' / (2 * (4 * martonCoveringBandConst pV K W + 6)) :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hcovC : ε_cov ≤ R₂' / (2 * (4 * martonCoveringBandConst pV K W + 6)) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hcovD : ε_cov ≤ martonCoveringRadius pV K W ε :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hcovE : ε_cov ≤ martonCoveringRadius₂ pV K W ε :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hεcov_pos : 0 < ε_cov := by
    rw [hεcov_def]
    exact lt_min (lt_min (lt_min (div_pos (by linarith) (by linarith))
        (div_pos hR₁'pos (by linarith))) (div_pos hR₂'pos (by linarith)))
      (lt_min (martonCoveringRadius_pos pV K W hε_pos)
        (martonCoveringRadius₂_pos pV K W hε_pos))
  have hcov1 : martonInfoV₁V₂ pV K W + (martonCoveringBandConst pV K W + 3) * ε_cov
      < R₁' + R₂' := by
    have h := (le_div_iff₀ (show (0:ℝ) < 2 * (martonCoveringBandConst pV K W + 3) by
      linarith)).mp hcovA
    rw [show ε_cov * (2 * (martonCoveringBandConst pV K W + 3))
      = 2 * ((martonCoveringBandConst pV K W + 3) * ε_cov) from by ring] at h
    linarith
  have hcov2 : (4 * martonCoveringBandConst pV K W + 6) * ε_cov < R₁' := by
    have h := (le_div_iff₀ (show (0:ℝ) < 2 * (4 * martonCoveringBandConst pV K W + 6) by
      linarith)).mp hcovB
    rw [show ε_cov * (2 * (4 * martonCoveringBandConst pV K W + 6))
      = 2 * ((4 * martonCoveringBandConst pV K W + 6) * ε_cov) from by ring] at h
    linarith
  have hcov3 : (4 * martonCoveringBandConst pV K W + 6) * ε_cov < R₂' := by
    have h := (le_div_iff₀ (show (0:ℝ) < 2 * (4 * martonCoveringBandConst pV K W + 6) by
      linarith)).mp hcovC
    rw [show ε_cov * (2 * (4 * martonCoveringBandConst pV K W + 6))
      = 2 * ((4 * martonCoveringBandConst pV K W + 6) * ε_cov) from by ring] at h
    linarith
  -- The six vanishing contributions, each below `ε' / 8`.
  obtain ⟨Ncov, hNcov⟩ := meas_marton_codebook_no_jointStronglyTypicalPair_lt pV K W hpV hK hW
    (ε := ε_cov) (η := ε' / 8) hεcov_pos (by linarith) hcov1 hcov2 hcov3
  obtain ⟨Nsel₁, hNsel₁⟩ := marton_condAEP_selected_avg_le pV K W hε_pos
    (show (0:ℝ) < ε' / 8 by linarith)
  obtain ⟨Nsel₂, hNsel₂⟩ := marton_condAEP_selected_avg₂_le pV K W hε_pos
    (show (0:ℝ) < ε' / 8 by linarith)
  obtain ⟨Na₁, hNa₁⟩ := bc_Ec_lt_of_rate (Ijoint := martonInfo₁ pV K W) (R₁ := R₁') (R₂ := R₁)
    (ε := ε) (ε' := ε' / 8) hR₁'pos.le hgap₁ (by linarith)
  obtain ⟨Na₂, hNa₂⟩ := bc_Ec_lt_of_rate (Ijoint := martonInfo₂ pV K W) (R₁ := R₂') (R₂ := R₂)
    (ε := ε) (ε' := ε' / 8) hR₂'pos.le hgap₂ (by linarith)
  refine ⟨max (max Ncov Nsel₁) (max Nsel₂ (max Na₁ Na₂)), fun n hn ↦ ?_⟩
  have hcover := (hNcov n (by omega)).le
  have halias₁ := hNa₁ n (by omega)
  have halias₂ := hNa₂ n (by omega)
  have hsel₁ := hNsel₁ n (by omega)
  have hsel₂ := hNsel₂ n (by omega)
  set M₁ : ℕ := ⌈Real.exp ((n : ℝ) * R₁)⌉₊ with hM₁_def
  set M₂ : ℕ := ⌈Real.exp ((n : ℝ) * R₂)⌉₊ with hM₂_def
  set M₁' : ℕ := ⌈Real.exp ((n : ℝ) * R₁')⌉₊ with hM₁'_def
  set M₂' : ℕ := ⌈Real.exp ((n : ℝ) * R₂')⌉₊ with hM₂'_def
  have hM₁pos : 0 < M₁ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hM₂pos : 0 < M₂ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hM₁'pos : 0 < M₁' := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hM₂'pos : 0 < M₂' := Nat.ceil_pos.mpr (Real.exp_pos _)
  have h_avg₁ := marton_random_codebook_average₁_le pV K W hpV hK hW hM₁pos hM₂pos hM₁'pos hM₂'pos
    (show (0:ℝ) ≤ ε' / 8 by linarith) hcovD hsel₁ hcover
  have h_avg₂ := marton_random_codebook_average₂_le pV K W hpV hK hW hM₁pos hM₂pos hM₁'pos hM₂'pos
    (show (0:ℝ) ≤ ε' / 8 by linarith) hcovE hsel₂ hcover
  have hexp₁ : Real.exp (-(n : ℝ) * (martonInfo₁ pV K W - 3 * ε))
      = Real.exp ((n : ℝ) * (-(martonInfo₁ pV K W) + 3 * ε)) := by congr 1; ring
  have hexp₂ : Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε))
      = Real.exp ((n : ℝ) * (-(martonInfo₂ pV K W) + 3 * ε)) := by congr 1; ring
  set B : ℝ :=
    ((ε' / 8 + ε' / 8)
        + ((M₁ : ℝ) - 1) * (M₁' : ℝ) * Real.exp (-(n : ℝ) * (martonInfo₁ pV K W - 3 * ε)))
      + ((ε' / 8 + ε' / 8)
        + ((M₂ : ℝ) - 1) * (M₂' : ℝ) * Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε)))
    with hB_def
  have hB_lt : B < ε' := by
    rw [hB_def, hexp₁, hexp₂]
    linarith
  have h_avg_le : ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
      (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
        * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
            (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
              * ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
                  (martonInputCodebookMeasure pV K W hM₁'pos hM₂'pos ε_cov c₁ c₂).real {cX}
                    * (((martonCodebookToCode pV K W hM₁pos hM₂pos ε c₁ c₂ cX).averageErrorProb₁
                          W).toReal
                      + ((martonCodebookToCode pV K W hM₁pos hM₂pos ε c₁ c₂ cX).averageErrorProb₂
                          W).toReal) ≤ B := by
    calc _ = _ := sum_three_tier_add
            (fun c₁ ↦ (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁})
            (fun c₂ ↦ (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂})
            (fun c₁ c₂ cX ↦
              (martonInputCodebookMeasure pV K W hM₁'pos hM₂'pos ε_cov c₁ c₂).real {cX})
            (fun c₁ c₂ cX ↦
              ((martonCodebookToCode pV K W hM₁pos hM₂pos ε c₁ c₂ cX).averageErrorProb₁ W).toReal)
            (fun c₁ c₂ cX ↦
              ((martonCodebookToCode pV K W hM₁pos hM₂pos ε c₁ c₂ cX).averageErrorProb₂ W).toReal)
      _ ≤ B := by rw [hB_def]; exact add_le_add h_avg₁ h_avg₂
  obtain ⟨c₁, c₂, cX, hle⟩ := marton_exists_codebook_le_avg pV K W hM₁pos hM₂pos hM₁'pos hM₂'pos
    (B := B) h_avg_le
  have hnn₁ : 0 ≤ ((martonCodebookToCode pV K W hM₁pos hM₂pos ε c₁ c₂ cX).averageErrorProb₁
      W).toReal := ENNReal.toReal_nonneg
  have hnn₂ : 0 ≤ ((martonCodebookToCode pV K W hM₁pos hM₂pos ε c₁ c₂ cX).averageErrorProb₂
      W).toReal := ENNReal.toReal_nonneg
  exact ⟨M₁, M₂, le_refl _, le_refl _, martonCodebookToCode pV K W hM₁pos hM₂pos ε c₁ c₂ cX,
    by linarith, by linarith⟩

end InformationTheory.Shannon.BroadcastChannel.Marton

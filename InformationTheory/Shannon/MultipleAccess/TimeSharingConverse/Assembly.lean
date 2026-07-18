import InformationTheory.Shannon.MultipleAccess.TimeSharingConverse.Bridge

/-!
# Multiple access channel — time-sharing converse, CV/V assembly

The converse-half headline `mac_timesharing_converse`: an achievable rate pair in the first
quadrant lies in the closed convex hull of the union of all per-input pentagons.  Assembled from
the Fano → 0 weak-converse limit, the uniformly-shrunk rate-point construction, and the axis
casework, on top of the geometric gateway and measure bridge in `TimeSharingConverse.Bridge`.
-/

namespace InformationTheory.Shannon.MAC

open scoped BigOperators

/-! ### CV assembly (Dispatch B): Fano→0 limit + point construction + axis casework

The converse-half headline `mac_timesharing_converse`.  An achievable rate pair `(R₁, R₂)` in the
first quadrant lies in the closed convex hull of the union of all per-input pentagons.  The core is
the interior case `0 < R₁`, `0 < R₂`: for a sequence of block codes with error `→ 0` and length
`→ ∞`, the uniformly-shrunk rate point `(R₁(1−Pe) − log2/n, R₂(1−Pe) − log2/n)` lies in the hull
(per-code, via the geometric gateway `mac_avgPentagon_mem_convexHull`), and converges to `(R₁, R₂)`,
which is therefore in the *closed* hull. -/

section CVAssembly

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCodingConverseGeneral
open Filter
open scoped ENNReal Topology

variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁]
    [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂]
    [MeasurableSingletonClass α₂] [StandardBorelSpace α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
    [MeasurableSingletonClass β] [StandardBorelSpace β]
variable {M₁ M₂ n : ℕ}

/-- Per-letter mutual-information superadditivity under input independence (Dispatch A deliverable).
`I((X₁, X₂); Y) ≤ I(X₁; Y | X₂) + I(X₂; Y | X₁)`.  This is the `hsub` well-formedness hypothesis of
`mac_avgPentagon_mem_convexHull`; it is a universal geometric fact about the product input, threaded
here exactly like the existing `hac`/`hbc` corners `mac_macInfo₁/₂_le_macInfoBoth`.
Proved by the two chain-rule decompositions `I((X₁, X₂); Y) = I(X₂; Y) + I(X₁; Y | X₂)` and the
identity `I(X₂; Y | X₁) = I(X₂; Y) + I(X₁; X₂ | Y)` (the `I(X₁; X₂) = 0` term drops under the
independent product input), so `I(X₂; Y) ≤ I(X₂; Y | X₁)` and the claim follows. -/
lemma mac_perletter_superadd (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂] (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    macInfoBoth p₁ p₂ W ≤ macInfo₁ p₁ p₂ W + macInfo₂ p₁ p₂ W := by
  have hX1 : Measurable (Prod.fst : α₁ × α₂ × β → α₁) := measurable_fst
  have hX2 : Measurable (fun q : α₁ × α₂ × β ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hY : Measurable (fun q : α₁ × α₂ × β ↦ q.2.2) := measurable_snd.comp measurable_snd
  rw [macInfoBoth_eq_mutualInfo_toReal p₁ p₂ W, macInfo₁_eq_condMutualInfo_toReal p₁ p₂ W,
      macInfo₂_eq_condMutualInfo_toReal p₁ p₂ W]
  set J := macJointDistribution p₁ p₂ W with hJ
  -- Finiteness of the two corner informations.
  have hC1_ne : condMutualInfo J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1) ≠ ∞ :=
    condMutualInfo_ne_top J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1) hX1 hY hX2
  have hC2_ne : condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst ≠ ∞ :=
    condMutualInfo_ne_top J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst hX2 hY hX1
  -- Independence of the two inputs under the product law `p₁ ⊗ p₂`.
  have indep0 : mutualInfo J Prod.fst (fun q : α₁ × α₂ × β ↦ q.2.1) = 0 :=
    macJoint_mutualInfo_X1_X2_eq_zero p₁ p₂ W
  -- Chain-rule decomposition A: `I((X₁, X₂); Y) = I(X₂; Y) + I(X₁; Y | X₂)`.
  have heqA1 : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) (fun q ↦ q.2.2)
      = mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.2.1, q.1)) (fun q ↦ q.2.2) :=
    mutualInfo_map_left_measurableEquiv J (fun q : α₁ × α₂ × β ↦ (q.2.1, q.1))
      (fun q ↦ q.2.2) (hX2.prodMk hX1) hY MeasurableEquiv.prodComm
  have hchainA : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.2.1, q.1)) (fun q ↦ q.2.2)
      = mutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2)
        + condMutualInfo J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1) :=
    mutualInfo_chain_rule J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1) hX1 hY hX2
  have decompA := heqA1.trans hchainA
  -- Reshaping and chain rules feeding `I(X₂; Y) ≤ I(X₂; Y | X₁)`.
  have reshapeE : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.1, q.2.2)) (fun q ↦ q.2.1)
      = mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.2.2, q.1)) (fun q ↦ q.2.1) :=
    mutualInfo_map_left_measurableEquiv J (fun q : α₁ × α₂ × β ↦ (q.2.2, q.1))
      (fun q ↦ q.2.1) (hY.prodMk hX1) hX2 MeasurableEquiv.prodComm
  -- `I((X₁, Y); X₂) = I(X₁; X₂) + I(Y; X₂ | X₁)`.
  have chainB : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.1, q.2.2)) (fun q ↦ q.2.1)
      = mutualInfo J Prod.fst (fun q ↦ q.2.1)
        + condMutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1) Prod.fst :=
    mutualInfo_chain_rule J (fun q ↦ q.2.2) (fun q ↦ q.2.1) Prod.fst hY hX2 hX1
  -- `I((Y, X₁); X₂) = I(Y; X₂) + I(X₁; X₂ | Y)`.
  have chainD : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.2.2, q.1)) (fun q ↦ q.2.1)
      = mutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1)
        + condMutualInfo J Prod.fst (fun q ↦ q.2.1) (fun q ↦ q.2.2) :=
    mutualInfo_chain_rule J Prod.fst (fun q ↦ q.2.1) (fun q ↦ q.2.2) hX1 hX2 hY
  -- `I((Y, X₁); X₂) = I(Y; X₂ | X₁)` (the `I(X₁; X₂) = 0` term drops out).
  have e2 : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.2.2, q.1)) (fun q ↦ q.2.1)
      = condMutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1) Prod.fst := by
    rw [← reshapeE, chainB, indep0, zero_add]
  -- `I(Y; X₂ | X₁) = I(Y; X₂) + I(X₁; X₂ | Y)`.
  have hCMI : condMutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1) Prod.fst
      = mutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1)
        + condMutualInfo J Prod.fst (fun q ↦ q.2.1) (fun q ↦ q.2.2) := by
    rw [← e2, chainD]
  -- Commute to `I(X₂; Y | X₁)` (the `macInfo₂` corner form).
  have commC2 : condMutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1) Prod.fst
      = condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst :=
    condMutualInfo_comm J (fun q ↦ q.2.2) (fun q ↦ q.2.1) Prod.fst hY hX2 hX1
  have hC2 : condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst
      = mutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1)
        + condMutualInfo J Prod.fst (fun q ↦ q.2.1) (fun q ↦ q.2.2) := by
    rw [← commC2, hCMI]
  -- Conditioning increases mutual information under independence: `I(X₂; Y) ≤ I(X₂; Y | X₁)`.
  have comm2 : mutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2)
      = mutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1) :=
    mutualInfo_comm J (fun q ↦ q.2.1) (fun q ↦ q.2.2) hX2 hY
  have hSub : mutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2)
      ≤ condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst := by
    rw [hC2, comm2]
    exact self_le_add_right _ _
  -- Assemble: `I((X₁, X₂); Y) = I(X₂; Y) + I(X₁; Y | X₂) ≤ I(X₁; Y | X₂) + I(X₂; Y | X₁)`.
  have hMBle : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) (fun q ↦ q.2.2)
      ≤ condMutualInfo J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1)
        + condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst := by
    rw [decompA, add_comm (condMutualInfo J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1))
        (condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst)]
    gcongr
  rw [← ENNReal.toReal_add hC1_ne hC2_ne]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hC1_ne, hC2_ne⟩) hMBle

-- `macInfo₁_nonneg` / `macInfo₂_nonneg` / `macInfoBoth_nonneg` now live in
-- `InformationTheory.Shannon.MultipleAccess.TimeSharing` (needed there for the all-probability
-- achievability upgrade) and are inherited via the import.

/-- **Per-code shrunk-point membership** (Dispatch B analytic core).  For a length-`n` two-user code
with `2 ≤ M₁`, `2 ≤ M₂` and `⌈exp (n Rⱼ)⌉ ≤ Mⱼ`, if the uniformly-shrunk rate point
`(R₁(1−Pe) − log2/n, R₂(1−Pe) − log2/n)` (with `Pe` the average error probability) is in the first
quadrant, then it lies in the closed convex hull of all per-input pentagons.  Combines the finite-`n`
Fano bounds with the geometric gateway `mac_avgPentagon_mem_convexHull` and the per-letter
identification of Gap B′. -/
lemma mac_converse_shrunk_point_mem
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂)
    {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
    (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
    (hx1 : 0 ≤ R₁ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ))
    (hx2 : 0 ≤ R₂ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ)) :
    (R₁ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ),
     R₂ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ))
      ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  haveI : NeZero M₁ := ⟨by omega⟩
  haveI : NeZero M₂ := ⟨by omega⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hM₁R : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hcard₁
  have hM₂R : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hcard₂
  have hM₁ne : (M₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hM₂ne : (M₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- the finite-`n` converse from the code
  have h := mac_converse_from_code c W hcard₁ hcard₂
  -- per-letter product-input marginals
  set p₁ : Fin n → Measure α₁ :=
    fun i => (macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) with hp₁def
  set p₂ : Fin n → Measure α₂ :=
    fun i => (macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) with hp₂def
  have hp₁prob : ∀ i, IsProbabilityMeasure (p₁ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hp₂prob : ∀ i, IsProbabilityMeasure (p₂ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  -- abbreviate the average error and the three symbolic per-letter information sums
  set Pe := (c.averageErrorProb W).toReal with hPeDef
  set Pe₁ := MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
    (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω)) (fun p ↦ (c.decoder p.2).1) with hPe₁def
  set Pe₂ := MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
    (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω)) (fun p ↦ (c.decoder p.2).2) with hPe₂def
  set S₁ := (∑ i : Fin n, condMutualInfo (macConverseAmbient c W)
      (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) (macConverseYs i)
      (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)).toReal with hS₁def
  set S₂ := (∑ i : Fin n, condMutualInfo (macConverseAmbient c W)
      (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) (macConverseYs i)
      (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)).toReal with hS₂def
  set Sb := (∑ i : Fin n, mutualInfo (macConverseAmbient c W)
      (fun ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i))
      (macConverseYs i)).toReal with hSbdef
  -- the joint decode error equals the code's average error probability `Pe`
  have hjoint : MeasureFano.errorProb (macConverseAmbient c W)
      (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω) c.decoder = Pe :=
    mac_converse_ambient_errorProb_joint_eq c W
  -- error-probability bounds
  have hPe_0 : 0 ≤ Pe := ENNReal.toReal_nonneg
  have hPe_1 : Pe ≤ 1 := by rw [← hjoint]; exact measureReal_le_one
  have hPe1_0 : 0 ≤ Pe₁ := measureReal_nonneg
  have hPe1_1 : Pe₁ ≤ 1 := measureReal_le_one
  have hPe1_le : Pe₁ ≤ Pe := (mac_converse_ambient_errorProb_user1_le c W).trans (le_of_eq hjoint)
  have hPe2_0 : 0 ≤ Pe₂ := measureReal_nonneg
  have hPe2_1 : Pe₂ ≤ 1 := measureReal_le_one
  have hPe2_le : Pe₂ ≤ Pe := (mac_converse_ambient_errorProb_user2_le c W).trans (le_of_eq hjoint)
  -- log-slack pieces
  have hnR1 : (n : ℝ) * R₁ ≤ Real.log (M₁ : ℝ) := le_log_of_ceil_exp_le hM₁
  have hnR2 : (n : ℝ) * R₂ ≤ Real.log (M₂ : ℝ) := le_log_of_ceil_exp_le hM₂
  have hlogm1 : Real.log ((M₁ : ℝ) - 1) ≤ Real.log (M₁ : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogm2 : Real.log ((M₂ : ℝ) - 1) ≤ Real.log (M₂ : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2n_nonneg : 0 ≤ Real.log 2 / (n : ℝ) :=
    div_nonneg (le_of_lt (Real.log_pos (by norm_num))) (le_of_lt hn')
  -- user-1 clean Fano bound: `R₁(1-Pe) - log2/n ≤ S₁/n`
  have hbound1 : R₁ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ S₁ / (n : ℝ) := by
    have hb1 := h.bound₁
    have hbe1 : Real.binEntropy Pe₁ ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hprod1 : Pe₁ * Real.log ((M₁ : ℝ) - 1) ≤ Pe₁ * Real.log (M₁ : ℝ) :=
      mul_le_mul_of_nonneg_left hlogm1 hPe1_0
    have hstep1 : Real.log (M₁ : ℝ) * (1 - Pe₁) ≤ S₁ + Real.log 2 := by
      have e : Real.log (M₁ : ℝ) * (1 - Pe₁) = Real.log (M₁ : ℝ) - Pe₁ * Real.log (M₁ : ℝ) := by ring
      rw [e]; linarith [hb1, hbe1, hprod1]
    have hstep2 : (n : ℝ) * R₁ * (1 - Pe₁) ≤ Real.log (M₁ : ℝ) * (1 - Pe₁) :=
      mul_le_mul_of_nonneg_right hnR1 (by linarith)
    have hstep3 : (n : ℝ) * R₁ * (1 - Pe) ≤ (n : ℝ) * R₁ * (1 - Pe₁) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (Nat.cast_nonneg n) hR₁)
    have key1 : (n : ℝ) * R₁ * (1 - Pe) ≤ S₁ + Real.log 2 := hstep3.trans (hstep2.trans hstep1)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn',
      show R₁ * (1 - Pe) * (n : ℝ) = (n : ℝ) * R₁ * (1 - Pe) from by ring]
    exact key1
  -- user-2 clean Fano bound: `R₂(1-Pe) - log2/n ≤ S₂/n`
  have hbound2 : R₂ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ S₂ / (n : ℝ) := by
    have hb2 := h.bound₂
    have hbe2 : Real.binEntropy Pe₂ ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hprod2 : Pe₂ * Real.log ((M₂ : ℝ) - 1) ≤ Pe₂ * Real.log (M₂ : ℝ) :=
      mul_le_mul_of_nonneg_left hlogm2 hPe2_0
    have hstep1 : Real.log (M₂ : ℝ) * (1 - Pe₂) ≤ S₂ + Real.log 2 := by
      have e : Real.log (M₂ : ℝ) * (1 - Pe₂) = Real.log (M₂ : ℝ) - Pe₂ * Real.log (M₂ : ℝ) := by ring
      rw [e]; linarith [hb2, hbe2, hprod2]
    have hstep2 : (n : ℝ) * R₂ * (1 - Pe₂) ≤ Real.log (M₂ : ℝ) * (1 - Pe₂) :=
      mul_le_mul_of_nonneg_right hnR2 (by linarith)
    have hstep3 : (n : ℝ) * R₂ * (1 - Pe) ≤ (n : ℝ) * R₂ * (1 - Pe₂) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (Nat.cast_nonneg n) hR₂)
    have key2 : (n : ℝ) * R₂ * (1 - Pe) ≤ S₂ + Real.log 2 := hstep3.trans (hstep2.trans hstep1)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn',
      show R₂ * (1 - Pe) * (n : ℝ) = (n : ℝ) * R₂ * (1 - Pe) from by ring]
    exact key2
  -- sum clean Fano bound: `(R₁+R₂)(1-Pe) - log2/n ≤ Sb/n`
  have hboundS : (R₁ + R₂) * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ Sb / (n : ℝ) := by
    have hbs := h.boundSum
    rw [hjoint] at hbs
    have hbeJ : Real.binEntropy Pe ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hge4 : (4 : ℝ) ≤ ((M₁ * M₂ : ℕ) : ℝ) := by exact_mod_cast Nat.mul_le_mul hcard₁ hcard₂
    have hlogJ : Real.log (((M₁ * M₂ : ℕ) : ℝ) - 1) ≤ Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ) := by
      rw [← Real.log_mul hM₁ne hM₂ne, ← Nat.cast_mul]
      exact Real.log_le_log (by linarith) (by linarith)
    have hprodJ : Pe * Real.log (((M₁ * M₂ : ℕ) : ℝ) - 1) ≤ Pe * (Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogJ hPe_0
    have hnR12 : (n : ℝ) * (R₁ + R₂) ≤ Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ) := by
      have e : (n : ℝ) * (R₁ + R₂) = (n : ℝ) * R₁ + (n : ℝ) * R₂ := by ring
      rw [e]; linarith [hnR1, hnR2]
    have hstepS1 : (Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ)) * (1 - Pe) ≤ Sb + Real.log 2 := by
      have e : (Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ)) * (1 - Pe)
          = (Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ)) - Pe * (Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ)) := by
        ring
      rw [e]; linarith [hbs, hbeJ, hprodJ]
    have hstepS2 : (n : ℝ) * (R₁ + R₂) * (1 - Pe) ≤ (Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ)) * (1 - Pe) :=
      mul_le_mul_of_nonneg_right hnR12 (by linarith)
    have keyS : (n : ℝ) * (R₁ + R₂) * (1 - Pe) ≤ Sb + Real.log 2 := hstepS2.trans hstepS1
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn',
      show (R₁ + R₂) * (1 - Pe) * (n : ℝ) = (n : ℝ) * (R₁ + R₂) * (1 - Pe) from by ring]
    exact keyS
  -- identify the symbolic sums with the per-letter `macInfo` sums (Gap B′): distribute `.toReal`
  -- over the finite sum (each term finite on the finite alphabets) and apply the per-letter values
  have hSm1 : S₁ = ∑ i : Fin n, macInfo₁ (p₁ i) (p₂ i) W := by
    rw [hS₁def, ENNReal.toReal_sum (fun i _ => condMutualInfo_ne_top _ _ _ _
      (measurable_of_countable _) (measurable_of_countable _) (measurable_of_countable _))]
    exact Finset.sum_congr rfl (fun i _ => mac_condMI_eq_macInfo₁_at c W i)
  have hSm2 : S₂ = ∑ i : Fin n, macInfo₂ (p₁ i) (p₂ i) W := by
    rw [hS₂def, ENNReal.toReal_sum (fun i _ => condMutualInfo_ne_top _ _ _ _
      (measurable_of_countable _) (measurable_of_countable _) (measurable_of_countable _))]
    exact Finset.sum_congr rfl (fun i _ => mac_condMI_eq_macInfo₂_at c W i)
  have hSmb : Sb = ∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W := by
    rw [hSbdef, ENNReal.toReal_sum (fun i _ => mutualInfo_ne_top _ _ _
      (measurable_of_countable _) (measurable_of_countable _))]
    exact Finset.sum_congr rfl (fun i _ => mac_mutualInfo_eq_macInfoBoth_at c W i)
  -- the gateway hypotheses in `macInfo` form
  have h1 : R₁ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ (∑ i : Fin n, macInfo₁ (p₁ i) (p₂ i) W) / (n : ℝ) :=
    hSm1 ▸ hbound1
  have h2 : R₂ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ (∑ i : Fin n, macInfo₂ (p₁ i) (p₂ i) W) / (n : ℝ) :=
    hSm2 ▸ hbound2
  have hs : (R₁ * (1 - Pe) - Real.log 2 / (n : ℝ)) + (R₂ * (1 - Pe) - Real.log 2 / (n : ℝ))
      ≤ (∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W) / (n : ℝ) := by
    have hboundS' : (R₁ + R₂) * (1 - Pe) - Real.log 2 / (n : ℝ)
        ≤ (∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W) / (n : ℝ) := hSmb ▸ hboundS
    calc (R₁ * (1 - Pe) - Real.log 2 / (n : ℝ)) + (R₂ * (1 - Pe) - Real.log 2 / (n : ℝ))
        = (R₁ + R₂) * (1 - Pe) - 2 * (Real.log 2 / (n : ℝ)) := by ring
      _ ≤ (R₁ + R₂) * (1 - Pe) - Real.log 2 / (n : ℝ) := by linarith
      _ ≤ (∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W) / (n : ℝ) := hboundS'
  -- geometric gateway
  have hmem : (R₁ * (1 - Pe) - Real.log 2 / (n : ℝ), R₂ * (1 - Pe) - Real.log 2 / (n : ℝ))
      ∈ convexHull ℝ (⋃ i : Fin n,
          ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ (p₁ i) (p₂ i) W
            ∧ p.2 ≤ macInfo₂ (p₁ i) (p₂ i) W ∧ p.1 + p.2 ≤ macInfoBoth (p₁ i) (p₂ i) W}
           : Set (ℝ × ℝ))) :=
    mac_avgPentagon_mem_convexHull hn
      (fun i => macInfo₁ (p₁ i) (p₂ i) W) (fun i => macInfo₂ (p₁ i) (p₂ i) W)
      (fun i => macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₁_nonneg (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₂_nonneg (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₁_le_macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₂_le_macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_perletter_superadd (p₁ i) (p₂ i) W)
      hx1 hx2 h1 h2 hs
  -- reindex the raw per-letter union into the master probability-input union
  have hsubset : (⋃ i : Fin n,
        ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ (p₁ i) (p₂ i) W
          ∧ p.2 ≤ macInfo₂ (p₁ i) (p₂ i) W ∧ p.1 + p.2 ≤ macInfoBoth (p₁ i) (p₂ i) W}
         : Set (ℝ × ℝ)))
      ⊆ (⋃ (q₁ : Measure α₁) (q₂ : Measure α₂)
          (_ : IsProbabilityMeasure q₁) (_ : IsProbabilityMeasure q₂), macPentagon q₁ q₂ W) := by
    intro pt hpt
    rw [Set.mem_iUnion] at hpt
    obtain ⟨i, hi⟩ := hpt
    haveI := hp₁prob i; haveI := hp₂prob i
    simp only [Set.mem_iUnion]
    exact ⟨p₁ i, p₂ i, hp₁prob i, hp₂prob i, hi⟩
  exact convexHull_subset_closedConvexHull (convexHull_mono hsubset hmem)

/-- **Interior case** of the converse: for strictly positive rates, an achievable pair lies in the
closed convex hull of the per-input pentagons. -/
lemma mac_timesharing_converse_interior (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hach : MACAchievable W R₁ R₂) :
    (R₁, R₂) ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
        (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  -- for each `k`, extract a length-`nₖ ≥ k+1` code with `2 ≤ M₁, M₂` and error `< 1/(k+1)`
  have hex : ∀ k : ℕ, ∃ (nn m₁ m₂ : ℕ) (c : MACCode m₁ m₂ nn α₁ α₂ β),
      0 < nn ∧ 2 ≤ m₁ ∧ 2 ≤ m₂ ∧ (k : ℝ) + 1 ≤ (nn : ℝ)
        ∧ Nat.ceil (Real.exp ((nn : ℝ) * R₁)) ≤ m₁ ∧ Nat.ceil (Real.exp ((nn : ℝ) * R₂)) ≤ m₂
        ∧ (c.averageErrorProb W).toReal < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨N, hN⟩ := hach (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨m₁, m₂, hm₁, hm₂, c, hPe⟩ := hN (max N (k + 1)) (le_max_left _ _)
    have hnnpos : 0 < max N (k + 1) := lt_of_lt_of_le (Nat.succ_pos k) (le_max_right _ _)
    have hnge : (k : ℝ) + 1 ≤ ((max N (k + 1) : ℕ) : ℝ) := by
      have hle : k + 1 ≤ max N (k + 1) := le_max_right _ _
      calc (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((max N (k + 1) : ℕ) : ℝ) := by exact_mod_cast hle
    have hcard : ∀ R : ℝ, 0 < R → ∀ M : ℕ, Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R)) ≤ M
        → 2 ≤ M := by
      intro R hR M hM
      have hpos : (0 : ℝ) < ((max N (k + 1) : ℕ) : ℝ) * R := mul_pos (by exact_mod_cast hnnpos) hR
      have h1lt : (1 : ℝ) < Real.exp (((max N (k + 1) : ℕ) : ℝ) * R) := by
        rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]; exact Real.exp_lt_exp.mpr hpos
      have h1c : (1 : ℝ) < (Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R)) : ℝ) :=
        lt_of_lt_of_le h1lt (Nat.le_ceil _)
      have : 1 < Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R)) := by exact_mod_cast h1c
      omega
    exact ⟨max N (k + 1), m₁, m₂, c, hnnpos, hcard R₁ hR₁ m₁ hm₁, hcard R₂ hR₂ m₂ hm₂, hnge,
      hm₁, hm₂, hPe⟩
  choose nn m₁ m₂ c hnpos hcard₁ hcard₂ hnge hM₁ hM₂ hPe using hex
  -- the average error probabilities converge to `0`, hence so does `log2/nₖ`
  have hPe0 : Tendsto (fun k => ((c k).averageErrorProb W).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun k => (hPe k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hnn_top : Tendsto (fun k => (nn k : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun k => le_trans (by linarith) (hnge k)) tendsto_natCast_atTop_atTop
  have hlog0 : Tendsto (fun k => Real.log 2 / (nn k : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hnn_top
  -- each coordinate of the shrunk-rate sequence converges to `Rⱼ`
  have hf1 : Tendsto (fun k => R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))
      atTop (𝓝 R₁) := by
    have hlim : Tendsto (fun k => R₁ * (1 - ((c k).averageErrorProb W).toReal)
        - Real.log 2 / (nn k : ℝ)) atTop (𝓝 (R₁ * (1 - 0) - 0)) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hPe0)).sub hlog0
    simpa using hlim
  have hf2 : Tendsto (fun k => R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))
      atTop (𝓝 R₂) := by
    have hlim : Tendsto (fun k => R₂ * (1 - ((c k).averageErrorProb W).toReal)
        - Real.log 2 / (nn k : ℝ)) atTop (𝓝 (R₂ * (1 - 0) - 0)) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hPe0)).sub hlog0
    simpa using hlim
  have htend : Tendsto (fun k => (R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ),
      R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))) atTop (𝓝 (R₁, R₂)) :=
    hf1.prodMk_nhds hf2
  -- eventually the shrunk point is in the first quadrant
  have hpos1 : ∀ᶠ k in atTop, 0 ≤ R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ) := by
    filter_upwards [hf1.eventually (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hR₁))] with k hk
    exact le_of_lt hk
  have hpos2 : ∀ᶠ k in atTop, 0 ≤ R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ) := by
    filter_upwards [hf2.eventually (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hR₂))] with k hk
    exact le_of_lt hk
  -- eventually the shrunk point lies in the closed convex hull (via the per-code lemma)
  have hev : ∀ᶠ k in atTop, (R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ),
      R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))
      ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
    filter_upwards [hpos1, hpos2] with k hk1 hk2
    exact mac_converse_shrunk_point_mem (c k) W (hnpos k) (hcard₁ k) (hcard₂ k) hR₁.le hR₂.le
      (hM₁ k) (hM₂ k) hk1 hk2
  exact isClosed_closedConvexHull.mem_of_tendsto htend hev

/-- **User-1 finite-`n` Fano corner bound** (axis extract).  Extracts the single user-1 corner
inequality `log |M₁| ≤ ∑ᵢ I(X₁ᵢ; Yᵢ | X₂ᵢ) + h(Pe₁) + Pe₁ log(|M₁| − 1)` directly from
`mac_converse_bound₁` and `mac_singleletterize_bound₁` on the canonical ambient measure, *without*
routing through the two-user `mac_converse_from_code`.  Requires only `2 ≤ M₁`; user 2 enters only
through `NeZero M₂`, so this survives the `M₂ = 1` axis degeneracy that blocks the joint converse. -/
lemma mac_converse_from_code_bound₁
    [NeZero M₁] [NeZero M₂]
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hcard₁ : 2 ≤ M₁) :
    Real.log (M₁ : ℝ) ≤
      (∑ i : Fin n,
          condMutualInfo (macConverseAmbient c W)
              (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) (macConverseYs i)
              (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
              (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).1))
        + MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
              (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).1) * Real.log ((M₁ : ℝ) - 1) := by
  have hbound := mac_converse_bound₁ (macConverseAmbient c W) macConverseMsg₁ macConverseMsg₂
    macConverseYs c measurable_macConverseMsg₁ measurable_macConverseMsg₂ measurable_macConverseYs
    (macConverseMsg₁_uniform c W) hcard₁
  have hsingle := mac_singleletterize_bound₁ (macConverseAmbient c W) macConverseMsg₁ macConverseMsg₂
    macConverseYs c measurable_macConverseMsg₁ measurable_macConverseMsg₂ measurable_macConverseYs
    (macConverse_memorylessChannel c W) (macConverse_mutualInfo_eq_zero c W)
    (macConverse_isMarkovChain c W)
  have hfin : (∑ i : Fin n,
      condMutualInfo (macConverseAmbient c W)
        (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) (macConverseYs i)
        (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)) ≠ ∞ :=
    (ENNReal.sum_lt_top.mpr fun i _ =>
      (condMutualInfo_ne_top _ _ _ _ (measurable_of_countable _) (measurable_of_countable _)
        (measurable_of_countable _)).lt_top).ne
  have hle := ENNReal.toReal_mono hfin hsingle
  linarith [hbound, hle]

/-- **User-2 finite-`n` Fano corner bound** (axis extract).  Symmetric to
`mac_converse_from_code_bound₁`: requires only `2 ≤ M₂`, surviving the `M₁ = 1` axis degeneracy. -/
lemma mac_converse_from_code_bound₂
    [NeZero M₁] [NeZero M₂]
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hcard₂ : 2 ≤ M₂) :
    Real.log (M₂ : ℝ) ≤
      (∑ i : Fin n,
          condMutualInfo (macConverseAmbient c W)
              (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) (macConverseYs i)
              (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
              (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).2))
        + MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
              (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).2) * Real.log ((M₂ : ℝ) - 1) := by
  have hbound := mac_converse_bound₂ (macConverseAmbient c W) macConverseMsg₁ macConverseMsg₂
    macConverseYs c measurable_macConverseMsg₁ measurable_macConverseMsg₂ measurable_macConverseYs
    (macConverseMsg₂_uniform c W) hcard₂
  have hsingle := mac_singleletterize_bound₂ (macConverseAmbient c W) macConverseMsg₁ macConverseMsg₂
    macConverseYs c measurable_macConverseMsg₁ measurable_macConverseMsg₂ measurable_macConverseYs
    (macConverse_memorylessChannel c W) (macConverse_mutualInfo_eq_zero c W)
    (macConverse_isMarkovChain c W)
  have hfin : (∑ i : Fin n,
      condMutualInfo (macConverseAmbient c W)
        (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) (macConverseYs i)
        (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)) ≠ ∞ :=
    (ENNReal.sum_lt_top.mpr fun i _ =>
      (condMutualInfo_ne_top _ _ _ _ (measurable_of_countable _) (measurable_of_countable _)
        (measurable_of_countable _)).lt_top).ne
  have hle := ENNReal.toReal_mono hfin hsingle
  linarith [hbound, hle]

/-- **Per-code shrunk-point membership, axis user 1** (`R₂ = 0`).  Trimmed copy of
`mac_converse_shrunk_point_mem` for the axis point `(R₁(1−Pe) − log2/n, 0)`: uses only the user-1
Fano bound (`mac_converse_from_code_bound₁`, needing just `2 ≤ M₁`) plus per-letter nonnegativity, so
it survives the `M₂ = 1` degeneracy. -/
lemma mac_converse_shrunk_point_mem_axis1 [NeZero M₂]
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₁ : 2 ≤ M₁)
    {R₁ : ℝ} (hR₁ : 0 ≤ R₁)
    (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
    (hx1 : 0 ≤ R₁ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ)) :
    (R₁ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ), (0 : ℝ))
      ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  haveI : NeZero M₁ := ⟨by omega⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hM₁R : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hcard₁
  -- per-letter product-input marginals
  set p₁ : Fin n → Measure α₁ :=
    fun i => (macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) with hp₁def
  set p₂ : Fin n → Measure α₂ :=
    fun i => (macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) with hp₂def
  have hp₁prob : ∀ i, IsProbabilityMeasure (p₁ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hp₂prob : ∀ i, IsProbabilityMeasure (p₂ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  -- abbreviate the average error, the user-1 marginal error, and the user-1 information sum
  set Pe := (c.averageErrorProb W).toReal with hPeDef
  set Pe₁ := MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
    (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω)) (fun p ↦ (c.decoder p.2).1) with hPe₁def
  set S₁ := (∑ i : Fin n, condMutualInfo (macConverseAmbient c W)
      (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) (macConverseYs i)
      (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)).toReal with hS₁def
  -- the joint decode error equals the code's average error probability `Pe`
  have hjoint : MeasureFano.errorProb (macConverseAmbient c W)
      (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω) c.decoder = Pe :=
    mac_converse_ambient_errorProb_joint_eq c W
  have hPe_0 : 0 ≤ Pe := ENNReal.toReal_nonneg
  have hPe_1 : Pe ≤ 1 := by rw [← hjoint]; exact measureReal_le_one
  have hPe1_0 : 0 ≤ Pe₁ := measureReal_nonneg
  have hPe1_1 : Pe₁ ≤ 1 := measureReal_le_one
  have hPe1_le : Pe₁ ≤ Pe := (mac_converse_ambient_errorProb_user1_le c W).trans (le_of_eq hjoint)
  have hnR1 : (n : ℝ) * R₁ ≤ Real.log (M₁ : ℝ) := le_log_of_ceil_exp_le hM₁
  have hlogm1 : Real.log ((M₁ : ℝ) - 1) ≤ Real.log (M₁ : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2n_nonneg : 0 ≤ Real.log 2 / (n : ℝ) :=
    div_nonneg (le_of_lt (Real.log_pos (by norm_num))) (le_of_lt hn')
  -- user-1 clean Fano bound: `R₁(1-Pe) - log2/n ≤ S₁/n`
  have hbound1 : R₁ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ S₁ / (n : ℝ) := by
    have hb1 := mac_converse_from_code_bound₁ c W hcard₁
    have hbe1 : Real.binEntropy Pe₁ ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hprod1 : Pe₁ * Real.log ((M₁ : ℝ) - 1) ≤ Pe₁ * Real.log (M₁ : ℝ) :=
      mul_le_mul_of_nonneg_left hlogm1 hPe1_0
    have hstep1 : Real.log (M₁ : ℝ) * (1 - Pe₁) ≤ S₁ + Real.log 2 := by
      have e : Real.log (M₁ : ℝ) * (1 - Pe₁) = Real.log (M₁ : ℝ) - Pe₁ * Real.log (M₁ : ℝ) := by ring
      rw [e]; linarith [hb1, hbe1, hprod1]
    have hstep2 : (n : ℝ) * R₁ * (1 - Pe₁) ≤ Real.log (M₁ : ℝ) * (1 - Pe₁) :=
      mul_le_mul_of_nonneg_right hnR1 (by linarith)
    have hstep3 : (n : ℝ) * R₁ * (1 - Pe) ≤ (n : ℝ) * R₁ * (1 - Pe₁) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (Nat.cast_nonneg n) hR₁)
    have key1 : (n : ℝ) * R₁ * (1 - Pe) ≤ S₁ + Real.log 2 := hstep3.trans (hstep2.trans hstep1)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn',
      show R₁ * (1 - Pe) * (n : ℝ) = (n : ℝ) * R₁ * (1 - Pe) from by ring]
    exact key1
  -- identify the user-1 sum with the per-letter `macInfo₁` sum (Gap B′)
  have hSm1 : S₁ = ∑ i : Fin n, macInfo₁ (p₁ i) (p₂ i) W := by
    rw [hS₁def, ENNReal.toReal_sum (fun i _ => condMutualInfo_ne_top _ _ _ _
      (measurable_of_countable _) (measurable_of_countable _) (measurable_of_countable _))]
    exact Finset.sum_congr rfl (fun i _ => mac_condMI_eq_macInfo₁_at c W i)
  have h1 : R₁ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ (∑ i : Fin n, macInfo₁ (p₁ i) (p₂ i) W) / (n : ℝ) :=
    hSm1 ▸ hbound1
  -- second coordinate is `0`, so the user-2 and sum gateway bounds are nonnegativity / user-1 chained
  have h2 : (0 : ℝ) ≤ (∑ i : Fin n, macInfo₂ (p₁ i) (p₂ i) W) / (n : ℝ) := by
    refine div_nonneg (Finset.sum_nonneg fun i _ => ?_) (le_of_lt hn')
    haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₂_nonneg (p₁ i) (p₂ i) W
  have hsumle : (∑ i : Fin n, macInfo₁ (p₁ i) (p₂ i) W)
      ≤ ∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W := by
    refine Finset.sum_le_sum fun i _ => ?_
    haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₁_le_macInfoBoth (p₁ i) (p₂ i) W
  have hs : (R₁ * (1 - Pe) - Real.log 2 / (n : ℝ)) + 0
      ≤ (∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W) / (n : ℝ) := by
    rw [add_zero]
    exact h1.trans (div_le_div_of_nonneg_right hsumle (le_of_lt hn'))
  -- geometric gateway with the second rate `= 0`
  have hmem : (R₁ * (1 - Pe) - Real.log 2 / (n : ℝ), (0 : ℝ))
      ∈ convexHull ℝ (⋃ i : Fin n,
          ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ (p₁ i) (p₂ i) W
            ∧ p.2 ≤ macInfo₂ (p₁ i) (p₂ i) W ∧ p.1 + p.2 ≤ macInfoBoth (p₁ i) (p₂ i) W}
           : Set (ℝ × ℝ))) :=
    mac_avgPentagon_mem_convexHull hn
      (fun i => macInfo₁ (p₁ i) (p₂ i) W) (fun i => macInfo₂ (p₁ i) (p₂ i) W)
      (fun i => macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₁_nonneg (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₂_nonneg (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₁_le_macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₂_le_macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_perletter_superadd (p₁ i) (p₂ i) W)
      hx1 (le_refl 0) h1 h2 hs
  -- reindex the raw per-letter union into the master probability-input union
  have hsubset : (⋃ i : Fin n,
        ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ (p₁ i) (p₂ i) W
          ∧ p.2 ≤ macInfo₂ (p₁ i) (p₂ i) W ∧ p.1 + p.2 ≤ macInfoBoth (p₁ i) (p₂ i) W}
         : Set (ℝ × ℝ)))
      ⊆ (⋃ (q₁ : Measure α₁) (q₂ : Measure α₂)
          (_ : IsProbabilityMeasure q₁) (_ : IsProbabilityMeasure q₂), macPentagon q₁ q₂ W) := by
    intro pt hpt
    rw [Set.mem_iUnion] at hpt
    obtain ⟨i, hi⟩ := hpt
    haveI := hp₁prob i; haveI := hp₂prob i
    simp only [Set.mem_iUnion]
    exact ⟨p₁ i, p₂ i, hp₁prob i, hp₂prob i, hi⟩
  exact convexHull_subset_closedConvexHull (convexHull_mono hsubset hmem)

/-- **Per-code shrunk-point membership, axis user 2** (`R₁ = 0`).  Symmetric to
`mac_converse_shrunk_point_mem_axis1`. -/
lemma mac_converse_shrunk_point_mem_axis2 [NeZero M₁]
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₂ : 2 ≤ M₂)
    {R₂ : ℝ} (hR₂ : 0 ≤ R₂)
    (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
    (hx2 : 0 ≤ R₂ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ)) :
    ((0 : ℝ), R₂ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ))
      ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  haveI : NeZero M₂ := ⟨by omega⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hM₂R : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hcard₂
  set p₁ : Fin n → Measure α₁ :=
    fun i => (macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) with hp₁def
  set p₂ : Fin n → Measure α₂ :=
    fun i => (macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) with hp₂def
  have hp₁prob : ∀ i, IsProbabilityMeasure (p₁ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hp₂prob : ∀ i, IsProbabilityMeasure (p₂ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  set Pe := (c.averageErrorProb W).toReal with hPeDef
  set Pe₂ := MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
    (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω)) (fun p ↦ (c.decoder p.2).2) with hPe₂def
  set S₂ := (∑ i : Fin n, condMutualInfo (macConverseAmbient c W)
      (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) (macConverseYs i)
      (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)).toReal with hS₂def
  have hjoint : MeasureFano.errorProb (macConverseAmbient c W)
      (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω) c.decoder = Pe :=
    mac_converse_ambient_errorProb_joint_eq c W
  have hPe_0 : 0 ≤ Pe := ENNReal.toReal_nonneg
  have hPe_1 : Pe ≤ 1 := by rw [← hjoint]; exact measureReal_le_one
  have hPe2_0 : 0 ≤ Pe₂ := measureReal_nonneg
  have hPe2_1 : Pe₂ ≤ 1 := measureReal_le_one
  have hPe2_le : Pe₂ ≤ Pe := (mac_converse_ambient_errorProb_user2_le c W).trans (le_of_eq hjoint)
  have hnR2 : (n : ℝ) * R₂ ≤ Real.log (M₂ : ℝ) := le_log_of_ceil_exp_le hM₂
  have hlogm2 : Real.log ((M₂ : ℝ) - 1) ≤ Real.log (M₂ : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2n_nonneg : 0 ≤ Real.log 2 / (n : ℝ) :=
    div_nonneg (le_of_lt (Real.log_pos (by norm_num))) (le_of_lt hn')
  have hbound2 : R₂ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ S₂ / (n : ℝ) := by
    have hb2 := mac_converse_from_code_bound₂ c W hcard₂
    have hbe2 : Real.binEntropy Pe₂ ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hprod2 : Pe₂ * Real.log ((M₂ : ℝ) - 1) ≤ Pe₂ * Real.log (M₂ : ℝ) :=
      mul_le_mul_of_nonneg_left hlogm2 hPe2_0
    have hstep1 : Real.log (M₂ : ℝ) * (1 - Pe₂) ≤ S₂ + Real.log 2 := by
      have e : Real.log (M₂ : ℝ) * (1 - Pe₂) = Real.log (M₂ : ℝ) - Pe₂ * Real.log (M₂ : ℝ) := by ring
      rw [e]; linarith [hb2, hbe2, hprod2]
    have hstep2 : (n : ℝ) * R₂ * (1 - Pe₂) ≤ Real.log (M₂ : ℝ) * (1 - Pe₂) :=
      mul_le_mul_of_nonneg_right hnR2 (by linarith)
    have hstep3 : (n : ℝ) * R₂ * (1 - Pe) ≤ (n : ℝ) * R₂ * (1 - Pe₂) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (Nat.cast_nonneg n) hR₂)
    have key2 : (n : ℝ) * R₂ * (1 - Pe) ≤ S₂ + Real.log 2 := hstep3.trans (hstep2.trans hstep1)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn',
      show R₂ * (1 - Pe) * (n : ℝ) = (n : ℝ) * R₂ * (1 - Pe) from by ring]
    exact key2
  have hSm2 : S₂ = ∑ i : Fin n, macInfo₂ (p₁ i) (p₂ i) W := by
    rw [hS₂def, ENNReal.toReal_sum (fun i _ => condMutualInfo_ne_top _ _ _ _
      (measurable_of_countable _) (measurable_of_countable _) (measurable_of_countable _))]
    exact Finset.sum_congr rfl (fun i _ => mac_condMI_eq_macInfo₂_at c W i)
  have h2 : R₂ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ (∑ i : Fin n, macInfo₂ (p₁ i) (p₂ i) W) / (n : ℝ) :=
    hSm2 ▸ hbound2
  have h1 : (0 : ℝ) ≤ (∑ i : Fin n, macInfo₁ (p₁ i) (p₂ i) W) / (n : ℝ) := by
    refine div_nonneg (Finset.sum_nonneg fun i _ => ?_) (le_of_lt hn')
    haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₁_nonneg (p₁ i) (p₂ i) W
  have hsumle : (∑ i : Fin n, macInfo₂ (p₁ i) (p₂ i) W)
      ≤ ∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W := by
    refine Finset.sum_le_sum fun i _ => ?_
    haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₂_le_macInfoBoth (p₁ i) (p₂ i) W
  have hs : (0 : ℝ) + (R₂ * (1 - Pe) - Real.log 2 / (n : ℝ))
      ≤ (∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W) / (n : ℝ) := by
    rw [zero_add]
    exact h2.trans (div_le_div_of_nonneg_right hsumle (le_of_lt hn'))
  have hmem : ((0 : ℝ), R₂ * (1 - Pe) - Real.log 2 / (n : ℝ))
      ∈ convexHull ℝ (⋃ i : Fin n,
          ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ (p₁ i) (p₂ i) W
            ∧ p.2 ≤ macInfo₂ (p₁ i) (p₂ i) W ∧ p.1 + p.2 ≤ macInfoBoth (p₁ i) (p₂ i) W}
           : Set (ℝ × ℝ))) :=
    mac_avgPentagon_mem_convexHull hn
      (fun i => macInfo₁ (p₁ i) (p₂ i) W) (fun i => macInfo₂ (p₁ i) (p₂ i) W)
      (fun i => macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₁_nonneg (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₂_nonneg (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₁_le_macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₂_le_macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_perletter_superadd (p₁ i) (p₂ i) W)
      (le_refl 0) hx2 h1 h2 hs
  have hsubset : (⋃ i : Fin n,
        ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ (p₁ i) (p₂ i) W
          ∧ p.2 ≤ macInfo₂ (p₁ i) (p₂ i) W ∧ p.1 + p.2 ≤ macInfoBoth (p₁ i) (p₂ i) W}
         : Set (ℝ × ℝ)))
      ⊆ (⋃ (q₁ : Measure α₁) (q₂ : Measure α₂)
          (_ : IsProbabilityMeasure q₁) (_ : IsProbabilityMeasure q₂), macPentagon q₁ q₂ W) := by
    intro pt hpt
    rw [Set.mem_iUnion] at hpt
    obtain ⟨i, hi⟩ := hpt
    haveI := hp₁prob i; haveI := hp₂prob i
    simp only [Set.mem_iUnion]
    exact ⟨p₁ i, p₂ i, hp₁prob i, hp₂prob i, hi⟩
  exact convexHull_subset_closedConvexHull (convexHull_mono hsubset hmem)

/-- **Axis case, user 1** (`R₂ = 0`).  For a strictly positive rate `R₁` achievable with `R₂ = 0`,
the pair `(R₁, 0)` lies in the closed convex hull of the per-input pentagons.  Uses the user-1-only
finite-`n` Fano bound `mac_converse_from_code_bound₁` (which needs only `2 ≤ M₁`, and thus survives
the `M₂ = 1` degeneracy of the axis), then takes the Fano→0 limit as in the interior case. -/
lemma mac_timesharing_converse_axis1 (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {R₁ : ℝ} (hR₁ : 0 < R₁) (hach : MACAchievable W R₁ 0) :
    (R₁, (0 : ℝ)) ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
        (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  -- for each `k`, extract a length-`nₖ ≥ k+1` code with `2 ≤ m₁`, `1 ≤ m₂` and error `< 1/(k+1)`
  have hex : ∀ k : ℕ, ∃ (nn m₁ m₂ : ℕ) (c : MACCode m₁ m₂ nn α₁ α₂ β),
      0 < nn ∧ 2 ≤ m₁ ∧ 1 ≤ m₂ ∧ (k : ℝ) + 1 ≤ (nn : ℝ)
        ∧ Nat.ceil (Real.exp ((nn : ℝ) * R₁)) ≤ m₁
        ∧ (c.averageErrorProb W).toReal < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨N, hN⟩ := hach (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨m₁, m₂, hm₁, hm₂, c, hPe⟩ := hN (max N (k + 1)) (le_max_left _ _)
    have hnnpos : 0 < max N (k + 1) := lt_of_lt_of_le (Nat.succ_pos k) (le_max_right _ _)
    have hnge : (k : ℝ) + 1 ≤ ((max N (k + 1) : ℕ) : ℝ) := by
      have hle : k + 1 ≤ max N (k + 1) := le_max_right _ _
      calc (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((max N (k + 1) : ℕ) : ℝ) := by exact_mod_cast hle
    have hcardm₁ : 2 ≤ m₁ := by
      have hpos : (0 : ℝ) < ((max N (k + 1) : ℕ) : ℝ) * R₁ := mul_pos (by exact_mod_cast hnnpos) hR₁
      have h1lt : (1 : ℝ) < Real.exp (((max N (k + 1) : ℕ) : ℝ) * R₁) := by
        rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]; exact Real.exp_lt_exp.mpr hpos
      have h1c : (1 : ℝ) < (Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R₁)) : ℝ) :=
        lt_of_lt_of_le h1lt (Nat.le_ceil _)
      have : 1 < Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R₁)) := by exact_mod_cast h1c
      omega
    have hcardm₂ : 1 ≤ m₂ := by
      have h := hm₂
      simp only [mul_zero, Real.exp_zero, Nat.ceil_one] at h
      exact h
    exact ⟨max N (k + 1), m₁, m₂, c, hnnpos, hcardm₁, hcardm₂, hnge, hm₁, hPe⟩
  choose nn m₁ m₂ c hnpos hcard₁ hcard₂ hnge hM₁ hPe using hex
  -- the average error probabilities converge to `0`, hence so does `log2/nₖ`
  have hPe0 : Tendsto (fun k => ((c k).averageErrorProb W).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun k => (hPe k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hnn_top : Tendsto (fun k => (nn k : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun k => le_trans (by linarith) (hnge k)) tendsto_natCast_atTop_atTop
  have hlog0 : Tendsto (fun k => Real.log 2 / (nn k : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hnn_top
  -- the first coordinate of the shrunk-rate sequence converges to `R₁`; the second is constant `0`
  have hf1 : Tendsto (fun k => R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))
      atTop (𝓝 R₁) := by
    have hlim : Tendsto (fun k => R₁ * (1 - ((c k).averageErrorProb W).toReal)
        - Real.log 2 / (nn k : ℝ)) atTop (𝓝 (R₁ * (1 - 0) - 0)) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hPe0)).sub hlog0
    simpa using hlim
  have htend : Tendsto (fun k => (R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ),
      (0 : ℝ))) atTop (𝓝 (R₁, (0 : ℝ))) :=
    hf1.prodMk_nhds tendsto_const_nhds
  -- eventually the shrunk point is in the first quadrant
  have hpos1 : ∀ᶠ k in atTop, 0 ≤ R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ) := by
    filter_upwards [hf1.eventually (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hR₁))] with k hk
    exact le_of_lt hk
  -- eventually the shrunk point lies in the closed convex hull (via the axis per-code lemma)
  have hev : ∀ᶠ k in atTop, (R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ),
      (0 : ℝ))
      ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
    filter_upwards [hpos1] with k hk1
    haveI : NeZero (m₂ k) := ⟨by have := hcard₂ k; omega⟩
    exact mac_converse_shrunk_point_mem_axis1 (c k) W (hnpos k) (hcard₁ k) hR₁.le (hM₁ k) hk1
  exact isClosed_closedConvexHull.mem_of_tendsto htend hev

/-- **Axis case, user 2** (`R₁ = 0`).  Symmetric to `mac_timesharing_converse_axis1`: uses the
user-2-only finite-`n` Fano bound `mac_converse_from_code_bound₂` (needing only `2 ≤ M₂`, surviving
the `M₁ = 1` degeneracy), then takes the Fano→0 limit. -/
lemma mac_timesharing_converse_axis2 (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {R₂ : ℝ} (hR₂ : 0 < R₂) (hach : MACAchievable W 0 R₂) :
    ((0 : ℝ), R₂) ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
        (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  -- for each `k`, extract a length-`nₖ ≥ k+1` code with `1 ≤ m₁`, `2 ≤ m₂` and error `< 1/(k+1)`
  have hex : ∀ k : ℕ, ∃ (nn m₁ m₂ : ℕ) (c : MACCode m₁ m₂ nn α₁ α₂ β),
      0 < nn ∧ 1 ≤ m₁ ∧ 2 ≤ m₂ ∧ (k : ℝ) + 1 ≤ (nn : ℝ)
        ∧ Nat.ceil (Real.exp ((nn : ℝ) * R₂)) ≤ m₂
        ∧ (c.averageErrorProb W).toReal < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨N, hN⟩ := hach (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨m₁, m₂, hm₁, hm₂, c, hPe⟩ := hN (max N (k + 1)) (le_max_left _ _)
    have hnnpos : 0 < max N (k + 1) := lt_of_lt_of_le (Nat.succ_pos k) (le_max_right _ _)
    have hnge : (k : ℝ) + 1 ≤ ((max N (k + 1) : ℕ) : ℝ) := by
      have hle : k + 1 ≤ max N (k + 1) := le_max_right _ _
      calc (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((max N (k + 1) : ℕ) : ℝ) := by exact_mod_cast hle
    have hcardm₂ : 2 ≤ m₂ := by
      have hpos : (0 : ℝ) < ((max N (k + 1) : ℕ) : ℝ) * R₂ := mul_pos (by exact_mod_cast hnnpos) hR₂
      have h1lt : (1 : ℝ) < Real.exp (((max N (k + 1) : ℕ) : ℝ) * R₂) := by
        rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]; exact Real.exp_lt_exp.mpr hpos
      have h1c : (1 : ℝ) < (Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R₂)) : ℝ) :=
        lt_of_lt_of_le h1lt (Nat.le_ceil _)
      have : 1 < Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R₂)) := by exact_mod_cast h1c
      omega
    have hcardm₁ : 1 ≤ m₁ := by
      have h := hm₁
      simp only [mul_zero, Real.exp_zero, Nat.ceil_one] at h
      exact h
    exact ⟨max N (k + 1), m₁, m₂, c, hnnpos, hcardm₁, hcardm₂, hnge, hm₂, hPe⟩
  choose nn m₁ m₂ c hnpos hcard₁ hcard₂ hnge hM₂ hPe using hex
  have hPe0 : Tendsto (fun k => ((c k).averageErrorProb W).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun k => (hPe k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hnn_top : Tendsto (fun k => (nn k : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun k => le_trans (by linarith) (hnge k)) tendsto_natCast_atTop_atTop
  have hlog0 : Tendsto (fun k => Real.log 2 / (nn k : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hnn_top
  have hf2 : Tendsto (fun k => R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))
      atTop (𝓝 R₂) := by
    have hlim : Tendsto (fun k => R₂ * (1 - ((c k).averageErrorProb W).toReal)
        - Real.log 2 / (nn k : ℝ)) atTop (𝓝 (R₂ * (1 - 0) - 0)) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hPe0)).sub hlog0
    simpa using hlim
  have htend : Tendsto (fun k => ((0 : ℝ),
      R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ)))
      atTop (𝓝 ((0 : ℝ), R₂)) :=
    tendsto_const_nhds.prodMk_nhds hf2
  have hpos2 : ∀ᶠ k in atTop, 0 ≤ R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ) := by
    filter_upwards [hf2.eventually (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hR₂))] with k hk
    exact le_of_lt hk
  have hev : ∀ᶠ k in atTop, ((0 : ℝ),
      R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))
      ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
    filter_upwards [hpos2] with k hk2
    haveI : NeZero (m₁ k) := ⟨by have := hcard₁ k; omega⟩
    exact mac_converse_shrunk_point_mem_axis2 (c k) W (hnpos k) (hcard₂ k) hR₂.le (hM₂ k) hk2
  exact isClosed_closedConvexHull.mem_of_tendsto htend hev

/-- **MAC time-sharing converse (CV headline).**  Every achievable first-quadrant rate pair lies in
the closed convex hull of the union of all per-input pentagons `macPentagon p₁ p₂ W` over
probability inputs `p₁`, `p₂`.  Assembled by casework on whether each rate is zero or positive:
the interior case uses the Fano→0 limit `mac_timesharing_converse_interior`, the origin `(0,0)` lies
in any pentagon, and the two axis cases reduce to the single-user Fano corner via
`mac_timesharing_converse_axis1/2`. -/
theorem mac_timesharing_converse (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    {p | MACAchievable W p.1 p.2 ∧ 0 ≤ p.1 ∧ 0 ≤ p.2}
      ⊆ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  rintro ⟨R₁, R₂⟩ ⟨hach, hR₁0, hR₂0⟩
  rcases hR₁0.lt_or_eq with hR₁ | hR₁
  · rcases hR₂0.lt_or_eq with hR₂ | hR₂
    · exact mac_timesharing_converse_interior W hR₁ hR₂ hach
    · subst hR₂
      exact mac_timesharing_converse_axis1 W hR₁ hach
  · subst hR₁
    rcases hR₂0.lt_or_eq with hR₂ | hR₂
    · exact mac_timesharing_converse_axis2 W hR₂ hach
    · subst hR₂
      -- origin: `(0, 0)` lies in every pentagon (all five inequalities are `0 ≤ nonneg`)
      apply subset_closedConvexHull
      haveI hd1 : IsProbabilityMeasure (Measure.dirac (Classical.arbitrary α₁) : Measure α₁) :=
        inferInstance
      haveI hd2 : IsProbabilityMeasure (Measure.dirac (Classical.arbitrary α₂) : Measure α₂) :=
        inferInstance
      simp only [Set.mem_iUnion]
      refine ⟨Measure.dirac (Classical.arbitrary α₁), Measure.dirac (Classical.arbitrary α₂),
        hd1, hd2, le_refl _, le_refl _, ?_, ?_, ?_⟩
      · exact macInfo₁_nonneg _ _ W
      · exact macInfo₂_nonneg _ _ W
      · simpa using macInfoBoth_nonneg (Measure.dirac (Classical.arbitrary α₁))
          (Measure.dirac (Classical.arbitrary α₂)) W

end CVAssembly

section VAssembly

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon Filter
open scoped ENNReal Topology

variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁]
    [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂]
    [MeasurableSingletonClass α₂] [StandardBorelSpace α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
    [MeasurableSingletonClass β] [StandardBorelSpace β]

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂] [StandardBorelSpace α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] [StandardBorelSpace β] in
/-- Clamping a rate pair into the first quadrant does not change achievability.  `MACAchievable`
depends on the rates `R₁`, `R₂` only through the message-count thresholds `⌈exp (n Rⱼ)⌉ ≤ Mⱼ`,
and `⌈exp (n R)⌉ = ⌈exp (n (max R 0))⌉` for every block length `n` (for `R < 0` both ceilings
equal `1`, since `exp (n R) ∈ (0, 1]`).  This lets the antisymmetry argument fold a negative
achievable rate back onto the axis. -/
theorem mac_achievable_clamp_iff (W : MACChannel α₁ α₂ β) (R₁ R₂ : ℝ) :
    MACAchievable W R₁ R₂ ↔ MACAchievable W (max R₁ 0) (max R₂ 0) := by
  -- the ceiling thresholds are unchanged by clamping the rate to the first quadrant
  have key : ∀ (R : ℝ) (n : ℕ),
      Nat.ceil (Real.exp ((n : ℝ) * max R 0)) = Nat.ceil (Real.exp ((n : ℝ) * R)) := by
    intro R n
    by_cases hR : 0 ≤ R
    · rw [max_eq_left hR]
    · replace hR : R < 0 := not_le.mp hR
      rw [max_eq_right hR.le, mul_zero, Real.exp_zero, Nat.ceil_one]
      symm
      apply le_antisymm
      · apply Nat.ceil_le.mpr
        rw [Nat.cast_one, ← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hR.le)
      · exact Nat.ceil_pos.mpr (Real.exp_pos _)
  constructor
  · intro h ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨M₁, M₂, hM₁, hM₂, c, hc⟩ := hN n hn
    refine ⟨M₁, M₂, ?_, ?_, c, hc⟩
    · rw [key R₁ n]; exact hM₁
    · rw [key R₂ n]; exact hM₂
  · intro h ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨M₁, M₂, hM₁, hM₂, c, hc⟩ := hN n hn
    refine ⟨M₁, M₂, ?_, ?_, c, hc⟩
    · rw [← key R₁ n]; exact hM₁
    · rw [← key R₂ n]; exact hM₂

/-- **MAC time-sharing capacity region (full first-quadrant characterization).**  The operational
capacity region, intersected with the first quadrant, equals the closed convex hull of the union of
all per-input pentagons `macPentagon p₁ p₂ W` over probability inputs `p₁`, `p₂` (Cover–Thomas
Theorem 15.3.1).  The `⊆` half is the converse (`mac_timesharing_converse`, with negative rates
clamped back to the axis via `mac_achievable_clamp_iff`); the `⊇` half is achievability
(`mac_achievability_region_allprob`, whose pentagons already lie in the first quadrant). -/
@[entry_point]
theorem mac_timesharing_capacity_region (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b}) :
    macCapacityRegion W ∩ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}
      = closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  apply Set.Subset.antisymm
  · -- converse: an achievable first-quadrant pair lies in the hull (clamp negative rates to axis)
    rintro x ⟨hxcap, hx1, hx2⟩
    have hxcl : x ∈ closure {p : ℝ × ℝ | MACAchievable W p.1 p.2} := hxcap
    rw [mem_closure_iff_seq_limit] at hxcl
    obtain ⟨u, hu_mem, hu_lim⟩ := hxcl
    -- the clamping map `p ↦ (max p.1 0, max p.2 0)` is continuous and fixes `x`
    have hcont : Continuous (fun p : ℝ × ℝ => (max p.1 0, max p.2 0)) :=
      (continuous_fst.max continuous_const).prodMk (continuous_snd.max continuous_const)
    have htend : Tendsto (fun n => (max (u n).1 0, max (u n).2 0)) atTop (𝓝 x) := by
      have h := (hcont.tendsto x).comp hu_lim
      have hx_eq : (max x.1 0, max x.2 0) = x := by rw [max_eq_left hx1, max_eq_left hx2]
      rwa [hx_eq] at h
    -- each clamped point is achievable in the first quadrant, hence in the hull via the converse
    have hmem : ∀ n, (max (u n).1 0, max (u n).2 0)
        ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
            (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
      intro n
      exact mac_timesharing_converse W
        ⟨(mac_achievable_clamp_iff W (u n).1 (u n).2).mp (hu_mem n),
          le_max_right _ _, le_max_right _ _⟩
    exact isClosed_closedConvexHull.mem_of_tendsto htend (Eventually.of_forall hmem)
  · -- achievability: the hull is in the capacity region and in the first quadrant
    have hset : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} = Set.Ici 0 ×ˢ Set.Ici 0 := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ici]
    have hQconv : Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := by
      rw [hset]; exact (convex_Ici 0).prod (convex_Ici 0)
    have hQclosed : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := by
      rw [hset]; exact isClosed_Ici.prod isClosed_Ici
    have hunion_sub_Q : (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
        (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W)
        ⊆ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := by
      simp only [Set.iUnion_subset_iff]
      intro p₁ p₂ _ _ pt hpt
      exact ⟨hpt.1, hpt.2.1⟩
    exact Set.subset_inter (mac_achievability_region_allprob W hW)
      (closedConvexHull_min hunion_sub_Q hQconv hQclosed)

end VAssembly

end InformationTheory.Shannon.MAC

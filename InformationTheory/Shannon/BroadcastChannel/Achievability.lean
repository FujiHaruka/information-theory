import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Basic
import InformationTheory.Shannon.MultipleAccess.JointTypicality
import InformationTheory.Shannon.MultipleAccess.IIDAmbient

/-!
# Degraded broadcast channel — achievability (superposition inner bound)

The achievability half of the degraded broadcast-channel coding theorem
(Cover–Thomas *Elements of Information Theory* Thm 15.6.2): the superposition (two-tier
cloud / satellite) random-coding inner bound.  The net-new tier relative to the
multiple-access achievability (`InformationTheory.Shannon.MAC`) is the **conditional
(superposition) random codebook**: satellite codewords are drawn from a conditional
product law `Πᵢ K(Uᵢ)` steered by the cloud codeword, rather than a flat product law.

## Main definitions

* `bcJointDistribution pU K W` — the per-coordinate joint law of `(U, X, Y₁, Y₂)`,
  `U ∼ pU`, `X ∣ U ∼ K`, `(Y₁, Y₂) ∣ X ∼ W`.
* `bcInfo₂ pU K W` — the cloud information `I(U; Y₂) = H(U) + H(Y₂) − H(U, Y₂)`.
* `bcInfo₁ pU K W` — the satellite conditional information
  `I(X; Y₁ ∣ U) = H(U, X) + H(U, Y₁) − H(U, X, Y₁) − H(U)`.
* `IsBCDegraded W` — physical degradedness `X → Y₁ → Y₂` (there is a degrading kernel).
* `BCCloudCodebook` / `BCSatelliteCodebook` and their random-coding measures
  `bcCloudCodebookMeasure`, `bcSatelliteCodebookMeasure`, `bcCodebookMeasure` — the
  two-tier ensemble; the satellite law is a **conditional product** `Πᵢ K(Uᵢ)`.

## Main results

* `bc_conditional_slice_prob_le` — the gateway covering bound: the conditional-product
  mass of the jointly-typical satellite slice is `≤ exp(−n (I(X; Y₁ ∣ U) − ε))`.
* `bc_achievability` — the headline: any rate pair strictly inside the degraded-BC region
  `R₁ < I(X; Y₁ ∣ U)`, `R₂ < I(U; Y₂)` is achievable with vanishing per-receiver error.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.MAC
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

variable {U α β₁ β₂ : Type*}
  [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-! ### Physical degradedness -/

/-- Physical degradedness `X → Y₁ → Y₂`: the second (degraded) output is a stochastic
function of the first output alone.  There is a Markov kernel `Q : Kernel β₁ β₂` (the
degrading channel) such that sampling `(y₁, y₂) ∼ W x` is the same as sampling
`y₁ ∼ (W x).map Prod.fst` and then `y₂ ∼ Q y₁`.  A structural precondition of the
degraded-BC achievability theorem (parity with the converse's block-prefix degradedness),
not a load-bearing hypothesis. -/
def IsBCDegraded (W : BCChannel α β₁ β₂) : Prop :=
  ∃ Q : Kernel β₁ β₂, IsMarkovKernel Q ∧
    ∀ a : α, W a = ((W a).map Prod.fst).bind (fun y₁ ↦ (Q y₁).map (fun y₂ ↦ (y₁, y₂)))

/-! ### Per-coordinate joint distribution -/

/-- The per-coordinate broadcast joint law on `U × α × β₁ × β₂`: the compProd chain
`pU → K → W` (`U ∼ pU`, `X ∣ U ∼ K`, `(Y₁, Y₂) ∣ X ∼ W`), reshaped from the left-nested
`(U × α) × (β₁ × β₂)` to the right-nested quadruple. -/
noncomputable def bcJointDistribution
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) :
    Measure (U × α × β₁ × β₂) :=
  ((pU ⊗ₘ K) ⊗ₘ (W.comap Prod.snd measurable_snd)).map MeasurableEquiv.prodAssoc

instance bcJointDistribution.instIsProbabilityMeasure
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsProbabilityMeasure (bcJointDistribution pU K W) := by
  unfold bcJointDistribution
  exact Measure.isProbabilityMeasure_map MeasurableEquiv.prodAssoc.measurable.aemeasurable

/-! ### I.i.d. ambient measure on `ℕ → U × α × β₁ × β₂` -/

/-- The i.i.d. broadcast ambient measure:
`Measure.infinitePi (fun _ => bcJointDistribution pU K W)`. -/
noncomputable def bcAmbientMeasure
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) :
    Measure (ℕ → U × α × β₁ × β₂) :=
  Measure.infinitePi (fun _ : ℕ ↦ bcJointDistribution pU K W)

/-- The cloud coordinate `ω ↦ (ω i).1`. -/
def bcUs : ℕ → (ℕ → U × α × β₁ × β₂) → U := fun i ω ↦ (ω i).1

/-- The satellite input coordinate `ω ↦ (ω i).2.1`. -/
def bcXs : ℕ → (ℕ → U × α × β₁ × β₂) → α := fun i ω ↦ (ω i).2.1

/-- The strong-receiver output coordinate `ω ↦ (ω i).2.2.1`. -/
def bcY₁s : ℕ → (ℕ → U × α × β₁ × β₂) → β₁ := fun i ω ↦ (ω i).2.2.1

/-- The degraded-receiver output coordinate `ω ↦ (ω i).2.2.2`. -/
def bcY₂s : ℕ → (ℕ → U × α × β₁ × β₂) → β₂ := fun i ω ↦ (ω i).2.2.2

/-! ### Auxiliary-variable informations -/

/-- The cloud information `I(U; Y₂) = H(U) + H(Y₂) − H(U, Y₂)` of the per-coordinate joint
law.  This is the achievable rate of receiver 2 (the degraded receiver). -/
noncomputable def bcInfo₂
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) : ℝ :=
  entropy (bcJointDistribution pU K W) Prod.fst
    + entropy (bcJointDistribution pU K W) (fun q ↦ q.2.2.2)
    - entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.2.2))

/-- The satellite conditional information
`I(X; Y₁ ∣ U) = H(U, X) + H(U, Y₁) − H(U, X, Y₁) − H(U)` of the per-coordinate joint law.
This is the achievable rate of receiver 1 (the strong receiver) given the cloud `U`.  Unlike
the MAC `macInfo`, this is a genuine four-entropy *conditional* mutual information, not a
plain three-term unconditional one. -/
noncomputable def bcInfo₁
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) : ℝ :=
  entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.1))
    + entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.2.1))
    - entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.1, q.2.2.1))
    - entropy (bcJointDistribution pU K W) Prod.fst

/-! ### Two-tier (cloud / satellite) random codebook -/

/-- A length-`n` cloud codebook: for each cloud message `w₂` a cloud codeword `Uⁿ(w₂)`. -/
abbrev BCCloudCodebook (M₂ n : ℕ) (U : Type*) := Fin M₂ → (Fin n → U)

/-- A length-`n` satellite codebook: for each message pair `(w₁, w₂)` a satellite codeword
`Xⁿ(w₁, w₂)`.  Definitionally the `BroadcastCode` joint encoder. -/
abbrev BCSatelliteCodebook (M₁ M₂ n : ℕ) (α : Type*) := Fin M₁ × Fin M₂ → (Fin n → α)

/-- The cloud codebook law: `pU`-i.i.d. over all `M₂ · n` cloud letters. -/
noncomputable def bcCloudCodebookMeasure
    (pU : Measure U) (M₂ n : ℕ) : Measure (BCCloudCodebook M₂ n U) :=
  Measure.pi (fun _ : Fin M₂ ↦ Measure.pi (fun _ : Fin n ↦ pU))

/-- The satellite codebook law *conditional on* the cloud codebook `u`: each satellite
letter `Xₗ(w₁, w₂)` is drawn from `K (u w₂ l)`, independently across pairs and letters.  This
is the conditional product `Πᵢ K(Uᵢ)` at the heart of superposition coding — the single point
of departure from the MAC flat-product ensemble. -/
noncomputable def bcSatelliteCodebookMeasure
    (K : Kernel U α) (M₁ M₂ n : ℕ) (u : BCCloudCodebook M₂ n U) :
    Measure (BCSatelliteCodebook M₁ M₂ n α) :=
  Measure.pi (fun p : Fin M₁ × Fin M₂ ↦ Measure.pi (fun l : Fin n ↦ K (u p.2 l)))

/-- The joint two-tier codebook law on `(cloud, satellite)` pairs: draw the cloud codebook
from `bcCloudCodebookMeasure`, then the satellite codebook conditionally from
`bcSatelliteCodebookMeasure`. -/
noncomputable def bcCodebookMeasure
    (pU : Measure U) (K : Kernel U α) (M₁ M₂ n : ℕ) :
    Measure (BCCloudCodebook M₂ n U × BCSatelliteCodebook M₁ M₂ n α) :=
  (bcCloudCodebookMeasure pU M₂ n).bind
    (fun u ↦ (bcSatelliteCodebookMeasure K M₁ M₂ n u).map (fun x ↦ (u, x)))

/-! ### Gateway atom: conditional-slice satellite typicality bound -/

/-- **Conditional-slice satellite typicality probability bound** (superposition covering
step).  For a fixed *typical* cloud codeword `u` and a fixed *typical* received word `y₁`,
the probability under the conditional product law `Πᵢ K(uᵢ)` that an independently drawn
satellite `x` is jointly typical with `(u, y₁)` is at most `exp(−n (I(X; Y₁ ∣ U) − ε))`.
This is the receiver-1 "wrong satellite, correct cloud" sub-event of the superposition
random-coding argument (Cover–Thomas Thm 15.6.2); the exponent matches `bcInfo₁`
out of the box.
@residual(plan:bc-superposition-inner) -/
theorem bc_conditional_slice_prob_le
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {n : ℕ} {ε : ℝ}
    (u : Fin n → U) (y₁ : Fin n → β₁)
    (hu : u ∈ typicalSet (bcAmbientMeasure pU K W) bcUs n ε)
    (hy₁ : y₁ ∈ typicalSet (bcAmbientMeasure pU K W) bcY₁s n ε) :
    (Measure.pi (fun l : Fin n ↦ K (u l))).real
        { x : Fin n → α |
          (u, x, y₁) ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
      ≤ Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - ε)) := by
  sorry

/-! ### Headline: degraded broadcast achievability -/

/-- **Broadcast channel achievability (degraded, superposition inner bound).**
Cover–Thomas *Elements of Information Theory* Thm 15.6.2 achievability.  Over a physically
degraded broadcast channel `W` with cloud law `pU` and conditional input kernel `K`, any
rate pair strictly inside the auxiliary-variable region

* `R₁ < I(X; Y₁ ∣ U)` (`= bcInfo₁`, the strong receiver), and
* `R₂ < I(U; Y₂)` (`= bcInfo₂`, the degraded receiver)

is achievable: for all large enough block lengths `n` there is a `BroadcastCode` whose two
per-receiver average error probabilities are both below any prescribed `ε' > 0`.  The proof
is the two-tier superposition random-coding argument; degradedness `X → Y₁ → Y₂` is a
structural precondition ensuring the receiver-1 joint-decoding rate sum is met automatically.
@residual(plan:bc-superposition-inner) -/
theorem bc_achievability
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (hdeg : IsBCDegraded W)
    {R₁ R₂ : ℝ} (_hR₁ : 0 < R₁) (_hR₂ : 0 < R₂)
    (hR₁lt : R₁ < bcInfo₁ pU K W) (hR₂lt : R₂ < bcInfo₂ pU K W)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M₁ M₂ : ℕ) (_hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
        (_hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
        (c : BroadcastCode M₁ M₂ n α β₁ β₂),
        (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε' := by
  sorry

end InformationTheory.Shannon.BroadcastChannel

import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.ChannelCodingShannonTheorem
import Common2026.Shannon.MIChainRule
import Common2026.Shannon.CondEntropyMemoryless
import Mathlib.Analysis.Subadditive
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Blockwise channel + capacity limit form (I-2 seed)

A `BlockwiseChannel α β` is a sequence of kernels
`W_n : Kernel (Fin n → α) (Fin n → β)` (one per block length). The **general**
DMC capacity is the asymptotic per-letter capacity

  capacity_lim W := lim_{n → ∞} (1/n) · sup_{p^n} I(X^n; Y^n)

For memoryless DMC (`ofMemoryless W`, with all `W_n := ⊗_n W`), this reduces
to the single-letter formula `capacity W` via Fekete's lemma applied to the
(here linear in `n`) sequence `capacityN W n`.

## Main definitions

* `BlockwiseChannel α β := (n : ℕ) → Kernel (Fin n → α) (Fin n → β)`
* `Channel.toBlock W n` — direct `Measure.pi` product kernel `W^{⊗n}`.
* `BlockwiseChannel.ofMemoryless W := fun n => W.toBlock n` — memoryless extension.
* `BlockwiseChannel.capacityN W n : ℝ≥0∞` — per-block capacity (`sSup` MI over
  probability inputs).
* `BlockwiseChannel.capacity_lim W : ℝ` — asymptotic per-letter capacity.

## Main results

* `capacityN_ofMemoryless_eq` — Phase 4-α: `(ofMemoryless W).capacityN n` matches
  `n · capacity W` (per-`n` equality, via `mutualInfo_iid_eq_nsmul`).
* `capacity_lim_eq_capacity_of_memoryless` — Phase 4-β: limit form matches the
  single-letter capacity.

Design judgements (see `docs/shannon/general-dmc-plan.md`):

* `BlockwiseChannel` is the **function form** `(n : ℕ) → Kernel _ _`. No marginal
  consistency axiom; sufficient for memoryless extension + AWGN/MAC/BC seeds.
* `Channel.toBlock` is defined directly via `Measure.pi` (Pivot A): this makes
  the `compProd ↔ pi` bridge (`toBlock_compProd_pi_factor`) almost definitional
  via `measurePreserving_arrowProdEquivProdArrow`, replacing the previous
  inductive `MeasurableEquiv.piFinSuccAbove` construction whose bridge
  required ~80-150 lines of self-written plumbing.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## `BlockwiseChannel` definition -/

variable {α β : Type*}

/-- A **blockwise channel** is a sequence of kernels, one per block length `n`. -/
def BlockwiseChannel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Type _ :=
  (n : ℕ) → Kernel (Fin n → α) (Fin n → β)

variable [MeasurableSpace α] [MeasurableSpace β]

/-! ## `Channel.toBlock W` : the i.i.d. block extension of `W`

Defined directly as `Kernel.mk (fun x => Measure.pi (fun i => W (x i)))` with
explicit measurability proof. This makes the `compProd ↔ pi` bridge below
definitionally tractable via `measurePreserving_arrowProdEquivProdArrow`. -/

/-- The block kernel `W^{⊗n}` of `W`, defined as `Measure.pi` of per-coordinate
applications of `W`. Requires `[IsMarkovKernel W]` so each fibre measure is a
probability measure (used in the measurability proof via the π-system route). -/
noncomputable def Channel.toBlock (W : Channel α β) [IsMarkovKernel W] (n : ℕ) :
    Kernel (Fin n → α) (Fin n → β) where
  toFun x := Measure.pi (fun i : Fin n => W (x i))
  measurable' := by
    -- `Measure.pi (fun i => W (x i))` is a probability measure for each `x`, so use
    -- `Measurable.measure_of_isPiSystem_of_isProbabilityMeasure` on the cylinder
    -- π-system `pi univ '' pi univ {MeasurableSet}` generating `MeasurableSpace.pi`.
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (S := Set.pi Set.univ '' Set.pi Set.univ
        (fun i : Fin n => { s : Set β | MeasurableSet s }))
      generateFrom_pi.symm isPiSystem_pi ?_
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_imp_iff] at ht
    -- On `Set.univ.pi t`, `Measure.pi (...) = ∏ i, W (x i) (t i)` by `pi_pi`.
    have h_eval : ∀ x : Fin n → α,
        Measure.pi (fun i : Fin n => W (x i)) (Set.univ.pi t)
          = ∏ i : Fin n, (W (x i)) (t i) := by
      intro x; rw [Measure.pi_pi]
    simp_rw [h_eval]
    refine Finset.measurable_prod _ ?_
    intro i _
    exact (Kernel.measurable_coe W (ht i)).comp (measurable_pi_apply i)

/-- `Channel.toBlock W n` is a Markov kernel when `W` is. -/
instance Channel.toBlock.instIsMarkovKernel (W : Channel α β) [IsMarkovKernel W] (n : ℕ) :
    IsMarkovKernel (Channel.toBlock W n) where
  isProbabilityMeasure x := by
    show IsProbabilityMeasure (Measure.pi (fun i : Fin n => W (x i)))
    infer_instance

@[simp] lemma Channel.toBlock_apply (W : Channel α β) [IsMarkovKernel W] (n : ℕ)
    (x : Fin n → α) :
    (Channel.toBlock W n) x = Measure.pi (fun i : Fin n => W (x i)) := rfl

/-! ## `BlockwiseChannel.ofMemoryless` -/

/-- Memoryless block extension: `ofMemoryless W n := W.toBlock n`. -/
noncomputable def BlockwiseChannel.ofMemoryless
    (W : Channel α β) [IsMarkovKernel W] : BlockwiseChannel α β :=
  fun n => W.toBlock n

instance BlockwiseChannel.ofMemoryless.instIsMarkovKernel
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) :
    IsMarkovKernel ((BlockwiseChannel.ofMemoryless W) n) :=
  Channel.toBlock.instIsMarkovKernel W n

/-! ## `capacityN` and `capacity_lim` -/

/-- Per-block capacity: `sup_{p : prob measure on (Fin n → α)} I(p; W_n)`.
Type is `ℝ≥0∞` to match `mutualInfoOfChannel`. -/
noncomputable def BlockwiseChannel.capacityN
    (W : BlockwiseChannel α β) (n : ℕ) : ℝ≥0∞ :=
  sSup ((fun p : Measure (Fin n → α) => mutualInfoOfChannel p (W n)) ''
        { p : Measure (Fin n → α) | IsProbabilityMeasure p })

theorem BlockwiseChannel.capacityN_nonneg (W : BlockwiseChannel α β) (n : ℕ) :
    0 ≤ W.capacityN n := bot_le

/-- The asymptotic per-letter capacity:
`capacity_lim W := lim_{n → ∞} (capacityN W n).toReal / n`. -/
noncomputable def BlockwiseChannel.capacity_lim (W : BlockwiseChannel α β) : ℝ :=
  Filter.atTop.limUnder (fun n : ℕ => (W.capacityN n).toReal / n)

/-! ## Phase B — Structural bridge `toBlock_compProd_pi_factor`

With `Channel.toBlock` defined directly via `Measure.pi`, the bridge becomes
nearly definitional: `(Measure.pi p) ⊗ₘ (toBlock W n)` lives on `(Fin n → α) × (Fin n → β)`,
and pushing it through the canonical equiv to `Fin n → α × β` recovers
`Measure.pi (fun i => p i ⊗ₘ W)` via `measurePreserving_arrowProdEquivProdArrow.symm`. -/

/-- **Structural bridge**. For any product input `p_i : Fin n → Measure α` (each
`IsProbabilityMeasure`) and Markov `W`, the joint distribution
`(Measure.pi p_i) ⊗ₘ (W.toBlock n)` on `(Fin n → α) × (Fin n → β)`, pushed through
the canonical equiv `(Fin n → α) × (Fin n → β) ≃ᵐ Fin n → (α × β)`, factors as
`Measure.pi (fun i => p_i ⊗ₘ W)`. -/
private theorem toBlock_compProd_pi_factor
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ)
    (p : Fin n → Measure α) [∀ i, IsProbabilityMeasure (p i)] :
    ((Measure.pi p) ⊗ₘ (Channel.toBlock W n)).map
        (fun z : (Fin n → α) × (Fin n → β) => fun i => (z.1 i, z.2 i))
      = Measure.pi (fun i => p i ⊗ₘ W) := by
  -- Both sides are probability measures on the countable finite space `Fin n → α × β`.
  -- Apply `Measure.ext_iff_singleton` and compute each singleton via `pi_pi`,
  -- `compProd_apply_prod`, and `Set.singleton_prod_singleton`.
  have h_meas_map :
      Measurable (fun z : (Fin n → α) × (Fin n → β) => fun i => (z.1 i, z.2 i)) := by
    refine measurable_pi_iff.mpr (fun i => ?_)
    exact ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  refine Measure.ext_of_singleton (fun f => ?_)
  -- Decompose `{f}` on the codomain `Fin n → α × β` as `univ.pi (fun i => {f i})`.
  have h_univ_pi_singleton :
      ({f} : Set (Fin n → α × β)) = Set.univ.pi (fun i : Fin n => ({f i} : Set (α × β))) := by
    ext g; simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_imp_iff]
    exact ⟨fun h _ => by rw [h], fun h => funext h⟩
  -- Each `(p i ⊗ₘ W) {f i} = p i {fst (f i)} * W (fst (f i)) {snd (f i)}`.
  have h_rhs_each : ∀ i : Fin n,
      (p i ⊗ₘ W) ({f i} : Set (α × β))
        = p i ({(f i).1} : Set α) * W (f i).1 ({(f i).2} : Set β) := by
    intro i
    have h_decomp : ({f i} : Set (α × β)) = ({(f i).1} : Set α) ×ˢ ({(f i).2} : Set β) := by
      ext x; simp [Prod.ext_iff]
    rw [h_decomp,
        Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
        lintegral_singleton, mul_comm]
  -- RHS: pi (p ⊗ₘ W) {f} = ∏ i, p i {fst (f i)} * W (fst (f i)) {snd (f i)}.
  have h_rhs :
      (Measure.pi (fun i : Fin n => p i ⊗ₘ W)) ({f} : Set (Fin n → α × β))
        = ∏ i : Fin n, p i ({(f i).1} : Set α) * W (f i).1 ({(f i).2} : Set β) := by
    rw [h_univ_pi_singleton, Measure.pi_pi]
    exact Finset.prod_congr rfl (fun i _ => h_rhs_each i)
  -- LHS: Compute the map application.
  -- Preimage of `{f}` under `fun z i => (z.1 i, z.2 i)` is `{(fst ∘ f, snd ∘ f)}` (single point).
  have h_preimage :
      (fun z : (Fin n → α) × (Fin n → β) => fun i => (z.1 i, z.2 i)) ⁻¹' ({f} : Set _)
        = ({((fun i => (f i).1, fun i => (f i).2))} : Set ((Fin n → α) × (Fin n → β))) := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · intro h
      refine ⟨funext fun i => ?_, funext fun i => ?_⟩
      · exact congrArg Prod.fst (congrFun h i)
      · exact congrArg Prod.snd (congrFun h i)
    · rintro ⟨hx, hy⟩
      funext i
      have hxi : x i = (f i).1 := congrFun hx i
      have hyi : y i = (f i).2 := congrFun hy i
      rw [hxi, hyi]
  -- Now compute ((pi p) ⊗ₘ toBlock W n) on the single point preimage.
  have h_lhs_compProd :
      ((Measure.pi p) ⊗ₘ (Channel.toBlock W n))
          ({((fun i => (f i).1, fun i => (f i).2))} : Set ((Fin n → α) × (Fin n → β)))
        = (Measure.pi p) ({fun i => (f i).1} : Set (Fin n → α))
          * (Measure.pi (fun i : Fin n => W (f i).1)) ({fun i => (f i).2} : Set (Fin n → β)) := by
    have h_decomp :
        ({((fun i => (f i).1, fun i => (f i).2))} :
          Set ((Fin n → α) × (Fin n → β)))
          = ({fun i => (f i).1} : Set (Fin n → α)) ×ˢ ({fun i => (f i).2} : Set (Fin n → β)) := by
      ext ⟨x, y⟩; simp [Prod.ext_iff]
    rw [h_decomp,
        Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
        lintegral_singleton, Channel.toBlock_apply, mul_comm]
  -- Decompose each factor as a finite product.
  have h_pi_p :
      (Measure.pi p) ({fun i => (f i).1} : Set (Fin n → α))
        = ∏ i : Fin n, p i ({(f i).1} : Set α) := by
    have : ({fun i => (f i).1} : Set (Fin n → α))
          = Set.univ.pi (fun i : Fin n => ({(f i).1} : Set α)) := by
      ext g; simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_imp_iff]
      exact ⟨fun h _ => by rw [h], fun h => funext h⟩
    rw [this, Measure.pi_pi]
  have h_pi_W :
      (Measure.pi (fun i : Fin n => W (f i).1)) ({fun i => (f i).2} : Set (Fin n → β))
        = ∏ i : Fin n, W (f i).1 ({(f i).2} : Set β) := by
    have : ({fun i => (f i).2} : Set (Fin n → β))
          = Set.univ.pi (fun i : Fin n => ({(f i).2} : Set β)) := by
      ext g; simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_imp_iff]
      exact ⟨fun h _ => by rw [h], fun h => funext h⟩
    rw [this, Measure.pi_pi]
  -- Assemble LHS.
  rw [Measure.map_apply h_meas_map (measurableSet_singleton _), h_preimage,
      h_lhs_compProd, h_pi_p, h_pi_W, ← Finset.prod_mul_distrib, h_rhs]

/-! ## Phase C — Helper: arbitrary measure MI ≤ capacity -/

/-- Any probability measure on a finite alphabet equals `pmfToMeasure` of its
real-valued atoms. -/
private lemma measure_eq_pmfToMeasure_of_finite
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (q : Measure α) [IsProbabilityMeasure q] :
    q = pmfToMeasure (fun a => q.real {a}) := by
  -- Use Measure.ext_iff_singleton.
  refine (Measure.ext_iff_singleton.mpr ?_)
  intro a
  rw [pmfToMeasure_apply_singleton]
  -- q {a} = ENNReal.ofReal (q.real {a}) = ENNReal.ofReal (q {a}).toReal = q {a}
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top q _)]

/-- The real-valued atom pmf of a probability measure on a finite alphabet lies
in the standard simplex. -/
private lemma real_atoms_mem_stdSimplex
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (q : Measure α) [IsProbabilityMeasure q] :
    (fun a : α => q.real {a}) ∈ stdSimplex ℝ α := by
  refine ⟨fun a => measureReal_nonneg, ?_⟩
  -- ∑ a, q.real {a} = q.real univ = 1.
  -- Use ENNReal route to avoid measureReal_biUnion finiteness side conditions.
  have h_sum_ennreal : (∑ a : α, q ({a} : Set α)) = q Set.univ := by
    rw [← measure_biUnion_finset
      (fun _ _ _ _ hne => by
        simpa [Set.disjoint_singleton] using hne)
      (fun _ _ => measurableSet_singleton _)]
    congr 1; ext x; simp
  have hq_univ : q Set.univ = 1 := measure_univ
  have h_real_sum : (∑ a : α, q.real ({a} : Set α)) = q.real Set.univ := by
    simp only [Measure.real]
    rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top q _), h_sum_ennreal]
  rw [h_real_sum]
  show q.real Set.univ = 1
  rw [Measure.real, hq_univ]
  rfl

/-- Any probability measure on a finite alphabet has channel MI bounded by capacity. -/
private theorem mutualInfoOfChannel_toReal_le_capacity
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W]
    (q : Measure α) [IsProbabilityMeasure q] :
    (mutualInfoOfChannel q W).toReal ≤ capacity W := by
  -- Write q = pmfToMeasure p with p := q.real {·} ∈ stdSimplex.
  set p : α → ℝ := fun a => q.real {a} with hp_def
  have hp_mem : p ∈ stdSimplex ℝ α := real_atoms_mem_stdSimplex q
  have hq_eq : q = pmfToMeasure p := measure_eq_pmfToMeasure_of_finite q
  -- Apply le_csSup on capacity definition.
  refine le_csSup (capacity_bddAbove W) ⟨p, hp_mem, ?_⟩
  show (mutualInfoOfChannel (pmfToMeasure p) W).toReal = (mutualInfoOfChannel q W).toReal
  rw [← hq_eq]

/-! ## Phase 4-α core lemma — i.i.d. input MI multiplicativity

The key identity behind Phase 4-α (≥ direction): for an i.i.d. product input
`q := Measure.pi (fun _ : Fin n => p₀)`, the channel mutual information with the
block kernel `W^{⊗n}` factors as `n • I(p₀; W)`. Proven by pushing both joint and
marginal-product through the canonical `(Fin n → α × β) ≃ᵐ (Fin n → α) × (Fin n → β)`
and applying `klDiv_pi_eq_sum`.
-/

/-- For an i.i.d. product input `q := Measure.pi (fun _ : Fin n => p₀)`, the
channel mutual information with the block kernel `Channel.toBlock W n` equals
`n • mutualInfoOfChannel p₀ W`.

**Proof sketch**: Use the canonical `(Fin n → α × β) ≃ᵐ (Fin n → α) × (Fin n → β)`
to reshape both joint (via `toBlock_compProd_pi_factor`) and marginal product (via
`measurePreserving_arrowProdEquivProdArrow`) into `Measure.pi` form, then apply
`klDiv_pi_eq_sum`. -/
private theorem mutualInfoOfChannel_pi_iid_eq_nsmul
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ)
    (p₀ : Measure α) [IsProbabilityMeasure p₀] :
    mutualInfoOfChannel (Measure.pi (fun _ : Fin n => p₀)) (Channel.toBlock W n)
      = n • mutualInfoOfChannel p₀ W := by
  classical
  set q : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => p₀) with hq_def
  haveI : IsProbabilityMeasure q := by rw [hq_def]; infer_instance
  let e : (Fin n → α × β) ≃ᵐ (Fin n → α) × (Fin n → β) :=
    MeasurableEquiv.arrowProdEquivProdArrow α β (Fin n)
  -- The function form of `e.symm`: `fun z i => (z.1 i, z.2 i)`.
  have h_e_symm_fun :
      (e.symm : (Fin n → α) × (Fin n → β) → Fin n → α × β)
        = fun z i => (z.1 i, z.2 i) := by
    funext z i; rfl
  -- Measurability of the reshaped function.
  have h_reshape_meas :
      Measurable (fun z : (Fin n → α) × (Fin n → β) => fun i => (z.1 i, z.2 i)) := by
    refine measurable_pi_iff.mpr (fun i => ?_)
    exact ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  -- Step A: Joint pushed via e.symm equals `Measure.pi (fun _ => p₀ ⊗ₘ W)`.
  have h_joint_map :
      (q ⊗ₘ Channel.toBlock W n).map (e.symm : _ ≃ᵐ _)
        = Measure.pi (fun _ : Fin n => p₀ ⊗ₘ W) := by
    rw [show (e.symm : (Fin n → α) × (Fin n → β) → Fin n → α × β)
          = (fun z i => (z.1 i, z.2 i)) from h_e_symm_fun]
    -- Apply the structural bridge.
    have := toBlock_compProd_pi_factor (α := α) (β := β) W n (fun _ : Fin n => p₀)
    rw [hq_def]
    exact this
  -- Step B: `outputDistribution q (toBlock W n) = Measure.pi (fun _ => output p₀ W)`.
  -- Derived by pushing h_joint_map further via `fun f i => (f i).2`.
  have h_output_pi :
      outputDistribution q (Channel.toBlock W n)
        = Measure.pi (fun _ : Fin n => outputDistribution p₀ W) := by
    -- output = (q ⊗ₘ toBlock W n).snd = .map Prod.snd.
    -- Note `(q ⊗ₘ toBlock W n).map Prod.snd = (q ⊗ₘ toBlock W n).map (fun z i => z.2 i)`
    -- via the fact that the codomain `Fin n → β` and `Prod.snd z` agree as functions of z.
    show ((q ⊗ₘ Channel.toBlock W n).map Prod.snd : Measure (Fin n → β))
      = Measure.pi (fun _ : Fin n => outputDistribution p₀ W)
    -- Compose: (q ⊗ₘ toBlock).map Prod.snd = ((q ⊗ₘ toBlock).map e.symm).map (fun f i => (f i).2).
    have h_comp :
        Prod.snd = (fun f : Fin n → α × β => fun i : Fin n => (f i).2)
          ∘ (e.symm : (Fin n → α) × (Fin n → β) → Fin n → α × β) := by
      funext z; rw [h_e_symm_fun]; rfl
    rw [h_comp, ← Measure.map_map (f := e.symm)
        (measurable_pi_iff.mpr (fun i => (measurable_pi_apply i).snd))
        e.symm.measurable]
    rw [h_joint_map]
    -- Now: (Measure.pi (fun _ => p₀ ⊗ₘ W)).map (fun f i => (f i).2)
    --   = Measure.pi (fun _ => (p₀ ⊗ₘ W).map Prod.snd)
    --   = Measure.pi (fun _ => outputDistribution p₀ W).
    rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
    rfl
  -- Step C: Marginal product pushed via e.symm equals `Measure.pi (fun _ => p₀.prod (output p₀ W))`.
  have h_marg_map :
      (q.prod (outputDistribution q (Channel.toBlock W n))).map (e.symm : _ ≃ᵐ _)
        = Measure.pi (fun _ : Fin n => p₀.prod (outputDistribution p₀ W)) := by
    rw [hq_def, h_output_pi]
    -- (Measure.pi p₀).prod (Measure.pi output) = (Measure.pi (fun i => p₀.prod output)).map e.
    have hmp := measurePreserving_arrowProdEquivProdArrow α β (Fin n)
      (fun _ : Fin n => p₀) (fun _ : Fin n => outputDistribution p₀ W)
    -- hmp.map_eq : (Measure.pi (fun _ => p₀.prod (output p₀ W))).map e
    --     = (Measure.pi (fun _ => p₀)).prod (Measure.pi (fun _ => output p₀ W))
    have h_step :
        ((Measure.pi (fun _ : Fin n => p₀)).prod
            (Measure.pi (fun _ : Fin n => outputDistribution p₀ W))).map e.symm
          = Measure.pi (fun _ : Fin n => p₀.prod (outputDistribution p₀ W)) := by
      rw [← hmp.map_eq, Measure.map_map e.symm.measurable e.measurable]
      simp [MeasurableEquiv.symm_comp_self]
    exact h_step
  -- Step D: klDiv invariance under e.symm + klDiv_pi_eq_sum + sum_const.
  unfold mutualInfoOfChannel
  -- The two sides we need to apply klDiv_map_measurableEquiv to.
  show klDiv (jointDistribution q (Channel.toBlock W n))
        (q.prod (outputDistribution q (Channel.toBlock W n)))
      = n • klDiv (jointDistribution p₀ W) (p₀.prod (outputDistribution p₀ W))
  rw [show jointDistribution q (Channel.toBlock W n) = q ⊗ₘ Channel.toBlock W n from rfl,
      ← klDiv_map_measurableEquiv e.symm
        (q ⊗ₘ Channel.toBlock W n)
        (q.prod (outputDistribution q (Channel.toBlock W n))),
      h_joint_map, h_marg_map]
  -- Now goal: klDiv (Measure.pi (fun _ => p₀ ⊗ₘ W)) (Measure.pi (fun _ => p₀.prod (output p₀ W)))
  --        = n • klDiv (p₀ ⊗ₘ W) (p₀.prod (output p₀ W))
  rw [klDiv_pi_eq_sum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-! ## Phase 4-α ≤ direction structure — per-letter marginal bridge

The ≤ direction `capacityN_ofMemoryless_le` requires reducing per-block MI to a sum
of per-letter MIs via the Cover-Thomas Thm 7.9 chain (subadditivity + memoryless
splitting of conditional entropy). The chain ultimately reduces to two
`IsMarkovChain` facts about `μ := q ⊗ₘ (Channel.toBlock W n)`, both of which require
non-trivial `condDistrib` discharge (~50-100 lines each in the existing Mathlib
infrastructure). These are **deferred** as `sorry` here, leaving the entire ≤
direction as a single placeholder bridge for now.

The ≥ direction (`capacityN_ofMemoryless_ge`) goes through cleanly via
`mutualInfoOfChannel_pi_iid_eq_nsmul`, providing the i.i.d.-input achievability of
`n · capacity W`. Combined with `capacityN_ofMemoryless_le` (once discharged), the
full equality `capacityN_ofMemoryless_eq` and limit form
`capacity_lim_eq_capacity_of_memoryless` follow as in the original plan.

The per-letter marginal bridge (`per_letter_marginal_eq_compProd`) and per-letter
MI identification (`mutualInfo_per_letter_eq_marginal`) below are kept as building
blocks for a future discharge attempt.
-/

section LeDirection

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β] in
/-- For `μ := q ⊗ₘ (toBlock W n)` with coordinate RVs `Xs i z := z.1 i`,
`Ys i z := z.2 i`, the per-letter marginal `μ.map (Xs i, Ys i)` equals
`(q.map (eval i)) ⊗ₘ W`. -/
private lemma per_letter_marginal_eq_compProd
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ)
    (q : Measure (Fin n → α)) [IsProbabilityMeasure q]
    (i : Fin n) :
    (q ⊗ₘ Channel.toBlock W n).map
        (fun z : (Fin n → α) × (Fin n → β) => (z.1 i, z.2 i))
      = (q.map (fun x : Fin n → α => x i)) ⊗ₘ W := by
  -- Measurability of the map.
  have hmap_meas : Measurable (fun z : (Fin n → α) × (Fin n → β) => (z.1 i, z.2 i)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  -- Singleton-level identity (both sides are probability measures on α × β finite).
  refine Measure.ext_of_singleton (fun ab => ?_)
  obtain ⟨a, b⟩ := ab
  -- RHS singleton: (q.map (eval i) ⊗ₘ W) {(a,b)} = q.map (eval i) {a} * W a {b}.
  have h_rhs :
      ((q.map (fun x : Fin n → α => x i)) ⊗ₘ W) ({(a, b)} : Set (α × β))
        = (q.map (fun x : Fin n → α => x i)) ({a} : Set α) * W a ({b} : Set β) := by
    rw [← Set.singleton_prod_singleton,
        Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
        lintegral_singleton, mul_comm]
  rw [h_rhs]
  -- LHS singleton: rewrite the preimage.
  -- ({(a, b)})ᵖ = {z | z.1 i = a ∧ z.2 i = b} = {x | x i = a} ×ˢ {y | y i = b}.
  have h_preimage :
      (fun z : (Fin n → α) × (Fin n → β) => (z.1 i, z.2 i)) ⁻¹' ({(a, b)} : Set (α × β))
        = ({x : Fin n → α | x i = a}) ×ˢ ({y : Fin n → β | y i = b}) := by
    ext ⟨x, y⟩
    simp [Prod.ext_iff]
  rw [Measure.map_apply hmap_meas (measurableSet_singleton _), h_preimage]
  -- compProd_apply_prod on the product set.
  have hset_a : MeasurableSet ({x : Fin n → α | x i = a}) := by
    have : {x : Fin n → α | x i = a} = (fun x => x i) ⁻¹' ({a} : Set α) := rfl
    rw [this]
    exact (measurable_pi_apply i) (measurableSet_singleton _)
  have hset_b : MeasurableSet ({y : Fin n → β | y i = b}) := by
    have : {y : Fin n → β | y i = b} = (fun y => y i) ⁻¹' ({b} : Set β) := rfl
    rw [this]
    exact (measurable_pi_apply i) (measurableSet_singleton _)
  rw [Measure.compProd_apply_prod hset_a hset_b]
  -- ∫⁻ x ∈ {x | x i = a}, (toBlock W n) x {y | y i = b} ∂q.
  -- Inner: (toBlock W n) x {y | y i = b} = (Measure.pi (W (x j))) {y | y i = b}
  --      = (W (x i)) {b}  (marginal property).
  have h_inner : ∀ x : Fin n → α,
      (Channel.toBlock W n) x ({y : Fin n → β | y i = b} : Set (Fin n → β))
        = W (x i) ({b} : Set β) := by
    intro x
    rw [Channel.toBlock_apply]
    -- (Measure.pi (fun j => W (x j))) ({y | y i = b})
    --   = (Measure.pi (fun j => W (x j))).map (eval i) {b}
    --   = W (x i) {b}  (via measurePreserving_eval for prob measure pi).
    have h_eval :
        (Measure.pi (fun j : Fin n => W (x j))).map (fun y : Fin n → β => y i) ({b} : Set β)
          = (Measure.pi (fun j : Fin n => W (x j))) ({y | y i = b}) := by
      rw [Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton _)]
      rfl
    -- measurePreserving_eval for the i.i.d. pi: (Measure.pi W·).map (eval i) = W (x i)
    have hmp := measurePreserving_eval (μ := fun j : Fin n => W (x j)) i
    rw [hmp.map_eq] at h_eval
    exact h_eval.symm
  simp_rw [h_inner]
  -- Now: ∫⁻ x ∈ {x | x i = a}, W (x i) {b} ∂q
  --    = W a {b} * q {x | x i = a}  (since W (x i) = W a on the set)
  --    = q.map (eval i) {a} * W a {b}.
  have h_eqOn : Set.EqOn (fun x : Fin n → α => W (x i) ({b} : Set β))
      (fun _ : Fin n → α => W a ({b} : Set β)) {x : Fin n → α | x i = a} := by
    intro x hx
    show W (x i) {b} = W a {b}
    rw [show x i = a from hx]
  rw [setLIntegral_congr_fun hset_a h_eqOn]
  rw [setLIntegral_const]
  rw [Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton _)]
  -- Goal: W a {b} * q ({x | x i = a}) = q ({x | x i = a}) * W a {b}.
  show W a {b} * q ({x | x i = a}) = q ({x | x i = a}) * W a {b}
  ring

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β] in
/-- Per-letter MI from the joint `q ⊗ₘ (toBlock W n)` equals MI of the i-th
input marginal of `q` against `W`. -/
private lemma mutualInfo_per_letter_eq_marginal
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ)
    (q : Measure (Fin n → α)) [IsProbabilityMeasure q]
    (i : Fin n) :
    InformationTheory.Shannon.mutualInfo (q ⊗ₘ Channel.toBlock W n)
        (fun z : (Fin n → α) × (Fin n → β) => z.1 i)
        (fun z : (Fin n → α) × (Fin n → β) => z.2 i)
      = mutualInfoOfChannel (q.map (fun x : Fin n → α => x i)) W := by
  -- Notation.
  set μ : Measure ((Fin n → α) × (Fin n → β)) := q ⊗ₘ Channel.toBlock W n with hμ_def
  set q_i : Measure α := q.map (fun x : Fin n → α => x i) with hq_i_def
  haveI : IsProbabilityMeasure q_i := by
    rw [hq_i_def]; exact Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  -- Step 1: μ.map (z => (z.1 i, z.2 i)) = q_i ⊗ₘ W.
  have h_joint_eq :
      μ.map (fun z : (Fin n → α) × (Fin n → β) => (z.1 i, z.2 i))
        = q_i ⊗ₘ W := by
    rw [hμ_def, hq_i_def]
    exact per_letter_marginal_eq_compProd W n q i
  -- Step 2: μ.map (z => z.1 i) = q_i.
  have h_X_marg :
      μ.map (fun z : (Fin n → α) × (Fin n → β) => z.1 i) = q_i := by
    -- μ.map (eval i ∘ Prod.fst) = (μ.fst).map (eval i) = q.map (eval i) = q_i.
    have h_comp : (fun z : (Fin n → α) × (Fin n → β) => z.1 i)
        = (fun x : Fin n → α => x i) ∘ Prod.fst := by funext z; rfl
    rw [h_comp, ← Measure.map_map (measurable_pi_apply i) measurable_fst]
    rw [show μ.map Prod.fst = μ.fst from rfl]
    rw [hμ_def, Measure.fst_compProd]
  -- Step 3: μ.map (z => z.2 i) = outputDistribution q_i W.
  have h_Y_marg :
      μ.map (fun z : (Fin n → α) × (Fin n → β) => z.2 i)
        = outputDistribution q_i W := by
    -- μ.map (z.2 i) = (μ.map (z => (z.1 i, z.2 i))).map Prod.snd
    --              = (q_i ⊗ₘ W).map Prod.snd = (q_i ⊗ₘ W).snd = output q_i W.
    have h_comp : (fun z : (Fin n → α) × (Fin n → β) => z.2 i)
        = Prod.snd ∘ (fun z : (Fin n → α) × (Fin n → β) => (z.1 i, z.2 i)) := by
      funext z; rfl
    have hmap_meas : Measurable (fun z : (Fin n → α) × (Fin n → β) => (z.1 i, z.2 i)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
    rw [h_comp, ← Measure.map_map measurable_snd hmap_meas, h_joint_eq]
    show ((q_i ⊗ₘ W).map Prod.snd) = outputDistribution q_i W
    rw [show (q_i ⊗ₘ W).map Prod.snd = (q_i ⊗ₘ W).snd from rfl]
    rfl
  -- Step 4: combine.
  unfold InformationTheory.Shannon.mutualInfo
  -- LHS = klDiv (μ.map (z.1 i, z.2 i)) ((μ.map z.1 i).prod (μ.map z.2 i)).
  rw [h_X_marg, h_Y_marg]
  rw [show μ.map (fun ω : (Fin n → α) × (Fin n → β) => (ω.1 i, ω.2 i))
       = μ.map (fun ω : (Fin n → α) × (Fin n → β) => (ω.1 i, ω.2 i)) from rfl]
  rw [h_joint_eq]
  rfl

/-- IsMarkovChain `(X^n) → X_i → Y_i` under `μ := q ⊗ₘ (toBlock W n)`.

**Status: deferred**. Mathematically true (the channel is per-letter memoryless,
so `Y_i` depends on `X^n` only through `X_i`). The proof reduces to identifying
`condDistrib (z.2 i) (z.1 i) μ =ᵐ W` (via `condDistrib_ae_eq_of_measure_eq_compProd`
+ `per_letter_marginal_eq_compProd`, ~10 lines) plus the compProd-of-prod-kernel
factorization of the triple joint `μ.map (z.1 i, z.1, z.2 i)` (~30-50 lines of
`compProd_congr` + `Kernel.prod` manipulations). Total: ~50-80 lines. -/
private lemma isMarkovChain_per_letter_input
    [StandardBorelSpace α] [StandardBorelSpace β]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ)
    (q : Measure (Fin n → α)) [IsProbabilityMeasure q]
    (i : Fin n) :
    InformationTheory.Shannon.IsMarkovChain (q ⊗ₘ Channel.toBlock W n)
      (fun z : (Fin n → α) × (Fin n → β) => z.1)
      (fun z : (Fin n → α) × (Fin n → β) => z.1 i)
      (fun z : (Fin n → α) × (Fin n → β) => z.2 i) := by
  sorry

/-- IsMarkovChain `Y^{≠i} → X^n → Y_i` under `μ := q ⊗ₘ (toBlock W n)`.

**Status: deferred**. Mathematically true (conditional on the full input `X^n`,
all coordinates of `Y^n` are independent due to the `Measure.pi` structure of
`Channel.toBlock W n`). The proof reduces to identifying the two condDistribs:
`condDistrib (z.2 i) (z.1) μ =ᵐ W.comap (eval i)` and similarly for the `{j ≠ i}`
product, plus the kernel-product factorization. ~50-100 lines. -/
private lemma isMarkovChain_outputs_cond_indep
    [StandardBorelSpace α] [StandardBorelSpace β]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ)
    (q : Measure (Fin n → α)) [IsProbabilityMeasure q]
    (i : Fin n) :
    InformationTheory.Shannon.IsMarkovChain (q ⊗ₘ Channel.toBlock W n)
      (fun (z : (Fin n → α) × (Fin n → β)) (j : {j : Fin n // j ≠ i}) => z.2 j.val)
      (fun z : (Fin n → α) × (Fin n → β) => z.1)
      (fun z : (Fin n → α) × (Fin n → β) => z.2 i) := by
  sorry

/-- Phase 4-α (≤ direction): block capacity is bounded by `n · capacity W`.

Strategy: for any block input `q`, apply `mutualInfo_le_sum_per_letter_of_memoryless_strong`
to `μ := q ⊗ₘ (toBlock W n)` with coordinate RVs `Xs i z := z.1 i`, `Ys i z := z.2 i`.
Each `I(X_i; Y_i) ≤ capacity W` follows from `mutualInfo_per_letter_eq_marginal` +
`mutualInfoOfChannel_toReal_le_capacity`. Sum gives `n · capacity W`. -/
private theorem capacityN_ofMemoryless_le
    [StandardBorelSpace α] [StandardBorelSpace β]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) (_hn : 0 < n) :
    (BlockwiseChannel.ofMemoryless W).capacityN n
      ≤ ENNReal.ofReal ((n : ℝ) * capacity W) := by
  unfold BlockwiseChannel.capacityN
  refine sSup_le ?_
  rintro v ⟨q, hq_prob, rfl⟩
  rw [Set.mem_setOf_eq] at hq_prob
  -- mutualInfoOfChannel q (ofMemoryless W n) ≤ ENNReal.ofReal (n * capacity W).
  show mutualInfoOfChannel q ((BlockwiseChannel.ofMemoryless W) n)
    ≤ ENNReal.ofReal ((n : ℝ) * capacity W)
  rw [show (BlockwiseChannel.ofMemoryless W) n = Channel.toBlock W n from rfl]
  haveI : IsProbabilityMeasure q := hq_prob
  -- Set up μ and per-letter RVs.
  set μ : Measure ((Fin n → α) × (Fin n → β)) := q ⊗ₘ Channel.toBlock W n with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  let Xs : Fin n → (Fin n → α) × (Fin n → β) → α := fun i z => z.1 i
  let Ys : Fin n → (Fin n → α) × (Fin n → β) → β := fun i z => z.2 i
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i =>
    (measurable_pi_apply i).comp measurable_fst
  have hYs_meas : ∀ i, Measurable (Ys i) := fun i =>
    (measurable_pi_apply i).comp measurable_snd
  -- Step 1: Strong-converse bound.
  have h_le := InformationTheory.Shannon.mutualInfo_le_sum_per_letter_of_memoryless_strong
    μ Xs Ys hXs_meas hYs_meas
    (isMarkovChain_per_letter_input W n q)
    (isMarkovChain_outputs_cond_indep W n q)
  -- Identify LHS with mutualInfoOfChannel q (toBlock W n).
  have h_joint_eq :
      InformationTheory.Shannon.mutualInfo μ (fun ω j => Xs j ω) (fun ω j => Ys j ω)
        = mutualInfoOfChannel q (Channel.toBlock W n) := by
    -- (fun ω j => Xs j ω) = (fun z => z.1) and (fun ω j => Ys j ω) = (fun z => z.2).
    have h_fst : (fun (ω : (Fin n → α) × (Fin n → β)) (j : Fin n) => Xs j ω)
        = (fun z : (Fin n → α) × (Fin n → β) => z.1) := by
      funext z j; rfl
    have h_snd : (fun (ω : (Fin n → α) × (Fin n → β)) (j : Fin n) => Ys j ω)
        = (fun z : (Fin n → α) × (Fin n → β) => z.2) := by
      funext z j; rfl
    rw [h_fst, h_snd]
    -- mutualInfo μ Prod.fst Prod.snd = mutualInfoOfChannel q (toBlock W n) by def + compProd.
    rw [show (fun z : (Fin n → α) × (Fin n → β) => z.1) = Prod.fst from rfl,
        show (fun z : (Fin n → α) × (Fin n → β) => z.2) = Prod.snd from rfl]
    rw [hμ_def]
    show InformationTheory.Shannon.mutualInfo (q ⊗ₘ Channel.toBlock W n) Prod.fst Prod.snd
      = mutualInfoOfChannel q (Channel.toBlock W n)
    rw [mutualInfoOfChannel_eq_mutualInfo_prod q (Channel.toBlock W n)]
    rfl
  -- Step 2: Bound each I(X_i; Y_i) ≤ capacity W.
  have h_per_letter_bound : ∀ i : Fin n,
      (InformationTheory.Shannon.mutualInfo μ (Xs i) (Ys i)).toReal ≤ capacity W := by
    intro i
    have h_eq := mutualInfo_per_letter_eq_marginal W n q i
    -- h_eq : mutualInfo μ (Xs i) (Ys i) = mutualInfoOfChannel (q.map (eval i)) W.
    haveI : IsProbabilityMeasure (q.map (fun x : Fin n → α => x i)) := by
      exact Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
    rw [show (fun z : (Fin n → α) × (Fin n → β) => z.1 i) = Xs i from rfl,
        show (fun z : (Fin n → α) × (Fin n → β) => z.2 i) = Ys i from rfl] at h_eq
    rw [h_eq]
    exact mutualInfoOfChannel_toReal_le_capacity W _
  -- Step 3: combine.
  have h_sum_bound :
      (∑ i : Fin n, (InformationTheory.Shannon.mutualInfo μ (Xs i) (Ys i)).toReal)
        ≤ (n : ℝ) * capacity W := by
    have : (∑ _i : Fin n, capacity W) = (n : ℝ) * capacity W := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← this]
    exact Finset.sum_le_sum (fun i _ => h_per_letter_bound i)
  have h_real_bound :
      (mutualInfoOfChannel q (Channel.toBlock W n)).toReal ≤ (n : ℝ) * capacity W := by
    rw [← h_joint_eq]
    exact h_le.trans h_sum_bound
  -- Convert real bound to ENNReal.ofReal bound.
  -- mutualInfoOfChannel q (toBlock W n) is finite.
  have h_MI_fin : mutualInfoOfChannel q (Channel.toBlock W n) ≠ ∞ := by
    rw [mutualInfoOfChannel_eq_mutualInfo_prod q (Channel.toBlock W n)]
    exact InformationTheory.Shannon.mutualInfo_ne_top
      (q ⊗ₘ Channel.toBlock W n) Prod.fst Prod.snd measurable_fst measurable_snd
  have hC_nn : 0 ≤ capacity W := capacity_nonneg W
  have hmul_nn : 0 ≤ (n : ℝ) * capacity W := mul_nonneg (Nat.cast_nonneg n) hC_nn
  -- ENNReal.ofReal (toReal_MI) ≤ ENNReal.ofReal (n * C).
  rw [← ENNReal.ofReal_toReal h_MI_fin]
  exact ENNReal.ofReal_le_ofReal h_real_bound

end LeDirection

/-- Phase 4-α (≥ direction): block capacity is bounded below by `n · capacity W`.

Strategy: pick the capacity achiever `p_opt ∈ stdSimplex` via `exists_capacity_achiever`,
use `q := Measure.pi (fun _ => pmfToMeasure p_opt)` as the i.i.d. block input, and
apply `mutualInfoOfChannel_pi_iid_eq_nsmul` to get
`MI(q, toBlock W n) = n • MI(p_opt, W) = n • capacity W` (in ENNReal). The `sSup`
in `capacityN` then witnesses `n • capacity W` as a lower bound. -/
private theorem capacityN_ofMemoryless_ge
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) (_hn : 0 < n) :
    ENNReal.ofReal ((n : ℝ) * capacity W)
      ≤ (BlockwiseChannel.ofMemoryless W).capacityN n := by
  classical
  -- Get capacity achiever p_opt (a maximizer of MI on stdSimplex).
  obtain ⟨p_opt, hp_opt_mem, hp_opt_max⟩ := exists_capacity_achiever W
  -- Use q := Measure.pi (fun _ => pmfToMeasure p_opt) as block input.
  set p₀ : Measure α := pmfToMeasure p_opt with hp₀_def
  haveI : IsProbabilityMeasure p₀ := by
    rw [hp₀_def]; exact pmfToMeasure_isProbabilityMeasure hp_opt_mem
  set q : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => p₀) with hq_def
  haveI : IsProbabilityMeasure q := by rw [hq_def]; infer_instance
  -- Apply the iid product MI identity.
  have h_mi_eq : mutualInfoOfChannel q (Channel.toBlock W n)
      = n • mutualInfoOfChannel p₀ W := by
    rw [hq_def]; exact mutualInfoOfChannel_pi_iid_eq_nsmul W n p₀
  -- Extract MI(p_opt; W).toReal = capacity W from `IsMaxOn`.
  have h_C_eq : (mutualInfoOfChannel p₀ W).toReal = capacity W := by
    refine le_antisymm ?_ ?_
    · -- ≤: MI(p_opt; W).toReal ≤ capacity W by csSup (le_csSup).
      rw [hp₀_def]
      exact mutualInfoOfChannel_toReal_le_capacity W _
    · -- ≥: capacity W = sSup (image) ≤ MI(p_opt; W).toReal since p_opt is a max.
      unfold capacity
      refine csSup_le (capacity_image_nonempty W) ?_
      rintro v ⟨p, hp_mem, rfl⟩
      exact hp_opt_max hp_mem
  -- mutualInfoOfChannel p₀ W is finite (finite alphabet).
  have h_MI_fin : mutualInfoOfChannel p₀ W ≠ ∞ := by
    rw [mutualInfoOfChannel_eq_mutualInfo_prod p₀ W]
    exact InformationTheory.Shannon.mutualInfo_ne_top (jointDistribution p₀ W)
      Prod.fst Prod.snd measurable_fst measurable_snd
  -- q is a probability measure on (Fin n → α), so q ∈ image-defining set of capacityN.
  -- Use le_csSup pattern.
  unfold BlockwiseChannel.capacityN
  refine le_sSup ?_
  -- Show: ENNReal.ofReal (n * capacity W) ∈ image.
  refine ⟨q, by rw [Set.mem_setOf_eq]; infer_instance, ?_⟩
  -- mutualInfoOfChannel q (ofMemoryless W n) = ENNReal.ofReal (n * capacity W).
  show mutualInfoOfChannel q ((BlockwiseChannel.ofMemoryless W) n)
    = ENNReal.ofReal ((n : ℝ) * capacity W)
  rw [show (BlockwiseChannel.ofMemoryless W) n = Channel.toBlock W n from rfl]
  rw [h_mi_eq]
  -- n • mutualInfoOfChannel p₀ W = ENNReal.ofReal (n * capacity W).
  rw [show mutualInfoOfChannel p₀ W = ENNReal.ofReal (capacity W) by
        rw [← h_C_eq, ENNReal.ofReal_toReal h_MI_fin]]
  -- n • ENNReal.ofReal (capacity W) = ENNReal.ofReal (n * capacity W).
  rw [nsmul_eq_mul]
  have hC_nn : 0 ≤ capacity W := capacity_nonneg W
  rw [← ENNReal.ofReal_natCast n,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]

/-- Phase 4-α: per-`n` block-capacity equality for memoryless `W`.

Note: `[StandardBorelSpace α/β]` is added to satisfy the Cover-Thomas Thm 7.9
route used in the ≤ direction (`mutualInfo_le_sum_per_letter_of_memoryless_strong`).
Both are auto-derived on `[Fintype α] [MeasurableSingletonClass α]` via the
`MeasurableSingletonClass + Countable → DiscreteMeasurableSpace → StandardBorelSpace`
instance chain. -/
theorem capacityN_ofMemoryless_eq
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) (_hn : 0 < n) :
    (BlockwiseChannel.ofMemoryless W).capacityN n
      = ENNReal.ofReal ((n : ℝ) * capacity W) :=
  le_antisymm (capacityN_ofMemoryless_le W n _hn) (capacityN_ofMemoryless_ge W n _hn)

/-! ## Phase 4-β — `capacity_lim_eq_capacity_of_memoryless` -/

/-- Phase 4-β: limit form matches the single-letter `capacity W` in the
memoryless case. Direct from Phase 4-α (the sequence is eventually the constant
`capacity W`). -/
theorem capacity_lim_eq_capacity_of_memoryless
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
    (W : Channel α β) [IsMarkovKernel W] :
    (BlockwiseChannel.ofMemoryless W).capacity_lim = capacity W := by
  have hC_nn : 0 ≤ capacity W := capacity_nonneg W
  have h_eq_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        ((BlockwiseChannel.ofMemoryless W).capacityN n).toReal / (n : ℝ) = capacity W := by
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn_pos : 0 < n := hn
    have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hN := capacityN_ofMemoryless_eq W n hn_pos
    rw [hN]
    have hmul_nn : 0 ≤ (n : ℝ) * capacity W := mul_nonneg (by exact_mod_cast hn_pos.le) hC_nn
    rw [ENNReal.toReal_ofReal hmul_nn]
    field_simp
  have h_tendsto :
      Filter.Tendsto
        (fun n : ℕ => ((BlockwiseChannel.ofMemoryless W).capacityN n).toReal / (n : ℝ))
        Filter.atTop (nhds (capacity W)) := by
    refine (tendsto_const_nhds (x := capacity W)).congr' ?_
    exact h_eq_eventually.mono (fun n hn => hn.symm)
  unfold BlockwiseChannel.capacity_lim
  exact h_tendsto.limUnder_eq

end InformationTheory.Shannon.ChannelCoding

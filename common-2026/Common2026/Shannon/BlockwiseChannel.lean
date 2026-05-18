import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.ChannelCodingShannonTheorem
import Common2026.Shannon.MIChainRule
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

/-! ## Phase 4-α — `capacityN_ofMemoryless_eq` (per-`n` equality) -/

/-- Phase 4-α (≤ direction): block capacity is bounded by `n · capacity W`. -/
private theorem capacityN_ofMemoryless_le
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) (_hn : 0 < n) :
    (BlockwiseChannel.ofMemoryless W).capacityN n
      ≤ ENNReal.ofReal ((n : ℝ) * capacity W) := by
  sorry

/-- Phase 4-α (≥ direction): block capacity is bounded below by `n · capacity W`.

**Sketch** (deferred to next session — see plan §H-4):
1. Get capacity-achiever `p_opt ∈ stdSimplex` via `exists_capacity_achiever`.
2. Use `q := Measure.pi (fun _ => pmfToMeasure p_opt)` as the i.i.d. input.
3. Apply `mutualInfo_iid_eq_nsmul` to `μ := q ⊗ₘ (toBlock W n)` with
   `Xs i ω := ω.1 i`, `Ys i ω := ω.2 i`:
   - All 6 i.i.d. hypotheses follow from `toBlock_compProd_pi_factor` (already
     discharged above) + `Measure.pi_map_pi`/`Measure.fst_compProd`.
4. Resulting `(MI q (toBlock W n)) = n • (MI p_opt W)`. Take `.toReal` and conclude. -/
private theorem capacityN_ofMemoryless_ge
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) (_hn : 0 < n) :
    ENNReal.ofReal ((n : ℝ) * capacity W)
      ≤ (BlockwiseChannel.ofMemoryless W).capacityN n := by
  sorry

/-- Phase 4-α: per-`n` block-capacity equality for memoryless `W`. -/
theorem capacityN_ofMemoryless_eq
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
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
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
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

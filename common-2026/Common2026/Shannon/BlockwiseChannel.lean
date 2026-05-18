import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.ChannelCodingShannonTheorem
import Common2026.Shannon.MIChainRule
import Mathlib.Analysis.Subadditive
import Mathlib.MeasureTheory.Constructions.Pi

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
* `Channel.toBlock W n`  — inductive product kernel `W^{⊗n}`.
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
* `Channel.toBlock` is built inductively via `MeasurableEquiv.piFinSuccAbove`
  (Mathlib has no `Kernel.pi` for finite product of kernels).
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

Built inductively via `MeasurableEquiv.piFinSuccAbove 0`:

* `Channel.toBlock W 0 = Kernel.const _ (Measure.dirac default)`
  (degenerate — the only function `Fin 0 → β` is the trivial one).
* `Channel.toBlock W (n+1)` is obtained by:
  - Splitting `Fin (n+1) → α ≃ᵐ α × (Fin n → α)` via `piFinSuccAbove 0`.
  - Forming the parallel kernel `W ×ₖ (Channel.toBlock W n)` (after `comap`).
  - Mapping back to `Fin (n+1) → β` via the same equiv on the codomain.
-/

/-- Inductive `Kernel.pi` for the constant-family case (memoryless extension). -/
noncomputable def Channel.toBlock (W : Channel α β) : (n : ℕ) → Kernel (Fin n → α) (Fin n → β)
  | 0 => Kernel.const _ (Measure.dirac default)
  | n + 1 =>
    -- `e : (Fin (n+1) → γ) ≃ᵐ γ × (Fin n → γ)` for γ = α (via `piFinSuccAbove 0`).
    let eα : (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
    let eβ : (Fin (n + 1) → β) ≃ᵐ β × (Fin n → β) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => β) 0
    -- precompose `W ×ₖ toBlock W n` with `eα`, then push forward by `eβ.symm`.
    (((W.comap (Prod.fst : α × (Fin n → α) → α) measurable_fst) ×ₖ
      ((Channel.toBlock W n).comap (Prod.snd : α × (Fin n → α) → Fin n → α)
        measurable_snd)).comap eα eα.measurable).map eβ.symm

/-- `Channel.toBlock W n` is a Markov kernel when `W` is. -/
instance Channel.toBlock.instIsMarkovKernel (W : Channel α β) [IsMarkovKernel W] :
    ∀ n : ℕ, IsMarkovKernel (Channel.toBlock W n)
  | 0 => by
      unfold Channel.toBlock
      infer_instance
  | n + 1 => by
      unfold Channel.toBlock
      have _ : IsMarkovKernel (Channel.toBlock W n) := Channel.toBlock.instIsMarkovKernel W n
      exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.measurable _)

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
`capacity_lim W := lim_{n → ∞} (capacityN W n).toReal / n`.

When the limit does not exist this returns Mathlib's junk value `0`. The
memoryless specialization (`capacity_lim_eq_capacity_of_memoryless`) provides
the only existence guarantee in this file; general subadditivity (Fekete) is
out of scope for the I-2 seed. -/
noncomputable def BlockwiseChannel.capacity_lim (W : BlockwiseChannel α β) : ℝ :=
  Filter.atTop.limUnder (fun n : ℕ => (W.capacityN n).toReal / n)

/-! ## Phase 4-α — `capacityN_ofMemoryless_eq` (per-`n` equality)

When `W_n = W^{⊗n}` is the memoryless extension of a single-letter Markov kernel,
the block capacity is `n · capacity W`. The `≥` direction is achieved by the
i.i.d. input `p^n` where `p` is the single-letter capacity-achieving distribution
(`mutualInfo_iid_eq_nsmul`). The `≤` direction follows from
`mutualInfo_le_sum_per_letter_of_memoryless_strong`.

**Status (2026-05-18 持ち越し)**: Split into two one-sided lemmas
(`capacityN_ofMemoryless_le` and `capacityN_ofMemoryless_ge`) per plan §H-4,
each with a single `sorry` documenting the **structural bridge facts** that are
not yet in Mathlib or `Common2026/Shannon/`:

* **For `≤`**: requires `IsMemorylessChannelStrong` instance for the joint
  `Measure.pi`-pushforward of `p ⊗ₘ W.toBlock n` (per-letter Markov + outputs
  conditional independence). The inductive `Channel.toBlock` definition does
  NOT yet have a structural equality identifying `p ⊗ₘ W.toBlock n` with the
  IID joint `Measure.pi (fun i => p_i ⊗ₘ W)` (transported through the canonical
  `(Fin n → α) × (Fin n → β) ≃ᵐ Fin n → (α × β)` equiv). This bridge is the
  rate-limiting step (~80-150 lines of measure-theoretic plumbing, NOT in
  Mathlib — see plan §H-1 / §H-4).

* **For `≥`**: requires the same bridge fact specialized to the IID case
  `p_i := pmfToMeasure p_opt` for the capacity-achieving `p_opt`, combined with
  `mutualInfo_iid_eq_nsmul` (`MIChainRule.lean:392`). The 6 i.i.d. hypotheses of
  `mutualInfo_iid_eq_nsmul` are discharged by `Measure.infinitePi_map_eval` +
  marginal computations on `Measure.pi`, but require the same `compProd` ↔
  `Measure.pi` structural bridge as `≤`.

The shared structural gap is captured in the auxiliary statement
`toBlock_compProd_pi_factor` below (also `sorry`), which would carry both
directions.

Recommendation: escalate to `proof-pivot-advisor` for the
`toBlock_compProd_pi_factor` bridge. Likely outcome is to redefine
`Channel.toBlock` directly via `Measure.pi` (with manual measurability witness)
rather than the inductive `piFinSuccAbove` construction, so that the bridge
becomes definitionally trivial. See plan §H-1 (Kernel.pi helper split). -/

/-- **Structural bridge (sorry — needs proof-pivot)**. For any product input
`p_i : Fin n → Measure α` (each `IsProbabilityMeasure`) and Markov `W`, the
joint distribution `(Measure.pi p_i) ⊗ₘ (W.toBlock n)` on `(Fin n → α) × (Fin n → β)`,
pushed through the canonical equiv `(Fin n → α) × (Fin n → β) ≃ᵐ Fin n → (α × β)`,
factors as `Measure.pi (fun i => p_i ⊗ₘ W)`.

This is the **rate-limiting bridge** for Phase 4-α (both directions).
NOT in Mathlib (`loogle "MeasureTheory.Measure.compProd, MeasureTheory.Measure.pi"`
returns 0). Without it, `mutualInfo_iid_eq_nsmul` and
`mutualInfo_le_sum_per_letter_of_memoryless_strong` cannot be invoked on
`Channel.toBlock`.

Pragmatic resolution: redefine `Channel.toBlock` directly as `Kernel.mk` of
`fun x => Measure.pi (fun i => W (x i))` with explicit measurability proof
(see plan §H-1, ~30-50 lines), then this lemma becomes definitional. -/
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
  sorry

/-- Phase 4-α (≤ direction): block capacity is bounded by `n · capacity W`.

Proof skeleton (deferred to next session):
1. Apply `sSup_le`: take an arbitrary probability measure `q : Measure (Fin n → α)`.
2. Express `mutualInfoOfChannel q (W.toBlock n)` via `mutualInfoOfChannel_eq_mutualInfo_prod`
   as `mutualInfo (q ⊗ₘ W.toBlock n) Prod.fst Prod.snd`.
3. Build the ambient `Ω := (Fin n → α) × (Fin n → β)` with `μ := q ⊗ₘ W.toBlock n`.
   Define `Xs i ω := ω.1 i`, `Ys i ω := ω.2 i`.
4. Apply `mutualInfo_le_sum_per_letter_of_memoryless_strong` — requires
   `IsMemorylessChannelStrong` axioms on `(μ, Xs, Ys)`, derivable from
   `toBlock_compProd_pi_factor` (since under the pushforward the kernel is per-letter
   `W` independently of other coordinates).
5. Each summand `≤ capacity W` via `le_csSup` (sup over `pmfToMeasure` covers all
   marginal measures on finite α).
6. Sum gives `n * capacity W`. -/
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

Proof skeleton (deferred to next session):
1. Apply `le_sSup`: exhibit a probability measure `p_n : Measure (Fin n → α)` with
   `mutualInfoOfChannel p_n (W.toBlock n) ≥ ENNReal.ofReal (n * capacity W)`.
2. Take `p_opt := pmfToMeasure p_opt_pmf` for the capacity-achiever
   (`exists_capacity_achiever` from `ChannelCodingShannonTheorem.lean:317`).
3. Set `p_n := Measure.pi (fun _ : Fin n => p_opt)`.
4. Compute `mutualInfoOfChannel p_n (W.toBlock n) = n • mutualInfoOfChannel p_opt W`:
   a. Apply `mutualInfoOfChannel_eq_mutualInfo_prod`.
   b. Use `toBlock_compProd_pi_factor` to rewrite the joint as
      `Measure.pi (fun _ : Fin n => p_opt ⊗ₘ W)`.
   c. Apply `mutualInfo_iid_eq_nsmul` with the 6 hypotheses discharged by
      `Measure.pi_map_eval` (marginal) + product-form / IID copy properties.
5. Cast `.toReal` via `ENNReal.toReal_ofReal` and conclude. -/
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

/-- Phase 4-α: per-`n` block-capacity equality for memoryless `W`.

Proof: combine `capacityN_ofMemoryless_le` and `capacityN_ofMemoryless_ge` via
`le_antisymm`. The two halves remain `sorry` (carrying the deferred structural
bridge `toBlock_compProd_pi_factor`); the main theorem itself has its proof
fully expressed. -/
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
  -- For `n ≥ 1`, Phase 4-α gives `(capacityN (ofMemoryless W) n).toReal = n * capacity W`,
  -- so `(capacityN _).toReal / n = capacity W`. The sequence is eventually constant.
  have hC_nn : 0 ≤ capacity W := capacity_nonneg W
  -- Build the eventual-equality witness.
  have h_eq_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        ((BlockwiseChannel.ofMemoryless W).capacityN n).toReal / (n : ℝ) = capacity W := by
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn_pos : 0 < n := hn
    have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hN := capacityN_ofMemoryless_eq W n hn_pos
    rw [hN]
    -- ENNReal.ofReal (n * capacity W).toReal = n * capacity W since `n * capacity W ≥ 0`.
    have hmul_nn : 0 ≤ (n : ℝ) * capacity W := mul_nonneg (by exact_mod_cast hn_pos.le) hC_nn
    rw [ENNReal.toReal_ofReal hmul_nn]
    field_simp
  -- The constant sequence tends to its constant.
  have h_tendsto :
      Filter.Tendsto
        (fun n : ℕ => ((BlockwiseChannel.ofMemoryless W).capacityN n).toReal / (n : ℝ))
        Filter.atTop (nhds (capacity W)) := by
    refine (tendsto_const_nhds (x := capacity W)).congr' ?_
    exact h_eq_eventually.mono (fun n hn => hn.symm)
  -- Apply `limUnder_eq`.
  unfold BlockwiseChannel.capacity_lim
  exact h_tendsto.limUnder_eq

end InformationTheory.Shannon.ChannelCoding

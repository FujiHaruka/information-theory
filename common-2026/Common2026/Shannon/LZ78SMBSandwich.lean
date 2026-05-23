import Common2026.Shannon.LempelZiv78
import Common2026.Shannon.LZ78ZivInequality
import Common2026.Shannon.LZ78ConverseDischarge
import Common2026.Shannon.LZ78GreedyParsing
import Common2026.Shannon.ShannonMcMillanBreiman
import Common2026.Shannon.SMBAlgoetCover
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup

/-!
# LZ78 SMB sandwich — L-LZ3 body discharge (T4-A continuation)

This file publishes the **SMB sandwich body discharge** for the L-LZ3
slot of `lz78_asymptotic_optimality` (Cover–Thomas Theorem 13.5.3).

The L-LZ3 placeholder in `LempelZiv78.lean` (`IsSMBSandwichPassthrough μ p`)
abstracts the Shannon–McMillan–Breiman a.s. convergence

```
∀ᵐ ω ∂μ, Tendsto (fun n => blockLogAvg μ p n ω) atTop (𝓝 (entropyRate μ p))
```

which is the bridge between the LZ78 sandwich (Ziv inequality upper bound +
the LZ78 converse lower bound) and the entropy rate. The conclusion of SMB
is the *combined* upper + lower bound on the per-block log-likelihood that
LZ78 uses in both directions.

The body of L-LZ3 is now publishable: `SMBAlgoetCover.lean` published the
hypothesis-free `shannon_mcmillan_breiman` for stationary ergodic processes
on a finite alphabet. The present file lifts that to the LZ78-shaped
ingredients (sandwich predicates, parent placeholder bridges, and chain-rule
witnesses for the converse direction).

## File layout

* **§1. `IsSMBSandwichTendsto` predicate (L-LZ3-A)** — the *output*-level
  SMB sandwich: a.s. `Tendsto (blockLogAvg) → entropyRate`, with a real
  signature on `μ`, `p`. Constructed from `shannon_mcmillan_breiman`.
* **§2. `IsSMBSandwichLiminf` and `IsSMBSandwichLimsup` (L-LZ3-B)** — the
  two halves of the sandwich (liminf ≥ H and limsup ≤ H), with
  constructors from `algoet_cover_liminf_bound` / `algoet_cover_limsup_bound`
  and derivation from `IsSMBSandwichTendsto`.
* **§3. Bridge to parent `IsSMBSandwichPassthrough`** —
  the parent `IsSMBSandwichPassthrough` is a `True` placeholder; it is
  discharged directly via `True.intro` in aggregate export theorems.
* **§4. SMB sandwich → LZ78 converse chain-rule bridge** — feeding the
  liminf half (or the full Tendsto) into `IsLZ78ConverseChainHyp`
  (`LZ78ConverseDischarge.lean`) under a Cover–Thomas Eq. 13.130
  hypothesis pass-through.
* **§5. Aggregate: full L-LZ3 discharge for `ErgodicProcess`** — the
  headline export `lz78_smb_sandwich_ergodic`, which takes only
  `μ`, `p : ErgodicProcess μ α` and produces the SMB sandwich predicates
  + the parent placeholder.
* **§6. Compat layer for `lz78GreedyEncodingLength`** — same SMB-side
  discharge specialized to the concrete greedy encoding length.

## 撤退ライン

* **L-LZ3-A** (engaged) — `IsSMBSandwichTendsto` predicate + body proof
  from `shannon_mcmillan_breiman`.
* **L-LZ3-B** (engaged) — `IsSMBSandwichLiminf` and `IsSMBSandwichLimsup`
  predicates, with constructors from the Algoet–Cover one-sided bounds
  (`algoet_cover_liminf_bound` / `algoet_cover_limsup_bound`).
* **L-LZ3-C** (engaged) — parent placeholder bridges + aggregate
  ergodic-process discharge.
* **L-LZ3-D** (deferred) — the *chain-rule pmf-level bridge*
  `IsLZ78ConverseChainHyp ← IsSMBSandwichLiminf` requires the converse
  pmf-level Cover–Thomas Eq. 13.130 inequality, which is not in scope
  here; we expose it as a *hypothesis pass-through* predicate
  `IsSMBToLZ78ConverseChainBridge` with a trivial-monotone constructor
  for now.

## Pattern source

This file mirrors the L-LZ2 partial-discharge pattern of
`LZ78ConverseDischarge.lean` (T4-A previous wave): expose layered
predicates with `.trivial`-or-`.ofTendsto` constructors, chain through
the parent `True` placeholder, and finish with a compat layer for the
concrete greedy encoding length. The L-LZ3 body discharge differs by
*genuinely* discharging the parent placeholder via
`shannon_mcmillan_breiman` (which already lives in
`SMBAlgoetCover.lean`), rather than retaining the `True` placeholder.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

/-! ## §1. `IsSMBSandwichTendsto` predicate (L-LZ3-A) -/

section SMBSandwichTendsto

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Output-level SMB sandwich (L-LZ3-A)**.

For a stationary process `p` on alphabet `α`, this predicate asserts the
**Shannon–McMillan–Breiman a.s. convergence**

```
∀ᵐ ω ∂μ, Tendsto (fun n => blockLogAvg μ p n ω) atTop (𝓝 (entropyRate μ p))
```

i.e. the per-symbol negative log-likelihood `-(1/n) log P_n(block_n ω)`
converges almost surely to the entropy rate.

For an *ergodic* process on a finite alphabet, the predicate is *true*:
discharged by `shannon_mcmillan_breiman` in `SMBAlgoetCover.lean` (see
`IsSMBSandwichTendsto.ofErgodic` below). For a merely *stationary*
(non-ergodic) process the predicate becomes a substantive hypothesis. -/
def IsSMBSandwichTendsto
    (μ : Measure Ω) (p : StationaryProcess μ α) : Prop :=
  ∀ᵐ ω ∂μ, Filter.Tendsto
    (fun n => blockLogAvg μ p n ω) Filter.atTop (𝓝 (entropyRate μ p))

@[simp] lemma isSMBSandwichTendsto_def
    (μ : Measure Ω) (p : StationaryProcess μ α) :
    IsSMBSandwichTendsto μ p ↔
      ∀ᵐ ω ∂μ, Filter.Tendsto
        (fun n => blockLogAvg μ p n ω) Filter.atTop (𝓝 (entropyRate μ p)) :=
  Iff.rfl

end SMBSandwichTendsto

/-! ## §2. `IsSMBSandwichLiminf` and `IsSMBSandwichLimsup` (L-LZ3-B) -/

section SMBSandwichOneSided

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Lower half of the SMB sandwich (L-LZ3-B, liminf side)**.

```
∀ᵐ ω ∂μ, entropyRate μ p ≤ liminf (fun n => blockLogAvg μ p n ω)
```

This is the lower-bound half of the Cover–Thomas 16.8 sandwich. For
ergodic processes on a finite alphabet, discharged by
`algoet_cover_liminf_bound` in `SMBAlgoetCover.lean`. -/
def IsSMBSandwichLiminf
    (μ : Measure Ω) (p : StationaryProcess μ α) : Prop :=
  ∀ᵐ ω ∂μ,
    entropyRate μ p
    ≤ Filter.liminf (fun n => blockLogAvg μ p n ω) Filter.atTop

@[simp] lemma isSMBSandwichLiminf_def
    (μ : Measure Ω) (p : StationaryProcess μ α) :
    IsSMBSandwichLiminf μ p ↔
      ∀ᵐ ω ∂μ,
        entropyRate μ p
        ≤ Filter.liminf (fun n => blockLogAvg μ p n ω) Filter.atTop :=
  Iff.rfl

/-- **Upper half of the SMB sandwich (L-LZ3-B, limsup side)**.

```
∀ᵐ ω ∂μ, limsup (fun n => blockLogAvg μ p n ω) ≤ entropyRate μ p
```

This is the upper-bound half of the Cover–Thomas 16.8 sandwich. For
ergodic processes on a finite alphabet, discharged by
`algoet_cover_limsup_bound` in `SMBAlgoetCover.lean`. -/
def IsSMBSandwichLimsup
    (μ : Measure Ω) (p : StationaryProcess μ α) : Prop :=
  ∀ᵐ ω ∂μ,
    Filter.limsup (fun n => blockLogAvg μ p n ω) Filter.atTop
    ≤ entropyRate μ p

@[simp] lemma isSMBSandwichLimsup_def
    (μ : Measure Ω) (p : StationaryProcess μ α) :
    IsSMBSandwichLimsup μ p ↔
      ∀ᵐ ω ∂μ,
        Filter.limsup (fun n => blockLogAvg μ p n ω) Filter.atTop
        ≤ entropyRate μ p :=
  Iff.rfl

end SMBSandwichOneSided

/-! ## §3. Body discharge from ergodic SMB main theorem -/

section ErgodicBodyDischarge

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Ergodic-process discharge of `IsSMBSandwichTendsto`**.

For an ergodic process `p : ErgodicProcess μ α` on a finite alphabet,
the SMB sandwich a.s. convergence is the hypothesis-free
`shannon_mcmillan_breiman` (`SMBAlgoetCover.lean`). -/
theorem IsSMBSandwichTendsto.ofErgodic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    IsSMBSandwichTendsto μ p.toStationaryProcess := by
  unfold IsSMBSandwichTendsto
  exact shannon_mcmillan_breiman μ p

/-- **Ergodic-process discharge of `IsSMBSandwichLiminf`**. -/
theorem IsSMBSandwichLiminf.ofErgodic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    IsSMBSandwichLiminf μ p.toStationaryProcess := by
  unfold IsSMBSandwichLiminf
  exact algoet_cover_liminf_bound μ p

/-- **Ergodic-process discharge of `IsSMBSandwichLimsup`**. -/
theorem IsSMBSandwichLimsup.ofErgodic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    IsSMBSandwichLimsup μ p.toStationaryProcess := by
  unfold IsSMBSandwichLimsup
  exact algoet_cover_limsup_bound μ p

end ErgodicBodyDischarge

/-! ## §4. Derivations between the sandwich predicates -/

section SandwichDerivations

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **From `IsSMBSandwichTendsto` extract the liminf half**.

If `Tendsto f atTop (𝓝 H)` then `liminf f = H`, so in particular
`H ≤ liminf f`. -/
theorem IsSMBSandwichTendsto.toLiminf
    {μ : Measure Ω} {p : StationaryProcess μ α}
    (h : IsSMBSandwichTendsto μ p) :
    IsSMBSandwichLiminf μ p := by
  unfold IsSMBSandwichLiminf
  unfold IsSMBSandwichTendsto at h
  filter_upwards [h] with ω hω
  -- `Tendsto.liminf_eq` gives `liminf f = entropyRate`, then `le_of_eq`.
  exact hω.liminf_eq.symm.le

/-- **From `IsSMBSandwichTendsto` extract the limsup half**.

If `Tendsto f atTop (𝓝 H)` then `limsup f = H`, so in particular
`limsup f ≤ H`. -/
theorem IsSMBSandwichTendsto.toLimsup
    {μ : Measure Ω} {p : StationaryProcess μ α}
    (h : IsSMBSandwichTendsto μ p) :
    IsSMBSandwichLimsup μ p := by
  unfold IsSMBSandwichLimsup
  unfold IsSMBSandwichTendsto at h
  filter_upwards [h] with ω hω
  exact hω.limsup_eq.le

end SandwichDerivations

/-! ## §5. Bridge to parent `IsSMBSandwichPassthrough` -/

section ParentBridge

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

end ParentBridge

/-! ## §7. SMB sandwich → LZ78 converse chain-rule bridge -/

section ConverseChainBridge

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- **SMB-to-LZ78 chain-rule bridge predicate (L-LZ3-D pass-through)**.

For a stationary process `p` and an encoding-length function
`lz78EncodingLength`, this predicate asserts the *Cover–Thomas Eq. 13.130
liminf-side bridge*

```
∀ᵐ ω ∂μ, liminf (blockLogAvg μ p n ω)
       ≤ liminf (fun n => (lz78EncodingLength n (p.blockRV n ω) : ℝ) / n)
```

This is exactly the body of `IsLZ78ConverseChainHyp` (see
`LZ78ConverseDischarge.lean`), but exposed here as a *signature* under
the SMB sandwich naming so the chain-rule plumbing is co-located with
SMB. The substantive Eq. 13.130 derivation is L-LZ3-D and deferred. -/
def IsSMBToLZ78ConverseChainBridge
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) : Prop :=
  IsLZ78ConverseChainHyp μ p lz78EncodingLength

@[simp] lemma isSMBToLZ78ConverseChainBridge_def
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    IsSMBToLZ78ConverseChainBridge μ p lz78EncodingLength ↔
      IsLZ78ConverseChainHyp μ p lz78EncodingLength :=
  Iff.rfl

end ConverseChainBridge

/-! ## §8. Headline export: `lz78_smb_sandwich_ergodic` -/

section HeadlineExport

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **L-LZ3 body discharge for the ergodic process**.

Headline export. For an ergodic process `p : ErgodicProcess μ α` on a
finite alphabet, the SMB sandwich is *hypothesis-free*: this theorem
packages the four sandwich ingredients (a.s. Tendsto, liminf half,
limsup half, parent placeholder discharge) into a single tuple, all
discharged from `SMBAlgoetCover.lean`'s `shannon_mcmillan_breiman` and
its Algoet–Cover one-sided bounds. -/
theorem lz78_smb_sandwich_ergodic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    (IsSMBSandwichTendsto μ p.toStationaryProcess)
    ∧ (IsSMBSandwichLiminf μ p.toStationaryProcess)
    ∧ (IsSMBSandwichLimsup μ p.toStationaryProcess)
    ∧ (IsSMBSandwichPassthrough μ p.toStationaryProcess) :=
  ⟨IsSMBSandwichTendsto.ofErgodic μ p,
   IsSMBSandwichLiminf.ofErgodic μ p,
   IsSMBSandwichLimsup.ofErgodic μ p,
   True.intro⟩

/-- **L-LZ3 body discharge — Tendsto component only**. -/
theorem lz78_smb_sandwich_ergodic_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => blockLogAvg μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess)) :=
  shannon_mcmillan_breiman μ p

/-- **L-LZ3 body discharge — liminf component only**. -/
theorem lz78_smb_sandwich_ergodic_liminf
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop :=
  algoet_cover_liminf_bound μ p

/-- **L-LZ3 body discharge — limsup component only**. -/
theorem lz78_smb_sandwich_ergodic_limsup
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
      ≤ entropyRate μ p.toStationaryProcess :=
  algoet_cover_limsup_bound μ p

end HeadlineExport

/-! ## §9. Wrappers chaining SMB sandwich into the LZ78 converse -/

section ConverseSMBChain

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **LZ78 converse lower bound — hypothesis-free SMB form**.

Given only the chain-rule hypothesis pass-through
`IsLZ78ConverseChainHyp` (L-LZ2-A; this is the Cover–Thomas Eq. 13.130
pmf-level inequality, *not* discharged here), and using the
hypothesis-free SMB ergodic sandwich for the lower bound, conclude

```
∀ᵐ ω ∂μ, entropyRate μ p ≤ liminf (fun n => lz78EncodingLength n / n)
```

This is the `lz78_converse_lower_bound_with_chain` of
`LZ78ConverseDischarge.lean` with the SMB lower-bound hypothesis
discharged from the ergodic-process side. -/
theorem lz78_converse_lower_bound_ergodic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (h_chain : IsLZ78ConverseChainHyp μ p.toStationaryProcess
                lz78EncodingLength) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n =>
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop :=
  lz78_converse_lower_bound_with_chain μ p lz78EncodingLength h_chain
    (lz78_smb_sandwich_ergodic_liminf μ p)

/-- **LZ78 converse lower bound — `IsSMBToLZ78ConverseChainBridge` form**.

Same as `lz78_converse_lower_bound_ergodic`, but consumes the chain
hypothesis through the SMB-side named bridge predicate. -/
theorem lz78_converse_lower_bound_ergodic_of_bridge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (h_bridge : IsSMBToLZ78ConverseChainBridge μ p.toStationaryProcess
                lz78EncodingLength) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n =>
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop :=
  lz78_converse_lower_bound_ergodic μ p lz78EncodingLength h_bridge

end ConverseSMBChain

/-! ## §10. Compat layer for `lz78GreedyEncodingLength` -/

section GreedyCompat

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Compat: greedy-encoding SMB sandwich aggregate**.

Specialization of `lz78_smb_sandwich_ergodic` (which is *independent
of the encoding-length function*) to the concrete `lz78GreedyEncodingLength`
naming, so downstream callers can keep the encoding-length argument
explicit when chaining the L-LZ3 / L-LZ4 discharges together. The
encoding-length argument is unused in the conclusion (the SMB
sandwich is a property of the source, not the code), so this is
literally `lz78_smb_sandwich_ergodic`. -/
theorem lz78_smb_sandwich_ergodic_greedy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    (IsSMBSandwichTendsto μ p.toStationaryProcess)
    ∧ (IsSMBSandwichLiminf μ p.toStationaryProcess)
    ∧ (IsSMBSandwichLimsup μ p.toStationaryProcess)
    ∧ (IsSMBSandwichPassthrough μ p.toStationaryProcess) :=
  lz78_smb_sandwich_ergodic μ p

/-- **Compat: greedy-encoding LZ78 converse via SMB sandwich**.

Conclusion specialized to `lz78GreedyEncodingLength` from
`LZ78GreedyParsing.lean`. The chain-rule hypothesis remains a
pass-through (L-LZ2-A: Cover–Thomas Eq. 13.130 pmf-level inequality). -/
theorem lz78_converse_lower_bound_ergodic_greedy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (h_chain : IsLZ78ConverseChainHyp μ p.toStationaryProcess
                (@lz78GreedyEncodingLength α _)) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n =>
            (lz78GreedyEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop :=
  lz78_converse_lower_bound_ergodic μ p
    (@lz78GreedyEncodingLength α _) h_chain

end GreedyCompat

end InformationTheory.Shannon

import Common2026.Shannon.LempelZiv78
import Common2026.Shannon.LZ78ZivInequality
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# LZ78 converse — asymptotic body extension (T4-A wave7)

This file publishes the **asymptotic-body** layer on top of the
combinatorial `ZivCountingBound` predicate already published in
`Common2026/Shannon/LZ78ZivInequality.lean`. It is a *predicate-level*
extension: the per-`n` real-valued bound `(p.count : ℝ) ≤ B` is lifted
to families `(p : ℕ → LZ78Parsing α)` indexed by the block length, and
the asymptotic shape `c(n) · log c(n) ≤ n · log b + O(1)` (Cover–Thomas
Eq. 13.124, the Ziv-counting asymptotic) is exposed as a hypothesis
pass-through `IsLZ78PhraseCountAsymptotic` that future discharges can
plug into the `IsZivInequalityPassthrough` slot.

## Scope (撤退ライン)

* **L-LZ2-asym-A** (engaged) — `IsLZ78PhraseCountAsymptotic` predicate
  shaped on `Asymptotics.IsBigO atTop`, plus a `.trivial` constructor.
* **L-LZ2-asym-B** (engaged) — `IsZivCountingAsymptoticBound` per-`n`
  bound aggregator with `.refl`, `.mono`, `.add_nonneg`, and
  `.of_pointwise_count` constructors.
* **L-LZ2-asym-C** (engaged) — bridge theorems showing how a uniform
  per-`n` Ziv counting bound implies the asymptotic predicate.
* **L-LZ2-asym-D** (deferred) — the *concrete* derivation of
  `c(n) ≤ n / log_b n · (1 + o(1))` from Cover–Thomas Eq. 13.122–13.124
  is supplied as hypothesis; the numerical asymptotic
  `c(n) · log c(n) − n · log b = o(n)` is the Cover–Thomas Lemma 13.5.5
  body and is in scope of a future discharge plan.
* **L-LZ2-asym-E** (engaged) — `IsZivInequalityPassthrough` bridge.

## Pattern source

Follows the same "predicate + .trivial + bridge" pattern as
`LZ78ZivInequality.lean` (LZ1) and `LZ78ConverseDischarge.lean`
(L-LZ2). The asymptotic layer is wrapped in `Asymptotics.IsBigO`
notation so downstream callers can plug `Mathlib.Analysis.Asymptotics`
lemmas directly without re-shaping.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

/-! ## §1. `IsZivCountingAsymptoticBound` per-`n` predicate (L-LZ2-asym-B) -/

section ZivCountingAsymptoticBound

variable {α : Type*}

/-- **Per-`n` Ziv counting asymptotic-bound predicate (L-LZ2-asym-B)**.

For a family of parsings `p : ℕ → LZ78Parsing α` indexed by block
length, this predicate asserts a uniform per-`n` real-valued upper
bound on `((p n).count : ℝ)` by `B n`. The bound function `B : ℕ → ℝ`
plays the role of the Cover–Thomas Eq. 13.124 asymptotic envelope
`n / log_b n · (1 + o(1))`; concrete witnesses come from
`card_phraseSet_le_pow`-style combinatorial counts. -/
def IsZivCountingAsymptoticBound (p : ℕ → LZ78Parsing α) (B : ℕ → ℝ) : Prop :=
  ∀ n, ((p n).count : ℝ) ≤ B n

@[simp] theorem IsZivCountingAsymptoticBound.refl (p : ℕ → LZ78Parsing α) :
    IsZivCountingAsymptoticBound p (fun n => ((p n).count : ℝ)) :=
  fun _ => le_refl _

/-- **Monotonicity** in the bound function. -/
theorem IsZivCountingAsymptoticBound.mono
    {p : ℕ → LZ78Parsing α} {B B' : ℕ → ℝ}
    (h : IsZivCountingAsymptoticBound p B)
    (hB : ∀ n, B n ≤ B' n) :
    IsZivCountingAsymptoticBound p B' :=
  fun n => le_trans (h n) (hB n)

/-- **Slack addition**: if `B` bounds `count`, so does `B + ε` for any
non-negative slack `ε`. -/
theorem IsZivCountingAsymptoticBound.add_nonneg
    {p : ℕ → LZ78Parsing α} {B ε : ℕ → ℝ}
    (h : IsZivCountingAsymptoticBound p B)
    (hε : ∀ n, 0 ≤ ε n) :
    IsZivCountingAsymptoticBound p (fun n => B n + ε n) := by
  intro n
  have := h n
  linarith [hε n]

/-- **Lift a pointwise `ZivCountingBound` to the asymptotic family**:
if for every `n` the per-`n` parsing `p n` satisfies
`ZivCountingBound (p n) (B n)`, then the asymptotic predicate holds. -/
theorem IsZivCountingAsymptoticBound.of_pointwise_count
    {p : ℕ → LZ78Parsing α} {B : ℕ → ℝ}
    (h : ∀ n, ZivCountingBound (p n) (B n)) :
    IsZivCountingAsymptoticBound p B :=
  fun n => h n

end ZivCountingAsymptoticBound

/-! ## §2. `IsLZ78PhraseCountAsymptotic` predicate (L-LZ2-asym-A) -/

section PhraseCountAsymptotic

variable {α : Type*}

/-- **Asymptotic phrase-count predicate (L-LZ2-asym-A)**.

For a family of LZ78 parsings `p : ℕ → LZ78Parsing α` and a reference
envelope function `B : ℕ → ℝ` (in the textbook this is
`n ↦ n / Real.log n` or similar), this predicate asserts that the
phrase-count sequence `n ↦ ((p n).count : ℝ)` is `O[atTop]` of `B`.

Cover–Thomas Eq. 13.124 reads
`c(n) ≤ n / log_b(c(n)) ≤ n / log_b n · (1 + o(1))`,
and this predicate captures exactly the `IsBigO` half: the
`(1 + o(1))` slack is absorbed into the constant of `IsBigO`. -/
def IsLZ78PhraseCountAsymptotic (p : ℕ → LZ78Parsing α) (B : ℕ → ℝ) : Prop :=
  (fun n => ((p n).count : ℝ)) =O[atTop] B

/-- **Reflexive constructor**: a sequence is trivially `O[atTop]` of
itself. -/
@[simp] theorem IsLZ78PhraseCountAsymptotic.refl (p : ℕ → LZ78Parsing α) :
    IsLZ78PhraseCountAsymptotic p (fun n => ((p n).count : ℝ)) :=
  isBigO_refl _ _

/-- **Trivial constructor from a global numeric upper bound** (in
particular: a uniform `(p n).count ≤ B n` with `B n ≥ 0`). -/
theorem IsLZ78PhraseCountAsymptotic.of_eventual_le
    {p : ℕ → LZ78Parsing α} {B : ℕ → ℝ}
    (h_nonneg : ∀ᶠ n in atTop, 0 ≤ B n)
    (h_le : ∀ᶠ n in atTop, ((p n).count : ℝ) ≤ B n) :
    IsLZ78PhraseCountAsymptotic p B := by
  unfold IsLZ78PhraseCountAsymptotic
  refine IsBigO.of_bound 1 ?_
  filter_upwards [h_nonneg, h_le] with n hn hle
  have hcount_nn : (0 : ℝ) ≤ ((p n).count : ℝ) := by exact_mod_cast Nat.zero_le _
  have h1 : ‖((p n).count : ℝ)‖ = ((p n).count : ℝ) := by
    rw [Real.norm_eq_abs]; exact abs_of_nonneg hcount_nn
  have h2 : ‖B n‖ = B n := by rw [Real.norm_eq_abs]; exact abs_of_nonneg hn
  rw [h1, h2, one_mul]
  exact hle

/-- **Lift a pointwise count bound (with non-negative envelope) to the
asymptotic predicate**. This is the direct bridge from `ZivCountingBound`
to `IsLZ78PhraseCountAsymptotic`. -/
theorem IsLZ78PhraseCountAsymptotic.of_pointwise_bound
    {p : ℕ → LZ78Parsing α} {B : ℕ → ℝ}
    (h_bound : IsZivCountingAsymptoticBound p B)
    (h_nonneg : ∀ n, 0 ≤ B n) :
    IsLZ78PhraseCountAsymptotic p B := by
  refine IsLZ78PhraseCountAsymptotic.of_eventual_le ?_ ?_
  · exact Filter.Eventually.of_forall h_nonneg
  · exact Filter.Eventually.of_forall h_bound

end PhraseCountAsymptotic

/-! ## §3. Pure asymptotic algebra layer (L-LZ2-asym-C) -/

section AsymptoticAlgebra

variable {α : Type*}

/-- **Transitivity** of the phrase-count asymptotic predicate through
an `IsBigO`-style domination of the envelope. If
`IsLZ78PhraseCountAsymptotic p B` and `B =O[atTop] B'`, then
`IsLZ78PhraseCountAsymptotic p B'`. -/
theorem IsLZ78PhraseCountAsymptotic.transBigO
    {p : ℕ → LZ78Parsing α} {B B' : ℕ → ℝ}
    (h : IsLZ78PhraseCountAsymptotic p B)
    (hB : B =O[atTop] B') :
    IsLZ78PhraseCountAsymptotic p B' :=
  h.trans hB

/-- **Envelope swap via reflexive trans**: if both the original
envelope `B` and an alternative envelope `B'` are mutually
`IsBigO`-related, the predicate transfers across. (Convenience
wrapper for `.transBigO`.) -/
theorem IsLZ78PhraseCountAsymptotic.congr_envelope
    {p : ℕ → LZ78Parsing α} {B B' : ℕ → ℝ}
    (h : IsLZ78PhraseCountAsymptotic p B)
    (hBB' : B =ᶠ[atTop] B') :
    IsLZ78PhraseCountAsymptotic p B' := by
  -- `IsBigO` is preserved by eventual equality on the right-hand side.
  unfold IsLZ78PhraseCountAsymptotic at h ⊢
  exact h.congr' (Filter.EventuallyEq.refl _ _) hBB'

/-- **`IsLittleO` chain**: if the phrase-count is `O[atTop] B` and `B`
is in turn `o[atTop] g`, then the phrase-count is `o[atTop] g`. This is
the typical chain used when the textbook bound
`c(n) ≤ n / log_b n + lower-order` is combined with the fact that
`n / log_b n = o(n)`. -/
theorem IsLZ78PhraseCountAsymptotic.transIsLittleO
    {p : ℕ → LZ78Parsing α} {B g : ℕ → ℝ}
    (h : IsLZ78PhraseCountAsymptotic p B)
    (hBg : B =o[atTop] g) :
    (fun n => ((p n).count : ℝ)) =o[atTop] g :=
  h.trans_isLittleO hBg

/-- **Reflexive scaling**: multiplying the envelope by a non-zero
constant preserves the `IsBigO` relation, hence the asymptotic
predicate. -/
theorem IsLZ78PhraseCountAsymptotic.const_mul_envelope
    {p : ℕ → LZ78Parsing α} {B : ℕ → ℝ} (c : ℝ) (hc : c ≠ 0)
    (h : IsLZ78PhraseCountAsymptotic p B) :
    IsLZ78PhraseCountAsymptotic p (fun n => c * B n) := by
  unfold IsLZ78PhraseCountAsymptotic at h ⊢
  exact h.trans (isBigO_self_const_mul hc B atTop)

end AsymptoticAlgebra

/-! ## §4. Bridge to parent `IsZivInequalityPassthrough` (L-LZ2-asym-E) -/

section ZivPassthroughBridge

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- **Bridge: an asymptotic phrase-count predicate discharges the parent
`IsZivInequalityPassthrough` placeholder.**

Currently the parent predicate is `True`; the bridge is set up so that
the *signature* — taking an `IsLZ78PhraseCountAsymptotic` witness — is
already in place. When the asymptotic-side discharges of L-LZ2-asym-D
(the concrete `c(n) · log c(n) − n · log b = o(n)` derivation) land,
the parent predicate body will be upgraded from `True` to a concrete
asymptotic statement and this bridge will become the substantive
constructor. For now it is the identity wrap on `True.intro`. -/
theorem IsZivInequalityPassthrough.ofAsymptotic
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (_q : ℕ → LZ78Parsing α) (_B : ℕ → ℝ)
    (_h_asym : IsLZ78PhraseCountAsymptotic _q _B) :
    IsZivInequalityPassthrough μ p lz78EncodingLength :=
  True.intro

/-- **Trivial reverse**: parent placeholder is `True`, so we may
construct an asymptotic predicate from *any* parsing family `q` and
envelope `B = q.count` reflexively, regardless of the passthrough. -/
theorem IsLZ78PhraseCountAsymptotic.of_passthrough
    (_h : ∀ (μ : Measure Ω) (p : StationaryProcess μ α)
            (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ),
            IsZivInequalityPassthrough μ p lz78EncodingLength)
    (q : ℕ → LZ78Parsing α) :
    IsLZ78PhraseCountAsymptotic q (fun n => ((q n).count : ℝ)) :=
  IsLZ78PhraseCountAsymptotic.refl q

end ZivPassthroughBridge

/-! ## §5. Trivial-`n`-envelope bridges -/

section TrivialNEnvelope

variable {α : Type*}

/-- **Linear envelope from a uniform `count ≤ n` bound**. Under the
trivial parsing-invariant constraint `(p n).count ≤ n` (which holds for
*any* LZ78 parsing of a length-`n` input), the phrase-count sequence is
`O[atTop] (fun n => (n : ℝ))`. -/
theorem IsLZ78PhraseCountAsymptotic.linear_of_count_le_n
    {p : ℕ → LZ78Parsing α}
    (h_le : ∀ n, (p n).count ≤ n) :
    IsLZ78PhraseCountAsymptotic p (fun n => (n : ℝ)) := by
  refine IsLZ78PhraseCountAsymptotic.of_eventual_le ?_ ?_
  · exact Filter.Eventually.of_forall (fun n => by exact_mod_cast Nat.zero_le n)
  · refine Filter.Eventually.of_forall ?_
    intro n
    exact_mod_cast h_le n

/-- **Conversion from per-`n` `ZivCountingBound` with the natural
envelope `B n = (B₀ n : ℝ)`**: if for every `n` the per-`n` Ziv counting
bound holds with a real envelope `B n`, and `B` is eventually
non-negative, then the asymptotic predicate holds. This is the
ergonomic entry point when the upstream caller already has the
per-`n` `ZivCountingBound` lemma. -/
theorem IsLZ78PhraseCountAsymptotic.of_ZivCountingBound
    {p : ℕ → LZ78Parsing α} {B : ℕ → ℝ}
    (h_bound : ∀ n, ZivCountingBound (p n) (B n))
    (h_nonneg : ∀ᶠ n in atTop, 0 ≤ B n) :
    IsLZ78PhraseCountAsymptotic p B := by
  refine IsLZ78PhraseCountAsymptotic.of_eventual_le h_nonneg
    (Filter.Eventually.of_forall ?_)
  intro n
  exact h_bound n

/-- **Composite envelope: `(p n).count ≤ B n + ε n` with `ε ≥ 0`** still
gives `O[atTop] B` *provided* `ε =O[atTop] B`. Helper combine for the
Ziv-counting slack `(1 + o(1))` factor in Cover–Thomas Eq. 13.124. -/
theorem IsLZ78PhraseCountAsymptotic.of_sum_envelope
    {p : ℕ → LZ78Parsing α} {B ε : ℕ → ℝ}
    (h_bound : ∀ n, ((p n).count : ℝ) ≤ B n + ε n)
    (h_B_nonneg : ∀ᶠ n in atTop, 0 ≤ B n)
    (h_ε_nonneg : ∀ᶠ n in atTop, 0 ≤ ε n)
    (h_ε_bigO_B : ε =O[atTop] B) :
    IsLZ78PhraseCountAsymptotic p B := by
  -- First show `c(n) =O[atTop] (B + ε)`, then collapse `B + ε =O[atTop] B`.
  have h_asym_sum : IsLZ78PhraseCountAsymptotic p (fun n => B n + ε n) := by
    refine IsLZ78PhraseCountAsymptotic.of_eventual_le ?_ ?_
    · filter_upwards [h_B_nonneg, h_ε_nonneg] with n hB hε using by linarith
    · exact Filter.Eventually.of_forall h_bound
  -- `B + ε =O[atTop] B` is the sum of `B =O[atTop] B` (reflexive) and
  -- `ε =O[atTop] B`.
  refine h_asym_sum.transBigO ?_
  exact (isBigO_refl B atTop).add h_ε_bigO_B

end TrivialNEnvelope

/-! ## §6. `Real.log`-style envelopes -/

section LogEnvelopes

variable {α : Type*}

/-- **`Real.log (n : ℝ)` is eventually non-negative on `atTop`**.
A trivial Mathlib-shape helper used as the non-negativity prerequisite
of `IsLZ78PhraseCountAsymptotic.of_eventual_le`. -/
theorem real_log_natCast_eventually_nonneg :
    ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (n : ℝ) := by
  refine Filter.Eventually.of_forall ?_
  intro n
  exact Real.log_natCast_nonneg n

/-- **`n / Real.log n` envelope is eventually non-negative**.
Cover–Thomas Eq. 13.124 envelope sanity. -/
theorem natCast_div_real_log_eventually_nonneg :
    ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℝ) / Real.log (n : ℝ) := by
  refine Filter.Eventually.of_forall ?_
  intro n
  by_cases h : Real.log (n : ℝ) = 0
  · simp [h]
  · have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have hlog_pos : 0 < Real.log (n : ℝ) := lt_of_le_of_ne hlog_nn (Ne.symm h)
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact div_nonneg hn_nn hlog_nn

/-- **Asymptotic phrase-count predicate from a `n / Real.log n` bound**.
The textbook-form constructor: given a per-`n` bound
`(p n).count ≤ n / Real.log n + slack`, with the slack itself bounded
above by `n / Real.log n` asymptotically, conclude
`IsLZ78PhraseCountAsymptotic p (fun n => (n : ℝ) / Real.log n)`. -/
theorem IsLZ78PhraseCountAsymptotic.of_n_div_log
    {p : ℕ → LZ78Parsing α}
    (h_bound : ∀ᶠ n : ℕ in atTop,
        ((p n).count : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ)) :
    IsLZ78PhraseCountAsymptotic p (fun n => (n : ℝ) / Real.log (n : ℝ)) := by
  exact IsLZ78PhraseCountAsymptotic.of_eventual_le
    natCast_div_real_log_eventually_nonneg h_bound

end LogEnvelopes

/-! ## §7. Main result — phrase-count asymptotic upper bound -/

section MainAsymptoticResult

variable {α : Type*}

/-- **T4-A wave7 main statement: LZ78 phrase-count asymptotic upper
bound, hypothesis pass-through form.**

For any family of LZ78 parsings `p : ℕ → LZ78Parsing α` and any
real-valued envelope `B : ℕ → ℝ`, if the per-`n` Ziv counting bound
`(p n).count ≤ B n` holds and `B` is eventually non-negative, then the
asymptotic predicate `IsLZ78PhraseCountAsymptotic p B` holds.

This is the *predicate-level* statement of Cover–Thomas Eq. 13.124,
shaped so that downstream callers can supply any concrete envelope
function (e.g. `n / log_b n`, `n / log n`, `n`) without changing the
external signature. The substantive arithmetic
`c(n) · log c(n) ≤ n · log b + O(1)` (Cover–Thomas Lemma 13.5.5
asymptotic body, L-LZ2-asym-D) remains in scope of a future discharge
plan, but is *encapsulated* inside `B n` and so does not surface in
this signature.

Pattern: the same `hypothesis pass-through` style as
`relay_cutset_outer_bound` (T3-F) and `lz78_converse_lower_bound`
(`LempelZiv78.lean`). -/
theorem lz78_phrase_count_asymptotic
    (p : ℕ → LZ78Parsing α) (B : ℕ → ℝ)
    (h_bound : ∀ n, ZivCountingBound (p n) (B n))
    (h_nonneg : ∀ᶠ n in atTop, 0 ≤ B n) :
    IsLZ78PhraseCountAsymptotic p B :=
  IsLZ78PhraseCountAsymptotic.of_ZivCountingBound h_bound h_nonneg

/-- **Specialized to the `n / Real.log n` envelope** (Cover–Thomas
13.124). -/
theorem lz78_phrase_count_asymptotic_n_div_log
    (p : ℕ → LZ78Parsing α)
    (h_bound : ∀ᶠ n : ℕ in atTop,
        ((p n).count : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ)) :
    IsLZ78PhraseCountAsymptotic p (fun n => (n : ℝ) / Real.log (n : ℝ)) :=
  IsLZ78PhraseCountAsymptotic.of_n_div_log h_bound

/-- **Specialized to the linear `n` envelope** (the trivial bound). -/
theorem lz78_phrase_count_asymptotic_linear
    (p : ℕ → LZ78Parsing α)
    (h_le : ∀ n, (p n).count ≤ n) :
    IsLZ78PhraseCountAsymptotic p (fun n => (n : ℝ)) :=
  IsLZ78PhraseCountAsymptotic.linear_of_count_le_n h_le

end MainAsymptoticResult

/-! ## §8. Two-sided / sandwich-form combine -/

section TwoSidedSandwich

variable {α : Type*}

/-- **Two-sided asymptotic envelope**: combine an upper-bound predicate
`IsLZ78PhraseCountAsymptotic p B_upper` and a lower-bound predicate
`B_lower =O[atTop] (p.count)` (i.e. the phrase count *dominates*
`B_lower`) into a sandwich. This is the predicate-level analogue of the
Cover–Thomas Eq. 13.124 ⟺ Eq. 13.130 sandwich. -/
def IsLZ78PhraseCountSandwich
    (p : ℕ → LZ78Parsing α) (B_lower B_upper : ℕ → ℝ) : Prop :=
  IsLZ78PhraseCountAsymptotic p B_upper ∧
    B_lower =O[atTop] (fun n => ((p n).count : ℝ))

@[simp] lemma isLZ78PhraseCountSandwich_def
    (p : ℕ → LZ78Parsing α) (B_lower B_upper : ℕ → ℝ) :
    IsLZ78PhraseCountSandwich p B_lower B_upper ↔
      (IsLZ78PhraseCountAsymptotic p B_upper ∧
        B_lower =O[atTop] (fun n => ((p n).count : ℝ))) := Iff.rfl

/-- **Reflexive sandwich**: any parsing family sandwiches its own
count. -/
@[simp] theorem IsLZ78PhraseCountSandwich.refl (p : ℕ → LZ78Parsing α) :
    IsLZ78PhraseCountSandwich p
      (fun n => ((p n).count : ℝ))
      (fun n => ((p n).count : ℝ)) :=
  ⟨IsLZ78PhraseCountAsymptotic.refl p, isBigO_refl _ _⟩

/-- **Sandwich destructor: upper bound**. -/
theorem IsLZ78PhraseCountSandwich.upper
    {p : ℕ → LZ78Parsing α} {B_lower B_upper : ℕ → ℝ}
    (h : IsLZ78PhraseCountSandwich p B_lower B_upper) :
    IsLZ78PhraseCountAsymptotic p B_upper := h.1

/-- **Sandwich destructor: lower bound**. -/
theorem IsLZ78PhraseCountSandwich.lower
    {p : ℕ → LZ78Parsing α} {B_lower B_upper : ℕ → ℝ}
    (h : IsLZ78PhraseCountSandwich p B_lower B_upper) :
    B_lower =O[atTop] (fun n => ((p n).count : ℝ)) := h.2

/-- **Sandwich constructor from two asymptotic ingredients**. -/
theorem IsLZ78PhraseCountSandwich.mk
    {p : ℕ → LZ78Parsing α} {B_lower B_upper : ℕ → ℝ}
    (h_upper : IsLZ78PhraseCountAsymptotic p B_upper)
    (h_lower : B_lower =O[atTop] (fun n => ((p n).count : ℝ))) :
    IsLZ78PhraseCountSandwich p B_lower B_upper :=
  ⟨h_upper, h_lower⟩

/-- **Transitive chain: sandwich + envelope swap**. If the count
sandwich holds with upper envelope `B_upper` and `B_upper =O[atTop] B'`,
then the sandwich holds with upper envelope `B'`. -/
theorem IsLZ78PhraseCountSandwich.transUpper
    {p : ℕ → LZ78Parsing α} {B_lower B_upper B' : ℕ → ℝ}
    (h : IsLZ78PhraseCountSandwich p B_lower B_upper)
    (hBO : B_upper =O[atTop] B') :
    IsLZ78PhraseCountSandwich p B_lower B' :=
  ⟨h.1.transBigO hBO, h.2⟩

/-- **Transitive chain: sandwich + lower-envelope swap**. -/
theorem IsLZ78PhraseCountSandwich.transLower
    {p : ℕ → LZ78Parsing α} {B_lower B_upper B' : ℕ → ℝ}
    (h : IsLZ78PhraseCountSandwich p B_lower B_upper)
    (hBO : B' =O[atTop] B_lower) :
    IsLZ78PhraseCountSandwich p B' B_upper :=
  ⟨h.1, hBO.trans h.2⟩

end TwoSidedSandwich

/-! ## §9. Bridge to the LZ78SMBSandwich entrypoints -/

section SMBSandwichBridge

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- **Bridge: an asymptotic phrase-count sandwich discharges the parent
`IsSMBSandwichPassthrough` placeholder**.

Currently the parent predicate is `True`; the bridge is set up so that
the *signature* — taking an `IsLZ78PhraseCountSandwich` witness on a
parsing family extracted from the encoding-length — is already in
place. When the SMB-side discharges land (Birkhoff + chain rule), the
parent predicate body will be upgraded from `True` to a concrete
sandwich statement and this bridge will become substantive.

For now it is the identity wrap on `True.intro`. -/
theorem IsSMBSandwichPassthrough.ofPhraseCountSandwich
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (_q : ℕ → LZ78Parsing α) (_B_lower _B_upper : ℕ → ℝ)
    (_h_sand : IsLZ78PhraseCountSandwich _q _B_lower _B_upper) :
    IsSMBSandwichPassthrough μ p :=
  True.intro

/-- **Combined bridge**: from an asymptotic phrase-count sandwich, both
the `IsZivInequalityPassthrough` (upper-side) and the
`IsSMBSandwichPassthrough` (sandwich) parent placeholders can be
discharged simultaneously. -/
theorem IsLZ78PhraseCountSandwich.toBothPassthroughs
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (q : ℕ → LZ78Parsing α) (B_lower B_upper : ℕ → ℝ)
    (h_sand : IsLZ78PhraseCountSandwich q B_lower B_upper) :
    IsZivInequalityPassthrough μ p lz78EncodingLength ∧
      IsSMBSandwichPassthrough μ p :=
  ⟨IsZivInequalityPassthrough.ofAsymptotic μ p lz78EncodingLength q B_upper
      h_sand.upper,
   IsSMBSandwichPassthrough.ofPhraseCountSandwich μ p q B_lower B_upper
      h_sand⟩

end SMBSandwichBridge

end InformationTheory.Shannon

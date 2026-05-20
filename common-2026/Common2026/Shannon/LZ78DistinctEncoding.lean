import Common2026.Shannon.LempelZiv78
import Common2026.Shannon.LZ78GreedyParsing
import Common2026.Shannon.LZ78GreedyParsingImpl
import Common2026.Shannon.LZ78GreedyLongestPrefix
import Common2026.Shannon.LZ78ZivCountingBody
import Common2026.Shannon.LZ78FinalGlue
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Order.Filter.IsBounded

/-!
# LZ78 distinct-count encoding length — Phase C/D structural bridge (T4-A)

Phase A (`LZ78GreedyLongestPrefix.lean`) published the genuine
longest-prefix greedy parse `lz78PhraseStrings` with its **distinct
invariant** (`lz78PhraseStrings_nodup`) and **count bound**
(`lz78PhraseStrings_count_le : c(n) ≤ n`). Phase B
(`LZ78ZivCountingBody.lean`) supplied the genuine Cover–Thomas counting
envelope `c(n) = O(n / log n)` (`lz78PhraseStrings_count_isBigO`).

These genuine ingredients live on the *phrase-string* side; the headline
`lz78_two_sided_optimality_greedy_impl_bdd_below_free`
(`LZ78FinalGlue.lean`) is, however, stated about
`lz78GreedyImplEncodingLength`, whose underlying parse
(`lz78GreedyParse`) is the worst-case **one-symbol** form (`count = n`),
for which the per-symbol bit-rate diverges and `h_bdd_above` is *not*
dischargeable.

This file closes the gap by the **structural transformation** noted at
the end of Phase B: build an encoding-length function whose count is the
genuine *distinct* phrase count, so the existing per-phrase bit-length
plumbing (`LZ78Phrase.bitLength`, `LZ78Parsing.encodingLength`) applies
and the Phase B `O(n / log n)` envelope discharges `h_bdd_above`.

## Approach (overall strategy / shape)

* **§1 — structural transformation.** From `lz78PhraseStrings input`
  build `lz78DistinctParsing input : LZ78Parsing α`, a parsing whose
  phrase list is the all-root form of the distinct strings, so its
  `.count` equals `(lz78PhraseStrings input).length` *by construction*
  (the back-pointer `inRange` invariant is vacuous on root phrases).
  Define `lz78DistinctEncodingLength n x` via `LZ78Parsing.encodingLength`
  on this parsing, reusing the same `c · bitLength c |α|` formula as the
  one-symbol code — but now with the genuine distinct `c`.

* **§2 — bit-length bound.** `lz78DistinctEncodingLength n x =
  c(n) · bitLength c(n) |α| ≤ c(n) · (Nat.log 2 (n+1) + Nat.log 2 |α| + 2)`,
  using the Phase A bound `c(n) ≤ n` and `bitLength` monotonicity.

* **§3 — `h_bdd_above` discharge (Phase C).** From the Phase B envelope
  `c(n) =O (n / log n)` and the §2 bound, the per-symbol rate
  `lz78DistinctEncodingLength n (block) / n` is `=O 1`, hence
  `IsBoundedUnder (· ≤ ·)`. This is the genuine boundedness the headline
  needs, supplied internally rather than as a hypothesis.

* **§4 — headline.** A two-sided optimality headline parameterized on
  `lz78DistinctEncodingLength` with `h_bdd_above` *removed* (discharged
  by §3); only the two Cover–Thomas chain hypotheses remain.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

/-! ## §1. Structural transformation: distinct parse → `LZ78Parsing` -/

section Structural

variable {α : Type*} [DecidableEq α]

/-- **Root-phrase list of the distinct phrase strings**: map each distinct
phrase string to a root phrase carrying its first symbol (or, for the
empty string, an arbitrary symbol — but the distinct strings are all
non-empty by `lz78PhraseStrings_forall_ne_nil`, so this branch never
fires for the count we care about). The point of this list is purely its
**length**, which equals the distinct phrase count. -/
noncomputable def lz78DistinctRootPhrases [Nonempty α] (input : List α) :
    List (LZ78Phrase α) :=
  (lz78PhraseStrings input).map
    (fun w => { parent := none, symbol := w.headD (Classical.arbitrary α) })

@[simp] lemma lz78DistinctRootPhrases_length [Nonempty α] (input : List α) :
    (lz78DistinctRootPhrases input).length = (lz78PhraseStrings input).length := by
  unfold lz78DistinctRootPhrases
  rw [List.length_map]

/-- **Structural transformation `lz78PhraseStrings → LZ78Parsing`**: the
distinct phrase strings packaged as a valid `LZ78Parsing` of all-root
phrases. The back-pointer `inRange` invariant is vacuous (every phrase
has `parent = none`), and the phrase count equals the genuine distinct
phrase count. -/
noncomputable def lz78DistinctParsing [Nonempty α] (input : List α) : LZ78Parsing α :=
  { phrases := lz78DistinctRootPhrases input
    inRange := by
      intro i hi k hk
      exfalso
      have hparent : ((lz78DistinctRootPhrases input).get ⟨i, hi⟩).parent = none := by
        unfold lz78DistinctRootPhrases
        rw [List.get_eq_getElem, List.getElem_map]
      rw [hparent] at hk
      cases hk }

/-- **Count = genuine distinct phrase count** (the heart of the structural
transformation): `lz78DistinctParsing` has exactly
`(lz78PhraseStrings input).length` phrases. -/
@[simp] theorem lz78DistinctParsing_count [Nonempty α] (input : List α) :
    (lz78DistinctParsing input).count = (lz78PhraseStrings input).length := by
  unfold lz78DistinctParsing LZ78Parsing.count
  exact lz78DistinctRootPhrases_length input

end Structural

/-! ## §2. Distinct encoding length + bit-length bound -/

section EncodingLength

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- **Distinct-count LZ78 encoding length**: the total bit length of the
distinct parsing (`c · bitLength c |α|`), now with the genuine distinct
phrase count `c = (lz78PhraseStrings (List.ofFn x)).length`. Plugs into
the parent `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` parameter slot. -/
noncomputable def lz78DistinctEncodingLength (n : ℕ) (x : Fin n → α) : ℕ :=
  (lz78DistinctParsing (List.ofFn x)).encodingLength (Fintype.card α)

/-- **The distinct encoding length on `n`-tuples equals
`c(n) · bitLength c(n) |α|`** with the genuine distinct count `c(n)`. -/
theorem lz78DistinctEncodingLength_eq (n : ℕ) (x : Fin n → α) :
    lz78DistinctEncodingLength n x
      = (lz78PhraseStrings (List.ofFn x)).length
          * LZ78Phrase.bitLength (lz78PhraseStrings (List.ofFn x)).length
              (Fintype.card α) := by
  unfold lz78DistinctEncodingLength LZ78Parsing.encodingLength
  rw [lz78DistinctParsing_count]

/-- **Distinct phrase count of an `n`-tuple is `≤ n`** (Phase A
`lz78PhraseStrings_count_le` instantiated at `List.ofFn x`). -/
theorem lz78Distinct_count_ofFn_le (n : ℕ) (x : Fin n → α) :
    (lz78PhraseStrings (List.ofFn x)).length ≤ n := by
  have h := lz78PhraseStrings_count_le (List.ofFn x)
  rwa [List.length_ofFn] at h

/-- **Cover–Thomas Lemma 13.5.2 bit-length bound for the distinct code**:
`lz78DistinctEncodingLength n x ≤ c(n) · (Nat.log 2 (n+1) + Nat.log 2 |α| + 2)`,
using `c(n) ≤ n` for the per-phrase dictionary-size cost. -/
theorem lz78DistinctEncodingLength_le (n : ℕ) (x : Fin n → α) :
    lz78DistinctEncodingLength n x
      ≤ (lz78PhraseStrings (List.ofFn x)).length
          * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2) := by
  rw [lz78DistinctEncodingLength_eq]
  apply Nat.mul_le_mul_left
  rw [LZ78Phrase.bitLength_eq]
  have hc := lz78Distinct_count_ofFn_le n x
  have : Nat.log 2 ((lz78PhraseStrings (List.ofFn x)).length + 1)
      ≤ Nat.log 2 (n + 1) := Nat.log_mono_right (by omega)
  omega

/-- **Per-symbol nonnegativity** of the distinct rate (for the lower
boundedness side, mirroring the greedy-impl form). -/
theorem lz78DistinctEncodingLength_per_symbol_nonneg (n : ℕ) (x : Fin n → α) :
    (0 : ℝ) ≤ (lz78DistinctEncodingLength n x : ℝ) / (n : ℝ) :=
  div_nonneg (by positivity) (by positivity)

end EncodingLength

/-! ## §3. `h_bdd_above` discharge (Phase C) -/

section BoundedAbove

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- **Real-valued per-symbol upper bound**: `(lz78DistinctEncodingLength n x)/n
≤ (c(n)/n)·(log₂(n+1) + log₂|α| + 2)` on `ℝ` (for `n ≥ 1`). The factor
`c(n)/n` is what the Phase B `O(n/log n)` envelope shrinks. -/
theorem lz78DistinctEncodingLength_real_per_symbol_le (n : ℕ) (hn : 0 < n)
    (x : Fin n → α) :
    (lz78DistinctEncodingLength n x : ℝ) / (n : ℝ)
      ≤ ((lz78PhraseStrings (List.ofFn x)).length : ℝ) / (n : ℝ)
          * ((Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2) := by
  set c := (lz78PhraseStrings (List.ofFn x)).length with hc
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hle := lz78DistinctEncodingLength_le n x
  have hleR : (lz78DistinctEncodingLength n x : ℝ)
      ≤ (c : ℝ) * ((Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2) := by
    rw [hc]
    have : (lz78DistinctEncodingLength n x : ℝ)
        ≤ ((c * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2) : ℕ) : ℝ) := by
      rw [hc]; exact_mod_cast hle
    refine this.trans (le_of_eq ?_)
    push_cast; ring
  rw [div_le_iff₀ hn']
  calc (lz78DistinctEncodingLength n x : ℝ)
      ≤ (c : ℝ) * ((Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2) := hleR
    _ = (c : ℝ) / (n : ℝ)
          * ((Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2) * (n : ℝ) := by
        field_simp

/-- **`Nat.log 2 (n+1) =O Real.log n`** (atTop): the per-phrase dictionary
cost grows only logarithmically. -/
theorem natLog_succ_isBigO_log :
    (fun n : ℕ => (Nat.log 2 (n + 1) : ℝ)) =O[atTop] (fun n => Real.log (n : ℝ)) := by
  refine IsBigO.of_bound (2 / Real.log 2) ?_
  have hev : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  filter_upwards [hev] with n hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn_pos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- `Nat.log 2 (n+1) ≤ Real.logb 2 (n+1) = Real.log (n+1) / Real.log 2`
  have hnat : (Nat.log 2 (n + 1) : ℝ) ≤ Real.logb 2 ((n + 1 : ℕ) : ℝ) := by
    have := Real.natLog_le_logb (n + 1) 2
    push_cast at this ⊢
    convert this using 2
  -- `Real.log (n+1) ≤ 2 * Real.log n` since `n + 1 ≤ n^2` for `n ≥ 2`.
  have hsucc : Real.log ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hle : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (n + 1 : ℕ) ≤ n ^ 2 := by nlinarith [hn]
      calc ((n + 1 : ℕ) : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
        _ = (n : ℝ) ^ 2 := by push_cast; ring
    calc Real.log ((n + 1 : ℕ) : ℝ)
        ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by positivity) hle
      _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; push_cast; ring
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg hlogn_pos.le]
  calc (Nat.log 2 (n + 1) : ℝ)
      ≤ Real.logb 2 ((n + 1 : ℕ) : ℝ) := hnat
    _ = Real.log ((n + 1 : ℕ) : ℝ) / Real.log 2 := by rw [Real.logb]
    _ ≤ (2 * Real.log (n : ℝ)) / Real.log 2 := by
        gcongr
    _ = 2 / Real.log 2 * Real.log (n : ℝ) := by ring

/-- **Per-phrase bit cost `=O log n`**: `Nat.log 2 (n+1) + log₂|α| + 2 =O log n`. -/
theorem bitCost_isBigO_log :
    (fun n : ℕ => (Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2)
      =O[atTop] (fun n => Real.log (n : ℝ)) := by
  -- the constant tail `log₂|α| + 2` is `=O log n` (log → atTop, ≥ 1 eventually);
  -- add to the `natLog` envelope.
  have hconst : (fun _ : ℕ => (Nat.log 2 (Fintype.card α) : ℝ) + 2)
      =O[atTop] (fun n => Real.log (n : ℝ)) := by
    refine IsBigO.of_bound ((Nat.log 2 (Fintype.card α) : ℝ) + 2) ?_
    -- once `Real.log n ≥ 1` (i.e. `n ≥ 3`), the constant `k ≤ k · log n`.
    have hev : ∀ᶠ n : ℕ in atTop, 3 ≤ n :=
      Filter.eventually_atTop.2 ⟨3, fun _ hn => hn⟩
    filter_upwards [hev] with n hn
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h13 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    have hlogn_ge : (1 : ℝ) ≤ Real.log (n : ℝ) := by
      have : Real.log 3 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn3
      linarith
    have hknn : (0 : ℝ) ≤ (Nat.log 2 (Fintype.card α) : ℝ) + 2 := by positivity
    rw [Real.norm_of_nonneg hknn, Real.norm_of_nonneg (by linarith)]
    calc (Nat.log 2 (Fintype.card α) : ℝ) + 2
        = ((Nat.log 2 (Fintype.card α) : ℝ) + 2) * 1 := by ring
      _ ≤ ((Nat.log 2 (Fintype.card α) : ℝ) + 2) * Real.log (n : ℝ) := by
          apply mul_le_mul_of_nonneg_left hlogn_ge hknn
  have hsum := (natLog_succ_isBigO_log.add hconst)
  -- reshape `(natLog (n+1) + (log|α| + 2))` to `(natLog (n+1) + log|α| + 2)`
  refine hsum.congr_left ?_
  intro n; ring

/-- **Per-symbol distinct rate is `=O 1`** for a fixed sample point `x : ℕ → α`
with `(input n).length = n`: combining the Phase B envelope `c(n) =O (n/log n)`
with the §3 per-phrase `=O log n` bound, the rate is bounded. -/
theorem lz78DistinctEncodingLength_rate_isBigO_one
    (input : ℕ → List α) (hlen : ∀ n, (input n).length = n) :
    (fun n => ((lz78PhraseStrings (input n)).length : ℝ) / (n : ℝ)
        * ((Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2))
      =O[atTop] (fun _ => (1 : ℝ)) := by
  -- Extract explicit constants from the two `=O` ingredients.
  obtain ⟨C₁, hC₁⟩ := (lz78PhraseStrings_count_isBigO input hlen).bound
  obtain ⟨C₂, hC₂⟩ := (bitCost_isBigO_log (α := α)).bound
  refine IsBigO.of_bound (max C₁ 0 * (max C₂ 0)) ?_
  -- work where `n ≥ 2` (so `n > 0`, `log n > 0`).
  have hev : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  filter_upwards [hC₁, hC₂, hev] with n h1 h2 hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn_pos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by linarith)
  -- The two `c(n)` and `bitcost` factors are nonnegative.
  set c : ℝ := ((lz78PhraseStrings (input n)).length : ℝ) with hc
  set B : ℝ := (Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2 with hB
  have hc_nn : (0 : ℝ) ≤ c := by positivity
  have hB_nn : (0 : ℝ) ≤ B := by positivity
  -- Re-read the two bounds with the norms collapsed.
  have hndiv_nn : (0 : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) :=
    div_nonneg hnpos.le hlogn_pos.le
  rw [Real.norm_of_nonneg hc_nn, Real.norm_of_nonneg hndiv_nn] at h1
  rw [Real.norm_of_nonneg hB_nn, Real.norm_of_nonneg hlogn_pos.le] at h2
  -- `c ≤ (max C₁ 0)·(n/log n)`, `B ≤ (max C₂ 0)·log n`.
  have h1' : c ≤ (max C₁ 0) * ((n : ℝ) / Real.log (n : ℝ)) :=
    h1.trans (by gcongr; exact le_max_left _ _)
  have h2' : B ≤ (max C₂ 0) * Real.log (n : ℝ) :=
    h2.trans (by gcongr; exact le_max_left _ _)
  have hM1 : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
  have hM2 : (0 : ℝ) ≤ max C₂ 0 := le_max_right _ _
  -- Bound the product `(c / n) * B`.
  rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (1:ℝ)), mul_one,
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ c / (n:ℝ) * B)]
  -- `(c/n)*B = (c*B)/n ≤ ((M₁·n/log n)·(M₂·log n))/n = M₁·M₂`.
  have hcB : c * B ≤ (max C₁ 0) * (max C₂ 0) * (n : ℝ) := by
    calc c * B
        ≤ ((max C₁ 0) * ((n : ℝ) / Real.log (n : ℝ))) * ((max C₂ 0) * Real.log (n : ℝ)) := by
          apply mul_le_mul h1' h2' hB_nn
          positivity
      _ = (max C₁ 0) * (max C₂ 0) * ((n : ℝ) / Real.log (n : ℝ) * Real.log (n : ℝ)) := by ring
      _ = (max C₁ 0) * (max C₂ 0) * (n : ℝ) := by
          rw [div_mul_cancel₀ _ (ne_of_gt hlogn_pos)]
  calc c / (n : ℝ) * B = (c * B) / (n : ℝ) := by ring
    _ ≤ ((max C₁ 0) * (max C₂ 0) * (n : ℝ)) / (n : ℝ) := by
        gcongr
    _ = (max C₁ 0) * (max C₂ 0) := by
        rw [mul_div_assoc, div_self (ne_of_gt hnpos), mul_one]

/-- **Phase C — `h_bdd_above` genuine discharge**: for the distinct code,
the per-symbol output rate is eventually bounded above (uniformly in `n`),
a.s. in `ω`. This is the genuine boundedness the headline needs, supplied
internally from the Phase B counting envelope rather than as a hypothesis.

(`α Ω` carry the full measure-theoretic instance set since the conclusion
is phrased through `blockRV` / `ErgodicProcess`.) -/
theorem lz78DistinctEncodingLength_isBoundedUnder_le
    {Ω : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n =>
          (lz78DistinctEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ)) := by
  -- Holds for *every* `ω`: the rate is dominated by the `=O 1` envelope.
  refine Filter.Eventually.of_forall (fun ω => ?_)
  -- The per-`ω` input family.
  set input : ℕ → List α :=
    fun n => List.ofFn (p.toStationaryProcess.blockRV n ω) with hinput
  have hlen : ∀ n, (input n).length = n := by
    intro n; rw [hinput]; exact List.length_ofFn
  -- The envelope `(c/n)·bitcost` is `=O 1`, so eventually bounded above.
  obtain ⟨C, hC⟩ := (lz78DistinctEncodingLength_rate_isBigO_one input hlen).bound
  refine Filter.isBoundedUnder_of_eventually_le (a := C) ?_
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n :=
    Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩
  filter_upwards [hC, hev] with n hCn hn
  -- The actual rate is `≤` the envelope (per-symbol bound), and the
  -- envelope is `≤ C·‖1‖ = C`.
  have hbound :
      (lz78DistinctEncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
          / (n : ℝ)
        ≤ ((lz78PhraseStrings (input n)).length : ℝ) / (n : ℝ)
            * ((Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2) := by
    rw [hinput]
    exact lz78DistinctEncodingLength_real_per_symbol_le n hn
      (p.toStationaryProcess.blockRV n ω)
  have henv_le : ((lz78PhraseStrings (input n)).length : ℝ) / (n : ℝ)
      * ((Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2) ≤ C := by
    have := hCn
    rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (1:ℝ)), mul_one,
      Real.norm_of_nonneg (by positivity)] at this
    exact this
  exact le_trans hbound henv_le

/-- **Lower boundedness** of the distinct rate (mirror of
`lz78GreedyImpl_isBoundedUnder_ge`): the rate is `≥ 0` for every `n`. -/
theorem lz78DistinctEncodingLength_isBoundedUnder_ge
    {Ω : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n =>
          (lz78DistinctEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ)) := by
  refine Filter.Eventually.of_forall (fun ω => ?_)
  refine Filter.isBoundedUnder_of_eventually_ge (a := 0) ?_
  exact Filter.Eventually.of_forall (fun n =>
    lz78DistinctEncodingLength_per_symbol_nonneg n
      (p.toStationaryProcess.blockRV n ω))

end BoundedAbove

/-! ## §4. Headline with `h_bdd_above` discharged -/

section Headline

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **T4-A headline for the distinct code, with `h_bdd_above` and
`h_bdd_below` both discharged internally**.

Compared to `lz78_two_sided_optimality_greedy_impl_bdd_below_free`
(`LZ78FinalGlue.lean`, which still carries the honest `h_bdd_above`), this
form is stated about `lz78DistinctEncodingLength` (whose count is the
genuine *distinct* phrase count) and **removes** the boundedness
hypothesis entirely: both `IsBoundedUnder` halves are discharged from the
Phase B counting envelope (`lz78DistinctEncodingLength_isBoundedUnder_le`)
and nonnegativity (`..._ge`). Only the two genuine Cover–Thomas chain
hypotheses (Eq. 13.124 / 13.130) remain. -/
theorem lz78_two_sided_optimality_distinct_bdd_free
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (h_achiev : IsLZ78AchievabilityChainHyp μ p.toStationaryProcess
                  (@lz78DistinctEncodingLength α _ _ _))
    (h_converse : IsLZ78ConverseChainHyp μ p.toStationaryProcess
                  (@lz78DistinctEncodingLength α _ _ _)) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78DistinctEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) :=
  lz78_two_sided_optimality_ergodic μ p (@lz78DistinctEncodingLength α _ _ _)
    h_achiev h_converse
    (lz78DistinctEncodingLength_isBoundedUnder_le μ p)
    (lz78DistinctEncodingLength_isBoundedUnder_ge μ p)

end Headline

end InformationTheory.Shannon

import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.Basic
import InformationTheory.Shannon.LZ78.GreedyParsing
import InformationTheory.Shannon.LZ78.GreedyLongestPrefix
import InformationTheory.Shannon.LZ78.PhraseCounting
import InformationTheory.Shannon.LZ78.ZivAchievabilityComposition
import InformationTheory.Shannon.SMB.AlgoetCover.Liminf
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.GroupWithZero
import InformationTheory.Shannon.LZ78.AsymptoticOptimality.EncodingLength

/-! # LZ78 parent-bridge: converse a.s.-eventual lower bound (part 2/3) -/

namespace InformationTheory.Shannon

open scoped Topology

set_option linter.unusedSectionVars false

/-! ## §3. Parent-theorem bridge -/

section ParentBridge

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The genuine greedy encoding length has the
right type to plug into the parent `lz78_asymptotic_optimality`
`lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` parameter slot. -/
example : (∀ n, (Fin n → α) → ℕ) := @lz78GreedyEncodingLength α _ _

/-- The per-symbol negative log-likelihood in bits, `blockLogAvg / Real.log 2`.

The base-2 (bit) version of `blockLogAvg`. SMB (`shannon_mcmillan_breiman`)
converges `blockLogAvg → entropyRate` in nats; dividing through by `Real.log 2`
gives the bit-unit version converging to `entropyRate₂`, the unit that matches
the base-2 LZ78 bit-rate `lz78GreedyEncodingLength/n`. -/
noncomputable def blockLogAvg₂
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ blockLogAvg μ p n ω / Real.log 2

/-- The Shannon–McMillan–Breiman theorem in bits: `blockLogAvg₂` converges a.s. to
`entropyRate₂`.

Obtained from `shannon_mcmillan_breiman` (nat units) by dividing the
convergence through by `Real.log 2`: this is the unit rescaling
`entropyRate / Real.log 2 = entropyRate₂`, not new ergodic content.

The body is a genuine unit rescaling (`Tendsto.div_const (Real.log 2)` then
`simpa [blockLogAvg₂, entropyRate₂]`); both defs unfold to `… / Real.log 2`,
so no degenerate rewrite.
@audit:ok -/
theorem shannon_mcmillan_breiman₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n ↦ blockLogAvg₂ μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate₂ μ p.toStationaryProcess)) := by
  filter_upwards [shannon_mcmillan_breiman μ p] with ω hω
  have := hω.div_const (Real.log 2)
  simpa only [blockLogAvg₂, entropyRate₂] using this

/-- Factorial-power decay `c! · 2^c ≤ (c+1)^c` (real form). The per-`c`
structure-Kraft term `c!/(c+1)^c` is geometrically small. Proved by induction;
the step uses Bernoulli `2·(c+1)^(c+1) ≤ (c+2)^(c+1)`. -/
theorem factorial_two_pow_le_succ_pow (c : ℕ) :
    (c.factorial : ℝ) * 2 ^ c ≤ ((c : ℝ) + 1) ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
      -- `(c+1)!·2^(c+1) = 2(c+1)·(c!·2^c) ≤ 2(c+1)·(c+1)^c = 2·(c+1)^(c+1)`.
      have hcpos : (0 : ℝ) ≤ (c : ℝ) + 1 := by positivity
      have hstep1 : ((c + 1).factorial : ℝ) * 2 ^ (c + 1)
          ≤ 2 * ((c : ℝ) + 1) ^ (c + 1) := by
        have hfac : ((c + 1).factorial : ℝ) = ((c : ℝ) + 1) * (c.factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        rw [hfac]
        calc ((c : ℝ) + 1) * (c.factorial : ℝ) * 2 ^ (c + 1)
            = (2 * ((c : ℝ) + 1)) * ((c.factorial : ℝ) * 2 ^ c) := by ring
          _ ≤ (2 * ((c : ℝ) + 1)) * (((c : ℝ) + 1) ^ c) := by
              apply mul_le_mul_of_nonneg_left ih; positivity
          _ = 2 * ((c : ℝ) + 1) ^ (c + 1) := by ring
      -- Bernoulli: `2·(c+1)^(c+1) ≤ (c+2)^(c+1)`.
      have hcne : ((c : ℝ) + 1) ≠ 0 := by positivity
      have hcpos' : (0 : ℝ) < (c : ℝ) + 1 := by positivity
      have hbern : 2 * ((c : ℝ) + 1) ^ (c + 1) ≤ ((c : ℝ) + 2) ^ (c + 1) := by
        -- Bernoulli with `a = 1/(c+1)`, `n = c+1`: `1 + (c+1)·a ≤ (1+a)^(c+1)`.
        have hb := one_add_mul_le_pow (a := 1 / ((c : ℝ) + 1)) (by
          have : (0 : ℝ) ≤ 1 / ((c : ℝ) + 1) := by positivity
          linarith) (c + 1)
        -- LHS `1 + ↑(c+1)·(1/(c+1)) = 2`.
        have hlhs : (1 : ℝ) + ((c + 1 : ℕ) : ℝ) * (1 / ((c : ℝ) + 1)) = 2 := by
          push_cast; field_simp; ring
        rw [hlhs] at hb
        -- RHS `(1 + 1/(c+1))^(c+1) = (c+2)^(c+1)/(c+1)^(c+1)`.
        have hrhs : (1 + 1 / ((c : ℝ) + 1)) ^ (c + 1)
            = ((c : ℝ) + 2) ^ (c + 1) / ((c : ℝ) + 1) ^ (c + 1) := by
          rw [← div_pow]
          congr 1
          field_simp; ring
        rw [hrhs] at hb
        have hden : (0 : ℝ) < ((c : ℝ) + 1) ^ (c + 1) := by positivity
        rw [le_div_iff₀ hden] at hb
        linarith [hb]
      calc ((c + 1).factorial : ℝ) * 2 ^ (c + 1)
          ≤ 2 * ((c : ℝ) + 1) ^ (c + 1) := hstep1
        _ ≤ ((c : ℝ) + 2) ^ (c + 1) := hbern
        _ = ((↑(c + 1) : ℝ) + 1) ^ (c + 1) := by push_cast; ring

/-- Bit-length decay (nat form) `2^{bitLength c a} ≥ (c+1)·a`. The per-phrase
bit cost is large enough that `2^{-bitLength}` collapses the dictionary-size and
alphabet-size factors. From `Nat.lt_pow_succ_log_self`: `m + 1 ≤ 2·2^{log₂ m}`. -/
theorem two_pow_bitLength_ge (c a : ℕ) :
    (c + 1) * a ≤ 2 ^ LZ78Phrase.bitLength c a := by
  -- `2^{bitLength c a} = 4 · 2^{log₂(c+1)} · 2^{log₂ a}`.
  have hbit : 2 ^ LZ78Phrase.bitLength c a
      = 4 * 2 ^ Nat.log 2 (c + 1) * 2 ^ Nat.log 2 a := by
    rw [LZ78Phrase.bitLength_eq]
    rw [show Nat.log 2 (c + 1) + Nat.log 2 a + 2
          = 2 + Nat.log 2 (c + 1) + Nat.log 2 a from by ring]
    rw [pow_add, pow_add]
    ring
  rw [hbit]
  -- `c+1 ≤ 2·2^{log₂(c+1)}` and `a ≤ 2·2^{log₂ a}`, then multiply.
  have hc1 : c + 1 ≤ 2 * 2 ^ Nat.log 2 (c + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (c + 1)
    rw [pow_succ] at this
    omega
  have ha : a ≤ 2 * 2 ^ Nat.log 2 a := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) a
    rw [pow_succ] at this
    omega
  calc (c + 1) * a
      ≤ (2 * 2 ^ Nat.log 2 (c + 1)) * (2 * 2 ^ Nat.log 2 a) :=
        Nat.mul_le_mul hc1 ha
    _ = 4 * 2 ^ Nat.log 2 (c + 1) * 2 ^ Nat.log 2 a := by ring

/-- The dependent function type assigning
each phrase position `j : Fin c` a parent index in `Fin (j+1)` (one of the `j`
earlier phrases or the empty prefix) has exactly `c!` elements. -/
theorem fintype_card_parentIdx (c : ℕ) :
    Fintype.card ((j : Fin c) → Fin (j.val + 1)) = c.factorial := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ i + 1) c]
  exact Finset.prod_range_add_one_eq_factorial c

theorem lz78PhraseStrings_getElem_eq_of_parentData_eq {n c : ℕ} (x y : Fin n → α)
    (hPx_len : (lz78PhraseStrings (List.ofFn x)).length = c)
    (hPy_len : (lz78PhraseStrings (List.ofFn y)).length = c)
    (hparent : ∀ j (hj : j < c),
      min ((lz78PhraseStrings (List.ofFn x)).idxOf
            (((lz78PhraseStrings (List.ofFn x))[j]'(by omega)).dropLast)) j
        = min ((lz78PhraseStrings (List.ofFn y)).idxOf
            (((lz78PhraseStrings (List.ofFn y))[j]'(by omega)).dropLast)) j)
    (hsym : ∀ j (hj : j < c),
      ((lz78PhraseStrings (List.ofFn x))[j]'(by omega)).getLast
          (lz78PhraseStrings_forall_ne_nil (List.ofFn x) _ (List.getElem_mem _))
        = ((lz78PhraseStrings (List.ofFn y))[j]'(by omega)).getLast
          (lz78PhraseStrings_forall_ne_nil (List.ofFn y) _ (List.getElem_mem _))) :
    lz78PhraseStrings (List.ofFn x) = lz78PhraseStrings (List.ofFn y) := by
  classical
  let P : (Fin n → α) → List (List α) := fun z ↦ lz78PhraseStrings (List.ofFn z)
  have hPx_len : (P x).length = c := hPx_len
  have hPy_len : (P y).length = c := hPy_len
  have hparent : ∀ j (hj : j < c),
      min ((P x).idxOf (((P x)[j]'(by omega)).dropLast)) j
        = min ((P y).idxOf (((P y)[j]'(by omega)).dropLast)) j := hparent
  have hsym : ∀ j (hj : j < c),
      ((P x)[j]'(by omega)).getLast
          (lz78PhraseStrings_forall_ne_nil (List.ofFn x) _ (List.getElem_mem _))
        = ((P y)[j]'(by omega)).getLast
          (lz78PhraseStrings_forall_ne_nil (List.ofFn y) _ (List.getElem_mem _)) :=
    hsym
  have hne_x : ∀ w ∈ P x, w ≠ [] := lz78PhraseStrings_forall_ne_nil (List.ofFn x)
  have hne_y : ∀ w ∈ P y, w ≠ [] := lz78PhraseStrings_forall_ne_nil (List.ofFn y)
  have hidx_nil_x : (P x).idxOf [] = (P x).length := by
    rw [List.idxOf_eq_length_iff]
    intro h; exact (hne_x [] h) rfl
  have hinv_x := lz78PhraseStrings_dropLast_earlier (List.ofFn x)
  have hinv_y := lz78PhraseStrings_dropLast_earlier (List.ofFn y)
  -- KEY: phrase lists agree, by strong induction on the position.
  have hPeq : ∀ j (hj : j < c),
      (P x)[j]'(by omega) = (P y)[j]'(by omega) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j IH =>
      intro hj
      -- step 1: dropLast agree at j
      have hdl : ((P x)[j]'(by omega)).dropLast = ((P y)[j]'(by omega)).dropLast := by
        -- parent index agreement at j (as naturals)
        have hpeq : min ((P x).idxOf (((P x)[j]'(by omega)).dropLast)) j
            = min ((P y).idxOf (((P y)[j]'(by omega)).dropLast)) j := hparent j hj
        -- the dropLast-earlier invariants at j
        have hix : ((P x)[j]'(by omega)).dropLast ∈ (P x).take j
            ∨ ((P x)[j]'(by omega)).dropLast = [] := hinv_x j (by omega)
        have hiy : ((P y)[j]'(by omega)).dropLast ∈ (P y).take j
            ∨ ((P y)[j]'(by omega)).dropLast = [] := hinv_y j (by omega)
        set dx := ((P x)[j]'(by omega)).dropLast with hdx_def
        set dy := ((P y)[j]'(by omega)).dropLast with hdy_def
        rcases hix with hix | hix
        · -- dx ∈ take j: idxOf dx < j, so parent picks dx = (P x)[idxOf dx]
          have hidx_x : (P x).idxOf dx < j := (List.mem_take_iff_idxOf_lt
            (List.mem_of_mem_take hix)).mp hix
          have hpx_eq : min ((P x).idxOf dx) j = (P x).idxOf dx := min_eq_left (by omega)
          -- from hpeq, min (idxOf dy) j = idxOf dx < j ⇒ idxOf dy < j too
          rw [hpx_eq] at hpeq
          have hidx_y : (P y).idxOf dy < j := by
            by_contra hge
            rw [min_eq_right (by omega : j ≤ (P y).idxOf dy)] at hpeq
            omega
          have hpy_eq : min ((P y).idxOf dy) j = (P y).idxOf dy :=
            min_eq_left (by omega)
          rw [hpy_eq] at hpeq
          -- p := idxOf dx = idxOf dy < j; recover dx, dy via getElem_idxOf
          set p := (P x).idxOf dx with hp_def
          have hp_lt_x : p < (P x).length := by omega
          have hp_lt_y : (P y).idxOf dy < (P y).length := by omega
          have hgx : (P x)[p]'hp_lt_x = dx := List.getElem_idxOf hp_lt_x
          have hgy : (P y)[(P y).idxOf dy]'hp_lt_y = dy := List.getElem_idxOf hp_lt_y
          -- IH at p < j
          have hpeq' : (P y).idxOf dy = p := hpeq.symm
          have hIH := IH p (by omega) (by omega)
          rw [← hgx, ← hgy]
          -- goal: (P x)[p] = (P y)[idxOf dy]; reindex idxOf dy → p, then IH
          rw [getElem_congr rfl hpeq' hp_lt_y]
          exact hIH
        · -- dx = []: idxOf [] = length = c ≥ j, so parent = j, forcing dy = []
          rw [hix]
          rw [hix, hidx_nil_x, hPx_len] at hpeq
          rw [min_eq_right (by omega : j ≤ c)] at hpeq
          -- hpeq : j = min (idxOf dy) j  ⇒ idxOf dy ≥ j
          have hge : j ≤ (P y).idxOf dy := by
            by_contra hlt
            rw [min_eq_left (by omega)] at hpeq
            omega
          -- so dy ∉ take j, hence dy = []
          rcases hiy with hiy | hiy
          · exfalso
            have := (List.mem_take_iff_idxOf_lt (List.mem_of_mem_take hiy)).mp hiy
            omega
          · exact hiy.symm
      -- step 2: getLast agree at j (from sym equality)
      have hgl : ((P x)[j]'(by omega)).getLast (hne_x _ (List.getElem_mem _))
          = ((P y)[j]'(by omega)).getLast (hne_y _ (List.getElem_mem _)) := hsym j hj
      -- assemble: phrase = dropLast ++ [getLast]
      rw [← List.dropLast_append_getLast (hne_x _ (List.getElem_mem _)),
        ← List.dropLast_append_getLast (hne_y _ (List.getElem_mem _)), hdl, hgl]
  -- phrase lists equal as lists
  apply List.ext_getElem (by rw [hPx_len, hPy_len])
  intro j h1 h2
  have hjc : j < c := by rw [← hPx_len]; exact h1
  exact hPeq j hjc

theorem lz78PhraseStrings_tail_eq_of_tailIdx_eq {n c : ℕ} (x y : Fin n → α)
    (hPlist : lz78PhraseStrings (List.ofFn x) = lz78PhraseStrings (List.ofFn y))
    (hPx_len : (lz78PhraseStrings (List.ofFn x)).length = c)
    (htx_mem : Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn x))
        ∈ lz78PhraseStrings (List.ofFn x)
      ∨ Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn x)) = [])
    (hty_mem : Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn y))
        ∈ lz78PhraseStrings (List.ofFn y)
      ∨ Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn y)) = [])
    (htailval :
      min ((lz78PhraseStrings (List.ofFn x)).idxOf
          (Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn x)))) c
        = min ((lz78PhraseStrings (List.ofFn x)).idxOf
          (Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn y)))) c) :
    Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn x))
      = Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn y)) := by
  classical
  set tx := Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn x)) with htx_def
  set ty := Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn y)) with hty_def
  -- [] is never a phrase, so its idxOf = length = c (for `P x`)
  have hne_x : ∀ w ∈ lz78PhraseStrings (List.ofFn x), w ≠ [] :=
    lz78PhraseStrings_forall_ne_nil (List.ofFn x)
  have hidx_nil_x : (lz78PhraseStrings (List.ofFn x)).idxOf []
      = (lz78PhraseStrings (List.ofFn x)).length := by
    rw [List.idxOf_eq_length_iff]
    intro h; exact (hne_x [] h) rfl
  have hidx_nil : (lz78PhraseStrings (List.ofFn x)).idxOf [] = c := by
    rw [hidx_nil_x, hPx_len]
  rcases htx_mem with htx_mem | htx_mem
  · -- tx ∈ P x: idxOf tx < c, so min = idxOf tx, forcing idxOf ty = idxOf tx < c
    have hlt_x : (lz78PhraseStrings (List.ofFn x)).idxOf tx
        < (lz78PhraseStrings (List.ofFn x)).length := List.idxOf_lt_length_of_mem htx_mem
    have hlt_x' : (lz78PhraseStrings (List.ofFn x)).idxOf tx < c := by
      rw [← hPx_len]; exact hlt_x
    rw [min_eq_left (by omega)] at htailval
    have hlt_y : (lz78PhraseStrings (List.ofFn x)).idxOf ty < c := by
      by_contra hge
      rw [min_eq_right (by omega)] at htailval
      omega
    rw [min_eq_left (by omega)] at htailval
    -- idxOf tx = idxOf ty in P x; recover both via getElem_idxOf
    have hgx :
        (lz78PhraseStrings (List.ofFn x))[(lz78PhraseStrings (List.ofFn x)).idxOf tx]'(by omega)
        = tx := List.getElem_idxOf (by omega)
    have hgy :
        (lz78PhraseStrings (List.ofFn x))[(lz78PhraseStrings (List.ofFn x)).idxOf ty]'(by omega)
        = ty := List.getElem_idxOf (by omega)
    rw [← hgx, ← hgy, getElem_congr rfl htailval (by omega)]
  · -- tx = []: idxOf tx = c, min = c, forcing idxOf ty ≥ c, so ty ∉ P x ⇒ ty = []
    rw [htx_mem, hidx_nil, min_self] at htailval
    have hge : c ≤ (lz78PhraseStrings (List.ofFn x)).idxOf ty := by
      by_contra hlt
      rw [min_eq_left (by omega)] at htailval
      omega
    rcases hty_mem with hty_mem | hty_mem
    · exfalso
      have hmem' : ty ∈ lz78PhraseStrings (List.ofFn x) := by rw [hPlist]; exact hty_mem
      have hlt := List.idxOf_lt_length_of_mem hmem'
      rw [hPx_len] at hlt
      omega
    · rw [htx_mem, hty_mem]

theorem fintype_card_parentData_eq (c : ℕ) :
    Fintype.card
        (((j : Fin c) → Fin (j.val + 1)) × (Fin c → α) × Fin (c + 1))
      = c.factorial * (Fintype.card α) ^ c * (c + 1) := by
  rw [Fintype.card_prod, Fintype.card_prod, fintype_card_parentIdx,
    Fintype.card_pi]
  simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ]
  ring

/-- The fiber-cardinality count is bounded by the parent-data target (nat form):
the map sending `x` (in the `c`-phrase fiber) to its parent indices, phrase
symbols, and tail index is injective, so the fiber injects into
`((j : Fin c) → Fin (j+1)) × (Fin c → α) × Fin (c+1)`, whose cardinality is
`c! · |α|^c · (c+1)`. Injectivity uses the parent-extension invariant
`lz78PhraseStrings_dropLast_earlier` (each phrase's `dropLast` is an earlier
phrase or empty) to reconstruct the phrase list by strong induction on the
position, and `lz78PhraseStrings_flatten_prefix` + `List.ofFn_injective` to
recover `x` from the phrase list and tail. -/
theorem lz78_phrase_count_fiber_card_le_nat (n c : ℕ) :
    (Finset.univ.filter
          (fun x : Fin n → α ↦ (lz78PhraseStrings (List.ofFn x)).length = c)).card
      ≤ c.factorial * (Fintype.card α) ^ c * (c + 1) := by
  classical
  -- Encoding target: parent indices, phrase symbols, tail index.
  let D := ((j : Fin c) → Fin (j.val + 1)) × (Fin c → α) × Fin (c + 1)
  -- For a tuple `x`, its phrase list.
  let P : (Fin n → α) → List (List α) := fun x ↦ lz78PhraseStrings (List.ofFn x)
  -- Parent index of phrase `j` of `x`: the first index of `(P x)[j].dropLast`
  -- in `P x`, capped to `Fin (j+1)` (value `j` marks the empty parent).
  let parent : (Fin n → α) → (j : Fin c) → Fin (j.val + 1) := fun x j ↦
    ⟨min ((P x).idxOf ((((P x)[j.val]?).getD []).dropLast)) j.val, by
      have : min ((P x).idxOf ((((P x)[j.val]?).getD []).dropLast)) j.val ≤ j.val :=
        min_le_right _ _
      omega⟩
  -- Last symbol of phrase `j` of `x`.
  let sym : (Fin n → α) → Fin c → α := fun x j ↦
    ((P x)[j.val]?.getD []).getLastD (Classical.arbitrary α)
  -- Tail index of `x`: index of the unfinished tail in `P x` (or `c` for empty).
  let tailIdx : (Fin n → α) → Fin (c + 1) := fun x ↦
    ⟨min ((P x).idxOf (Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn x)))) c, by
      have : min ((P x).idxOf (Classical.choose (lz78PhraseStrings_flatten_tail_mem
        (List.ofFn x)))) c ≤ c := min_le_right _ _
      omega⟩
  let Φ : (Fin n → α) → D := fun x ↦ (parent x, sym x, tailIdx x)
  -- The fiber injects into `D` via `Φ`.
  have hcard : (Finset.univ.filter
        (fun x : Fin n → α ↦ (lz78PhraseStrings (List.ofFn x)).length = c)).card
      ≤ Fintype.card D := by
    rw [← Finset.card_univ (α := D)]
    refine Finset.card_le_card_of_injOn Φ (fun x _ ↦ Finset.mem_univ _) ?_
    -- injectivity on the fiber
    intro x hx y hy hΦ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx hy
    -- both phrase lists have length `c`
    have hPx_len : (P x).length = c := hx
    have hPy_len : (P y).length = c := hy
    -- componentwise equality of the encoding
    have hpar : parent x = parent y := congrArg Prod.fst hΦ
    have hsym : sym x = sym y := congrArg (fun t ↦ t.2.1) hΦ
    have htail : tailIdx x = tailIdx y := congrArg (fun t ↦ t.2.2) hΦ
    -- all phrases non-empty
    have hne_x : ∀ w ∈ P x, w ≠ [] := lz78PhraseStrings_forall_ne_nil (List.ofFn x)
    have hne_y : ∀ w ∈ P y, w ≠ [] := lz78PhraseStrings_forall_ne_nil (List.ofFn y)
    -- `sym x j = (P x)[j].getLast` on the fiber (and same for y)
    have hgetLast_x : ∀ j (hj : j < c), sym x ⟨j, hj⟩
        = ((P x)[j]'(by omega)).getLast (hne_x _ (List.getElem_mem _)) := by
      intro j hj
      have hget? : (P x)[j]? = some ((P x)[j]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      simp only [sym, hget?, Option.getD_some]
      rw [List.getLastD_eq_getLast?,
        List.getLast?_eq_some_getLast (hne_x _ (List.getElem_mem _)), Option.getD_some]
    have hgetLast_y : ∀ j (hj : j < c), sym y ⟨j, hj⟩
        = ((P y)[j]'(by omega)).getLast (hne_y _ (List.getElem_mem _)) := by
      intro j hj
      have hget? : (P y)[j]? = some ((P y)[j]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      simp only [sym, hget?, Option.getD_some]
      rw [List.getLastD_eq_getLast?,
        List.getLast?_eq_some_getLast (hne_y _ (List.getElem_mem _)), Option.getD_some]
    -- `parent x j = min (idxOf (P x)[j].dropLast) j` on the fiber (and same for y)
    have hpar_x : ∀ j (hj : j < c), (parent x ⟨j, hj⟩ : ℕ)
        = min ((P x).idxOf (((P x)[j]'(by omega)).dropLast)) j := by
      intro j hj
      have hget? : (P x)[j]? = some ((P x)[j]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      simp only [parent, hget?, Option.getD_some]
    have hpar_y : ∀ j (hj : j < c), (parent y ⟨j, hj⟩ : ℕ)
        = min ((P y).idxOf (((P y)[j]'(by omega)).dropLast)) j := by
      intro j hj
      have hget? : (P y)[j]? = some ((P y)[j]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      simp only [parent, hget?, Option.getD_some]
    -- KEY: phrase lists agree, via the parent-data reconstruction helper. The
    -- parent-index and last-symbol agreements come from `hpar`/`hsym`.
    have hparent : ∀ j (hj : j < c),
        min ((lz78PhraseStrings (List.ofFn x)).idxOf
              (((lz78PhraseStrings (List.ofFn x))[j]'(by omega)).dropLast)) j
          = min ((lz78PhraseStrings (List.ofFn y)).idxOf
              (((lz78PhraseStrings (List.ofFn y))[j]'(by omega)).dropLast)) j := by
      intro j hj
      have := congrArg (fun f ↦ (f ⟨j, hj⟩ : ℕ)) hpar
      simp only at this
      rw [hpar_x j hj, hpar_y j hj] at this
      exact this
    have hsymeq : ∀ j (hj : j < c),
        ((lz78PhraseStrings (List.ofFn x))[j]'(by omega)).getLast
            (lz78PhraseStrings_forall_ne_nil (List.ofFn x) _ (List.getElem_mem _))
          = ((lz78PhraseStrings (List.ofFn y))[j]'(by omega)).getLast
            (lz78PhraseStrings_forall_ne_nil (List.ofFn y) _ (List.getElem_mem _)) := by
      intro j hj
      rw [← hgetLast_x j hj, ← hgetLast_y j hj, hsym]
    have hPlist : P x = P y :=
      lz78PhraseStrings_getElem_eq_of_parentData_eq x y hPx_len hPy_len hparent hsymeq
    -- step C: tails agree, hence inputs agree.
    set tx := Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn x)) with htx_def
    set ty := Classical.choose (lz78PhraseStrings_flatten_tail_mem (List.ofFn y)) with hty_def
    obtain ⟨htx_flat, htx_mem⟩ :=
      Classical.choose_spec (lz78PhraseStrings_flatten_tail_mem (List.ofFn x))
    obtain ⟨hty_flat, hty_mem⟩ :=
      Classical.choose_spec (lz78PhraseStrings_flatten_tail_mem (List.ofFn y))
    rw [← htx_def] at htx_flat htx_mem
    rw [← hty_def] at hty_flat hty_mem
    -- tail index value equality (as naturals), with `P x = P y`
    have htvx : (tailIdx x).val = min ((P x).idxOf tx) c := by
      simp only [tailIdx, ← htx_def]
    have htvy : (tailIdx y).val = min ((P y).idxOf ty) c := by
      simp only [tailIdx, ← hty_def]
    have htailval : min ((P x).idxOf tx) c = min ((P x).idxOf ty) c := by
      have hval : (tailIdx x).val = (tailIdx y).val := congrArg Fin.val htail
      rw [htvx, htvy, ← hPlist] at hval
      exact hval
    -- the tails coincide, via the tail-index reconstruction helper.
    have htxy : tx = ty :=
      lz78PhraseStrings_tail_eq_of_tailIdx_eq x y hPlist hPx_len htx_mem hty_mem htailval
    -- assemble the inputs
    have hinput : List.ofFn x = List.ofFn y := by
      rw [← htx_flat, ← hty_flat]
      rw [htxy]
      exact congrArg (· ++ ty) (congrArg List.flatten hPlist)
    exact List.ofFn_injective hinput
  refine hcard.trans ?_
  -- `Fintype.card D = c! · |α|^c · (c+1)`.
  have hcardD : Fintype.card D = c.factorial * (Fintype.card α) ^ c * (c + 1) :=
    fintype_card_parentData_eq c
  omega

/-- **Distinct-phrase fiber-cardinality count (the genuine combinatorial
counting core of G2)**.

The number of `n`-tuples `x : Fin n → α` whose genuine greedy parse emits
exactly `c` distinct phrases is bounded by `(n + 1) · c! · |α|^c`. This is the
counting fact behind the polynomial Kraft bound `lz78_block_kraft_poly`: the
map `x ↦ (lz78PhraseStrings (List.ofFn x), tail)` is injective
(`lz78PhraseStrings_flatten_prefix` reconstructs `List.ofFn x`, and
`List.ofFn_injective`), and the parent-extension dictionary structure
(`lz78PhraseStrings_dropLast_earlier`: each phrase's `dropLast` is an earlier
entry or empty) makes the `j`-th phrase one of the `j` earlier entries (or the
empty prefix) extended by one symbol, giving `≤ c! · |α|^c` valid phrase-lists;
the unfinished tail (`lz78PhraseStrings_flatten_tail_mem`, a dictionary member
or empty) contributes a multiplicity `≤ c + 1 ≤ n + 1` (since `c ≤ n`).

Proved unconditionally in `lz78_phrase_count_fiber_card_le_nat` via
`Finset.card_le_card_of_injOn` into the parent-data Fintype
`((j : Fin c) → Fin (j+1)) × (Fin c → α) × Fin (c+1)` (cardinality
`fintype_card_parentIdx` = `c!`, times `|α|^c`, times `c+1`), with the empty
fiber for `c > n` handled by `lz78PhraseStrings_count_le`.

@audit:ok (FINAL completion audit 2026-06-21, commit `bd28e0e`, independent
subagent). Genuine counting bound — the injection `x ↦ (parent, sym, tailIdx)`
in `lz78_phrase_count_fiber_card_le_nat` is really injective (strong induction
reconstructs each phrase's `dropLast` from the parent index via the
parent-extension invariant, recovers the last symbol from `sym`, reassembles
the phrase, then recovers `x` via `flatten ++ tail` + `List.ofFn_injective`);
no smuggling. Non-circular, non-degenerate; the `(c+1) ≤ (n+1)` cast upgrade
+ empty-fiber-for-`c>n` are genuine. `#print axioms =
[propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-confirmed). -/
theorem lz78_phrase_count_fiber_card_le (n c : ℕ) :
    ((Finset.univ.filter
          (fun x : Fin n → α ↦ (lz78PhraseStrings (List.ofFn x)).length = c)).card : ℝ)
      ≤ ((n : ℝ) + 1) * (c.factorial : ℝ) * (Fintype.card α : ℝ) ^ c := by
  -- The fiber is empty once `c > n` (the parse emits `≤ n` phrases), so `c ≤ n`
  -- whenever the fiber is non-empty; combine with the nat-form count bound.
  set S := Finset.univ.filter
    (fun x : Fin n → α ↦ (lz78PhraseStrings (List.ofFn x)).length = c) with hS
  rcases Nat.lt_or_ge n c with hcn | hcn
  · -- c > n: the fiber is empty (the parse emits at most `n` phrases).
    have hempty : S = ∅ := by
      rw [hS, Finset.filter_eq_empty_iff]
      intro x _ hlen
      have hle : (lz78PhraseStrings (List.ofFn x)).length ≤ (List.ofFn x).length :=
        lz78PhraseStrings_count_le _
      rw [hlen, List.length_ofFn] at hle
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · -- c ≤ n: `(c+1) ≤ (n+1)` upgrades the nat bound's tail factor.
    have hnat := lz78_phrase_count_fiber_card_le_nat (α := α) n c
    have hcast : (S.card : ℝ) ≤ (c.factorial * (Fintype.card α) ^ c * (c + 1) : ℕ) := by
      exact_mod_cast hnat
    refine hcast.trans ?_
    push_cast
    have hc1 : ((c : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hcn
    have hfac_nn : (0 : ℝ) ≤ (c.factorial : ℝ) := by positivity
    have hpow_nn : (0 : ℝ) ≤ (Fintype.card α : ℝ) ^ c := by positivity
    calc (c.factorial : ℝ) * (Fintype.card α : ℝ) ^ c * ((c : ℝ) + 1)
        ≤ (c.factorial : ℝ) * (Fintype.card α : ℝ) ^ c * ((n : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left hc1; positivity
      _ = ((n : ℝ) + 1) * (c.factorial : ℝ) * (Fintype.card α : ℝ) ^ c := by ring

/-- The per-`c` Kraft term bound (Part C, geometric collapse).

The fiber sum over `n`-tuples with `c` distinct phrases is geometrically small:
`#fiber(c) · (1/2)^{c·bitLength(c,|α|)} ≤ (n+1)·(1/2)^c`. Combines the counting
bound `lz78_phrase_count_fiber_card_le` (`#fiber(c) ≤ (n+1)·c!·|α|^c`) with the
bit-length decay `2^{c·bitLength(c,|α|)} ≥ ((c+1)·|α|)^c` (from
`Nat.lt_pow_succ_log_self`), giving `#fiber·2^{-...} ≤ (n+1)·c!/(c+1)^c` and the
elementary inequality `c!·2^c ≤ (c+1)^c`. -/
theorem lz78_block_kraft_term_le (n c : ℕ) :
    (((Finset.univ.filter
          (fun x : Fin n → α ↦ (lz78PhraseStrings (List.ofFn x)).length = c)).card : ℝ)
        * (1 / 2 : ℝ) ^ (c * LZ78Phrase.bitLength c (Fintype.card α)))
      ≤ ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ c := by
  set F : ℝ := ((Finset.univ.filter
          (fun x : Fin n → α ↦ (lz78PhraseStrings (List.ofFn x)).length = c)).card : ℝ) with hF
  set a : ℕ := Fintype.card α with ha
  set B : ℕ := LZ78Phrase.bitLength c a with hB
  have hF_nn : 0 ≤ F := by rw [hF]; positivity
  have ha1 : 1 ≤ (a : ℝ) := by
    rw [ha]; exact_mod_cast Fintype.card_pos
  have haR_pos : (0 : ℝ) < (a : ℝ) := by linarith
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  -- Step 1: counting residual `F ≤ (n+1)·c!·a^c`.
  have hcount : F ≤ ((n : ℝ) + 1) * (c.factorial : ℝ) * (a : ℝ) ^ c :=
    lz78_phrase_count_fiber_card_le n c
  -- Step 2: `(1/2)^(c·B) = ((1/2)^B)^c`, and `(1/2)^B ≤ 1/((c+1)·a)`.
  have hpow_rw : (1 / 2 : ℝ) ^ (c * B) = ((1 / 2 : ℝ) ^ B) ^ c := by
    rw [pow_mul, ← pow_mul, Nat.mul_comm, pow_mul]
  -- `(c+1)·a ≤ 2^B`, so `a·(1/2)^B ≤ 1/(c+1)`.
  have hbit : ((c : ℝ) + 1) * (a : ℝ) ≤ (2 : ℝ) ^ B := by
    have := two_pow_bitLength_ge c a
    have hcast : (((c + 1) * a : ℕ) : ℝ) ≤ ((2 ^ B : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast
    convert hcast using 2
  have h2Bpos : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
  have hhalfB : (1 / 2 : ℝ) ^ B = 1 / (2 : ℝ) ^ B := by
    rw [div_pow, one_pow]
  -- `a·(1/2)^B ≤ 1/(c+1)`.
  have haB_le : (a : ℝ) * (1 / 2 : ℝ) ^ B ≤ 1 / ((c : ℝ) + 1) := by
    rw [hhalfB, mul_one_div, le_div_iff₀ (by positivity : (0:ℝ) < (c:ℝ) + 1),
      div_mul_eq_mul_div, div_le_one (by positivity : (0:ℝ) < (2:ℝ) ^ B)]
    -- `a · (c+1) ≤ 2^B`
    calc (a : ℝ) * ((c : ℝ) + 1) = ((c : ℝ) + 1) * (a : ℝ) := by ring
      _ ≤ (2 : ℝ) ^ B := hbit
  have haB_nn : 0 ≤ (a : ℝ) * (1 / 2 : ℝ) ^ B := by positivity
  -- Step 3: `c!·(a·(1/2)^B)^c ≤ c!·(1/(c+1))^c = c!/(c+1)^c ≤ (1/2)^c`.
  have hcore : (c.factorial : ℝ) * ((a : ℝ) * (1 / 2 : ℝ) ^ B) ^ c
      ≤ (1 / 2 : ℝ) ^ c := by
    have hpow_le : ((a : ℝ) * (1 / 2 : ℝ) ^ B) ^ c ≤ (1 / ((c : ℝ) + 1)) ^ c :=
      pow_le_pow_left₀ haB_nn haB_le c
    have hfac_nn : (0 : ℝ) ≤ (c.factorial : ℝ) := by positivity
    calc (c.factorial : ℝ) * ((a : ℝ) * (1 / 2 : ℝ) ^ B) ^ c
        ≤ (c.factorial : ℝ) * (1 / ((c : ℝ) + 1)) ^ c :=
          mul_le_mul_of_nonneg_left hpow_le hfac_nn
      _ = (c.factorial : ℝ) / ((c : ℝ) + 1) ^ c := by
          rw [div_pow, one_pow, mul_one_div]
      _ ≤ (1 / 2 : ℝ) ^ c := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < ((c:ℝ) + 1) ^ c), div_pow, one_pow,
            div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ) ^ c), one_mul]
          -- `c!·2^c ≤ (c+1)^c`
          exact factorial_two_pow_le_succ_pow c
  -- Assemble: `F·(1/2)^(cB) ≤ (n+1)·c!·a^c·(1/2)^(cB) = (n+1)·c!·(a·(1/2)^B)^c ≤ (n+1)·(1/2)^c`.
  have hpow_cB_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (c * B) := by positivity
  calc F * (1 / 2 : ℝ) ^ (c * B)
      ≤ (((n : ℝ) + 1) * (c.factorial : ℝ) * (a : ℝ) ^ c) * (1 / 2 : ℝ) ^ (c * B) :=
        mul_le_mul_of_nonneg_right hcount hpow_cB_nn
    _ = ((n : ℝ) + 1) * ((c.factorial : ℝ) * ((a : ℝ) * (1 / 2 : ℝ) ^ B) ^ c) := by
        rw [hpow_rw, mul_pow]; ring
    _ ≤ ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ c :=
        mul_le_mul_of_nonneg_left hcore hn1

/-- **G2 — polynomial `n`-block Kraft for the genuine greedy parse (the
genuine combinatorial converse brick)**.

The Kraft sum of `2^{-L_n(x)}` over all `n`-tuples `x : Fin n → α` is bounded
by a polynomial in `n`:

```
∑_{x : Fin n → α} (1/2)^{lz78GreedyEncodingLength n x} ≤ (n + 1)^2.
```

Why a polynomial and not the exact Kraft `≤ 1`: the greedy
longest-prefix-match parse is *not complete* — `lz78PhraseStrings_flatten` is a
genuine *prefix* of the input, and the unfinished tail (`flatten ++ tail =
input`, with `tail ≠ []` possible and `tail` a prefix of an existing phrase)
is *not* charged a fresh `(parent, symbol)` token. Hence
`lz78GreedyEncodingLength n x = c · bitLength c |α|` is the cost of only
the `c` completed phrases and is not a lossless code length for `x`, so the
exact Kraft inequality `∑ 2^{-L_n} ≤ 1` is FALSE. The polynomial bound is
the honest statement: the number of distinct parse *structures* with `c`
phrases is `≤ c! · |α|^c`, and `2^{-c·bitLength(c,|α|)} ≈ (c+1)^{-c}|α|^{-c}4^{-c}`,
so the structure-Kraft sum `∑_c (#structures)·2^{-c·bitLength} = O(1)`; the
unfinished tail contributes a multiplicity `≤ n + 1`, giving `O(n) ≤ (n+1)^2`.

The math is `O(n)`, so any polynomial degree `≥ 1` is a true bound; the degree
`2` here gives the summable `μ(B_n) ≤ 1/n^2` in the Barron Markov +
Borel–Cantelli lift (`blockLogAvg₂_minus_error_le_rate_ae`).

This is the genuine combinatorial new-math brick of the LZ78 converse
(Cover–Thomas Thm 13.5.3 lower bound, distinct-phrase counting).

The proof structure (Parts A + B + C, all proven, sorryAx-free) is assembled from
* Part A — fiberwise regrouping of the Kraft sum by the distinct-phrase
  count `c = φ x` (`Finset.sum_fiberwise_of_maps_to'`, `φ x ≤ n`);
* Part B — the finite counting fact `lz78_phrase_count_fiber_card_le`
  (`#fiber(c) ≤ (n+1)·c!·|α|^c`), proved via the LZ78 dictionary
  parent-extension invariant (`lz78PhraseStrings_dropLast_earlier`) and a
  `Fintype.card` injection into `((j:Fin c)→Fin (j+1)) × (Fin c → α) × Fin (c+1)`;
* Part C — the per-`c` geometric collapse `lz78_block_kraft_term_le`
  (`#fiber(c)·2^{-c·bitLength} ≤ (n+1)·(1/2)^c`, built from the bit-length decay
  `two_pow_bitLength_ge` and the factorial-power decay
  `factorial_two_pow_le_succ_pow`), then `sum_geometric_two_le` and
  `(n+1)·2 ≤ (n+1)²` (with the `n = 0` boundary `1 ≤ 1`).

The genuine combinatorial brick (Part B) is closed, so this theorem is fully
`sorryAx`-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`),
carrying no `@residual`. The statement is TRUE-as-framed (numerically checked
α=Bool, n≤6, with large slack; `n = 0` boundary exactly `1 ≤ 1`). -/
theorem lz78_block_kraft_poly (n : ℕ) :
    ∑ x : Fin n → α, (1 / 2 : ℝ) ^ (lz78GreedyEncodingLength n x)
      ≤ ((n : ℝ) + 1) ^ 2 := by
  classical
  -- Part A: group the Kraft sum by the distinct-phrase count `c = φ x`.
  set φ : (Fin n → α) → ℕ := fun x ↦ (lz78PhraseStrings (List.ofFn x)).length with hφ
  -- The encoding length depends on `x` only through `c = φ x`.
  have hLfac : ∀ x : Fin n → α,
      lz78GreedyEncodingLength n x = φ x * LZ78Phrase.bitLength (φ x) (Fintype.card α) := by
    intro x; rfl
  -- `φ x ≤ n`, so `φ x ∈ Finset.range (n+1)`.
  have hmaps : ∀ x ∈ (Finset.univ : Finset (Fin n → α)), φ x ∈ Finset.range (n + 1) := by
    intro x _
    rw [Finset.mem_range]
    have hle : φ x ≤ n := lz78GreedyPhraseCount_ofFn_le n x
    omega
  -- Fiberwise regrouping: ∑_x f(φ x) = ∑_{c∈range(n+1)} ∑_{x : φ x = c} f(φ x).
  have hfiber :
      ∑ x : Fin n → α, (1 / 2 : ℝ) ^ (lz78GreedyEncodingLength n x)
        = ∑ c ∈ Finset.range (n + 1),
            ∑ x ∈ Finset.univ.filter (fun x ↦ φ x = c),
              (1 / 2 : ℝ) ^ (c * LZ78Phrase.bitLength c (Fintype.card α)) := by
    -- `(1/2)^(L_n x) = f (φ x)` with `f c = (1/2)^(c·bitLength c |α|)`.
    have hrw : ∀ x : Fin n → α, (1 / 2 : ℝ) ^ (lz78GreedyEncodingLength n x)
        = (fun c ↦ (1 / 2 : ℝ) ^ (c * LZ78Phrase.bitLength c (Fintype.card α))) (φ x) := by
      intro x; rw [hLfac x]
    -- On each fiber `φ x = c`, the summand `f (φ x)` collapses to `f c`.
    rw [Finset.sum_congr rfl (fun x _ ↦ hrw x),
      ← Finset.sum_fiberwise_of_maps_to' hmaps
        (fun c ↦ (1 / 2 : ℝ) ^ (c * LZ78Phrase.bitLength c (Fintype.card α)))]
  rw [hfiber]
  -- Part B + C: each per-`c` term is ≤ (n+1)·(1/2)^c, then sum the geometric series.
  have hterm : ∀ c ∈ Finset.range (n + 1),
      (∑ x ∈ Finset.univ.filter (fun x ↦ φ x = c),
          (1 / 2 : ℝ) ^ (c * LZ78Phrase.bitLength c (Fintype.card α)))
        ≤ ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ c := by
    intro c _
    -- The inner summand is constant on the fiber, so the sum is `#fiber · (1/2)^…`.
    rw [Finset.sum_const, nsmul_eq_mul]
    exact lz78_block_kraft_term_le n c
  calc
    ∑ c ∈ Finset.range (n + 1),
        ∑ x ∈ Finset.univ.filter (fun x ↦ φ x = c),
          (1 / 2 : ℝ) ^ (c * LZ78Phrase.bitLength c (Fintype.card α))
      ≤ ∑ c ∈ Finset.range (n + 1), ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ c :=
        Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) * ∑ c ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ c := by
        rw [Finset.mul_sum]
    _ ≤ ((n : ℝ) + 1) ^ 2 := by
        rcases Nat.eq_zero_or_pos n with hn0 | hn1
        · -- n = 0: the sum has one term `(1/2)^0 = 1`, giving `1·1 = 1 ≤ 1`.
          subst hn0; norm_num
        · -- n ≥ 1: `∑_{c<n+1}(1/2)^c ≤ 2` and `(n+1)·2 ≤ (n+1)^2` since `2 ≤ n+1`.
          have hgeom : (∑ c ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ c) ≤ 2 :=
            sum_geometric_two_le (n + 1)
          have hnpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
          have h2le : (2 : ℝ) ≤ (n : ℝ) + 1 := by
            have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
            linarith
          calc ((n : ℝ) + 1) * ∑ c ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ c
              ≤ ((n : ℝ) + 1) * 2 := by
                exact mul_le_mul_of_nonneg_left hgeom hnpos
            _ ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) := by
                exact mul_le_mul_of_nonneg_left h2le hnpos
            _ = ((n : ℝ) + 1) ^ 2 := by ring

/-- The per-`n` bad-set measure bound (Markov on the discrete block law + G2).

For `n ≥ 1`, the LZ78 converse bad set
`B_n = {ω : lz/n < blockLogAvg₂ n ω − err_n}`
has `μ`-measure at most `1/n²`, where
`err_n = (2 log n + 2 log(n+1))/(n log 2)`.

This is the genuine Markov step of the Barron lift. The bad set factors through
the block random variable (`lz` and `blockLogAvg₂` depend on `ω` only via
`block_n ω`), so `μ(B_n) = (μ.map block_n)(S_n) = ∑_{x ∈ S_n} Pₙ(x)` over the
discrete block law `Pₙ = μ.map block_n`. For each `x ∈ S_n` with `Pₙ(x) > 0`
the defining inequality (cleared of denominators) gives
`Pₙ(x) < 2^{−Lₙ(x)}·2^{−n·err_n}`, and `2^{−n·err_n} = 1/(n²(n+1)²)`. Summing
and applying G2 (`lz78_block_kraft_poly`: `∑_x 2^{−Lₙ(x)} ≤ (n+1)²`) gives
`μ(B_n) ≤ (n+1)²/(n²(n+1)²) = 1/n²`. The genuine combinatorial residual lives
entirely in G2; this lemma is its measure-theoretic plumbing. -/
theorem lz78_converse_bad_set_measure_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) (n : ℕ) (hn : 1 ≤ n) :
    μ {ω | (lz78GreedyEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ)
          < blockLogAvg₂ μ p.toStationaryProcess n ω
            - (2 * Real.log n + 2 * Real.log (n + 1)) / ((n : ℝ) * Real.log 2)}
      ≤ (1 : ℝ≥0∞) / ((n : ℝ≥0∞) ^ 2) := by
  classical
  set q := p.toStationaryProcess with hq
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hℓ2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set Pn : Measure (Fin n → α) := μ.map (q.blockRV n) with hPn
  have hB_meas : Measurable (q.blockRV n) := q.measurable_blockRV n
  have hPn_prob : IsProbabilityMeasure Pn :=
    Measure.isProbabilityMeasure_map hB_meas.aemeasurable
  -- The bad set on the discrete block alphabet.
  set rateX : (Fin n → α) → ℝ :=
    fun x ↦ (lz78GreedyEncodingLength n x : ℝ) / (n : ℝ) with hrateX
  set bla₂X : (Fin n → α) → ℝ :=
    fun x ↦ (-(1 / (n : ℝ)) * Real.log (Pn.real {x})) / Real.log 2 with hbla₂X
  set errR : ℝ := (2 * Real.log n + 2 * Real.log (n + 1)) / ((n : ℝ) * Real.log 2) with herrR
  set S : Finset (Fin n → α) :=
    Finset.univ.filter (fun x ↦ rateX x < bla₂X x - errR) with hS
  -- `blockLogAvg₂ μ q n ω = bla₂X (block_n ω)` (depends on `ω` only via `block_n`).
  have h_bla_factor : ∀ ω, blockLogAvg₂ μ q n ω = bla₂X (q.blockRV n ω) := by
    intro ω; rw [hbla₂X]; simp only [blockLogAvg₂, blockLogAvg, hPn]
  -- The bad set is the preimage of `S` under `block_n`.
  have h_setEq : {ω | (lz78GreedyEncodingLength n (q.blockRV n ω) : ℝ) / (n : ℝ)
        < blockLogAvg₂ μ q n ω
          - (2 * Real.log n + 2 * Real.log (n + 1)) / ((n : ℝ) * Real.log 2)}
      = (q.blockRV n) ⁻¹' (S : Set (Fin n → α)) := by
    ext ω
    rw [Set.mem_preimage, Finset.mem_coe, hS, Finset.mem_filter]
    simp only [Set.mem_setOf_eq, Finset.mem_univ, true_and, hrateX, hbla₂X, herrR,
      h_bla_factor ω]
  rw [h_setEq]
  -- Pushforward: `μ(block⁻¹ S) = Pn(S) = ∑_{x∈S} Pn.real{x}`.
  have h_meas_S : MeasurableSet (S : Set (Fin n → α)) := S.measurableSet
  have h_push : μ ((q.blockRV n) ⁻¹' (S : Set (Fin n → α)))
      = Pn (S : Set (Fin n → α)) := by
    rw [hPn, Measure.map_apply hB_meas h_meas_S]
  rw [h_push]
  -- Work with the real-valued measure (`Pn` is finite).
  have h_toReal : (Pn (S : Set (Fin n → α))).toReal ≤ 1 / (n : ℝ) ^ 2 := by
    -- `Pn(S) = ∑_{x∈S} Pn.real{x}`.
    have h_sum : (Pn (S : Set (Fin n → α))).toReal = ∑ x ∈ S, Pn.real {x} := by
      rw [← measureReal_def, ← sum_measureReal_singleton]
    rw [h_sum]
    -- Per-element bound: `Pn.real{x} ≤ (1/2)^{Lₙ(x)} · (1/(n²(n+1)²))` for `x ∈ S`.
    have h_elt : ∀ x ∈ S, Pn.real {x}
        ≤ (1 / 2 : ℝ) ^ (lz78GreedyEncodingLength n x)
            * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
      intro x hxS
      have hxlt : rateX x < bla₂X x - errR := by
        rw [hS, Finset.mem_filter] at hxS; exact hxS.2
      simp only [hrateX, hbla₂X] at hxlt
      set P := Pn.real {x} with hP
      have hP_nn : 0 ≤ P := by rw [hP]; exact measureReal_nonneg
      have hcoef_pos : (0 : ℝ) < 1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) := by positivity
      have hpow_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ (lz78GreedyEncodingLength n x) := by
        positivity
      rcases eq_or_lt_of_le hP_nn with hP0 | hPpos
      · -- `P = 0`: the bound is trivial (RHS > 0).
        rw [← hP0]; positivity
      · -- `P > 0`: clear denominators and exponentiate.
        -- `n · errR · log 2 = 2 log n + 2 log(n+1)`.
        have h_nerr : (n : ℝ) * errR * Real.log 2
            = 2 * Real.log n + 2 * Real.log (n + 1) := by
          rw [herrR]; field_simp
        -- From `L/n < (-(1/n) log P)/log2 - errR`, multiply by `n · log 2 > 0`
        -- to get `L · log 2 < -log P - (2 log n + 2 log(n+1))`.
        have hLn : (lz78GreedyEncodingLength n x : ℝ) * Real.log 2
            < -Real.log P - (2 * Real.log n + 2 * Real.log (n + 1)) := by
          have h1 : (lz78GreedyEncodingLength n x : ℝ) / (n : ℝ)
                * ((n : ℝ) * Real.log 2)
              < ((-(1 / (n : ℝ)) * Real.log P) / Real.log 2 - errR)
                * ((n : ℝ) * Real.log 2) :=
            mul_lt_mul_of_pos_right hxlt (by positivity)
          have hlhs : (lz78GreedyEncodingLength n x : ℝ) / (n : ℝ)
              * ((n : ℝ) * Real.log 2)
              = (lz78GreedyEncodingLength n x : ℝ) * Real.log 2 := by
            field_simp
          have hrhs : ((-(1 / (n : ℝ)) * Real.log P) / Real.log 2 - errR)
              * ((n : ℝ) * Real.log 2)
              = -Real.log P - (n : ℝ) * errR * Real.log 2 := by
            field_simp
          rw [hlhs, hrhs, h_nerr] at h1
          exact h1
        -- Take `exp` of both sides: `P < 2^{-Lₙ} · 1/(n²(n+1)²)`.
        have hlogP_lt : Real.log P
            < Real.log ((1 / 2 : ℝ) ^ (lz78GreedyEncodingLength n x)
                * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2))) := by
          rw [Real.log_mul hpow_pos.ne' hcoef_pos.ne', Real.log_pow]
          have h_log_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
            rw [one_div, Real.log_inv]
          have h_log_coef : Real.log (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2))
              = -(2 * Real.log n + 2 * Real.log (n + 1)) := by
            rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity),
              Real.log_pow, Real.log_pow]
            push_cast; ring
          rw [h_log_half, h_log_coef]
          have : (lz78GreedyEncodingLength n x : ℝ) * -Real.log 2
              = -((lz78GreedyEncodingLength n x : ℝ) * Real.log 2) := by ring
          nlinarith [hLn, hℓ2]
        have := (Real.log_lt_log_iff hPpos (by positivity)).mp hlogP_lt
        exact le_of_lt this
    -- Sum the per-element bound and apply G2.
    calc ∑ x ∈ S, Pn.real {x}
        ≤ ∑ x ∈ S, (1 / 2 : ℝ) ^ (lz78GreedyEncodingLength n x)
            * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2)) :=
          Finset.sum_le_sum h_elt
      _ = (∑ x ∈ S, (1 / 2 : ℝ) ^ (lz78GreedyEncodingLength n x))
            * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
          rw [← Finset.sum_mul]
      _ ≤ (∑ x : Fin n → α, (1 / 2 : ℝ) ^ (lz78GreedyEncodingLength n x))
            * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          intro x _ _; positivity
      _ ≤ ((n : ℝ) + 1) ^ 2 * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
          apply mul_le_mul_of_nonneg_right (lz78_block_kraft_poly n) (by positivity)
      _ = 1 / (n : ℝ) ^ 2 := by
          have hn1 : ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
          field_simp
  -- Convert the real bound back to `ℝ≥0∞`.
  have h_ne_top : Pn (S : Set (Fin n → α)) ≠ ∞ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal h_ne_top]
  rw [show (1 : ℝ≥0∞) / ((n : ℝ≥0∞) ^ 2)
      = ENNReal.ofReal (1 / (n : ℝ) ^ 2) by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
      show (n : ℝ) ^ 2 = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring,
      ENNReal.ofReal_natCast]; push_cast; ring]
  exact ENNReal.ofReal_le_ofReal h_toReal

/-- The Barron a.s.-eventual lift: the per-realization, a.s.-eventual
converse lower bound on the greedy bit-rate by `blockLogAvg₂` minus an `o(1)`
error term.

For a stationary process `p`, almost surely the greedy bit-rate
`lz78GreedyEncodingLength n (block_n ω) / n` is, eventually in `n`, at
least `blockLogAvg₂ n ω` minus the vanishing error
`(2 log n + 2 log(n+1))/(n log 2)`:

```
∀ᵐ ω, ∀ᶠ n,  blockLogAvg₂ n ω − (2 log n + 2 log(n+1))/(n log 2) ≤ lz/n.
```

This is the Barron competitive-optimality a.s. lift (Cover–Thomas Thm 13.5.3):
a per-realization LZ78 codeword can be *shorter* than `−log₂ Pₙ{xⁿ}`, so the
expectation-level converse `H_D ≤ E[L]` does not transfer pointwise. The lift
is a Markov + first Borel–Cantelli argument on the bad set
`B_n = {ω : lz/n < blockLogAvg₂ n ω − err_n}`: by G2 (`lz78_block_kraft_poly`),
`μ(B_n) = Pₙ{xⁿ : Pₙ(xⁿ) < 2^{−Lₙ}·2^{−n·err}} ≤ 2^{−n·err}·∑ 2^{−Lₙ} ≤
2^{−n·err}·(n+1)²`, and with `n·err = 2 log₂(n+1) + 2 log₂ n` this is `≤ 1/n²`,
summable, so first Borel–Cantelli gives `∀ᵐ ω, ∀ᶠ n, ω ∉ B_n`.

Modeled on the Z-side `blockLogAvgZ_ge_negLogQInftyZ_minus_error`
(`SMB/AlgoetCover/Liminf.lean`) — the same Markov + p-series + Borel–Cantelli
template. The body is `sorry`-free: the Markov + Borel–Cantelli lift is
genuinely proven; it consumes the genuine combinatorial brick G2
(`lz78_block_kraft_poly`) through the per-`n` bad-set measure bound
`lz78_converse_bad_set_measure_le`. G2 (and hence its Part B counting lemma
`lz78_phrase_count_fiber_card_le`) is now closed, so this lemma is fully
`sorryAx`-free. -/
theorem blockLogAvg₂_minus_error_le_rate_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      blockLogAvg₂ μ p.toStationaryProcess n ω
          - (2 * Real.log n + 2 * Real.log (n + 1)) / ((n : ℝ) * Real.log 2)
        ≤ (lz78GreedyEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ) := by
  set q := p.toStationaryProcess with hq
  -- The bad set at scale `n`: the realizations where the greedy bit-rate
  -- undershoots `blockLogAvg₂ − err` by more than the error margin.
  set err : ℕ → ℝ :=
    fun n ↦ (2 * Real.log n + 2 * Real.log (n + 1)) / ((n : ℝ) * Real.log 2) with herr
  set B : ℕ → Set Ω :=
    fun n ↦ {ω | (lz78GreedyEncodingLength n (q.blockRV n ω) : ℝ) / (n : ℝ)
        < blockLogAvg₂ μ q n ω - err n} with hB
  -- Per-`n` bad-set measure bound `μ(B n) ≤ 1/n²` (Markov on the discrete
  -- block law + G2 polynomial Kraft); summable, so first Borel–Cantelli.
  have h_bound : ∀ n, 1 ≤ n → μ (B n) ≤ (1 : ℝ≥0∞) / ((n : ℝ≥0∞) ^ 2) :=
    fun n hn ↦ lz78_converse_bad_set_measure_le μ p n hn
  -- ∑' n, μ (B n) < ∞ (p-series), via the same machinery as
  -- `MRatioLowerZ_le_sq_eventually`.
  have h_tsum : ∑' n, μ (B n) ≠ ∞ := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    refine ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ?_⟩
    have h_le : (∑' n : ℕ, μ (B (n + 1)))
        ≤ ∑' n : ℕ, (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2) :=
      ENNReal.tsum_le_tsum (fun n ↦ h_bound (n + 1) (Nat.succ_le_succ (Nat.zero_le _)))
    refine ne_top_of_le_ne_top ?_ h_le
    have h_summable_real : Summable (fun n : ℕ ↦ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
    have h_nonneg : ∀ n : ℕ, (0 : ℝ) ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := fun _ ↦ by positivity
    have h_ennreal_tsum : ∑' n : ℕ,
        ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) ≠ ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg h_summable_real]
      exact ENNReal.ofReal_ne_top
    have h_pointwise : ∀ n : ℕ,
        (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2) =
          ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      intro n
      have h_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
      rw [ENNReal.ofReal_div_of_pos h_pos, ENNReal.ofReal_one,
        show ((n + 1 : ℕ) : ℝ) ^ 2 = (((n + 1)^2 : ℕ) : ℝ) by push_cast; ring,
        ENNReal.ofReal_natCast]
      push_cast; ring_nf
    rw [tsum_congr h_pointwise]
    exact h_ennreal_tsum
  -- First Borel–Cantelli: a.s. `ω ∉ B n` eventually.
  have h_BC := MeasureTheory.ae_eventually_notMem h_tsum
  filter_upwards [h_BC] with ω hx
  filter_upwards [hx] with n hn
  -- `ω ∉ B n` is exactly the desired inequality.
  simp only [hB, Set.mem_setOf_eq, not_lt] at hn
  exact hn

/-- **LZ78 converse lower bound for the genuine greedy parser
(Cover–Thomas Theorem 13.5.3, lower-bound half), a.s. form**.

For a stationary ergodic source `p` the per-symbol length of the genuine
longest-prefix-match greedy LZ78 parse is, almost surely, asymptotically at
least the bit entropy rate:

```
entropyRate₂ μ p ≤ liminf_n (1/n) · lz78GreedyEncodingLength(X^n)   a.s.
```

This is the lower-bound (converse) half of LZ78 asymptotic optimality —
the harder direction (SMB liminf lower bound + arbitrary-prefix Kraft
inequality + finite-alphabet bookkeeping).

Units: the encoding length is a base-2 code length
(`lz78GreedyEncodingLength = c · bitLength c |α|`, `bitLength` uses
`Nat.log 2`), so the per-symbol rate `lz/n` is in bits, and the correct
RHS is the bit entropy rate `entropyRate₂ = entropyRate / Real.log 2`
(not the nat-unit `entropyRate`), exactly the unit-correction documented in
`ZivEntropyBridge.lean` ("Base-2 (bit) layer") and
`McMillanKraftBridge.lean` (converse target `blockLogAvg₂`).

The dependency shape (Barron reduction): the body is genuinely wired from two
bricks plus the bit SMB convergence,

* `shannon_mcmillan_breiman₂` (SMB in bits, sorryAx-free) — gives
  `Tendsto blockLogAvg₂ → entropyRate₂` a.s.;
* `blockLogAvg₂_minus_error_le_rate_ae` (G3, Barron a.s.-eventual lift) —
  gives `∀ᶠ n, blockLogAvg₂ n ω − err_n ≤ lz/n` a.s., with `err_n → 0`;

assembled by `Filter.liminf_le_liminf` between the lower sequence
`Low n = blockLogAvg₂ n ω − err_n` (which `→ entropyRate₂`, so
`liminf Low = entropyRate₂`) and `lz/n` (bounded above by
`lz78_rate_le_const`, hence cobounded below). The genuine converse
content (the Barron competitive-optimality lift) is in G3, which in turn
consumes the genuine combinatorial brick G2 (`lz78_block_kraft_poly`, the
polynomial `n`-block Kraft bound). G2's Part B counting lemma
(`lz78_phrase_count_fiber_card_le`) is now closed, so this converse is fully
`sorryAx`-free.

This statement is TRUE-as-framed against the bit target `entropyRate₂` (the
RHS is stated against `entropyRate₂` rather than the nat-unit `entropyRate`):
on a uniform i.i.d. source on A symbols the bit-rate limit
is `log₂ A = entropyRate / Real.log 2 = entropyRate₂` exactly, so the
converse `entropyRate₂ ≤ liminf` is the genuine LZ78 converse (e.g. A=2:
`entropyRate₂ = log₂ 2 = 1 ≤ liminf`, with equality in the limit); on the
degenerate `entropyRate = 0` boundary it reads `0 ≤ liminf` (`entropyRate₂ =
0`), again genuine. Signature takes only source data (`μ`, `p`), no
load-bearing hypothesis.

@audit:ok (FINAL completion audit 2026-06-21, commit `bd28e0e`, independent
subagent). Non-circular, non-bundled (signature `(μ, p)` +
`[IsProbabilityMeasure μ]` only), non-degenerate, sufficiency TRUE-as-framed:
the body genuinely wires SMB-in-bits (`Low n → entropyRate₂`) with the Barron
a.s.-eventual lift (`Low n ≤ lz/n` eventually, `err_n → 0` proven) via
`liminf_le_liminf`. `#print axioms = [propext, Classical.choice, Quot.sound]`
(sorryAx-free, machine-confirmed). -/
theorem lz78Greedy_converse_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      entropyRate₂ μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n ↦
            (lz78GreedyEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop := by
  set q := p.toStationaryProcess with hq
  -- The greedy bit-rate sequence and its eventual lower envelope.
  set rate : Ω → ℕ → ℝ :=
    fun ω n ↦ (lz78GreedyEncodingLength n (q.blockRV n ω) : ℝ) / (n : ℝ) with hrate
  set err : ℕ → ℝ :=
    fun n ↦ (2 * Real.log n + 2 * Real.log (n + 1)) / ((n : ℝ) * Real.log 2) with herr
  -- `err n → 0` (each `log n / n → 0`).
  have h_err_tend : Filter.Tendsto err Filter.atTop (𝓝 0) := by
    have hℓ2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlogn : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 0) := by
      have hR : Filter.Tendsto (fun x : ℝ ↦ Real.log x ^ 1 / (1 * x + 0))
          Filter.atTop (𝓝 0) := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
      simpa using hR.comp tendsto_natCast_atTop_atTop
    have hlogn1 : Filter.Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / (n : ℝ))
        Filter.atTop (𝓝 0) := by
      have hR : Filter.Tendsto (fun x : ℝ ↦ Real.log x ^ 1 / (1 * x + (-1)))
          Filter.atTop (𝓝 0) := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 (by norm_num)
      have hcomp := hR.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
      refine hcomp.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      simp only [Function.comp_apply, pow_one]
      rw [show (1 : ℝ) * ((n : ℝ) + 1) + (-1) = (n : ℝ) by ring]
    set g : ℕ → ℝ := fun n ↦
      (2 / Real.log 2) * (Real.log (n : ℝ) / (n : ℝ))
      + (2 / Real.log 2) * (Real.log ((n : ℝ) + 1) / (n : ℝ)) with hg
    have hg_tend : Filter.Tendsto g Filter.atTop (𝓝 0) := by
      have t1 := hlogn.const_mul (2 / Real.log 2)
      have t2 := hlogn1.const_mul (2 / Real.log 2)
      simpa [hg] using t1.add t2
    refine hg_tend.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [hg, herr]
    field_simp
  filter_upwards [shannon_mcmillan_breiman₂ μ p,
      blockLogAvg₂_minus_error_le_rate_ae μ p] with ω h_smb h_lift
  -- The lower sequence `Low n = blockLogAvg₂ n ω − err n` tends to `entropyRate₂`.
  set Low : ℕ → ℝ := fun n ↦ blockLogAvg₂ μ q n ω - err n with hLow
  have h_Low_tend : Filter.Tendsto Low Filter.atTop
      (𝓝 (entropyRate₂ μ q)) := by
    have := h_smb.sub h_err_tend
    simpa only [hLow, hq, sub_zero] using this
  -- The rate `lz/n` is bounded above (deterministic constant), hence cobounded below.
  have h_rate_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (rate ω) :=
    Filter.isBoundedUnder_of
      ⟨(1 + 8 * Real.log (Fintype.card α + 1) / Real.log 2)
          + ((Nat.log 2 (Fintype.card α) : ℝ) + 2),
        fun n ↦ lz78_rate_le_const n _⟩
  -- `Low n ≤ rate ω n` eventually, from G3.
  have h_le : ∀ᶠ n in Filter.atTop, Low n ≤ rate ω n := by
    filter_upwards [h_lift] with n hn
    simpa only [hLow, hrate, hq] using hn
  -- Assemble via `liminf_le_liminf`, with `liminf Low = entropyRate₂`.
  have h_liminf_le : Filter.liminf Low Filter.atTop
      ≤ Filter.liminf (rate ω) Filter.atTop :=
    Filter.liminf_le_liminf h_le (hu := h_Low_tend.isBoundedUnder_ge)
      (hv := h_rate_bdd.isCoboundedUnder_ge)
  rw [h_Low_tend.liminf_eq] at h_liminf_le
  exact h_liminf_le

end ParentBridge

end InformationTheory.Shannon

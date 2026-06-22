import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ShannonCode.Basic
import InformationTheory.Shannon.ShannonCode.KraftReverse
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Logic.Equiv.Defs

/-!
# Arithmetic Coding / Shannon-Fano-Elias (Cover-Thomas Theorem 13.3.3)

For a finite-alphabet probability distribution `P` on `α`, the **arithmetic code**
assigns each symbol `a : α` a binary codeword of length `ℓ(a) = ⌈-log₂ P(a)⌉ + 1`,
achieving the expected-length sandwich `H₂(P) ≤ E[L] ≤ H₂(P) + 2` and prefix-freeness.

## Main definitions

* `sfeLength` — Shannon-Fano-Elias codeword length `⌈-log₂ P(a)⌉ + 1`.

## Main statements

* `sfeLength_kraft_le_one` — `sfeLength` satisfies the Kraft inequality.
* `arithmeticCode_expected_length_bounds` — `H₂(P) ≤ E[L] ≤ H₂(P) + 2`.
* `arithmeticCode_prefix_free` — existence of a length-`sfeLength`, injective,
  prefix-free binary code.
* `arithmeticCode_unique_decodable` — prefix-free ⟹ uniquely decodable.

## Implementation notes

The textbook construction truncates the binary expansion of the cumulative midpoint
`F̄(a) := F(a) - P(a)/2`; the real-valued binary expansion is a Mathlib gap and is
avoided entirely. The expected-length bounds use a length-only linear lift of the
Shannon-code machinery (`entropyD_le_expectedLength_of_kraft` /
`expectedLength_shannon_lt_entropyD_add_one`),
and the prefix-free code is obtained from `exists_prefix_code_of_kraft` (integer-slot
Kraft-reverse) lifted to `List Bool` via `finTwoEquiv`. The textbook midpoint-expansion
equivalence is out of scope — it gives the same code and is not needed for the bounds.
-/

namespace InformationTheory.Shannon.ArithmeticCoding

open MeasureTheory
open InformationTheory.Shannon.ShannonCode
  (entropyD expectedLength shannonLength kraftSum
   shannonLength_kraft_le_one entropyD_le_expectedLength_of_kraft
   expectedLength_shannon_lt_entropyD_add_one)
open InformationTheory.Shannon.ShannonCodeKraftReverse
  (exists_prefix_code_of_kraft IsPrefixFree)

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Shannon-Fano-Elias codeword length**: `ℓ(a) = ⌈-log₂ P(a)⌉ + 1`. -/
noncomputable def sfeLength (P : Measure α) (a : α) : ℕ := shannonLength 2 P a + 1

lemma sfeLength_pos (P : Measure α) (a : α) : 0 < sfeLength P a := by
  unfold sfeLength; exact Nat.succ_pos _

/-- **`sfeLength` satisfies the Kraft inequality** `Σ 2^(-ℓ(a)) ≤ 1`.

Each term halves the Shannon-length term: `2^(-(l+1)) = 2^(-l)/2`, so the whole
sum is `(1/2) · kraftSum 2 (shannonLength 2 P) ≤ 1/2 ≤ 1`. -/
lemma sfeLength_kraft_le_one
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a : α, 0 < P.real {a}) :
    kraftSum 2 (sfeLength P) ≤ 1 := by
  unfold kraftSum sfeLength
  -- Each term halves: `2^(-(l+1)) ≤ 2^(-l)`; summing gives `≤ kraftSum 2 (shannonLength 2 P) ≤ 1`.
  refine le_trans (Finset.sum_le_sum (fun a _ => ?_))
    (shannonLength_kraft_le_one (D := 2) (by norm_num) P hP)
  -- RHS is the unfolded form of `kraftSum 2 (shannonLength 2 P)`
  show (2 : ℝ) ^ (-((shannonLength 2 P a + 1 : ℕ) : ℤ))
      ≤ (2 : ℝ) ^ (-((shannonLength 2 P a : ℕ) : ℤ))
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  push_cast
  omega

/-- **Expected-length sandwich** (full discharge): `H₂(P) ≤ E[L] ≤ H₂(P) + 2`. -/
@[entry_point]
theorem arithmeticCode_expected_length_bounds
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a : α, 0 < P.real {a}) :
    entropyD 2 P ≤ expectedLength P (sfeLength P) ∧
      expectedLength P (sfeLength P) ≤ entropyD 2 P + 2 := by
  -- Linearity: `E[L_sfe] = E[L_shannon] + 1` via `∑ P(a) = 1`.
  have h_sum_one : (∑ a : α, P.real {a}) = (1 : ℝ) := by
    rw [show (∑ a : α, P.real {a})
          = ∑ a ∈ (Finset.univ : Finset α), P.real {a} from rfl,
        MeasureTheory.sum_measureReal_singleton (s := (Finset.univ : Finset α))]
    rw [show ((Finset.univ : Finset α) : Set α) = Set.univ from Finset.coe_univ]
    simp [measureReal_def, measure_univ]
  have h_lin : expectedLength P (sfeLength P)
      = expectedLength P (shannonLength 2 P) + 1 := by
    unfold expectedLength sfeLength
    rw [← h_sum_one, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · -- Lower bound: apply the Gibbs lower bound directly to `sfeLength`.
    exact entropyD_le_expectedLength_of_kraft (D := 2) (by norm_num) P hP
      (sfeLength P) (sfeLength_kraft_le_one P hP)
  · -- Upper bound: `E[L_sfe] = E[L_sh] + 1 < (H+1)+1 = H+2`.
    have h_up : expectedLength P (shannonLength 2 P) < entropyD 2 P + 1 :=
      expectedLength_shannon_lt_entropyD_add_one (D := 2) (by norm_num) P hP
    rw [h_lin]
    linarith

/-- **Prefix-free construction** (full discharge): there is a binary code of
length `sfeLength P` that is injective and prefix-free. -/
@[entry_point]
theorem arithmeticCode_prefix_free
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a : α, 0 < P.real {a}) :
    ∃ c : α → List Bool,
      (∀ a, (c a).length = sfeLength P a) ∧
      Function.Injective c ∧
      (∀ a b : α, a ≠ b → ¬ c a <+: c b) := by
  classical
  -- Bridge `sfeLength` Kraft inequality to the `hk` form required by `exists_prefix_code_of_kraft`.
  have hk : ∑ a : α, ((2 : ℕ) : ℝ) ^ (-(sfeLength P a : ℤ)) ≤ 1 := by
    have h := sfeLength_kraft_le_one P hP
    unfold kraftSum at h
    convert h using 2 with a
  -- Obtain `c₀ : α → List (Fin 2)` via the integer-slot construction.
  obtain ⟨c₀, hc₀_inj, hc₀_len, hc₀_pf⟩ :=
    exists_prefix_code_of_kraft (D := 2) (by norm_num) (sfeLength P)
      (sfeLength_pos P) hk
  -- Lift to `List Bool` via `finTwoEquiv`.
  refine ⟨fun a => (c₀ a).map ⇑finTwoEquiv, ?_, ?_, ?_⟩
  · intro a
    rw [List.length_map]
    exact hc₀_len a
  · -- injective: (map ⇑finTwoEquiv) ∘ c₀
    have hmap : Function.Injective (List.map (⇑finTwoEquiv)) :=
      Function.Injective.list_map finTwoEquiv.injective
    exact hmap.comp hc₀_inj
  · intro a b hab hpref
    -- Pull the prefix back through the map to `c₀` and derive a contradiction with prefix-freeness.
    rw [List.prefix_map_iff_of_injective finTwoEquiv.injective] at hpref
    exact hc₀_pf a b hab hpref

private lemma uncons_eq_of_flatten_eq
    {c : α → List Bool}
    (h_pf : ∀ a b : α, a ≠ b → ¬ c a <+: c b)
    {a b : α} {r₁ r₂ : List Bool}
    (h : c a ++ r₁ = c b ++ r₂) :
    a = b ∧ r₁ = r₂ := by
  -- Both `c a` and `c b` are prefixes of the common list `c a ++ r₁`, so comparable by length.
  have hpa : c a <+: c a ++ r₁ := List.prefix_append _ _
  have hpb : c b <+: c a ++ r₁ := h ▸ List.prefix_append _ _
  have hab : a = b := by
    by_contra hne
    rcases le_total (c a).length (c b).length with hle | hle
    · exact h_pf a b hne (List.prefix_of_prefix_length_le hpa hpb hle)
    · exact h_pf b a (Ne.symm hne) (List.prefix_of_prefix_length_le hpb hpa hle)
  subst hab
  exact ⟨rfl, List.append_cancel_left h⟩

/-- **Unique decodability** (Cover-Thomas 5.2.2): for a prefix-free code with
nonempty codewords, the map `s ↦ (s.map c).flatten` is injective. Proved by
induction, peeling one block at a time via `uncons_eq_of_flatten_eq`. -/
@[entry_point]
theorem arithmeticCode_unique_decodable
    (c : α → List Bool)
    (h_pf : ∀ a b : α, a ≠ b → ¬ c a <+: c b)
    (h_ne : ∀ a : α, c a ≠ []) :
    ∀ (s₁ s₂ : List α),
      (s₁.map c).flatten = (s₂.map c).flatten → s₁ = s₂ := by
  intro s₁
  induction s₁ with
  | nil =>
    intro s₂ h
    -- LHS = []; nonempty codewords force s₂ = [] as well.
    cases s₂ with
    | nil => rfl
    | cons b t =>
      simp only [List.map_cons, List.map_nil, List.flatten_nil, List.flatten_cons] at h
      exact absurd (List.append_eq_nil_iff.mp h.symm).1 (h_ne b)
  | cons a s ih =>
    intro s₂ h
    cases s₂ with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.flatten_nil, List.flatten_cons] at h
      exact absurd (List.append_eq_nil_iff.mp h).1 (h_ne a)
    | cons b t =>
      simp only [List.map_cons, List.flatten_cons] at h
      obtain ⟨hab, hrest⟩ := uncons_eq_of_flatten_eq h_pf h
      subst hab
      rw [ih t hrest]

end InformationTheory.Shannon.ArithmeticCoding

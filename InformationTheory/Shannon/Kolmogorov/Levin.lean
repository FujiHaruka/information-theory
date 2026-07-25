import Mathlib.Analysis.SpecialFunctions.Log.Base
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Kolmogorov.UniversalProbability

/-!
# Prefix complexity and universal probability: the factor-two relation

The self-delimiting machine `prefixUniversalEval` accepts a program only when its
unary length prefix matches the length of its payload, so every accepted program
is `selfDelimit d` for its payload `d`, of length `2 * d.length + 1`. Prefix
complexity is therefore rigidly tied to the shortest payload length
`payloadComplexity x` by `prefixComplexity x = 2 * payloadComplexity x + 1`, and
the two-sided relation between `prefixComplexity` and `universalProb` carries
that same factor of two:

  `-log₂ P_U(x) ≤ K(x) ≤ 2 * (-log₂ P_U(x)) + 1`.

The left inequality is `neg_logb_universalProb_le_prefixComplexity`; the right one
is `prefixComplexity_le_two_mul_neg_logb_universalProb`, proved here by counting.
The programs producing `x` inject into the payloads of length at least
`payloadComplexity x`, and re-wrapping such a payload with a unary prefix shortened
by `payloadComplexity x` (the map `padDelimit`) exhibits the weight
`2^{-(2|d|+1)}` as `2^{-payloadComplexity x}` times a Kraft-summable weight over a
prefix-free set.

## Main definitions

* `payloadComplexity` — the length of the shortest payload describing `x`.
* `padDelimit` — the unary length-prefix wrapper with the run of `true`s
  shortened by a fixed offset.

## Main results

* `prefixComplexity_eq_two_mul_payloadComplexity_add_one` — the structural
  identity `K(x) = 2 * m(x) + 1` for the shortest payload length `m(x)`.
* `universalProb_le_two_pow_neg_payloadComplexity` — the counting bound
  `P_U(x) ≤ 2^{-m(x)}`.
* `prefixComplexity_le_two_mul_neg_logb_universalProb` — the upper half of the
  factor-two relation, `K(x) ≤ 2 * (-log₂ P_U(x)) + 1`.

## Implementation notes

The factor two is a property of this machine rather than an artifact of the
argument: it is forced by the shape of the accepted programs, since a payload of
length `n` can only be presented as a program of length `2 * n + 1`. The additive
coding theorem `K(x) = -log₂ P_U(x) + O(1)` is a statement about additively
universal prefix machines — those able to simulate any other prefix machine at a
cost bounded by a constant — and is not claimed here.

The offset wrapper `padDelimit m` is deliberately not a program of the machine
for `m ≠ 0`: its unary prefix undercounts its payload, so the acceptance guard
rejects it. Only prefix-freeness of its image is needed, which is why the Kraft
bound is used in the form `PrefixFree.tsum_inv_two_pow_length_le_one`, stated for
an arbitrary prefix-free set rather than for the machine's domain.

## References

The universal probability and its relation to prefix complexity follow
Cover–Thomas (2nd ed.) §14.6.

## Tags

Kolmogorov complexity, prefix complexity, universal probability, coding theorem
-/

open scoped ENNReal

namespace InformationTheory.Kolmogorov

open Computability (encodeNat decodeNat)

/-- The payload complexity of `x`: the length of the shortest payload `d` that
decodes to `x`. Every accepted program of `prefixUniversalEval` is `selfDelimit`
of its payload, so this is the complexity measure the machine actually minimizes,
up to the self-delimiting overhead. -/
noncomputable def payloadComplexity (x : ℕ) : ℕ :=
  sInf { l | ∃ d : List Bool, d.length = l ∧ x ∈ decodePayload d }

/-- The self-delimiting wrapper with its unary run of `true`s shortened by the
offset `m`: `replicate (d.length - m) true ++ false :: d`. For `m ≤ d.length` the
images over all payloads still form a prefix-free set, while each codeword is
shorter than `selfDelimit d` by exactly `m`. -/
def padDelimit (m : ℕ) (d : List Bool) : List Bool :=
  List.replicate (d.length - m) true ++ false :: d

theorem prefixUniversalEval_selfDelimit (d : List Bool) :
    prefixUniversalEval (selfDelimit d) = decodePayload d := by
  rw [prefixUniversalEval, parseUnary_selfDelimit]
  simp

theorem selfDelimit_parseUnary_snd_of_mem {x : ℕ} {p : List Bool}
    (h : x ∈ prefixUniversalEval p) : selfDelimit (parseUnary p).2 = p := by
  obtain ⟨d, hd⟩ := dom_imp_mem_range (Part.dom_iff_mem.mpr ⟨x, h⟩)
  rw [← hd, parseUnary_selfDelimit]

theorem payloadComplexity_set_nonempty (x : ℕ) :
    { l | ∃ d : List Bool, d.length = l ∧ x ∈ decodePayload d }.Nonempty :=
  ⟨(false :: encodeNat x).length, false :: encodeNat x, rfl, by simp [decodePayload]⟩

theorem payloadComplexity_spec (x : ℕ) :
    ∃ d : List Bool, d.length = payloadComplexity x ∧ x ∈ decodePayload d :=
  Nat.sInf_mem (payloadComplexity_set_nonempty x)

theorem payloadComplexity_le_of_mem {x : ℕ} {d : List Bool} (h : x ∈ decodePayload d) :
    payloadComplexity x ≤ d.length :=
  Nat.sInf_le ⟨d, rfl, h⟩

theorem prefixComplexity_eq_two_mul_payloadComplexity_add_one (x : ℕ) :
    prefixComplexity x = 2 * payloadComplexity x + 1 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨d, hlen, hmem⟩ := payloadComplexity_spec x
    have hmem' : (selfDelimit d).length ∈
        { l | ∃ p : List Bool, p.length = l ∧ x ∈ prefixUniversalEval p } :=
      ⟨selfDelimit d, rfl, by rw [prefixUniversalEval_selfDelimit]; exact hmem⟩
    have hle : prefixComplexity x ≤ (selfDelimit d).length := Nat.sInf_le hmem'
    rw [selfDelimit_length, hlen] at hle
    exact hle
  · obtain ⟨p, hlen, hmem⟩ := prefixComplexity_spec x
    obtain ⟨d₀, rfl⟩ := dom_imp_mem_range (Part.dom_iff_mem.mpr ⟨x, hmem⟩)
    have hle : payloadComplexity x ≤ d₀.length :=
      payloadComplexity_le_of_mem (by rwa [prefixUniversalEval_selfDelimit] at hmem)
    rw [selfDelimit_length] at hlen
    omega

theorem parseUnary_padDelimit (m : ℕ) (d : List Bool) :
    parseUnary (padDelimit m d) = (d.length - m, d) := by
  rw [padDelimit]
  exact parseUnary_replicate (d.length - m) d

theorem padDelimit_length {m : ℕ} {d : List Bool} (h : m ≤ d.length) :
    (padDelimit m d).length = 2 * d.length + 1 - m := by
  simp only [padDelimit, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem padDelimit_injective (m : ℕ) : Function.Injective (padDelimit m) := by
  intro d₁ d₂ h
  have h1 : parseUnary (padDelimit m d₁) = parseUnary (padDelimit m d₂) := by rw [h]
  rw [parseUnary_padDelimit, parseUnary_padDelimit, Prod.mk.injEq] at h1
  exact h1.2

theorem padDelimit_image_prefixFree (m : ℕ) :
    PrefixFree (padDelimit m '' {d : List Bool | m ≤ d.length}) := by
  rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩ hab
  simp only [Set.mem_setOf_eq] at hs ht
  obtain ⟨w, hw⟩ := hab
  have h1 : parseUnary (padDelimit m s ++ w) = (s.length - m, s ++ w) := by
    have hass : padDelimit m s ++ w
        = List.replicate (s.length - m) true ++ false :: (s ++ w) := by
      simp [padDelimit, List.append_assoc]
    rw [hass, parseUnary_replicate]
  rw [hw, parseUnary_padDelimit, Prod.mk.injEq] at h1
  obtain ⟨hlen, hst⟩ := h1
  have hw0 : w = [] := by
    have h2 : t.length = s.length + w.length := by rw [hst, List.length_append]
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hw0
  rw [List.append_nil] at hst
  rw [hst]

theorem nil_not_mem_padDelimit_image (m : ℕ) :
    [] ∉ padDelimit m '' {d : List Bool | m ≤ d.length} := by
  rintro ⟨d, -, hd⟩
  simp [padDelimit] at hd

theorem tsum_inv_two_pow_padDelimit_length_le_one (m : ℕ) :
    ∑' d : { d : List Bool // m ≤ d.length },
        (2 : ℝ≥0∞)⁻¹ ^ (padDelimit m (d : List Bool)).length ≤ 1 := by
  have hmem : ∀ d : { d : List Bool // m ≤ d.length },
      padDelimit m (d : List Bool) ∈ padDelimit m '' {d : List Bool | m ≤ d.length} :=
    fun d ↦ ⟨d, d.2, rfl⟩
  have hinj : Function.Injective fun d : { d : List Bool // m ≤ d.length } ↦
      (⟨padDelimit m (d : List Bool), hmem d⟩ :
        { q : List Bool // q ∈ padDelimit m '' {d : List Bool | m ≤ d.length} }) :=
    fun a b hab ↦ Subtype.ext (padDelimit_injective m (Subtype.ext_iff.mp hab))
  refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective hinj
    fun q ↦ (2 : ℝ≥0∞)⁻¹ ^ (q : List Bool).length) ?_
  exact (padDelimit_image_prefixFree m).tsum_inv_two_pow_length_le_one
    (nil_not_mem_padDelimit_image m)

theorem universalProb_le_two_pow_neg_payloadComplexity (x : ℕ) :
    universalProb x ≤ (2 : ℝ≥0∞)⁻¹ ^ payloadComplexity x := by
  have hA : ∀ p : { p : List Bool // x ∈ prefixUniversalEval p },
      payloadComplexity x ≤ (parseUnary (p : List Bool)).2.length := fun p ↦
    payloadComplexity_le_of_mem (by
      rw [← prefixUniversalEval_selfDelimit, selfDelimit_parseUnary_snd_of_mem p.2]; exact p.2)
  have hB : ∀ p : { p : List Bool // x ∈ prefixUniversalEval p },
      (p : List Bool).length = 2 * (parseUnary (p : List Bool)).2.length + 1 := by
    intro p
    have h := selfDelimit_length (parseUnary (p : List Bool)).2
    rw [selfDelimit_parseUnary_snd_of_mem p.2] at h
    exact h
  have hinj : Function.Injective fun p : { p : List Bool // x ∈ prefixUniversalEval p } ↦
      (⟨(parseUnary (p : List Bool)).2, hA p⟩ :
        { d : List Bool // payloadComplexity x ≤ d.length }) := by
    intro a b hab
    have h1 : (parseUnary (a : List Bool)).2 = (parseUnary (b : List Bool)).2 :=
      Subtype.ext_iff.mp hab
    refine Subtype.ext ?_
    rw [← selfDelimit_parseUnary_snd_of_mem a.2, ← selfDelimit_parseUnary_snd_of_mem b.2, h1]
  calc universalProb x
      = ∑' p : { p : List Bool // x ∈ prefixUniversalEval p },
          (2 : ℝ≥0∞)⁻¹ ^ (2 * (parseUnary (p : List Bool)).2.length + 1) := by
        rw [universalProb]
        exact tsum_congr fun p ↦ by rw [hB p]
    _ ≤ ∑' d : { d : List Bool // payloadComplexity x ≤ d.length },
          (2 : ℝ≥0∞)⁻¹ ^ (2 * (d : List Bool).length + 1) :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj
          fun d ↦ (2 : ℝ≥0∞)⁻¹ ^ (2 * (d : List Bool).length + 1)
    _ = (2 : ℝ≥0∞)⁻¹ ^ payloadComplexity x *
          ∑' d : { d : List Bool // payloadComplexity x ≤ d.length },
            (2 : ℝ≥0∞)⁻¹ ^ (padDelimit (payloadComplexity x) (d : List Bool)).length := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun d ↦ ?_
        rw [padDelimit_length d.2, ← pow_add]
        congr 1
        omega
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ payloadComplexity x * 1 :=
        mul_le_mul_right (tsum_inv_two_pow_padDelimit_length_le_one _) _
    _ = (2 : ℝ≥0∞)⁻¹ ^ payloadComplexity x := mul_one _

/-- The upper half of the factor-two relation between prefix complexity and
universal probability: `K(x) ≤ 2 * (-log₂ P_U(x)) + 1`. Together with
`neg_logb_universalProb_le_prefixComplexity` this places `K(x)` between
`-log₂ P_U(x)` and twice that value plus one. -/
@[entry_point]
theorem prefixComplexity_le_two_mul_neg_logb_universalProb (x : ℕ) :
    (prefixComplexity x : ℝ) ≤ 2 * (-Real.logb 2 (universalProb x).toReal) + 1 := by
  have hne : universalProb x ≠ ⊤ := ((universalProb_le_one x).trans_lt ENNReal.one_lt_top).ne
  have hlow : ((2 : ℝ)⁻¹) ^ prefixComplexity x ≤ (universalProb x).toReal := by
    simpa [ENNReal.toReal_pow] using
      ENNReal.toReal_mono hne (universalProb_ge_two_pow_neg_prefixComplexity x)
  have hpos : (0 : ℝ) < (universalProb x).toReal := lt_of_lt_of_le (by positivity) hlow
  have hupper : (universalProb x).toReal ≤ ((2 : ℝ)⁻¹) ^ payloadComplexity x := by
    simpa [ENNReal.toReal_pow] using
      ENNReal.toReal_mono (by simp) (universalProb_le_two_pow_neg_payloadComplexity x)
  have hmono := Real.logb_le_logb_of_le (b := 2) one_lt_two hpos hupper
  rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one one_lt_two] at hmono
  rw [prefixComplexity_eq_two_mul_payloadComplexity_add_one]
  push_cast
  linarith

end InformationTheory.Kolmogorov

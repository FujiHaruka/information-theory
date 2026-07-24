import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Encoding
import Mathlib.InformationTheory.Coding.KraftMcMillan
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import InformationTheory.Shannon.Kolmogorov.UniversalMachine

/-!
# A self-delimiting (prefix-free) universal machine for prefix complexity

The plain universal machine `universalEval` is not self-delimiting: the echo
program `false :: encodeNat x` is prefix-closed, so its valid-program set is not
prefix-free and the Kraft-McMillan inequality does not apply. This file builds a
separate machine `prefixUniversalEval` whose valid-program set is prefix-free.

Every valid program has the shape `selfDelimit bs = replicate |bs| true ++ false :: bs`
(a unary length prefix followed by the payload). The machine reads the unary
prefix with `parseUnary`, accepts only when the recovered length matches the
payload length (full self-delimited consumption), and then decodes the payload
in the same two modes as the plain machine (literal echo / interpret). Because
the accepted set is contained in the prefix-free image of `selfDelimit`, the
Kraft-McMillan inequality applies to each of its finite subsets.

## Main definitions

* `PrefixFree` — a set of bit-string codewords is prefix-free.
* `selfDelimit` — the unary length-prefix self-delimiting wrapper.
* `prefixUniversalEval` — the fixed self-delimiting universal machine.
* `prefixComplexity` — prefix Kolmogorov complexity `K(x)`.
* `universalProb` — the universal probability `P_U(x)` in `ℝ≥0∞`.

## Main results

* `PrefixFree.uniquelyDecodable` — prefix-free (with no empty codeword) implies
  uniquely decodable, bridging to `kraft_mcmillan_inequality`.
* `prefixUniversalEval_kraft` — every finite set of valid programs satisfies the
  Kraft bound `∑ 2^{-|p|} ≤ 1`.
-/

open scoped ENNReal

namespace InformationTheory.Kolmogorov

open Nat.Partrec Nat.Partrec.Code
open Computability (encodeNat decodeNat)
open InformationTheory (UniquelyDecodable)

/-- A set of bit-string codewords is prefix-free (self-delimiting): no codeword
is a prefix of a distinct codeword. -/
def PrefixFree (S : Set (List Bool)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a <+: b → a = b

theorem PrefixFree.mono {S S' : Set (List Bool)} (h : PrefixFree S) (hsub : S' ⊆ S) :
    PrefixFree S' := fun a ha b hb hab ↦ h a (hsub ha) b (hsub hb) hab

/-- Prefix-free codes with no empty codeword are uniquely decodable. Not in
Mathlib; bridges to `kraft_mcmillan_inequality`.
@audit:ok -/
theorem PrefixFree.uniquelyDecodable {S : Set (List Bool)} (h : PrefixFree S)
    (h0 : [] ∉ S) : UniquelyDecodable S := by
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ _ h2 hflat
    cases L₂ with
    | nil => rfl
    | cons w L₂' =>
      exfalso
      rw [List.flatten_nil, List.flatten_cons] at hflat
      have hw : w = [] := (List.append_eq_nil_iff.mp hflat.symm).1
      exact h0 (hw ▸ h2 w List.mem_cons_self)
  | cons w₁ L₁' ih =>
    intro L₂ h1 h2 hflat
    cases L₂ with
    | nil =>
      exfalso
      rw [List.flatten_cons, List.flatten_nil] at hflat
      have hw : w₁ = [] := (List.append_eq_nil_iff.mp hflat).1
      exact h0 (hw ▸ h1 w₁ List.mem_cons_self)
    | cons w₂ L₂' =>
      rw [List.flatten_cons, List.flatten_cons] at hflat
      have hw₁S : w₁ ∈ S := h1 w₁ List.mem_cons_self
      have hw₂S : w₂ ∈ S := h2 w₂ List.mem_cons_self
      have hp₁ : w₁ <+: w₁ ++ L₁'.flatten := ⟨L₁'.flatten, rfl⟩
      have hp₂ : w₂ <+: w₁ ++ L₁'.flatten := ⟨L₂'.flatten, hflat.symm⟩
      have heq : w₁ = w₂ := by
        rcases le_total w₁.length w₂.length with hle | hle
        · exact h w₁ hw₁S w₂ hw₂S (List.prefix_of_prefix_length_le hp₁ hp₂ hle)
        · exact (h w₂ hw₂S w₁ hw₁S (List.prefix_of_prefix_length_le hp₂ hp₁ hle)).symm
      subst heq
      have hrest : L₁'.flatten = L₂'.flatten := List.append_cancel_left hflat
      rw [ih L₂' (fun w hw ↦ h1 w (List.mem_cons_of_mem _ hw))
        (fun w hw ↦ h2 w (List.mem_cons_of_mem _ hw)) hrest]

theorem uniquelyDecodable_mono {S S' : Set (List Bool)} (h : UniquelyDecodable S)
    (hsub : S' ⊆ S) : UniquelyDecodable S' :=
  fun L₁ L₂ h1 h2 hflat ↦
    h L₁ L₂ (fun w hw ↦ hsub (h1 w hw)) (fun w hw ↦ hsub (h2 w hw)) hflat

/-- The unary length-prefix self-delimiting wrapper: `bs.length` in unary
(a run of `true`s terminated by `false`) followed by the payload `bs`. Its image
over all payloads is prefix-free. -/
def selfDelimit (bs : List Bool) : List Bool :=
  List.replicate bs.length true ++ false :: bs

theorem parseUnary_snd_eq_nil_of_not_mem {p : List Bool} (h : false ∉ p) :
    (parseUnary p).2 = [] := by
  induction p with
  | nil => rfl
  | cons a rest ih =>
    cases a with
    | false => exact absurd List.mem_cons_self h
    | true => exact ih fun hm ↦ h (List.mem_cons_of_mem _ hm)

theorem parseUnary_reconstruct {p : List Bool} (h : false ∈ p) :
    p = List.replicate (parseUnary p).1 true ++ false :: (parseUnary p).2 := by
  induction p with
  | nil => exact absurd h List.not_mem_nil
  | cons a rest ih =>
    cases a with
    | false => simp [parseUnary]
    | true =>
      have hr : false ∈ rest := by
        rcases List.mem_cons.mp h with he | hm
        · exact absurd he (by decide)
        · exact hm
      simp only [parseUnary, List.replicate_succ, List.cons_append]
      rw [← ih hr]

theorem parseUnary_selfDelimit (bs : List Bool) :
    parseUnary (selfDelimit bs) = (bs.length, bs) := by
  simp only [selfDelimit]
  exact parseUnary_replicate bs.length bs

theorem range_selfDelimit_prefixFree : PrefixFree (Set.range selfDelimit) := by
  rintro a ⟨s, rfl⟩ b ⟨t, rfl⟩ hab
  obtain ⟨w, hw⟩ := hab
  have h1 : parseUnary (selfDelimit s ++ w) = (s.length, s ++ w) := by
    have hass : selfDelimit s ++ w = List.replicate s.length true ++ false :: (s ++ w) := by
      simp [selfDelimit, List.append_assoc]
    rw [hass, parseUnary_replicate]
  rw [hw, parseUnary_selfDelimit, Prod.mk.injEq] at h1
  obtain ⟨hlen, hst⟩ := h1
  have hw0 : w = [] := by
    have h2 : t.length = s.length + w.length := by rw [hst, List.length_append]
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hw0
  rw [List.append_nil] at hst
  rw [hst]

/-- Decode a self-delimited payload. `false :: bs` echoes `decodeNat bs`;
`true :: bs` interprets `bs` as a code index (unary) plus a description,
delegating to Mathlib's universal interpreter `eval`. -/
noncomputable def decodePayload : List Bool → Part ℕ
  | [] => Part.none
  | (false :: bs) => Part.some (decodeNat bs)
  | (true :: bs) =>
      eval (Denumerable.ofNat Code (parseUnary bs).1)
        (Nat.pair (decodeNat (parseUnary bs).2) 0)

/-- The fixed self-delimiting universal machine. A program is accepted only if
its unary length prefix matches the payload length (so its domain lies in the
prefix-free image of `selfDelimit`), then the payload is decoded. -/
noncomputable def prefixUniversalEval (p : List Bool) : Part ℕ :=
  if (parseUnary p).1 = (parseUnary p).2.length then decodePayload (parseUnary p).2
  else Part.none

theorem decodePayload_dom_ne_nil {q : List Bool} (h : (decodePayload q).Dom) :
    q ≠ [] := by
  rintro rfl
  simp [decodePayload] at h

theorem prefixUniversalEval_nil_not_dom : ¬ (prefixUniversalEval []).Dom := by
  intro h
  simp [prefixUniversalEval, parseUnary, decodePayload] at h

theorem dom_imp_mem_range {p : List Bool} (h : (prefixUniversalEval p).Dom) :
    p ∈ Set.range selfDelimit := by
  by_cases hg : (parseUnary p).1 = (parseUnary p).2.length
  · have hd : (decodePayload (parseUnary p).2).Dom := by
      rw [prefixUniversalEval, if_pos hg] at h; exact h
    have hq : (parseUnary p).2 ≠ [] := decodePayload_dom_ne_nil hd
    have hfalse : false ∈ p := by
      by_contra hc
      exact hq (parseUnary_snd_eq_nil_of_not_mem hc)
    refine ⟨(parseUnary p).2, ?_⟩
    rw [selfDelimit, ← hg]
    exact (parseUnary_reconstruct hfalse).symm
  · exfalso
    rw [prefixUniversalEval, if_neg hg] at h
    exact h

theorem prefixUniversalEval_dom_prefixFree :
    PrefixFree {p | (prefixUniversalEval p).Dom} :=
  range_selfDelimit_prefixFree.mono fun _ hp ↦ dom_imp_mem_range hp

/-- The prefix echo program describing `x`: `x`'s binary payload wrapped by the
literal mode flag and the self-delimiting length prefix. -/
def prefixLiteralProg (x : ℕ) : List Bool := selfDelimit (false :: encodeNat x)

theorem prefixUniversalEval_literal (x : ℕ) :
    prefixUniversalEval (prefixLiteralProg x) = Part.some x := by
  rw [prefixLiteralProg, prefixUniversalEval, parseUnary_selfDelimit]
  simp [decodePayload, Computability.decode_encodeNat]

/-- Every finite set of valid programs of the self-delimiting machine satisfies
the Kraft-McMillan bound `∑ 2^{-|p|} ≤ 1`.
@audit:ok -/
theorem prefixUniversalEval_kraft (u : Finset (List Bool))
    (hu : ∀ p ∈ u, (prefixUniversalEval p).Dom) :
    ∑ p ∈ u, (1 / 2 : ℝ) ^ p.length ≤ 1 := by
  have hsub : (↑u : Set (List Bool)) ⊆ {p | (prefixUniversalEval p).Dom} :=
    fun p hp ↦ hu p (Finset.mem_coe.mp hp)
  have hUD_dom : UniquelyDecodable {p | (prefixUniversalEval p).Dom} :=
    prefixUniversalEval_dom_prefixFree.uniquelyDecodable prefixUniversalEval_nil_not_dom
  have hUD_u : UniquelyDecodable (↑u : Set (List Bool)) := uniquelyDecodable_mono hUD_dom hsub
  have hk := kraft_mcmillan_inequality (α := Bool) (S := u) hUD_u
  simpa [Fintype.card_bool] using hk

/-- Prefix Kolmogorov complexity `K(x)`: the length of the shortest
self-delimiting program producing `x`. The literal echo makes the set nonempty,
so this infimum is attained (`prefixComplexity_spec`). -/
noncomputable def prefixComplexity (x : ℕ) : ℕ :=
  sInf { l | ∃ p : List Bool, p.length = l ∧ x ∈ prefixUniversalEval p }

theorem prefixComplexity_set_nonempty (x : ℕ) :
    { l | ∃ p : List Bool, p.length = l ∧ x ∈ prefixUniversalEval p }.Nonempty :=
  ⟨(prefixLiteralProg x).length, prefixLiteralProg x, rfl, by
    rw [prefixUniversalEval_literal]; exact Part.mem_some x⟩

theorem prefixComplexity_spec (x : ℕ) :
    ∃ p : List Bool, p.length = prefixComplexity x ∧ x ∈ prefixUniversalEval p :=
  Nat.sInf_mem (prefixComplexity_set_nonempty x)

/-- Universal probability `P_U(x) = ∑_{p : U_prefix p = x} 2^{-|p|}` in `ℝ≥0∞`.
The `tsum` is always defined; `P_U(x) ≤ 1` follows from Kraft on finite subsets. -/
noncomputable def universalProb (x : ℕ) : ℝ≥0∞ :=
  ∑' p : { p : List Bool // x ∈ prefixUniversalEval p }, (2 : ℝ≥0∞)⁻¹ ^ (p : List Bool).length

end InformationTheory.Kolmogorov

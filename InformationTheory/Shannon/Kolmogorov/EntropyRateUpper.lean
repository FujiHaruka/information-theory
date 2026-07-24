import InformationTheory.Shannon.Kolmogorov.Invariance
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.List

/-!
# A partial recursive type-class decoder for the entropy-rate upper bound

The method-of-types upper half of `kolmogorov_entropy_rate` encodes a length-`n`
block by the pair `⟨type descriptor, index in its type class⟩`. To turn this into
a `condComplexity` bound through `invariance`, the corresponding *decoder* — the map
that recovers a block from such a pair — must be a single partial recursive function,
uniform in the block length `n` (a per-`n` code would make the additive constant of
`invariance_code` diverge with `n`).

This file builds that decoder over a finite alphabet `α` and certifies it as
`Partrec₂`. The decoder `A(m, n)` unpairs `m` into a type descriptor `cCode` and an
index `i`, enumerates every length-`n` word (represented as a value-level `List α`,
not the length-indexed `Fin n → α`), keeps those whose occurrence signature equals the
one decoded from `cCode`, and returns the `i`-th such word encoded back to `ℕ`.

## Main definitions

* `typeDecoder` — the decoder as a function `ℕ → ℕ → Part ℕ`.
* `enumWords` / `typeSig` — the length-`n` word enumerator and the occurrence signature.

## Main results

* `typeDecoder_partrec` — `typeDecoder` is `Partrec₂`.
-/

namespace InformationTheory.Kolmogorov

section Decoder

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A `Primcodable` structure on the finite type `α`, derived locally from
`α ≃ Fin (Fintype.card α)`. This keeps the certification unconditional: no ambient
`[Primcodable α]` hypothesis is threaded through the entropy-rate development. -/
noncomputable local instance primcodableOfFintype : Primcodable α :=
  Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.equivFin α)

/-- The canonical letter list of the finite alphabet; a constant, independent of the
block length `n`. -/
noncomputable def decoderAlphabet : List α := (Finset.univ : Finset α).toList

/-- All length-`n` words over `α`, listed in canonical order. Built by primitive
recursion: `enumWords 0 = [[]]` and each step prepends every letter. -/
noncomputable def enumWords (n : ℕ) : List (List α) :=
  n.rec [[]] fun _ prev ↦ prev.flatMap fun w ↦ (decoderAlphabet : List α).map fun a ↦ a :: w

/-- The occurrence signature of a word: for every letter `a` (in canonical order), the
number of times `a` appears in `w`. Two words lie in the same type class iff their
signatures agree. -/
noncomputable def typeSig (w : List α) : List ℕ :=
  (decoderAlphabet : List α).map fun a ↦ (w.filter fun b ↦ b = a).length

/-- The decoder as an `Option`-valued total-computable map: `None` marks the index being
out of range of the enumerated type class. -/
noncomputable def typeDecoderOption (m n : ℕ) : Option ℕ :=
  (((enumWords (α := α) n).filter fun w ↦ typeSig w = Denumerable.ofNat (List ℕ) m.unpair.1
    )[m.unpair.2]?).map Encodable.encode

/-- The type-class decoder consumed by `invariance`: on input `(m, n)` it recovers the
`n`-block indexed inside its type class. -/
noncomputable def typeDecoder (m n : ℕ) : Part ℕ := (typeDecoderOption (α := α) m n : Part ℕ)

/-! ### Primitive-recursive certification of the pieces -/

omit [DecidableEq α] in
/-- The word enumerator is primitive recursive in the length. -/
theorem enumWords_primrec : Primrec (enumWords (α := α)) := by
  have hcons : Primrec₂ (fun (pw : (List (List α)) × (List α)) (letter : α) ↦ letter :: pw.2) :=
    Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
  have hmap : Primrec₂ (fun (prev : List (List α)) (w : List α) ↦
      (decoderAlphabet : List α).map fun a ↦ a :: w) :=
    Primrec.list_map (Primrec.const decoderAlphabet) hcons
  have hexpand : Primrec (fun prev : List (List α) ↦
      prev.flatMap fun w ↦ (decoderAlphabet : List α).map fun a ↦ a :: w) :=
    Primrec.list_flatMap Primrec.id hmap
  have hstep : Primrec₂ (fun (_ : ℕ) (prev : List (List α)) ↦
      prev.flatMap fun w ↦ (decoderAlphabet : List α).map fun a ↦ a :: w) :=
    hexpand.comp Primrec.snd
  exact Primrec.nat_rec₁ [[]] hstep

/-- The occurrence signature is primitive recursive. -/
theorem typeSig_primrec : Primrec (typeSig (α := α)) := by
  have hfilter : Primrec₂ (fun (L : List α) (b : α) ↦ L.filter fun a ↦ a = b) :=
    PrimrecRel.listFilter Primrec.eq
  have hoccLen : Primrec₂ (fun (w : List α) (a : α) ↦ (w.filter fun b ↦ b = a).length) :=
    Primrec.list_length.comp hfilter
  exact Primrec.list_map (Primrec.const decoderAlphabet) hoccLen

/-- The `Option`-valued decoder is total computable in `(m, n)`. -/
theorem typeDecoderOption_computable :
    Computable fun p : ℕ × ℕ ↦ typeDecoderOption (α := α) p.1 p.2 := by
  have hR : PrimrecRel (fun (w : List α) (s : List ℕ) ↦ typeSig w = s) :=
    PrimrecRel.comp Primrec.eq (typeSig_primrec.comp Primrec.fst) Primrec.snd
  have hunpair : Primrec (fun p : ℕ × ℕ ↦ Nat.unpair p.1) := Primrec.unpair.comp Primrec.fst
  have hcCode : Primrec (fun p : ℕ × ℕ ↦ (Nat.unpair p.1).1) := Primrec.fst.comp hunpair
  have hi : Primrec (fun p : ℕ × ℕ ↦ (Nat.unpair p.1).2) := Primrec.snd.comp hunpair
  have hsig : Primrec (fun p : ℕ × ℕ ↦ Denumerable.ofNat (List ℕ) (Nat.unpair p.1).1) :=
    (Primrec.ofNat (List ℕ)).comp hcCode
  have hwords : Primrec (fun p : ℕ × ℕ ↦ enumWords (α := α) p.2) :=
    enumWords_primrec.comp Primrec.snd
  have hfiltered : Primrec (fun p : ℕ × ℕ ↦ (enumWords (α := α) p.2).filter
      fun w ↦ typeSig w = Denumerable.ofNat (List ℕ) (Nat.unpair p.1).1) :=
    (PrimrecRel.listFilter hR).comp hwords hsig
  have hindexed : Primrec (fun p : ℕ × ℕ ↦ ((enumWords (α := α) p.2).filter
      fun w ↦ typeSig w = Denumerable.ofNat (List ℕ) (Nat.unpair p.1).1)[(Nat.unpair p.1).2]?) :=
    Primrec.list_getElem?.comp hfiltered hi
  have hresult : Primrec (fun p : ℕ × ℕ ↦ typeDecoderOption (α := α) p.1 p.2) :=
    Primrec.option_map hindexed (Primrec.encode.comp Primrec.snd)
  exact hresult.to_comp

/-- The type-class decoder is partial recursive. -/
theorem typeDecoder_partrec : Partrec₂ (typeDecoder (α := α)) :=
  Computable.ofOption typeDecoderOption_computable

end Decoder

end InformationTheory.Kolmogorov

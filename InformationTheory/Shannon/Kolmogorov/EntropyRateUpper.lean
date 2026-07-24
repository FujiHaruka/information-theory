import InformationTheory.Shannon.Kolmogorov.Invariance
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Nat.Digits.Defs

/-!
# A partial recursive type-class decoder for the entropy-rate upper bound

The method-of-types upper half of `kolmogorov_entropy_rate` encodes a length-`n`
block by the pair `⟨type descriptor, index in its type class⟩`. To turn this into
a `condComplexity` bound through `invariance`, the corresponding *decoder* — the map
that recovers a block from such a pair — must be a single partial recursive function,
uniform in the block length `n` (a per-`n` code would make the additive constant of
`invariance_code` diverge with `n`).

This file builds that decoder over a finite alphabet `α` and certifies it as
`Partrec₂`. The decoder `A(m, n)` splits `m` by division and remainder against
`K = (n + 1) ^ card α`: the type descriptor is the remainder `m % K` (the base-`(n + 1)`
numeral of the occurrence signature, whose letter counts each lie in `[0, n]`), and the
index is the quotient `m / K`. It enumerates every length-`n` word (a value-level
`List α`, not the length-indexed `Fin n → α`), keeps those whose signature re-encodes to
`m % K`, and returns the `m / K`-th such word as its base-`card α` numeral. This
`div`/`mod` packing is length-additive (`natLen m ≈ natLen index + card α · log (n + 1)`),
unlike `Nat.pair`, and the base-`card α` output matches the block encoder used by the
upper bound.

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
out of range of the enumerated type class. The modulus `K = (n + 1) ^ card α` bounds the
base-`(n + 1)` numeral of every length-`n` signature, so `m % K` recovers the type
descriptor and `m / K` the index inside the type class. -/
noncomputable def typeDecoderOption (m n : ℕ) : Option ℕ :=
  let K := (n + 1) ^ Fintype.card α
  (((enumWords (α := α) n).filter fun w ↦ Nat.ofDigits (n + 1) (typeSig w) = m % K)[m / K]?).map
    fun w ↦ Nat.ofDigits (Fintype.card α) (w.map fun a ↦ (Fintype.equivFin α a).val)

/-- The type-class decoder consumed by `invariance`: on input `(m, n)` it recovers the
`n`-block indexed inside its type class. -/
noncomputable def typeDecoder (m n : ℕ) : Part ℕ :=
  (typeDecoderOption (α := α) m n : Part ℕ)

/-! ### Primitive-recursive certification of the pieces -/

omit [DecidableEq α] in
/-- The word enumerator is primitive recursive in the length. -/
theorem enumWords_primrec : Primrec (enumWords (α := α)) := by
  have hcons : Primrec₂
      (fun (pw : (List (List α)) × (List α)) (letter : α) ↦ letter :: pw.2) :=
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

/-- Reading a list of digits in a variable base is primitive recursive in the base and
the digit list, via the `foldr` form of `Nat.ofDigits`. -/
theorem ofDigits_primrec : Primrec₂ (fun (b : ℕ) (L : List ℕ) ↦ Nat.ofDigits b L) := by
  have h : Primrec₂ (fun (a : ℕ × List ℕ) (p : ℕ × ℕ) ↦ p.1 + a.1 * p.2) :=
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))).to₂
  have hfold : Primrec (fun a : ℕ × List ℕ ↦ (a.2).foldr (fun x y ↦ x + a.1 * y) 0) :=
    Primrec.list_foldr Primrec.snd (Primrec.const 0) h
  have key : Primrec (fun a : ℕ × List ℕ ↦ Nat.ofDigits a.1 a.2) := by
    refine hfold.of_eq fun a ↦ ?_
    simp [Nat.ofDigits_eq_foldr]
  exact key.to₂

/-- The `Option`-valued decoder is total computable in `(m, n)`. -/
theorem typeDecoderOption_computable :
    Computable fun p : ℕ × ℕ ↦ typeDecoderOption (α := α) p.1 p.2 := by
  have nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
    Primrec₂.unpaired'.1 Nat.Primrec.pow
  -- `K = (n + 1) ^ card α`, the modulus separating index (quotient) from descriptor (remainder)
  have hbase : Primrec (fun p : ℕ × ℕ ↦ p.2 + 1) := Primrec.succ.comp Primrec.snd
  have hK : Primrec (fun p : ℕ × ℕ ↦ (p.2 + 1) ^ Fintype.card α) :=
    nat_pow.comp hbase (Primrec.const (Fintype.card α))
  have htypeCode : Primrec (fun p : ℕ × ℕ ↦ p.1 % (p.2 + 1) ^ Fintype.card α) :=
    Primrec.nat_mod.comp Primrec.fst hK
  have hindex : Primrec (fun p : ℕ × ℕ ↦ p.1 / (p.2 + 1) ^ Fintype.card α) :=
    Primrec.nat_div.comp Primrec.fst hK
  have hparams : Primrec (fun p : ℕ × ℕ ↦ (p.2 + 1, p.1 % (p.2 + 1) ^ Fintype.card α)) :=
    hbase.pair htypeCode
  -- Filter predicate: keep words whose base-`(n + 1)` signature numeral equals the descriptor.
  have hR : PrimrecRel
      (fun (w : List α) (params : ℕ × ℕ) ↦ Nat.ofDigits params.1 (typeSig w) = params.2) :=
    PrimrecRel.comp Primrec.eq
      (ofDigits_primrec.comp (Primrec.fst.comp Primrec.snd) (typeSig_primrec.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd)
  have hwords : Primrec (fun p : ℕ × ℕ ↦ enumWords (α := α) p.2) :=
    enumWords_primrec.comp Primrec.snd
  have hfiltered : Primrec (fun p : ℕ × ℕ ↦ (enumWords (α := α) p.2).filter
      fun w ↦ Nat.ofDigits (p.2 + 1) (typeSig w) = p.1 % (p.2 + 1) ^ Fintype.card α) :=
    (PrimrecRel.listFilter hR).comp hwords hparams
  have hindexed : Primrec (fun p : ℕ × ℕ ↦ ((enumWords (α := α) p.2).filter
      fun w ↦ Nat.ofDigits (p.2 + 1) (typeSig w) = p.1 % (p.2 + 1) ^ Fintype.card α
        )[p.1 / (p.2 + 1) ^ Fintype.card α]?) :=
    Primrec.list_getElem?.comp hfiltered hindex
  -- Output: the recovered word as its base-`card α` numeral (matching `encodeBlock`).
  have hmapval : Primrec (fun w : List α ↦ w.map fun a ↦ (Fintype.equivFin α a).val) :=
    Primrec.list_map Primrec.id (Primrec.encode.comp Primrec.snd)
  have houtput : Primrec₂ (fun (_ : ℕ × ℕ) (w : List α) ↦
      Nat.ofDigits (Fintype.card α) (w.map fun a ↦ (Fintype.equivFin α a).val)) :=
    (ofDigits_primrec.comp (Primrec.const (Fintype.card α)) (hmapval.comp Primrec.snd)).to₂
  have hresult : Primrec (fun p : ℕ × ℕ ↦ typeDecoderOption (α := α) p.1 p.2) :=
    Primrec.option_map hindexed houtput
  exact hresult.to_comp

/-- The type-class decoder is partial recursive. -/
theorem typeDecoder_partrec : Partrec₂ (typeDecoder (α := α)) :=
  Computable.ofOption typeDecoderOption_computable

end Decoder

end InformationTheory.Kolmogorov

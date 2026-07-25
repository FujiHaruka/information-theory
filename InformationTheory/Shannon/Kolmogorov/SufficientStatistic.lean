import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Equiv.List
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Kolmogorov.Levin

/-!
# Kolmogorov sufficient statistics and two-part descriptions

Cover–Thomas (2nd ed.) §14.12. A finite model `S ∋ x` describes `x` in two parts:
the model itself, and the index of `x` inside `S`. The model part is measured by
the prefix complexity `modelComplexity S` of a canonical code for `S`, and the
index part by `Nat.clog 2 S.card` bits.

## Main definitions

* `modelCode` / `modelComplexity` — the canonical code of a finite model and its
  prefix complexity.
* `twoPartLength` — the length of the two-part description built from a model.
* `mdlComplexity` — the shortest two-part description length of `x`.
* `structureFunction` — the least index part achievable within a model budget.
* `IsSufficientStatistic` — a model whose two-part description is within an
  additive constant of `prefixComplexity x`.

## Main results

* `prefixComplexity_le_twoPartLength` — every two-part description bounds the
  prefix complexity, up to an additive constant.
* `mdlComplexity_sub_prefixComplexity_le` — the shortest two-part description
  length and the prefix complexity agree up to an additive constant.

## Implementation notes

The index part of `twoPartLength` carries the coefficient `4`, not `1`, and the
two factors of two have different sources. One is a property of the machine
`prefixUniversalEval`: prefix complexity and payload complexity are rigidly tied
by the identity `prefixComplexity x = 2 * payloadComplexity x + 1`, so a bound
proved in the payload world doubles on the way back. The other is a property of
the packing used here, which delimits the index with `selfDelimit` and therefore
spends two bits per index bit. The textbook inequality
`K(x) ≤ K(S) + log |S| + O(1)`, with coefficient `1` on the index part, is a
statement about an additively universal prefix machine and is not claimed here;
the coefficient on the model part `modelComplexity S` is exactly `1` because both
sides pass through the same identity.

## References

Cover–Thomas (2nd ed.) §14.12.

## Tags

Kolmogorov complexity, sufficient statistic, minimum description length
-/

namespace InformationTheory.Kolmogorov

open Encodable Nat.Partrec Nat.Partrec.Code
open Computability (encodeNat decodeNat encodeNum decodeNum encodePosNum decodePosNum)

/-! ### Models and two-part descriptions -/

/-- The canonical code of a finite model: the `Encodable` code of its sorted
element list. Sorted lists are used rather than `Finset` itself because the
decoder that reads a model back has to be primitive recursive, and `List ℕ` is
`Primcodable` while `Finset ℕ` is not.
@audit:ok -/
noncomputable def modelCode (S : Finset ℕ) : ℕ := encode (S.sort (· ≤ ·))

/-- The description length of a finite model: the prefix complexity of its
canonical code. Using prefix complexity rather than the literal length of
`modelCode` keeps the quantity insensitive to the redundancy of the canonical
code.
@audit:ok -/
noncomputable def modelComplexity (S : Finset ℕ) : ℕ := prefixComplexity (modelCode S)

/-- The length of the two-part description built from the model `S`: the model
part plus the index part. The coefficient `4` on the index part is built into the
definition rather than recovered by the argument (see the implementation notes);
the coefficient on the model part is exactly `1`.
@audit:ok -/
noncomputable def twoPartLength (S : Finset ℕ) : ℕ :=
  modelComplexity S + 4 * Nat.clog 2 S.card

/-- The shortest two-part description length of `x`, minimized over all finite
models containing `x`. The singleton model always competes, so the infimum is
attained (`mdlComplexity_spec`).
@audit:ok -/
noncomputable def mdlComplexity (x : ℕ) : ℕ :=
  sInf { l | ∃ S : Finset ℕ, x ∈ S ∧ twoPartLength S = l }

/-- The structure function of `x`: the least index part `⌈log₂ |S|⌉` over models
`S ∋ x` whose description length is within the budget `k`. The value is `ℕ∞`
because the constraint set is empty for small budgets, where the value has to be
`⊤` rather than `0` (`structureFunction_zero`); over `ℕ` the empty infimum would
collapse to `0` and contradict `structureFunction_antitone`.
@audit:ok -/
noncomputable def structureFunction (x k : ℕ) : ℕ∞ :=
  sInf { l | ∃ S : Finset ℕ,
    x ∈ S ∧ modelComplexity S ≤ k ∧ (Nat.clog 2 S.card : ℕ∞) = l }

/-- A model `S` is a sufficient statistic for `x` at slack `c` when it contains
`x` and its two-part description is no longer than `prefixComplexity x + c`. The
slack is an explicit argument so that minimality statements can quantify over it.
@audit:ok -/
def IsSufficientStatistic (c x : ℕ) (S : Finset ℕ) : Prop :=
  x ∈ S ∧ twoPartLength S ≤ prefixComplexity x + c

theorem natLen_le_clog_card {S : Finset ℕ} {i : ℕ} (h : i < S.card) :
    natLen i ≤ Nat.clog 2 S.card :=
  natLen_le_of_lt_two_pow i _ (lt_of_lt_of_le h (Nat.le_pow_clog Nat.one_lt_two _))

theorem exists_index_of_mem {S : Finset ℕ} {x : ℕ} (h : x ∈ S) :
    ∃ i, i < S.card ∧ (S.sort (· ≤ ·))[i]? = some x := by
  have hmem : x ∈ S.sort (· ≤ ·) := (Finset.mem_sort _).2 h
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hmem
  exact ⟨i, by rwa [Finset.length_sort] at hi, by rw [List.getElem?_eq_getElem hi, hix]⟩

theorem structureFunction_antitone (x : ℕ) {k k' : ℕ} (h : k ≤ k') :
    structureFunction x k' ≤ structureFunction x k := by
  refine sInf_le_sInf ?_
  rintro l ⟨S, hxS, hSk, rfl⟩
  exact ⟨S, hxS, hSk.trans h, rfl⟩

theorem structureFunction_zero (x : ℕ) : structureFunction x 0 = ⊤ := by
  rw [structureFunction, ← sInf_empty]
  congr 1
  refine Set.eq_empty_of_forall_notMem ?_
  rintro l ⟨S, -, hSk, -⟩
  rw [modelComplexity, prefixComplexity_eq_two_mul_payloadComplexity_add_one] at hSk
  omega

theorem structureFunction_eq_zero_of_singleton_budget {x k : ℕ}
    (h : modelComplexity {x} ≤ k) : structureFunction x k = 0 := by
  refine le_antisymm ?_ (by simp)
  refine sInf_le ⟨{x}, Finset.mem_singleton_self x, h, ?_⟩
  simp

theorem mdlComplexity_set_nonempty (x : ℕ) :
    { l | ∃ S : Finset ℕ, x ∈ S ∧ twoPartLength S = l }.Nonempty :=
  ⟨twoPartLength {x}, {x}, Finset.mem_singleton_self x, rfl⟩

theorem mdlComplexity_spec (x : ℕ) :
    ∃ S : Finset ℕ, x ∈ S ∧ twoPartLength S = mdlComplexity x :=
  Nat.sInf_mem (mdlComplexity_set_nonempty x)

theorem mdlComplexity_le_of_mem {x : ℕ} {S : Finset ℕ} (h : x ∈ S) :
    mdlComplexity x ≤ twoPartLength S :=
  Nat.sInf_le ⟨S, h, rfl⟩

/-! ### The bit codec is primitive recursive -/

theorem encodeNat_zero : encodeNat 0 = [] := rfl

theorem encodeNat_cast_posNum (p : PosNum) : encodeNat (p : ℕ) = encodePosNum p := by
  change encodeNum ((p : ℕ) : Num) = encodePosNum p
  rw [PosNum.of_to_nat]
  rfl

theorem encodePosNum_eq_cons (p : PosNum) :
    encodePosNum p = decide ((p : ℕ) % 2 = 1) :: encodeNat ((p : ℕ) / 2) := by
  induction p with
  | one => rfl
  | bit0 q _ =>
    have hc : ((PosNum.bit0 q : PosNum) : ℕ) = (q : ℕ) + (q : ℕ) := PosNum.cast_bit0 q
    change false :: encodePosNum q = _
    congr 1
    · symm
      rw [decide_eq_false_iff_not]
      omega
    · rw [show ((PosNum.bit0 q : PosNum) : ℕ) / 2 = (q : ℕ) by omega, encodeNat_cast_posNum]
  | bit1 q _ =>
    have hc : ((PosNum.bit1 q : PosNum) : ℕ) = (q : ℕ) + (q : ℕ) + 1 := PosNum.cast_bit1 q
    change true :: encodePosNum q = _
    congr 1
    · symm
      rw [decide_eq_true_iff]
      omega
    · rw [show ((PosNum.bit1 q : PosNum) : ℕ) / 2 = (q : ℕ) by omega, encodeNat_cast_posNum]

theorem encodeNat_eq_cons {n : ℕ} (hn : n ≠ 0) :
    encodeNat n = decide (n % 2 = 1) :: encodeNat (n / 2) := by
  have hto : ((n : Num) : ℕ) = n := Num.to_of_nat n
  cases hnum : (n : Num) with
  | zero =>
    rw [hnum] at hto
    exact absurd hto.symm (by simpa using hn)
  | pos p =>
    rw [hnum] at hto
    have hn' : (p : ℕ) = n := by simpa using hto
    subst hn'
    rw [encodeNat_cast_posNum]
    exact encodePosNum_eq_cons p

theorem encodePosNum_decodePosNum_concat (w : List Bool) :
    encodePosNum (decodePosNum (w ++ [true])) = w ++ [true] := by
  induction w with
  | nil => rfl
  | cons b v ih =>
    have hne : (v ++ [true] : List Bool) ≠ [] := by simp
    cases b with
    | false =>
      change encodePosNum (PosNum.bit0 (decodePosNum (v ++ [true]))) = _
      change false :: encodePosNum (decodePosNum (v ++ [true])) = _
      rw [ih]
      simp
    | true =>
      change encodePosNum (if (v ++ [true] : List Bool) = [] then PosNum.one
        else PosNum.bit1 (decodePosNum (v ++ [true]))) = _
      rw [if_neg hne]
      change true :: encodePosNum (decodePosNum (v ++ [true])) = _
      rw [ih]
      simp

theorem encodeNat_decodeNat_concat (w : List Bool) :
    encodeNat (decodeNat (w ++ [true])) = w ++ [true] := by
  have hne : (w ++ [true] : List Bool) ≠ [] := by simp
  have h1 : decodeNat (w ++ [true]) = ((decodePosNum (w ++ [true]) : PosNum) : ℕ) := by
    change ((decodeNum (w ++ [true]) : Num) : ℕ) = _
    rw [Computability.decodeNum, if_neg hne]
    simp
  rw [h1, encodeNat_cast_posNum, encodePosNum_decodePosNum_concat]

/-- One step of the little-endian bit expansion: peel off the lowest bit of the
remaining value and append it to the accumulated bit string. -/
def bitStep (s : ℕ × List Bool) : ℕ × List Bool :=
  if s.1 = 0 then s else (s.1 / 2, s.2 ++ [decide (s.1 % 2 = 1)])

theorem bitStep_iterate (k : ℕ) :
    ∀ (n : ℕ) (acc : List Bool), n ≤ k → (bitStep^[k] (n, acc)).2 = acc ++ encodeNat n := by
  induction k with
  | zero =>
    intro n acc hn
    obtain rfl : n = 0 := Nat.le_zero.mp hn
    simp [encodeNat_zero]
  | succ k ih =>
    intro n acc hn
    rw [Function.iterate_succ_apply]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [show bitStep (0, acc) = (0, acc) by simp [bitStep], ih 0 acc (Nat.zero_le k)]
    · have hne : n ≠ 0 := by omega
      rw [show bitStep (n, acc) = (n / 2, acc ++ [decide (n % 2 = 1)]) by simp [bitStep, hne],
        ih (n / 2) _ (by omega), encodeNat_eq_cons hne]
      simp

theorem encodeNat_eq_iterate (n : ℕ) : (bitStep^[n] (n, [])).2 = encodeNat n := by
  simpa using bitStep_iterate n n [] le_rfl

theorem encodeNat_primrec : Primrec encodeNat := by
  have hbool : PrimrecPred fun s : ℕ × List Bool ↦ s.1 % 2 = 1 :=
    PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2))
      (Primrec.const 1)
  have hstep : Primrec bitStep := by
    change Primrec fun s : ℕ × List Bool ↦
      if s.1 = 0 then s else (s.1 / 2, s.2 ++ [decide (s.1 % 2 = 1)])
    refine Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.fst (Primrec.const 0)) Primrec.id ?_
    exact Primrec.pair (Primrec.nat_div.comp Primrec.fst (Primrec.const 2))
      (Primrec.list_append.comp Primrec.snd
        (Primrec.list_cons.comp hbool.decide (Primrec.const [])))
  have hiter : Primrec fun n : ℕ ↦ bitStep^[n] (n, ([] : List Bool)) :=
    Primrec.nat_iterate Primrec.id (Primrec.id.pair (Primrec.const []))
      (hstep.comp Primrec.snd).to₂
  exact (Primrec.snd.comp hiter).of_eq encodeNat_eq_iterate

theorem decodeNat_of_ne_nil {l : List Bool} (h : l ≠ []) :
    decodeNat l = ((decodePosNum l : PosNum) : ℕ) := by
  change ((decodeNum l : Num) : ℕ) = _
  rw [Computability.decodeNum, if_neg h]
  simp

theorem decodeNat_cons (b : Bool) (l : List Bool) :
    decodeNat (b :: l) = if l = [] then cond b 1 2 else 2 * decodeNat l + cond b 1 0 := by
  rw [decodeNat_of_ne_nil (List.cons_ne_nil b l)]
  rcases eq_or_ne l [] with rfl | hne
  · cases b <;> simp [Computability.decodePosNum]
  · rw [if_neg hne, decodeNat_of_ne_nil hne]
    cases b with
    | false =>
      change ((PosNum.bit0 (decodePosNum l) : PosNum) : ℕ) = _
      rw [PosNum.cast_bit0]
      simp
      ring
    | true =>
      change ((if l = [] then PosNum.one else PosNum.bit1 (decodePosNum l) : PosNum) : ℕ) = _
      rw [if_neg hne, PosNum.cast_bit1]
      simp
      ring

theorem decodeNat_eq_rec (l : List Bool) :
    decodeNat l =
      List.recOn l 0 fun b rest IH ↦ if rest = [] then cond b 1 2 else 2 * IH + cond b 1 0 := by
  induction l with
  | nil => rfl
  | cons b rest ih => rw [decodeNat_cons, ih]

theorem decodeNat_primrec : Primrec decodeNat := by
  have hb : Primrec fun x : List Bool × (Bool × List Bool × ℕ) ↦ x.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hl : Primrec fun x : List Bool × (Bool × List Bool × ℕ) ↦ x.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hih : Primrec fun x : List Bool × (Bool × List Bool × ℕ) ↦ x.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hh : Primrec₂ fun (_ : List Bool) (t : Bool × List Bool × ℕ) ↦
      if t.2.1 = [] then cond t.1 1 2 else 2 * t.2.2 + cond t.1 1 0 :=
    (Primrec.ite (PrimrecRel.comp Primrec.eq hl (Primrec.const []))
      (Primrec.cond hb (Primrec.const 1) (Primrec.const 2))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hih)
        (Primrec.cond hb (Primrec.const 1) (Primrec.const 0)))).to₂
  exact (Primrec.list_rec Primrec.id (Primrec.const 0) hh).of_eq fun l ↦ (decodeNat_eq_rec l).symm

theorem parseUnary_eq_rec (l : List Bool) :
    parseUnary l =
      List.recOn l (0, ([] : List Bool)) fun b rest IH ↦ cond b (IH.1 + 1, IH.2) (0, rest) := by
  induction l with
  | nil => rfl
  | cons b rest ih => cases b <;> simp [parseUnary, ih]

theorem parseUnary_primrec : Primrec parseUnary := by
  have hb : Primrec fun x : List Bool × (Bool × List Bool × (ℕ × List Bool)) ↦ x.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hrest : Primrec fun x : List Bool × (Bool × List Bool × (ℕ × List Bool)) ↦ x.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hih : Primrec fun x : List Bool × (Bool × List Bool × (ℕ × List Bool)) ↦ x.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hh : Primrec₂ fun (_ : List Bool) (t : Bool × List Bool × (ℕ × List Bool)) ↦
      cond t.1 (t.2.2.1 + 1, t.2.2.2) (0, t.2.1) :=
    (Primrec.cond hb
      (Primrec.pair (Primrec.succ.comp (Primrec.fst.comp hih)) (Primrec.snd.comp hih))
      (Primrec.pair (Primrec.const 0) hrest)).to₂
  exact (Primrec.list_rec Primrec.id (Primrec.const (0, [])) hh).of_eq
    fun l ↦ (parseUnary_eq_rec l).symm

/-! ### The payload decoder is partial recursive -/

/-- The payload decoder presented as a code together with its input: the literal
mode uses the identity code, and the interpret mode the code named by the unary
index. The empty payload has no dispatch, which is how `decodePayload` diverges
on it. -/
noncomputable def payloadDispatch : List Bool → Option (Code × ℕ)
  | [] => none
  | (false :: bs) => some (Code.id, decodeNat bs)
  | (true :: bs) =>
      some (Denumerable.ofNat Code (parseUnary bs).1,
        Nat.pair (decodeNat (parseUnary bs).2) 0)

theorem payloadDispatch_primrec : Primrec payloadDispatch := by
  have hb : Primrec fun x : List Bool × (Bool × List Bool) ↦ x.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hbs : Primrec fun x : List Bool × (Bool × List Bool) ↦ x.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hpu : Primrec fun x : List Bool × (Bool × List Bool) ↦ parseUnary x.2.2 :=
    parseUnary_primrec.comp hbs
  have hlit : Primrec fun x : List Bool × (Bool × List Bool) ↦
      (some (Code.id, decodeNat x.2.2) : Option (Code × ℕ)) :=
    Primrec.option_some.comp
      (Primrec.pair (Primrec.const Code.id) (decodeNat_primrec.comp hbs))
  have hint : Primrec fun x : List Bool × (Bool × List Bool) ↦
      (some (Denumerable.ofNat Code (parseUnary x.2.2).1,
        Nat.pair (decodeNat (parseUnary x.2.2).2) 0) : Option (Code × ℕ)) :=
    Primrec.option_some.comp (Primrec.pair
      ((Primrec.ofNat Code).comp (Primrec.fst.comp hpu))
      (Primrec₂.natPair.comp (decodeNat_primrec.comp (Primrec.snd.comp hpu))
        (Primrec.const 0)))
  have hh : Primrec₂ fun (_ : List Bool) (t : Bool × List Bool) ↦
      cond t.1 (some (Denumerable.ofNat Code (parseUnary t.2).1,
          Nat.pair (decodeNat (parseUnary t.2).2) 0))
        (some (Code.id, decodeNat t.2)) :=
    (Primrec.cond hb hint hlit).to₂
  refine (Primrec.list_casesOn Primrec.id (Primrec.const none) hh).of_eq ?_
  rintro (_ | ⟨b, bs⟩)
  · rfl
  · cases b <;> rfl

theorem payloadDispatch_computable : Computable payloadDispatch :=
  payloadDispatch_primrec.to_comp

theorem decodePayload_eq_dispatch (d : List Bool) :
    decodePayload d = (payloadDispatch d : Part (Code × ℕ)).bind fun p ↦ eval p.1 p.2 := by
  rcases d with _ | ⟨b, bs⟩
  · simp [decodePayload, payloadDispatch]
  · cases b with
    | false => simp [decodePayload, payloadDispatch, eval_id]
    | true => simp [decodePayload, payloadDispatch]

theorem decodePayload_partrec : Partrec decodePayload := by
  have hg : Partrec₂ fun (_ : List Bool) (p : Code × ℕ) ↦ eval p.1 p.2 :=
    Partrec₂.comp eval_part (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)
  exact (Partrec.bind (Computable.ofOption payloadDispatch_computable) hg).of_eq
    fun d ↦ (decodePayload_eq_dispatch d).symm

/-! ### Self-simulation of the machine -/

theorem payloadComplexity_le_of_eval (c : Code) :
    ∃ b : ℕ, ∀ (x : ℕ) (q : List Bool),
      x ∈ eval c (Nat.pair (decodeNat q) 0) → payloadComplexity x ≤ q.length + b := by
  refine ⟨encodeCode c + 2, fun x q hx ↦ ?_⟩
  have hcode : Denumerable.ofNat Code (encodeCode c) = c := by
    rw [← encodeCode_eq]; exact Denumerable.ofNat_encode c
  have hmem : x ∈ decodePayload
      (true :: (List.replicate (encodeCode c) true ++ (false :: q))) := by
    change x ∈ eval (Denumerable.ofNat Code
        (parseUnary (List.replicate (encodeCode c) true ++ (false :: q))).1)
      (Nat.pair (decodeNat
        (parseUnary (List.replicate (encodeCode c) true ++ (false :: q))).2) 0)
    rw [parseUnary_replicate, hcode]
    exact hx
  have hle := payloadComplexity_le_of_mem hmem
  have hlen : (true :: (List.replicate (encodeCode c) true ++ (false :: q))).length
      = q.length + (encodeCode c + 2) := by simp; omega
  rwa [hlen] at hle

theorem payload_invariance (A : ℕ → ℕ → Part ℕ) (hA : Partrec₂ A) :
    ∃ b : ℕ, ∀ (x : ℕ) (q : List Bool),
      x ∈ A (decodeNat q) 0 → payloadComplexity x ≤ q.length + b := by
  obtain ⟨c, hc⟩ := exists_code.1 (Partrec₂.unpaired'.2 hA)
  obtain ⟨b, hb⟩ := payloadComplexity_le_of_eval c
  refine ⟨b, fun x q hx ↦ ?_⟩
  apply hb x q
  rw [hc]
  simpa [Nat.unpaired, Nat.unpair_pair] using hx

/-- The index part packed into `N`: the self-delimited prefix of the bit string
of `N`. -/
def packIndex (N : ℕ) : ℕ :=
  decodeNat ((parseUnary (encodeNat N)).2.take (parseUnary (encodeNat N)).1)

/-- The payload part packed into `N`: what follows the self-delimited index,
with the terminating sentinel bit removed. -/
def packPayload (N : ℕ) : List Bool :=
  ((parseUnary (encodeNat N)).2.drop (parseUnary (encodeNat N)).1).dropLast

/-- The bit string packing an index `i` together with a payload `d`: the index in
self-delimited form, then the payload, then a sentinel bit making the string a
canonical binary expansion. -/
def packBits (i : ℕ) (d : List Bool) : List Bool :=
  selfDelimit (encodeNat i) ++ (d ++ [true])

theorem packBits_length (i : ℕ) (d : List Bool) :
    (packBits i d).length = 2 * natLen i + d.length + 2 := by
  simp [packBits, selfDelimit_length, natLen]
  omega

theorem parseUnary_packBits (i : ℕ) (d : List Bool) :
    parseUnary (packBits i d) = (natLen i, encodeNat i ++ (d ++ [true])) := by
  have h : packBits i d
      = List.replicate (natLen i) true ++ (false :: (encodeNat i ++ (d ++ [true]))) := by
    simp [packBits, selfDelimit, natLen]
  rw [h, parseUnary_replicate]

theorem encodeNat_decodeNat_packBits (i : ℕ) (d : List Bool) :
    encodeNat (decodeNat (packBits i d)) = packBits i d := by
  have h : packBits i d = (selfDelimit (encodeNat i) ++ d) ++ [true] := by
    simp [packBits]
  rw [h]
  exact encodeNat_decodeNat_concat _

theorem packIndex_packBits (i : ℕ) (d : List Bool) :
    packIndex (decodeNat (packBits i d)) = i := by
  rw [packIndex, encodeNat_decodeNat_packBits, parseUnary_packBits]
  simp [natLen]

theorem packPayload_packBits (i : ℕ) (d : List Bool) :
    packPayload (decodeNat (packBits i d)) = d := by
  rw [packPayload, encodeNat_decodeNat_packBits, parseUnary_packBits]
  simp [natLen]

/-- The unpacking machine: read the index and the payload out of `N`, run the
payload through the machine's own payload decoder, and feed the result together
with the index to `A`. -/
noncomputable def twoPartUnpack (A : ℕ → ℕ → Part ℕ) (N : ℕ) (_ : ℕ) : Part ℕ :=
  (decodePayload (packPayload N)).bind fun y ↦ A y (packIndex N)

theorem packIndex_primrec : Primrec packIndex := by
  have he : Primrec fun N : ℕ ↦ parseUnary (encodeNat N) :=
    parseUnary_primrec.comp encodeNat_primrec
  exact decodeNat_primrec.comp
    (Primrec.list_take.comp (Primrec.fst.comp he) (Primrec.snd.comp he))

theorem packPayload_primrec : Primrec packPayload := by
  have he : Primrec fun N : ℕ ↦ parseUnary (encodeNat N) :=
    parseUnary_primrec.comp encodeNat_primrec
  have hdl : Primrec fun l : List Bool ↦ l.dropLast :=
    (Primrec.list_take.comp
      (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)) Primrec.id).of_eq
      fun _ ↦ List.dropLast_eq_take.symm
  exact hdl.comp (Primrec.list_drop.comp (Primrec.fst.comp he) (Primrec.snd.comp he))

theorem twoPartUnpack_partrec {A : ℕ → ℕ → Part ℕ} (hA : Partrec₂ A) :
    Partrec₂ (twoPartUnpack A) := by
  have hf : Partrec fun x : ℕ × ℕ ↦ decodePayload (packPayload x.1) :=
    decodePayload_partrec.comp (packPayload_primrec.to_comp.comp Computable.fst)
  have hg : Partrec₂ fun (x : ℕ × ℕ) (y : ℕ) ↦ A y (packIndex x.1) :=
    Partrec₂.comp hA Computable.snd
      (packIndex_primrec.to_comp.comp (Computable.fst.comp Computable.fst))
  exact Partrec.bind hf hg

/-- Feeding a partial recursive `A` a value `y` and an index `i` costs, in payload
complexity, no more than the payload complexity of `y` plus the self-delimited
index, up to a constant depending only on `A`. The hypothesis `Partrec₂ A` is what
puts `A` on the machine at all: it is discharged into a `Code` and never supplies
the bound.
@audit:ok -/
theorem payloadComplexity_two_part_le (A : ℕ → ℕ → Part ℕ) (hA : Partrec₂ A) :
    ∃ c : ℕ, ∀ (x y i : ℕ), x ∈ A y i →
      payloadComplexity x ≤ payloadComplexity y + 2 * natLen i + c := by
  obtain ⟨b, hb⟩ := payload_invariance (twoPartUnpack A) (twoPartUnpack_partrec hA)
  refine ⟨b + 2, fun x y i hx ↦ ?_⟩
  obtain ⟨d, hdlen, hdmem⟩ := payloadComplexity_spec y
  have hmem : x ∈ twoPartUnpack A (decodeNat (packBits i d)) 0 := by
    rw [twoPartUnpack, packPayload_packBits, packIndex_packBits]
    exact Part.mem_bind_iff.2 ⟨y, hdmem, hx⟩
  have hle := hb x (packBits i d) hmem
  rw [packBits_length] at hle
  omega

/-! ### Two-part descriptions bound the prefix complexity -/

/-- The two-part decoder: read `y` as a list of naturals and return its `i`-th
entry. -/
def listIndexDecoder (y i : ℕ) : Option ℕ := ((decode (α := List ℕ) y).getD [])[i]?

theorem listIndexDecoder_partrec :
    Partrec₂ fun y i ↦ (listIndexDecoder y i : Part ℕ) := by
  have hgetD : Primrec fun p : ℕ × ℕ ↦ ((decode (α := List ℕ) p.1).getD []) :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const [])
  exact Computable.ofOption (Primrec.list_getElem?.comp hgetD Primrec.snd).to_comp

theorem singletonCode_partrec :
    Partrec₂ fun (y _ : ℕ) ↦ (Part.some (encode [y]) : Part ℕ) :=
  Computable₂.partrec₂
    (Primrec.encode.comp (Primrec.list_cons.comp Primrec.fst (Primrec.const []))).to_comp

theorem modelComplexity_singleton_le :
    ∃ c : ℕ, ∀ x : ℕ, modelComplexity {x} ≤ prefixComplexity x + c := by
  obtain ⟨c, hc⟩ := payloadComplexity_two_part_le _ singletonCode_partrec
  refine ⟨2 * c, fun x ↦ ?_⟩
  have h := hc (encode [x]) x 0 (Part.mem_some _)
  have h0 : natLen 0 = 0 := by simp [natLen, encodeNat_zero]
  rw [h0] at h
  simp only [modelComplexity, modelCode, Finset.sort_singleton,
    prefixComplexity_eq_two_mul_payloadComplexity_add_one]
  omega

theorem exists_isSufficientStatistic_singleton :
    ∃ c : ℕ, ∀ x : ℕ, IsSufficientStatistic c x {x} := by
  obtain ⟨c, hc⟩ := modelComplexity_singleton_le
  refine ⟨c, fun x ↦ ⟨Finset.mem_singleton_self x, ?_⟩⟩
  rw [twoPartLength, Finset.card_singleton, Nat.clog_one_right]
  simpa using hc x

/-- Every two-part description of `x` bounds its prefix complexity, up to an
additive constant independent of `x` and of the model. The index part carries the
machine-specific coefficient `4` built into `twoPartLength`, so this is not the
textbook inequality `K(x) ≤ K(S) + log |S| + O(1)`; the model part does carry
coefficient `1`.
@audit:ok -/
@[entry_point]
theorem prefixComplexity_le_twoPartLength :
    ∃ c : ℕ, ∀ (x : ℕ) (S : Finset ℕ),
      x ∈ S → prefixComplexity x ≤ twoPartLength S + c := by
  obtain ⟨c, hc⟩ := payloadComplexity_two_part_le _ listIndexDecoder_partrec
  refine ⟨2 * c, fun x S hxS ↦ ?_⟩
  obtain ⟨i, hi, hix⟩ := exists_index_of_mem hxS
  have hval : listIndexDecoder (modelCode S) i = some x := by
    rw [listIndexDecoder, modelCode, Encodable.encodek]
    simpa using hix
  have h := hc x (modelCode S) i (by simp [hval])
  have hnat : natLen i ≤ Nat.clog 2 S.card := natLen_le_clog_card hi
  simp only [twoPartLength, modelComplexity,
    prefixComplexity_eq_two_mul_payloadComplexity_add_one]
  omega

/-- The shortest two-part description length agrees with the prefix complexity up
to an additive constant. As with `prefixComplexity_le_twoPartLength`, the index
part of `twoPartLength` carries the machine-specific coefficient `4`, so this is
a statement about that quantity and not the textbook minimum description length
principle.
@audit:ok -/
@[entry_point]
theorem mdlComplexity_sub_prefixComplexity_le :
    ∃ c : ℕ, ∀ x : ℕ, mdlComplexity x ≤ prefixComplexity x + c ∧
      prefixComplexity x ≤ mdlComplexity x + c := by
  obtain ⟨c₁, h₁⟩ := modelComplexity_singleton_le
  obtain ⟨c₂, h₂⟩ := prefixComplexity_le_twoPartLength
  refine ⟨c₁ + c₂, fun x ↦ ⟨?_, ?_⟩⟩
  · have hle : mdlComplexity x ≤ twoPartLength {x} :=
      mdlComplexity_le_of_mem (Finset.mem_singleton_self x)
    rw [twoPartLength, Finset.card_singleton, Nat.clog_one_right] at hle
    have := h₁ x
    omega
  · obtain ⟨S, hxS, hS⟩ := mdlComplexity_spec x
    have := h₂ x S hxS
    omega

end InformationTheory.Kolmogorov

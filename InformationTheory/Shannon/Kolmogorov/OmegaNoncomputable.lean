import InformationTheory.Shannon.Kolmogorov.PrefixComputability

/-!
# A step-bounded evaluator for the self-delimiting machine

Cover–Thomas (2nd ed.) §14.9. Running the self-delimiting machine
`prefixUniversalEval` with a finite budget yields a total function
`prefixEvaln`, primitive recursive in the budget and the program, which is sound
and complete for the unbounded machine. It is the computable skeleton behind the
approximation of the halting probability `Ω` from below.

The section also fixes the notion of a computable nonnegative extended real used
to state that `Ω` is not one: a computable sequence of dyadic numerators whose
values approximate the target within `2 ^ (-n)`.

## Main definitions

* `IsComputableENNReal` — computability of an extended nonnegative real by a
  computable sequence of dyadic rationals with error `2 ^ (-n)`.
* `prefixEvaln` — the step-bounded evaluator of the self-delimiting machine.
* `omegaApprox` — the stage-`t` approximation to `Ω` from below, with numerator
  `omegaApproxNum` over the denominator `2 ^ t`.

## Main results

* `prefixEvaln_primrec` — the bounded evaluator is primitive recursive.
* `prefixEvaln_complete` — a value is output by the machine exactly when some
  finite budget already produces it.
* `omegaApproxNum_computable` — the numerators of the lower approximation form a
  computable sequence.
-/

open scoped ENNReal

namespace InformationTheory.Kolmogorov

open Nat.Partrec Nat.Partrec.Code

/-- A computable nonnegative extended real: a computable sequence of dyadic
numerators `a n`, whose value `a n / 2 ^ n` is within `2 ^ (-n)` of `x`. The two
bounds are stated additively, so no truncated subtraction occurs.

The standard notion — a computable sequence of rationals converging to `x` with
error `2 ^ (-n)` — implies this one: rounding a sufficiently accurate rational
approximation to a multiple of `2 ^ (-n)` produces such a numerator sequence. The
converse-facing strict form `a n * 2 ^ (-n) ≤ x ≤ (a n + 1) * 2 ^ (-n)` is
deliberately avoided: deciding which side of a dyadic grid point `x` falls on is
not computable, so that form is a strictly stronger predicate. -/
def IsComputableENNReal (x : ℝ≥0∞) : Prop :=
  ∃ a : ℕ → ℕ, Computable a ∧ ∀ n : ℕ,
    x ≤ (a n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n + (2 : ℝ≥0∞)⁻¹ ^ n ∧
      (a n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n ≤ x + (2 : ℝ≥0∞)⁻¹ ^ n

/-- The step-bounded evaluator: the self-delimiting machine run with budget `k`,
following `decodePayload_eq_dispatch` with `eval` replaced by `evaln k`. -/
noncomputable def prefixEvaln (k : ℕ) (p : List Bool) : Option ℕ :=
  if (parseUnary p).1 = (parseUnary p).2.length then
    (payloadDispatch (parseUnary p).2).bind fun q ↦ evaln k q.1 q.2
  else none

theorem prefixEvaln_mono {k₁ k₂ : ℕ} {p : List Bool} {x : ℕ}
    (h : k₁ ≤ k₂) (hx : x ∈ prefixEvaln k₁ p) : x ∈ prefixEvaln k₂ p := by
  by_cases hg : (parseUnary p).1 = (parseUnary p).2.length
  · rw [prefixEvaln, if_pos hg] at hx ⊢
    obtain ⟨q, hq, hxq⟩ := Option.mem_bind_iff.mp hx
    exact Option.mem_bind_iff.mpr ⟨q, hq, evaln_mono h hxq⟩
  · rw [prefixEvaln, if_neg hg] at hx
    simp at hx

theorem prefixEvaln_sound {k : ℕ} {p : List Bool} {x : ℕ}
    (hx : x ∈ prefixEvaln k p) : x ∈ prefixUniversalEval p := by
  by_cases hg : (parseUnary p).1 = (parseUnary p).2.length
  · rw [prefixEvaln, if_pos hg] at hx
    obtain ⟨q, hq, hxq⟩ := Option.mem_bind_iff.mp hx
    rw [prefixUniversalEval, if_pos hg, decodePayload_eq_dispatch]
    exact Part.mem_bind_iff.mpr ⟨q, Part.mem_coe.mpr hq, evaln_sound hxq⟩
  · rw [prefixEvaln, if_neg hg] at hx
    simp at hx

theorem prefixEvaln_complete {p : List Bool} {x : ℕ} :
    x ∈ prefixUniversalEval p ↔ ∃ k, x ∈ prefixEvaln k p := by
  refine ⟨fun hx ↦ ?_, fun ⟨_, hk⟩ ↦ prefixEvaln_sound hk⟩
  by_cases hg : (parseUnary p).1 = (parseUnary p).2.length
  · rw [prefixUniversalEval, if_pos hg, decodePayload_eq_dispatch] at hx
    obtain ⟨q, hq, hxq⟩ := Part.mem_bind_iff.mp hx
    obtain ⟨k, hk⟩ := evaln_complete.mp hxq
    refine ⟨k, ?_⟩
    rw [prefixEvaln, if_pos hg]
    exact Option.mem_bind_iff.mpr ⟨q, Part.mem_coe.mp hq, hk⟩
  · rw [prefixUniversalEval, if_neg hg] at hx
    simp at hx

theorem prefixEvaln_dom_iff {p : List Bool} :
    (prefixUniversalEval p).Dom ↔ ∃ k, (prefixEvaln k p).isSome := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := prefixEvaln_complete.mp (Part.get_mem h)
    exact ⟨k, Option.isSome_iff_exists.mpr ⟨_, hk⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
    exact Part.dom_iff_mem.mpr ⟨x, prefixEvaln_sound hx⟩

theorem prefixEvaln_primrec : Primrec fun a : ℕ × List Bool ↦ prefixEvaln a.1 a.2 := by
  have hpu : Primrec fun a : ℕ × List Bool ↦ parseUnary a.2 :=
    parseUnary_primrec.comp Primrec.snd
  have hguard : PrimrecPred fun a : ℕ × List Bool ↦
      (parseUnary a.2).1 = (parseUnary a.2).2.length :=
    PrimrecRel.comp Primrec.eq (Primrec.fst.comp hpu)
      (Primrec.list_length.comp (Primrec.snd.comp hpu))
  have hevaln : Primrec₂ fun (a : ℕ × List Bool) (q : Code × ℕ) ↦ evaln a.1 q.1 q.2 :=
    (primrec_evaln.comp
      (((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd))).to₂
  have hbind : Primrec fun a : ℕ × List Bool ↦
      (payloadDispatch (parseUnary a.2).2).bind fun q ↦ evaln a.1 q.1 q.2 :=
    Primrec.option_bind (payloadDispatch_primrec.comp (Primrec.snd.comp hpu)) hevaln
  exact Primrec.ite hguard hbind (Primrec.const none)

/-! ### Enumerating bit strings -/

theorem primrec_list_sum : Primrec (List.sum : List ℕ → ℕ) := by
  refine (Primrec.list_foldr Primrec.id (Primrec.const 0)
    ((Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)).of_eq fun l ↦ ?_
  induction l with
  | nil => rfl
  | cons a l ih => simpa using ih

theorem primrec_list_filter {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a ↦ (f a).filter (p a) := by
  refine (Primrec.listFilterMap hf
    ((Primrec.cond hp (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂)).of_eq
      fun a ↦ ?_
  generalize f a = L
  induction L with
  | nil => rfl
  | cons b l ih => cases hb : p a b <;> simp [hb, ih]

theorem primrec_two_pow : Primrec fun n : ℕ ↦ 2 ^ n := by
  have key : ∀ n : ℕ, (fun m : ℕ ↦ 2 * m)^[n] 1 = 2 ^ n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ']
  exact (Primrec.nat_iterate Primrec.id (Primrec.const 1)
    ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂)).of_eq key

/-- All bit strings of length exactly `n`. -/
def allBitStrings : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBitStrings n).flatMap fun l ↦ [false :: l, true :: l]

theorem mem_allBitStrings {p : List Bool} {n : ℕ} : p ∈ allBitStrings n ↔ p.length = n := by
  induction n generalizing p with
  | zero => simp [allBitStrings, List.length_eq_zero_iff]
  | succ n ih =>
    rw [allBitStrings]
    simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, ih]
    constructor
    · rintro ⟨l, hl, rfl | rfl⟩ <;> simp [hl]
    · intro hp
      match p with
      | b :: l => exact ⟨l, by simpa using hp, by cases b <;> simp⟩

theorem allBitStrings_nodup (n : ℕ) : (allBitStrings n).Nodup := by
  induction n with
  | zero => simp [allBitStrings]
  | succ n ih =>
    rw [allBitStrings, List.nodup_flatMap]
    refine ⟨fun l _ ↦ by simp, ih.imp fun {l₁ l₂} hne ↦ ?_⟩
    intro q hq₁ hq₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq₁ hq₂
    rcases hq₁ with rfl | rfl <;> rcases hq₂ with h | h <;> simp_all

theorem allBitStrings_primrec : Primrec allBitStrings := by
  have key : ∀ n : ℕ,
      (fun L : List (List Bool) ↦ L.flatMap fun l ↦ [false :: l, true :: l])^[n] [[]]
        = allBitStrings n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl
  have hstep : Primrec₂ fun (_ : ℕ) (L : List (List Bool)) ↦
      L.flatMap fun l ↦ [false :: l, true :: l] := by
    have hsnd : Primrec fun x : ℕ × List (List Bool) ↦ x.2 := Primrec.snd
    have hpair : Primrec fun x : (ℕ × List (List Bool)) × List Bool ↦
        ([false :: x.2, true :: x.2] : List (List Bool)) :=
      Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
        (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
          (Primrec.const ([] : List (List Bool))))
    exact (Primrec.list_flatMap hsnd hpair.to₂).to₂
  exact (Primrec.nat_iterate Primrec.id
    (Primrec.const ([[]] : List (List Bool))) hstep).of_eq key

/-- All bit strings of length at most `t`. -/
def allBitStringsLE (t : ℕ) : List (List Bool) :=
  (List.range (t + 1)).flatMap allBitStrings

theorem mem_allBitStringsLE {p : List Bool} {t : ℕ} : p ∈ allBitStringsLE t ↔ p.length ≤ t := by
  simp only [allBitStringsLE, List.mem_flatMap, List.mem_range, mem_allBitStrings]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · exact fun h ↦ ⟨p.length, by omega, rfl⟩

theorem allBitStringsLE_nodup (t : ℕ) : (allBitStringsLE t).Nodup := by
  rw [allBitStringsLE, List.nodup_flatMap]
  refine ⟨fun n _ ↦ allBitStrings_nodup n, List.nodup_range.imp fun {n m} hne q hq₁ hq₂ ↦ ?_⟩
  exact hne ((mem_allBitStrings.mp hq₁).symm.trans (mem_allBitStrings.mp hq₂))

theorem allBitStringsLE_primrec : Primrec allBitStringsLE := by
  have hrange : Primrec fun t : ℕ ↦ List.range (t + 1) := Primrec.list_range.comp Primrec.succ
  exact Primrec.list_flatMap hrange (allBitStrings_primrec.comp Primrec.snd).to₂

/-! ### Approximating the halting probability from below -/

/-- The programs of length at most `t` on which the machine already halts within
budget `t`. -/
noncomputable def haltingList (t : ℕ) : List (List Bool) :=
  (allBitStringsLE t).filter fun p ↦ (prefixEvaln t p).isSome

theorem mem_haltingList {t : ℕ} {p : List Bool} :
    p ∈ haltingList t ↔ p.length ≤ t ∧ (prefixEvaln t p).isSome := by
  simp [haltingList, List.mem_filter, mem_allBitStringsLE]

theorem haltingList_nodup (t : ℕ) : (haltingList t).Nodup :=
  (allBitStringsLE_nodup t).filter _

theorem haltingList_primrec : Primrec haltingList :=
  primrec_list_filter allBitStringsLE_primrec
    (Primrec.option_isSome.comp prefixEvaln_primrec).to₂

/-- The stage-`t` approximation to `Ω` from below: the mass of the programs of
length at most `t` on which the machine halts within budget `t`. -/
noncomputable def omegaApprox (t : ℕ) : ℝ≥0∞ :=
  ∑ p ∈ (haltingList t).toFinset, (2 : ℝ≥0∞)⁻¹ ^ p.length

/-- The numerator of `omegaApprox t` written over the denominator `2 ^ t`. -/
noncomputable def omegaApproxNum (t : ℕ) : ℕ :=
  ((haltingList t).map fun p ↦ 2 ^ (t - p.length)).sum

theorem natCast_two_pow_sub_mul_inv_pow {ℓ t : ℕ} (h : ℓ ≤ t) :
    ((2 ^ (t - ℓ) : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ t = (2 : ℝ≥0∞)⁻¹ ^ ℓ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hcast : ((2 ^ k : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ k := by push_cast; ring
  have hcancel : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero (by simp)
  rw [Nat.add_sub_cancel_left, hcast, pow_add,
    show (2 : ℝ≥0∞) ^ k * ((2 : ℝ≥0∞)⁻¹ ^ ℓ * (2 : ℝ≥0∞)⁻¹ ^ k)
      = ((2 : ℝ≥0∞) * 2⁻¹) ^ k * (2 : ℝ≥0∞)⁻¹ ^ ℓ by rw [mul_pow]; ring,
    hcancel, one_pow, one_mul]

theorem omegaApprox_eq_num (t : ℕ) :
    omegaApprox t = (omegaApproxNum t : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ t := by
  have key : ∀ L : List (List Bool), (∀ p ∈ L, p.length ≤ t) →
      (L.map fun p ↦ (2 : ℝ≥0∞)⁻¹ ^ p.length).sum
        = (((L.map fun p ↦ 2 ^ (t - p.length)).sum : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ t := by
    intro L hL
    induction L with
    | nil => simp
    | cons p L ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        ih fun q hq ↦ hL q (List.mem_cons_of_mem _ hq), Nat.cast_add, add_mul,
        natCast_two_pow_sub_mul_inv_pow (hL p List.mem_cons_self)]
  rw [omegaApprox, List.sum_toFinset _ (haltingList_nodup t), omegaApproxNum]
  exact key _ fun p hp ↦ (mem_haltingList.mp hp).1

theorem omegaApprox_ne_top (t : ℕ) : omegaApprox t ≠ ⊤ := by
  rw [omegaApprox_eq_num]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero))

theorem omegaApproxNum_computable : Computable omegaApproxNum := by
  have hmap : Primrec fun t : ℕ ↦ (haltingList t).map fun p ↦ 2 ^ (t - p.length) :=
    Primrec.list_map haltingList_primrec
      ((primrec_two_pow.comp
        (Primrec.nat_sub.comp Primrec.fst (Primrec.list_length.comp Primrec.snd))).to₂)
  exact (primrec_list_sum.comp hmap).to_comp

end InformationTheory.Kolmogorov

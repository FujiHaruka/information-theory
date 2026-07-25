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

The stage approximations increase to `Ω` — each is a subsum of the halting
weight, and every finite subsum is already reached at some stage. So a
computable approximation of `Ω` from above lets one search for a stage whose
weight is within `2 ^ (-n)` of `Ω`, and that search is itself computable because
every comparison involved is between natural numbers over a common power of two.

## Main definitions

* `IsComputableENNReal` — computability of an extended nonnegative real by a
  computable sequence of dyadic rationals with error `2 ^ (-n)`.
* `prefixEvaln` — the step-bounded evaluator of the self-delimiting machine.
* `omegaApprox` — the stage-`t` approximation to `Ω` from below, with numerator
  `omegaApproxNum` over the denominator `2 ^ t`.
* `searchPred` — the stage-lookup predicate, phrased over natural numbers.

## Main results

* `prefixEvaln_primrec` — the bounded evaluator is primitive recursive.
* `prefixEvaln_complete` — a value is output by the machine exactly when some
  finite budget already produces it.
* `omegaApproxNum_computable` — the numerators of the lower approximation form a
  computable sequence.
* `iSup_omegaApprox` — the stage approximations have supremum `Ω`, so
  `exists_omegaApprox_gt` brings them within any positive margin of `Ω`.
* `searchTime_computable` — the stage located by the search is a computable
  function of the requested precision.
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

/-! ### Monotonicity and cofinality of the lower approximation -/

theorem prefixEvaln_isSome_mono {k₁ k₂ : ℕ} {p : List Bool} (h : k₁ ≤ k₂)
    (hp : (prefixEvaln k₁ p).isSome) : (prefixEvaln k₂ p).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
  exact Option.isSome_iff_exists.mpr ⟨x, prefixEvaln_mono h hx⟩

theorem haltingList_toFinset_subset {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    (haltingList t₁).toFinset ⊆ (haltingList t₂).toFinset := by
  intro p hp
  rw [List.mem_toFinset, mem_haltingList] at hp ⊢
  exact ⟨hp.1.trans h, prefixEvaln_isSome_mono h hp.2⟩

theorem omegaApprox_mono : Monotone omegaApprox :=
  fun _ _ h ↦ Finset.sum_le_sum_of_subset (haltingList_toFinset_subset h)

theorem sum_le_chaitinOmega {s : Finset (List Bool)}
    (hs : ∀ p ∈ s, (prefixUniversalEval p).Dom) :
    ∑ p ∈ s, (2 : ℝ≥0∞)⁻¹ ^ p.length ≤ chaitinOmega := by
  classical
  have hinj : ∀ x ∈ s.attach, ∀ y ∈ s.attach,
      (⟨x.1, hs x.1 x.2⟩ : { p : List Bool // (prefixUniversalEval p).Dom })
        = ⟨y.1, hs y.1 y.2⟩ → x = y :=
    fun _ _ _ _ hxy ↦ Subtype.ext (by simpa using hxy)
  calc ∑ p ∈ s, (2 : ℝ≥0∞)⁻¹ ^ p.length
      = ∑ q ∈ s.attach.image fun x ↦
          (⟨x.1, hs x.1 x.2⟩ : { p : List Bool // (prefixUniversalEval p).Dom }),
          (2 : ℝ≥0∞)⁻¹ ^ (q : List Bool).length := by
        rw [Finset.sum_image hinj]
        exact (Finset.sum_attach s fun p ↦ (2 : ℝ≥0∞)⁻¹ ^ p.length).symm
    _ ≤ chaitinOmega := by rw [chaitinOmega]; exact ENNReal.sum_le_tsum _

theorem omegaApprox_le_chaitinOmega (t : ℕ) : omegaApprox t ≤ chaitinOmega := by
  rw [omegaApprox]
  refine sum_le_chaitinOmega fun p hp ↦ ?_
  rw [List.mem_toFinset, mem_haltingList] at hp
  exact prefixEvaln_dom_iff.mpr ⟨t, hp.2⟩

theorem exists_sum_le_omegaApprox (s : Finset { p : List Bool // (prefixUniversalEval p).Dom }) :
    ∃ t, ∑ q ∈ s, (2 : ℝ≥0∞)⁻¹ ^ (q : List Bool).length ≤ omegaApprox t := by
  classical
  have hex : ∀ q : { p : List Bool // (prefixUniversalEval p).Dom },
      ∃ k, (prefixEvaln k (q : List Bool)).isSome := fun q ↦ prefixEvaln_dom_iff.mp q.2
  obtain ⟨t, ht⟩ : ∃ t : ℕ, ∀ q ∈ s,
      (q : List Bool).length ≤ t ∧ (prefixEvaln t (q : List Bool)).isSome := by
    refine ⟨s.sup fun q ↦ max (hex q).choose (q : List Bool).length, fun q hq ↦ ?_⟩
    have hle : max (hex q).choose (q : List Bool).length
        ≤ s.sup fun q ↦ max (hex q).choose (q : List Bool).length :=
      Finset.le_sup (f := fun q ↦ max (hex q).choose (q : List Bool).length) hq
    exact ⟨(le_max_right _ _).trans hle,
      prefixEvaln_isSome_mono ((le_max_left _ _).trans hle) (hex q).choose_spec⟩
  refine ⟨t, ?_⟩
  have hsub : s.image (Subtype.val : { p : List Bool // (prefixUniversalEval p).Dom } → List Bool)
      ⊆ (haltingList t).toFinset := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    rw [List.mem_toFinset, mem_haltingList]
    exact ht q hq
  calc ∑ q ∈ s, (2 : ℝ≥0∞)⁻¹ ^ (q : List Bool).length
      = ∑ p ∈ s.image (Subtype.val :
          { p : List Bool // (prefixUniversalEval p).Dom } → List Bool),
          (2 : ℝ≥0∞)⁻¹ ^ p.length :=
        (Finset.sum_image (f := fun p : List Bool ↦ (2 : ℝ≥0∞)⁻¹ ^ p.length)
          (g := Subtype.val) fun _ _ _ _ h ↦ Subtype.ext h).symm
    _ ≤ omegaApprox t := by rw [omegaApprox]; exact Finset.sum_le_sum_of_subset hsub

theorem chaitinOmega_eq_iSup_sum :
    chaitinOmega = ⨆ s : Finset { p : List Bool // (prefixUniversalEval p).Dom },
      ∑ q ∈ s, (2 : ℝ≥0∞)⁻¹ ^ (q : List Bool).length := by
  rw [chaitinOmega]
  exact ENNReal.tsum_eq_iSup_sum

theorem exists_omegaApprox_gt {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ t, chaitinOmega < omegaApprox t + ε := by
  have hlt : chaitinOmega - ε < chaitinOmega :=
    ENNReal.sub_lt_self chaitinOmega_ne_top chaitinOmega_pos.ne' hε
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp (hlt.trans_eq chaitinOmega_eq_iSup_sum)
  obtain ⟨t, ht⟩ := exists_sum_le_omegaApprox s
  exact ⟨t, ENNReal.lt_add_of_sub_lt_right (Or.inl chaitinOmega_ne_top) (hs.trans_le ht)⟩

theorem iSup_omegaApprox : ⨆ t, omegaApprox t = chaitinOmega := by
  refine le_antisymm (iSup_le omegaApprox_le_chaitinOmega) ?_
  rw [chaitinOmega_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  obtain ⟨t, ht⟩ := exists_sum_le_omegaApprox s
  exact ht.trans (le_iSup _ t)

/-! ### Locating a stage from a computable approximation -/

theorem inv_two_pow_add_self (k : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ (k + 1) + (2 : ℝ≥0∞)⁻¹ ^ (k + 1) = (2 : ℝ≥0∞)⁻¹ ^ k := by
  have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero (by simp)
  calc (2 : ℝ≥0∞)⁻¹ ^ (k + 1) + (2 : ℝ≥0∞)⁻¹ ^ (k + 1)
      = (2 : ℝ≥0∞)⁻¹ ^ k * ((2 : ℝ≥0∞) * 2⁻¹) := by rw [pow_succ]; ring
    _ = (2 : ℝ≥0∞)⁻¹ ^ k := by rw [h2, mul_one]

theorem natCast_mul_inv_pow_eq (c : ℕ) {d ℓ m : ℕ} (h : ℓ + d = m) :
    (c : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ ℓ = ((c * 2 ^ d : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ m := by
  subst h
  have hkey : ((2 ^ d : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (ℓ + d) = (2 : ℝ≥0∞)⁻¹ ^ ℓ := by
    simpa using natCast_two_pow_sub_mul_inv_pow (ℓ := ℓ) (t := ℓ + d) (Nat.le_add_right ℓ d)
  rw [Nat.cast_mul, mul_assoc, hkey]

/-- The search predicate behind the stage lookup, written over the common
denominator `2 ^ (n + 2 + t)` so that every comparison is between natural
numbers: `a (n + 2) * 2 ^ (-(n+2)) ≤ omegaApprox t + 2 ^ (-(n+1))`. -/
def searchPred (a : ℕ → ℕ) (n t : ℕ) : Prop :=
  a (n + 2) * 2 ^ t ≤ omegaApproxNum t * 2 ^ (n + 2) + 2 ^ (t + 1)

noncomputable instance instDecidableSearchPred (a : ℕ → ℕ) (n t : ℕ) :
    Decidable (searchPred a n t) :=
  Nat.decLe _ _

theorem searchPred_iff (a : ℕ → ℕ) (n t : ℕ) :
    searchPred a n t ↔ (a (n + 2) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + 2)
      ≤ omegaApprox t + (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
  have hne : (2 : ℝ≥0∞)⁻¹ ^ (n + 2 + t) ≠ 0 :=
    pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp))
  have htop : (2 : ℝ≥0∞)⁻¹ ^ (n + 2 + t) ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero)
  have h1 : (a (n + 2) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + 2)
      = ((a (n + 2) * 2 ^ t : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + 2 + t) :=
    natCast_mul_inv_pow_eq _ rfl
  have h2a : omegaApprox t
      = ((omegaApproxNum t * 2 ^ (n + 2) : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + 2 + t) := by
    rw [omegaApprox_eq_num]
    exact natCast_mul_inv_pow_eq _ (by omega)
  have h2b : (2 : ℝ≥0∞)⁻¹ ^ (n + 1)
      = ((2 ^ (t + 1) : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + 2 + t) := by
    simpa using natCast_mul_inv_pow_eq (c := 1) (d := t + 1) (ℓ := n + 1) (by omega)
  rw [h1, h2a, h2b, ← add_mul, ← Nat.cast_add,
    ENNReal.mul_le_mul_iff_left hne htop, Nat.cast_le]
  exact Iff.rfl

theorem searchPred_computablePred {a : ℕ → ℕ} (ha : Computable a) :
    ComputablePred fun p : ℕ × ℕ ↦ searchPred a p.1 p.2 := by
  have hmul : Computable₂ fun x y : ℕ ↦ x * y := Primrec₂.to_comp Primrec.nat_mul
  have hadd : Computable₂ fun x y : ℕ ↦ x + y := Primrec₂.to_comp Primrec.nat_add
  have hshift : Primrec fun p : ℕ × ℕ ↦ p.1 + 2 :=
    Primrec.nat_add.comp Primrec.fst (Primrec.const 2)
  have hlhs : Computable fun p : ℕ × ℕ ↦ a (p.1 + 2) * 2 ^ p.2 :=
    hmul.comp (ha.comp hshift.to_comp) (primrec_two_pow.comp Primrec.snd).to_comp
  have hrhs : Computable fun p : ℕ × ℕ ↦ omegaApproxNum p.2 * 2 ^ (p.1 + 2) + 2 ^ (p.2 + 1) :=
    hadd.comp
      (hmul.comp (omegaApproxNum_computable.comp Computable.snd)
        (primrec_two_pow.comp hshift).to_comp)
      (primrec_two_pow.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))).to_comp
  obtain ⟨f, hf, hfeq⟩ := ComputablePred.computable_iff.mp
    (PrimrecPred.computablePred (p := fun q : ℕ × ℕ ↦ q.1 ≤ q.2) Primrec.nat_le)
  refine ComputablePred.computable_iff.mpr
    ⟨fun p ↦ f (a (p.1 + 2) * 2 ^ p.2,
      omegaApproxNum p.2 * 2 ^ (p.1 + 2) + 2 ^ (p.2 + 1)), hf.comp (hlhs.pair hrhs), ?_⟩
  funext p
  exact congrFun hfeq
    (a (p.1 + 2) * 2 ^ p.2, omegaApproxNum p.2 * 2 ^ (p.1 + 2) + 2 ^ (p.2 + 1))

theorem exists_searchPred {a : ℕ → ℕ}
    (ha : ∀ n : ℕ, (a n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n ≤ chaitinOmega + (2 : ℝ≥0∞)⁻¹ ^ n)
    (n : ℕ) : ∃ t, searchPred a n t := by
  have hbase : ((2 : ℝ≥0∞)⁻¹ ^ (n + 2)) ≠ 0 :=
    pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp))
  obtain ⟨t, ht⟩ := exists_omegaApprox_gt hbase
  refine ⟨t, (searchPred_iff a n t).mpr ?_⟩
  calc (a (n + 2) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + 2)
      ≤ chaitinOmega + (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := ha (n + 2)
    _ ≤ omegaApprox t + (2 : ℝ≥0∞)⁻¹ ^ (n + 2) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2) :=
        add_le_add ht.le le_rfl
    _ = omegaApprox t + (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
        rw [add_assoc]
        exact congrArg _ (inv_two_pow_add_self (n + 1))

theorem searchTime_computable {a : ℕ → ℕ} (ha : Computable a)
    (hex : ∀ n, ∃ t, searchPred a n t) : Computable fun n ↦ Nat.find (hex n) :=
  Computable.find (searchPred_computablePred ha) hex

theorem chaitinOmega_lt_omegaApprox_find {a : ℕ → ℕ}
    (ha : ∀ n : ℕ, chaitinOmega ≤ (a n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n + (2 : ℝ≥0∞)⁻¹ ^ n)
    (hex : ∀ n, ∃ t, searchPred a n t) (n : ℕ) :
    chaitinOmega < omegaApprox (Nat.find (hex n)) + (2 : ℝ≥0∞)⁻¹ ^ n := by
  have hne : ((2 : ℝ≥0∞)⁻¹ ^ (n + 1) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero),
      ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero)⟩
  have hsum : (2 : ℝ≥0∞)⁻¹ ^ (n + 1) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2)
      = (2 : ℝ≥0∞)⁻¹ ^ n := by
    rw [add_assoc, congrArg (HAdd.hAdd ((2 : ℝ≥0∞)⁻¹ ^ (n + 1))) (inv_two_pow_add_self (n + 1))]
    exact inv_two_pow_add_self n
  have hmargin : (2 : ℝ≥0∞)⁻¹ ^ (n + 1) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2) < (2 : ℝ≥0∞)⁻¹ ^ n :=
    hsum ▸ ENNReal.lt_add_right hne (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp)))
  have hP := (searchPred_iff a n (Nat.find (hex n))).mp (Nat.find_spec (hex n))
  refine lt_of_le_of_lt ?_
    (ENNReal.add_lt_add_left (omegaApprox_ne_top (Nat.find (hex n))) hmargin)
  calc chaitinOmega
      ≤ (a (n + 2) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + 2) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := ha (n + 2)
    _ ≤ omegaApprox (Nat.find (hex n)) + (2 : ℝ≥0∞)⁻¹ ^ (n + 1) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2) :=
        add_le_add hP le_rfl
    _ = omegaApprox (Nat.find (hex n))
          + ((2 : ℝ≥0∞)⁻¹ ^ (n + 1) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2)) := add_assoc _ _ _

end InformationTheory.Kolmogorov

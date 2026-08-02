import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Support reduction for a convex objective on a transportation polytope

A nonnegative weight vector `q : ι → ℝ` acting on a family of rows `A : ι → X → ℝ` can always be
replaced by one supported on at most `Fintype.card X` indices, without moving the aggregate
`fun x ↦ ∑ i, q i * A i x` and without decreasing the value of a convex objective `f`.

This is the mechanism behind cardinality bounds for auxiliary random variables: the rows are the
conditional laws `A i = p(· | i)` on the alphabet `X`, the aggregate is the input law `p(x)` that
must be preserved, and `f` is the (convex) functional being maximized.  The argument is elementary
— a nonzero linear dependence among more than `Fintype.card X` rows moves `q` along a line
inside the polytope, and convexity of `f` says one of the two endpoints of that line does at least
as well as `q` while killing one coordinate.

## Main statements

* `exists_support_card_le_of_convexOn` — the support reduction described above.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

variable {ι : Type*} [Fintype ι] {X : Type*} [Fintype X]

private lemma exists_dep_of_card_lt (A : ι → X → ℝ) (q : ι → ℝ)
    (hcard : Fintype.card X < {i | q i ≠ 0}.ncard) :
    ∃ c : ι → ℝ, (∀ x, ∑ i, c i * A i x = 0) ∧ (∀ i, q i = 0 → c i = 0) ∧ c ≠ 0 := by
  classical
  set S : Finset ι := Finset.univ.filter fun i ↦ q i ≠ 0 with hS
  have hmemS : ∀ i, i ∈ S ↔ q i ≠ 0 := by intro i; simp [hS]
  have hScard : Fintype.card X < S.card := by
    rwa [show {i | q i ≠ 0} = (↑S : Set ι) by ext i; simp [hS], Set.ncard_coe_finset] at hcard
  have hdep : ¬ LinearIndependent ℝ fun i : {x // x ∈ S} ↦ A i.1 := by
    intro hli
    have h1 := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
    omega
  obtain ⟨g, hgsum, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.mp hdep
  set c : ι → ℝ := fun i ↦ if h : i ∈ S then g ⟨i, h⟩ else 0 with hc
  have hcS : ∀ (i : ι) (h : i ∈ S), c i = g ⟨i, h⟩ := fun i h ↦ dif_pos h
  have hcnot : ∀ i, i ∉ S → c i = 0 := fun i h ↦ dif_neg h
  refine ⟨c, fun x ↦ ?_, fun i hi ↦ hcnot i fun hiS ↦ (hmemS i).mp hiS hi, ?_⟩
  · have hval : ∑ i : {x // x ∈ S}, g i * A i.1 x = 0 := by
      have := congrFun hgsum x
      rw [Finset.sum_apply] at this
      simpa using this
    have hsplit : ∑ i, c i * A i x = ∑ i ∈ S, c i * A i x :=
      (Finset.sum_subset (Finset.subset_univ S) fun i _ hiS ↦ by rw [hcnot i hiS, zero_mul]).symm
    calc ∑ i, c i * A i x = ∑ i ∈ S.attach, c i.1 * A i.1 x := by
          rw [Finset.sum_attach S fun i ↦ c i * A i x]; exact hsplit
      _ = ∑ i : {x // x ∈ S}, g i * A i.1 x := by
          rw [Finset.univ_eq_attach]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [hcS i.1 i.2]
      _ = 0 := hval
  · intro hzero
    exact hi₁ (by rw [← hcS i₁.1 i₁.2, hzero, Pi.zero_apply])

private lemma sum_eq_zero_of_dep (A : ι → X → ℝ) (hA : ∀ i, ∑ x, A i x = 1) (c : ι → ℝ)
    (hc : ∀ x, ∑ i, c i * A i x = 0) : ∑ i, c i = 0 := by
  have hswap : ∑ x, ∑ i, c i * A i x = ∑ i, c i := by
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, hA]
  rw [← hswap]
  simp [hc]

private lemma exists_neg_and_pos (c : ι → ℝ) (hc0 : ∑ i, c i = 0) (hcne : c ≠ 0) :
    (∃ i, c i < 0) ∧ ∃ i, 0 < c i := by
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra hall
    exact hcne (funext fun i ↦ not_not.mp fun h ↦ hall ⟨i, h⟩)
  constructor
  · by_contra hall
    have hall' : ∀ i, 0 ≤ c i := fun i ↦ not_lt.mp (not_exists.mp hall i)
    exact hj ((Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hall' i).mp hc0 j (Finset.mem_univ j))
  · by_contra hall
    have hall' : ∀ i, c i ≤ 0 := fun i ↦ not_lt.mp (not_exists.mp hall i)
    have hneg : ∑ i, (-c i) = 0 := by simp [Finset.sum_neg_distrib, hc0]
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ neg_nonneg.mpr (hall' i)).mp hneg j
      (Finset.mem_univ j)
    exact hj (neg_eq_zero.mp this)

private lemma exists_step (q c : ι → ℝ) (hq : 0 ≤ q) (hcs : ∀ i, q i = 0 → c i = 0)
    (hneg : ∃ i, c i < 0) :
    ∃ t : ℝ, 0 < t ∧ 0 ≤ q + t • c ∧ {i | (q + t • c) i ≠ 0} ⊂ {i | q i ≠ 0} := by
  classical
  have hqpos : ∀ i, c i ≠ 0 → 0 < q i := by
    intro i hi
    rcases lt_or_eq_of_le (hq i) with h | h
    · exact h
    · exact absurd (hcs i h.symm) hi
  set N : Finset ι := Finset.univ.filter fun i ↦ c i < 0 with hN
  obtain ⟨j, hj⟩ := hneg
  have hNne : N.Nonempty := ⟨j, by simp [hN, hj]⟩
  obtain ⟨i₀, hi₀N, hi₀min⟩ := Finset.exists_min_image N (fun i ↦ q i / -c i) hNne
  have hi₀ : c i₀ < 0 := by simpa [hN] using hi₀N
  refine ⟨q i₀ / -c i₀, div_pos (hqpos i₀ hi₀.ne) (neg_pos.mpr hi₀), ?_, ?_⟩
  · intro i
    have hqi : (0 : ℝ) ≤ q i := hq i
    have happ : (q + (q i₀ / -c i₀) • c) i = q i + q i₀ / -c i₀ * c i := rfl
    rw [Pi.zero_apply, happ]
    rcases lt_or_ge (c i) 0 with hci | hci
    · have hmem : i ∈ N := by simp [hN, hci]
      have hle : q i₀ / -c i₀ ≤ q i / -c i := hi₀min i hmem
      have hpos : (0 : ℝ) < -c i := neg_pos.mpr hci
      have hmul := (le_div_iff₀ hpos).mp hle
      nlinarith
    · have : 0 ≤ q i₀ / -c i₀ * c i :=
        mul_nonneg (le_of_lt (div_pos (hqpos i₀ hi₀.ne) (neg_pos.mpr hi₀))) hci
      linarith
  · constructor
    · intro i hi
      simp only [Set.mem_setOf_eq] at hi ⊢
      intro hqi
      exact hi (by simp [hqi, hcs i hqi])
    · intro hsub
      have hmem : i₀ ∈ {i | q i ≠ 0} := (hqpos i₀ hi₀.ne).ne'
      have hne := hsub hmem
      simp only [Set.mem_setOf_eq] at hne
      have hc0 : c i₀ ≠ 0 := hi₀.ne
      refine hne ?_
      change q i₀ + q i₀ / -c i₀ * c i₀ = 0
      field_simp
      ring

omit [Fintype ι] in
private lemma le_or_le_of_convexOn (f : (ι → ℝ) → ℝ) (hf : ConvexOn ℝ {q : ι → ℝ | 0 ≤ q} f)
    (q c : ι → ℝ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hp : 0 ≤ q + t • c)
    (hm : 0 ≤ q + s • (-c)) :
    f q ≤ f (q + t • c) ∨ f q ≤ f (q + s • (-c)) := by
  have hst : (0 : ℝ) < s + t := by linarith
  have hlam : (0 : ℝ) < s / (s + t) := div_pos hs hst
  have hmu : (0 : ℝ) < t / (s + t) := div_pos ht hst
  have hsum : s / (s + t) + t / (s + t) = 1 := by field_simp
  have hcomb : (s / (s + t)) • (q + t • c) + (t / (s + t)) • (q + s • (-c)) = q := by
    funext i
    change s / (s + t) * (q i + t * c i) + t / (s + t) * (q i + s * -c i) = q i
    field_simp
    ring
  have hconv := hf.2 (Set.mem_setOf.mpr hp) (Set.mem_setOf.mpr hm) hlam.le hmu.le hsum
  rw [hcomb] at hconv
  simp only [smul_eq_mul] at hconv
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  have hkey : s / (s + t) * f q + t / (s + t) * f q = f q := by
    rw [← add_mul, hsum, one_mul]
  linarith [mul_lt_mul_of_pos_left hcon.1 hlam, mul_lt_mul_of_pos_left hcon.2 hmu]

private lemma exists_support_reduction_aux (A : ι → X → ℝ) (hA : ∀ i, ∑ x, A i x = 1)
    (f : (ι → ℝ) → ℝ) (hf : ConvexOn ℝ {q : ι → ℝ | 0 ≤ q} f) (n : ℕ) :
    ∀ q : ι → ℝ, 0 ≤ q → {i | q i ≠ 0}.ncard ≤ n →
      ∃ q' : ι → ℝ, 0 ≤ q' ∧ (∀ x, ∑ i, q' i * A i x = ∑ i, q i * A i x) ∧ f q ≤ f q' ∧
        {i | q' i ≠ 0}.ncard ≤ Fintype.card X := by
  have hpres : ∀ (q : ι → ℝ) (u : ℝ) (d : ι → ℝ), (∀ x, ∑ i, d i * A i x = 0) →
      ∀ x, ∑ i, (q + u • d) i * A i x = ∑ i, q i * A i x := by
    intro q u d hd x
    have hterm : ∀ i, (q + u • d) i * A i x = q i * A i x + u * (d i * A i x) := by
      intro i
      change (q i + u * d i) * A i x = _
      ring
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_add_distrib, ← Finset.mul_sum, hd x,
      mul_zero, add_zero]
  induction n with
  | zero => exact fun q hq hn ↦ ⟨q, hq, fun _ ↦ rfl, le_rfl, hn.trans (Nat.zero_le _)⟩
  | succ n ih =>
    intro q hq hn
    by_cases hsmall : {i | q i ≠ 0}.ncard ≤ Fintype.card X
    · exact ⟨q, hq, fun _ ↦ rfl, le_rfl, hsmall⟩
    obtain ⟨c, hc0, hcs, hcne⟩ := exists_dep_of_card_lt A q (not_le.mp hsmall)
    obtain ⟨⟨ineg, hineg⟩, ipos, hipos⟩ := exists_neg_and_pos c (sum_eq_zero_of_dep A hA c hc0) hcne
    have hnc0 : ∀ x, ∑ i, (-c) i * A i x = 0 := by
      intro x
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hc0 x, neg_zero]
    obtain ⟨t, ht, hpt, hsubt⟩ := exists_step q c hq hcs ⟨ineg, hineg⟩
    obtain ⟨s, hs, hps, hsubs⟩ :=
      exists_step q (-c) hq (fun i hi ↦ by simp [Pi.neg_apply, hcs i hi])
        ⟨ipos, by simpa using hipos⟩
    rcases le_or_le_of_convexOn f hf q c s t hs ht hpt hps with hle | hle
    · have hlt : {i | (q + t • c) i ≠ 0}.ncard ≤ n := by
        have := Set.ncard_lt_ncard hsubt (Set.toFinite _)
        omega
      obtain ⟨q', hq', hq'c, hq'f, hq'card⟩ := ih _ hpt hlt
      exact ⟨q', hq', fun x ↦ (hq'c x).trans (hpres q t c hc0 x), hle.trans hq'f, hq'card⟩
    · have hlt : {i | (q + s • (-c)) i ≠ 0}.ncard ≤ n := by
        have := Set.ncard_lt_ncard hsubs (Set.toFinite _)
        omega
      obtain ⟨q', hq', hq'c, hq'f, hq'card⟩ := ih _ hps hlt
      exact ⟨q', hq', fun x ↦ (hq'c x).trans (hpres q s (-c) hnc0 x), hle.trans hq'f, hq'card⟩

/-- A nonnegative weight vector can be replaced by one supported on at most `Fintype.card X`
indices, keeping the aggregate `fun x ↦ ∑ i, q i * A i x` and not decreasing a convex objective
`f`, provided every row `A i` sums to one. -/
theorem exists_support_card_le_of_convexOn (A : ι → X → ℝ) (hA : ∀ i, ∑ x, A i x = 1)
    (f : (ι → ℝ) → ℝ) (hf : ConvexOn ℝ {q : ι → ℝ | 0 ≤ q} f) (q : ι → ℝ) (hq : 0 ≤ q) :
    ∃ q' : ι → ℝ, 0 ≤ q' ∧ (∀ x, ∑ i, q' i * A i x = ∑ i, q i * A i x) ∧ f q ≤ f q' ∧
      {i | q' i ≠ 0}.ncard ≤ Fintype.card X :=
  exists_support_reduction_aux A hA f hf (Fintype.card ι) q hq <| by
    calc {i | q i ≠ 0}.ncard
        ≤ (Set.univ : Set ι).ncard := Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      _ = Fintype.card ι := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]

end InformationTheory.Shannon.BroadcastChannel.Marton

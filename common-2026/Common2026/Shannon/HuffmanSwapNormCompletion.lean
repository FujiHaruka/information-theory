import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Common2026.Meta.EntryPoint
import Common2026.Shannon.HuffmanSwapNormProof

/-!
# T1-A'' — Kraft completion (shorten-to-Kraft=1)

`HuffmanSwapNormProof.lean` の keystone `exists_two_equal_longest` は **Kraft 和が
ちょうど `1`** の符号にしか適用できない。一般の feasible 符号 (`Kraft ≤ 1`) を
keystone に乗せるための前段が本 file。

## 主結果

`shorten_to_kraft_one` — 正値 `ll : β → ℕ` で `∑ 2^(-ll x) ≤ 1` (かつ `2 ≤ card β`)
ならば、正値 `l1 ≤ ll` (各点) で `∑ 2^(-l1 x) = 1` が存在する。各点 `l1 x ≤ ll x` から
expected length 非増加が直ちに従う (確率は非負)。

## Approach (genuine, no false-chain)

自然数 Kraft 和 `N M l = ∑ 2^(M - l c)` (M = 最大語長) を介す。実 Kraft `∑ 2^(-l c)` と
`N` は `realKraft = N / 2^M` で結ばれ、`realKraft ≤ 1 ↔ N ≤ 2^M`、`realKraft = 1 ↔ N = 2^M`。

induction は **総語長 `∑ ll x`** 上の strong induction:
- Kraft = 1 ならそのまま。
- Kraft < 1 のとき、最大語長 leaf `m` を 1 縮める。最大語長 `L` の項は `2^(M-L)=2^0=1`
  を `N` に寄与するので、縮めると `N → N+1`。`N < 2^M` より `N+1 ≤ 2^M`、つまり新 Kraft ≤ 1。
  さらに `card ≥ 2` のとき Kraft < 1 ならば `L ≥ 2` (もし `L = 1` なら全語長 1 ⇒
  `Kraft = card/2 ≥ 1`、矛盾)、よって縮めても正値を保つ。総語長が真に減るので IH。
-/

namespace InformationTheory.Shannon.Huffman

open scoped BigOperators

variable {β : Type*} [Fintype β] [DecidableEq β]

/-! ### 自然数 Kraft 和 ↔ 実 Kraft 和 -/

omit [DecidableEq β] in
/-- **Key bridge identity**: `((∑ c, 2^(M - l c) : ℕ) : ℝ) = 2^M · ∑ c, (2:ℝ)^(-(l c))`.
real / nat Kraft 和を結ぶ中核等式 (`kraft_one_nat_sum` の `hterm` を再利用). -/
lemma natKraft_cast_eq
    (l : β → ℕ) (M : ℕ) (hM : ∀ c, l c ≤ M) :
    ((∑ c : β, 2 ^ (M - l c) : ℕ) : ℝ)
      = (2 : ℝ) ^ M * ∑ c : β, ((2 : ℝ)) ^ (-(l c : ℤ)) := by
  push_cast
  have hterm : ∀ c : β,
      ((2 : ℝ)) ^ (M - l c) = (2 : ℝ) ^ M * ((2 : ℝ)) ^ (-(l c : ℤ)) := by
    intro c
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hle : l c ≤ M := hM c
    have hzpow : (2 : ℝ) ^ M * ((2 : ℝ)) ^ (-(l c : ℤ))
        = (2 : ℝ) ^ ((M : ℤ) - (l c : ℤ)) := by
      rw [zpow_sub₀ h2, ← zpow_natCast (2 : ℝ) M, zpow_neg, div_eq_mul_inv]
    rw [hzpow, ← zpow_natCast (2 : ℝ) (M - l c)]
    congr 1
    push_cast [hle]
    omega
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.mul_sum]

omit [DecidableEq β] in
/-- 実 Kraft 和 `≤ 1` と 自然数 Kraft 和 `≤ 2^M` の同値 (`M` が上界のとき). -/
lemma realKraft_le_one_iff_nat_le
    (l : β → ℕ) (M : ℕ) (hM : ∀ c, l c ≤ M) :
    (∑ c : β, ((2 : ℝ)) ^ (-(l c : ℤ)) ≤ 1) ↔ (∑ c : β, 2 ^ (M - l c) ≤ 2 ^ M) := by
  have hcast := natKraft_cast_eq l M hM
  have h2M_pos : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  constructor
  · intro h
    have : ((∑ c : β, 2 ^ (M - l c) : ℕ) : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by
      rw [hcast]; push_cast
      calc (2 : ℝ) ^ M * ∑ c : β, ((2 : ℝ)) ^ (-(l c : ℤ))
          ≤ (2 : ℝ) ^ M * 1 := by exact mul_le_mul_of_nonneg_left h (le_of_lt h2M_pos)
        _ = (2 : ℝ) ^ M := by ring
    exact_mod_cast this
  · intro h
    have hr : ((∑ c : β, 2 ^ (M - l c) : ℕ) : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast h
    rw [hcast] at hr
    push_cast at hr
    have hr' : (2 : ℝ) ^ M * ∑ c : β, ((2 : ℝ)) ^ (-(l c : ℤ)) ≤ (2 : ℝ) ^ M * 1 := by
      rw [mul_one]; exact hr
    exact le_of_mul_le_mul_left hr' h2M_pos

omit [DecidableEq β] in
/-- 実 Kraft 和 `= 1` と 自然数 Kraft 和 `= 2^M` の同値 (`M` が上界のとき). -/
lemma realKraft_eq_one_iff_nat_eq
    (l : β → ℕ) (M : ℕ) (hM : ∀ c, l c ≤ M) :
    (∑ c : β, ((2 : ℝ)) ^ (-(l c : ℤ)) = 1) ↔ (∑ c : β, 2 ^ (M - l c) = 2 ^ M) := by
  have hcast := natKraft_cast_eq l M hM
  have h2M_pos : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  constructor
  · intro h
    have : ((∑ c : β, 2 ^ (M - l c) : ℕ) : ℝ) = ((2 ^ M : ℕ) : ℝ) := by
      rw [hcast, h]; push_cast; ring
    exact_mod_cast this
  · intro h
    have hr : ((∑ c : β, 2 ^ (M - l c) : ℕ) : ℝ) = ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast h
    rw [hcast] at hr
    push_cast at hr
    have hr' : (2 : ℝ) ^ M * ∑ c : β, ((2 : ℝ)) ^ (-(l c : ℤ)) = (2 : ℝ) ^ M * 1 := by
      rw [mul_one]; exact hr
    exact mul_left_cancel₀ (ne_of_gt h2M_pos) hr'

/-! ### 縮約 step -/

/-- **shorten-to-Kraft=1 (主結果, 総語長 induction motor)**: 正値 feasible 符号は、
各点でより短い正値完全符号 (Kraft = 1) に縮められる。`n = ∑ ll x` 上の strong induction. -/
private theorem shorten_to_kraft_one_aux
    [Nonempty β] (n : ℕ)
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (h_card : 2 ≤ Fintype.card β)
    (hn : (∑ x : β, ll x) = n) :
    ∃ l1 : β → ℕ, (∀ x, 0 < l1 x) ∧ (∀ x, l1 x ≤ ll x) ∧
      ∑ x : β, ((2 : ℝ)) ^ (-(l1 x : ℤ)) = 1 := by
  induction n using Nat.strong_induction_on generalizing ll with
  | _ n IH =>
    classical
    -- max-length leaf m, L = ll m
    obtain ⟨m, _, hm_max⟩ :=
      Finset.exists_max_image (Finset.univ : Finset β) ll Finset.univ_nonempty
    set L := ll m with hL_def
    have hL_max : ∀ c, ll c ≤ L := fun c => hm_max c (Finset.mem_univ c)
    -- Kraft = 1 か Kraft < 1 で場合分け
    by_cases h_eq : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) = 1
    · exact ⟨ll, hll_pos, fun _ => le_refl _, h_eq⟩
    · -- Kraft < 1
      have h_lt : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) < 1 := lt_of_le_of_ne hll_kraft h_eq
      -- nat form: N(ll, L) < 2^L
      have h_nat_lt : (∑ c : β, 2 ^ (L - ll c)) < 2 ^ L := by
        by_contra hge
        push Not at hge
        have hle : (∑ c : β, 2 ^ (L - ll c)) ≤ 2 ^ L :=
          (realKraft_le_one_iff_nat_le ll L hL_max).mp hll_kraft
        have heq : (∑ c : β, 2 ^ (L - ll c)) = 2 ^ L := le_antisymm hle hge
        exact h_eq ((realKraft_eq_one_iff_nat_eq ll L hL_max).mpr heq)
      -- L ≥ 2: もし L = 1 なら全 ll c = 1 で Kraft = card/2 ≥ 1, 矛盾
      have hL_ge_2 : 2 ≤ L := by
        by_contra hL_lt
        push Not at hL_lt
        have hL_eq_1 : L = 1 := le_antisymm (by omega) (hll_pos m)
        -- 全 ll c = 1
        have hall_one : ∀ c, ll c = 1 := fun c => le_antisymm (hL_eq_1 ▸ hL_max c) (hll_pos c)
        have hsum_eq : (∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)))
            = ∑ x : β, ((2 : ℝ)) ^ (-(1 : ℤ)) := by
          apply Finset.sum_congr rfl
          intro x _; rw [hall_one x]; norm_num
        rw [hsum_eq] at h_lt
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h_lt
        have h2 : ((2 : ℝ)) ^ (-(1 : ℤ)) = 1 / 2 := by norm_num
        rw [h2] at h_lt
        have hcard_real : (2 : ℝ) ≤ (Fintype.card β : ℝ) := by exact_mod_cast h_card
        nlinarith [h_lt, hcard_real]
      -- shortened function ll'
      set ll' : β → ℕ := Function.update ll m (L - 1) with hll'_def
      have hll'_m : ll' m = L - 1 := by rw [hll'_def]; simp
      have hll'_off : ∀ x, x ≠ m → ll' x = ll x := by
        intro x hx; rw [hll'_def]; simp [hx]
      -- positivity of ll'
      have hll'_pos : ∀ x, 0 < ll' x := by
        intro x
        by_cases hx : x = m
        · rw [hx, hll'_m]; omega
        · rw [hll'_off x hx]; exact hll_pos x
      -- pointwise ll' ≤ ll
      have hll'_le : ∀ x, ll' x ≤ ll x := by
        intro x
        by_cases hx : x = m
        · rw [hx, hll'_m]; omega
        · rw [hll'_off x hx]
      -- ll' c ≤ L still (so L is a valid bound for ll')
      have hll'_max : ∀ c, ll' c ≤ L := fun c => le_trans (hll'_le c) (hL_max c)
      -- total length strictly decreases
      have htotal_lt : (∑ x : β, ll' x) < n := by
        rw [← hn]
        rw [← Finset.add_sum_erase _ ll (Finset.mem_univ m),
            ← Finset.add_sum_erase _ ll' (Finset.mem_univ m)]
        have h_erase_eq : (∑ x ∈ (Finset.univ : Finset β).erase m, ll' x)
            = ∑ x ∈ (Finset.univ : Finset β).erase m, ll x := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hll'_off x (Finset.ne_of_mem_erase hx)
        rw [h_erase_eq, hll'_m]
        have : 0 < L := hll_pos m
        omega
      -- nat Kraft for ll': N(ll', L) = N(ll, L) + 1 ≤ 2^L
      have h_nat'_eq : (∑ c : β, 2 ^ (L - ll' c)) = (∑ c : β, 2 ^ (L - ll c)) + 1 := by
        rw [← Finset.add_sum_erase _ (fun c => 2 ^ (L - ll c)) (Finset.mem_univ m),
            ← Finset.add_sum_erase _ (fun c => 2 ^ (L - ll' c)) (Finset.mem_univ m)]
        have h_erase_eq : (∑ x ∈ (Finset.univ : Finset β).erase m, 2 ^ (L - ll' x))
            = ∑ x ∈ (Finset.univ : Finset β).erase m, 2 ^ (L - ll x) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hll'_off x (Finset.ne_of_mem_erase hx)]
        rw [h_erase_eq, hll'_m]
        -- m term: 2^(L - (L-1)) = 2^1 = 2 vs 2^(L - L) = 2^0 = 1
        have hm_term' : (2 : ℕ) ^ (L - (L - 1)) = 2 := by
          have : L - (L - 1) = 1 := by omega
          rw [this]; rfl
        have hm_term : (2 : ℕ) ^ (L - L) = 1 := by simp
        rw [hm_term', hm_term]
        omega
      have h_nat'_le : (∑ c : β, 2 ^ (L - ll' c)) ≤ 2 ^ L := by
        rw [h_nat'_eq]; omega
      have hll'_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll' x : ℤ)) ≤ 1 :=
        (realKraft_le_one_iff_nat_le ll' L hll'_max).mpr h_nat'_le
      -- apply IH
      obtain ⟨l1, hl1_pos, hl1_le, hl1_kraft⟩ :=
        IH (∑ x : β, ll' x) htotal_lt ll' hll'_pos hll'_kraft rfl
      exact ⟨l1, hl1_pos, fun x => le_trans (hl1_le x) (hll'_le x), hl1_kraft⟩

/-- **shorten-to-Kraft=1 (主結果)**: 正値 feasible 符号は、各点でより短い正値完全符号
(Kraft = 1) に縮められる。 -/
@[entry_point]
theorem shorten_to_kraft_one
    [Nonempty β]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (h_card : 2 ≤ Fintype.card β) :
    ∃ l1 : β → ℕ, (∀ x, 0 < l1 x) ∧ (∀ x, l1 x ≤ ll x) ∧
      ∑ x : β, ((2 : ℝ)) ^ (-(l1 x : ℤ)) = 1 :=
  shorten_to_kraft_one_aux (∑ x : β, ll x) ll hll_pos hll_kraft h_card rfl

end InformationTheory.Shannon.Huffman

import Common2026.Meta.EntryPoint
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Dedup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Shannon コード Kraft 逆向き (prefix code 存在構成)

B-8' ムーンショット ([`docs/shannon/shannon-code-kraft-reverse-plan.md`](../../docs/shannon/shannon-code-kraft-reverse-plan.md))。
Cover-Thomas 5.2.1 reverse direction / McMillan の逆形。

任意の正整数列 `l : α → ℕ` が Kraft 不等式 `Σ_a D^{-l(a)} ≤ 1` を充足するとき、
長さ `l(a)` の **prefix code** が存在する。

## 主定理

* `exists_prefix_code_of_kraft` — `Σ_a D^{-l(a)} ≤ 1` (`D ≥ 2`, `0 < l a`) ⟹
  ∃ `c : α → List (Fin D)` injective かつ prefix-free で `(c a).length = l a`.

## 設計メモ

- **D-進数エンコーダ `toBaseDLen`**: most-significant-first 固定長 `List (Fin D)`。
- **Greedy 構成**: `Finset.univ.toList` を `l` の昇順に `List.mergeSort` で並べ替え、累積和
  `slotStart k := Σ_{j < k} D^(L - l (as[j]))` を取り、各 `as[k]` の code-word を
  `toBaseDLen D (l (as[k])) (slotStart k / D^(L - l (as[k])))` で定義。
-/

namespace InformationTheory.Shannon.ShannonCodeKraftReverse

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Phase A — 定義 -/

/-- **MSB-first base-`D` digit expansion of length `L` of `n`**.

For `n < D^L`, this is the canonical length-`L` digit list (most-significant first). -/
def toBaseDLen (D : ℕ) [NeZero D] (L n : ℕ) : List (Fin D) :=
  List.ofFn (n := L) fun i =>
    ⟨(n / D ^ (L - 1 - (i : ℕ))) % D,
      Nat.mod_lt _ (Nat.pos_of_neZero D)⟩

/-- **Prefix-free 述語**: 異なる `a, b` で `c a` が `c b` の prefix にならない. -/
def IsPrefixFree {D : ℕ} (c : α → List (Fin D)) : Prop :=
  ∀ a b : α, a ≠ b → ¬ c a <+: c b

/-! ### Phase B — `toBaseDLen` 補助補題 -/

/-- 長さは `L`. -/
@[simp] lemma toBaseDLen_length (D : ℕ) [NeZero D] (L n : ℕ) :
    (toBaseDLen D L n).length = L := by
  unfold toBaseDLen
  exact List.length_ofFn

/-- **核補題**: `L₁ ≤ L₂` のとき `(toBaseDLen D L₂ n).take L₁ = toBaseDLen D L₁ (n / D^(L₂ - L₁))`.
MSB-first 表現の特徴: 上位 `L₁` digit は `n / D^(L₂ - L₁)` の `L₁` digit と一致. -/
lemma toBaseDLen_take (D : ℕ) [NeZero D] {L₁ L₂ : ℕ} (h : L₁ ≤ L₂) (n : ℕ) :
    (toBaseDLen D L₂ n).take L₁ = toBaseDLen D L₁ (n / D ^ (L₂ - L₁)) := by
  apply List.ext_getElem
  · -- 長さ一致: min L₁ L₂ = L₁ ↔ L₁ ≤ L₂
    rw [List.length_take, toBaseDLen_length, toBaseDLen_length, min_eq_left h]
  · -- 各 i < L₁ で要素一致
    intro i hi₁ _
    rw [List.length_take, toBaseDLen_length, min_eq_left h] at hi₁
    rw [List.getElem_take]
    -- toBaseDLen D L₂ n の i-th = ⟨(n / D^(L₂-1-i)) % D, _⟩
    unfold toBaseDLen
    rw [List.getElem_ofFn, List.getElem_ofFn]
    -- (n / D^(L₂ - 1 - i)) % D = ((n / D^(L₂ - L₁)) / D^(L₁ - 1 - i)) % D
    apply Fin.ext
    simp only
    -- 算術: (n / D^(L₂ - L₁)) / D^(L₁ - 1 - i) = n / D^(L₂ - 1 - i)
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    have : L₂ - L₁ + (L₁ - 1 - i) = L₂ - 1 - i := by omega
    rw [this]

/-- `IsPrefix` 特徴づけ (forward direction): codewords are prefixes ⟹
`toBaseDLen D L₁ n₁ = toBaseDLen D L₁ (n₂ / D^(L₂-L₁))`. -/
lemma toBaseDLen_eq_of_isPrefix (D : ℕ) [NeZero D] {L₁ L₂ : ℕ}
    (h : L₁ ≤ L₂) {n₁ n₂ : ℕ}
    (hpref : toBaseDLen D L₁ n₁ <+: toBaseDLen D L₂ n₂) :
    toBaseDLen D L₁ n₁ = toBaseDLen D L₁ (n₂ / D ^ (L₂ - L₁)) := by
  -- toBaseDLen D L₁ n₁ = (toBaseDLen D L₂ n₂).take L₁ via prefix
  have h_len : (toBaseDLen D L₁ n₁).length = L₁ := toBaseDLen_length _ _ _
  have h_take_eq :
      toBaseDLen D L₁ n₁ = (toBaseDLen D L₂ n₂).take (toBaseDLen D L₁ n₁).length := by
    rw [List.prefix_iff_eq_take] at hpref
    exact hpref
  rw [h_take_eq, h_len, toBaseDLen_take D h]

/-- Strict variant: if `n₁, n₂ < D^L`, `toBaseDLen D L n₁ = toBaseDLen D L n₂` ⟹ `n₁ = n₂`. -/
lemma toBaseDLen_injOn_lt (D : ℕ) [NeZero D] (L : ℕ) {n₁ n₂ : ℕ}
    (h₁ : n₁ < D ^ L) (h₂ : n₂ < D ^ L)
    (heq : toBaseDLen D L n₁ = toBaseDLen D L n₂) :
    n₁ = n₂ := by
  -- 帰納 `∀ k ≤ L, n₁ % D^k = n₂ % D^k`、k = L で `n₁ = n₂` (両方 < D^L).
  have key : ∀ k, k ≤ L → n₁ % D ^ k = n₂ % D ^ k := by
    intro k hk
    induction k with
    | zero => simp [pow_zero, Nat.mod_one]
    | succ k ih =>
      have ihk : n₁ % D ^ k = n₂ % D ^ k := ih (Nat.le_of_succ_le hk)
      -- digit-by-digit 一致: (n / D^k) % D は MSB-first 表現の (L-1-k)-th index
      have hi_canc : L - 1 - (L - 1 - k) = k := by omega
      have h_idx_lt : L - 1 - k < L := by omega
      have h_dig : (n₁ / D ^ k) % D = (n₂ / D ^ k) % D := by
        -- Extract (L-1-k)-th digit from both, use heq
        have h_get_left :
            (toBaseDLen D L n₁).get
              ⟨L - 1 - k, by rw [toBaseDLen_length]; exact h_idx_lt⟩
              = (toBaseDLen D L n₂).get
                  ⟨L - 1 - k, by rw [toBaseDLen_length]; exact h_idx_lt⟩ := by
          rw [List.get_eq_getElem, List.get_eq_getElem]
          congr 1
        unfold toBaseDLen at h_get_left
        rw [List.get_ofFn, List.get_ofFn] at h_get_left
        have := Fin.val_eq_of_eq h_get_left
        simp only [Fin.cast_mk, hi_canc] at this
        exact this
      -- n % D^(k+1) = (n % D^k) + D^k * ((n / D^k) % D)  via Nat.mod_pow_succ
      rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ihk, h_dig]
  have hL := key L (le_refl L)
  rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hL
  exact hL

/-! ### Phase C — Greedy 構成 -/

/-- `α` 上の `l` 昇順 sort. -/
noncomputable def sortedByLen (l : α → ℕ) : List α :=
  List.mergeSort (Finset.univ : Finset α).toList (fun a b => decide (l a ≤ l b))

omit [DecidableEq α] in
lemma sortedByLen_length (l : α → ℕ) :
    (sortedByLen l).length = Fintype.card α := by
  unfold sortedByLen
  rw [List.length_mergeSort, Finset.length_toList]
  exact Finset.card_univ


omit [DecidableEq α] in
lemma mem_sortedByLen (l : α → ℕ) (a : α) : a ∈ sortedByLen l := by
  unfold sortedByLen
  rw [List.mem_mergeSort]
  exact Finset.mem_toList.mpr (Finset.mem_univ a)

omit [DecidableEq α] in
lemma sortedByLen_pairwise_le (l : α → ℕ) :
    (sortedByLen l).Pairwise (fun a b => l a ≤ l b) := by
  unfold sortedByLen
  have h := List.pairwise_mergeSort (le := fun a b => decide (l a ≤ l b))
    (l := (Finset.univ : Finset α).toList)
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hab hbc)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _)
  refine h.imp ?_
  intro a b hab
  simpa using hab

/-- 累積和 `slotStart k`: `take k` で取った sorted-list 先頭 `k` 個 element の `D^(L - l a)` の和.
`k ≥ |α|` のときは全体和に飽和. -/
noncomputable def slotStart (D : ℕ) (l : α → ℕ) (L : ℕ) (k : ℕ) : ℕ :=
  ((sortedByLen l).take k).map (fun a => D ^ (L - l a)) |>.sum


omit [DecidableEq α] in
/-- 単調性. -/
lemma slotStart_mono (D : ℕ) (l : α → ℕ) (L : ℕ) {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    slotStart D l L k₁ ≤ slotStart D l L k₂ := by
  unfold slotStart
  apply List.Sublist.sum_le_sum
  · -- (take k₁ as).map f <+ (take k₂ as).map f
    apply List.Sublist.map
    exact (List.take_prefix_take_left h).sublist
  · intro a _; exact Nat.zero_le _

omit [DecidableEq α] in
/-- `slotStart (k+1) = slotStart k + D^(L - l (as[k]))`. -/
lemma slotStart_succ (D : ℕ) (l : α → ℕ) (L : ℕ) {k : ℕ}
    (hk : k < (sortedByLen l).length) :
    slotStart D l L (k + 1) =
      slotStart D l L k + D ^ (L - l ((sortedByLen l)[k]'hk)) := by
  unfold slotStart
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
      List.map_append, List.sum_append]
  simp

omit [DecidableEq α] in
/-- 不要 case (`k ≥ length`). -/
lemma slotStart_of_ge (D : ℕ) (l : α → ℕ) (L : ℕ) {k : ℕ}
    (hk : (sortedByLen l).length ≤ k) :
    slotStart D l L k = slotStart D l L (sortedByLen l).length := by
  unfold slotStart
  rw [List.take_of_length_le hk, List.take_length]

omit [DecidableEq α] in
/-- 全体合計 (Σ over α 形と一致). -/
lemma slotStart_card_eq_sum (D : ℕ) (l : α → ℕ) (L : ℕ) :
    slotStart D l L (Fintype.card α) = ∑ a : α, D ^ (L - l a) := by
  -- |α| = (sortedByLen l).length なので take = id.
  rw [slotStart_of_ge D l L (by rw [sortedByLen_length])]
  unfold slotStart
  rw [List.take_length]
  -- (List.map f (sortedByLen l)).sum = Σ_{a ∈ Finset.univ} f a
  -- via List.sum = Multiset.sum (sortedByLen l).map f
  -- and (sortedByLen l).toFinset = Finset.univ
  have hperm : (sortedByLen l).Perm (Finset.univ : Finset α).toList := by
    unfold sortedByLen
    exact List.mergeSort_perm _ _
  rw [show (List.map (fun a => D ^ (L - l a)) (sortedByLen l)).sum
        = (List.map (fun a => D ^ (L - l a)) ((Finset.univ : Finset α).toList)).sum
        from (hperm.map _).sum_eq]
  -- ((univ.toList).map f).sum = univ.sum f
  rw [← Finset.sum_map_val]
  simp [Finset.toList]

/-! ### Phase D — Kraft 仮定からの slot 上界 -/

omit [DecidableEq α] in
/-- Kraft 充足を `Nat` 形に: `Σ_a D^(L - l(a)) ≤ D^L`.
鍵: `Σ_a (D : ℝ)^(L - l a) = (D : ℝ)^L · Σ_a (D : ℝ)^(-(l a : ℤ)) ≤ D^L`. -/
lemma kraft_sum_nat_le_of_real
    {D : ℕ} (hD : 2 ≤ D) (l : α → ℕ) (L : ℕ) (hL : ∀ a, l a ≤ L)
    (hk : ∑ a : α, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    (∑ a : α, D ^ (L - l a)) ≤ D ^ L := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.le_of_lt (Nat.lt_of_lt_of_le (by norm_num) hD)
  -- Cast to ℝ and use D^L * Kraft ≤ D^L * 1
  rw [show (∑ a : α, D ^ (L - l a) : ℕ) = ((∑ a : α, D ^ (L - l a) : ℕ) : ℕ) from rfl]
  -- Strategy: prove the real version, then cast back.
  have h_real_sum_eq : ((∑ a : α, D ^ (L - l a) : ℕ) : ℝ)
      = (D : ℝ) ^ L * ∑ a : α, (D : ℝ) ^ (-(l a : ℤ)) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    have hla : l a ≤ L := hL a
    have hDne : (D : ℝ) ≠ 0 := ne_of_gt hD0
    -- Show: (D : ℝ)^(L - l a) = D^L * D^(-(l a : ℤ))
    rw [zpow_neg, zpow_natCast]
    -- Goal: ↑D ^ (L - l a) = ↑D ^ L * (↑D ^ ↑(l a))⁻¹
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hDne), ← pow_add,
        Nat.sub_add_cancel hla]
  have h_real_bound : ((∑ a : α, D ^ (L - l a) : ℕ) : ℝ) ≤ (D : ℝ) ^ L := by
    rw [h_real_sum_eq]
    have hLpow_pos : (0 : ℝ) < (D : ℝ) ^ L := pow_pos hD0 L
    calc (D : ℝ) ^ L * ∑ a, (D : ℝ) ^ (-(l a : ℤ))
        ≤ (D : ℝ) ^ L * 1 := by
          apply mul_le_mul_of_nonneg_left hk hLpow_pos.le
      _ = (D : ℝ) ^ L := by ring
  -- Cast back: real ≤ ⇒ Nat ≤
  exact_mod_cast h_real_bound

omit [DecidableEq α] in
/-- `slotStart` の上界. -/
lemma slotStart_le_pow
    {D : ℕ} (hD : 2 ≤ D) (l : α → ℕ) (L : ℕ) (hL : ∀ a, l a ≤ L)
    (hk : ∑ a : α, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1)
    (k : ℕ) :
    slotStart D l L k ≤ D ^ L := by
  -- slotStart は monotone, so slotStart k ≤ slotStart (Fintype.card α) = Σ_a D^(L - l a) ≤ D^L.
  calc slotStart D l L k
      ≤ slotStart D l L (Fintype.card α) := by
        rcases le_or_gt k (Fintype.card α) with hk' | hk'
        · exact slotStart_mono D l L hk'
        · rw [slotStart_of_ge D l L (by rw [sortedByLen_length]; exact Nat.le_of_lt hk')]
          rw [show Fintype.card α = (sortedByLen l).length from (sortedByLen_length l).symm]
    _ = ∑ a : α, D ^ (L - l a) := slotStart_card_eq_sum D l L
    _ ≤ D ^ L := kraft_sum_nat_le_of_real hD l L hL hk

/-! ### Phase E — code の構成と主定理 -/

/-- α における sort 後の位置. -/
noncomputable def sortedIndex (l : α → ℕ) (a : α) : ℕ :=
  (sortedByLen l).idxOf a

lemma sortedIndex_lt (l : α → ℕ) (a : α) :
    sortedIndex l a < (sortedByLen l).length := by
  classical
  unfold sortedIndex
  rw [List.idxOf_lt_length_iff]
  exact mem_sortedByLen l a

lemma getElem_sortedByLen_sortedIndex (l : α → ℕ) (a : α) :
    (sortedByLen l)[sortedIndex l a]'(sortedIndex_lt l a) = a := by
  unfold sortedIndex
  exact List.getElem_idxOf _

lemma sortedIndex_injective (l : α → ℕ) :
    Function.Injective (sortedIndex l) := by
  intro a b hab
  have ha : (sortedByLen l)[sortedIndex l a]'(sortedIndex_lt l a) = a :=
    getElem_sortedByLen_sortedIndex l a
  have hb : (sortedByLen l)[sortedIndex l b]'(sortedIndex_lt l b) = b :=
    getElem_sortedByLen_sortedIndex l b
  -- index 等しい ⇒ getElem 等しい ⇒ a = b
  have : (sortedByLen l)[sortedIndex l a]'(sortedIndex_lt l a)
       = (sortedByLen l)[sortedIndex l b]'(sortedIndex_lt l b) := by
    congr 1
  rw [ha, hb] at this
  exact this

/-- 主 code 構成. -/
noncomputable def shannonFanoCode {D : ℕ} [NeZero D] (l : α → ℕ) (L : ℕ) (a : α) :
    List (Fin D) :=
  toBaseDLen D (l a) (slotStart D l L (sortedIndex l a) / D ^ (L - l a))

@[simp] lemma shannonFanoCode_length {D : ℕ} [NeZero D] (l : α → ℕ) (L : ℕ) (a : α) :
    (shannonFanoCode (D := D) l L a).length = l a := by
  unfold shannonFanoCode
  exact toBaseDLen_length _ _ _

omit [DecidableEq α] in
/-- **Phase D の鍵不等式**: `j < k` (in sortedByLen) で `slotStart j + D^(L - l (as[j])) ≤ slotStart k`. -/
lemma slotStart_gap
    (D : ℕ) (l : α → ℕ) (L : ℕ) {j k : ℕ}
    (hjk : j < k) (hk : k ≤ (sortedByLen l).length) :
    slotStart D l L j + D ^ (L - l ((sortedByLen l)[j]'
      (Nat.lt_of_lt_of_le hjk hk))) ≤ slotStart D l L k := by
  have hj : j < (sortedByLen l).length := Nat.lt_of_lt_of_le hjk hk
  -- slotStart (j+1) ≤ slotStart k by monotone
  have h1 : slotStart D l L (j + 1) ≤ slotStart D l L k := slotStart_mono D l L hjk
  rw [← slotStart_succ D l L hj]
  exact h1

omit [DecidableEq α] in
/-- 補助: `slotStart j` の strict 上界. -/
lemma slotStart_lt_pow_of_lt
    {D : ℕ} (hD : 2 ≤ D) (l : α → ℕ)
    (L : ℕ) (hL : ∀ a, l a ≤ L)
    (hk_real : ∑ a : α, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1)
    {j : ℕ} (hj : j < (sortedByLen l).length) :
    slotStart D l L j < D ^ L := by
  have h_succ_le : slotStart D l L (j + 1) ≤ D ^ L :=
    slotStart_le_pow hD l L hL hk_real _
  rw [slotStart_succ D l L hj] at h_succ_le
  have h_pow_pos : 0 < D ^ (L - l ((sortedByLen l)[j]'hj)) :=
    Nat.pow_pos (Nat.lt_of_lt_of_le (by norm_num) hD)
  omega

/-- 補助: index 小 → index 大 で `c (small) <+: c (big)` を不可能と示す.
ここで `small`, `big` の sortedIndex は `j < k` で固定する. -/
lemma not_isPrefix_of_sortedIndex_lt
    {D : ℕ} [NeZero D] (hD : 2 ≤ D)
    (l : α → ℕ)
    (L : ℕ) (hL : ∀ a, l a ≤ L)
    (hk_real : ∑ a : α, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1)
    {x y : α}
    (h_idx_lt : sortedIndex l x < sortedIndex l y)
    (h_len_le : l x ≤ l y) :
    ¬ shannonFanoCode (D := D) l L x <+: shannonFanoCode l L y := by
  intro hpref
  -- slotStart_gap で `slotStart (idx x) + D^(L - l x) ≤ slotStart (idx y)`
  have hk_le : sortedIndex l y ≤ (sortedByLen l).length := Nat.le_of_lt (sortedIndex_lt l y)
  have h_x_at_j : (sortedByLen l)[sortedIndex l x]'(sortedIndex_lt l x) = x :=
    getElem_sortedByLen_sortedIndex l x
  have h_y_at_k : (sortedByLen l)[sortedIndex l y]'(sortedIndex_lt l y) = y :=
    getElem_sortedByLen_sortedIndex l y
  have h_gap : slotStart D l L (sortedIndex l x) + D ^ (L - l x) ≤
      slotStart D l L (sortedIndex l y) := by
    have h := slotStart_gap D l L h_idx_lt hk_le
    rw [h_x_at_j] at h
    exact h
  have hlx_le_L : l x ≤ L := hL x
  have hly_le_L : l y ≤ L := hL y
  have h_pow_pos : 0 < D ^ (L - l x) :=
    Nat.pow_pos (Nat.lt_of_lt_of_le (by norm_num) hD)
  unfold shannonFanoCode at hpref
  have h_eq_take := toBaseDLen_eq_of_isPrefix D h_len_le hpref
  have h_arg2 :
      (slotStart D l L (sortedIndex l y) / D ^ (L - l y)) / D ^ (l y - l x)
        = slotStart D l L (sortedIndex l y) / D ^ (L - l x) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    congr 2
    omega
  rw [h_arg2] at h_eq_take
  have h_lt_x : slotStart D l L (sortedIndex l x) / D ^ (L - l x) < D ^ l x := by
    have h_strict : slotStart D l L (sortedIndex l x) < D ^ L :=
      slotStart_lt_pow_of_lt hD l L hL hk_real (sortedIndex_lt l x)
    rw [Nat.div_lt_iff_lt_mul h_pow_pos]
    calc slotStart D l L (sortedIndex l x)
        < D ^ L := h_strict
      _ = D ^ l x * D ^ (L - l x) := by
          rw [← pow_add]; congr 1; omega
  have h_lt_y : slotStart D l L (sortedIndex l y) / D ^ (L - l x) < D ^ l x := by
    have h_strict : slotStart D l L (sortedIndex l y) < D ^ L :=
      slotStart_lt_pow_of_lt hD l L hL hk_real (sortedIndex_lt l y)
    rw [Nat.div_lt_iff_lt_mul h_pow_pos]
    calc slotStart D l L (sortedIndex l y)
        < D ^ L := h_strict
      _ = D ^ l x * D ^ (L - l x) := by
          rw [← pow_add]; congr 1; omega
  have h_eq_div := toBaseDLen_injOn_lt D (l x) h_lt_x h_lt_y h_eq_take
  -- 矛盾
  have h_step :
      slotStart D l L (sortedIndex l x) / D ^ (L - l x) + 1 ≤
      slotStart D l L (sortedIndex l y) / D ^ (L - l x) := by
    have h_div_mono :
        (slotStart D l L (sortedIndex l x) + D ^ (L - l x)) / D ^ (L - l x) ≤
          slotStart D l L (sortedIndex l y) / D ^ (L - l x) :=
      Nat.div_le_div_right h_gap
    rw [Nat.add_div_right _ h_pow_pos] at h_div_mono
    exact h_div_mono
  omega

/-- prefix-free 性. (`hl : 0 < l a` 仮定は `hk` から redundant だが、API 整合のため受ける.) -/
lemma shannonFanoCode_prefixFree
    {D : ℕ} [NeZero D] (hD : 2 ≤ D)
    (l : α → ℕ) (_hl : ∀ a, 0 < l a)
    (L : ℕ) (hL : ∀ a, l a ≤ L)
    (hk : ∑ a : α, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    IsPrefixFree (shannonFanoCode (D := D) (α := α) l L) := by
  intro a b hab hpref
  have h_len_le : l a ≤ l b := by
    have := hpref.length_le
    rwa [shannonFanoCode_length, shannonFanoCode_length] at this
  have hidx_ne : sortedIndex l a ≠ sortedIndex l b := fun h =>
    hab (sortedIndex_injective l h)
  rcases lt_or_gt_of_ne hidx_ne with h_idx_lt | h_idx_gt
  · -- Case: idx a < idx b, prefix flows correct direction
    exact not_isPrefix_of_sortedIndex_lt hD l L hL hk h_idx_lt h_len_le hpref
  · -- Case: idx a > idx b. Sort order: l b ≤ l a. Combined with l a ≤ l b ⟹ l a = l b.
    have h_pairwise := sortedByLen_pairwise_le l
    have hb_idx : (sortedByLen l)[sortedIndex l b]'(sortedIndex_lt l b) = b :=
      getElem_sortedByLen_sortedIndex l b
    have ha_idx : (sortedByLen l)[sortedIndex l a]'(sortedIndex_lt l a) = a :=
      getElem_sortedByLen_sortedIndex l a
    have h_lb_le_la : l b ≤ l a := by
      have h := (List.pairwise_iff_getElem.mp h_pairwise) _ _
        (sortedIndex_lt l b) (sortedIndex_lt l a) h_idx_gt
      rw [hb_idx, ha_idx] at h
      exact h
    have h_la_eq_lb : l a = l b := le_antisymm h_len_le h_lb_le_la
    -- 同長 prefix ⟹ 等しい code
    have h_eq_codes :
        shannonFanoCode (D := D) l L a = shannonFanoCode (D := D) l L b := by
      apply hpref.eq_of_length_le
      rw [shannonFanoCode_length, shannonFanoCode_length]; omega
    -- 等しい code から `c b <+: c a` (in fact equal both ways)
    have hpref' : shannonFanoCode (D := D) l L b <+: shannonFanoCode l L a := by
      rw [h_eq_codes]
    -- これで forward direction で矛盾 (idx b < idx a, l b ≤ l a)
    exact not_isPrefix_of_sortedIndex_lt hD l L hL hk h_idx_gt h_lb_le_la hpref'

/-- injective. -/
lemma shannonFanoCode_injective
    {D : ℕ} [NeZero D] (hD : 2 ≤ D)
    (l : α → ℕ) (hl : ∀ a, 0 < l a)
    (L : ℕ) (hL : ∀ a, l a ≤ L)
    (hk : ∑ a : α, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    Function.Injective (shannonFanoCode (D := D) (α := α) l L) := by
  intro a b hab
  by_contra h_ne
  -- a ≠ b, but codes equal. prefix-free ⟹ c a not prefix of c b, contradiction since c a = c b is.
  have hpf := shannonFanoCode_prefixFree hD l hl L hL hk a b h_ne
  apply hpf
  rw [hab]

/-- 共通深度 `L`: 全 `l a` の sup. -/
noncomputable def commonDepth (l : α → ℕ) : ℕ := Finset.univ.sup l

omit [DecidableEq α] in
lemma le_commonDepth (l : α → ℕ) (a : α) : l a ≤ commonDepth l :=
  Finset.le_sup (Finset.mem_univ a)

/-- **主定理**: Kraft 充足 ⟹ prefix code 存在. -/
@[entry_point]
theorem exists_prefix_code_of_kraft
    {D : ℕ} (hD : 2 ≤ D)
    (l : α → ℕ) (hl : ∀ a, 0 < l a)
    (hk : ∑ a : α, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    ∃ c : α → List (Fin D),
      Function.Injective c ∧
      (∀ a, (c a).length = l a) ∧
      IsPrefixFree c := by
  haveI : NeZero D := ⟨by omega⟩
  set L := commonDepth l with hL_def
  have hL_bound : ∀ a, l a ≤ L := le_commonDepth l
  refine ⟨shannonFanoCode (D := D) l L, ?_, ?_, ?_⟩
  · exact shannonFanoCode_injective hD l hl L hL_bound hk
  · intro a; exact shannonFanoCode_length _ _ _
  · exact shannonFanoCode_prefixFree hD l hl L hL_bound hk

end InformationTheory.Shannon.ShannonCodeKraftReverse

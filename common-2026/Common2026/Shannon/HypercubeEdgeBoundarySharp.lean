import Common2026.Meta.EntryPoint
import Common2026.Shannon.HypercubeEdgeBoundary
import Common2026.Shannon.HanD
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Hypercube edge-boundary entropy-sharp inequality (B-2'')

Boolean cube `Fin n → Bool` 上の edge-boundary に関する **entropy-sharp** 形
isoperimetric 不等式:

  `|A| · (n - log₂ |A|) ≤ |∂_e A|`

(Harper / Han / Cover-Thomas 流。AM-GM 形 B-2' `edgeBoundary_ge_AMGM` よりも sharp。)

戦略は `condEntropy_coord_eq` (核補題, Phase B) で `μ_A := uniformOn A` 上の
方向 `i` の条件付きエントロピーを fibre size 1/2 の point-wise 計算で
`(2 (|A| - |π_{≠i}(A)|) / |A|) · log 2` と評価し、chain rule (`jointEntropy_chain_rule`) +
conditioning monotonicity (`condEntropy_subset_anti`) で Σ を log|A| で押さえ、
B-2' counting identity (`edgeBoundary_count_eq`) と組み合わせる。

詳細は `docs/shannon/hypercube-edge-boundary-sharp-plan.md` を参照。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

/-! ## Phase A — `μ_A := uniformOn (A : Set (Fin n → Bool))` setup -/

/-- `μ_A := uniformOn (A : Set (Fin n → Bool))` は `A.Nonempty` で確率測度。 -/
private lemma uniformOn_A_isProb
    {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    IsProbabilityMeasure (uniformOn (A : Set (Fin n → Bool))) :=
  isProbabilityMeasure_uniformOn A.finite_toSet hA

/-- 座標射影 `ω ↦ ω i` の可測性。`measurable_pi_apply` の薄いラッパー。 -/
private lemma xsCoord_measurable {n : ℕ} (i : Fin n) :
    Measurable (fun ω : Fin n → Bool => ω i) :=
  measurable_pi_apply i

/-- `{j // j ≠ i}` 上への投影 `ω ↦ fun j => ω j.val` の可測性。 -/
private lemma xExceptCoord_measurable {n : ℕ} (i : Fin n) :
    Measurable (fun ω : Fin n → Bool => fun (j : {j : Fin n // j ≠ i}) => ω j.val) :=
  measurable_pi_iff.mpr (fun j => measurable_pi_apply j.val)

/-- `μ_A` 上の coord-family `Xs i ω := ω i` の joint entropy は `log |A|`。
B-2' AM-GM 形と同じ `h_joint_log` reshape パターン。 -/
private lemma jointEntropy_xs_eq_log_card
    {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    jointEntropy (uniformOn (A : Set (Fin n → Bool)))
        (fun (i : Fin n) (ω : Fin n → Bool) => ω i)
      = Real.log A.card := by
  unfold jointEntropy
  have h_eq : (fun (ω : Fin n → Bool) (i : Fin n) => ω i) = id := by
    funext ω; funext i; rfl
  rw [h_eq]
  exact entropy_uniformOn_eq_log_card hA

/-! ## Phase B — 核補題 `condEntropy_coord_eq`

戦略 (plan の `pointwise_condEntropy_value` / `fibre_size_classification` から差し替え):
`condDistrib` の点別値を計算する代わりに **chain rule**
`H(X_{≠i}, X_i) = H(X_{≠i}) + H(X_i | X_{≠i})` を使う:

* `H(X_{≠i}, X_i) = H(Xs) = log |A|` (reshape).
* `H(X_{≠i})` は `μ_A.map X_{≠i}` の各点質量 `c_i(y)/|A|` から直接計算
  (`negMulLog (1/|A|) = log|A|/|A|`、`negMulLog (2/|A|) = (2/|A|)(log|A| - log 2)`)。
* 差し引いて `H(X_i | X_{≠i}) = 2 (|A| - |π_{≠i}(A)|) log 2 / |A|`。

`condDistrib` の点別 Bern(1/2) 評価 (R1) を完全に回避できる。 -/

/-- `μ_A.map (projMap i)` の各点質量は fibre size / |A|。
`uniformOn_apply_finset` を `t := Finset.univ.filter (projMap i x = y)` で当てる。 -/
private lemma map_projMap_real
    {n : ℕ} (i : Fin n) {A : Finset (Fin n → Bool)} (_hA : A.Nonempty)
    (y : {j : Fin n // j ≠ i} → Bool) :
    ((uniformOn (A : Set (Fin n → Bool))).map
        (fun ω : Fin n → Bool => fun (j : {j : Fin n // j ≠ i}) => ω j.val)).real {y}
      = ((A.filter (fun x => projMap i x = y)).card : ℝ) / A.card := by
  classical
  set f : (Fin n → Bool) → ({j : Fin n // j ≠ i} → Bool) :=
    fun ω j => ω j.val with hf_def
  have hf_meas : Measurable f := xExceptCoord_measurable i
  -- Preimage as a Finset
  set t : Finset (Fin n → Bool) :=
    (Finset.univ : Finset (Fin n → Bool)).filter (fun x => f x = y) with ht_def
  have ht_set : (t : Set (Fin n → Bool)) = f ⁻¹' ({y} : Set _) := by
    ext x
    simp [ht_def]
  -- mass = uniformOn (A) (f ⁻¹' {y}).
  rw [Measure.real, Measure.map_apply hf_meas (measurableSet_singleton y), ← ht_set,
    uniformOn_apply_finset (s := A) (t := t)]
  -- A ∩ t = A.filter (projMap i x = y)
  have h_inter : A ∩ t = A.filter (fun x => projMap i x = y) := by
    ext x
    simp [ht_def, Finset.mem_inter, hf_def]
    tauto
  rw [h_inter, ENNReal.toReal_div]
  rfl

/-- `entropy μ_A X_{≠i}` の閉形:
size-1 fibre (`S_1 = |proj| - D_i`) は `negMulLog (1/|A|)`、
size-2 fibre (`S_2 = D_i = |A| - |proj|`) は `negMulLog (2/|A|)`、それ以外 0。
代数簡約後 `log|A| - 2 D_i log 2 / |A|`。 -/
private lemma entropy_projMap_eq
    {n : ℕ} (i : Fin n) {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    entropy (uniformOn (A : Set (Fin n → Bool)))
        (fun ω : Fin n → Bool => fun (j : {j : Fin n // j ≠ i}) => ω j.val)
      = Real.log A.card
        - 2 * ((A.card : ℝ) - ((projectionExcept i A).card : ℝ))
            * Real.log 2 / A.card := by
  classical
  haveI : IsProbabilityMeasure (uniformOn (A : Set (Fin n → Bool))) :=
    uniformOn_A_isProb hA
  set f : (Fin n → Bool) → ({j : Fin n // j ≠ i} → Bool) :=
    fun ω j => ω j.val
  set proj : Finset ({j : Fin n // j ≠ i} → Bool) := projectionExcept i A
  set fibre : ({j : Fin n // j ≠ i} → Bool) → ℕ :=
    fun y => (A.filter (fun x => projMap i x = y)).card
  -- positivity
  have h_card_pos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have h_card_ne : (A.card : ℝ) ≠ 0 := h_card_pos.ne'
  -- Mass values: per y, mass = fibre y / |A|.
  have h_mass : ∀ y : {j : Fin n // j ≠ i} → Bool,
      ((uniformOn (A : Set (Fin n → Bool))).map f).real {y}
        = ((fibre y : ℕ) : ℝ) / A.card := fun y =>
    map_projMap_real i hA y
  unfold entropy
  -- Rewrite each term of the sum with the mass formula.
  rw [show (∑ y : ({j : Fin n // j ≠ i} → Bool),
        Real.negMulLog (((uniformOn (A : Set (Fin n → Bool))).map f).real {y}))
        = ∑ y : ({j : Fin n // j ≠ i} → Bool),
            Real.negMulLog ((fibre y : ℝ) / A.card) from
        Finset.sum_congr rfl (fun y _ => by rw [h_mass])]
  -- For y ∉ proj, fibre y = 0 so the term is 0; restrict sum to proj.
  have h_fibre_zero : ∀ y : {j : Fin n // j ≠ i} → Bool,
      y ∉ proj → fibre y = 0 := by
    intro y hy
    show (A.filter (fun x => projMap i x = y)).card = 0
    rw [Finset.card_eq_zero]
    rw [Finset.filter_eq_empty_iff]
    intro x hxA hpx
    apply hy
    show y ∈ A.image (projMap i)
    rw [← hpx]
    exact Finset.mem_image_of_mem _ hxA
  have h_outside_zero : ∀ y ∈ (Finset.univ : Finset ({j : Fin n // j ≠ i} → Bool)),
      y ∉ proj → Real.negMulLog ((fibre y : ℝ) / A.card) = 0 := by
    intro y _ hy
    rw [h_fibre_zero y hy]
    push_cast
    simp [Real.negMulLog_zero]
  rw [← Finset.sum_subset (Finset.subset_univ proj) h_outside_zero]
  -- Now sum over proj. Each y ∈ proj has fibre y ∈ {1, 2}.
  -- Split proj by fibre size.
  set S2 : Finset ({j : Fin n // j ≠ i} → Bool) :=
    proj.filter (fun y => fibre y = 2) with hS2_def
  set S1 : Finset ({j : Fin n // j ≠ i} → Bool) :=
    proj.filter (fun y => fibre y = 1) with hS1_def
  -- Each y ∈ proj has fibre size 1 or 2 (B-2' classification).
  have h_fibre_oneortwo : ∀ y ∈ proj, fibre y = 1 ∨ fibre y = 2 := by
    intro y hy
    -- Use the B-2' analysis: A.filter (projMap i x = y) ⊆ {ext0 y, ext1 y}, and at least one in A.
    have hext_ne : extension i false y ≠ extension i true y := by
      intro h
      have := congrFun h i
      simp at this
    -- y ∈ proj = A.image (projMap i), so at least one extension is in A.
    have h_y_in_A : extension i false y ∈ A ∨ extension i true y ∈ A := by
      show extension i false y ∈ A ∨ extension i true y ∈ A
      rw [show proj = A.image (projMap i) from rfl, Finset.mem_image] at hy
      obtain ⟨x, hxA, hxy⟩ := hy
      have hxext : x = extension i (x i) y := (projMap_eq_iff i x y).mp hxy
      cases hb : x i with
      | false => left; rw [hxext, hb] at hxA; exact hxA
      | true => right; rw [hxext, hb] at hxA; exact hxA
    -- fibre y = (A.filter (projMap i x = y)).card; characterize.
    -- A.filter (· = y) = ({ext0 y} ∩ A) ∪ ({ext1 y} ∩ A) (as Finsets).
    have h_filter_eq : A.filter (fun x => projMap i x = y) =
        (({extension i false y} : Finset _).filter (· ∈ A)) ∪
        (({extension i true y} : Finset _).filter (· ∈ A)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨hxA, hpx⟩
        have hxext : x = extension i (x i) y := (projMap_eq_iff i x y).mp hpx
        cases hb : x i with
        | false => left; exact ⟨by rw [hxext, hb], hxA⟩
        | true => right; exact ⟨by rw [hxext, hb], hxA⟩
      · rintro (⟨rfl, hxA⟩ | ⟨rfl, hxA⟩) <;> exact ⟨hxA, by simp⟩
    have h_disjoint :
        Disjoint (({extension i false y} : Finset _).filter (· ∈ A))
          (({extension i true y} : Finset _).filter (· ∈ A)) := by
      apply Finset.disjoint_filter_filter
      rw [Finset.disjoint_singleton]; exact hext_ne
    rcases h_y_in_A with h0 | h1
    · by_cases h1 : extension i true y ∈ A
      · -- both in A: fibre = 2
        right
        show (A.filter (fun x => projMap i x = y)).card = 2
        rw [h_filter_eq, Finset.card_union_of_disjoint h_disjoint]
        rw [show (({extension i false y} : Finset (Fin n → Bool)).filter (· ∈ A))
              = {extension i false y} from by
                apply Finset.filter_eq_self.mpr
                intro x hx; simp [Finset.mem_singleton] at hx; rw [hx]; exact h0,
            show (({extension i true y} : Finset (Fin n → Bool)).filter (· ∈ A))
              = {extension i true y} from by
                apply Finset.filter_eq_self.mpr
                intro x hx; simp [Finset.mem_singleton] at hx; rw [hx]; exact h1]
        simp
      · -- only h0: fibre = 1
        left
        show (A.filter (fun x => projMap i x = y)).card = 1
        rw [h_filter_eq, Finset.card_union_of_disjoint h_disjoint]
        rw [show (({extension i false y} : Finset (Fin n → Bool)).filter (· ∈ A))
              = {extension i false y} from by
                apply Finset.filter_eq_self.mpr
                intro x hx; simp [Finset.mem_singleton] at hx; rw [hx]; exact h0,
            show (({extension i true y} : Finset (Fin n → Bool)).filter (· ∈ A))
              = ∅ from by
                apply Finset.filter_eq_empty_iff.mpr
                intro x hx; simp [Finset.mem_singleton] at hx; rw [hx]; exact h1]
        simp
    · by_cases h0 : extension i false y ∈ A
      · right
        show (A.filter (fun x => projMap i x = y)).card = 2
        rw [h_filter_eq, Finset.card_union_of_disjoint h_disjoint]
        rw [show (({extension i false y} : Finset (Fin n → Bool)).filter (· ∈ A))
              = {extension i false y} from by
                apply Finset.filter_eq_self.mpr
                intro x hx; simp [Finset.mem_singleton] at hx; rw [hx]; exact h0,
            show (({extension i true y} : Finset (Fin n → Bool)).filter (· ∈ A))
              = {extension i true y} from by
                apply Finset.filter_eq_self.mpr
                intro x hx; simp [Finset.mem_singleton] at hx; rw [hx]; exact h1]
        simp
      · left
        show (A.filter (fun x => projMap i x = y)).card = 1
        rw [h_filter_eq, Finset.card_union_of_disjoint h_disjoint]
        rw [show (({extension i false y} : Finset (Fin n → Bool)).filter (· ∈ A))
              = ∅ from by
                apply Finset.filter_eq_empty_iff.mpr
                intro x hx; simp [Finset.mem_singleton] at hx; rw [hx]; exact h0,
            show (({extension i true y} : Finset (Fin n → Bool)).filter (· ∈ A))
              = {extension i true y} from by
                apply Finset.filter_eq_self.mpr
                intro x hx; simp [Finset.mem_singleton] at hx; rw [hx]; exact h1]
        simp
  -- proj = S1 ∪ S2, disjoint
  have hS_disjoint : Disjoint S1 S2 := by
    apply Finset.disjoint_filter.mpr
    intro y _ h1 h2; omega
  have hS_union : S1 ∪ S2 = proj := by
    ext y
    simp [hS1_def, hS2_def, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    · intro hy
      rcases h_fibre_oneortwo y hy with h | h
      · left; exact ⟨hy, h⟩
      · right; exact ⟨hy, h⟩
  -- Sum split
  rw [← hS_union, Finset.sum_union hS_disjoint]
  -- On S1: each term is negMulLog (1/|A|) = log|A|/|A|
  have h_S1_const : ∀ y ∈ S1,
      Real.negMulLog ((fibre y : ℝ) / A.card) = Real.log A.card / A.card := by
    intro y hy
    have hf : fibre y = 1 := (Finset.mem_filter.mp hy).2
    rw [hf]
    push_cast
    rw [Real.negMulLog, Real.log_div one_ne_zero h_card_ne, Real.log_one]
    ring
  -- On S2: each term is negMulLog (2/|A|) = (2/|A|)(log|A| - log 2)
  have h_S2_const : ∀ y ∈ S2,
      Real.negMulLog ((fibre y : ℝ) / A.card)
        = 2 / A.card * (Real.log A.card - Real.log 2) := by
    intro y hy
    have hf : fibre y = 2 := (Finset.mem_filter.mp hy).2
    rw [hf]
    push_cast
    rw [Real.negMulLog, Real.log_div (by norm_num : (2:ℝ) ≠ 0) h_card_ne]
    field_simp
    ring
  rw [Finset.sum_congr rfl h_S1_const, Finset.sum_congr rfl h_S2_const,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  -- Cards: S2.card = |A| - |proj| (= D_i), S1.card = 2|proj| - |A|.
  -- Use 2 * proj.card = |A| + S1.card (a known relation, but we can avoid by using
  -- |A| = S1.card + 2 * S2.card and proj.card = S1.card + S2.card).
  have h_A_card : (A.card : ℕ) = S1.card + 2 * S2.card := by
    have h_A_sum := Finset.card_eq_sum_card_fiberwise
      (f := projMap i) (s := A) (t := proj) (by
        intro x hxA
        show projMap i x ∈ A.image (projMap i)
        exact Finset.mem_image_of_mem _ hxA)
    -- A.card = ∑ y ∈ proj, fibre y = S1.card + 2 * S2.card
    rw [h_A_sum]
    rw [show proj = S1 ∪ S2 from hS_union.symm, Finset.sum_union hS_disjoint]
    have h1 : (∑ y ∈ S1, (A.filter (fun x => projMap i x = y)).card) = S1.card := by
      have h1a : ∀ y ∈ S1, (A.filter (fun x => projMap i x = y)).card = 1 := by
        intro y hy
        exact (Finset.mem_filter.mp hy).2
      rw [Finset.sum_congr rfl h1a, Finset.sum_const, smul_eq_mul, mul_one]
    have h2 : (∑ y ∈ S2, (A.filter (fun x => projMap i x = y)).card) = 2 * S2.card := by
      have h2a : ∀ y ∈ S2, (A.filter (fun x => projMap i x = y)).card = 2 := by
        intro y hy
        exact (Finset.mem_filter.mp hy).2
      rw [Finset.sum_congr rfl h2a, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    rw [h1, h2]
  have h_proj_card : (proj.card : ℕ) = S1.card + S2.card := by
    rw [← hS_union, Finset.card_union_of_disjoint hS_disjoint]
  -- S2.card = A.card - proj.card, cast to ℝ
  have h_S2_card : (S2.card : ℝ) = (A.card : ℝ) - proj.card := by
    have h_A_R : (A.card : ℝ) = (S1.card : ℝ) + 2 * (S2.card : ℝ) := by exact_mod_cast h_A_card
    have h_proj_R : (proj.card : ℝ) = (S1.card : ℝ) + (S2.card : ℝ) := by
      exact_mod_cast h_proj_card
    linarith
  -- A.card = S1.card + 2 * S2.card, cast
  have h_A_card_R : (A.card : ℝ) = (S1.card : ℝ) + 2 * (S2.card : ℝ) := by
    exact_mod_cast h_A_card
  -- Now show the assembled sum equals the target.
  -- LHS of `entropy = ...`: S1.card • (log|A|/|A|) + S2.card • (2/|A|*(log|A| - log 2))
  -- Note that after nsmul_eq_mul we get S1.card * (log|A|/|A|) + S2.card * (2/|A| * (log|A| - log 2)).
  -- Goal: ... = log|A| - 2 * (|A| - proj) * log 2 / |A|
  -- Substitute S1.card = |A| - 2*S2.card and S2.card = |A| - proj.
  rw [show (S1 ∪ S2).card = proj.card from by rw [hS_union]]
  rw [h_S2_card]
  have h_S1_card_R : (S1.card : ℝ) = (A.card : ℝ) - 2 * ((A.card : ℝ) - proj.card) := by
    rw [← h_S2_card]; linarith
  rw [h_S1_card_R]
  field_simp
  ring

/-! ## Phase B (cont'd) -- chain rule で核補題 -/

/-- 主結果向け bridge: pair `(X_{≠i}, X_i)` の joint entropy は `log |A|`。

`(Fin n → Bool) ≃ᵐ ({j // j ≠ i} → Bool) × Bool` を直接構成して reshape。 -/
private lemma entropy_pair_proj_coord_eq_log_card
    {n : ℕ} (i : Fin n) {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    entropy (uniformOn (A : Set (Fin n → Bool)))
        (fun ω : Fin n → Bool =>
          ((fun (j : {j : Fin n // j ≠ i}) => ω j.val), ω i))
      = Real.log A.card := by
  classical
  haveI : IsProbabilityMeasure (uniformOn (A : Set (Fin n → Bool))) :=
    uniformOn_A_isProb hA
  -- Build equiv: (Fin n → Bool) ≃ᵐ ({j // j ≠ i} → Bool) × Bool.
  let e : (Fin n → Bool) ≃ᵐ ({j : Fin n // j ≠ i} → Bool) × Bool :=
    { toFun := fun ω => ((fun j : {j : Fin n // j ≠ i} => ω j.val), ω i)
      invFun := fun p j => if h : j = i then p.2 else p.1 ⟨j, h⟩
      left_inv := by
        intro ω
        funext j
        by_cases h : j = i
        · subst h; simp
        · simp [h]
      right_inv := by
        intro ⟨f, b⟩
        apply Prod.ext
        · funext ⟨j, hj⟩
          show (if h : j = i then b else f ⟨j, h⟩) = f ⟨j, hj⟩
          rw [dif_neg hj]
        · show (if h : i = i then b else f ⟨i, h⟩) = b
          simp
      measurable_toFun :=
        (xExceptCoord_measurable i).prodMk (xsCoord_measurable i)
      measurable_invFun := by
        change Measurable (fun p : ({j : Fin n // j ≠ i} → Bool) × Bool =>
          fun j : Fin n => if h : j = i then p.2 else p.1 ⟨j, h⟩)
        refine measurable_pi_iff.mpr (fun j => ?_)
        by_cases h : j = i
        · have : (fun p : ({j : Fin n // j ≠ i} → Bool) × Bool =>
              (fun j' : Fin n => if h : j' = i then p.2 else p.1 ⟨j', h⟩) j) =
              fun p => p.2 := by
            funext p; show (if hh : j = i then p.2 else p.1 ⟨j, hh⟩) = p.2
            rw [dif_pos h]
          rw [this]
          exact measurable_snd
        · have : (fun p : ({j : Fin n // j ≠ i} → Bool) × Bool =>
              (fun j' : Fin n => if h : j' = i then p.2 else p.1 ⟨j', h⟩) j) =
              fun p => p.1 ⟨j, h⟩ := by
            funext p; show (if hh : j = i then p.2 else p.1 ⟨j, hh⟩) = p.1 ⟨j, h⟩
            rw [dif_neg h]
          rw [this]
          exact (measurable_pi_apply _).comp measurable_fst }
  have h_full := jointEntropy_xs_eq_log_card (A := A) hA
  unfold jointEntropy at h_full
  -- h_full: entropy μ_A (fun ω i => ω i) = log |A|
  -- Note: (fun ω i => ω i) = id, so this is entropy μ_A id = log|A|.
  have h_id : (fun (ω : Fin n → Bool) (i : Fin n) => ω i) = id := by
    funext ω i; rfl
  rw [h_id] at h_full
  -- Apply entropy_measurableEquiv_comp with e: (fun ω => e ω) = our target.
  have h_eq : (fun ω : Fin n → Bool => e ω)
      = fun ω : Fin n → Bool =>
          ((fun (j : {j : Fin n // j ≠ i}) => ω j.val), ω i) := rfl
  have h := entropy_measurableEquiv_comp
    (uniformOn (A : Set (Fin n → Bool))) (id : (Fin n → Bool) → Fin n → Bool)
    measurable_id e
  -- h: entropy μ_A (fun ω => e (id ω)) = entropy μ_A id
  -- LHS pointwise = e ω = ((..), ω i)
  rw [show (fun ω => e (id ω)) = (fun ω : Fin n → Bool =>
      ((fun (j : {j : Fin n // j ≠ i}) => ω j.val), ω i)) from rfl] at h
  rw [h, h_full]

/-- 核補題: 方向 `i` の条件付きエントロピー
`condEntropy μ_A (Xs i) X_{≠i} = (2 (|A| - |π_{≠i}(A)|) / |A|) · log 2`。

戦略: chain rule `H(X_{≠i}, X_i) = H(X_{≠i}) + H(X_i | X_{≠i})` で
`H(X_i | X_{≠i}) = H(joint) - H(X_{≠i})`、各成分を直接計算。 -/
theorem condEntropy_coord_eq
    {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) (i : Fin n) :
    InformationTheory.MeasureFano.condEntropy
        (uniformOn (A : Set (Fin n → Bool)))
        (fun ω : Fin n → Bool => ω i)
        (fun ω (j : {j : Fin n // j ≠ i}) => ω j.val)
      = (2 * ((A.card : ℝ) - ((projectionExcept i A).card : ℝ)) / A.card)
          * Real.log 2 := by
  classical
  haveI : IsProbabilityMeasure (uniformOn (A : Set (Fin n → Bool))) :=
    uniformOn_A_isProb hA
  -- chain rule
  have h_chain := entropy_pair_eq_entropy_add_condEntropy
    (uniformOn (A : Set (Fin n → Bool)))
    (fun ω : Fin n → Bool => fun (j : {j : Fin n // j ≠ i}) => ω j.val)
    (fun ω : Fin n → Bool => ω i)
    (xExceptCoord_measurable i) (xsCoord_measurable i)
  -- pair joint
  have h_pair := entropy_pair_proj_coord_eq_log_card i hA
  -- single proj
  have h_proj := entropy_projMap_eq i hA
  rw [h_pair, h_proj] at h_chain
  -- log|A| = (log|A| - 2 * (|A| - |proj|) * log 2 / |A|) + condEntropy
  -- ⟹ condEntropy = 2 * (|A| - |proj|) * log 2 / |A|
  have h_form : (2 * ((A.card : ℝ) - ((projectionExcept i A).card : ℝ)) / A.card)
        * Real.log 2
      = 2 * ((A.card : ℝ) - ((projectionExcept i A).card : ℝ))
          * Real.log 2 / A.card := by ring
  rw [h_form]
  linarith

/-! ## Phase C — chain rule + conditioning monotonicity -/

/-- chain rule summand `Fin i.val → α` 形 と `↥(univ.filter (· < i)) → α` 形 の reshape。
HanD.lean `condEntropy_chainSummand_bridge` の S = univ 版を局所写経。 -/
private lemma condEntropy_chain_to_subset
    {n : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (i : Fin n) :
    InformationTheory.MeasureFano.condEntropy μ (Xs i)
        (fun ω (j : Fin i.val) =>
          Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
      = InformationTheory.MeasureFano.condEntropy μ (Xs i)
          (fun ω (j : ↥((Finset.univ : Finset (Fin n)).filter (· < i))) =>
            Xs j.val ω) := by
  classical
  -- Index equiv Fin i.val ≃ ↥(univ.filter (· < i))
  let idx : Fin i.val ≃ ↥((Finset.univ : Finset (Fin n)).filter (· < i)) :=
    { toFun := fun j => ⟨⟨j.val, j.isLt.trans i.isLt⟩, by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, j.isLt⟩⟩
      invFun := fun vh => ⟨vh.val.val, (Finset.mem_filter.mp vh.property).2⟩
      left_inv := by rintro ⟨j, hj⟩; rfl
      right_inv := by rintro ⟨⟨v, hv⟩, hv2⟩; rfl }
  let e_cond : (Fin i.val → α)
      ≃ᵐ (↥((Finset.univ : Finset (Fin n)).filter (· < i)) → α) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : ↥((Finset.univ : Finset (Fin n)).filter (· < i)) => α) idx
  have hcond_meas : Measurable
      (fun ω (j : Fin i.val) =>
        Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr (fun _ => hXs _)
  have h_eq :
      (fun ω => e_cond (fun (j : Fin i.val) =>
          Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω))
        = fun ω (j : ↥((Finset.univ : Finset (Fin n)).filter (· < i))) =>
            Xs j.val ω := by
    funext ω jh
    have h_apply :=
      MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ↥((Finset.univ : Finset (Fin n)).filter (· < i)) => α)
        idx
        (fun (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
        (idx.symm jh)
    have h_idx : idx (idx.symm jh) = jh := idx.apply_symm_apply jh
    rw [h_idx] at h_apply
    show e_cond (fun (j : Fin i.val) =>
        Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) jh = Xs jh.val ω
    rw [h_apply]
    -- idx maps j to ⟨⟨j.val, ...⟩, ...⟩; so its .val.val = j.val. After idx.symm idx = id.
    -- Need: Xs ⟨(idx.symm jh).val, _⟩ ω = Xs jh.val ω.
    -- (idx.symm jh).val = jh.val.val (by def of idx)
    rfl
  exact (condEntropy_measurableEquiv_comp μ (Xs i) (hXs _)
    (fun ω (j : Fin i.val) =>
      Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) hcond_meas e_cond).symm.trans
    (by rw [h_eq])

/-- subtype `{j // j ≠ i}` 形 と `↥(univ.erase i)` 形 の reshape。 -/
private lemma condEntropy_subtype_erase_bridge
    {n : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (i : Fin n) :
    InformationTheory.MeasureFano.condEntropy μ (Xs i)
        (fun ω (j : {j : Fin n // j ≠ i}) => Xs j.val ω)
      = InformationTheory.MeasureFano.condEntropy μ (Xs i)
          (fun ω (j : ↥((Finset.univ : Finset (Fin n)).erase i)) =>
            Xs j.val ω) := by
  classical
  let idx : {j : Fin n // j ≠ i}
      ≃ ↥((Finset.univ : Finset (Fin n)).erase i) :=
    { toFun := fun jh => ⟨jh.val, by
        rw [Finset.mem_erase]; exact ⟨jh.property, Finset.mem_univ _⟩⟩
      invFun := fun vh => ⟨vh.val, (Finset.mem_erase.mp vh.property).1⟩
      left_inv := by rintro ⟨j, hj⟩; rfl
      right_inv := by rintro ⟨v, hv⟩; rfl }
  let e_cond : ({j : Fin n // j ≠ i} → α)
      ≃ᵐ (↥((Finset.univ : Finset (Fin n)).erase i) → α) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : ↥((Finset.univ : Finset (Fin n)).erase i) => α) idx
  have hcond_meas : Measurable
      (fun ω (j : {j : Fin n // j ≠ i}) => Xs j.val ω) :=
    measurable_pi_iff.mpr (fun _ => hXs _)
  have h_eq :
      (fun ω => e_cond (fun (j : {j : Fin n // j ≠ i}) => Xs j.val ω))
        = fun ω (j : ↥((Finset.univ : Finset (Fin n)).erase i)) =>
            Xs j.val ω := by
    funext ω jh
    have h_apply :=
      MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ↥((Finset.univ : Finset (Fin n)).erase i) => α)
        idx
        (fun (j : {j : Fin n // j ≠ i}) => Xs j.val ω)
        (idx.symm jh)
    have h_idx : idx (idx.symm jh) = jh := idx.apply_symm_apply jh
    rw [h_idx] at h_apply
    show e_cond (fun (j : {j : Fin n // j ≠ i}) => Xs j.val ω) jh = Xs jh.val ω
    rw [h_apply]
    rfl
  exact (condEntropy_measurableEquiv_comp μ (Xs i) (hXs _)
    (fun ω (j : {j : Fin n // j ≠ i}) => Xs j.val ω) hcond_meas e_cond).symm.trans
    (by rw [h_eq])

/-- Σ_i の条件付きエントロピーを `log|A|` で押さえる。

chain rule (`jointEntropy_chain_rule`) で
`log|A| = Σ_i condEntropy μ_A (Xs i) X_{<i}` を取り、
各 `i` で `condEntropy_subset_anti` を
`T₁ := univ.filter (· < i) ⊆ T₂ := univ.erase i` に適用し、
`Fin i.val ≃ ↥(univ.filter (· < i))` と `{j // j ≠ i} ≃ ↥(univ.erase i)` の reshape で結ぶ。 -/
theorem sum_condEntropy_le_log_card
    {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    ∑ i : Fin n,
        InformationTheory.MeasureFano.condEntropy
          (uniformOn (A : Set (Fin n → Bool)))
          (fun ω : Fin n → Bool => ω i)
          (fun ω (j : {j : Fin n // j ≠ i}) => ω j.val)
      ≤ Real.log A.card := by
  classical
  haveI : IsProbabilityMeasure (uniformOn (A : Set (Fin n → Bool))) :=
    uniformOn_A_isProb hA
  set Xs : Fin n → (Fin n → Bool) → Bool := fun i ω => ω i with hXs_def
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i => xsCoord_measurable i
  -- chain rule
  have h_chain :=
    jointEntropy_chain_rule (uniformOn (A : Set (Fin n → Bool))) Xs hXs_meas
  -- jointEntropy = log |A|
  have h_joint := jointEntropy_xs_eq_log_card (A := A) hA
  rw [h_joint] at h_chain
  -- For each i, prove condEntropy(X_i | X_{≠i}) ≤ chain summand
  have h_per_i : ∀ i : Fin n,
      InformationTheory.MeasureFano.condEntropy
          (uniformOn (A : Set (Fin n → Bool))) (Xs i)
          (fun ω (j : {j : Fin n // j ≠ i}) => Xs j.val ω)
        ≤ InformationTheory.MeasureFano.condEntropy
            (uniformOn (A : Set (Fin n → Bool))) (Xs i)
            (fun ω (j : Fin i.val) =>
              Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) := by
    intro i
    -- Step 1: Convert chain summand to subset form via condEntropy_chain_to_subset.
    rw [condEntropy_chain_to_subset (μ := uniformOn (A : Set (Fin n → Bool)))
        (Xs := Xs) hXs_meas i]
    -- Step 2: Convert subtype form to Finset form.
    rw [condEntropy_subtype_erase_bridge (μ := uniformOn (A : Set (Fin n → Bool)))
        (Xs := Xs) hXs_meas i]
    -- Step 3: Apply condEntropy_subset_anti with T₁ := univ.filter (· < i),
    -- T₂ := univ.erase i. T₁ ⊆ T₂ since j < i ⟹ j ≠ i.
    have hT : (Finset.univ : Finset (Fin n)).filter (· < i)
        ⊆ (Finset.univ : Finset (Fin n)).erase i := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_erase]
      exact ⟨ne_of_lt hj.2, hj.1⟩
    exact condEntropy_subset_anti (uniformOn (A : Set (Fin n → Bool)))
      Xs hXs_meas i hT
  -- Sum the per-i bound and combine with chain rule
  have h_sum_per_i :
      ∑ i : Fin n,
        InformationTheory.MeasureFano.condEntropy
          (uniformOn (A : Set (Fin n → Bool))) (Xs i)
          (fun ω (j : {j : Fin n // j ≠ i}) => Xs j.val ω)
      ≤ ∑ i : Fin n,
          InformationTheory.MeasureFano.condEntropy
            (uniformOn (A : Set (Fin n → Bool))) (Xs i)
            (fun ω (j : Fin i.val) =>
              Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    Finset.sum_le_sum (fun i _ => h_per_i i)
  rw [← h_chain] at h_sum_per_i
  exact h_sum_per_i

/-! ## Phase D — 主定理 -/

/-- B-2'' 主結果 (Harper / Han entropy-sharp edge-isoperimetric):
nonempty `A ⊆ Fin n → Bool` で `|A| · (n - log₂ |A|) ≤ |∂_e A|`。

`condEntropy_coord_eq` (Phase B) と `sum_condEntropy_le_log_card` (Phase C) で
Σ を `log|A|` で押さえ、B-2' の counting identity `edgeBoundary_count_eq`
(`2 Σ_i |π_{≠i}(A)| = n|A| + |∂_e A|`) を ℝ にキャストして代入、
`Real.logb 2 |A| = log |A| / log 2` の bridge で `log₂` 形に整える。 -/
@[entry_point]
theorem edgeBoundary_entropy_sharp {n : ℕ} {A : Finset (Fin n → Bool)}
    (hA : A.Nonempty) :
    (A.card : ℝ) * ((n : ℝ) - Real.logb 2 A.card) ≤ (edgeBoundaryCount A : ℝ) := by
  classical
  -- n = 0 case: Fin 0 → Bool は単一点、A.card = 1、edgeBoundary = 0、両辺 0。
  by_cases hn : n = 0
  · subst hn
    -- A : Finset (Fin 0 → Bool); Subsingleton.
    have hA_card : A.card = 1 := by
      have h1 : A.card ≤ 1 := by
        have h_univ : Fintype.card (Fin 0 → Bool) = 1 := by
          rw [Fintype.card_pi, Fin.prod_univ_zero]
        calc A.card ≤ Fintype.card (Fin 0 → Bool) := Finset.card_le_univ _
          _ = 1 := h_univ
      have h2 : 1 ≤ A.card := hA.card_pos
      omega
    -- edgeBoundaryCount A = 0
    have hEB : edgeBoundaryCount A = 0 := by
      unfold edgeBoundaryCount
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      rintro ⟨x, j⟩ _
      exact Fin.elim0 j
    rw [hA_card]
    simp [hEB, Real.logb_one]
  -- n ≥ 1 case
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_card_pos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have h_card_ne : (A.card : ℝ) ≠ 0 := h_card_pos.ne'
  -- Sum of Phase B over i:
  have h_phaseB_sum :
      ∑ i : Fin n,
        InformationTheory.MeasureFano.condEntropy
          (uniformOn (A : Set (Fin n → Bool)))
          (fun ω : Fin n → Bool => ω i)
          (fun ω (j : {j : Fin n // j ≠ i}) => ω j.val)
        = ∑ i : Fin n,
            (2 * ((A.card : ℝ) - ((projectionExcept i A).card : ℝ)) / A.card)
              * Real.log 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact condEntropy_coord_eq hA i
  -- Pull out constant log 2 and bring sum inside
  have h_pull :
      ∑ i : Fin n,
          (2 * ((A.card : ℝ) - ((projectionExcept i A).card : ℝ)) / A.card)
            * Real.log 2
        = (2 * ((n : ℝ) * A.card - ∑ i : Fin n, ((projectionExcept i A).card : ℝ)) / A.card)
          * Real.log 2 := by
    rw [← Finset.sum_mul]
    congr 1
    rw [show (∑ i : Fin n,
          2 * ((A.card : ℝ) - ((projectionExcept i A).card : ℝ)) / A.card)
          = (2 / A.card) * ∑ i : Fin n,
              ((A.card : ℝ) - ((projectionExcept i A).card : ℝ)) from by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_); ring]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  -- Counting identity: 2 Σ |proj_i| = n |A| + |∂A|
  have h_count := edgeBoundary_count_eq A
  have h_count_R : 2 * ∑ i : Fin n, ((projectionExcept i A).card : ℝ)
      = (n : ℝ) * A.card + (edgeBoundaryCount A : ℝ) := by
    have := congrArg (Nat.cast : ℕ → ℝ) h_count
    push_cast at this
    linarith
  -- So Σ |proj_i| = (n|A| + |∂A|) / 2, hence n|A| - Σ |proj_i| = (n|A| - |∂A|)/2.
  have h_diff :
      (n : ℝ) * A.card - ∑ i : Fin n, ((projectionExcept i A).card : ℝ)
        = ((n : ℝ) * A.card - (edgeBoundaryCount A : ℝ)) / 2 := by
    linarith
  rw [h_diff] at h_pull
  -- So Σ condEntropy_coord = (n|A| - |∂A|) / |A| * log 2 (after simplification)
  -- Now use Phase C: Σ condEntropy ≤ log|A|
  have h_phaseC := sum_condEntropy_le_log_card hA
  rw [h_phaseB_sum, h_pull] at h_phaseC
  -- h_phaseC: (2 * ((n|A| - |∂A|)/2) / |A|) * log 2 ≤ log|A|
  -- Simplify: ((n|A| - |∂A|)/|A|) * log 2 ≤ log|A|
  have h_simplify :
      (2 * (((n : ℝ) * A.card - (edgeBoundaryCount A : ℝ)) / 2) / A.card) * Real.log 2
        = (((n : ℝ) * A.card - (edgeBoundaryCount A : ℝ)) / A.card) * Real.log 2 := by
    ring
  rw [h_simplify] at h_phaseC
  -- Now: ((n|A| - |∂A|)/|A|) * log 2 ≤ log|A|
  -- Multiply by |A| > 0: (n|A| - |∂A|) * log 2 ≤ |A| * log|A|
  have h_mul : ((n : ℝ) * A.card - (edgeBoundaryCount A : ℝ)) * Real.log 2
      ≤ A.card * Real.log A.card := by
    have h := mul_le_mul_of_nonneg_left h_phaseC h_card_pos.le
    have h_eq1 : (A.card : ℝ) *
          ((((n : ℝ) * A.card - (edgeBoundaryCount A : ℝ)) / A.card) * Real.log 2)
        = ((n : ℝ) * A.card - (edgeBoundaryCount A : ℝ)) * Real.log 2 := by
      field_simp
    linarith [h_eq1, h]
  -- Divide by log 2 (positive)
  have h_div : (n : ℝ) * A.card - (edgeBoundaryCount A : ℝ)
      ≤ A.card * Real.log A.card / Real.log 2 := by
    rw [le_div_iff₀ h_log2_pos]
    exact h_mul
  -- A.card * log A.card / log 2 = A.card * logb 2 A.card
  have h_logb_eq : (A.card : ℝ) * Real.logb 2 A.card
      = A.card * Real.log A.card / Real.log 2 := by
    rw [Real.logb, mul_div_assoc]
  rw [← h_logb_eq] at h_div
  linarith

end InformationTheory.Shannon

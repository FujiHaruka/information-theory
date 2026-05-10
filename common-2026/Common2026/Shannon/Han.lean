import Common2026.Shannon.Entropy

/-!
# Joint entropy on `Fin n` and the n-variable chain rule (Phase B skeleton)

Han 不等式ムーンショット ([`docs/han-moonshot-plan.md`](../../../docs/han-moonshot-plan.md))
の Phase B skeleton。Phase A の 2 変数 chain rule
`entropy_pair_eq_entropy_add_condEntropy` を `Fin n` の prefix に対して反復適用して
n 変数 chain rule を得る。Phase C (Han の不等式本体) の入口。

## 主要定義・主定理

* `jointEntropy μ Xs` ─ `Fin n → Ω → α` の joint entropy。`entropy` の薄いラッパー。
* `jointEntropyExcept μ Xs i` ─ index `i` を除いた `{j // j ≠ i}`-値の joint entropy。
* `jointEntropy_chain_rule` ─ `H(X_0, …, X_{n-1}) = ∑ i, H(X_i | X_0, …, X_{i-1})`。

## 戦略

`n` に関する induction:

* base (`n = 0`): joint は単一点 `Fin 0 → α` 上、`entropy = 0`、和も空。
* step (`n + 1`): `Fin (n+1) → α` を「`Fin n` への restriction」と「`Xs ⟨n, _⟩`」の
  pair に分解 → Phase A `entropy_pair_eq_entropy_add_condEntropy` を 1 段適用 →
  IH で n-prefix を展開 → `Fin.sum_univ_castSucc` 系で和に整形。

Pi-値 RV の instance (`Pi.fintype`, `MeasurableSpace.pi`,
`Pi.instMeasurableSingletonClass`) は Phase 0 で `Fin n → α` まで自動発火確認済。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Joint entropy of a finite family of random variables. -/
noncomputable def jointEntropy
    (μ : Measure Ω) (Xs : Fin n → Ω → α) : ℝ :=
  entropy μ (fun ω i => Xs i ω)

/-- Joint entropy with the `i`-th coordinate removed. -/
noncomputable def jointEntropyExcept
    (μ : Measure Ω) (Xs : Fin n → Ω → α) (i : Fin n) : ℝ :=
  entropy μ (fun ω (j : {j // j ≠ i}) => Xs j ω)

/-- entropy is invariant under push-forward by a `MeasurableEquiv`. Helper for the
`Fin (n+1) → α` ↔ `α × (Fin n → α)` reshape used in the chain-rule induction. -/
private lemma entropy_measurableEquiv_comp
    {β γ : Type*}
    [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure Ω) (Xs : Ω → β) (hXs : Measurable Xs) (e : β ≃ᵐ γ) :
    entropy μ (fun ω => e (Xs ω)) = entropy μ Xs := by
  unfold entropy
  refine (Fintype.sum_equiv e.toEquiv
    (fun x => Real.negMulLog ((μ.map Xs).real {x}))
    (fun y => Real.negMulLog ((μ.map (fun ω => e (Xs ω))).real {y}))
    ?_).symm
  intro x
  have hpre : (e : β → γ) ⁻¹' {e x} = {x} := by
    ext y
    simp [Set.mem_preimage, Set.mem_singleton_iff, e.injective.eq_iff, eq_comm]
  show Real.negMulLog ((μ.map Xs).real {x})
      = Real.negMulLog ((μ.map (fun ω => e (Xs ω))).real {(e.toEquiv x : γ)})
  congr 1
  rw [show (e.toEquiv x : γ) = e x from rfl,
      show (fun ω => e (Xs ω)) = (e : β → γ) ∘ Xs from rfl,
      ← Measure.map_map e.measurable hXs,
      measureReal_def, measureReal_def,
      Measure.map_apply e.measurable (measurableSet_singleton _),
      hpre]

/-- n 変数 chain rule for Shannon joint entropy:
`H(X_0, …, X_{n-1}) = ∑ i, H(X_i | X_0, …, X_{i-1})`.

Phase A の `entropy_pair_eq_entropy_add_condEntropy` を `n` についての帰納で
反復適用して証明する。 -/
theorem jointEntropy_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    jointEntropy μ Xs
      = ∑ i : Fin n,
          InformationTheory.MeasureFano.condEntropy μ (Xs i)
            (fun ω (j : Fin i.val) =>
              Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) := by
  induction n with
  | zero =>
    -- RHS: empty sum over Fin 0
    rw [show (∑ i : Fin 0,
        InformationTheory.MeasureFano.condEntropy μ (Xs i)
          (fun ω (j : Fin i.val) =>
            Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)) = 0 from Fin.sum_univ_zero _]
    -- LHS: entropy of a `(Fin 0 → α)`-valued RV. The codomain is a singleton,
    -- so the probability measure puts all mass on `default` and `negMulLog 1 = 0`.
    rw [jointEntropy]
    unfold entropy
    have hmeas : Measurable (fun ω (i : Fin 0) => Xs i ω) :=
      measurable_pi_iff.mpr (fun i => Fin.elim0 i)
    haveI : IsProbabilityMeasure (μ.map (fun ω (i : Fin 0) => Xs i ω)) :=
      Measure.isProbabilityMeasure_map hmeas.aemeasurable
    haveI : Unique (Fin 0 → α) := Pi.uniqueOfIsEmpty _
    rw [Fintype.sum_unique]
    have hsingle : ((μ.map (fun ω (i : Fin 0) => Xs i ω)).real {default} : ℝ) = 1 := by
      have huniv : ({default} : Set (Fin 0 → α)) = Set.univ := by
        ext f; simp [Subsingleton.elim f default]
      rw [huniv, measureReal_def, measure_univ, ENNReal.toReal_one]
    rw [hsingle, Real.negMulLog_one]
  | succ n IH =>
    -- Split `Xs : Fin (n+1) → Ω → α` into prefix `f` and last `g`.
    set f : Ω → (Fin n → α) := fun ω j => Xs j.castSucc ω with hf_def
    set g : Ω → α := Xs (Fin.last n) with hg_def
    have hf : Measurable f := measurable_pi_iff.mpr (fun j => hXs j.castSucc)
    have hg : Measurable g := hXs (Fin.last n)
    -- Pair-form joint = pi-form joint via the measurable equivalence
    -- `MeasurableEquiv.piFinSuccAbove (Fin.last n)`. We use its inverse to land on
    -- `Fin (n+1) → α` from the pair `(α (last n)) × (Fin n → α)`, but it's simpler
    -- to express the equality in the forward direction.
    have h_reshape : jointEntropy μ Xs
        = entropy μ (fun ω => (f ω, g ω)) := by
      -- Apply `entropy_measurableEquiv_comp` with the equiv that turns the pair
      -- `(g ω, f ω)` (note: α first, prefix second matches piFinSuccAbove's image)
      -- into the pi `(fun i => Xs i ω)`.
      let e : (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) (Fin.last n))
      have hjoint_meas : Measurable (fun ω (i : Fin (n + 1)) => Xs i ω) :=
        measurable_pi_iff.mpr (fun i => hXs i)
      -- For each ω, e maps `fun i => Xs i ω` to `(Xs (last n) ω, fun j => Xs (succAbove (last n) j) ω)`.
      -- And `succAbove (last n) j = j.castSucc`.
      have h_e_eq : ∀ ω, e (fun i => Xs i ω) = (Xs (Fin.last n) ω, fun (j : Fin n) => Xs j.castSucc ω) := by
        intro ω
        apply Prod.ext
        · simp [e, MeasurableEquiv.piFinSuccAbove_apply]
        · funext j
          simp [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.init]
      -- entropy μ (e ∘ Xs_pi) = entropy μ Xs_pi
      have h1 := entropy_measurableEquiv_comp μ
        (fun ω (i : Fin (n + 1)) => Xs i ω) hjoint_meas e
      rw [show (fun ω => e (fun i : Fin (n + 1) => Xs i ω))
            = fun ω => (Xs (Fin.last n) ω, fun (j : Fin n) => Xs j.castSucc ω) from
          funext h_e_eq] at h1
      -- entropy μ (g, f) = entropy μ ((Xs (last n)), (fun j => Xs j.castSucc))
      -- We want jointEntropy μ Xs = entropy μ (f, g), but h1 gives entropy of (g, f).
      -- Swap with another MeasurableEquiv.
      let e2 : α × (Fin n → α) ≃ᵐ (Fin n → α) × α := MeasurableEquiv.prodComm
      have h_swap_meas : Measurable
          (fun ω => (Xs (Fin.last n) ω, fun (j : Fin n) => Xs j.castSucc ω)) :=
        hg.prodMk hf
      have h2 := entropy_measurableEquiv_comp μ
        (fun ω => (Xs (Fin.last n) ω, fun (j : Fin n) => Xs j.castSucc ω)) h_swap_meas e2
      simp [e2, MeasurableEquiv.prodComm] at h2
      -- h2: entropy μ (fun ω => (fun (j : Fin n) => Xs j.castSucc ω, Xs (last n) ω))
      --      = entropy μ (fun ω => (Xs (last n) ω, fun (j : Fin n) => Xs j.castSucc ω))
      rw [jointEntropy, ← h1, ← h2, hf_def, hg_def]
    rw [h_reshape]
    rw [entropy_pair_eq_entropy_add_condEntropy μ f g hf hg]
    -- Apply IH to the Fin n prefix.
    have IH' := IH (fun i ω => Xs i.castSucc ω) (fun i => hXs i.castSucc)
    rw [show jointEntropy μ (fun i ω => Xs i.castSucc ω) = entropy μ f from rfl] at IH'
    rw [IH']
    -- Now: (∑ i : Fin n, condEntropy μ (Xs i.castSucc) ...) + condEntropy μ g f
    -- Goal: ∑ i : Fin (n+1), condEntropy μ (Xs i) ...
    rw [Fin.sum_univ_castSucc]
    congr 1

/-! ## Phase C: Han の不等式 -/

section HanInequality

variable [DecidableEq α]

/-- `Fin i.val ⊕ {j : Fin n // i < j}` と `{j : Fin n // j ≠ i}` の自然な同型。
prefix `j < i` と suffix `i < j` を合わせた像が補集合 `j ≠ i` と一致することを使う。 -/
private def exceptIdxEquiv {n : ℕ} (i : Fin n) :
    Fin i.val ⊕ {j : Fin n // i < j} ≃ {j : Fin n // j ≠ i} where
  toFun := Sum.elim
    (fun (k : Fin i.val) =>
      ⟨⟨k.val, k.isLt.trans i.isLt⟩, by
        intro h
        have hval : k.val = i.val := congrArg Fin.val h
        omega⟩)
    (fun (k : {j : Fin n // i < j}) => ⟨k.val, ne_of_gt k.property⟩)
  invFun j :=
    if h : j.val.val < i.val then
      Sum.inl ⟨j.val.val, h⟩
    else
      Sum.inr ⟨j.val, by
        have hne : j.val.val ≠ i.val := fun heq =>
          j.property (Fin.ext heq)
        have : i.val ≤ j.val.val := Nat.le_of_not_lt h
        exact Fin.mk_lt_mk.mpr (lt_of_le_of_ne this (Ne.symm hne))⟩
  left_inv := by
    rintro (k | k)
    · simp only [Sum.elim_inl]
      have h : (⟨k.val, k.isLt.trans i.isLt⟩ : Fin n).val < i.val := k.isLt
      simp [h]
    · simp only [Sum.elim_inr]
      have h : ¬ k.val.val < i.val := not_lt_of_gt k.property
      simp [h]
  right_inv := by
    rintro ⟨j, hj⟩
    by_cases h : j.val < i.val
    · simp only [h, dite_true, Sum.elim_inl]
    · simp only [h, dite_false, Sum.elim_inr]

/-- 補集合 `{j // j ≠ i}` を prefix `Fin i.val` + suffix `{j // i < j}` に分解する
MeasurableEquiv。`exceptIdxEquiv` を index 同型として `piCongrLeft` で逆向きに転送し、
`sumPiEquivProdPi` で sum を product に分解する。 -/
private def exceptSplitMEquiv {n : ℕ} (i : Fin n) :
    ({j : Fin n // j ≠ i} → α) ≃ᵐ
      (Fin i.val → α) × ({j : Fin n // i < j} → α) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : {j : Fin n // j ≠ i} => α)
      (exceptIdxEquiv i)).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin i.val ⊕ {j : Fin n // i < j} => α))

/-- `α ⊕ {j : Fin n // j ≠ i} ≃ Fin n` 相当の index 同型 (`i` を Sum.inl,
補集合を Sum.inr に対応させる)。実装は `Fin.cases` 風の場合分け。
ここでは Pi 値で使うので等価性を直接書き下す。 -/
private def fullIdxEquiv {n : ℕ} (i : Fin n) :
    Unit ⊕ {j : Fin n // j ≠ i} ≃ Fin n where
  toFun := Sum.elim (fun _ => i) (fun j => j.val)
  invFun j := if h : j = i then Sum.inl () else Sum.inr ⟨j, h⟩
  left_inv := by
    rintro (⟨⟩ | ⟨j, hj⟩)
    · simp
    · simp [hj]
  right_inv := by
    intro j
    by_cases h : j = i
    · simp [h]
    · simp [h]

/-- Pi `Fin n → α` を `α × ({j // j ≠ i} → α)` に分解する MeasurableEquiv。 -/
private def piExceptMEquiv {n : ℕ} (i : Fin n) :
    (Fin n → α) ≃ᵐ α × ({j : Fin n // j ≠ i} → α) := by
  -- Step 1: piCongrLeft で `Fin n → α ≃ᵐ (Unit ⊕ {j // j ≠ i}) → α`
  let e1 : (Unit ⊕ {j : Fin n // j ≠ i} → α) ≃ᵐ (Fin n → α) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => α) (fullIdxEquiv i)
  -- Step 2: sumPi → prod
  let e2 : (Unit ⊕ {j : Fin n // j ≠ i} → α) ≃ᵐ (Unit → α) × ({j // j ≠ i} → α) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ {j : Fin n // j ≠ i} => α)
  -- Step 3: Unit → α ≃ᵐ α
  let e3 : (Unit → α) ≃ᵐ α := MeasurableEquiv.funUnique Unit α
  exact e1.symm.trans (e2.trans (MeasurableEquiv.prodCongr e3 (.refl _)))

/-- `(Fin n → α)` を `α × (prefix × suffix)` に分解する MeasurableEquiv。
`piExceptMEquiv` と `exceptSplitMEquiv` の合成。 -/
private def fullSplitMEquiv {n : ℕ} (i : Fin n) :
    (Fin n → α) ≃ᵐ α × ((Fin i.val → α) × ({j : Fin n // i < j} → α)) :=
  (piExceptMEquiv i).trans (MeasurableEquiv.prodCongr (.refl α) (exceptSplitMEquiv i))

set_option linter.unusedSectionVars false in
/-- 個別不等式: 各 `i : Fin n` で `H(Xs) - H(Xs except i) ≤ H(Xs i | prefix)`。
Phase A の chain rule + 「条件付けで減る」を 1 段ずつ組み合わせる。 -/
private lemma han_single_bound
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (i : Fin n) :
    jointEntropy μ Xs - jointEntropyExcept μ Xs i
      ≤ InformationTheory.MeasureFano.condEntropy μ (Xs i)
          (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) := by
  -- Definitions
  set pref : Ω → (Fin i.val → α) :=
      fun ω j => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω with hpref_def
  set suff : Ω → ({j : Fin n // i < j} → α) :=
      fun ω j => Xs j.val ω with hsuff_def
  set prefSuff : Ω → ((Fin i.val → α) × ({j : Fin n // i < j} → α)) :=
      fun ω => (pref ω, suff ω) with hprefSuff_def
  set «except» : Ω → ({j : Fin n // j ≠ i} → α) :=
      fun ω j => Xs j.val ω with hexcept_def
  -- Measurability
  have hpref_meas : Measurable pref :=
    measurable_pi_iff.mpr (fun _ => hXs _)
  have hsuff_meas : Measurable suff :=
    measurable_pi_iff.mpr (fun _ => hXs _)
  have hprefSuff_meas : Measurable prefSuff := hpref_meas.prodMk hsuff_meas
  have hexcept_meas : Measurable «except» :=
    measurable_pi_iff.mpr (fun _ => hXs _)
  have hjoint_meas : Measurable (fun ω (j : Fin n) => Xs j ω) :=
    measurable_pi_iff.mpr (fun j => hXs j)
  -- Phase A chain rule on (prefSuff, Xs i)
  have h_chain :=
    entropy_pair_eq_entropy_add_condEntropy μ prefSuff (Xs i) hprefSuff_meas (hXs i)
  -- Bridge 1: entropy of (prefSuff, Xs i) = jointEntropy μ Xs
  have h_lhs : entropy μ (fun ω => (prefSuff ω, Xs i ω)) = jointEntropy μ Xs := by
    let e_full :
        (Fin n → α) ≃ᵐ ((Fin i.val → α) × ({j : Fin n // i < j} → α)) × α :=
      (fullSplitMEquiv i).trans MeasurableEquiv.prodComm
    have h_e := entropy_measurableEquiv_comp μ (fun ω (j : Fin n) => Xs j ω)
      hjoint_meas e_full
    have h_pointwise : (fun ω => e_full (fun j : Fin n => Xs j ω))
        = (fun ω => (prefSuff ω, Xs i ω)) := by
      funext ω
      apply Prod.ext
      · apply Prod.ext
        · funext k
          simp [e_full, fullSplitMEquiv, piExceptMEquiv, exceptSplitMEquiv,
            fullIdxEquiv, exceptIdxEquiv, MeasurableEquiv.piCongrLeft,
            MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.funUnique,
            MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm,
            prefSuff, pref,
            Equiv.piCongrLeft, Equiv.sumPiEquivProdPi]
        · funext k
          simp [e_full, fullSplitMEquiv, piExceptMEquiv, exceptSplitMEquiv,
            fullIdxEquiv, exceptIdxEquiv, MeasurableEquiv.piCongrLeft,
            MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.funUnique,
            MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm,
            prefSuff, suff,
            Equiv.piCongrLeft, Equiv.sumPiEquivProdPi]
      · simp [e_full, fullSplitMEquiv, piExceptMEquiv, exceptSplitMEquiv,
          fullIdxEquiv, exceptIdxEquiv, MeasurableEquiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.funUnique,
          MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm,
          Equiv.piCongrLeft, Equiv.sumPiEquivProdPi]
    rw [h_pointwise] at h_e
    rw [jointEntropy]
    exact h_e
  -- Bridge 2: entropy of prefSuff = jointEntropyExcept
  have h_first : entropy μ prefSuff = jointEntropyExcept μ Xs i := by
    have h_e := entropy_measurableEquiv_comp μ «except» hexcept_meas
      (exceptSplitMEquiv i)
    have h_pointwise : (fun ω => exceptSplitMEquiv i («except» ω)) = prefSuff := by
      funext ω
      apply Prod.ext
      · funext k
        simp [exceptSplitMEquiv, exceptIdxEquiv, MeasurableEquiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, prefSuff, pref, «except»,
          Equiv.piCongrLeft, Equiv.sumPiEquivProdPi]
      · funext k
        simp [exceptSplitMEquiv, exceptIdxEquiv, MeasurableEquiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, prefSuff, suff, «except»,
          Equiv.piCongrLeft, Equiv.sumPiEquivProdPi]
    rw [h_pointwise] at h_e
    rw [jointEntropyExcept]
    exact h_e
  -- condEntropy_le_condEntropy_of_pair
  have h_drop := condEntropy_le_condEntropy_of_pair μ (Xs i) pref suff
    (hXs i) hpref_meas hsuff_meas
  -- Combine
  rw [h_lhs, h_first] at h_chain
  -- h_chain : jointEntropy μ Xs = jointEntropyExcept μ Xs i + condEntropy μ (Xs i) prefSuff
  -- h_drop : condEntropy μ (Xs i) (fun ω => (pref ω, suff ω)) ≤ condEntropy μ (Xs i) pref
  -- Note: prefSuff = fun ω => (pref ω, suff ω), so they match definitionally.
  linarith

set_option linter.unusedSectionVars false in
/-- Han の不等式: 任意個 `n` の確率変数 `Xs : Fin n → Ω → α` に対し
`(n - 1) · H(Xs) ≤ ∑ i, H(Xs except i)`。

Phase A の `entropy_pair_eq_entropy_add_condEntropy` と
`condEntropy_le_condEntropy_of_pair`、Phase B の `jointEntropy_chain_rule` を
組み合わせて証明する。`n = 0, 1` の退化ケース (両辺 0) も含めて成立する。 -/
theorem han_inequality
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    ((n : ℝ) - 1) * jointEntropy μ Xs
      ≤ ∑ i : Fin n, jointEntropyExcept μ Xs i := by
  -- Sum the per-i bound
  have h_sum_bound : ∑ i : Fin n,
        (jointEntropy μ Xs - jointEntropyExcept μ Xs i)
      ≤ ∑ i : Fin n,
          InformationTheory.MeasureFano.condEntropy μ (Xs i)
            (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    Finset.sum_le_sum (fun i _ => han_single_bound μ Xs hXs i)
  -- Phase B chain rule for the RHS
  have h_chain := jointEntropy_chain_rule μ Xs hXs
  rw [← h_chain] at h_sum_bound
  -- LHS simplification: ∑ (H - H_i) = n·H - ∑ H_i
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h_sum_bound
  -- h_sum_bound: n · H - ∑ H_i ≤ H
  linarith

end HanInequality

end InformationTheory.Shannon

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

end InformationTheory.Shannon

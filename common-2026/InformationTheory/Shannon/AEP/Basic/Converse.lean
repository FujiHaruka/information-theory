import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Bridge
import InformationTheory.Shannon.Han.Basic
import InformationTheory.Shannon.Pi
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.SlepianWolf.Basic
import InformationTheory.Fano.Measure
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecificLimits.Basic
import InformationTheory.Shannon.AEP.Basic.Core

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Source-coding theorem, weak converse

The source-coding converse (Cover-Thomas Theorem 5.4.1) is stated in
`Filter.liminf` form. The block entropy identity `H(X^n) = n · H(X)` is not
available from the `Pairwise IndepFun` hypothesis used elsewhere in this family,
so the converse takes mutual independence (`iIndepFun`) as a hypothesis.
-/

/-! ### I.i.d. block entropy chain rule -/

omit [DecidableEq α] in
lemma condEntropy_eq_entropy_of_indepFun
    {β : Type*} [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y)
    (hindep : IndepFun X Y μ) :
    InformationTheory.MeasureFano.condEntropy μ X Y = entropy μ X := by
  classical
  have h_bridge :
      (mutualInfo μ X Y).toReal
        = entropy μ X - InformationTheory.MeasureFano.condEntropy μ X Y :=
    mutualInfo_eq_entropy_sub_condEntropy μ X Y hX hY
  have h_zero : mutualInfo μ X Y = 0 :=
    (mutualInfo_eq_zero_iff_indep μ X Y hX hY).mpr hindep
  rw [h_zero, ENNReal.toReal_zero] at h_bridge
  linarith

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma entropy_eq_of_identDistrib
    {Ω' : Type*} [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → α) (Y : Ω' → α)
    (h : IdentDistrib X Y μ ν) :
    entropy μ X = entropy ν Y := by
  unfold entropy
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [show (μ.map X).real {x} = (ν.map Y).real {x} from by rw [h.map_eq]]

/-- The block `jointRV` as a `Fin n`-indexed family. -/
private noncomputable def jointFamily (Xs : ℕ → Ω → α) (n : ℕ) : Fin n → Ω → α :=
  fun i ω ↦ Xs i.val ω

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
private lemma measurable_jointFamily (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (n : ℕ) (i : Fin n) : Measurable (jointFamily Xs n i) := hXs i.val

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
private lemma indepFun_Xs_prefix_of_iIndepFun
    (μ : Measure Ω)
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ) (i : ℕ) :
    IndepFun (Xs i) (fun ω (j : Fin i) ↦ Xs j.val ω) μ := by
  -- Apply `iIndepFun.indepFun_finset` with `S = {i}`, `T = Finset.range i`.
  set S : Finset ℕ := {i} with hS_def
  set T : Finset ℕ := Finset.range i with hT_def
  have hST_disj : Disjoint S T := by
    rw [Finset.disjoint_singleton_left, Finset.mem_range]
    exact lt_irrefl i
  have h_pair_indep := hindep_full.indepFun_finset S T hST_disj hXs
  -- h_pair_indep : IndepFun (fun a (k : S) => Xs k.val a) (fun a (k : T) => Xs k.val a) μ.
  -- Project: S → Unit → α, T → Fin i → α via measurable functions.
  -- LHS projection: (S → α) → α, "evaluate at i".
  let projS : (S → α) → α := fun f ↦ f ⟨i, Finset.mem_singleton.mpr rfl⟩
  have hprojS_meas : Measurable projS := by
    show Measurable (fun (f : S → α) ↦ f ⟨i, _⟩)
    exact measurable_pi_apply _
  -- RHS projection: (T → α) → (Fin i → α) by reindexing.
  let projT : (T → α) → (Fin i → α) :=
    fun f j ↦ f ⟨j.val, Finset.mem_range.mpr j.isLt⟩
  have hprojT_meas : Measurable projT := by
    refine measurable_pi_iff.mpr ?_
    intro j
    show Measurable (fun (f : T → α) ↦ f ⟨j.val, _⟩)
    exact measurable_pi_apply _
  have h_lifted := h_pair_indep.comp hprojS_meas hprojT_meas
  -- h_lifted : IndepFun (projS ∘ ...) (projT ∘ ...) = IndepFun (Xs i) (fun ω j => Xs j.val ω).
  exact h_lifted

omit [DecidableEq α] in
/-- **Entropy chain rule for i.i.d. blocks**: `H(X^n) = n · H(X_0)`. -/
@[entry_point]
theorem entropy_jointRV_eq_n_smul
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (n : ℕ) :
    entropy μ (jointRV Xs n) = (n : ℝ) * entropy μ (Xs 0) := by
  classical
  -- `jointRV` is defeq to the joint of `jointFamily`.
  set F : Fin n → Ω → α := jointFamily Xs n with hF_def
  have hF_meas : ∀ i, Measurable (F i) := measurable_jointFamily Xs hXs n
  -- jointEntropy μ F = entropy μ (jointRV Xs n) by defeq.
  have h_je_eq : jointEntropy μ F = entropy μ (jointRV Xs n) := rfl
  -- Apply `jointEntropy_chain_rule`.
  have h_chain := jointEntropy_chain_rule μ F hF_meas
  -- Each summand: condEntropy μ (F i) prefix_i = entropy μ (F i) (independence).
  have h_each : ∀ i : Fin n,
      InformationTheory.MeasureFano.condEntropy μ (F i)
          (fun ω (j : Fin i.val) ↦ F ⟨j.val, j.isLt.trans i.isLt⟩ ω)
        = entropy μ (Xs 0) := by
    intro i
    -- prefix is the tuple of `F j` for `j : Fin i.val` (which is `Xs j.val`).
    set prefix_i : Ω → (Fin i.val → α) :=
      fun ω j ↦ F ⟨j.val, j.isLt.trans i.isLt⟩ ω with hprefix_def
    have hprefix_meas : Measurable prefix_i :=
      measurable_pi_iff.mpr fun j ↦ hF_meas _
    -- prefix_i = fun ω j => Xs j.val ω (defeq via F = jointFamily).
    have hprefix_eq : prefix_i = fun ω (j : Fin i.val) ↦ Xs j.val ω := rfl
    -- F i = Xs i.val (defeq).
    have hFi_eq : F i = Xs i.val := rfl
    -- Independence of F i and prefix_i.
    have h_FI_prefix : IndepFun (F i) prefix_i μ := by
      rw [hFi_eq, hprefix_eq]
      exact indepFun_Xs_prefix_of_iIndepFun μ Xs hXs hindep_full i.val
    -- Now condEntropy μ (F i) prefix_i = entropy μ (F i).
    have h_cond_eq :=
      condEntropy_eq_entropy_of_indepFun μ (F i) prefix_i (hF_meas i) hprefix_meas h_FI_prefix
    rw [h_cond_eq]
    -- entropy μ (F i) = entropy μ (Xs 0) via IdentDistrib.
    rw [hFi_eq]
    exact entropy_eq_of_identDistrib μ μ (Xs i.val) (Xs 0) (hident i.val)
  -- Combine: jointEntropy = ∑ i, H(Xs 0) = n · H(Xs 0).
  rw [← h_je_eq, h_chain]
  rw [Finset.sum_congr rfl (fun i _ ↦ h_each i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Per-block converse bound -/

omit [DecidableEq α] in
/-- Per-block source-coding converse bound:
`(n : ℝ) · H(Xs 0) ≤ log M + h(Pe_n) + Pe_n · n · log |α|`. -/
@[entry_point]
theorem source_coding_per_n_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α)
    (n : ℕ) (hn : 1 ≤ n)
    {M : ℕ} [NeZero M]
    (c : (Fin n → α) → Fin M)
    (d : Fin M → (Fin n → α)) :
    (n : ℝ) * entropy μ (Xs 0)
      ≤ Real.log (M : ℝ)
        + Real.binEntropy
            (InformationTheory.MeasureFano.errorProb μ
              (jointRV Xs n) (fun ω ↦ c (jointRV Xs n ω)) d)
        + InformationTheory.MeasureFano.errorProb μ
            (jointRV Xs n) (fun ω ↦ c (jointRV Xs n ω)) d
          * (n : ℝ) * Real.log (Fintype.card α) := by
  classical
  -- ## B.0 Setup
  set Xn : Ω → (Fin n → α) := jointRV Xs n with hXn_def
  set Yn : Ω → Fin M := fun ω ↦ c (Xn ω) with hYn_def
  set Pe : ℝ := InformationTheory.MeasureFano.errorProb μ Xn Yn d with hPe_def
  have hXn_meas : Measurable Xn := measurable_jointRV Xs hXs n
  have hc_meas : Measurable c := measurable_of_countable _
  have hd_meas : Measurable d := measurable_of_countable _
  have hYn_meas : Measurable Yn := hc_meas.comp hXn_meas
  -- Product Fintype card: Fintype.card (Fin n → α) = (Fintype.card α)^n.
  have hcard_Pi : (Fintype.card (Fin n → α) : ℝ) = (Fintype.card α : ℝ)^n := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rfl
  -- Fano applies on the product alphabet: 2 ≤ Fintype.card (Fin n → α).
  have hcard_Pi_ge_2 : 2 ≤ Fintype.card (Fin n → α) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    have h2n : 2 ≤ 2^n := by
      have : (2 : ℕ)^1 ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
      simpa using this
    exact h2n.trans (Nat.pow_le_pow_left hcard n)
  -- ## B.1 Step A: entropy μ Yn ≤ log M.
  have hcard_Fin : (Fintype.card (Fin M) : ℝ) = (M : ℝ) := by rw [Fintype.card_fin]
  have h_step_A : entropy μ Yn ≤ Real.log (M : ℝ) := by
    have := entropy_le_log_card μ Yn hYn_meas
    rwa [hcard_Fin] at this
  -- ## B.2 Step B: I(Xn; Yn) ≤ entropy μ Yn  (= H(Yn) - H(Yn|Xn) ≤ H(Yn))
  have h_bridge_B :
      (mutualInfo μ Yn Xn).toReal
        = entropy μ Yn - InformationTheory.MeasureFano.condEntropy μ Yn Xn :=
    mutualInfo_eq_entropy_sub_condEntropy μ Yn Xn hYn_meas hXn_meas
  have h_comm_B : mutualInfo μ Xn Yn = mutualInfo μ Yn Xn :=
    mutualInfo_comm μ Xn Yn hXn_meas hYn_meas
  have h_step_B : (mutualInfo μ Xn Yn).toReal ≤ entropy μ Yn := by
    rw [h_comm_B, h_bridge_B]
    have h_nn := condEntropy_nonneg μ Yn Xn
    linarith
  -- ## B.3 Step C (skip): not needed in this assembly path; Fano applies directly to
  -- `condEntropy μ Xn Yn` with decoder `d`, no DPI postprocess needed.
  -- ## B.4 Step D: Fano on (Xn, d∘Yn) — `condEntropy μ Xn (d∘Yn)` bounded.
  -- Note: condEntropy is over the conditioner; we want a bound on `H(Xn | Yn)` via Fano.
  have h_step_D :
      InformationTheory.MeasureFano.condEntropy μ Xn Yn ≤
        Real.binEntropy Pe + Pe * Real.log ((Fintype.card (Fin n → α) : ℝ) - 1) := by
    have := InformationTheory.MeasureFano.fano_inequality_measure_theoretic
      μ Xn Yn d hXn_meas hYn_meas hd_meas hcard_Pi_ge_2
    exact this
  -- ## B.5 Step E: log ((|α|^n) - 1) ≤ n · log |α|.
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by
    have : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast this
  have hcard_ge_one : 1 ≤ (Fintype.card α : ℝ) := by
    have : 1 ≤ Fintype.card α := Fintype.card_pos
    exact_mod_cast this
  have hcardPi_ge_one : 1 ≤ (Fintype.card α : ℝ)^n :=
    one_le_pow₀ hcard_ge_one
  have h_log_pow : Real.log ((Fintype.card (Fin n → α) : ℝ) - 1)
        ≤ (n : ℝ) * Real.log (Fintype.card α) := by
    rw [hcard_Pi]
    have h_le : (Fintype.card α : ℝ)^n - 1 ≤ (Fintype.card α : ℝ)^n := by linarith
    have h_nonneg_sub : 0 ≤ (Fintype.card α : ℝ)^n - 1 :=
      sub_nonneg.mpr hcardPi_ge_one
    rcases lt_or_eq_of_le h_nonneg_sub with hpos | hzero
    · calc Real.log ((Fintype.card α : ℝ)^n - 1)
          ≤ Real.log ((Fintype.card α : ℝ)^n) :=
            Real.log_le_log hpos h_le
        _ = (n : ℝ) * Real.log (Fintype.card α) := by
            rw [Real.log_pow]
    · rw [← hzero, Real.log_zero]
      have : 0 ≤ (n : ℝ) * Real.log (Fintype.card α) := by
        apply mul_nonneg (Nat.cast_nonneg n)
        exact Real.log_nonneg hcard_ge_one
      linarith
  -- ## B.6 Combine: H(X^n) = I(Xn; Yn) + H(Xn | Yn) ≤ log M + h(Pe) + Pe · n log |α|.
  have h_HXn_decomp :
      entropy μ Xn = (mutualInfo μ Xn Yn).toReal
        + InformationTheory.MeasureFano.condEntropy μ Xn Yn := by
    have h := mutualInfo_eq_entropy_sub_condEntropy μ Xn Yn hXn_meas hYn_meas
    linarith
  -- LHS = n · H(Xs 0) via the i.i.d. block entropy chain rule.
  have h_LHS : (n : ℝ) * entropy μ (Xs 0) = entropy μ Xn := by
    rw [hXn_def]
    exact (entropy_jointRV_eq_n_smul μ Xs hXs hindep_full hident n).symm
  -- Pe ≥ 0 to push the Fano bound through monotonicity of `* log |α|`.
  have h_Pe_nn : 0 ≤ Pe := by
    rw [hPe_def, InformationTheory.MeasureFano.errorProb]
    exact measureReal_nonneg
  -- Pe * log(|α|^n - 1) ≤ Pe * n * log |α|.
  have h_Pe_mul : Pe * Real.log ((Fintype.card (Fin n → α) : ℝ) - 1)
      ≤ Pe * (n : ℝ) * Real.log (Fintype.card α) := by
    have := mul_le_mul_of_nonneg_left h_log_pow h_Pe_nn
    linarith [this]
  -- Final assembly: linarith on Steps A-E + decomp.
  rw [h_LHS, h_HXn_decomp]
  linarith [h_step_A, h_step_B, h_step_D, h_Pe_mul]

/-! ### Converse theorem in `Filter.liminf` form -/

omit [DecidableEq α] in
/-- **Source coding theorem, weak converse**:
For any block code `(c_n, d_n)` with `M_n` codewords and i.i.d. discrete source,
if the error probability vanishes then the rate is at least the entropy.

The boundedness assumption `hM_bdd` (rate bounded above) captures the practical
setting: it rules out the pathological case `M n` growing super-exponentially in
`n` (where `liminf log M_n / n` would collapse to junk in the conditionally
complete real lattice). For rate-bounded codes `M n = 2^⌈n R⌉` this is automatic
with `R'` any constant `> R`. -/
@[entry_point]
theorem source_coding_converse
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α)
    (M : ℕ → ℕ) [hM_pos : ∀ n, NeZero (M n)]
    (c : ∀ n, (Fin n → α) → Fin (M n))
    (d : ∀ n, Fin (M n) → (Fin n → α))
    (hPe_to_zero :
      Tendsto (fun n ↦ InformationTheory.MeasureFano.errorProb μ
                          (jointRV Xs n) (fun ω ↦ c n (jointRV Xs n ω)) (d n))
              atTop (𝓝 0))
    (hM_bdd : ∃ R, ∀ n, Real.log (M n : ℝ) / n ≤ R) :
    entropy μ (Xs 0)
      ≤ Filter.liminf (fun n : ℕ ↦ Real.log (M n : ℝ) / n) atTop := by
  classical
  set H : ℝ := entropy μ (Xs 0) with hH_def
  set Pe : ℕ → ℝ := fun n ↦ InformationTheory.MeasureFano.errorProb μ
    (jointRV Xs n) (fun ω ↦ c n (jointRV Xs n ω)) (d n) with hPe_def
  -- δ_n := h(Pe_n) / n + Pe_n · log |α|.
  set δ : ℕ → ℝ := fun n ↦ Real.binEntropy (Pe n) / n + Pe n * Real.log (Fintype.card α)
    with hδ_def
  -- (C.1) Tendsto δ atTop (𝓝 0).
  have h_binEntropy_tendsto : Tendsto (fun n ↦ Real.binEntropy (Pe n)) atTop (𝓝 0) := by
    have := Real.binEntropy_continuous.tendsto 0
    rw [Real.binEntropy_zero] at this
    exact this.comp hPe_to_zero
  have h_one_div_n : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h_binEntropy_div : Tendsto (fun n ↦ Real.binEntropy (Pe n) / n) atTop (𝓝 0) := by
    have hprod := h_binEntropy_tendsto.mul h_one_div_n
    simp only [mul_zero] at hprod
    have h_eq : ∀ n : ℕ, Real.binEntropy (Pe n) * (1 / (n : ℝ))
        = Real.binEntropy (Pe n) / n := fun n ↦ by ring
    exact (Tendsto.congr h_eq hprod)
  have h_Pe_log : Tendsto (fun n ↦ Pe n * Real.log (Fintype.card α)) atTop (𝓝 0) := by
    have h_const : Tendsto (fun _ : ℕ ↦ Real.log (Fintype.card α)) atTop
        (𝓝 (Real.log (Fintype.card α))) := tendsto_const_nhds
    have hprod := hPe_to_zero.mul h_const
    simpa using hprod
  have h_δ : Tendsto δ atTop (𝓝 0) := by
    have h_add := h_binEntropy_div.add h_Pe_log
    simpa [δ] using h_add
  -- (C.2) per-n bound /n: H ≤ log M_n / n + δ_n eventually.
  have h_per_n : ∀ᶠ n in atTop, H ≤ Real.log (M n : ℝ) / n + δ n := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn ↦ ?_⟩
    have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
    have h_bound := source_coding_per_n_bound μ Xs hXs hindep_full hident hcard n hn (c n) (d n)
    -- h_bound : n · H ≤ log M + h(Pe) + Pe · n · log |α|.
    -- divide by n.
    have hn_ne : (n : ℝ) ≠ 0 := hn_pos_R.ne'
    -- Divide h_bound by n.
    have h_div : H ≤
        (Real.log (M n : ℝ) + Real.binEntropy (Pe n)
          + Pe n * (n : ℝ) * Real.log (Fintype.card α)) / (n : ℝ) := by
      have := (div_le_div_iff_of_pos_right hn_pos_R).mpr h_bound
      have h_lhs : (n : ℝ) * H / (n : ℝ) = H := by field_simp
      rw [h_lhs] at this
      exact this
    -- Now expand the RHS.
    have h_target : (Real.log (M n : ℝ) + Real.binEntropy (Pe n)
        + Pe n * (n : ℝ) * Real.log (Fintype.card α)) / (n : ℝ)
        = Real.log (M n : ℝ) / n + δ n := by
      simp only [δ]
      field_simp
      ring
    linarith [h_target ▸ h_div]
  -- (C.3) Apply liminf_le_liminf via `H = liminf (H + 0)` + `(log M_n/n + δ_n) → ?`.
  -- Strategy: `H - δ_n ≤ log M_n / n` eventually, take liminf both sides.
  -- `liminf (H - δ_n) = H` since `(H - δ_n) → H`.
  have h_per_n' : ∀ᶠ n in atTop, H - δ n ≤ Real.log (M n : ℝ) / n := by
    filter_upwards [h_per_n] with n hn
    linarith
  have h_LHS_tendsto : Tendsto (fun n ↦ H - δ n) atTop (𝓝 H) := by
    have := (tendsto_const_nhds (x := H) (f := atTop)).sub h_δ
    simpa using this
  have h_LHS_liminf : Filter.liminf (fun n ↦ H - δ n) atTop = H :=
    h_LHS_tendsto.liminf_eq
  -- IsCoboundedUnder for log M_n / n: from `hM_bdd` (eventual upper bound R) we get
  -- frequent (in fact universal) `log M_n / n ≤ R`, hence `IsCoboundedUnder (· ≥ ·)`.
  obtain ⟨R, hR⟩ := hM_bdd
  have h_cobdd : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ ↦ Real.log (M n : ℝ) / n) :=
    Filter.IsCoboundedUnder.of_frequently_le (a := R)
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hR))
  -- liminf monotone via `liminf_le_liminf`.
  have h_LHS_bdd : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n ↦ H - δ n) :=
    h_LHS_tendsto.isBoundedUnder_ge
  have h_liminf_mono :
      Filter.liminf (fun n ↦ H - δ n) atTop ≤
        Filter.liminf (fun n : ℕ ↦ Real.log (M n : ℝ) / n) atTop :=
    Filter.liminf_le_liminf h_per_n' h_LHS_bdd h_cobdd
  rw [h_LHS_liminf] at h_liminf_mono
  exact h_liminf_mono


end InformationTheory.Shannon

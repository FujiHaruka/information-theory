import InformationTheory.Shannon.EntropyPower.Ext
import InformationTheory.Shannon.EPI.Unconditional.CondEntropyExt
import InformationTheory.Shannon.EPI.Unconditional.Monotone
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.InformationTheory.KullbackLeibler.Basic
import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit.Core
import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit.Mono

/-!
# TruncationLimit — Limit part

截断密度 a.e. 収束 / h(W_n)→⊤ / route (d'') ⊤-枝 assembly /
無条件 gateway 単調性 (方針 Y) と entropyPower lift。Core / Mono part に依存。
umbrella: `InformationTheory.Shannon.EPI.Unconditional.TruncationLimit`。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(2a) helper — truncated W-marginal density a.e. 収束**: `((truncW P W n).map W).rnDeriv vol x).toReal`
は n→∞ で `((P.map W).rnDeriv vol x).toReal` に volume-a.e. 収束。`(truncW P W n).map W = cond (P.map W) Sn`
(`Sn n := {r | |r| ≤ n}`) + `rnDeriv_cond_eq` で `fn_n x = c_n⁻¹ · 1_{Sn n}(x) · fW_enn x` (a.e.)、
`c_n = (P.map W) Sn → 1` (`tendsto_measure_iUnion_atTop`、`⋃ Sn = univ`) + 固定 x で十分大 n で `x ∈ Sn n`。
weak-conv 不使用 (各点極限)。`hW_ac` は a.c. (cond 保存)、regularity precondition。

**独立 honesty audit 2026-06-08 (fresh subagent → ok)**: (B) `hW_ac` は body 未参照 (unused
warning line 1463) = over-hypothesized だが honesty-safe (a.c. 無しでも各点 a.e. 密度収束は cond
公式 + 質量収束で閉じる = より弱い前提で済む、退化定義悪用でなく単なる冗長)。除去可能 (非必須)、
caller 一様性のため残置。(E) weak-conv portmanteau (`tendsto_iff_forall_integral_tendsto` 等) 不使用、
`rnDeriv_cond_eq` + `tendsto_measure_iUnion_atTop` + indicator 各点極限で閉じる (L-Uncond-Y-roi 不発動)。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。@audit:ok -/
theorem truncW_map_density_tendsto_ae
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (_hW_ac : (P.map W) ≪ volume) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun n => (((truncW P W n).map W).rnDeriv volume x).toReal) atTop
        (𝓝 (((P.map W).rnDeriv volume x).toReal)) := by
  classical
  haveI hWmap_prob : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  -- truncation set in the W-marginal and its mass.
  set Sn : ℕ → Set ℝ := fun n => {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : ∀ n, MeasurableSet (Sn n) := fun n =>
    measurableSet_le measurable_norm measurable_const
  have hSn_mono : Monotone Sn := by
    intro n m hnm r hr
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    exact le_trans hr this
  have hSn_union : ⋃ n, Sn n = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro r
    obtain ⟨k, hk⟩ := exists_nat_ge |r|
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  set c : ℕ → ℝ≥0∞ := fun n => (P.map W) (Sn n) with hc_def
  -- `c n → 1` (union is everything).
  have hc_lim : Tendsto c atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := P.map W) hSn_mono
    rw [hSn_union, measure_univ] at h
    exact h
  -- `(truncW P W n).map W = cond (P.map W) (Sn n)` for every `n` (direct measure equality).
  have hmap_eq : ∀ n, ((truncW P W n).map W) = ProbabilityTheory.cond (P.map W) (Sn n) := by
    intro n
    set E : Set Ω := {ω : Ω | |W ω| ≤ (n : ℝ)} with hE_def
    have hE_meas : MeasurableSet E := hW.abs measurableSet_Iic
    have hE_eq : E = W ⁻¹' (Sn n) := by ext ω; simp [hE_def, hSn_def]
    refine Measure.ext (fun A hA => ?_)
    have hLHS : ((truncW P W n).map W) A = ((P.map W) (Sn n))⁻¹ * (P.map W) (Sn n ∩ A) := by
      rw [Measure.map_apply hW hA, truncW, ProbabilityTheory.cond_apply hE_meas P, hE_eq,
        Measure.map_apply hW (hSn_meas n), Measure.map_apply hW ((hSn_meas n).inter hA),
        Set.preimage_inter]
    have hRHS : (ProbabilityTheory.cond (P.map W) (Sn n)) A
        = ((P.map W) (Sn n))⁻¹ * (P.map W) (Sn n ∩ A) := by
      rw [ProbabilityTheory.cond_apply (hSn_meas n) (P.map W) A]
    rw [hLHS, hRHS]
  -- real-valued mass and its inverse converge to 1.
  set cr : ℕ → ℝ := fun n => (c n).toReal with hcr_def
  have hcr_lim : Tendsto cr atTop (𝓝 1) := by
    have := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hc_lim
    simpa [hcr_def, Function.comp] using this
  -- eventually `c n ≠ 0`.
  have hc_ne : ∀ᶠ n in atTop, c n ≠ 0 := by
    have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) := isOpen_ne.mem_nhds one_ne_zero
    exact hc_lim.eventually_mem h_nhds
  -- the inverse mass (real) converges to 1.
  have hcbar_lim : Tendsto (fun n => ((c n)⁻¹).toReal) atTop (𝓝 1) := by
    have heq : (fun n => (cr n)⁻¹) =ᶠ[atTop] fun n => ((c n)⁻¹).toReal := by
      filter_upwards [hc_ne] with n hn
      rw [hcr_def]; simp only; rw [ENNReal.toReal_inv]
    refine Tendsto.congr' heq ?_
    have : Tendsto (fun n => (cr n)⁻¹) atTop (𝓝 (1 : ℝ)⁻¹) :=
      (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hcr_lim
    simpa using this
  -- on the tail (`c n ≠ 0`), the cond density formula:
  -- `fn_n =ᵐ (c n)⁻¹ · 1_{Sn n} · μW.rnDeriv vol`.
  have h_rn : ∀ n, c n ≠ 0 → ((truncW P W n).map W).rnDeriv volume
      =ᵐ[volume] fun x => (c n)⁻¹ * (Sn n).indicator ((P.map W).rnDeriv volume) x := by
    intro n hcn
    have hrn := rnDeriv_cond_eq (P.map W) (hSn_meas n) hcn
    rw [hmap_eq n]; exact hrn
  -- assemble: an a.e. set of `x` where (i) all tail density formulas hold and (ii) `μW.rnDeriv x < ⊤`.
  -- Then `fn_n x → fW x`.
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hc_ne
  -- the a.e. set: tail density formulas hold simultaneously (countable conjunction) + finite density.
  have h_all : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n, N₀ ≤ n →
      ((truncW P W n).map W).rnDeriv volume x
        = (c n)⁻¹ * (Sn n).indicator ((P.map W).rnDeriv volume) x := by
    rw [ae_all_iff]; intro n
    by_cases hn : N₀ ≤ n
    · filter_upwards [h_rn n (hN₀ n hn)] with x hx _; exact hx
    · filter_upwards with x h; exact absurd h hn
  filter_upwards [h_all, (P.map W).rnDeriv_lt_top volume] with x hx hx_fin
  -- abbreviations.
  set fWe : ℝ≥0∞ := (P.map W).rnDeriv volume x with hfWe_def
  have hfWe_ne : fWe ≠ ⊤ := hx_fin.ne
  -- `x ∈ Sn n` eventually (when `|x| ≤ n`).
  obtain ⟨Nx, hNx⟩ := exists_nat_ge |x|
  -- the tail formula simplifies (on `n ≥ max N₀ Nx`) to `(c n)⁻¹.toReal * fWe.toReal`.
  have hev : ∀ᶠ n in atTop, (((truncW P W n).map W).rnDeriv volume x).toReal
      = ((c n)⁻¹).toReal * fWe.toReal := by
    filter_upwards [Filter.eventually_ge_atTop N₀, Filter.eventually_ge_atTop Nx] with n hnN₀ hnNx
    have hxSn : x ∈ Sn n := le_trans hNx (by exact_mod_cast hnNx)
    rw [hx n hnN₀, Set.indicator_of_mem hxSn, ENNReal.toReal_mul, ← hfWe_def]
  -- the product `(c n)⁻¹.toReal * fWe.toReal → 1 * fWe.toReal = fWe.toReal`.
  refine Tendsto.congr' (Filter.EventuallyEq.symm hev) ?_
  have hprod : Tendsto (fun n => ((c n)⁻¹).toReal * fWe.toReal) atTop (𝓝 (1 * fWe.toReal)) :=
    hcbar_lim.mul tendsto_const_nhds
  simpa using hprod

/-- **(2b) helper — `h(μ) = ⊤ ⟹ A(μ) = ⊤`** (正部 lintegral 発散の抽出)。
`differentialEntropyExt μ = (A:EReal) − (B:EReal) = ⊤` (a.c. 枝) から、`A ≠ ⊤` だと EReal 引き算が
`⊤` になり得ない (`B = ⊤`: `fin − ⊤ = ⊥`、`B ≠ ⊤`: `fin − fin = fin`) ので `A = ⊤`。`B(μ) < ⊤` 不要
(`h = ⊤` だけで `A = ⊤` が follow、より強い形)。

**独立 honesty audit 2026-06-08 (fresh subagent → ok)**: genuine (新規 helper)。`htop : h(μ)=⊤`
から `A=⊤` を EReal 減算規約 (`sub_top`/`top_sub`) の場合分けで抽出、循環/bundling/退化なし。
本 helper の対称形が #1 の `hW_negPart_fin` redundancy (= `h=⊤ ⟹ B≠⊤`) を裏付ける。`#print axioms`
= `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。@audit:ok -/
theorem posPart_lintegral_eq_top_of_diffEntExt_top {μ : Measure ℝ} (hac : μ ≪ volume)
    (htop : differentialEntropyExt μ = ⊤) :
    (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume) = ⊤ := by
  rw [differentialEntropyExt_of_ac hac] at htop
  set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume
    with hA_def
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB_def
  -- `htop : (A : EReal) - (B : EReal) = ⊤`.  Suppose `A ≠ ⊤`; derive a contradiction.
  by_contra hA
  -- `A` finite ⟹ `(A : EReal) = ((A.toReal : ℝ) : EReal)`, a real coe.
  have hAcoe : (A : EReal) = ((A.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hA).symm
  rcases eq_or_ne B (⊤ : ℝ≥0∞) with hBtop | hBfin
  · -- `B = ⊤`: `(A:EReal) - ⊤ = ⊥ ≠ ⊤`.
    rw [hBtop, EReal.coe_ennreal_top, EReal.sub_top] at htop
    exact absurd htop (by simp)
  · -- `B ≠ ⊤`: difference of two finite reals is finite (`≠ ⊤`).
    have hBcoe : (B : EReal) = ((B.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hBfin).symm
    rw [hAcoe, hBcoe, ← EReal.coe_sub] at htop
    exact (EReal.coe_ne_top _ htop)

/-- **Step 0 helper — `h(μ) = ⊤ ⟹ B(μ) ≠ ⊤`** (負部 lintegral 有限性の抽出、`posPart_…` の対称形)。
`differentialEntropyExt μ = (A:EReal) − (B:EReal) = ⊤` (a.c. 枝) から、`B = ⊤` だと EReal 引き算が
`(A:EReal) − ⊤ = ⊥ ≠ ⊤` (`EReal.sub_top`、`(A:ℝ≥0∞) ≠ ⊥`) ゆえ矛盾、よって `B ≠ ⊤`。これにより
assembly の Step 0 で `hW_top` から `B(P.map W) ≠ ⊤` を導出でき、signature に `hW_negPart_fin` を
足さずに済む (= 無条件性の鍵)。

genuine (新規 helper)。`htop : h(μ)=⊤` から `B ≠ ⊤` を EReal 減算規約の場合分けで抽出、
循環/bundling/退化なし。@residual なし。

**独立 honesty audit 2026-06-08 (fresh subagent, route closure 監査, commit 803e489 → ok)**:
`posPart_…` の genuine 対称形。`hac` は regularity precondition、結論 `B≠⊤` は body の EReal `sub_top`
場合分け (`B=⊤⟹(A:EReal)−⊤=⊥≠⊤=htop` 矛盾) で `htop` から抽出 = 仮説に核を encode せず (非循環・
非バンドル・非退化)。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 独立
機械確認)。@audit:ok -/
theorem negPart_lintegral_ne_top_of_diffEntExt_top {μ : Measure ℝ} (hac : μ ≪ volume)
    (htop : differentialEntropyExt μ = ⊤) :
    (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume) ≠ ⊤ := by
  rw [differentialEntropyExt_of_ac hac] at htop
  set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume
    with hA_def
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB_def
  -- `htop : (A : EReal) - (B : EReal) = ⊤`.  If `B = ⊤`, then `(A:EReal) - ⊤ = ⊥ ≠ ⊤`.
  intro hBtop
  rw [hBtop, EReal.coe_ennreal_top, EReal.sub_top] at htop
  exact absurd htop (by simp)

/-- **(2c) helper — truncated W-marginal の負部 lintegral の明示上界**: `c_n ≠ 0` のとき
`B(W_n) ≤ ofReal|cbar_n · log cbar_n| + ofReal(cbar_n) · B(W)`、`cbar_n := ((P.map W)(Sn n))⁻¹.toReal`、
`Sn n := {r | |r| ≤ n}`。truncated 密度 `fn = cbar_n · 1_{Sn n} · fW` の `negMulLog_mul` 分解 +
`∫⁻ ofReal(fW) = 1` (確率密度正規化) で得る。`cbar_n → 1` ゆえ B(W_n) を最終的に固定有限値で抑えるための
per-n bound。

**独立 honesty audit 2026-06-08 (fresh subagent → ok)**: genuine (新規 helper)。`hcn` (positive
mass) は cond well-defined の scope = regularity、`hW`/`hW_ac` も regularity。結論 = per-n B 上界の
explicit 式で、仮説に核を encode せず (`negMulLog_mul` 分解 + 確率密度正規化が body で担う)。`#print
axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。NB: docstring 旧版が言及
していた `hW_negPart_fin` は本 helper の signature に**無い** (caller #1 / 単調性側の仮説)。@audit:ok -/
theorem truncW_map_negPart_lintegral_le
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hW_ac : (P.map W) ≪ volume) (n : ℕ)
    (hcn : (P.map W) {r : ℝ | |r| ≤ (n : ℝ)} ≠ 0) :
    (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((((truncW P W n).map W).rnDeriv volume x).toReal)))
        ∂volume)
      ≤ ENNReal.ofReal (|(((P.map W) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal
          * Real.log ((((P.map W) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal)|)
        + ENNReal.ofReal ((((P.map W) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal)
          * (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
              ∂volume) := by
  classical
  haveI hWmap_prob : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn := measurableSet_le measurable_norm measurable_const
  set fW : ℝ → ℝ := fun x => ((P.map W).rnDeriv volume x).toReal with hfW_def
  set c : ℝ≥0∞ := (P.map W) Sn with hc_def
  set cbar : ℝ := (c⁻¹).toReal with hcbar_def
  have hcbar_nn : 0 ≤ cbar := ENNReal.toReal_nonneg
  -- `(truncW P W n).map W = cond (P.map W) Sn` and its density.
  have hmap_eq : ((truncW P W n).map W) = ProbabilityTheory.cond (P.map W) Sn := by
    set E : Set Ω := {ω : Ω | |W ω| ≤ (n : ℝ)} with hE_def
    have hE_meas : MeasurableSet E := hW.abs measurableSet_Iic
    have hE_eq : E = W ⁻¹' Sn := by ext ω; simp [hE_def, hSn_def]
    refine Measure.ext (fun A hA => ?_)
    have hLHS : ((truncW P W n).map W) A = ((P.map W) Sn)⁻¹ * (P.map W) (Sn ∩ A) := by
      rw [Measure.map_apply hW hA, truncW, ProbabilityTheory.cond_apply hE_meas P, hE_eq,
        Measure.map_apply hW hSn_meas, Measure.map_apply hW (hSn_meas.inter hA),
        Set.preimage_inter]
    have hRHS : (ProbabilityTheory.cond (P.map W) Sn) A = ((P.map W) Sn)⁻¹ * (P.map W) (Sn ∩ A) := by
      rw [ProbabilityTheory.cond_apply hSn_meas (P.map W) A]
    rw [hLHS, hRHS]
  set fn : ℝ → ℝ := fun x => (((truncW P W n).map W).rnDeriv volume x).toReal with hfn_def
  have h_rn : ((truncW P W n).map W).rnDeriv volume
      =ᵐ[volume] fun x => c⁻¹ * Sn.indicator ((P.map W).rnDeriv volume) x := by
    rw [hmap_eq]; exact rnDeriv_cond_eq (P.map W) hSn_meas hcn
  have hfW_meas : Measurable (fun x => ENNReal.ofReal (fW x)) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal.ennreal_ofReal
  have hfW_lint : (∫⁻ x, ENNReal.ofReal (fW x) ∂volume) = 1 := by
    have hae_eq : (fun x => ENNReal.ofReal (fW x)) =ᵐ[volume] (P.map W).rnDeriv volume := by
      filter_upwards [(P.map W).rnDeriv_ne_top volume] with x hx
      rw [hfW_def]; exact ENNReal.ofReal_toReal hx
    rw [lintegral_congr_ae hae_eq, Measure.lintegral_rnDeriv hW_ac, measure_univ]
  -- pointwise `=ᵐ`: `-(negMulLog fn) = 1_Sn · ((cbar log cbar)·fW + cbar·(-(negMulLog fW)))`.
  have h_int_eq : (fun x => ENNReal.ofReal (-(Real.negMulLog (fn x))))
      =ᵐ[volume] fun x => ENNReal.ofReal (Sn.indicator
        (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x) := by
    filter_upwards [h_rn] with x hx
    rw [hfn_def]; simp only; rw [hx]
    by_cases hxs : x ∈ Sn
    · rw [Set.indicator_of_mem hxs (f := (P.map W).rnDeriv volume),
        Set.indicator_of_mem hxs
          (f := fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))),
        ENNReal.toReal_mul]
      congr 1
      show -(Real.negMulLog (cbar * fW x))
        = cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))
      rw [Real.negMulLog_mul cbar (fW x)]
      ring_nf
      rw [Real.negMulLog]
      ring
    · rw [Set.indicator_of_notMem hxs (f := (P.map W).rnDeriv volume),
        Set.indicator_of_notMem hxs
          (f := fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x))))]
      simp [Real.negMulLog]
  rw [hfn_def] at *
  rw [show (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((((truncW P W n).map W).rnDeriv volume x).toReal)))
      ∂volume)
    = ∫⁻ x, ENNReal.ofReal (Sn.indicator
        (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x) ∂volume from
    lintegral_congr_ae h_int_eq]
  -- Bound the indicator integrand by two finite-integral pieces (`≤`, then evaluate).
  have hbound : ∀ x, ENNReal.ofReal (Sn.indicator
        (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x)
      ≤ ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)
        + ENNReal.ofReal cbar * ENNReal.ofReal (-(Real.negMulLog (fW x))) := by
    intro x
    by_cases hxs : x ∈ Sn
    · rw [Set.indicator_of_mem hxs]
      refine le_trans ENNReal.ofReal_add_le ?_
      refine add_le_add ?_ ?_
      · rw [← ENNReal.ofReal_mul (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) ?_)
        have hfW_nn : (0 : ℝ) ≤ fW x := ENNReal.toReal_nonneg
        rw [abs_mul, abs_of_nonneg hfW_nn]
      · rw [← ENNReal.ofReal_mul hcbar_nn]
    · rw [Set.indicator_of_notMem hxs]; simp
  have hnegm_meas : Measurable (fun x => ENNReal.ofReal (-(Real.negMulLog (fW x)))) :=
    ((Real.continuous_negMulLog.measurable.comp
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal)).neg).ennreal_ofReal
  have hg1_meas : Measurable
      (fun x => ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)) :=
    measurable_const.mul hfW_meas
  calc (∫⁻ x, ENNReal.ofReal (Sn.indicator
          (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x) ∂volume)
      ≤ ∫⁻ x, (ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)
          + ENNReal.ofReal cbar * ENNReal.ofReal (-(Real.negMulLog (fW x)))) ∂volume :=
        lintegral_mono hbound
    _ = ENNReal.ofReal (|cbar * Real.log cbar|) + ENNReal.ofReal cbar
          * (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (fW x))) ∂volume) := by
        rw [lintegral_add_left hg1_meas, lintegral_const_mul _ hfW_meas, hfW_lint, mul_one,
          lintegral_const_mul _ hnegm_meas]

/-- **W-marginal の ⊤-divergence** (route (d'') 専用、⊤ ケースに縮小): `h(W) = ⊤` のとき
`h(W_n) → ⊤`、`W_n := truncW P W n` (= `P` を W-事象 `{|W| ≤ n}` で条件付けた compact-support 近似)。

**スコープ縮小 (判断ログ6)**: 旧版は任意 `h(W)` の full `Tendsto … (𝓝 (h(W)))` だったが、
これは有限ケースで reverse-Fatou (`≥` 方向) を要し over-scoped。route (d'') が実際に必要とするのは
⊤ ケースのみ (gateway ⊤ 枝の closure で per-n 単調性との squeeze に使う発散) なので、結論を
`𝓝 (⊤ : EReal)` に固定し finite ケースを切り落とす。LSC/Fatou は `≤` しか出さないが、⊤ への発散は
`liminf = ⊤` から `Tendsto … ⊤` が一発で出るため (`eventually_lt_of_lt_liminf` + `ENNReal.tendsto_nhds_top`)
極限と相性が良い。

**証明の骨格 (3 段、weak-conv 不使用)**:
1. **density a.e. 収束** `fn_n → fW` a.e.(volume): `(truncW P W n).map W = cond (P.map W) Sn`
   (`Sn n := {r | |r| ≤ n}`、`hQW_eq` 同型) → `rnDeriv_cond_eq` で `fn_n x = c_n⁻¹.toReal · 1_{Sn n}(x) · fW x`、
   `c_n = (P.map W) Sn`。n→∞: `c_n → 1` (`tendsto_measure_iUnion_atTop`、`⋃ Sn = univ`) ゆえ
   `c_n⁻¹.toReal → 1`、各固定 x で十分大 n で `x ∈ Sn n` ゆえ `1_{Sn n}(x) → 1`、積 → `fW x`。各点極限で弱収束でない。
2. **`A(P.map W) = ⊤`**: `h(P.map W) = A − B = ⊤` (EReal) から `A = ⊤` (EReal の `(A:EReal) − (B:EReal) = ⊤`
   は `A ≠ ⊤` だと不可能、場合分けで `A(P.map W) = ⊤`)。`B(P.map W) < ⊤` 不要 (helper はより強い形)。
3. **合成**: Fatou helper `differentialEntropyExt_posPart_le_liminf_of_ae_tendsto` (1 を h_ae に渡す) で
   `A(P.map W) ≤ liminf A(Q_n.map W)` → `A(P.map W)=⊤` ⟹ `liminf A(Q_n.map W) = ⊤` (`top_le_iff`) ⟹
   `A(Q_n.map W) → ⊤` (ℝ≥0∞ liminf=⊤ ⟹ tendsto ⊤)。+ `B(Q_n.map W)` 有界 (`hBn_fin` 分解、`cbar→1`
   ゆえ eventually 一様有界) ⟹ `h(Q_n.map W) = A−B → ⊤` (EReal、A→⊤ かつ B 有界)。

仮説は全て regularity (非 load-bearing): `hW`/`hW_ac` は可測/絶対連続、`hW_negPart_fin` (= `B(W) < ⊤`)
は h(W) 負部有限性 (2 の `⊤−⊤` 不定形回避 + 3 の B 有界化に必要)、`hW_top` は ⊤-divergence の前提
(結論の発散先 ⊤ を grant する precondition であって発散の核を encode しない)。

**proof-done (Phase 3、0 sorry)**: 上記 3 段を helper `truncW_map_density_tendsto_ae` (1) /
`posPart_lintegral_eq_top_of_diffEntExt_top` (2) / `differentialEntropyExt_posPart_le_liminf_of_ae_tendsto`
(Fatou) / `truncW_map_negPart_lintegral_le` (B 有界化) で組立、最終 EReal Tendsto は
`EReal.tendsto_nhds_top_iff_real` で `∀ M, eventually M < A_n − B_n`。weak-convergence portmanteau
(`tendsto_iff_forall_integral_tendsto` 等) は使わず density a.e. 収束 (finitary) のみで閉じる
(L-Uncond-Y-roi 不発動)。

**独立 honesty audit 2026-06-08 (fresh subagent, proof-done 主張検証 → ok)**: A〜E 全 PASS。
(A) **`hW_negPart_fin` = regularity (非 load-bearing) かつ redundant**: B(W)<⊤ を grant しても
結論 `h(W_n)→⊤` は出ない (核は body の Fatou + posPart-⊤ lift、core-reconstruction FAIL) = 非
load-bearing。body では `C:=1+2·Bμ` 有限化 + #5 の per-n B-bound で genuine 消費 = regularity
precondition として生きている。**さらに redundant**: `hW_top : h(P.map W)=⊤` が EReal 減算規約
(`EReal.sub_top : x-⊤=⊥`、`EReal.top_sub : ⊤-x=⊤ (x≠⊤)`、機械確認) 上 B(W)<⊤ を含意する
(`A-B=⊤` ⟹ A=⊤ ∧ B≠⊤、#4 と対称の抽出)。除去可能 (非必須、別タスク)。honesty 上は無害。
(B) line ~1463 unused `hW_ac` は #3 (density helper) のもの、本定理の `hW_ac` は genuine 消費。
(C) rescope (full Tendsto → ⊤ 専用) honesty-safe: 結論を弱める方向、唯一の consumer = Phase 4
⊤ 枝 (`_top_of_indep_add_unconditional`) が `𝓝 ⊤` のみ要求、偽の含意隠蔽なし。(D) `#print axioms`
= `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。(E) weak-conv portmanteau 不使用
(density a.e. 収束 finitary のみ、L-Uncond-Y-roi 不発動)。@audit:ok -/
theorem differentialEntropyExt_truncW_tendsto_top
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hW_ac : (P.map W) ≪ volume)
    (hW_negPart_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    Tendsto (fun n => differentialEntropyExt ((truncW P W n).map W)) atTop
      (𝓝 (⊤ : EReal)) := by
  classical
  haveI hWmap_prob : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  -- Abbreviations for the positive / negative parts of `Q_n.map W := (truncW P W n).map W`.
  set μW : Measure ℝ := P.map W with hμW_def
  set A : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((((truncW P W n).map W).rnDeriv volume x).toReal)) ∂volume
    with hA_def
  set B : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((((truncW P W n).map W).rnDeriv volume x).toReal)))
      ∂volume with hB_def
  -- each truncated W-marginal is a.c. (`cond` preserves a.c.).
  have hQac : ∀ n, ((truncW P W n).map W) ≪ volume := by
    intro n
    refine (Measure.AbsolutelyContinuous.trans ?_ hW_ac)
    rw [truncW]; exact (ProbabilityTheory.cond_absolutelyContinuous).map hW
  -- **Step (2b): `A(μW) = ⊤`** (positive-part divergence from `h(μW) = ⊤`, `B(μW) < ⊤`).
  have hA_top : (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μW.rnDeriv volume x).toReal)) ∂volume) = ⊤ :=
    posPart_lintegral_eq_top_of_diffEntExt_top hW_ac hW_top
  -- **Step (2a)+(2c): Fatou ⟹ `liminf A = ⊤`**.
  have hfatou := differentialEntropyExt_posPart_le_liminf_of_ae_tendsto μW
    (fun n => (truncW P W n).map W)
    (truncW_map_density_tendsto_ae W P hW hW_ac)
  -- `⊤ = A(μW) ≤ liminf A` ⟹ `liminf A = ⊤`.
  have hliminf_top : Filter.liminf A atTop = ⊤ := by
    rw [hA_def]
    rw [hA_top] at hfatou
    exact top_le_iff.mp hfatou
  -- `A n → ⊤` in ℝ≥0∞ (liminf = ⊤ ⟹ tendsto ⊤).
  have hA_tendsto : Tendsto A atTop (𝓝 (⊤ : ℝ≥0∞)) := by
    apply ENNReal.tendsto_nhds_top
    intro k
    have hk_lt : (k : ℝ≥0∞) < Filter.liminf A atTop := by rw [hliminf_top]; exact ENNReal.coe_lt_top
    exact Filter.eventually_lt_of_lt_liminf hk_lt
  -- **`B n` eventually bounded by a fixed finite constant `C`.**
  -- `C := 1 + 2 * B(μW)` (finite since `B(μW) = hW_negPart_fin < ⊤`).
  set Bμ : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μW.rnDeriv volume x).toReal))) ∂volume with hBμ_def
  set C : ℝ≥0∞ := 1 + 2 * Bμ with hC_def
  have hC_fin : C ≠ ⊤ := by
    rw [hC_def]
    refine ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top (by simp) hW_negPart_fin⟩
  have hB_bound : ∀ᶠ n in atTop, B n ≤ C := by
    -- mass of the truncation set and its inverse (real) both → 1.
    set Sn : ℕ → Set ℝ := fun n => {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
    have hSn_mono : Monotone Sn := by
      intro p q hpq r hr
      have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
      exact le_trans hr this
    have hSn_union : ⋃ k, Sn k = Set.univ := by
      rw [Set.eq_univ_iff_forall]; intro r
      obtain ⟨k, hk⟩ := exists_nat_ge |r|
      exact Set.mem_iUnion.2 ⟨k, hk⟩
    set cc : ℕ → ℝ≥0∞ := fun n => μW (Sn n) with hcc_def
    have hcc_lim : Tendsto cc atTop (𝓝 1) := by
      have h := tendsto_measure_iUnion_atTop (μ := μW) hSn_mono
      rw [hSn_union, measure_univ] at h
      exact h
    have hcc_ne : ∀ᶠ n in atTop, cc n ≠ 0 := by
      have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) := isOpen_ne.mem_nhds one_ne_zero
      exact hcc_lim.eventually_mem h_nhds
    -- inverse-mass (real) `cbar n := (cc n)⁻¹.toReal → 1`.
    have hcbar_lim : Tendsto (fun n => ((cc n)⁻¹).toReal) atTop (𝓝 1) := by
      have hcr_lim : Tendsto (fun n => (cc n).toReal) atTop (𝓝 1) := by
        have := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hcc_lim
        simpa [Function.comp] using this
      have heq : (fun n => ((cc n).toReal)⁻¹) =ᶠ[atTop] fun n => ((cc n)⁻¹).toReal := by
        filter_upwards [hcc_ne] with n hn; rw [ENNReal.toReal_inv]
      refine Tendsto.congr' heq ?_
      have : Tendsto (fun n => ((cc n).toReal)⁻¹) atTop (𝓝 (1 : ℝ)⁻¹) :=
        (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hcr_lim
      simpa using this
    -- eventually `cbar n ≤ 2` and `|cbar n · log (cbar n)| ≤ 1`.
    have hcbar_le : ∀ᶠ n in atTop, ((cc n)⁻¹).toReal ≤ 2 :=
      hcbar_lim.eventually_le_const (by norm_num : (1 : ℝ) < 2)
    have hlog_le : ∀ᶠ n in atTop,
        |((cc n)⁻¹).toReal * Real.log (((cc n)⁻¹).toReal)| ≤ 1 := by
      -- `t ↦ |t · log t|` is continuous and `→ 0` at `1` (`log 1 = 0`); so eventually `≤ 1`.
      have hcont : Tendsto (fun n => |((cc n)⁻¹).toReal * Real.log (((cc n)⁻¹).toReal)|)
          atTop (𝓝 |(1 : ℝ) * Real.log 1|) := by
        apply Tendsto.abs
        exact (hcbar_lim.mul ((Real.continuousAt_log (by norm_num)).tendsto.comp hcbar_lim))
      rw [Real.log_one, mul_zero, abs_zero] at hcont
      exact hcont.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hcc_ne, hcbar_le, hlog_le] with n hcn hcbar2 hlog1
    -- combine the per-`n` bound with the two eventual estimates.
    have hbnd := truncW_map_negPart_lintegral_le W P hW hW_ac n hcn
    calc B n
        ≤ ENNReal.ofReal (|((μW (Sn n))⁻¹).toReal * Real.log (((μW (Sn n))⁻¹).toReal)|)
            + ENNReal.ofReal (((μW (Sn n))⁻¹).toReal) * Bμ := hbnd
      _ ≤ 1 + 2 * Bμ := by
          refine add_le_add ?_ ?_
          · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hlog1
          · refine mul_le_mul' ?_ (le_refl Bμ)
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
            exact ENNReal.ofReal_le_ofReal hcbar2
      _ = C := by rw [hC_def]
  -- **Final EReal Tendsto** via `tendsto_nhds_top_iff_real`.
  rw [EReal.tendsto_nhds_top_iff_real]
  intro M
  -- coe `A n → ⊤` to EReal.
  have hAE_tendsto : Tendsto (fun n => ((A n : EReal))) atTop (𝓝 (⊤ : EReal)) := by
    have : Tendsto (fun n => ((A n : ℝ≥0∞) : EReal)) atTop (𝓝 ((⊤ : ℝ≥0∞) : EReal)) :=
      (continuous_coe_ennreal_ereal.tendsto _).comp hA_tendsto
    rwa [EReal.coe_ennreal_top] at this
  -- eventually `(M + C.toReal : EReal) < A n`.
  have hev_A : ∀ᶠ n in atTop, ((M + C.toReal : ℝ) : EReal) < (A n : EReal) := by
    rw [EReal.tendsto_nhds_top_iff_real] at hAE_tendsto
    exact hAE_tendsto (M + C.toReal)
  -- combine with the `B`-bound and a.c. expansion of `differentialEntropyExt`.
  filter_upwards [hev_A, hB_bound] with n hAn hBn
  -- expand `differentialEntropyExt (Q_n.map W) = (A n : EReal) - (B n : EReal)`.
  rw [differentialEntropyExt_of_ac (hQac n)]
  show ((M : ℝ) : EReal) < (A n : EReal) - (B n : EReal)
  -- `(B n : EReal) ≤ (C.toReal : EReal)`.
  have hBn_fin : B n ≠ ⊤ := ne_top_of_le_ne_top hC_fin hBn
  have hBn_le : (B n : EReal) ≤ ((C.toReal : ℝ) : EReal) := by
    rw [← EReal.coe_ennreal_toReal hBn_fin]
    exact_mod_cast (ENNReal.toReal_le_toReal hBn_fin hC_fin).mpr hBn
  -- `M < A n - B n` ⟸ `M + B n < A n` ⟸ `M + C.toReal < A n` and `B n ≤ C.toReal`.
  rw [EReal.lt_sub_iff_add_lt (Or.inl (EReal.coe_ennreal_ne_bot _))
    (Or.inr (EReal.coe_ne_bot _))]
  calc ((M : ℝ) : EReal) + (B n : EReal)
      ≤ ((M : ℝ) : EReal) + ((C.toReal : ℝ) : EReal) := add_le_add (le_refl _) hBn_le
    _ = ((M + C.toReal : ℝ) : EReal) := by rw [← EReal.coe_add]
    _ < (A n : EReal) := hAn

/-- **Step-0 helper for the ⊤-branch assembly — `B(ν_n) ≠ ⊤`** (negative part of the truncated sum
law). `ν_n := (truncW P W n).map (W+V)`. Decomposes `ν_n = (Q_n.map W) ∗ (Q_n.map V)` (independence
preserved under conditioning on the `W`-event `{|W| ≤ n}`), bounds `B(Q_n.map W) ≠ ⊤` via the per-n
explicit bound `truncW_map_negPart_lintegral_le` (finite since `B(W) < ⊤` and `c_n ≠ 0`), then lifts
to the sum law via the single-component finiteness `negPart_negMulLog_conv_single_ne_top`.

genuine (新規 helper)。`hW`/`hV`/`hWV`/`hW_ac`/`hBW`/`hn` は全て regularity precondition
(結論 = 截断和周辺負部の有限性 を encode せず)。@residual なし。

**独立 honesty audit 2026-06-08 (fresh subagent, route closure 監査, commit 803e489 → ok)**:
非循環・非バンドル・非退化 全 PASS。6 仮説は可測/独立/絶対連続/`B(W)<⊤`/positive-mass = 全 regularity
precondition (grant しても結論 `B(ν_n)≠⊤` は出ない、core = body の独立保存 conditioning + per-n explicit
bound `truncW_map_negPart_lintegral_le` + single-component lift `negPart_negMulLog_conv_single_ne_top`)。
sufficiency — `hBW` (=B(W)<⊤) + cond の per-n bound で genuine に follow。`#print axioms` (in-file
transient + `lake env lean`) = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 独立機械確認)。
@audit:ok -/
private theorem negPart_lintegral_map_truncW_add_ne_top
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hBW : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤)
    (n : ℕ) (hn : P {ω | |W ω| ≤ (n : ℝ)} ≠ 0) :
    (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((((truncW P W n).map (fun ω => W ω + V ω)).rnDeriv
        volume x).toReal))) ∂volume) ≠ ⊤ := by
  classical
  set Q : Measure Ω := truncW P W n with hQ_def
  haveI hQ_prob : IsProbabilityMeasure Q := by
    rw [hQ_def, truncW]; exact ProbabilityTheory.cond_isProbabilityMeasure hn
  haveI hQW_prob : IsProbabilityMeasure (Q.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI hQV_prob : IsProbabilityMeasure (Q.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  -- W stays a.c. under conditioning.
  have hW_ac_Q : (Q.map W) ≪ volume := by
    refine (Measure.AbsolutelyContinuous.trans ?_ hW_ac)
    rw [hQ_def, truncW]
    exact (ProbabilityTheory.cond_absolutelyContinuous).map hW
  -- W ⊥ V under `Q` (conditioning on a `W`-event preserves independence).
  have hE_meas : MeasurableSet {ω : Ω | |W ω| ≤ (n : ℝ)} := hW.abs measurableSet_Iic
  set E : Set Ω := {ω : Ω | |W ω| ≤ (n : ℝ)} with hE_def
  have hindep : IndepFun W V Q := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    have hEW : E ∩ W ⁻¹' s = W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) := by
      ext ω; simp [hE_def, Set.mem_inter_iff, and_comm]
    have hIcc_meas : MeasurableSet {r : ℝ | |r| ≤ (n : ℝ)} :=
      (_root_.continuous_abs.measurable measurableSet_Iic)
    have hAW : MeasurableSet ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) := hIcc_meas.inter hs
    rw [hQ_def, truncW, cond_apply hE_meas, cond_apply hE_meas, cond_apply hE_meas]
    have hjoint : E ∩ (W ⁻¹' s ∩ V ⁻¹' t) = W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) ∩ V ⁻¹' t := by
      rw [← Set.inter_assoc, hEW]
    rw [hjoint, hEW]
    have hfac1 : P (W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) ∩ V ⁻¹' t)
        = P (W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s)) * P (V ⁻¹' t) :=
      hWV.measure_inter_preimage_eq_mul _ _ hAW ht
    have hEV : E ∩ V ⁻¹' t = W ⁻¹' {r : ℝ | |r| ≤ (n : ℝ)} ∩ V ⁻¹' t := by
      ext ω; simp [hE_def]
    have hfac2 : P (E ∩ V ⁻¹' t) = P E * P (V ⁻¹' t) := by
      rw [hEV, hWV.measure_inter_preimage_eq_mul _ _ hIcc_meas ht, hE_def]; rfl
    rw [hfac1, hfac2]
    have hPE_ne : P E ≠ 0 := by rw [hE_def]; exact hn
    have hPE_ne_top : P E ≠ ∞ := measure_ne_top P E
    have hcancel : (P E)⁻¹ * (P E * P (V ⁻¹' t)) = P (V ⁻¹' t) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hPE_ne hPE_ne_top, one_mul]
    rw [hcancel]; ring
  -- the sum law equals the convolution of the marginals.
  have hsum_conv : Q.map (fun ω => W ω + V ω) = (Q.map W) ∗ (Q.map V) := by
    have := hindep.map_add_eq_map_conv_map hW hV
    simpa [Pi.add_apply] using this
  -- `B(Q.map W) ≠ ⊤` via the explicit per-n bound (finite under `B(W) < ⊤` and `c_n ≠ 0`).
  have hcn' : (P.map W) {r : ℝ | |r| ≤ (n : ℝ)} ≠ 0 := by
    have hmeas : MeasurableSet {r : ℝ | |r| ≤ (n : ℝ)} :=
      _root_.continuous_abs.measurable measurableSet_Iic
    rw [Measure.map_apply hW hmeas]
    have : W ⁻¹' {r : ℝ | |r| ≤ (n : ℝ)} = {ω | |W ω| ≤ (n : ℝ)} := by ext ω; simp
    rw [this]; exact hn
  have hBQW : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((Q.map W).rnDeriv volume x).toReal)))
      ∂volume) ≠ ⊤ := by
    have hbnd := truncW_map_negPart_lintegral_le W P hW hW_ac n hcn'
    rw [← hQ_def] at hbnd
    refine ne_top_of_le_ne_top ?_ hbnd
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBW⟩
  -- lift to the sum law.
  rw [hsum_conv]
  exact negPart_negMulLog_conv_single_ne_top (Q.map W) (Q.map V) hW_ac_Q hBQW

/-- **gateway ⊤ 枝 (無条件)**: `h(W) = ⊤ ⟹ h(W+V) = ⊤`、無条件版② (i-a) を bypass。
per-n 単調性 `h(W_n) ≤ h(W_n + V)` (`differentialEntropyExt_mono_add_truncW`) と `h(W_n) → ⊤`
(`differentialEntropyExt_truncW_tendsto_top`、⊤ ケース専用に縮小済) を組み、
`h(W_n + V) ≥ h(W_n) → ⊤` で `h(W+V) = ⊤`。
route T capstone Case 2 (`EPIInfiniteVarianceCapstone.lean:343`、`entropyPowerExt = ⊤` を
`le_top`) と同型の「⊤ 枝は EReal ⊤ 表現で trivial に閉じる」を再利用する。

**⊤ 枝のみ無条件、有限枝は別 lemma** (finite ② / coe 枝)。`_unconditional` 命名は本 ⊤ 枝が真に
無条件 (regularity precondition `hW`/`hV`/`hWV`/`hW_ac` のみ、無条件版② sorry を継承しない) なため
honest。`hW_top` (h(W)=⊤) は場合分け precondition で load-bearing でない。

route β' Phase 4 で埋める。
@audit:ok -/
theorem differentialEntropyExt_top_of_indep_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    differentialEntropyExt (P.map (fun ω => W ω + V ω)) = ⊤ := by
  classical
  -- ν := P.map(W+V),  ν_n := (truncW P W n).map(W+V),  c_n := P{|W| ≤ n}.
  set ν : Measure ℝ := P.map (fun ω => W ω + V ω) with hν_def
  haveI hμW_prob : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI hμV_prob : IsProbabilityMeasure (P.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  haveI hν_prob : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (hW.add hV).aemeasurable
  -- **Step 0 — regularity.**
  -- ν = (P.map W) ∗ (P.map V) (independence).
  have hconv : ν = (P.map W) ∗ (P.map V) := by
    rw [hν_def]; exact hWV.map_add_eq_map_conv_map hW hV
  -- B(P.map W) ≠ ⊤ from h(W) = ⊤  (Step-0 helper, avoids adding a hypothesis to the signature).
  have hBW : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
      ∂volume) ≠ ⊤ := negPart_lintegral_ne_top_of_diffEntExt_top hW_ac hW_top
  -- ν ≪ volume (convolution with an a.c. left factor is a.c.).
  have hν_ac : ν ≪ volume := by
    rw [hconv, conv_eq_withDensity_translate_average (P.map W) (P.map V) hW_ac]
    exact withDensity_absolutelyContinuous _ _
  -- B(ν) ≠ ⊤ (single-component negative-part finiteness of the sum law).
  have hBν : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((ν.rnDeriv volume x).toReal))) ∂volume)
      ≠ ⊤ := by
    rw [hconv]
    exact negPart_negMulLog_conv_single_ne_top (P.map W) (P.map V) hW_ac hBW
  -- **Step 1 — `h(ν_n) → ⊤`** (squeeze: per-n monotone below a tendsto-⊤ sequence).
  -- Phase 3: `h(Q_n.map W) → ⊤`.
  have hW_tendsto : Tendsto (fun n => differentialEntropyExt ((truncW P W n).map W)) atTop
      (𝓝 (⊤ : EReal)) :=
    differentialEntropyExt_truncW_tendsto_top W P hW hW_ac hBW hW_top
  -- eventually positive mass `c_n ≠ 0`.
  have hcn_ev : ∀ᶠ n : ℕ in atTop, P {ω | |W ω| ≤ (n : ℝ)} ≠ 0 := by
    set E : ℕ → Set Ω := fun n => {ω | |W ω| ≤ (n : ℝ)} with hE_def
    have hE_mono : Monotone E := by
      intro p q hpq ω hω
      have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
      exact le_trans hω this
    have hE_union : ⋃ k, E k = Set.univ := by
      rw [Set.eq_univ_iff_forall]; intro ω
      obtain ⟨k, hk⟩ := exists_nat_ge |W ω|
      exact Set.mem_iUnion.2 ⟨k, hk⟩
    have hlim : Tendsto (fun n => P (E n)) atTop (𝓝 1) := by
      have h := tendsto_measure_iUnion_atTop (μ := P) hE_mono
      rw [hE_union, measure_univ] at h
      exact h
    have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) := isOpen_ne.mem_nhds one_ne_zero
    exact hlim.eventually_mem h_nhds
  -- per-n monotone (eventually): `h(Q_n.map W) ≤ h(ν_n)`.
  have hmono_ev : ∀ᶠ n in atTop,
      differentialEntropyExt ((truncW P W n).map W)
        ≤ differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω)) := by
    filter_upwards [hcn_ev] with n hn
    exact differentialEntropyExt_mono_add_truncW W V P hW hV hWV hW_ac hBW n hn
  -- squeeze to get `h(ν_n) → ⊤`.
  have hνn_tendsto : Tendsto (fun n => differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω)))
      atTop (𝓝 (⊤ : EReal)) := by
    rw [EReal.tendsto_nhds_top_iff_real]
    intro M
    rw [EReal.tendsto_nhds_top_iff_real] at hW_tendsto
    filter_upwards [hW_tendsto M, hmono_ev] with n hMn hmn
    exact lt_of_lt_of_le hMn hmn
  -- **Steps 2–4 — `A(ν) = ⊤`** (by_contra + per-n Gibbs + measure domination).
  set Aν : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((ν.rnDeriv volume x).toReal)) ∂volume
    with hAν_def
  have hAν_top : Aν = ⊤ := by
    by_contra hAν_ne
    -- eventually `c_n⁻¹ ≤ 2`.
    have hcinv_ev : ∀ᶠ n : ℕ in atTop, ((P {ω | |W ω| ≤ (n : ℝ)})⁻¹).toReal ≤ 2 := by
      set E : ℕ → Set Ω := fun n => {ω | |W ω| ≤ (n : ℝ)} with hE_def
      have hE_mono : Monotone E := by
        intro p q hpq ω hω
        have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
        exact le_trans hω this
      have hE_union : ⋃ k, E k = Set.univ := by
        rw [Set.eq_univ_iff_forall]; intro ω
        obtain ⟨k, hk⟩ := exists_nat_ge |W ω|
        exact Set.mem_iUnion.2 ⟨k, hk⟩
      have hlim : Tendsto (fun n => P (E n)) atTop (𝓝 1) := by
        have h := tendsto_measure_iUnion_atTop (μ := P) hE_mono
        rw [hE_union, measure_univ] at h
        exact h
      -- `(P (E n))⁻¹.toReal → 1`.
      have hcinv_lim : Tendsto (fun n => ((P (E n))⁻¹).toReal) atTop (𝓝 1) := by
        have hr_lim : Tendsto (fun n => (P (E n)).toReal) atTop (𝓝 1) := by
          have := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hlim
          simpa [Function.comp] using this
        have heq : (fun n => ((P (E n)).toReal)⁻¹) =ᶠ[atTop] fun n => ((P (E n))⁻¹).toReal := by
          filter_upwards [hcn_ev] with n hn; rw [ENNReal.toReal_inv]
        refine Tendsto.congr' heq ?_
        have : Tendsto (fun n => ((P (E n)).toReal)⁻¹) atTop (𝓝 (1 : ℝ)⁻¹) :=
          (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr_lim
        simpa using this
      exact hcinv_lim.eventually_le_const (by norm_num : (1 : ℝ) < 2)
    -- the finite EReal upper bound `(2 * Aν : EReal)`.
    -- eventually `h(ν_n) ≤ (2 * Aν : EReal)`.
    have hub : ∀ᶠ n in atTop,
        differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω))
          ≤ ((2 * Aν : ℝ≥0∞) : EReal) := by
      filter_upwards [hcn_ev, hcinv_ev] with n hn hcinv
      set νn : Measure ℝ := (truncW P W n).map (fun ω => W ω + V ω) with hνn_def
      set cinv : ℝ≥0∞ := (P {ω | |W ω| ≤ (n : ℝ)})⁻¹ with hcinv_def
      -- mass `c_n ∈ (0, 1]` so `cinv ∈ [1, ⊤)`.
      have hcn_ne_top : (P {ω | |W ω| ≤ (n : ℝ)}) ≠ ⊤ := measure_ne_top _ _
      have hcinv_top : cinv ≠ ⊤ := by
        rw [hcinv_def]; exact ENNReal.inv_ne_top.mpr hn
      have hcinv_le_two : cinv ≤ (2 : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_toReal hcinv_top, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
        exact ENNReal.ofReal_le_ofReal hcinv
      -- measure domination `ν_n ≤ cinv • ν` (atom 1).
      have hdom : νn ≤ cinv • ν := by
        rw [hνn_def, hcinv_def, hν_def]
        exact map_truncW_add_le_smul_map_add W V P hW hV n hn
      -- `ν_n ≪ ν ≪ volume`.
      have hνn_ν : νn ≪ ν := by
        rw [hνn_def, hν_def]
        exact map_truncW_add_absolutelyContinuous_map_add W V P hW hV n hn
      have hνn_ac : νn ≪ volume := hνn_ν.trans hν_ac
      haveI hQ_prob : IsProbabilityMeasure (truncW P W n) := by
        rw [truncW]; exact ProbabilityTheory.cond_isProbabilityMeasure hn
      haveI hνn_prob : IsProbabilityMeasure νn := by
        rw [hνn_def]
        exact Measure.isProbabilityMeasure_map (hW.add hV).aemeasurable
      -- `B(ν_n) ≠ ⊤`.
      have hBνn : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((νn.rnDeriv volume x).toReal)))
          ∂volume) ≠ ⊤ := by
        rw [hνn_def]
        exact negPart_lintegral_map_truncW_add_ne_top W V P hW hV hWV hW_ac hBW n hn
      -- `crossNeg ν_n ν ≤ cinv * crossNeg ν ν = cinv * B(ν)`, hence `≠ ⊤`.
      have hCNνn_dom : crossNeg νn ν ≤ cinv * crossNeg ν ν := by
        rw [crossNeg, crossNeg]
        calc (∫⁻ x, ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)) ∂νn)
            ≤ ∫⁻ x, ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)) ∂(cinv • ν) :=
              lintegral_mono' hdom (le_refl _)
          _ = cinv * ∫⁻ x, ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)) ∂ν := by
              rw [lintegral_smul_measure]; rfl
      have hCNν_eq : crossNeg ν ν
          = ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((ν.rnDeriv volume x).toReal))) ∂volume :=
        crossNeg_self ν hν_ac
      have hCNνn_fin : crossNeg νn ν ≠ ⊤ := by
        refine ne_top_of_le_ne_top ?_ hCNνn_dom
        exact ENNReal.mul_ne_top hcinv_top (by rw [hCNν_eq]; exact hBν)
      -- Gibbs (consumer form): `A(ν_n) + crossNeg ≤ crossPos + B(ν_n)`.
      have hgibbs := ennreal_gibbs_rearranged hνn_ac hν_ac hνn_ν hBνn hCNνn_fin
      -- `A(ν_n) ≤ crossPos ν_n ν + B(ν_n)`  (drop the nonneg `crossNeg`).
      have hA_le : (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((νn.rnDeriv volume x).toReal)) ∂volume)
          ≤ crossPos νn ν
            + ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((νn.rnDeriv volume x).toReal))) ∂volume :=
        le_trans (le_add_right (le_refl _)) hgibbs
      -- `h(ν_n) = (A(ν_n):EReal) - (B(ν_n):EReal) ≤ (crossPos ν_n ν : EReal)`.
      have hh_le : differentialEntropyExt νn ≤ ((crossPos νn ν : ℝ≥0∞) : EReal) := by
        rw [differentialEntropyExt_of_ac hνn_ac]
        rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ennreal_ne_bot _))
          (Or.inl ((EReal.coe_ennreal_eq_top_iff).not.mpr hBνn))]
        rw [← EReal.coe_ennreal_add]
        exact_mod_cast hA_le
      -- domination of the positive cross-entropy: `crossPos ν_n ν ≤ cinv * Aν ≤ 2 * Aν`.
      have hCPνn_dom : crossPos νn ν ≤ (2 : ℝ≥0∞) * Aν := by
        have hstep : crossPos νn ν ≤ cinv * crossPos ν ν := by
          rw [crossPos, crossPos]
          calc (∫⁻ x, ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)) ∂νn)
              ≤ ∫⁻ x, ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)) ∂(cinv • ν) :=
                lintegral_mono' hdom (le_refl _)
            _ = cinv * ∫⁻ x, ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)) ∂ν := by
                rw [lintegral_smul_measure]; rfl
        have hCPν_eq : crossPos ν ν = Aν := by
          rw [hAν_def]; exact crossPos_self ν hν_ac
        calc crossPos νn ν ≤ cinv * crossPos ν ν := hstep
          _ = cinv * Aν := by rw [hCPν_eq]
          _ ≤ (2 : ℝ≥0∞) * Aν := by exact mul_le_mul' hcinv_le_two (le_refl _)
      -- chain: `h(ν_n) ≤ (crossPos ν_n ν : EReal) ≤ (2 * Aν : EReal)`.
      calc differentialEntropyExt νn ≤ ((crossPos νn ν : ℝ≥0∞) : EReal) := hh_le
        _ ≤ ((2 * Aν : ℝ≥0∞) : EReal) := by exact_mod_cast hCPνn_dom
    -- contradiction with `h(ν_n) → ⊤`.
    rw [EReal.tendsto_nhds_top_iff_real] at hνn_tendsto
    have h2Aν_fin : (2 * Aν) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hAν_ne
    -- pick `M` larger than `(2 * Aν).toReal` and derive `(M:EReal) < h(ν_n) ≤ (2*Aν:EReal) ≤ (M:EReal)`.
    have hcontra := hνn_tendsto ((2 * Aν).toReal)
    obtain ⟨n, hMn, hubn⟩ := (hcontra.and hub).exists
    have : ((2 * Aν : ℝ≥0∞) : EReal) = (((2 * Aν).toReal : ℝ) : EReal) :=
      (EReal.coe_ennreal_toReal h2Aν_fin).symm
    rw [this] at hubn
    exact absurd (lt_of_lt_of_le hMn hubn) (by simp)
  -- **conclude `h(ν) = ⊤`** : `h(ν) = (Aν:EReal) - (B(ν):EReal) = ⊤ - fin = ⊤`.
  rw [differentialEntropyExt_of_ac hν_ac, ← hAν_def, hAν_top, EReal.coe_ennreal_top,
    ← EReal.coe_ennreal_toReal hBν, EReal.top_sub_coe]

/-! ## 無条件 gateway 単調性 (方針 Y、(i-a) 非依存)

⊥ 枝 (`bot_le`)、有限枝 (`differentialEntropyExt_mono_add_of_integrable`、per-fibre Gibbs)、
⊤ 枝 (`differentialEntropyExt_top_of_indep_add_unconditional`、route β') の 3 部品を組んで
gateway 単調性を無条件で建てる。有限枝は finiteness → integrability の bridge
(`differentialEntropyExt_integrable_of_finite`) を経由する。 -/

/-- **有限微分エントロピー → `negMulLog∘density` 可積分** (`differentialEntropyExt_of_ac_integrable`
の converse)。a.c. + `h(μ) ≠ ⊤` + `h(μ) ≠ ⊥` から、`negMulLog (density)` が `volume` 上可積分。

`differentialEntropyExt_of_ac hac` で `h = (A:EReal) − (B:EReal)` (A/B = 正部・負部 lintegral)。
- `A ≠ ⊤`: A=⊤ なら `(⊤:EReal) − B = ⊤` (B<⊤) で `h=⊤`、`hne_top` に矛盾。
- `B ≠ ⊤`: B=⊤ なら `A − ⊤ = ⊥` (A<⊤) で `h=⊥`、`hne_bot` に矛盾。
- `A<⊤ ∧ B<⊤ ⟹ Integrable`: aestronglyMeasurable + HasFiniteIntegral
  (`∫⁻ ‖negMulLog f‖ₑ = A + B < ⊤`)。

honesty: `hne_top`/`hne_bot` は有限性 regularity precondition (結論 = Integrable を encode せず)。

**独立 honesty audit 2026-06-08 (fresh subagent, commit 64cb872 → ok)**: 4-check 全 PASS。
(1) 非循環 — 結論 `Integrable (negMulLog∘density)` は 3 仮説のいずれとも非同型、body は EReal
分岐 (`hsplit` の `A−B` 展開 + `EReal.sub_top`/`top_sub` で A≠⊤/B≠⊤) → `integrable_of_lintegral_
ofReal_pos_neg_ne_top` で genuine 組立 (`:= h` でない)。(2) 非バンドル — `hac` 絶対連続性、
`hne_top`/`hne_bot` 有限性 regularity precondition、3 仮説 grant しても Integrable は body の
EReal 推論を要し核を encode せず。(3) 非退化 — Integrable は実命題、vacuous/exfalso なし。
(4) **sufficiency (反例試行) — 両仮説 genuine に必要**: `hne_bot` 落とすと A<⊤∧B=⊤ (h=fin−⊤=⊥,
hne_top 成立だが非可積分) が反例、`hne_top` 落とすと A=⊤∧B<⊤ (h=⊤−fin=⊤, hne_bot 成立だが
非可積分) が反例。under-hypothesized でない。`#print axioms` = `[propext, Classical.choice,
Quot.sound]` (sorryAx-free 機械確認、(i-a) `differentialEntropyExt_indep_add_eq_add_klDiv` 非継承)。@audit:ok -/
theorem differentialEntropyExt_integrable_of_finite {μ : Measure ℝ} (hac : μ ≪ volume)
    (hne_top : differentialEntropyExt μ ≠ ⊤) (hne_bot : differentialEntropyExt μ ≠ ⊥) :
    Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume := by
  -- positive- and negative-part lintegrals of the density's `negMulLog`.
  set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume
    with hA_def
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB_def
  -- `h(μ) = (A : EReal) - (B : EReal)`.
  have hsplit : differentialEntropyExt μ = (A : EReal) - (B : EReal) := by
    rw [differentialEntropyExt_of_ac hac]
  -- **`A ≠ ⊤`**: otherwise `⊤ - B` is `⊤` (B≠⊤) or `⊥` (B=⊤), both excluded.
  have hA_ne_top : A ≠ ⊤ := by
    intro hAtop
    by_cases hBtop : (B : EReal) = ⊤
    · -- `⊤ - ⊤ = ⊥` contradicts `hne_bot`.
      apply hne_bot
      rw [hsplit, hAtop, EReal.coe_ennreal_top, hBtop, EReal.sub_top]
    · -- `⊤ - (coe) = ⊤` contradicts `hne_top`.
      apply hne_top
      rw [hsplit, hAtop, EReal.coe_ennreal_top, EReal.top_sub hBtop]
  -- **`B ≠ ⊤`**: with `A < ⊤`, `(A : EReal) - ⊤ = ⊥` contradicts `hne_bot`.
  have hB_ne_top : B ≠ ⊤ := by
    intro hBtop
    apply hne_bot
    rw [hsplit, hBtop, EReal.coe_ennreal_top, EReal.sub_top]
  -- assemble integrability from the two finite lintegrals + measurability.
  refine integrable_of_lintegral_ofReal_pos_neg_ne_top ?_ hA_ne_top hB_ne_top
  exact (Real.continuous_negMulLog.measurable.comp
    (μ.measurable_rnDeriv volume).ennreal_toReal).aestronglyMeasurable

/-- **無条件 gateway 単調性** (方針 Y、(i-a) 非依存): `W a.c. ∧ W ⊥ V ⟹ h(W) ≤ h(W+V)`。
⊥ 枝 = `bot_le`、有限枝 = `differentialEntropyExt_mono_add_of_integrable` (per-fibre Gibbs)、
⊤ 枝 = `differentialEntropyExt_top_of_indep_add_unconditional` (route β')。

旧 `EPIUncondMonotone.differentialEntropyExt_mono_add` の無条件 proof-done 版 (旧版は無条件版②
`differentialEntropyExt_indep_add_eq_add_klDiv` (i-a) に transitive 依存)。本版は (i-a) を継承しない。

**独立 honesty audit 2026-06-08 (fresh subagent, commit 64cb872 → ok)**: 4-check 全 PASS。
(1) 非循環 — 結論 `h(W)≤h(W+V)` は 4 仮説のいずれとも非同型、body は genuine 3 枝場合分け。
(2) 非バンドル — `hW`/`hV`/`hWV`/`hW_ac` は可測/独立/絶対連続 regularity、核 (単調性) は body の
3 枝 (⊥=`bot_le` / ⊤=route β' `@audit:ok` / 有限=per-fibre Gibbs `@audit:ok` + bridge) が担う。
(3) 非退化 — ⊤ 枝の `⊤≤⊤` は route β' `differentialEntropyExt_top_of_indep_add_unconditional`
(genuine, `@audit:ok`) で `h(W+V)=⊤` を確立してから閉じる、退化定義悪用でない。
(4) **sufficiency (反例試行) — 含意 TRUE**: 「独立ノイズ加算は微分エントロピーを減らさない」の genuine
EPI 単調性、`hW_ac`/`hWV` は genuine に必要。under-hypothesized でない。**name-laundering check —
NOT laundering**: `_unconditional` = (i-a) sorryAx 非継承の proof-route 主張で正当、open load-bearing
hyp も偽装 sorry-body も無し。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free
機械確認、axiom 出力に (i-a) `differentialEntropyExt_indep_add_eq_add_klDiv` 不在で非継承を独立裏取り)。@audit:ok -/
theorem differentialEntropyExt_mono_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume) :
    differentialEntropyExt (P.map W) ≤ differentialEntropyExt (P.map (fun ω => W ω + V ω)) := by
  -- **⊥ branch**: `h(W) = ⊥ ≤ anything`.
  rcases eq_bot_or_bot_lt (differentialEntropyExt (P.map W)) with hbot | hpos
  · rw [hbot]; exact bot_le
  · have hne_bot : differentialEntropyExt (P.map W) ≠ ⊥ := hpos.ne'
    by_cases htop : differentialEntropyExt (P.map W) = ⊤
    · -- **⊤ branch**: route β' gives `h(W+V) = ⊤`, so `⊤ ≤ ⊤`.
      rw [htop, differentialEntropyExt_top_of_indep_add_unconditional W V P hW hV hWV hW_ac htop]
    · -- **finite branch**: bridge finiteness → integrability, then per-fibre Gibbs.
      exact differentialEntropyExt_mono_add_of_integrable W V P hW hV hWV hW_ac
        (differentialEntropyExt_integrable_of_finite hW_ac htop hne_bot)

/-- **無条件 gateway atom** (方針 Y): `W a.c. ∧ W ⊥ V ⟹ N(W+V) ≥ N(W)`。
`differentialEntropyExt_mono_add_unconditional` を `EReal.exp_monotone` で `entropyPowerExt`
(= `EReal.exp (2 · differentialEntropyExt)`) に lift。proof-done (i-a 非依存)。

**独立 honesty audit 2026-06-08 (fresh subagent, commit 64cb872 → ok)**: `mono_add_unconditional`
(@audit:ok) の genuine な `EReal.exp_monotone` lift (`mul_le_mul_of_nonneg_left ... (2≥0)` 経由)、
循環/bundling なし。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認、
(i-a) 非継承)。@audit:ok -/
theorem entropyPowerExt_mono_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume) :
    entropyPowerExt (P.map (fun ω => W ω + V ω)) ≥ entropyPowerExt (P.map W) := by
  unfold entropyPowerExt
  apply EReal.exp_monotone
  exact mul_le_mul_of_nonneg_left
    (differentialEntropyExt_mono_add_unconditional W V P hW hV hWV hW_ac) (by norm_num)


end InformationTheory.Shannon

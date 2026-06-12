import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.AchievabilityAEP
import InformationTheory.Shannon.BlockwiseChannel
import InformationTheory.Shannon.ChannelCoding.MIDecomp
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Draft.Shannon.MultivariateDiffEntropy
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# AWGN Walls — shared sorry 補題集約 file

Parent plan: `docs/shannon/awgn-m5-sorry-migration-plan.md` Phase 2.

10 declaration の Tier 3 (`@audit:retract-candidate(load-bearing-predicate)`、
bookkeeping) → Tier 2 (`sorry` + `@residual(<class>:<slug>)`、honest 撤退口) 移行に
おいて、analytic content の Mathlib 壁を「shared sorry 補題」(`docs/audit/audit-tags.md`
「共有 Mathlib 壁: shared sorry 補題パターン」) として 1 ヶ所に集約する file。

Phase 2 = shared sorry 補題の signature + body sorry 残置のみ (Phase 3 で consumer
側の predicate 削除 + signature 書換)。本 file 単独で type-check done。

## Achievability-side 補題 (δ-separation + D4 後の現状)

| 補題名 | 状態 | 備考 |
|---|---|---|
| `continuousAepGaussian_holds` | δ-separated, 2 deep-atom sorry (`@residual(plan:awgn-achievability-walls-discharge-plan)`) | (ii) 削除済 / (iii) δ-exponent。残: `hφ_memLp` + (iii) change-of-measure |
| `awgnPowerConstraintPerCodeword_holds` | genuine, sorryAx-free | per-codeword expurgation 形 (false `∀m`-form の置換) |

**RETIRED (2026-06-12, D4)**: false `awgnRandomCodingBound_holds` (`∀decoder` 過大) +
`awgnPowerConstraintHonest_holds` (`∀m` 指数 rate unsatisfiable) は削除済 (本 file 下部
の retire note 参照)。union bound の genuine 形 `awgn_random_coding_union_bound` は
consumer file (`AchievabilityDischarge.lean`) に置く (kernel/decoder が local)。

## Signature 設計方針 (Mathlib-shape-driven)

- `continuousAepGaussian_holds`: 旧 predicate body と verbatim 同型 (`gaussianCodebook`
  不使用 / 2 段 `Measure.pi` の inline 形で書き、consumer は `gaussianCodebook` ≡ 2 段
  `Measure.pi` defeq で接続)。slack `δ` を error 目標 `ε` と分離した形。

## Import policy

`AWGN.lean` 経由で `ChannelCoding.Code` / `errorEvent` などへの transitive access あり
(本 file 内で `Code.mk` を直接書かないため、明示 import 不要)。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Wall 1 — `awgn-continuous-aep-gaussian`

(Note: the former Wall 0 `contChannelMIDecomp_holds` — the continuous-channel MI
chain rule `I(X;Y) = h(Y) − h(Y|X)` — was **closed 2026-05-28**: it is now assembled
genuinely from local helpers in
`InformationTheory.Draft.Shannon.ContChannelMIDecomp.mutualInfoOfChannel_toReal_eq_diffEntropy_sub`
(0 sorry), so no shared wall is needed. This file's active wall count is now **3**:
Wall 6 `awgn-converse-markov-regularity` was **genuine-closed 2026-06-04**
(`awgnConverseMarkov_holds` is sorryAx-free, see its docstring); Wall 4
`awgn-per-letter-integrability` was **genuine-closed 2026-06-10**
(`awgnPerLetterIntegrability_holds` is sorryAx-free — the wall verdict over-claimed:
the per-letter law is a finite 1-D Gaussian mixture, no SMB needed); Wall 5
`awgn-continuous-mi-chain-rule` was **genuine-closed 2026-06-12**
(`awgnContinuousMIChainRule_holds` is sorryAx-free — W-input route: deterministic DPI +
generic n-D channel MI decomposition + n-D subadditivity + per-letter 1-D decomposition;
the wall verdict over-claimed continuous-output MI chain machinery). Remaining active
walls (all achievability-side): 1 `awgn-continuous-aep-gaussian`, 2
`awgn-random-coding-bound`, 3 `awgn-power-constraint-honest`.) -/

/-- **Continuous AEP for n-dim Gaussian** (Phase B-0 wall, 旧 `IsContinuousAEPGaussian`).

Given `P : ℝ`, `N : ℝ≥0`, a **typicality slack** `δ > 0` and an **error tolerance**
`ε > 0` (separated as independent parameters), there exists a threshold `N₀` such that
for every `n ≥ N₀`, a measurable typical set `A ⊆ (Fin n → ℝ) × (Fin n → ℝ)` exists
satisfying the 2 AEP sub-bounds:

* **(i) joint codebook+noise mass `≥ 1 - ε`**: under the joint law of `(X, Y)` with
  `X ∼ N(0,P)` i.i.d. and `Y = X + Z`, `Z ∼ N(0,N)` i.i.d.;
* **(iii) independent-pair upper bound** (`X'` independent of `Y`): under the product
  of marginals, `A` has mass `≤ exp(−(klDiv_n − n·3δ)) = exp(−n(I − 3δ))`, where
  `klDiv_n = klDiv(joint, product) = n·I` is the n-letter KL (per-letter MI `I`).

The slack `δ` controls the typical set's width (engine slack); the error target `ε`
controls the mass-failure level of (i). Decoupling them lets the consumer pick
`R + 3δ < I` (typicality margin) independently of the error goal `ε`, which is what
makes the union-bound's second term honestly decay (the previous `δ ≡ ε` coupling made
the union bound's term-2 false-as-framed when `3ε ≥ I`).

**STATUS (2026-06-12) — sub-bound (ii) DELETED; (iii) STATEMENT-FIXED (exponent
n-normalized); (i)/(iii) targeted for genuine closure via engine + change-of-measure.**

* **(ii) volume bound REMOVED (earlier phase):** the old (ii) `klDiv`-to-`volume` form was
  a false statement (`volume univ = ⊤ ⇒ ν.real univ = 0` clamps the term to 0), not a
  Mathlib gap. The consumer discarded it and the union-bound's second-term mass is supplied
  by (iii), so (ii) was non-load-bearing. Excised (not statement-fixed).
* **(i) genuine (engine):** the AEP mass concentration needs only a finite-`n` Chebyshev
  weak law (`pi_empirical_mean_concentration` / `pi_empirical_mean_typical_mass`,
  `AchievabilityAEP.lean`, sorryAx-free). The typical set `A` is built from the per-letter
  joint info-density `φ(x,y) = log dJ₁/dQ₁`, wired into the engine's abstract `μ`/`φ`.
* **(iii) STATEMENT-FIXED (exponent n-normalized) + δ-SEPARATED:** the previous form
  double-counted `n` (`−n·(klDiv_n − 3ε) = −n²·I + 3nε`, false because `klDiv_n = n·I`
  already carries one factor of `n`). The corrected exponent is `−(klDiv_n − n·3δ) =
  −n·(I − 3δ)` — a single factor of `n`, with the **typicality slack `δ`** (not the error
  target `ε`), matching the standard independent-pair AEP change-of-measure bound
  `product(A) = ∫_A exp(−∑φ) d(joint) ≤ exp(−(klDiv_n − n·δ'))`. `klDiv_n = n·I` follows
  from `klDiv_pi_eq_sum` / `klDiv_prod_eq_add` after the `arrowProdEquivProdArrow` reshape
  (both measures are probability measures), exactly as in `mutualInfo_pi_eq_sum`. The
  consumer (`AchievabilityDischarge.lean`) currently discards this bound; Phase 4's D2
  union-bound is the first real consumer.

@residual(plan:awgn-achievability-walls-discharge-plan) -/
theorem continuousAepGaussian_holds (P : ℝ) (N : ℝ≥0) :
    ∀ ⦃δ ε : ℝ⦄, 0 < δ → 0 < ε → ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
      ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
        MeasurableSet A
        ∧ (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
              (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                  (p.1, fun i => p.1 i + p.2 i))) A
            ≥ ENNReal.ofReal (1 - ε)
        ∧ ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
              (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))) A
            ≤ ENNReal.ofReal (Real.exp (-(
                (klDiv
                    (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                        (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
                      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                          (p.1, fun i => p.1 i + p.2 i)))
                    ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                      (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))))).toReal
                  - (n : ℝ) * (3 * δ)))) := by
  intro δ ε hδ hε
  classical
  -- Per-letter measures (abbreviating `P' := P.toNNReal`).
  set μX : Measure ℝ := gaussianReal 0 P.toNNReal with hμX_def
  set μZ : Measure ℝ := gaussianReal 0 N with hμZ_def
  set μY : Measure ℝ := gaussianReal 0 (P.toNNReal + N) with hμY_def
  -- per-letter joint law of `(X, X+Z)` and product of marginals
  set J₁ : Measure (ℝ × ℝ) := (μX.prod μZ).map (fun p => (p.1, p.1 + p.2)) with hJ₁_def
  set Q₁ : Measure (ℝ × ℝ) := μX.prod μY with hQ₁_def
  -- per-letter info density `φ = log dJ₁/dQ₁` (= `llr J₁ Q₁`)
  set φ : ℝ × ℝ → ℝ := fun p => Real.log ((J₁.rnDeriv Q₁ p).toReal) with hφ_def
  haveI : IsProbabilityMeasure J₁ := by
    rw [hJ₁_def]
    exact Measure.isProbabilityMeasure_map
      (measurable_fst.prodMk (measurable_fst.add measurable_snd)).aemeasurable
  haveI : IsProbabilityMeasure Q₁ := by rw [hQ₁_def]; infer_instance
  -- `MemLp φ 2 J₁`: the info density is a quadratic polynomial in `(x, y)` (the
  -- difference of two Gaussian log-densities, nondegenerate case `P', N > 0`; in the
  -- degenerate case `J₁ ⊀ Q₁` so `φ = 0` a.e.), hence lies in L² of the joint law.
  -- @residual(plan:awgn-achievability-walls-discharge-plan)
  have hφ_memLp : MemLp φ 2 J₁ := by
    sorry
  -- Engine: choose `N₀` so the empirical-mean typical set (slack `δ`) has mass
  -- `≥ 1 - ε` (the engine's `ε`-slot = our typicality slack `δ`, `η`-slot = error
  -- target `ε`, separated so the (iii) exponent uses `δ` independently of `ε`).
  obtain ⟨N₀, hN₀⟩ :=
    pi_empirical_mean_typical_mass J₁ hφ_memLp (ε := δ) (η := ε) hδ hε
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le Nat.one_pos (le_of_max_le_right hn)
  -- The reshaping equiv `(Fin n → ℝ × ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → ℝ)`.
  set e : (Fin n → ℝ × ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → ℝ) :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) with he_def
  -- Engine typical set on `Fin n → ℝ × ℝ`.
  set B : Set (Fin n → ℝ × ℝ) :=
    {w : Fin n → ℝ × ℝ | |(∑ i, φ (w i)) / (n : ℝ) - J₁[φ]| < δ} with hB_def
  -- The signature's set `A` is `B` pulled back through `e.symm`.
  -- `φ` is measurable (log ∘ toReal ∘ rnDeriv), hence `B` is measurable.
  have hφ_meas : Measurable φ := by
    rw [hφ_def]
    exact Real.measurable_log.comp (Measure.measurable_rnDeriv J₁ Q₁).ennreal_toReal
  have hB_meas : MeasurableSet B := by
    rw [hB_def]
    have hsum : Measurable (fun w : Fin n → ℝ × ℝ => (∑ i, φ (w i)) / (n : ℝ) - J₁[φ]) :=
      ((Finset.measurable_sum _
        (fun i _ => hφ_meas.comp (measurable_pi_apply i))).div_const _).sub_const _
    have hT : MeasurableSet {r : ℝ | |r| < δ} :=
      measurableSet_lt (measurable_norm.comp measurable_id) measurable_const
    exact hsum hT
  -- **Joint measure-identity**: the signature's joint law equals `(Measure.pi J₁).map e`.
  -- `g ∘ e = e ∘ H` where `g (x,z) = (x, x+z)` (the AWGN map) and `H` applies
  -- `(a,b) ↦ (a, a+b)` componentwise; reshape via `arrowProdEquivProdArrow` + `pi_map_pi`.
  set g : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
    fun p => (p.1, fun i => p.1 i + p.2 i) with hg_def
  set h₁ : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.1 + p.2) with hh₁_def
  set H : (Fin n → ℝ × ℝ) → (Fin n → ℝ × ℝ) := fun w i => h₁ (w i) with hH_def
  have hg_meas : Measurable g := by
    rw [hg_def]; exact measurable_fst.prodMk (measurable_pi_lambda _
      (fun i => (measurable_pi_apply i).comp measurable_fst |>.add
        ((measurable_pi_apply i).comp measurable_snd)))
  have hh₁_meas : Measurable h₁ := by
    rw [hh₁_def]; exact measurable_fst.prodMk (measurable_fst.add measurable_snd)
  have hH_meas : Measurable H :=
    measurable_pi_lambda _ (fun i => hh₁_meas.comp (measurable_pi_apply i))
  have hJ_eq :
      ((Measure.pi (fun _ : Fin n => μX)).prod (Measure.pi (fun _ : Fin n => μZ))).map g
        = (Measure.pi (fun _ : Fin n => J₁)).map e := by
    -- reshape `(pi μX).prod (pi μZ) = (pi (μX × μZ)).map e`
    have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
      (fun _ : Fin n => μX) (fun _ : Fin n => μZ)
    have hprod_reshape :
        (Measure.pi (fun _ : Fin n => μX)).prod (Measure.pi (fun _ : Fin n => μZ))
          = (Measure.pi (fun _ : Fin n => μX.prod μZ)).map e := by
      rw [he_def, ← hmp.map_eq]
    -- `pi J₁ = (pi (μX × μZ)).map H` via `pi_map_pi`
    have hpiJ₁ :
        Measure.pi (fun _ : Fin n => J₁)
          = (Measure.pi (fun _ : Fin n => μX.prod μZ)).map H := by
      rw [hH_def, hJ₁_def]
      rw [Measure.pi_map_pi (f := fun _ : Fin n => h₁) (fun _ => hh₁_meas.aemeasurable)]
    rw [hprod_reshape, hpiJ₁, Measure.map_map hg_meas e.measurable,
      Measure.map_map e.measurable hH_meas]
    -- `g ∘ e = e ∘ H` pointwise (the two pushforward maps coincide)
    rfl
  refine ⟨e.symm ⁻¹' B, ?_, ?_, ?_⟩
  · -- measurability of `A`
    exact e.symm.measurable hB_meas
  · -- (i) joint mass `≥ 1 - ε` via the engine + the joint measure-identity
    rw [hJ_eq, Measure.map_apply e.measurable (e.symm.measurable hB_meas)]
    have he_preim : e ⁻¹' (e.symm ⁻¹' B) = B := by
      ext w; simp [Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
    rw [he_preim]
    exact hN₀ (le_of_max_le_left hn)
  · -- (iii) product mass `≤ exp(−(klDiv_n − n·3δ))` via change of measure.
    -- On `A`, `∑φ > n(J₁[φ] − δ)` (typicality slack `δ`, decoupled from the error
    -- target `ε`); the tensorized RN-derivative `dJ/dQ = exp(∑φ)` gives
    -- `Q(A) = ∫_A exp(−∑φ) dJ ≤ exp(−n(J₁[φ] − δ)) · J(A) ≤ exp(−(klDiv_n − n·3δ))`,
    -- using `J₁[φ] = (klDiv J₁ Q₁).toReal` and `klDiv_n = n · klDiv(J₁,Q₁)` (the latter from
    -- `klDiv_pi_eq_sum` / `klDiv_prod_eq_add` after the `arrowProdEquivProdArrow` reshape, both
    -- probability measures). The RN-derivative tensorization + `setLIntegral` change of measure
    -- is the genuine Mathlib-absent wiring core.
    -- @residual(plan:awgn-achievability-walls-discharge-plan)
    sorry

/-! ## Wall 2 / Wall 3 — RETIRED false statements (2026-06-12, D4)

The two old false achievability walls were **deleted** in the δ-separation + D4
consumer rewire:

* `awgnRandomCodingBound_holds` (`∀decoder` abstraction, false by the constant
  decoder `fun _ _ ↦ m₀` counterexample) → replaced by the genuine δ-separated
  `awgn_random_coding_union_bound` (decoder fixed to `jointTypicalDecoder A`, the
  two AEP bounds threaded as arguments) in `AchievabilityDischarge.lean`.
* `awgnPowerConstraintHonest_holds` (`∀m`-form, mass `= q^M` unsatisfiable for `R`
  near capacity) → replaced by the per-codeword expurgation form
  `awgnPowerConstraintPerCodeword_holds` below (Phase 5a, sorryAx-free), which the
  consumer's per-codeword combined-penalty barrier consumes.

Wall name register entries `awgn-random-coding-bound` / `awgn-power-constraint-honest`
in `docs/audit/audit-tags.md` are now stale (no active `@residual(wall:…)`). -/

/-- **Per-codeword power-constraint expurgation bound** (Phase 5a / D3, genuine
replacement for the false `∀ m`-form power-constraint wall).

For a codebook drawn from the 2-stage Gaussian product law at codeword variance
`P_cb`, and a power target `P_target` with strict slack `P_cb < P_target`, each
*individual* codeword `m` violates the power budget `∑ᵢ (c m i)² > n · P_target`
on a codebook set of mass `≤ ε` (for all `n` past a threshold `N₀`).

This is the **per-codeword marginal** form: unlike the false `∀ m`-form (mass of
the all-codewords-OK set `≥ 1 − ε`, which decays like `q^M ≈ exp(−exp(n(R−ψ)))`),
the per-codeword marginal mass is `M`-independent (the `m`-th coordinate marginal
of `Measure.pi (fun _ : Fin M => νₙ)` is `νₙ`), so no exponential rate / capacity
rate bound is needed. It is exactly the WLLN/Markov fact the Cover–Thomas
expurgation argument consumes.

Proof: the `m`-th coordinate marginal is `νₙ = Measure.pi (fun _ : Fin n =>
gaussianReal 0 P_cb.toNNReal)` (`measurePreserving_eval`), reducing the codebook
mass to the single-codeword chi-square upper-tail mass. Apply the abstract
Chebyshev engine `pi_empirical_mean_concentration` with statistic `φ x = x²`,
`μ[φ] = (P_cb.toNNReal : ℝ)` (centred Gaussian second moment = variance), and the
deviation level `δ = P_target − (P_cb.toNNReal : ℝ) > 0`: the violating set
`{x | n·P_target < ∑ᵢ xᵢ²}` is contained in the deviation set
`{x | δ ≤ |(∑ᵢ φ(xᵢ))/n − μ[φ]|}`, whose mass is `≤ variance(φ)/(n·δ²)`; choosing
`N₀ > variance(φ)/(ε·δ²)` gives `≤ ε`. `MemLp φ 2` holds because the Gaussian has a
finite 4th moment (`memLp_id_gaussianReal 4`, polynomial — no log). -/
theorem awgnPowerConstraintPerCodeword_holds
    (P_cb P_target : ℝ) (hP_slack : (P_cb.toNNReal : ℝ) < P_target) (N : ℝ≥0) :
    ∀ ⦃ε : ℝ⦄, 0 < ε →
      ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n → ∀ ⦃M : ℕ⦄ (_hM_pos : 0 < M),
        ∀ m : Fin M,
          (Measure.pi
              (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 P_cb.toNNReal)))
            {c : Fin M → Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (c m i) ^ 2}
          ≤ ENNReal.ofReal ε := by
  classical
  -- Abbreviations: codeword law `μ`, statistic `φ = x²`, mean `μ[φ] = variance = P_cb`.
  set v : ℝ≥0 := P_cb.toNNReal with hv_def
  set μ : Measure ℝ := gaussianReal 0 v with hμ_def
  set φ : ℝ → ℝ := fun x => x ^ 2 with hφ_def
  -- `φ ∈ MemLp 2` via finite 4th moment of the Gaussian.
  have hφ_mem : MemLp φ 2 μ := by
    have hmeas : AEStronglyMeasurable φ μ := by
      rw [hφ_def]; exact (measurable_id.pow_const 2).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmeas]
    -- `Integrable (fun x => (x²)²) = Integrable (fun x => x⁴)`, from `MemLp id 4`.
    have hmem4 : MemLp (id : ℝ → ℝ) 4 μ := by
      rw [hμ_def]; exact memLp_id_gaussianReal' 4 (by simp)
    have hint4 : Integrable (fun x : ℝ => ‖(id : ℝ → ℝ) x‖ ^ 4) μ :=
      hmem4.integrable_norm_pow (by norm_num)
    refine hint4.congr ?_
    filter_upwards with x
    rw [hφ_def]
    simp only [id_eq, Real.norm_eq_abs]
    rw [← abs_pow, abs_of_nonneg (by positivity)]
    ring
  -- `μ[φ] = (v : ℝ)` (centred Gaussian second moment = variance).
  have hμφ : μ[φ] = (v : ℝ) := by
    have hmem_id : MemLp (id : ℝ → ℝ) 2 μ := by
      rw [hμ_def]; exact memLp_id_gaussianReal' 2 (by simp)
    have hvar : variance (id : ℝ → ℝ) μ = (v : ℝ) := by
      rw [hμ_def]; exact variance_id_gaussianReal
    have hsub := variance_eq_sub hmem_id
    have hmean : μ[(id : ℝ → ℝ)] = 0 := by
      rw [hμ_def]; simp [integral_id_gaussianReal (μ := (0 : ℝ)) (v := v)]
    rw [hvar, hmean] at hsub
    -- `hsub : (v : ℝ) = μ[id ^ 2] - 0 ^ 2`.
    have hid2 : (μ[(id : ℝ → ℝ) ^ 2]) = μ[φ] := by
      congr 1
    rw [hid2] at hsub
    simpa using hsub.symm
  -- The strict deviation level.
  set δ : ℝ := P_target - (v : ℝ) with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith [hP_slack]
  intro ε hε
  -- Choose `N₀` so that `variance φ μ / (N₀ · δ²) ≤ ε`, mirroring the engine's own
  -- existence construction.
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (variance φ μ / (ε * δ ^ 2))
  refine ⟨N₀ + 1, fun n hn M _hM_pos m => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.succ_pos N₀) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  -- The `m`-th coordinate marginal of the codebook law is `νₙ = Measure.pi μ`.
  have hmarg :
      (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => μ)))
          {c : Fin M → Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (c m i) ^ 2}
        = (Measure.pi (fun _ : Fin n => μ))
            {x : Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (x i) ^ 2} := by
    have hmp :
        MeasurePreserving (Function.eval m)
          (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => μ)))
          (Measure.pi (fun _ : Fin n => μ)) :=
      measurePreserving_eval (fun _ : Fin M => Measure.pi (fun _ : Fin n => μ)) m
    have hmeasSet :
        MeasurableSet {x : Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (x i) ^ 2} := by
      apply measurableSet_lt measurable_const
      exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).pow_const 2)
    have hpre :
        {c : Fin M → Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (c m i) ^ 2}
          = (Function.eval m) ⁻¹' {x : Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (x i) ^ 2} := by
      rfl
    rw [hpre, hmp.measure_preimage hmeasSet.nullMeasurableSet]
  rw [hmarg]
  -- The violating set is contained in the level-`δ` deviation set.
  have hsubset :
      {x : Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (x i) ^ 2}
        ⊆ {x : Fin n → ℝ | δ ≤ |(∑ i, φ (x i)) / (n : ℝ) - μ[φ]|} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    -- `∑ᵢ φ(xᵢ) = ∑ᵢ xᵢ²` since `φ = (·)²`.
    have hsumφ : (∑ i, φ (x i)) = ∑ i, (x i) ^ 2 := by simp [hφ_def]
    rw [hsumφ, hμφ]
    -- From `n·P_target < ∑ xᵢ²` and `n > 0`: `δ < (∑ xᵢ²)/n − v`.
    have hkey : δ < (∑ i, (x i) ^ 2) / (n : ℝ) - (v : ℝ) := by
      have hdiv : P_target < (∑ i, (x i) ^ 2) / (n : ℝ) := by
        rw [lt_div_iff₀ hnR]; linarith [hx]
      show P_target - (v : ℝ) < (∑ i, (x i) ^ 2) / (n : ℝ) - (v : ℝ)
      linarith
    exact le_of_lt (lt_of_lt_of_le hkey (le_abs_self _))
  -- Mass of the violating set ≤ mass of the deviation set ≤ variance/(n·δ²) ≤ ε.
  have hdev := pi_empirical_mean_concentration μ hφ_mem hδ_pos hn0
  have hviol_le := measure_mono (μ := Measure.pi (fun _ : Fin n => μ)) hsubset
  refine le_trans (le_trans hviol_le hdev) ?_
  -- `variance φ μ / (n · δ²) ≤ ε`.
  apply ENNReal.ofReal_le_ofReal
  have hVarnn : (0 : ℝ) ≤ variance φ μ := variance_nonneg φ μ
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hεδ : (0 : ℝ) < ε * δ ^ 2 := by positivity
  -- `variance / (ε·δ²) < N₀ ≤ n`.
  have hNn : variance φ μ / (ε * δ ^ 2) < (n : ℝ) := by
    calc variance φ μ / (ε * δ ^ 2) < (N₀ : ℝ) := hN₀
      _ ≤ (n : ℝ) := by exact_mod_cast le_trans (Nat.le_succ N₀) hn
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hεδ] at hNn
  nlinarith [hNn, hVarnn, hδ2, hnR]

/-! ## Converse-side walls — `awgn-per-letter-integrability` / `awgn-continuous-mi-chain-rule`
/ `awgn-converse-markov-regularity`

Phase 3-α (`docs/shannon/awgn-m5-sorry-migration-plan.md`) で `AWGNConverseDischarge.lean`
の 3 sub-bound predicate (`PerLetterIntegrabilityForConverse` /
`ContinuousMIChainRuleForConverse` / `MarkovChainForConverse`) + bundle
`IsAwgnConverseFeasible` を削除し、各 sub-bound の analytic content を shared sorry
補題に格上げする。

**Import cycle 回避**: 旧 predicate body は `awgnConverseJoint` / `perLetterYLaw` /
`perLetterMI` / `jointMIXnYn` (いずれも `AWGNConverseDischarge.lean` 定義) を参照する。
これら named def を本 file から直接参照すると `AwgnWalls → AWGNConverseDischarge →
AwgnWalls` の import cycle になるため、`awgnConverseJoint` の body を本 file の
private mirror def `converseJointInline` に inline する (両 def は同一 RHS なので
**defeq**: consumer 側 `unfold awgnConverseJoint perLetterYLaw …` で goal が本 file の
inline 形に一致し、shared 補題が適用可能)。

**Markov の Route 判定 (Phase 3α-1, 更新)**: `MarkovChainForConverse` の genuine 化
(`IsMarkovChain (awgnConverseJoint) Prod.fst (encoder∘fst) Prod.snd`) は当初 Route B
(shared sorry, wall `awgn-converse-markov-regularity`) で撤退したが、独立壁再評価で「真の
Mathlib 不在ではなく deterministic-encoder factorization plumbing 過大評価」と判定され、
`awgnConverseMarkov_holds` で **genuine 化完了** (mixture-of-diracs 上の message-space
marginal `μ = (μ.map fst) ⊗ₘ (W.comap encoder)` を起点に `condDistrib` 同定、precedent
`BlockwiseChannel.isMarkovChain_per_letter_input`)。

**Wall 4 `awgn-per-letter-integrability` の closure (2026-06-10)**: 当初の wall verdict
(continuous SMB / n-dim `differentialEntropy`) は **過大評価** だった。実際の goal は
`volume` 上の **1 次元** integrability で、per-letter 出力法 `Y_i` は有限 Gaussian 混合
`(1/M) ∑ₘ 𝒩(encoder m i, N)` (`perLetterLaw_eq_mixture`)、その `rnDeriv volume` は混合
密度 `perLetterMixtureDensity` (`perLetterLaw_withDensity`)。`negMulLog` of density を
Gaussian moment integrand で dominate して genuine 化 (`awgnPerLetterIntegrability_holds`
は sorryAx-free)。連続入力版 `outputDistribution_logDensity_integrable` を mirror した形
だが、有限混合ゆえ Chebyshev 集中不要 (lower bound は単一成分で出る)。cause:single-route
(壁判定が 1 ルート = SMB のみ想定で、1-D 混合密度の直接 domination ルートを見落とした)。

よって converse-side の active wall は **0 件** (Wall 1/2/3 = achievability 系のみ残存)、
Markov / per-letter integrability / MI chain rule (Wall 5) は全て genuine。 -/

/-- Mirror of `awgnConverseJoint` (`AWGNConverseDischarge.lean:65`) body, inlined here
to break the would-be import cycle. Defeq to `awgnConverseJoint h_meas c` (both `def`s
share the same RHS, so consumer-side `unfold awgnConverseJoint` reduces to this form). -/
private noncomputable def converseJointInline
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) :
    Measure (Fin M × (Fin n → ℝ)) :=
  ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) •
    ∑ m : Fin M,
      (Measure.dirac m).prod
        (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i)))

/-- `converseJointInline` is a probability measure for `M ≥ 1` (mixture with weights
`1/M` summing to 1). Mirror of `awgnConverseJoint.instIsProbabilityMeasure`
(`AWGNConverseDischarge.lean:77`); needed so `IsMarkovChain`'s `[IsFiniteMeasure μ]`
prerequisite resolves on the inlined joint. -/
private instance converseJointInline.instIsProbabilityMeasure
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsProbabilityMeasure (converseJointInline h_meas c) := by
  refine ⟨?_⟩
  unfold converseJointInline
  rw [Measure.smul_apply, Measure.finsetSum_apply _ _ Set.univ]
  have h_summand : ∀ m : Fin M,
      ((Measure.dirac m).prod
          (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))))
            Set.univ = 1 := fun _ => measure_univ
  simp only [h_summand, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  have hM_ne_zero : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hM_ne_top : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
  exact ENNReal.inv_mul_cancel hM_ne_zero hM_ne_top

/-! ### Wall 4 — `awgn-per-letter-integrability`

**Genuine closure (2026-06-10).** The wall verdict (continuous SMB / n-dim
`differentialEntropy`) over-claimed: the actual goal is a **1-dimensional** integrability
against `volume` on `ℝ`. The per-letter output law `Y_i` is a **finite mixture of shifted
1-D Gaussians** `(1/M) ∑ₘ 𝒩(encoder m i, N)`, so its `rnDeriv volume` is the finite
Gaussian-mixture density `(1/M) ∑ₘ gaussianPDF (encoder m i) N`. `negMulLog` of that density
is dominated by a Gaussian moment integrand — pure 1-D measure-theoretic domination, no SMB.
The proof mirrors the continuous-input analogue
`AwgnCapacityConverseMaxent.outputDistribution_logDensity_integrable` (not importable here —
import cycle), but is simpler: the finite mixture needs no Chebyshev concentration (the
lower bound comes from a single component). -/

/-- The finite per-letter Gaussian-mixture density at coordinate `i`:
`(1/M) ∑ₘ gaussianPDF (encoder m i) N y` (`ℝ≥0∞`-valued). For `M ≥ 1` and `N ≠ 0` this is
the `rnDeriv volume` of the per-letter output law `(converseJointInline h_meas c).map (·.2 i)`. -/
private noncomputable def perLetterMixtureDensity
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (y : ℝ) : ℝ≥0∞ :=
  ((M : ℝ≥0∞))⁻¹ * ∑ m : Fin M, gaussianPDF (c.encoder m i) N y

private lemma perLetterMixtureDensity_measurable
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) :
    Measurable (perLetterMixtureDensity N c i) := by
  unfold perLetterMixtureDensity
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_sum _ (fun m _ => measurable_gaussianPDF (c.encoder m i) N)

/-- The per-letter output law equals the explicit finite Gaussian mixture
`(1/M) • ∑ₘ 𝒩(encoder m i, N)` (the decisive atom: pushforward of the inlined joint
mixture-of-diracs⊗pi through `ω ↦ ω.2 i`, marginalizing the `pi` to its `i`-th factor). -/
private lemma perLetterLaw_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) :
    (converseJointInline h_meas c).map (fun ω => ω.2 i)
      = ((M : ℝ≥0∞))⁻¹ • ∑ m : Fin M, gaussianReal (c.encoder m i) N := by
  classical
  have hf_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) => ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  unfold converseJointInline
  rw [Measure.map_smul, Measure.map_finset_sum hf_meas.aemeasurable]
  simp only [Fintype.card_fin]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  -- `((dirac m).prod (pi μ_m)).map (·.2 i) = gaussianReal (encoder m i) N`
  -- via `map ((eval i) ∘ snd) = (map snd).map (eval i)`.
  have h_comp : (fun ω : Fin M × (Fin n → ℝ) => ω.2 i)
      = (Function.eval i) ∘ (Prod.snd : Fin M × (Fin n → ℝ) → (Fin n → ℝ)) := rfl
  rw [h_comp, ← Measure.map_map (measurable_pi_apply i) measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul,
    Measure.pi_map_eval]
  -- `∏ j ∈ erase i, (awgnChannel N (encoder m j)) univ = 1` (each fibre is a prob measure)
  have h_prod_one : (∏ j ∈ Finset.univ.erase i,
      (awgnChannel N h_meas (c.encoder m j)) Set.univ) = 1 := by
    refine Finset.prod_eq_one (fun j _ => ?_)
    rw [awgnChannel_apply]; exact measure_univ
  rw [h_prod_one, one_smul, awgnChannel_apply]

/-- For `M ≥ 1` and `N ≠ 0`, the per-letter output law is
`volume.withDensity (perLetterMixtureDensity c i)`. -/
private lemma perLetterLaw_withDensity
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (hN : N ≠ 0) :
    (converseJointInline h_meas c).map (fun ω => ω.2 i)
      = volume.withDensity (perLetterMixtureDensity N c i) := by
  classical
  rw [perLetterLaw_eq_mixture h_meas c i]
  -- Each component: `gaussianReal μ N = volume.withDensity (gaussianPDF μ N)`.
  have h_comp : ∀ m : Fin M,
      gaussianReal (c.encoder m i) N
        = volume.withDensity (gaussianPDF (c.encoder m i) N) :=
    fun m => gaussianReal_of_var_ne_zero (c.encoder m i) hN
  -- Sum of withDensity = withDensity of sum (finset induction).
  have h_sum : ∀ s : Finset (Fin M),
      (∑ m ∈ s, gaussianReal (c.encoder m i) N)
        = volume.withDensity (∑ m ∈ s, gaussianPDF (c.encoder m i) N) := by
    intro s
    induction s using Finset.induction with
    | empty => simp [withDensity_zero]
    | insert m s hms ih =>
        rw [Finset.sum_insert hms, Finset.sum_insert hms, ih, h_comp m,
          withDensity_add_left (measurable_gaussianPDF _ _)]
  rw [h_sum Finset.univ]
  -- `M⁻¹ • volume.withDensity g = volume.withDensity (M⁻¹ • g)`.
  have hM_ne_top : (M : ℝ≥0∞)⁻¹ ≠ ∞ := by
    simp
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hM)
  rw [← withDensity_smul' _ _ hM_ne_top]
  -- `M⁻¹ • (∑ₘ gaussianPDF ...) = perLetterMixtureDensity N c i` (pointwise = M⁻¹ * ∑).
  congr 1
  funext y
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, perLetterMixtureDensity]

/-- The mixture density is bounded above by `(√(2πN))⁻¹` (each component is, and the
weights `1/M` sum to ≤ 1). -/
private lemma perLetterMixtureDensity_le_sup
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (y : ℝ) :
    perLetterMixtureDensity N c i y ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
  -- each Gaussian component pdf is `≤ ofReal (√(2πN))⁻¹`
  have h_comp : ∀ m : Fin M,
      gaussianPDF (c.encoder m i) N y ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
    intro m
    rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    -- `gaussianPDFReal μ N y ≤ (√(2πN))⁻¹` (exp factor ≤ 1)
    rw [gaussianPDFReal]
    have h_const_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ := by positivity
    have h_exp_le_one : Real.exp (-(y - c.encoder m i) ^ 2 / (2 * N)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      have : 0 ≤ (y - c.encoder m i) ^ 2 / (2 * (N : ℝ)) := by positivity
      linarith
    calc (Real.sqrt (2 * Real.pi * N))⁻¹ * Real.exp (-(y - c.encoder m i) ^ 2 / (2 * N))
        ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h_exp_le_one h_const_nonneg
      _ = (Real.sqrt (2 * Real.pi * N))⁻¹ := mul_one _
  unfold perLetterMixtureDensity
  -- `M⁻¹ * ∑ₘ (≤ B) ≤ M⁻¹ * (M • B) = M⁻¹ * (M * B) = B`
  calc (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, gaussianPDF (c.encoder m i) N y
      ≤ (M : ℝ≥0∞)⁻¹ * ∑ _m : Fin M, ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
        gcongr with m _
        exact h_comp m
    _ = (M : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hM))
          (ENNReal.natCast_ne_top M), one_mul]

/-- Lower bound on `log` of the mixture density (no Chebyshev needed — a single component
suffices): there are `c₀ c₁` with `|log (f y).toReal| ≤ c₀ + c₁ y²`. -/
private lemma perLetterMixtureDensity_log_abs_le
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (hN : N ≠ 0) :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ y : ℝ,
      |Real.log ((perLetterMixtureDensity N c i y).toReal)| ≤ c₀ + c₁ * y ^ 2 := by
  classical
  have hN_pos : (0 : ℝ) < N := lt_of_le_of_ne N.coe_nonneg (fun h => hN (by exact_mod_cast h.symm))
  set sup : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hsup_def
  have hsup_nonneg : 0 ≤ sup := by rw [hsup_def]; positivity
  -- a fixed representative message `m₀`
  set m₀ : Fin M := ⟨0, hM⟩ with hm₀_def
  set μ₀ : ℝ := c.encoder m₀ i with hμ₀_def
  -- The mixture density never exceeds `sup` (real form via `le_sup`).
  have h_up_real : ∀ y, (perLetterMixtureDensity N c i y).toReal ≤ sup := by
    intro y
    have h := perLetterMixtureDensity_le_sup N c i hM y
    rw [← hsup_def] at h
    calc (perLetterMixtureDensity N c i y).toReal
        ≤ (ENNReal.ofReal sup).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = sup := ENNReal.toReal_ofReal hsup_nonneg
  -- upper bound on `log f(y)`: `≤ max (log sup) 0`.
  have h_up : ∀ y, Real.log ((perLetterMixtureDensity N c i y).toReal) ≤ max (Real.log sup) 0 := by
    intro y
    rcases le_or_gt (perLetterMixtureDensity N c i y).toReal 0 with h0 | h0
    · have : (perLetterMixtureDensity N c i y).toReal = 0 := le_antisymm h0 ENNReal.toReal_nonneg
      rw [this, Real.log_zero]; exact le_max_right _ _
    · exact le_trans (Real.log_le_log h0 (h_up_real y)) (le_max_left _ _)
  -- single-component lower bound: `f(y).toReal ≥ M⁻¹ * gaussianPDFReal μ₀ N y`.
  have h_low_real : ∀ y, ((M : ℝ)⁻¹) * gaussianPDFReal μ₀ N y
      ≤ (perLetterMixtureDensity N c i y).toReal := by
    intro y
    -- `f y = M⁻¹ * ∑ₘ ofReal (gaussianPDFReal · ) ≥ M⁻¹ * ofReal (gaussianPDFReal μ₀)`
    have h_ne_top : perLetterMixtureDensity N c i y ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (perLetterMixtureDensity_le_sup N c i hM y)
    have h_ge : ENNReal.ofReal ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)
        ≤ perLetterMixtureDensity N c i y := by
      unfold perLetterMixtureDensity
      rw [ENNReal.ofReal_mul (by positivity)]
      have h_inv : ENNReal.ofReal ((M : ℝ)⁻¹) = (M : ℝ≥0∞)⁻¹ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hM)]
      rw [h_inv]
      gcongr
      -- `ofReal (gaussianPDFReal μ₀ N y) = gaussianPDF μ₀ N y ≤ ∑ₘ gaussianPDF · `
      rw [← gaussianPDF]
      exact Finset.single_le_sum (f := fun m => gaussianPDF (c.encoder m i) N y)
        (fun m _ => zero_le') (Finset.mem_univ m₀)
    calc ((M : ℝ)⁻¹) * gaussianPDFReal μ₀ N y
        = (ENNReal.ofReal ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)).toReal := by
          rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity) (gaussianPDFReal_nonneg μ₀ N y))]
      _ ≤ (perLetterMixtureDensity N c i y).toReal := ENNReal.toReal_mono h_ne_top h_ge
  -- lower bound on `log f(y)`: `-log f(y) ≤ (1/N) y² + b` from the single-component bound.
  -- `M⁻¹ · gaussianPDFReal μ₀ N y = M⁻¹ · sup · exp(-(y-μ₀)²/(2N))`, so
  -- `-log(M⁻¹ gaussianPDFReal) = log M - log sup + (y-μ₀)²/(2N) ≤ a y² + b`.
  have hgpos : ∀ y, 0 < gaussianPDFReal μ₀ N y := fun y => gaussianPDFReal_pos μ₀ N y hN
  set bLow : ℝ := Real.log M - Real.log sup + μ₀ ^ 2 / (N : ℝ) with hbLow_def
  refine ⟨max (Real.log sup) 0 + max bLow 0, 1 / (N : ℝ), by positivity, fun y => ?_⟩
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- `-(c₀ + c₁ y²) ≤ log f(y)`: use single-component lower bound + log algebra.
    have h_low := h_low_real y
    have hlow_pos : 0 < (M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y :=
      mul_pos (by positivity) (hgpos y)
    have h_log_low : Real.log ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)
        ≤ Real.log ((perLetterMixtureDensity N c i y).toReal) :=
      Real.log_le_log hlow_pos h_low
    -- compute `log (M⁻¹ gaussianPDFReal μ₀ N y)`
    have h_log_eq : Real.log ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)
        = -Real.log M + (Real.log sup - (y - μ₀) ^ 2 / (2 * N)) := by
      rw [Real.log_mul (by positivity) (hgpos y).ne', Real.log_inv, gaussianPDFReal,
        Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, ← hsup_def, neg_div]
      ring
    rw [h_log_eq] at h_log_low
    -- `(y-μ₀)²/(2N) ≤ (y²+μ₀²)/N` (cleared division)
    have h_quad : (y - μ₀) ^ 2 / (2 * (N : ℝ)) ≤ (y ^ 2 + μ₀ ^ 2) / (N : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hN_pos]
      nlinarith [sq_nonneg (y + μ₀), hN_pos]
    have h_split : (y ^ 2 + μ₀ ^ 2) / (N : ℝ) = y ^ 2 / (N : ℝ) + μ₀ ^ 2 / (N : ℝ) := by
      rw [add_div]
    have h_max1 : (0 : ℝ) ≤ max (Real.log sup) 0 := le_max_right _ _
    have h_max2 : bLow ≤ max bLow 0 := le_max_left _ _
    have h_c1 : 1 / (N : ℝ) * y ^ 2 = y ^ 2 / (N : ℝ) := by rw [div_mul_eq_mul_div, one_mul]
    rw [h_c1]
    -- unfold `bLow` so linarith sees the same atom `μ₀²/N`
    simp only [hbLow_def] at *
    linarith [h_log_low, h_quad, h_split, h_max1, h_max2]
  · -- `log f(y) ≤ c₀ + c₁ y²`: from the upper bound.
    have h := h_up y
    have h_sq : (0 : ℝ) ≤ 1 / (N : ℝ) * y ^ 2 := by positivity
    have h_max2 : (0 : ℝ) ≤ max bLow 0 := le_max_right _ _
    linarith [h, h_sq, h_max2]

/-- `y²` is integrable against the per-letter output law (finite mixture of Gaussians,
each with finite second moment). -/
private lemma perLetterLaw_sq_integrable
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (hN : N ≠ 0) :
    Integrable (fun y : ℝ => y ^ 2)
      ((converseJointInline h_meas c).map (fun ω => ω.2 i)) := by
  rw [perLetterLaw_eq_mixture h_meas c i]
  -- each component Gaussian has integrable `y²`
  have h_comp : ∀ m : Fin M, Integrable (fun y : ℝ => y ^ 2) (gaussianReal (c.encoder m i) N) := by
    intro m
    have h := (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 2).integrable_sq
    simpa using h
  have hM_ne_top : (M : ℝ≥0∞)⁻¹ ≠ ∞ := by
    simp only [ne_eq, ENNReal.inv_eq_top, Nat.cast_eq_zero]
    exact Nat.pos_iff_ne_zero.mp hM
  refine Integrable.smul_measure ?_ hM_ne_top
  exact integrable_finsetSum_measure.mpr (fun m _ => h_comp m)

/-- **Per-letter `Y_i` log-density integrability** (旧 `PerLetterIntegrabilityForConverse`).

For every coordinate `i`, the per-letter output law `Y_i` (here written as the pushforward
of the inlined joint along `ω ↦ ω.2 i`) has Lebesgue-integrable `negMulLog (rnDeriv · vol)`.
Consumer-side `unfold perLetterYLaw awgnConverseJoint` reduces `perLetterYLaw h_meas c i`
to `(converseJointInline h_meas c).map (fun ω => ω.2 i)` (defeq).

Genuine: the per-letter law is a finite Gaussian mixture; `negMulLog` of its `rnDeriv`
is dominated by a Gaussian-moment integrand (`perLetterMixtureDensity_log_abs_le` +
`perLetterLaw_sq_integrable`). The degenerate `M = 0` / `N = 0` cases give a singular
law (`rnDeriv = 0` a.e., `negMulLog 0 = 0`, constant, integrable).

Independently audited 2026-06-11 (wall-overturn confirmed genuine): signature is
byte-identical to the pre-closure `sorry` version (no hypothesis added, conclusion
unweakened — the former `wall:awgn-per-letter-integrability` over-claimed continuous
SMB / n-dim `differentialEntropy` for what is a 1-D finite-mixture log-density
domination); the `M = 0` / `N = 0` boundary is discharged by a genuine singular-law
argument (`rnDeriv =ᵐ 0`), not an exfalso/vacuity exploit; `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (sorryAx-free, this theorem + all 6 helpers).
@audit:ok -/
@[entry_point]
theorem awgnPerLetterIntegrability_holds
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) :
    ∀ i : Fin n,
      MeasureTheory.Integrable (fun y : ℝ =>
          Real.negMulLog
            (((converseJointInline h_meas c).map (fun ω => ω.2 i)).rnDeriv
                MeasureTheory.volume y).toReal)
        MeasureTheory.volume := by
  classical
  intro i
  set ν : Measure ℝ := (converseJointInline h_meas c).map (fun ω => ω.2 i) with hν_def
  -- Degenerate cases (`M = 0` or `N = 0`): `ν ⟂ volume`, so `rnDeriv =ᵐ 0` and the
  -- integrand is a.e. `negMulLog 0 = 0`, hence integrable.
  by_cases hMN : 0 < M ∧ N ≠ 0
  · obtain ⟨hM, hN⟩ := hMN
    haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM⟩
    -- `ν` is a probability measure (pushforward of the probability mixture)
    haveI hν_prob : IsProbabilityMeasure ν := by
      rw [hν_def]
      exact Measure.isProbabilityMeasure_map ((measurable_pi_apply i).comp measurable_snd).aemeasurable
    -- main case: `ν = volume.withDensity f`, `f := perLetterMixtureDensity N c i`.
    set f : ℝ → ℝ≥0∞ := perLetterMixtureDensity N c i with hf_def
    have hf_meas : Measurable f := perLetterMixtureDensity_measurable N c i
    have hν_wd : ν = volume.withDensity f := by
      rw [hν_def, hf_def]; exact perLetterLaw_withDensity h_meas c i hM hN
    -- `ν.rnDeriv volume =ᵐ[volume] f`
    have h_rn_ae : ν.rnDeriv volume =ᵐ[volume] f := by
      rw [hν_wd]; exact Measure.rnDeriv_withDensity volume hf_meas
    -- `f y < ∞` a.e. (bounded above)
    have hf_lt_top : ∀ᵐ y ∂(volume : Measure ℝ), f y < ∞ :=
      Filter.Eventually.of_forall (fun y =>
        lt_of_le_of_lt (perLetterMixtureDensity_le_sup N c i hM y) ENNReal.ofReal_lt_top)
    -- quadratic abs bound on `log f`
    obtain ⟨c₀, c₁, hc₁, h_abs⟩ := perLetterMixtureDensity_log_abs_le N c i hM hN
    -- `c₀ + c₁ y²` integrable against ν, transport to `(f y).toReal • (c₀+c₁y²)` on volume
    have h_dom_ν : Integrable (fun y : ℝ => c₀ + c₁ * y ^ 2) ν :=
      (integrable_const c₀).add ((perLetterLaw_sq_integrable h_meas c i hM hN).const_mul c₁)
    have h_dom_vol : Integrable (fun y : ℝ => (f y).toReal • (c₀ + c₁ * y ^ 2)) volume :=
      (integrable_withDensity_iff_integrable_smul' hf_meas hf_lt_top).mp
        (by rw [← hν_wd]; exact h_dom_ν)
    -- dominate `negMulLog (rnDeriv)` by `(f y).toReal · (c₀ + c₁ y²)`
    refine Integrable.mono' h_dom_vol ?_ ?_
    · have h_rn_meas : Measurable (fun y => (ν.rnDeriv volume y).toReal) :=
        (Measure.measurable_rnDeriv ν volume).ennreal_toReal
      exact (Real.continuous_negMulLog.measurable.comp h_rn_meas).aestronglyMeasurable
    · filter_upwards [h_rn_ae] with y hy
      rw [hy, smul_eq_mul, Real.norm_eq_abs]
      set t : ℝ := (f y).toReal with ht_def
      have ht_nonneg : 0 ≤ t := ENNReal.toReal_nonneg
      rw [Real.negMulLog_def, abs_mul, abs_neg, abs_of_nonneg ht_nonneg]
      exact mul_le_mul_of_nonneg_left (h_abs y) ht_nonneg
  · -- degenerate: `ν ⟂ volume`, so `rnDeriv =ᵐ 0`; integrand a.e. `0`.
    have h_rn_zero : ν.rnDeriv volume =ᵐ[volume] 0 := by
      rcases not_and_or.mp hMN with hM0 | hN0
      · -- `M = 0`: `ν = 0` measure
        have hM_eq : M = 0 := Nat.le_zero.mp (Nat.not_lt.mp hM0)
        have hν_zero : ν = 0 := by
          rw [hν_def, perLetterLaw_eq_mixture h_meas c i]
          subst hM_eq
          simp
        rw [hν_zero]; exact Measure.rnDeriv_zero volume
      · -- `N = 0`: `ν` is a finite sum of Diracs, mutually singular with volume
        have hN_eq : N = 0 := not_not.mp hN0
        have hν_dirac : ν = ((M : ℝ≥0∞))⁻¹ • ∑ m : Fin M, Measure.dirac (c.encoder m i) := by
          rw [hν_def, perLetterLaw_eq_mixture h_meas c i]
          subst hN_eq
          simp only [gaussianReal_zero_var]
        have h_sum_sing : ∀ s : Finset (Fin M),
            (∑ m ∈ s, Measure.dirac (c.encoder m i)) ⟂ₘ (volume : Measure ℝ) := by
          intro s
          induction s using Finset.induction with
          | empty => simp [Measure.MutuallySingular.zero_left]
          | insert m s hms ih =>
              rw [Finset.sum_insert hms]
              exact (mutuallySingular_dirac (c.encoder m i) volume).add_left ih
        have h_sing : ν ⟂ₘ volume := by
          rw [hν_dirac]
          exact (h_sum_sing Finset.univ).smul _
        exact h_sing.rnDeriv_ae_eq_zero
    -- integrand a.e. equals `negMulLog 0 = 0`
    refine (integrable_zero ℝ ℝ volume).congr ?_
    filter_upwards [h_rn_zero] with y hy
    rw [hy]; simp

/-! ### Wall 5 — `awgn-continuous-mi-chain-rule` (genuine closure)

**Genuine closure (2026-06-12, false-wall overturn).** The wall verdict over-claimed: the
`I(X^n;Y^n) ≤ ∑ᵢ I(X_i;Y_i)` chain rule is the textbook proof
`I(W;Y^n) = h(Y^n) − n·h(noise) ≤ ∑ h(Y_i) − n·h(noise) = ∑ I(X_i;Y_i)`, combined with the
**deterministic data-processing inequality** `I(X^n;Y^n) ≤ I(W;Y^n)` (since `X^n = encoder ∘ W`
is a measurable post-processing of `W`, via `mutualInfo_le_of_postprocess` — no Markov-chain
machinery needed). The `I(W;Y^n)` decomposition uses the **discrete-input** block kernel
`blockKernelInline : Channel (Fin M) (Fin n → ℝ)` whose measurability is *free*
(`measurable_of_countable`, input `Fin M`), so the parallel-Gaussian kernel-measurability
gap (X-input route) is sidestepped. Pieces:

* the generic n-D continuous-channel MI decomposition
  `ChannelCoding.mutualInfoOfChannel_toReal_eq_log_density_sub` (the gateway atom, output
  type `β := Fin n → ℝ`, reference `volume`; genuine, no wall), giving
  `I(W;Y^n).toReal = h(Y^n) − n·h(noise)`;
* the n-D subadditivity `Shannon.jointDifferentialEntropyPi_le_sum` (genuine);
* the per-letter 1-D decomposition `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (genuine),
  giving `I(X_i;Y_i).toReal = h(Y_i) − h(noise)`.

The block regularity machinery mirrors the per-letter Wall-4 closure above and the
`AWGNConverseDischarge.lean` block infrastructure. -/

/-- Discrete-input block kernel `K m := pi (gaussianReal (encoder m i) N)` (`Fin M → Y^n`).
Measurability is free (`measurable_of_countable`, input `Fin M`). -/
private noncomputable def blockKernelInline
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) :
    ChannelCoding.Channel (Fin M) (Fin n → ℝ) :=
  { toFun := fun m => Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)
    measurable' := measurable_of_countable _ }

private instance blockKernelInline_isMarkov
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) :
    ProbabilityTheory.IsMarkovKernel (blockKernelInline N c) :=
  ⟨fun m => by
    show IsProbabilityMeasure (Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N))
    infer_instance⟩

/-- Uniform message law `msgLawInline := (M⁻¹ : ℝ≥0∞) • count` on `Fin M`. -/
private noncomputable def msgLawInline (M : ℕ) : Measure (Fin M) :=
  (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count

private instance msgLawInline_isProb (M : ℕ) [NeZero M] :
    IsProbabilityMeasure (msgLawInline M) := by
  refine ⟨?_⟩
  rw [msgLawInline, Measure.smul_apply, smul_eq_mul, Fintype.card_fin]
  have h_count : (Measure.count : Measure (Fin M)) Set.univ = (M : ℝ≥0∞) := by
    rw [Measure.count_apply_finite _ (Set.finite_univ)]
    simp [Fintype.card_fin]
  rw [h_count, ENNReal.inv_mul_cancel (by exact_mod_cast (NeZero.ne M))
    (ENNReal.natCast_ne_top M)]

/-- Block output law `Y^n` = `(converseJointInline).map snd` (= mixture of product
Gaussians). This is `outputDistribution msgLawInline blockKernelInline`. -/
private noncomputable def blockYLawInline
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) : Measure (Fin n → ℝ) :=
  (converseJointInline h_meas c).map Prod.snd

/-- Real-valued block mixture density `M⁻¹ ∑ₘ ∏ᵢ gaussianPDFReal (encoder m i) N (yᵢ)`. -/
private noncomputable def blockRealDensityInline
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (y : Fin n → ℝ) : ℝ :=
  (1 / (M : ℝ)) * ∑ m : Fin M, ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)

/-- `blockYLawInline = M⁻¹ • ∑ₘ pi (gaussianReal (encoder m i) N)` (closed mixture form). -/
private lemma blockYLawInline_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLawInline h_meas c
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
          ∑ m : Fin M, Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) := by
  classical
  unfold blockYLawInline converseJointInline
  have h_meas_snd :
      Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := measurable_snd
  rw [Measure.map_smul,
    Measure.map_finset_sum (s := Finset.univ)
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
      h_meas_snd.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [Measure.map_snd_prod, measure_univ, one_smul]
  refine congrArg (Measure.pi) ?_
  funext i
  rw [awgnChannel_apply]

private lemma blockRealDensityInline_pos
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (y : Fin n → ℝ) :
    0 < blockRealDensityInline N c y := by
  classical
  obtain ⟨m₀⟩ : Nonempty (Fin M) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩⟩
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  unfold blockRealDensityInline
  refine mul_pos (by positivity) ?_
  refine Finset.sum_pos (fun m _ => Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ hN)) ?_
  exact ⟨m₀, Finset.mem_univ m₀⟩

private lemma blockRealDensityInline_measurable
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) :
    Measurable (blockRealDensityInline N c) := by
  unfold blockRealDensityInline
  refine measurable_const.mul ?_
  refine Finset.measurable_sum _ (fun m _ => ?_)
  exact Finset.measurable_prod _ (fun i _ =>
    (measurable_gaussianPDFReal (c.encoder m i) N).comp (measurable_pi_apply i))

private lemma blockComponentInline_withDensity
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0)
    {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
  have h_each : ∀ i, gaussianReal (c.encoder m i) N
      = (MeasureTheory.volume : Measure ℝ).withDensity (gaussianPDF (c.encoder m i) N) :=
    fun i => gaussianReal_of_var_ne_zero (c.encoder m i) hN
  haveI : ∀ i, SigmaFinite ((MeasureTheory.volume : Measure ℝ).withDensity
      (gaussianPDF (c.encoder m i) N)) := by
    intro i; rw [← h_each i]; infer_instance
  rw [show (fun i : Fin n => gaussianReal (c.encoder m i) N)
        = (fun i => (MeasureTheory.volume : Measure ℝ).withDensity
            (gaussianPDF (c.encoder m i) N)) from funext h_each,
    InformationTheory.Shannon.pi_withDensity_fin (fun _ => (MeasureTheory.volume : Measure ℝ))
      (fun i => measurable_gaussianPDF (c.encoder m i) N), ← volume_pi]

private lemma blockYLawInline_withDensity_real
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLawInline h_meas c
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y => ENNReal.ofReal (blockRealDensityInline N c y)) := by
  classical
  rw [blockYLawInline_eq_mixture h_meas c]
  have h_comp := fun m : Fin M => blockComponentInline_withDensity hN c m
  have h_sum : ∀ s : Finset (Fin M),
      (∑ m ∈ s, Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N))
        = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
            (fun y => ∑ m ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert m s hms ih =>
        have h_density_eq :
            (fun y : Fin n → ℝ => ∑ m' ∈ insert m s, ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i))
              = (fun y : Fin n → ℝ => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
                + (fun y : Fin n → ℝ => ∑ m' ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i)) := by
          funext y; simp only [Pi.add_apply]; rw [Finset.sum_insert hms]
        rw [Finset.sum_insert hms, ih, h_comp m, h_density_eq]
        rw [withDensity_add_left
            (μ := (MeasureTheory.volume : Measure (Fin n → ℝ)))
            (f := fun y : Fin n → ℝ => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
            (Finset.measurable_prod _ (fun i _ =>
              (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i)))
            (fun y : Fin n → ℝ => ∑ m' ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i))]
  rw [h_sum Finset.univ]
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  rw [← withDensity_smul' _ _ hM_inv_ne_top]
  congr 1
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, blockRealDensityInline, Fintype.card_fin]
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  · rw [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)),
      ENNReal.ofReal_natCast]
  · rw [ENNReal.ofReal_sum_of_nonneg
          (fun m _ => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _))]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [gaussianPDF]

private lemma blockYLawInline_ac_volume
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLawInline h_meas c ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
  rw [blockYLawInline_withDensity_real hN h_meas c]
  exact MeasureTheory.withDensity_absolutelyContinuous _ _

private lemma volume_ac_blockYLawInline
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (MeasureTheory.volume : Measure (Fin n → ℝ)) ≪ blockYLawInline h_meas c := by
  rw [blockYLawInline_withDensity_real hN h_meas c]
  refine withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp (blockRealDensityInline_measurable c)).aemeasurable ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact blockRealDensityInline_pos hN c y

private instance blockYLawInline_isProb
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsProbabilityMeasure (blockYLawInline h_meas c) := by
  rw [blockYLawInline]
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

/-- The block component `pi (gaussianReal (encoder m i) N) ≪ blockYLawInline`
(`νₘ ≪ vol ≪ blockYLaw`). -/
private lemma blockComponentInline_ac_blockYLaw
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) ≪ blockYLawInline h_meas c := by
  have h1 : Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)
      ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  exact h1.trans (volume_ac_blockYLawInline hN h_meas c)

/-- Per-component lower bound:
`blockRealDensityInline y ≥ M⁻¹ · ∏ᵢ gaussianPDFReal (encoder m i) N (yᵢ)`. -/
private lemma blockRealDensityInline_ge_component
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) (y : Fin n → ℝ) :
    (1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ blockRealDensityInline N c y := by
  unfold blockRealDensityInline
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.single_le_sum
    (f := fun m => ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i))
    (fun m _ => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _))
    (Finset.mem_univ m)

/-- Sup upper bound: `blockRealDensityInline y ≤ ∏ᵢ (√(2πN))⁻¹`. -/
private lemma blockRealDensityInline_le_sup
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (y : Fin n → ℝ) :
    blockRealDensityInline N c y ≤ ∏ _i : Fin n, (Real.sqrt (2 * Real.pi * N))⁻¹ := by
  classical
  unfold blockRealDensityInline
  set Bpeak : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hBpeak
  have hBpeak_nonneg : (0 : ℝ) ≤ Bpeak := by rw [hBpeak]; positivity
  have h_comp_le : ∀ (a x : ℝ), gaussianPDFReal a N x ≤ Bpeak := by
    intro a x
    rw [gaussianPDFReal, hBpeak]
    have h_exp_le_one : Real.exp (-(x - a) ^ 2 / (2 * N)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      have : 0 ≤ (x - a) ^ 2 / (2 * (N : ℝ)) := by positivity
      linarith
    calc (Real.sqrt (2 * Real.pi * N))⁻¹ * Real.exp (-(x - a) ^ 2 / (2 * N))
        ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h_exp_le_one (by positivity)
      _ = (Real.sqrt (2 * Real.pi * N))⁻¹ := mul_one _
  have h_prod_le : ∀ m : Fin M,
      (∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)) ≤ ∏ _i : Fin n, Bpeak := by
    intro m
    refine Finset.prod_le_prod (fun i _ => gaussianPDFReal_nonneg _ _ _) (fun i _ => ?_)
    exact h_comp_le (c.encoder m i) (y i)
  calc (1 / (M : ℝ)) * ∑ m : Fin M, ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ (1 / (M : ℝ)) * ∑ _m : Fin M, ∏ _i : Fin n, Bpeak := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun m _ => h_prod_le m)
    _ = (1 / (M : ℝ)) * ((M : ℝ) * ∏ _i : Fin n, Bpeak) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∏ _i : Fin n, Bpeak := by
        have : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
        field_simp

/-- Per-component output log-density integrability (n-dim) against the m-th product-Gaussian
fibre `pi (gaussianReal (encoder m i) N)`. Mirror of
`AWGNConverseDischarge.integrable_log_blockYLaw_on_component`. -/
private lemma integrable_log_blockYLawInline_on_component
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Integrable
      (fun y => Real.log ((blockYLawInline h_meas c).rnDeriv MeasureTheory.volume y).toReal)
      (Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)) := by
  classical
  set q := blockYLawInline h_meas c with hq_def
  set νm := Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) with hνm_def
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i => inferInstance
  haveI hνm_prob : IsProbabilityMeasure νm := by rw [hνm_def]; infer_instance
  have hq_wd : q = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
      (fun y => ENNReal.ofReal (blockRealDensityInline N c y)) := by
    rw [hq_def]; exact blockYLawInline_withDensity_real hN h_meas c
  have hDR_meas : Measurable (fun y => ENNReal.ofReal (blockRealDensityInline N c y)) :=
    ENNReal.measurable_ofReal.comp (blockRealDensityInline_measurable c)
  have hνm_ac : νm ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [hνm_def, blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_rn_vol : q.rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[(MeasureTheory.volume : Measure (Fin n → ℝ))]
      (fun y => ENNReal.ofReal (blockRealDensityInline N c y)) := by
    rw [hq_wd]; exact Measure.rnDeriv_withDensity _ hDR_meas
  have h_rn_νm : q.rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[νm] (fun y => ENNReal.ofReal (blockRealDensityInline N c y)) :=
    hνm_ac.ae_le h_rn_vol
  have h_log_ae : (fun y => Real.log (q.rnDeriv MeasureTheory.volume y).toReal)
      =ᵐ[νm] (fun y => Real.log (blockRealDensityInline N c y)) := by
    filter_upwards [h_rn_νm] with y hy
    rw [hy, ENNReal.toReal_ofReal (blockRealDensityInline_pos hN c y).le]
  refine (Integrable.congr ?_ h_log_ae.symm)
  set Bpeak : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hBpeak
  have hBpeak_pos : 0 < Bpeak := by rw [hBpeak]; positivity
  have hD_le : ∀ y, blockRealDensityInline N c y ≤ ∏ _i : Fin n, Bpeak :=
    blockRealDensityInline_le_sup c
  have hD_ge : ∀ y, (1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ blockRealDensityInline N c y := fun y => blockRealDensityInline_ge_component c m y
  set c₀ : ℝ := -(1 / 2) * Real.log (2 * Real.pi * N) with hc₀
  set c₁ : ℝ := -(1 / (2 * (N : ℝ))) with hc₁
  set Aconst : ℝ := |Real.log (∏ _i : Fin n, Bpeak)|
      + |Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀| with hAconst
  set Bcoef : ℝ := |c₁| with hBcoef
  have h_dom : Integrable
      (fun y : Fin n → ℝ => Aconst + Bcoef * ∑ i : Fin n, (y i - c.encoder m i) ^ 2) νm := by
    refine (integrable_const Aconst).add (Integrable.const_mul ?_ Bcoef)
    rw [hνm_def]
    refine integrable_finsetSum _ (fun i _ => ?_)
    have h_1d : Integrable (fun y : ℝ => (y - c.encoder m i) ^ 2)
        (gaussianReal (c.encoder m i) N) := by
      have h_id : Integrable (fun y : ℝ => y) (gaussianReal (c.encoder m i) N) := by
        simpa using (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 1).integrable (by norm_num)
      have h_sq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal (c.encoder m i) N) :=
        (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 2).integrable_sq
      have hrw : (fun y : ℝ => (y - c.encoder m i) ^ 2)
          = fun y => y ^ 2 - 2 * (c.encoder m i) * y + (c.encoder m i) ^ 2 := by funext y; ring
      rw [hrw]
      exact ((h_sq.sub (h_id.const_mul (2 * c.encoder m i))).add
        (integrable_const ((c.encoder m i) ^ 2)))
    exact integrable_comp_eval (μ := fun i : Fin n => gaussianReal (c.encoder m i) N)
      (i := i) h_1d
  refine Integrable.mono' h_dom ?_ ?_
  · exact (Real.measurable_log.comp (blockRealDensityInline_measurable c)).aestronglyMeasurable
  · filter_upwards with y
    have hDy_pos : 0 < blockRealDensityInline N c y := blockRealDensityInline_pos hN c y
    set S : ℝ := ∑ i : Fin n, (y i - c.encoder m i) ^ 2 with hS
    have hS_nonneg : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hc₁_nonpos : c₁ ≤ 0 := by rw [hc₁]; simp only [neg_nonpos]; positivity
    have h_upper : Real.log (blockRealDensityInline N c y) ≤ Real.log (∏ _i : Fin n, Bpeak) :=
      Real.log_le_log hDy_pos (hD_le y)
    have h_lower : Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S
        ≤ Real.log (blockRealDensityInline N c y) := by
      have hMinv_pos : (0 : ℝ) < 1 / (M : ℝ) := by positivity
      have hprod_pos : (0 : ℝ) < ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i) :=
        Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ hN)
      have h_log_prod : Real.log ((1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i))
          = Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S := by
        rw [Real.log_mul hMinv_pos.ne' hprod_pos.ne', Real.log_prod (fun i _ =>
          (gaussianPDFReal_pos (c.encoder m i) N (y i) hN).ne')]
        have h_each : ∀ i : Fin n, Real.log (gaussianPDFReal (c.encoder m i) N (y i))
            = c₀ + c₁ * (y i - c.encoder m i) ^ 2 := by
          intro i
          rw [InformationTheory.Shannon.log_gaussianPDFReal_eq (c.encoder m i) hN (y i), hc₀, hc₁]
          ring
        rw [Finset.sum_congr rfl (fun i _ => h_each i), hS, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
        ring
      calc Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S
          = Real.log ((1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)) :=
            h_log_prod.symm
        _ ≤ Real.log (blockRealDensityInline N c y) :=
            Real.log_le_log (mul_pos hMinv_pos hprod_pos) (hD_ge y)
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, ?_⟩
    · have hc₁S : c₁ * S = -(Bcoef * S) := by rw [hBcoef, abs_of_nonpos hc₁_nonpos]; ring
      have hlb : -(Aconst + Bcoef * S)
          ≤ Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S := by
        rw [hAconst, hc₁S]
        have h1 := neg_abs_le (Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀)
        have h2 := abs_nonneg (Real.log (∏ _i : Fin n, Bpeak))
        linarith
      exact le_trans hlb h_lower
    · have hub : Real.log (∏ _i : Fin n, Bpeak) ≤ Aconst + Bcoef * S := by
        rw [hAconst]
        have h1 := le_abs_self (Real.log (∏ _i : Fin n, Bpeak))
        have h2 := abs_nonneg (Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀)
        have h3 : 0 ≤ Bcoef * S := mul_nonneg (abs_nonneg _) hS_nonneg
        linarith
      exact le_trans h_upper hub

/-- The proxy density `g z := ∏ᵢ gaussianPDF (encoder z.1 i) N (z.2 i)`, jointly measurable. -/
private noncomputable def blockProxy
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P)
    (z : (Fin M) × (Fin n → ℝ)) : ℝ≥0∞ :=
  ∏ i : Fin n, gaussianPDF (c.encoder z.1 i) N (z.2 i)

private lemma blockProxy_measurable
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) :
    Measurable (blockProxy N c) := by
  -- `Fin M` (input) is countable: measurability reduces to measurability in `y` for each `m`.
  refine measurable_from_prod_countable_right (fun m => ?_)
  show Measurable (fun y : Fin n → ℝ => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
  exact Finset.measurable_prod _ (fun i _ =>
    (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i))

/-- Per-fibre a.e. agreement: `(blockKernelInline m).rnDeriv volume =ᵐ blockProxy (m, ·)`. -/
private lemma blockProxy_ae
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    (fun y => ((blockKernelInline N c) m).rnDeriv MeasureTheory.volume y)
      =ᵐ[(blockKernelInline N c) m] fun y => blockProxy N c (m, y) := by
  -- `blockKernelInline m = vol.withDensity (∏ᵢ gaussianPDF (encoder m i)(·i))`, so its
  -- rnDeriv =ᵐ[vol] that density; transport to `=ᵐ[blockKernelInline m]` since fibre ≪ vol.
  have hfibre_eq : (blockKernelInline N c) m
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    show Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) = _
    exact blockComponentInline_withDensity hN c m
  have h_dens_meas : Measurable (fun y : Fin n → ℝ =>
      ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) :=
    Finset.measurable_prod _ (fun i _ =>
      (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i))
  have h_fibre_ac : (blockKernelInline N c) m ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [hfibre_eq]; exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_rn_vol : ((blockKernelInline N c) m).rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[(MeasureTheory.volume : Measure (Fin n → ℝ))]
      (fun y => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    conv_lhs => rw [hfibre_eq]
    exact Measure.rnDeriv_withDensity _ h_dens_meas
  filter_upwards [h_fibre_ac.ae_le h_rn_vol] with y hy
  simpa [blockProxy] using hy

/-- Fibre log-density integral identity: the proxy log-density integrates the same as the
rnDeriv log-density against the m-th fibre (used to feed `h_fibre_self`). -/
private lemma fibre_log_proxy_integral
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    ∫ y, Real.log (blockProxy N c (m, y)).toReal ∂((blockKernelInline N c) m)
      = ∫ y, Real.log
          (((blockKernelInline N c) m).rnDeriv MeasureTheory.volume y).toReal
          ∂((blockKernelInline N c) m) := by
  refine integral_congr_ae ?_
  filter_upwards [blockProxy_ae hN c m] with y hy
  rw [hy]

/-- Per-Gaussian log-density integrability (mirror of
`ParallelGaussian.gaussianReal_logRnDeriv_integrable`, inaccessible downstream). -/
private lemma gaussianReal_logRnDeriv_integrable_inline (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun y => Real.log ((gaussianReal m v).rnDeriv volume y).toReal)
      (gaussianReal m v) := by
  have h_memLp : MemLp (fun y : ℝ => y - m) 2 (gaussianReal m v) :=
    (memLp_id_gaussianReal 2).sub (memLp_const m)
  have h_sq_int : Integrable (fun y => (y - m) ^ 2) (gaussianReal m v) := h_memLp.integrable_sq
  have h_rn : ∀ᵐ y ∂(gaussianReal m v),
      Real.log ((gaussianReal m v).rnDeriv volume y).toReal
        = -(1/2) * Real.log (2 * Real.pi * v) - (y - m) ^ 2 / (2 * v) := by
    have h_ac : gaussianReal m v ≪ volume := gaussianReal_absolutelyContinuous m hv
    filter_upwards [h_ac.ae_le (rnDeriv_gaussianReal m v)] with y hy
    rw [hy, toReal_gaussianPDF, log_gaussianPDFReal_eq m hv y]
  have h_affine_int : Integrable
      (fun y => -(1/2) * Real.log (2 * Real.pi * v) - (y - m) ^ 2 / (2 * v))
      (gaussianReal m v) :=
    (integrable_const _).sub (h_sq_int.div_const (2 * v))
  refine h_affine_int.congr ?_
  filter_upwards [h_rn] with y hy
  exact hy.symm

/-- Per-fibre log-density integrability: `log (rnDeriv (blockKernelInline m) vol)` is
integrable against the m-th product-Gaussian fibre `blockKernelInline m`. -/
private lemma integrable_log_fibre_rnDeriv
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    Integrable
      (fun y => Real.log (((blockKernelInline N c) m).rnDeriv MeasureTheory.volume y).toReal)
      ((blockKernelInline N c) m) := by
  classical
  set νp := Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) with hνp
  have hfibre : (blockKernelInline N c) m = νp := rfl
  rw [hfibre]
  haveI : IsProbabilityMeasure νp := by rw [hνp]; infer_instance
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i => inferInstance
  -- `log (rnDeriv νp vol) =ᵐ[νp] ∑ᵢ log gaussianPDFReal (encoder m i) (·i)`
  set a : Fin n → ℝ → ℝ≥0∞ := fun i => (gaussianReal (c.encoder m i) N).rnDeriv volume with ha
  have ha_meas : ∀ i, Measurable (a i) := fun i => Measure.measurable_rnDeriv _ _
  have hac : ∀ i, gaussianReal (c.encoder m i) N ≪ (volume : Measure ℝ) :=
    fun i => gaussianReal_absolutelyContinuous (c.encoder m i) hN
  have hνp_ac : νp ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hνp, blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_rn_pi : (νp.rnDeriv volume) =ᵐ[νp] fun z => ∏ i, a i (z i) := by
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (a i) = gaussianReal (c.encoder m i) N :=
      fun i => Measure.withDensity_rnDeriv_eq _ volume (hac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (a i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_wd : νp = (volume : Measure (Fin n → ℝ)).withDensity (fun z => ∏ i, a i (z i)) := by
      rw [hνp, ← (funext h_eq : (fun i => (volume : Measure ℝ).withDensity (a i))
          = fun i => gaussianReal (c.encoder m i) N)]
      rw [InformationTheory.Shannon.pi_withDensity_fin (fun _ : Fin n => (volume : Measure ℝ)) ha_meas,
        volume_pi]
    have h_prod_meas : Measurable (fun z : Fin n → ℝ => ∏ i, a i (z i)) :=
      Finset.measurable_prod _ (fun i _ => (ha_meas i).comp (measurable_pi_apply i))
    have h_rn_vol : (νp.rnDeriv volume) =ᵐ[volume] fun z => ∏ i, a i (z i) := by
      conv_lhs => rw [h_pi_wd]
      exact Measure.rnDeriv_withDensity volume h_prod_meas
    exact hνp_ac.ae_le h_rn_vol
  have h_pos : ∀ i, ∀ᵐ z ∂νp, 0 < a i (z i) := by
    intro i
    have h1d : ∀ᵐ y ∂(gaussianReal (c.encoder m i) N), 0 < a i y := Measure.rnDeriv_pos (hac i)
    exact (Measure.quasiMeasurePreserving_eval (μ := fun i => gaussianReal (c.encoder m i) N) i).ae h1d
  have h_lt : ∀ i, ∀ᵐ z ∂νp, a i (z i) < ∞ := by
    intro i
    have h1d : ∀ᵐ y ∂(gaussianReal (c.encoder m i) N), a i y < ∞ :=
      (hac i).ae_le (Measure.rnDeriv_lt_top _ volume)
    exact (Measure.quasiMeasurePreserving_eval (μ := fun i => gaussianReal (c.encoder m i) N) i).ae h1d
  have h_log_split : (fun z => Real.log ((νp.rnDeriv volume z).toReal))
      =ᵐ[νp] fun z => ∑ i, Real.log ((a i (z i)).toReal) := by
    filter_upwards [h_rn_pi, eventually_countable_forall.mpr h_pos,
      eventually_countable_forall.mpr h_lt] with z hz hpos hlt
    rw [hz, ENNReal.toReal_prod, Real.log_prod]
    intro i _
    exact (ENNReal.toReal_pos (hpos i).ne' (hlt i).ne).ne'
  refine (Integrable.congr ?_ h_log_split.symm)
  refine integrable_finsetSum _ (fun i _ => ?_)
  -- each `log (a i (z i))` integrable against νp = pi gaussian via `integrable_comp_eval`
  have h_1d : Integrable (fun y => Real.log ((a i y).toReal)) (gaussianReal (c.encoder m i) N) :=
    gaussianReal_logRnDeriv_integrable_inline (c.encoder m i) hN
  rw [hνp]
  exact integrable_comp_eval (μ := fun i : Fin n => gaussianReal (c.encoder m i) N) (i := i) h_1d

/-- Product entropy additivity (mirror of `ParallelGaussian.jointDifferentialEntropyPi_pi_eq_sum`,
inaccessible downstream): `h(∏ᵢ νᵢ) = ∑ᵢ h(νᵢ)` for component-`≪ volume`, log-density-integrable
factors. -/
private lemma jointDifferentialEntropyPi_pi_eq_sum_inline {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (h_ac : ∀ i, μ i ≪ (volume : Measure ℝ))
    (h_int : ∀ i, Integrable (fun y => Real.log ((μ i).rnDeriv volume y).toReal) (μ i)) :
    InformationTheory.Shannon.jointDifferentialEntropyPi (Measure.pi μ)
      = ∑ i, InformationTheory.Shannon.differentialEntropy (μ i) := by
  classical
  set Pm := Measure.pi μ with hP
  set a : Fin n → ℝ → ℝ≥0∞ := fun i => (μ i).rnDeriv volume with ha_def
  have ha_meas : ∀ i, Measurable (a i) := fun i => Measure.measurable_rnDeriv (μ i) volume
  have hP_ac : Pm ≪ (volume : Measure (Fin n → ℝ)) := by
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (a i) = μ i :=
      fun i => Measure.withDensity_rnDeriv_eq (μ i) volume (h_ac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (a i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_eq : Measure.pi μ
        = (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity
            (fun z => ∏ i, a i (z i)) := by
      rw [← (funext h_eq : (fun i => (volume : Measure ℝ).withDensity (a i)) = μ)]
      exact InformationTheory.Shannon.pi_withDensity_fin (fun _ : Fin n => (volume : Measure ℝ)) ha_meas
    rw [hP, h_pi_eq, volume_pi]
    exact withDensity_absolutelyContinuous _ _
  have h_step1 : InformationTheory.Shannon.jointDifferentialEntropyPi Pm
      = -∫ z, Real.log ((Pm.rnDeriv volume z).toReal) ∂Pm := by
    rw [InformationTheory.Shannon.integral_log_rnDeriv_self_eq_neg hP_ac, neg_neg]; rfl
  have h_rn_pi : (Pm.rnDeriv volume) =ᵐ[Pm] fun z => ∏ i, a i (z i) := by
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (a i) = μ i :=
      fun i => Measure.withDensity_rnDeriv_eq (μ i) volume (h_ac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (a i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_wd : Pm = (volume : Measure (Fin n → ℝ)).withDensity (fun z => ∏ i, a i (z i)) := by
      rw [hP, ← (funext h_eq : (fun i => (volume : Measure ℝ).withDensity (a i)) = μ)]
      rw [InformationTheory.Shannon.pi_withDensity_fin (fun _ : Fin n => (volume : Measure ℝ)) ha_meas,
        volume_pi]
    have h_prod_meas : Measurable (fun z : Fin n → ℝ => ∏ i, a i (z i)) :=
      Finset.measurable_prod _ (fun i _ => (ha_meas i).comp (measurable_pi_apply i))
    have h_rn_vol : (Pm.rnDeriv volume) =ᵐ[volume] fun z => ∏ i, a i (z i) := by
      conv_lhs => rw [h_pi_wd]
      exact Measure.rnDeriv_withDensity volume h_prod_meas
    exact hP_ac.ae_le h_rn_vol
  have h_pos : ∀ i, ∀ᵐ z ∂Pm, 0 < a i (z i) := by
    intro i
    have h1d : ∀ᵐ y ∂(μ i), 0 < a i y := Measure.rnDeriv_pos (h_ac i)
    exact (Measure.quasiMeasurePreserving_eval (μ := μ) i).ae h1d
  have h_lt : ∀ i, ∀ᵐ z ∂Pm, a i (z i) < ∞ := by
    intro i
    have h1d : ∀ᵐ y ∂(μ i), a i y < ∞ := (h_ac i).ae_le (Measure.rnDeriv_lt_top (μ i) volume)
    exact (Measure.quasiMeasurePreserving_eval (μ := μ) i).ae h1d
  have h_log_split : (fun z => Real.log ((Pm.rnDeriv volume z).toReal))
      =ᵐ[Pm] fun z => ∑ i, Real.log ((a i (z i)).toReal) := by
    filter_upwards [h_rn_pi, eventually_countable_forall.mpr h_pos,
      eventually_countable_forall.mpr h_lt] with z hz hpos hlt
    rw [hz, ENNReal.toReal_prod, Real.log_prod]
    intro i _
    have : (0 : ℝ) < (a i (z i)).toReal := ENNReal.toReal_pos (hpos i).ne' (hlt i).ne
    exact this.ne'
  have h_int_P : ∀ i, Integrable (fun z => Real.log ((a i (z i)).toReal)) Pm := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) Pm (μ i) := by
      rw [hP]; exact MeasureTheory.measurePreserving_eval μ i
    have hcomp : (fun z : Fin n → ℝ => Real.log ((a i (z i)).toReal))
        = (fun y => Real.log ((a i y).toReal)) ∘ (Function.eval i) := rfl
    rw [hcomp]
    exact (hmp.integrable_comp
      ((((ha_meas i).ennreal_toReal.log).aestronglyMeasurable))).mpr (h_int i)
  have h_marg : ∀ i, (∫ z, Real.log ((a i (z i)).toReal) ∂Pm)
      = -InformationTheory.Shannon.differentialEntropy (μ i) := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) Pm (μ i) := by
      rw [hP]; exact MeasureTheory.measurePreserving_eval μ i
    have hGmeas : AEStronglyMeasurable (fun y => Real.log ((a i y).toReal)) (μ i) :=
      ((ha_meas i).ennreal_toReal.log).aestronglyMeasurable
    have h_map : (∫ z, Real.log ((a i (z i)).toReal) ∂Pm)
        = ∫ y, Real.log ((a i y).toReal) ∂(μ i) := by
      rw [← hmp.map_eq]
      exact (MeasureTheory.integral_map (measurable_pi_apply i).aemeasurable
        (by rw [hmp.map_eq]; exact hGmeas)).symm
    rw [h_map, ha_def, InformationTheory.Shannon.integral_log_rnDeriv_self_eq_neg (h_ac i)]
    rfl
  rw [h_step1, integral_congr_ae h_log_split, integral_finsetSum _ (fun i _ => h_int_P i)]
  rw [show (∑ i, ∫ z, Real.log ((a i (z i)).toReal) ∂Pm)
        = ∑ i, -InformationTheory.Shannon.differentialEntropy (μ i) from
    Finset.sum_congr rfl (fun i _ => h_marg i)]
  rw [Finset.sum_neg_distrib, neg_neg]

/-- Fibre neg-entropy value: `∫ y, log (rnDeriv (blockKernelInline m) vol) ∂(blockKernelInline m)
= -n·h(gaussianReal 0 N)`. -/
private lemma fibre_neg_entropy
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    ∫ y, Real.log
        (((blockKernelInline N c) m).rnDeriv MeasureTheory.volume y).toReal
        ∂((blockKernelInline N c) m)
      = -((n : ℝ) * InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N)) := by
  -- the m-th fibre is the product Gaussian `pi (gaussianReal (encoder m i) N)`
  have hfibre : (blockKernelInline N c) m
      = Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) := rfl
  rw [hfibre]
  set νp := Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) with hνp
  haveI : IsProbabilityMeasure νp := by rw [hνp]; infer_instance
  have h_ac : νp ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hνp, blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  -- `jointDifferentialEntropyPi νp = ∑ᵢ h(gaussian (encoder m i) N) = n·h(gaussian 0 N)`
  have h_sum : InformationTheory.Shannon.jointDifferentialEntropyPi νp
      = ∑ i : Fin n, InformationTheory.Shannon.differentialEntropy
          (gaussianReal (c.encoder m i) N) := by
    rw [hνp]
    exact jointDifferentialEntropyPi_pi_eq_sum_inline
      (fun i => gaussianReal (c.encoder m i) N)
      (fun i => gaussianReal_absolutelyContinuous (c.encoder m i) hN)
      (fun i => gaussianReal_logRnDeriv_integrable_inline (c.encoder m i) hN)
  have h_inv : ∀ i : Fin n,
      InformationTheory.Shannon.differentialEntropy (gaussianReal (c.encoder m i) N)
        = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
    intro i
    rw [InformationTheory.Shannon.differentialEntropy_gaussianReal (c.encoder m i) hN,
      InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hN]
  rw [show (∫ y, Real.log (νp.rnDeriv volume y).toReal ∂νp)
        = -InformationTheory.Shannon.jointDifferentialEntropyPi νp from by
    rw [InformationTheory.Shannon.integral_log_rnDeriv_self_eq_neg h_ac]; rfl]
  rw [h_sum, Finset.sum_congr rfl (fun i _ => h_inv i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- `count = ∑ₐ dirac a` on a `Fintype` (mirror of `count_eq_finset_sum_dirac`). -/
private lemma count_eq_finset_sum_dirac_inline (α : Type*) [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (Measure.count : Measure α) = ∑ a : α, Measure.dirac a := by
  have h_one : ∀ a : α, (Measure.count : Measure α) {a} = 1 := fun a =>
    Measure.count_singleton a
  have h_sum : Measure.sum (fun a : α => Measure.dirac a)
      = (Measure.count : Measure α) := by
    have h := Measure.sum_smul_dirac (μ := (Measure.count : Measure α))
    simp_rw [h_one, one_smul] at h
    exact h
  rw [← h_sum, Measure.sum_fintype]

/-- **Elementary discrete-input factorization** (mixture-of-diracs):
`converseJointInline = msgLawInline ⊗ₘ blockKernelInline`. -/
private lemma converseJointInline_eq_compProd
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    converseJointInline h_meas c = msgLawInline M ⊗ₘ blockKernelInline N c := by
  classical
  unfold converseJointInline msgLawInline
  rw [Measure.compProd_smul_left]
  congr 1
  rw [count_eq_finset_sum_dirac_inline (Fin M), ← Measure.sum_fintype
        (fun a : Fin M => Measure.dirac a),
    Measure.compProd_sum_left, Measure.sum_fintype]
  symm
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [show (Measure.dirac m) ⊗ₘ blockKernelInline N c
        = (Measure.dirac m).prod (blockKernelInline N c m) by
      ext s hs
      rw [Measure.dirac_compProd_apply hs, Measure.dirac_prod,
        Measure.map_apply measurable_prodMk_left hs]]
  refine congrArg ((Measure.dirac m).prod) ?_
  show Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))
      = Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)
  refine congrArg Measure.pi ?_
  funext i
  rw [awgnChannel_apply]

/-- **Output law identification**: `outputDistribution msgLawInline blockKernelInline
= blockYLawInline`. -/
private lemma outputDistribution_msgLawInline_eq
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    ChannelCoding.outputDistribution (msgLawInline M) (blockKernelInline N c)
      = blockYLawInline h_meas c := by
  -- `outputDistribution p W = (p ⊗ₘ W).snd = (p ⊗ₘ W).map snd`
  show (msgLawInline M ⊗ₘ blockKernelInline N c).map Prod.snd = blockYLawInline h_meas c
  rw [← converseJointInline_eq_compProd h_meas c]
  rfl

/-- `mutualInfo μ fst snd = mutualInfoOfChannel msgLawInline blockKernelInline`. -/
private lemma mutualInfo_fst_snd_eq_channel
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd
      = ChannelCoding.mutualInfoOfChannel (msgLawInline M) (blockKernelInline N c) := by
  rw [ChannelCoding.mutualInfoOfChannel_eq_mutualInfo_prod]
  -- `jointDistribution msgLaw blockKernel = msgLaw ⊗ₘ blockKernel = converseJointInline`
  congr 1
  rw [ChannelCoding.jointDistribution_def, ← converseJointInline_eq_compProd h_meas c]

/-- **Deterministic DPI**: `I(X^n;Y^n) ≤ I(W;Y^n)` (`X^n = encoder ∘ fst` is a
post-processing of `W = fst`). -/
private lemma mutualInfo_encoder_le_fst
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (converseJointInline h_meas c) (fun ω => c.encoder ω.1) Prod.snd
      ≤ mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd := by
  set μ := converseJointInline h_meas c with hμ
  have hfst : Measurable (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) := measurable_fst
  have hsnd : Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := measurable_snd
  have henc : Measurable (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1) :=
    (measurable_of_countable c.encoder).comp measurable_fst
  -- `encoder ∘ fst = encoder ∘ (id) ∘ fst`; post-process the FIRST argument via comm + 2nd DPI.
  rw [mutualInfo_comm μ (fun ω => c.encoder ω.1) Prod.snd henc hsnd,
    mutualInfo_comm μ Prod.fst Prod.snd hfst hsnd]
  -- now: `I(Y; encoder∘fst) ≤ I(Y; fst)`; `encoder∘fst = encoder ∘ fst`
  have h_comp : (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1)
      = c.encoder ∘ (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) := rfl
  rw [h_comp]
  exact mutualInfo_le_of_postprocess μ Prod.snd Prod.fst hsnd hfst
    (measurable_of_countable c.encoder)

/-- `converseJointInline.map fst = msgLawInline` (uniform message marginal). -/
private lemma converseJointInline_map_fst_eq_msgLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (converseJointInline h_meas c).map (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
      = msgLawInline M := by
  classical
  unfold converseJointInline msgLawInline
  rw [Measure.map_smul, Measure.map_finset_sum (s := Finset.univ)
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
      measurable_fst.aemeasurable]
  rw [count_eq_finset_sum_dirac_inline (Fin M)]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- Marginals product `(μ.map fst).prod (μ.map snd) = msgLaw ⊗ₘ const blockYLaw`. -/
private lemma converseJointInline_prod_marginals_eq
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    ((converseJointInline h_meas c).map Prod.fst).prod ((converseJointInline h_meas c).map Prod.snd)
      = msgLawInline M ⊗ₘ Kernel.const (Fin M) (blockYLawInline h_meas c) := by
  rw [converseJointInline_map_fst_eq_msgLaw h_meas c,
    show (converseJointInline h_meas c).map Prod.snd = blockYLawInline h_meas c from rfl,
    Measure.compProd_const]

/-- Per-fibre log-likelihood-ratio integrability:
`log (νₘ.rnDeriv blockYLaw)` integrable against the m-th block component `νₘ`. -/
private lemma integrable_log_component_rnDeriv_blockYLawInline
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Integrable
      (fun y => Real.log
        ((Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)).rnDeriv
          (blockYLawInline h_meas c) y).toReal)
      (Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)) := by
  classical
  set νm := Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) with hνm
  set q := blockYLawInline h_meas c with hq
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i => inferInstance
  haveI hνm_prob : IsProbabilityMeasure νm := by rw [hνm]; infer_instance
  haveI hq_prob : IsProbabilityMeasure q := by rw [hq]; infer_instance
  have hνm_q : νm ≪ q := by rw [hνm, hq]; exact blockComponentInline_ac_blockYLaw hN h_meas c m
  have hq_vol : q ≪ (volume : Measure (Fin n → ℝ)) := by rw [hq]; exact blockYLawInline_ac_volume hN h_meas c
  have hνm_vol : νm ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hνm, blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  -- `log(νₘ/q) =ᵐ[νₘ] log(νₘ/vol) − log(q/vol)`; both terms integrable.
  have h_split : (fun y => Real.log ((νm.rnDeriv q y).toReal))
      =ᵐ[νm] (fun y => Real.log ((νm.rnDeriv volume y).toReal)
                - Real.log ((q.rnDeriv volume y).toReal)) :=
    ChannelCoding.log_rnDeriv_split_gen hνm_q hq_vol
  refine Integrable.congr ?_ h_split.symm
  -- term A: `log(νₘ.rnDeriv vol)` integrable against νₘ (product-Gaussian log-density)
  have hA : Integrable (fun y => Real.log ((νm.rnDeriv volume y).toReal)) νm := by
    rw [hνm]; exact integrable_log_fibre_rnDeriv hN c m
  -- term B: `log(q.rnDeriv vol)` integrable against νₘ (= component output log-density)
  have hB : Integrable (fun y => Real.log ((q.rnDeriv volume y).toReal)) νm := by
    rw [hνm, hq]; exact integrable_log_blockYLawInline_on_component hN h_meas c m
  exact hA.sub hB

/-- `I(W;Y^n) ≠ ∞` (finiteness, so `.toReal` is monotone). -/
private lemma mutualInfo_fst_snd_ne_top
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd ≠ ∞ := by
  classical
  rw [mutualInfo]
  have h_joint : (converseJointInline h_meas c).map
      (fun ω : Fin M × (Fin n → ℝ) => (ω.1, ω.2)) = msgLawInline M ⊗ₘ blockKernelInline N c := by
    rw [show (fun ω : Fin M × (Fin n → ℝ) => (ω.1, ω.2)) = id from rfl, Measure.map_id]
    exact converseJointInline_eq_compProd h_meas c
  rw [h_joint, converseJointInline_prod_marginals_eq h_meas c]
  refine klDiv_ne_top ?_ ?_
  · -- AC: msgLaw ⊗ₘ K ≪ msgLaw ⊗ₘ const blockY
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    filter_upwards with m
    show blockKernelInline N c m ≪ (Kernel.const (Fin M) (blockYLawInline h_meas c)) m
    rw [Kernel.const_apply]
    show Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) ≪ blockYLawInline h_meas c
    exact blockComponentInline_ac_blockYLaw hN h_meas c m
  · -- integrable llr
    set K := blockKernelInline N c with hK
    set ηc := Kernel.const (Fin M) (blockYLawInline h_meas c) with hηc
    have h_ac : msgLawInline M ⊗ₘ K ≪ msgLawInline M ⊗ₘ ηc := by
      refine Measure.AbsolutelyContinuous.compProd_right ?_
      filter_upwards with m
      rw [hηc, Kernel.const_apply]
      show Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) ≪ blockYLawInline h_meas c
      exact blockComponentInline_ac_blockYLaw hN h_meas c m
    have h_llr_ae : (fun p => llr (msgLawInline M ⊗ₘ K) (msgLawInline M ⊗ₘ ηc) p)
        =ᵐ[msgLawInline M ⊗ₘ K]
        (fun p : Fin M × (Fin n → ℝ) => Real.log ((K.rnDeriv ηc p.1 p.2)).toReal) := by
      have h1 : (msgLawInline M ⊗ₘ K).rnDeriv (msgLawInline M ⊗ₘ ηc)
          =ᵐ[msgLawInline M ⊗ₘ K] fun p => K.rnDeriv ηc p.1 p.2 :=
        h_ac.ae_le (ChannelCoding.rnDeriv_compProd_fibre h_ac)
      simp only [llr_def]
      filter_upwards [h1] with p hp1
      rw [hp1]
    refine Integrable.congr ?_ h_llr_ae.symm
    refine (Measure.integrable_compProd_iff ?_).mpr ⟨?_, ?_⟩
    · exact ((Kernel.measurable_rnDeriv K ηc).ennreal_toReal.log).aestronglyMeasurable
    · filter_upwards with m
      have h_fibre_ae : (fun y => Real.log ((K.rnDeriv ηc m y)).toReal)
          =ᵐ[K m] (fun y => Real.log (((K m).rnDeriv (blockYLawInline h_meas c) y)).toReal) := by
        have hKm_blockY : K m ≪ blockYLawInline h_meas c := by
          rw [hK]
          show Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) ≪ blockYLawInline h_meas c
          exact blockComponentInline_ac_blockYLaw hN h_meas c m
        have h_meas_eq : K m ≪ ηc m := by rw [hηc, Kernel.const_apply]; exact hKm_blockY
        filter_upwards [h_meas_eq.ae_le
          (Kernel.rnDeriv_eq_rnDeriv_measure (κ := K) (η := ηc) (a := m))] with y hy
        rw [hy]; simp only [hηc, Kernel.const_apply]
      refine Integrable.congr ?_ h_fibre_ae.symm
      show Integrable
        (fun y => Real.log
          ((Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)).rnDeriv
            (blockYLawInline h_meas c) y).toReal)
        (Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N))
      exact integrable_log_component_rnDeriv_blockYLawInline hN h_meas c m
    · exact Integrable.of_finite

/-- **Block MI decomposition**: `I(W;Y^n).toReal = h(Y^n) − n·h(noise)`. -/
private lemma blockMI_decomp
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd).toReal
      = InformationTheory.Shannon.jointDifferentialEntropyPi (blockYLawInline h_meas c)
        - (n : ℝ) * InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
  classical
  set p := msgLawInline M with hp
  set W := blockKernelInline N c with hW
  -- output distribution identification
  have hq_eq : ChannelCoding.outputDistribution p W = blockYLawInline h_meas c :=
    outputDistribution_msgLawInline_eq h_meas c
  -- regularity (in the generic decomp's `outputDistribution` form)
  have hWx_q : ∀ m, W m ≪ ChannelCoding.outputDistribution p W := by
    intro m; rw [hq_eq]
    exact blockComponentInline_ac_blockYLaw hN h_meas c m
  have hq_ref : ChannelCoding.outputDistribution p W ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hq_eq]; exact blockYLawInline_ac_volume hN h_meas c
  haveI : (ChannelCoding.outputDistribution p W).HaveLebesgueDecomposition
      (volume : Measure (Fin n → ℝ)) := by infer_instance
  have h_joint_ac : (p ⊗ₘ W) ≪ p.prod (ChannelCoding.outputDistribution p W) := by
    rw [← Measure.compProd_const]
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    exact Filter.Eventually.of_forall (fun m => by
      simpa only [Kernel.const_apply] using hWx_q m)
  -- proxy
  set g : (Fin M) × (Fin n → ℝ) → ℝ≥0∞ := blockProxy N c with hg
  have hg_meas : Measurable g := blockProxy_measurable N c
  have hg_ae : ∀ m, (fun y => (W m).rnDeriv volume y) =ᵐ[W m] fun y => g (m, y) :=
    fun m => blockProxy_ae hN c m
  -- compProd-level integrabilities (msgLaw is finite-support → norm-integrability free)
  have h_int_fibre_self : ∀ m, Integrable (fun y => Real.log (g (m, y)).toReal) (W m) := by
    intro m
    refine (integrable_log_fibre_rnDeriv hN c m).congr ?_
    filter_upwards [hg_ae m] with y hy
    rw [hy]
  have h_int_fibre : Integrable (fun z : (Fin M) × (Fin n → ℝ) => Real.log (g z).toReal) (p ⊗ₘ W) := by
    rw [Measure.integrable_compProd_iff ((hg_meas.ennreal_toReal.log).aestronglyMeasurable)]
    refine ⟨Filter.Eventually.of_forall (fun m => h_int_fibre_self m), ?_⟩
    -- `p = msgLaw` is a finite measure on the finite type `Fin M` → integrable for free
    exact Integrable.of_finite
  have h_out_self : Integrable
      (fun y => Real.log ((ChannelCoding.outputDistribution p W).rnDeriv volume y).toReal)
      (ChannelCoding.outputDistribution p W) := by
    rw [hq_eq]
    -- integrate the fixed function against the mixture measure (rewrite only the measure)
    set F : (Fin n → ℝ) → ℝ :=
      fun y => Real.log ((blockYLawInline h_meas c).rnDeriv volume y).toReal with hF
    have h_mix : blockYLawInline h_meas c
        = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
            ∑ m : Fin M, Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) :=
      blockYLawInline_eq_mixture h_meas c
    rw [h_mix]
    have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
      rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
    refine Integrable.smul_measure ?_ hM_inv_ne_top
    refine integrable_finsetSum_measure.mpr (fun m _ => ?_)
    exact integrable_log_blockYLawInline_on_component hN h_meas c m
  have h_int_out : Integrable
      (fun z : (Fin M) × (Fin n → ℝ) => Real.log
          ((ChannelCoding.outputDistribution p W).rnDeriv volume z.2).toReal) (p ⊗ₘ W) := by
    set ψ : (Fin n → ℝ) → ℝ := fun y => Real.log
      ((ChannelCoding.outputDistribution p W).rnDeriv volume y).toReal with hψ
    have hψ_meas : Measurable ψ :=
      (Real.measurable_log.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal)
    show Integrable (fun z : (Fin M) × (Fin n → ℝ) => ψ z.2) (p ⊗ₘ W)
    rw [Measure.integrable_compProd_iff
      (f := fun z : (Fin M) × (Fin n → ℝ) => ψ z.2)
      ((hψ_meas.comp measurable_snd).aestronglyMeasurable)]
    refine ⟨Filter.Eventually.of_forall (fun m => ?_), ?_⟩
    · -- per-fibre: `ψ` integrable against `W m = pi gaussian`; via output id + on-component
      have : Integrable
          (fun y => Real.log ((blockYLawInline h_meas c).rnDeriv volume y).toReal) (W m) :=
        integrable_log_blockYLawInline_on_component hN h_meas c m
      refine this.congr ?_
      filter_upwards with y; rw [hψ, hq_eq]
    · exact Integrable.of_finite
  have h_fibre_self : ∀ m, ∫ y, Real.log (g (m, y)).toReal ∂(W m)
      = ∫ y, Real.log ((W m).rnDeriv volume y).toReal ∂(W m) := fun m => fibre_log_proxy_integral hN c m
  -- apply the generic decomposition
  rw [mutualInfo_fst_snd_eq_channel h_meas c]
  rw [ChannelCoding.mutualInfoOfChannel_toReal_eq_log_density_sub
    (volume : Measure (Fin n → ℝ)) hWx_q hq_ref h_joint_ac g hg_meas hg_ae
    h_int_fibre h_int_out h_fibre_self h_out_self]
  -- fibre term: `∫ m, (∫ y, log(rnDeriv (W m) vol) ∂(W m)) ∂msgLaw = -n·h(noise)`
  have h_fibre_val : (∫ m, (∫ y, Real.log ((W m).rnDeriv volume y).toReal ∂(W m)) ∂p)
      = -((n : ℝ) * InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun m => fibre_neg_entropy hN c m)),
      integral_const, probReal_univ, one_smul]
  -- output term: `∫ y, log(rnDeriv blockYLaw vol) ∂blockYLaw = -jointDiff`
  have h_out_val : (∫ y, Real.log
        ((ChannelCoding.outputDistribution p W).rnDeriv volume y).toReal
        ∂(ChannelCoding.outputDistribution p W))
      = -InformationTheory.Shannon.jointDifferentialEntropyPi (blockYLawInline h_meas c) := by
    rw [hq_eq, InformationTheory.Shannon.integral_log_rnDeriv_self_eq_neg
      (blockYLawInline_ac_volume hN h_meas c)]
    rfl
  rw [h_fibre_val, h_out_val]
  ring

/-- Joint measurability of `(x, y) ↦ gaussianPDF x N y` (mean × point). -/
private lemma gaussianPDF_joint_measurable (N : ℝ≥0) :
    Measurable (fun p : ℝ × ℝ => gaussianPDF p.1 N p.2) := by
  unfold gaussianPDF
  refine ENNReal.measurable_ofReal.comp ?_
  unfold gaussianPDFReal
  refine Measurable.mul measurable_const ?_
  refine Real.measurable_exp.comp ?_
  refine Measurable.div ?_ measurable_const
  refine (Measurable.pow ?_ measurable_const).neg
  exact (measurable_snd.sub measurable_fst)

/-- Per-letter input law `μ.map (encoder · i)` (discrete, real-valued). -/
private noncomputable def perLetterInputLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) : Measure ℝ :=
  (converseJointInline h_meas c).map (fun ω => c.encoder ω.1 i)

private instance perLetterInputLaw_isProb
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    IsProbabilityMeasure (perLetterInputLaw h_meas c i) := by
  rw [perLetterInputLaw]
  exact Measure.isProbabilityMeasure_map
    (((measurable_of_countable (fun m : Fin M => c.encoder m i)).comp measurable_fst).aemeasurable)

/-- `perLetterInputLaw_i = (1/M) • ∑ₘ δ_{encoder m i}` (mixture-of-diracs form). -/
private lemma perLetterInputLaw_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    perLetterInputLaw h_meas c i
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • ∑ m : Fin M, Measure.dirac (c.encoder m i) := by
  classical
  unfold perLetterInputLaw converseJointInline
  have henc_i : Measurable (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1 i) :=
    (measurable_of_countable (fun m : Fin M => c.encoder m i)).comp measurable_fst
  rw [Measure.map_smul, Measure.map_finset_sum (s := Finset.univ)
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
      henc_i.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  -- `((δ_m).prod ν).map (fun ω => encoder ω.1 i) = (δ_m).map (encoder · i) = δ_{encoder m i}`
  rw [show (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1 i)
        = (fun a : Fin M => c.encoder a i) ∘ Prod.fst from rfl,
    ← Measure.map_map (measurable_of_countable _) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul, MeasureTheory.Measure.map_dirac' (measurable_of_countable _)]

/-- **Per-letter X-input factorization** (mixture-of-diracs, holds with collisions):
`μ.map (fun ω => (encoder ω.1 i, ω.2 i)) = perLetterInputLaw_i ⊗ₘ awgnChannel`. -/
private lemma perLetter_map_eq_compProd
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (converseJointInline h_meas c).map (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i))
      = perLetterInputLaw h_meas c i ⊗ₘ awgnChannel N h_meas := by
  classical
  -- RHS: explicit mixture of diracs ⊗ₘ awgnChannel = (1/M) ∑ₘ δ_{encoder m i} ⊗ awgn
  rw [perLetterInputLaw_eq_mixture h_meas c i, Measure.compProd_smul_left]
  rw [← Measure.sum_fintype (fun m : Fin M => Measure.dirac (c.encoder m i)),
    Measure.compProd_sum_left, Measure.sum_fintype, Fintype.card_fin]
  -- LHS: distribute the map over the mixture
  unfold converseJointInline
  have hmap_fn : Measurable (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i)) :=
    ((measurable_of_countable (fun m : Fin M => c.encoder m i)).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  rw [Measure.map_smul, Measure.map_finset_sum (s := Finset.univ)
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
      hmap_fn.aemeasurable]
  have h_per : ∀ m : Fin M,
      ((Measure.dirac m).prod
          (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j)))).map
            (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i))
        = (Measure.dirac (c.encoder m i)) ⊗ₘ awgnChannel N h_meas := by
    intro m
    -- per-message: `((δ_m).prod (pi gaussian)).map (encoder·i, ·.2 i) = δ_{encoder m i} ⊗ₘ awgn`
    rw [show (Measure.dirac (c.encoder m i)) ⊗ₘ awgnChannel N h_meas
          = (Measure.dirac (c.encoder m i)).prod (awgnChannel N h_meas (c.encoder m i)) by
        ext s hs
        rw [Measure.dirac_compProd_apply hs, Measure.dirac_prod,
          Measure.map_apply measurable_prodMk_left hs]]
    -- LHS per-message
    rw [show (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i))
          = Prod.map (fun a : Fin M => c.encoder a i) (fun y : Fin n → ℝ => y i) from rfl]
    rw [← Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_pi_apply i)]
    rw [MeasureTheory.Measure.map_dirac' (measurable_of_countable _)]
    congr 1
    -- `(pi (gaussian (encoder m j))).map (·i) = gaussian (encoder m i) = awgnChannel (encoder m i)`
    rw [Measure.pi_map_eval]
    have h_prod_one : (∏ j ∈ Finset.univ.erase i,
        (awgnChannel N h_meas (c.encoder m j)) Set.univ) = 1 := by
      refine Finset.prod_eq_one (fun j _ => ?_)
      rw [awgnChannel_apply]; exact measure_univ
    rw [h_prod_one, one_smul, awgnChannel_apply]
  rw [Finset.sum_congr rfl (fun m _ => h_per m), Fintype.card_fin]

/-- Positivity of the per-letter mixture density (single full-support component suffices). -/
private lemma perLetterMixtureDensity_pos
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} [NeZero M] (c : AwgnCode M n P)
    (i : Fin n) (y : ℝ) :
    0 < (perLetterMixtureDensity N c i y).toReal := by
  classical
  obtain ⟨m₀⟩ : Nonempty (Fin M) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩⟩
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h_ne_top : perLetterMixtureDensity N c i y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (perLetterMixtureDensity_le_sup N c i hM_pos y)
  rw [ENNReal.toReal_pos_iff]
  refine ⟨?_, lt_of_le_of_ne le_top h_ne_top⟩
  unfold perLetterMixtureDensity
  refine ENNReal.mul_pos ?_ ?_
  · simp only [ne_eq, ENNReal.inv_eq_zero]
    exact ENNReal.natCast_ne_top M
  · -- `∑ₘ gaussianPDF ... ≠ 0` (single component positive)
    have h_comp_pos : 0 < gaussianPDF (c.encoder m₀ i) N y := by
      rw [gaussianPDF, ENNReal.ofReal_pos]
      exact gaussianPDFReal_pos (c.encoder m₀ i) N y hN
    refine (lt_of_lt_of_le h_comp_pos (Finset.single_le_sum
      (f := fun m => gaussianPDF (c.encoder m i) N y) (fun m _ => zero_le')
      (Finset.mem_univ m₀))).ne'

/-- `perLetterYLaw_i ≪ volume` (mixture of full-support Gaussians). -/
private lemma perLetterLaw_ac_volume
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (converseJointInline h_meas c).map (fun ω => ω.2 i) ≪ (volume : Measure ℝ) := by
  rw [perLetterLaw_withDensity h_meas c i (Nat.pos_of_ne_zero (NeZero.ne M)) hN]
  exact MeasureTheory.withDensity_absolutelyContinuous _ _

/-- `volume ≪ perLetterYLaw_i` (mixture density everywhere positive). -/
private lemma volume_ac_perLetterLaw
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (volume : Measure ℝ) ≪ (converseJointInline h_meas c).map (fun ω => ω.2 i) := by
  rw [perLetterLaw_withDensity h_meas c i (Nat.pos_of_ne_zero (NeZero.ne M)) hN]
  refine withDensity_absolutelyContinuous'
    (perLetterMixtureDensity_measurable N c i).aemeasurable ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  have := perLetterMixtureDensity_pos hN c i y
  simp only [ne_eq]
  intro h0
  rw [h0] at this; simp at this

/-- **Marginal identification**: `blockYLawInline.map (· i) = (converseJointInline).map (·.2 i)`
= the per-letter law `Y_i`. -/
private lemma blockYLawInline_map_eval
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) :
    (blockYLawInline h_meas c).map (fun y => y i)
      = (converseJointInline h_meas c).map (fun ω => ω.2 i) := by
  show ((converseJointInline h_meas c).map Prod.snd).map (fun y => y i)
      = (converseJointInline h_meas c).map (fun ω => ω.2 i)
  rw [Measure.map_map (measurable_pi_apply i) measurable_snd]
  rfl

/-- Per-letter MI = channel MI: `mutualInfo μ X_i Y_i = mutualInfoOfChannel inputLaw_i awgn`. -/
private lemma perLetterMI_eq_channel
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    mutualInfo (converseJointInline h_meas c)
        (fun ω => c.encoder ω.1 i) (fun ω => ω.2 i)
      = ChannelCoding.mutualInfoOfChannel (perLetterInputLaw h_meas c i) (awgnChannel N h_meas) := by
  classical
  set μ := converseJointInline h_meas c with hμ
  set p := perLetterInputLaw h_meas c i with hp
  set W := awgnChannel N h_meas with hW
  have hX_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1 i) :=
    (measurable_of_countable (fun m : Fin M => c.encoder m i)).comp measurable_fst
  have hY_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) => ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hpair_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i)) :=
    hX_meas.prodMk hY_meas
  -- `mutualInfoOfChannel = klDiv (p ⊗ₘ W) (p.prod (outputDistribution p W))`
  rw [ChannelCoding.mutualInfoOfChannel_def, ChannelCoding.jointDistribution_def]
  -- `mutualInfo μ X_i Y_i = klDiv (μ.map (X_i,Y_i)) ((μ.map X_i).prod (μ.map Y_i))`
  unfold mutualInfo
  -- joint: `μ.map (X_i,Y_i) = p ⊗ₘ W`
  have h_joint : μ.map (fun ω => (c.encoder ω.1 i, ω.2 i)) = p ⊗ₘ W := by
    rw [hμ, hp, hW]; exact perLetter_map_eq_compProd h_meas c i
  -- input marginal: `μ.map X_i = p`
  have h_in : μ.map (fun ω => c.encoder ω.1 i) = p := by rw [hp, perLetterInputLaw]
  -- output marginal: `μ.map Y_i = outputDistribution p W`
  have h_out : μ.map (fun ω => ω.2 i) = ChannelCoding.outputDistribution p W := by
    show μ.map (fun ω => ω.2 i) = (p ⊗ₘ W).map Prod.snd
    rw [← h_joint, Measure.map_map measurable_snd hpair_meas]
    rfl
  rw [h_joint, h_in, h_out]

/-- Any measurable real function is integrable against the finite-support `perLetterInputLaw`
(a `(1/M)`-weighted sum of `M` Diracs). -/
private lemma integrable_of_perLetterInputLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n)
    {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f (perLetterInputLaw h_meas c i) := by
  classical
  rw [perLetterInputLaw_eq_mixture h_meas c i]
  have hM_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  refine Integrable.smul_measure ?_ hM_ne_top
  refine integrable_finsetSum_measure.mpr (fun m _ => ?_)
  exact integrable_dirac (enorm_lt_top)

/-- Per-fibre output log-density integrability (1-D): `log (rnDeriv perLetterYLaw_i vol)`
integrable against each Gaussian fibre `gaussian x N`. -/
private lemma integrable_log_perLetterLaw_on_fibre
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) (x : ℝ) :
    Integrable
      (fun y => Real.log
        (((converseJointInline h_meas c).map (fun ω => ω.2 i)).rnDeriv volume y).toReal)
      (gaussianReal x N) := by
  classical
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  set q := (converseJointInline h_meas c).map (fun ω => ω.2 i) with hq
  set f : ℝ → ℝ≥0∞ := perLetterMixtureDensity N c i with hf_def
  have hf_meas : Measurable f := perLetterMixtureDensity_measurable N c i
  have hq_wd : q = volume.withDensity f := by
    rw [hq, hf_def]; exact perLetterLaw_withDensity h_meas c i hM_pos hN
  have hgx_ac : gaussianReal x N ≪ (volume : Measure ℝ) := gaussianReal_absolutelyContinuous x hN
  have h_rn_vol : q.rnDeriv volume =ᵐ[volume] f := by
    rw [hq_wd]; exact Measure.rnDeriv_withDensity volume hf_meas
  have h_log_ae : (fun y => Real.log (q.rnDeriv volume y).toReal)
      =ᵐ[gaussianReal x N] (fun y => Real.log ((perLetterMixtureDensity N c i y).toReal)) := by
    filter_upwards [hgx_ac.ae_le h_rn_vol] with y hy
    rw [hy]
  refine (Integrable.congr ?_ h_log_ae.symm)
  obtain ⟨c₀, c₁, hc₁, h_abs⟩ := perLetterMixtureDensity_log_abs_le N c i hM_pos hN
  have h_sq_int : Integrable (fun y : ℝ => y ^ 2) (gaussianReal x N) :=
    (memLp_id_gaussianReal (μ := x) (v := N) 2).integrable_sq
  have h_dom : Integrable (fun y : ℝ => c₀ + c₁ * y ^ 2) (gaussianReal x N) :=
    (integrable_const c₀).add (h_sq_int.const_mul c₁)
  refine Integrable.mono' h_dom ?_ ?_
  · exact (Real.measurable_log.comp
      (perLetterMixtureDensity_measurable N c i).ennreal_toReal).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs]
    exact h_abs y

/-- **Per-letter MI decomposition**: `I(X_i;Y_i).toReal = h(Y_i) − h(noise)`. -/
private lemma perLetterMI_decomp
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (mutualInfo (converseJointInline h_meas c)
        (fun ω => c.encoder ω.1 i) (fun ω => ω.2 i)).toReal
      = InformationTheory.Shannon.differentialEntropy
          ((converseJointInline h_meas c).map (fun ω => ω.2 i))
        - InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
  classical
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  set p := perLetterInputLaw h_meas c i with hp
  set W := awgnChannel N h_meas with hW
  have hpair_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i)) :=
    ((measurable_of_countable (fun m : Fin M => c.encoder m i)).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  -- output distribution `q = perLetterYLaw_i`
  have hq_eq : ChannelCoding.outputDistribution p W
      = (converseJointInline h_meas c).map (fun ω => ω.2 i) := by
    show ((p ⊗ₘ W).map Prod.snd) = _
    rw [hp, hW, ← perLetter_map_eq_compProd h_meas c i]
    rw [Measure.map_map measurable_snd hpair_meas]
    rfl
  -- regularity
  have hW_ac : ∀ x, W x ≪ (volume : Measure ℝ) := by
    intro x; rw [hW, awgnChannel_apply]; exact gaussianReal_absolutelyContinuous x hN
  have hq_ac : ChannelCoding.outputDistribution p W ≪ (volume : Measure ℝ) := by
    rw [hq_eq]; exact perLetterLaw_ac_volume hN h_meas c i
  have hvol_ac_q : (volume : Measure ℝ) ≪ ChannelCoding.outputDistribution p W := by
    rw [hq_eq]; exact volume_ac_perLetterLaw hN h_meas c i
  have hWx_q : ∀ x, W x ≪ ChannelCoding.outputDistribution p W :=
    fun x => (hW_ac x).trans hvol_ac_q
  have h_joint_ac : (p ⊗ₘ W) ≪ p.prod (ChannelCoding.outputDistribution p W) := by
    rw [← Measure.compProd_const]
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Kernel.const_apply] using hWx_q x)
  -- proxy `g (x, y) := gaussianPDF x N y`
  set g : ℝ × ℝ → ℝ≥0∞ := fun z => gaussianPDF z.1 N z.2 with hg
  have hg_meas : Measurable g := gaussianPDF_joint_measurable N
  have hg_ae : ∀ x, (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y) := by
    intro x
    rw [hW, awgnChannel_apply]
    filter_upwards [(gaussianReal_absolutelyContinuous x hN).ae_le (rnDeriv_gaussianReal x N)]
      with y hy
    rw [hy]
  -- per-fibre log-density integrability against `W x = gaussian x N`
  have h_int_fibre_self : ∀ x, Integrable (fun y => Real.log (g (x, y)).toReal) (W x) := by
    intro x
    have hint := gaussianReal_logRnDeriv_integrable_inline x hN
    have hWx : W x = gaussianReal x N := by rw [hW, awgnChannel_apply]
    rw [hWx]
    refine hint.congr ?_
    filter_upwards [(gaussianReal_absolutelyContinuous x hN).ae_le (rnDeriv_gaussianReal x N)]
      with y hy
    rw [hg]; simp only; rw [hy]
  -- `h_fibre_self` (proxy integral = rnDeriv integral, per fibre)
  have h_fibre_self : ∀ x, ∫ y, Real.log (g (x, y)).toReal ∂(W x)
      = ∫ y, Real.log ((W x).rnDeriv volume y).toReal ∂(W x) := by
    intro x
    refine integral_congr_ae ?_
    filter_upwards [hg_ae x] with y hy
    rw [← hy]
  -- output log-density integrability against q (= perLetterYLaw_i)
  have h_out_self : Integrable
      (fun y => Real.log ((ChannelCoding.outputDistribution p W).rnDeriv volume y).toReal)
      (ChannelCoding.outputDistribution p W) := by
    rw [hq_eq]
    set ν : Measure ℝ := (converseJointInline h_meas c).map (fun ω => ω.2 i) with hν
    haveI hν_prob : IsProbabilityMeasure ν := by
      rw [hν]
      exact Measure.isProbabilityMeasure_map
        (((measurable_pi_apply i).comp measurable_snd).aemeasurable)
    set f : ℝ → ℝ≥0∞ := perLetterMixtureDensity N c i with hf_def
    have hf_meas : Measurable f := perLetterMixtureDensity_measurable N c i
    have hν_wd : ν = volume.withDensity f := by
      rw [hν, hf_def]; exact perLetterLaw_withDensity h_meas c i hM_pos hN
    have hν_ac : ν ≪ (volume : Measure ℝ) := by
      rw [hν_wd]; exact MeasureTheory.withDensity_absolutelyContinuous _ _
    have h_rn_vol : ν.rnDeriv volume =ᵐ[volume] f := by
      conv_lhs => rw [hν_wd]
      exact Measure.rnDeriv_withDensity volume hf_meas
    have h_log_ae : (fun y => Real.log (ν.rnDeriv volume y).toReal)
        =ᵐ[ν] (fun y => Real.log ((perLetterMixtureDensity N c i y).toReal)) := by
      filter_upwards [hν_ac.ae_le h_rn_vol] with y hy
      rw [hy]
    refine (Integrable.congr ?_ h_log_ae.symm)
    obtain ⟨c₀, c₁, hc₁, h_abs⟩ := perLetterMixtureDensity_log_abs_le N c i hM_pos hN
    have h_dom : Integrable (fun y : ℝ => c₀ + c₁ * y ^ 2) ν :=
      (integrable_const c₀).add (((by rw [hν]; exact perLetterLaw_sq_integrable h_meas c i hM_pos hN)
        : Integrable (fun y : ℝ => y ^ 2) ν).const_mul c₁)
    refine Integrable.mono' h_dom ?_ ?_
    · exact (Real.measurable_log.comp
        (perLetterMixtureDensity_measurable N c i).ennreal_toReal).aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs]
      exact h_abs y
  -- compProd-level integrabilities (the `p`-norm-integrability is free: `p` is finite-support)
  have h_int_fibre : Integrable (fun z : ℝ × ℝ => Real.log (g z).toReal) (p ⊗ₘ W) := by
    rw [Measure.integrable_compProd_iff
      ((hg_meas.ennreal_toReal.log).aestronglyMeasurable)]
    refine ⟨Filter.Eventually.of_forall (fun x => h_int_fibre_self x), ?_⟩
    rw [hp]
    refine integrable_of_perLetterInputLaw h_meas c i ?_
    -- measurability of `x ↦ ∫ y, ‖log g(x,y)‖ ∂(W x)`
    have : StronglyMeasurable
        (fun x => ∫ y, ‖Real.log (g (x, y)).toReal‖ ∂(W x)) :=
      (StronglyMeasurable.integral_kernel_prod_right' (κ := W)
        (f := fun z : ℝ × ℝ => ‖Real.log (g z).toReal‖)
        (hg_meas.ennreal_toReal.log.norm.stronglyMeasurable))
    exact this.measurable
  have h_int_out : Integrable
      (fun z : ℝ × ℝ => Real.log
          ((ChannelCoding.outputDistribution p W).rnDeriv volume z.2).toReal) (p ⊗ₘ W) := by
    rw [hq_eq]
    set ψ : ℝ → ℝ := fun y => Real.log
      (((converseJointInline h_meas c).map (fun ω => ω.2 i)).rnDeriv volume y).toReal with hψ
    have hψ_meas : Measurable ψ :=
      (Real.measurable_log.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal)
    show Integrable (fun z : ℝ × ℝ => ψ z.2) (p ⊗ₘ W)
    rw [Measure.integrable_compProd_iff
      (f := fun z : ℝ × ℝ => ψ z.2) ((hψ_meas.comp measurable_snd).aestronglyMeasurable)]
    refine ⟨Filter.Eventually.of_forall (fun x => ?_), ?_⟩
    · -- per-fibre: `ψ` integrable against `W x = gaussian x N`
      have hWx : W x = gaussianReal x N := by rw [hW, awgnChannel_apply]
      rw [hWx]
      exact integrable_log_perLetterLaw_on_fibre hN h_meas c i x
    · -- `p`-norm-integrability (finite support)
      rw [hp]
      refine integrable_of_perLetterInputLaw h_meas c i ?_
      have : StronglyMeasurable (fun x => ∫ y, ‖ψ y‖ ∂(W x)) :=
        (StronglyMeasurable.integral_kernel_prod_right' (κ := W)
          (f := fun z : ℝ × ℝ => ‖ψ z.2‖)
          ((hψ_meas.comp measurable_snd).norm.stronglyMeasurable))
      exact this.measurable
  -- apply the generic 1-D decomposition
  rw [perLetterMI_eq_channel h_meas c i]
  rw [ChannelCoding.mutualInfoOfChannel_toReal_eq_diffEntropy_sub
    hW_ac hWx_q hq_ac h_joint_ac g hg_meas hg_ae h_int_fibre h_int_out]
  rw [hq_eq]
  -- fibre term: `∫ x, h(W x) ∂p = ∫ x, h(gaussian 0 N) ∂p = h(gaussian 0 N)`
  have h_fibre_ent : ∀ x, InformationTheory.Shannon.differentialEntropy (W x)
      = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
    intro x
    rw [hW, awgnChannel_apply,
      InformationTheory.Shannon.differentialEntropy_gaussianReal x hN,
      InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hN]
  rw [integral_congr_ae (Filter.Eventually.of_forall h_fibre_ent), integral_const,
    probReal_univ, one_smul]

/-- `log(blockYLaw.rnDeriv vol)` integrable against `blockYLaw` itself (mixture of components). -/
private lemma integrable_log_blockYLawInline_self
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    Integrable
      (fun y => Real.log ((blockYLawInline h_meas c).rnDeriv volume y).toReal)
      (blockYLawInline h_meas c) := by
  classical
  set F : (Fin n → ℝ) → ℝ :=
    fun y => Real.log ((blockYLawInline h_meas c).rnDeriv volume y).toReal with hF
  rw [blockYLawInline_eq_mixture h_meas c]
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  refine Integrable.smul_measure ?_ hM_inv_ne_top
  refine integrable_finsetSum_measure.mpr (fun m _ => ?_)
  exact integrable_log_blockYLawInline_on_component hN h_meas c m

/-- `log(perLetterYLaw_i.rnDeriv vol (y i))` integrable against `blockYLaw` (per-coord marginal
log-density against the joint). -/
private lemma integrable_log_marg_on_blockYLawInline
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    Integrable
      (fun y => Real.log
        ((((converseJointInline h_meas c).map (fun ω => ω.2 i))).rnDeriv volume (y i)).toReal)
      (blockYLawInline h_meas c) := by
  classical
  set F : (Fin n → ℝ) → ℝ := fun y => Real.log
      ((((converseJointInline h_meas c).map (fun ω => ω.2 i))).rnDeriv volume (y i)).toReal with hF
  rw [blockYLawInline_eq_mixture h_meas c]
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  refine Integrable.smul_measure ?_ hM_inv_ne_top
  refine integrable_finsetSum_measure.mpr (fun m _ => ?_)
  -- `F y = (ψ ∘ eval i) y` where `ψ = log(perLetterYLaw_i.rnDeriv vol)`, integrable against the
  -- i-th 1-D Gaussian factor via `integrable_comp_eval`
  rw [hF]
  show Integrable (fun y : Fin n → ℝ => Real.log
      (((converseJointInline h_meas c).map (fun ω => ω.2 i)).rnDeriv volume (y i)).toReal)
    (Measure.pi (fun j : Fin n => gaussianReal (c.encoder m j) N))
  exact integrable_comp_eval (μ := fun j : Fin n => gaussianReal (c.encoder m j) N) (i := i)
    (integrable_log_perLetterLaw_on_fibre hN h_meas c i (c.encoder m i))

/-- **n-D subadditivity for the block output law**: `h(Y^n) ≤ ∑ᵢ h(Y_i)`. -/
private lemma jointDifferentialEntropyPi_blockYLawInline_le_sum
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    InformationTheory.Shannon.jointDifferentialEntropyPi (blockYLawInline h_meas c)
      ≤ ∑ i : Fin n, InformationTheory.Shannon.differentialEntropy
          ((converseJointInline h_meas c).map (fun ω => ω.2 i)) := by
  classical
  set q := blockYLawInline h_meas c with hq
  haveI : IsProbabilityMeasure q := by rw [hq]; infer_instance
  -- marginal identification: `q.map (·i) = perLetterYLaw_i`
  have h_marg_eq : ∀ i, q.map (fun y => y i) = (converseJointInline h_meas c).map (fun ω => ω.2 i) :=
    fun i => blockYLawInline_map_eval h_meas c i
  haveI : ∀ i, IsProbabilityMeasure (q.map (fun z => z i)) := by
    intro i; rw [h_marg_eq i]
    exact Measure.isProbabilityMeasure_map (((measurable_pi_apply i).comp measurable_snd).aemeasurable)
  have h_marg_ac : ∀ i, (q.map (fun z => z i)) ≪ (volume : Measure ℝ) := by
    intro i; rw [h_marg_eq i]; exact perLetterLaw_ac_volume hN h_meas c i
  have hμ_ac : q ≪ (volume : Measure (Fin n → ℝ)) := by rw [hq]; exact blockYLawInline_ac_volume hN h_meas c
  -- `q ≪ pi(marginals)` via `q ≪ vol` and `vol ≪ pi(marginals)`
  have hvol_ac_pi : (volume : Measure (Fin n → ℝ)) ≪ Measure.pi (fun i => q.map (fun z => z i)) := by
    have h_rev : ∀ i, (volume : Measure ℝ) ≪ q.map (fun z => z i) := by
      intro i; rw [h_marg_eq i]; exact volume_ac_perLetterLaw hN h_meas c i
    -- mirror of `pi_absolutelyContinuous_reverse`
    set f : Fin n → ℝ → ℝ≥0∞ := fun i => (q.map (fun z => z i)).rnDeriv volume with hf_def
    have hf_meas : ∀ i, Measurable (f i) := fun i => Measure.measurable_rnDeriv _ _
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (f i) = q.map (fun z => z i) :=
      fun i => Measure.withDensity_rnDeriv_eq _ volume (h_marg_ac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_eq : Measure.pi (fun i => q.map (fun z => z i))
        = (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity
            (fun z => ∏ i, f i (z i)) := by
      rw [← (funext h_eq : (fun i => (volume : Measure ℝ).withDensity (f i))
          = fun i => q.map (fun z => z i))]
      exact InformationTheory.Shannon.pi_withDensity_fin (fun _ : Fin n => (volume : Measure ℝ)) hf_meas
    rw [h_pi_eq, ← volume_pi]
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (Finset.measurable_prod _ (fun i _ => (hf_meas i).comp (measurable_pi_apply i))).aemeasurable
    · -- each `f i (z i)` a.e.-positive on `volume` (from `volume ≪ q.map(·i)`)
      have h_pos : ∀ i, ∀ᵐ y ∂(volume : Measure ℝ), f i y ≠ 0 := by
        intro i
        have := Measure.rnDeriv_pos' (h_rev i)
        filter_upwards [this] with y hy using hy.ne'
      filter_upwards [eventually_countable_forall.mpr
        (fun i => (Measure.quasiMeasurePreserving_eval
          (μ := fun _ : Fin n => (volume : Measure ℝ)) i).ae (h_pos i))] with z hz
      simp only [ne_eq, Finset.prod_eq_zero_iff, not_exists, not_and]
      intro i _
      exact hz i
  have h_joint_ac : q ≪ Measure.pi (fun i => q.map (fun z => z i)) := hμ_ac.trans hvol_ac_pi
  -- integrability
  have h_int_joint : Integrable (fun z => Real.log ((q.rnDeriv volume z).toReal)) q := by
    rw [hq]; exact integrable_log_blockYLawInline_self hN h_meas c
  have h_int_marg : ∀ i, Integrable
      (fun z => Real.log (((q.map (fun z => z i)).rnDeriv volume (z i)).toReal)) q := by
    intro i
    have h_eq : (fun z : Fin n → ℝ => Real.log (((q.map (fun z => z i)).rnDeriv volume (z i)).toReal))
        = (fun z => Real.log
            ((((converseJointInline h_meas c).map (fun ω => ω.2 i)).rnDeriv volume (z i)).toReal)) := by
      funext z; rw [h_marg_eq i]
    rw [h_eq, hq]
    exact integrable_log_marg_on_blockYLawInline hN h_meas c i
  -- apply the n-D subadditivity bridge, then rewrite marginals
  have h_sub := InformationTheory.Shannon.jointDifferentialEntropyPi_le_sum
    (μ := q) h_marg_ac hμ_ac h_joint_ac h_int_joint h_int_marg
  rw [Finset.sum_congr rfl (fun i _ => congrArg InformationTheory.Shannon.differentialEntropy
    (h_marg_eq i))] at h_sub
  exact h_sub

/-- **Memoryless AWGN continuous MI chain rule** (旧 `ContinuousMIChainRuleForConverse`).

`I(X^n; Y^n) ≤ ∑ᵢ I(X_i; Y_i)` on the inlined joint — **genuine closure** (false-wall
overturn, 2026-06-12). The route: `I(X^n;Y^n) ≤ I(W;Y^n)` (deterministic DPI) `= h(Y^n) −
n·h(noise) ≤ ∑ h(Y_i) − n·h(noise) = ∑ I(X_i;Y_i)`, combining `mutualInfo_encoder_le_fst`,
`blockMI_decomp`, `jointDifferentialEntropyPi_blockYLawInline_le_sum`, and `perLetterMI_decomp`.
Consumer-side `unfold jointMIXnYn perLetterMI awgnConverseJoint` で defeq.

`[NeZero M]` (`M ≥ 1`, the uniform message law is a probability measure) and `hN : N ≠ 0`
(full-support Gaussian fibres ⇒ blockYLaw absolutely continuous) are **regularity
preconditions**, both supplied by the converse consumer `isAwgnConverseFeasible_discharger`
(`2 ≤ M` ⇒ `NeZero M`, and `hN : (N:ℝ) ≠ 0`). Not load-bearing: the MI inequality is
proved genuinely from the entropy chain, not encoded in the hypotheses.
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free).

Independent honesty audit 2026-06-12 PASS (4-check): non-circular / non-bundled
(all helpers `mutualInfo_encoder_le_fst` (real DPI `mutualInfo_le_of_postprocess`),
`blockMI_decomp` / `perLetterMI_decomp` (genuine gateway-atom applications, all-regularity
hyps discharged locally), `jointDifferentialEntropyPi_blockYLawInline_le_sum` (KL≥0
subadditivity) carry regularity, not the claim) / non-degenerate / sufficiency
(degenerate boundary N=0 ⇒ Gaussian fibres collapse to Diracs, breaking only the
density route — the MI inequality itself stays true (KL≥0-backed), so `hN`/`NeZero M`
are density-route regularity, not false-statement constraints). `#print axioms` re-confirmed
sorryAx-free with refreshed oleans.
@audit:ok -/
@[entry_point]
theorem awgnContinuousMIChainRule_holds
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (mutualInfo (converseJointInline h_meas c)
        (fun ω => c.encoder ω.1) Prod.snd).toReal
      ≤ ∑ i : Fin n,
          (mutualInfo (converseJointInline h_meas c)
            (fun ω => c.encoder ω.1 i) (fun ω => ω.2 i)).toReal := by
  classical
  set h := InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) with hh
  -- LHS ≤ I(W;Y^n).toReal via deterministic DPI + finiteness.
  have h_dpi := mutualInfo_encoder_le_fst h_meas c
  have h_fin := mutualInfo_fst_snd_ne_top hN h_meas c
  have h_lhs_le :
      (mutualInfo (converseJointInline h_meas c) (fun ω => c.encoder ω.1) Prod.snd).toReal
        ≤ (mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd).toReal :=
    ENNReal.toReal_mono h_fin h_dpi
  -- I(W;Y^n).toReal = h(Y^n) − n·h(noise).
  have h_block := blockMI_decomp hN h_meas c
  -- h(Y^n) ≤ ∑ᵢ h(Y_i).
  have h_sub := jointDifferentialEntropyPi_blockYLawInline_le_sum hN h_meas c
  -- ∑ᵢ I(X_i;Y_i).toReal = (∑ᵢ h(Y_i)) − n·h(noise).
  have h_sum_perletter :
      ∑ i : Fin n,
          (mutualInfo (converseJointInline h_meas c)
            (fun ω => c.encoder ω.1 i) (fun ω => ω.2 i)).toReal
        = (∑ i : Fin n, InformationTheory.Shannon.differentialEntropy
              ((converseJointInline h_meas c).map (fun ω => ω.2 i))) - (n : ℝ) * h := by
    rw [Finset.sum_congr rfl (fun i _ => perLetterMI_decomp hN h_meas c i)]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Combine.
  rw [h_sum_perletter]
  calc
    (mutualInfo (converseJointInline h_meas c) (fun ω => c.encoder ω.1) Prod.snd).toReal
        ≤ (mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd).toReal := h_lhs_le
    _ = InformationTheory.Shannon.jointDifferentialEntropyPi (blockYLawInline h_meas c)
          - (n : ℝ) * h := h_block
    _ ≤ (∑ i : Fin n, InformationTheory.Shannon.differentialEntropy
            ((converseJointInline h_meas c).map (fun ω => ω.2 i))) - (n : ℝ) * h := by
        gcongr

/-! ### Wall 6 — `awgn-converse-markov-regularity` (Route B, L-AWGNM5-1-α) -/

/-- **Markov chain `W → encoder ∘ W → Y^n` factorization** (旧 `MarkovChainForConverse`).

`IsMarkovChain (converseJointInline h_meas c) Prod.fst (encoder ∘ fst) Prod.snd` の γ-form
joint factorization, **genuine closure** (旧 wall `awgn-converse-markov-regularity` は
真の Mathlib 不在ではなく deterministic-encoder factorization の plumbing 過大評価だった)。

証明骨子: 基本恒等式 `μ = (μ.map fst) ⊗ₘ (W.comap encoder)` (message-space marginal、
`W := Channel.toBlock (awgnChannel N) n` は noise block kernel) を mixture-of-diracs 上で
`ext_of_lintegral` により確立 (`h_marginalA`)。これから `condDistrib Yo Zc μ =ᵐ W`
(`condDistrib_ae_eq_of_measure_eq_compProd`) を導き、`condDistrib Xs Zc μ` を
`compProd_map_condDistrib` で吸収、triple-joint factorization を `ext_of_lintegral` +
`h_marginalA` reduction で検証する (precedent:
`BlockwiseChannel.isMarkovChain_per_letter_input`)。`#print axioms` は sorryAx-free
(`[propext, Classical.choice, Quot.sound]`、本 session 機械確認)。
@audit:ok -/
@[entry_point]
theorem awgnConverseMarkov_holds
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsMarkovChain (converseJointInline h_meas c)
      (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
      (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1)
      (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := by
  set μ : Measure (Fin M × (Fin n → ℝ)) := converseJointInline h_meas c with hμ_def
  -- The three RVs.
  set Xs : Fin M × (Fin n → ℝ) → Fin M := Prod.fst with hXs_def
  set Zc : Fin M × (Fin n → ℝ) → (Fin n → ℝ) := fun ω => c.encoder ω.1 with hZc_def
  set Yo : Fin M × (Fin n → ℝ) → (Fin n → ℝ) := Prod.snd with hYo_def
  -- The noise block kernel `W^{⊗n}` of the AWGN channel.
  set W : Kernel (Fin n → ℝ) (Fin n → ℝ) :=
    ChannelCoding.Channel.toBlock (awgnChannel N h_meas) n with hW_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  -- Measurability of the three RVs.
  have hXs_meas : Measurable Xs := measurable_fst
  have hZc_meas : Measurable Zc := by
    rw [hZc_def]; exact (Measurable.of_discrete).comp measurable_fst
  have hYo_meas : Measurable Yo := measurable_snd
  have hg_meas : Measurable c.encoder := Measurable.of_discrete
  -- `W.comap encoder`: the channel kernel reindexed from message to codeword.
  set Wg : Kernel (Fin M) (Fin n → ℝ) := W.comap c.encoder hg_meas with hWg_def
  -- **Fundamental message-space marginal (A)**: `μ = (μ.map Xs) ⊗ₘ (W.comap encoder)`.
  -- Since `(Xs ω, Yo ω) = ω`, this says the converse joint factors as
  -- `uniform(W) ⊗ₘ (∏ᵢ awgnChannel (encoder · i))`. Proved by `ext_of_lintegral` on the
  -- mixture-of-diracs.
  -- `μ.map Xs = (1/M) • ∑ₘ δ_m` (uniform message law).
  have h_map_Xs : μ.map Xs
      = ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) • ∑ m : Fin M, (Measure.dirac m) := by
    rw [hμ_def, hXs_def, converseJointInline]
    rw [Measure.map_smul]
    congr 1
    rw [Measure.map_finset_sum (measurable_fst.aemeasurable)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Measure.map_fst_prod]
    simp
  have h_marginalA : μ = (μ.map Xs) ⊗ₘ Wg := by
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    -- RHS via compProd, then h_map_Xs (do RHS first, before unfolding μ on LHS).
    rw [Measure.lintegral_compProd hf, h_map_Xs, lintegral_smul_measure,
      lintegral_finsetSum_measure]
    have hRHS_summand : ∀ m : Fin M,
        ∫⁻ a : Fin M, ∫⁻ y : Fin n → ℝ, f (a, y) ∂(Wg a) ∂(Measure.dirac m)
          = ∫⁻ y : Fin n → ℝ, f (m, y)
              ∂(Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))) := by
      intro m
      rw [lintegral_dirac]
      rfl
    simp_rw [hRHS_summand]
    -- LHS over the mixture.
    rw [hμ_def, converseJointInline, lintegral_smul_measure,
      lintegral_finsetSum_measure]
    have hLHS_summand : ∀ m : Fin M,
        ∫⁻ ω : Fin M × (Fin n → ℝ), f ω
            ∂((Measure.dirac m).prod
              (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))))
          = ∫⁻ y : Fin n → ℝ, f (m, y)
              ∂(Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))) := by
      intro m
      rw [lintegral_prod _ hf.aemeasurable, lintegral_dirac]
    simp_rw [hLHS_summand]
  -- `μ.map Zc = (1/M) • ∑ₘ δ_(encoder m)` (codeword law).
  have h_map_Zc : μ.map Zc
      = ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) • ∑ m : Fin M, (Measure.dirac (c.encoder m)) := by
    have hZc_comp : Zc = c.encoder ∘ Xs := rfl
    rw [hZc_comp, ← Measure.map_map Measurable.of_discrete hXs_meas, h_map_Xs,
      Measure.map_smul]
    congr 1
    rw [Measure.map_finset_sum' Measurable.of_discrete.aemeasurable]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Measure.map_dirac' Measurable.of_discrete]
  -- Linchpin marginal: `μ.map (Zc, Yo) = (μ.map Zc) ⊗ₘ W`.
  have h_pair_eq : μ.map (fun ω => (Zc ω, Yo ω)) = (μ.map Zc) ⊗ₘ W := by
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    -- RHS via compProd + h_map_Zc.
    rw [Measure.lintegral_compProd hf, h_map_Zc, lintegral_smul_measure,
      lintegral_finsetSum_measure]
    have hRHS_summand : ∀ m : Fin M,
        ∫⁻ z : Fin n → ℝ, ∫⁻ y : Fin n → ℝ, f (z, y) ∂(W z) ∂(Measure.dirac (c.encoder m))
          = ∫⁻ y : Fin n → ℝ, f (c.encoder m, y)
              ∂(Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))) := by
      intro m
      rw [lintegral_dirac' _
        (Measurable.lintegral_kernel_prod_right' (κ := W) hf)]
      rfl
    simp_rw [hRHS_summand]
    -- LHS over the mixture.
    rw [lintegral_map hf (hZc_meas.prodMk hYo_meas), hμ_def, converseJointInline,
      lintegral_smul_measure, lintegral_finsetSum_measure]
    have hLHS_summand : ∀ m : Fin M,
        ∫⁻ ω : Fin M × (Fin n → ℝ), f (Zc ω, Yo ω)
            ∂((Measure.dirac m).prod
              (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))))
          = ∫⁻ y : Fin n → ℝ, f (c.encoder m, y)
              ∂(Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))) := by
      intro m
      rw [lintegral_prod (fun ω : Fin M × (Fin n → ℝ) => f (Zc ω, Yo ω))
        (hf.comp (hZc_meas.prodMk hYo_meas)).aemeasurable, lintegral_dirac]
    simp_rw [hLHS_summand]
  -- Identify `condDistrib Yo Zc μ =ᵐ[μ.map Zc] W`.
  haveI : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc_meas.aemeasurable
  have hK_Y_eq : condDistrib Yo Zc μ =ᵐ[μ.map Zc] W :=
    condDistrib_ae_eq_of_measure_eq_compProd Zc hYo_meas.aemeasurable h_pair_eq
  -- Unfold IsMarkovChain and substitute condDistrib Yo Zc → W on the RHS.
  unfold IsMarkovChain
  set K_X : Kernel (Fin n → ℝ) (Fin M) := condDistrib Xs Zc μ with hK_X_def
  have h_compProd_eq :
      (μ.map Zc) ⊗ₘ (K_X ×ₖ condDistrib Yo Zc μ) = (μ.map Zc) ⊗ₘ (K_X ×ₖ W) := by
    refine Measure.compProd_congr ?_
    filter_upwards [hK_Y_eq] with a ha
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, ha]
  rw [h_compProd_eq]
  -- Triple-joint factorization via ext_of_lintegral.
  have h_LHS_meas : Measurable (fun ω => (Zc ω, Xs ω, Yo ω)) :=
    hZc_meas.prodMk (hXs_meas.prodMk hYo_meas)
  -- `compProd_map_condDistrib`: fold K_X back into `μ.map (Zc, Xs)`.
  have hKX_fold : (μ.map Zc) ⊗ₘ K_X = μ.map (fun ω => (Zc ω, Xs ω)) :=
    compProd_map_condDistrib (μ := μ) (X := Zc) (Y := Xs) hXs_meas.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  -- LHS: ∫⁻ ω, f (Zc ω, Xs ω, Yo ω) ∂μ.
  rw [lintegral_map hf h_LHS_meas]
  -- RHS: unfold the outer compProd over (μ.map Zc), then the inner product kernel.
  rw [Measure.lintegral_compProd hf]
  -- RHS inner: ∫⁻ p ∂((K_X ×ₖ W) z), f (z, p.1, p.2)
  --          = ∫⁻ x ∂(K_X z), ∫⁻ y ∂(W z), f (z, x, y).
  have h_inner_split : ∀ z : Fin n → ℝ,
      ∫⁻ p : Fin M × (Fin n → ℝ), f (z, p.1, p.2) ∂((K_X ×ₖ W) z)
        = ∫⁻ x : Fin M, ∫⁻ y : Fin n → ℝ, f (z, x, y) ∂(W z) ∂(K_X z) := by
    intro z
    rw [Kernel.prod_apply]
    rw [lintegral_prod (fun p : Fin M × (Fin n → ℝ) => f (z, p.1, p.2))
      (hf.comp (measurable_const.prodMk
        (measurable_fst.prodMk measurable_snd))).aemeasurable]
  simp_rw [h_inner_split]
  -- Define G (z, x) := ∫⁻ y ∂(W z), f (z, x, y), so RHS = ∫⁻ z ∂(μ.map Zc), ∫⁻ x ∂(K_X z), G (z, x).
  set G : (Fin n → ℝ) × Fin M → ℝ≥0∞ :=
    fun p => ∫⁻ y : Fin n → ℝ, f (p.1, p.2, y) ∂(W p.1) with hG_def
  have hG_meas : Measurable G := by
    let K' : Kernel ((Fin n → ℝ) × Fin M) (Fin n → ℝ) :=
      W.comap (Prod.fst : (Fin n → ℝ) × Fin M → (Fin n → ℝ)) measurable_fst
    have h_eq_K' : G = fun p : (Fin n → ℝ) × Fin M =>
        ∫⁻ y : Fin n → ℝ, f (p.1, p.2, y) ∂(K' p) := by
      funext p; simp [G, K', Kernel.comap_apply]
    rw [h_eq_K']
    exact Measurable.lintegral_kernel_prod_right' (κ := K')
      (f := fun pp : ((Fin n → ℝ) × Fin M) × (Fin n → ℝ) => f (pp.1.1, pp.1.2, pp.2))
      (hf.comp (((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  have h_RHS_is_G : ∀ z : Fin n → ℝ, ∀ x : Fin M,
      ∫⁻ y : Fin n → ℝ, f (z, x, y) ∂(W z) = G (z, x) := fun _ _ => rfl
  simp_rw [h_RHS_is_G]
  -- RHS = ∫⁻ z ∂(μ.map Zc), ∫⁻ x ∂(K_X z), G (z, x) = ∫⁻ p ∂((μ.map Zc) ⊗ₘ K_X), G p.
  rw [← Measure.lintegral_compProd hG_meas, hKX_fold]
  -- RHS = ∫⁻ p ∂(μ.map (Zc, Xs)), G p = ∫⁻ ω ∂μ, G (Zc ω, Xs ω).
  rw [lintegral_map hG_meas (hZc_meas.prodMk hXs_meas)]
  -- Now goal: ∫⁻ ω, f (Zc ω, Xs ω, Yo ω) ∂μ = ∫⁻ ω, G (Zc ω, Xs ω) ∂μ.
  rw [← hμ_def]
  -- Reduce any `∫⁻ ω, H ω ∂μ` through message-space marginal (A).
  have h_reduce : ∀ H : Fin M × (Fin n → ℝ) → ℝ≥0∞, Measurable H →
      ∫⁻ ω, H ω ∂μ
        = ∫⁻ a : Fin M, ∫⁻ y : Fin n → ℝ, H (a, y) ∂(Wg a) ∂(μ.map Xs) := by
    intro H hH
    conv_lhs => rw [h_marginalA]
    rw [Measure.lintegral_compProd hH]
  rw [h_reduce (fun ω => f (Zc ω, Xs ω, Yo ω)) (hf.comp h_LHS_meas),
    h_reduce (fun ω => G (Zc ω, Xs ω)) (hG_meas.comp (hZc_meas.prodMk hXs_meas))]
  -- Both inner integrals over `Wg a`. For each message `a`:
  refine lintegral_congr fun a => ?_
  have hWg_eq : Wg a = W (c.encoder a) := by rw [hWg_def, Kernel.comap_apply]
  haveI : IsProbabilityMeasure (Wg a) := by rw [hWg_eq]; infer_instance
  -- LHS inner: ∫⁻ y ∂(Wg a), f (encoder a, a, y).  `(Zc (a,y), Xs (a,y), Yo (a,y)) = (encoder a, a, y)`.
  -- RHS inner: ∫⁻ y ∂(Wg a), G (encoder a, a), constant in y, value `∫⁻ y' ∂(W (encoder a)), f (encoder a, a, y')`.
  have hRHS_eval : (fun y : Fin n → ℝ => G (Zc (a, y), Xs (a, y)))
      = (fun _ : Fin n → ℝ => ∫⁻ y' : Fin n → ℝ, f (c.encoder a, a, y') ∂(Wg a)) := by
    funext y
    show G (c.encoder a, a) = _
    rw [hG_def, hWg_eq]
  rw [hRHS_eval, lintegral_const, measure_univ, mul_one]

end InformationTheory.Shannon.AWGN

import Common2026.Shannon.FisherInfoV2DeBruijnPerTime
import Common2026.Shannon.FisherConvBound   -- shared 壁 gaussianConv_fisher_le_inv_var
import Common2026.Shannon.EPIConvDensitySecondDeriv  -- STEP-D bridge convDensityAdd_deriv2_eq_gaussian
import Common2026.Shannon.EntropyConvFinite  -- entropy-finiteness wall (log-factor integrands)

/-!
# per-time de Bruijn identity — Phase 5 capstone assembly

`debruijnIdentityV2_holds` (`FisherInfoV2DeBruijn.lean`,
`@residual(plan:epi-debruijn-pertime-closure)`) を一般 `X` で genuine 化する
**Phase 5 assembly** (`epi-debruijn-pertime-closure-plan.md` §Phase 5 詳細設計 §5C)。

## import cycle 回避 (新 file 方式)

`FisherInfoV2DeBruijnPerTime.lean` (atom 供給元) は
`import Common2026.Shannon.FisherInfoV2DeBruijn` している (atom が wall file の
`gaussianConvolution` 等を使うため)。assembly は逆に atom を使うので、
`FisherInfoV2DeBruijn.lean` の `debruijnIdentityV2_holds` body に直接書くと **import 循環**。
→ 本 file (`FisherInfoV2DeBruijnAssembly.lean`) を atom file の下流に置き
(`import FisherInfoV2DeBruijnPerTime` 合法、循環なし)、ここで同 signature の genuine theorem
`debruijnIdentityV2_holds_assembled` を証明する。元の `debruijnIdentityV2_holds` は wall
sorry のまま残し、本 file の `_assembled` が genuine 版 (plan §運用ルール「import cycle 注意」
第一選択)。

## assembly 7 段 (plan §5C)

`debruijnIdentityV2_holds_assembled` body を 6 genuine atom で組む:

1. **density 同定** (`pPath_eq_convDensityAdd`、`h_reg.pX`/`pX_law` 等) +
   `density_t_eq` (rnDeriv pin) + `toReal_ofReal` で `density_t =ᵐ pPath t`。
2. **entropy = ∫ negMulLog pPath** (`differentialEntropy_eq_integral_density`)。
3. **parametric diff** (`entropy_hasDerivAt_via_parametric`)。
4. **heat eq** (`heatFlow_density_heat_equation`、∂_σ pPath = (1/2)∂²_x pPath)。
5. **IBP** (`debruijn_ibp_step`)。
6. **fisher congr** (`fisher_from_logDeriv`)。
7. **最終 congr** で RHS を `(1/2)*fisherInfoOfDensityReal h_reg.density_t` に一致。

## 残 regularity gap (named private lemma に factor out、honest sorry)

各 atom は genuine だが、atom を呼ぶための具体的 regularity discharge (Gaussian-tail
domination の `Integrable`、被積分関数 ae-measurability、`tsupport` 全域 C¹、chain-rule
plumbing) は PR 級 (plan §5C 表 L-PT-γ/δ + §5B-4)。これらは named private lemma に分離し
`sorry` + `@residual(plan:epi-debruijn-pertime-closure)` で残す (monolithic wall →
構造化 + 名前付き regularity gap)。**仮説束化・load-bearing 禁止** — gap lemma は全て
regularity precondition (被積分関数の微分・有界性・可測性) であって結論 (`HasDerivAt` /
heat eq) を bundle しない。
-/

namespace Common2026.Shannon.FisherInfoV2

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal

open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAddDeriv)

variable {Ω : Type*} {_mΩ : MeasurableSpace Ω}

/-! ## §5C assembly — `debruijnIdentityV2_holds_assembled`

下記 named private lemma は assembly が各 atom を呼ぶための regularity/chain plumbing。
全て honest sorry (`@residual(plan:epi-debruijn-pertime-closure)`)、本来証明したい形を保つ。
-/

/-! ## §5G `_chain` sub-lemma split (plan §Phase 5-G)

`debruijnIdentityV2_holds_assembled_chain` (段 2-7) is factored into 5 named sub-lemmas
so the genuine plumbing (chain rule / atom composition) is separated from the true
remaining cost (Gaussian-tail domination integrability + full-support C¹ + log-tail
integrable majorant). All hyps are pX-system regularity + integrand-level
domination/integrability/measurability; no `HasDerivAt`/Fisher/heat-eq conclusion is
bundled into a hypothesis (load-bearing forbidden, plan §5G honesty constraint).

Convention: `pPath σ x := convDensityAdd pX (gaussianPDFReal 0 ⟨σ,_⟩) x`. -/

/-- **§5G-1: per-`x` entropy-integrand chain rule.**
At `x` with `pPath t x ≠ 0`, `(d/ds) negMulLog (pPath s x)|_{s=t} = (- log (pPath t x) - 1) · D`
where `D` is the σ-derivative `∂_s pPath t x`, supplied as the `HasDerivAt` witness.

`hpos` (positivity at `t`) is a regularity precondition needed by `Real.hasDerivAt_negMulLog`;
`hpath_deriv` is the σ-derivative of the *integrand* `fun s => pPath s x` (integrand-level
regularity from `heatFlow_density_heat_equation`). The composed `HasDerivAt` conclusion is
the genuine claim, derived via `HasDerivAt.comp` — NOT bundled into a hypothesis.

Independent honesty audit (2026-05-31, fresh auditor, §5G split commit `8906b5c`): verdict
ok. 0 local sorry; `#print axioms` confirms `[propext, Classical.choice, Quot.sound]` only
(sorryAx-free). `hpos` is a positivity precondition required by `hasDerivAt_negMulLog`;
`hpath_deriv` is an integrand-level σ-derivative `HasDerivAt` witness — neither bundles the
composed conclusion (core-reconstruction test: granting both does not hand over the chain-rule
composite value `(-log p - 1)·D`, which `hneg.comp t hpath_deriv` genuinely derives). NOT
circular, NOT load-bearing. proof-done. @audit:ok -/
private theorem debruijnIdentityV2_holds_assembled_chain_entDeriv_formula
    (pX : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) (D : ℝ)
    (hpos : convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x ≠ 0)
    (hpath_deriv : HasDerivAt
      (fun s : ℝ => convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) D t) :
    HasDerivAt
      (fun s : ℝ => Real.negMulLog
        (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x))
      ((- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1) * D)
      t := by
  -- the inner path value at `t` is `pPath t x` (since `max t 0 = t`).
  have hmaxt : (⟨max t 0, le_max_right t 0⟩ : ℝ≥0) = ⟨t, ht.le⟩ := by
    apply NNReal.eq; exact max_eq_left ht.le
  -- `negMulLog` is differentiable at `pPath t x ≠ 0`, with derivative `-log(pPath t x) - 1`.
  have hneg : HasDerivAt Real.negMulLog
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
      (convDensityAdd pX (gaussianPDFReal 0 ⟨max t 0, le_max_right t 0⟩) x) := by
    rw [hmaxt]
    exact Real.hasDerivAt_negMulLog hpos
  -- chain rule: `negMulLog ∘ (fun s => pPath s x)`.
  exact hneg.comp t hpath_deriv

/-- **Genuine integrability helper**: `x ↦ x^k · exp(-b·x²)` is Lebesgue integrable for any
`k : ℕ` and `b > 0`. Bridges the Mathlib `rpow` lemma `integrable_rpow_mul_exp_neg_mul_sq`
(which uses `x ^ (k:ℝ)`) to the `pow` (`ℕ`-exponent) form via `rpow_natCast`.

Independent honesty audit (2026-05-31, fresh auditor, §5G-2 wiring commit `cf88267`): verdict
ok. 0 sorry; `#print axioms` confirms `[propext, Classical.choice, Quot.sound]` only
(sorryAx-free). The bridge is genuine: `integrable_rpow_mul_exp_neg_mul_sq` exists in Mathlib
(`Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`, loogle confirmed), and the body
is a `rpow_natCast` `funext`/`rwa` rewrite from `x^(k:ℝ)` to `x^k`. NOT circular, NOT
degenerate. proof-done. @audit:ok -/
private theorem integrable_natPow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) volume := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hrpow := integrable_rpow_mul_exp_neg_mul_sq hb hk
  -- bridge `x ^ (k:ℝ)` (rpow) to `x ^ k` (pow): equal everywhere by `Real.rpow_natCast`.
  have hcongr : (fun x : ℝ => x ^ (k : ℝ) * Real.exp (-b * x ^ 2))
      = fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2) := by
    funext x; rw [Real.rpow_natCast]
  rwa [hcongr] at hrpow

/-- **Closed-form Gaussian pdf upper bound (genuine, Assembly-local).** The centered Gaussian
density is bounded above by its normalizing prefactor `(√(2πv))⁻¹` (since `exp` of a
nonpositive exponent is `≤ 1`). Re-proved here because the PerTime version is `private`.

Independent honesty audit (2026-05-31, commit `b53107a`): verdict ok. sorryAx-free
(`[propext, Classical.choice, Quot.sound]`). Genuine standalone re-proof (`exp` of nonpositive
exponent `≤ 1`), not an alias of the PerTime version. @audit:ok -/
private theorem gaussianPDFReal_le_prefactor' (v : ℝ≥0) (u : ℝ) :
    gaussianPDFReal 0 v u ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDFReal]
  have hpref_nn : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  have hexp_le : Real.exp (-(u - 0) ^ 2 / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (u - 0) ^ 2 / (2 * v) := by positivity
    linarith [neg_div (2 * (v : ℝ)) ((u - 0) ^ 2)]
  calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(u - 0) ^ 2 / (2 * v))
      ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp_le hpref_nn
    _ = (Real.sqrt (2 * Real.pi * v))⁻¹ := mul_one _

/-- **Convolution density upper bound (genuine, Assembly-local).** For a probability density
`pX` (`∫ pX = 1`), the convolution density `p_s x = ∫ pX y · g_s(x-y)` is bounded above by the
Gaussian prefactor `(√(2πs))⁻¹`, uniformly in `x`. (`p_s x ≤ ∫ pX y · prefactor =
prefactor · ∫ pX = prefactor`.) Used for the lower side of the GAP① `‖·‖` bound.

Independent honesty audit (2026-05-31, commit `b53107a`): verdict ok. sorryAx-free
(`[propext, Classical.choice, Quot.sound]`). `hpX_nn`/`hpX_int`/`hpX_mass` are regularity; the upper
bound is derived via `integral_mono` to the majorant `pX·pref` + `hpX_mass` (`∫(pX·pref)=pref·1`), NOT
assumed. @audit:ok -/
private theorem convDensityAdd_le_prefactor
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume)
    (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {s : ℝ} (hs : 0 < s) (x : ℝ) :
    convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x
      ≤ (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹ := by
  set pref : ℝ := (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹ with hpref
  have hpref_nn : 0 ≤ pref := by rw [hpref]; positivity
  -- integrand `F y := pX y * g_s(x-y)` integrable; majorant `pX y * pref` integrable.
  have hF_int : Integrable (fun y => pX y * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y)) volume := by
    refine hpX_int.mul_bdd (c := pref) ?_ ?_
    · exact ((measurable_gaussianPDFReal 0 ⟨s, hs.le⟩).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 _ (x - y))]
      exact gaussianPDFReal_le_prefactor' ⟨s, hs.le⟩ (x - y)
  have hmaj_int : Integrable (fun y => pX y * pref) volume := hpX_int.mul_const _
  -- `∫ F ≤ ∫ (pX · pref) = pref · ∫ pX = pref`.
  have hle : (∫ y, pX y * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y) ∂volume)
      ≤ ∫ y, pX y * pref ∂volume := by
    refine integral_mono hF_int hmaj_int (fun y => ?_)
    exact mul_le_mul_of_nonneg_left (gaussianPDFReal_le_prefactor' ⟨s, hs.le⟩ (x - y)) (hpX_nn y)
  rwa [integral_mul_const, hpX_mass, one_mul] at hle

/-- Monotonicity of the centered Gaussian pdf in `|·|` (Assembly-local re-proof of the
PerTime `private` version): if `|u| ≤ |w|` then `g_v(w) ≤ g_v(u)`.

Independent honesty audit (2026-05-31, commit `b53107a`): verdict ok. sorryAx-free
(`[propext, Classical.choice, Quot.sound]`). Genuine re-proof (monotone `exp` of `-u²/(2v)` in `|·|`,
`v=0` branch handled), not an alias. @audit:ok -/
private theorem gaussianPDFReal_antitone_abs'
    (v : ℝ≥0) {u w : ℝ} (huw : |u| ≤ |w|) :
    gaussianPDFReal 0 v w ≤ gaussianPDFReal 0 v u := by
  simp only [gaussianPDFReal, sub_zero]
  have hpref_nn : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpref_nn
  rw [Real.exp_le_exp]
  have hsq : u ^ 2 ≤ w ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg u) huw 2
    rwa [sq_abs, sq_abs] at this
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ 2 * v from by positivity) with hv0 | hvpos
  · rw [← hv0]; simp
  · rw [neg_div, neg_div, neg_le_neg_iff]; gcongr

/-- **Uniform-`R` Gaussian lower bound (genuine, Assembly-local).** A single tightness radius
`R > 0`, *independent of `s`*, with `(1/2)·g_s(|x|+R) ≤ convDensityAdd pX g_s x` for every
`s > 0` and `x`. The PerTime `convDensityAdd_lower_bound_gaussian` produces an `R` per `s`; for
the `s`-uniform GAP① majorant the same tightness radius (`∫_{[-R,R]} pX ≥ 1/2`, which depends
only on `pX`) must be reused across all `s`, so the tightness step is hoisted out and the per-`s`
box-drop + Gaussian-monotonicity argument is applied with the common `R`.

Independent honesty audit (2026-05-31, commit `b53107a`): verdict ok. sorryAx-free
(`[propext, Classical.choice, Quot.sound]`). The `s`-uniform tightness hoist is genuine: STEP 1
extracts a single `R` (depending only on `pX`) via `tendsto_setIntegral_of_monotone` over the monotone
`Icc(-n,n)` exhaustion (using `hpX_mass:∫pX=1` to identify the limit as 1), then STEPs 2-3 apply the
per-`s` box-drop + `gaussianPDFReal_antitone_abs'` with that common `R`. No circularity/degeneracy;
hyps are pX regularity, the lower bound is derived. @audit:ok -/
private theorem convDensityAdd_lower_bound_gaussian_uniformR
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume)
    (hpX_mass : (∫ y, pX y ∂volume) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ (s : ℝ) (hs : 0 < s) (x : ℝ),
      (1/2) * gaussianPDFReal 0 ⟨s, hs.le⟩ (|x| + R)
        ≤ convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x := by
  classical
  -- STEP 1 (tightness, `s`-independent): `∃ R > 0, ∫_{[-R,R]} pX ≥ 1/2`.
  obtain ⟨R, hR_pos, hR_mass⟩ :
      ∃ R : ℝ, 0 < R ∧ (1:ℝ)/2 ≤ ∫ y in Set.Icc (-R) R, pX y ∂volume := by
    set sN : ℕ → Set ℝ := fun n => Set.Icc (-(n:ℝ)) (n:ℝ) with hsN_def
    have hsN_meas : ∀ n, MeasurableSet (sN n) := fun n => measurableSet_Icc
    have hsN_mono : Monotone sN := by
      intro m n hmn
      apply Set.Icc_subset_Icc
      · exact neg_le_neg (by exact_mod_cast hmn)
      · exact_mod_cast hmn
    have hsN_union : (⋃ n, sN n) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      obtain ⟨n, hn⟩ := exists_nat_ge |y|
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      rw [hsN_def]; simp only [Set.mem_Icc]
      rw [abs_le] at hn; exact ⟨hn.1, hn.2⟩
    have hfi : IntegrableOn pX (⋃ n, sN n) volume := by
      rw [hsN_union]; exact hpX_int.integrableOn
    have htends := tendsto_setIntegral_of_monotone hsN_meas hsN_mono hfi
    rw [hsN_union, setIntegral_univ, hpX_mass] at htends
    have hev : ∀ᶠ n in Filter.atTop, (1:ℝ)/2 < ∫ y in sN n, pX y ∂volume :=
      htends.eventually (eventually_gt_nhds (by norm_num : (1:ℝ)/2 < 1))
    obtain ⟨N, hN⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
    refine ⟨(N:ℝ), by exact_mod_cast hN.2, ?_⟩
    rw [hsN_def] at hN; exact hN.1.le
  refine ⟨R, hR_pos, fun s hs x => ?_⟩
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨s, hs.le⟩ with hg_def
  -- integrand `F y := pX y * g (x - y)` nonnegative + integrable.
  set F : ℝ → ℝ := fun y => pX y * g (x - y) with hF_def
  have hF_nn : ∀ y, 0 ≤ F y := fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ (x - y))
  have hF_int : Integrable F volume := by
    refine hpX_int.mul_bdd (c := (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact ((measurable_gaussianPDFReal 0 ⟨s, hs.le⟩).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 _ (x - y))]
      exact gaussianPDFReal_le_prefactor' ⟨s, hs.le⟩ (x - y)
  -- STEP 2: drop the integral to the box `Icc (-R) R`.
  have hbox_le : (∫ y in Set.Icc (-R) R, F y ∂volume) ≤ ∫ y, F y ∂volume :=
    setIntegral_le_integral hF_int (Filter.Eventually.of_forall hF_nn)
  -- STEP 3: on the box, `g (x-y) ≥ g (|x| + R)`.
  have hbox_lb : (1/2) * g (|x| + R) ≤ ∫ y in Set.Icc (-R) R, F y ∂volume := by
    have hxR_nn : 0 ≤ |x| + R := add_nonneg (abs_nonneg x) hR_pos.le
    have hpt : ∀ y ∈ Set.Icc (-R) R, pX y * g (|x| + R) ≤ F y := by
      intro y hy
      have hy_abs : |x - y| ≤ |x| + R := by
        have h1 : |x - y| ≤ |x| + |y| := abs_sub _ _
        have h2 : |y| ≤ R := abs_le.mpr ⟨hy.1, hy.2⟩
        linarith
      have hmono : g (|x| + R) ≤ g (x - y) := by
        rw [hg_def]
        refine gaussianPDFReal_antitone_abs' ⟨s, hs.le⟩ ?_
        rwa [abs_of_nonneg hxR_nn]
      exact mul_le_mul_of_nonneg_left hmono (hpX_nn y)
    have hlb_int : IntegrableOn (fun y => pX y * g (|x| + R)) (Set.Icc (-R) R) volume :=
      hpX_int.integrableOn.mul_const _
    have hstep : (∫ y in Set.Icc (-R) R, pX y * g (|x| + R) ∂volume)
        ≤ ∫ y in Set.Icc (-R) R, F y ∂volume :=
      setIntegral_mono_on hlb_int hF_int.integrableOn measurableSet_Icc hpt
    rw [integral_mul_const] at hstep
    have hg_nn : 0 ≤ g (|x| + R) := by rw [hg_def]; exact gaussianPDFReal_nonneg 0 _ _
    have hhalf : g (|x| + R) * (1/2) ≤ g (|x| + R) * ∫ y in Set.Icc (-R) R, pX y ∂volume :=
      mul_le_mul_of_nonneg_left hR_mass hg_nn
    calc (1/2) * g (|x| + R)
        = g (|x| + R) * (1/2) := by ring
      _ ≤ g (|x| + R) * ∫ y in Set.Icc (-R) R, pX y ∂volume := hhalf
      _ = (∫ y in Set.Icc (-R) R, pX y ∂volume) * g (|x| + R) := by rw [mul_comm]
      _ ≤ ∫ y in Set.Icc (-R) R, F y ∂volume := hstep
  calc (1/2) * g (|x| + R)
      ≤ ∫ y in Set.Icc (-R) R, F y ∂volume := hbox_lb
    _ ≤ ∫ y, F y ∂volume := hbox_le
    _ = convDensityAdd pX g x := rfl

/-- **§5G-2a (GAP①): `s`-uniform polynomial majorant for the log factor — GENUINE (0 sorry).**
On the `t`-neighborhood `Set.Ioo (t/2) (2*t)` (where `t/2 < s`, hence `s > 0`), the entropy
log-factor `- log (p_s x) - 1` of the convolution density `p_s = convDensityAdd pX g_s` admits
a polynomial-in-`x²` majorant uniform in `s`:
`‖- log (p_s x) - 1‖ ≤ A + B·x²` with `B ≥ 0` (concretely `B = 2/t`).

**Closure (2026-05-31)**: now fully proved (was `sorry`). Two-sided `abs_le`:
- **upper** (`- log p_s x - 1 ≤ A + B·x²`): the `s`-uniform Gaussian lower bound
  `(1/2)·g_s(|x|+R) ≤ p_s x` (`convDensityAdd_lower_bound_gaussian_uniformR`, a single tightness
  radius `R` reused across all `s`) + `Real.log_le_log`, then the closed form
  `-log((1/2)g_s(|x|+R)) = log 2 + (1/2)log(2πs) + (|x|+R)²/(2s)`; on `s ∈ (t/2,2t)` use
  `(1/2)log(2πs) ≤ (1/2)log(4πt)` (`s<2t`) and `(|x|+R)²/(2s) ≤ (2x²+2R²)/t` (`s>t/2`,
  `(|x|+R)²≤2x²+2R²`).
- **lower** (`-(A+B·x²) ≤ - log p_s x - 1`): `p_s x ≤ (√(2πs))⁻¹` (`convDensityAdd_le_prefactor`,
  `g_s ≤ prefactor` + `∫pX=1`) ⇒ `-log p_s x ≥ (1/2)log(2πs) ≥ (1/2)log(πt)` (`s>t/2`), a constant
  lower bound absorbed by `A`. `p_s x > 0` from `convDensityAdd_pos` (uses `0 < ∫ pX`).
The route is "log of the lower bound" (`Real.log_le_log`+`Real.log_exp`), NOT `-log p ≤ p⁻¹-1`
(which would blow up as `exp(+x²)`).

`hpX_mass : ∫ pX = 1` is an honest probability-density regularity precondition (threaded from
`debruijnIdentityV2_holds_assembled`, supplied via `(P.map X) univ = 1`); it feeds
`convDensityAdd_lower_bound_gaussian_uniformR` / `_le_prefactor` / `_pos`. NOT load-bearing
(the majorant inequality is derived, not assumed). `B ≥ 0` and the existential output are genuine.

Independent honesty audit (2026-05-31, fresh auditor, GAP①+hpX_mass threading commit `b53107a`):
verdict ok (proof-done). `#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free,
transitive 0 sorry; the file's 4 remaining sorrys at GAP②/fisher/IBP-step/_chain_parametric are NOT
in this declaration's dependency cone). Signature honest: all hyps are pX-system regularity
(`hpX_nn`/`hpX_int`/`hpX_mass:∫pX=1`) + `ht`; `_hpX_meas` unused. core-reconstruction test: granting
all hyps does NOT hand over the majorant — it is derived by two-sided `abs_le` (upper via
`convDensityAdd_lower_bound_gaussian_uniformR` + `Real.log_le_log` + closed-form log expansion; lower
via `convDensityAdd_le_prefactor`). `hpX_mass` is consumed as genuine normalization (in `_le_prefactor`
`∫(pX·pref)=pref`, in `_uniformR` tightness `∫_{[-R,R]}pX≥1/2`, in `convDensityAdd_pos` positive mass) =
regularity precondition, NOT load-bearing. NOT circular/degenerate. proof-done.
@audit:ok -/
private theorem convDensityAdd_logFactor_poly_majorant
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (_hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {t : ℝ} (ht : 0 < t) :
    ∃ A B : ℝ, 0 ≤ B ∧
      ∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖- Real.log (convDensityAdd pX
            (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩) x) - 1‖
          ≤ A + B * x ^ 2 := by
  -- positive mass from `∫ pX = 1` (for `convDensityAdd_pos`).
  have hpX_pos : 0 < ∫ y, pX y ∂volume := by rw [hpX_mass]; norm_num
  -- `s`-uniform tightness radius `R > 0` and the Gaussian lower bound.
  obtain ⟨R, hR_pos, hLB⟩ :=
    convDensityAdd_lower_bound_gaussian_uniformR pX hpX_nn hpX_int hpX_mass
  -- constants for the two-sided bound (`B = 2/t`; `A` covers both the upper polynomial
  -- offset and the lower constant, uniform over `s ∈ Ioo (t/2, 2t)`).
  set A_up : ℝ := Real.log 2 + (1/2) * Real.log (4 * Real.pi * t) + 2 * R ^ 2 / t - 1 with hA_up
  set A_lo : ℝ := 1 - (1/2) * Real.log (Real.pi * t) with hA_lo
  refine ⟨max A_up A_lo, 2 / t, by positivity, ?_⟩
  -- the bound is pointwise in `x`, holds for every `x` (so trivially a.e.).
  refine Filter.Eventually.of_forall (fun x s hs => ?_)
  have hspos : (0:ℝ) < s := by have := hs.1; linarith
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨s, hspos.le⟩ with hg_def
  set p : ℝ := convDensityAdd pX g x with hp_def
  -- `p > 0` and a closed form for `log` of the Gaussian prefactor.
  have hp_pos : 0 < p := by
    rw [hp_def, hg_def]; exact convDensityAdd_pos pX hpX_nn hpX_int hpX_pos hspos x
  have h2pis_pos : (0:ℝ) < 2 * Real.pi * s := by positivity
  have hpref_pos : (0:ℝ) < (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹ := by positivity
  have hcoe : ((⟨s, hspos.le⟩ : ℝ≥0) : ℝ) = s := rfl
  -- `log pref_s = -(1/2)·log(2πs)`.
  have hlog_pref : Real.log (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹
      = -((1/2) * Real.log (2 * Real.pi * s)) := by
    rw [Real.log_inv, hcoe, Real.log_sqrt h2pis_pos.le]; ring
  -- ============ upper side: `- log p - 1 ≤ A_up + (2/t)·x²` ============
  have hxR_nn : (0:ℝ) ≤ |x| + R := add_nonneg (abs_nonneg x) hR_pos.le
  -- lower bound on `p`: `(1/2)·g(|x|+R) ≤ p`, and `(1/2)·g(|x|+R) > 0`.
  have hlb := hLB s hspos x
  rw [← hg_def, ← hp_def] at hlb
  have hg_xR_pos : 0 < g (|x| + R) := by
    rw [hg_def]; exact gaussianPDFReal_pos 0 _ _ (by
      intro h; exact hspos.ne' (congrArg NNReal.toReal h))
  have hhalf_pos : (0:ℝ) < (1/2) * g (|x| + R) := by positivity
  -- `log p ≥ log ((1/2)·g(|x|+R))`.
  have hlog_lb : Real.log ((1/2) * g (|x| + R)) ≤ Real.log p := Real.log_le_log hhalf_pos hlb
  -- closed form: `log((1/2)·g(|x|+R)) = log(1/2) + log pref_s - (|x|+R)²/(2s)`.
  -- proved via the defeq natural unfold (RHS keeps the `- 0` and NNReal cast verbatim),
  -- then reshaped by the `s`-form equation `hlog_reshape`.
  have hlog_nat : Real.log ((1/2) * g (|x| + R))
      = Real.log (1/2) + (Real.log ((Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹)
        + -(|x| + R - 0) ^ 2 / (2 * s)) := by
    rw [hg_def]
    simp only [gaussianPDFReal]
    rw [Real.log_mul (by norm_num) (ne_of_gt (by positivity)),
      Real.log_mul (ne_of_gt (by positivity)) (Real.exp_ne_zero _), Real.log_exp]
    rfl
  have hlog_half : Real.log ((1/2) * g (|x| + R))
      = Real.log (1/2) + Real.log (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹
        - (|x| + R) ^ 2 / (2 * s) := by
    rw [hlog_nat]; ring
  -- `(|x|+R)²/(2s) ≤ (2/t)·x² + 2R²/t` (using `s > t/2` and `2|x|R ≤ x²+R²`).
  have hquad : (|x| + R) ^ 2 / (2 * s) ≤ (2 / t) * x ^ 2 + 2 * R ^ 2 / t := by
    have h2s : t ≤ 2 * s := by have := hs.1; linarith
    have hnum : (|x| + R) ^ 2 ≤ 2 * x ^ 2 + 2 * R ^ 2 := by
      have hcross : 2 * |x| * R ≤ x ^ 2 + R ^ 2 := by
        nlinarith [sq_nonneg (|x| - R), sq_abs x]
      have hsplit : (|x| + R) ^ 2 = x ^ 2 + 2 * |x| * R + R ^ 2 := by
        rw [add_sq]; rw [sq_abs]
      rw [hsplit]; linarith
    calc (|x| + R) ^ 2 / (2 * s)
        ≤ (|x| + R) ^ 2 / t := div_le_div_of_nonneg_left (sq_nonneg _) ht h2s
      _ ≤ (2 * x ^ 2 + 2 * R ^ 2) / t := div_le_div_of_nonneg_right hnum ht.le
      _ = (2 / t) * x ^ 2 + 2 * R ^ 2 / t := by ring
  -- `(1/2)·log(2πs) ≤ (1/2)·log(4πt)` (using `s < 2t`).
  have hlog_2pis_up : (1/2) * Real.log (2 * Real.pi * s) ≤ (1/2) * Real.log (4 * Real.pi * t) := by
    have hle : 2 * Real.pi * s ≤ 4 * Real.pi * t := by
      have := hs.2; nlinarith [Real.pi_pos]
    have := Real.log_le_log h2pis_pos hle; linarith
  -- assemble the upper bound: `- log p ≤ log 2 + (1/2)log(2πs) + (|x|+R)²/(2s)`.
  have hupper : - Real.log p - 1 ≤ max A_up A_lo + (2 / t) * x ^ 2 := by
    have hstep : - Real.log p
        ≤ Real.log 2 + (1/2) * Real.log (2 * Real.pi * s) + (|x| + R) ^ 2 / (2 * s) := by
      have := hlog_lb
      rw [hlog_half, hlog_pref] at this
      have hlog2 : Real.log (1/2) = - Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
      rw [hlog2] at this
      linarith
    have : - Real.log p - 1
        ≤ Real.log 2 + (1/2) * Real.log (4 * Real.pi * t) + ((2 / t) * x ^ 2 + 2 * R ^ 2 / t) - 1 :=
      by linarith [hquad, hlog_2pis_up]
    have hAup : A_up + (2 / t) * x ^ 2
        = Real.log 2 + (1/2) * Real.log (4 * Real.pi * t) + ((2 / t) * x ^ 2 + 2 * R ^ 2 / t) - 1 :=
      by rw [hA_up]; ring
    calc - Real.log p - 1
        ≤ Real.log 2 + (1/2) * Real.log (4 * Real.pi * t) + ((2 / t) * x ^ 2 + 2 * R ^ 2 / t) - 1 :=
          this
      _ = A_up + (2 / t) * x ^ 2 := hAup.symm
      _ ≤ max A_up A_lo + (2 / t) * x ^ 2 := by
          gcongr; exact le_max_left _ _
  -- ============ lower side: `-(A + (2/t)x²) ≤ - log p - 1` ============
  -- `p ≤ pref_s` ⇒ `log p ≤ log pref_s = -(1/2)log(2πs)` ⇒ `- log p ≥ (1/2)log(2πs)`.
  have hp_le := convDensityAdd_le_prefactor pX hpX_nn hpX_int hpX_mass hspos x
  rw [← hg_def, ← hp_def] at hp_le
  have hlog_p_up : Real.log p ≤ -((1/2) * Real.log (2 * Real.pi * s)) := by
    have := Real.log_le_log hp_pos hp_le
    rwa [hlog_pref] at this
  -- `(1/2)log(πt) ≤ (1/2)log(2πs)` (using `2πs > πt`, i.e. `s > t/2`).
  have hlog_lo : (1/2) * Real.log (Real.pi * t) ≤ (1/2) * Real.log (2 * Real.pi * s) := by
    have hpit_pos : (0:ℝ) < Real.pi * t := by positivity
    have hle : Real.pi * t ≤ 2 * Real.pi * s := by
      have := hs.1; nlinarith [Real.pi_pos]
    have := Real.log_le_log hpit_pos hle; linarith
  have hlower : -(max A_up A_lo + (2 / t) * x ^ 2) ≤ - Real.log p - 1 := by
    -- `- log p ≥ (1/2)log(2πs) ≥ (1/2)log(πt)`, so `- log p - 1 ≥ (1/2)log(πt) - 1 = -A_lo`.
    have hge : (1/2) * Real.log (Real.pi * t) ≤ - Real.log p := by linarith [hlog_p_up, hlog_lo]
    have hAlo : -A_lo ≤ - Real.log p - 1 := by rw [hA_lo]; linarith
    have hnonpos : (0:ℝ) ≤ (2 / t) * x ^ 2 := by positivity
    calc -(max A_up A_lo + (2 / t) * x ^ 2)
        ≤ - max A_up A_lo := by linarith
      _ ≤ - A_lo := by apply neg_le_neg (le_max_right _ _)
      _ ≤ - Real.log p - 1 := hAlo
  -- combine into the `‖·‖` bound.
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨hlower, hupper⟩

/-! ### §5G-2b helpers — the `s`-uniform Gaussian-Hessian majorant `gaussHessMaj t`

The `s`-uniform kernel majorant on the window `s ∈ (t/2, 2t)`:
`g_s(u)·|u²/s² − 1/s| ≤ gaussHessMaj t u := (√(πt))⁻¹·exp(−u²/(4t))·(4u²/t² + 2/t)`.
The prefactor `(2πs)^(−1/2)` is decreasing in `s` (min at `s = t/2` ⇒ `(πt)^(−1/2)`); the
exponent `exp(−u²/(2s))` is increasing in `s` (`2s ≤ 4t` ⇒ `exp(−u²/(4t))`); the polynomial
factor `|u²/s² − 1/s| ≤ u²/s² + 1/s ≤ 4u²/t² + 2/t` (`s ≥ t/2`). `gaussHessMaj t` is a
Gaussian × quadratic, hence Lebesgue-integrable. This is the genuine `s`-uniform pointwise
envelope feeding GAP②'s triangle inequality. -/

/-- The `s`-uniform Gaussian-Hessian kernel majorant on the window `s ∈ (t/2, 2t)`.
Independent honesty audit (2026-05-31, fresh auditor, Wave 3 commit `b5b9360`): genuine def,
not load-bearing (the consumer `convDensityAdd_deriv2_poly_moment_majorant` builds its envelope
as a convolution against this kernel; the kernel is a plain Gaussian×quadratic, no claim bundled).
@audit:ok -/
private noncomputable def gaussHessMaj (t : ℝ) (u : ℝ) : ℝ :=
  (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2 + 2 / t)

/-- `gaussHessMaj t` is nonnegative.
@audit:ok -/
private theorem gaussHessMaj_nonneg {t : ℝ} (ht : 0 < t) (u : ℝ) : 0 ≤ gaussHessMaj t u := by
  unfold gaussHessMaj
  have h1 : (0:ℝ) ≤ (Real.sqrt (Real.pi * t))⁻¹ := by positivity
  have h2 : (0:ℝ) ≤ Real.exp (-u ^ 2 / (4 * t)) := (Real.exp_pos _).le
  have h3 : (0:ℝ) ≤ 4 * u ^ 2 / t ^ 2 + 2 / t := by positivity
  positivity

/-- `gaussHessMaj t` is globally bounded (Gaussian decay kills the quadratic).
Used to prove `Integrable (fun y => pX y · gaussHessMaj t (x − y))` via `Integrable.mul_bdd`.

Independent honesty audit (2026-05-31, Wave 4, fresh auditor): verdict **ok**. Bound
`(√(πt))⁻¹·(16e⁻¹/t + 2/t)` is a genuine global sup: the body bounds `u²·exp(−u²/4t) ≤ 4t·e⁻¹`
via `Real.mul_exp_neg_le_exp_neg_one` and `exp(−u²/4t) ≤ 1`, so
`exp·(4u²/t² + 2/t) ≤ 16e⁻¹/t + 2/t` — mathematically sound. `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-verified). Single hyp `0<t`
regularity; conclusion not load-bearing.
@audit:ok -/
private theorem gaussHessMaj_bdd {t : ℝ} (ht : 0 < t) :
    ∀ u : ℝ, gaussHessMaj t u
      ≤ (Real.sqrt (Real.pi * t))⁻¹ * (16 * Real.exp (-1) / t + 2 / t) := by
  intro u
  unfold gaussHessMaj
  set P : ℝ := (Real.sqrt (Real.pi * t))⁻¹ with hP
  have hP_nn : (0:ℝ) ≤ P := by rw [hP]; positivity
  have hexp_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (4 * t)) := (Real.exp_pos _).le
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hP_nn
  -- `u²·exp(-u²/(4t)) ≤ 4t·exp(-1)` via `mul_exp_neg_le_exp_neg_one (u²/(4t))`.
  have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (4 * t))
  have hexp_eq : Real.exp (-(u ^ 2 / (4 * t))) = Real.exp (-u ^ 2 / (4 * t)) := by congr 1; ring
  rw [hexp_eq] at hmul
  have h4t : (0:ℝ) < 4 * t := by linarith
  have hu2 : u ^ 2 * Real.exp (-u ^ 2 / (4 * t)) ≤ 4 * t * Real.exp (-1) := by
    have hmul' := mul_le_mul_of_nonneg_left hmul h4t.le
    have heq : (4 * t) * ((u ^ 2 / (4 * t)) * Real.exp (-u ^ 2 / (4 * t)))
        = u ^ 2 * Real.exp (-u ^ 2 / (4 * t)) := by field_simp
    rw [heq] at hmul'; linarith [hmul']
  have hexp_le1 : Real.exp (-u ^ 2 / (4 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ u ^ 2 / (4 * t) := by positivity
    linarith [neg_div (4 * t) (u ^ 2)]
  -- `exp·(4u²/t²+2/t) = 4/t²·(u²·exp) + 2/t·exp ≤ 4/t²·4t·exp(-1) + 2/t = 16·exp(-1)/t + 2/t`.
  have ht1 : Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2) ≤ 16 * Real.exp (-1) / t := by
    have heq : Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2)
        = (4 / t ^ 2) * (u ^ 2 * Real.exp (-u ^ 2 / (4 * t))) := by ring
    rw [heq]
    have h4t2 : (0:ℝ) ≤ 4 / t ^ 2 := by positivity
    calc (4 / t ^ 2) * (u ^ 2 * Real.exp (-u ^ 2 / (4 * t)))
        ≤ (4 / t ^ 2) * (4 * t * Real.exp (-1)) :=
          mul_le_mul_of_nonneg_left hu2 h4t2
      _ = 16 * Real.exp (-1) / t := by rw [pow_two]; field_simp; ring
  have ht2 : Real.exp (-u ^ 2 / (4 * t)) * (2 / t) ≤ 2 / t := by
    have h2t : (0:ℝ) ≤ 2 / t := by positivity
    calc Real.exp (-u ^ 2 / (4 * t)) * (2 / t) ≤ 1 * (2 / t) := by gcongr
      _ = 2 / t := one_mul _
  calc Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2 + 2 / t)
      = Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2)
        + Real.exp (-u ^ 2 / (4 * t)) * (2 / t) := by ring
    _ ≤ 16 * Real.exp (-1) / t + 2 / t := by linarith [ht1, ht2]

/-- `gaussHessMaj t` is Lebesgue-integrable (Gaussian × quadratic).
Independent honesty audit (2026-05-31, fresh auditor, Wave 3 commit `b5b9360`): genuine,
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free). All hyps regularity.
@audit:ok -/
private theorem gaussHessMaj_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (gaussHessMaj t) volume := by
  have hb : (0:ℝ) < 1 / (4 * t) := by positivity
  -- the two Gaussian building blocks: `exp(-b u²)` and `|u|² · exp(-b u²)`.
  have hexp : Integrable (fun u : ℝ => Real.exp (-(1 / (4 * t)) * u ^ 2)) volume :=
    integrable_exp_neg_mul_sq hb
  have hsq : Integrable (fun u : ℝ => u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume := by
    have := integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1:ℝ) < 2)
    refine this.congr (Filter.Eventually.of_forall (fun u => ?_))
    simp only [Real.rpow_two]
  -- assemble `gaussHessMaj` as a linear combination of the two.
  have hcomb : Integrable
      (fun u : ℝ => (Real.sqrt (Real.pi * t))⁻¹ * (4 / t ^ 2)
            * (u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2))
          + (Real.sqrt (Real.pi * t))⁻¹ * (2 / t)
            * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume :=
    (hsq.const_mul _).add (hexp.const_mul _)
  refine hcomb.congr (Filter.Eventually.of_forall (fun u => ?_))
  -- pointwise: `gaussHessMaj t u = ` the combination.
  unfold gaussHessMaj
  have hexp_eq : Real.exp (-u ^ 2 / (4 * t)) = Real.exp (-(1 / (4 * t)) * u ^ 2) := by
    congr 1; field_simp
  rw [hexp_eq]; ring

/-- For any constants `a b : ℝ`, the polynomial-weighted Gaussian-Hessian majorant
`fun u => (a + b·u²)·gaussHessMaj t u` is Lebesgue-integrable. `gaussHessMaj t` is a
Gaussian × quadratic, so the weight `(a+b·u²)` raises it to a Gaussian × quartic — still
integrable via `integrable_rpow_mul_exp_neg_mul_sq` (the `u⁴` and `u²` Gaussian moments).
This is the kernel `G(u) = (a+b·u²)·gaussHessMaj t u` used by the joint-envelope Tonelli
route (`_chain_domination` first goal): the `x²`-weight `(A+B·x²)` of the log factor is split
via `x² ≤ 2(x−y)² + 2y²`, and the `(x−y)²` part absorbs into this polynomial-weighted kernel.

**Independent honesty audit (2026-05-31, Wave 5, commit `647015d`, fresh auditor): verdict ok.**
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free). Mathematically sound:
`(a+b·u²)·gaussHessMaj t u` is Gaussian × quartic, integrable via the u²/u⁴ Gaussian moments
(`integrable_rpow_mul_exp_neg_mul_sq`). Hyps `0<t` + free constants `a b` are regularity.
@audit:ok -/
private theorem gaussHessMaj_polyWeight_integrable {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    Integrable (fun u : ℝ => (a + b * u ^ 2) * gaussHessMaj t u) volume := by
  have hbpos : (0:ℝ) < 1 / (4 * t) := by positivity
  -- the three Gaussian moment building blocks: `exp`, `u²·exp`, `u⁴·exp`.
  have hexp : Integrable (fun u : ℝ => Real.exp (-(1 / (4 * t)) * u ^ 2)) volume :=
    integrable_exp_neg_mul_sq hbpos
  have hsq : Integrable (fun u : ℝ => u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume := by
    have := integrable_rpow_mul_exp_neg_mul_sq hbpos (by norm_num : (-1:ℝ) < 2)
    refine this.congr (Filter.Eventually.of_forall (fun u => ?_))
    simp only [Real.rpow_two]
  have hquart : Integrable (fun u : ℝ => u ^ 4 * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume := by
    have := integrable_rpow_mul_exp_neg_mul_sq hbpos (by norm_num : (-1:ℝ) < 4)
    refine this.congr (Filter.Eventually.of_forall (fun u => ?_))
    simp only []
    rw [show ((4:ℝ)) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  -- `(a+b·u²)·gaussHessMaj t u = c·exp·[(a + b·u²)·(4u²/t² + 2/t)]`
  --   = c·[ (4a/t² + 4b/t²·u² )·u² + (2a/t + 2b/t·u²) ]·exp  — a linear combo of exp, u²·exp, u⁴·exp.
  set c : ℝ := (Real.sqrt (Real.pi * t))⁻¹ with hc
  have hcomb : Integrable
      (fun u : ℝ =>
          c * (4 * b / t ^ 2) * (u ^ 4 * Real.exp (-(1 / (4 * t)) * u ^ 2))
        + (c * (4 * a / t ^ 2) + c * (2 * b / t))
            * (u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2))
        + c * (2 * a / t) * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume :=
    ((hquart.const_mul _).add (hsq.const_mul _)).add (hexp.const_mul _)
  refine hcomb.congr (Filter.Eventually.of_forall (fun u => ?_))
  simp only []
  unfold gaussHessMaj
  have hexp_eq : Real.exp (-u ^ 2 / (4 * t)) = Real.exp (-(1 / (4 * t)) * u ^ 2) := by
    congr 1; field_simp
  rw [hexp_eq, hc]; ring

/-- For nonneg constants `a b`, the polynomial-weighted Gaussian-Hessian majorant
`(a + b·u²)·gaussHessMaj t u` is globally bounded by an explicit constant.
`gaussHessMaj t` is a Gaussian × quadratic, so `(a+b·u²)·gaussHessMaj t u` is a Gaussian × quartic,
which decays to 0 at ±∞ (Gaussian wins). The bound uses `gaussHessMaj_bdd` for the `a·gaussHessMaj`
term and `u²·gaussHessMaj ≤ (√(πt))⁻¹·(256e⁻² + 8e⁻¹)` (from `u⁴·exp(-u²/4t) = (u²·exp(-u²/8t))²
≤ (8t·e⁻¹)²` and `u²·exp(-u²/4t) ≤ 4t·e⁻¹`, both via `mul_exp_neg_le_exp_neg_one`). Used to discharge
the per-`y` fibre integrability `Integrable (fun y => pX y · G(x−y))` (bounded kernel × integrable pX)
in the joint-envelope route II.

**Independent honesty audit (2026-05-31, Wave 5, commit `647015d`, fresh auditor): verdict ok.**
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free). Mathematically sound:
Gaussian × quartic decays to 0 at ±∞, global bound via `mul_exp_neg_le_exp_neg_one`. Hyps `0<t`,
`0≤a`, `0≤b` are regularity (nonneg constants needed for the bound direction).
@audit:ok -/
private theorem gaussHessMaj_polyWeight_bdd {t : ℝ} (ht : 0 < t) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ u : ℝ, (a + b * u ^ 2) * gaussHessMaj t u
      ≤ a * ((Real.sqrt (Real.pi * t))⁻¹ * (16 * Real.exp (-1) / t + 2 / t))
        + b * ((Real.sqrt (Real.pi * t))⁻¹ * (256 * Real.exp (-1) ^ 2 + 8 * Real.exp (-1))) := by
  intro u
  set P : ℝ := (Real.sqrt (Real.pi * t))⁻¹ with hP
  have hP_nn : (0:ℝ) ≤ P := by rw [hP]; positivity
  have hg_nn : (0:ℝ) ≤ gaussHessMaj t u := gaussHessMaj_nonneg ht u
  -- term `a·gaussHessMaj ≤ a·(P·(16e⁻¹/t+2/t))`.
  have hterm_a : a * gaussHessMaj t u ≤ a * (P * (16 * Real.exp (-1) / t + 2 / t)) :=
    mul_le_mul_of_nonneg_left (by rw [hP]; exact gaussHessMaj_bdd ht u) ha
  -- term `b·u²·gaussHessMaj ≤ b·(P·(256e⁻²+8e⁻¹))`.
  have hsqg : u ^ 2 * gaussHessMaj t u ≤ P * (256 * Real.exp (-1) ^ 2 + 8 * Real.exp (-1)) := by
    unfold gaussHessMaj
    rw [← hP]
    -- `u²·(P·exp(-u²/4t)·(4u²/t²+2/t)) = P·exp·(4u⁴/t² + 2u²/t)`.
    have h4t : (0:ℝ) < 4 * t := by linarith
    have h8t : (0:ℝ) < 8 * t := by linarith
    -- `u²·exp(-u²/4t) ≤ 4t·e⁻¹`.
    have hu2 : u ^ 2 * Real.exp (-u ^ 2 / (4 * t)) ≤ 4 * t * Real.exp (-1) := by
      have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (4 * t))
      have hexp_eq : Real.exp (-(u ^ 2 / (4 * t))) = Real.exp (-u ^ 2 / (4 * t)) := by
        congr 1; ring
      rw [hexp_eq] at hmul
      have hmul' := mul_le_mul_of_nonneg_left hmul h4t.le
      have heq : (4 * t) * ((u ^ 2 / (4 * t)) * Real.exp (-u ^ 2 / (4 * t)))
          = u ^ 2 * Real.exp (-u ^ 2 / (4 * t)) := by field_simp
      rw [heq] at hmul'; linarith [hmul']
    -- `u²·exp(-u²/8t) ≤ 8t·e⁻¹`, then square to get `u⁴·exp(-u²/4t) ≤ (8t·e⁻¹)²`.
    have hu2_8 : u ^ 2 * Real.exp (-u ^ 2 / (8 * t)) ≤ 8 * t * Real.exp (-1) := by
      have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (8 * t))
      have hexp_eq : Real.exp (-(u ^ 2 / (8 * t))) = Real.exp (-u ^ 2 / (8 * t)) := by
        congr 1; ring
      rw [hexp_eq] at hmul
      have hmul' := mul_le_mul_of_nonneg_left hmul h8t.le
      have heq : (8 * t) * ((u ^ 2 / (8 * t)) * Real.exp (-u ^ 2 / (8 * t)))
          = u ^ 2 * Real.exp (-u ^ 2 / (8 * t)) := by field_simp
      rw [heq] at hmul'; linarith [hmul']
    have hu2_8_nn : (0:ℝ) ≤ u ^ 2 * Real.exp (-u ^ 2 / (8 * t)) := by positivity
    have hsplit : Real.exp (-u ^ 2 / (8 * t)) * Real.exp (-u ^ 2 / (8 * t))
        = Real.exp (-u ^ 2 / (4 * t)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have hu4 : u ^ 4 * Real.exp (-u ^ 2 / (4 * t)) ≤ (8 * t * Real.exp (-1)) ^ 2 := by
      have hsq := mul_le_mul hu2_8 hu2_8 hu2_8_nn (by positivity)
      have heq : (u ^ 2 * Real.exp (-u ^ 2 / (8 * t))) * (u ^ 2 * Real.exp (-u ^ 2 / (8 * t)))
          = u ^ 4 * Real.exp (-u ^ 2 / (4 * t)) := by
        rw [show u ^ 4 = u ^ 2 * u ^ 2 by ring, ← hsplit]; ring
      rw [heq] at hsq
      calc u ^ 4 * Real.exp (-u ^ 2 / (4 * t)) ≤ (8 * t * Real.exp (-1)) * (8 * t * Real.exp (-1)) :=
            hsq
        _ = (8 * t * Real.exp (-1)) ^ 2 := by ring
    -- assemble: `P·exp·(4u⁴/t²+2u²/t) = P·(4/t²·(u⁴·exp) + 2/t·(u²·exp))`
    --   ≤ P·(4/t²·64t²e⁻² + 2/t·4t·e⁻¹) = P·(256e⁻²+8e⁻¹).
    have hexpr : u ^ 2 * (P * Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2 + 2 / t))
        = P * ((4 / t ^ 2) * (u ^ 4 * Real.exp (-u ^ 2 / (4 * t)))
              + (2 / t) * (u ^ 2 * Real.exp (-u ^ 2 / (4 * t)))) := by
      rw [show u ^ 4 = u ^ 2 * u ^ 2 by ring]; ring
    rw [hexpr]
    apply mul_le_mul_of_nonneg_left _ hP_nn
    have h4t2 : (0:ℝ) ≤ 4 / t ^ 2 := by positivity
    have h2t : (0:ℝ) ≤ 2 / t := by positivity
    have hb1 : (4 / t ^ 2) * (u ^ 4 * Real.exp (-u ^ 2 / (4 * t)))
        ≤ (4 / t ^ 2) * (8 * t * Real.exp (-1)) ^ 2 := mul_le_mul_of_nonneg_left hu4 h4t2
    have hb2 : (2 / t) * (u ^ 2 * Real.exp (-u ^ 2 / (4 * t)))
        ≤ (2 / t) * (4 * t * Real.exp (-1)) := mul_le_mul_of_nonneg_left hu2 h2t
    have heval1 : (4 / t ^ 2) * (8 * t * Real.exp (-1)) ^ 2 = 256 * Real.exp (-1) ^ 2 := by
      rw [pow_two]; field_simp; ring
    have heval2 : (2 / t) * (4 * t * Real.exp (-1)) = 8 * Real.exp (-1) := by
      field_simp; ring
    rw [heval1] at hb1; rw [heval2] at hb2
    linarith [hb1, hb2]
  have hterm_b : b * (u ^ 2 * gaussHessMaj t u)
      ≤ b * (P * (256 * Real.exp (-1) ^ 2 + 8 * Real.exp (-1))) :=
    mul_le_mul_of_nonneg_left hsqg hb
  calc (a + b * u ^ 2) * gaussHessMaj t u
      = a * gaussHessMaj t u + b * (u ^ 2 * gaussHessMaj t u) := by ring
    _ ≤ a * (P * (16 * Real.exp (-1) / t + 2 / t))
          + b * (P * (256 * Real.exp (-1) ^ 2 + 8 * Real.exp (-1))) := by
        linarith [hterm_a, hterm_b]

/-- `s`-uniform pointwise majorant: for `s ∈ (t/2, 2t)`,
`g_s(u)·|u²/s² − 1/s| ≤ gaussHessMaj t u`.

Independent honesty audit (2026-05-31, fresh auditor, Wave 3 commit `b5b9360`):
**MAJORANT-INEQUALITY SOUNDNESS = PASS** (verified the 3 sub-bounds on the window `s ∈ (t/2,2t)`):
(i) prefactor `(√(2πs))⁻¹ ≤ (√(πt))⁻¹` ⟺ `2s ≥ t`, holds from `s > t/2` (`hpref`, `ht2s`);
(ii) exponent `exp(−u²/(2s)) ≤ exp(−u²/(4t))` ⟺ `s ≤ 2t` (with `u² ≥ 0`), holds from `s < 2t`
(`hexp`, `sq_nonneg u`); (iii) polynomial `|u²/s²−1/s| ≤ u²/s²+1/s ≤ 4u²/t²+2/t` ⟺ `t ≤ 2s`
(`u²/s² ≤ 4u²/t²` ⟺ `t² ≤ 4s²`; `1/s ≤ 2/t` ⟺ `t ≤ 2s`), holds from `2s > t` (`hpoly` `h1`/`h2`).
**Case-A re-emergence ruled out**: this is the single Gaussian kernel `g_s` *outside* the
convolution (`g_s` is genuinely Gaussian, so a Gaussian majorant is correct) — categorically
different from the deleted case-A defect, which falsely asserted a Gaussian tail for the
*convolution* `pX∗g_s` against polynomial-tail `pX`. A wrong majorant here would make GAP②
pointwise vacuous; it is correct. `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(sorryAx-free). All hyps regularity; not load-bearing.
@audit:ok -/
private theorem gaussianHess_le_gaussHessMaj {t : ℝ} (ht : 0 < t) {s : ℝ}
    (hs : s ∈ Set.Ioo (t/2) (2*t)) (u : ℝ) :
    gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩ u
        * |u ^ 2 / s ^ 2 - 1 / s|
      ≤ gaussHessMaj t u := by
  have hspos : (0:ℝ) < s := by have := hs.1; linarith
  have ht2s : t < 2 * s := by have := hs.1; linarith
  have hs2t : s ≤ 2 * t := hs.2.le
  -- unfold the Gaussian: `(√(2πs))⁻¹ · exp(-u²/(2s))`.
  rw [gaussianPDFReal]
  simp only [sub_zero]
  -- prefactor bound: `(√(2πs))⁻¹ ≤ (√(πt))⁻¹`.
  have hpref : (Real.sqrt (2 * Real.pi * s))⁻¹ ≤ (Real.sqrt (Real.pi * t))⁻¹ := by
    apply inv_anti₀ (by positivity)
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_pos]
  -- exponent bound: `exp(-u²/(2s)) ≤ exp(-u²/(4t))`.
  have hexp : Real.exp (-u ^ 2 / (2 * s)) ≤ Real.exp (-u ^ 2 / (4 * t)) := by
    apply Real.exp_le_exp.2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg u]
  -- polynomial factor bound: `|u²/s² − 1/s| ≤ 4u²/t² + 2/t`.
  have hpoly : |u ^ 2 / s ^ 2 - 1 / s| ≤ 4 * u ^ 2 / t ^ 2 + 2 / t := by
    have h1 : u ^ 2 / s ^ 2 ≤ 4 * u ^ 2 / t ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have ht2 : t ^ 2 ≤ 4 * s ^ 2 := by nlinarith [hspos, ht]
      nlinarith [sq_nonneg u, ht2, mul_nonneg (sq_nonneg u) (sub_nonneg.2 ht2)]
    have h2 : 1 / s ≤ 2 / t := by
      rw [div_le_div_iff₀ hspos ht]; nlinarith
    have h3 : (0:ℝ) ≤ u ^ 2 / s ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ 1 / s := by positivity
    rw [abs_le]
    constructor
    · nlinarith [h1, h2, h3, h4]
    · nlinarith [h1, h2, h3, h4]
  -- nonnegativity of all factors, then multiply the three bounds.
  have hpref_nn : (0:ℝ) ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ := by positivity
  have hexp_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (2 * s)) := (Real.exp_pos _).le
  have habs_nn : (0:ℝ) ≤ |u ^ 2 / s ^ 2 - 1 / s| := abs_nonneg _
  have hprefT_nn : (0:ℝ) ≤ (Real.sqrt (Real.pi * t))⁻¹ := by positivity
  have hexpT_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (4 * t)) := (Real.exp_pos _).le
  unfold gaussHessMaj
  calc (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-u ^ 2 / (2 * s)) * |u ^ 2 / s ^ 2 - 1 / s|
      ≤ (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2 + 2 / t) := by
        apply mul_le_mul (mul_le_mul hpref hexp hexp_nn hprefT_nn) hpoly habs_nn
        exact mul_nonneg hprefT_nn hexpT_nn

/-- **Tonelli integrability of the convolution-of-an-integrable-kernel envelope.**
For an integrable kernel `K` and an integrable density `pX`, the convolution-shaped function
`x ↦ ∫ y, pX y · K (x − y)` is Lebesgue-integrable (`∫_x = (∫K)·∫pX`, by translation
invariance + `Integrable.integral_prod_left`). The product integrability on `volume.prod volume`
uses `integrable_prod_iff'`.

Independent honesty audit (2026-05-31, fresh auditor, Wave 3 commit `b5b9360`): genuine Tonelli
helper, `#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free). All four hyps
(`hpX_int`/`hpX_meas`/`hK_int`/`hK_meas`) are regularity (integrability + measurability of the two
factors); the integrability conclusion is the genuine claim, not bundled in any hyp. This is the
helper that genuinely closes the `Integrable bound` half of GAP②.
@audit:ok -/
private theorem convKernel_envelope_integrable
    (pX K : ℝ → ℝ) (hpX_int : Integrable pX volume) (hpX_meas : Measurable pX)
    (hK_int : Integrable K volume) (hK_meas : Measurable K) :
    Integrable (fun x => ∫ y, pX y * K (x - y) ∂volume) volume := by
  -- the 2D integrand `f (x,y) = pX y · K (x − y)`.
  set f : ℝ × ℝ → ℝ := fun p => pX p.2 * K (p.1 - p.2) with hf_def
  -- a.e.-strong measurability of `f` on the product measure.
  have hf_meas : AEStronglyMeasurable f (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => pX p.2) (volume.prod volume) :=
      (hpX_meas.comp measurable_snd).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => K (p.1 - p.2)) (volume.prod volume) := by
      have hsub : Measurable (fun p : ℝ × ℝ => p.1 - p.2) := measurable_fst.sub measurable_snd
      exact (hK_meas.comp hsub).aestronglyMeasurable
    exact h1.mul h2
  -- `f` is integrable on the product via `integrable_prod_iff'`.
  have hf_int : Integrable f (volume.prod volume) := by
    rw [integrable_prod_iff' hf_meas]
    refine ⟨?_, ?_⟩
    · -- for each `y`, `x ↦ pX y · K (x − y)` is integrable.
      refine Filter.Eventually.of_forall (fun y => ?_)
      exact (hK_int.comp_sub_right y).const_mul (pX y)
    · -- `y ↦ ∫ x ‖pX y · K(x−y)‖ dx = (∫‖K‖) · ‖pX y‖` is integrable.
      have hKnorm : Integrable (fun x => ‖K x‖) volume := hK_int.norm
      have heq : (fun y => ∫ x, ‖f (x, y)‖ ∂volume)
          = (fun y => ‖pX y‖ * ∫ x, ‖K x‖ ∂volume) := by
        funext y
        simp only [hf_def, norm_mul]
        rw [integral_const_mul]
        congr 1
        rw [← integral_sub_right_eq_self (fun x => ‖K x‖) y]
      rw [heq]
      exact (hpX_int.norm.mul_const _)
  -- conclude via `Integrable.integral_prod_left`.
  exact hf_int.integral_prod_left

/-! ### §5G-2b helpers — global sup bounds of the Gaussian kernel spatial derivatives

The STEP-D bridge `convDensityAdd_deriv2_eq_gaussian` consumes per-`s` domination hypotheses
`‖pX y · kernel-deriv s (ξ-y)‖ ≤ bound y` *uniform in `ξ`*. Since the kernel argument `ξ - y`
ranges over all of `ℝ`, the bound is `pX y · M` with `M` a **global sup** of the kernel
derivative. Both global sups have closed forms provable from `Real.mul_exp_neg_le_exp_neg_one`
(`y·exp(-y) ≤ exp(-1)`) and `exp ≤ 1`:

* `kernel·(-(u/s))` (1st deriv): `‖·‖ = (√(2πs))⁻¹·exp(-u²/(2s))·|u|/s`, bounded via
  `2|u| ≤ 1+u²` then `u²·exp(-u²/(2s)) ≤ 2s·exp(-1)` and `exp(-u²/(2s)) ≤ 1`.
* `kernel·(u²/s²-1/s)` (2nd deriv): `‖·‖ ≤ (√(2πs))⁻¹·exp(-u²/(2s))·(u²/s²+1/s)`, bounded
  termwise the same way.

These are genuine global-boundedness facts (continuous Gaussian×polynomial → 0 at ∞), NOT
load-bearing: they assert pure analytic majorants, no convolution/Hessian claim. -/

/-- Global sup bound of the kernel spatial 1st derivative `g_s(u)·(-(u/s))`.

Independent honesty audit (2026-05-31, Wave 4, fresh auditor): verdict **ok**. Bound
`(√(2πs))⁻¹·((1+2s·e⁻¹)/(2s))` is a genuine global sup of the single Gaussian kernel 1st spatial
derivative: body uses `2|u| ≤ 1+u²`, `u²·exp(−u²/2s) ≤ 2s·e⁻¹` (`mul_exp_neg_le_exp_neg_one`),
`exp ≤ 1` — sound. Single Gaussian `g_s` *outside* convolution (Gaussian → bounded), unrelated to
the deleted case-A polynomial-tail defect. Hyp `0<s` regularity; not load-bearing.
@audit:ok -/
private theorem kernel_x_deriv1_global_bound {s : ℝ} (hs : 0 < s) :
    ∀ u : ℝ, ‖heatFlow_density_heat_equation_kernel s u * (-(u / s))‖
      ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ * ((1 + 2 * s * Real.exp (-1)) / (2 * s)) := by
  intro u
  unfold heatFlow_density_heat_equation_kernel
  set P : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ with hP
  have hP_nn : (0:ℝ) ≤ P := by rw [hP]; positivity
  have hexp_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (2 * s)) := (Real.exp_pos _).le
  -- ‖P·exp·(-(u/s))‖ = P·exp·(|u|/s)
  rw [norm_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hP_nn, abs_of_nonneg hexp_nn,
    Real.norm_eq_abs, abs_neg, abs_div, abs_of_pos hs]
  -- reduce to `exp·|u| ≤ (1+2s·exp(-1))/2`
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hP_nn
  -- key: `exp(-u²/(2s))·|u| ≤ (1+2s·exp(-1))/2`, then divide by `s`.
  have hkey : Real.exp (-u ^ 2 / (2 * s)) * |u| ≤ (1 + 2 * s * Real.exp (-1)) / 2 := by
    -- `2|u| ≤ 1 + u²`
    have h2u : 2 * |u| ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (|u| - 1), sq_abs u]
    -- `u²·exp(-u²/(2s)) ≤ 2s·exp(-1)` via `mul_exp_neg_le_exp_neg_one (u²/(2s))`
    have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (2 * s))
    have hexp_eq : Real.exp (-(u ^ 2 / (2 * s))) = Real.exp (-u ^ 2 / (2 * s)) := by
      congr 1; ring
    rw [hexp_eq] at hmul
    -- so `u²·exp ≤ 2s·exp(-1)`
    have hu2 : u ^ 2 * Real.exp (-u ^ 2 / (2 * s)) ≤ 2 * s * Real.exp (-1) := by
      have h2s : (0:ℝ) < 2 * s := by linarith
      have hmul' := mul_le_mul_of_nonneg_left hmul h2s.le
      -- `2s·((u²/(2s))·exp) = u²·exp` and `2s·exp(-1)`
      have heq : (2 * s) * ((u ^ 2 / (2 * s)) * Real.exp (-u ^ 2 / (2 * s)))
          = u ^ 2 * Real.exp (-u ^ 2 / (2 * s)) := by field_simp
      rw [heq] at hmul'
      linarith [hmul']
    -- `exp ≤ 1`
    have hexp_le1 : Real.exp (-u ^ 2 / (2 * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ u ^ 2 / (2 * s) := by positivity
      linarith [neg_div (2 * s) (u ^ 2)]
    -- combine: `exp·|u| = exp·(2|u|)/2 ≤ exp·(1+u²)/2 = (exp + u²·exp)/2 ≤ (1 + 2s·exp(-1))/2`
    nlinarith [mul_le_mul_of_nonneg_left h2u hexp_nn, hu2, hexp_le1, abs_nonneg u]
  -- divide hkey by `s`
  calc Real.exp (-u ^ 2 / (2 * s)) * (|u| / s)
      = (Real.exp (-u ^ 2 / (2 * s)) * |u|) / s := by ring
    _ ≤ ((1 + 2 * s * Real.exp (-1)) / 2) / s := by gcongr
    _ = (1 + 2 * s * Real.exp (-1)) / (2 * s) := by ring

/-- Global sup bound of the kernel spatial 2nd derivative `g_s(u)·(u²/s²-1/s)`.

Independent honesty audit (2026-05-31, Wave 4, fresh auditor): verdict **ok**. Bound
`(√(2πs))⁻¹·((2e⁻¹+1)/s)` is a genuine global sup: body splits `|u²/s²−1/s| ≤ u²/s²+1/s`, bounds
`exp·u²/s² ≤ 2e⁻¹/s` (`mul_exp_neg_le_exp_neg_one`) and `exp·1/s ≤ 1/s` — sound. Single Gaussian
`g_s` outside convolution. `#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free,
machine-verified). Hyp `0<s` regularity; not load-bearing.
@audit:ok -/
private theorem kernel_x_deriv2_global_bound {s : ℝ} (hs : 0 < s) :
    ∀ u : ℝ, ‖heatFlow_density_heat_equation_kernel s u * (u ^ 2 / s ^ 2 - 1 / s)‖
      ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ * ((2 * Real.exp (-1) + 1) / s) := by
  intro u
  unfold heatFlow_density_heat_equation_kernel
  set P : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ with hP
  have hP_nn : (0:ℝ) ≤ P := by rw [hP]; positivity
  have hexp_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (2 * s)) := (Real.exp_pos _).le
  -- ‖P·exp·(u²/s²-1/s)‖ = P·exp·|u²/s²-1/s|
  rw [norm_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hP_nn, abs_of_nonneg hexp_nn,
    Real.norm_eq_abs]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hP_nn
  -- bound: exp·|u²/s²-1/s| ≤ exp·(u²/s²+1/s) ≤ (2·exp(-1)+1)/s
  -- `u²·exp(-u²/(2s)) ≤ 2s·exp(-1)`
  have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (2 * s))
  have hexp_eq : Real.exp (-(u ^ 2 / (2 * s))) = Real.exp (-u ^ 2 / (2 * s)) := by congr 1; ring
  rw [hexp_eq] at hmul
  have h2s : (0:ℝ) < 2 * s := by linarith
  have hu2 : u ^ 2 * Real.exp (-u ^ 2 / (2 * s)) ≤ 2 * s * Real.exp (-1) := by
    have hmul' := mul_le_mul_of_nonneg_left hmul h2s.le
    have heq : (2 * s) * ((u ^ 2 / (2 * s)) * Real.exp (-u ^ 2 / (2 * s)))
        = u ^ 2 * Real.exp (-u ^ 2 / (2 * s)) := by field_simp
    rw [heq] at hmul'; linarith [hmul']
  have hexp_le1 : Real.exp (-u ^ 2 / (2 * s)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ u ^ 2 / (2 * s) := by positivity
    linarith [neg_div (2 * s) (u ^ 2)]
  -- abs split + termwise bounds, all divided by appropriate powers of s
  have habs : |u ^ 2 / s ^ 2 - 1 / s| ≤ u ^ 2 / s ^ 2 + 1 / s := by
    have h1 : (0:ℝ) ≤ u ^ 2 / s ^ 2 := by positivity
    have h2 : (0:ℝ) ≤ 1 / s := by positivity
    rw [abs_le]; constructor <;> nlinarith [h1, h2]
  -- `exp · u²/s² ≤ 2·exp(-1)/s` and `exp · 1/s ≤ 1/s`
  have hssq : (0:ℝ) < s ^ 2 := by positivity
  have ht1 : Real.exp (-u ^ 2 / (2 * s)) * (u ^ 2 / s ^ 2) ≤ 2 * Real.exp (-1) / s := by
    have : Real.exp (-u ^ 2 / (2 * s)) * (u ^ 2 / s ^ 2)
        = (u ^ 2 * Real.exp (-u ^ 2 / (2 * s))) / s ^ 2 := by ring
    rw [this]
    calc (u ^ 2 * Real.exp (-u ^ 2 / (2 * s))) / s ^ 2
        ≤ (2 * s * Real.exp (-1)) / s ^ 2 := by gcongr
      _ = 2 * Real.exp (-1) / s := by
            rw [pow_two, mul_comm s s, ← div_div]
            congr 1
            field_simp
  have ht2 : Real.exp (-u ^ 2 / (2 * s)) * (1 / s) ≤ 1 / s := by
    have : (0:ℝ) ≤ 1 / s := by positivity
    calc Real.exp (-u ^ 2 / (2 * s)) * (1 / s) ≤ 1 * (1 / s) := by gcongr
      _ = 1 / s := one_mul _
  calc Real.exp (-u ^ 2 / (2 * s)) * |u ^ 2 / s ^ 2 - 1 / s|
      ≤ Real.exp (-u ^ 2 / (2 * s)) * (u ^ 2 / s ^ 2 + 1 / s) :=
        mul_le_mul_of_nonneg_left habs hexp_nn
    _ = Real.exp (-u ^ 2 / (2 * s)) * (u ^ 2 / s ^ 2)
          + Real.exp (-u ^ 2 / (2 * s)) * (1 / s) := by ring
    _ ≤ 2 * Real.exp (-1) / s + 1 / s := by linarith [ht1, ht2]
    _ = (2 * Real.exp (-1) + 1) / s := by ring

/-- **Concrete pointwise Hessian bound** (extracted from GAP②'s pointwise body, reused by
`_chain_domination`). For `s ∈ (t/2, 2t)`, the spatial second derivative of the convolution
density is dominated by the convolution of `pX` against the `s`-uniform Gaussian-Hessian kernel
majorant `gaussHessMaj t`:
`‖∂²_x (pX ∗ g_s) x‖ ≤ ∫ y, pX y · gaussHessMaj t (x − y) ∂volume`.

The proof routes through the STEP-D bridge `convDensityAdd_deriv2_eq_gaussian`
(`∂²_x p_s x = ∫ y, pX y·g_s(x−y)·((x−y)²/s²−1/s)`), supplying its per-`s` domination hyps
with the closed-form global sups `kernel_x_deriv1/2_global_bound`, then triangle inequality +
the `s`-uniform majorant `gaussianHess_le_gaussHessMaj`. This is GAP②'s pointwise content as a
named lemma so that **both** GAP② (as the existential envelope) **and** `_chain_domination` (route
II Tonelli, which needs the concrete envelope, not the abstract `∃`) consume it. Only `0<t`
regularity hyps; the Hessian bound (conclusion) is the genuine claim, not load-bearing.

**Independent honesty audit (2026-05-31, Wave 5, commit `647015d`, fresh auditor): verdict ok.**
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-verified — the
STEP-D bridge `convDensityAdd_deriv2_eq_gaussian` it calls is itself sorry-free). Conclusion
`‖∂²(pX∗g_s) x‖ ≤ ∫ pX y·gaussHessMaj t (x−y)` is a genuine pointwise claim (not a hypothesis-bundled
existence); all 5 hyps are pX-regularity + `0<t`. NOT circular/false-statement/load-bearing.
@audit:ok -/
private theorem convDensityAdd_deriv2_le_gaussHessMaj_conv
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) (x : ℝ) {s : ℝ}
    (hs : s ∈ Set.Ioo (t/2) (2*t)) :
    ‖deriv (deriv (convDensityAdd pX
        (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩))) x‖
      ≤ ∫ y, pX y * gaussHessMaj t (x - y) ∂volume := by
  have hspos : (0:ℝ) < s := by have := hs.1; linarith
  -- kernel continuity (for measurability of the bridge integrands).
  have hker_cont : Continuous (fun u : ℝ => heatFlow_density_heat_equation_kernel s u) := by
    unfold heatFlow_density_heat_equation_kernel
    fun_prop
  have hker_meas : Measurable (fun u : ℝ => heatFlow_density_heat_equation_kernel s u) :=
    hker_cont.measurable
  -- global sup constants of the kernel spatial derivatives.
  set M1 : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ * ((1 + 2 * s * Real.exp (-1)) / (2 * s)) with hM1
  set M2 : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ * ((2 * Real.exp (-1) + 1) / s) with hM2
  have hM1_nn : (0:ℝ) ≤ M1 := by rw [hM1]; positivity
  have hM2_nn : (0:ℝ) ≤ M2 := by rw [hM2]; positivity
  have hF1_meas : ∀ ξ : ℝ,
      AEStronglyMeasurable
        (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume := by
    intro ξ
    exact (hpX_meas.aestronglyMeasurable).mul
      ((hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  have hker_le : ∀ v : ℝ, |heatFlow_density_heat_equation_kernel s v|
      ≤ (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹ := by
    intro v
    rw [heatFlow_density_heat_equation_kernel_eq hspos v,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 _ v)]
    exact gaussianPDFReal_le_prefactor' ⟨s, hspos.le⟩ v
  have hF1_int : ∀ ξ : ℝ,
      Integrable (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume := by
    intro ξ
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]; exact hker_le (ξ - y))
  have hF1'_meas : ∀ ξ : ℝ, AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s)))) volume := by
    intro ξ
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact ((measurable_const.sub measurable_id).div_const s).neg.aestronglyMeasurable
  have hb1 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s)))‖ ≤ (fun y => |pX y| * M1) y := by
    refine Filter.Eventually.of_forall (fun y ξ _ => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv1_global_bound hspos (ξ - y)
    rwa [hM1]
  have hb1_int : Integrable (fun y => |pX y| * M1) volume := hpX_int.abs.mul_const _
  have hF2'_meas : AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (x - y)
        * ((x - y) ^ 2 / s ^ 2 - 1 / s))) volume := by
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact (((measurable_const.sub measurable_id).pow_const 2).div_const _).sub
        measurable_const |>.aestronglyMeasurable
  have hb2 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * ((ξ - y) ^ 2 / s ^ 2 - 1 / s))‖ ≤ (fun y => |pX y| * M2) y := by
    refine Filter.Eventually.of_forall (fun y ξ _ => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv2_global_bound hspos (ξ - y)
    rwa [hM2]
  have hb2_int : Integrable (fun y => |pX y| * M2) volume := hpX_int.abs.mul_const _
  have hF2_int : Integrable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (x - y)
        * (-((x - y) / s)))) volume := by
    refine Integrable.mono' hb1_int (hF1'_meas x) (Filter.Eventually.of_forall (fun y => ?_))
    have := kernel_x_deriv1_global_bound hspos (x - y)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rwa [hM1]
  have hbridge :=
    InformationTheory.Shannon.EPIConvDensitySecondDeriv.convDensityAdd_deriv2_eq_gaussian
    pX hpX_nn hpX_int hspos x
    (fun y => |pX y| * M1) hb1_int hF1_meas hF1_int hF1'_meas hb1
    (fun y => |pX y| * M2) hb2_int hF2_int hF2'_meas hb2
  rw [show (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩)
      = gaussianPDFReal 0 ⟨s, hspos.le⟩ from rfl, hbridge]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _)) ?_
    (Filter.Eventually.of_forall (fun y => ?_))
  · have hMmeas : Measurable (gaussHessMaj t) := by unfold gaussHessMaj; fun_prop
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (Real.pi * t))⁻¹ * (16 * Real.exp (-1) / t + 2 / t)) ?_ ?_
    · exact (hMmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussHessMaj_nonneg ht (x - y))]
      exact gaussHessMaj_bdd ht (x - y)
  · simp only []
    have hg_nn : (0:ℝ) ≤ gaussianPDFReal 0 ⟨s, hspos.le⟩ (x - y) := gaussianPDFReal_nonneg 0 _ _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hpX_nn y),
      Real.norm_eq_abs, abs_of_nonneg hg_nn, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (hpX_nn y)
    exact gaussianHess_le_gaussHessMaj ht hs (x - y)

/-- **§5G-2b (GAP②, 案B polynomial-moment restate): integrable envelope for the spatial Hessian.**
On the `t`-neighborhood `Set.Ioo (t/2) (2*t)`, the spatial second derivative
`∂²_x p_s x = deriv (deriv (convDensityAdd pX g_s)) x` of the convolution density admits a
**single Lebesgue-integrable envelope** `bound : ℝ → ℝ` uniform in `s`:
`‖∂²_x p_s x‖ ≤ bound x` for all `s ∈ (t/2, 2t)`, with `Integrable bound volume`.

**Why the conclusion is an integrable-envelope existential, not a Gaussian-tail bound.** The
prior `≤ C·(1+x²)·exp(-x²/c')` (Gaussian-tail) conclusion was a false statement: it asserts the
Hessian decays *faster than any polynomial* in `x`, which fails for polynomial-tail finite-variance
`pX` (counterexample `pX(y) = (2/π)/(1+y²)²` satisfies `∫pX = 1`, `∫y²·pX < ∞`, yet
`∂²_x p_s(x) ~ const/x²` decays only polynomially — judgment log #15). The honest envelope keeps the
Gaussian `g_s` *inside* the convolution rather than dropping it via a prefactor bound: via the
heat-eq STEP D identification
`∂²_x p_s x = ∫ y, pX y · g_s(x-y)·((x-y)²/s² - 1/s)`
(`FisherInfoV2DeBruijnPerTime.heatFlow_density_heat_equation` STEP D + the kernel 2nd-deriv
closed form `heatFlow_density_heat_equation_kernel_x_deriv2`), the triangle inequality gives the
pointwise bound `‖∂²_x p_s x‖ ≤ ∫ y, pX y · g_s(x-y)·|(x-y)²/s² - 1/s| dy =: bound x` (the `g_s`
Gaussian factor is retained, not bounded by its prefactor constant).

**Integrability of the envelope (finite-second-moment).** `bound` is Lebesgue-integrable for any
finite-variance `pX`: by Tonelli (the integrand is nonnegative)
`∫_x bound x dx = ∫_y pX(y)·[∫_x g_s(x-y)·|(x-y)²/s² - 1/s| dx] dy = ∫_y pX(y)·K(y) dy`, where after
the substitution `u = x - y` the inner integral
`K(y) = ∫_u g_s(u)·|u²/s² - 1/s| du` is a *constant* in `y` (independent of `y`, since `g_s` is
centred at 0 and `u` ranges over all of `ℝ`); more generally when the envelope is paired with a
polynomial log-factor (`_chain_domination`) the `y`-integral picks up only `∫pX`, `∫y·pX`, `∫y²·pX`
(mass + first + second moment), all finite under `hpX_mass`/`hpX_mom` (`∫y·pX` finite by `2|y| ≤ 1+y²`
domination via `hpX_int.add hpX_mom`). The result is finite.

This is honestly **true for polynomial-tail finite-variance pX** (the judgment-log-#15 counterexample
`(2/π)/(1+y²)²` is *inside* scope — the envelope does not claim Gaussian tail), and heavy-tailed `pX`
with infinite variance (e.g. Cauchy) is honestly excluded by the regularity hyp `hpX_mom`. All hyps
(`hpX_mass`/`hpX_mom` included) are pX-system regularity, NOT load-bearing.

**Progress (2026-05-31, this session)**: the envelope is now **concretely constructed** as
`bound x := ∫ y, pX y · gaussHessMaj t (x − y)`, where `gaussHessMaj t u := (√(πt))⁻¹·exp(−u²/(4t))·
(4u²/t² + 2/t)` is the genuine `s`-uniform Gaussian-Hessian kernel majorant (proved:
`gaussianHess_le_gaussHessMaj` gives `g_s(u)·|u²/s²−1/s| ≤ gaussHessMaj t u` for all `s ∈ (t/2,2t)`;
`gaussHessMaj_integrable` gives `Integrable (gaussHessMaj t)` as a Gaussian×quadratic). The
**`Integrable bound` half is now genuinely closed** via `convKernel_envelope_integrable` (Tonelli
`integrable_prod_iff'` + `Integrable.integral_prod_left` + translation invariance). The **only
remaining residual is the pointwise bound** `‖∂²_x p_s x‖ ≤ bound x`: it needs the STEP-D bridge
`convDensityAdd_deriv2_eq_gaussian` (∂²p_s as `∫ y, pX y·g_s(x−y)·((x−y)²/s²−1/s)`) + triangle +
`gaussianHess_le_gaussHessMaj`, where the bridge's per-`s` domination hypotheses (global sup bounds of
`g_s·(−v/s)` and `g_s·(v²/s²−1/s)` over `v`) remain to supply. So this stays an **honest sorry** but
narrowed to the bridge/triangle pointwise step only.

Independent honesty audit (2026-05-31, fresh auditor, 案B-core split commit `1c194dd`): verdict
honest_residual. **Statement-truth (case-A re-emergence check PASS)**: the restated conclusion
`∃ bound, Integrable bound ∧ ∀ᵐ x ∀ s∈Ioo(t/2,2t), ‖∂²_x p_s x‖ ≤ bound x` is TRUE & satisfiable
for finite-2nd-moment pX, and is qualitatively different from the deleted case-A Gaussian-tail
`C(1+x²)exp(-x²/c')` (which asserted a *specific false decay form*). The envelope existential
demands no concrete shape: the s-uniform candidate `sup_{s∈Ioo} ∫_y pX(y)·g_s(x-y)·|(x-y)²/s²−1/s| dy`
is a genuine pointwise majorant (STEP-D kernel form `g_σ(u)·(u²/σ²−1/σ)` verified genuine at
`FisherInfoV2DeBruijnPerTime.heatFlow_density_heat_equation_kernel_x_deriv2:290`, sorryAx-free) and is
Lebesgue-integrable (s ranges over a compact-away-from-0 window so the g_s moments are bounded; the
x-integral collapses to ∫pX·const + moments, all finite). **Not vacuous**: `Integrable bound` is a
genuine constraint a non-integrable bound would fail. The judgment-log-#15 counterexample `(2/π)/(1+y²)²`
(finite 2nd moment, polynomial `∂²p_s` decay) is now *inside* scope — polynomial `~1/x⁴` decay IS
dominated by an integrable bound, so it is not a counterexample (independent re-check). Cauchy / infinite
variance honestly excluded by `hpX_mom`. **Classification `plan:` correct** (NOT a new wall): the
envelope-construction residual closes via Tonelli (`MeasureTheory.lintegral_lintegral_swap` /
`Integrable.integral_prod_left` present in Mathlib) + g_s Gaussian moments + finite-2nd-moment — same-family
plumbing, not a Mathlib gap; plan `docs/shannon/epi-debruijn-pertime-closure-plan.md` exists. All 5 pX hyps
(incl. `hpX_mass`/`hpX_mom`) are regularity preconditions (positivity/measurability/integrability/normalization/
finite 2nd moment), NOT load-bearing — the Hessian bound (the conclusion) is asserted by none of them. NOT
circular, NOT false-statement, NOT degenerate. The prior `@audit:defect(false-statement)` +
`@audit:retract-candidate` are correctly removed (statement now genuinely true). @residual kept.

Independent honesty audit (2026-05-31, fresh auditor, Wave 3 genuine-helper commit `b5b9360`):
verdict **honest_residual** (re-confirmed after envelope concretisation). **Integrability half now
genuinely closed** (body L678-681 calls `convKernel_envelope_integrable` — audited `@audit:ok`,
sorryAx-free — with the concrete `bound x = ∫ y, pX y · gaussHessMaj t (x−y)`; the s-uniform kernel
majorant `gaussHessMaj` is `@audit:ok` and its pointwise bound `gaussianHess_le_gaussHessMaj` passed
the 3-sub-bound soundness check). **Only the pointwise `sorry` (L690) remains** and is correctly
narrowed: the bridge `EPIConvDensitySecondDeriv.convDensityAdd_deriv2_eq_gaussian` it routes through is
already genuine + `@audit:ok` + Mathlib-present (a `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
gateway), so the residual is supplying that bridge's per-`s` `bound1`/`bound2` domination hyps + triangle
+ `gaussianHess_le_gaussHessMaj` = same-family **plan plumbing**, NOT a Mathlib gap. **Classification
`plan:epi-debruijn-pertime-closure` correct** (plan file exists at `docs/shannon/`). All 5 pX hyps are
regularity (nn/meas/int/normalisation/2nd-moment); the Hessian bound (conclusion) is asserted by none of
them — NOT load-bearing. Statement TRUE & satisfiable for finite-2nd-moment pX (existential envelope,
no concrete decay shape demanded, so NOT the case-A false Gaussian-tail). NOT circular/degenerate.

**GENUINELY CLOSED (2026-05-31, this session, GAP② proof done).** The pointwise residual is now
discharged: both halves are genuine. (1) `Integrable bound` via `convKernel_envelope_integrable`
(Tonelli). (2) The pointwise bound `‖∂²_x p_s x‖ ≤ bound x` via the STEP-D bridge
`EPIConvDensitySecondDeriv.convDensityAdd_deriv2_eq_gaussian` (∂²p_s as
`∫ y, pX y·g_s(x−y)·((x−y)²/s²−1/s)`), supplying its 11 per-`s` domination hyps with bound
functions `|pX y|·M1`/`|pX y|·M2` (`M1`/`M2` = closed-form global sups of the kernel spatial
derivatives, `kernel_x_deriv1_global_bound`/`kernel_x_deriv2_global_bound`, proved from
`Real.mul_exp_neg_le_exp_neg_one` + `exp ≤ 1`), then `norm_integral_le_integral_norm` (triangle) +
`integral_mono_of_nonneg` + the `s`-uniform majorant `gaussianHess_le_gaussHessMaj`. The envelope
integrand integrability uses `gaussHessMaj_bdd` (global boundedness) + `Integrable.mul_bdd`.
`hpX_mass`/`hpX_mom` are now unused (the genuine route via the concrete Gaussian-kernel envelope
does not need finite-2nd-moment of pX — the `g_s` Gaussian inside the convolution supplies all decay)
but kept in the signature for caller compatibility. 0 sorry / 0 residual.

Independent honesty audit (2026-05-31, Wave 4, fresh auditor, commits `5dba37a`+`a382aea`):
verdict **ok** (proof done) — re-confirmed independently. (1) **sorryAx-free machine-verified**:
`#print axioms Common2026.Shannon.FisherInfoV2.convDensityAdd_deriv2_poly_moment_majorant` =
`[propext, Classical.choice, Quot.sound]` (transient `#print axioms` + `lake env lean`, sorryAx
ABSENT). GAP② does NOT transitively depend on the file's 3 remaining sorrys
(`_chain_domination`/`_ibp_step`/`_chain_parametric`) — the abstract `∃ bound` is closed in-body by
the concrete envelope `bound x = ∫ y, pX y · gaussHessMaj t (x−y)`. (2) **Statement unchanged & TRUE**:
the conclusion `∃ bound, Integrable bound ∧ ∀ᵐ x ∀ s∈Ioo, ‖∂²p_s x‖ ≤ bound x` is the genuine claim;
no precondition was weakened to make it vacuous. (3) **Bridge inputs genuine**: the 11 per-`s`
domination hyps fed to `convDensityAdd_deriv2_eq_gaussian` (itself `@audit:ok`, 0 sorry, in
`EPIConvDensitySecondDeriv.lean:145`) are constructed in-body from `kernel_x_deriv1/2_global_bound` +
`hpX_int.abs.mul_const`/`mul_bdd` — pure regularity/measurability, none asserts the Hessian bound.
(4) **`hpX_mass`/`hpX_mom` now genuinely unused** (the Gaussian `g_s` inside the convolution supplies
all decay) — not load-bearing, kept only for caller compatibility (lint warns, harmless). NOT
circular/false-statement/degenerate/load-bearing. `@audit:ok` confirmed.

**Re-confirm after Wave 5 refactor (2026-05-31, commit `647015d`, fresh auditor): verdict ok
(proof done) — STILL HOLDS.** GAP②'s pointwise content was extracted to the named lemma
`convDensityAdd_deriv2_le_gaussHessMaj_conv`; the body is now a thin wrapper
(`convKernel_envelope_integrable` for integrability + that named lemma for pointwise domination,
L1187-1192), still 0 local sorry. `#print axioms` re-run = `[propext, Classical.choice, Quot.sound]`
(sorryAx-free, machine-verified). The file's remaining sorrys are now only 2 (`_ibp_step`:1602 /
`_chain_parametric`:1702) since `_chain_domination` reached proof-done this wave — GAP② does not call
either. `@audit:ok` retained.
@audit:ok -/
private theorem convDensityAdd_deriv2_poly_moment_majorant
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      ∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖deriv (deriv (convDensityAdd pX
            (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩))) x‖
          ≤ bound x := by
  -- The concrete envelope: `bound x = ∫ y, pX y · gaussHessMaj t (x − y)` — the convolution of
  -- the integrable density `pX` against the `s`-uniform Gaussian-Hessian kernel majorant.
  -- Integrability via Tonelli (`convKernel_envelope_integrable`), pointwise domination via the
  -- extracted concrete lemma `convDensityAdd_deriv2_le_gaussHessMaj_conv` (reused by `_chain_domination`).
  refine ⟨fun x => ∫ y, pX y * gaussHessMaj t (x - y) ∂volume, ?_, ?_⟩
  · have hMmeas : Measurable (gaussHessMaj t) := by unfold gaussHessMaj; fun_prop
    exact convKernel_envelope_integrable pX (gaussHessMaj t) hpX_int hpX_meas
      (gaussHessMaj_integrable ht) hMmeas
  · refine Filter.Eventually.of_forall (fun x s hs => ?_)
    exact convDensityAdd_deriv2_le_gaussHessMaj_conv pX hpX_nn hpX_meas hpX_int ht x hs

/-- **§5G-2: full-entDeriv joint-domination group (L-PT-γ, 案B joint strategy).**
Produces an integrable majorant `bound` dominating the **full** entropy σ-derivand
`(- log (pPath s x) - 1) · ((1/2)·∂²_x pPath s x)` over the `t`-neighborhood
`Set.Ioo (t/2) (2*t)`. On `Ioo (t/2)(2*t)` with `t > 0` we have `s > t/2 > 0`, so the NNReal
variance witness `⟨s, _⟩` is well-defined (no `max s 0` needed).

**案B joint-domination wiring (2026-05-31, judgment log #16/#17)**: the body `obtain`s two
`s`-uniform regularity helpers and forms their *joint* product envelope:
- §5G-2a / GAP① (`convDensityAdd_logFactor_poly_majorant`, genuine `@audit:ok`): an `s`-uniform
  polynomial majorant `A + B·x²` for the log factor `-log p_s x - 1`;
- §5G-2b / GAP② (`convDensityAdd_deriv2_poly_moment_majorant`, honest sorry, polynomial-moment
  restate): an `s`-uniform **integrable envelope** `hessBound x` for the spatial Hessian
  `∂²_x p_s x` (keeping the `g_s` Gaussian inside the convolution; NO Gaussian-tail claim).

The joint majorant is `(A + B·x²)·((1/2)·hessBound x)`. Its integrability is the analytic core,
discharged via **route II = Tonelli + g_s moment** (the only honest route, judgment log #17):
`∫_x (A+Bx²)·(1/2)hessBound x dx = (1/2)∫_y pX(y)·K(y) dy` where `K(y)` is a degree-2 polynomial in
`y` (from `∫_u (A+B(u+y)²)·g_s(u)·|u²/s²−1/s| du` after `u = x−y` and the even-moment closed forms of
`g_s`), so the outer integral collapses to `c0 + c1·∫y·pX + c2·∫y²·pX < ∞` (mass + first + second
moment, all finite under `hpX_mass`/`hpX_mom`; the first moment is dominated by `2|y| ≤ 1+y²`).

**Why route I is forbidden (judgment log #17, proof-pivot-advisor mpmath verification)**: the
Hessian envelope `hessBound x` decays only **polynomially** `~const/x⁴` in `x` (the `g_s` Gaussian
factor is dominated/killed by polynomial-tail `pX`, e.g. `(2/π)/(1+y²)²`). The closed-form route
"bound `hessBound` by `x^{0,2,4}·exp(-(1/c)x²)` and close with `integrable_natPow_mul_exp_neg_mul_sq`"
is **FALSE for polynomial-tail finite-variance pX** (it is the case-A defect re-emerging — the old
Gaussian-tail `exp(-x²/c')` factor does not exist). Route II keeps the integrability honest by never
asserting a Gaussian-tail closed form; the Gaussian decay only ever appears inside `g_s` under the
moment integral.

The `_chain_domination` statement (∃ integrable majorant over `Ioo (t/2,2t)`) is TRUE for general
finite-2nd-moment pX, and the joint-domination wiring is the genuine route to it (no separated
Gaussian-tail product, no false-statement dependency). All hyps are pX-system regularity; the
existential output is integrand-level domination. The honest residual is localized in (a) the GAP②
poly-moment envelope (§5G-2b) and (b) the joint envelope integrability core (route II Tonelli+moment,
first goal below); the domination goal (second) is closed genuinely by `norm_mul`/`mul_le_mul`. The
`@residual` is kept (transitive over GAP② + the integrability core).

Independent honesty audit (2026-05-31, fresh auditor, 案B-core split commit `1c194dd`): verdict
honest_residual. **Vacuous-genuine RESOLVED**: the prior body (commit `cf88267`/`b53107a`,
`@audit:defect(false-statement)`) "closed" the integrability locally via
`integrable_natPow_mul_exp_neg_mul_sq` (route I), which rested on GAP②'s FALSE Gaussian-tail decay —
vacuous-genuine. The 案B body now honestly leaves the integrability as `sorry` (first goal) and only
closes the domination (second goal) genuinely. **Core-reconstruction test PASS (genuine wiring)**:
granting the two helpers' outputs — GAP① `⟨A,B,…,hLog⟩` (polynomial majorant `A+Bx²` for the *log
factor only*) and GAP② `⟨hessBound, hHess_int, hHess⟩` (integrable envelope for the *Hessian only*) —
does NOT auto-discharge the conclusion: the conclusion needs the **product** `(A+Bx²)·(1/2)hessBound`
to be integrable, and polynomial-growth × integrable-envelope is NOT auto-integrable from `hHess_int`
alone; this is the genuine analytic core, correctly localized to the first-goal `sorry` (route II
Tonelli + g_s moment, judgment log #17). The domination (second goal) genuinely consumes BOTH `hLog`
and `hHess` via `mul_le_mul`. **`integrable_natPow_mul_exp_neg_mul_sq` is correctly NOT used** (route I
= deleted case-A defect, would be false for polynomial-tail pX). **Classification `plan:` correct** for
the integrability-core sorry: Tonelli + Gaussian moments + finite-2nd-moment are Mathlib-present
(`lintegral_lintegral_swap` / `Integrable.integral_prod_left`) = same-family plumbing, not a wall; plan
exists. All hyps are pX regularity, NOT load-bearing; the existential output is integrand-level
domination (the genuine claim). NOT circular, NOT vacuous-genuine, NOT false-statement. The
`@audit:defect(false-statement)` is correctly removed (statement true via 案B joint route). @residual kept.

Independent honesty audit (2026-05-31, fresh auditor, Wave 3 genuine-helper commit `b5b9360`):
verdict **honest_residual** (re-confirmed). Two goals: (1st) joint-envelope integrability `sorry`
(L784), (2nd) domination — **genuine, sorry-free** (L786-809: `filter_upwards [hLog, hHess]` then
`norm_mul`/`mul_le_mul hlf hhalf` consumes BOTH GAP① `hLog` and GAP② `hHess` outputs; verified
no `sorry`). **Core-reconstruction PASS**: granting GAP① (poly majorant `A+Bx²` for the log factor
ONLY) + GAP② (integrable envelope for the Hessian ONLY) does NOT auto-discharge the conclusion —
the conclusion needs the **product** `(A+Bx²)·(1/2)hessBound` integrable, and poly-growth ×
integrable-envelope is not auto-integrable from `hHess_int` alone; the genuine analytic core is
correctly localised to the 1st-goal `sorry` (route II = Tonelli + g_s moment). **`integrable_natPow_mul_exp_neg_mul_sq`
correctly NOT used** (route I = deleted case-A defect, false for polynomial-tail pX). **Classification
`plan:` correct**: route II = `lintegral_lintegral_swap`/`Integrable.integral_prod_left` (Mathlib-present)
+ Gaussian moments + finite-2nd-moment = same-family plumbing, not a wall. All hyps pX regularity, NOT
load-bearing; existential output is integrand-level domination (genuine claim). NOT circular/vacuous-genuine/false-statement. @residual kept.

**GENUINELY CLOSED (2026-05-31, this session, `_chain_domination` proof done).** Both goals are
now sorry-free. The integrability core (1st goal) is discharged via **route II = Tonelli +
even-moment**, NOT route I: GAP②'s concrete envelope `E x = ∫ y, pX y · gaussHessMaj t (x−y)` is
used directly (GAP② refactored to expose the pointwise lemma `convDensityAdd_deriv2_le_gaussHessMaj_conv`,
both `@audit:ok`). The joint envelope `(A+B·x²)·(1/2)·E x` is dominated by
`H x = ∫ pX y·G(x−y) + 2|B|·∫ (y²·pX y)·g(x−y)` (`G(u)=(|A|+2|B|u²)·gaussHessMaj t u`,
`g=gaussHessMaj t`), via `x² ≤ 2(x−y)²+2y²` (NO odd cross-term — only even Gaussian moments). `H`
is integrable as a sum of two `convKernel_envelope_integrable` envelopes: `∫ pX y·G(x−y)` (`pX`
integrable, `G` integrable via `gaussHessMaj_polyWeight_integrable`) and `∫ (y²·pX y)·g(x−y)`
(`y²·pX` integrable = **`hpX_mom` genuinely used here**, `g` integrable). Per-`y` fibre integrability
uses `gaussHessMaj_polyWeight_bdd`/`gaussHessMaj_bdd` (`Integrable.mul_bdd`). The domination goal (2nd)
uses `convDensityAdd_deriv2_le_gaussHessMaj_conv` for `‖∂²p_s x‖ ≤ E x` + `norm_mul`/`mul_le_mul`.
`integrable_natPow_mul_exp_neg_mul_sq` (route I = deleted case-A defect) is NOT used. `#print axioms`
= `[propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-verified). `hpX_mass` remains
unused (only `hpX_mom` is load-bearing for the integrability); kept for caller compatibility.
0 sorry / 0 residual.

**Independent honesty audit (2026-05-31, Wave 5, commit `647015d`, fresh auditor): verdict ok
(proof done).** (1) **sorryAx-free machine-verified**: transient `#print axioms` + `lake env lean`
gives `[propext, Classical.choice, Quot.sound]`, sorryAx ABSENT — confirms `_chain_domination` does
NOT transitively call the file's 2 remaining sorrys (`_ibp_step`:1602 / `_chain_parametric`:1702).
(2) **even-envelope soundness PASS**: `x² ≤ 2(x−y)²+2y²` (L1421) is exactly `(x−2y)² ≥ 0`, supplied
by `sq_nonneg (x−2y)` — mathematically correct; no odd cross-term so only even Gaussian moments are
needed (route I = `integrable_natPow_mul_exp_neg_mul_sq` confirmed ABSENT from the body). (3) **hpX_mom
is regularity, NOT load-bearing**: it supplies `Integrable (y²·pX)` (heavy-tail / finite-variance
control), genuinely consumed at L1322 (`hmomPX_int`) for the 2nd convolution envelope; the conclusion
(existence of an integrable domination envelope) is NOT assumed by it — "load-bearing for the
integrability" in the prose above means "genuinely consumed", not the honesty-sense load-bearing hyp.
The 2nd goal (domination) is genuine via `convDensityAdd_deriv2_le_gaussHessMaj_conv` + `norm_mul`/
`mul_le_mul` (L1434-1463), no sorry. @audit:ok -/
private theorem debruijnIdentityV2_holds_assembled_chain_domination
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      (∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖(- Real.log (convDensityAdd pX
              (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩) x) - 1)
            * ((1/2) * deriv (deriv (convDensityAdd pX
              (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩))) x)‖
          ≤ bound x) := by
  -- 案B joint domination: the σ-derivand at `s` is the product
  --   LogFactor(s,x) = - log (p_s x) - 1     (poly-in-x growth, GAP① `A + B·x²`)
  --   (1/2)·Hess(s,x) = (1/2)·∂²_x p_s x     (integrable envelope `(1/2)·hessBound x`, GAP②).
  -- GAP① gives an `s`-uniform polynomial majorant for the log factor;
  -- GAP② (poly-moment restate) gives an `s`-uniform integrable envelope `hessBound` for the Hessian.
  obtain ⟨A, B, hB_nn, hLog⟩ :=
    convDensityAdd_logFactor_poly_majorant pX hpX_nn hpX_meas hpX_int hpX_mass ht
  -- The **concrete** envelope `E x = ∫ y, pX y · gaussHessMaj t (x − y)` (= GAP②'s in-body envelope),
  -- used directly here so that route II Tonelli sees the convolution shape (not an abstract `∃`).
  set E : ℝ → ℝ := fun x => ∫ y, pX y * gaussHessMaj t (x - y) ∂volume with hE_def
  have hg_meas : Measurable (gaussHessMaj t) := by unfold gaussHessMaj; fun_prop
  have hg_nn : ∀ u, (0:ℝ) ≤ gaussHessMaj t u := gaussHessMaj_nonneg ht
  -- the joint majorant: (A + B·x²) · ((1/2)·E x).
  refine ⟨fun x => (A + B * x ^ 2) * ((1/2) * E x), ?_, ?_⟩
  · -- **route II = Tonelli + g_s moment** (the only honest route, judgment log #17).
    -- The dominating function: `H x = ∫ pX y·G(x−y) + 2|B|·∫ (y²·pX y)·g(x−y)`, where
    -- `G(u) = (|A| + 2|B|·u²)·gaussHessMaj t u` (Gaussian × quartic) and `g = gaussHessMaj t`.
    -- Both summands are `convKernel_envelope_integrable` envelopes (`pX` / `y²·pX` integrable,
    -- `G` / `g` integrable). Pointwise `‖(A+Bx²)·(1/2)E x‖ ≤ H x` via `x² ≤ 2(x−y)²+2y²` (NO odd
    -- cross-term, so only even Gaussian moments needed). `hpX_mom` is genuinely used (it supplies
    -- integrability of `y²·pX`, the heavy-tail-controlling density). `integrable_natPow_mul_exp_neg_mul_sq`
    -- (route I = deleted case-A defect, false for polynomial-tail pX) is NOT used.
    set G : ℝ → ℝ := fun u => (|A| + 2 * |B| * u ^ 2) * gaussHessMaj t u with hG_def
    have hG_int : Integrable G volume := gaussHessMaj_polyWeight_integrable ht |A| (2 * |B|)
    have hG_meas : Measurable G := by rw [hG_def]; fun_prop
    have hG_nn : ∀ u, (0:ℝ) ≤ G u := fun u => by
      rw [hG_def]; exact mul_nonneg (by positivity) (hg_nn u)
    -- `y²·pX` integrable (= `hpX_mom`) and measurable.
    have hmomPX_int : Integrable (fun y => y ^ 2 * pX y) volume := hpX_mom
    have hmomPX_meas : Measurable (fun y => y ^ 2 * pX y) := by fun_prop
    -- the two convolution envelopes.
    have hEnv1_int : Integrable (fun x => ∫ y, pX y * G (x - y) ∂volume) volume :=
      convKernel_envelope_integrable pX G hpX_int hpX_meas hG_int hG_meas
    have hEnv2_int : Integrable (fun x => ∫ y, (y ^ 2 * pX y) * gaussHessMaj t (x - y) ∂volume)
        volume :=
      convKernel_envelope_integrable (fun y => y ^ 2 * pX y) (gaussHessMaj t)
        hmomPX_int hmomPX_meas (gaussHessMaj_integrable ht) hg_meas
    -- dominating function `H x` integrable.
    have hH_int : Integrable (fun x => (∫ y, pX y * G (x - y) ∂volume)
        + 2 * |B| * (∫ y, (y ^ 2 * pX y) * gaussHessMaj t (x - y) ∂volume)) volume :=
      hEnv1_int.add (hEnv2_int.const_mul _)
    -- measurability of the target (poly × convolution envelope).
    have hE_meas : AEStronglyMeasurable E volume := by
      rw [hE_def]
      exact (convKernel_envelope_integrable pX (gaussHessMaj t) hpX_int hpX_meas
        (gaussHessMaj_integrable ht) hg_meas).aestronglyMeasurable
    have htarget_meas : AEStronglyMeasurable
        (fun x => (A + B * x ^ 2) * ((1/2) * E x)) volume := by
      refine AEStronglyMeasurable.mul ?_ ?_
      · fun_prop
      · exact hE_meas.const_mul _
    -- pointwise domination `‖(A+Bx²)·(1/2)·E x‖ ≤ H x`.
    refine Integrable.mono' hH_int htarget_meas (Filter.Eventually.of_forall (fun x => ?_))
    -- nonneg of `E x` (= `∫ pX y·g(x−y)`, integrand `≥ 0`).
    have hEnv_pos_int : Integrable (fun y => pX y * gaussHessMaj t (x - y)) volume := by
      have hMmeas := hg_meas
      refine hpX_int.mul_bdd
        (c := (Real.sqrt (Real.pi * t))⁻¹ * (16 * Real.exp (-1) / t + 2 / t)) ?_ ?_
      · exact (hMmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn (x - y))]
        exact gaussHessMaj_bdd ht (x - y)
    have hE_nn : (0:ℝ) ≤ E x := by
      rw [hE_def]
      exact integral_nonneg (fun y => mul_nonneg (hpX_nn y) (hg_nn (x - y)))
    -- `‖(A+Bx²)·(1/2)·E x‖ = |A+Bx²|·(1/2)·E x ≤ (|A|+|B|x²)·E x`.
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h12 : |(1/2 : ℝ)| = 1/2 := by rw [abs_of_pos]; norm_num
    rw [h12, abs_of_nonneg hE_nn]
    -- step 1: `|A+Bx²|·(1/2)·E x ≤ (|A|+|B|x²)·E x`.
    have hstep1 : |A + B * x ^ 2| * (1/2 * E x) ≤ (|A| + |B| * x ^ 2) * E x := by
      have hbound : |A + B * x ^ 2| ≤ |A| + |B| * x ^ 2 := by
        calc |A + B * x ^ 2| ≤ |A| + |B * x ^ 2| := abs_add_le _ _
          _ = |A| + |B| * x ^ 2 := by rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
      calc |A + B * x ^ 2| * (1/2 * E x)
          ≤ (|A| + |B| * x ^ 2) * (1/2 * E x) :=
            mul_le_mul_of_nonneg_right hbound (by positivity)
        _ ≤ (|A| + |B| * x ^ 2) * E x := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [hE_nn]
    -- step 2: `(|A|+|B|x²)·E x = ∫ (|A|+|B|x²)·pX y·g(x−y) ≤ ∫ pX y·G(x−y) + 2|B|∫(y²pX)·g(x−y) = H x`.
    refine le_trans hstep1 ?_
    -- pull the constant `(|A|+|B|x²)` into the integral.
    have hpull : (|A| + |B| * x ^ 2) * E x
        = ∫ y, (|A| + |B| * x ^ 2) * (pX y * gaussHessMaj t (x - y)) ∂volume := by
      rw [hE_def, ← integral_const_mul]
    rw [hpull]
    -- per-`y` fibre integrability of the two dominating pieces.
    -- (1) `fun y => pX y · G(x−y)`: `G` globally bounded (`gaussHessMaj_polyWeight_bdd`) × `pX` integ.
    have hfib1_int : Integrable (fun y => pX y * G (x - y)) volume := by
      refine hpX_int.mul_bdd
        (c := |A| * ((Real.sqrt (Real.pi * t))⁻¹ * (16 * Real.exp (-1) / t + 2 / t))
          + 2 * |B| * ((Real.sqrt (Real.pi * t))⁻¹
              * (256 * Real.exp (-1) ^ 2 + 8 * Real.exp (-1)))) ?_ ?_
      · exact (hG_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun y => ?_)
        rw [Real.norm_eq_abs, hG_def, abs_of_nonneg (hG_nn (x - y))]
        exact gaussHessMaj_polyWeight_bdd ht (abs_nonneg A) (by positivity) (x - y)
    -- (2) `fun y => (y²·pX y)·g(x−y)`: `g` globally bounded (`gaussHessMaj_bdd`) × `y²·pX` integ.
    have hfib2_int : Integrable (fun y => (y ^ 2 * pX y) * gaussHessMaj t (x - y)) volume := by
      refine hmomPX_int.mul_bdd
        (c := (Real.sqrt (Real.pi * t))⁻¹ * (16 * Real.exp (-1) / t + 2 / t)) ?_ ?_
      · exact (hg_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn (x - y))]
        exact gaussHessMaj_bdd ht (x - y)
    -- target integrand integrability (for the LHS of `integral_mono`).
    have hlhs_int : Integrable
        (fun y => (|A| + |B| * x ^ 2) * (pX y * gaussHessMaj t (x - y))) volume :=
      hEnv_pos_int.const_mul _
    -- the dominating integrand: `pX y·G(x−y) + 2|B|·((y²pX)·g(x−y))`.
    have hdom_int : Integrable
        (fun y => pX y * G (x - y) + 2 * |B| * ((y ^ 2 * pX y) * gaussHessMaj t (x - y)))
        volume :=
      hfib1_int.add (hfib2_int.const_mul _)
    -- `H x = ∫ pX y·G(x−y) + 2|B|·∫(y²pX)·g(x−y) = ∫ [pX y·G(x−y) + 2|B|·(y²pX)·g(x−y)]`.
    have hH_eq : (∫ y, pX y * G (x - y) ∂volume)
          + 2 * |B| * (∫ y, (y ^ 2 * pX y) * gaussHessMaj t (x - y) ∂volume)
        = ∫ y, (pX y * G (x - y)
            + 2 * |B| * ((y ^ 2 * pX y) * gaussHessMaj t (x - y))) ∂volume := by
      rw [integral_add hfib1_int (hfib2_int.const_mul _), integral_const_mul]
    rw [hH_eq]
    -- pointwise: `(|A|+|B|x²)·pX y·g(x−y) ≤ pX y·G(x−y) + 2|B|·(y²pX)·g(x−y)`.
    refine integral_mono hlhs_int hdom_int (fun y => ?_)
    -- `(|A|+|B|x²) ≤ |A| + 2|B|(x−y)² + 2|B|y²` via `x² ≤ 2(x−y)²+2y²`, then multiply by `pX y·g ≥ 0`.
    have hpXg_nn : (0:ℝ) ≤ pX y * gaussHessMaj t (x - y) :=
      mul_nonneg (hpX_nn y) (hg_nn (x - y))
    have hx2 : x ^ 2 ≤ 2 * (x - y) ^ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (x - 2 * y), sq_nonneg x]
    have hcoef : (|A| + |B| * x ^ 2)
        ≤ (|A| + 2 * |B| * (x - y) ^ 2) + 2 * |B| * y ^ 2 := by
      have hBabs : (0:ℝ) ≤ |B| := abs_nonneg B
      nlinarith [mul_le_mul_of_nonneg_left hx2 hBabs]
    -- `G(x−y) = (|A|+2|B|(x−y)²)·g(x−y)`.
    have hGval : G (x - y) = (|A| + 2 * |B| * (x - y) ^ 2) * gaussHessMaj t (x - y) := by
      rw [hG_def]
    calc (|A| + |B| * x ^ 2) * (pX y * gaussHessMaj t (x - y))
        ≤ ((|A| + 2 * |B| * (x - y) ^ 2) + 2 * |B| * y ^ 2) * (pX y * gaussHessMaj t (x - y)) :=
          mul_le_mul_of_nonneg_right hcoef hpXg_nn
      _ = pX y * G (x - y) + 2 * |B| * ((y ^ 2 * pX y) * gaussHessMaj t (x - y)) := by
          rw [hGval]; ring
  · -- domination: `‖LogFactor · (1/2 · Hess)‖ ≤ (A + B·x²)·((1/2)·E x)`, genuine via norm_mul.
    --   the Hessian bound `‖∂²p_s x‖ ≤ E x` is the concrete pointwise lemma.
    filter_upwards [hLog] with x hLogx
    intro s hs
    have hspos : (0:ℝ) < s := by have := hs.1; linarith
    -- `‖a·b‖ = ‖a‖·‖b‖`, then bound each factor.
    rw [norm_mul]
    have hlf := hLogx s hs
    have hhf : ‖deriv (deriv (convDensityAdd pX
        (gaussianPDFReal 0 ⟨s, hspos.le⟩))) x‖ ≤ E x := by
      have := convDensityAdd_deriv2_le_gaussHessMaj_conv pX hpX_nn hpX_meas hpX_int ht x hs
      rwa [show (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩)
        = gaussianPDFReal 0 ⟨s, hspos.le⟩ from rfl] at this
    -- E x ≥ ‖Hess‖ ≥ 0, so the envelope is nonneg.
    have hE_nn : (0:ℝ) ≤ E x := le_trans (norm_nonneg _) hhf
    -- ‖(1/2)·Hess‖ = (1/2)·‖Hess‖ ≤ (1/2)·E x.
    have hhalf : ‖(1/2 : ℝ) * deriv (deriv (convDensityAdd pX
        (gaussianPDFReal 0 ⟨s, hspos.le⟩))) x‖
        ≤ (1/2) * E x := by
      rw [norm_mul]
      have hhn : ‖(1/2 : ℝ)‖ = 1/2 := by rw [Real.norm_eq_abs]; rw [abs_of_pos]; norm_num
      rw [hhn]
      exact mul_le_mul_of_nonneg_left hhf (by norm_num)
    -- combine: ‖LogFactor‖·‖(1/2)Hess‖ ≤ (A+B·x²)·((1/2)·E x).
    have hLog_nn : (0:ℝ) ≤ A + B * x ^ 2 := le_trans (norm_nonneg _) hlf
    calc ‖(- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hspos.le⟩) x) - 1)‖
            * ‖(1/2 : ℝ) * deriv (deriv (convDensityAdd pX
                (gaussianPDFReal 0 ⟨s, hspos.le⟩))) x‖
          ≤ (A + B * x ^ 2) * ((1/2) * E x) := by
            apply mul_le_mul hlf hhalf (norm_nonneg _) hLog_nn

/-- **Fisher integrability of the time-`t` convolution density (wall call + Step-3 plumbing).**
The square-score density `(logDeriv p_t)² · p_t` of the convolution density
`p_t = convDensityAdd pX g_t` is Lebesgue-integrable, where `g_t = gaussianPDFReal 0 ⟨t,_⟩`.

**Rewire (2026-05-31, fisher-finiteness-closure-plan R-A Step 3 — genuine plumbing).** The
former monolithic body sorry (`@residual(wall:fisher-finiteness)`) is replaced by a call to
the shared Stam-convolution-Fisher wall `gaussianConv_fisher_le_inv_var`
(`FisherConvBound.lean`, the sole `@residual(wall:fisher-finiteness)` carrier) plus genuine
plumbing. The body now: (Step 2) `p_t ≥ 0` pointwise via `integral_nonneg`; (Step 3) calls
the wall for `J(p_t) ≤ 1/t`; (Step 4) `J(p_t) < ⊤` by `lt_of_le_of_lt … ENNReal.ofReal_lt_top`;
(Step 5) unfolds `fisherInfoOfDensity` and merges the two `ENNReal.ofReal` factors via
`← ENNReal.ofReal_mul (sq_nonneg _)` (same as `fisher_from_logDeriv`) to `∫⁻ ofReal((logDeriv
p_t)²·p_t) ≠ ∞`; (Step 6) a.e.-strong-measurability of `(logDeriv p_t)²·p_t` is now **genuine
plumbing** (`p_t` strongly measurable via `StronglyMeasurable.integral_prod_right` on the
jointly-measurable integrand `(z,x) ↦ pX x · g_t (z-x)`, `logDeriv p_t = deriv p_t / p_t` via
`measurable_deriv` + the div), and concludes via
`lintegral_ofReal_ne_top_iff_integrable`. **0 local sorry** here; the only residual is the
shared wall it calls (transitive `sorryAx` via `gaussianConv_fisher_le_inv_var`).

**True statement** (Stam convolution Fisher bound): for any probability density `pX`, the
Fisher information of `X + √t·Z` is bounded by that of the Gaussian noise alone,
`J(X + √t·Z) ≤ J(√t·Z) = 1/t < ∞` (Stam / Blachman score-of-convolution monotonicity). The
integral `∫ (logDeriv p_t)²·p_t = J(X+√t·Z)` is therefore finite, hence the integrand is
integrable. Even for a heavy-tailed `pX` (e.g. Cauchy) the Gaussian-smoothed score
`(∂_x p_t)²/p_t ~ x⁻⁴` decays integrably.

**Classification `wall:fisher-finiteness`** (NOT `plan:`): Mathlib has no convolution Fisher
bound — loogle `fisherInfo` / `Blachman` return `Found 0 declarations`, and the in-repo Stam
machinery (`EPIStam*`) is predicate pass-through only (no genuine `J(X+Z) ≤ J(Z)` lemma).
Closing this requires a self-written Stam-convolution-Fisher-bound PR (`J(X+Z) ≤ J(Z) = 1/t`),
i.e. a genuine Mathlib gap rather than a same-family closure plan. After this rewire the wall
is localized to `gaussianConv_fisher_le_inv_var`; this consumer carries no local sorry.

`hpX_nn`/`hpX_meas`/`hpX_int` are pure pX regularity preconditions; the integrability
conclusion is the genuine claim. No load-bearing hypothesis bundled.

The `@residual` is now **transitive** (the wall sorry lives in the shared lemma, not here).
Marker kept so the transitive dependency on the Fisher wall stays grep-visible until the wall
is closed.

Independent honesty audit (2026-05-31, fresh auditor, Wave 2 rewire): verdict honest_residual
(transitive). Body is genuine: 0 local sorry (`:694-741` contains no literal `sorry`); the wall
is consumed as a *lemma call* `gaussianConv_fisher_le_inv_var pX …` (Step 3), NOT bundled as a
hypothesis. Step-6 a.e.-strong-measurability is genuine plumbing, not circular/false: `hpt_meas`
via `StronglyMeasurable.integral_prod_right` on the jointly-measurable integrand, `hlogderiv_meas`
via `measurable_deriv` + `.div` (`logDeriv = deriv p_t / p_t`) — all Mathlib std, no conclusion
assumed. `hpX_nn`/`hpX_meas`/`hpX_int` are pure pX regularity; the integrability conclusion is the
genuine claim. `#print axioms` = `[propext, sorryAx, Classical.choice, Quot.sound]`, where the lone
`sorryAx` is **transitive** via the shared wall `gaussianConv_fisher_le_inv_var`
(`FisherConvBound.lean:73`, the sole `wall:fisher-finiteness` carrier). Wall aggregation verified:
`rg wall:fisher-finiteness` shows exactly ONE real sorry (FisherConvBound.lean:73); this consumer
and `…_chain_ibp_fisher` (`:844` call site) are transitive markers only. The transitive `@residual`
is retained per audit-tags.md compound-syntax scenario 1 (transitive sorry の正式表現); docstring
states the wall is localized to the shared lemma and this declaration carries no local sorry —
honest. `@residual(wall:fisher-finiteness)` kept.
@residual(wall:fisher-finiteness) -/
private theorem convDensityAdd_fisher_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => (logDeriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x)^2
      * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) volume := by
  set p_t : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hp_def
  -- Step 2: `p_t ≥ 0` pointwise (convolution of nonnegatives).
  have hp_nn : ∀ x, 0 ≤ p_t x := fun x =>
    integral_nonneg fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  -- the integrand `g x = (logDeriv p_t x)² · p_t x` is pointwise nonnegative.
  have hg_nn : 0 ≤ᵐ[volume] fun x => (logDeriv p_t x) ^ 2 * p_t x :=
    Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hp_nn x)
  -- Step 3: shared Stam-convolution-Fisher wall `J(p_t) ≤ 1/t`.
  have hbound : fisherInfoOfDensity p_t ≤ ENNReal.ofReal (1 / t) :=
    gaussianConv_fisher_le_inv_var pX hpX_nn hpX_meas hpX_int ht
  -- Step 4: hence `J(p_t) < ⊤`.
  have hfin : fisherInfoOfDensity p_t < ⊤ :=
    lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  -- Step 5: merge the two `ENNReal.ofReal` factors so the lintegrand is `ofReal g`.
  have hmerge :
      fisherInfoOfDensity p_t
        = ∫⁻ x, ENNReal.ofReal ((logDeriv p_t x) ^ 2 * p_t x) ∂volume := by
    unfold fisherInfoOfDensity
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  -- `∫⁻ ofReal g < ⊤` i.e. `≠ ∞`.
  rw [hmerge] at hfin
  -- Step 6: a.e.-strong-measurability of `g = (logDeriv p_t)² · p_t`.
  -- `p_t = z ↦ ∫ x, pX x · g_t (z - x)` is strongly measurable (parametric integral of a
  -- jointly measurable integrand); `logDeriv p_t = deriv p_t / p_t` with `deriv p_t`
  -- measurable. All genuine plumbing (Mathlib `StronglyMeasurable.integral_prod_right` +
  -- `measurable_deriv`), not a wall.
  have hgt_meas : Measurable (gaussianPDFReal 0 ⟨t, ht.le⟩) :=
    measurable_gaussianPDFReal 0 ⟨t, ht.le⟩
  have hpt_meas : Measurable p_t := by
    have huncurry :
        StronglyMeasurable
          (Function.uncurry fun z x => pX x * gaussianPDFReal 0 ⟨t, ht.le⟩ (z - x)) := by
      apply Measurable.stronglyMeasurable
      apply (hpX_meas.comp measurable_snd).mul
      exact hgt_meas.comp ((measurable_fst).sub measurable_snd)
    have h := huncurry.integral_prod_right (ν := volume)
    simpa only [hp_def, convDensityAdd] using h.measurable
  have hderiv_meas : Measurable (deriv p_t) := measurable_deriv p_t
  have hlogderiv_meas : Measurable (logDeriv p_t) := by
    simp only [logDeriv]
    exact hderiv_meas.div hpt_meas
  have hg_aesm :
      AEStronglyMeasurable (fun x => (logDeriv p_t x) ^ 2 * p_t x) volume :=
    ((hlogderiv_meas.pow_const 2).mul hpt_meas).aestronglyMeasurable
  -- Step 6 (concl): `∫⁻ ofReal g ≠ ∞ ↔ Integrable g`.
  exact (lintegral_ofReal_ne_top_iff_integrable hg_aesm hg_nn).mp hfin.ne

/-- **Differentiability of the convolution density (deriv-existence helper).**
`HasDerivAt p_t (deriv p_t x) x` for `p_t = convDensityAdd pX g_t` at every `x` (`t > 0`).

Genuinely closed (0 sorry / 0 residual). The proof reconstructs the spatial first derivative
of the heat-flow convolution density at `x` via the parametric-integral gateway
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` (the same machinery as the `@audit:ok` atom
`convDensityAdd_deriv1_gaussian_eq`), supplying the integrand-level domination group from the
`@audit:ok` global-sup bound `kernel_x_deriv1_global_bound` (`bound1 := |pX y| · M1` integrable
via `Integrable.mul_const`). It then concludes `HasDerivAt p_t (deriv p_t x) x` by rewriting the
derivative value (`hgate.2.deriv`). All hyps are pX regularity (`hpX_nn` carried for the family
signature; `hpX_meas`/`hpX_int` used). NOT load-bearing, NOT circular.

Independent honesty audit (2026-06-01, fresh auditor, commits `e0e81ba`/`c7df95f`): `@audit:ok`.
Genuine closure machine-verified — transient `#print axioms` + `lake env lean` reports
`[propext, Classical.choice, Quot.sound]` only (sorryAx-free, transitive 0 sorry). NOT circular:
the `deriv … x` in the conclusion is the derivative VALUE, reconstructed independently via the
parametric-integral gateway then `hderiv.deriv` (no hypothesis ≡ conclusion). NOT load-bearing:
every hypothesis is pX regularity / context; `hpX_nn` is unused, carried only for family-signature
uniformity (a benign precondition, not a defect). The differentiability is genuinely derived from
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` + per-`y` kernel `HasDerivAt`, not granted by a
`HasDerivAt`/`Differentiable` bundle.
@audit:ok -/
private theorem convDensityAdd_hasDerivAt_self
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x) x := by
  -- kernel continuity / measurability.
  have hker_cont : Continuous (fun u : ℝ => heatFlow_density_heat_equation_kernel t u) := by
    unfold heatFlow_density_heat_equation_kernel; fun_prop
  have hker_meas : Measurable (fun u : ℝ => heatFlow_density_heat_equation_kernel t u) :=
    hker_cont.measurable
  -- `convDensityAdd pX g_t = fun ζ => ∫ y, pX y · kernel t (ζ-y)` (t>0).
  have hconv_eq : (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      = (fun ζ : ℝ => ∫ y, pX y * heatFlow_density_heat_equation_kernel t (ζ - y) ∂volume) := by
    funext ζ
    unfold convDensityAdd
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [heatFlow_density_heat_equation_kernel_eq ht (ζ - y)]
  -- the global-sup constant of the kernel 1st spatial derivative.
  set M1 : ℝ := (Real.sqrt (2 * Real.pi * t))⁻¹ * ((1 + 2 * t * Real.exp (-1)) / (2 * t)) with hM1
  -- domination group for the parametric-integral gateway (`bound1 := |pX y| · M1`).
  have hF1_meas : ∀ ξ : ℝ,
      AEStronglyMeasurable
        (fun y => pX y * heatFlow_density_heat_equation_kernel t (ξ - y)) volume := by
    intro ξ
    exact (hpX_meas.aestronglyMeasurable).mul
      ((hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  have hker_le : ∀ v : ℝ, |heatFlow_density_heat_equation_kernel t v|
      ≤ (Real.sqrt (2 * Real.pi * (⟨t, ht.le⟩ : ℝ≥0)))⁻¹ := by
    intro v
    rw [heatFlow_density_heat_equation_kernel_eq ht v,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 _ v)]
    exact gaussianPDFReal_le_prefactor' ⟨t, ht.le⟩ v
  have hF1_int : ∀ ξ : ℝ,
      Integrable (fun y => pX y * heatFlow_density_heat_equation_kernel t (ξ - y)) volume := by
    intro ξ
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (2 * Real.pi * (⟨t, ht.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]; exact hker_le (ξ - y))
  have hF1'_meas : ∀ ξ : ℝ, AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * (-((ξ - y) / t)))) volume := by
    intro ξ
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact ((measurable_const.sub measurable_id).div_const t).neg.aestronglyMeasurable
  have hb1 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * (-((ξ - y) / t)))‖ ≤ (fun y => |pX y| * M1) y := by
    refine Filter.Eventually.of_forall (fun y ξ _ => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv1_global_bound ht (ξ - y)
    rwa [hM1]
  have hb1_int : Integrable (fun y => |pX y| * M1) volume := hpX_int.abs.mul_const _
  -- per-y spatial 1st-derivative HasDerivAt (kernel `_x_deriv1` chained through `ξ ↦ ξ-y`).
  have hdiff : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun ξ => pX y * heatFlow_density_heat_equation_kernel t (ξ - y))
        (pX y * (heatFlow_density_heat_equation_kernel t (ξ - y) * (-((ξ - y) / t)))) ξ := by
    filter_upwards with y
    intro ξ _
    have hk := heatFlow_density_heat_equation_kernel_x_deriv1 ht (ξ - y)
    have hshift : HasDerivAt (fun ξ : ℝ => ξ - y) 1 ξ := by
      simpa using (hasDerivAt_id ξ).sub_const y
    have hcomp := hk.comp ξ hshift
    simp only [mul_one] at hcomp
    exact hcomp.const_mul (pX y)
  -- parametric-integral gateway at `x`.
  have hgate :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun ζ y => pX y * heatFlow_density_heat_equation_kernel t (ζ - y))
      (F' := fun ζ y => pX y * (heatFlow_density_heat_equation_kernel t (ζ - y)
        * (-((ζ - y) / t))))
      (bound := fun y => |pX y| * M1) (Filter.univ_mem)
      (Filter.Eventually.of_forall hF1_meas) (hF1_int x) (hF1'_meas x)
      hb1 hb1_int hdiff
  -- `hgate.2 : HasDerivAt p_t (∫ y, pX y · kernel·(-(x-y)/t)) x`.
  have hderiv : HasDerivAt (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      (∫ y, pX y * (heatFlow_density_heat_equation_kernel t (x - y) * (-((x - y) / t))) ∂volume) x := by
    rw [hconv_eq]; exact hgate.2
  -- conclude `HasDerivAt p_t (deriv p_t x) x` by rewriting the derivative value.
  rw [hderiv.deriv]
  exact hderiv

/-- **Differentiability of the convolution-density derivative (deriv-existence helper).**
`HasDerivAt (deriv p_t) (deriv (deriv p_t) x) x` for `p_t = convDensityAdd pX g_t` at every
`x` (`t > 0`).

Genuinely closed (0 sorry / 0 residual). Same family as `convDensityAdd_hasDerivAt_self`. The
proof: (STEP 1) identifies `deriv p_t` as the kernel-form 1st-derivative function
`fun ζ => ∫ y, pX y·(kernel t (ζ-y)·(-((ζ-y)/t)))` via the `@audit:ok` atom
`convDensityAdd_deriv1_gaussian_eq` (`bound1 := |pX y| · M1` from `kernel_x_deriv1_global_bound`)
+ a `gaussianPDFReal`↔kernel rewrite; (STEP 2) differentiates that 1st-derivative function at `x`
via the parametric-integral gateway `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(`bound2 := |pX y| · M2` from `kernel_x_deriv2_global_bound`, per-`y` 2nd-derivative
`heatFlow_density_heat_equation_kernel_x_deriv2`); then concludes `HasDerivAt (deriv p_t)
(deriv (deriv p_t) x) x` by rewriting the 2nd-derivative value (`hgate2.2.deriv`). All hyps are
pX regularity (`hpX_nn` carried for the family signature). NOT load-bearing, NOT circular.

Independent honesty audit (2026-06-01, fresh auditor, commits `e0e81ba`/`c7df95f`): `@audit:ok`.
Genuine closure machine-verified — transient `#print axioms` + `lake env lean` reports
`[propext, Classical.choice, Quot.sound]` only (sorryAx-free, transitive 0 sorry; covers the
`@audit:ok` atom `convDensityAdd_deriv1_gaussian_eq` (STEP 1) + `kernel_x_deriv2_global_bound`
(STEP 2) transitively). NOT circular: the nested `deriv (deriv …) x` in the conclusion is the
2nd-derivative VALUE, reconstructed independently via STEP-1 `deriv p_t` identification + the 2nd
parametric-integral gateway then `hderiv2.deriv` (no hypothesis ≡ conclusion). NOT load-bearing:
every hypothesis is pX regularity / context; `hpX_nn` unused, carried only for family-signature
uniformity.
@audit:ok -/
private theorem convDensityAdd_deriv_hasDerivAt_self
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)))
      (deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x) x := by
  -- kernel continuity / measurability.
  have hker_cont : Continuous (fun u : ℝ => heatFlow_density_heat_equation_kernel t u) := by
    unfold heatFlow_density_heat_equation_kernel; fun_prop
  have hker_meas : Measurable (fun u : ℝ => heatFlow_density_heat_equation_kernel t u) :=
    hker_cont.measurable
  -- global-sup constants of the kernel 1st / 2nd spatial derivatives.
  set M1 : ℝ := (Real.sqrt (2 * Real.pi * t))⁻¹ * ((1 + 2 * t * Real.exp (-1)) / (2 * t)) with hM1
  set M2 : ℝ := (Real.sqrt (2 * Real.pi * t))⁻¹ * ((2 * Real.exp (-1) + 1) / t) with hM2
  -- ===== bound1 group (for the deriv1 atom function equality) =====
  have hF1_meas : ∀ ξ : ℝ,
      AEStronglyMeasurable
        (fun y => pX y * heatFlow_density_heat_equation_kernel t (ξ - y)) volume := by
    intro ξ
    exact (hpX_meas.aestronglyMeasurable).mul
      ((hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  have hker_le : ∀ v : ℝ, |heatFlow_density_heat_equation_kernel t v|
      ≤ (Real.sqrt (2 * Real.pi * (⟨t, ht.le⟩ : ℝ≥0)))⁻¹ := by
    intro v
    rw [heatFlow_density_heat_equation_kernel_eq ht v,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 _ v)]
    exact gaussianPDFReal_le_prefactor' ⟨t, ht.le⟩ v
  have hF1_int : ∀ ξ : ℝ,
      Integrable (fun y => pX y * heatFlow_density_heat_equation_kernel t (ξ - y)) volume := by
    intro ξ
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (2 * Real.pi * (⟨t, ht.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]; exact hker_le (ξ - y))
  have hF1'_meas : ∀ ξ : ℝ, AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * (-((ξ - y) / t)))) volume := by
    intro ξ
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact ((measurable_const.sub measurable_id).div_const t).neg.aestronglyMeasurable
  have hb1 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * (-((ξ - y) / t)))‖ ≤ (fun y => |pX y| * M1) y := by
    refine Filter.Eventually.of_forall (fun y ξ _ => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv1_global_bound ht (ξ - y)
    rwa [hM1]
  have hb1_int : Integrable (fun y => |pX y| * M1) volume := hpX_int.abs.mul_const _
  -- ===== bound2 group (for the 2nd gateway) =====
  have hb2 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * ((ξ - y) ^ 2 / t ^ 2 - 1 / t))‖ ≤ (fun y => |pX y| * M2) y := by
    refine Filter.Eventually.of_forall (fun y ξ _ => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv2_global_bound ht (ξ - y)
    rwa [hM2]
  have hb2_int : Integrable (fun y => |pX y| * M2) volume := hpX_int.abs.mul_const _
  have hF2'_meas : AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel t (x - y)
        * ((x - y) ^ 2 / t ^ 2 - 1 / t))) volume := by
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact (((measurable_const.sub measurable_id).pow_const 2).div_const _).sub
        measurable_const |>.aestronglyMeasurable
  have hF2_int : Integrable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel t (x - y)
        * (-((x - y) / t)))) volume := by
    refine Integrable.mono' hb1_int (hF1'_meas x) (Filter.Eventually.of_forall (fun y => ?_))
    have := kernel_x_deriv1_global_bound ht (x - y)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rwa [hM1]
  -- STEP 1: identify `deriv p_t` as the 1st-derivative integral function (deriv1 atom).
  have hd1 := InformationTheory.Shannon.EPIConvDensitySecondDeriv.convDensityAdd_deriv1_gaussian_eq
    pX ht (fun y => |pX y| * M1) hb1_int hF1_meas hF1_int hF1'_meas hb1
  -- the 1st-derivative function, in kernel form.
  have hd1_kernel : (fun ζ : ℝ => ∫ y, pX y * (gaussianPDFReal 0 ⟨t, ht.le⟩ (ζ - y)
        * (-((ζ - y) / t))) ∂volume)
      = (fun ζ : ℝ => ∫ y, pX y * (heatFlow_density_heat_equation_kernel t (ζ - y)
          * (-((ζ - y) / t))) ∂volume) := by
    funext ζ
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [heatFlow_density_heat_equation_kernel_eq ht (ζ - y)]
  -- so `deriv p_t = kernel-form 1st-derivative function`.
  have hderiv_eq : deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      = (fun ζ : ℝ => ∫ y, pX y * (heatFlow_density_heat_equation_kernel t (ζ - y)
          * (-((ζ - y) / t))) ∂volume) := by
    rw [hd1, hd1_kernel]
  -- STEP 2: per-y spatial 2nd-derivative HasDerivAt (kernel `_x_deriv2` chained through `ξ ↦ ξ-y`).
  have hdiff2 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun ξ => pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
          * (-((ξ - y) / t))))
        (pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
          * ((ξ - y) ^ 2 / t ^ 2 - 1 / t))) ξ := by
    filter_upwards with y
    intro ξ _
    have hk := heatFlow_density_heat_equation_kernel_x_deriv2 ht (ξ - y)
    have hshift : HasDerivAt (fun ξ : ℝ => ξ - y) 1 ξ := by
      simpa using (hasDerivAt_id ξ).sub_const y
    have hcomp := hk.comp ξ hshift
    simp only [mul_one] at hcomp
    exact hcomp.const_mul (pX y)
  -- the 2nd gateway at `x` (differentiate the kernel-form 1st-derivative function).
  have hgate2 :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun ξ y => pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * (-((ξ - y) / t))))
      (F' := fun ξ y => pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * ((ξ - y) ^ 2 / t ^ 2 - 1 / t)))
      (bound := fun y => |pX y| * M2) (Filter.univ_mem)
      (Filter.Eventually.of_forall hF1'_meas) hF2_int hF2'_meas
      hb2 hb2_int hdiff2
  -- `hgate2.2 : HasDerivAt (kernel-form 1st-deriv fn) (∫ y, pX y·kernel·((x-y)²/t²-1/t)) x`.
  have hderiv2 : HasDerivAt (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)))
      (∫ y, pX y * (heatFlow_density_heat_equation_kernel t (x - y)
        * ((x - y) ^ 2 / t ^ 2 - 1 / t)) ∂volume) x := by
    rw [hderiv_eq]; exact hgate2.2
  -- conclude by rewriting the 2nd-derivative value.
  rw [hderiv2.deriv]
  exact hderiv2

/-- **de Bruijn IBP step on the time-`t` convolution density — genuine atom application.**
The de Bruijn integration-by-parts identity at fixed time `t`:
`∫ (- log p_t - 1) · ∂²_x p_t = ∫ (logDeriv p_t)² · p_t`, where `p_t = convDensityAdd pX g_t`.

**§Phase 5-G IBP localization (2026-05-31)**: the former monolithic body `sorry` is **factored**
into a genuine `debruijn_ibp_step` (`@audit:ok`) application + named residuals (0 local sorry).
The body now:
- identifies the IBP quadruple `u = -log p_t - 1`, `v = ∂_x p_t`, `u' = -logDeriv p_t`,
  `v' = ∂²_x p_t`;
- supplies `hp_pos : 0 < p_t` genuinely (`convDensityAdd_pos`, mass `0 < ∫ pX = 1` from `hpX_mass`);
- builds `hu : HasDerivAt u (u' ·)` genuinely (`Real.hasDerivAt_log ∘ HasDerivAt p_t` via the
  deriv-existence helper `convDensityAdd_hasDerivAt_self`);
- builds `hv : HasDerivAt v (v' ·)` from the deriv-existence helper
  `convDensityAdd_deriv_hasDerivAt_self`;
- supplies the three integrability hyps from the **entropy-finiteness wall** (`huv'`/`huv` =
  `EntropyConvFinite.convDensityAdd_logFactor_deriv2_integrable` / `_deriv_integrable`) and the
  **Fisher-finiteness wall** (`hu'v` from `convDensityAdd_fisher_integrable`, via the genuine
  pointwise identity `u'·v = -((logDeriv p_t)²·p_t)` using `hp_pos`);
- applies `debruijn_ibp_step` and reconciles RHS `-∫ u'·v = ∫ (logDeriv p_t)²·p_t` by
  `integral_congr_ae` (same genuine pointwise identity).

`hpX_nn`/`hpX_meas`/`hpX_int`/`hpX_mass` are pure pX regularity preconditions (`hpX_mass`:
unit mass, used for strict positivity); the IBP equality is the genuine claim. No load-bearing
hypothesis bundled. The remaining honest `sorry`s are localized in: (a) the `plan:` arm — the two
deriv-existence helpers `convDensityAdd_hasDerivAt_self` / `convDensityAdd_deriv_hasDerivAt_self`
are now **genuinely closed** (`@audit:ok`, 0 sorry), so the live `plan:` residual is the per-`x`
heat-equation domination plumbing in `debruijnIdentityV2_holds_assembled_chain_hdiff` (`:2088`,
in-tree machinery, NOT a Mathlib gap); (b) the entropy-finiteness wall (`EntropyConvFinite.lean`);
(c) the Fisher-finiteness wall (`convDensityAdd_fisher_integrable`). The transitive marker is
compound (AND of the plan + the two walls).

Independent honesty audit (2026-05-31, fresh auditor, commit `d5951a5`): honest_residual
(transitive). 0 local sorry confirmed (`lake env lean` shows no `sorry` warning at this decl;
only B helpers `:1629`/`:1649` warn). `debruijn_ibp_step` application genuine: u/v/u'/v'
identified, `hp_pos` discharged via `convDensityAdd_pos` with `0 < ∫ pX = 1` from `hpX_mass`;
`hu`/`hv` via the deriv-existence helpers + `Real.hasDerivAt_log`; the pointwise identity
`u'·v = -((logDeriv p_t)²·p_t)` is derived once (`field_simp` using `hp_pos`), genuine; `hu'v`
supplied from the Fisher wall via `.neg.congr` on that identity; RHS reconciled by
`integral_congr_ae` on the same identity. NOT name-laundering: `hpX_mass` is unit-mass
regularity (used only to discharge `convDensityAdd_pos`'s `0 < ∫ pX`), conclusion is the
original IBP equality unchanged. Compound `@residual` correctly reflects the AND of the plan
+ the entropy-finiteness wall (`huv'`/`huv`) + the Fisher-finiteness wall (`hu'v`). Carries
`@residual` not `@audit:ok` (transitive sorry, honest). NOT circular, NOT load-bearing.

Re-audit (2026-06-01, fresh auditor, commits `e0e81ba`/`c7df95f`): the deriv-existence helpers
`hu`/`hv` are now genuinely closed (`@audit:ok`).

**Wave 4b correction (2026-06-01)**: the `plan:epi-debruijn-pertime-closure` arm was a
misattribution — this declaration's body (`debruijn_ibp_step` + the entropy-finiteness +
Fisher-finiteness wall lemmas) does NOT call `debruijnIdentityV2_holds_assembled_chain_hdiff`
(verified by reading the body: it uses `convDensityAdd_logFactor_deriv/deriv2_integrable` from
`EntropyConvFinite`, `convDensityAdd_fisher_integrable`, and `debruijn_ibp_step`). With
`_chain_hdiff` now closed anyway, the remaining transitive `sorryAx` is exclusively the two
Mathlib walls. The stale `plan:` component is dropped.
@residual(wall:entropy-finiteness,wall:fisher-finiteness) -/
private theorem debruijnIdentityV2_holds_assembled_chain_ibp_fisher_ibp_step
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {t : ℝ} (ht : 0 < t) :
    ∫ x, (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x ∂volume
      = ∫ x, (logDeriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x)^2
        * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x ∂volume := by
  -- abbreviate the time-`t` convolution density.
  set p_t : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hp_t
  -- STEP 2: strict positivity of `p_t` (genuine; `0 < ∫ pX = 1` from `hpX_mass`).
  have hp_pos : ∀ x, 0 < p_t x := fun x =>
    convDensityAdd_pos pX hpX_nn hpX_int (by rw [hpX_mass]; norm_num) ht x
  -- IBP quadruple: u, v, u', v'.
  set u : ℝ → ℝ := fun x => - Real.log (p_t x) - 1 with hu_def
  set v : ℝ → ℝ := deriv p_t with hv_def
  set u' : ℝ → ℝ := fun x => - logDeriv p_t x with hu'_def
  set v' : ℝ → ℝ := deriv (deriv p_t) with hv'_def
  -- STEP 3: `hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x` — proved for all `x`.
  have hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x := by
    intro x _
    -- `HasDerivAt p_t (deriv p_t x) x` from the differentiability helper.
    have hpt_diff : HasDerivAt p_t (deriv p_t x) x :=
      convDensityAdd_hasDerivAt_self pX hpX_nn hpX_meas hpX_int ht x
    -- `HasDerivAt (log ∘ p_t) (deriv p_t x / p_t x) x` via `Real.hasDerivAt_log`.
    have hlog : HasDerivAt (fun x => Real.log (p_t x)) (deriv p_t x / p_t x) x := by
      have := (Real.hasDerivAt_log (hp_pos x).ne').comp x hpt_diff
      simpa [one_div, div_eq_mul_inv, mul_comm] using this
    -- `u x = - log (p_t x) - 1`, `u' x = - logDeriv p_t x = - (deriv p_t x / p_t x)`.
    have : HasDerivAt u (-(deriv p_t x / p_t x)) x := by
      simpa [hu_def] using (hlog.neg.sub_const 1)
    have hu'_eq : u' x = -(deriv p_t x / p_t x) := by
      rw [hu'_def]; simp [logDeriv]
    rw [hu'_eq]; exact this
  -- STEP 3': `hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x` — proved for all `x`.
  have hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x := by
    intro x _
    rw [hv_def, hv'_def]
    exact convDensityAdd_deriv_hasDerivAt_self pX hpX_nn hpX_meas hpX_int ht x
  -- STEP 4: the three integrability preconditions.
  -- `huv' = Integrable (u * v')`: entropy-finiteness wall.
  have huv' : Integrable (u * v') := by
    simpa only [Pi.mul_def, hu_def, hv'_def, hp_t] using
      InformationTheory.Shannon.EntropyConvFinite.convDensityAdd_logFactor_deriv2_integrable
        pX hpX_nn hpX_meas hpX_int ht
  -- `huv = Integrable (u * v)`: entropy-finiteness wall.
  have huv : Integrable (u * v) := by
    simpa only [Pi.mul_def, hu_def, hv_def, hp_t] using
      InformationTheory.Shannon.EntropyConvFinite.convDensityAdd_logFactor_deriv_integrable
        pX hpX_nn hpX_meas hpX_int ht
  -- `hu'v = Integrable (u' * v)`: from the Fisher-finiteness wall (`(logDeriv)²·p_t`),
  --   since `u' x · v x = - logDeriv p_t x · deriv p_t x = -((logDeriv p_t x)²·p_t x)`.
  have hfisher := convDensityAdd_fisher_integrable pX hpX_nn hpX_meas hpX_int ht
  -- pointwise identity `u' x · v x = -((logDeriv p_t x)² · p_t x)`, derived once.
  have hpt_pointwise : ∀ x, (u' * v) x
      = -(logDeriv p_t x ^ 2 * p_t x) := by
    intro x
    have hpx := (hp_pos x).ne'
    simp only [Pi.mul_apply, hu'_def, hv_def, logDeriv, Pi.div_apply]
    field_simp
  have hu'v : Integrable (u' * v) := by
    refine (hfisher.neg).congr ?_
    filter_upwards with x
    rw [Pi.neg_apply, hpt_pointwise x]
  -- STEP 5: apply the IBP atom and reconcile.
  have hibp := debruijn_ibp_step u v u' v' hu hv huv' hu'v huv
  -- LHS of the goal = `∫ u x * v' x`; RHS of `hibp` = `- ∫ u' x * v x`.
  rw [show (∫ x, (- Real.log (p_t x) - 1) * deriv (deriv p_t) x ∂volume)
        = ∫ x, u x * v' x ∂volume from rfl, hibp]
  -- `- ∫ u' x * v x = ∫ (logDeriv p_t x)² * p_t x`.
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [show u' x * v x = (u' * v) x from rfl, hpt_pointwise x, neg_neg]

/-- **§5G-4: IBP + Fisher value match (L-PT-δ) — genuine plumbing over 2 named walls.**
The integrated entropy-derivative equals half the Fisher info of `pPath t`. de Bruijn IBP
(`debruijn_ibp_step`) moves the spatial-2nd-derivative factor onto the `negMulLog'` factor
`(- log p - 1)`, yielding `∫ (∂_x p)²/p = ∫ (logDeriv p)²·p`, identified with
`fisherInfoOfDensityReal` via `fisher_from_logDeriv`.

**§Phase 5-G case B split (2026-05-31, 案 B)**: the former monolithic body sorry is **factored**
into two named walls + genuine plumbing (0 local sorry). The body now:
(1) rewrites `∫ entDeriv` to `∫ (- log p_t - 1)·((1/2)·∂²_x p_t)` via the a.e. pin `hentDeriv`;
(2) pulls out the `(1/2)` constant (`integral_const_mul` after an a.e. `ring` congr); (3) applies
the **IBP step wall** `_chain_ibp_fisher_ibp_step` (de Bruijn IBP, `plan:` — `debruijn_ibp_step`
atom + tsupport=ℝ + integrability); (4) applies `fisher_from_logDeriv` (atom `@audit:ok`) with its
integrability hyp supplied by the **Fisher integrability wall** `convDensityAdd_fisher_integrable`
(`wall:fisher-finiteness` — Stam convolution Fisher bound `J(X+Z)≤J(Z)=1/t`, Mathlib/repo absent).
The `p_t ≥ 0` precondition of `fisher_from_logDeriv` is `convDensityAdd` nonnegativity
(`integral_nonneg` + `hpX_nn` + `gaussianPDFReal_nonneg`, mirrors `_entropy_eq:293`).

`hentDeriv` pins `entDeriv` to the §5G-1 closed form (integrand-level identification, not the
conclusion). The Fisher-equality conclusion is the genuine claim. The remaining honest `sorry`s
are localized in the 2 named walls above (no local sorry here).

Independent honesty audit (2026-05-31, fresh auditor, 案 B split commit): verdict
honest_residual (transitive). 0 local sorry — the former monolithic body sorry is genuinely
removed: the body is `integral_congr_ae hentDeriv` + `integral_const_mul` + the 2 named-wall
rewrites (`_ibp_step` + `fisher_from_logDeriv` fed by `convDensityAdd_fisher_integrable`), all
genuine plumbing. `#print axioms` shows `sorryAx` only via the 2 walls (`fisher_from_logDeriv`
verified sorryAx-free; `integral_congr_ae`/`integral_const_mul` are Mathlib std). `fisher_from_logDeriv`'s
`hp_nn` is discharged genuinely (`integral_nonneg` + `hpX_nn` + `gaussianPDFReal_nonneg`) and its
`hint` is the Fisher-finiteness wall verbatim — a regularity precondition, NOT a bundled
conclusion (core-reconstruction test: granting `hentDeriv` alone does not hand over `∫ entDeriv =
(1/2)·fisher`; the two walls supply the substance). NOT circular, NOT load-bearing, NOT
name-laundering (carries `@residual`, not `@audit:ok`).

**Wave 4b correction (2026-06-01)**: the `plan:epi-debruijn-pertime-closure` component was stale
— this body calls only `_chain_ibp_fisher_ibp_step` (entropy + Fisher walls) +
`fisher_from_logDeriv` + `convDensityAdd_fisher_integrable` (Fisher wall), NOT `_chain_hdiff`
(now closed anyway). The transitive `sorryAx` is exclusively the two Mathlib walls.
@residual(wall:fisher-finiteness,wall:entropy-finiteness) -/
private theorem debruijnIdentityV2_holds_assembled_chain_ibp_fisher
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {t : ℝ} (ht : 0 < t)
    (entDeriv : ℝ → ℝ)
    (hentDeriv : ∀ᵐ x ∂volume, entDeriv x =
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * ((1/2) * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x)) :
    ∫ x, entDeriv x ∂volume
      = (1/2) * fisherInfoOfDensityReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) := by
  -- abbreviate the time-`t` convolution density.
  set p_t := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hp_t
  -- `p_t ≥ 0` (convolution of nonneg pX with nonneg Gaussian PDF).
  have hp_nn : ∀ x, 0 ≤ p_t x := by
    intro x
    rw [hp_t]
    exact integral_nonneg fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  -- (1) rewrite `∫ entDeriv` to `∫ (1/2)·((- log p_t - 1)·∂²_x p_t)` via the a.e. pin
  --     `hentDeriv` (and `ring` to move the `(1/2)` to the front).
  have hstep1 : ∫ x, entDeriv x ∂volume
      = ∫ x, (1/2) * ((- Real.log (p_t x) - 1) * deriv (deriv p_t) x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hentDeriv] with x hx
    rw [hx]; ring
  -- (2) pull out the `(1/2)` constant.
  rw [hstep1, integral_const_mul]
  -- (3) IBP step wall: `∫ (- log p_t - 1)·∂²_x p_t = ∫ (logDeriv p_t)²·p_t`.
  rw [debruijnIdentityV2_holds_assembled_chain_ibp_fisher_ibp_step pX hpX_nn hpX_meas hpX_int hpX_mass ht]
  -- (4) Fisher value: `∫ (logDeriv p_t)²·p_t = fisherInfoOfDensityReal p_t`,
  --     integrability supplied by the Fisher-finiteness wall.
  rw [fisher_from_logDeriv p_t hp_nn
    (convDensityAdd_fisher_integrable pX hpX_nn hpX_meas hpX_int ht)]

/-- **§5G-3 hdiff plumbing (a.e.-over-Ioo per-`x` chain-rule) — GENUINELY CLOSED (0 sorry).**
The per-`x`, per-`s∈Ioo (t/2)(2*t)` chain-rule derivative of the entropy integrand
`fun s => negMulLog (pPath s x)`, with value the §5G-1 closed form
`entDerivFn s x = (- log (pPath s x) - 1)·((1/2)·∂²_x pPath_s x)`, where
`pPath s x = convDensityAdd pX g_{max s 0} x`.

This is the `hdiff` precondition of the parametric-diff atom `entropy_hasDerivAt_via_parametric`.
The genuine derivation route is, for each `(x, s∈Ioo)`:
(1) §5G-1 `_chain_entDeriv_formula` (the negMulLog chain rule, `@audit:ok`), fed the σ-derivative
    witness `hpath_deriv : HasDerivAt (fun σ => convDensityAdd pX g_{max σ 0} x) ((1/2)·∂²_x p_s x) s`;
(2) that σ-derivative from `heatFlow_density_heat_equation` (`@audit:ok` atom), whose 11
    integrand-level Gaussian-tail domination hyps plus the two deriv pins
    (`convDensityAdd_hasDerivAt_self` / `convDensityAdd_deriv_hasDerivAt_self`, `@audit:ok`) are
    supplied per-`x`.

**Closure (2026-06-01, Wave 4b)**: the former monolithic `sorry` is now fully discharged.
- The two deriv pins `hpathDeriv1`/`hpathDeriv2` are built by σ-case-split: for `σ > 0` the
  `max σ 0 = σ` reconciliation (`NNReal.eq`+`max_eq_left`) lets the Wave-4a deriv-existence
  helpers `convDensityAdd_hasDerivAt_self` / `convDensityAdd_deriv_hasDerivAt_self` (`@audit:ok`)
  apply; for `σ ≤ 0` the path `pPath σ = convDensityAdd pX g_0 = 0` (since `gaussianPDFReal 0 0 = 0`,
  `gaussianPDFReal_zero_var`) is the zero constant, so the derivs are 0 (`hasDerivAt_const`).
- The 11 heat-eq domination hyps are discharged genuinely: the σ-direction group via the
  `s`-uniform Gaussian-Hessian majorant `gaussHessMaj s` at base `s` (the σ-window `Ioo (s/2)(2s)`
  is exactly `gaussianHess_le_gaussHessMaj`'s window with `t := s`); the two spatial-direction
  groups via the fixed-`s` global kernel bounds `kernel_x_deriv1/2_global_bound` (`@audit:ok`,
  `bound = |pX|·M`, integrable via `Integrable.mul_const` / `mul_bdd`) — the same template as
  the Wave-4a helpers.
- The chain rule (B+C) composes via `_chain_entDeriv_formula` with the `max s 0 = s` log-factor
  reconciliation; `pathDeriv2 s x` is defeq to the goal's `deriv (deriv (g_{max s 0})) x`.

`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-verified;
no transitive `sorryAx`). The conclusion is an integrand-level derivative-existence statement —
NOT the composed `HasDerivAt`-of-the-integral, NOT hyp-bundled. All hyps pX regularity. -/
private theorem debruijnIdentityV2_holds_assembled_chain_hdiff
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂volume, ∀ s ∈ Set.Ioo (t/2) (2*t),
      HasDerivAt
        (fun s => Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x))
        ((- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) - 1)
          * ((1/2) * deriv (deriv (convDensityAdd pX
              (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩))) x)) s := by
  classical
  -- positive mass from `∫ pX = 1` (for `convDensityAdd_pos`).
  have hpX_pos : 0 < ∫ y, pX y ∂volume := by rw [hpX_mass]; norm_num
  -- the heat-flow path and its two spatial derivatives, in `max σ 0` form.
  set pPath : ℝ → ℝ → ℝ :=
    fun σ => convDensityAdd pX (gaussianPDFReal 0 ⟨max σ 0, le_max_right σ 0⟩) with hpPath_def
  set pathDeriv1 : ℝ → ℝ → ℝ := fun σ y => deriv (pPath σ) y with hpathDeriv1_def
  set pathDeriv2 : ℝ → ℝ → ℝ := fun σ y => deriv (deriv (pPath σ)) y with hpathDeriv2_def
  -- definitional pin: on `σ > 0`, `max σ 0 = σ`, so `pPath σ = convDensityAdd pX g_σ`.
  have hpPath_pos : ∀ (σ : ℝ) (hσ : 0 < σ),
      pPath σ = convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩) := by
    intro σ hσ
    show convDensityAdd pX (gaussianPDFReal 0 ⟨max σ 0, le_max_right σ 0⟩)
      = convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩)
    have : (⟨max σ 0, le_max_right σ 0⟩ : ℝ≥0) = ⟨σ, hσ.le⟩ := by
      apply NNReal.eq; exact max_eq_left hσ.le
    rw [this]
  -- definitional pin (degenerate σ ≤ 0): `pPath σ = 0` (const).
  have hpPath_nonpos : ∀ (σ : ℝ), σ ≤ 0 → pPath σ = fun _ => (0 : ℝ) := by
    intro σ hσ
    show convDensityAdd pX (gaussianPDFReal 0 ⟨max σ 0, le_max_right σ 0⟩)
      = fun _ => (0 : ℝ)
    have hmax : (⟨max σ 0, le_max_right σ 0⟩ : ℝ≥0) = 0 := by
      apply NNReal.eq
      show max σ 0 = (0 : ℝ)
      exact max_eq_right hσ
    rw [hmax]
    funext z
    show (∫ y, pX y * gaussianPDFReal 0 0 (z - y) ∂volume) = 0
    have hzero : (fun y => pX y * gaussianPDFReal 0 0 (z - y)) = fun _ => (0 : ℝ) := by
      funext y; rw [gaussianPDFReal_zero_var]; simp
    rw [hzero, integral_zero]
  -- pin `hpathDeriv1`: spatial 1st derivative of `pPath σ`, for ALL σ.
  have hpathDeriv1 : ∀ σ y : ℝ, HasDerivAt (fun ξ => pPath σ ξ) (pathDeriv1 σ y) y := by
    intro σ y
    show HasDerivAt (fun ξ => pPath σ ξ) (deriv (pPath σ) y) y
    rcases le_or_gt σ 0 with hσ | hσ
    · -- σ ≤ 0: `pPath σ` is the zero function; deriv is 0.
      rw [hpPath_nonpos σ hσ]
      simpa using hasDerivAt_const y (0 : ℝ)
    · -- σ > 0: use the Wave-4a deriv-existence helper.
      rw [hpPath_pos σ hσ]
      exact convDensityAdd_hasDerivAt_self pX hpX_nn hpX_meas hpX_int hσ y
  -- pin `hpathDeriv2`: spatial 2nd derivative of `pPath σ`, for ALL σ.
  have hpathDeriv2 : ∀ σ y : ℝ, HasDerivAt (fun ξ => pathDeriv1 σ ξ) (pathDeriv2 σ y) y := by
    intro σ y
    show HasDerivAt (fun ξ => deriv (pPath σ) ξ) (deriv (deriv (pPath σ)) y) y
    rcases le_or_gt σ 0 with hσ | hσ
    · -- σ ≤ 0: `pPath σ = 0`, so `deriv (pPath σ) = 0` and the 2nd deriv is 0.
      have hd1 : deriv (pPath σ) = fun _ => (0 : ℝ) := by
        funext ξ; rw [hpPath_nonpos σ hσ]; simp
      rw [hd1]
      simpa using hasDerivAt_const y (0 : ℝ)
    · -- σ > 0: differentiate `deriv (pPath σ) = deriv (convDensityAdd pX g_σ)`.
      have hfun : (fun ξ => deriv (pPath σ) ξ)
          = deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩)) := by
        rw [hpPath_pos σ hσ]
      rw [hfun]
      have hval : deriv (deriv (pPath σ)) y
          = deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩))) y := by
        rw [hpPath_pos σ hσ]
      rw [hval]
      exact convDensityAdd_deriv_hasDerivAt_self pX hpX_nn hpX_meas hpX_int hσ y
  -- the per-`x`, per-`s` derivative is now obtained by combining the heat-eq atom
  -- (σ-derivative) with the §5G-1 negMulLog chain rule.
  refine Filter.Eventually.of_forall (fun x s hs => ?_)
  have hspos : (0:ℝ) < s := by have := hs.1; linarith
  -- kernel continuity / measurability (shared by the domination groups).
  have hker_cont : Continuous (fun u : ℝ => heatFlow_density_heat_equation_kernel s u) := by
    unfold heatFlow_density_heat_equation_kernel; fun_prop
  have hker_meas : Measurable (fun u : ℝ => heatFlow_density_heat_equation_kernel s u) :=
    hker_cont.measurable
  -- the kernel uniform sup bound `|kernel s v| ≤ (√(2πs))⁻¹`.
  have hker_le : ∀ v : ℝ, |heatFlow_density_heat_equation_kernel s v|
      ≤ (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹ := by
    intro v
    rw [heatFlow_density_heat_equation_kernel_eq hspos v,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 _ v)]
    exact gaussianPDFReal_le_prefactor' ⟨s, hspos.le⟩ v
  -- spatial 1st/2nd-derivative global-bound constants.
  set Mξ1 : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ * ((1 + 2 * s * Real.exp (-1)) / (2 * s)) with hMξ1
  set Mξ2 : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ * ((2 * Real.exp (-1) + 1) / s) with hMξ2
  -- (A) σ-derivative pin from `heatFlow_density_heat_equation`.
  have hpath_deriv : HasDerivAt (fun σ => pPath σ x) ((1/2) * pathDeriv2 s x) s := by
    refine heatFlow_density_heat_equation pX pPath pathDeriv1 pathDeriv2
      hpPath_pos hpathDeriv1 hpathDeriv2 hspos x
      ?boundσ ?hboundσ_int ?hFσ_meas ?hFσ_int ?hFσ'_meas ?hbσ
      ?boundξ1 ?hboundξ1_int ?hFξ1_meas ?hFξ1_int ?hFξ1'_meas ?hbξ1
      ?boundξ2 ?hboundξ2_int ?hFξ2_int ?hFξ2'_meas ?hbξ2
    -- σ-direction domination (`s`-uniform Gaussian-Hessian majorant `gaussHessMaj s`,
    -- whose σ-window `Ioo (s/2)(2s)` matches `gaussianHess_le_gaussHessMaj` at base `s`).
    case boundσ => exact fun y => pX y * gaussHessMaj s (x - y)
    case hboundσ_int =>
      -- `pX · (bounded gaussHessMaj s)` integrable via `mul_bdd`.
      refine hpX_int.mul_bdd
        (c := (Real.sqrt (Real.pi * s))⁻¹ * (16 * Real.exp (-1) / s + 2 / s)) ?_ ?_
      · refine (Measurable.aestronglyMeasurable ?_)
        have hM : Measurable (gaussHessMaj s) := by unfold gaussHessMaj; fun_prop
        exact hM.comp (measurable_const.sub measurable_id)
      · refine Filter.Eventually.of_forall (fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (gaussHessMaj_nonneg hspos (x - y))]
        exact gaussHessMaj_bdd hspos (x - y)
    case hFσ_meas =>
      -- a.e.-strong measurability of `y ↦ pX y · kernel σ (x-y)` for σ near `s`.
      refine Filter.Eventually.of_forall (fun σ => ?_)
      exact (hpX_meas.aestronglyMeasurable).mul
        (((show Measurable (fun u : ℝ => heatFlow_density_heat_equation_kernel σ u) by
            unfold heatFlow_density_heat_equation_kernel; fun_prop).comp
          (measurable_const.sub measurable_id)).aestronglyMeasurable)
    case hFσ_int =>
      refine hpX_int.mul_bdd
        (c := (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
      · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun y => by
          rw [Real.norm_eq_abs]; exact hker_le (x - y))
    case hFσ'_meas =>
      refine (hpX_meas.aestronglyMeasurable).mul ?_
      refine AEStronglyMeasurable.const_mul ?_ _
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      · exact (((measurable_const.sub measurable_id).pow_const 2).div_const _).sub
          measurable_const |>.aestronglyMeasurable
    case hbσ =>
      -- `‖pX y · (1/2)·(kernel σ ·(…))‖ ≤ pX y · gaussHessMaj s (x-y)` on σ ∈ Ioo(s/2,2s).
      refine Filter.Eventually.of_forall (fun y σ hσ => ?_)
      have hσpos : (0:ℝ) < σ := by have := hσ.1; linarith
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hpX_nn y)]
      apply mul_le_mul_of_nonneg_left _ (hpX_nn y)
      -- the kernel equals the Gaussian pdf for σ>0; reuse the s-uniform Hessian majorant at base `s`.
      rw [heatFlow_density_heat_equation_kernel_eq hσpos (x - y)]
      have hmaj := gaussianHess_le_gaussHessMaj hspos hσ (x - y)
      -- `‖(1/2)·(g_σ·(…))‖ = (1/2)·g_σ·|…| ≤ (1/2)·gaussHessMaj s ≤ gaussHessMaj s`.
      have hg_nn : 0 ≤ gaussianPDFReal 0 ⟨σ, le_of_lt (by have := hσ.1; linarith : (0:ℝ) < σ)⟩ (x - y) :=
        gaussianPDFReal_nonneg 0 _ _
      have hgM_nn : 0 ≤ gaussHessMaj s (x - y) := gaussHessMaj_nonneg hspos (x - y)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      have habs : |gaussianPDFReal 0 ⟨σ, hσpos.le⟩ (x - y) * ((x - y) ^ 2 / σ ^ 2 - 1 / σ)|
          = gaussianPDFReal 0 ⟨σ, hσpos.le⟩ (x - y) * |(x - y) ^ 2 / σ ^ 2 - 1 / σ| := by
        rw [abs_mul, abs_of_nonneg hg_nn]
      rw [habs]
      calc 1 / 2 * (gaussianPDFReal 0 ⟨σ, hσpos.le⟩ (x - y) * |(x - y) ^ 2 / σ ^ 2 - 1 / σ|)
          ≤ 1 / 2 * gaussHessMaj s (x - y) := by
            apply mul_le_mul_of_nonneg_left hmaj (by norm_num)
        _ ≤ gaussHessMaj s (x - y) := by linarith [hgM_nn]
    -- spatial-direction domination (fixed-s global bounds, Wave-4a route).
    case boundξ1 => exact fun y => |pX y| * Mξ1
    case hboundξ1_int => exact hpX_int.abs.mul_const _
    case hFξ1_meas =>
      intro ξ
      exact (hpX_meas.aestronglyMeasurable).mul
        ((hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
    case hFξ1_int =>
      intro ξ
      refine hpX_int.mul_bdd
        (c := (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
      · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun y => by
          rw [Real.norm_eq_abs]; exact hker_le (ξ - y))
    case hFξ1'_meas =>
      intro ξ
      refine (hpX_meas.aestronglyMeasurable).mul ?_
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      · exact ((measurable_const.sub measurable_id).div_const s).neg.aestronglyMeasurable
    case hbξ1 =>
      refine Filter.Eventually.of_forall (fun y ξ _ => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have := kernel_x_deriv1_global_bound hspos (ξ - y)
      rwa [hMξ1]
    case boundξ2 => exact fun y => |pX y| * Mξ2
    case hboundξ2_int => exact hpX_int.abs.mul_const _
    case hFξ2_int =>
      have hbound_int : Integrable (fun y => |pX y| * Mξ1) volume := hpX_int.abs.mul_const _
      refine hbound_int.mono' ?_ (Filter.Eventually.of_forall (fun y => ?_))
      · refine (hpX_meas.aestronglyMeasurable).mul ?_
        refine AEStronglyMeasurable.mul ?_ ?_
        · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
        · exact ((measurable_const.sub measurable_id).div_const s).neg.aestronglyMeasurable
      · rw [norm_mul, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have := kernel_x_deriv1_global_bound hspos (x - y)
        rwa [hMξ1]
    case hFξ2'_meas =>
      refine (hpX_meas.aestronglyMeasurable).mul ?_
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      · exact (((measurable_const.sub measurable_id).pow_const 2).div_const _).sub
          measurable_const |>.aestronglyMeasurable
    case hbξ2 =>
      refine Filter.Eventually.of_forall (fun y ξ _ => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have := kernel_x_deriv2_global_bound hspos (ξ - y)
      rwa [hMξ2]
  -- (B+C) chain rule: pin the `max s 0 = s` reconciliation then apply §5G-1.
  have hmaxs : (⟨max s 0, le_max_right s 0⟩ : ℝ≥0) = ⟨s, hspos.le⟩ := by
    apply NNReal.eq; exact max_eq_left hspos.le
  have hpos : convDensityAdd pX (gaussianPDFReal 0 ⟨s, hspos.le⟩) x ≠ 0 :=
    (convDensityAdd_pos pX hpX_nn hpX_int hpX_pos hspos x).ne'
  -- `hpath_deriv : HasDerivAt (fun σ => pPath σ x) D s`; since `pPath σ x = conv g_{max σ 0} x`
  -- definitionally, this is exactly the `hpath_deriv` shape §5G-1 expects.
  have hchain := debruijnIdentityV2_holds_assembled_chain_entDeriv_formula
    pX hspos x ((1/2) * pathDeriv2 s x) hpos hpath_deriv
  -- `hchain` value: `(- log (conv g_{⟨s,_⟩} x) - 1) * ((1/2)·pathDeriv2 s x)`.
  -- goal value: `(- log (conv g_{max s 0} x) - 1) * ((1/2)·deriv(deriv(conv g_{max s 0})) x)`.
  -- the log factor: rewrite `⟨s,_⟩ → ⟨max s 0,_⟩` in hchain; `pathDeriv2 s x` is defeq to the
  -- goal's deriv-deriv form.
  rw [← hmaxs] at hchain
  exact hchain

/-- **§5G-3: parametric-diff composition.**
The entropy integral `∫ negMulLog (pPath s ·)` has its `s`-derivative at `t` given by the
integral of `entDeriv` (the §5G-1 per-`x` closed form), and that integral equals
`(1/2)·fisherInfoOfDensityReal (pPath t)`. Composes `entropy_hasDerivAt_via_parametric` (atom,
now neighborhood-version: `hb`/`hdiff` quantified over `Set.Ioo (t/2)(2*t)`, requires `0 < t`)
with §5G-1 (per-`x` chain rule), §5G-2 (full-entDeriv Ioo domination), §5G-4 (Fisher value). The
`HasDerivAt` and Fisher-value conclusions are genuine claims; they are NOT supplied as
hypotheses.

**§Phase 5-G case C wiring (2026-05-31, §5G-3 配線完了)**: the former monolithic body `sorry`
is **factored** into a genuine `entropy_hasDerivAt_via_parametric` (`@audit:ok` atom) application
+ named residuals (0 local sorry). The existential output `entDeriv` is the §5G-1 per-`x` closed
form `entDerivFn t x = (- log p_t x - 1)·((1/2)·∂²_x p_t x)` (kept in `max s 0` form so the
被微分関数 matches `_chain` verbatim; `max s 0 = s` on the `Ioo (t/2)(2*t)` neighborhood). The body:

- **first goal** (`HasDerivAt`): applies the Ioo-version atom `entropy_hasDerivAt_via_parametric`,
  supplying its 6 preconditions —
  · `hbound_int` / `hb` from §5G-2 `_chain_domination` (proof-done envelope, `@audit:ok`), with the
    `max s 0 = s` reconciliation on `Ioo` (each `s > 0`);
  · `hint` from the entropy-finiteness wall `convDensityAdd_negMulLog_integrable`
    (`wall:entropy-finiteness`), moved to the `g_{max t 0}` form via `max t 0 = t`;
  · `hmeas` / `hderiv_meas` **genuine** (joint-measurable convolution integrand + `negMulLog`/`log`
    composition + `measurable_deriv`, all Mathlib std — mirrors `convDensityAdd_fisher_integrable`'s
    `hpt_meas` route);
  · `hdiff` from the named honest-sorry helper `_chain_hdiff` (a.e.-over-Ioo §5G-1 chain rule +
    heat-eq atom domination plumbing, `plan:`).
- **second goal** (Fisher value): applies §5G-4 `_chain_ibp_fisher` (genuine plumbing over the
  Fisher + entropy walls), with `hentDeriv` pinning `entDerivFn t` to the `⟨t,_⟩`-form integrand a.e.
  (definitional `max t 0 = t` reconciliation).

The `HasDerivAt` + Fisher-value conclusions are the genuine claims, NOT bundled into hypotheses.
The remaining honest `sorry` is localized in `_chain_hdiff` (named, `plan:`); the file-level
residual grep still reflects this declaration's transitive dependency on §5G-2, §5G-3, §5G-4.

`hpX_mass:∫pX=1` and `hpX_mom : Integrable (fun y => y²·pX y) volume` are honest regularity
preconditions (unit mass + finite second moment / variance of `X`), threaded purely to supply
the §5G-2 domination's GAP① normalization and route-II Tonelli even-moment envelope; they do NOT
change the residual's meaning.

Independent honesty audit (2026-05-31, Wave fresh auditor, commit `20ecddc`): honest_residual.
Body has **0 local sorry** (machine-confirmed: only `_chain_hdiff`/deriv-helpers carry sorry warnings,
not this decl); sorryAx dependency is purely transitive. The `entropy_hasDerivAt_via_parametric` atom
(PerTime:659, `#print axioms` sorryAx-free) application is sound: arg order matches signature, `hint`
from entropy-finiteness wall + `hb` from `_chain_domination` reconciled genuinely via `max s 0 = s`
(`NNReal.eq`+`max_eq_left`, `s>0` on `Ioo` by linarith); `hmeas`/`hderiv_meas` genuine (Mathlib std
joint-measurability + `measurable_deriv`, no sorry/admit); 2nd goal `_chain_ibp_fisher` applied with
`hentDeriv` pin (`max t 0 = t`) — genuine. Conclusion `∃ entDeriv, HasDerivAt ∧ ∫ = (1/2)·fisher` is
the genuine claim (NOT hyp-bundled, NOT weakened) — no name laundering. `@residual` correctly
maintained (transitive sorry present, not falsely `@audit:ok`).

**Wave 4b update (2026-06-01)**: `_chain_hdiff` (`hdiff` arm) is now genuinely closed (0 sorry,
sorryAx-free). The remaining transitive `sorryAx` is exclusively via `_chain_ibp_fisher`'s two
Mathlib walls `wall:fisher-finiteness` + `wall:entropy-finiteness`; the `plan:` component is
dropped as stale.
@residual(wall:fisher-finiteness,wall:entropy-finiteness) -/
private theorem debruijnIdentityV2_holds_assembled_chain_parametric
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∃ entDeriv : ℝ → ℝ,
      HasDerivAt
        (fun s => ∫ x, Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) ∂volume)
        (∫ x, entDeriv x ∂volume) t
      ∧ (∫ x, entDeriv x ∂volume
          = (1/2) * fisherInfoOfDensityReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) := by
  -- the §5G-1 per-`x` closed form `entDerivFn s x`, as a 2-arg function for the atom.
  set entDerivFn : ℝ → ℝ → ℝ := fun s x =>
    (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) - 1)
      * ((1/2) * deriv (deriv (convDensityAdd pX
          (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩))) x) with hentDerivFn
  -- the witness derivative is `entDerivFn t`.
  refine ⟨fun x => entDerivFn t x, ?_, ?_⟩
  · -- ===== first goal: the HasDerivAt, via the parametric-diff atom. =====
    -- §5G-2 domination: an integrable `bound` dominating `entDerivFn s` on `Ioo (t/2)(2*t)`.
    obtain ⟨bound, hbound_int, hb_dom⟩ :=
      debruijnIdentityV2_holds_assembled_chain_domination
        pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
    -- `max t 0 = t` reconciliation of the variance witness at the base point.
    have hmaxt : (⟨max t 0, le_max_right t 0⟩ : ℝ≥0) = ⟨t, ht.le⟩ := by
      apply NNReal.eq; exact max_eq_left ht.le
    -- abbreviate the path.
    set pPath : ℝ → ℝ → ℝ := fun s x =>
      convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x with hpPath
    -- `hint`: entropy-integrand integrability at `t` (entropy-finiteness wall), moved to
    --   the `pPath t = g_{max t 0}` form via `max t 0 = t`.
    have hint : Integrable (fun x => Real.negMulLog (pPath t x)) volume := by
      have h := InformationTheory.Shannon.EntropyConvFinite.convDensityAdd_negMulLog_integrable
        pX hpX_nn hpX_meas hpX_int ht
      refine h.congr ?_
      filter_upwards with x
      rw [hpPath]; simp only; rw [hmaxt]
    -- `hmeas`: a.e.-strong-measurability of the entropy integrand, for `s` near `t` (genuine).
    have hmeas : ∀ᶠ s in nhds t,
        AEStronglyMeasurable (fun x => Real.negMulLog (pPath s x)) volume := by
      refine Filter.Eventually.of_forall (fun s => ?_)
      -- `convDensityAdd pX g_{max s 0}` is measurable (joint-measurable integrand + Fubini).
      have hg_meas : Measurable (gaussianPDFReal 0 ⟨max s 0, le_max_right s 0⟩) :=
        measurable_gaussianPDFReal 0 _
      have hpath_meas : Measurable
          (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right s 0⟩)) := by
        have huncurry : StronglyMeasurable
            (Function.uncurry fun z x =>
              pX x * gaussianPDFReal 0 ⟨max s 0, le_max_right s 0⟩ (z - x)) := by
          apply Measurable.stronglyMeasurable
          apply (hpX_meas.comp measurable_snd).mul
          exact hg_meas.comp ((measurable_fst).sub measurable_snd)
        have h := huncurry.integral_prod_right (ν := volume)
        simpa only [convDensityAdd] using h.measurable
      exact (Real.continuous_negMulLog.measurable.comp hpath_meas).aestronglyMeasurable
    -- `hderiv_meas`: a.e.-strong-measurability of `entDerivFn t` (genuine).
    have hderiv_meas : AEStronglyMeasurable (entDerivFn t) volume := by
      have hg_meas : Measurable (gaussianPDFReal 0 ⟨max t 0, le_max_right t 0⟩) :=
        measurable_gaussianPDFReal 0 _
      have hpath_meas : Measurable
          (convDensityAdd pX (gaussianPDFReal 0 ⟨max t 0, le_max_right t 0⟩)) := by
        have huncurry : StronglyMeasurable
            (Function.uncurry fun z x =>
              pX x * gaussianPDFReal 0 ⟨max t 0, le_max_right t 0⟩ (z - x)) := by
          apply Measurable.stronglyMeasurable
          apply (hpX_meas.comp measurable_snd).mul
          exact hg_meas.comp ((measurable_fst).sub measurable_snd)
        have h := huncurry.integral_prod_right (ν := volume)
        simpa only [convDensityAdd] using h.measurable
      have hlog_meas : Measurable
          (fun x => - Real.log (convDensityAdd pX
            (gaussianPDFReal 0 ⟨max t 0, le_max_right t 0⟩) x) - 1) :=
        ((Real.measurable_log.comp hpath_meas).neg).sub_const 1
      have hd2_meas : Measurable
          (fun x => (1:ℝ)/2 * deriv (deriv (convDensityAdd pX
            (gaussianPDFReal 0 ⟨max t 0, le_max_right t 0⟩))) x) :=
        (measurable_deriv _).const_mul _
      exact (hlog_meas.mul hd2_meas).aestronglyMeasurable
    -- `hb`: §5G-2 domination, restated for `entDerivFn s` (= `max s 0` form). On `Ioo (t/2)(2*t)`
    --   each `s > 0` so `max s 0 = s`, matching `_chain_domination`'s `⟨s,_⟩` form.
    have hb : ∀ᵐ x ∂volume, ∀ s ∈ Set.Ioo (t/2) (2*t), ‖entDerivFn s x‖ ≤ bound x := by
      filter_upwards [hb_dom] with x hx
      intro s hs
      have hspos : (0:ℝ) < s := by have := hs.1; linarith
      have hmaxs : (⟨max s 0, le_max_right s 0⟩ : ℝ≥0) = ⟨s, hspos.le⟩ := by
        apply NNReal.eq; exact max_eq_left hspos.le
      have hbx := hx s hs
      rw [hentDerivFn]; simp only; rw [hmaxs]; exact hbx
    -- `hdiff`: §5G-3 hdiff plumbing (named honest sorry helper).
    have hdiff := debruijnIdentityV2_holds_assembled_chain_hdiff
      pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
    -- apply the parametric-diff atom (its `entDeriv` arg is `entDerivFn`, `pPath` arg is `pPath`).
    exact entropy_hasDerivAt_via_parametric pPath entDerivFn bound ht
      hbound_int hmeas hint hderiv_meas hb hdiff
  · -- ===== second goal: Fisher value, via §5G-4 `_chain_ibp_fisher`. =====
    -- the witness `entDeriv x = entDerivFn t x` equals the `⟨t,_⟩`-form §5G-1 integrand a.e.
    have hmaxt : (⟨max t 0, le_max_right t 0⟩ : ℝ≥0) = ⟨t, ht.le⟩ := by
      apply NNReal.eq; exact max_eq_left ht.le
    have hentDeriv : ∀ᵐ x ∂volume, entDerivFn t x =
        (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
          * ((1/2) * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x) := by
      filter_upwards with x
      rw [hentDerivFn]; simp only; rw [hmaxt]
    exact debruijnIdentityV2_holds_assembled_chain_ibp_fisher
      pX hpX_nn hpX_meas hpX_int hpX_mass ht (fun x => entDerivFn t x) hentDeriv

/-- **Assembly chain core (段 2-7, genuine plumbing over §5G sub-lemmas)**: given the
heat-flow density path `pPath s = convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩)` (the
convolution density of the law of `X + √s·Z`) with its X-density witness `pX`, the
`s`-derivative of the entropy `∫ negMulLog (pPath s ·)` at `t` equals
`(1/2) · fisherInfoOfDensityReal (pPath t)`.

After the §Phase 5-G sub-lemma split (2026-05-31), the former monolithic sorry is
**factored** into the 5 §5G sub-lemmas. The body of this lemma is now **genuine plumbing**
(§5G-5): it `obtain`s the entropy-derivative + value from `_chain_parametric` (§5G-3) and
rewrites — no local sorry. After the §5G wiring (2026-05-31), `_chain_domination` (§5G-2) and
`_chain_entDeriv_formula` (§5G-1) are genuine (proof-done / `@audit:ok`); `_chain_parametric`
(§5G-3) and `_chain_ibp_fisher` (§5G-4) are genuine plumbing (0 local sorry). The remaining
honest `sorry` + `@residual` are localized in the named leaf residuals only: `_chain_hdiff`
(§5G-3 hdiff, `plan:` heat-eq domination plumbing), the 2 deriv-existence helpers
(`convDensityAdd_hasDerivAt_self` / `_deriv_hasDerivAt_self`, `plan:`), the entropy-finiteness
wall (`EntropyConvFinite.lean`), and the Fisher-finiteness wall (`convDensityAdd_fisher_integrable`).

`pX`/`hpX_nn`/`hpX_meas`/`hpX_int` are pure regularity preconditions (X has a Lebesgue
density `pX`). The conclusion (`HasDerivAt … (1/2) · fisher`) is NOT bundled into a
hypothesis — it is the genuine claim, derived from the sub-lemmas once the regularity is
supplied. The `@residual` is transitive (the sorry now lives in the named §5G sub-lemmas),
kept here so the file-level residual grep still reflects this declaration's dependency.

**Wave 4b update (2026-06-01)**: `_chain_hdiff` (the former `plan:epi-debruijn-pertime-closure`
plumbing leaf) is now genuinely closed (0 sorry, `#print axioms` sorryAx-free). The remaining
transitive `sorryAx` of this declaration is now exclusively via the two Mathlib walls
`wall:fisher-finiteness` (`gaussianConv_fisher_le_inv_var`, FisherConvBound.lean) and
`wall:entropy-finiteness` (`EntropyConvFinite.lean`), used by `_chain_ibp_fisher`. The
`plan:` component is dropped as stale.
@residual(wall:fisher-finiteness,wall:entropy-finiteness) -/
private theorem debruijnIdentityV2_holds_assembled_chain
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s => ∫ x, Real.negMulLog
        (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) ∂volume)
      ((1/2) * fisherInfoOfDensityReal
        (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)))
      t := by
  -- §5G-5 body assembly: §5G-3 (`_parametric`) supplies the entropy-derivative and its
  -- value `= (1/2)·fisher`. The `max s 0` neighborhood correction is baked into the
  -- `_parametric` signature (integrand matches the `_chain` conclusion verbatim).
  obtain ⟨entDeriv, hderiv, hval⟩ :=
    debruijnIdentityV2_holds_assembled_chain_parametric pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
  rw [hval] at hderiv
  exact hderiv

/-- **Entropy ↔ ∫ negMulLog density bridge (段 1-2, honest sorry)**: along the heat-flow
path, the differential entropy of the pushforward equals the `∫ negMulLog` of the
convolution density, on a neighborhood of `t`, and the entropy function agrees
eventually with the `∫ negMulLog (convDensityAdd …)` function used by the chain core.

Concretely: for `s` near `t` (so `s > 0`),
`differentialEntropy (P.map (X + √s·Z)) = ∫ x, negMulLog (convDensityAdd pX g_s x)`.
This uses Phase 1b (`pPath_eq_convDensityAdd`, density identification) +
`differentialEntropy_eq_integral_density` (`DifferentialEntropy.lean:65`,
`negMulLog x = -(x log x)`). The gap is the a.e.-equality bookkeeping
(`rnDeriv =ᵐ ofReal∘convDensityAdd` → `differentialEntropy` integrand congr).

All hypotheses are regularity preconditions; the conclusion (an entropy/integral
equality) is NOT a `HasDerivAt` core.

Independent honesty audit (2026-05-31, Wave8 fresh auditor): verdict ok. Body is a
genuine `filter_upwards` + `integral_congr_ae` + `toReal_ofReal` derivation (no local
sorry). `#print axioms` confirms dependency `[propext, Classical.choice, Quot.sound]`
only (sorryAx-free, transitive 0 sorry). All hyps are regularity preconditions
(X/Z law/measurability + pX density data); the eventual-equality conclusion is not a
HasDerivAt core. proof-done. @audit:ok -/
private theorem debruijnIdentityV2_holds_assembled_entropy_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    {t : ℝ} (ht : 0 < t) :
    (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      =ᶠ[nhds t] (fun s => ∫ x, Real.negMulLog
        (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) ∂volume) := by
  -- on the neighborhood `s > 0` the two functions are equal pointwise.
  filter_upwards [eventually_gt_nhds ht] with s hs
  -- at `s > 0`: `max s 0 = s`.
  have hmax : max s 0 = s := max_eq_left hs.le
  -- Phase 1b: `rnDeriv (P.map (X+√s·Z)) =ᵐ ofReal∘convDensityAdd pX g_s`.
  have h1b := pPath_eq_convDensityAdd X Z hX hZ hXZ hZ_law pX hpX_nn hpX_meas hpX_law hs
  -- unfold differentialEntropy = ∫ negMulLog ((rnDeriv).toReal).
  unfold differentialEntropy
  -- rewrite the variance witness `⟨max s 0, _⟩` to `⟨s, hs.le⟩`.
  have hwit : (⟨max s 0, le_max_right s 0⟩ : ℝ≥0) = ⟨s, hs.le⟩ := by
    apply NNReal.eq; exact hmax
  rw [hwit]
  -- congr the two integrands a.e. via Phase 1b + `toReal_ofReal` (convDensityAdd ≥ 0).
  refine integral_congr_ae ?_
  filter_upwards [h1b] with x hx
  rw [hx]
  -- `negMulLog ((ofReal (convDensityAdd …)).toReal) = negMulLog (convDensityAdd …)`
  -- needs `convDensityAdd … x ≥ 0` (so `toReal_ofReal`).
  rw [ENNReal.toReal_ofReal]
  -- nonnegativity of `convDensityAdd pX g_s x = ∫ y, pX y · g_s (x-y)`.
  refine integral_nonneg (fun y => ?_)
  exact mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)

/-- **Fisher value match (段 1+7, genuine closure)**: the Fisher info of the time-`t`
convolution density `convDensityAdd pX g_t` equals the Fisher info of the structure's
density witness `density_t`.

With the **conv pin** (`density_t_eq`, conv-pin redesign §Phase 5-F 案 1), `density_t` is
pinned pointwise to the smooth convolution representative `convDensityAdd pX g_t`. So the
two functions are **equal** (`funext (hdensity_t_eq ht)`), and `fisherInfoOfDensityReal`
applied to the same function gives the same value. No a.e.-congruence gap remains — this
pointwise equality is exactly what the old rnDeriv pin could not supply (rnDeriv agrees
with the smooth conv only a.e.), and what makes this match genuine (0 sorry). -/
private theorem debruijnIdentityV2_holds_assembled_fisher_match
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (_hX : Measurable X) (_hZ : Measurable Z) (_hXZ : IndepFun X Z P)
    (_hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (_hpX_nn : ∀ x, 0 ≤ pX x) (_hpX_meas : Measurable pX)
    (_hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    {t : ℝ}
    (density_t : ℝ → ℝ)
    (hdensity_t_eq : ∀ (ht : 0 < t) (x : ℝ),
      density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)
    (ht : 0 < t) :
    fisherInfoOfDensityReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      = fisherInfoOfDensityReal density_t := by
  have hfun : density_t = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) :=
    funext (hdensity_t_eq ht)
  rw [hfun]

/-- **de Bruijn identity body — genuine assembly (Phase 5, plan §5C)**.

Same signature as `debruijnIdentityV2_holds` (`FisherInfoV2DeBruijn.lean`), proved by
assembling the 6 genuine per-time atoms
(`FisherInfoV2DeBruijnPerTime.lean`, all `@audit:ok`). Lives in a separate file to avoid
the import cycle (the atom file imports `FisherInfoV2DeBruijn`, so the wall file cannot
import the atoms; the assembly is the *reverse* dependency).

The assembly threads through three named regularity-plumbing lemmas
(`_entropy_eq` = 段 1-2, `_chain` = 段 2-7, `_fisher_match` = 段 1+7). After the conv-pin
redesign (§Phase 5-F 案 1, 2026-05-31), `_entropy_eq` and `_fisher_match` are **genuine**
(0 sorry) — `_fisher_match` closes by `funext` because the conv pin makes `density_t`
*pointwise equal* to `convDensityAdd pX g_t`. After the Wave 4b closure (2026-06-01), the
`_chain` (段 2-7) plumbing leaf `_chain_hdiff` is also genuinely closed; the only remaining
transitive `sorryAx` is now the two Mathlib walls `wall:fisher-finiteness` +
`wall:entropy-finiteness` (de Bruijn IBP / Fisher integrability). The atoms themselves are
genuine.

Honesty sign-off (conv-pin redesign, 2026-05-31): verdict honest_residual (NOT
proof-done — Mathlib-wall residual remains). (1) **Signature identical to wall
`debruijnIdentityV2_holds`** (`FisherInfoV2DeBruijn.lean`): same conclusion `HasDerivAt
(… differentialEntropy …) ((1/2)·fisherInfoOfDensityReal h_reg.density_t) t`, same hyps
(`h_reg : IsRegularDeBruijnHypV2`); no weakening / no extra regularity added (the wall
uses underscore `_hX/_hZ/_hXZ/_ht`, the assembly genuinely consumes `hX/hZ/hXZ/ht`).
(2) **Body genuine**: real wiring (`_chain` deriv + `_eq` eventual-equality →
`congr_of_eventuallyEq` → `rw [_fisher_match]`), no circular `:= h`, no degenerate.
(3) **NOT name-laundering**: `_assembled` + same signature, but `#print axioms` confirms
transitive `sorryAx` dependency (now via the two Mathlib walls only).

**Wave 4b update (2026-06-01)**: the `plan:epi-debruijn-pertime-closure` component is dropped
as stale (its plumbing leaf `_chain_hdiff` is now genuinely closed). The remaining transitive
`sorryAx` is exclusively `wall:fisher-finiteness` + `wall:entropy-finiteness`.
@residual(wall:fisher-finiteness,wall:entropy-finiteness) -/
theorem debruijnIdentityV2_holds_assembled
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    {t : ℝ} (ht : 0 < t)
    (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal h_reg.density_t)
      t := by
  -- pX integrability from `pX_law` + `P` probability (mirrors Phase 1b `:210`).
  have hpX_int : Integrable h_reg.pX volume := by
    rw [Integrable, hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h_reg.pX_nn)]
    refine ⟨h_reg.pX_meas.aestronglyMeasurable, ?_⟩
    have hlint : ∫⁻ x, ENNReal.ofReal (h_reg.pX x) ∂volume = (P.map X) Set.univ := by
      rw [h_reg.pX_law, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [hlint, Measure.map_apply hX MeasurableSet.univ, Set.preimage_univ, measure_univ]
    exact ENNReal.one_lt_top
  -- pX is a genuine probability density ⇒ `∫ pX = 1` (mass = (P.map X) univ = P univ = 1).
  --   Honest regularity precondition for the convolution Gaussian lower bound
  --   (`convDensityAdd_lower_bound_gaussian`, GAP① route).
  have hpX_mass : (∫ y, h_reg.pX y ∂volume) = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h_reg.pX_nn)
      h_reg.pX_meas.aestronglyMeasurable]
    have hlint : ∫⁻ x, ENNReal.ofReal (h_reg.pX x) ∂volume = (P.map X) Set.univ := by
      rw [h_reg.pX_law, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [hlint, Measure.map_apply hX MeasurableSet.univ, Set.preimage_univ, measure_univ,
      ENNReal.toReal_one]
  -- 段 2-7: the entropy-as-∫negMulLog chain has the half-fisher derivative at t.
  have h_chain := debruijnIdentityV2_holds_assembled_chain h_reg.pX h_reg.pX_nn
    h_reg.pX_meas hpX_int hpX_mass h_reg.pX_mom ht
  -- 段 1-2: entropy =ᶠ ∫ negMulLog (convDensityAdd …) near t.
  have h_eq := debruijnIdentityV2_holds_assembled_entropy_eq X Z hX hZ hXZ h_reg.Z_law
    h_reg.pX h_reg.pX_nn h_reg.pX_meas h_reg.pX_law ht
  -- transfer the derivative to the entropy function via eventual equality.
  have h_ent : HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal
        (convDensityAdd h_reg.pX (gaussianPDFReal 0 ⟨t, ht.le⟩)))
      t := h_chain.congr_of_eventuallyEq h_eq
  -- 段 1+7: rewrite the RHS fisher value to use `h_reg.density_t`.
  rw [debruijnIdentityV2_holds_assembled_fisher_match X Z hX hZ hXZ h_reg.Z_law
    h_reg.pX h_reg.pX_nn h_reg.pX_meas h_reg.pX_law h_reg.density_t h_reg.density_t_eq ht]
    at h_ent
  exact h_ent

end Common2026.Shannon.FisherInfoV2

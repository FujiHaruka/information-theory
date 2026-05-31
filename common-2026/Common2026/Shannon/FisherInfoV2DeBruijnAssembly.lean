import Common2026.Shannon.FisherInfoV2DeBruijnPerTime

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

/-- **§5G-2b (GAP②): `s`-uniform Gaussian-tail majorant for the spatial Hessian.**
On the `t`-neighborhood `Set.Ioo (t/2) (2*t)`, the spatial second derivative
`∂²_x p_s x = deriv (deriv (convDensityAdd pX g_s)) x` of the convolution density admits a
Gaussian-tail majorant uniform in `s`:
`‖∂²_x p_s x‖ ≤ C·(1 + x²)·exp(-x²/c')` with `0 < c'`, `0 ≤ C`.

Via the heat-eq STEP D identification `∂²_x p_s x = ∫ y, pX y · g_s(x-y)·((x-y)²/s² - 1/s)`
(`FisherInfoV2DeBruijnPerTime.heatFlow_density_heat_equation` STEP D + the kernel 2nd-deriv
closed form `heatFlow_density_heat_equation_kernel_x_deriv2`), the triangle inequality and the
Gaussian prefactor bound (`gaussianPDFReal_le_prefactor`) give a Gaussian-tail bound uniform on
the bounded window `s ∈ (t/2, 2t)`. The bridge `deriv (deriv (convDensityAdd …)) = pathDeriv2`
requires the `pathDeriv1/2` `HasDerivAt` preconditions (full-support C¹ plumbing shared with
L-PT-δ), which is the remaining honest `sorry`.

All hyps are pX-system regularity; the existential output is a pointwise Gaussian-tail bound.

**Finite-second-moment restate (2026-05-31, §Phase 5-G case A, 案A, 判断ログ #14)**: the statement is
now made **TRUE & satisfiable** by adding two pX regularity preconditions: `hpX_mass : ∫pX = 1` and
`hpX_mom : Integrable (fun y => y²·pX y)` (finite second moment). Why this closes the prior
false-statement gap: via the heat-eq STEP D표시 the supported majorant term is
`∫ pX(y)·g_s(x-y)·(x-y)² dy`, which after the Gaussian prefactor bound is dominated by
`pref(s)·∫ pX(y)·(x-y)² dy`. Expanding the (x-y)² polynomial,
`∫ pX(y)(x-y)² dy = x²·∫pX − 2x·∫y·pX + ∫y²·pX`; under `hpX_mass` (`∫pX = 1 < ∞`), `hpX_mom`
(`∫y²·pX < ∞`), and the derived first moment (`∫y·pX < ∞`, obtained from `2|y| ≤ 1+y²` domination
by `hpX_int.add hpX_mom`), all three terms are finite. The result is a finite-coefficient polynomial
`A·x² + B·x + C` absorbable into `C·(1 + x²)` and multiplied by the Gaussian factor `exp(-x²/c')`,
matching the `C·(1 + x²)·exp(-x²/c')` conclusion form (no signature change to the conclusion). A
heavy-tailed `pX` (e.g. standard Cauchy `1/(π(1+y²))`) has `∫y²·pX = ∞`, so `hpX_mom` is **not
satisfiable** for it — it is honestly excluded from the statement's scope rather than being a
counterexample to a claimed-universal bound (the prior false-statement defect was that no moment
hypothesis was present, so the bound was asserted for all pX including Cauchy, where it is false).
Finite second moment is the standard de Bruijn regularity precondition; it is a regularity hyp, NOT
load-bearing.

The body Gaussian-tail majorant construction (STEP D bridge + `gaussianPDFReal_le_prefactor` +
moment expansion) is not yet implemented, so this remains an **honest sorry** to be discharged in
Phase 5-G (L-PT-γ/δ).

**INDEPENDENT HONESTY AUDIT (2026-05-31, fresh auditor, commit `23ea70a`): verdict false_statement
(tier 5) — 案A does NOT fix the defect; it REPLACES the Cauchy counterexample with a polynomial-tail
counterexample. The restate is REJECTED.** The added `hpX_mom` (finite 2nd moment) is insufficient
for the `exp(-x²/c')` (Gaussian-tail) conclusion. Two mutually exclusive routes both fail:
(1) **prefactor route** (the one the docstring/plan §1302-1308 actually describe): `gaussianPDFReal_le_prefactor`
bounds `g_s(x-y) ≤ pref(s) = (√(2πs))⁻¹`, a CONSTANT in x — it DROPS the `exp(-(x-y)²/2s)` factor
(verified at `FisherInfoV2DeBruijnPerTime.lean:115-126`; the plan's `pref(s)·exp(-(x-y)²/2s)級`
parenthetical at §1303 is wishful, not what the lemma gives). This yields only a POLYNOMIAL majorant
`A·x²+B·x+C` (finite under `hpX_mom`/`hpX_mass`, true), but a polynomial does NOT satisfy
`≤ C(1+x²)exp(-x²/c')`: for any fixed C,c' the Gaussian RHS → 0 while the polynomial → ∞, so it fails
for all large x. The plan's "多項式は (1+x²) に吸収可能" (§1308) is the error — absorption into `(1+x²)`
is fine, but the `exp(-x²/c')` factor still kills the RHS below the polynomial.
(2) **keep-Gaussian route**: to factor `exp(-x²/c')` out of `∫pX(y)g_s(x-y)(x-y)²dy` one needs the MGF
`∫pX(y)exp(xy/s)dy < ∞` (the ORIGINAL defect note at the old `:483` was CORRECT), which is ∞ for any
polynomial-tail pX, not only Cauchy.
**Counterexample satisfying ALL hypotheses** (`hpX_nn`/`hpX_meas`/`hpX_int`/`hpX_mass`/`hpX_mom`):
`pX(y) = (2/π)·1/(1+y²)²`. Verified: `∫pX = 1` (exact, `∫1/(1+y²)² = π/2`), `∫y²·pX = 1 < ∞` (exact,
`∫y²/(1+y²)² = π/2`) so `hpX_mom` holds — yet its convolution-density 2nd derivative
`∂²_x p_s(x) = ∫pX(y)g_s(x-y)((x-y)²/s²−1/s)dy` decays only POLYNOMIALLY `~const/x²` (numerically:
`I(x)·x²` ≈ const ≈ 1e-5 over x∈[20,300]; `I(x) >> C(1+x²)exp(-x²/c')` already at x=200 for C=c'=1e3,
gap widening to 1e-11 vs 1e-32 at x=300). So the Gaussian-tail conclusion is FALSE for this pX.
Finite 2nd moment is NOT the right precondition; the conclusion would require a sub-Gaussian / finite-MGF
tail condition (e.g. `∫pX(y)exp(a|y|)dy < ∞`), which is MUCH stronger and excludes all polynomial-tail
densities. **Orchestrator action: this commit's defect-removal must be reverted (or the conclusion
weakened to a polynomial majorant `‖∂²_x p_s x‖ ≤ A(1+x²)`, which IS provable under finite 2nd moment
— but then `_chain_domination`'s separated-product integrability FAILS, exactly the §judgment-log-#13
obstruction, so 案B joint strategy is the real fix). Mark restored below pending rewrite.**

@audit:defect(false-statement)
@audit:retract-candidate(finite-2nd-moment-insufficient-polynomial-tail-counterexample: GAP②-Gaussian-tail-false-for-pX∝1/(1+y²)²)
@residual(plan:epi-debruijn-pertime-closure) -/
private theorem convDensityAdd_deriv2_tail_majorant
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∃ C c' : ℝ, 0 < c' ∧ 0 ≤ C ∧
      ∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖deriv (deriv (convDensityAdd pX
            (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩))) x‖
          ≤ C * (1 + x ^ 2) * Real.exp (-x ^ 2 / c') := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)  -- GAP②

/-- **§5G-2: full-entDeriv Gaussian-tail domination group (L-PT-γ, max cost).**
Produces an integrable majorant `bound` dominating the **full** entropy σ-derivand
`(- log (pPath s x) - 1) · ((1/2)·∂²_x pPath s x)` over the `t`-neighborhood
`Set.Ioo (t/2) (2*t)`. The integrability is genuine because the σ-derivand is taken as a
*product*: the Gaussian-tail decay of the spatial 2nd-derivative factor `∂²_x p_s x`
(super-polynomial in `x`) absorbs the `~x²` growth of the log factor, so the product has a
Lebesgue-integrable majorant.

**False-statement fix (2026-05-31, §Phase 5-G case A)**: the previous statement dominated the
**log factor alone** `(- log (pPath s x) - 1)` over `∀ s ∈ Set.univ`. That statement is FALSE:
(a) for `pX = N(0,1)`, `- log p_s x - 1 = (1/2)log(2π(1+s)) + x²/(2(1+s)) - 1`, which diverges as
`s → ∞` (so the `∀ s ∈ univ` quantifier is unsatisfiable by any single integrand bound), and
(b) the log factor alone grows `~x²` in `x`, which is Lebesgue **non-integrable** (no integrable
majorant exists). The fix dominates the **full σ-derivand product** (the `∂²_x p` Gaussian tail
kills the `x²` factor → integrable) over a **bounded `t`-neighborhood** `Ioo (t/2)(2*t)` (so
`s` stays in a compact away-from-0/∞ window), which is the true, satisfiable shape
(proof-pivot-advisor confirmed). On `Ioo (t/2)(2*t)` with `t > 0` we have `s > t/2 > 0`, so the
NNReal variance witness `⟨s, _⟩` is well-defined (no `max s 0` needed).

**Genuine-wiring split (2026-05-31)**: the former monolithic `sorry` is **factored** into
genuine wiring over two named regularity helpers. The body is now **genuine** (0 local sorry):
it `obtain`s an `s`-uniform polynomial majorant `A + B·x²` for the log factor
(`convDensityAdd_logFactor_poly_majorant`, §5G-2a / GAP①) and an `s`-uniform Gaussian-tail
majorant `C·(1+x²)·exp(-x²/c')` for the spatial Hessian (`convDensityAdd_deriv2_tail_majorant`,
§5G-2b / GAP②), then (i) proves the product majorant `(A+B·x²)·((1/2)·C·(1+x²)·exp(-x²/c'))` is
Lebesgue integrable (genuine: expands to a finite combination of `x^{0,2,4}·exp(-(1/c')x²)`,
each integrable via `integrable_natPow_mul_exp_neg_mul_sq`), and (ii) proves the domination
`‖LogFactor · (1/2·Hess)‖ ≤ bound` via `norm_mul` + `mul_le_mul`. The remaining honest `sorry`s
are localized in the two named helpers GAP①/GAP② (Mathlib/repo-absent: convolution-density
Gaussian lower bound + `deriv∘deriv` → STEP-D bridge, plan L-PT-γ/δ).

All hyps are pX-system regularity; the existential output is integrand-level domination. The
`@residual` is transitive (the sorries now live in the named §5G-2a/§5G-2b helpers), kept here
so the file-level residual grep still reflects this declaration's dependency.

Independent honesty audit (2026-05-31, fresh auditor, §5G-2 wiring commit `cf88267`): verdict
honest_residual (transitive). **0 local sorry** — the former monolithic sorry is genuinely
removed. **Genuine wiring (core-reconstruction test PASS)**: granting the two helpers' existential
outputs (`⟨A,B,…⟩` log majorant, `⟨C,c',…⟩` Hessian majorant) does NOT auto-discharge the
domination conclusion; the body genuinely constructs the product majorant
`(A+B·x²)·((1/2)·C·(1+x²)·exp(-x²/c'))` then (i) proves its integrability by a `ring`-expansion
into `x^{0,2,4}·exp(-(1/c')x²)` + 3× `integrable_natPow_mul_exp_neg_mul_sq` (`@audit:ok`,
sorryAx-free), and (ii) proves the domination via `norm_mul` + `mul_le_mul` +
`mul_le_mul_of_nonneg_left`. The helper outputs are `obtain`ed (genuinely consumed), NOT bundled
as load-bearing hypotheses. NOT circular, NOT load-bearing, NOT name-laundering (carries
`@residual`). The false-statement fix (judgment log #11: full-σ-derivand product over bounded
`Ioo (t/2,2t)`, not log-factor-alone over `univ`) makes the dominated statement true and
satisfiable.

Independent honesty audit (2026-05-31, fresh auditor, hpX_mass threading commit `b53107a`): verdict
honest_residual. **Update**: GAP① (`convDensityAdd_logFactor_poly_majorant`) is now genuine
(sorryAx-free, `@audit:ok` this commit), so the transitive `sorryAx` here comes **only** from GAP②
(`convDensityAdd_deriv2_tail_majorant`, still `@residual(plan:…)`). The new `hpX_mass` hyp is honest
regularity threaded to GAP①'s normalization need (NOT load-bearing). Body is genuine wiring (0 local
sorry); the single remaining residual is GAP②. @residual kept (transitive over the GAP② plan wall).

**INDEPENDENT HONESTY AUDIT (2026-05-31, fresh auditor, commit `23ea70a`): the claim that GAP② is
"restated TRUE" is REJECTED — verdict false_statement (transitive-via-GAP②), still tier 5.** The
consumed helper GAP② (`convDensityAdd_deriv2_tail_majorant`) remains a false-statement defect even
WITH `hpX_mass` + `hpX_mom`: finite 2nd moment is insufficient for its `exp(-x²/c')` Gaussian-tail
Hessian conclusion (counterexample `pX(y) = (2/π)/(1+y²)²` satisfies all five hyps incl. `hpX_mom`
but has only POLYNOMIAL `~1/x²` 2nd-derivative decay; see GAP② docstring audit note). Therefore this
body's product-majorant integrability proof (`(A+Bx²)·C(1+x²)exp(-x²/c')` → finite sum of
`x^{0,2,4}·exp(-(1/c')x²)`) is STILL **VACUOUS-GENUINE**: locally sorry-free but resting on GAP②'s
false `exp(-x²/c')` Hessian decay. The `_chain_domination` STATEMENT (∃ integrable majorant over
`Ioo(t/2,2t)`) is itself TRUE for general finite-2nd-moment pX (the true product
`(-log p_s)·∂²p_s ~ (log x)/x²·...` is integrable), but it is **NOT provable via the GAP①×GAP②
separated-product strategy** — GAP①'s `~x²` log-factor overestimate times any HONEST Hessian bound
(only polynomial `~1/x²` for polynomial-tail pX) gives a NON-integrable `~const` product majorant.
This is exactly the §judgment-log-#13 obstruction, which 案A did NOT remove (it only narrowed the
class from "all pX" to "finite-2nd-moment pX", but the obstruction persists on polynomial-tail
finite-2nd-moment pX). **DO NOT build further genuine claims downstream of this wiring until GAP② is
rewritten — either weaken GAP②/`_chain_domination` to a polynomial majorant (then this separated body
fails integrability) or adopt the 案B joint entropy-finiteness strategy.** Body type-checks (GAP②
conclusion form invariant under the hyp addition) but type-check passing ≠ honest.

@audit:defect(false-statement)
@residual(plan:epi-debruijn-pertime-closure) -/
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
  -- The σ-derivand at `s` is the product `LogFactor(s,x) · ((1/2)·Hess(s,x))`:
  --   LogFactor(s,x) = - log (p_s x) - 1     (poly-in-x growth, GAP①)
  --   Hess(s,x)      = ∂²_x p_s x            (Gaussian super-poly tail decay, GAP②).
  -- §5G-2a (GAP①) gives an `s`-uniform polynomial majorant for the log factor;
  -- §5G-2b (GAP②) gives an `s`-uniform Gaussian-tail majorant for the spatial Hessian.
  -- The product of (poly) × (poly × Gaussian) is poly × Gaussian = Lebesgue integrable.
  obtain ⟨A, B, hB_nn, hLog⟩ :=
    convDensityAdd_logFactor_poly_majorant pX hpX_nn hpX_meas hpX_int hpX_mass ht
  obtain ⟨C, c', hc'_pos, hC_nn, hHess⟩ :=
    convDensityAdd_deriv2_tail_majorant pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
  -- the integrable majorant: (A + B·x²) · ((1/2)·C·(1+x²)·exp(-x²/c')).
  refine ⟨fun x => (A + B * x ^ 2) * ((1/2) * (C * (1 + x ^ 2) * Real.exp (-x ^ 2 / c'))), ?_, ?_⟩
  · -- integrability: expand into a finite sum of `x^k · exp(-b·x²)` terms (poly × Gaussian).
    have hb : (0:ℝ) < 1 / c' := by positivity
    -- `exp(-x²/c') = exp(-(1/c')·x²)`.
    have hexp_eq : ∀ x : ℝ, Real.exp (-x ^ 2 / c') = Real.exp (-(1/c') * x ^ 2) := by
      intro x; congr 1; rw [neg_div, div_eq_inv_mul]; ring
    -- the bound equals a polynomial combination of `x^{0,2,4}·exp(-(1/c')x²)`.
    have hbound_eq : (fun x : ℝ => (A + B * x ^ 2) * ((1/2) * (C * (1 + x ^ 2)
          * Real.exp (-x ^ 2 / c'))))
        = fun x : ℝ =>
            ((1/2 * (A * C)) * (x ^ 0 * Real.exp (-(1/c') * x ^ 2))
            + (1/2 * (A * C) + 1/2 * (B * C)) * (x ^ 2 * Real.exp (-(1/c') * x ^ 2))
            + (1/2 * (B * C)) * (x ^ 4 * Real.exp (-(1/c') * x ^ 2))) := by
      funext x; rw [hexp_eq x]; ring
    rw [hbound_eq]
    refine ((((integrable_natPow_mul_exp_neg_mul_sq hb 0).const_mul _).add
      ((integrable_natPow_mul_exp_neg_mul_sq hb 2).const_mul _)).add
      ((integrable_natPow_mul_exp_neg_mul_sq hb 4).const_mul _))
  · -- domination: `‖LogFactor · (1/2 · Hess)‖ ≤ (A + B·x²)·((1/2)·C·(1+x²)·exp(-x²/c'))`.
    filter_upwards [hLog, hHess] with x hLogx hHessx
    intro s hs
    have hspos : (0:ℝ) < s := by have := hs.1; linarith
    -- `‖a·b‖ = ‖a‖·‖b‖`, then bound each factor.
    rw [norm_mul]
    have hlf := hLogx s hs
    have hhf := hHessx s hs
    -- ‖(1/2)·Hess‖ = (1/2)·‖Hess‖ ≤ (1/2)·(C·(1+x²)·exp(-x²/c')).
    have hhalf : ‖(1/2 : ℝ) * deriv (deriv (convDensityAdd pX
        (gaussianPDFReal 0 ⟨s, hspos.le⟩))) x‖
        ≤ (1/2) * (C * (1 + x ^ 2) * Real.exp (-x ^ 2 / c')) := by
      rw [norm_mul]
      have : ‖(1/2 : ℝ)‖ = 1/2 := by rw [Real.norm_eq_abs]; rw [abs_of_pos]; norm_num
      rw [this]
      have hHnn : (0:ℝ) ≤ C * (1 + x ^ 2) * Real.exp (-x ^ 2 / c') := by positivity
      exact mul_le_mul_of_nonneg_left hhf (by norm_num)
    -- combine: ‖LogFactor‖·‖(1/2)Hess‖ ≤ (A+B·x²)·((1/2)·C·(1+x²)·exp(-x²/c')).
    have hLog_nn : (0:ℝ) ≤ A + B * x ^ 2 := le_trans (norm_nonneg _) hlf
    calc ‖(- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hspos.le⟩) x) - 1)‖
            * ‖(1/2 : ℝ) * deriv (deriv (convDensityAdd pX
                (gaussianPDFReal 0 ⟨s, hspos.le⟩))) x‖
          ≤ (A + B * x ^ 2) * ((1/2) * (C * (1 + x ^ 2) * Real.exp (-x ^ 2 / c'))) := by
            apply mul_le_mul hlf hhalf (norm_nonneg _) hLog_nn

/-- **Fisher integrability of the time-`t` convolution density (Mathlib/repo wall).**
The square-score density `(logDeriv p_t)² · p_t` of the convolution density
`p_t = convDensityAdd pX g_t` is Lebesgue-integrable, where `g_t = gaussianPDFReal 0 ⟨t,_⟩`.

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
i.e. a genuine Mathlib gap rather than a same-family closure plan.

`hpX_nn`/`hpX_meas`/`hpX_int` are pure pX regularity preconditions; the integrability
conclusion is the genuine claim. No load-bearing hypothesis bundled.

Independent honesty audit (2026-05-31, fresh auditor, 案 B split commit): verdict
honest_residual. Statement true for any probability density `pX` (incl. heavy-tailed Cauchy)
by the Stam convolution Fisher bound `J(X+√t·Z) ≤ J(√t·Z) = 1/t < ∞` (proof-pivot-advisor +
判断ログ #12 独立確認). Classification `wall:fisher-finiteness` correct: loogle `fisherInfo` /
`Blachman` = Found 0 (`Stam` hits are `Std.Time.Timestamp`, unrelated), in-repo Stam machinery
is predicate pass-through only — a genuine Mathlib/repo gap, not a same-family closure plan.
Register entry (audit-tags.md L70) matches; semantic distinction vs `stam` (superadditivity =
EPI conclusion) is honored. The 3 pX hyps are regularity preconditions; integrability is the
claim (not bundled). @residual kept.

@residual(wall:fisher-finiteness) -/
private theorem convDensityAdd_fisher_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => (logDeriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x)^2
      * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) volume := by
  sorry -- @residual(wall:fisher-finiteness)

/-- **de Bruijn IBP step on the time-`t` convolution density (IBP + full-support wall).**
The de Bruijn integration-by-parts identity at fixed time `t`:
`∫ (- log p_t - 1) · ∂²_x p_t = ∫ (logDeriv p_t)² · p_t`, where `p_t = convDensityAdd pX g_t`.

**True statement** (de Bruijn / heat-flow IBP): writing `negMulLog'(p) = - log p - 1`, two
integrations by parts on `ℝ` move the spatial second derivative `∂²_x p_t` onto the score
factor, producing `∫ (∂_x p_t)²/p_t = ∫ (logDeriv p_t)²·p_t`. The boundary terms vanish by the
Gaussian/heavy-tail decay of `p_t` and its derivatives. The genuine atom
`debruijn_ibp_step` (`FisherInfoV2DeBruijnPerTime.lean:693`, `@audit:ok`) supplies the
Mathlib IBP core; what remains (the honest residual) is constructing its preconditions:
`tsupport = ℝ` full-support C¹ of `p_t` and the three IBP integrability hyps + identifying
the spatial 2nd derivative as a `HasDerivAt` (PR-level, plan L-PT-δ).

`hpX_nn`/`hpX_meas`/`hpX_int` are pure pX regularity preconditions; the IBP equality is the
genuine claim. No load-bearing hypothesis bundled.

Independent honesty audit (2026-05-31, fresh auditor, 案 B split commit): verdict
honest_residual. de Bruijn IBP identity is true (boundary terms vanish by Gaussian/heavy-tail
decay). Classification `plan:` correct (NOT a new wall): the IBP core is the in-tree atom
`debruijn_ibp_step` (`@audit:ok`, sorryAx-free via `integral_mul_deriv_eq_deriv_mul_of_integrable`);
the residual is constructing that atom's preconditions (`tsupport`=ℝ full-support C¹ + the 3 IBP
integrability hyps + 2nd-derivative `HasDerivAt` identification) = same-family plumbing, closeable
under the named plan. The 3 pX hyps are regularity; the IBP equality is the claim (not bundled).
Note for orchestrator: the atom's `Integrable (u'*v)` precondition (= `∫(logDeriv p)²·p` shape)
overlaps the Fisher-finiteness wall — when both residuals close, consider whether the integrability
can be sourced from `convDensityAdd_fisher_integrable` to avoid duplicate construction. @residual kept.

@residual(plan:epi-debruijn-pertime-closure) -/
private theorem debruijnIdentityV2_holds_assembled_chain_ibp_fisher_ibp_step
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    ∫ x, (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x ∂volume
      = ∫ x, (logDeriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x)^2
        * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x ∂volume := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)

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
name-laundering (carries `@residual`, not `@audit:ok`). The transitive marker is compound (AND of
the wall + plan walls below). @residual(wall:fisher-finiteness,plan:epi-debruijn-pertime-closure) -/
private theorem debruijnIdentityV2_holds_assembled_chain_ibp_fisher
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
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
  rw [debruijnIdentityV2_holds_assembled_chain_ibp_fisher_ibp_step pX hpX_nn hpX_meas hpX_int ht]
  -- (4) Fisher value: `∫ (logDeriv p_t)²·p_t = fisherInfoOfDensityReal p_t`,
  --     integrability supplied by the Fisher-finiteness wall.
  rw [fisher_from_logDeriv p_t hp_nn
    (convDensityAdd_fisher_integrable pX hpX_nn hpX_meas hpX_int ht)]

/-- **§5G-3: parametric-diff composition.**
The entropy integral `∫ negMulLog (pPath s ·)` has its `s`-derivative at `t` given by the
integral of `entDeriv` (the §5G-1 per-`x` closed form), and that integral equals
`(1/2)·fisherInfoOfDensityReal (pPath t)`. Composes `entropy_hasDerivAt_via_parametric` (atom,
now neighborhood-version: `hb`/`hdiff` quantified over `Set.Ioo (t/2)(2*t)`, requires `0 < t`)
with §5G-1 (per-`x` chain rule), §5G-2 (full-entDeriv Ioo domination), §5G-4 (Fisher value). The
`HasDerivAt` and Fisher-value conclusions are genuine claims; they are NOT supplied as
hypotheses.

**Statement true (2026-05-31, §Phase 5-G)**: the existential output `entDeriv` is the §5G-1
per-`x` closed form `(- log p_s x - 1)·((1/2)·∂²_x p_s x)`, which on the `Ioo (t/2)(2*t)`
neighborhood (each `s > 0`) satisfies the per-`x` chain rule (§5G-1, `pPath_s x > 0` a.e. + heat
eq) and is dominated by §5G-2's integrable majorant. Feeding these into the Ioo-version atom
yields the `HasDerivAt`; the Fisher value is §5G-4. The body is left as an honest `sorry` (the
a.e.-over-`Ioo` `hdiff` plumbing + atom invocation is L-PT-γ scope), but the **statement is
satisfiable** (proof-pivot-advisor confirmed). The被微分関数 keeps the `max s 0` form to match
`_chain` verbatim (`max s 0 = s` on the `t`-neighborhood).

Independent honesty audit (2026-05-31, fresh auditor, hpX_mass threading commit `b53107a`): verdict
honest_residual. The new `hpX_mass:∫pX=1` hyp is an honest regularity precondition threaded purely to
supply the §5G-2 domination's GAP① subcall (`_chain_domination` → `convDensityAdd_logFactor_poly_majorant`,
which needs normalization for the Gaussian lower/upper bounds); it does NOT change the residual's meaning
(the body is still the parametric-diff / `hdiff`-over-Ioo plumbing sorry, L-PT-γ scope). Conclusion
(`HasDerivAt` + Fisher value) is the genuine claim, not bundled. Classification `plan:` unchanged and
correct. @residual kept. @residual(plan:epi-debruijn-pertime-closure) -/
private theorem debruijnIdentityV2_holds_assembled_chain_parametric
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {t : ℝ} (ht : 0 < t) :
    ∃ entDeriv : ℝ → ℝ,
      HasDerivAt
        (fun s => ∫ x, Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) ∂volume)
        (∫ x, entDeriv x ∂volume) t
      ∧ (∫ x, entDeriv x ∂volume
          = (1/2) * fisherInfoOfDensityReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)

/-- **Assembly chain core (段 2-7, genuine plumbing over §5G sub-lemmas)**: given the
heat-flow density path `pPath s = convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩)` (the
convolution density of the law of `X + √s·Z`) with its X-density witness `pX`, the
`s`-derivative of the entropy `∫ negMulLog (pPath s ·)` at `t` equals
`(1/2) · fisherInfoOfDensityReal (pPath t)`.

After the §Phase 5-G sub-lemma split (2026-05-31), the former monolithic sorry is
**factored** into the 5 §5G sub-lemmas. The body of this lemma is now **genuine plumbing**
(§5G-5): it `obtain`s the entropy-derivative + value from `_chain_parametric` (§5G-3) and
rewrites — no local sorry. The remaining honest `sorry` + `@residual` are localized in
`_chain_domination` (§5G-2, L-PT-γ Gaussian-tail log-tail majorant), `_chain_ibp_fisher`
(§5G-4, L-PT-δ `tsupport`=ℝ C¹ + integrability), and `_chain_parametric` (§5G-3, transitive
over §5G-1/§5G-2/§5G-4). `_chain_entDeriv_formula` (§5G-1, the negMulLog chain rule) is
genuine (0 sorry).

`pX`/`hpX_nn`/`hpX_meas`/`hpX_int` are pure regularity preconditions (X has a Lebesgue
density `pX`). The conclusion (`HasDerivAt … (1/2) · fisher`) is NOT bundled into a
hypothesis — it is the genuine claim, derived from the sub-lemmas once the regularity is
supplied. The `@residual` is transitive (the sorry now lives in the named §5G sub-lemmas),
kept here so the file-level residual grep still reflects this declaration's dependency.

@residual(plan:epi-debruijn-pertime-closure) -/
private theorem debruijnIdentityV2_holds_assembled_chain
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
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
    debruijnIdentityV2_holds_assembled_chain_parametric pX hpX_nn hpX_meas hpX_int hpX_mass ht
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
*pointwise equal* to `convDensityAdd pX g_t`. The only remaining honest `sorry` +
`@residual(plan:epi-debruijn-pertime-closure)` is `_chain` (段 2-7) for the concrete
Gaussian-tail domination / `tsupport`-wide C¹ / integrability regularity (PR-level,
plan L-PT-γ/δ). The atoms themselves are genuine.

Honesty sign-off (conv-pin redesign, 2026-05-31): verdict honest_residual (NOT
proof-done — `_chain` sorry remains). (1) **Signature identical to wall
`debruijnIdentityV2_holds`** (`FisherInfoV2DeBruijn.lean`): same conclusion `HasDerivAt
(… differentialEntropy …) ((1/2)·fisherInfoOfDensityReal h_reg.density_t) t`, same hyps
(`h_reg : IsRegularDeBruijnHypV2`); no weakening / no extra regularity added (the wall
uses underscore `_hX/_hZ/_hXZ/_ht`, the assembly genuinely consumes `hX/hZ/hXZ/ht`).
(2) **Body genuine**: real wiring (`_chain` deriv + `_eq` eventual-equality →
`congr_of_eventuallyEq` → `rw [_fisher_match]`), no circular `:= h`, no degenerate.
(3) **NOT name-laundering**: `_assembled` + same signature, but `#print axioms` confirms
transitive `sorryAx` dependency (now via `_chain` only); docstring explicitly states it
is NOT proof-done, with the remaining gap localized in the named `_chain` honest-sorry
lemma. It carries `@residual` (not `@audit:ok`), so it does not claim completion.
classification `plan:` correct (downstream of @audit:ok atoms = plumbing). @residual kept.

`@residual(plan:epi-debruijn-pertime-closure)` -/
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
    h_reg.pX_meas hpX_int hpX_mass ht
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

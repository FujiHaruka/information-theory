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
NNReal variance witness `⟨s, _⟩` is well-defined (no `max s 0` needed). The remaining honest
`sorry` is the Gaussian-tail integrable majorant construction (~120-180 lines, plan L-PT-γ).

All hyps are pX-system regularity; the existential output is integrand-level domination.

@residual(plan:epi-debruijn-pertime-closure) -/
private theorem debruijnIdentityV2_holds_assembled_chain_domination
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    {t : ℝ} (ht : 0 < t) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      (∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖(- Real.log (convDensityAdd pX
              (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩) x) - 1)
            * ((1/2) * deriv (deriv (convDensityAdd pX
              (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩))) x)‖
          ≤ bound x) := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)

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
are localized in the 2 named walls above (no local sorry here). -/
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

@residual(plan:epi-debruijn-pertime-closure) -/
private theorem debruijnIdentityV2_holds_assembled_chain_parametric
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
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
    (hpX_int : Integrable pX volume)
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
    debruijnIdentityV2_holds_assembled_chain_parametric pX hpX_nn hpX_meas hpX_int ht
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
  -- 段 2-7: the entropy-as-∫negMulLog chain has the half-fisher derivative at t.
  have h_chain := debruijnIdentityV2_holds_assembled_chain h_reg.pX h_reg.pX_nn
    h_reg.pX_meas hpX_int ht
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

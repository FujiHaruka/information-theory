import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.V2DeBruijnPerTime
import InformationTheory.Shannon.FisherConvBound   -- shared 壁 gaussianConv_fisher_le_inv_var
import InformationTheory.Shannon.EPI.Conv.DensitySecondDeriv  -- STEP-D bridge convDensityAdd_deriv2_eq_gaussian
import InformationTheory.Shannon.FisherInfo.V2DeBruijnAssembly.Core
import InformationTheory.Shannon.FisherInfo.V2DeBruijnAssembly.Domination
import InformationTheory.Shannon.FisherInfo.V2DeBruijnAssembly.Derivatives

namespace InformationTheory.Shannon.FisherInfoV2

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal

open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAddDeriv)

variable {Ω : Type*} {_mΩ : MeasurableSpace Ω}

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

**Entropy-finiteness closed (2026-06-01)**: the 3 former `EntropyConvFinite.lean`
`wall:entropy-finiteness` lemmas (`convDensityAdd_logFactor_deriv2/deriv_integrable`,
`convDensityAdd_negMulLog_integrable`) are now genuinely closed in-file as Assembly plumbing onto
`_chain_domination` / the Gaussian envelopes (orchestrator independent re-check: NOT a Mathlib
wall).

**Fisher-finiteness wall CLOSED (2026-06-01, commit b5e13e2)**: `gaussianConv_fisher_le_inv_var`
(FisherConvBound.lean) is now genuinely closed (pointwise Cauchy-Schwarz), so this declaration has
NO remaining transitive `sorryAx`.

@audit:ok — independent honesty audit (2026-06-01, fresh auditor, commit b5e13e2): genuine,
sorryAx-free. `#print axioms` = `[propext, Classical.choice, Quot.sound]` (transient `#print axioms`
+ `lake env lean` after olean refresh; 0 sorryAx). Stale `@residual(wall:fisher-finiteness)` removed. -/
private theorem debruijnIdentityV2_holds_assembled_chain_ibp_fisher_ibp_step
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
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
      convDensityAdd_logFactor_deriv2_integrable
        pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
  -- `huv = Integrable (u * v)`: entropy-finiteness wall.
  have huv : Integrable (u * v) := by
    simpa only [Pi.mul_def, hu_def, hv_def, hp_t] using
      convDensityAdd_logFactor_deriv_integrable
        pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
  -- `hu'v = Integrable (u' * v)`: from the Fisher-finiteness wall (`(logDeriv)²·p_t`),
  --   since `u' x · v x = - logDeriv p_t x · deriv p_t x = -((logDeriv p_t x)²·p_t x)`.
  have hfisher := convDensityAdd_fisher_integrable pX hpX_nn hpX_meas hpX_int hpX_mass ht
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
name-laundering.

**Both walls CLOSED (2026-06-01, commit b5e13e2)**: entropy-finiteness closed in-file as Assembly
plumbing; Fisher-finiteness (`gaussianConv_fisher_le_inv_var`, FisherConvBound.lean) genuinely
closed via pointwise Cauchy-Schwarz. NO remaining transitive `sorryAx`.

@audit:ok — independent honesty audit (2026-06-01, fresh auditor, commit b5e13e2): genuine,
sorryAx-free. `#print axioms` = `[propext, Classical.choice, Quot.sound]` (transient `#print axioms`
+ `lake env lean` after olean refresh; 0 sorryAx). Stale `@residual(wall:fisher-finiteness)` removed. -/
private theorem debruijnIdentityV2_holds_assembled_chain_ibp_fisher
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
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
  rw [debruijnIdentityV2_holds_assembled_chain_ibp_fisher_ibp_step pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht]
  -- (4) Fisher value: `∫ (logDeriv p_t)²·p_t = fisherInfoOfDensityReal p_t`,
  --     integrability supplied by the Fisher-finiteness wall.
  rw [fisher_from_logDeriv p_t hp_nn
    (convDensityAdd_fisher_integrable pX hpX_nn hpX_meas hpX_int hpX_mass ht)]

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
NOT the composed `HasDerivAt`-of-the-integral, NOT hyp-bundled. All hyps pX regularity.

Independent honesty audit (2026-06-01, fresh auditor, commit `76afc39`): **proof-done, @audit:ok**.
`#print axioms` re-verified = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, machine
re-run via transient print + `lake env lean`). σ≤0 degenerate branch is HONEST (not a vacuous
exfalso / false-statement exploit): `pPath σ = convDensityAdd pX g_0` evaluates to the genuine
definitional value `0` via `gaussianPDFReal_zero_var` (var-0 Gaussian pdf = 0), and the σ≤0 pins
feed the all-σ deriv-pin requirement of the `@audit:ok` atom `heatFlow_density_heat_equation`
(its hpathDeriv1/2 are `∀ σ`); the actual conclusion is only used at `s > 0` (`hspos` from
`hs.1`), so the degenerate branch is forced plumbing, not the load-bearing content. NOT circular
(conclusion value = §5G-1 closed form computed from `heatFlow_density_heat_equation` +
`_chain_entDeriv_formula`, not a hypothesis), NOT load-bearing (all hyps pX regularity), 0 local
sorry. @audit:ok -/
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
the genuine claim (NOT hyp-bundled, NOT weakened) — no name laundering.

**Both walls CLOSED (2026-06-01, commit b5e13e2)**: `_chain_hdiff` genuinely closed,
entropy-finiteness closed in-file, and Fisher-finiteness (`gaussianConv_fisher_le_inv_var`)
genuinely closed via pointwise Cauchy-Schwarz. NO remaining transitive `sorryAx`.

@audit:ok — independent honesty audit (2026-06-01, fresh auditor, commit b5e13e2): genuine,
sorryAx-free. `#print axioms` = `[propext, Classical.choice, Quot.sound]` (transient `#print axioms`
+ `lake env lean` after olean refresh; 0 sorryAx). Stale `@residual(wall:fisher-finiteness)` removed. -/
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
      have h := convDensityAdd_negMulLog_integrable
        pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
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
      pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht (fun x => entDerivFn t x) hentDeriv

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
supplied.

**All walls CLOSED (2026-06-01, commit b5e13e2)**: `_chain_hdiff` genuinely closed,
entropy-finiteness closed in-file as Assembly plumbing, and Fisher-finiteness
(`gaussianConv_fisher_le_inv_var`, FisherConvBound.lean) genuinely closed via pointwise
Cauchy-Schwarz. NO remaining transitive `sorryAx`.

@audit:ok — independent honesty audit (2026-06-01, fresh auditor, commit b5e13e2): genuine,
sorryAx-free. `#print axioms` = `[propext, Classical.choice, Quot.sound]` (transient `#print axioms`
+ `lake env lean` after olean refresh; 0 sorryAx). Stale `@residual(wall:fisher-finiteness)` removed. -/
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
  -- Phase 1b (now general noise variance): instantiate at `v_Z := 1` (recovers `s·1 = s`).
  have h1b := pPath_eq_convDensityAdd X Z hX hZ hXZ (1 : ℝ≥0) one_pos hZ_law
    pX hpX_nn hpX_meas hpX_law hs
  -- unfold differentialEntropy = ∫ negMulLog ((rnDeriv).toReal).
  unfold differentialEntropy
  -- rewrite the variance witness `⟨max s 0, _⟩` to `⟨s, hs.le⟩`.
  have hwit : (⟨max s 0, le_max_right s 0⟩ : ℝ≥0) = ⟨s, hs.le⟩ := by
    apply NNReal.eq; exact hmax
  -- the Phase 1b result variance `⟨s·1, _⟩` equals `⟨s, hs.le⟩` (`s·1 = s`).
  have hwit1 : (⟨s * (1 : ℝ≥0), by positivity⟩ : ℝ≥0) = ⟨s, hs.le⟩ := by
    apply NNReal.eq; simp
  rw [hwit1] at h1b
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

Honesty sign-off (conv-pin redesign, 2026-05-31 / closure update 2026-06-01):
(1) **Signature identical to shim `debruijnIdentityV2_holds`** (`FisherInfoV2DeBruijn.lean`): same
conclusion `HasDerivAt (… differentialEntropy …) ((1/2)·fisherInfoOfDensityReal h_reg.density_t) t`,
same hyps (`h_reg : IsRegularDeBruijnHypV2`); no weakening / no extra regularity added (the shim uses
underscore `_hX/_hZ/_hXZ/_ht`, this assembly genuinely consumes `hX/hZ/hXZ/ht`).
(2) **Body genuine**: real wiring (`_chain` deriv + `_eq` eventual-equality →
`congr_of_eventuallyEq` → `rw [_fisher_match]`), no circular `:= h`, no degenerate.
(3) **NOT name-laundering**: `_assembled` + same signature; `#print axioms` now confirms NO
`sorryAx` dependency.

**End-to-end CLOSED (2026-06-01, commit b5e13e2)**: with `_chain_hdiff`, entropy-finiteness, and
Fisher-finiteness (`gaussianConv_fisher_le_inv_var`) all genuinely closed, the per-time de Bruijn
identity is now genuine end-to-end with NO remaining transitive `sorryAx`.

@audit:ok — independent honesty audit (2026-06-01, fresh auditor, commit b5e13e2): genuine,
proof-done, sorryAx-free. `#print axioms` = `[propext, Classical.choice, Quot.sound]` (transient
`#print axioms` + `lake env lean` after `lake build` olean refresh; 0 sorryAx). Stale
`@residual(wall:fisher-finiteness)` removed. NOTE (2026-06-01, import cycle resolved): the
same-signature per-time shim `debruijnIdentityV2_holds` (formerly in FisherInfoV2DeBruijn.lean) has
been **deleted**, and its two consumers (`deBruijn_identity_v2`,
`debruijnIntegrationIdentity_holds`) were relocated downstream of this assembly into
`FisherInfoV2DeBruijnGenuine.lean`, where they now delegate to this genuine sorryAx-free
`_assembled`. The de Bruijn pipeline therefore carries no per-time `sorry` anymore. -/
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

end InformationTheory.Shannon.FisherInfoV2

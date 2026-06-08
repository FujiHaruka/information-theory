import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.EPI.Plumbing
import InformationTheory.Shannon.EPI.Stam.ToBridge
import InformationTheory.Shannon.EPI.Unconditional.MixedCase
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPI.G2.ConvEntropyDensity
import InformationTheory.Shannon.EPI.Case1.ProducerMeasurability

/-!
# EPI case-1 via ratio + scaling squeeze (entropic-CLT-free)

This file lands the **monotone + limit** architecture for the classical (case-1,
a.c. inputs) entropy power inequality, **bypassing the entropic CLT wall**.

## Architecture (advisor-verified, `epi-case1-difference-g3-closure-plan.md` 判断ログ 7/8)

Let `R(t) = csiszarLogRatioGap X Y Z_X Z_Y P t
          = log N(law(X+Y+√t·(Z_X+Z_Y))) − log (N(law(X+√t·Z_X)) + N(law(Y+√t·Z_Y)))`,
the genuine log-ratio gap (`EPIL3Integration.csiszarLogRatioGap`).

* `csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1085`, genuine,
  sorryAx-free) gives `AntitoneOn R (Set.Ici 0)`.
* `epi_of_csiszarLogRatioGap_zero_nonneg` (`EPIStamToBridge.lean:985`, genuine)
  gives `0 ≤ R 0 ⟹ EPI`.

So if `R t → 0` as `t → ∞`, then by antitonicity `R 0 ≥ lim_{t→∞} R t = 0`, hence
EPI. **No entropic CLT** is needed: `R t → 0` follows from a *scaling squeeze*.

### Scaling cancellation

`X + √t·Z_X = √t·(X/√t + Z_X)`, so by `entropyPower_map_mul_const`
(`EPIPlumbing.lean:136`, `N(μ.map(·*c)) = c²·N(μ)`, `c = √t`):
`N(law(X+√t·Z_X)) = t · N(law(X/√t + Z_X))`. Applying this to all three paths, the
`t` factor cancels inside the `log`s (`Real.log_mul`, `t > 0`, `N > 0`):
`R t = log N(W_sum t) − log (N(W_X t) + N(W_Y t))`,
`W_X t = X/√t + Z_X`, `W_Y t = Y/√t + Z_Y`, `W_sum t = (X+Y)/√t + (Z_X+Z_Y)`.

### Squeeze

Each `N(W_X t) → N(law Z_X)` as `t → ∞` (input mass shrinks like `1/√t`): the lower
bound is `N(W_X t) = N(Z_X + X/√t) ≥ N(Z_X)` (independent-noise monotonicity,
`differentialEntropy_add_ge_of_indep`); the upper bound is the Gaussian max-entropy
`N(W_X t) ≤ 2πe (Var X / t + 1) → 2πe = N(Z_X)`
(`differentialEntropy_le_gaussian_of_variance_le`). With
`N(law(Z_X)+law(Z_Y)) = N(Z_X) + N(Z_Y)` (`entropyPower_gaussian_additivity`,
standard normals), the two `log`s converge to the same value, so `R t → 0`.

## Honesty

All per-`t` regularity (a.c., finite-entropy integrability of the W-path laws, the
8 fibre-integrability preconditions of `differentialEntropy_add_ge_of_indep`, finite
variance) is threaded as **honest preconditions** in the signatures (方針 X). The
Stam core / EPI core is never bundled as a `*Hypothesis`. The genuine analytic glue
(scaling cancellation, log-continuity composition, Gaussian additivity, order limit)
is the deliverable; preconditions not discharged here remain honest hypotheses.

Status: all four sections (§1 `epi_of_csiszarLogRatioGap_tendsto`, §2
`entropyPower_path_scaling`, §3 `entropyPower_rescaled_path_tendsto`, §4
`csiszarLogRatioGap_tendsto_zero_atTop`) have `sorry`-free bodies and are
sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
The §3 squeeze is now genuine: both envelopes are derived from the genuine
lemmas `differentialEntropy_add_ge_of_indep` (lower) and
`differentialEntropy_le_gaussian_of_variance_le` (upper) using the per-`t`
regularity bundle `IsRescaledPathRegular` (方針 X, NOT load-bearing). §4 threads
three such bundles transparently. Discharging `IsRescaledPathRegular` (supplying
the per-`t` regularity from a.c. inputs + Gaussian smoothing) is deferred to a
later phase; here it is an honest precondition.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace InformationTheory.Shannon.EPICase1RatioLimit

open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamToBridge
open InformationTheory.Shannon.EPIL3Integration (csiszarLogRatioGap csiszarLogRatioGap_at_zero)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## §1 — Order-theoretic deliverable (fully genuine)

`epi_of_csiszarLogRatioGap_tendsto`: antitone `R` on `Ici 0` together with
`R t → 0` forces `R 0 ≥ 0`, hence EPI. Pure order-limit argument; no analysis. -/

/-- **Order-limit bridge → EPI**. If the log-ratio gap `R = csiszarLogRatioGap …`
is antitone on `Set.Ici 0` and `R t → 0` as `t → ∞`, then `R 0 ≥ 0`, and therefore
the entropy power inequality holds.

`R 0 ≥ R t` for every `t ≥ 0` (antitonicity); since `R t → 0` and the tail predicate
`R 0 ≥ R t` holds eventually, `ge_of_tendsto` gives `R 0 ≥ 0`. The final EPI step is
`epi_of_csiszarLogRatioGap_zero_nonneg` (genuine bridge).

Genuine — no `sorry`, no load-bearing hypotheses (the antitone carrier and the limit
are honest inputs, both about `R` itself, not the EPI conclusion).

@audit:ok (independent honesty audit 2026-06-05: own body + transitive sorryAx-free
[propext, Classical.choice, Quot.sound]; `h_anti`/`h_lim` are statements about `R`
itself, not the EPI conclusion — non-load-bearing, sufficiency holds via `ge_of_tendsto`
+ genuine `epi_of_csiszarLogRatioGap_zero_nonneg`). -/
theorem epi_of_csiszarLogRatioGap_tendsto
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω)
    (h_anti : AntitoneOn (fun t => csiszarLogRatioGap X Y Z_X Z_Y P t) (Set.Ici (0 : ℝ)))
    (h_lim : Filter.Tendsto (fun t => csiszarLogRatioGap X Y Z_X Z_Y P t)
        Filter.atTop (nhds (0 : ℝ))) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  set R := fun t => csiszarLogRatioGap X Y Z_X Z_Y P t with hR
  -- `R 0 ≥ R t` for every `t ≥ 0` by antitonicity (`0 ≤ t`).
  have h_tail : ∀ᶠ t in Filter.atTop, R t ≤ R 0 := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact h_anti Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht
  -- `R t → 0` and `R t ≤ R 0` eventually ⟹ `0 ≤ R 0`.
  have h_zero_le : (0 : ℝ) ≤ R 0 := le_of_tendsto h_lim h_tail
  -- Bridge to EPI.
  exact epi_of_csiszarLogRatioGap_zero_nonneg X Y Z_X Z_Y P h_zero_le

/-! ## §2 — Scaling cancellation (genuine glue + threaded regularity)

`N(law(X+√t·Z_X)) = t · N(law(X/√t + Z_X))` via `entropyPower_map_mul_const`. -/

/-- **Single-path scaling identity**: for `t > 0`,
`entropyPower (P.map (fun ω => A ω + √t · B ω))
   = t · entropyPower (P.map (fun ω => A ω / √t + B ω))`.

`A + √t·B = √t·(A/√t + B)`, so the law on the left is the law on the right pushed
forward by `(· * √t)`; `entropyPower_map_mul_const` with `c = √t` (squared `= t`)
finishes. The a.c. + entropy-integrability of the *unscaled* W-path law are honest
regularity preconditions (consumed by `entropyPower_map_mul_const`).

@audit:ok (independent honesty audit 2026-06-05: own body + transitive sorryAx-free;
`h_ac`/`h_ent_int` are regularity preconditions of `entropyPower_map_mul_const`
[a.c. + negMulLog integrability], NOT load-bearing — the scaling identity is genuine
glue, conclusion `N(path) = t·N(W)` not encoded in any hypothesis). -/
theorem entropyPower_path_scaling
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hA : Measurable A) (hB : Measurable B)
    {t : ℝ} (ht : 0 < t)
    (h_ac : (P.map (fun ω => A ω / Real.sqrt t + B ω)) ≪ volume)
    (h_ent_int : Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => A ω / Real.sqrt t + B ω)).rnDeriv volume x).toReal)) volume) :
    entropyPower (P.map (fun ω => A ω + Real.sqrt t * B ω))
      = t * entropyPower (P.map (fun ω => A ω / Real.sqrt t + B ω)) := by
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_sqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt h_sqrt_pos
  set W : Ω → ℝ := fun ω => A ω / Real.sqrt t + B ω with hW
  have hW_meas : Measurable W := (hA.div_const _).add hB
  have hmul_meas : Measurable (fun x : ℝ => x * Real.sqrt t) :=
    measurable_id.mul_const _
  haveI : IsProbabilityMeasure (P.map W) :=
    Measure.isProbabilityMeasure_map hW_meas.aemeasurable
  -- `A + √t·B = (A/√t + B) * √t = (· * √t) ∘ W` pointwise.
  have h_path_eq : (fun ω => A ω + Real.sqrt t * B ω)
      = (fun x => x * Real.sqrt t) ∘ W := by
    funext ω
    simp only [hW, Function.comp_apply]
    field_simp
  -- Push forward through `map_map`: `P.map ((·*√t) ∘ W) = (P.map W).map (·*√t)`.
  have h_map_eq : P.map (fun ω => A ω + Real.sqrt t * B ω)
      = (P.map W).map (fun x => x * Real.sqrt t) := by
    rw [h_path_eq, Measure.map_map hmul_meas hW_meas]
  rw [h_map_eq]
  -- `entropyPower ((P.map W).map (·*√t)) = (√t)² · entropyPower (P.map W) = t · …`.
  rw [entropyPower_map_mul_const h_ac h_sqrt_ne h_ent_int]
  rw [Real.sq_sqrt ht.le]

/-! ## §3 — Per-path limit (squeeze, regularity threaded)

`N(W_X t) → N(law Z_X)` via the independent-noise lower bound and the Gaussian
max-entropy upper bound. -/

/-- **Per-`t` regularity bundle for the rescaled path `A/√t + B`**, holding the
preconditions of the two genuine envelope lemmas
(`differentialEntropy_add_ge_of_indep` for the lower bound, applied with
`X := B, Y := A/√t`; `differentialEntropy_le_gaussian_of_variance_le` for the
upper bound on `μ := P.map (A/√t + B)` with variance bound `varA/t + v_B`).

This is a **regularity** bundle (IndepFun / a.c. / fibre integrabilities / mean +
variance-bound + integrabilities), **NOT** load-bearing: it never contains the
conclusion `Tendsto … N(B)` nor either envelope inequality — those are derived in
`entropyPower_rescaled_path_tendsto` by calling the genuine lemmas with these
preconditions.

Independent honesty audit 2026-06-05: non-load-bearing AFFIRMED. Each conjunct was
matched verbatim to a regularity precondition of `differentialEntropy_add_ge_of_indep`
(lower bundle, X:=B Y:=A/√t) or `differentialEntropy_le_gaussian_of_variance_le`
(upper bundle). The variance-bound conjunct `∫(x-m)² ≤ varA/t + v_B` is the standard
`h_var` max-entropy input (not the squeeze core): `varA` is pinned `≥ Var A` by the
all-t requirement and the squeeze limit `N(B)` is independent of `varA`'s value. Not
vacuous (real constraints, satisfiable by Gaussian-smoothed a.c. paths, falsifiable by
non-a.c. paths; conclusion nontrivial via the separate `hB_law`/`hv_B`). -/
def IsRescaledPathRegular (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (varA : ℝ) (v_B : ℝ≥0) : Prop :=
  (∀ t : ℝ, 0 < t →
      IndepFun B (fun ω => A ω / Real.sqrt t) P
      ∧ (P.map (fun ω => B ω + A ω / Real.sqrt t)) ≪ volume
      ∧ ((P.map (fun ω => A ω / Real.sqrt t))
          ⊗ₘ condDistrib (fun ω => B ω + A ω / Real.sqrt t)
              (fun ω => A ω / Real.sqrt t) P
          ≪ (P.map (fun ω => A ω / Real.sqrt t))
              ⊗ₘ Kernel.const ℝ (P.map (fun ω => B ω + A ω / Real.sqrt t)))
      ∧ Integrable
          (llr ((P.map (fun ω => A ω / Real.sqrt t))
                  ⊗ₘ condDistrib (fun ω => B ω + A ω / Real.sqrt t)
                      (fun ω => A ω / Real.sqrt t) P)
                ((P.map (fun ω => A ω / Real.sqrt t))
                  ⊗ₘ Kernel.const ℝ (P.map (fun ω => B ω + A ω / Real.sqrt t))))
          ((P.map (fun ω => A ω / Real.sqrt t))
            ⊗ₘ condDistrib (fun ω => B ω + A ω / Real.sqrt t)
                (fun ω => A ω / Real.sqrt t) P)
      ∧ (∀ᵐ z ∂(P.map (fun ω => A ω / Real.sqrt t)),
          condDistrib (fun ω => B ω + A ω / Real.sqrt t)
              (fun ω => A ω / Real.sqrt t) P z ≪ volume)
      ∧ (∀ᵐ z ∂(P.map (fun ω => A ω / Real.sqrt t)), Integrable
          (fun x => ((condDistrib (fun ω => B ω + A ω / Real.sqrt t)
                (fun ω => A ω / Real.sqrt t) P z).rnDeriv volume x).toReal
            * Real.log (((condDistrib (fun ω => B ω + A ω / Real.sqrt t)
                (fun ω => A ω / Real.sqrt t) P z).rnDeriv volume x).toReal)) volume)
      ∧ (∀ᵐ z ∂(P.map (fun ω => A ω / Real.sqrt t)), Integrable
          (fun x => ((condDistrib (fun ω => B ω + A ω / Real.sqrt t)
                (fun ω => A ω / Real.sqrt t) P z).rnDeriv volume x).toReal
            * Real.log (((P.map (fun ω => B ω + A ω / Real.sqrt t)).rnDeriv
                volume x).toReal)) volume)
      ∧ Integrable
          (fun z => InformationTheory.Shannon.differentialEntropy
            (condDistrib (fun ω => B ω + A ω / Real.sqrt t)
                (fun ω => A ω / Real.sqrt t) P z))
          (P.map (fun ω => A ω / Real.sqrt t))
      ∧ Integrable
          (fun z => ∫ x, ((condDistrib (fun ω => B ω + A ω / Real.sqrt t)
                (fun ω => A ω / Real.sqrt t) P z).rnDeriv volume x).toReal
            * Real.log (((P.map (fun ω => B ω + A ω / Real.sqrt t)).rnDeriv
                volume x).toReal) ∂volume)
          (P.map (fun ω => A ω / Real.sqrt t))
      ∧ Integrable
          (fun x => Real.log (((P.map (fun ω => B ω + A ω / Real.sqrt t)).rnDeriv
                volume x).toReal))
          (P.map (fun ω => B ω + A ω / Real.sqrt t)))
  ∧ (∀ t : ℝ, 0 < t →
      (P.map (fun ω => A ω / Real.sqrt t + B ω)) ≪ volume
      ∧ (∫ x, (x - (∫ y, y ∂(P.map (fun ω => A ω / Real.sqrt t + B ω))))^2
            ∂(P.map (fun ω => A ω / Real.sqrt t + B ω)))
          ≤ varA / t + (v_B : ℝ)
      ∧ Integrable
          (fun x => (x - (∫ y, y ∂(P.map (fun ω => A ω / Real.sqrt t + B ω))))^2)
          (P.map (fun ω => A ω / Real.sqrt t + B ω))
      ∧ Integrable
          (fun x => Real.negMulLog
            (((P.map (fun ω => A ω / Real.sqrt t + B ω)).rnDeriv volume x).toReal))
          volume)

/-- **Per-path entropy-power limit**: as `t → ∞`, the rescaled W-path entropy power
`N(law(A/√t + B))` converges to the noise entropy power `N(law B)` when `B` has a
Gaussian law of nonzero variance.

Squeeze: lower bound `N(A/√t + B) ≥ N(B)` (independent-noise monotonicity,
genuine `differentialEntropy_add_ge_of_indep` applied with `X := B, Y := A/√t`),
upper bound `N(A/√t + B) ≤ 2πe·(varA/t + v_B) → 2πe·v_B = N(B)` (Gaussian
max-entropy, `differentialEntropy_le_gaussian_of_variance_le`), both sandwiching
`N(law B) = 2πe·v_B` (`entropyPower_gaussianReal`) as `varA/t → 0`
(`tendsto_of_tendsto_of_tendsto_of_le_of_le'`).

The squeeze structure (constant lower envelope from independent-noise monotonicity
+ decaying upper envelope from Gaussian max-entropy → common limit `N(B)`) is the
genuine analytic content of this lemma. All the per-`t` data feeding the two
genuine envelope lemmas are threaded as **honest regularity preconditions**
(方針 X, NOT load-bearing): `IndepFun B (A/√t)` (`h_indep`), a.c. of the path laws
(`h_path_ac`, `hB_ac`), the 8 fibre integrabilities of the lower-bound lemma
(`h_lb`), the max-entropy data of the upper-bound lemma (mean / variance bound by
`varA/t + v_B` / integrabilities, packaged in `h_ub`). The conclusion
`N(W t) → N(B)` is **not** encoded in any hypothesis — both envelopes are produced
by genuine Mathlib / in-tree lemmas, and their common limit is computed here.

`varA` (`= Var A`, threaded as a real regularity datum with `h_varA_nn : 0 ≤ varA`)
makes the upper envelope `varA/t + v_B` an explicit decaying-to-`v_B` function whose
limit is proved genuinely; it is **not** the conclusion bundled in.

@audit:ok (independent honesty audit 2026-06-05: own body + transitive sorryAx-free
[propext, Classical.choice, Quot.sound]. `IsRescaledPathRegular` bundle is regularity,
NOT load-bearing — its conjuncts match verbatim the regularity preconditions of the two
genuine envelope lemmas (lower: `differentialEntropy_add_ge_of_indep` X:=B,Y:=A/√t, 10
IndepFun/≪/Integrable slots; upper: `differentialEntropy_le_gaussian_of_variance_le`
ac/var-bound/integrabilities) and contains neither envelope inequality nor the conclusion.
Variance-bound conjunct `∫(x-m)² ≤ varA/t + v_B` is the standard `h_var` input of the
genuine max-entropy lemma: `varA` (only `0 ≤ varA`) is pinned `≥ Var A` by requiring the
bound to hold for all t (real-measure regularity datum), and the limit `N(B) = 2πe·v_B`
is computed independently of `varA` (since varA/t → 0) — `varA` sets only the decay rate,
not the limit, so it does not smuggle the conclusion. Vacuity: conclusion is nontrivial
via separate `hB_law`/`hv_B` (N(B) = 2πe·v_B ≠ 0). Sufficiency: squeeze of constant lower
+ decaying upper to common limit N(B) is semantically valid.) -/
theorem entropyPower_rescaled_path_tendsto
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hA : Measurable A) (hB : Measurable B)
    (v_B : ℝ≥0) (hv_B : v_B ≠ 0)
    (hB_law : P.map B = gaussianReal 0 v_B)
    (varA : ℝ) (h_varA_nn : 0 ≤ varA)
    (hB_ac : (P.map B) ≪ volume)
    (h_reg : IsRescaledPathRegular A B P varA v_B) :
    Filter.Tendsto
      (fun t => entropyPower (P.map (fun ω => A ω / Real.sqrt t + B ω)))
      Filter.atTop (nhds (entropyPower (P.map B))) := by
  obtain ⟨h_lb, h_ub⟩ := h_reg
  -- `N(B) = 2πe·v_B` (Gaussian reference value).
  have hNB : entropyPower (P.map B) = 2 * Real.pi * Real.exp 1 * (v_B : ℝ) := by
    rw [hB_law, entropyPower_gaussianReal 0 hv_B]
  -- `v_B > 0` as a real.
  have hvB_pos : (0 : ℝ) < (v_B : ℝ) := by
    have : (v_B : ℝ) ≠ 0 := by exact_mod_cast hv_B
    exact lt_of_le_of_ne v_B.coe_nonneg (Ne.symm this)
  -- The upper envelope value `varBound t = varA/t + v_B`, positive for `t > 0`.
  have hvt_pos : ∀ t : ℝ, 0 < t → (0 : ℝ) < varA / t + (v_B : ℝ) := by
    intro t ht
    have : (0 : ℝ) ≤ varA / t := by positivity
    linarith
  -- ===== Lower envelope: `N(B) ≤ N(A/√t + B)` for `t > 0`. =====
  have h_lower : ∀ t : ℝ, 0 < t →
      entropyPower (P.map B)
        ≤ entropyPower (P.map (fun ω => A ω / Real.sqrt t + B ω)) := by
    intro t ht
    obtain ⟨h_indep, hW_ac, h_ac, h_int, hκ_v, hκ_logp, hκ_cross,
      h_fibreEnt, h_cross, h_logq⟩ := h_lb t ht
    have hAt_meas : Measurable (fun ω => A ω / Real.sqrt t) := hA.div_const _
    -- `h(B) ≤ h(B + A/√t)` from the genuine independent-noise monotonicity lemma.
    have h_de : InformationTheory.Shannon.differentialEntropy (P.map B)
        ≤ InformationTheory.Shannon.differentialEntropy
            (P.map (fun ω => B ω + A ω / Real.sqrt t)) :=
      differentialEntropy_add_ge_of_indep B (fun ω => A ω / Real.sqrt t) P hB hAt_meas
        h_indep hB_ac hW_ac h_ac h_int hκ_v hκ_logp hκ_cross h_fibreEnt h_cross h_logq
    -- `B + A/√t = A/√t + B` pointwise, so the laws agree.
    have h_path : (fun ω => B ω + A ω / Real.sqrt t)
        = (fun ω => A ω / Real.sqrt t + B ω) := by funext ω; ring
    rw [h_path] at h_de
    exact entropyPower_le_of_differentialEntropy_le h_de
  -- ===== Upper envelope: `N(A/√t + B) ≤ 2πe·(varA/t + v_B)` for `t > 0`. =====
  have h_upper : ∀ t : ℝ, 0 < t →
      entropyPower (P.map (fun ω => A ω / Real.sqrt t + B ω))
        ≤ 2 * Real.pi * Real.exp 1 * (varA / t + (v_B : ℝ)) := by
    intro t ht
    obtain ⟨hμ_ac, h_var, h_var_int, h_ent_int⟩ := h_ub t ht
    set μ : Measure ℝ := P.map (fun ω => A ω / Real.sqrt t + B ω) with hμ_def
    have hW_meas : Measurable (fun ω => A ω / Real.sqrt t + B ω) :=
      (hA.div_const _).add hB
    haveI : IsProbabilityMeasure μ :=
      Measure.isProbabilityMeasure_map hW_meas.aemeasurable
    -- The variance-bound value as a positive `ℝ≥0`.
    set vt : ℝ≥0 := (varA / t + (v_B : ℝ)).toNNReal with hvt_def
    have hvt_coe : (vt : ℝ) = varA / t + (v_B : ℝ) := by
      rw [hvt_def, Real.coe_toNNReal _ (hvt_pos t ht).le]
    have hvt_ne : vt ≠ 0 := by
      rw [hvt_def]
      simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
      exact hvt_pos t ht
    -- Gaussian max-entropy upper bound at mean `m := ∫ x ∂μ`.
    have h_de : InformationTheory.Shannon.differentialEntropy μ
        ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (vt : ℝ)) := by
      refine differentialEntropy_le_gaussian_of_variance_le hμ_ac
        (∫ y, y ∂μ) hvt_ne rfl ?_ h_var_int h_ent_int
      rw [hvt_coe]; exact h_var
    -- Lift `h(μ) ≤ (1/2)log(2πe·vt)` to `N(μ) ≤ 2πe·vt = entropyPower (𝒩 0 vt)`.
    have h_ep : entropyPower μ ≤ entropyPower (gaussianReal 0 vt) := by
      apply entropyPower_le_of_differentialEntropy_le
      rw [InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hvt_ne]
      exact h_de
    rw [entropyPower_gaussianReal 0 hvt_ne, hvt_coe] at h_ep
    exact h_ep
  -- ===== Tendsto of the two envelopes to the common value `N(B) = 2πe·v_B`. =====
  -- Constant lower envelope.
  have h_lim_low : Filter.Tendsto (fun _ : ℝ => entropyPower (P.map B))
      Filter.atTop (nhds (entropyPower (P.map B))) := tendsto_const_nhds
  -- Decaying upper envelope `2πe·(varA/t + v_B) → 2πe·v_B = N(B)`.
  have h_lim_up : Filter.Tendsto
      (fun t : ℝ => 2 * Real.pi * Real.exp 1 * (varA / t + (v_B : ℝ)))
      Filter.atTop (nhds (entropyPower (P.map B))) := by
    rw [hNB]
    have h_div : Filter.Tendsto (fun t : ℝ => varA / t) Filter.atTop (nhds 0) :=
      Filter.Tendsto.const_div_atTop Filter.tendsto_id varA
    have h_inner : Filter.Tendsto (fun t : ℝ => varA / t + (v_B : ℝ))
        Filter.atTop (nhds ((0 : ℝ) + (v_B : ℝ))) := h_div.add tendsto_const_nhds
    simp only [zero_add] at h_inner
    have := h_inner.const_mul (2 * Real.pi * Real.exp 1)
    simpa using this
  -- ===== Squeeze. =====
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lim_low h_lim_up ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    exact h_lower t ht
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    exact h_upper t ht

/-! ## §3b — Discharging `IsRescaledPathRegular` from method-X regularity

`isRescaledPathRegular_of_methodX`: construct the per-`t` regularity bundle
`IsRescaledPathRegular A B P varA v_B` from bare method-X premises, exploiting that
`B` is a Gaussian noise (`P.map B = gaussianReal 0 v_B`) independent of `A`. The fibre
of `condDistrib (B + A/√t) (A/√t) P` is the translated Gaussian `gaussianReal z v_B`
(`affineShiftKernel`, c = 1), so the fibre-level conditions reduce to Gaussian-density
integrability rather than the general density-witness wall.

All conjuncts (IndepFun / a.c. / fibre a.c. / fibre self-entropy / fibre-entropy-over-z /
joint-≪-product / squared-deviation / both path-entropy log-integrabilities + the 3
conditional-KL cross-entropy integrabilities) are closed genuinely using `hA_ac` + the
`convDensityAdd` path-density identification + the extracted cross-entropy lemmas
(`convCrossEntropy_perFibre_integrable` / `convCrossEntropy_zAvg_integrable` /
`convJointLlr_integrable`, `EPIG2ConvEntropyDensity.lean`). sorryAx-free. -/

/-- **Scaling preserves a.c.**: if `P.map A ≪ volume` then `P.map (A/√t) ≪ volume`
for `t > 0` (the map `(·/√t)` is a Lebesgue-a.c. linear isomorphism). Genuine. -/
theorem map_div_sqrt_absolutelyContinuous
    (A : Ω → ℝ) (P : Measure Ω) (hA : Measurable A) (hA_ac : (P.map A) ≪ volume)
    {t : ℝ} (ht : 0 < t) :
    (P.map (fun ω => A ω / Real.sqrt t)) ≪ volume := by
  have h_sqrt_ne : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hc_ne : (Real.sqrt t)⁻¹ ≠ 0 := inv_ne_zero h_sqrt_ne
  have hf_meas : Measurable (fun x : ℝ => x * (Real.sqrt t)⁻¹) :=
    measurable_id.mul_const _
  -- `A/√t = (· * (√t)⁻¹) ∘ A`, so `P.map (A/√t) = (P.map A).map (· * (√t)⁻¹)`.
  have hmap : (P.map (fun ω => A ω / Real.sqrt t))
      = (P.map A).map (fun x => x * (Real.sqrt t)⁻¹) := by
    rw [Measure.map_map hf_meas hA]
    rfl
  rw [hmap]
  -- `(P.map A).map (·*c) ≪ volume.map (·*c) = ofReal|c⁻¹| • volume ≪ volume`.
  have hac1 : (P.map A).map (fun x => x * (Real.sqrt t)⁻¹)
      ≪ (volume : Measure ℝ).map (fun x => x * (Real.sqrt t)⁻¹) :=
    hA_ac.map hf_meas
  have hvol : (volume : Measure ℝ).map (fun x => x * (Real.sqrt t)⁻¹)
      = ENNReal.ofReal |((Real.sqrt t)⁻¹)⁻¹| • (volume : Measure ℝ) :=
    Real.map_volume_mul_right hc_ne
  refine hac1.trans ?_
  rw [hvol]
  exact Measure.smul_absolutelyContinuous

/-- **Density witness for `A/√t`**: from `P.map A ≪ volume`, the rescaled input
`A/√t` admits a Real density witness `pX := ((P.map (A/√t)).rnDeriv volume).toReal`
with all the regularity (`≥ 0`, measurable, `withDensity` law, integrable, mass `= 1`,
finite second moment) needed to invoke `convDensityAdd_negMulLog_integrable_pub` and the
`pPath_eq_convDensityAdd` identification. Genuine. -/
theorem rescaledInput_density_witness
    (A : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hA : Measurable A) (hA_ac : (P.map A) ≪ volume)
    (h_mom_A : Integrable (fun ω => (A ω)^2) P) {t : ℝ} (ht : 0 < t) :
    ∃ pX : ℝ → ℝ, (∀ x, 0 ≤ pX x) ∧ Measurable pX
      ∧ (P.map (fun ω => A ω / Real.sqrt t)
          = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
      ∧ Integrable pX volume ∧ (∫ y, pX y ∂volume) = 1
      ∧ Integrable (fun y => y ^ 2 * pX y) volume := by
  set Zt : Ω → ℝ := fun ω => A ω / Real.sqrt t with hZt
  have hZt_meas : Measurable Zt := hA.div_const _
  have hZt_ac : (P.map Zt) ≪ volume :=
    map_div_sqrt_absolutelyContinuous A P hA hA_ac ht
  haveI : IsProbabilityMeasure (P.map Zt) :=
    Measure.isProbabilityMeasure_map hZt_meas.aemeasurable
  set pX : ℝ → ℝ := fun x => ((P.map Zt).rnDeriv volume x).toReal with hpX
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x => ENNReal.toReal_nonneg
  have hpX_meas : Measurable pX :=
    ((P.map Zt).measurable_rnDeriv volume).ennreal_toReal
  -- `withDensity` law via `withDensity_rnDeriv_eq` + `ofReal ∘ toReal =ᵐ id` (finite rnDeriv).
  have hpX_law : P.map Zt = volume.withDensity (fun x => ENNReal.ofReal (pX x)) := by
    have hfin : ∀ᵐ x ∂volume, (P.map Zt).rnDeriv volume x < ∞ :=
      Measure.rnDeriv_lt_top (P.map Zt) volume
    have hcongr : (fun x => ENNReal.ofReal (pX x)) =ᵐ[volume]
        (P.map Zt).rnDeriv volume := by
      filter_upwards [hfin] with x hx
      simp only [hpX, ENNReal.ofReal_toReal hx.ne]
    rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hZt_ac]
  -- `pX` integrable (finite-mass density): `∫⁻ ofReal pX = (P.map Zt) univ = 1`.
  have hpX_int : Integrable pX volume := by
    rw [Integrable, hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpX_nn)]
    refine ⟨hpX_meas.aestronglyMeasurable, ?_⟩
    have hlint : ∫⁻ x, ENNReal.ofReal (pX x) ∂volume = (P.map Zt) Set.univ := by
      rw [hpX_law, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [hlint, measure_univ]
    exact ENNReal.one_lt_top
  -- mass `∫ pX = 1` from the same.
  have hpX_mass : (∫ y, pX y ∂volume) = 1 := by
    have h1 : ∫ y, pX y ∂volume = ((P.map Zt) Set.univ).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpX_nn)
        hpX_meas.aestronglyMeasurable]
      congr 1
      have : ∫⁻ x, ENNReal.ofReal (pX x) ∂volume = (P.map Zt) Set.univ := by
        rw [hpX_law, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
      exact this
    rw [h1, measure_univ, ENNReal.toReal_one]
  -- second moment: `∫ y²·pX = ∫ Zt² dP = (1/t)·∫ A² dP < ∞`.
  have hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume := by
    -- Transport the integrand to `P.map Zt` (withDensity), then to `P`.
    have hZt_sq : Integrable (fun ω => (Zt ω)^2) P := by
      have : (fun ω => (Zt ω)^2) = (fun ω => (1 / t) * (A ω)^2) := by
        funext ω; simp only [hZt, div_pow, Real.sq_sqrt ht.le]; ring
      rw [this]; exact h_mom_A.const_mul _
    -- `Integrable (y²) (P.map Zt)` (transport of `Zt²` to the law).
    have hsq_law : Integrable (fun y => y ^ 2) (P.map Zt) := by
      rw [integrable_map_measure
        ((by fun_prop : Measurable (fun y : ℝ => y ^ 2)).aestronglyMeasurable)
        hZt_meas.aemeasurable]
      simpa [Function.comp] using hZt_sq
    -- Move from `P.map Zt = withDensity (ofReal ∘ pX)` to the `y²·pX` integral on volume.
    rw [hpX_law] at hsq_law
    rw [integrable_withDensity_iff_integrable_smul₀'
      hpX_meas.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at hsq_law
    refine hsq_law.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hpX_nn x)]; ring
  exact ⟨pX, hpX_nn, hpX_meas, hpX_law, hpX_int, hpX_mass, hpX_mom⟩

/-- **Discharge `IsRescaledPathRegular` from method-X regularity.**

Given a Gaussian noise `B` (`P.map B = gaussianReal 0 v_B`, `v_B ≠ 0`) independent of
the input `A` (`hAB : IndepFun A B P`), with `A` measurable + finite-second-moment
data threaded as `varA`-regularity, construct the per-`t` regularity bundle
`IsRescaledPathRegular A B P varA v_B`.

The key insight (demonstrated genuinely here): the fibre of
`condDistrib (B + A/√t) (A/√t) P` is the translated Gaussian `gaussianReal z v_B` (the
law of `B + z` by `affineShiftKernel`/Gaussian translation). This **avoids the
2026-05-25 density-witness wall** for the general fibre: the fibre identification
`condDistrib (B + A/√t) (A/√t) P =ᵐ affineShiftKernel (P.map B) 1` (`h_fibre_ae`) and
the per-fibre a.c. `condDistrib z ≪ volume` (`hκ_v`, via `gaussianReal z v_B`) are both
**closed genuinely** — exactly the conjuncts that are intractable in the general case.

Honest preconditions only (NOT load-bearing): measurability, `IndepFun A B P`, the
Gaussian noise law, finite-second-moment `h_mom_A` + `varA`-regularity (`h_var_bound`).
The bundle being constructed is itself regularity (audited non-load-bearing at its def
site §3).

**Closure status (proof done — ALL 9 integrability conjuncts genuinely closed,
2026-06-05):** the theorem and all its transitive helpers are sorryAx-free
(`#print axioms isRescaledPathRegular_of_methodX` = `[propext, Classical.choice,
Quot.sound]`). The 3 conditional-KL integrabilities formerly parked are now closed via
the extracted standalone lemmas in `EPIG2ConvEntropyDensity.lean`
(`convCrossEntropy_perFibre_integrable` / `convCrossEntropy_zAvg_integrable` /
`convJointLlr_integrable`, all `#print axioms` clean), instantiated here with the
**Gaussian fibre** `q := gaussianPDFReal 0 v_B` (translated by `z`) and the target
convolution density `g := convDensityAdd pX g_{v_B}`. No signature change was needed:
because the fibre is Gaussian (not the input density), the joint-llr branch (b)
abs-entropy `∫ q·|log q|` is the Gaussian self-entropy (finite via
`integrable_density_log_density_of_gaussian`), so the inventory's suspected `hpX_ent`
input-density-entropy precondition is **not required** (the `X`/`Z` roles are swapped vs.
the density template, where the fibre is the input). All honest preconditions:
`hA_ac : P.map A ≪ volume` (case-1 a.c. input, NOT load-bearing — consumed only for the
density witness and `P.map (A/√t) ≪ volume`), `h_mom_A` (finite second moment, feeds the
Gaussian-fibre moment domination), the Gaussian noise law, `h_var_bound`.

- Genuine (regularity, closed here): `IndepFun B (A/√t)` (`h_indep`), a.c. of `B + A/√t`
  and `A/√t + B` (`hW_ac`/`hμ_ac`), the fibre identification `h_fibre_ae` + per-fibre a.c.
  `hκ_v`, the variance bound (threaded `h_var_bound`), joint-≪-product, the fibre/path
  self-entropy + log-density integrabilities, the squared-deviation, and the **3
  cross-entropy conjuncts** (per-z cross integrand, z-averaged cross-term, joint llr).
- The cross-entropy analytic core (`condDifferentialEntropy_le`'s
  `h_int`/`hκ_cross_int`/`h_cross_int`): integrability of the path-density `log g` against
  each Gaussian fibre, dominated by the `convDensityAdd_logFactor_poly_majorant`
  `|log g| ≤ (A+1)+B·x²` and the Gaussian-fibre quadratic moments. Genuine, no `sorry`.

Earlier honesty audit (2026-06-05, B(i)-cont, AFFIRMED): `hA_ac` non-load-bearing,
`h_var_bound` pass-through non-circular (its type ≡ ONE conjunct of the constructed
regularity bundle, not the theorem's conclusion; the substantive squeeze lives in the
separate `@audit:ok` consumer `entropyPower_rescaled_path_tendsto`), honest naming
`_of_methodX`. The bundle `IsRescaledPathRegular` is def-site `@audit:ok` regularity.
@audit:ok -/
theorem isRescaledPathRegular_of_methodX
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hA : Measurable A) (hB : Measurable B)
    (v_B : ℝ≥0) (hv_B : v_B ≠ 0) (hB_law : P.map B = gaussianReal 0 v_B)
    (hAB : IndepFun A B P)
    (hA_ac : (P.map A) ≪ volume)
    (varA : ℝ) (h_varA_nn : 0 ≤ varA)
    (h_mom_A : Integrable (fun ω => (A ω)^2) P)
    (h_var_bound : ∀ t : ℝ, 0 < t →
      (∫ x, (x - (∫ y, y ∂(P.map (fun ω => A ω / Real.sqrt t + B ω))))^2
            ∂(P.map (fun ω => A ω / Real.sqrt t + B ω)))
          ≤ varA / t + (v_B : ℝ)) :
    IsRescaledPathRegular A B P varA v_B := by
  -- Noise is a.c. (Gaussian).
  have hB_ac : (P.map B) ≪ volume := by
    rw [hB_law]; exact gaussianReal_absolutelyContinuous 0 hv_B
  refine ⟨?_, ?_⟩
  · -- ===== Lower bundle (per `t`, conditions of `differentialEntropy_add_ge_of_indep`,
    --       framing X := B, Y := A/√t). =====
    intro t ht
    have h_sqrt_pos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
    set Zt : Ω → ℝ := fun ω => A ω / Real.sqrt t with hZt
    have hZt_meas : Measurable Zt := hA.div_const _
    -- (1) `IndepFun B (A/√t)`: `A/√t` is a measurable function of `A`, `B ⊥ A`.
    have h_indep : IndepFun B Zt P := by
      have : Zt = (fun a => a / Real.sqrt t) ∘ A := by funext ω; rfl
      rw [this]
      exact (hAB.symm).comp measurable_id (measurable_id.div_const _)
    -- (2) a.c. of `B + A/√t` (convolution with the a.c. Gaussian factor `B`).
    have hW_ac : (P.map (fun ω => B ω + Zt ω)) ≪ volume :=
      map_add_absolutelyContinuous B Zt P hB hZt_meas h_indep hB_ac
    -- Fibre identification: `condDistrib (B + Zt) Zt P =ᵐ affineShiftKernel (P.map B) 1`.
    -- (Same construction as `condDifferentialEntropy_indep_add_eq`, here `X := B, Z := Zt, c := 1`.)
    have hZt_law_prob : IsProbabilityMeasure (P.map Zt) :=
      Measure.isProbabilityMeasure_map hZt_meas.aemeasurable
    have hB_law_prob : IsProbabilityMeasure (P.map B) :=
      Measure.isProbabilityMeasure_map hB.aemeasurable
    have h_fibre_ae : condDistrib (fun ω => B ω + Zt ω) Zt P
        =ᵐ[P.map Zt] affineShiftKernel (P.map B) 1 := by
      set W : Ω → ℝ := fun ω => B ω + Zt ω with hW_def
      have hW : Measurable W := hB.add hZt_meas
      -- Joint `(Zt, B)` is the product law (independence `B ⊥ Zt`, i.e. `Zt ⊥ B`).
      have hZtB : IndepFun Zt B P := h_indep.symm
      have hjoint_ZB : P.map (fun ω => (Zt ω, B ω)) = (P.map Zt).prod (P.map B) :=
        (indepFun_iff_map_prod_eq_prod_map_map hZt_meas.aemeasurable hB.aemeasurable).mp hZtB
      -- Push the product through `g (z, x) = (z, x + 1·z)`.
      have hg : Measurable fun p : ℝ × ℝ => (p.1, p.2 + (1 : ℝ) * p.1) := by fun_prop
      have hjoint_ZW : P.map (fun ω => (Zt ω, W ω))
          = (P.map Zt) ⊗ₘ (affineShiftKernel (P.map B) 1) := by
        have hcomp : (fun ω => (Zt ω, W ω))
            = (fun p : ℝ × ℝ => (p.1, p.2 + (1 : ℝ) * p.1)) ∘ (fun ω => (Zt ω, B ω)) := by
          funext ω; simp [hW_def, one_mul, add_comm]
        rw [hcomp, ← Measure.map_map hg (hZt_meas.prodMk hB), hjoint_ZB,
          prod_map_affine_eq_compProd]
      exact condDistrib_ae_eq_of_measure_eq_compProd Zt hW.aemeasurable hjoint_ZW
    -- (3) fibre a.c.: each fibre is `(P.map B).map(·+z) = gaussianReal z v_B`, a.c.
    have h_fibre_gauss : ∀ z : ℝ,
        affineShiftKernel (P.map B) 1 z = gaussianReal z v_B := by
      intro z
      rw [affineShiftKernel_apply, hB_law]
      simp only [one_mul]
      rw [gaussianReal_map_add_const z]
      simp
    have hκ_v : ∀ᵐ z ∂(P.map Zt),
        condDistrib (fun ω => B ω + Zt ω) Zt P z ≪ volume := by
      filter_upwards [h_fibre_ae] with z hz
      rw [hz, h_fibre_gauss z]
      exact gaussianReal_absolutelyContinuous z hv_B
    refine ⟨h_indep, hW_ac, ?_, ?_, hκ_v, ?_, ?_, ?_, ?_, ?_⟩
    · -- joint ≪ product-with-const. Per-fibre `gaussianReal z v_B ≪ volume ≪ P.map W`,
      -- the latter since the convolution density `g = convDensityAdd pX g_{v_B}` is strictly
      -- positive everywhere (`convDensityAdd_pos`, positive mass), so `volume ≪ P.map W`.
      have hv_B_pos : (0 : ℝ≥0) < v_B := pos_iff_ne_zero.mpr hv_B
      -- Density witness + path identification (X := Zt, Z := B, s := 1).
      obtain ⟨pX, hpX_nn, hpX_meas, hpX_law, hpX_int, hpX_mass, hpX_mom⟩ :=
        rescaledInput_density_witness A P hA hA_ac h_mom_A ht
      have hpath_eq : (fun ω => B ω + Zt ω)
          = InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Zt B 1 := by
        funext ω
        simp only [InformationTheory.Shannon.FisherInfoV2.gaussianConvolution,
          Real.sqrt_one, one_mul]; ring
      have h_path_rnDeriv : (P.map (fun ω => B ω + Zt ω)).rnDeriv volume
          =ᵐ[volume] fun z => ENNReal.ofReal
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
              (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) z) := by
        rw [hpath_eq]
        exact InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
          Zt B hZt_meas hB h_indep.symm v_B hv_B_pos hB_law pX hpX_nn hpX_meas hpX_law
          (s := 1) one_pos
      -- `g > 0` everywhere (`convDensityAdd_pos`, mass `= 1 > 0`).
      have hg_pos : ∀ x, 0 < InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
          (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) x := by
        intro x
        exact InformationTheory.Shannon.FisherInfoV2.convDensityAdd_pos pX hpX_nn hpX_int
          (by rw [hpX_mass]; norm_num) (by positivity) x
      -- `P.map W = withDensity (ofReal g)`, hence `volume ≪ P.map W`.
      have hW_density : (P.map (fun ω => B ω + Zt ω))
          = volume.withDensity (fun x => ENNReal.ofReal
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
              (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) x)) := by
        rw [← Measure.withDensity_rnDeriv_eq _ _ hW_ac]
        exact withDensity_congr_ae h_path_rnDeriv
      have hvol_ac_W : (volume : Measure ℝ) ≪ P.map (fun ω => B ω + Zt ω) := by
        rw [hW_density]
        refine withDensity_absolutelyContinuous' ?_ ?_
        · exact ((P.map (fun ω => B ω + Zt ω)).measurable_rnDeriv volume).aemeasurable.congr
            h_path_rnDeriv
        · exact Filter.Eventually.of_forall fun x => by
            simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hg_pos x
      -- Per-fibre a.c.: `condDistrib z ≪ gaussianReal z v_B ≪ volume ≪ P.map W`.
      refine Measure.AbsolutelyContinuous.compProd_right ?_
      filter_upwards [h_fibre_ae] with z hz
      rw [ProbabilityTheory.Kernel.const_apply]
      refine (?_ : condDistrib (fun ω => B ω + Zt ω) Zt P z ≪ volume).trans hvol_ac_W
      rw [hz, h_fibre_gauss z]
      exact gaussianReal_absolutelyContinuous z hv_B
    · -- llr integrable (Gaussian fibre: log-density of `gaussianReal z v_B` vs path law).
      -- Joint conditional-KL integrand; closed via `convJointLlr_integrable` with the
      -- Gaussian fibre `q := gaussianPDFReal 0 v_B` (self-entropy finite, NO input-density
      -- entropy precondition) and target `g := convDensityAdd pX g_{v_B}`.
      have hv_B_pos : (0 : ℝ≥0) < v_B := pos_iff_ne_zero.mpr hv_B
      obtain ⟨pX, hpX_nn, hpX_meas, hpX_law, hpX_int, hpX_mass, hpX_mom⟩ :=
        rescaledInput_density_witness A P hA hA_ac h_mom_A ht
      have hpath_eq : (fun ω => B ω + Zt ω)
          = InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Zt B 1 := by
        funext ω
        simp only [InformationTheory.Shannon.FisherInfoV2.gaussianConvolution,
          Real.sqrt_one, one_mul]; ring
      have h_path_rnDeriv : (P.map (fun ω => B ω + Zt ω)).rnDeriv volume
          =ᵐ[volume] fun z => ENNReal.ofReal
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
              (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) z) := by
        rw [hpath_eq]
        exact InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
          Zt B hZt_meas hB h_indep.symm v_B hv_B_pos hB_law pX hpX_nn hpX_meas hpX_law
          (s := 1) one_pos
      have hvar_eq : (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B :=
        NNReal.coe_injective (by show (1 : ℝ) * (v_B : ℝ) = (v_B : ℝ); rw [one_mul])
      set g : ℝ → ℝ :=
        InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 v_B)
        with hg_def
      have hg_nn : ∀ x, 0 ≤ g x := fun x =>
        integral_nonneg fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg _ _ _)
      have hg_meas : Measurable g := by
        rw [hg_def]
        have hg_pdf : Measurable (gaussianPDFReal 0 v_B) := measurable_gaussianPDFReal 0 _
        have huncurry : StronglyMeasurable
            (Function.uncurry fun w x => pX x * gaussianPDFReal 0 v_B (w - x)) := by
          apply Measurable.stronglyMeasurable
          exact (hpX_meas.comp measurable_snd).mul
            (hg_pdf.comp (measurable_fst.sub measurable_snd))
        have h := huncurry.integral_prod_right (ν := volume)
        simpa only [InformationTheory.Shannon.EPIConvDensity.convDensityAdd] using h.measurable
      have hg_pos : ∀ x, 0 < g x := by
        intro x
        rw [hg_def]
        exact InformationTheory.Shannon.FisherInfoV2.convDensityAdd_pos pX hpX_nn hpX_int
          (by rw [hpX_mass]; norm_num) (show (0:ℝ) < v_B from hv_B_pos) x
      -- path rnDeriv (Real, a.e.) is `g`.
      have h_g_rnDeriv : (P.map (fun ω => B ω + Zt ω)).rnDeriv volume
          =ᵐ[volume] fun x => ENNReal.ofReal (g x) := by
        filter_upwards [h_path_rnDeriv] with x hx
        rw [hx, hvar_eq]
      -- `μ.map W = withDensity (ofReal g)`, hence `volume ≪ P.map W`.
      have hW_density : (P.map (fun ω => B ω + Zt ω))
          = volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
        rw [← Measure.withDensity_rnDeriv_eq _ _ hW_ac]
        exact withDensity_congr_ae h_g_rnDeriv
      have hvol_ac_W : (volume : Measure ℝ) ≪ P.map (fun ω => B ω + Zt ω) := by
        rw [hW_density]
        refine withDensity_absolutelyContinuous' ?_ ?_
        · exact ((P.map (fun ω => B ω + Zt ω)).measurable_rnDeriv volume).aemeasurable.congr
            h_g_rnDeriv
        · exact Filter.Eventually.of_forall fun x => by
            simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hg_pos x
      -- `h_ac`: joint ≪ product-with-const.
      have h_ac_loc : (P.map Zt) ⊗ₘ condDistrib (fun ω => B ω + Zt ω) Zt P
          ≪ (P.map Zt) ⊗ₘ Kernel.const ℝ (P.map (fun ω => B ω + Zt ω)) := by
        refine Measure.AbsolutelyContinuous.compProd_right ?_
        filter_upwards [h_fibre_ae] with z hz
        rw [ProbabilityTheory.Kernel.const_apply]
        refine (?_ : condDistrib (fun ω => B ω + Zt ω) Zt P z ≪ volume).trans hvol_ac_W
        rw [hz, h_fibre_gauss z]
        exact gaussianReal_absolutelyContinuous z hv_B
      -- fibre rnDeriv `=ᵐ ofReal (gaussianPDFReal 0 v_B (x − √1·z))`.
      have hfib_eq : ∀ᵐ z ∂(P.map Zt),
          (condDistrib (fun ω => B ω + Zt ω) Zt P z).rnDeriv volume
            =ᵐ[volume] fun x => ENNReal.ofReal (gaussianPDFReal 0 v_B (x - Real.sqrt 1 * z)) := by
        filter_upwards [h_fibre_ae] with z hz
        rw [hz, h_fibre_gauss z]
        filter_upwards [rnDeriv_gaussianReal z v_B] with x hx
        rw [hx, gaussianPDF]
        rw [Real.sqrt_one, one_mul]
        congr 1
        unfold gaussianPDFReal; simp [sub_zero]
      -- majorant `|log g| ≤ (A+1) + B·x²`.
      obtain ⟨Amaj, Bmaj, hBmaj_nn, hLog0⟩ :=
        InformationTheory.Shannon.FisherInfoV2.convDensityAdd_logFactor_poly_majorant
          pX hpX_nn hpX_meas hpX_int hpX_mass hv_B_pos
      have hv_mem : (v_B : ℝ) ∈ Set.Ioo ((v_B : ℝ) / 2) (2 * v_B) :=
        ⟨by linarith [(show (0:ℝ) < v_B from hv_B_pos)],
          by linarith [(show (0:ℝ) < v_B from hv_B_pos)]⟩
      have hvval : (⟨(v_B : ℝ), le_of_lt (show (0:ℝ) < v_B from hv_B_pos)⟩ : ℝ≥0) = v_B :=
        NNReal.coe_injective rfl
      have hLog : ∀ᵐ x ∂volume, |Real.log (g x)| ≤ (Amaj + 1) + Bmaj * x ^ 2 := by
        filter_upwards [hLog0] with x hx
        have hb := hx (v_B : ℝ) hv_mem
        have hpt_eq : InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
            (gaussianPDFReal 0 ⟨(v_B : ℝ), le_of_lt (show (0:ℝ) < v_B from hv_B_pos)⟩) x = g x := by
          rw [hg_def, hvval]
        rw [hpt_eq, Real.norm_eq_abs] at hb
        have habs : |Real.log (g x)| ≤ |(- Real.log (g x) - 1)| + 1 := by
          calc |Real.log (g x)| = |(- Real.log (g x) - 1) + 1| := by
                rw [show (- Real.log (g x) - 1) + 1 = - Real.log (g x) by ring, abs_neg]
            _ ≤ |(- Real.log (g x) - 1)| + |(1:ℝ)| := abs_add_le _ _
            _ = |(- Real.log (g x) - 1)| + 1 := by norm_num
        linarith
      -- per-fibre self-entropy integrand (Gaussian).
      have hκ_logp_int : ∀ᵐ z ∂(P.map Zt), Integrable
          (fun x => ((condDistrib (fun ω => B ω + Zt ω) Zt P z).rnDeriv volume x).toReal
            * Real.log (((condDistrib (fun ω => B ω + Zt ω) Zt P z).rnDeriv volume x).toReal))
          volume := by
        filter_upwards [h_fibre_ae] with z hz
        refine (InformationTheory.Shannon.integrable_density_log_density_of_gaussian z hv_B).congr ?_
        have hrn : (condDistrib (fun ω => B ω + Zt ω) Zt P z).rnDeriv volume
            =ᵐ[volume] fun x => ENNReal.ofReal (gaussianPDFReal z v_B x) := by
          rw [hz, h_fibre_gauss z]
          filter_upwards [rnDeriv_gaussianReal z v_B] with x hx
          rw [hx, gaussianPDF]
        filter_upwards [hrn] with x hx
        rw [hx, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg z v_B x)]
      -- per-fibre cross-term integrand (closed via the extract lemma).
      have hκ_cross_int : ∀ᵐ z ∂(P.map Zt), Integrable
          (fun x => ((condDistrib (fun ω => B ω + Zt ω) Zt P z).rnDeriv volume x).toReal
            * Real.log (((P.map (fun ω => B ω + Zt ω)).rnDeriv volume x).toReal)) volume := by
        have hg_rn' : (fun x => ((P.map (fun ω => B ω + Zt ω)).rnDeriv volume x).toReal)
            =ᵐ[volume] g := by
          filter_upwards [h_g_rnDeriv] with x hx
          rw [hx, ENNReal.toReal_ofReal (hg_nn x)]
        filter_upwards [h_fibre_ae] with z hz
        have hbase := InformationTheory.Shannon.convCrossEntropy_perFibre_integrable
          (gaussianPDFReal 0 v_B) pX (gaussianPDFReal_nonneg 0 v_B)
          (measurable_gaussianPDFReal 0 v_B) (integrable_gaussianPDFReal 0 v_B)
          (InformationTheory.Shannon.integrable_sq_mul_gaussianPDFReal hv_B)
          hpX_nn hpX_meas hpX_int hpX_mass hv_B_pos z
        refine hbase.congr ?_
        have hfib_rn : (fun x => ((condDistrib (fun ω => B ω + Zt ω) Zt P z).rnDeriv volume x).toReal)
            =ᵐ[volume] fun x => gaussianPDFReal 0 v_B (x - z) := by
          have hrn : (condDistrib (fun ω => B ω + Zt ω) Zt P z).rnDeriv volume
              =ᵐ[volume] fun x => ENNReal.ofReal (gaussianPDFReal z v_B x) := by
            rw [hz, h_fibre_gauss z]
            filter_upwards [rnDeriv_gaussianReal z v_B] with x hx
            rw [hx, gaussianPDF]
          filter_upwards [hrn] with x hx
          rw [hx, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg z v_B x)]
          unfold gaussianPDFReal; simp [sub_zero]
        filter_upwards [hfib_rn, hg_rn'] with x hx hxg
        rw [hx, hxg, hg_def]
      -- Gaussian self-entropy in absolute value (NO input-density entropy needed).
      have hq_abs_ent : Integrable
          (fun x => gaussianPDFReal 0 v_B x * |Real.log (gaussianPDFReal 0 v_B x)|) volume := by
        have h := (InformationTheory.Shannon.integrable_density_log_density_of_gaussian 0 hv_B).norm
        refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 v_B x)]
      -- `Integrable (z²) (P.map Zt)`.
      have hZt_sq : Integrable (fun ω => (Zt ω)^2) P := by
        have : (fun ω => (Zt ω)^2) = (fun ω => (1 / t) * (A ω)^2) := by
          funext ω; simp only [hZt, div_pow, Real.sq_sqrt ht.le]; ring
        rw [this]; exact h_mom_A.const_mul _
      have hZ_sq : Integrable (fun z => z ^ 2) (P.map Zt) := by
        rw [integrable_map_measure
          ((by fun_prop : Measurable (fun y : ℝ => y ^ 2)).aestronglyMeasurable)
          hZt_meas.aemeasurable]
        simpa [Function.comp] using hZt_sq
      exact InformationTheory.Shannon.convJointLlr_integrable P Zt (fun ω => B ω + Zt ω)
        (gaussianPDFReal 0 v_B) g (gaussianPDFReal_nonneg 0 v_B) hg_nn
        (measurable_gaussianPDFReal 0 v_B) hg_meas Amaj Bmaj one_pos
        hW_ac hvol_ac_W hκ_v h_ac_loc hfib_eq h_g_rnDeriv hLog hBmaj_nn
        hκ_logp_int hκ_cross_int (integrable_gaussianPDFReal 0 v_B)
        (integral_gaussianPDFReal_eq_one 0 hv_B)
        (InformationTheory.Shannon.integrable_sq_mul_gaussianPDFReal hv_B)
        hq_abs_ent hZ_sq
    · -- fibre rnDeriv·log(fibre rnDeriv) integrable (Gaussian density `gaussianReal z v_B`
      -- self-entropy integrand, finite for each z).
      filter_upwards [h_fibre_ae] with z hz
      -- The fibre is `gaussianReal z v_B`; its `rnDeriv =ᵐ gaussianPDFReal z v_B`, and the
      -- self-entropy integrand is integrable (`integrable_density_log_density_of_gaussian`).
      refine (InformationTheory.Shannon.integrable_density_log_density_of_gaussian z hv_B).congr
        ?_
      have hrn : (condDistrib (fun ω => B ω + Zt ω) Zt P z).rnDeriv volume
          =ᵐ[volume] fun x => ENNReal.ofReal (gaussianPDFReal z v_B x) := by
        rw [hz, h_fibre_gauss z]
        filter_upwards [rnDeriv_gaussianReal z v_B] with x hx
        rw [hx, gaussianPDF]
      filter_upwards [hrn] with x hx
      rw [hx, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg z v_B x)]
    · -- fibre rnDeriv·log(path rnDeriv) integrable (cross-term, Gaussian fibre × path law).
      -- The fibre is `gaussianReal z v_B` (rnDeriv `gaussianPDFReal z v_B`), the path law has
      -- density `g = convDensityAdd pX g_{v_B}`; the integrand a.e.-equals
      -- `gaussianPDFReal 0 v_B (x − z)·log (g x)`, integrable by `convCrossEntropy_perFibre_integrable`.
      have hv_B_pos : (0 : ℝ≥0) < v_B := pos_iff_ne_zero.mpr hv_B
      obtain ⟨pX, hpX_nn, hpX_meas, hpX_law, hpX_int, hpX_mass, hpX_mom⟩ :=
        rescaledInput_density_witness A P hA hA_ac h_mom_A ht
      have hpath_eq : (fun ω => B ω + Zt ω)
          = InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Zt B 1 := by
        funext ω
        simp only [InformationTheory.Shannon.FisherInfoV2.gaussianConvolution,
          Real.sqrt_one, one_mul]; ring
      have h_path_rnDeriv : (P.map (fun ω => B ω + Zt ω)).rnDeriv volume
          =ᵐ[volume] fun z => ENNReal.ofReal
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
              (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) z) := by
        rw [hpath_eq]
        exact InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
          Zt B hZt_meas hB h_indep.symm v_B hv_B_pos hB_law pX hpX_nn hpX_meas hpX_law
          (s := 1) one_pos
      have hvar_eq : (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B :=
        NNReal.coe_injective (by show (1 : ℝ) * (v_B : ℝ) = (v_B : ℝ); rw [one_mul])
      set g : ℝ → ℝ :=
        InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 v_B)
        with hg_def
      have hg_nn : ∀ x, 0 ≤ g x := fun x =>
        integral_nonneg fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg _ _ _)
      -- path rnDeriv (as a Real, a.e.) is `g`.
      have h_g_rnDeriv : (fun x => ((P.map (fun ω => B ω + Zt ω)).rnDeriv volume x).toReal)
          =ᵐ[volume] g := by
        filter_upwards [h_path_rnDeriv] with x hx
        rw [hx, hvar_eq, ENNReal.toReal_ofReal (hg_nn x)]
      filter_upwards [h_fibre_ae] with z hz
      -- per-fibre integrability via the extract lemma (fibre `q := gaussianPDFReal 0 v_B`).
      have hbase := InformationTheory.Shannon.convCrossEntropy_perFibre_integrable
        (gaussianPDFReal 0 v_B) pX (gaussianPDFReal_nonneg 0 v_B) (measurable_gaussianPDFReal 0 v_B)
        (integrable_gaussianPDFReal 0 v_B)
        (InformationTheory.Shannon.integrable_sq_mul_gaussianPDFReal hv_B)
        hpX_nn hpX_meas hpX_int hpX_mass hv_B_pos z
      -- transport `q(x − z)·log g x` to the rnDeriv form.
      refine hbase.congr ?_
      -- fibre rnDeriv `=ᵐ gaussianPDFReal z v_B = gaussianPDFReal 0 v_B (· − z)`.
      have hfib_rn : (fun x => ((condDistrib (fun ω => B ω + Zt ω) Zt P z).rnDeriv volume x).toReal)
          =ᵐ[volume] fun x => gaussianPDFReal 0 v_B (x - z) := by
        have hrn : (condDistrib (fun ω => B ω + Zt ω) Zt P z).rnDeriv volume
            =ᵐ[volume] fun x => ENNReal.ofReal (gaussianPDFReal z v_B x) := by
          rw [hz, h_fibre_gauss z]
          filter_upwards [rnDeriv_gaussianReal z v_B] with x hx
          rw [hx, gaussianPDF]
        filter_upwards [hrn] with x hx
        rw [hx, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg z v_B x)]
        unfold gaussianPDFReal; simp [sub_zero]
      filter_upwards [hfib_rn, h_g_rnDeriv] with x hx hxg
      rw [hx, hxg, hg_def]
    · -- fibre entropy integrable (`z ↦ h(gaussianReal z v_B) = (1/2)log(2πe v_B)` constant
      -- in z, hence integrable; the fibre is the translated Gaussian `gaussianReal z v_B`).
      refine (integrable_const ((1/2) * Real.log (2 * Real.pi * Real.exp 1 * v_B))).congr ?_
      filter_upwards [h_fibre_ae] with z hz
      rw [hz, h_fibre_gauss z,
        InformationTheory.Shannon.differentialEntropy_gaussianReal z hv_B]
    · -- cross-term integrable (z-average of the Gaussian-fibre × path cross integrand).
      -- The inner integral a.e.-equals `∫ gaussianPDFReal 0 v_B (x − z)·log (g x) dx`, integrable
      -- over `P.map Zt` (finite second moment) by `convCrossEntropy_zAvg_integrable` (`s = 1`).
      have hv_B_pos : (0 : ℝ≥0) < v_B := pos_iff_ne_zero.mpr hv_B
      obtain ⟨pX, hpX_nn, hpX_meas, hpX_law, hpX_int, hpX_mass, hpX_mom⟩ :=
        rescaledInput_density_witness A P hA hA_ac h_mom_A ht
      have hpath_eq : (fun ω => B ω + Zt ω)
          = InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Zt B 1 := by
        funext ω
        simp only [InformationTheory.Shannon.FisherInfoV2.gaussianConvolution,
          Real.sqrt_one, one_mul]; ring
      have h_path_rnDeriv : (P.map (fun ω => B ω + Zt ω)).rnDeriv volume
          =ᵐ[volume] fun z => ENNReal.ofReal
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
              (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) z) := by
        rw [hpath_eq]
        exact InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
          Zt B hZt_meas hB h_indep.symm v_B hv_B_pos hB_law pX hpX_nn hpX_meas hpX_law
          (s := 1) one_pos
      have hvar_eq : (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B :=
        NNReal.coe_injective (by show (1 : ℝ) * (v_B : ℝ) = (v_B : ℝ); rw [one_mul])
      set g : ℝ → ℝ :=
        InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 v_B)
        with hg_def
      have hg_nn : ∀ x, 0 ≤ g x := fun x =>
        integral_nonneg fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg _ _ _)
      have h_g_rnDeriv : (fun x => ((P.map (fun ω => B ω + Zt ω)).rnDeriv volume x).toReal)
          =ᵐ[volume] g := by
        filter_upwards [h_path_rnDeriv] with x hx
        rw [hx, hvar_eq, ENNReal.toReal_ofReal (hg_nn x)]
      -- `Integrable (z²) (P.map Zt)` from `h_mom_A` (witness `hsq_law` pattern).
      have hZt_sq : Integrable (fun ω => (Zt ω)^2) P := by
        have : (fun ω => (Zt ω)^2) = (fun ω => (1 / t) * (A ω)^2) := by
          funext ω; simp only [hZt, div_pow, Real.sq_sqrt ht.le]; ring
        rw [this]; exact h_mom_A.const_mul _
      have hνZ_sq : Integrable (fun z => z ^ 2) (P.map Zt) := by
        rw [integrable_map_measure
          ((by fun_prop : Measurable (fun y : ℝ => y ^ 2)).aestronglyMeasurable)
          hZt_meas.aemeasurable]
        simpa [Function.comp] using hZt_sq
      -- invoke the extract lemma (`q := gaussianPDFReal 0 v_B`, `s := 1`).
      have hbase := InformationTheory.Shannon.convCrossEntropy_zAvg_integrable
        (gaussianPDFReal 0 v_B) pX (gaussianPDFReal_nonneg 0 v_B) (measurable_gaussianPDFReal 0 v_B)
        (integrable_gaussianPDFReal 0 v_B) (integral_gaussianPDFReal_eq_one 0 hv_B)
        (InformationTheory.Shannon.integrable_sq_mul_gaussianPDFReal hv_B)
        hpX_nn hpX_meas hpX_int hpX_mass hv_B_pos (s := 1) one_pos (P.map Zt) hνZ_sq
      -- transport the inner integral: `(condDistrib z).rnDeriv · log (path rnDeriv)`
      -- `=ᵐ[P.map Zt] ∫ gaussianPDFReal 0 v_B (x − z)·log (g x) dx` (the `√1·z = z` shift).
      refine hbase.congr ?_
      filter_upwards [h_fibre_ae] with z hz
      have hfib_rn : (fun x => ((condDistrib (fun ω => B ω + Zt ω) Zt P z).rnDeriv volume x).toReal)
          =ᵐ[volume] fun x => gaussianPDFReal 0 v_B (x - z) := by
        have hrn : (condDistrib (fun ω => B ω + Zt ω) Zt P z).rnDeriv volume
            =ᵐ[volume] fun x => ENNReal.ofReal (gaussianPDFReal z v_B x) := by
          rw [hz, h_fibre_gauss z]
          filter_upwards [rnDeriv_gaussianReal z v_B] with x hx
          rw [hx, gaussianPDF]
        filter_upwards [hrn] with x hx
        rw [hx, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg z v_B x)]
        unfold gaussianPDFReal; simp [sub_zero]
      rw [Real.sqrt_one, one_mul]
      refine integral_congr_ae ?_
      filter_upwards [hfib_rn, h_g_rnDeriv] with x hx hxg
      rw [hx, hxg, hg_def]
    · -- log(path rnDeriv) integrable wrt path (path law a.c. + finite second moment;
      -- entropy-finiteness CLOSED asset via convDensityAdd identification bridge).
      have hv_B_pos : (0 : ℝ≥0) < v_B := pos_iff_ne_zero.mpr hv_B
      have hv_B_pos' : (0 : ℝ) < v_B := hv_B_pos
      -- Density witness for `Zt = A/√t`.
      obtain ⟨pX, hpX_nn, hpX_meas, hpX_law, hpX_int, hpX_mass, hpX_mom⟩ :=
        rescaledInput_density_witness A P hA hA_ac h_mom_A ht
      -- `B + Zt = Zt + B = gaussianConvolution Zt B 1` pointwise.
      have hpath_eq : (fun ω => B ω + Zt ω)
          = InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Zt B 1 := by
        funext ω
        simp only [InformationTheory.Shannon.FisherInfoV2.gaussianConvolution,
          Real.sqrt_one, one_mul]
        ring
      -- Path density identification.
      have h_path_rnDeriv : (P.map (fun ω => B ω + Zt ω)).rnDeriv volume
          =ᵐ[volume] fun z => ENNReal.ofReal
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
              (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) z) := by
        rw [hpath_eq]
        exact InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
          Zt B hZt_meas hB h_indep.symm v_B hv_B_pos hB_law pX hpX_nn hpX_meas hpX_law
          (s := 1) one_pos
      set g : ℝ → ℝ := fun x =>
        InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
          (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) x with hg_def
      have hg_nn : ∀ x, 0 ≤ g x := fun x =>
        integral_nonneg fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg _ _ _)
      -- negMulLog asset (variance `1·v_B = v_B`).
      have hvar_eq : (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B := by
        apply NNReal.coe_injective; show (1 : ℝ) * (v_B : ℝ) = (v_B : ℝ); rw [one_mul]
      have h_negMulLog : Integrable (fun x => Real.negMulLog (g x)) volume := by
        rw [hg_def, show (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B from hvar_eq]
        simpa using InformationTheory.Shannon.convDensityAdd_negMulLog_integrable_pub
          hpX_nn hpX_meas hpX_int hpX_mass hpX_mom (t := (v_B : ℝ)) hv_B_pos'
      -- `∫ log p_W d(P.map W) = ∫ p_W·log p_W dx = ∫ -negMulLog p_W dx`, so integrable.
      -- Reduce `Integrable (log p_W) (P.map W)` to `Integrable (p_W·log p_W) volume`.
      have hW_ac' : (P.map (fun ω => B ω + Zt ω))
          = volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
        have hrn := h_path_rnDeriv
        rw [← Measure.withDensity_rnDeriv_eq _ _ hW_ac]
        exact withDensity_congr_ae hrn
      -- `ofReal ∘ g` is a.e.-measurable (a.e.-equal to the measurable path rnDeriv).
      have hg_ofReal_aem : AEMeasurable (fun x => ENNReal.ofReal (g x)) volume :=
        ((P.map (fun ω => B ω + Zt ω)).measurable_rnDeriv volume).aemeasurable.congr
          h_path_rnDeriv
      -- Step 1: replace `log ((path.rnDeriv x).toReal)` with `log (g x)` a.e.-`P.map W`
      -- (the path is a.c., so the vol-a.e. rnDeriv identification holds `P.map W`-a.e.).
      have h_rn_toReal_ae : (fun x => ((P.map (fun ω => B ω + Zt ω)).rnDeriv volume x).toReal)
          =ᵐ[P.map (fun ω => B ω + Zt ω)] g := by
        have h0 : (fun x => ((P.map (fun ω => B ω + Zt ω)).rnDeriv volume x).toReal)
            =ᵐ[volume] g := by
          filter_upwards [h_path_rnDeriv] with x hx
          rw [hx, ENNReal.toReal_ofReal (hg_nn x)]
        exact hW_ac.ae_eq h0
      have h_int_logg : Integrable (fun x => Real.log (g x))
          (P.map (fun ω => B ω + Zt ω)) := by
        -- `Integrable (log g) (P.map W) = Integrable (g·log g) volume`.
        rw [hW_ac', integrable_withDensity_iff_integrable_smul₀' hg_ofReal_aem
          (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
        refine (h_negMulLog.neg).congr (Filter.Eventually.of_forall fun x => ?_)
        simp only [Pi.neg_apply, smul_eq_mul, ENNReal.toReal_ofReal (hg_nn x),
          Real.negMulLog, neg_mul, neg_neg]
      refine h_int_logg.congr ?_
      filter_upwards [h_rn_toReal_ae] with x hx
      rw [hx]
  · -- ===== Upper bundle (per `t`, conditions of
    --       `differentialEntropy_le_gaussian_of_variance_le` + a.c.). =====
    intro t ht
    have h_sqrt_pos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
    set Zt : Ω → ℝ := fun ω => A ω / Real.sqrt t with hZt
    have hZt_meas : Measurable Zt := hA.div_const _
    have h_indep : IndepFun Zt B P := by
      have : Zt = (fun a => a / Real.sqrt t) ∘ A := by funext ω; rfl
      rw [this]
      exact hAB.comp (measurable_id.div_const _) measurable_id
    -- a.c. of `A/√t + B` (= `B + A/√t` reordered, both a.c.).
    have hμ_ac : (P.map (fun ω => Zt ω + B ω)) ≪ volume := by
      have h_indepBZ : IndepFun B Zt P := h_indep.symm
      have hWac : (P.map (fun ω => B ω + Zt ω)) ≪ volume :=
        map_add_absolutelyContinuous B Zt P hB hZt_meas h_indepBZ hB_ac
      have h_path : (fun ω => Zt ω + B ω) = (fun ω => B ω + Zt ω) := by funext ω; ring
      rw [h_path]; exact hWac
    set W : Ω → ℝ := fun ω => Zt ω + B ω with hW_def
    have hW_meas : Measurable W := hZt_meas.add hB
    -- `B` has finite second moment (Gaussian, `memLp_id_gaussianReal`).
    have hB_sq : Integrable (fun ω => (B ω)^2) P := by
      have hB_memLp : MemLp B 2 P := by
        have : MemLp (id : ℝ → ℝ) 2 (P.map B) := by
          rw [hB_law]; exact memLp_id_gaussianReal' 2 (by simp)
        have := (memLp_map_measure_iff (p := 2) (μ := P)
          (g := (id : ℝ → ℝ)) aestronglyMeasurable_id hB.aemeasurable).mp this
        simpa [Function.comp] using this
      simpa using hB_memLp.integrable_sq
    -- `Zt = A/√t` has finite second moment (`h_mom_A`, scaled by `1/t`).
    have hZt_sq : Integrable (fun ω => (Zt ω)^2) P := by
      have : (fun ω => (Zt ω)^2) = (fun ω => (1 / t) * (A ω)^2) := by
        funext ω
        simp only [hZt, div_pow, Real.sq_sqrt ht.le]
        ring
      rw [this]
      exact h_mom_A.const_mul _
    -- `W = Zt + B` is `MemLp 2 P`, so `W` and `W²` are integrable.
    have hW_memLp : MemLp W 2 P := by
      refine MemLp.add ?_ ?_
      · exact (memLp_two_iff_integrable_sq_norm hZt_meas.aestronglyMeasurable).mpr
          (by simpa using hZt_sq)
      · exact (memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).mpr
          (by simpa using hB_sq)
    have hW_int : Integrable W P := hW_memLp.integrable (by norm_num)
    have hW_sq_int : Integrable (fun ω => (W ω)^2) P := hW_memLp.integrable_sq
    refine ⟨hμ_ac, h_var_bound t ht, ?_, ?_⟩
    · -- squared-deviation `(x-m)²` integrable wrt path law (finite second moment of the
      -- path: `A/√t` finite second moment from `h_mom_A` + Gaussian `B` finite variance,
      -- transported to the pushforward law).
      set m : ℝ := ∫ y, y ∂(P.map W) with hm_def
      -- Transport to `P` via `integrable_map_measure`, then expand `(W-m)²`.
      have hg_meas : AEStronglyMeasurable (fun x : ℝ => (x - m)^2) (P.map W) :=
        ((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable
      rw [integrable_map_measure hg_meas hW_meas.aemeasurable]
      -- `(W ω - m)² = W² - 2m·W + m²`, each integrable.
      have hexp : (fun x => (x - m)^2) ∘ W
          = (fun ω => (W ω)^2 - 2 * m * W ω + m^2) := by
        funext ω; simp only [Function.comp]; ring
      rw [hexp]
      exact (hW_sq_int.sub ((hW_int.const_mul (2 * m)))).add
        (integrable_const _)
    · -- negMulLog (path rnDeriv) integrable (path entropy finiteness; entropy-finiteness
      -- CLOSED asset via convDensityAdd identification bridge for the a.c. path law).
      have hv_B_pos : (0 : ℝ≥0) < v_B := pos_iff_ne_zero.mpr hv_B
      -- Density witness for `Zt = A/√t`.
      obtain ⟨pX, hpX_nn, hpX_meas, hpX_law, hpX_int, hpX_mass, hpX_mom⟩ :=
        rescaledInput_density_witness A P hA hA_ac h_mom_A ht
      -- Path density: `(P.map W).rnDeriv volume =ᵐ ofReal (convDensityAdd pX g_{v_B})`.
      -- Use `pPath_eq_convDensityAdd` with X:=Zt, Z:=B, v_Z:=v_B, s:=1.
      have hgconv : InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Zt B 1 = W := by
        funext ω
        simp only [InformationTheory.Shannon.FisherInfoV2.gaussianConvolution, hW_def,
          Real.sqrt_one, one_mul]
      have h_path_rnDeriv : (P.map W).rnDeriv volume
          =ᵐ[volume] fun z => ENNReal.ofReal
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
              (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) z) := by
        have := InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
          Zt B hZt_meas hB h_indep v_B hv_B_pos hB_law pX hpX_nn hpX_meas hpX_law
          (s := 1) one_pos
        rwa [hgconv] at this
      -- The asset gives integrability of `negMulLog (convDensityAdd pX g_{v_B})`.
      -- Normalize the variance witness `⟨1·v_B,_⟩ = ⟨v_B,_⟩`.
      have hvar_eq : (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B := by
        apply NNReal.coe_injective
        show (1 : ℝ) * (v_B : ℝ) = (v_B : ℝ)
        rw [one_mul]
      have h_asset : Integrable (fun x =>
          Real.negMulLog (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
            (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) x)) volume := by
        rw [show (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B from hvar_eq]
        have hv_B_pos' : (0 : ℝ) < v_B := hv_B_pos
        simpa using InformationTheory.Shannon.convDensityAdd_negMulLog_integrable_pub
          hpX_nn hpX_meas hpX_int hpX_mass hpX_mom (t := (v_B : ℝ)) hv_B_pos'
      -- Transfer along the a.e. density identification.
      refine h_asset.congr ?_
      filter_upwards [h_path_rnDeriv] with x hx
      have hcd_nn : 0 ≤ InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
          (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) x :=
        integral_nonneg fun y =>
          mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg _ _ _)
      rw [hx, ENNReal.toReal_ofReal hcd_nn]

/-! ## §4 — Main analytic deliverable

`csiszarLogRatioGap_tendsto_zero_atTop`: composing §2 (cancellation), §3 (per-path
limits), and Gaussian additivity yields `R t → 0`. -/

/-- **`R t → 0` as `t → ∞`** (entropic-CLT-free). Combining the scaling cancellation
(`entropyPower_path_scaling`), the three per-path limits
(`entropyPower_rescaled_path_tendsto`), Gaussian additivity of the noise
(`entropyPower_gaussian_additivity`), and continuity of `log` on positive reals.

The per-`t` regularity (a.c. + entropy integrability of the three W-path laws for
the scaling step; the §3 squeeze regularity bundles `IsRescaledPathRegular` for the
three paths) is threaded as honest preconditions (方針 X); the noise Gaussian laws +
independence are regularity. No EPI / Stam core is bundled.

Genuine analytic glue — **own body is `sorry`-free**, and now **transitively
sorryAx-free** (§3 `entropyPower_rescaled_path_tendsto` is genuinely closed):
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

@audit:ok (independent honesty audit 2026-06-05: own body + transitive sorryAx-free
[propext, Classical.choice, Quot.sound]. `h_scale_X/Y/sum` are regularity preconditions of
`entropyPower_path_scaling` (a.c. + negMulLog integrability), `hZX_law`/`hZY_law`/
`hZXZY_indep`/`hZX_ac`/`hZY_ac`/`hZXZY_ac` are noise Gaussian regularity, `varX/Y/S` +
`h_reg_X/Y/S` are §3's `IsRescaledPathRegular` bundles (audited non-load-bearing, see §3)
threaded transparently. The deliverable is genuine analytic glue (scaling cancellation via
log_mul, three §3 path limits, Gaussian additivity, log-continuity composition → R t → 0);
no EPI/Stam core is bundled. Sufficiency holds: both log arguments converge to N(Z_X)+N(Z_Y)
[via §3 + `entropyPower_gaussian_additivity`], so log-ratio gap → 0.) -/
theorem csiszarLogRatioGap_tendsto_zero_atTop
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    (v_X v_Y : ℝ≥0) (hv_X : v_X ≠ 0) (hv_Y : v_Y ≠ 0)
    (hZX_law : P.map Z_X = gaussianReal 0 v_X)
    (hZY_law : P.map Z_Y = gaussianReal 0 v_Y)
    (hZXZY_indep : IndepFun Z_X Z_Y P)
    -- per-`t` scaling regularity (consumed by `entropyPower_path_scaling`)
    (h_scale_X : ∀ t : ℝ, 0 < t →
      (P.map (fun ω => X ω / Real.sqrt t + Z_X ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => X ω / Real.sqrt t + Z_X ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_Y : ∀ t : ℝ, 0 < t →
      (P.map (fun ω => Y ω / Real.sqrt t + Z_Y ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => Y ω / Real.sqrt t + Z_Y ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_sum : ∀ t : ℝ, 0 < t →
      (P.map (fun ω => (X ω + Y ω) / Real.sqrt t + (Z_X ω + Z_Y ω))) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => (X ω + Y ω) / Real.sqrt t
            + (Z_X ω + Z_Y ω))).rnDeriv volume x).toReal)) volume)
    -- noise laws are a.c. (Gaussian)
    (hZX_ac : (P.map Z_X) ≪ volume) (hZY_ac : (P.map Z_Y) ≪ volume)
    (hZXZY_ac : (P.map (fun ω => Z_X ω + Z_Y ω)) ≪ volume)
    -- per-path variance data + §3 regularity bundles (方針 X, all regularity)
    (varX varY varS : ℝ)
    (h_varX_nn : 0 ≤ varX) (h_varY_nn : 0 ≤ varY) (h_varS_nn : 0 ≤ varS)
    (h_reg_X : IsRescaledPathRegular X Z_X P varX v_X)
    (h_reg_Y : IsRescaledPathRegular Y Z_Y P varY v_Y)
    (h_reg_S : IsRescaledPathRegular (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P
      varS (v_X + v_Y)) :
    Filter.Tendsto
      (fun t => csiszarLogRatioGap X Y Z_X Z_Y P t)
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Abbreviations for the rescaled W-paths and the noise entropy powers.
  set NX := fun t => entropyPower (P.map (fun ω => X ω / Real.sqrt t + Z_X ω)) with hNX
  set NY := fun t => entropyPower (P.map (fun ω => Y ω / Real.sqrt t + Z_Y ω)) with hNY
  set NS := fun t =>
    entropyPower (P.map (fun ω => (X ω + Y ω) / Real.sqrt t + (Z_X ω + Z_Y ω))) with hNS
  -- `v_X + v_Y ≠ 0` over `ℝ≥0`.
  have hv_sum : v_X + v_Y ≠ 0 := by
    intro h
    exact hv_X (le_antisymm (h ▸ le_self_add) bot_le)
  -- Gaussian additivity for the noise sum.
  have hZXZY_law : P.map (fun ω => Z_X ω + Z_Y ω) = gaussianReal 0 (v_X + v_Y) := by
    have h := gaussianReal_add_gaussianReal_of_indepFun hZXZY_indep hZX_law hZY_law
    have h_eq : (Z_X + Z_Y) = fun ω => Z_X ω + Z_Y ω := by funext ω; rfl
    rw [h_eq] at h; simpa using h
  -- Limits of the three rescaled paths (§3).
  have hlimX : Filter.Tendsto NX Filter.atTop (nhds (entropyPower (P.map Z_X))) :=
    entropyPower_rescaled_path_tendsto X Z_X P hX hZX v_X hv_X hZX_law varX h_varX_nn
      hZX_ac h_reg_X
  have hlimY : Filter.Tendsto NY Filter.atTop (nhds (entropyPower (P.map Z_Y))) :=
    entropyPower_rescaled_path_tendsto Y Z_Y P hY hZY v_Y hv_Y hZY_law varY h_varY_nn
      hZY_ac h_reg_Y
  have hlimS : Filter.Tendsto NS Filter.atTop
      (nhds (entropyPower (P.map (fun ω => Z_X ω + Z_Y ω)))) :=
    entropyPower_rescaled_path_tendsto (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P
      (hX.add hY) (hZX.add hZY) (v_X + v_Y) hv_sum hZXZY_law varS h_varS_nn
      hZXZY_ac h_reg_S
  -- `N(law(Z_X + Z_Y)) = N(Z_X) + N(Z_Y)` (Gaussian additivity).
  have h_add : entropyPower (P.map (fun ω => Z_X ω + Z_Y ω))
      = entropyPower (P.map Z_X) + entropyPower (P.map Z_Y) :=
    entropyPower_gaussian_additivity P Z_X Z_Y hZX hZY hZXZY_indep 0 0 v_X v_Y hv_X hv_Y
      hZX_law hZY_law
  -- Positivity of the limit values (entropy power is strictly positive).
  have hNX0_pos : 0 < entropyPower (P.map Z_X) := entropyPower_pos _
  have hNY0_pos : 0 < entropyPower (P.map Z_Y) := entropyPower_pos _
  -- The rescaled gap agrees with `R` eventually (for `t > 0`) via §2 cancellation.
  have h_eventually_eq : ∀ᶠ t in Filter.atTop,
      csiszarLogRatioGap X Y Z_X Z_Y P t
        = Real.log (NS t) - Real.log (NX t + NY t) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    have hsX := h_scale_X t ht
    have hsY := h_scale_Y t ht
    have hsS := h_scale_sum t ht
    -- Scaling identities: `N(path) = t · N(W)`.
    have eqX : entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) = t * NX t :=
      entropyPower_path_scaling X Z_X P hX hZX ht hsX.1 hsX.2
    have eqY : entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) = t * NY t :=
      entropyPower_path_scaling Y Z_Y P hY hZY ht hsY.1 hsY.2
    have eqS : entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)))
        = t * NS t := by
      have := entropyPower_path_scaling (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P
        (hX.add hY) (hZX.add hZY) ht hsS.1 hsS.2
      simpa using this
    -- Positivity for the `log` cancellation.
    have ht_pos : (0 : ℝ) < t := ht
    have hNXt : 0 < NX t := entropyPower_pos _
    have hNYt : 0 < NY t := entropyPower_pos _
    have hNSt : 0 < NS t := entropyPower_pos _
    unfold csiszarLogRatioGap
    rw [eqS, eqX, eqY]
    -- `log (t·NS) − log (t·NX + t·NY) = log NS − log (NX + NY)`.
    rw [show t * NX t + t * NY t = t * (NX t + NY t) by ring]
    rw [Real.log_mul ht_pos.ne' hNSt.ne',
        Real.log_mul ht_pos.ne' (by positivity : (NX t + NY t) ≠ 0)]
    ring
  -- Limit of the rescaled gap: both `log` arguments → `N(Z_X)+N(Z_Y)`.
  have h_lim_rescaled : Filter.Tendsto
      (fun t => Real.log (NS t) - Real.log (NX t + NY t))
      Filter.atTop (nhds (0 : ℝ)) := by
    have hlogS : Filter.Tendsto (fun t => Real.log (NS t)) Filter.atTop
        (nhds (Real.log (entropyPower (P.map Z_X) + entropyPower (P.map Z_Y)))) := by
      rw [← h_add]
      exact (Real.continuousAt_log (entropyPower_pos _).ne').tendsto.comp hlimS
    have hlogD : Filter.Tendsto (fun t => Real.log (NX t + NY t)) Filter.atTop
        (nhds (Real.log (entropyPower (P.map Z_X) + entropyPower (P.map Z_Y)))) := by
      have hsum : Filter.Tendsto (fun t => NX t + NY t) Filter.atTop
          (nhds (entropyPower (P.map Z_X) + entropyPower (P.map Z_Y))) :=
        hlimX.add hlimY
      have hpos : entropyPower (P.map Z_X) + entropyPower (P.map Z_Y) ≠ 0 := by
        positivity
      exact (Real.continuousAt_log hpos).tendsto.comp hsum
    have := hlogS.sub hlogD
    simpa using this
  -- Transfer the limit through the eventual equality.
  exact (Filter.tendsto_congr' h_eventually_eq).mpr h_lim_rescaled

/-! ## §5 — End-to-end case-1 assembly (with-noise)

`entropyPower_add_ge_case1_of_regular`: combine the genuine ratio antitonicity
(`csiszarLogRatioGap_antitoneOn_Ici_zero`, `EPIStamToBridge.lean:1085`) and the
genuine saturation (`csiszarLogRatioGap_tendsto_zero_atTop`, §4) through the
genuine order-limit bridge (§1 `epi_of_csiszarLogRatioGap_tendsto`) to obtain the
classical (case-1, a.c. inputs) entropy power inequality. Pure assembly — no new
analytic content, no `sorry`. -/

/-- **Case-1 EPI (with-noise, entropic-CLT-free), under heat-flow + scaling
regularity**. The classical entropy power inequality
`N(law(X+Y)) ≥ N(law X) + N(law Y)` for a.c. inputs, assembled from the two genuine
pillars:

* `csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1085`, genuine):
  the log-ratio gap `R = csiszarLogRatioGap X Y Z_X Z_Y P` is `AntitoneOn (Set.Ici 0)`.
* `csiszarLogRatioGap_tendsto_zero_atTop` (§4, genuine): `R t → 0` as `t → ∞`.

By the order-limit bridge §1 `epi_of_csiszarLogRatioGap_tendsto`, antitonicity +
`R t → 0` force `R 0 ≥ 0`, hence EPI. **No entropic CLT** — the saturation `R t → 0`
is the scaling squeeze of §4.

All hypotheses are **honest regularity preconditions** (方針 X), the union of the two
pillars' preconditions: pairwise + joint independence (`hXZX`/`hYZY`/`hXYZXY`), the
three `IsDeBruijnRegularityHyp` / `IsHeatFlowEndpointRegular` density-witness bundles,
the per-`t` `h_pos_stam` Fisher/Stam/Blachman bundle (ratio antitone side), the noise
Gaussian laws + a.c. (`hZX_law`/`hZY_law`/`hZXZY_indep`/`hZX_ac`/`hZY_ac`/`hZXZY_ac`),
the per-`t` scaling regularity (`h_scale_X/Y/sum`), and the per-path variance data +
three `IsRescaledPathRegular` bundles (§4 side). **None is load-bearing**: the EPI /
Stam core is supplied genuinely inside the two pillars; the conclusion
`N(X+Y) ≥ N(X)+N(Y)` is not encoded in any hypothesis. Honest naming
(`_of_regular`, not bare `_unconditional`): the regularity preconditions are real.

@audit:ok (independent honesty audit 2026-06-05): genuine assembly of two `@audit:ok`
pillars through one `@audit:ok` bridge; own body `sorry`-free and **transitively
sorryAx-free** (`#print axioms` = [propext, Classical.choice, Quot.sound]; the
antitone pillar's stale "G2 continuity wall" docstring note refers to walls CLOSED
2026-06-05 per audit-tags register). Over-claim check: conclusion is verbatim the
case-1 EPI `N(X+Y) ≥ N(X)+N(Y)`, no weaker substitute. Non-load-bearing AFFIRMED via
core-reconstruction test: the ~30 preconditions are the union of the two pillars'
regularity bundles; granting them (incl. the per-`t` `h_pos_stam` whose
`IsStamInequalityHyp` is itself genuinely provable, `wall:stam-step2-density` CLOSED)
does NOT hand the EPI conclusion — that requires the pillars' genuine de Bruijn
integration + scaling squeeze, neither encoded in any hypothesis. Sufficiency: body
threads pillar args in matching order and composes via §1 bridge.
**@audit:superseded-by(entropyPowerExt_add_ge_unconditional)** (2026-06-08): 本 single-time de Bruijn/
ratio-limit case-1 EPI は、無条件 EPI が route T (smoothing+truncation、`entropyPowerExt_add_ge_finite_ac`
経由 → `entropyPowerExt_add_ge_unconditional`) で case-1 を閉じたため EPI 用途では不要。consumer は dead leaf
`entropyPower_add_ge_case1_of_methodX` のみ (無条件 headline チェーン外)。proof-done ゆえ残置。
注: two-time 版 `entropyPower_add_ge_case1_of_regular_twotime` は別物で smoothing-limit 経由 LIVE。 -/
theorem entropyPower_add_ge_case1_of_regular
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    -- independence (pairwise + joint), shared by both pillars
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    (hXZX : IndepFun X Z_X P) (hYZY : IndepFun Y Z_Y P)
    (hXYZXY : IndepFun (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (hZXZY_indep : IndepFun Z_X Z_Y P)
    -- noise Gaussian laws + variances (§4 side), nonzero
    (v_X v_Y : ℝ≥0) (hv_X : v_X ≠ 0) (hv_Y : v_Y ≠ 0)
    (hZX_law : P.map Z_X = gaussianReal 0 v_X)
    (hZY_law : P.map Z_Y = gaussianReal 0 v_Y)
    (hZX_ac : (P.map Z_X) ≪ volume) (hZY_ac : (P.map Z_Y) ≪ volume)
    (hZXZY_ac : (P.map (fun ω => Z_X ω + Z_Y ω)) ≪ volume)
    -- ratio-antitone density-witness + de Bruijn regularity bundles
    (h_reg_sum : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X' : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y' : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp Y Z_Y P)
    (h_endpt_sum : InformationTheory.Shannon.IsHeatFlowEndpointRegular
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_endpt_X : InformationTheory.Shannon.IsHeatFlowEndpointRegular X Z_X P)
    (h_endpt_Y : InformationTheory.Shannon.IsHeatFlowEndpointRegular Y Z_Y P)
    (h_pos_stam : ∀ (t : ℝ) (ht : 0 < t),
      (0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_X'.reg_at t ht).density_t)) ∧
      (0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_Y'.reg_at t ht).density_t)) ∧
      (0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_sum.reg_at t ht).density_t)) ∧
      InformationTheory.Shannon.EPIStamDischarge.IsStamInequalityHyp
        (fun ω => X ω + Real.sqrt t * Z_X ω)
        (fun ω => Y ω + Real.sqrt t * Z_Y ω) P ∧
      InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
        ((h_reg_X'.reg_at t ht).density_t) ∧
      InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
        ((h_reg_Y'.reg_at t ht).density_t) ∧
      (∫ x, (h_reg_X'.reg_at t ht).density_t x ∂MeasureTheory.volume = 1) ∧
      (∫ x, (h_reg_Y'.reg_at t ht).density_t x ∂MeasureTheory.volume = 1) ∧
      (∀ x, (h_reg_sum.reg_at t ht).density_t x
            = InformationTheory.Shannon.EPIConvDensity.convDensityAdd
                ((h_reg_X'.reg_at t ht).density_t)
                ((h_reg_Y'.reg_at t ht).density_t) x) ∧
      InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady
        ((h_reg_X'.reg_at t ht).density_t)
        ((h_reg_Y'.reg_at t ht).density_t))
    -- per-`t` scaling regularity (§4 side, consumed by `entropyPower_path_scaling`)
    (h_scale_X : ∀ t : ℝ, 0 < t →
      (P.map (fun ω => X ω / Real.sqrt t + Z_X ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => X ω / Real.sqrt t + Z_X ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_Y : ∀ t : ℝ, 0 < t →
      (P.map (fun ω => Y ω / Real.sqrt t + Z_Y ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => Y ω / Real.sqrt t + Z_Y ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_sum : ∀ t : ℝ, 0 < t →
      (P.map (fun ω => (X ω + Y ω) / Real.sqrt t + (Z_X ω + Z_Y ω))) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => (X ω + Y ω) / Real.sqrt t
            + (Z_X ω + Z_Y ω))).rnDeriv volume x).toReal)) volume)
    -- per-path variance data + §3 squeeze regularity bundles (§4 side)
    (varX varY varS : ℝ)
    (h_varX_nn : 0 ≤ varX) (h_varY_nn : 0 ≤ varY) (h_varS_nn : 0 ≤ varS)
    (h_reg_X : IsRescaledPathRegular X Z_X P varX v_X)
    (h_reg_Y : IsRescaledPathRegular Y Z_Y P varY v_Y)
    (h_reg_S : IsRescaledPathRegular (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P
      varS (v_X + v_Y)) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  -- Pillar 1: genuine ratio antitonicity on `Set.Ici 0`.
  have h_anti := csiszarLogRatioGap_antitoneOn_Ici_zero X Y Z_X Z_Y P
    hX hZX hXZX hY hZY hYZY hXYZXY
    h_reg_sum h_reg_X' h_reg_Y'
    h_endpt_sum h_endpt_X h_endpt_Y h_pos_stam
  -- Pillar 2: genuine saturation `R t → 0`.
  have h_lim := csiszarLogRatioGap_tendsto_zero_atTop X Y Z_X Z_Y P
    hX hY hZX hZY v_X v_Y hv_X hv_Y hZX_law hZY_law hZXZY_indep
    h_scale_X h_scale_Y h_scale_sum
    hZX_ac hZY_ac hZXZY_ac
    varX varY varS h_varX_nn h_varY_nn h_varS_nn
    h_reg_X h_reg_Y h_reg_S
  -- Order-limit bridge §1: antitone + `R t → 0` ⟹ EPI.
  exact epi_of_csiszarLogRatioGap_tendsto X Y Z_X Z_Y P h_anti h_lim

/-- **Case-1 EPI under method-X regularity** (entropic-CLT-free, unit-noise form).
`N(P.map(X+Y)) ≥ N(P.map X) + N(P.map Y)` for a.c. inputs, reduced to **method-X
regularity** (a.c. inputs + finite second moments + **standard-normal** `𝒩(0,1)`
noise laws + 4-tuple independence) **plus de Bruijn per-time regularity**.

**PB-1 unit-noise restate (2026-06-05, `epi-case1-debruijn-producer-plan`)**: the noise
laws were generalized `gaussianReal 0 v_X`/`gaussianReal 0 v_Y` (`v_X v_Y` arbitrary
nonzero). Since the conclusion `N(X+Y) ≥ N(X)+N(Y)` does not mention the noise, the noise
is an auxiliary variable and fixing it to `𝒩(0,1)` loses no generality. This is required
so the de Bruijn producers (`isDeBruijnRegularityHyp_of_methodX_unitnoise`) — whose
`IsRegularDeBruijnHypV2.Z_law` hardcodes `gaussianReal 0 1` — can actually supply the
threaded `IsDeBruijnRegularityHyp` group (previously vacuous for `v_X ≠ 1`). The body
re-introduces `v_X v_Y := (1 : ℝ≥0)` existentially to keep the `_of_regular` plumbing
(general `v_B` on the §4 saturation side) unchanged.

@audit-note: independent honesty audit (2026-06-05, fresh auditor, commit c0cd760).
PB-1 restate VERIFIED to genuinely resolve the latent vacuity defect. The old signature
took arbitrary nonzero `v_X v_Y` while threading `IsDeBruijnRegularityHyp X Z_X P`, whose
`reg_at t ht .Z_law` (= `IsRegularDeBruijnHypV2.Z_law`, `FisherInfoV2DeBruijn.lean:210`)
hardcodes `P.map Z_X = gaussianReal 0 1` — so for `v_X ≠ 1` the hypotheses `hZX_law` and
`Z_law` were mutually unsatisfiable, making the theorem vacuously true (premises never
jointly inhabitable). Fixing `hZX_law : P.map Z_X = gaussianReal 0 1` removes the
contradiction. The body's `obtain ⟨v_X, hv_X, hZX_law⟩ : ∃ v, v≠0 ∧ … := ⟨1, one_ne_zero,
hZX_law⟩` is HONEST (not circular `:= h`, not `:True`): it locally re-derives the
`∃ v ≠ 0` shape the `_of_regular` plumbing expects, instantiated at the genuine witness
`v = 1` carried by the unit hypothesis. The conclusion `N(X+Y) ≥ N(X)+N(Y)` is unchanged and
not weakened; the noise is genuinely auxiliary (absent from the conclusion) so the unit
restriction loses no generality. Wrapper itself sorryAx-free (orchestrator-confirmed); the
threaded `IsDeBruijnRegularityHyp` / `h_reg_*` are honest preconditions (residuals live in
the producer's `integrable_deriv`, see `isDeBruijnRegularityHyp_of_methodX_unitnoise`). Not
`@audit:ok` only because it threads residual-carrying regularity hyps (type-check done, not
proof done).

This wrapper discharges the supply-able preconditions of
`entropyPower_add_ge_case1_of_regular` from clean method-X data:
* noise a.c. (`hZX_ac`/`hZY_ac`/`hZXZY_ac`) via `gaussianReal_absolutelyContinuous`
  + `map_add_absolutelyContinuous`;
* the four individual independences from the single 4-tuple
  `iIndepFun ![X,Y,Z_X,Z_Y] P` (pairwise via `iIndepFun.indepFun`, joint via
  `iIndepFun.indepFun_prodMk_prodMk` + `IndepFun.comp`);
* the three `IsRescaledPathRegular` bundles via `isRescaledPathRegular_of_methodX`;
* the per-`t` scaling regularity (`h_scale_*`) via the B(i)-identical density-witness
  plumbing (`rescaledInput_density_witness` + `pPath_eq_convDensityAdd` +
  `convDensityAdd_negMulLog_integrable_pub`);
* the variance bounds (`varX/Y/S := Var[·;P]`) via `IndepFun.variance_fun_add` +
  variance scaling, which hold with equality.

The **de Bruijn per-time regularity group** (`h_reg_*'` / `h_endpt_*` / `h_pos_stam`)
is **not supplied from method-X** (it depends on the moonshot
`epi-debruijn-pertime-closure`) and is threaded as an honest precondition.

Independent honesty audit 2026-06-05 (honest_residual AFFIRMED, 4-check): (1) non-circular
— conclusion `N(X+Y) ≥ N(X)+N(Y)` matches no hypothesis (`IsStamInequalityHyp` is the
Fisher form `1/J_sum ≥ 1/J_X+1/J_Y`, a different statement). (2) non-load-bearing — the
threaded de Bruijn group is regularity, not core: `IsStamInequalityHyp` is genuinely
derivable from pure regularity (`isStamInequalityHyp_via_step3`, takes only
measurability/independence, sorryAx-free), so granting it hands no EPI; the genuine EPI
core lives in `_of_regular`'s two pillars. (3) non-degenerate — non-vacuous (Gaussian
witness inhabits `IsStamInequalityHyp`), conclusion is verbatim case-1 EPI. (4) sufficiency
— body genuinely derives all supply-able `_of_regular` preconditions (4 independences from
the 4-tuple, noise a.c./laws, variance bounds with equality, scaling regularity, three
`IsRescaledPathRegular`) and threads the de Bruijn group verbatim; conclusion follows
(`#print axioms` = [propext, Classical.choice, Quot.sound], sorryAx-free, transitively).
`hXY_ac` honest (sum-a.c. regularity, standard case-1 hyp, cannot encode EPI). Helper
assets (`convDensityAdd_negMulLog_integrable_pub` / `pPath_eq_convDensityAdd` /
`map_add_absolutelyContinuous` / `isRescaledPathRegular_of_methodX`) all `@audit:ok`. Naming
`_of_methodX` honest (de Bruijn group remains open, not `_unconditional`/`_discharged`).
`@residual(plan:epi-debruijn-pertime-closure)` slug correct (established convention shared
by 6 FisherInfoV2DeBruijn* files for the same wall; plan file
`epi-debruijn-pertime-closure-plan.md` exists).
**@audit:superseded-by(entropyPowerExt_add_ge_unconditional)** (2026-06-08): 本 method-X case-1 EPI
wrapper は consumer 0、かつ未解消 de Bruijn per-time 残壁 (`@residual` 下記) を抱える。無条件 EPI は
route T で case-1 を閉じた (`entropyPowerExt_add_ge_unconditional`) ため、この de Bruijn EPI 経路は EPI
用途では不要 = retract 候補。ただし de Bruijn 恒等式 closure 計画 `epi-debruijn-pertime-closure` 自体は
EPI と独立の standalone goal として有効 (本 wrapper の supersede は de Bruijn 計画の中止を意味しない)。
@residual(plan:epi-debruijn-pertime-closure) -/
theorem entropyPower_add_ge_case1_of_methodX
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    -- method-X: input regularity (both inputs a.c. + their sum a.c.; the sum-a.c. is the
    -- standard case-1 hypothesis, NOT derivable from `hX_ac`/`hY_ac` without `X ⊥ Y`)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hXY_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω)^2) P)
    (h_mom_Y : Integrable (fun ω => (Y ω)^2) P)
    -- method-X: noise standard-normal law (unit variance, PB-1 restate — the noise is an
    -- auxiliary variable absent from the conclusion, so fixing it to `𝒩(0,1)` loses no
    -- generality and aligns with the de Bruijn group's unit-variance requirement)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    -- method-X: 4-tuple joint independence (inputs/noise all independent)
    (h_iIndep : iIndepFun ![X, Y, Z_X, Z_Y] P)
    -- de Bruijn per-time regularity (cross-plan thread, NOT supply-able)
    -- @residual(plan:epi-debruijn-pertime-closure)
    (h_reg_sum : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X' : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y' : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp Y Z_Y P)
    (h_endpt_sum : InformationTheory.Shannon.IsHeatFlowEndpointRegular
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_endpt_X : InformationTheory.Shannon.IsHeatFlowEndpointRegular X Z_X P)
    (h_endpt_Y : InformationTheory.Shannon.IsHeatFlowEndpointRegular Y Z_Y P)
    (h_pos_stam : ∀ (t : ℝ) (ht : 0 < t),
      (0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_X'.reg_at t ht).density_t)) ∧
      (0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_Y'.reg_at t ht).density_t)) ∧
      (0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_sum.reg_at t ht).density_t)) ∧
      InformationTheory.Shannon.EPIStamDischarge.IsStamInequalityHyp
        (fun ω => X ω + Real.sqrt t * Z_X ω)
        (fun ω => Y ω + Real.sqrt t * Z_Y ω) P ∧
      InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
        ((h_reg_X'.reg_at t ht).density_t) ∧
      InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
        ((h_reg_Y'.reg_at t ht).density_t) ∧
      (∫ x, (h_reg_X'.reg_at t ht).density_t x ∂MeasureTheory.volume = 1) ∧
      (∫ x, (h_reg_Y'.reg_at t ht).density_t x ∂MeasureTheory.volume = 1) ∧
      (∀ x, (h_reg_sum.reg_at t ht).density_t x
            = InformationTheory.Shannon.EPIConvDensity.convDensityAdd
                ((h_reg_X'.reg_at t ht).density_t)
                ((h_reg_Y'.reg_at t ht).density_t) x) ∧
      InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady
        ((h_reg_X'.reg_at t ht).density_t)
        ((h_reg_Y'.reg_at t ht).density_t)) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  classical
  -- PB-1: unit-noise restate. The noise variances are fixed to `1`; the §4 saturation
  -- side (`entropyPower_rescaled_path_tendsto`) takes a general `v_B`, so `v_X = v_Y = 1`
  -- and `v_sum = 1 + 1 = 2` flow through `_of_regular` unchanged. We rebind the unit laws
  -- to the `gaussianReal 0 v_X` shape the body expects (defeq `v_X := (1 : ℝ≥0)`).
  obtain ⟨v_X, hv_X, hZX_law⟩ :
      ∃ v : ℝ≥0, v ≠ 0 ∧ P.map Z_X = gaussianReal 0 v :=
    ⟨1, one_ne_zero, hZX_law⟩
  obtain ⟨v_Y, hv_Y, hZY_law⟩ :
      ∃ v : ℝ≥0, v ≠ 0 ∧ P.map Z_Y = gaussianReal 0 v :=
    ⟨1, one_ne_zero, hZY_law⟩
  -- ===== C-3a: extract the four individual independences from the 4-tuple. =====
  -- Pointwise reduction of the `![X,Y,Z_X,Z_Y]` family entries.
  have hf_meas : ∀ i, Measurable (![X, Y, Z_X, Z_Y] i) := by
    intro i; fin_cases i <;> simpa using ‹_›
  -- pairwise independences
  have hXZX : IndepFun X Z_X P := by
    have := h_iIndep.indepFun (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
    simpa using this
  have hYZY : IndepFun Y Z_Y P := by
    have := h_iIndep.indepFun (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
    simpa using this
  have hZXZY_indep : IndepFun Z_X Z_Y P := by
    have := h_iIndep.indepFun (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
    simpa using this
  -- joint independence `IndepFun (X+Y) (Z_X+Z_Y) P` via prodMk_prodMk + sum-comp.
  have hXYZXY : IndepFun (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P := by
    have hpair : IndepFun (fun a => (X a, Y a)) (fun a => (Z_X a, Z_Y a)) P := by
      have := h_iIndep.indepFun_prodMk_prodMk hf_meas 0 1 2 3
        (by decide) (by decide) (by decide) (by decide)
      simpa using this
    have hsum : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
    have := hpair.comp hsum hsum
    simpa [Function.comp] using this
  -- ===== C-3b: noise a.c. from Gaussian a.c. + independent-sum a.c. =====
  have hZX_ac : (P.map Z_X) ≪ volume := by
    rw [hZX_law]; exact gaussianReal_absolutelyContinuous 0 hv_X
  have hZY_ac : (P.map Z_Y) ≪ volume := by
    rw [hZY_law]; exact gaussianReal_absolutelyContinuous 0 hv_Y
  have hZXZY_ac : (P.map (fun ω => Z_X ω + Z_Y ω)) ≪ volume :=
    map_add_absolutelyContinuous Z_X Z_Y P hZX hZY hZXZY_indep hZX_ac
  -- noise-sum Gaussian law (independent Gaussians).
  have hv_sum : v_X + v_Y ≠ 0 := by
    intro h
    exact hv_X (le_antisymm (h ▸ le_self_add) bot_le)
  have hZXZY_law : P.map (fun ω => Z_X ω + Z_Y ω) = gaussianReal 0 (v_X + v_Y) := by
    have h := gaussianReal_add_gaussianReal_of_indepFun hZXZY_indep hZX_law hZY_law
    have h_eq : (Z_X + Z_Y) = fun ω => Z_X ω + Z_Y ω := by funext ω; rfl
    rw [h_eq] at h; simpa using h
  -- ===== C-5: variance bounds (hold with equality, `varA := Var[A;P]`). =====
  -- General per-path variance bound: for a method-X input `A` (measurable, finite
  -- second moment) and Gaussian noise `B` (`P.map B = gaussianReal 0 v_B`)
  -- independent of `A`, the path `A/√t + B` has variance exactly `Var[A]/t + v_B`,
  -- so the `≤ varA/t + v_B` bound holds with equality at `varA := Var[A;P]`.
  have h_var_general : ∀ (A B : Ω → ℝ), Measurable A → Measurable B →
      IndepFun A B P → Integrable (fun ω => (A ω)^2) P →
      (v_B : ℝ≥0) → P.map B = gaussianReal 0 v_B →
      ∀ t : ℝ, 0 < t →
        (∫ x, (x - (∫ y, y ∂(P.map (fun ω => A ω / Real.sqrt t + B ω))))^2
              ∂(P.map (fun ω => A ω / Real.sqrt t + B ω)))
            ≤ ProbabilityTheory.variance A P / t + (v_B : ℝ) := by
    intro A B hA hB hAB h_mom_A v_B hB_law t ht
    have h_sqrt_pos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
    set Zt : Ω → ℝ := fun ω => A ω / Real.sqrt t with hZt
    have hZt_meas : Measurable Zt := hA.div_const _
    have hW_meas : Measurable (fun ω => Zt ω + B ω) := hZt_meas.add hB
    -- `A/√t` and `B` finite second moments → `MemLp 2`.
    have hB_memLp : MemLp B 2 P := by
      have hid : MemLp (id : ℝ → ℝ) 2 (P.map B) := by
        rw [hB_law]; exact memLp_id_gaussianReal' 2 (by simp)
      have := (memLp_map_measure_iff (p := 2) (μ := P) (g := (id : ℝ → ℝ))
        aestronglyMeasurable_id hB.aemeasurable).mp hid
      simpa [Function.comp] using this
    have hZt_sq : Integrable (fun ω => (Zt ω)^2) P := by
      have : (fun ω => (Zt ω)^2) = (fun ω => (1 / t) * (A ω)^2) := by
        funext ω; simp only [hZt, div_pow, Real.sq_sqrt ht.le]; ring
      rw [this]; exact h_mom_A.const_mul _
    have hZt_memLp : MemLp Zt 2 P :=
      (memLp_two_iff_integrable_sq_norm hZt_meas.aestronglyMeasurable).mpr (by simpa using hZt_sq)
    -- `Zt ⊥ B`.
    have h_indep : IndepFun Zt B P := by
      have : Zt = (fun a => a / Real.sqrt t) ∘ A := by funext ω; rfl
      rw [this]; exact hAB.comp (measurable_id.div_const _) measurable_id
    -- LHS = `Var[id; P.map path]`.
    have hLHS : (∫ x, (x - (∫ y, y ∂(P.map (fun ω => Zt ω + B ω))))^2
          ∂(P.map (fun ω => Zt ω + B ω)))
        = ProbabilityTheory.variance (fun ω => Zt ω + B ω) P := by
      rw [← ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable]
      exact ProbabilityTheory.variance_id_map hW_meas.aemeasurable
    -- `Var[path] = Var[Zt] + Var[B] = (1/t)Var[A] + v_B`.
    have hVarZt : ProbabilityTheory.variance Zt P
        = (1 / t) * ProbabilityTheory.variance A P := by
      have hZt_eq : Zt = fun ω => (1 / Real.sqrt t) * A ω := by
        funext ω; simp only [hZt]; rw [div_eq_inv_mul, one_div]
      rw [hZt_eq, ProbabilityTheory.variance_const_mul]
      congr 1
      rw [div_pow, one_pow, Real.sq_sqrt ht.le]
    have hVarB : ProbabilityTheory.variance B P = (v_B : ℝ) := by
      rw [← ProbabilityTheory.variance_id_map hB.aemeasurable, hB_law,
        ProbabilityTheory.variance_id_gaussianReal]
    have hVarSum : ProbabilityTheory.variance (fun ω => Zt ω + B ω) P
        = (1 / t) * ProbabilityTheory.variance A P + (v_B : ℝ) := by
      rw [ProbabilityTheory.IndepFun.variance_fun_add hZt_memLp hB_memLp h_indep,
        hVarZt, hVarB]
    rw [hLHS, hVarSum, one_div, inv_mul_eq_div]
  -- Concrete variances.
  set varX : ℝ := ProbabilityTheory.variance X P with hvarX_def
  set varY : ℝ := ProbabilityTheory.variance Y P with hvarY_def
  set varS : ℝ := ProbabilityTheory.variance (fun ω => X ω + Y ω) P with hvarS_def
  have h_varX_nn : 0 ≤ varX := ProbabilityTheory.variance_nonneg X P
  have h_varY_nn : 0 ≤ varY := ProbabilityTheory.variance_nonneg Y P
  have h_varS_nn : 0 ≤ varS := ProbabilityTheory.variance_nonneg _ P
  -- second moment of `X+Y` from `MemLp 2` of `X`,`Y`.
  have h_mom_S : Integrable (fun ω => (X ω + Y ω)^2) P := by
    have hX_memLp : MemLp X 2 P :=
      (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mpr (by simpa using h_mom_X)
    have hY_memLp : MemLp Y 2 P :=
      (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mpr (by simpa using h_mom_Y)
    have hS_memLp : MemLp (fun ω => X ω + Y ω) 2 P := hX_memLp.add hY_memLp
    simpa using hS_memLp.integrable_sq
  -- ===== C-2: the three `IsRescaledPathRegular` bundles. =====
  have h_reg_X : IsRescaledPathRegular X Z_X P varX v_X :=
    isRescaledPathRegular_of_methodX X Z_X P hX hZX v_X hv_X hZX_law hXZX hX_ac
      varX h_varX_nn h_mom_X (h_var_general X Z_X hX hZX hXZX h_mom_X v_X hZX_law)
  have h_reg_Y : IsRescaledPathRegular Y Z_Y P varY v_Y :=
    isRescaledPathRegular_of_methodX Y Z_Y P hY hZY v_Y hv_Y hZY_law hYZY hY_ac
      varY h_varY_nn h_mom_Y (h_var_general Y Z_Y hY hZY hYZY h_mom_Y v_Y hZY_law)
  have h_reg_S : IsRescaledPathRegular (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P
      varS (v_X + v_Y) :=
    isRescaledPathRegular_of_methodX (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P
      (hX.add hY) (hZX.add hZY) (v_X + v_Y) hv_sum hZXZY_law hXYZXY hXY_ac
      varS h_varS_nn h_mom_S
      (h_var_general (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) (hX.add hY) (hZX.add hZY)
        hXYZXY h_mom_S (v_X + v_Y) hZXZY_law)
  -- ===== C-4: per-`t` scaling regularity (B(i)-identical density plumbing). =====
  have h_scale_general : ∀ (A B : Ω → ℝ), Measurable A → Measurable B →
      IndepFun A B P → (P.map A) ≪ volume → Integrable (fun ω => (A ω)^2) P →
      (v_B : ℝ≥0) → v_B ≠ 0 → P.map B = gaussianReal 0 v_B →
      ∀ t : ℝ, 0 < t →
        (P.map (fun ω => A ω / Real.sqrt t + B ω)) ≪ volume ∧
        Integrable (fun x => Real.negMulLog
          (((P.map (fun ω => A ω / Real.sqrt t + B ω)).rnDeriv volume x).toReal)) volume := by
    intro A B hA hB hAB hA_ac h_mom_A v_B hv_B hB_law t ht
    set Zt : Ω → ℝ := fun ω => A ω / Real.sqrt t with hZt
    have hZt_meas : Measurable Zt := hA.div_const _
    have hB_ac : (P.map B) ≪ volume := by
      rw [hB_law]; exact gaussianReal_absolutelyContinuous 0 hv_B
    have h_indep : IndepFun Zt B P := by
      have : Zt = (fun a => a / Real.sqrt t) ∘ A := by funext ω; rfl
      rw [this]; exact hAB.comp (measurable_id.div_const _) measurable_id
    -- a.c. of `A/√t + B`.
    have hμ_ac : (P.map (fun ω => Zt ω + B ω)) ≪ volume := by
      have hWac : (P.map (fun ω => B ω + Zt ω)) ≪ volume :=
        map_add_absolutelyContinuous B Zt P hB hZt_meas h_indep.symm hB_ac
      have h_path : (fun ω => Zt ω + B ω) = (fun ω => B ω + Zt ω) := by funext ω; ring
      rw [h_path]; exact hWac
    refine ⟨hμ_ac, ?_⟩
    -- negMulLog (path rnDeriv) integrable (B(i)-identical, path = `Zt + B`).
    have hv_B_pos : (0 : ℝ≥0) < v_B := pos_iff_ne_zero.mpr hv_B
    obtain ⟨pX, hpX_nn, hpX_meas, hpX_law, hpX_int, hpX_mass, hpX_mom⟩ :=
      rescaledInput_density_witness A P hA hA_ac h_mom_A ht
    have hgconv : InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Zt B 1
        = fun ω => Zt ω + B ω := by
      funext ω
      simp only [InformationTheory.Shannon.FisherInfoV2.gaussianConvolution,
        Real.sqrt_one, one_mul]
    have h_path_rnDeriv : (P.map (fun ω => Zt ω + B ω)).rnDeriv volume
        =ᵐ[volume] fun z => ENNReal.ofReal
          (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
            (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) z) := by
      have := InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
        Zt B hZt_meas hB h_indep v_B hv_B_pos hB_law pX hpX_nn hpX_meas hpX_law
        (s := 1) one_pos
      rwa [hgconv] at this
    have hvar_eq : (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B := by
      apply NNReal.coe_injective; show (1 : ℝ) * (v_B : ℝ) = (v_B : ℝ); rw [one_mul]
    have h_asset : Integrable (fun x =>
        Real.negMulLog (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
          (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) x)) volume := by
      rw [show (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B from hvar_eq]
      have hv_B_pos' : (0 : ℝ) < v_B := hv_B_pos
      simpa using InformationTheory.Shannon.convDensityAdd_negMulLog_integrable_pub
        hpX_nn hpX_meas hpX_int hpX_mass hpX_mom (t := (v_B : ℝ)) hv_B_pos'
    refine h_asset.congr ?_
    filter_upwards [h_path_rnDeriv] with x hx
    have hcd_nn : 0 ≤ InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
        (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) x :=
      integral_nonneg fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg _ _ _)
    rw [hx, ENNReal.toReal_ofReal hcd_nn]
  have h_scale_X := h_scale_general X Z_X hX hZX hXZX hX_ac h_mom_X v_X hv_X hZX_law
  have h_scale_Y := h_scale_general Y Z_Y hY hZY hYZY hY_ac h_mom_Y v_Y hv_Y hZY_law
  have h_scale_sum := h_scale_general (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω)
    (hX.add hY) (hZX.add hZY) hXYZXY hXY_ac h_mom_S (v_X + v_Y) hv_sum hZXZY_law
  -- ===== C-6 + final: thread de Bruijn group, invoke `_of_regular`. =====
  exact entropyPower_add_ge_case1_of_regular X Y Z_X Z_Y P hX hY hZX hZY
    hXZX hYZY hXYZXY hZXZY_indep v_X v_Y hv_X hv_Y hZX_law hZY_law hZX_ac hZY_ac hZXZY_ac
    h_reg_sum h_reg_X' h_reg_Y' h_endpt_sum h_endpt_X h_endpt_Y h_pos_stam
    h_scale_X h_scale_Y h_scale_sum varX varY varS h_varX_nn h_varY_nn h_varS_nn
    h_reg_X h_reg_Y h_reg_S

/-! ## PB-2 — path-identification reduction (B-0) -/

/-- **Path-identification (B-0)**: the standardized noise `Z' = Z/√v` (`v > 0`) on the
time-reparametrized path `X + √(t·v)·Z'` agrees *pointwise* (everywhere, not just a.e.)
with the original path `X + √t·Z`. Used to bridge the sum-instance's `𝒩(0,2)` noise to a
unit `W`. The hypothesis `0 < v` is required (`√v ≠ 0`); the `v = 0` degeneracy (division
by `√0 = 0`) is excluded.

@audit:ok — independent honesty audit (2026-06-05, fresh auditor, commit c0cd760):
genuine 0-sorry pointwise identity (`funext` + `Real.sqrt_mul` + `field_simp`).
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free, transient
`#print axioms` + `lake env lean`). Signature honest: conclusion is an equality of two
explicit `gaussianConvolution` functions, not embedded in any hypothesis; `0 < v` is a
genuine non-degeneracy precondition (excludes the `√0 = 0` division), NOT load-bearing.
`map_gaussianConvolution_rescale_eq` likewise `@audit:ok` (sorryAx-free, single `rw`). -/
theorem gaussianConvolution_rescale_eq {α : Type*}
    (X Z : α → ℝ) (v : ℝ) (hv : 0 < v) (t : ℝ) (ht : 0 ≤ t) :
    InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X
        (fun ω => Z ω / Real.sqrt v) (t * v)
      = InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z t := by
  funext ω
  unfold InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
  rw [Real.sqrt_mul ht v]
  have hsv : Real.sqrt v ≠ 0 := (Real.sqrt_ne_zero' (x := v)).mpr hv
  field_simp

/-- **Path-identification, `P.map` form**: the laws of the standardized time-reparam path
and the original path coincide (consequence of the pointwise identity). -/
theorem map_gaussianConvolution_rescale_eq {α : Type*} [MeasurableSpace α]
    (P : Measure α) (X Z : α → ℝ) (v : ℝ) (hv : 0 < v) (t : ℝ) (ht : 0 ≤ t) :
    P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X
        (fun ω => Z ω / Real.sqrt v) (t * v))
      = P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z t) := by
  rw [gaussianConvolution_rescale_eq X Z v hv t ht]

/-! ## PB-2b — Fisher monotonicity under Gaussian convolution (Stam corollary)

The genuine Stam-side input to closing `integrable_deriv`: convolution with a regular
density only *decreases* Fisher information, `J(pX ∗ fY) ≤ J(pX)`. This is the `lam = 1`
specialization of the genuine convex Fisher bound `convex_fisher_bound_of_ready`
(`EPIBlachmanDensity.lean:932`, `@audit:ok`, sorryAx-free):

    `J(conv) ≤ lam²·J(fX) + (1-lam)²·J(fY)`  →  (`lam = 1`)  →  `J(conv) ≤ J(fX)`.

It is conditioned on the *regularity* preconditions that the genuine Stam machinery
actually requires (`IsRegularDensityV2 fX/fY`, normalization, `IsBlachmanConvReady fX fY`),
NOT on any inequality core — the bound is genuinely supplied by `convex_fisher_bound_of_ready`.

**Why this does NOT directly close `integrable_deriv` for the case-1 producer**: the
producer's input density `pX = (P.map X).rnDeriv volume` is a *general* L¹ a.c. density with
finite second moment. It need NOT satisfy `IsRegularDensityV2` (differentiable + strictly
positive everywhere + both tails → 0) nor the boundedness fields of `IsBlachmanConvReady`
(`pX` and `deriv pX` bounded). So this regularity-conditioned monotonicity lemma cannot be
instantiated at the producer's general `pX`; closing `integrable_deriv` for a general input
needs Fisher monotonicity for *general* L¹ densities (genuine score-of-convolution work, a
Mathlib gap), or a strengthened input regularity precondition on `X`. The lemma below is the
genuine landing of the monotonicity content for the regular case; `integrable_deriv` remains
parked. -/

/-- **Fisher monotonicity under Gaussian convolution** (Stam `lam = 1` corollary).

For densities `fX`, `fY` satisfying the genuine Stam regularity preconditions
(`IsRegularDensityV2`, normalization to `1`, and the `IsBlachmanConvReady` integrability /
boundedness bundle), convolution decreases Fisher information:

    `(J(convDensityAdd fX fY)).toReal ≤ (J fX).toReal`.

Genuine derivation: specialize `convex_fisher_bound_of_ready` at `lam = 1` (RHS collapses to
`1²·J(fX) + 0²·J(fY) = J(fX)`). The hypotheses are regularity preconditions, NOT load-bearing
— the inequality core is supplied by the `@audit:ok` `convex_fisher_bound_of_ready`. -/
theorem fisherInfoOfDensity_convDensityAdd_le
    (fX fY : ℝ → ℝ)
    (hregX : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fX)
    (hregY : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fY)
    (hnormX : ∫ x, fX x ∂MeasureTheory.volume = 1)
    (hnormY : ∫ x, fY x ∂MeasureTheory.volume = 1)
    (hready : InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady fX fY) :
    (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity
        (InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY)).toReal
      ≤ (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity fX).toReal := by
  have h := InformationTheory.Shannon.EPIBlachmanDensity.convex_fisher_bound_of_ready
    fX fY 1 (by norm_num) (le_refl 1) hregX hregY hnormX hnormY hready
  simpa using h

/-! ## PB-3 — `IsDeBruijnRegularityHyp` producer (X / Y, unit-noise direct)

The de Bruijn regularity group threaded by the case-1 wrapper is produced from method-X
input regularity. Since PB-1 fixes the noise to `𝒩(0,1)`, the unit-variance `Z_law`
required by `IsRegularDeBruijnHypV2` is satisfied directly (no reparametrization needed for
the X / Y singletons; the sum-instance `𝒩(0,2)` is the only reparam case, deferred to a
later wave). The `pX`-witness fields are the same plumbing as `IsRegularDeBruijnHypV2.ofHeatFlow`
(`FisherInfoV2DeBruijnBody.lean`); the conv-pin `density_path` reuses the genuine density
of `P.map (X + √t·Z)`. -/

/-- **PB-3 producer (X / Y, unit-noise direct)**: from method-X input regularity (`X`
measurable, a.c., finite second moment) and **standard-normal** noise `Z_X` independent of
`X`, supply the `IsDeBruijnRegularityHyp X Z_X P` group threaded by the case-1 wrapper.

The V2 `reg_at` instance is built directly (mirroring `IsRegularDeBruijnHypV2.ofHeatFlow`'s
field plumbing, but taking the unit `Z_law` from `hZX_law` instead of an
`IsHeatFlowDensity` witness — `ofHeatFlow` only consumes `h_heat.Z_law` anyway, so going
direct avoids bundling the load-bearing heat-equation field). The `density_path`/conv-pin
fields use the genuine convolution density. The `pX` series is a regularity precondition
(`X` has a Lebesgue density + finite variance), discharged genuinely from `hX_ac`/`h_mom_X`.

The `integrable_deriv` field — interval-integrability of `t ↦ (1/2)·J(density_t)` on `[0,T]`
— is now closed by **design (b)** (strengthened input regularity), with only the
`t`-measurability of the integrand remaining parked.

**Closure (2026-06-05, design (b))**. Three input-regularity preconditions are now threaded
(`hreg_pX`, `hnorm_pX`, `hready_pX` — see signature below), together with the earlier
`h_fisher_X`. They state that `pX = (P.map X).rnDeriv volume` is a *regular* L¹ density
(`IsRegularDensityV2 pX`: differentiable + strictly positive + tails → 0 + integrable
derivative), is normalized (`∫ pX = 1`), and satisfies the `Integrable`/boundedness/positivity
bundle `IsBlachmanConvReady pX (gaussianPDFReal 0 v)` against every centered Gaussian
(`h_fisher_X` adds finiteness of the input's Fisher info). **None of these encode the
Fisher-monotonicity / de Bruijn inequality core** — they are regularity preconditions, NOT
load-bearing.

With them the bound is now **GENUINE**:

1. **Fisher monotonicity (Stam), genuine.** For every `t ∈ Ioc 0 T`, `t.toNNReal ≠ 0`, so
   `g_t := gaussianPDFReal 0 t.toNNReal` is a regular normalized density
   (`isRegularDensityV2_gaussianPDFReal`, `integral_gaussianPDFReal_eq_one`). PB-2b
   (`fisherInfoOfDensity_convDensityAdd_le`, sorryAx-free, = `convex_fisher_bound_of_ready` at
   `lam = 1`) then fires directly on `fX := pX`, `fY := g_t`, giving the *uniform* bound
   `(1/2)·J(density_t).toReal ≤ (1/2)·J(pX).toReal =: C` on `Ioc 0 T`, finite and `t`-independent.
   (The bridge `fisherInfoOfMeasureV2 _ f = fisherInfoOfDensity f` is `rfl`, so the measure
   argument is dropped; the integrand reduces to `(1/2)·J(convDensityAdd pX g_t).toReal`.) This
   replaces the previous full park, where the entire field was a single `sorry` because PB-2b was
   deemed not instantiable for a general L¹ `pX` — the design-(b) preconditions make it
   instantiable, and the bound is now machine-checked with no `sorry`.
2. **`t`-measurability** of `t ↦ J(density_t).toReal` (AEStronglyMeasurable on `Ι 0 T`), required
   by `Measure.integrableOn_of_bounded`. The `(t,x)`-jointly measurable
   `logDeriv (convDensityAdd pX g_t)` feeding the `fisherInfoOfDensity` lintegral has no direct
   Mathlib parameter-measurability lemma; this was the **sole remaining residual**, now
   **CLOSED** (2026-06-06) by `EPICase1ProducerMeasurability.aestronglyMeasurable_fisherInfo_t`
   (C-b closed-form score route).

The rest of the group is genuine, and the finite-Fisher precondition is in place so PB-6 can
thread it to the case-1 wrapper.

@audit:ok (independent honesty audit 2026-06-06, fresh auditor, commit 64896e7): the
formerly-parked `integrable_deriv` `t`-measurability residual is CLOSED; own body sorry-free
and **transitively sorryAx-free** (`#print axioms isDeBruijnRegularityHyp_of_methodX_unitnoise`
= `[propext, Classical.choice, Quot.sound]`, machine-confirmed). Stale
`@residual(plan:epi-case1-debruijn-producer-plan)` retired. All threaded preconditions
(`IsRegularDensityV2` / normalization / `IsBlachmanConvReady` / finite Fisher / a.c. / second
moment) verified regularity, NOT load-bearing; the `IsDeBruijnRegularityHyp` structure's
`density_t_eq` anti-trivial-zero pin keeps the conclusion non-degenerate.
@audit-note: independent honesty audit (2026-06-05, fresh auditor, commit c0cd760).
honest_residual — slug VALID (plan exists at `docs/shannon/epi-case1-debruijn-producer-plan.md`).
Verified: (i) `pX` series (pX_nn/pX_meas/pX_law/pX_mom) is a verbatim mirror of
`IsRegularDeBruijnHypV2.ofHeatFlow`'s `@audit:ok` plumbing (`FisherInfoV2DeBruijnBody.lean:275-`,
`withDensity_rnDeriv_eq` + `integrable_map_measure`), genuinely derived from `hX_ac`/`h_mom_X`,
NON-circular. (ii) `reg_at` fields are all regularity/witness (the structure
`IsRegularDeBruijnHypV2` carries NO analytic-core field — de Bruijn is delivered externally by
`debruijnIdentityV2_holds_assembled`), so NO load-bearing `*Hypothesis` bundling; going direct
on `Z_law := hZX_law` rather than via `IsHeatFlowDensity` is honest (only `Z_law` is consumed).
(iii) `density_t_eq := fun _ _ => rfl` genuine (density_t IS the conv-pin). (iv) the sole sorry
is `integrable_deriv` only. CLASSIFICATION REFINED from "Mathlib analytic wall" to
"under-hypothesized (missing finite-entropy/Fisher precondition)"; the `plan:` slug is the
correct home (resolve by threading the precondition). NOTE: the plan (`:403-404`) optimistically
predicted this field closes via `gaussianConv_fisher_le_inv_var` claiming `J ≤ 1/t` is
"continuous bounded" on `[0,T]` — that prediction is mathematically WRONG (`1/t` is unbounded
at `t=0`); the implementer correctly caught the drift and parked instead.
UPDATE 2026-06-05 (design (b)): the uniform Fisher-monotonicity bound is now GENUINE (PB-2b
`fisherInfoOfDensity_convDensityAdd_le` fires on `pX`/`g_t` via the threaded input-regularity
preconditions `hreg_pX`/`hnorm_pX`/`hready_pX`/`h_fisher_X`). The `integrable_deriv` field is no
longer fully parked: its sole remaining `sorry` is the `t`-measurability of the integrand
(AEStronglyMeasurable on `Ι 0 T`), a separate plumbing obstacle (no direct Mathlib
parameter-measurability lemma for the `logDeriv (convDensityAdd …)` lintegral). All four added
preconditions are regularity (regular density / normalization / Integrable-boundedness bundle /
finite Fisher), NOT load-bearing — they do not encode the inequality core.
@audit-note: INDEPENDENT honesty audit of design-(b) change (2026-06-05, fresh auditor, commit
`06a2989`). Verdict honest_residual — CONFIRMED. (1) The 3 added preconditions are genuine
regularity, NOT load-bearing: `hreg_pX` = 7-field `IsRegularDensityV2` (diff / pos / tails→0 /
integrable-deriv / ∫deriv=0); `hnorm_pX` = normalization; `hready_pX` = the 19-field
`IsBlachmanConvReady` bundle (`EPIBlachmanDensity.lean:712-761`, read verbatim) whose every field
is `Integrable (…)` / `∃ M, |·| ≤ M` / `0 < …` — the `int_inner`/`int_prod{1,2,3}`/`int_W`/
`int_Wsq` fields assert only INTEGRABILITY of the Tonelli-expansion integrands, never their
*values* nor any inequality, so the Fisher-monotonicity conclusion `J(conv)≤J(pX)` is NOT smuggled
through `hready_pX` — it is produced by `convex_fisher_bound_of_ready` (`@audit:ok`) at `lam=1`
(RHS collapses to `1²·J(pX)+0²·J(g_t)=J(pX)`). (2) The bound branch is GENUINE, not vacuous:
`integrableOn_of_bounded` (`IntegrableOn.lean:649`) has 3 obligations — `s_finite` (discharged),
`f_mble : AEStronglyMeasurable` (now GENUINE, see below), `f_bdd` (discharged from `hbound`).
`hbound` fires PB-2b on `pX`/`g_t` with `t.toNNReal≠0` genuinely from `t>0`, giving a uniform
`t`-independent finite bound `C=(1/2)·J(pX).toReal`; the rfl bridge `fisherInfoOfMeasureV2_def`
(`FisherInfoV2DeBruijn.lean:90`, genuine `rfl`) is legitimate. (3) sufficiency: non-circular
(conclusion ≢ any hyp), non-degenerate (`density_t_eq:=fun _ _=>rfl` genuine, no `:True` slot).
(4) **[CLOSED 2026-06-06]** the `f_mble` `t`-measurability (formerly the SOLE `sorryAx` leaf) is
now discharged genuinely by `EPICase1ProducerMeasurability.aestronglyMeasurable_fisherInfo_t`
via the **C-b closed-form score route** (`measurable_deriv_with_param` fully avoided): the joint
`(t,x)`-measurability of `logDeriv (convDensityAdd pX g_t)` follows from `deriv (conv_t) =
∫ x, pX x · deriv g_t (z-x)` (differentiation-under-integral for `t>0`, both sides `0` for
`t≤0`) divided by `conv_t`, then `Measurable.lintegral_prod_right`. `Integrable pX` is supplied
genuinely via `Measure.integrable_toReal_rnDeriv`. `#print axioms
isDeBruijnRegularityHyp_of_methodX_unitnoise` = `[propext, Classical.choice, Quot.sound]`
(sorryAx-free, machine-checked 2026-06-06). No deprecated tags in this declaration. -/
noncomputable def isDeBruijnRegularityHyp_of_methodX_unitnoise
    (X Z_X : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hX_ac : (P.map X) ≪ volume) (h_mom_X : Integrable (fun ω => (X ω) ^ 2) P)
    (h_fisher_X : InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity
        (fun x => ((P.map X).rnDeriv volume x).toReal) ≠ ∞)
    -- Design (b) input-regularity preconditions (regularity, NOT load-bearing):
    -- they assert only that the input density `pX` is a *regular* L¹ density (differentiable,
    -- strictly positive, tails → 0, integrable derivative), is normalized, and satisfies the
    -- `Integrable`/boundedness/positivity bundle `IsBlachmanConvReady` against any centered
    -- Gaussian. None of them encode the de Bruijn / Fisher-monotonicity inequality core.
    (hreg_pX : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
        (fun x => ((P.map X).rnDeriv volume x).toReal))
    (hnorm_pX : ∫ x, ((P.map X).rnDeriv volume x).toReal ∂volume = 1)
    (hready_pX : ∀ v : ℝ≥0, v ≠ 0 →
        InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady
          (fun x => ((P.map X).rnDeriv volume x).toReal) (gaussianPDFReal 0 v)) :
    InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P := by
  classical
  -- Real density witness for `X` from a.c.
  set pX : ℝ → ℝ := fun x => ((P.map X).rnDeriv volume x).toReal with hpX_def
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x => ENNReal.toReal_nonneg
  have hpX_meas : Measurable pX :=
    ((P.map X).measurable_rnDeriv volume).ennreal_toReal
  have hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)) := by
    have hfin : ∀ᵐ x ∂volume, (P.map X).rnDeriv volume x < ∞ :=
      Measure.rnDeriv_lt_top (P.map X) volume
    have hcongr : (fun x => ENNReal.ofReal (pX x)) =ᵐ[volume]
        (P.map X).rnDeriv volume := by
      filter_upwards [hfin] with x hx
      simp only [hpX_def, ENNReal.ofReal_toReal hx.ne]
    rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hX_ac]
  have hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume := by
    have hsq_law : Integrable (fun y => y ^ 2) (P.map X) := by
      rw [integrable_map_measure
        ((by fun_prop : Measurable (fun y : ℝ => y ^ 2)).aestronglyMeasurable)
        hX.aemeasurable]
      simpa [Function.comp] using h_mom_X
    rw [hpX_law] at hsq_law
    rw [integrable_withDensity_iff_integrable_smul₀'
      hpX_meas.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at hsq_law
    refine hsq_law.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hpX_nn x)]; ring
  refine
    { density_path := fun t => InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
        (gaussianPDFReal 0 t.toNNReal),
      reg_at := fun t ht =>
        { Z_law := hZX_law
          density_t := InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
            (gaussianPDFReal 0 ⟨t, ht.le⟩)
          density_t_eq := fun _ _ => rfl
          pX := pX
          pX_nn := hpX_nn
          pX_meas := hpX_meas
          pX_law := hpX_law
          pX_mom := hpX_mom }
      density_t_eq := ?_
      integrable_deriv := ?_ }
  · -- density_t_eq: the V2-internal density_t is pinned to density_path t (both = conv-pin).
    intro t ht
    have : t.toNNReal = (⟨t, ht.le⟩ : ℝ≥0) := by
      apply NNReal.eq; exact Real.coe_toNNReal t ht.le
    rw [this]
  · -- integrable_deriv: design (b) — strengthen the input regularity so PB-2b
    -- (`fisherInfoOfDensity_convDensityAdd_le`) applies directly, giving the uniform bound
    -- `(1/2)·J(density_t).toReal ≤ (1/2)·J(pX).toReal =: C` for every `t ∈ Ioc 0 T`.
    -- The bound is GENUINE (no sorry); the only remaining residual is the `t`-measurability of
    -- the integrand, parked separately.
    intro T hT
    -- bridge (item 1): `fisherInfoOfMeasureV2 _ f = fisherInfoOfDensity f` (rfl, measure dropped).
    simp only [InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2_def]
    set C : ℝ := (1 / 2) *
      (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity pX).toReal with hC_def
    -- uniform pointwise bound on `Ioc 0 T`: each `t > 0` gives `t.toNNReal ≠ 0`, so the Gaussian
    -- `g_t := gaussianPDFReal 0 t.toNNReal` is a regular normalized density, and PB-2b fires.
    have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) T,
        (1 / 2) * (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
              (gaussianPDFReal 0 t.toNNReal))).toReal ≤ C := by
      intro t ht
      have htpos : 0 < t := ht.1
      have hv_ne : t.toNNReal ≠ 0 := by
        simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; exact htpos
      have hregY : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
          (gaussianPDFReal 0 t.toNNReal) :=
        InformationTheory.Shannon.EPIBlachmanGaussianWitness.isRegularDensityV2_gaussianPDFReal hv_ne
      have hnormY : ∫ x, gaussianPDFReal 0 t.toNNReal x ∂volume = 1 :=
        ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 hv_ne
      have hmono := fisherInfoOfDensity_convDensityAdd_le pX (gaussianPDFReal 0 t.toNNReal)
        hreg_pX hregY hnorm_pX hnormY (hready_pX _ hv_ne)
      simp only [hC_def]
      exact mul_le_mul_of_nonneg_left hmono (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    refine MeasureTheory.Measure.integrableOn_of_bounded
      (by
        simp only [ne_eq]
        exact (measure_Ioc_lt_top).ne)
      ?_meas (M := C) ?_bdd
    · -- `t`-measurability of `t ↦ (1/2)·J(convDensityAdd pX g_t).toReal`, closed via the
      -- C-b (closed-form score) route in `EPICase1ProducerMeasurability`: the joint
      -- measurability of `logDeriv (convDensityAdd pX g_t)` (= scoreNum / conv) feeds the
      -- `fisherInfoOfDensity` lintegral, parameter-measurable by `lintegral_prod_right`.
      have hpX_int : Integrable pX volume := by
        rw [hpX_def]
        exact MeasureTheory.Measure.integrable_toReal_rnDeriv
      exact InformationTheory.Shannon.EPICase1ProducerMeasurability.aestronglyMeasurable_fisherInfo_t
        hpX_meas hpX_int
    · -- pointwise bound from the genuine `hbound`, transported to the `Ioc`-restricted measure.
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
      intro t ht
      have hnn : (0 : ℝ) ≤ (1 / 2) *
          (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
              (gaussianPDFReal 0 t.toNNReal))).toReal :=
        mul_nonneg (by norm_num) ENNReal.toReal_nonneg
      rw [Real.norm_of_nonneg hnn]
      exact hbound t ht

end InformationTheory.Shannon.EPICase1RatioLimit

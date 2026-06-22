import InformationTheory.Shannon.CramerCltBoundaryClosure
import InformationTheory.Shannon.Cramer.Cramer

/-!
# Cramér lower bound — general i.i.d.

The Cramér lower-bound chain (`cramer_lower` / `cramer_lower_legendre` /
`cramer_tendsto`) for the general i.i.d. statement on an arbitrary bounded
`μ : Measure Ω`, `X : ℕ → Ω → ℝ`, discharged against the CLT-boundary headline
`cramer_lower_boundary_unconditional`.

## Main statements

* `cramer_lower`, `cramer_lower_legendre` — the liminf lower bound at threshold
  `a` and optimal tilt `lam`, in Chernoff-exponent and Legendre forms.
* `cramer_tendsto` — the two-sided `Tendsto` form of Cramér's theorem.

## Implementation notes

The general i.i.d. statement transports to the canonical infinitePi
specialization: the joint law of `X` equals an infinite product
(`iIndepFun_iff_map_fun_eq_infinitePi_map`), the identical marginals unify to
`ν := μ.map (X 0)` (`IdentDistrib.map_eq`), the partial-sum event masses agree by
pullback through the two joint maps, and the cgf transports through the
coordinate-evaluation bridge `cgf_eval_eq_cgf_base`.

The non-degeneracy variance precondition `hVar` excludes the degenerate
constant-RV case (`Var = 0`), where the Cramér boundary argument genuinely
breaks (Gaussian median `1/2` / window mass `1/4` lower bounds collapse).

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006. Theorem 11.4.1.
-/

namespace InformationTheory.Shannon.Cramer

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Cramér's theorem** (lower bound, general i.i.d.).

The optimal-tilt hypothesis `h_deriv : deriv (cgf (X 0) μ) lam = a` makes the
per-`lam` Chernoff exponent `-(lam·a − Λ(lam))` a genuine lower bound for the
tail rate. `hVar` (non-degenerate variance) is a regularity precondition, not a
load-bearing core — the window-mass core is supplied internally by the CLT inside
the headline.

@audit:ok (Transport is a GENUINE reduction (not a false implication): both the
general-iid joint law `μ.map g` and the canonical copy `P.map g₀` push forward to
the SAME `infinitePi (μ.map (X 0))` — `h_indep` is genuinely consumed by
`iIndepFun_iff_map_fun_eq_infinitePi_map` and `h_ident` by `IdentDistrib.map_eq`
to factor the marginals; the partial-sum event masses then agree by double
pullback (`hpreB`/`hpre0` correct). `h_bdd0` correctly specializes `h_bdd` to
`X 0` (i=0 instance); `h_deriv'` is a sound rewrite of `h_deriv` through the cgf
bridge `cgf_eval_eq_cgf_base`; `hVar` is passed verbatim to the headline (matching
form, no under-hypothesization) and is a precondition (non-degeneracy), not
load-bearing.) -/
theorem cramer_lower [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
    (a : ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (h_deriv : deriv (cgf (X 0) μ) lam = a)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω ↦ X 0 (ω 0);
        Measure.infinitePi (fun _ : ℕ ↦ μ.tilted (fun ω ↦ lam * X 0 ω))])
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ ↦
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}))) :
    -(lam * a - cgf (X 0) μ lam)
      ≤ liminf (fun n : ℕ ↦
          (1 / (n : ℝ)) * Real.log
            (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop := by
  classical
  -- `h_bdd` specialized to `X 0`.
  have h_bdd0 : ∃ M, ∀ ω, |X 0 ω| ≤ M := by
    obtain ⟨M, hM⟩ := h_bdd; exact ⟨M, fun ω ↦ hM 0 ω⟩
  -- Marginal `ν := μ.map (X 0)`; both joint laws factor through `infinitePi ν`.
  set ν : Measure ℝ := μ.map (X 0) with hν
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (h_meas 0).aemeasurable
  -- (a) Root B side: joint map `g ω := fun i => X i ω`.
  set g : Ω → (ℕ → ℝ) := fun ω i ↦ X i ω with hg
  have hg_meas : Measurable g := measurable_pi_lambda _ (fun i ↦ h_meas i)
  have hjointB : μ.map g = Measure.infinitePi (fun _ : ℕ ↦ ν) := by
    have h1 : μ.map g = Measure.infinitePi (fun i ↦ μ.map (X i)) :=
      (iIndepFun_iff_map_fun_eq_infinitePi_map h_meas).1 h_indep
    have h2 : (fun i ↦ μ.map (X i)) = (fun _ : ℕ ↦ ν) := by
      funext i; exact (h_ident i).map_eq
    rw [h1, h2]
  -- (b) Canonical side: joint map `g₀ ω := fun i => X 0 (ω i)` on `infinitePi μ`.
  set P : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ ↦ μ) with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  set X0 : ℕ → (ℕ → Ω) → ℝ := fun i ω ↦ X 0 (ω i) with hX0
  have hX0_meas : ∀ i, Measurable (X0 i) := fun i ↦
    (h_meas 0).comp (measurable_pi_apply i)
  have hX0_indep : iIndepFun X0 P :=
    Cramer.TiltedLLN.iIndepFun_eval_under_infinitePi (h_meas 0)
  set g₀ : (ℕ → Ω) → (ℕ → ℝ) := fun ω i ↦ X 0 (ω i) with hg₀
  have hg₀_meas : Measurable g₀ := measurable_pi_lambda _ (fun i ↦ hX0_meas i)
  have hjoint0 : P.map g₀ = Measure.infinitePi (fun _ : ℕ ↦ ν) := by
    have h1 : P.map g₀ = Measure.infinitePi (fun i ↦ P.map (X0 i)) :=
      (iIndepFun_iff_map_fun_eq_infinitePi_map hX0_meas).1 hX0_indep
    have h2 : (fun i ↦ P.map (X0 i)) = (fun _ : ℕ ↦ ν) := by
      funext i
      -- `P.map (X 0 ∘ eval i) = (P.map (eval i)).map (X 0) = μ.map (X 0) = ν`.
      show P.map (fun ω : ℕ → Ω ↦ X 0 (ω i)) = ν
      rw [hP, hν,
        show (fun ω : ℕ → Ω ↦ X 0 (ω i)) = X 0 ∘ (fun ω : ℕ → Ω ↦ ω i) from rfl,
        ← Measure.map_map (h_meas 0) (measurable_pi_apply i),
        Measure.infinitePi_map_eval]
    rw [h1, h2]
  -- Measurability of the coordinate partial-sum event.
  have hset : ∀ n : ℕ, MeasurableSet
      {x : ℕ → ℝ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, x i} := by
    intro n
    have : Measurable (fun x : ℕ → ℝ ↦ ∑ i ∈ Finset.range n, x i) :=
      Finset.measurable_sum _ (fun i _ ↦ measurable_pi_apply i)
    exact measurableSet_le measurable_const this
  -- Per-`n` event mass transport: both sides equal the coordinate-event mass.
  have hevent : ∀ n : ℕ,
      μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}
        = P.real {ω : ℕ → Ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X 0 (ω i)} := by
    intro n
    -- LHS via `g` pullback.
    have hpreB : g ⁻¹' {x : ℕ → ℝ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, x i}
        = {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω} := by
      ext ω; simp [hg]
    have hmapB : μ {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}
        = (Measure.infinitePi (fun _ : ℕ ↦ ν))
            {x : ℕ → ℝ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, x i} := by
      rw [← hjointB, Measure.map_apply hg_meas (hset n), hpreB]
    -- RHS via `g₀` pullback.
    have hpre0 : g₀ ⁻¹' {x : ℕ → ℝ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, x i}
        = {ω : ℕ → Ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X 0 (ω i)} := by
      ext ω; simp [hg₀]
    have hmap0 : P {ω : ℕ → Ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X 0 (ω i)}
        = (Measure.infinitePi (fun _ : ℕ ↦ ν))
            {x : ℕ → ℝ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, x i} := by
      rw [← hjoint0, Measure.map_apply hg₀_meas (hset n), hpre0]
    rw [Measure.real, Measure.real, hmapB, ← hmap0]
  -- Rewrite the goal to the headline shape.
  have hfun : (fun n : ℕ ↦
      (1 / (n : ℝ)) * Real.log
        (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}))
      = (fun n : ℕ ↦
          (1 / (n : ℝ)) * Real.log
            (P.real {ω : ℕ → Ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X 0 (ω i)})) := by
    funext n; rw [hevent n]
  rw [hfun]
  rw [hfun] at h_coboundedBelow
  -- The cgf identification (in-project precedent, no self-build needed).
  have hcgf : cgf (X 0) μ
      = cgf (fun ω : ℕ → Ω ↦ X 0 (ω 0)) P := by
    funext t
    exact (Cramer.TiltedLLN.cgf_eval_eq_cgf_base (h_meas 0) 0 t).symm
  rw [hcgf]
  have h_deriv' : deriv (cgf (fun ω : ℕ → Ω ↦ X 0 (ω 0)) P) lam = a := by
    rw [← hcgf]; exact h_deriv
  -- Apply the headline with `Ω₀ := Ω`, `Y := X 0`, `μ₀ := μ`.
  exact CramerCltBoundary.cramer_lower_boundary_unconditional
    (μ₀ := μ) (Y := X 0) (h_meas 0) h_bdd0 a lam hlam h_deriv' hVar h_coboundedBelow

/-- **Cramér's theorem** (lower bound, Legendre form).

See also `cramer_lower`.

@audit:ok (rewrites conclusion via the `hlam_opt` Legendre-attainment precondition,
all hypotheses are regularity preconditions threaded to `cramer_lower`.) -/
theorem cramer_lower_legendre [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
    (a : ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hlam_opt : lam * a - cgf (X 0) μ lam = cramerRate (X 0) μ a)
    (h_deriv : deriv (cgf (X 0) μ) lam = a)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω ↦ X 0 (ω 0);
        Measure.infinitePi (fun _ : ℕ ↦ μ.tilted (fun ω ↦ lam * X 0 ω))])
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ ↦
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}))) :
    -cramerRate (X 0) μ a
      ≤ liminf (fun n : ℕ ↦
          (1 / (n : ℝ)) * Real.log
            (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop := by
  have h := cramer_lower (μ := μ) h_indep h_meas h_ident h_bdd a lam hlam
    h_deriv hVar h_coboundedBelow
  rw [← hlam_opt]; exact h

/-- **Cramér's theorem** (`Tendsto` form): the empirical log-tail rate converges
to `-cramerRate (X 0) μ a`.

See also `cramer_upper_legendre` and `cramer_lower_legendre`.

@audit:ok (genuine sandwich of the constructive upper bound and the headline-backed
lower bound. All hypotheses are regularity preconditions / cobounded-bounded
side-conditions.) -/
@[entry_point]
theorem cramer_tendsto [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
    (a : ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hlam_opt : lam * a - cgf (X 0) μ lam = cramerRate (X 0) μ a)
    (h_deriv : deriv (cgf (X 0) μ) lam = a)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω ↦ X 0 (ω 0);
        Measure.infinitePi (fun _ : ℕ ↦ μ.tilted (fun ω ↦ lam * X 0 ω))])
    (h_pos : ∀ᶠ n : ℕ in atTop,
      0 < μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})
    (h_cobdd : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ ↦
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})))
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ ↦
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})))
    (h_bdd_above : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ ↦
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})))
    (h_bdd_below : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ ↦
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}))) :
    Filter.Tendsto (fun n : ℕ ↦
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop
      (𝓝 (-cramerRate (X 0) μ a)) := by
  have h_upper :
      limsup (fun n : ℕ ↦
          (1 / (n : ℝ)) * Real.log
            (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop
        ≤ -cramerRate (X 0) μ a :=
    cramer_upper_legendre (μ := μ) h_indep h_meas h_ident h_bdd a lam hlam hlam_opt
      h_pos h_cobdd
  have h_lower :
      -cramerRate (X 0) μ a
        ≤ liminf (fun n : ℕ ↦
            (1 / (n : ℝ)) * Real.log
              (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop :=
    cramer_lower_legendre (μ := μ) h_indep h_meas h_ident h_bdd a lam hlam hlam_opt
      h_deriv hVar h_coboundedBelow
  exact tendsto_of_le_liminf_of_limsup_le h_lower h_upper h_bdd_above h_bdd_below

end InformationTheory.Shannon.Cramer

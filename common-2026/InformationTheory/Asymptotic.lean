import InformationTheory.Meta.EntryPoint
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Asymptotic / exponent framework

The exponent-equality relation `\doteq` of Cover–Thomas and a closed-form rate-extraction
wrapper, forming the asymptotic / rate API layer.

## Notation

* `a ≐ b` (`DotEq a b`): `(Real.log ∘ a − Real.log ∘ b) =o[atTop] (·:ℝ)`.
* The textbook `f(n) = o(n)` is `f =o[atTop] (fun n : ℕ => (n : ℝ))`.
* The textbook `f(n) = o(1)` is `f =o[atTop] (fun _ => (1 : ℝ))`.

## Main definitions

* `DotEq` — exponent equality, defined directly as an `IsLittleO`.

## Main statements

* `dotEq_iff_tendsto_log_div` — the bridge to `(1/n) · log (a/b) → 0` under positivity.
* `exp_decay_N_of_pos` — a closed-form block length for `exp(-n·g) < ε'`.

## Implementation notes

* `DotEq` is `ℝ`-valued; no `ℝ≥0∞` alias is published here.
* The notation `≐` is `scoped[InformationTheory.Asymptotic]`, so only call sites that
  `open InformationTheory.Asymptotic` see it.
* Positivity is not built into the predicate (Mathlib's `Real.log` returns `0` for `x ≤ 0`,
  so `DotEq` is well-defined for any `ℕ → ℝ`); it is required at the bridge / `mul` / `inv`
  use sites instead.
-/

namespace InformationTheory.Asymptotic

open Asymptotics Filter Topology Real

/-- Exponent equality (the textbook `\doteq`): `a ≐ b` when
`Real.log (a n) − Real.log (b n) = o(n)` along `atTop`.

Under positivity `0 < a n ∧ 0 < b n` this is equivalent to
`(1/n) · log (a n / b n) → 0` (`dotEq_iff_tendsto_log_div`). Positivity is required at
the use site rather than in the predicate. -/
@[entry_point]
def DotEq (a b : ℕ → ℝ) : Prop :=
  (fun n : ℕ => Real.log (a n) - Real.log (b n)) =o[atTop] (fun n : ℕ => (n : ℝ))

@[inherit_doc] scoped notation:50 a:51 " ≐ " b:51 => DotEq a b

/-- `DotEq` is reflexive: `Real.log (a n) - Real.log (a n) = 0 = o(n)`. -/
@[entry_point]
lemma DotEq.refl (a : ℕ → ℝ) : a ≐ a := by
  show (fun n : ℕ => Real.log (a n) - Real.log (a n)) =o[atTop] (fun n : ℕ => (n : ℝ))
  have h0 : (fun n : ℕ => Real.log (a n) - Real.log (a n)) = (fun _ : ℕ => (0 : ℝ)) := by
    funext n; ring
  rw [h0]
  exact Asymptotics.isLittleO_zero _ _

/-- `DotEq` is symmetric: swap `a` / `b` and negate the inside. -/
@[entry_point]
lemma DotEq.symm {a b : ℕ → ℝ} (h : a ≐ b) : b ≐ a := by
  show (fun n : ℕ => Real.log (b n) - Real.log (a n)) =o[atTop] (fun n : ℕ => (n : ℝ))
  have h_eq : (fun n : ℕ => Real.log (b n) - Real.log (a n))
      = fun n : ℕ => -(Real.log (a n) - Real.log (b n)) := by
    funext n; ring
  rw [h_eq]
  exact h.neg_left

/-- `DotEq` is transitive: `(log a - log b) + (log b - log c) = (log a - log c)`. -/
@[entry_point]
lemma DotEq.trans {a b c : ℕ → ℝ} (hab : a ≐ b) (hbc : b ≐ c) : a ≐ c := by
  show (fun n : ℕ => Real.log (a n) - Real.log (c n)) =o[atTop] (fun n : ℕ => (n : ℝ))
  have h_eq : (fun n : ℕ => Real.log (a n) - Real.log (c n))
      = fun n : ℕ => (Real.log (a n) - Real.log (b n))
                      + (Real.log (b n) - Real.log (c n)) := by
    funext n; ring
  rw [h_eq]
  exact hab.add hbc

/-- Multiplicative compatibility: `a₁ * a₂ ≐ b₁ * b₂` if `a_i ≐ b_i` (under positivity).

Proof: `log(a₁·a₂) - log(b₁·b₂) = (log a₁ - log b₁) + (log a₂ - log b₂)` via `Real.log_mul`. -/
@[entry_point]
lemma DotEq.mul {a₁ a₂ b₁ b₂ : ℕ → ℝ}
    (hPos₁ : ∀ n, 0 < a₁ n ∧ 0 < b₁ n) (hPos₂ : ∀ n, 0 < a₂ n ∧ 0 < b₂ n)
    (h₁ : a₁ ≐ b₁) (h₂ : a₂ ≐ b₂) :
    (fun n => a₁ n * a₂ n) ≐ (fun n => b₁ n * b₂ n) := by
  show (fun n : ℕ => Real.log (a₁ n * a₂ n) - Real.log (b₁ n * b₂ n))
        =o[atTop] (fun n : ℕ => (n : ℝ))
  have h_eq : (fun n : ℕ => Real.log (a₁ n * a₂ n) - Real.log (b₁ n * b₂ n))
      = fun n : ℕ => (Real.log (a₁ n) - Real.log (b₁ n))
                      + (Real.log (a₂ n) - Real.log (b₂ n)) := by
    funext n
    have ha₁ : a₁ n ≠ 0 := ne_of_gt (hPos₁ n).1
    have hb₁ : b₁ n ≠ 0 := ne_of_gt (hPos₁ n).2
    have ha₂ : a₂ n ≠ 0 := ne_of_gt (hPos₂ n).1
    have hb₂ : b₂ n ≠ 0 := ne_of_gt (hPos₂ n).2
    rw [Real.log_mul ha₁ ha₂, Real.log_mul hb₁ hb₂]
    ring
  rw [h_eq]
  exact h₁.add h₂

/-- Inverse compatibility: `(a n)⁻¹ ≐ (b n)⁻¹` if `a ≐ b`.

Proof: `log a⁻¹ - log b⁻¹ = -(log a - log b)` via `Real.log_inv` (unconditional in Mathlib). -/
@[entry_point]
lemma DotEq.inv {a b : ℕ → ℝ} (h : a ≐ b) :
    (fun n => (a n)⁻¹) ≐ (fun n => (b n)⁻¹) := by
  show (fun n : ℕ => Real.log ((a n)⁻¹) - Real.log ((b n)⁻¹))
        =o[atTop] (fun n : ℕ => (n : ℝ))
  have h_eq : (fun n : ℕ => Real.log ((a n)⁻¹) - Real.log ((b n)⁻¹))
      = fun n : ℕ => -(Real.log (a n) - Real.log (b n)) := by
    funext n
    rw [Real.log_inv, Real.log_inv]; ring
  rw [h_eq]
  exact h.neg_left

/-- Bridge: under positivity, `a ≐ b` is equivalent to
`Tendsto (fun n => (1/n) * log (a n / b n)) atTop (𝓝 0)`. -/
@[entry_point]
lemma dotEq_iff_tendsto_log_div (a b : ℕ → ℝ) (hPos : ∀ n, 0 < a n ∧ 0 < b n) :
    a ≐ b ↔
    Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (a n / b n)) atTop (𝓝 0) := by
  -- `DotEq` ⟺ `(log a - log b) =o[atTop] (·:ℝ)`
  -- ⟺ (by `isLittleO_iff_tendsto'`) `Tendsto ((log a - log b) / n) atTop (𝓝 0)`
  -- ⟺ (under positivity, `log_div`) `Tendsto ((1/n) * log (a/b)) atTop (𝓝 0)`
  have h_eventually : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) = 0 → Real.log (a n) - Real.log (b n) = 0) := by
    filter_upwards [eventually_gt_atTop 0] with n hn h_eq
    exact absurd h_eq (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn))
  have h_iff := Asymptotics.isLittleO_iff_tendsto' (l := atTop)
      (f := fun n : ℕ => Real.log (a n) - Real.log (b n))
      (g := fun n : ℕ => (n : ℝ)) h_eventually
  -- Rewrite the ratio form to the `(1/n) * log (a/b)` form.
  have h_ratio_eq : (fun n : ℕ =>
        (Real.log (a n) - Real.log (b n)) / (n : ℝ))
      = fun n : ℕ => (1 / (n : ℝ)) * Real.log (a n / b n) := by
    funext n
    have ha : a n ≠ 0 := ne_of_gt (hPos n).1
    have hb : b n ≠ 0 := ne_of_gt (hPos n).2
    rw [Real.log_div ha hb]
    ring
  rw [show (a ≐ b)
        = ((fun n : ℕ => Real.log (a n) - Real.log (b n))
            =o[atTop] (fun n : ℕ => (n : ℝ))) from rfl, h_iff, h_ratio_eq]

/-- Closed-form block length for `exp(-n·g) < ε'` (rate-extraction wrapper).
For `g, ε' > 0`, the witness `N := ⌈max 0 (-Real.log ε' / g)⌉ + 1` works. -/
@[entry_point]
theorem exp_decay_N_of_pos {g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N, Real.exp (-(n : ℝ) * g) < ε' := by
  -- Witness: `N := ⌈max 0 (-log ε' / g)⌉ + 1`.
  set t : ℝ := max 0 (-Real.log ε' / g) with ht_def
  set N : ℕ := Nat.ceil t + 1 with hN_def
  refine ⟨N, ?_⟩
  intro n hn_ge
  -- `(n : ℝ) ≥ N = ⌈t⌉ + 1 > t`.
  have h_t_nn : 0 ≤ t := le_max_left _ _
  have h_ceil_lt_succ : (Nat.ceil t : ℝ) < (Nat.ceil t + 1 : ℝ) := by linarith
  have h_t_le_ceil : t ≤ (Nat.ceil t : ℝ) := Nat.le_ceil _
  have h_N_le_n : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have h_N_eq : (N : ℝ) = (Nat.ceil t : ℝ) + 1 := by
    simp [hN_def]
  have h_t_lt_n : t < (n : ℝ) := by
    have : t < (N : ℝ) := by rw [h_N_eq]; linarith
    linarith
  -- `t ≥ -log ε' / g`, hence `-log ε' / g < n`, hence `-log ε' < n · g` (g > 0).
  have h_div_le_t : -Real.log ε' / g ≤ t := le_max_right _ _
  have h_div_lt_n : -Real.log ε' / g < (n : ℝ) := lt_of_le_of_lt h_div_le_t h_t_lt_n
  have h_neg_log_lt : -Real.log ε' < (n : ℝ) * g := by
    rw [div_lt_iff₀ hg] at h_div_lt_n
    exact h_div_lt_n
  have h_lt_log : -((n : ℝ) * g) < Real.log ε' := by linarith
  -- Conclude via `Real.lt_log_iff_exp_lt`.
  have h_iff := Real.lt_log_iff_exp_lt (x := -((n : ℝ) * g)) (y := ε') hε'
  have h_step : Real.exp (-((n : ℝ) * g)) < ε' := h_iff.mp h_lt_log
  have h_neg_eq : -(n : ℝ) * g = -((n : ℝ) * g) := by ring
  rw [h_neg_eq]
  exact h_step

/-! ## Usage examples -/

-- `≐` notation via `dotEq_iff_tendsto_log_div`.
example (a b : ℕ → ℝ) (hPos : ∀ n, 0 < a n ∧ 0 < b n)
    (h : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (a n / b n)) atTop (𝓝 0)) :
    a ≐ b :=
  (dotEq_iff_tendsto_log_div a b hPos).mpr h

-- Direct use of `exp_decay_N_of_pos`.
example {g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N, Real.exp (-(n : ℝ) * g) < ε' :=
  exp_decay_N_of_pos hg hε'

-- `DotEq` reflexivity through the notation.
example (a : ℕ → ℝ) : a ≐ a := DotEq.refl a

end InformationTheory.Asymptotic

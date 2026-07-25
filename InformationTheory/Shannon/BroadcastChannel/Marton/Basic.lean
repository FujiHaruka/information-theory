import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Rate region of Marton's inner bound

Marton's inner bound for a two-receiver broadcast channel with private messages is cut out by
three inequalities on a rate pair `(R₁, R₂)`, stated here over abstract information bounds
`I₁`, `I₂`, `I₁₂` standing for `I(V₁; Y₁)`, `I(V₂; Y₂)` and `I(V₁; V₂)`.

The random coding scheme behind the bound attaches to every message a subcodebook, of rate
`R₁'` for the first receiver and `R₂'` for the second, so the three region inequalities are
traded for one covering constraint `I₁₂ < R₁' + R₂'` together with two decoding constraints
`R₁ + R₁' < I₁` and `R₂ + R₂' < I₂`.  Eliminating the subcodebook rates from that system
recovers the region, and `exists_martonRateSplit` is the converse direction of the
elimination.

## Main definitions

* `InMartonRegion R₁ R₂ I₁ I₂ I₁₂` — the three inequalities cutting out the region.

## Main results

* `exists_martonRateSplit` — a rate pair satisfying the three inequalities strictly admits a
  splitting into positive subcodebook rates meeting the covering and decoding constraints.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

/-- Marton's inner-bound region for a two-receiver broadcast channel with private messages:
a bundle of the two corner inequalities `R₁ ≤ I₁`, `R₂ ≤ I₂` and the sum-rate inequality
`R₁ + R₂ ≤ I₁ + I₂ - I₁₂` on five real numbers. The slots `I₁, I₂, I₁₂` are abstract
information bounds — the predicate does not fix their meaning, the intended instantiation
being `I₁ = I(V₁; Y₁)`, `I₂ = I(V₂; Y₂)` and `I₁₂ = I(V₁; V₂)` for a pair of auxiliary
variables `(V₁, V₂)`.

Taking `I₁₂ = 0` degenerates the sum-rate inequality into the one implied by the two corner
inequalities, so independent auxiliary variables give back the rectangular region of
`InformationTheory.Shannon.BroadcastChannel.InBCCapacityRegion`. -/
structure InMartonRegion (R₁ R₂ I₁ I₂ I₁₂ : ℝ) : Prop where
  /-- Receiver-1 rate bound. -/
  bound₁ : R₁ ≤ I₁
  /-- Receiver-2 rate bound. -/
  bound₂ : R₂ ≤ I₂
  /-- Sum-rate bound, discounted by the dependence between the auxiliary variables. -/
  boundSum : R₁ + R₂ ≤ I₁ + I₂ - I₁₂

theorem InMartonRegion.mono {R₁ R₂ I₁ I₂ I₁₂ I₁' I₂' I₁₂' : ℝ}
    (h : InMartonRegion R₁ R₂ I₁ I₂ I₁₂)
    (h₁ : I₁ ≤ I₁') (h₂ : I₂ ≤ I₂') (h₁₂ : I₁₂' ≤ I₁₂) :
    InMartonRegion R₁ R₂ I₁' I₂' I₁₂' :=
  ⟨h.bound₁.trans h₁, h.bound₂.trans h₂, by linarith [h.boundSum]⟩

/-- Splitting of a strictly interior rate pair into subcodebook rates: the three strict Marton
inequalities produce positive rates `R₁'`, `R₂'` whose sum exceeds `I₁₂` while each message
rate still leaves room for its subcodebook, `R₁ + R₁' < I₁` and `R₂ + R₂' < I₂`. This is the
direction of the Fourier–Motzkin elimination that the coding scheme consumes; the reverse
direction, that such a splitting forces the three inequalities, is immediate. Positivity rather
than nonnegativity is what the covering step needs: it sizes the selection radius by a fraction
of each subcodebook rate, which a rate of zero leaves no room for.

@audit:ok -/
theorem exists_martonRateSplit {R₁ R₂ I₁ I₂ I₁₂ : ℝ}
    (h₁ : R₁ < I₁) (h₂ : R₂ < I₂) (hsum : R₁ + R₂ < I₁ + I₂ - I₁₂) :
    ∃ R₁' R₂' : ℝ, 0 < R₁' ∧ 0 < R₂' ∧ I₁₂ < R₁' + R₂' ∧ R₁ + R₁' < I₁ ∧ R₂ + R₂' < I₂ := by
  have ha : 0 < I₁ - R₁ := sub_pos.mpr h₁
  have hb : 0 < I₂ - R₂ := sub_pos.mpr h₂
  -- Distribute the slack `D = (I₁ - R₁) + (I₂ - R₂)` between the two subcodebooks in
  -- proportion to the room each receiver has, keeping a fraction `θ` of it strictly between
  -- `I₁₂ / D` and `1`.  Clamping `θ` from below at `1 / 2` covers a negative `I₁₂`.
  have key : ∀ D : ℝ, 0 < D → I₁₂ < D → ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ I₁₂ < θ * D := by
    intro D hD hlt
    have hq : I₁₂ / D < 1 := (div_lt_one hD).mpr hlt
    refine ⟨max ((I₁₂ / D + 1) / 2) (1 / 2), lt_of_lt_of_le (by norm_num) (le_max_right _ _),
      max_lt (by linarith) (by norm_num), ?_⟩
    exact (div_lt_iff₀ hD).mp (lt_of_lt_of_le (by linarith) (le_max_left _ _))
  obtain ⟨θ, hθ₀, hθ₁, hθ⟩ := key ((I₁ - R₁) + (I₂ - R₂)) (by linarith) (by linarith)
  refine ⟨(I₁ - R₁) * θ, (I₂ - R₂) * θ, mul_pos ha hθ₀, mul_pos hb hθ₀,
    by nlinarith, ?_, ?_⟩
  · nlinarith [mul_pos ha (sub_pos.mpr hθ₁)]
  · nlinarith [mul_pos hb (sub_pos.mpr hθ₁)]

end InformationTheory.Shannon.BroadcastChannel.Marton

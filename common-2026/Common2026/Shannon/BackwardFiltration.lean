import Common2026.Meta.EntryPoint
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Backward filtration and tail σ-algebra (E-8'' / Birkhoff a.s. — Phase α)

Given a measurable transformation `T : Ω → Ω` on a measurable space `(Ω, m₀)`,
the *backward filtration* is the antitone sequence

```
ℋ_n := T⁻ⁿ(m₀) = MeasurableSpace.comap (T^[n]) m₀
```

Indexed over `ℕᵒᵈ`, this becomes a `MeasureTheory.Filtration ℕᵒᵈ m₀`. The tail
σ-algebra is `ℋ_∞ := ⋂_n ℋ_n`.

These objects underpin the backward martingale approach to Birkhoff's ergodic
theorem (Phase β / γ); see `docs/shannon/birkhoff-ergodic-plan.md`.

## Main definitions

* `backwardFiltration` — the antitone sequence `n ↦ comap (T^[n]) m₀`
  packaged as a `Filtration ℕᵒᵈ m₀`.
* `tailSigma` — the tail σ-algebra `⨅ n, comap (T^[n]) m₀`.

## Main results

* `backwardFiltration_apply` — applied form (definitional).
* `tailSigma_le_comap_iterate` — `tailSigma ≤ comap (T^[n]) m₀` for every `n`.
* `comap_T_tailSigma_le` — `comap T (tailSigma) ≤ tailSigma` (one half of
  T-invariance; the equality direction requires extra structure such as
  measure preservation and is deferred to Phase γ when actually needed).
-/

namespace InformationTheory.Shannon

open MeasureTheory

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-- Backward filtration `ℋ_n := σ(T^[n]) = T⁻ⁿ(m₀)`, indexed by `ℕᵒᵈ`.

In `ℕᵒᵈ`, `n ≤ m` corresponds to `m ≤ n` in `ℕ`, so the underlying ℕ-indexed
family `n ↦ comap (T^[n]) m₀` is antitone — exactly the backward-filtration
shape needed for reverse-time martingale arguments. -/
@[entry_point]
def backwardFiltration (T : Ω → Ω) (hT : Measurable T) : Filtration ℕᵒᵈ m₀ where
  seq n := MeasurableSpace.comap (T^[OrderDual.ofDual n]) m₀
  mono' i j hij := by
    -- `hij : i ≤ j` in `ℕᵒᵈ` means `ofDual j ≤ ofDual i` in `ℕ`.
    set a : ℕ := OrderDual.ofDual i
    set b : ℕ := OrderDual.ofDual j
    have hba : b ≤ a := hij
    -- Goal: `comap (T^[a]) m₀ ≤ comap (T^[b]) m₀`.
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hba
    -- `a = b + k`, so `T^[a] = T^[b+k] = T^[b] ∘ T^[k]`.
    have h_iter : (T^[k]) ∘ (T^[b]) = T^[a] := by
      have := (Function.iterate_add T k b).symm
      -- `T^[k + b] = T^[k] ∘ T^[b]`; `k + b = b + k = a`.
      simpa [hk, Nat.add_comm k b] using this
    -- `m₀.comap (T^[k]) ≤ m₀` since `T^[k]` is measurable.
    have h_T_k : MeasurableSpace.comap (T^[k]) m₀ ≤ m₀ :=
      (hT.iterate k).comap_le
    -- Apply `comap (T^[b])` on both sides.
    have h_lift :
        MeasurableSpace.comap (T^[b]) (MeasurableSpace.comap (T^[k]) m₀)
          ≤ MeasurableSpace.comap (T^[b]) m₀ :=
      MeasurableSpace.comap_mono h_T_k
    -- LHS rewrites via `comap_comp` and `h_iter`.
    have h_rewrite :
        MeasurableSpace.comap (T^[b]) (MeasurableSpace.comap (T^[k]) m₀)
          = MeasurableSpace.comap (T^[a]) m₀ := by
      rw [MeasurableSpace.comap_comp, h_iter]
    rw [h_rewrite] at h_lift
    exact h_lift
  le' i := (hT.iterate (OrderDual.ofDual i)).comap_le

/-- Applied form of `backwardFiltration`. -/
@[simp] lemma backwardFiltration_apply (T : Ω → Ω) (hT : Measurable T) (n : ℕᵒᵈ) :
    (backwardFiltration T hT) n
      = MeasurableSpace.comap (T^[OrderDual.ofDual n]) m₀ := rfl

/-- Tail σ-algebra `ℋ_∞ := ⋂_n ℋ_n = ⨅_n comap (T^[n]) m₀`. -/
@[entry_point, reducible] def tailSigma (T : Ω → Ω) (hT : Measurable T) : MeasurableSpace Ω :=
  ⨅ n : ℕ, (backwardFiltration T hT) (OrderDual.toDual n)

/-- `tailSigma` is bounded above by every level of the backward filtration. -/
@[entry_point]
lemma tailSigma_le_comap_iterate (T : Ω → Ω) (hT : Measurable T) (n : ℕ) :
    tailSigma T hT ≤ MeasurableSpace.comap (T^[n]) m₀ := by
  simpa [tailSigma, backwardFiltration_apply] using
    (iInf_le (fun k : ℕ =>
      MeasurableSpace.comap (T^[OrderDual.ofDual (OrderDual.toDual k)]) m₀) n)

/-- `tailSigma` is contained in `m₀`: it is a sub-σ-algebra of the ambient space. -/
@[entry_point]
lemma tailSigma_le (T : Ω → Ω) (hT : Measurable T) :
    tailSigma T hT ≤ m₀ := by
  -- Use the `n = 0` level: `comap (T^[0]) m₀ = comap id m₀ = m₀`.
  have h0 : tailSigma T hT ≤ MeasurableSpace.comap (T^[0]) m₀ :=
    tailSigma_le_comap_iterate T hT 0
  have h_id : MeasurableSpace.comap (T^[0]) m₀ = m₀ := by
    simp [Function.iterate_zero, MeasurableSpace.comap_id]
  rw [h_id] at h0
  exact h0

/-- One half of T-invariance: pulling the tail σ-algebra back through `T` lands
again inside the tail. The reverse inclusion requires additional structure
(e.g. measure preservation) and is deferred. -/
@[entry_point]
lemma comap_T_tailSigma_le (T : Ω → Ω) (hT : Measurable T) :
    MeasurableSpace.comap T (tailSigma T hT) ≤ tailSigma T hT := by
  -- For every `n`, `tailSigma ≤ comap (T^[n+1]) m₀ = comap T (comap (T^[n]) m₀)`.
  -- Hence `comap T (tailSigma) ≤ comap T (comap (T^[n]) m₀) = comap (T^[n+1]) m₀`,
  -- and re-indexing `k := n+1` gives `comap T (tailSigma) ≤ comap (T^[k]) m₀` for
  -- every `k ≥ 1`. Combined with the `k = 0` case (which collapses to `m₀`,
  -- containing `comap T (tailSigma)` since `T` is measurable), we obtain the
  -- bound for every `k`, hence for the iInf.
  refine le_iInf (fun n => ?_)
  rcases n with _ | k
  · -- `n = 0`: `backwardFiltration` at `0` is `comap (T^[0]) m₀ = m₀`.
    simp [backwardFiltration_apply, Function.iterate_zero]
    -- Goal: `comap T (tailSigma T hT) ≤ m₀`.
    exact (MeasurableSpace.comap_mono (tailSigma_le T hT)).trans hT.comap_le
  · -- `n = k+1`: factor `T^[k+1] = T^[k] ∘ T`.
    have h_le_k : tailSigma T hT ≤ MeasurableSpace.comap (T^[k]) m₀ :=
      tailSigma_le_comap_iterate T hT k
    have h_step :
        MeasurableSpace.comap T (tailSigma T hT)
          ≤ MeasurableSpace.comap T (MeasurableSpace.comap (T^[k]) m₀) :=
      MeasurableSpace.comap_mono h_le_k
    -- `comap T (comap (T^[k]) m₀) = comap (T^[k] ∘ T) m₀ = comap (T^[k+1]) m₀`.
    have h_eq :
        MeasurableSpace.comap T (MeasurableSpace.comap (T^[k]) m₀)
          = MeasurableSpace.comap (T^[k+1]) m₀ := by
      -- `iterate_succ : T^[k.succ] = T^[k] ∘ T`, so `T^[k+1] = T^[k] ∘ T`.
      have h_iter : (T^[k]) ∘ T = T^[k+1] := (Function.iterate_succ T k).symm
      rw [MeasurableSpace.comap_comp, h_iter]
    rw [h_eq] at h_step
    simpa [backwardFiltration_apply] using h_step

end InformationTheory.Shannon

import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AEP.Basic
import InformationTheory.Shannon.SlepianWolf.Basic

/-!
# Slepian–Wolf achievability (corner point of the sum bound)

Starting from the single-shot converse, this file publishes the **deterministic
achievability** of the separate encoder pair `(f_X^n, f_Y^n) + d^n` at the corner
point `R_X = log|α|, R_Y > H(Y)` (Cover–Thomas 15.4).

## Main statements

* `slepian_wolf_achievability_via_Y_aep` — the `X`-uncompressed, `Y`-AEP encoder
  pair: `Ys` is compressed by a single-source AEP code at any rate `R_Y > H(Y)`
  while `Xs` is sent uncompressed at `R_X = log|α|`, achieving error `→ 0`. The
  sum rate `R_X + R_Y > log|α| + H(Y) ≥ H(X, Y)` covers the segment of the
  Slepian–Wolf region along the `R_X = log|α|` boundary.

## Implementation notes

* The `Y`-side AEP code is reused directly from `source_coding_achievability`.
  The encoder pair composes the trivial `X`-encoder
  `f_X := id : (Fin n → α) ≃ Fin (|α|^n)` with `f_Y := aep_encoder`, and the
  joint decoder is `(i, j) ↦ (i_as_xⁿ, aep_decoder j)`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## Definitions -/

/-- The joint error probability of a Slepian–Wolf encoder pair and joint decoder:
the decoder recovers the wrong `(x, y)` pair. -/
noncomputable def swErrorProb
    (μ : Measure Ω) {n M_X M_Y : ℕ}
    (Xs : Ω → Fin n → α) (Ys : Ω → Fin n → β)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y)
    (d : Fin M_X × Fin M_Y → (Fin n → α) × (Fin n → β)) : ℝ :=
  μ.real {ω | d (f_X (Xs ω), f_Y (Ys ω)) ≠ (Xs ω, Ys ω)}

/-! ## Trivial-rate achievability -/

/-- The trivial Slepian–Wolf `X`-encoder: the `Fintype` index of `Fin n → α`. -/
noncomputable def swTrivialEncoderX (n : ℕ) :
    (Fin n → α) → Fin (Fintype.card (Fin n → α)) :=
  (Fintype.equivFin (Fin n → α)).toFun

/-- The trivial Slepian–Wolf `Y`-encoder: the `Fintype` index of `Fin n → β`. -/
@[entry_point]
noncomputable def swTrivialEncoderY (n : ℕ) :
    (Fin n → β) → Fin (Fintype.card (Fin n → β)) :=
  (Fintype.equivFin (Fin n → β)).toFun

/-- The trivial SW joint decoder: apply each axis-equivalence inverse. -/
@[entry_point]
noncomputable def swTrivialDecoder (n : ℕ) :
    Fin (Fintype.card (Fin n → α)) × Fin (Fintype.card (Fin n → β)) →
      (Fin n → α) × (Fin n → β) :=
  fun p => ((Fintype.equivFin (Fin n → α)).invFun p.1,
            (Fintype.equivFin (Fin n → β)).invFun p.2)

/-! ## Sum bound via the Y-side AEP encoder

The `X` side is sent uncompressed (`f_X := identity, M_X := |α|^n`) and the `Y`
side is compressed via AEP at any rate `R_Y > H(Y) = entropy μ (Ys 0)`. The joint
decoder reads `i` as the raw `Xⁿ` (via the trivial inverse) and `j` as the
AEP-decoded `Yⁿ`.
-/

omit [DecidableEq α] [DecidableEq β] in
/-- The `X`-uncompressed, `Y`-AEP encoder pair achieves the corner point
`(log|α|, R_Y)` for any `R_Y > H(Y)` with `errorProb → 0`. Given an AEP `Y`-side
encoder/decoder pair `(c_Y, d_Y)` from `source_coding_achievability` combined with
the trivial `X`-encoder, the Slepian–Wolf error equals the `Y`-side AEP error
because the `X` side is decoded perfectly. The sum rate
`log|α| + R_Y > log|α| + H(Y) ≥ H(X) + H(Y) ≥ H(X, Y)`. -/
@[entry_point]
theorem slepian_wolf_achievability_via_Y_aep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hYs : ∀ i, Measurable (Ys i))
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hindepY_full : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    {R_Y : ℝ} (hR_Y : entropy μ (Ys 0) < R_Y) :
    ∃ M_Y : ℕ → ℕ, ∃ _hM_Y_pos : ∀ n, 0 < M_Y n,
    ∃ f_Y : ∀ n, (Fin n → β) → Fin (M_Y n),
    ∃ d_Y : ∀ n, Fin (M_Y n) → (Fin n → β),
      Tendsto (fun n => Real.log (M_Y n : ℝ) / n) atTop (𝓝 R_Y) ∧
      Tendsto
        (fun n => swErrorProb μ
                    (jointRV Xs n) (jointRV Ys n)
                    (swTrivialEncoderX n)
                    (f_Y n)
                    (fun p => ((Fintype.equivFin (Fin n → α)).invFun p.1, d_Y n p.2)))
        atTop (𝓝 0) := by
  classical
  -- Apply Y-side AEP source coding achievability.
  obtain ⟨M_Y, hM_Y_pos, c_Y, d_Y, hRate, hPe⟩ :=
    source_coding_achievability μ Ys hYs hposY hindepY_full hidentY hR_Y
  refine ⟨M_Y, hM_Y_pos, c_Y, d_Y, hRate, ?_⟩
  -- The SW error equals the Y-side AEP error: the X side is decoded perfectly via the
  -- trivial inverse, so error ⟺ Y-error.
  -- More precisely: swErrorProb n = errorProb μ (jointRV Ys n) (c_Y n ∘ jointRV Ys n) (d_Y n).
  have h_eq : ∀ n,
      swErrorProb μ (jointRV Xs n) (jointRV Ys n)
          (swTrivialEncoderX n) (c_Y n)
          (fun p => ((Fintype.equivFin (Fin n → α)).invFun p.1, d_Y n p.2))
        = InformationTheory.MeasureFano.errorProb μ
            (jointRV Ys n) (fun ω => c_Y n (jointRV Ys n ω)) (d_Y n) := by
    intro n
    unfold swErrorProb InformationTheory.MeasureFano.errorProb
    -- The two error events are equal as sets.
    -- LHS: { ω | ((Fintype.equivFin ...).invFun (swTrivialEncoderX n (jointRV Xs n ω)),
    --             d_Y n (c_Y n (jointRV Ys n ω))) ≠ (jointRV Xs n ω, jointRV Ys n ω) }
    -- The X coord: `equivFin.invFun (equivFin.toFun (X)) = X` always (left_inv).
    -- So the LHS reduces to: d_Y n (c_Y n Y) ≠ Y.
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq]
    -- equivFin.invFun (equivFin.toFun (jointRV Xs n ω)) = jointRV Xs n ω.
    have hX_inv : (Fintype.equivFin (Fin n → α)).invFun
        (swTrivialEncoderX n (jointRV Xs n ω)) = jointRV Xs n ω := by
      unfold swTrivialEncoderX
      exact (Fintype.equivFin (Fin n → α)).left_inv (jointRV Xs n ω)
    -- Goal: (eqInv (swTrivialEncoderX (jointRV Xs n ω)), d_Y n (c_Y n (jointRV Ys n ω)))
    --        ≠ (jointRV Xs n ω, jointRV Ys n ω)
    --       ↔
    --       jointRV Ys n ω ≠ d_Y n (c_Y n (jointRV Ys n ω))
    rw [hX_inv]
    -- Goal: (jointRV Xs n ω, d_Y n (c_Y n (jointRV Ys n ω))) ≠ (jointRV Xs n ω, jointRV Ys n ω)
    --        ↔ jointRV Ys n ω ≠ d_Y n (c_Y n (jointRV Ys n ω))
    constructor
    · intro h hYeq
      apply h
      rw [← hYeq]
    · intro h hPair
      have hY_eq : d_Y n (c_Y n (jointRV Ys n ω)) = jointRV Ys n ω :=
        (Prod.mk.inj hPair).2
      exact h hY_eq.symm
  -- Convert tendsto via the equality.
  refine Tendsto.congr (fun n => (h_eq n).symm) ?_
  -- hPe gives the tendsto.
  -- hPe : Tendsto (fun n => errorProb μ (jointRV Ys n) (fun ω => c_Y n (jointRV Ys n ω)) (d_Y n))
  --          atTop (𝓝 0)
  -- Need: tendsto of toReal of this? swErrorProb is `μ.real`, errorProb is `μ.real`.
  exact hPe

end InformationTheory.Shannon

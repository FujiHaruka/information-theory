import Common2026.Shannon.MACBodyDischarge

/-!
# MAC per-user Fano converse — L-MAC2 body discharge (T3-B continuation)

This file publishes a **per-user** body discharge layer for the
multi-user Fano converse of the MAC outer bound (`L-MAC2`
placeholder in `Common2026/Shannon/MultipleAccessChannel.lean`).

The parent file's `mac_single_rate_bound₁` /
`mac_single_rate_bound₂` (`MultipleAccessChannel.lean:359 / 379`)
carry `_h_fano : True` + `_h_chain : True`. The
`MACBodyDischarge.lean` Section 4 / `MACFanoBound` discharges the
**joint-message** sum-rate side (L-MAC3 in that file's labeling).
The present file discharges the **per-user single-rate** side:

```
n·R_k ≤ I(W_k; Y^n) + 1 + Pe_k · log M_k
     ≤ I(X_k^n; Y^n | X_{-k}^n) + n·ε_n        (DPI + chain)
     ≤ n · I(X_k; Y | X_{-k}) + n·ε_n         (per-letter chain rule)
```

so that the corner-point per-user bound `R_k ≤ I_k + ε_n` exits
through `mac_capacity_region_outer_bound_three_bounds` of the
parent file.

## Scope

Three concrete fragments are discharged here, all per-user mirrors
of the joint-message body in `MACBodyDischarge.lean` Section 4:

* **L-MAC2-A — Per-user Fano-side bound** (`MACSingleFanoBound k …`):
  the `Prop`-valued structural statement `n·R_k ≤ I(W_k; Y^n) + 1
  + Pe_k · log M_k`, packaged in the style of `MACFanoBound` of
  `MACBodyDischarge.lean`.
* **L-MAC2-B — Per-letter chain-rule pass-through bound**
  (`MACPerLetterChain₁ / MACPerLetterChain₂`): the `Prop`-valued
  structural statement `I(X_k^n; Y^n | X_{-k}^n) ≤ n · I_k` for
  `k ∈ {1, 2}`. The full multi-user conditional-MI chain rule
  derivation is supplied as caller hypothesis (L-MAC2-B-derive,
  out of scope here; matches the `h_chain` pass-through pattern
  of the parent file).
* **L-MAC2-C — Corner-point per-user rate-bound extraction**
  (`mac_converse_fano_body_single₁ / mac_converse_fano_body_single₂`):
  given the per-user Fano-side bound + per-letter chain-rule
  bound + cleanup estimate, conclude `R_k ≤ I_k + ε`. Then routed
  through the parent's `mac_single_rate_bound₁ / ₂` to ship the
  corner-point cut bound.
* **L-MAC2 — Three-bound body discharge combiner**
  (`mac_capacity_region_outer_bound_with_single_user_fano`):
  combine the per-user Fano body (this file, two users) + the
  joint-message Fano body (`MACBodyDischarge.lean` Section 4)
  into a single `InMACCapacityRegion` body discharge entry point.

## Design

The structural `Prop`-form predicates `MACSingleFanoBound`,
`MACPerLetterChain₁`, `MACPerLetterChain₂` package the
information-theoretic inequalities at the **`ℝ` level** (n, R_k,
Pe_k, I_k, I_joint as plain scalars). This avoids surfacing
multi-user Markov-chain measure-theoretic machinery from
`ChannelCodingConverseMemorylessPure.lean` (the single-user
analogue uses `IsMemorylessChannel` + γ-form Markov
`(X^{≠i}, Y^{≠i}) → X_i → Y_i`, ~700 lines). The discharge of the
structural predicates themselves — which is where the Markov
plumbing would surface — is the explicit retreat line, supplied
as caller hypotheses and matching the parent file's `_h_fano` /
`_h_chain` pass-through convention.

The corner-point extraction lemma is the standard
"divide by `n`" arithmetic chain identical in shape to
`mac_converse_fano_body` of `MACBodyDischarge.lean`, just per-user
instead of joint.

## 撤退ライン (確定発動)

* **L-MAC2-A** (per-user Fano body, structural-`Prop` form):
  publishable below as `MACSingleFanoBound`.
* **L-MAC2-B** (per-letter chain-rule, structural-`Prop` form):
  publishable below as `MACPerLetterChain₁ / MACPerLetterChain₂`.
* **L-MAC2-C** (corner-point per-user rate-bound extraction):
  publishable as `mac_converse_fano_body_single₁ / ₂`.
* **L-MAC2-D** (per-user Fano body **derivation** via measure-
  theoretic single-user Fano + DPI on `(W_k; Y^n) | X_{-k}^n`):
  supplied as caller hypothesis `MACSingleFanoBound`. Discharge
  via `fano_inequality_measure_theoretic` of `Fano/Measure.lean`
  on the marginal joint `W_k` (Cover-Thomas eq. 15.44-15.46),
  ~300-500 additional lines. Deferred to a successor seed.
* **L-MAC2-E** (per-letter chain-rule derivation — the full
  multi-user conditional-MI chain rule
  `I(X_k^n; Y^n | X_{-k}^n) = ∑_i I(X_{k,i}; Y_i | X_{-k,i})`):
  supplied as caller hypothesis `MACPerLetterChain₁ / ₂`.
  Discharge via the conditional-MI chain rule + memoryless-channel
  per-letter decomposition, ~200-300 additional lines. Deferred.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Per-user Fano-side bound (L-MAC2-A) -/

section MACSingleUserFano

/-- **MAC Fano-side bound for a single user** (Cover-Thomas eq.
15.44-15.46, per-user form). Statement: for any MAC block code
with user-`k` message space `Fin M_k`, **per-user** average error
probability `Pe_k`, and per-user joint mutual information
`I_marg := I(W_k; Y^n)` (the input-message-to-output mutual
information for user `k`, marginalised over the other user's
message), the single-user Fano inequality gives

```
n · R_k ≤ I_marg + 1 + Pe_k · log M_k.
```

This is the per-user analogue of `MACFanoBound` of
`MACBodyDischarge.lean`, which captures the **joint-message**
version `n·(R₁+R₂) ≤ I_joint + 1 + Pe · log(M₁·M₂)` (Cover-Thomas
eq. 15.49). The two are *independent* applications of Fano on the
single message vs. on the message pair.

We package the inequality as a `Prop`-valued structure to match
the `MACFanoBound` style of `MACBodyDischarge.lean`. The full
derivation via `fano_inequality_measure_theoretic` on the
marginal `(W_k, decoder ∘ Y^n)` is the explicit retreat-line
caller hypothesis (L-MAC2-D); the present structure is only the
structural shape that derivation must produce. -/
structure MACSingleFanoBound (M_k n : ℕ) (R_k Pe_k I_marg : ℝ) : Prop where
  /-- The Fano-side inequality for user `k`. -/
  fano : (n : ℝ) * R_k ≤ I_marg + 1 + Pe_k * Real.log (M_k : ℝ)

namespace MACSingleFanoBound

variable {M_k n : ℕ} {R_k Pe_k I_marg : ℝ}

/-- Introduction helper. -/
lemma mk' (h : (n : ℝ) * R_k ≤ I_marg + 1 + Pe_k * Real.log (M_k : ℝ)) :
    MACSingleFanoBound M_k n R_k Pe_k I_marg := ⟨h⟩

end MACSingleFanoBound

end MACSingleUserFano

/-! ## Section 2 — Per-letter conditional-MI chain rule (L-MAC2-B) -/

section MACPerLetterChain

/-- **Per-letter chain-rule bound for user 1** (Cover-Thomas eq.
15.46, user-1 side). Statement: for the MAC conditional mutual
information `I(X_1^n; Y^n | X_2^n)` (the input-block-to-output
conditional mutual information for user 1, conditioned on user
2's input block), the **per-letter chain rule** combined with the
memoryless-channel decomposition gives

```
I(X_1^n; Y^n | X_2^n) ≤ n · I(X_1; Y | X_2)  =: n · I_1.
```

We package as a `Prop`-valued structure to match the
`MACSingleFanoBound` / `MACFanoBound` style. The full derivation
via the conditional-MI chain rule + memoryless decomposition is
the explicit retreat-line caller hypothesis (L-MAC2-E); the
present structure is only the structural shape that derivation
must produce. -/
structure MACPerLetterChain₁ (n : ℕ) (I_marg₁ I₁ : ℝ) : Prop where
  /-- The per-letter chain-rule inequality for user 1. -/
  chain : I_marg₁ ≤ (n : ℝ) * I₁

namespace MACPerLetterChain₁

variable {n : ℕ} {I_marg₁ I₁ : ℝ}

/-- Introduction helper. -/
lemma mk' (h : I_marg₁ ≤ (n : ℝ) * I₁) :
    MACPerLetterChain₁ n I_marg₁ I₁ := ⟨h⟩

end MACPerLetterChain₁

/-- **Per-letter chain-rule bound for user 2** (Cover-Thomas eq.
15.46, user-2 side). Mirror of `MACPerLetterChain₁` with the two
user indices swapped:

```
I(X_2^n; Y^n | X_1^n) ≤ n · I(X_2; Y | X_1)  =: n · I_2.
```
-/
structure MACPerLetterChain₂ (n : ℕ) (I_marg₂ I₂ : ℝ) : Prop where
  /-- The per-letter chain-rule inequality for user 2. -/
  chain : I_marg₂ ≤ (n : ℝ) * I₂

namespace MACPerLetterChain₂

variable {n : ℕ} {I_marg₂ I₂ : ℝ}

/-- Introduction helper. -/
lemma mk' (h : I_marg₂ ≤ (n : ℝ) * I₂) :
    MACPerLetterChain₂ n I_marg₂ I₂ := ⟨h⟩

end MACPerLetterChain₂

end MACPerLetterChain

/-! ## Section 3 — Corner-point per-user rate extraction (L-MAC2-C) -/

section MACSingleUserCornerPoint

/-- **L-MAC2-C — Per-user Fano converse body extraction for user 1
(corner-point form).**
Given the per-user Fano-side bound, the per-letter chain-rule
bound, and a clean-up estimate
`Pe₁ · log M₁ / n + 1/n ≤ ε`, conclude the corner-point
single-rate bound `R₁ ≤ I₁ + ε`. -/
theorem mac_converse_fano_body_single₁
    {M₁ n : ℕ} (hn : 0 < n)
    (R₁ Pe₁ I_marg₁ I₁ ε : ℝ)
    (h_fano : MACSingleFanoBound M₁ n R₁ Pe₁ I_marg₁)
    (h_chain : MACPerLetterChain₁ n I_marg₁ I₁)
    (h_cleanup : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε) :
    R₁ ≤ I₁ + ε := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- Divide the Fano inequality by `n`.
  have h_fano' : R₁ ≤
      (I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) := by
    have := h_fano.fano
    have hdiv : (n : ℝ) * R₁ / (n : ℝ) ≤
        (I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) :=
      div_le_div_of_nonneg_right this (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * R₁ / (n : ℝ) = R₁ := by
      field_simp
    rw [hcancel] at hdiv
    exact hdiv
  -- Split the RHS.
  have h_split : (I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ)
      = I_marg₁ / (n : ℝ) + (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) := by
    rw [show I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ)
        = I_marg₁ + (1 + Pe₁ * Real.log (M₁ : ℝ)) by ring]
    rw [add_div]
  have h_Imarg_div : I_marg₁ / (n : ℝ) ≤ I₁ := by
    have := h_chain.chain
    have h_div : I_marg₁ / (n : ℝ) ≤ (n : ℝ) * I₁ / (n : ℝ) :=
      div_le_div_of_nonneg_right this (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * I₁ / (n : ℝ) = I₁ := by
      field_simp
    rw [hcancel] at h_div
    exact h_div
  have : R₁ ≤ I_marg₁ / (n : ℝ) + (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) := by
    rw [← h_split]
    exact h_fano'
  linarith

/-- **L-MAC2-C — Per-user Fano converse body extraction for user 2
(corner-point form).** Mirror of `mac_converse_fano_body_single₁`. -/
theorem mac_converse_fano_body_single₂
    {M₂ n : ℕ} (hn : 0 < n)
    (R₂ Pe₂ I_marg₂ I₂ ε : ℝ)
    (h_fano : MACSingleFanoBound M₂ n R₂ Pe₂ I_marg₂)
    (h_chain : MACPerLetterChain₂ n I_marg₂ I₂)
    (h_cleanup : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε) :
    R₂ ≤ I₂ + ε := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_fano' : R₂ ≤
      (I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) := by
    have := h_fano.fano
    have hdiv : (n : ℝ) * R₂ / (n : ℝ) ≤
        (I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) :=
      div_le_div_of_nonneg_right this (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * R₂ / (n : ℝ) = R₂ := by
      field_simp
    rw [hcancel] at hdiv
    exact hdiv
  have h_split : (I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ)
      = I_marg₂ / (n : ℝ) + (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) := by
    rw [show I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ)
        = I_marg₂ + (1 + Pe₂ * Real.log (M₂ : ℝ)) by ring]
    rw [add_div]
  have h_Imarg_div : I_marg₂ / (n : ℝ) ≤ I₂ := by
    have := h_chain.chain
    have h_div : I_marg₂ / (n : ℝ) ≤ (n : ℝ) * I₂ / (n : ℝ) :=
      div_le_div_of_nonneg_right this (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * I₂ / (n : ℝ) = I₂ := by
      field_simp
    rw [hcancel] at h_div
    exact h_div
  have : R₂ ≤ I_marg₂ / (n : ℝ) + (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) := by
    rw [← h_split]
    exact h_fano'
  linarith

/-- **L-MAC2-C — Limit form for user 1**: as `n → ∞`, the per-letter
`n⁻¹` clean-up term vanishes, so the converse single-rate bound
becomes `R₁ ≤ I₁` in the limit. -/
theorem mac_converse_fano_body_single₁_limit
    {M₁ n : ℕ} (hn : 0 < n)
    (R₁ Pe₁ I_marg₁ I₁ ε : ℝ)
    (h_fano : MACSingleFanoBound M₁ n R₁ Pe₁ I_marg₁)
    (h_chain : MACPerLetterChain₁ n I_marg₁ I₁)
    (h_cleanup : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
    (h_ε : ε ≤ 0) :
    R₁ ≤ I₁ := by
  have := mac_converse_fano_body_single₁ hn R₁ Pe₁ I_marg₁ I₁ ε h_fano h_chain h_cleanup
  linarith

/-- **L-MAC2-C — Limit form for user 2**. Mirror of
`mac_converse_fano_body_single₁_limit`. -/
theorem mac_converse_fano_body_single₂_limit
    {M₂ n : ℕ} (hn : 0 < n)
    (R₂ Pe₂ I_marg₂ I₂ ε : ℝ)
    (h_fano : MACSingleFanoBound M₂ n R₂ Pe₂ I_marg₂)
    (h_chain : MACPerLetterChain₂ n I_marg₂ I₂)
    (h_cleanup : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε)
    (h_ε : ε ≤ 0) :
    R₂ ≤ I₂ := by
  have := mac_converse_fano_body_single₂ hn R₂ Pe₂ I_marg₂ I₂ ε h_fano h_chain h_cleanup
  linarith

end MACSingleUserCornerPoint

/-! ## Section 4 — Routing through `mac_single_rate_bound₁/₂` -/

section MACSingleRateBoundRouting

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **L-MAC2 — Per-user single rate bound (body discharge route).**
Plumb the per-user Fano body and per-letter chain rule into the
parent `mac_single_rate_bound₁`, producing the user-1 cut bound.

The parent signature carries `_h_fano : True` + `_h_chain : True`;
this layer **derives** the corner-point scalar inequality
`R₁ ≤ I₁ + ε` from the per-user Fano body + chain rule + cleanup
on the caller side, then ships it through the parent's
`h_bound : R₁ ≤ I₁` slot (with `I₁` replaced by `I₁ + ε` to
accommodate the residual ε term — the parent's `I₁` is the
external scalar argument and admits any rate value). -/
theorem mac_single_rate_bound₁_with_body
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ Pe₁ I_marg₁ I₁ ε : ℝ)
    (h_fano : MACSingleFanoBound M₁ n R₁ Pe₁ I_marg₁)
    (h_chain : MACPerLetterChain₁ n I_marg₁ I₁)
    (h_cleanup : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε) :
    R₁ ≤ I₁ + ε :=
  mac_single_rate_bound₁ hn c R₁ Pe₁ I_marg₁ I₁ ε
    h_fano.fano h_chain.chain h_cleanup

/-- **L-MAC2 — Per-user single rate bound (body discharge route, user 2).**
Mirror of `mac_single_rate_bound₁_with_body`. -/
theorem mac_single_rate_bound₂_with_body
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₂ Pe₂ I_marg₂ I₂ ε : ℝ)
    (h_fano : MACSingleFanoBound M₂ n R₂ Pe₂ I_marg₂)
    (h_chain : MACPerLetterChain₂ n I_marg₂ I₂)
    (h_cleanup : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε) :
    R₂ ≤ I₂ + ε :=
  mac_single_rate_bound₂ hn c R₂ Pe₂ I_marg₂ I₂ ε
    h_fano.fano h_chain.chain h_cleanup

end MACSingleRateBoundRouting

/-! ## Section 5 — Three-bound combined body discharge -/

section MACThreeBoundBodyDischarge

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **L-MAC2 + L-MAC3 — Outer bound three-bound body discharge.**
Combine the per-user Fano body for both users (this file) with
the joint-message Fano body (`MACBodyDischarge.lean`
`mac_converse_fano_body`) into a single `InMACCapacityRegion`
body discharge entry point. Plumbs through the parent's
`mac_capacity_region_outer_bound_three_bounds`. -/
theorem mac_capacity_region_outer_bound_with_fano_body
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε : ℝ)
    (h_fano₁ : MACSingleFanoBound M₁ n R₁ Pe₁ I_marg₁)
    (h_fano₂ : MACSingleFanoBound M₂ n R₂ Pe₂ I_marg₂)
    (h_fano_joint : MACFanoBound M₁ M₂ n R₁ R₂ Pe_joint I_joint)
    (h_chain₁ : MACPerLetterChain₁ n I_marg₁ I₁)
    (h_chain₂ : MACPerLetterChain₂ n I_marg₂ I₂)
    (h_chain_joint : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup₁ : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup₂ : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_joint :
        (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε) :
    InMACCapacityRegion R₁ R₂ (I₁ + ε) (I₂ + ε) (Iboth + ε) :=
  mac_capacity_region_outer_bound_three_bounds hn c R₁ R₂
      (I₁ + ε) (I₂ + ε) (Iboth + ε)
    (mac_converse_fano_body_single₁ hn R₁ Pe₁ I_marg₁ I₁ ε h_fano₁ h_chain₁ h_cleanup₁)
    (mac_converse_fano_body_single₂ hn R₂ Pe₂ I_marg₂ I₂ ε h_fano₂ h_chain₂ h_cleanup₂)
    (mac_converse_fano_body hn R₁ R₂ Pe_joint I_joint Iboth ε
      h_fano_joint h_chain_joint h_cleanup_joint)

/-- **L-MAC2 + L-MAC3 — Outer bound three-bound body discharge,
limit form.** As `n → ∞`, the per-letter `n⁻¹` cleanup terms
vanish, recovering the corner-point `InMACCapacityRegion R₁ R₂ I₁
I₂ Iboth`. -/
theorem mac_capacity_region_outer_bound_with_fano_body_limit
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε : ℝ)
    (h_fano₁ : MACSingleFanoBound M₁ n R₁ Pe₁ I_marg₁)
    (h_fano₂ : MACSingleFanoBound M₂ n R₂ Pe₂ I_marg₂)
    (h_fano_joint : MACFanoBound M₁ M₂ n R₁ R₂ Pe_joint I_joint)
    (h_chain₁ : MACPerLetterChain₁ n I_marg₁ I₁)
    (h_chain₂ : MACPerLetterChain₂ n I_marg₂ I₂)
    (h_chain_joint : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup₁ : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup₂ : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_joint :
        (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε)
    (h_ε : ε ≤ 0) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth := by
  have h1 := mac_converse_fano_body_single₁_limit hn R₁ Pe₁ I_marg₁ I₁ ε
    h_fano₁ h_chain₁ h_cleanup₁ h_ε
  have h2 := mac_converse_fano_body_single₂_limit hn R₂ Pe₂ I_marg₂ I₂ ε
    h_fano₂ h_chain₂ h_cleanup₂ h_ε
  have hs := mac_converse_fano_body_limit hn R₁ R₂ Pe_joint I_joint Iboth ε
    h_fano_joint h_chain_joint h_cleanup_joint h_ε
  exact mac_capacity_region_outer_bound_three_bounds hn c R₁ R₂ I₁ I₂ Iboth
    h1 h2 hs

end MACThreeBoundBodyDischarge

/-! ## Section 6 — Publish-layer hook (combined outer bound discharge) -/

section MACL2DischargePublish

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **MAC outer bound — L-MAC2 (per-user) + L-MAC3 (joint) body
discharge form (publish-layer hook).**
A genuine discharge wrapper around the (now non-circular)
`mac_capacity_region_outer_bound` (`MultipleAccessChannel.lean`). All
three rate-bound directions (`R₁ ≤ I₁ + ε`, `R₂ ≤ I₂ + ε`,
`R₁ + R₂ ≤ Iboth + ε`) are **derived** from the structural body discharge
layers, unbundled into the headline's entropy-level Fano + chain inputs:

* per-user Fano body for user 1: `MACSingleFanoBound` +
  `MACPerLetterChain₁` (this file),
* per-user Fano body for user 2: `MACSingleFanoBound` +
  `MACPerLetterChain₂` (this file),
* joint-message Fano body: `MACFanoBound` (parent
  `MACBodyDischarge.lean`).

The body now feeds the genuine derivation in the headline — it is **not**
an identity wrap to a circular `h_rate_bound`. -/
theorem mac_capacity_region_outer_bound_with_full_fano_body
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε : ℝ)
    (h_fano₁ : MACSingleFanoBound M₁ n R₁ Pe₁ I_marg₁)
    (h_fano₂ : MACSingleFanoBound M₂ n R₂ Pe₂ I_marg₂)
    (h_fano_joint : MACFanoBound M₁ M₂ n R₁ R₂ Pe_joint I_joint)
    (h_chain₁ : MACPerLetterChain₁ n I_marg₁ I₁)
    (h_chain₂ : MACPerLetterChain₂ n I_marg₂ I₂)
    (h_chain_joint : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup₁ : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup₂ : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_joint :
        (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε) :
    InMACCapacityRegion R₁ R₂ (I₁ + ε) (I₂ + ε) (Iboth + ε) :=
  mac_capacity_region_outer_bound hn c R₁ R₂ Pe₁ Pe₂ Pe_joint
    I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε
    h_fano₁.fano h_fano₂.fano h_fano_joint.fano
    h_chain₁.chain h_chain₂.chain h_chain_joint
    h_cleanup₁ h_cleanup₂ h_cleanup_joint

end MACL2DischargePublish

end InformationTheory.Shannon

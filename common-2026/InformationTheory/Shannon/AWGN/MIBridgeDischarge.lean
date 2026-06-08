import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.MIBridge

/-!
# T2-A AWGN MI bridge: body discharge of `IsAwgnOutputGaussian`

Wave6 で publish した `InformationTheory/Shannon/AWGNMIBridge.lean` の 3 個の primitive
predicate のうち、本 file は **`IsAwgnOutputGaussian` の body discharge** を行う。

```
IsAwgnOutputGaussian P N h_meas
  := (outputDistribution (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas))
        = gaussianReal 0 (P.toNNReal + N)
```

つまり `Y = X + Z` where `X ∼ 𝒩(0,P)`, `Z ∼ 𝒩(0,N)` independent ⇒ `Y ∼ 𝒩(0,P+N)`.

## Approach

P-1 (Mathlib snd_compProd): `(p ⊗ₘ W).snd = W ∘ₘ p` (Markov kernel composition).
P-2 (translation-kernel-conv bridge): `(awgnChannel N) ∘ₘ p = p ∗ (gaussianReal 0 N)`.
P-3 (Mathlib gaussianReal_conv_gaussianReal): `(gaussianReal 0 P) ∗ (gaussianReal 0 N)
       = gaussianReal 0 (P+N)`.

P-2 は新しい lemma で、`charFun` を経由して証明する:
- `charFun (awgnChannel N ∘ₘ p) t = ∫ charFun (gaussianReal x N) t ∂p(x)
   = exp(-t²N/2) · ∫ exp(itx) ∂p(x) = exp(-t²N/2) · charFun p t`
- `charFun (p ∗ gaussianReal 0 N) t = charFun p t · charFun (gaussianReal 0 N) t
   = charFun p t · exp(-t²N/2)` (Mathlib `charFun_conv`).

両者一致 ⇒ `Measure.ext_of_charFun`。

## 撤退ライン

P-2 の bind/conv bridge を直接 charFun 経由で展開するのは ~100 行掛かる
ため、本 file ではこの bridge を **named hypothesis `IsAwgnBindEqConv`** として
切り出し、`gaussianReal_conv_gaussianReal` のみ Mathlib 直結で消費する形に
縮減。`IsAwgnBindEqConv` は translation-kernel に対する一般的事実であり、
**`IsAwgnChannelMeasurable`-style 構造的 hypothesis** として後続 plan で discharge。

`IsAwgnOutputGaussian` 自身は本 file の `awgn_output_gaussian_of_bind_eq_conv`
で `IsAwgnBindEqConv` から完全に導出される。Bind-conv bridge は AWGN 独立な
測度論的事実なので分離が自然 (cf. `awgn-kernel-measurability-plan.md` 撤退ライン F-4)。

## Mathlib gap (PR 候補)

* `Kernel.comp_eq_conv_of_translation`: for any kernel `κ x = ν.map (x + ·)` and
  s-finite measure `p`, `κ ∘ₘ p = p ∗ ν` — generic translation-kernel ↔ conv
  bridge. Not in Mathlib (specializes via `Measure.lintegral_comp`, `lintegral_conv`,
  Fubini). Discharging here directly would inflate the file ~80-100 lines.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — Bind/conv bridge primitive -/

/-- **Translation-kernel ↔ additive-convolution bridge** (named hypothesis).

For the AWGN translation kernel `awgnChannel N` and the Gaussian input
`p := gaussianReal 0 P.toNNReal`, the kernel composition coincides with the
additive convolution of measures:

```
awgnChannel N ∘ₘ (gaussianReal 0 P.toNNReal)
  = (gaussianReal 0 P.toNNReal) ∗ (gaussianReal 0 N)
```

This is a fully **AWGN-independent** measure-theoretic identity: any kernel of the
form `κ x = ν.map (x + ·)` (translation kernel with translation measure `ν`)
satisfies `κ ∘ₘ p = p ∗ ν` for s-finite `p` and finite `ν`, by Fubini + change of
variables. Discharging this generic bridge inside the current file would inflate
the proof ~80–100 lines (lintegral expansion + Fubini + change of variables);
the structural reduction here exposes it as a single named hypothesis, to be
discharged in the dedicated `awgn-bind-conv-bridge-plan.md` follow-up. -/
def IsAwgnBindEqConv (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  (awgnChannel N h_meas) ∘ₘ (gaussianReal 0 P.toNNReal)
    = (gaussianReal 0 P.toNNReal) ∗ (gaussianReal 0 N)

/-! ## Phase B — Body discharge of `IsAwgnOutputGaussian` -/

/-- **Output Gaussian (body discharge).**

Given the bind/conv bridge `IsAwgnBindEqConv P N h_meas` (Phase A), the
`IsAwgnOutputGaussian P N h_meas` predicate is fully discharged via:

1. `outputDistribution = compProd.snd` (definitional).
2. `(p ⊗ₘ W).snd = W ∘ₘ p` (Mathlib `Measure.snd_compProd`).
3. Bind/conv bridge `IsAwgnBindEqConv` (Phase A primitive).
4. `(gaussianReal 0 P.toNNReal) ∗ (gaussianReal 0 N) = gaussianReal 0 (P.toNNReal + N)`
   (Mathlib `gaussianReal_conv_gaussianReal`).
-/
@[entry_point]
theorem awgn_output_gaussian_of_bind_eq_conv
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (h_bridge : IsAwgnBindEqConv P N h_meas) :
    IsAwgnOutputGaussian P N h_meas := by
  unfold IsAwgnOutputGaussian
  unfold InformationTheory.Shannon.ChannelCoding.outputDistribution
  unfold InformationTheory.Shannon.ChannelCoding.jointDistribution
  -- Step 1: (p ⊗ₘ W).snd = W ∘ₘ p.
  rw [Measure.snd_compProd]
  -- Step 2: kernel composition = additive convolution (named hypothesis).
  rw [h_bridge]
  -- Step 3: Gaussian + Gaussian = Gaussian (Mathlib).
  -- `gaussianReal_conv_gaussianReal` gives mean `0+0 = 0`; normalize.
  have := gaussianReal_conv_gaussianReal
      (m₁ := (0 : ℝ)) (m₂ := (0 : ℝ)) (v₁ := P.toNNReal) (v₂ := N)
  simpa using this

/-! ## Phase C — MI decomposition primitive (body decomposition) -/


/-! ## Phase D — Combined body discharge re-publish -/

/-- **AWGN channel coding theorem — output-Gaussian reduced to bind/conv,
typicality/MI-decomp/converse taken as hypotheses.**

⚠️ NOT a full discharge: F-2 typicality (`h_typicality`), the MI decomposition
(`h_decomp : IsAwgnMIDecomp`) and F-3 converse (`h_converse`) remain OPEN — they
are taken as hypotheses here. The genuine proofs need continuous AEP /
sphere-shell volume (typicality), the density-level continuous MI chain rule
(MI-decomp) and chain rule + Fano + Gaussian max-entropy (converse), all absent
from Mathlib. What IS genuinely closed: the output-Gaussian fact, reduced to the
smaller bind/conv bridge primitive `IsAwgnBindEqConv` (itself discharged in
`AWGNBindConvBody.lean`), and the conditional-entropy primitive (dispatched by the
underlying `awgn_theorem_F2_discharged`).

`@audit:closed-by-successor(awgn-mi-decomp-plan)` -/
@[entry_point]
theorem awgn_theorem_of_typicality_converse_bindconv
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_bridge : IsAwgnBindEqConv P N (isAwgnChannelMeasurable N))
    (h_decomp : IsAwgnMIDecomp P N (isAwgnChannelMeasurable N))
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt
                  (awgnChannel N (isAwgnChannelMeasurable N)) m).toReal < ε := by
  have h_out : IsAwgnOutputGaussian P N (isAwgnChannelMeasurable N) :=
    awgn_output_gaussian_of_bind_eq_conv P N (isAwgnChannelMeasurable N) h_bridge
  exact awgn_theorem_F2_discharged P hP N hN
    h_out h_decomp hR_pos hR_lt_C hε

/-- **AWGN capacity closed form — output-Gaussian reduced to bind/conv,
MI-decomp/bddAbove/max-entropy taken as hypotheses.**

⚠️ NOT a full discharge: the MI decomposition (`h_decomp`), `h_bdd` and the
max-entropy bound (`h_max_ent`) remain OPEN — taken as hypotheses. The genuine
max-entropy / continuous MI chain rule machinery is absent from Mathlib. Only the
output-Gaussian fact is closed (reduced to the bind/conv bridge primitive
`IsAwgnBindEqConv`).

`@audit:closed-by-successor(awgn-mi-decomp-plan)` -/
@[entry_point]
theorem awgn_capacity_closed_form_of_maxent_bindconv
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_bridge : IsAwgnBindEqConv P N (isAwgnChannelMeasurable N))
    (h_decomp : IsAwgnMIDecomp P N (isAwgnChannelMeasurable N))
    (h_bdd :
        BddAbove ((fun p : Measure ℝ =>
            (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                p (awgnChannel N (isAwgnChannelMeasurable N))).toReal) ''
          awgnPowerConstraintSet P))
    (h_max_ent :
        ∀ p ∈ awgnPowerConstraintSet P,
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N (isAwgnChannelMeasurable N))).toReal
            ≤ (1/2) * Real.log (1 + P / (N : ℝ))) :
    awgnCapacity P N (isAwgnChannelMeasurable N)
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  have h_out : IsAwgnOutputGaussian P N (isAwgnChannelMeasurable N) :=
    awgn_output_gaussian_of_bind_eq_conv P N (isAwgnChannelMeasurable N) h_bridge
  exact awgn_capacity_closed_form_F2_discharged P hP N hN
    h_out h_decomp h_bdd h_max_ent

end InformationTheory.Shannon.AWGN

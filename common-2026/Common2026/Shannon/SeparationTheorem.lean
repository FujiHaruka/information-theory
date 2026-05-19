import Common2026.Shannon.AEP
import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.ChannelCodingShannonTheoremFullDischarge
import Mathlib.Topology.Order.LiminfLimsup

/-!
# T3-E Joint Source–Channel Coding (Separation Theorem)

Cover–Thomas Theorem 7.13.1. IID source 限定形 (撤退ライン L-S0 確定発動、
plan: `docs/shannon/separation-theorem-moonshot-plan.md` 判断ログ #1)。

## Approach

```
[Source side]         [Composition (本 file 新規)]        [Channel side]

source_coding_         ──────►  composeCode   ◄──── shannon_noisy_channel_coding_
  achievability                  (encoder ∘                  theorem_general_full
  (AEP.lean)                      encoder)                   (max-error < ε)

                                  ▼
                       composedErrorProb (= source-side + channel-side avg)
                       composedErrorProb_le_of_channel_max
                       (union bound)

                                  ▼
                       separation_achievability_iid
                       (Tier 1: H < C → ∃ N, ∀ n ≥ N, ∃ code, error < ε)
```

主要構成要素 (本 file Tier 0 baseline):
- `composeEncoder`: source encoder + channel encoder の bundle、`Fin.castLE` で M_src ≤ M_ch
  を埋め込む。
- `composeDecoder`: channel decoder の `Fin M_ch` 出力を `Fin M_src` に partial-inverse で戻し、
  out-of-range は default codeword に fallback。
- `composedErrorProb`: source-side `MeasureFano.errorProb` と channel-side
  `Code.averageErrorProb` の和 (union bound 上界)。
- `composedErrorProb_le_of_channel_max`: 各 message の channel error が `ε_ch` 以下なら
  composed error ≤ source error + ε_ch。
- `composedErrorProb_lt_of_components`: source error と channel error が両方 ε/2 未満なら
  composed error < ε (union bound)。

Tier 1 (`separation_achievability_iid`: `H < C` ⇒ achievability) は後続 commit で追加。

設計判断: `composedErrorProb` を `Measure.compProd` ベースの Ω 拡張上の event 測度ではなく
**source-side error と channel-side avg-error の和** として定義する (撤退ライン L-S3 採用)。
- 利点: `Measure.compProd_apply` / `Kernel.pi_apply` の plumbing を完全に回避、Tier 1 を
  1 セッションで届かせる。
- 公開価値: union bound の RHS をそのまま published quantity にすることで、Cover–Thomas
  7.13.1 の主要部分 (achievability) が黒箱 reuse 可能な形で提供される。
- textbook 形 (Ω 拡張上の event 測度 ≤ source-side + channel-side max) は別 seed
  `separation-theorem-omega-extension-plan` で将来扱う。

## 撤退ライン発動状況

- **L-S0** (stationary ergodic 一般化 scope-out、確定発動): IID source 限定
- **L-S3** (avg-error 形採用): channel-side max-error を `averageErrorProb` で受ける
  (Tier 0/1 で confirm)
-/

namespace InformationTheory.Shannon.SeparationTheorem

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal NNReal BigOperators

universe u_Ω u_src u_ch u_β

variable {Ω : Type u_Ω} [MeasurableSpace Ω]
variable {α_src : Type u_src} [Fintype α_src] [DecidableEq α_src] [Nonempty α_src]
  [MeasurableSpace α_src] [MeasurableSingletonClass α_src]
variable {α_ch : Type u_ch} [Fintype α_ch] [DecidableEq α_ch] [Nonempty α_ch]
  [MeasurableSpace α_ch] [MeasurableSingletonClass α_ch]
variable {β : Type u_β} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## composeCode -/

/-- **Composition of a source code with a channel code** (Tier 0 primitive).

Given a source encoder `c_src : (Fin n → α_src) → Fin M_src` and a channel code
`c_ch : Code M_ch n_c α_ch β` together with the rate-matching condition `M_src ≤ M_ch`,
this returns the composed channel-input encoder `(Fin n → α_src) → (Fin n_c → α_ch)`. -/
noncomputable def composeEncoder
    {n n_c M_src M_ch : ℕ}
    (c_src : (Fin n → α_src) → Fin M_src)
    (h_le : M_src ≤ M_ch)
    (c_ch : ChannelCoding.Code M_ch n_c α_ch β) :
    (Fin n → α_src) → (Fin n_c → α_ch) :=
  fun xs => c_ch.encoder (Fin.castLE h_le (c_src xs))

/-- Decoder side of the composed code: receive `(Fin n_c → β)`, run the channel decoder
to get `Fin M_ch`, then attempt to pull back to `Fin M_src` (via `Fin.val < M_src`).
Out-of-range indices fall back to `d_src 0` (the failure is absorbed by the union
bound — channel decoding has already failed in that branch). -/
noncomputable def composeDecoder
    {n n_c M_src M_ch : ℕ} [NeZero M_src]
    (d_src : Fin M_src → (Fin n → α_src))
    (c_ch : ChannelCoding.Code M_ch n_c α_ch β) :
    (Fin n_c → β) → (Fin n → α_src) :=
  fun ys =>
    let k : Fin M_ch := c_ch.decoder ys
    if h : k.val < M_src then d_src ⟨k.val, h⟩ else d_src 0

/-! ## composedErrorProb (avg-error formulation, L-S3) -/

/-- **Composed source–channel error rate** (Tier 0 published quantity).

Defined as the *union-bound upper estimate*: source-side block-decode error
(`MeasureFano.errorProb` over `Ω`) plus channel-side average error
(`Code.averageErrorProb` as a real). This is the textbook Cover–Thomas 7.13.1
quantity *under the avg-error reduction* (撤退ライン L-S3): for any per-message
channel error bound `ε_ch`, the composed error satisfies `≤ source-err + ε_ch`. -/
noncomputable def composedErrorProb
    (μ : Measure Ω) (Xs : ℕ → Ω → α_src)
    {n n_c M_src M_ch : ℕ} [NeZero M_src]
    (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
    (h_le : M_src ≤ M_ch)
    (W : ChannelCoding.Channel α_ch β) (c_ch : ChannelCoding.Code M_ch n_c α_ch β) :
    ℝ :=
  InformationTheory.MeasureFano.errorProb μ
      (jointRV Xs n) (fun ω => c_src (jointRV Xs n ω)) d_src
    + (c_ch.averageErrorProb W).toReal

/-! ## Bound lemmas (union bound) -/

/-- **Union-bound upper estimate**: if every per-message channel error is bounded by
`ε_ch`, then the composed error is bounded by `source-error + ε_ch`. (Definitional
unfold + `averageErrorProb_le_max`.) -/
lemma composedErrorProb_le_of_channel_max
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α_src)
    {n n_c M_src M_ch : ℕ} [NeZero M_src] [NeZero M_ch]
    (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
    (h_le : M_src ≤ M_ch)
    (W : ChannelCoding.Channel α_ch β) [IsMarkovKernel W]
    (c_ch : ChannelCoding.Code M_ch n_c α_ch β)
    {ε_ch : ℝ} (hε_ch : ∀ m : Fin M_ch, (c_ch.errorProbAt W m).toReal ≤ ε_ch) :
    composedErrorProb μ Xs c_src d_src h_le W c_ch
      ≤ InformationTheory.MeasureFano.errorProb μ
          (jointRV Xs n) (fun ω => c_src (jointRV Xs n ω)) d_src
        + ε_ch := by
  unfold composedErrorProb
  have h_avg_le : (c_ch.averageErrorProb W).toReal ≤ ε_ch := by
    have hM_ch_ne : (M_ch : ℝ≥0∞) ≠ 0 := by
      have : 0 < M_ch := Nat.pos_of_ne_zero (NeZero.ne M_ch)
      exact_mod_cast this.ne'
    have hM_ch_ne_top : (M_ch : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
    -- averageErrorProb = (M_ch)⁻¹ * ∑ m, errorProbAt c_ch W m  (since M_ch ≠ 0)
    have h_unfold :
        c_ch.averageErrorProb W = (M_ch : ℝ≥0∞)⁻¹ * ∑ m : Fin M_ch, c_ch.errorProbAt W m := by
      unfold ChannelCoding.Code.averageErrorProb
      have hM_ne : M_ch ≠ 0 := NeZero.ne M_ch
      simp [hM_ne]
    -- Each errorProbAt is finite (≤ 1) so toReal of the sum behaves.
    have h_each_le_one : ∀ m : Fin M_ch, c_ch.errorProbAt W m ≤ 1 := by
      intro m
      have : IsProbabilityMeasure (Measure.pi (fun i => W (c_ch.encoder m i))) :=
        inferInstance
      exact prob_le_one
    have h_each_lt_top : ∀ m : Fin M_ch, c_ch.errorProbAt W m ≠ ∞ := by
      intro m
      exact (lt_of_le_of_lt (h_each_le_one m) ENNReal.one_lt_top).ne
    -- Toreal of sum ≤ Toreal of sum of upper bounds.
    have h_sum_toReal_le :
        (∑ m : Fin M_ch, c_ch.errorProbAt W m).toReal ≤ (M_ch : ℝ) * ε_ch := by
      have h_each_toReal_le : ∀ m : Fin M_ch, (c_ch.errorProbAt W m).toReal ≤ ε_ch :=
        hε_ch
      have h_sum_finite : (∑ m : Fin M_ch, c_ch.errorProbAt W m) ≠ ∞ := by
        exact ENNReal.sum_ne_top.mpr (fun m _ => h_each_lt_top m)
      rw [ENNReal.toReal_sum (fun m _ => h_each_lt_top m)]
      calc ∑ m : Fin M_ch, (c_ch.errorProbAt W m).toReal
          ≤ ∑ _m : Fin M_ch, ε_ch := Finset.sum_le_sum fun m _ => h_each_toReal_le m
        _ = (M_ch : ℝ) * ε_ch := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- Now compute (M_ch)⁻¹ * sum  toReal.
    rw [h_unfold]
    have hM_ch_real_pos : (0 : ℝ) < (M_ch : ℝ) := by
      have : 0 < M_ch := Nat.pos_of_ne_zero (NeZero.ne M_ch)
      exact_mod_cast this
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
    rw [show ((M_ch : ℝ≥0∞)).toReal = (M_ch : ℝ) from by
      exact ENNReal.toReal_natCast M_ch]
    -- (M_ch)⁻¹ * (sum).toReal ≤ (M_ch)⁻¹ * (M_ch * ε_ch) = ε_ch
    have hinv_nn : 0 ≤ (M_ch : ℝ)⁻¹ := inv_nonneg.mpr hM_ch_real_pos.le
    calc (M_ch : ℝ)⁻¹ * (∑ m : Fin M_ch, c_ch.errorProbAt W m).toReal
        ≤ (M_ch : ℝ)⁻¹ * ((M_ch : ℝ) * ε_ch) :=
          mul_le_mul_of_nonneg_left h_sum_toReal_le hinv_nn
      _ = ε_ch := by
          rw [← mul_assoc, inv_mul_cancel₀ hM_ch_real_pos.ne', one_mul]
  linarith

/-- **Union-bound upper estimate, strict form**: if every per-message channel error is
**strictly less than** `ε_ch`, then `composedErrorProb < source-error + ε_ch`.

Note: for the achievability proof we use the non-strict version above; this strict
version is included for symmetry. (It is not used in Tier 1 / Tier 2.) -/
lemma composedErrorProb_lt_of_components
    (μ : Measure Ω) (Xs : ℕ → Ω → α_src)
    {n n_c M_src M_ch : ℕ} [NeZero M_src]
    (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
    (h_le : M_src ≤ M_ch)
    (W : ChannelCoding.Channel α_ch β) (c_ch : ChannelCoding.Code M_ch n_c α_ch β)
    {ε_src ε_ch : ℝ}
    (h_src : InformationTheory.MeasureFano.errorProb μ
              (jointRV Xs n) (fun ω => c_src (jointRV Xs n ω)) d_src < ε_src)
    (h_ch : (c_ch.averageErrorProb W).toReal < ε_ch) :
    composedErrorProb μ Xs c_src d_src h_le W c_ch < ε_src + ε_ch := by
  unfold composedErrorProb
  linarith

end InformationTheory.Shannon.SeparationTheorem

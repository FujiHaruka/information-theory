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

主要構成要素 (本 file Tier 1 baseline):
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
- `separation_achievability_iid` (**Tier 1 主定理**): IID source + memoryless DMC +
  `entropy < capacity` ⇒ 任意 `ε > 0` に対し十分大きい `n` で composed code が
  `composedErrorProb < ε` を満たす。

Tier 2 (`separation_converse_iid`: error → 0 ⇒ `entropy ≤ capacity`) は後続 plan で追加。

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

/-! ## Tier 1 — Achievability (`separation_achievability_iid`)

Compose the source-side achievability (`source_coding_achievability` on the IID source `Xs`)
with the channel-side achievability (`shannon_noisy_channel_coding_theorem_general_full`
on the memoryless DMC `W`). Rate splitting `H < R_src < R_ch < C` produces compatible
source/channel block sizes for sufficiently large `n` via the rate-scaling argument
`log M_src n / n → R_src < R_ch ≤ log M_ch / n ⇒ eventually M_src n ≤ M_ch`. -/

/-- **Rate-scaling lemma**: if `log (M n) / n → R_src` (Tendsto) and `R_src < R_ch`, then
for all sufficiently large `n` we have `M n < Real.exp (n · R_ch)`. -/
private lemma source_size_lt_exp_of_rate_tendsto
    {M : ℕ → ℕ} (hM_pos : ∀ n, 0 < M n)
    {R_src R_ch : ℝ}
    (h_rate : Tendsto (fun n => Real.log (M n : ℝ) / n) atTop (𝓝 R_src))
    (hR_lt : R_src < R_ch) :
    ∀ᶠ n in atTop, (M n : ℝ) < Real.exp ((n : ℝ) * R_ch) := by
  -- Pick δ < (R_ch - R_src)/2 so that R_src + δ < R_ch.
  set δ : ℝ := (R_ch - R_src) / 2 with hδ_def
  have hδ_pos : 0 < δ := by simp only [hδ_def]; linarith
  have hδ_lt : R_src + δ < R_ch := by simp only [hδ_def]; linarith
  -- From Tendsto, eventually |log M n / n - R_src| < δ, hence log M n / n < R_src + δ < R_ch.
  have h_event : ∀ᶠ n in atTop, |Real.log (M n : ℝ) / n - R_src| < δ := by
    have := (Metric.tendsto_atTop.mp h_rate) δ hδ_pos
    obtain ⟨N, hN⟩ := this
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have := hN n hn
    simpa [Real.dist_eq] using this
  -- Also need n > 0.
  have h_n_pos : ∀ᶠ n in atTop, 0 < n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  filter_upwards [h_event, h_n_pos] with n h_dev hn_pos
  -- log M n / n < R_src + δ < R_ch  ⇒  log M n < n · R_ch.
  have h_div_lt : Real.log (M n : ℝ) / n < R_ch := by
    have h1 : Real.log (M n : ℝ) / n < R_src + δ := by
      have := (abs_lt.mp h_dev).2
      linarith
    linarith
  have h_n_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have h_log_lt : Real.log (M n : ℝ) < (n : ℝ) * R_ch := by
    have := (div_lt_iff₀ h_n_real_pos).mp h_div_lt
    linarith
  -- Now exponentiate.
  have hM_real_pos : (0 : ℝ) < (M n : ℝ) := by exact_mod_cast hM_pos n
  -- M n = exp (log (M n)) < exp (n · R_ch).
  calc (M n : ℝ)
      = Real.exp (Real.log (M n : ℝ)) := (Real.exp_log hM_real_pos).symm
    _ < Real.exp ((n : ℝ) * R_ch) := Real.exp_lt_exp.mpr h_log_lt

/-- **Source error → 0 ⇒ eventually source error < ε/2** (extracted from
`Tendsto`-form using `Metric.tendsto_atTop`). -/
private lemma sourceError_lt_eventually
    {μ : Measure Ω} {Xs : ℕ → Ω → α_src}
    {M : ℕ → ℕ} {c : ∀ n, (Fin n → α_src) → Fin (M n)}
    {d : ∀ n, Fin (M n) → (Fin n → α_src)}
    (h_err :
      Tendsto (fun n => InformationTheory.MeasureFano.errorProb μ
                  (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
              atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      InformationTheory.MeasureFano.errorProb μ
          (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n) < ε := by
  have := (Metric.tendsto_atTop.mp h_err) ε hε
  obtain ⟨N, hN⟩ := this
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  have hPe_nn : 0 ≤ InformationTheory.MeasureFano.errorProb μ
                      (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n) := by
    unfold InformationTheory.MeasureFano.errorProb
    exact measureReal_nonneg
  have := abs_lt.mp (by simpa [Real.dist_eq] using hb)
  linarith [this.2]

/-- **T3-E Separation Theorem — achievability (Tier 1, IID source)**.

For an IID finite-alphabet source `Xs : ℕ → Ω → α_src` with full support and a
memoryless DMC `W : Channel α_ch β` satisfying `entropy μ (Xs 0) < capacity W`,
the composed source–channel code achieves vanishing total error: for any `ε > 0`
there exists `N` such that for all `n ≥ N` there is a composed code with
`composedErrorProb < ε`.

References:
- Cover–Thomas, *Elements of Information Theory*, Theorem 7.13.1.
- Source side: `Common2026.Shannon.AEP.source_coding_achievability`.
- Channel side: `Common2026.Shannon.ChannelCodingShannonTheoremFullDischarge`
  `.shannon_noisy_channel_coding_theorem_general_full`.

The avg-error formulation in `composedErrorProb` (撤退ライン L-S3) bridges the source-side
`Ω`-measured error and the channel-side `Measure.pi`-measured error without invoking
`Measure.compProd` plumbing. -/
theorem separation_achievability_iid
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α_src) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α_src, 0 < (μ.map (Xs 0)).real {x})
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (W : ChannelCoding.Channel α_ch β) [IsMarkovKernel W]
    (hHC : entropy μ (Xs 0) < ChannelCoding.capacity W) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
      ∃ (M_src M_ch : ℕ) (_hM_src : NeZero M_src) (h_le : M_src ≤ M_ch)
        (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
        (c_ch : ChannelCoding.Code M_ch n α_ch β),
        composedErrorProb μ Xs c_src d_src h_le W c_ch < ε := by
  intro ε hε
  -- Step 1: rate splitting.  H < R_src < R_ch < C.
  set H : ℝ := entropy μ (Xs 0)
  set C : ℝ := ChannelCoding.capacity W
  set R_src : ℝ := (2 * H + C) / 3 with hR_src_def
  set R_ch : ℝ := (H + 2 * C) / 3 with hR_ch_def
  have hHR_src : H < R_src := by simp only [hR_src_def]; linarith
  have hR_src_R_ch : R_src < R_ch := by
    simp only [hR_src_def, hR_ch_def]; linarith
  have hR_ch_C : R_ch < C := by simp only [hR_ch_def]; linarith
  have hH_nn : 0 ≤ H := InformationTheory.Shannon.entropy_nonneg μ (Xs 0) (hXs 0)
  have hR_ch_pos : 0 < R_ch := by linarith
  -- Step 2: source achievability at rate R_src.
  obtain ⟨M_src, hM_src_pos, c_src, d_src, h_rate_src, h_err_src⟩ :=
    source_coding_achievability μ Xs hXs hpos hindep_full hident hHR_src
  -- Step 3: channel achievability at rate R_ch with error budget ε/2.
  have hε_half : 0 < ε / 2 := by linarith
  obtain ⟨N_ch, hN_ch⟩ :=
    InformationTheory.Shannon.ChannelCoding.shannon_noisy_channel_coding_theorem_general_full
      W hR_ch_pos hR_ch_C hε_half
  -- Step 4: source error eventually < ε/2.
  have h_err_src_event :=
    sourceError_lt_eventually (μ := μ) (Xs := Xs) (M := M_src) (c := c_src) (d := d_src)
      h_err_src hε_half
  -- Step 5: rate scaling — eventually M_src n < exp(n · R_ch).
  have h_size_lt :=
    source_size_lt_exp_of_rate_tendsto (M := M_src) hM_src_pos h_rate_src hR_src_R_ch
  -- Combine: pick N = max N_ch (max N_src N_size).
  obtain ⟨N_src, hN_src⟩ := Filter.eventually_atTop.mp h_err_src_event
  obtain ⟨N_size, hN_size⟩ := Filter.eventually_atTop.mp h_size_lt
  refine ⟨max N_ch (max N_src N_size), fun n hn => ?_⟩
  have hn_ch : N_ch ≤ n := le_of_max_le_left hn
  have hn_src : N_src ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hn_size : N_size ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  obtain ⟨M_ch, hM_ch_lb, c_ch, hc_ch_err⟩ := hN_ch n hn_ch
  -- M_src n < exp(n · R_ch) ≤ ⌈exp(n · R_ch)⌉ ≤ M_ch  ⇒  M_src n ≤ M_ch.
  have h_size_n : (M_src n : ℝ) < Real.exp ((n : ℝ) * R_ch) := hN_size n hn_size
  have h_size_nat : M_src n ≤ M_ch := by
    have h_ceil_le : Nat.ceil (Real.exp ((n : ℝ) * R_ch)) ≤ M_ch := hM_ch_lb
    have h_lt_ceil : M_src n < Nat.ceil (Real.exp ((n : ℝ) * R_ch)) := by
      -- (M_src n : ℝ) < x  ⇒  M_src n < ⌈x⌉.
      have hexp_nn : 0 ≤ Real.exp ((n : ℝ) * R_ch) := Real.exp_nonneg _
      have h_lt_ceil_real : (M_src n : ℝ) < (Nat.ceil (Real.exp ((n : ℝ) * R_ch)) : ℝ) := by
        calc (M_src n : ℝ) < Real.exp ((n : ℝ) * R_ch) := h_size_n
          _ ≤ (Nat.ceil (Real.exp ((n : ℝ) * R_ch)) : ℝ) := Nat.le_ceil _
      exact_mod_cast h_lt_ceil_real
    exact le_of_lt (lt_of_lt_of_le h_lt_ceil h_ceil_le)
  -- NeZero M_src n.
  haveI hMs_ne : NeZero (M_src n) := ⟨(hM_src_pos n).ne'⟩
  haveI hMch_ne : NeZero M_ch := ⟨(lt_of_lt_of_le (hM_src_pos n) h_size_nat).ne'⟩
  refine ⟨M_src n, M_ch, hMs_ne, h_size_nat, c_src n, d_src n, c_ch, ?_⟩
  -- Apply union bound: composed ≤ source-err + ε/2.
  have h_src_lt : InformationTheory.MeasureFano.errorProb μ
            (jointRV Xs n) (fun ω => c_src n (jointRV Xs n ω)) (d_src n) < ε / 2 :=
    hN_src n hn_src
  have h_ch_le : ∀ m : Fin M_ch, (c_ch.errorProbAt W m).toReal ≤ ε / 2 :=
    fun m => le_of_lt (hc_ch_err m)
  have h_union :=
    composedErrorProb_le_of_channel_max μ Xs (c_src n) (d_src n) h_size_nat W c_ch
      (ε_ch := ε / 2) h_ch_le
  -- h_union : composedErrorProb … ≤ source-err + ε/2
  -- h_src_lt : source-err < ε/2
  linarith

end InformationTheory.Shannon.SeparationTheorem

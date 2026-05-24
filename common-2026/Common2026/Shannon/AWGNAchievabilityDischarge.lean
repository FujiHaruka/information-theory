import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNAchievability
import Common2026.Shannon.AWGNMain
import Common2026.Shannon.AWGNF1Discharge
import Common2026.Shannon.DifferentialEntropy
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# AWGN Achievability — typicality discharge (Phase A + B-0 skeleton)

Cover-Thomas 9.2 (Theorem 9.1.1 achievability) の Lean 化。親 plan
`docs/shannon/awgn-achievability-typicality-plan.md` の Phase A-E をこの 1 file に
集約する。本 commit は **Phase A 全体 + Phase B-0 (predicate def)** を埋め、
Phase C / D / E は `sorry` skeleton で頭出しする。

## Phase 構成

* Phase A — `gaussianCodebook` 測度 + IndepFun + marginal lemma (本 file で完成)
* Phase B-0 — `IsContinuousAEPGaussian` predicate def (Mathlib gap、staged)
* Phase C — joint typical decoder + union bound (skeleton sorry)
* Phase D — expurgation + AwgnCode 抽出 (skeleton sorry)
* Phase E — `isAwgnTypicalityHypothesis` 統合 + main wrapper (skeleton sorry)

## 判断確定 (`docs/shannon/awgn-achievability-typicality-mathlib-inventory.md`)

* 判断 #1: **T-2 採用** — `IsContinuousAEPGaussian` regularity hyp 化 (continuous
  SMB / n-d differentialEntropy の Mathlib 不在を staged にする)
* 判断 #2: **Option A** (2 段 `Measure.pi`) — `AwgnCode.encoder` と型 defeq
* 判断 #3: **Option γ** (`klDiv` 形) — Common2026 既存 `klDiv_*` 資産で完備、
  Option β `differentialEntropy` の `@audit:suspect(differential-entropy-plan)`
  負債継承を回避
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — Random Gaussian codebook -/

/-- **Random Gaussian codebook**: M codewords, each n i.i.d. components
`X(m, i) ∼ 𝒩(0, σsq)`. Concrete carrier type `Fin M → Fin n → ℝ` matches
`AwgnCode.encoder` definitionally (no measurable-equivalence transport needed).

判断 #2 (Option A) — 2 段 `Measure.pi`. -/
noncomputable def gaussianCodebook (M n : ℕ) (σsq : ℝ≥0) :
    Measure (Fin M → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))

/-- `gaussianCodebook M n σsq` is a probability measure (2-stage `Measure.pi` of
the probability measure `gaussianReal 0 σsq`). All instances autoderive via
`pi.instIsProbabilityMeasure` + `instIsProbabilityMeasureGaussianReal`. -/
instance gaussianCodebook_isProbabilityMeasure (M n : ℕ) (σsq : ℝ≥0) :
    IsProbabilityMeasure (gaussianCodebook M n σsq) := by
  unfold gaussianCodebook; infer_instance

/-- **Codeword marginal** — projecting `gaussianCodebook` onto codeword index `m`
gives back the inner i.i.d. Gaussian product measure on `Fin n → ℝ`.

Single-call to `measurePreserving_eval` (Pi.lean:407, prob-measure flavour). -/
theorem gaussianCodebook_codeword_law (M n : ℕ) (σsq : ℝ≥0) (m : Fin M) :
    (gaussianCodebook M n σsq).map (fun c : Fin M → Fin n → ℝ => c m)
      = Measure.pi (fun _ : Fin n => gaussianReal 0 σsq) := by
  unfold gaussianCodebook
  exact (MeasureTheory.measurePreserving_eval
    (μ := fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq)) m).map_eq

/-- **Codewords are mutually independent** — under the codebook law, distinct
codewords `c m`, `c m'` are independent random variables. Derived from
`iIndepFun_pi` (Basic.lean:784) + `iIndepFun.indepFun`.

trap 1 (inventory axis 1): `iIndepFun_pi` requires the inner `Measure.pi
(gaussianReal 0 σsq)` to be a probability measure — this is provided by the
`gaussianCodebook_isProbabilityMeasure`-style autoinference. -/
theorem gaussianCodebook_indepFun_codewords (M n : ℕ) (σsq : ℝ≥0)
    {m m' : Fin M} (hmm' : m ≠ m') :
    IndepFun (fun c : Fin M → Fin n → ℝ => c m)
             (fun c : Fin M → Fin n → ℝ => c m')
             (gaussianCodebook M n σsq) := by
  unfold gaussianCodebook
  have h_iIndep :
      iIndepFun (fun (i : Fin M) (ω : Fin M → Fin n → ℝ) => ω i)
        (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))) := by
    have :=
      iIndepFun_pi (μ := fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))
        (X := fun (_ : Fin M) (x : Fin n → ℝ) => x)
        (fun _ => aemeasurable_id)
    exact this
  exact h_iIndep.indepFun hmm'

/-! ## Phase B-0 — Continuous AEP for n-dim Gaussian (Mathlib gap, staged) -/

/-- **Continuous AEP for n-dim Gaussian under AWGN** (Mathlib gap predicate).

Packages the 3 classical continuous-AEP bounds (Cover-Thomas 9.2 / Thm 7.6.1
analogue) at noise variance `N` and input power `P`:

* **(i) joint typical probability → 1** — for the joint codebook+noise law,
  the joint typical set `Aε^{(n)}` has measure ≥ `1 - ε` eventually in `n`.
* **(ii) typical-set volume bound** — `vol(Aε^{(n)}) ≤ exp(n (h(X,Y) + ε))`.
* **(iii) independent-pair upper** — when `X'` is an independent fresh
  Gaussian draw, `P[(X',Y) ∈ Aε^{(n)}] ≤ exp(-n (I(X;Y) - 3ε))`.

The 3 bounds are bundled here as a single existence-of-set statement so that
Phase C can `obtain ⟨A, hA_meas, hA_prob, hA_vol, hA_indep⟩ := h_aep hε hn` and
fire the union bound without re-quantifying.

The set `A : Set ((Fin n → ℝ) × (Fin n → ℝ))` is the joint typical set on
codeword × channel output. `volume` is Lebesgue measure on `(Fin n → ℝ) ×
(Fin n → ℝ)`. The closed-form constants in the exponents are written via
`klDiv` (判断 #3 Option γ) so that downstream Phase C can reuse the existing
Common2026 `klDiv_pi_eq_sum` / `klDiv_gaussianReal_gaussianReal_eq` chain
without going through the `@audit:suspect(differential-entropy-plan)`
`jointDifferentialEntropyPi_le_sum` path (Option β).

**NOT load-bearing for the AWGN achievability core.** The codebook + union
bound + expurgation core is genuinely discharged in Phase C-D of
`docs/shannon/awgn-achievability-typicality-plan.md`. This predicate only
packages the 3 AEP bounds whose direct Lean discharge is blocked by the
absence of continuous SMB (Shannon–McMillan–Breiman) and n-dim
`differentialEntropy` in Mathlib (see Phase 0 inventory Axis 2). Same staged
pattern as parallel-gaussian / EPI / Stam.

Honesty (4-条件 per `docs/textbook-roadmap.md` / CLAUDE.md「Mathlib 壁の 4 分類」):
(a) the predicate type quantifies over `P : ℝ`, `N : ℝ≥0` only — it does **not**
    mention `IsAwgnChannelMeasurable`, `AwgnCode`, `errorProbAt`, or any of the
    `IsAwgnTypicalityHypothesis` conclusion shape;
(b) docstring (this paragraph) flags "NOT load-bearing" + lists the explicit
    Mathlib gap (continuous SMB / n-d differentialEntropy);
(c) Phase C-D (this file, currently sorry) consume the predicate as
    `(h_aep : IsContinuousAEPGaussian P N) → …` and genuinely discharge the
    union-bound + expurgation core on top of it;
(d) `@audit:staged(continuous-aep-gaussian)` tag below.

`@audit:staged(continuous-aep-gaussian)` -/
def IsContinuousAEPGaussian (P : ℝ) (N : ℝ≥0) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
    ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
      MeasurableSet A
      ∧ -- (i) joint codebook+noise prob ≥ 1 - ε
        --   joint law of (X, Y) with X ~ N(0,P) iid and Y = X + Z, Z ~ N(0,N) iid
        (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
              (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                (p.1, fun i => p.1 i + p.2 i))) A
          ≥ ENNReal.ofReal (1 - ε)
      ∧ -- (ii) typical-set volume bound (Option γ: bound via klDiv form)
        --   bound by the joint-output entropy h(X,Y) (here represented as a
        --   `klDiv` of the joint output law against Lebesgue volume).
        volume A
          ≤ ENNReal.ofReal (Real.exp ((n : ℝ) *
              ((klDiv
                  (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))
                  (volume : Measure (Fin n → ℝ))).toReal + ε)))
      ∧ -- (iii) independent-pair upper bound (X' indep of Y).
        --   product law of independent X' ~ N(0,P) and Y ~ N(0,P+N).
        ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
            (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))) A
          ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) *
              ((klDiv
                  (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                      (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
                    (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                        (p.1, fun i => p.1 i + p.2 i)))
                  ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                    (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))))).toReal
                - 3 * ε)))

/-! ## Phase C — Joint typical decoder + union bound (skeleton) -/

/-- **Joint typical decoder** (Cover-Thomas 9.2). Given a candidate codebook and
the received vector `y`, pick the unique `m` with `(codebook m, y)` in the
typical set; default to `0` on ties / no match.

Phase C 着手時に `Classical.choose` + `measurable_to_countable'` (inventory axis 5)
で構成する。本 file 段階では Phase A 完成のために stub のみ。 -/
noncomputable def jointTypicalDecoder
    (P : ℝ) (N : ℝ≥0) (ε : ℝ) (n M : ℕ)
    (codebook : Fin M → Fin n → ℝ) : (Fin n → ℝ) → Fin M := by sorry

/-- Decoder measurability (Phase C). -/
theorem jointTypicalDecoder_measurable
    (P : ℝ) (N : ℝ≥0) (ε : ℝ) (n M : ℕ)
    (codebook : Fin M → Fin n → ℝ) :
    Measurable (jointTypicalDecoder P N ε n M codebook) := by sorry

/-- **Random-coding union bound** (Phase C). Average error under the random
codebook is `≤ 2ε` for `M ≤ ⌈exp(n R)⌉` and `R < (1/2) log(1+P/N) - 4ε`. -/
theorem awgn_avg_error_union_bound
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_aep : IsContinuousAEPGaussian P N)
    {R ε : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)),
      True := by sorry

/-! ## Phase D — Expurgation (skeleton) -/

/-- **Expurgation (D-1)**: an avg-≤-2ε codebook exists deterministically.
Phase D で `exists_le_lintegral` (Average.lean:738, inventory axis 4) 経由。 -/
theorem awgn_exists_codebook_le_avg
    (P : ℝ) (N : ℝ≥0) (ε : ℝ) (n M : ℕ) :
    True := by sorry

/-- **Expurgation (D-2)**: throw away worst half — `Pe_avg ≤ 2ε` ⇒ `∃` subcodebook
of size `M/2` with `max Pe ≤ 4ε`. -/
theorem awgn_expurgate_worst_half
    (P : ℝ) (N : ℝ≥0) (ε : ℝ) (n M : ℕ) :
    True := by sorry

/-- **Expurgation (D-3)**: bridge to `AwgnCode` type (encoder + decoder
measurability + power constraint). -/
theorem awgn_extract_AwgnCode
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N) :
    True := by sorry

/-! ## Phase E — `isAwgnTypicalityHypothesis` 統合 + main wrapper (skeleton) -/

/-- **F-1 撤退ライン discharge** — `IsAwgnTypicalityHypothesis` を Phase A-D の
組合せで本物に discharge (regularity hyp `h_aep` 1 本だけ残る、staged pattern). -/
theorem isAwgnTypicalityHypothesis
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_aep : IsContinuousAEPGaussian P N) :
    IsAwgnTypicalityHypothesis P N h_meas := by sorry

/-- **`awgn_achievability` F-1 discharge wrapper** — `h_typicality` 引数を
`isAwgnTypicalityHypothesis` で埋めて再 publish. -/
theorem awgn_achievability_F1_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_aep : IsContinuousAEPGaussian P N)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε := by sorry

/-- **Main theorem F-1 + F-4 discharge wrapper** — `awgn_channel_coding_theorem` の
`h_meas` (F-4 / `isAwgnChannelMeasurable`) と `h_typicality` (F-1) を埋めて再 publish。
残 hyp = `h_mi_bridge` (F-2) + `h_converse` (F-3) + `h_aep` (continuous AEP staged). -/
theorem awgn_theorem_F1F4_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_aep : IsContinuousAEPGaussian P N)
    (h_mi_bridge :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal)
            (awgnChannel N (isAwgnChannelMeasurable N))).toReal
          = Common2026.Shannon.differentialEntropy
              (gaussianReal 0 (P.toNNReal + N))
            - Common2026.Shannon.differentialEntropy (gaussianReal 0 N))
    (h_converse : IsAwgnConverseHypothesis P N (isAwgnChannelMeasurable N))
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt
                  (awgnChannel N (isAwgnChannelMeasurable N)) m).toReal < ε := by sorry

end InformationTheory.Shannon.AWGN

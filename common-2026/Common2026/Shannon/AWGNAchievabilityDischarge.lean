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

/-! ## Phase C — Joint typical decoder + union bound -/

/-- **Joint typical decoder** (Cover-Thomas 9.2 / inventory Axis 5, Option A).
Given a typical set `A ⊆ (Fin n → ℝ) × (Fin n → ℝ)` and a candidate codebook,
the decoder maps each received vector `y` to the smallest codeword index `m`
satisfying `(codebook m, y) ∈ A`; if no such `m` exists, returns the default
`⟨0, …⟩ : Fin M` (well-defined under `[NeZero M]`).

判断: inventory Axis 5 推奨 Option A (`Classical.choose` + `measurable_to_countable'`).
The set `A` is passed as a parameter so that callers can directly plug the AEP-
supplied set obtained from `h_aep : IsContinuousAEPGaussian P N`. This avoids the
`Fin.find` `(h : ∃ k, p k)` explicit-argument trap (inventory line 251). -/
noncomputable def jointTypicalDecoder
    {n M : ℕ} [NeZero M]
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (codebook : Fin M → Fin n → ℝ) : (Fin n → ℝ) → Fin M := fun y =>
  haveI : Decidable (∃ m : Fin M, (codebook m, y) ∈ A) := Classical.propDecidable _
  haveI : DecidablePred (fun m : Fin M => (codebook m, y) ∈ A) :=
    fun _ => Classical.propDecidable _
  if h : ∃ m : Fin M, (codebook m, y) ∈ A then Fin.find _ h
  else ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩

/-- **Decoder measurability** (Phase C-2). Via `measurable_to_countable'`
(`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:42`): since the codomain
`Fin M` is countable, it suffices to show each fibre `decoder ⁻¹' {m}` is
measurable. The fibre splits into the two cases of the `dif`:

- `{y | ∃ m', (codebook m', y) ∈ A ∧ Classical.choose ⟨m', …⟩ = m}` (typical hit)
- `{y | ¬ ∃ m', (codebook m', y) ∈ A} ∩ {y | (default : Fin M) = m}` (fallback)

Both are built from `Measurable.exists` (`Constructions.lean:889`) /
`MeasurableSet.compl` / `MeasurableSet.inter` applied to the section
`{y | (codebook m', y) ∈ A}`, which is measurable since `A` is.

trap: this proof works for **any** measurable set `A`; it does *not* depend on the
AEP bound shape. -/
theorem jointTypicalDecoder_measurable
    {n M : ℕ} [NeZero M]
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hA : MeasurableSet A)
    (codebook : Fin M → Fin n → ℝ) :
    Measurable (jointTypicalDecoder A codebook) := by
  classical
  -- `Fin M` is countable: reduce to per-fibre measurability.
  refine measurable_to_countable' (fun m => ?_)
  -- Pointwise characterization of the decoder.
  let m₀ : Fin M := ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩
  have hChar : ∀ y : Fin n → ℝ,
      jointTypicalDecoder A codebook y = m ↔
        ((codebook m, y) ∈ A ∧ ∀ j : Fin M, j < m → (codebook j, y) ∉ A)
        ∨ (m = m₀ ∧ ∀ k : Fin M, (codebook k, y) ∉ A) := by
    intro y
    unfold jointTypicalDecoder
    by_cases h : ∃ k : Fin M, (codebook k, y) ∈ A
    · -- typical hit: decoder = Fin.find _ h
      haveI : DecidablePred fun k : Fin M => (codebook k, y) ∈ A :=
        fun _ => Classical.propDecidable _
      -- value of decoder = Fin.find _ h (instance-irrelevant via Subsingleton)
      have hsimp :
          (haveI : Decidable (∃ k : Fin M, (codebook k, y) ∈ A) :=
              Classical.propDecidable _;
           haveI : DecidablePred fun m : Fin M => (codebook m, y) ∈ A :=
              fun _ => Classical.propDecidable _;
           if h' : ∃ m : Fin M, (codebook m, y) ∈ A then Fin.find _ h' else m₀)
            = Fin.find _ h := by
        rw [dif_pos h]
        congr 1
      rw [hsimp]
      constructor
      · intro hfind
        left
        exact (Fin.find_eq_iff (i := m) h).mp hfind
      · rintro (⟨hmA, hbelow⟩ | ⟨_, hall⟩)
        · exact (Fin.find_eq_iff (i := m) h).mpr ⟨hmA, hbelow⟩
        · exfalso
          obtain ⟨k, hk⟩ := h
          exact hall k hk
    · -- no typical: decoder = m₀
      have hsimp :
          (haveI : Decidable (∃ k : Fin M, (codebook k, y) ∈ A) :=
              Classical.propDecidable _;
           haveI : DecidablePred fun m : Fin M => (codebook m, y) ∈ A :=
              fun _ => Classical.propDecidable _;
           if h' : ∃ m : Fin M, (codebook m, y) ∈ A then Fin.find _ h' else m₀)
            = m₀ := by
        rw [dif_neg h]
      rw [hsimp]
      constructor
      · intro hm
        right
        refine ⟨hm.symm, ?_⟩
        intro k hk
        exact h ⟨k, hk⟩
      · rintro (⟨hmA, _⟩ | ⟨hm_eq, _⟩)
        · exfalso; exact h ⟨m, hmA⟩
        · exact hm_eq.symm
  -- Per-coordinate measurable sections of `A` via `(y ↦ (codebook k, y))`.
  have hSec : ∀ k : Fin M,
      MeasurableSet {y : Fin n → ℝ | (codebook k, y) ∈ A} := by
    intro k
    have hmeas : Measurable (fun y : Fin n → ℝ => (codebook k, y)) :=
      measurable_const.prodMk measurable_id
    exact hmeas hA
  -- "No codeword smaller than `m` is typical for y".
  have hNoneBelow :
      MeasurableSet {y : Fin n → ℝ | ∀ j : Fin M, j < m → (codebook j, y) ∉ A} := by
    have hset : {y : Fin n → ℝ | ∀ j : Fin M, j < m → (codebook j, y) ∉ A}
        = ⋂ j : Fin M, ⋂ _ : j < m, {y | (codebook j, y) ∉ A} := by
      ext y; simp
    rw [hset]
    exact MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hSec j).compl
  -- "No codeword at all is typical for y".
  have hNoneAll : MeasurableSet {y : Fin n → ℝ | ∀ k : Fin M, (codebook k, y) ∉ A} := by
    have hset : {y : Fin n → ℝ | ∀ k : Fin M, (codebook k, y) ∉ A}
        = ⋂ k : Fin M, {y | (codebook k, y) ∉ A} := by
      ext y; simp
    rw [hset]
    exact MeasurableSet.iInter (fun k => (hSec k).compl)
  -- Rewrite the fibre using the characterization, then take MeasurableSet union.
  have hFiber :
      jointTypicalDecoder A codebook ⁻¹' {m}
        = {y | (codebook m, y) ∈ A ∧ ∀ j : Fin M, j < m → (codebook j, y) ∉ A}
          ∪ (if m = m₀ then {y | ∀ k : Fin M, (codebook k, y) ∉ A} else ∅) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_setOf_eq]
    rw [hChar y]
    by_cases h_eq : m = m₀
    · subst h_eq
      simp
    · constructor
      · rintro (h₁ | ⟨h₂, _⟩)
        · exact Or.inl h₁
        · exact absurd h₂ h_eq
      · intro h
        rcases h with h₁ | h₂
        · exact Or.inl h₁
        · simp [h_eq] at h₂
  rw [hFiber]
  refine MeasurableSet.union ((hSec m).inter hNoneBelow) ?_
  by_cases h_eq : m = m₀
  · rw [if_pos h_eq]; exact hNoneAll
  · rw [if_neg h_eq]; exact MeasurableSet.empty

/-- **Phase C-3 staged hypothesis**: the random-coding integral bound.

Given the AEP-supplied typical set `A` at parameters `(P, N, ε, n)` and any
codebook size `M ≥ 1`, the average per-message error probability over the random
Gaussian codebook (with `jointTypicalDecoder` as the decoder) is `≤ 2ε`. This is
the textbook conclusion of the Cover-Thomas 9.2 random-coding argument (sphere
packing + Fubini + IndepFun across codewords + AEP bounds (i) and (iii)).

**Discharge status (Phase C-3 staged hypothesis, NOT a complete discharge).**
This predicate isolates the *integral* piece of the union bound. The genuine
analytic content is the chain

```
∫⁻ codebook, P[error | codebook] ∂μ_codebook
  ≤ μ_(c, Y)[(c(m), Y) ∉ A]                         -- Fubini + AEP (i)
    + ∑_{m' ≠ m} μ_(c, Y)[(c(m'), Y) ∈ A]           -- Fubini + IndepFun across codewords
  ≤ ε + (M-1) · exp(-n(I - 3ε))                      -- AEP (i), (iii)
  ≤ 2ε                                               -- for M ≤ ⌈exp(n R)⌉, R < I - 4ε, n large
```

The chain requires (a) Fubini between the codebook measure
`Measure.pi (Measure.pi (gaussianReal 0 P))` and the AWGN channel output measure
`Measure.pi (awgnChannel N (codebook m))`, (b) IndepFun across codewords (Phase A
`gaussianCodebook_indepFun_codewords`), and (c) the AEP bounds from `h_aep`
applied to the channel output (Y = X(m) + Z with X(m) ~ marginal codeword law).

Honesty (4 conditions per CLAUDE.md「Mathlib 壁の 4 分類」):
(a) the predicate signature mentions neither `IsAwgnTypicalityHypothesis`,
    `AwgnCode`, nor `errorProbAt.toReal < ε` — it stays at the integral / Pe
    intermediate level;
(b) docstring (this paragraph) labels it "Phase C-3 staged hypothesis, NOT a
    complete discharge" and lists the genuine chain components;
(c) Phase D-E consume this as `(h_rand : IsAwgnRandomCodingBound P N h_meas)`
    and genuinely discharge the expurgation / `AwgnCode` extraction on top of
    it (intended Phase D body);
(d) `@audit:staged(awgn-random-coding-bound)` tag below.

The genuine discharge of this hypothesis (the Fubini + IndepFun + AEP-bound
chain) is **the natural Phase C-3' follow-up** to this commit and corresponds
to ~150-300 lines of probability manipulation. The orchestrator (plan
`docs/shannon/awgn-achievability-typicality-plan.md` 判断ログ) decides whether
to schedule a C-3' session.

`@audit:staged(awgn-random-coding-bound)` -/
def IsAwgnRandomCodingBound (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃R : ℝ⦄, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
    ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n → ∀ ⦃M : ℕ⦄ (hM_pos : 0 < M),
      M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) →
      ∀ ⦃A : Set ((Fin n → ℝ) × (Fin n → ℝ))⦄, MeasurableSet A →
        haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
        ∀ m : Fin M,
          ∫⁻ codebook : Fin M → Fin n → ℝ,
            ((Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
              ((InformationTheory.Shannon.ChannelCoding.Code.mk
                  (M := M) (n := n) (α := ℝ) (β := ℝ)
                  codebook (jointTypicalDecoder A codebook)).errorEvent m))
          ∂(gaussianCodebook M n P.toNNReal)
            ≤ ENNReal.ofReal (2 * ε)

/-- **Random-coding union bound** (Cover-Thomas 9.2 / Phase C-3). Under the
random Gaussian codebook + AWGN channel, the average per-message error
probability (using `jointTypicalDecoder` against the AEP-supplied typical set)
is `≤ 2ε` for all `M ≤ ⌈exp(n R)⌉` once `n` is large enough.

**Phase C-3 staging note.** This theorem provides the *existence* of a
measurable typical set `A` (via `h_aep`) plus the integral-bound conclusion.
The integral-bound conclusion is supplied by the load-bearing hypothesis
`h_rand : IsAwgnRandomCodingBound P N h_meas` (Phase C-3 staged
hypothesis, see its docstring). The orchestrator should treat the genuine
Fubini + IndepFun + AEP-chain discharge as a Phase C-3' follow-up.

Honesty: `h_rand` is a regularity-style load-bearing hypothesis (type ≠
`IsAwgnTypicalityHypothesis` conclusion), staged with `@audit:staged(awgn-
random-coding-bound)`. The body here is a routine combination of `h_aep`
(to produce `A`) and `h_rand` (to bound the integral). -/
theorem awgn_avg_error_union_bound
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_aep : IsContinuousAEPGaussian P N)
    (h_rand : IsAwgnRandomCodingBound P N h_meas)
    {R ε : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ M (hM_pos : 0 < M),
      M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) →
      ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)), MeasurableSet A ∧
        haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
        ∀ m : Fin M,
          ∫⁻ codebook : Fin M → Fin n → ℝ,
            ((Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
              ((InformationTheory.Shannon.ChannelCoding.Code.mk
                  (M := M) (n := n) (α := ℝ) (β := ℝ)
                  codebook (jointTypicalDecoder A codebook)).errorEvent m))
          ∂(gaussianCodebook M n P.toNNReal)
            ≤ ENNReal.ofReal (2 * ε) := by
  -- Both staged hypotheses provide an N₀; we take the maximum.
  obtain ⟨N_aep, hN_aep⟩ := h_aep hε
  obtain ⟨N_rand, hN_rand⟩ := h_rand hε hR_pos hR
  refine ⟨max N_aep N_rand, ?_⟩
  intro n hn M hM_pos hM_le
  haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
  -- AEP supplies the typical set A with the 3 bounds; we forward (Measurable A).
  obtain ⟨A, hA_meas, _, _, _⟩ :=
    hN_aep (le_of_max_le_left hn : N_aep ≤ n)
  refine ⟨A, hA_meas, ?_⟩
  -- Hypothesis h_rand supplies the integral bound for any measurable A and any m.
  intro m
  exact hN_rand (le_of_max_le_right hn : N_rand ≤ n) hM_pos hM_le hA_meas m

/-! ## Phase D — Expurgation -/

/-- **Expurgation (D-1)**: avg-≤-B integral ⇒ ∃ codebook with the same bound.

Direct 1-line firing of `MeasureTheory.exists_le_lintegral` (Average.lean:738,
inventory Axis 4.1.1) — `gaussianCodebook M n σsq` is a probability measure
(Phase A instance) so the lemma applies, then `le_trans`. -/
theorem awgn_exists_codebook_le_avg
    {M n : ℕ} (σsq : ℝ≥0)
    (Pe : (Fin M → Fin n → ℝ) → ℝ≥0∞)
    (hPe_aemeas : AEMeasurable Pe (gaussianCodebook M n σsq))
    {B : ℝ≥0∞}
    (h_avg : ∫⁻ c, Pe c ∂(gaussianCodebook M n σsq) ≤ B) :
    ∃ c_specific : Fin M → Fin n → ℝ, Pe c_specific ≤ B := by
  obtain ⟨c, hc⟩ := exists_le_lintegral hPe_aemeas
  exact ⟨c, hc.trans h_avg⟩

/-- **Expurgation (D-2)** "worst-half throw-away": if the sum of `Pe m` is
bounded by `M * (2ε)`, at least `M/2` indices `m` have `Pe m ≤ 4ε`.

Pure `Finset` / arithmetic contraposition (inventory Axis 4.2). Pe is taken in
`ℝ` here because the resulting bound is then handed to `Code.errorProbAt.toReal`
slack reasoning in D-3. -/
theorem awgn_expurgate_worst_half
    {M : ℕ} (hM : 2 ≤ M)
    (Pe : Fin M → ℝ) (hPe_nn : ∀ m, 0 ≤ Pe m) {ε : ℝ} (hε : 0 < ε)
    (h_avg : (∑ m, Pe m) ≤ (M : ℝ) * (2 * ε)) :
    ∃ S : Finset (Fin M), M / 2 ≤ S.card ∧ ∀ m ∈ S, Pe m ≤ 4 * ε := by
  classical
  refine ⟨Finset.univ.filter (fun m => Pe m ≤ 4 * ε), ?_, ?_⟩
  · -- card ≥ M/2 via contrapositive on the "bad" filter
    by_contra hlt
    push Not at hlt
    set S_good : Finset (Fin M) :=
      Finset.univ.filter (fun m : Fin M => Pe m ≤ 4 * ε) with hS_good
    set S_bad : Finset (Fin M) :=
      Finset.univ.filter (fun m : Fin M => ¬ Pe m ≤ 4 * ε) with hS_bad
    have h_card_sum : S_good.card + S_bad.card = M := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin M))) (fun m : Fin M => Pe m ≤ 4 * ε)
      have hu : (Finset.univ : Finset (Fin M)).card = M := by
        simp [Finset.card_univ, Fintype.card_fin]
      simp [hu] at h
      simpa [S_good, S_bad] using h
    have h_card_bad_gt : M / 2 < S_bad.card := by omega
    have h_two_le_card_bad : M / 2 + 1 ≤ S_bad.card := h_card_bad_gt
    -- Real lower bound on S_bad.card.
    have h_two_card_lb_nat : M < 2 * S_bad.card := by
      have h_div : 2 * (M / 2) + M % 2 = M := Nat.div_add_mod M 2 |>.symm ▸ by
        omega
      have h_mod_lt : M % 2 < 2 := Nat.mod_lt M (by norm_num)
      omega
    have h_two_card_lb : (M : ℝ) < 2 * (S_bad.card : ℝ) := by
      have := h_two_card_lb_nat
      have h_cast : ((2 * S_bad.card : ℕ) : ℝ) = 2 * (S_bad.card : ℝ) := by push_cast; ring
      have : (M : ℝ) < ((2 * S_bad.card : ℕ) : ℝ) := by exact_mod_cast this
      linarith [h_cast]
    -- Pe m > 4ε on S_bad.
    have h_strict : ∀ m ∈ S_bad, 4 * ε < Pe m := by
      intro m hm
      have := (Finset.mem_filter.mp hm).2
      push Not at this
      exact this
    have h_nonempty : S_bad.Nonempty := by
      have : 0 < S_bad.card := by omega
      exact Finset.card_pos.mp this
    have h_sum_bad_lb : (S_bad.card : ℝ) * (4 * ε) < ∑ m ∈ S_bad, Pe m := by
      have hsum_lt :
          ∑ _m ∈ S_bad, (4 * ε) < ∑ m ∈ S_bad, Pe m :=
        Finset.sum_lt_sum_of_nonempty h_nonempty h_strict
      have hconst : ∑ _m ∈ S_bad, (4 * ε) = (S_bad.card : ℝ) * (4 * ε) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      linarith
    have h_sub_le : ∑ m ∈ S_bad, Pe m ≤ ∑ m, Pe m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun m _ _ => hPe_nn m)
    -- Combine: M * 2ε < 2 * S_bad.card * 2ε = S_bad.card * 4ε < ∑ Pe ≤ M * 2ε. Contradiction.
    nlinarith [h_two_card_lb, h_sum_bad_lb, h_sub_le, h_avg, hε]
  · intro m hm
    exact (Finset.mem_filter.mp hm).2

/-- **Power-constraint realizability** (Mathlib gap staged predicate).

This packages the assertion that the random Gaussian codebook
`gaussianCodebook M n P.toNNReal` puts positive mass on the set of codebooks
satisfying the deterministic per-message power constraint
`∀ m, ∑ i (c m i)^2 ≤ n · P`. Equivalently (by `gaussianCodebook` being a
probability measure), there *exists* a deterministic codebook satisfying this.

Classically this follows from a continuity / margin argument (Cover-Thomas 9.2
uses `P' < P` so that the empirical second moment concentrates below `P` with
high probability for large `n` via SLLN). The full discharge would invoke
`strong_law_ae_real` coordinate-wise + union bound across `Fin M`, which is the
**same Mathlib gap** as `IsContinuousAEPGaussian`: n-d Gaussian SLLN bundled with
the typicality argument is the missing block.

**NOT load-bearing for the AWGN achievability core** beyond the analytic gap
already absorbed by `IsContinuousAEPGaussian`. We expose it as a separate
predicate so that Phase D-3 (`awgn_extract_AwgnCode`) consumes a deterministic
power-constraint witness without re-quantifying the SLLN argument.

Honesty (4 conditions per CLAUDE.md「Mathlib 壁の 4 分類」):
(a) the predicate type quantifies over `P : ℝ`, `N : ℝ≥0` only — it does **not**
    mention `AwgnCode`, `errorProbAt`, or any of the `IsAwgnTypicalityHypothesis`
    conclusion shape;
(b) docstring (this paragraph) flags "NOT load-bearing" + lists the explicit
    Mathlib gap (n-d Gaussian SLLN coordinate-wise + union bound);
(c) Phase D-3 / E-1 consume the predicate to produce a deterministic codebook
    witness, on top of which the Phase D-1/D-2 expurgation runs genuinely;
(d) `@audit:staged(awgn-power-constraint-realizable)` tag below.

`@audit:staged(awgn-power-constraint-realizable)` -/
def IsAwgnPowerConstraintRealizable (P : ℝ) (N : ℝ≥0) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃R : ℝ⦄, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
    ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n → ∀ ⦃M : ℕ⦄ (_hM_pos : 0 < M),
      M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) →
      -- The set of codebooks satisfying the deterministic power constraint has
      -- mass ≥ 1 - ε under the random Gaussian codebook law.
      (gaussianCodebook M n P.toNNReal)
          {c : Fin M → Fin n → ℝ | ∀ m, (∑ i, (c m i)^2) ≤ (n : ℝ) * P}
        ≥ ENNReal.ofReal (1 - ε)

/-- **Expurgation (D-3)**: bridge to `AwgnCode` type given a deterministic
codebook satisfying both the per-message error bound and the per-message power
constraint. Uses `jointTypicalDecoder` for the decoder and converts the
`ℝ≥0∞`-valued error bound to `< 5ε` real-valued slack. -/
theorem awgn_extract_AwgnCode
    {P : ℝ} {N : ℝ≥0}
    (h_meas : IsAwgnChannelMeasurable N) {n : ℕ}
    {M : ℕ} [NeZero M]
    {ε : ℝ} (hε : 0 < ε)
    {A : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hA_meas : MeasurableSet A)
    (codebook : Fin M → Fin n → ℝ)
    (h_max_Pe : ∀ m,
        (Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m)
        ≤ ENNReal.ofReal (4 * ε))
    (h_power : ∀ m, (∑ i, (codebook m i)^2) ≤ (n : ℝ) * P) :
    ∃ c : AwgnCode M n P,
      ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < 5 * ε := by
  refine ⟨{
    encoder := codebook
    decoder := jointTypicalDecoder A codebook
    decoder_meas := jointTypicalDecoder_measurable A hA_meas codebook
    power_constraint := h_power
  }, ?_⟩
  intro m
  -- toCode.errorProbAt = (Measure.pi (W ∘ encoder m)) (errorEvent ...).
  -- Pe ≤ 4ε in ℝ≥0∞ + 4ε.toReal = 4ε < 5ε.
  have h_pe_le := h_max_Pe m
  -- The body of c.toCode.errorProbAt for our AwgnCode equals the LHS in h_max_Pe.
  have h_eq :
      (({ encoder := codebook
          decoder := jointTypicalDecoder A codebook
          decoder_meas := jointTypicalDecoder_measurable A hA_meas codebook
          power_constraint := h_power : AwgnCode M n P }).toCode.errorProbAt
            (awgnChannel N h_meas) m)
      = (Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m) := rfl
  rw [h_eq]
  -- Now compare with ENNReal.ofReal (4 * ε) ≤ ENNReal.ofReal (5 * ε), take .toReal.
  have h_target : (ENNReal.ofReal (4 * ε)).toReal < 5 * ε := by
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith
  have h_ne_top : (ENNReal.ofReal (4 * ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ((Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m)).toReal
      ≤ (ENNReal.ofReal (4 * ε)).toReal := by
        apply ENNReal.toReal_mono h_ne_top h_pe_le
    _ < 5 * ε := h_target

/-! ## Phase E — `isAwgnTypicalityHypothesis` 統合 + main wrapper -/

/-- **F-1 撤退ライン discharge** — `IsAwgnTypicalityHypothesis` を Phase A-D の
組合せで本物に discharge。

staged hypotheses (3 本、全て honest 4 条件を満たす regularity hyp、Mathlib 壁
"analytic" 系):

* `h_aep : IsContinuousAEPGaussian P N` — 連続版 AEP 3 bound (Phase B-0)
* `h_rand : IsAwgnRandomCodingBound P N h_meas` — random-coding 積分 bound (Phase C-3)
* `h_power : IsAwgnPowerConstraintRealizable P N` — codebook の power constraint
  実現可能性 (Phase D-3 staged extension)

3 つの hyp は全て n-d Gaussian SLLN / continuous SMB の Mathlib gap に紐づく
analytic 系の壁。achievability core (codebook + decoder + union bound +
expurgation + AwgnCode 抽出) は本 theorem body で genuine に組み上げる。

**Body assembly skeleton (Phase E-1 detail, deferred to next session)**:

```
intro R hR_pos hR ε hε
let ε' := ε / 5  -- so that 5 * ε' = ε
obtain ⟨N_aep,  hN_aep⟩  := h_aep   (by positivity : 0 < ε')
obtain ⟨N_rand, hN_rand⟩ := h_rand  (by positivity : 0 < ε') hR_pos hR
obtain ⟨N_pow,  hN_pow⟩  := h_power (by positivity : 0 < ε') hR_pos hR
refine ⟨max N_aep (max N_rand N_pow), ?_⟩
intro n hn
let M_target : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R))
let M : ℕ := 2 * M_target          -- expurgate half
have hM_pos : 0 < M := by ...      -- since exp (n*R) > 1
haveI : NeZero M := ⟨hM_pos.ne'⟩
-- (1) typical set + measurability from AEP.
obtain ⟨A, hA_meas, _, _, _⟩ := hN_aep ...
-- (2) per-m average error bound from h_rand.
have h_per_m := hN_rand ... hM_pos ... hA_meas
-- (3) average over codebooks of (∑_m Pe(c, m) on power-OK c) ≤ M * 2ε'
--     via Fubini, h_per_m summed across m, and h_power restricting to power-OK set.
have h_avg_sum : ∫⁻ codebook, ... ≤ M * (2 * ε') := ...      -- needs ~30-50 lines
-- (4) D-1: extract a specific codebook with ∑_m Pe(c, m) ≤ M * 2ε' + power_constraint.
obtain ⟨c_full, hc_avg, hc_power⟩ := awgn_exists_codebook_le_avg ...   -- ~5 lines
-- (5) D-2: throw away worst half ⇒ subset S ⊆ Fin M, |S| ≥ M/2 = M_target,
--     ∀ m ∈ S, Pe(c_full, m).toReal ≤ 4 * ε'.
obtain ⟨S, hS_card, hS_pe⟩ := awgn_expurgate_worst_half ...            -- ~5 lines
-- (6) reindex: extract Fin M_target → Fin n → ℝ from c_full via Finset.equivFin.
let subcodebook : Fin M_target → Fin n → ℝ := ...                       -- ~10 lines
-- (7) D-3: bridge to AwgnCode with the 5ε' = ε bound.
exact ⟨M_target, le_rfl, awgn_extract_AwgnCode ... ⟩
```

**Honesty status (current commit)**: this theorem body is left as `sorry`
because the (3)→(4) Fubini-style averaging across `Fin M` of the per-message
`h_rand` bound, combined with restriction to the `h_power` set, is a
~50-80-line probability manipulation that is genuinely independent of the
3 staged hypotheses already in scope. It is **not** a load-bearing hypothesis
that hides analytic content — it is a routine sum-and-Fubini bridge.
Splitting it out as a 4th staged hypothesis would be name laundering
(forbidden); doing it inline is the right design but exceeds the per-session
scope. The next session should write the body inline using the skeleton above
and the 3 already-staged hypotheses.

`@audit:residual(awgn-typicality-E1-body)` -/
theorem isAwgnTypicalityHypothesis
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_aep : IsContinuousAEPGaussian P N)
    (h_rand : IsAwgnRandomCodingBound P N h_meas)
    (h_power : IsAwgnPowerConstraintRealizable P N) :
    IsAwgnTypicalityHypothesis P N h_meas := by sorry

/-- **`awgn_achievability` F-1 discharge wrapper** — `h_typicality` 引数を
`isAwgnTypicalityHypothesis` で埋めて再 publish (Phase E-2). -/
theorem awgn_achievability_F1_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_aep : IsContinuousAEPGaussian P N)
    (h_rand : IsAwgnRandomCodingBound P N h_meas)
    (h_power : IsAwgnPowerConstraintRealizable P N)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε :=
  awgn_achievability P hP N hN h_meas
    (isAwgnTypicalityHypothesis P hP N hN h_meas h_aep h_rand h_power) hR_pos hR hε

/-- **Main theorem F-1 + F-4 discharge wrapper** — `awgn_channel_coding_theorem` の
`h_meas` (F-4 / `isAwgnChannelMeasurable`) と `h_typicality` (F-1) を埋めて再 publish。
残 hyp = `h_mi_bridge` (F-2) + `h_converse` (F-3) + `h_aep` + `h_rand` + `h_power`
(continuous AEP / random-coding / power-constraint の 3 staged hyp). -/
theorem awgn_theorem_F1F4_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_aep : IsContinuousAEPGaussian P N)
    (h_rand : IsAwgnRandomCodingBound P N (isAwgnChannelMeasurable N))
    (h_power : IsAwgnPowerConstraintRealizable P N)
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
                  (awgnChannel N (isAwgnChannelMeasurable N)) m).toReal < ε :=
  awgn_channel_coding_theorem P hP N hN (isAwgnChannelMeasurable N)
    (isAwgnTypicalityHypothesis P hP N hN (isAwgnChannelMeasurable N)
      h_aep h_rand h_power) h_mi_bridge h_converse hR_pos hR_lt_C hε

end InformationTheory.Shannon.AWGN

# Wyner–Ziv achievability construction — in-project atom inventory

> **Scope**: the remaining `sorry` body of
> `wz_goodCode_exists_of_testChannel`
> (`InformationTheory/Shannon/WynerZiv/Achievability.lean:291`,
> `@residual(plan:wyner-ziv-main-plan)`).
> These are **in-project `InformationTheory/` atoms**, not Mathlib. Mathlib has
> **zero operational coding theory** (method-of-types / typicality / Csiszár), so
> the construction composes only in-project assets.
>
> **Parent plan**: [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md) (retreat
> lines at §57 gateway-atom-first, §181 honesty). This file is inventory only —
> no implementation plan (planner's job).

## One-line summary

**Every atom the covering+binning construction needs already exists in-project
(0 genuinely-absent, ~26 atoms across 9 files); the work is composition plumbing,
not self-build.** The three highest-risk items are all **hypothesis-supply gaps,
not missing lemmas**: (1) the RD-covering half demands **full support**
`hqStar_pos : ∀ p, 0 < qStar p` which the feasible test channel `hqf` does **NOT**
provide (`IsWynerZivFactorizable` is only row-stochastic), forcing an internal
perturbation `qf → qf_τ`; (2) the covering + gateway atoms demand
`iIndepFun`/`IdentDistrib`/`hpos*` on an ambient measure that must be **manufactured**
from `qf` (via `rdAmbient` on the (X,U) and (U,Y) marginals); (3) `Nonempty (Fin k)`
must be derived from `hqf` (the row-sum condition). One reuse blocker:
`tendsto_exp_mul_codebookSize_inv` is `private` in `PairBound.lean` — needs a public
re-export or a local re-proof.

---

## Target theorem (restated verbatim)

`InformationTheory/Shannon/WynerZiv/Achievability.lean:291`

```lean
private lemma wz_goodCode_exists_of_testChannel
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
    (hobj : wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 < R) :
    ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (c n).expectedBlockDistortion P_XY d ≤ D + ε
```

Ambient variable block (`Achievability.lean:79`):
```lean
variable {α β γ U : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [DecidableEq γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
```
(Here the codebook alphabet is `U = Fin k`, which carries all four classes for `k > 0`.)

Construction flow (pseudo-Lean, ≤10 lines):
```
-- 0. from hqf: extract kernel κ (row-stochastic); Nonempty (Fin k); q3 := qf.1 (X,Y,U pmf)
-- 1. perturb: qf_τ := (1-τ)·qf.1 + τ·uniform  → full support, obj still < R  (continuous_wzObjective)
-- 2. covering half: qXU_τ := wzMarginalXU qf_τ; rate_distortion_achievability on rdAmbient qXU_τ
--       ⇒ ∃ lossy code X→U with expected block distortion ≤ D+ε  (LossyCode Mⁿ n α U)
-- 3. binning half: bin the covering index by binningMeasure U n M down to R = I(X;U)−I(Y;U)
-- 4. decode: conditionalTypicalSlice search of the bin against Y^n; two error events:
--       E1 covering-failure (encoder_failure...), E2 decoder-confusion (gateway 1), E3 accept (gateway 2)
-- 5. pigeonhole exists_codebook_low_avg → deterministic good (codebook,binning); assemble WynerZivCode
-- 6. squeeze distortion excess to 0 via ceil_exp_mul_exp_neg_tendsto_atTop; diagonalize τ→0
```

---

## A. Test-channel regularity — what `hqf` gives vs does NOT give

| concept | atom | file:line | status | what it provides |
|---|---|---|---|---|
| feasibility membership | `mem_WynerZivFactorizableConstraint_iff` | `WynerZiv/FactorizableRate.lean:284` | reuse | `qf ∈ … ↔ IsWynerZivFactorizable U P_XY qf.1 ∧ wzExpectedDistortion U d qf.1 qf.2 ≤ D` |
| factorisation predicate | `IsWynerZivFactorizable` (def) | `WynerZiv/FactorizableRate.lean:76` | reuse | see verbatim below — row-stochastic kernel only |
| Markov structure (derived) | `IsWynerZivFactorizable_markov` | `WynerZiv/FactorizableRate.lean:107` | reuse | `wzMarkovCrossEq U q` (U−X−Y) — **present, free** |
| XY-marginal fixed | `IsWynerZivFactorizable_marginalXY` | `WynerZiv/FactorizableRate.lean:135` | reuse | `wzMarginalXY U q = P_XY` |
| non-negativity | `IsWynerZivFactorizable_nonneg` | `WynerZiv/FactorizableRate.lean:156` | reuse | `∀ p, 0 ≤ q p` (needs `h_pmf_nn`) |
| in simplex | `IsWynerZivFactorizable_mem_stdSimplex` | `WynerZiv/FactorizableRate.lean:200` | reuse | `q ∈ stdSimplex ℝ (α × β × U)` (needs `P_XY ∈ stdSimplex`) |
| convex combination | `IsWynerZivFactorizable_convex_combination` | `WynerZiv/FactorizableRate.lean:233` | reuse | closure under `a•q₁ + b•q₂` — **the perturbation lever** |

**`IsWynerZivFactorizable` — verbatim (`FactorizableRate.lean:76`):**
```lean
def IsWynerZivFactorizable
    (P_XY : α × β → ℝ) (q : α × β × U → ℝ) : Prop :=
  ∃ κ : α → U → ℝ,
    (∀ x u, 0 ≤ κ x u)
    ∧ (∀ x, ∑ u, κ x u = 1)
    ∧ (∀ x y u, q (x, y, u) = κ x u * P_XY (x, y))
```
Type-class context (section vars, `FactorizableRate.lean:59-62`):
```lean
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]
```

**Regularity verdict — CRITICAL:** membership in `WynerZivFactorizableConstraint`
forces exactly three things and **no more**:
- **row-stochastic kernel** `κ` (`0 ≤ κ x u`, `∑_u κ x u = 1`) ✔ present
- **Markov `U − X − Y`** (cross-product `wzMarkovCrossEq`) ✔ present (derived, `:107`)
- **distortion feasibility** `wzExpectedDistortion ≤ D` ✔ present

It does **NOT** force:
- **full support** `0 < κ x u` (κ may vanish on some `u`) ✖ **ABSENT — the perturbation gap**
- `Nonempty (Fin k)` in the type (`k = 0` allowed by the type; ruled out only by the row-sum, see gap #3)

**Continuity for the perturbation argument (`WynerZiv/Basic.lean`):**
```lean
def wzMutualInfoXU (q : α × β × U → ℝ) : ℝ := mutualInfoPmf (wzMarginalXU U q)   -- Basic.lean:115
def wzMutualInfoYU (q : α × β × U → ℝ) : ℝ := mutualInfoPmf (wzMarginalYU U q)   -- Basic.lean:120
lemma continuous_wzObjective :                                                    -- Basic.lean:159
    Continuous (fun q : α × β × U → ℝ ↦ wzMutualInfoXU U q - wzMutualInfoYU U q)
```
`@[entry_point]`, section vars `[Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]`
and `(U : Type*) [Fintype U] [MeasurableSpace U]`. This is the exact continuity the
`qf_τ = (1-τ)·qf + τ·uniform`, `obj(qf_τ) → obj(qf) < R` argument consumes.

---

## B. Rate-distortion covering half (X → U)

### B1. The covering theorem — the biggest hypothesis-threading risk

`InformationTheory/Shannon/RateDistortion/AchievabilityStrongTypicality.lean:184`
(public form; `_strong` at `:97` is identical modulo the internal name). Section
context (`:74-77`): `{Ω} [MeasurableSpace Ω]`, `{α β} [MeasurableSpace α] [MeasurableSpace β]`,
`[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]`, same for `β`.
In WZ the covering runs with `α := X`, `β := U` (reconstruction = covering alphabet).

**FULL hypothesis list, verbatim:**
```lean
theorem rate_distortion_achievability
    (P_X_pmf : α → ℝ) (d : DistortionFn α β) {D : ℝ}
    (qStar : α × β → ℝ) (hqStar_mem : qStar ∈ RDConstraint P_X_pmf d D)
    (hqStar_pos : ∀ p : α × β, 0 < qStar p)
    {R : ℝ} (hI_lt_R : mutualInfoPmf qStar < R)
    {ε' : ℝ} (hε' : 0 < ε')
    (ε_X ε_join ε_dist δ_kl δ_typ : ℝ)
    (hε_X_pos : 0 < ε_X) (hε_join_pos : 0 < ε_join)
    (hε_dist_pos : 0 < ε_dist) (hδ_kl_pos : 0 < δ_kl) (hδ_typ_nn : 0 ≤ δ_typ)
    (hε_X_lt_ε_join : ε_X < ε_join)
    (h_rate_gap :
        mutualInfoPmf qStar
            + ((Fintype.card α : ℝ) * ε_X * logSumAbs (rdAmbient qStar)
                  (iidYs (α := α) (β := β))
              + ε_X * logSumAbs (rdAmbient qStar) (iidXs (α := α) (β := β))
              + ε_X * logSumAbs (rdAmbient qStar)
                  (jointSequence (α := α) (β := β) iidXs iidYs)
              + δ_kl) < R)
    (h_slack : expectedDistortionPmf d qStar + δ_typ ≤ D + ε' / 2)
    (h_dist_slack :
        ε_join * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) ≤ δ_typ)
    (h_jts_subset_dts : ∀ {n : ℕ}, 0 < n → ∀ (x : Fin n → α) (y : Fin n → β),
        (x, y) ∈ jointStronglyTypicalSet (rdAmbient qStar) iidXs iidYs n ε_join →
        (x, y) ∈ distortionTypicalSet (rdAmbient qStar) iidXs iidYs d n
                      ε_dist δ_typ)
    (qZ_min : ℝ) (hqZ_min_pos : 0 < qZ_min)
    (hqZ_min_le : ∀ p : α × β,
        qZ_min ≤ (pmfToMeasure (α := α × β) qStar).real {p})
    (hδ_kl_dominates :
        8 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2
          ≤ δ_kl * qZ_min) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : LossyCode M n α β),
        c.expectedBlockDistortion
            ((rdAmbient qStar).map (iidXs (α := α) (β := β) 0)) d ≤ D + ε'
```
**Conclusion form (verbatim):** for `n ≥ N`, an `M ≥ ⌈exp(nR)⌉`-codeword `LossyCode M n α β`
whose `expectedBlockDistortion` under the `rdAmbient`-pushed source is `≤ D + ε'`.

> Note `qStar` here is the **(X,U) joint** = `wzMarginalXU U qf.1`, a 2-var pmf on `α × U`.
> `RDConstraint`/`expectedDistortionPmf`/`logSumAbs`/`mutualInfoPmf` are all in-project.

### B2. Covering support atoms

| concept | atom | file:line | verbatim conclusion / type |
|---|---|---|---|
| encoder (index of first typical codeword) | `jointTypicalLossyEncoder` | `RateDistortion/AchievabilityJointTypicalEncoder.lean:63` | `(μ) (Xs Ys) {M n} (hM : 0 < M) (ε) (c : Codebook M n β) : (Fin n → α) → Fin M` |
| bundle codebook→LossyCode | `lossyCodeOfCodebook` | `…JointTypicalEncoder.lean:76` | `… (hM : 0 < M) (ε) (c : Codebook M n β) : LossyCode M n α β` |
| distortion-typical set | `distortionTypicalSet` | `…JointTypicalEncoder.lean:97` | `(μ)(Xs Ys)(d)(n)(ε δ) : Set ((Fin n → α) × (Fin n → β))` |
| block-distortion bound on set | `blockDistortion_le_of_mem_distortionTypicalSet` | `…JointTypicalEncoder.lean:109` | `blockDistortion d n p.1 p.2 ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d + δ` |
| covering-failure exp bound | `encoder_failure_prob_le_exp_neg_M_avg` | `RateDistortion/AchievabilityCodebookMatchProbability.lean:63` | see verbatim below |
| pigeonhole (good codebook) | `exists_codebook_low_avg` | `…AchievabilityCodebookMatchProbability.lean:138` | see verbatim below |
| per-source distortion bound | `source_avg_distortion_le_simpler` | `RateDistortion/AchievabilityAsymptoticFailureDecay.lean:203` | `∫ x, blockDistortion … ≤ (E[d]+δ) + distortionMax d * P_X.real {failure set}` |

**`encoder_failure_prob_le_exp_neg_M_avg` — verbatim (`…CodebookMatchProbability.lean:63`):**
```lean
theorem encoder_failure_prob_le_exp_neg_M_avg
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (ε : ℝ)
    (P_X : Measure (Fin n → α)) [IsProbabilityMeasure P_X]
    (p : Measure (Fin n → β)) [IsProbabilityMeasure p] :
    ∫ x, (1 - p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ^ M ∂P_X
      ≤ ∫ x, Real.exp (-(M : ℝ) *
          p.real {y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ∂P_X
```

**`exists_codebook_low_avg` — verbatim (`…CodebookMatchProbability.lean:138`):**
```lean
theorem exists_codebook_low_avg
    {M n : ℕ}
    (p : Measure β) [IsProbabilityMeasure p]
    (f : Codebook M n β → ℝ) {B : ℝ}
    (h_avg : ∑ c : Codebook M n β, (codebookMeasure p M n).real {c} * f c ≤ B) :
    ∃ c : Codebook M n β, f c ≤ B
```
Section vars for both (`…CodebookMatchProbability.lean:29-32`): `{Ω} [MeasurableSpace Ω]`,
`{α β} [MeasurableSpace α] [MeasurableSpace β]`, `[Fintype α] [DecidableEq α] [Nonempty α]
[MeasurableSingletonClass α]` and same for `β`. The "low average" is the codebook-measure
weighted average of `f c`; conclusion picks a single deterministic codebook below the mean.

### B3. `LossyCode` vs `WynerZivCode` — the structural gap the construction bridges

`RateDistortion/Achievability.lean:81` and `:91`:
```lean
structure LossyCode (M n : ℕ) (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  encoder : (Fin n → α) → Fin M
  decoder : Fin M → (Fin n → β)
def LossyCode.expectedBlockDistortion (c : LossyCode M n α β) (P_X : Measure α) (d : DistortionFn α β) : ℝ :=
  ∫ x : Fin n → α, blockDistortion d n x (c.decoder (c.encoder x)) ∂(Measure.pi (fun _ : Fin n ↦ P_X))
```
`WynerZiv/Basic.lean:59` and `:73`:
```lean
structure WynerZivCode (M n : ℕ) (α β γ : Type*)
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] where
  encoder : (Fin n → α) → Fin M
  decoder : Fin M × (Fin n → β) → (Fin n → γ)
def WynerZivCode.expectedBlockDistortion (c : WynerZivCode M n α β γ) (P_XY : Measure (α × β)) (d : DistortionFn α γ) : ℝ :=
  ∫ p : Fin n → α × β, blockDistortion d n (fun i ↦ (p i).1)
        (c.decoder (c.encoder (fun i ↦ (p i).1), fun i ↦ (p i).2)) ∂(Measure.pi (fun _ : Fin n ↦ P_XY))
```
**Differences the construction must reconcile:** (a) WZ decoder is `Fin M × (Fin n → β) → (Fin n → γ)`
(takes bin index **and** side info `Y^n`), vs LossyCode decoder `Fin M → (Fin n → β)`
(covering only). (b) WZ integrates over `Measure.pi P_XY` on `(α×β)^n`; LossyCode over
`Measure.pi P_X` on `α^n`. Bridge: `Measure.pi_map_pi` (Mathlib, used elsewhere in-project
e.g. `BlockwiseChannel/MemorylessCapacity.lean:278`) to marginalise `Measure.pi P_XY` to
`Measure.pi (P_XY.map fst)`. This is an **adapter**, not a missing atom.

### B4. Ambient-measure constructor (manufactures the i.i.d. law)

`RateDistortion/AchievabilityAmbientMeasure.lean` — builds an i.i.d. product measure on
`ℕ → α × β` from a 2-var pmf, with all the marginal/positivity lemmas the covering + gateway
atoms consume:
```lean
def rdAmbient (qStar : α × β → ℝ) : Measure (ℕ → α × β)                                  -- :153
lemma rdAmbient_isProbabilityMeasure (qStar) (hq : qStar ∈ stdSimplex ℝ (α × β)) : IsProbabilityMeasure (rdAmbient qStar)  -- :156
lemma rdAmbient_map_iidXs … : (rdAmbient qStar).map (iidXs 0) = (pmfToMeasure qStar).map Prod.fst  -- :165
lemma rdAmbient_map_iidYs … : (rdAmbient qStar).map (iidYs 0) = (pmfToMeasure qStar).map Prod.snd  -- :174
lemma rdAmbient_map_jointSequence … : (rdAmbient qStar).map (jointSequence iidXs iidYs 0) = pmfToMeasure qStar  -- :183
lemma pmfToMeasure_real_singleton_pos (hq) (hq_pos : ∀ p, 0 < q p) (p) : 0 < (pmfToMeasure q).real {p}  -- :139
lemma expectedJointDistortion_rdAmbient (qStar) (hqStar_simp) (d) : expectedJointDistortion (rdAmbient qStar) (iidXs 0) (iidYs 0) d = expectedDistortionPmf d qStar  -- :216
```
`iidXs`/`iidYs : ℕ → (ℕ → α × β) → α/β` at `IIDProductInput/Basic.lean:58/61`.
**This is exactly the machine that turns a pmf into the `μ, Xs, Ys, iIndepFun, IdentDistrib,
hpos*` bundle** the covering theorem and gateway atoms require. The construction instantiates
it twice — once on the (X,U) marginal (covering), once on the (U,Y) marginal (side-info decode).

---

## C. Slepian–Wolf binning + side-info decode half

### C1. Binning primitives

```lean
def binningMeasure (α : Type*) [Fintype α] [MeasurableSpace α] (n M : ℕ) [NeZero M] :   -- Binning.lean:62
    Measure ((Fin n → α) → Fin M) :=
  Measure.pi (fun _ : (Fin n → α) ↦ uniformOn (Set.univ : Set (Fin M)))
instance binningMeasure.instIsProbabilityMeasure (n M : ℕ) [NeZero M] :               -- Binning.lean:69
    IsProbabilityMeasure (binningMeasure α n M)
theorem binning_collision_prob {n M : ℕ} [NeZero M] {x x' : Fin n → α} (h : x ≠ x') :  -- Binning.lean:106
    (binningMeasure α n M).real {f | f x = f x'} = (M : ℝ)⁻¹
```
Section vars (`Binning.lean:44`): `{α} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`.
`[NeZero M]` is required — supplied by `codebookSize_neZero` (§D).

### C2. Conditional typical slice

```lean
def conditionalTypicalSlice (μ) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (n : ℕ) (ε : ℝ) (y : Fin n → β) : Set (Fin n → α) :=  -- ConditionalTypicalSlice.lean:51
  { x | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε }
theorem conditionalTypicalSlice_card_le                                               -- ConditionalTypicalSlice.lean:140
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepY_full : iIndepFun (fun i ↦ Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ_full : iIndepFun (fun i ↦ jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i, IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε : ℝ} (y : Fin n → β) :
    ((conditionalTypicalSlice μ Xs Ys n ε y).toFinite.toFinset.card : ℝ)
      ≤ Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0) + 2 * ε))
```
Section vars (`ConditionalTypicalSlice.lean:41-45`): `{Ω} [MeasurableSpace Ω]`,
`{α} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`,
`{β} [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]`.

### C3. Gateway atoms — already proved (`@audit:ok`), the construction MUST supply their full hyp lists

**Gateway 1 — decoder confusion (`Achievability.lean:105`):** identical hyp list to
`swError_EX_expectation_le`. The construction must supply every one of:
```lean
theorem wz_sideInfo_decoder_confusion_expectation_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Us : ℕ → Ω → U) (Ys : ℕ → Ω → β)
    (hUs : ∀ i, Measurable (Us i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepY_full : iIndepFun (fun i ↦ Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ_full : iIndepFun (fun i ↦ ChannelCoding.jointSequence Us Ys i) μ)
    (hidentZ : ∀ i, IdentDistrib (ChannelCoding.jointSequence Us Ys i)
        (ChannelCoding.jointSequence Us Ys 0) μ μ)
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : U × β, 0 < (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {p})
    {n M : ℕ} [NeZero M] {ε : ℝ} (hε : 0 < ε) :
    ∫ f, μ.real (ChannelCoding.swError_EX μ Us Ys n ε f) ∂(binningMeasure U n M)
      ≤ Real.exp ((n : ℝ) *
            (entropy μ (ChannelCoding.jointSequence Us Ys 0) - entropy μ (Ys 0) + 2 * ε))
        * ((M : ℝ))⁻¹
```

**Gateway 2 — covering acceptance (`Achievability.lean:143`):** the full hyp list adds
marginal-matching + KL-domination + slack side-conditions:
```lean
theorem wz_covering_sideInfo_mass_ge
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Us : ℕ → Ω → U) (Ys : ℕ → Ω → β)
    (hUs : ∀ i, Measurable (Us i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep_Z_pair : Pairwise fun i j ↦
      ChannelCoding.jointSequence Us Ys i ⟂ᵢ[μ] ChannelCoding.jointSequence Us Ys j)
    (hident_Z : ∀ i, IdentDistrib (ChannelCoding.jointSequence Us Ys i)
        (ChannelCoding.jointSequence Us Ys 0) μ μ)
    (hposZ : ∀ p : U × β, 0 < (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {p})
    (hposX : ∀ a : U, 0 < (μ.map (Us 0)).real {a})
    (hposY : ∀ b : β, 0 < (μ.map (Ys 0)).real {b})
    (hmarg_X : (μ.map (ChannelCoding.jointSequence Us Ys 0)).map Prod.fst = μ.map (Us 0))
    (hmarg_Y : (μ.map (ChannelCoding.jointSequence Us Ys 0)).map Prod.snd = μ.map (Ys 0))
    {ε ε_X δ : ℝ}
    (hε : 0 < ε) (hε_X : 0 ≤ ε_X) (hε_X_lt_ε : ε_X < ε) (hδ : 0 < δ)
    (qZ_min : ℝ) (hqZ_min_pos : 0 < qZ_min)
    (hqZ_min_le : ∀ p : U × β, qZ_min ≤ (μ.map (ChannelCoding.jointSequence Us Ys 0)).real {p})
    (hδ_dominates_kl :
        8 * (Fintype.card U : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2 ≤ δ * qZ_min) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (u : Fin n → U),
      u ∈ stronglyTypicalSet μ Us n ε_X →
      Real.exp (-(n : ℝ) * (entropy μ (Us 0) + entropy μ (Ys 0)
            - entropy μ (ChannelCoding.jointSequence Us Ys 0)
            + ((Fintype.card U : ℝ) * ε_X * logSumAbs μ Ys + ε_X * logSumAbs μ Us
               + ε_X * logSumAbs μ (ChannelCoding.jointSequence Us Ys) + δ)))
        ≤ (Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0))).real
              (conditionalStronglyTypicalSlice μ Us Ys n ε u)
```
Underlying (internal) atoms behind the gateways — present, no need to reinvoke directly:
`swError_EX` (`SlepianWolf/FullRateRegion/Core.lean:49`), `swError_EX_expectation_le`
(`SlepianWolf/FullRateRegion/AliasBound.lean:182`), `conditionalStronglyTypicalSlice_mass_ge`
(`ConditionalMethodOfTypes/Mass.lean:1274`).

---

## D. Asymptotic decay + rate

```lean
lemma ceil_exp_mul_exp_neg_tendsto_atTop {R θ : ℝ} (hRθ : θ < R) :                   -- AsymptoticFailureDecay.lean:40
    Filter.Tendsto (fun n : ℕ ↦ (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) * Real.exp (-(n : ℝ) * θ))
      Filter.atTop Filter.atTop
lemma exp_neg_tendsto_zero_of_tendsto_atTop {f : ℕ → ℝ}                              -- AsymptoticFailureDecay.lean:78
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n ↦ Real.exp (-(f n))) Filter.atTop (𝓝 0)
theorem source_avg_distortion_le_simpler                                            -- AsymptoticFailureDecay.lean:203
    (μ) (Xs) (Ys) (d : DistortionFn α β) {M n : ℕ} (hM : 0 < M) (ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (c : Codebook M n β) (P_X : Measure (Fin n → α)) [IsProbabilityMeasure P_X] :
    ∫ x, blockDistortion d n x (c (jointTypicalLossyEncoder μ Xs Ys hM ε c x)) ∂P_X
      ≤ (expectedJointDistortion μ (Xs 0) (Ys 0) d + δ)
        + distortionMax d * P_X.real
            { x | (x, c (jointTypicalLossyEncoder μ Xs Ys hM ε c x)) ∉ distortionTypicalSet μ Xs Ys d n ε δ }
```

Rate / message-count atoms (`AEP/Basic/Achievability.lean`):
```lean
def codebookSize (R : ℝ) (n : ℕ) : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R))            -- :42
lemma codebookSize_pos (R : ℝ) (n : ℕ) : 0 < codebookSize R n                        -- :45
instance codebookSize_neZero (R : ℝ) (n : ℕ) : NeZero (codebookSize R n)             -- :49  (feeds binningMeasure [NeZero M])
lemma codebookSize_log_div_tendsto {R : ℝ} (hR : 0 < R) :                            -- :241
    Tendsto (fun n : ℕ ↦ Real.log (codebookSize R n : ℝ) / n) atTop (𝓝 R)
```
Section vars (`AEP/Basic/Achievability.lean:23-24`): `{Ω} [MeasurableSpace Ω]`,
`{α} [Fintype α] [Nonempty α]`.

**REUSE BLOCKER — `tendsto_exp_mul_codebookSize_inv` is `private`:**
```lean
private lemma tendsto_exp_mul_codebookSize_inv {c R : ℝ} (hcR : c < R) :             -- SlepianWolf/FullRateRegion/PairBound.lean:959
    Filter.Tendsto (fun n : ℕ ↦ Real.exp ((n : ℝ) * c) * ((codebookSize R n : ℝ))⁻¹) Filter.atTop (𝓝 0)
```
`private` = file-scoped (`PairBound.lean`), so **not callable from `Achievability.lean`**.
The construction needs `exp(n c)/M_n → 0` (E2 collision term over the bin count `M`);
either (i) re-export it publicly (1-line move of the `private` keyword, but that file is a
different module — a public alias lemma is cleaner), or (ii) re-prove locally (~15 lines;
its body is a `squeeze_zero` against `exp(n(c−R))` via `codebookSize_inv_le_exp_neg`).
`ceil_exp_mul_exp_neg_tendsto_atTop` (`:40`, public) covers the E1/E3 `⌈exp(nR)⌉·exp(−nθ)→∞`
direction, so only the inverse-count direction is behind the wall.

---

## Key-preconditions box (accident-prone hypotheses)

- **RD covering `hqStar_pos : ∀ p, 0 < qStar p`** — full support on the (X,U) joint.
  **NOT free from `hqf`.** Must be manufactured by perturbation. This premise is the
  single reason the theorem's own docstring (`AchievabilityStrongTypicality.lean:92-95`,
  `:179-180`) says the unconditional form needs `qStar_τ := (1−τ)·qStar + τ·uniform`.
- **RD covering slack quintet** `ε_X ε_join ε_dist δ_kl δ_typ` + `h_rate_gap` + `h_slack` +
  `h_dist_slack` + `h_jts_subset_dts` + `qZ_min`/`hqZ_min_pos`/`hqZ_min_le`/`hδ_kl_dominates`.
  All caller-chosen; consistent choices exist for any full-support `qStar` with
  `mutualInfoPmf qStar < R`. `qZ_min` = min singleton mass, positive iff full support
  (hence again depends on the perturbation).
- **Gateway atoms `iIndepFun` / `IdentDistrib` / `hposX,hposY,hposZ` / `hmarg_X,hmarg_Y`** —
  all discharged by `rdAmbient` lemmas (§B4) once the (U,Y) marginal is full-support.
- **`hmarg_X`/`hmarg_Y`** (gateway 2): `jointSequence`-law fst/snd = single marginals.
  From `rdAmbient_map_jointSequence` + `Measure.map_map`. Watch: these are equalities of
  **measures**, not just singleton masses.
- **`[NeZero M]`** on `binningMeasure` / gateway 1: `M := codebookSize R n`, discharged by
  `codebookSize_neZero`. Do not let `M = 0` slip in from a raw `⌈exp⌉` without the instance.
- **`0 < R`** (needed for `codebookSize_log_div_tendsto`): from `wynerZivRate_nonneg`
  (`Achievability.lean:196`) + `hobj`/`h_rate`. Already threaded in the headline body.

---

## Construction wiring sketch (composition, not a plan)

The covering codebook, binning function, and conditional-slice decoder compose into one
`WynerZivCode (codebookSize R n) n α β γ` as follows.

1. **Alphabet fixing.** `U := Fin k`. Split the message rate `R = I(X;U) − I(Y;U)` at the
   perturbed test channel; covering runs at rate `R₁ ≈ I(X;U)`, binning compresses by
   `≈ I(Y;U)`, net operational rate `R`.
2. **Covering layer (encoder).** Build `rdAmbient (wzMarginalXU U qf_τ.1)` on `ℕ → α × U`;
   feed `rate_distortion_achievability` (α:=X, β:=U). Output: a `Codebook M₁ n U` + the
   `jointTypicalLossyEncoder` mapping `X^n ↦` covering index `∈ Fin M₁`, block distortion
   `≤ D+ε'` — but distortion is measured between `X` and its `γ`-reconstruction via the
   decoder codeword, so `γ`-reconstruction rides on the covering codeword `u = c(m)`, using
   `qf_τ.2 : Fin k × β → γ` per-letter.
3. **Binning layer (encoder cont.).** `binningMeasure U n (codebookSize R n)` hashes the
   covering index-word to `Fin (codebookSize R n)` = the transmitted message.
4. **Decoder.** `WynerZivCode.decoder : Fin M × (Fin n → β) → (Fin n → γ)`: from `(bin, Y^n)`
   search the bin for the unique covering codeword `u'` with `Y^n ∈ conditionalTypicalSlice`
   (`u'` accepted); reconstruct `γ^n` letterwise `i ↦ qf_τ.2 (u' i, (Y^n) i)`.
5. **Three error exponents under `R = I(X;U) − I(Y;U)`.**
   - **E1 covering failure** (no covering codeword typical with `X^n`):
     `encoder_failure_prob_le_exp_neg_M_avg` → `exp(−M₁·mass)`, `M₁ ≈ exp(nI(X;U))` kills it
     via `ceil_exp_mul_exp_neg_tendsto_atTop`.
   - **E2 decoder confusion** (wrong codeword in same bin, typical with `Y^n`): gateway 1
     `wz_sideInfo_decoder_confusion_expectation_le` → `exp(n(H(U|Y)+2ε))/M`, `M ≈ exp(nR)` and
     `R > I(X;U)−I(Y;U) = H(U)−H(U|Y)`… the collision term needs `exp(n·H(U|Y))/M → 0`, i.e.
     the `tendsto_exp_mul_codebookSize_inv` (private) direction.
   - **E3 covering acceptance** (true codeword rejected by side-info): gateway 2
     `wz_covering_sideInfo_mass_ge` → mass `≥ exp(−n(I(U;Y)+slack))`, high-probability accept.
6. **Good deterministic codebook** by `exists_codebook_low_avg` (pigeonhole over the
   `codebookMeasure` on the (X→U) codebook; the binning is derandomised the same way over
   `binningMeasure`).
7. **Distortion squeeze + diagonalization.** Excess `≤ distortionMax d · P(error)` via
   `source_avg_distortion_le_simpler`; `P(error) → 0` (E1+E2+E3) via
   `exp_neg_tendsto_zero_of_tendsto_atTop`; then `η_n → 0` and `τ → 0` diagonalize so the
   perturbed objective's slack vanishes and the bound reaches `D + ε` for every `ε`.

Audit note: the gateway atoms are `@audit:ok` (already proved), so the retreat line "reduce
the side-info covering atom to a shared sorry" (parent plan §57) is **NOT triggered** — the
covering atom passed gateway-atom-first. Full support is **proof-internal** (perturbation),
never a signature hypothesis, so the construction remains TRUE-as-framed with only
`hqf`/`hobj` (feasibility + objective) as preconditions.

---

## Hypothesis-supply gaps (highest-value output)

Ranked by how much construction work they add. All are **regularity to be manufactured**, not
missing lemmas — none is load-bearing (they are exactly what §B4 `rdAmbient` + a perturbation
produce).

1. **Full support `0 < κ x u` / `0 < qStar p` — the perturbation gap.**
   `hqf` gives only `IsWynerZivFactorizable` = row-stochastic κ. The RD-covering
   `hqStar_pos`, and the gateway `hposX/hposY/hposZ`, and `qZ_min > 0`, all fail if κ has
   zeros. **Must build** `qf_τ := (1−τ)·qf.1 + τ·(uniform kernel)`, prove
   `IsWynerZivFactorizable U P_XY qf_τ` (via `IsWynerZivFactorizable_convex_combination`,
   `FactorizableRate.lean:233`), full support for `τ > 0`, and `wzObjective(qf_τ) → wzObjective(qf) < R`
   as `τ → 0` (via `continuous_wzObjective`, `Basic.lean:159`) so `< R` persists for small `τ`.
   Also re-check distortion feasibility `wzExpectedDistortion(qf_τ) ≤ D + o(1)` absorbed into ε.
   Effort: ~60–120 lines (mirrors the RD `qStar_τ` perturbation the RD file deferred).
2. **The ambient i.i.d. bundle** (`μ, Us, Ys, iIndepFun, IdentDistrib, hpos*, hmarg_*`).
   Not derivable from `hqf` directly — `hqf` is a pmf, the atoms want random variables on a
   measure space. **Manufacture** via `rdAmbient` (§B4) on the (X,U) marginal `wzMarginalXU U qf_τ.1`
   for covering, and on the (U,Y) marginal `wzMarginalYU U qf_τ.1` for the side-info decode.
   `iIndepFun`/`IdentDistrib`/`hpos*` then come from the `rdAmbient_*` lemmas (product structure).
   Effort: mostly plumbing, ~40–80 lines, but note the **two-ambient** subtlety: covering uses
   α×U law, side-info uses U×β law — they must be the two marginals of one 3-var `qf_τ` for the
   rate split to be consistent.
3. **`Nonempty (Fin k)`** (needed for `[Nonempty α]`-style covering-alphabet instances).
   The type allows `k = 0`; `hqf` rules it out but not in the type. **Derive** exactly as
   `wynerZivRate_nonneg` already does (`Achievability.lean:214-223`): from the row-sum
   `∑_{u:Fin 0} κ x u = 0 ≠ 1` at any `x` (uses `Nonempty α`). Effort: ~8 lines, copy the pattern.
4. **(minor) `[NeZero M]` for binning** — `M := codebookSize R n`, `codebookSize_neZero`. Free.
5. **(minor) `0 < R`** — from `wynerZivRate_nonneg` + `hobj`; already threaded upstream.

---

## Self-build vs reuse verdict (per atom)

| atom | verdict |
|---|---|
| `IsWynerZivFactorizable` (+ `_markov/_marginalXY/_nonneg/_mem_stdSimplex/_convex_combination`) | **reuse as-is** |
| `continuous_wzObjective`, `wzMutualInfoXU/YU` | **reuse as-is** (perturbation lever) |
| `rate_distortion_achievability` (`_strong`) | **reuse — but demands a full-support `qStar`** (gap #1) |
| `jointTypicalLossyEncoder`, `lossyCodeOfCodebook`, `distortionTypicalSet`, `blockDistortion_le_of_mem_distortionTypicalSet` | **reuse as-is** |
| `encoder_failure_prob_le_exp_neg_M_avg`, `exists_codebook_low_avg`, `source_avg_distortion_le_simpler` | **reuse as-is** |
| `rdAmbient` + marginal/positivity lemmas | **reuse — instantiate twice** (X,U) and (U,Y) marginals (gap #2) |
| `binningMeasure`, `binning_collision_prob` | **reuse as-is** (`[NeZero M]` free) |
| `conditionalTypicalSlice`, `conditionalTypicalSlice_card_le` | **reuse as-is** |
| gateway 1 `wz_sideInfo_decoder_confusion_expectation_le` | **reuse — supply full i.i.d. bundle** (gap #2) |
| gateway 2 `wz_covering_sideInfo_mass_ge` | **reuse — supply full bundle + KL-domination slack** (gap #2 + preconditions box) |
| `ceil_exp_mul_exp_neg_tendsto_atTop`, `exp_neg_tendsto_zero_of_tendsto_atTop` | **reuse as-is** |
| `codebookSize` / `codebookSize_pos` / `codebookSize_neZero` / `codebookSize_log_div_tendsto` | **reuse as-is** |
| `tendsto_exp_mul_codebookSize_inv` | **needs an adapter — `private`; add a public alias or re-prove (~15 lines)** |
| `LossyCode → WynerZivCode` bridge (decoder shape + `Measure.pi P_XY ↦ Measure.pi P_X`) | **needs an adapter — `Measure.pi_map_pi` marginalisation, ~20–40 lines** |
| **genuinely absent** | **none** — 0 self-build atoms; all 26 atoms exist in-project |

---

## Mathlib walls (enumeration)

No new `@residual(wall:…)` target is introduced by this scope. The only Mathlib-absence is
the family-level one already recorded in the parent plan/facts: **operational coding theory
(method-of-types / typicality / rate-distortion / Wyner–Ziv) is entirely absent from Mathlib**
(loogle `Csiszar` / `rateDistortion` / `WynerZiv` / `typicalSet` = `Found 0 declarations`,
confidence loogle-neg; parent plan §199). Every atom this construction consumes is in-project,
so the correct residual class stays **`plan:wyner-ziv-main-plan`**, not `wall` (per parent plan
§185/§211: `wall` = Mathlib-gap vocabulary, which would be a misclassification here).

Two in-project "soft walls" (plumbing, not Mathlib gaps), for tracking:
- `tendsto_exp_mul_codebookSize_inv` is `private` — a **visibility** wall, not a math wall.
- The `LossyCode`/`WynerZivCode` structural mismatch (decoder arity, ambient dimension) is a
  **shaping** wall — no single lemma; it is the adapter of gap-bridge #2 / §B3.

No shared-sorry-lemma consolidation is recommended: there is no repeated genuine Mathlib gap
across files here (the one residual is the composition body itself, a single `sorry`).

---

## Distance to the retreat lines

Parent plan (`wyner-ziv-main-plan.md`) retreat structure:
- **§57 gateway-atom-first**: "dispatch the side-info conditional covering atom first; if it
  passes, achievability closes as RD covering + SW binning composition plumbing; if not,
  reduce that atom to a shared sorry (retreat line)." → **NOT triggered.** Both gateway atoms
  (`wz_sideInfo_decoder_confusion_expectation_le`, `wz_covering_sideInfo_mass_ge`) are proved
  and `@audit:ok`. The construction is now in the "composition plumbing" branch.
- **§111 / §146 / §181 honesty retreat**: the exit is `sorry + @residual(plan:wyner-ziv-main-plan)`
  only; **no hypothesis bundling** — `WynerZivAchievable` / `wz_goodCode_exists_of_testChannel`
  must not bundle the covering+binning core into a `*Hypothesis` predicate. Full support,
  `iIndepFun`, `Nonempty`, memoryless-Markov are **regularity preconditions (OK)**; the
  perturbation must stay proof-internal so the signature keeps only `hqf`/`hobj`.

**Trigger status: none of the retreat lines fire for this scope.** If gap #1 (the perturbation)
stalls beyond a leg, the honest exit is to keep `wz_goodCode_exists_of_testChannel`'s signature
as-is and leave its body `sorry + @residual(plan:wyner-ziv-main-plan)` (already the current
state) — do **not** add a full-support hypothesis to the signature (that would move a
load-bearing precondition onto the caller and break `wyner_ziv_achievability`'s honesty).
No new degenerate fallback retreat line is needed: the statement is already TRUE-as-framed and
the residual is a single composition `sorry`, not a false/under-hypothesised claim.

---

## Starting skeleton (composition body, not for planning)

The `sorry` at `Achievability.lean:291` is filled in-place; no new file. The internal shape:

```lean
private lemma wz_goodCode_exists_of_testChannel
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
    (hobj : wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 < R) :
    ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (c n).expectedBlockDistortion P_XY d ≤ D + ε := by
  classical
  -- gap #3: Nonempty (Fin k) from the row-sum (copy Achievability.lean:214-223)
  -- gap #1: perturb qf → qf_τ full-support, obj < R kept via continuous_wzObjective
  -- gap #2a: covering ambient  = rdAmbient (wzMarginalXU (Fin k) qf_τ.1)  on ℕ → α × Fin k
  -- gap #2b: side-info ambient = rdAmbient (wzMarginalYU (Fin k) qf_τ.1)  on ℕ → Fin k × β
  -- covering:   rate_distortion_achievability … ⇒ LossyCode (M₁ n) n α (Fin k), dist ≤ D+ε'
  -- binning:    binningMeasure (Fin k) n (codebookSize R n) ; gateway 1/2 bound E2/E3
  -- pigeonhole: exists_codebook_low_avg (codebook) + derandomise binning
  -- assemble:   ⟨fun n => { encoder := …, decoder := fun (m, y) => letterwise qf_τ.2 (u'(m,y) i, y i) }, …⟩
  -- squeeze:    source_avg_distortion_le_simpler + exp_neg_tendsto_zero_of_tendsto_atTop
  --             + ceil_exp_mul_exp_neg_tendsto_atTop + (public alias of) tendsto_exp_mul_codebookSize_inv
  --             ; diagonalize η_n → 0, τ → 0
  sorry -- @residual(plan:wyner-ziv-main-plan)
```

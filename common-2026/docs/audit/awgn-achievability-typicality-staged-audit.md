# AWGN Typicality Discharge — Independent Staged Honesty Audit (2026-05-24)

> ⚠️ **OBSOLETE — superseded by re-audit (2026-05-24 同日)**。本文書は orchestrator が **bad prompt** (CORE doctrine 未適用、自前 4 条件 framework 発明) で起動した最初の独立監査の output。全 7 件 OK 判定だが、CORE doctrine 「`@audit:staged` の存在を honest 完了の signal と読まない」原則を未適用のため **偽陰性ありの判定**。
>
> 同日に CORE doctrine 適用の **再監査** 実施、verdict は全 7 件 `suspect` (5 件 `load_bearing_hyp` + 2 件 `name_laundering`) に修正。canonical verdict は **コード docstring の `@audit:KIND(SLUG)` タグ** が SoT (`Common2026/Shannon/AWGNAchievabilityDischarge.lean` 内、`@audit:staged(...)` + `@audit:suspect("")` + `@audit:defect(launder)` 各 docstring)。
>
> 本文書は (a) bad prompt → false-positive の実例 (b) docstring 自己評価を trust した場合の偽陰性パターン の方法論的記録として保存。

Subject: 3 `@audit:staged` predicates introduced in commits `fbdf996..924f8be`
(file `Common2026/Shannon/AWGNAchievabilityDischarge.lean`, 1485 lines, silent
`lake env lean` re-verified at audit time).

Auditor: independent — no involvement in the implementation. Read the source
directly and consulted Mathlib via `loogle` rather than trusting docstring claims.

Standard: `CLAUDE.md` 「検証の誠実性」 4 conditions (a)–(d), name-laundering
test, vacuous-truth test, plus `docs/textbook-roadmap.md` 「Mathlib 壁の 4 分類」
(a quantity / (b) analysis / (c) genuine depth / (d) choice-not-wall.

Reference point for the type-independence test:
`InformationTheory.Shannon.AWGN.IsAwgnTypicalityHypothesis P N h_meas`
(`AWGNAchievability.lean:47`, currently carrying
`@audit:defect(circular)` `@audit:defer(awgn-achievability-typicality)`
`@audit:staged(n-dim-gaussian-aep)`). Its conclusion shape is

```
∀ {R} (0 < R) (R < C), ∀ {ε} (0 < ε),
  ∃ N₀, ∀ n ≥ N₀, ∃ (M : ℕ) (_ : ⌈exp(nR)⌉ ≤ M) (c : AwgnCode M n P),
    ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε
```

— i.e. **the existence of an actual `AwgnCode` with explicit per-message error
bound, universally in `R < C` and `ε > 0`.**

## Verdicts

| Predicate | (a) 型独立 | (b) docstring 事実 | (c) genuine consume | (d) tag | Name laundering | Vacuous | 壁分類 | 総合 |
|---|---|---|---|---|---|---|---|---|
| `IsContinuousAEPGaussian` | ✓ | ✓ | ✓ | ✓ | none | none | (a)+(b) | **OK** |
| `IsAwgnRandomCodingBound` | ✓ | partial | ✓ | ✓ | none | minor | (b) | **OK** (with one wart) |
| `IsAwgnPowerConstraintRealizable` | ✓ | partial | ✓ | ✓ | none | none | (a)/(b) (docstring overshoots to (d)) | **OK** (with one wart) |

Cross-cutting: the 3 hypotheses are **orthogonal analytic facts** (AEP-set
existence vs. random-coding integral bound vs. SLLN-style power concentration).
Combining them in `isAwgnTypicalityHypothesis` requires ~600 lines of genuine
plumbing (rate inflation `R'' = (R+C)/2`, doubling for `2 · ⌈exp(nR)⌉ ≤ ⌈exp(nR'')⌉`,
sum-and-barrier integrand, Markov contradiction for power-OK extraction, monotone
reindex via `Finset.orderEmbOfFin`, sub-decoder ⊆ full-decoder inclusion). **NOT
name laundering.**

No `Prop := True` placeholders, no `:= h` circularity, no `sorry`. Three honest,
load-bearing-but-orthogonal staged hypotheses with correct `@audit:staged` tags.

Net assessment: **the AWGN typicality discharge is honest**. It reduces the
original `@audit:defect(circular)` `IsAwgnTypicalityHypothesis` to 3 hypotheses
whose individual types are genuinely different from the conclusion type, and the
glue between them is non-trivial real work, not name laundering. The audit
recommends transitioning the original `IsAwgnTypicalityHypothesis` tag from
`defect(circular)` to `defer(awgn-achievability-typicality)` once an orchestrator
wires `awgn_achievability_F1_discharged` as the canonical entry point, since the
new code path no longer has the type-≡-conclusion defect.

## Per-predicate analysis

### `IsContinuousAEPGaussian P N`

Signature (file `AWGNAchievabilityDischarge.lean:140-171`):

```
def IsContinuousAEPGaussian (P : ℝ) (N : ℝ≥0) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
    ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
      MeasurableSet A
      ∧ ⟨joint codebook+noise law⟩(A) ≥ ENNReal.ofReal (1 - ε)
      ∧ volume A ≤ ENNReal.ofReal (Real.exp (n * (klDiv ... .toReal + ε)))
      ∧ ⟨independent-pair product law⟩(A) ≤ ENNReal.ofReal (Real.exp (-n * (klDiv ... .toReal - 3ε)))
```

**(a) 型独立**: ✓. The predicate quantifies over `(ε, n)` and returns existence
of a typical *set* `A` together with three measure inequalities. It does not
mention `AwgnCode`, `errorProbAt`, or universal `R < C` quantification over
codes. Completely different shape from `IsAwgnTypicalityHypothesis`.

**(b) docstring 事実**: ✓. Claims "Mathlib gap = continuous SMB +
n-d differentialEntropy". Verified via loogle:
- `loogle "ShannonMcMillanBreiman", "MeasureTheory.Measure.pi"` — n-d/continuous
  SMB: not present. (Mathlib has discrete `ShannonMcMillanBreiman` in
  `SMBAlgoetCover.lean` per common2026's own code, but not for continuous
  product measures.)
- `loogle "differentialEntropy", "MeasureTheory.Measure.pi"` → 0 declarations.
  n-dim differentialEntropy is genuinely absent from Mathlib.
- `loogle "jointTypical"` → 0 declarations. Confirms no AEP / joint-typicality
  infrastructure exists.

The "NOT load-bearing for AWGN achievability core" claim is also accurate in the
**relative** sense: the achievability *plumbing* (codebook, decoder, union
bound, expurgation, AwgnCode extraction) is genuinely done in the rest of the
file. But this predicate *is* load-bearing in the standard-B sense — without it
the achievability theorem is not proven. The docstring is slightly elliptical
here but `@audit:staged` already captures the residual status.

**(c) genuine consume**: ✓. In `isAwgnTypicalityHypothesis`
(`AWGNAchievabilityDischarge.lean:898-984`):
- Line 899: `obtain ⟨N_aep, hN_aep⟩ := h_aep hε_rand_pos` — extract N₀.
- Line 985: `obtain ⟨A, hA_meas, _hA_prob, _hA_vol, _hA_indep⟩ := hN_aep hn_aep`
  — extracts the typical set `A` and its measurability `hA_meas`.

`hA_meas` is then routed into `jointTypicalDecoder_measurable` (decoder
measurability), `jointTypicalDecoder_joint_measurable` (joint
`(c, y)`-measurability), and `awgn_extract_AwgnCode` (downstream Pe bound).
Note: the three other AEP bounds `_hA_prob`, `_hA_vol`, `_hA_indep` are **dropped
with `_` placeholders** in the current discharge body. They are nominally
"consumed" via destructuring but the integral chain leading to `2ε` per-message
average error bound is supplied by `h_rand` (the next predicate) rather than
re-derived from `hA_prob/hA_vol/hA_indep`. This is **honest**: those three
bounds are precisely what `IsAwgnRandomCodingBound` packages at a higher level
of abstraction (already-evaluated integral), so re-deriving them here would be
the missing ~150-300 lines that Phase C-3' defers.

The mild oddity: `IsContinuousAEPGaussian` packages *both* the existence of `A`
and the 3 bounds on it; the current consumer only uses the existence + measurability
of `A`. The bound conjuncts are dead weight in the current discharge. This is
not a honesty defect — it just means the predicate is somewhat over-engineered
relative to what the current `isAwgnTypicalityHypothesis` body needs. The Phase
C-3' discharge of `IsAwgnRandomCodingBound` is the natural consumer of those
bound conjuncts.

**(d) tag**: ✓. `@audit:staged(continuous-aep-gaussian)` at line 139.

**Name laundering risk**: none. The predicate is not a renaming of the
conclusion; it is a packaging of three classical AEP bounds. The "NOT
load-bearing for the achievability core" phrasing is mildly misleading (it *is*
load-bearing for standard B) but is correctly clarified by the `@audit:staged`
tag.

**Vacuous risk**: none. The predicate is non-vacuous as written — for ε close
to 0, the conjunction of the three bounds (probability ≥ 1-ε, volume bound,
independent-pair upper) is genuinely restrictive on `A`. There is no degenerate
set that makes all three bounds trivially hold (the volume bound *upper*-bounds
A's Lebesgue measure while the probability bound *lower*-bounds its measure
under the joint law, so A cannot be empty for small ε).

**Wall classification**: docstring claims "Mathlib gap (continuous SMB / n-d
differentialEntropy)". This is mostly **(a) 量の壁 + (b) 解析の壁** mixed:
- continuous AEP for Gaussian channels is well-understood probability with
  pieces already in Mathlib (Gaussian product measures, KL divergence between
  Gaussians via Common2026's `klDiv_gaussianReal_gaussianReal_eq`,
  `strong_law_ae_real`); the missing piece is bundling them into a joint
  typicality statement at the level Cover-Thomas uses.
- n-dim `differentialEntropy` requires `differentialEntropy` for `Measure.pi` to
  be defined and proven equal to the sum (entropy chain rule for independent
  components). That bundling is missing from Mathlib but is well-defined
  upstream work, not a deep theorem.

Estimated discharge: hundreds of lines combining `strong_law_ae_real` per
coordinate + union bound across `m` + KL/volume identities for Gaussian
product measures. **Not (c) genuine depth, not (d) choice.**

### `IsAwgnRandomCodingBound P N h_meas`

Signature (file `AWGNAchievabilityDischarge.lean:543-557`):

```
def IsAwgnRandomCodingBound (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃R : ℝ⦄, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
    ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n → ∀ ⦃M : ℕ⦄ (hM_pos : 0 < M),
      M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) →
      ∀ ⦃A : Set ((Fin n → ℝ) × (Fin n → ℝ))⦄, MeasurableSet A →
        haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
        ∀ m : Fin M,
          ∫⁻ codebook : Fin M → Fin n → ℝ,
            ⟨channel measure⟩(errorEvent ⟨Code with jointTypicalDecoder A⟩ m)
          ∂(gaussianCodebook M n P.toNNReal)
            ≤ ENNReal.ofReal (2 * ε)
```

**(a) 型独立**: ✓. The conclusion is an **`∫⁻`-integral bound over the random
codebook law**, NOT an `∃ AwgnCode … ∀ m, errorProb < ε` statement. No
`AwgnCode` mentioned; no concrete deterministic codebook extracted. The
quantifier signature does mirror the conclusion's `(R, ε, n, M)` layer, which is
the principal source of unease, but the conclusion clause itself is
fundamentally different: it bounds the *average* (over random codebooks)
ENNReal-valued error probability — a measure-theoretic intermediate object —
rather than constructing a deterministic code with explicit `< ε` ℝ-valued bound.

**(b) docstring 事実**: partial ✓.
- "NOT a complete discharge, Phase C-3 staged hypothesis" → ✓ honest framing.
- "~150-300 lines of probability manipulation" → ✓ plausible; the chain is
  Fubini + IndepFun + AEP-bounds-(i)-(iii) applied to channel output, with the
  three coordinate parts independently estimated.
- Listed pieces (a) Fubini between gaussianCodebook and channel measure, (b)
  IndepFun across codewords (Phase A done), (c) AEP bounds from `h_aep` — all
  three are real pieces of the textbook Cover-Thomas 9.2 argument. ✓.

The docstring is honest about the fact that this predicate carries *real
analytical content* and is not just an abstract slot.

**(c) genuine consume**: ✓. In `isAwgnTypicalityHypothesis`:
- Line 900: `obtain ⟨N_rand, hN_rand⟩ := h_rand hε_rand_pos hR''_pos hR''_lt_C`
  — extract N₀ at the inflated rate `R'' = (R+C)/2`.
- Lines 988-997: builds `h_per_m`, a per-`m` instantiation of `hN_rand` giving
  the per-message integral bound `≤ ENNReal.ofReal (2 * ε_rand)`.
- Lines 1087-1103: builds `h_int_sum`, summing those per-`m` bounds across
  `m ∈ Fin M` to get `∫⁻ c, ∑ m, Pe c m ∂μ ≤ M · 2ε_rand`. This sum-over-m
  step uses `lintegral_finsetSum'` and is genuine — `h_rand`'s output (the
  per-m bound) is consumed inside a finite sum and not in a degenerate slot.
- Lines 1146-1159: the resulting bound feeds into
  `awgn_exists_codebook_le_avg` (D-1 extraction).

So the consumption chain is: `h_rand` → per-m bound → ∑_m bound → c_full
extraction → expurgated subcodebook → AwgnCode. Each step is non-trivial.

**(d) tag**: ✓. `@audit:staged(awgn-random-coding-bound)` at line 542.

**Name laundering risk**: none. While the quantifier signature `∀ R, ε →
∃ N₀, ∀ n ≥ N₀, …` matches the conclusion's outer layer, the *conclusion clause*
is structurally different (integral bound, not code existence). The body of
`isAwgnTypicalityHypothesis` does genuine work (rate inflation, doubling,
sum-and-barrier, contradiction-based extraction) on top of `h_rand`'s output.
Were the predicate's conclusion `∀ m, ∃ AwgnCode, ∀ m, errorProb < ε` (i.e.,
matching `IsAwgnTypicalityHypothesis` shape with rebrand), it would be
laundering — but it is not.

**Vacuous risk**: one minor wart, not a defect.
- The predicate does not require `AEMeasurable Pe` of the integrand. In
  Mathlib, `∫⁻` is defined for arbitrary `f` via the sup of simple-function
  lower-approximations and can give pathological values for non-measurable f.
  However, since `Pe c m ≤ 1` pointwise (a probability), the integral against
  the probability measure `gaussianCodebook` is bounded by 1 regardless of
  measurability. So the predicate is non-vacuously meaningful for `2ε ≤ 1`.
- The natural `Pe c m` *is* measurable in `c` (proven via the three private
  helpers `jointTypicalDecoder_joint_measurable`, `awgnCodebookKernel`,
  `Kernel.measurable_kernel_prodMk_left` in lines 339-497), so in practice this
  is not a concern. But a strengthened predicate would add an `AEMeasurable Pe`
  conjunct for the user, removing any pathological-measurability ambiguity.
- For `ε > 1/2`, the predicate becomes trivial (`∫⁻ Pe ≤ 1 ≤ 2ε`), but this is
  not a defect — `IsAwgnTypicalityHypothesis` proper is also trivial at `ε > 1`
  (anything below probability 1 satisfies it). The non-trivial regime is small
  ε, where the bound is genuine.

**Wall classification**: docstring claims **(b) 解析の壁, ~150-300 lines**.
Verified plausible:
- Fubini between gaussianCodebook (Phase A construction) and channel measure:
  uses `Measure.lintegral_prod` family; this is standard infrastructure
  available in Mathlib.
- IndepFun across codewords: already proven in Phase A
  (`gaussianCodebook_indepFun_codewords`, lines 79-93).
- AEP bounds (i) and (iii) applied to channel output: requires conditioning the
  joint codebook+noise law of `IsContinuousAEPGaussian` on a fixed codebook
  marginal — this is real measure-theoretic manipulation but in well-charted
  Mathlib territory.

So **(b) is plausible**. Not (c) genuine depth (no PDE / Fourier / spectral
theory needed), not (d) choice.

### `IsAwgnPowerConstraintRealizable P N`

Signature (file `AWGNAchievabilityDischarge.lean:720-728`):

```
def IsAwgnPowerConstraintRealizable (P : ℝ) (N : ℝ≥0) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃R : ℝ⦄, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
    ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n → ∀ ⦃M : ℕ⦄ (_hM_pos : 0 < M),
      M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) →
      (gaussianCodebook M n P.toNNReal)
          {c : Fin M → Fin n → ℝ | ∀ m, (∑ i, (c m i)^2) ≤ (n : ℝ) * P}
        ≥ ENNReal.ofReal (1 - ε)
```

**(a) 型独立**: ✓. The conclusion is a **probability mass bound on the
power-constraint-satisfying codebook set** under the random Gaussian codebook
law. No `AwgnCode`, no `errorProbAt`, no decoder. Completely different from
`IsAwgnTypicalityHypothesis`. (The outer `(ε, R, n, M, N₀)` quantification
matches the conclusion, but the *conclusion clause* is a measure-theoretic
mass inequality.)

**(b) docstring 事実**: partial.
- "NOT load-bearing for the AWGN achievability core" → similar caveat as #1:
  the predicate *is* load-bearing in standard-B sense. Adequately covered by
  `@audit:staged` tag.
- "Same Mathlib gap as IsContinuousAEPGaussian (n-d Gaussian SLLN coordinate-
  wise + union bound)" → questionable, see Wall classification below.
- "Classically follows from continuity / margin argument" → ✓ honest framing.

**(c) genuine consume**: ✓. In `isAwgnTypicalityHypothesis`:
- Line 901: `obtain ⟨N_pow, hN_pow⟩ := h_power hε_pow_pos hR''_pos hR''_lt_C`
  — extract N₀.
- Lines 999-1003: builds `h_power_mass`, the power-set mass lower bound at the
  current `(n, M)`.
- Lines 1104-1125: builds `h_int_barrier` via `prob_compl_eq_one_sub` — turns
  the lower bound on `PowSet` into an upper bound on `PowSetᶜ` under the
  codebook law, giving `∫⁻ M · 𝟙_{PowSetᶜ} ≤ M · ofReal(ε_pow)`.
- Lines 1161-1197: the barrier-augmented integrand
  `∑_m Pe + M · 𝟙_{PowSetᶜ}` and the assumption that `c_full` realizes a value
  ≤ `M · 2ε_d2` jointly imply `c_full ∈ PowSet` (otherwise the indicator
  contributes `M`, contradicting `M ≤ M · 2ε_d2 < M`).

So `h_power` is genuinely consumed in a Markov-style contradiction extracting
a power-OK codebook from the random codebook average — not in a degenerate
slot. The barrier construction (lines 1004-1006, "sum-and-barrier integrand")
is real probabilistic plumbing and the contradiction at lines 1163-1193 uses
the `2 * ε_d2 < 1` ENNReal inequality non-trivially.

**(d) tag**: ✓. `@audit:staged(awgn-power-constraint-realizable)` at line 719.

**Name laundering risk**: none. The conclusion is a measure-mass inequality,
not a code-existence statement.

**Vacuous risk**: none. The conclusion `μ(PowSet) ≥ ENNReal.ofReal (1 - ε)`
under the random Gaussian codebook is non-trivial for small `ε` — for `ε close
to 0`, this asks that almost every random codebook satisfies the power
constraint, which is genuinely a fact requiring SLLN-style estimates (the
empirical 2nd moment of n iid `N(0, P)` samples concentrates around `P`, and
union-bound over `M` codewords lets `1 - ε` close to 1).

**Wall classification**: docstring claims **(d) 真の壁 (n-d Gaussian SLLN
gap)**. **This overshoots.** Verified via loogle:
- `loogle "strong_law"` → 12 declarations including
  `ProbabilityTheory.strong_law_ae_real` (1-D real SLLN, in
  `Mathlib.Probability.StrongLaw`).
- The actual gap here is: apply `strong_law_ae_real` to `(c m i)^2` for fixed
  m (these are iid since coordinates are iid `N(0, P)` and `(·)^2` is
  measurable; finite 1st moment = `P` because `E[X^2] = P` for `X ~ N(0, P)`).
  Then convert a.s. convergence to in-probability convergence (Mathlib has
  this), then union bound over `m ∈ Fin M` with `M ≤ ⌈exp(nR)⌉` polynomially
  bounded.

This is a multi-step but well-understood derivation, not a deep theorem. It is
**(a) 量の壁** (well-understood probability, no Mathlib lemma at that exact
shape but composable from existing pieces) or **(b) 解析の壁** if you count
quantitative SLLN (Bernstein / Hoeffding bounds for sums of `X_i^2 - P`) as the
right tool. Either way, **NOT (d)**. The docstring's "(d) 真の壁" claim
overstates the difficulty.

This is a minor honesty wart (wall mis-classification), not a defect. The
predicate itself is correctly staged with `@audit:staged(awgn-power-
constraint-realizable)`, and the discharge effort is plausibly in the
single-session-feasible range (~200-400 lines combining `strong_law_ae_real`
+ in-probability conversion + union bound).

## Cross-cutting findings

### 3-hypothesis combination — name laundering check

The 3 staged hypotheses together let `isAwgnTypicalityHypothesis`
(`AWGNAchievabilityDischarge.lean:865-1439`) construct an `AwgnCode` with
per-message error `< ε`. **Does the combination merely "rebrand" the
conclusion?**

The body's flow:

1. `h_aep` → typical set `A` with `MeasurableSet A`.
2. `h_rand` → integral bound `∫⁻ c, Pe c m ∂μ_cb ≤ 2 ε_rand` per `m` at the
   inflated rate `R'' = (R+C)/2` and codebook size `M = ⌈exp(nR'')⌉`.
3. `h_power` → mass bound `μ_cb(PowSet) ≥ 1 - ε_pow`.

The genuine work (lines 855-1439, ~580 lines):

- **Rate inflation**: pick `R'' = (R+C)/2 ∈ (R, C)` and codebook size
  `M = ⌈exp(nR'')⌉` so that `2 · M_target ≤ M` for large `n` (the
  "doubling" lemma, lines 905-961). This step is needed because expurgation
  throws away half — without inflation, the remaining codebook size would be
  `M_target/2 < M_target`. The inflation lets the discarded half match the
  expurgated half. Real combinatorics, not name laundering.
- **Sum-and-barrier integrand**: combine the per-m random-coding bound
  (`h_rand`) and the power-OK mass bound (`h_power`) into a single integrand
  `g c := ∑_m Pe c m + M · 𝟙_{PowSetᶜ} c`. Lines 1086-1145. This is real
  measure-theoretic plumbing (lintegral additivity, constant-times-indicator
  integral, ENNReal subtraction for `prob_compl_eq_one_sub`).
- **D-1 extraction** (Markov-style): `exists_le_lintegral` gives a codebook
  `c_full` with `g c_full ≤ M · 2 ε_d2`. Lines 1146-1159.
- **Power-OK contradiction**: if `c_full ∉ PowSet`, the indicator term
  contributes `M`, forcing `M ≤ M · 2 ε_d2`, i.e., `1 ≤ 2 ε_d2 < 1` (by
  `hε_d2_lt_half`), contradiction. So `c_full ∈ PowSet`. Lines 1161-1197.
- **D-2 expurgation**: `awgn_expurgate_worst_half` keeps half of the per-m
  errors below `4 ε_d2`. Lines 1227-1230.
- **Monotone reindex**: since `|S| ≥ M_target` (from doubling), pick a strictly
  monotone `Fin M_target ↪o Fin M` and observe that the sub-decoder's tie-break
  on smallest index respects the embedding, so the sub-decoder's error event is
  a *subset* of the full-decoder's. Lines 1238-1406. This is the most subtle
  step — it requires the full proof that `jointTypicalDecoder A subcodebook y =
  reindex j ↔ jointTypicalDecoder A c_full y = reindex j` modulo the case where
  no codebook is typical (where both decoders default to index 0, with a
  separate `reindex 0 < reindex j` contradiction for `j ≠ 0`).
- **D-3 bridge to AwgnCode**: line 1430,
  `awgn_extract_AwgnCode` packages the subcodebook into an `AwgnCode` with
  per-message error `< 5 · ε_d2 = ε₁ ≤ ε`.

**Verdict**: this is **genuine probabilistic plumbing**, not name laundering.
The 3 hypotheses are individually orthogonal (set existence vs. integral bound
vs. mass bound), and the assembly is non-trivial. The discharge path would
fall apart at multiple points if any of the 3 hypotheses were trivially
satisfied or coincided in type with the conclusion.

### Comparison with the original `@audit:defect(circular)`

The original `IsAwgnTypicalityHypothesis` in `AWGNAchievability.lean` is
`@audit:defect(circular)` precisely because its type **is** the conclusion
type — instantiating `awgn_achievability` is `:= h_typicality hR_pos hR hε`,
i.e., one beta-reduction.

The new discharge in `AWGNAchievabilityDischarge.lean` reduces this to 3
hypotheses whose types are **demonstrably different** from the conclusion type
(measure-set existence + integral bound + mass bound). This is a **genuine
improvement** in honesty: the new path no longer has the type-≡-conclusion
defect. The remaining residual is honestly three staged-analytic facts.

Once the orchestrator wires `awgn_achievability_F1_discharged` (lines
1442-1455) as the canonical entry point, the original
`@audit:defect(circular)` can be transitioned to `@audit:defer(awgn-
achievability-typicality)` since the defect has been retired by construction.

### Minor warts (not defects)

1. **`IsAwgnRandomCodingBound` lacks an explicit `AEMeasurable Pe` premise.**
   In Mathlib's modern `lintegral`, this is not strictly necessary (integral
   defined via sup of simple functions ≤ f a.e., bounded by 1 since Pe is a
   probability), but adding it would make the predicate's intended meaning
   sharper for non-pathological readers. Optional refinement.

2. **`IsAwgnPowerConstraintRealizable` docstring claims wall classification
   "(d) 真の壁".** This overstates difficulty. The discharge path is
   `strong_law_ae_real` on `(c m i)^2` + a.s.-to-in-probability conversion +
   union bound over `m` — well-understood probability composable from existing
   Mathlib pieces. More accurate classification: **(a)/(b)**. Recommend
   updating the docstring's wall classification to "(b) 解析の壁 — n-d
   Gaussian SLLN + quantitative concentration, composable from
   `strong_law_ae_real` + Hoeffding-type bounds".

3. **`IsContinuousAEPGaussian` packages three bound conjuncts (i), (ii),
   (iii), but the current discharge only uses (existence of `A` +
   measurability).** The other three bounds are forwarded into the
   destructuring `obtain ⟨A, hA_meas, _hA_prob, _hA_vol, _hA_indep⟩` at line
   985 with `_` placeholders. This is honest (the predicate is over-engineered
   relative to what the current code needs) but suggests that a future
   `IsAwgnRandomCodingBound` discharge will need those three bounds. The
   current factoring assumes the natural Phase C-3' discharge of
   `IsAwgnRandomCodingBound` consumes `_hA_prob, _hA_vol, _hA_indep` — but
   this is an *implicit* dependency, not enforced by signature. Optional
   refinement: have `IsAwgnRandomCodingBound` take `IsContinuousAEPGaussian`
   as a premise so the bound conjuncts are visibly threaded through.

## Recommended actions

- [ ] **(OK)** Record verdict `ok` for the 3 staged predicates in
  `docs/audit/honesty.db` with note "independent staged-honesty audit
  2026-05-24 (auditor: no-implementation-involvement); honest 4-conditions
  satisfied; name-laundering rejected; vacuous-truth rejected".

- [ ] **(questionable, wall mis-classification)** Update
  `IsAwgnPowerConstraintRealizable` docstring (line 689-719 area) to soften
  "(d) 真の壁 (n-d Gaussian SLLN gap)" to "(a)/(b) 量+解析の壁 — `strong_law_
  ae_real` on `(c m i)^2` + a.s.-to-in-probability + union bound over `m`,
  composable from existing Mathlib pieces". Estimated discharge: ~200-400
  lines, not a hard wall.

- [ ] **(questionable, docstring softening)** Clarify
  `IsContinuousAEPGaussian` and `IsAwgnPowerConstraintRealizable` docstrings:
  replace "NOT load-bearing for the AWGN achievability core" with "load-
  bearing in the standard-B sense (residual staged); not part of the
  achievability *plumbing* (codebook, decoder, expurgation), which is
  genuinely discharged". This avoids the optical illusion that these
  hypotheses are "free".

- [ ] **(optional refinement)** Strengthen `IsAwgnRandomCodingBound` by
  adding an `AEMeasurable Pe (gaussianCodebook M n P.toNNReal)` premise (or
  by phrasing the predicate via `Kernel.measurable_kernel_prodMk_left`
  directly). Improves predicate clarity without affecting the current
  discharge.

- [ ] **(orchestrator)** Once `awgn_achievability_F1_discharged` is wired as
  the canonical entry point, transition `IsAwgnTypicalityHypothesis`'s tag in
  `AWGNAchievability.lean:46, 85` from `@audit:defect(circular)` to
  `@audit:defer(awgn-achievability-typicality) @audit:staged(continuous-aep-
  gaussian, awgn-random-coding-bound, awgn-power-constraint-realizable)`. The
  defect is retired by construction.

- [ ] **(orchestrator, Phase C-3')** Schedule discharge of
  `IsAwgnRandomCodingBound` (~150-300 lines, (b) 解析の壁). This is the
  highest-ROI next step among the 3 staged hypotheses.

- [ ] **(orchestrator, Phase D-4)** Schedule discharge of
  `IsAwgnPowerConstraintRealizable` (~200-400 lines, (a)/(b) wall via
  `strong_law_ae_real`). Second-highest ROI.

- [ ] **(orchestrator, long-term)** `IsContinuousAEPGaussian` discharge is
  the largest of the three — requires bundling continuous AEP for joint
  Gaussian product measures, which Mathlib does not have. Estimated 500-1000
  lines. Treat as Tier-3 long-term work.

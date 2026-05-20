# FLAW-VACUOUS review — `Common2026/Shannon/` — 2026-05-20

Read-only deep review hunting for **vacuous proofs**: theorems that type-check and
are "technically correct" while not actually proving their intended mathematical
content. Ranked by IMPACT (headline-affecting first). Severity ∈ {High, Med, Low,
By-design}.

Methodology: confirmed the seed `fisherInfo`-V1 defect, traced the entire EPI/Stam
chain to its headline theorems, and pattern-swept the directory for `Prop := True`
predicates, conclusion-as-hypothesis `:= h` bodies, `exfalso`-on-precondition
vacuity, and trivial-value placeholder defs.

---

## Summary of severity counts

- **High: 2** (clusters) — both in the EPI/Stam chain, driven by the seed `fisherInfo`-V1 defect.
- **Med: 1** — the EPI conclusion-as-hypothesis main theorem (transparently labelled, but the *name* claims Cover-Thomas 17.7.3).
- **Low / By-design: 5+ clusters** — honest, header-documented hypothesis pass-through scaffolding across other chapters (ArithmeticCoding, LZ78, MAC, BC, Relay, …). Not deceptive; flagged for completeness.

---

## HIGH-1 — Vacuous "Gaussian discharge" of the Stam inequality (seed defect, fully confirmed) — **RESOLVED (2026-05-20)**

> **RESOLVED (2026-05-20).** All `*_of_gaussian_fisherInfo_zero` /
> `*_of_fisherInfoReal_zero` / `*_v1_zero` discharges and their chain wrappers
> (`isStamInequalityHyp_of_gaussian_via_step12/_step3/_body[_Y]`,
> `isStamFisherCoupling_of_gaussian_saturation`, `epi_from_degenerate_stam`,
> `isEPIL3IntegratedPipeline_gaussian`) were **removed**. They proved the Stam
> predicates only by `exfalso`-ing the `0 < J_X` precondition against the buggy
> V1 `fisherInfo = 0` value. Nothing genuine depended on them: the genuine
> Gaussian EPI runs through `entropy_power_inequality_gaussian_saturation`, and
> the non-vacuous V2 Gaussian convex Fisher bound is
> `FisherInfoV2.stam_convex_fisher_bound_gaussian`. V1 `fisherInfo` itself is now
> carrying a `⚠️ BUGGED` deprecation docstring (kept only as the type-level
> scaffold of the genuine *open* Stam/de Bruijn predicates; no honest result uses
> its value).


**Files / declarations:**
- `Common2026/Shannon/EPIStamStep12Body.lean:327` `isStamCondExpCSHyp_of_gaussian_fisherInfo_zero`
- `Common2026/Shannon/EPIStamStep3Body.lean:271` `isStamTotalExpectation_of_gaussian_fisherInfo_zero`
- `Common2026/Shannon/EPIStamInequalityBody.lean:307` `isStamCauchySchwarzOptimal_of_gaussian_fisherInfo_zero` (and the `IsStamInequalityHyp` form at :327)
- `Common2026/Shannon/EPIStamDischarge.lean:277` `isStamInequalityHyp_of_fisherInfoReal_zero`; :132 `isStamInequalityHyp_of_fisher_info_zero`
- `Common2026/Shannon/EPIL3Integration.lean:410` `isStamInequalityHyp_of_gaussian_v1_zero`

**Why flaw-vacuous.** The published Stam predicates are all guarded by a positivity
precondition on the V1 Fisher information, e.g.
`IsStamInequalityHyp` (`EPIStamDischarge.lean:121`):

```
∀ J_X J_Y J_sum, 0 < J_X → 0 < J_Y → 0 < J_sum →
  J_X = (fisherInfo (P.map X)).toReal → … → 1/J_sum ≥ 1/J_X + 1/J_Y
```

Every `*_of_gaussian_fisherInfo_zero` proof body is literally `intro …; exfalso;
rw [hX_zero] …; linarith` — it discharges the predicate by **contradicting the
`0 < J_X` precondition** using the supplied fact `(fisherInfo (P.map X)).toReal = 0`.
For a Gaussian law, V1 `fisherInfo` does indeed collapse to `0` (the
`Classical.choose` Lebesgue-decomposition representative is non-differentiable
a.e., so `logDeriv = 0` a.e. — documented at `FisherInfoGaussian.lean:302-327`,
"`fisherInfo (gaussianReal m v) = 0` … not provable [as 1/v]"). So the Stam
inequality is "discharged" for Gaussians **for no informative reason**: it asserts
nothing about Stam actually holding. The Stam optimum bound `1/J(X+Y) ≥ 1/J(X)+1/J(Y)`
is never established for any genuine Fisher information.

This is corroborated *in the codebase itself*: `StamGaussianBound.lean:11-17`
explicitly states `isStamCondExpCSHyp_of_gaussian_fisherInfo_zero` is "vacuous …
It asserts nothing about Stam actually holding for Gaussians," and supplies a
separate **non-vacuous** V2-keyed bound (`stam_convex_fisher_bound_gaussian`,
`StamGaussianBound.lean:83`) using `fisherInfoOfMeasureV2 = 1/v`. **But that
genuine V2 bound is never wired into the headline Stam/EPI chain** — the chain
keeps consuming V1 `fisherInfo`.

**IMPACT (High).** Makes every "Gaussian discharge" of the Stam inequality
misleading. The genuine V2 fix exists (`fisherInfoOfDensity (gaussianPDFReal m v)
= 1/v`, `FisherInfoV2.lean:296`) but is deliberately not connected, so the
project's *only* Stam-inequality discharge path is the vacuous one. Honestly
*named* (`_fisherInfo_zero`) and documented, which limits the deception, but the
theorems are presented as the Gaussian instance of a real result.

---

## HIGH-2 — `entropy_power_inequality_gaussian_via_stamDeBruijn`: name claims a Stam+de Bruijn derivation that is vacuous — **RESOLVED (2026-05-20)**

> **RESOLVED (2026-05-20).** `entropy_power_inequality_gaussian_via_stamDeBruijn`
> and its pipeline witness `isEPIStamDeBruijnPipeline_of_gaussian` were
> **removed** (the Stam half was discharged vacuously via the V1-zero artefact, so
> the Stam/de Bruijn machinery was non-load-bearing). No genuine result is lost:
> the honest Gaussian EPI is `entropy_power_inequality_gaussian_full'`
> (`EPIStamDeBruijnConclusion.lean`, direct from
> `entropy_power_inequality_gaussian_saturation`, no Stam mention).


**File / declaration:** `Common2026/Shannon/EPIStamDeBruijnConclusion.lean:269`
`entropy_power_inequality_gaussian_via_stamDeBruijn` (and its pipeline witness
`isEPIStamDeBruijnPipeline_of_gaussian:255`).

**Why flaw-vacuous.** The theorem is named/presented as deriving Gaussian EPI
"via Stam + de Bruijn". In reality:
1. its `totalExp` (Stam total-expectation) field is discharged **vacuously** via
   `isStamTotalExpectation_of_gaussian_fisherInfo_zero` (HIGH-1, the V1-zero
   `exfalso` route — line 264);
2. the actual inequality comes **entirely** from `isStamToEPIBridgeHyp_of_gaussian`
   → `entropy_power_inequality_gaussian_saturation` (the genuine Gaussian
   closed-form equality `2πe(v₁+v₂) = 2πe v₁ + 2πe v₂`). The Stam/de Bruijn
   primitives play **no load-bearing role** in the conclusion;
3. it requires the caller to supply `hX_v1_zero : (fisherInfo (P.map X)).toReal = 0`
   — a value with no clean in-repo lemma and that is itself the known V1 bug.

Crucially, the "bridge" predicate is *definitionally* the conclusion:
`IsStamToEPIBridgeHyp X Y P` unfolds (`isStamToEPIBridgeHyp_iff_implication`,
`EPIStamToBridge.lean:585`, `:= Iff.rfl`) to
`IsStamInequalityHyp X Y P → IsEntropyPowerInequalityHypothesis X Y P`, and
`IsEntropyPowerInequalityHypothesis` (`EntropyPowerInequality.lean:168`) **is** the
EPI inequality. The non-Gaussian discharge of the bridge
(`isStamToEPIScalingHyp_of_epi`, `EPIStamToBridge.lean:384`) simply *feeds the EPI
conclusion back in*. So "EPI via Stam" reduces to "EPI given EPI" everywhere
except the Gaussian-saturation special case, where the Stam half is vacuous.

**IMPACT (High).** A reader citing `*_via_stamDeBruijn` would believe the EPI was
obtained through the Stam-inequality / de Bruijn-integration machinery (the actual
Cover-Thomas 17.7 proof). It was not. The only genuine content is the Gaussian
saturation *equality*, which is already and honestly available as
`entropy_power_inequality_gaussian_full'` (`:285`) and
`entropy_power_inequality_gaussian_saturation` with no Stam mention.

---

## MED-1 — `entropy_power_inequality` main theorem is conclusion-as-hypothesis (L-EPI3)

**File / declaration:** `Common2026/Shannon/EntropyPowerInequality.lean:188`
`entropy_power_inequality` (Cover-Thomas Theorem 17.7.3).

**Why flaw-vacuous.** Body is `:= h_epi`. The hypothesis
`h_epi : IsEntropyPowerInequalityHypothesis X Y P` is **definitionally the EPI
conclusion** (`:168-171`, an unfolded `≥`). The two companion hypotheses
`_h_stam : IsStamInequalityHypothesis` and `_h_debruijn : IsDeBruijnIntegrationHypothesis`
are `Prop := True` placeholders (`:139`, `:153`) — passed but unused. So the
"theorem" `entropy_power_inequality` proves the EPI inequality *given the EPI
inequality*, with two decorative `True` arguments.

**IMPACT (Med).** The header (`:26-46`, `:183-187`) is fully transparent that this
is "L-EPI1+L-EPI2+L-EPI3 hypothesis pass-through" and the body is `:= h_epi`.
That transparency keeps it from being deceptive *to a careful reader of the
source*. But the **theorem name is the headline Cover-Thomas result**, so a
downstream `#check`/citation by name alone is misleading: nothing of EPI is proved.
Rated Med (not High) only because the same file proves the genuine Gaussian
saturation case unconditionally (`:226`). All the `entropy_power_inequality_*`
variants (exp/log/normalized/3-arg/4-arg/integrated/scaling-decomposed) inherit
this and are the same By-design pass-through in different clothing.

---

## LOW / BY-DESIGN — honest, header-documented hypothesis pass-through scaffolding

These are transparently labelled signature placeholders, each with a header
stating "hypothesis pass-through form" and naming the (unwritten) discharge plan.
They are *not* presented as genuine results in their docstrings. Listed for
completeness; none should be "fixed" beyond eventually discharging them.

- **ArithmeticCoding.lean** — `IsCumulativeTruncationPassthrough` (:157),
  `IsArithmeticPrefixFreePassthrough` (:176), `IsArithmeticExpectedLengthPassthrough`
  (:201) are `Prop := True`. Headline `arithmetic_coding_expected_length_bounds`
  (:249) returns `:= h_bound` (the `H ≤ E[L] ≤ H+2` conclusion supplied as a
  hypothesis); `arithmetic_coding_prefix_free` (:265) and
  `arithmetic_coding_unique_decodable` (:276) likewise `:= h_pf_real` / `:= h_ud`.
  By-design (header `:222-248` is explicit). Note `c : ArithmeticCode` length is a
  free field, so nothing ties results to the actual arithmetic-coding construction.
- **LempelZiv78.lean** — `IsZivInequalityPassthrough` (:223),
  `IsLZ78ConversePassthrough` (:250), `IsSMBSandwichPassthrough` (:276) are
  `Prop := True`. `lz78_asymptotic_optimality` (:409) takes `lz78EncodingLength`
  as an **arbitrary parameter** and returns `:= h_rate_bound`; similarly
  `lz78_achievability_upper_bound` (:312) `:= h_upper`,
  `lz78_converse_lower_bound` (:345) `:= h_lower`. Proves nothing about LZ78
  specifically. By-design (header `:377-408`).
- **EPIStamDischarge.lean** — `IsFisherInfoSumHyp` (:96), and the bridge
  `IsStamInequalityHypothesis`/`IsDeBruijnIntegrationHypothesis` re-exports are
  `True`. By-design, but feed the HIGH-1/HIGH-2 chain.
- **MAC / BroadcastChannel / Relay / Wyner-Ziv / RateDistortion / SeparationTheorem /
  AWGN / BrunnMinkowski / Chernoff converse** — dozens of
  `theorem …_capacity_region_… / _bound / _inner_bound / _outer_bound / _formula`
  with one-line `:= h…` bodies over conclusion-as-hypothesis `Prop` predicates
  (e.g. `bc_capacity_region_inner_bound`, `mac_sum_rate_bound`,
  `relay_cutset_outer_bound`, `parallel_gaussian_capacity_formula`,
  `prekopa_leindler_inequality`, `brunn_minkowski_entropy_inequality`,
  `sanov_ldp_upper_bound`). Each header documents the pass-through. By-design.
  (Spot-check note: `chernoff_converse_discharged`, `ChernoffConverse.lean:400`,
  is **genuinely better** — it consumes a real analytic per-tilt lower-bound
  hypothesis and derives the converse through actual lemmas, not `:= h`. Honest
  Low.)

---

## Patterns checked that came up CLEAN

- **Pattern 5 (trivial-value placeholder defs `:= 0/∅/fun _ => 0` used downstream
  as meaningful):** none found in `Common2026/Shannon/`.
- **Pattern 4 (contradictory/`False`-style vacuous hypotheses outside the Stam
  chain):** the only `exfalso`-on-precondition vacuity is the HIGH-1 cluster. All
  other `exfalso` uses (SlepianWolfFullRateRegion, SMBChainRule, LZ78GreedyParsing,
  HoeffdingMinimizerAttainment) are legitimate proof-by-contradiction case splits,
  not vacuous-hypothesis exploits.
- **V2 Fisher info (`FisherInfoV2.lean`, `FisherInfoV2DeBruijn.lean`,
  `StamGaussianBound.lean`):** the V2 line is **correct and non-vacuous**
  (`fisherInfoOfDensity (gaussianPDFReal m v) = 1/v`; Gaussian de Bruijn
  `1/(2(v+t))`). The defect is purely that it is *not wired into the headline EPI
  chain* (HIGH-1/HIGH-2), which still runs on V1.

---

## Bottom line

The directory's headline theorems are pervasively "hypothesis pass-through," but
that style is transparently documented and is mostly By-design. The genuinely
**flaw-vacuous** material — proofs whose discharge secretly relies on a quantity
being `0`/`⊥` — is confined to the **EPI/Stam chain** and is caused by the seed
V1 `fisherInfo` definitional bug. The two High findings are the vacuous "Gaussian
Stam discharge" family (HIGH-1) and the misleadingly-named
`entropy_power_inequality_gaussian_via_stamDeBruijn` (HIGH-2). The correct V2
Fisher information exists in-tree but is never connected to these.

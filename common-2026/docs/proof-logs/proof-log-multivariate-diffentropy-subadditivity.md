# proof-log — multivariate-diffentropy-subadditivity (Phase 1-2)

date: 2026-05-25
agent: lean-implementer (parallel worktree)
parent plan: `docs/shannon/multivariate-diffentropy-subadditivity-plan.md`
touched file: `Common2026/Shannon/MultivariateDiffEntropy.lean`

## summary of landing state

| Phase | result |
|---|---|
| 0 — inventory + slug verify | ✅ 4 suspect tags already on correct slug (no rewrite needed); Mathlib API confirmed (`prod_withDensity` `WithDensity.lean:712`, `rnDeriv_withDensity₀` `Lebesgue.lean:583`, `rnDeriv_mul_rnDeriv` `RadonNikodym.lean:402`) |
| 1 — 2-variable genuine discharge | ✅ `_v2` versions publish honest-hyp-free, original tagged `@audit:superseded-by(<v2>)` |
| 2 — n-variable genuine discharge | ❌ withdrawn (reshape friction, plan §"撤退条件" path), residual `@audit:suspect(multivariate-diffentropy-subadditivity-plan)` retained |
| 3 — AWGN plan-side reflection | ✅ `rg` confirmed L32 / L117 in `AWGNAchievabilityDischarge.lean` are prose, not tags |
| V — slug update + clean | ✅ `lake env lean` silent, 0 sorry / 0 warning, 4 tags re-classified into 2 `superseded-by(<v2>)` (2-variable, discharged) + 2 `suspect(multivariate-diffentropy-subadditivity-plan)` (n-variable, residual) |

## Phase 1 — 2-variable Bayes density split discharge

### Approach taken (matches plan §1.1–§1.5 verbatim)

1. **`prod_marginals_eq_volume_withDensity`** (~20 lines): Rewrite each marginal `μX` as `vol.withDensity (μX.rnDeriv vol)` via `Measure.withDensity_rnDeriv_eq` (from `h_fst_ac : μX ≪ vol`), then fuse via `prod_withDensity₀ : (μ.withDensity f).prod (ν.withDensity g) = (μ.prod ν).withDensity (z ↦ f z.1 * g z.2)`, and identify `vol.prod vol = (vol : Measure (ℝ × ℝ))` via `Measure.volume_eq_prod` (rfl).

2. **`llr_split_from_density_factorize`** (~80 lines): Set `ρ := μX.prod μY`, `g z := μX.rnDeriv vol z.1 * μY.rnDeriv vol z.2`.
   - Chain rule (a.e.[vol]): `μ.rnDeriv ρ z * ρ.rnDeriv vol z = μ.rnDeriv vol z` via `Measure.rnDeriv_mul_rnDeriv h_joint_ac`.
   - Identify `ρ.rnDeriv vol =ᵐ[vol] g` via `Measure.rnDeriv_withDensity₀` applied to the `prod_marginals_eq_volume_withDensity` equation.
   - Combine → `μ.rnDeriv ρ z * g z =ᵐ[vol] μ.rnDeriv vol z`, then pull to `=ᵐ[μ]` via `(μ ≪ vol).ae_le`.
   - For each z satisfying 6 a.e. conditions (`μ.rnDeriv ρ z ≠ 0, ≠ ∞`, `μ.rnDeriv vol z ≠ 0, ≠ ∞`, `μX.rnDeriv vol z.1 ≠ 0, ≠ ∞`, `μY.rnDeriv vol z.2 ≠ 0, ≠ ∞`): take `toReal` (via `ENNReal.toReal_mul`), then `log` (via `Real.log_mul` with positivity).
   - Marginal positivity transfer: `μX(rnDeriv = 0) = 0` (from `rnDeriv_pos h_fst_ac`), pulled to `μ({z | μX.rnDeriv vol z.1 = 0}) = 0` via `ae_map_iff` with `measurable_fst.aemeasurable`. Similar for finiteness and for μY.

3. **`klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2`** + **`jointDifferentialEntropy_le_sum_v2`** (~10 lines each): Just plug `llr_split_from_density_factorize` into the existing honest-hyp versions, removing the `h_llr_split` argument. The remaining honest hyps (5 integrability conditions) are regularity (Bochner) and conservative.

### lemma misses / corrections during build

- `MeasureTheory.Measure.ae_map_iff` → actually in `MeasureTheory` (root namespace via `Measure.lean`); had to drop the `Measure.` qualifier. **1 build cycle**.
- `measurable_set_eq_fun` → camelCase `measurableSet_eq_fun` (Mathlib style). **1 build cycle**.

### honest hyp inventory after Phase 1

The `_v2` 2-variable versions take 8 honest hyps:
- 3 `AbsolutelyContinuous`: `h_fst_ac`, `h_snd_ac`, `h_joint_ac` (regularity — fundamentally about which measures the bridge applies to)
- 5 `Integrable`: `h_int_fst`, `h_int_snd`, `h_int_joint`, `h_int_fst_marg`, `h_int_snd_marg` (Bochner regularity — log-density integrability against joint + marginal)

**Removed**: `h_llr_split` (~3-line Bayes density split equation), which was the **single suspect** (= load-bearing-on-Mathlib-fact, not regularity) honest hyp. All remaining hyps are regularity (not algebraic content of the claim), matching the 1-D differentialEntropy bound's hyp style.

## Phase 2 — n-variable case (withdrawal)

### Approach attempted (case A: 2-variable induction)

Followed plan §2.1–§2.2 + §2.3 (case A first, fall back to case B if needed).

Code sketched ~250 lines:
- `pi_marginals_eq_volume_withDensity` by `Nat.rec` on n: base `n=0` via Subsingleton; step `n+1` via `MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0` + `measurePreserving_piFinSuccAbove` + IH + `prod_withDensity₀`.
- `llr_split_from_density_factorize_pi`: parallel to 2-variable, with `Finset.prod` + `Real.log_prod`.

### Frictions hit (in priority order)

1. **`withDensity_one` vs `withDensity (fun _ => 1)`** in the `n=0` base case. The lemma `Measure.withDensity_one` matches against literal `(1 : α → ℝ≥0∞)` not `(fun _ => 1)`. Fixable with `withDensity_const 1` or by working around. **Minor**.

2. **`volume : Measure (Fin n → ℝ)` vs `Measure.pi (fun _ => volume)`**. The two are equal via `volume_pi`, but they're not definitionally identical in all surface forms. Inserting `volume_pi` rewrites at the right points is fiddly. **Medium**.

3. **`piFinSuccAbove 0` vs `piFinSuccAbove (Fin.last n)` orientation** for the inductive step. `Fin.succAbove 0 j = j.succ`, but `Fin.succAbove (Fin.last n) j = j.castSucc`. The IH builds a "rest" indexed by `j.succ`, but the conclusion index runs over `Fin (n+1)` via `Fin.prod_univ_succ`. Both formulations work, but choosing the wrong one creates intractable mismatches. **Medium**.

4. **Change-of-variables for `withDensity` under measurable equivalences**. Mathlib has `MeasurableEmbedding.map_withDensity_rnDeriv` (specialized to `rnDeriv` densities), but not a generic `(μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm)` for arbitrary measurable density `g`. The generic version *is* provable in ~10 lines via `Measure.ext` + `MeasurableEquiv.lintegral_map`, but it's another helper to write. **Major** (the missing lemma is the single biggest blocker).

5. **`Finset.aemeasurable_prod` signature mismatch** — Lean wants `(fun i => ...).Measurable`, not `i.Measurable`. Fixable but adds wiring. **Minor**.

Estimated remaining work to land case A genuinely: another 2–3 turns to debug all 5 frictions, totaling >250 lines. Per plan §"撤退条件 — Phase 2 案 A / 案 B 双方で行き詰まる (>250 行) → n 変数のみ honest hyp 温存", withdrew.

### What was kept

- Original `klDiv_pi_marginals_toReal_eq_sum_sub_joint` + `jointDifferentialEntropyPi_le_sum` unchanged, tagged `@audit:suspect(multivariate-diffentropy-subadditivity-plan)` (this plan's slug = correct residual SoT).
- Phase 2 docstring withdrawal note added in the file explaining the genuine direction tried + the missing Mathlib piece (generic `withDensity_map`), so a future session can pick up.

## Phase 3 — AWGN plan-side reflection

`rg -nB1 'differential-entropy-plan' Common2026/Shannon/AWGNAchievabilityDischarge.lean` confirmed:
- L31–32: prose docstring referencing `@audit:suspect(differential-entropy-plan)` in an *explanatory* narrative ("Option β goes through the suspect tag X; Option γ avoids it").
- L116–117: similar prose narrative.

Neither is a Lean `@audit:` tag (no closing `... -/` association with a declaration's docstring). Per plan §"L32 / L117 散文引用の再確認", no Edit needed. The `IsContinuousAEPGaussian` predicate (`AWGNAchievabilityDischarge.lean:140`, `@audit:staged(continuous-aep-gaussian)`) remains staged — Mathlib wall = continuous SMB, out of scope for this plan.

## Phase V — slug update + clean

After Phase 1 success + Phase 2 withdrawal:

- 2-variable wrappers (`klDiv_prod_marginals_toReal_eq_sum_sub_joint` L90, `jointDifferentialEntropy_le_sum` L176): retagged `@audit:suspect(multivariate-diffentropy-subadditivity-plan)` → `@audit:superseded-by(<v2-name>)`. Audit vocabulary `docs/audit/audit-tags.md:24` matches exactly: "後続版 (typically `_unconditional` 版) が既に存在している旧 declaration の残置 ... typically `_of_condEntDiff` 等の conditional 版が unconditional 版に置き換えられた後の history record".
- n-variable wrappers (`klDiv_pi_marginals_toReal_eq_sum_sub_joint` L215, `jointDifferentialEntropyPi_le_sum` L280): kept `@audit:suspect(multivariate-diffentropy-subadditivity-plan)` (residual discharge target).
- File header docstring "Honesty status" section rewritten to reflect the Phase 1 / Phase 2 split, with explicit pointer to `_v2` successors and the `pi_withDensity` Mathlib gap as the n-variable blocker.

Final `@audit:` grep:
```
108:`@audit:superseded-by(klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2)` -/
198:`@audit:superseded-by(jointDifferentialEntropy_le_sum_v2)` -/
237:`@audit:suspect(multivariate-diffentropy-subadditivity-plan)` -/
302:`@audit:suspect(multivariate-diffentropy-subadditivity-plan)` -/
```
(Lines 41 / 51 / 586 are docstring narrative references to tag names, not standalone tags.)

`lake env lean Common2026/Shannon/MultivariateDiffEntropy.lean` → silent (0 error, 0 sorry, 0 warning).

## meta — observations for the plan family

- **Mathlib gap surfaced**: generic `(μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm)` for `e : α ≃ᵐ β` measurable equivalence. Mathlib has the rnDeriv-specialized form (`MeasurableEmbedding.map_withDensity_rnDeriv`) but not the universal one. This is the **single highest-leverage Mathlib helper** to upstream for n-variable subadditivity to close cleanly. Candidate PR title: `Measure.map_withDensity` (or `MeasurableEquiv.map_withDensity`).
- **Phase 2 case A vs case B was not the critical choice** — both routes would hit the same generic-`withDensity_map` gap eventually. The plan's case-B-as-fallback labeling slightly misanalyses the blocker; the real gap is one level lower than `pi_withDensity` itself.

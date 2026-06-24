# proof-log — EPI case-1 G3 Phase 3b (§3 squeeze genuine closure)

対象: `InformationTheory/Shannon/EPICase1RatioLimit.lean` §3
`entropyPower_rescaled_path_tendsto` を 0 sorry に閉じ、波及で §4
`csiszarLogRatioGap_tendsto_zero_atTop` も transitively sorryAx-free に保った。

## deliverable

- §3 own body: 0 sorry (`#print axioms` = `[propext, Classical.choice, Quot.sound]`)。
- §4: transitively sorryAx-free (§3 が閉じたため)。
- file 全体: 実 `sorry` tactic トークン 0、`@residual` 0、deprecated タグ 0。
- §1/§2 の既存 `@audit:ok` は未編集。

## squeeze の質的観察

1. **両 envelope を genuine lemma から導出 (core bundling 回避)**。下界は
   `differentialEntropy_add_ge_of_indep` を `X := B, Y := A/√t` で適用 →
   `h(B) ≤ h(B + A/√t)`、`B + A/√t = A/√t + B` の funext rewrite で path を揃え、
   `entropyPower_le_of_differentialEntropy_le` で N に持ち上げ。上界は
   `differentialEntropy_le_gaussian_of_variance_le` を `μ := P.map(A/√t+B)`,
   `m := ∫ x ∂μ`, `v := (varA/t + v_B).toNNReal` で適用 →
   `h(μ) ≤ (1/2)log(2πe·v_t)`、`entropyPower_gaussianReal` で
   `N(μ) ≤ 2πe·v_t = N(𝒩 0 v_t)` に lift。**envelope 不等式自体は hypothesis に
   渡していない** (regularity precondition のみ渡し、不等式は body で genuine 導出)。

2. **honest signature 設計の肝 = `IsRescaledPathRegular` abbrev (regularity 束)**。
   §3 の 10-conjunct (下界 fibre integrability) + 4-conjunct (上界 max-ent data) を
   1 つの `def IsRescaledPathRegular A B P varA v_B : Prop` に束ねた。これにより §4 が
   3 path 分を `h_reg_X/Y/S` として透過 thread できる (型を 3 回 spell out せずに済む)。
   この束は IndepFun / a.c. / condDistrib fibre integrability / 平均+分散上界+integrability
   のみで、結論 `Tendsto … N(B)` も envelope 不等式も含まないので **NOT load-bearing**。

3. **`varA` を real regularity datum として thread**。上界 envelope を
   `varBound t := varA/t + v_B` と explicit にし、`varA/t → 0` から
   `varBound t → v_B = N(B)/(2πe)` を genuine 証明 (`Tendsto.const_div_atTop` +
   `tendsto_const_nhds` + `const_mul`)。convergence を hypothesis に渡さず body で
   計算 = core bundling 回避。下界は定数 `N(B)` (const tendsto)、squeeze は
   `tendsto_of_tendsto_of_tendsto_of_le_of_le'` (eventual 版、bound は t>0 でのみ成立)。

4. **`IndepFun B (A/√t)` の扱い**: brief は `IndepFun A B` から `IndepFun.comp`/symm で
   導出する想定だったが、本実装では per-t `IndepFun B (A/√t)` を
   `IsRescaledPathRegular` の field として **直接 thread** (regularity precondition)。
   discharge phase で `IndepFun A B` + `IndepFun.comp` (`A/√t` は `A` の可測関数) +
   `IndepFun.symm` から供給する想定。本 task では thread に留める (honest)。

## 詰まり / 後戻り

- **synthInstanceFailed (condDistrib)**: `def IsRescaledPathRegular` に
  `[IsProbabilityMeasure P]` を付け忘れて `condDistrib` の instance 合成が 9 箇所失敗。
  binder 追加で解決。bare `def` は囲む theorem の instance context を継承しないので、
  condDistrib を含む Prop def は instance binder を明示する必要がある。
- それ以外は LSP 第 1 戻りでほぼ通過 (skeleton → 下界 → 上界 の順で 1 個ずつ埋め、
  各 fill が一発で通った)。

## 使用 lemma

`differentialEntropy_add_ge_of_indep` (EPIUncondMixedCase:76)、
`differentialEntropy_le_gaussian_of_variance_le` (DifferentialEntropy:520)、
`entropyPower_gaussianReal` / `entropyPower_le_of_differentialEntropy_le` (EPIPlumbing)、
`differentialEntropy_gaussianReal`、`tendsto_of_tendsto_of_tendsto_of_le_of_le'`
(Mathlib Topology.Order.Basic)、`Filter.Tendsto.const_div_atTop`、
`Real.coe_toNNReal` / `Real.toNNReal_eq_zero`。

## 在庫メモ

- `IndepFun.variance_add` / `variance_smul` は loogle で実在確認したが、本実装では
  分散計算を直接行わず `varA/t + v_B` を threaded variance bound として受けたため未使用。
  discharge phase で `Var(A/√t + B) = Var A/t + v_B` を組むときに使う見込み
  (`IndepFun.variance_add` は `MemLp A 2 P` / `MemLp B 2 P` を要求、`variance_smul`
  は `variance (c • X) = c²·variance X`、`A/√t = (1/√t)•A`)。

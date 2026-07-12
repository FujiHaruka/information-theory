# WynerZiv settled-facts ledger

再導出が高コストな事実のみ記録。sorry 数 / axiom status / decl 存在は **キャッシュしない**
(`#print axioms` / `scripts/sig_view.ts --sorry` / `rg` で都度)。confidence = `machine` /
`loogle-neg` / `human-judgment`。

| claim | confidence | re-verification command | last-verified (commit) | notes |
|---|---|---|---|---|
| `condDistrib` + `Measure.pi` の product-measure disintegration は Mathlib 不在 | loogle-neg | `loogle "ProbabilityTheory.condDistrib, MeasureTheory.Measure.pi"` | `d5e5d8fa` | 実装者機械確認。**ただし Markov-core の critical path に無い** — piece (a) は有限 Fubini で回避 (下記行)。general machinery を探した 0-hit は正しいが off-path |
| `typicalSet` + `condDistrib` の conditional-AEP typical-set concentration は Mathlib 不在 | loogle-neg | `loogle "InformationTheory.Shannon.typicalSet, ProbabilityTheory.condDistrib"` | `d5e5d8fa` | 実装者機械確認。conditional AEP は in-project self-build 必須 (Atom B) |
| `Measure.pi (fun _ ↦ pmfToMeasure Src)` の block-event mass は有限和 `∑_{block} ∏_i Src(block i)` に展開でき、`Src=P_X·P(y\|x)` の x-block factor-out は有限 Fubini (`Measure.pi_pi` + `pmfToMeasure_apply_singleton` + `Fintype.sum_prod_type`) で済む | machine | Read `ChannelCoding/ShannonTheorem.lean:55` (pmfToMeasure atomic) + `rg "Measure.pi_pi" InformationTheory/` (in-tree 多用) | `d5e5d8fa` | piece (a) が general disintegration を回避する根拠。finite-vs-general 解決の核 |
| `IndepFun.variance_sum` は **IdentDistrib を要求しない** (pairwise 独立 + MemLp のみ) ⟹ 非-ident 独立和の分散分解が使える | machine | Read `AEP/Rate.lean:149` (`rw [IndepFun.variance_sum ...]`、hident 非依存) | `d5e5d8fa` | piece (b) conditional Chebyshev が feasible な根拠。固定 x-block 上で `y_i` 独立・非-ident |
| `aep_chebyshev_bound` (`AEP/Rate.lean:108`) は `hident : IdentDistrib` を必須前提とする ⟹ 非-ident conditional 和に drop-in 不可、self-build 要 | machine | Read `AEP/Rate.lean:112` (署名の `hident` 引数) | `d5e5d8fa` | Atom B を self-build する理由 (plain AEP は非適用) |
| in-tree 唯一の conditional-slice asset `conditionalStronglyTypicalSlice_mass_ge` (`ConditionalMethodOfTypes/Mass.lean:1274`) は **独立-product Ys 法則上の LOWER bound** (`_mass_ge`) | machine | Read `Mass.lean:1274` (結論 `exp(...) ≤ (Measure.pi (μ.map (Ys 0))).real (...)`、独立-product、下界) | `d5e5d8fa` | wrong direction + wrong measure ゆえ Atom B の drop-in 不可、ingredient 止まり |
| `wz_covering_jointBand_concentration` (L5302、outer) は proved、`_markov_core` (L5246) を consume (L5462) | machine | `scripts/sig_view.ts --sorry InformationTheory/Shannon/WynerZiv/Achievability.lean` (core のみ sorry) | `d5e5d8fa` | Markov chain の isolated sorry は `_markov_core` 単独。再導出容易ゆえ将来はキャッシュ参照せず sig_view で確認 |

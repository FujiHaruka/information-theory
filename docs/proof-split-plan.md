# 長大証明の分割プラン（1 証明 ≤ 200 行 目安）

`docs/rules/lean-style.md`（2026-07-19 追記: 1 証明本体 200 行以内 目安）に反する 16 宣言を、証明本体内の `have` / `let` ブロックを `private` 補助補題へ切り出して 200 行以下に収める。

## Context

ファイル分割（1500 行超）は 2026-07-19 に解消済（1500 行超 0）。一段下の粒度として、単一宣言の証明本体が突出して長いものが残る。計測（`scratchpad/decl_len.ts`: decl 開始 → 次 decl / セクション境界までの行数）で 200 行超が 16 件。

## Approach

**have ブロック → private 補助補題の切り出し**（headline の signature は不変、証明本体のみリファクタ）。

- **behavior-preserving**: 対象宣言の**型（statement）は一切変えない**。証明本体の自己完結した `have h : P := by …` 塊を `private lemma <name>_aux… (<その時点の local context>) : P := by …` へ持ち上げ、元の箇所を補題適用（`have h : P := <name>_aux… <args>`）に置換。
- **honesty 不変**: 補助補題は P を**証明する**（P を仮定に持つ load-bearing hyp ではない）。プロジェクトは全 sorry-free なので新 sorry は入らない。→ honesty gate は原則不要（新 sorry / @residual / honesty 変更 signature が出た場合のみ）。
- **補助補題は bare private**: internal supporting lemma。docstring 不要、名前に意味を持たせる（naming.md）。可能なら補助補題自身も < 200 行。
- **local context の捕捉**: `have` が参照する file-level `variable` / section 仮定 / それまでの `have` を過不足なく引数化する。ここが唯一の技術リスク。
- **検証**: `lake env lean <file>` 0 error + `#print axioms <headline>` が分割前と不変（sorryAx-free 保持）。
- **gate**: 新規 private 補助補題（decl 追加）につき `style-auditor` を触ったファイルへ。honesty gate は上記のとおり原則スキップ。
- **粒度**: 1 ディスパッチ = 1 ファイル（同一ファイル複数対象はまとめる）。**同時 1 体**（orchestrator パターン）。

## 対象バッチ（14 ファイル / 16 宣言、行数降順）

| # | ファイル | 対象宣言（行数） | 状態 |
|---|---|---|---|
| 1 | `WynerZiv/Achievability/ChosenWord.lean` | `wz_covering_lossyCode_joint_exists` (431) | TODO |
| 2 | `WynerZiv/Achievability/MassBound.lean` | `wz_exists_binning_E2_bound` (357), `wz_source_codeword_sideInfo_mass_le` (332) | TODO |
| 3 | `WynerZiv/Converse/SingleLetter.lean` | `wz_singleletter_rate_le` (324) | TODO |
| 4 | `ShannonHartley/Main.lean` | `exists_testFn_family` (278) | TODO |
| 5 | `WynerZiv/Converse/Headline.lean` | `wz_support_reduce` (273) | TODO |
| 6 | `BroadcastChannel/Converse.lean` | `bc_input_singleletterize` (259) | TODO |
| 7 | `ConditionalMethodOfTypes/Mass.lean` | `conditional_KL_concentration_ge` (249), `conditionalStronglyTypicalSlice_mass_ge` (210) | TODO |
| 8 | `AWGN/AchievabilityTypicalDecoder.lean` | `awgn_random_coding_union_bound` (245) | TODO |
| 9 | `EPI/G2/ConvEntropyDensity.lean` | `negMulLog_convDensity_entropy_ge_density` (243), `convJointLlr_integrable` (230) | TODO |
| 10 | `SMB/AlgoetCover/TwoSidedRatio.lean` | `integral_MRatioLowerZ_le_one` (240) | TODO |
| 11 | `WynerZiv/Achievability/Concentration.lean` | `wz_covering_uyBand_condSlice_le` (230) | TODO |
| 12 | `EPI/Case1/SmoothingLimit.lean` | `entropy_power_inequality_of_density_explicit` (230) | TODO |
| 13 | `RateDistortion/AchievabilityStrongTypicality/FailureTendstoZero.lean` | `codebookAvgFailureStrong_tendsto_zero` (225) | TODO |

境界（任意）: `entropyPower_smoothed_epi_perT` (SmoothingLimit.lean, 200 ちょうど) は目安と同値なので #12 のついでに対応可、単独では見送り。

## 注意

- 対象は `private` のことが多い（headline ではなく中間補題）。分割で新規 private を増やすが、file-scoped private のままでよい（同一ファイル内）。
- WynerZiv 系が多い（1,2,3,5,11）が、いずれも別ファイルなので順序自由。

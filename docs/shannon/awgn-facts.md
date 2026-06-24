# AWGN family — settled-facts ledger

> family `awgn` の確定事実の**単一の真実源**。フォーマット規約 → `CLAUDE.md`「Plan / docs hygiene」。
> 列 = claim / confidence / 再検証コマンド / last-verified (commit) / notes。
> confidence: `machine` (axiom/sorry 機械検証、再検証コマンド必須) / `loogle-neg` (Found 0、query 併記) / `human-judgment` (解析的壁/overturn 判断、低信頼、独立 pivot で再確認)。
> プラン散文に settled fact をキャッシュせず、ここにリンクする (re-derive > cache)。

## 達成 (proof-done / sorryAx-free — キャッシュでなく再導出レシピ)

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| `awgn_converse` (`AWGN/Converse.lean`) は **完全 transitively sorryAx-free** | machine | `#print axioms InformationTheory.Shannon.AWGN.awgn_converse` (= `[propext, Classical.choice, Quot.sound]`) + `lake env lean InformationTheory/Shannon/AWGN/Converse.lean` (silent) | `61b32e6` | converse の 3 Mathlib 壁すべて genuine closure 後の到達状態。Cover-Thomas 9.1.2 converse の headline |
| achievability **continuous-AEP 集中エンジン** `pi_empirical_mean_concentration` / `pi_empirical_mean_typical_mass` (`AWGN/AchievabilityAEP.lean`) sorryAx-free | machine | `#print axioms InformationTheory.Shannon.AWGN.pi_empirical_mean_concentration` (= `[propext, Classical.choice, Quot.sound]`) + `lake env lean InformationTheory/Shannon/AWGN/AchievabilityAEP.lean` (silent) | `(本セッション)` | **Wall 1 false-wall overturn の gateway atom**。inventory axis2 の T-2 判断は「SLLN (a.s. 収束=無限積測度) で 200-400 行 → 撤退」だったが、**AEP 質量集中には Chebyshev 弱法則 (有限 n、無限積不要) で十分**。`variance_sum_pi` + `meas_ge_le_variance_div_sq` で組成。inventory はこの経路を見落としていた。abstract (一般 μ + L² 統計量 φ) ゆえ Wall 1 (ii)(iii)・Wall 3 にも再利用可 |
| achievability **Wall 3 (D3) per-codeword power 制約** `awgnPowerConstraintPerCodeword_holds` (`AWGN/Walls.lean:370`) sorryAx-free | machine | `#print axioms InformationTheory.Shannon.AWGN.awgnPowerConstraintPerCodeword_holds` (= `[propext, Classical.choice, Quot.sound]`) + `lake env lean InformationTheory/Shannon/AWGN/Walls.lean` (silent) | `e4587aa` | per-codeword 形 `∀m, mass{c | n·P_target < ∑ᵢ(c m i)²} ≤ ε`。engine φ=x² (MemLp 4次モーメント素直、`memLp_id_gaussianReal' 4`) + per-codeword marginal 同定 (`measurePreserving_eval`) + variance 同定で genuine。**slack form = `(P_cb.toNNReal:ℝ) < P_target`** (分散値ベースが honest、D4 で `awgnPowerWitness_exists` の `0<P'<P` から導出)。旧 false `∀m`-mass `awgnPowerConstraintHonest_holds` の honest 後継 (D4 で retire 済)。 |
| achievability **stack 全体 (解析核) sorryAx-free**: `continuousAepGaussian_holds` (Wall 1 縮小) + `awgn_random_coding_union_bound` (D2 union bound) + `awgnPowerConstraintPerCodeword_holds` (D3) + consumer `isAwgnTypicalityHypothesis` | machine | `#print axioms InformationTheory.Shannon.AWGN.continuousAepGaussian_holds` / 同 `awgn_random_coding_union_bound` / 同 `isAwgnTypicalityHypothesis` (= `[propext, Classical.choice, Quot.sound]`) + `lake env lean InformationTheory/Shannon/AWGN/Walls.lean` + `…/AchievabilityDischarge.lean` (silent) | `c44be72` | deep atoms 5 件 (`hφ_memLp` / (iii) change-of-measure / term1 / term2 / N₀ pin) + degenerate corner すべて閉鎖した到達状態。achievability 解析核が genuine。`AWGN/Walls.lean` + `AchievabilityDischarge.lean` の active `@residual` (実 sorry token) は 0 (`rg` 確認)。旧 wrapper 2 本のうち `awgn_achievability_F1_via_staged_hyps` は headline discharge により削除 (superseded、git 履歴)、`awgn_theorem_F4_discharged_F1_via_staged` は F1Discharge.lean へ移設後 2026-06-12 物理削除 (headline supersede、git 履歴) |
| **headline `awgn_achievability` (`AWGN/Achievability.lean`) + `awgn_channel_coding_theorem` (`AWGN/Main.lean`) sorryAx-free — AWGN family 実 sorry 全閉鎖** | machine | `#print axioms InformationTheory.Shannon.AWGN.awgn_achievability` / 同 `awgn_channel_coding_theorem` (= `[propext, Classical.choice, Quot.sound]`) + `lake env lean InformationTheory/Shannon/AWGN/Achievability.lean` (silent) | `c44be72` | import 反転 wiring (`AchievabilityDischarge` の上流 import 3 本除去 → `Achievability` が Discharge を import、headline body = `isAwgnTypicalityHypothesis` 直呼び)。`@residual(plan:awgn-achievability-typicality-plan)` 解消。独立 honesty 監査 all OK (`cb1af3c`)。残る AWGN 壁は X-input kernel-measurability gap のみ (残存壁テーブル)。dead `h_mi_bridge` hyp は 2026-06-12 cleanup (`e728ebf`) で主定理 chain 4 decl の signature から除去 (6 decl `#print axioms` 再検証 + 独立監査 all OK)。superseded だった重複 achievability wrapper 5 decl (`awgn_theorem_F4_discharged_F1_via_staged` / `awgn_theorem_F2_discharged` / `awgn_theorem_of_F2F3_hypotheses` + dead bindconv chain `awgn_theorem_of_typicality_converse_bindconv(_discharged)`) を 2026-06-12 物理削除 (headline `awgn_achievability` が完全 supersede、削除後 full build green + headline 3 本 sorryAx-free 維持。capacity chain `awgn_capacity_closed_form_genuine` は LIVE のため不可触) |
| achievability **bridge ① 共有 lemma 2 本** `klDiv_perLetter_eq_capacity` (`AWGN/Walls.lean:465`、前提 `0<P` / `(N:ℝ)≠0`) + `klDiv_nFold_eq_nsmul` (`AWGN/Walls.lean:649` 付近、無条件) sorryAx-free | machine | `#print axioms InformationTheory.Shannon.AWGN.klDiv_perLetter_eq_capacity` / 同 `klDiv_nFold_eq_nsmul` (= `[propext, Classical.choice, Quot.sound]`) | `2036bfa` | D1 (iii) の klDiv 積分解の核。1a = per-letter KL = `(1/2)log(1+P/N)` (capacity 閉形式)、1b = `klDiv(J_n,Q_n).toReal = n·klDiv(J₁,Q₁).toReal`。G-1 import cycle (Walls→MIClosedForm→ContChannelMIDecomp→Walls) を compProd 経路 (`klDiv_compProd_const_toReal_integral` + `klDiv_gaussianReal_gaussianReal_eq`) + `import InformationTheory.Shannon.CondKLIntegral` で回避 |

## 壁 false-wall overturn (human-judgment overturn — 記録価値大)

3 壁とも当初 Mathlib 壁と判断されたが、独立 pivot で false-wall と判明し genuine closure。overturn の論理を 1 行ずつ残す (同型の overturn を他家系で再利用するため)。

| 壁 (slug) | overturn の論理 (覆した route) | 後継 decl (genuine) | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|---|
| `awgn-mi-bridge` (per-letter MI = h(Y_i) − h(noise)) | mixture→compProd 因子分解 + generic continuous-channel MI chain rule asset (上流 relocate 済) + 混合 log-density 可積分性 + fibre entropy 平行移動不変 | `awgn_per_letter_mi_bridge_genuine` (`AWGN/Converse.lean:549`、`@audit:ok`) | `#print axioms InformationTheory.Shannon.AWGN.awgn_per_letter_mi_bridge_genuine` | `61b32e6` | commit `9d5edf1` + 監査 `34e58e7` |
| `multivariate-mi` (I(W;Y^n)/I(X^n;Y^n) finiteness) | ENNReal chain rule 循環は **Real-form を経由した場合の話**で、直接 `klDiv_ne_top` (discrete-input compProd chain rule) で回避 | `awgnConverseJoint_pair_mi_ne_top` (`AWGN/ConverseDischarge.lean:933`、`@audit:ok`) | `rg '@audit:ok' InformationTheory/Shannon/AWGN/ConverseDischarge.lean` (該当 private lemma が genuine) | `61b32e6` | commit `0b71235` + 監査 `a6dc973` |
| `awgn-continuous-mi-chain-rule` (I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)) | chain rule は **X-input 連続 kernel measurability が真の gap** だが、**W-input route (離散 Fin M)** で kernel measurability を自由化 (決定的 DPI) して回避 | `awgnContinuousMIChainRule_holds` (`AWGN/Walls.lean:2074`、`@audit:ok`) | `#print axioms InformationTheory.Shannon.AWGN.awgnContinuousMIChainRule_holds` | `61b32e6` | gateway atom = generic n-D MI 分解 `mutualInfoOfChannel_toReal_eq_log_density_sub` (`ChannelCoding/MIDecomp.lean:457`)。commit `b95e788`〜`534f884` + 監査 `61b32e6`。`hN` / `NeZero M` は regularity precondition (監査確認) |

## 残存壁 (未解消、コード `@residual` が SoT)

| 壁 (slug / 定義) | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| X-input kernel measurability gap (`Measure.pi (gaussian (x i) N)` の x 可測性、`IsParallelGaussianKernelMeasurable`) | loogle-neg | `loogle "MeasureTheory.Measure.pi, Measurable"` → 5 hits (lintegral/marginal 系のみ、parallel Gaussian kernel の x-measurability は該当 0) | `61b32e6` | `ParallelGaussian/Basic.lean:84` で deferred (`IsParallelGaussianKernelMeasurable` hyp 形)。chain-rule の X-input route はこれに当たるため **W-input route (離散 Fin M) で回避済** (converse は無影響)。真の Mathlib gap。**Wall 2 の codebook-kernel 可測性とは別物** (後者は location-varying でなく `awgnCodebookKernel` で discharge 済) |

> **achievability 3 壁 (Wall 1/2/3) は壁でなく statement-fix/削除と確定** (M0、2026-06-12)。残存壁
> テーブルから除外し、下記「achievability decomposition の確定 (D1-D4)」に移管。3 壁の旧 `@residual(wall:…)`
> はいずれも閉じる壁を指さなかった (D1=(ii)削除 + (iii) statement-fix /D2=false lemma retire/D3=per-codeword
> 再 state)。**全 deep atom 閉鎖後、achievability 解析核は sorryAx-free** (達成テーブル参照、code SoT)。
> **本 line 全体での false-statement 発見は計 6 件** (Wall1 (ii)/(iii) = 2 件 / D2 union-bound term2
> under-hypothesized = #5 (Fix B 解消) / degenerate corner abs 規約 = #6 (Fix #6 解消)、下記 false-statement
> 台帳参照)。

## achievability decomposition の確定 (D1-D4、2026-06-12、M0 で feasible 確定)

「achievability 3 壁に挑戦」した結果、**3 壁すべてが hard な Mathlib gap ではなく、staged
migration で検証されなかった足場であり、個別に false/mis-stated** と判明した (converse の
false-wall overturn の逆向き = 「壁と思ったら statement が偽だった」)。M0 で **正しい
true-statement 集合 (D1-D4) を 2 subagent の独立検証により feasible 確定** (NO-GO なし)。

- **D1 — Wall 1 `continuousAepGaussian_holds`**: ∃可測A + **2 bounds のみ** ((i)mass + (iii)indep-pair)
  に縮小。**(ii) volume bound は削除** — consumer が破棄済 + union bound 第2項 mass は (iii) が担当
  (volume counting とは別軸) ゆえ load-bearing でない。false klDiv-to-volume を削除で honest 化。
  `jointDifferentialEntropyPi` 系資産は achievability 不要化 (converse 側資産)。
  **【訂正 (Phase 1 実装、commit eab36aa)】M0 の「(iii) は sound」は stale (実装時に監査が指摘)**:
  (iii) indep-pair も **false-statement だった** — 旧指数 `−n·(klDiv_n−3ε)` が n を二重計上
  `−n²I+3nε` になっており、**4 件目の false-statement**。正しい形 `exp(−n(I−3ε))` に statement-fix 済。
  consumer 非消費の bound は downstream の型圧不在で scaling error が生存し続けた。
  **【閉鎖 (commits 2036bfa→ce9d1bf)】bridge ① 2 本 (達成テーブル) で (iii) を klDiv 積分解 + G-2 tensorize
  change-of-measure + 退化 `hkl0` で closure、deep atom `hφ_memLp` も 1-D Gaussian 密度比への因子化 (f_X
  相殺) で genuine。`continuousAepGaussian_holds` は sorryAx-free (code SoT = `Walls.lean`、`@audit:ok`)。**
- **D2 — Wall 2 `awgnRandomCodingBound_holds` は壁でなく false lemma**: **retire 済 (削除、commit b6d0089)**。
  genuine union-bound lemma **`awgn_random_coding_union_bound` (`AchievabilityDischarge.lean`)** を新設、
  decoder = `jointTypicalDecoder A` 固定、AEP output (i)(iii) を hyp に thread (modular composition、
  Wall1 conjunct と逐語一致の bare measure 不等式、load-bearing bundle 非該当)。**kernel 可測性は壁でない**
  (既存 `awgnCodebookKernel` で discharge 済)。
  **【false-statement #5 + Fix B 解消 (2026-06-12、commit b6d0089、honesty 監査 PASS)】** D2 の初版
  union-bound は **under-hypothesized で term2 が false-statement** だった (5 件目): signature が
  `hR: R<I` と `hn: 0<n` のみで `∃N₀` 閾値と rate-slack を欠き、term2 `(M−1)·Q(A) ≤ ε ≈ exp(n(R−I+3ε))`
  が小 n / capacity 近傍 R で偽 (具体反例 P=N=1, R=0.1, ε=0.2(3ε>I), n=1, M=2 で term2=1>ε。直接
  refutation + 独立 proof-pivot-advisor 確定)。**Fix B (typicality slack δ を error 目標 ε と分離)** で
  honest 化: signature を `{ε δ R}` + `hslack: R+3δ<(1/2)log(1+P/N)` + `∃N₀,∀n≥N₀,...` に。`hslack` は
  precondition (consumer が `δ:=(C−R)/12` で自前導出 = bundle でない決定的証拠)。term2 goal は新 sig で
  **真 (closable)**: gap `g:=I−R−3δ>0` から `exp(−ng)→0`。教訓: sub-lemma 切り出しで consumer 側の量化子構造
  (`∃N₀`+rate-slack) を内側に保たないと未消費 bound に型圧がかからず false-statement が生存。
  **【false-statement #6 + 閉鎖 (2026-06-12、commit f69cfea)】** N₀ 閾値 + term1/term2 collapse の残 sorry を
  closure する過程で **degenerate corner (`1+P/N<0`) が 6 件目の false-statement** と判明 (`@audit:defect(false-statement)`
  cd016ec、下記 false-statement 台帳)。`awgn_random_coding_union_bound` に `(hP : 0 < P) (hN : (N:ℝ)≠0)` を追加し
  corner を矛盾 discharge、consumer 2 件 rewire (f69cfea) で **sorryAx-free** に到達 (達成テーブル参照)。
- **D3 — Wall 3 `awgnPowerConstraintHonest_holds`**: `∀m`-mass false 形 → **per-codeword expurgation 形**
  `∀m, mass{c | n·P_target<∑ᵢ(c m i)²}≤ε`、engine を `φ=x²` で適用 (4次モーメント有限、指数 rate 不要)。
  2-stage `Measure.pi` 形維持で Walls.lean に残せる。**genuine 後継 `awgnPowerConstraintPerCodeword_holds`
  (`Walls.lean:370`) を proof-done sorryAx-free で実装済 (commit e4587aa、達成テーブル参照)**。
  旧 false 補題は D4 で retire 済。
- **D4 — consumer restructure (完了、commit b6d0089、honesty 監査 PASS)**: `isAwgnTypicalityHypothesis`
  を新 decomposition に rewire 済。Wall 1 destructure を (i)(iii) 保持に変更、all-or-nothing barrier
  `g c := ∑_m Pe + M·𝟙_{∃m violate}` → per-codeword 合算 `g c := ∑_m (Pe c m + Viol c m)` に再構築、
  worst-half を combined penalty `Comb m := (Pe).toReal + (Viol).toReal` に適用、`h_sub_power` は
  `Comb(reindex j)<1 ⟹ Viol=0 ⟹ ∑≤n·P` で導出。reindex/inclusion 機構は signature 不変で再利用。
  consumer body は 0 sorry (deep atom を transitive 継承、`@audit:ok`→`@residual(plan:)` retract)。
  旧 false `awgnRandomCodingBound_holds`/`awgnPowerConstraintHonest_holds` は削除。wrappers pass-through。
- **achievability 解析核は全 deep atom 閉鎖で sorryAx-free** (code SoT、達成テーブル参照)。Wall 1
  (`continuousAepGaussian_holds`) は (ii)削除 + (iii) statement-fix + change-of-measure/`hφ_memLp` closure
  で genuine (`@audit:ok`)、Wall 2/3 の新 genuine 後継 2 本 (`awgn_random_coding_union_bound` /
  `awgnPowerConstraintPerCodeword_holds`) + consumer `isAwgnTypicalityHypothesis` も sorryAx-free。
  旧 false 補題 (`awgnRandomCodingBound_holds` / `awgnPowerConstraintHonest_holds`) は D4 で削除済。
  headline `awgn_achievability` の最終 wiring も閉鎖済 (import 反転、`c44be72`、達成テーブル参照)。
- **【確定事実 — MemLp 1-D 因子化 insight (deep atom `hφ_memLp`、genuine closure)】** Wall 1 (i) の per-letter
  log-density `φ` の `MemLp φ 2`: `dJ₁/dQ₁ = f_Z(y−x)/f_Y(y)` で **f_X が相殺** するため、φ は
  **1-D Gaussian 密度の比 (log)** に帰着し **2-D Gaussian は不要**。`integrable_density_log_density_of_gaussian`
  風の二次多項式分解で genuine 化 (commit cd5419c、confidence: machine、`#print axioms` は親 `continuousAepGaussian_holds` 経由)。
- 詳細 plan → [`awgn-achievability-walls-discharge-plan.md`](awgn-achievability-walls-discharge-plan.md)
  (**CLOSED**: 「3 壁 discharge」→「decomposition 再設計」escalation → D1-D4 + deep atoms 全閉鎖、achievability
  解析核 sorryAx-free)。

## false-statement 台帳 (本 line で発見した 6 件、human-judgment overturn — 過小評価系、記録価値大)

achievability 3 補題が staged migration で個別検証されなかった足場であることの現れ。各 false-statement の
反例 witness + cause を 1 行ずつ残す (同型の under-hypothesized signature を他家系で再利用するため)。

| # | 場所 | 偽の核 | 反例 / 解消 | cause | commit |
|---|---|---|---|---|---|
| 1 | Wall 1 (ii) volume bound | `klDiv`-to-`volume` 退化 (無限参照 `volume` の `ν.real univ = 0`) | 削除 (consumer 破棄済 + 第2項 mass は (iii) 担当ゆえ load-bearing でない) | `false-statement` | M0 / eab36aa |
| 2 | Wall 3 旧 `∀m`-form | `∀m`-over-`exp(nR)` の指数 rate over-claim | per-codeword expurgation 形に再 state | `false-statement` | M0 |
| 3 | (旧 typicality plan judgment #3) | 同上 (ii) の前身 | (本 plan で解消) | `false-statement` | — |
| 4 | Wall 1 (iii) indep-pair | 指数 `−n·(klDiv_n−3ε)` が n を二重計上 `−n²I+3nε` | 正しい形 `exp(−n(I−3ε))` に statement-fix | `false-statement` | eab36aa |
| 5 | D2 union-bound term2 | under-hypothesized: `∃N₀` 閾値 + rate-slack 欠落で小 n / capacity 近傍 R で term2 偽 | 反例 P=N=1, R=0.1, ε=0.2(3ε>I), n=1, M=2 で term2=1>ε。Fix B (δ-separation、`hslack: R+3δ<(1/2)log(1+P/N)` + `∃N₀`) で解消 | `signature-drops-constraint` | b6d0089 |
| 6 | D2 union-bound degenerate corner | `Real.log x = log\|x\|` abs 規約で `1+P/N<0` でも `hslack` 充足可 → corner で `J=Q`、`klDiv=0`、decay 消失、term2 偽 | 反例 N=1, P=−3, R=0.1, δ=0.01。Fix #6 (`(hP : 0 < P) (hN : (N:ℝ)≠0)` 追加で corner 矛盾 discharge) で解消、consumer 2 件 rewire | `degenerate-boundary` | f69cfea |

> **教訓 (#5/#6 共通)**: sub-lemma 切り出しで consumer 側の量化子構造 (`∃N₀`+rate-slack) を内側に保たないと
> 未消費 bound に型圧がかからず false-statement が生存する。#6 の abs 規約 corner は **型圧で拾えない** ので、
> hypothesis に positivity guard なしの `Real.log (1 + ·)` が現れたら **負値代入の refutation probe を標準**に
> する (confidence: human-judgment、独立 pivot で再確認)。

## M0 確定事実 (2026-06-12、decomposition 再設計の verbatim 検証、再検証コマンド付き)

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| import 構造に cycle なし: `AchievabilityAEP` (AWGN 依存ゼロ) → `Walls.lean` → `AchievabilityDischarge.lean`、`Walls.lean` に `import ...AchievabilityAEP` 追加可 | human-judgment | `lake env lean InformationTheory/Shannon/AWGN/Walls.lean` (import 追加後 silent) で確認 | `(本セッション)` | D1/D2 配置の前提 (engine を Walls に import、union-bound lemma は kernel/decoder が local な AchievabilityDischarge に新設) |
| `klDiv_pi_eq_sum` (`MIChainRule.lean:249`) / `klDiv_prod_eq_add` (:230) の型クラス前提 = **`IsProbabilityMeasure` のみ** (SigmaFinite/IsFiniteMeasure 不要)、両者 sorryAx-free | machine | `#print axioms InformationTheory.Shannon.klDiv_pi_eq_sum` + 同 `klDiv_prod_eq_add` (= `[propext, Classical.choice, Quot.sound]`) + signature Read で `[...]` 前提確認 | `(本セッション)` | D1 (iii) indep-pair の klDiv 積分解。engine の `IsProbabilityMeasure` 維持要件と整合 |
| `jointDifferentialEntropyPi_pi_eq_sum` (`ParallelGaussian/Converse/Core.lean:145`) 結論形 = heterogeneous `jointDifferentialEntropyPi (Measure.pi μ) = ∑ i, differentialEntropy (μ i)` (i.i.d. 特殊形でない)、sorryAx-free | machine | `#print axioms InformationTheory.Shannon.ParallelGaussian.jointDifferentialEntropyPi_pi_eq_sum` (= `[propext, Classical.choice, Quot.sound]`) | `(本セッション)` | **D1 で (ii) 削除につき achievability では不要化** (converse 側資産)。記録は (ii) 旧 statement-fix の検証履歴 |
| `MemLp φ 2` (per-letter log-density が L²): Mathlib 直接補題なし (`memLp_id_gaussianReal` は id のみ)。in-project `integrable_density_log_density_of_gaussian` (`DifferentialEntropy.lean:86`) の二次多項式分解スタイルで自家製 wiring 要 | loogle-neg | `loogle "MeasureTheory.MemLp, Real.log, MeasureTheory.gaussianReal"` (log-density 直接補題 0) + `rg "integrable_density_log_density_of_gaussian" InformationTheory/` | `(本セッション)` | **Phase 1 (i) の bottleneck**。Wall 3 (D3) の `φ=x²` は4次モーメント有限で素直 |
| 退化境界: `P=0` (Dirac) は `≪volume` を破る、`N=0` は `hv₂≠0` (klDiv closed form) を破る。両方とも既存 precondition (`hN:(N:ℝ)≠0` / `P>0`、`awgnPowerWitness_exists`) で吸収済 | human-judgment | docstring の precondition Read (`hN` / `P>0` / `awgnPowerWitness_exists` の存在) で確認 | `(本セッション)` | degenerate-boundary 過小評価の予防確認。statement は退化境界で死なない |

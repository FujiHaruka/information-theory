# AWGN achievability — 3 shared 壁 discharge + statement-fix サブ計画

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) F-1 (achievability typicality)。
> **Sibling (history)**: [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md) (DONE、3 壁を staged/shared sorry 化した元 plan) / [`awgn-power-constraint-realizable-pivot-plan.md`](awgn-power-constraint-realizable-pivot-plan.md) (judgment #7 = 1 回目の power-constraint pivot)。
> **Facts ledger**: [`awgn-facts.md`](awgn-facts.md) (壁 overturn / 残存壁 / 確定事実の SoT)。
>
> **Status (2026-06-12)**: **CLOSED — achievability stack 全体 proof done / sorryAx-free**。
> deep atoms 5 件 + degenerate 残件すべて閉鎖、3 壁の honest 後継 2 本 + 縮小 Wall 1 が
> genuine、consumer (`isAwgnTypicalityHypothesis` / 主要 wrapper 2 本) も sorryAx-free。
> 計 6 件の false-statement (Wall1 (ii)/(iii)、D2 term2 #5 Fix B、degenerate corner #6) を
> いずれも honest 化済。再検証コマンドは facts ledger の達成テーブル参照。

## 進捗

- [x] M0 — decomposition 再設計の feasible 確定 (D1-D4、2 subagent 独立検証) ✅
- [x] Phase 1 — Wall 1 (D1): (ii) 削除 + (iii) statement-fix + change-of-measure/`hφ_memLp` genuine、`continuousAepGaussian_holds` sorryAx-free ✅ (commits eab36aa→cd5419c→2036bfa→ce9d1bf)
- [x] Phase 4 — Wall 2 (D2): 新 lemma `awgn_random_coding_union_bound` genuine + term1/term2 collapse + Fix B (#5) + Fix #6 → sorryAx-free ✅ (commits 7c26322→e4587aa→b6d0089→8405696→c543ae3→f69cfea)
- [x] Phase 5a — Wall 3 (D3): 新 lemma `awgnPowerConstraintPerCodeword_holds` proof done sorryAx-free ✅ (commit e4587aa)
- [x] D4 — consumer rewire: 旧 Wall2/3 retire + per-codeword barrier 再構築、`isAwgnTypicalityHypothesis` sorryAx-free ✅ (commit b6d0089)
- [x] deep atoms — 5 件 (Wall1 `hφ_memLp` / Wall1 (iii) change-of-measure / Wall2 term1 / Wall2 term2 / N₀ pin) + degenerate corner 全閉鎖 ✅ (commits cd5419c / 8405696 / c543ae3 / ce9d1bf / f69cfea)
- [x] Phase V — verify + 親 plan / facts ledger 同期 + 独立 honesty 監査 ✅ (本同期セッション)

## ゴール / Approach (達成)

### Goal (達成)

`AWGN/Walls.lean` の achievability 側 3 shared sorry 補題を **genuine closure** し、親 plan F-1 の
headline 系 (`AchievabilityDischarge.lean` の `isAwgnTypicalityHypothesis` + 主要 wrapper) を
transitively sorryAx-free にする。**達成**: deep atoms 全閉鎖後、achievability stack 全体が
sorryAx-free。converse は既に genuine 完了済 (`awgn_converse`)。本 plan 完走で AWGN channel
coding theorem の achievability 解析核が genuine。

### Approach (採用した解の形 — 完了)

3 壁を「個別 discharge」でなく AEP engine を最上流に置いた **modular decomposition (D1-D4)** に
組み替えた。確定した依存鎖 (import cycle 不在、検証済):

```
AchievabilityAEP.lean (engine、Mathlib のみ依存、AWGN 依存ゼロ)
  └→ Walls.lean        (D1 Wall 1 + D3 Wall 3、engine を import)
       └→ AchievabilityDischarge.lean (D2 union-bound lemma + D4 consumer、kernel/decoder が local)
```

- **D1 (Wall 1 `continuousAepGaussian_holds`)** = ∃可測A + **2 bounds のみ** ((i)mass + (iii)indep-pair) に縮小。**(ii) volume bound は削除** (false klDiv-to-volume、consumer 破棄済 + 第2項 mass は (iii) 担当ゆえ load-bearing でない)。(iii) は klDiv 積分解 (`klDiv_perLetter_eq_capacity` + `klDiv_nFold_eq_nsmul`、新設 bridge ①) + G-2 tensorize change-of-measure + 退化 `hkl0` で genuine。`hφ_memLp` は 1-D Gaussian 密度の比への因子化 (f_X 相殺) で genuine。
- **D2 (Wall 2)** = `AchievabilityDischarge.lean` の新 genuine lemma `awgn_random_coding_union_bound`。decoder = `jointTypicalDecoder A` 固定、AEP output (i)(iii) を hyp に thread (modular composition、load-bearing bundle 非該当)。term1 = J marginal collapse / term2 = Q marginal collapse + exp 算術で genuine。Fix B (δ-separation) + Fix #6 (`hP`/`hN` で degenerate corner 排除) で honest。
- **D3 (Wall 3)** = `awgnPowerConstraintPerCodeword_holds` (per-codeword expurgation 形、engine φ=x²、proof done sorryAx-free)。
- **D4 (consumer)** = `isAwgnTypicalityHypothesis` を新 decomposition に rewire、per-codeword 合算 barrier 再構築、旧 false 補題 retire。consumer body sorryAx-free。

#### bridge ① 共有 lemma 2 本 (Phase 1 で新設、sorryAx-free)

D1 (iii) の klDiv 積分解の核を `Walls.lean` の 2 shared lemma に切り出した:

- `klDiv_perLetter_eq_capacity` (`Walls.lean:465`、`0 < P` / `(N:ℝ)≠0` 前提): per-letter KL = `(1/2)log(1+P/N)` (capacity 閉形式)。compProd 経路 (`klDiv_compProd_const_toReal_integral` (`CondKLIntegral.lean`) + `klDiv_gaussianReal_gaussianReal_eq` (`DifferentialEntropy.lean`)) で MIClosedForm import cycle を回避。
- `klDiv_nFold_eq_nsmul` (`Walls.lean` :649 付近、無条件): `klDiv(J_n,Q_n).toReal = n·klDiv(J₁,Q₁).toReal` (reshape + `klDiv_pi_eq_sum`)。

import cycle 回避: G-1 (Walls→MIClosedForm→ContChannelMIDecomp→Walls) を上記 compProd 経路 + `import InformationTheory.Shannon.CondKLIntegral` 追加で解消 (commit 2036bfa)。

## 既存資産インベントリ (file:line)

| 資産 | file:line | 用途 | sorryAx 状態 |
|---|---|---|---|
| `pi_empirical_mean_concentration` | `AWGN/AchievabilityAEP.lean:38` | (i)/(D3) engine: 有限-n Chebyshev 集中 (abstract μ+φ) | sorryAx-free (facts ledger) |
| `pi_empirical_mean_typical_mass` | `AWGN/AchievabilityAEP.lean:130` | (i)/(D3) engine: ∃N₀ で mass `≥ 1−η` の存在形 | sorryAx-free |
| `klDiv_pi_eq_sum` | `Shannon/MIChainRule.lean:249` | (iii)/1b: `klDiv (pi P) (pi Q) = ∑ klDiv P Q` (型前提 = `IsProbabilityMeasure` のみ) | sorryAx-free |
| `klDiv_prod_eq_add` | `Shannon/MIChainRule.lean:230` | (iii): prod の KL 加法分解 | sorryAx-free |
| `klDiv_compProd_const_toReal_integral` | `Shannon/CondKLIntegral.lean` | bridge ① 1a: compProd 経路で MIClosedForm cycle 回避 | (既存) |
| `klDiv_gaussianReal_gaussianReal_eq` | `Shannon/DifferentialEntropy.lean:672` | bridge ① 1a: 1-D Gaussian KL closed form | (既存) |
| `awgnCodebookKernel` (+ `Kernel.measurable_kernel_prodMk_left`) | `AWGN/AchievabilityDischarge.lean:998-1028` | D2: codebook-kernel x-可測性 (壁でない、既コンパイル通過) | (既存、通過済) |
| `awgn_expurgate_worst_half` | `AWGN/AchievabilityDischarge.lean:526` | D4: worst-half throwaway、signature 不変で combined penalty に再利用 | `@audit:ok` |
| `awgnPowerWitness_exists` | `AWGN/AchievabilityDischarge.lean:614` | D3: strict slack `P' < P` witness (4次モーメント有限) | `@audit:ok` |

> **converse 側資産 (achievability では不要)**: `jointDifferentialEntropyPi` 系
> (`Draft/Shannon/MultivariateDiffEntropy.lean` / `ParallelGaussian/Converse/Core.lean:145`)
> は旧 Wall 1 (ii) statement-fix 専用だった。D1 で (ii) を削除したため achievability では参照不要
> (converse line の資産として維持)。

## consumer restructure の影響範囲 (blast radius、`scripts/dep_consumers.sh` 実測)

3 壁すべて consumer は **`AchievabilityDischarge.lean` 1 file のみ**、`--transitive` でも 1 file 内
3 decl (他 family / lineage への波及なし)。主たる touch 先 = D4 の 2 consumer
(`awgn_avg_error_union_bound` + `isAwgnTypicalityHypothesis`)、wrapper
`awgn_achievability_F1_via_staged_hyps` → `awgn_theorem_F4_discharged_F1_via_staged` は
signature 不変で 1 行 pass-through 自動追従。D4 rewire 完了済 (commit b6d0089)。

## Phase 詳細

### M0 — decomposition 再設計の feasible 確定 ✅ (commit M0、proof-log: no)

2 subagent 独立検証で D1-D4 feasible 確定 (NO-GO なし)。import 構造 cycle 不在 + numeric/型予測の
verbatim 検証 + 退化境界吸収を確認 → facts ledger に記録。

### Phase 1 — Wall 1 (D1): engine mass (i) + klDiv indep-pair (iii)、(ii) 削除 ✅ sorryAx-free (proof-log: yes)

`continuousAepGaussian_holds` (`Walls.lean`) を **∃可測A + 2 bounds** に縮小、(ii) volume bound 削除、
(iii) を statement-fix (4 件目 false-statement、指数 `−n²I+3nε` → `−n(I−3ε)`)。bridge ① 2 本
(`klDiv_perLetter_eq_capacity` / `klDiv_nFold_eq_nsmul`、sorryAx-free) を新設して (iii) を klDiv
積分解、G-2 tensorize change-of-measure (`pi_withDensity` + `lintegral_pi_prod_eq_prod`) + 退化
`hkl0` (`awgn_perLetter_klDiv_degenerate`) で closure。deep atom `hφ_memLp` (`MemLp φ 2`) は
1-D Gaussian 密度の比への因子化 (f_X 相殺、`integrable_density_log_density_of_gaussian` 風二次多項式
分解) で genuine 化。**全 deep atom 閉鎖、`continuousAepGaussian_holds` sorryAx-free**
(commits eab36aa / cd5419c / 2036bfa / ce9d1bf)。

### Phase 4 — Wall 2 (D2): genuine union-bound lemma ✅ sorryAx-free (proof-log: yes)

新 lemma `awgn_random_coding_union_bound` (`AchievabilityDischarge.lean:502`) を新設、Wall 1 (i)/(iii)
を hyp に thread (decoder = `jointTypicalDecoder A` 固定)、union bound `∫⁻ Pe ≤ 2ε`。term1 (J marginal
collapse、commit 8405696) / term2 (Q marginal collapse + 和 + exp 算術、commit c543ae3) を genuine
closure。**Fix B (#5、commit b6d0089)**: 初版が under-hypothesized で term2 false-statement → typicality
slack δ を error 目標 ε と分離 (`hslack: R+3δ<(1/2)log(1+P/N)` precondition + `∃N₀` 量化子) し honest 化。
**Fix #6 (commit f69cfea)**: degenerate corner (`1+P/N<0`、abs 規約で term2 偽) を `(hP : 0 < P)
(hN : (N:ℝ)≠0)` 追加で矛盾 discharge、consumer 2 件 rewire。**sorryAx-free** (false-statement #5/#6
解消、独立 honesty 監査 PASS)。

### Phase 5a — Wall 3 (D3): per-codeword expurgation 形 ✅ proof done / sorryAx-free (commit e4587aa、proof-log: yes)

新 lemma `awgnPowerConstraintPerCodeword_holds` (`Walls.lean:370`) を genuine sorryAx-free で追加。
per-codeword 形 `∀m, mass{c | n·P_target < ∑ᵢ(c m i)²} ≤ ε`、engine φ=x² (MemLp 4次モーメント素直、
`memLp_id_gaussianReal' 4`) + per-codeword marginal 同定 (`measurePreserving_eval`) + variance 同定。
slack form = `(P_cb.toNNReal:ℝ) < P_target` (分散値ベース)。

### D4 — consumer rewire ✅ (commit b6d0089、proof-log: yes)

旧 false `awgnRandomCodingBound_holds` (`∀decoder` 過大) + `awgnPowerConstraintHonest_holds`
(`∀m` 指数 rate) を retire/削除、consumer を新 lemma 2 本に rewire。`isAwgnTypicalityHypothesis`
の Wall 1 destructure を (i)(iii) 保持に変更、all-or-nothing barrier
`g c := ∑_m Pe + M·𝟙_{∃m violate}` → per-codeword 合算 `g c := ∑_m (Pe c m + Viol c m)` に再構築、
worst-half を combined penalty に適用。reindex/inclusion 機構は signature 不変で再利用。
**consumer body sorryAx-free**、wrapper pass-through 自動追従。

### deep atoms ✅ 全閉鎖 (proof-log: yes)

| atom | 内容 | commit |
|---|---|---|
| a | Wall1 `hφ_memLp` (`MemLp φ 2`、1-D Gaussian 密度の比に因子化、f_X 相殺) | cd5419c |
| (iii) cm | Wall1 (iii) change-of-measure (G-2 RN-deriv tensorize + setLIntegral) | 2036bfa / ce9d1bf |
| d | Wall2 term1 (J marginal collapse `J(Aᶜ)≤ε`、genuine change-of-variables) | 8405696 |
| e | Wall2 term2 (Q marginal collapse + 和 + exp 算術、nondegenerate regime genuine) | c543ae3 |
| c | N₀ を `⌈log(2/ε)/g⌉` に pin (`g = cap − R − 3δ`) | c543ae3 |
| corner | degenerate corner (`1+P/N<0`) を `hP`/`hN` で矛盾 discharge (#6 解消) | f69cfea |

### Phase V — verify + 同期 + 監査 ✅ (proof-log: no)

- `#print axioms` で achievability stack の headline 系 (`isAwgnTypicalityHypothesis` / 主要 wrapper 2 本) が sorryAx-free (= `[propext, Classical.choice, Quot.sound]`) を確認 (再検証コマンド → facts ledger 達成テーブル)。
- 親 `awgn-moonshot-plan.md` の F-1 撤退ライン + 進捗ブロックを本子の状態に同期 (child SoT)、facts ledger に achievability stack sorryAx-free + false-statement #6 + bridge ① 2 本 + 教訓行を追記。
- 独立 honesty 監査: Walls 側 3 宣言 (`continuousAepGaussian_holds` / `klDiv_perLetter_eq_capacity` / `klDiv_nFold_eq_nsmul`) `@audit:ok` (cd016ec)、f69cfea の最終監査は並行実行 (sign-off は別 commit)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。決着済 entry は削除 (git が履歴)。

### #5 (2026-06-12) false-statement #6 = degenerate corner / abs 規約

D2 union-bound の最後の sorry = degenerate corner (`1+P/N<0`) が **false-statement (6 件目)**。
`Real.log x = log|x|` の abs 規約により `1+P/N<0` でも `hslack` (= `R+3δ < (1/2)log(1+P/N)`) が
充足可能 → その corner で `J=Q`、`klDiv=0`、decay 消失、term2 偽 (witness: N=1, P=−3, R=0.1, δ=0.01)。
**fix**: `awgn_random_coding_union_bound` に `(hP : 0 < P) (hN : (N:ℝ)≠0)` を追加し corner を矛盾で
discharge、consumer 2 件 rewire (commit f69cfea)。**教訓**: hypothesis に positivity guard なしの
`Real.log (1 + ·)` が現れたら負値代入の refutation probe を標準にする (abs 規約 corner は型圧で
拾えない)。

### #4 (2026-06-12) Fix B = δ-separation で term2 #5 解消

D2 初版 union-bound が under-hypothesized で term2 false-statement (5 件目): signature が `hR: R<I` と
`hn: 0<n` のみで `∃N₀` 閾値と rate-slack を欠き、term2 が小 n / capacity 近傍 R で偽 (反例 P=N=1,
R=0.1, ε=0.2, n=1, M=2)。**Fix B**: typicality slack δ を error 目標 ε と分離 (`hslack: R+3δ<(1/2)log(1+P/N)`
precondition + `∃N₀,∀n≥N₀,...`)。`hslack` は precondition (consumer が `δ:=(C−R)/12` で自前導出 =
bundle でない決定的証拠)。**教訓**: sub-lemma 切り出しで consumer 側の量化子構造 (`∃N₀`+rate-slack) を
内側に保たないと未消費 bound に型圧がかからず false-statement が生存。

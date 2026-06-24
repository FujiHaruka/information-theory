# EPI G2 連続性壁 `csiszarLogRatioGap_continuousOn` ピボット診断

対象: `csiszarLogRatioGap_continuousOn` (`InformationTheory/Shannon/EPIStamToBridge.lean:1030`)
結論型: `ContinuousOn (fun t => csiszarLogRatioGap X Y Z_X Z_Y P t) (Set.Ici 0)`
body: `sorry` + `@residual(plan:epi-stam-to-conclusion-phaseA-plan)`
診断方法: Read (verbatim) + rg (caller 全列挙) + loogle (Mathlib 壁独立確認)。直感不使用。

## 根本診断 (1 行)

このゴールは genuine に閉じる必要が **ほぼ無い** — 消費先 AntitoneOn が下流で「未使用キャリア引数」として捨てられ、その下流 (`csiszarGap_antitoneOn_Icc_zero_one`) 自身が `sorry` なので、本連続性は最終 EPI に load-bearing でない。最安ルートは route C-変種 (Ioi 経由) ではなく **再分類 + 構造整理**。

## §1 消費先 trace 表

| # | 消費 declaration | file:line | どう使うか | 要求 domain |
|---|---|---|---|---|
| 1 | `csiszarLogRatioGap_antitoneOn_Ici_zero` | EPIStamToBridge.lean:1098 | `antitoneOn_of_deriv_nonpos` の `hf : ContinuousOn f D` 引数 | `Set.Ici 0` (full、端点含む) |
| 2 | (上の出力 `h_anti1`) → `csiszarGap_antitoneOn_Icc_zero_one` | EPIStamToBridge.lean:1356 | 引数 `_h_1source_anti` (**先頭 `_` = 未使用キャリア**) | — |
| 3 | `csiszarGap_antitoneOn_Icc_zero_one` body | EPIStamToBridge.lean:1262 | **本体が `sorry`** (`@residual(...A4-rescale)`)。`_h_1source_anti` を読まずに sorry で結論 | — |

差分版 base `csiszarGap1Source_continuousOn` (EPIStamToBridge.lean:1173) は **live consumer ゼロ** (rg 確認)。唯一の旧 consumer D6 `csiszarGap1Source_antitoneOn_Ici_zero` は false-D3 依存で削除済 (line 1118-1126)。よって差分版連続性は完全に dead code。

決定的観察: `csiszarLogRatioGap_continuousOn` → `_antitoneOn_Ici_zero` → `_Icc_zero_one(_h_1source_anti, body=sorry)`。AntitoneOn は **discard される引数位置**にしか流れない。本連続性 sorry を埋めても最終 EPI の sorryAx 依存は 1 つも減らない (下流 rescale sorry が gate)。

## §2 full ContinuousOn[Ici 0] 必要性 verdict

**verdict: 直接 consumer (`antitoneOn_of_deriv_nonpos`) は full `ContinuousOn f (Set.Ici 0)` (端点 t=0 込み) を要求する。だが下流が unused-carrier + sorry のため、最終結果への寄与はゼロ。**

根拠 lemma verbatim (`Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:478`):
```
theorem antitoneOn_of_deriv_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_nonpos : ∀ x ∈ interior D, deriv f x ≤ 0) : AntitoneOn f D
```
`hf` は `D` 全体 (= `Set.Ici 0`、端点込み)。`hf'` のみ `interior D = Ioi 0`。

HasDerivAt 基盤の domain (verbatim):
- `csiszarGap1Source_hasDerivAt` (:476) — `{t : ℝ} (ht : 0 < t)` → **Ioi 0 のみ**。端点 t=0 で導関数なし。
- `csiszarLogRatioGap_hasDerivAt` (:682) — 同じく `{t : ℝ} (ht : 0 < t)` → **Ioi 0 のみ**。

⇒ HasDerivAt.continuousAt からは内部 (Ioi 0) 連続性のみ無料。端点 t=0 連続性 (= `entropyPower(P.map(X+√t Z)) → entropyPower(P.map X)` as t→0⁺、消えゆく Gaussian) が full ContinuousOn の唯一の真の analytic content であり、これが G2 壁。

route 別評価:
- (a) Ioi 0 連続 + 端点片側極限: `antitoneOn_of_deriv_nonpos` がそのまま使えず、AntitoneOn を Ioi 上で出して別途端点接続が要る → route C と合流。
- (b) upper semicontinuity at 0 のみ: `antitoneOn_of_deriv_nonpos` の `hf` は full ContinuousOn を要求し usc では型が合わない。Mathlib に「usc + 内部 antitone ⇒ Ici 上 antitone」直結 lemma は無い (loogle `AntitoneOn, deriv` = 3 件、いずれも full continuity 系)。usc 単独 route は別途自作 >30 行で不採用。
- (c) `antitoneOn_of_deriv_nonpos` を `Set.Ioi 0` で適用し端点を tendsto 接続: 技術的には可能だが、**そもそも消費先 AntitoneOn が捨てられる**ため投資価値なし。

## §3 最安ルート推奨: 真壁確定 → 再分類 (route 投資せず)

genuine な数学内容として、端点連続性は真の Mathlib 壁:
- loogle `Continuous, entropyPower` / `Filter.Tendsto, Measure.map, ProbabilityTheory.gaussianReal` / `ProbabilityTheory.gaussianReal, Filter.Tendsto` = いずれも **Found 0 / 該当なし**。
- `entropyPower μ := Real.exp (2 * differentialEntropy μ)` (EntropyPowerInequality.lean:101)。差分エントロピーの弱収束連続性 (gaussian smoothing / convolution DCT) は Mathlib 未整備。
- gaussian の var→0 weak-convergence (`gaussianReal 0 t → dirac` as t→0) すら Mathlib に無い (`Found 0`)。

⇒ 端点 t=0 連続性は genuine な heat-flow / vanishing-Gaussian 収束壁。**ただし最安ルートは「この壁を閉じる」ことではない**。下流で AntitoneOn が unused-carrier + sorry に流れるため、本連続性は最終 EPI に non-load-bearing。

**推奨アクション (1 つ): classification 訂正のみ。新たな証明投資なし。**

atom 分解 (コードは触らないので owner への指示形):
1. **atom-1 再分類**: `csiszarLogRatioGap_continuousOn` の `@residual` を `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` → `@residual(wall:heatflow-continuity)` に変更。docstring の「同じ G2 壁を D4 から継承」は正しいが、現状の slug は plan 系で「plan 1 つで閉じる」を含意しており誤分類 (真の Mathlib 壁)。precondition は load-bearing でない (regularity bundle `IsDeBruijnRegularityHyp` は density regularity = 前提条件、結論の核ではない)。
2. **atom-2 redundancy 注記**: docstring に「本連続性の唯一の下流消費 (`_antitoneOn_Ici_zero` → `_Icc_zero_one` の `_h_1source_anti`) は unused carrier であり、下流 rescale 自身が sorry。本 sorry は最終 EPI に non-load-bearing」を 1-2 行追記。次セッションの誤投資を防ぐ。
3. **atom-3 (任意) dead-code 候補マーク**: 差分版 `csiszarGap1Source_continuousOn` (:1173) は live consumer ゼロ。`@audit:retract-candidate(no-live-consumer; D6 deleted)` を付与候補。削除すれば file から 1 sorry 減 (proof-done 集計が前進)。

Mathlib 当て先 (端点を本当に閉じる場合の参照、当面は不要):
- `Mathlib.Analysis.Calculus.Deriv.MeanValue.antitoneOn_of_deriv_nonpos:478` (full ContinuousOn 要求、上記)。
- `Filter.Tendsto` + `le_of_tendsto` 系 (端点接続用、Mathlib にあるが gaussian smoothing convergence 部品が無いため起点が立たない)。

## §4 撤退ライン判定

**発動: YES (既発火、再確認)。** L-Concl-A-θ (plan:158-176) = まさに本壁 (`t=0 端点接続が現行 regularity bundle で carry されず、A-4 budget 超え`)、status `active 発火確定`。本診断は L-Concl-A-θ の再評価であり、新規発火ではなく **classification 訂正** を勧告。

撤退指示 (owner / 別 task):
- slug `plan:...` → `wall:heatflow-continuity` 訂正 commit (§3 atom-1)。理由: loogle Found 0 で plan 1 本では閉じない真壁、honest な再分類。
- 独立 honesty audit は「既存 residual の slug 変更」のみで新規 sorry 導入なしのため、CLAUDE.md 起動条件「signature 変更で honesty 意味が変わる」に該当せず不要。ただし wall 再分類 commit 後に audit-tags.md「共有 Mathlib 壁」へ heatflow-continuity 行追加が望ましい (D4 差分版と ratio 版が同一壁、shared sorry 補題集約候補)。

撤退の撤退 (M ターン以内に進展なければ): 本壁を genuine に閉じる必要が将来生じた場合のみ、`gaussianReal 0 t → dirac (t→0)` weak-convergence を Mathlib に PR するか自作 (>100 行、別 moonshot)。現フェーズでは投資不要。

## proof-log 候補の教訓 (1 行)

連続性 sorry の「埋めるべきか」判定は、消費先を file:line で trace して **AntitoneOn が unused carrier (`_h_1source_anti`) + 下流 sorry に流れていないか**を先に確認すべき — load-bearing でない sorry に DCT 自作を投じる drift を rg trace 一発で防げる。

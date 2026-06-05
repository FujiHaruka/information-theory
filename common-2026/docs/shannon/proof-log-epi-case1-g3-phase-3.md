# Proof-log — EPI case-1 G3 closure Phase 3 (G3 rescale assembly)

対象 sorry: `csiszarGap_antitoneOn_Icc_zero_one` (`EPIStamToBridge.lean`, 現 :1289)
plan: `docs/shannon/epi-case1-difference-g3-closure-plan.md` §Phase 3

## verdict: NOT closed — sufficiency gap (carrier insufficient), 真の analytic 壁

Phase 3 の前提「pure assembly, no Mathlib wall」は **誤り**。実装着手前の verbatim
照合 (proof-pivot ではなく Read + 算術) で、carrier から target が **semantic に
follow しない** こと (honesty check 4 = sufficiency) が判明。signature 保持・body
`sorry`・docstring に sufficiency finding を明記・`@residual` を本 plan slug に再分類、
という honest 撤退で着地した (新規偽構造を積まず)。

## sufficiency finding の中身 (算術)

- **target** (= `IsStamToEPIScalingHyp` の AntitoneOn field、bridge body
  `isStamToEPIBridgeHyp_of_scaling` が `gap(1) ≤ gap(0)` で load-bearing 消費):
  `AntitoneOn (s ↦ eP(sum_s) − eP(X_s) − eP(Y_s)) (Icc 0 1)` = **difference** 形。
- **carrier** `_h_1source_anti`:
  `AntitoneOn (csiszarLogRatioGap ··) (Ici 0)` = **ratio** 形
  `R(t) = log N_sum(t) − log(N_X(t)+N_Y(t))` (R-5-c, genuine, sorryAx-free)。
- rescale 等式 `csiszarGap_eq_one_source_via_rescale` は difference-2-source を
  **difference-1-source** に繋ぐだけ: `csiszarGap(s) = (1−s)·csiszarGap1Source(s/(1−s))`。
  **ratio には繋がらない**。
- `csiszarGap1Source(t) = (N_X(t)+N_Y(t))·(exp(R(t)) − 1)` (entropyPower>0 より
  `N_sum = (N_X+N_Y)·exp R`)。`R` antitone → `exp(R)−1` antitone だが
  `N_X+N_Y` は t で **増加** (entropyPower はノイズ追加で増大) → 積の単調性は
  carrier だけからは不定。⇒ `antitone(ratio) ⊬ antitone(difference)`。
- 必要な genuine 部品 = **1-source difference antitone**
  `csiszarGap1Source_antitoneOn_Ici_zero` (旧 D6) だが、これは false-as-framed
  `csiszarGap1Source_deriv_le_zero` (旧 D3, `@audit:defect(false-statement)`、
  `eP_sum·J_sum ≤ eP_X·J_X+eP_Y·J_Y` は plain harmonic Stam から出ない) に依存して
  いたため **R-5 rewire で削除済**。in-tree に genuine な後継は無い。

これは reframe plan 判断ログ 10 が既に予告していた事実 (「G3 の honest closure 路は
(a) difference-1-source antitone の genuine 再導出 + 6 per-`s` AC/integrability
discharge、または (b) 新規 `R(t)→0 (t→∞)` ratio 極限補題、の 2 択。どちらも
mechanical refactor ではなく実作業」) と一致。Phase 3 brief は判断ログ 10 の
「pure assembly に縮小」を採ったが、それは **AC/integrability 供給** に関する縮小で
あって、ratio→difference の sufficiency gap は別問題として残っていた。

## grep / loogle 観察

- `csiszarGap1Source_antitoneOn_Ici_zero` (difference 1-source antitone) →
  in-tree に **declaration 不在** (コメント言及のみ、R-5 で削除確認)。これが
  carrier→target の唯一の genuine bridge だった。
- a.c. 供給 (Phase 0-b): `P.map (X + √r·Z) ≪ volume` を出す in-house lemma を
  `EPIConvDensity.lean` / `EPIBlachmanGeneralDensity.lean` で `rg "≪|AbsolutelyContinuous"`
  → **0 件**。smoothed-density の AC は in-stock でなく新規 bridge 補題が要る
  (route (a) の追加コスト、ただし plausibly closable)。
- `AntitoneOn.insert_of_continuousWithinAt` (端点 insert machinery) は in-tree 実在
  (carrier 自身が :1165 で使用)。Icc-assembly (Phase 3-d) は feasible — 唯一の壁は
  interior (Ico) の difference antitonicity。

## 設計判断

- **新規偽構造を積まない**: rescale + 端点 + Icc-assembly の scaffolding を組んでも
  最終的に difference-1-source antitone の `sorry` に底打ちするだけ (gap を移動する
  のみ・「pure assembly 完了」の誤印象リスク)。doctrine 通り signature 保持 + body
  `sorry` + 正直な classification を選択。
- `@residual` を `plan:epi-stam-to-conclusion-phaseA-plan` →
  `plan:epi-case1-difference-g3-closure-plan` に再分類 (本 plan が引き取り、
  撤退ライン共通規律 §)。docstring に「NOT a discharge / carrier insufficient /
  genuine route は real analytic work」を明記。

## 後続への引き継ぎ

Phase 3 は本 plan の現 carrier 設計では closure 不能。closure には plan 側の再設計が
要る:
1. **route (a)**: 正しい difference-form `g'(t) ≤ 0` (false D3 の genuine 後継) を
   建てて difference-1-source antitone を再導出 → rescale + 6 AC/integrability
   (新規 smoothed-AC bridge 補題) + s=1 端点。Stam から difference 形 deriv-bound が
   出るか自体が未解決 (reframe plan が「closable 不明」と注記)。
2. **route (b)**: ratio 路を `R(t)→0 (t→∞)` 極限補題で別途完成し、bridge body を
   ratio EPI 復元路に張替 (ただし判断ログ 10 は「bridge の ratio 化は pure-Gaussian
   端点を失うので誤り」と警告 — t→∞ entropic CLT 壁の懸念あり)。

いずれも planner / proof-pivot-advisor マターであり、本 implementer dispatch の
scope (carrier→target の assembly) では closure 不能。orchestrator に carrier 設計の
再検討をエスカレーション推奨。

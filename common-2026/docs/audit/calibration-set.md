# Honesty audit — calibration gate（本番投入前の必須ゲート）

N 並列ワーカーを 2942 件に放つ**前に**、ここに固定したラベル済みセットで Sonnet ワーカー（doctrine 入り）を試走し、**既知の load-bearing を取りこぼさないこと**を確認する。

## PASS 基準（偽陰性回避を最優先）

- **必須**: 下表の `LB`（load-bearing）6件が**すべて `status != ok`**（=捕捉）。1件でも `ok` なら **不合格** → doctrine を修正して再走。
  - verdict コードの逐語一致は問わない（`load_bearing_hyp` でも `degenerate_def`/`circular` でも「捕捉」とみなす）。重要なのは `ok` にしないこと。
- **副次**: `OK` アンカー2件が `ok` のまま（=全部 suspect で塗り潰す退化ワーカーでないことの sanity）。アンカーが suspect 化しても**即不合格にはしない**（偽陽性は軽い）が、doctrine が過敏化していないか点検する。

判定根拠: 偽陰性（load-bearing を `ok` で見逃す）は標準B 未達のまま素通りする最悪ケース。偽陽性（genuine を suspect）は再検査で拾えるので軽い。→ ゲートは偽陰性ゼロを死守。

## ラベル済みセット

| tag | 期待 status | 参考 verdict | id（`module::fqn`） | file:line | src_hash | ground-truth 根拠 |
|---|---|---|---|---|---|---|
| LB | not-ok | `load_bearing_hyp` | `Common2026/Shannon/ParallelGaussianPerCoord.lean::InformationTheory.Shannon.ParallelGaussian.isParallelGaussianPerCoordReduction_discharged` | L295 | 5c441c60 | `h_reg` の `achiever_mi`(達成)＋`max_ent`(逆問題) で `le_antisymm` 両側を供給。容量等式=核心を仮定が肩代わり |
| LB | not-ok | `load_bearing_hyp` | `Common2026/Shannon/AWGNF2F3Discharge.lean::InformationTheory.Shannon.AWGN.awgn_theorem_of_F2F3_hypotheses` | L302 | 83b0eafb | doc「NOT a full discharge: F-2/F-3 を仮定」。`h_F2`(達成)＋`h_F3_chain`(逆問題)が核心 |
| LB | not-ok | `load_bearing_hyp` | `Common2026/Shannon/HuffmanStrongForm.lean::InformationTheory.Shannon.Huffman.huffmanLength_optimal_modulo_aux_ident` | L174 | 1606013c | doc「`MergedHuffmanAuxIdentHypothesis` を唯一の load-bearing hypothesis として受ける」。帰納核心 |
| LB | not-ok | `load_bearing_hyp` | `Common2026/Shannon/ShannonHartley.lean::InformationTheory.Shannon.ShannonHartley.shannon_hartley_formula` | L198 | a557653d | `h_two_w`(`IsTwoWDegreesOfFreedom`)が容量恒等式そのもの。body は unfold+代入 |
| LB | not-ok | `degenerate_def` / `load_bearing_hyp` | `Common2026/Shannon/WhittakerShannonFull.lean::InformationTheory.Shannon.WhittakerShannonFull.whittaker_shannon_full_reconstruction` | L335 | aa340525 | `IsBandlimitedFull := 0<W ∧ ∃ _, True`（vacuous）、仮定 `_h_full` 未使用、任意 f で成立。名が過大 |
| LB | not-ok | `load_bearing_hyp` | `Common2026/Shannon/MultipleAccessChannel.lean::InformationTheory.Shannon.mac_capacity_region_inner_bound` | L731 | 0eb07183 | `h_jt`(`MACJointTypicalityAchievable`)に random-coding 核心。body は実質 `h_jt h_strict` |
| OK | ok | `ok` | `Common2026/Shannon/AEP.lean::InformationTheory.Shannon.jointRV_apply` | L58 | 95fc6e66 | body `rfl`、定義的等式、仮定なし |
| OK | ok | `ok` | `Common2026/Shannon/AEP.lean::InformationTheory.Shannon.logLikelihood_eq_comp` | L89 | 4c637edd | body `rfl`、定義的等式、仮定なし |

## ゲートの回し方

1. `cp docs/audit/honesty.db /tmp/cal.db`（捨て DB）。
2. doctrine（plan「load-bearing 判定ドクトリン」5ルール）を埋めた Sonnet ワーカー1体を起動し、上表8件の id を `show → 本体 Read → 層C → verdict --db /tmp/cal.db` で監査させる。
3. `list --db /tmp/cal.db --status ok` を確認: **`LB` 6件が1つも現れない**こと＝合格。`OK` 2件は `ok` のまま。
4. `rm -f /tmp/cal.db*`。合格なら本番（外側ループ）へ。不合格なら doctrine 修正 → 1 に戻る。

## staleness（再ラベル要否）

`src_hash` は登録時点の `signature+body` のハッシュ。`build` 後に対象の `theorems.src_hash` がここと食い違えば、その定理は監査後に**文が変わっている** → ground-truth ラベルを読み直して更新する（id が消えていれば rename/削除 → 差し替え）。

## 履歴

- run #1（doctrine 前）: `isParallelGaussianPerCoordReduction_discharged` を `ok` 誤判定（偽陰性）→ doctrine 追加の契機。
- run #2（doctrine 後）: 同件を `suspect/load_bearing_hyp` で捕捉。genuine 3件は `ok` 維持。
- calibration（doctrine 後・本ファイルの LB 5件）: 5/5 捕捉、`ok` ゼロ。#4 は `degenerate_def` に（私の予想 load_bearing より厳しい正解）。
- 累計: 既知 load-bearing **6/6 捕捉**、偽陰性ゼロ。

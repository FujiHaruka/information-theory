# 東大 2026 第1問 Lean 形式化 — 作業ログ

将来「Mathlib 検索を楽にするツール」を作るためのベースライン記録。
2026-05-06、Claude Opus 4.7 (1M context) による単発セッション。

## 0. 対象問題

東大 2026 数学 第1問（理系）：

- **(1)** `f(θ) = sin θ - θ + θ³/6` の `[-1, 1]` 上の最大値 M、最小値 m を求めよ。
- **(2)** (1) で定めた M に対し、`7π/8 ≤ ∫₀^{2π} sin(cos x - x) dx ≤ 7π/8 + 4M` を示せ。

成果物：

- `Common2026/T_Q1_1.lean` — 75 行、0 errors / 0 warnings / 0 sorry
- `Common2026/T_Q1_2.lean` — 273 行、同上
- `lake build` 通過（合計 2684 jobs）

## 1. 定量サマリー

| 項目 | (1) | (2) |
|---|---|---|
| 体感所要時間 | 約 30 分 | 約 60 分 |
| 完成行数 | 75 | 273 |
| 内 sorry-skeleton 行数 | 約 50 | 約 130 |
| 主要 lemma 数 | 5 | 14 |
| Mathlib lemma 探索の grep 回数 | 約 6 | 約 12 |
| `lake env lean` 実行回数 | 6 | 約 10 |
| `lake build` 実行回数 | 0 | 1 |
| 補正を要した Edit 回数 | 0 | 1（`push_neg` 非推奨） |

ツールコール総数は 30〜40 回前後（うち TaskCreate/Update を除けば 20〜25 回）。

体感比率：

| 工程 | 体感比率 | 内容 |
|---|---|---|
| Mathlib lemma 探索 | **50%** | grep を当てて補題名を確定する |
| 証明組み立て | 25% | skeleton → fill のサイクル |
| エラー対応 | 15% | private 解除、stale LSP の見極め |
| 数学的方針立て | 10% | "sin(A−B) で消える" 等の見抜き |

## 2. 数学的方針

### (1)

`f'(θ) = cos θ - 1 + θ²/2`。これが `≥ 0`（Taylor 不等式の系）なので f は単調増加。よって端点で達成。

- M = f(1) = sin 1 − 5/6
- m = f(−1) = 5/6 − sin 1

### (2)

工程：

1. `sin(cos x − x) = sin(cos x) cos x − cos(cos x) sin x`（加法定理）
2. `∫₀^{2π} cos(cos x) sin x dx = 0`：原始関数 `−sin(cos x)` が `0` と `2π` で同じ値。
3. `sin θ = θ − θ³/6 + f(θ)` に代入。
4. `∫₀^{2π} cos²x dx = π`、`∫₀^{2π} cos⁴x dx = 3π/4`。主項 = `π − π/8 = 7π/8`。
5. f は奇関数で `f(0)=0` かつ単調 ⇒ `sign(f θ) = sign θ` ⇒ `f(cos x) cos x ≥ 0`。
6. f(1) = M, f(−1) = −M、`|θ| ≤ 1` で `f(θ) θ ≤ M |θ|`。
7. `∫₀^{2π} |cos x| dx = 4`。

`(7π/8) + ∫ f(cos x) cos x` で、`∫` は `[0, 4M]`。

問題が「`∫ f cos = 0` 〜 `4M`」の幅にぴたっとはまる、よくできた問題。

## 3. Mathlib 補題探索の実録

### 3.1 (1) で探した補題

| 必要だったもの | 実際の grep クエリ（最終形） | 所要試行 | 発見場所 |
|---|---|---|---|
| `1 − x²/2 ≤ cos x` | `cos.*one_sub.*sq\|one_sub_sq.*cos\|cos.*sub_one.*sq` を Trigonometric/ で | 1 回（一発） | `Bounds.lean:Real.one_sub_sq_div_two_le_cos` |
| `sin(x) ≤ x` | `^(theorem\|lemma\|protected).*sin_lt\|sin_le_self\|sin_le ` | 1 回 | `Bounds.lean:Real.sin_le` （結局未使用） |
| `HasDerivAt sin / cos` | `^(theorem\|lemma).*hasDerivAt_(sin\|cos)` を Deriv.lean で | 1 回 | `Real.hasDerivAt_sin / cos` |
| 単調性 from 導関数 | (1) `monotone_of_deriv\|monotoneOn_of_deriv\|StrictMono.*deriv` で空振り → (2) ファイル特定 → (3) 署名読み → (4) HasDerivAt 版に絞り込み | 4 段階 | `Deriv/MeanValue.lean:monotone_of_hasDerivAt_nonneg` |

### 3.2 (2) で探した補題

| 必要だったもの | grep クエリ（最終形） | 所要試行 | 結果 |
|---|---|---|---|
| `∫ cos²` の閉形式 | `^(theorem\|lemma\|@\[).*integral_cos_pow\|integral_cos_sq` | 3 回（最初に Integrals.lean 系のファイル名を間違えた） | `integral_cos_sq` |
| `∫ cos⁴` の閉形式 | 上と同時に発見 | — | **直接形は無し**。`integral_cos_pow` の reduction formula で n=2 適用 |
| FTC `∫ f' = F b − F a` | `integral_eq_sub_of_hasDerivAt\b` を MeasureTheory/Integral 配下で | 2 回（場所特定 → 署名読み） | `IntervalIntegral/FundThmCalculus.lean:integral_eq_sub_of_hasDerivAt` |
| 三角関数の特殊値 | `sin_pi\|cos_pi_div_two\|sin_add_pi` で一括 | 1 回 | 標準的な揃い |
| `cos(x − 2π) = cos x` | `cos_sub_two_pi\|cos_periodic` | 1 回 | `cos_sub_two_pi` |
| 区間内の cos 符号 | (1) Basic.lean のみで `cos_nonneg\|cos_nonpos` → (2) 全 Trig で再度 | 2 回 | `cos_nonneg_of_mem_Icc`, `cos_nonpos_of_pi_div_two_le_of_le` |
| `∫ f / c = (∫ f)/c` | `integral_div_const\|theorem integral_div ` | 1 回 | `intervalIntegral.integral_div` |
| 積分線形性 | `integral_const_mul\|integral_mul_const` | 1 回 | `intervalIntegral.integral_const_mul` |
| `∫ f ≥ 0` from pointwise | `^theorem integral_nonneg\b` | 1 回 | `intervalIntegral.integral_nonneg` |
| `sin(3π/2) = −1` | — | — | **存在せず**。`sin_add_pi` + `sin_pi_div_two` から手で導出 |
| `∫₀^{2π} \|cos x\| dx = 4` | `integral.*abs_cos\|abs_cos.*integral` で空振り、`integral_sin\|integral_norm_cos` 等も空振り | 2 回 | **存在せず**。3 分割で手計算（70 行） |

### 3.3 「無いもの探し」の代償

`integral_abs_cos` と `sin_three_pi_div_two` は Mathlib に**存在しなかった**。これは：

1. 探索を一定回数試して「無い」と判断する判断時間を消費する。
2. 自分で証明する大きなコストが発生する。

特に `integral_abs_cos` は手計算で約 70 行（`T_Q1_2.lean` の **25%**）を占めた。これがあれば全体は 200 行、所要時間も 30%-40% 短縮できた可能性が高い。

## 4. 段階別タイムライン

### Phase 1: 既存スタイル把握（約 5 分）

- `ls Common2026/` で既存問題を確認。
- `Common2026/A_Q1_1_i.lean` を Read（CLAUDE.md 推奨のテンプレ）。
- `Common2026/B_Q7.lean` を peek。
- `grep -h "^import" Common2026/*.lean` で既存 import パターン把握。

### Phase 2: (1) skeleton 作成（約 5 分）

- 数学的見通しを立て、必要補題を列挙：`cos_taylor_lower`, `f_hasDerivAt`, `f_monotone`, `f_one`, `f_neg_one`, `max_value`, `min_value`。
- Write でファイル生成。LSP の `<new-diagnostics>` で sorry 警告のみを確認。

### Phase 3: (1) 補題穴埋め（約 15 分）

順序：
1. `cos_taylor_lower` — `Real.one_sub_sq_div_two_le_cos` → `linarith` 一発。
2. `f_hasDerivAt` — `Real.hasDerivAt_sin`, `hasDerivAt_id`, `hasDerivAt_pow 3` を `.add` `.sub` で合成、`convert _ using 1; ring`。
3. `f_monotone` — `monotone_of_hasDerivAt_nonneg` に `f_hasDerivAt` と `cos_taylor_lower` を渡す。
4. `f_one`, `f_neg_one` — `show ...; ring`（`f_neg_one` だけ `Real.sin_neg` を挟む）。
5. `max_value`, `min_value` — `f_monotone` に `hθ.2` / `hθ.1` を渡し、`rw [f_one]` / `rw [f_neg_one]`。

各補題後に `lake env lean Common2026/T_Q1_1.lean` で確認。LSP の自動診断と冗長になるが、bash の方が確実。

### Phase 4: (2) 数学方針確認（約 5 分）

- 紙の上で「`cos(cos x) sin x` の積分が消える」「`∫ cos² = π`、`∫ cos⁴ = 3π/4`」「主項 7π/8」を計算で確認。
- 各工程に対応する Mathlib 補題を予想して列挙。

### Phase 5: (2) skeleton 作成（約 5 分）

- 14 の補題を sorry で並べる。
- `open Common2026.T_Q1_1 (f f_monotone f_one f_neg_one)` で T_Q1_1 から取り込み。
- LSP 一発で「skeleton clean」を期待 → **失敗**。`f_monotone` 等が `private lemma` で外から見えない。

### Phase 6: 可視性問題の修正（約 3 分）

- `T_Q1_1.lean` で `f_monotone`, `f_one`, `f_neg_one` を `private lemma` → `lemma` へ。
- `lake env lean Common2026/T_Q1_1.lean` だけでは downstream の olean が更新されないことに気付き、`lake build Common2026.T_Q1_1` を実行。**約 5 秒で済んだ**。

### Phase 7: (2) 補題穴埋め（約 50 分）

順序と所要：

| # | 補題 | 体感時間 | 詰まりポイント |
|---|---|---|---|
| 1 | `f_zero`, `f_mul_self_nonneg` | 5 分 | `le_or_lt` を知らず、`by_cases` に切替 |
| 2 | `integral_cos_cos_mul_sin`（FTC） | 8 分 | 合成微分 `h2.comp x h1` の符号調整、`convert ... using 1; ring` |
| 3 | `integral_sin_eq` | 5 分 | `intervalIntegral.integral_congr` の使い方、calc の組み立て |
| 4 | `integral_cos_sq_zero_two_pi`, `integral_cos_four_zero_two_pi` | 5 分 | reduction formula 経由でも `linarith` 一発 |
| 5 | `integral_eq_main` | 5 分 | linearity を rw で連打、`integral_div` の存在確認 |
| 6 | `f_mul_le_M_abs` | 5 分 | `mul_le_mul_of_nonpos_right` の符号方向 |
| 7 | `integral_f_cos_mul_cos_nonneg` | 2 分 | 一発 |
| 8 | `integral_abs_cos` | **15 分** | 3 分割、各区間で `Set.uIcc_of_le` で unwrap、`cos_sub_two_pi` 経由の周期性 |
| 9 | `integral_f_cos_mul_cos_le` | 3 分 | `integral_mono_on` で素直に |
| 10 | 主結果 `main_lower` / `main_upper` | 1 分 | `linarith` だけ |

各補題後に `lake env lean` で確認、grep 結果に基づく即時修正。

### Phase 8: 仕上げ（約 2 分）

- `push_neg` の deprecation warning 対応 → `not_le.mp` に置換。
- `lake build` で全体ビルド、2684 jobs 通過を確認。

## 5. 試行錯誤の例

### 失敗 1: 補題名の見当外し

`monotone from derivative` を探したとき、最初は `Mathlib/Analysis/Calculus/MeanValue.lean` 単体に grep を打って空振り。実際は `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` の方に主要補題がある。**「ファイル名の階層が複数ある」** ことに気付くまで grep が無駄になった。

教訓：lemma サーチは最初から「Mathlib 全域 grep → ヒットしたファイルの中身を読む」の 2 段階構成が安定。ピンポイントで「ここにあるはず」と決め打ちしない。

### 失敗 2: 命名規則の揺れ

`integral_cos_pow` を探したとき、`Integrals.lean` というファイル名を仮定 → `find` で見つかったのは `Probability/.../Integrals.lean`（無関係）。実体は `SpecialFunctions/Integrals/Basic.lean` 配下のディレクトリ構成。**ディレクトリが `Integrals/` でファイルが `Basic.lean`** という階層を予想できず迷った。

教訓：Mathlib の最新版ではモジュール分割が進んでおり、古い knowledge では辿れない。

### 失敗 3: 「無い」を確定させるコスト

`integral_abs_cos` を 2 種類の grep（命名直接、関連語）で空振りしてから「自分で書く」と決断。実際は 3 種類試したが、Mathlib の命名規則上「他の名前で隠されているかも」という疑念を完全には払拭できなかった。**「無いことの証明」** が grep ベースだと不可能で、これが意思決定の遅延を生む。

教訓：Mathlib の網羅的な lemma index（型シグネチャベースの `loogle` のようなもの）があれば、判断が速くなる。

### 失敗 4: LSP の stale 状態

`Common2026.T_Q1_2.lean` の編集中、LSP の `<new-diagnostics>` が **古い状態の f 未定義エラーを延々と返してきた**。bash の `lake env lean` 出力との不整合で混乱した。最終的に「bash を信じる」と決めて作業継続。

LSP の再起動／キャッシュ無効化トリガーを掴めると、人間（あるいは Agent）の判断負荷が下がる。

### 失敗 5: 古いタクティクス

`push_neg` が deprecation warning を出した。Mathlib の進化に追従できていない部分。これは大したコストではないが、「いま現在何が推奨か」が API search で出ると嬉しい。

## 6. ボトルネックではなかったもの

- **数学のアイデア**：問題が "Mathlib にある部品の組合せ" で解けるタイプだったので、creative leap が要らなかった。
- **Lean の型チェック**：`ring`, `linarith`, `simp`, `nlinarith` がほぼ最後の決め手で、詰まることはなかった。
- **コンテキスト長**：grep 結果は短く、ファイル全体も 350 行未満で、LSP の冗長な diagnostic を含めても圧迫せず。
- **ビルド時間**：単一ファイル `lake env lean` は数秒、`lake build` 全体も 5 秒で済んだ。

## 7. ツール開発への示唆

定性的な失敗パターンから、補助ツールに欲しい機能：

### 必須

1. **Loogle 風の「型ベース lemma 検索」**：「`a ≤ b → b ≤ c → ∫ a..c, f = ∫ a..b f + ∫ b..c f`」のような型シグネチャから候補を返す。grep の限界は「命名を当てに行く」点。
2. **「無い」の素早い判定**：複数の命名規則・関連語をまとめて検索し、「これらすべてに該当無し」と確定させる。今回の 70 行手書きを回避できた可能性あり。
3. **モジュール構造の最新マップ**：`Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` のように階層が深く、かつ更新される。ファイル名で grep ターゲットを決める運用は脆い。

### 中優先

4. **LSP / olean 状態の可視化**：上流ファイル編集後に `lake build <module>` が必要かどうかを自動判定 / 通知。
5. **deprecation 検知**：使ったタクティクス・補題が deprecated だと事前に警告。
6. **使用頻度ランキング**：`monotone_of_deriv_nonneg` と `monotone_of_hasDerivAt_nonneg` のように複数バリアントがあるとき、ユースケースから推奨を出す。

### 低優先

7. **proof skeleton 自動生成**：問題文から「補題を `sorry` で並べる」までを補助。
8. **ベンチマーク化**：本ログのフォーマットを定型化して、別の入試問題でも同じ計測を取り、ツール導入前後で比較。

## 8. 補足メトリクス

`grep` 系の bash コマンド一覧（プロジェクト初期探索除く）：

```
grep -rE "cos.*one_sub.*sq|one_sub_sq.*cos|cos.*sub_one.*sq" \
  .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/

grep -rE "^(theorem|lemma|protected).*sin_lt|sin_le_self|sin_le " \
  .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/

grep -E "^(theorem|lemma).*hasDerivAt_(sin|cos)|HasDerivAt.*Real\.(sin|cos)" \
  .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean

grep -E "monotone_of_deriv|monotoneOn_of_deriv|StrictMono.*deriv|deriv.*nonneg.*Mono" \
  .lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean

grep -rEl "monotone_of_deriv_nonneg|monotoneOn_of_deriv" \
  .lake/packages/mathlib/Mathlib/Analysis/Calculus/

grep -E "^(theorem|lemma) (monotone_of_deriv|monotoneOn_of_deriv|strictMono)" \
  .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean

grep -E "monotone.*hasDeriv|hasDeriv.*[Mm]onotone" \
  .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean \
  .lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean

grep -E "^(theorem|lemma).*integral_cos.*pow|^(theorem|lemma).*integral.*cos_sq" \
  .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals*.lean

grep -rEl "integral_cos_pow|integral_cos_sq|integral_sin_pow" \
  .lake/packages/mathlib/Mathlib/

grep -E "^(theorem|lemma|@\[).*integral_cos_pow|integral_cos_sq|integral_pow_cos" \
  .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean

grep -rE "^(theorem|lemma) integral_eq_sub_of_hasDeriv" \
  .lake/packages/mathlib/Mathlib/

grep -B 1 -A 6 "^theorem integral_eq_sub_of_hasDerivAt " \
  .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean

grep -E "^(theorem|lemma).*cos_two_pi|sin_pi|cos_pi_div_two|sin_add_pi" \
  .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean

grep -rE "integral.*abs_cos|abs_cos.*integral" .lake/packages/mathlib/Mathlib/

grep -rE "^(theorem|lemma|protected).*cos_nonneg|cos_nonpos|cos_neg_of" \
  .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/
```

15 件。各回ファイル特定と署名読みを足すと、有効ヒットまで平均 1.5 回。

## 9. 結論

「数学的アイデア」よりも「Mathlib API のサーフェス知識」が支配的。これは AI コーディング一般の傾向（ライブラリ関数を呼べるかが鍵）と一致する。

このプロジェクトを Mathlib 検索ツールの開発台座にするなら、**「型ベース検索 + 無いの素早い判定」** の 2 機能をまず作るのが最大の ROI と思われる。

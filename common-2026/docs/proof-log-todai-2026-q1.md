# 東大 2026 第1問 Lean 形式化 — ボトルネック分析

将来「Mathlib 検索を楽にするツール」「自動 sorry 埋めエージェント」を作るためのベースライン記録。

**定量データ**: [docs/metrics/todai-2026-q1.metrics.md](metrics/todai-2026-q1.metrics.md)

## 0. 対象問題と成果物

東大 2026 数学 第1問（理系）:

- **(1)** `f(θ) = sin θ - θ + θ³/6` の `[-1, 1]` 上の最大値 M、最小値 m を求めよ。
- **(2)** (1) で定めた M に対し、`7π/8 ≤ ∫₀^{2π} sin(cos x - x) dx ≤ 7π/8 + 4M` を示せ。

成果物:

- `Common2026/T_Q1_1.lean` — 75 行、0 errors / 0 warnings / 0 sorry
- `Common2026/T_Q1_2.lean` — 272 行、同上
- `lake build` 通過

## 1. 問題のキャラクター

「Mathlib にある微積分・三角関数の部品を呼び出して組み合わせる」型。創造的飛躍は要らないが、**「呼びたい部品の名前が当たるか」「無かったときに自分で書く判断ができるか」が支配項**になった。

特に (2) は、以下 4 種の Mathlib API を全部正しく呼べることが要求された:

- `intervalIntegral` 系（`integral_eq_sub_of_hasDerivAt`、`integral_congr`、`integral_sub`、`integral_const_mul`、`integral_div`、`integral_mono_on`、`integral_nonneg`）
- `Real` の三角関数値（`cos_two_pi`、`sin_two_pi`、`cos_pi_div_two`、`sin_add_pi` など）
- 三角関数積分の閉形式（`integral_cos_sq`、`integral_cos_pow`）
- 微分の合成 / 加減（`HasDerivAt.comp`、`.add`、`.sub`、`.neg`、`.div_const`）

## 2. 数学的方針

### (1)

`f'(θ) = cos θ - 1 + θ²/2`。Taylor 不等式の系として `f' ≥ 0`、よって f は単調増加で、`[-1, 1]` 上の極値は端点で達成。`M = f(1) = sin 1 - 5/6`、`m = f(-1) = 5/6 - sin 1`。

### (2)

主たる機械的書き換え:

1. `sin(cos x - x) = sin(cos x) cos x - cos(cos x) sin x`（加法定理）
2. `cos(cos x) sin x` の原始関数は `-sin(cos x)`、両端 `0`, `2π` で同値 → 積分 0
3. `sin θ = θ - θ³/6 + f(θ)` を `θ = cos x` に代入し、`cos x` を掛けて `[0, 2π]` で積分
4. `∫ cos²x dx = π`、`∫ cos⁴x dx = 3π/4` ⇒ 主項 `π - π/8 = 7π/8`
5. f は奇関数で単調 ⇒ `f(θ)·θ ≥ 0` ⇒ 下限 `7π/8` 確定
6. `|θ| ≤ 1` で `f(θ) ≤ M`、`∫ |cos x| dx = 4` ⇒ 上限 `7π/8 + 4M` 確定

「`∫ f(cos x) cos x` の幅が `[0, 4M]` にぴたっと収まる」のが本質。問題側で残余を `4M` に封じ込めるよう設計されている。

数学的な気づきは早かった（紙計算で 5 分程度）。**支配項は Mathlib API の名前当てだった**。

## 3. Mathlib 補題探索の実録

### 3.1 当たった検索（grep の最終形）

| 必要だったもの | grep クエリ | 試行 | 場所 |
|---|---|---|---|
| `1 - x²/2 ≤ cos x` | `cos.*one_sub.*sq\|one_sub_sq.*cos\|cos.*sub_one.*sq` を `Trigonometric/` で再帰 | 1 | `Trigonometric/Bounds.lean : Real.one_sub_sq_div_two_le_cos` |
| `HasDerivAt sin / cos` | `^(theorem\|lemma).*hasDerivAt_(sin\|cos)\|HasDerivAt.*Real\.(sin\|cos)` を `Trigonometric/Deriv.lean` で | 1 | `Real.hasDerivAt_sin / cos` |
| `∫ cos²` の閉形式 | `^(theorem\|lemma\|@\[).*integral_cos_pow\|integral_cos_sq\|integral_pow_cos` を `Integrals/Basic.lean` で | 3（ファイル名で迷走） | `Integrals/Basic.lean : integral_cos_sq` / `integral_cos_pow` |
| FTC `∫ f' = F b - F a` | `^(theorem\|lemma) integral_eq_sub_of_hasDeriv` を Mathlib 全体で | 2 | `IntervalIntegral/FundThmCalculus.lean : integral_eq_sub_of_hasDerivAt` |
| `cos_sub_two_pi`、特殊値 | `^(theorem\|lemma\|@\[).*sin_pi\|sin_three_pi\|sin.*pi_div_two\|cos_pi_div_two\|sin_add_pi\|cos_pi\b` を `Trigonometric/Basic.lean` で | 1 | `Real.cos_two_pi`、`Real.sin_pi`、`Real.cos_pi_div_two`、`Real.sin_add_pi` |
| 区間内 cos の符号 | `^(theorem\|lemma\|protected).*cos_nonneg\|cos_nonpos\|cos_neg_of` を `Trigonometric/` で再帰 | 2（最初 `Basic.lean` 単独で空振り → ディレクトリ全体に拡大） | `cos_nonneg_of_mem_Icc` / `cos_nonpos_of_pi_div_two_le_of_le` |
| `monotone from derivative` | `monotone_of_deriv\|monotoneOn_of_deriv\|StrictMono.*deriv\|deriv.*nonneg.*Mono` を `Calculus/MeanValue.lean` 単独で | 4 段階（後述） | `Deriv/MeanValue.lean : monotone_of_hasDerivAt_nonneg` |

### 3.2 「無かった」もの — ここが将来ツールの主戦場

- **`integral_abs_cos`** — `integral.*abs_cos\|abs_cos.*integral` を Mathlib 全体に再帰 grep して空振り。
  代わりに `[0, π/2]`、`[π/2, 3π/2]`、`[3π/2, 2π]` の 3 区間に分けて、各区間内で `|cos x|` を `cos x` または `-cos x` に置換し直接積分。約 70 行の手書き、最終ファイル `T_Q1_2.lean` の **約 25%** を占める。**もし Mathlib にあれば全体の 30% 以上の節約**だった可能性が高い。
  教訓: 「`∫_{0}^{2π} |cos x| dx = 4`」のような **物理的に普遍な定数** は、Mathlib 命名規則だと何で索かれるか不明。型ベース検索（`∫₀^{2π} |cos x| dx = ?` の形で問い合わせ）か、「定数値積分テーブル」のような特殊化された索引が要る。

- **`sin_three_pi_div_two`（`= -1`）** — そもそも検索クエリには出さず、`sin_add_pi` + `sin_pi_div_two` から `sin(3π/2) = sin(π/2 + π) = -sin(π/2) = -1` と手動で導出して回避。Mathlib に直接無いと判断するのは目分量だが、空振りコストが小さいので深追いしなかった。
  教訓: 「自明だが無いかもしれない補題」を即座に「あるか／無いか／自分で導出するか」3 択に解決する仕組みがあると、迷いが減る。

### 3.3 ファイル階層誤認による迷走

`monotone_of_hasDerivAt_nonneg` を見つけるまで 4 段階を要した:

1. `Calculus/MeanValue.lean` 単独に `monotone_of_deriv` 系で grep → 空振り
2. ディレクトリ全体 `Calculus/` に `grep -rEl` でファイル名を逆引き → `Deriv/MeanValue.lean` 発見
3. その中で `monotone_of_deriv\|strictMono` で grep → ヒット
4. ヒットしたが署名が `deriv` 版で `HasDerivAt` 版でない → 周辺を `monotone.*hasDeriv\|hasDeriv.*[Mm]onotone` で再 grep して `monotone_of_hasDerivAt_nonneg` を発見

**`Calculus/MeanValue.lean` と `Calculus/Deriv/MeanValue.lean` の 2 ファイルが並存する**ことを知らないと最初の grep が必ず空振りする。Mathlib のモジュール分割は時間とともに進化するので、過去の知識（あるいは GPT の事前学習データ）は脆い。

教訓: ピンポイントで「ここにある」と決め打つ検索は脆弱。最初から「ディレクトリ全体 → ヒットしたファイル名を確認」の 2 段階構成にすべき。

## 4. 試行錯誤と後戻り

### 4.1 `private lemma` の可視性で詰まる

**症状**: `T_Q1_1.lean` の補題（`f_monotone`、`f_one`、`f_neg_one`）を `T_Q1_2.lean` から `open Common2026.T_Q1` で参照しようとすると `unknown identifier`。

**原因**: skeleton 段階で全部 `private lemma` で書いていた（CLAUDE.md のサンプル `A_Q1_1_i.lean` がそう書いている）。`private` は同一ファイルからしか見えない。

**抜け方**: 公開すべき補題（`f_monotone`、`f_one`、`f_neg_one`）を `lemma` に変更。

**教訓**: スキルレベルで「クロスモジュール参照する補題は `private` を外す」のチェックリストが要る。または `open` 失敗時の LSP エラーから「対応補題が `private` だ」を自動診断する仕組み。

### 4.2 LSP の stale olean 問題

**症状**: `T_Q1_1.lean` を編集して `private` を外した直後、`T_Q1_2.lean` の LSP `<new-diagnostics>` が **古い `f` 未定義エラーを返し続ける**。

**原因**: LSP は `lake setup-file` で `.olean` を再ビルドせず、上流の olean が古いまま下流をチェックする。`lake env lean Common2026/T_Q1_2.lean` は正しく silent だった。

**抜け方**: `lake build Common2026.T_Q1_1` を 1 回走らせて olean を更新（5 秒程度で完了）。次の LSP チェックは正常な状態を返した。

**教訓**: CLAUDE.md にすでに記載のあるトピックだが、実際に踏むと判断に時間を食う。「上流ファイル編集時に下流をリチェックすべきタイミング」を agent 側に明示通知する hook がほしい。

### 4.3 `push_neg` deprecation warning

**症状**: `lake env lean` 出力に `push_neg has been deprecated` の warning。

**原因**: Mathlib の最新版で `push_neg` の挙動が変わり、`not_le.mp` を直接使う方が推奨に。

**抜け方**: `not_le.mp` に置換。

**教訓**: deprecated tactic / lemma の代替を提示する API ドキュメント検索が欲しい。grep ベースだと「現在のベストプラクティス」が分からない。

### 4.4 `cos⁴` の閉形式は Mathlib に直接無い

**症状**: `∫₀^{2π} cos⁴x dx = 3π/4` を一発で取りたかったが、`integral_cos_pow` は **reduction formula** の形（`∫ cos^(n+2) = ... + (n+1)/(n+2) ∫ cos^n`）でしか提供されていない。

**抜け方**: `integral_cos_pow (n := 2)` を呼んで `∫ cos² = π` で展開、`linarith`。

**教訓**: 多くの「閉形式」は reduction formula から導く必要がある。「具体的な n に対する閉形式テーブル」が事前展開されていれば即座に終わる作業。

### 4.5 `integral_eq_sub_of_hasDerivAt` のファイル位置

**症状**: 「FTC」を Mathlib のどこから呼ぶか確信が持てず、`MeasureTheory/Integral/FundThmCalculus.lean` を見たが本命でない。

**抜け方**: `grep -rE "^(theorem|lemma) integral_eq_sub_of_hasDeriv" .lake/packages/mathlib/Mathlib/` で全域検索 → `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean` を特定。

**教訓**: 「同名ファイルがディレクトリ違いで複数存在する」は Mathlib では普通。最初から全域 `grep -rEl` を打つべき。

## 5. ボトルネックではなかったもの

- **数学的アイデア**: 問題が「Mathlib の部品の組合せで解ける」型だったので、creative leap が要らない。紙の上で 5 分程度で全工程の見通しが立った。
- **Lean の型チェック / 証明戦術**: `ring`、`linarith`、`simp`、`nlinarith` がほぼすべての最終仕上げで通った。`convert ... using 1; ring` の定型もすぐ嵌った。
- **コンテキスト長**: 1M context で grep 結果も中間ファイルも全部抱えて余裕があった。圧縮判断は不要。
- **ビルド時間**: 単一ファイル `lake env lean` は秒、`lake build` 全体も短時間で済んだ。インナーループのフィードバックが速かった。

これらは将来のツール開発で「投資の優先度を下げてよい」領域。

## 6. ツール開発への示唆

| 優先度 | 機能 | 節約できたコスト |
|---|---|---|
| 高 | **型ベース lemma 検索（loogle 風）** | `integral_abs_cos` の空振り判定、`monotone_of_hasDerivAt_nonneg` の 4 段階探索を即決にできた |
| 高 | **「無い」の素早い確定** | `integral_abs_cos` を「存在しない」と早期確定できれば、迷いコストと「他の名前で隠されているかも」という疑念のコストを排除できる |
| 高 | **Mathlib モジュール構造の最新マップ** | `Calculus/MeanValue.lean` と `Calculus/Deriv/MeanValue.lean` が並存することを最初から知っていれば 4 段階を 1 段階にできた |
| 中 | **deprecation 検知 + 代替提示** | `push_neg` のような deprecated tactic を編集時点で警告し `not_le.mp` を提案 |
| 中 | **特殊定積分テーブル** | `∫₀^{2π} cos⁴ = 3π/4`、`∫₀^{2π} |cos x| = 4` のような「具体定数値」を即座に引ける |
| 中 | **上流 olean 更新の通知** | `T_Q1_1.lean` を編集後、下流 LSP が古い結果を返している状況で `lake build <upstream>` を促す |
| 低 | **proof skeleton 自動生成** | 問題文 → 補題リスト → `:= by sorry` skeleton を 1 段で生成。今回の skeleton 段階自体は 5 分程度で詰まらなかったので、優先度は低 |

優先度判断: 高優先度の 3 項目はいずれも **「探索の空振り」と「ファイル位置の誤認」を排除**するものに集中している。これは proof engineering 一般で再現する課題と思われる。

## 7. 補足

実際に打った grep コマンドの一覧と Edit 系列の詳細は JSONL に残っている。再現したい場合は `references/reconstruction.md` の手順で抽出可能。

定量サマリ（ツールコール数・所要時間・ファイル別 Edit 回数など）は [metrics.md](metrics/todai-2026-q1.metrics.md) に記載。本文中で引いた「最終ファイルの 25% を `integral_abs_cos` 手書きが占める」のような具体比率もそちらに準拠。

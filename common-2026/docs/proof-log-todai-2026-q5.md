# 東大 2026 第5問 Lean 形式化 — ボトルネック分析

将来「中間値定理 + 三角恒等式の代数化 + sqrt の rewrite」型の問題向けに、`sqrt_sq` の方向性 / `Mathlib.Topology` 配下のモジュール名 / `rewrite` の pattern matching を自動補正するエージェントを作るためのベースライン記録。

**定量データ**: [docs/metrics/todai-2026-q5.metrics.md](metrics/todai-2026-q5.metrics.md)

## 0. 対象問題と成果物

東大 2026 数学 第5問:

> 複素数平面上の原点を中心とする半径 1 の円を C とする。複素数 α と C 上の点 P(z) に対し、w = (z − α)³ とおく。P が C 上を動くときの点 Q(w) の軌跡を D とする。
> (1) α = −3 のとき、w の偏角 θ に対して sin θ がとりうる値の範囲を求めよ。
> (2) D が実軸の正の部分・負の部分の両方と共有点を持つように α が動くとき、α が動きうる範囲の面積を求めよ。

成果物:

- `Common2026/T_Q5.lean` — 469 行、`theorem sinTheta_range : SinThetaSet = Set.Icc (-(23/27)) (23/27)`（(1) 完全形式化）と `theorem isGoodAlpha_of_inside`（(2) の構造的補題：単位開円板 ⊂ GoodSet）。
- `lake env lean` クリーン通過、`sorry` ゼロ、警告ゼロ。
- (2) の答え 4√3 そのものは形式化していない（理由：`∫ r arcsin(1/r) dr` の積分計算が Mathlib の measure-theoretic integral を呼び出すと大規模になる）。冒頭 docstring に方針を略述するに留めた。

## 1. 問題のキャラクター

**「複素数の代数化 + 中間値定理 + sqrt の rewrite」**型。Mathlib の本体補題は `intermediate_value_Icc` / `intermediate_value_Icc'` / `sq_sqrt` / `sqrt_sq` の 4 種類で済むが、`Real.sqrt` を含む等式の `rw` のパターンが微妙に合わず詰まる。

過去問との比較:

| 問題 | 支配工程 | Mathlib 検索の重さ | 主な詰まりどころ |
|---|---|---|---|
| Q1 (微積分) | Mathlib 部品呼び出し | 重い | `MeanValue` 系の名前 |
| Q3 (座標 + 除算) | `set` + `field_simp` | 軽い | `nlinarith` ヒント |
| Q4 (代数恒等式) | 多項式の押し回し | 0 | `private` 可視性 / 場合分け爆発 |
| **Q5 (複素数 + IVT + sqrt)** | **`Real.sqrt` を含む等式の rw** | **軽い** | **モジュール名 / `sqrt_sq` 方向 / pattern matching** |

複素数を `ℝ × ℝ` で表現する設計（`Complex` を使わない）は問題ファイル冒頭で意識的に決めた選択。`Mathlib.Analysis.Complex` は import 重量が大きいので避け、`(z.1, z.2)` の組として手書き。`cube : ℝ × ℝ → ℝ × ℝ` を 1 関数として定義するだけで済んだので元は取れた。

## 2. 数学的方針

### (1)

z = (x, y) (x² + y² = 1)、α = −3 のとき w = (z + 3)³。

- `Im(w) = y(3(x+3)² − y²)`、`|w| = (10+6x)^{3/2}`
- ψ = arg(z+3) として **sin θ = sin 3ψ = 3 sin ψ − 4 sin³ ψ**（三倍角）
- t := y/√(10+6x) と置くと sin θ = 3t − 4t³

ステップ:

1. `t² ≤ 1/9`：x² + y² = 1 と (3x+1)² ≥ 0 より 9y² ≤ 10 + 6x。
2. `|3t − 4t³| ≤ 23/27`：キーの分解
   ```
   2(23 − 81t + 108t³) = (3t − 1)²(24t + 31) + 15(1 − 9t²)
   ```
   `t ≥ −1/3` より `24t + 31 > 0`、`t² ≤ 1/9` より `1 − 9t² ≥ 0`、よって右辺 ≥ 0。
3. 逆向きは中間値の定理：上半円 `f(x) := sinTheta(x, √(1−x²))` は `[−1, −1/3]` 上で連続、`f(−1) = 0`, `f(−1/3) = 23/27` なので `IVT` で `[0, 23/27]` を網羅。負側は下半円で対称。

### (2)

ω = e^{2πi/3} として、`(z − α)³ ∈ ℝ_{>0} ⇔ z − α ∈ ℝ_{>0}{1, ω, ω²}`、`(z − α)³ ∈ ℝ_{<0} ⇔ z − α ∈ ℝ_{>0}{−1, −ω, −ω²}`。α からの 6 方向（kπ/3, k=0..5）のうち偶 k と奇 k からそれぞれ少なくとも 1 本が単位円と交わる必要がある。

α が単位開円板内なら任意の方向の半直線が単位円と交わる（α 自身が円内なので）。これが `isGoodAlpha_of_inside` の核。z = (±√(1−α.2²), α.2) を取れば z − α は実軸上で、3 乗して正/負を切り替えられる。

面積 4√3 の積分パートは形式化しなかった（冒頭 docstring 参照）。

数学的アイデアの試行錯誤は **無し**。最初の sketch にあった三倍角と中間値の経路がそのまま最終証明になっている。詰まったのは Lean 翻訳の工程のみ。

## 3. Mathlib 補題探索の実録

| 必要だったもの | 試した名前 | 真の名前 / 場所 | 解決手段 |
|---|---|---|---|
| 中間値定理 (連続関数の像が区間) | `import Mathlib.Topology.Algebra.Order.IntermediateValue` | `Mathlib.Topology.Order.IntermediateValue` | 1 回目の `lake env lean` で「olean does not exist」→ `Algebra.` を削って即解決 |
| IVT の単調減少版 | (記憶頼み) | `intermediate_value_Icc'` | grep `intermediate_value\|ContinuousOn` を T_Q*.lean / B_Q*.lean に打って既存使用例を確認 |
| `√x ^ 2 = x` (x ≥ 0) | `sq_sqrt` | `sq_sqrt` | 一発 |
| `(√x)² = a → √x = √a` 方向の補題 | `sqrt_sq h1` | `sqrt_sq` (但し方向に注意) | 後述 §4.2 |
| `¬(0 ≤ s) → s ≤ 0` | `push_neg at h0` | `(lt_of_not_ge h0).le` | `push_neg` deprecation 警告 → 直接 `lt_of_not_ge` に切替 |

「Mathlib に存在しなかった」もの:

- **`le_or_lt`** — 「0 ≤ s か s < 0 か」で分岐したくて `rcases le_or_lt 0 s with h | h` と書いたら `Unknown identifier`。最終的には `by_cases h0 : 0 ≤ s` に変更（決定可能性の立て方を変えた）。検索コスト 0 の代わりに 1 回の rewrite を要した。教訓：実数の二択は `le_or_lt` でも `lt_or_ge` でもなく、Mathlib では `by_cases` が最も安定。

- **`sqrt_div`** で `√(8/9) = √8 / 3` を直接 rewrite する補題 — 探さなかった。代わりに `(√8 / 3)² = 8/9` を `sq_sqrt` で示してから `sqrt_sq` で逆方向に取る 5 行の補題 `sqrt_eight_ninths_eq` を書いた。教訓：sqrt の比に関する rewrite は等式の方向と分母の正値を両方扱う必要があり、定式化済みの単一補題に依存しない方が安全。

## 4. 試行錯誤と後戻り

### 4.1 `import Mathlib.Topology.Algebra.Order.IntermediateValue` が存在しなかった

**症状**: 1 回目の Write 直後の `lake env lean Common2026/T_Q5.lean` が `error: object file 'Mathlib/Topology/Algebra/Order/IntermediateValue.olean' does not exist`。

**原因**: Mathlib のディレクトリ構造を記憶ベースで推測して `Algebra.Order` の下にあると勘違い。実際は `Mathlib/Topology/Order/IntermediateValue.lean`。

**抜け方**: `find .lake/packages/mathlib/Mathlib -name "IntermediateValue*.lean"` を 1 回打って正しいパス確定。1 文字 Edit で修正。

**教訓**: Mathlib のサブディレクトリ階層は 4〜5 階の深さがあり、`Algebra` `Order` `Topology` の組み合わせ順序を記憶で当てるのは無理。最初に `find` を打つコストは安い（1 回の Bash）。将来のツールは「import path を提案する前に `find` で実在確認する」プリチェック。

### 4.2 `sqrt_sq` の方向性ハマり（最初の Write を全置換した直接の原因）

**症状**: 1 回目の Write で `sqrt_eight_ninths_eq : √(8/9) = √8 / 3` を以下のように証明しようとした:

```lean
private lemma sqrt_eight_ninths_eq : sqrt (8 / 9 : ℝ) = sqrt 8 / 3 := by
  rw [show (8 / 9 : ℝ) = 8 / 3 ^ 2 from by norm_num]
  rw [sqrt_div ...]
```

→ `Tactic 'rewrite' failed: Did not find an occurrence of the pattern √?m.76 / ?m.76`。

`Eq.symm (sqrt_sq h1)` も書き間違えて型不整合：

```
Eq.symm (sqrt_sq h1) has type √8 / 3 = √((√8 / 3) ^ 2)
but is expected to have type √((√8 / 3) ^ 2) = √8 / 3
```

**原因**: `sqrt_sq : 0 ≤ a → √(a²) = a` の方向は「中身が平方の sqrt」→「中身」。逆向き（「√8/3」を「√((√8/3)²)」に書き戻す）にしようとして `Eq.symm` を逆に当てた。さらに `sqrt_div` の引数パターンが (a / b) ではなく特定の正値性付き形を要求するので、`8 / 3 ^ 2` の rewrite では一致しなかった。

**抜け方**: Write で全置換（13:35:36）。修正後の証明はまったく別の構造：

```lean
have h : (sqrt 8 / 3 : ℝ) ^ 2 = 8 / 9 := by
  rw [div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 8)]
  norm_num
have h1 : (0 : ℝ) ≤ sqrt 8 / 3 := div_nonneg (sqrt_nonneg _) (by norm_num)
rw [show (8 / 9 : ℝ) = (sqrt 8 / 3) ^ 2 from h.symm]
exact sqrt_sq h1
```

つまり「`(√8/3)² = 8/9`」を先に作っておき、`8/9` を `(√8/3)²` に書き換えてから `sqrt_sq` で剥がす。方向を一方通行にして `Eq.symm` を使わない設計。

**教訓**: `sqrt`/`sq` の rewrite は「どっちが target、どっちが known」を 1 行ずつ書き出して向きを固定するのが安全。`Eq.symm` を組み合わせると失敗時に「方向間違い」と「pattern 不一致」の区別が付かない。将来のツールは `sqrt`/`sq` を含む goal でユーザが `rw` を書いたとき、左右両方の rewrite を試して通る方を提案する。

### 4.3 `push_neg` の deprecation

**症状**: 4 回目の `lake env lean` で `warning: 'push_neg' has been deprecated. Prefer using 'push Not' instead.`

**原因**: 1 回目の Write で `· push_neg at h0` と書いた。Mathlib 最新で deprecate された。

**抜け方**: `(lt_of_not_ge h0).le` に直接置換（1 Edit）。`push_neg` を経由する必要すら無かった。

**教訓**: 否定の取り扱いは `push_neg` ではなく `not_lt.mp` / `not_le.mp` / `lt_of_not_ge` などの単発補題で書く方が deprecation に強い。

### 4.4 (1) の最初の Write は 5 件のエラーを出した

最初の `lake env lean` 出力（13:32:35）:

```
:126:2: error: No goals to be solved
:194:8: error: No goals to be solved
:238:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern √?m.76 / ?m.76
:250:2: error: Type mismatch (Eq.symm (sqrt_sq h1) の方向)
:401:11: error(lean.unknownIdentifier): Unknown identifier `le_or_lt`
:401:29: error: Tactic `rcases` failed: `x : ?m.65` is not an inductive datatype
```

`No goals to be solved` 2 件は `field_simp` 直後に冗長な `rw` を打った系。`sqrt` まわり 2 件は §4.2、`le_or_lt` 1 件は §3 の表参照。

中間に 1 度 Edit を試みたが（13:32:21、import 修正のみ）、本体エラーは依然 5 件。**3 連続 lake env lean で同じエラーが出た時点で「個別 Edit ではなく Write 全置換」に切り替え**（13:35:36）。これは Q4 の §4.4 の `head -N` 二分探索とは逆の判断（複数箇所が壊れているので一括書き直しの方が早い）。

**教訓**: 同じファイルで 3 回連続同じエラーが出たら、Edit を捨てて Write で全置換を検討。エラー件数が 5 を超えると個別修正のコストが Write を超える。

## 5. ボトルネックではなかったもの

- **数学のアイデア** — 三倍角と中間値定理の組み合わせは最初の sketch のまま。試行錯誤の余地が無かった。
- **連続性の証明** — `ContinuousOn.div`, `ContinuousOn.mul`, `Real.continuous_sqrt.comp_continuousOn` を組み合わせるだけで 1 回も詰まらなかった。
- **(2) の設計** — 「単位開円板 ⊂ GoodSet」だけ示せば良いと割り切ったのが効いた。ターン (2) の lake env lean は 1 回で通った（エラー 0）。
- **コンテキスト長** — cache_read 11.6M tokens で全く圧迫なし。
- **問題理解** — PDF 1 回読み + 既存 T_Q*.lean を 4 ファイル流し読みで終わり。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | `import Mathlib.X.Y.Z` の存在事前チェック（fuzzy match 提案） | §4.1 の 1 回 lake 失敗 + 1 find + 1 Edit が消える |
| 高 | `sqrt`/`sq` を含む rewrite の双方向自動試行 | §4.2 の Write 全置換（実質 1 回の rewrite で済むはず） |
| 中 | 同一ファイルで 3 回連続同じ lake エラーが出たら「Write 全置換」を提案 | §4.4 の判断遅延を 1 ターン早める |
| 中 | `push_neg` 等 deprecated tactic の自動置換 | §4.3 の 1 Edit |
| 低 | Mathlib の決定可能性 (`le_or_lt` vs `by_cases` vs `lt_or_ge`) の選択ガイド | 1 回の rewrite |

このセッションは「Mathlib 検索は軽いが、`Real.sqrt` の rewrite と import path が地雷」型。**補題検索ツールよりも path/rewrite の事前検証ツールが ROI 高い**。Q4 と合わせると「sibling-import lint」「sqrt-rewrite 双方向試行」「冗長 ring 検出」「import path fuzzy match」あたりが共通インフラとして欲しくなる。

## 7. 補足

### 採らなかった代替案

- **`Complex` を使う**: `Mathlib.Analysis.Complex.Basic` を import すると `Complex.arg` / `Complex.exp` まわりの API が使えるが、import 重量が増える上に「`(z − α)³` を実部・虚部に展開する」工程は結局必要。`ℝ × ℝ` を素のまま扱う方が浅く済んだ。
- **(2) の面積 4√3 まで形式化**: `∫_{2/√3}^2 r·arcsin(1/r) dr` の 部分積分は Mathlib の `MeasureTheory.integral_*` 経由で書けるが、`integral_mul_deriv_eq_deriv_mul` 系の補題を 3〜4 段重ねる必要があり、ファイルが 1500 行を超える見積もり。問題の主旨（位相条件）と独立な計算なので docstring 略述で割り切った。
- **`fUpper` / `fLower` を `Set.Icc (-1) 1` 全域で連続性を出してから IVT を打つ**: 当初の設計はそうだった。最終的には `[−1, −1/3]` への mono で十分（`f(−1/3) = 23/27` までを覆えば良い）と気づいて狭めた。`mono` 経由の連続性継承は 1 行で書ける。

### 実際に打った主要 Bash 系列（時系列）

```
ls Common2026/ | head -50                              # スタイル参照
wc -l Common2026/T_Q*.lean                              # 既存問題の規模感
cat Common2026.lean                                     # ライブラリ root
grep -rn "intermediate_value\|ContinuousOn" Common2026/T_Q*.lean Common2026/B_Q*.lean
grep -rn "sqrt" Common2026/B_Q*.lean                    # sqrt 使用例
lake env lean Common2026/T_Q5.lean | head -150          # 1 回目: import path エラー
find .lake/packages/mathlib/Mathlib -name "IntermediateValue*.lean"
lake env lean Common2026/T_Q5.lean | head -200          # 2 回目: 5 件のエラー
lake env lean Common2026/T_Q5.lean | head -100          # 3 回目: 同じ 5 件
... (Write 全置換)
lake env lean Common2026/T_Q5.lean | head -50           # 4 回目: deprecation 警告のみ
... (Edit で push_neg → lt_of_not_ge)
lake env lean Common2026/T_Q5.lean                      # 5 回目: silent
... (ターン 2 開始)
lake env lean Common2026/T_Q5.lean | head -50           # 6 回目: silent
lake env lean Common2026/T_Q5.lean | head -30           # 7 回目: silent
lake build Common2026.T_Q5                              # 最終確認
```

WebSearch / WebFetch / Glob は 0 回。Grep は 2 回（既存使用例の確認のみ）。

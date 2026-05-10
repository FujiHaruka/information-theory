# 東大 2026 第4問 Lean 形式化 — ボトルネック分析

将来「多項式恒等式を Lean 上で押し回す」型の問題向けに、`private` 可視性 / `field_simp` 連鎖 / 場合分け爆発を自動回避するエージェントを作るためのベースライン記録。

**定量データ**: [docs/metrics/todai-2026-q4.metrics.md](../metrics/todai-2026-q4.metrics.md)

## 0. 対象問題と成果物

東大 2026 数学 第4問:

> 実数 k と曲線 C: y = x³ − kx について、原点 O と C 上の相異なる 2 点 P, Q を考える。
> 接線 (O, P, Q) のうちどの 2 本も交わり、なす角がすべて π/3 となる条件 (*) を考える。
> (1) (*) を満たす P, Q が存在する k の範囲を求めよ。
> (2) k が (1) の範囲のとき、3 本の接線が囲む三角形の面積 S の最大値 M と最小値 m について、M = 4m となる k を求めよ（3 直線が一点で交わるときは S = 0）。

成果物:

- `Common2026/T_Q4_1.lean` — 481 行、`theorem existence_iff`：`Nonempty (Config k) ↔ √3/3 < k`。
- `Common2026/T_Q4_2.lean` — 526 行、`theorem main_part2`：`(M, m が存在し M = 4m) ↔ k = 5√3/12`。
- `lake env lean` 両ファイルともクリーン通過、`sorry` ゼロ、警告ゼロ。

## 1. 問題のキャラクター

**「多項式恒等式を Lean 上で押し回す」**型。Mathlib の特殊補題はほぼ要らず、`ring` / `linarith` / `nlinarith` / `field_simp` / `linear_combination` で代数を回す。

過去問との比較:

| 問題 | 支配工程 | Mathlib 検索の重さ | 補助計算機構 |
|---|---|---|---|
| Q1 (微積分) | Mathlib 部品呼び出し | 重い | `MeanValue` 系 |
| Q2 (Finset 場合分け) | 256 ケースの数え上げ | 中 | `decide`, `Finset.card` |
| Q3 (座標 + 除算) | `set` + `field_simp` の戦い | 軽い | `nlinarith` ヒント |
| **Q4 (代数恒等式)** | **多項式の押し回し + 場合分け爆発の制御** | **0**（Grep ゼロ） | `ring`, `linear_combination` |

Q4 は **Mathlib 検索 0 回 / Grep 0 回 / WebSearch 0 回** で終わった。代わりに `lake env lean` 9 連打で軌道修正する Lean 構文との戦いに集中した。

## 2. 数学的方針

### (1)

接線の傾き：O で `−k`, x = a で `3a² − k`。なす角 π/3 の条件 `(m₁ − m₂)² = 3(1 + m₁m₂)²` を平方差として因数分解：

`3(p²)² = (1 + k² − 3kp²)² ⇔ ((1+k²−3kp²) − √3·p²)((1+k²−3kp²) + √3·p²) = 0`

⇒ `p²` は `(3k+√3)·u = 1+k²` か `(3k−√3)·u = 1+k²` のどちらかの根。`p² ≠ q²` (hPQ 由来) と `1+k² > 0` から、`p², q²` は別側を取り、両方の係数が正 ⇔ `k > √3/3`。

### (2)

接線の交点座標から `S = 2 p² q² |p−q| / (3 |p+q|)`。`{p², q²} = {α², β²}` (α := mkP k, β := mkQ k) なので、対称式 `(p+q)² + (p−q)² = 2(α² + β²)` と `(p+q)²(p−q)² = (α²−β²)²` から `{(p+q)², (p−q)²} = {(α+β)², (β−α)²}` を導出。S は 2 値:

- `areaMinus = 2α²β²(β−α) / (3(α+β))` （p, q 同符号）
- `areaPlus = 2α²β²(α+β) / (3(β−α))` （異符号）

両方達成可能で `areaPlus / areaMinus = ((α+β)/(β−α))² > 1`。M = 4m ⇔ `(α+β) = 2(β−α)` ⇔ `β = 3α` ⇔ `(3k+√3)/(3k−√3) = 9` ⇔ **k = 5√3/12**。

数学的アイデアの試行錯誤は無し。**最初の Math summary（10:22）に書かれた方針がそのまま最終証明になっている**。詰まったのは Lean に翻訳する工程のみ。

## 3. Mathlib 補題探索の実録

このセッションでは **Grep / WebSearch / WebFetch をそれぞれ 0 回**。Bash の Mathlib 検索も 0 回（実行された Bash は `lake env lean` 9 / `lake build` 2 / `ls` 1 のみ）。

検索は記憶頼みで、`lake env lean` のエラーから補題名を引き直すスタイル。

| 必要だったもの | 試した名前 | 真の名前 | 解決手段 |
|---|---|---|---|
| `(¬ a < b) → b ≤ a` | `push_neg at h_ge`（古い） | `not_lt.mp` | `Unknown identifier` 警告 → `le_of_not_lt` を試す → さらに deprecation で `not_lt.mp` に到達（2 段階迂回） |
| `a · b > 0 → a > 0`（左因子正と仮定） | (直接記憶) | `mul_pos_iff_of_pos_left` | 一発 |
| `a / b = c / d` の clearing | (直接) | `field_simp` + `ring` | `field_simp` 単独で十分なケース・`ring` も必要なケースの判別ミスで 1 回後戻り |
| `a, b ≥ 0 ⇒ a² = b² ↔ a = b` | (Mathlib にありそうだが探さず) | 自前 `sq_eq_iff_of_nonneg` | T_Q4_2 冒頭に 8 行で書き下し |

「Mathlib に存在しなかった（か、探さなかった）」もの:

- **`sq_eq_iff_of_nonneg`** — 非負実数の平方の単射性。「あるはず」と思いつつ Mathlib 探索 0 回で自前定義。`(a − b)(a + b) = 0` を `mul_eq_zero` で割ってから linarith 2 連打。`pq_abs_partition` と `mkQ_eq_three_mkP_iff` で 2 回再利用したので元は取れた。教訓：「探さない」決断のコスト（再利用 2 回 / 8 行）は小さく、検索試行コスト（仮に 5 分）より安い場合がある。

## 4. 試行錯誤と後戻り

### 4.1 `private` 可視性の連鎖修正

**症状**: T_Q4_1.lean を `A_Q1_1.lean` のスタイルに合わせて補助補題を全部 `private lemma` で書いた。T_Q4_2.lean が import した瞬間に `mkConfig_hOP`, `mkConfig_hOQ`, `mkConfig_hPQ`, `p_sq_root`, `q_sq_root`, `three_k_add_sqrt3_pos`, `three_k_sub_sqrt3_pos`, `sqrt3_sq` などが軒並み「unknown identifier」。

**原因**: 同じ問題を `_1` `_2` に分割した時点で「補題は全部 private」のスタイル仮定が破綻していた。Lean の `private` はモジュール越境では完全に隠蔽される。

**抜け方**: 8 連続 Edit で `private` を機械的に剥がした（10:55:26 〜 10:55:54、約 30 秒に 8 回）。一括置換で済むがキーワード境界の取り扱いを慎重にしたかったので一個ずつ剥がした。

**教訓**: 同じ問題を `_1` `_2` に分けるなら、`_1` の helper は最初から `private` を付けない。あるいは「import で公開予定」のフラグを建てておく。将来のツールは「同名 prefix の sibling ファイルが import 関係にある場合、`private` を warning する」ような lint をかけられると 8 Edits / 30s が消える。

### 4.2 場合分け爆発の途中放棄

**症状**: T_Q4_2 の最初の Write（10:51:05）で、`triArea_eq` を `p, q` の符号 4 ケースで場合分けして書こうとしたら、各ケースの `|p−q|` `|p+q|` の符号判定が爆発した（4 × 2 × 2 = 16 ケース）。

**原因**: 三角形面積の公式が `|p−q|, |p+q|` で書かれているのに、Config の `p, q` を直接動かして符号場合分けすると、本質的に同じ恒等式を 16 回繰り返すことになる。

**抜け方**: 3 分後に 1 回 abort し、対称式 `(p±q)²` を経由する設計に書き換えた（10:54:14 の 2 度目の Write）。`pq_diff_sum_partition` で `{(p−q)², (p+q)²} = {(α+β)², (β−α)²}` を出してから `sq_eq_iff_of_nonneg` で平方根を取る、の 2 段。これで本質的に 2 ケースで済んだ。

**教訓**: 「絶対値 / 符号で場合分け」を見たら、まず「対称式に上げて場合数を半減できないか」を考える。将来のツールは「ケース数 N が方針提案の段階で見えるなら、N=4 を超えたら別ルートを提案」のヒューリスティクスが効く。

### 4.3 `field_simp; ring` の過剰応用

**症状**: `four_aMinus_eq_aPlus_iff` 内で `field_simp` のあとに `ring` を打ったら「unsolved goals」。

**原因**: `field_simp` は分母を払って多項式恒等式に整形する時点で `ring_nf` 相当を内部で走らせている。続く `ring` がさらに正規形を変えて goal が崩れた。

**抜け方**: `ring` を削除（11:01:33 の 1 回 Edit）。同じ理由で `mkQ_eq_three_mkP_iff` の証明内 `show ... from by field_simp; ring` も `ring` を削った。

**教訓**: `field_simp` 直後に `ring` を盲目的に書かない。閉じる必要があれば `field_simp; ring` ではなく `field_simp` 単独で試して、残ったら `ring` を追加。将来のツールは「`field_simp` の直後の `ring` は冗長な可能性が高い」を警告できる。

### 4.4 `lake env lean ... | head -N` の二分探索

**症状**: T_Q4_2 のコンパイル後に複数行のエラーが出るので、`lake env lean Common2026/T_Q4_2.lean 2>&1 | head -200` → `head -100` → `head -80` → `head -60` → `head -30` と順に絞り込んだ（10:51:59 〜 10:55:20、4 連 lake 実行）。

**原因**: 1 つのエラーを潰すと先のエラーが読めるので、`head -N` の N を小さくして「どこまで通った」を確認する人力二分探索。LSP が `<new-diagnostics>` を返してくれれば本来不要なはずだが、新規 Write 直後の diagnostics は遅延が出ることがある。

**抜け方**: 各回で 1〜2 個のエラーを修正して再実行。最終的に 10:55:30 で T_Q4_1 への `private` 剥がしと連鎖して T_Q4_2 のエラーも消えた。

**教訓**: `head -N` 漸減の運用は冗長。最初に `lake env lean ... 2>&1 | sed -n '/error/,+5p'` のような「エラー周辺だけ抜く」関数を持っておくと早い。将来のツールは「Lean エラー出力をエラーごとにグループ化して 1 件ずつ提示する」ラッパーが欲しい。

## 5. ボトルネックではなかったもの

- **数学のアイデア** — 最初の 1 分で書いた方針がそのまま最終証明になった。試行錯誤の余地が無かった。
- **Mathlib 検索** — Grep 0 回 / WebSearch 0 回。`linear_combination`, `field_simp`, `nlinarith`, `mul_left_cancel₀`, `mul_pos_iff_of_pos_left` などはすべて記憶ベースで一発出し。
- **型チェック** — `Real.sqrt` まわりの `≥ 0` 引数で 1 回詰まった以外は `linarith [sqrt3_pos]` 的な定型で潰せた。
- **コンテキスト長** — 1M context で全く圧迫感なし（cache_read 12M tok）。
- **問題理解** — PDF を 1 回読んで終わり。`AngleEq60` の定義 `(m₁ − m₂)² = 3(1 + m₁m₂)²` を最初に提示できたのが効いた（`tan(π/3) = √3` から平方を取ると平行/直交が自動排除される観察を、`linear_combination` を使う前に 1 行で済ませた）。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | sibling file import 時の `private` lint | §4.1 の 8 連続 Edit / 30s が消える |
| 高 | Lean エラー出力のエラー単位グルーピング | §4.4 の 4 連 lake `head -N` 二分探索が 1 回で済む |
| 中 | `field_simp` の直後 `ring` 冗長性チェック | §4.3 の 1〜2 Edit が消える |
| 中 | 「絶対値場合分け」検出 → 対称式リフト提案 | §4.2 の 1 回 abort と再設計が初手で済む（推定 5〜10 分） |
| 低 | 型ベース lemma 検索 (`Mathlib.contains : a, b ≥ 0 → a² = b² ↔ a = b`?) | このセッションでは 8 行の自前補題で済んだので低 |
| 低 | deprecation chain (`push_neg`/`le_of_not_lt`/`not_lt.mp`) の自動マイグレーション | 1 ケースのみ |

このセッションは「Mathlib 検索が問題ではない」「Lean 構文の細かい摩擦が累積する」型なので、**補題検索ツールより lint / refactor 提案ツールの方が ROI が高い**。

## 7. 補足

### 採らなかった代替案

- **接線の傾き条件を `Real.tan` で書く**: `Real.tan (π/3) = √3` を経由すると `Real.tan` まわりの境界条件（極での未定義など）に巻き込まれる。`(m₁−m₂)² = 3(1+m₁m₂)²` の代数形に最初から落としたのが正解だった。
- **`triArea` を `Real.abs` ではなく `(p−q)·sign` で定義**: 符号管理が爆発する（§4.2 と同じ問題）。

### 実際に打った主要 Lean コマンド系列（時系列）

```
ls Common2026/T_*.lean              # スタイル参照
lake env lean Common2026/T_Q4_1.lean | head -150  # 最初の skeleton
... (T_Q4_1 修正後 silent)
lake env lean Common2026/T_Q4_2.lean | head -200  # 1 度目の Write 後、エラー多数
lake build Common2026.T_Q4_1                       # T_Q4_2 視点で olean を更新
lake env lean Common2026/T_Q4_2.lean | head -100   # 二分探索
lake env lean Common2026/T_Q4_2.lean | head -80
lake env lean Common2026/T_Q4_2.lean | head -60
lake env lean Common2026/T_Q4_2.lean | head -30    # 残 1 件
lake build Common2026                              # 最終確認
lake env lean Common2026/T_Q4_1.lean Common2026/T_Q4_2.lean | head -20
lake env lean Common2026/T_Q4_1.lean && lake env lean Common2026/T_Q4_2.lean | head -10  # silent
```

外部 Web 検索 / Grep は 0 回。

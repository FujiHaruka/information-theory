# 東大 2026 第3問 Lean 形式化 — ボトルネック分析

将来 Mathlib 補題検索を支援するツール / `set` + `field_simp` の罠を回避するタクティク提案エージェントを作るためのベースライン記録。

**定量データ**: [docs/metrics/todai-2026-q3.metrics.md](../metrics/todai-2026-q3.metrics.md)

## 0. 対象問題と成果物

東大 2026 数学 第3問:

> 座標空間内の原点を中心とする半径 5 の球面 S 上に、相異なる 3 点 P, Q, R が動く。条件は (i) P, Q は xy 平面上、(ii) 三角形 PQR の重心が G(2, 0, 1)。
> (1) 線分 PQ の中点 M の軌跡を求めよ。
> (2) 線分 PQ の通過する範囲を図示せよ。

成果物:

- `Common2026/T_Q3_1.lean` — 287 行、`theorem locus_iff`：M の軌跡 ⇔ 円 (x−3)² + y² = 4 から (5, 0) を除いたもの。
- `Common2026/T_Q3_2.lean` — 434 行、`theorem swept_range_iff`：通過範囲 ⇔ 大円板 ∩ 双曲線 5(x−3)² − 4y² ≤ 20 から (5, 0) を除いたもの。
- `lake build Common2026` クリーン通過、`sorry` ゼロ。

## 1. 問題のキャラクター

座標計算と除算を交えた**陽な代数構成**が支配項。Mathlib 検索は最小限で済み、「`Real.sqrt` を使った陽な構成 → 多項式恒等式 → 線形条件」の素朴な計算をどう Lean に飲み込ませるかが本体。Q1（微積分）が「Mathlib の部品呼び出し」型、Q2 が「区間と Finset 場合分け」型だったのに対し、Q3 は **「`set` で名付けた中間変数を `field_simp` から守るゲーム」** 型だった。

## 2. 数学的方針

P = (p₁, p₂, 0), Q = (q₁, q₂, 0), R = (r₁, r₂, 3) と置くと、球面と重心の条件から

- p₁² + p₂² = 25, q₁² + q₂² = 25
- r₁ = 6 − 2x, r₂ = −2y（M = (x, y) は中点）
- r₁² + r₂² = 16

### (1)

M の代数条件は `(6 − 2x)² + 4y² = 16 ⇔ (x − 3)² + y² = 4`。M = (5, 0) では弦が退化（P = Q）するので除外。

### (2)

A = (x, y) が線分 PQ 上 ⇔ A・M = |M|² (弦の中点性) かつ |OA|² ≤ 25 (端点の内側)。M を陽に動かして整理すると:

- 線形条件 `(6 − x) m − y n = 5`
- 中点軌跡 `(m − 3)² + n² = 4`

の両立条件は、中心 (3, 0) から直線までの距離 ≤ 2 ⇔ Cauchy–Schwarz より `(3x − 13)² ≤ 4 ((6 − x)² + y²) ⇔ 5(x − 3)² − 4y² ≤ 20`。右枝が円板と交わるのは (5, 0) のみで、これが除外点に対応する。

「Cauchy–Schwarz で線形条件を不等式化する」という発想に着いてからは一直線。**気づくのに時間がかかった部分は無く**、Mathlib 検索ではなく Lean 構文との戦いに費用が集中した。

## 3. Mathlib 補題探索の実録

このセッションでは **WebSearch / WebFetch / Mathlib への grep を 0 回**しか使っていない。検索は記憶頼みで、`lake env lean` のエラーで軌道修正するスタイル。

| 必要だったもの | 試した名前 | 真の名前（最終）| 解決手段 |
|---|---|---|---|
| `(¬ a < b) → b ≤ a` | `le_of_not_lt` | `not_lt.mp` | `Unknown identifier` を見て記憶を引き直し |
| `a/c + b/c = (a+b)/c` | `div_add_div_same` | `← add_div` | `Unknown identifier` → 別名を再試行 |
| `a / b = c → a = c * b` | `field_simp at h1` でリライト | `(div_eq_iff hD_ne).mp h1` | `field_simp` が atomic 変数を展開して破綻 |
| Cauchy–Schwarz の積形 | (探索しなかった) | `nlinarith [sq_nonneg ((6 - A.1)*b + A.2*a)]` | 古典恒等式 `(ax−by)² + (ay+bx)² = (a²+b²)(x²+y²)` を手で出してヒントにした |

「Mathlib に存在しなかった」もの:

- **`le_of_not_lt`** — Lean 4 / Mathlib では `not_lt.mp` が正解（旧 Lean 3 系の英語直訳でハズレ）。一発で `Unknown identifier` が出てすぐ修正。
- **`div_add_div_same`** — Mathlib にはこの名前で存在しない。`add_div : (a + b) / c = a / c + b / c` を逆方向 rewrite (`← add_div`) する。一発でハズレ。

両方とも「英語自然語 → snake_case 直訳」での検索失敗。**型ベースの自然言語検索（loogle 風）があれば即解決**するパターン。

## 4. 試行錯誤と後戻り

### 4.1 `set` で名付けた変数を `field_simp` が let-展開する

**状況**: T_Q3_2 逆方向の `(m − 3)² + n² = 4` の証明で、`m := 3 + a/D`, `n := b/D` のように `set` で導入し、`a² + b² = 4 D²` を経由して

```
4 * D^2 / D^2 = 4
```

を `field_simp` で閉じようとした。

**原因**: `set` は本体に `let` を残すため、`field_simp` がその `let` を展開して D を `(6 − x)² + y²` に戻し、目標が巨大な多項式になった（出力ログに `-468 + x*264 - x*y*sqrtE*2 - x*y²*3 ...` という展開が観測された）。

**抜け方**: `clear_value a b D` を直前に挟み、`a`, `b`, `D` を atomic な仮定に変える。これで `field_simp` は分子・分母と乗除のみクリアして、多項式展開を起こさなくなる。

**教訓**: `set` で導入した名前は `field_simp` から自動では守られない。**「`set` ＋ `field_simp` = 必ず `clear_value` を挟む」**は機械的に提案できるパターン。タクティク使用時の lint として実装する価値がある。

### 4.2 線形結合の符号ミスに `ring` 経由で気付く

**状況**: a := 分子1, b := 分子2 として `(6 − x)·a + y·b = D · (3x − 13)` を経由しようとした。実際には `+ y·b` ではなく `− y·b` でないと sqrtE 成分が消えない。

**原因**: 紙の上で展開を端折って符号を一つ間違えた。

**抜け方**: `ring` がエラーを出して気付き、Edit 1 回で `+` → `−` に修正。

**教訓**: `ring` は「符号レベルの計算チェッカ」として機能はするが、デバッグサイクルが Edit → `lake env lean` 起動 → エラー読みで分単位かかる。**chiral な代数恒等式は ring に投げる前に CAS で 1 度検算する**のが速い。将来のツールが「ユーザーが `ring` で示そうとしている等式を Wolfram Alpha 互換の入力形に変換 → 即時検算」してくれると体験が良い。

### 4.3 `unfold midpointOf at hM1_eq` が let に対して効かない

**状況**: `noncomputable def midpointOf cfg : ℝ × ℝ := ((P.1+Q.1)/2, (P.2+Q.2)/2)` を `unfold` で展開しようとした。

**原因**: `def` の中身が tuple でも、Lean 4 の `unfold` は本体に `let` が混ざっているとそのままでは展開しないことがある。

**抜け方**: `lemma midpointOf_fst (cfg) : (midpointOf cfg).1 = (cfg.P.1 + cfg.Q.1) / 2 := rfl` のような **射影付き補助補題を用意して `rw` で叩く**。

**教訓**: `def` に `unfold` を直接打つのは脆い。**ペア型 def には射影 lemma を最初から自動生成する `@[simps]` 風アトリビュートが定石**。これは Mathlib にあるのを呼べばいいだけだが、その存在を思い出すコストが本セッションでは大きかった。

### 4.4 `noncomputable` 漏れ

**状況**: `def midpointOf := ((P.1+Q.1)/2, ...)` でいきなりエラー:

> failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Real.instDivInvMonoid', which is 'noncomputable'

**原因**: 実数除算は `noncomputable`。

**抜け方**: `noncomputable def` に変更（Edit 1 回）。

**教訓**: 機械的に判定可能。**「実数演算を含む def は最初から noncomputable」**を提案する linter がほしい。

### 4.5 `rw [div_le_iff₀ hσm_sq_pos]` のパターン照合失敗

**状況**: `(6m − 5)·(y − n)² / ((30 − 6m) · m²) ≤ 1` を示すため、`div_le_iff₀ hσm_sq_pos` を打った。`hσm_sq_pos : 0 < (mkσ m * m)^2`。

**原因**: 直前の `rw [mul_pow, hρ_sq, ...]` で `(mkσ m * m)^2` が `(30 − 6m) * m^2` に既に書き換わっており、`div_le_iff₀` のパターン `?m / (mkσ m * m)^2` がマッチしなくなっていた。

**抜け方**: 順序を入れ替え、`div_le_one (by positivity : ...)` を先に打って `≤ 1` を消費 → その後で `mul_pow, hρ_sq, hσ_sq` の順に rewrite。

**教訓**: `rw` は **順序敏感**で、一度書き換わったパターンは戻せない。「分母の `_pos` 補題は分母を rewrite する前に消費」というベストプラクティスはある。**将来のツールが `rw` 列をシミュレーションし、後段の補題が前段で消えるパターンを警告**できると良い。

### 4.6 `field_simp; ring` の「No goals to be solved」

**状況**: `field_simp; ring` と書いたら `ring` が `No goals to be solved` で失敗。

**原因**: `field_simp` は分子分母を整理した結果、項そのものを完全に閉じることがある。

**抜け方**: Edit 1 回で `; ring` を削除。

**教訓**: `field_simp` は「`ring` の前段」と機械的に組まないほうが安全。**`field_simp <;> try ring`** のような防御パターンを定形化したい。

### 4.7 `nlinarith` を一発で通すには「ヒント補題」が必要

**状況**: u² ≤ 1 を `u := mkρ m * (n - y) / (mkσ m * m)` に対し直接 `nlinarith [hLine, hMsq, hDisk, sq_nonneg ...]` で示そうとして通らなかった。

**原因**: `nlinarith` は積の連鎖を勝手にはやらない（仕様）。

**抜け方**: 鍵不等式 `(6m − 5)(y − n)² ≤ (30 − 6m) m²` を `key_sq_ineq` という補助補題に切り出し、内部で

1. `m(x − m) = −n(y − n)`（線形条件と m² + n² = 6m − 5 から）
2. `m²(x−m)² = n²(y−n)²`（両辺二乗）
3. `m²((x−m)² + (y−n)²) = (6m−5)(y−n)²`
4. `|A − M|² ≤ 30 − 6m`（disk から）

を逐次 `linarith` / `nlinarith` で繋いだ。

**教訓**: 大きな二次不等式は **必ず補助補題に切り出す**。`nlinarith` を「魔法の自動証明」と思って一発を狙うのは時間の無駄。実装では「`nlinarith` 失敗 → ヒント候補を生成して補助補題を提案する」エージェントが効くはず。

### 4.8 LSP のキャッシュで T_Q3_2 が古い T_Q3_1 を見続けた

**状況**: T_Q3_1 を `mkLocusConfig` 公開のためにリファクタしたあと、T_Q3_2 で `Unknown identifier 'mkρ'`, `Unknown identifier 'mkσ'`, `Unknown identifier 'm_ge_one_of_locus'` などの大量の LSP エラー。

**原因**: T_Q3_1 を Edit しても LSP は `lake setup-file` 経由で oleans を rebuild しないため、T_Q3_2 が古い `.olean` を読み続ける（CLAUDE.md にも明記されている既知挙動）。

**抜け方**: `lake build Common2026.T_Q3_1` を明示的に走らせて `.olean` を更新。

**教訓**: 公開シンボルを上流ファイルで変えたら **必ず `lake build <upstream>`**。これはタスク依存解析で機械化できる。

## 5. ボトルネックではなかったもの

- **数学のアイデア** — 主結果（双曲線 ⇔ Cauchy–Schwarz）に到達するのは紙ベースで一直線。`thinking` 中で代数を完了させてから Lean に降ろした。
- **Mathlib の補題探索** — このセッションでは Mathlib への grep / Web 検索は 0 回。記憶ベースで足りた。ただし「無い名前を試す」コストは複数回発生（4 章参照）。
- **コンテキスト長** — 1M context で T_Q3_1 (287 行) と T_Q3_2 (434 行) と PDF を抱えても圧迫感なし。
- **`ring`, `linarith`, `nlinarith`, `positivity`** — それぞれの **得意領域では一発で通る**。問題は「不得意領域に投げて空振りする」コスト（4.7）。
- **型推論** — Real への型統一はトラブルにならず。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | 型ベース lemma 検索（loogle 風） | `le_of_not_lt`, `div_add_div_same` の試行錯誤を即時に潰す |
| 高 | `set` + `field_simp` 警告 / `clear_value` 自動提案 | 4.1 の試行錯誤をまるごと節約 |
| 中 | `rw` 列のシミュレータ（前段で消費されるパターンの警告） | 4.5 のリライト順序ミス |
| 中 | 上流 Lean ファイル変更時の `lake build <upstream>` 自動実行 | 4.8 の LSP キャッシュ起因エラー |
| 中 | `ring`/`linarith`/`nlinarith` 失敗時のヒント候補生成（補助補題提案） | 4.7 の大きな二次不等式 |
| 低 | `noncomputable` linter | 4.4 は機械的だが頻度低 |
| 低 | `field_simp` で `; ring` を自動 try する糖衣 | 4.6 はそもそも体感コストが小さい |

「高」優先度は **WebSearch を 0 回で走り切ってしまう Claude の癖を補完するツール** が中心。記憶ベースだと Mathlib のリネームに追随できず、`le_of_not_lt` のような Lean 3 直訳でハズレが定常的に起きる。型ベースの自然語検索は最も投資効果が高い。

## 7. 補足

- 構成パートの sqrt 構成を最後まで「`set` 派」で押し切ったが、**「raw expression のまま受ける」スタイルに途中で切り替える**選択肢もあった（テキストログで "complete に書き直し set を使わず raw expressions" と判断したが、最終形では `set` を残した）。最終形が読みやすい以上、後判断としてはこれで良い。
- `nlinarith` のヒントに `sq_nonneg ((6 - A.1) * b + A.2 * a)` を使った Cauchy–Schwarz は手書き。Mathlib の `inner_mul_le_norm_mul_norm` 等で代替できる余地はあるが、検索コストが上回ると判断して採用せず。
- 問題文は「図示せよ」だが図描画は行わず、代数的特徴付けだけを返した。`Mathlib.Plot` 等で SVG を吐くオプションは将来検討。

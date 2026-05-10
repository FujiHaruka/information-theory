# 東大 2026 第2問 Lean 形式化 — ボトルネック分析

将来 Mathlib 補題探索ツール / タクティク失敗の説明可能性ツール / 重い tactic を試打する sandbox を作るためのベースライン記録。

**定量データ**: [docs/metrics/todai-2026-q2.metrics.md](../metrics/todai-2026-q2.metrics.md)

## 0. 対象問題と成果物

東大 2026 数学 第2問:

3n 個の格子点 `{(x, y) ∈ ℤ² | 1 ≤ x ≤ 3, 1 ≤ y ≤ n}` から相異なる 3 点を等確率で選び、三角形をなす確率を p_n とする。

- **(1)** p_5 を求めよ → 412 / 455
- **(2)** m ≥ 2 で p_{2m} を求めよ → m(16m − 7) / ((6m − 1)(3m − 1))

成果物:

- `Common2026/T_Q2_1.lean` — 104 行、共通定義 + (1) を `decide` で解決
- `Common2026/T_Q2_2.lean` — 676 行、一般 m での分割数え上げ
- 0 errors / 0 warnings / 0 sorry
- 途中で `Common2026/T_Q2_probe.lean` を作って `decide` の所要時間を測定 → 本体採用後に削除

## 1. 問題のキャラクター

過去問との比較:

| 観点 | T_Q1 (積分) | **T_Q2 (本問)** | T_Q3 (図示) |
|---|---|---|---|
| 支配項 | Mathlib 補題探索 | **Finset 数え上げの設計と Lean 構文** | 不等式の手証明 |
| 主タクティク | 既存補題召喚 | `linear_combination` / `decide` / 場合分け | `nlinarith` / `polyrith` |
| 「無い」判定 | 中 | **多** (`Nat.choose 3` の閉形式が無い) | 少 |
| 分割数え上げ | — | **中核** | — |

q1 が「Mathlib にある部品を呼び出す」型だったのに対し、q2 は **「Finset 上の数え上げを場合分けで書き下す」型**。設計判断と Lean 構文の細部が支配項。

## 2. 数学的方針

### (1) p_5

15 点 = `(15 choose 3) = 455` 通り。3 点が共線になる組み合わせを除外して三角形数を出す。

実装上は、`coll3 a b c` を「クロス積 = 0」で定義 → `Decidable` 派生 → `IsCollinear s := ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ coll3 a b c` を全 3 元集合に渡す。具体値 n=5 では Finset.univ 上の filter とカード比較が `decide` で 17 秒程度で終わる。**(1) 専用の場合分けを書かず一発で答えに到達した**。

### (2) p_{2m}

3n 点から取った相異なる 3 点が共線になるパターンを 2 種類に分割:

- **vertTriples**: 同じ列 (x = c) の 3 点 (3 列 × C(n, 3))
- **lineTriples**: 各列に 1 点ずつで AP (中項の y 座標が両端の平均)

`coll = vertTriples ⊎ lineTriples` の disjoint union を厳密に出すために forward direction (`IsCollinear s ⇒ s ∈ vert ∨ s ∈ line`) を 27 ケース dispatch で処理した。これが 500 行食った最大の理由。

n = 2m に絞ったのは、`lineTriples` の数え上げで「両端の y 座標和が偶数」という条件が、`Fin (2m)` 上で偶/奇の分割で綺麗に `2m²` になるため。一般 n では中項の存在条件がもっと複雑で、奇数/偶数が混ざる。

時間的構造としては「**(2) の分割設計を skeleton 段階で書いた後、補題の返り値の型を後付けで変えた**」のが手戻り発生ポイント (4.1 で詳述)。

## 3. Mathlib 補題探索の実録

定量メトリクス (metrics.md) では grep が 25 回、その他 Bash (`time lake env lean` を含む) が 26 回。grep の試行を時系列で並べると以下の通り。

| 必要だったもの | 最終的な grep クエリ | 試行 | 結果 |
|---|---|---|---|
| `Finset.card_powersetCard` 形式 | `card_powersetCard\|powersetCard.*card` を `Mathlib/Data/Finset/Powerset.lean` で | 2 | 仕様確認のみ、採用せず |
| `Fintype.card_prod` の存在 | `instance.*Fintype.*Prod` を `Mathlib/Data/Fintype/` で | 1 | `import Mathlib.Data.Fintype.Prod` で自動派生されると確認 |
| `Finset.card_univ` の場所 | `card_univ` を `Mathlib/Data/Fintype/` で 3 種 | 3 | `Fintype.card_univ` ではなく `Finset.card_univ` で、import 階層を要修正 |
| `card_filter_add_filter_neg` | `card_filter.*card_filter\|filter_card_add_filter_neg` で 2 種 | 2 | 該当なし。代わりに `Finset.filter_card_add_filter_neg_card_eq_card` を発見 |
| `Finset.card_eq_three` | `card_eq_three` を `Mathlib/Data/Finset/Card.lean` で | 1 | 即発見 |
| `Finset.card_image_of_injective` | `card_image_of_injective\|card_image_of_injOn` で 2 種 | 2 | 即発見 |
| `card_insert_of_not_mem` | snake_case と camelCase 両方 | 1 | `card_insert_of_notMem` (camelCase) が現役と判明 |
| `linear_combination` の import | `Mathlib.Tactic.LinearCombination` 確認 | 1 | 該当 |
| `Prod.ext` の所在 | Mathlib と lean4 の両方 | 4 | core Prelude 由来。Mathlib でなく `Init/Prelude.lean` を見る必要あり |
| `Nat.descFactorial` の補題群 | `descFactorial\b\|Nat\.descFactorial` で `Nat/Factorial/` 配下 | 4 | `descFactorial_eq_div`, `factorial_dvd_descFactorial` を発見 |

「Mathlib に存在しなかった」もの (**特に重要**):

- **`Nat.choose_three_eq` (n.choose 3 = n*(n-1)*(n-2)/6 の閉形式)** — `choose.*succ_eq`、`Nat.choose_three`、`choose_eq_descFact`、`choose_mul_factorial`、`six.*choose_three`、`choose 3 =` の 6 つで `Mathlib/Combinatorics/`、`Mathlib/Data/Nat/Choose/`、`Mathlib/Data/Nat/` を捜索したが発見できず。代わりに `Nat.choose_eq_descFactorial_div_factorial` + `Nat.factorial_dvd_descFactorial` から自前導出 (約 8 行)。**コスト感**: grep に 5 試行ぶんの試行錯誤、自前導出に 10 分前後。
- **「Fin n の偶数値の個数 = ⌈n/2⌉」直接補題** — Mathlib 標準では bijection を組み立てる前提らしく、直接の補題は無し。`fun k : Fin m => ⟨2 * k.val, _⟩ : Fin (2 * m)` で injection を作って `card_image_of_injective` 経由で `2m` を出した。

教訓: いずれも「型ベース検索 (loogle 風) で `Nat.choose ?n 3 = ?` のような問い合わせができれば 1 ステップで『無い』が確定する」型のロス。grep だと「自分が知らない命名」を試すだけになる。

## 4. 試行錯誤と後戻り

### 4.1 `exists_col_match` の返り値設計を後付けで変えた

**状況**: `coll = vert ∪ line` の forward direction を書くにあたり、3 点の (`x` 座標) が「全部同じ」「ちょうど 2 つ同じ」「全部異なる」の 3 ケース分割をした。最後のケースで「3 点を `(p₀, p₁, p₂)` の正規順に並べ替える存在補題」`exists_col_match` が必要になった。

**原因**: 最初は `∃ p₀ p₁ p₂, {p₀, p₁, p₂} = {a, b, c} ∧ p₀.1 = 0 ∧ p₁.1 = 1 ∧ p₂.1 = 2` という Prop だけ返す形で書いた。すると呼び出し側で `IsCollinear {a,b,c}` から `coll3 p₀ p₁ p₂` を出す段で 6 順列のどれが当たるかを再場合分けする羽目になり、行数が倍増した。

**抜け方**: 補題の返り値に「`coll3 a b c → coll3 p₀ p₁ p₂` の関数」を含めることにし、補題側の証明で `coll3` の置換不変性 (`coll3_swap12`、`coll3_swap23`、`coll3_rot` など) を使い分けた。これで呼び出し側は単純に `apply` で済む。

**教訓**: 「skeleton を書く前に、補題のシグネチャを紙レベルで設計する」べき。具体的には **「補題の返り値に変換関数を埋め込んだ方が呼び出し側が薄くなるか」を skeleton 設計時にチェックするチェックリスト** が欲しい。今回は手戻りで 100 行ぶん書き直した。

### 4.2 `nlinarith` で polynomial 等式を出そうとした

**状況**: `2(k+1)(6k+5)(3k+2) = 2(k+1)k(2k+1) + 2(k+1)² + 2(k+1)²(16k+9)` のような純粋な polynomial 等式 (再帰式の展開) を `nlinarith` で出そうとして空振り。

**原因**: `nlinarith` は単項式の符号付き組合せ探索なので、純粋な多項式恒等式は対象外。`ring` で書ける。

**抜け方**: `have h_poly : ... := by ring` を先に出して `linarith` に渡す形に書き換え。

**教訓**: 「`nlinarith` が落ちたとき、それが `ring` 案件 (恒等式) なのか `linarith + 補助項` 案件 (符号付き不等式) なのかを suggest してくれるツール」が欲しい。今回は 3 回 `nlinarith` を打ち変えてから判断した。

### 4.3 `rw [h6_5] at *` が hypothesis に効かなかった

**状況**: `rw [h6_5] at *` を打ったところ、ターゲットの hypothesis `h_eq` には書き換えが入らず、ゴールだけに適用された。

**原因**: 書き換えるたびに `h6_5` 自身が `6*k+5 = 6*k+5` という自明形に rewrite され、`at *` の伝播で hypothesis を回るときには既に no-op 状態だった。

**抜け方**: `at h_eq` を明示的に書いた。

**教訓**: `rw [...] at *` の dry-run で「どの hypothesis にいくつヒットしたか」を表示するツールがあれば即時判定できる。今回は 5 分浪費。

### 4.4 `Prod.mk.injEq` の `.mp` / `.mpr` 方向ミス

**状況**: `(c', y') = (c, y)` から `c = c' ∧ y = y'` を出すのに `.mp` か `.mpr` か、どちらに `Prod.mk.injEq` を当てるかで何度か左右間違えた。

**原因**: `Prod.mk.injEq : (a, b) = (c, d) ↔ a = c ∧ b = d` は左辺が原型なので、`.mp` で `=` から `∧` に変換するのが正しい。

**抜け方**: 1〜2 回試行して当てた。

**教訓**: `injEq` のような bidirectional の `.mp` / `.mpr` を hover で表示する LSP 拡張があると秒で済む。

### 4.5 `fin_cases h : a.1` の構文が効かない

**状況**: `Fin 3` の値を 3 ケースに分けたかった。`fin_cases h : a.1` を試したが、コロン構文がそのバージョンの Mathlib では受け付けられなかった。

**抜け方**: 自前で `private lemma fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by have := (by decide : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2); exact this x` を書き、`rcases fin3_cases a.1 with ha | ha | ha` で代替した。

**教訓**: `fin_cases` のシンタックスは Mathlib 側で揺れがある。`Fin n` (n 小) 用の安定した case dispatcher を skill 化したい (3.の wishlist 参照)。

### 4.6 cast まわりで `rw` 連打が鎖を作れなかった

**状況**: 最終ステップで `(triangleTriples ...).card : ℚ) / (allTriples ...).card = m * (16*m - 7) / ((6m-1)(3m-1))` を出すため、`Nat.cast_mul`, `Nat.cast_sub h_16_7`, ... を順番に `rw` で適用しようとした。中間で `↑(2*m*(6*m-1))` の中に `↑(6*m-1)` が直接現れず rewrite が止まる。

**抜け方**: `push_cast [Nat.cast_sub h_16_7, Nat.cast_sub h_6_1, Nat.cast_sub h_3_1]` で必要な non-negativity を渡しつつ一発で押し下げた。

**教訓**: **cast は手動 rw ではなく `push_cast` に賭ける**。`push_cast` の non-negativity hint をどれだけ渡せばゴールが閉じるかの dry-run があると、賭けが計算可能になる。

## 5. ボトルネックではなかったもの

- **数学のアイデア**: (2) の分割構造 (vertical + AP) は、「3 点共線 ⇔ 2 つ重複 or 1 列に 1 点ずつ + AP」という標準的な観察。気付くのに時間はかからなかった。
- **コンテキスト長**: 1M context で `T_Q2_2.lean` を 670 行まで膨らませても全く圧迫感なし。
- **型チェック・終結性**: `decide` (17 秒) と `linear_combination` で coll3 対称性が一発で出る点は嬉しい誤算。`linear_combination` を一度知ると polynomial relations が極めて簡潔になる。
- **`lake env lean` の所要時間**: warm 状態で T_Q2_2.lean 単発 5 秒、T_Q2_1.lean (decide 含む) 単発 17 秒、`lake build` 全体 50 秒。**ビルド時間自体は本体ではない**。

つまり **「アイデア生成支援ツール」は q2 では効かない**。投資すべきは Lean 構文・タクティク失敗・cast の領域。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **タクティク失敗の "なぜ" 説明** (`nlinarith` 落ちが ring 案件か linarith+補助項案件かを suggest) | 4.2 の試行 3 回ぶん、5〜10 分 |
| 高 | **`rw` / `simp` の dry-run** (`at *` でどの hypothesis にいくつヒットするかを事前表示) | 4.3 で浪費した 5 分、再発頻度高 |
| 高 | **型ベース Mathlib 検索** (`Nat.choose ?n 3 = ?` で「無い」が即時に確定) | 3 章「無い」判定で 10〜15 分 |
| 中 | **重い tactic の sandbox** (`decide` を本体投入前に別ファイルで時間測定) | 今回は手で `T_Q2_probe.lean` を切ったが、これを skill 化すると 5 分節約 |
| 中 | **cast 自動補完** (`push_cast` 用の non-negativity hint suggest) | 4.6 で 5〜10 分 |
| 中 | **補題シグネチャ設計チェックリスト** (skeleton 段階で「返り値に変換関数を埋め込むべきか」を問う) | 4.1 の手戻り 100 行ぶん、20〜30 分 |
| 低 | **`Fin n` (n 小) の安定 case dispatcher** | 4.5 で 5 分 |
| 低 | **`field_simp` の close 検出** (単独で goal が閉じるか dry-run) | 1〜2 分 |

## 7. 補足

### 「無い」判定で打った grep の全リスト (再現性のため)

```
grep -rE "choose.*succ_eq|Nat.choose_three\b|choose_eq_descFact" .lake/packages/mathlib/Mathlib/Combinatorics/ .lake/packages/mathlib/Mathlib/Data/Nat/Choose/
grep -rE "descFactorial\b|Nat\.descFactorial" .lake/packages/mathlib/Mathlib/Data/Nat/Factorial/
grep -rE "choose_mul_factorial|choose.*descFactorial|six.*choose_three" .lake/packages/mathlib/Mathlib/Data/Nat/
grep -rE "descFactorial_eq_div|descFactorial_succ\b" .lake/packages/mathlib/Mathlib/Data/Nat/Factorial/
grep -rE "choose 3 = | three.*factorial|6 \* .*choose" .lake/packages/mathlib/Mathlib/Data/Nat/
```

5 種試して `Nat.choose_three_eq` 形式は無し、`descFactorial` 経由で自前導出。

### probe 戦略

`Common2026/T_Q2_probe.lean` を別途作って `decide` の所要時間を 17 秒と確認してから本体で採用。これは**重い tactic を本体に投入する前の sandbox 戦略**として再利用価値が高い。今回は手作業だが、`decide` / `decide!` / `native_decide` の選択肢を自動でベンチして best を返す skill にすると効く。

### 採らなかった代替案

- **(2) を `decide` で押し切る**: 一般 m を `decide` できないので不採用 (m が変数のため)。仮に有限ケース (m = 2..k) だけ `decide` で押すこともできるが、問題文が「m ≥ 2 で証明せよ」なので普遍式で書く必要があり、却下。
- **`coll3` の置換不変性を全 6 順列ぶん書く**: 4.1 の補題設計で「変換関数を返り値に埋める」方針に切り替えた結果、必要な置換補題は 5 つで済んだ。

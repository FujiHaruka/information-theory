# 東大 2026 第2問 Lean 形式化 — ボトルネック分析

2026-05-06、Claude Opus 4.7 (1M context) による単発セッション。

## 0. 対象問題と成果物

東大 2026 数学 第2問:

3n 個の格子点 {(x, y) ∈ ℤ² | 1 ≤ x ≤ 3, 1 ≤ y ≤ n} から相異なる 3 点を等確率で選び、三角形をなす確率を p_n とする。

- **(1)** p_5 を求めよ → 412 / 455
- **(2)** m ≥ 2 で p_{2m} を求めよ → m(16m − 7) / ((6m − 1)(3m − 1))

成果物:

- `Common2026/T_Q2_1.lean` — 104 行 (共通定義 + (1) は `decide` で済ませた)
- `Common2026/T_Q2_2.lean` — 678 行 (一般 m での分割数え上げ)
- `lake build` 通過 (2686 jobs)

## 1. q1 とのキャラの違い

q1 が「Mathlib に揃った微分・積分の部品を呼び出す」仕事だったのに対し、q2 は **「Finset 上の数え上げを場合分けで愚直に書き下す」仕事**。

体感の支配項が変わった:

| 工程 | q1 | q2 |
|---|---|---|
| Mathlib lemma 探索 | 50% | 15% |
| 証明設計 (分解の仕方) | 10% | 30% |
| Lean 4 の細部 (cast / Prod.ext / Fin n / 構文) | 5% | 25% |
| タクティク選択 (linarith vs nlinarith vs ring) | 5% | 15% |
| エラー対応 / 設計手戻り | 15% | 15% |
| 主結果まで畳む | 15% | — |

つまり q2 では **証明設計 + Lean 構文の細部** が二大ボトルネック。

## 2. 設計上の判断と、それで失った時間

### 2.1 (1) は `decide` 一発で良いと判断 → 正解

15 点 = 455 通りの全 3 元組合せに対し、collinearity の existential を decidable にしておけば `decide` で 17 秒程度で終わる。q1 と同様に rigor を維持しつつ、(1) のためだけの場合分けを書かずに済んだ。

ここで投資したのは:
- `coll3` を `((b.1.val : ℤ) - a.1.val) * ... = ...` で定義し `Decidable` 派生
- `IsCollinear s := ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ...` 形の existential
- Finset 上で `Classical` を使わず `Decidable (∃ a ∈ s, P a)` で押し切れる

`decide` を使う前は別ファイル (`T_Q2_probe.lean`) で reachability を確認した。**この probe が時間節約に効いた** — 17 秒で動くか分からないまま skeleton を組むのは怖かったため。

### 2.2 (2) の分割証明が 500 行食った

`collTriples = vertTriples ∪ lineTriples` を厳密に出すために、 `IsCollinear s ⇒ (s ∈ vertTriples ∨ s ∈ lineTriples)` の forward direction を場合分けで処理した。

主要な内訳:

- `coll3` の置換不変性 4 補題 (swap × 3 + rot × 2)
- `triple_set_perm_*` 5 補題 (`{a, b, c} = {p₀, p₁, p₂}` の 5 順列パターン)
- `exists_col_match` (3 点の x 座標が全て異なるとき正規順列を返す。**27 ケース dispatch**)
- `mem_vertTriples_of_same_col` (全 x 一致から vertTriples メンバシップへ)
- `coll_eq_vert_union_line` 本体 (4 つのサブ場合分け)

ここで設計上の鍵が一つ: `exists_col_match` に **「coll3 a b c から coll3 p₀ p₁ p₂ への変換関数」を返り値に含めた**こと。これが無いと、6 順列のどれを当てるかを呼び出し側で再場合分けする羽目になり、行数倍増。

設計を最初から決めずに skeleton から書き始めたので、ここに来てから書き直したのに 30 分くらい持って行かれた。

### 2.3 lineMap の midY: ℕ の整数除算で罠

`midY (y₀, y₂) := ⟨(y₀.val + y₂.val) / 2, _⟩ : Fin n`

「y₀ + y₂ が偶数なら midY は AP の中項」を示すには、`2 * (midY p).val = p.1.val + p.2.val` を omega で出してから ℤ にキャスト。

`exact_mod_cast hmid` でいけるところを最初 `push_cast; omega` でゴチャゴチャやった。`exact_mod_cast` の方が一行で済む。

## 3. 失敗ログ (具体的にトークン/時間を吸った)

### 3.1 import / 名前 の細かい外し

- **`instFintypeProd _ _` を手動で書く**: `Mathlib.Data.Fintype.Prod` を import すれば `abbrev Pt := Fin 3 × Fin n` から自動派生される。手動 instance 宣言を書こうとして 1 ターン無駄。
- **`Finset.card_univ` が見つからない**: `Mathlib.Data.Fintype.Card` 配下。デフォルトでは入っていない。
- **`linear_combination` 未 import**: `Mathlib.Tactic.LinearCombination` の追加で解決。最初「unknown tactic」エラーで一瞬戸惑った。
- **`card_insert_of_not_mem` vs `card_insert_of_notMem`**: 後者が現役。型クラス命名規則の camelCase に統一されている。

### 3.2 Lean 4 構文の罠

- **`fun k : Fin m => ⟨...⟩ : Fin (2 * m)`**: 型注釈が ⟨⟩ の中身ではなく lambda 全体に係って型ミス。`fun k : Fin m => (⟨...⟩ : Fin (2 * m))` と内側に書く必要。
- **`refine ⟨...⟩` の Quot.lift エラー**: `unfold vertTriples; rw [Finset.mem_image]; refine ⟨...⟩` で、ゴールが `Quot.lift (fun l => p ∈ l) ⋯ s.val` という形に変質して anonymous constructor が効かない。`refine Finset.mem_image.mpr ⟨...⟩` と書き直して解決。
- **`Prod.mk.injEq` の方向**: `(c', y') = (c, y)` から `c = c'` か `c' = c` か、`.mp` か `.mpr` か。何度か左右間違えた。
- **`fin_cases h : a.1`**: 期待した構文が効かず、自前で `private lemma fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by have := (by decide : ∀ y : Fin 3, ...); exact this x` を書いて `rcases fin3_cases a.1 with ha | ha | ha` で代替。

### 3.3 タクティク選択ミス

- **`nlinarith` への過信**: polynomial identity (例: `2(k+1)(6k+5)(3k+2) = 2(k+1)k(2k+1) + 2(k+1)² + 2(k+1)²(16k+9)`) を nlinarith で出そうとして失敗。
   - 正解: **`have h_poly : ... := by ring` を先に出して `linarith` に渡す**。 `nlinarith` は単項式の符号付き組合せ探索で、こういう純粋な polynomial 等式は専門外。
- **`field_simp; ring` のオーバーシュート**: `p_2m` 最後で `field_simp` だけで既にゴールが閉じていたのに `ring` を続けて「no goals to be solved」エラー。defensive に `; try ring` を書くか、最初から `field_simp` で止めるか。
- **`rw [...] at *` の挙動**: `rw [h6_5] at *` を打ったら h_eq には適用されず goal だけに適用された (h6_5 自身が rewrite 後に `6*k+5 = 6*k+5` という自明形になっていた)。`at h_eq` を明示すべきだった。

### 3.4 「無い」判定で詰まったもの

| 探したもの | Mathlib にあるか | 代替 |
|---|---|---|
| `n.choose 3 = n*(n-1)*(n-2)/6` の閉形式補題 | **無い** | `Nat.choose_eq_descFactorial_div_factorial` + `Nat.factorial_dvd_descFactorial` で自前導出 (8 行) |
| `Nat.choose 3 * 6 = ...` の系 | **無い** | 同上 |
| 「Fin n の偶数値の個数 = ⌈n/2⌉」 | 直接は **無い** | bijection `Fin m → Fin (2m), k ↦ 2k` で自前 |

`Nat.choose 3` 閉形式の探索で 5-10 分浪費。q1 のログでも同種の「無い判定コスト」が指摘されていたので、これは普遍的なボトルネックっぽい。

### 3.5 cast 周りの怪談

`(triangleTriples ...).card : ℚ) / (allTriples ...).card = m * (16*m - 7) / ((6m-1)(3m-1))` の最終ステップで:

- 最初 `rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h_16_7, ...]` を順番に重ねて `↑(2*m*(6*m-1))` の中に `↑(6*m-1)` が直接現れず rewrite 失敗。
- 解決: `push_cast [Nat.cast_sub h_16_7, Nat.cast_sub h_6_1, Nat.cast_sub h_3_1]` で必要な non-negativity 補題を渡しつつ一発で押し下げる。
- 教訓: **cast は手動 rw より push_cast に賭ける**。

## 4. ツール呼び出し統計 (概算)

| ツール | 回数 |
|---|---|
| Edit | 約 30 |
| Bash (lake env lean) | 約 15 |
| Bash (grep mathlib) | 約 10 |
| Read | 約 10 |
| Write | 3 (probe + 本体 2 ファイル) |
| TaskCreate/Update | 約 16 |
| ToolSearch | 1 |
| **合計** | **約 85** |

タイミング:

- 単発 `lake env lean Common2026/T_Q2_2.lean`: 約 5 秒 (Mathlib olean warm 後)
- `T_Q2_1.lean` 単発 (decide 含む): 約 17 秒
- `lake build` (全プロジェクト, 最終): 約 50 秒
- `lake build Common2026.T_Q2_1` (downstream 用 olean 更新): 約 20 秒

ビルド時間自体は全体で 5 分にも満たない。**思考時間と Edit-error の往復が時間の本体**。

## 5. ツール wishlist

q1 のログでは「Mathlib loogle 風型ベース検索」「無いの素早い判定」が筆頭だった。q2 を経て、別ベクトルの欲求が増えた:

### 高 ROI

1. **タクティク失敗の "なぜ" 説明**:
   `nlinarith failed to find a contradiction` が出たとき、**どの単項式の係数が合わないか** / **何が線形に乗らないか** を出してほしい。今は手で polynomial 整形して `have ... := by ring; linarith` のテンプレに落とすしかなく、「これは ring 案件」と気付くまでが遅い。

2. **rewrite 適用範囲の dry-run**:
   `rw [h] at *` がどの仮説/ゴールに何回マッチするか事前に見せてほしい。`at h_eq` を明示するか、`at *` で十分か、その判断が経験頼り。

3. **「これは Mathlib に無い」確信**:
   q1 でも挙げられたが q2 でも繰り返し効いた。`leansearch` / `loogle` を統合した CLI が一発で「該当なし、自前で書け」と返してくれると 5 分は救える。

### 中 ROI

4. **cast 自動補完**:
   「ℕ→ℚ で subtraction が絡む」と検出した瞬間、必要な `Nat.cast_sub` の non-negativity 補題候補を suggest してほしい。今は手で `7 ≤ 16 * m` 等を omega に投げる手作業。

5. **`field_simp` の close 検出**:
   `field_simp` が単独でゴールを閉じる場合と閉じない場合があり、`; ring` を付けるか毎回賭けになる。dry-run で結果を見せてくれれば良い。

6. **Fin n の安定 case dispatcher**:
   `fin_cases` の挙動が変数のバインド形によってブレる。`Fin 3` に対する確定的な `rcases ... with rfl | rfl | rfl` の砂糖が欲しい。

### 低 ROI

7. **decide の事前タイムアウト見積**:
   `decide` を投入する前に「どれくらいかかりそうか」をヒューリスティックに見せてほしい。今回 n=5 で 17 秒だったが、これが 5 分なら撤退して別戦略に切り替えたい。

## 6. q1 / q2 比較で見える教訓

- **q1**: 数学のゴールに対して Mathlib の補題が直接対応していた → 「探す」が中心。
- **q2**: 数学のゴールが Finset カードという「構造」を経由する必要があった → 「組み立てる」が中心。

ツール ROI も二極化していて、

- q1 系の問題には **Loogle** が最大インパクト。
- q2 系の問題には **タクティク失敗の説明可能性 + rewrite 透明化** が効く。

両者は実装パスが違うので、「どちらの問題か」を session 開始時に見立てて投資配分を決められると効率が上がる。

## 7. 一行サマリー

q2 は **「分割を設計し直すと行数が半分になる」局面が随所にあった**。設計→ skeleton →穴埋めの素朴サイクルだと、分割を後付けで再考する手戻りが効く。今回もそれで 100 行ぶん書き直しが発生した。次回は skeleton 前に **データフロー (どの補題から何を返してもらうか)** を紙に書いておく方が良い。

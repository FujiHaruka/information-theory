# Fano 不等式 Phase 1 (Markov 形 + DPI) Lean 形式化 — ボトルネック分析

将来「Mathlib 補題探索を楽にするツール」「`.olean` の依存解決と LSP 同期を診断するツール」を作るためのベースライン記録。Fano ムーンショット計画 (`docs/fano/fano-moonshot-plan.md`) の Phase 1 を、計画 (`docs/fano/fano-phase1-plan.md`) に沿って 1 ターンで完走した記録。

**定量データ**: [docs/metrics/fano-phase1.metrics.md](../metrics/fano-phase1.metrics.md)

## 0. 対象問題と成果物

Cover & Thomas Theorem 2.10.1（教科書形 Fano）：

```
H(X | X̂) ≤ binEntropy(Pe) + Pe · log(|X| − 1)
  where  X, X̂ : Fintype（離散・有限）
         joint PMF P on (X, X̂) は任意（X̂ は決定論的関数とは限らない）
         Pe = ∑ {(x, x̂) : x ≠ x̂}, P(x, x̂)
```

Phase 0（決定論的 decoder `decode : Y → X` 形）からの拡張で、Phase 0 形は data processing inequality（DPI）経由で系として復元する。

成果物:

- `Common2026/Fano.lean` — `errorProb` / `fano_inequality_of_core` / `error_lower_bound_of_core` を Markov 形に書き換え（既存ファイルへの差分編集）
- `Common2026/Fano/Core.lean` — 446 行、`(P : FiniteJointPMF X Y)` + `decode : Y → X` 引数を `(P : FiniteJointPMF X X)` に統一する全面書き直し
- `Common2026/Fano/DPI.lean` — 新規 350 行、`log_sum_inequality_negMulLog` / `pushforward` / `pushforward_marginalY` / `condEntropy_le_pushforward_condEntropy` / `pushforward_errorProb` / Phase 0 wrapper 3 種
- `Common2026.lean` — `import Common2026.Fano.DPI` を追記

`lake env lean` 全ファイル silent、`lake build Common2026.Fano.DPI` 通過。0 errors / 0 sorry / 0 警告（`push_neg` deprecated は最終的に `by_contra` に置換）。

## 1. 問題のキャラクター

「**機械的リファクタ + 1 つの非自明な数学**」が並列に走る形。

- 機械的部分（M1+M2、Core.lean 書き直し）は計画が `Y → X̂` の置換 4 種を事前に列挙しており、Write 1 回 + 識別子問題の修正 1 回でほぼ片付いた
- 非自明部分（M3、DPI）は **log-sum 不等式を Jensen + `mul_negMulLog_div` 経由で組み立てる**新規証明。Phase 0 にあった補題群と同じ Jensen 系の道具で書けるが、Mathlib に名前付きで存在しないので自前で書き下す必要がある

過去の Fano 関連作業（Phase 0）との関係:

| 項目 | Phase 0 (前回) | Phase 1 (本回) |
|---|---|---|
| 主軸 | Jensen + chain rule + `condE_XY_zero_of_deterministic` | log-sum 不等式 + `Finset.sum_fiberwise` |
| 既存補題のリネーム | — | 4 種の置換で 446 行を一気に書き換え |
| 新規補題 | 多数（`entropyOfFn_le_log_supportCard`, `binEntropy_jensen_finset`, ...） | 1 つ（`log_sum_inequality_negMulLog`） |

## 2. 数学的方針

### Markov 形 (M1+M2)

Phase 0 の `Fano/Core.lean` は `errIndicator decode x y := decide (x ≠ decode y)` で `decode y` を介して `x = ?` を判定していた。Phase 1 では `decode` を消し、`errIndicator x x̂ := decide (x ≠ x̂)` に置き換える。

`errIndicator` の比較が `x ∈ X` と `x̂ ∈ X̂` の間で起きるので両者を同じ型にする必要がある。計画通り `FiniteJointPMF X X` で固定し、`X̂` は変数名 `xh` と docstring 上の概念だけ残した。

`withErr` / `Joint3` / per-term bound の構造はすべて「`y` を `x̂` と読み替える」だけで通った。

### DPI (M3)

`H(X|Y) ≤ H(X|f(Y))` を `negMulLog` の凹性 + Jensen で示す。具体的には**ログサム不等式の `negMulLog` 形**：

```
∀ s, a, b ≥ 0 with (b_i = 0 → a_i = 0):
  ∑ i, [negMulLog(a_i) + a_i log(b_i)]
    ≤ negMulLog(∑ a_i) + (∑ a_i) log(∑ b_i)
```

これは `b_i = 0` の項を除外した上で重み `b_i / B` での Jensen に帰着し、`mul_negMulLog_div` で per-term を翻訳して両辺に揃えるという流れ。

DPI 本体はファイバー `F = univ.filter (f y = x̂)` ごとに上の不等式を `(a, b) = (P.mass x ·, P.marginalY ·)` で適用し、`x` で和、`x̂` で和、`Finset.sum_fiberwise` で `∑ x̂ ∑ y∈F = ∑ y` に畳む。

### Phase 0 復元 (M4)

Markov 形の `fano_inequality` を `P.pushforward decode` に適用し、DPI で `P.condEntropy ≤ (pushforward).condEntropy` を挟むだけ。各 wrapper は計画通り 5 行以内で書けた。

## 3. Mathlib 補題探索の実録

| 必要だったもの | 最終的な grep クエリ | 所要試行 | 見つかった場所 / 結果 |
|---|---|---|---|
| `Finset.sum_fiberwise` (additive 形) | `(theorem|lemma) (Finset\.)?sum_fiberwise` 等 5 通り | **5 回**、最終的に `to_additive sum_fiberwise` で hit | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:prod_fiberwise_of_maps_to` の `to_additive` で生成される。ソースコードに直接 `theorem sum_fiberwise` という記述は無い |
| `Real.concaveOn_negMulLog` | （Phase 0 で利用済み、再検索なし） | 0 回 | `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` |
| `mul_negMulLog_div` | （自前、`Common2026/Fano/BinaryJensen.lean`） | 0 回 | local |

### 「Mathlib に存在しなかった」もの

- **`log_sum_inequality_negMulLog`** — log-sum 不等式の `negMulLog` 形。`grep -rE "log_sum"`, `grep "logSum"` を試したがそれらしい命題は無い。`Mathlib.MeasureTheory.kullbackLeibler` 系を眺めたが、測度論的すぎて有限和に直接使えない。**結局自前で 70 行ほど書いた**（Jensen + `mul_negMulLog_div` + s' フィルタ + AC 条件処理）。Phase 1 の中核補題。

- **`mul_le_mul_left.mp`** — `0 < c → (c * a ≤ c * b ↔ a ≤ b)` の iff 形が手元にあるかと期待したが、`mul_le_mul_left` は単方向の `theorem` で `.mp` を持たなかった。`mul_le_mul_of_nonneg_left` で順方向に書き直した。

- **`Real.negMulLog ↔ -t log t` の自動正規化** — `Real.negMulLog t = -t * log t` を簡約する `simp` lemma があるかと期待したが、`unfold Real.negMulLog; ring` で十分だった。

## 4. 試行錯誤と後戻り

### 4.1 識別子に結合発音記号 `x̂` が使えない

**状況**: 計画の例示コードに沿って `def errIndicator : X → X → Bool := fun x x̂ => decide (x ≠ x̂)` と書き、Core.lean / Fano.lean / DPI.lean に合計 100 箇所以上 `x̂` / `X̂` を散布した。

**原因**: `x̂` は `x` + U+0302（COMBINING CIRCUMFLEX ACCENT）。Lean 4 の lexer は識別子に結合 diacritic を許可しない。docstring 内（`/-- -/`）は OK だが識別子はダメ。LSP 反応は即時で `expected token` を line 137:10 等で 10 件以上検出。

**抜け方**: `sed -i '' 's/x̂/xh/g; s/X̂/Xh/g'` で 3 ファイル一括置換。docstring も含めて `xh` / `Xh` に統一。

**教訓**: 
- 「Unicode 識別子サポート」は precomposed か combining かで挙動が違う。`α β γ ε` は OK だが `x̂` は NG
- 計画段階で疑似コードに変な記号を含めるなら、**Write 前に最小例で識別子可能性を確かめる**チェックがあると効率的
- ツール仕様への示唆: 「Lean 識別子 lint」ツールがあれば即時警告できる

### 4.2 `lake env lean` がアップストリームの編集を反映しない

**状況**: M1+M2 で `Common2026/Fano.lean` の `errorProb` の signature を `(P : FiniteJointPMF X Y) (decode : Y → X)` から `(P : FiniteJointPMF X X)` に変更した直後、`lake env lean Common2026/Fano/Core.lean` が `P.errorProb has type (X → X) → ℝ` という古いエラーを大量に吐いた。

**原因**: `lake env lean` は依存モジュールの `.olean` を**再ビルドしない**。`Fano.lean` の `.olean` は古い `errorProb` の signature を持ったままで、`Core.lean` がそれを参照していた。

**抜け方**: CLAUDE.md の「LSP shows stale errors after upstream edits」節を参照して `lake build Common2026.Fano` を実行。`.olean` が更新され、次の `lake env lean Common2026/Fano/Core.lean` は silent に通った。

**教訓**: 
- アップストリームを変更した後は `lake build <upstream>` を 1 回挟む癖が必要
- ツール仕様への示唆: `.olean` の mtime と `.lean` の mtime を比較して「アップストリームが古い」ことを警告するヘルパがあれば事故が減る

### 4.3 `Finset.sum_fiberwise` の出処が見つからない

**状況**: DPI 証明の plumbing で `∑ x̂, ∑ y ∈ univ.filter (f y = x̂), g y = ∑ y, g y` を使いたく、その正確な定理名を探した。

**原因**: 直接 `theorem sum_fiberwise` という記述が Mathlib に無い。`to_additive` macro が `prod_fiberwise_of_maps_to` から自動生成しているため。

**抜け方**: 試したクエリの順序：
1. `grep -r "theorem (Finset\.)?sum_fiberwise|sum_partition" .../Algebra/BigOperators` → 0 件
2. `find ... | xargs grep -l "sum_fiberwise"` → 利用箇所の 5 ファイルが出るが定義が無い
3. `grep -r "theorem sum_fiberwise" .../Mathlib` → 1 件だが BoxIntegral 専用の別物
4. `grep -B2 -A6 "sum_fiberwise_of_maps_to" .../Algebra/BigOperators/Group/Finset/Basic.lean` → 0 件 **（誤報。空マッチ）**
5. `grep -B2 -A6 "prod_fiberwise_of_maps_to\b" .../Algebra/BigOperators/Group/Finset/Basic.lean` → ヒット、`@[to_additive]` で sum 形が生成されると分かった

**教訓**: 
- Mathlib では `to_additive` で multiplicative → additive を一括生成しているため、`grep "theorem foo"` で additive 形だけを探すと空振りする
- ツール仕様への示唆: 
  - **「multiplicative ↔ additive aware grep」**があれば「`sum_fiberwise`」と聞いて `prod_fiberwise` の `to_additive` 生成を答えられる
  - もしくは Mathlib の declaration index（`loogle` 風）を使うべきだったかもしれない

### 4.4 ログサム不等式の `s'` フィルタ周りの細かいバグ

**状況**: `log_sum_inequality_negMulLog` の B > 0 ケースで、support の filter `s' = s.filter (b · ≠ 0)` を導入した。`hbi_zero_outside : ∀ i ∈ s, i ∉ s' → b i = 0` を経由して `Finset.sum_subset` で `∑ s = ∑ s'` を示そうとした。

**原因**: 連発した小バグ：
- `hni hi : b i = 0` だが context は `b i = 0` を期待していた（ところが `push_neg` の deprecation 警告で代わりに別のロジックに切替）
- `Finset.sum_subset hs'_subset` は `∑ s' = ∑ s` を返す（s' ⊆ s 方向の延長）。`∑ s = ∑ s'` を欲していたので `.symm` 必要
- `(mul_le_mul_left hBinv_pos).mp` を書いたが `mul_le_mul_left` は単方向 `theorem`、`.mp` 不存在
- `▸` を使った rewrite 連鎖を `linarith` の引数で渡そうとして metavariable が残った

**抜け方**: 全部 `calc` チェーンに置換。中間の have で各等式を独立に証明し、最後に `calc` で繋ぐ。

**教訓**: 
- `Finset.sum_subset` の方向を毎回確認する。引数の `s' ⊆ s` から「`∑ s' = ∑ s`」と覚える（subset は「小から大への延長」を返す）
- 複雑な代数操作は `linarith [a, b, c]` よりも `calc` のほうが堅牢
- `mul_le_mul_left` 系の iff vs 単方向は混乱しやすい — `mul_le_mul_of_nonneg_left` を使うのが安全

### 4.5 `pushforward_errorProb` の `if x = x` 簡約

**状況**: Markov 形 errorProb と Phase 0 形 errorProb の同値を示す `pushforward_errorProb` で、`if x = x̂ then 0 else (∑ y in fiber, P.mass x y)` を `∑ y in fiber, if x = f y then 0 else P.mass x y` に書き換えたい。`x = x̂` のケースで `subst hx` 後、`if x = x then 0 else ∑ ... = ∑ y in fiber, if x = f y then 0 else P.mass x y` を示す必要があった。

**原因**: `apply Eq.symm` で flip した後、LHS が `∑ y in fiber, if x = f y then 0 else P.mass x y` となるが RHS は `if x = x then 0 else _` のまま。`apply Finset.sum_eq_zero` は RHS が `0` であることを期待するが、`if x = x then 0` は **構文的には 0 ではない**（reducible には 0 だが）。

**抜け方**: 先に `rw [if_pos rfl]` で `if x = x then 0` を `0` に簡約し、その後 `symm` + `Finset.sum_eq_zero` でファイバー内の各項を `if hy' : f y = x` で潰す。

**教訓**: 
- `if cond then a else b` で `cond` が syntactic に `True` でないが decidable に `True` の場合、`if_pos rfl` で明示的に書き換える必要がある
- ツール仕様への示唆: 「if 条件の自動簡約」を `simp` 標準で含めるかは tradeoff

## 5. ボトルネックではなかったもの

- **計画書の精度**: `docs/fano/fano-phase1-plan.md` が「機械的置換 4 種」「DPI に必要な API」「per-x̂ 不等式の構造」を事前に書き下していたので、M0 監査は「計画通りか追認するだけ」で済んだ。Plan to code が**ほぼ 1:1 対応**だった。
- **Markov 形リファクタの数学的正しさ**: `withErr` / `Joint3` / chain rule の構造は `Y → X̂` の rename に対して**完全に invariant**。証明本体に手を入れる必要は皆無で、計画の予想通り。
- **Phase 0 wrapper の証明長**: 計画では「各 wrapper 5 行以内」と予想されていたが実際にも 5 行以内（`linarith`、`exact ... le_trans ...`）で十分だった。
- **`negMulLog` の凹性 / `Real.binEntropy`**: Mathlib に揃っており Phase 0 で動作確認済み。
- **lake build の所要時間**: Mathlib oleans が warm なので `lake build Common2026.Fano` 系は毎回 5 秒前後。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **Mathlib の multiplicative ↔ additive 認識付き grep / loogle** | §4.3 の `sum_fiberwise` 探索で 5 回の grep を 1 回に減らせる。再発頻度が高い（Mathlib では多くの大運営者が `to_additive` で対称生成している） |
| 高 | **アップストリーム `.olean` の更新時刻を見て LSP / `lake env lean` で警告** | §4.2 の混乱を未然に防ぐ。CLAUDE.md に「`lake build <upstream>` を挟む」と明記したが、ツール側で検知できれば人間 / Claude のメモリに頼らずに済む |
| 中 | **Lean 4 識別子 linter（結合 diacritic 等の lexer 非対応 Unicode を Write 前に警告）** | §4.1 で Write 後にエラー診断と sed 一括置換のラウンドトリップ 1 回（実時間 1〜2 分）を節約 |
| 中 | **`Finset.sum_subset` 等の方向性メモを diagnostics に組み込む** | §4.4 の `.symm` 必要性を毎回確認しなくて済む |
| 低 | **`if_pos rfl` 系の自動 unfold（オプトイン）** | §4.5 の `rw [if_pos rfl]` の手作業を減らせる。tradeoff あり（暗黙の簡約は副作用が大きい） |

## 7. 補足

### 実際に打った grep の主要なもの

```
grep -rE "(theorem|lemma) (Finset\.)?sum_fiberwise|sum_partition" .../Mathlib/Algebra/BigOperators
grep -rl "sum_fiberwise" .../Mathlib
grep -rE "^theorem.*sum_fiberwise|^lemma.*sum_fiberwise" .../Mathlib
grep -B2 -A6 "prod_fiberwise_of_maps_to\b" .../Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean
```

### 自前で書いた中核補題のシグネチャ

```lean
lemma log_sum_inequality_negMulLog {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (h_ac : ∀ i ∈ s, b i = 0 → a i = 0) :
    ∑ i ∈ s, (Real.negMulLog (a i) + a i * Real.log (b i))
      ≤ Real.negMulLog (∑ i ∈ s, a i)
          + (∑ i ∈ s, a i) * Real.log (∑ i ∈ s, b i)

theorem condEntropy_le_pushforward_condEntropy
    (P : FiniteJointPMF X Y) (f : Y → X) :
    P.condEntropy ≤ (P.pushforward f).condEntropy
```

### 採らなかった代替案

- **Joint3 を使った DPI 証明**: 3-変数 mass `μ x y x̂ = if x̂ = f y then P.mass x y else 0` を作って `condX_EY μ ≤ condX_Y μ` に帰着する経路を一度検討。しかしこれは結局「conditioning reduces entropy（H(X|A) ≥ H(X|A,B)）」を要請し、その証明は同じ log-sum 不等式に帰着するので**回り道**になる。直接 log-sum 経由のほうが約 30 行短い。
- **Mathlib の `MeasureTheory.kl`**: KL ダイバージェンスから DPI を導く経路もあり得るが、有限離散 PMF の世界に閉じる目的では plumbing が増えるだけ。Phase 3 で測度論版に行ったときに再検討の余地あり。

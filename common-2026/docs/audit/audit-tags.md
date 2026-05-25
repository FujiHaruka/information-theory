# Audit tags — code-as-source-of-truth 規約

honesty audit の状態 (genuine 完成 / 残課題 / 移行履歴) を **コード内に構造化マーカーで埋め込む** ことで、`rg` が単一の source of truth になる。snapshot 文書ではなく、コード自身が「現状どうなっているか」を答える。

## SoT 階層

1. **`sorry`** — primary residual marker。compiler-visible。「ここはまだ証明していない」を一語で表現する正直な道具。
2. **`@residual(<class>:<slug>)`** — 当該 `sorry` の分類補助。docstring または近接コメント。
3. **`@audit:*`** — bookkeeping (audit pass 済 / 別 plan に移管 / 後続版に置換済) 専用。残課題マーカーではない。

実装中に詰まったら **`sorry` + `@residual` で抜ける**。仮説束 (`*Hypothesis` predicate で結論型と同等の核を抱えさせる) や `:True` slot で `sorry` を回避するのは禁止 → CLAUDE.md「検証の誠実性」。

## Honesty 階層 (high → low)

honesty audit が評価する「正直さ」の階層。auditor の verdict 序列 + 実装側の選好順位はこの順で決まる。**一番 honest なのは `sorry`** — コンパイラ可視 + 「ごめんね」と明示している、隠蔽しようがない正直な未完成マーカー。

| Tier | 形態 | 含意 |
|---|---|---|
| **1** | `@audit:ok` (0 sorry / 0 @residual、auditor pass) | proof done、最高 honest |
| **2** | `sorry` + `@residual(<class>:<slug>)` | type-check done、新規実装の唯一の honest 撤退口 |
| **3** | bookkeeping (`@audit:defer(plan)` / `@audit:closed-by-successor(slug)` / `@audit:superseded-by(slug)` / `@audit:retract-candidate(reason)`) | honest だが当該 file の外に処理が逃げている。tier 2 の sorry を別 file に持っている場合 + 削除候補等 |
| **4** ⚠ | **legacy** `@audit:suspect(plan)` / `@audit:staged(wall)` / 散文 `🟢ʰ` | 旧方針で「honest 残課題」として許容されていた load-bearing hypothesis / predicate bundling 形態。**新方針では defect 寄り** — tier 2 に書換待ち ([[sorry-based-migration]])。auditor は発見しても即時 alert せず、incidental migration を推奨する程度の severity |
| **5** | `@audit:defect(*)` / 仮説型 ≡ 結論 (`:= h` 循環) / `:True` slot / 退化定義悪用 / name laundering / mathlib wall misuse | 真の honesty defect、即修正必要 |

**重要な含意**:

- **tier 2 (sorry + @residual) は tier 4 (suspect/staged) より strictly honest**。旧方針で「honest 名前付き仮説で抜く」と書かれていた撤退口は tier 4 で、新方針ではより上位の tier 2 に置き換える。
- **tier 4 (legacy) は無期限放置を意味しない**。新規実装で tier 4 declarations を touch するときに incidental に tier 2 へ migrate する (移行レシピ → 本ファイル下部 + [[sorry-based-migration]])。
- **auditor の verdict**: tier 5 を見つけたら即 rewrite recommend (commit revert)。tier 4 を見つけたら incidental migration recommend (緊急性低)。tier 2 の `@residual` 分類検証が主たる仕事。
- **実装側の選好**: 詰まったら必ず tier 2 を選ぶ。tier 4 を新規作成するのは禁止 (CLAUDE.md「検証の誠実性」)。

## 動機

- snapshot 文書 (defect-101 report 等) は **書いた瞬間から陳腐化** する。defect 数が変わっても文書は更新されない。
- 散文表現 (`🟢ʰ`, `(未着手)`, "NOT a discharge", "load-bearing hypothesis") が併存していると **集計不能** + 表現ゆれで grep 信頼度が落ちる。
- 監査で発見した新規 issue を「次セッションのタスク」に保管するのではなく、**発見した場所 (= 当該 docstring)** に埋め込めば、タスクリストが肥大化しない。

## 語彙

### `@residual(<class>:<slug>)` — 残課題分類 (sorry に併走)

各 `sorry` には対応する `@residual(...)` タグを 1 つ持たせる。

| Class | 意味 | Slug 規約 | 例 |
|---|---|---|---|
| `plan` | 別 plan で closure 予定 | plan filename stem (no `.md`) | `@residual(plan:epi-stam-closure)` |
| `wall` | Mathlib に未整備の壁。長期残課題 | wall name (kebab-case, extensible) | `@residual(wall:stam)`、`@residual(wall:n-dim-gaussian-aep)` |
| `defect` | 旧 defect の fix 待ち残置 (signature は honest 化済、body だけ `sorry`) | defect kind | `@residual(defect:circular)` |

**配置**: 1 sorry / 1 theorem の場合は docstring 末尾、複数 sorry の場合は各 sorry の直前行コメント。

```lean
-- パターン A: 単一 sorry → docstring に
/-- Stam の不等式の本体。
@residual(plan:epi-stam-closure) -/
theorem stamInequality_body : ... := by
  sorry

-- パターン B: 複数 sorry → 各 sorry 直前
theorem foo : ... := by
  have h1 : ... := by
    -- @residual(wall:stam)
    sorry
  have h2 : ... := by
    -- @residual(plan:foo-step-2)
    sorry
  ...
```

### `@audit:*` — bookkeeping (sorry を伴わない)

| Tag | 意味 | Slug の中身 | 例 |
|---|---|---|---|
| `@audit:ok` | 独立 auditor が honesty pass 判定。genuine 完成 (0 sorry / 0 residual) | (なし) | `@audit:ok` |
| `@audit:defer(PLAN)` | 当該 def/theorem の discharge を別 plan に切り出した。本 file 内の `sorry` ではなく、別 plan 側で対応 | PLAN filename stem | `@audit:defer(awgn-achievability-typicality)` |
| `@audit:closed-by-successor(SLUG)` | 当該 plan は完成、ただし残存 `@residual` の closure を後続 plan に明示的に委譲。**後続 plan が closure する前提**で残っている wrapper | 後続 plan filename stem | `@audit:closed-by-successor(chernoff-converse-sanov-discharge)` |
| `@audit:superseded-by(SLUG)` | 当該 declaration は後続版に置き換え済 (`_unconditional` 版が併存している `_of_condEntDiff` conditional 版等)。history record / API 後方互換のため削除しない | 後続 declaration / plan filename stem | `@audit:superseded-by(wyner-ziv-convexity-unconditional)` |
| `@audit:retract-candidate(REASON)` | 削除候補。circular passthrough で honest 経路が他にあるケース等 | REASON 短文 (kebab-case) | `@audit:retract-candidate(circular-passthrough)` |

### 複数タグの併用

1 つの def/theorem に `@residual` + `@audit:*` が同居しうる。順序は意味別:

```lean
/-- ...

@residual(wall:n-dim-gaussian-aep) @audit:defer(awgn-achievability-typicality) -/
theorem foo : ... := by sorry
```

意味: 「壁: n-dim Gaussian AEP、AWGN typicality plan に defer 済」。

### 解除

状態が変わったら **タグ自体を編集する** (`@residual(wall:stam)` → `@audit:ok` 等)。タグは 1 declaration につき可能な限り 1 行にまとめて、`rg -A1` で前後文脈付きレビューしやすくする。

## 配置ルール

- **`@residual`**: docstring 末尾 (単一 sorry) または sorry 直前のラインコメント (複数 sorry)。
- **`@audit:*`**: 必ず docstring 内 (line comment ではなく `/-- ... -/`)。理由: docstring は declaration とライフサイクルが揃っており、grep で declaration と pair で取れる。
- **`@param` `@field` のような Lean doc-tools の予約形式とは衝突しない** (`@residual` / `@audit:` は Lean が解釈しない、純粋にコメント文字列)。

## grep レシピ

### 残課題集計

```bash
# residual 全件 (= sorry の分類済件数の下限)
rg "@residual" Common2026/ | wc -l

# class 別ヒストグラム
rg -o "@residual\([a-z]+:" Common2026/ | sort | uniq -c | sort -rn

# 特定壁の影響範囲
rg -nB1 "@residual\(wall:stam\)" Common2026/

# 特定 plan の closure 待ち件数
rg "@residual\(plan:epi-stam-closure\)" Common2026/

# tag 無し sorry (= 分類漏れ、CI で検出すべき)
rg -B2 "^\s*sorry\b" Common2026/ | rg -L "@residual"  # ※ rg -L は file 単位なので参考目安
```

### 完成状態の確認

```bash
# audit pass 済件数
rg "@audit:ok" Common2026/ | wc -l

# 残課題総数 (sorry + residual の整合確認用)
rg "\bsorry\b" Common2026/ | wc -l
rg "@residual" Common2026/ | wc -l
```

### plan からの逆検索

```bash
# AWGN typicality plan は何件を抱えるか
rg "@residual\(plan:awgn-achievability-typicality\)" Common2026/

# 後続 plan が closure 引き受ける declaration 件数
rg "@audit:closed-by-successor\(chernoff-converse-sanov-discharge\)" Common2026/

# 後続版に置き換え済の旧 declaration
rg "@audit:superseded-by\(" Common2026/
```

## 運用ルール

### 残課題の埋め方 (実装中)

実装中に dead-end に遭遇したら:

1. 仮説束 (`(h : <core claim>) → conclusion`) で核を bundling **しない**
2. signature を本来証明したい形に保つ
3. body を `sorry` にする
4. 直近 docstring/コメントに `@residual(<class>:<slug>)` を書く

これだけ。「honest 名前付き仮説」「`*Hypothesis` predicate」等の語彙は不要。

### 監査時の発見 → 即タグ付け

監査中に honesty issue を発見したら **その場で `sorry` 化 + `@residual` または `@audit:*` を docstring に書き込む**。次セッションのタスクリストやハンドオフに「これも audit したい」と書かない。

なぜ:
- タスクリストは current session 内で消える / ハンドオフは多重化して読み逃す。docstring は declaration とともに永続。
- 発見場所 = 修正場所なので、置き場が決定論的。
- レビュー時に diff で見える。

## 共有 Mathlib 壁: shared sorry 補題パターン

同じ壁 (例: Stam の不等式) を複数 file から参照する場合、**各 use site で個別に `sorry` を書かない**。1 ヶ所に「shared sorry 補題」を立て、他は normal な lemma 呼び出しで使う:

```lean
-- Common2026/Shannon/EPIStamWalls.lean
/-- Stam の不等式。Mathlib 未収録、closure 待ち。
@residual(wall:stam) -/
theorem stamInequality
    (μ : Measure ℝ) [...] :
    fisherInfo μ ≥ ... := by
  sorry

-- 各 consumer は普通に呼ぶ
theorem foo : ... := by
  have h := stamInequality μ ...
  ...
```

これにより:
- 壁 1 件 = `sorry` 1 件。重複しない。
- consumer 側 file は `@residual` を持たず、proof done 判定可能 (壁 file だけが未完成)。
- 壁 closure 時は shared 補題 1 件を埋めれば全 consumer が genuine 化。

## Deprecated (移行対象 — 別セッションで sweep)

以下のタグは旧 honesty workflow (load-bearing hyp 容認) の名残。新規導入禁止、既存は sorry-based に移行。

| 旧タグ | 移行先 |
|---|---|
| `@audit:suspect(PLAN)` (≒ 🟢ʰ load-bearing hyp) | 仮説解除 → signature を本来の形に → body `sorry` → `@residual(plan:<PLAN>)` |
| `@audit:staged(WALL)` (Mathlib 壁 predicate bundling) | predicate 削除 → 共有 sorry 補題に置換 → `@residual(wall:<WALL>)` |
| `@audit:defect(circular)` | 仮説解除 → signature 修正 → body `sorry` → `@residual(defect:circular)` |
| `@audit:defect(prop-true)` | `:True` slot 削除 → 該当 residual を sorry 化 → `@residual(defect:prop-true)` |
| `@audit:defect(launder)` | rename → signature が claim 通り → `sorry` + 適切な `@residual` |
| `@audit:defect(degenerate)` | 退化定義削除 / 修正 → `sorry` + `@residual` |
| 散文 `🟢ʰ` / `🟢ʰ load-bearing hypothesis` | 上記 `@audit:suspect` と同じ移行 |
| 散文 `**NOT a discharge**` / `**load-bearing — NOT a discharge.**` | 同上 |
| 散文 `⚠️ OPEN — conclusion-as-hypothesis` | `@audit:defect(circular)` と同じ移行 |

### 移行レシピ (suspect 1 件あたり)

```lean
-- 旧
/-- Stam ineq 経由の EPI step.
@audit:suspect(epi-stam-closure) -/
theorem epiStep
    (hStam : StamInequalityHolds μ ν)  -- ← load-bearing hyp
    (h... : ...) :  -- 残りは regularity
    epi μ ν := by
  exact ... hStam ...

-- 新
/-- Stam ineq 経由の EPI step.
@residual(plan:epi-stam-closure) -/
theorem epiStep
    (h... : ...) :  -- regularity だけ残す
    epi μ ν := by
  sorry
```

ポイント:
- `StamInequalityHolds` のような **core を抱える predicate hypothesis を削除**
- regularity (`IsFiniteMeasure`, full-support 等) は precondition なので残す
- body は `sorry` だけ
- tag を `@residual(plan:...)` に書換

shared sorry 補題化する場合は `StamInequalityHolds` を削除した代わりに `stamInequality μ ...` を body で呼び出し、補題側に `sorry` + `@residual(wall:stam)` を集約。

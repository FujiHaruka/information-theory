# Audit tags — code-as-source-of-truth 規約

honesty audit の状態 (defect / suspect / staged / defer) を **コード内 docstring に構造化タグで埋め込む** ことで、grep が単一の source of truth になる。snapshot 文書ではなく、コード自身が「現状どうなっているか」を答える。

## 動機

- snapshot 文書 (defect-101 report 等) は **書いた瞬間から陳腐化** する。defect 数が変わっても文書は更新されない。
- 散文表現 (`🟢ʰ`, `(未着手)`, "NOT a discharge", "load-bearing hypothesis") が併存していると **集計不能** + 表現ゆれで grep 信頼度が落ちる。
- 監査で発見した新規 issue を「次セッションのタスク」に保管するのではなく、**発見した場所 (= 当該 docstring)** に埋め込めば、タスクリストが肥大化しない。

## 語彙

すべて `@audit:KIND(SLUG)` 形式。Lean docstring (`/-- ... -/`) 内に直書きする。

| タグ | 意味 | SLUG の中身 | 例 |
|---|---|---|---|
| `@audit:ok` | honesty 確認済。data def や trivial helper、または audit pass で `ok` 判定 | (なし) | `@audit:ok` |
| `@audit:suspect(PLAN)` | honest load-bearing hyp (`🟢ʰ` の後継表現)。標準B 残課題、type ≠ conclusion | discharge 予定 plan の filename stem。plan が無ければ `""` | `@audit:suspect(epi-stam-closure)` |
| `@audit:defect(KIND)` | honesty 違反。`type ≡ conclusion` / `Prop := True` / name-laundering / vacuous def | KIND ∈ `{circular, prop-true, launder, degenerate, false-statement}` | `@audit:defect(circular)` |
| `@audit:defer(PLAN)` | 該当 def/theorem の discharge を別 plan に切り出した | PLAN filename stem (no `.md`) | `@audit:defer(awgn-achievability-typicality)` |
| `@audit:staged(WALL)` | Mathlib 壁で intentionally staged。長期残課題 | WALL ∈ `{stam, csiszar, n-dim-gaussian-aep, sphere-volume, fourier, ...}` (extensible) | `@audit:staged(n-dim-gaussian-aep)` |
| `@audit:retract-candidate(REASON)` | 削除候補。circular passthrough で honest 経路が他にあるケース等 | REASON 短文 (kebab-case) | `@audit:retract-candidate(circular-passthrough)` |
| `@audit:closed-by-successor(SLUG)` | 当該 plan は計画通り完成、ただし load-bearing hyp の discharge を**後続 plan** に明示的に切り出して委譲している。`suspect` の「要再検査」ニュアンスは外れたが、後続 plan が closure する前提で残っている honest hyp 持ち wrapper | 後続 plan filename stem | `@audit:closed-by-successor(chernoff-converse-sanov-discharge)` |
| `@audit:superseded-by(SLUG)` | 当該 declaration は**後続版に置き換え済**で残置されている (`_unconditional` 版が併存している `_of_condEntDiff` conditional 版等)。retract-candidate に近いが、history record / API 後方互換のため削除しない判断付き | 後続 declaration / plan filename stem | `@audit:superseded-by(wyner-ziv-convexity-unconditional)` |

### 複数タグの併用

1 つの def/theorem に複数タグが付きうる。順序は意味別:

```lean
/-- ...

`@audit:defect(circular)` `@audit:defer(awgn-achievability-typicality)` `@audit:staged(n-dim-gaussian-aep)` -/
def IsAwgnTypicalityHypothesis ...
```

意味: 「circular defect で、AWGN typicality plan に defer 済、Mathlib 壁は n-dim Gaussian AEP」。

### 解除

状態が変わったら **タグ自体を編集する** (`defect(circular)` → `suspect(awgn-typicality)` 等)。書き換え忘れを防ぐため、タグは 1 declaration につき可能な限り 1 行にまとめて、`rg -A1` で前後文脈付きレビューしやすくする。

### `suspect` と `closed-by-successor` / `superseded-by` の区別

- **`suspect(<slug>)`**: 当該 declaration の honest hyp が plan の主たる discharge 対象である。plan が完了するまで「要再検査」状態。
- **`closed-by-successor(<successor-slug>)`**: 当該 declaration が属する plan は完成 (plan body Status が DONE-HONEST-HYPS 等)。残存している load-bearing hyp の discharge は別の後続 plan に分離されており、本 declaration は計画通りの完成 wrapper。後続 plan の完成で hyp が hyp pass-through 経由で genuine 化される見込みあり。
- **`superseded-by(<replacement>)`**: 後続版 (typically `_unconditional` 版) が既に存在している旧 declaration の残置。typically `_of_condEntDiff` 等の conditional 版が unconditional 版に置き換えられた後の history record。

判定基準: 「**親 plan が DONE 表記済か否か**」 + 「**後続 plan / 後続 declaration を URL/slug で名指しできるか否か**」。両方 Yes なら `closed-by-successor` または `superseded-by`。片方でも No なら `suspect` のまま据え置き。

## 配置ルール

- **必ず docstring 内** (line comment ではなく `/-- ... -/`)。理由: docstring は declaration とライフサイクルが揃っており、grep で declaration と pair で取れる。
- **docstring 末尾** に置く (本文の散文の後)。docstring の冒頭は説明、末尾はメタデータ、という構造を採用。
- **`@param` `@field` のような Lean doc-tools の予約形式とは衝突しない** (`@audit:` は Lean が解釈しない、純粋にコメント文字列)。

## grep レシピ

### 現状計数

```bash
# defect 全件数 (現 SoT)
rg "@audit:defect" Common2026/ | wc -l

# suspect 全件数
rg "@audit:suspect" Common2026/ | wc -l

# Mathlib 壁別の集計
rg -o "@audit:staged\([a-z-]+\)" Common2026/ | sort | uniq -c | sort -rn

# 特定 plan に defer されている件数
rg "@audit:defer\(awgn-achievability-typicality\)" Common2026/ | wc -l

# defect の種別ヒストグラム
rg -o "@audit:defect\([a-z-]+\)" Common2026/ | sort | uniq -c | sort -rn
```

### 出現箇所一覧

```bash
# defect 全件 (file:line + 短い context)
rg -nB1 "@audit:defect" Common2026/

# circular defect だけ
rg -nB1 "@audit:defect\(circular\)" Common2026/

# 特定 Mathlib 壁の影響範囲
rg -nB1 "@audit:staged\(stam\)" Common2026/
```

### plan からの逆検索

```bash
# AWGN typicality plan は何件を抱えるか
rg "@audit:defer\(awgn-achievability-typicality\)" Common2026/

# 後続 plan が closure 引き受ける declaration 件数
rg "@audit:closed-by-successor\(chernoff-converse-sanov-discharge\)" Common2026/

# 後続版に置き換え済の旧 declaration
rg "@audit:superseded-by\(" Common2026/
```

## 運用ルール (発見時即時タグ付け)

監査中 / 実装中に honesty issue を発見したら **その場で docstring にタグを書き込む**。次セッションのタスクリストやハンドオフに「これも audit したい」と書かない。

- 発見 → docstring 編集 → commit (1 turn)
- 「あとで audit する」と思った時点で、`@audit:suspect("")` (plan 未確定) を仮置きしてもよい。後で `suspect(PLAN)` に確定する。

なぜ:
- タスクリストは current session 内で消える / ハンドオフは多重化して読み逃す。docstring は declaration とともに永続。
- 発見場所 = 修正場所なので、置き場が決定論的。
- レビュー時に diff で見える (DB だと invisible)。

## 既存表現との対応

cleanup 中に併存していた散文表現は以下のタグへ集約 (Phase 3 sweep で順次置換):

| 旧表現 | 新タグ |
|---|---|
| `🟢ʰ` / `🟢ʰ load-bearing hypothesis` | `@audit:suspect(PLAN)` |
| `**NOT a discharge**` | `@audit:suspect(PLAN)` |
| `**load-bearing hypothesis — NOT a discharge.**` | `@audit:suspect(PLAN)` |
| `(未着手)` / `(plan drafted; body pending)` | (削除、`@audit:defer(PLAN)` に集約) |
| `⚠️ OPEN — conclusion-as-hypothesis` | `@audit:defect(circular)` |
| `type ≡ conclusion` | `@audit:defect(circular)` |
| `Renamed from ... (laundering)` | `@audit:defect(launder)` (該当時のみ、rebrand 済なら `ok`) |
| `Mathlib 壁` の言及 | `@audit:staged(WALL)` |

ただし **散文の本文は残す** — タグは集計用の付加情報であって、人間向けの説明を置き換えない。`@audit:defect(circular)` だけ書いて conclusion 同一性の解説を消すのは NG。

## Phase 3 sweep 対象 (現時点で確定している付与対象)

- `Common2026/Shannon/AWGNAchievability.lean:44, 76` — `@audit:defect(circular)` `@audit:defer(awgn-achievability-typicality)` `@audit:staged(n-dim-gaussian-aep, sphere-volume)`
- `Common2026/Shannon/BrunnMinkowski.lean:132, 188` — `@audit:defect(circular)` `@audit:defer(brunn-minkowski-from-epi-discharge)` `@audit:staged(epi-n-dim)`
- `Common2026/Shannon/ParallelGaussian.lean:285, 392` — `@audit:retract-candidate(circular-passthrough)` `@audit:defer(pg-honest-rewire)`
- `Common2026/Shannon/ParallelGaussianL_PG0Discharge.lean:170, 194` — 同上

Phase 3 完了後は `rg "@audit:defect" Common2026/` で defect 3 件 (`circular`) が hit する想定。Phase 4 以降で suspect 381 件、staged 全件、への展開。

# BC 未解決問題 — attack 台帳

> 個々の attack の**状態と死因**の単一の真実源。運用規約 (no empty leg / kill-first / round-robin /
> harvest line) は親 [`bc-open-problem-plan.md`](bc-open-problem-plan.md) §5 が SoT。
> 文献事実・数値判定・機械検証の確定は [`bc-facts.md`](bc-facts.md) 側。
>
> **状態**: `live` (進行中) / `killed` (死亡、死因必須) / `parked` (3 leg ゼロ進捗で退避) /
> `harvested` (収穫して終了) / `todo` (未着手)
> **死因の語彙**: `numeric-counterexample` / `known-result` / `probe-failed` / `too-hard` /
> `mathlib-wall`
>
> ⚠ `killed` の行は**削除しない**。plan hygiene の「決着済は削除」の例外 — ここでは死因そのものが
> 資産で、削除すると長期 relay が同じ壁に再び当たる。

## Attack 一覧

| slug | 軸 | 状態 | 直近 leg | 死因 / 現況 | 残った副産物 |
|---|---|---|---|---|---|
| `lit-landscape` | — | `todo` | — | 親 plan §1.1 の F1–F8 を原論文で verbatim 確認 (Leg 0) | — |
| `weakest-hyp-morecapable` | A | `todo` | — | `bc_moreCapable_uv_subset_superposition` の実使用仮説を最弱化 (Leg 1) | — |
| `outer-slack-localize` | B | `todo` | — | `bc_capacity_subset_uv` の不等号ステップを全列挙し等号成立条件を書き出す | — |
| `jog-nair-inequality` | C | `todo` | — | BSSC の情報不等式を Lean で述べる (T1) | — |
| `multiletter-subject` | D | `todo` | — | multi-letter 表現の Lean 構成 + 「単一文字特徴付けを持つ」の定義候補 (Leg 2) | — |
| `product-bc-tensor` | E | `todo` | — | 積 BC の構成と非加法性の例 | — |
| `cardinality-bound` | F | `todo` | — | Fenchel–Eggleston が Mathlib 不在ゆえ高コスト。予備 | — |

## 軸ごとの連続ゼロ進捗カウント (round-robin 判定用)

| 軸 | 連続ゼロ進捗 leg 数 | 判定 |
|---|---|---|
| A | 0 | — |
| B | 0 | — |
| C | 0 | — |
| D | 0 | — |
| E | 0 | — |
| F | 0 | — |

3 に達した軸は `parked` にして別軸へ移る (親 plan §5-5)。

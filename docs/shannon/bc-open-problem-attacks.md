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

## Leg 予算

**20 leg** (L0–L20 の枠割りは親 plan §6.2 が SoT)。延長判断は L20 完了時点。
**固定枠**: L0 文献 / L1 probe 基盤 / L4・L9・L14 棚卸し / **L19 収穫・L20 記録 (予約済、探索に流用しない)**。
**現在**: leg 0 / 20 (未着手)。

## Attack 一覧

| slug | 軸 | 状態 | 直近 leg | 死因 / 現況 | 残った副産物 |
|---|---|---|---|---|---|
| `lit-landscape` | — | `todo` | — | 親 plan §1.1 の F1–F8 を原論文で verbatim 確認 (L0) | — |
| `probe-harness` | — | `todo` | — | `bc-marton-union-gap-check.py` を候補命題差し替え可能な形へ一般化 (L1)。kill-first の道具 | — |
| `weakest-hyp-morecapable` | A | `todo` | — | `bc_moreCapable_uv_subset_superposition` の実使用仮説を最弱化 (L2) | — |
| `outer-slack-localize` | B | `todo` | — | `bc_capacity_subset_uv` の不等号ステップを全列挙し等号成立条件を書き出す | — |
| `jog-nair-inequality` | C | `todo` | — | BSSC の情報不等式を Lean で述べる (T1) | — |
| `multiletter-subject` | D | `todo` | — | multi-letter 表現の Lean 構成 + 「単一文字特徴付けを持つ」の定義候補 (Leg 2) | — |
| `product-bc-tensor` | E | `todo` | — | 積 BC の構成と非加法性の例 | — |
| `cardinality-bound` | F | `todo` | — | Fenchel–Eggleston が Mathlib 不在ゆえ高コスト。予備 | — |

## 候補経路 (本 relay の主成果物)

親 plan §3.1 の 5 条件を**すべて**満たしたものだけをここに載せる。満たさないものは下の `idea` 枠。
確信度ラベル (`probed` / `unprobed` / `refuted`) は §3.2。中身の散文は `bc-open-problem-routes.md`。

| route | 軸 | 主張 (1 文) | 5 条件 | 確信度 | 最終更新 leg |
|---|---|---|---|---|---|
| (まだ無い) | | | | | |

**到達目標** (L14 の収穫判定): 最低ライン = 経路 ≥ 2 本 / うち `probed` ≥ 1 本。目標 = ≥ 3 本 / ≥ 2 本。

## idea 枠 (経路の 5 条件を満たす前のもの)

量産してよい。制約をかけるのは経路への昇格時だけ。

| idea | 軸 | 中身 | 起票 leg |
|---|---|---|---|
| (まだ無い) | | | |

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

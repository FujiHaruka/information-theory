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
**現在**: leg 1 / 20 (**L0 完了** 2026-08-01 — 次は L1)。

## Attack 一覧

| slug | 軸 | 状態 | 直近 leg | 死因 / 現況 | 残った副産物 |
|---|---|---|---|---|---|
| `lit-landscape` | — | `harvested` | **L0** | **完了**。F1–F8 + 外部ノート V6–V10 を原論文で verbatim 確認し `bc-facts.md` に 13 行。うち **F3 REFUTED** (UV は最良既知 outer でない) / **F7 は plan より強い** (`Δ₁₈ᴴ`) / **F4・F6・F8 は PARTIAL** (帰属・内容・出典の誤り) / 外部ノートの文献層は生存 (V9 は日付まで一致) | 訂正済ランドスケープ (親 plan §1.1 / §1.3) + 下記の子 attack 6 本 |
| `probe-harness` | — | `todo` | — | `bc-marton-union-gap-check.py` を候補命題差し替え可能な形へ一般化 + テストケース 2 本 = 外部ノート V1–V3 と `markovity-local-max-repro` (L1)。kill-first の道具 | — |
| `selftensor-reduction` | E+D | `todo` | — | **L2 = 本 relay の分岐点**。外部ノート V4 / V5 — multi-letter 表現 (定理1) と support function 経由の還元 (3) が我々の定義で生きているか。**+ L0 が足した項目**: support function `h_n^T(θ)` の加法性が既知予想の双対汎関数 `F(T,{a_x})` の加法性と同一命題か (どちらの文献も述べていない) | — |
| `selftensor-counterexample` | E | `todo` | — | 同一チャネルの自己テンソルで `h_2 > 2 h_1` を数値探索 (外部ノート (11))。これが 1 つ出れば `C(T) ⊋ M(T)` が直ちに従う。**L2 が生きたら着手**。⚠ 還元自体は既知ゆえ、軸 E で新規性を主張できるのはここ | — |
| `weakest-hyp-morecapable` | A | `todo` | — | `bc_moreCapable_uv_subset_superposition` の実使用仮説を最弱化 (L3) | — |
| `outer-slack-localize` | B | **`killed`** | **L0** | **死因 `known-result`** — 「UV の証明で捨てた項を拾って新しい outer を作る」は Gohari–Nair Theorem 7 (auxiliary-receiver approach、IEEE TIT 68(2):701–736, 2022) が既に実行済で、その導出法が逐語で「UV 導出で捨てられる項を最小化する」もの (F3)。着手前に文献で死亡 | 子 attack 2 本 (`outer-slack-vs-thm7` / `jbound-optimality`) |
| `outer-slack-vs-thm7` | B | `todo` | — | **`outer-slack-localize` の死因から起票** (親 plan §5-9)。先に Theorem 7 の改善項リストを抽出 → `bc_uv_converse` / `bc_capacity_subset_uv` の不等号ステップを全列挙して対応付ける。**対応が付かないステップ = 我々固有の緩み**。⚠ 順序を逆にすると既知の再発見 | — |
| `jbound-optimality` | B | `todo` | — | 同上の子。J version of UV outer bound の最適性は Li が逐語で "optimality unknown" ⟹ ここは開いている。J-bound が緩む例を探す | — |
| `jog-nair-inequality` | C | `todo` | — | BSSC の情報不等式を Lean で述べる (T1)。⚠ この不等式は inner の明示評価を**可能にする**道具 (F4 の訂正) | — |
| `multiletter-subject` | D | `todo` | — | multi-letter 表現の Lean 構成 + **Li の Table I のレベル (`Σ₁ᴴ` / `Π₂ᴴ` / `Δ₁₈ᴴ`) と我々の在庫の等号定理の対応付け** (L2)。⚠ 旧「単一文字特徴付けを持つ、の定義候補」は F7 で肯定決着済ゆえ主語を差し替え | — |
| `bc-computability-openness` | D | `todo` | — | **F8 の NOT-FOUND から起票**。「BC 容量領域の計算可能性は未決」と明示する一次文献が見つかっていない。否定的解決を標的にする前に出典を立てるか、**無いことを確定事実にする** (⚠ Fawzi–Fermé arXiv:2310.05515 は一発符号化の近似困難性で別物) | — |
| `markovity-conjecture` | G | `todo` | — | Gohari–Liu–Nair (ISIT 2025) **Conjecture 2 (Markovity Conjecture)** = 「Marton 領域の極点評価では `U → (W,X) → V` を持つ組だけで十分」。**真に未解決、根拠は数値証拠のみ** (`|X|=3,4,5` で各 10,000 チャネル超)。本 relay 最大の近距離標的 (L5)。⚠ 局所最適性条件だけで証明する路線は論文自身の反例が潰している | — |
| `markovity-local-max-repro` | G | `todo` | — | 同論文 §III-B の局所最大点インスタンス (`X=Y=Z={A,B,C}`、`{a_x}` / `α` / `λ` / 3×3 遷移行列 2 枚 / 目的値 4 つがすべて明示) の数値再現。**L1 harness の 2 つ目のテストケース = 既知の答えがある検証課題** | — |
| `sum-bc-classes` | A | `todo` | — | arXiv:2606.12839 (Gohari–Liu–Nair, 2026-06-11) が degraded / less noisy / more capable / deterministic / semi-deterministic **成分の和 (sum) BC** で auxiliary-receiver 外界 = Marton を示した。我々は成分クラス 3 本の等号定理を Lean で持つ ⟹ 軸 A の最弱仮説抽出がそのまま乗る。⚠ **積ではなく和** — 軸 E のテンソル冪とは別演算 | — |
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
| `residual-as-slack-diagnostic` | B | 外部ノートの残差恒等式 (5) は「一文字化がどこで壊れるか」を明示する。これを我々の `bc_capacity_subset_uv` の緩みの局所化に転用できないか | L(-1) |
| `absorption-as-class-def` | A+E | 外部ノートの吸収条件 (9) `Δ₁₂ ≤ N₁₂ + G₁₂` を**満たすチャネルのクラス**として定義すると、既知クラス (degraded / less noisy / more capable) を含む新クラスになるか。軸 A の最弱仮説抽出と合流しうる | L(-1) |
| `collider-conditioning` | C | 残差の正体が collider conditioning (独立な `A,B` が共通の子 `Y₁` を条件付けて従属化) なら、その現象を直接測る情報量が新しい情報不等式の候補になる | L(-1) |
| `markovity-as-class-def` | G+A | Markovity 予想が**成り立つチャネルのクラス**を定義すると、我々が等号を持つ 3 クラス (degraded / less noisy / more capable) を含むか。含むなら軸 A の最弱仮説抽出と合流し、含まないならクラスの境界が新しい標的になる | L0 |

## 軸ごとの連続ゼロ進捗カウント (round-robin 判定用)

| 軸 | 連続ゼロ進捗 leg 数 | 判定 |
|---|---|---|
| A | 0 | — |
| B | 0 | L0 は軸に紐づかない文献 leg。**死亡も確定事実**なのでゼロ進捗ではない (親 plan §5-1) |
| C | 0 | — |
| D | 0 | — |
| E | 0 | — |
| F | 0 | — |
| G | 0 | L0 で新設 (親 plan §4 軸 G) |

3 に達した軸は `parked` にして別軸へ移る (親 plan §5-5)。

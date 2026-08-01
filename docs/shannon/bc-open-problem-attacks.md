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
**現在**: leg 3 / 20 (**L2 完了** 2026-08-01 — 次は L3)。

## Attack 一覧

| slug | 軸 | 状態 | 直近 leg | 死因 / 現況 | 残った副産物 |
|---|---|---|---|---|---|
| `lit-landscape` | — | `harvested` | **L0** | **完了**。F1–F8 + 外部ノート V6–V10 を原論文で verbatim 確認し `bc-facts.md` に 13 行。うち **F3 REFUTED** (UV は最良既知 outer でない) / **F7 は plan より強い** (`Δ₁₈ᴴ`) / **F4・F6・F8 は PARTIAL** (帰属・内容・出典の誤り) / 外部ノートの文献層は生存 (V9 は日付まで一致) | 訂正済ランドスケープ (親 plan §1.1 / §1.3) + 下記の子 attack 6 本 |
| `probe-harness` | — | `harvested` | **L1** | **完了**。基盤 `bc_probe.py` (情報量式の記号展開 / 構造制約つき掃引 / 補助変数上の最大化、selftest 18 項目) + 実行可能 probe 2 本。使い方は親 plan §2.1。テストケース (a) 外部ノート V1–V3 は**3 本とも TRUE**、うち V1 は係数相殺による**証明** (掃引ではない)、V2 は**強化つき** (無仮定の (5) の残差が正確に `I(A;B) − I(Y₁;Z₂∣A,B)` ⟹ ノートの 2 仮定はちょうど必要十分)。⚠ **ノートへの訂正 1 件**: V3 の数値例は**ノート自身の結論には不要** — 残差が相互情報量 2 本の和ゆえ設定下で `Φ ≥ Ψ` は恒真で、例が示すのは「残差が恒等的に 0 ではない」ことだけ。逐語 → [`bc-facts.md`](bc-facts.md) §数値 probe の判定 (L1) | 基盤そのもの (以後の全 attack の入力) + idea `residual-as-slack-diagnostic` の裏づけ (残差の**閉じた式**が確定) |
| `selftensor-reduction` | E+D | `harvested` | **L2** | **完了**。4 判定。**V4 = 条件つき生存** — 定理1 の逆側は我々の `bcCapacityRegion` の上で成立し、しかも**共通メッセージ層は不要** (私信のみの定義ゆえ)。ただし**達成側は在庫では閉じない** (`marton_region_subset_capacity` の full-support 仮説を決定論的符号器が満たさない)。**V5 = 還元 (3) は support function 経由ゆえ*閉凸包*の命題**。`martonRegionUnion` は既に `closure` 済で未証明なのは凸性だけ ⟹ 「closure を取れば入る」退路は最初から無く、劣化 BSC 対で測ったギャップは凸性ギャップではなく**本物の support function ギャップ** (`λ* = 0.2622134001` で `+2.23e-03`)。**V5-b = (11) は我々の 2 補助変数 `def` の上では自明に充足** — 原因は非加法性ではなく共通補助 `U₀` の欠落なので**保証された偽陽性**。**新項目 = `h_n^T(θ)` 加法性と `F(T,{a_x})` 加法性は別命題** (定義域・汎関数の型・共通補助の扱いの 3 点で食い違い、どちらも他方を構文的に含まない)。逐語 → [`bc-facts.md`](bc-facts.md) §定義照合と数値 probe の判定 (L2) | `bc-marton-convexhull-check.py` + 下記の子 attack 3 本 (`marton-3aux-probe` / `support-vs-dual-additivity` / `u0-necessity-quantified`) + **既存の負の判定行の射程拡大** (union までの距離 → 閉凸包までの距離) |
| `selftensor-counterexample` | E | `todo` | — | ⚠ **ブロッキング前提**: **我々の `martonRegionUnion` (2 補助変数) の上で走らせてはならない** (V5-b: 保証された偽陽性)。**3 補助変数版 `M(T)` を probe 側に用意すること = `marton-3aux-probe` が前提**。その上での中身 = 同一チャネルの自己テンソルで `h_2 > 2 h_1` を数値探索 (外部ノート (11))。これが 1 つ出れば `C(T) ⊋ M(T)` が直ちに従う。⚠ 還元自体は既知ゆえ、軸 E で新規性を主張できるのはここ | — |
| `marton-3aux-probe` | E | `todo` | — | **V5-b から起票** (§5-9)。3 補助変数 Marton 領域 (共通補助 `U₀` つき、[`bc-facts.md`](bc-facts.md) F2 の Jog–Nair Bound 1 の形) を**数値 probe 側に**用意する。`selftensor-counterexample` のブロッキング前提。⚠ **Lean 側の新規実装は層 3 でスコープ外** (親 plan §2.1) — `bc_probe.py` の消費者として probe 側に閉じること | — |
| `support-vs-dual-additivity` | E | `todo` | — | **新項目の判定「別命題」から起票** (§5-9)。`h_n^T(θ)` の加法性と `F(T,{a_x})` の加法性を繋ぐのに要る 2 段のうち、(b) `{a_x}` ↔ `θ` の Legendre / 上凹包の段を明示的に書き下せるか ((a) は `M` の閉凸性)。**親 plan §4 軸 E の新規性 (ii) の実体**で、どちらの文献も述べていない | — |
| `u0-necessity-quantified` | A+E | `todo` | — | **V5 の副産物から起票** (§5-9)。2 補助変数 Marton union の閉凸包が劣化 BSC 対で**時分割領域そのものに潰れる** (`S(λ)` が退化コーナー 2 つの上包絡と全 `λ` で一致、最大偏差 `+3.331e-16`)。⚠ 2 元入力なので F6 (randomized time-division が Marton の sum rate を達成) と整合し、**非自明になるのは `\|X\| ≥ 3` から**。潰れないチャネルを 1 つ見つければ「共通補助 `U₀` 無しでも時分割より真に強い」の実例になり、`U₀` の必要性の定量になる | — |
| `weakest-hyp-morecapable` | A | `todo` | — | `bc_moreCapable_uv_subset_superposition` の実使用仮説を最弱化 (L3) | — |
| `outer-slack-localize` | B | **`killed`** | **L0** | **死因 `known-result`** — 「UV の証明で捨てた項を拾って新しい outer を作る」は Gohari–Nair Theorem 7 (auxiliary-receiver approach、IEEE TIT 68(2):701–736, 2022) が既に実行済で、その導出法が逐語で「UV 導出で捨てられる項を最小化する」もの (F3)。着手前に文献で死亡 | 子 attack 2 本 (`outer-slack-vs-thm7` / `jbound-optimality`) |
| `outer-slack-vs-thm7` | B | `todo` | — | **`outer-slack-localize` の死因から起票** (親 plan §5-9)。先に Theorem 7 の改善項リストを抽出 → `bc_uv_converse` / `bc_capacity_subset_uv` の不等号ステップを全列挙して対応付ける。**対応が付かないステップ = 我々固有の緩み**。⚠ 順序を逆にすると既知の再発見 | — |
| `jbound-optimality` | B | `todo` | — | 同上の子。J version of UV outer bound の最適性は Li が逐語で "optimality unknown" ⟹ ここは開いている。J-bound が緩む例を探す | — |
| `jog-nair-inequality` | C | `todo` | — | BSSC の情報不等式を Lean で述べる (T1)。⚠ この不等式は inner の明示評価を**可能にする**道具 (F4 の訂正) | — |
| `multiletter-subject` | D | `todo` | — | multi-letter 表現の Lean 構成 + **Li の Table I のレベル (`Σ₁ᴴ` / `Π₂ᴴ` / `Δ₁₈ᴴ`) と我々の在庫の等号定理の対応付け** (L2)。⚠ 旧「単一文字特徴付けを持つ、の定義候補」は F7 で肯定決着済ゆえ主語を差し替え | — |
| `bc-computability-openness` | D | `todo` | — | **F8 の NOT-FOUND から起票**。「BC 容量領域の計算可能性は未決」と明示する一次文献が見つかっていない。否定的解決を標的にする前に出典を立てるか、**無いことを確定事実にする** (⚠ Fawzi–Fermé arXiv:2310.05515 は一発符号化の近似困難性で別物) | — |
| `markovity-conjecture` | G | `todo` | — | Gohari–Liu–Nair (ISIT 2025) **Conjecture 2 (Markovity Conjecture)** = 「Marton 領域の極点評価では `U → (W,X) → V` を持つ組だけで十分」。**真に未解決、根拠は数値証拠のみ** (`\|X\|=3,4,5` で各 10,000 チャネル超)。本 relay 最大の近距離標的 (L5)。⚠ 「局所最適性条件だけで証明する路線は論文自身の反例が潰している」は **L1 で弱まった** (下記 `markovity-localopt-route`) | — |
| `markovity-local-max-repro` | G | `harvested` | **L1** | **完了、ただし想定外の結果**。目的値 4 つは**8 桁全桁再現** (harness は既知の答えに対して検証された)。一方、論文が §III-B で逐語 "satisfies (4), (7) and (8)" と書く 3 条件のうち**成立するのは (4) だけで、(7)/(8) は `+1.08e-03` / `+2.79e-03` 違反する** — 改善の witness は明示 (種類 2/3 = 補助アルファベットを 1 増やす摂動、改善方向は決定論的境界)。**実装に関与していない独立エージェントの敵対的監査 (自前再実装・コード非共有) が CONFIRMED**、加えて**肯定コントロール** (同一インスタンスの大域最大点では論文の条件が全て成立) で「コードの性質ではない」を分離した。⚠ **射程の限定 (監査が追加)**: 論文が §I で引く濃度限界 `\|U\|+\|V\| ≤ \|X\|+1 = 4` を課した空間の内側では報告点は**真の局所最大** (改善摂動は `\|U\|+\|V\|=5` へ出る)。**論文への影響範囲**: Conjecture 1 / Conjecture 2 / 目的値 4 つ / §IV Theorem 2 はいずれも**無傷**。逐語と再検証コマンド → [`bc-facts.md`](bc-facts.md) §数値 probe の判定 (L1) の (b) 行 | 検証済 harness + 子 attack 2 本 (`markovity-localopt-route` / `cardinality-localmax-boundary`) |
| `markovity-localopt-route` | G | `todo` | — | **`markovity-local-max-repro` の結果から起票** (親 plan §5-9)。**確立している事実**: §III-B の報告点は、論文が §III で自ら定義する 3 種の摂動の意味では (7)/(8) を満たさない (独立監査 + 肯定コントロール、上行)。**ここから先は推論であって確立していない**: ⟹ §II-B が「局所最適性条件による証明路線の障害」として提示したインスタンスは、**主張されたほどには路線を塞いでいない**かもしれない。⚠ **自動的には従わない** — (i) 論文の記述は逐語 "we failed to do this" であって「この点が唯一の障害だ」とは書いていない、(ii) 濃度限界の内側では報告点は真の局所最大 (下記 `cardinality-localmax-boundary`) ⟹ **路線が開きうるのは濃度非制約の空間に限る**。**最初の一手 = 診断であって証明ではない**: (7)–(10) が非矩形パターン `A B / C A` を排除するのはどの濃度領域か、を harness で走査する。証明に投資するのは診断が生き残ってから (§5-2 kill-first) | — |
| `cardinality-localmax-boundary` | F | `todo` | — | **同じく `markovity-local-max-repro` から起票、ただし軸が違う**。濃度限界 `\|U\|+\|V\| ≤ \|X\|+1` を課すか否かが、**同一の点について「局所最大である / でない」を反転させる** (改善摂動はちょうど限界の外へ出る)。`F(T,{a_x})` の定義自体には濃度制約が無い (逐語 "where the maximum is taken over all p(u, v, x) defined on U × V × X") ので、**この 2 つは同じ最適化問題ではない**。最初の一手 = Marton 領域まわりの主張を「濃度制約の内側でしか成り立たないもの / 外でも成り立つもの」に仕分ける。⚠ 軸 F の旧コスト論拠 (Fenchel–Eggleston が Mathlib 不在) は**層 3 の話**で、本 relay (層 1–2) には効かない | — |
| `sum-bc-classes` | A | `todo` | — | arXiv:2606.12839 (Gohari–Liu–Nair, 2026-06-11) が degraded / less noisy / more capable / deterministic / semi-deterministic **成分の和 (sum) BC** で auxiliary-receiver 外界 = Marton を示した。我々は成分クラス 3 本の等号定理を Lean で持つ ⟹ 軸 A の最弱仮説抽出がそのまま乗る。⚠ **積ではなく和** — 軸 E のテンソル冪とは別演算 | — |
| `product-bc-tensor` | E | `todo` | — | 積 BC の構成と非加法性の例 | — |
| `cardinality-bound` | F | `todo` | — | 旧主語「cardinality bound の改善」は Fenchel–Eggleston が Mathlib 不在ゆえ高コスト = 予備枠だった。**L1 で軸 F の主語が「濃度限界がどの主張の生死を分けるか」へ変わった** (親 plan §4 軸 F、優先度 4 → 3) ⟹ 本行は改善路線として保持し、当面の実働は `cardinality-localmax-boundary` | — |

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
| `residual-as-slack-diagnostic` | B | 外部ノートの残差恒等式 (5) は「一文字化がどこで壊れるか」を明示する。これを我々の `bc_capacity_subset_uv` の緩みの局所化に転用できないか。**L1 で前提が強くなった** — 残差は散文の見込みではなく**閉じた式** `I(A;B) − I(Y₁;Z₂∣A,B)` として確定した (記号的に証明、`probe-harness` 行) ので、「どの項が緩みか」を式のレベルで名指せる | L(-1) |
| `absorption-as-class-def` | A+E | 外部ノートの吸収条件 (9) `Δ₁₂ ≤ N₁₂ + G₁₂` を**満たすチャネルのクラス**として定義すると、既知クラス (degraded / less noisy / more capable) を含む新クラスになるか。軸 A の最弱仮説抽出と合流しうる | L(-1) |
| `collider-conditioning` | C | 残差の正体が collider conditioning (独立な `A,B` が共通の子 `Y₁` を条件付けて従属化) なら、その現象を直接測る情報量が新しい情報不等式の候補になる | L(-1) |
| `markovity-as-class-def` | G+A | Markovity 予想が**成り立つチャネルのクラス**を定義すると、我々が等号を持つ 3 クラス (degraded / less noisy / more capable) を含むか。含むなら軸 A の最弱仮説抽出と合流し、含まないならクラスの境界が新しい標的になる | L0 |

## 軸ごとの連続ゼロ進捗カウント (round-robin 判定用)

| 軸 | 連続ゼロ進捗 leg 数 | 判定 |
|---|---|---|
| A | 0 | — |
| B | 0 | L0 は軸に紐づかない文献 leg。**死亡も確定事実**なのでゼロ進捗ではない (親 plan §5-1) |
| C | 0 | — |
| D | 0 | L2 で multi-letter 表現が我々の定義で**逆側だけ生きる**と確定 (`multiletter-subject` の入力)。⚠ ただし L2 は軸 E の leg なので**本軸のカウントはリセットしない** (下記の二重計上の注意) |
| E | 0 | L2 で V4 / V5 / 新項目が決着。⚠ ただし**決着の中身は軸 E 内の路線 1 本 (`selftensor-counterexample`) を条件付きで塞ぐもの** — 前提工事 `marton-3aux-probe` を挟むまで動かせない |
| F | 0 | L1 で主語が変わったが、**leg は消費していない** (下記の二重計上の注意) |
| G | 0 | L0 で新設 (親 plan §4 軸 G)。L1 (b) で確定事実 |

3 に達した軸は `parked` にして別軸へ移る (親 plan §5-5)。**L0 / L1 はどちらも軸に紐づかない固定枠
(文献 / 基盤) なので、その leg で触れなかった軸のカウントは進めない**。

⚠ **二重計上の注意**: L1 の (b) は軸 G の leg で得た事実だが、副産物として軸 F の主語を変えた。
**進捗として数えるのは軸 G の側だけ**にする — 同じ 1 事実で 2 つの軸のカウントをリセットすると、
round-robin (§5-5) が「回っているように見えて回っていない」状態を検出できなくなる。
**L2 も同じ扱い**: multi-letter 表現の確定は軸 D の入力になるが、L2 は軸 E の leg なので
**数えるのは軸 E の側だけ**にする。

# BC 未解決問題 — attack 台帳

> 個々の attack の**状態と死因**の単一の真実源。運用規約 (no empty leg / kill-first / round-robin /
> harvest line) は親 [`bc-open-problem-plan.md`](bc-open-problem-plan.md) §5 が SoT。
> 文献事実・数値判定・機械検証の確定は [`bc-facts.md`](bc-facts.md) 側。
>
> **状態**: `live` (進行中) / `killed` (死亡、死因必須) / `parked` (3 leg ゼロ進捗で退避) /
> `harvested` (収穫して終了) / `todo` (未着手)
> ⚠ **語彙の穴 (L5 で発覚、改定は提案のみ)**: 「進捗はあったが**前提工事が入るまで進めない**」に当たる状態が
> 無い。`parked` はゼロ進捗による退避の意味なので、流用すると「回しても進まなかった」と
> 「別の工事待ち」が同じ語で表示される (L4 が §5-5 のカウンタで見つけたのと同じ形の欠陥)。
> **提案**: `blocked(<前提の slug>)` を足す。当面は `parked` + 現況欄に前提と再開条件を明記して運用する。
> **死因の語彙**: `numeric-counterexample` / `known-result` / `probe-failed` / `too-hard` /
> `mathlib-wall`
>
> ⚠ `killed` の行は**削除しない**。plan hygiene の「決着済は削除」の例外 — ここでは死因そのものが
> 資産で、削除すると長期 relay が同じ壁に再び当たる。

## Leg 予算

**20 leg** (L0–L20 の枠割りは親 plan §6.2 が SoT)。延長判断は L20 完了時点。
**固定枠**: L0 文献 / L1 probe 基盤 / L4・L9・L14 棚卸し / **L19 収穫・L20 記録 (予約済、探索に流用しない)**。
**現在**: leg 6 / 20 (**L5 = 軸 G の第一手 完了** 2026-08-02 — 次は L6 = 軸 B `outer-slack-vs-thm7`)。

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
| `weakest-hyp-morecapable` | A | **`killed`** | **L3** | **死因 `probe-failed`** — `IsBCMoreCapable` を `IsBCMoreCapable.condMutualInfo_le` の結論そのものに差し替えると**通らない**。足りなかったのは `IsBCMoreCapable` の `def` 本体 (非条件つき比較) **1 本のみ** (chain の残り 6 本は差し替え仮説だけで通る)。さらに**両方向を機械検証したところ差し替え先は元クラスと同値** (`#print axioms` sorryAx-free) ⟹ **新クラス候補は 1 本も立たない**。⚠ 親 plan の「核は `condMutualInfo_le` 1 本」は `mutualInfo_out₂_le_out₁_of_moreCapable` 最終行の `exact hmc _` = **`def` の直接展開**を見落としていた。逐語 → [`bc-facts.md`](bc-facts.md) §機械検証 probe の判定 (L3) | 同値 2 本 (どちらも sorryAx-free) + probe 本体 [`bc-probe-l3-weakest-hyp.lean.txt`](bc-probe-l3-weakest-hyp.lean.txt) + 下記の子 attack 2 本 |
| `weakest-hyp-degraded-lessnoisy` | A | `todo` | — | **`weakest-hyp-morecapable` の死因から起票** (§5-9)。同じ最弱仮説抽出を degraded / less noisy の等号定理へ横展開する。⚠ **手順を訂正して適用すること** — 実使用の棚卸しは証明本文の `rg` ではなく `dep_graph.sh` の前方閉包で行い、**辺の向き先が `def` 自身か名前つき補題か**を区別する (more capable ではこの区別を落として「核は 1 本」と誤った)。⚠ more capable が同値で潰れた以上、**同じ形の同値で潰れる公算も高い** — 先に「条件つき版と非条件版が同値になる構造」がそのクラスにもあるかを確認してから probe を組む | — |
| `class-def-vs-consequence-gap` | A | `todo` | — | **同じ死因から起票、ただし主語が違う**。more capable では条件つき版と非条件版が同値だった (平均化) が、**これが同値にならないクラスはあるか**。同値にならないクラスがあれば、そこでは「帰結を定義に採る」が実際に真に広いクラスを生む = **軸 A の第一手が生きる場所**になる。最初の一手 = 3 クラス (degraded / less noisy / more capable) の定義を並べ、条件つき化が平均化で潰れるか否かを**構造として**判定する (probe より先に散文で) | — |
| `outer-slack-localize` | B | **`killed`** | **L0** | **死因 `known-result`** — 「UV の証明で捨てた項を拾って新しい outer を作る」は Gohari–Nair Theorem 7 (auxiliary-receiver approach、IEEE TIT 68(2):701–736, 2022) が既に実行済で、その導出法が逐語で「UV 導出で捨てられる項を最小化する」もの (F3)。着手前に文献で死亡 | 子 attack 2 本 (`outer-slack-vs-thm7` / `jbound-optimality`) |
| `outer-slack-vs-thm7` | B | `todo` | — | **`outer-slack-localize` の死因から起票** (親 plan §5-9)。先に Theorem 7 の改善項リストを抽出 → `bc_uv_converse` / `bc_capacity_subset_uv` の不等号ステップを全列挙して対応付ける。**対応が付かないステップ = 我々固有の緩み**。⚠ 順序を逆にすると既知の再発見 | — |
| `jbound-optimality` | B | `todo` | — | 同上の子。J version of UV outer bound の最適性は Li が逐語で "optimality unknown" ⟹ ここは開いている。J-bound が緩む例を探す | — |
| `jog-nair-inequality` | C | `todo` | — | BSSC の情報不等式を Lean で述べる (T1)。⚠ この不等式は inner の明示評価を**可能にする**道具 (F4 の訂正) | — |
| `multiletter-subject` | D | `todo` | — | multi-letter 表現の Lean 構成 + **Li の Table I のレベル (`Σ₁ᴴ` / `Π₂ᴴ` / `Δ₁₈ᴴ`) と我々の在庫の等号定理の対応付け** (L2)。⚠ 旧「単一文字特徴付けを持つ、の定義候補」は F7 で肯定決着済ゆえ主語を差し替え | — |
| `bc-computability-openness` | D | `todo` | — | **F8 の NOT-FOUND から起票**。「BC 容量領域の計算可能性は未決」と明示する一次文献が見つかっていない。否定的解決を標的にする前に出典を立てるか、**無いことを確定事実にする** (⚠ Fawzi–Fermé arXiv:2310.05515 は一発符号化の近似困難性で別物) | — |
| `markovity-conjecture` | G | **`parked`** (前提工事待ち) | **L5** | Gohari–Liu–Nair (ISIT 2025) **Conjecture 2 (Markovity Conjecture)** = 「Marton 領域の極点評価では `U → (W,X) → V` を持つ組だけで十分」。**真に未解決、根拠は数値証拠のみ** (`\|X\|=3,4,5` で各 10,000 チャネル超)。⚠ 「局所最適性条件だけで証明する路線は論文自身の反例が潰している」は **L1 で弱まった** (下記 `markovity-localopt-route`)。**L5 の第一手 = 「述べられるが偽」**: 第 1 形 ((U,V,W,X) 版) は共通補助が無いので在庫に主語が無く、第 2 形 (F 側) は `V₁ ⊥ V₂ ∣ X` として我々の support function へ移せる (命題 **M2**) が、**M2 は数値反例で FALSE** (`+7.147687e-04`、hardening 3 段 + 独立 4 系統 + 肯定コントロール 3 本)。⚠ **Conjecture 2 の反例ではない** — 論文の `F` に残る `−αH(Y) − (λ−α)H(Z) + Σ p(x)a_x` は線形項では相殺できないので M2 は部分族ではなく**移植**。逐語 → [`bc-facts.md`](bc-facts.md) §数値 probe の判定 (L5)。**park の理由はゼロ進捗ではなく前提工事**: 2 補助変数の在庫の上では行き止まりで、**軸 E に L2 が課したのと同一の `marton-3aux-probe` が挟まる**。**再開条件** = `marton-3aux-probe` または `support-vs-dual-additivity` のどちらかが済むこと | probe [`bc-markovity-conjecture-check.py`](bc-markovity-conjecture-check.py) (反例インスタンスを逐語ハードコード) + 子 attack `markovity-via-dual-F` + 下記 `markovity-localopt-route` への入力 |
| `markovity-local-max-repro` | G | `harvested` | **L1** | **完了、ただし想定外の結果**。目的値 4 つは**8 桁全桁再現** (harness は既知の答えに対して検証された)。一方、論文が §III-B で逐語 "satisfies (4), (7) and (8)" と書く 3 条件のうち**成立するのは (4) だけで、(7)/(8) は `+1.08e-03` / `+2.79e-03` 違反する** — 改善の witness は明示 (種類 2/3 = 補助アルファベットを 1 増やす摂動、改善方向は決定論的境界)。**実装に関与していない独立エージェントの敵対的監査 (自前再実装・コード非共有) が CONFIRMED**、加えて**肯定コントロール** (同一インスタンスの大域最大点では論文の条件が全て成立) で「コードの性質ではない」を分離した。⚠ **射程の限定 (監査が追加)**: 論文が §I で引く濃度限界 `\|U\|+\|V\| ≤ \|X\|+1 = 4` を課した空間の内側では報告点は**真の局所最大** (改善摂動は `\|U\|+\|V\|=5` へ出る)。**論文への影響範囲**: Conjecture 1 / Conjecture 2 / 目的値 4 つ / §IV Theorem 2 はいずれも**無傷**。逐語と再検証コマンド → [`bc-facts.md`](bc-facts.md) §数値 probe の判定 (L1) の (b) 行 | 検証済 harness + 子 attack 2 本 (`markovity-localopt-route` / `cardinality-localmax-boundary`) |
| `markovity-localopt-route` | G | `todo` | — | **`markovity-local-max-repro` の結果から起票** (親 plan §5-9)。**確立している事実**: §III-B の報告点は、論文が §III で自ら定義する 3 種の摂動の意味では (7)/(8) を満たさない (独立監査 + 肯定コントロール、上行)。**ここから先は推論であって確立していない**: ⟹ §II-B が「局所最適性条件による証明路線の障害」として提示したインスタンスは、**主張されたほどには路線を塞いでいない**かもしれない。⚠ **自動的には従わない** — (i) 論文の記述は逐語 "we failed to do this" であって「この点が唯一の障害だ」とは書いていない、(ii) 濃度限界の内側では報告点は真の局所最大 (下記 `cardinality-localmax-boundary`) ⟹ **路線が開きうるのは濃度非制約の空間に限る**。**最初の一手 = 診断であって証明ではない**: (7)–(10) が非矩形パターン `A B / C A` を排除するのはどの濃度領域か、を harness で走査する。証明に投資するのは診断が生き残ってから (§5-2 kill-first)。**L5 が入力を 1 本足した**: 我々の 2 補助変数の support function の最適点 90 点で **決定論性 90/90 / rectangular 89/90 / Markov 89/90**、しかも**破れる 1 点がそのまま M2 の反例で、その写像は §III-B の非矩形パターンと同型** ⟹ 「ギャップが立つ ⟺ 最適点が非 Markov ⟺ 非 rectangular」が完全一致した。**診断の主語をここへ寄せられる** — 濃度領域の走査に加えて「非矩形が残るチャネルはどれだけ稀か」を定量できる (L5 の走査では 3/10、`λ` の窓は幅 0.05 程度) | 上記の統計 (facts §L5 の 3 行目) |
| `markovity-via-dual-F` | G+E | `todo` | — | **`markovity-conjecture` の L5 の park から起票** (§5-9)。M2 が偽だったのは共通補助 `W` を落としたためなので、**Conjecture 2 は領域側 `h` ではなく双対側 `F` の言葉で扱う**。⚠ **`F` の逐語実装は L1 の [`bc-markovity-localmax-check.py`](bc-markovity-localmax-check.py) に既にある** (§III-B の目的値 4 つを 8 桁再現済) ⟹ 工事の実体は「我々の領域 `def` と `F` を繋ぐ段」であって `F` の実装ではない。**`support-vs-dual-additivity` (`{a_x}` ↔ `θ` の Legendre / 上凹包の段) と大きく重なる** — 先にそちらを済ませるのが安い。⟹ **軸 E と軸 G が 1 つの前提工事を共有する**ことが L5 の最大の産物 (親 plan 判断ログ 16) | — |
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
| `conditioning-collapse-schema` | A | **L3 の死因からの派生**。条件つき版と非条件版が同値になったのは more capable 固有の事情ではなく、`∀ p, F(p) ≤ G(p)` という**周辺分布で量化されたチャネル述語**一般に効く平均化の帰結かもしれない。そうならば degraded / less noisy でも同じ形で潰れ、`weakest-hyp-degraded-lessnoisy` は着手前に結末が読める。先にやるのは schema の書き下し — どの汎関数の組 `(F,G)` について「全周辺分布での不等式」と「全 `(pU,K)` での条件つき不等式」が同値になるか。**昇格条件**: schema に**境界**を付けること (同値にならない `(F,G)` の実例を 1 つ出す)。出れば `class-def-vs-consequence-gap` に主張 1 文と step 列が入り、軸 A の第一手が生きる場所が特定される | L4 |
| `region-convexity-transplant` | E+D | **類似問題からの移植**。領域の凸性を時分割で示す機構が**別家系に 2 系統ある** — MAC は `macConcatCode` (`MultipleAccess/TimeSharing.lean:163`) → `mac_timesharing_strict` (:369) → `mac_capacityRegion_convex` (:565)、WynerZiv は補助変数上の値集合について `wzRateValueSet_timeShare_mem` (`WynerZiv/FactorizableRate.lean:948`) / `mutualInfoPmf_mixture_affine` (:783) / `wzRateValueSet_avg_mem` (:1230) / `wynerZivRate_convex_in_D` (:1122)。一方 **BC 側には `Convex ℝ (bcCapacityRegion W)` も union の凸性も無い** (`rg 'Convex ℝ' InformationTheory/Shannon/BroadcastChannel/` のヒットは四辺形版 `martonRegion_convex` の 1 本のみ)。L2 の V5 が還元 (3) を**閉凸包の命題**と確定させた以上、「support function が領域を決める」という言明自体が両端の凸性に依存する。**昇格条件**: 時分割変数を補助アルファベットへ吸収する標準手が我々の `def` の上で step 列として書けること。書ければ (3) の主張が「閉凸包」から「領域そのもの」へ降り、V5 の測定の意味が 1 段強くなる | L4 |
| `entropic-vector-as-hierarchy-atom` | D | **同じく移植**。Li の `Δ^H_atom` は逐語 `aᵀh(X₁,…,X_n) ≥ 0` で `h` は entropic vector ([`bc-facts.md`](bc-facts.md) F7)。その entropic vector が**在庫にそのまま在る** — `jointEntropySubset` (`Shannon/Han/D.lean:36` = `S ↦ H(X_S)`) と `entropyPolymatroid` (`Shannon/Polymatroid.lean:281`、`@[entry_point]`、axiom 3 本 `jointEntropySubset_empty` / `_mono` / `_submodular` (:47 / :76 / :202) を `Combinatorics.Polymatroid` に束ねたもの)。⟹ `multiletter-subject` が要求する「Li の階層のレベルを我々の型で書く」は、少なくとも `Δ₀ᴴ` 層については**在庫の消費だけで書ける**。**昇格条件**: `Δ^H_atom` / `Δ₀ᴴ` を `entropyPolymatroid` 上の述語として 1 文で書き、Table I の `Σ₁ᴴ` (degraded BC) が我々の `bc_degraded_capacity_eq_uv` の形と照合できること | L4 |
| `uv-slack-step-enumeration` | B | **既存証明の読み直しから**。`dep_rank.sh` の実測で BC family の重い entry point は `bc_degraded_capacity_eq_uv` 2425 / `bc_moreCapable_capacity_eq_uv` 2402 / `bc_lessNoisy_capacity_eq_uv` 2373 / `bc_capacity_subset_uv` 1687 / `martonRegionUnion_subset_capacity` 1661 (推移依存数)。軸 B が列挙したい対象 = `bc_capacity_subset_uv` の前方閉包で、実測は**内部 266 decl / 外部 1412**、うち名前が不等号形のものは **21 本だけ**。緩みを入れる本体は `mutualInfo_le_of_markov` (DPI) / `mutualInfo_le_of_postprocess` / `condMutualInfo_le_of_markov_joint` / `condMutualInfo_le_add_condMutualInfo` / `mutualInfo_le_condMutualInfo_of_indep_markov` / `bcUVTimeShare_uvInfo₁_ge` / `bcUVTimeShare_uvInfoSum₁_ge` / `bcConverseFanoSlack₁_le` / `klDiv_map_le`。⟹ `outer-slack-vs-thm7` の「不等号ステップを全列挙」は散文の読解ではなく **`dep_graph.sh` + 名前フィルタで機械的に得られ、規模は 21 本**。**昇格条件**: 21 本それぞれに等号成立条件を書き、Gohari–Nair Theorem 7 の「捨てられる項」と対応が付くか / 付かないものが残るかを判定できること | L4 |
| `shannon-cone-lp` | C | **数値実験のパターンの空き口から**。`bc_probe.py` は情報量式を**同時エントロピー `h(S)` 上の有理係数ベクトル**として保持する (`LinInfo.terms`) が、その表現を使っているのは恒等式の係数相殺 `prove_identity` / `is_zero` **だけ**。不等式側は掃引 `test_relation` (証拠) しかなく、**証明側の口が空いている** — 同じベクトルに elemental Shannon 不等式を制約とした LP を当てれば「その不等式は Shannon 型か」を機械判定できる (ITIP 相当。`scipy.optimize.linprog` は既に依存)。軸 C にとっての意味は大きい: F4 の Jog–Nair 不等式は Shannon 型でないからこそ定理なので、**LP が通る候補はその場で既知として殺せる = §5-7 novelty gate の機械化**。**昇格条件**: LP が Jog–Nair 不等式に「Shannon 型でない」を返し (肯定コントロール = Shannon 型不等式が通ること)、その上で生き残る新候補が 1 本でも出ること | L4 |
| `product-outer-claim4` | E+B | **文献の未使用の道具から**。F5 / V10 の逐語 "In Section III we establish a new outer bound (Claim 4) for product broadcast channels and use it to determine the capacity region of some new classes (Theorems 2 and 3). This outer bound is strictly better than the UV outer bound as it is optimal for the example where the UV outer bound is loose." — **Claim 4 はどの attack にも使われていない**。我々は `bc_capacity_subset_uv` を `T^{⊗n}` に当てて `h_n` の上界を引けるが、それは UV 由来で緩いことが F5 で判明済。Claim 4 は**積 BC 専用でかつ UV より真に強い**外界なので、軸 E の自己テンソル化 (`h_n` の評価) と軸 B の「UV はどこで緩むか」の**両方に同時に効く唯一の未使用資産**。**昇格条件**: Claim 4 を逐語取得し、(i) 自己テンソル `T ⊗ T` に特化した形が書けるか、(ii) それが `h_2` に UV より真に良い上界を与えるか。与えるなら `selftensor-counterexample` のブロッキング前提 (`marton-3aux-probe`) を迂回する別ルートが立つ | L4 |

## 軸ごとの連続ゼロ進捗カウント (round-robin 判定用)

| 軸 | 連続ゼロ進捗 leg 数 | 判定 |
|---|---|---|
| A | 0 | L3 で第一手が `probe-failed`。**同値という確定事実 + 子 attack 2 本** (`weakest-hyp-degraded-lessnoisy` / `class-def-vs-consequence-gap`) が残るのでゼロ進捗ではない (親 plan §5-1) |
| B | 0 | L0 は軸に紐づかない文献 leg。**死亡も確定事実**なのでゼロ進捗ではない (親 plan §5-1) |
| C | 0 | **L0–L3 の 4 leg で一度も leg の主語になっていない** (下記 L4 の点検で唯一の該当軸)。カウントは 0 だが、それは「進んだ」ではなく「回ってきていない」 |
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
**数えるのは軸 E の側だけ**にする。**L3 も同じ**: 棚卸し手順の訂正 (`dep_graph.sh` + 辺の向き先の区別) は
他軸の最弱仮説抽出にも効くが、L3 は軸 A の leg なので**他軸のカウントは動かさない**。

### L4 の点検 — 強制 park 対象は無い。ただしカウンタは構造的に発火しえない

**park 対象**: **無い** (全軸 0、3 に達した軸はゼロ本)。park 済みの軸も無いので再開条件の点検も空。

**カウンタが実態を反映しているかの点検 — 反映していない**。免除規定 (L0 / L1 は軸に紐づかない
固定枠なので触れなかった軸のカウントを進めない) 自体は妥当で、これを外して「その leg で触れなかった
全軸のカウントを進める」に変えると、**回ってきていない軸まで park される** = round-robin の趣旨
(詰まった軸から強制的に離す) と逆向きになる。過剰なのは免除ではなく、**3 つの規約の合成**の側:

- 親 plan §5-1 (no empty leg) が**全 leg に確定事実 1 行を義務づける**
- 親 plan §6.1 が **1 leg = 1 attack の 1 ステップ**に粒度を固定する
- 上の二重計上の注意が、**leg の主語になった軸以外はカウントを動かさない**と定める

⟹ カウンタが増えるのは「その軸の leg なのに確定事実がゼロ」のときだけで、それは §5-1 違反。
**§5-1 を守る限りカウンタは 3 に到達できない** — L0–L3 で全軸 0 なのは順調さの表示ではなく、
**機構が一度も動きうる状態になっていないこと**の表示である。加えて軸 C のように「一度も回ってきて
いない」状態と「回したが進まなかった」状態が**同じ 0 で表示される**ため、区別も付かない。

**⚠ 規約の改定は提案までにとどめる** (本 leg では規約本文を書き換えない)。提案の中身は親 plan
§9 判断ログ 14 に 1 件として起票した — 要点は (i) §5-5 のカウンタを「詰まりの検出」専用と明記し、
(ii) 別に**枯渇カウンタ** (その軸が最後に leg の主語になってからの leg 数) を持ち、
(iii) 棚卸し leg で枯渇カウンタが閾値を超えた軸は**次の可変枠を割り当てるか、優先度を下げる理由を
書くかの二択を強制する**、の 3 点。判定は棚卸し leg にだけ発生するので運用コストは増えない。

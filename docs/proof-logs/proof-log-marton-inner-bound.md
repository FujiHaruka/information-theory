# Marton inner bound Lean 形式化 — ボトルネック分析

将来「in-project 資産の重複検出ツール」「対称鏡像の自動生成・検証ツール」を作るためのベースライン記録。

**定量データ**: [docs/metrics/marton-inner-bound.metrics.md](../metrics/marton-inner-bound.metrics.md)

参照: plan [`docs/shannon/marton-inner-bound-plan.md`](../shannon/marton-inner-bound-plan.md) /
在庫 [`docs/shannon/marton-inner-bound-inventory.md`](../shannon/marton-inner-bound-inventory.md)

---

## 0. 対象問題と成果物

一般 (non-degraded) broadcast channel に対する **Marton inner bound の achievability**
(El Gamal–Kim Thm 8.3 の `U = ∅` 版)。3 本の厳密不等式
`R₁ < I(V₁;Y₁)` / `R₂ < I(V₂;Y₂)` / `R₁+R₂ < I(V₁;Y₁)+I(V₂;Y₂)−I(V₁;V₂)`
を満たすレート対が達成可能であることを示す。Cover–Thomas の範囲外で、親 plan では
撤退ライン L-BC5 (Marton は完全 scope-out) が張られていた領域。

成果物 (すべて 0 error / 0 sorry / 0 `@residual`):

| ファイル | 行 | decl | 役割 |
|---|---|---|---|
| `Marton/MutualCovering.lean` | 730 | 51 | typicality を一切知らない抽象核 (二重添字指標和の second moment / Chebyshev) |
| `Marton/Basic.lean` | 79 | 3 | `InMartonRegion` + `exists_martonRateSplit` (Fourier–Motzkin) |
| `Marton/Setup.lean` | 329 | 22 | ambient 測度 + 座標補題 + `martonInfo₁/₂/V₁V₂` |
| `Marton/Covering.lean` | 1068 | 30 | mutual covering の typicality 具体化 (weak 版 4 本 + strong 版 4 本を並置) |
| `Marton/ErrorAnalysis.lean` | 1027 | 27 | 符号帳 / 選択規則 / 復号器 + `martonCodebookToCode` + 両受信機の Bonferroni |
| `Marton/MarkovCore/Prelim.lean` | 152 | 6 | 半径単調性など受信機非依存の部品 |
| `Marton/MarkovCore/Receiver1.lean` | 796 | 25 | 受信機 1 の条件付き AEP / 半径 / 帯定数 |
| `Marton/MarkovCore/Receiver2.lean` | 721 | 23 | 同 受信機 2 (鏡像) |
| `Marton/MarkovCore.lean` | 61 | — | 上 3 本の umbrella |
| `Marton/Achievability.lean` | 928 | 17 | 3 段アンサンブルの再結合 + ε 配分 + headline |
| `Shannon/ConditionalAEP.lean` | 267 | 5 | 型汎用の条件付き AEP (Marton 家系の外に切り出し) |

headline `marton_achievability` は `@[entry_point]` + `@audit:ok`、
`#print axioms` = `[propext, Classical.choice, Quot.sound]`。

---

## 1. 問題のキャラクター

支配項は **「Mathlib 補題探索」ではなく「in-project 資産の再利用可否判定」**だった。
Mathlib 壁は 0 件で確定しており (在庫 §8)、必要だった Mathlib 原子はすべて家系の
import 閉包に最初から入っていた。実際に時間を食ったのは次の 3 つ:

1. **既存の degraded BC 家系 (`BroadcastChannel/Achievability/`) のどこまで写経できるか**の判定
2. **受信機 1 → 受信機 2 の鏡像がどこで非対称になるか**の判定
3. **weak typicality の在庫では閉じない**と分かってからの層の切り分け

過去の proof-log との比較で言えば、`shannon-hartley-converse-final` 系が
「Mathlib のどこに何があるか」型だったのに対し、本件は
**「自分たちが 3 か月前に書いた資産のどこに何があるか」型**だった。
後者に効くツールは loogle ではない。

---

## 2. 数学的方針

### (1) 層を「抽象度」で切る

`MutualCovering.lean` (Phase 1/4) は typicality を一切知らない。
入力は「二重添字の指標和」だけで、結論は Chebyshev 型の確率上界。
covering 補題としての意味づけは `Covering.lean` (Phase 5) が与える。

この分離は結果的に一番効いた設計判断だった。後述の方針転換
(weak typicality → covering 集合のみ strong 化) が `MutualCovering.lean` を
**無改変**で通過し、書換が typicality 層に閉じたため。

### (2) 分散上界の鋭化 (Phase 4 の存在理由)

粗い分散上界では sum-rate 制約 `R₁+R₂ < I₁+I₂−I(V₁;V₂)` に届かない。
スライスごとの一様な条件付き上界を **両方向** 取って共分散を押さえる必要がある。
「片方向で足りる」という当初予測は反例で棄却した
(`α = {0}`, `β = {0,1}`, `μX = δ₀`, `μY(0) = ε`, `S = {(0,0)}` で共有組の共分散
`ε−ε²` が `q̄·p = ε²` を `ε = 0.1` で破る)。
これが `covariance_pairIndicator_shared_le` が仮説を 2 本取る理由。

### (3) covering 集合のみを strong typicality 化

「選択された `V₁ⁿ` に対して一様に E1」は一般アルファベットで**偽**で、
weak typicality の在庫だけでは E1 が閉じない
(補助 3 元・周辺 `(1/2,1/4,1/4)`・型 `(1/2,1/2,0)` が weak 典型なのに
出力側経験エントロピーが `H(Y₁)` から n 非依存の定数ずれを持つ。補助 2 元では
型が pin されて反例が消えるので、小さいケースだけ見ていると気づけない)。

covering 集合だけを strong 化し、weak 版 4 本は**削除せず並置**した。
strong ⊆ weak なので上界は含意され、帯定数 `C = 0` で weak 版に退化するのが
領域不変性の検算になる。

### (4) 半径は「パラメータ」ではなく「`ε` の計算項」

復号半径 `ε` ⊃ 送信対の pin `martonStrongRadius(₂) ε` ⊃ covering の pin
`martonCoveringRadius(₂) ε` という 3 本の入れ子。後 2 者を `ε` の**関数として定義**したので、
下流の署名が持つ半径は `ε` と `ε_cov` の 2 本だけで済み、
Phase 7 の ε 配分は入れ子 `min` 1 本 (`ε_cov := min (min (min …) …) …`) に収まった。

---

## 3. 補題探索の実録

### 3.1 Mathlib 側 (Phase 0 の在庫調査)

loogle を打ったのは在庫フェーズだけで、実装フェーズでは 1 回も要らなかった。

| 想定した補題 | loogle クエリ | 結果 | 対応 |
|---|---|---|---|
| Paley–Zygmund 不等式 | `"Paley"` | `Found 0 declarations` | **不要**と判明。Chebyshev で足りた |
| second moment method | `"second_moment"` | `Found 0 declarations` | 自前 (10–25 行) |
| `P(X = 0) ≤ Var/E²` | 第 1 段 `ProbabilityTheory.variance, \|- _ ≤ _` → 5 件を網羅列挙 / 第 2 段 (結論形) `\|- MeasureTheory.Measure.real _ _ ≤ ProbabilityTheory.variance _ _ / _` | 第 2 段は `Found 0` | `meas_ge_le_variance_div_sq` から 10 行 |
| covering lemma 一般形 | `"covering_lemma"` | `Found 0 declarations` | 自前 (家系ごと新規) |

4 件の 0-hit いずれについても「結論形が近い既存テンプレ補題」を名指しできていたので、
壁ではなく plumbing 側と判定した。この判定は最後まで覆らなかった (`@residual(wall:…)` 0 件)。

### 3.2 in-project 側 (Phase 7 の組み立て)

Phase 7 で「あるはず」と思って探し、無いと判断して自前構築したものが 3 件。
**うち 1 件は誤判定だった** (→ 4.2)。

| 必要だったもの | 実際のクエリ | 結果 | 対応 |
|---|---|---|---|
| singleton 質量の総和 = 1 (公開形) | `rg -n "lemma sum_measureReal_singleton\b\|theorem sum_measureReal_singleton\b" --glob '*.lean' InformationTheory/` → 次に `rg -n "sum_measureReal_singleton" --glob '*.lean' InformationTheory/ \| head -20` | 定義行を拾えず | `Achievability.lean:46` に private で再宣言。**誤判定** — 公開版が 2 本、import 閉包内に既存 |
| `martonSelectRow` の仕様補題 | `rg -n "martonSelectRow" ErrorAnalysis.lean` | 呼び出し 8 箇所のみ、仕様補題なし | `martonSelectRow_mem` を新規 (`Achievability.lean:222`)。**正しい判定** |
| `martonInputCodebookMeasure` の 1 メッセージ対での周辺化 | `rg -n "lemma sum_weighted_map\|theorem sum_weighted_map\|lemma measurePreserving_eval\|theorem measurePreserving_eval" -A 8 --glob '*.lean' InformationTheory/` | 素材はあるが周辺化の形は無し | `marton_inputTier_marginal` / `marton_subcodebook_row_marginal` を新規。**正しい判定** — 既存は `ErrorAnalysis.lean` の証明本体に `have step1 :` としてインラインで存在するだけだった (L689 / L937) |

---

## 4. 試行錯誤と後戻り

### 4.1 「対称だから共通のはず」が壊れ続けた

**症状**: 受信機 2 は受信機 1 の完全な鏡像 (Phase 6b) であるにもかかわらず、
plan の設計記述が 2 件破れた。しかも **どちらも「対称性の主張」**だった。

- 「covering 半径は受信機間で共通」→ **誤り**。実物は
  `martonCoveringRadius = martonStrongRadius ε / (4 * (Fintype.card (V₁ × V₂) + 1))` で
  strong 半径経由で帯定数に依存する。受信機 2 は独立に `martonCoveringRadius₂` が要り、
  両者を同時に満たすには `min` を取って `jointStronglyTypicalSet_mono_radius` で
  各受信機の半径へ開き直す段が必要になった。
- 「degraded BC 版の Bonferroni が入力になる」→ **誤り**。受信機 1 の Bonferroni は
  BC 版を一切呼ばず自己完結する。alias 和の索引形が `Fin M₂` 単独 vs `Fin M₂ × Fin M₂'` で
  異なるため。鏡像元は同一ファイル内の Marton 受信機 1 側 6 本だった。

同じ軸の 3 件目が §2(2) の「スライス上界は片方向で足りる」で、これも反例で棄却された。

**原因**: 対称性の主張は **型が通ってしまう**。帯定数は
`martonBandConst` (`(V₁,X)` 対) / `martonBandConst₂` (`(V₂,X)` 対) /
`martonCoveringBandConst` (`(V₁,V₂)` 対) の 3 種あり、取り違えても型検査は通り、
意味だけが壊れる。だから「対称だから同じはず」は**コンパイラに否定されない**種類の誤りになる。

**抜け方**: 実装で潰した後に plan を書き換える。

**教訓**: 予測の破れが対称性の主張に偏る以上、ツール側で
「plan が『共通』『流用可能』と書いた宣言について、実物の定義本体を diff する」
チェックが作れる。逆に**実装で潰した後の対称性の主張は信頼できる** —
Phase 7 では前回の同期で入れた訂正 (下記 4.1b) がそのまま当たった。

### 4.1b 逆側の観察: `MarkovCore` は意図的に非対称

`marton_condAEP_jointlyTypical_ge` と `marton_strongRadius_prob_tendsto_one` は
受信機 1 側にのみ存在する。下流が消費しないので鏡像を作らなかった判断は、
Phase 7 でも実際に不要と確定した。

機械確認 (`sig_view.ts --names` の出力から添字を除去して diff):

```
$ diff <(sig_view.ts --names …/Receiver1.lean | sed 's/₁//g') \
       <(sig_view.ts --names …/Receiver2.lean | sed 's/₂//g')
24,25d23
< theorem marton_strongRadius_prob_tendsto_one
< theorem marton_condAEP_jointlyTypical_ge
```

宣言リストが添字を除いて完全一致し、差分がこの 2 本ちょうどになる。
**「鏡像の網羅性」は機械判定できる** — これは 4.1 の対称性主張と違い、ツール化が容易な側。

### 4.2 in-project 資産の見落とし: 同一命題が repo に 7 本

**症状**: `∑ z : γ, μ.real {z} = 1` (probability measure の singleton 質量の総和) を
「公開形が無い」と判断して `Achievability.lean:46` に `private` で再宣言した。

**実物**: 同じ命題が **公開で 2 本**、しかも両方 `Achievability.lean` の import 閉包内に存在した。

- `InformationTheory/Shannon/ConditionalMethodOfTypes/Mass/Concentration.lean:388`
  — `sum_measureReal_singleton_eq_one`
- `InformationTheory/Shannon/ChannelCoding/Achievability/RandomCodebook.lean:38`
  — `sum_measureReal_singleton_univ_eq_one`

`import` 行を BFS した閉包は 135 モジュールで、上記 2 本はどちらもその中にある
(= import 追加すら不要だった)。Marton 家系自身も `ErrorAnalysis.lean:70` に
同じ private 版を持っている。

**当初「4 本」と数えたが、実物は 7 本だった** (`71965d3f` で
`Probability/SingletonMass.lean` へ統合)。名前検索を積み増しても 4 本より先に進めず、
**結論形での検索** (`rg -B4 '\.real \{.*\} = 1\s*(:=|$)'` を `lemma|theorem` 行で絞る) で
初めて残り 3 本が出た。うち `sum_prob_real_singleton_eq_one`
(`WynerZiv/Achievability/FailureTendstoZero.lean`) は**名前に `measureReal` を含まない**ため、
どんな名前ベースの検索でも原理的に出ない。**数え落とし自体が、最初の見落としと同じ機構
(名前で引いている) で起きた**。

**原因** (2 段階):

1. 第 1 クエリが `sum_measureReal_singleton\b` と **語境界 `\b` を付けた**。
   Mathlib の `sum_measureReal_singleton` を「同名で」探す意図だったが、
   `\b` は `_eq_one` / `_univ_eq_one` のような**接尾辞つきの派生名を構造的に排除する**。
   in-project のラッパは必ず接尾辞を持つので、この 1 文字で目的の資産だけが落ちる。
2. 第 2 クエリで `\b` を外したが `| head -20` を付けた。このパターンの in-project ヒットは
   **116 件**あり、大半が呼び出し側の `rw [...]`。`rg` は並列走査で出力順が安定しないため、
   定義行 2 本が先頭 20 行に入る保証がない。実際、当該サブエージェントの transcript 全体で
   `sum_measureReal_singleton_eq_one` / `sum_measureReal_singleton_univ_eq_one` は
   **1 回も出現しない**。

**抜け方**: Phase 7 は private 再宣言のまま closure し (honesty 上の欠陥ではないので closure は
妨げない)、Phase 8 の follow-up で 7 本を `Probability/SingletonMass.lean` の 1 本へ統合した
(`71965d3f`)。宣言レベルの重複は解消したが、証明内 `have` での再導出は ~20 箇所残っている。

**教訓**: 4 つ、いずれもツール仕様に落とせる。

- **`\b` は in-project 検索では有害**。Mathlib 名を探すときの癖がそのまま出ると、
  自分たちのラッパ (必ず接尾辞つき) だけが落ちる。「定義を探す」検索は
  `^(private )?(lemma|theorem) <prefix>` のように**行頭アンカー + 接尾辞ワイルドカード**にすべき。
- **`| head -N` は「無い」の証拠にならない**。件数が N を超えた時点で
  「上位 N 件に無かった」しか言えないのに、判断は「無い」に流れる。
  ヒット数が N を超えたときに警告を出すだけで防げる。
- **名前ベースの検索は改良しても天井がある**。接頭辞を変えても `\b` を外しても、
  命名規則を共有しない 3 本目以降は出ない。**結論形で引く**のが唯一の網羅手段。
- **命題単位の重複検出**が本命。名前ではなく**型 (`∑ z : γ, μ.real {z} = 1`) で
  in-project を引く**手段があれば、この 7 重複はすべて 1 クエリで見える。
  loogle は Mathlib しか見ないのでここを埋めない。
  この教訓は `CLAUDE.md`「In-repo asset search」に規則として落とした。

### 4.3 再利用の境界が予測とずれた

**症状**: degraded BC 家系からの写経可否が、起票時の予測と両方向にずれた。

| 宣言 | plan の入力リスト | 実際 |
|---|---|---|
| `bc_two_tier_pigeonhole` | 載っていた | **逐語再利用できた** (`κU := κ₁ × κ₂` に束ねて 3 段を 2 段へ再結合) |
| `bc_weighted_two_tier_{mono,add,const_mul,sum_index}` | 載っていない | **逐語再利用できた** |
| `bc_Ec_lt_of_rate` | 載っていない | **逐語再利用できた** (Marton の alias 末尾項そのもの。両受信機に `(R₁ := R'ᵢ) (R₂ := Rᵢ)` で当たる)。自己実装 1 本の節約 |
| `bc_pair_aggregate₁/₂` | 載っていた | **再利用不可**。`hE0 : ∀ m, ∑ … = A` を**等式**で固定しているが Marton は `≤ A` が要り、alias 索引形も違う |

**原因**: plan は「degraded BC の achievability」というレベルで再利用可否を見積もっていたが、
実際の境界はそこではなかった。

**抜け方**: `marton_two_tier_aggregate` / `marton_three_tier_aggregate` を
`Achievability.lean` に private で建て直した (中身は上の generic 4 本)。

**教訓**: 再利用可否の実際の境界は
**「generic な畳み込み補題か、索引形を固定した集約補題か」**。
前者は写経でき、後者はできない。次に BC 家系から写経したくなったら、
この軸で仕分けてから該当宣言を Read すればよい。
ツール的には「仮説が等式で pin されているか不等式か」は署名から機械判定できる。

### 4.4 3 段アンサンブルへの述べ直し (唯一の設計の後戻り)

**症状**: `marton_random_codebook_average₁/₂_le` と `marton_exists_codebook_le_avg` を、
最初 `bc_two_tier_pigeonhole` の形に合わせて `κ₁ × κ₂` を束ねた**積形**で述べた。
すると既存 `ErrorAnalysis` のアンサンブル補題がそのままでは当たらない。

**原因**: 「下流 (pigeonhole) の形に合わせる」を優先して、
「上流 (アンサンブル補題) が返す形」を見ていなかった。
CLAUDE.md の「Mathlib-shape-driven Definitions」を in-project 資産に対して適用し損ねた形。

**抜け方**: 3 段形に述べ直し、積形への再結合を 2 本の generic ラッパ
(`sum_prodTier_eq` / `marton_three_tier_aggregate`) に押し下げた。

**教訓**: 「上流の結論形 / 下流の仮説形」が食い違うとき、
**述べ直すべきは上流に合わせる側**で、変換は generic ラッパに閉じ込める。
この後戻りは 1 件だけで済んでおり、他の Phase では層の切り分け (§2(1)) が効いていた。

### 4.5 elaboration の事故 2 件 (Phase 7)

いずれも数学ではなく Lean のエラボレーションの問題。

**(i) `Decidable` インスタンス不一致**

`if … then 1 else 0` を書いたところ、ゴールに `Set.decidableSetOf (r₁, r₂) fun c => …` が現れ、
`martonSelectRow` の定義が使っている `Classical.propDecidable` と一致しなくなった。
`sum_pair_le_add_prodReal` を `Set.indicator` に切り替えて解消
(`Achievability.lean` L368/376/509/517)。

**教訓**: 決定不能な述語に対する指示関数は、最初から `Set.indicator` で書けば
インスタンス一致の問題が起きない。`if … then 1 else 0` は書ける形なので誘惑されるが、
`Decidable` インスタンスが署名に漏れる。

**(ii) `whnf` タイムアウト**

`exact marton_three_tier_aggregate …` の最初の呼び出しで

```
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

暗黙引数 `A` / `e` / `k` / `Minv` を名前付きで渡す
(`(A := tol + η) (e := Real.exp …) (k := …) (Minv := …)`) と ~5 秒に低下した。

**教訓**: 引数が 20 本を超える集約補題では、暗黙引数の統一が
探索空間の爆発を起こす。**タイムアウトは「証明が難しい」ではなく
「名前付き引数を書いていない」のサインでありうる**。
エラーメッセージからはこれが読み取れないので、
`whnf` タイムアウト時に「未指定の暗黙引数を列挙する」診断があれば直結する。

---

## 5. ボトルネックではなかったもの

- **Mathlib 探索**。実装フェーズでは loogle を 1 回も打っていない。
  使った Mathlib 原子はすべて家系の import 閉包に最初から入っていた。
  在庫フェーズの 4 件の 0-hit も、すべて「近接テンプレ補題を名指しできる自前構築」に落ちた。
- **Mathlib 壁**。`@residual(wall:…)` は最後まで 0 件。
  撤退ライン L-MT6 も不発動。
- **数学のアイデア**。教科書 (El Gamal–Kim Thm 8.3) の証明構造をそのまま追えた。
  時間を食ったのは「その構造を既存資産にどう載せるか」であって、証明の筋ではない。
- **honesty**。load-bearing hypothesis の誘惑が出る場面
  (weak typicality で E1 が閉じないと分かった時点) はあったが、
  方針 B (covering 集合のみ strong 化) が通ったので `sorry` を 1 本も残していない。
  頑健性仮説 `hpV` / `hK` / `hW` は full-support の前提条件で、証明の核を担っていない。
- **ファイル分割**。`MarkovCore.lean` が 1500 行を超えたが、
  受信機 1 / 受信機 2 / 共通の 3 分割が自明だったので機械的に済んだ。

---

## 6. 計測の罠

proof-log を書く側が踏んだ罠を 2 件。どちらも**測定手段そのものの欠陥**。

### 6.1 macOS の `awk length()` はバイト数を数える

行長 100 のスタイルゲートを `awk 'length($0)>100'` で回すと、
Unicode の密なこのファミリでは**偽陽性が大量に出る**。

| 対象 | `awk` (バイト) | code point |
|---|---|---|
| `Marton/Achievability.lean` | 102 行 | **0 行** |
| `Marton/ErrorAnalysis.lean` | 72 行 | **0 行** |
| Marton 家系 全 10 ファイル | 375 行 | **0 行** |

添字 (`₁` `₂`)・矢印 (`↦` `⟹`)・集合記号がすべて 3 バイトなので、
Lean の数式行はバイト長が code point 長の 2〜3 倍になる。
**行長ゲートを回す者は `awk` を使ってはいけない**。

### 6.2 最初に出した metrics はサブエージェントの作業を 1 件も見ていなかった (修正済)

**症状**: 生成された metrics が `対象ファイル Edit 回数 = 0` / `サブエージェント側 entries = 0` を
出した。実装は全部オーケストレーターが `Agent` で dispatch したので、
親セッションの JSONL には `.lean` の Edit が 1 件も無い。

**原因**: スクリプトが親 JSONL の `d.isSidechain` だけを見ていたが、現行のハーネスは
サブエージェントの transcript を `<session-id>/subagents/*.jsonl` という**別ディレクトリ**に置く。

**修正** (`ec955da1`): `subagents/*.jsonl` を走査対象に追加し、
`オーケストレーター / サブエージェント / 合計` の 3 列で出すようにした。
`--no-subagents` で旧挙動 (親のみ) も再現できる。同一セッション群の再計測値:

| 項目 | オーケストレーターのみ (`--no-subagents`) | 合計 |
|---|---|---|
| 対象ファイル Edit 回数 | 0 | **314** |
| `Edit` ツールコール | 18 | **364** (うちサブエージェント 346) |
| Active time | 4h 21m | **9h 13m** |
| LLM ターン数 | 264 | **1822** |

**残る教訓**: 数値そのものではなく、**オーケストレーター型の leg では計測手段が実装コストを
構造的に過少報告する**という性質のほう。親 transcript にはツールコールの内訳として
`Agent` しか残らないので、「何をどれだけ書いたか」は原理的に親からは見えない。
新しいツールで工数を測るときは、まず**測定対象が実際の作業者と一致しているか**を確認する。
最新の実測値は [`../metrics/marton-inner-bound.metrics.md`](../metrics/marton-inner-bound.metrics.md)
（本文にキャッシュしない）。

---

## 7. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **in-project の命題単位重複検出** (名前ではなく型で引く)。loogle の in-project 版 | 4.2 の 7 重複。「無い」の誤判定 1 件と、それが生んだ private 再宣言。**未実装** — 暫定の運用規則は `CLAUDE.md`「In-repo asset search」 |
| ✅ | ~~**`session_metrics.ts` の `subagents/` 対応**~~ → `ec955da1` で実装 (6.2) | オーケストレーター作業の計測が実装コストと誤読される問題は解消 |
| 中 | **検索の「無い」判定の健全性チェック** — `\b` 付き検索の警告 / `\| head -N` でヒット数が N を超えたときの警告 | 4.2 の 2 段階の失敗はどちらもこれで止まる |
| 中 | **plan の対称性主張の実物 diff** — plan が「共通」「流用可能」と書いた宣言の定義本体を突き合わせる | 4.1 の 2 件 + §2(2) の 1 件 |
| 中 | **鏡像網羅性の機械判定** — 添字を除去した宣言リストの diff (4.1b の手法をスクリプト化) | 鏡像 leg のレビューが目視から機械確認になる |
| 中 | **行長ゲートの code point 化** (`awk` の禁止) | 6.1 の 375 件の偽陽性 |
| 低 | **`whnf` タイムアウト時の未指定暗黙引数の列挙** | 4.5(ii) |
| 低 | 署名からの「等式で pin された仮説」検出 (再利用可否の事前判定) | 4.3 の `bc_pair_aggregate₁/₂` |

---

## 8. 補足

### 抽象化の利得は 1 leg 遅れて現れる

Phase 6a' で `MarkovCore` (と `Shannon/ConditionalAEP.lean`) を建てたコストは、
6a' 単体では割に合わなかった。回収されたのは 6b で、
受信機 2 の鏡像がほぼ写経で済んだことによる。

ただし「写経で済んだ」は**行数が少ないという意味ではない**。
6b の実装は約 1070 行で、起票時の見積 350–500 行の 2 倍超だった。
**1 行あたりの思考コストは下がったが、総量は下がっていない**。
抽象化の効果を「行数」で見積もると外す。

### 重複の後始末 (Phase 8 で消化)

- Wyner–Ziv `WynerZiv/Achievability/Concentration.lean` の `private` 3 本を
  `Shannon/ConditionalAEP.lean` の public 版へ再配線 (`34c2aaf0`、−170 行)。
  比較の決め手は `#check` の**展開後の署名**だった: `variable` ブロックから流れ込む
  `[Fintype T] [DecidableEq T]` は宣言行に現れないので、`rg` で行を並べても
  どちらが強い形か判定できない。
- 4.2 の質量和 7 重複を `Probability/SingletonMass.lean` へ統合 (`71965d3f`)。
  証明内 `have` での再導出 ~20 箇所は未処理。
- `stronglyTypicalSet_mono_radius` / `jointStronglyTypicalSet_mono_radius` は
  完全に generic で Marton 固有要素が無く、本来 `Shannon/StrongTypicality.lean` に属する (未移動)。

いずれも headline には影響しない。

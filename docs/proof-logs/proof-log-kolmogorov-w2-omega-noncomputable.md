# Chaitin Ω の非計算性 Lean 形式化 — ボトルネック分析

将来「計算可能性 (`Primrec` / `Computable` / `Partrec`) を扱う証明の部品探索と、在庫エージェントの署名検証」を自動化するためのベースライン記録。

**定量データ**: [docs/metrics/kolmogorov-w2-omega-noncomputable.metrics.md](../metrics/kolmogorov-w2-omega-noncomputable.metrics.md)

⚠️ **この metrics は実作業量を表さない**。Lean の編集は全て subagent (lean-implementer 4 体ほか) に dispatch したが、sidechain entries は 0 と記録された = 親セッションの JSONL に subagent のツール呼び出しが残っていない。数字はオーケストレーション分のみ。これ自体が計測基盤の穴として §6 に挙げる。

## 0. 対象問題と成果物

自己限定万能機械 `prefixUniversalEval` の停止確率 Ω が計算可能でないことを形式化する。第 2 波 (prefix 塔) が「後継 scope」として park していた 2 件のうちの 1 件で、着手時点ではコード側に対応する `sorry` を持たない (命題自体をまだ述べていない) 状態だった。

成果物:

- `InformationTheory/Shannon/Kolmogorov/PrefixComputability.lean` — 85 行 / 4 decl
- `InformationTheory/Shannon/Kolmogorov/OmegaNoncomputable.lean` — 598 行 / 52 decl
- `InformationTheory/Shannon/Kolmogorov/SufficientStatistic.lean` — `payloadDispatch_primrec` 新設 (既存 `payloadDispatch_computable` は署名不変で `.to_comp` の 1 行に)
- headline `chaitinOmega_not_computable : ¬ IsComputableENNReal chaitinOmega` (`@[entry_point]`、**仮説ゼロ**)
- 再検証: `rg 'sorry|@residual' InformationTheory/Shannon/Kolmogorov/` → 0、`#print axioms` → `[propext, Classical.choice, Quot.sound]`、独立 honesty 監査 + style ゲートとも PASS (`@audit:ok` 4 件)

## 1. 問題のキャラクター

支配項は **計算可能性の配線**であって解析でも数え上げでもなかった。Chaitin 論法そのもの (下からの近似 → 精度の有理近似 → 探索 → 長さ ≤ n の停止確定 → 停止問題と矛盾) は教科書どおりで、設計の後戻りは 1 度も起きていない。代わりに時間を取ったのは「その論法の各ステップを `Primrec` / `Computable` / `Partrec` の合成として書けるか」であり、そこで Mathlib の計算可能性階層が **ℕ-codable な構造で止まっていて算術 API を持たない**という壁に当たった (§3)。

第 2 波の兄弟 Phase との比較:

| Phase | 支配項 | 壁の型 |
|---|---|---|
| P8 factor-2 Levin | 機械の構造恒等式 + 数え上げ | 定義の選択 (加法版は真偽不明) |
| P10 十分統計量 | bit codec の `Primrec` 化 + 自己シミュレーション | 選択 (係数 4 を定義側へ) |
| **本 scope** | **計算可能性の配線 + 述語の強度設計** | **`ℚ`/`ℤ` の `Primrec` API 全欠 (定義形を強制)** |

## 2. 数学的方針

**(1) 下からの近似**: 時刻 `t` までに停止した長さ `≤ t` のプログラムの質量 `Ω_t` を、ビット列の有限列挙 + 有界評価 `prefixEvaln` で定義する。`Ω_t` は単調で `⨆ t, Ω_t = Ω`。

**(2) 精度からの探索**: Ω が「計算可能な二進有理近似列を持つ」なら、`Ω - Ω_t` が `2^{-n}` を切る `t` を `Nat.find` で探索でき、その探索自体が計算可能。

**(3) 質量超過による停止確定**: その `t` 以降に長さ `≤ n` の未停止プログラムが停止すると、質量が `2^{-n}` 以上増えて Ω の上限を破る。⟹ 長さ `≤ n` の停止性が決定でき、gateway atom で入れた `prefixUniversalEval_dom_not_computablePred` と矛盾。

気づきの時間的構造としては、**論法側には気づきが要らなかった** (教科書どおり) 一方、**定義形の選択に全ての難所が移動した**のが本 scope の特徴である。特に「精度添字をプログラム長に一致させる」という 1 つの選択が、事前に予期していた「指数について冪が単調」のステップを丸ごと消した。

## 3. Mathlib 補題探索の実録

**「Mathlib に存在しなかった」もの** (本 scope の一次データ):

- **`ℚ` / `ℤ` の `Primrec` 算術一式** — loogle `Primrec, Rat` → `Found 0 declarations mentioning Rat and Primrec.`、`Primrec, Int` も 0。`rg 'ℚ|Rat\.' Mathlib/Computability/` → 0 hit (ℤ は 3 ファイルに出るが `Primrec` を 1 度も含まない)。**これが定義形を強制した**: 近似列を ℚ でも ℤ でもなく **ℕ 分子の二進有理数**で建てるほかなく、分母は `2^t` 側に固定した。Mathlib の計算可能性階層は ℕ-codable 構造で止まっており、その上に算術 API が無い。
- **`Primrec (List.sum : List ℕ → ℕ)`** — loogle `Primrec, List.sum` → `Found 0`。在庫は template (`Primrec.list_foldl`) を正しく名指ししていたが、`.sum` への橋自体が自作である点を落としていた。自作 7 行。
- **`Primrec.list_replicate`** — loogle `Primrec List.replicate` → `Found 0`、`rg replicate Mathlib/Computability/Primrec*` も 0 hit。`Primrec.nat_iterate` (`Primrec/Basic.lean:539`) + `List.replicate n a = (a :: ·)^[n] []` で自作 8 行。
- **`ENNReal.two_ne_top`** — 識別子として存在しない (unknown constant)。`(by simp)` で潰す。
- **`Finset`-of-subtype transport** — 停止プログラムの subtype 上の `Finset` と `List Bool` 上の `Finset` を往復する補題は両方向とも不在。`attach` + `image` + `InjOn` で自作 (`sum_le_chaitinOmega` / `exists_sum_le_omegaApprox`)。

**存在したが在庫の記録どおりには使えなかったもの** (§4.1):

- `Primrec.listFilter` (`Mathlib/Computability/Primrec/List.lean:260`) — `variable {p : α → Prop} [DecidablePred p]` により述語がパラメータ非依存。`t` に依存する述語 (`fun p ↦ (prefixEvaln t p).isSome`) には使えず、汎用版を自作 10 行。

**逆に予想外に良かったもの**:

- `evaln` 群 (`Mathlib/Computability/PartrecCode.lean`) は **型クラス前提を 1 つも持たない**。`primrec_evaln` (`:922`) も実在し、有界評価の `Primrec` 性が既製品で手に入った。
- `ENNReal.lt_add_of_sub_lt_right` (`Mathlib/Data/ENNReal/Operations.lean:367`) — 在庫が挙げていた `ENNReal.sub_lt_iff_lt_right` は `b ≤ a` の side condition で三分岐を強いるが、こちらは仮説 `a ≠ ∞ ∨ c ≠ ∞` だけで 1 行に潰れる。

## 4. 試行錯誤と後戻り

### 4.1 在庫の ✅ が使用サイトで使えない (`Primrec.listFilter`)

**状況**: 在庫が「存在する ✅」と記録した `Primrec.listFilter` を、`t` 依存の述語でフィルタするのに使おうとした。

**原因**: 在庫は補題の**存在**を確認したが、`variable` 宣言による**述語のパラメータ非依存性**を確認していなかった。署名を verbatim で写していれば `variable {p : α → Prop}` が見えたはずだが、表には「✅ 存在」とだけ記録されていた。

**抜け方**: 汎用版 `primrec_list_filter` を `Primrec.listFilterMap` + `Primrec.cond` から自作 (10 行)。

**教訓**: CLAUDE.md の Subagent-Inventory 規約 (「`[...]` の型クラス前提を verbatim で、省略も言い換えもさせない」) は `variable` 由来の束縛にも及ぶ。在庫ツールを作るなら、**補題の存在ではなく「使用サイトの引数構造に適合するか」を出力単位にする**べきである。同じ形の取りこぼしが本 scope で 3 件 (`listFilter` / `List.sum` / `two_ne_top`) 起きた。

### 4.2 `rg` 0-hit を「不在」と読んだ (Lean core の補題)

**状況**: `Option.bind` の membership 補題を探して `rg -n 'mem_bind|bind_eq_some' Mathlib/Data/Option/*.lean` → 0 hit。

**原因**: 当該補題 `Option.mem_bind_iff` は **Mathlib ではなく Lean core** (`Init/Data/Option/Lemmas.lean:219`) にある。Mathlib パッケージ配下だけを `rg` すると core の資産が落ちる。

**抜け方**: loogle (`"_ ∈ Option.bind _ _"`) が正しく 1 件で返した。

**教訓**: CLAUDE.md の `cause:loogle-blind` (「loogle は Mathlib しか見ないので in-project を `rg` せよ」) の**鏡像**が存在する — `rg` は Mathlib しか見ないので core を落とす。不在判定には loogle と core を含む検索の**両方**が要る。片側 0-hit は必要条件ですらない。

### 4.3 `PrimrecRel` / `PrimrecPred` が存在型である

**状況**: `Primrec₂.to_comp Primrec.nat_le` の形で述語の計算可能性を作ろうとした。

**原因**: `PrimrecPred p` は `∃ (_ : DecidablePred p), Primrec fun a => decide (p a)` という**存在型**であって `Primrec₂` ではない。エラーメッセージ (「has type `PrimrecRel …` but is expected to have type `Primrec₂ …`」) は transparency の問題に見えるが、実際は型不一致。2 回の後戻り。

**抜け方**: `ComputablePred.computable_iff` の往復 — `∃ f : α → Bool, Computable f ∧ p = fun a => (f a : Prop)` の形で Bool 関数を取り出し、合成して戻す。この定石は `Decidable` インスタンスの不一致を丸ごと回避するので、後の N5 headline でも組み立てを 11 行に縮めた。

**教訓**: 「`X` は `Y` の別名だろう」と読ませる命名 (`PrimrecPred` / `Primrec₂`) で、片方だけが存在型のとき、型エラーは意味論の問題として表示されない。**定義本体を `#print` させる**のが最短の抜け方だった。

### 4.4 truncated subtraction が side goal を量産する

**状況**: `natCast_mul_inv_pow_eq` を切り捨て減算 (`m - ℓ`) で述べたところ、使用サイトごとに `omega` の side goal が生えた。

**抜け方**: `ℓ + d = m` を仮説に取る**加法分割**へ述べ直し、side goal が全消滅。同様に探索述語の共通分母を `max (n+2) t` ではなく `n + 2 + t` にすることで、3 箇所の切り捨て減算が消えた。

**教訓**: `ℝ≥0∞` / ℕ の切り捨て減算は「定義の強度」ではなく「証明の摩擦」として現れる。plan 段で「加法形、切り捨て減算なし」を原則として書いておいたことが、下位の補題設計でも効いた (原則が 1 段下へ伝播した)。

### 4.5 未検証の否定主張が plan から docstring へ伝播した

**状況**: 「標準の計算可能実数 (計算可能な有理 Cauchy 列) は `ℚ` の `Primrec` 不在ゆえ **Lean で述べることすらできない**」と plan に書き、実装がそれを docstring に転記した。

**原因**: 「証明できない」と「述べられない」を切り分けなかった。実際には `Denumerable ℚ` (`Mathlib/Data/Rat/Denumerable.lean:30`) + `Primcodable.ofDenumerable` (`Mathlib/Computability/Primrec/Basic.lean:139`) があるので、標準述語は **import 1 行で elaborate する**。塞がっているのは含意の証明 (丸めに計算可能除算が要る) だけだった。

**抜け方**: 独立 honesty 監査がコンパイラで反証。plan / module docstring / headline docstring / 定義 2 本の docstring / Main definitions の計 5 箇所を訂正。

**教訓**: CLAUDE.md が繰り返し警告している「見つけた資産に対する未検証の否定主張」がまた出た。今回の再発形は **`ℚ` が Mathlib に無いのではなく `ℚ` の `Primrec` 算術が無い**という、対象の粒度のずれである。ツール側の対策は明快で、**否定的主張を含む文を書いたら、その否定を反証する最小の Lean スニペットを 1 本書かせて `lake env lean` に通す**こと。今回それは 4 行で済んだ。

## 5. ボトルネックではなかったもの

- **数学的アイデア** — Chaitin 論法は教科書どおりで、設計の後戻りゼロ。5 つの Phase のうち 3 つ (N0 / N5 / gateway atom) は詰まり 0 turn で、提出した `sorry` が 1 回目の `lake env lean` で全て緑になった。
- **数え上げ / Kraft** — 事前には `tsum_inv_two_pow_length_le_one` や `chaitinOmega_le_one` を消費する想定だったが、N3 で入れた `sum_le_chaitinOmega` (停止プログラムの任意の有限集合の質量が Ω 以下) がそれらを包含したため、質量超過補題は 16 行で済み Kraft を一度も触っていない。
- **撤退ライン** — 4 段 (R-ONC0〜3) 用意して**全て未発動**。退避出口 `sorry + @residual` は一度も使わなかった。
- **ripple** — `payloadDispatch` の本体移設は署名不変で consumer 1 decl のみ。`chaitinOmega` の consumer も 3 decl / 1 file (`dep_consumers.sh` 実測) で、機械 (`prefixUniversalEval`、21 decl / 3 file) を触る場合との差が 1 桁。**Ω 側から攻めた**のが安上がりだった。
- **見積の精度は着地を予言しない** — 配線系は過大見積 (在庫 #2 が実測の 2.5 倍)、逆に N4 は過小 (`searchPred_computablePred` が 23 行 vs 予想 ~8)。合計は 601 行で見積 460–705 の範囲内に収まったが、内訳は当たっていない。

## 6. ツール開発への示唆

| 優先度 | 機能 | 節約できたであろうコスト |
|---|---|---|
| 高 | **在庫の出力単位を「補題の存在」から「使用サイトへの適合」へ** — `variable` 由来の束縛と型クラス前提を含む署名を機械抽出し、想定する適用先の型と照合する | §4.1 系の取りこぼし 3 件。1 件あたり 7〜10 行の自作 + 発見までの往復 |
| 高 | **否定的主張の自動反証** — 「〜は書けない / 存在しない」を含む文を plan / docstring に書いたら、反証を試みる最小スニペットを生成して `lake env lean` に通す | §4.5。plan → docstring への伝播 5 箇所、監査 1 往復 |
| 中 | **core を含む横断検索** — loogle (Mathlib のみ) と `rg` (Mathlib 配下のみ) の**両方の盲点**を埋める、Lean core + Mathlib + in-project を一度に引く検索 | §4.2。片側 0-hit を「不在」と読む事故 |
| 中 | **subagent の作業を計測できるようにする** — 現行 `session_metrics.ts` は sidechain entries を 0 と記録し、dispatch 主体の作業では定量データが取れない | この proof-log の定量部分そのもの |
| 低 | 存在型として定義された述語 (`PrimrecPred` / `PrimrecRel`) を型エラー時に自動 `#print` する | §4.3 の後戻り 2 回 |

## 7. 補足

**実際に打った loogle クエリ** (再現性のため、いずれも `--read-index` 経由):

```
Primrec, Rat            → Found 0 declarations mentioning Rat and Primrec.
Primrec, Int            → Found 0
Primrec, List.sum       → Found 0
Primrec List.replicate  → Found 0
Computable, Real        → Found 0   (前 leg から引き継いだ claim の再確認)
ComputableReal          → unknown identifier
_ ∈ Option.bind _ _     → Option.mem_bind_iff (core 由来、rg では 0 hit だった)
```

**採らなかった代替案**: 候補定式化として (i) 計算可能実数の自前定義、(ii) 機械の停止問題の決定不能性、(iii) 子 plan へ切り出し、の 3 案があった。(ii) は gateway atom として**実際に入れた** (`prefixUniversalEval_dom_not_computablePred`) が、それは Ω ではなく機械についての命題なので、headline には据えなかった (別 object を同じ名前で呼ばない)。着地した headline は (i) 側の述語 `IsComputableENNReal` の否定である。

**強度に関する開示**: 採用した述語は加法形 (弱い述語) で、その否定は床形の否定を含意する (`isComputableENNReal_of_floor` が機械検証)。標準の計算可能実数からの含意方向は `ℚ` の計算可能算術が無いため形式化できず、paper-level に留まる — この差分は module docstring と README の note に明記した。

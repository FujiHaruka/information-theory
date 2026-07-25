# Ch.14 Phase P10 — Kolmogorov 十分統計量 / MDL Lean 形式化 — ボトルネック分析

将来「在庫→実装の受け渡しを機械化するツール」および「computability 証明の自動組み立て支援」を作るためのベースライン記録。

**定量データ**: [docs/metrics/kolmogorov-w2-p10-kss.metrics.md](../metrics/kolmogorov-w2-p10-kss.metrics.md)

対象コミット: `1c965555` (在庫) / `ffefd9d8` (実装) / `ec2f6eba` (完成) / `56d6a773` (追補) / `d6cc3062` (style ゲート)。
親計画: [docs/kolmogorov/kolmogorov-w2-moonshot-plan.md](../kolmogorov/kolmogorov-w2-moonshot-plan.md) §Phase P10。
在庫: [docs/kolmogorov/kolmogorov-w2-p10-inventory.md](../kolmogorov/kolmogorov-w2-p10-inventory.md)。

---

## 0. 対象問題と成果物

Cover-Thomas §14.12（Kolmogorov 十分統計量 / 最小記述長）。有限モデル `S ∋ x` による二部記述
「モデル本体 + `S` の中での `x` の index」を定式化し、二部記述が prefix 複雑さを抑えることを示す。

成果物:

- `InformationTheory/Shannon/Kolmogorov/SufficientStatistic.lean` — 594 行 / 56 decl、0 sorry / 0 `@residual`
  - **定義 6 本**: `modelCode` / `modelComplexity` / `twoPartLength` / `mdlComplexity` / `structureFunction`（ℕ∞ 値）/ `IsSufficientStatistic`
  - **headline 2 本**（`@[entry_point]`）: `prefixComplexity_le_twoPartLength` / `mdlComplexity_sub_prefixComplexity_le`
  - **bit codec の `Primrec` 化 16 本**（`:154`–`:319`）+ **decoder の `Partrec` 化 4 本**（`:340`–`:388`）
    + **自己シミュレーション 15 本**（`:392`–`:513`）
  - crux `payloadComplexity_two_part_le`（機械が自分自身の payload decoder を走らせる）
- 全 decl が `#print axioms` で標準 3 公理のみ

**教科書との差（意図的）**: 教科書の `K(x) ≤ K(S) + log|S| + O(1)` は index 項の係数が 1 だが、
この機械では係数 1 は**偽**。取れるのは係数 4。これを定義 `twoPartLength` の側に埋め込んだ（§2 / §4.4）。

---

## 1. 問題のキャラクター

**支配項は 2 つ。定義形の決定（在庫段で完了済み）と、computability infra の手組み（実装段の重量物）。**
解析的な壁はゼロで、在庫の「genuine な `wall:` は 0 件」判定は実測で追認された。

行数の内訳が問題のキャラクターをそのまま表している:

| 部分 | 見積 | 実測 |
|---|---|---|
| §14.12 の定義群 + 構造的定理 | 約 120 行 | ほぼ見積どおり（在庫段で machine 検証済み、§4.1） |
| bit codec の `Primrec` 化 + 自己シミュレーション crux | 150–290 行 | 360 行（`SufficientStatistic.lean:154`–`:513`、上限超過） |
| ファイル全体 | 250–500 行 | 594 行（上振れ） |

つまり **上振れは全部 crux 側**で、定義量は読み違えていない。
P8 が下振れ（[proof-log-kolmogorov-w2-p8-levin.md](proof-log-kolmogorov-w2-p8-levin.md) §1）だったのと合わせて、
**行数見積は着地の可否を予言しない**という同じ結論になる。

---

## 2. 数学的方針

### 係数会計 — どこで 2 倍を被るかを先に決める

この機械では `prefixComplexity = 2 * payloadComplexity + 1` が恒等式（P8 の着地物）。
したがって「payload 世界で述べれば加法的、`K` 世界へ上げると 2 倍を被る」。二部記述の各項について:

- **モデル項**: 両辺が同じ変換を通るので係数はちょうど 1 に相殺される。
- **index 項**: payload 内で自己限定符号にすると `2·natLen i + 1` bit、それを program 化するとさらに 2 倍。
  ⟹ `4·⌈log₂|S|⌉`。

`twoPartLength S := modelComplexity S + 4 * Nat.clog 2 S.card` と**定義側に係数 4 を置く**ことで、
headline の汚染は加法定数だけになる。

### crux — 機械の自己シミュレーション

```lean
theorem payloadComplexity_two_part_le (A : ℕ → ℕ → Part ℕ) (hA : Partrec₂ A) :
    ∃ c : ℕ, ∀ (x y i : ℕ), x ∈ A y i →
      payloadComplexity x ≤ payloadComplexity y + 2 * natLen i + c
```

「`y` を作る payload」と「index `i`」を 1 本の bit 列に詰め（`packBits`）、
それを読み戻して `decodePayload` を**機械の内部で走らせて** `A` に食わせる code を作る。
Mathlib の `Nat.Partrec.Code.eval_part`（`PartrecCode.lean:994`）が自己シミュレーションの核で、
残りは `decodePayload` を `Partrec` にするための bit codec の `Primrec` 化。

---

## 3. Mathlib 補題探索の実録

在庫段（`mathlib-inventory`）と実装段（`lean-implementer`）で性格が違う。在庫段は網羅的な loogle 掃引、
実装段は 0-hit が 1 件だけで、あとは在庫テーブルを引くだけで足りた。

### 在庫段の loogle クエリ（打った順）

```bash
L="./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index"
$L "Encodable (Finset _)" ; $L "Denumerable (Finset _)"
$L "Primcodable (Finset _)" ; $L "Primcodable (Multiset _)" ; $L "Primcodable (List _)"
$L "Nat.Partrec.Code.eval_part" ; $L "Nat.Partrec.Code.exists_code"
$L "Computability.encodeNat" ; $L "Primrec, Computability.encodeNat"
$L "Finset.orderIsoOfFin" ; $L "Finset.equivFin" ; $L "Finset.sort_nodup"
$L "Primrec Nat.unpair" ; $L "Primrec₂ Nat.pair"
$L '"SufficientStatistic"' ; $L '"structureFunction"' ; $L '"MinimumDescriptionLength"'
$L '"KolmogorovComplexity"' ; $L '"Sufficient"' ; $L '"Kolmogorov"' ; $L '"descriptionLength"'
$L "Nat.log, Real.logb" ; $L "Nat.clog, Real.logb" ; $L "List.idxOf, List.length"
```

### 「無かった」もの

- **`Primcodable (Finset _)` / `Primcodable (Multiset _)`** — 両方 `Found 0 declarations mentioning Finset and Primcodable. Of these, 0 match your pattern(s).`
  **これが在庫段で最も危険な発見**だった。`Finset.encodable` は存在するのに、それを復号する decoder は
  `Computable` を名乗れず `Nat.Partrec.Code` に載らない。モデルを `Finset` の符号で表す設計は decoder 段で行き止まる。
  回避は「`Finset` は statement 側だけに置き、符号は `S.sort (· ≤ ·) : List ℕ` にする」で**追加作業ゼロ**。
- **`Primrec` × `Computability.encodeNat`** — `Found 0 declarations mentioning Primrec and Computability.encodeNat.`
  （`Computability.encodeNat` に付く Mathlib 補題は `Computability.decode_encodeNat` の 1 本のみ）。自作 16 本。
- **`Primrec Nat.bits`** — `Found 0 declarations mentioning Primcodable.ofDenumerable, Nat.bits, Primrec, List, Primcodable.bool, Nat, Bool, Denumerable.nat, and Primcodable.list. Of these, 0 match your pattern(s).`
  `Nat.bits` 経由を諦め、`encodeNat n = decide (n % 2 = 1) :: encodeNat (n / 2)` を `PosNum` 帰納で自作し、
  `Primrec.nat_iterate`（`Primrec/Basic.lean:539`）で `Primrec` に載せた。
- **`Partrec.cond`（存在しない、`Computable.cond` のみ）** — `decodePayload` の 3 分岐（空 / literal / interpret）を
  `Partrec` のまま場合分けできない。**回避が設計として効いた**: 分岐を
  `payloadDispatch : List Bool → Option (Code × ℕ)` に潰して `Primrec.cond` の側で済ませ、
  literal モードを `Code.id` + `eval_id`（`PartrecCode.lean:502`）で interpret モードと同じ `eval` 経路に載せ、
  最後に `Partrec.bind` 1 本（`SufficientStatistic.lean:340`–`388`）。これが無ければ 3 分岐の合成が要った。
- **`Primrec List.dropLast`** — `List.dropLast_eq_take` + `Primrec.list_take` で 3 行。
- **`Encodable.encode` のサイズ補題** — Mathlib に 1 本も無い。設計で回避（モデル項を `K(S)` で述べればサイズ補題が要らない）。
- **§14.12 の object 一式**（`SufficientStatistic` / `structureFunction` / `MinimumDescriptionLength` /
  `descriptionLength` / `KolmogorovComplexity`）— 全部 `Found 0`。定義から自作。

### 名前が違ったもの（在庫が先に潰した / 実装で判明した）

| 想定した名前 | 実際 | 出所 |
|---|---|---|
| `Nat.clog_le_clog_of_le` | `Nat.clog_mono_right` | 在庫が事前に訂正 |
| `Primrec.natPair` | `Primrec₂.natPair` | 実装段 |
| `PrimrecPred p` ≡ `Primrec (fun a ↦ decide (p a))` | `PrimrecPred` は `∃ (_ : DecidablePred p), Primrec …` なので直接は型が合わず、`PrimrecPred.decide`（`Basic.lean:409`）を挟む | 実装段 |

---

## 4. 試行錯誤と後戻り

### 4.1 在庫段で skeleton を `lake env lean` に通しておくと、実装で定義の pivot が起きない

**状況**: 在庫エージェントは調査中に scratchpad で probe を 4 本 + skeleton を 1 本書き、
**定義 6 本 + 構造的定理 7 本を 0 error / 0 sorry で machine 検証した状態**で在庫の §着手 skeleton に載せた
（`kolmogorov-w2-p10-inventory.md:361`）。

**結果**: 実装は**定義形を 1 つも変えずに走った**。6 定義は在庫の記載と最終コードで一致している
（`modelCode` / `modelComplexity` / `twoPartLength` / `mdlComplexity` / `structureFunction` / `IsSufficientStatistic`）。
修正は 2 点だけ: 補題 1 本の改名（`structureFunction_zero_of_singleton_budget` →
`structureFunction_eq_zero_of_singleton_budget`）と、証明 1 行の差し替え（ℕ∞ では `zero_le` が効かず `by simp`）。

**教訓**: CLAUDE.md「Mathlib-shape-driven Definitions」が警告する mid-proof の定義 pivot が**ゼロ**だった。
効いたのは「在庫に定義形を**書く**」ことではなく「在庫の定義形を**コンパイルしてから書く**」こと。
在庫エージェントに scratchpad での probe を許し、機械検証済みの skeleton を成果物に含めさせる運用は、
そのまま定型化できる。同じ在庫が予測した数値（`clog 2 1 = 0`、`natLen 0 = 0`、係数 4 の会計、
`Finset.sort_singleton` の挙動）も全部実測どおりだった。

### 4.2 「唯一の crux・退避候補」が退避せずに閉じた

**状況**: 在庫は自作 4 項目のうち crux（自己シミュレーション、見積 90–160 行、bit codec 込みで 150–290 行）を
「P10 の他の全部より重い」と評価し、撤退ライン R-W2c を提案していた
——crux 1 本だけを `sorry + @residual(plan:kolmogorov-w2-machine-partrec)` の共有補題として残し、
残りを type-check done で着地させる、という縮退出口。

**結果**: **退避出口は発火しなかった**。crux は見積上限を少し超える 360 行（`:154`–`:513`）で proof done。
その結果、新 slug `kolmogorov-w2-machine-partrec` は plan に登録していない
——貼る先の `sorry` が 1 つも無いため、slug を作ると「存在しない残作業」を plan が主張することになる。

**教訓**: 退避出口を用意することのコストは「発火しなかったときに slug を消し忘れる」ことに集中している。
plan 側に「未発火の退避ラインは slug を起票しない」を明文化しておくと、
plan が架空の残作業を抱えるのを防げる。逆に、**退避出口を用意しておいたこと自体は正しかった**——
crux が本当に発散した場合、仮説束ね（`IsSelfSimulationHypothesis` のような述語化）に逃げる圧力がかかる場面だった。

### 4.3 実装が依存構造を変えた（P10 は P9 に依存しない）

**状況**: 在庫は crux を `Omega.lean` の `prefix_invariance`（`K(x) ≤ 2·|q| + b`）に投入する想定で書かれており、
「`prefix_invariance` を使う段で `import …Kolmogorov.Omega` を追加」と明記していた
（`kolmogorov-w2-p10-inventory.md:414`）。

**原因**: `prefix_invariance` は `K` 世界の主張なので **2 倍係数を被っている**。crux は payload 世界の加法的な主張が欲しい。

**抜け方**: 実装は `Omega` を import せず、payload 世界で自前の
`payload_invariance : ∃ b, ∀ x q, x ∈ A (decodeNat q) 0 → payloadComplexity x ≤ q.length + b`
を建てた（`SufficientStatistic.lean:411`、`Nat.Partrec.Code.exists_code` +
`payloadComplexity_le_of_eval` の 9 行）。実際の import 行は `Levin` までで `Omega` を含まない。

**結果**: **P10 は P9 に依存しない**ことが実装で判明し、親 plan の DAG を訂正した。
副産物 `payload_invariance` は「加法性が欲しい主張」全般の入口として残る
（P8 で park した加法版 Levin を今後攻めるときに最初に見る資産）。

**教訓**: これは §4.2（P8 の恒等式）が P10 の**依存構造まで**変えた例。
「上位量の補題を再利用する」より「下位量で建て直す」方が安いケースは、
上位量が下位量の定数倍で定義されているとき（＝係数が定理の形の一部であるとき）に系統的に起きる。
在庫の依存欄は「どの補題を使うか」だけでなく「その補題はどの世界で述べられているか」を持つべき。

### 4.4 honesty のための定式化変更が、証明量そのものを減らした

**状況**: 教科書形 `twoPartLength S = K(S) + ⌈log₂|S|⌉` で定義すると、headline
`K(x) ≤ twoPartLength S + c` は**偽**（`3·⌈log₂|S|⌉` の不足）。
係数 1 を主張しないために、係数 4 を `twoPartLength` の定義側に置いた。

**結果**: headline の汚染が**加法定数だけ**になり、`4·⌈log₂|S|⌉` と実際の bit 数を突き合わせる bridge 補題が
一切不要になった。honesty ゲート（`honesty-auditor`）は独立に、係数 1 版がこの機械では
**数え上げにより偽**であることを確認している（P8 の加法版が「真偽不明」だったのより強い根拠）。

**教訓**: 「正直さのための定式化変更」と「Mathlib-shape-driven な定式化」が同じ方向を向いた例。
偽を避けるために係数を定義へ動かすと、その係数を証明中に運ぶ必要が消える。
逆向きの読み方をすると、**bridge 補題が生えそうになったら、まず「定義側が主張を弱めていないか」を疑う**と
honesty の欠陥も同時に見つかる可能性がある。

なお honesty ゲートは実装ノートの negative claim も 1 箇所訂正している:
2 つの 2 倍のうち `selfDelimit` 由来の側は**今回の packing の性質**であり、より賢い区切り符号なら下がりうる
（機械の性質と言い切るのは、コンパイラで棄却していない negative claim）。

### 4.5 pack の設計 backtrack（`Encodable.encode` は長さに対して指数的に無駄）

**状況**: index と payload を 1 本にまとめるのに、当初 `Encodable.encode (pack : List Bool)` を検討した。

**原因**: `encodeList` は要素ごとに `Nat.pair` で二乗するので、**長さが二重指数**に膨らむ。
在庫段の実測でも 12 要素モデルの `modelCode` が 14941 bit だった。

**抜け方**: `packBits i d := selfDelimit (encodeNat i) ++ (d ++ [true])` で bit 列を直接組み、
`decodeNat` で ℕ に落とす。末尾の sentinel `[true]` は
`encodeNat (decodeNat w) = w`（`w` が `true` で終わるとき）の canonical 条件を満たすため
（`decodePosNum [false] = 2` なので canonical 制限は必須）。

**教訓**: `Encodable` は「符号が存在する」ことを保証するだけで、**符号長について何も約束しない**。
記述長を測る形式化で `Encodable.encode` を長さの担い手にしてはいけない。
在庫 §A に「`encode` のサイズ補題は Mathlib に 1 本も無い」が書かれていたのは、この判断の予告だった。

### 4.6 `decide` の中を rewrite すると Decidable instance が付いてこない

**状況**: `encodeNat n = decide (n % 2 = 1) :: encodeNat (n / 2)` の形を `PosNum` 帰納で示す途中、
`PosNum.cast_bit0` を `simp only` した時点で「型が instances transparency で不整合」になった。

**原因**: `decide p` の `p` を書き換えると、対応する `Decidable p` インスタンスが自動では追従しない。

**抜け方**: `congr 1` + `decide_eq_false_iff_not` / `decide_eq_true_iff` で `Prop` 側に降ろしてから扱う。

**教訓**: `decide` を含む項の rewrite は、`Prop` 側に降ろしてから行うのを既定手順にする。
このパターンは bit 列を扱う形式化で必ず出る（bit の取り出しが `decide (n % 2 = 1)` の形になるため）。

### 4.7 `Partrec₂` は metavariable 位置で `Partrec` から unify しない

`Partrec.bind` の第 2 引数を `have` で用意するとき、型注記を `Partrec₂ fun …` 側に書かないと通らない。
`Partrec₂ f` は `Partrec (fun p ↦ f p.1 p.2)` の略記だが、
elaborator は metavariable 位置でこの展開を選んでくれない。

### 4.8 loogle をループでバッチ実行すると、後続クエリの出力が黙って消える

**状況**: `for q in "Primrec Nat.bits" "Nat.bits" "Primrec Nat.binaryRec"; do … loogle "$q" | head -20; done`
という 3 連クエリを打った。

**原因**: 2 本目の裸の `Nat.bits` クエリが返らず、**コマンド全体が 2 分でタイムアウト**した（`Exit code 143`）。
3 本目 `Primrec Nat.binaryRec` は実行されずに終わったが、
出力上は 1 本目の `Found 0` と 2 本目の途中までが見えているので、**失敗が失敗に見えない**。

**教訓**: 「0-hit だったから壁」の判定材料が、実は**そもそも実行されていないクエリ**である経路がある。
loogle をバッチで回すときは (a) クエリごとに終了コードを表示する、(b) 修飾語なしの裸の識別子クエリは
結果過多で返らないことがあるので単独で打つ。CLAUDE.md の「loogle 0-hit は必要だが十分でない」に、
**「0-hit と未実行を区別せよ」**を足す価値がある。

---

## 5. ボトルネックではなかったもの

- **定義形の決定** — 在庫段で完了しており、実装段のコストは 0（§4.1）。これは投資済みだっただけで、
  「安い工程」という意味ではない。
- **解析的な壁** — 0 件。在庫の判定どおり、不在物はすべて (a) 定義の選択、(b) 設計での回避、(c) 自作で処理できた。
- **`Nat.clog` / `Nat.log` の算術** — Mathlib の在庫がほぼ 100%（境界・単調性・Galois 接続・実 log への橋
  `Real.natCeil_logb_natCast` まで揃っている）。
- **`Nat.Partrec.Code` の中核** — `eval_part` / `exists_code` が Mathlib にある。
  自己シミュレーションが「重い」のは核が無いからではなく、**自前の codec を `Primrec` に持ち上げる手数**のため。
- **`sInf` の退化** — `mdlComplexity` は singleton モデルが常に居るので ℕ で安全、
  `structureFunction` は ℕ∞ にすることで `Nat.sInf ∅ = 0` の黙示退化を塞いだ（在庫段で機械確認済み）。

---

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **在庫成果物に「machine 検証済み skeleton」を必須化**（在庫エージェントに scratchpad probe を許し、`lake env lean` を通した定義群を在庫に載せる、§4.1） | 定義 pivot 0 件。実装段で定義を作り直すコスト（このサイズなら 100 行超の書き直し）がまるごと消えている |
| 高 | **在庫の依存欄に「その補題が述べられている世界」を持たせる**（§4.3） | 在庫が指定した `Omega` 依存は実装で不要と判明した。依存の誤りは親 plan の DAG まで波及していた |
| 中 | **loogle バッチ実行のラッパー**: クエリごとの終了コード表示 + 裸の識別子クエリの単独実行強制（§4.8） | 「未実行のクエリを 0-hit と読む」経路を塞ぐ。壁判定の信頼性に直結 |
| 中 | **`Encodable` を長さの担い手にしていないかの検出**: 記述長を定義する場所で `Encodable.encode` の**長さ**を取っていたら警告（§4.5） | 設計 backtrack 1 回。Mathlib にサイズ補題が 1 本も無いので、気づかないと後段で行き止まる |
| 中 | **`Primrec` / `Partrec` 組み立ての定型集**: `Partrec.cond` が無いときに `Option` に潰して `Primrec.cond` へ寄せる、`Code.id` + `eval_id` で分岐を単一 `eval` に載せる、といった定石（§3） | crux の設計で最も効いた判断がこの 2 つ。定石として持っていれば探索が要らない |
| 低 | **`decide` を含む項の rewrite 手順**（§4.6）/ **`Partrec₂` の型注記位置**（§4.7） | それぞれ 1〜2 回の試行 |

---

## 7. 補足

### 在庫が正しく予言していたこと（実装で追認）

- `Nat.clog_mono_right` が正しい名前（`clog_le_clog_of_le` は非在）
- `clog 2 0 = 0` / `clog 2 1 = 0` / `natLen 0 = 0`
- 係数 4 の会計（モデル項の係数がちょうど 1 に相殺される）
- `Finset.sort_singleton` の挙動
- 「genuine な `wall:` は 0 件」

### 在庫の見立てと実装が食い違った点

- 在庫 §自作 3 は `Primrec decodeNat` を主役に挙げていたが、crux で本質的だったのは **`Primrec encodeNat`** の側
  （code は ℕ を受け取って bit 列に戻す）。両方必要で、`encodeNat` 側は `bitStep` の `Primrec.nat_iterate` で組んだ。
- 在庫は crux を `Omega.lean` の `prefix_invariance` に投入する想定だったが、実装は payload 世界で建て直した（§4.3）。

### 採らなかった代替案

- **Route A**（`natLen (modelCode S)` を「モデル記述長」とする弱い two-part bound、在庫 §自作 5、約 40 行）。
  真だが退化している——`Encodable` の符号が無駄なので literal 上界 `K(x) ≤ 2·natLen x + 3` より常に弱く、
  二部符号のトレードオフ（§14.12 の主題）を表現しない。K(S) 版が入ったので採らなかった。
- **「最小十分統計量が存在する」の無条件形**。ℕ で書くと空集合退化を踏むため、
  `c` を明示引数に取り「`c` を十分大きく取る形」に落とす（`exists_isSufficientStatistic_singleton`、
  `∃ c, ∀ x, IsSufficientStatistic c x {x}`）。

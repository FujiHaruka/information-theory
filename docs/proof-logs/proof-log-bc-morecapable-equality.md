# more capable broadcast channel の容量領域の等号 Lean 形式化 — ボトルネック分析

将来「片側だけ実測して一般化する誤りを潰す検算ツール」「loogle の *クエリが走らなかった* を
*Mathlib に無い* と読ませない層」を作るためのベースライン記録。

**定量データ**: [docs/metrics/bc-morecapable-equality.metrics.md](../metrics/bc-morecapable-equality.metrics.md)

参照: plan [`docs/shannon/bc-general-region-plan.md`](../shannon/bc-general-region-plan.md) /
在庫 [`docs/shannon/bc-morecapable-equality-inventory.md`](../shannon/bc-morecapable-equality-inventory.md) /
前キャンペーンの proof-log [`proof-log-bc-lessnoisy-equality.md`](proof-log-bc-lessnoisy-equality.md)

---

## 0. 対象問題と成果物

**more capable な broadcast channel の容量領域の単一文字特徴づけ** (Nair–El Gamal、
El Gamal–Kim Ch. 8)。less noisy より真に広いクラスで、操作的に定義した容量領域が UV 外界と一致する:

```lean
@[entry_point] theorem bc_moreCapable_capacity_eq_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hmc : IsBCMoreCapable W) :
    bcCapacityRegion W = bcOuterRegionUV W
```

`InformationTheory/Shannon/BroadcastChannel/Superposition/MoreCapable.lean:892`。
`#print axioms` は 3 本の headline すべてで `[propext, Classical.choice, Quot.sound]`。
明示仮説は前キャンペーンと同じ 2 本で、`hW` は全支持の regularity、`hmc` は領域を一切参照しない
チャネルレベルの述語。**`bc_lessNoisy_capacity_eq_uv` を包含する** (`IsBCLessNoisy.isBCMoreCapable`
経由で系になる。畳み直しは意図的に未実施 = plan §後続作業 G-1)。

成果物は新設 1 ファイル + 上流 5 ファイルへの移設のみ (行数は
`git show <commit>:<file> | wc -l` / `git show --stat` で再導出。散文からの転記ではない):

| ファイル | 変化 | 役割 |
|---|---|---|
| `Superposition/MoreCapable.lean` | 新設 909 行 / 32 decl / import 1 本 | 条件付き more capable → 3 制約内界 → 等号 |
| `OuterBoundUV/Bridge.lean` | +11 −0 | `uvInfoJoint` を 4 スロットの隣へ (F-28) |
| `OuterBoundUV/Assembly.lean` | +8 −0 | 再ラベル不変性を兄弟の隣へ |
| `Superposition/TimeShare.lean` | +6 −6 | ベタ書き 5 箇所を `uvInfoJoint` へ置換 |
| `Shannon/{MutualInfo,CondMutualInfo}.lean` | +26 −0 | 汎用 2 本を BC namespace から昇格 |

0 error / 0 `sorry` / 0 `@residual` / 0 `set_option linter.*` 抑止。

---

## 1. 問題のキャラクター

**このキャンペーンは異例に滑らかだった**ので、記録する価値があるのは「何に詰まったか」ではなく
**「なぜ詰まらなかったか」と「それでも予測が外れた軸はどこか」**である。

支配項は実装ではなく**後片付け**だった。metrics の subagent 別表で、整理 leg C の active time は
実装 leg A・leg B のどちらより長い。leg A / leg B が短いのは、前 leg が実装前に probe 7 本を
**全部コンパイル通過させてから**在庫を書いたためで、実装は probe の証明本文の逐語持ち上げに近い。

過去の proof-log との比較:

| 家系 | 支配項 | 効くツール |
|---|---|---|
| `shannon-hartley-converse-final` | Mathlib のどこに何があるか | loogle |
| `marton-inner-bound` | 自分たちが書いた資産のどこに何があるか | in-project の型検索 |
| `bc-lessnoisy-equality` | plan が書いた命題・仮説・見積りが実物と合っているか | plan と実物の突合、probe |
| **本件** | **probe が届かない軸 (個数 / 自動性 / 波及の向き / 命名) の予測誤差** | **予測の型を分けて、届かない軸だけ着手時に再実測させる** |

4 つ目は 3 つ目の続きだが質が違う。probe は「この等式は成り立つ」を機械で確定させる道具として
完全に機能した (実装段で数学が覆った箇所は 0)。外れたのはすべて **probe が確かめていない種類の主張**
だった。

---

## 2. 数学的方針

### (1) 第 3 制約の形が下流をすべて決めた

3 制約内界の和レート制約を `p.1 + p.2 ≤ bcInfoJoint` ではなく
**`max p.1 0 + p.2 ≤ bcInfoJoint`** にした。理由は達成側の入口
`bc_achievability_of_rate_lt` (`Achievability/Assembly.lean:1103`) の仮説が逐語で
`hJlt : max R₁ 0 + R₂ < bcInfoJoint` だから — CLAUDE.md「Mathlib-shape-driven Definitions」の
教科書ケースで、参照するのが Mathlib ではなく in-project の到達点になっているだけである。

効果は署名に出た。**内界の達成可能性が比較クラス仮説を 1 本も要求しない**
(`bcSuperpositionRegionSumRate_subset_capacity` は `hW` のみ)。素直な `p.1 + p.2` 形にすると
負レート枝で `bcInfo₂ ≤ bcInfoJoint` が必要になり、クラス仮説が達成側へ漏れる。

### (2) 核は more capable の「条件付き版」

`IsBCMoreCapable` は無条件の `I(X;Y₂) ≤ I(X;Y₁)` を全入力分布について言う述語である。
必要なのは補助変数で条件付けた版 `I(X;Y₂|U) ≤ I(X;Y₁|U)` で、これは
`condMutualInfo_bcJointDistribution_out₁/₂_eq_lintegral` で両辺を `∫⁻ u, mutualInfoOfChannel (K u) …`
に落とし、被積分関数へ点ごとに述語を当て、積分の単調性で閉じる (`MoreCapable.lean:176`)。

これが gateway `uvInfoSum₁ ν ≤ uvInfoJoint ν` を出し、**less noisy の逆包含が
`obtain ⟨hb₁, hb₂, hs₂, -⟩` で捨てていた外界の 4 本目 `sumBound₁` が第 3 制約の担い手になる**。
前キャンペーンの 4.4 で「捨ててよい制約と捨ててはいけない制約は独立に点検するしかない」と
書いた箇所が、1 キャンペーン後に「捨てた側が主役になる」形で回収された。

### (3) 負レート枝が独立の obligation を要求した

`R₁ < 0` の枝では `max R₁ 0 = 0` に潰れるので、和制約は `R₂ ≤ uvInfoJoint` になる。
これは gateway からは出ず、別に `uvInfo₂ ν ≤ uvInfoJoint ν` (`:364`) が要る。
**plan にも S8 在庫にも無かった obligation** で、在庫 leg が probe MC6 で見つけた。
全平面規約 (第一象限制約を持たない外界) の代償が、ここでも 1 本増える形で出ている。

---

## 3. 補題探索の実録

### 3.1 実装 3 leg の loogle 照会は 0 回

実装 leg A / leg B / leg C、style ゲート 2 回、README 同期、plan 同期の
subagent transcript の Bash に `loogle` は 1 度も現れない。再導出:

```bash
D=~/.claude/projects/-Users-haruka-dev-lean-projects/<session>/subagents
jq -r 'select(.message.content) | .message.content[]?
  | select(.type=="tool_use" and .name=="Bash") | .input.command' $D/agent-*.jsonl | grep -c loogle
```

Mathlib 側の 0-hit も 0 件。BC 家系は more capable の実装 leg まで **10 leg 連続で Mathlib の穴が 0**
で、この家系の探索コストはとうに Mathlib から in-project へ移っている。

### 3.2 在庫段の loogle 8 クエリ — 3 件は `Found 0` ですらなかった

在庫 leg は loogle を 8 クエリ打った。**`Found 0 declarations` は 1 件も出ていない**。
代わりに 3 件が `unknown identifier` を返した:

```
$L "InformationTheory.Shannon.mutualInfo"      → unknown identifier 'InformationTheory.Shannon.mutualInfo'
                                                  Maybe you meant: * "InformationTheory.Shannon.mutualInfo"
$L "ProbabilityTheory.klDiv, ConcaveOn"        → unknown identifier 'ProbabilityTheory.klDiv'
                                                  Maybe you meant: * "ProbabilityTheory.klDiv", ConcaveOn
$L "MeasureTheory.mutualInfo"                  → unknown identifier 'MeasureTheory.mutualInfo'
```

**これは否定的回答ではない — クエリが走っていない**。loogle の "Maybe you meant" は
同じ文字列を引用符で括り直したもの、つまり「識別子検索ではなく名前部分文字列検索として出し直せ」
という提案であって、「その命題は Mathlib に無い」ではない。CLAUDE.md は
「loogle は権威的に答える (例: `Found 0 declarations`)」と書いているが、**その権威が付くのは
`Found 0` にだけ**で、`unknown identifier` に同じ重みを読むと「Mathlib に無い ⟹ 自作」の
推論が根拠なしに走る。

在庫 leg はここで `rg` に落として `.lake/packages/mathlib/Mathlib/InformationTheory/` を
直接見に行き、`ConcaveOn` / `ConvexOn` がその配下に無いことを確認してから
「相互情報量の入力についての凹性は Mathlib に無い」と結論している (前キャンペーンと同じ判定)。
**手順としては正しかったが、正しさは loogle 出力の読み分けに依存していて、そこは規約に書かれていない**。

### 3.3 「Mathlib に無い」ではなく「向きが名前と逆」が 1 件

新規実装の 2 leg (A / B) が記録した Lean のコンパイルエラーは leg B の 1 件だけで、
それがこれだった (出力は逐語。整理 leg C の 1 件は別物 → 4.2):

```
MoreCapable.lean:554:13: error: Application type mismatch: The argument
  add_le_add_right (le_max_left R₁ 0) R₂
has type   R₂ + R₁ ≤ R₂ + max R₁ 0
but is expected to have type   R₁ + R₂ ≤ max R₁ 0 + R₂
```

`#check` で逐語確認した本体:

```
@add_le_add_left  : b ≤ c → ∀ (a : α), b + a ≤ c + a
@add_le_add_right : b ≤ c → ∀ (a : α), a + b ≤ a + c
```

**2 本とも名前から期待する向きの逆**である。回避は向きを問わず `add_le_add le_rfl h` (左固定) /
`add_le_add h le_rfl` (右固定)。詳細は 4.1。

---

## 4. 試行錯誤と後戻り

### 4.1 片側だけ実測して一般化する — 同一キャンペーン内で 3 件

**症状**: 在庫 §Q5 は `add_le_add_left` の向きだけを `#check` で確かめ、
「本 Mathlib では右加算の向き」と 1 行で注記していた。実装 leg B は**逆側の
`add_le_add_right` で同じ罠を踏んだ** (3.3)。

**原因**: 「名前と逆」という現象は 2 本の対で成り立っているのに、実測したのは 1 本だけだった。
片方を確かめた時点で「これで対の性質は分かった」と読める書き方になっており、
読んだ実装 leg は逆側を無警戒で使った。

**同型が 2 件**: どちらも「一方を数えて他方を数えなかった」:

- **改名表**: ブリーフの改名対象一覧を `rg` ではなく在庫の表から写したので、S7 変種側の
  `exists_fullSupport_bcInfo3_ge` 一族が落ちた。
- **置換対象**: F-28 のベタ書き置換対象を `TimeShare.lean` だけ数え、`MoreCapable.lean` を
  数えなかった (4.4)。

**抜け方**: いずれも実装時にコンパイラ / `rg` が拾って、その場で 1 行〜数行で片付いた。
**コストは低いが検出は偶然に依存している** — 改名表の漏れは leg C が着手時に
`rg -n "bcSuperposition3Region|bcInfo3" -g '*.lean'` を打ち直したから見つかった。

**教訓**: 再発防止線は「**一方を実測したら他方も実測する**」。対をなす API (`_left` / `_right`、
`fst` / `snd`、`out₁` / `out₂`)、対をなすファイル (定義元 / 消費側)、対をなす方向 (順包含 / 逆包含)
は、片方の実測を他方の根拠にできない。ツール化するなら「在庫が `_left` を注記したら `_right` の
`#check` を必須にする」程度の機械的な対称性チェックで足りる。

### 4.2 波及の「向き」も予測から外れる

**症状**: 在庫は F-28 (`uvInfoJoint` の def 化 + ベタ書き置換) について
「**consumer** が旧ベタ書き形に `rw` していると落ちる」と予告した。

**実測**: **consumer 側の修正は 0 箇所**。落ちたのは `bcInfoJoint_uvCloudLaw`
(`TimeShare.lean:477`) **自身の証明本文**で、`unsolved goals` 1 件、末尾に `rfl` を 1 行足して解決。
逆に副産物として、leg B が予防的に置いていた
`show mutualInfo ν' … = uvInfoJoint ν' from rfl` 2 箇所が**不要になり削除された**。

**原因**: 非 reducible な `def` を挟むと、`rfl` で埋まっていた syntactic な一致が
明示的な `rfl` を要求する形に変わる。それが現れるのは「その項を結論に持つ宣言」であって
「その宣言を呼ぶ側」ではない。前キャンペーンの 4.6 (`inferInstance` が落ちない) と同じ機構の
別の面である。

**教訓**: probe / 事前予測が保証するのは**確かめた等式だけ**で、そこから
「ちょうど N 本」(完全性)・「探索が見つける」(自動性)・「壊れるのは下流」(**波及方向**) は出てこない。
3 つ目が本キャンペーンで足された軸。予測を書くときは「これは probe が確かめた」と
「これは probe の外の推測」を型で分けるべきで、後者は着手時に 1 行書いてコンパイラに落とさせる
以外に確かめる手が無い。

### 4.3 自前ルールが規約より厳しいと後続 leg を縛る

**症状**: 在庫 §Q8 が「**600 行を超えたら `MoreCapable/{Slot,Assembly}.lean` の 2 分割**」という
方針を自前で立てていた。実装は 909 行で着地した。

**原因**: `docs/rules/module-structure.md` の閾値は 1500 行で、拘束条件は行数ではなく
**関心の混在**である。600 という数字は規約のどの条文の言い換えでもなく、在庫 leg が
その場で発明したものだった。

**抜け方**: style ゲートが**規約違反として無効化**した。判定の根拠は行数ではなく突き合わせで、
module doc の 7 つの主張すべてが実コードの各段
(`condMutualInfo_bcJointDistribution_out₁_eq_lintegral` → `IsBCMoreCapable.condMutualInfo_le` →
和制約 → `uvInfoJoint` の 3 不変性 → 時分割 / 摂動 / 量子化 → 閉包回収) に対応していることを
確認した上で「1 本の筋として書けている ⟹ 分割不要」としている。将来の切れ目
(`MoreCapable/{Comparison,Equality}.lean`) だけを確定させて残した。

**教訓**: **規約の SoT は `docs/rules/` 側**。在庫 / plan が数値の閾値を書くときは
「規約のどの条文の言い換えか」を明示し、言い換えでないなら **その leg 限りの目安**と明記する。
ここは `plan_lint.ts` で機械化できる — plan / 在庫の散文に現れる行数閾値を
`docs/rules/` の値と突き合わせて、一致しないものに SUSPECT を出せばよい。

### 4.4 def を作った leg が、その def を使い切らない

**症状**: leg A は `uvInfoJoint` と命名した直後の証明本文に、同じ項
`mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)` のベタ書きを 2 箇所残した。
在庫が予告した置換対象は `TimeShare.lean` の 5 箇所で、実測は **7 箇所**だった。

**原因**: 在庫は「既存のベタ書きを数える」タスクとして書いており、
「これから書くコードもベタ書きしうる」を数えていない。

**同一プロジェクト内の再発**: F-6 (`martonInfoSum` が実在しない識別子として plan に登場) /
F-28 と**同じ失敗モードが、名前を付ける当の leg で再発した**形になる。

**教訓**: 「def 化 leg」のチェックリストは既存箇所だけでなく**同 leg の新規コードも走査対象**にする。
`rg` 1 発で済むので、def を追加した leg の終了条件に「その def の展開形が
ファイル内に残っていないこと」を入れるのが安い。

### 4.5 命名は在庫の仮名より、実装 / 監査の実測判断が上位だった

2 件とも在庫の仮名が却下された。

**(a) `kernel_slice` → `compProd_comap_snd_apply`** (`MoreCapable.lean:130`)。
旧名は statement のシンボルを **1 つも転写していない**。新名は左辺
`(K ⊗ₖ (W.comap Prod.snd _)) u` をそのまま読み下したもので、in-repo 先例
`compProd_comap_map_prodMap` と頭を共有する。

**(b) `bcSuperposition3Region` → `bcSuperpositionRegionSumRate`** (`506c5184`)。
在庫は「`3` は数字混じりで先例が無い」と自覚した上で「本 leg では入れて style ゲートの判断に委ねる」
と明記していた。判定は却下 — **`3` は*制約の本数*というメタデータで、statement に現れる記号ではない**
(リポジトリの数字入り先例は添字とバージョンだけ)。在庫が挙げた代案 2 つ
(`bcSuperpositionRegionFullSupportSum` / `bcSuperpositionSumRegion`) は**どちらも不採用**。

**効いたのはタイミング**である。style ゲートは「兄弟の誤称 (`bcSuperpositionRegionFullSupport`) を
待たず今やる方が安い」と判断した。根拠は実測で、`.lean` 参照は本ファイル 1 本 32 箇所のみ
(他ファイル 0)。**改名コストは消費者数について単調増加**なので、leg C が消費した瞬間に上がる。

**教訓**: 「style ゲートの判断に委ねる」と在庫に明記して未決のまま実装へ渡す運用は機能した。
逆に、在庫段で仮名を確定させていたら、consumer が増えてから直すことになっていた。
**未決を未決と書いて渡せるのは、ゲートが着地直後に走る運用があるからこそ**である。

### 4.6 検証バーの「warning 0」は既存 warning のある家系では成立しない

**症状**: オーケストレーターがブリーフに書いた検証バーは当初「warning 0」で、
既存条件として `Copyright too short!` 1 件だけを挙げていた。**これは誤り**。

**実測**: style ゲート A が第 1 段の訂正を返し (「`-D linter.mathlibStandardSet=true` は
プロジェクト内のどのファイルでも `Copyright too short!` を出す。未編集の
`Superposition/Assembly.lean` で再現確認済」)、leg C が第 2 段を返した — BC 家系の既存ファイル
(`Superposition/TimeShare.lean` など) には `linter.style.show` や
「`DecidableEq` を使っていない」系の warning が**実在する**。

**抜け方**: leg C は HEAD 版を取り出して同一設定で lint し、warning 集合の完全一致で
新規増加 0 を示した:

```bash
git show HEAD:<file> > $SP/head.lean
lake env lean -D linter.mathlibStandardSet=true -D linter.unusedFintypeInType=false $SP/head.lean
```

**教訓**: 正しいバーは「warning 0」ではなく「**既存 warning からの増分 0**」。
件数は触るたび動く機械再導出可能値なので、ブリーフにも proof-log にも書かない — 手順だけ書く。
前キャンペーンの 4.5 が「`lake env lean` は linter に盲目」を潰し、今回はその次の層
(「フラグを揃えても既存 warning がある」) が出た形で、**検証ループの穴は 1 段ずつしか閉じない**。

### 4.7 型クラス束は「抑止」ではなく「section 分割」で消す

**症状**: 在庫は probe で出た `unusedSectionVars` 12 件を「実装時は束を絞れば消える」と予告した。
これ自体は当たっている。分かれたのは**消し方**である。

**実測**: 実装は `set_option linter.unusedSectionVars false` を **1 行も使わず**、
section を入れ子に割って消した (`rg 'set_option' MoreCapable.lean` は 0 行、`omit` は 2 箇所)。
結果、`section SumBound` の中で:

```lean
section Chain
variable [StandardBorelSpace U] [Nonempty U] [StandardBorelSpace V] [Nonempty V]
-- uvInfoJoint_eq_uvInfo₁_add_condMutualInfo

section Compare
variable [Countable V] [MeasurableSingletonClass V]
-- condMutualInfo_out₂_le_out₁_of_moreCapable
```

**警告が消える点では抑止と同じでも、分割は「必要な型クラス束の実測値」を副産物として残す**。
これで 6 宣言の束が狭化していることが判明し、後続 leg の要求面として使えた。
抑止で潰していたら得られていない情報である。

併せて、証明冒頭に `classical` を置くと `DecidableEq` が埋まる。leg B の新規 12 宣言の
型クラス束から `DecidableEq` は完全に消えた。

**教訓**: linter の抑止と構造の修正は「警告が消える」という観測では区別できないが、
**残る情報量が違う**。抑止 `set_option` を 1 行入れる差分と section を割る差分は
レビューでは同じ大きさに見えるので、規約側で「抑止は最後の手段」を明示する価値がある。

### 4.8 生成物の自己修復は、生成コマンドを回して初めて効く

**症状**: README の定理表は「curation だけを `docs/readme-theorems.txt` に置き、
パスは毎回コードから解決するので、ファイルが移動しても自己修復する」設計である。
にもかかわらず `gen_readme_table.ts --check` が **FAIL したまま残っていた**。

**原因**: 前キャンペーンの昇格 leg (F-19、`SuperpositionAssembly.lean` →
`Superposition/Assembly.lean`) で `--write` を回し忘れていた。表の
`bc_lessNoisy_capacity_eq_uv` のリンクが旧パスを指したままだった (`594887a4` の diff で確認)。

**抜け方**: 今回の `--write` 1 回で、新規行の追加と旧パスの是正が同時に解消した。

**教訓**: 「自己修復する生成物」は **`--check` が CI に載っていても、修復のトリガが人 (エージェント)
側にある**。ファイル移動 / 昇格を伴う leg のチェックリストに `gen_readme_table.ts --write` を
入れる (plan §後続作業 G-6 に起票)。より根本的には、`--check` の FAIL を
「表が古い」ではなく「移動した leg が `--write` を忘れた」と読ませるメッセージにするのが安い。

### 4.9 `docs/rules` と linter が正面から衝突している (家系外の独立課題)

`docs/rules/docstrings.md` item 1 は docstring を必須とする対象に
「headline 定理 (`@[entry_point]` / module doc の *Main statements* に挙がるもの)」を含める。
一方 `scripts/lean_doc_lint.ts:469`–`:477` の internal-doc ratchet は、
`@[entry_point]` でも `@residual` / `@audit:` タグ持ちでもない `theorem` / `lemma` の
散文 docstring を**一律に加算する**。

⟹ **条文どおり Main statements の headline に docstring を付けると CI が落ちる**。
本ファイルの該当 6 本は linter に従って裸のままにしてある。安い運用解は
「docstring を付けたい headline には `@[entry_point]` を付ける」の明文化。
BC 家系の外に効くので本キャンペーンでは実作業をせず、plan §後続作業 G-5 に起票した。

---

## 5. ボトルネックではなかったもの

- **Mathlib 壁**。`@residual(wall:…)` は 1 本も無く、`Found 0 declarations` も 0 件。
  実装 3 leg の loogle 照会は 0 回 (3.1)。
- **honesty**。新規 `sorry` が 0 なので `honesty-auditor` は launch 条件外で、
  キャンペーンを通じて 1 度も起動していない。load-bearing hyp の誘惑が出る場面
  (第 3 制約を `IsMoreCapableTight` のような述語に束ねる) は L-BCO3 / L-BCO9 で明示的に
  禁止されており、そもそも証明が通ったので発火しなかった。
- **数学のアイデア**。中核 5 本すべてが在庫段の probe で証明済みで、実装段で**新しく発明した数学は
  ほぼ 0**。leg A は 14 回の `lake env lean` を通じてコンパイルエラーを 1 件も出していない
  (gateway atom `uvInfoSum₁_le_uvInfoJoint_of_moreCapable` は初回で通過)。
- **設計バックトラック**。定義の作り直し / 経路の差し替えは 0 件。前キャンペーンは
  ここで 1 度経路ごと差し替えている (Marton union が偽) ので、差は「在庫段で目標の真偽を
  数値実験まで含めて確定させたか」に帰着する。
- **universe / 型検査**。`IsBCMoreCapable` が `∀ (U : Type u)` を量化する点は
  `bcAuxAlphabet = ULift.{u} (Fin (k+1))` が前キャンペーンと同様に 0 行で吸収した。
- **ファイル分割**。909 行は閾値 1500 の 6 割で、判定は「分割不要」(4.3)。

---

## 6. 計測から見えたこと

数値は [metrics.md](../metrics/bc-morecapable-equality.metrics.md) が SoT。そこから読める性質を 3 点。

**(a) plan がホットスポットでなくなった**。編集ファイル別 Edit 回数で
`MoreCapable.lean` が 74 に対し `bc-general-region-plan.md` が 61 で、**Lean が plan を上回った**。
前キャンペーンは plan 218 / Lean 最大 45 で 4 倍以上の開きがあった。差は leg 構成にある —
本キャンペーンは実装が 1 ファイルに集中し、plan 同期が末尾 1 回に畳まれている。
**relay の leg 数が減ると plan の編集回数は線形に減る**が、Lean の編集回数は減らない。

**(b) オーケストレーターの対象ファイル Edit は 0**。前キャンペーンと同じで、実装はすべて
subagent が書いており親 transcript には `Agent` しか残らない。`--no-subagents` で読むと
実作業がまるごと消える性質は変わっていない。

**(c) `python3` が Bash 内訳に立っているが、中身が前回と違う**。前キャンペーンの `python3` は
反例探索の数値計算だった。本キャンペーンのそれは**在庫 leg が probe ファイルに対して行った
テキスト手術** (heredoc + `str.replace` で証明本文を差し替え、`lake env lean` に掛け直す)である。
`Edit` ツールではなく `python3` を使ったのは、同じ置換を複数の probe ファイルへ一括で当てるためで、
**Bash カテゴリ名は同じでも作業の種類が違う**。metrics のカテゴリだけを横比較すると
この差は見えない。

---

## 7. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **対称性チェック** — 在庫 / plan が対をなす API の片方 (`_left`、`fst`、`out₁`、定義元) だけを実測したら、他方の実測を必須にする | 4.1 の 3 件。とくに `add_le_add_right` は新規実装 2 leg 唯一のコンパイルエラーで、在庫が対で確かめていれば 0 件だった |
| 高 | **loogle 出力の読み分け層** — `unknown identifier` を `Found 0 declarations` と別物として扱い、前者では「クエリが走っていない」と明示して名前部分文字列検索へ自動リトライする | 3.2 の 3 件。CLAUDE.md の「loogle は権威的に答える」が `Found 0` にしか掛からないことは条文に書かれていない |
| 中 | **予測の型付け** — 在庫 / plan の予測を「probe が確かめた等式」「個数」「自動性」「波及方向」に分け、後ろ 3 つは着手時の再実測を必須にする | 4.2 / 4.4。3 種類とも本キャンペーンで外れ、いずれも着手時の `rg` 1 発 / 1 行のコンパイルで確定した |
| 中 | **`plan_lint.ts` に自前閾値の検出を足す** — plan / 在庫の散文に現れる行数閾値を `docs/rules/` の値と突き合わせ、一致しないものを SUSPECT にする | 4.3。600 という数字が規約の 1500 と拘束条件の両方に反したまま在庫に残り、実装 leg の判断材料になっていた |
| 中 | **ファイル移動を検出したら生成物の再生成を促す** — `git diff --name-status` の `R` を見て `gen_readme_table.ts --write` を要求する | 4.8。前キャンペーンから 1 leg 分 `--check` が FAIL したまま残っていた |
| 中 | **def 追加 leg の終了条件** — 追加した `def` の展開形が同 leg の新規コードに残っていないことを `rg` で確認させる | 4.4。F-6 / F-28 と同じ失敗モードの 3 度目 |
| 低 | **linter 抑止 `set_option` の差分検出** — 抑止で消した警告と構造修正で消した警告をレビュー時に区別する | 4.7。抑止していたら 6 宣言の束の狭化は観測されなかった |
| 低 | **既存 warning のベースライン取得を検証手順に組み込む** — `git show HEAD:<file>` 版との warning 集合 diff | 4.6。ブリーフの「warning 0」が 2 段階で訂正された |

---

## 8. 補足

### 「訂正の個数」自体が手数えでずれる — 2 家系連続

plan / 在庫の同期 leg が書き残した訂正の記録が、機械計測と合わない。

**本件**: 在庫と plan は改名について「**予告 6 本に対し実測 8 本**」と記録している。
実際の commit を数えると:

```bash
git show 9eb87b38:docs/shannon/bc-morecapable-equality-inventory.md \
  | grep -oE '[A-Za-z_][A-Za-z0-9_]*3[A-Za-z0-9_]*' | sort -u   # 在庫が名指した宣言名
git show 506c5184 | grep '^-' \
  | grep -oE '[A-Za-z_][A-Za-z0-9_]*3[A-Za-z0-9_]*' | sort -u   # 実際に改名された宣言名
scripts/sig_view.ts --names <file> | grep -i sumrate            # 新名を持つ宣言
```

在庫が名指していた `3` 入りの宣言名は **5 本**、実際に改名された宣言は **10 本**、
HEAD で新名を持つ宣言も **10 本**。予告側も実測側も、記録された数字とずれている。

**前件**: 前キャンペーンの §8 は、plan が S5 の行数を `289 行 (見積 280)` と記録して
「ほぼ的中」と評価したが実測は 375 行だった件を扱っている。**同期 leg が手で数えた数値が
ずれるという同じ機構が、対象を変えて再発した**。

前件は下流 2 本の在庫で較正基準として引用され、確信度の議論に化けた。本件はまだ引用されていない
(記録された「6 → 8」が使われるのは、次に改名 leg を積むときの見積り基準としてである)。
**引用される前に潰せる形にしておくのが安い**。

**教訓**: 「N 件訂正した」「N 本改名した」は行数と同じく `git show | grep -c` で機械再導出できる。
CLAUDE.md の「re-derive > cache」の禁止対象は「機械で安く引ける事実」と書かれているが、
**同期 leg が自分で数えた個数は「実測したはずの数値」に見えるので cache 側に置かれやすい**。
行数と個数はどちらも re-derive 側である。

### 見積りは 2 列で積めば当たり続ける

行数見積りの実測 (すべて `git show <commit>:<file> | wc -l` と `git show --stat` で再導出):

| leg | 在庫の見積り | 実測 (as-landed) | 帯の中か |
|---|---|---|---|
| leg A | ~450 | **487** (style 後 498) | 中 (+8%) |
| leg B | ~400 | **+475 −8** (計 965) | 中 (+17%) |
| 合計 | 帯 820–980 (数学 735 = probe 実測 525 + 未 probe 210、散文・section 145) | **909** (leg C の整理後) | 中 |

前キャンペーンの §8 が確立した「**数学 (probe 実測) / 散文・section** の 2 列で積む」方式は、
S7 / S8 に続き本キャンペーンでも帯内に入った (**2 列方式に切り替えてから 4 leg 連続**)。
probe 行数を下限として読み、散文と section 構造を別枠で積む、という手順は再現している。

ただし帯が当たることと**個々の予測が当たること**は別で、本キャンペーンで外れたのは
すべて行数以外の軸だった (4.1 / 4.2 / 4.4 / 4.5)。**行数の見積りが当たるようになったので、
残る誤差は個数・自動性・向き・命名に寄っている**、というのが 2 家系分の到達点である。

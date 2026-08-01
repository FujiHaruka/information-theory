# BC / MAC 後続作業のリファクタ relay — ボトルネック分析

将来「plan / ブリーフが書いた参照 (宣言名・場所・件数) を実物と機械照合するツール」および
「同名重複と名前解決の実測ツール」を作るためのベースライン記録。証明を 1 行も足さない
**純リファクタ**の relay なので、証明系の proof-log とは支配項が違う。

**定量データ**: [docs/metrics/bc-followup-refactor.metrics.md](../metrics/bc-followup-refactor.metrics.md)

参照: plan [`docs/shannon/bc-general-region-plan.md`](../shannon/bc-general-region-plan.md) §後続作業 /
先行 proof-log [`proof-log-bc-lessnoisy-equality.md`](proof-log-bc-lessnoisy-equality.md)

---

## 0. 対象問題と成果物

BC / MAC 家系で **style / honesty ゲートが提起して当該 leg では見送った負債**を一括消化する。
plan の §後続作業 に B (命名 / 死んだ宣言) / C (数学的な締めどころ) / D (汎用補題の置換統合) /
E / F / G の群として溜まっていたもので、数学は 1 つも増えない。
commit range は `aad88f5d`..`ac0d5163` (29 commits)。
plan はこれを「後続作業の一括消化 (9 leg relay)」と記録している。

| leg | 内容 | commit (実装 / style) |
|---|---|---|
| T1+T2 | 死宣言 2 本削除 + 改名束 9 本 + `ℝ≥0∞` イディオム 2 箇所 | `aad88f5d` / `715605b7` |
| T4 | `IsBCDegraded` を `Achievability/Setup` から `Basic` へ移設 | `19d7f6ab` / `6630a5ee` |
| T3 | 汎用補題 11 本を `Shannon/` へ昇格 (`BoolLaw` / `MutualInfoFiniteRange` 新設) | `27c909ca` / `61971e9b` |
| T3' | MAC 汎用混合 API 13 本を `Probability/` へ昇格し **BC→MAC import を除去** | `08cfde86` / `cacc59d6` |
| T7+T8 | 重複 4 件を既存一般形の系へ畳む (D-1 / G-3 / G-4 + F-24 残余) | `083aceef` / `434f16fd` |
| T6 | 誤称 `bcSuperpositionRegionFullSupport` → `NoSumRate` + 姉妹 `SumRate` の集約 | `2ed67320` / `371dce85` |
| T5 | 再符号化不変性 3 本を `MutualInfoReencoding.lean` へ分離 | `abbf8e58` / `43cd2d0c` |
| T10a | `Achievability/` クラスタの module doc を degradedness 非依存の実態へ | `6a0c68ff` / `4bc00e36` |
| T10b | 可視性 / 改名 / 引数順 / 上流移動 / 呼称是正 / linter | `8cac522b` `054f3994` / `be0750b8` |

家系横断の 4 件が続く: `#20` MAC 側 `*_point_mem` 3 本の追随改名 (`6de04dd9` / `12109990`) /
`#22` `natIndex` の据え置き判断 (`9d16a21e`) / `#23` `entropy_le_log_card` 重複の統合
(`b5c55683` / `939e3550`) / `#25` MAC の `axis` 語彙の意味反転解消 (`d832baef` / `9081cef4`)。
締めが `#21` docs stale sweep (`27fb9bfc` `595acb3c` `ac0d5163`)。

差分 (再導出: `git diff --numstat aad88f5d~1..ac0d5163 -- <path>`):

- `InformationTheory/` — 38 ファイル / +1160 −1236。新設 4 ファイル
  (`Probability/Mixture.lean` / `Shannon/BoolLaw.lean` / `Shannon/MutualInfoFiniteRange.lean` /
  `Shannon/MutualInfoReencoding.lean`)、削除 0 ファイル
- `docs/` — 25 ファイル / +329 −360。plan 本体は 603 → 542 行
  (`git show 27fb9bfc{~1,}:docs/shannon/bc-general-region-plan.md | wc -l`)

**新規 `sorry` 0 / 署名の honesty 変更 0 / `@residual` 新規 0**
(`git diff aad88f5d~1..ac0d5163 -- InformationTheory/ | rg -c '^\+.*\bsorry\b'` が 0 件)。
その結果 `honesty-auditor` は全 leg で起動条件を満たさず **0 回**。代わりに毎 leg
`style-auditor` を回した (metrics のサブエージェント別表)。

---

## 1. 問題のキャラクター

支配項は先行 proof-log と同じ「**書かれた記述が実物と合っているか**」だが、
本件は証明が 1 行も無いので**それしか残らない**。T6 / T7+T8 / T10b の 3 leg で計 5 件、
plan / ブリーフの記述と実測が食い違い、その訂正がそのまま作業内容になった (→ 4.1)。

| 家系 | 支配項 | 効くツール |
|---|---|---|
| `shannon-hartley-converse-final` | Mathlib のどこに何があるか | loogle |
| `marton-inner-bound` | 自分たちが書いた資産のどこに何があるか | in-project の型検索 |
| `bc-lessnoisy-equality` | plan が書いた命題・仮説・見積りが実物と合っているか | plan と実物の突合、probe |
| **本件** | **plan が書いた参照 (宣言名 / 場所 / 件数) が実物と合っているか** | **参照の機械照合、名前解決の実測** |

3 段目との違いは、突合の対象が**命題**から**参照**へ落ちたこと。命題の真偽は Lean を
書かないと分からないが、参照の真偽は `rg` / `#check` / `dep_consumers.sh` で機械的に決まる。
にもかかわらず 5 件外れたのは、**照合そのものを誰も回していなかった**からで、
証明系より自動化の見込みが高い。

---

## 2. リファクタの設計方針

数学的アイデアは無い。設計判断だけを 3 点。

### (1) 昇格は 2 方向に走った

`F-15` は「BC が抱えている汎用補題を `Shannon/` へ上げる」だったが、**逆側**が残っていた:
BC の `MartonFullSupport.lean` が `Shannon/MultipleAccess/TimeSharing.lean` を import しており、
MAC 側の混合 API に依存していた。T3' はこれを `InformationTheory/Probability/Mixture.lean`
という家系中立の位置へ 13 本まとめて上げ、`-import InformationTheory.Shannon.MultipleAccess.TimeSharing`
を落とした (`git show 08cfde86 -- .../MartonFullSupport.lean | rg '^[-+]import'`)。
**「上げる」は片方向の作業ではなく、下向きの依存を消すためにもう一方向へ上げる必要がある**。

### (2) 重複は「一般形を残し特殊形を系にする」— ただし特殊形の署名は逐語で保つ

T7+T8 の 4 件はすべてこの形。特殊形を削除しなかったのは、外部 consumer を触らないため。
D-1 でこの判断が効いた (→ 4.1)。

### (3) 誤称の直し方は「旧名を完全に消す」

`#25` の `axis` 衝突では、番号を入れ替える案 (`axis1` ↔ `axis2`) を却下した。
旧名が生き残ったまま意味だけ反転すると、外部参照が**コンパイルを通ったまま誤解釈される**。
語彙ごと捨てて下付き (`mac_rate₁` / `mac_rate₂`) に移せば、旧名参照はコンパイルエラーになる (→ 4.6)。

---

## 3. 探索の実録

### 3.1 Mathlib — 相互情報量の宣言は 1 つも無い (機械確認)

T10b の F-b (private 補題の上流移動) で「Mathlib 側に同等物が無いか」を確かめた副産物:

```
loogle "ProbabilityTheory.mutualInfo"  → unknown identifier 'ProbabilityTheory.mutualInfo'
                                         Maybe you meant: * "ProbabilityTheory.mutualInfo"
loogle '"mutualInfo"'                  → Found 0 declarations whose name contains "mutualInfo".
```

文字列検索が 0 なので、名前に `mutualInfo` を含む宣言が Mathlib に存在しない。
本プロジェクトの `Shannon.mutualInfo` が定義する側であることの機械的裏づけで、
`bc-lessnoisy-equality` proof-log §3.1 が在庫段階で得ていた同じ 0-hit を、
別の入口 (リファクタの着手判断) から再確認したことになる。

relay 全体で打った loogle は 7 クエリで、**0-hit はこの 2 本だけ**。残りは全ヒット:

| クエリ | leg | 結果 |
|---|---|---|
| `ENNReal.toReal_le_add` | T1 | `Mathlib/Data/ENNReal/Operations.lean:170` (先行 leg で発見済のものの再確認) |
| `Function.Injective Encodable.encode` | T3 | `Encodable.encode_injective` |
| `Fintype.toEncodable` | T3 | `Mathlib/Logic/Equiv/List.lean` |
| `MeasureTheory.Measure.real (MeasureTheory.Measure.map _ _) _` | T3' | Found 7 |
| `MeasureTheory.Measure, ENNReal.ofReal, HSMul.hSMul` | T3' | Found 20 |
| `Encodable.encode_injective` | `#22` | 1 件 |
| `ProbabilityTheory.mutualInfo` / `"mutualInfo"` | T10b | **unknown identifier / Found 0** |

リファクタ leg で Mathlib 探索が発生するのは 2 つの場面だけ —
「自作 def を Mathlib のもので置き換えられるか」(T3 / `#22`) と
「移設しようとしている補題が Mathlib に既にあるか」(T10b)。
どちらでも 0-hit は**壁ではなく設計判断の入力**になる。

### 3.2 Mathlib が**散文で勧めている**書き方の実使用は 0 件

`#22` の差し替え版は `attribute [local instance] Fintype.toEncodable` を要求する。
Mathlib 内でこの語を含む行は 2 件だけで、**どちらも実際の attribute 発行ではなく散文**:

```
rg -n 'local instance.*Fintype.toEncodable' .lake/packages/mathlib/Mathlib/
  → Mathlib/Data/Prod/TProd.lean:29        (module doc の「こうすれば引数を消せる」という言及)
  → Mathlib/Logic/Equiv/List.lean:121      (Fintype.toEncodable 自身の docstring)
```

**Mathlib が docstring で推奨している書き方に、Mathlib 自身の使用例が 0 件**という状態がある。
「Mathlib に書いてある = 先例がある」を検索ヒットだけで判断すると外す (→ 4.5)。

### 3.3 in-repo — 同名重複は名前では引けても「どちらが使われているか」は引けない

`entropy_le_log_card` が `SlepianWolf/Basic.lean` と `MaxEntropy/Basic.lean` に 2 本あった。
名前検索では即座に見つかる。見つからないのは **各 consumer がどちらに解決していたか**で、
これは `rg` では原理的に出ない (→ 4.2)。

---

## 4. 試行錯誤と後戻り

### 4.1 plan / ブリーフの記述と実測が食い違った 5 件

この relay で最も再現性の高い機構。5 件とも「命題が偽だった」ではなく
「**参照が実物を指していなかった**」型で、いずれも機械照合で事前に潰せる。

| # | plan / ブリーフの記述 | 実測 | 外れ方 |
|---|---|---|---|
| G-2 | 「採用は `bcSuperpositionRegionSumRate` — 蒸し返さないこと」 | その名前は**姉妹 def の既済改名** (`506c5184`) の記録 | 対象の取り違え |
| D-1 | 「**同ファイル内で完結する**のでこちらだけ先に切るのが安い」 | 唯一の direct consumer は MAC 側の別ファイル | 件数は当たり、場所が外れ |
| F-13 | `isMarkovChain_map_comp` の呼び出し 3 箇所 | **3 箇所 (plan が正しい)**。突合側の `rg` が 2 と報告 | 測定側の切り詰め |
| F-b | 「条件付き版が `Gateway.lean` に public で既存」 | 別命題 | 命題の取り違え |
| T10b (6) | over-claim docstring を `file:line` で列挙 | 着地した差分は列挙より多くの行に触れた | 列挙の取りこぼし |

**(a) G-2 — 記録された名前が改名先ではなく別 decl の履歴だった**

plan G-2 は「`bcSuperpositionRegionFullSupport` の誤称。在庫の代案 2 つはどちらも不採用。
採用は `bcSuperpositionRegionSumRate` — 蒸し返さないこと」と、決着済みの体裁で書かれていた。
実物では `bcSuperpositionRegionSumRate` は**すでに `MoreCapable.lean` に存在する別の def** で、
先行 leg の style ゲート (`506c5184`、`bcSuperposition3Region` からの改名) が付けた名前だった。

2 つは別概念である。`Region.lean` の現物で比べると、旧 `FullSupport` は
`p.1 ≤ bcInfo₁ ∧ p.2 ≤ bcInfo₂` の **2 制約**、`SumRate` はそこに
`max p.1 0 + p.2 ≤ bcInfoJoint` を加えた **3 制約**で、後者は前者の真部分集合。
T6 は前者を `NoSumRate` に改名し、後者を `Region.lean` へ集約した。

**教訓**: 「採用は X」という決着表記は、X が**まだ存在しない名前**なのか
**すでに別の宣言が持っている名前**なのかで意味が正反対になる。plan は名前を書くとき
「新規に付ける名前」と「既存宣言への参照」を区別する語法を持っていない。
`plan_lint.ts` は宣言名の実在を照合するので、**「実在した」が警告にならない**のがこの穴の形。

**(b) D-1 — 件数は当たり、場所が外れた**

plan D-1 は「`compProd_pi_map_pair_eq_of_update_invariant` は**同ファイル**
`compProd_pi_map_pair_eq` の strict generalization — direct 1 decl / 1 file、
transitive 12 decl / 2 file。**同ファイル内で完結するのでこちらだけ先に切る**のが安い」。

件数 (1 decl / 1 file) は正しい。場所が違った:

```
git grep -n 'compProd_pi_map_pair_eq\b' 083aceef~1 -- InformationTheory/
  → ChannelCoding/CodeToAmbient.lean:27,430                     (module doc + 定義)
  → MultipleAccess/TimeSharingConverse/Bridge.lean:737          (唯一の direct consumer)
```

**唯一の consumer は MAC 側の別ファイル**で、家系もディレクトリも違う。
影響は着手判断ではなく**畳み方**に出た: 特殊形を削除すると MAC 側を触ることになるので、
署名を逐語で保ったまま一般形の系として残す形になった (`git show 083aceef -- .../CodeToAmbient.lean`)。

**教訓**: 「1 decl / 1 file」という**数**は `dep_consumers.sh` が出すが、それが同ファイルかは
数からは出ない。plan は数だけを転記して「同ファイル内で完結する」を推論で足していた。
consumer 表に**ファイルパスを必ず併記させる**だけで消える誤り。

**(c) F-13 — 測定の切り詰めが実測を誤らせた**

plan は `isMarkovChain_map_comp` の呼び出しを 3 箇所と書いていた。突合側が打った実測は:

```bash
rg -n "isMarkovChain_map_comp|condMutualInfo_map_comp'" InformationTheory/ | head -20
```

出力はちょうど 20 行で切れ、`OuterBoundUV/Region.lean:308` の 3 本目が落ちた。
2 パターンの or 検索で、片方 (`condMutualInfo_map_comp'`) のヒットが大量にあったため、
目的の側が末尾に押し出されている。実装エージェントの再実測で **plan の 3 が正しかった**。

**教訓**: 「plan が誤っている」の判定に使う実測こそ**切り詰めてはいけない**。
`head` は出力量の制御であって検索条件ではないのに、両者が同じコマンドラインに同居している。
件数を確かめる意図なら `rg -c`、一覧を見る意図なら `head` 無し、と目的で分けるべきで、
**or 検索 + `head` は最も外しやすい組み合わせ**。この 1 件は「plan を疑う」側が
「plan が正しい」に覆った唯一の例でもある。

**(d) F-b — 「既存」が別命題だった**

plan F-b は private な `mutualInfo_le_add_condMutualInfo` の上流移動を挙げ、
「条件付き版が `OuterBoundUV/Gateway.lean:194` に public で既存 ⟹ 判断ログ 29 と同じ温床」
と書いていた。実物を並べると別命題である:

- 移設対象: `I(X;Y) ≤ I(X;Z) + I(X;Y|Z)` (`CondMutualInfo.lean` の現行位置)
- Gateway の `condMutualInfo_le_add_condMutualInfo`: `I(A;C|Z) ≤ I(B;C|Z) + I(A;C|(Z,B))`

右辺第 1 項の第 1 引数が違う。`Z` を定数に潰すと後者は `I(B;C) ≤` の形になり、
前者の `I(X;Z)` にはならない (前者は左辺の第 1 引数と条件付け変数の組、
後者は**挿入する変数**と出力の組)。移設は「重複解消」ではなく単なる可視性の引き上げとして実施した。

**教訓**: 「条件付き版が既存」という判定は**変数の役割を追わないと下せない**。
名前 (`condMutualInfo_le_add_condMutualInfo` と `mutualInfo_le_add_condMutualInfo`) は
接頭辞 1 語しか違わず、命題の形も「不等式 + 右辺 2 項」で一致するので、
**署名を並べるまでは同じに見える**。plan に書くべきは名前ではなく `#check` の出力。

**(e) T10b (6) — 列挙の取りこぼし**

ブリーフは over-claim している docstring を `Setup.lean` / `ErrorAnalysis.lean` の
`file:line` で列挙し、「行番号は実測し直すこと」と付記していた。実装エージェントの報告では
列挙に無い 2 箇所が見つかっている — `Setup.lean` の decl docstring 1 本と、
**`ErrorAnalysis.lean` の module doc**。着地した差分で over-claim 語彙を落とした行は
`git show 054f3994 -- <2 ファイル> | rg -c '^-.*(strong|degraded)'` で再導出できる。

取りこぼしの片方が **module doc** だったのが要点。ブリーフは decl docstring を
`file:line` で拾っており、ファイル冒頭の module doc は同じ over-claim をしていても
列挙の走査対象に入っていなかった。

**教訓**: 「行番号は実測し直すこと」という指示は**位置**の再測定しか要求しておらず、
**件数**の再測定を要求していない。列挙をブリーフに書いた時点で件数が固定されるので、
列挙形式のブリーフは「これで全部とは限らない」を明示するか、
列挙ではなく**検索条件**を渡すべき。加えて、docstring の走査は
**module doc を別枠で 1 行足さないと落ちる** — 4.3 と同じ「module doc は誰も見ていない」の系。

### 4.2 同名重複の下では「明示 import があるから意図した方を使えている」が成立しない

**症状**: `entropy_le_log_card` が 2 本あった。`InformationTheory.Shannon.entropy_le_log_card`
(`SlepianWolf/Basic.lean`) と `InformationTheory.Shannon.MaxEntropy.entropy_le_log_card`
(`MaxEntropy/Basic.lean`)。`#check` で並べると**型クラス前提まで一致**する:

```
@InformationTheory.Shannon.MaxEntropy.entropy_le_log_card : ∀ {α} [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] {Ω} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α), Measurable X → entropy μ X ≤ Real.log ↑(Fintype.card α)
@InformationTheory.Shannon.entropy_le_log_card : ∀ {Ω} [MeasurableSpace Ω] {α}
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → α), Measurable Xs → entropy μ Xs ≤ Real.log ↑(Fintype.card α)
```

違うのは**暗黙引数ブロックの順序と束縛変数名だけ**で、明示引数の位置も結論も同じ。
両方 `@[entry_point]` 付きで、どちらも `[propext, Classical.choice, Quot.sound]`。

**原因**: `ChannelCoding/ShannonTheorem.lean` は `import InformationTheory.Shannon.MaxEntropy.Basic`
を**明示的に**書いていた。しかしこのファイルの namespace は
`InformationTheory.Shannon.ChannelCoding` で `open ... InformationTheory.Shannon` があり、
`MaxEntropy` は open されていない。したがって無修飾の `entropy_le_log_card` は
`InformationTheory.Shannon.entropy_le_log_card` = **SlepianWolf 版**にしか解決しない。
SlepianWolf 版はこのファイルの推移 import 経由で入っていた:

```
ShannonTheorem ← ChannelCoding/Basic ← AEP/Basic ← AEP/Basic/Core ← SlepianWolf/Basic
```

**明示 import 1 ホップの側ではなく、推移 import 4 ホップの側が勝っていた**。

**抜け方**: 各 consumer の `import` + `namespace` + `open` を逐語で再現した probe ファイルを
scratchpad に書き、`#check @entropy_le_log_card` を打って実測した。束縛変数名
(`Xs` か `X` か) が識別子になる:

```lean
-- ProbeST.lean (ShannonTheorem の文脈を再現)
import InformationTheory.Shannon.MaxEntropy.Basic
...
namespace InformationTheory.Shannon.ChannelCoding
open MeasureTheory ProbabilityTheory InformationTheory.Shannon
#check @entropy_le_log_card    -- → (Xs : Ω → α) = SlepianWolf 版
```

**教訓**: 同名重複下では、`import` 行を読んでも `rg` を打っても
「この呼び出しがどちらに解決しているか」は出ない。**名前解決は import・namespace・open の
3 つ組の関数**なので、その 3 つを再現した probe を打つしかない。
そして重複を潰してしまえば、この種の静かな取り違えは**構造的に起こり得なくなる**
(統合後は無修飾の呼び出しが 0 になり、全 consumer が `MaxEntropy.` 修飾に揃った)。

補足: この重複は**すでに機械チェックに痕跡を残していた**。`docs/readme-theorems.txt` の
12 章の行が `entropy_le_log_card @ MaxEntropy/Basic` とパス曖昧性回避を強いられており、
`gen_readme_table.ts --check` は「名前が曖昧」を検出できていた。
検出できていなかったのは「**2 本が同じ定理である**」ことのほうで、統合後この行は
`entropy_le_log_card` に戻っている。**曖昧性の回避策が、重複の存在を隠す**。

### 4.3 移設・削除 leg は `lean_doc_lint` の strict ルールを素通りする

**症状**: 移設 / 分割 / 削除を含む leg で、module doc の要約・`## Main statements`・
節見出しが**連続して** stale になった。style ゲート側の commit 見出しがそのまま記録になっている:
`715605b7` (削除で陳腐化した union の docstring) / `6630a5ee` (移設先 docstring を基礎定義の文脈へ) /
`61971e9b` (一般混合が入った TimeShare の節見出し) / `cacc59d6` (昇格先 module doc の API 表面) /
`434f16fd` (移設で stale 化した module doc と節見出し) / `371dce85` (2 領域同居後の Region module doc) /
`43cd2d0c` (再符号化ファイルと MIChainRule の関係) / `4bc00e36` (分割で stale 化した cross-file 参照) /
`be0750b8` (CondMutualInfo の節見出し)。**9 leg 連続**で手作業の突き合わせが必要だった。

**原因**: `scripts/lean_doc_lint.ts` の strict ルールのうち存在を見るのは 2 本だけである
(`RULES` テーブル、`cls: "strict"`):

- `retired-decl-ref` — 散文が参照する宣言名が **HEAD に有るか**
- `dead-file-ref` — 散文が参照する file / module が**存在するか**

どちらも「その decl が**このファイルに**有るか」を見ない。移設は decl を消さないので、
移設元の module doc が旧宣言を宣伝し続けても、移設先の module doc が新参を宣伝しなくても、
リンタは何も言わない。実際 HEAD で `deno run -A scripts/lean_doc_lint.ts --check` は PASS する。

**教訓**: 現行の strict ルールは「**参照先が消えた**」を検出する設計で、
「**参照先が動いた**」は射程外。移設は decl 集合を変えずファイル割当だけを変える操作なので、
消滅ベースの検出は原理的に無力。足すべきは
「module doc の `## Main definitions` / `## Main statements` が名指す decl が
**そのファイルに実在するか**」の 1 本で、これは既存の decl 索引 (`facts.headDecls`) を
ファイル単位に持ち替えるだけで書ける。**移設 leg のたびに人間が読む**という現行の運用は、
9 leg 連続で発火した時点で自動化の閾値を超えている。

### 4.4 `retired-decl-ref` は修飾を末尾 segment だけで解決する

**症状**: `MaxEntropy/Basic.lean` の module doc が
`` `LoomisWhitney.entropy_le_log_image_card` `` と書いていた。`LoomisWhitney` という
**namespace は存在しない** (`rg -n 'namespace LoomisWhitney' InformationTheory/` が 0 件)。
`entropy_le_log_image_card` は `Shannon/LoomisWhitney.lean` という**ファイル**にあり、
namespace は `InformationTheory.Shannon`。style ゲート `939e3550` が
「`entropy_le_log_image_card` (`LoomisWhitney.lean`)」に直した。

**原因**: リンタの実装がそう書いてある (`scripts/lean_doc_lint.ts`, `retired-decl-ref`):

```ts
// 名前空間修飾された参照 (`InformationTheory.Shannon.foo`) は末尾 segment で解決する — DECL_RE が
// 集めるのは base name なので、修飾ごと引き合わせると全件 miss になる。
const base = t.split(".").pop()!;
if (facts.headDecls.has(base) || ...) continue;
```

`LoomisWhitney.entropy_le_log_image_card` → base は `entropy_le_log_image_card` → HEAD に実在 → 無警告。
**「定理名は実在するが namespace 修飾が間違っている」参照は構造的に検出できない**。

**教訓**: これはバグではなく明示的なトレードオフ (コメントが理由を書いている) だが、
**回避された誤りの種類**が記録されていない。修飾付き参照については
「末尾 segment が実在する」に加えて「**その修飾で実際に解決するか**」を確かめられる。
コストは修飾を namespace 索引と引き合わせる 1 段で、全件 miss にはならない。
4.2 と合わせると、**この家系の docstring は namespace 修飾を 2 通りの理由で間違えている** —
存在しない namespace を書く (本項) / 正しい namespace を省いて別の宣言に解決させる (4.2)。

### 4.5 「据え置き」を機械検証で裏づけた

**症状**: `#22` は `natIndex (X) (x) := Fintype.equivFin X x` を Mathlib の
`Encodable.encode` に寄せられるかの判断。判断基準を 3 点
(自作 def が消える / 型クラス前提が悪化しない / 行数が増えない) で先に固定して着手した。

**実測**: 差し替え版を実際に書いて `lake env lean` を通した結果、**文言上は 3 つとも通った**
(505 → 503 行 = −2。`encode` の字母が implicit instance 引数になるため使用 10 箇所すべてに
型注釈が要り、5 行が 100 字を超えて折り返す — その増加を差し引いてなお −2)。
それでも据え置いた。理由は基準が想定していなかった機構にある:

- 有限アルファベットは `Encodable` インスタンスを持たないので
  `attribute [local instance] Fintype.toEncodable` をファイル全体に導入する必要がある
- これは**noncomputable な任意選択インスタンス**で、順序の選び方は `Fintype.equivFin` と同じ任意
- Mathlib 内にこの形の実使用が 0 件 (→ 3.2)
- `Encodable` のデコーダは `Option` 値だが、再符号化のスロット補題は**全域の左逆**を要求する

つまり「自作 def が 1 本消える」の代わりに「ファイル全体のインスタンス解決が
noncomputable な任意選択を含むようになる」を払う交換で、**構造的な得がゼロ**。
判断は `9d16a21e` で docstring に残した:

```
`Encodable.encode` is the same map up to the arbitrary choice of an ordering, but a finite
alphabet carries no `Encodable` instance, and its decoder is `Option`-valued where the slot
lemmas of the re-encoding take a total left inverse.
```

**教訓**: 「差し替えない」を根拠づけるには、**差し替え版を実際に書いてコンパイルを通す**必要がある。
書かずに却下すると CLAUDE.md が禁じる「散文による資産の却下」になり、書いてしまえば
判断基準の文言が捕まえていなかった代償 (この場合はインスタンス解決への副作用) が見える。
逆に言えば、**事前に固定した判断基準は「通った」ことを結論にできない** —
3 つとも通ったうえで却下が正しかった。基準は却下の十分条件であって採用の十分条件ではない。

なお `#22` はブリーフの行番号・件数が実測と**完全に一致した** leg でもある
(宣言位置 2 箇所 / 使用 10 箇所 / module doc 位置 / ファイル外 consumer 0)。
4.1 の 5 件と並べると、外れたのはいずれも**過去の leg から転記された参照**で、
当該 leg で新たに測った参照は外れていない。ただし 4.1(c) は逆向きの反例で、
**新たに測ったほうが誤り、転記されたほうが正しかった** — 転記の鮮度と測定の正確さは別の軸で、
「転記だから疑う」は片方しか説明しない。

### 4.6 同一 namespace 内で同じ語が正反対を指していた

**症状**: MAC の `axis` 語彙が達成側と converse 側で反転していた。改名前の署名:

- `mac_axis1_achievable ... : MACAchievable W 0 R₂` — **ユーザー 1 が沈黙**、生きているのは `R₂`
- `mac_timesharing_converse_axis1 ...` — docstring は「converse for user 1 (`R₂ = 0`)」、
  **生きているのは `R₁`**

同じ `axis1` が、片方では「沈黙するユーザー番号」、もう片方では「生きている座標番号」。
両者は同一 namespace (`InformationTheory.Shannon`) にあり、`open` 1 つで同時に見える。
`#check` で達成側の結論が `MACAchievable W 0 R₂` と出たことで、反転しているのが達成側だと確定した。

**却下した案**: 達成側の数字を入れ替える (`mac_axis1_achievable` → `mac_axis2_achievable`)。
旧名が**両方とも生き残ったまま意味だけ入れ替わる**ので、外部の参照は
コンパイルを通ったまま逆の定理を指す。

**採った案**: `axis` 語彙を捨てて下付きに統一 (`mac_rate₂_achievable` / `mac_rate₁_achievable` /
`mac_timesharing_converse_rate₁` / `_rate₂`)。**旧名が完全に消えるので誤参照はコンパイルエラーになる**。

**教訓**: 意味が反転している名前の直し方は、**旧名を残さない**方向にしか安全解がない。
「番号の付け替え」は差分が最小に見えるが、リネームのなかで唯一
**静かに間違えられる**形。命名衝突の検出は `rg` で名前を数えても出ず、
**同じ語を使う宣言の署名を並べる**ことでしか出ない。

### 4.7 `lake env lean` は一部 linter に盲目 — 家系の既定手として全 leg の検証バーに入れた

先行 proof-log §4.5 が実測した性質 (`lake env lean` が沈黙するファイルに `lake build` が
`linter.flexible` / `linter.style.show` / `linter.unusedDecidableInType` を出す) を受け、
本 relay では**全 leg のブリーフの検証バーに `lake build InformationTheory` を明記**した。
実測でも `lake_build` 62 回 / `lake_env_lean` 61 回とほぼ 1:1 で走っている
(metrics の Bash 内訳)。

実際に拾えた例が `MIChainRule.lean` の 3 件 (`054f3994`):

- `show Xs (...) ω = ...` → `change ...` (`linter.style.show`)
- `convert IH' using 2 <;> rfl` → `convert IH' using 2` + `rfl` (`linter.flexible`)
- `omit [DecidableEq α] [DecidableEq β] in` → `omit [DecidableEq α] [Nonempty α] [DecidableEq β] in`

いずれも `lake env lean` の沈黙下で残っていたもの。

**教訓**: 先行 proof-log は代替として
`lake env lean -D linter.mathlibStandardSet=true -D linter.unusedFintypeInType=false <file>` を
提案していたが、本 relay が実際に採ったのは `lake build InformationTheory` のほうだった。
リファクタ relay では**触ったファイル以外にも波及する** (移設で下流の import が変わる) ので、
単ファイル検査ではフラグを揃えても射程が足りない。
**証明 leg はフラグ付き単ファイル / 移設 leg はフルビルド**、という使い分けが実測から出た形。

---

## 5. ボトルネックではなかったもの

- **honesty**。新規 `sorry` 0 / 署名の honesty 変更 0 なので `honesty-auditor` は 0 回起動。
  load-bearing hyp の誘惑が出る場面が構造的に存在しない (証明を書いていない)。
- **Mathlib 壁**。0 件。loogle は 7 クエリで 0-hit は 1 組だけ、しかもそれは
  設計判断の入力であって障害ではない (→ 3.1)。
- **新しい数学**。T7+T8 で `Bridge.lean` / `TimeShare.lean` に現れた補題 3 本
  (`mutualInfo_pair_out₁_eq_uvInfoJoint` / `uvInfoJoint_smul_add_smul` /
  `uvInfoJoint_uvTimeShareLaw`) はいずれも `MoreCapable.lean` からの移設で、
  新規に立てた命題ではない (`git show 083aceef~1:.../MoreCapable.lean | rg -n '<name>'`)。
  D-1 の系化も marginal の一致を挟んで一般形を 1 回 `rw` するだけで閉じている。
- **import 循環**。T3' の逆向き昇格は `Probability/` という下層へ抜くことで循環を作らずに済んだ
  (`InformationTheory/Probability/Mixture.lean` 新設)。
- **型検査 / universe**。改名と移設だけなので発火しない。
- **コンテキスト長**。全 leg をサブエージェントに委譲しており、オーケストレーター側の
  対象ファイル Edit / Write は 0 (metrics サマリー)。

---

## 6. 計測から見えたこと

数値は [metrics.md](../metrics/bc-followup-refactor.metrics.md) が SoT。3 点。

**(a) plan はホットスポットではなかった** — 先行 proof-log の逆。
`bc-lessnoisy-equality` では `bc-general-region-plan.md` の Edit 218 回がどの `.lean` よりも
多かった (同 proof-log §6(a))。本 relay では plan 系 5 ファイルの編集がすべて最終 leg
(`#21` = ターン `3ff10d46` / `e130a395`) に集約され、どのファイルも Lean 側のホットスポット
(`TimeSharingConverse/Assembly.lean` 17 / `TimeShare.lean` 16 / `TimeSharing.lean` 15) に届かない。
**leg ごとに plan 同期を挟むのではなく末尾で 1 回圧縮する**運用にすると、
plan のホットスポット性が消える。実際 plan は 603 → 542 行と**縮んだ**。

**(b) 「BC の後続作業」なのに編集ホットスポットは MAC 側だった**。
上位 3 ファイルのうち 2 本が `MultipleAccess/`。T3' の逆向き昇格と `#20` / `#25` が
すべて MAC を触ったためで、**家系境界は負債の所在と一致しない**。
plan の §後続作業 は BC の plan にしか無く、MAC 側にはその項目が立っていなかった。

**(c) `lake build` と `lake env lean` がほぼ同数** (62 : 61)。
移設・改名 leg では単ファイル検査だけでは足りないという 4.7 の判断が、
コマンド比率にそのまま出ている。証明 leg 中心の家系では
`lake env lean` が一方的に多いのが普通なので、**この比率自体が leg 種別の指標になる**。

---

## 7. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **module doc の名指し先が「そのファイルに」あるかの照合** — `lean_doc_lint` の decl 索引をファイル単位に持ち替えるだけ。現行 2 本の strict ルールは「消えた」しか見ない | 4.3。移設 / 分割 / 削除を含む **9 leg 連続**の手作業突合 |
| 高 | **plan の consumer 参照にファイルパスを必須にする** — 件数だけ転記させない | 4.1(b)。D-1 の畳み方の判断が着手後まで確定しなかった |
| 高 | **同名重複の検出 + 各 consumer の実解決先の実測** — 名前 → (import, namespace, open) 3 つ組ごとの解決先。`gen_readme_table.ts` は曖昧性を検出できるが「同じ定理である」は見ない | 4.2。`ShannonTheorem.lean` が明示 import の裏で別宣言を使っていた |
| 中 | **plan の名前参照に「新規に付ける名前 / 既存宣言への参照」の型を持たせる** — `plan_lint.ts` は実在を照合するので「実在した」が警告にならない | 4.1(a)。G-2 の対象取り違え |
| 中 | **`retired-decl-ref` の修飾検証** — 末尾 segment 一致に加えて「その修飾で解決するか」 | 4.4。存在しない namespace 修飾が module doc に残っていた |
| 中 | **or 検索と `head` の同居を警告する** — 件数目的なら `rg -c`、一覧目的なら切らない | 4.1(c)。plan を疑った側が誤っていた唯一の例 |
| 低 | **列挙形式のブリーフに「検索条件」を併記させる** — 位置の再測定だけでなく件数の再測定を要求する | 4.1(e) |
| 低 | **リファクタ leg の検証バーを `lake build` 側に倒す** — 移設は下流の import を変えるのでフラグ付き単ファイルでは射程不足 | 4.7 |

---

## 8. 補足

### 「機械チェックを通っている」が重複を隠していた

`entropy_le_log_card` の重複は `gen_readme_table.ts --check` に**すでに検出されていた** —
ただし「同じ名前の宣言が 2 つあるので曖昧」という形でだけ。
curation ファイルは `entropy_le_log_card @ MaxEntropy/Basic` とパス指定で曖昧性を解消し、
**その時点で `--check` は PASS になり、重複は恒久状態として固定された**。
統合後 (`b5c55683`) この行は `entropy_le_log_card` に戻っている。

曖昧性回避の記法が存在すると、曖昧性は「解決すべき問題」ではなく
「記法で吸収する仕様」になる。同じ構造は 4.4 (末尾 segment 解決) にもある —
どちらも**精度を落とす代わりに全件 miss を避ける**設計で、
落とした精度の側に何が入るかは記録されていない。

### 却下した案

- **`axis` の数字入れ替え** (4.6) — 差分は最小だが旧名が生き残る。
- **`natIndex` の `Encodable.encode` 差し替え** (4.5) — 判断基準 3 つを通ったうえで却下。
- **`compProd_pi_map_pair_eq` の削除** (4.1(b)) — 唯一の consumer が MAC 側なので、
  署名を逐語で保った系として残した。

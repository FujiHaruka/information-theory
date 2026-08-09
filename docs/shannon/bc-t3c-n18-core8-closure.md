# N18 — 単位 B の中核 8 の残り 2 段 (headline `isClosed_thm7Region`) を閉じにいく

**Parent**: [`bc-open-problem-t3c-plan.md`](bc-open-problem-t3c-plan.md) §5.1 (N18 起票ブロック) /
**配分決定の SoT** = 同 plan §7 判断ログ 13 (⚠ **本 md は複製しない**) /
**単位の SoT** = 子 plan [`bc-computable-region-formalization-plan.md`](bc-computable-region-formalization-plan.md)
§3.2 (単位 B の (i)–(iv) + 撤退) / §4 (設計軸 (a) 決着済・(b) 未決) / §6 撤退ライン **R-2** / **R-3** / **R-4** /
**前 leg の SoT** = [`bc-t3c-n17-unit-b.md`](bc-t3c-n17-unit-b.md) (自己申告) +
[`bc-t3c-n17-audit.md`](bc-t3c-n17-audit.md) (敵対的独立監査) + facts [`bc-facts.md`](bc-facts.md) `## N17 (T3c)` /
**出発点** = `InformationTheory/Shannon/BroadcastChannel/Thm7Region.lean` (**22 decl / `sorry` 2 本**) +
監査 probe `docs/shannon/probes/t3c-n17/audit-probes.lean` (**P1–P4 / N1**)

**leg 冒頭宣言 (N18)**: 側 = 形式化債務 / 動かすもの = 子 plan の単位 B の gateway atom (中核 8) の残り
2 段 (`ν` 段と headline `isClosed_thm7Region`) を閉じにいき、閉じないなら何が閉じないかを機械で名指した
状態にする。あわせて `thm7Region W ≠ ∅` を機械で当て、閉性が空虚に真でありうる穴を先に塞ぐ

> ⚠⚠ **本書の §0 と §1 は着手前に凍結されており、実行 leg / 監査は 1 文字も書き換えてはならない**
> (親 plan §4.4-2 の義務。r19 / r20 / r21 で確立した作法 = **事後に見立てを直して当てにいく経路を
> 構造的に塞ぐ**)。⚠ **見立ての当たり外れ / 反証条件の発火状況は §4 に別途書く** — **§0 / §1 は動かさず、
> 効きは着地側に書く**。
> **凍結の機械確認**: 起票 commit と現行の同区間 (`## 0.` 行から `## 2.` の直前まで) の md5 一致で見る。
> ⚠⚠ **空行を落として正規化してから md5 を取る** / ⚠⚠ **範囲の非空 (行数) を先に確認してから md5 を取る**
> — **範囲指定を誤ると空文字列どうしの偽 PASS になる** (r20 / N17 監査の実測)。
>
> ⚠⚠ **本 leg は §0 のゴールの Lean 側には届かない**。親 §6-5 は既に「**形式化債務は残る形式化枠 2 leg に
> 収まらない**」と判定済であり (親 §7 判断ログ 3 / facts N2-a)、⟹ **N18 でそこへ届く見込みは無い**。
> ⚠⚠ **本 leg の成果を「§0 に近づいた」と書かない** (親 §0.1-2)。⚠ **同時に「だから走らせる意味が無い」とも
> 書かない** — 走らせる意味は **中核 8 の未閉 2 段が何によって閉じないのかを機械で名指し、あわせて閉性が
> 空虚に真でありうる穴 (facts N17-g (6)(7)) を塞ぐこと**である。

---

## 0. 着手前の見立てと「締める / 緩める」の明記 (§4.4 の義務。⚠ 事後に書き換えない)

⚠ **本節は `Thm7Region.lean` を 1 行も書く前に書いた**。⚠⚠ **本節は `lake` を 1 度も走らせていない** —
反証は `rg` と **Mathlib / in-project のソースの逐語読み**の上で行った (⟹ **機械の判定は §3 に別途書く。
一致しなかったものは一致しなかったと書く**)。⚠ **見立ては当てにいくものではなく較正の材料である**。
⚠⚠ **本節に壁宣言は 1 つも無い** — 「中核 8 は Mathlib に無い」型の判断は **機械検証を経た実行 leg の
仕事**であり (CLAUDE.md の wall 宣言規約: loogle 0 件は必要条件であって十分条件ではない / 結論形での
二段検索 / in-project を `rg` / 名指しした候補は compiler に否定させる)、**起票段階では書かない**。

### 見立て A (**締める**) — preflight (`thm7Region W ≠ ∅`) は「名指された原子を 3 本並べる」仕事ではない

理由 3 点 (⚠ **どれも 2026-08-09 に現物の逐語を読んだ。壁判定ではない**):

1. **構成は `(kJ, TJ)` について一様でなければならない**。`thm7RegionOfInput`
   (`Thm7Region.lean:187`) は `⋂ (kJ) (TJ) (_ : IsMarkovKernel TJ)` であり、原点は**すべての補助受信者に
   対して**属さねばならない ⟹ 監査 probe **P4** の仮定文がまさにその形 (`∀ kJ TJ, IsMarkovKernel TJ → ∃ kv ν, …`)
   である。⚠ **1 つの `TJ` で法則を作っても原点の所属は出ない**。
2. **法則そのものが 13 因子の周囲空間上の測度である**。`IsThm7Law` の第 2–4 節は
   `ν.map … = (ν.map …) ⊗ₘ W` / `… ⊗ₘ TJ` / `ν.map … = p` であり、構成側は
   **`p ⊗ₘ W` と `⊗ₘ TJ` を合成したうえで `Thm7Ambient` の座標順へ並べ替える写像**を要する
   (⚠ **並べ替えは測度の等式であって定義の展開ではない**)。
3. **⚠⚠ 名指された原子の 1 本は、逐語で読むと形が合わない**。facts N17-g (7) が挙げる
   `iCondIndepFun.of_subsingleton` (Mathlib `Probability/Independence/Conditional.lean:913`) の仮定は
   **`[Subsingleton ι]` = 族の *添字型* が subsingleton** であり、`IsThm7Law` の第 1 節の添字は
   **`Fin 3` (3 つの補助三つ組)** である ⟹ **そのままでは当たらない**。⚠⚠ **これを「無い」と読まない** —
   必要な形は「値の型が subsingleton」側であり、⟹ **実行 leg は結論形で引き直し、名指した候補を
   compiler に否定させること** (CLAUDE.md「A dismissed asset must be dismissed by the compiler」)。

**着手前の 1 行反証 (§4.4-1 の義務。⚠ 締める側は着手前に反証を当てる)** = ⭐ **逆に縮む部分が 1 つ在る** —
`bcAuxAlphabet` は逐語で `abbrev bcAuxAlphabet (k : ℕ) : Type u := ULift.{u} (Fin (k + 1))`
(`MartonUnion.lean:67`) であり、**`kv i = 0` を選べば補助変数の型は 1 点型**である。しかも
`thm7Cap α i` は `Fintype.card α + 6` / `+ 1` (`Thm7Region.lean:167`) ゆえ **`0 < thm7Cap α i` は無条件**
⟹ **上限つき合併の内側に入れる**。⟹ **補助変数側は「定数値を取る」ではなく「型が 1 点である」形で入り、
25 スロットのうち補助変数を含む分はそこで落ちる公算がある**。
⟹ **A は「原子が足りない」の形では成り立たず、「(1) の一様性と (2) の座標並べ替えが残る」形で生きる**。

### 見立て B (**締める**) — headline は `ν` 段の系ではない ⟹ 費用には「ファイルに無い言明を新たに立てる」分が入る

理由 = `thm7Region W = ⋃ (p : ProbabilityMeasure α), thm7RegionOfInput W p` (`Thm7Region.lean:195`) で、
**固定 `p` のはしごは監査 probe N1 の逐語で落ちている**
(`failed to synthesize instance of type class AlexandrovDiscrete (ℝ × ℝ × ℝ)`) ⟹ 残る道は
**`p` について一様なグラフ `{(p, R) | R ∈ thm7RegionOfInput W p}` の閉性 + コンパクト添字の射影**である。
⟹ ⚠⚠ **既存の `isClosed_thm7RegionOfAuxReceiver` / `isClosed_thm7RegionOfInput` (どちらも固定 `p`) は
headline の経路上に無い** (監査 訂正 3 / 訂正 7 と同じ向き) ⟹ **headline を閉じるには、いま 22 decl の
どれでもない言明を新たに立てる必要がある**。

**着手前の 1 行反証 (§4.4-1 の義務)** = ⭐ **射影側の道具は Mathlib に在る** —
`isClosedMap_snd_of_compactSpace [CompactSpace X] : IsClosedMap (Prod.snd …)`
(`Mathlib/Topology/Maps/Proper/Basic.lean:337`) / 積空間版の `IsCompact.isClosed_image_restrict` と
`isClosedMap_restrict_of_compactSpace` (`Mathlib/Topology/IsClosedRestrict.lean:124` / `:134`) を逐語確認した
⟹ **B は「道具が無い」の形では成り立たない**。⟹ **B が主張するのは「無いのは *言明* の側」**である。
⚠ **起票では loogle を 1 度も引いていない** ⟹ **実行 leg は結論形 (`|- IsClosed (⋃ _, _)`) で引き直すこと**。

### 見立て C (**緩める**) — (i) の未閉項は `condMutualInfoPmf` の不在ではない (25 スロットは pmf 座標を経由しない路を持つ)

理由 = **25 スロットの内訳は無条件 7 本 / 条件つき 18 本** (`Thm7Region.lean:82-106` を数えた) だが、
どちらも **entropy 形へ落ちる in-project 資産が在る** (⚠ **2026-08-09 に逐語で読んだ**):

- `mutualInfo_toReal_eq_entropy_form` (`Shannon/MultipleAccess/Reconciliation.lean:45`) =
  `(mutualInfo μ f g).toReal = entropy μ f + entropy μ g - entropy μ (fun ω ↦ (f ω, g ω))`。
- `condMutualInfo_eq_condEntropy_sub_condEntropy` (`Shannon/Entropy.lean:200`、`@[entry_point]`) =
  `(condMutualInfo μ Xs Zo Yo).toReal = condEntropy μ Xs Yo - condEntropy μ Xs (fun ω ↦ (Yo ω, Zo ω))`。
- `entropy` の定義そのものが有限和である — `entropy μ Xs := ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})`
  (`Shannon/Bridge.lean:40`) ⟹ **スロットの連続性は `ν ↦ (ν.map f).real {x}` の連続性へ落ちる**。
- 弱位相側の原子も Mathlib に在る — `ProbabilityMeasure.continuous_testAgainstNN_eval (f : Ω →ᵇ ℝ≥0)`
  (`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean:314`)。

⟹ **facts N17-e が「無い」と名指した `condMutualInfoPmf` は、この路では 1 度も要らない**
(⚠⚠ **N17-e の実測が誤りだという主張ではない** — `condMutualInfoPmf` が 0 件であることは今も真である。
⚠ **主張は「未閉項がそこにあるとは限らない」の側**である)。

**殺す道具 (§4.4-2 の義務どおり着手前に決めた。⚠ 形式化 leg ゆえ §4.5 の道具 3 = 明示 witness の直接評価を
機械へ読み替える)** = **`lake env lean` に 1 本**。**条件つきスロット 1 本** (例: slot 4 =
`condMutualInfoReal ν (A (0,0)) Y (A (0,2))`) を上の 2 本で entropy 差へ書き換える `example` を書き、
**無出力**なら C は生存。**`[IsProbabilityMeasure ν]` / `MeasurableSingletonClass` / `DecidableEq` /
`Nonempty` の型クラス列が周囲空間の因子で揃わない**か、**`condEntropy` の引数の向きが合わない**なら **C は死ぬ**。
⚠ **「在る」は「そのまま使える」ではない**。⚠ **C は緩める側ゆえ §4.4 の非対称性が効く** — 外れると
**その見立ての上に leg を組んでから死ぬ**。

### 見立て D (**緩める**) — 補題側に要る位相 3 本は、既存宣言の署名を汚さずに証明の中で構成できる

理由 = N17 §3-(4) は「コンパクト性の道具は `TopologicalSpace` / `DiscreteTopology` / `BorelSpace` の 3 本を
**仮定として**要求する」ところまでを機械で確定させ、**§5-(5) で「証明の中で構成できるか」を未検証のまま
残した**。⟹ その構成路の各段が Mathlib に instance として在る (⚠ **2026-08-09 に逐語で読んだ**):

- `measurableSingleton_of_standardBorel [StandardBorelSpace α] : MeasurableSingletonClass α`
  (`Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:132`)。
- `MeasurableSingletonClass.toDiscreteMeasurableSpace [MeasurableSingletonClass α] [Countable α] :
  DiscreteMeasurableSpace α` (`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:551`)。
- `DiscreteMeasurableSpace.toBorelSpace [TopologicalSpace α] [DiscreteTopology α] [MeasurableSpace α]
  [DiscreteMeasurableSpace α] : BorelSpace α` (`Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean:659`)
  + `borel_eq_top_of_discrete` (同 `:59`)。
- **補助アルファベット側は letI すら要らない** — `Fin n` は `⊥` 位相と `DiscreteTopology` を**大域 instance**
  で持ち (`Mathlib/Topology/Order.lean:576` / `:577`)、`ULift` は位相を継承する
  (`Mathlib/Topology/Constructions.lean:70`)。

⟹ **`letI : TopologicalSpace α := ⊥` を α / β₁ / β₂ に置く数行で、補題の署名を 4 型クラスのまま保てる見込み**。

**殺す道具 (§4.4-2 の義務どおり着手前に決めた)** = **`lake env lean` に 1 本**。`isClosed_iUnion_thm7RegionOfLaw`
の本体の冒頭に `letI` を置き、`have : CompactSpace (ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂)) :=
inferInstance` を書いて**無出力**なら D は生存、**`failed to synthesize` が 1 件でも出たら D は死ぬ**。
⚠⚠ **焦点は 13 因子の積 / Pi 型で `BorelSpace` と `OpensMeasurableSpace` が合成されるか**である
(⚠ **`ProbabilityMeasure` の位相 instance は `variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]` の
下にある** — `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean:280` / `:289` の逐語)。
⚠ **局所 `letI` と大域 instance が混ざる形は facts N2-f が記録した「符号化の副作用」の近傍である**。

### ⚠ 併記する 3 点 (どれか 1 つだけを書かない)

1. ⚠⚠ **本 leg は形式化債務であって `Thm7 ⊋ C` の材料を出す leg ではない** — **どちらに転んでも出ない。
   排除もされない**。⚠ **レート領域の包含についても 1 文字も言わない**。
2. ⚠⚠ **§6-5 は既に「収まらない」と判定済**ゆえ **N18 で §0 の Lean 側には届かない** ⟹
   ⚠⚠ **成果を「§0 に近づいた」と書かない** (親 §0.1-2)。
3. ⚠ **同時に「だから走らせる意味が無い」とも書かない** — 意味は **未閉 2 段が何によって閉じないのかを
   機械で名指すこと**と、**閉性が空虚に真でありうる穴 (facts N17-g (6)(7)) を preflight で塞ぐこと**である。

---

## 1. 反証条件 (§4.4-2 の義務。⚠ 着手前に書いてある。事後に書き換えない)

### (a) 継承分 — ⚠⚠ **無い。ただし継承しない理由を書く**

⚠ **本 leg は継承した反証条件を 1 本も持たない**。前 leg (N17) の 3 本は**どれも対象が違う**:

- **N17 §1-(b) 1 (受け皿が 0 error に落ちない)** = **対象が消滅した**。受け皿は既に層 3 に在り
  `Thm7Region.lean` は 0 error である ⟹ **継承しない**。⚠ **「不発火」とも書かない** (評価しない)。
- **N17 §1-(b) 2 (中核 8 が 3 段のいずれかで止まる)** = **対象が「残り 2 段」に変わっている**
  (段は 5 つに割れ、3 本は既に `sorryAx`-free) ⟹ **継承ではなく下の新規 2 として書き直す**。
  ⚠ **N17 で発火済の条件を再利用して「再発火」と書かない**。
- **N17 §1-(b) 3 (既存宣言の署名変更を要求する)** = **対象が違う**。N17 の対象は**ファイル外の資産**
  (`mutualInfoReal` / `condMutualInfoReal`) だが、本 leg で危ないのは**同一ファイル内の 20 decl と 4 本の
  def** である ⟹ **継承ではなく下の新規 3 として書き直す**。
- 子 plan §6 の **R-2 / R-3 / R-4** は**反証条件ではなく撤退ライン**である ⟹ 継承ではなく**そのまま効く**
  (⚠ とくに **R-4 = 「`R₀=0` スライスの Π01 性を『従う』で埋めた記述を見つけたら即座に差し戻す」は
  判定ではなく禁止条項の違反**である)。

### (b) 新規 3 本 (⚠ **発火を判定する道具を条件ごとに名指す**。⚠⚠ 「うまくいかなかったら」型は不可)

1. **preflight (`thm7Region W ≠ ∅`) が閉じない / 逆に空が出る** ⟹ ⚠ **閉性の結末の読み方が変わる**。
   **条件文** = 次の 3 分岐のいずれかに落ちたとき発火する — **(i)** 原点 (または任意の 1 点) の所属を
   `lake env lean` が 0 error で受け取る宣言を書けない、**(ii)** 書けたが本体が `sorry` のまま残る、
   **(iii)** ⚠⚠ **`thm7Region W = ∅` が機械で出る**。
   **発火したときの処置** = **(i)(ii)** ⟹ **中核 8 の 2 段へは進んでよい**が、⚠⚠ **着地文書に
   「閉性は空虚に真でありうる」を明記し、preflight を未閉として名指す** (facts N17-g (7) の位置づけを
   動かさない)。**(iii)** ⟹ ⚠⚠ **その場で止める**。**空集合の閉性で `sorry` を消して「中核 8 が閉じた」と
   書くのは退化定義の悪用 (tier 5) である** ⟹ **2 本の `sorry` は残したまま、空であることの機械の出力を
   そのまま報告し、`thm7Region` の def の妥当性を独立に起票へ回す**。
   **判定に使う道具** = **`lake env lean <preflight を書いたファイル>`** (無出力 = clean) + **`#print axioms`**
   (⚠ **`sorryAx` を経由していれば (ii) である**)。⚠ **監査 probe P4 は仮定を置いた形なので、
   それをそのまま引いて「閉じた」と書かない**。

2. **材料 (i) (25 スロットの連続性) / (ii) (法則の集合の閉性) のいずれかが立たない** ⟹
   ⚠ **その段を `sorry` + `@residual(plan:bc-computable-region-formalization)` で残して type-check done で
   着地する** (子 §3.2 撤退 / R-2 の規定そのもの)。
   **条件文** = 見立て C の 1 行 (条件つきスロットの entropy 形への書き換え) と 見立て D の 1 行
   (`letI` 3 行 + `CompactSpace` の合成) を**先に機械へ掛けたうえで**なお
   `isClosed_iUnion_thm7RegionOfLaw` が `sorry` 無しで出ないとき発火する。
   ⚠⚠ **発火しても「壁」と書かない** — `@residual(wall:<name>)` を立てるには CLAUDE.md の wall 宣言規約
   (loogle 0 件は必要条件であって十分条件ではない / **結論形での二段検索** / **in-project を `rg`** /
   **名指しした候補は compiler に否定させる**) を**全部**通す必要があり、**本 leg でそこまで通せなければ
   `@residual(plan:bc-computable-region-formalization)` であって `@residual(wall:…)` ではない**
   (⚠ **子 §1.1 のとおり現時点で ⓓ (壁) は 0 件**)。
   **判定に使う道具** = **`lake env lean`** + **loogle の結論形検索** (`|- IsClosed _` / `|- Continuous _`。
   ⚠ **裸の識別子検索で終わらせない**) + **`rg` の in-project 検索** (⚠ **loogle は Mathlib しか見ない**)。

3. **headline を出すために既存宣言の署名か def を変える必要が生じる** ⟹ ⚠⚠ **def の変更はその場で止めて
   独立に起票へ回す** (子 §3.3 撤退 / **R-3 の精神**)。
   **条件文** = 次のいずれかが要ると判明したとき発火する — **(i)** 既存 20 decl のどれかの署名に型クラスや
   仮定を足す、**(ii)** `thm7Region` / `thm7RegionOfInput` / `thm7RegionOfAuxReceiver` / `thm7RegionOfLaw`
   の **def そのもの**を書き換える、**(iii)** `Thm7Ambient` の因子順や束縛子を変える。
   **発火したときの処置** = **(i)** ⟹ **既存宣言は変えず、新規宣言 (グラフ閉性の補題など) を足す方向で
   回避する** (⚠ **新規宣言も `sorry` + `@residual` で退出してよい**)。**(ii)(iii)** ⟹ ⚠⚠ **止める**。
   ⚠⚠ **とくに `(ν : Measure _)` の下線を 1 つ戻すと elaborate が終わらなくなる** (facts N2-c) ⟹
   **係数を合併の外で解決する def を消さない**。
   **判定に使う道具** = **`git diff -- InformationTheory/Shannon/BroadcastChannel/Thm7Region.lean`**
   (⚠ **既存宣言の署名行が 1 行でも diff に出たら発火とみなす。docstring 行と新規宣言の追加は除く**) +
   **`scripts/dep_consumers.sh`** (⚠ **def を触る前に消費者を数える**) + **`lake env lean`**。

### 1.1 出力型 (⚠ 着手前に固定する。⚠⚠ 判定そのものはここに書かない)

本 leg の出力は **3 軸**である (⚠ **1 つでも欠かさない。3 軸を 1 語に畳まない**):

- **(1) 非空性** — `原点 (または 1 点) の所属を構成した (sorryAx-free)` / `構成を sorry + @residual で残した` /
  ⚠⚠ `空であることが機械で出た` / `評価していない` の **4 値**。⚠ **preflight は step 0 として必須なので
  `評価していない` は本来取らない値である** — 取ったならその理由を書く。
- **(2) 材料 (i) と (ii) それぞれの結末** — 各々 `通った (sorryAx-free)` /
  `sorry + @residual(plan:bc-computable-region-formalization) で退出` / `評価していない` の **3 値**。
  ⚠⚠ **(i) と (ii) を 1 つに畳まない** / ⚠ **「評価していない」を「通らなかった」と書かない**。
- **(3) headline (`isClosed_thm7Region`) の結末** — `通った (0 sorry)` /
  `新規宣言を足したうえで sorry + @residual のまま` / `1 行も動かなかった (sorry のまま)` の **3 値**。
  ⚠ **「あと少し」「残るのは行数と配線だけ」型の言い回しで表現しない** (親 §4.1 軸 2 が名指しで禁じる tell)。

⚠⚠ **どの値の組であっても「単位 B が閉じた」と書かない** — **中核 9 (有界性) / 10 ((α) 合致) は
本 leg の対象外であり、触れば §5.2 のはみ出しになる**。
⚠ **新規 `sorry` + `@residual` を入れたら親 plan §4.3 / CLAUDE.md の 2 gate (honesty-auditor /
style-auditor) が要る** — ⚠ **自己監査にしない**。

### 1.2 ⚠ 禁止事項 (親 plan / 子 plan からの再掲。⚠⚠ 本 leg でも 1 つも緩めない)

- ⚠⚠ **成果を「§0 に近づいた」と書かない** (親 §0.1-2。**§6-5 は既に「収まらない」と判定済**)。
  ⚠ **同時に「だから走らせる意味が無い」とも書かない** (親 §7 判断ログ 12-(4))。
- ⚠⚠ **`thm7Region` を `Thm7(W)` と呼び替えない** (facts **N17-c**。**偏差は 2 つあり向きが逆** —
  述語の弱化は広げ、濃度上限は狭める)。
- ⚠⚠ **`R₀ = 0` スライスの Π01 性を「3 レート版から従う」で埋めない** (子 §4-b / **R-4 = 判定ではなく
  禁止条項**。⚠ **半計算可能性は超平面との交わりで保たれるとは限らない**)。
- ⚠⚠ **hypothesis に証明の核を担わせて `sorry` を消すのは禁止** (`*Hypothesis` バンドル / `:True` slot /
  退化定義の悪用 / name laundering)。**唯一の退出路は `sorry` + `@residual(plan:…)` で、署名は証明したい形の
  まま**である。⚠ **`sorryAx`-free は必要条件であって十分条件ではない — 署名走査を併せる**。
- ⚠⚠ **空集合ゆえの閉性で `sorry` を消さない** (反証条件 1-(iii)。**退化定義の悪用 = tier 5**)。
- ⚠ **`@residual(wall:…)` を安易に立てない** — CLAUDE.md の wall 宣言規約を全部通していないなら分類は
  `plan:` である (子 §1.1 のとおり ⓓ は 0 件)。
- ⚠ **`Thm7 ⊋ C` の材料について何も主張しない / `Thm7 ⊄ Thm8` と書かない / `R ∈ Thm7` と書かない /
  「あと少し」「残るのは行数と配線だけ」型の言い回しを使わない** (親 §1 / §3.1 / §4.1 軸 2)。
- ⚠ **既存宣言の署名を先回りで変えない** (子 §3.3 撤退 / 反証条件 3。⚠ **N17 の教訓 = 回避は
  「昇格先の束縛子を既存宣言の形へ設計し直す第 3 の道」だった**)。
- ⚠ **`(ν : Measure _)` の下線を 1 つ戻すと elaborate が終わらなくなる** (facts **N2-c**) ⟹
  **係数を合併の外で解決する def を消さない**。
- ⚠ **型検査が通ったことを「段が軽い」と読まない** (facts **N2-d** = 監査自身が偽の命題をコンパイラに
  黙って通させた実例) ⟹ **型は実効性・一様性の脱落を守らない**。
- ⚠ **`import Mathlib` を書かない**。⚠ **新規ファイルを足したら `InformationTheory.lean` に import 行を
  追記する** (子 §5)。

---

## 2. 実施したこと

**触った file** = `InformationTheory/Shannon/BroadcastChannel/Thm7Region.lean` (**22 decl → 38 decl**、
`sorry` は **2 本のまま**) + 新規 probe 4 本 (`docs/shannon/probes/t3c-n18/`)。
commit = `c4ab66a6` (preflight + 殺す 1 行) / `8d4dd999` (材料 (i) の原子 + probe)。
⚠ **既存 20 decl の署名は 1 行も動かしていない** (§3-(6))。
⚠⚠ **本節の 38 decl は着地時点の数である** — **style gate が新規 1 本を in-repo 重複として削除したので
現況は 37 decl** (commit `a60219e3`。⚠ **削除されたのは下の (b) の `mutualInfo_eq_zero_of_ae_const`** で、
`sorry` は 2 本のまま。詳細 = §5-(9))。

**(a) step 0 — preflight を宣言として立てて閉じた** — `thm7Region_nonempty` (`@[entry_point]`) と
`origin_mem_thm7Region`。⚠⚠ **監査 probe P4 の仮定文をそのまま引かず、その仮定を構成した**。
機構は 4 つ:

1. **入力法則を 1 点測度に取る** (`Measure.dirac x₀`、`x₀ : α` は `Nonempty α` から)。
   ⟹ スロット 14 / 15 / 16 / 21–24 (X を第 1 引数に持つ 7 本) が落ちる。
2. **⭐ 起票 §0-A の 1 行反証をそのまま使った** — `kv i = 0` を選ぶと補助変数の型
   `bcAuxAlphabet 0 = ULift (Fin 1)` が 1 点型 ⟹ スロット 0–13 / 17–20 (補助変数を第 1 引数に持つ
   18 本) が落ちる。`0 < thm7Cap α i` は `simp only [thm7Cap]; split <;> omega` の 1 行。
3. **法則そのもの** = `thm7DegenerateLaw W TJ x₀ := ((dirac x₀ ⊗ₘ W) ⊗ₘ TJ).map e`、
   `e` は 13 因子への埋め込み。⚠ **起票 §0-A-(2) が「測度の等式であって定義の展開ではない」と
   予告した座標並べ替えは、実際には 3 本とも `rfl` で通った** (§4.3)。
4. **`IsThm7Law` の第 1 節 (条件つき独立性)** は自前で建てた
   (`iCondIndepFun_of_subsingleton_codomain`、**25 行**)。⚠ **起票 §0-A-(3) の名指しは正しかった** —
   Mathlib の `iCondIndepFun.of_subsingleton` は `[Subsingleton ι]` = *添字型* であり `Fin 3` には
   当たらない。必要なのは *値の型* が subsingleton の版で、`iCondIndepFun_iff_condExp_inter_preimage_eq_mul`
   から場合分け 2 本 (`sets` が全点を含むか / 含まない i が在るか) で作った。

**(b) スロット消滅の道具を 3 本自前で建てた** — `ae_eq_const_of_map_eq_dirac` /
`mutualInfo_eq_zero_of_ae_const` / `condMutualInfo_eq_zero_of_ae_const`。
⭐ **条件つき版は `IsMarkovChain` を経由せずに済んだ** — `mutualInfo_chain_rule` を
**引数を入れ替えて** (`μ Yo Xs Zc`) 当て、両辺の無条件項が 0 になることから `zero_add` で消す形。
⟹ `condDistrib` の一意性論法は 1 行も要らなかった。
⚠⚠ **「3 本自前」は誤りだった** — **`mutualInfo_eq_zero_of_ae_const` は既存の public 定理の再宣言である**
(`InformationTheory/Shannon/MutualInfoFiniteRange.lean:63`。⚠ **既存の方が仮定が厳密に弱い**) ⟹
**自前は 2 本**であり、⚠ **本節の残る 2 本についても「無い」ことを本 leg は結論形で引き直していない**
(⚠ **`iCondIndepFun_of_subsingleton_codomain` だけは compiler に否定させたうえでの自前建てである**。§4.3 A-(3))。
詳細と解消 = §5-(9)。
⚠ **`ae_eq_const_of_map_eq_dirac` を「18 スロットを消した実質」と読まない** — **この補題の仮定は確率測度の
下で結論と論理的に同値**であり (⚠ **循環ではない** — 型が異なり body は 5 行の実証である)、
**表現の取り替えであって強化ではない**。実質を担うのは `thm7DegenerateLaw_map_input`
(`Measure.fst_compProd` 2 段) の側である。

**(c) 見立て C の「殺す 1 行」を機械へ掛けた** (`probes/t3c-n18/kill-lines.lean`) — 生存 (§4.3)。

**(d) 見立て D の「殺す 1 行」を機械へ掛けた** (同 file) — 生存だが**起票が名指していない条件が 2 つ
出た** (§4.3)。

**(e) 材料 (i) の原子を閉じて昇格させた** (`continuous_measureReal_of_discrete` /
`continuous_entropy_of_discrete`、`Thm7Region.lean` の新 section `WeakContinuity`)。
⟹ **スロット 2 形 (無条件 slot 0 / 条件つき slot 4) の弱位相連続性を probe で機械確認**
(`probes/t3c-n18/continuity.lean`)。⚠ **残り 23 スロットは機械に掛けていない** (§5-(2))。

**(f) 材料 (ii) は第 4 節だけ閉じた** (同 probe) — `{ν | ν.map X = p}` の閉性。
⚠ **第 1–3 節は評価していない** (§5-(3))。

**(g) `isClosed_iUnion_thm7RegionOfLaw` の docstring を 3 行差し替えた** — 旧文の
「pmf への通過が未閉項」は (e) が機械で覆したため。⚠ **`@residual` タグは 1 文字も動かしていない**。

## 3. 機械検証の結果

⚠ **以下はすべて機械の出力である。散文の印象は入れていない**。

**(1) 対象 file** — `lake env lean InformationTheory/Shannon/BroadcastChannel/Thm7Region.lean` の
出力は **warning 2 件のみ / error 0**:

```
Thm7Region.lean:255:6: warning: declaration uses `sorry`
Thm7Region.lean:283:8: warning: declaration uses `sorry`
```

⚠⚠ **「warning 2 件のみ」は道具相対である** — `lake build InformationTheory.Shannon.BroadcastChannel.Thm7Region`
では **本 leg が入れた 3 件目**が出た (`The \`show\` tactic should only be used to indicate intermediate
goal states` = `linter.style.show`、`continuous_measureReal_of_discrete` の中)。⚠ **honesty ではなく
style gate の対象**である ⟹ ⭐ **style gate が `show` を `change` へ差し替えて消滅済**
(現況の `lake build` の warning は **`sorry` 2 件 + `linter.style.header` の `Copyright too short!` のみ**で、
⚠ **後者は project 全体の既存パターンであり本 leg とは無関係**)。

**(2) probe 4 本** — いずれも **error 0**:
`probes/t3c-n18/preflight.lean` / `kill-lines.lean` / `continuity.lean` / `axioms.lean`。

**(3) preflight を組む途中で落ちた逐語** (⚠ **不発火が無条件でないことの根拠**):

```
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  ∀ (i : Fin 3), Subsingleton ((i_1 : Fin 3) → bcAuxAlphabet ((fun x => 0) (i, i_1)))
```

原因 = **`Subsingleton (ULift (Fin (0+1)))` が instance 解決に乗らない** (`Fin 1` 版は乗る)。
処置 = `instSubsingletonBcAuxAlphabetZero` を 1 本置いた (2 行)。

**(4) 見立て C の殺す 1 行** — **無出力 (生存)**。条件つき slot 4 =
`condMutualInfo_eq_condEntropy_sub_condEntropy` で、無条件 slot 0 =
`mutualInfo_toReal_eq_entropy_form` で、いずれも `(by fun_prop)` 3 本で当たった。
⟹ **型クラス列は周囲空間の因子で揃い、`condEntropy` の引数の向きも合った**。
⚠ **`condMutualInfoPmf` は本 leg で 1 度も要らなかった** — `rg -c "condMutualInfoPmf"
InformationTheory/` は **0 件のまま** (facts N17-e の実測は今も真)。

**(5) 見立て D の殺す 1 行** — **生存。ただし起票が名指していない条件が 2 つ出た** (逐語):

```
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  TopologicalSpace (ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂))
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  CompactSpace (ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂))
```

- **条件 1** — `CompactSpace (ProbabilityMeasure _)` の instance は
  **`Mathlib.MeasureTheory.Measure.Prokhorov` に在り、`Thm7Region.lean` の import 閉包の外**である。
- **条件 2** — 13 因子側の instance 3 本 (`OpensMeasurableSpace` / `BorelSpace` / `CompactSpace`)
  を `haveI` で**先に持ち上げないと入れ子の探索が届かない**。⚠ `synthInstance.maxSize 2000` +
  `synthInstance.maxHeartbeats 4000000` に上げても届かない (機械で確認)。持ち上げれば **無出力**。
- ⚠ **起票 §0-D が焦点と名指した「13 因子の積 / Pi 型で `BorelSpace` と `OpensMeasurableSpace` が
  合成されるか」は合成される** (どちらも `inferInstance` 1 本)。落ちるのは合成そのものではなく
  **入れ子の探索の到達**である。

**(6) 既存署名の非改変** — `git diff --unified=0 c4ab66a6~1 -- <対象 file>` の削除行は
**docstring 散文 3 行のみ** (§2-(g))。⚠ **既存宣言の署名行は 1 行も削除されていない**
(起票 §1-(b) 3 の判定道具そのもの。docstring 行の除外も同条の規定どおり)。
`git diff --name-only HEAD~2 HEAD` = 対象 file 1 本 + probe 4 本。

**(7) `#print axioms`** (`probes/t3c-n18/axioms.lean`、19 宣言に当てた):

| 宣言 | 結果 |
|---|---|
| `thm7Region_nonempty` / `origin_mem_thm7Region` | **sorryAx-free** |
| `thm7DegenerateLaw` / `_map_input` / `_map_outputs` / `_map_full` / `_isThm7Law` | **sorryAx-free** |
| `thm7Slots_thm7DegenerateLaw` | **sorryAx-free** |
| `iCondIndepFun_of_subsingleton_codomain` | **sorryAx-free** |
| `mutualInfo_eq_zero_of_ae_const` / `condMutualInfo_eq_zero_of_ae_const` / `ae_eq_const_of_map_eq_dirac` | **sorryAx-free** |
| `isClosed_setOf_inThm7` / `isClosed_thm7RegionOfLaw` / `finite_setOf_lt_thm7Cap` | **sorryAx-free** |
| `isClosed_iUnion_thm7RegionOfLaw` / `isClosed_thm7RegionOfAuxReceiver` / `isClosed_thm7RegionOfInput` / `isClosed_thm7Region` | `sorryAx` |

⚠ **`sorryAx`-free は必要条件であって十分条件ではない** ⟹ **署名走査を併せた**: 新規 16 宣言の仮定は
すべて **データ引数か regularity の instance 引数** (`[IsMarkovKernel W]` / `[IsMarkovKernel TJ]` /
`[IsProbabilityMeasure μ]` / `[Fintype]` / `[StandardBorelSpace]` / `[Subsingleton (β i)]`) であり、
**核を担う hypothesis は 1 本も無い**。⚠⚠ **ただし `[IsMarkovKernel W]` は閉性 2 本が要求していない
仮定である** — §5-(1) に別途書く。

**(8) `scripts/sig_view.ts`** — `--names` = **38 decl / 2 with sorry**、`--sorry` =
`isClosed_iUnion_thm7RegionOfLaw` (L255) と `isClosed_thm7Region` (L283)、
どちらも `@residual(plan:bc-computable-region-formalization)`。
`rg -c "@residual" <対象 file>` = **2**。
⚠ **監査と style gate の後の現況は 37 decl / 2 with sorry** (L256 と L288、`@residual` は **2** のまま。
⚠ **行番号が動いたのは監査が docstring を 3 か所補ったため**)。

**(9) code-surface の機械層** — `deno run -A scripts/lean_doc_lint.ts <対象 file>` =
**strict 10 規則 / ratchet 4 規則すべて 0 件**。file は **529 行** (1500 行の分割閾値の内)。

**(10) 結論形での loogle 引き直し** (起票 §1-(b) 2 が judgement の道具として名指した検索):
`|- IsClosed (Set.iUnion _)` = **7 件**。内訳 = 有限 / 局所有限添字が 4 本
(`isClosed_iUnion_of_finite` / `Set.Finite.isClosed_biUnion` / `isClosed_biUnion_finset` /
`LocallyFinite.isClosed_iUnion`)、`Topology.AlexandrovDiscrete` の 2 本
(`isClosed_iUnion` / `isClosed_iUnion₂` = **監査 probe N1 が落ちた先そのもの**)、無関係 1 本。
⟹ **一般の添字の合併に当たる補題は無く、`ν` 段も headline も「引けば出る」形ではない**。
⚠⚠ **これは壁宣言ではない** — CLAUDE.md の wall 宣言規約を全部通していないので分類は `plan:` である。
`Continuous (fun _ => Measure.compProd _ _)` = **0 件**、
`MeasureTheory.ProbabilityMeasure, ProbabilityTheory.Kernel, Continuous` = **0 件**、
in-project の `rg` も 0 件 ⟹ **`μ ↦ μ ⊗ₘ TJ` の弱位相連続性は在庫に無い** (§5-(3))。

## 4. 判定 — 見立ての較正と反証条件の発火状況 (⚠⚠ §0 / §1 は 1 文字も書き換えていない)

**凍結の機械確認**: `awk '/^## 0\./,/^## 2\./' … | sed '$d' | grep -v '^[[:space:]]*$' | md5` =
**186 行 / `8e5b0ff16213479aecfd54cb69107fd0`** (起票時の期待値と一致)。

### 4.1 反証条件の発火 (⚠ 3 本それぞれについて明記する)

- **反証条件 1 (preflight が閉じない / 逆に空が出る)** = ⚠ **不発火**。
  **(i)(ii)(iii) のどれにも落ちなかった** — 原点の所属は `origin_mem_thm7Region` として 0 error で
  受け取られ、本体に `sorry` は無く (§3-(7) で `sorryAx`-free)、`thm7Region W = ∅` は出ていない。
  ⚠⚠ **ただし無条件の不発火ではない**。理由 2 点:
  **(a)** 途中で instance 解決が 1 度落ちている (§3-(3) の逐語) —
  「1 点型なのだから subsingleton は自明」は成り立たず、instance を 1 本置く必要があった。
  **(b)** ⚠⚠ **`[IsMarkovKernel W]` を足している** — 閉性 2 本は `W : BCChannel α β₁ β₂`
  (= 一般の `Kernel`) を取るので、**非空性は閉性より狭い仮定の下でしか言えていない** (§5-(1))。
- **反証条件 2 (材料 (i) / (ii) のいずれかが立たない)** = ⚠⚠ **発火**。
  ⭐ **条件文が要求したとおり、見立て C の 1 行と見立て D の 1 行を先に機械へ掛けたうえでの発火である**
  (§3-(4) / §3-(5))。処置は規定どおり **`sorry` + `@residual(plan:bc-computable-region-formalization)`
  を 2 本、署名は証明したい形のまま**で残した (新規に立てた `sorry` は 0 本 = 既存 2 本の据え置き)。
  ⚠⚠ **壁とは書かない** — §3-(10) の結論形検索は引いたが、CLAUDE.md の wall 宣言規約を全部
  通していない ⟹ 分類は `plan:` である。
- **反証条件 3 (既存宣言の署名か def を変える必要が生じる)** = ⚠ **不発火**。
  **(i)(ii)(iii) のどれも要らなかった**。§3-(6) の `git diff` で削除行は docstring 散文 3 行のみ。
  ⭐ **回避に使った手は「新規宣言を足す」だけで、既存 def への手当ては 0 だった** —
  非空性は新 section 2 本 (`WeakContinuity` / `Nonemptiness`) を足すことで、
  材料 (i)/(ii) の機械確認は **probe 側の `example`** で行った。
  ⚠ **`(ν : Measure _)` の下線を戻す形 (facts N2-c) には 1 度も触れていない**。

### 4.2 段ごとの結末 (⚠ 段を 1 語に畳まない)

| 段 | 結末 | 根拠 |
|---|---|---|
| **preflight** (`thm7Region W ≠ ∅`) | ⭐ **構成した (sorryAx-free)** | `thm7Region_nonempty` / `origin_mem_thm7Region`。⚠ `[IsMarkovKernel W]` つき。⚠ **witness は原点 1 点ではない** — スロットが全て 0 のとき `InThm7 0 (0, -t, -t)` は **`0 ≤ t` で成り立つ** (監査 probe **A5** の 2 本目。⚠ **スロットベクトル上の算術のみ**)。⚠⚠ **これは領域の上界方向についての主張ではない** (中核 9 には 1 文字も触れていない) |
| **ファイバ** (`thm7RegionOfLaw ν` が閉集合) | **通っている (N17 で既済、本 leg で変更なし)** | `isClosed_thm7RegionOfLaw` |
| **内側 `kv` 段** (有限合併) | **通っている (N17 で既済、本 leg で変更なし)** | `finite_setOf_lt_thm7Cap` + `Set.Finite.isClosed_biUnion` |
| **材料 (i)** (25 スロットの弱位相連続性) | ⚠ **`sorry` + `@residual(plan:bc-computable-region-formalization)` で退出**。⭐ **ただし原子は閉じた** | `continuous_entropy_of_discrete` (in-tree、sorryAx-free) + probe で **2/25 スロット**を `Continuous` まで機械確認。⚠ **残り 23 は未検証** |
| **材料 (ii)** (法則の集合の閉性) | ⚠ **`sorry` + `@residual(plan:bc-computable-region-formalization)` で退出**。⚠ **第 4 節のみ probe で閉じた** | `IsThm7Law` 第 4 節 = probe で `IsClosed` を機械確認。**第 1–3 節は評価していない** |
| **内側 `ν` 段** (法則の合併) | ⚠ **`sorry` + `@residual(plan:bc-computable-region-formalization)`** | `isClosed_iUnion_thm7RegionOfLaw` (L255) |
| **中間 `⋂_{kJ,T_J}` 段** | **通っている (N17 で既済、本 leg で変更なし)** | `isClosed_thm7RegionOfInput` (⚠ `ν` 段の `sorry` を経由する配線) |
| **外側 `⋃_p` 段** (= headline) | ⚠⚠ **1 行も動かなかった (`sorry` のまま)** | `isClosed_thm7Region` (L283)。⚠ **起票 §0-B が名指した「`p` について一様なグラフ」の宣言は 1 本も立てていない** |

### 4.3 見立て 4 本の較正 (⚠ 当てにいくものではない)

- **見立て A (締める)** = **生きたが、内訳は 3 点のうち 2 点が外れた**。
  **(1) 一様性**は当たり — 原点の所属は `∀ kJ TJ, IsMarkovKernel TJ → …` の形を実際に構成する
  必要があり、1 つの `TJ` では出なかった。
  ⚠ **(2) 座標並べ替えは外れた** — 「測度の等式であって定義の展開ではない」と予告されたが、
  **3 本の周辺分布補題はいずれも合成が `rfl` に落ち、測度レベルの並べ替え論法は 1 行も要らなかった**
  (埋め込み `e` を先に固定したので射影との合成が定義的に一致する)。
  ⭐ **(3) は当たり、しかも「無い」側だった** — 値の型が subsingleton の版は Mathlib に無く、
  自前で **25 行**建てた。⚠ **compiler に否定させたうえでの自前建てである** (§3-(3) の逐語)。
  ⭐ **A の ⭐ (1 行反証) は決定的に当たった** — `kv i = 0` で補助変数の型が 1 点になる筋が、
  18 スロットの消滅と第 1 節の両方を同時に与えた。
  ⟹ **A は「費用が名指した原子を並べるより高い」の形では生き、「並べ替えが要る」の形では死んだ**。
- **見立て B (締める)** = ⚠ **本 leg では検証していない部分が残る**。
  **「既存の固定 `p` の 2 本は headline の経路上に無い」は動かしていない** (§4.2 の headline 行) が、
  ⚠⚠ **「新たに立てる言明」を 1 本も立てていないので、B の費用の見立ては当たりも外れもしていない**。
  ⭐ **B が要求した結論形の引き直しは実行した** (§3-(10)) — 7 件はいずれも有限 / 局所有限 /
  Alexandrov 系で、**N1 が落ちた先を含む** ⟹ **B の「無いのは *言明* の側」は少なくとも
  「合併補題の側には無い」形で機械に支持された**。⚠ **射影側の道具 (`isClosedMap_snd_of_compactSpace`
  ほか) は 1 度も使っていない**。
- **見立て C (緩める)** = ⭐ **生存。しかも予告より強く当たった**。
  25 スロットが entropy 形へ落ちることは 2 形とも `(by fun_prop)` で通り (§3-(4))、
  ⭐ **さらに `condEntropy` を `entropy_pair_eq_entropy_add_condEntropy` で entropy の差へ潰せたので、
  条件つきスロットも「4 本の entropy」まで落ちた** ⟹ **材料 (i) の全体が
  `ν ↦ entropy ν f` の連続性 1 本に集約された**。⚠ **C は緩める側なので、この当たりは
  §4.4 の非対称性の下では「安く済んだ」ではなく「外れていたら高くついた賭けに勝った」である**。
  ⚠ **`condMutualInfoPmf` は 1 度も要らなかった** (§3-(4))。
  ⚠⚠ **本 leg の較正は検証範囲を過小に申告していた** — **機械に掛けた 2 スロット (slot 0 / slot 4) は
  どちらも α 値の観測量を含まず、構造的に一番易しい 2 本である**。⭐ **監査が構造的に最も重い形
  (α 値の観測量 + 対条件つき = slot 15 形) を独立に閉じた** — `condMutualInfo_eq_condEntropy_sub_condEntropy`
  で条件つき entropy の差へ (`(by fun_prop)` 3 本)、`entropy_pair_eq_entropy_add_condEntropy` で 4 本の
  entropy へ、原子 `continuous_entropy_of_discrete` は **対値の観測量も覆う** (`hf.prodMk hg`) ⟹
  ⭐ **追加の instance 持ち上げは 1 本も要らなかった** (`classical` も `MeasurableSingletonClass α` の
  `haveI` も不要であることを機械で確認) ⟹ **C は本 leg が測った範囲より広い範囲で機械に支持される**。
  ⚠ **スロットの形は 4 つある** — **(a)** 補助変数どうし / 出力の無条件 (slot 0 等) / **(b)** α 値の無条件
  (slot 14) / **(c)** 補助変数の単変数条件つき (slot 4 等) / **(d)** α 値 + 対条件つき (slot 15/16/21–24)
  ⟹ **本 leg が測ったのは (a)(c)、監査が測ったのは (d)** で、⚠⚠ **(b) は誰も測っていない**
  (⚠ **(b) は 4 形のうち最も軽い**)。⚠ **緩める側の当たりであることは変わらない**。
- **見立て D (緩める)** = ⚠ **生存だが訂正つき**。3 本の型クラスは既存署名を汚さずに
  **証明の中で構成できた** (§3-(5)) が、⚠⚠ **起票が名指していない条件が 2 つ出た** —
  **(a) `CompactSpace (ProbabilityMeasure _)` の instance が import 閉包の外に在る**、
  **(b) 13 因子側の instance 3 本を手で持ち上げないと入れ子の探索が届かない**
  (`maxSize` / `maxHeartbeats` を上げても届かない)。
  ⚠ **D が焦点と名指した `BorelSpace` / `OpensMeasurableSpace` の合成そのものは通った** ⟹
  **焦点の当て先が 1 つずれていた**。⚠ **緩める側の見立てが「条件つきで生存」に着地した形である**。

### 4.4 出力型 (起票 §1.1 が固定した 3 軸。⚠ 1 語に畳まない)

- **(1) 非空性** = ⭐ **原点 (または 1 点) の所属を構成した (sorryAx-free)**。
  ⚠ **ただし `[IsMarkovKernel W]` を仮定した形である** (閉性 2 本はこれを要求していない) ⟹ §5-(1)。
  ⚠⚠ **本 leg はこの結末をモジュール docstring で偽の理由節つきに書いていた** — `## Main statements` の
  「`thm7Region_nonempty` — the region is inhabited, **so its closedness is not a statement about the
  empty set**」は、**閉性 2 本が `[IsMarkovKernel W]` を要求しない**ため一般の `W` では成り立たない
  (反例 = §5-(1))。⟹ ⭐ **コードが SoT ゆえ監査が当該行を修正済**である。
  ⚠ **非空性そのものは動いていない — 動いたのは「それが閉性について何を言うか」の側だけ**である。
- **(2) 材料 (i)** = ⚠ **`sorry` + `@residual(plan:bc-computable-region-formalization)` で退出**
  (受け皿は `isClosed_iUnion_thm7RegionOfLaw` の既存 `sorry`)。
  ⚠ **「通った」とは書かない** — 25 スロット全部を `Continuous` として述べる宣言は無く、
  機械に掛けたのは **2 形 / 2 本**である。⭐ **原子 `continuous_entropy_of_discrete` は in-tree で
  sorryAx-free**。
- **(2) 材料 (ii)** = ⚠ **`sorry` + `@residual(plan:bc-computable-region-formalization)` で退出**
  (同じ受け皿)。⚠ **`IsThm7Law` 第 4 節のみ probe で `IsClosed` を機械確認**、
  ⚠⚠ **第 1 節 (条件つき独立性) / 第 2–3 節 (`⊗ₘ` 等式) は評価していない**。
  ⚠ **(i) と (ii) は同じ受け皿を共有しているが、結末の内訳は上のとおり別である**。
- **(3) headline (`isClosed_thm7Region`)** = ⚠⚠ **1 行も動かなかった (`sorry` のまま)**。
  ⚠ **新規宣言も足していない**。

⚠⚠ **これを「単位 B が閉じた」とは書かない** — **中核 9 (有界性) / 10 ((α) 合致) は 1 行も触れていない**。
⚠ **新規 `sorry` は 1 本も入れていない**が、**新規宣言 16 本と既存 docstring 3 行の差し替えが在る**
⟹ 親 plan §4.3 / CLAUDE.md の 2 gate (honesty-auditor / style-auditor) の対象である。
⚠ **自己監査にしない**。

## 5. ⚠ 確かめて「いない」ことの名指し

**(1) ⚠⚠ 非空性は閉性より狭い仮定の下でしか言っていない。⭐⭐ しかも「確かめていない」ではなく
「反例が在る」である** — `origin_mem_thm7Region` / `thm7Region_nonempty` は **`[IsMarkovKernel W]`** を
取るが、`isClosed_thm7Region` は `W : BCChannel α β₁ β₂` (= `Kernel α (β₁ × β₂)`、Markov 性なし) を取る。
⚠⚠ **本 leg はここを「`W` が Markov でないとき空でないかは確かめていない」と書いたが、それは弱すぎた** —
**監査が `thm7Region (0 : BCChannel α β₁ β₂) = ∅` を独立に sorryAx-free で証明した** (probe **A4**)。
機構 = `BCChannel` は `Kernel α (β₁ × β₂)` の `abbrev` ゆえ `W = 0` が取れ、`Measure.compProd_zero_right`
で `IsThm7Law` 第 2 節の右辺が `0` になる一方、左辺は `ν` が確率測度ゆえ全測度 1 ⟹ **どの `ν` も
第 2 節を満たせない** ⟹ 内側の合併が空 ⟹ Markov な `TJ` を 1 本当てれば交わりも空。
⟹ ⚠⚠ **`[IsMarkovKernel W]` は省けない** (過剰な締め付けでもない) / ⟹ ⚠⚠ **閉性 2 本との間に仮定の
ギャップが実在し、一般の `W` では閉性が空虚に真になりうる穴は塞がっていない**。
⭐ **コード側は監査が 2 か所補った** — `thm7Region_nonempty` の docstring (Markov 仮定は省けない旨) と
`isClosed_thm7Region` の docstring (零核では領域が空ゆえ内容は非空な範囲に限る旨)。
⚠ **`@residual` の行は 1 文字も動いていない**。
⚠ さらに `thm7RegionOfAuxReceiver` / `thm7RegionOfInput` は `p : Measure α` を確率測度に制限せず取る
(facts N17 §5-(4) が既に名指した向き) ので、**`p` が確率測度でない断面の非空性も確かめていない**。

**(2) 材料 (i) の未検証範囲** — 機械に掛けたのは **slot 0 (無条件) と slot 4 (条件つき)** の 2 本だけで、
**残り 23 スロットは `Continuous` として 1 度も elaborate していない**。
⚠⚠ **その 2 本はスロットの 4 形のうち構造的に一番易しい 2 形である** ((a) と (c)。§4.3) —
⭐ **監査が最も重い (d) 形 (α 値 + 対条件つき) を 1 本閉じたので機械に掛かったのは計 3 本**であり、
⚠ **(b) 形 (α 値の無条件、slot 14) は誰も測っていない**。
⚠ **「同じ形だから通る」は本 leg の機械の出力ではない** (facts N2-d = 型検査は実効性を守らない、の近傍)。
⚠ さらに **「25 スロットが連続」から `thm7RegionOfLaw` の族がグラフ閉である」への段は 1 行も書いていない**
(`InThm7` / `IsThm7Eligible` を通した閉グラフ化は未着手)。

**(3) 材料 (ii) の未検証範囲** — `IsThm7Law` の **第 1 節 (`iCondIndepFun`) / 第 2 節 / 第 3 節
(`⊗ₘ` 等式) の閉性は評価していない**。§3-(10) の検索で **`μ ↦ μ ⊗ₘ TJ` の弱位相連続性は
Mathlib にも in-project にも無い**ことまでは機械で出たが、⚠⚠ **これを壁とは書かない** —
有限離散の周囲空間では pmf の多項式であり、自前で建てる路が塞がっている証拠は 1 つも無い。
⚠ 第 1 節については **「条件つき独立性の集合が閉か」を検索すらしていない**。
⭐ **この否定的主張は監査が結論形検索 + in-project `rg` で独立に引き直して生存した** が、
⚠⚠ **本 leg は最寄りの資産を名指していなかった** — **`MeasureTheory.ProbabilityMeasure.continuous_map`**
(`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`、⭐ **`Thm7Region.lean` の import 閉包の内側**)
が**押し出し `ν ↦ ν.map f` の弱位相連続性**を与え、**第 4 節の閉性と第 2–3 節の左辺・第 1 引数はこれで出る**
⟹ ⭐ **残る欠落は `μ ↦ μ ⊗ₘ TJ` ただ 1 点に絞られる**。⚠ **これは `cause:loogle-blind` の再演ではない**
(否定的主張そのものは実測で生存した) が、⚠ **「無い」を書くとき最寄りの在る資産を併記していなかった**
のは本 leg の欠落である。

**(4) headline の経路** — 起票 §0-B が名指した **`p` について一様なグラフ
`{(p, R) | R ∈ thm7RegionOfInput W p}` の閉性**も、**射影側の道具**
(`isClosedMap_snd_of_compactSpace` / `IsCompact.isClosed_image_restrict` /
`isClosedMap_restrict_of_compactSpace`) も、**1 度も使っていない**。
⚠ **これらが当たるかどうかについて本 leg は何も言っていない**。

**(5) 見立て D の帰結を配線していない** — `CompactSpace (ProbabilityMeasure (Thm7Ambient …))` は
probe では出るが、⚠⚠ **`Thm7Region.lean` には `Mathlib.MeasureTheory.Measure.Prokhorov` の
import を足していない** (消費者がまだ無いため)。⟹ **`ν` 段を実際に閉じにいく leg は
import 1 行の追加から始まる**。⚠ **その追加が既存の型クラス解決に副作用を持たないかは未検証**
(facts N2-f が記録した「符号化の副作用」の近傍)。

**(6) 一次典拠との照合** — 本 leg は **1 行も追加照合していない**。
⚠ N17 §5-(2) が名指した **`IsThm7Law` の第 2–4 節が一次典拠の因数分解より弱い**という不足は
**そのまま残っている** ⟹ ⚠⚠ **本 leg が構成した非空性の witness は「弱い述語の下での witness」である**。
⚠ **この事実から他の領域との包含について何も導いていないし、導いてはならない**。

**(7) `R₀ = 0` スライスの Π01 性** — ⚠⚠ **1 行も触れていない**。
⚠ **「3 レート版から従う」とは書かない** (子 plan §4-b / R-4 = 判定ではなく禁止条項)。

**(8) 自前で建てた一般補題の置き場** — `iCondIndepFun_of_subsingleton_codomain` /
`condMutualInfo_eq_zero_of_ae_const` / `ae_eq_const_of_map_eq_dirac` (+ `continuous_measureReal_of_discrete`
/ `continuous_entropy_of_discrete`) は **どれも BroadcastChannel 固有ではない**が、
⚠ **`Thm7Region.lean` に置いた** (既存 file の署名を触らない方針を優先した)。
⚠ **本 leg はこれが `docs/rules/` の module 構造に照らして正しい置き場かを評価していない**。
⟹ ⭐ **style gate が評価し、非 BC 固有の一般補題 6 本の誤配置を flag した** (⚠ **`docs/rules/module-structure.md`
の「ディレクトリ = 主題」に照らして**)。⚠⚠ **移設は file 移動 + import 書換 + `InformationTheory.lean`
再登録を伴う blast-radius 項目ゆえ未実行**である (行き先の当ては子 plan §3.2 の残件が持つ)。

**(9) ⭐ in-repo 重複を 1 本作っていた (style gate が compiler で検出・解消済)** — 本 leg が §2-(b) で
「自前で建てた」と書いた `mutualInfo_eq_zero_of_ae_const` は、**既存の public 定理
(`InformationTheory/Shannon/MutualInfoFiniteRange.lean:63`) を shadowing していた**。
⚠⚠ **既存の方が仮定が厳密に弱い** (第 1 引数の可測性を要求しない) ⟹ **新規側を削除して既存を消費する形へ
解消済** (commit `a60219e3`。`lake env lean` = warning は `sorry` 2 件のみ / decl は 38 → 37)。
⚠⚠ **CLAUDE.md「In-repo asset search」が名指す「did we already write it?」の再発形をここで止めた** —
⚠ **loogle はこれを防がない** (Mathlib しか見ない)。⚠ **残る 2 本の自前補題について「既存に無い」ことを
本 leg は同じ強度で確かめていない** (⚠ `iCondIndepFun_of_subsingleton_codomain` は
Mathlib 側の候補を compiler に否定させている。§4.3 A-(3))。


## 6. 波及 — ⚠ **本 leg の結果でどの文書のどの行が書き換わったか**

⚠ **本節は「どこが書き換わったか」の索引である** — **後続 leg が何をするかは書かない** (本家系の規約)。
⚠ **監査 訂正 1 / 2 はコード側 (SoT) ゆえ監査自身が Edit 済**、**訂正 3 の消し込みは style gate が Edit 済**
であり、いずれも本節の対象外である。

| 文書 | 書き換わった箇所 | 由来 |
|---|---|---|
| **本書** | **§2 冒頭** (38 decl は着地時点の数である旨) / **§2-(b)** (「3 本自前」は誤り + `ae_eq_const_of_map_eq_dirac` の読み方) / **§3-(1)** (warning 2 件は道具相対である旨と style gate による消滅) / **§3-(8)** (現況 37 decl / 行番号の移動) / **§4.2 preflight 行** (witness は原点 1 点ではない) / **§4.3 見立て C** (検証範囲の過小申告 + スロットの 4 形) / **§4.4-(1)** (module docstring の理由節が偽だった) / **§5-(1)** (「確かめていない」→ **零核では空である**) / **§5-(2)** (測った 2 本は 4 形のうち易しい 2 形) / **§5-(3)** (最寄り資産の名指しと残る欠落 1 点) / **§5-(8)** (置き場は style gate が評価した) / **§5-(9) を新設** (in-repo 重複の検出と解消) | 監査 訂正 1–7 + style gate |
| [`bc-facts.md`](bc-facts.md) | **`## N18 (T3c)` 節を新設** (claim 行 `N18-a` … `N18-g`) | 本 leg + 監査 + style gate |
| 親 plan [`bc-open-problem-t3c-plan.md`](bc-open-problem-t3c-plan.md) | **§進捗の N18 行**を消化済へ / **§5.1 に N18 着地ブロック**を追記 / **§5 の「relay 終端の棚卸し」表の形式化枠 N17 / N18 行** / **§7 判断ログ 13 に着地時の追記** (⚠ **(1)–(n) の本文は書き換えていない**) / **§5.2-3 の義務 = §6-4 の配分カウンタを引いた実測** | 本 leg |
| 子 plan [`bc-computable-region-formalization-plan.md`](bc-computable-region-formalization-plan.md) | **Status 行 / §進捗の B 行** (中核 8 の測定が進んだ状態へ) / **§3.2 (iii)** (未閉項が (i)/(ii) のどちらに絞られたか + 残る欠落 1 点) / **§3.2 に残件を 1 つ追加** (非 BC 固有の一般補題 6 本の置き場) | 本 leg + style gate flag B |
| 親 moonshot [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) | **t3c の現況行 / facts 節一覧 / N18 の同期ブロック / Sub-plan テーブルの t3c 行** (⚠ **conflict では子が SoT**) | 親子 DAG の同期 |

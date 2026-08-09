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

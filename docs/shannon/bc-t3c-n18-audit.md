# N18 敵対的独立監査 — 中核 8 の残り 2 段 + preflight (`Thm7Region.lean`)

**被監査 commit** = `c4ab66a6` (preflight) / `8d4dd999` (材料 (i)) / `f1f49506` (成果物 §2–§5)。
**起票の凍結 commit** = `7390bc9a` / **branch** = `bc-computable-region` /
**被監査ファイル** = `InformationTheory/Shannon/BroadcastChannel/Thm7Region.lean` (**38 decl / `sorry` 2 本**) /
**自己申告** = [`bc-t3c-n18-core8-closure.md`](bc-t3c-n18-core8-closure.md) §2–§5 /
**親 plan** = [`bc-open-problem-t3c-plan.md`](bc-open-problem-t3c-plan.md) §4.3 / §4.4 / §4.6 / §5.2 / §7 判断ログ 13 /
**子 plan** = [`bc-computable-region-formalization-plan.md`](bc-computable-region-formalization-plan.md) §3.2 / §6 /
**前 leg の監査** = [`bc-t3c-n17-audit.md`](bc-t3c-n17-audit.md) (⚠ **本監査は 1 文字も書き換えていない**)

**主判定 = 訂正あり生存**。⚠ **主判定を動かす訂正は 0 件**。主判定 3 軸は
**(1) 非空性は構成した (sorryAx-free) / (2) 材料 (i)(ii) は `@residual` で退出 / (3) headline は 1 行も動かなかった**
のいずれも独立に再現した。⚠ **tier 5 defect は 0 件** (循環 `:= h` / `:True` slot / **退化定義の悪用** /
load-bearing hyp / name laundering のいずれも検出せず)。⚠ **`@residual` 2 本の分類は `plan:` のままで正しい**
(⚠⚠ **`wall:` へ上げる根拠も `defect:false-statement` へ落とす根拠も出なかった**)。

---

## 1. 監査の前提と道具

- ⚠ **既定の立場は「自己申告は誤りである」**。自己申告 §5 の 8 点を **1 本ずつ両方向に**当てた (§2)。
- ⚠ **被監査 leg の probe (`preflight` / `continuity` / `kill-lines` / `axioms`) は 1 行も呼んでいない**。
  監査自身の独立 probe = [`probes/t3c-n18/audit-probes.lean`](probes/t3c-n18/audit-probes.lean)
  (`lake env lean docs/shannon/probes/t3c-n18/audit-probes.lean` = **error 0 / warning 0**、`#print axioms` の
  出力のみ)。内訳 = **A1** 法則述語の 4 節の分離 / **A2** 第 1 節が `kv = 0` で空虚であること /
  **A3** 入れ子の束縛子の向き 2 本 / **A4** 零核での領域の空性 / **A5** 25 スロット全件の消滅 /
  **C** 対条件つきスロットの entropy 化 2 段 + 対値観測量の連続性 / 最寄り資産の `#check` / `#print axioms` 10 件。
- **機械の道具** = `lake env lean` / `lake build InformationTheory.Shannon.BroadcastChannel.Thm7Region` /
  `scripts/sig_view.ts` / `rg` / loogle (index 済) / `deno run -A scripts/lean_doc_lint.ts` / `git diff` / `md5`。
- ⚠ **一次典拠は 1 行も再取得していない** (§5)。

---

## 2. 軸ごとの検算

### 軸 1 — ⚠⚠ 退化定義の悪用 (tier 5) の疑い (A-1 … A-5)

**結論 = 悪用ではない**。5 点それぞれ:

- **(A-1) `IsThm7Law` の 4 節すべてを満たすか** = **満たす**。`#print axioms
  thm7DegenerateLaw_isThm7Law` を監査自身の file から独立に取り `[propext, Classical.choice, Quot.sound]`
  (**`sorryAx` なし**)。⚠ **4 節の分解も独立に確認した** — probe **A1** は `IsThm7Law … → 第 2 節 ∧ 第 3 節 ∧
  第 4 節` を `⟨h.2.1, h.2.2.1, h.2.2.2⟩` で取り出しており、述語が実際にその 4 連言であることを compiler が
  受け取っている。⚠⚠ **空虚に満たされているのは第 1 節だけ**で、**第 2–4 節は実効的な制約である** —
  根拠は (A-4) の零核の反例 (**第 2 節に解が無くなると領域ごと消える**)。
- **(A-2) 第 1 節は空虚さに乗っているだけか** = ⭐ **乗っている。ただし反則ではない**。probe **A2** は
  `Fintype.card (bcAuxAlphabet 0) = 1` を `rfl` で出し、**任意の**確率測度 `ν` について
  `IsThm7Law W TJ p ν ↔ (第 2 節 ∧ 第 3 節 ∧ 第 4 節)` を機械で通した ⟹ **`kv = 0` では第 1 節は情報を
  1 bit も担わない**。⚠ **`thm7Cap α i` は `Fintype.card α + 6` / `+ 1` ゆえ `kv = 0` は上限つき合併の
  内側に正当に入る**ので、これは定義の抜け道ではなく**合併が本当に含む要素**である。
  ⚠⚠ **弱める向きの効き**: `origin_mem_thm7Region` は **補助変数の構造を 1 mm も使っていない** ⟹
  **非空性は `IsThm7Law` 第 1 節の強度について何も検証しない**。⚠ **宣言はそれ以上を主張していない**
  (docstring は「原点を含む」と書く) ⟹ **名前も文言も laundering していない**。
- **(A-3) 入れ子の向きと一様性** = **正しい**。probe **A3** の 2 本が機械で出した形:
  `R ∈ thm7Region W ↔ ∃ p, ∀ kJ TJ, IsMarkovKernel TJ → R ∈ thm7RegionOfAuxReceiver W p TJ` と
  `R ∈ thm7RegionOfAuxReceiver W p TJ ↔ ∃ kv, (∀ i, kv i < thm7Cap α i) ∧ ∃ ν, IsThm7Law … ∧ R ∈ thm7RegionOfLaw ν`
  ⟹ ⭐ **`p` は `∀` の外 (`TJ` について一様)、`ν` は `TJ` に依存してよい**。本体は `intro kJ TJ hTJ` の
  **後**に `thm7DegenerateLaw W TJ x₀` を置いている ⟹ ⚠ **1 つの `TJ` で済ませてはいない**。
- **(A-4) ⚠⚠ `[IsMarkovKernel W]` は要るのか** = ⭐⭐ **要る。しかも自己申告より強い形で要る**。
  監査は `thm7Region (0 : BCChannel α β₁ β₂) = ∅` を**独立に証明した** (probe **A4**、
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`)。機構 = `BCChannel` は `Kernel α (β₁ × β₂)` の
  `abbrev` ゆえ `W = 0` が取れ、`Measure.compProd_zero_right` で第 2 節の右辺が `0` になり、
  左辺は `ν` が確率測度ゆえ全測度 1 ⟹ **どの `ν` も第 2 節を満たせない** ⟹ 内側の合併が空 ⟹
  Markov な `TJ` を 1 本 (`Kernel.const _ (dirac default)`) 当てれば交わりも空。
  ⟹ ⚠⚠ **自己申告 §5-(1) の「確かめていない」は弱すぎた** — 実態は **反例が在る**。
- **(A-5) 25 スロットすべてが 0 か** = **すべて 0**。probe **A5** は
  `∀ i : Fin 25, thm7Slots (thm7DegenerateLaw W TJ x₀) i = 0` を通す ⟹ ⚠ **一部だけを潰して残りを
  `simp` の副作用で流した形跡は無い**。

### 軸 2 — 署名の正直さ (38 decl / 新規 16 本を重点)

- **`sorryAx`-free の独立再導出** (監査 file から 10 件): `thm7Region_nonempty` /
  `origin_mem_thm7Region` / `thm7DegenerateLaw_isThm7Law` / `thm7Slots_thm7DegenerateLaw` /
  `iCondIndepFun_of_subsingleton_codomain` / `continuous_entropy_of_discrete` /
  `continuous_measureReal_of_discrete` = **標準 3 公理のみ**、
  `isClosed_thm7RegionOfInput` / `isClosed_thm7Region` = **`sorryAx` あり** (既知の 2 本の配線)。
- ⚠⚠ **`sorryAx`-free は必要条件であって十分条件ではない** ⟹ **新規 16 本の仮定を 1 本ずつ判定した**。
  結果 = **核を担う hypothesis は 1 本も無い**。内訳の判定:
  - `[IsMarkovKernel W]` / `[IsMarkovKernel TJ]` / `[IsProbabilityMeasure μ]` / `[Fintype]` /
    `[StandardBorelSpace]` / `[Subsingleton (β i)]` / `[Nonempty (β i)]` = **regularity の instance 引数**。
    ⭐ **`[IsMarkovKernel W]` は (A-4) により省けない** ⟹ **過剰な締め付けでもない**。
  - `(hf : Measurable f)` / `(hm' : m' ≤ mΩ)` = **regularity**。
  - `(h : μ.map f = Measure.dirac c)` (`ae_eq_const_of_map_eq_dirac`) = ⚠ **結論と論理的に同値**
    (確率測度の下で `μ.map f = dirac c ↔ f =ᵐ[μ] const c`)。⚠⚠ **循環 (`:= h`) ではない** — 型が異なり
    body は 5 行の実証である。⟹ **表現の取り替えであって強化ではない**と読むのが正しく、実質は
    `thm7DegenerateLaw_map_input` (`Measure.fst_compProd` 2 段) が担う。**tier 5 ではない**。
  - `(hc : Xs =ᵐ[μ] fun _ ↦ c)` (`mutualInfo_eq_zero_of_ae_const` / `condMutualInfo_eq_zero_of_ae_const`)
    = **結論より真に強い前提**であり、結論 (情報量 = 0) と同値ではない ⟹ **regularity 側**。
- **deprecated タグ** = `@audit:suspect` / `@audit:staged` / `@audit:defer` / 散文 `🟢ʰ` /
  `NOT a discharge` は **0 件** (`rg`)。
- **共有 sorry 補題の集約** = 本 file の `sorry` 2 本は**別の言明**である (`ν` 段は固定 `p` の断面、
  headline は `p` について一様な形) ⟹ ⚠ **集約漏れではない** (N17 監査の N17-d と同じ結論)。

### 軸 3 — `@residual(plan:…)` の分類

- **plan slug の実在** = `docs/shannon/bc-computable-region-formalization-plan.md` が在る。
  ⚠ **末尾 `-plan` を落とす in-tree の作法どおり**。
- **`wall:` へ上げるべきか** = ⚠ **上げない**。CLAUDE.md の wall 宣言規約を通していない
  (⟹ 自己申告 §4.1 の判断と一致)。⚠ 監査自身が引き直した結論形検索でも「壁」を支持する材料は出ていない —
  **有限離散の周囲空間では欠けている段は pmf の多項式**であり、自前で建てる路が塞がっている証拠は 0。
- **`defect:false-statement` へ落ちるか** = ⚠ **落とす根拠は出なかった**。監査の解析的な読み
  (⚠ **機械では 1 行も出していない**) = **(a)** 25 スロットは有限離散の周囲空間上で pmf の連続関数、
  **(b)** `InThm7` / `IsThm7Eligible` は閉条件、**(c)** 法則の 4 節はいずれも pmf の多項式等式 ⟹
  グラフ閉 + コンパクト添字の射影で 2 本とも真である公算が高い。⚠⚠ **公算は判定ではない**
  (facts N17-g (6) の位置づけを動かさない)。
- ⭐⭐ **オーケストレーターの問い「preflight が閉じた分だけ `IsClosed` が真である見込みは上がったか」への回答
  = 上がっていない。むしろ逆向きである**。空集合の閉性は**自明に真**であり、**非空性は閉性と直交する** ⟹
  preflight が消したのは「命題が空虚に真になる退化例のクラス」であって、**真であることの証拠は 1 つも
  足していない**。⟹ **命題の内容が増えた分だけ、偽でありうる余地は狭まっていない**。
  ⚠ **しかも消えたのは Markov な `W` の範囲だけ**である (A-4)。

### 軸 4 — 自己申告 §5-(3) の否定的主張 (資産に対する否定)

**生存。ただし最寄りの資産が名指されていない**。

- **loogle の結論形での引き直し** (⚠ **裸の識別子検索で終わらせていない**):
  `MeasureTheory.Measure.compProd, Continuous` = **0 件** /
  `MeasureTheory.ProbabilityMeasure, ProbabilityTheory.Kernel` = **0 件** /
  `ProbabilityTheory.Kernel.compProd, Continuous` = **1 件** (`Kernel.continuous_integral_integral` =
  **被積分関数についての連続性**であり測度についてではない ⟹ 当たらない) /
  `ProbabilityTheory.iCondIndepFun, IsClosed` = **0 件** / `ProbabilityTheory.IndepFun, IsClosed` = **0 件**。
- **in-project `rg`** (⚠ **loogle は Mathlib しか見ない**) = `Continuous.*compProd` / `IsClosed.*[iI]ndep`
  ともに 0 件。
- ⚠⚠ **名指すべき最寄りの資産** = `MeasureTheory.ProbabilityMeasure.continuous_map`
  (`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`、**`Thm7Region.lean` の import 閉包の内側**。
  probe で `#check` 済) = **押し出し `ν ↦ ν.map f` の弱位相連続性**。⟹ **第 4 節の閉性と、第 2–3 節の
  左辺・第 1 引数はこれで出る** ⟹ **残る欠落は `μ ↦ μ ⊗ₘ TJ` ただ 1 点**に絞られる。
  ⚠ **これは `cause:loogle-blind` の再演ではない** — 否定的主張そのものは実測で生存した。
- **§3-(5) 条件 1 の独立確認** = `CompactSpace (ProbabilityMeasure _)` の instance は
  `Mathlib.MeasureTheory.Measure.Prokhorov` にのみ在り (loogle 1 件)、`rg -n Prokhorov InformationTheory/`
  = 0 件、かつ `Thm7Region.lean` を import した scratch で `failed to synthesize instance of type class
  CompactSpace (ProbabilityMeasure (ULift (Fin 3)))` を実測 ⟹ **import 閉包の外である**。

### 軸 5 — 見立て 4 本の較正が正直か (⚠ とくに見立て C)

- ⭐⭐ **見立て C の「予告より強く当たった」は生存する。ただし自己申告は検証範囲を過小に申告している**。
  ⚠⚠ **機械に掛けた 2 スロット (slot 0 = `I(W;Y)` / slot 4 = `I(U;Y|W)`) は、どちらも α 値の観測量を
  含まない** (型は補助アルファベットと `β₁` だけ) ⟹ **自己申告の 2/25 は「構造的に一番易しい 2 本」である**。
  監査は**構造的に最も重い形** (α 値の観測量 + **対** 条件つき = slot 15 形) を独立に検算した:
  **(a)** `condMutualInfo_eq_condEntropy_sub_condEntropy` で条件つき entropy の差へ (`(by fun_prop)` 3 本)、
  **(b)** `entropy_pair_eq_entropy_add_condEntropy` で **4 本の entropy** へ、
  **(c)** 連続性の原子 `continuous_entropy_of_discrete` は**対値の観測量も覆う**
  (`hf.prodMk hg` で当たる) ⟹ ⭐ **追加の instance 持ち上げは 1 本も要らなかった**
  (⚠ **`classical` も `MeasurableSingletonClass α` の `haveI` も不要であることを機械で確認**)。
  ⟹ **C の「材料 (i) の全体が `ν ↦ entropy ν f` の連続性 1 本に集約された」は、自己申告が測った範囲より
  広い範囲で機械に支持される**。⚠⚠ **緩める側の当たりであることは変わらない**ので、親 §4.4 の非対称性の
  下では **「安く済んだ」ではなく「外れていたら高くついた賭けに勝った」** という自己申告の読み方は正しい。
- **見立て A / B / D** = 自己申告の較正と齟齬なし。⚠ **D の 2 条件のうち条件 1 は独立に再現した**
  (上記 軸 4)。⚠ **条件 2 (13 因子側 instance 3 本の持ち上げ) は監査は再現していない** (§5)。

### 軸 6 — 起票の凍結

- `awk '/^## 0\./,/^## 2\./' … | sed '$d' | grep -v '^[[:space:]]*$' | md5` =
  **186 行 / `8e5b0ff16213479aecfd54cb69107fd0`** ⟹ **一致**。
  ⚠ **範囲の非空 (186 行) を先に確認したうえでの一致である** (空文字列どうしの偽 PASS ではない)。
- `git diff 7390bc9a..HEAD -- docs/shannon/bc-t3c-n18-core8-closure.md` の**削除行は 0 行**である
  ⟹ ⚠ **§0 / §1 の行は 1 行も削除側に出ていない**。

### 軸 7 — 禁止条項の違反 / はみ出し

- `Thm7(W)` への呼び替え / 「3 レート版から従う」/ 「§0 に近づいた」/ 「あと少し」「残るのは行数と配線だけ」型 /
  `Thm7 ⊋ C` / `Thm7 ⊄ Thm8` / `R ∈ Thm7` = **`rg` の当たりはすべて禁止条項そのものの再掲**であり、
  **主張としての使用は 0 件** (コード側も 0 件)。
- **はみ出し** = 中核 9 (有界性) / 10 ((α) 合致) の宣言は **0 件** (`sig_view --names` の 38 decl に無い)。
- **既存署名の非改変** = `git diff 7390bc9a..f1f49506 -- <対象 file>` の削除行は **3 行**で、
  いずれも `isClosed_iUnion_thm7RegionOfLaw` の docstring 散文である ⟹ ⚠ **既存宣言の署名行は 0 行**。

---

## 3. 訂正一覧 (番号つき。⚠ **主判定を動かすものは 0 件**)

1. ⚠⚠ **モジュール docstring の理由節が偽だった** — `## Main statements` の
   「`thm7Region_nonempty` — the region is inhabited, **so its closedness is not a statement about the
   empty set**」は、**閉性 2 本が `[IsMarkovKernel W]` を要求しない**ため一般の `W` では成り立たない
   (反例 = 軸 1 (A-4))。⟹ ⭐ **監査がコード側を修正済** (`Thm7Region.lean` の `## Main statements`)。
   **伝播先** = コード (**済**) / 成果物 §4.4-(1) / facts。
2. ⚠⚠ **自己申告 §5-(1) は弱すぎた** — 「`W` が Markov でないとき空でないかは**確かめていない**」ではなく
   **「`W = 0` では空である」が機械で出る**。⟹ **伝播先** = 成果物 §5-(1) / facts (⚠ **非空性の適用範囲は
   Markov な `W` に限る、を反例つきで**)。⭐ **コード側は監査が 2 か所補った** —
   `thm7Region_nonempty` の docstring (Markov 仮定は省けない旨) と `isClosed_thm7Region` の docstring
   (零核では領域が空ゆえ内容は非空な範囲に限る旨)。⚠ **`@residual` の行は 1 文字も動かしていない**。
3. **§3-(1) の「warning 2 件のみ」は道具相対である** — `lake env lean` では 2 件だが、
   `lake build InformationTheory.Shannon.BroadcastChannel.Thm7Region` では **本 leg が入れた 3 件目**が出る
   (`The \`show\` tactic should only be used to indicate intermediate goal states` = `linter.style.show`、
   `continuous_measureReal_of_discrete` の中。**leg 着地時点で L301 / 監査の docstring 追記後は L304**)。
   ⚠ **同 file の L1 に出る `linter.style.header` は project 全体の既存パターン**であり本 leg とは無関係。
   ⚠ **honesty ではなく style gate の対象**。⟹ **伝播先** = style gate (`change` へ差し替え) /
   成果物 §3-(1) の但し書き。
4. **§4.3 見立て C の較正は、検証範囲を過小に申告している** — 機械に掛けた 2 スロットは**構造的に
   一番易しい 2 本**であり (α 値の観測量を含まない)、⭐ **監査が最も重い形 (α 値 + 対条件つき) を
   独立に閉じた** (軸 5)。⟹ **C の主張は自己申告より広い範囲で支持される**。
   **伝播先** = 成果物 §4.3 / §5-(2)。⚠ **スロットの形は 4 つある** — (a) 補助変数どうし/出力の無条件
   (slot 0 等)、(b) **α 値の無条件** (slot 14)、(c) 補助変数の単変数条件つき (slot 4 等)、
   (d) **α 値 + 対条件つき** (slot 15/16/21–24) ⟹ **leg が測ったのは (a)(c)、監査が測ったのは (d)、
   (b) は誰も測っていない** (⚠ **(b) は 4 形のうち最も軽い**)。
5. **§5-(3) の否定的主張は生存するが、最寄りの資産が名指されていない** —
   `MeasureTheory.ProbabilityMeasure.continuous_map` (import 閉包の内側) が押し出しの連続性を与える ⟹
   **残る欠落は `μ ↦ μ ⊗ₘ TJ` ただ 1 点**に絞られる。⟹ **伝播先** = 成果物 §5-(3) / facts。
6. ⚠ **非空性の witness は 1 点ではない** — スロットが全て 0 のとき `InThm7 0 (0, -t, -t)` は
   **`0 ≤ t` で成り立つ** (probe **A5** の 2 本目、⚠ **スロットベクトル上の算術のみを機械で確認した**)。
   ⟹ 成果物 §4.2 の preflight 行の読み方に効く (「原点 1 点」ではない)。
   ⚠⚠ **これは中核 9 (有界性) についての主張ではない** — **領域の上界方向には 1 文字も触れていない**。
7. **`ae_eq_const_of_map_eq_dirac` の仮定は結論と論理的に同値である** (軸 2)。⚠ **循環ではない**が、
   **強化ではなく表現の取り替え**である ⟹ ⚠ **この補題を「18 スロットを消した実質」と読まない**
   (実質は `thm7DegenerateLaw_map_input`)。**伝播先** = facts (読み方の注記のみ。コード修正は不要)。

**コード側への書込 (監査が実施済)** = `Thm7Region.lean` の docstring **3 か所** (`## Main statements` 1 行 /
`thm7Region_nonempty` に 1 段落 + **`@audit:ok`** / `isClosed_thm7Region` に 1 段落)。
⚠ **署名・本体・`@residual` の行は 1 文字も触れていない**。編集後 `lake env lean` = **warning 2 件のみ**、
`lean_doc_lint.ts` = **strict 10 / ratchet 4 すべて 0 件**。

---

## 4. 生存の限界 (⚠ 本監査が「生存」と言った範囲)

- **「非空性を構成した」の範囲は `[IsMarkovKernel W]` に限る**。⚠⚠ **その外では領域は空になりうる**
  (`W = 0` で機械)。⟹ **閉性が空虚に真でありうる穴は、Markov な `W` の範囲でのみ塞がった**。
- **「材料 (i)(ii) が `@residual` で退出した」は妥当**だが、⚠ **退出先の 2 本が真であること自体は
  誰も判定していない** (監査も含む。軸 3)。
- **「headline は 1 行も動かなかった」は正しい** — `p` について一様なグラフの宣言は 38 decl に無い。
- ⚠⚠ **本監査は `Thm7 ⊋ C` / レート領域の包含について 1 文字も言っていない**。
- ⚠⚠ **`thm7Region` が典拠の領域であるとは言っていない** (facts N17-c の 2 つの偏差はそのまま)。

---

## 5. 監査が確かめていないこと (⚠ 名指しする)

1. **一次典拠との照合を 1 行も行っていない** ⟹ N17 §5-(2) の `IsThm7Law` 強度不足は**監査も追認していない**。
   ⟹ ⚠⚠ **本 leg の非空性 witness が「弱い述語の下での witness」であるという自己申告 §5-(6) は、
   監査からは支持も反証もされていない**。
2. **`isClosed_iUnion_thm7RegionOfLaw` / `isClosed_thm7Region` が真かを機械では 1 行も出していない**
   (軸 3 は解析的な読みである)。
3. **見立て D の条件 2 (13 因子側 instance 3 本の持ち上げ) を独立に再現していない**。
   条件 1 (`CompactSpace (ProbabilityMeasure _)` が import 閉包の外) のみ独立確認した。
4. **「25 スロットが連続」から「族がグラフ閉」への段は監査も 1 行も書いていない**。
   ⚠ **監査が閉じたのは 1 スロットの entropy 化 2 段と、対値観測量への連続性の当たりまでである**。
5. **残り 22 スロットを個別に elaborate していない** (leg が 2 本 / 監査が 1 本 = 計 3 本のみ)。
   ⚠ **「同じ形だから通る」は監査の機械の出力ではない**。
6. **`R₀ = 0` スライスの Π01 性には 1 行も触れていない** (子 plan §4-b / R-4 = 禁止条項)。
7. **自前 4 補題の置き場 (module 構造) を評価していない** — style gate の対象。
8. **中核 9 (有界性) / 10 ((α) 合致) には 1 行も触れていない**。

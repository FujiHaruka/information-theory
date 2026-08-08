# N17 敵対的独立監査 — 単位 B 受け皿の昇格 + 中核 8 (`Thm7Region.lean`)

**被監査 commit** = `d1b78af9` (起票 = `93dd1527`) / **branch** = `bc-computable-region` /
**被監査ファイル** = `InformationTheory/Shannon/BroadcastChannel/Thm7Region.lean` (282 行 / 22 decl) +
`InformationTheory.lean` (import 1 行) /
**自己申告** = [`bc-t3c-n17-unit-b.md`](bc-t3c-n17-unit-b.md) §2–§5 /
**親 plan** = [`bc-open-problem-t3c-plan.md`](bc-open-problem-t3c-plan.md) §5.1 / §7 判断ログ 12 /
**子 plan** = [`bc-computable-region-formalization-plan.md`](bc-computable-region-formalization-plan.md)
§3.2 / §4 / §6

**主判定 = 訂正あり生存**。⚠ **主判定 (受け皿は昇格した / 中核 8 は未閉) を動かす訂正は 0 件**。
⚠ **tier 5 defect は 0 件** (循環 / `:True` slot / 退化定義悪用 / load-bearing hyp / name laundering の
いずれも検出せず)。⚠ **`@residual` 2 本の分類は `plan:` のままで正しい** (格上げも格下げもしない)。

---

## 1. 監査の前提と道具

- ⚠ **既定の立場は「自己申告は誤りである」**。自己申告 §5 の 7 点は 1 本ずつ向きごと検算した (§2 軸 1 / 軸 2)。
- **一次典拠を再取得した** — `docs/shannon/lit-fetch.sh /path auxrec` (Gohari–Nair, Auxiliary-Receiver)。
  ⚠ **抽出テキストは repo に置いていない** (public repo)。参照は `auxrec.txt` の Theorem 7 / (18a)–(18i) /
  (19a)–(19c) / (20a)–(20c) / 濃度の「Moreover」文。
- **機械の道具** = `lake env lean` / `lake build InformationTheory.Shannon.BroadcastChannel.Thm7Region`
  (olean 生成のみ) / `scripts/sig_view.ts` / `rg` / loogle / `deno run -A scripts/lean_doc_lint.ts`。
- ⚠ **否定的な主張はコンパイラに否定させた** — 監査自身の probe は
  [`probes/t3c-n17/audit-probes.lean`](probes/t3c-n17/audit-probes.lean) に置いた
  (`lake env lean docs/shannon/probes/t3c-n17/audit-probes.lean` = **無出力**)。
  内訳 = **P1** 制約系の無矛盾 / **P2** 総質量の強制 / **P3** 2 つの束縛子が同じ集合を定めること /
  **P4** 原点の所属の条件つき判定 / **N1** (コメント保存、コンパイル不能) 固定 `p` のはしごでは headline が
  出ないこと。

---

## 2. 軸ごとの検算

### 軸 1 — 束縛子の取り替えは「難所を消す定義変更」か

**結論 = 否。⭐ 自己申告 §5-(4) の「同じ集合を定めることは証明していない」は、監査が機械で閉じた。**

**(1-a) 総質量は第 4 節が既に強制している** (probe P2)。`IsThm7Law` の第 4 節
`ν.map (fun q ↦ q.2.1) = p` と `p : ProbabilityMeasure α` から `IsProbabilityMeasure ν` が出る
(`Measure.map_apply` + `Set.preimage_univ` の 3 行)。⟹ ⚠ **facts N2-l (5) が名指した未閉項
「束縛子が総質量を固定することは Lean で証明されていない」は、本監査で閉じた** (訂正 4)。

**(1-b) 2 つの束縛子は同じ集合を定める** (probe P3、`lake env lean` 無出力)。probe 側の形
`⋃ (ν : Measure _) (hν : IsFiniteMeasure ν) (_ : IsThm7Law …)` と昇格先の形
`⋃ (ν : ProbabilityMeasure _) (_ : IsThm7Law …)` の集合等式を、昇格先の def のまま両向き示した。
⚠ **成立するのは入力則が確率測度のときである** — `thm7RegionOfAuxReceiver` / `thm7RegionOfInput` は
`p : Measure α` を一般に取るので、`p` が確率測度でないときは前者が空、後者が非空でありうる。
⟹ **`thm7Region` の中では等しく、中間 def の一般 `p` では等しくない**。

**(1-c) 一次典拠との照合 (25 スロット / 9 制約 / 6 適格性 / 濃度 / 入れ子)**。⚠ **一般論ではなく逐語で当てた**。
(18a)–(18i) と `InThm7` の 9 連言、(19a)–(19c) + (20a)–(20c) と `IsThm7Eligible` の 8 連言、
0–24 の全スロットと 13 変数の対応、`thm7Cap` (`i.2 = 2` で `|X|+6`、他は `|X|+1`。
`bcAuxAlphabet k` の濃度が `k+1` ゆえ `kv i < |X|+6` が `濃度 ≤ |X|+6`) — **不一致 0 件**。
入れ子も「ある `p(x)` / 任意の `T_J` / ある同時分布」= `⋃_p ⋂_{kJ,T_J} ⋃_{kv,ν}` で一致。
⟹ **自己申告 §5-(1) の「照合した」側は生存**。

**(1-d) 退化定義の悪用 — `thm7Region W` は空でありうるか**。⚠ **自己申告 §5-(1) はこれを穴として
申告しているが、向きが 2 つ混ざっている**。分けて判定した:

- **制約系そのものは無矛盾** (probe P1、機械)。`IsThm7Eligible (fun _ ↦ 0)` と
  `InThm7 (fun _ ↦ 0) (0,0,0)` はいずれも `norm_num` で通る ⟹ **適格性 8 連言が互いに矛盾していて
  どのスロット列も弾かれる、という形の空虚さは無い**。
- **原点の所属は「スロットが全て 0 の法則が 1 つあること」に帰着する** (probe P4、機械)。
  ⟹ ⚠ **残る未閉項は「その法則の構成」だけ**であり、そのための原子は**すべて in-project に在る**:
  `mutualInfo_eq_zero_iff_indep` (`MutualInfo.lean:115`) / `condMutualInfo_eq_zero_of_markov`
  (`CondMutualInfo.lean:349`) / `iCondIndepFun.of_subsingleton` (Mathlib)。
- ⟹ **「空集合ゆえ閉性が空虚に真」は、少なくとも制約系の側からは出ない**。⚠ **ただし
  `thm7Region W ≠ ∅` 自体は機械で閉じていない** (§5-(1))。

### 軸 2 — `IsThm7Law` の強度 diff

**結論 = 自己申告 §5-(2) は正しい。⭐ ただし申告に無い 2 点を足す — 向きと、逆向きの偏差。**

**(2-a) 弱いことの確認 (一次典拠に当てた)**。典拠の因数分解は
`p_{U,V,W,X} p_{W̃,Ũ,Ṽ|X} p_{Ŵ,Û,V̂|X} T_{Y,Z|X} T_{J|X,Y,Z}` であり、`T_{Y,Z|X}` は
**`(Y,Z)` が全補助変数から `X` の下で条件つき独立**であることを含む。`IsThm7Law` の第 2 / 第 3 節は
`ν.map (X,Y,Z) = (ν.map X) ⊗ₘ W` / `ν.map ((X,Y,Z),J) = (ν.map (X,Y,Z)) ⊗ₘ TJ` という
**周辺分布の等式のみ**であり、この条件つき独立性を要求しない ⟹ **述語は真に弱い**。
第 1 節 (`iCondIndepFun` を `σ(X)` の下で 3 つ組に課す) は典拠の 3 因子に一致する。

**(2-b) ⭐ 向き (申告に無い)**。述語が弱い ⟹ `⋃_ν` が大きい ⟹ `⋂_{kJ,T_J}` も `⋃_p` も単調 ⟹
**`thm7Region W` は典拠の (同じ濃度上限の下での) 領域の上位集合**である。
⟹ ⚠⚠ **後続への含意**: 領域を**上から**押さえる主張 (閉性 / 他の領域への包含) を本 def で示せば
典拠の領域についても従うが、**下から**の主張 (ある点が領域に属する / 領域が真に大きい) は
**典拠の領域へは移らない**。⚠ **この非対称性が自己申告に書かれていない**のが本軸の実質的な穴である。

**(2-c) ⭐ 逆向きの偏差 (申告に無い)**。`thm7RegionOfAuxReceiver` は濃度上限を**課している**。
典拠の「Moreover, in computing the bound it suffices to assume …」は**上限つきと上限なしが一致する**という
主張であり、**Lean 側では未形式化**である ⟹ **本 def は「上限つき領域」であって、上限なしの
`Thm7(W)` と一致するかは典拠の濃度補題に依存する**。⟹ ⚠ **偏差は 2 つあり、向きが逆である**
(述語の弱化は広げ、上限は狭める) ⟹ **「`thm7Region` = `Thm7(W)`」とは書けない**。

**(2-d) tier 判定 = tier 5 ではない**。`IsThm7Law` は FALSE ではなく (充足可能)、vacuous でもなく
(P1/P4)、hypothesis として渡されてもいない (軸 4)。`degenerate` / `false-hypothesis` /
`false-statement` のいずれにも当たらない ⟹ **`@audit:defect(...)` は付けない**。
⚠ **ただし CLAUDE.md「Textbook-object strength diff」が名指す形そのもの**であり、
**開示の場所が `IsThm7Law` の docstring 1 か所しかない**のが弱い ⟹ 訂正 1 / 訂正 2。

### 軸 3 — `@residual(plan:…)` の分類

**結論 = `plan:` で正しい。⭐ ただし docstring の否定的主張 1 件が過大であり、共有の見立ても 1 件外れている。**

- **plan の実在**: `docs/shannon/bc-computable-region-formalization-plan.md` は実在する。
  ⚠ **slug は `-plan` を落としている** — audit-tags.md は「plan filename stem (no `.md`)」と書くが、
  in-tree の `plan:` 残課題は 2 slug しか無く、**2/2 とも `-plan` を落としている**
  (`epi-debruijn-pertime-closure` も同型) ⟹ **片方だけ直すと分裂する**。訂正 6 (語彙側の追記を提案)。
- **`wall:` へ格上げすべきか = 否**。子 plan §1.1 のとおり壁の主張は 1 件も無く、
  CLAUDE.md の wall 宣言規約を通していない ⟹ `plan:` が正しい (自己申告 §4.1 の判断は生存)。
- ⭐ **逆向き (過大評価) の検出**: `isClosed_iUnion_thm7RegionOfLaw` の docstring は
  「二十五の情報量が同時分布に連続に依存すること」と「因数分解が閉集合を切り出すこと」の
  **どちらも available でない** と書いていた。⚠ **これは資産に対する未検証の否定的主張**であり、
  CLAUDE.md が名指す再発形 (`cause:loogle-blind`) である。`rg` で実測すると:
  - **在る**: `continuous_mutualInfoPmf` (`RateDistortion/Achievability.lean:204`、
    `Continuous (fun q : α × β → ℝ ↦ mutualInfoPmf q)`) / それを周辺化写像と合成する型
    (`WynerZiv/Basic.lean:148-155`) / コンパクト単体 + 連続目的関数の先例
    (`Achievability.lean:242-246`) / `pmfToMeasure` と `stdSimplex` 圏の在庫 10 ファイル。
  - **無い**: 条件つき版 (`condMutualInfoPmf` は `rg` で 0 件) / 周囲空間上の測度と pmf 座標の橋。
  ⟹ **未閉項は「どちらも無い」ではなく「条件つき版と座標の橋」である**。訂正 1。
- **共有 sorry 補題への集約**: ⚠ **自己申告 §4.2 の「残った 2 つは同じ形の未閉項を共有している」は
  向きが不正確**。2 本は同じ*材料*を要するが、**同じ*言明*ではない** — 後者は添字 `p` について一様な
  (グラフの) 形を要し、前者はその `p` 断面にすぎない。⟹ **1 本の共有補題へ機械的に集約できる形ではない**
  (集約漏れではない)。訂正 3 で言い直す。

### 軸 4 — 署名の正直さ (11 宣言 + 全 22 decl)

**結論 = tier 5 は 0 件。自己申告 §3-(5) の署名走査は独立にやり直して一致した。**

- `scripts/sig_view.ts --no-context` で全 22 decl の署名を再走査した。**仮定はすべてデータ引数か
  regularity の instance 引数** (`[Fintype]` / `[MeasurableSpace]` / `[StandardBorelSpace]` /
  `[Nonempty]` / `[IsFiniteMeasure ν]`)。**`*Hypothesis` 述語を hypothesis に取る宣言は 0 本**。
- ⚠ **重点確認**: `IsThm7Eligible` / `IsThm7Law` は **def の内側 (setOf と `⋃` の束縛子) でしか
  使われていない** — 定理の仮定には 1 度も現れない。⟹ **「述語を狭めて領域を空にし閉性を自明に出す」形
  ではない**。⚠ しかも軸 2 のとおり述語は典拠より**広い** ⟹ **狭めによる退化はそもそも起きていない**。
- headline `isClosed_thm7Region (W : BCChannel α β₁ β₂)` は**仮定 0 本**。
  `isClosed_iUnion_thm7RegionOfLaw` は `p : Measure α` を**確率測度に制限せず**取っている
  ⟹ **言明はむしろ強い側**であり、隠れた precondition の密輸は無い。
- 循環 (`:= h`) / `:True` slot / name laundering (`_discharged` / `_full` / `_unconditional`) /
  deprecated タグ (`@audit:suspect` / `@audit:staged` / 散文 `🟢ʰ`) = **いずれも 0 件**
  (`rg '@residual|@audit:|🟢|suspect|staged' <file>` のヒットは `@residual` 2 行のみ)。
- **`.toReal` の junk 値**: 25 スロットは `ℝ≥0∞` の `.toReal` だが、周囲空間は 13 因子とも有限型で
  あり情報量は有限 ⟹ **`∞ ↦ 0` の切り捨てが効く経路は無い**。

### 軸 5 — 起票の凍結

**結論 = 凍結は守られている (機械確認)**。`## 0.` 行から `## 2.` 直前までを空行除去して md5 を取った:

```
起票 93dd1527 : 163 行 / 67cd1eec2d5e8b4a358b5d3b435ce4ee
現行 (HEAD)   : 163 行 / 67cd1eec2d5e8b4a358b5d3b435ce4ee
```

⚠ **範囲が非空であること (163 行) を先に確認してから md5 を取った** — ブリーフが警告した
「`^## §0` の誤った範囲指定が空を返して偽の PASS を出す」罠は踏んでいない。

---

## 3. 訂正一覧 (番号つき)

⚠ **どの文のどの語を何に直すか**まで書く。⚠ **1–2 はコード側 (SoT) ゆえ本監査が既に Edit 済**、
**3–7 は文書側ゆえ着地 leg が伝播する**。

1. **[実施済] `Thm7Region.lean` `isClosed_iUnion_thm7RegionOfLaw` の docstring**。
   旧: *"…cuts out a closed set of joint laws; **neither is available here**."*
   新: *"…cuts out a closed set of joint laws. Continuity of an unconditional information in the
   joint pmf is available, as is the pattern that composes it with a marginal map; the conditional
   form and the passage from a measure on the ambient space to its pmf are the missing pieces."*
   **理由** = 資産に対する未検証の否定的主張だったため (軸 3、`continuous_mutualInfoPmf` 他が実在)。
   ⚠ **`@residual(plan:bc-computable-region-formalization)` の行は 1 文字も触っていない**。
2. **[実施済] 同ファイル `IsThm7Law` の docstring 末尾に 1 文追加**。
   追加: *"Every set built from it below is accordingly at least as large as the corresponding set
   built from the product form."*
   **理由** = 弱さは書かれていたが**向き**が書かれておらず、後続が下からの主張を典拠へ移す危険が
   残っていたため (軸 2-b)。
3. **`bc-t3c-n17-unit-b.md` §4.2 末尾**。旧: 「**残った 2 つは同じ形の未閉項を共有している**」→
   新: 「**残った 2 つは同じ材料を要するが同じ言明ではない — headline は添字 `p` について一様な
   (グラフの) 形を要し、`ν` 段はその `p` 断面である**」。
   **機械の根拠 (逐語、probe N1)**: 固定 `p` のはしごで headline を出そうとすると
   `error(lean.synthInstanceFailed): failed to synthesize instance of type class
   AlexandrovDiscrete (ℝ × ℝ × ℝ)` で落ちる。
4. **同 §5-(4)**。旧: 「**2 つの束縛子が同じ集合を定めることは Lean で証明していない**」→
   新: 「**入力則が確率測度である限り同じ集合を定めることは機械で確認済 (`probes/t3c-n17/audit-probes.lean`
   P2 / P3)。未閉なのは中間 def が一般の `p : Measure α` を取る場合であり、そのとき 2 つは一致しない**」。
   ⚠ **同 §5-(4) が引く facts N2-l (5)「法則が総質量を固定することが証明されていない」も同時に閉じる**
   (訂正 5)。
5. **`bc-facts.md` `## N2 (T3c)` の **N2-l (5)****。「未閉項」の側から
   「**`IsThm7Law` 第 4 節が総質量を強制する (`Measure.map_apply` + `Set.preimage_univ`、3 行)。
   confidence = machine、再検証 = `lake env lean docs/shannon/probes/t3c-n17/audit-probes.lean`、
   last-verified = 本監査 commit**」へ移す。
6. **`docs/audit/audit-tags.md` の `plan` 行の Slug 規約**。現在「plan filename stem (no `.md`)」だが
   in-tree の `plan:` slug は 2/2 とも `-plan` を落としている ⟹
   「**plan filename stem (no `.md`)。末尾の `-plan` は落としてよい**」を追記する。
   ⚠ **タグ側を直さない** — 片方だけ直すと `epi-debruijn-pertime-closure` と分裂する。
7. **自己申告 §4.4 / commit message の要約語「5 段中 3 段が通り」**。
   新: 「**sorryAx-free は 3 本 (`isClosed_setOf_inThm7` / `isClosed_thm7RegionOfLaw` /
   `finite_setOf_lt_thm7Cap`)、残る 2 本の段 (`isClosed_thm7RegionOfAuxReceiver` /
   `isClosed_thm7RegionOfInput`) は `sorry` を経由する配線であり、かつ訂正 3 のとおり headline への
   経路上に無い**」。⚠ **自己申告 §3-(5) の表は既に `sorryAx` と正しく書いており、訂正対象は
   要約語だけである** (表は動かさない)。

**訂正 7 件。うち主判定 (受け皿は昇格した / 中核 8 は 2 段が未閉) を動かすもの = 0 件。**

---

## 4. 生存の限界 (⚠ 本監査が「生存」と言った範囲)

- **生存するのは**: 受け皿 22 decl の署名の正直さ / `@residual` 2 本の分類 (`plan:`) / 転記の
  一次典拠との一致 (25 スロット・9 制約・6 適格性・濃度・入れ子) / 束縛子の取り替えが
  `thm7Region` の定める集合を変えないこと / 中核 8 が未閉であること。
- **生存しないのは**: 「`thm7Region` は `Thm7(W)` である」という**同一視**。軸 2 のとおり偏差が
  2 つあり向きが逆である ⟹ ⚠ **後続はこの def を `Thm7(W)` と呼び替えて使ってはならない**。
- ⚠ **本監査は `Thm7 ⊋ C` について何も言っていない**。レート領域の包含についても 1 文字も判定していない。
- ⚠ **`R₀ = 0` スライスの Π01 性 (子 §4-b / R-4) は本監査でも 1 行も触れていない**。
  被監査ファイルにも「3 レート版から従う」型の記述は無い (`rg` で確認) ⟹ **R-4 の違反は無い**。

## 5. 監査が確かめていないこと (⚠ 名指しする)

1. **`thm7Region W ≠ ∅`** — 機械で閉じていない。probe P4 は「スロットが全て 0 の法則が 1 つあれば
   原点が属する」までで、**その法則を構成していない** (原子は in-project に在る、軸 1-d)。
2. **`IsClosed (thm7Region W)` が真であること** — ⚠ **本監査は命題の真偽を判定していない**。
   偽であれば `@residual(plan:…)` は `defect:false-statement` へ落ちるが、**その反証も証明も試みていない**
   (有限周囲空間 + 情報量の連続性 + 閉じた法則集合から真である見込みは高いが、**見込みは判定ではない**)。
3. **述語の弱化が領域を真に大きくするか** — 上位集合であることは確実だが、**真の包含かは未検証**。
4. **典拠の濃度補題** (上限つきと上限なしの一致) — Lean 側で未形式化であり、本監査も検証していない。
5. **一次典拠の証明** — 1 行も読んでいない ⟹ **定理 7 の主張自体の正しさは対象外**。
6. **中核 9 (有界性) / 10 ((α) 合致)** — 被監査 commit が 1 行も触れておらず、本監査も評価していない。
7. **`InformationTheory.lean` の import 1 行以外の波及** — `git diff --name-only` の再実行で既存
   `.lean` に差分が無いことは確認したが、**下流の olean 再生成の影響は測っていない**。
8. **style gate の判断項目** — 本監査は honesty gate であり、`lean_doc_lint.ts` の機械層が
   **strict 10 / ratchet 4 すべて 0 件**であることのみ確認した (訂正 1 / 2 の後に再実行)。

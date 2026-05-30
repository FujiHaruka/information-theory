# T1-A'' Huffman 最適性 — 強形完遂計画 (2 hypothesis genuine discharge) 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A''. Huffman 最適性」
> - 前任 (T1-A' weak form publish 済): [`huffman-optimality-moonshot-plan.md`](./huffman-optimality-moonshot-plan.md)
>
> **Supersedes**: [`huffman-optimality-t1apprime-moonshot-plan.md`](./huffman-optimality-t1apprime-moonshot-plan.md)
> — 旧 plan は Hyp1 を permutation 等長化縮約鎖 (`EqualizingPermHypothesis` 系) で閉じる
> 想定だったが、その縮約鎖は **数学的に偽** (機械検証済反例、§現況) であり前提が崩れた。
> 旧 plan は参照のみ (Phase 切り方と判断ログ #1-#3 の prior として有効)。
>
> **Inventory**: [`huffman-optimality-t1apprime-mathlib-inventory.md`](./huffman-optimality-t1apprime-mathlib-inventory.md)
> (Phase 0 で再点検)
>
> **Status (2026-05-21)**: 計画起草。実装未着手。

## 進捗

- [x] Phase H1 — Hyp1 (SwapNormalization) ✅ **無条件 genuine discharge 済** (`swap_normalization_proof` → `swap_normalization_strong`、shorten + keystone + 2-swap)
- [~] Phase H2 — Hyp2 (Identification) を C1 決定的再定義で discharge: **部分前進 (2026-05-30)**
  - [x] H2-a/H2-b — 決定的 (colex) relabel cornerstone `huffmanLengthAux_relabel_det` + 6 補助 ✅ (`HuffmanColexDeterminism.lean`、sorryAx 非依存、`@audit:ok`)。docstring-only defect 解消
  - [✗] H2-c — collapse correspondence `collapseLabel_huffmanLengthAux` は **FALSE statement と確定** (2026-05-30、機械的反例 + 独立監査、`@audit:defect(false-statement)`、判断ログ #4)。**per-symbol collapse path は dead-end**。`MergedHuffmanAuxIdentHypothesis` 本体は `Draft/HuffmanWalls.lean:70` で honest sorry 据置
  - [ ] H2-d — `huffman_merged_identification_proof` publish (新 reduction 経路 closure 後)
- [ ] Phase H2 残 — **`MergedHuffmanAuxIdentHypothesis` discharge を leaf-merge / length-multiset reduction へ pivot** (新規設計、判断ログ #4): 次セッション target。per-symbol collapse (旧判断ログ #3 の tie-order 独立 invariant) は偽命題で放棄
- [ ] Phase M — 強形主定理 `huffmanLength_optimal` (hypothesis 引数なし、~5 行 wrapper) 📋
- [ ] Phase V — 全 file silent + `#print axioms huffmanLength_optimal` で sorryAx 非依存確認 📋
- 注: 別壁 Hyp2 `huffman_merged_identification_hypothesis_holds` (`HuffmanWalls.lean:63`, `@residual(plan:huffman-2hyp-vertical-reduction)`) も強形完遂には要 closure (別 plan)

proof-log: yes (Phase H2-a の C1 redefine と Phase H1-a の shorten 設計は迷走しやすいので残す)

## ゴール / Approach

### Goal (最終定理 signature)

`Common2026/Shannon/HuffmanOptimality.lean` 末尾追記 (新規 file は H2/H1 の規模次第、§設計判断):

```lean
namespace InformationTheory.Shannon.Huffman

/-- Hyp1 discharge — Cover–Thomas Lemma 5.8.1 (i). genuine, NOT a hypothesis pass-through. -/
theorem swap_normalization_proof : SwapNormalizationHypothesis.{u} := …

/-- Hyp2 discharge — huffmanLength identification on mergedMeasure. genuine. -/
theorem huffman_merged_identification_proof : HuffmanMergedIdentificationHypothesis.{u} := …

/-- **Cover–Thomas Theorem 5.8.1 (strong form)** — hypothesis 引数なし. -/
theorem huffmanLength_optimal
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_hypotheses
    swap_normalization_proof huffman_merged_identification_proof P hP l hl_pos hl_kraft

end InformationTheory.Shannon.Huffman
```

### Approach (overall strategy / shape of solution)

weak form の skeleton (`huffmanLength_optimal_with_hypotheses`,
`HuffmanOptimality.lean:1041`) は不変。それが取る 2 open hypothesis を genuine に閉じ、
無引数 wrapper を被せて publish する。2 hypothesis は **互いに独立な技術** で閉じ、
全体は次の 3 ブロックの shape を取る:

1. **Hyp2 (Identification) を先に閉じる — C1 = `huffmanStep` 決定的再定義。**
   現 `huffmanStep` は `Multiset.exists_min_image` + `Classical.choose`
   (`Huffman.lean:79-95`) で min を **非決定的**に選ぶため、carrier 型を越えた
   (`α` ↔ `{y // y ≠ b}`) trajectory 対応が一般に取れず、`MergedHuffmanAuxIdentHypothesis`
   (`HuffmanMergedIdentBody.lean:135`) が証明できない。`huffmanStep` を **canonical
   tie-break 付き決定的選択** に再定義すると、両 carrier の Huffman 再帰が relabel で
   合わさる。これは `huffmanLength` の foundation を変える invasive 変更 (§blast radius)
   なので、**Hyp1 構成より先**に行い、波及範囲を全部再検証してから Hyp1 を積む。

2. **Hyp1 (SwapNormalization) を Kraft 保持 multiset 構成で閉じる — 偽縮約鎖は捨てる。**
   旧 plan の permutation 等長化 (`EqualizingPermHypothesis`) は **偽**
   (permutation は語長 multiset を保存、相異語長の feasible `ll` は等長化不能、反例
   `ll = ![1,2,3]`)。代わりに **語長 multiset を変える** 3 段構成:
   (i) feasible `ll` (Kraft ≤ 1) を Kraft = 1 へ shorten (E 非増加)、
   (ii) Kraft = 1 完全符号で最長 2 leaf が等長 (keystone `exists_two_equal_longest`,
   `HuffmanSwapNormProof.lean:110`、**証明済**を黒箱 reuse)、
   (iii) least-probable 対 `(a, b)` を最長 2 leaf へ swap し等長化 (`swap_step_le`,
   `HuffmanOptimality.lean:650`、**証明済**を黒箱 reuse)。Hyp1 は現 `huffmanLength` を
   触らず **追加のみ** で閉じられるが、C1 redefine が先行すると Hyp1 が依存する補題の
   olean が変わるため、着手順は H2 → RV → H1 に固定 (§設計判断)。

3. **無引数 wrapper で強形 publish。** weak form に 2 genuine proof を渡すだけ (~5 行)。

**honesty 線**: 本タスクは標準B (無条件機械検証)。各 Phase の target は genuine
(型 ≠ trivial、`:= h` 循環禁止、`:True` スロット禁止)。特に **`SwapStepLeChainHypothesis`
系 (`HuffmanT1APPrimeBody.lean:56` 他) へ逃げない** — これは既に
`swapStepLeChainHypothesis_holds` で完全 discharge されているが、`ll a = ll b` の trivial
case しか `SwapNormalizationHypothesis` を閉じず、**強形には到達しない弱化述語**である。
偽縮約鎖 (`EqualizingPermHypothesis`/`EqualizingSwapTargetHypothesis`) の上にも積まない。

## 現況 (詳細)

### 主役 skeleton (不変、再利用)

- `huffmanLength_optimal_with_hypotheses` (`HuffmanOptimality.lean:1041`) — weak form。
  `(h_swap : SwapNormalizationHypothesis)` + `(h_ident : HuffmanMergedIdentificationHypothesis)`
  の 2 open hypothesis を取る。本 plan はこの 2 つを閉じる。
- 内部 motor: `huffmanLength_optimal_aux_with_hypotheses` (`:793`) — `Nat.strong_induction_on`。

### Hyp1 = `SwapNormalizationHypothesis` (`HuffmanOptimality.lean:759`)

任意 feasible `ll` (positive, Kraft ≤ 1) と least-prob 対 `(a,b)` (`_h_min`) に対し、
`l_norm a = l_norm b` かつ E 非増加・Kraft 維持の `l_norm` の存在。

- **既存縮約鎖は偽 (機械検証済、捨てる)**: `HuffmanSwapNormalizationBody.lean` の
  `EqualizingPermHypothesis` (`:110`) / `EqualizingSwapTargetHypothesis` (`:184`) は
  **FALSE** (`:91` `:175` に HONESTY ALERT + 反例 `ll = ![1,2,3]` 明記済)。permutation は
  語長 multiset を保つので相異語長の feasible `ll` は等長化できない。これらを経由する
  `swapNormalizationHypothesis_of_equalizingPerm` 等は「(偽前提) → 結論」の vacuous な
  含意 (循環でも `:True` でもないが discharge 不能)。**本 plan はこの鎖を一切使わない。**
- **証明済の道具 (黒箱 reuse)**:
  - `exists_two_equal_longest` (`HuffmanSwapNormProof.lean:110`) — Kraft = 1 完全符号は
    最長 leaf を 2 つ持つ。keystone `strict_kraft_one_implies_pairing` (`:67`,
    parity 論法) + `kraft_one_nat_sum` (`:34`)。HuffmanSwapNormProof.lean は Common2026
    依存ゼロの自己完結 file なので C1 redefine の影響を受けない (insulated)。
  - `swap_step_le` (`HuffmanOptimality.lean:650`) — 単発 `Equiv.swap a m` で
    `l a ≤ l m ∧ P{a} ≤ P{m}` の下 E 非増加・Kraft 不変、かつ `l' a = l m ∧ l' m = l a`。
- **唯一の非自明点 = shorten-to-Kraft=1** (H1-a): feasible (Kraft < 1) を Kraft = 1 へ
  E 非増加で到達させる。設計を Phase H1-a で詰める (§設計判断)。

### Hyp2 = `HuffmanMergedIdentificationHypothesis` (`HuffmanOptimality.lean:776`)

merged measure 上で `huffmanLength (mergedMeasure Q a b hab) x = (if x = a then
huffmanLength Q a - 1 else huffmanLength Q x)`。

- **measure 層は剥離済**: `HuffmanMergedIdentBody.lean` が
  `huffmanMergedIdentification_of_aux` (`:151`, genuine 完全証明) で原 hypothesis を
  primitive `MergedHuffmanAuxIdentHypothesis` (`:135`) へ縦分解済。残るのは
  `huffmanLengthAux` (= Huffman 再帰) を 2 carrier (`β` と `{y // y ≠ b}`) 間で関連付ける
  pure-combinatorics の対応。`mergedInitMultiset` (`:54`) は
  `Finset.univ.val.map` 由来の explicit multiset。
- **証明不能の根因 = `huffmanStep` の非決定性**: `Classical.choose ∘ exists_min_image`
  (`Huffman.lean:79-95`) で min を選ぶため、relabel (型変更) で list/sort 順が崩れ、
  trajectory 対応が一般に取れない。⇒ C1 (決定的再定義) で根を断つ。

### C1 blast radius (検証済、prompt の想定と相違あり)

**重要**: `huffmanStep` を使う file は **Huffman 系 3 file のみ** (`Huffman.lean`,
`HuffmanOptimality.lean`, `HuffmanMergedIdentBody.lean`)。`huffmanLength` まで広げても
反映先は Huffman* 6 file のみ。

- **依存方向は prompt の想定と逆**: `Huffman.lean` が `ShannonCode` / `ShannonCodeKraftReverse`
  を **import する側** (`Huffman.lean:8-9`)。`ShannonCode.lean` / `ShannonCodeKraftReverse.lean`
  には `huffman`/`Huffman` の参照が **ゼロ** (grep 確認済)。⇒ **C1 は Ch.5 へ波及しない。**
  Phase RV の Ch.5 再検証は「波及しないことの確認」だけで、修正は発生しない見込み。
- 実際の再検証対象 (`Huffman.lean` を transitively import する file):
  `HuffmanOptimality.lean`, `HuffmanMergedIdentBody.lean`, `HuffmanT1APPrimePartial.lean`,
  `HuffmanT1APPrimeBody.lean`, `HuffmanSwapStepChainBody.lean`,
  `HuffmanSwapNormalizationBody.lean`。`HuffmanSwapNormProof.lean` は Common2026 依存ゼロで
  insulated。
- C1 で **シグネチャは変えない** (`huffmanStep : … → { p // <同じ spec> }`) のが目標。
  本体の選択ロジックだけ差し替えれば、`huffmanStep_spec`/`_grouping`/`_card_eq`/`_card_lt`
  /`huffmanLengthAux_eq_step` 等の **statement は不変** のまま証明だけ追従させられる
  (これが成立すれば下流 6 file の再検証はほぼ no-op)。これを Phase H2-a の設計目標とする。

## 設計判断

### 着手順: H2 (C1 redefine) → RV → H1 (確定)

- **H2 を先**。理由: C1 は `huffmanStep` の本体を差し替える foundation 変更。Hyp1 構成
  (H1) は `swap_step_le` (`huffmanStep` 非依存) と `exists_two_equal_longest` (insulated
  file) を使うので C1 後でも壊れないが、**H1 を先に積むと C1 redefine 時に olean refresh が
  必要になり二度手間**。先に foundation を確定 (H2 + RV で全 file silent) してから H1 を
  追加するのが安全。
- 旧 plan は H1 (Phase A) を先に置いていたが、それは Hyp1 を「現 huffmanLength 上の追加のみ」
  で閉じられる前提だった。C1 redefine を採る以上、foundation を先に固める順が正しい。

### C1 = `huffmanStep` 決定的選択の具体形

carrier は `Multiset (Finset α × ℝ)`。決定的に「最小確率 2 group」を選ぶには canonical
順序が要る。採用候補と判定:

- **採用案 (D1): `Multiset.sort` で canonical list 化 → 先頭 2 件を取る。**
  `Multiset.sort (r)` (`Mathlib.Data.Multiset.Sort`、既に `Huffman.lean:4` で import 済) を
  carrier `Finset α × ℝ` 上の **全順序 `r`** で適用し、`r` を「第 1 キー = 確率 `p.2`
  昇順、第 2 キー (tie-break) = group `p.1` の canonical 順」とする。`r` が `IsTotal` +
  `IsTrans` + `IsAntisymm` (実質 `LinearOrder` か、tie に強い total preorder) なら
  `Multiset.sort` は well-defined で、`x1 = (sort s).head`, `x2 = (sort s).tail.head`。
  - tie-break key: `Finset α` 上の canonical 順。`α` が `Fintype` + `DecidableEq` なので
    `Finset α` 上に `Multiset.sort`/`Finset.sort` 経由の lex 順、または `Finset` を
    `Finset.val.sort` で list 化した lex 比較が立つ。**最終的に group 第一要素 (singleton の
    場合 `α` の元) を tie-break に使えれば十分** — merged group が出るのは内部 node だけで、
    `mergedInitMultiset` の全 group は singleton から始まる。
  - spec 補題への影響: `huffmanStep_spec` 等の **結論は不変** (依然「min 2 件を merge した
    multiset」)。min 性 (`∀ z ∈ s, x1.2 ≤ z.2`) は `Multiset.sort` の `pairwise_sort` +
    `mem_sort` から取り直す。証明だけ差し替え。
- **却下案 (D2): `Multiset.exists_min_image` を残し tie だけ決定化** — `Classical.choose`
  が残る限り cross-type 対応が取れないので不可。
- **重大リスク = cross-type 対応 (H2-b の core risk)**: relabel `α` ↔ `{y // y ≠ b}` で
  **sort 順が対応するか**。Huffman pivot が「型越え list 順対応が新 core risk」と指摘した点。
  - 見込み: `mergedInitMultiset` は `Finset.univ.val.map (fun x => ({x}, prob x))`
    (`HuffmanMergedIdentBody.lean:57`) 由来。tie-break key を **group の確率値と、確率が
    等しいときは `α` の Fintype 順** にすれば、subtype `{y // y ≠ b}` 側の Fintype 順は
    `α` 側の順の制限なので、`b` を除いた leaf 集合上で sort 順が `α` 側の sort の部分列に
    なる ⇒ 対応が取れる見込み。ただし merged group が確率 tie で leaf と衝突するときの
    tie-break が両 carrier で一致するかを Phase 0 probe で確認。
  - 対応補題の形: 「`s` と relabel された `s'` で `sort` 結果が relabel で写り合う」
    (`Multiset.map_sort` 系を使う) を H2-b で genuine に証明。これが core 残タスク。

### C1 が取れない場合の fallback = C3 (retreat line)

C1 の cross-type 対応がどうしても取れない (H2-b で sort 順 relabel 対応が破綻) 場合、
`huffmanStep` を再定義せず、**`huffmanLengthAux` の値が min 選択の tie に依らない**
(swap-invariance of length under equal-probability ties) を additive 補題として直接証明
する (~150-300 行、refactor なし)。`Classical.choose` を残したまま「どの min を選んでも
語長関数は同じ」を示し、その下で cross-type 対応を取る。撤退条件と切替の判断は判断ログへ。
honesty: C3 も genuine 証明 (tie-invariance の補題)。`:True`/循環には逃げない。

### Hyp1 shorten-to-Kraft=1 (H1-a) の設計

feasible `ll` (Kraft < 1) を Kraft = 1 へ E 非増加で到達。subset-sum reachability は重いので
**「最短 leaf を 1 つ縮める」操作の反復**で十分かを設計で詰める:

- 1 操作: 最短語長 leaf `c` を `ll c - 1` に縮める → Kraft 和は `2^(-(l c)) → 2^(-(l c)+1)`
  で増える (1 項が倍)、E は `P{c}` だけ減る (非増加)。Kraft が 1 を超えない範囲で反復し、
  到達できなければ別 leaf を縮める。
- 懸念: 反復で **ちょうど Kraft = 1** に着地できる保証 (整数語長の格子上で 1 を飛び越えない
  か)。Kraft 値は `2^(-k)` の和なので、最短 leaf を縮めると最小増分が他項以上になり得る。
  H1-a で「最短 leaf を縮める操作で Kraft ≤ 1 を保ちつつ厳密増加させ、有限回で = 1 に
  到達」を ℕ 値 Kraft (`kraft_one_nat_sum` の逆向き、`2^M` スケール) の格子論法で示せるか
  Phase 0 で 1 行 probe。
- 代替: shorten を「Kraft = 1 へ」ではなく「Kraft ≤ 1 のまま最長 2 leaf 等長化に十分な
  Kraft = 1 部分符号へ埋め込む」形に弱められるか (keystone は Kraft = 1 を要求するので
  最終的に = 1 が必要)。H1-a の主リスク。設計が固まらなければ判断ログに記録し H1 を後回し
  (H2 だけ先に publish して partial 前進を確保) する撤退も可。

### file 配置

- H2-a の C1 redefine は `Huffman.lean` 本体の編集 (新規 file 不可、定義そのものの差し替え)。
- H2-c/H2-d は `HuffmanMergedIdentBody.lean` (primitive の証明) + `HuffmanOptimality.lean`
  末尾 (`huffman_merged_identification_proof` publish)。
- H1 は `HuffmanOptimality.lean` 末尾追記が基本。規模が ~500 行を超えるなら
  `HuffmanSwapNormCompletion.lean` 新規 file へ分離 (判断ログで決定)。
- Phase M wrapper + Phase V は `HuffmanOptimality.lean` 末尾。

## Phase 詳細

### Phase 0 — 在庫再確認 + 設計 probe 📋

- [ ] inventory (`huffman-optimality-t1apprime-mathlib-inventory.md`) を再点検、偽縮約鎖
      前提の項目を無効化メモ (inventory file は別エージェント所掌なので **読むだけ**)。
- [ ] `Multiset.sort` の API 確認 (`sort_eq` `mem_sort` `map_sort` `coe_sort` `sort_cons`
      `pairwise_sort` — 全て `Mathlib.Data.Multiset.Sort`、import 済)。`Finset α` 上の
      canonical 順 (tie-break) に使える順序型クラスを 1 行 probe。
- [ ] cross-type 順序対応の 1 行 probe: `Multiset.map_sort` で relabel 後 sort が relabel
      sort に写るかの statement を skeleton で型チェック (証明は H2-b)。
- [ ] H1-a shorten 格子論法の 1 行 probe (`2^M` スケール ℕ Kraft の到達可能性)。

### Phase H2 — Hyp2 を C1 で discharge 📋

- [ ] **H2-a**: `Huffman.lean` の `huffmanStep` 本体を D1 (sort ベース決定的選択) に再定義。
      signature `{ p // <既存 spec 4 件> }` は不変。spec 補題 `huffmanStep_spec` (`:231`)
      / `_grouping` (`:244`) / `_card_eq` (`:251`) / `_card_lt` (`:267`) /
      `huffmanLengthAux_eq_step` (`:305`) の statement を保ったまま証明追従。
      target: `Huffman.lean` 単体 silent。規模 ~150-250 行 (本体 + min 性の取り直し)。
- [ ] **H2-b**: relabel (`α` ↔ `{y // y ≠ b}`) で sort 順が対応する補題を genuine 証明。
      core risk。`Multiset.map_sort` 系利用。target: cross-type sort 対応補題 silent。
      規模 ~100-200 行。**ここで破綻したら C3 へ切替** (判断ログ #N)。
- [ ] **H2-c**: `MergedHuffmanAuxIdentHypothesis` (`HuffmanMergedIdentBody.lean:135`) を
      H2-b の対応 + `huffmanLengthAux` strong induction で genuine 証明。
      target: `theorem mergedHuffmanAuxIdent_proof : MergedHuffmanAuxIdentHypothesis.{u}`
      (型 = primitive predicate、`:= by` で実証明)。規模 ~150-250 行。
- [ ] **H2-d**: `huffman_merged_identification_proof : HuffmanMergedIdentificationHypothesis`
      を `huffmanMergedIdentification_of_aux mergedHuffmanAuxIdent_proof` で publish
      (`HuffmanMergedIdentBody.lean:151` の wrapper を黒箱 reuse、~3 行)。

### Phase RV — C1 blast radius 再検証 📋

- [ ] `lake build Common2026.Shannon.Huffman` で olean refresh 後、下流 6 Huffman* file を
      個別 `lake env lean` で silent 確認 (HuffmanOptimality, HuffmanMergedIdentBody,
      HuffmanT1APPrimePartial, HuffmanT1APPrimeBody, HuffmanSwapStepChainBody,
      HuffmanSwapNormalizationBody)。
- [ ] Ch.5 (`ShannonCode.lean`, `ShannonCodeKraftReverse.lean`) を確認のため `lake env lean`
      (依存方向上 **波及しない見込み**、修正 0 を確認するだけ)。

### Phase H1 — Hyp1 を Kraft 保持構成で discharge 📋

- [ ] **H1-a**: shorten-to-Kraft=1。feasible `ll` を Kraft = 1 へ E 非増加で到達する補題。
      target: `∃ l1, (∀ x, 0 < l1 x) ∧ Kraft l1 = 1 ∧ E[l1] ≤ E[ll]`。規模 ~120-200 行
      (設計次第、§設計判断)。最大リスク。
- [ ] **H1-b**: `exists_two_equal_longest` (`HuffmanSwapNormProof.lean:110`) を H1-a の
      Kraft = 1 `l1` に適用、最長 2 leaf `c₁ ≠ c₂` で等長を取得 (黒箱 reuse、~10 行)。
- [ ] **H1-c**: least-prob 対 `(a,b)` (`_h_min`) を最長 2 leaf `c₁,c₂` へ `swap_step_le`
      (`HuffmanOptimality.lean:650`) で swap、`l_norm a = l_norm b` を構成 (黒箱 reuse +
      2 回 swap の合成、~80-150 行)。
- [ ] **H1-d**: `swap_normalization_proof : SwapNormalizationHypothesis` publish
      (H1-a/b/c を組み上げ、`l_norm` の 4 条件 = positive/Kraft≤1/`l_norm a = l_norm b`/
      E 非増加 を充足、~30 行)。

### Phase M — 強形主定理 📋

- [ ] `huffmanLength_optimal` (hypothesis 引数なし) を
      `huffmanLength_optimal_with_hypotheses swap_normalization_proof
      huffman_merged_identification_proof …` で publish (~5 行)。
      `Common2026.lean` の import は既存 (Huffman* は登録済)、新規 file 作成時のみ追記。

### Phase V — 検証 📋

- [ ] 触れた全 file で `lake env lean <file>` silent (0 sorry / 0 warning)。
- [ ] `#print axioms huffmanLength_optimal` で `sorryAx` 非依存を確認 (= 標準B 達成)。
      `Classical.choice` / `propext` / `Quot.sound` のみが許容。
- [ ] 偽縮約鎖 file (`HuffmanSwapNormalizationBody.lean`) は HONESTY ALERT 付きで残存 OK
      (本 plan は使わない、削除は別タスク)。

## 撤退ライン

- **H2-b 破綻 (sort 順 cross-type 対応が取れない)** → C3 (tie-invariance 補題) へ切替。
  `huffmanStep` 再定義を撤回し、`Classical.choose` を残したまま「語長は tie 選択に不変」を
  genuine 証明。判断ログに切替記録。
- **H1-a 破綻 (shorten-to-Kraft=1 の格子論法が固まらない)** → H2 だけ先に publish して
  partial 前進を確保 (Hyp2 discharge 済 + Hyp1 open の中間 wrapper
  `huffmanLength_optimal_with_swap_and_aux` 系を H1 抜きで再公開)。Hyp1 は別 seed へ。
- **各 Phase 共通**: 行き詰まったら honest な名前付き仮説 (型 ≠ 結論、docstring で
  「load-bearing / NOT a discharge」明示) で抜く。**禁止**: 偽縮約鎖
  (`EqualizingPermHypothesis`) の上に積む / 弱化述語 `SwapStepLeChainHypothesis` 系へ逃げて
  「強形 discharge」と称する / `:= h` 循環 / `:True` スロット / `sorry`。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-21 起草 — 旧 plan supersede + 着手順 H2→RV→H1 確定**: 旧
   `huffman-optimality-t1apprime-moonshot-plan.md` は Hyp1 を permutation 等長化縮約鎖で
   閉じる前提だったが、その鎖が機械検証で偽と判明 (`HuffmanSwapNormalizationBody.lean`
   HONESTY ALERT)。本 plan は (a) 偽鎖を捨て Kraft 保持 multiset 構成で Hyp1 を閉じ、
   (b) Hyp2 は C1 = `huffmanStep` 決定的再定義で根を断つ。着手順は旧 plan の H1 先行を
   覆し、foundation 変更 (C1) を先に固める H2→RV→H1 に変更。
2. **2026-05-21 起草 — C1 blast radius が prompt 想定と相違 (Ch.5 へ波及しない)**:
   prompt は「C1 が Ch.5 `ShannonCode*` 依存に波及、要全再検証」と想定していたが、grep で
   依存方向は逆 (`Huffman.lean` が ShannonCode を import する側、ShannonCode 側に Huffman
   参照ゼロ) と確認。C1 の実 blast radius は `Huffman.lean` を import する Huffman* 6 file
   のみ。`HuffmanSwapNormProof.lean` (keystone) は Common2026 依存ゼロで insulated。
   Phase RV の Ch.5 再検証は「波及しないことの確認」に縮小。
3. **2026-05-30 — Hyp1 既 discharge 確認 + 決定的 relabel cornerstone genuine 化 + collapse は Case B 撤退**:
   実コード確認で **Hyp1 (SwapNormalization) は既に `swap_normalization_proof` で無条件 genuine
   discharge 済** (Phase H1 完了)。残 frontier = Hyp2 系 primitive `MergedHuffmanAuxIdentHypothesis`
   (= `merged_huffman_aux_ident_hypothesis_holds`, `Draft/HuffmanWalls.lean:70`, honest sorry 据置)。
   - **genuine 前進**: `HuffmanColexDeterminism.lean` は着手前 **docstring-only (declaration 0 個)**
     で「Section I cornerstone 確立済」と完了形記述する tier-5 寄り誤誘導だった。本 session で
     **無条件 (NodupChain 不要) relabel cornerstone `huffmanLengthAux_relabel_det` + 6 補助を genuine
     実装** (sorryAx 非依存、honesty audit で 7 件 `@audit:ok`)。Phase H2-a/H2-b の決定的 step-correspondence
     が確立。
   - **collapse correspondence は閉じず (Case B 撤退)**: `collapseLabel_huffmanLengthAux`
     (`HuffmanColexDeterminism.lean:316`, honest sorry + `@residual(plan:huffman-strong-form-completion)`)。
     **壁の正体 = Huffman 語長の tie-order 独立性**: collapse も first-step identification も同根で、
     `groupKey ({a},p)=(p,toColex{a})` と `({a,b},p)=(p,toColex{a,b})` が同確率 `p` で colex 異なるため、
     `rest` に `toColex{a} < toColex g < toColex{a,b}` な同確率 group があると singleton 木と card-2 木の
     merge 順が食い違い naive lockstep 帰納が閉じない。必要なのは「Huffman 語長は確率 multiset で決まり
     tie-break (colex) 選択に依らない」**tie-order 独立 invariant の機械化** (~150-250 行 + tie 場合分け)。
     これは Mathlib 壁でも C3 (tie-invariance、within-tree) でもなく、cross-tree 構造の自作補題。次セッション target。
   - **次の前提整備**: 本 cornerstone closure 後、`HuffmanMergedIdentBody.lean:117` の load-bearing-predicate
     wrapper 群 (`@audit:retract-candidate`) が tier 2→1 化可能になる (incidental migration の前提が整った)。
4. **2026-05-30 — collapse 補題 `collapseLabel_huffmanLengthAux` は FALSE statement と確定 (judgment #3 の壁診断は誤り)**:
   判断ログ #3 はこの補題を「tie-order 独立 invariant が要る true-but-hard な壁 (~150-250 行)」と診断したが、
   実装着手前の small-case シミュレーションで **statement 自体が偽**と判明、独立 honesty-auditor が反例を
   step-by-step 検算 + Mathlib `Colex.toColex_lt_toColex_iff_max'_mem` (Colex は max-element 優位) で confirm。
   - **反例** (`a=1, b=6, p=4`, `rest={({0},4),({2},4),({3},3),({4},6),({5},3)}`、consumer precondition 下でも 84230/2M trials):
     決定化 `huffmanStep` の tie-break は `groupKey = (prob, toColex label)`。label を `{1}→{1,6}` に拡げると
     `toColex {1,6} > toColex {2}` (6 が max) になり、同確率 prob-4 group 間の min-2 選択が `{0}+{1}→{0}+{2}` に反転、
     `z=2` (`≠a,≠b`) の depth が `2→3` に動く。`S₁` 側 depth(2)=2、`S₂` 側 depth(2)=3。
   - **根因**: `huffmanLengthAux` の depth は colex tie-break order に**依存する** (= tie-order 独立**でない**)。
     よって「colex を変える relabel 下の per-symbol 不変性」を主張する collapse statement は偽。judgment #3 の
     「tie-order 独立 invariant」前提が誤りだった。同じ決定化 (Section I の `@audit:ok` cornerstone を unlock) が
     collapse 系の per-symbol 不変性を**破る**方向に働く設計上の緊張。
   - **tag**: `@residual(plan:...)` → `@audit:defect(false-statement) @audit:retract-candidate @audit:closed-by-successor(huffman-strong-form-completion)`。standalone (consumer 0、伝播ゼロ)。
   - **次セッション設計 pivot**: per-symbol collapse は dead-end。`MergedHuffmanAuxIdentHypothesis`
     (`HuffmanMergedIdentBody.lean:124`) の discharge は (a) 確率 multiset 同一性 (`S₁`/`S₂` の確率は完全一致) から
     得る length-multiset / 期待長レベルの不変量、または (b) Cover-Thomas 5.8.1 本来の leaf-merge 逆操作 (merged tree
     最適性の lifting) に切り替える。`_h_sibling : huffmanLength Q a = huffmanLength Q b` は un-merged tree `Q` 上の
     性質で per-symbol collapse を直接救わない。
   - **教訓**: 撤退ライン設計で「閉じない (hard)」と「偽 (false)」を区別する verify step (small-case sim) を必須化。
     statement を信じて 200 行の invariant 機械化に着手していたら偽命題の証明で必ず行き詰まっていた。
5. **2026-05-30 — `MergedHuffmanAuxIdentHypothesis` 本体も FALSE と確定 (collapse 補題だけでなく primitive 本体が偽)**:
   判断 #4 は collapse 補題 (`collapseLabel_huffmanLengthAux`) を偽と確定したが、`MergedHuffmanAuxIdentHypothesis`
   **本体 (primitive predicate そのもの)** は「strong precondition (a,b first-merged 対) なら成立」と旧 docstring が
   主張していた。本 session で **本体も機械的に FALSE と確定** (反例構成 + 独立網羅検証)。
   - **反例** (`docs/shannon/verify/merged_huffman_aux_ident_counterexample.py`、機械検証済):
     β={0,1,2,3} (card 4)、weights `[1,2,1,1]`、`a=0`, `b=2`。全強前提 (a global-min / b rest-min / a≠b /
     `huffmanLength Q 0 = huffmanLength Q 2 = 2`) を充足し、**かつ a,b は実際に first-merged 対**
     (元木の最初の merge = {0},{2}) だが、x=0 で恒等式が要求する `huffmanLength Q a - 1 = 1` に対し merged
     depth = 2 で MISMATCH (x=1 でも depth 1 vs 期待 2 で失敗)。tie が無ければ恒等式は常に成立
     (870 distinct-weight case で反例 0)。
   - **根本原因**: 決定的 colex tie-break が merge 操作で不安定。merge 後 singleton {0}(確率 2/5) が再 Huffman で
     {3}(1/5) と先に対になり depth 2 に戻り、元木の {0,2} 部分木を collapse した構造に**対応しない**。collapse
     補題 (判断 #4) と同根。「strong precondition で救える」という旧 docstring 主張は誤り。
   - **帰結**: per-symbol depth identity を介する merged-identity 経路 (`MergedHuffmanAuxIdentHypothesis` /
     `HuffmanMergedIdentificationHypothesis` / combined walls) は**全体が dead**。`Draft/HuffmanWalls.lean` の
     wall 2 件は `@audit:defect(false-statement) @audit:retract-candidate(deterministic-colex-merge-instability)`
     に reclassify (sorry は false-statement の honest marker として残置)、combined/chain-combined 2 件は
     transitively false-premised (`@audit:defect(false-statement)`)。
   - **pivot 方向**: tie-invariant な **cost-level merge identity**
     (`expectedLength(huffman Q) = expectedLength(huffman mergedMeasure) + (Q{a}+Q{b})`) へ。cost は tie-break
     不変なので決定的 colex でも成立見込み。あるいは exchange-argument による任意 optimal code 経由。per-symbol
     (depth/length 単位) の identity は決定的 tie-break と相性が悪く、cost/expected-length 単位に上げるのが鍵。

# T1-A'' Huffman 強形 完遂 — `huffmanStep` colex 決定化で Hyp2 discharge 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) 章対応進捗 Ch.5 行 + frontier 節 (Huffman 強形) + 判断ログ #4/#6 (詳細経緯は `git log -- docs/textbook-roadmap.md` の 2026-05-26 整理前 commit 旧 #17/#19)
> - 前任 (Hyp1 genuine discharge 済): [`huffman-strong-form-completion-plan.md`](./huffman-strong-form-completion-plan.md)
>
> **Supersedes (真壁判定の撤回)**: 旧 textbook-roadmap 判断ログ #19 (現 #6 に統合、詳細は git log) + `HuffmanMergedAuxIdent.lean` Section E が
> Hyp2 (`MergedHuffmanAuxIdentHypothesis`) の確率 tie 一般ケースを「定義 artifact の真壁」と
> 判定したが、これは **早計** だった。判定根拠「決定的 huffmanStep に必要な
> `LinearOrder (Finset α)` が Mathlib に無い」は `Fintype.equivFin` (任意順序、subtype に
> 制限されない) だけ試した結果であり、**`[LinearOrder α]` を構造的仮説として加えれば
> `Finset.Colex.instLinearOrder` で道がある** ことを本 plan の起草前 probe で確認済。
> 旧判定 (#19, Section E) は撤回。ただし旧判断ログ entry 自体は append-only なので残す。
>
> **Status**: CLOSED ✅ — superseded。Hyp2 は cost-level pivot ([`huffman-cost-level-optimality-plan.md`](./huffman-cost-level-optimality-plan.md)) で別経路に無条件 genuine 達成 (`huffmanLength_optimal`、状態は roadmap Ch.5 が SoT)。本 route の relabel-determinization コード (`ColexDeterminism.lean` / `MergedAuxIdent.lean` / `FirstStepProbe.lean`) は consumer-0 dead と確定し削除済 (2026-06-13)。以下本文は探索記録 (historical)。

## 進捗

- [ ] Phase 0 — 在庫再確認 + colex 決定化の cross-type probe (skeleton 型チェックのみ) 📋
- [ ] Phase D — `huffmanStep` を colex 決定化 (`Huffman.lean` 本体差し替え、signature 不変) 📋
  - [ ] D-a — 決定的 key 型 `groupKey : Finset α × ℝ → ℝ ×ₗ Colex (Finset α)` と min 選択
  - [ ] D-b — 全 spec 補題 (`_spec`/`_min_fst`/`_min_snd`/`_grouping`/`_card_*`/`_eq_step`) 証明追従
  - [ ] D-c — `[LinearOrder α]` を `variable` に追加、`Huffman.lean` 単体 silent
- [ ] Phase RV — 決定化 blast radius 再検証 (Huffman* 系 + Ch.5 無影響確認) 📋
- [ ] Phase H2 — Hyp2 (`MergedHuffmanAuxIdentHypothesis`) を決定性で genuine discharge 📋
  - [ ] H2-a — `huffmanLengthAux_relabel` の `NodupChain` 前提を外す (決定的 min は無条件 relabel 可換)
  - [ ] H2-b — first-step identification: 決定的 min が `{a}`,`{b}` を merge することを示す
  - [ ] H2-c — collapse correspondence: card-2 merged group → singleton (carrier `β`↔`{y≠b}`)
  - [ ] H2-d — `mergedHuffmanAuxIdent_proof : MergedHuffmanAuxIdentHypothesis` を組み上げ
- [ ] Phase M — 無引数強形 `huffmanLength_optimal` を `huffmanLength_optimal_modulo_aux_ident` に被せて publish 📋
- [ ] Phase V — 全 file silent + `#print axioms huffmanLength_optimal` で sorryAx 非依存確認 📋

proof-log: yes (Phase D の colex key 設計と Phase H2-a/c の cross-type 対応は迷走しやすい)

## ゴール / Approach

### Goal (最終定理 signature)

`InformationTheory/Shannon/HuffmanStrongForm.lean` 末尾追記 (または同 namespace 新規 file、§file 配置):

```lean
namespace InformationTheory.Shannon.Huffman

/-- Hyp2 discharge — `MergedHuffmanAuxIdentHypothesis` を決定的 huffmanStep で genuine
discharge. NOT a hypothesis pass-through (型 = primitive predicate、`:= by` で実証明). -/
theorem mergedHuffmanAuxIdent_proof : MergedHuffmanAuxIdentHypothesis.{u} := …

/-- **Cover–Thomas Theorem 5.8.1 (strong form)** — 引数 hypothesis なし.
`[LinearOrder α]` のみ構造的仮説として追加 (load-bearing でない、§honesty). -/
theorem huffmanLength_optimal
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [LinearOrder α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_modulo_aux_ident mergedHuffmanAuxIdent_proof P hP l hl_pos hl_kraft

end InformationTheory.Shannon.Huffman
```

### 現況の正確な残スコープ (前 session 成果の上に立つ)

Hyp1 は **genuine discharge 済** (`swap_normalization_proof : SwapNormalizationHypothesis`,
`HuffmanStrongForm.lean:144`)。headline `huffmanLength_optimal_modulo_aux_ident`
(`HuffmanStrongForm.lean:174`) は **Hyp1 を被せ済**で、残る open hypothesis は
`MergedHuffmanAuxIdentHypothesis` (`HuffmanMergedIdentBody.lean:135`) **1 つだけ**。
本 plan の本体は **この primitive 1 つを閉じる**こと。measure 層も既に剥離済
(`huffmanMergedIdentification_of_aux`, `HuffmanMergedIdentBody.lean:153`、完全証明)。

### Approach (overall strategy / shape of solution)

判断ログ #19 / `HuffmanMergedAuxIdent.lean` Section E が列挙した Hyp2 の 3 障害
((i) first-step identification が tie で `Classical.choose` の不透明な tie 破りで a,b 以外を
選びうる、(ii) `mergedInitMultiset` が一般に `NodupChain` 不成立、(iii) naive per-symbol
invariance が反例で偽) は **すべて `huffmanStep` の非決定性に根ざす**。これを 1 点で断つ:

**`huffmanStep` の min 選択を colex 決定化する。**

1. **決定化 (Phase D) — `Classical.choose ∘ exists_min_image` を canonical 決定的 min に。**
   `[LinearOrder α]` を構造的仮説として追加すると、`Finset.Colex.instLinearOrder`
   (`Colex.lean:272`) から `LinearOrder (Colex (Finset α))` が立つ。これで group の比較キーを
   **2 段 lex**「第 1 = 確率 `p.2` 昇順、第 2 (tie-break) = `toColex p.1` (colex)」とする
   全順序が `Finset α × ℝ` 上に得られ、min が **一意に決定**する。signature
   (`{ p // <既存 spec 4 件> }`) は不変に保つのが設計目標 — そうすれば下流 spec 補題の
   statement は不変で証明だけ追従する。

2. **cross-type 対応が無条件に成立 (Phase H2-a/b/c) — colex は strict-mono embedding で保存。**
   既存 `HuffmanMergedAuxIdent.lean` Section B の no-ties 機構 (`huffmanStep_fst/snd_relabel`,
   `huffmanLengthAux_relabel`) は「probabilities が distinct なら min が一意」に依存して
   `NodupChain` を要求していた。決定化後は min は **常に一意** (確率 tie は colex で破られる)
   なので `NodupChain` 前提が **不要になる**。carrier 横断対応の核は:
   `subtypeNeEmbedding b` の underlying `Subtype.val` は **`Subtype.strictMono_coe`
   (`Order/Monotone/Defs.lean:497`) で strict-mono** → `Finset.map_eq_image`
   (`Data/Finset/Image.lean:293`) で `relabelGroup` の `Finset.map e` を `Finset.image e` に
   書き換え → **`toColex_image_le_toColex_image (hf : StrictMono f)`
   (`Colex.lean:396`) で colex 順が carrier 横断で保存される**。よって決定的 min は relabel と
   無条件に可換になり、障害 (ii)(iii) が消える。障害 (i) (first-step identification) も決定的
   min なら「`{a}` (確率 global-min) と `{b}` (rest-min) が forced で選ばれる」を strong
   precondition (`_h_a_min`/`_h_b_min`/`_h_sibling`) から直接証明できる (tie の場合の colex
   tie-break まで pin down 可能)。

3. **collapse correspondence (Phase H2-c) — relabel では非被覆な構造変更を決定性で橋渡し。**
   first-step 後の β 側残木 `s''` は card-2 group `{a,b}@(Q{a}+Q{b})` を含むが、
   `mergedInitMultiset` 側では a-merged は **singleton** `{⟨a,_⟩}@(Q{a}+Q{b})`。両者を結ぶのは
   card-2 group → singleton の collapse (relabel = cardinality 保存 では非表現)。決定化で
   両 carrier の再帰が lockstep に進むため、collapse + relabel の合成補題を genuine に書ける
   (`huffmanLengthAux_const_on_group`, `Huffman.lean:524` で値保存を併用)。

4. **無引数 publish (Phase M)。** `huffmanLength_optimal_modulo_aux_ident` に
   `mergedHuffmanAuxIdent_proof` を渡すだけ (~5 行)。

**honesty 線**: 標準B (無条件機械検証)。`[LinearOrder α]` は **構造的仮説 (regularity)
であって load-bearing でない** — 有限アルファベットには常に入れられ、Huffman optimality の
内容 (どの tie-break でも optimal、最終定理は full optimality の不等式のまま) を変えない。
判断ログ #19 で「`[LinearOrder α]` 下で publish は standardB regularity か load-bearing か
境界」と書かれたが、決定的選択は単に**実装上 1 つの最適木を選ぶ tie-break**であって、定理の
結論を弱めも前提化もしない (full-support `hP` と同類の regularity)。よって標準B 完成として
許容。`:= h` 循環 / `:True` スロット / 退化定義 / 弱化述語への逃避は禁止。各 Phase target は
genuine (型 ≠ trivial)。Section E が禁じた fake residual hypothesis
(`MergedHuffmanAuxIdentTieResidual` 等) も導入しない — 本 plan は primitive を **直接** 閉じる。

## 現況 (詳細)

### 確定済み資産 (再利用、前 session 成果)

- **Hyp1 完了**: `swap_normalization_proof : SwapNormalizationHypothesis`
  (`HuffmanStrongForm.lean:144`、shorten-to-Kraft=1 + keystone + 2-swap の genuine 証明)。
- **headline (Hyp1 被せ済・Hyp2 のみ open)**: `huffmanLength_optimal_modulo_aux_ident`
  (`HuffmanStrongForm.lean:174`、sorryAx 非依存)。Phase M の wrapper はこれに被せる。
- **measure 層剥離済**: `huffmanMergedIdentification_of_aux`
  (`HuffmanMergedIdentBody.lean:153`、完全証明) で原 Hyp2 → primitive
  `MergedHuffmanAuxIdentHypothesis` (`:135`) へ縦分解。`mergedInitMultiset` (`:54`) は
  measure-free な explicit multiset。
- **relabel 基盤 (HuffmanMergedAuxIdent.lean、487 行、0 sorry)**:
  - Section A: `relabelGroup`/`relabelMultiset` + 7 補題 (`_injective`/`_card`/`_grouping`/
    `_snd`/`_erase`/`_mem`/`_nodup_snd`)。`relabelGroup e = (p.1.map e, p.2)`、すなわち
    **`Finset.map e` を使う** — Phase H2 で `Finset.map_eq_image` で `image` に橋渡しが必要。
  - Section B: `huffmanStep_fst/snd_relabel`, `huffmanStep_step_relabel`,
    `min_unique_of_nodup_snd` — **すべて `NodupChain` (= no-ties) 前提**。Phase H2-a で決定化に
    合わせて前提を外す (or 並行版を新設)。
  - Section C: cornerstone `huffmanLengthAux_relabel` (NodupChain 下の carrier-embedding
    relabel-invariance、strong induction)。Phase H2-a で NodupChain 前提を外す。
  - Section D: `subtypeNeEmbedding b = Function.Embedding.subtype _` (`:429`),
    `huffmanLengthAux_mergedInitMultiset_relabel` (`:436`、NodupChain 前提下の subtype 解消)。
- **min 性 accessor (Huffman.lean)**: `huffmanStep_min_fst` (`:246`),
  `huffmanStep_min_snd` (`:266`) — 定義本体の `Classical.choose_spec` を `unfold huffmanStep` で
  取り出す。**決定化で証明書き換え、statement 維持**。
- **値保存**: `huffmanLengthAux_const_on_group` (`Huffman.lean:524`) — collapse で値が
  保たれることに使う。

### Hyp2 = `MergedHuffmanAuxIdentHypothesis` (`HuffmanMergedIdentBody.lean:135`) の中身

strong precondition (`_h_a_min` = a global-min, `_h_b_min` = b rest-min,
`_h_sibling : huffmanLength Q a = huffmanLength Q b`) 下で、subtype carrier
`x : {y // y ≠ b}` ごとに:
`huffmanLengthAux (mergedInitMultiset Q a b) x = if x.val = a then huffmanLength Q a - 1 else huffmanLength Q x.val`.

### Section E が列挙した 3 障害 と 決定化による解消対応

| # | 障害 (Section E / 判断ログ #19) | 決定化 (本 plan) での解消 |
|---|---|---|
| (i) | first-step が tie で a,b 以外を merge しうる (Classical.choose 不透明) | 決定的 min は forced。a global-min は確率で、b rest-min も確率で、tie は colex で破られ pin down。Phase H2-b |
| (ii) | `mergedInitMultiset` が一般に `NodupChain` 不成立 | 決定的 min は確率 tie を colex で破るので relabel-invariance に NodupChain 不要。Phase H2-a |
| (iii) | naive per-symbol tie-invariance が反例 `Q={.1,.15,.15,.6}` で偽 | 決定的 min なら per-symbol 語長は一意確定 (反例は Classical.choose の自由度に依存していた)。Phase H2-a で消える |

### 決定化 blast radius (前 session で grep 確認済、本 plan で再確認)

- `huffmanStep` を使う file は Huffman 系: `Huffman.lean`, `HuffmanOptimality.lean`,
  `HuffmanMergedAuxIdent.lean`, (transitively) Huffman* 系全体。
- **Ch.5 へ波及しない** (判断ログ #17 確認済): 依存方向は `Huffman.lean` が
  `ShannonCode`/`ShannonCodeKraftReverse` を **import する側** (`Huffman.lean:8-9`)、
  ShannonCode 側に Huffman 参照ゼロ。⇒ Phase RV の Ch.5 検証は「無影響の確認」だけ。
- `HuffmanSwapNormProof.lean` は InformationTheory 依存ゼロで insulated (決定化の影響を受けない)。
- aux 4 file (`HuffmanT1APPrimeBody`/`HuffmanSwapNormalizationBody`/`HuffmanSwapStepChainBody`/
  `HuffmanT1APPrimePartial`) は dead-weight leaf (判断ログ #19 所見、誰も import しない)。
  決定化で壊れても本 plan の publish path には無関係 — RV で silent でなければ別タスク削除候補
  としてフラグ (本 plan では修正しない、判断ログに記録)。

## 設計判断

### 設計判断 1 — `huffmanStep` colex 決定化の具体形 (採用 = colex 2 段 lex key)

**採用案 (DC)**: 比較キーを 2 段 lex とする。

```lean
-- 概念形 (実装は Phase D で確定)
noncomputable def groupKey [LinearOrder α] (p : Finset α × ℝ) : ℝ ×ₗ Colex (Finset α) :=
  (p.2, Finset.toColex p.1)
```

`ℝ ×ₗ _` の `Prod.Lex` 順序 (`Mathlib.Order.Prod` の `Prod.Lex.instLinearOrder`、
`[LinearOrder ℝ] [LinearOrder (Colex (Finset α))]` から) で第 1 = 確率昇順、tie で
第 2 = colex。これは `LinearOrder (Finset α × ℝ)`-相当の全順序を `groupKey` 経由で誘導する。

min 選択の **2 候補と判定**:

- **DC-1 (採用方針): `Multiset.exists_min_image` を `groupKey` で適用。**
  現行コード (`Huffman.lean:79`) は `Multiset.exists_min_image (fun p => p.2)` (= 確率のみ)。
  これを `Multiset.exists_min_image (fun p => groupKey p)` に差し替える。`exists_min_image` は
  `[LinearOrder R]` の `R = ℝ ×ₗ Colex (Finset α)` で動く。**min は一意** (`groupKey` が単射:
  確率が等しくても colex で区別、ただし「同一 group が重複しない」= `HuffmanGrouping.nodup`
  と合わせて key 単射)。`Classical.choose` は残るが **forced** (一意 minimizer)。
  - 利点: 定義本体の構造 (`Classical.choose ∘ exists_min_image`) を最小変更で保てる →
    `huffmanStep_min_fst/_min_snd` の `unfold huffmanStep` ベース証明が「確率 min →
    groupKey min」への置換で追従しやすい。signature 完全不変。
  - **min 性 spec の statement 変更リスク (Phase D-b で settle)**: 現 `huffmanStep_min_fst` は
    `∀ z ∈ s, .val.1.2 ≤ z.2` (確率の `≤`)。決定化後の forced min は `groupKey` の `≤` で
    最小。**確率の `≤` は groupKey min から従う** (第 1 キーが確率) ので、`huffmanStep_min_fst`
    の statement (確率 `≤`) は **保てる** (証明: groupKey min ⇒ 第 1 成分で確率最小)。これが
    成立すれば weak form (`huffmanStep_initMultiset_sibling`) の min 性も変更不要。
    加えて **groupKey min の一意性** を返す新 accessor (`huffmanStep_key_min_fst` 等) を
    追加して Phase H2 の決定的対応に使う。
- **DC-2 (検討のみ): `Multiset.sort groupKey` で list 化 → head 2 件。** `Multiset.sort` は
  `Huffman.lean:4` で import 済だが、`exists_min_image` を残す DC-1 の方が現行構造との差分が
  小さく、`unfold` ベース spec 証明の追従が容易。DC-1 を主、行き詰まったら DC-2 に切替
  (判断ログ)。

**colex tie-break が `mergedInitMultiset` の全 group で意味を持つこと**: `initMultiset`/
`mergedInitMultiset` の全 group は **singleton** (`{x}`) から始まる。`singleton_le_singleton`
(`Colex.lean:190`) で `toColex {a} ≤ toColex {b} ↔ a ≤ b` なので、singleton 同士の colex
tie-break は **`α` の `LinearOrder` 順そのもの**。merged group (内部 node) が出ても colex は
well-defined。これが第 2 キーの妥当性。

### 設計判断 2 — `[LinearOrder α]` の伝播範囲

- `groupKey` が `[LinearOrder α]` を要求するため、`huffmanStep`/`huffmanLengthAux`/
  `huffmanLength` の `variable` に `[LinearOrder α]` を追加。**全 Huffman* 定理に波及**
  (signature に instance 1 個追加)。weak form `huffmanLength_optimal_with_hypotheses`,
  Hyp1 `swap_normalization_proof`, headline `huffmanLength_optimal_modulo_aux_ident` も
  `[LinearOrder β]` を取る形に。
- **Ch.5 (`ShannonCode*`) は無影響** (依存方向逆、判断ログ #17)。
- **既存の値が tie-break で変わりうる点 (要確認、Phase RV)**: 決定化で `huffmanLength` の
  具体値 (どの最適木か) は変わりうるが、optimality 内容 (不等式) は不変。Hyp1
  `swap_normalization_proof` は **`huffmanStep` 非依存** (`swap_step_le` +
  keystone は huffmanLength の値ではなく feasible `l` 側を操作) なので決定化後も成立する
  見込み。weak form induction (`huffmanLength_optimal_aux_with_hypotheses`) は `huffmanStep`
  の **min 性 spec** にのみ依存 (`huffmanStep_initMultiset_sibling`) — これは設計判断 1 で
  statement 維持されるので壊れない。Phase RV で全 file silent を確認。

### 設計判断 3 — cross-type colex 対応の核 (Phase H2 の load-bearing lemma)

決定的 min が relabel (`α` ↔ `{y // y ≠ b}`) と可換であることの証明鎖:

1. `subtypeNeEmbedding b` の underlying map は `Subtype.val`。
   **`Subtype.strictMono_coe (Order/Monotone/Defs.lean:497) : StrictMono ((↑) : Subtype p → α)`**
   (`[Preorder α]` で十分、`[LinearOrder α]` から従う) で strict-mono。
2. `relabelGroup e p = (p.1.map e, p.2)` の `Finset.map e` を
   **`Finset.map_eq_image (Data/Finset/Image.lean:293) : s.map f = s.image f`** で
   `p.1.image e` に書き換え。
3. **`Finset.toColex_image_le_toColex_image (Colex.lean:396) (hf : StrictMono f) :
   toColex (s.image f) ≤ toColex (t.image f) ↔ toColex s ≤ toColex t`** で colex 順が
   `e` 越しに保存。⇒ `groupKey` の第 2 キー (colex) が relabel で対応、第 1 キー (確率) は
   `relabelMultiset_snd` (既存、`HuffmanMergedAuxIdent.lean:131`) で不変 ⇒ `groupKey` 全体が
   relabel で対応 ⇒ 決定的 min が可換。

この鎖は **NodupChain を一切使わない** (一意性は groupKey の全順序から無条件)。よって
`huffmanStep_fst/snd_relabel` の `NodupChain`/`Nodup` 前提を **`HuffmanGrouping` だけ** に
弱める (or 決定版を新設) のが Phase H2-a。

### 設計判断 4 — file 配置

- Phase D (決定化) は `Huffman.lean` 本体編集 (定義差し替え、新規 file 不可)。`groupKey` /
  `Prod.Lex` / `Colex` の import を `Huffman.lean` 冒頭に追加
  (`Mathlib.Combinatorics.Colex`, `Mathlib.Order.Prod` 等、pinpoint)。
- Phase H2 (Hyp2 discharge) は `HuffmanMergedAuxIdent.lean` に決定版 relabel 補題を追記
  (Section B/C の NodupChain 前提を外した版) + first-step identification + collapse
  correspondence。規模が ~400 行を超えるなら新規 file
  `HuffmanColexDeterminism.lean` へ分離 (判断ログで決定)。
- Phase M wrapper は `HuffmanStrongForm.lean` 末尾 (`mergedHuffmanAuxIdent_proof` +
  `huffmanLength_optimal`)。`InformationTheory.lean` の import は Huffman* 登録済、新規 file 時のみ追記。

## Phase 詳細

### Phase 0 — 在庫再確認 + 設計 probe (skeleton 型チェックのみ) 📋

- [ ] inventory (`huffman-optimality-t1apprime-mathlib-inventory.md`) を **読むだけ** で
      点検 (別エージェント所掌、編集禁止)。真壁前提の項目を心覚え。
- [ ] `groupKey : Finset α × ℝ → ℝ ×ₗ Colex (Finset α)` の型を skeleton で型チェック。
      `Prod.Lex.instLinearOrder` が `[LinearOrder ℝ] [LinearOrder (Colex (Finset α))]` から
      derive されることを確認 (`#synth LinearOrder (ℝ ×ₗ Colex (Finset α))`)。
- [ ] cross-type 対応の 1 行 probe: `toColex_image_le_toColex_image (Subtype.strictMono_coe _)`
      + `Finset.map_eq_image` で `relabelGroup` の colex 保存を skeleton 型チェック (証明は H2-a)。
- [ ] `huffmanStep_min_fst` の statement (確率 `≤`) が groupKey min から従うことの 1 行
      probe (第 1 キー射影で `Prod.Lex` の `le` ⇒ 第 1 成分 `≤`)。

### Phase D — `huffmanStep` colex 決定化 📋

- [ ] **D-a**: `Huffman.lean` に `groupKey` (設計判断 1) を定義、`variable` に `[LinearOrder α]`
      追加。`huffmanStep` 本体の `exists_min_image (fun p => p.2)` 2 箇所を
      `exists_min_image (fun p => groupKey p)` に差し替え (`Huffman.lean:79`,`:91`)。
      signature `{ p // <既存 spec 4 件> }` は不変。target: 本体が型チェック (spec 証明前)。
- [ ] **D-b**: spec 補題の証明追従。statement 維持:
      - `huffmanStep_min_fst` (`:246`) / `_min_snd` (`:266`): 確率 `≤` を groupKey min の
        第 1 キー射影から再証明。
      - `huffmanStep_spec` (`:231`) / `_grouping` (`:301`) / `_card_eq` (`:308`) /
        `_card_lt` (`:324`) / `huffmanLengthAux_eq_step` (`:362`): 構造は不変なので追従のみ。
      - **新 accessor 追加**: `huffmanStep_key_min_fst` (`.val.1` が `groupKey` 全体の min、
        一意性付き) — Phase H2 の決定的対応に使う genuine な新補題。
      target: `Huffman.lean` 単体 silent。規模 ~120-200 行 (本体 + spec 追従 + 新 accessor)。
- [ ] **D-c**: `huffmanStep_initMultiset_sibling` (`HuffmanOptimality.lean:66`) の inline
      `unfold huffmanStep` + `Classical.choose_spec` 経路 (107-145 行) を、決定化で壊れるなら
      publish 済 `huffmanStep_min_fst/_min_snd` accessor 経由に書き換え (statement 維持)。
      target: `HuffmanOptimality.lean` 単体 silent。

### Phase RV — 決定化 blast radius 再検証 📋

- [ ] `lake build InformationTheory.Shannon.Huffman` で olean refresh 後、Huffman* 系を個別
      `lake env lean` で silent 確認: `HuffmanOptimality`, `HuffmanMergedIdentBody`,
      `HuffmanMergedAuxIdent`, `HuffmanStrongForm`, `HuffmanSwapNormCompletion`。
- [ ] aux 4 dead-weight file が壊れたら **修正せず判断ログにフラグ** (削除候補、本 plan scope 外)。
- [ ] Ch.5 (`ShannonCode.lean`, `ShannonCodeKraftReverse.lean`) を `lake env lean` で確認
      (無影響の確認だけ、修正 0 見込み)。
- [ ] Hyp1 `swap_normalization_proof` + headline `huffmanLength_optimal_modulo_aux_ident` が
      `[LinearOrder β]` 追加後も silent を確認 (Hyp1 は `huffmanStep` 非依存の見込み)。

### Phase H2 — Hyp2 を決定性で genuine discharge 📋

- [ ] **H2-a**: `huffmanStep_fst/snd_relabel`, `huffmanStep_step_relabel`,
      `huffmanLengthAux_relabel` の **NodupChain 前提を外した決定版** を新設
      (`HuffmanMergedAuxIdent.lean` 追記 or 新 file)。核は設計判断 3 の colex 保存鎖
      (`Subtype.strictMono_coe` + `map_eq_image` + `toColex_image_le_toColex_image`)。
      target: `huffmanLengthAux_relabel_det` (NodupChain 不要、`HuffmanGrouping` のみ) silent。
      規模 ~120-200 行。**最大の cross-type risk** — ここで colex 保存鎖が破綻したら撤退ライン。
- [ ] **H2-b**: first-step identification。`initMultiset Q` の決定的 1st `huffmanStep` が
      `{a}` (確率 global-min、`_h_a_min`) を、2nd が `{b}` (rest-min、`_h_b_min`) を選ぶことを
      決定的 min から証明 (確率 tie は colex で破られるが、a/b が選ばれることは確率 + colex
      の組で pin down)。target: `firstStep_merges_ab` 系補題 silent。規模 ~100-150 行。
- [ ] **H2-c**: collapse correspondence。first-step 後の β 側残木 (card-2 group
      `{a,b}@sum`) と subtype 側 (singleton `{⟨a,_⟩}@sum`) を H2-a の決定版 relabel +
      `huffmanLengthAux_const_on_group` (`Huffman.lean:524`) で対応付け。
      target: collapse 合成補題 silent。規模 ~150-250 行。
- [ ] **H2-d**: `mergedHuffmanAuxIdent_proof : MergedHuffmanAuxIdentHypothesis.{u}` を
      H2-a/b/c + 既存 `huffmanLengthAux_mergedInitMultiset_relabel` (`:436`) を組み上げて
      genuine 証明 (型 = primitive predicate、`:= by` で実証明、`:= h` 循環でない)。規模 ~50-100 行。

### Phase M — 無引数強形主定理 📋

- [ ] `huffmanLength_optimal` ([LinearOrder α] のみ追加、他 hypothesis なし) を
      `huffmanLength_optimal_modulo_aux_ident mergedHuffmanAuxIdent_proof …` で publish
      (`HuffmanStrongForm.lean` 末尾、~5 行)。

### Phase V — 検証 📋

- [ ] 触れた全 file で `lake env lean <file>` silent (0 sorry / 0 warning)。
- [ ] 全体 `lake build` を 1 回 (大改修後の sanity)。
- [ ] `#print axioms huffmanLength_optimal` で `sorryAx` 非依存を確認 (= 標準B 達成)。
      `Classical.choice` / `propext` / `Quot.sound` のみ許容。
- [ ] roadmap (別エージェント所掌、本 plan は触らない) に「真壁判定撤回 + 強形完成」を
      記録するよう報告で促す。

## 撤退ライン

- **H2-a 破綻 (colex 保存鎖が cross-type で取れない)**: 設計判断 3 の鎖
  (`Subtype.strictMono_coe` + `map_eq_image` + `toColex_image_le_toColex_image`) は probe で
  型成立を確認済だが、`relabelGroup` の `Finset.map` と `Finset.image` の defeq/書き換えが
  実証明で重い場合、`relabelGroup` を **`image` ベースに再定義** する (Section A 7 補題の
  証明追従が必要、~80 行)。それでも破綻なら DC-2 (`Multiset.sort`) へ決定化方式を切替
  (判断ログ)。
- **D-b で min 性 spec の statement が維持できない (確率 `≤` が groupKey min から従わない)**:
  weak form (`huffmanStep_initMultiset_sibling`) と Hyp1 への波及が大きい。その場合は
  spec を「groupKey min」形に変えて weak form 側を追従させる (~50-100 行追加、判断ログ)。
- **H2-c collapse が決定性下でも非自明**: collapse は cardinality 変更を伴うため、決定版
  relabel だけでは閉じない場合がある。`huffmanLengthAux` の「card-2 group を含む木」と
  「対応 singleton を含む木」の語長一致を直接 strong induction で示す補助補題に切替
  (~100 行追加)。
- **`[LinearOrder α]` 追加が想定外に重い (Phase RV で多数 file が壊れる)**: 各 Huffman* file
  への instance 追加は機械的だが、aux 4 dead-weight file が壊れたら **修正せず削除候補として
  判断ログにフラグ** (本 plan の publish path に無関係)。
- **各 Phase 共通 (honest 限定)**: 行き詰まったら honest な名前付き仮説 (型 ≠ 結論、docstring
  で load-bearing 明示) で抜く。**禁止**: Section E が禁じた fake residual hypothesis
  (`MergedHuffmanAuxIdentTieResidual` 等、型 ≡ 結論) / `:= h` 循環 / `:True` スロット /
  弱化述語への逃避 / 偽縮約鎖 (`EqualizingPermHypothesis`) の上に積む / `sorry`。
  `[LinearOrder α]` 以外の load-bearing 仮説 (確率 distinct を要求する no-ties 限定など) で
  「強形」と称さない — それは full optimality に到達しない。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-21 起草 — 真壁判定 (#19 / Section E) の撤回 + colex 決定化を主軸に確定**:
   前 session は Hyp2 の確率 tie 一般ケースを「定義 artifact の真壁」と判定したが、その根拠
   「決定的 huffmanStep に必要な `LinearOrder (Finset α)` が Mathlib に無い」は
   `Fintype.equivFin` 順序 (任意・subtype 非制限) だけ試した結果。起草前 probe で
   `[LinearOrder α]` を構造的仮説に加えれば `Finset.Colex.instLinearOrder` (`Colex.lean:272`)
   で `LinearOrder (Colex (Finset α))` が立ち、`Subtype.strictMono_coe` +
   `Finset.map_eq_image` + `toColex_image_le_toColex_image` (`Colex.lean:396`) で carrier
   横断の colex 保存が取れる (型成立確認済) と判明。本 plan は `huffmanStep` を colex 決定化
   (DC-1, exists_min_image の key を `groupKey` に差し替え) し、Section E の 3 障害
   ((i) first-step identification / (ii) NodupChain 不成立 / (iii) per-symbol invariance 偽) を
   一括解消する。`[LinearOrder α]` は構造的仮説 (regularity) であって load-bearing でない —
   最終定理は full optimality の不等式のまま。
2. **2026-05-21 起草 — 残スコープは Hyp2 単独 (Hyp1 は前 session で完了)**:
   `huffman-strong-form-completion-plan.md` 起草時点では Hyp1/Hyp2 両方が open だったが、
   前 session で Hyp1 (`swap_normalization_proof`) は genuine discharge 済、headline
   `huffmanLength_optimal_modulo_aux_ident` (Hyp1 被せ済) も publish 済 (`HuffmanStrongForm.lean`)。
   本 plan の実装範囲は **Hyp2 = `MergedHuffmanAuxIdentHypothesis` 単独の discharge + 無引数
   wrapper** に縮小。前 plan の Phase H1 系 (Hyp1) は実行不要 (完了済)。
3. **2026-05-21 起草 — 決定化方式は DC-1 (exists_min_image key 差し替え) を主、DC-2
   (Multiset.sort) を fallback**: 現行 `huffmanStep` 本体が `Classical.choose ∘ exists_min_image`
   構造で、`huffmanStep_min_fst/_min_snd` の `unfold huffmanStep` 証明がこれに依存するため、
   key を `groupKey` に差し替える DC-1 が差分最小で追従容易。signature 不変を維持し、
   min 性 spec の statement (確率 `≤`) は groupKey min の第 1 キー射影で保つ設計。

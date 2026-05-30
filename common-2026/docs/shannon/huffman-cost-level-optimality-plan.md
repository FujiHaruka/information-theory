# T1-A'' Huffman 最適性 — cost-level pivot による強形完遂計画 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A''. Huffman 最適性」(判断ログ #15)
> - 前任 (per-symbol depth-identity 路線、FALSE 確定で放棄):
>   [`huffman-strong-form-completion-plan.md`](./huffman-strong-form-completion-plan.md)
>     — 同 plan 判断ログ #4/#5 で「pivot 方向 = tie-invariant cost-level merge identity」を
>       明示しており、本 plan はその指示を具体化する後継。
>
> **`@residual` slug 整合**: 本 file の filename stem = `huffman-cost-level-optimality`。
> 新規導入する sorry の `@residual(plan:huffman-cost-level-optimality)` がこれを指す。
> 既存 FALSE wall 5 件は `@audit:closed-by-successor(huffman-strong-form-completion)` を
> 引き続き持つ (= 前任 plan slug)。retract/書換手順は §「FALSE wall の retract 手順」参照。
>
> **Status (2026-05-30)**: 計画起草。実装未着手。

## 進捗

- [ ] Phase 0 — 在庫再点検 + cost-recurrence の API probe 📋
- [ ] Phase C1 — `huffmanCost` 定義 + `expectedLength = huffmanCost (initMultiset P)` link 📋
- [ ] Phase C2 — cost 1-step 漸化式 `huffmanCost_step` (`kraftPerGroup_step` template) 📋
- [ ] Phase C3 — merged-carrier cost 同定 (carrier-crossing 評価点) 📋
- [ ] Phase C4 — cost-level bridge L を `huffmanLength_bridge_L` 置換で再構成 📋
- [ ] Phase M — 帰納核の `h_L'_link` 除去 + 無引数 `huffmanLength_optimal` publish 📋
- [ ] Phase R — FALSE wall 5 件 retract + Phase V (`#print axioms`) 📋

proof-log: yes (C3 の carrier-crossing が core risk、迷走しやすいので残す)

## ゴール / Approach

### Goal (最終定理 signature)

`Common2026/Shannon/HuffmanOptimality.lean` 末尾追記:

```lean
/-- **Cover–Thomas Theorem 5.8.1 (strong form)** — hypothesis 引数なし. -/
theorem huffmanLength_optimal
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l
```

### Approach (overall strategy / shape)

**何を捨てるか**: per-symbol depth identity 路線を全廃。具体的には weak-form 帰納核
`huffmanLength_optimal_aux_with_hypotheses` (`HuffmanOptimality.lean:815`) の **唯一の
hypothesis 2 使用点** = `h_L'_link` (`:1036-1040`) を消す。`h_L'_link` は
`huffmanLength (mergedMeasure P a b hab) x = (if x.val=a then huffmanLength P a - 1 else
huffmanLength P x.val)` という per-symbol 等式 (= `HuffmanMergedIdentificationHypothesis`、
機械検証で FALSE) を `huffmanLength_bridge_L` に喰わせて bridge L を組んでいる。

**何で置き換えるか**: per-symbol depth ではなく、**期待長そのもの (cost = ∑ prob·depth)**
を多重集合上で漸化させる。決定的 colex tie-break は **木 (depth) を動かすが cost は動かさ
ない** — これが本 pivot の数学的命題で、全 61254 precond case で失敗 0 (orchestrator brief)。
鍵となる prior は `kraftPerGroup_step` (`Huffman.lean:770`、**証明済 `@audit:ok` 相当**):
`kraftPerGroup s = kraftPerGroup (huffmanStep s ...).val.2.2` という **per-group / tie-invariant
/ 単一 carrier の漸化式**を、actually-merged pair (`huffmanStep` の `.val.1`/`.val.2.1`、(a,b)
global-min framing 不要) について `huffmanStep_orig_decomp` + `huffmanLengthAux_step_merged`
+ `huffmanLengthAux_step_other` の組合せで証明している。cost は `2^(-d)/card` 重みを
`prob·d` 重みに替えるだけで **同じ template** が回る。

**carrier-crossing をどう回避するか (最重要評決)**: orchestrator brief の骨格は
`s''` (merged group `({a,b}, P{a}+P{b})` + 残 singleton) と `initMultiset(mergedMeasure)`
(subtype 上 singleton) を `huffmanLengthAux_relabel_det` で cost 一致させる、というもの
だったが、これは **取れない見込み** (§carrier-crossing 評決)。代わりに cost を
**measure-level で定義し、carrier を一切跨がない 3 段 chain** で閉じる:

```
expectedLength P (huffmanLength P)
  = expectedLength (mergedMeasure P a b hab) (huffmanLength (mergedMeasure ...))   -- bridge (C3+C4)
      + (P{a} + P{b})
  ≤ expectedLength (mergedMeasure ...) l'  + (P{a}+P{b})                            -- IH (既存 h_IH)
  = expectedLength P l_norm                                                          -- 既存 expectedLength_bridge_R
  ≤ expectedLength P l                                                               -- 既存 hln_le
```

1 行目 (bridge L の cost 版) を per-symbol link 無しで作るのが C3+C4。ここで
`huffmanLength (mergedMeasure ...)` は IH が直接生成する **merged carrier 自身の huffman
語長**なので、`huffmanLength P` の最初の `huffmanStep` が生む木と per-symbol 一致を要求
しない。両辺を「a,b を merge した後の残木の cost」に **cost-level で**落とせば一致する、
というのが C3 の主張。

**honesty 線**: 標準B (無条件機械検証)。各 Phase target は genuine (型 ≠ trivial、
`:= h` 循環禁止、`:True` 禁止、FALSE predicate を hypothesis に取り直さない)。詰まったら
`sorry` + `@residual(plan:huffman-cost-level-optimality)`。**FALSE 5 件 (§現況) の上に
積まない** — それらは hypothesis 引数として渡される形のまま残るが、本 plan の最終 wrapper
はそれらを **一切経由しない** (`huffmanLength_optimal_with_hypotheses` の `h_ident` 引数に
FALSE predicate を渡すのではなく、帰納核から `h_ident` 依存を除去した新 motor を立てる)。

## 現況 (詳細、verbatim 確認済)

### 主役 skeleton (再利用、一部改変)

- `huffmanLength_optimal_with_hypotheses` (`HuffmanOptimality.lean:1069`) — weak form headline。
  `(h_swap : SwapNormalizationHypothesis)` + `(h_ident : HuffmanMergedIdentificationHypothesis)`
  を取る。本 plan は **`h_ident` 引数を持たない新 headline `huffmanLength_optimal`** を
  立てる (既存 headline は API 後方互換のため残置可、§Phase M)。
- 内部 motor: `huffmanLength_optimal_aux_with_hypotheses` (`:815`) — `Nat.strong_induction_on`。
  `h_ident` の使用は **`h_L'_link` (`:1036-1040`) の 1 ヶ所のみ** (verbatim 確認済)。
  `h_swap` は step case の `l` 正規化 (`:944-945`) で使用。

### h_ident 使用点の解剖 (verbatim、置換対象)

`huffmanLength_optimal_aux_with_hypotheses` step case (`:936-1057`) の流れ:

1. `:941` `exists_sibling_min_pair P hP h_card_ge_2` で `(a,b,hab,h_sib,h_a_min,h_b_min)`。
2. `:944` `h_swap ...` で `l_norm` (`l_norm a = l_norm b`、E 非増加、Kraft 維持)。
3. `:1011` `expectedLength_bridge_R P l_norm ...` で `l'` (merged 側 lengths) + `hl'_eq`:
   `expectedLength P l_norm = expectedLength (mergedMeasure ...) l' + (P{a}+P{b})`。
4. `:1028` `h_IH` (IH): `expectedLength (mergedMeasure ...) (huffmanLength (mergedMeasure ...))
   ≤ expectedLength (mergedMeasure ...) l'`。
5. **`:1036-1040` `h_L'_link`** (= `h_ident` の唯一使用): per-symbol depth identity。
6. `:1042` `huffmanLength_bridge_L P hP h_card_ge_2 a b hab h_sib
   (huffmanLength (mergedMeasure ...)) h_L'_link` で `h_BL`:
   `expectedLength P (huffmanLength P) = expectedLength (mergedMeasure ...)
   (huffmanLength (mergedMeasure ...)) + (P{a}+P{b})`。
7. `:1049-1057` calc で連結。

**本 plan の置換**: step 5 (`h_L'_link`) を消し、step 6 の `huffmanLength_bridge_L`
(per-symbol link 必須) を **cost-level bridge** `expectedLength_merged_cost_bridge`
(C4、per-symbol link 不要) に差し替える。後者の結論型は step 6 の `h_BL` と同一なので、
calc chain (step 7) は無改変で通る。

### `huffmanLength_bridge_L` の depth-link 依存 (verbatim、置換理由)

`huffmanLength_bridge_L` (`HuffmanOptimality.lean:245`) は引数
`(L' : {x // x ≠ b} → ℕ)` + `(h_L'_link : ∀ x, L' x = if x.val=a then huffmanLength P a - 1
else huffmanLength P x.val)` を取る。本体は `expectedLength` を b 項分離 + subtype 化 +
`ring` で代数的に閉じており、**`h_L'_link` を `L'` の値の同定にしか使っていない** (per-symbol
の代数恒等式)。`L' := huffmanLength (mergedMeasure ...)` を渡すとき、この同定が FALSE
predicate (`h_ident`) を要求する。**本 plan は `huffmanLength_bridge_L` 自体は再利用せず**、
同じ結論を `huffmanLength (mergedMeasure ...)` の cost を **集約レベル**で同定する別補題
(C4) で得る。`huffmanLength_bridge_L` は API 残置 (consumer は新 motor 1 件のみ削除)。

### cost-recurrence prior = `kraftPerGroup_step` (`Huffman.lean:770`、証明済)

```lean
lemma kraftPerGroup_step (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card)
    (hg : HuffmanGrouping s) :
    kraftPerGroup s = kraftPerGroup (huffmanStep s hs hg).val.2.2
```

`kraftPerGroup s = (s.map (fun p => (∑ a ∈ p.1, 2^(-d s a)) / p.1.card)).sum`
(`Huffman.lean:655`)。証明 (`:770-`) は `huffmanStep_orig_decomp` で `s = x1 ::ₘ x2 ::ₘ ee`、
`s'' = merged ::ₘ ee`、ee 寄与は `huffmanLengthAux_step_eq_on_other_group` で不変、x1/x2
寄与は `huffmanLengthAux_step_merged` で `d_x1 = d_x2 = d_merged + 1`。**cost 版は重み
`(∑ 2^(-d))/card` を `(∑_{a∈p.1} prob_a · d s a)` に替えるが、prob_a は group 単位ではなく
per-element**。group 上 depth は定数 (`huffmanLengthAux_const_on_group`, `:581`) なので
cost も group 単位で `(group 内 prob 総和) · d_p` に書けるが、`Finset α × ℝ` の `ℝ` 成分
(`p.2`) は merged で `x1.2 + x2.2` = (group 内 prob 総和) と一致する設計 (initMultiset の
singleton で `p.2 = P.real {a}`)。⇒ cost を **`(s.map (fun p => p.2 * d s (代表元))).sum`**
で定義すれば `kraftPerGroup_step` と同じ template が回る。詳細は C2。

### 既存 genuine 資産 (黒箱 reuse)

| lemma / def | 行番号 | 役割 |
|---|---|---|
| `expectedLength` | `ShannonCode.lean:56` | `∑ a, P.real{a} * (l a)`。cost の最終形 |
| `huffmanLength` | `Huffman.lean:451` | `= huffmanLengthAux (initMultiset P)` (defeq) |
| `huffmanLengthAux` | `Huffman.lean:400` | strong-induction 再帰、step で `g a + 1`/`g a` |
| `initMultiset` | `Huffman.lean:420` | `univ.val.map (fun a => ({a}, P.real {a}))` |
| `huffmanStep_orig_decomp` | `Huffman.lean:687` | `s = x1 ::ₘ x2 ::ₘ ee` |
| `huffmanLengthAux_step_merged` | `Huffman.lean:702` | `d s a = d s'' a + 1` for `a ∈ x1.1 ∪ x2.1` |
| `huffmanLengthAux_step_other` | `Huffman.lean:713` | `d s a = d s'' a` for `a ∉ x1.1 ∪ x2.1` |
| `huffmanLengthAux_step_eq_on_other_group` | `Huffman.lean:724` | ee 内 group で `d s = d s''` |
| `huffmanLengthAux_const_on_group` | `Huffman.lean:581` | group 上 depth 定数 |
| `kraftPerGroup_step` | `Huffman.lean:770` | **cost-recurrence の template** |
| `huffmanStep_card_lt` / `_card_eq` | `Huffman.lean:389`/`:373` | `s''.card = s.card - 1` |
| `huffmanStep_spec` / `_grouping` | `Huffman.lean:270`/`:366` | step の 4-spec + grouping 保存 |
| `expectedLength_bridge_R` | `HuffmanOptimality.lean:353` | feasible `l` → merged `l'` (cost ≥)。改変不要 |
| `mergedMeasure` / `_real` / `_isProbabilityMeasure` / `_pos` | `HuffmanOptimality.lean:214/221/520/594` | merged carrier 構成 |
| `initMultiset_mergedMeasure_eq` | `HuffmanMergedIdentBody.lean:66` | `initMultiset (mergedMeasure ...) = mergedInitMultiset` |
| `mergedInitMultiset` / `_huffmanGrouping` | `HuffmanMergedIdentBody.lean:55`/:78 | merged carrier explicit multiset |
| `swap_normalization_proof` | `HuffmanStrongForm.lean:153` | Hyp1 = genuine discharge 済 (`SwapNormalizationHypothesis`) |
| `exists_sibling_min_pair` | `HuffmanOptimality.lean:196` | sibling pair `(a,b)` (a=global-min, b=rest-min) |
| `fintype_card_subtype_ne` | `HuffmanOptimality.lean:605` | `card {y≠b} = card α - 1` (IH の card 減少) |

### carrier-crossing 評決 (orchestrator brief の最優先評価)

**評決: `huffmanLengthAux_relabel_det` で `s'' ↔ initMultiset(mergedMeasure)` の cost 一致は
取れない。carrier-crossing は本 pivot の壁になる。回避策 (C3 の measure-level cost) を採る。**

根拠 (3 点、verbatim 確認済):

1. **`relabel_det` は per-symbol + cardinality 保存**。signature
   (`HuffmanColexDeterminism.lean:225`):
   ```lean
   lemma huffmanLengthAux_relabel_det {γ} [DecidableEq γ] [LinearOrder γ]
       {f : α → γ} (hf : StrictMono f) (hfi : Function.Injective f)
       (s : Multiset (Finset α × ℝ)) (hg : HuffmanGrouping s) (a : α) :
       huffmanLengthAux (relabelMultiset ⟨f, hfi⟩ s) (f a) = huffmanLengthAux s a
   ```
   `relabelMultiset` = `s.map (relabelGroup e)`、`relabelGroup e (F,p) = (F.map e, p)`
   (`HuffmanMergedAuxIdent.lean:71`) で **Finset の cardinality を保つ**。これは「同じ shape
   の木を別 carrier に写す」不変量。

2. **`s''` と `initMultiset(mergedMeasure)` は label cardinality が違う**。
   `HuffmanMergedAuxIdent.lean:448-453` (Section D docstring、機械検証済の記録) が明記:
   > `s''` は card-2 group `{a,b}@(Q{a}+Q{b})` を含むが、`mergedInitMultiset` では a-merged は
   > **singleton** `{⟨a,_⟩}@(Q{a}+Q{b})`。両者を結ぶのは card-2 group → singleton の
   > **collapse** であり、cardinality を保つ `Finset.map` (relabel) では表現できない。
   ⇒ `relabel_det` の適用前提 (`relabelMultiset` で写る関係) が成立しない。

3. **per-symbol collapse 自体が FALSE**。Section J `collapseLabel_huffmanLengthAux`
   (`HuffmanColexDeterminism.lean:353`) は label `{a}→{a,b}` 拡張下の per-symbol depth
   不変性を主張するが **機械的反例で FALSE 確定** (`@audit:defect(false-statement)`)。根因は
   「label の colex 変化が同確率 group の tie-break をずらし、`b` を含まない leaf の depth も
   動く」。⇒ 仮に carrier を揃えても per-symbol depth は一致しない。

**しかし cost は一致する**: 反例 (`HuffmanColexDeterminism.lean:320-323`) では `z=2` の depth が
`2→3` に動くが、別の leaf の depth が補償して `∑ prob·depth` (Kraft 総和も) は保たれる
(`kraftPerGroup_step` が tie 下でも成立する事実が傍証)。よって cost を **集約 (sum) レベルで**
扱えば、per-symbol/carrier-crossing の両方を回避できる。これが C3 の設計根拠。

**C3 で残る非自明点 = 「merged 残木の cost」を 2 表現で結ぶこと** (carrier 内に閉じる):
- 表現 A: `huffmanCost (huffmanStep (initMultiset P) ..).val.2.2` (= `s''`, carrier `α`)。
- 表現 B: `expectedLength (mergedMeasure P a b hab) (huffmanLength (mergedMeasure ...))`
  (carrier `{y≠b}`)。
A と B は確率 multiset として一致 (`relabelMultiset_snd` 系で prob 列は relabel 不変、
かつ merged group の prob = `P{a}+P{b}`)。**cost が確率 multiset のみで決まる** ことを示せれば
A=B が carrier を意識せず従う。これが C3 の core lemma で、最大リスク (§撤退ライン)。
**第一選択は A=B を直接結ばず**、両辺をそれぞれ自分の carrier の `huffmanCost_step` で
1 段ずつ剥がして cost の漸化 (prob 列が同じなら同じ値) に帰着させる設計。

## Phase 詳細

### Phase 0 — 在庫再点検 + cost-recurrence の API probe 📋

- [ ] inventory (`huffman-optimality-t1apprime-mathlib-inventory.md`) を読むだけで再点検
      (別エージェント所掌、編集しない)。cost 系で使う `Multiset.map` / `Multiset.sum` /
      `Finset.sum_*` の在庫を確認。
- [ ] `kraftPerGroup_step` (`Huffman.lean:770`) の証明全体を Read し、cost 版で再利用できる
      step 構造 (ee 寄与 / x1,x2 寄与 / merged 寄与) を 1:1 対応づける。
- [ ] `huffmanCost` 定義の Mathlib-shape probe: `expectedLength P l = ∑ a, P.real{a}*(l a)`
      (`ShannonCode.lean:56`) と `huffmanCost (initMultiset P)` が defeq or `Multiset.map`
      の `Finset.sum ↔ Multiset.sum` 1 補題で結べるかを 1 行 skeleton で型チェック
      (`Finset.sum_eq_multiset_sum` 系 / `Multiset.map_map`)。

### Phase C1 — `huffmanCost` 定義 + initMultiset link 📋

- [ ] **C1-a**: `huffmanCost` を `kraftPerGroup` (`Huffman.lean:655`) と同じ shape で定義。
      Mathlib-shape-driven: `kraftPerGroup_step` の template に乗るよう per-group sum 形に:
      ```lean
      /-- group 多重集合上の期待長 (= ∑ group, group の確率質量 · group depth).
      group 上 depth は `huffmanLengthAux_const_on_group` で定数なので代表元で評価. -/
      noncomputable def huffmanCost (s : Multiset (Finset α × ℝ)) : ℝ :=
        (s.map (fun p => p.2 * (∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / p.1.card)).sum
      -- @residual(plan:huffman-cost-level-optimality)  (詰まれば)
      ```
      注 (verbatim 確認要): `initMultiset` の group は singleton `({a}, P.real{a})` で
      `p.2 = P.real{a}`、`p.1.card = 1`、`∑_{x∈{a}} d = d a`。よって singleton では
      `p.2 * (∑/card) = P.real{a} * d a`。merged 内部 node の `p.2 = x1.2+x2.2` は group
      内 prob 総和に**一致しない**可能性 — initMultiset 由来では `p.2` は merge 履歴の prob 和
      であり group 内 leaf の `P.real` 総和に一致する (`huffmanStep` が `x1.2+x2.2` で積む)。
      この一致は **C2 で per-group に証明が要る** か、定義を `(∑_{a∈p.1} prob_a)` 明示形に
      する。**設計判断 (§下) で `p.2` を使うか `∑ prob` を使うか確定**。
- [ ] **C1-b**: `expectedLength P (huffmanLength P) = huffmanCost (initMultiset P)`。
      `huffmanLength P = huffmanLengthAux (initMultiset P)` (defeq, `:451`)、initMultiset の
      各 group は singleton なので `huffmanCost` の per-group sum が `∑ a, P.real{a}*(d a)` に
      collapse。`Finset.sum ↔ Multiset.sum` 1 補題 + singleton 簡約。
      target: `lemma expectedLength_eq_huffmanCost_init`。規模 ~40-80 行。

### Phase C2 — cost 1-step 漸化式 `huffmanCost_step` 📋

- [ ] **C2-a**: `kraftPerGroup_step` を template に cost 版を証明。
      ```lean
      /-- cost の step 不変 + merged ペナルティ:
      `huffmanCost s = huffmanCost s'' + (x1.2 + x2.2)`  where s'' = (huffmanStep s ..).val.2.2. -/
      lemma huffmanCost_step (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card)
          (hg : HuffmanGrouping s) :
          huffmanCost s
            = huffmanCost (huffmanStep s hs hg).val.2.2
              + ((huffmanStep s hs hg).val.1.2 + (huffmanStep s hs hg).val.2.1.2) := by
        sorry  -- @residual(plan:huffman-cost-level-optimality)
      ```
      論証 (kraftPerGroup_step と平行): `s = x1 ::ₘ x2 ::ₘ ee`、ee 寄与は
      `huffmanLengthAux_step_eq_on_other_group` で不変、x1/x2 寄与は
      `huffmanLengthAux_step_merged` (`d_x1 = d_x2 = d_merged + 1`) で
      `x1.2·(d_m+1) + x2.2·(d_m+1) = (x1.2+x2.2)·d_m + (x1.2+x2.2)`、merged 寄与は
      `(x1.2+x2.2)·d_m`。差分 = `(x1.2+x2.2)`。規模 ~120-200 行
      (`kraftPerGroup_step` が ~180 行なので同程度、cost は `/card` が無いぶん軽い可能性)。
      **最初に着手する非自明補題**。kraftPerGroup_step を逐行 mirror できれば想定内。
- [ ] **C2-b** (C1-a の `p.2` 設計に依存): merged group の `p.2 = x1.2 + x2.2` が group 内
      prob 総和と整合することを使う or 不要にする。C1-a で `∑ prob` 明示形を採れば C2-b 不要。

### Phase C3 — merged-carrier cost 同定 (carrier-crossing 評価点) 📋

- [ ] **C3-a**: `huffmanCost (huffmanStep (initMultiset P) ..).val.2.2` (carrier α の s'')
      と `expectedLength (mergedMeasure P a b hab) (huffmanLength (mergedMeasure ...))`
      (carrier {y≠b}) を結ぶ。**carrier を跨がない設計**:
      - merged 側を C1-b 類似で `huffmanCost (initMultiset (mergedMeasure ...))` に書換
        (`= huffmanCost (mergedInitMultiset P a b)` via `initMultiset_mergedMeasure_eq`)。
      - α 側 `s''` と `{y≠b}` 側 `mergedInitMultiset` は **prob 多重集合が一致**
        (`s''` の merged group prob `P{a}+P{b}` = mergedInit の a-singleton prob、残 singleton
        も一致)。
      - **核 lemma**: cost が確率多重集合のみで決まる (label/carrier 非依存) ことを示す
        補題、または両 cost を `huffmanCost_step` で同時に剥がし帰納で一致させる。
        ```lean
        lemma huffmanCost_merged_carrier_eq
            (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
            (a b : α) (hab : a ≠ b) (h_card : 3 ≤ Fintype.card α)
            (h_first_merge : <a,b が initMultiset P で first-merged を要すれば>) :
            huffmanCost (huffmanStep (initMultiset P) _ _).val.2.2
              = expectedLength (mergedMeasure P a b hab)
                  (huffmanLength (mergedMeasure P a b hab)) := by
          sorry  -- @residual(plan:huffman-cost-level-optimality)  ← core risk
        ```
      **core risk**: (i) `a,b` が `initMultiset P` の first `huffmanStep` で実際に merge される
      か (`exists_sibling_min_pair` の (a,b) は global-min/rest-min だが `huffmanStep` の
      決定的 min が同じ pair を選ぶ保証は colex tie-break 次第)。(ii) prob 多重集合一致から
      cost 一致を導く補題が Mathlib/自作で取れるか。**ここが破綻したら §撤退ライン C3'**。
- [ ] **C3-b**: C3-a が要求する first-merge 補題 (`huffmanStep (initMultiset P)` の
      `.val.1`, `.val.2.1` が `{a}`, `{b}` group)。`huffmanStep_min_fst`/`_min_snd`
      (`Huffman.lean:309`/:357) + `exists_sibling_min_pair` の min 性で取れるか確認。
      tie がある場合の colex tie-break で a/b 以外が選ばれうる懸念
      (`huffman-strong-form-completion-plan.md` 判断ログ #5 の dead-end と同根)。
      **これが取れないことが C3 の最大の不確実性**。§撤退ライン参照。

### Phase C4 — cost-level bridge L 再構成 📋

- [ ] **C4-a**: `huffmanLength_bridge_L` の cost 版を per-symbol link 無しで立てる:
      ```lean
      lemma expectedLength_merged_cost_bridge
          (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
          (h_card : 2 ≤ Fintype.card α) (a b : α) (hab : a ≠ b)
          (h_sibling : huffmanLength P a = huffmanLength P b) :
          expectedLength P (huffmanLength P)
            = expectedLength (mergedMeasure P a b hab)
                (huffmanLength (mergedMeasure P a b hab))
              + (P.real {a} + P.real {b}) := by
        sorry  -- @residual(plan:huffman-cost-level-optimality)
      ```
      論証 chain: `expectedLength P (huffmanLength P)` =[C1-b]= `huffmanCost (initMultiset P)`
      =[C2 `huffmanCost_step`]= `huffmanCost s'' + (P{a}+P{b})` =[C3]=
      `expectedLength (mergedMeasure ...) (huffmanLength (mergedMeasure ...)) + (P{a}+P{b})`。
      規模 ~30-60 行 (C1-b/C2/C3 を連結するだけ)。
      **結論型は既存 `h_BL` (`HuffmanOptimality.lean:1042` の結果) と同一** なので Phase M の
      calc は無改変。

### Phase M — 帰納核改変 + 無引数 publish 📋

- [ ] **M-a**: `huffmanLength_optimal_aux_with_hypotheses` の **`h_ident` 引数を除去**した
      新 motor `huffmanLength_optimal_aux` を立てる (or 既存を直接編集)。step case で
      `h_L'_link` (`:1036-1040`) と `huffmanLength_bridge_L` 呼出 (`:1042`) を削除し、
      代わりに `expectedLength_merged_cost_bridge` (C4) を `h_BL` として使う。
      `h_swap` 引数は残す (Hyp1 は genuine、ただし `swap_normalization_proof` で後段除去)。
      他の step (sibling pair / l_norm / bridge_R / IH / calc) は無改変。規模 ~改変 20 行。
- [ ] **M-b**: 無引数 `huffmanLength_optimal` を
      `huffmanLength_optimal_aux (Fintype.card α) swap_normalization_proof P hP l hl_pos
      hl_kraft rfl` で publish (~6 行)。`swap_normalization_proof` は
      `HuffmanStrongForm.lean:153` から import (循環チェック: HuffmanStrongForm が
      HuffmanOptimality を import する向きなので、`huffmanLength_optimal` は
      **HuffmanStrongForm.lean 末尾** or 新 file に置く — §file 配置)。
- [ ] **M-c**: 既存 `huffmanLength_optimal_with_hypotheses` / `_modulo_aux_ident` は API
      後方互換のため残置 (consumer があれば壊さない)。`@residual` は除去 (新 motor が
      hypothesis なしで閉じたので、これらは optional な weak-form として `@audit:ok` 化
      可能か独立 audit で判定)。

### Phase R — FALSE wall retract + 検証 📋

- [ ] **R-a**: FALSE 5 件の retract 手順 (§下「FALSE wall の retract 手順」)。
- [ ] **R-b**: 触れた全 file `lake env lean <file>` silent。`Huffman.lean` を編集する場合
      (C1/C2 追記) は `lake build Common2026.Shannon.Huffman` で olean refresh 後、下流
      Huffman* file を個別検証。
- [ ] **R-c**: `#print axioms huffmanLength_optimal` で `sorryAx` 非依存確認
      (`Classical.choice` / `propext` / `Quot.sound` のみ許容 = 標準B 達成)。

## FALSE wall の retract 手順

機械検証で FALSE 確定済の 5 declarations。本 plan の新 motor は **これらを一切経由しない**
(hypothesis 引数に渡さない) ため、retract は新 headline publish 後に行える:

| # | file:line | declaration | 種別 | retract 方針 |
|---|---|---|---|---|
| 1 | `HuffmanMergedIdentBody.lean:131` | `MergedHuffmanAuxIdentHypothesis` (abbrev) | FALSE predicate | consumer (`huffmanMergedIdentification_of_aux`:157 / `huffmanLength_optimal_modulo_aux_ident`) が無くなれば削除。残すなら `@audit:retract-candidate(false-hypothesis)` 維持 |
| 2 | `HuffmanOptimality.lean:786` | `HuffmanMergedIdentificationHypothesis` (abbrev) | FALSE predicate | weak-form headline `_with_hypotheses` の `h_ident` 引数を削除した新 motor に置換後、API 残置なら tag 維持、削除可なら削除 |
| 3 | `HuffmanColexDeterminism.lean:353` | `collapseLabel_huffmanLengthAux` (lemma, sorry) | FALSE statement | term-level consumer 0 件 (確認済)。**削除推奨** (`@audit:defect(false-statement)` の sorry は honest marker だが statement が偽なので proof done 不能、dead artifact)。削除で `HuffmanColexDeterminism.lean` の Section J 丸ごと除去 |
| 4 | `HuffmanT1APPrimeBody.lean:73` | `swapStepLeChainHypothesis_holds` | transitively false-premised | chain conjunct (#1) が偽なので vacuous。consumer 確認後 retract |
| 5 | `HuffmanSwapStepChainBody.lean:235` | `swapStepLeChainHypothesis_holds_via_subpredicates` | transitively false-premised | 同上 |

**手順**:
1. Phase M で新 headline `huffmanLength_optimal` が hypothesis なしで閉じたことを確認。
2. 各 FALSE declaration の term-level consumer を `rg` で再確認 (docstring 言及は除外、
   `rg -n "<name>" Common2026/ | grep -v "^.*--"` で declaration 参照のみ)。
3. consumer 0 件のもの (#3 は確認済) は削除。consumer が weak-form API として残るもの
   (#1/#2) は abbrev を残し、tag を `@audit:retract-candidate(false-hypothesis)
   @audit:closed-by-successor(huffman-cost-level-optimality)` に更新 (slug を本 plan に
   付替え — 本 plan が genuine closure を達成したため)。
4. 独立 honesty audit (orchestrator が `honesty-auditor` 起動) で signature の honesty +
   slug 整合を verify。

**注意 (CLAUDE.md 共有壁の regularity 落とし防止)**: retract で abbrev を消すとき、それを
hypothesis に取っていた wrapper の他の regularity 前提 (`IsProbabilityMeasure` 等) を
道連れに落とさないこと。新 motor は regularity を引数で持つ。

## 設計判断

### `huffmanCost` の `p.2` vs `∑ prob` (C1-a の核)

`huffmanCost` の per-group 重みに `p.2` (group の ℝ 成分) を使うか `(∑_{a∈p.1} prob_a)` を
使うかで C2/C3 の証明難度が変わる:
- **`p.2` 採用**: `kraftPerGroup` (`p.2` を使わず `(∑ 2^(-d))/card`) とは異なるが、merged
  step で `merged.2 = x1.2 + x2.2` が自動的に積まれるので `huffmanCost_step` の merged
  ペナルティ `(x1.2+x2.2)` が `p.2` で直接出る。ただし `initMultiset` の `p.2 = P.real{a}`
  が `expectedLength` の `P.real{a}` と一致する link (C1-b) は singleton で自明。
  **リスク**: 一般の `s` で `p.2` が group 内 leaf の `P.real` 総和に一致する保証は
  initMultiset 由来 descendant に限る (定義的に積まれるので OK だが要確認)。
- **`∑ prob` 採用**: leaf prob を外から与える必要があり initMultiset と結合度が高い。
- **第一選択: `p.2` 採用** (`huffmanStep` が `x1.2+x2.2` で prob を積む設計と整合、
  `kraftPerGroup_step` の merged 寄与計算とも平行)。C1-a の定義はこれで確定し、C2 で
  `p.2` の積み上げが `expectedLength` と整合することを C1-b の singleton 簡約で吸収。

### file 配置

- C1/C2 (`huffmanCost`, `huffmanCost_step`) は **`Huffman.lean` 末尾追記**
  (`kraftPerGroup` 群の隣、同じ template を共有)。`huffmanLengthAux` の private helper に
  依存しないので新 file でも可だが、`huffmanLengthAux_step_*` が同 file なので Huffman.lean
  が自然。
- C3/C4 (`huffmanCost_merged_carrier_eq`, `expectedLength_merged_cost_bridge`) は
  `mergedMeasure` (HuffmanOptimality.lean) に依存するので **`HuffmanOptimality.lean` 末尾**。
- M (新 motor + headline) は `swap_normalization_proof` (`HuffmanStrongForm.lean`) に依存。
  import 向き: `HuffmanStrongForm.lean` → `HuffmanOptimality.lean` (前者が後者を import、
  verbatim 確認: HuffmanStrongForm が `huffmanLength_optimal_with_hypotheses` を呼ぶ)。
  ⇒ **無引数 `huffmanLength_optimal` は `HuffmanStrongForm.lean` 末尾** に置く
  (HuffmanOptimality に置くと swap_normalization_proof を import できず循環)。
  新 motor `huffmanLength_optimal_aux` も `swap_normalization_proof` を使わない形
  (h_swap を引数で残す) なら HuffmanOptimality に置け、headline だけ HuffmanStrongForm。
  **Phase 0 で import 向きを verbatim 再確認** (CLAUDE.md 依存方向 verbatim 義務)。

### 帰納核を「新 motor」にするか「既存を編集」するか

`huffmanLength_optimal_aux_with_hypotheses` (`:815`) を直接編集して `h_ident` 引数を消すと、
それを呼ぶ `huffmanLength_optimal_with_hypotheses` (`:1069`) と
`huffmanLength_optimal_modulo_aux_ident` (`HuffmanStrongForm.lean:188`) が壊れる。
- **第一選択**: 既存 motor は残し、`h_ident` 引数なしの新 motor
  `huffmanLength_optimal_aux` を追加 (step case の bridge 部だけ差し替えた copy)。
  既存 weak-form API は無改変で残置 → consumer 後方互換。
- **代替**: 既存を編集して weak-form headline も新 motor に付替え + FALSE abbrev 削除
  (よりクリーンだが影響範囲大)。Phase M で consumer 数を見て判断。

## 撤退ライン

- **C3 破綻 (first-merge 同定 or prob-multiset→cost 補題が取れない)** → **C3' 代替**:
  cost を measure-level で直接定義し直す。`huffmanCost` を multiset 上ではなく
  `expectedLength` の measure-level 漸化として立て、`huffmanStep` を経由せず
  `mergedMeasure` の構成 (`Measure.sum_smul_dirac_singleton`) から cost 差分を直接計算。
  carrier-crossing を完全に回避する代わりに、merged 残木の cost を「`mergedMeasure` 上の
  huffman 語長の期待長」として **定義的に** 受け、`huffmanCost_step` のペナルティ項だけを
  bridge する設計。C3-b の first-merge 同定が依然必要なら、そこが真の壁。
- **C3-b 破綻 (first-merge が決定的 colex で a,b に pin できない)** → これは
  `huffman-strong-form-completion-plan.md` 判断ログ #5 が指摘した dead-end と同根。
  cost-level でも「最初の merge が (a,b) でない」場合、cost 漸化の base が崩れる。
  **回避案**: first-merge の同定を要さない形に C2/C3 を再設計 — `huffmanCost_step` は
  actually-merged pair (`huffmanStep` の `.val.1/.val.2.1`、(a,b) framing 不要) で既に
  閉じるので、bridge を「(a,b) を merge」ではなく「(huffmanStep が選ぶ pair) を merge」で
  立て、(a,b) との同定を cost-level で `exists_sibling_min_pair` の min 性 + cost 不変性で
  吸収できるか検討。これが取れれば C3-b 不要。**最初に C3-b の要否を Phase 0 probe で判定**。
- **C2 が想定外に重い (kraftPerGroup_step の mirror が 200 行超)** → C2 を更に
  `huffmanCost_step_ee` (ee 寄与不変) / `_merged` (x1,x2,merged 寄与) の 2 補題に分割。
- **各 Phase 共通**: 詰まったら `sorry` + `@residual(plan:huffman-cost-level-optimality)`。
  **禁止**: FALSE predicate (`HuffmanMergedIdentificationHypothesis` 等) を hypothesis に
  取り直す / `:= h` 循環 / `:True` スロット / per-symbol depth identity への回帰。

## 規模見積り

- 新規行数: C1 (~120) + C2 (~150-220) + C3 (~150-280) + C4 (~50) + M (~40) ≈ **510-710 行**。
- 想定 sorry (実装中の中間): 5-7 個 (`huffmanCost` 定義、`huffmanCost_step`、
  `huffmanCost_merged_carrier_eq`、first-merge 同定、`expectedLength_merged_cost_bridge`、
  新 motor、headline)。**proof done では 0** (genuine closure 目標)。
- 最大リスク = C3 (carrier-crossing 回避の cost 同定) + C3-b (first-merge 同定)。
  C1/C2 は `kraftPerGroup_step` template の mirror で想定内。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-30 起草 — depth-identity 路線放棄 + cost-level pivot 確定**: 前任
   `huffman-strong-form-completion-plan.md` の per-symbol depth identity 路線は
   `MergedHuffmanAuxIdentHypothesis` / `HuffmanMergedIdentificationHypothesis` /
   `collapseLabel_huffmanLengthAux` の 3 系が全て機械検証で FALSE 確定 (同 plan 判断ログ
   #4/#5)。本 plan は同 plan の pivot 指示「tie-invariant cost-level merge identity へ」を
   具体化。weak-form 帰納核の唯一の hypothesis 2 使用点 = `h_L'_link`
   (`HuffmanOptimality.lean:1036-1040`) を cost-level bridge (C4) で置換する設計。
2. **2026-05-30 起草 — carrier-crossing 評決: `relabel_det` ルート不採用**: orchestrator
   brief の `huffmanLengthAux_relabel_det` で `s'' ↔ initMultiset(mergedMeasure)` cost 一致
   を取る骨格は **取れない** と評決 (§carrier-crossing 評決、3 根拠 verbatim 確認)。
   `relabel_det` は cardinality 保存 per-symbol 不変量で、`s''` の card-2 group `{a,b}` →
   mergedInit の singleton という collapse (cardinality 変化) を表現できず
   (`HuffmanMergedAuxIdent.lean:448-453` 既記録)、かつ per-symbol collapse 自体が FALSE
   (Section J)。代替として cost を **集約 (sum) レベル + carrier 内**で扱う設計に確定
   (`kraftPerGroup_step` が tie 下でも成立する prior が cost 不変性の傍証)。
3. **2026-05-30 起草 — cost-recurrence prior = `kraftPerGroup_step` を template に採用**:
   `huffmanCost_step` (C2) は既存 `kraftPerGroup_step` (`Huffman.lean:770`、証明済) の
   重み `(∑ 2^(-d))/card` を `prob·d` に替えた直接 mirror。これにより C2 は新規発明では
   なく既存 ~180 行証明の平行移植となり、想定内のリスクに格下げ。最大リスクは C3
   (carrier-crossing 回避の cost 同定) + C3-b (first-merge 同定、前任判断ログ #5 dead-end と同根)
   に局所化。

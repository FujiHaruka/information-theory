# T1-A'' Huffman 強形 完遂 — full-B 構造定理で Hyp2 (collapse) を閉じる 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) 章対応進捗 Ch.5 行 + frontier 節 (Huffman 強形) + 判断ログ #6 (pivot 選択肢 **B = depth-from-prob-multiset 構造定理** の経緯は `git log -- docs/textbook-roadmap.md` の 2026-05-26 整理前 commit 旧 #19 追記3/追記4)
> - 直前 (colex 決定化 + 無条件 cornerstone genuine 済): [`huffman-colex-determinism-plan.md`](./huffman-colex-determinism-plan.md)
> - measure 層剥離 + Hyp2 正確 statement: [`HuffmanMergedIdentBody.lean`](../../Common2026/Shannon/HuffmanMergedIdentBody.lean)
>
> **本 plan の位置づけ**: colex 決定化 plan の Phase H2 が、cornerstone `huffmanLengthAux_relabel_det`
> (strict-mono embedding 限定、無条件) を確立した上で **collapse correspondence (`{a}` ↔ `{a,b}`
> の label 拡張不変性)** で停止した。collapse は (a) equal-prob tie 下で 2 木の merge **order** が
> 食い違い、(b) first-step identification が `∀ a b` では FALSE (probe で機械検証済) のため、
> 局所版 (relabel + cornerstone) では閉じない。roadmap 追記4 の判定: 残りは「depth = prob multiset の
> 関数」の特殊形 = **full-B 構造定理 (500+ 行 moonshot)** に逢着する。本 plan は **その full-B 構造定理を
> genuine に証明し、collapse を系で出して `MergedHuffmanAuxIdentHypothesis` を無条件 discharge** する。
>
> **Status (2026-05-21)**: 計画起草。実装未着手。コードは未編集。

## 進捗

- [ ] Phase 0 — full-B statement 確定 probe + 在庫再確認 (skeleton 型チェックのみ) 📋
- [ ] Phase B1 — `huffmanLengthAux` の per-leaf depth を tie-robust に特徴づける structural invariant の定義 + 型チェック 📋
- [ ] Phase B2 — full-B 構造定理: per-leaf depth が prob-multiset の rank-bijection で 2 木間に対応 📋
  - [ ] B2-a — 補助: merged group `(F, p)` の depth は `F` の label に依らず `(prob-multiset, p)` で決まる (label-blindness)
  - [ ] B2-b — confluence/divergence 吸収: equal-prob tie 下の merge-order 発散を invariant が吸収することを strong induction で証明
  - [ ] B2-c — full-B の本体 statement を B2-a/B2-b から組み上げ
- [ ] Phase C — collapse correspondence を full-B の系として導出 (`{a}` ↔ `{a,b}` label 拡張不変性) 📋
- [ ] Phase H2 — `mergedHuffmanAuxIdent_proof : MergedHuffmanAuxIdentHypothesis` を Phase C + sibling driver で組み上げ 📋
- [ ] Phase M — 無引数強形 `huffmanLength_optimal` を `huffmanLength_optimal_modulo_aux_ident` に被せて publish 📋
- [ ] Phase V — 全 file silent + `lake build` + `#print axioms huffmanLength_optimal` で sorryAx 非依存確認 📋

proof-log: yes (Phase B1 の invariant 設計と B2-b の divergence 吸収帰納は迷走しやすい。膨張早期判定の証跡として必須)

## ゴール / Approach

### Goal (最終定理 signature)

`Common2026/Shannon/HuffmanStrongForm.lean` 末尾追記:

```lean
namespace InformationTheory.Shannon.Huffman

/-- Hyp2 discharge — `MergedHuffmanAuxIdentHypothesis` を full-B 構造定理経由で genuine
discharge. NOT a hypothesis pass-through (型 = primitive predicate、`:= by` で実証明、
`:= h` 循環でない). -/
theorem mergedHuffmanAuxIdent_proof : MergedHuffmanAuxIdentHypothesis.{u} := …

/-- **Cover–Thomas Theorem 5.8.1 (strong form)** — 引数 hypothesis なし.
`[LinearOrder α]` のみ構造的仮説 (regularity、load-bearing でない、§honesty). -/
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

### 現況の正確な残スコープ (直前 session 成果の上に立つ)

直前の colex 決定化 plan で **以下が genuine 完了** (全 sorryAx 非依存、`lake build` green):

- **`huffmanStep` colex 決定化** (`Huffman.lean`、`groupKey = toLex (p.2, toColex p.1)`、signature 不変)。
- **無条件 cornerstone `huffmanLengthAux_relabel_det`** (`HuffmanColexDeterminism.lean:189`):
  strict-mono embedding `e : α ↪ γ` 越しの relabel-invariance、`NodupChain` 不要。
- **無条件 step-correspondence** (`huffmanStep_fst/snd/step_relabel_det`、`HuffmanColexDeterminism.lean:81/109/150`)。
- **groupKey 保存鎖** (`toColex_map_le_toColex_map`, `groupKey_relabel_le`, `min_unique_of_key`)。
- **first-step probe (確定)** (`HuffmanFirstStepProbe.lean`): 決定的 first 選択は `(Q{·}, ·)` の lex-min
  (`huffmanStep_initMultiset_fst_isLexMin:60`)、`astar ≤ a` のみ従い `a = astar` は一般に FALSE
  (`chosen_le_given:97`)。⇒ first-step identification 経由の route は **no-go と確定**。
- **Hyp1 完了** (`swap_normalization_proof`, `HuffmanStrongForm.lean:144`)。
- **headline (Hyp1 被せ済・Hyp2 のみ open)** `huffmanLength_optimal_modulo_aux_ident`
  (`HuffmanStrongForm.lean:174`)。

残る open hypothesis は **`MergedHuffmanAuxIdentHypothesis` (`HuffmanMergedIdentBody.lean:135`) 1 つだけ**。
これは strong precondition (`_h_a_min` = a global-min, `_h_b_min` = b rest-min,
`_h_sibling : huffmanLength Q a = huffmanLength Q b`) 下で、subtype carrier `x : {y // y ≠ b}` ごとに:
`huffmanLengthAux (mergedInitMultiset Q a b) x = if x.val = a then huffmanLength Q a - 1 else huffmanLength Q x.val`.

### なぜ局所版 (relabel + cornerstone) で閉じないか — 確立した知見

cornerstone `huffmanLengthAux_relabel_det` は **strict-mono embedding** に沿った
**cardinality 保存** (`Finset.map`) の relabel-invariance のみを与える。collapse correspondence は
2 つの異質な構造変更を同時に要求し、cornerstone の射程外:

1. **label 拡張 (cardinality 変更)**: `mergedInitMultiset` は a-merged を **singleton** `({a}, Q{a}+Q{b})`
   (subtype `{y // y ≠ b}` carrier)、β-側 first-merge 残木は **card-2 group** `({a,b}, Q{a}+Q{b})`。
   `{a} → {a,b}` は cardinality を増やすので `Finset.map` (relabel) では表現不能。
2. **merge-order divergence (tie 依存)**: 同確率 `Q{a}+Q{b}` だが `toColex {a} < toColex {a,b}`
   (`{a} ⊊ {a,b}` より strict)。colex 決定化はこの 2 group を **別位置に sort** するため、後続 step の
   選択が両木で分岐する (コード内反例 `Q={.1,.15,.15,.6}` で確認済)。よって naive な lockstep 帰納
   (2 木の `huffmanStep` を同期させる) は **崩壊**する。

⇒ tie-break order **に依らない** 不変量 (= depth が prob-multiset で決まる Huffman 性質) が必要で、
これが **full-B 構造定理**。決定化は障害 (ii) NodupChain 不成立 / (iii) per-symbol invariance 偽 を
解消したが、(1) label 拡張 + (2) merge-order divergence の同時吸収は full-B でしか閉じない。

### Approach (overall strategy / shape of solution)

full-B 構造定理 = **「`huffmanLengthAux s` の per-leaf depth は、merge 軌跡 (tie-break で選ばれる順)
に依らず、`s` の確率 multiset構造で決まる」**。これを直接 per-leaf レベルで述べるのではなく、
**collapse が要求する最小の形** に絞り込む (設計判断 1)。全体の shape は次の 4 ブロック:

1. **full-B の最小 statement = label-blindness (Phase B1/B2-a/B2-c)。**
   collapse が必要とするのは「per-leaf depth が prob-multiset の関数」という full strength ではなく、
   その **特殊形**: 「`huffmanLengthAux` は、ある group の Finset-**label** を、確率と『その label が
   どの leaf を含むか』を保ったまま別の label に置換しても、各 leaf の depth を変えない」。
   merge-order divergence (障害 2) はこの label 置換で生じる colex 差を invariant が吸収すればよく、
   per-leaf depth を prob 多重集合の rank に明示対応させる full-B 本体までは要らない。これが
   **本 plan の核心の絞り込み** — 設計判断 1 で「最小 statement = label-blindness (一般 relabel ではなく
   "確率と leaf-集合 を保つ label 写像")」と確定する。

2. **merge-order divergence の吸収 = confluence on the depth function (Phase B2-b)。**
   2 木の merge 軌跡そのものは発散する (lockstep 不能)。吸収戦略は設計判断 2 の **(a)
   length-function-level confluence**: 「異なる tie-break choice が生む 2 つの `huffmanStep` 出力 `s''₁`,
   `s''₂` は、得られる **depth 関数** (`huffmanLengthAux ·`) が一致する」を `s.card` の strong induction で
   示す。具体的には label-blind な group 置換は depth 関数を保つ (B2-a) を、再帰の各 step で適用し、
   軌跡が分岐しても depth が合流することを示す。これにより per-leaf 軌跡対応 (lockstep) を **回避**して
   per-leaf depth 一致だけを取る。

3. **collapse correspondence を full-B の系で導出 (Phase C)。**
   label-blindness (B2-c) を `(F, p) = ({a}, Q{a}+Q{b})` ↔ `({a,b}, Q{a}+Q{b})` に instantiate して、
   `huffmanLengthAux (({a},p) ::ₘ rest) z = huffmanLengthAux (({a,b},p) ::ₘ rest) z` (`z ≠ b`) を得る。
   `b` は他 group に現れない fresh element なので、`{a,b}` の `b` 成分は depth に寄与しない。
   relabel は cornerstone (`huffmanLengthAux_relabel_det`) で subtype carrier `{y // y ≠ b}` ↔ β を
   橋渡しし、label 拡張は label-blindness で橋渡しする — 2 つを **別々の補題**で扱い合成する。

4. **Hyp2 組み上げ (Phase H2) + 無引数 publish (Phase M)。**
   sibling driver: `_h_sibling` (a, b 等語長) は a, b が同 depth の sibling であることを意味し、
   sibling pair を 1 leaf に collapse すると merge order に依らず depth が 1 減る (probe 確認済の
   "sibling-driven collapse" route)。これを Phase C の collapse + cornerstone の relabel で
   `MergedHuffmanAuxIdentHypothesis` の RHS (`if x.val = a then huffmanLength Q a - 1 else huffmanLength Q x.val`)
   に一致させる。`huffmanLengthAux_step_merged` (`Huffman.lean:730`、merged leaf は depth +1) と
   `huffmanLengthAux_const_on_group` (`:583`、group 内 depth 一定) を depth 算術に使う。

**honesty 線 (重要)**: 標準B (無条件機械検証)。`[LinearOrder α]` は構造的仮説 (regularity、
有限アルファベットに常に入る、最終定理は full optimality の不等式のまま)。各 Phase の target は
genuine (型 ≠ trivial)。**禁止**: full-B / label-blindness / collapse を結論型 ≡
`MergedHuffmanAuxIdentHypothesis` の fake residual hypothesis で抜く (Section E が明示的に禁じた
name-laundering / `:= h` 循環) / `:True` スロット / 退化定義の悪用 / 偽縮約鎖の上に積む / `sorry`。
撤退する場合も honest 名前付き仮説 (型 ≠ 結論、docstring で load-bearing 明示) のみ。

## 設計判断

### 設計判断 1 — full-B の最小 statement (採用 = label-blindness、full rank-bijection は不要)

**問い (prompt 設計判断 1)**: collapse に必要なのは「length-multiset が prob-multiset の関数」だけか、
それとも per-leaf レベルの不変量 (prob 順位 bijection で length 対応) か。

**結論 (採用)**: collapse が必要とするのは **per-leaf label-blindness** であって、length-multiset レベル
でも full rank-bijection でもない。理由:

- collapse の結論は per-leaf identity (`MergedHuffmanAuxIdentHypothesis` は各 `x : {y // y ≠ b}` ごとの
  等式)。length-multiset レベル (語長の多重集合が等しい) だけでは **どの leaf がどの語長か** が出ず、
  per-leaf identity に落とせない。⇒ length-multiset レベルは **不十分**、却下。
- 一方 full rank-bijection (「同 prob-multiset の 2 木は prob 順位を保つ bijection で length が対応」) は
  collapse には **過剰**。collapse の 2 木は leaf 集合が (`b` を除いて) **同一**で、prob-multiset も同一、
  違うのは 1 group の Finset-label だけ。bijection を構成せずとも「label を変えても各 leaf の depth 不変」
  で十分。over-engineering を避ける。
- **採用 statement (概念形、Phase B1 で確定)**:
  ```lean
  -- label-blindness: group の label `F` を、含む leaf 集合を保ったまま別 label `G` に置換しても
  -- (`F` も `G` も同確率 `p`、置換は他 group に影響しない)、b 以外の leaf の depth を変えない。
  -- 実体は「`({a},p) ::ₘ rest` と `({a,b},p) ::ₘ rest` で z(≠b) の depth が一致」の一般形。
  huffmanLengthAux (({a}, p) ::ₘ rest) z = huffmanLengthAux (({a, b}, p) ::ₘ rest) z   -- (z ≠ b, b ∉ ⋃ rest.label)
  ```
  これを general label `F ⊆ G` (差分が他 group に現れない fresh elements) に一般化するか、collapse
  専用の `{a} → {a,b}` 形に特化するかは Phase B1 の規模見積りで決める (一般版は再帰が回しやすいが
  ~50 行多い、特化版は collapse 直結だが汎用性なし)。**第一候補は一般版** (再帰が label の集合演算で
  自然に閉じるため)。

### 設計判断 2 — merge-order divergence の吸収法 (採用 = (a) length-function-level、(b)(c) は却下/補助)

**問い (prompt 設計判断 2)**: equal-prob tie 下の merge 軌跡発散を吸収する不変量・帰納の取り方。
候補 (a) length-multiset で論じ per-leaf へ prob-rank bijection で落とす / (b) `huffmanStep` の合流性
confluence / (c) 確率順位タグ付き invariant。

**結論 (採用 = 修正 (a) + 補助 (b))**:

- **(a) length-function-level confluence を採用 (prompt の (a) を per-leaf 関数に修正)**。prompt の (a)
  原案「length-multiset レベルで論じ prob-rank bijection で per-leaf に落とす」は、bijection 構成が
  設計判断 1 で不要と判定されたので **bijection は使わない**。代わりに **depth 関数そのものの合流**
  「label-blind 置換は `huffmanLengthAux ·` (関数全体) を保つ」を strong induction で示す。これが回る
  根拠: `huffmanLengthAux_eq_step` (`Huffman.lean:421`) で 1 step 展開すると、depth 関数は
  `fun a => if a ∈ A ∪ B then g a + 1 else g a` (`g = huffmanLengthAux s''`)。label 置換は `A ∪ B` の
  集合構造 (どの leaf を含むか) を保つので `if` 分岐は不変、`g` への帰納が回る。divergence は
  `huffmanStep` が **どの 2 group を選ぶか** の差に出るが、label-blind 置換下では選ばれる group の
  **leaf 集合と確率** が両木で一致する (colex 差は label にしか出ない) ので、選択の leaf-content は同じ。
- **(b) confluence は B2-b の補助に使う**: 「label が違う 2 group のうち決定的 min がどちらを選んでも、
  選ばれた group の leaf-content + 残木の depth 関数は一致」を step 単位の補題として切り出し、(a) の
  induction step に差し込む。full confluence (任意の異 tie-break が後で合流) までは証明せず、
  label-blind 置換に限定した弱い合流で十分。
- **(c) prob-rank タグ付き invariant は却下**: タグの定義 + 保存補題で ~150 行の overhead、設計判断 1 で
  rank-bijection が不要と判定された以上、タグも不要。Lean で帰納が最も軽いのは (a) (既存
  `huffmanLengthAux_eq_step` の `if` 構造をそのまま使える)。
- **strict-mono 限定 cornerstone を超える新道具 (prompt の要求)**: `huffmanLengthAux_relabel_det`
  (strict-mono embedding = injective label 写像、cardinality 保存) を超えて、**non-injective でない
  label 拡張 (`{a} → {a,b}`、cardinality +1)** を扱う新補題 `huffmanLengthAux_label_blind` (Phase B2-c)
  が新道具。これは relabel ではなく **同 carrier 内の group 置換** で、cornerstone とは別系統。

### 設計判断 3 — 既存資産の再利用 vs 新規 (prompt 設計判断 3)

| 資産 | 場所 | 本 plan での用途 |
|---|---|---|
| cornerstone `huffmanLengthAux_relabel_det` | `HuffmanColexDeterminism.lean:189` | Phase C で subtype carrier `{y // y ≠ b}` ↔ β の relabel 橋渡し (collapse の **carrier** 部分)。strict-mono 限定で十分 (subtypeNeEmbedding は injective)。 |
| step-correspondence `huffmanStep_*_relabel_det` | `HuffmanColexDeterminism.lean:81/109/150` | B2-b の confluence 補題の prior (構造を真似る)。直接は使わない (relabel ≠ label 置換)。 |
| `huffmanLengthAux_const_on_group` | `Huffman.lean:583` | Phase C/H2 の depth 算術 (group 内 depth 一定)。collapse 後の `{a,b}` group 内で `a` と `b` が同 depth。 |
| `huffmanLengthAux_step_merged` | `Huffman.lean:730` | H2 の sibling driver (merged leaf は depth +1 = `huffmanLength Q a - 1` の +1 を逆算)。 |
| `huffmanLengthAux_step_other` / `_step_eq_on_other_group` | `Huffman.lean:741/752` | B2-a の induction step (他 group の depth が `s''` に持ち越し)。 |
| `huffmanLengthAux_eq_step` / `_eq_zero` | `Huffman.lean:421/435` | B2 の strong induction の展開/base case。 |
| `huffmanStep_key_min_fst/snd` | `Huffman.lean:284/315` | B2-b の confluence で「label-blind 置換下で min の leaf-content 一致」を groupKey 比較から。 |
| `mergedInitMultiset` + `_huffmanGrouping` + `_card_*` | `HuffmanMergedIdentBody.lean:54/77/110/121` | Phase H2 の入力 multiset (measure-free explicit form)。`huffmanMergedIdentification_of_aux` で原 hypothesis に橋渡し済。 |
| `subtypeNeEmbedding` | `HuffmanMergedAuxIdent.lean:429` | Phase C の carrier 写像 (strict-mono、`Subtype.val`)。 |
| **NodupChain 版機構** (Section B-D, `HuffmanMergedAuxIdent.lean:154-446`) | — | **再利用しない**。決定化で無条件版 (`HuffmanColexDeterminism.lean`) に置換済。Section D の `huffmanLengthAux_mergedInitMultiset_relabel` は `NodupChain` 前提付きで一般 Q に供給不能。本 plan は cornerstone の無条件版を使う。 |
| first-step probe (`HuffmanFirstStepProbe.lean`) | — | **route を否定する証跡として参照のみ**。first-step identification は使わず sibling-driven collapse に行く (probe の verdict)。 |

**新規が必要なもの**: (1) label-blindness invariant (Phase B1 定義 + B2-c 証明)、(2) confluence step 補題
(B2-b)、(3) collapse correspondence の系 (Phase C)、(4) Hyp2 組み上げ (H2)。

### 設計判断 4 — file 配置

- Phase B1/B2/C は **新規 file `HuffmanFullBStructure.lean`** に集約 (import `HuffmanColexDeterminism`
  + `HuffmanMergedIdentBody`)。理由: full-B は ~300-400 行と見込まれ、既存 file への追記は
  `HuffmanColexDeterminism.lean` (270 行) を 600+ に膨らませ可読性を損なう。`HuffmanFirstStepProbe` の
  系譜 (probe → structure) として独立 file が自然。
- Phase H2 (`mergedHuffmanAuxIdent_proof`) + Phase M (`huffmanLength_optimal`) は
  `HuffmanStrongForm.lean` 末尾追記 (headline `huffmanLength_optimal_modulo_aux_ident` と同 file)。
- `Common2026.lean` に `import Common2026.Shannon.HuffmanFullBStructure` を 1 行追加。
  ただし `HuffmanStrongForm.lean` が `HuffmanFullBStructure` を import するなら順序に注意。

## Phase 詳細

### Phase 0 — full-B statement 確定 probe + 在庫再確認 📋

- [ ] inventory (`huffman-optimality-t1apprime-mathlib-inventory.md` / `huffman-mathlib-inventory.md`) を
      **読むだけ** で点検 (別エージェント所掌、編集禁止)。label 置換に使える Finset/Multiset API を心覚え。
- [ ] **設計判断 1 の最小 statement を 1 file skeleton で型チェック**: label-blindness の一般版
      (`huffmanLengthAux (({F}, p) ::ₘ rest) z = huffmanLengthAux (({G}, p) ::ₘ rest) z`、`F`/`G` が
      `z`-非含有差分) と特化版 (`{a} → {a,b}`) の両方を `:= by sorry` で書き、型が通る方/両方を確認。
- [ ] **divergence 吸収の 1 行 probe**: `huffmanLengthAux_eq_step` で 1 step 展開した後、label-blind 置換が
      `if a ∈ A ∪ B` の分岐を保つこと (集合 membership が label に依らず leaf-content で決まる) を skeleton
      で型チェック (証明は B2)。
- [ ] **confluence step の go/no-go probe**: 「label が違う 2 group のうち決定的 min が選ぶ leaf-content が
      両木で一致」を `huffmanStep_key_min_fst` + `groupKey` 比較で 1 行 probe (証明は B2-b)。
- [ ] cornerstone `huffmanLengthAux_relabel_det` の subtypeNeEmbedding 適用が型チェックすることを再確認
      (Phase C で carrier 橋渡しに使う、既に決定化 plan で確立済だが本 file の import 構成で再確認)。

### Phase B1 — label-blindness invariant の定義 + 型チェック 📋

- [ ] `HuffmanFullBStructure.lean` 新規。namespace + pinpoint import。
- [ ] label-blindness の statement を **採用形に確定** (設計判断 1、第一候補 = 一般版)。target: skeleton が
      型チェック (sorry 警告のみ)。
- [ ] full-B 本体 (Phase B2-c で証明) と collapse 系 (Phase C) と Hyp2 (Phase H2) の **全 skeleton** を
      `:= by sorry` で並べ、依存関係 (どの補題がどれを使うか) を型レベルで固定。skeleton-driven の起点。
      規模 (skeleton): ~80-120 行。

### Phase B2 — full-B 構造定理 (label-blindness) の genuine 証明 📋

- [ ] **B2-a**: group の depth が label に依らないことの **step-local 補助補題**。
      `huffmanLengthAux_step_eq_on_other_group` (`Huffman.lean:752`) を prior に、label 置換下で
      「他 group の leaf の depth は `s''` に持ち越し」を示す。target: step-local label-blindness silent。
      規模 ~60-100 行。
- [ ] **B2-b**: **divergence 吸収 = confluence step**。設計判断 2 の核。label が違う 2 multiset
      (`({F},p) ::ₘ rest` と `({G},p) ::ₘ rest`) で、決定的 `huffmanStep` が選ぶ 2 group の **leaf-content**
      (= union の Finset) と **残木の depth 関数** が一致することを示す。`huffmanStep_key_min_fst/snd`
      (`Huffman.lean:284/315`) で min の groupKey 比較、colex 差が leaf-content に影響しないことを使う。
      target: confluence step 補題 silent。規模 ~100-150 行。**最大の divergence risk** — ここで
      「label-blind 置換でも min が別 group を選び leaf-content が食い違う」反例に当たったら撤退ライン。
- [ ] **B2-c**: full-B 本体 = label-blindness を `s.card` strong induction で組み上げ (B2-a + B2-b)。
      `huffmanLengthAux_eq_step` 展開 → B2-b で step が depth 関数を保つ → IH で `s''` へ。
      target: `huffmanLengthAux_label_blind` silent。規模 ~80-120 行。

### Phase C — collapse correspondence (full-B の系) 📋

- [ ] label-blindness (`huffmanLengthAux_label_blind`) を `{a} → {a,b}` に instantiate して
      `huffmanLengthAux (({a}, Q{a}+Q{b}) ::ₘ rest) z = huffmanLengthAux (({a,b}, Q{a}+Q{b}) ::ₘ rest) z`
      (`z ≠ b`、`b` fresh) を得る。`{a,b}` 内で `a`/`b` が同 depth は `huffmanLengthAux_const_on_group`
      (`Huffman.lean:583`)。
- [ ] carrier 橋渡し: cornerstone `huffmanLengthAux_relabel_det` (`HuffmanColexDeterminism.lean:189`) を
      `subtypeNeEmbedding b` で適用し subtype carrier `{y // y ≠ b}` ↔ β を解消 (label 拡張とは別補題、
      合成する)。target: collapse correspondence 補題 silent。規模 ~100-150 行。

### Phase H2 — `mergedHuffmanAuxIdent_proof` 組み上げ 📋

- [ ] **sibling driver**: `_h_sibling` (a, b 等語長) から a, b が同 depth sibling であることを使い、
      collapse 後の depth が `huffmanLength Q a - 1` (merged leaf は 1 段上) であることを
      `huffmanLengthAux_step_merged` (`Huffman.lean:730`) の depth 算術で示す。
- [ ] Phase C の collapse + cornerstone relabel を組み上げ、`MergedHuffmanAuxIdentHypothesis` の RHS
      (`if x.val = a then huffmanLength Q a - 1 else huffmanLength Q x.val`) に各 `x : {y // y ≠ b}` で一致。
      target: `mergedHuffmanAuxIdent_proof : MergedHuffmanAuxIdentHypothesis.{u}` (型 = primitive predicate、
      `:= by` で実証明、`:= h` 循環でない) silent。規模 ~80-150 行。

### Phase M — 無引数強形主定理 📋

- [ ] `huffmanLength_optimal` (`[LinearOrder α]` のみ追加、他 hypothesis なし) を
      `huffmanLength_optimal_modulo_aux_ident mergedHuffmanAuxIdent_proof …` で publish
      (`HuffmanStrongForm.lean` 末尾、~5 行)。

### Phase V — 検証 📋

- [ ] 触れた全 file で `lake env lean <file>` silent (0 sorry / 0 warning):
      `HuffmanFullBStructure`, `HuffmanStrongForm`。
- [ ] `lake build Common2026.Shannon.HuffmanFullBStructure` で olean refresh 後、`HuffmanStrongForm` を
      再検証 (新規 file の olean 反映)。
- [ ] 全体 `lake build` を 1 回 (新規 file 追加後の sanity)。
- [ ] `#print axioms huffmanLength_optimal` で `sorryAx` 非依存を確認 (= 標準B 達成)。
      `Classical.choice` / `propext` / `Quot.sound` のみ許容。
- [ ] `Common2026.lean` に import 1 行追加済を確認。
- [ ] roadmap (別エージェント所掌、本 plan は触らない) に「full-B 構造定理で Hyp2 完全 discharge +
      強形完成」を記録するよう報告で促す。

## 撤退ライン

膨張早期判定点を明示する (本 plan は 500+ 行想定、800+ への膨張兆候を各 Phase で監視):

- **Phase 0 で最小 statement が型チェックしない (label-blindness が `huffmanLengthAux` の `if` 構造で
  自然に表現できない)**: full-B 本体 (label-blindness) が前提から崩れる。この時点で撤退判断 — full-B
  route 自体を断念し honest frontier (`huffmanLength_optimal_modulo_aux_ident`) で停止する旨を判断ログ。
  **これが最初の go/no-go 判定点** (実装着手前)。
- **B2-b 破綻 (confluence step が取れない = label-blind 置換でも min の leaf-content が両木で食い違う)**:
  設計判断 2 (a) の核が崩れる。代替: (c) prob-rank タグ付き invariant へ切替 (~150 行追加、800+ への
  膨張兆候)。**膨張早期判定点**: B2-b が 200 行を超えたら タグ版/別 route を検討する旨を判断ログに記録し
  proof-pivot-advisor へエスカレーション。
- **B2-c の strong induction が回らない (label 置換が再帰の `s''` で保たれない)**: label-blindness の
  一般版 (設計判断 1 第一候補) を `{a} → {a,b}` 特化版に縮小 (~50 行減るが汎用性なし)。それでも回らねば
  撤退ライン。
- **Phase C の carrier 橋渡しと label 拡張の合成が重い (defeq/書き換えが whnf timeout)**:
  `HuffmanColexDeterminism.lean` docstring の dual-instance timeout 教訓 (`[DecidableEq α]` と
  `[LinearOrder α]` の 2 instance で colex 保存鎖が爆発) を踏襲し、carrier variable は `[LinearOrder α]`
  のみ持つ (DecidableEq は導出)。それでも timeout するなら collapse を carrier-fixed (β 側で完結) に
  再構成。
- **規模が 800+ 行へ膨張 (各 Phase 累計が見積りの 1.5 倍)**: full-B route が moonshot を超えると判断し、
  その時点までの genuine な前進 (label-blindness や confluence のうち閉じた分) を独立補題として残し、
  Hyp2 全体は honest frontier で停止。**`MergedHuffmanAuxIdentHypothesis` を fake residual で抜く publish は
  絶対にしない** (Section E / 決定化 plan 撤退ラインの禁止事項)。
- **各 Phase 共通 (honest 限定)**: 行き詰まったら honest 名前付き仮説 (型 ≠ 結論、docstring で
  「load-bearing / NOT a discharge」明示) で抜く。**禁止**: 結論型 ≡ `MergedHuffmanAuxIdentHypothesis` の
  residual symbol (name-laundering) / `:= h` 循環 / `:True` スロット / 退化定義の悪用 / 偽縮約鎖
  (`EqualizingPermHypothesis`) の上に積む / `sorry` / `[LinearOrder α]` 以外の load-bearing 仮説
  (全確率 distinct 等) で「強形」と称する (full optimality に到達しない)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-21 起草 — full-B route (roadmap pivot B) を採用、局所版の死を確定**:
   直前の colex 決定化 plan が cornerstone `huffmanLengthAux_relabel_det` (strict-mono、無条件) を
   確立した上で collapse correspondence で停止した。collapse は (1) label 拡張 (`{a} → {a,b}`、
   cardinality +1、`Finset.map` relabel で表現不能) + (2) merge-order divergence (同確率だが
   `toColex {a} < toColex {a,b}` で後続 step 分岐、`Q={.1,.15,.15,.6}` で機械検証) の同時吸収を要求し、
   cornerstone の射程外。first-step identification は probe (`HuffmanFirstStepProbe.lean`) で
   `∀ a b` では FALSE (`a = astar` 偽) と確定済。⇒ 局所版 (relabel + cornerstone + first-step) は
   全て死に、roadmap 追記4 の pivot B (depth-from-prob-multiset 構造定理) = full-B が唯一の honest route。
2. **2026-05-21 起草 — full-B の最小 statement = label-blindness (full rank-bijection は不要)**:
   設計判断 1 の確定。collapse の結論は per-leaf identity なので length-multiset レベルでは不十分、
   一方 full rank-bijection は collapse (2 木が `b` 除き同 leaf 集合・同 prob-multiset) には過剰。
   必要十分は「group の Finset-label を leaf-content + 確率を保ったまま置換しても per-leaf depth 不変」
   = label-blindness。これにより divergence 吸収を per-leaf 軌跡対応 (lockstep、divergence で崩壊) では
   なく **depth 関数の confluence** で取れる (設計判断 2 (a))。新道具 = `huffmanLengthAux_label_blind`
   (cornerstone の strict-mono cardinality 保存とは別系統の、同 carrier 内 label 拡張不変性)。
3. **2026-05-21 起草 — divergence 吸収は (a) length-function-level confluence、(c) タグ版は却下**:
   設計判断 2 の確定。prob-rank タグ付き invariant (c) はタグ定義 + 保存で ~150 行 overhead、設計判断 2 で
   bijection 不要と判定された以上不要。最軽量は (a) (既存 `huffmanLengthAux_eq_step` の `if a ∈ A ∪ B`
   構造をそのまま使い、label-blind 置換が `if` 分岐を保つことを strong induction で示す)。confluence (b) は
   step 単位の補助補題として (a) に差し込む (full confluence は不要、label-blind 置換限定の弱合流で十分)。
4. **2026-05-21 起草 — file 配置 = 新規 `HuffmanFullBStructure.lean`**: full-B が ~300-400 行と見込まれ、
   `HuffmanColexDeterminism.lean` (270 行) への追記は可読性を損なう。probe → structure の系譜として独立
   file が自然。Hyp2 + 無引数 publish は `HuffmanStrongForm.lean` 末尾。`Common2026.lean` に import 1 行追加。

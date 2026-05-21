# LZ78 Ziv combinatorial core — tree-node-context discharge サブ計画 🌙

> **Parent**:
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md) §「achievability core / 撤退ライン」
> - [`lz78-ziv-inequality-discharge-moonshot-plan.md`](./lz78-ziv-inequality-discharge-moonshot-plan.md) (L-LZ1 系の後続)
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. LZ78 漸近最適性」(Ch.13)
>
> **Goal (短形)**: `IsLZ78ZivCombinatorialCore` (Cover–Thomas Lemma 13.5.4/13.5.5、
> `c·log₂c ≤ -log₂Pₙ` の真の核心) を **LZ 木ノード context** 基盤で genuine に
> discharge し、achievability primitive を完全 discharge → headline 仮定 2→1。
>
> **proof-log: yes** (Phase T2/T3 の measure-theoretic 再証明は判断ログ + 別途 proof-log を残す)

## 進捗

- [ ] Phase M0 — Mathlib + 既存資産 在庫調査 (tree-node sub-distribution / parent-prefix 抽出) 📋
- [ ] Phase T1 — tree-node context モデル化 + parent-prefix 抽出 (worker 不変条件) 📋
- [ ] Phase T2 — per-node sub-distribution `∑_{a} q(node·a | node) ≤ 1` (genuine) 📋
- [ ] Phase T3 — distinct (node, symbol) → `c log c ≤ ∑ -log q` (log-sum 組立) 📋
- [ ] Phase T4 — tree-node 条件付き積 → `-log₂Pₙ` への接続 (telescoping 整合) 📋
- [ ] Phase T5 — `IsLZ78ZivCombinatorialCore` 構築 + headline 再配線 (2→1) 📋
- [ ] Phase V — `Common2026.lean` 編入 + `lake env lean` + `#print axioms` 📋

## 現況 (前任が機械確認、本 plan の前提)

LZ78 achievability sound path は **core hyp `IsLZ78ZivCombinatorialCore` 1 本に縮約済**。

- core の上の層 (Z3 base-2 Ziv 不等式 `ziv_count_mul_logb_le_neg_logb_blockProb`、
  Z4 envelope `lz78Distinct_count_div_le_envelope`、slack `lz78AchievSlack`、
  headline 配線 `lz78_two_sided_optimality_distinct_ziv_core_wired`) は
  **全て genuine 済** (`Common2026/Shannon/LZ78ZivCombinatorics.lean`, sorryAx 非依存)。
- 現在の正確な statement (`LZ78ZivCombinatorics.lean:247`):

  ```lean
  def IsLZ78ZivCombinatorialCore (μ : Measure Ω) (p : StationaryProcess μ α) : Prop :=
    ∀ (n : ℕ) (ω : Ω),
      ((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ)
          * Real.log ((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ)
        ≤ ∑ j ∈ Finset.range (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length,
            - Real.log (condPhraseProb μ p n ω j)
  ```

  すなわち `c · log c ≤ ∑ⱼ -log qⱼ` (qⱼ = `condPhraseProb`)。

### core が既存 foundation で閉じない確定理由 (path-prefix の罠)

- `condPhraseProb μ p n ω j` (`LZ78ZivEntropyBridge.lean:164`) は **path-prefix 比**
  `prefixBlockProb ω (boundary (j+1)) / prefixBlockProb ω (boundary j)`。
- log-sum (`log_sum_inequality`, `aⱼ≡1`, `bⱼ≡qⱼ`) は `c·log(c/∑qⱼ) ≤ ∑ⱼ-log qⱼ` を出すが、
  `c log c` を得るには `∑ⱼqⱼ ≤ 1` が必要。path-prefix の qⱼ は nested ratio `Θ(1)` で
  **`∑ⱼqⱼ ≈ c`** (罠、`LZ78ZivCombinatorics.lean:229-233` のコメントに記録済)。
- Z2 の per-symbol sub-distribution `condNextSymbol_sum_eq_one`
  (`LZ78ZivCombinatorics.lean:159`) は **単一観測 prefix `ω` を固定** した
  `∑_a P(prefix·a) = P(prefix)`。これは tree-node 1 個ぶんの sub-distribution の
  raw material だが、**distinct phrase 横断のグルーピング**にはなっていない
  (phrase boundary は disjoint position 区間で、per-symbol 条件付け prefix が
  全て異なるので distinct-phrase 横断 sub-distribution にならない)。
- genuine route = **LZ 木ノード context で条件付け** (CT 13.5.4)。committed
  StationaryKernel 層に tree-node 基盤は無い (grep: `treeNode`/`nodeContext`/
  `parentNode` = 0)。

## ゴール / Approach (必須)

### Approach — tree-node-context 基盤の全体像

CT 13.5.4/13.5.5 の genuine argument shape を Lean に移す。**鍵となる構造的観察**:
`lz78PhraseStrings` の worker `lz78PhraseStringsAux` (`LZ78GreedyLongestPrefix.lean:81`) は
各 phrase を `w = cur ++ [s]` の形で emit し、その時 `cur ∈ dict`
(= 既出 phrase) **または** `cur = []`。つまり **emit された各 phrase string `w` は
`(parent node = w.dropLast, 新 symbol = w.getLast)` に一意分解**でき、`parent node` は
既出 phrase か `[]` (root)。これが **LZ dictionary tree** そのもの:

```
Cover–Thomas Lemma 13.5.4 (LZ-tree)         本 plan の Lean 化
──────────────────────────────────────     ─────────────────────────────
distinct phrases = tree の node            lz78PhraseStrings = Nodup list of nodes
各 phrase = (parent node, 新 symbol)        w ↦ (w.dropLast, w.getLast) (T1)
node ごとに symbol が分岐                    同一 parent を持つ phrase は symbol distinct
node ごとに ∑_symbol P(child|node) ≤ 1     per-node cylinder sub-distribution (T2)
                                            ← extendCylinder_measureReal_sum_eq 再利用
distinct nodes c 個 → c log c               log-sum を node-context で適用 (T3)
∏ node 条件付き → Pₙ                         tree-node telescoping (T4)
```

**core discharge の道筋** (5 step):

1. **T1 — context モデル化 + parent-prefix 抽出**: phrase string `w` を
   `(context := w.dropLast, symbol := w.getLast)` で表す。worker 不変条件
   「emit 時 `cur ∈ dict`」を補題化 (`lz78PhraseStringsAux_emit_dropLast_mem` 系) し、
   各 distinct phrase の context が既出 phrase string か `[]` であることを genuine に証明。
   **同一 context を持つ distinct phrases は symbol が distinct** (Nodup ⟹ context
   一致なら symbol 不一致) を導く。これが per-node 分岐の構造。

2. **T2 — per-node sub-distribution (★crux, measure-theoretic)**: 各 context (node)
   `v` について、`v` cylinder に対する次 symbol cylinder の条件付き確率
   `q(v·a | v) := P(blockRV_{|v|+1} = v·a) / P(blockRV_{|v|} = v)` が
   `∑_{a∈α} q(v·a | v) ≤ 1` を満たす。**既存 `extendCylinder_measureReal_sum_eq`
   (`LZ78ZivCombinatorics.lean:123`) を node-context 版に再キャスト**
   (現状は単一観測 prefix 固定; node-context 版は固定された tuple `v : Fin m → α` で
   parametrize)。cylinder disjointness + finite additivity は再利用。

3. **T3 — distinct → `c log c`**: distinct phrases を **context でグルーピング**
   (`Finset.sum` の二重和 ∑_node ∑_{symbol at node})。各 node で log-sum 不等式
   (`log_sum_inequality`) に T2 の `∑ q ≤ 1` を入れると `(#children)·log(#children) ≤
   ∑ -log q`。node 全体で集計し、`∑_node #children = c`, convexity (Jensen) で
   `c log c ≤ ∑_node (#children) log(#children) ≤ ∑_all -log q`。
   `card_phraseSet_le_pow` 系 (counting body) との接続は ★規模注意 (下記設計判断 3)。

4. **T4 — `-log₂Pₙ` 接続**: T3 の RHS は **node-context 条件付き** `q(child|node)` の
   sum だが、`IsLZ78ZivCombinatorialCore` の RHS は **path-prefix** `condPhraseProb`
   の sum。両者は **同じ phrase boundary に沿った telescoping で Pₙ に集約される**
   ことを示すか、または core の statement 側を node-context 条件付きで書き直す
   (下記設計判断 4 + 撤退ライン)。base-2 整合は既存 Z3 層が吸収。

5. **T5 — core 構築 + headline 再配線**: T1–T4 を組んで
   `theorem isLZ78ZivCombinatorialCore_of_treeNode (μ p) (hreg : regularity) :
   IsLZ78ZivCombinatorialCore μ p` を genuine に証明。これを
   `lz78_two_sided_optimality_distinct_ziv_core_wired` の `hcore` slot に注入し、
   headline 仮定を `hcore + h_lb` → `h_lb (+ regularity hreg)` に縮約 (2→1)。

### 設計判断 (settle)

#### 判断 1 — tree-node context の Lean モデル化

**採用**: phrase string `w : List α` を `(context := w.dropLast, symbol := w.getLast)`
で表す (新規 struct を作らず、既存 `lz78PhraseStrings : List (List α)` の各要素を
`dropLast`/`getLast` で分解)。理由:

- `lz78PhraseStrings_forall_ne_nil` (`LZ78GreedyLongestPrefix.lean:232`) で
  各 phrase は `≠ []`、`getLast` が定義可能。`dropLast` で context (parent node) を取る。
- worker `w = cur ++ [s]` ⟹ `w.dropLast = cur`, `w.getLast = s`。`cur` は emit 時に
  `dict` に居た (or `[]`)。**parent-prefix 抽出はこの不変条件の補題化が core**。
- 新規 struct (`LZ78TreeNode`) は **作らない**: 既存 `List α` 表現で十分、Mathlib
  の `List.dropLast`/`List.getLast`/`Finset.image`/`List.Nodup` がそのまま効く
  (Mathlib-shape-driven)。tree を陽に構築しない (CT の「木」は概念上のもので、
  必要なのは「同一 context の symbol distinct」+「node ごと sub-distribution」だけ)。

**未確定 (M0/T1 で判定)**: worker 不変条件「emit 時 `cur ∈ dict`」が現状の
`lz78PhraseStringsAux` 定義から genuine に取り出せるか。取り出せれば T1 は中規模、
取り出せない (worker が context を捨てている) なら worker 拡張が要り大規模化
→ 撤退ライン参照。

#### 判断 2 — per-node sub-distribution

**採用**: 既存 `extendCylinder` 系 (`LZ78ZivCombinatorics.lean:39-167`) を
**node-context 版に一般化**。現状の `extendCylinder μ p ω m a` は「観測 `ω` の
length-m prefix を symbol `a` で延長」。node-context 版は **固定 tuple
`v : Fin m → α` (= node) を symbol `a` で延長**:
`nodeExtendCylinder μ p v a := blockRV (m+1) ⁻¹' {Fin.snoc v a}`。

再利用できる genuine 補題 (verbatim conclusion form):
- `extendCylinder_pairwiseDisjoint` (`:49`): `Set.PairwiseDisjoint univ (extendCylinder …)` — node 版に転記可
- `iUnion_extendCylinder` (`:83`): `⋃ a, extendCylinder … = blockRV m ⁻¹' {…}` — node 版に転記可
- `measurableSet_extendCylinder` (`:104`)
- `extendCylinder_measureReal_sum_eq` (`:123`): **`∑_a P(snoc v a) = P(v)` (= の形)** ★
  これがそのまま `∑ q ≤ 1` (正規化後 `condNextSymbol_sum_eq_one` `:159`) を出す核心。

node-context 版は `ω` 依存を切って `v` で parametrize するだけ (現状 `ω` 経由で
`p.blockRV m ω` を渡しているのを `v` 直渡しに) なので **転記 ~中規模**。`∑ q ≤ 1`
(等式でなく不等式) を T3 が直接消費する形 (`log_sum_inequality` の `∑bᵢ ≤ ∑aᵢ` 側)。

#### 判断 3 — distinct → `c log c` (log-sum 組立)

**採用**: 二段 Jensen。

- 内側: 各 node `v` で `log_sum_inequality` (既 genuine, `LZ78ZivEntropyBridge.lean:69`)
  に `aⱼ≡1` (children 数 `k_v` 個)、`bⱼ≡q(child|v)`、`∑bⱼ ≤ 1` (T2) を入れ
  `k_v · log k_v ≤ ∑_{children} -log q` (∑b ≤ 1 で `log(k/∑b) ≥ log k`)。
- 外側: `∑_v k_v = c`、`x↦x log x` の convexity (`Real.convexOn_mul_log`、既 import
  済 `LZ78ZivEntropyBridge.lean:3`) で `c log c = (∑k_v) log(∑k_v) ≤ ∑_v k_v log k_v`
  ... **ではなく** superadditivity 方向に注意 (Jensen は `≤` が逆向き)。
  正しくは `∑_v k_v log k_v ≥ c log c` は **偽**; CT の議論は
  `c log c ≤ ∑_v k_v log(k_v) + c log(#nodes)` 形のグルーピング不等式
  (log-sum を node 集合に対して 1 回適用)。**T3 の正確な補題列は M0/T3 で確定**
  (下記 feasibility リスク #1)。

**接続**: `card_phraseSet_le_pow` (`LZ78ZivCountingBody.lean` の packing/stratification、
特に `card_short_le` `:111` の `Fin(L+1)→Option α` 単射) は **distinct count の
geometric 上界**。T3 のグルーピングで「distinct phrases ↔ distinct (node,symbol)」の
全単射 (`w ↦ (w.dropLast, w.getLast)` が `Nodup` list 上単射) を立て、
`Finset.sum_image` / `Finset.sum_sigma` で二重和に変換。

#### 判断 4 — `-log₂Pₙ` 接続 (telescoping 整合)

**2 案**、T4 で確定:

- **案 A (core statement 維持)**: node-context 条件付き積 `∏ q(child|node)` が
  path-prefix 積 `∏ condPhraseProb` と一致 (or `≤`) し、既存
  `blockProb_neg_log_ge_sum` (`LZ78ZivEntropyBridge.lean:225`) +
  `prod_condPhraseProb_telescope` (`StationaryKernel.lean:73`) に乗る。
  両者の積はどちらも phrase boundary に沿って `prefixBlockProb (boundary c)` に
  telescoping するので **一致が期待される** が、node-context 条件付けと path-prefix
  条件付けの **factor 単位が違う** (path-prefix は phrase 単位 1 factor、node-context
  は symbol 単位の積) ので、`condPhraseProb j = ∏_{symbol in phrase j} q(...|...)` の
  分解補題が要る。これが genuine に立つかが ★最大の接続リスク。
- **案 B (core statement を node-context 版に再定義)**: `IsLZ78ZivCombinatorialCore`
  の RHS を path-prefix `condPhraseProb` から node-context 条件付き sum に書き換え、
  `ziv_count_mul_logb_le_neg_logb_blockProb` (`:283`) 以降の Z3 配線も連動修正。
  この場合 Z3/Z4/headline の再証明が必要 (中規模追加) だが、T4 の接続リスクは消える。
  **案 B を第一候補**とする (Mathlib-shape-driven: T2/T3 が node-context で出る形に
  core 定義を合わせる。textbook 形 path-prefix は後付け equivalence で良い)。

base-2 整合: 既存 Z3 の `Real.logb` 割り算層 (`:283-304`) はそのまま流用。

#### 判断 5 — 既存資産の再利用 vs 新規 / 撤退ライン

**再利用 (黒箱)**:
- `extendCylinder*` 系 (T2 の measure-theoretic 核心、node 版に転記)
- `log_sum_inequality` (T3 内側、無改変)
- `Real.convexOn_mul_log` + `ConvexOn.map_sum_le` (T3 外側)
- `lz78PhraseStrings_nodup` / `_forall_ne_nil` (T1 の distinct/non-empty)
- `card_short_le` / packing (T3 の counting 接続、再利用検討)
- 案 B なら Z4 envelope `lz78AchievSlack*` / headline はそのまま

**新規構築**: T1 parent-prefix 抽出 (worker 不変条件補題)、T2 node-context cylinder
転記、T3 二重和 + node グルーピング、T4 接続、T5 core 構築。**新規 1 ファイル
`Common2026/Shannon/LZ78ZivTreeNode.lean`** に集約 (private helper を共有するため
1 file)。

## Phase 詳細 (skeleton-driven)

各 Phase は target signature + 依存補題 (file:line) + 規模見積を持つ。

### Phase M0 — 在庫調査 📋

- [ ] worker 不変条件「emit 時 `cur ∈ dict`」が `lz78PhraseStringsAux` から genuine に
      取れるか確認 (取れなければ worker 拡張 → 大規模化判定)。`mathlib-inventory`
      subagent には委譲せず本 plan 範囲で `lz78PhraseStringsAux` を精読。
- [ ] Mathlib: `Finset.sum_sigma` / `Finset.sum_image` / `Finset.sum_fiberwise`
      (node グルーピング二重和)、`ConvexOn.inner_le_iff` / `ConvexOn.map_sum_le`
      (T3 外側 Jensen)、`List.dropLast`/`List.getLast`/`List.dropLast_append_getLast`
      の conclusion form を loogle で確認 (`[...]` prerequisites verbatim)。
- [ ] T3 のグルーピング不等式 `c log c ≤ ∑_node k_v log k_v + …` の **正確な形**を
      CT 13.5.5 から確定 (feasibility リスク #1 の解消が M0 のゴール)。
- [ ] 案 A vs 案 B の接続を 1 例 (`block = (a,a,b)`) で手計算し、factor 分解
      `condPhraseProb j = ∏ q(symbol|node)` が成立するか検証 (判断 4 の確定)。

### Phase T1 — context モデル化 + parent-prefix 抽出 📋

- [ ] `lz78PhraseStringsAux_emit_context_mem` (worker 不変条件): emit される `w` の
      `w.dropLast` (= `cur`) は emit 時の `dict` の要素 or `[]`。
      規模: **~80-150 行** (worker 帰納、不変条件が現定義から取れる場合)。
- [ ] `lz78PhraseStrings_sameContext_symbol_distinct`: `Nodup` list 上で
      `w₁.dropLast = w₂.dropLast ∧ w₁ ≠ w₂ → w₁.getLast ≠ w₂.getLast`。
      規模: **~40 行** (`Nodup` + `dropLast_append_getLast` の対偶)。

### Phase T2 — per-node sub-distribution 📋

- [ ] `nodeExtendCylinder` 定義 + `nodeExtend_pairwiseDisjoint` /
      `iUnion_nodeExtendCylinder` / `measurableSet_nodeExtendCylinder`
      (`extendCylinder*` `:49/:83/:104` の node 版転記)。規模: **~80 行**。
- [ ] `nodeExtend_measureReal_sum_le` (★crux): `∑_a P(snoc v a) ≤ P(v)` (≤ で十分)。
      `extendCylinder_measureReal_sum_eq` `:123` の証明を node 版に。規模: **~40 行**。
- [ ] `condNode_sum_le_one` (正規化): `∑_a q(v·a|v) ≤ 1` (`condNextSymbol_sum_eq_one`
      `:159` 類似)。規模: **~30 行**。

### Phase T3 — distinct → `c log c` 📋

- [ ] `node_logsum_step`: 各 node `v` で `k_v · log k_v ≤ ∑_{a child} -log q(v·a|v)`
      (`log_sum_inequality` + `condNode_sum_le_one`)。規模: **~60 行**。
- [ ] `distinct_phrase_node_bijection`: `w ↦ (w.dropLast, w.getLast)` が
      `lz78PhraseStrings` 上単射、二重和 `Finset.sum_sigma`/`sum_image` 変換。
      規模: **~80 行**。
- [ ] `count_mul_log_le_sum_node` (T3 集約): `c log c ≤ ∑_all -log q` の node-context 形。
      ★T3 のグルーピング不等式 (M0 で確定した正確形)。規模: **~120-200 行** (feasibility
      リスク #1 が顕在化すればここが膨らむ)。

### Phase T4 — `-log₂Pₙ` 接続 📋

- [ ] (案 B 採用時) `IsLZ78ZivCombinatorialCore` を node-context RHS に再定義、
      `condPhraseProb_eq_prod_condNode` (factor 分解) または直接 telescoping。
      規模: **~80-150 行**。
- [ ] tree-node telescoping → `prefixBlockProb (boundary c)` → `Pₙ` (≥)。
      `prod_condPhraseProb_telescope` `:73` / `prefixBlockProb_antitone`
      (`StationaryKernel.lean:157`) 再利用。規模: **~60 行**。

### Phase T5 — core 構築 + headline 再配線 📋

- [ ] `isLZ78ZivCombinatorialCore_of_treeNode (hreg)` : `IsLZ78ZivCombinatorialCore μ p`
      を genuine 構築。許容仮説は regularity (full-support cylinder 正値) のみ。
      規模: **~50 行**。
- [ ] `lz78_two_sided_optimality_distinct_ziv_core_discharged`: headline を
      `hcore` 不要版に。`lz78_two_sided_optimality_distinct_ziv_core_wired` `:678` の
      `hcore` を `isLZ78ZivCombinatorialCore_of_treeNode hreg` で埋める。仮定 2→1。
      規模: **~30 行**。

### Phase V — 編入 + 検証 📋

- [ ] `Common2026.lean` に `import Common2026.Shannon.LZ78ZivTreeNode` 追記。
- [ ] `lake env lean Common2026/Shannon/LZ78ZivTreeNode.lean` silent (0 sorry / 0 warning)。
- [ ] `#print axioms isLZ78ZivCombinatorialCore_of_treeNode` で sorryAx 非依存確認。

## 規模見積 + feasibility

| Phase | 中央 | 出力 | リスク |
|---|---|---|---|
| M0 | 0 行 (調査) | worker 不変条件 + T3 形 + 案A/B 確定 | ★ feasibility gate |
| T1 | **120-190 行** | parent-prefix 抽出 | worker 不変条件が取れるか |
| T2 | **150 行** | per-node sub-distribution | 低 (転記主体) |
| T3 | **260-340 行** | `c log c` 組立 | ★ グルーピング不等式 (#1) |
| T4 | **140-210 行** | `-log₂Pₙ` 接続 | ★ factor 分解 / 案 B 再証明 |
| T5 | **80 行** | core 構築 + headline | 低 |
| V | **5 行** | import + 検証 | 低 |
| **累計** | **~750-1100 行** | 1 新規ファイル | — |

**feasibility 判定 (最重要)**: tree-node-context 基盤の genuine 化は **現実的だが
中〜大規模 (~750-1100 行)**、3 つの load-bearing リスクに依存:

1. **(T3) グルーピング不等式の正確形** — `c log c ≤ ∑_node …` の Jensen 方向。
   CT 13.5.5 は単一の log-sum を node 集合に適用する形なので **Mathlib の
   `log_sum_inequality` 1 回適用で出る可能性が高い** (二段 Jensen 不要かもしれない)。
   M0 で確定。最も数学的に微妙な点。
2. **(T1) worker 不変条件抽出** — `lz78PhraseStringsAux` が emit 時の `cur ∈ dict` を
   保持している。定義 (`LZ78GreedyLongestPrefix.lean:85-90`) の `if w ∈ dict` 分岐から
   **genuine に取り出せる見込みが高い** (worker は `cur` を持って再帰しており、
   emit は `else` 枝 = `w ∉ dict` だが `cur = w.dropLast` の素性は別途必要)。
   取れなければ worker を context 付きに拡張 (+150 行) → 撤退ライン T1-fallback。
3. **(T4) node-context ↔ path-prefix 接続** — 案 B (core 再定義) で **回避可能**。
   案 B は Z3 配線の再証明 (+100 行) を払うが接続リスクを消す。第一候補。

**committed 資産でどこまで再利用**: T2 の measure-theoretic 核心
(`extendCylinder_measureReal_sum_eq`) と T3 の log-sum/Jensen
(`log_sum_inequality`, `Real.convexOn_mul_log`) は **既に genuine で存在**し転記主体。
distinct/non-empty 不変条件 (`lz78PhraseStrings_nodup`, `_forall_ne_nil`)、
telescoping (`prod_condPhraseProb_telescope`)、prefix monotonicity
(`prefixBlockProb_antitone`)、base-2 層 (Z3) も再利用。**真の新規構築は
T1 parent-prefix 抽出 + T3 node グルーピング + T4 接続 (~400-600 行)**。

## 撤退ライン (honest 限定)

標準B。core を genuine 証明する (型≠結論、`:= h` 循環/`:True`/結論同型 fake residual
**禁止**)。許容仮説は **regularity のみ** (full-support cylinder 正値 `hreg`、ergodic;
`isLZ78PerPathParsingFactorization_of_pos` と同族)。

- **T1-fallback**: worker 不変条件が現定義から取れない場合、worker を context 付き
  (`lz78PhraseStringsAux'` が `(node, symbol)` を emit) に拡張し、既存
  `lz78PhraseStrings` との一致 (`map`) を別途証明。+150 行、scope 内。
- **T3 撤退 (最終手段)**: グルーピング不等式が Mathlib で genuine に組めず、
  かつ自前 Jensen 補強も 200 行超で立たない場合 — **`IsLZ78ZivCombinatorialCore`
  を isolated honest hyp のまま現状維持** (`LZ78ZivCombinatorics.lean:247` の現状)。
  この場合 headline 仮定は 2 のまま、本 plan は T1/T2 (genuine な tree-node sub-
  distribution 基盤) を publish して **次 plan に道を残す**。撤退時も T2 の
  per-node sub-distribution は genuine 資産として残る (no `:True`, no 循環)。
- **honest 撤退の形式**: 行き詰まり時も `IsLZ78ZivCombinatorialCore` の現 docstring
  (`:210-246`, 「NOT a discharge / load-bearing」明示) を維持。新規に
  `*_discharged`/`*_full` の name laundering をしない。部分 genuine 成果は
  正直な名前 (`nodeExtend_measureReal_sum_le` 等、結論と一致しない補題) で publish。

## 検証

- `lake env lean Common2026/Shannon/LZ78ZivTreeNode.lean` が silent (0 sorry / 0 warning)。
- `#print axioms isLZ78ZivCombinatorialCore_of_treeNode` が `sorryAx` 非依存。
- headline 再配線後 `#print axioms lz78_two_sided_optimality_distinct_ziv_core_discharged`
  で残る honest hyp が `h_lb` (converse, Core 2) + `hreg` (regularity) のみであることを確認。

## 当面の next step

**Phase M0 から着手**。M0 が feasibility gate: (a) worker 不変条件の抽出可否
(T1 規模を決める)、(b) T3 グルーピング不等式の正確形 (最大の数学リスク #1)、
(c) 案 A/B 接続の手計算検証 (T4 方針確定) の 3 点を解消してから T1 skeleton に進む。
M0 で #1 が「`log_sum_inequality` 1 回適用で出る」と確認できれば全体は中規模
(~750 行) で genuine 完遂見込み。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

# LZ78 achievability — a.s.-eventual ergodic (CT 13.5.3 original) サブ計画 🌙

> **Parent**:
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md) §「achievability core / 撤退ライン L-LZ1」
> - [`lz78-completion-plan.md`](./lz78-completion-plan.md) §「Core 1 (Eq.13.124)」(Phase Z1–Z4)
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. LZ78 漸近最適性」(Cover–Thomas Ch.13.5, Thm 13.5.3)
>
> **Supersedes (方針として)**: per-block `c·log c ≤ -log Pₙ` を core にする全アプローチ
> ([`lz78-ziv-treenode-plan.md`](./lz78-ziv-treenode-plan.md) Phase T4–T5、
> [`lz78-completion-plan.md`](./lz78-completion-plan.md) Phase Z2–Z3)。これらの per-block
> formulation は **数学的に FALSE** と本 round で機械確定 (下記 §現況)。本 plan は
> **a.s.-eventual ergodic** に path を切り替える。treenode-plan の T1/T2/T3 (tree-node
> sub-distribution 基盤) は genuine 資産として残り、本 plan からも部分再利用候補。
>
> **Goal (短形)**: achievability の honest input `IsLZ78AchievabilityZivUpperBound`
> (`LZ78AchievabilityLimsup.lean:114`) を、per-block の偽 core を経由せず
> **a.s.-eventual `limsup (c·log₂c)/n ≤ entropyRate₂` 構造**から genuine に構成し、
> base-2 distinct headline の achievability primitive を discharge (headline 仮定 2→1)。
> 標準B、0 sorry / 0 warning、`#print axioms` で sorryAx 非依存。
>
> **proof-log: yes** (Phase A2 の a.s.-eventual core 接続は判断ログ + 別途 proof-log を残す)

## 進捗

- [ ] Phase M0 — feasibility gate: a.s.-eventual core の正確 formulation + ergodic 接続が既存機構で組めるか確定 📋
- [ ] Phase A1 — a.s.-eventual envelope reduction: `lz/n = (c·log₂c)/n + o(1)` を envelope から genuine に 📋
- [ ] Phase A2 — a.s.-eventual Ziv core: `limsup (c·log₂c)/n ≤ entropyRate₂` a.s. の genuine 接続 (★ feasibility 核心) 📋
- [ ] Phase A3 — `IsLZ78AchievabilityZivUpperBound` 構成 (a.s.-eventual 形 assembly) 📋
- [ ] Phase A4 — headline 再配線 (achievability primitive discharge, 仮定 2→1) 📋
- [ ] Phase V — `InformationTheory.lean` 編入 + `lake env lean` + `#print axioms` 📋

## 現況 (本 round で機械確定、本 plan の前提)

### per-block formulation は FALSE (確定)

- `not_isLZ78ZivCombinatorialCoreOverhead` (`LZ78ZivTreeBridge.lean:130`, sorryAx 非依存):
  per-block `∀n∀ω` の overhead 付き core `c·log c ≤ -log Pₙ + c·log(|α|+1)` は **偽**。
  反例 = constant process (`X≡true`, Dirac on `Unit`)、`n=16` で `Pₙ=1` (`-log Pₙ=0`)、
  `c=5` distinct phrases、`5·log 5 > 5·log 3`。
- clean core `c·log c ≤ -log Pₙ` も偽 (`(a,a,b)`)。`O(c)` overhead で **修復不能**
  (`Pₙ→1` で `-log Pₙ→0` だが `c log c ∼ √n·log√n → ∞`、ギャップは super-`O(c)`)。
- 帰結として、`IsLZ78ZivCombinatorialCore` (`LZ78ZivCombinatorics.lean:247`、path-prefix
  `condPhraseProb` の sum 形) も同じ per-block 失敗を継承する (path-prefix 罠
  `∑ⱼ qⱼ ≈ c`、`LZ78ZivCombinatorics.lean:229-233`)。tree-node 経由 (treenode-plan T4)
  の path-block 接続も成立しない。

### genuine 完成済 (sorryAx 非依存、再利用基盤)

- **RHS = SMB 収束 (機械確認済)**: `shannon_mcmillan_breiman` (`SMBAlgoetCover.lean:2840`)
  は `#print axioms` で **`[propext, Classical.choice, Quot.sound]` のみ**に依存 (本 plan
  起草時に確認)。`blockLogAvg → entropyRate` を a.s. に genuine 供給。base-2 化
  `shannon_mcmillan_breiman₂` (`LZ78ConverseKraft.lean:133`) で
  `blockLogAvg₂ → entropyRate₂` a.s.。**load-bearing hyp なし、無条件**。
- **LHS counting (genuine)**: `lz78PhraseStrings_mul_log_le` (`LZ78ZivCountingBody.lean:353`)
  = `c·log c ≤ 8·log(|α|+1)·n` (constant rate `K`)。`lz78Distinct_count_div_le_envelope`
  (`LZ78ZivCombinatorics.lean:327`) = `c/n ≤ 2K/log n + 1/√n` (`→ 0`)。
- **bit-length 展開 (genuine)**: `lz78DistinctEncodingLength_eq` + `LZ78Phrase.bitLength_eq`
  で `lz = c·(Nat.log 2 (c+1) + Nat.log 2 |α| + 2)`。
- **achievability 上位層 (genuine, a.s.-eventual を消費する形で既に組まれている)**:
  `IsLZ78AchievabilityZivUpperBound` (`LZ78AchievabilityLimsup.lean:114`, structure) は
  既に **a.s.-eventual** 形 (`∀ᵐ ω, ∀ᶠ n, lz/n ≤ blockLogAvg₂ + slack` + `slack→0`)。
  `lz78_achievability_limsup_le₂` (`:153`) が SMB と組んで `limsup (lz/n) ≤ entropyRate₂`
  を genuine に出す。**本 plan の出力先 (target slot) はここ**。
- **headline (genuine, primitive 引数取り)**: `lz78_two_sided_optimality_distinct_genuine`
  (`LZ78AchievabilityLimsup.lean:233`) は achievability + converse の 2 primitive を取り
  base-2 sandwich → Tendsto を genuine に出す。
- **tree-node 基盤 (genuine, treenode-plan 産)**: `node_logsum_step`
  (`LZ78ZivTreeNode.lean:290`)、`nodeExtend_measureReal_sum_eq` (`:181`)、worker context
  invariant T1 (`:95`)。per-node `k_v·log k_v ≤ ∑ -log q(child|node)` まで genuine。
- **telescoping / prefix monotonicity (genuine)**: `prod_condPhraseProb_telescope`
  (`StationaryKernel.lean:73`)、`prefixBlockProb_antitone` (`:157`)、
  `blockProb_neg_log_ge_sum` (`LZ78ZivEntropyBridge.lean:225`)。

## ゴール / Approach (必須)

### 出力先 (target slot)

`IsLZ78AchievabilityZivUpperBound μ p lz78DistinctEncodingLength slack` を **genuine 構成**
する定理 `isLZ78AchievabilityZivUpperBound_aseventual` を新規 publish し、これを
`lz78_two_sided_optimality_distinct_genuine` の `h_ub` slot に注入して
achievability primitive を discharge。許容仮説は regularity (`hreg`: full-support
cylinder 正値、ergodic) のみ。

### Approach — a.s.-eventual achievability の全体像

本質的洞察: **per-block `c·log c ≤ -log Pₙ` を経由しない**。achievability に必要なのは
`/n` した後の **limsup 上界**だけであり、per-block 不等式 (偽) は途中に不要。

```
lz/n  =  (c/n)·(log₂(c+1)+log₂|α|+2)        [bit-length 展開, genuine]
      =  (c·log₂c)/n  +  (c/n)·O(1)          [c/n→0 envelope で第2項 o(1), genuine]
      =  (c·log₂c)/n  +  o(1)                a.s. (eventually)

target: limsup (lz/n) ≤ entropyRate₂  ⟸  limsup (c·log₂c)/n ≤ entropyRate₂  (★core)
```

★core (`limsup (c·log₂c)/n ≤ H`) を出す道は 2 系統。**M0 でどちらが既存機構で
組めるか判定する** (これが feasibility gate)。

- **Route Q (CT 13.5.3 original, tree-measure 経由)**:
  1. LZ tree が誘導する sub-probability measure `Q_c(x^n)` を定義 (各 node で実測 cylinder
     条件付き、tree-node sub-dist `∑ child q ≤ 1` で `∑ Q ≤ 1`)。
  2. tree-node log-sum (genuine `node_logsum_step` 集約) で **`c·log c ≤ -log Q_c(x^n)`**
     (per-block でも TRUE — `Q_c` は path measure `Pₙ` ではなく tree-measure。disproof は
     `Pₙ` 相手だった、`Q_c` 相手なら成立する)。
  3. ergodic で **`-log Q_c(x^n)/n → H`** a.s.。`Q_c` は `Pₙ` と異なるが、stationarity +
     ergodicity で **同じ entropy rate `H` に収束** (CT の核心 Lemma)。これと SMB の
     `-log Pₙ/n → H` で `(c·log c)/n → H` を sandwich。
  - **feasibility リスク (★最大)**: ステップ 3「`-log Q_c/n → H`」は InformationTheory に
    **不在の ergodic 補題** (tree-measure の AEP)。`Q_c` の定義も InformationTheory に無い。
    SMB/Birkhoff/AEP は `Pₙ` (path block law) 専用で、tree-induced measure には直接効かない。
    library-scale の新規 ergodic 構築 (markov 近似 / k-th order entropy → entropy rate)。
- **Route C (counting + SMB sandwich を直接)**:
  - counting は `c·log c ≤ K·n` (constant `K`、`LZ78ZivCountingBody.lean:353`) しか出ない。
    これは `limsup (c·log₂c)/n ≤ K/log 2` を与えるが **`K ≠ H`** (定数 rate であって
    entropy rate ではない)。`H` まで絞るには結局 source 統計 (cylinder 確率) を使う必要が
    あり、Route Q の tree-measure か markov 近似に帰着。**Route C 単独では `H` に到達不能**
    (counting は universal だが rate が緩い)。

退化ケース (`H=0`, constant process) の整合: `c≈√n` で `(c·log₂c)/n ≈ (log n)/(2√n)·...
→ 0 = H`。per-block では `c log c ≤ -log Pₙ=0` が偽だが、**`/n` 後の limsup は `0 ≤ 0`
で成立** — a.s.-eventual core は退化ケースでも TRUE。これが per-block FALSE と矛盾しない
理由 (設計判断 4)。

## 設計判断 (settle)

### 判断 1 — a.s.-eventual core の正確な formulation

**採用**: core を **`∀ᵐ ω, limsup (fun n => (c(n,ω)·log₂ c(n,ω))/n) atTop ≤ entropyRate₂`**
とする (per-block 不等式 `c log c ≤ -log Pₙ` は **採らない** — 偽)。

理由: target structure `IsLZ78AchievabilityZivUpperBound.upper` は
`∀ᵐ ω, ∀ᶠ n, lz/n ≤ blockLogAvg₂ + slack`。これを `limsup` 形 core から組むには 2 経路:

- **(1a) 直接 limsup**: core を上の limsup 形にし、`IsLZ78AchievabilityZivUpperBound`
  ではなく **`lz78_achievability_limsup_le₂` (`:153`) を bypass** して直接
  `limsup (lz/n) ≤ entropyRate₂` を出す版を新設。target slot は headline の
  `h_limsup_le` ではなく `lz78_two_sided_optimality_distinct_genuine` 内部の
  limsup 半分に相当 — **headline 再配線が必要** (現 headline は `IsLZ78Achievability...`
  structure を取る)。
- **(1b) structure 経由 (現 headline 互換)**: a.s.-eventual な per-`n` 不等式
  `lz/n ≤ blockLogAvg₂ + slack(n,ω)` を **ω 依存 slack** で出す。ただし
  `IsLZ78AchievabilityZivUpperBound.upper` の slack は **`slack : ℕ → ℝ` (ω 非依存)**。
  Route Q の `-log Q_c/n` と `-log Pₙ/n` のギャップ `(-log Q_c + log Pₙ)/n` は **ω 依存で
  eventually → 0 (a.s.)** だが ω-uniform に bound できる保証がない → structure の
  `slack : ℕ → ℝ` に乗らない可能性。

**M0 で確定**: (1b) が structure の `ℕ → ℝ` slack に乗るか (Route Q のギャップが
ω-uniform vanishing か)。乗らなければ **(1a) を採用し structure を ω-依存 slack 版に
一般化** or headline の limsup 半分を直接構成 (中規模追加)。**(1a) 第一候補**
(Mathlib-shape-driven: SMB が limsup 形を直接消費する `lz78_achievability_limsup_le₂`
が既にある)。

### 判断 2 — Ziv の a.s.-eventual 化 (★ core feasibility = go/no-go の核心)

per-block `c log c ≤ -log Pₙ` (偽) を、ergodic で `-log Pₙ/n → H` (SMB) + `c/n → 0` を
使い **eventual に** `(c·log₂c)/n ≤ -log₂Pₙ/n + o(1)` a.s. が出るか — が本 plan の go/no-go。

**判定 (M0 で機械確認、起草時点の見立て)**: **per-block FALSE が `/n` で消える保証はない**。
constant process では消える (`H=0` で両辺 `→0`) が、**`Pₙ→1` family (i.i.d. with `p→1`)** で
`-log Pₙ/n = -log p → 小` (定数), `(c log c)/n → 0` も成立し `0 ≤ -log p` で OK。実は
**`(c log c)/n → 0` が常に成立** (`c/n→0` かつ `log c = O(log n)`)。よって退化的に
`limsup (c·log₂c)/n ≤ H` は **`H ≥ 0` なら自明に成立しそう** に見えるが — **これは罠**。

- `(c log c)/n` の真の漸近は CT では `→ H` (定数 0 ではない、`H>0` の非退化 ergodic で)。
  `c ∼ n/log_b n` (Eq.13.124) なら `c log c ∼ (n/log n)·log(n/log n) ∼ n` (定数 rate),
  `(c log₂c)/n → log b / log 2`... ではなく source 統計依存で `→ H`。
- counting `c·log c ≤ K·n` だけでは `(c log₂c)/n` の **下からの漸近 = H** を捕まえられない
  (counting は上界のみ)。`limsup (c log₂c)/n ≤ H` を出すには `c` の実際の成長を source の
  cylinder 確率で抑える = **Route Q の tree-measure 不等式 `c log c ≤ -log Q_c` が本質的に
  必要** (これだけが `c` を source 統計に結びつける genuine な道)。

**結論 (go/no-go)**: a.s.-eventual core は **数学的に TRUE** だが、その genuine 証明は
**Route Q を要し、Route Q ステップ 3 (`-log Q_c/n → H`) が InformationTheory 不在の major gap**。
counting 単独 (Route C) では `H` に到達できない。**M0 で Route Q ステップ 3 が既存
SMB/Birkhoff から組めるか (= `Q_c` の AEP が `Pₙ` の SMB から derive できるか) を
機械的に詰める。組めなければ撤退ライン (honest hyp 化)**。

### 判断 3 — 既存 SMB/AEP/Birkhoff でどこまで出るか + Mathlib gap

| 部品 | 既存資産 | genuine? | gap |
|---|---|---|---|
| RHS `-log₂Pₙ/n → H` | `shannon_mcmillan_breiman₂` | ✅ (axioms 3 個のみ) | なし |
| LHS counting `c log c ≤ K·n` | `lz78PhraseStrings_mul_log_le` | ✅ | rate が `K≠H` |
| envelope `c/n → 0` | `lz78Distinct_count_div_le_envelope` | ✅ | なし |
| bit 展開 `lz = c(...)` | `lz78DistinctEncodingLength_eq` | ✅ | なし |
| tree-node `c log c ≤ ∑ -log q(child\|node)` | `node_logsum_step` 集約 (treenode T3) | ✅ (per-node) / ⚠ (集約 = treenode-plan 未完) | node→全体集約は treenode-plan T3 残 |
| **tree-measure `Q_c` 定義** | **なし** | ✗ | **新規定義 (Mathlib gap b)** |
| **`c log c ≤ -log Q_c` (per-block, TRUE)** | tree-node sub-dist から (新規) | ✗ | tree-node 集約 + Q_c 接続 |
| **`-log Q_c/n → H` (ergodic AEP)** | **なし** | ✗ | **★ major gap (library-scale ergodic)** |

**Mathlib 壁 4 分類での判定** (textbook-roadmap.md「Mathlib 壁の 4 分類」):
`-log Q_c/n → H` は **(b) 解析/ergodic の壁** (Stam 型と同類)。SMB は `Pₙ` 専用で、
tree-induced measure `Q_c` の AEP は別の ergodic 議論 (markov 近似経由)。Mathlib にも
InformationTheory にも不在。**「選択 (big)」ではなく「未証明 (hard)」**。

### 判断 4 — 退化ケース (H=0, constant process) の整合

**確認済**: constant process (`H=0`) で `c≈√n`, `(c·log₂c)/n ≈ (log n)/(2√n)·O(1) → 0 = H`。
SMB は `-log₂Pₙ/n = 0 → 0` を a.s. に出す (`Pₙ=1` for the Dirac-supported block)。
`limsup (c·log₂c)/n ≤ 0 = entropyRate₂` 成立。**per-block FALSE (n 固定で
`c log c=5 log 5 > 0=-log Pₙ`) と矛盾しない** — `/n` と limsup が ratio を潰す。

honesty: 退化ケースは **vacuous でなく genuine に成立** (`exfalso`/`0=値` の悪用ではない、
両辺が実際に 0 に収束)。a.s.-eventual core を退化ケースで誤魔化さない。

## Phase 詳細 (skeleton-driven)

### Phase M0 — feasibility gate (★ 最重要、着手前必須) 📋

- [ ] **Route Q ステップ 3 の go/no-go**: `Q_c` (tree-induced measure) の AEP
      `-log Q_c/n → H` が、既存 `shannon_mcmillan_breiman` / `BirkhoffErgodic` /
      `AEP` から derive 可能か機械的に詰める。`Q_c` と `Pₙ` の関係 (CT Lemma 13.5.4 の
      tree superadditivity) を Lean shape で書き、必要 ergodic 補題を列挙。
      **不在補題が library-scale (markov order-k entropy → entropy rate の ergodic 収束) なら
      no-go → 撤退ライン**。
- [ ] **judgment 1 (1a vs 1b)**: Route Q のギャップ `(-log Q_c + log Pₙ)/n` が ω-uniform
      vanishing か (structure の `ℕ → ℝ` slack に乗るか) を 1 例で検算。乗らなければ (1a)
      (limsup 直接 + headline 再配線) 確定。
- [ ] **judgment 2 (core feasibility 最終)**: counting 単独 (Route C) で `limsup ≤ H` が
      **絶対に出ない**ことを確認 (counting は `K≠H` の定数 rate のみ)。`H` への絞り込みに
      tree-measure or markov 近似が必須であることを確定。
- [ ] Mathlib: `Filter.limsup_le_of_le` / `Filter.le_limsup_of_le` (`LiminfLimsup`)、
      `Real.logb`、ergodic averaging 系の conclusion form を loogle で確認
      (`[...]` prerequisites verbatim、`mathlib-inventory` subagent に委譲可)。
- [ ] **M0 出力 = go/no-go 判定文**: (a) Route Q ステップ 3 が既存機構で組めるなら
      A2 で genuine 完遂見込み (規模見積)、(b) library-scale gap なら honest hyp 撤退
      (撤退ライン L-AS1)。判断ログに記録。

### Phase A1 — a.s.-eventual envelope reduction 📋

- [ ] `lz78DistinctRate_eq_countLogRate_add_envelope`:
      `lz/n = (c·log₂c)/n + r(n,ω)` で `|r| ≤ env(n)·D` (ω-uniform, `→0`)。
      既存 `lz78DistinctRate_le_blockLogAvg₂_add_slack` (`LZ78ZivCombinatorics.lean:406`)
      の bit-展開部 (`hlz`, `htermA_num`) を **`-log Pₙ` でなく `c log c` で止める**形に
      再利用。規模: **~80-120 行** (既存証明の前半流用)。
- [ ] `countLogRate_envelope_tendsto`: `r(n,·) → 0` (envelope `c/n→0` 経由)。
      `lz78AchievSlack_tendsto_zero` (`:565`) の構造流用。規模: **~40 行**。

### Phase A2 — a.s.-eventual Ziv core (★ feasibility 核心、M0 の go 判定後のみ) 📋

> **着手条件**: M0 で Route Q が go と判定された場合のみ。no-go なら撤退ライン L-AS1 に直行。

- [ ] (Route Q go の場合) `treeInducedProb` (`Q_c`) 定義 + `count_mul_log_le_neg_log_treeProb`
      (`c log c ≤ -log Q_c`, per-block TRUE)。tree-node `node_logsum_step` (`:290`) 集約 +
      treenode-plan T3 (distinct→`c log c` グルーピング) を流用。規模: **~200-300 行**。
- [ ] (★ major gap) `treeProb_aep`: `-log Q_c/n → entropyRate` a.s.。**M0 で derive 可能と
      判定された手段で構成**。不在 ergodic 補題が library-scale なら **ここで撤退** (L-AS1)。
      規模: **~300-600 行 (go の場合) / no-go なら honest hyp**。
- [ ] `aseventual_countLogRate_limsup_le`: A1 (`lz = c log c/n + o(1)`) + A2 core +
      `treeProb_aep` + SMB sandwich で `limsup (lz/n) ≤ entropyRate₂` a.s.。
      規模: **~80-120 行**。

### Phase A3 — `IsLZ78AchievabilityZivUpperBound` 構成 (or limsup 直接) 📋

- [ ] (judgment 1 = 1b) `isLZ78AchievabilityZivUpperBound_aseventual (hreg)`:
      structure 構成 (ω-uniform slack)。規模: **~60 行**。
- [ ] (judgment 1 = 1a) limsup 半分を直接出す版 + headline 再配線で structure bypass。
      規模: **~100 行 (+ headline 一般化)**。

### Phase A4 — headline 再配線 (achievability primitive discharge) 📋

- [ ] `lz78_two_sided_optimality_distinct_aseventual`: `lz78_two_sided_optimality_distinct_genuine`
      の `h_ub` を A3 で埋め、achievability 仮定を discharge。残る honest input は
      converse `h_lb` (Core 2) + regularity `hreg` のみ (仮定 2→1)。規模: **~30 行**。

### Phase V — 編入 + 検証 📋

- [ ] `InformationTheory.lean` に新規ファイル import 追記。
- [ ] `lake env lean InformationTheory/Shannon/<new>.lean` silent (0 sorry / 0 warning)。
- [ ] `#print axioms isLZ78AchievabilityZivUpperBound_aseventual` で sorryAx 非依存確認。
      Route Q go なら honest hyp は `hreg` のみ。no-go なら honest hyp (L-AS1) の docstring
      に「load-bearing / NOT a discharge」明示。

## 規模見積 + feasibility 判定 (最重要)

| Phase | 中央 (go) | 出力 | リスク |
|---|---|---|---|
| M0 | 0 行 (調査) | go/no-go 判定 + Route 確定 | ★★ feasibility gate |
| A1 | 120-160 行 | envelope reduction | 低 (既存流用) |
| A2 | **500-900 行** (go) | a.s.-eventual core + `Q_c` AEP | ★★★ major ergodic gap |
| A3 | 60-160 行 | structure or limsup 構成 | 中 (1a/1b 分岐) |
| A4 | 30 行 | headline 再配線 | 低 |
| V | 5 行 | import + 検証 | 低 |
| **累計 (go)** | **~700-1250 行** | 1-2 新規ファイル | — |

**feasibility 判定 (go/no-go)**:

- **RHS は完全 genuine** (SMB `[propext, Classical.choice, Quot.sound]` のみ)。**LHS counting /
  envelope / bit 展開も genuine**。残るギャップは **LHS `(c log c)/n` を RHS `H` に
  a.s.-eventual で繋ぐ一点**。
- a.s.-eventual core (`limsup (c log₂c)/n ≤ H`) は **数学的に TRUE** (per-block FALSE と
  矛盾しない、退化ケースも整合)。しかし **counting 単独では `H` に到達不能** (定数 rate
  `K≠H`)。`H` への絞り込みには **tree-measure `Q_c` の AEP `-log Q_c/n → H` が本質的**。
- **`-log Q_c/n → H` は InformationTheory にも Mathlib にも不在の major ergodic 補題**
  (markov 近似 / k-th order entropy → entropy rate、textbook-roadmap「Mathlib 壁 (b)
  解析/ergodic」)。SMB は `Pₙ` (path block law) 専用で tree-induced measure には効かない。
- **結論 = 慎重 (cautious go, gated on M0)**: per-block が偽だった以上 a.s.-eventual も
  慎重判定が必要。本 plan の go/no-go は **M0 で Route Q ステップ 3 (`Q_c` AEP) が既存
  SMB/Birkhoff から derive 可能か**に懸かる。
  - **derive 可能なら go** (~700-1250 行、A2 が主)。
  - **library-scale な新規 ergodic 構築が必要なら no-go** → 撤退ライン L-AS1 (honest hyp)。
    その場合でも tree-node 基盤 (T1/T2/T3) + A1 envelope reduction は genuine 資産として
    publish、`-log Q_c/n → H` を **honest named hyp** (regularity でなく load-bearing
    ergodic content) として明示し、次 plan に道を残す。

**起草時の見立て**: per-block disproof と同じ source 統計の困難 (`c` を `Pₙ` に直接繋げない)
が a.s.-eventual でも残る。tree-measure `Q_c` 経由は数学的に正しい道だが、その AEP は
**SMB と独立な新規 ergodic 定理**で、InformationTheory の既存機構では **直接組めない見込みが高い**
(SMB は 2800 行の専用構築。`Q_c` AEP は同規模の別構築になりうる)。**したがって本 plan の
最も確度の高い着地は「A1 (envelope reduction) を genuine に閉じ、`-log Q_c/n → H` を
honest named hyp として A2 で明示する撤退ライン形」**。完全無仮説 achievability は M0 が
go を出した場合のみ。

## 撤退ライン (honest 限定)

標準B。a.s.-eventual core を genuine に。**per-block 偽 core (`IsLZ78ZivCombinatorialCore` /
`IsLZ78ZivCombinatorialCoreOverhead`) には依存しない** (disproof 済)。許容仮説は
regularity (`hreg`: full-support cylinder 正値、ergodic) のみ。

- **L-AS1 (主要撤退、確度高)**: M0 で `Q_c` AEP (`-log Q_c/n → H`) が既存 ergodic 機構から
  derive できないと判定した場合、これを **honest named hyp `IsTreeInducedAEP` (型≠結論、
  docstring で「load-bearing ergodic content, NOT a discharge / NOT regularity」明示)** として
  A2 で受け、その上に A1/A3/A4 を genuine に組む。`:True` / `:= h` 循環 / 結論同型 fake
  residual **禁止**。name laundering (`*_discharged` 等) **禁止**。撤退時も A1 (envelope
  reduction) + tree-node 集約 (per-block TRUE な `c log c ≤ -log Q_c`) は genuine 資産。
- **L-AS2 (A2 集約が組めない場合)**: tree-node の per-node `node_logsum_step` を distinct
  全体に集約する treenode-plan T3 (グルーピング不等式) が genuine に組めなければ、
  `c log c ≤ -log Q_c` (per-block) を honest named hyp 化。ただし **これは per-block TRUE**
  (path `Pₙ` でなく tree `Q_c` 相手なので disproof の対象外) なので honest hyp として正当。
- **honest 撤退の形式**: 行き詰まり時も genuine 部分 (A1 envelope、SMB 接続、tree-node 集約)
  は正直な名前で publish。撤退 hyp は `IsTreeInducedAEP` 等、結論 (`limsup ≤ H`) と一致
  しない名前 + docstring で load-bearing 明示。

## 検証

- `lake env lean InformationTheory/Shannon/<new>.lean` が silent (0 sorry / 0 warning)。
- `#print axioms isLZ78AchievabilityZivUpperBound_aseventual` (or limsup 直接版) が
  `sorryAx` 非依存。
- headline 再配線後 `#print axioms lz78_two_sided_optimality_distinct_aseventual` で残る
  honest hyp が converse `h_lb` (Core 2) + regularity `hreg` (go の場合) / + `IsTreeInducedAEP`
  (L-AS1 撤退の場合) のみであることを確認。
- 撤退 hyp がある場合、それが `Prop` (型≠結論)、`:True` でない、`:= h` 循環でないことを
  docstring + 型で確認。

## 当面の next step

**Phase M0 から着手。M0 が go/no-go gate**: (a) Route Q ステップ 3 (`Q_c` AEP
`-log Q_c/n → H`) が既存 `shannon_mcmillan_breiman` / `BirkhoffErgodic` / `AEP` から derive
可能か機械的に詰める、(b) judgment 1 (1a limsup 直接 vs 1b structure)、(c) counting 単独
(Route C) で `H` に到達不能であることの確認。M0 で `Q_c` AEP が **既存機構で組める**と
確認できれば A2 を genuine 完遂目標 (~700-1250 行)、**組めない (library-scale gap)** なら
撤退ライン L-AS1 (`IsTreeInducedAEP` honest hyp + A1 genuine) に切り替えて publish。
**per-block が偽だった以上、M0 の go 判定なしに A2 へ進まない**。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **per-block → a.s.-eventual への方針転換 (本 plan 起草の前提)**: per-block `c·log c ≤ -log Pₙ`
   (clean / overhead 両方) が `not_isLZ78ZivCombinatorialCoreOverhead` (`LZ78ZivTreeBridge.lean:130`,
   sorryAx 非依存) で機械的に FALSE 確定。`lz78-completion-plan.md` Phase Z2-Z3 と
   `lz78-ziv-treenode-plan.md` Phase T4-T5 (path-block 接続) は数学的に閉じない。本 plan は
   CT 13.5.3 original の a.s.-eventual ergodic に path を切替。treenode-plan の T1/T2/T3
   (tree-node sub-dist、per-block TRUE な部分) は genuine 資産として残し再利用候補。
2. **SMB が genuine 完成済と確認 (起草時 axiom check)**: `#print axioms shannon_mcmillan_breiman`
   = `[propext, Classical.choice, Quot.sound]`。achievability の RHS (`-log₂Pₙ/n → H`) は
   無条件 genuine。残ギャップは LHS `(c log c)/n` を RHS に繋ぐ一点に局所化。
3. **feasibility = cautious go (M0 gated)**: a.s.-eventual core は数学的に TRUE だが genuine
   証明は tree-measure `Q_c` AEP (`-log Q_c/n → H`) を要し、これは InformationTheory/Mathlib 不在の
   major ergodic gap (壁分類 (b))。counting 単独では `H` に到達不能 (定数 rate `K≠H`)。
   起草時の見立てでは L-AS1 撤退 (`IsTreeInducedAEP` honest hyp + A1 genuine) が最も確度の高い
   着地。完全無仮説 achievability は M0 が `Q_c` AEP の既存機構 derive を go と出した場合のみ。

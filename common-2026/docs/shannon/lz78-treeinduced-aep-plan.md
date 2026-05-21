# LZ78 可変depth tree-induced measure AEP — `-log₂ Q_c/n → H` genuine 構築 サブ計画 🌙

> **Parent**:
> - [`lz78-aseventual-achievability-plan.md`](./lz78-aseventual-achievability-plan.md) §「Phase A2 / Route Q ステップ 3 / 撤退ライン L-AS1」
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md) §「achievability core / 撤退ライン」
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. LZ78 漸近最適性」(Cover–Thomas Ch.13.5, Thm 13.5.3)
>
> **位置づけ**: a.s.-eventual achievability plan の Phase A2 で **honest named hyp 撤退ライン
> L-AS1 候補**だった `Q_c` AEP (`-log₂ Q_c/n → H`) を、撤退でなく **genuine 構築**する
> 専用 plan。a.s.-eventual achievability の唯一の major gap がこれ。本 plan が閉じれば
> achievability は regularity (ergodic, full-support) のみで genuine に完遂する。
>
> **Goal (短形)**: 可変depth LZ tree-induced sub-probability measure `Q_c(x^n)` を Lean に
> 定義し、その AEP **`∀ᵐ ω, -log₂ Q_c(blockRV n ω)/n → entropyRate₂`** を genuine 構築
> (Cover–Thomas Thm 13.5.3 の ergodic 核心)。これを Phase A2 の `treeProb_aep` slot に注入し、
> a.s.-eventual core `limsup (c·log₂c)/n ≤ entropyRate₂` を per-block 偽 core 非依存で閉じる。
> 標準B、0 sorry / 0 warning、`#print axioms` で sorryAx 非依存。許容仮説は regularity のみ。
>
> **proof-log: yes** (Phase Q3 の sandwich 誤差項 ω-uniform 性 + k↔n 連動接続は判断ログ +
> 別途 proof-log を残す)

## 進捗

- [ ] Phase M0 — 在庫調査 + sandwich 誤差項 ω-uniform 性の機械検算 (★ feasibility 再確認) 📋
- [ ] Phase Q1 — `Q_c` (可変depth tree-induced measure) の Lean 定義 + `∑ Q_c ≤ 1` (sub-prob) 📋
- [ ] Phase Q2 — sandwich 不等式: 固定 k `qkSingleton` で `Q_c` を上下に挟む (★ route C crux) 📋
- [ ] Phase Q3 — AEP 組立: `-log₂ Q_c/n → H` を `negLogQk_div→H_k` + `H_k→H` + sandwich で 📋
- [ ] Phase Q4 — Phase A2 への wiring: `treeProb_aep` slot 注入 + `c log c ≤ -log Q_c` 集約 📗
- [ ] Phase V — `Common2026.lean` 編入 + `lake env lean` + `#print axioms` 📋

## 現況 (本 plan の前提、起草時に機械確認)

### この gap が achievability の唯一の残り

a.s.-eventual achievability plan の feasibility は M0 gate で精査済 ([`lz78-aseventual-achievability-plan.md`](./lz78-aseventual-achievability-plan.md) 判断 1-4):

- **RHS = SMB 収束 (genuine)**: `shannon_mcmillan_breiman₂` (`LZ78ConverseKraft.lean:133`)
  = `blockLogAvg₂ → entropyRate₂` a.s.、`#print axioms` で `[propext, Classical.choice,
  Quot.sound]` のみ。無条件。
- **LHS counting / envelope / bit 展開 (genuine)**: `lz78PhraseStrings_mul_log_le`
  (`LZ78ZivCountingBody.lean:353`)、`lz78Distinct_count_div_le_envelope`
  (`LZ78ZivCombinatorics.lean:327`)、`lz78DistinctRate_le_blockLogAvg₂_add_slack`
  (`:406`)。
- **per-block `c log c ≤ -log Pₙ` は FALSE (disproof 済)**: `not_isLZ78ZivCombinatorialCoreOverhead`
  (`LZ78ZivTreeBridge.lean:130`, sorryAx 非依存)。**本 plan は path block law `Pₙ` ではなく
  tree-induced measure `Q_c` を相手にする** ので disproof の対象外 (`Q_c` 相手なら
  `c log c ≤ -log Q_c` は TRUE — disproof は `Pₙ` 限定)。
- **唯一の gap**: 可変depth `Q_c` の AEP `-log₂ Q_c/n → H`。これが本 plan。

### 再利用可能な既存資産 (SMB 内に genuine 存在、固定depth機構)

**固定 k の k-Markov product sub-measure は SMB 内に完全 genuine に存在する**。これが本 plan の
route C を成立させる決定的事実 (M0 gate が特定):

| 資産 | 場所 | conclusion form (verbatim) | genuine? |
|---|---|---|---|
| `qkSingleton` | `SMBAlgoetCover.lean:269` | `(n:ℕ) → (Fin n → α) → ℝ≥0∞`、`qkSingleton k 0 _ = 1`、`qkSingleton k (n+1) y = qkSingleton k n (Fin.init y) * markovFactor k n y` | ✅ |
| `sum_qkSingleton_le_one` | `SMBAlgoetCover.lean:278` | `∑ y : Fin n → α, qkSingleton μ p k n y ≤ 1` | ✅ |
| `negLogQk` | `SMBAlgoetCover.lean:212` | `fun ω => ∑ i ∈ range n, pmfLogCondMarkov μ p k i ω` (= `-log qkSingleton(blockRV n ω)`) | ✅ |
| `negLogQk_div_tendsto_condEntropyTail` | `SMBAlgoetCover.lean:219` | `∀ᵐ ω, Tendsto (fun n => negLogQk μ p k n ω / n) atTop (𝓝 (conditionalEntropyTail μ p k))` | ✅ (固定 k AEP) |
| `qkSingleton_blockRV_eq_ofReal_exp_negLogQk` | `SMBAlgoetCover.lean:472` | `∀ᵐ ω, qkSingleton μ p k n (p.blockRV n ω) = ENNReal.ofReal (Real.exp (-negLogQk μ p k n ω))` | ✅ (M1 bridge) |
| `conditionalEntropyTail_tendsto_entropyRate` | `EntropyRate.lean:466` (`entropyRate_eq_lim_condEntropy`) | `Tendsto (conditionalEntropyTail μ p) atTop (𝓝 (entropyRate μ p))` | ✅ (`H_k → H`) |
| `birkhoffAverage_pmfLogCondMarkov_tendsto` | `SMBAlgoetCover.lean:58` | (固定 f Birkhoff、`negLogQk_div→H_k` の土台) | ✅ |

> **決定的観察**: `negLogQk_div_tendsto_condEntropyTail` は **固定 k の tree-measure AEP を
> 既に genuine に持っている** (`-log qk/n → H_k`、Birkhoff `birkhoffAverage_pmfLogCondMarkov_tendsto`
> 経由)。可変depth `Q_c` を固定 k `qkSingleton` で sandwich し `k→∞` を `H_k→H` で取れば、
> **新規 ergodic 定理を一から組まずに済む**。これが route C を route A より優位にする核心。

### tree-node 基盤 (genuine, treenode-plan / 既存ファイル産)

- T1 worker context invariant: `lz78PhraseStringsAux_emit_context_mem` (`LZ78ZivTreeNode.lean:95`)、
  `string_eq_of_context_symbol` (`:144`)。
- T2 per-node sub-distribution: `nodeExtend_measureReal_sum_eq` (`:181`、`∑_a P(snoc v a) = P(v)`)、
  `condNode_subset_sum_le_one` (`:247`)。
- T3-inner log-sum: `node_logsum_step` (`:290`、`|S|·log|S| ≤ ∑_{a∈S} -log q(v·a|v)`)。
- per-block `c log c ≤ -log Q_c` (TRUE — `Pₙ` 相手の disproof 対象外) は T3-inner の集約として
  Phase Q4 で組む (treenode-plan T3 集約の残課題、ただし `Q_c` 相手なので honest hyp 不要)。

### 出力先 (target slot)

a.s.-eventual achievability plan の Phase A2 step 2 (`treeProb_aep`、現状 L-AS1 撤退候補):

```
-- aseventual plan A2 の honest hyp 撤退候補だったもの:
∀ᵐ ω, Tendsto (fun n => -log₂ Q_c(blockRV n ω) / n) atTop (𝓝 (entropyRate₂ μ p))
```

本 plan はこれを genuine 定理 `treeInducedProb_negLogb_div_tendsto_entropyRate₂` として publish。
aseventual plan は L-AS1 (`IsTreeInducedAEP` honest hyp) を本定理で discharge し、
A2/A3/A4 を完遂、achievability 仮定を converse + regularity のみに縮約する。

## ゴール / Approach (必須)

### Approach — route C (k-Markov sandwich) で `Q_c` AEP を固定depth機構に帰着

本質的洞察: **可変depth `Q_c` の AEP を一から組まない**。固定 k `qkSingleton` の AEP
(`-log qk/n → H_k`、既存 genuine) で `Q_c` を上下に挟み、`k → ∞` を `H_k → H`
(`conditionalEntropyTail_tendsto_entropyRate`、既存 genuine) で別途取る。`Q_c` 専用の
新規 ergodic 定理 (SMB と同規模の 2800 行構築) を回避する。

```
                  固定 k AEP (既存 genuine)             k→∞ (既存 genuine)
  -log Q_c(x^n)/n  ──sandwich──▶  -log qk(x^n)/n  ──▶  H_k  ──H_k→H──▶  H
       │                              │                  │                │
   可変depth                     固定 k                conditional       entropyRate₂
   (本 plan 定義)            (SMBAlgoetCover)         EntropyTail        (= H/log2)
```

sandwich の形 (Phase Q2 で確定する正確な不等式の候補):

```
∀ k, ∀ᵐ ω, ∀ᶠ n, qk^{(depth≥k cutoff)}(x^n) ≥ Q_c(x^n) ≥ qk^{(depth≤k truncation)}(x^n) · ε_k(n)
```

すなわち `Q_c` を「depth を k で cutoff した固定 k Markov measure」で挟む。**LZ tree の各 node
は可変 depth だが、depth ≤ k の node は固定 k Markov と一致し、depth > k の node の寄与は
ergodic stationarity で `H_k` に吸収される** (Cover–Thomas の k-th order Markov 近似)。

`-log` を取り `/n` すると:

```
-log qk^{(upper)}/n ≤ -log Q_c/n ≤ -log qk^{(lower)}/n + δ_k(n)
        │                                      │           │
   → H_k (固定 k AEP)              → H_k (固定 k AEP)    誤差項 δ_k(n)
```

両側 limit が `H_k`、誤差項 `δ_k(n)` が `n→∞` で消えれば `-log Q_c/n → H_k` ∀k、
そして `k→∞` で `H_k → H` を取ると `-log Q_c/n → H`。

### route A (diagonal) を採らない理由

aseventual plan の Route Q ステップ 3 は当初「`Q_c` を直接 k↔n 連動 (depth が n とともに増える)
diagonal/cutoff で」を route A として挙げた。**本 plan は route A を採らない**:

- route A の核心 risk = `birkhoffAverage` が **固定 f 専用**で、可変 f (depth が n とともに
  変わる) には直接効かない。これを回避する diagonal 引数 (Mathlib の
  `tendsto_of_tendsto_of_tendsto_of_le_of_le` 系 + double-limit の対角化) は **Mathlib に
  ready-made が無く**、収束の uniform 性を自前で立てる必要がある (中規模新規)。
- route C は **固定 k AEP を黒箱で再利用**し、`k → ∞` は `H_k → H` (既存) で取る。
  新規構築は「sandwich 不等式」と「誤差項 → 0」の 2 点に局所化される。
- **結論**: route C が既存資産 (`qkSingleton` / `negLogQk_div→H_k` / `H_k→H`) を最大再利用し、
  新規 ergodic content を sandwich 誤差項の一点に絞る。**route C 採用**。

### 退化ケース (H=0)

constant process (`H=0`) では `H_k = 0` ∀k、両側 sandwich も `→ 0`、`Q_c` AEP `→ 0 = H`。
per-block `c log c ≤ -log Q_c` (TRUE、`Q_c` 相手) と `/n` 後 limit `0 ≤ 0` が整合。
**vacuous でなく genuine** (両辺が実際に 0 に収束、`exfalso`/`0=値` 悪用なし)。

## 設計判断 (settle)

### 判断 1 — route A vs route C の選択 (★ 最重要)

**採用: route C (k-Markov sandwich)**。理由:

- **既存資産の再利用範囲が決定的に広い**: 固定 k AEP `negLogQk_div_tendsto_condEntropyTail`
  (`-log qk/n → H_k`)、sub-prob `sum_qkSingleton_le_one` (`∑ qk ≤ 1`)、bridge
  `qkSingleton_blockRV_eq_ofReal_exp_negLogQk` (`qk(blockRV) = exp(-negLogQk)`)、
  `H_k → H` (`entropyRate_eq_lim_condEntropy`) が **全て genuine に存在**。route C は
  これらを黒箱で組むだけ。新規 ergodic content は sandwich 誤差項のみ。
- **route A は Birkhoff 固定 f 制約に正面衝突**: 可変 f の Birkhoff は Mathlib 不在。
  diagonal で回避するにも double-limit の uniform 性を自前で立てる必要 (中規模新規、
  かつ収束 rate の制御が `Q_c` 構造依存で脆い)。
- **risk の局所化**: route C の唯一の crux = sandwich 誤差項 `δ_k(n)` が「(a) `n→∞` で
  消えるか」「(b) ω-uniform か (a.s. eventually で十分か)」。これは Phase Q2/M0 の検算対象。
  route A は「対角化が Mathlib で組めるか」という more open-ended な risk。

**未確定 (M0 で確定)**: sandwich 誤差項 `δ_k(n)` の正確な形と、それが `n→∞` で消えるか。
LZ tree の depth > k node の寄与が「ergodic stationarity で `H_k` に吸収される」を Lean shape で
書き、誤差項を明示する。消えなければ判断 2 (sandwich の片側のみで limsup/liminf 別取り) に
fallback、それも組めなければ撤退ライン L-TI1。

### 判断 2 — sandwich の片側性 (limsup / liminf 分離)

`-log Q_c/n → H` (Tendsto) を直接出すには両側 sandwich が要る。**両側が ω-uniform に
組めない場合、limsup / liminf を別々に取る**:

- **upper (limsup)**: `Q_c(x^n) ≥ qk^{(cutoff)}(x^n)` (depth k 以下に truncate すると確率が
  増える方向、tree node が浅いほど cylinder が広い) ⟹ `-log Q_c/n ≤ -log qk/n → H_k`
  ⟹ `limsup (-log Q_c/n) ≤ H_k`、`k→∞` で `limsup ≤ H`。
- **lower (liminf)**: `Q_c(x^n) ≤ qk^{(extend)}(x^n) · (誤差)` ⟹ `liminf (-log Q_c/n) ≥ H_k − o(1)`、
  `k→∞` で `liminf ≥ H`。
- 両側を合わせて squeeze → Tendsto。

**achievability に必要なのは upper (limsup) のみ** — aseventual plan の target は
`limsup (c·log₂c)/n ≤ H`。**upper だけ genuine に組めれば achievability は閉じる**
(lower は SMB 側の `-log Pₙ/n → H` が既に供給)。これが本 plan の**最小到達目標**:
`limsup (-log₂ Q_c/n) ≤ entropyRate₂` の半分だけでも Phase A2 を閉じられる可能性。
判断ログに「upper 半分 = 最小到達」を明記。

**第一候補**: upper 半分を先に閉じる (Phase Q3 で `limsup` 形を優先)。両側 Tendsto は
誤差項が両側 ω-uniform に取れた場合の bonus。

### 判断 3 — `Q_c` の Lean 定義 (`qkSingleton` 枠組みで可変 k として)

**採用**: `Q_c` を **`qkSingleton` と同じ markovFactor 積構造**で、ただし各 coordinate の
context depth を「その position までの LZ phrase boundary が決める可変 k」にする。

- `qkSingleton k n y` = `∏ markovFactor k i (init...)` で **全 coordinate が同じ k**。
- `Q_c` = LZ tree node の depth で各 factor の context window が変わる版。**T2 の
  `nodeExtend_measureReal_sum_eq` (node-context cylinder sub-dist) を factor とする積**で定義。
- **Mathlib-shape-driven**: sandwich (Phase Q2) で `qkSingleton` と比較するため、`Q_c` を
  **`qkSingleton` の積構造に寄せて**定義 (markovFactor 類似の per-coordinate factor の積)。
  textbook の「tree path に沿った node 条件付き積」は後付け equivalence で良い。
- **`LZ78ZivTreeNode.lean` の T2 (`nodeExtendCylinder` / `nodeExtend_measureReal_sum_eq`) との
  接続**: `Q_c` の各 factor を node-context 条件付き `q(v·a|v)` (= T2 の量) にすると、
  `∑ Q_c ≤ 1` が T2 の `∑_a q ≤ 1` の積として出る (`sum_qkSingleton_le_one` の証明構造を流用)。

**未確定 (Q1 で確定)**: `Q_c` の coordinate-wise factor 構造が `qkSingleton` の
`Fin.snocEquiv` 再帰と整合するか (`∑ Q_c ≤ 1` を `sum_qkSingleton_le_one` の induction で
流用できるか)。整合しなければ `Q_c` を tree path 積で定義し `∑ ≤ 1` を別途 (T2 集約) で。

### 判断 4 — AEP の組み立て (固定 k + H_k→H + sandwich)

**採用**: 3 段:

1. **固定 k**: `negLogQk_div_tendsto_condEntropyTail` (`-log qk/n → H_k`) + bridge
   `qkSingleton_blockRV_eq_ofReal_exp_negLogQk` で `qk(blockRV n ω)` の self-information を
   `negLogQk` に変換 (a.s.)。base-2 化は `/log 2` (SMB₂ と同じ手口)。
2. **sandwich**: Phase Q2 の `qk^{(upper)} ≤ Q_c` (or 両側) で `-log₂ Q_c/n` を `-log₂ qk/n`
   で挟む。誤差項 `δ_k(n)` (Q2 で明示) を `n→∞` で潰す。
3. **k→∞**: `conditionalEntropyTail_tendsto_entropyRate` で `H_k → H` (nat 単位)、`/log 2` で
   `entropyRate₂`。`∀k, limsup (-log₂ Q_c/n) ≤ H_k` と `H_k → H` (下限へ収束、antitone) から
   `limsup (-log₂ Q_c/n) ≤ inf_k H_k = H`。

base-2 整合: 全て nat (`Real.log`) で組んでから `/ Real.log 2` で `logb 2` / `entropyRate₂` に
落とす (SMB₂ と同じ。`Real.log` 版で組む方が既存補題に乗る)。

### 判断 5 — 退化ケース (H=0) の扱い

constant process は `H_k = 0` ∀k で sandwich 両側 `→ 0`。`Q_c` AEP `→ 0 = H` が genuine に
成立 (per-block `c log c ≤ -log Q_c` も `Q_c` 相手なら TRUE)。**vacuous truth で誤魔化さない**
(両辺が実際に 0 に収束)。`entropyRate₂` の `H=0` ケースで `limsup ≤ 0` が squeeze で出ることを
Phase Q3 で確認 (`H_k → 0` の antitone 収束を使う)。

## Phase 詳細 (skeleton-driven)

各 Phase は target signature + 依存補題 (file:line) + 規模見積を持つ。新規 1 ファイル
`Common2026/Shannon/LZ78TreeInducedAEP.lean` に集約 (private helper 共有のため 1 file)。

### Phase M0 — 在庫調査 + sandwich 誤差項 ω-uniform 性検算 (★ feasibility 再確認) 📋

- [ ] sandwich 誤差項 `δ_k(n)` の正確な形を Cover–Thomas Thm 13.5.3 / Lemma 13.5.4 から
      確定。LZ tree の depth > k node の寄与を固定 k Markov で抑える際の誤差を Lean shape で
      書き、「`n→∞` で消えるか」「ω-uniform か (a.s. eventually で十分か)」を 1 例
      (`block = (a,a,b,a,a)`、k=1,2) で手計算検算。
- [ ] **upper 半分 (`Q_c ≥ qk^{(cutoff)}`) の方向確認**: depth を k で truncate すると
      `Q_c` の各 factor の cylinder が広がり確率が増えるか (`-log` が減る方向)。これが
      `-log Q_c/n ≤ -log qk/n` を出す。1 例で符号確認。
- [ ] `qkSingleton_blockRV_eq_ofReal_exp_negLogQk` (`SMBAlgoetCover.lean:472`) で `Q_c` の
      self-information も同様の bridge が立つか (可変 k 版の `negLogQ_c`)。
- [ ] Mathlib: `Filter.limsup_le_of_le` / `Filter.le_limsup_of_le` (`LiminfLimsup`)、
      `tendsto_atTop_ciInf` (antitone → iInf、`EntropyRate.lean:481` で既使用)、
      `ENNReal.ofReal` / `Real.log` / `Real.logb` 変換、`Filter.Tendsto.squeeze` 系の
      conclusion form を loogle で確認 (`[...]` prerequisites verbatim、`mathlib-inventory`
      subagent に委譲可)。
- [ ] **M0 出力 = feasibility 再判定文**: (a) sandwich 誤差項が `n→∞` で消え ω-uniform なら
      Phase Q2/Q3 で genuine 完遂見込み (upper 半分は確度高)、(b) 片側のみ取れるなら upper
      半分で achievability 閉じる、(c) 誤差項が消えない / ω-uniform でないなら撤退ライン
      L-TI1。判断ログに記録。

### Phase Q1 — `Q_c` 定義 + `∑ Q_c ≤ 1` (sub-prob) 📋

- [ ] `treeInducedProb` (`Q_c`) 定義: `qkSingleton` の markovFactor 積構造に寄せ、各 factor を
      node-context 条件付き (T2 `nodeExtend_measureReal_sum_eq` の量) にする。
      target: `noncomputable def treeInducedProb (μ p) : (n:ℕ) → (Fin n → α) → ℝ≥0∞`。
      依存: `qkSingleton` (`SMBAlgoetCover.lean:269`)、`nodeExtendCylinder`
      (`LZ78ZivTreeNode.lean:170`)。規模: **~60-100 行**。
- [ ] `sum_treeInducedProb_le_one`: `∑ y, treeInducedProb n y ≤ 1`。
      `sum_qkSingleton_le_one` (`SMBAlgoetCover.lean:278`) の induction + `Fin.snocEquiv`
      reindex 構造を流用、各 node の `∑_a q ≤ 1` は `condNode_subset_sum_le_one`
      (`LZ78ZivTreeNode.lean:247`)。規模: **~80-120 行**。
- [ ] `negLogTreeInducedProb` (= `-log Q_c(blockRV n ω)`) 定義 + bridge
      `treeInducedProb_blockRV_eq_ofReal_exp` (`qkSingleton_blockRV_eq_ofReal_exp_negLogQk`
      `:472` の可変 k 版)。規模: **~60-100 行**。

### Phase Q2 — sandwich 不等式 (★ route C crux) 📋

> **着手条件**: M0 で誤差項が `n→∞` で消える (少なくとも upper 側) と判定された場合。

- [ ] `treeInducedProb_ge_qkSingleton_cutoff` (upper 半分の核心): `∀ k, ∀ n, ∀ y,
      qkSingleton k n y · (cutoff factor) ≤ treeInducedProb n y` (or 逆向き、M0 の符号確認次第)。
      depth ≤ k truncation の cylinder inclusion から。依存: T2 cylinder monotonicity、
      `nodeExtend_measureReal_sum_eq` (`:181`)。規模: **~120-200 行** (★ crux、誤差項顕在化時)。
- [ ] `negLogTreeInduced_le_negLogQk_add_err`: `-log Q_c(blockRV n ω)/n ≤ negLogQk k n ω/n
      + δ_k(n)/n`、`δ_k(n)/n → 0`。bridge (Q1) で `Q_c`/`qk` の self-information に変換。
      規模: **~80-120 行**。
- [ ] (両側 Tendsto 狙う場合) lower 半分 `negLogTreeInduced_ge_negLogQk_sub_err`。
      規模: **~80-120 行 (両側時のみ)**。

### Phase Q3 — AEP 組立 `-log₂ Q_c/n → H` (or limsup ≤ H) 📋

- [ ] `negLogbTreeInduced_div_limsup_le_condEntropyTail₂`: `∀ k, ∀ᵐ ω,
      limsup (-log₂ Q_c(blockRV n ω)/n) ≤ conditionalEntropyTail₂ μ p k`。
      Q2 sandwich (upper) + `negLogQk_div_tendsto_condEntropyTail` (`:219`、`/log 2` で base-2)
      + 誤差項 `→0`。`Filter.limsup_le_of_le`。規模: **~100-150 行**。
- [ ] `condEntropyTail₂_tendsto_entropyRate₂`: `conditionalEntropyTail₂ μ p k → entropyRate₂`
      (`entropyRate_eq_lim_condEntropy` `:466` の `/log 2`)。規模: **~30 行**。
- [ ] `treeInducedProb_negLogb_div_limsup_le_entropyRate₂` (★ 主定理 / 最小到達):
      `∀ᵐ ω, limsup (-log₂ Q_c(blockRV n ω)/n) ≤ entropyRate₂ μ p`。
      `∀k, limsup ≤ H_k` + `H_k → H` (antitone, `tendsto_atTop_ciInf`) → `limsup ≤ inf H_k = H`。
      規模: **~80-120 行**。
- [ ] (両側 Tendsto 狙う場合) `treeInducedProb_negLogb_div_tendsto_entropyRate₂` (Tendsto 形)。
      lower 半分 + squeeze。規模: **~80 行 (両側時のみ)**。

### Phase Q4 — Phase A2 への wiring 📗

> **目的**: aseventual plan Phase A2 の `treeProb_aep` slot に本 plan の主定理を注入。
> **このセクションは aseventual plan 側の Phase A2/A3 と協調** (本 plan は主定理 publish まで)。

- [ ] `count_mul_logb_le_negLogb_treeInduced` (per-block `c log₂c ≤ -log₂ Q_c`、TRUE):
      tree-node T3-inner `node_logsum_step` (`LZ78ZivTreeNode.lean:290`) を distinct phrase
      全体に集約。`Q_c` 相手なので disproof 対象外 (path `Pₙ` の罠を回避)。
      依存: `node_logsum_step` (`:290`)、`string_eq_of_context_symbol` (`:144`)、
      `lz78PhraseStrings_nodup`。規模: **~150-250 行** (treenode-plan T3 集約の残課題)。
- [ ] aseventual plan A2 の `aseventual_countLogRate_limsup_le` への接続:
      Q3 主定理 + Q4 per-block + A1 envelope reduction で `limsup (lz/n) ≤ entropyRate₂`。
      **本 step は aseventual plan 側で完結** (本 plan は主定理を提供)。

### Phase V — 編入 + 検証 📋

- [ ] `Common2026.lean` に `import Common2026.Shannon.LZ78TreeInducedAEP` 追記。
- [ ] `lake env lean Common2026/Shannon/LZ78TreeInducedAEP.lean` silent (0 sorry / 0 warning)。
- [ ] `#print axioms treeInducedProb_negLogb_div_limsup_le_entropyRate₂` (主定理) で sorryAx
      非依存確認。残る honest hyp が regularity (`hreg`: full-support cylinder 正値、ergodic)
      のみであることを確認。

## 規模見積 + feasibility 判定 (最重要)

| Phase | 中央 (upper 半分) | 両側 Tendsto | 出力 | リスク |
|---|---|---|---|---|
| M0 | 0 行 (調査) | — | 誤差項形 + feasibility 再判定 | ★★ feasibility gate |
| Q1 | 200-320 行 | 同 | `Q_c` 定義 + `∑ ≤ 1` + bridge | 中 (`qkSingleton` 構造流用) |
| Q2 | 200-320 行 | +160-240 行 | sandwich 不等式 | ★★★ route C crux (誤差項) |
| Q3 | 210-390 行 | +160 行 | AEP (`limsup ≤ H` or Tendsto) | 中 (固定 k + H_k→H 黒箱) |
| Q4 | 150-250 行 | 同 | per-block 集約 + wiring | ★ T3 集約 (treenode 残課題) |
| V | 5 行 | 同 | import + 検証 | 低 |
| **累計 (upper 半分)** | **~765-1280 行** | (+320-400 行 両側) | 1 新規ファイル | — |

> Q4 の per-block 集約 (~150-250 行) は aseventual plan が A2 で別途扱う場合は本 plan から
> 外せる (主定理 Q3 のみで ~615-1030 行)。本 plan の核心は **Q1-Q3 (`Q_c` AEP genuine 構築)**。

**feasibility 判定 (route C が genuine に閉じる見込み)**:

- **固定depth機構は完全 genuine に存在** (`qkSingleton` / `sum_qkSingleton_le_one` /
  `negLogQk_div_tendsto_condEntropyTail` / `qkSingleton_blockRV_eq_ofReal_exp_negLogQk` /
  `H_k→H`)。route C はこれらを黒箱で組む。**aseventual plan 起草時の「`Q_c` AEP は SMB と
  独立な新規 ergodic 定理で直接組めない見込みが高い」という悲観的見立ては、固定 k AEP が
  既に存在する事実で緩和される** — 一から組むのではなく sandwich で帰着できる。
- **唯一の crux = sandwich 誤差項 `δ_k(n)`** (Phase Q2)。「`n→∞` で消え ω-uniform か」が
  go/no-go。**LZ tree の depth > k node の寄与を固定 k Markov で抑える誤差は、stationary
  ergodic では `o(n)` (CT Thm 13.5.3 の核心評価) で、`/n → 0` が期待される**が、ω-uniform
  性 (a.s. eventually で足りるか) は M0 検算対象。
- **upper 半分 (`limsup ≤ H`) が最小到達で achievability を閉じる**: lower は SMB が供給済。
  upper 半分なら sandwich は片側のみ (`Q_c ≥ qk^{(cutoff)}`) で済み、誤差項 risk が半減。
- **結論 = cautious go (M0 gated, route C)**: route C は固定depth機構を最大再利用し、新規
  ergodic content を sandwich 誤差項一点に局所化する。**aseventual plan の L-AS1 撤退より
  確度高く genuine 完遂が見込める道**。go/no-go は M0 の誤差項検算に懸かる。
  - **誤差項が消え ω-uniform (少なくとも upper 側) なら go** (~615-1030 行、Q2/Q3 が主)。
  - **upper 片側のみ取れるなら go (achievability は upper で閉じる)**。
  - **誤差項が消えない / ω-uniform でないなら no-go** → 撤退ライン L-TI1 (honest hyp、ただし
    本 plan は Q1 の `Q_c` 定義 + `∑ ≤ 1` を genuine 資産として publish)。

**起草時の見立て (aseventual plan からの更新)**: aseventual plan は「`Q_c` AEP = SMB 同規模の
別構築になりうる、L-AS1 撤退が最も確度の高い着地」と見立てた。**本 plan は固定 k AEP が
既存 genuine である事実を起点に route C を採り、その見立てを「sandwich 誤差項が制御できれば
genuine 完遂可能」に更新する**。crux は SMB の再構築ではなく、可変depth `Q_c` を固定 k で
挟む sandwich 誤差項 `δ_k(n)/n → 0` の ω-uniform 評価 (CT Thm 13.5.3 の k-th order Markov
近似誤差)。これが M0 で制御可能と確認できれば、本 plan は aseventual achievability を完全
無仮説 (regularity のみ) に閉じる。

## 撤退ライン (honest 限定)

標準B。`Q_c` AEP を genuine に (型≠結論、`:= h` 循環/`:True`/退化定義悪用 禁止)。
per-block 偽 core (`IsLZ78ZivCombinatorialCore` / `Overhead`) には依存しない (disproof 済、
本 plan は `Q_c` 相手なので対象外)。許容仮説は regularity (`hreg`: full-support cylinder
正値、ergodic) のみ。

- **L-TI1 (主要撤退、確度中)**: M0 で sandwich 誤差項 `δ_k(n)/n` が `n→∞` で消えない、または
  ω-uniform に取れない (a.s. eventually で足りない) と判定した場合、`Q_c` AEP
  (`limsup (-log₂ Q_c/n) ≤ H`) を **honest named hyp `IsTreeInducedAEP` (型≠結論、docstring
  で「load-bearing ergodic content (CT Thm 13.5.3 k-th order Markov 近似誤差)、NOT a discharge
  / NOT regularity」明示)** として publish。**これは aseventual plan L-AS1 と同一 slot** — 撤退
  時も本 plan は Q1 (`Q_c` 定義 + `sum_treeInducedProb_le_one` sub-prob) + Q2 部分 (片側
  sandwich の組めた範囲) を genuine 資産として残す。`:True` / `:= h` 循環 / name laundering
  (`*_discharged`) 禁止。
- **L-TI2 (両側が組めず upper のみの場合)**: 両側 Tendsto が誤差項の片側 ω-uniform 不成立で
  組めなければ、**upper 半分 `limsup (-log₂ Q_c/n) ≤ H` のみ genuine に publish** (これで
  achievability は閉じる、lower は SMB 供給)。これは撤退でなく **設計判断 2 の予定された
  最小到達** — honest hyp 不要。
- **L-TI3 (Q4 集約が組めない場合)**: per-block `c log₂c ≤ -log₂ Q_c` (treenode T3 集約) が
  組めなければ Q4 を aseventual plan A2 側に委ね、本 plan は Q1-Q3 (`Q_c` AEP) のみ publish。
  per-block 集約は `Q_c` 相手なので TRUE (disproof 対象外)、honest hyp 化も正当だが、本 plan
  scope からは外して aseventual plan に戻すのが clean。
- **honest 撤退の形式**: 行き詰まり時も genuine 部分 (`Q_c` 定義、`∑ ≤ 1`、固定 k AEP 接続、
  組めた sandwich 片側) は正直な名前で publish。撤退 hyp は `IsTreeInducedAEP` 等、結論
  (`limsup ≤ H`) と一致しない名前 + docstring で load-bearing 明示。

## 検証

- `lake env lean Common2026/Shannon/LZ78TreeInducedAEP.lean` が silent (0 sorry / 0 warning)。
- `#print axioms treeInducedProb_negLogb_div_limsup_le_entropyRate₂` (主定理、upper 半分) が
  `sorryAx` 非依存。両側 Tendsto 版を組んだ場合は
  `#print axioms treeInducedProb_negLogb_div_tendsto_entropyRate₂` も。
- aseventual plan A2 への wiring 後、`#print axioms isLZ78AchievabilityZivUpperBound_aseventual`
  で残る honest hyp が converse `h_lb` (Core 2) + regularity `hreg` のみであることを確認
  (L-AS1 honest hyp が本 plan の主定理で discharge されたことの確認)。
- **library-scale build**: 本 plan は ~500-900 行の major ergodic build。最終 1 回
  `lake build Common2026.Shannon.LZ78TreeInducedAEP` で olean 整合確認 (per-fill は
  `lake env lean`)。
- 撤退 hyp (L-TI1) がある場合、それが `Prop` (型≠結論)、`:True` でない、`:= h` 循環でない、
  退化定義悪用でないことを docstring + 型で確認。

## 当面の next step

**Phase M0 から着手。M0 が feasibility gate**: (a) sandwich 誤差項 `δ_k(n)` の正確な形と
`n→∞` で消えるか + ω-uniform 性を 1 例 (`(a,a,b,a,a)`, k=1,2) で手計算検算、(b) upper 半分
(`Q_c ≥ qk^{(cutoff)}`) の符号確認、(c) `Q_c` の self-information bridge が `qkSingleton`
bridge (`:472`) の可変 k 版として立つか。M0 で誤差項が制御可能 (少なくとも upper 側) と
確認できれば Q1 (`Q_c` 定義) → Q2 (sandwich) → Q3 (AEP) を genuine 完遂目標
(~615-1030 行)、制御不能なら撤退ライン L-TI1 (`IsTreeInducedAEP` honest hyp + Q1 genuine)。
**固定 k AEP が既存 genuine である以上、route C は SMB 再構築を回避できる — go の確度は
aseventual plan 起草時の悲観的見立てより高い。**

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **route C 採用 (本 plan 起草の核心判断)**: aseventual plan は Route Q ステップ 3
   (`-log Q_c/n → H`) を「SMB と独立な新規 ergodic 定理、L-AS1 撤退が最も確度の高い着地」と
   見立てた。本 plan 起草時に SMBAlgoetCover を精読し、**固定 k の k-Markov AEP が既に genuine に
   存在する**ことを確認 (`negLogQk_div_tendsto_condEntropyTail` `:219` = `-log qk/n → H_k`、
   `qkSingleton` `:269` = sub-prob measure、`sum_qkSingleton_le_one` `:278`、bridge
   `qkSingleton_blockRV_eq_ofReal_exp_negLogQk` `:472`)。これと `H_k → H`
   (`entropyRate_eq_lim_condEntropy` `:466`) を使えば、`Q_c` を固定 k で sandwich して
   `k→∞` を取る route C で **SMB 再構築を回避できる**。route A (diagonal) は Birkhoff 固定 f
   制約に正面衝突し Mathlib 不在の対角化が要るため不採用。**route C 採用、feasibility 見立てを
   「sandwich 誤差項が制御できれば genuine 完遂可能」に更新**。
2. **upper 半分 = 最小到達 (設計判断 2)**: achievability の target は `limsup (c·log₂c)/n ≤ H`
   なので、`Q_c` AEP も **upper 半分 `limsup (-log₂ Q_c/n) ≤ H` だけで achievability を閉じる**
   (lower は SMB `-log Pₙ/n → H` が供給)。upper 半分なら sandwich は片側 (`Q_c ≥ qk^{(cutoff)}`)
   のみで誤差項 risk が半減。両側 Tendsto は誤差項両側 ω-uniform が取れた場合の bonus。
3. **crux の局所化**: route C の唯一の go/no-go = sandwich 誤差項 `δ_k(n)/n → 0` の ω-uniform
   評価 (CT Thm 13.5.3 の k-th order Markov 近似誤差)。SMB 再構築ではなく可変depth→固定 k の
   近似誤差一点に絞られた。M0 でこれを 1 例検算し go/no-go を出す。L-TI1 撤退でも `Q_c` 定義 +
   `∑ ≤ 1` (Q1) は genuine 資産、aseventual plan L-AS1 と同一 slot に honest hyp として残す。

# Wyner–Ziv: Markov-core (conditional-AEP) 実装サブ計画

> **Parent**: [`wz-binning-covering-plan.md`](wz-binning-covering-plan.md) §Leg F

## Context

WZ achievability chain 唯一の genuine hard residual = `wz_covering_jointBand_markov_core`
(`InformationTheory/Shannon/WynerZiv/Achievability.lean` L5246、位置は `scripts/sig_view.ts --sorry`
で都度確認)。C2 covering-acceptance の outer lemma `wz_covering_jointBand_concentration` (L5302) は
既に proved (`_markov_core` を consume、L5462)、この core だけが isolated sorry。core = 選ばれた
covering word `U = c.decoder (c.encoder x-block)` (= x-block 全体の deterministic 関数) と相関 side-info
`Y` が jointly `(U,Y)`-atypical になる事象の SRC-measure 上界。**class `plan`、NOT a Mathlib wall**
(独立 honesty audit 2026-07-12 PASS、tier-2)。難所は `(U_i, Y_i)` が iid でも独立でもないため plain
`aep_chebyshev_bound` (IdentDistrib 前提) が効かない点 = conditional AEP (Markov lemma U—X—Y)。

## 進捗

- [ ] M0 API 確認 (大半は本 plan `wz-facts.md` に記録済、残 = Chebyshev tail lemma + conditional product-measure 構成) 📋
- [ ] Atom C — mean-identity (WARM-UP) 📋
- [ ] Atom A — finite Fubini split (disintegration 回避) 📋
- [ ] Atom B — conditional Chebyshev (bulk) 📋
- [ ] Atom D — core 組立 (`wz_covering_jointBand_markov_core` body) 📋

## ゴール / Approach

### Goal

`wz_covering_jointBand_markov_core` を genuine sorry-free 化し、親 §Leg F の C2 chain を閉じる。
署名は不変 (3 hyps `hκ'_pos`/`hκ'_sum`/`hqStar` 固定、bundling 禁止)。撤退口は
`sorry + @residual(plan:wz-binning-covering)` のみ。

### Approach — 3-piece 分解 + finite-vs-general disintegration の解決

core の自然な証明 = conditional AEP (Markov lemma)。x-block を固定すると `U = c.decoder(c.encoder x)`
は決定的、`y_i ~ P(·|x_i)` は条件付き独立。3 piece に分解する:

- **(a) SRC の x-block disintegration**: SRC = `Measure.pi (fun _ ↦ pmfToMeasure Src)`、Src = pair 法則
  `P_XY.real{(·,·)}`。x-block 固定で `u` 決定的・`y_i` 条件付き独立化。
- **(b) conditional Chebyshev**: 固定 x-block 上で `−(1/n)∑ log wsm(u_i,y_i)` を条件付き平均へ集中
  (`wsm = wzSideInfoMarginal P_XY κ'`)。
- **(c) mean-identity (deterministic)**: 条件付き平均 = `H(wsm)`。covering-success ((x,u) 型 ≈ qStar)
  + (x,y)-typicality で pin。

**finite-vs-general disintegration の解決 (最重要、親 §Leg F の stale 主張を訂正)**:

親 Leg F の「disintegration bridge は回避可 (SRC は既に iid joint-pair `Measure.pi`)」は **結論は正しい**
が理由が未記載だった。実装者が見つけた「`condDistrib` + `Measure.pi` = Found 0」は **general machinery
を探した結果で正しいが off-path** — 両者は矛盾しない。正しい理由:

- `Src(x,y) = P_XY.real{(x,y)} = P_X(x)·P(y|x)` は **有限 pmf の分解** (elementary 有限算術)。
- `pmfToMeasure` は atomic (`= ∑ a, ENNReal.ofReal (p a) • dirac a`、ShannonTheorem.lean:55)、ゆえ
  `(Measure.pi (fun _ ↦ pmfToMeasure Src)).real {block-event} = ∑_{block∈event} ∏_i Src(block i)` =
  **有限和**。各 factor で `Src = P_X·P(y|x)` を割り、x-block を外に factor する reindex は `Measure.pi_pi`
  (in-tree で多用: BlockwiseChannel/MemorylessCapacity, ParallelGaussian/PerCoord 他) + `pmfToMeasure_apply_singleton`
  + `Fintype.sum_prod_type` の **有限 Fubini** で済む。**general `condDistrib` on `Measure.pi` (0-hit の壁) は不要**。

∴ piece (a) は「from-scratch measure theory (general disintegration)」でなく **elementary 有限 Fubini** に collapse。
真の bulk は piece (b) の conditional Chebyshev。ここも `IndepFun.variance_sum` (AEP/Rate.lean:149、**IdentDistrib
不要**、pairwise 独立 + MemLp のみ) が非-ident 独立和の分散分解を供給するため、`aep_chebyshev_bound`
(IdentDistrib 前提で drop-in 不可) を経由せず self-build で組める。全体 effort が「multi-session from-scratch」
から「既存部品の focused 組立 (few sessions)」に下がる。

## Phase 詳細

各 atom は Achievability.lean 内の新規 `private lemma` (署名は core と同じ 3 hyps を必要分だけ threading)。
`open ChannelCoding in` scope 内。conclusion 形は下の Mathlib 出口形に合わせる (「Mathlib-shape-driven」)。

### M0 — API 確認 (proof-log: no)

大半は `wz-facts.md` に記録済。残の open item のみ確認:
- [ ] Chebyshev tail の Mathlib lemma 名 (`ProbabilityTheory.meas_ge_le_variance_div_sq` 系) の verbatim 署名。
- [ ] 固定 x-block 上の conditional product measure `Measure.pi (fun i ↦ pmfToMeasure (fun y ↦ P(y|x_i)))`
      の構成と、`IndepFun.variance_sum` を乗せる際の各 summand `y ↦ −log wsm(u_i,y)` の MemLp/可測性。

### Atom C — mean-identity (WARM-UP、proof-log: no)

- [ ] `wz_wsm_negLog_condMean_eq_entropy` (仮): 決定的恒等式
  `∑_{x,u} P_X(x)·κ'(u|x)·(∑_y P(y|x)·(−log wsm(u,y))) = ∑_{u,y} wsm(u,y)·(−log wsm(u,y))`。
  `wsm(u,y) = ∑_x κ'(x,u)·P_XY(x,y)` (`wzSideInfoMarginal` def L943) + `P_X(x)·κ'(u|x)·P(y|x) = κ'(x,u)·P_XY(x,y)`
  (`hqStar`/`hκ'_sum`) の代入 + `Fintype.sum_prod_type`/`Finset.sum_comm` の reindex。
- **conclusion 形**: 有限 `Finset.sum` 等式 (`_ = _`)。standalone provable、pmf 上の Fubini/reindex のみ。
- **tractability**: easy。**最初の target** (残 2 atom の mean を供給、独立)。

### Atom A — finite Fubini split (proof-log: yes、disintegration 回避が durable)

- [ ] `wz_srcBlock_condMeasure_split` (仮): block event `S ⊆ (Fin n → α'×β)` に対し
  `(Measure.pi (fun _ ↦ pmfToMeasure Src)).real S = ∑_{xb : Fin n → α'} (∏_i P_X(xb_i)) ·
   (Measure.pi (fun i ↦ pmfToMeasure (fun y ↦ P(y|xb_i)))).real (S の xb-slice)`。
  `Measure.pi_pi` + `pmfToMeasure_apply_singleton` (atomic) + 各 coord の `(x,y)` を `x` 外・`y` 内に割る
  `Fintype.sum_prod_type`。
- **conclusion 形**: 実数等式 (SRC-mass = x-block 和 × 条件付き y-block mass)。`Measure.pi_pi` 出口形に整合。
- **tractability**: med (有限 bookkeeping)。**general condDistrib を使わない** ことが本 atom の要点 (durable)。

### Atom B — conditional Chebyshev (bulk、proof-log: yes)

- [ ] `wz_condBlock_negLog_wsm_concentration` (仮): cover-success + (x,y)-typical な固定 xb に対し
  `(Measure.pi (fun i ↦ pmfToMeasure (fun y ↦ P(y|xb_i)))).real {yb | (u,y)-block atypical} ≤ (small tol')`
  が `n ≥ N` で uniform。summand `y ↦ −log wsm(u_i,y)` は `y_i` のみの関数 ⟹ 条件付き product measure 下で
  **独立 (非-ident)** ⟹ `IndepFun.variance_sum` (IdentDistrib 不要) で分散分解 → Chebyshev tail。条件付き平均は
  Atom C + covering-success/(x,y)-typicality で `H(wsm)` に pin (deviation を ε 内に)。`typicalSet` 定義
  (`|(∑ pmfLog)/n − H| < ε`、AEP/Basic/Core.lean:214) の empirical-band 形に直接乗る。
- **conclusion 形**: 実数不等式 `condY.real{atypical} ≤ V/(n·δ²)` 系 (`aep_chebyshev_bound` L108 の出口形に相当、ただし
  per-coord 変動する分散/平均)。
- **tractability**: med-large (~100-200 行)、本 build の genuine bulk。`hκ'_pos`/`hκ'_sum`/`hqStar` threading 必須。

### Atom D — core 組立 (proof-log: no)

- [ ] `wz_covering_jointBand_markov_core` body: Atom A で SRC-mass を xb 和に還元 → cover-success ∩ (x,y)-typical
  の xb だけが寄与 → 各 slice を Atom B で `≤ tol'` → `∑_{xb} P_X-block(xb) ≤ 1` で `≤ tol/8`。
- **tractability**: easy (~40 行)。

**依存順**: C (独立) → A (独立) → B (C を要) → D (A+B を要)。C と A は順不同、B は C 後、D は最後。
署名変更なし (core の 3 hyps 固定、新規は全て private lemma 追加) ⟹ 既存 shared lemma の ripple 無し
(`dep_consumers` 不要)。

**撤退**: 各 atom で詰まったら `sorry + @residual(plan:wz-binning-covering)`。covering-acceptance / conditional
concentration を `*Hypothesis` predicate に bundle するのは禁止 (tier-5)。

## Cross-family 再利用の判断 (実装者の気づきへの回答)

Markov-lemma パターン (決定的 word `u=f(x-block)`、相関 side-info `y`、atypical joint 集合の UPPER
concentration) は relay-CF / broadcast で再出しうる。**推奨 = WZ-internal で先に build (default、低結合)**:

- 現 target は WZ 固有 def (`wzSideInfoMarginal`/`rdAmbient qStar`/α' subtype) に密結合。1 つも working instance が
  無い段階で shared sorry-lemma primitive に abstract すると、これらの一般化コストが先行して結合度を上げる。
- audit-tags.md「Proposed wall」register の promote-trigger (2+ family 参照 or closure-plan 整合) に従い、
  **WZ instance を proved 化した後**、relay-CF が具体的に必要とした時点で shared 化 (候補 name 例
  `markov-lemma-conditional-aep`) を再判定する。今 over-engineer しない。

## 判断ログ

1. **finite-vs-general disintegration = finite Fubini で解決 (active、durable)**: piece (a) は general
   `condDistrib` on `Measure.pi` (0-hit) を要さず、`pmfToMeasure` atomicity + `Measure.pi_pi` + `Fintype.sum_prod_type`
   の有限 Fubini で x-block を factor できる。実装者の condDistrib 0-hit は general machinery を探した正しい結果だが
   off-path。真の bulk は piece (b) conditional Chebyshev (`IndepFun.variance_sum`、IdentDistrib 不要)。→ 詳細 Approach、
   settled は `wz-facts.md`。

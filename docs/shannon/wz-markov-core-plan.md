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

- [ ] M0 API 確認 — 大半 `wz-facts.md` 済 (finite-Fubini + `IndepFun.variance_sum`)、conditional product-measure 構成は Atom A で確定 (condY)。残 = Chebyshev tail lemma verbatim (Atom B 用) 📋
- [x] Atom C — mean-identity (WARM-UP)、sorry-free (`ef34494a`) ✅
- [x] Atom A — finite Fubini split (disintegration 回避)、sorry-free (`95a07fa4`) ✅
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

大半は `wz-facts.md` に記録済。conditional product measure `condY(xb)` の構成は Atom A で確定
(正規化 division 形、各 factor は proper pmf、helper `wz_pmfToMeasure_isFiniteMeasure` L5274)。残の open item:
- [ ] Chebyshev tail の Mathlib lemma 名 (`ProbabilityTheory.meas_ge_le_variance_div_sq` 系) の verbatim 署名。
- [ ] `IndepFun.variance_sum` を乗せる際の各 summand `y ↦ −log wsm(u_i,y)` の MemLp/可測性 (Atom B 内)。

### Atom C — mean-identity (WARM-UP、proof-log: no) — [x] done `ef34494a`

**shipped は 2 lemma**:
- `wz_wsm_negLog_mean_eq_entropy` (L5216): **division-FREE workhorse**、`Atom B/D の primary`。
- `wz_wsm_negLog_condMean_eq_entropy` (L5241): division 形、workhorse から derive。

- 決定的恒等式 `∑_{x,u} P_X(x)·κ'(u|x)·(∑_y P(y|x)·(−log wsm(u,y))) = ∑_p Real.negMulLog (wsm p)`
  (`wsm = wzSideInfoMarginal P_XY κ'`)。代入 `P_X·κ'(u|x)·P(y|x) = κ'(x,u)·P_XY(x,y)` (`hqStar`/`hκ'_sum`) + reindex。
- **landed 出口形** = `∑ p, Real.negMulLog (wzSideInfoMarginal P_XY κ' p)` = `wz_entropy_ambient_joint`
  (L3317、`= entropy (rdAmbient wsm) (jointSequence iidXs iidYs 0)`) の **EXACT RHS** ⟹ Atom D は Atom C →
  (reverse) `wz_entropy_ambient_joint` を typicalSet band center に直結、**bridge lemma 不要**。`pmfLog` は署名不一致で不使用。

### Atom A — finite Fubini split (proof-log: yes、disintegration 回避が durable) — [x] done `95a07fa4`

**PINNED interface** (verbatim、Atom B/D はこれに整合させる):
- `wz_srcBlock_condMeasure_split` (L5346): `S : Set (Fin n → α'×β)` に対し **equality** (両方向再利用可)
  `SRC.real S = ∑_{xb:(Fin n→α')} (∏_i ∑_y P_XY.real{((xb i).1, y)}) · condY(xb).real {yb | (fun i ↦ (xb i, yb i)) ∈ S}`。
- `condY(xb) := Measure.pi (fun i ↦ pmfToMeasure (fun y : β ↦ P_XY.real{((xb i).1, y)} / ∑_{y'} P_XY.real{((xb i).1, y')}))`
  — **正規化 division 形**、各 factor は genuine PROBABILITY measure (proper pmf、`(xb i).2 : 0 < P_X`)、
  **y-alphabet = FULL β** (subtype ではない)。Atom B の `IndepFun.variance_sum`/Chebyshev が要求する形。
- 上流に自作 sorry-free `private` helper 2 本: `wz_pmfToMeasure_isFiniteMeasure` (L5274)、
  `wz_pi_pmf_real_eq_sum` (L5292、real singleton-sum を `measure_biUnion_finset`+`Measure.pi_pi`+`pmfToMeasure_apply_singleton` で)。
- **要点 (durable)**: **general condDistrib を使わない** finite-Fubini。

### Atom B — conditional Chebyshev (bulk、proof-log: yes)

- [ ] `wz_condBlock_negLog_wsm_concentration` (仮): cover-success + (x,y)-typical な固定 xb に対し
  `condY(xb).real {yb | (u,y)-block atypical} ≤ (small tol')` が `n ≥ N` で uniform。summand
  `y ↦ −log wsm(u_i,y)` は `y_i` のみの関数 ⟹ condY (product measure) 下で **独立 (非-ident)** ⟹
  `IndepFun.variance_sum` (IdentDistrib 不要) で分散分解 → Chebyshev tail。条件付き平均は Atom C
  (workhorse `wz_wsm_negLog_mean_eq_entropy`) + covering-success/(x,y)-typicality で `H(wsm)` に pin。`typicalSet` 定義
  (`|(∑ pmfLog)/n − H| < ε`、AEP/Basic/Core.lean:214) の empirical-band 形に直接乗る。
- **subtype↔full-β 整合 callout (必須)**: condY は **FULL β** 上、wsm の y-index は subtype
  `{y // 0 < ∑_x' P_XY{(x',y)}}` (core は subtype→β キャストを iidYs site ~L5266-5270 で行う)。
  subtype 外の `y` は `∑_x' P_XY{(x',y)}=0 ⟹ P_XY{(x,y)}=0 ⟹` condY mass 0 ⟹ tail が consistent に消える。
  B は core の subtype-indexed empirical `(u,y)`-entropy を full-β condY に対して bridge する。
- **conclusion 形**: 実数不等式 `condY.real{atypical} ≤ V/(n·δ²)` 系 (`aep_chebyshev_bound` L108 出口形相当、
  ただし per-coord 変動する分散/平均)。
- **tractability**: med-large (~100-200 行)、本 build の genuine bulk。`hκ'_pos`/`hκ'_sum`/`hqStar` threading 必須。

### Atom D — core 組立 (proof-log: no)

- [ ] `wz_covering_jointBand_markov_core` body、**assembly recipe**:
  - Atom A で `SRC.real(triple-∩)` を `∑_{xb} (∏_i P_X(xb_i)) · condY(xb).real(slice)` に還元。
  - **good xb** (cover-success ∧ (x,y)-typical) → Atom B で `condY(xb).real(slice) ≤ tol'`。
  - **bad xb** → condY `≤ 1` で bound、D は `∑_{xb} ∏_i P_X(xb_i) = (∑_{x:α'} P_X x)^n = 1` (degenerate x は drop)
    のみ使い全体を `≤ tol/8`。
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
2. **危惧された disintegration 壁は CLOSED sorry-free (Atom A `95a07fa4`)**: finite-Fubini 解決 (判断 1) を実装で確認、
   `wz_srcBlock_condMeasure_split` (L5346) が genuine。残 bulk は Atom B (conditional Chebyshev) 単独。
   低優先 TODO: `wz_pi_pmf_real_eq_sum` は `private` `measure_pi_eq_sum_singletons` (ShannonTheoremGeneral.lean:410) を
   再導出しており、後で shared lemma 昇格の候補。

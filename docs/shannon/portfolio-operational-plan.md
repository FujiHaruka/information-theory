# Portfolio: operational / universal theorems サブ計画

> **Parent**: [`portfolio-moonshot-plan.md`](portfolio-moonshot-plan.md) — Ch.16 静的核 (concavity / KT / competitive) の operational 拡張

Cover–Thomas *Elements of Information Theory* 2nd ed **Ch.16 "Information Theory and Investment"** のうち、
親計画で **operational / universal 定理として scope-out** されていた 4 群を proof-done (0 sorry / 0 @residual /
sorryAx-free / 独立 `@audit:ok`) まで持っていく。静的核 (`growthRate` / `wealthRelative` / KT 4 定理、
`Portfolio/Basic.lean`) は proof-done 済で、本計画は **すべて consume のみ** (既存共有補題の署名変更ゼロ、
ripple 無し → `dep_consumers.sh` 不要)。

## 進捗

- [ ] M0 在庫 — 群 A–D の Mathlib / in-project 資産を verbatim 署名で確定 📋
- [ ] Leg A — AO-iid (operational 漸近最適性、CT §16.3 Thm 16.3.1) 📋 **gateway atom 第一候補**
- [ ] Leg C — side-info & growth rate (`ΔW ≤ I(X;Y)`、CT §16.4 Thm 16.4.1) 📋
- [ ] Leg B — stationary market (定常エルゴード成長率収束、CT §16.5 Thm 16.5.1) 📋
- [ ] Leg D — Cover universal portfolio (regret bound、CT §16.7) 📋 **最リスク・別 gateway で早期壁判定**

## Context

親 `portfolio-moonshot-plan.md` は Ch.16 の **解析核 3 中核 (4 定理)** を proof-done 済:
`growthRate_concaveOn` (16.2.2) / `logOptimal_of_kuhnTucker` / `kuhnTucker_of_logOptimal` (16.2.1 双方向) /
`competitive_optimality` (one-shot `E[S_b/S_bs] ≤ 1`)。これらは **静的 (1 期間、pmf ベース)**。

本計画が拾うのは **時間列 / universal 側** — CT §16.3 (iid 列の漸近最適性)・§16.4 (副情報)・§16.5 (定常市場)・
§16.7 (universal portfolio)。gambling (Ch.6) の operational 版 (`Gambling/OperationalSequences.lean` /
`SideInformation.lean`、全 proof-done) の **非対角一般化** = 本計画の骨格テンプレ。

**⚠️ CT 節番号ラベルの是正 (実状に合わせよ)**: 親計画・roadmap・`Basic.lean` docstring は
`competitive_optimality` を **"16.3.1"** とラベルしているが、CT 2nd ed の実節番号では competitive optimality は
**§16.6 (Thm 16.6.1)**、§16.3 は本計画 Leg A の **asymptotic optimality (iid)** である。本子計画の
Leg ラベルは **CT 実節番号** に合わせる (A=§16.3 / C=§16.4 / B=§16.5 / D=§16.7)。親の 16.3.1 誤ラベルは
**別途 orchestrator が親 docstring / roadmap を是正** (本計画の書込対象外)。

## ゴール / Approach

**ゴール** — 静的 `α` `[Fintype α]` (アウトカム)、`m : ℕ` (株数)、price-relative `X : α → (Fin m → ℝ)`、
portfolio `b ∈ stdSimplex ℝ (Fin m)` を基盤に、時間列 `As : ℕ → Ω → α` (iid / 定常) 上の operational 定理と、
universal portfolio の regret bound を headline とする。

**Approach — gambling → portfolio の分岐点を operational 側でどう扱うか**。gambling (対角
`X a i = o i · [a=i]`) は gap が per-term に log 分離し **KL 還元** (Gibbs) で閉じた。portfolio の一般 (非対角)
X では `log(∑ i b_i X_{a,i})` が per-term 分離せず KL 還元は効かない — 静的側はこれを **凹性 + 有限 Jensen**
ルートで閉じた (親 Approach)。**operational 側では、この分岐点は既に静的核が吸収済** という観測が本計画の要:

- **Leg A (iid)** の operational core は **SLLN のみ** (`strong_law_ae_real`)。極限の同定
  `E[log(b·X_0)] = growthRate p X b` は静的 `growthRate` の定義参照であり、**凹性 / KL とは無関係**。
  gambling `seqLogWealth_div_tendsto_doublingRate` の `betLogReturn → portfolioLogReturn` /
  `doublingRate → growthRate` 置換の **1:1 clone**。分岐点 (対角 vs 非対角) は極限値 `growthRate` の中に
  封じ込まれ、SLLN 骨格には現れない ⟹ **gambling と同じく壁は想定されない**。
- **Leg A dominance** (`W(b) ≤ W(bs)`) は静的 `logOptimal_of_kuhnTucker` (IsMaxOn) を **consume** して得る
  決定的不等式。非対角の困難は静的 KT 定理が既に処理済。
- **Leg C (side info)** が **唯一 gambling と証明ルートが分岐する** — gambling は Kelly 賭けの
  per-term cancellation で **等号** `ΔW = I(X;Y)` を得たが、portfolio では log-optimal ≠ 比例のため
  **不等号** `ΔW ≤ I(X;Y)` になり、KT + KL 上界を要する (per-term cancellation が効かない)。
- **Leg B (定常)** は SLLN を **Birkhoff エルゴード定理** (`birkhoff_ergodic_ae`) に差し替えた Leg A。
  fixed-b 収束は tractable、log-optimal `W_∞` の AEP (CT 16.5.1 完全形) は SMB 級で重い。
- **Leg D (universal)** は operational 列ではなく **単体上の多変量積分** — gambling にミラー無し。
  Mathlib に simplex 上の測度も Dirichlet 積分も**不在** (M0 probe 確認) ⟹ 最リスク・壁公算大。

**着手順 (mirror 確実な順、D 最後)**: **A (gateway) → C → B → D**。A の SLLN core が通れば scope-out の壁
over-estimation が反証され、C/B は A の operational テンプレ + 静的核の再利用。D は独立 gateway atom で
早期に壁判定し、壁なら analytic core を `sorry` + `@residual(wall:simplex-dirichlet-integral)` で分離する。

**署名変更 ripple 無し**: 全 Leg は `Portfolio/Basic.lean` の 4 定理 + `growthRate` / `wealthRelative` を
consume のみ (署名不変)。新規 def / 定理の追加のみで、既存共有補題の hypothesis threading は無い。

## ファイル配置 (gambling ディレクトリ構造 mirror)

`InformationTheory/Shannon/Portfolio/` 配下に新規 4 ファイル。root `InformationTheory.lean` に各 import 追記
(各 Leg の skeleton phase で先行登録):

| Leg | file | mirror 元 |
|---|---|---|
| A | `Portfolio/OperationalSequences.lean` | `Gambling/OperationalSequences.lean` |
| C | `Portfolio/SideInformation.lean` | `Gambling/SideInformation.lean` |
| B | `Portfolio/StationaryMarket.lean` | `SMB/ChainRule.lean` の Birkhoff 適用テンプレ |
| D | `Portfolio/Universal.lean` | (mirror 無し — 新規解析) |

各ファイルは `variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] {m : ℕ}` +
`{Ω : Type*} [MeasurableSpace Ω]` (静的 Basic は `{α} [Fintype α] {m}` のみ、operational は Ω / 可測性を追加)。

## Leg A — AO-iid (operational 漸近最適性、CT §16.3 Thm 16.3.1) — gateway atom

**gambling `seqLogWealth_div_tendsto_doublingRate` の 1:1 clone**。iid 列 `As : ℕ → Ω → α` の各期に
固定 rebalance portfolio b を適用した log-wealth の時間平均が a.s. で成長率 `growthRate (lawPmf μ (As 0)) X b`
に収束する。**gateway atom = SLLN core**: これが通れば scope-out が壁 over-estimation だったと実機確認。

### def / statement (proof-log: yes — SLLN 組立 + 極限同定は記録に値する)

```lean
-- alphabet-side per-period log return  g(a) = log(S_b(a)) = log(∑ i, b i · X a i)
noncomputable def portfolioLogReturn (X : α → Fin m → ℝ) (b : Fin m → ℝ) : α → ℝ :=
  fun a ↦ Real.log (wealthRelative X b a)

-- log-wealth after n periods:  log S_n = ∑_{i<n} log(S_b(As i ω))
noncomputable def seqLogWealth (X : α → Fin m → ℝ) (b : Fin m → ℝ) (As : ℕ → Ω → α) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range n, portfolioLogReturn X b (As i ω)

-- headline (§16.3): (1/n)·log S_n → W(b) = growthRate p X b  a.s.  (p = law of As 0)
@[entry_point]
theorem seqLogWealth_div_tendsto_growthRate
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : α → Fin m → ℝ) (b : Fin m → ℝ)
    (As : ℕ → Ω → α) (hAs : ∀ i, Measurable (As i))
    (hindep : Pairwise fun i j ↦ As i ⟂ᵢ[μ] As j)
    (hident : ∀ i, IdentDistrib (As i) (As 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ seqLogWealth X b As n ω / n) atTop
      (𝓝 (growthRate (lawPmf μ (As 0)) X b))
```

`portfolioLogReturn X b a = log (wealthRelative X b a)`、`growthRate p X b = ∑ a, p a · portfolioLogReturn X b a`
ゆえ `E[portfolioLogReturn X b (As 0)] = growthRate (lawPmf μ (As 0)) X b`。gambling の `betLogReturn` /
`doublingRate` を置換しただけで **極限同定が gambling と同型**。headline は **positivity 不要** (`Real.log 0 = 0`
規約で全域定義、gambling headline と同性質)。

### dominance corollary (任意 causal portfolio に対する漸近支配)

```lean
@[entry_point]
theorem seqLogWealth_asymptotically_optimal
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : α → Fin m → ℝ) (b bs : Fin m → ℝ)
    (hb : b ∈ stdSimplex ℝ (Fin m)) (hbs : bs ∈ stdSimplex ℝ (Fin m))
    (hpos : ∀ a, ∀ c ∈ stdSimplex ℝ (Fin m), 0 < wealthRelative X c a)
    (As : ℕ → Ω → α) (hAs : ∀ i, Measurable (As i))
    (hindep : Pairwise fun i j ↦ As i ⟂ᵢ[μ] As j)
    (hident : ∀ i, IdentDistrib (As i) (As 0) μ μ)
    (hKT : ∀ i, (∑ a, lawPmf μ (As 0) a * X a i / wealthRelative X bs a) ≤ 1) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ seqLogWealth X b As n ω / n) atTop (𝓝 (growthRate (lawPmf μ (As 0)) X b)) ∧
      Tendsto (fun n ↦ seqLogWealth X bs As n ω / n) atTop (𝓝 (growthRate (lawPmf μ (As 0)) X bs)) ∧
      growthRate (lawPmf μ (As 0)) X b ≤ growthRate (lawPmf μ (As 0)) X bs
```

決定的不等式 `W(b) ≤ W(bs)` は `logOptimal_of_kuhnTucker (lawPmf μ (As 0)) X bs hp hbs hpos hKT` (`hp` は
`lawPmf_mem_stdSimplex` で内部導出) の `IsMaxOn` に `hb` を適用して得る。**`hKT` は bs が log-optimal で
あることの具体的・検証可能な KT 条件 (regularity/定義的、gambling の `doublingRate_le_proportional` に相当) で
あり load-bearing bundling ではない** (正直性メモ参照)。`limsup (1/n) log(S_n/S_bs_n) ≤ 0` は 2 収束 + 差分の
系として即従う (実装で `∀ᵐ` 内 `Tendsto.sub` から `limsup` 形も付記可)。

### 再利用資産 (verbatim は M0 で確定)

- **静的 (Portfolio/Basic.lean、consume のみ)**: `wealthRelative` / `growthRate` / `logOptimal_of_kuhnTucker`
  (`Basic.lean:154`、KT ⟹ IsMaxOn) / `lawPmf_mem_stdSimplex` 相当。
- **generic 再利用 (Gambling/OperationalSequences.lean、import して consume)**: `lawPmf` (`:68`) /
  `lawPmf_mem_stdSimplex` (`:109`) / `integral_comp_law` (`:76`、`∫ ω, g (X ω) = ∑ x, (μ.map X).real{x}·g x`)。
  この 3 本は **generic** (賭け非依存) で portfolio から直接 consume 可。
- **clone (gambling → portfolio、`portfolioLogReturn` に置換)**: `measurable_betLogReturn` /
  `integrable_betLogReturn_zero` / `identDistrib_betLogReturn` / `indepFun_betLogReturn` (`:71`–`:108`) の 4 本。
- **Mathlib**: `strong_law_ae_real` (`StrongLaw.lean:598`、極限 `μ[X 0]`)。

### phases

- [ ] A0 (proof-log: no): `strong_law_ae_real` + gambling `integral_comp_law` / `lawPmf` / plumbing 4 本 +
      静的 `logOptimal_of_kuhnTucker` の verbatim 署名を再 Read。
- [ ] A1 skeleton (proof-log: no): def 2 本 (`portfolioLogReturn` / `seqLogWealth`) + plumbing 4 clone +
      headline + dominance を `:= by sorry`、root import 登録、type-check done。
      **gateway 判定**: skeleton が型検査を通り極限 `growthRate (lawPmf μ (As 0)) X b` が def に乗ることを確認。
- [ ] A2 (proof-log: yes): headline を `strong_law_ae_real` + `integral_comp_law` で組む (gambling Phase 4 clone)。
      極限同定 `E[portfolioLogReturn] = growthRate` を記録。
- [ ] A3 (proof-log: no): plumbing 4 clone + dominance corollary (`logOptimal_of_kuhnTucker` consume)。
- [ ] A4: 配線 (root は A1 済 / README / roadmap) + 独立 honesty 監査 (hKT が regularity である旨も検査)。

**DoD**: headline + dominance が proof-done (sorryAx-free `[propext, Classical.choice, Quot.sound]`)、
`@[entry_point]` + `@audit:ok`。**壁リスク: ~ゼロ** (gambling が同 machinery で proof-done、mirror 確実)。

## Leg C — side-info & growth rate (`ΔW ≤ I(X;Y)`、CT §16.4 Thm 16.4.1)

gambling `Gambling/SideInformation.lean` の非対角ミラー。**唯一 gambling と証明ルートが分岐** — gambling は
`ΔW = I(X;Y)` (等号)、portfolio は **`ΔW ≤ I(X;Y)` (不等号)** で per-term cancellation が効かず KT + KL 上界を要す。

### def / statement (proof-log: yes — 不等号ルートは gambling 等号と別機構、記録に値する)

pmf ベース (gambling ミラー): `pY : γ → ℝ` (副情報の法)、`pXgivenY : γ → α → ℝ` (条件付き法)。

```lean
-- conditional growth rate with side info: 各 y で条件付き portfolio b(y) を使う成長率
noncomputable def condGrowthRate
    (X : α → Fin m → ℝ) (b : γ → Fin m → ℝ) (pY : γ → ℝ) (pXgivenY : γ → α → ℝ) : ℝ :=
  ∑ y, pY y * growthRate (pXgivenY y) X (b y)

-- pmf-based mutual info  I(X;Y) = H(X) + H(Y) − H(X,Y)  (gambling sideInfoMutualInfo を α×γ で再利用)
-- (Gambling.SideInformation.sideInfoMutualInfo を import 再利用、または Portfolio 名前空間で再定義)

-- headline (§16.4): 副情報による成長率増分は相互情報量で上から抑えられる (不等号)
@[entry_point]
theorem sideInfo_growthRate_increment_le_mutualInfo
    (X : α → Fin m → ℝ) (bs : Fin m → ℝ) (bcond : γ → Fin m → ℝ)
    (pY : γ → ℝ) (pXgivenY : γ → α → ℝ)
    (hpY : pY ∈ stdSimplex ℝ γ) (hcond : ∀ y, pXgivenY y ∈ stdSimplex ℝ α)
    (hpos : ∀ a, ∀ c ∈ stdSimplex ℝ (Fin m), 0 < wealthRelative X c a)
    -- bs は無条件 KT、bcond y は各 y の条件付き KT (log-optimal の具体的特徴付け = regularity)
    (hKT : ∀ i, (∑ a, sideMarginalX pY pXgivenY a * X a i / wealthRelative X bs a) ≤ 1)
    (hKTcond : ∀ y, ∀ i, (∑ a, pXgivenY y a * X a i / wealthRelative X (bcond y) a) ≤ 1) :
    condGrowthRate X bcond pY pXgivenY - growthRate (sideMarginalX pY pXgivenY) X bs
      ≤ sideInfoMutualInfo pY pXgivenY
```

**証明ルート (gambling 等号 → portfolio 不等号)**: `ΔW = ∑_y pY_y · W*(X|Y=y) − W*(X)` を、無条件/条件付き
KT portfolio (`bs` / `bcond`) の成長率で表現。KT 条件下で各項を KL 差に落とし
`ΔW ≤ D(pXgivenY(·|y) · pY ‖ sideMarginalX · pY) = I(X;Y)` を **Gibbs 非負性の逆向き上界** で得る。
`klDivPmf` / `klDivPmf_nonneg` (`CsiszarProjection`) を再利用。gambling の per-term log cancellation
(`sideInfo_logOdds_cancel`) は **効かない** — 非対角では log-optimal が比例でないため。

### 再利用資産

- **静的**: `growthRate` / `wealthRelative` / `logOptimal_of_kuhnTucker` (KT ⟹ 各 W* が max)。
- **gambling (SideInformation.lean、consume/再定義)**: `sideMarginalX` (`:44`) / `sideInfoJoint` (`:49`) /
  `sideInfoMutualInfo` (`:66`、`H(X)+H(Y)−H(X,Y)`) / `sideInfoJointEntropy_eq_chain` (`:126`、chain rule)。
- **KL**: `klDivPmf` / `klDivPmf_nonneg` (`Gambling.Basic` open 済の `CsiszarProjection` 由来)。

### phases

- [ ] C0 (proof-log: no): gambling SideInformation の `sideMarginalX`/`sideInfoMutualInfo`/chain rule と
      静的 `logOptimal_of_kuhnTucker`、`klDivPmf_nonneg` の verbatim 署名を確定。**honesty guard**: 増分の
      粒度 (`condGrowthRate − growthRate`) と KL 上界の向きを実機で確認 (coarse/fine ミスマッチ・向き逆転を排除)。
- [ ] C1 skeleton: `condGrowthRate` def + headline `:= by sorry`、root import 登録、type-check done。
- [ ] C2 (proof-log: yes): ΔW を KT portfolio の成長率差で展開 → KL 差に還元 → `klDivPmf_nonneg` の逆向き
      上界で `≤ sideInfoMutualInfo`。等号 (gambling) と不等号 (portfolio) の分岐を記録。
- [ ] C3: 配線 + 独立 honesty 監査 (hKT/hKTcond が regularity、check 4 sufficiency = 不等号が仮説から follow)。

**DoD**: headline proof-done + `@audit:ok`。**壁リスク: 中** — statement mirror は素直だが不等号ルートが
gambling 等号と別機構 (KT + KL 上界)。KL 上界の向き / 条件付き KT portfolio の扱いで詰まる可能性。

## Leg B — stationary market (定常エルゴード成長率収束、CT §16.5 Thm 16.5.1)

SLLN を **Birkhoff エルゴード定理** に差し替えた Leg A。定常エルゴードシフト `T : Ω → Ω` + 第一観測
`X : Ω → (Fin m → ℝ)` に対し、固定 portfolio b の log-wealth 時間平均が a.s. で `E[log(b·X)]` に収束。

### statement (proof-log: yes — Birkhoff 適用 + 正規化規約の確認は記録に値する)

```lean
-- gateway/headline (§16.5、fixed-b): 定常エルゴード市場での成長率収束
@[entry_point]
theorem seqLogWealth_div_tendsto_stationary
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    (X : Ω → (Fin m → ℝ)) (b : Fin m → ℝ)
    (hint : Integrable (fun ω ↦ Real.log (∑ j, b j * X ω j)) μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n ↦ (∑ i ∈ Finset.range n, Real.log (∑ j, b j * X (T^[i] ω) j)) / n) atTop
      (𝓝 (∫ ω, Real.log (∑ j, b j * X ω j) ∂μ))
```

`f ω = Real.log (∑ j, b j * X ω j)` に `birkhoff_ergodic_ae hT hT_erg hint` を適用するだけ
(`birkhoffAverage_pmfLogCond_tendsto`, `SMB/ChainRule.lean:355` の 1:1 テンプレ)。**正規化規約に注意**:
`birkhoffAverageReal` の分母が `/n` か `/(n+1)`・和域が `range n` か `range (n+1)` かは M0 で verbatim 確認
(`BirkhoffErgodic.lean` docstring は `lnAverageReal` を `/(n+1)` と記す — 上の statement は実 def に合わせる)。

### 完全形 CT 16.5.1 (W_∞ AEP) — 高リスク拡張

CT 16.5.1 の完全形は **log-optimal `W_∞`** (無限過去条件付き成長率の増加極限 `W*(X_0 | X_{-1..−k}) ↑ W_∞`) +
AEP `(1/n) log S*_n → W_∞`。これは条件付き log-optimal portfolio の列 + 単調収束 + SMB 級論法を要し、
`shannon_mcmillan_breiman` (`SMB/AlgoetCover/Liminf.lean:497`) をテンプレとするが **fixed-b 収束より格段に重い**。

### 再利用資産

- **Mathlib/in-project**: `birkhoff_ergodic_ae` (`BirkhoffErgodic.lean:1000`、`MeasurePreserving`+`Ergodic`+
  `Integrable` ⟹ 時間平均 → `∫ f`) / `birkhoffAverageReal` def。
- **テンプレ**: `birkhoffAverage_pmfLogCond_tendsto` (`SMB/ChainRule.lean:355`、`birkhoff_ergodic_ae` を
  `pmfLogCond` に適用する 1:1 パターン)。完全形は `shannon_mcmillan_breiman` (`Liminf.lean:497`)。

### phases

- [ ] B0 (proof-log: no): `birkhoff_ergodic_ae` verbatim 署名 + `birkhoffAverageReal` の正規化規約 (`/n` vs
      `/(n+1)`) を確認。`birkhoffAverage_pmfLogCond_tendsto` を Read しテンプレ確定。
- [ ] B1 skeleton + B2 fixed-b headline (proof-log: yes): `birkhoff_ergodic_ae` を `f = log(b·X)` に適用。
- [ ] B3 (完全形、optional / 高リスク): W_∞ AEP。詰まったら **retreat** (下記)。
- [ ] B4: 配線 + 独立 honesty 監査。

**DoD**: fixed-b headline proof-done + `@audit:ok` (**壁リスク: 低**、Birkhoff 在庫)。W_∞ AEP 完全形は
**壁リスク: 中〜高** — 条件付き log-optimal + 単調収束 + SMB。

## Leg D — Cover universal portfolio (regret bound、CT §16.7) — 最リスク

`Ŝ_n(x^n) = ∫_Δ ∏_{i<n} S_b(x_i) dμ(b)` (Dirichlet/一様加重) が `(1/n) log(Ŝ_n / S*_n) → 0` を達成する
regret bound。**operational 列ではなく単体上の多変量積分** — gambling にミラー無し。

### M0 probe 結果 (2026-07-19、機械確認) — 壁公算の根拠

- **`stdSimplex` 上の測度は Mathlib MeasureTheory に不在** (`rg stdSimplex .lake/…/Mathlib/MeasureTheory/`
  = 0 file)。単体上の一様測度 / Lebesgue 制限が無い。
- **Dirichlet 分布 / 多変量 Dirichlet 積分は Mathlib Probability に不在** (`rg Dirichlet` = 0)。
  `∫_Δ ∏ b_i^{k_i} db = (∏ k_i!)/((∑k_i)+m−1)!` 型の閉形式が無い。
- **在るのは 1 次元 Beta/Gamma のみ**: `Real.betaIntegral` / `Real.Gamma` (loogle で識別子確認)。多変量への
  昇格 (Fubini + 帰納) は self-build。

⟹ **多変量単体積分は genuine Mathlib gap の公算大**。`@residual(wall:simplex-dirichlet-integral)` を
新規 wall name 候補として想定 (M0 gateway で確定後、`docs/audit/audit-tags.md` の register に追記)。

### gateway atom (D の壁を早期確定)

**D 本体着手前に単独 dispatch**: 「`stdSimplex ℝ (Fin m)` 上に一様測度を定義し、単項式
`∫_Δ ∏ b_i^{k_i}` を 1 つ評価する」atom を lean-implementer に投げ、**通るか / 壁かを実機判定**。
- **通れば** (Mathlib に simplex measure がある or 軽い self-build で足りる): D 本体を Leg として続行。
- **壁なら** (simplex measure が無く self-build が重い): analytic core を `sorry` +
  `@residual(wall:simplex-dirichlet-integral)` で分離し、regret bound の **組合せ骨格** (Ŝ_n ≥ S*_n / poly)
  だけを積分核を仮定した補題の consumer として組む。**hypothesis bundling は禁止** — 積分核を `*Hypothesis`
  predicate に抱えさせず、`sorry` を積分評価補題の body に置く (audit-tags.md「shared Mathlib wall」形)。

### phases

- [ ] D0 gateway atom (proof-log: yes): simplex 一様測度 + 単項式積分 1 本を probe。**壁 / not-wall を確定**
      (loogle 0-hit だけで壁宣言しない — 2 段階 conclusion-shape 検索 + template lemma の自作行数見積、
      CLAUDE.md「壁を宣言するとき」)。
- [ ] D1 (gateway=not-wall の場合): `universalWealth` def + regret bound headline を skeleton → 実装。
- [ ] D1' (gateway=wall の場合): analytic core を `sorry` + `@residual(wall:simplex-dirichlet-integral)`、
      組合せ骨格を積分核補題の consumer として組む。wall name を register に追記。
- [ ] D2: 配線 + 独立 honesty 監査 (retreat 時は `sorry` の class 正当性 = 積分核が genuine gap である旨)。

**DoD**: regret bound proof-done (gateway=not-wall) or 組合せ骨格 proof-done + analytic core が honest な
`sorry` + `@residual(wall:…)` (gateway=wall)。**壁リスク: 高** (M0 probe が simplex measure 不在を確認済)。

## gateway-atom 方針 (集約)

- **Leg A = 主 gateway**: SLLN core (`seqLogWealth_div_tendsto_growthRate` の骨格) をまず単独で通し、
  scope-out が壁 over-estimation だったことを実機確認 (公算大で通る、gambling が同 machinery で proof-done)。
- **Leg D = 独立 gateway**: simplex 一様測度 + 単項式積分 1 本を D 本体前に probe し、壁 / not-wall を早期判定。
  壁なら analytic core だけを分離し組合せ骨格は救う。
- **gateway-atom-first の効用**: A が通れば C/B のテンプレ確度が上がり、D の壁が早期に分離されるため、
  A→C→B で 3 群 genuine closure を確保しつつ D のリスクを局所化できる。

## 正直性メモ (regularity precondition の性質)

全 Leg の追加仮説は **regularity precondition**、load-bearing hypothesis bundling ではない:

- **iid / 定常 / 可測性** (`hAs` / `hindep` / `hident` / `MeasurePreserving` / `Ergodic` / `Integrable`):
  列の統計的構造 + SLLN/Birkhoff の必須前提。命題の核 (収束) を encode せず、gambling operational と同性質。
- **`hpos : 0 < wealthRelative X c a`** (Leg A dominance / C): `Real.log` の凹性定義域 `Ioi 0` 由来の
  correctness precondition (静的 P3 と同性質、`log 0 = 0` 規約)。
- **`hKT` / `hKTcond`** (Leg A dominance / C): **bs / bcond が log-optimal であることの具体的・検証可能な
  KT 条件** (`∀ i, ∑ … ≤ 1`)。これは **どの portfolio が log-optimal かを pin する定義的特徴付け** であり、
  証明の核 (収束 / 増分不等式) を仮説に抱えさせる bundling ではない。gambling が
  `doublingRate_le_proportional` (proven theorem) を consume するのと同型で、静的
  `logOptimal_of_kuhnTucker` (KT ⟹ IsMaxOn、proof-done) を経由して決定的不等式を **内部導出** する。
  ⟹ honesty gate 通過の前提 (check 2 非バンドル / check 4 sufficiency = 収束/不等式が仮説から semantic follow)。
- **`lawPmf μ (As 0)` 束縛** (Leg A): `As 0` の法 (law) という **定義そのもの** の参照。gambling headline が
  極限を `doublingRate b o (lawPmf μ (Xs 0))` と書くのと同型、genuine 定義的束縛。

**撤退時 retreat exit は `sorry` のみ**。極限値 / 増分 / 積分核を仮説で渡す (`(h : … = growthRate …) → …`)
形の load-bearing bundling は **禁止**。

## 撤退ライン (Leg 別)

在庫が壁ゼロを確認済の A は発動リスク ~ゼロ。B 完全形・C 不等号・D 積分核は非ゼロ。

- **Leg A**: SLLN core が想定外に詰まった場合、当該補題 (bridge / 極限同定) の signature を target 形のまま
  body を `sorry` + `@residual(plan:portfolio-operational-plan)`。想定壁無しゆえ `wall:` は使わない。
- **Leg C**: 不等号ルート (KT + KL 上界) が詰まった場合、headline signature を保ち body を `sorry` +
  `@residual(plan:portfolio-operational-plan)`。**gambling 等号版で代用する誘惑を排す** (portfolio は不等号が
  正しく、等号は false-as-framed)。
- **Leg B**: W_∞ AEP 完全形が SMB 級で重い場合、fixed-b headline のみで着地し、完全形を後続
  `portfolio-stationary-woo-plan.md` に分離 (`@residual(plan:portfolio-stationary-woo-plan)`、slug 整合)。
- **Leg D**: gateway=wall 確定時、analytic core (単体積分 / Dirichlet) を `sorry` +
  `@residual(wall:simplex-dirichlet-integral)`、組合せ骨格は救う。積分核を `*Hypothesis` に抱えさせる形は
  **禁止** — `sorry` は積分評価補題の body に置く。

## DoD / gate

- **各 phase**: type-check done (`lake env lean` 0 error、`sorry` は `@residual` 付き) で commit/push 可。
  proof-done (0 sorry ∧ 0 @residual、file 内) が genuine 完成。
- **headline `@[entry_point]`**: 各 Leg headline を `@[entry_point]`、proof-done + 独立 `honesty-auditor`
  PASS で `@audit:ok`。
- **honesty gate**: 新規 `sorry` + `@residual` 導入 commit (Leg B/C/D の retreat 時) / dominance の `hKT` が
  regularity である旨は独立 `honesty-auditor` 必須。
- **style gate**: 新規 file の decl/docstring 追加 (全 Leg) で `style-auditor` を touched file に適用。

## 完了時の配線

- **root**: 各 Leg の skeleton phase で `import InformationTheory.Shannon.Portfolio.<file>` を先行登録。
- **README**: `docs/readme-theorems.txt` の Ch.16 節に各 Leg headline を追記 → `gen_readme_table.ts --write`
  (marker 内は手編集しない)。
- **roadmap**: `docs/textbook-roadmap.md` Ch.16 行に operational/universal 復帰を追記 (gambling §6.3 の mirror)。
  **併せて親の "16.3.1" 誤ラベルを 16.6.1 (competitive) に是正** (orchestrator が親 docstring / roadmap を修正)。
- **facts**: `docs/shannon/portfolio-facts.md` に headline の sorryAx-free 再検証コマンド + D の壁 slug (壁確定時)
  を追記。
- **parent 同期**: 本子計画の状態変化時は親 `portfolio-moonshot-plan.md` に sub-plan テーブル行を追加 +
  DAG を同期 (子が SoT、衝突時は親を子に合わせる)。**本計画作成時点で親に未登録** → orchestrator が追加要。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)、active のみ残す。

1. **CT 節ラベル是正 (active)**: 親 / roadmap / `Basic.lean` は `competitive_optimality` を "16.3.1" と誤ラベル
   だが CT 実節では competitive = §16.6 (Thm 16.6.1)、§16.3 = 本計画 Leg A (AO-iid)。本子計画は CT 実節に合わせ
   (A=16.3 / C=16.4 / B=16.5 / D=16.7)、親側是正は orchestrator に委任。
2. **`lawPmf` / `integral_comp_law` は gambling から import 再利用 (active)**: この 3 本 (`lawPmf` /
   `lawPmf_mem_stdSimplex` / `integral_comp_law`) は generic (賭け非依存) ゆえ `Gambling.OperationalSequences`
   を import して consume。Portfolio→Gambling 依存が生じるが cycle 無し (gambling は portfolio を import せず)。
   import weight が重ければ 3 本を Portfolio 側に再 clone (各 ~15 行) に切替可 — A1 実装で判断。
3. **Leg C は不等号、gambling 等号を代用しない (active)**: portfolio の log-optimal ≠ 比例ゆえ
   `ΔW ≤ I(X;Y)` が正しく、gambling 等号 `= I(X;Y)` は false-as-framed。C2 の KL 上界の向きを C0 honesty guard
   で実機確認 (coarse/fine ミスマッチ + 向き逆転を排除)。
4. **Leg D 壁公算 (active)**: M0 probe が `stdSimplex` 測度 / Dirichlet 積分の Mathlib 不在を機械確認済
   (1 次元 Beta/Gamma のみ在)。D0 gateway atom で壁 / not-wall を確定してから本体着手 (loogle 0-hit だけで
   壁宣言せず、conclusion-shape 検索 + 自作行数見積を経由)。壁確定時のみ `wall:simplex-dirichlet-integral` を
   register に追記。

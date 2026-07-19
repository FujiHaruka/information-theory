# Portfolio: operational / universal theorems サブ計画

> **Parent**: [`portfolio-moonshot-plan.md`](portfolio-moonshot-plan.md) — Ch.16 静的核 (concavity / KT / competitive) の operational 拡張

Cover–Thomas *Elements of Information Theory* 2nd ed **Ch.16 "Information Theory and Investment"** のうち、
親計画で **operational / universal 定理として scope-out** されていた 4 群を形式化する。静的核
(`growthRate` / `wealthRelative` / KT 4 定理、`Portfolio/Basic.lean`) を **consume のみ** (既存共有補題の署名変更
ゼロ、ripple 無し) で組み立てる方針。**Leg A/C/D は proof-done、Leg B は fixed-b core を proof-done + W_∞ AEP
完全形を後継計画へ deferral。**

## 進捗 — ✅ core DONE (2026-07-19)

- [x] M0 在庫 — 群 A–D の Mathlib / in-project 資産を verbatim 署名で確定
- [x] Leg A — AO-iid (operational 漸近最適性、CT §16.3 Thm 16.3.1) — proof-done sorryAx-free + @audit:ok
- [x] Leg C — side-info & growth rate (`ΔW ≤ I(X;Y)`、CT §16.4 Thm 16.4.1) — proof-done + @audit:ok（署名 honesty 修正）
- [x] Leg B — stationary market fixed-b (定常エルゴード成長率収束 + dominance、CT §16.5) — proof-done + @audit:ok
- [ ] Leg B 完全形 — W_∞ AEP (CT 16.5.1 完全形) — **🚧 R1 proof-done + R2 core proof-done (selection残)、R3/R4 残** → [`portfolio-stationary-woo-plan.md`](portfolio-stationary-woo-plan.md)
- [x] Leg D — Cover universal portfolio (regret bound、CT §16.7) — proof-done sorryAx-free + @audit:ok（**not-a-wall 判明**）

## Closure summary

全 4 Leg の headline は proof-done (0 sorry / 0 @residual / sorryAx-free / 独立 `honesty-auditor` PASS で
`@audit:ok`)。gambling operational (`Gambling/OperationalSequences.lean` / `SideInformation.lean`) の
**非対角一般化** をテンプレとし、静的核が gambling→portfolio の分岐点 (対角 vs 非対角) を既に吸収済という観測で
壁 over-estimation を実機反証した。

| Leg | file / headline | commit | 実装ノート |
|---|---|---|---|
| A | `Portfolio/OperationalSequences.lean`：`seqLogWealth_div_tendsto_growthRate` + `seqLogWealth_asymptotically_optimal` | `af215336` / gates `7f1f65b9` | SLLN core (`strong_law_ae_real`) の 1:1 clone。分岐点は極限値 `growthRate` に封じ込まれ SLLN 骨格に現れず、想定どおり壁ゼロ。dominance は静的 `logOptimal_of_kuhnTucker` (IsMaxOn) を consume |
| C | `Portfolio/SideInformation.lean`：`sideInfo_growthRate_increment_le_mutualInfo` | `7b126592` / gates `f5c13a5d` | ΔW ≤ I(X;Y) の **不等号**ルート (gambling 等号と別機構)。KT + Gibbs 上界 (`gibbs_core` 自作、`Real.log` 凸性経由)。**署名を honesty 修正** (下記) |
| B (core) | `Portfolio/StationaryMarket.lean`：`seqLogWealth_div_tendsto_stationary` + `stationaryLogReturn_integral_le_of_kuhnTucker` | `b977af36` / gates `eafaa121` | fixed-b 収束は `birkhoff_ergodic_ae` の 1:1 適用 (`birkhoffAverage_pmfLogCond_tendsto` テンプレ、正規化 `/(n+1)`・和域 `range (n+1)`)。**dominance は新規 measure-theoretic 証明** — 有限アルファベット `logOptimal_of_kuhnTucker` は general-measure 市場に効かず、`Real.log_le_sub_one_of_pos` 経由の積分版 KT dominance を自作 |
| D | `Portfolio/Universal.lean`：`universal_portfolio_regret_tendsto_zero` | `b4a2928e` / `2d32959f` / gates `187d0f82` | Cover universal portfolio (CT 16.7 regret bound)。プラン想定の wall 候補名 `simplex-dirichlet-integral` は **not-a-wall** と判明 (下記) |

## Leg C — 署名 honesty 修正 (実コード = SoT)

`7b126592` で当初 skeleton 署名を修正し着地。**実装済の正しい署名** (`SideInformation.lean:145`):

```lean
theorem sideInfo_growthRate_increment_le_mutualInfo
    (X : α → Fin m → ℝ) (bs : Fin m → ℝ) (bcond : γ → Fin m → ℝ)
    (pY : γ → ℝ) (pXgivenY : γ → α → ℝ)
    (hpY : pY ∈ stdSimplex ℝ γ) (hcond : ∀ y, pXgivenY y ∈ stdSimplex ℝ α)
    (hpos : ∀ a, ∀ c ∈ stdSimplex ℝ (Fin m), 0 < wealthRelative X c a)
    (hbs : bs ∈ stdSimplex ℝ (Fin m))
    (hbcond : ∀ y, bcond y ∈ stdSimplex ℝ (Fin m))
    (hKT : ∀ i, (∑ a, sideMarginalX pY pXgivenY a * X a i / wealthRelative X bs a) ≤ 1) :
    condGrowthRate X bcond pY pXgivenY - growthRate (sideMarginalX pY pXgivenY) X bs
      ≤ sideInfoMutualInfo pY pXgivenY
```

**修正内容**: 起草 skeleton は `hKTcond : ∀ y, ∀ i, (∑ a, pXgivenY y a · X a i / wealthRelative X (bcond y) a) ≤ 1`
(= bcond y が条件付き KT-optimal) を持ち、`hbs` / `hbcond` (simplex 帰属) を欠いていた。**honesty 修正**で
`hbcond` は不要 (bcond は任意の条件付き portfolio でよく、CT 16.4.1 の一般形はより強い)、代わりに `hbs` / `hbcond`
(simplex 帰属) を追加。

**honesty メモ**: KT 条件は simplex 帰属を強制しない (反例 m=1, `bcond y = fun _ ↦ 100`: `stdSimplex ℝ (Fin 1)`
は単点 `{1}` だが KT 条件 `∑ a pXgivenY y a · X a 0 / (100·X a 0) = 1/100 ≤ 1` は成立)。⟹ `condGrowthRate`
の成長率解釈 (bcond/bs が genuine portfolio であること) には simplex 帰属が **regularity precondition として
必須**であり、KT bundling で代替できない。独立 `honesty-auditor` が check 4 (増分不等式が仮説から semantic follow、
coarse/fine ミスマッチ・向き逆転無し) を含め PASS で `@audit:ok`。

## Leg B 完全形 (W_∞ AEP) — 🚧 R1 proof-done + R2 core proof-done (selection残)、R3/R4 残

fixed-b core (固定 rebalance portfolio の成長率収束 + KT dominance) は proof-done。**CT 16.5.1 完全形** =
log-optimal `W_∞` (無限過去条件付き成長率の増加極限 `W*(X_0 | X_{-1..−k}) ↑ W_∞`) + AEP `(1/n) log S*_n → W_∞`
は後継計画 [`portfolio-stationary-woo-plan.md`](portfolio-stationary-woo-plan.md) で着手中。着地状況:

- **R1 gateway = 条件付き log-optimal portfolio の可測選択** (`exists_measurable_argmax_on_stdSimplex`) proof-done
  + `@audit:ok` sorryAx-free。
- **R2 core = 条件付き成長率の単調収束** (`condOptGrowth_monotone` / `condOptGrowth_bddAbove`) proof-done
  + `@audit:ok` sorryAx-free、headline `exists_condOptGrowth_tendsto_condOptGrowthInfty` は honest reduction。残る
  residual 1 本 = 条件付き log-optimal 選択 `exists_condLogOptimalSeq` (= R1 gateway の条件付きリフト、Mathlib 壁
  ではない解析 disintegration lift)。R2 は抽象 `Filtration ℕ m0` でパラメータ化 (R3/R4 が具体化を負う)。
- 残る **R3 (real-valued AEP) / R4 (組立)** は未着手。

要件:

- real-valued market の新規インフラを要する — 条件付き log-optimal portfolio の可測選択 + 条件付き成長率の単調収束
  + real-valued SMB 級 AEP。
- in-project `shannon_mcmillan_breiman` (`SMB/AlgoetCover/Liminf.lean:497`) は `[Fintype α] [DecidableEq α]`
  前提の **有限アルファベット機構依存** (`blockLogAvg` / `entropyRate` が pmf ベース) で、連続 price-relative の
  general-measure 市場に直接は lift 不可 (Leg B gateway で評価済)。

⟹ 後継計画 [`portfolio-stationary-woo-plan.md`](portfolio-stationary-woo-plan.md) に分離。要件・gateway-atom 案・
壁リスクは後継計画本文が SoT。

## Leg D — not-a-wall 判明 (壁前提の除去)

起草時 M0 probe は `stdSimplex` 上の測度 / 多変量 Dirichlet 積分の Mathlib 不在を機械確認し、analytic core を
`@residual(wall:…)` (候補名 `simplex-dirichlet-integral`) で分離する撤退を想定していた。**実装で not-a-wall と判明**:

- **Dirichlet 積分の閉形式 (exact-constant regret) は実際には不要** — 正確な定数は Dirichlet 積分に依存するが、
  headline の **asymptotic** regret `(1/n) log(Ŝ_n / S*_n) → 0` は Cover shrink 論法で閉じる。
- shrink 論法 = `bestConstantWealth ≤ exp(1)·(n+1)^d · universalWealth` を simplex を頂点へ相似縮小した部分体積
  比較で得る (`Measure.addHaar_image_homothety` + `exp_neg_one_le_shrink`)。積分核の閉形式評価を回避。

⟹ **wall 候補名 `simplex-dirichlet-integral` は not-a-wall、register 未登録のまま (登録不要)**。regret headline は
proof-done sorryAx-free + `@audit:ok`。撤退ライン (積分核を `sorry` + `@residual(wall:…)` で分離) は不発。

## 正直性メモ (regularity precondition の性質)

全 Leg の追加仮説は **regularity precondition**、load-bearing hypothesis bundling ではない (独立 honesty-auditor
PASS 済):

- **iid / 定常 / 可測性 / Integrable** (`hAs` / `hindep` / `hident` / `MeasurePreserving` / `Ergodic` /
  `Integrable`): 列の統計的構造 + SLLN/Birkhoff の必須前提。命題の核 (収束) を encode しない。
- **`hpos` (`0 < wealthRelative`)**: `Real.log` の凹性定義域 `Ioi 0` 由来の correctness precondition
  (`log 0 = 0` 規約)。
- **simplex 帰属** (`hb` / `hbs` / `hbcond` / `hpY` / `hcond`): 成長率解釈が genuine portfolio / pmf を要する
  ための定義的 precondition。KT 条件からは follow しない (Leg C 反例参照) ゆえ独立に必要。
- **`hKT`** (Leg A dominance / B dominance / C): bs が log-optimal であることの具体的・検証可能な KT 条件。
  証明の核ではなく、静的/積分版 `logOptimal_of_kuhnTucker` を経由して決定的不等式を **内部導出**する定義的特徴付け。

**撤退時 retreat exit は `sorry` のみ**。極限値 / 増分 / 積分核を仮説で渡す load-bearing bundling は禁止。

## 撤退ライン (active — W_∞ 完全形のみ)

A/C/D + B core は proof-done で撤退ライン不発。残る active retreat は Leg B 完全形のみ:

- **Leg B 完全形 (W_∞ AEP)**: 後継 [`portfolio-stationary-woo-plan.md`](portfolio-stationary-woo-plan.md) で
  着手し、詰まった補題は signature を target 形のまま body を `sorry` + `@residual(plan:portfolio-stationary-woo-plan)`
  (slug 整合)。real-valued SMB 級 AEP が genuine Mathlib gap を露呈したらその時点で新 wall slug を建てる。
  **W_∞ を仮説で渡す (`(h : … = W_∞) → …`) load-bearing bundling は禁止。**

## DoD / gate

- **各 phase**: type-check done (`lake env lean` 0 error) で commit/push 可。proof-done (0 sorry ∧ 0 @residual、
  file 内) が genuine 完成。
- **headline `@[entry_point]`**: 各 Leg headline proof-done + 独立 `honesty-auditor` PASS で `@audit:ok`（達成済）。

## 完了時の配線 (状態)

- **root**: 各 Leg の import 登録済。
- **README / roadmap / facts**: 別エージェントが `docs/readme-theorems.txt` / `docs/textbook-roadmap.md` /
  `docs/shannon/portfolio-facts.md` を担当。
- **parent 同期**: 親 `portfolio-moonshot-plan.md` の sub-plan テーブルに本子計画を登録済 (状態 =
  A/B-core/C/D proof-done + W_∞ deferral)。競合時は本子計画が SoT。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)、active のみ残す。

1. **Leg B 完全形は後継計画へ deferral (active)**: fixed-b core を proof-done で着地し、W_∞ AEP (CT 16.5.1 完全形)
   は real-valued SMB 級インフラを要すため [`portfolio-stationary-woo-plan.md`](portfolio-stationary-woo-plan.md)
   に分離。`shannon_mcmillan_breiman` は有限アルファベット機構依存で直接 lift 不可 (gateway 評価済)。

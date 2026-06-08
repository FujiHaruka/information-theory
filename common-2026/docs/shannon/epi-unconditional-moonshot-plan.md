# EPI 無条件化 — entropyPower 再型付け + 3-case 分岐 ムーンショット計画 🌙

> **目標**: 主定理 `entropy_power_inequality` を **全仮説除去した無条件形**にする。
> 現状 (`EntropyPowerInequality.lean:289`) は `(hX hY : Measurable) (hXY : IndepFun X Y P)
> (h_stam : IsStamInequalityResidual X Y P)` を取るが、`h_stam` も密度 regularity も無い、
> **独立性 + 可測性のみ**からの EPI を達成する。
> **slug**: `epi-unconditional-moonshot-plan` (本 plan は傘 umbrella。各 sub-plan の slug は §sub-plan 一覧)。

<!--
記法: 状態絵文字 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更(判断ログ参照)。
取り消し線 = 廃止 Phase (履歴のため残す)。判断ログ append-only。
rg "^- \[ \]" で残タスク横断 grep、rg "🔄" でピボット箇所だけ拾える。
-->

## 規模見積りサマリ (冒頭)

| 項目 | 値 |
|---|---|
| 新規行数オーダー | **~1500–2500 行** (定義二層 + coercion bridge ~300、downstream re-port ~800–1400、3-case assembly ~400–600) |
| touch file 数 | **~38–40 file** (`differentialEntropy` 36 file + `entropyPower` 11 file、重複あり実数 ~40)。ただし下層 (a) Real workhorse を温存する設計のため、大半は **statement 層だけの shim 経由 re-port** に圧縮可能 |
| 最大の wall 候補 | **(W-A) a.c. EPI core** (既存 `stamToEPIBridge_holds` 系の残 sorry。本 plan の責務外、既存 plan 群で進行)。先行調査で **有限分散+有限エントロピーの隠れ regularity が判明** (発見 3) → 射程縮小、要スコープ判断。**(W-B) 混合 case** — 先行調査で **GO/soft 確定** (発見 2、既存 2 補題 + convolution-a.c. 3 行)。**(W-C) coercion 整合** — 先行調査で **解決** (発見 1、`EReal.exp` 実在で非分岐定義可)。真の残 wall は方針 Y を取る場合の **entropy power 弱収束 半連続性** (Mathlib 完全不在、新規) のみ |

**致命的前提 (実コード verbatim 確認済、§Phase 0 の出発点)**: 現定義のままだと無条件 EPI は
**literally FALSE**。`differentialEntropy (Measure.dirac m) = 0` (`DifferentialEntropy.lean:155`
`differentialEntropy_dirac`)、`entropyPower μ := Real.exp (2 * differentialEntropy μ)`
(`EntropyPowerInequality.lean:102`) ⇒ Dirac で `entropyPower = exp 0 = 1`、かつ
`entropyPower_pos` (`:109`) で常に `> 0`。定数 X,Y (独立自明) で 3 項とも 1、左辺 1 ≥ 右辺 2 が
矛盾。根本原因: `differentialEntropy` が rnDeriv の a.c. 部のみ見て `negMulLog 0 = 0` のため
特異測度で `0` に退化 (`-∞` にならない)。現条件付き定理が `h_stam` を load-bearing に持つのは
この退化反例を除外するため。

## 先行調査の結論 (2026-06-05、wall 3 本 verbatim 裏取り済)

3 inventory で壁候補を先行調査。結論を計画に反映。

### 発見 1 (定義 shape, W-C) — GO、設計が簡素化
`docs/shannon/epi-uncond-entropypower-retype-inventory.md`。
- **`Real.exp` ℝ≥0∞ 版不在の前提は覆る**: `EReal.exp : EReal → ℝ≥0∞` が実在
  (`Mathlib/Analysis/SpecialFunctions/Log/ERealExp.lean`、loogle 48 宣言、orchestrator 裏取り済)。
  `EReal.exp_bot : exp ⊥ = 0`、`EReal.exp_coe : exp ↑x = ENNReal.ofReal (Real.exp x)`、
  `EReal.exp_monotone` [gcongr]、`EReal.exp_top`。
  ⇒ **`entropyPower μ := EReal.exp (2 * differentialEntropyExt μ)` の非分岐定義**が可能。
  case-split は `differentialEntropyExt : EReal` 側に一元化 (特異で `⊥`、a.c. で `↑(workhorse)`)。
- **a.c. 判定の definitional 化 GO**: `Decidable (μ ≪ volume)` は不在だが、Mathlib `klDiv`
  (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean:55-58`) が `open Classical in` +
  `irreducible_def` + `if μ ≪ ν then ... else ...` を実運用する precedent。
  `haveLebesgueDecomposition_of_sigmaFinite` (priority 100 instance) が確率測度 on ℝ で自動発火。
- 新規 primitive 自作 0、bridge ~6 本 (~30-40 行)。新撤退ライン候補 L-Uncond-0-δ:
  `EReal.mul` の `2 * ⊥` / `(2:EReal) * ↑x` 挙動が想定外なら ℝ≥0∞ 直接 case-split 定義へ退避。

### 発見 2 (混合 case, W-B) — GO、soft、隠れ壁なし
`docs/shannon/epi-uncond-mixed-case-inventory.md`。
- 混合 case core `h(X) ≤ h(X+Y)` は既存 genuine 2 補題
  (`condDifferentialEntropy_le` `:224` + `condDifferentialEntropy_indep_add_eq` `:328`、両 `@audit:ok`)
  の `c=1` 合成で **そのまま typecheck**。残る穴は `μ.map(X+Y) ≪ volume` の 1 点のみ。
- その 1 点 (`X a.c. ⟹ X+Y a.c.`) は Mathlib に存在: `IndepFun.map_add_eq_map_conv_map` →
  `Measure.conv_comm` → `Measure.conv_absolutelyContinuous` の **3 行で 0 sorry** (撤退ライン不発)。
  注意: `conv_absolutelyContinuous` は a.c. 因子を右に要求する非対称形 → `conv_comm` を 1 段噛ます。
- ℝ≥0∞ lift は `Real.exp_le_exp` + `ENNReal.ofReal_le_ofReal` 標準。`[StandardBorelSpace]` 不要。
- blocker (壁でない): `condDifferentialEntropy_le` の integrability precondition 8 本の threading 量。
  Gaussian 版 `differentialEntropy_indep_gaussian_add_ge` `:378` が同型 threading の雛形。非 load-bearing。

### 発見 3 (a.c. core, W-A) — ⚠ 「無条件」の射程を縮める。要スコープ判断
`docs/shannon/epi-uncond-ac-density-witness-inventory.md`。
- **verdict: case-1 (両 a.c.) EPI は「真に一般 a.c.」では閉じない。有限分散 + 有限微分エントロピーを隠し持つ。**
- assembly `isStamToEPIScalingHyp_of_stam_debruijn` の density-witness は **生入力**
  `P.map X` / `P.map Y` / `P.map (X+Y)` に課される (`EPIStamToBridge.lean:1413/1419/1425`、
  heat-flow 平滑後ではない — wall lemma endpoint は t→0⁺ で平滑が消える生入力点)。
- `IsHeatFlowEndpointRegular` (`EPIG2HeatFlowContinuity.lean`) は **8 density field**
  (`pX`/`hpX_nn`/`hpX_meas`/`hpX_law`/`hpX_int`/`hpX_mass`/`hpX_mom`/`hpX_ent`)。
  assembly の density sorry は **8×3 = 24 個** が正 (旧記載「21」「7 field」は assembly docstring
  `:1307` の `hpX_ent` 脱落由来の誤り、本計画で訂正)。
  - `hpX_mom`: `Integrable (fun y => y^2 * pX y) volume` = **有限 2 次 moment (有限分散)**。a.c. から自動で出ない (Cauchy 反例)。
  - `hpX_ent`: `Integrable (fun x => Real.negMulLog (pX x)) volume` = **有限微分エントロピー**。a.c.+有限分散からも出ない。project が「L¹+2次moment ⟹ negMulLog 可積分」を **false-as-stated と判定して削除済** (`EPIG2HeatFlowContinuity.lean:485` 周辺 docstring) ⇒ honest な追加前提として持つしかない (`@residual(wall:...)` 不可)。
  - 残 6 field は a.c.+確率測度から R-N で自動。
- 余波: `fisherInfo`/`differentialEntropy` は project-local (Mathlib 不在、loogle unknown)。将来 upstream 時 scope 大。

### ⇒ 達成可能な「無条件」の honest な射程 (要ユーザー判断)
退化トラップ除去 (特異入力 → entropyPower 0) は cases 2/3 で**追加前提なし**に達成できる (発見 1+2)。
しかし a.c. ブランチの heat-flow/de Bruijn 証明路は **有限分散 + 有限微分エントロピー**を本質的に要求する (発見 3)。
これは証明技法由来 (Fisher info が heat path 上で有限である必要) で、ただ落とすことはできない。よって:

- **方針 X (regularity-scoped, 推奨)**: `h_stam` と密度 predicate 仮説束を除去するが、a.c. 入力に
  **有限分散 + 有限微分エントロピー**を honest な regularity precondition として残す。教科書 EPI の標準射程
  (densities + finite variance 前提) と一致。本計画の Phase 構造はこれを前提に組める = 達成可能。
- **方針 Y (truly hypothesis-free)**: さらに有限分散も除く。任意 a.c. を有限分散で近似し極限を取る
  truncation/approximation 論法が要る。だが entropy power の弱収束下半連続性は **Mathlib 完全不在**
  (発見 3 + epi-g2-main-closure-inventory「entropy/KL 半連続性 loogle Found 0」) で、これ自体が新規 wall。
  別 moonshot 規模、しかも genuine Mathlib 壁を含む。

→ Phase 3/5 の最終 signature をどちらに置くかをユーザーに確認後、確定する (下記 §スコープ判断)。

## スコープ判断 — **DECIDED: 方針 Y (真に仮説ゼロ)** (2026-06-05、ユーザー確定)

最終主定理は独立性 + 可測性のみ。a.c. ブランチの有限分散 + 有限微分エントロピーも除く。
撤退ライン **L-Uncond-3-scope** = 「方針 Y が semicontinuity wall で genuine に詰まったら、
有限分散+有限エントロピーを honest precondition として残す方針 X に縮退して着地」(honest 後退口、tier 2)。

### 方針 Y の機構 (新クリティカルパス) — § Phase Y / sub-plan S5

a.c. ブランチで生入力に regularity を課す根因は **heat-flow endpoint t→0⁺ の連続性**
(`heatFlowEntropyPower_continuousWithinAt_zero` が生入力の有限分散+有限エントロピー density-witness を要求、発見 3)。
方針 Y はこの endpoint 依存を **近似 + 極限** で迂回する:

1. **t > 0 (平滑側) で無前提 EPI**: heat-flow path 上 `t > 0` では入力が Gaussian と畳み込み済で
   自動的に regular (有限分散・滑らか・有限エントロピー)。よって EPI_t `N(X+√t Z_X + Y+√t Z_Y) ≥
   N(X+√t Z_X) + N(Y+√t Z_Y)` は **入力 regularity 無し**に既存 a.c. core で閉じる (要確認: 平滑後測度が
   density-witness を自動充足するか — 発見 3 は「生入力」と判定したが t>0 平滑後は別、Phase Y-0 で検算)。
2. **t→0⁺ 極限**: EPI_t の各項で `t→0` を取る。RHS は `N(X+√t Z) → N(X)` の収束、LHS は
   `liminf` を取る。不等式が極限で保たれるには **entropy power の下半連続性** (LHS)
   `N(X+Y) ≤ liminf N((X+Y)+√t Z)` と RHS の収束が要る。
3. **真の wall = entropy power 弱収束 半連続性**: `X_t → X` (weak / 法則収束) のとき
   `liminf N(X_t) ≥ N(X)` (or 適切な向き)。**Mathlib 完全不在** (entropy/KL の半連続性 loogle Found 0、
   epi-g2-main-closure-inventory)。これが方針 Y の新規 genuine Mathlib 壁。自作必要。
   - 関連在庫: KL の下半連続性 `MeasureTheory.??` / `lowerSemicontinuous` + portmanteau /
     Fatou 系 (EPIG2KLFatouLSC.lean に klFun-Fatou サンドイッチの genuine 実績あり — 流用候補)。
     **→ § Phase Y の先行調査 S5-inventory で確定 (起動済)**。

注: 退化トラップ除去 (特異 → entropy power 0) は方針 Y でも cases 2/3 の枠組みをそのまま使う。
方針 Y が追加するのは「a.c. だが有限分散でない入力」を平滑近似で救う層のみ。

### ⚠ 方針 Y feasibility verdict (S5 先行調査、2026-06-05、`epi-uncond-truncation-lsc-inventory.md`)

> **🔄 SUPERSEDED (2026-06-07、判断ログ 6 参照)**: 本 verdict の核心 step 1「平滑側は無前提が FALSE」は
> **heat-flow smoothing ルート前提**で、route T (conditioning truncation) が同障害を全回避し覆った **FALSE WALL**。
> 以下「moonshot 規模 + Mathlib 壁 2 本」も smoothing ルート前提の死んだ見積り。現状は W-Y1 第一 chunk 着地
> (`EPIUncondCondEntropyExt.lean`: ①fibre同定/def genuine、mono/(i-a) genuine modulo ②、crux = **② EReal chain rule 1 本に局所化**、
> 監査 honest_residual PASS、S5 子 §7-7)、残る genuine wall は W-Y2 (病的両部発散 a.c.) の 1 本のみ。本節は履歴として残置するが
> 判定は判断ログ 6 + S5 子 §7-6/§7-7 + `epi-uncond-monotone-inventory.md` が SoT。

**結論 (2026-06-05 時点、SUPERSEDED): 方針 Y は数学的には真だが proof route が moonshot 規模 + genuine Mathlib 壁 2 本。L-Uncond-3-scope (方針 X 縮退) を投資効率の点で推奨。ただし最終判断はユーザー。**

- **step 1「平滑側は無前提」が FALSE (genuine 障害)**: Gaussian 畳み込みは **X 由来の裾を消さない**
  (`X+√t Z` は X が無限分散なら無限分散)。よって平滑後測度も `hpX_mom`(有限分散)/`hpX_ent`(有限エントロピー)
  を自動充足しない。⇒ 方針 Y は出発点で既に regularity を要求し、平滑単独では剥がせない。
  剥がすには **X 自体を compact support に truncate する二重近似** (truncate → 平滑 → 二重極限) が必要、層が 1 段増える。
- **核心壁 Mathlib 完全不在 (loogle Found 0 × 5)**: entropy/KL の弱収束下半連続性、Gaussian 畳み込み弱収束。
  新規 wall slug 2 本 `wall:entropy-lsc-weak` / `wall:gaussian-approx-identity-weak`、shared sorry 補題化。
- **流用見込みが食い違い**: §S5 が流用候補とした `negMulLog_convDensity_limsup_le`
  (`EPIG2KLFatouLSC.lean:359`) は **limsup ≤ の逆向き**半連続性で、方針 Y LHS で要る liminf ≥ と向きが逆。
  かつ自身が有限分散 precondition 持ち ⇒ **方針 X でしか機能しない**。
- **型衝突**: `differentialEntropy : Measure ℝ → ℝ` (Bochner、ℝ 値) は `h=+∞` を持てず、極限で `h=+∞` 入力を
  扱う型が無い。二層定義の「Real workhorse 温存」制約と衝突 → workhorse 側も EReal 化が要る可能性 (blast radius 増)。
- **自作量概算**: 弱収束 LSC bridge 200-400 行 (Mathlib 壁含む) + 近似単位元弱収束 80-150 行 +
  a.c. 枝 `h=+∞` 型修正。別 moonshot 規模。

⇒ **本計画は当面 case1 を有限分散版 (= 方針 X 相当の honest 中間到達点) で完成させ、方針 Y (regularity 完全剥がし)
は独立 moonshot `epi-uncond-truncation-lsc-plan` として分離する**のが構造的に妥当
(方針 X 中間形が方針 Y の入力でもあるため、どちらに進んでも先に case1 有限分散版が要る)。
最終 signature を方針 X で締めるか方針 Y まで押すかは、case1 完成後に再判断可能 (後戻り無し)。

## 進捗

- [x] Phase 0 — feasibility gate ✅ (発見 1-3 + 方針 Y verdict、§先行調査)
- [x] Phase 1 — 二層定義導入 + coercion bridge ✅ **genuine 0 sorry** (commit `3421948`、`EntropyPowerExt.lean`、`epi-entropypower-retype-plan` 全 Phase done) → [sub-plan: epi-entropypower-retype-plan]
- [~] Phase 2 — downstream re-port 🔄 **rename 不要 verdict (S2 plan)** → headline は `entropyPowerExt` 直接、旧 10 consumer 全 (a) Real 不変で書換 0、naming cleanup は後回し可 → [sub-plan: epi-downstream-report-plan]
- [x] Phase 3 — a.c. EPI core (case 1) ✅ **CLOSED 2026-06-07 (両有限エントロピー前提のみ、有限分散不要)**: case 1 (両 a.c.) は `entropyPowerExt_add_ge_finite_ac` (`EPIUncondDispatch.lean`、`#print axioms` sorryAx-free、`@audit:ok`) で proof-done。有限分散枝 = smoothing-limit closure、無限分散枝 = route T (S6 capstone、FALSE WALL 解消)。当初の「difference G3 経路 / ratio-limit walled」判定 (判断ログ 2/3) は route T pivot で迂回され不要に。**有限分散すら precondition から外れた** (当初の方針 X 射程 a.c.+有限分散+有限エントロピー より強く、a.c.+有限エントロピーのみ) → 判断ログ 5
- [x] Phase 4 — 特異・混合 case ✅ **case 2/3 genuine** (commits `fd5d05c`/`9a25df9`、`EPIUncondMixedCase.lean`、`#print axioms` sorryAx-free) → [sub-plan: epi-singular-mixed-case-plan]
- [x] Phase 5 — 主定理 assembly ✅ **方針 X 完全達成 2026-06-07**: `entropyPowerExt_add_ge_dispatch_skeleton` の全 4 枝が proof-done (case 1 closure 済 + case 2/3 genuine、`#print axioms` = sorryAx-free)。実数版 headline も `entropy_power_inequality_of_ac` (`EPIUncondDispatch.lean:249`、a.c.+有限エントロピー precondition、proof-done、独立監査 `@audit:ok` tier-1) で達成 — 現 `entropy_power_inequality` (h_stam + 未証明橋 `stamToEPIBridge_holds` を transitive 消費、proof-done でない) の honest 後継。**真の `_unconditional` 命名は依然不可** (dispatch は 16 integrability precondition を持つ、完全無条件 = 方針 Y は別 moonshot で genuine walled) → 判断ログ 5

proof-log: 各 Phase 完了時に別途 `docs/shannon/proof-log-epi-unconditional-phase-*.md` (Phase 0 のみ proof-log: no、調査のみ)。

---

## ゴール / Approach

**最終定理 (達成目標)**: 独立可測 `X Y : Ω → ℝ` に対し、新 `entropyPower : Measure ℝ → ℝ≥0∞` 下で

```
entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)
```

を **`h_stam` 無し・密度 regularity 無し**で証明する (`hX hY hXY` のみ)。

### Approach (解の全体形 — 3 つの柱)

#### 柱 1: 二層定義 (退化トラップ除去、解析中核を Real に温存)

退化トラップの除去は「特異測度を `0` でなく `-∞`(エントロピー) / `0`(エントロピーパワー) に
落とす」再型付けで達成する。ただし de Bruijn / Fisher / heat-flow / Stam の解析中核は **normed
field (ℝ) を要求** するため EReal/ℝ≥0∞ を載せられない (下記設計制約)。よって **二層構造**:

- **(a) Real 値 workhorse** — `differentialEntropy : Measure ℝ → ℝ` (現定義を**そのまま温存**、改名のみ検討)。a.c. 測度 / 密度の微分エントロピー。de Bruijn `HasDerivAt` / Stam / AWGN translation invariance が主役として使う。**触らない (= 既存 genuine 資産を保護)**。
- **(b) EReal / ℝ≥0∞ 上位レイヤ** — 任意測度に対する `differentialEntropyExt : Measure ℝ → EReal` (a.c. ブランチで (a) から coerce、特異ブランチで `⊥`) + `entropyPower : Measure ℝ → ℝ≥0∞` (a.c. ブランチで (a) から、特異で `0`)。**EPI 主定理の statement だけ (b)**。

**Mathlib-shape-driven** (先行調査 発見 1 で確定、2026-06-05):
- **`entropyPower μ := EReal.exp (2 * differentialEntropyExt μ)` の非分岐定義を採用** (第一候補)。
  `EReal.exp : EReal → ℝ≥0∞` 実在 (`Mathlib/Analysis/SpecialFunctions/Log/ERealExp.lean`)、
  `exp_bot : exp ⊥ = 0` (特異 → entropyPower 0 自動)、`exp_coe : exp ↑x = ENNReal.ofReal (Real.exp x)`
  (a.c. → Real workhorse と一致)、`exp_monotone` [gcongr] (EPI 不等式の lift に直結)。
  case-split は `differentialEntropyExt : EReal` 側のみ。
- `differentialEntropyExt μ := if μ ≪ volume then ↑(differentialEntropy μ) else (⊥ : EReal)`。
  a.c. 判定の definitional 化は `klDiv` precedent (`open Classical in` + `irreducible_def`) で GO。
- 退避 (L-Uncond-0-δ): `EReal.mul` の `2 * ⊥` 挙動が想定外なら ℝ≥0∞ 直接 case-split
  `if μ ≪ volume then ENNReal.ofReal (Real.exp (2 * differentialEntropy μ)) else 0` へ。

#### 柱 2: 3-case 分岐 (無条件成立の構造)

新 ℝ≥0∞ 定義下で EPI を case 分けで TRUE にする。`hXac := (P.map X) ≪ volume` 等で a.c./特異を判定:

1. **両方 a.c.** (密度あり): 既存 genuine 機械 (柱 3) を (a) 層で再配線。a.c. なら新 `entropyPower = ENNReal.ofReal (exp (2·h))` が Real workhorse の値と一致し、不等式は **既存 Real EPI を ℝ≥0∞ に coerce** すれば従う。**ここが hard core (= 既存 plan 群の残課題)**。
2. **片方のみ特異** (例 Y 特異、`N(Y)=0`): RHS = `N(X) + 0 = N(X)`。要するは `N(X+Y) ≥ N(X)`。これは full EPI より **soft**: `h(X+Y) ≥ h(X+Y | Y) = h(X | Y) = h(X)` (conditioning reduces entropy + 独立)。**既存 genuine 資産 2 本で組める** (柱 3 注記)。
3. **両方特異**: RHS = `0 + 0 = 0`。`N(X+Y) ≥ 0` は ℝ≥0∞ で **型自明** (`zero_le`)。

3-case を `Phase 4` (case 2/3) + `Phase 3` (case 1) + `Phase 5` (assembly) に割り振る。

#### 柱 3: a.c. 既存 genuine 資産の保存 + 再配線

既存 EPI bridge chain の genuine 部分は (a) Real 層の上で**不変**。`#print axioms` 実測済 genuine:
G1 log-ratio reframe / G2 heat-flow 端点連続 / scaling→bridge 組立 / richness lift B1 /
Gaussian saturation / L-EPI1 Stam / L-EPI2 de Bruijn。残 sorry (G3 rescale / assembly 22 sorry の
21 density-witness + 1 joint-indep / richness in-place B2 / W0/W1 wiring) は **case 1 (両 a.c.)
内部の前提**として残り、a.c. なので density-witness は充足可能。

**case 2 (混合) の鍵資産 (verbatim 確認済、既に genuine CLOSED)**:
- `condDifferentialEntropy_le` (`EPIG2ConvEntropyMonotone.lean:224`、genuine sorryAx-free): `h(X|Z) ≤ h(X)` (conditioning reduces entropy)。
- `condDifferentialEntropy_indep_add_eq` (`:328`、genuine `@audit:ok`): `X ⊥ Z` で `h(X + c·Z | Z) = h(X)` (独立和 fibre 同定)。

この 2 本の合成で混合 case の `h(X+Y) ≥ h(X)` の core が **既に in-tree に存在**。Phase 4 は
これを ℝ≥0∞ entropyPower の単調性 (`exp` 単調 → `ENNReal.ofReal` 単調) に持ち上げる plumbing。

### 設計制約 (Mathlib-shape-driven 必須、orchestrator 実測根拠)

- de Bruijn 恒等式は `HasDerivAt (fun t => differentialEntropy (P.map ...)) ((1/2)·fisherInfo) t` 形 (`FisherInfoV2DeBruijnAssembly.lean:3522`)。`HasDerivAt` は normed field を要求 → **EReal 不可**。
- AWGN 系 (`AWGNMIBridge.lean` 等) は translation invariance / Gaussian 値の等式・不等式で `differentialEntropy` を Real 算術の主役に使う。
- ⇒ **(a) を Real のまま温存**、(b) は a.c. 枝で (a) を coerce する薄いラッパに留める。これにより 36-file re-port の大半が「(a) を呼ぶ箇所はそのまま、(b) を要求する箇所だけ shim」に圧縮される。

---

## Sub-plan 一覧 (umbrella 配下、依存順)

本 plan を傘とし、実装は以下 sub-plan に分割する。slug は `@residual(plan:<slug>)` と一致させる。

| # | sub-plan slug | スコープ | 依存 | 状態 |
|---|---|---|---|---|
| S1 | `epi-entropypower-retype-plan` | 柱 1: (a)(b) 二層定義導入 (`differentialEntropyExt : Measure ℝ → EReal`、新 `entropyPower : Measure ℝ → ℝ≥0∞`) + (a)→(b) coercion bridge lemma 群。a.c./特異 判定述語。`EReal.toENNReal_bot` 整合。 | Phase 0 (在庫確定) | 📋 **plan 起草済** ([`epi-entropypower-retype-plan.md`](epi-entropypower-retype-plan.md)、Phase A–D) |
| S2 | `epi-downstream-report-plan` | 柱 1 cont.: 36-file の `differentialEntropy`/`entropyPower` 参照を (a)(b) いずれが必要か分類し re-port。statement-層 shim + import 順序の DAG。AWGN/Fisher/de Bruijn は (a) のまま不変であることを検証する re-port。 | S1 | 📋 |
| S3 | `epi-singular-mixed-case-plan` | 柱 2: case 2 (混合) + case 3 (両特異) の新規補題。`condDifferentialEntropy_le` + `condDifferentialEntropy_indep_add_eq` から ℝ≥0∞ `N(X+Y) ≥ N(X)` への lift。case 3 は `zero_le` 自明。3-case 判定 + dispatch。 | S1 (補題は直接立つ)、S2 (headline assembly のみ) | 📋 **plan 起草済** ([`epi-singular-mixed-case-plan.md`](epi-singular-mixed-case-plan.md)、Phase 0–5。case 2 integrability feasibility = **GO**。補題は S1 のみで着地可、headline は傘 Phase 5 defer) |
| — | (case 1 a.c. core closure) | 柱 3: 既存 plan 群を**流用** (新規 sub-plan を作らない)。`epi-stam-to-conclusion-plan` / `epi-csiszar-ratio-reframe-plan` / `epi-richness-route-b-plan` / `epi-g2-*` が SoT。 | (進行中) | 既存 |
| S5 | [`epi-uncond-deffix-monotone-plan`](epi-uncond-deffix-monotone-plan.md) (W-Y1) / [`epi-uncond-truncation-lsc-plan`](epi-uncond-truncation-lsc-plan.md) (W-Y2 = route β') | **方針 Y クリティカルパス (2026-06-07 再評価、smoothing FALSE WALL)**: W-Y1 拡張単調性 + +∞ 伝播 (plan-closeable plumbing、gateway atom 着手済) / W-Y2 = **route β' (truncation+monotone-limit)** で無限エントロピー a.c. 入力の gateway ⊤ 枝を closure。smoothing ルートの「t>0 平滑側無前提 EPI + t→0⁺ 極限」は route T/β' が迂回し不要に。 | case1 (route T closure 済) + S1 | 🚧 W-Y1: 新 file `EPIUncondCondEntropyExt.lean` で ①fibre同定/def genuine + (i-a) sorry 消滅、crux を **② EReal chain rule 1 本に局所化**。**✅ 2026-06-08: ② finite-entropy 版 `differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite` genuine 着地** (sorryAx-free、`@audit:ok`)。**finiteness-free 版②は per-fibre mass 相殺で証明不能と確定** (advisor 裏取り) → 無条件版は **W-Y2 = route β' で別途**。**✅ 2026-06-08: route β' plan 起草 + Phase 0 gate = GO** (`epi-uncond-truncation-lsc-plan.md`、判定 (B) path 可視 moonshot、ターゲット = gateway ⊤ 枝不等式)。Phase 0 で weak-conv 回避を機械裏取り (Fatou lift `A_W≤liminf A_{W_n}` が density a.e. 収束のみから fire、`klDiv_le_liminf_of_ae_tendsto` 同型) ⇒ `wall:entropy-lsc-weak` 回避確定。**✅ 2026-06-08: Phase 1 skeleton + Phase 2 proof-done。`differentialEntropyExt_mono_add_truncW` (per-n 単調性) sorryAx-free、独立 honesty-auditor all OK**。**ルート転換**: chain rule 等式 (finite ②) は `hκ_dens_meas` (joint 密度可測、Mathlib 真 gap、loogle Found 0) を必須仮説に持ち proof-done 不能 → **単調性は不等式で足る**との advisor 判定で chain rule lemma を捨て、場合分け + explicit translate per-fibre Gibbs (`differentialEntropy_le_cross_entropy` + 平行移動 fibre + Tonelli collapse) に転換。`hκ_dens_meas`/`hκ_KL`/`hκ_cross_int` を**全廃**。残単一 crux = single-component Jensen helper `negPart_negMulLog_conv_single_ne_top` も genuine。次: **Phase 3 = `h(W_n) ↑ h(W)` 極限** (`differentialEntropyExt_truncW_tendsto` + Fatou helper)。SoT → `epi-uncond-truncation-lsc-plan.md` 判断ログ5 |
| S4 | (assembly、本 plan Phase 5 で直接) | 柱 2+3 合流: 3-case dispatch → 無条件主定理。方針 Y では case1 を S5 経由の無前提版に差替。新 sub-plan 不要、本 plan §Phase 5。 | S1–S3 + S5 | 📋 |
| S6 | [`epi-infinite-variance-truncation-plan`](epi-infinite-variance-truncation-plan.md) | **無限分散 a.c. 古典 EPI 構築 (`wall:epi-infinite-variance-classical` の genuine close)** ✅ **CLOSED 2026-06-07**: route T (conditioning truncation、有限分散 EPI 黒箱再利用 + R→∞) で **sorryAx-free genuine closure 完了**。`wall:epi-infinite-variance-classical` は FALSE WALL と判明 (sharp Young/Brascamp-Lieb 不要)。集約先 `EPIInfiniteVarianceCapstone.lean` の `entropyPowerExt_add_ge_infinite_variance` (case split + P 版負部可積分)、無条件 dispatch `entropyPowerExt_add_ge_dispatch_skeleton` まで sorryAx-free、独立 honesty audit PASS (defect 0)。 | case1 有限分散版 EPI (closure 済) | ✅ CLOSED (route T、capstone) |

**依存 DAG (方針 Y、2026-06-07 再評価)**: `Phase 0 → S1 → S2 → {S3, case1(route T closure 済)} → S5 → Phase 5(S4)`。
S5 が方針 Y の本体。**smoothing ルート (「平滑側無前提 EPI + 半連続性極限」) は route T が迂回し不要**。
S5 は W-Y1 (拡張単調性 + +∞ 伝播、plan-closeable、gateway atom `entropyPowerExt_mono_add` 着手済) と
W-Y2 = route β' (有限エントロピーすら無い a.c. を truncation 近似で救う層、`epi-uncond-truncation-lsc-plan`
起草済、ターゲット = gateway ⊤ 枝不等式、route T 機構流用、総合判定 (B) path 可視 moonshot) に分離。
L-Uncond-3-scope (方針 X 縮退) は **発動不要** (smoothing 壁解消、判断ログ 6)。W-Y1 が closeable でなければ
dispatch headline を a.c.+有限エントロピー版 (`entropy_power_inequality_of_ac`、proof-done) に留める honest 中間形。

---

## Phase 0 — feasibility gate (新定義 shape 確定 + 数学的裏付け + Mathlib 在庫指示) 📋

proof-log: no (調査のみ。実装着手しない)。**この Phase が GO/NO-GO gate**。

### 0-A: 新定義 shape の確定 (要 inventory phase 委任項目を明示)

- [ ] `entropyPower : Measure ℝ → ℝ≥0∞` の定義形を確定。**設計分岐 (i) case-split 定義** を第一候補とする: a.c. case `ENNReal.ofReal (Real.exp (2 * differentialEntropy μ))`、特異 case `0`。判定述語は `μ ≪ volume` (Mathlib `Measure.AbsolutelyContinuous`)。**要在庫**: a.c./特異の **decidable でない** 判定をどう定義に組むか — `if μ ≪ volume then ... else 0` は `Decidable` instance を要する。代替: `differentialEntropyExt : Measure ℝ → EReal` を `(μ.rnDeriv volume の積分が finite かつ μ が a.c.) ? coe(h) : ⊥` 形で定義し、`entropyPower μ := (差分形).toENNReal`-経由で exp を**避ける**経路を再評価 (が、`exp` 不在ゆえ toENNReal だけでは entropyPower にならない)。**→ inventory に「a.c. 判定を definitional に組む Mathlib パターン (`Measure.rnDeriv` の `withDensity` 復元 `μ = volume.withDensity (rnDeriv) + singular`、`Measure.haveLebesgueDecomposition`)」を委任**。
- [ ] `differentialEntropyExt : Measure ℝ → EReal` の特異 case `⊥`、a.c. case `coe (differentialEntropy μ)` の coercion 形を確定。`EReal.coe_add` で和保存。
- [ ] **要在庫確認 (verbatim、予測禁止)**: `Real.exp` の ℝ≥0∞/EReal 持ち上げ不在 (loogle Found 0 を再確認)。`ENNReal.ofReal_exp` 系の有無。`EReal.toENNReal` の単調性 `EReal.toENNReal_le_toENNReal` (存在確認済)。`ENNReal.ofReal` の加法 `ENNReal.ofReal_add` (a.c.+a.c. の RHS 和を coerce で組むため)。

### 0-B: 無条件成立の数学的裏付け (3-case feasibility)

- [ ] **case 1 (両 a.c.)**: 既存 Real EPI `exp(2h(X+Y)) ≥ exp(2h(X))+exp(2h(Y))` が成立する前提下で、`ENNReal.ofReal` が和を保存する (`ENNReal.ofReal_add`、両 nonneg) ことを確認 → ℝ≥0∞ 不等式が従う。**裏付け OK の条件 = case1 で Real EPI が genuine に閉じること** (= 既存 plan 群の残課題、本 plan の責務外だが gate には記録)。
- [ ] **case 2 (混合)**: `condDifferentialEntropy_le` + `condDifferentialEntropy_indep_add_eq` の合成で `h(X+Y) ≥ h(X)` が出るか **verbatim signature で検算** (両者の前提 — measurability / `μ.map X ≪ volume` / KL 有限性系 integrability — が case 2 で充足可能か)。⚠ **要確認**: これらの前提は a.c. 側 X についての regularity であり、Y が特異でも X が a.c. なら満たせる見込み。ただし `condDifferentialEntropy_le` は多数の integrability precondition を持つ (`:229-245` verbatim) — これらが「特異 Y を条件付ける」設定で充足可能かを inventory で検算。**NO-GO 兆候**: X も特異な混合は case 2 でなく case 3 に落ちる (RHS の a.c. 項が消える) ので、case 2 は「X a.c. ∧ Y 特異」に限定して良いことを確認。
- [ ] **case 3 (両特異)**: RHS = 0、`N(X+Y) ≥ 0` は `zero_le` で自明。裏付け不要。

### 0-C: Mathlib / InformationTheory API 在庫指示 (inventory phase へ委任)

以下を `mathlib-inventory` サブエージェントに **structured per-lemma output** (file:line / 完全 signature / `[...]` 前提 verbatim / 結論形 verbatim) で委任する。**予測値は書かず、確認できないものは「要調査」マーク**:

1. **EReal/ℝ≥0∞ 算術**: `EReal.coe_add` / `EReal.toENNReal` 系 32 lemmas のうち単調性・⊥規約・`toENNReal_bot`、`ENNReal.ofReal_add` / `ENNReal.ofReal_le_ofReal`、`Real.exp` の ℝ≥0∞ 持ち上げ (不在確認)。
2. **a.c./特異 definitional 判定**: `Measure.haveLebesgueDecomposition` / `Measure.rnDeriv` / `Measure.singularPart` / `Measure.MutuallySingular`、a.c. を `Prop`/`Decidable` で定義に組むパターン。
3. **case 2 資産 verbatim**: `condDifferentialEntropy_le` (`:224`) + `condDifferentialEntropy_indep_add_eq` (`:328`) の全前提を verbatim 抽出 + 充足可能性。
4. **既存 entropyPower consumer 11 file の参照形** (どれが等式・不等式・Real 算術を要求するか) を grep ベースで列挙 (re-port 分類の素材、S2 の DAG 入力)。

### Phase 0 撤退ライン

- **L-Uncond-0-α** (NO-GO 条件): `entropyPower` の case-split 定義に `Decidable (μ ≪ volume)` が要り、かつ Mathlib に classical instance が無く `Classical.dec` で組むと downstream の `simp`/`rfl` が全滅する場合 → 定義を `differentialEntropyExt : EReal` 一本に寄せ、`entropyPower := (差分の toENNReal)` で `exp` を回避する代替設計を再評価。最悪、本 moonshot を「EReal 微分エントロピー版 EPI (entropyPower 版は corollary)」に縮退。
- **L-Uncond-0-β** (case 2 NO-GO): `condDifferentialEntropy_le` の integrability 前提が「特異 Y を条件付ける」設定で充足不能 (= 混合 case の core が組めない) と判明 → 混合 case を **honest precondition 付き partial** (`entropy_power_inequality_mixed_under_X_regular` 等) に留め、無条件性を「両 a.c. ∨ 両特異」に縮小。docstring に「NOT fully unconditional」明示。
- **L-Uncond-0-γ** (退化定義悪用の自己監査): 新定義が特異測度で `⊥`/`0` を返す設計は、case 3 で RHS=0 を突いた **vacuous 達成** に見えうる。これは退化 case の正しい値 (特異測度のエントロピーパワーは真に 0) なので OK だが、**LHS が常に 0 になるような定義ミス** (例: a.c. 判定が常に false に転ぶ) を Phase 1 着地時に `gaussianReal` で非自明値確認する (Gaussian は a.c. で `entropyPower (gaussianReal m v) = 2πe v ≠ 0`)。退化定義悪用 (CLAUDE.md tells) の自己 gate。

---

## Phase 1 — 二層定義導入 + 既存 Real 資産の coercion bridge 📋 → `epi-entropypower-retype-plan`

proof-log: yes (sub-plan 側)。

- [ ] (a) `differentialEntropy : Measure ℝ → ℝ` を温存 (改名するなら全 consumer 同期、しないのが第一候補)。
- [ ] (b) `differentialEntropyExt : Measure ℝ → EReal` + `entropyPower : Measure ℝ → ℝ≥0∞` を新規導入 (Phase 0 で確定した shape)。**`def` の RHS が詰まったら** CLAUDE.md「sorry を書けない箇所」第一選択 = 結論形に合わせた定義書換、第二選択 = `@audit:defect` マーク (本 plan を `@audit:closed-by-successor`)。`Prop := True`/退化定義悪用は禁止。
- [ ] coercion bridge: `entropyPower_eq_ofReal_of_ac : μ ≪ volume → entropyPower μ = ENNReal.ofReal (Real.exp (2 * differentialEntropy μ))`、`entropyPower_singular : ¬(μ ≪ volume) → entropyPower μ = 0` (or Lebesgue 分解の特異部判定形)。
- [ ] **非自明値 sanity** (L-Uncond-0-γ gate): `entropyPower (gaussianReal m v) = 2πe v` (a.c. 枝)、`entropyPower (dirac m) = 0` (特異枝)。Dirac が **新定義で 0 になる**ことを確認 (旧 1 → 新 0 の退化トラップ除去を verbatim 検証)。

### Phase 1 撤退ライン

- **L-Uncond-1-α**: coercion bridge で `ENNReal.ofReal` と `EReal.toENNReal` の経路が二重定義になり整合 lemma が hell 化 → 一方の経路に統一 (定義は 1 つ、もう一方は導出 lemma)。
- **L-Uncond-1-β**: 旧 `entropyPower` (Real) を消すと EPI 系 11 file が一斉に壊れる → 旧 Real `entropyPower` を `entropyPowerReal` に退避して残し、新 ℝ≥0∞ 版を `entropyPower` とする (S2 で consumer を順次移行)。

---

## Phase 2 — downstream 36-file re-port (段階順序・依存) 📋 → `epi-downstream-report-plan`

proof-log: yes (sub-plan 側)。

re-port は **(a) を呼ぶ箇所は不変、(b) を要求する箇所だけ shim** 原則。順序は import DAG の葉から根へ:

- [ ] **層 0 (不変確認)**: Fisher / de Bruijn / AWGN 系 (`FisherInfoV2DeBruijnAssembly` / `AWGNMIBridge` / `ParallelGaussianConverse` 等、計 ~25 file) は (a) `differentialEntropy : ℝ` を使う。**変更不要**を `lake env lean` で確認するだけ (改名しない限り no-op)。
- [ ] **層 1 (entropyPower consumer 11 file)**: EPI 系のみ。新 ℝ≥0∞ `entropyPower` への移行。等式形は coercion lemma で書換、不等式形は ℝ≥0∞ 不等式に。Gaussian saturation `entropyPower_gaussian_additivity` (`:331`) は a.c. なので bridge 経由。
- [ ] **層 2 (主定理 + corollary)**: `EntropyPowerInequality.lean` の statement を新型に。corollary (scaling / log-form / multi-arg) を新型 reshape。
- [ ] import 順序 DAG を sub-plan 冒頭に表で固定 (循環回避)。**verbatim 確認**: 改名する場合の olean refresh 順 (CLAUDE.md「upstream edits 後 olean refresh」)。

### Phase 2 撤退ライン

- **L-Uncond-2-α**: AWGN/Fisher 系が実は (b) 上位型を要求している箇所が見つかる (Real 不変の前提が崩れる) → 当該箇所だけ (a)→(b) coercion を挿入。広範なら S2 のスコープを再見積り。
- **L-Uncond-2-β**: 36-file re-port が 1 session で終わらない → file 群を family batch に分割し type-check done 単位で commit (各 batch `lake env lean` clean)。

---

## Phase 3 — a.c. EPI core 完成 (case 1) 📋 → 既存 plan 群流用

proof-log: 既存 plan 側 (新規起こさない)。

case 1 (両 a.c.) の hard core は **既存の bridge chain closure**。本 plan では新規 sorry を作らず、
既存 plan の残課題を消費する形で参照する:

- 残 G3 rescale (`csiszarGap_antitoneOn_Icc_zero_one`, `EPIStamToBridge.lean`) → `epi-stam-to-conclusion-plan` §Phase A-close G3。
- assembly `isStamToEPIScalingHyp_of_stam_debruijn` の 22 sorry (21 density-witness + 1 joint-indep) → **a.c. case 内部の前提として正当化**。a.c. なので density-witness は充足可能 (= 入力分布の Real 密度 regularity を a.c. case 仮定から供給)。本 plan の Approach 柱 3 がこの「density-witness を a.c. case 仮定として正当化する」流れを設計。
- richness in-place B2 → `epi-richness-route-b-plan` (G2 待ち保留中)。
- G1 ratio reframe / G2 端点連続性 → 既に genuine CLOSED (verbatim 確認済)。

**本 plan Phase 3 の唯一の新規作業**: a.c. case の `entropyPower` (新 ℝ≥0∞) が、既存 Real EPI
`entropy_power_inequality` (旧、Real 版) を coerce して得られることを示す bridge lemma
`entropy_power_inequality_ac : (P.map X ≪ volume) → (P.map Y ≪ volume) → (h_stam) → 新型 EPI`。
**注意**: ここで `h_stam` は **a.c. case 内部前提**として残ってよい (a.c. なので density から供給可能、無条件化の対象は最終 statement であり、case 1 内部での density 前提は柱 3 の設計上 honest)。最終的に case 1 の `h_stam` も既存 plan 群が closure すれば完全 sorryAx-free。

### Phase 3 撤退ライン

- **L-Uncond-3-α**: 既存 plan 群の case1 core が未完 (G3/B2 残 sorry) のまま → case1 を `@residual(plan:epi-stam-to-conclusion-plan)` で transitive park。本 plan の **無条件性は「3-case dispatch が genuine」で達成**し、case1 内部 sorry は既存 plan に委譲 (compound `@residual` で両方指す)。これは honest (sorry は被呼出 wall が保持、dispatch 自体は genuine)。

---

## Phase 4 — 特異・混合 case (soft 補題) 📋 → `epi-singular-mixed-case-plan`

proof-log: yes (sub-plan 側)。

- [ ] **case 3 (両特異)**: `entropyPower (P.map (X+Y)) ≥ 0` を `zero_le` で。RHS = `0 + 0 = 0` を特異判定から。**最も soft**、新規 ~20-40 行。
- [ ] **case 2 (X a.c. ∧ Y 特異)**: RHS = `N(X) + 0 = N(X)`。要 `N(X+Y) ≥ N(X)`。鍵: `condDifferentialEntropy_le` + `condDifferentialEntropy_indep_add_eq` (両 genuine、verbatim 確認済) の合成で `h(X+Y) ≥ h(X+Y | Y) = h(X)`、`exp` 単調 + `ENNReal.ofReal` 単調で `N(X+Y) ≥ N(X)`。**前提充足**: `condDifferentialEntropy_le` の integrability 群を「X a.c.、Y 特異」設定で供給 (Phase 0-B で feasibility 確認済が前提)。
- [ ] **case 対称性**: case 2 の X↔Y 対称版 (Y a.c. ∧ X 特異)。
- [ ] **3-case 判定 + dispatch** スケルトン (Phase 5 で本体 assembly)。`P.map X ≪ volume` 等の Lebesgue 分解判定。

### Phase 4 撤退ライン

- **L-Uncond-4-α** (case 2 前提不足): `condDifferentialEntropy_le` の integrability 前提が混合設定で組めない → case 2 を honest precondition 付き (`..._of_X_integrable`) に留め `sorry` + `@residual(plan:epi-singular-mixed-case-plan)`、無条件性は「両 a.c. ∨ case3」に縮小 (L-Uncond-0-β と整合)。
- **L-Uncond-4-β** (`X+Y` の a.c./特異判定): X a.c. ∧ Y 特異のとき `X+Y` が a.c. になる (convolution は a.c. を保つ) ことの Mathlib lemma が要る → 在庫不在なら `condDifferentialEntropy` 経由で a.c. 判定を迂回 (entropy 直接比較、`entropyPower` の a.c. 枝に依らない形)。**禁止**: 退化定義悪用 (特異判定を常に true に倒して case3 に流し vacuous 達成) — L-Uncond-0-γ gate で検出。

---

## Phase 5 — 無条件主定理 assembly + #print axioms 検証 📋

proof-log: yes。

- [ ] 3-case dispatch を `entropy_power_inequality_unconditional` (新名) に組む: `P.map X ≪ volume` / `P.map Y ≪ volume` の 4 通り (両 a.c. / X のみ / Y のみ / 両特異) を `by_cases` 分岐し、各々 Phase 3 (case1) / Phase 4 (case2 両向き / case3) を呼ぶ。
- [ ] 主定理 signature: `(hX hY : Measurable) (hXY : IndepFun X Y P)` **のみ** (h_stam 除去)。conclusion は新 ℝ≥0∞ EPI。
- [ ] **`#print axioms entropy_power_inequality_unconditional`** で sorryAx 依存を実測。case1 が既存 plan に transitive park 中なら sorryAx 残存は honest (compound `@residual(plan:epi-stam-to-conclusion-plan,...)` で明示)。case2/3 + dispatch が genuine なら、無条件性の **構造**は sorryAx-free に達成、残は case1 内部のみ。
- [ ] 旧条件付き `entropy_power_inequality` (`:289`、Real 版 + h_stam) は **取り消し線化せず corollary として残す** (a.c. 特殊形)。または無条件版から導出。
- [ ] **独立 honesty-auditor 起動** (新規 sorry + `@residual` を導入した場合、CLAUDE.md 必須)。dispatch の honesty (退化定義悪用していないか、case3 の vacuous 達成でないか、case2 の前提が load-bearing でなく regularity か) を独立検証。

### Phase 5 撤退ライン

- **L-Uncond-5-α**: dispatch の `by_cases (P.map X ≪ volume)` が `Decidable` を要し classical で組むと axioms に `Classical.choice` が増える → これは propext/Quot.sound と同列で許容範囲 (sorryAx ではない)、honest。問題なし。
- **L-Uncond-5-β**: 無条件主定理が case1 の残 sorry を transitive 消費し続ける場合 → **部分達成として honest 命名**で commit (`entropy_power_inequality_unconditional` の docstring に「case1 (両 a.c.) は `epi-stam-to-conclusion-plan` の closure 待ち、混合/特異 case は genuine」明示)。moonshot の「無条件構造」は達成、「完全 sorryAx-free」は case1 closure 後。

---

## 撤退ライン共通規律

全 Phase 共通禁止 (CLAUDE.md 検証の誠実性): `Prop := True` placeholder / 結論型≡仮説型 `:= h`
循環 / load-bearing `*Hypothesis` predicate に核を bundle / **退化定義悪用** (特に本 plan は新定義
が特異 case で `0`/`⊥` を返すため、case3 の vacuous 達成や a.c. 判定の常時 false 倒しが
退化定義悪用に該当しうる — L-Uncond-0-γ gate で常時自己監査)。撤退時 docstring に「NOT a
discharge / load-bearing on <...>」明示。新規 `sorry` + `@residual` 導入時は独立 honesty-auditor 起動。

**honest 撤退口**: 詰まったら `sorry` + `@residual(plan:<該当 sub-plan slug>)` (def RHS が詰まったら
CLAUDE.md「sorry を書けない箇所」第一選択 = 定義書換、第二選択 = `@audit:defect` + `@audit:closed-by-successor(epi-unconditional-moonshot-plan)`)。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-06-05 起草 (Approach 1 採用、二層構造確定)**: project owner が「既存 def を作り直す
   (Approach 1)」を選択。orchestrator 実測の致命的事実 (`differentialEntropy_dirac = 0` →
   現定義で無条件 EPI literally FALSE) + 設計制約 (de Bruijn `HasDerivAt` が normed field 要求で
   EReal 不可) から **二層構造** (a) Real workhorse 温存 + (b) EReal/ℝ≥0∞ statement 層 を確定。
   3-case 分岐 (両 a.c. / 混合 / 両特異) を Phase 骨格に。
   - **verbatim 確認済 (予測でなく実コード)**: `differentialEntropy_dirac = 0`
     (`DifferentialEntropy.lean:155`)、`entropyPower := Real.exp (2 * differentialEntropy)`
     (`EntropyPowerInequality.lean:102`)、`entropyPower_pos` (`:109`)、主定理 +
     `IsStamInequalityResidual` shape (`:211/:289`)、case2 鍵資産 `condDifferentialEntropy_le`
     (`EPIG2ConvEntropyMonotone.lean:224`、genuine) + `condDifferentialEntropy_indep_add_eq`
     (`:328`、genuine `@audit:ok`)。
   - **loogle 在庫 (verbatim)**: `EReal.toENNReal` 系 32 lemmas + `EReal.toENNReal_bot` (⊥→0、
     特異→entropyPower=0 ルート) 存在。`EReal.coe_add` 存在。⚠ **`Real.exp` の EReal/ℝ≥0∞ 版は
     不在** (loogle `Real.exp, EReal` = Found 0、`ENNReal.exp` = unknown) → entropyPower を
     ℝ≥0∞ で素朴 exp 定義できない、case-split 定義 (a.c. 枝で Real exp + `ENNReal.ofReal`) を
     第一候補に。`negMulLog` EReal 版も不在。
   - **要在庫調査マーク (Phase 0-C で inventory 委任、予測値を書かない)**: a.c./特異の
     definitional 判定パターン (`Measure.haveLebesgueDecomposition` / `Decidable (μ ≪ volume)`)、
     `ENNReal.ofReal_add` / 単調性、`X a.c. ∧ Y 特異 ⇒ X+Y a.c.` (convolution 保存) の Mathlib
     lemma 有無、`condDifferentialEntropy_le` の integrability 前提が混合設定で充足可能か。
   - **既存 plan 統合方針**: case1 (a.c. core) は新 sub-plan を作らず既存
     `epi-stam-to-conclusion-plan` / `epi-csiszar-ratio-reframe-plan` (G1 CLOSED) /
     `epi-richness-route-b-plan` (B1 done) / `epi-g2-general-sandwich-moonshot-plan` (G2 CLOSED) を
     流用。新規 sub-plan は S1 retype / S2 downstream re-port / S3 singular-mixed の 3 本。

2. **2026-06-05 orchestrator セッション (S1 + S3 genuine 着地、case 1 両ルート walled 確定)**: Phase 0 の
   方針 Y 分離後、本線 case1 有限分散版を進めるべく orchestrator パターンで複数トラック並列実行。
   - **Phase 1 (S1 retype) genuine 完成** (commit `3421948`): `EntropyPowerExt.lean`、非分岐
     `entropyPowerExt := EReal.exp (2 * differentialEntropyExt μ)` + bridge/sanity 8 declaration 全 0 sorry。
     退化トラップ除去を verbatim 検証 (旧 dirac=1 → 新 dirac=0)。`epi-entropypower-retype-plan` 全 Phase done。
   - **Phase 4 (S3 case 2/3) genuine 完成** (commits `fd5d05c`/`9a25df9`): `EPIUncondMixedCase.lean`、
     case 2 (混合) + case 3 (両特異) が `entropyPowerExt` 上で sorryAx-free。独立 honesty-auditor が
     dispatch skeleton に tier-5 DEFECT (load-bearing implication-hyp) を検出 → Phase 4 補題直接呼出に修正。
   - **Phase 2 (S2) rename 不要 verdict**: headline は `entropyPowerExt` 直接 state 可、旧 10 consumer 全
     (a) Real 不変で書換 0。dep DAG を `S1→{S2-A, S3, case1}→Phase5` に訂正。Phase 5 は naming cleanup 不要。
   - **Phase 3 (case 1) 両ルート walled 確定 (重要)**: (i) ratio-limit 経路 = `csiszarLogRatioGap_tendsto_zero_atTop`
     (t→∞ 極限) が **entropic CLT 級の genuine Mathlib 壁** (`entropy-power-clt-limit`、Mathlib CLT は分布収束のみ、
     loogle 0 件) で NO-GO (`epi-case1-ratio-limit-plan`)。(ii) difference G3 経路 = rescale が削除済 false-as-framed
     D3/D6 (difference-1-source-antitone) を要求するもつれ (`epi-csiszar-ratio-reframe-plan` 判断ログ 10)。
     ⇒ **case 1 (両 a.c. = 古典 EPI) は honest park 継続が確定**。
   - **Phase 5 = 方針 X partial が honest 到達点**: `entropyPowerExt_add_ge_dispatch_skeleton` が case 2/3 genuine
     + case 1 park の 3-case dispatch。これを bare `entropy_power_inequality_unconditional` に rename するのは
     **name laundering** (16 integrability precondition + case 1 sorry を持つため、`*_unconditional` 命名禁止、
     CLAUDE.md)。完全 `_unconditional` は case 1 closure (両ルート walled) + 方針 Y (別 moonshot) を要する。
   - **副次発見**: G2 系 3 wall は 2026-06-05 全 CLOSED (layer-2 sandwich) → `epi-richness-route-b-plan` の
     B2 trigger 発火済。だが case 1 は G3 で別途 block ゆえ B2 の headline ROI は依然低い (richness 単独で
     unblock しない)。proof-pivot-advisor の「G3 false-dependent」verdict は implementer verbatim check が訂正。

3. **(2026-06-05 後刻、独立壁再確認で case 1 difference G3 を walled でないと訂正)**: 判断ログ 2 の Phase 3
   「両ルート walled」のうち **difference G3 経路は walled でなかった** (ratio-limit NO-GO は維持)。独立壁
   再確認 3 件で 2 つの誤前提を訂正:
   - **(i) `wall:blachman-general-density` は FALSE WALL**: 一般密度 producer
     `isBlachmanConvReady_convDensityAdd_gaussian` (`EPIBlachmanGeneralDensity.lean:224`、19/19 genuine、
     sorryAx-free、`@audit:ok`) が実在し per-`t` の `IsBlachmanConvReady` を任意 a.c. 密度から供給。
     reframe plan の wall 判定 (`:93, :113`) は producer landing 後の drift
     (`epi-blachman-general-density-recheck-inventory.md`)。
   - **(ii) difference G3 carrier は genuine**: `csiszarLogRatioGap_antitoneOn_Ici_zero`
     (`EPIStamToBridge.lean:1085`, sorryAx-free) を rescale lift `csiszarGap_antitoneOn_Icc_zero_one`
     (`:1270`, sorry) の carrier に持ち、判断ログ 2 の「false-as-framed D3/D6 もつれ」は誤り。残る G3 sorry は
     6 AC/integrability の per-`s` 供給 + s=1 端点 = pure assembly (Mathlib 壁なし、reframe plan 判断ログ 10
     の verbatim 訂正)。
   - **(iii) 方針 Y は genuine walled**: entropy LSC が Mathlib 不在 + klFun-Fatou と向き逆
     (`epi-method-y-lsc-recheck.md`) → honest 到達目標は **方針 X** (a.c.+有限分散+有限エントロピー
     precondition)。
   - **帰結**: Phase 3 は park 解除、新規 closure plan `epi-case1-difference-g3-closure-plan` に展開。残課題
     = G3 rescale assembly + joint-indep `hXYZXY` under-hyp + 24 density-witness precondition thread +
     `stamToEPIScaling_holds:214` over-claim 修正 (前提ゼロ主張、honest 化要)。headline
     `stamToEPIBridge_holds` を方針 X で sorryAx-free 化するのが closure plan の到達点。**真の
     `_unconditional` (前提ゼロ)** は方針 Y (別 moonshot、genuine walled) を要する点は不変 — closure plan
     は方針 X の honest 限界まで。

4. **2026-06-06 S1 retype の false-statement defect 発見 + def-fix** (orchestrator 機械検証 + 独立 honesty audit): Phase 1 (S1 retype, commit `3421948`) で "genuine 0 sorry" とした `entropyPowerExt` は、a.c. 枝 `ofReal(exp(2·differentialEntropy μ))` が Bochner `differentialEntropy` の非可積分時 garbage `0` 返しにより **infinite-entropy a.c. 入力で FALSE-as-stated** だった (機械検証 `/tmp/test_garbage.lean`: 密度 ∝ 1/(x log²x) 等 h=±∞ の a.c. を entropyPowerExt=1 に潰し、dispatch case-1 obligation を偽に)。退化トラップ除去 (特異→0) は正しかったが a.c. 枝の ±∞ 表現が欠けていた。
   - **訂正**: `differentialEntropyExt` の a.c. 枝を **正部・負部の EReal 差** `(∫⁻ ofReal(negMulLog f):EReal) - (∫⁻ ofReal(-(negMulLog f)):EReal)` に書換 (`EReal.exp` が exp⊤=∞/exp⊥=0/exp↑x=ofReal を吸収)。h=+∞ (正部発散)→⊤→∞、h=−∞ (負部発散)→⊥→0、有限→workhorse 一致。⚠ recon synthesis の素朴案「非可積分→⊤」は **h=−∞ を ∞ に飛ばす別の偽命題ゆえ誤り** (符号判別必須)。全 sorryAx-free (`integral_eq_lintegral_pos_part_sub_lintegral_neg_part` 経由 bridge)。
   - **dispatch**: case-2 に finite-entropy 前提追加 + `_of_ac_integrable` 化 (genuine 維持)、case-1 の false bare sorry を named wall `entropyPowerExt_add_ge_finite_ac` に置換。**headline TRUE-as-stated 化 + sorry を named wall に局所化**。独立 honesty audit 0 defect。(2026-06-07: 旧 bundled wall を正則 [Phase A 既閉] / 有限分散 [closure 済、commit 452ea1b] / 無限分散 [`@residual(wall:epi-infinite-variance-classical)`] に 3 分解。dispatch は import cycle 回避で `EPIUncondDispatch.lean` に分離移動。)
   - **slug**: `epi-uncond-deffix-monotone-plan` (def-fix campaign)。infinite-entropy (±∞) 入力の precondition 撤去 (+∞ 伝播 / 拡張単調性) は同 plan で後続。教訓: 「0 sorry」は false-statement を排除しない (CLAUDE.md「0 sorry だけでは完成判定にならない」の def-level 実例)。退化境界値 (h=±∞) は実機械検証で裏取りしないと直感 (garbage 0) で偽定義を量産する。

5. **2026-06-07 case 1 完全 closure + 実数版 a.c. EPI proof-done (本セッション)**: route T (S6 capstone、無限分散 conditioning truncation) が無限分散 a.c. 枝を genuine closure (sorryAx-free) したことで、case 1 (両 a.c.) 全体が `entropyPowerExt_add_ge_finite_ac` で **proof-done** に到達 (有限分散枝 = smoothing、無限分散枝 = route T、両枝 sorryAx-free、`#print axioms` 機械再確認 = `[propext, Classical.choice, Quot.sound]`)。**当初の方針 X 射程 (a.c.+有限分散+有限エントロピー) より強く、有限分散 precondition が外れた** (a.c.+有限エントロピーのみ)。判断ログ 2/3 の「case 1 difference G3 / ratio-limit walled」判定は route T pivot で迂回され無効化 (壁を別ルートで迂回した実例、CLAUDE.md「壁判定は独立 pivot で再確認」)。
   - **実数版 headline 橋**: `entropy_power_inequality_of_ac` (`EPIUncondDispatch.lean:249`) を追加。拡張版 `entropyPowerExt_add_ge_finite_ac` (proof-done) + 既存橋 `entropyPowerExt_of_ac_integrable` (`EntropyPowerExt.lean:118`) で実数版 EPI を a.c.+有限エントロピー前提下に **proof-done** 化。独立 honesty-auditor PASS (tier-1、core-reconstruction test で precondition 非バンドル確定 = a.c.+有限エントロピーは entropyPower を well-defined にするだけで superadditivity 核を供給しない、命名 `_of_ac` honest)。**現 `entropy_power_inequality` (`:289`) は h_stam + 未証明橋 `stamToEPIBridge_holds` を transitive 消費し proof-done でない** ため、本補題がその honest 後継 (precondition を h_stam → a.c.+有限エントロピー regularity に置換)。park 理由 (型壁 +∞ / 弱収束 LSC Mathlib 不在) は完全無条件 (方針 Y) の壁であり、a.c.+有限エントロピー版は回避。
   - **方針 Y への含意**: route T が「a.c. だが有限分散でない入力」を救う層 (方針 Y クリティカルパス §Phase Y step) を genuine に達成した。残る完全無条件 (方針 Y) の壁は「有限エントロピーも剥がす (h=±∞ a.c. 入力)」+「a.c. でない一般測度」。entropyPowerExt の def-fix で h=±∞ は表現可能になったが EPI 不等式自体の h=±∞ 成立性は別検討。完全無条件は引き続き別 moonshot として park (再評価の余地は次セッション)。

6. **2026-06-07 方針 Y 再評価 — smoothing 壁 FALSE WALL 判明 + W-Y1 gateway atom 着手**: 判断ログ 5 末尾「完全無条件は別 moonshot として park」を **ユーザー指示で再評価**し、§方針 Y feasibility verdict (2026-06-05、SUPERSEDED 済) を覆した。
   - **smoothing 壁は FALSE WALL**: `epi-method-y-lsc-recheck.md` / `epi-uncond-truncation-lsc-inventory.md` の「方針 Y genuine walled (L-Uncond-3-scope 推奨)」判定は **全て heat-flow smoothing ルート前提**だった。proof-pivot-advisor + mathlib-inventory 独立確認で、route T (conditioning truncation) が smoothing の 3 障害 (平滑が裾を消さない / ℝ workhorse が ±∞ 非表現 / 弱収束 LSC が Mathlib 不在) を **全回避**すると判明。route T は既に case 1 無限分散枝を genuine closure 済 (判断ログ 5) で、同機構が方針 Y の「±∞ a.c. 入力」層にも効く。L-Uncond-3-scope (方針 X 縮退) は **発動不要**。
   - **W-Y1/W-Y2 分離** (`epi-uncond-monotone-inventory.md`): 方針 Y の残壁を 2 本に分離。
     - **W-Y1 = 拡張単調性 + +∞ 伝播** (`h=±∞ 含む a.c.`、両部発散除く): `plan:epi-uncond-deffix-monotone-plan` 所有の **known-shape self-build** (wall でない)。gateway atom `entropyPowerExt_mono_add` (`EPIUncondMonotone.lean`、新規 file) を着手 (commit `834af6d`、当初 2 sorry = +∞ 伝播 + 有限枝)。**2026-06-07 continuation (本ハンドオフ系列): feasibility gate (route α-ii probe) → restructure 済** (commit `2826f9f`/`44130ab`): probe verdict = route α viable (verdict B、Mathlib 壁でない)、crux を単一 EReal 恒等式 (i-a) `differentialEntropyExt(P.map(W+V)) = differentialEntropyExt(P.map W) + (klDiv(...):EReal)` (h(W)≠⊥) に局所化。gateway を「(i-a)+算術」の identity-centric 形に rewrite し trichotomy 廃止 → **`differentialEntropyExt_mono_add` / `differentialEntropyExt_top_of_indep_add` は genuine modulo (i-a)** (top-propagation は mono の系に逆転、旧 2 sorry → **単一 crux sorry (i-a)**)。独立 honesty-audit (本 session) = 3 declaration 全て honest_residual PASS、classification `plan:` 妥当。残務 = (i-a) 本体の EReal chain rule self-build (§7-6 道 A、~150-300 行 moonshot だが path 可視)。
     - **W-Y2 = entropy power 弱収束半連続性** (病的両部発散 a.c. = 有限エントロピーすら無い入力): `wall:gaussian-approx-identity-weak` (Gaussian approx identity loogle Found 0) で **genuine wall 1 本残置** = 完全無条件の限界。W-Y1 まで closure すれば h=±∞ 含む a.c. (両部発散除く) + 退化 case が無条件化。
   - **+∞ 伝播 machine 再評価 (本セッション、proof-pivot-advisor + 独立 loogle 裏取り)**: advisor は「案 F (V a.c. 追加) + 案 B (B-only Jensen + enorm A=⊤) で ~80-130 行 closeable、撤退ライン不発」と楽観したが、**実機械検証で過小評価と判明** (CLAUDE.md「楽観主張も実機械で裏取り」)。(1) Mathlib の Jensen は全て `Integrable (g∘f)` 要求 (verbatim) → B_{W+V}<⊤ の Jensen route は ⊤ 枝 (A_W=⊤) で破綻。(2) `Measure.conv` entropy-monotone / essSup peak bound / lintegral Jensen = loogle conclusion-shape 二段とも **Found 0**。(3) advisor の「enorm で A=⊤」は **循環** (B<⊤ 下で「和エントロピー非可積分」≡「A=⊤」、capstone Case 2 は `¬hent_sum` を by_cases で得ていた)。⇒ 真の攻略は **EReal 単調性を直接出す route α (EReal-conditioning)** で、A/B 分解 (B<⊤ も A=⊤ も) を回避する。これは `differentialEntropy : Measure ℝ → ℝ` の型壁 (h=±∞ 非表現) を越える **multi-session moonshot 規模**。攻略計画は子 plan `epi-uncond-deffix-monotone-plan.md` §7 が SoT。
   - **ユーザー判断 (本セッション)**: 大ゴール (方針 Y 完全無条件) は不変、次 session で壁に挑む。⇒ honest dead-park でなく、§7 攻略計画を立ててハンドオフ。現到達点 `entropy_power_inequality_of_ac` (a.c.+有限エントロピー、proof-done) は方針 X より strictly 強い honest 中間形として保持しつつ、W-Y1 (route α) を次 session の本線とする。residual は `plan:` 据置 (Mathlib-不能 wall でなく known-shape の大規模 self-build、route α 型壁で詰まれば §7-4 判断点で `wall:` 昇格)。

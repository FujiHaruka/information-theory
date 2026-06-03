# T4-A LZ78 漸近最適性 完遂 — blockRV/StationaryProcess kernel 層 サブ計画 🌙

> **Parent**:
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md) §「撤退ライン L-LZ1 (Ziv inequality) / L-LZ2 (converse)」
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. LZ78 漸近最適性」(Cover–Thomas Ch.13.5, Thm 13.5.3)
>
> **Supersedes (一部 / 設計 prior)**:
> - [`lz78-residual-discharge-plan.md`](./lz78-residual-discharge-plan.md) — 当該 plan の **Phase C3
>   converse 経路 (`2^{-lz(x)} ≤ Pₙ{x}` via shannonLength)** は **数学的に不健全** と確定済
>   (`LZ78ConverseKraft.lean:38-40,103-105` のコメントが「LZ78 は per-path で Shannon code を下回りうる
>   = pointwise 偽」と明記)。本 plan は採らない。
> - [`lz78-ziv-bridge-plan.md`](./lz78-ziv-bridge-plan.md) — Phase 4 compProd telescoping が
>   実行不可だった経緯。本 plan はその根本原因 (blockRV の射影性) に**正面から対処する refactor 設計**。
> ziv-bridge / residual plan は archive 扱い (削除しない、prior として参照)。
>
> **Inventory (必読、設計確定済)**:
> - [`lz78-ziv-bridge-inventory.md`](./lz78-ziv-bridge-inventory.md) — log-sum 原始子在庫、per-path
>   factorization 不在の確定、`blockLogAvg ↔ parsing` bridge 0% の確定
> - [`lz78-mathlib-inventory.md`](./lz78-mathlib-inventory.md) — Kraft / Shannon code 資産
>
> **Goal (短形)**: 主定理 `lz78_two_sided_optimality_distinct_genuine`
> (`InformationTheory/Shannon/LZ78AchievabilityLimsup.lean:254`) が現在 honest load-bearing 入力として
> 受ける **2 つの per-path primitive 仮説**:
> - `IsLZ78AchievabilityZivUpperBound` (`LZ78AchievabilityLimsup.lean:102`、Eq.13.124)
> - `IsLZ78ConverseCodingLowerBound` (`LZ78ConverseKraft.lean:106`、Eq.13.130)
>
> を **genuine 構成で discharge** し、無仮定 distinct headline `lz78_two_sided_optimality_distinct`
> (ergodic process + finite alphabet のみ) を publish する。**0 sorry / 0 warning / 標準B**。
>
> 両 primitive の真の crux はいずれも **per-path parsing factorization `Pₙ{x} = ∏ⱼ qⱼ`**
> (telescoping / 条件確率の連鎖) を当層で導出すること。それを阻むのが **`blockRV` の射影性**:
> `StationaryProcess` (`Stationary.lean:81`) は shift `T` + 単一観測 `X` のみで kernel / compProd /
> disintegration 構造を持たない。本 plan はこの **kernel 層を additive に注入する refactor を設計**する。

## Status (2026-05-21)

> **本 plan 起草時の実態整合 (Read 確認済)**:
>
> 1. **headline は 2 primitive まで来ている**。`lz78_two_sided_optimality_distinct_genuine`
>    (`LZ78AchievabilityLimsup.lean:254`) は 2 つの **structure 型 honest 仮説** (`slack` 付き
>    per-realization eventual inequality) から `lz78_two_sided_optimality_distinct_bdd_free`
>    へ genuine に合流済 (`limsup`/`liminf` plumbing + SMB boundedness はすべて genuine)。
>    `h_bdd_above`/`h_bdd_below` も distinct counting envelope で内部 discharge 済
>    (`lz78DistinctEncodingLength_isBoundedUnder_le/_ge`)。**残るのは 2 primitive のみ**。
>
> 2. **2 primitive はいずれも honest** — `structure ... : Prop where upper/lower + slack_tendsto`、
>    型 ≠ 結論、`:= h` 循環でも `:True` でもない。docstring が load-bearing を明示。これらは
>    本プロジェクトの撤退ライン慣習の正しい姿。本 plan は **撤退ラインを越えて proving** する。
>
> 3. **factorization の足場は既に組まれている**。`LZ78ZivEntropyBridge.lean` に
>    `parsingBoundary` (`:133`) / `prefixBlockProb` (`:141`) / `condPhraseProb` (`:158`、
>    `= Pₘ₊₁{prefix}/Pₘ{prefix}` の concrete ratio) / `IsLZ78PerPathParsingFactorization`
>    (`:179`、honest hyp、`factor` + `pos` 2 field) / `blockProb_neg_log_eq_sum` (`:206`、
>    genuine、`Real.log_prod` 経由) が **既に存在**。Z-side の真の残作業は
>    `IsLZ78PerPathParsingFactorization.factor` を **proving** すること。
>
> 4. **`blockRV` は単純射影で kernel 構造ゼロ** (`Stationary.lean:81`、`blockRV p n = fun ω i => p.obs i ω`、
>    `obs i = X ∘ T^[i]`)。`StationaryProcess` の 4 field は `T`/`X`/`measurePreserving`/`measurable_X` のみ。
>    Mathlib `Measure.compProd_apply` (`= ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ`) は適用先 kernel `κ` が無い。
>
> 5. **converse は per-path には偽、a.s. eventual でのみ真** (`LZ78ConverseKraft.lean:30-40`)。
>    LZ78 は universality ゆえ固定 `x` で Shannon code を下回りうる。`IsLZ78ConverseCodingLowerBound`
>    の per-path eventual 形 (`blockLogAvg n ω - slack n ≤ lz/n`) は **expectation-level coding 下界
>    (averaged Kraft) を ergodic theorem で a.s. eventual に持ち上げて初めて genuine になる**。
>    pointwise Shannon-code 経路 (`2^{-lz} ≤ Pₙ`) は不健全につき**採らない**。

## 進捗

- [ ] Phase 0 — 在庫調査 (kernel/disintegration の typeclass 前提 + blast radius 全数確定) 📋 → [`lz78-blockrv-refactor-inventory.md`](./lz78-blockrv-refactor-inventory.md)
- [ ] Phase K1 — `KernelStationaryProcess` (or additive field) 設計確定 + skeleton 📋
- [ ] Phase K2 — kernel 層から `Pₙ{x} = ∏ⱼ qⱼ` (telescoping factorization) を genuine 構成 📋
- [ ] Phase K3 — `IsLZ78PerPathParsingFactorization.factor` を K2 から供給 (Z-side crux) 📋
- [ ] Phase Z — achievability primitive `IsLZ78AchievabilityZivUpperBound` を factorization + log-sum + counting から genuine 構成 📋
- [ ] Phase C — converse primitive `IsLZ78ConverseCodingLowerBound` を expectation-level Kraft + ergodic lift で genuine 構成 📋
- [ ] Phase R — Ch.4 既存定理 (EntropyRate/SMB/Birkhoff) 全数再検証 (refactor 非破壊確認) 📋
- [ ] Phase V — 無仮定 headline publish + `InformationTheory.lean` 編入 + clean check 📋

## ゴール / Approach

### 最終到達点 (Phase V 完成形)

```lean
namespace InformationTheory.Shannon

/-- **T4-A 無仮定 distinct headline (Cover–Thomas Thm 13.5.3)**: finite alphabet 上の
ergodic process について、distinct LZ78 encoding の per-symbol rate は a.s. entropy rate に
収束する。2 per-path primitive (Eq.13.124 / 13.130) は内部で genuine discharge 済、
h_bdd_above/below も distinct counting envelope で discharge 済。標準B (無条件機械検証)。 -/
theorem lz78_two_sided_optimality_distinct
    {α Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n => (lz78DistinctEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess)) := ...
```

既存 `..._genuine` / `..._bdd_free` / `..._converse_discharged` は **signature 不変で残す**
(下流互換)。本 plan は新規補題の追加 + import のみ、既存 genuine 補題の証明・型は触らない。

### Approach (overall strategy / shape of solution)

**全体戦略 = factorization の根本原因 (blockRV 射影性) を kernel 層 additive 注入で解消 →
両 primitive を genuine 構成 → 無仮定 headline。**

#### 設計の中核判断: factorization 経路 (a/b/c の選択)

タスクが提示した 3 経路を Mathlib API の conclusion form verbatim と blast radius で評価した。
**結論: 経路 (a) の additive 変種 = `[KernelStationaryProcess]`-style な「kernel 構造を付帯情報
として供給する別構造 / typeclass」を採る。既存 `StationaryProcess` 定義は一切改変しない。**

```
経路 (a) StationaryProcess に kernel/compProd 構造を additive 注入        ← 採用 (additive 変種)
経路 (b) refactor せず Mathlib disintegration (condKernel) で Pₙ を直接分解   ← 不採用 (理由 ★1)
経路 (c) per-path Ziv を factorization 非依存に純組合せで組み直す            ← 不採用 (理由 ★2)
```

**★1 経路 (b) を不採用とする理由 (Mathlib API 確認結果)**:
Mathlib disintegration `Measure.compProd_fst_condKernel : ρ.fst ⊗ₘ ρ.condKernel = ρ`
(`Kernel/Disintegration/StandardBorel.lean:64`) は **任意の measure を後ろ向き Bayes 条件付きに
分解する純 measure-theoretic 恒等式**であり、`[StandardBorelSpace]` を要求する (有限 alphabet ×
有限 index で `Fin n → α` は自動 derive 見込みだが要 Phase 0 確認)。**しかしこれは factorization の
"形" を与えるだけで Cover–Thomas の中身を与えない**: `condKernel` は単に `Pₙ = Pₙ₋₁ ⊗ₘ (条件付き)`
の分解で、その条件付き kernel が **stationary process の「次の記号の条件付き法則」と一致する保証が
無い**。parsing factorization の核心は「条件確率が phrase 確率と一致し、stationarity で telescoping
する」点であり、それは **process の逐次条件付け構造そのもの (Markov-like)** に依る。disintegration
だけでは process 構造に触れないため、結局 stationarity を別途 process 側で表現する必要がある。
→ disintegration は K2 の**道具**として使うが (compProd_apply / lintegral_compProd の conclusion
form を再利用)、process 側に kernel 構造を持たせる経路 (a) と**組み合わせて**初めて genuine に閉じる。

**★2 経路 (c) を不採用とする理由**:
Cover–Thomas Eq.13.122–124 の Ziv 不等式 `c·log c ≤ -log Pₙ{x}` の右辺は **measure-theoretic な
`-log Pₙ{x}`** であり、これを下から押さえるには `-log Pₙ = -Σⱼ log qⱼ` の積分解 (= factorization)
が論理的に不可避。既存 genuine counting `lz78PhraseStrings_mul_log_le` (`LZ78ZivCountingBody.lean:353`)
は `c·log c ≤ K·n` (定数 rate `K` への bound) を与えるが、これは `limsup blockLogAvg` ではなく
`K` への bound。`K·n → -log Pₙ` の橋がまさに factorization。純組合せで `-log Pₙ` 自体を回避する
経路は無い (inventory VERDICT (C) と一致)。

#### kernel 層 additive 注入の具体形 (経路 a 変種、Phase K1)

**既存 `StationaryProcess` (`Stationary.lean:45`) の 4 field は一切触らない**。代わりに、process の
逐次条件付け構造を表す **別構造 or typeclass** を新規に置く。2 案を Phase K1 で確定:

- **案 K1-α (typeclass)**: `class HasTransitionKernel (μ) (p : StationaryProcess μ α)` を新設し、
  `transKernel : Kernel (List α) α` (履歴 → 次記号の条件付き法則) + `compatible :
  μ.map (blockRV n) = (μ.map X) ⊗ₘ ... ⊗ₘ transKernel` 系の **compatibility field** を持たせる。
  ergodic / finite-alphabet では実例構成が必要 (Phase K1 で「typeclass を要求するだけで実例は
  下流が供給」か「finite case で実例を genuine 構成」かを判定)。

- **案 K1-β (別構造)**: `structure KernelStationaryProcess (μ) (α)` を新設し、`toStationaryProcess`
  coercion + kernel field を持たせる。`ErgodicProcess` とは別系統で、本 plan の定理だけがこれを
  消費する。**既存 `StationaryProcess`/`ErgodicProcess` を要求する全 Ch.4 定理は無傷**。

**blast radius を最小化するため案 K1-β (別構造) を第一候補**とする (理由: 既存 `StationaryProcess`
への field 追加・typeclass 制約追加が一切無く、Ch.4 の全 consumer が型レベルで無傷)。ただし
**主定理は最終的に `ErgodicProcess` のみで無仮定にしたい**ので、K1-β の `KernelStationaryProcess`
を ergodic + finite-alphabet から **genuine に構成する instance/補題** が必要 (Phase K2 の前半)。
これが本 plan の最大の数学的負荷であり、撤退ライン L-K (下記) の判定点。

> **honesty 注記 (最重要)**: kernel 構造の compatibility field を「公理的に仮定するだけ」で
> ergodic process から実例を構成しないと、それは **load-bearing hyp を別名で隠す name laundering**
> になる。本 plan の genuine 完遂条件は「ergodic + finite alphabet **だけ**から kernel 層を構成」
> すること。構成できなければ撤退ライン L-K で **isolated honest hyp として明示** (現状の 2 primitive
> より厳密に primitive な 1 述語、型 ≠ 結論、docstring で load-bearing 明示) に留める。

#### Mathlib-shape-driven の設計選択 (結論側を変えない)

- `condPhraseProb` (`LZ78ZivEntropyBridge.lean:158`、ratio of prefix block probs) と
  `IsLZ78PerPathParsingFactorization.factor`/`pos` (`:183,:190`) の述語定義を **一切変えない**。
  Phase K3 はこれら既存 honest hyp の **body を満たす定理を kernel 層から genuine に証明**する。
- 2 primitive `IsLZ78AchievabilityZivUpperBound` (`LZ78AchievabilityLimsup.lean:102`) /
  `IsLZ78ConverseCodingLowerBound` (`LZ78ConverseKraft.lean:106`) の structure 定義も **変えない**。
  Phase Z/C はこれらを満たす instance を `slack` を明示構成して返す。
- kernel field の結論形は `Measure.compProd_apply` (`= ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ`) と
  `Measure.lintegral_compProd` の conclusion に合わせて固定 (Phase K1 で verbatim 確認)。
  textbook literal の `P(phrase|context)` 形を先に書かない。

### Approach 図

```
                lz78_two_sided_optimality_distinct (Phase V, 無仮定)
                                  │  (h_bdd_above/below は distinct 版で discharge 済)
        ┌──────────────────────────┴──────────────────────────┐
   IsLZ78AchievabilityZivUpperBound        IsLZ78ConverseCodingLowerBound
   (Eq.13.124, per-path upper, Phase Z)    (Eq.13.130, per-path lower, Phase C)
        │                                       │
   ┌────┴──────────────┐                  ┌─────┴──────────────────┐
 per-path Ziv          既存 counting       expectation-level       既存 SMB blockLogAvg
 c·logc ≤ -log Pₙ      c·logc ≤ Kn ✅      Kraft 下界 (averaged)    (黒箱 reuse)
 = factorization (K3)  (黒箱 reuse)        + ergodic a.s. lift
        │                                       │
   IsLZ78PerPathParsingFactorization.factor   ┌─┴────────────────┐
        │ (既存 honest hyp の body、Phase K3) entropyD_le_       Birkhoff/ergodic
        │                                     expectedLength_     による a.s. eventual 化
   ┌────┴──────────────────────┐              of_kraft ✅          (Cover–Thomas 13.130)
 KernelStationary 層 (K1)   disintegration     (ShannonCode:164)
 = kernel 構造 additive 注入  compProd_apply
   + ergodic から実例構成 (K2)  (Mathlib 道具)
        │
   ★ 最大の数学的負荷 = 撤退ライン L-K の判定点
```

### 規模見積

| Phase | 中央 | 範囲 | 出力 | proof-log |
|---|---|---|---|---|
| Phase 0 | — | — | `lz78-blockrv-refactor-inventory.md` (kernel typeclass 前提 + blast radius 全数) | no |
| Phase K1 | **80 行** | 50–150 | kernel 層 (`KernelStationaryProcess` or class) 設計確定 + skeleton | no |
| Phase K2 | **250 行** | 150–450 / 撤退時 honest hyp 1 本 | ergodic→kernel 層 実例 + telescoping factorization | yes |
| Phase K3 | **80 行** | 50–150 | `IsLZ78PerPathParsingFactorization.factor`/`pos` 供給 | yes |
| Phase Z | **150 行** | 100–250 | `IsLZ78AchievabilityZivUpperBound` instance (factorization + log-sum + counting + slack) | yes |
| Phase C | **220 行** | 150–400 | `IsLZ78ConverseCodingLowerBound` instance (averaged Kraft + ergodic lift) | yes |
| Phase R | **20 行** | 10–40 | Ch.4 既存定理 全数再検証 (非破壊確認、新規証明なし) | no |
| Phase V | **20 行** | 10–40 | 無仮定 headline + `InformationTheory.lean` import + clean check | no |
| **累計** | **~820 行** | **520–1480** | 1–2 新規 file + import | — |

### ファイル構成

```
InformationTheory/Shannon/
  StationaryKernel.lean         ← 新規 (~330 行) — kernel 層 (経路 a 変種、K1–K3)
                                  ・KernelStationaryProcess (or class HasTransitionKernel)
                                  ・ergodic + finite → kernel 層 実例 (K2 前半、★crux)
                                  ・blockProb_eq_prod_telescope (K2 後半、disintegration 道具)
                                  ・IsLZ78PerPathParsingFactorization 供給定理 (K3)
  LZ78ZivEntropyBridge.lean     ← (拡張) achievability primitive instance (Phase Z)
                                  ・既存 def/hyp/補題は不変、ziv_per_path_mul_log_le +
                                    isLZ78AchievabilityZivUpperBound_distinct を追記
  LZ78ConverseKraft.lean        ← (拡張) converse primitive instance (Phase C)
                                  ・既存 def/hyp/補題は不変、averaged Kraft 下界 +
                                    ergodic lift + isLZ78ConverseCodingLowerBound_distinct を追記
  LZ78AchievabilityLimsup.lean  ← (拡張) 無仮定 headline lz78_two_sided_optimality_distinct (Phase V)
  InformationTheory.lean               ← import 1–2 行追記
```

> **設計判断: kernel 層は 1 新規 file `StationaryKernel.lean` に隔離**。Ch.4 core file
> (Stationary/EntropyRate/SMB) には触れない。Z/C primitive instance は既存 file の拡張
> (既存 def 不変)。これにより blast radius が「新規 1 file + 既存 file への追記のみ」に閉じ、
> Ch.4 publish 済定理の再証明をゼロにできる (Phase R は再検証のみ)。

---

## blast radius (最重要報告事項)

**判定: refactor は Ch.4 を壊さず additive に可能。** 根拠は以下の全数確認:

### `StationaryProcess`/`ErgodicProcess` の利用箇所と種別

`rg "blockRV|StationaryProcess|ErgodicProcess"` で InformationTheory 全体を走査した結果:

| file | 利用形 | 種別 |
|---|---|---|
| `Stationary.lean` | 定義元 | 改変しない |
| `EntropyRate.lean` | `(p : StationaryProcess μ α)` consumer。`blockRV`/`obs`/`measurable_blockRV` を read-only。`entropyRate_eq_lim_condEntropy` (`:85`) は `blockRV (n+1)` の射影分解に依存 | **read-only consumer** |
| `ShannonMcMillanBreiman.lean` | `blockLogAvg` def が `blockRV` を read-only 消費 | read-only consumer |
| `SMBAlgoetCover.lean` / `SMBChainRule.lean` | `(p : StationaryProcess/ErgodicProcess)` consumer | read-only consumer |
| `TwoSidedExtension.lean` | `(p : StationaryProcess μ α)` consumer (~10 箇所、すべて変数) | read-only consumer |
| LZ78 系 (14 file) | すべて `(p : ...)` consumer | read-only consumer |

### コンストラクションサイト (refactor で壊れる候補) — **ゼロ**

`rg "StationaryProcess.mk|ErgodicProcess.mk|: StationaryProcess μ α :=|ergodic :="` の結果、
**InformationTheory 内に `StationaryProcess`/`ErgodicProcess` の anonymous constructor / `.mk` /
全 field 供給サイトは存在しない**。唯一ヒットした `TwoSidedExtension.lean:959` は
`set q : StationaryProcess μ α := p.toStationaryProcess` で、これは **既存 process の別名束縛**で
あり構築ではない。

→ **`StationaryProcess` に新 field を追加しても、それを供給する箇所が無いため既存ファイルは
コンパイル上壊れない** (consumer は新 field を無視できる)。さらに本 plan は **field 追加すらせず
別構造 `KernelStationaryProcess` を新設** (案 K1-β) するので、`StationaryProcess` の定義は
バイト単位で不変。Ch.4 の全 consumer は型レベルで完全に無傷。

### additive 判定の結論

- **新規 `StationaryKernel.lean` 1 file**: kernel 層を隔離。Ch.4 core に import されない (Ch.4 が
  kernel 層に依存しない)。逆依存方向 (kernel 層が Ch.4 を import) なので循環なし。
- **既存 file への追記**: Z/C primitive instance は `LZ78ZivEntropyBridge`/`LZ78ConverseKraft` の
  末尾に追記、既存 def/hyp/補題は不変。`LZ78AchievabilityLimsup` の headline 追記も既存定理不変。
- **再証明が要る既存定理: ゼロ**。Phase R は `lake env lean` / `lake build` での非破壊**再検証**のみ。

---

## Phase 0 — 在庫調査 (kernel/disintegration 前提 + blast radius 全数確定) 📋

**proof-log: no。新規 `lz78-blockrv-refactor-inventory.md` を起草。**

- [ ] **kernel/compProd/disintegration API の typeclass 前提を verbatim 確認** (CLAUDE.md「Subagent
      Inventory」基準: `file:line` + 完全 signature + `[...]` 前提 + conclusion form verbatim):
  - `Measure.compProd` (`Kernel/Composition/MeasureCompProd.lean`)、`compProd_apply`
    (`:61`、`(μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ`、前提 `[SFinite μ] [IsSFiniteKernel κ]`)、
    `compProd_apply_prod` (`:69`)、`lintegral_compProd`。
  - `Measure.condKernel` / `Measure.compProd_fst_condKernel` (`Kernel/Disintegration/StandardBorel.lean:64`、
    `ρ.fst ⊗ₘ ρ.condKernel = ρ`)。**`[StandardBorelSpace]` 前提を verbatim** で記録し、
    `Fin n → α` (finite alphabet) で自動 derive されるか instance 探索で確認 (`StandardBorelSpace`
    of finite / countable discrete)。
  - `ProbabilityTheory.Kernel` の基本 (`IsMarkovKernel`/`IsSFiniteKernel` instance 要件)。
  - `eq_condKernel_of_measure_eq_compProd` 系 (`Kernel/Disintegration/Unique.lean`) — 一意性で
    process の条件付き法則 = condKernel を同定できるか (K2 の telescoping で stationarity を使う橋)。
- [ ] **blockRV 射影性の再確認** (`Stationary.lean:81`): `blockRV p n = fun ω i => p.obs i ω`。
      compProd / kernel 構造が無いことを再確認 → kernel 層を additive 注入する経路 (a) 変種を確定。
- [ ] **2 primitive の structure body verbatim** (Phase Z/C の target):
  - `IsLZ78AchievabilityZivUpperBound` (`LZ78AchievabilityLimsup.lean:102`、field `upper`:
    `∀ᵐ ω, ∀ᶠ n, lz/n ≤ blockLogAvg + slack n` + `slack_tendsto`)。
  - `IsLZ78ConverseCodingLowerBound` (`LZ78ConverseKraft.lean:106`、field `lower`:
    `∀ᵐ ω, ∀ᶠ n, blockLogAvg - slack n ≤ lz/n` + `slack_tendsto`)。
- [ ] **factorization 足場の body verbatim** (Phase K3 の target):
  - `IsLZ78PerPathParsingFactorization` (`LZ78ZivEntropyBridge.lean:179`、`factor` + `pos`)、
    `condPhraseProb` (`:158`)、`prefixBlockProb` (`:141`)、`parsingBoundary` (`:133`)。
- [ ] **Kraft 資産の full-support hyp** (Phase C):
  - `entropyD_le_expectedLength_of_kraft` (`ShannonCode.lean:164`、expectation-level + `hP : ∀ a, 0 < P.real {a}`)、
    `shannonLength_kraft_le_one` (`:129`)、`rpow_neg_shannonLength_le_real` (`:106`)、
    `kraftSum`/`expectedLength` def (`:59,:55`)。**converse は averaged Kraft → ergodic lift 一択**
    (pointwise Shannon-code 経路は不健全、`LZ78ConverseKraft.lean:103-105` 確認済)。
- [ ] **ergodic theorem (Birkhoff) 資産** (Phase C の a.s. lift):
  - `BirkhoffErgodic.lean` の Birkhoff 主定理 / `shannon_mcmillan_breiman` (`SMBAlgoetCover.lean`) の
    a.s. convergence。expectation → a.s. eventual の lift にどれを使うか確認。
- [ ] **blast radius 全数確認 (本 plan §blast radius を裏取り)**: コンストラクションサイト ゼロ、
      全 consumer が read-only であることを `rg` で再確認、新 file の import 方向に循環が無いこと。
- [ ] **既存 counting/encoding genuine 資産の reuse 形** (Phase Z 黒箱 reuse):
  - `lz78PhraseStrings_mul_log_le` (`LZ78ZivCountingBody.lean:353`)、`card_phraseSet_le_pow`
    (`LZ78ZivInequality.lean:204`)、`lz78DistinctEncodingLength_eq` (`LZ78DistinctEncoding.lean:133`)、
    counting envelope (`LZ78ZivCountingBody.lean:405`)、`log_sum_inequality`/`blockProb_neg_log_eq_sum`
    (`LZ78ZivEntropyBridge.lean:63,:206`)。

### Done 条件

- kernel/disintegration API の typeclass 前提が verbatim 記録済 (特に `[StandardBorelSpace]` の
  finite-alphabet 自動 derive 可否)
- 2 primitive + factorization 足場 + Kraft + Birkhoff の signature 確認済
- blast radius §が `rg` で裏取り済 (コンストラクションサイト ゼロ確認)
- Phase K1 skeleton (~80 行) を inventory に書き出し済

---

## Phase K1 — kernel 層 設計確定 + skeleton 📋

**proof-log: no。skeleton-driven (CLAUDE.md)。**

- [ ] **案 K1-α (typeclass) vs K1-β (別構造) を Phase 0 結果で確定**。第一候補 K1-β (別構造、
      `StationaryProcess` 完全不変、blast radius 最小)。判断ログに記録。
- [ ] **kernel field の結論形を Mathlib-shape-driven で固定**: `Measure.compProd_apply` /
      `lintegral_compProd` の conclusion (`∫⁻ a, κ a (...) ∂μ`) に合わせる。`condPhraseProb`
      (= prefix block prob の ratio) と整合する telescoping 形を決める。
- [ ] **新規 `StationaryKernel.lean` skeleton**: imports (pinpoint、`Mathlib.Probability.Kernel.*` +
      `InformationTheory.Shannon.Stationary` + `ShannonMcMillanBreiman` + `LZ78ZivEntropyBridge`)、namespace、
      variable、全 def/定理を `:= by sorry` で stub:
  - `KernelStationaryProcess` (or `class HasTransitionKernel`) — kernel field + compatibility field。
  - `kernelStationaryProcess_of_ergodic` (ergodic + finite → kernel 層 実例、K2 前半)。
  - `blockProb_eq_prod_telescope` (kernel から factorization、K2 後半)。
  - `isLZ78PerPathParsingFactorization_of_kernel` (K3)。
- [ ] **検証**: `lake env lean InformationTheory/Shannon/StationaryKernel.lean` が sorry warning のみ。
- **撤退ライン**: なし (skeleton のみ)。

---

## Phase K2 — ergodic→kernel 実例 + telescoping factorization 📋

**proof-log: yes。本 plan の最大の数学的負荷。撤退ライン L-K の判定点。**

- [ ] **K2-a (実例構成、★crux)**: ergodic + finite alphabet **だけ**から kernel 層 (transition
      kernel + compatibility) を genuine 構成。finite-alphabet では `μ.map (blockRV n)` が
      `Fin n → α` 上の有限台 measure であり、disintegration が `[StandardBorelSpace (Fin n → α)]`
      (finite ⟹ 自動) で成立する見込み。**stationarity (`identDistrib_obs_zero` `Stationary.lean:94`)
      が条件付き kernel を shift-invariant に固定する**ことを使い、`compProd_fst_condKernel` の
      condKernel を process の条件付き法則に同定 (`eq_condKernel_of_measure_eq_compProd` 系)。
- [ ] **K2-b (telescoping)**: `Pₙ{x} = (μ.map (blockRV n)).real {x}` を K2-a の kernel で
      `Pₙ{x} = ∏ⱼ qⱼ` に開く。`compProd_apply` を逐次適用、singleton `{x}` を prefix が一致する
      cylinder の交わりで分解。結論形を `condPhraseProb` (`LZ78ZivEntropyBridge.lean:158`、prefix
      block prob ratio) と一致させる (Mathlib-shape-driven)。
- [ ] zero-mass edge: 未出現 prefix で `qⱼ = 0` → `Pₙ{x} = 0`、`log 0 = 0` 規約。`n = 0` edge も special-case。
- **依存補題**: `Measure.compProd_apply` (`:61`), `lintegral_compProd`, `compProd_fst_condKernel`
      (`StandardBorel.lean:64`), `eq_condKernel_of_measure_eq_compProd` (`Unique.lean`),
      `identDistrib_obs_zero` (`Stationary.lean:94`), `Measure.map_apply`, `Measure.real` 有限加法性。
- **proof-log: yes** — 実例構成の経路 (disintegration の condKernel を stationarity で同定)、
      telescoping の集合分解、zero-mass branch、`[StandardBorelSpace]` の解決を記録。
- **撤退ライン [L-K、最重要]**: K2-a の実例構成が `~1 セッション / ~400 行`で閉じない、または
      `[StandardBorelSpace (Fin n → α)]` の自動 derive / disintegration 一意性で詰まる場合:
      **`IsLZ78PerPathParsingFactorization` を isolated honest hyp として残す** (現状の足場
      `LZ78ZivEntropyBridge.lean:179` のまま、明示 signature、型 ≠ 結論、docstring で「kernel 層
      未構成、load-bearing」明示)。この場合 Phase K3 は skip、Phase Z は factorization を hyp で受ける。
      **`sorry` / `:True` / `:= h` 循環は使わない**。これは現状 (per-path primitive 2 本) を
      factorization 1 本 + converse 1 本に組み替えた **より primitive な deferral** (achievability
      側のみ完全前進)。

---

## Phase K3 — `IsLZ78PerPathParsingFactorization.factor`/`pos` を K2 から供給 📋

**proof-log: yes。**

- [ ] **target**: `isLZ78PerPathParsingFactorization_of_kernel` — K2 の `blockProb_eq_prod_telescope`
      から、既存 `IsLZ78PerPathParsingFactorization` (`LZ78ZivEntropyBridge.lean:179`) の `factor`
      field (`Pₙ{x} = ∏ⱼ condPhraseProb ...`) と `pos` field (各因子 > 0) を genuine に供給。
- [ ] `factor`: K2-b の telescoping を `condPhraseProb` の def (`:158`) と照合し rw。
- [ ] `pos`: 出現 prefix で各 ratio `qⱼ > 0` (full-support / a.s. の範疇)。未出現 branch の扱いを
      `IsLZ78PerPathParsingFactorization.pos` の要求形 (phrase position 上で > 0) に合わせる。
- **依存補題**: K2 `blockProb_eq_prod_telescope`, `condPhraseProb`/`prefixBlockProb` def, `parsingBoundary`。
- **proof-log: yes** — factor の rw 経路、pos の出現 branch 限定を記録。
- **撤退ライン**: K2 が L-K で honest 化された場合は本 Phase skip (factorization が hyp のまま)。

---

## Phase Z — achievability primitive `IsLZ78AchievabilityZivUpperBound` を genuine 構成 📋

**proof-log: yes。`LZ78ZivEntropyBridge.lean` を拡張 (既存 def/hyp/補題不変)。**

- [ ] **Z-a per-path Ziv `ziv_per_path_mul_log_le`**: `c·log c ≤ -log Pₙ{x}`
      (`c := (lz78PhraseStrings (List.ofFn x)).length`)。K3 factorization で
      `-log Pₙ{x} = Σⱼ -log qⱼ` (既存 `blockProb_neg_log_eq_sum` `:206` 経由) → 既存 log-sum
      (`log_sum_inequality` `:63`) を `aₖ ≡ 1` / `bₖ ≡ qⱼ` で適用 → `c·log c ≤ -Σⱼ log qⱼ`。
      項数縛りは既存 genuine `card_phraseSet_le_pow` (`LZ78ZivInequality.lean:204`) 黒箱 reuse。
- [ ] **Z-b per-symbol bridge + slack**: `lz78DistinctEncodingLength_eq` (`:133`、`lz n x = c·bitLength`)、
      `bitLength ≈ log₂ c + O(log|α|)` (`bitLength_eq` 上界) → `(lz n x)/n ≤ C·(c log c)/n + o(1)`、
      Z-a + `blockLogAvg_eq_neg_log_blockProb` (`:117`) で `≤ blockLogAvg + slack n`。
      `slack n` を明示構成 (`c = O(n/log n)` envelope `LZ78ZivCountingBody.lean:405` で余剰項 → 0)、
      `slack_tendsto` を genuine に。
- [ ] **target**: `isLZ78AchievabilityZivUpperBound_distinct μ p slack :
      IsLZ78AchievabilityZivUpperBound μ p.toStationaryProcess (@lz78DistinctEncodingLength α _ _ _) slack`。
- **依存補題**: K3 factorization, `blockProb_neg_log_eq_sum` (`:206`), `log_sum_inequality` (`:63`),
      `blockLogAvg_eq_neg_log_blockProb` (`:117`), `card_phraseSet_le_pow` (`:204`),
      `lz78DistinctEncodingLength_eq` (`:133`), counting envelope (`:405`), `bitLength` 上界。
- **proof-log: yes** — log-sum の weight 選択、slack の明示構成 + Tendsto、edge case を記録。
- **撤退ライン**: log-sum の weight 設計が合わなければ uniform-distribution 版で再構成。
      K2 が L-K で honest 化された場合は本 Phase は factorization hyp を受けて残りは genuine。

---

## Phase C — converse primitive `IsLZ78ConverseCodingLowerBound` を genuine 構成 📋

**proof-log: yes。`LZ78ConverseKraft.lean` を拡張 (既存 def/hyp/補題不変)。**

> **honesty 注記**: per-path lower bound は pointwise には偽 (`LZ78ConverseKraft.lean:30-40`)。
> 正しい経路は **expectation-level の averaged coding 下界 → ergodic theorem で a.s. eventual 化**。
> pointwise Shannon-code 経路 (`2^{-lz} ≤ Pₙ`) は不健全につき**採らない**。

- [ ] **C-a expectation-level Kraft 下界**: distinct LZ78 が prefix code (uniquely decodable、
      `lz78PhraseStrings_nodup` `LZ78GreedyLongestPrefix.lean:126` の延長で block レベル単射 +
      prefix-free) → block pushforward `Pₙ = μ.map (blockRV n)` 上で
      `entropyD_le_expectedLength_of_kraft` (`ShannonCode.lean:164`) 系を適用し
      `entropyD Pₙ ≤ expectedLength Pₙ lz` (= `𝔼[blockLogAvg]·n ≤ 𝔼[lz]` の coding 下界)。
      full-support hyp `0 < Pₙ.real {x}` は a.s. (出現 block) で扱う = regularity 範疇。
- [ ] **C-b ergodic a.s. lift**: expectation-level 下界を Birkhoff / SMB の a.s. convergence で
      per-realization eventual `blockLogAvg n ω - slack n ≤ lz/n` に持ち上げ。`slack n` を明示構成
      (Kraft の O(1) overhead + counting envelope)、`slack_tendsto` genuine。**ここが converse の crux**:
      averaged 不等式から a.s. eventual を出すのに ergodicity (Birkhoff) を使う Cover–Thomas 13.130 の
      論証を formalize。
- [ ] **target**: `isLZ78ConverseCodingLowerBound_distinct μ p slack :
      IsLZ78ConverseCodingLowerBound μ p.toStationaryProcess (@lz78DistinctEncodingLength α _ _ _) slack`。
- **依存補題**: `entropyD_le_expectedLength_of_kraft` (`:164`), `kraftSum`/`expectedLength` def
      (`:59,:55`), `lz78PhraseStrings_nodup` (`:126`), `lz78DistinctEncodingLength_eq` (`:133`),
      Birkhoff (`BirkhoffErgodic.lean`) / `shannon_mcmillan_breiman`, counting envelope (`:405`)。
- **proof-log: yes** — averaged Kraft の prefix-free 出所、ergodic lift の Birkhoff 補題選択、
      full-support の a.s. 回避、slack の明示構成を記録。
- **撤退ライン [L-C]**: averaged Kraft → a.s. lift が `~1 セッション / ~400 行`で閉じない場合、
      **`IsLZ78ConverseCodingLowerBound` を isolated honest hyp として残す** (現状の足場
      `LZ78ConverseKraft.lean:106` のまま、明示 signature、docstring で load-bearing 明示)。
      この場合でも achievability (Phase Z) が genuine に閉じれば headline の honest 入力は 2→1。
      `:True` / `:= h` 循環は使わない。

---

## Phase R — Ch.4 既存定理 全数再検証 (refactor 非破壊確認) 📋

**proof-log: no。新規証明なし、非破壊の再検証のみ。**

- [ ] **Ch.4 core file の再検証**: `lake env lean` で以下が clean (silent):
      `Stationary.lean` (定義不変なので変化なしのはず)、`EntropyRate.lean`、`ShannonMcMillanBreiman.lean`、
      `SMBAlgoetCover.lean`、`SMBChainRule.lean`、`BirkhoffErgodic.lean`、`TwoSidedExtension.lean`。
- [ ] **LZ78 系の再検証**: `LZ78ZivEntropyBridge.lean`、`LZ78ConverseKraft.lean`、
      `LZ78AchievabilityLimsup.lean`、`LZ78DistinctEncoding.lean` が clean。
- [ ] **olean refresh**: 新 public symbol を下流が拾うなら `lake build InformationTheory.Shannon.StationaryKernel`
      一回 (CLAUDE.md「After upstream edits」)。
- [ ] **signature 無変更の横断確認**: 既存 genuine 補題 (`blockRV`/`blockLogAvg`/`entropyRate`/
      `shannon_mcmillan_breiman`/`card_phraseSet_le_pow`/`lz78DistinctEncodingLength_eq`/Kraft 資産/
      2 primitive structure) の signature を `rg` で無変更確認 (新規追加のみ)。
- **Done 条件**: Ch.4 + LZ78 全 file が `lake env lean` clean、既存 signature 無変更、新規証明ゼロ。

---

## Phase V — 無仮定 headline publish + `InformationTheory.lean` 編入 + clean check 📋

**proof-log: no。**

- [ ] **無仮定 headline publish**: `lz78_two_sided_optimality_distinct` を
      `lz78_two_sided_optimality_distinct_genuine μ p slackUp slackLow
        (isLZ78AchievabilityZivUpperBound_distinct μ p slackUp)
        (isLZ78ConverseCodingLowerBound_distinct μ p slackLow)` で publish。**既存
      `..._genuine`/`..._bdd_free`/`..._converse_discharged` は signature 不変で残す**。
- [ ] **段階着地時**: 片方の primitive のみ genuine の場合、残った honest 入力を正直に明記した
      中間 headline (例: `..._achiev_genuine` / `..._converse_hyp_only`) を publish。
      L-K 発動 (factorization が honest) でも achievability が通れば achiev 側は前進固定。
- [ ] **`InformationTheory.lean` 編入**: `import InformationTheory.Shannon.StationaryKernel` を `Stationary` import の後ろ、
      LZ78 系 import の前に追記。
- [ ] **検証**: `lake env lean InformationTheory/Shannon/StationaryKernel.lean` /
      `LZ78ZivEntropyBridge.lean` / `LZ78ConverseKraft.lean` / `LZ78AchievabilityLimsup.lean` が
      silent (0 error / 0 sorry / 0 warning)。最後に **`lake build`** で project-wide sanity check
      (大規模 refactor 後の一回限り、CLAUDE.md 準拠)。
- [ ] **`#print axioms lz78_two_sided_optimality_distinct`** で `sorryAx` が無いことを確認
      (標準B 検証、honest hyp が残る場合はそれが axioms ではなく hypothesis であることを確認)。
- [ ] **roadmap 更新**: `docs/textbook-roadmap.md` Ch.13 行 / Tier 4 T4-A カードを更新
      (genuine 完遂 or 2→1 前進を反映)。

---

## 撤退ライン (本 plan)

各 Phase は **独立撤退可能**。撤退時も honest 限定 (名前付き仮説、型 ≠ 結論、docstring で
load-bearing 明示)。`:True` / 結論同型述語への `:= h` 循環 / `sorry` は **禁止** (CLAUDE.md
「検証の誠実性」)。

| ID | 対象 | 発動条件 | 撤退後の着地 |
|---|---|---|---|
| **L-K (最重要)** | kernel 層 実例構成 (Phase K2-a) | ergodic→kernel が >400 行、または `[StandardBorelSpace]` 自動 derive / disintegration 一意性で詰まる | `IsLZ78PerPathParsingFactorization` を isolated honest hyp で残す (既存足場のまま)。achiev 側 (Phase Z) は factorization hyp を受けて残り genuine。現状 2 primitive → factorization 1 + converse 1 のより primitive な deferral |
| **L-C** | converse averaged Kraft → ergodic lift (Phase C-b) | a.s. lift が >400 行で閉じない | `IsLZ78ConverseCodingLowerBound` を isolated honest hyp で残す (既存足場 `LZ78ConverseKraft.lean:106`)。achiev が通れば headline honest 入力 2→1 |
| **L-K1** | kernel 層 設計 (Phase K1) | 案 K1-β (別構造) が `condPhraseProb` の既存 def と噛み合わない | 案 K1-α (typeclass) に切替。それでも噛み合わなければ `condPhraseProb` を再 def (Mathlib-shape-driven、ただし `IsLZ78PerPathParsingFactorization` の body 整合を保つ) |

**all-or-nothing 注記**: 2 primitive は独立 (achiev = factorization 経由、converse = averaged Kraft
+ ergodic 経由、共有 crux なし)。**achiev 群 (K1→K2→K3→Z) が genuine になれば `h_ub` が flip、
converse 群 (C) が genuine になれば `h_lb` が flip**。片方だけでも honest 入力数を 2→1 に減らせる。
両方 genuine で完全 hypothesis-free headline (標準B 完遂)。L-K / L-C 発動時は当該 1 述語が isolated
honest 入力として明示的に残る (現状より primitive な deferral だが完全 discharge ではない)。

> **撤退の優先順位の助言**: kernel 層 (Phase K) は両 primitive の crux のうち achievability 側に
> 直結し、blast radius が新規 1 file に隔離されるので **achievability 群を先行**するのが ROI 高。
> converse 群 (Phase C) は ergodic lift が独立に重く、Birkhoff の formalize 負荷が読めない場合は
> L-C 発動で achiev 完遂 (2→1) を確定させるのが堅実。

---

## 検証 (Done 条件)

標準B (無条件機械検証)。

- **inner loop**: 各 fill 後 `lake env lean InformationTheory/Shannon/<file>.lean` が silent (CLAUDE.md
  「Primary」)。`StationaryKernel.lean` / `LZ78ZivEntropyBridge.lean` / `LZ78ConverseKraft.lean` /
  `LZ78AchievabilityLimsup.lean` の 4 file。
- **project-wide**: 大規模 refactor 完了後に **`lake build`** 一回 (Phase R + Phase V、
  Ch.4 publish 済定理の非破壊確認)。inner loop には使わない。
- **axiom check**: `#print axioms lz78_two_sided_optimality_distinct` で `sorryAx` 不在。
  honest hyp が残る場合 (L-K / L-C 発動) は、それが axioms ではなく明示 hypothesis であることを確認
  (= 主定理が hyp を引数で受ける形)。
- **honesty 監査**: 完了時、新規追加した述語/補題に `:True` / `:= h` 循環 / `*_discharged` name
  laundering / 退化定義悪用が無いことを自己点検。kernel 層 compatibility が「ergodic から genuine
  構成」されたか「公理的に仮定しただけ」かを判定 (後者は L-K の honest hyp 扱い)。

---

## 当面の next step

1. **Phase 0** 在庫調査 (`lz78-blockrv-refactor-inventory.md` 起草)。最重要確認:
   `[StandardBorelSpace (Fin n → α)]` の finite-alphabet 自動 derive 可否、disintegration 一意性
   (`eq_condKernel_of_measure_eq_compProd`) で stationarity を kernel に同定できるか、blast radius
   コンストラクションサイト ゼロの裏取り。
2. **Phase K1** kernel 層 設計確定 (案 K1-β 別構造 第一候補) + `StationaryKernel.lean` skeleton。
3. **Phase K2** ergodic→kernel 実例 (★crux、L-K 判定点) → ~400 行 / 1 セッションで判定 →
   閉じなければ L-K (isolated honest hyp) 発動。
4. **Phase K3 → Z** factorization 供給 → achievability primitive genuine 構成 (achiev 群完遂)。
5. **Phase C** converse averaged Kraft + ergodic lift (独立、L-C 判定)。
6. **Phase R** Ch.4 全数再検証 → **Phase V** 無仮定 headline publish + `lake build` + axiom check。

**並行実行の余地**: achiev 群 (K1–K3, Z) と converse 群 (C) は別 crux・別 file なので並列 agent で
同時着手可。ただし両群とも Ch.4 の同じ kernel/ergodic 基盤に触れる可能性があるため、Phase 0 の
blast radius 確定後に分岐するのが安全。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 起草時点の確定事項 (実装中の方針変更があればここに追記):

1. **(2026-05-21) factorization 経路は (a) 変種 (kernel 層 additive 注入) を採用** — 経路 (b)
   disintegration 単独は不採用 (Mathlib `compProd_fst_condKernel` は任意 measure の Bayes 分解で、
   stationary process の条件付き法則と一致する保証が無い = Cover–Thomas の中身を与えない)。
   経路 (c) 純組合せは不採用 (`-log Pₙ` の積分解が論理的に不可避、既存 counting は定数 rate K への
   bound で limsup blockLogAvg ではない)。disintegration は経路 (a) の道具として併用。

2. **(2026-05-21) blast radius 判定: additive で Ch.4 非破壊と確定** — `rg` 全数確認で
   `StationaryProcess`/`ErgodicProcess` の anonymous constructor / `.mk` / 全 field 供給サイトが
   InformationTheory 内にゼロ (唯一のヒット `TwoSidedExtension.lean:959` は別名束縛で構築ではない)。
   全 consumer が read-only。よって新 field 追加でも既存は壊れないが、本 plan は更に保守的に
   **別構造 `KernelStationaryProcess` を新規 file `StationaryKernel.lean` に隔離** (案 K1-β)、
   `StationaryProcess` 定義をバイト単位で不変に保つ。Ch.4 再証明ゼロ、Phase R は再検証のみ。

3. **(2026-05-21) converse は averaged Kraft + ergodic lift 一択** — pointwise Shannon-code 経路
   (`2^{-lz} ≤ Pₙ`) は LZ78 universality ゆえ per-path で偽 (`LZ78ConverseKraft.lean:30-40,103-105`
   が明記)。`lz78-residual-discharge-plan.md` Phase C3 の当該経路を本 plan は採らない (supersede)。
   expectation-level `entropyD_le_expectedLength_of_kraft` を block pushforward に適用 → Birkhoff で
   a.s. eventual 化が genuine 経路。

4. **(2026-05-21) factorization 足場は既存 (LZ78ZivEntropyBridge.lean) を流用** — `condPhraseProb`
   (`:158`) / `IsLZ78PerPathParsingFactorization` (`:179`) / `blockProb_neg_log_eq_sum` (`:206`) は
   既に存在し genuine (log_prod 経由)。Z-side の真の残作業は `factor`/`pos` の **proving** のみ。
   述語定義は変えない (Mathlib-shape-driven、結論側不変)。

5. **(2026-05-21) honesty 最重要ライン: kernel compatibility を「仮定だけ」にしない** — ergodic +
   finite alphabet から kernel 層を genuine 構成 (Phase K2-a) しないと name laundering になる。
   構成できなければ L-K で `IsLZ78PerPathParsingFactorization` を isolated honest hyp に留める
   (現状より primitive な deferral、achiev 側のみ前進固定)。「その仮説は前提条件か証明の核心か」=
   kernel compatibility は核心 → 構成必須、構成不能なら honest hyp として明示。
-->

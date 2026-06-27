# Stam 不等式 + de Bruijn 恒等式 + Fisher 情報 — standalone genuine 完成 ムーンショット計画 🌙

> **関連 SoT**: [`ch17-inequalities-status.md`](ch17-inequalities-status.md)（Ch.17 状態の SoT）、コード内 `@audit:*` / `@residual` タグ（最終 SoT、`docs/audit/audit-tags.md`）。
> **隣接 plan（重複起草しない）**: [`epi-blachman-general-density-plan.md`](epi-blachman-general-density-plan.md)（producer 層）、[`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md)（Stam→EPI、CLOSED）、[`epi-debruijn-pertime-closure-plan.md`](epi-debruijn-pertime-closure-plan.md)（per-time de Bruijn）。
> **位置付け**: 本 plan は EPI の無条件化路ではなく、Cover-Thomas Ch.17.7 の **Fisher 情報路の主結果そのもの**を、散在した conditional 部品から **clean な standalone genuine 定理**として組み上げ、かつ **非空虚性（規則性バンドルが Gaussian 以外でも discharge 可能であること）を担保**する。

## 進捗

- [ ] Phase M0 — 在庫確認 + 配線マップ 📋 → [stam-debruijn-standalone-mathlib-inventory.md](stam-debruijn-standalone-mathlib-inventory.md)
- [ ] Phase 1 — Fisher 基本性質 audit + smoothed-density Fisher 正値性 producer 📋
- [ ] Phase 2 — Stam standalone headline（H1、非空虚 instantiation）📋
- [ ] Phase 3 — de Bruijn per-time standalone headline（H2a、再 export + 非空虚 witness）📋
- [ ] Phase 4 — de Bruijn integration (path) producer + 非空虚化（H2b、唯一の実質フロンティア）📋
- [ ] Phase 5 — headline 配線（`InformationTheory.lean` / README）+ 独立 honesty audit 📋

## ゴール / Approach

### ゴール（完遂条件）

Cover-Thomas Ch.17.7 の 3 主結果を、**規則性バンドルを呼出側に押し付けない standalone genuine 定理**として publish し、proof done（sorryAx-free + `@audit:ok`）にする:

1. **Stam の不等式**（CT Lemma 17.7.2 / Blachman 1965）: `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)`（調和平均形）。
2. **de Bruijn 恒等式**（CT Thm 17.7.2）: `(d/dt) h(X+√t·Z) = (1/2)·J(X+√t·Z)`（per-time）+ 積分形。
3. **Fisher 情報の基本性質**（Gaussian 閉形 `J(𝒩(m,v)) = 1/v` 等）— 既存で足りるか確認。

### Approach（解の全体形）

**重要な事実: 解析核はすべて既存・genuine・sorryAx-free。本ムーンショットの本体は (A) 組み上げと (B) 非空虚性の担保**であり、新規の analytic 証明はほぼ Phase 4（de Bruijn 積分形の path-regularity 生成）の 1 点に局在する。以下、verbatim 確認済みの根拠とともに戦略を述べる。

**(A) 既に genuine な部品（verbatim 確認済、すべて `@audit:ok`）**

| 役割 | decl（file:line） | 入力 | 結論 |
|---|---|---|---|
| Stam 解析核 | `StamInequality.stam_step2_density_wall`（`EPI/Stam/Inequality.lean:247`） | `Measurable X/Y`, `IndepFun X Y P`, `[IsProbabilityMeasure P]` のみ | `IsStamCauchySchwarzOptimal X Y P` |
| Stam（primitives 版） | `FisherInfo.isStamInequalityHyp_of_primitives`（`EPI/Stam/DeBruijnConclusion.lean:158`） | 同上 | `IsStamInequalityHyp X Y P`（sorryAx-free、ch17-status §54） |
| 凸 Fisher 上界 | `EPIBlachmanDensity.convex_fisher_bound_of_ready`（`EPI/Blachman/Density.lean:833`） | regularity + `IsBlachmanConvReady fX fY` | `J(p_Z).toReal ≤ λ²J(fX)+(1-λ)²J(fY)` |
| λ 最適化 | `StamInequality.stam_lambda_min`（`Inequality.lean:161`） | — | 調和平均 RHS |
| 逆形整形 | `StamInequality.stam_inverse_form_of_harmonic_mean`（`Inequality.lean:192`） | `J_sum ≤ J_X J_Y/(J_X+J_Y)` | `1/J_sum ≥ 1/J_X + 1/J_Y` |
| Fisher Gaussian 閉形 | `FisherInfo.fisherInfoOfDensity_gaussianPDFReal`（`FisherInfo/OfDensity.lean:192`） | `v ≠ 0` | `= ENNReal.ofReal (1/v)`（実数版 `fisherInfoOfDensityReal_gaussianPDFReal:226` = `1/v`） |
| de Bruijn per-time | `FisherInfo.deBruijn_identity_v2`（`FisherInfo/DeBruijnGeneral.lean:36`） | `IsRegularDeBruijnHypV2 X Z P t` | `HasDerivAt (h(X+√s·Z)) ((1/2)·J(...)) t` |
| de Bruijn per-time（clean-hyp 版） | `FisherInfo.deBruijn_identity_v2_of_heat_flow`（`FisherInfo/DeBruijnHeatFlow.lean:225`） | `(P.map X)≪volume`, `Integrable(X²) P`, `IsHeatFlowDensity` | 同上 |
| de Bruijn 積分形 | `FisherInfo.debruijnIntegrationIdentity_holds`（`DeBruijnGeneral.lean:53`） | `IsDeBruijnPathRegular X Z P T` | FTC 積分恒等式 |

**(B) 非空虚性 — 最重要の honesty 判定（verbatim 確認済）**

`IsStamInequalityHyp` / `IsBlachmanConvReady` / `IsRegularDeBruijnHypV2` 等は規則性バンドルに条件付き。これが Gaussian 以外で discharge できなければ Stam は等号ケースのみで事実上空虚 = honesty 重大欠陥。**結論: Stam・de Bruijn per-time は非空虚（一般 producer 既存）。de Bruijn 積分形のみ非空虚性に gap がある。**

- **Stam バンドル discharge は GENERAL（Gaussian 限定でない）**:
  - `EPIBlachmanGeneralDensity.isBlachmanConvReady_convDensityAdd_gaussian`（`EPI/Blachman/GeneralDensity.lean:605`、**19/19 field genuine, `@audit:ok`**）: **任意の確率密度** `pX, pY`（非負・可測・可積分・mass>0・∫=1）と `t>0` に対し `IsBlachmanConvReady (convDensityAdd pX g_t) (convDensityAdd pY g_t)` を構成。
  - `EPIConvDensityRegular.isRegularDensityV2_convDensityAdd_gaussian`（`EPI/Conv/DensityRegular.lean`）: 同じ smoothed 形に `IsRegularDensityV2` を供給（6 field genuine、tail も DCT 閉鎖）。
  - `EPIConvDensityNormalization.integral_convDensityAdd_gaussian_eq_one`: `∫ (pX∗g_t) = 1`。
  - ⟹ **非空虚な具体クラス = Gaussian-smoothed 密度 `pX ∗ g_t`（t>0、pX は任意の確率密度）**。これはすべての heat-flow 平滑化分布を含む広い非自明クラスであり、Gaussian 等号ケースに限定されない。**Stam の非空虚性は確定。**
- **de Bruijn per-time も非空虚（一般 a.c.）**: `IsRegularDeBruijnHypV2.ofHeatFlow`（`DeBruijnHeatFlow.lean:159`）が `(P.map X)≪volume` + `Integrable(X²) P` + `IsHeatFlowDensity` 証人から bundle を構成。証人は `IsHeatFlowDensity_of_sub_predicates`（`HeatFlow.lean:171`）で再組立可能。⟹ **任意の有限 2 次モーメント a.c. X で非空虚。**
- **de Bruijn 積分形 = 唯一の非空虚性 gap**: `IsDeBruijnPathRegular`（`FisherInfo/DeBruijn.lean:201`）には **inhabitant が 1 個も存在しない**（Gaussian 証人すら無い。`grep` で 0 件）。⟹ `debruijnIntegrationIdentity_holds` は現状 vacuity-risk。**Phase 4 でこの producer を新規に組む**（3 field は個別に CLOSED 機構で裏付け済 → 組み上げ + path-integrand 可積分性の小フロンティア）。

**(B') load-bearing 判定（honesty）**

- `IsStamCauchySchwarzOptimal` / `IsStamInequalityHyp` は **load-bearing でない**: `stam_step2_density_wall` / `isStamInequalityHyp_of_primitives` が primitives だけから genuine に証明（sorryAx-free、ch17-status §54 機械確認）。バンドルは precondition であって結論の核を encode していない。
- `IsBlachmanConvReady` / `IsRegularDensityV2` / `IsRegularDeBruijnHypV2` / `IsDeBruijnPathRegular` は regularity precondition（genuine producer 既存 or Phase 4 で生成）。
- ⚠ **スコープ外だが flag**: `IsDeBruijnRegularityHyp`（`EPI/Stam/EPIBridge.lean:123`、`@audit:retract-candidate(load-bearing-predicate)`、genuine `HasDerivAt` content を抱える tier-4）は **本 plan の headline chain では使わない**（EPI Case1 two-time 路の述語）。本 plan の de Bruijn は `IsRegularDeBruijnHypV2` / `IsDeBruijnPathRegular`（regularity 形）を使い、この load-bearing 述語を継承しない。混同しないこと。

**(C) 組み上げの形（Mathlib-shape-driven）**

H1 は密度レベル形を primary headline とする（`convex_fisher_bound_of_ready` の結論形 `fisherInfoOfDensity` に直結、`P.map` の measure-ignoring quirk〔`fisherInfoOfMeasureV2 μ f = fisherInfoOfDensity f` rfl〕を回避）。measure-level corollary は law-density bridge が安価なら追加。

### 規模見積りの総括

- **ほぼ「組み上げのみ」**: Phase 1（正値性、小）/ Phase 2（Stam 配線、小〜中）/ Phase 3（de Bruijn per-time 再 export、小）/ Phase 5（配線、小）。
- **実質的な新規証明が要るのは Phase 4 のみ**: de Bruijn 積分形の `IsDeBruijnPathRegular` 生成（中。ただし 3 field とも既存 CLOSED 機構で裏付けられるため、PR 級の壁ではなく assembly + path-integrand interval-integrability）。
- 本 plan は既存 shared lemma の **signature を変更しない**（新規 standalone wrapper を上に足すのみ）。よって consumer ripple は無く、`dep_consumers.sh` の事前棚卸しは不要（Phase 4 も `IsDeBruijnPathRegular` の inhabitant を作るだけで struct を変えない）。

### 最初に着手すべき Phase

**Phase M0 → Phase 1 → Phase 2**。理由: Stam の非空虚性は既に確定しているので、最大価値の headline（H1 Stam standalone）を最短で genuine に landing できる。Phase 4（唯一のフロンティア）は H1/H2a と独立に進められるので後回し可。Phase 4 の最初の一手は **gateway atom = Gaussian の `IsDeBruijnPathRegular` 証人を 1 本作る**（CLAUDE.md gateway-atom-first）。

---

## Phase M0 — 在庫確認 + 配線マップ 📋

proof-log: no（在庫は `mathlib-inventory` 担当、`docs/shannon/stam-debruijn-standalone-mathlib-inventory.md` に出力）。

本 plan の部品は大半が in-project の既存資産なので、M0 は「Mathlib 新規探索」よりも **既存 producer / bridge の verbatim 配線確認**が主。

- [ ] 上記 (A) 表の 9 decl を verbatim 再確認（signature + `#print axioms` で sorryAx-free を実測。プロセスで cache せず再導出）。
- [ ] 非空虚 producer 3 本（`isBlachmanConvReady_convDensityAdd_gaussian` / `isRegularDensityV2_convDensityAdd_gaussian` / `integral_convDensityAdd_gaussian_eq_one`）の入力前提を verbatim 列挙（型クラス括弧含む）。
- [ ] Phase 4 用: `IsDeBruijnPathRegular` の 3 field（`reg_t` / `cont` / `integrable`）それぞれに対応する既存 CLOSED 資産を同定（`ofHeatFlow` / G2 `heatFlowEntropyPower_continuousWithinAt_zero` / `gaussianConv_fisher_le_inv_var`）。path-integrand interval-integrability の Mathlib 補題候補（`ContinuousOn.intervalIntegrable` 等）を 1 本以上名指し。
- [ ] smoothed-density Fisher 正値性 `0 < (fisherInfoOfDensity (convDensityAdd pX g_t)).toReal` の既存補題有無を確認（無ければ Phase 1 で新規）。

---

## Phase 1 — Fisher 基本性質 audit + smoothed-density Fisher 正値性 📋

proof-log: no（小、既存確認 + 1 補題）。

- [ ] **H3 = 既存で足りる確認**: `fisherInfoOfDensity_gaussianPDFReal`（= `ofReal(1/v)`）/ `fisherInfoOfDensityReal_gaussianPDFReal`（= `1/v`）/ `fisherInfoOfDensity_nonneg` / `_zero` を確認。**新規不要なら H3 は audit のみで close**（結論: Fisher 基本性質は既に完備）。
- [ ] **正値性 producer**（H1/H2 の `0 < J_X` 前提に必要）: `fisherInfoOfDensity_convDensityAdd_gaussian_pos`（仮）。`pX` 確率密度・`t>0` に対し `0 < (fisherInfoOfDensity (convDensityAdd pX g_t)).toReal`。上界 `gaussianConv_fisher_le_inv_var`（`J ≤ 1/t`、fisher-finiteness CLOSED）で有限性は既知、正値性は smoothed 密度の score が a.e. 非零（密度が定数でない）から。Mathlib-shape: 上界補題の `toReal` 形に合わせる。
- 撤退ライン: 正値性が想定外に重い場合、`0 < J` を H1 の **明示 precondition** として残し、Gaussian 具体例（`J = 1/(v+t)`）で非空虚性 demo を別途付ける（バンドル化はしない。precondition のまま）。それも詰まれば body を `sorry` + `@residual(plan:stam-debruijn-standalone-moonshot-plan)`。

---

## Phase 2 — Stam standalone headline（H1）📋

proof-log: yes（honesty-critical な非空虚 instantiation。多数の precondition を thread する）。

**headline target（primary、密度レベル）**:

```
theorem stam_inequality_smoothed_density
    (pX pY : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hpX : <確率密度: 非負・可測・可積分・∫=1>) (hpY : <同>) :
    1 / (fisherInfoOfDensity (convDensityAdd fX fY)).toReal
      ≥ 1 / (fisherInfoOfDensity fX).toReal + 1 / (fisherInfoOfDensity fY).toReal
  where fX := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩),
        fY := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩)
```

配置候補: 新規 `InformationTheory/Shannon/EPI/Stam/Standalone.lean`（`StamInequality` namespace 近傍）。

- [ ] 組み上げ手順（新規 analytic 核なし、全部既存 genuine 部品）:
  1. `isRegularDensityV2_convDensityAdd_gaussian` で `IsRegularDensityV2 fX/fY`。
  2. `integral_convDensityAdd_gaussian_eq_one` で `∫ fX = ∫ fY = 1`。
  3. `isBlachmanConvReady_convDensityAdd_gaussian` で `IsBlachmanConvReady fX fY`。
  4. Phase 1 正値性で `0 < J(fX)`, `0 < J(fY)`, `0 < J(convDensityAdd fX fY)`。
  5. `convex_fisher_bound_of_ready` + `stam_lambda_min` + `stam_inverse_form_of_harmonic_mean`（または `stam_step2_density_wall` 経由）で結論。
- [ ] **measure-level corollary（optional、H1'）**: `P.map X = volume.withDensity (ofReal ∘ fX)` 形の law-density bridge が安価なら、確率変数 X, Y 版 `1/J(P.map(X+Y)) ≥ 1/J(P.map X) + 1/J(P.map Y)` を追加。bridge が重ければ scope 外（密度版で headline は十分）。
- [ ] **非空虚 demo**: Gaussian 入力 `pX = gaussianPDFReal mX vX` で具体値が出る（smoothed = `𝒩(mX, vX+t)`、`J = 1/(vX+t)`）ことをコメント or 補題で明示。
- 撤退ライン: 5 の配線で型不整合が出たら、当該 `have` を `sorry` + `@residual(plan:stam-debruijn-standalone-moonshot-plan)` で残す（**バンドル化禁止** — `IsStam*Optimal` を仮説に取り直す形に逃げない。核は既に genuine なので逃げる必要は無いはず）。

---

## Phase 3 — de Bruijn per-time standalone headline（H2a）📋

proof-log: no（大半が既存 `deBruijn_identity_v2_of_heat_flow` の再 export + 証人組立）。

**headline target**:

```
theorem debruijn_identity_per_time
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hX_ac : (P.map X) ≪ volume) (h_mom_X : Integrable (fun ω ↦ (X ω)^2) P)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal <density witness>) t
```

- [ ] `IsHeatFlowDensity_of_sub_predicates`（`HeatFlow.lean:171`）で `IsHeatFlowDensity X Z P p` 証人を組み、`deBruijn_identity_v2_of_heat_flow` に渡す clean-hyp ラッパを 1 本 publish。Z は標準正規（`gaussianReal 0 1`）に固定 or `Z_law` 前提。
- [ ] **非空虚性確認**: (i) Gaussian X（`deBruijn_identity_v2_gaussian`（`DeBruijn.lean:286`）で既に witness 済）、(ii) 一般 a.c. X（`ofHeatFlow` が `hX_ac` + `h_mom_X` から bundle 構成）。両方で非空虚を plan に記録。
- 撤退ライン: 証人組立に欠けがあれば `deBruijn_identity_v2`（`IsRegularDeBruijnHypV2` 条件付き、既 genuine）を headline とし、非空虚性は `ofHeatFlow` への参照で示す（producer を呼ぶ薄いラッパに留める。新規 sorry は不要見込み）。

---

## Phase 4 — de Bruijn integration (path) producer + 非空虚化（H2b）📋

proof-log: yes（**本 plan 唯一の実質フロンティア**。新規 producer 構成）。

**目標**: `IsDeBruijnPathRegular X Z P T` の **inhabitant を新規構成**（現状 0 件）し、`debruijnIntegrationIdentity_holds` を非空虚化。さらに clean-hyp ラッパ headline を publish。

**headline target**:

```
theorem isDeBruijnPathRegular_of_heat_flow      -- 新規 producer（唯一の新規 analytic）
    ... (hX_ac, h_mom_X, Z_law, T 前提) ... : IsDeBruijnPathRegular X Z P T

theorem debruijn_identity_integrated            -- clean-hyp 再 export
    ... : h(X+√T·Z) - h(X) = ∫₀ᵀ (1/2)·J(X+√t·Z) dt
```

`IsDeBruijnPathRegular`（`DeBruijn.lean:201`）の 3 field と裏付け資産:

- [ ] **`reg_t`**（各内点 t で `∃ h_reg : IsRegularDeBruijnHypV2 ∧ density_t = fPath t`）: `ofHeatFlow` を内点 t ごとに呼ぶ。`fPath t := convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩)`（`ofHeatFlow` の `density_t` と defeq に pin）。
- [ ] **`cont`**（`[0,T]` 上の heat-flow 微分エントロピー連続性）: G2 `heatFlowEntropyPower_continuousWithinAt_zero`（CLOSED、一般密度）+ 内点連続性で `ContinuousOn ... (Icc 0 T)` に組む。端点 0 の連続性が肝（G2 が供給）。**M0 で `differentialEntropy` 連続性と entropy-power 連続性の対応補題を verbatim 同定すること**（G2 の結論は entropy-power 側。微分エントロピー側への bridge 有無を要確認）。
- [ ] **`integrable`**（`(1/2)·J(fPath t)` の `(0,T)` interval-integrability）: `gaussianConv_fisher_le_inv_var`（`J(fPath t) ≤ 1/t`、fisher-finiteness CLOSED）+ path-integrand の可測性/連続性 → `ContinuousOn.intervalIntegrable` 等。`1/t` は `t→0⁺` で発散するが interval-integrable（`∫₀ᵀ 1/t` は improper だが de Bruijn は `Ioo 0 T` で、実際は `J` は `t→0` で `J(X)` に有界 or 可積分。**ここが Phase 4 の最大不確実点** — M0 で可積分性の根拠を 1 本特定）。
- [ ] **gateway atom（最初の一手、CLAUDE.md gateway-atom-first）**: **Gaussian X の `IsDeBruijnPathRegular` 証人を 1 本** dispatch して通るか確認（Gaussian なら `J(𝒩(m,v+t)) = 1/(v+t)` が `[0,T]` 上連続有界で `integrable` field が容易）。通れば一般 a.c. に拡張、詰まれば壁の所在が `integrable` field と確定。
- 撤退ライン:
  - `integrable` field が genuine Mathlib gap と判明（path-integrand の interval-integrability が組めない）→ `isDeBruijnPathRegular_of_heat_flow` の当該 field を `sorry` + `@residual(plan:stam-debruijn-standalone-moonshot-plan)`。それでも **`IsDeBruijnPathRegular` struct に load-bearing field を足さない**（既存 struct の inhabitant を作るだけ、struct 改変禁止）。
  - 壁が再現的・family 横断と判明したら、**proposed wall `debruijn-path-integrability`** として register 格上げ判断（既存 `debruijn-integration` は per-time の CLOSED 壁、本件は path-regularity 生成側で semantic 別）。register 追記は code/inventory 側の作業。本 plan では plan-slug 撤退を primary とする。
  - Phase 4 が肥大（>200 行 / 多 session）したら sub-plan `stam-debruijn-path-regularity-plan.md` に分離し、`@residual(plan:stam-debruijn-path-regularity-plan)` に切替。

---

## Phase 5 — headline 配線 + 独立 honesty audit 📋

proof-log: no。

- [ ] H1（密度版 + optional measure 版）/ H2a / H2b（成功時）の新規 file を `InformationTheory.lean` に import 追記。
- [ ] README theorem table 候補に H1 Stam / H2 de Bruijn を登録（`docs/readme-theorems.txt` 編集 → `gen_readme_table.ts --write`。これはコード変更時の別作業）。
- [ ] **独立 honesty audit 起動**（CLAUDE.md「Independent honesty audit」必須）: 新規 `sorry`+`@residual` を導入した Phase（特に Phase 4）について `honesty-auditor` を起動。観点: (a) signature の非循環・非バンドル（`IsDeBruijnPathRegular` inhabitant が core を仮説で受けていないか）、(b) `@residual` 分類の正しさ、(c) Stam headline が non-vacuous instantiation になっているか（Gaussian-smoothed クラスで実際に discharge される）。
- [ ] 各 headline の `#print axioms` で sorryAx-free を実測 → `@audit:ok` 付与。

---

## 撤退ライン（plan 全体）

- 各 Phase の撤退は **`sorry` + `@residual(plan:stam-debruijn-standalone-moonshot-plan)`**（filename stem。`docs/audit/audit-tags.md` placement 規約）。
- **禁止**: `IsStam*Optimal` / `IsBlachmanConvReady` 等を「核を抱える仮説」として headline の前提に取り直す形（load-bearing bundling）。Stam 核は既に genuine（`stam_step2_density_wall` sorryAx-free）なので、honest な道は常に「producer を呼んで discharge」。
- **非空虚性が崩れた場合の扱い**: もし producer のどれかが実は Gaussian 限定だった（M0 で反証）なら、それは honesty 上の最重要事項として即 flag し、当該 headline を「Gaussian-smoothed クラス限定」と明示名（`_gaussian` 接尾）にする — 一般を偽装しない。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除（git が履歴）、active な判断のみ残す（→ CLAUDE.md「Plan / docs hygiene」）。プラン予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。

1. **(2026-06-27) 非空虚性の事前確定 + フロンティア局在**: orchestrator の現状報告を verbatim 検証した結果、(i) Stam の非空虚 discharge は `isBlachmanConvReady_convDensityAdd_gaussian`（19/19 field genuine, `@audit:ok`）により **Gaussian-smoothed 密度クラス（任意確率密度 ∗ g_t）で確立済**＝ Gaussian 等号限定ではない、(ii) Stam 核 `isStamInequalityHyp_of_primitives` は sorryAx-free・load-bearing でない、(iii) de Bruijn per-time も `ofHeatFlow` で一般 a.c. 非空虚、と確認。**唯一の非空虚性 gap = de Bruijn 積分形の `IsDeBruijnPathRegular`（inhabitant 0 件、Gaussian 証人すら無い）** → Phase 4 に局在。よって本ムーンショットの総合判定は「ほぼ組み上げ（Phase 1/2/3/5 は小〜中）+ Phase 4 のみ実質新規（path-regularity producer、ただし 3 field とも CLOSED 機構で裏付け、PR 級壁ではない）」。

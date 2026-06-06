# EPI Stam → EPI conclusion — B-wire honest discharge plan

> **Parent**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) (無条件 EPI moonshot の最終 wall "B-wire")
> **Status**: `stamToEPIBridge_holds` (`EntropyPowerInequality.lean:251`、`@residual(plan:epi-stam-to-conclusion-plan)`) が唯一の残 transitive sorry。**W2 cluster は完全 CLOSED** (sorryAx-free、2026-06-06 機械検証済)。
> **2026-06-06 全面 destale + 2-phase 再構成**: 旧 difference-form route (G1-G4/W0-W2 表、ratio 再frame route B、Phase A skeleton/A-close 等) は **すべて履歴**。W2-cluster CLOSED + assembly 部品が genuine 着地したのを受け、本 plan を **Phase A (密度あり標準形) + Phase B (完全一般形)** の 2-phase に再構成する。旧記述は本ファイル末尾「## 旧記述 (履歴、参照しない)」へ退避。

## 進捗

- [ ] Phase A — 密度あり標準形 EPI `entropy_power_inequality_of_density` を sorryAx-free 化 (lift + producer + step3 + methodX assembly) 🚧 → 下記 §Phase A
- [ ] Phase B — 完全一般形 `entropy_power_inequality` を任意可測 X,Y で sorryAx-free 化 (密度 case split + 退化枝) 📋 → 下記 §Phase B (概略のみ)

proof-log: yes (Phase A 完了時 `docs/shannon/proof-log-epi-stam-to-conclusion-phaseA.md`)

---

## ゴール / Approach

**最終ゴール** (Phase B): 任意可測 `X Y : Ω → ℝ`、`IndepFun X Y P` に対し
`entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)`
を `#print axioms` sorryAx-free にし、`stamToEPIBridge_holds` を off-bridge 化 or 撤去する。

**中間ゴール** (Phase A、今 session): X,Y に **a.c.(密度) + 有限2次モーメント** を honest regularity 前提として付けた形で同 EPI を sorryAx-free 化する。新 theorem `entropy_power_inequality_of_density` を産み、`#print axioms` で sorryAx-free を確認する。一般 headline `entropy_power_inequality` は Phase B まで `stamToEPIBridge_holds` sorry 経由のまま残す。

### Approach (解の全体形)

W2-cluster (Stam-Blachman / de Bruijn / G2 端点連続性 / lift noise / step3 producer) は **すべて genuine sorryAx-free** に着地済 (下記「確認済 genuine 部品」)。残る作業は **これらを正しい順で組み立てる assembly + precondition の discharge** であり、新しい解析的 math 構造の設計は (Phase A では) 不要。

組み立ての backbone は **lift + producer + step3 + methodX** の 4 段:

```
base (Ω,P) ──[lift]──→ (Ω×ℝ×ℝ, liftMeasure P)
   雑音 Z_X := p.2.1, Z_Y := p.2.2 は lift から gaussianReal 0 1 + 独立を genuine 供給
        ↓
   methodX assembly (entropyPower_add_ge_case1_of_methodX, :1499) を lift 上で適用
   ├ de Bruijn group  h_reg_X'/h_reg_Y'/h_reg_sum  ← producer isDeBruijnRegularityHyp_of_methodX_unitnoise (:1950)
   ├ endpoint group   h_endpt_X/h_endpt_Y/h_endpt_sum  ← IsHeatFlowEndpointRegular を密度前提から構成
   ├ per-time Stam    h_pos_stam (IsStamInequalityHyp + IsRegularDensityV2 + IsBlachmanConvReady)
   │                  ← step3 producer (isStamInequalityHyp_via_step3, :123) ⊕ density_t 正則性供給
   └ scaling group    h_scale_* / IsRescaledPathRegular  ← methodX 本体が内部生成 (:1740, supply 済)
        ↓ lift 上 EPI
   entropy_power_inequality_via_lift (EPINoiseExtension.lean:145)  ← measure-transport
        ↓
   base (Ω,P) 上 EPI
```

**Phase B の追加構造** (別 session): 任意可測 X,Y を「密度を持つ枝」(= Phase A を再利用) と「密度を持たない退化枝」(離散・特異等、微分エントロピーが退化) で case split し、退化枝を新規に解く。これは plumbing でなく解析的作業 (退化境界値を verbatim 確認してから設計)。

### 構造的所見 (Phase B が必須な理由)

`stamToEPIBridge_holds` の signature (`IsStamToEPIBridge`、`EntropyPowerInequality.lean:234`) は `(X Y P)` のみで **measurability も independence も a.c. も持たない**。一方 methodX route は density(a.c.)+moments+雑音 law+indep を必須とする。よって bridge を現 signature のまま「任意可測 X,Y」で honest discharge するのは不可能 — 密度を持たない退化ケースを別途解く case split が要る (= Phase B)。Phase A はその密度ケース枝を先に完成させる。

---

## 確認済 genuine 部品 (2026-06-06 機械検証済、本 plan の前提、全て verbatim 照合済)

すべて `#print axioms` で `[propext, Classical.choice, Quot.sound]` (sorryAx-free)。file:line + signature/前提を verbatim 転記。

### P-1 step3 producer (純 measurable+indep から Stam を産む)

- **`isStamInequalityHyp_via_step3`** — `EPIStamStep3Body.lean:123`、`@audit:ok`。
  - signature: `(P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) : IsStamInequalityHyp X Y P`
  - 純 measurability + independence + probability measure のみ。load-bearing analytic hyp なし。

### P-2 雑音 lift (lift 上 EPI → base EPI の measure-transport)

- **`liftMeasure`** — `EPINoiseExtension.lean:48`: `liftMeasure P := P.prod ((gaussianReal 0 1).prod (gaussianReal 0 1))` (noncomputable abbrev、型 `Measure (Ω × ℝ × ℝ)`)。
- **`entropy_power_inequality_via_lift`** — `EPINoiseExtension.lean:145`、`@audit:ok`。
  - signature: `(hX : Measurable X) (hY : Measurable Y) (h_lift_epi : entropyPower ((liftMeasure P).map (fun p => X p.1 + Y p.1)) ≥ entropyPower ((liftMeasure P).map (fun p => X p.1)) + entropyPower ((liftMeasure P).map (fun p => Y p.1))) : entropyPower (P.map (fun ω => X ω + Y ω)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)`
  - honest measure-transport reduction (lift 測度 EPI → base 測度 EPI)、circular でも bundle でもない。
- lift 座標 `p.2.1`/`p.2.2` が genuine `gaussianReal 0 1` 雑音 + 独立であることの供給:
  - **`stamScalingNoise_exists_on_lift`** — `EPINoiseExtension.lean:76`、`@audit:ok`: `(hX hY : Measurable …) : IsStamScalingNoiseHyp (fun p => X p.1) (fun p => Y p.1) (liftMeasure P)`。witness は座標射影 `Z_X' := (·.2.1)`, `Z_Y' := (·.2.2)`、7 conjunct (Measurable×2 / gaussian law×2 / IndepFun×3) を product-measure API で genuine 充足。
  - **`indepFun_add_add_on_lift`** — `EPINoiseExtension.lean:122`、`@audit:ok`: `IndepFun (fun p => X p.1 + Y p.1) (fun p => p.2.1 + p.2.2) (liftMeasure P)` (`indepFun_prod` 直接)。
  - **`entropyPower_map_comp_fst_eq`** — `EPINoiseExtension.lean:59`、`@audit:ok`: lift 上 X law 保存 `entropyPower ((liftMeasure P).map (fun p => X p.1)) = entropyPower (P.map X)`。

### P-3 de Bruijn producer (a.c.+moment+正則性 → de Bruijn group)

- **`isDeBruijnRegularityHyp_of_methodX_unitnoise`** — `EPICase1RatioLimit.lean:1950`、`@audit:ok`、2026-06-06 producer measurability CLOSED で sorryAx-free。
  - signature (precondition verbatim):
    - `(X Z_X : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]`
    - `(hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)`
    - `(hZX_law : P.map Z_X = gaussianReal 0 1)`
    - `(hX_ac : (P.map X) ≪ volume) (h_mom_X : Integrable (fun ω => (X ω) ^ 2) P)`
    - `(h_fisher_X : FisherInfoV2.fisherInfoOfDensity (fun x => ((P.map X).rnDeriv volume x).toReal) ≠ ∞)` ← **入力密度の Fisher 有限性**
    - `(hreg_pX : FisherInfoV2.IsRegularDensityV2 (fun x => ((P.map X).rnDeriv volume x).toReal))` ← **入力密度 pX の正則性**
    - `(hnorm_pX : ∫ x, ((P.map X).rnDeriv volume x).toReal ∂volume = 1)`
    - `(hready_pX : ∀ v : ℝ≥0, v ≠ 0 → EPIBlachmanDensity.IsBlachmanConvReady (fun x => ((P.map X).rnDeriv volume x).toReal) (gaussianPDFReal 0 v))`
  - 結論: `IsDeBruijnRegularityHyp X Z_X P`。
  - **⚠ 重大**: `hreg_pX`(`IsRegularDensityV2`)/`hready_pX`(`IsBlachmanConvReady`)/`h_fisher_X` は **一般 L¹ a.c. 密度では満たされない** (producer docstring `:1799-1808` が明言: "general L¹ a.c. density … need NOT satisfy `IsRegularDensityV2` (differentiable + strictly positive everywhere + both tails → 0) nor the boundedness fields")。Phase A の supply 不能候補 (§Phase A 撤退ライン)。

### P-4 methodX 組み立て (de Bruijn group + Stam group + scaling group → case-1 EPI)

- **`entropyPower_add_ge_case1_of_methodX`** — `EPICase1RatioLimit.lean:1499`、`@residual(plan:epi-debruijn-pertime-closure)`。
  - precondition verbatim (`:1499-1548`):
    - measurability: `hX hY hZX hZY`
    - a.c.: `hX_ac : (P.map X) ≪ volume`、`hY_ac`、`hXY_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume` (sum-a.c. は X⊥Y なしでは hX_ac/hY_ac から出ない標準 case-1 hyp)
    - moments: `h_mom_X : Integrable (fun ω => (X ω)^2) P`、`h_mom_Y`
    - 雑音 law: `hZX_law : P.map Z_X = gaussianReal 0 1`、`hZY_law`
    - 4-tuple indep: `h_iIndep : iIndepFun ![X, Y, Z_X, Z_Y] P`
    - de Bruijn group: `h_reg_sum/h_reg_X'/h_reg_Y' : IsDeBruijnRegularityHyp …`
    - endpoint group: `h_endpt_sum/h_endpt_X/h_endpt_Y : IsHeatFlowEndpointRegular …`
    - **`h_pos_stam`** (`:1526-1548`): `∀ t > 0,` 以下の 10-conjunct ∧:
      `0 < fisherInfoOfDensityReal (density_t)` ×3 ∧ `IsStamInequalityHyp (X+√t Z_X)(Y+√t Z_Y) P` ∧ `IsRegularDensityV2 (density_t)` ×2 ∧ `∫ density_t = 1` ×2 ∧ `density_sum_t = convDensityAdd density_X_t density_Y_t` ∧ `IsBlachmanConvReady (density_X_t)(density_Y_t)`
  - 結論: `entropyPower (P.map (fun ω => X ω + Y ω)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)` (= case-1 EPI)。
  - 本体 (`:1740-1749`): `h_scale_*` (3個) のみ内部生成 (`h_scale_general` + `convDensityAdd_negMulLog_integrable_pub`)、`IsRescaledPathRegular` を `varX/varY/varS` 経由で内部生成。**de Bruijn group / endpoint group / h_pos_stam は caller 前提のまま `entropyPower_add_ge_case1_of_regular` (:1344) に pass-through**。producer は methodX 本体では呼ばれていない (要 Phase A で外側 assembly が呼ぶ)。

### P-5 退化境界値 (Phase B 設計用、verbatim 確認済)

- `differentialEntropy_dirac (m : ℝ) : differentialEntropy (Measure.dirac m) = 0` — `DifferentialEntropy.lean:155-156`。よって `entropyPower (Measure.dirac m) = exp(2·0) = 1` (退化 measure でも entropyPower は 0 でなく **1**)。Phase B 退化枝の境界処理はこの値で設計する (直感の `-∞` / `0` は誤り)。

---

## Phase A — 密度あり標準形 EPI 🚧

> **目標**: 新 theorem `entropy_power_inequality_of_density` を `#print axioms` sorryAx-free にする。一般 `entropy_power_inequality` は Phase B まで bridge sorry のまま。

proof-log: yes

### A-Approach (Phase A の shape)

base `(Ω,P)` を lift `(Ω×ℝ×ℝ, liftMeasure P)` へ持ち上げ、lift 上で雑音 `Z_X := p.2.1`/`Z_Y := p.2.2` (gaussianReal 0 1 + 独立、P-2 が genuine 供給) を使って `entropyPower_add_ge_case1_of_methodX` (P-4) を適用し、`entropy_power_inequality_via_lift` (P-2) で base に戻す。methodX の前提群 (de Bruijn group / endpoint group / h_pos_stam) を **producer (P-3) + step3 (P-1) + 密度前提から discharge** する。

### A-Steps

- [ ] **A-0 在庫調査 + 新 theorem signature 確定**。Phase A の密度前提 (a.c. + 有限2次モーメント) を `IsRegularDensityV2`/`IsBlachmanConvReady`/Fisher 有限まで強化する必要があるか (= producer precondition 表の「supply 不能」セルがいくつあるか) を verbatim 確定する。signature 案 → §A-signature。
- [ ] **A-1 lift 適用 skeleton**。`entropy_power_inequality_via_lift` を呼ぶ外殻を skeleton で立て、必要な lift 上前提 (X∘fst の measurability/a.c./moment、Z_X'/Z_Y' の law/indep、4-tuple iIndepFun) を `sorry` placeholder で列挙し type-check 通す。lift 上 a.c./moment が base a.c./moment から transport できるか確認 (`map_map` + `measurePreserving_fst`、P-2 の `entropyPower_map_comp_fst_eq` と同型)。
- [ ] **A-2 4-tuple iIndepFun 構成**。lift 上 `iIndepFun ![X∘fst, Y∘fst, Z_X', Z_Y'] (liftMeasure P)` を P-2 の pairwise (`stamScalingNoise_exists_on_lift`) + base `IndepFun X Y P` から組む。`iIndepFun` (4-tuple joint) が pairwise から自動では出ない場合は product-measure 構成で直接 (lift の構造は `P.prod (ν.prod ν)` なので joint indep は product 構造から genuine)。
- [ ] **A-3 de Bruijn group 供給 (producer P-3 経由)**。`isDeBruijnRegularityHyp_of_methodX_unitnoise` を 3 pair (X∘fst,Z_X')/(Y∘fst,Z_Y')/(X∘fst+Y∘fst, Z_X'+Z_Y') 分呼ぶ。**ここが Phase A の難所**: producer の `hreg_pX`/`hready_pX`/`h_fisher_X` を Phase A 密度前提から供給できるか (§A-precondition 表)。sum-pair の雑音は `Z_X'+Z_Y' ~ gaussianReal 0 2` (unit でない) なので producer の `gaussianReal 0 1` 前提と不整合 → sum-instance は reparametrization 要 (producer docstring `:1840` "sum-instance `𝒩(0,2)` is the only reparam case, deferred to a later wave")。**撤退候補**。
- [ ] **A-4 endpoint group 供給**。`IsHeatFlowEndpointRegular X Z_X P` の 14 field (`EPIG2HeatFlowContinuity.lean:490-505`: measurability/indep/v_Z/gaussian law/pX witness/normalization/moment/entropy 有限性) を密度前提 + lift 雑音から構成。`hpX_ent : Integrable (negMulLog pX)` は密度の微分エントロピー有限性で、a.c.+moment からは出ない可能性 (§A-precondition)。
- [ ] **A-5 h_pos_stam 供給 (step3 P-1 + density_t 正則性)**。`IsStamInequalityHyp (X+√t Z_X)(Y+√t Z_Y) P` は step3 producer (P-1) で `Measurable + IndepFun` から供給 (X+√t Z_X は可測、独立は 4-tuple から)。per-t `IsRegularDensityV2 (density_t)`/`IsBlachmanConvReady (density_t)` は **RESOLVED** (L-PhA-γ 参照): `density_t_eq` pin で `convDensityAdd pX gaussian` に rewrite → `isRegularDensityV2_convDensityAdd_gaussian` (`:202`)/`isBlachmanConvReady_convDensityAdd_gaussian` (`:224`) 適用。normalization (`∫ density_t = 1`) は `convDensityAdd` の質量保存補題、conv-pin (`density_sum_t = convDensityAdd density_X_t density_Y_t`) は heat-flow 密度の convolution 構造から。これらの bridge 補題が in-tree にあるか A-0 で verbatim 確認。
- [ ] **A-6 methodX 適用 + lift→base**。A-2〜A-5 が揃えば `entropyPower_add_ge_case1_of_methodX` を lift 上で適用し、`entropy_power_inequality_via_lift` で base に戻す。`h_scale_*`/`IsRescaledPathRegular` は methodX 本体が内部生成するので caller 供給不要。
- [ ] **A-7 `#print axioms entropy_power_inequality_of_density` で sorryAx-free 確認**。新規 `sorry` + `@residual` を導入したら **独立 honesty-auditor 起動** (CLAUDE.md 必須)。

### A-signature (新 theorem 案、A-0 で確定)

```
theorem entropy_power_inequality_of_density
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω)^2) P)
    (h_mom_Y : Integrable (fun ω => (Y ω)^2) P)
    -- A-0 で確定: 以下の追加 regularity 前提が producer precondition の
    -- supply 不能セルを埋めるために必要か (load-bearing でない密度正則性)
    -- 候補: 入力密度の IsRegularDensityV2 / IsBlachmanConvReady / Fisher 有限 / entropy 有限
    : entropyPower (P.map (fun ω => X ω + Y ω))
        ≥ entropyPower (P.map X) + entropyPower (P.map Y)
```

**honesty 制約** (CLAUDE.md 検証の誠実性): 追加する regularity 前提 (`IsRegularDensityV2`/`IsBlachmanConvReady`/Fisher 有限/entropy 有限) は **入力密度の正則性 precondition であり load-bearing でない** (EPI / Stam の核を encode しない) ことを honesty-auditor が確認すること。`IsBlachmanConvReady` は 19 field の Integrable/boundedness/positivity bundle (`EPIBlachmanDensity.lean:712-761`)、各 field は値や不等式でなく integrability/boundedness のみ主張 → regularity precondition (producer docstring `:1929-1934` の audit 判定済)。命名は `_of_density` で honest (一般化されていないことを明示、`_unconditional`/`_discharged` は禁止)。

### A-precondition 表 (producer/methodX 前提 × Phase A 密度前提からの供給可否)

> A-0 で各セルを verbatim 確定する。「supply 不能」が残ったら §A-撤退ライン の退避先へ。

| methodX/producer 前提 | 供給元 (Phase A 前提) | 必要 bridge 補題 (file:line) | 供給可否 |
|---|---|---|---|
| `hX`/`hY` (measurability) | `hX`/`hY` 直接 | — | OK |
| 4-tuple `iIndepFun ![X∘fst,…]` | `hXY` + lift product 構造 | `stamScalingNoise_exists_on_lift` (P-2) + product-indep | A-2 で確定 (pairwise→joint 自動でない可能性) |
| `hX_ac`/`hY_ac` (lift 上) | base a.c. + `measurePreserving_fst` | `map_map` transport (P-2 同型) | OK 見込み |
| `hXY_ac` (sum a.c., lift 上) | `hX_ac` + `hXY` (X⊥Y) | `map_add_absolutelyContinuous` (`:1704` 既存) | OK 見込み |
| `h_mom_X`/`h_mom_Y` | base moment + transport | (新規 transport 補題?) | A-1 で確定 |
| 雑音 law/indep (Z_X'/Z_Y') | lift 構造 | `stamScalingNoise_exists_on_lift` (P-2) | OK (genuine) |
| de Bruijn group `h_reg_*` (X/Y singleton) | producer P-3 | `isDeBruijnRegularityHyp_of_methodX_unitnoise` | **要 `hreg_pX`/`hready_pX`/`h_fisher_X` (A-signature 追加前提)** |
| de Bruijn group `h_reg_sum` (sum-instance, methodX 経路) | — | — | **uninhabitable (`Z_law(sum)=𝒩(0,1)` が偽、variance 2)。methodX 経路は放棄、two-time route へ (Gap 2 RETRACTED 節)** |
| endpoint group `h_endpt_*` | 密度前提 + 雑音 | `IsHeatFlowEndpointRegular` field 構成 | **`hpX_ent` (entropy 有限) が要追加前提 (撤退 A-β)** |
| `h_pos_stam`: `IsStamInequalityHyp` | step3 producer P-1 | `isStamInequalityHyp_via_step3` | OK (genuine) |
| `h_pos_stam`: per-t `IsRegularDensityV2/IsBlachmanConvReady(density_t)` | conv-gaussian producer (in-tree 既存) + `density_t_eq` pin | `isRegularDensityV2_convDensityAdd_gaussian` (`EPIConvDensityRegular.lean:202`, `@audit:ok`) / `isBlachmanConvReady_convDensityAdd_gaussian` (`EPIBlachmanGeneralDensity.lean:224`, `@audit:ok`) を `density_t_eq` (`FisherInfoV2DeBruijn.lean:236`, density_t = convDensityAdd pX gaussian へ pin) で rewrite 後適用 | **OK (RESOLVED 2026-06-06)** — 前提は input pX の nonneg/measurable/integrable/mass>0/normalized のみ (input IsRegularDensityV2 不要) |
| `h_scale_*` / `IsRescaledPathRegular` | methodX 本体が内部生成 | — (caller 供給不要) | OK (済) |

### A-撤退ライン

- **L-PhA-α** (sum-instance 𝒩(0,2)) — **撤退でなく route 変更 (2026-06-06)**: methodX 経路の sum de Bruijn group `h_reg_sum` は `IsRegularDeBruijnHypV2.Z_law` ハードコードにより **uninhabitable** (variance-2 で `Z_law=𝒩(0,1)` 偽)。これは「park すれば後で埋まる」residual ではなく**構造的に充足不能**。→ methodX 経路を放棄し **two-time route 載せ替え** (Gap 2 節)。現 4 sorry は honest park (type-check done, commit OK) のまま、two-time assembly 完成時に置換消滅。
- **L-PhA-β** (endpoint entropy 有限性 `hpX_ent`): `Integrable (negMulLog pX)` が a.c.+moment から出ない → 密度の微分エントロピー有限性を A-signature の **追加 honest precondition** として明示 (load-bearing でない regularity)。これは退避でなく honest 強化 (許容)。
- **L-PhA-γ** (h_pos_stam per-t density_t 正則性) — **RESOLVED 2026-06-06、park 不要**。当初「in-tree producer 不在」と評価したが誤り (naming miss): `isRegularDensityV2_convDensityAdd_gaussian` (`EPIConvDensityRegular.lean:202`) と `isBlachmanConvReady_convDensityAdd_gaussian` (`EPIBlachmanGeneralDensity.lean:224`) が conv-gaussian (t>0 heat-flow) 密度の正則性を **sorryAx-free** で産む。`IsRegularDeBruijnHypV2.density_t_eq` (`FisherInfoV2DeBruijn.lean:236`) が `density_t` を `convDensityAdd pX (gaussianPDFReal 0 ⟨t,ht.le⟩)` に pin するので、これで rewrite → 上記 producer 適用。前提は input pX の nonneg/measurable/integrable/mass>0/normalized のみ (input IsRegularDensityV2 は **不要**)。よって per-t density_t 正則性は genuine 供給可能、Phase A の sorryAx-free 到達を阻まない。(CLAUDE.md「Mathlib 壁判定は独立 pivot で再確認」の実例: 単一想定ルート blocked を壁と誤認。)
- **共通禁止** (CLAUDE.md 検証の誠実性): producer を **bypass** して de Bruijn group や h_pos_stam を caller 供給のまま積む (= signature に load-bearing `IsDeBruijnRegularityHyp`/`h_pos_stam` を残す) のは **禁止** (tier-4/5 defect)。必ず producer/step3 経由 discharge。`Y:=0`/`Z_Y:=0` の退化定義悪用も禁止。撤退時 docstring に「NOT a discharge / residual on <plan slug>」明示。

### A-gap closure roadmap (2026-06-06、Phase A 実装後 + pivot-advisor 評価で確定)

Phase A 実装 (commit `eb0825b`、`EPIDensityForm.lean`) は type-check done + 6 residual。X/Y singleton route は genuine。残 6 residual = 2 gap、**両者 Mathlib 壁なし・in-tree 資産で genuine close 可能** (pivot-advisor 2026-06-06 評価)。両 close で Phase A sorryAx-free 到達見込み。

- **Gap 1 = `epi-phaseA-fisher-positivity`** (新 slug、先に attack 推奨): h_pos_stam の `0 < fisherInfoOfDensityReal (density_t)` 3 conjunct (X'/Y'/sum)。新 lemma `fisherInfoOfDensityReal_convDensityAdd_pos` (X'/Y' 同形で 1 本)。route: `J=0` → `lintegral_eq_zero_iff` + `convDensityAdd_pos` (`FisherInfoV2DeBruijnPerTime.lean:808`, `@audit:ok`、everywhere 正) → `logDeriv f=0 a.e.` → `deriv f=0 a.e.`、`convDensityAdd_deriv1_gaussian_eq` (`EPIConvDensitySecondDeriv.lean:58`、deriv の explicit closed form) の score factor `-(ζ-y)/s` non-vanishing で矛盾。**~40-60 行、自己完結、signature 不変**。`gaussianConv_fisher_le_inv_var` は上界のみ (下界 lemma 在庫ゼロ)。
- **Gap 2 = `epi-phaseA-sum-reparam` → RETRACTED (2026-06-06 機械検証 + pivot-advisor 裏取り)。代替 = two-time route 載せ替え (新 slug `epi-phaseA-twotime-assembly`)**。
  - **旧ルート (producer `gaussianReal 0 v` 一般化) は構造的に実行不能**: methodX 経路の `h_reg_sum : IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) lift` は `reg_at` 戻り型 `IsRegularDeBruijnHypV2` (`FisherInfoV2DeBruijn.lean:205`) の `Z_law : P.map Z = gaussianReal 0 1` フィールドを要求するが、sum 雑音の真の law は `gaussianReal 0 2` → `Z_law(sum)=𝒩(0,1)` は**偽**、`h_reg_sum` は **uninhabitable**。producer 引数 `hZX_law` を一般化しても `Z_law := hZX_law` フィールド代入が型エラー (v≠1)。`density_t_eq` も variance `t` ハードコード。これは「PB-1 の惰性」でなく**構造フィールドの制約**。**既存独立監査が同結論を code 側で確定済**: `EPIStamToBridge.lean:552-582` GS-A3' scope limitation (`@audit:ok`)「`h_reg_sum` is uninhabitable in that setting」「the `IsRegularDeBruijnHypV2.Z_law` general-variance refactor is no longer needed」「Honest closure of the sum line is achieved by the **two-time route**」。`EPICase1SumProducer.lean` は dead orphan として削除済。
  - **正規 honest ルート = two-time route**: `entropyPower_add_ge_case1_of_regular_twotime` (`EPICase1TwoTime.lean:1620`, `@audit:ok`, sorryAx-free) は sum を **別個の単一 unit noise `Z` (`P.map Z = gaussianReal 0 1`)** で摂動 → `h_reg_sum : IsDeBruijnRegularityHyp (X+Y) Z P` の `Z_law` が**真**。variance-2 view が発生しない。`EPIDensityForm.lean` の assembly を methodX 呼出 (`:416-421`) から twotime 呼出へ載せ替える。
  - **blast radius (pivot-advisor 2026-06-06): 3-4 file、新規 lemma 5-8 本、壁なし**。
    1. **3-noise lift 拡張**: `liftMeasure` (`EPINoiseExtension.lean:48`) は `Measure (Ω×ℝ×ℝ)` (2-noise) → `Ω×ℝ×ℝ×ℝ` (3 独立 unit Gaussian) に拡張。供給補題 `entropyPower_map_comp_fst_eq`/`stamScalingNoise_exists_on_lift`/`indepFun_add_add_on_lift` の 3-noise 版を product-measure API で再供給 (新規 3-4 本、genuine、壁ゼロ)。「2-noise で sum 用 Z を流用」は Z ⊥ (Z_X,Z_Y) 独立性 (`EPICase1TwoTime.lean:1631-1632`) が崩れるので無理筋。
    2. **`h_stam_supply` producer (inverse-form, 唯一の analytic 内容、big-not-wall)**: two-time は `∀ σ τ>0, ... ∧ 1/J_S(σ+τ) ≥ 1/J_X(σ)+1/J_Y(τ)` を要求 (`:1667-1679`)。in-tree producer はゼロ。**数学的帰着 (確定済)**: `density_sum_{σ+τ} = conv(p_{X+Y}, g_{σ+τ}) = conv(conv pX pY, g_σ*g_τ) = conv(density_X_σ, density_Y_τ)` (convolution-splitting `g_{σ+τ}=g_σ*g_τ`)。よって `isStamInequalityHyp_via_step3` (`EPIStamStep3Body.lean`, `@audit:ok`) を摂動変数 `A=X+√σ·Z_X`, `B=Y+√τ·Z_Y` (lift 上独立) に適用 + sum を単一 noise Z (variance σ+τ) に law-match + conv-pin 供給。`IsStamInequalityHyp` 定義 (`EPIStamDischarge.lean:128-140`) は universal で `fXY = convDensityAdd fX fY` pin 付き inverse-form なので接続可能。新規 1-3 本 (step3 適用 + conv-splitting bridge + law-match)。**着手前に conv-splitting bridge `g_{σ+τ}=g_σ*g_τ` の Mathlib/in-tree 資産有無を確定** (壁誤認回避、CLAUDE.md)。
    3. **endpoint_sum (unit Z) + sum Fisher 正値 (σ+τ)**: `h_endpt_sum : IsHeatFlowEndpointRegular (X+Y) Z P` を unit Z で構成 (現 `endpt_of` helper 再利用、v_Z=1 で genuine)。sum Fisher 正値は Gap 1 lemma `fisherInfoOfDensityReal_convDensityAdd_pos` を density_sum に適用。
    4. **assembler 書換**: `EPIDensityForm.lean` の methodX 呼出を twotime 呼出へ + 3-noise endpoint/scale/rescale 前提供給。
- 注: 現 4 residual (L214 h_reg_sum / L279 h_endpt_sum / L404 sum Fisher / L409 conv-pin) は全て methodX 経路の uninhabitable obligation に乗っている → two-time 載せ替えで assembly ごと置換され消える。**個別 fill でなく assembly 再構成**。

### A-Done 条件

- `entropy_power_inequality_of_density` が `#print axioms` sorryAx-free (理想)。L-PhA-γ は RESOLVED、Gap 1 (Fisher 正値) は CLOSED。**唯一の残作業 = Gap 2 = two-time route 載せ替え** (`epi-phaseA-twotime-assembly`、Gap 2 節参照)。methodX 経路の sum de Bruijn group は uninhabitable のため、assembly を `entropyPower_add_ge_case1_of_regular_twotime` 経由に再構成する (3-noise lift + h_stam_supply producer + endpoint_sum)。完成で sorryAx-free 到達。
- 新 theorem の signature に load-bearing hyp なし (honesty-auditor 確認)。
- `InformationTheory.lean` 編入 + `lake env lean` clean。

---

## Phase B — 完全一般形 EPI (最終目標、別 session) 📋

> **概略のみ。退化枝は未解析。撤退ライン = Phase A で止める可。**

proof-log: yes (別 session)

### B-Approach (概略)

任意可測 `X Y : Ω → ℝ` (`IndepFun X Y P`) で `entropy_power_inequality` を sorryAx-free 化する。Phase A の `entropy_power_inequality_of_density` を「密度ケースの枝」として再利用し、密度の有無で case split する:

```
任意可測 X,Y
 ├ X,Y とも密度を持つ (P.map X ≪ volume ∧ P.map Y ≪ volume) ──→ Phase A 枝 (entropy_power_inequality_of_density)
 │     ただし Phase A の追加 regularity (IsRegularDensityV2 等) も成立する必要 → 一般 a.c. では追加正則性が出ない場合あり (要解析)
 └ 密度を持たない退化枝 (離散/特異/混合) ──→ 新規に解く (未解析)
```

### B-未解析項目 (別 session で着手前に verbatim 確認)

- **退化境界値**: 密度なし measure での `differentialEntropy` / `entropyPower` の値を Mathlib/InformationTheory verbatim で確認 (CLAUDE.md 具体的数値・型予測の verbatim 確認)。P-5 で `differentialEntropy_dirac = 0` (`DifferentialEntropy.lean:155`、よって `entropyPower (dirac) = 1`) を確認済。一般の密度なし measure (連続特異・混合) の値は別途確認。退化枝の EPI が境界値で trivially 成立するか / 反例があるかを設計前に確定。
- **密度枝の追加正則性 gap**: Phase A が要求する `IsRegularDensityV2`/`IsBlachmanConvReady` は「一般 a.c. 密度」でも出ない (producer docstring `:1799-1808`)。完全一般形では一般 a.c. 密度に対し score-of-convolution Fisher monotonicity を genuine に解く必要 (Mathlib gap、`wall:stam` 系の最深部) → これが Phase B の真の analytic 壁。
- **case split の境界**: 「密度を持つ ∧ Phase A 追加正則性を持つ」/「密度を持つが追加正則性なし」/「密度なし」の 3-way split になる可能性。中間枝 (a.c. だが非正則密度) を smoothing (heat-flow ε→0) で密度枝に帰着できるか (= G2 端点連続性 `heatFlowEntropyPower_continuousWithinAt_zero` の再利用) を検討。
- **bridge off-wire**: Phase B 完成時、`entropy_power_inequality` を `stamToEPIBridge_holds` 非経由で証明し直し、`stamToEPIBridge_holds` を off-bridge 化 or 撤去 (consumer 0 件確認後)。

### B-撤退ライン

- **L-PhB-stop** (許容、デフォルト): 退化枝 / 一般 a.c. の Fisher monotonicity が当該 session で解けない → **Phase A で止める**。`entropy_power_inequality_of_density` を genuine 達成成果とし、一般 `entropy_power_inequality` は `stamToEPIBridge_holds` sorry 経由のまま残す (現状維持、honest)。Phase B は後続 session に持ち越し。
- **L-PhB-smoothing** (検討): 一般 a.c. を heat-flow smoothing で密度枝に帰着できれば中間枝を消せる。できなければ smoothing 極限の連続性 (G2 系) を honest precondition 化。

---

## Position

- 親: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) (無条件 EPI moonshot、B-wire = 最終 wall)
- producer closure: [`epi-debruijn-pertime-closure-plan.md`](epi-debruijn-pertime-closure-plan.md) (per-t de Bruijn / density_t 正則性の residual 引受先、A-α/A-γ の退避先)
- methodX wrapper: [`epi-case1-phaseC-methodx-wrapper-plan.md`](epi-case1-phaseC-methodx-wrapper-plan.md)
- 関連 inventory: [`epi-stam-to-conclusion-phaseA-mathlib-inventory.md`](epi-stam-to-conclusion-phaseA-mathlib-inventory.md)

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 仮定修正時。append-only。

1. **2026-05-24 Wave 2 起草** (履歴、§旧記述): stub plan に Phase 0/A/B/V 埋込。EPIPlumbing 3 件先行 close。
2. **2026-05-25 〜 2026-06-01 difference-form route** (履歴、§旧記述): G1-G4/W0-W2 分解、Phase A skeleton/A-close、G1 false-as-framed 判明、ratio 再frame route B 決定。これらは下記「旧記述」に退避、**新規着手では参照しない**。
3. **2026-06-06 W2-cluster CLOSED + 2-phase 再構成**: 以下を機械検証 (`#print axioms`) で確定し、本 plan を difference-form route から **Phase A (密度標準形) + Phase B (完全一般形)** に全面再構成:
   - **残壁 = `stamToEPIBridge_holds` のみ** (`EntropyPowerInequality.lean:251`)。W2-cluster (Stam-Blachman `isStamInequalityHyp_via_step3`、de Bruijn、G2 端点連続性、lift noise `entropy_power_inequality_via_lift`、step3 producer) は全て sorryAx-free。
   - **構造的所見**: `IsStamToEPIBridge` signature は `(X Y P)` のみで measurability/indep/a.c. を持たない → 現 signature の honest discharge は密度退化 case split (= Phase B) 必須。Phase A は密度ケース枝を先に完成。
   - **producer precondition gap 発見** (verbatim 照合): `isDeBruijnRegularityHyp_of_methodX_unitnoise` (`:1950`) は `hreg_pX`(IsRegularDensityV2)/`hready_pX`(IsBlachmanConvReady)/`h_fisher_X` を要求し、これらは「一般 L¹ a.c. 密度」では満たされない (producer docstring `:1799-1808` 明言)。Phase A の最大 supply 不能候補 = h_pos_stam の per-t `density_t` 正則性 (in-tree producer 不在、grep 0件) → 撤退 L-PhA-γ。
   - **methodX 本体は producer を呼ばない** (`:1740-1749` 照合): de Bruijn group / endpoint group / h_pos_stam は signature 前提のまま `_of_regular` に pass-through、`h_scale_*`/`IsRescaledPathRegular` のみ内部生成。よって Phase A の assembly は **外側で producer を呼んで de Bruijn group を作り methodX に渡す** 必要がある (pure assembly でなく producer 適用 + precondition discharge を含む)。
   - 退化境界値 `differentialEntropy_dirac = 0` (`DifferentialEntropy.lean:155`) verbatim 確認 → Phase B 退化枝設計用 (`entropyPower (dirac) = 1`、直感の 0/-∞ は誤り)。
4. **2026-06-06 pivot 再確認で L-PhA-γ 撤回** (orchestrator independent pivot): 判断ログ #3 が「最大 supply 不能候補」とした h_pos_stam per-t density_t 正則性は **誤判定** (naming miss)。conv-gaussian 正則性 producer が in-tree に既存 (`isRegularDensityV2_convDensityAdd_gaussian` `:202` / `isBlachmanConvReady_convDensityAdd_gaussian` `:224`、両者 `@audit:ok`)、`density_t_eq` pin (`FisherInfoV2DeBruijn.lean:236`) で適用可能。前提は input pX の基本性質のみ (input IsRegularDensityV2 不要)。→ L-PhA-γ は RESOLVED、park 不要。**Phase A の唯一 genuine 残 gap = L-PhA-α (sum-instance 𝒩(0,2) reparam)**。producer の input-density 正則性 (`hreg_pX`/`hready_pX`/`h_fisher_X`) は honest precondition 追加で吸収 (load-bearing でない、producer audit 済)。CLAUDE.md「Mathlib 壁判定は独立 pivot で再確認」が機能した実例。
5. **2026-06-06 Gap 2 producer-一般化ルート RETRACTED → two-time route 確定** (orchestrator 機械検証 + pivot-advisor 独立裏取り): 判断ログ #4 と handoff が「Gap 2 = producer `hZX_law` を `gaussianReal 0 v` に一般化、~30-50 行、壁なし」とした評価は **誤り (楽観過大)**。実機械検証で確定: producer が構築する構造 `IsRegularDeBruijnHypV2` (`FisherInfoV2DeBruijn.lean:205`) の `Z_law : P.map Z = gaussianReal 0 1` と `density_t_eq` (variance t) は**フィールドでハードコード**、producer 引数の惰性ではない。sum 雑音 `Z_X+Z_Y ~ gaussianReal 0 2` では `Z_law(sum)=𝒩(0,1)` が**偽** → `h_reg_sum` は **uninhabitable** (型エラー、永久に埋まらない)。**この事実は既に code 側の独立監査が確定済**: `EPIStamToBridge.lean:552-582` GS-A3' (`@audit:ok`)「uninhabitable in that setting」「Z_law general-variance refactor is no longer needed」「Honest closure = two-time route」、`EPICase1SumProducer.lean` 削除済。docs (本 plan #4 + handoff) が code 訂正に追従していなかった。**正規ルート = `entropyPower_add_ge_case1_of_regular_twotime` (`EPICase1TwoTime.lean:1620`, `@audit:ok`) への載せ替え** (sum を別個 unit noise Z で摂動、variance-2 view 回避)。blast radius 3-4 file / 新規 5-8 lemma / 壁なし。唯一の analytic 内容 = `h_stam_supply` inverse-form producer だが `density_sum_{σ+τ}=conv(density_X_σ, density_Y_τ)` (convolution-splitting `g_{σ+τ}=g_σ*g_τ`) で `isStamInequalityHyp_via_step3` に帰着 (big-not-wall)。教訓: 「引数の一般化可能性」と「構造フィールドの制約」を区別せず docstring 自認を鵜呑みにすると詰みルートに投資する。着手前に既存独立監査ノート (GS-A3' 等) を grep するのが最安回避。CLAUDE.md「pivot が楽観しすぎることもある」「最終判定は実機械検証」の実例。

---

## 旧記述 (履歴、参照しない)

> 以下は 2026-05-24〜2026-06-06 の difference-form route + ratio 再frame route B の記述。W2-cluster CLOSED + 2-phase 再構成により **すべて obsolete**。新規着手では §Phase A / §Phase B を参照すること。難所診断 (G1 false-as-framed、G2 continuity wall、richness lift closure 等) は当時の route 固有で、現 lift+producer+methodX route には適用されない。詳細な旧 route 記録は git 履歴 (commit 履歴 + `epi-stam-to-conclusion-phaseA-plan.md` / `epi-csiszar-ratio-reframe-plan.md`) に残る。

- 旧 difference-form route (G1 deriv≤0 / G2 continuity / G3 rescale / G4 richness / W0-W2 集約): **判断 #2 で dead 削除**、ratio 形 (`csiszarLogRatioGap_*`) に pivot 済。
- 旧 Phase 0 (`IsStamToEPIScalingHyp` defect cleanup) / Phase 0-Plumbing (EPIPlumbing 3 件) / Phase A skeleton (A-1〜A-6) / Phase A-close: difference-form route 固有、現 route では `entropyPower_add_ge_case1_of_*` (`EPICase1RatioLimit.lean`) が assembly backbone を担う。
- 旧 closure criteria (23 件 `@audit:suspect` → `@audit:ok`、76 件 close): sorry-based migration 前の数字、現状と drift。

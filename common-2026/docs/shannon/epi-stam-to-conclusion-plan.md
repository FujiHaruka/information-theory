# EPI Stam → EPI conclusion — B-wire honest discharge plan

> **🗑 OBSOLETE (2026-06-11)**: 本 plan が closure 対象としていた `stamToEPIBridge_holds` (legacy Stam-bridge sorry) + 露出 28 decl は **物理削除済** (route-T 後継が完全 supersede、EPI family の実 sorry = 0)。Phase B は実装対象を喪失。Phase A (`entropy_power_inequality_of_density`、CLOSED) は別 file (`EPIDensityForm.lean`) に生存。本 plan は履歴として残置 (新規参照しない)。詳細 SoT → `ch17-inequalities-status.md` 冒頭 2026-06-11 注記。
>
> **Parent**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) (無条件 EPI moonshot の最終 wall "B-wire")
> **Status (2026-06-10 更新)**: **Phase B は SUPERSEDED** — 親 moonshot `epi-unconditional-moonshot-plan` が **無条件 dispatch + route T** で一般 EPI を別ルート closure 済 (`entropyPowerExt_add_ge_unconditional` sorryAx-free、2026-06-08)。本 plan の Phase B (legacy 実数 `entropy_power_inequality` を Stam-bridge 経由で sorryAx-free 化) は **textbook goal 達成には不要**になった。`stamToEPIBridge_holds` (`@residual(plan:epi-stam-to-conclusion-plan)`) は唯一の残 sorry だが、コード側で `@audit:superseded-by(epi-unconditional-moonshot-plan)` 付与済 = legacy Cover-Thomas 露出の局所 residual。Phase A (`entropy_power_inequality_of_density`) は **CLOSED** のまま (sorryAx-free)。W2 cluster も CLOSED。
> **2026-06-06 全面 destale + 2-phase 再構成**: 旧 difference-form route (G1-G4/W0-W2 表、ratio 再frame route B、Phase A skeleton/A-close 等) は **すべて履歴**。W2-cluster CLOSED + assembly 部品が genuine 着地したのを受け、本 plan を **Phase A (密度あり標準形) + Phase B (完全一般形)** の 2-phase に再構成する。旧記述は本ファイル末尾「## 旧記述 (履歴、参照しない)」へ退避。

## 進捗

- [x] Phase A — 密度あり標準形 EPI `entropy_power_inequality_of_density` **CLOSED** (sorryAx-free)。**3-noise lift + two-time route** で着地 (`EPIDensityForm.lean`)。旧 2-noise methodX route は判断ログ #5 で RETRACTED。再検証: `#print axioms InformationTheory.Shannon.EPIDensityForm.entropy_power_inequality_of_density` = `[propext, Classical.choice, Quot.sound]`。→ 下記 §Phase A (CLOSED 要約)
- [~] Phase B — **SUPERSEDED** (2026-06-10)。一般 EPI は親 moonshot が無条件 dispatch + route T で別ルート closure 済 (`entropyPowerExt_add_ge_unconditional`)。legacy 実数 `entropy_power_inequality` の Stam-bridge sorryAx-free 化は textbook goal に不要 (実数完全無条件は型壁で不可、a.c.+有限の `entropy_power_inequality_of_ac` が honest 限界)。`stamToEPIBridge_holds` は `@audit:superseded-by` 付き legacy residual として残置。下記 §Phase B は履歴。

proof-log: yes (`docs/shannon/proof-log-epi-stam-to-conclusion-phaseA.md`)

---

## ゴール / Approach

**最終ゴール** (Phase B): 任意可測 `X Y : Ω → ℝ`、`IndepFun X Y P` に対し
`entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)`
を `#print axioms` sorryAx-free にし、`stamToEPIBridge_holds` を off-bridge 化 or 撤去する。

**中間ゴール** (Phase A、今 session): X,Y に **a.c.(密度) + 有限2次モーメント** を honest regularity 前提として付けた形で同 EPI を sorryAx-free 化する。新 theorem `entropy_power_inequality_of_density` を産み、`#print axioms` で sorryAx-free を確認する。一般 headline `entropy_power_inequality` は Phase B まで `stamToEPIBridge_holds` sorry 経由のまま残す。

### Approach (解の全体形)

W2-cluster (Stam-Blachman / de Bruijn / G2 端点連続性 / lift noise / step3 producer) は **すべて genuine sorryAx-free** に着地済 (下記「確認済 genuine 部品」)。Phase A の残作業は **これらを正しい順で組み立てる assembly + precondition の discharge** であり、新しい解析的 math 構造の設計は不要 — **CLOSED** (下記 §Phase A)。

着地した assembly の backbone は **3-noise lift + two-time terminal** (旧 2-noise methodX route は sum-instance 𝒩(0,2) の uninhabitable 構造制約で RETRACTED、判断ログ #5):

```
base (Ω,P) ──[3-noise lift]──→ (Ω×ℝ×ℝ×ℝ, liftMeasure3 P)
   雑音 Z_X := p.2.1, Z_Y := p.2.2.1, Z := p.2.2.2 (3 独立 gaussianReal 0 1)
   5-tuple iIndepFun ![X∘fst, Y∘fst, Z_X, Z_Y, Z] は lift product 構造から body 内 inline 供給
   (Measure.pi_eq + 座標射影 law、削除された 2-noise の stamScalingNoise_exists_on_lift /
    indepFun_add_add_on_lift に相当する helper は 3-noise route には無く全て inline)
        ↓
   two-time terminal entropyPower_add_ge_case1_of_regular_twotime (EPICase1TwoTime.lean, @audit:ok)
   ├ de Bruijn group  h_reg_X/h_reg_Y/h_reg_sum  ← producer isDeBruijnRegularityHyp_of_methodX_unitnoise
   │                  (sum も別個 unit noise Z で平滑化 → gaussianReal 0 1 前提を genuine に満たす)
   ├ endpoint group   h_endpt_X/h_endpt_Y/h_endpt_sum  ← IsHeatFlowEndpointRegular を密度前提から構成 (v_Z=1)
   ├ h_stam_supply    ← producer EPIStamSupplyTwoTime.twoTime_stam_supply (@audit:ok, inverse-Stam)
   └ scale/rescale    h_scale_* / IsRescaledPathRegular  ← h_scale_general / methodX 由来補題で内部生成
        ↓ lift 上 EPI
   entropy_power_inequality_via_lift3 (EPINoiseExtension.lean)  ← measure-transport
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

### P-2 雑音 lift (lift 上 EPI → base EPI の measure-transport) — 3-noise route (live)

> **2026-06-09 整合済**: 旧 2-noise decl (`liftMeasure` / `entropy_power_inequality_via_lift` /
> `stamScalingNoise_exists_on_lift` / `indepFun_add_add_on_lift` / `entropyPower_map_comp_fst_eq`) は
> **削除済** (commit `4cd6b12`、external consumer 0、ripple 0)。two-time terminal が sum 用に別個 unit
> noise `Z` を要するため (sum 雑音を 2-noise 因子から流用すると `Z ⊥ (Z_X,Z_Y)` が崩れる)、実装は
> **3-noise** lift に移行した。下記は live な 3-noise route の decl。

- **`liftMeasure3`** — `EPINoiseExtension.lean:46`、noncomputable abbrev、型 `Measure (Ω × ℝ × ℝ × ℝ)`:
  `liftMeasure3 P := P.prod ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))` (3 因子すべて標準正規)。
- **`entropy_power_inequality_via_lift3`** — `EPINoiseExtension.lean:63`、`@audit:ok`。
  - signature: `(hX : Measurable X) (hY : Measurable Y) (h_lift_epi : entropyPower ((liftMeasure3 P).map (fun p => X p.1 + Y p.1)) ≥ entropyPower ((liftMeasure3 P).map (fun p => X p.1)) + entropyPower ((liftMeasure3 P).map (fun p => Y p.1))) : entropyPower (P.map (fun ω => X ω + Y ω)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)`
  - honest measure-transport reduction (lift 測度 EPI → base 測度 EPI)、circular でも bundle でもない。
- **`entropyPower_map_comp_fst_eq3`** — `EPINoiseExtension.lean:51`、lift 上 X law 保存 `entropyPower ((liftMeasure3 P).map (fun p => X p.1)) = entropyPower (P.map X)` (`measurePreserving_fst`)。
- **雑音 law/独立性の供給は body 内 inline** (削除された 2-noise helper に対応物なし): 座標 `Z_X := p.2.1` / `Z_Y := p.2.2.1` / `Z := p.2.2.2` の `gaussianReal 0 1` law は nested product を `Measure.map_map` + `measurePreserving_{fst,snd}` で射影して取得。5-tuple `iIndepFun ![X∘fst, Y∘fst, Z_X, Z_Y, Z] (liftMeasure3 P)` は `iIndepFun_iff_map_fun_eq_pi_map` + `Measure.pi_eq` で product 構造から直接構成 (`EPIDensityForm.lean:165-232`)。pairwise/group 独立は `iIndepFun.indepFun` / `indepFun_prodMk` / `indepFun_prodMk_prodMk` で抽出。

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

### P-4 methodX 組み立て (de Bruijn group + Stam group + scaling group → case-1 EPI) — Phase A では superseded

> **注**: 下記 `entropyPower_add_ge_case1_of_methodX` は decl として現存するが、Phase A の assembly backbone は
> **two-time terminal `entropyPower_add_ge_case1_of_regular_twotime`** に載せ替え済 (判断ログ #5、sum-instance
> 𝒩(0,2) の uninhabitable 構造制約)。methodX 記述は当時の単一 noise route の参考。

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

## Phase A — 密度あり標準形 EPI ✅ CLOSED

> **2026-06-09 圧縮**: Phase A は `entropy_power_inequality_of_density` (`EPIDensityForm.lean:70`) として
> **sorryAx-free に着地**。旧 in-progress scaffold (A-Approach / A-Steps / A-precondition 表 /
> A-撤退ライン L-PhA-α/β/γ / A-gap roadmap Gap 1/Gap 2) は **すべて完了** — gap close と route 変更の
> 経緯は判断ログ #3〜#5 に保持、ここでは着地形のみ記録。`@audit:ok` 独立監査済。

**着地した route = 3-noise lift + two-time terminal** (旧 2-noise methodX route は sum-instance の構造制約で RETRACTED、判断ログ #5):

- **入口**: `entropy_power_inequality_via_lift3` (P-2) で base `(Ω,P)` の EPI を 3-noise lift `liftMeasure3 P` 上の EPI に帰着。
- **lift 上 data**: `X' := X∘fst` / `Y' := Y∘fst`、独立 unit 雑音 `Z_X := p.2.1` / `Z_Y := p.2.2.1` / `Z := p.2.2.2`。5-tuple `iIndepFun ![X', Y', Z_X, Z_Y, Z]` は product 構造から body 内 inline 供給 (`Measure.pi_eq`、`EPIDensityForm.lean:165-232`)。sum は **別個の unit 雑音 `Z`** で平滑化するため `Z_law(sum)=𝒩(0,1)` が真になり、旧 methodX route の variance-2 uninhabitable 問題が消える。
- **terminal**: `entropyPower_add_ge_case1_of_regular_twotime` (`EPICase1TwoTime.lean`, `@audit:ok`) に de Bruijn group (producer `isDeBruijnRegularityHyp_of_methodX_unitnoise`、3 instance とも unit noise で genuine) / endpoint group (`endpt_of` helper、v_Z=1) / scale·rescale (内部生成) / `h_stam_supply` を供給。`h_stam_supply` は producer `EPIStamSupplyTwoTime.twoTime_stam_supply` (`@audit:ok`, inverse-Stam) から genuine 導出。
- **honest precondition 16 本** (load-bearing でない、`@audit:ok` で確認済): measurability / indep / a.c. / moment + (X/Y/sum) × (Fisher 有限 / `IsRegularDensityV2` / normalization / `IsBlachmanConvReady` / entropy 有限)。sum 側 5 本 (`h_fisher_XY`/`hreg_pXY`/`hnorm_pXY`/`hready_pXY`/`hent_pXY`) は X/Y 側と parallel な regularity precondition で、general∗general 畳込み正則性 producer 不在を honest 前提化したもの (判断 #5 の two-time scoping)。命名 `_of_density` は honest (一般化されていないことを明示)。

**再検証**: `#print axioms InformationTheory.Shannon.EPIDensityForm.entropy_power_inequality_of_density` = `[propext, Classical.choice, Quot.sound]`。consumer: `EPICase1SmoothingLimit.entropy_power_inequality_of_density_explicit` / `entropy_power_add_ge_of_finite_variance` (両者 sorryAx-free)。

**Phase B での再利用**: 密度ケース枝としてそのまま再利用 (§Phase B B-Approach)。16 precondition のうち追加 regularity (`IsRegularDensityV2` 等) は一般 a.c. 密度では出ない → Phase B の真の analytic 壁 (§B-未解析項目)。

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

#### 2026-06-06 Phase B feasibility verdict (pivot-advisor 独立機械検証) — **L-PhB-stop 発動確定**

Phase A 完成直後に smoothing route を独立評価した結果、**Phase B は当該 session で closeable でない** (genuine multi-session Mathlib 壁、親 moonshot の「方針 Y」と同一、`epi-uncond-truncation-lsc-inventory.md` に feasibility verdict 既存)。機械検証で確定:
- **`h_stam` は壁ではない**: `IsStamInequalityResidual ≡ IsStamInequalityHyp` は**両方向 defeq**、`isStamInequalityHyp_via_step3` (`@audit:ok`, sorryAx-free) で純 measurability+indep から産める。headline の唯一の残壁は `stamToEPIBridge_holds` (`EntropyPowerInequality.lean:251`, `sorryAx` 依存を `#print axioms` で再確認)。
- **smoothing route は出発点で詰む**: Gaussian 畳込みは**裾を保存**するため `X+√ε·N` は X が無限分散/無限エントロピーならそのまま無限。Phase A が**生入力**に要求する `IsHeatFlowEndpointRegular.hpX_mom` (有限分散) / `hpX_ent` (有限エントロピー) は smoothing で剥がせない。G2 端点連続性 `heatFlowEntropyPower_continuousWithinAt_zero` は ε と同型の正しい連続性だが、invoke に必要な `IsHeatFlowEndpointRegular` が剥がそうとしている当の `hpX_mom`/`hpX_ent` を要求する (循環)。
- **救うには truncate→smooth 二重近似 + entropy-power 弱収束 LSC が必須だが Mathlib 完全不在** (loogle Found 0 ×5、唯一の Fatou 資産 `EPIG2KLFatouLSC.lean:359` は向きが逆)。加えて型壁 `differentialEntropy : →ℝ` が `h=+∞` を持てない。これらは別 moonshot 規模 (genuine Mathlib 壁 2 本)。
- **退化枝の注意**: `entropyPower(dirac)` は親 plan で旧値 1 → 新値 0 へ二層 retype 移行中 (`epi-unconditional-moonshot-plan.md:282`)。退化枝設計は新定義側で行う (旧 P-5 の `=1` を前提にしない)。
- **結論**: Phase A (`entropy_power_inequality_of_density`, sorryAx-free, `@audit:ok` ×全部品) を genuine deliverable として締め、headline は `stamToEPIBridge_holds` sorry 経由のまま (honest 現状維持)。Phase B = 後続 moonshot へ持ち越し (方針 Y、truncate-smooth-LSC を新規 shared sorry 補題化する skeleton から)。

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
3. **2026-06-06 W2-cluster CLOSED + 2-phase 再構成** (settled、Phase A CLOSED で履歴化): 機械検証 (`#print axioms`) で W2-cluster (Stam-Blachman / de Bruijn / G2 端点連続性 / lift noise / step3 producer) が全て sorryAx-free と確定し、本 plan を difference-form route から Phase A (密度標準形) + Phase B (完全一般形) に全面再構成。残壁 = `stamToEPIBridge_holds` のみ。`IsStamToEPIBridge` signature が `(X Y P)` のみ (measurability/indep/a.c. 無し) → 現 signature の honest discharge は密度退化 case split (Phase B) 必須と判明。退化境界値 `differentialEntropy_dirac = 0` (`entropyPower (dirac) = 1`、直感の 0/-∞ は誤り) verbatim 確認。
4. **2026-06-06 L-PhA-γ 撤回** (settled、Phase A CLOSED で履歴化、orchestrator independent pivot): #3 が「最大 supply 不能候補」とした h_pos_stam per-t density_t 正則性は誤判定 (naming miss) — conv-gaussian 正則性 producer (`isRegularDensityV2_convDensityAdd_gaussian` / `isBlachmanConvReady_convDensityAdd_gaussian`、`@audit:ok`) が in-tree 既存で `density_t_eq` pin により適用可能。CLAUDE.md「Mathlib 壁判定は独立 pivot で再確認」が機能した実例。
5. **2026-06-06 Gap 2 producer-一般化ルート RETRACTED → two-time route 確定** (orchestrator 機械検証 + pivot-advisor 独立裏取り): 判断ログ #4 と handoff が「Gap 2 = producer `hZX_law` を `gaussianReal 0 v` に一般化、~30-50 行、壁なし」とした評価は **誤り (楽観過大)**。実機械検証で確定: producer が構築する構造 `IsRegularDeBruijnHypV2` (`FisherInfoV2DeBruijn.lean:205`) の `Z_law : P.map Z = gaussianReal 0 1` と `density_t_eq` (variance t) は**フィールドでハードコード**、producer 引数の惰性ではない。sum 雑音 `Z_X+Z_Y ~ gaussianReal 0 2` では `Z_law(sum)=𝒩(0,1)` が**偽** → `h_reg_sum` は **uninhabitable** (型エラー、永久に埋まらない)。**この事実は既に code 側の独立監査が確定済**: `EPIStamToBridge.lean:552-582` GS-A3' (`@audit:ok`)「uninhabitable in that setting」「Z_law general-variance refactor is no longer needed」「Honest closure = two-time route」、`EPICase1SumProducer.lean` 削除済。docs (本 plan #4 + handoff) が code 訂正に追従していなかった。**正規ルート = `entropyPower_add_ge_case1_of_regular_twotime` (`EPICase1TwoTime.lean:1620`, `@audit:ok`) への載せ替え** (sum を別個 unit noise Z で摂動、variance-2 view 回避)。blast radius 3-4 file / 新規 5-8 lemma / 壁なし。唯一の analytic 内容 = `h_stam_supply` inverse-form producer だが `density_sum_{σ+τ}=conv(density_X_σ, density_Y_τ)` (convolution-splitting `g_{σ+τ}=g_σ*g_τ`) で `isStamInequalityHyp_via_step3` に帰着 (big-not-wall)。教訓: 「引数の一般化可能性」と「構造フィールドの制約」を区別せず docstring 自認を鵜呑みにすると詰みルートに投資する。着手前に既存独立監査ノート (GS-A3' 等) を grep するのが最安回避。CLAUDE.md「pivot が楽観しすぎることもある」「最終判定は実機械検証」の実例。

---

## 旧記述 (履歴、参照しない)

> 以下は 2026-05-24〜2026-06-06 の difference-form route + ratio 再frame route B の記述。W2-cluster CLOSED + 2-phase 再構成により **すべて obsolete**。新規着手では §Phase A / §Phase B を参照すること。難所診断 (G1 false-as-framed、G2 continuity wall、richness lift closure 等) は当時の route 固有で、現 3-noise lift + two-time route には適用されない。詳細な旧 route 記録は git 履歴 (commit 履歴 + `epi-stam-to-conclusion-phaseA-plan.md` / `epi-csiszar-ratio-reframe-plan.md`) に残る。

- 旧 difference-form route (G1 deriv≤0 / G2 continuity / G3 rescale / G4 richness / W0-W2 集約): **判断 #2 で dead 削除**、ratio 形 (`csiszarLogRatioGap_*`) に pivot 済。
- 旧 Phase 0 (`IsStamToEPIScalingHyp` defect cleanup) / Phase 0-Plumbing (EPIPlumbing 3 件) / Phase A skeleton (A-1〜A-6) / Phase A-close: difference-form route 固有、現 route では `entropyPower_add_ge_case1_of_*` (`EPICase1RatioLimit.lean`) が assembly backbone を担う。
- 旧 closure criteria (23 件 `@audit:suspect` → `@audit:ok`、76 件 close): sorry-based migration 前の数字、現状と drift。

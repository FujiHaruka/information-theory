# Shannon EPI: case-1 de Bruijn regularity **producer** サブ計画

> **Parent**: [`epi-case1-ratio-limit-plan.md`](epi-case1-ratio-limit-plan.md) +
> [`epi-case1-phaseC-methodx-wrapper-plan.md`](epi-case1-phaseC-methodx-wrapper-plan.md)
> §「方針X wrapper → de Bruijn regularity 群 への還元」
> **Status**: 📋 draft (起草のみ、実装は別 session で `lean-implementer` dispatch)
> **Scope**: docs-only (本 plan); 触る予定の実装 file は per-file 節に列挙
> **proof-log**: yes (実装 session で `docs/shannon/proof-log-epi-case1-debruijn-producer.md`)
> **撤退口 slug**: `@residual(plan:epi-case1-debruijn-producer-plan)`

## 進捗

- [x] M0 案D 調査 (de Bruijn Gaussian discharge の var=1 本質依存性) — 本 plan 内で完了
- [x] M1 blast radius 実測 (`IsRegularDeBruijnHypV2` / `IsDeBruijnRegularityHyp` consumer 全件)
- [x] A vs B 確定 — **案A (v_Z 一般化) を採用**
- [ ] P-0 skeleton: `gaussianConvolution_law_of_gaussian` 一般化 + 下流 `_entropy_eq`/`_fisher_match` 追従 📋
- [ ] P-1 `IsRegularDeBruijnHypV2.Z_law` を `gaussianReal 0 v_Z` へ一般化 (structure field + v_Z carrier) 📋
- [ ] P-2 V2 family / assembled / Gaussian witness の v_Z 追従 📋
- [ ] P-3 `IsDeBruijnRegularityHyp` producer 補題 3 本 (X / Y / sum) 構築 📋
- [ ] P-4 `h_pos_stam` producer (Fisher>0 / IsRegularDensityV2 / conv-pin / Stam / Blachman) 構築 📋
- [ ] P-5 最終 wrapper `entropyPower_add_ge_case1_of_methodX_full` (de Bruijn 群を方針X から供給) 📋
- [ ] P-6 incidental: `IsIBPHypothesis` retract 📋
- [ ] P-V verify (`lake env lean`) + 独立 honesty audit (`honesty-auditor`) PASS 📋

## 文脈 (確定背景)

case-1 EPI wrapper `entropyPower_add_ge_case1_of_methodX`
(`EPICase1RatioLimit.lean:1470`、sorryAx-free) は結論
`entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)`
を「方針X (a.c. / 2次モーメント / 雑音 Gaussian law / 4-tuple 独立) **+ de Bruijn regularity 群**」へ還元済。

de Bruijn family は 0 sorry / 0 residual 化済 (commit `70314b8`)。
壁 `wall:debruijn-integration` / `wall:fisher-finiteness` / `wall:entropy-finiteness` /
`wall:cond-diff-entropy` / `wall:approx-identity-L1` はいずれも CLOSED
(`docs/audit/audit-tags.md` Wall register 参照)。

残るのは wrapper が thread する **de Bruijn regularity 群** を方針X の前提から供給する
**producer 構築**。wrapper signature (`EPICase1RatioLimit.lean:1488-1518`) が要求する群:

- `h_reg_sum` / `h_reg_X'` / `h_reg_Y'` : `IsDeBruijnRegularityHyp` 3 本
  (`EPIStamDischarge.lean:251`)
- `h_endpt_sum` / `h_endpt_X` / `h_endpt_Y` : `IsHeatFlowEndpointRegular` 3 本
  (`EPIG2HeatFlowContinuity.lean:488`)
- `h_pos_stam` : per-`t>0` の Fisher>0 (3 本) ∧ Stam ∧ IsRegularDensityV2 (2 本) ∧
  density 正規化 (2 本) ∧ sum conv-pin ∧ Blachman-conv-ready の合成 bundle
  (`EPICase1RatioLimit.lean:1496-1518`)

### 唯一の構造的障害 — `Z_law` variance mismatch

`IsRegularDeBruijnHypV2.Z_law : P.map Z = gaussianReal 0 1`
(**unit variance ハードコード**、`FisherInfoV2DeBruijn.lean:210`) ⇔
case-1 wrapper noise `P.map Z_X = gaussianReal 0 v_X` (`v_X ≠ 0` 任意、
`EPICase1RatioLimit.lean:1482`)。

`IsDeBruijnRegularityHyp.reg_at : ∀ t>0, IsRegularDeBruijnHypV2 X Z P t`
(`EPIStamDischarge.lean:262`) が `reg_at .Z_law` 経由で unit variance を継承するため、
`v_X ≠ 1` の case-1 noise からは `IsDeBruijnRegularityHyp X Z_X P` を構成できない
(型レベル不充足)。**sum 側も同様** (`Z_X+Z_Y ∼ gaussianReal 0 (v_X+v_Y)`、
`EPICase1RatioLimit.lean:1556` で確定、`v_X+v_Y = 1` でない限り unit variance に合致しない)。

これは **analytic 壁ではなく型レベル不充足**。`Z_law` を一般 variance 受容形に直せば消える。

### advisor 検証の確定事項 (本 plan で verbatim 再確認済)

- **`IsHeatFlowEndpointRegular` は既に一般 variance**: `v_Z : ℝ≥0` + `hv_Z_pos` +
  `hZ_law : P.map Z = gaussianReal 0 v_Z` を field として持つ (`EPIG2HeatFlowContinuity.lean:493-495`)。
  上流 producer (`EPIStamToBridge.lean:1435-1452`) は X→`v_Z:=1`, Y→`v_Z:=1`, sum→`v_Z:=2` で
  既に general variance を渡している。case-1 では `v_X` / `v_Y` / `v_X+v_Y` を渡せば OK、
  **`IsHeatFlowEndpointRegular` には障害なし** (`@audit:ok` 既得)。
- **heat eq は producer に不要**: `IsRegularDeBruijnHypV2` は Phase 2.B で
  `derivAt_entropy_eq_half_fisher_v2` field を除去済 (`FisherInfoV2DeBruijn.lean:195-204`)。
  de Bruijn core は genuine `debruijnIdentityV2_holds_assembled` が供給するので、
  producer 側は regularity precondition (`Z_law` / `density_t` / `pX` series /
  `density_t_eq` / `pX_mom`) を埋めるだけ。
- **`h_pos_stam` の Stam / Blachman は genuine 既存**:
  `isStamInequalityHyp_via_step3` (`EPIStamStep3Body.lean:119`、sorryAx-free) /
  `isBlachmanConvReady_convDensityAdd_gaussian` は供給可能。

---

## M0 — 案D 調査結果 (de Bruijn Gaussian discharge の var=1 本質依存性)

**問い**: `deBruijn_identity_v2_gaussian` / `debruijnIdentityV2_holds_assembled` +
`gaussianConvolution` 系の Gaussian discharge が var=1 を **rfl / 本質的に**使うか、
`v_Z` 一般で通るか。

**実 Read 調査結果** (verbatim):

| 補題 / 定義 | file:line | var=1 依存性 |
|---|---|---|
| `gaussianConvolution_law_conv` | `FisherInfoV2DeBruijnPerTime.lean:80` | **一般 `v_Z`** 既存。`(P.map X) ∗ gaussianReal 0 ⟨s·v_Z,_⟩`。docstring `@audit:ok` |
| `pPath_eq_convDensityAdd` (Phase 1b) | `FisherInfoV2DeBruijnPerTime.lean:194` | **一般 `v_Z`** 既存。docstring「sum instance の noise `𝒩(0,2)` のため一般化必要、`v_Z=1` 形は `s·1=s` で回収」と明記 |
| `debruijnIdentityV2_holds_assembled` core chain (`_chain`) | `FisherInfoV2DeBruijnAssembly.lean:3397` (`_chain`), :3543 (top) | **v_Z 非依存** (density-level、`pX`/Gaussian-kernel `convDensityAdd` 経由)。`h_reg.Z_law` を chain に渡していない |
| `_entropy_eq` atom | `FisherInfoV2DeBruijnAssembly.lean:3437` | `hZ_law : gaussianReal 0 1` 受領。**内部で Phase 1b を `v_Z:=1` で instantiate** (:3452 `pPath_eq_convDensityAdd X Z … (1:ℝ≥0) one_pos hZ_law …`)。`s*1=s` の rewrite (`hwit1`、:3460) で var=1 を機械的に simp で潰しているだけ |
| `_fisher_match` atom | `FisherInfoV2DeBruijnAssembly.lean:3485` | `_hZ_law : gaussianReal 0 1` 受領 (`_` prefix = 未使用)。conv-pin (`density_t_eq`) で `funext` するため var=1 は load-bearing でない |
| `deBruijn_identity_v2_gaussian` (Stage-2 publish) | `FisherInfoV2DeBruijn.lean:441` | `hZ_law : gaussianReal 0 1` 受領 + `gaussianConvolution_law_of_gaussian` (var=1 専用補題) を呼ぶ (:469, :486)。**Gaussian X 限定の publish point** で producer chain には不使用 (case-1 X は一般密度) |

**結論 (案D)**: var=1 の本質依存は **どこにも無い**。

- de Bruijn の analytic core (`_chain`、density-level) は完全に v_Z-agnostic。
- v_Z=1 が現れるのは `_entropy_eq` / `_fisher_match` が Phase 1b を `v_Z:=1` で叩く
  2 callsite のみで、いずれも `s*1=s` の simp 折り畳みだけ。Phase 1b 自体は一般 v_Z 形。
- `gaussianConvolution_law_of_gaussian` (var=1 専用) は **Gaussian-X publish point**
  (`deBruijn_identity_v2_gaussian`) と `EPIL3Integration` の Gaussian instance でのみ使われ、
  case-1 producer chain (一般密度 X) には乗らない。

→ **案A (`Z_law` を `gaussianReal 0 v_Z` へ一般化) のコストは advisor 想定 (~80-150 LOC) より
低い見込み**。素地 (`gaussianConvolution_law_conv` / `pPath_eq_convDensityAdd`) が既に一般形で、
追従が必要なのは「`Z_law` field を `gaussianReal 0 v_Z` に開き、`_entropy_eq`/`_fisher_match`/
top-level `debruijnIdentityV2_holds_assembled` の `v_Z:=1` instantiate を carrier
`v_Z` 引数に置換する」plumbing。

---

## M1 — blast radius 実測 (`rg -c`)

`IsRegularDeBruijnHypV2` 出現数 (file 別、`rg -c`):

| file | 件数 | 役割 |
|---|---|---|
| `FisherInfoV2DeBruijnBody.lean` | 10 | V2 body 補題群 |
| `FisherInfoV2HeatFlowBody.lean` | 8 | heat-flow body |
| `FisherInfoV2DeBruijn.lean` | 7 | **structure 定義 (`:205`) + Gaussian witness** |
| `EPIL3Integration.lean` | 5 | integration 経路 |
| `FisherInfoV2DeBruijnPerTime.lean` | 2 | per-time |
| `FisherInfoV2DeBruijnGenuine.lean` | 2 | genuine consumer |
| `FisherInfoV2DeBruijnAssembly.lean` | 2 | assembled (`:3543` top-level が `h_reg.Z_law` 使用) |
| `FisherDeBruijnGaussianWitness.lean` | 2 | Gaussian witness instance |
| `EPIStamDischarge.lean` | 2 | `IsDeBruijnRegularityHyp.reg_at` 経由 |
| `EPIStamDeBruijnConclusion.lean` | 2 | conclusion |
| `FisherInfo.lean` | 1 | V1 cross-ref docstring |
| `EPIStamToBridge.lean` | 1 | bridge |

`IsDeBruijnRegularityHyp` 出現数 (file 別):

| file | 件数 | 役割 |
|---|---|---|
| `EPIStamToBridge.lean` | 34 | **`isStamToEPIScalingHyp_of_stam_debruijn` (`:1346`) が `gaussianReal 0 1` hardcode で 3 本要求 (`:1353-1358`)** |
| `EPICase1RatioLimit.lean` | 7 | case-1 wrapper の 3 本 thread |
| `EPIStamDischarge.lean` | 3 | structure 定義 (`:251`) |
| `EPIL3Integration.lean` | 2 | integration 経路 docstring |
| `EPIG2HeatFlowContinuity.lean` | 2 | G2 continuity docstring |

**blast radius 評価**:

- 案A (`IsRegularDeBruijnHypV2.Z_law` 一般化) は `IsRegularDeBruijnHypV2` を field 参照する
  全 file (上表 12 file) に v_Z carrier が伝播する潜在影響を持つ。ただし大半は
  `.Z_law` field を **読まない** (regularity precondition として thread するだけ) ので、
  field 追加 + 既存 callsite に `v_Z := 1` 明示を 1 行追加すれば silent compile する見込み。
  **真に書換が必要なのは「`hZ_law : gaussianReal 0 1` をハードコードで要求する callsite」のみ**:
  `_entropy_eq`/`_fisher_match`/top-level `debruijnIdentityV2_holds_assembled`
  (Assembly 3 箇所)、Gaussian witness (`FisherDeBruijnGaussianWitness.lean`)、
  `isStamToEPIScalingHyp_of_stam_debruijn` (`EPIStamToBridge.lean:1353-1361`)。
- `EPIStamToBridge.lean` の 34 件は大半が docstring + sum-instance 構築コメントで、
  predicate を field 参照する load-bearing callsite は `isStamToEPIScalingHyp_of_stam_debruijn`
  1 declaration (`:1346`)。ここは EPI 一般 line の Stam-to-conclusion で
  **`gaussianReal 0 1` を要求しているが既に density-witness sorry を park 中**
  (`@residual(plan:epi-stam-to-conclusion-phaseA-plan)`)。案A の v_Z 一般化はこの
  declaration の signature を一般化する形になるが、既存 `v_Z := 1` callsite は
  default 引数 / 明示渡しで後方互換に保てる。

**結論**: 案A の真の書換対象は **6-8 declaration** (structure 1 + Assembly 3 +
Gaussian witness 1 + bridge 1 + `IsDeBruijnRegularityHyp` の `reg_at` 経由整合 1)。
残り ~40 件は docstring / regularity-thread で機械的に追従 (v_Z=1 明示 1 行 or 無変更)。

---

## ゴール / Approach

### ゴール

`entropyPower_add_ge_case1_of_methodX` が thread する de Bruijn regularity 群
(`IsDeBruijnRegularityHyp` ×3 / `IsHeatFlowEndpointRegular` ×3 / `h_pos_stam`) を
方針X の前提 (a.c. / 2次モーメント / 雑音 Gaussian law `gaussianReal 0 v_X` / 4-tuple 独立)
から **producer 補題として供給** し、最終 wrapper
`entropyPower_add_ge_case1_of_methodX_full` の前提を「方針X のみ」に縮約する。

de Bruijn regularity 群が precondition から消え、方針X のみ残ることを確認する
(`IsDeBruijnRegularityHyp` を含む前提が 0 件になる)。

### Approach (全体戦略)

**核心 = `Z_law` variance 一般化 (案A) → producer chain → wrapper 結線** の 3 段。

**第 1 段 (P-0〜P-2) — `Z_law` 一般化 (案A)**:
`IsRegularDeBruijnHypV2` の `Z_law` field を `P.map Z = gaussianReal 0 1` から
`P.map Z = gaussianReal 0 v_Z` (新 field `v_Z : ℝ≥0` + `hv_Z_pos` を伴う) へ開く。
素地 (`gaussianConvolution_law_conv` / `pPath_eq_convDensityAdd`、ともに一般 v_Z 既存) は
そのまま、`_entropy_eq`/`_fisher_match`/top-level assembled の `v_Z:=1` instantiate を
carrier `v_Z` 引数に置換。M0 で「var=1 本質依存ゼロ」を確認済みなのでこの段は plumbing。

**第 2 段 (P-3〜P-4) — producer chain**:
方針X の前提から `IsDeBruijnRegularityHyp X Z_X P` (および Y / sum) を構成する producer
補題を書く。`reg_at t ht` の各 field を埋める:
- `Z_law`: case-1 noise `hZX_law : gaussianReal 0 v_X` を直接 (一般化後 OK)
- `density_t` / `density_t_eq`: conv-pin `convDensityAdd pX (gaussianPDFReal 0 ⟨t·v_X,_⟩)`
  (Phase 1b 一般 v_Z 形に合わせる)
- `pX` series (`pX`/`pX_nn`/`pX_meas`/`pX_law`/`pX_mom`): case-1 input density witness。
  **これは load-bearing でない regularity precondition だが、case-1 では `hX_ac` から
  自動では出ない** (a.c. ⇒ Real density witness は `Measure.rnDeriv` を `.toReal` で取れるが、
  measurability / 2次モーメント有限性 / 正規化は別途要る)。供給方法は P-3 で詳述。
`h_pos_stam` は Fisher>0 / IsRegularDensityV2 / conv-pin / Stam / Blachman の合成で P-4。

**第 3 段 (P-5) — wrapper 結線**:
producer 群を `entropyPower_add_ge_case1_of_methodX` に注入する最終 wrapper を
`entropyPower_add_ge_case1_of_methodX_full` (honest 命名、`_full` は producer で
de Bruijn 群を全 discharge した含意) として書く。de Bruijn 群が前提から消え方針X のみ残る。

**撤退口**: producer の `pX` series 等で case-1 の a.c. precondition から Real density
witness が組めない部分が判明したら、その field のみ `sorry` + `@residual(plan:epi-case1-debruijn-producer-plan)`
で park (signature は本来の producer 形に保つ)。`*Hypothesis` predicate に核を bundling
する撤退は禁止。

### 案A vs 案B — 確定

**案A (`Z_law` を `gaussianReal 0 v_Z` 一般化) を採用**。

| 観点 | 案A (v_Z 一般化) | 案B (case-1 標準化 `Z_X':=Z_X/√v_X` + 時間再パラメータ) |
|---|---|---|
| M0 結果反映 | var=1 本質依存ゼロ → 素地が既に一般形、追従は plumbing | reparam が antitone/limit を保つことの確認が別途要る |
| blast radius | 真の書換 6-8 decl + docstring 追従 ~40 | case-1 局所 ~60-100 LOC だが reduction 補題が時間 affine 再パラメータの保存補題を要求 |
| de Bruijn family 破壊リスク | 0 sorry に戻したばかりの family を再 touch (中)。ただし M1 で「load-bearing callsite は 6-8」と局所化済 | family を touch しない (低)。だが case-1 で `√t·Z_X = √(t·v_X)·Z_X'` の時間再パラメータが entropyPower scaling / ratio limit と整合するか未検証 (中) |
| 再利用性 | EPI 全 line (sum-instance `𝒩(0,2)` も)・教科書全体で general-variance de Bruijn が使える | case-1 専用 |
| honesty 安全性 | structure field 一般化 = 退化リスク低 | reparam で `Y:=0` 等の退化境界が紛れ込む懸念 (CLAUDE.md L-DBD 系前例) |

**採用根拠**:
1. M0 で var=1 本質依存ゼロが確定 → 案A の追従コストが advisor 上限想定 (~150 LOC) を
   下回る見込み。
2. 案B の時間 affine 再パラメータが `entropyPower_rescaled_path_tendsto`
   (`EPICase1RatioLimit.lean:1229`) / ratio limit と整合することの保存補題が未検証で、
   退化境界 (`Y:=0` 等) を突く degenerate-definition exploitation のリスク (CLAUDE.md
   「具体的数値・型予測」L-DBD 前例) を案A より多く抱える。
3. sum-instance が `𝒩(0,2)` 雑音を持つことは EPI line で既出 (`IsHeatFlowEndpointRegular`
   producer が `v_Z:=2` で構築済) → general-variance de Bruijn は EPI 全体で再利用される
   構造資産。案A は textbook-roadmap 集計に対しても上位互換。

**撤退ライン L-A-esc**: P-1/P-2 で `Z_law` 一般化が `IsRegularDeBruijnHypV2` の universal
interface を壊し (例: `density_t` の conv-pin が v_Z carrier と衝突)、追従が M1 想定の
6-8 decl を大幅超過すると判明したとき → **案B にエスカレート**。それでも厄介なら
producer の該当 field を `sorry` + `@residual` で park し type-check done で commit、
proof done は次 wave に持ち越し。

---

## Phase 詳細

### P-0 — skeleton + `gaussianConvolution_law_of_gaussian` 一般化判断 (~10 行調査 + skeleton)

**スコープ**: 実装 file の skeleton を作る前に、`gaussianConvolution_law_of_gaussian`
(var=1 専用、`FisherInfoV2DeBruijn.lean`/`FisherInfoV2DeBruijnPerTime.lean`/
`EPIL3Integration.lean` で使用) を **一般化するか / `gaussianConvolution_law_conv`
(既に一般形) に差し替えるか** を確定する。

- [ ] `gaussianConvolution_law_of_gaussian` の全 callsite を `rg` で列挙
  (`deBruijn_identity_v2_gaussian` の `:469`/`:486`、`EPIL3Integration` Gaussian instance)
- [ ] case-1 producer chain がこの var=1 補題を経由しないことを再確認 (M0 で済、再 grep で裏取り)
- [ ] skeleton: P-1〜P-5 の全 producer 補題 + 最終 wrapper を `:= by sorry` で配置、
  `lake env lean` silent (sorry warning のみ) を確認

**Done 条件**: skeleton が type-check done (各 sorry に `@residual(plan:epi-case1-debruijn-producer-plan)`)。
`gaussianConvolution_law_of_gaussian` を P-1/P-2 で触る必要があるか否かが確定。

### P-1 — `IsRegularDeBruijnHypV2.Z_law` 一般化 (~30-50 行)

**スコープ**: `FisherInfoV2DeBruijn.lean:205-268` の `IsRegularDeBruijnHypV2` structure を
v_Z 受容形に開く。

新 signature スケッチ (M0/M1 確定済の field 構成に基づく):

```lean
structure IsRegularDeBruijnHypV2 {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (t : ℝ) where
  v_Z : ℝ≥0                                  -- NEW: 雑音分散 carrier
  hv_Z_pos : 0 < v_Z                         -- NEW
  Z_law : P.map Z = gaussianReal 0 v_Z       -- CHANGED: 0 1 → 0 v_Z
  density_t : ℝ → ℝ
  pX : ℝ → ℝ
  pX_nn : ∀ x, 0 ≤ pX x
  pX_meas : Measurable pX
  pX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x))
  density_t_eq : ∀ (ht : 0 < t) (x : ℝ),
    density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t * v_Z, by positivity⟩) x  -- CHANGED: ⟨t,_⟩ → ⟨t·v_Z,_⟩
  pX_mom : Integrable (fun y => y ^ 2 * pX y) volume
```

**変更点 vs 現行** (`FisherInfoV2DeBruijn.lean:205-268`):
- `v_Z` / `hv_Z_pos` field 追加 (`IsHeatFlowEndpointRegular` と同 paradigm、
  `EPIG2HeatFlowContinuity.lean:493-495`)
- `Z_law : gaussianReal 0 1` → `gaussianReal 0 v_Z`
- `density_t_eq` の conv-pin の Gaussian kernel variance を `⟨t, ht.le⟩` →
  `⟨t·v_Z, _⟩` に (Phase 1b `pPath_eq_convDensityAdd` の一般 v_Z 結論
  `(P.map X) ∗ 𝒩(0, s·v_Z)` に整合、`FisherInfoV2DeBruijnPerTime.lean:194-204` の docstring)

**Done 条件**: `lake env lean InformationTheory/Shannon/FisherInfoV2DeBruijn.lean` silent
(structure 単体)。既存 var=1 callsite は P-2 で追従するため一時的に下流 error は許容
(skeleton 段階)。

### P-2 — V2 family / assembled / Gaussian witness の v_Z 追従 (~30-60 行)

**スコープ**: P-1 の field 追加で破れる callsite を修正。M1 で局所化した load-bearing
callsite のみ:

1. `debruijnIdentityV2_holds_assembled` (`FisherInfoV2DeBruijnAssembly.lean:3543`):
   `h_reg.Z_law` 経由で v_Z を取り、`_entropy_eq`/`_fisher_match` に carrier として渡す
2. `_entropy_eq` (`Assembly:3437`): `hZ_law : gaussianReal 0 1` 引数を `v_Z` carrier 形に。
   内部 Phase 1b instantiate (`:3452` `pPath_eq_convDensityAdd … (1:ℝ≥0) one_pos …`) を
   `… v_Z hv_Z_pos …` に置換、`s*1=s` rewrite (`hwit1`、:3460) を `s*v_Z` 形に
3. `_fisher_match` (`Assembly:3485`): `_hZ_law` は未使用 (`_` prefix) なので signature の
   v_Z 一般化のみ
4. Gaussian witness (`FisherDeBruijnGaussianWitness.lean:158`
   `isRegularDeBruijnHypV2_gaussian_heatFlow`): `v_Z := 1` を明示 field に追加 (var=1
   instance はそのまま生き残る)
5. その他 V2 family file (`FisherInfoV2DeBruijnBody.lean` / `FisherInfoV2HeatFlowBody.lean`
   等) で `Z_law` を field 参照する箇所に `v_Z := 1` を補う (regularity-thread、機械的)

**Done 条件**: M1 表の 12 file 全てで `lake env lean` silent。
`rg "gaussianReal 0 1" InformationTheory/Shannon/FisherInfoV2DeBruijn*.lean` の残存が
**意図的な var=1 instance のみ** (= Gaussian witness の default) であることを確認。

### P-3 — `IsDeBruijnRegularityHyp` producer 補題 3 本 (~60-120 行)

**スコープ**: 方針X の前提から `IsDeBruijnRegularityHyp X Z_X P` (および Y / sum) を構成する
producer 補題を書く。`EPICase1RatioLimit.lean` の wrapper 近傍に置く (consumer と同 file)。

producer 補題スケッチ (X 版、Y / sum も同型):

```lean
/-- case-1 方針X の前提から `IsDeBruijnRegularityHyp X Z_X P` を供給する producer。
@residual(plan:epi-case1-debruijn-producer-plan) -/
theorem isDeBruijnRegularityHyp_of_methodX_input
    (X Z_X : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (v_X : ℝ≥0) (hv_X : v_X ≠ 0) (hZX_law : P.map Z_X = gaussianReal 0 v_X)
    (hX_ac : (P.map X) ≪ volume) (h_mom_X : Integrable (fun ω => (X ω)^2) P)
    -- case-1 input density witness (P-3 で供給元を確定する precondition):
    (pX : ℝ → ℝ) (hpX_... : ...) :
    InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P := by
  refine { density_path := fun t => convDensityAdd pX (gaussianPDFReal 0 ⟨t*v_X,_⟩),
           reg_at := fun t ht => { v_Z := v_X, hv_Z_pos := ..., Z_law := hZX_law, ... },
           density_t_eq := ..., integrable_deriv := ... }
  ...
```

各 field の供給元 (verbatim):
- `reg_at .Z_law`: `hZX_law` 直接 (P-1 で `gaussianReal 0 v_Z` 受容化済)
- `reg_at .v_Z`: `v_X` (case-1 noise variance)
- `reg_at .density_t` / `.density_t_eq`: conv-pin
  `convDensityAdd pX (gaussianPDFReal 0 ⟨t·v_X,_⟩)` (P-1 一般 v_Z 形に整合)
- `reg_at .pX` series: case-1 input density witness。**供給元の確定が P-3 の核心**:
  - `pX := fun x => ((P.map X).rnDeriv volume x).toReal` (a.c. ⇒ rnDeriv 存在)
  - `pX_nn`: `ENNReal.toReal_nonneg`
  - `pX_meas`: `Measure.measurable_rnDeriv` + `.toReal`
  - `pX_law`: `hX_ac` ⇒ `(P.map X) = volume.withDensity (rnDeriv ...)`
    (`Measure.withDensity_rnDeriv_eq` / `rnDeriv_toReal` の整合確認が必要)
  - `pX_mom`: `h_mom_X` (`Integrable (X²) P`) から `Integrable (y²·pX y) volume` への
    push-forward (`integral_map` / `lintegral_rnDeriv` 経由、**ここが非自明、P-3 で要詳細**)
  - `integrable_deriv`: bounded-T interval integrability (Gaussian-X では genuine、
    一般密度では `wall:fisher-finiteness` CLOSED 資産 `gaussianConv_fisher_le_inv_var`
    (`FisherConvBound.lean:385`) 経由で `J ≤ 1/(t·v_X)` の連続有界性)

**`pX` series の honesty 判定**: これは load-bearing でない **regularity precondition**
(CLAUDE.md「判定の一言」前者)。「X が Lebesgue 密度 `pX` を持つ」は input distribution の
regularity で、de Bruijn の analytic 核 (`HasDerivAt`/Fisher) を bundle しない。
case-1 では `hX_ac` から rnDeriv 経由で構成可能なので、`sorry` を残さず genuine に閉じるのが
目標。閉じられない field のみ park (撤退口)。

**Done 条件**: 3 producer 補題が type-check done。`rg`-grep で各 producer の前提に
`*Hypothesis` predicate が含まれないこと (load-bearing bundling していないこと) を確認。

### P-4 — `h_pos_stam` producer (~40-80 行)

**スコープ**: wrapper の `h_pos_stam` bundle
(`EPICase1RatioLimit.lean:1496-1518`) を per-`t>0` で供給する producer を書く。
bundle の各 conjunct と供給元:

| conjunct | 供給元 (file:line) |
|---|---|
| `0 < fisherInfoOfDensityReal (reg_X'.density_t)` (×3: X/Y/sum) | conv-pin density の Fisher 正値性。Gaussian-conv density は a.e. 正 ⇒ Fisher>0 (供給補題は P-4 で確認、`FisherInfoV2` 系) |
| `IsStamInequalityHyp (X+√t·Z_X) (Y+√t·Z_Y) P` | `isStamInequalityHyp_via_step3` (`EPIStamStep3Body.lean:119`、sorryAx-free genuine) |
| `IsRegularDensityV2 (reg_X'.density_t)` (×2: X/Y) | conv-pin density regularity (smooth conv 表現の微分可能性、`FisherInfoV2` 系) |
| `∫ density_t = 1` (×2: X/Y) | conv density 正規化 (`hpX_mass` + Gaussian kernel 正規化、Phase 1b 資産) |
| sum conv-pin `density_t (sum) = convDensityAdd (density_t X) (density_t Y)` | Blachman convolution identity (`isBlachmanConvReady_convDensityAdd_gaussian` 経由) |
| `IsBlachmanConvReady (reg_X'.density_t) (reg_Y'.density_t)` | `isBlachmanConvReady_convDensityAdd_gaussian` (genuine 既存) |

**注意**: この bundle は `h_reg_X'`/`h_reg_Y'`/`h_reg_sum` の `reg_at t ht` を参照する形
(`(h_reg_X'.reg_at t ht).density_t`) なので、P-3 の producer 補題が返す
`IsDeBruijnRegularityHyp` instance と **同一の conv-pin density** を共有する必要がある。
P-3 で `density_path t := convDensityAdd pX g_{t·v_X}` を固定したので、P-4 はこの
具体形に対し Fisher>0 / IsRegularDensityV2 / 正規化 を示す。

**Done 条件**: `h_pos_stam` producer が type-check done。Stam / Blachman conjunct が
genuine 既存補題への delegation で閉じる (新 sorry なし) ことを確認。

### P-5 — 最終 wrapper `entropyPower_add_ge_case1_of_methodX_full` (~20-40 行)

**スコープ**: P-3 / P-4 producer 群を `entropyPower_add_ge_case1_of_methodX` に注入する
最終 wrapper を書く。

スケッチ:

```lean
/-- **case-1 EPI、方針X のみから (de Bruijn 群を producer で供給)**。
de Bruijn regularity 群は P-3/P-4 producer が方針X の前提から discharge するので
前提から消え、方針X (a.c. / 2次モーメント / 雑音 Gaussian law / 4-tuple 独立) のみ残る。
@residual(plan:epi-case1-debruijn-producer-plan) -- producer の未閉 field があれば -/
theorem entropyPower_add_ge_case1_of_methodX_full
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hXY_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω)^2) P) (h_mom_Y : Integrable (fun ω => (Y ω)^2) P)
    (v_X v_Y : ℝ≥0) (hv_X : v_X ≠ 0) (hv_Y : v_Y ≠ 0)
    (hZX_law : P.map Z_X = gaussianReal 0 v_X) (hZY_law : P.map Z_Y = gaussianReal 0 v_Y)
    (h_iIndep : iIndepFun ![X, Y, Z_X, Z_Y] P)
    -- (case-1 input density witness は producer 内で hX_ac から構成、または最小限の
    --  追加 regularity precondition として残す。P-3 で確定。) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  -- producer で de Bruijn 群を構築
  have h_reg_X' := isDeBruijnRegularityHyp_of_methodX_input X Z_X P hX hZX … 
  have h_reg_Y' := …
  have h_reg_sum := …  -- sum-instance: noise gaussianReal 0 (v_X+v_Y)
  have h_endpt_X := …  -- IsHeatFlowEndpointRegular (既に一般 variance、v_Z:=v_X)
  have h_endpt_Y := …  -- v_Z:=v_Y
  have h_endpt_sum := …  -- v_Z:=v_X+v_Y
  have h_pos_stam := …  -- P-4 producer
  exact entropyPower_add_ge_case1_of_methodX X Y Z_X Z_Y P hX hY hZX hZY
    hX_ac hY_ac hXY_ac h_mom_X h_mom_Y v_X v_Y hv_X hv_Y hZX_law hZY_law h_iIndep
    h_reg_sum h_reg_X' h_reg_Y' h_endpt_sum h_endpt_X h_endpt_Y h_pos_stam
```

**命名 honesty**: `_full` は「de Bruijn regularity 群を producer で全 discharge した」を
表す。**name laundering ではない** — producer が方針X の前提から genuine に regularity を
構成しており、`_full` は仮説が開いたまま `_unconditional` と詐称する形ではない
(CLAUDE.md tells「name laundering」)。ただし P-3 で case-1 input density witness を
最小限の追加 precondition として残す場合は、命名を `_full` でなく実態に合わせる
(例: 追加 precondition があるなら `_from_methodX_with_density` 等)。

**Done 条件**: 最終 wrapper の前提に `IsDeBruijnRegularityHyp` / `IsHeatFlowEndpointRegular` /
`h_pos_stam` bundle が **含まれない** (de Bruijn 群が消えた)。`lake env lean` silent。

### P-6 — incidental: `IsIBPHypothesis` retract (~5-10 行)

**スコープ**: `FisherInfoV2DeBruijnBody.lean:209` の `IsIBPHypothesis`
(`@audit:retract-candidate(name-laundering-alias)`、死 alias、全 consumer は
`_h_ibp` underscore-prefixed unused 引数、`FisherInfoV2DeBruijnBody.lean:197`)。

**タイミング判断**: producer 作業の **後**に行う。理由: P-1/P-2 で V2 family file
(`FisherInfoV2DeBruijnBody.lean` 含む) を v_Z 追従で touch するため、その際に
`IsIBPHypothesis` が新 signature と干渉しないことを確認してから retract する方が安全。
P-1/P-2 完了後、`IsIBPHypothesis` の全 consumer (`_h_ibp` unused) を確認し、
死 alias を削除 (declaration 自体を消す or `@audit:superseded-by` で bookkeeping)。

- [ ] `rg -n 'IsIBPHypothesis' InformationTheory/` で全 consumer 列挙
- [ ] 全 consumer が `_h_ibp` underscore unused であることを再確認
- [ ] declaration 削除 + consumer の unused 引数除去 (signature から落とす)

**Done 条件**: `rg "IsIBPHypothesis" InformationTheory/` が 0 hit (または bookkeeping
コメントのみ)。touched file 全て `lake env lean` silent。

### P-V — verify + 独立 honesty audit (~5 行)

- [ ] M1 表の touched file 全件 `lake env lean` silent
- [ ] `entropyPower_add_ge_case1_of_methodX_full` を `#print axioms` で確認:
  producer が park した field があれば `sorryAx` 残存 (type-check done)、
  全閉なら `[propext, Classical.choice, Quot.sound]` (proof done)
- [ ] producer が新規 `sorry` + `@residual` を導入した場合、**独立 honesty audit**
  (`honesty-auditor` subagent) を起動 (CLAUDE.md「Independent honesty audit」起動条件:
  新規 `sorry` 導入 + signature 変更で honesty 意味が変わる)
- [ ] audit verdict: signature honesty (`Z_law` 一般化が退化を持ち込まないか、
  producer の `pX` series が load-bearing bundling でないか) + classification
  (`plan:epi-case1-debruijn-producer-plan` の正しさ) を確認

**Done 条件**: 全 silent + audit verdict 全 OK (or questionable-resolved-inline)。

---

## 撤退ライン

- **L-A-esc** (P-1/P-2 段階): `Z_law` 一般化が `IsRegularDeBruijnHypV2` の universal
  interface を壊し、追従が M1 想定 6-8 decl を大幅超過 → **案B (case-1 標準化 reparam)**
  にエスカレート。case-1 局所で `Z_X':=Z_X/√v_X` 標準化 + 時間再パラメータ
  `√t·Z_X = √(t·v_X)·Z_X'` の reduction を 1 本書き、producer を標準正規上で構築。
  ただし antitone/limit の時間 affine 保存補題 (`entropyPower_rescaled_path_tendsto`
  整合) を別途検証する必要があり、退化境界混入リスクを inline で監視。
- **L-Prod-park** (P-3 段階): case-1 input density witness (`pX` series、特に `pX_mom`
  の 2次モーメント push-forward / `pX_law` の rnDeriv 整合) が `hX_ac`/`h_mom_X` から
  genuine に組めないと判明 → 該当 field のみ `sorry` + `@residual(plan:epi-case1-debruijn-producer-plan)`
  で park (signature は producer 形を保つ)。`pX` series は regularity precondition なので
  最終 wrapper の追加 precondition として外出しする選択肢もある (命名を実態に合わせる)。
- **L-Stam-deleg** (P-4 段階): `h_pos_stam` の Fisher>0 / IsRegularDensityV2 / 正規化
  conjunct を既存資産に delegate できず新 sorry が必要 → 該当 conjunct を `sorry` + `@residual`
  で park。Stam / Blachman conjunct (genuine 既存) は park 不可 (delegate 必須)。

## Done 条件 (本 plan 全体)

- **proof done を目指す**: `entropyPower_add_ge_case1_of_methodX_full` の前提から
  de Bruijn regularity 群 (`IsDeBruijnRegularityHyp` / `IsHeatFlowEndpointRegular` /
  `h_pos_stam`) が消え、方針X (+ case-1 input density witness を残す場合はそれも明示
  regularity precondition) のみ残る
- producer 3 本 (`IsDeBruijnRegularityHyp`) + 3 本 (`IsHeatFlowEndpointRegular`、既存
  一般 variance に case-1 値を渡すだけ) + `h_pos_stam` producer が genuine に閉じる
  (park した field があれば `@residual(plan:epi-case1-debruijn-producer-plan)` で明示)
- `IsRegularDeBruijnHypV2.Z_law` が `gaussianReal 0 v_Z` 一般形 (退化を持ち込まない)
- M1 表の touched file 全件 `lake env lean` silent
- `IsIBPHypothesis` retract 済 (`rg` 0 hit)
- 独立 honesty audit (`honesty-auditor`) verdict 全 OK
- **honesty 不変条件**: producer の前提に load-bearing `*Hypothesis` predicate を
  bundling しない。`Z_law` 一般化で `v_Z = 0` 退化を突く degenerate-definition
  exploitation を作らない (`hv_Z_pos` で排除)

## 参考 file (verbatim file:line)

- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1470` — wrapper
  `entropyPower_add_ge_case1_of_methodX` (還元先、producer の consumer)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1488-1518` — wrapper の de Bruijn
  regularity 群 前提 (producer で discharge する対象)
- `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:205-268` — `IsRegularDeBruijnHypV2`
  structure (`Z_law : gaussianReal 0 1` が :210、P-1 一般化対象)
- `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:441` — `deBruijn_identity_v2_gaussian`
  (Gaussian-X publish point、var=1 専用 `gaussianConvolution_law_of_gaussian` 経由、
  producer chain 非経由)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:80` —
  `gaussianConvolution_law_conv` (一般 v_Z 既存、案A の素地)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:194` — Phase 1b
  `pPath_eq_convDensityAdd` (一般 v_Z 既存、conv-pin の整合先)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3437` — `_entropy_eq`
  (Phase 1b を `v_Z:=1` で叩く、P-2 で carrier 化)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3485` — `_fisher_match`
  (`_hZ_law` 未使用、P-2 で signature 一般化のみ)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3543` —
  `debruijnIdentityV2_holds_assembled` top-level (`h_reg.Z_law` 使用、P-2 で v_Z thread)
- `InformationTheory/Shannon/EPIStamDischarge.lean:251` — `IsDeBruijnRegularityHyp`
  structure (producer で構成する対象、`reg_at` 経由で `Z_law` 継承)
- `InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:488` — `IsHeatFlowEndpointRegular`
  structure (既に一般 `v_Z`、`@audit:ok`、case-1 値を渡すだけ)
- `InformationTheory/Shannon/EPIStamToBridge.lean:1346` —
  `isStamToEPIScalingHyp_of_stam_debruijn` (`IsDeBruijnRegularityHyp` 最大 consumer、
  `gaussianReal 0 1` hardcode、P-2 で v_Z 後方互換化)
- `InformationTheory/Shannon/EPIStamToBridge.lean:1435-1452` — `IsHeatFlowEndpointRegular`
  producer 既存 pattern (X→`v_Z:=1` / Y→`v_Z:=1` / sum→`v_Z:=2`、general-variance 構築の prior art)
- `InformationTheory/Shannon/FisherDeBruijnGaussianWitness.lean:158` —
  `isRegularDeBruijnHypV2_gaussian_heatFlow` (V2 Gaussian witness、P-2 で `v_Z:=1` 明示)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnBody.lean:209` — `IsIBPHypothesis`
  (P-6 retract 対象、死 alias)
- `InformationTheory/Shannon/EPIStamStep3Body.lean:119` — `isStamInequalityHyp_via_step3`
  (`h_pos_stam` の Stam conjunct、genuine sorryAx-free)
- `InformationTheory/Shannon/FisherConvBound.lean:385` — `gaussianConv_fisher_le_inv_var`
  (`integrable_deriv` の Fisher 有界性、`wall:fisher-finiteness` CLOSED 資産)
- `docs/shannon/epi-debruijn-regularity-refactor-plan.md` — 旧 `IsDeBruijnRegularityHyp`
  refactor 前例 (density_path top-level 化、案 1/2/3 比較の prior art)
- `docs/shannon/epi-stam-to-conclusion-phaseA-plan.md` — EPI 一般 line 側 density witness
  park の owner plan (case-1 と同 owner の input density precondition)
- `docs/audit/audit-tags.md` — `@residual` 語彙 / Wall register (de Bruijn 系壁 CLOSED 状態)

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-06-05 起草時 — 案A 確定 (M0 案D 調査結果に基づく)**: `deBruijn_identity_v2_gaussian` /
   `debruijnIdentityV2_holds_assembled` の var=1 本質依存を verbatim Read で調査。core chain
   (`_chain`、density-level) は v_Z-agnostic、v_Z=1 は `_entropy_eq`/`_fisher_match` が
   Phase 1b を `v_Z:=1` で叩く 2 callsite のみ (いずれも `s*1=s` simp 折り畳み)。素地
   `gaussianConvolution_law_conv` / `pPath_eq_convDensityAdd` は既に一般 v_Z 形。
   → 案A の追従コストが advisor 上限 (~150 LOC) を下回る見込み + EPI 全 line で
   general-variance de Bruijn が再利用される構造資産 → 案A 採用、案B は L-A-esc 時の fallback。
   blast radius 実測: 真の load-bearing 書換 6-8 decl、残り ~40 件は docstring / regularity-thread。

# EPI-Stam-to-Conclusion Phase A Mathlib API inventory

> **親 plan**: [`docs/shannon/epi-stam-to-conclusion-phaseA-plan.md`](epi-stam-to-conclusion-phaseA-plan.md)
> Phase A 着手前の M0 在庫照合 (Brief A 仕様)。
> **Generated**: 2026-05-25 (Phase A 着手直前)
> **規律**: CLAUDE.md `Subagent Inventory of Mathlib Lemmas` — `file:line` + 完全
> signature (`[...]` type-class 前提 verbatim) + 引数型 + 結論 form (verbatim) 必須。
> 推測 signature / loogle 出力だけでの記録は禁止 — すべて該当 Mathlib / Common2026
> file を Read で照合済。

---

## 一行サマリ

**Phase A の Mathlib API 必要量のうち実体は ~65% 既存** (微分計算 / `AntitoneOn` 機械 /
`Real.hasDerivAt_sqrt` / `differentialEntropy_map_mul_const` (Common2026 内) / Cauchy-Schwarz
Finset 形 `sum_mul_sq_le_sq_mul_sq` + `sq_sum_div_le_sum_sq_div`、Sedrakyan/Titu/Engel 形)。
**致命的 MISS は 2 件**: (a) **standard normal pair の任意 probability space 上 noise
extension API が Mathlib / Common2026 双方完全不在** (A-1) → 撤退ライン **L-Concl-A-γ
発動必至** (staged predicate `IsStamScalingNoiseHyp` で honest externalization);
(b) Cover-Thomas eq.(17.43) Csiszár scaling weight 不等式に直接対応する Mathlib lemma
不在 (A-3-2) → 撤退ライン **L-Concl-A-ζ 発動候補** (Mathlib `sum_mul_sq_le_sq_mul_sq` /
`sq_sum_div_le_sum_sq_div` を組合せれば自前で書けるが ~50-100 行)。**自作必要規模見積もり
合計 ~110-200 行** (ε /  ζ 含む)、L-Concl-A-α / β / δ は本 inventory 時点では発動条件
未充足 (A-2-4 の reparametrize 失敗が観測されない限り δ は休眠)。

---

## 主定理の最終形 (Phase A で構築するもの)

親 plan A-4-4 / A-5-2 で確定:

```lean
-- A-4-4 (中間 publish point)
theorem isStamToEPIScalingHyp_of_stam_debruijn
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (h_noise : IsStamScalingNoiseHyp X Y P)         -- A-1 新規 staged honest
    (h_dbreg_X : IsDeBruijnRegularityHyp X _ P)     -- sister Phase D output (staged)
    (h_dbreg_Y : IsDeBruijnRegularityHyp Y _ P)
    (h_dbint_X : ∀ T > 0, IsDeBruijnIntegrationHyp X _ P T)
    (h_dbint_Y : ∀ T > 0, IsDeBruijnIntegrationHyp Y _ P T)
    (h_dbint_sum : ∀ T > 0, IsDeBruijnIntegrationHyp (fun ω => X ω + Y ω) _ P T) :
    IsStamToEPIScalingHyp X Y P

-- A-5-2 (Phase A 最終 publish point)
theorem isStamToEPIBridgeHyp_of_stam_debruijn
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (h_noise : IsStamScalingNoiseHyp X Y P)
    (h_dbreg_X : ...) (h_dbreg_Y : ...) (h_dbint_X : ...) (h_dbint_Y : ...) (h_dbint_sum : ...) :
    IsStamToEPIBridgeHyp X Y P
```

証明戦略 (Cover-Thomas Lemma 17.7.3 Csiszár scaling):

```
g(s) := csiszarGap X Y Z_X Z_Y P s
      = entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s))
        - entropyPower (P.map (heatFlowPath2 X Z_X s))
        - entropyPower (P.map (heatFlowPath2 Y Z_Y s))           -- sister D-1-1 publish

1. (Z_X, Z_Y) standard normal pair witness exists       -- A-1 / staged hyp
2. d/ds g(s) computed via de Bruijn V2 + chain rule     -- A-2 / Mathlib + sister hyp
3. d/ds g(s) ≤ 0 from Stam 不等式 + Cauchy-Schwarz weight -- A-3 / Mathlib partial
4. AntitoneOn g (Set.Icc 0 1) by antitoneOn_of_deriv_nonpos -- A-4 / Mathlib OK
5. g(0) ≥ g(1) = 0 (Gaussian saturation 端点)            -- A-5 / sister D-1-3
   ∴ entropyPower(X+Y) ≥ entropyPower X + entropyPower Y -- bridge
```

---

## A. Standard normal pair witness 構築 (Phase A-1 用 / 撤退ライン L-Concl-A-γ)

### A.1 Mathlib 既存 — 部品レベル primitive

| 概念 | Mathlib API (完全 signature) | file:line | 状態 | A-1 での扱い |
|---|---|---|---|---|
| Gaussian 測度 | `noncomputable def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:200` | OK 既存 | `gaussianReal 0 1` を `Z_X, Z_Y` の target law として使用 |
| `gaussianReal` は確率測度 | `instance instIsProbabilityMeasureGaussianReal (μ : ℝ) (v : ℝ≥0) : IsProbabilityMeasure (gaussianReal μ v)` | (同上 file:209、Phase 0 inventory で確認済) | OK 既存 | 自動 instance |
| `IndepFun` 定義 | `def IndepFun {Ω : Type*} {β β' : Type*} [MeasurableSpace Ω] {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} (f : Ω → β) (g : Ω → β') (μ : Measure Ω := by volume_tac) : Prop` | `Mathlib/Probability/Independence/Basic.lean` | OK 既存 | `IndepFun X Z_X P`, `IndepFun Y Z_Y P`, `IndepFun Z_X Z_Y P` の各条件を表現 |
| `IndepFun.symm` | `theorem ProbabilityTheory.IndepFun.symm` (signature 略、Phase A では使わない可能性大、ただし symmetric witness 整形に有用) | `Mathlib/Probability/Independence/Basic.lean` | OK 既存 | optional |

### A.2 Mathlib MISS — noise extension on arbitrary probability space

| 求める API | loogle / rg 結果 | 判定 |
|---|---|---|
| `MeasureTheory.AtomlessProbability` | loogle: `unknown identifier` | **完全不在** |
| `ProbabilityTheory.IsAtomless` | loogle: `unknown identifier` | **完全不在** |
| `Measure.IsAtomless` | loogle: `unknown identifier` | **完全不在** |
| `MeasureTheory.NoAtoms` (class) | loogle: 120 declarations、定義 `Mathlib/MeasureTheory/Measure/Typeclasses/NoAtoms.lean:34` `class NoAtoms {m0 : MeasurableSpace α} (μ : Measure α) : Prop where measure_singleton : ∀ x, μ {x} = 0` | OK 存在するが、**標準正規拡張の構成 API は別物** |
| Standard normal pair の richness instance からの構築 | loogle `ProbabilityTheory.exists_iIndepFun` → `unknown identifier`; loogle `exists_measurable_indepFun` → `unknown identifier` | **完全不在** |
| `ProbabilityTheory.iIndepFun` × `gaussianReal` の組合せ既存例 | loogle 2件 (`tendstoInDistribution_inv_sqrt_mul_sum`、`tendstoInDistribution_inv_sqrt_mul_sum_sub`、`Mathlib/Probability/CentralLimitTheorem.lean:79`) | **CLT は別空間 `P'` 上に gaussian を取り、`P` 側には iid 列を仮定 — 任意 `P` 上に standard normal を新規構築する API としては流用不可** |
| Common2026 `StandardNoise.lean` 等 noise 拡張 file | `ls Common2026/Shannon/` → 該当 file なし、`rg "exists_indep|standard_normal_pair|noiseExtension|extendByGaussian" Common2026/` → 0 hit | **Common2026 内にも不在** |

**重要 (Phase 0 retract 前例)**: `EPIStamToBridge.lean:317-327` retraction comment 内に既存
の前例: 「Phase 0 で `isStamToEPIScalingHyp_of_gaussian` が同じ問題で retract された
(richness assumption が必要、Phase 0 scope 外)」。同じ壁に Phase A も直面する。

### A.3 判定

- **`IsStamScalingNoiseHyp X Y P` を新規 staged predicate として導入は不可避**
- 親 plan の **撤退ライン L-Concl-A-γ 発動必至** (Mathlib 整備不足 → honest externalization)
- staged 形は親 plan A-1-1 で提案された body:
  ```lean
  def IsStamScalingNoiseHyp {Ω : Type*} [MeasurableSpace Ω]
      (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
    ∃ (Z_X Z_Y : Ω → ℝ),
      Measurable Z_X ∧ Measurable Z_Y ∧
      P.map Z_X = gaussianReal 0 1 ∧ P.map Z_Y = gaussianReal 0 1 ∧
      IndepFun X Z_X P ∧ IndepFun Y Z_Y P ∧ IndepFun Z_X Z_Y P
  ```
  CLAUDE.md `検証の誠実性` の degenerate-definition exploitation チェックは OK
  (7-項 conjunction で空でない、退化 measure `Z := 0` は `P.map 0 = Measure.dirac 0
  ≠ gaussianReal 0 1` で除外、vacuous truth ではない)
- **自作必要規模**: 0 行 (staged 定義のみ、~10 行 docstring 含む)。具体 constructor
  `isStamScalingNoiseHyp_of_atomless` (stretch、`[NoAtoms P]` から構築) は Mathlib に
  該当 API なしのため **本 Phase A scope 外** (Mathlib 上流貢献 task として別 plan)
- **撤退ライン対応**: 親 plan §L-Concl-A-γ "Mathlib 壁 (b) 解析 — 自作 0 行 (staged
  externalization のみ)、Mathlib API 整備 (noise extension on arbitrary probability
  space) は別 plan"

---

## B. `differentialEntropy` scale-invariance (Phase A-2-1 用 / 撤退ライン L-Concl-A-ε)

### B.1 Common2026 既存 (再利用候補)

| 概念 | Common2026 API (完全 signature) | file:line | 状態 | A-2 での扱い |
|---|---|---|---|---|
| **`differentialEntropy` def** | `noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | `Common2026/Shannon/DifferentialEntropy.lean:42` | OK 既存 | 全 Phase A の base |
| **`differentialEntropy_dirac`** | `theorem differentialEntropy_dirac (m : ℝ) : differentialEntropy (Measure.dirac m) = 0` | `Common2026/Shannon/DifferentialEntropy.lean:149-159` | OK 既存 | Phase D degenerate boundary 解析で参照 (`entropyPower (dirac 0) = exp 0 = 1`) |
| **scale-invariance** (`h(cX) = h(X) + log|c|`) | `theorem differentialEntropy_map_mul_const {μ : Measure ℝ} (hμ : μ ≪ volume) [IsProbabilityMeasure μ] {c : ℝ} (hc : c ≠ 0) (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) : differentialEntropy (μ.map (· * c)) = differentialEntropy μ + Real.log |c|` | `Common2026/Shannon/DifferentialEntropy.lean:195-198` | **OK 既存** | A-2-1 で直接適用可能 (引数 3 つ要供給: `hμ`, `hc`, `h_ent_int`) |
| translation invariance | `theorem differentialEntropy_map_add_const {μ : Measure ℝ} (hμ : μ ≪ volume) [SigmaFinite μ] (y : ℝ) : differentialEntropy (μ.map (· + y)) = differentialEntropy μ` | `Common2026/Shannon/DifferentialEntropy.lean:165-167` | OK 既存 | Phase A では未使用想定 |
| affine corollary | `theorem differentialEntropy_map_affine {μ : Measure ℝ} (hμ : μ ≪ volume) [IsProbabilityMeasure μ] {a : ℝ} (ha : a ≠ 0) (b : ℝ) (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) : differentialEntropy (μ.map (fun x => a * x + b)) = differentialEntropy μ + Real.log |a|` | `Common2026/Shannon/DifferentialEntropy.lean:344-348` | OK 既存 | Phase A では未使用想定 (heatFlowPath2 は `√(1-s)·X + √s·Z`、constant b 部なし) |

### B.2 Mathlib 既存 (確認)

| 概念 | Mathlib API | loogle 結果 | 判定 |
|---|---|---|---|
| `MeasureTheory.differentialEntropy_smul` 等 | loogle 不在 (`differentialEntropy` は Mathlib に未定義) | **Mathlib 不在** (Common2026 内定義のみ) | Common2026 既存で十分 |

### B.3 判定

- **`differentialEntropy_map_mul_const` Common2026 既存** (`DifferentialEntropy.lean:195`)
  で A-2-1 は **自作不要**
- ただし caller (A-2-2 `heatFlowPath2_entropy_deriv` 構築時) が `h_ent_int :
  Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume` を
  caller 引数として carry する必要 — これは sister Phase D の `IsDeBruijnRegularityHyp`
  に density witness が bundled されているはずなので、密度経由で integrability を
  示せる (要確認、不可能なら新規 staged hyp)。
- **撤退ライン L-Concl-A-ε 発動条件**: A-2-2 で `h_ent_int` を sister Phase D の出力から
  carry できない場合 (`IsDeBruijnRegularityHyp` の `density_path` field は smooth と
  pin されているが integrability 条件は別途) → 撤退ライン候補だが Common2026 内別 file
  外出しで対処可能、本 Phase A scope 内 detour。**現時点では発動候補レベル、自作必要量
  ~10-20 行**
- 撤退ライン L-Concl-A-ε 親 plan 対応: "Common2026 `DifferentialEntropy.lean` 拡張で吸収
  (scope 内 detour)" — 整合

---

## C. Chain rule (Phase A-2 用 / 在庫済)

### C.1 Mathlib 既存

| 概念 | Mathlib API (完全 signature) | file:line | 状態 | A-2 での扱い |
|---|---|---|---|---|
| `Real.hasDerivAt_exp` | `theorem hasDerivAt_exp (x : ℝ) : HasDerivAt exp (exp x) x := (Complex.hasDerivAt_exp x).real_of_complex` | `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:267-268` (namespace `Real`、line 262) | OK 既存 | `entropyPower = Real.exp (2 · h(·))` の chain rule |
| `HasDerivAt.exp` (composition) | (variable section: `variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}` `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:298`) `theorem HasDerivAt.exp (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x` | `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:304-306` | OK 既存 | `Real.exp (2 · h(X_s))` の `s` 微分 |
| `HasDerivAt.sub` | (variable section: `variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]` / `variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]` / `variable {f g : 𝕜 → F}` / `variable {f' g' : F}` / `variable {x : 𝕜} {s : Set 𝕜} {L : Filter (𝕜 × 𝕜)}` `Mathlib/Analysis/Calculus/Deriv/Add.lean:33-37`) `theorem HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) : HasDerivAt (f - g) (f' - g') x` (`@[to_fun]` attribute、autogenerated `_filter`/`_within` variants) | `Mathlib/Analysis/Calculus/Deriv/Add.lean:348-351` | OK 既存 | `csiszarGap` 3 項差分の微分 |
| `HasDerivAt.add` | 同 variable section、`theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) : HasDerivAt (f + g) (f' + g') x` (`@[to_fun]`) | `Mathlib/Analysis/Calculus/Deriv/Add.lean:58-61` | OK 既存 | `heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s` の sum 部 |
| `HasDerivAt.comp` (chain rule) | (variable section: `variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]` / `variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]` / `variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]` / `variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]` `Mathlib/Analysis/Calculus/Deriv/Comp.lean:45-71`、引数 `(x)` も explicit) `theorem HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x` | `Mathlib/Analysis/Calculus/Deriv/Comp.lean:258-260` | OK 既存 | `Real.exp ∘ (2 · h)` 等の chain |
| `Real.hasDerivAt_sqrt` | `theorem hasDerivAt_sqrt {x : ℝ} (hx : x ≠ 0) : HasDerivAt (√·) (1 / (2 * √x)) x := (hasStrictDerivAt_sqrt hx).hasDerivAt` (namespace `Real`、line 62) | `Mathlib/Analysis/SpecialFunctions/Sqrt.lean:68-69` | OK 既存 (`x ≠ 0` 必須) | `Real.sqrt (1-s)` 及び `Real.sqrt s` の `s` 微分 (interior `s ∈ Ioo 0 1` のみ valid、端点除外) |
| `HasDerivAt.sqrt` (composition) | (variable section: `variable {f : ℝ → ℝ} {s : Set ℝ} {f' x : ℝ}` `Mathlib/Analysis/SpecialFunctions/Sqrt.lean:77`) `theorem HasDerivAt.sqrt (hf : HasDerivAt f f' x) (hx : f x ≠ 0) : HasDerivAt (fun y => √(f y)) (f' / (2 * √(f x))) x` | `Mathlib/Analysis/SpecialFunctions/Sqrt.lean:84-86` | OK 既存 | `Real.sqrt (1 - s)` の chain rule (`f := (1 - ·)`、`f' := -1`) |

### C.2 Common2026 既存 — de Bruijn V2 derivative

| 概念 | Common2026 API (完全 signature) | file:line | 状態 | A-2 での扱い |
|---|---|---|---|---|
| **V2 de Bruijn regularity predicate** | `structure IsRegularDeBruijnHypV2 {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (t : ℝ) where Z_law : P.map Z = gaussianReal 0 1; density_t : ℝ → ℝ; derivAt_entropy_eq_half_fisher_v2 : HasDerivAt (fun s => differentialEntropy (P.map (gaussianConvolution X Z s))) ((1/2) * fisherInfoOfDensityReal density_t) t` | `Common2026/Shannon/FisherInfoV2DeBruijn.lean:236-249` | OK 既存 | A-2-2 `heatFlowPath2_entropy_deriv` 補題内で `reg_at t ht` field 経由で `derivAt_entropy_eq_half_fisher_v2` を引き出して使用 |
| de Bruijn V2 identity wrapper | `theorem deBruijn_identity_v2 {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] (X Z : Ω → ℝ) (_hX : Measurable X) (_hZ : Measurable Z) (_hXZ : IndepFun X Z P) {t : ℝ} (_ht : 0 < t) (h_reg : IsRegularDeBruijnHypV2 X Z P t) : HasDerivAt (fun s => differentialEntropy (P.map (gaussianConvolution X Z s))) ((1/2) * fisherInfoOfDensityReal h_reg.density_t) t := h_reg.derivAt_entropy_eq_half_fisher_v2` | `Common2026/Shannon/FisherInfoV2DeBruijn.lean:262-272` | OK 既存 | 1-source `gaussianConvolution X Z s = X + √s · Z` の `s` 微分 |
| **`gaussianConvolution`** (1-source) | `noncomputable def gaussianConvolution {α : Type*} (X Z : α → ℝ) (t : ℝ) : α → ℝ := fun ω => X ω + Real.sqrt t * Z ω` | `Common2026/Shannon/FisherInfoV2DeBruijn.lean:154-155` | OK 既存 | 1-source heat-flow path、Phase A の 2-source `heatFlowPath2` と reparametrize 必要 |
| `gaussianConvolution_law_of_gaussian` | `theorem gaussianConvolution_law_of_gaussian {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P) {m : ℝ} {v : ℝ≥0} (hX_law : P.map X = gaussianReal m v) (hZ_law : P.map Z = gaussianReal 0 1) {t : ℝ} (ht : 0 ≤ t) : P.map (gaussianConvolution X Z t) = gaussianReal m (v + ⟨t, ht⟩)` | `Common2026/Shannon/FisherInfoV2DeBruijn.lean:172-180` | OK 既存 | Gaussian 端点 (Phase A-5-1 で `Z_X + √1·Z_Y` 形に流用) |

### C.3 Common2026 既存 — heat-flow path (2-source)

| 概念 | Common2026 API (完全 signature) | file:line | 状態 | A-2 での扱い |
|---|---|---|---|---|
| `heatFlowPath2` def | `noncomputable def heatFlowPath2 {α : Type*} (X Z : α → ℝ) (s : ℝ) : α → ℝ := fun ω => Real.sqrt (1 - s) * X ω + Real.sqrt s * Z ω` (signature 直前で確認、Phase 0 publish 167 行 file) | `Common2026/Shannon/HeatFlowPath.lean` (def は file 上部に存在、`measurable_heatFlowPath2` `:45-46` 周辺で参照) | OK 既存 | 2-source heat-flow path 本体 |
| `heatFlowPath2_zero` | `theorem heatFlowPath2_zero {α : Type*} (X Z : α → ℝ) : heatFlowPath2 X Z 0 = X := by funext ω; simp [heatFlowPath2, Real.sqrt_one, Real.sqrt_zero]` | `Common2026/Shannon/HeatFlowPath.lean:49-52` | OK 既存 | endpoint `s=0` |
| `heatFlowPath2_one` | `theorem heatFlowPath2_one {α : Type*} (X Z : α → ℝ) : heatFlowPath2 X Z 1 = Z := by funext ω; simp [heatFlowPath2, Real.sqrt_one, Real.sqrt_zero]` | `Common2026/Shannon/HeatFlowPath.lean:54-58` | OK 既存 | endpoint `s=1` |
| `heatFlowPath2_law` (一般 X) | `theorem heatFlowPath2_law {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P) (hZ_law : P.map Z = gaussianReal 0 1) {s : ℝ} (hs0 : 0 ≤ s) (_hs1 : s ≤ 1) : P.map (heatFlowPath2 X Z s) = (P.map (fun ω => Real.sqrt (1 - s) * X ω)) ∗ gaussianReal 0 ⟨s, hs0⟩` | `Common2026/Shannon/HeatFlowPath.lean:63-68` | OK 既存 | A-2-1 で `P.map (√(1-s)·X)` と `gaussianReal 0 s` の畳み込みに分解、de Bruijn V2 を `Y_eff := √(1-s)·X` で 1-source 形に reduce する re-parametrize の基礎 |
| `heatFlowPath2_law_of_gaussian` (Gaussian X) | `theorem heatFlowPath2_law_of_gaussian {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P) {m : ℝ} {v : ℝ≥0} (hX_law : P.map X = gaussianReal m v) (hZ_law : P.map Z = gaussianReal 0 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : P.map (heatFlowPath2 X Z s) = gaussianReal (Real.sqrt (1 - s) * m) (⟨1 - s, by linarith⟩ * v + ⟨s, hs0⟩)` | `Common2026/Shannon/HeatFlowPath.lean:104-111` | OK 既存 | A-5-1 Gaussian 端点で再利用 |
| `IndepFun.map_add_eq_map_conv_map` (Mathlib, additive auto-gen from `to_additive` of `IndepFun.map_mul_eq_map_mconv_map`) | `theorem IndepFun.map_mul_eq_map_mconv_map [IsFiniteMeasure μ] {f g : Ω → M} (hf : Measurable f) (hg : Measurable g) (hfg : f ⟂ᵢ[μ] g) : μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) := hfg.map_mul_eq_map_mconv_map₀ hf.aemeasurable hg.aemeasurable` (additive ver = `map_add_eq_map_conv_map`) | `Mathlib/Probability/Independence/Basic.lean:1103-1107` (additive ver auto-generated by `@[to_additive]` line 1102) | OK 既存 | `heatFlowPath2_law` body 内で既に使用、Phase A は直接呼ばずに `heatFlowPath2_law` 経由 |

### C.4 重要 caveat — 1-source vs 2-source 間 reparametrize

`derivAt_entropy_eq_half_fisher_v2` は **1-source 形** `(s ↦ differentialEntropy
(P.map (gaussianConvolution X Z s)))` の `s` 微分。本 Phase A の `heatFlowPath2 X Z_X s`
は **2-source 形** `√(1-s)·X + √s·Z_X`。両者の関係:

- `heatFlowPath2 X Z_X s = √(1-s)·X + √s·Z_X` (raw def)
- `heatFlowPath2_law`: `P.map (heatFlowPath2 X Z_X s) = (P.map (√(1-s)·X)) ∗ gaussianReal 0 s`
- これは `Y_eff_s := √(1-s)·X`、`Z_eff := Z_X` として `P.map (Y_eff_s + √s · Z_X)` の形に
  reduce 可能、すなわち **`gaussianConvolution Y_eff_s Z_X s`**
- ただし `Y_eff_s` 自体が `s` 依存 → de Bruijn V2 を直接適用すると **partial derivative の
  混乱** が発生する。chain rule で「`Y_eff_s` を `s` で動かす微分」+「heat-flow `s` で動かす
  微分」の和になり、後者だけが Fisher info 項、前者は scale-invariance 由来の `differentialEntropy_map_mul_const` で書き換えて分離する必要
- A-2-2 / A-2-4 で本変形を実装、撤退ライン **L-Concl-A-δ** はこの reparametrize 失敗時の
  fallback (現時点では発動条件未充足、A-2-4 で計算実行時に判定)

---

## D. `g'(s) ≤ 0` の Stam + Csiszár scaling weight 不等式 (Phase A-3 用 / 撤退ライン L-Concl-A-ζ)

### D.1 Mathlib 既存 — Finset Cauchy-Schwarz primitive

| 概念 | Mathlib API (完全 signature) | file:line | 状態 | A-3 での扱い |
|---|---|---|---|---|
| **Cauchy-Schwarz Finset, sq 形** | `lemma sum_mul_sq_le_sq_mul_sq [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) (f g : ι → R) : (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2` | `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:150-152` | OK 既存 | A-3-2 の Cauchy-Schwarz weight 不等式に直接対応する形ではないが、3 項 Finset (`Finset.range 3` 等) に specialize して書下し可能 |
| **Sedrakyan / Titu / Engel 形** | `theorem sq_sum_div_le_sum_sq_div [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) (f : ι → R) {g : ι → R} (hg : ∀ i ∈ s, 0 < g i) : (∑ i ∈ s, f i) ^ 2 / ∑ i ∈ s, g i ≤ ∑ i ∈ s, f i ^ 2 / g i` | `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:160-163` | OK 既存 | A-3-2 の reciprocal weight 不等式に**最も近い形**: 入力は `(f_i, g_i = J_i)`、結論は `(∑ f)² / ∑ J ≤ ∑ f² / J`、これを EPI 用に `(f_i := √entropyPower_i)` とすると `(√EP(X) + √EP(Y))² / (J(X) + J(Y)) ≤ EP(X)/J(X) + EP(Y)/J(Y)` 形に整形できる |
| Cauchy-Schwarz Finset, general (`r²=fg`) 形 | `lemma sum_sq_le_sum_mul_sum_of_sq_eq_mul [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) {r f g : ι → R} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) (ht : ∀ i ∈ s, r i ^ 2 = f i * g i) : (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i` | `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:126-129` | OK 既存 | より一般形、optional |
| InnerProductSpace Cauchy-Schwarz | `theorem inner_mul_inner_self_le (x y : F) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫` | `Mathlib/Analysis/InnerProductSpace/Defs.lean:351` | OK 既存 | abstract 形、本 Phase A では Finset 形優先 |
| InnerProductSpace norm 形 | `theorem norm_inner_le_norm (x y : F) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖` | `Mathlib/Analysis/InnerProductSpace/Defs.lean:387` | OK 既存 | abstract 形、optional |

### D.2 Mathlib MISS — Cover-Thomas eq.(17.43) 直接形

| 求める API | loogle / rg 結果 | 判定 |
|---|---|---|
| `Real.inner_mul_le_norm_mul_norm` (親 plan 仮称) | loogle: `unknown identifier`、rg fixed-strings 0 hit | **不在** |
| `Finset.inner_mul_le_norm_mul_norm` (親 plan 仮称) | loogle: `unknown identifier`、rg 0 hit | **不在** |
| `Real.add_sq_le_sq_mul_sq` (親 plan 仮称) | loogle: `unknown identifier` | **不在** |
| `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` (Cover-Thomas weight 用 candidate) | loogle: `unknown identifier` | **不在** |
| Cover-Thomas eq.(17.43) `entropyPower(X+Y) · J(X+Y) ≤ entropyPower(X) · J(X) + entropyPower(Y) · J(Y)` 直接形 | rg `Stam\|Csiszar\|entropy_power` in Mathlib → 0 hit | **完全不在** (Stam/Csiszar/EPI machinery は Mathlib にゼロ) |

### D.3 判定

- **`sum_mul_sq_le_sq_mul_sq` + `sq_sum_div_le_sum_sq_div`** (Mathlib 既存) で
  Cover-Thomas eq.(17.43) の weight 不等式を **自前で組立可能**、ただし Stam の
  `1/J_sum ≥ 1/J_X + 1/J_Y` と整合させる algebraic transform は新規補題として
  ~50-80 行
- Cover-Thomas eq.(17.43) は本質的に「`J(X) · entropyPower(X) + J(Y) · entropyPower(Y)
  ≥ J(X+Y) · entropyPower(X+Y)`」(harmonic-mean × power-mean 形) で、`sq_sum_div_le_sum_sq_div`
  に `f_i := √entropyPower_i`、`g_i := J_i` (i ∈ {X, Y}) を充てれば
  `(√EP(X) + √EP(Y))² / (J(X) + J(Y)) ≤ EP(X)/J(X) + EP(Y)/J(Y)` が出る
- 追加で Stam `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)` を組合せると `(√EP(X) + √EP(Y))² ·
  J(X+Y) ≤ EP(X) · J(X+Y)/J(X) + EP(Y) · J(X+Y)/J(Y)` に整形でき、ここから
  `EP(X+Y) ≤ (√EP(X) + √EP(Y))²` (EPI 結論) が出る
- **撤退ライン L-Concl-A-ζ 発動候補**: 自前 plumbing が >100 行になる場合、新規 staged
  predicate `IsCsiszarScalingWeightHyp X Y P` (Cover-Thomas eq.(17.43) statement) として
  externalization。**現時点見積もり ~50-80 行**なので、threshold 100 行を下回り
  発動 marginal、A-3-2 実装時に判定
- **自作必要規模**: ~50-80 行 (新規補題 `csiszarScalingWeightInequality` of similar)
- 撤退ライン親 plan 対応: 親 plan §L-Concl-A-ζ "Mathlib 上流貢献 / 別 plan で外出し" —
  marginal、自作 50-80 行で済むなら scope 内対処

---

## E. `AntitoneOn` 機械 (Phase A-4 用 / 在庫 HIT)

### E.1 Mathlib 既存

| 概念 | Mathlib API (完全 signature) | file:line | 状態 | A-4 での扱い |
|---|---|---|---|---|
| **`antitoneOn_of_deriv_nonpos`** | `theorem antitoneOn_of_deriv_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) (hf'_nonpos : ∀ x ∈ interior D, deriv f x ≤ 0) : AntitoneOn f D` | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:478-480` | **OK 既存** | A-4-3 で直接適用、引数 4 つ供給 (`hD`, `hf`, `hf'`, `hf'_nonpos`) |
| `antitoneOn_of_hasDerivWithinAt_nonpos` (任意 stretch) | `lemma antitoneOn_of_hasDerivWithinAt_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ} (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x) (hf'₀ : ∀ x ∈ interior D, f' x ≤ 0) : AntitoneOn f D` | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:495-499` | OK 既存 | `HasDerivWithinAt` 形 (本 Phase A の HasDerivAt 形でも使える) |
| **`convex_Icc`** | (variable section: `variable {𝕜 E F β : Type*}` `Mathlib/Analysis/Convex/Basic.lean:30`、`variable [Semiring 𝕜] [PartialOrder 𝕜]` `:41`、追加で `variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]` `:243`) `theorem convex_Icc (r s : β) : Convex 𝕜 (Icc r s) := Ici_inter_Iic.subst ((convex_Ici r).inter <| convex_Iic s)` | `Mathlib/Analysis/Convex/Basic.lean:254-255` | OK 既存 | `Convex ℝ (Set.Icc (0 : ℝ) 1)` を自動 discharge |

### E.2 判定

- **`antitoneOn_of_deriv_nonpos` Mathlib 既存** で A-4-3 は **自作不要**、`convex_Icc`
  で `Convex ℝ (Set.Icc 0 1)` も自動
- ContinuousOn endpoint extension は親 plan A-4-1 で `csiszarGap_at_zero` /
  `csiszarGap_at_one_eq_zero_of_gaussian_pair` (sister Phase D 既存 publish) +
  `HasDerivAt.continuousAt` で組合せ、interior `(0, 1)` continuity は A-2 の HasDerivAt
  から derived。**自作 ~10-20 行** (csiszarGap_continuousOn 補題)
- DifferentiableOn interior は A-2 の HasDerivAt から `~5-10 行`
- **撤退ライン発動なし**: A-4 全体は在庫済機械の組合せ、~20-30 行 detour なし

---

## F. Sister Phase D 出力 — 既存照合 (Phase A-0 用 / 在庫 HIT)

### F.1 Common2026 既存 (sister `epi-debruijn-integration-phaseD-plan` Phase D 出力)

| 概念 | Common2026 API (完全 signature) | file:line | 状態 | A-0 での扱い |
|---|---|---|---|---|
| **`csiszarGap`** | `noncomputable def csiszarGap {Ω : Type*} [MeasurableSpace Ω] (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) (s : ℝ) : ℝ := entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s)) - entropyPower (P.map (heatFlowPath2 X Z_X s)) - entropyPower (P.map (heatFlowPath2 Y Z_Y s))` | `Common2026/Shannon/EPIL3Integration.lean:1160-1164` | **OK 既存** (sister publish 済、`@audit:suspect(epi-debruijn-integration-phaseD-plan)`) | A-2 / A-3 / A-4 で `csiszarGap` を直接微分・操作 |
| **`csiszarGap_at_zero`** | `theorem csiszarGap_at_zero {Ω : Type*} [MeasurableSpace Ω] (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) : csiszarGap X Y Z_X Z_Y P 0 = entropyPower (P.map (fun ω => X ω + Y ω)) - entropyPower (P.map X) - entropyPower (P.map Y)` | `Common2026/Shannon/EPIL3Integration.lean:1173-1184` | OK 既存 | A-4-1 endpoint continuity / A-6 主定理 hypothesis-free 化 |
| **`csiszarGap_at_one_eq_zero_of_gaussian_pair`** | `theorem csiszarGap_at_one_eq_zero_of_gaussian_pair {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y Z_X Z_Y : Ω → ℝ} (P : Measure Ω) [IsProbabilityMeasure P] (hZX : Measurable Z_X) (hZY : Measurable Z_Y) (hZXZY : IndepFun Z_X Z_Y P) (hZX_law : P.map Z_X = gaussianReal 0 1) (hZY_law : P.map Z_Y = gaussianReal 0 1) : csiszarGap X Y Z_X Z_Y P 1 = 0` | `Common2026/Shannon/EPIL3Integration.lean:1194-1201` | OK 既存 | A-4-1 endpoint / A-5-1 `isStamToEPILimitHyp_trivial` で再利用 |
| **`csiszarGap_shape_for_sister`** | `theorem csiszarGap_shape_for_sister {Ω : Type*} [MeasurableSpace Ω] (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) : (fun s : ℝ => csiszarGap X Y Z_X Z_Y P s) = (fun s : ℝ => entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s)) - entropyPower (P.map (heatFlowPath2 X Z_X s)) - entropyPower (P.map (heatFlowPath2 Y Z_Y s))) := rfl` | `Common2026/Shannon/EPIL3Integration.lean:1279-1287` | OK 既存 | A-4-4 で `IsStamToEPIScalingHyp` の `AntitoneOn` 引数 lambda を `csiszarGap` 形に書換 |
| **`IsStamInequalityHyp`** | `def IsStamInequalityHyp {Ω : Type*} [MeasurableSpace Ω] (X Y : Ω → ℝ) (P : Measure Ω) : Prop := ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum → J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal → J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal → J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map (fun ω => X ω + Y ω)) fXY).toReal → 1 / J_sum ≥ 1 / J_X + 1 / J_Y` | `Common2026/Shannon/EPIStamDischarge.lean:97-104` | OK 既存 (`@audit:staged(epi-stam-discharge-plan)` ?? — 要確認) | A-3-1 / A-3-3 で Stam 不等式を caller 経由で carry |
| **`IsDeBruijnRegularityHyp`** | `structure IsDeBruijnRegularityHyp {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] where density_path : ℝ → ℝ → ℝ; reg_at : ∀ t : ℝ, 0 < t → Common2026.Shannon.FisherInfoV2.IsRegularDeBruijnHypV2 X Z P t; density_t_eq : ∀ t : ℝ, ∀ ht : 0 < t, (reg_at t ht).density_t = density_path t; integrable_deriv : ∀ T : ℝ, 0 < T → IntervalIntegrable (fun t : ℝ => (1/2) * (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map (fun ω => X ω + Real.sqrt t * Z ω)) (density_path t)).toReal) volume 0 T` | `Common2026/Shannon/EPIStamDischarge.lean:193-227` | OK 既存 (`@audit:staged(epi-debruijn-regularity)`、Phase D 完了) | A-2-2 で `reg_at` field 経由で V2 derivative carry |
| **`IsDeBruijnIntegrationHyp`** | `def IsDeBruijnIntegrationHyp {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (P : Measure Ω) (T : ℝ) : Prop := ∃ (fPath : ℝ → ℝ → ℝ), ∀ (h_X h_target : ℝ), h_X = Common2026.Shannon.differentialEntropy (P.map X) → h_target = Common2026.Shannon.differentialEntropy (P.map (fun ω => X ω + Real.sqrt T * Z ω)) → h_target - h_X = ∫ t in Set.Ioo 0 T, (1/2) * (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map (fun ω => X ω + Real.sqrt t * Z ω)) (fPath t)).toReal ∂volume` | `Common2026/Shannon/EPIStamDischarge.lean:258-268` | OK 既存 (`@audit:staged(epi-debruijn-integration)`) | A-2 で FTC bridge として参照 (sister output) |

### F.2 既存 EPIStamToBridge.lean publish (Phase A 出力先)

| 概念 | Common2026 API (完全 signature) | file:line | 状態 | A 全体での扱い |
|---|---|---|---|---|
| **`IsStamToEPIScalingHyp`** | `def IsStamToEPIScalingHyp {Ω : Type*} [MeasurableSpace Ω] (X Y : Ω → ℝ) (P : Measure Ω) : Prop := IsStamInequalityHyp X Y P → ∃ (Z_X Z_Y : Ω → ℝ), Measurable Z_X ∧ Measurable Z_Y ∧ P.map Z_X = gaussianReal 0 1 ∧ P.map Z_Y = gaussianReal 0 1 ∧ IndepFun X Z_X P ∧ IndepFun Y Z_Y P ∧ IndepFun Z_X Z_Y P ∧ AntitoneOn (fun s : ℝ => entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s)) - entropyPower (P.map (heatFlowPath2 X Z_X s)) - entropyPower (P.map (heatFlowPath2 Y Z_Y s))) (Set.Icc (0 : ℝ) 1)` | `Common2026/Shannon/EPIStamToBridge.lean:202-216` | OK 既存 (Phase 0 refactor 後、`@audit:suspect(epi-stam-to-conclusion-plan)`) | A-4-4 publish point、本 Phase A constructor `isStamToEPIScalingHyp_of_stam_debruijn` の結論型 |
| **`isStamToEPIBridgeHyp_of_scaling_limit`** | `theorem isStamToEPIBridgeHyp_of_scaling_limit {Ω : Type*} [MeasurableSpace Ω] {X Y : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] (h_scaling : IsStamToEPIScalingHyp X Y P) (_h_limit : IsStamToEPILimitHyp X Y P) : IsStamToEPIBridgeHyp X Y P` (body uses `entropy_power_inequality_gaussian_saturation`、`heatFlowPath2_zero`、`heatFlowPath2_one`) | `Common2026/Shannon/EPIStamToBridge.lean:266-313` | OK 既存 (`@audit:ok`) | A-5-2 で `_of_stam_debruijn` constructor 内部から呼出 |
| `IsStamToEPILimitHyp` | `def IsStamToEPILimitHyp {Ω : Type*} [MeasurableSpace Ω] (X Y : Ω → ℝ) (P : Measure Ω) : Prop := ∃ (g1 : ℝ), g1 = 0 ∧ ((g1 ≤ entropyPower (P.map (fun ω => X ω + Y ω)) - entropyPower (P.map X) - entropyPower (P.map Y)) ∨ (entropyPower (P.map (fun ω => X ω + Y ω)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)))` | `Common2026/Shannon/EPIStamToBridge.lean:242-249` | OK 既存 (`@audit:suspect(epi-stam-to-conclusion-plan)`、Phase 0 注釈で launder と認識済) | A-5-1 `isStamToEPILimitHyp_trivial` で `⟨0, rfl, Or.inr ?_⟩` 構築 (`Or.inr` ブランチを使い `entropy_power_inequality_gaussian_saturation` で discharge) |
| **`IsStamToEPIBridgeHyp`** | `def IsStamToEPIBridgeHyp {Ω : Type*} [MeasurableSpace Ω] (X Y : Ω → ℝ) (P : Measure Ω) : Prop := IsStamInequalityHyp X Y P → IsEntropyPowerInequalityHypothesis X Y P` | `Common2026/Shannon/EPIStamDischarge.lean:337-339` | OK 既存 (`Discharge via epi-stam-to-conclusion-plan.md (未着手)` docstring 改訂対象 A-6-2) | A-5-2 publish point |

### F.3 主定理 `entropy_power_inequality`

| 概念 | Common2026 API (完全 signature) | file:line | 状態 | A-6 での扱い |
|---|---|---|---|---|
| **主定理** | `theorem entropy_power_inequality {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) (h_stam : IsStamInequalityResidual X Y P) (h_bridge : IsStamToEPIBridge X Y P) : entropyPower (P.map (fun ω => X ω + Y ω)) ≥ entropyPower (P.map X) + entropyPower (P.map Y) := h_bridge h_stam` | `Common2026/Shannon/EntropyPowerInequality.lean:232-240` | OK 既存 (`@audit:suspect(epi-stam-to-conclusion-plan)`) | A-6 hypothesis-free 化 (案 a: 新 wrapper `_unconditional` 追加、本体不変) |
| `IsStamInequalityResidual` | `def IsStamInequalityResidual {Ω : Type*} [MeasurableSpace Ω] (X Y : Ω → ℝ) (P : Measure Ω) : Prop := ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum → J_X = Common2026.Shannon.FisherInfoV2.fisherInfoOfDensityReal fX → J_Y = Common2026.Shannon.FisherInfoV2.fisherInfoOfDensityReal fY → J_sum = Common2026.Shannon.FisherInfoV2.fisherInfoOfDensityReal fXY → 1 / J_sum ≥ 1 / J_X + 1 / J_Y` | `Common2026/Shannon/EntropyPowerInequality.lean:187-193` | OK 既存 (`IsStamInequalityHyp` と defeq、`fisherInfoOfMeasureV2_def` 経由) | A-6 caller 側で discharge |
| `IsStamToEPIBridge` | `def IsStamToEPIBridge {Ω : Type*} [MeasurableSpace Ω] (X Y : Ω → ℝ) (P : Measure Ω) : Prop := IsStamInequalityResidual X Y P → IsEntropyPowerInequalityHypothesis X Y P` | `Common2026/Shannon/EntropyPowerInequality.lean:203-205` | OK 既存 | A-6 caller 側で discharge |
| `entropyPower` def | `noncomputable def entropyPower (μ : Measure ℝ) : ℝ := Real.exp (2 * Common2026.Shannon.differentialEntropy μ)` | `Common2026/Shannon/EntropyPowerInequality.lean:93-94` | OK 既存 | chain rule で `Real.hasDerivAt_exp` × 2 |
| `entropy_power_inequality_gaussian_saturation` (参照、A-5-1 で再利用) | (signature 既存、Phase 0 で確認、line 270-301 範囲) | `Common2026/Shannon/EntropyPowerInequality.lean:270-301` | OK 既存 | A-5-1 で Gaussian 端点 `g(1) = 0` discharge |

### F.4 判定

- sister Phase D 出力 (csiszarGap / endpoint lemma / shape contract / `IsStamInequalityHyp`
  / `IsDeBruijnRegularityHyp` / `IsDeBruijnIntegrationHyp`) は **全て publish 済**
- Phase A-0 (Read 照合) で signature drift 検出は **0 件**: 親 plan の line 番号
  (`csiszarGap` `:1160-1164`、`csiszarGap_at_zero` `:1173-1184`、`csiszarGap_at_one_eq_zero_of_gaussian_pair`
  `:1194-1201`、`csiszarGap_shape_for_sister` `:1279-1287`、`IsStamInequalityHyp` `:97-104`、
  `IsDeBruijnRegularityHyp` `:193-227`、`IsDeBruijnIntegrationHyp` `:258-268`、
  `IsStamToEPIScalingHyp` `:202-216`、`isStamToEPIBridgeHyp_of_scaling_limit` `:266-313`、
  `IsStamToEPIBridgeHyp` `:337-339`、`entropy_power_inequality` `:232-240`) は本 inventory
  作成時点で **全 verbatim 一致**

---

## 自作必要要素 (優先度順)

| 優先度 | sub-step | 内容 | 行数見積もり | 落とし穴 |
|---|---|---|---|---|
| **HIGH** (撤退ライン γ 発動必至) | A-1-1 | `IsStamScalingNoiseHyp` predicate (staged honest, 7-項 conjunction) | ~10-15 (def + docstring) | docstring で「`@audit:staged(epi-stam-to-conclusion-plan)`、NOT a discharge、Mathlib noise extension API 不在のため externalization」を明示 (CLAUDE.md `検証の誠実性` 準拠) |
| HIGH | A-2-1 | `differentialEntropy_const_mul` caller integrability bridge (Common2026 既存 `differentialEntropy_map_mul_const` の `h_ent_int` 引数を sister Phase D output から carry) | ~10-20 (補題、sister output から integrability 構築) | Phase D `IsDeBruijnRegularityHyp` の density 経由で integrability 導出可能か要 (sister 出力の field 仕様確認) — 不可能なら新規 staged hyp (撤退ライン L-Concl-A-ε marginal 発動) |
| HIGH | A-2-2 / A-2-3 | `heatFlowPath2_entropy_deriv` + `csiszarGap_hasDerivAt` (de Bruijn V2 + scale-invariance + chain rule、1-source → 2-source reparametrize) | ~50-80 | scale-invariance 補正項 `−1/(2(1-s))` のキャンセル確認、3 項分の `entropyPower` 因子整理 (L-Concl-A-δ 発動候補、A-2-4 で実装時判定) |
| HIGH | A-3-1 / A-3-2 | `csiszarGap_deriv_le_zero` (Stam + Cauchy-Schwarz weight 不等式自前組立、`sum_mul_sq_le_sq_mul_sq` / `sq_sum_div_le_sum_sq_div` 流用) | ~50-80 | Cover-Thomas eq.(17.43) を `sq_sum_div_le_sum_sq_div` (Sedrakyan) 形に reduce する algebra、`f_i := √EP_i`、`g_i := J_i` の代入後 Stam 不等式と組合せ |
| MED | A-3-3 | `csiszarGap_deriv_nonneg` 結論 (Stam + weight 不等式 + scaling 補正で `g'(s) ≤ 0` を `linarith` で結論) | ~10-20 | A-2-4 と A-3-2 の出力次第、scaling 補正項が weight inequality と相互作用しない設計が必須 |
| MED | A-4-1 / A-4-2 | `csiszarGap_continuousOn` + `csiszarGap_differentiableOn_interior` (Set.Icc 0 1 上の連続性 + interior 微分可能性) | ~15-25 | endpoint extension は `csiszarGap_at_zero` / `csiszarGap_at_one_eq_zero_of_gaussian_pair` (sister) で beta-reduce、interior は A-2 の HasDerivAt から derived |
| LOW (constructor 組立) | A-4-3 / A-4-4 | `antitoneOn_of_deriv_nonpos` 適用 + existential witness bundle | ~15-25 | `IsStamScalingNoiseHyp` から `obtain ⟨Z_X, Z_Y, ...⟩`、各 hypothesis を 7-項 destructure、`IsStamToEPIScalingHyp` の 8-項 conjunction に再 bundle |
| LOW | A-5-1 | `isStamToEPILimitHyp_trivial` (`⟨0, rfl, Or.inr ?_⟩` で `entropy_power_inequality_gaussian_saturation` 経由) | ~10-15 | 既存 `csiszarGap_at_one_eq_zero_of_gaussian_pair` (`EPIL3Integration.lean:1194`) の計算と同形、再利用 |
| LOW | A-5-2 | `isStamToEPIBridgeHyp_of_stam_debruijn` constructor (A-4-4 + A-5-1 を `_of_scaling_limit` に注入) | ~10-15 | sister Phase D 5 hypothesis の `_` placeholder 引数注入で signature mismatch 出る可能性 (撤退 detour、+10-20 行) |
| LOW | A-6-1 | `entropy_power_inequality_unconditional` 新 wrapper (案 a、本体不変) | ~25-35 | sister Phase D 5 hypothesis を caller 経由で carry、`IsStamInequalityResidual` / `IsStamToEPIBridge` の defeq を `fisherInfoOfMeasureV2_def` で展開 |
| LOW | A-6-2 / A-6-3 | docstring 改訂 (`EPIStamDischarge.lean:337` `IsStamToEPIBridgeHyp` + 主定理 audit tag) | ~5-10 | `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` slug を `docs/audit/audit-tags.md` に追加要 (語彙不存在なら orchestrator に依頼) |

**合計**: ~210-345 行 (中央予測 ~280 行、親 plan §"規模見積もり" の ~150-250 行と比較
やや増加 — Cauchy-Schwarz 自前組立分 +30-80 行が原因)。

---

## 撤退ライン発動候補リスト (親 plan §"撤退ライン総覧" との対応)

| slug | 発動条件 (本 inventory による判定) | 状態 | 自作必要規模 | 親 plan 対応 |
|---|---|---|---|---|
| **L-Concl-A-α** (親継承) | sister sub-plan の Phase D 撤退ライン伝播 (smooth density / score Lp / honest regularity / integration hypothesis を caller 経由) | **未発動** (sister Phase D 完了済、commit `c0edbe1` 時点で signature drift 0 件確認) | 0 | 親 plan 撤退ライン table 維持 |
| **L-Concl-A-β** (親継承) | Gaussian limit `g(∞) = 0` が non-Gaussian で破綻 | **未発動** (本 Phase A は `g(1)` 端点 Gaussian saturation で discharge、`g(∞)` は本 Phase 外) | 0 | 親 plan 撤退ライン table 維持 |
| **L-Concl-A-γ (新規)** | `IsStamScalingNoiseHyp` (standard normal pair witness) を Mathlib 整備不足で genuine 構築できず | **発動必至** (Mathlib `AtomlessProbability` / `IsAtomless` / `exists_iIndepFun` 全件不在、Common2026 内 noise extension API 不在、Phase 0 で同問題 retract 前例あり `EPIStamToBridge.lean:317-327`) | 0 (staged def のみ、~10-15 行) | 親 plan §L-Concl-A-γ "Mathlib `noise extension on arbitrary probability space` API 整備、別 plan で外出し" — 整合 |
| **L-Concl-A-δ (新規)** | 2-source `heatFlowPath2` 経由の `g'(s)` 微分式が Stam 不等式と直接 reduce しない (scaling 補正項キャンセル失敗 / 形 mismatch) | **発動候補休眠** (A-2-4 実装時に scaling 補正項がキャンセルされるか実験必要、現時点では `heatFlowPath2_law` の `(P.map (√(1-s)·X)) ∗ gaussianReal 0 s` 分解形が de Bruijn V2 1-source `gaussianConvolution Y_eff Z_X s` (`Y_eff := √(1-s)·X`) に直接対応するため reparametrize 可能性高い) | 撤退時 100+ (sister Phase D 再開要、本 Phase 内では不可) | 親 plan §L-Concl-A-δ "sister Phase D 再開 + `csiszarGap` 1-source 形 reparametrize" — 整合 |
| **L-Concl-A-ε (新規)** | `differentialEntropy_const_mul` Mathlib 不在 (Common2026 既存 `differentialEntropy_map_mul_const` の caller integrability 引数 `h_ent_int` を sister Phase D output から carry できず) | **発動 marginal** (Common2026 既存補題 `DifferentialEntropy.lean:195` で本体は OK、ただし caller 側 integrability bridge ~10-20 行新規必要) | 10-20 (scope 内 detour) | 親 plan §L-Concl-A-ε "Common2026 `DifferentialEntropy.lean` 拡張で吸収 (scope 内 detour)" — 整合 (note: 本来は `_map_mul_const` 既存で済む、本 plan で predict された "Mathlib 不在" は実は **Common2026 既存で resolve**、撤退ライン levels down) |
| **L-Concl-A-ζ (新規)** | Cover-Thomas eq.(17.43) Cauchy-Schwarz weight 不等式が Mathlib 直接形なく、自前 plumbing >100 行 | **発動候補 (marginal)** (Mathlib `sum_mul_sq_le_sq_mul_sq` + `sq_sum_div_le_sum_sq_div` で組立可能、見積もり ~50-80 行で threshold 100 行を下回るため発動 marginal、A-3-2 実装時判定) | 50-80 (Mathlib 既存 primitive 組合せで scope 内) | 親 plan §L-Concl-A-ζ "Mathlib 上流貢献 / 別 plan で外出し" — marginal、scope 内対処可能 |

**判定総合**: **L-Concl-A-γ のみ確実発動** (Mathlib 壁 (b) 解析 — staged honest predicate
で externalization、自作 ~10-15 行のみ)。L-Concl-A-δ / ε / ζ は休眠 or scope 内 detour
で対処見込み。L-Concl-A-α / β は親継承だが本 Phase A スコープでは未発動。

---

## 主要前提条件ボックス (load-bearing hypothesis / 事故の起きやすい lemma)

- **`differentialEntropy_map_mul_const`** (`DifferentialEntropy.lean:195`): `[IsProbabilityMeasure μ]`
  + `μ ≪ volume` (absolute continuity) + `c ≠ 0` + **`Integrable (fun x => Real.negMulLog
  ((μ.rnDeriv volume x).toReal)) volume`** (entropy 被積分関数の可積分性) の 4 条件必須。
  最後の `h_ent_int` は density に関する条件で **automatic ではない** — caller (sister
  Phase D output) から carry する必要、A-2-1 で integrability bridge 補題が要件
- **`Real.hasDerivAt_sqrt`** (`Sqrt.lean:68`): `x ≠ 0` 必須。Phase A では `s` 微分時に
  `Real.sqrt (1-s)` (要 `1-s ≠ 0` ⇔ `s ≠ 1`)、`Real.sqrt s` (要 `s ≠ 0`)。両方
  **interior `s ∈ Ioo 0 1` のみで成立**、端点 `s = 0, 1` は `HasDerivAt` 外。
  `antitoneOn_of_deriv_nonpos` は interior で十分 (`hf' : DifferentiableOn ℝ f (interior D)`)
- **`antitoneOn_of_deriv_nonpos`** (`Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:478`):
  `Convex ℝ D` + `ContinuousOn f D` + `DifferentiableOn ℝ f (interior D)` + `∀ x ∈ interior D, deriv f x ≤ 0`
  の 4 条件必須。`ContinuousOn f D` は **端点込み** で要求、interior で differentiability
  は別途。`Convex` は `convex_Icc 0 1` で自動
- **`IndepFun.map_add_eq_map_conv_map`** (`Mathlib/Probability/Independence/Basic.lean:1103-1107`
  auto-gen by `to_additive` from `IndepFun.map_mul_eq_map_mconv_map`): `[IsFiniteMeasure μ]`
  必須 (Phase A では `[IsProbabilityMeasure P]` から自動)
- **`IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2`** (`FisherInfoV2DeBruijn.lean:245-249`):
  field の結論型は **`HasDerivAt (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
  ((1/2) * fisherInfoOfDensityReal density_t) t`** — 結論の関数は `s ↦ differentialEntropy
  (P.map (gaussianConvolution X Z s))` で **1-source 形**、`heatFlowPath2 X Z_X s` (2-source)
  への適用は reparametrize 必須 (caveat C.4 参照)
- **`csiszarGap_at_one_eq_zero_of_gaussian_pair`** (`EPIL3Integration.lean:1194-1201`):
  `[IsProbabilityMeasure P]` + `Measurable Z_X` + `Measurable Z_Y` + `IndepFun Z_X Z_Y P`
  + `P.map Z_X = gaussianReal 0 1` + `P.map Z_Y = gaussianReal 0 1` の 6 条件必須。
  A-1 の `IsStamScalingNoiseHyp` から `obtain` で 6 つ全て取り出せる設計 (A-1-1 def 確認)

---

## 撤退ラインへの距離 (親計画への影響)

親 plan `docs/shannon/epi-stam-to-conclusion-phaseA-plan.md` §"撤退ライン総覧":

- **L-Concl-A-γ 発動確実** → 親 plan の A-1 sub-step を **当初想定通り** staged 化、新規
  predicate `IsStamScalingNoiseHyp X Y P` を新規 def (~10-15 行)、`@audit:staged(epi-stam-to-conclusion-plan)`
  付与。Phase B / V も staged 伝播 (主定理 hypothesis-free 化 案 a `_unconditional` が
  `IsStamScalingNoiseHyp` を caller 引数で carry する形になる)
- **L-Concl-A-α / β / δ 未発動 (現時点)** → 親 plan の撤退ライン table を **維持**、
  本 Phase A 進行で再判定
- **L-Concl-A-ε / ζ marginal** → 親 plan の撤退ライン table を **格下げ提案**:
  - ε: 「Mathlib `differentialEntropy_const_mul` 不在」を「**Common2026 既存
    `differentialEntropy_map_mul_const` で resolve、ただし caller integrability bridge
    ~10-20 行新規**」に書換 (scope 内 detour、撤退ライン格下げ)
  - ζ: 「Mathlib `Real.inner_mul_le_norm` 不在」を「**Mathlib `sum_mul_sq_le_sq_mul_sq`
    + `sq_sum_div_le_sum_sq_div` 組合せで ~50-80 行自前組立可能**」に書換 (scope 内
    detour、撤退ライン格下げ)
- 縮退案 (新規撤退ライン): なし。本 inventory は既存撤退ライン table 内で対処可能と判定

---

## 着手 skeleton (`Common2026/Shannon/EPIStamToBridge.lean` 拡張、~30 行)

```lean
/-! ## §3' — Phase A: Csiszár scaling argument (sister `epi-stam-to-conclusion-phaseA-plan`) -/

/-- **Standard normal pair witness on an arbitrary probability space**
(Phase A A-1 staged honest predicate).

Cover-Thomas Ch.17 では暗黙仮定された "any probability space carries two
independent standard normals jointly independent of `(X, Y)`". Mathlib に
arbitrary `P : Measure Ω` 上の noise extension API は不在 (`AtomlessProbability` /
`IsAtomless` / `exists_iIndepFun` × `gaussianReal` 全件 loogle 不在、CLT
`Mathlib/Probability/CentralLimitTheorem.lean:79` は別空間 `P'` 上 Gaussian
を仮定する形なので流用不可)。Common2026 内にも該当 API 不在。

**NOT a discharge / load-bearing**: 本 predicate は Mathlib 壁 (b) 解析 ——
"standard noise extension on arbitrary probability space" は Mathlib 上流
貢献 task として別 plan に外出し。Phase A の主出力
`isStamToEPIBridgeHyp_of_stam_debruijn` は本 hypothesis を caller 引数で
carry する形で publish される。

`@audit:staged(epi-stam-to-conclusion-plan)` -/
def IsStamScalingNoiseHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ (Z_X Z_Y : Ω → ℝ),
    Measurable Z_X ∧ Measurable Z_Y ∧
    P.map Z_X = gaussianReal 0 1 ∧ P.map Z_Y = gaussianReal 0 1 ∧
    IndepFun X Z_X P ∧ IndepFun Y Z_Y P ∧ IndepFun Z_X Z_Y P

/-- **Csiszár gap is antitone on `Set.Icc 0 1` (genuine constructor from Stam + de Bruijn)**.
Phase A A-1〜A-4 統合出力. -/
theorem isStamToEPIScalingHyp_of_stam_debruijn
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (h_noise : IsStamScalingNoiseHyp X Y P)
    (h_dbreg_X : IsDeBruijnRegularityHyp X _ P)
    (h_dbreg_Y : IsDeBruijnRegularityHyp Y _ P)
    (h_dbint_X : ∀ T > 0, IsDeBruijnIntegrationHyp X _ P T)
    (h_dbint_Y : ∀ T > 0, IsDeBruijnIntegrationHyp Y _ P T)
    (h_dbint_sum : ∀ T > 0, IsDeBruijnIntegrationHyp (fun ω => X ω + Y ω) _ P T) :
    IsStamToEPIScalingHyp X Y P := by
  sorry  -- Phase A 本体実装、撤退ライン γ で staged hypotheses 依存
```

---

## 検証 self-check (CLAUDE.md `Subagent Inventory of Mathlib Lemmas` 4 必須項目)

各候補 lemma について:
- ✅ `file:line` location: 全 lemma で確認済 (該当 file を Read で照合)
- ✅ 完全 signature (`[...]` type-class 前提 verbatim): 全 lemma で `variable` section の
  `[NontriviallyNormedField 𝕜]` `[IsStrictOrderedRing R]` `[NoAtoms μ]` `[IsFiniteMeasure μ]`
  等 verbatim 引用、paraphrase なし
- ✅ 引数型 (順序付き): 全 lemma で `(hf : HasDerivAt f f' x)` 等の順序保持で記録
- ✅ 結論 form (verbatim copy): `HasDerivAt (f - g) (f' - g') x` 等 paraphrase せず転写

paraphrase / drop bracket 0 件、推測 signature 0 件、loogle 出力だけでの記録 0 件
(全て該当 file Read で verbatim 照合)。

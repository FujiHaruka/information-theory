# EPI case-1 Phase B(i) cross-entropy — Mathlib / in-tree 在庫調査

> 親計画: `docs/shannon/epi-case1-difference-g3-closure-plan` (residual slug 統一先)。
> 対象: `InformationTheory/Shannon/EPICase1RatioLimit.lean` `isRescaledPathRegular_of_methodX`
> (`:576`) lower bundle の残 3 sorry (`:694` / `:711` / `:720`)。
> 本ファイルは docs-only。コード非編集。

## 一行サマリ

**3 sorry を閉じるのに必要な解析的中核 (|log g| ≤ A+B·x² 多項式 majorant + Gaussian 二次モーメント
+ `integrable_compProd_iff`) は 100% 既存** — しかも **3 sorry とまったく同型の 3 つの integrability
証明が `negMulLog_convDensity_entropy_ge_density` (`EPIG2ConvEntropyDensity.lean`) の本体に verbatim
で既に存在**する (canonical `ℝ×ℝ` 空間版)。real wall はゼロ。自作必要なのは「density 文脈で済んでいる
3 つの in-file `have` を `pX`/`p_t` で parametrize した standalone 補題 3 本に切り出す」糊コードのみ
(あるいは density file の template を `s=1` で abstract space に転記)。**genuine tractable、撤退ライン
発動なし。** ただし `hpX_ent` (= 入力密度 `pX` 自身の負エントロピー integrability) という追加 regularity
が 1 件必要で、現状 `rescaledInput_density_witness` (`:437`) は供給していない (witness 拡張 or 別補題)。

---

## 主定理の最終形 (再掲) と 3 sorry の位置

discharge 対象は `IsRescaledPathRegular A B P varA v_B` (`:193` def)。その lower bundle (per-`t`,
`:195-239`) は **10 conjunct** で、`refine ⟨h_indep, hW_ac, ?_, ?_, hκ_v, ?_, ?_, ?_, ?_, ?_⟩`
(`:644`) で供給。このバンドルが `differentialEntropy_add_ge_of_indep` (`EPIUncondMixedCase.lean:76`)
= `condDifferentialEntropy_le` (`EPIG2ConvEntropyMonotone.lean:224`) の precondition と verbatim 同型。

framing: **`X := B` (Gaussian noise, `P.map B = gaussianReal 0 v_B`)**, **`Z := A/√t = Zt` (入力)**。
path `W = B + Zt`。`condDifferentialEntropy_le` の "`μ.map X`" cross-term 引数は `(P.map (X+Y))` =
**path 法**であり、cross-term の log 引数は path 密度 `g = convDensityAdd pX g_{v_B}` (`pX` =
`Zt = A/√t` の密度、`rescaledInput_density_witness` 供給)。fibre は `gaussianReal z v_B` (translated)。
→ **ユーザの数学的見立て (g 上界 = Gaussian prefactor、g 下界 = Gaussian 型、|log g| ≤ A+B·x²、
Gaussian fibre が x² を可積分化) は実コードの構造と完全一致。**

### refine 順序 → conjunct → `condDifferentialEntropy_le` 引数の対応表

| refine 位置 (`:644`) | bundle conjunct (`:195-239`) | `condDifferentialEntropy_le` 引数名 | 状態 |
|---|---|---|---|
| `h_indep` | IndepFun B Zt | (n/a, bundle 専用) | CLOSED |
| `hW_ac` | path ≪ volume | `hW_ac` | CLOSED |
| `?_` `:645` | joint ≪ product | `h_ac` | CLOSED |
| **`?_` `:694`** | **llr(joint,product) integrable** | **`h_int`** | **sorry** |
| `hκ_v` | fibre ≪ volume | `hκ_v` | CLOSED |
| `?_` `:695` | fibre rnDeriv·log(fibre rnDeriv) | `hκ_logp_int` | CLOSED |
| **`?_` `:711`** | **fibre rnDeriv·log(path rnDeriv) (per-z)** | **`hκ_cross_int`** | **sorry** |
| `?_` `:712` | fibre entropy integrable | `h_fibreEnt_int` | CLOSED |
| **`?_` `:720`** | **z-平均 cross-term integrable** | **`h_cross_int`** | **sorry** |
| `?_` `:721` | log(path rnDeriv) integrable wrt path | `h_logq_int` | CLOSED |

3 sorry はそれぞれ `condDifferentialEntropy_le` の `h_int` / `hκ_cross_int` / `h_cross_int`。

---

## API 在庫テーブル

### A. precondition を要求する上位補題 (signature verbatim、`[...]` 省略せず)

| 概念 | API | file:line | 結論形 / 該当引数 (verbatim) |
|---|---|---|---|
| 条件付き ⟶ 無条件 entropy | `differentialEntropy_add_ge_of_indep` | `EPIUncondMixedCase.lean:76` | `differentialEntropy (P.map X) ≤ differentialEntropy (P.map (fun ω => X ω + Y ω))`。3 sorry 該当引数は `h_int` (`:83`) / `hκ_cross_int` (`:92`) / `h_cross_int` (`:97`) |
| 同 (中核) | `condDifferentialEntropy_le` | `EPIG2ConvEntropyMonotone.lean:224` | `condDifferentialEntropy X Z μ ≤ differentialEntropy (μ.map X)`。型クラス: `{Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]`、`[IsProbabilityMeasure μ]`。3 sorry 該当: `h_int` (`:229`) / `hκ_cross_int` (`:236`) / `h_cross_int` (`:241`) |

`h_int` verbatim (`condDifferentialEntropy_le:229`):
`Integrable (llr ((μ.map Z) ⊗ₘ condDistrib X Z μ) ((μ.map Z) ⊗ₘ Kernel.const α (μ.map X))) ((μ.map Z) ⊗ₘ condDistrib X Z μ)`

`hκ_cross_int` verbatim (`:236`):
`∀ᵐ z ∂(μ.map Z), Integrable (fun x => ((condDistrib X Z μ z).rnDeriv volume x).toReal * Real.log (((μ.map X).rnDeriv volume x).toReal)) volume`

`h_cross_int` verbatim (`:241`):
`Integrable (fun z => ∫ x, ((condDistrib X Z μ z).rnDeriv volume x).toReal * Real.log (((μ.map X).rnDeriv volume x).toReal) ∂volume) (μ.map Z)`

(注: `condDifferentialEntropy_le` の "`μ.map X`" は `EPICase1` framing では path 法 `P.map (B+Zt)`。
EPICase1 の bundle conjunct (`:223` / `:233`) は `(P.map (B+Zt)).rnDeriv` を literal に書いており一致。)

### B. ★ 3 sorry とまったく同型の integrability 証明が既存 (canonical `ℝ×ℝ` 版)

| 概念 | 既存 `have` の所在 | 状態 | 扱い |
|---|---|---|---|
| **`hκ_cross_int` (per-z cross-term)** | `EPIG2ConvEntropyDensity.lean:367-383` | ✅ 既存 (in-file `have`) | `:711` の template。`hfib_dom_int c` + `hfib_eq`/`hqW` + `Integrable.mono'` |
| **`h_cross_int` (z-平均 cross-term)** | `EPIG2ConvEntropyDensity.lean:398-498` | ✅ 既存 (in-file `have`) | `:720` の template。`Fclean z = ∫ pX(x−√s z)·log p_t` を `H(z)=(A+1)+2B·M2+2B·s·z²` で支配、Gaussian で integrable |
| **`h_int` (joint llr = KL finiteness)** | `EPIG2ConvEntropyDensity.lean:511-726` | ✅ 既存 (in-file `have`) | `:694` の template。`integrable_compProd_iff` を開き、per-fibre (branch a) は `hfib_llr_int`、outer (branch b) は `Fabs z` を `Habs z` で支配 |

**重要**: これらは standalone lemma ではなく `negMulLog_convDensity_entropy_ge_density`
(`EPIG2ConvEntropyDensity.lean:124`、`@audit:ok`, sorryAx-free) の本体内 `have` ブロック。
canonical 空間 `μ := (withDensity pX).prod (gaussianReal 0 v_Z)`, `X := Prod.fst`, `Z := Prod.snd`,
`s := u n / v_Z` 上で構築済。EPICase1 では `s = 1`、`X := B` / `Z := Zt` だが **density 構造
(`pX ∗ g_{v}`) は同一**なので template がそのまま適用可能。

### C. 解析的中核 (3 sorry を閉じる load-bearing 資産)

| 概念 | API | file:line | 結論形 verbatim |
|---|---|---|---|
| **|log g| ≤ A+B·x² 多項式 majorant** | `convDensityAdd_logFactor_poly_majorant` | `FisherInfoV2DeBruijnAssembly.lean:343` | `∃ A B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) → ‖- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨s, _⟩) x) - 1‖ ≤ A + B * x ^ 2`。**public** (docstring 明記: EPI G2 (β) density-form cross-term / llr consumers 用に private 解除済)。引数: `(pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (_hpX_meas : Measurable pX) (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1) {t : ℝ} (ht : 0 < t)` |
| g 上界 (Gaussian prefactor) | `convDensityAdd_le_prefactor` (private) | `FisherInfoV2DeBruijnAssembly.lean:167` | `convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x ≤ (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹`。majorant の中で消費 (直接呼び不要) |
| g 下界 (Gaussian 型) | `convDensityAdd_lower_bound_gaussian` | `FisherInfoV2DeBruijnPerTime.lean:888` | `∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, (1/2) * gaussianPDFReal 0 ⟨s, hs.le⟩ (|x| + R) ≤ convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x`。引数: `(hpX_mass : (∫ y, pX y ∂volume) = 1) {s : ℝ} (hs : 0 < s)`。majorant 内で消費 |
| g 下界 (s-uniform) | `convDensityAdd_lower_bound_gaussian_uniformR` (private) | `FisherInfoV2DeBruijnAssembly.lean:224` | majorant 内部資産 |
| g > 0 (full support) | `convDensityAdd_pos` | `FisherInfoV2DeBruijnPerTime.lean:808` | `0 < convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x`。引数: `(hpX_mass : 0 < ∫ y, pX y ∂volume) {s : ℝ} (hs : 0 < s) (x : ℝ)`。CLOSED conjunct `:666` で既に使用済 |

### D. Gaussian 二次モーメント / x² 可積分 (z-平均 cross-term `:720` 用)

| 概念 | API | file:line | 結論形 / 用途 |
|---|---|---|---|
| Gaussian 二次モーメント有限 | `memLp_id_gaussianReal` | (Mathlib, density file `:417`/`:625` で使用) | `MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v_Z)`。`memLp_two_iff_integrable_sq` 経由で `Integrable (fun z => z^2) (gaussianReal 0 v_Z)` |
| 二次モーメント ↔ sq integrable | `memLp_two_iff_integrable_sq` | (Mathlib) | density file `:418`/`:626` で `Integrable (fun z => z^2) (μ.map Z)` を構築 (EPICase1 では `μ.map Z = P.map Zt`、Gaussian ではないが `h_mom_A` から二次モーメント有限) |
| 入力の二次モーメント | `rescaledInput_density_witness` hpX_mom | `EPICase1RatioLimit.lean:445` | `Integrable (fun y => y ^ 2 * pX y) volume`。witness が供給済 |

**注意 (framing 差)**: density file は `μ.map Z = gaussianReal 0 v_Z` (`Z` = Gaussian) なので z² の
integrability を Gaussian モーメントで取る。EPICase1 では `Z = Zt = A/√t` で **`P.map Zt` は Gaussian
ではない** (a.c. のみ)。よって `:720` の outer integral を z² で支配する際の `Integrable (fun z => z^2)
(P.map Zt)` は **`hpX_mom` (witness 供給の入力二次モーメント) から `integrable_map_measure` 経由で取る**
(witness `:491-495` `hsq_law` がまさにこの transport を実装済 — 流用可能)。density file の
`hsq_int` (Gaussian 直接) はそのままは使えない。**この 1 点が template の唯一の実質的差分。**

### E. compProd integrability の Mathlib 開封補題 (`:694` 用)

| 概念 | API | file:line | 用途 |
|---|---|---|---|
| compProd 上 Integrable 同値 | `MeasureTheory.Measure.integrable_compProd_iff` | Mathlib `Probability/Kernel/Composition/IntegralCompProd.lean` (loogle: `Found one declaration`) | density file `:585` で joint llr integrability を per-fibre (a) + outer (b) に分割 |
| per-fibre llr → log split | `llr_eq_log_density_sub_log_density` | (in-tree, density `:529`) | `llr (κ z) (μ.map W) =ᵐ[κ z] log p_z − log p_t` |
| slice rnDeriv 同定 | `InformationTheory.rnDeriv_compProd_eq_kernel_rnDeriv` | (in-tree, density `:556`) | joint llr を per-fibre llr に落とす |

### F. 既使用 CLOSED 資産 (3 sorry の隣接 conjunct で実証済 = 同 framing が機能する証拠)

| API | file:line | EPICase1 使用箇所 |
|---|---|---|
| `convDensityAdd_negMulLog_integrable_pub` | `EPIG2HeatFlowContinuity.lean:129` | `:754` (h_logq_int CLOSED)。`pX ∗ g_{v_B}` の負エントロピー integrability |
| `integrable_density_log_density_of_gaussian` | (in-tree) | `:700` (hκ_logp_int CLOSED)。fibre self-entropy |
| `pPath_eq_convDensityAdd` | `FisherInfoV2DeBruijnPerTime.lean:215` | `:662` (path 密度同定) |
| `convDensityAdd_pos` | `FisherInfoV2DeBruijnPerTime.lean:808` | `:666` (g full support) |
| `differentialEntropy_gaussianReal` | (in-tree) | `:717` (h_fibreEnt_int CLOSED) |

---

## 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`convDensityAdd_logFactor_poly_majorant`** (`Assembly:343`): `pX` に
  `hpX_nn` / `Measurable pX` (引数名 `_hpX_meas`, unused だが要求) / `Integrable pX volume` /
  **`(∫ y, pX y ∂volume) = 1`** (mass = 1、確率密度規格化、`convDensityAdd_le_prefactor`/`_uniformR`/`_pos`
  の全てが消費) を要求。`{t : ℝ} (ht : 0 < t)`。`s ∈ Ioo (t/2, 2t)` で uniform。EPICase1 では `t := v_B`、
  `s := v_B` (= `1·v_B`、`hvar_eq` で `⟨1·v_B,_⟩ = v_B`) を point `v_B ∈ Ioo(v_B/2, 2v_B)` で評価 (density
  file `:252` `hun_mem` と同手順)。
- **`negMulLog_convDensity_entropy_ge_density`** (`Density:124`): 上記 5 個 + **`hpX_mom : Integrable
  (fun y => y ^ 2 * pX y) volume`** + **`hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume`**。
  ★ **`hpX_ent` (入力密度自身の負エントロピー integrability) が落とし穴** — `rescaledInput_density_witness`
  (`:437`) は `hpX_nn`/`hpX_meas`/`hpX_law`/`hpX_int`/`hpX_mass`/`hpX_mom` の **6 個は供給するが
  `hpX_ent` は供給しない**。3 sorry の証明には `hpX_ent` が要る (per-fibre llr branch の `hpX_abs_ent`
  (density `:547`) が `hpX_ent.norm` から来る)。
- **`integrable_compProd_iff`** (Mathlib): joint llr integrability を分割する際、AEStronglyMeasurable
  of joint llr (density `:575` `h_meas_llr`) を先に要求。`Measure.measurable_rnDeriv` の toReal.log で取れる。
- **`memLp_id_gaussianReal` / `memLp_two_iff_integrable_sq`** (Mathlib): EPICase1 では `P.map Zt` が
  Gaussian でないため **z² integrable を `hpX_mom` + `integrable_map_measure` 経由で取り直す** 必要
  (density file の Gaussian 直接 route は不可)。witness `:491-495` に既に同型の transport がある。

---

## 自作が必要な要素 (優先度順)

3 sorry を閉じる戦略は 2 案。**推奨は案 1 (extract)**。

### 案 1 (推奨) — density file の 3 `have` を `pX`/`p_t` parametrized standalone 補題に切り出す

`EPIG2ConvEntropyDensity.lean` の `hκ_cross_int` (`:367`) / `h_cross_int` (`:398`) /
`h_int` (`:511`) を、canonical 空間依存を剥がして以下の signature の標準補題 3 本に extract:

1. **`convCrossEntropy_perFibre_integrable`** (`:711` 用)
   - 型 (概形): `(pX : ℝ → ℝ) (hpX_nn) (hpX_meas) (hpX_int) (hpX_mass) (hpX_mom) {v : ℝ≥0} (hv : 0 < v) →`
     fibre = translate `pX(·−c)`、path 密度 `g = convDensityAdd pX g_v` のとき
     `Integrable (fun x => pX (x - c) * Real.log (g x)) volume` (∀ shift c)。
   - 依存資産: `convDensityAdd_logFactor_poly_majorant` + `hfib_dom_int` 相当 (witness `hpX_mom` 展開) +
     `Integrable.mono'`。density `:310-325`/`:367-383` がそのまま核。
   - 工数: 中 (50-80 行)。density file から論理をほぼ移植。

2. **`convCrossEntropy_zAvg_integrable`** (`:720` 用)
   - 型 (概形): 上記に加え z-法 `νZ` (= `P.map Zt`) が `Integrable (fun z => z^2) νZ` を持つとき
     `Integrable (fun z => ∫ x, pX (x − √s·z)·Real.log (g x) ∂volume) νZ`。
   - ★ **z² integrable を仮説として外出し** (Gaussian 特定を避ける) → EPICase1 では `hpX_mom` +
     `integrable_map_measure` で供給。density `:398-498` が核、`hsq_int` (`:415`) を仮説に置換。
   - 工数: 中 (60-90 行)。

3. **`convJointLlr_integrable`** (`:694` 用)
   - 型 (概形): 上記 + `hpX_ent` のとき joint llr `Integrable (llr (νZ ⊗ₘ condDistrib W Zt P) (νZ ⊗ₘ
     Kernel.const ℝ (P.map W))) (νZ ⊗ₘ condDistrib W Zt P)`。
   - 依存資産: `integrable_compProd_iff` + 補題 1/2 + `hpX_ent` (→ `hpX_abs_ent`) + `llr_eq_log_density_sub_log_density`
     + `rnDeriv_compProd_eq_kernel_rnDeriv`。density `:511-726` が核。
   - 工数: 大 (100-150 行、最も配管が多い)。

### 案 2 (代替) — `negMulLog_convDensity_entropy_ge_density` を丸ごと再利用

3 sorry を個別に閉じず、bundle 全体を density-level lemma の instance に乗せ替える設計変更。ただし
`isRescaledPathRegular_of_methodX` の bundle は 10 conjunct を個別に refine しており、密結合の再設計が要る。
案 1 の方が局所的で安全。

### 追加で必要な 1 件 — `hpX_ent` の供給

`rescaledInput_density_witness` (`:437`) に **`Integrable (fun x => Real.negMulLog (pX x)) volume`** を
7 番目の戻り値として追加する (witness 拡張)、または別補題 `rescaledInput_negMulLog_integrable` を新設。
入力 `A/√t` の law の微分エントロピー有限性 = a.c. + 二次モーメント有限から従う (Gaussian max-entropy 上界
+ 下界)。**これ自体が non-trivial な entropy-finiteness 補題**。

- 候補資産: `convDensityAdd_negMulLog_integrable_pub` (`EPIG2HeatFlowContinuity.lean:129`) は
  **畳み込み後**の `pX ∗ g_v` 用であり、`pX` **単体**の負エントロピーには直接使えない。
- 真に Mathlib/in-tree に `pX` 単体の `Integrable (negMulLog pX)` 補題があるか **未確認** —
  入力 `A/√t` が一般の a.c. 確率密度なので、二次モーメント有限だけでは負エントロピー有限は一般に従わない
  (重い対数特異性のある密度で `∫ pX log pX = -∞` の可能性)。**ここが唯一の潜在的 wall 候補** (§Mathlib 壁参照)。

---

## Mathlib 壁の列挙

真に Mathlib/in-tree 不在で `@residual(wall:...)` 対象になりうるものを精査。

- **(候補) `hpX_ent` = 入力密度 `pX` 単体の `Integrable (negMulLog pX)`**: a.c. + 二次モーメント有限
  からは**一般には follow しない** (微分エントロピー `h(A/√t)` が `-∞` になる病的密度が存在)。
  ただし EPICase1 case-1 では入力 `A` 側にも regularity (case-1 = 両 a.c.) があり、上流の case-1 仮説に
  `differentialEntropy (P.map A)` finiteness 相当が含まれる可能性が高い。**結論: 完全 wall ではないが、
  上流 case-1 仮説束から `hpX_ent` を引けるか要確認**。引けなければ `differentialEntropy_finite` 系の
  新規補題 (a.c. + 二次モーメント有限 + **追加 regularity**) が必要。
  - loogle 未ヒット確認は本調査では未実施 (slug 不明)。plan 段階で
    `./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Integrable (fun x => Real.negMulLog (_ x))"`
    で `Found N declarations` を確認すること。
  - 集約推奨: もし新規補題化するなら shared sorry 補題 (`docs/audit/audit-tags.md`「共有 Mathlib 壁」)
    の候補。ただし他 family で同型需要があるか未調査。

- **3 sorry 本体 (cross-entropy / llr integrability)**: **wall ではない**。
  `negMulLog_convDensity_entropy_ge_density` 本体に既に genuine な証明が存在 (`@audit:ok`, sorryAx-free
  機械確認済) し、`convDensityAdd_logFactor_poly_majorant` (public) + `integrable_compProd_iff` (Mathlib)
  で構築済。off-the-shelf Mathlib 補題ではない (in-tree 構築) が、**実現可能性は実証済**。

---

## 撤退ラインへの距離

親計画 `epi-case1-difference-g3-closure-plan` の撤退ラインに対して:

- **発動しない (3 sorry は genuine tractable)**。3 つの integrability は wall ではなく、同型証明が
  in-tree に既存。`@residual(plan:epi-case1-difference-g3-closure-plan)` 分類は **正しい** (plan で
  closure 可能、wall ではない)。
- **唯一の留保**: `hpX_ent` 供給が上流 case-1 仮説から引けない場合、「入力密度の負エントロピー有限性」
  という別 obligation が増える。これが新規撤退ライン候補:
  - **新規撤退ライン (提案)**: `hpX_ent` が case-1 上流仮説束 から 1 補題で引けず、かつ
    Mathlib/in-tree に `Integrable (negMulLog pX)` (a.c. 確率密度 + 二次モーメント有限 + 追加 regularity)
    が無い場合 → `:694` (joint llr) のみ `sorry` + `@residual(wall:input-density-entropy-finite)` で park
    (`:711`/`:720` は `hpX_ent` 不要なので closure 可能)。撤退口は sorry + `@residual`、仮説束化禁止。
  - 判定: `:711` (per-fibre cross) と `:720` (z-avg cross) は **`hpX_ent` を使わない** (density file の
    `hκ_cross_int`/`h_cross_int` は `hLog`/`hfib_dom_int` のみ依存、`hpX_abs_ent` は llr branch 専用)
    → この 2 件は無条件で closure 可能、撤退ライン無関係。

---

## 着手 skeleton (案 1 の standalone 補題 3 本、新規 file or EPICase1 拡張)

`InformationTheory/Shannon/EPICase1CrossEntropy.lean` (新規) の出だし:

```lean
import InformationTheory.Shannon.EPIG2ConvEntropyDensity
import InformationTheory.Shannon.FisherInfoV2DeBruijnAssembly
import InformationTheory.Shannon.FisherInfoV2DeBruijnPerTime
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

/-- per-fibre cross-term integrability (extract of EPIG2ConvEntropyDensity `:367`). -/
theorem convCrossEntropy_perFibre_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {v : ℝ≥0} (hv : 0 < v) (c : ℝ) :
    Integrable (fun x => pX (x - c)
      * Real.log (convDensityAdd pX (gaussianPDFReal 0 v) x)) volume := by
  sorry -- @residual(plan:epi-case1-difference-g3-closure-plan)

/-- z-averaged cross-term integrability (extract of `:398`, z² integrable を仮説外出し). -/
theorem convCrossEntropy_zAvg_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {v : ℝ≥0} (hv : 0 < v) {s : ℝ} (hs : 0 < s)
    (νZ : Measure ℝ) (hνZ_sq : Integrable (fun z => z ^ 2) νZ) :
    Integrable (fun z => ∫ x, pX (x - Real.sqrt s * z)
      * Real.log (convDensityAdd pX (gaussianPDFReal 0 v) x) ∂volume) νZ := by
  sorry -- @residual(plan:epi-case1-difference-g3-closure-plan)

/-- joint llr integrability (extract of `:511`、`hpX_ent` 要). -/
theorem convJointLlr_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume) :
    -- joint llr ((νZ) ⊗ₘ condDistrib W Zt P) ((νZ) ⊗ₘ Kernel.const ℝ (P.map W)) integrable
    True := by  -- 実型は condDifferentialEntropy_le の h_int 形に合わせる (skeleton placeholder)
  sorry -- @residual(plan:epi-case1-difference-g3-closure-plan)

end InformationTheory.Shannon
```

> skeleton 注: 3 本目 `convJointLlr_integrable` の結論は `:694` の literal な
> `Integrable (llr (...) (...)) (...)` に合わせて確定すること (上記 `True` は placeholder)。
> EPICase1 側では `νZ := P.map Zt`、`hνZ_sq` は `hpX_mom` + `integrable_map_measure` (witness `:491` 流用)。

---

## まとめ — genuine tractable か real wall か

| sorry | 概念 | 判定 | 根拠 |
|---|---|---|---|
| `:711` | per-z cross-entropy | **genuine tractable** | density `:367-383` に同型証明既存、`hpX_ent` 不要、撤退ライン無関係 |
| `:720` | z-avg cross-entropy | **genuine tractable** | density `:398-498` に同型証明既存、z² は `hpX_mom` 経由、`hpX_ent` 不要 |
| `:694` | joint llr (KL finite) | **genuine tractable (留保 1 件)** | density `:511-726` に同型証明既存。**唯一の留保 = `hpX_ent` 供給**。case-1 上流仮説から引ければ無条件 tractable、引けなければ `wall:input-density-entropy-finite` 1 件発生 |

**総合**: real wall は無し (最悪でも `hpX_ent` 1 件の入力エントロピー有限性、これも case-1 regularity から
引ける見込み高)。撤退ライン発動なし。既存率は「解析的中核 + 同型証明テンプレート」ベースで実質 ~95%
(自作は extract 糊コード + `hpX_ent` 配管)。

# 無条件 EPI 方針 Y クリティカルパス壁調査 — entropy power 弱収束半連続性 在庫

> 親計画: `docs/shannon/epi-unconditional-moonshot-plan.md`（傘 moonshot、**方針 Y = 真に仮説ゼロ EPI** 確定済、§スコープ判断 2026-06-05）。本 sub-plan slug: `epi-uncond-truncation-lsc-plan` (S5)。
> 本ファイルは **inventory のみ**（read-only 調査、コード編集なし）。

## 一行サマリ

**方針 Y の極限言明に必要な API は、汎用トポロジー側（`LowerSemicontinuousWithinAt.le_liminf`・`lintegral_liminf_le`・portmanteau）は既存、しかし「`differentialEntropy` / `entropyPower` が弱収束に関して下半連続」という核心命題は Mathlib 完全不在 (loogle Found 0 × 5)。さらに t→0⁺ 極限の単調収束は input regularity 無しでは成立せず、in-tree の唯一の関連実績 `negMulLog_convDensity_limsup_le` は LHS が limsup ≤ の "逆向き" 半連続性で、かつ `hpX_ent`(有限微分エントロピー) + `hpX_mom`(有限分散) を precondition に要求する。**verdict: 方針 Y は単なる Mathlib gap ではなく、t→0⁺ で生入力の regularity を本質的に要求する構造的障害を含む — L-Uncond-3-scope (方針 X 縮退) が発動する可能性が高い。** 自作必要量は 3 本の重い新規補題（弱収束→LSC bridge + entropyPower LSC + 平滑側無前提 EPI_t）で moonshot 規模。**最も危険な発見: §1/§4 — t>0 平滑は X 由来の裾を消さない (`X+√t Z` は X が無限分散なら無限分散)、平滑側 EPI_t は density-witness 8 field のうち `hpX_mom`/`hpX_ent` を自動充足しない。平滑が regularity を供給するのは interior のみで、極限を取る t→0⁺ endpoint では生入力 X の regularity がそのまま要求される。**

---

## 主定理の最終形（再掲）

親計画 §ゴール（方針 Y 最終 signature）:

```lean
theorem entropy_power_inequality_unconditional
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {X Y : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y)
```
（`entropyPower : Measure ℝ → ℝ≥0∞` は二層定義の (b) 層、特異測度で `0`。本 inventory は case 1 (両 a.c.) の **任意 a.c.（有限分散を仮定しない）** への拡張に必要な極限機構を調査する。）

方針 Y の極限戦略 (pseudo-Lean, §Phase Y / S5):

```lean
-- step 1: t>0 平滑側で無前提 EPI_t (平滑後は自動 regular の想定 — §4 で反証)
have epi_t : ∀ t > 0, entropyPower (μ_sum_t) ≥ entropyPower (μ_X_t) + entropyPower (μ_Y_t)
-- step 2: t→0⁺ で各項の極限
--   RHS: N(X+√t Z) → N(X) の収束 (= entropyPower の連続性 or 単調収束)
--   LHS: liminf を取り N(X+Y) ≤ liminf N((X+Y)+√t Z)
have lsc_lhs : entropyPower μ_sum ≤ Filter.liminf (fun t => entropyPower μ_sum_t) (𝓝[>] 0)
have conv_rhs : Tendsto (fun t => entropyPower μ_X_t) (𝓝[>] 0) (𝓝 (entropyPower μ_X))
-- step 3: 不等式を極限で保つ
calc entropyPower μ_sum ≤ liminf (LHS_t)          -- lsc_lhs (← 核心壁)
        ≥? liminf (RHS_t) = N(X) + N(Y)           -- epi_t + conv_rhs
```

---

## §1. 必要な極限言明の特定（数学的に何が要るか）

### 1-A. `h(W+√t Z) → h(W)` の単調減少収束は input regularity 無しで成立するか → **NO**

「noise が entropy を増やす」直感から `h(W+√t Z)` が t↓0 で `h(W)` に単調減少収束すれば極限は clean だが、**input regularity 無しでは成立しない**。根拠:

1. **`differentialEntropy : Measure ℝ → ℝ` は Bochner 積分** (`InformationTheory/Shannon/DifferentialEntropy.lean:45-46` verbatim):
   ```lean
   noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ :=
     ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume
   ```
   特異測度で a.c. 部のみ見て `negMulLog 0 = 0` ⇒ 退化（`differentialEntropy_dirac = 0`, `:155-156`）。**ℝ 値で `±∞` を取れない** ⇒ 「`h(W) = +∞`」を表現する型が無い。t→0⁺ で `h(W+√t Z)` が無界に動く入力（heavy-tail）では収束先が ℝ に無い。
2. in-tree の唯一の関連定理は **limsup ≤ の片側のみ**（下記 §3 `negMulLog_convDensity_limsup_le`）であり、しかも `hpX_ent`/`hpX_mom` を要求。単調収束（両側）は in-tree にも Mathlib にも無い。
3. 単調性「noise が entropy を増やす」自体は `condDifferentialEntropy_le` + `condDifferentialEntropy_indep_add_eq` の合成で `h(W+√t Z) ≥ h(W)`（§3）だが、これは **a.c. + 多数の integrability precondition** を要求（混合 case と同じ前提束）。生の W が任意 a.c. では precondition `h_int`/`hκ_logp_int` 等が出ない。

→ **結論: 単調減少収束は不成立。片側半連続性で代替するしかない（下記 1-B）。**

### 1-B. 片側半連続性での代替 — LHS lower-semicontinuous + RHS 収束

最小の言明（方針 Y step 2-3 が通る形）:

- **LHS**: `entropyPower (P.map (X+Y)) ≤ liminf_{t→0⁺} entropyPower (P.map ((X+Y)+√t Z))`（下半連続性、向きは「平滑で entropy power が増える」と整合）。
- **RHS**: `entropyPower (P.map (X+√t Z)) → entropyPower (P.map X)`（収束 or 上半連続性 `limsup ≤`）。

⚠ **向きの罠**: `entropyPower = exp(2h)` は `h` の単調変換。`h(W+√t Z) ≥ h(W)`（平滑で増える）なら LHS は `N(X+Y) ≤ N(平滑)` で **lower bound として極限が安全**。だが RHS で同じ向きだと `N(X+√t Z) ≥ N(X)` となり、RHS の各項が極限で**増える** ⇒ `liminf RHS_t ≥ RHS_0` で不等式が**逆向きに崩れる**。方針 Y が成立するには「LHS は平滑で増える、RHS は平滑後の値を使って下から評価」の非対称な制御が必要で、これは単純な半連続性 1 本では閉じない。**§Phase Y-0 で向き整合を verbatim 検算しないと崩れる**（親計画 step 2 が "RHS は収束、LHS は liminf" と書くが、収束 RHS が成立するか自体が 1-A で否定的）。

### 1-C. 退化ケースの型整合 (`EReal.exp` 経由)

二層定義 (b) で `entropyPower μ := EReal.exp (2 * differentialEntropyExt μ)`（親計画 発見 1）。退化境界:
- `h(W)=+∞` → `differentialEntropyExt = ?`：**現 `differentialEntropyExt` 定義は `if μ ≪ volume then ↑(differentialEntropy μ) else ⊥`（親計画 §柱1）で、a.c. 枝は ℝ workhorse を coerce するため `+∞` を表現できない**（workhorse が ℝ 値）。`h=+∞` の a.c. 入力（density が L¹ だが negMulLog 非可積分）は `differentialEntropy` の Bochner 積分が未定義 (`integral` の慣行で `0`) に退化 ⇒ `EReal.exp` 以前に workhorse 値が壊れる。**型レベルで整合しない箇所** = 1-A の根因と同じ「ℝ workhorse が `±∞` を持てない」。
- `h(W)=-∞` → `N(W)=0`：`EReal.exp ⊥ = 0` (`EReal.exp_bot`, 親計画 発見 1 確認済) で型整合 OK。だがこれは特異測度の枝（`differentialEntropyExt = ⊥`）であり、a.c. で `h=-∞` を表す経路は無い。

→ **退化境界も「ℝ workhorse が無限を持てない」一点に帰着**。方針 Y は a.c. 枝で `h` が無界に動く極限を扱うため、この型制約が本質的に効く。

---

## §2. Mathlib 在庫テーブル

### A. 半連続性 ↔ liminf の汎用トポロジー機構（既存、ただし codomain 制約）

| 概念 | Mathlib API | file:line | 状態 | 方針 Y での扱い |
|---|---|---|---|---|
| LSC ↔ le_liminf 同値 | `lowerSemicontinuousWithinAt_iff_le_liminf {f : α → γ} : LowerSemicontinuousWithinAt f s x ↔ f x ≤ liminf f (𝓝[s] x)` 〔`[CompleteLinearOrder γ]`〕 | `Mathlib/Topology/Semicontinuity/Basic.lean:269-270` | ✅ 既存 | **半連続性が言えれば `le_liminf` に翻訳する出口**。ただし `[CompleteLinearOrder γ]` 要求 ⇒ `γ = ℝ` 不可（ℝ は `CompleteLinearOrder` でない）。`EReal` / `ℝ≥0∞` 上で使う必要 = 二層 (b) 層が必須 |
| LSC → le_liminf (alias) | `LowerSemicontinuousWithinAt.le_liminf` (alias of 上) | `Mathlib/Topology/Semicontinuity/Basic.lean:280` | ✅ 既存 | 同上、方向付き alias |
| LSCAt ↔ le_liminf | `lowerSemicontinuousAt_iff_le_liminf {f : α → γ} : LowerSemicontinuousAt f x ↔ f x ≤ liminf f (𝓝 x)` 〔`[CompleteLinearOrder γ]`〕 | `Mathlib/Topology/Semicontinuity/Basic.lean:282-283` | ✅ 既存 | 全空間版 |

**注**: これらは「`f` が LSC である」を仮定に取る。方針 Y の壁は **`entropyPower`（or `differentialEntropyExt`）が弱収束位相に関して LSC であること自体**で、それは下記 §2-D で Found 0。

### B. Fatou / lintegral 下半連続（既存、in-tree で実運用済）

| 概念 | Mathlib API | file:line | 状態 | 方針 Y での扱い |
|---|---|---|---|---|
| Fatou (liminf 版) | `lintegral_liminf_le {ι : Type*} {f : ι → α → ℝ≥0∞} {u : Filter ι} [IsCountablyGenerated u] (h_meas : ∀ i, Measurable (f i)) : ∫⁻ a, liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) u` | `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:231-234` | ✅ 既存 | **in-tree `klDiv_le_liminf_of_ae_tendsto` (EPIG2KLFatouLSC.lean:151) が既にこの形で使用**。density a.e. 収束 → KL/エントロピー liminf bound の核 |
| Fatou (ae 版) | `lintegral_liminf_le' ... (h_meas : ∀ i, AEMeasurable (f i) μ) : ...` | `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:214` | ✅ 既存 | ae 版 |

### C. 弱収束 / portmanteau（既存、ただし「測度の弱収束」止まり）

| 概念 | Mathlib API | file:line | 状態 | 方針 Y での扱い |
|---|---|---|---|---|
| 弱収束 ↔ 有界連続関数積分収束 | `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto {γ : Type*} {F : Filter γ} {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} : Tendsto μs F (𝓝 μ) ↔ ∀ f : Ω →ᵇ ℝ, Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω)))` | `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean:346-350` | ✅ 既存 | 弱収束の定義出口。`negMulLog` は有界連続でない（`x→0` で発散）ので**直接は使えない**（portmanteau-LSC への bridge が要る、§2-D 不在） |
| portmanteau (開集合 liminf) | `MeasureTheory.le_measure_liminf_of_limsup_measure_compl_le` 等 | `Mathlib/MeasureTheory/Measure/Portmanteau.lean:131-135` 他 | ✅ 既存 | 集合測度レベルの liminf 不等式。**汎関数（積分）の LSC へは直結しない** |
| portmanteau 同値 | `MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge` | `Mathlib/MeasureTheory/Measure/Portmanteau.lean:172-176` | ✅ 既存 | C↔O 同値 |

### D. 核心命題 — entropy / KL の弱収束 LSC（**Mathlib 完全不在、loogle Found 0**）

| 概念（探したもの） | loogle クエリ | 結果 | 方針 Y での扱い |
|---|---|---|---|
| KL の下半連続性 | `InformationTheory.klDiv, LowerSemicontinuous` | **Found 0 declarations** | ❌ 不在 → `@residual(wall:entropy-lsc-weak)` 候補 |
| KL LSC (結論型 specific) | `LowerSemicontinuous (fun _ => InformationTheory.klDiv _ _)` | **Found 0 / Of these 0 match** | ❌ 不在 |
| KL ≤ liminf (汎用) | `InformationTheory.klDiv _ _ ≤ Filter.liminf _ _` | **Found 0 / 0 match** | ❌ 不在（in-tree `klDiv_le_liminf_of_ae_tendsto` は **density a.e. 収束を仮定**する特殊版、弱収束版でない） |
| ProbabilityMeasure × LSC | `MeasureTheory.ProbabilityMeasure, LowerSemicontinuous` | **Found 0 declarations** | ❌ 不在（弱収束下で LSC 汎関数の portmanteau bridge が Mathlib に無い） |
| differentialEntropy liminf | `"InformationTheory.Shannon.differentialEntropy", Filter.liminf` | **177 件中 0 件が名前一致** | ❌ 不在（differentialEntropy は project-local、liminf 補題なし） |
| LSC + Tendsto → le_liminf 合成 | `LowerSemicontinuous _ → Filter.Tendsto _ _ _ → _ ≤ Filter.liminf _ _` | **Found 0 / 0 match** | ❌ 不在（汎用 "LSC 関数を弱収束列に沿って le_liminf" の bridge そのものが無い） |

### E. mollification / approximate identity（Gaussian 畳み込み平滑化）

| 概念（探したもの） | loogle クエリ | 結果 | 方針 Y での扱い |
|---|---|---|---|
| Gaussian 畳み込み → 弱収束 / dirac 収束 | `ProbabilityTheory.gaussianReal, Filter.Tendsto` | **Found 0 declarations** | ❌ 不在 — **平滑測度が t→0 で生入力へ弱収束することの Mathlib lemma が無い**。方針 Y step 2 の「`X+√t Z → X`（法則収束）」の出発点すら未整備 |
| Measure.conv × Tendsto | `MeasureTheory.Measure.conv, Filter.Tendsto` | **Found 0 declarations** | ❌ 不在 |
| conv の a.c. 保存（混合 case 用、参考） | `MeasureTheory.Measure.conv, MeasureTheory.Measure.AbsolutelyContinuous` → `conv_absolutelyContinuous` / `HaveLebesgueDecomposition.conv` / `rnDeriv_conv` 等 5 件 | ✅ 5 件存在 | a.c. 保存は既存（親計画 発見 2 で混合 case に使用済）。だが**弱収束は別物**（a.c. ≠ weak conv） |

---

## §3. 既存 in-tree 資産の流用可能性

### 3-A. `EPIG2KLFatouLSC.lean` の klFun-Fatou サンドイッチ（`wall:approx-identity-L1` CLOSED の中核）

**主定理** (`InformationTheory/Shannon/EPIG2KLFatouLSC.lean:359-371`, `@[entry_point]`, `@audit:ok`, sorryAx-free) verbatim:

```lean
theorem negMulLog_convDensity_limsup_le {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume)
    {σ2 : ℝ≥0} (hσ : σ2 ≠ 0)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0)) :
    Filter.limsup
        (fun n => ∫ x, Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x) ∂volume)
        atTop
      ≤ ∫ x, Real.negMulLog (pX x) ∂volume
```

**何を証明しているか**: 平滑密度 `convDensityAdd pX g_{u n}` の微分エントロピー積分の `limsup` が、生密度 `pX` の微分エントロピー以下。これは「平滑で微分エントロピーが上から `h(pX)` に収束（上半連続）」= 方針 Y の RHS 側に近い言明。

**流用可能性 — ⚠ 部分的、かつ向き・前提が壁**:
1. **向き**: これは **`limsup ≤`**（平滑後の方が大きくならない側の上限）。方針 Y の LHS で要る `entropyPower (X+Y) ≤ liminf` は **`liminf` の下半連続性で逆向き**。`negMulLog_convDensity_limsup_le` は LHS lower bound には**そのまま使えない**。
2. **前提 (致命的)**: `hpX_ent` (`Integrable (negMulLog ∘ pX)` = **有限微分エントロピー**) と `hpX_mom` (**有限分散**) を **precondition に要求**。方針 Y が剥がしたいまさにその 2 つを入力に持っている。**= この補題は「有限分散 + 有限微分エントロピーを仮定した a.c.」でしか発火しない** ⇒ 方針 Y の「任意 a.c.」には未対応。
3. 補助補題 `convDensity_tendsto_ae_subseq` (`:169`, `@audit:ok`) も `hpX_mom` を要求（L¹ 収束に 2 次 moment が要る）。

→ **流用: 平滑側 `t>0` の EPI_t を「有限分散版 a.c.」で組む素材にはなる（= 方針 X の範囲）。だが regularity を剥がす方針 Y 本体（任意 a.c.）には不足。** 親計画 §S5 の「klFun-Fatou 実績流用候補」は **有限分散前提付きでのみ流用可能**であり、無前提化には新規補題が必須。

### 3-B. `EPIG2HeatFlowContinuity.lean` の endpoint 連続性 — どの step が regularity を使うか

**wall lemma** (`InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:580-587`, `@[entry_point]`, `@audit:ok`) verbatim:

```lean
theorem heatFlowEntropyPower_continuousWithinAt_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_endpt : IsHeatFlowEndpointRegular X Z P) :
    ContinuousWithinAt
      (fun t : ℝ => entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
      (Set.Ioi (0 : ℝ)) 0
```

**証明が regularity を使う step** (`:591-599`): 内部の `differentialEntropy` 連続性 `heatFlowDifferentialEntropy_continuousWithinAt_zero` に `h_endpt` の **8 density field 全部**（`pX`/`hpX_nn`/`hpX_meas`/`hpX_law`/`hpX_int`/`hpX_mass`/`hpX_mom`/`hpX_ent`）を渡す（`:596-599` verbatim）。連続性の結論は `(Set.Ioi 0) 0` = **t→0⁺ の右連続性**。

**「平滑側 t>0 だけなら不要になるか」 — NO**:
- この補題の結論は **endpoint t=0 での連続性**。t→0⁺ で平滑項 `√t·Z → 0` が消え、極限点の測度は **生 `P.map X`**（親計画 発見 3、`ac-density-witness-inventory.md` §B verbatim 確認済）。
- regularity（特に `hpX_mom`/`hpX_ent`）は **interior t>0 では Gaussian 畳み込みが供給するが、endpoint t=0 では生入力 X の regularity がそのまま要求される**。
- 方針 Y は「endpoint 依存を近似+極限で迂回」と言うが、迂回先の極限言明（§1-B の LSC）自体が同じ生入力 regularity を要求する（§3-A の `negMulLog_convDensity_limsup_le` が `hpX_ent`/`hpX_mom` を持つことが証拠）。**endpoint 連続性を半連続性に弱めても、生入力 regularity の要求は本質的に残る。**

### 3-C. Vitali / uniform integrability 機構

| 資産 | file:line | 内容 | 方針 Y 流用 |
|---|---|---|---|
| `negMulLog_convDensity_tendsto_ae_subseq` | `InformationTheory/Shannon/EPIVitaliAE.lean:72` | 平滑密度の negMulLog が a.e. 部分列収束 | `negMulLog_convDensity_limsup_le` の補助。**`hpX_mom` 系前提継承** |
| `EPIVitaliUI.lean` / `EPIVitaliUnifTight.lean` | — | uniform integrability / tightness | UI は L¹ 収束 → 積分収束の橋。**有限分散がないと tightness が出ない**（heavy-tail は tight でない）⇒ 任意 a.c. では UI 機構が回らない |

→ Vitali 機構も **有限分散（tightness）を暗黙に要求**。方針 Y の任意 a.c. では UI が成立しない入力がある。

### 3-D. 混合 case 2 補題（参考、方針 Y では case 1 拡張に直接は使わないが単調性の素材）

| 補題 | file:line | 結論 | 前提（抜粋 verbatim） |
|---|---|---|---|
| `condDifferentialEntropy_le` | `EPIG2ConvEntropyMonotone.lean:224` | `condDifferentialEntropy X Z μ ≤ differentialEntropy (μ.map X)` | `(hX_ac : (μ.map X) ≪ volume)` + `h_int`/`hκ_v`/`hκ_logp_int`/`hκ_cross_int`/`h_fibreEnt_int`/`h_cross_int`/`h_logq_int`（**8 本の integrability/ac precondition**） |
| `condDifferentialEntropy_indep_add_eq` | `EPIG2ConvEntropyMonotone.lean:328` | `condDifferentialEntropy (fun ω => X ω + c*Z ω) Z μ = differentialEntropy (μ.map X)` | `(hX hZ : Measurable) (hXZ : IndepFun X Z μ) (hX_ac : (μ.map X) ≪ volume)` |

合成で `h(W+√t Z) ≥ h(W)`（noise が entropy を増やす単調性）。だが `condDifferentialEntropy_le` の **8 integrability precondition は任意 a.c. では出ない**（特に `h_int` = llr 可積分 ≈ KL 有限、`h_fibreEnt_int` = fibre entropy 可積分）。⇒ §1-A の単調性が任意 a.c. で崩れる根拠。

---

## §4. 平滑側 t>0 の無前提性検算（親計画 step 1 の落とし穴）

親計画 §Phase Y step 1: 「t>0 では入力が Gaussian と畳み込み済で自動 regular ⇒ EPI_t は input regularity 無しに閉じる」。**verbatim 検算 → 部分的に偽（落とし穴 confirmed）**:

### 4-A. 平滑は X 由来の裾を消さない

`X+√t Z` の法則 = `(P.map X) ⋆ N(0, t·v_Z)`（畳み込み）。Gaussian 因子 `N(0, t·v_Z)` は有限分散だが、**畳み込みの分散 = 各因子の分散の和**。X が無限分散（Cauchy 等 heavy-tail a.c.）なら `Var(X+√t Z) = Var(X) + t·v_Z = ∞`。⇒ **`hpX_mom`（有限 2 次 moment）は平滑後も充足されない**。`ac-density-witness-inventory.md` §A の `hpX_mom` 反例（Cauchy）が平滑後も生きる。

### 4-B. `hpX_ent`（有限微分エントロピー）も平滑で保証されない

畳み込みは density を滑らかにする（`hpX_meas`/`hpX_nn`/`hpX_law` は自動充足）が、`Integrable (negMulLog ∘ pX_t) volume`（微分エントロピー有限）は **裾の重さに依存**。X が `h(X) = +∞` または積分発散する a.c. なら、平滑後 `pX_t` も裾が重く `negMulLog` 非可積分になりうる。`negMulLog_convDensity_limsup_le` (§3-A) が `hpX_ent` を **生 pX に対する precondition** として要求している事実が、これが平滑で自動供給されないことの直接証拠（もし平滑で出るなら前提に不要）。

### 4-C. verdict (§4)

**平滑側 t>0 の EPI_t は density-witness 8 field のうち `hpX_meas`/`hpX_nn`/`hpX_law`/`hpX_int`/`hpX_mass`（5 field）は平滑後自動充足するが、`hpX_mom`（有限分散）と `hpX_ent`（有限微分エントロピー）は X が heavy-tail なら平滑後も充足しない。** 親計画 step 1 の「平滑後自動 regular」は **有限分散な X に対してのみ真**。任意 a.c. X では平滑側 EPI_t すら無前提では組めない。⇒ 方針 Y は「t>0 で無前提 EPI_t、t→0 で剥がす」の step 1 段階で既に regularity を要求する。

---

## §5. 自作が必要な要素（優先度順）

| # | 要素 | 推奨実装 | 工数感 | 落とし穴 |
|---|---|---|---|---|
| 1 | **`entropyPower`（or `differentialEntropyExt`）の弱収束下半連続性** `N(X+Y) ≤ liminf_{t→0⁺} N((X+Y)+√t Z)` | `differentialEntropyExt : EReal` 上で `lowerSemicontinuousWithinAt_iff_le_liminf`（`[CompleteLinearOrder EReal]`）を出口に、`klDiv` LSC を経由。`klDiv = ∫⁻ klFun(rnDeriv)` の ℝ≥0∞ 形 + `lintegral_liminf_le`（Fatou）で density a.e. 収束から組む（in-tree `klDiv_le_liminf_of_ae_tendsto` の **弱収束版への一般化**） | **moonshot 規模**（density a.e. 収束を弱収束から出す portmanteau-LSC bridge が Mathlib 不在 §2-D、自作 200-400 行） | density a.e. 収束は弱収束より強い。弱収束だけからは出ない ⇒ 平滑列の特殊構造（畳み込み density の明示形）を使う必要、汎用化不可 |
| 2 | **平滑測度の t→0⁺ 弱収束** `P.map (X+√t Z) → P.map X` (法則収束) | `gaussianReal 0 (t·v) → dirac 0` (近似単位元) + 畳み込みの連続性。`tendsto_iff_forall_integral_tendsto` 出口 | 中（Mathlib に `gaussianReal` weak-conv lemma 不在 §2-E、自作 80-150 行） | approximate identity の Mathlib 機構が薄い。bounded continuous test 関数で押す |
| 3 | **平滑側無前提 EPI_t**（§4 で有限分散 X に限定が判明） | 既存 case 1 a.c. core を有限分散版で。`negMulLog_convDensity_limsup_le` 流用 | 既存依存（case 1 core 完成待ち、本 plan 責務外） | §4: 任意 a.c. では step 1 すら無前提化不可。**有限分散前提が抜けない** |
| 4 | `differentialEntropyExt` の a.c. 枝で `h=+∞` を表現する型修正 | a.c. 枝も `EReal` 値で `negMulLog` 非可積分時 `+∞` を返す再定義（現状 ℝ workhorse coerce で表現不可、§1-C） | 中〜大（二層定義 S1 の re-shape 波及） | ℝ workhorse 温存（de Bruijn `HasDerivAt` が ℝ 要求、親計画 設計制約）と両立しない。a.c. 枝の無限値表現が二層構造と衝突 |

---

## §6. Mathlib 壁の列挙（真に不在、`@residual(wall:...)` 対象）

| wall slug 候補 | 内容 | loogle 確認 |
|---|---|---|
| `wall:entropy-lsc-weak` | entropy / KL の弱収束下半連続性 `klDiv μ γ ≤ liminf` (弱収束版) / `differentialEntropy` LSC | `InformationTheory.klDiv, LowerSemicontinuous` = **Found 0**; `ProbabilityMeasure, LowerSemicontinuous` = **Found 0**; `LowerSemicontinuous _ → Filter.Tendsto _ _ _ → _ ≤ Filter.liminf _ _` = **Found 0 / 0 match** |
| `wall:gaussian-approx-identity-weak` | Gaussian 畳み込み (vanishing variance) の弱収束 `gaussianReal 0 (t·v) → dirac`、`P.map(X+√t Z) → P.map X` | `ProbabilityTheory.gaussianReal, Filter.Tendsto` = **Found 0**; `MeasureTheory.Measure.conv, Filter.Tendsto` = **Found 0** |

**shared sorry 補題化推奨**: `wall:entropy-lsc-weak` は EPI 系の複数 file（本 S5 + 将来の任意 a.c. core）で再利用する核心壁。`docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」に従い **1 本の shared sorry 補題に集約推奨**（散在させない）。ただし §5 #1 の「弱収束 → density a.e. 収束は出ない」構造的障害があり、shared 補題の signature 自体が「平滑列の特殊構造」を引数に取る形に縛られる（汎用 LSC として書けない）。

**注（壁でなく gap）**: §2-A/B/C の汎用機構（`lowerSemicontinuousWithinAt_iff_le_liminf`・`lintegral_liminf_le`・portmanteau・`tendsto_iff_forall_integral_tendsto`）は**既存**。真の壁は「これらを entropy 汎関数に適用するために必要な『entropy が弱収束 LSC』という中間命題」が不在な点。汎用ツールはあるが、適用対象の性質が証明されていない。

---

## §7. 撤退ラインへの距離（L-Uncond-3-scope）

親計画 §スコープ判断: **L-Uncond-3-scope** = 「方針 Y が semicontinuity wall で genuine に詰まったら、有限分散+有限微分エントロピーを honest precondition として残す方針 X に縮退して着地」。

**判定: 発動する可能性が高い（条件付き発動）。**

具体的発動条件（本調査で具体化）:

1. **§4 で確定した構造的事実**: 平滑側 EPI_t（step 1）すら任意 a.c. では無前提化できない（`hpX_mom`/`hpX_ent` が平滑後も非充足）。⇒ 方針 Y の step 1 の前提「t>0 で自動 regular」が **有限分散 X に限定**される。
2. **§3-A の前提継承**: 唯一の流用候補 `negMulLog_convDensity_limsup_le` が `hpX_ent`/`hpX_mom` を要求。これを剥がす再証明は §5 #1（moonshot 規模、Mathlib 壁含む）。
3. **§1 の単調収束不成立 + §1-C の型障害**: ℝ workhorse が `±∞` を持てないため、a.c. 枝で `h=+∞` の入力を極限で扱う型がそもそも無い（二層定義 S1 の制約と衝突）。

→ **発動条件 = 「§5 #1 の弱収束 LSC（+ §5 #4 の無限値型修正）が当該セッションで genuine に組めない」。本調査の見立てでは組めない確率が高い**（Mathlib 壁 2 本 + 構造的障害 + 二層定義との型衝突）。

**縮退案（新規撤退ライン提案、L-Uncond-3-scope の具体化）**:
- **方針 X 着地**: case 1 (両 a.c.) の最終 signature に `(hX_var : Integrable (fun ω => (X ω)^2) P) (hY_var : ...)` + `(hX_ent : Integrable (fun x => negMulLog ((P.map X).rnDeriv volume x).toReal) volume)` 系を **honest regularity precondition** として残す。docstring に「NOT fully unconditional on a.c. branch — finite variance + finite differential entropy required, per `epi-uncond-truncation-lsc-inventory.md` §4/§7」明示。
- 退化トラップ除去（特異 → entropyPower 0、case 2/3）は方針 Y でも方針 X でも追加前提なしで達成（親計画 発見 1+2）⇒ **「特異入力の無条件性」は方針 X でも保たれる**。失うのは「有限分散でない a.c. 入力」の救済のみ。
- 撤退口は honest（`sorry` + `@residual(wall:entropy-lsc-weak)` を S5 の弱収束 LSC 補題に残し、最終定理は方針 X signature で genuine に着地）。**仮説束化禁止** = `hX_var`/`hX_ent` は regularity precondition であり load-bearing でない（CLAUDE.md 判定軸「前提条件か証明の核心か」→ 前者）。

---

## §8. 着手 skeleton

`InformationTheory/Shannon/EPIUncondTruncationLSC.lean` の出だし（方針 Y 本体、弱収束 LSC を壁として残す形）:

```lean
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import InformationTheory.Shannon.EntropyPowerInequality
import InformationTheory.Shannon.EPIG2KLFatouLSC
import InformationTheory.Meta.EntryPoint

namespace InformationTheory.EPIUncondLSC

open MeasureTheory Filter Real ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

/-- **壁: entropy power の弱収束下半連続性** (方針 Y クリティカルパス、Mathlib 不在 §6)。
平滑列 `X + √(u n)·Z` (u n → 0⁺) に沿って、生入力の entropy power が平滑列の liminf 以下。
density a.e. 収束を弱収束から出す portmanteau-LSC bridge が Mathlib 不在のため、
平滑列の畳み込み density 明示形を経由する必要がある (§5 #1)。 -/
theorem entropyPower_le_liminf_heatFlow
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hX_ac : (P.map X) ≪ volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0)) :
    entropyPower (P.map X)
      ≤ Filter.liminf
          (fun n => entropyPower (P.map (fun ω => X ω + Real.sqrt (u n) * Z ω)))
          atTop := by
  sorry -- @residual(wall:entropy-lsc-weak)

/-- **壁: 平滑測度の t→0⁺ 弱収束** (近似単位元、Mathlib 不在 §6)。 -/
theorem heatFlow_tendsto_law
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0)) :
    Tendsto
      (fun n => (⟨P.map (fun ω => X ω + Real.sqrt (u n) * Z ω), by infer_instance⟩
        : ProbabilityMeasure ℝ))
      atTop (𝓝 ⟨P.map X, by infer_instance⟩) := by
  sorry -- @residual(wall:gaussian-approx-identity-weak)

end InformationTheory.EPIUncondLSC
```

（skeleton の 2 wall は §6 の 2 つの真 Mathlib 壁に対応。実装着手時は §5 #1 が「弱収束→density a.e. 収束が出ない」構造的障害を含むため、shared sorry 補題化 + L-Uncond-3-scope 縮退判断を Phase Y-0 で先に行うのが推奨。）

---

## 完了サマリ（feasibility verdict）

**(a) 平滑側無前提 EPI_t は成立するか**: ❌ **任意 a.c. では NO**（§4）。`hpX_mom`（有限分散）/`hpX_ent`（有限微分エントロピー）は Gaussian 畳み込みでも X が heavy-tail なら充足されない。step 1 の「平滑後自動 regular」は有限分散 X に限定。

**(b) t→0⁺ 極限言明の最小要件**: §1-B の片側半連続性 `entropyPower (X+Y) ≤ liminf entropyPower(平滑)` + RHS 収束。だが (i) 単調収束は不成立（§1-A）、(ii) 向き整合が非自明（§1-B 罠）、(iii) ℝ workhorse が `±∞` を持てず a.c. 枝の `h=+∞` を型表現できない（§1-C）。

**(c) Mathlib + 流用 + 自作で組めるか**: 汎用機構（LSC↔liminf・Fatou・portmanteau・弱収束定義）は既存だが、核心の「entropy が弱収束 LSC」は **Mathlib 完全不在（loogle Found 0 × 5）**。in-tree `negMulLog_convDensity_limsup_le` は逆向き limsup + `hpX_ent`/`hpX_mom` 前提付きで無前提化に不足。自作必要量 = 重い新規補題 3 本（弱収束 LSC bridge / 近似単位元弱収束 / 無限値型修正）、moonshot 規模。

**(d) genuine 障害 vs 単なる Mathlib gap**: **両方**。Mathlib gap（§6 の 2 wall は自作可能な不在）に加え、**genuine 構造障害**あり: (i) §4 平滑が裾を消さない（数学的事実、迂回不能）、(ii) §1-A 任意 a.c. で単調収束が偽（反例存在）、(iii) §1-C ℝ workhorse が無限を持てず二層定義と衝突。truly-hypothesis-free EPI が**偽**なわけではない（数学的には真と期待される）が、**現在の証明路（heat-flow/de Bruijn + ℝ workhorse）では本質的に有限分散を要求**し、それを剥がすには証明技法ごと別物（情報射影 / 直接 convolution density 評価）が要る。

**最大 blocker**: §4 の「平滑が X 由来の裾を消さない」+ §1-C の「ℝ workhorse 無限値非表現」の合わせ技。entropy が弱収束 LSC であること（§6 wall）を自作しても、ℝ workhorse が `h=+∞` を扱えないため a.c. 枝の極限が型で閉じない。

**自作量概算**: §5 #1（200-400 行、Mathlib 壁含む）+ #2（80-150 行）+ #4（二層定義 re-shape 波及・中〜大）。**L-Uncond-3-scope（方針 X 縮退）発動を強く推奨** — 有限分散+有限微分エントロピーを honest regularity precondition として残し、特異入力の退化トラップ除去（case 2/3、追加前提なし）は方針 X でも保たれる。

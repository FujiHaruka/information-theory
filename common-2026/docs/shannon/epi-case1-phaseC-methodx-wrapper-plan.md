# EPI case 1 Phase C: 方針X wrapper `entropyPower_add_ge_case1_of_methodX` サブ計画

> **Parent**: [`epi-case1-ratio-limit-plan.md`](epi-case1-ratio-limit-plan.md)
>   (headline `entropyPower_add_ge_case1_of_regular` の供給可能 precondition を方針Xに還元)。
> grandparent: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §Phase A-close。
> **slug**: `epi-case1-phaseC-methodx-wrapper-plan`
>   (新規 `sorry` の `@residual(plan:epi-case1-phaseC-methodx-wrapper-plan)` slug と一致)。

<!-- 記法は subplan-template と同じ (状態絵文字 📋🚧✅🔄 / 取り消し線 / 判断ログ append-only)。 -->

## 進捗

- [ ] M0 在庫確認 (本 plan で完了済 — 供給補題 verbatim 確認済) ✅
- [ ] C-1 skeleton: `entropyPower_add_ge_case1_of_methodX` signature 確定 📋
- [ ] C-2 (A) 群 discharge: §3 regularity bundle 供給 (`isRescaledPathRegular_of_methodX`) 📋
- [ ] C-3 (A) 群 discharge: noise a.c. + 4-tuple→pair indep + scaling regularity 📋
- [ ] C-4 (A) 群 discharge: `h_scale_X/Y/sum` (entropy integrability of conv path) 📋
- [ ] C-5 (A) 群 discharge: `varX/Y/S` variance bound (`h_var_bound`) 📋
- [ ] C-6 de Bruijn 群 thread (B群、honest precondition、cross-link) 📋
- [ ] C-7 独立 honesty 監査 (新規 `sorry` 1 件想定) 📋
- [ ] C-8 (別 sub-phase) Phase C 結線: lift route-B 経由 dispatch case-1 / `stamToEPIBridge_holds` への配線 📋

## ゴール / Approach

### ゴール

`EPICase1RatioLimit.lean` に新 wrapper `entropyPower_add_ge_case1_of_methodX` を追加する。
clean な方針X precondition (input 側の a.c. + 有限分散 + 独立性、noise 側の Gaussian law +
独立性) を取り、`entropyPower_add_ge_case1_of_regular`
(`EPICase1RatioLimit.lean:1343`、`@audit:ok`、~30 precondition) の **供給可能 precondition
を全て discharge** し、**de Bruijn per-time regularity 群のみを honest precondition として
thread** する。これにより case-1 EPI を「方針X + de Bruijn per-time regularity」に還元し、
真の残壁を 1 箇所 (de Bruijn 群) に isolate する。

### Approach (解の全体形)

`entropyPower_add_ge_case1_of_regular` は 2 つの genuine pillar (`@audit:ok` 化済)
の合成であり、その precondition は **2 つの pillar の regularity 前提の union** である。
本 wrapper は precondition を **方針X = 低レベル input/noise データ** に置き換え、間に
discharge 補題を挟むことで `_of_regular` を呼ぶ。具体的には:

1. **noise 側**: `Z_X, Z_Y` の Gaussian law + 独立性は `_of_regular` がそのまま要求する。
   wrapper はこれらを clean precondition として受け取り、Gaussian a.c.
   (`hZX_ac`/`hZY_ac`/`hZXZY_ac`) を `gaussianReal_absolutelyContinuous` +
   `map_add_absolutelyContinuous` で **自前 derive** する。独立性は **4-tuple
   `iIndepFun ![X, Y, Z_X, Z_Y] P`** を 1 本 precondition に取り、`_of_regular` が要求する
   pairwise (`hXZX`/`hYZY`) + joint (`hXYZXY`) + `hZXZY_indep` を group-split で derive。

2. **§3 squeeze regularity bundle (`h_reg_X/Y/S : IsRescaledPathRegular`)**: 既存
   `isRescaledPathRegular_of_methodX` (`:561`、`@audit:ok`) を **3 回呼ぶ** ことで方針X
   premises (有限分散 `h_mom_*`、a.c. `h*_ac`、variance bound `h_var_bound`) から genuine
   供給する。sum path の instance は `X+Y` を input、`Z_X+Z_Y` を noise (Gaussian
   `gaussianReal 0 (v_X+v_Y)`、独立 Gaussian の和) として渡す。

3. **scaling regularity (`h_scale_X/Y/sum`)**: a.c. は §2 と同じ
   `map_add_absolutelyContinuous`、entropy integrability は B(i) で使った
   `convDensityAdd_negMulLog_integrable_pub` + `pPath_eq_convDensityAdd` の同型 plumbing
   で供給。

4. **variance bound (`h_var_bound`)**: `IndepFun.variance_add` (Mathlib) +
   分散スケーリングで `varX/Y/S` を genuine に出し、`isRescaledPathRegular_of_methodX` の
   `h_var_bound` 入力に渡す。

5. **de Bruijn per-time regularity 群** (`h_reg_sum/X'/Y' : IsDeBruijnRegularityHyp` ×3、
   `h_endpt_sum/X/Y : IsHeatFlowEndpointRegular` ×3、`h_pos_stam` bundle):
   **方針Xから供給不能** (general-density discharge が別 moonshot
   `epi-debruijn-pertime-closure` 依存)。これらは **honest precondition として
   そのまま thread** し、wrapper signature に残す。cross-link コメント
   `@residual(plan:epi-debruijn-pertime-closure)` を docstring に書く。

**honesty 設計の核**: Stam core (`h_pos_stam` 内の `IsStamInequalityHyp`) は
**`_of_regular` の precondition であって本 wrapper が新たに bundle するものではない**
(`wall:stam-step2-density` は CLOSED、producer 側 genuine)。wrapper の body は
discharge 補題の合成 + `_of_regular` 呼出のみで、EPI 結論を仮説に encode しない。
命名は `_of_methodX` (regularity preconditions are real、`_unconditional` 禁止)。

**新規 `sorry` の見込み**: 上記 (1)-(4) は全て既存 `@audit:ok` 資産への plumbing なので、
本 wrapper の body は **0 sorry で閉じる見込み** (type-check done かつ proof done、
ただし de Bruijn 群を thread しているため `_of_regular` 経由で transitive には de Bruijn
壁を消費しない — de Bruijn 群は wrapper 利用者が供給する未解決前提)。万一 plumbing が
詰まったら当該 `have` を `sorry` + `@residual(plan:epi-case1-phaseC-methodx-wrapper-plan)`
で抜く (撤退口)。

---

## §A — `entropyPower_add_ge_case1_of_regular` precondition の 2 分類

`EPICase1RatioLimit.lean:1343-1409` を verbatim Read。precondition を (A) 方針X供給可能 /
(B) de Bruijn regularity (cross-plan thread) に分類。

| # | precondition (verbatim 名) | 型 (要約) | 分類 | 供給/thread 方法 |
|---|---|---|---|---|
| 1 | `hX hY hZX hZY` | `Measurable _` ×4 | A | wrapper precondition そのまま |
| 2 | `hXZX : IndepFun X Z_X P` | pairwise indep | A | 4-tuple iIndepFun の group-split |
| 3 | `hYZY : IndepFun Y Z_Y P` | pairwise indep | A | 同上 |
| 4 | `hXYZXY : IndepFun (X+Y) (Z_X+Z_Y) P` | joint indep | A | 4-tuple → {X,Y}/{Z_X,Z_Y} group → `IndepFun.comp` で和 |
| 5 | `hZXZY_indep : IndepFun Z_X Z_Y P` | noise indep | A | 4-tuple group-split |
| 6 | `v_X v_Y hv_X hv_Y` | `ℝ≥0` + `≠0` | A | wrapper precondition そのまま |
| 7 | `hZX_law hZY_law` | `P.map Z_* = gaussianReal 0 v_*` | A | wrapper precondition そのまま |
| 8 | `hZX_ac hZY_ac` | `P.map Z_* ≪ volume` | A | `gaussianReal_absolutelyContinuous` で derive |
| 9 | `hZXZY_ac : P.map (Z_X+Z_Y) ≪ volume` | noise sum a.c. | A | `map_add_absolutelyContinuous` (noise indep) |
| 10 | `h_reg_sum h_reg_X' h_reg_Y'` | `IsDeBruijnRegularityHyp` ×3 | **B** | thread (cross-link) |
| 11 | `h_endpt_sum h_endpt_X h_endpt_Y` | `IsHeatFlowEndpointRegular` ×3 | **B** | thread (cross-link) |
| 12 | `h_pos_stam` | per-`t` Fisher>0 ∧ `IsStamInequalityHyp` ∧ `IsRegularDensityV2` ∧ mass=1 ∧ conv-pin ∧ `IsBlachmanConvReady` の連言 | **B** | thread (cross-link、de Bruijn density witness `(h_reg_*'.reg_at t ht).density_t` に依存するため B群と不可分) |
| 13 | `h_scale_X h_scale_Y h_scale_sum` | per-`t` (a.c. ∧ negMulLog rnDeriv integrable) | A | §C-4 discharge 補題 |
| 14 | `varX varY varS` + `h_var*_nn` | `ℝ` + `0 ≤ _` | A | `IndepFun.variance_add` + scaling から construct |
| 15 | `h_reg_X h_reg_Y h_reg_S` | `IsRescaledPathRegular` ×3 | A | `isRescaledPathRegular_of_methodX` ×3 |

**B群の不可分性 (重要)**: #12 `h_pos_stam` は `(h_reg_X'.reg_at t ht).density_t` を直接
参照する (`:1368` 等) ため、`h_reg_X'/Y'/sum` (#10) を thread しない限り型が立たない。
よって #10-#12 は **1 つの cross-plan precondition 束**として thread する (これは
load-bearing bundling **ではない** — `IsDeBruijnRegularityHyp` は density witness の
regularity 構造体であり、`h_pos_stam` の `IsStamInequalityHyp` は CLOSED wall の producer
側で genuine、いずれも EPI 結論を encode しない。`_of_regular` の `@audit:ok` 監査で
非load-bearing 確認済)。

---

## §B — (A) 群供給補題の在庫 (`file:line` + verbatim signature)

### B-1. §3 regularity bundle 供給 — `isRescaledPathRegular_of_methodX`

`InformationTheory/Shannon/EPICase1RatioLimit.lean:561` (`@audit:ok`):

```
theorem isRescaledPathRegular_of_methodX
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hA : Measurable A) (hB : Measurable B)
    (v_B : ℝ≥0) (hv_B : v_B ≠ 0) (hB_law : P.map B = gaussianReal 0 v_B)
    (hAB : IndepFun A B P)
    (hA_ac : (P.map A) ≪ volume)
    (varA : ℝ) (h_varA_nn : 0 ≤ varA)
    (h_mom_A : Integrable (fun ω => (A ω)^2) P)
    (h_var_bound : ∀ t : ℝ, 0 < t →
      (∫ x, (x - (∫ y, y ∂(P.map (fun ω => A ω / Real.sqrt t + B ω))))^2
            ∂(P.map (fun ω => A ω / Real.sqrt t + B ω)))
          ≤ varA / t + (v_B : ℝ)) :
    IsRescaledPathRegular A B P varA v_B
```

- **3 回呼ぶ** (A:=X, B:=Z_X / A:=Y, B:=Z_Y / A:=X+Y, B:=Z_X+Z_Y)。
- sum instance: `v_B := v_X + v_Y` (Gaussian 和の分散加法、`hv_B := hv_sum` 既に headline
  body `:1218` で構成済の `v_X + v_Y ≠ 0`)。`hB_law` = `P.map (Z_X+Z_Y) = gaussianReal 0
  (v_X+v_Y)` は独立 Gaussian 和の law (要供給補題 → B-5 確認)。
- 入力 `hA_ac`/`h_mom_A`/`h_var_bound` は方針X precondition から組む (下記 B-2/B-4)。

### B-2. 入力 a.c. — `map_div_sqrt_absolutelyContinuous` / `map_add_absolutelyContinuous`

`isRescaledPathRegular_of_methodX` の `hA_ac : P.map A ≪ volume` (input 側) は wrapper の
方針X precondition `hX_ac : P.map X ≪ volume` 等そのまま渡す (wrapper が input a.c. を
取る)。

noise / path a.c.:
- `InformationTheory/Shannon/EPIUncondMixedCase.lean:55` `map_add_absolutelyContinuous`
  (`A + B` の a.c.、independence + 片側 Gaussian a.c.)。`hZXZY_ac`/`h_scale_*` の a.c. 部に使用。
- `rescaledInput_density_witness` (`EPICase1RatioLimit.lean:439`、`private`) 内部で
  `map_div_sqrt_absolutelyContinuous A P hA hA_ac ht` (`:451`) を呼んでいる
  (= `P.map (A/√t) ≪ volume`)。a.c. 系は既存資産で揃う。
- `gaussianReal_absolutelyContinuous 0 hv_X : gaussianReal 0 v_X ≪ volume` →
  `hZX_law` rewrite で `hZX_ac` を derive (B(i) body `:576` で実演済の手筋)。

### B-3. density witness + path entropy integrability — B(i) 同型資産

`h_scale_X/Y/sum` の entropy integrability conjunct
(`Integrable (negMulLog (rnDeriv …))`) は B(i) headline body (`:1108-1148`) で**全く同型**に
discharge 済。再利用補題:
- `rescaledInput_density_witness` (`:439`、`private`) — `A/√t` の Real density witness
  `pX` (非負・可測・`withDensity` law・`Integrable`・mass=1・2次モーメント可積分) を供給。
- `InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd`
  (`FisherInfoV2DeBruijnPerTime.lean:215`) — path rnDeriv =ᵐ `ofReal (convDensityAdd pX g_v)`。
- `InformationTheory.Shannon.convDensityAdd_negMulLog_integrable_pub`
  (`EPIG2HeatFlowContinuity.lean:129`、`@audit:ok`):

```
theorem convDensityAdd_negMulLog_integrable_pub
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume
```

- `h_scale_X` の path は `X/√t + Z_X` (B(i) は `B + A/√t` = `Z_X + X/√t`、add_comm で同型)。
  density identification → `h_asset.congr` で rnDeriv に転送 (`:1142-1148` と同一手筋)。

### B-4. variance bound — `IndepFun.variance_add` + scaling

`isRescaledPathRegular_of_methodX` の `h_var_bound`:
`∀ t>0, ∫(x − mean)² d(law(A/√t + B)) ≤ varA/t + v_B`。

供給補題:
- `ProbabilityTheory.IndepFun.variance_add` (`Mathlib/Probability/Moments/Variance.lean:406`):

```
nonrec theorem IndepFun.variance_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) (h : X ⟂ᵢ[μ] Y) : Var[X + Y; μ] = Var[X; μ] + Var[Y; μ]
```
  (`⟂ᵢ[μ]` = `IndepFun … μ`、`Var[·;μ]` = `ProbabilityTheory.variance`)。

設計メモ (verbatim 確認の要点):
- path `A/√t + B` の law の variance = `Var[A/√t + B; P]` (variance は law-only)。
  `A/√t ⊥ B` (independence の comp、B(i) body `:585` で実演) かつ両 `MemLp 2` (B(i)
  `:1067-1089` で `hZt_sq`/`hB_sq` から `MemLp 2` 構成済) なので `IndepFun.variance_add`
  適用可。`Var[A/√t] = (1/t) Var[A]` (scaling、`Real.sq_sqrt`)、`Var[B] = v_B` (Gaussian
  N(0,v_B) の分散)。よって `Var[path] = Var[A]/t + v_B`。
- `varA := Var[A; P]` と置けば `h_var_bound` は **等号で**成立 (`≤` は自明)。
  `varX := Var[X;P]`, `varY := Var[Y;P]`, `varS := Var[X+Y;P]`。
  sum instance の input は `X+Y` なので `varS = Var[X+Y;P]`、これも
  `IndepFun.variance_add` (もし `X⊥Y` を仮定するなら `Var[X]+Var[Y]`、ただし wrapper は
  必ずしも `X⊥Y` を要求しない → `varS := Var[X+Y;P]` を直接置けばよく、和分解は不要)。
- ⚠ **`mean` の扱い**: `h_var_bound` の積分は `∫(x − ∫y)² d(law)` = まさに variance の
  定義形 (`ProbabilityTheory.variance` の `μ[id]` 引き)。Mathlib `variance` 定義形と
  本積分形の bridge (`variance_eq` / `Var[X;μ] = ∫(x−μ[X])²`) を verbatim 確認のうえ
  使う (C-5 実装時に `loogle ProbabilityTheory.variance` で出口形を Read)。

  > **数値予測の verbatim 確認義務**: `Var[B] = v_B` (Gaussian N(0,v_B)) は実コードで
  > 裏取りしてから C-5 で使う (`gaussianReal` の variance 補題を `loogle
  > ProbabilityTheory.variance (gaussianReal _ _)` で確認、`v_B` が `ℝ≥0` coercion で
  > 何になるか verbatim 照合)。直感に頼らない。

### B-5. 独立性 group-split — 4-tuple `iIndepFun`

wrapper precondition は **`iIndepFun ![X, Y, Z_X, Z_Y] P`** (4-tuple、`Fin 4` index)。
`_of_regular` が要求する各 indep を derive:

- pairwise `hXZX`/`hYZY`/`hZXZY_indep`: `iIndepFun` の 2-成分射影
  (`iIndepFun.indepFun` で index pair 抽出、`loogle ProbabilityTheory.iIndepFun.indepFun`
  で出口形確認)。
- joint `hXYZXY : IndepFun (X+Y) (Z_X+Z_Y) P`:
  `ProbabilityTheory.iIndepFun.indepFun_prodMk_prodMk`
  (`Mathlib/Probability/Independence/Basic.lean:862`):

```
lemma iIndepFun.indepFun_prodMk_prodMk (h_indep : iIndepFun f μ) (hf : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) μ
```
  → `i:=0,j:=1` ({X,Y}), `k:=2,l:=3` ({Z_X,Z_Y}) で `IndepFun (X,Y) (Z_X,Z_Y)`。
  次に `ProbabilityTheory.IndepFun.comp` (`Basic.lean`、verbatim):

```
theorem IndepFun.comp {…} {φ : β → γ} {ψ : β' → γ'}
    (hfg : f ⟂ᵢ[μ] g) (hφ : Measurable φ) (hψ : Measurable ψ) :
    (φ ∘ f) ⟂ᵢ[μ] ψ ∘ g
```
  → `φ := (·.1 + ·.2)`, `ψ := (·.1 + ·.2)` (pair の和) で
  `IndepFun (X+Y) (Z_X+Z_Y) P` を得る。

- noise sum law `hZXZY_law : P.map (Z_X+Z_Y) = gaussianReal 0 (v_X+v_Y)`: 独立 Gaussian の
  和の law。供給補題を `loogle` で確認 (`gaussianReal _ _ , ProbabilityTheory.IndepFun`、
  または既存 InformationTheory 内 `gaussian_add` 系)。**B-5 実装時に verbatim 確認必須**
  (無ければ `convolution` 経由 or 既存 EPI 資産から)。

---

## §C — wrapper signature 案

```lean
/-- **Case-1 EPI under method-X regularity** (entropic-CLT-free).
`N(P.map(X+Y)) ≥ N(P.map X) + N(P.map Y)` for a.c. inputs, reduced to
**method-X regularity + de Bruijn per-time regularity**. -/
theorem entropyPower_add_ge_case1_of_methodX
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    -- 方針X: input regularity
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω)^2) P)
    (h_mom_Y : Integrable (fun ω => (Y ω)^2) P)
    -- 方針X: noise Gaussian law + nonzero variance
    (v_X v_Y : ℝ≥0) (hv_X : v_X ≠ 0) (hv_Y : v_Y ≠ 0)
    (hZX_law : P.map Z_X = gaussianReal 0 v_X)
    (hZY_law : P.map Z_Y = gaussianReal 0 v_Y)
    -- 方針X: 4-tuple joint independence (input/noise すべて独立)
    (h_iIndep : iIndepFun ![X, Y, Z_X, Z_Y] P)
    -- de Bruijn per-time regularity (cross-plan thread, 供給不能)
    -- @residual(plan:epi-debruijn-pertime-closure)
    (h_reg_sum : EPIStamDischarge.IsDeBruijnRegularityHyp (fun ω => X ω + Y ω)
                    (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X' : EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y' : EPIStamDischarge.IsDeBruijnRegularityHyp Y Z_Y P)
    (h_endpt_sum : IsHeatFlowEndpointRegular (fun ω => X ω + Y ω)
                    (fun ω => Z_X ω + Z_Y ω) P)
    (h_endpt_X : IsHeatFlowEndpointRegular X Z_X P)
    (h_endpt_Y : IsHeatFlowEndpointRegular Y Z_Y P)
    (h_pos_stam : ∀ (t : ℝ) (ht : 0 < t), …(= `_of_regular` と同型、B群不可分)…) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  …
```

**設計判断**:
- input regularity は `hX_ac`/`h_mom_X` (+ Y) のみ取る。variance `varX/Y/S` は body で
  `Var[X;P]` 等として construct (precondition に出さない → caller 負担減 + honest)。
- 独立性は 4-tuple `iIndepFun ![X,Y,Z_X,Z_Y] P` 1 本に集約 (`_of_regular` の 4 個別 indep
  precondition を body で derive)。
- de Bruijn 群 (#10-#12) はそのまま thread (signature に残る、cross-link コメント付き)。
  これが本 wrapper の **honest 残壁の isolate 点**。
- `h_scale_*`/`hZ*_ac`/`hZXZY_ac`/`h_reg_X/Y/S`/`var*` は **全て body で discharge** →
  signature から消える (caller が供給する必要なし)。
- **有限エントロピー (`hpX_ent`) の要否**: B(i) では fibre=Gaussian で input entropy
  不要だった。ただし `IsHeatFlowEndpointRegular` の field `hpX_ent`
  (`EPIG2HeatFlowContinuity.lean:503`) として B群 (#11) 内に既に含まれており、wrapper は
  これを **新規 precondition として追加しない** (de Bruijn 群経由で供給済)。§4 squeeze 側
  (`IsRescaledPathRegular`) は fibre=Gaussian なので input entropy 不要 — C-4 実装時に
  `convDensityAdd_negMulLog_integrable_pub` が input entropy を要求しないことを再確認
  (上記 verbatim signature は `hpX_ent` を取らない → 不要が確定)。

**honesty 命名**: `_of_methodX`。`_unconditional`/`_full`/`_discharged` は禁止
(de Bruijn 群が開いた honest precondition として残るため)。

---

## §D — 実装ステップ (skeleton-driven)

撤退口: 各 step が詰まったら当該 `have` を `sorry` +
`@residual(plan:epi-case1-phaseC-methodx-wrapper-plan)` で抜く。de Bruijn 群 thread は
`@residual(plan:epi-debruijn-pertime-closure)` (cross-link コメント、wrapper body には
sorry を持たせない — thread するだけ)。

1. **C-1 skeleton**: §C signature を書き、body は `sorry`。`lake env lean` で型整合確認
   (`h_pos_stam` の B群不可分連言が `h_reg_*'` を参照できる順序であることを LSP で確認)。
2. **C-2 §3 bundle**: `h_reg_X/Y/S` を `isRescaledPathRegular_of_methodX` ×3 で
   `have`。入力 `h_var_bound` は C-5 の `have` を前方参照 (順序: C-5 → C-2)。
3. **C-3 noise a.c. + indep**: `hZX_ac`/`hZY_ac` (Gaussian a.c.)、`hZXZY_ac`
   (`map_add_absolutelyContinuous`)、4-tuple → pairwise/joint indep (B-5)、
   noise sum law (B-5 verbatim 確認後)。
4. **C-4 scaling regularity**: `h_scale_X/Y/sum` を B(i) 同型 plumbing
   (`rescaledInput_density_witness` + `pPath_eq_convDensityAdd` +
   `convDensityAdd_negMulLog_integrable_pub`) で `have`。
5. **C-5 variance bound**: `varX/Y/S := Var[·;P]`、`h_var_bound` を
   `IndepFun.variance_add` + scaling で `have`。**`variance` 出口形 + Gaussian variance
   = v_B を verbatim 確認してから**。
6. **C-6 de Bruijn thread**: `h_reg_*'`/`h_endpt_*`/`h_pos_stam` をそのまま
   `_of_regular` に渡す (body で thread のみ)。
7. **最終**: `exact entropyPower_add_ge_case1_of_regular X Y Z_X Z_Y P hX hY hZX hZY
   (derive した各 indep) v_X v_Y hv_X hv_Y hZX_law hZY_law hZX_ac hZY_ac hZXZY_ac
   h_reg_sum h_reg_X' h_reg_Y' h_endpt_sum h_endpt_X h_endpt_Y h_pos_stam
   h_scale_X h_scale_Y h_scale_sum varX varY varS h_varX_nn h_varY_nn h_varS_nn
   h_reg_X h_reg_Y h_reg_S`。
8. **C-7 独立 honesty 監査**: 新規 `sorry` が 0 件でも、signature の honesty
   (`_of_methodX` が de Bruijn 群を honest thread していること、4-tuple iIndepFun が
   load-bearing でないこと、結論が方針X+de Bruijn から follow すること) を fresh
   `honesty-auditor` で確認 (新 declaration + signature 変更に該当)。`sorry` が残った場合は
   `@residual` classification 検証も。

**proof done の見込み**: 本 wrapper body は 0 sorry で閉じる見込み (全 (A) 群が `@audit:ok`
資産への plumbing)。ただし wrapper は de Bruijn 群を **未解決 precondition として** 取るため、
「wrapper 自身は proof done だが、case-1 EPI を無条件に主張するものではない」。EPI moonshot
全体の proof done は `epi-debruijn-pertime-closure` の完成待ち。

---

## §E — Phase C 結線 (別 sub-phase、依存順)

本 wrapper `entropyPower_add_ge_case1_of_methodX` を Phase C dispatch に配線する。
結論型の gap (noise 導入 = bare `X,Y` に `Z_X,Z_Y` を導入) が問題。

### 結線先 1: dispatch skeleton case-1 枝

`EPIUncondMixedCase.lean:289` の case-1 (両 a.c.) 枝は現在
`-- @residual(plan:epi-stam-to-conclusion-plan)` の `sorry`。結論型は
`entropyPowerExt (P.map (X+Y)) ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)`
(注: `entropyPowerExt`、`EntropyPowerExt.lean:40`)。本 wrapper は `entropyPower`
(Ext なし) を返すので、**両 a.c. case では `entropyPower = entropyPowerExt` の bridge**
が要る (a.c. 下で `entropyPowerExt` は `entropyPower` に一致するはず → 要 verbatim 確認)。

### 結線先 2: `stamToEPIBridge_holds`

`EntropyPowerInequality.lean:251` の `stamToEPIBridge_holds X Y P : IsStamToEPIBridge X Y P`
は現在 `:= sorry` (shared wall、`@residual(plan:epi-stam-to-conclusion-plan)`)。これは
bare `X,Y` (noise なし) の `IsStamToEPIBridge`。

### 結線の核 — noise 導入の lift (route-B)

本 wrapper は `Z_X, Z_Y` (Gaussian noise) を **存在として要求** する。bare `X,Y` に
noise を同一確率空間上で導入する in-place 存在主張 (`IsStamScalingNoiseHyp`、
`EPIStamToBridge.lean:402`) は **atomic 空間で偽** (`@audit:defect(false-statement)`)。
honest 後継は **lift route-B**:
`EPINoiseExtension.stamScalingNoise_exists_on_lift` が lift 空間 `Ω × ℝ × ℝ`
(`liftMeasure P = P.prod ((gaussianReal 0 1).prod (gaussianReal 0 1))`) 上で coordinate
projection witness を genuine 構成 (0 sorry)。`entropyPower` の law-only 性 +
`IsStamInequalityResidual` の carrier-free defeq で lift から `(Ω,P)` へ EPI を transport
(`entropy_power_inequality_via_lift`)。詳細 → `epi-richness-route-b-plan`。

**依存順 (Phase C 結線)**:
1. (本 plan §A-D) wrapper `entropyPower_add_ge_case1_of_methodX` 完成 (de Bruijn 群 thread)。
2. lift 空間で wrapper を呼ぶ (coordinate projection が方針X precondition を満たす:
   2 番目/3 番目座標が standard normal で独立、1 番目座標が input)。lift 上で
   `iIndepFun ![X∘fst, Y∘fst, Z_X, Z_Y]` を product-measure API で供給。
   ⚠ ただし lift 上でも de Bruijn 群 (#10-#12) は依然 thread (供給不能) — Phase C 結線は
   de Bruijn 壁を消さない、richness を解くだけ。
3. `entropy_power_inequality_via_lift` で lift → `(Ω,P)` transport。
4. dispatch case-1 / `stamToEPIBridge_holds` に配線 (`entropyPowerExt = entropyPower`
   bridge を a.c. 下で挟む)。

この結線は **本 plan の主 scope (§A-D) とは別 sub-phase** (C-8)。§A-D 完成後に着手。
lift の具体構成は `epi-richness-route-b-plan` 側が SoT。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **B群の不可分性確定 (起草時)**: brief は de Bruijn regularity 群を 3 種 (`IsDeBruijnRegularityHyp` ×3 / `IsHeatFlowEndpointRegular` ×3 / `h_pos_stam`) と挙げたが、`_of_regular:1366-1388` を verbatim Read した結果、`h_pos_stam` が `(h_reg_X'.reg_at t ht).density_t` を直接参照するため `h_reg_*'` と型レベルで不可分と判明。3 種を 1 つの cross-plan precondition 束として thread する設計に確定 (§A #12 注)。
2. **line 番号修正 (起草時)**: brief は headline を `:1083-1149`、B(i) を `:576` と記したが、verbatim Read で `entropyPower_add_ge_case1_of_regular` は `:1343-1411`、`isRescaledPathRegular_of_methodX` は `:561`、`:1083-1149` は B(i) headline (`csiszarLogRatioGap_tendsto_zero_atTop`) の body 一部だった。本 plan は実 line 番号で記述。
3. **`hpX_ent` 不要確定 (起草時)**: §4 squeeze 側 (`convDensityAdd_negMulLog_integrable_pub:129`) の verbatim signature は input entropy `hpX_ent` を取らない (fibre=Gaussian で自動)。input entropy 有限性は B群 `IsHeatFlowEndpointRegular.hpX_ent` 経由でのみ要求され、wrapper は新規 precondition として追加しない。

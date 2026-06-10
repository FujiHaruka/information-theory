# Rate-distortion convexity + n-letter regulated-distortion form (E-4'' deferred)

> 実態整合 (2026-06-10): **genuine proof done** — `rateDistortionFunction_convexOn`
> (`InformationTheory/Draft/Shannon/RateDistortionConvexity.lean:390`) は
> **DPI selector-forget 経路で genuine に閉じた** (一般 Measure 形、有限アルファベット仮定なし)。
> `#print axioms` で `[propext, Classical.choice, Quot.sound]` (sorryAx 非依存)、独立監査 7 decl
> `@audit:ok` (commit `96fd6a2`)。経路 = 既存 `klDiv_map_le` (一般 pushforward DPI) 再利用 +
> gateway `klDiv_joint_convex` (`:283`、RD 構造から切り離した純 KL joint convexity) +
> 自作 disjoint-slice 加法性 `klDiv_add_of_mutuallySingular` (`:181`)。3 層
> `klDiv_joint_convex` → `klDiv_mixture_le` (`:338`) → 主補題 (`:390`)。
> **旧 subnormal `h_klDiv_conv` hyp 化 / pmf log-sum discharge 経路ではない** (それらは撤回済、判断ログ参照)。
> Phase C (n-letter form) は本 file scope 外。n-letter converse の Stage 1/2 は
> `RateDistortionConverseNLetter.lean` に landing 済 (`rate-distortion-converse-plan.md` 側)。

E-4'' シードカード ([`docs/moonshot-seeds.md`](../moonshot-seeds.md))、E-4 / E-4' の後継。
親シード: `InformationTheory/Shannon/RateDistortionConverseMonotone.lean` (151 行、E-4' 完了)。

Cover-Thomas 10.4 の **n-letter 規定歪み形** converse:
```
任意の長さ n block lossy code (encoder : α^n → M, decoder : M → β^n) と
i.i.d. 源 X^n ∼ P_X^n、規定歪み閾値 D に対して、ブロック歪み平均 D̃_n ≤ D ⟹
(rateDistortionFunction d P_X D).toReal ≤ (1/n) · log|M|.
```

到達手段は R(D) の **convexity** (`R(λD₁+(1-λ)D₂) ≤ λ R(D₁) + (1-λ) R(D₂)`) +
**MI chain rule + i.i.d.** (`I(X^n; X̂^n) = ∑ I(X_i; X̂_i)`) + per-letter 平均化 (Jensen) の合成。

## 進捗

- [x] Phase 0 — Mathlib API inventory + 設計判断
- [x] Phase A — 入力分布の混合 (`λ • ν₁ + (1-λ) • ν₂` 形 measure / feasibility 保存)
- [x] Phase B — R(D) convexity 主補題 ✅ **genuine closure (DPI 経路、一般 Measure 形)** (commit `96fd6a2`)
- [x] ~~Phase B specialization — finite-alphabet pmf 形での log-sum discharge~~ — **不要化** (DPI 経路で
      Measure 形のまま閉じたため pmf 特殊化を経由せず。退役、判断ログ参照)
- [ ] Phase C — (任意) n-letter 規定歪み形 converse 主定理 (deferred、`rate-distortion-converse-plan.md` 側で attack)

## ゴール / Approach

### 最終的に証明したい定理 (本 plan scope)

**Phase B 主補題** (本 plan 最小成果物):
```lean
theorem rateDistortionFunction_convexOn
    (d : α → β → ℝ) (P : Measure α) [IsProbabilityMeasure P] :
    ∀ D₁ D₂ : ℝ, ∀ {λ : ℝ}, 0 ≤ λ → λ ≤ 1 →
      rateDistortionFunction d P (λ * D₁ + (1 - λ) * D₂)
        ≤ ENNReal.ofReal λ * rateDistortionFunction d P D₁
          + ENNReal.ofReal (1 - λ) * rateDistortionFunction d P D₂
```

**Phase C 主定理** (任意。n-letter form 着地):
```lean
theorem rate_distortion_converse_n_letter_specified
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {M n : ℕ} (hn : 0 < n) (hM : 0 < M)
    (P_X : Measure α) [IsProbabilityMeasure P_X]
    (c : LossyCode M n α β) (d : DistortionFn α β)
    {D : ℝ} (hD : c.expectedBlockDistortion P_X d ≤ D)
    (hMI_finite : ...) :
    (rateDistortionFunction (fun a b => ((d a b : NNReal) : ℝ)) P_X D).toReal
      ≤ (1 / (n : ℝ)) * Real.log (M : ℝ)
```

### 全体戦略 (Approach) — Mathlib-shape-driven

**設計判断 1: convexity 主補題は `iInf_add` ベースで証明する**

`klDiv` の joint convexity (= log-sum inequality on measures) は Mathlib 不在で
~500 行規模の gap。**避ける**。代わりに R(D) は `iInf` で定義済みなので、
`λD₁ + (1-λ)D₂` 形の閾値での **feasibility 保存** + `iInf_le_of_le` + `add_le_add`
の合成で convexity 不等式を一辺ずつ直接示す。

**戦略の核**:
任意の feasible joint `ν₁` at `D₁`, feasible `ν₂` at `D₂` に対し、
`ν := λ • ν₁ + (1-λ) • ν₂` (measure scalar smul + add) は:
- marginal: `ν.map fst = λ • P + (1-λ) • P = P` (確率測度なら) — **問題**: 一般には
  `λ + (1-λ) = 1` でないと marginal が `P` に戻らない。`λ ∈ [0, 1]` 必須、
  かつ `Measure.smul_add` 系の `withDensity` plumbing.
- distortion: `expectedDistortion d ν = λ · ∫ d ∂ν₁ + (1-λ) · ∫ d ∂ν₂ ≤ λ D₁ + (1-λ) D₂`
  (積分の線形性)
- klDiv: **ここが gap**。`klDiv (λ ν₁ + (1-λ) ν₂) (marginals)` の上界が
  `λ klDiv ν₁ (marg₁) + (1-λ) klDiv ν₂ (marg₂)` (joint convexity)。

**ピボット: convexity を `iInf` 階層で press する**

joint convexity を直接示す代わりに、**R(D) 自体の凸性**を `iInf_add_iInf` 型で press
する道がある。だが measure-level の `+` は marginal も `+` で変わるため、`ν` の
marginal が `P` であるという拘束が壊れる。**ここで詰む**。

**Retreat: pmf 形 (有限 α, β) に絞る**

`Fintype α, β` + `MeasurableSingletonClass` 下では `Measure (α × β)` は `pmf` と同型
(`Finset.sum` 形)。pmf 上で convex combination を取れば marginal も `Finset.sum` で
明示計算でき、`klDiv` も `Finset.sum` 形で `klFun` の凸性 (`convexOn_klFun` Mathlib済)
を直接 per-atom 適用できる。**~300-500 行** 規模で着地。**本 plan は pmf 形 scope**。

**設計判断 2: pmf 形 vs Measure 形 の bridge**

E-3' (rate-distortion achievability deferred、`RateDistortionAchievability.lean`) も
pmf 形を計画している。本 plan は **既存 Measure 形 R(D) を保ったまま** pmf 形に
落とす per-atom 凸性 → Measure 形 凸性 への bridge lemma を 1 本書く方針。

**証明 chain (Phase B 主補題)**:

```
Step 1 (pmf-side): R_pmf(D) := ⨅ ν ∈ pmf-feasible(P, D), I_pmf(ν)
Step 2 (per-atom convex): klFun の凸性 (convexOn_klFun) + Finset.sum_le_sum で
        I_pmf(λν₁ + (1-λ)ν₂) ≤ λ I_pmf(ν₁) + (1-λ) I_pmf(ν₂)
Step 3 (feasibility): pmf 上で `λν₁ + (1-λ)ν₂` は marginal P 保存 + distortion 線形
Step 4 (iInf 不等式): 任意 feasible (ν₁, ν₂) 取って convex combo は (λD₁+(1-λ)D₂)-feasible
        ⇒ R_pmf(λD₁+(1-λ)D₂) ≤ λ I(ν₁) + (1-λ) I(ν₂)、両辺で iInf 取る
Step 5 (bridge): R_pmf(D) = rateDistortionFunction d P D (有限 α, β 下で rfl-に近い等価)
```

### 規模見積

- Phase 0 (Mathlib inventory): ~30 行 plan 内記載のみ
- Phase A (mixture measure / pmf 構成 + feasibility): ~200-300 行
- Phase B (convexity 主補題): ~300-400 行 (うち per-atom klFun 凸性 + Finset.sum_le_sum で
  ~150 行、pmf-Measure bridge で ~100 行、iInf plumbing で ~100 行)
- Phase C (任意 n-letter form): ~300-500 行 (chain rule `mutualInfo_pi_eq_sum` 既存利用 +
  Jensen via convexity + 1/n 平均)

**合計 ~800-1200 行** (Phase A+B+C)。Phase A+B のみで **~500-700 行**。

## Phase 0 — Mathlib API inventory + 設計判断

### 採用 API (DPI 経路、実装で使った資産)

| API | 出所 | 用途 |
|---|---|---|
| `klDiv_map_le` | InformationTheory 既存 (一般 pushforward DPI) | gateway `klDiv_joint_convex` の核 (selector-forget 再配線) |
| `Measure.map_add` / `Measure.map_smul` | Mathlib `MeasureTheory.Measure.MeasureSpace` | mixture pushforward (marginal 線形) |
| `integral_add_measure` / `integral_smul_measure` | Mathlib `MeasureTheory.Integral` | distortion 線形性 |
| `ENNReal.mul_iInf_of_ne` / `ENNReal.iInf_add` / `ENNReal.add_iInf` | Mathlib | iInf 系不等式 plumbing (主補題 press) |
| `ENNReal.ofReal_add` / `ENNReal.ofReal_mul` | Mathlib | ofReal 算術 |

### 退役 API (旧 pmf log-sum 経路想定、DPI 経路では未使用)

`convexOn_klFun` / `strictConvexOn_klFun` (Mathlib `Mathlib.InformationTheory.KullbackLeibler.KLFun`) +
`Finset.sum_le_sum` + `ConvexOn.smul_le_sum` + `klDiv_eq_lintegral_klFun_of_ac` は **per-atom pmf 形**
discharge 想定の在庫。DPI 経路で Measure 形のまま閉じたため未使用 (Phase B specialization 退役)。
Phase C (n-letter) で `mutualInfo_pi_eq_sum` (`InformationTheory.Shannon.MIChainRule`) を使う想定は維持。

### Mathlib gap (実装後の確定状態)

- **`klDiv` の joint convexity を直接探す**のは Mathlib 不在 (loogle Found 0、確認済) ——
  だが **直接探さず** 既存 DPI 資産 `klDiv_map_le` (一般 pushforward DPI) を selector-forget
  で再配線して genuine に閉じた (判断ログ参照)。pmf 特殊化も log-sum も不要。
- **`klDiv_add_le_add_klDiv`** (一般 measure add-form) も不在だが、互いに特異な成分に限定した
  自作 `klDiv_add_of_mutuallySingular` (rnDeriv 分解) で selector の per-slice 加法性を press。

### 設計判断 (実装後に確定)

1. **一般 Measure 形 scope** (起草時の pmf 形 retreat を **更新**): 起草時は joint convexity
   を有限アルファベット pmf 形に落とす予定だったが、DPI selector-forget 経路が
   **Measure 形のまま** (`[Fintype α] [Fintype β]` 不要) で閉じたため、有限アルファベット
   仮定を落とした一般形で publish。
2. **iInf-level value 形**: convexity は `ℝ≥0∞` 値の iInf-level で publish
   (`ENNReal.ofReal λ` 係数形)。`.toReal` 化は consumer 側 (n-letter converse) で行う。
3. **n-letter form (Phase C) deferred**: Phase B 主補題が core scope で genuine 達成済。
   Phase C (n-letter chain rule + Jensen) は `rate-distortion-converse-plan.md` 側で attack。

## Phase A — 入力分布の混合 (mixture measure 構成)

### A.1 `mixtureMeasure` (pmf 形)

```lean
/-- Convex combination of two joint measures on `α × β`. -/
noncomputable def mixtureMeasure
    (λ : ℝ) (hλ₀ : 0 ≤ λ) (hλ₁ : λ ≤ 1)
    (ν₁ ν₂ : Measure (α × β)) : Measure (α × β) :=
  ENNReal.ofReal λ • ν₁ + ENNReal.ofReal (1 - λ) • ν₂
```

### A.2 marginal of mixture = mixture of marginals

```lean
theorem mixtureMeasure_map_fst
    (λ : ℝ) (hλ₀ : 0 ≤ λ) (hλ₁ : λ ≤ 1)
    (ν₁ ν₂ : Measure (α × β)) :
    (mixtureMeasure λ hλ₀ hλ₁ ν₁ ν₂).map Prod.fst
      = ENNReal.ofReal λ • ν₁.map Prod.fst
        + ENNReal.ofReal (1 - λ) • ν₂.map Prod.fst
```

`Measure.map_add` + `Measure.map_smul` で 1-line。

### A.3 marginal保存

`P` 上での結合: `ν₁.map fst = P, ν₂.map fst = P ⟹ mixture.map fst = P` (確率測度則
`ofReal λ + ofReal (1-λ) = 1` の plumbing)。

### A.4 distortion 線形

`expectedDistortion d (mixture λ ν₁ ν₂) = λ · expectedDistortion d ν₁ + (1-λ) · expectedDistortion d ν₂`
(`integral_add` + `integral_smul_measure` 合成)。

### A.5 feasibility 保存

`ν_i feasible at D_i ⟹ mixture feasible at λD₁ + (1-λ)D₂`。

## Phase B — R(D) convexity 主補題 ✅ (genuine、DPI 経路)

実装は **B.1' (DPI 経路)** で確定。B.1 (旧 pmf log-sum 想定) は退役。

### B.1' joint klDiv convexity = DPI selector-forget (gateway `klDiv_joint_convex`)

joint convexity を pmf に落として per-atom で出すのではなく、**既存 DPI を再配線**:
selector `Bool × Ω` を介して `λ ν₁ + (1-λ) ν₂` を 2 成分の pushforward と見て
`klDiv_map_le` (一般 pushforward DPI) を適用、二点 selector の per-slice 加法性は
`klDiv_add_of_mutuallySingular` (互いに特異な成分の rnDeriv 分解) で自作。

### B.2 R(D) convexity 主補題 (実コード signature、一般 Measure 形)

```lean
theorem rateDistortionFunction_convexOn
    (d : α → β → ℝ) (P : Measure α) [IsProbabilityMeasure P] :
    ∀ {λ : ℝ} (hλ₀ : 0 ≤ λ) (hλ₁ : λ ≤ 1) (D₁ D₂ : ℝ),
      rateDistortionFunction d P (λ * D₁ + (1 - λ) * D₂)
        ≤ ENNReal.ofReal λ * rateDistortionFunction d P D₁
          + ENNReal.ofReal (1 - λ) * rateDistortionFunction d P D₂
```
（有限アルファベット仮定なし。`InformationTheory/Draft/Shannon/RateDistortionConvexity.lean:390`。）

### B.3 antitone vs convex compatibility

E-4' `rateDistortionFunction_antitone` と convex は両立 (decreasing convex)。

## Phase C — n-letter 規定歪み形 converse (任意)

### C.1 ブロック歪み → per-letter 歪みの平均

i.i.d. 源 `X^n ∼ P_X^n` 下で:
```
c.expectedBlockDistortion P_X d
  = ∫ x, (1/n) ∑ i, d(x_i, decoder_i(x)) ∂P_X^n
  = (1/n) ∑ i, ∫ x, d(x_i, decoder_i(x)) ∂P_X^n
  = (1/n) ∑ i, D̃_i  (per-letter expected distortion)
```

### C.2 per-letter single-shot lift

各 `i` で marginal `P_X` 上 + `X̂_i := decoder_i ∘ encoder` で
`rate_distortion_converse_single_shot_specified` (E-4') を適用。

### C.3 chain rule + Jensen

```
log|M| ≥ H(W) ≥ I(X^n; X̂^n) = ∑ I(X_i; X̂_i)
                              ≥ ∑ R(D̃_i)
                              ≥ n · R((1/n) ∑ D̃_i)   (Jensen via Phase B convexity)
                              ≥ n · R(D)              (antitone E-4')
```

### C.4 主定理

`rate_distortion_converse_n_letter_specified` (signature 上記)。

## Risks / unknowns

1. **pmf-Measure bridge の overhead**: 有限アルファベットでの `klDiv = Finset.sum`
   形は in principle rfl だが、`klDiv_eq_lintegral_klFun_of_ac` の `≪` 前提 plumbing
   が ~50-100 行見込み。既存 `CsiszarProjection` の `klDivPmf` パターンを流用。
2. **`smul` of measure + `ENNReal.ofReal` の plumbing**: `(ENNReal.ofReal λ) • ν` と
   `λ • ν` (NNReal) の混在で `simp` が暴れる可能性。**起草時に統一規約**を決める。
3. **`klDiv` 値 `∞` ケース**: convex combination で片方 `∞` のとき `ofReal λ * ∞` の
   挙動、`iInf_add` 前提 (`a ≠ ∞`) の充足。要確認。
4. **i.i.d. 仮定の plumbing (Phase C)**: `μ.map (X^n) = Measure.pi (fun _ => P_X)` の
   仮説持ち上げか、source を直接 `Measure.pi` で構成するか。
5. **Phase C antitone**: `(1/n) ∑ D̃_i ≤ D` の保証 + `R` 引数 ENNReal/Real plumbing。

## Mathlib inventory 必要箇所

- `convexOn_klFun` (Mathlib KLFun.lean): per-atom 凸性 ✓
- `Measure.map_add`, `Measure.map_smul`: marginal 線形性 ✓
- `integral_smul_measure`, `integral_add_measure`: distortion 線形性 ✓
- `ENNReal.iInf_add`, `ENNReal.add_iInf`: iInf-level 加算交換 ✓
- `ENNReal.ofReal_add` + `ENNReal.ofReal_mul`: ofReal 算術 ✓
- `Finset.sum_le_sum`: per-atom 集約 ✓
- `mutualInfo_pi_eq_sum` (InformationTheory 既存): Phase C chain rule ✓
- `convexOn_klFun.2`: `f(λa + (1-λ)b) ≤ λ f(a) + (1-λ) f(b)` 形 ✓

## 既存 plan / カード相互参照

- 親: [`rate-distortion-converse-plan.md`](rate-distortion-converse-plan.md) (E-4 single-shot ✅)
- 隣接: `RateDistortionConverseMonotone.lean` (E-4' antitone + specified ✅)
- 流用予定: `MIChainRule.mutualInfo_pi_eq_sum` (Phase C)
- 類似 pmf 凸性: `CsiszarProjection.klDivPmf_strictConvexOn_left` (per-atom 凸性パターン)
- 関連 deferred: `E-3'` (achievability、pmf 形 `RDConstraint` 計画あり)

## 規模見積 (再掲)

- Phase A+B のみ: ~500-700 行 / 0 sorry
- Phase A+B+C: ~800-1200 行 / 0 sorry

E-3' (~1800 行) と E-4' (~151 行) の中間 scale、`CsiszarProjection.lean` (~700 行) と同等。

## 判断ログ — 実装後 (`RateDistortionConvexity.lean`)

### 採用経路 — DPI selector-forget (genuine、一般 Measure 形)

- **Phase A + B core genuine 完成**, **Phase C deferred**, **Phase B specialization 不要化**。
  `InformationTheory/Draft/Shannon/RateDistortionConvexity.lean`、`#print axioms` sorryAx 非依存、
  独立監査 7 decl `@audit:ok` (commit `96fd6a2`)。
- **Phase A** (`mixtureMeasure` + marginal / distortion / feasibility 保存): 5 補題、
  `Measure.map_add` / `Measure.map_smul` / `integral_add_measure` / `integral_smul_measure`
  + `ENNReal.ofReal_add` の plumbing で straight。
- **Phase B 主補題** (`rateDistortionFunction_convexOn`, `:390`): **joint convexity を hypothesis
  化せず genuine に閉じた**。3 層構成:
  1. gateway `klDiv_joint_convex` (`:283`) — RD 固有構造から切り離した **純 KL joint convexity**。
     証明 = selector-extension (`Bool × Ω`) を介して既存資産 `klDiv_map_le`
     (一般 pushforward DPI = Cover-Thomas 2.7.2 data-processing) を再利用し、二点 selector の
     per-slice KL 加法性を自作 `klDiv_add_of_mutuallySingular` (`:181`、互いに特異な成分の
     rnDeriv 分解) で press。
  2. `klDiv_mixture_le` (`:338`) — gateway の plumbing 適用で mixture KL の凸上界。
  3. 主補題 (`:390`) — 層2 を iInf で press。

### 退役 Phase

- **Phase B specialization (pmf log-sum discharge)** — **不要化して退役**。当初は
  joint convexity を有限アルファベット pmf 形に落として per-atom `convexOn_klFun` +
  `Finset.sum_le_sum` で discharge する予定だったが、DPI selector-forget 経路が
  **Measure 形のまま** (有限アルファベット仮定なし) で gateway を閉じたため、pmf 特殊化を
  一切経由せず。`klDiv` の measure 形 log-sum gap (~150-200 行) も迂回。

### 採らなかった旧経路 (1 行)

- 旧 subnormal `h_klDiv_conv` hyp 化 + pmf discharge file (`RateDistortionConvexityDischarge.lean`、
  実在せず orphan 想定だった) は **撤回**。DPI 経路 (既存 `klDiv_map_le` 配線) のほうが
  hypothesis bundling を避けつつ Measure 形で genuine に閉じるため不採用 (履歴は git)。

### 教訓

- 「Mathlib `klDiv` joint convexity 不在 (loogle Found 0)」は事実だが、**結論 (joint
  convexity) を直接探すのではなく、既存 DPI 資産 `klDiv_map_le` を selector-forget で再配線**
  すれば pmf 特殊化なしに Measure 形で閉じる。「壁 → 既存資産で配線」前科 (Ch.8/9/17) に追加。

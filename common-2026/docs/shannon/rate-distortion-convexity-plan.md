# Rate-distortion convexity + n-letter regulated-distortion form (E-4'' deferred)

E-4'' シードカード ([`docs/moonshot-seeds.md`](../moonshot-seeds.md))、E-4 / E-4' の後継。
親シード: `Common2026/Shannon/RateDistortionConverseMonotone.lean` (151 行、E-4' 完了)。

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
- [x] Phase B core — R(D) convexity 主補題 (klDiv joint convexity を hypothesis 化した subnormal 形)
- [ ] Phase B specialization — finite-alphabet pmf 形での log-sum 経由 discharge (deferred)
- [ ] Phase C — (任意) n-letter 規定歪み形 converse 主定理 (deferred)

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

### Mathlib 必要 API (in-scope)

| API | 場所 | 用途 |
|---|---|---|
| `convexOn_klFun` | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:66` | per-atom 凸性 (Step 2 核心) |
| `strictConvexOn_klFun` | 同上 line 62 | 必要なら厳密版 |
| `Measure.map_add` | `MeasureTheory/Measure/MeasureSpace` | mixture pushforward (marginal 線形) |
| `Measure.map_smul` | 同上 | scalar mixture pushforward |
| `integral_add` / `integral_smul_measure` | `MeasureTheory/Integral/...` | distortion 線形性 |
| `ENNReal.iInf_add` / `ENNReal.add_iInf` | `Data/ENNReal/Operations.lean:550` | iInf 系不等式 plumbing |
| `Finset.sum_le_sum` + `mul_add` | basic | per-atom 凸性集約 |
| `ConvexOn.smul_le_sum` (の片側) | `Analysis/Convex/Jensen.lean` | Jensen 不等式 finite 形 |
| `klDiv_eq_lintegral_klFun_of_ac` | `KullbackLeibler/Basic.lean` | KL ↔ klFun-積分 bridge |
| `mutualInfo` def | `Common2026/Shannon/MutualInfo.lean:36` | 既存 R(D) との接続 |
| `mutualInfo_pi_eq_sum` | `Common2026/Shannon/MIChainRule.lean:341` | Phase C n-letter 鎖 |

### Mathlib gap

- **`klDiv` の joint convexity**: Mathlib 不在 (確認済)。**避ける**設計判断 (上記 retreat)。
- **`klDiv_add_le_add_klDiv`**: 一般 measure に対する add-form: 不在。pmf 経由で press。

### 設計判断 (起草時)

1. **pmf 形 scope**: `klDiv` joint convexity を Measure 形で press するのは ~500 行
   gap。`Fintype α, β` + `MeasurableSingletonClass` で pmf 形に落とし、per-atom
   `convexOn_klFun` + `Finset.sum_le_sum` で press。本 plan は **有限アルファベット仮定**。
2. **iInf-level vs value-level**: convexity を `iInf` の値レベルで主張すると
   `ENNReal.ofReal λ` の plumbing が pain。**ENNReal.toReal で `.toReal` 形で publish**
   + finiteness 仮定で逃げる選択肢もある。要再検討。
3. **n-letter form (Phase C) を deferred とするか**: 設定次第で ~500 行追加。
   Phase B 主補題が core scope。Phase C は MIChainRule 既存利用で hopefully 短いが、
   1/n 平均の Jensen で更に 1 段詰める。**起草時 commitment は Phase B until 0 sorry**、
   Phase C は Phase B 完成後の判断。

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

## Phase B — R(D) convexity 主補題

### B.1 per-atom klFun convexity → pmf-form joint klDiv convexity

`Fintype α, β` + `MeasurableSingletonClass` 下で `klDiv` を `Finset.sum` 形に reduce。
mixture `ν = λ ν₁ + (1-λ) ν₂` で per-atom:
```
ν {p} = λ (ν₁ {p}) + (1-λ) (ν₂ {p})
```
ratio + `convexOn_klFun.2` で per-atom 不等式、`Finset.sum_le_sum` で集約。

### B.2 R(D) convexity 主補題

```lean
theorem rateDistortionFunction_convexOn
    (d : α → β → ℝ) (P : Measure α) [IsProbabilityMeasure P]
    [Fintype α] [Fintype β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    ∀ {λ : ℝ} (hλ₀ : 0 ≤ λ) (hλ₁ : λ ≤ 1) (D₁ D₂ : ℝ),
      rateDistortionFunction d P (λ * D₁ + (1 - λ) * D₂)
        ≤ ENNReal.ofReal λ * rateDistortionFunction d P D₁
          + ENNReal.ofReal (1 - λ) * rateDistortionFunction d P D₂
```

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
- `mutualInfo_pi_eq_sum` (Common2026 既存): Phase C chain rule ✓
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

### 採用経路

- **Phase A+B core 完成**, **Phase C 全 deferred**, **Phase B specialization (log-sum 経由
  klDiv joint convexity discharge) も deferred**。`Common2026/Shannon/RateDistortionConvexity.lean`
  **256 行 / 0 sorry / 0 warning**。
- **Phase A** (`mixtureMeasure` + marginal / distortion / feasibility 保存): 5 補題、
  `Measure.map_add` / `Measure.map_smul` / `integral_add_measure` / `integral_smul_measure`
  + `ENNReal.ofReal_add` の plumbing で straight。
- **Phase B 主補題** (`rateDistortionFunction_convexOn`): **subnormal weakening** 採用 ——
  `klDiv` joint convexity を hypothesis (`h_klDiv_conv`) として取り回し、specializations
  (有限アルファベット pmf 形 etc.) は別ファイルで discharge する pattern。

### 撤退点

- **`klDiv` joint convexity の log-sum 経由 discharge** は撤退: per-atom `convexOn_klFun`
  だけでは joint 凸性が出ない (`q * klFun(p/q)` の `q` 側依存で log-sum inequality が必要、
  Mathlib 不在で ~150-200 行 gap)。subnormal 形で publish して discharge は specialization
  に委ねる方針に切替え。本格 discharge は別シード (例: E-4''' / E-4'') として再着手可能。
- **boundary case (lam = 0, lam = 1)** を明示的に case-split: `mul_iInf_of_ne` が `a ≠ 0`
  を要求するため、`ENNReal.ofReal lam = 0` ⟺ `lam = 0` の境界で詰む。strict 内部
  `0 < lam < 1` だけ `mul_iInf_of_ne` 適用、両端は別 branch で trivially close。

### iInf plumbing の流れ

1. `h_per_pair`: 任意 feasible `(ν₁, ν₂)` に対し mixture を構成、`mixtureMeasure_feasible` +
   `rateDistortionFunction_le_of_feasible` + hypothesis で `R(λD₁+(1-λ)D₂) ≤
   a · klDiv ν₁ + b · klDiv ν₂` を取得 (per-pair bound)。
2. RHS factorization: `a · R(D₁) + b · R(D₂)` を入れ子 iInf に展開
   (`ENNReal.mul_iInf_of_ne` を3層、`iInf_add` / `add_iInf` で外側 sum を分配)。
3. `le_iInf` を6層降りて per-pair bound に帰着。

### 規模実測

- Phase A: ~90 行 (mixtureMeasure 定義 + 5 補題 + docstring)
- Phase B 主補題: ~120 行 (h_per_pair sub-proof + boundary case split + iInf manipulation)
- 合計 **256 行** (見積 ~500-700 行を下回る、subnormal 化により log-sum 部分を省いたため)

### 自信のないコード箇所

- `h_aR1` / `h_bR2` の `iInf_congr` chain: nested iInf を `iInf_congr fun _ => ...` で
  深く降ろす手で書いており、層の数を間違えると `ENNReal.mul_iInf_of_ne` の側条件が合わずに
  失敗する。具体例として `klDiv` の引数に `ν₁.map Prod.fst` がそのまま現れる箇所が
  rfl で同型として扱えているのを確認済。
- boundary case `lam = 0, 1` の rewrite 順序: `ha_def` で `set` 済の `a, b` を `ha0, hb1`
  で書き換える順序を間違えると `rw` が pattern を見失う (実際初回はミスして再修正)。

### 計画通り / 乖離点

- **計画通り**: pmf 形 retreat の趣旨に沿って "joint convexity を hypothesis 化" で
  Phase B を完成。
- **乖離**: 計画は pmf 形 (Fintype α, β + MeasurableSingletonClass) 下で per-atom
  `convexOn_klFun` 適用を想定したが、log-sum inequality 経由の bridge が ~150-200 行
  gap で cap risk。subnormal weakening で抽象化、specialization は別ファイル / 別シード
  に委ねる方針 (D-1' / D-2'' Phase A 縮小と同 pattern)。

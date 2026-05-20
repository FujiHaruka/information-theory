# Shannon–McMillan–Breiman Phase C+D+E (E-8') 計画 🌙

(E-8' / moonshot-seeds.md、2026-05-14 起草)

> 実態整合 (2026-05-20): 主定理 DONE-UNCOND (別ファイル) — 無条件
> `shannon_mcmillan_breiman` は `Common2026/Shannon/SMBAlgoetCover.lean:2840` で完成
> (Algoet–Cover sandwich 経路、0 sorry、標準 `ErgodicProcess μ α` 仮定のみ)。
> Phase C の Birkhoff a.s. も `BirkhoffErgodic.lean:1031` で done。
> 例外: Phase E の **i.i.d. 特殊化 `aep_strong_of_smb`** は UNSTARTED
> (`rg aep_strong_of_smb Common2026/` で 0 件)。主定理は本 plan が想定した
> 「Birkhoff per-i 分解 + Levy upward」ではなく Algoet–Cover で先に閉じた。
>
> **Status (2026-05-14)**: 起草。E-8 Phase A+B (`Stationary.lean` 119 行 +
> `EntropyRate.lean` 498 行 = 617 行、0 sorry) 完了を前提に、
> Cover-Thomas 16.8 の **主定理 SMB + i.i.d. 特殊化** までを 3 段で完遂する。
> Phase C は **Mathlib に Birkhoff 個別エルゴード a.s. 版が不在** で plan の最大の山場。

## 進捗

- [x] Phase A — 定常エルゴード過程 ✅
- [x] Phase B — Entropy rate 定義 + 存在性 ✅
- [x] **Phase 0' — Mathlib 整備度再調査** ✅
- [x] **Phase C — Birkhoff a.s.** ✅ (`BirkhoffErgodic.lean:1031`)
- [x] **Phase D — SMB 主定理 `-(1/n) log p(X^n) → entropyRate` a.s.** ✅ (`SMBAlgoetCover.lean:2840`、Algoet–Cover 経路で達成)
- [ ] **Phase E — i.i.d. 特殊化 `aep_strong_of_smb`** 📋 UNSTARTED (未着手、コードに存在せず)

## 1. Goal (statement)

```lean
theorem shannon_mcmillan_breiman
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                 [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ =>
        -(1 / (n : ℝ)) *
          Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω}))
      Filter.atTop
      (𝓝 (entropyRate μ p.toStationaryProcess))
```

I.i.d. 特殊化 (Phase E):

```lean
theorem aep_strong_of_smb (μ₀ : Measure α) [IsProbabilityMeasure μ₀] :
    ∀ᵐ ω ∂(Measure.pi (fun _ : ℕ => μ₀)),
      Filter.Tendsto
        (fun n : ℕ => -(1 / (n : ℝ)) *
          ∑ i ∈ Finset.range n, Real.log (μ₀.real {ω i}))
        Filter.atTop
        (𝓝 (entropy μ₀ id))
```

## 2. Context

### E-8 Phase A+B 完了状況 (2026-05-14)

| 補題 | ファイル | 役割 |
|---|---|---|
| `StationaryProcess` / `ErgodicProcess` | `Stationary.lean:45,114` | `T` + `X` + `MeasurePreserving T μ μ` (+ `Ergodic`) |
| `obs i` / `blockRV n` | `Stationary.lean:62,81` | `X ∘ T^[i]` / `(X_0, …, X_{n-1})` |
| `identDistrib_obs_zero` | `Stationary.lean:94` | 定常性 |
| `blockEntropy` / `conditionalEntropyTail` / `entropyRate` | `EntropyRate.lean:58,63,69` | `H_n` / `H(X_n|X_{<n})` / `lim H_n/n` |
| `entropyRate_exists_of_stationary` | `EntropyRate.lean:432` | `H_n/n` 収束 |
| `entropyRate_eq_lim_condEntropy` | `EntropyRate.lean:466` | `H(X_n|X_{<n}) → entropyRate` |

### Mathlib 既存 API (E-8 Phase 0 確認済)

| API | パス | 役割 |
|---|---|---|
| `Ergodic` / `PreErgodic` / `aeconst_set` | `Dynamics/Ergodic/Ergodic.lean` | ergodic 構造 |
| `Integrable.tendsto_ae_condExp` (Levy) | `Probability/Martingale/Convergence.lean:360` | Levy 上昇収束 |
| `Submartingale.ae_tendsto_limitProcess` | `Probability/Martingale/Convergence.lean:209` | submartingale a.s. 収束 |
| `Filtration.natural` | `Probability/Process/Filtration.lean:394` | 自然 filtration |
| `condDistrib` | `Probability/Kernel/CondDistrib.lean:64` | 条件付き分布 |

### Mathlib 不在 (Phase C/E で自前要)

- **Birkhoff 個別エルゴード定理 a.s. 版**: `Dynamics/BirkhoffSum/` には等連続収束 + 固定点のみ。`MeanErgodic.lean` は Hilbert mean ergodic (L²)。a.s. 版 0 件。
- **i.i.d. shift の ergodicity**: 0 件。

## 3. Approach (3 段)

### (γ) Phase C ─ Birkhoff a.s. + log-likelihood 分解

**(γ.1) Birkhoff 個別エルゴード自前** (Mathlib gap、~200-300 行):
- Martingale 経路 (Lalley): 不変 σ-代数 `𝓘` を取り、`M_n := ∑_{i<n} (f ∘ T^[i] - condExp[f|𝓘])` を martingale 差分和、`Submartingale.ae_tendsto_limitProcess` で `M_n/n → 0` a.s.
- Ergodic ⇒ `𝓘` μ-trivial ⇒ `condExp[f|𝓘] = ∫ f dμ` a.s.

**(γ.2) Per-symbol conditional log-likelihood の Levy 収束** (~100 行):
- `pmfLogCond i ω := -log μ(X_i | X_0,…,X_{i-1})` (Levy で `pmfLogCondInfty` に a.s. 収束)
- `condDistrib` と `condExp[1_{X=a}]` の identity 経由

**(γ.3) Block log-likelihood の chain rule** (~50 行):
`-log p^n(x^n) = ∑_{i<n} -log p(x_i | x^{<i})` の Lean 翻訳

### (δ) Phase D ─ SMB 主定理 (Cover-Thomas 16.8 sandwich)

3 段 (~150-200 行):
1. Birkhoff を `pmfLogCondInfty` に適用 → `(1/n) ∑ pmfLogCondInfty(T^[k] ω) → ∫ pmfLogCondInfty dμ`
2. `∫ pmfLogCondInfty dμ = lim conditionalEntropyTail = entropyRate` (Phase B + monotone convergence)
3. Sandwich: 固定 `l` で `l`-Markov approximation + `l → ∞`

### (ε) Phase E ─ i.i.d. 特殊化 (~200-400 行)

- `iidProcess μ₀` 構成 (shift + projection)
- `Ergodic shift (Measure.pi μ₀)` (Kolmogorov 0-1 経由、~100-200 行)
- `entropyRate iidProcess = entropy μ₀ id`
- 既存 `AEP.lean:aep_ae` との 2 通り証明統合

### ファイル構成 (Phase E 完時)

```
Common2026/Shannon/
  Stationary.lean              ← Phase A (既存、119 行)
  EntropyRate.lean             ← Phase B (既存、498 行)
  BirkhoffErgodic.lean         ← Phase C.1 (新規、~250 行)
  SMB.lean                     ← Phase C.2-3 + D (新規、~300 行)
  SMBiid.lean                  ← Phase E (新規、~200 行)
```

## 4. Phase 0' Mathlib 再調査

- (0'.1) `Submartingale.ae_tendsto_limitProcess` の `hR` (L¹ bound) 適用方法
- (0'.2) Levy `Integrable.tendsto_ae_condExp` の filtration 引数形
- (0'.3) `condDistrib` と `condExp[1_{X=a}]` の identity
- (0'.4) `Measure.pi` shift invariance
- (0'.5) Kolmogorov 0-1 law からの shift ergodicity 経路

## 5-7. Phase C/D/E 詳細

(本文章は subagent 起草版を保存、Phase ごとの細目は省略 — 実装着手時に展開する)

## 8. Risks / Unknowns

### 最大 (Phase C.1 Birkhoff 自前)

Martingale 経路の `Submartingale.ae_tendsto_limitProcess` の `hR` plumbing が予測困難。
代替: maximal ergodic inequality (~400 行)。撤退: Birkhoff hypothesis 受け取り形に弱体化、自前は別 plan へ。

### 中 (Phase C.2 Levy + condDistrib、Phase E.2 i.i.d. shift ergodicity)

`α : Fintype` atom-wise plumbing / Kolmogorov 0-1 経由 plumbing。

## 9. 規模見積

| 経路 | 工数 | 行数 |
|---|---|---|
| Phase C (Birkhoff + Levy + chain rule) | 2〜3 週 | 350-450 |
| Phase D (SMB 主定理) | 0.5〜1 週 | 150-200 |
| Phase E (i.i.d. 接続) | 0.5〜1 週 | 250-400 |
| **Phase C+D+E** | **3〜5 週** | **750-1050** |

## 10. 撤退ライン

| 撤退ポイント | 判定基準 | アクション |
|---|---|---|
| C.1 Birkhoff 自前で 2 週超 | `Submartingale.ae_tendsto_limitProcess` 適用で詰まる | Birkhoff hypothesis 形に弱体化、自前は別 plan 切り出し |
| C.2 Levy で 1 週超 | `condDistrib` ↔ `condExp` 詰まり | `α := {0, 1}` MVP に縮退 |
| D.2 sandwich 詰まり | `l`-Markov approximation 詰まり | convergence in probability に弱体化 |
| E.2 i.i.d. shift ergodicity | Kolmogorov 0-1 経由 plumbing 詰まり | SMB を ergodic 仮定形で受け取り |

**Phase C+D 完で本 deferred 主目的達成**、Phase E (i.i.d. 接続) は付加。
**Phase C.1 Birkhoff 自前が最大の山場**、ここで詰まれば "Birkhoff 仮定形 SMB" + "Birkhoff 自前 Mathlib PR" の 2 段 publish。

## 11. 判断ログ

### 2026-05-14 — 起草

1. **Birkhoff 経路選択**: Martingale 経路 (Lalley) 採用 — Mathlib `Submartingale.ae_tendsto_limitProcess` + `tendsto_ae_condExp` 流用で 200-300 行見込み。Garsia 1965 (maximal ergodic) 経路 (~400 行) 却下。
2. **Filtration の向き**: Forward `ℱ_n := σ(X_0,…,X_{n-1})` 採用 (T invertibility 不要)。
3. **撤退優先順位**: Phase C.1 完 > Phase D 完 > Phase E 完。各撤退ラインで proof-log + metrics 取得、Mathlib gap (Birkhoff a.s.) 可視化が公的データポイント。

### 2026-05-14 — Phase C.1 着手分析 → 撤退

**結論**: 着手 Phase 0' Mathlib 再調査の時点で **martingale 経路は Mathlib API では成立しない**ことが判明。`BirkhoffErgodic.lean` 着手せず撤退。実装ファイルは未作成。

**Phase 0' 再調査結果**:
1. `loogle "birkhoff, Filter.Tendsto"` で Birkhoff a.s. 版 0 件確認 — Mathlib 既存は `Function.IsFixedPt.tendsto_birkhoffAverage` (固定点) / `tendsto_birkhoffAverage_apply_sub_birkhoffAverage` (等連続) / `MeanErgodic.lean` (Hilbert L²) のみ。
2. `MeasureTheory.Submartingale.ae_tendsto_limitProcess` (`Probability/Martingale/Convergence.lean:209`) は L¹-bounded submartingale `f n` 自体の a.s. 収束を `ℱ.limitProcess f μ` に与える。Birkhoff `(1/n) S_n` が必要とするのは `M_n / n → 0` (`M_n` が martingale 差分和)、これは `M_n` の収束ではない。**Mathlib API として直接適用できない**。
3. `grep -rn "backward\|reversed" Mathlib/Probability/Martingale/` で **reversed/backward martingale 収束定理は Mathlib に不在**を確認。Lalley 標準証明は `𝔼[S_n/n | T^{-n} σ]` を backward martingale として扱い `Doob`reversed convergence で `M_n / n → 0` を導くが、Mathlib にその基盤がない。
4. `Probability/StrongLaw.lean:strong_law_ae_real` は **i.i.d. 独立変数** 前提で ergodic 過程には流用不能。

**plan 想定との乖離**:
- plan §3.γ.1 想定: 「Lalley 経路で `Submartingale.ae_tendsto_limitProcess` で `M_n/n → 0` a.s.」
- 実態: その theorem は `M_n` (not `M_n / n`) の収束を与える別物。plan の `M_n/n → 0` 適用ルートは存在しない。

**残る代替経路**:
- (A) **Backward martingale 自前**: `Tendsto` of `𝔼[S_n/n | 𝒢_n]` (decreasing σ-algebra filtration) を自前構築 (~300-500 行)、`Submartingale.ae_tendsto_limitProcess` の reversed 版 PR。これ自体が独立な Mathlib 寄与候補。
- (B) **Maximal ergodic inequality (Garsia 1965)**: 純粋 ergodic 理論経路、Mathlib `Dynamics/Ergodic` を拡張 (~400-600 行)。事前却下していたが backward martingale も自前なら同程度の重量。
- (C) **Birkhoff 仮説形 SMB**: SMB を `birkhoff_hypothesis : Birkhoff f T μ` 仮定下で証明。Phase C.1 自前を完全に切り出し別 plan に。Phase D の主定理は `birkhoff_hypothesis` 引数を持つ形で着地。

**次セッション引き継ぎ**:
- 推奨: 経路 (C) Birkhoff 仮説形 SMB に弱体化、`BirkhoffErgodic.lean` は別 plan (`E-8''` 新規 deferred、`BirkhoffErgodic.lean` 自前 ~400-600 行 + Mathlib PR 1 本)。
- Phase D (SMB 本体) は経路 (C) 採用なら Birkhoff を `hypothesis` で受け取り `~150-200 行` で着地可能、本 plan の主目的 (Cover-Thomas 16.8) は仮説形で達成。
- 経路 (A)(B) は単独で Mathlib 寄与 PR の価値があるため別 plan 切り出し推奨。
- moonshot-seeds.md の `E-8'` deferred は「Phase C.1 Birkhoff 自前は別 plan、Phase D は仮説形」に再定義。

## 参考

- 親 plan: [`shannon-mcmillan-breiman-plan.md`](shannon-mcmillan-breiman-plan.md)
- E-8 実装: `Common2026/Shannon/Stationary.lean` + `EntropyRate.lean`
- moonshot template: [`docs/moonshot-plan-template.md`](../moonshot-plan-template.md)

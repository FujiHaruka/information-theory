# Shannon–McMillan–Breiman (E-8) ムーンショット計画 🌙

(E-8 / moonshot-seeds.md, 2026-05-13 起草)

> 実態整合 (2026-05-20): 主定理 DONE-UNCOND — 無条件 `shannon_mcmillan_breiman`
> 完成済 (`InformationTheory/Shannon/SMBAlgoetCover.lean:2840`、0 sorry、標準 `ErgodicProcess μ α`
> 仮定のみ)。4 sandwich 仮説は `algoet_cover_liminf_bound` / `algoet_cover_limsup_bound`
> / `blockLogAvg_bddAbove_ae` / `blockLogAvg_bddBelow_ae` で real discharge (pass-through
> でない)。liminf 下界は 2-sided 拡張 `μZ` (`InformationTheory/Probability/TwoSidedExtension.lean`、
> `ergodic_shiftZ` 経由) を使用。Phase C Birkhoff = `BirkhoffErgodic.lean:1031`。
> 例外: Phase E **i.i.d. 特殊化 `aep_strong_of_smb`** は UNSTARTED (コードに存在せず)。
>
> **Status (2026-05-13)**: 起草。`AEP.lean` (i.i.d.) を **定常エルゴード** に一般化する
> Cover-Thomas 16.8 SMB の Lean 形。Mathlib `Dynamics/Ergodic` + `Martingale/Convergence`
> (Levy's upward theorem) が前段揃っており、唯一の主要 gap は **定常確率過程の表現** と
> **entropy rate の定義**。
> **撤退ライン**: Phase A〜C 完了 (= 定常過程 + entropy rate + Birkhoff 接続) で
> 「SMB の `n · H ≤ -log p^n(X^n) + o(n) a.s.` の弱形」が立つ。Phase D / E は次セッション可。

## 進捗

- [x] Phase 0 — Mathlib 整備度調査 ✅ (2026-05-13)
- [x] Phase A — 定常エルゴード過程の Lean 表現 ✅ (2026-05-14、`Stationary.lean` 119 行、0 sorry)
- [x] Phase B — Entropy rate 定義 + 存在性 ✅ (2026-05-14、`EntropyRate.lean` 498 行、0 sorry)
- [x] Phase C — Birkhoff 接続 ✅ (`BirkhoffErgodic.lean:1031` `birkhoff_ergodic_ae`)
- [x] Phase D — 主定理 `-(1/n) log p(X^n) → H(𝒳) a.s.` ✅ (`SMBAlgoetCover.lean:2840`、Algoet–Cover 経路)
- [ ] Phase E — i.i.d. 特殊化との接続 📋 UNSTARTED (`aep_strong_of_smb` 未着手、コードに存在せず)

**MVP 完了サマリ (2026-05-14)**: `InformationTheory/Shannon/Stationary.lean` (119 行) + `EntropyRate.lean` (498 行) = 合計 617 行、0 sorry / 0 warning。
- Phase A: `StationaryProcess` / `ErgodicProcess` 構造体 + `obs` / `blockRV` 定義 + measurability + `identDistrib_obs_zero` (定常性ラベル)
- Phase B: `blockEntropy` / `conditionalEntropyTail` / `entropyRate` 定義 + `blockEntropy_succ_chain_rule` (B.1) + `conditionalEntropyTail_antitone` (B.2、定常性 reshape + conditioning monotonicity) + `entropyRate_exists_of_stationary` (B.3、Cesàro) + `entropyRate_eq_lim_condEntropy` (B.4)
- 鍵 helper: `condEntropy_eq_pushforward` (joint pushforward 等式 ⇒ condEntropy 等式、汎用性高い)

**残り Phase C-E は `E-8'` deferred として後継**: Birkhoff 個別エルゴード a.s. 版が Mathlib 不在で自前 200-400 行が最大の山場。MVP の Phase A+B は Mathlib 上流 PR 候補 (`Stationary.lean` + `EntropyRate.lean` の structure 部分)。

## ゴール / Approach

**最終定理 (Cover-Thomas 16.8.1)**: `(Ω, T, μ)` 定常エルゴード過程, `X : Ω → α`
observable (有限アルファベット), `X_i := X ∘ T^i` で
```
∀ᵐ ω ∂μ, Tendsto (fun n => -(1/n) · Real.log (μ.real {ω' | (X_0 ω', …, X_{n-1} ω') = (X_0 ω, …, X_{n-1} ω)}))
                  Filter.atTop (𝓝 (entropyRate μ T X))
```

ただし `entropyRate μ T X := lim_n H(X_0, X_1, …, X_{n-1}) / n` (定常性で存在)。

### Approach (3 段)

**(α) 定常エルゴード過程を `MeasurePreserving` shift + `Ergodic` で表現**:
`(Ω, μ)` 上の `T : Ω → Ω` を `MeasurePreserving T μ μ`、`Ergodic T μ` の 2 条件で押さえる。
`X : Ω → α` は単一の観測写像で十分 (= `Xs i := X ∘ T^i` で時系列を生成、`i.i.d.` 形の
`Xs : ℕ → Ω → α` の代替)。i.i.d. 特殊化は `Ω := ℕ → α`, `T := shift`, `μ := pi (μ_0)`,
`X := fun ω => ω 0` で再得 (Phase E)。

**(β) Entropy rate を `lim H(X_0, …, X_{n-1}) / n` で定義** (Cover-Thomas 4.2.1):
`H_n := entropy μ (blockRV X T n)` (= `H(X_0, …, X_{n-1})`) は定常性 + chain rule で
`H_{n+1} - H_n = H(X_n | X_0, …, X_{n-1}) ≤ H(X_{n-1} | X_0, …, X_{n-2}) = H_n - H_{n-1}`
の凸性 (差分が単調非増) を持ち、`H_n / n` が極限を持つ (Cesàro)。同値形
`entropyRate = lim H(X_n | X_0, …, X_{n-1})` も別補題で確立。

**(γ) Birkhoff 個別エルゴードを log-likelihood 列に適用**:
SMB の鍵は分解
```
-(1/n) log μ(X^n = x^n) = -(1/n) ∑_{i=0}^{n-1} log μ(X_i = x_i | X^{<i} = x^{<i})
```
+ Levy's upward theorem (`tendsto_ae_condExp`) で
`-log μ(X_i = · | X^{<i})` が `i → ∞` で `-log μ(X_0 = · | X^{<∞})` に a.s. 収束する点別収束を取り、
Birkhoff の個別エルゴード定理で時系列平均 → 空間平均 (= `entropyRate`) に持ち上げる。
**Mathlib に Birkhoff の個別エルゴード a.s. 版は未整備** (mean ergodic は `MeanErgodic.lean`
に Hilbert 空間版だけ)、Phase C で自前で書く必要あり。これが本 plan の **最大リスク**。

### Approach 図

```
Phase 0  : Mathlib 整備度調査                                ← 1〜2 ターン
           ─────────────────────────────────────────
Phase A  : 定常エルゴード過程 `MeasurePreserving T μ μ` +    ← 0.5〜1 週
           `Ergodic T μ` + `Xs i := X ∘ T^i` plumbing
           ─────────────────────────────────────────
Phase B  : entropy rate 定義 + 単調収束による存在             ← 1〜1.5 週
           ─────────────────────────────────────────
Phase C  : Birkhoff 個別エルゴード定理 (自前 or Mathlib 補強) ← 山場、2〜3 週
           + log-likelihood の per-i 分解
           ─────────────────────────────────────────
Phase D  : 主定理 `-(1/n) log p^n(X^n) → H a.s.`             ← 0.5〜1 週
           ─────────────────────────────────────────
Phase E  : i.i.d. 特殊化 (既存 AEP.lean との橋渡し)           ← 0.5〜1 週
```

**ファイル構成 (Phase E 完時)**:
```
InformationTheory/Shannon/
  Stationary.lean              ← Phase A (定常過程 + shift API)
  EntropyRate.lean             ← Phase B (entropy rate 定義 + 存在性)
  BirkhoffErgodic.lean         ← Phase C (個別エルゴード定理、自前)
  ShannonMcMillanBreiman.lean  ← Phase D + E (主定理)
```

**撤退ライン**: Phase A〜C 緑通過 = 定常過程 + entropy rate + Birkhoff の基盤完成、
Phase D の SMB 主定理は組み立てだけで届く位置に。Birkhoff 個別エルゴードが Mathlib
に整備されれば Phase C は数日に短縮、未整備のままなら Phase C 単独で全体の半分以上の
労力。

---

## Phase 0 — Mathlib 整備度調査

### スコープ

Birkhoff / Ergodic / 定常過程 / entropy rate が Mathlib にどこまであるか裏取り。

### 調査結果 (起草時、2026-05-13)

#### 1. `MeasureTheory.Ergodic` ✅ 整備済み

`.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/Ergodic.lean:50`:

```lean
structure Ergodic (f : α → α) (μ : Measure α := by volume_tac) : Prop extends
  MeasurePreserving f μ μ, PreErgodic f μ
```

- 派生形: `PreErgodic` (測度保存抜き), `QuasiErgodic` (準測度保存)
- 基本 API: `Ergodic.ae_empty_or_univ_of_preimage_ae_le` (`Ergodic.lean:208`),
  `Ergodic.aeconst_preimage` (`MeasurePreserving.lean:176`),
  `PreErgodic.prob_eq_zero_or_one` (`Ergodic.lean:75`)

#### 2. `MeasureTheory.MeasurePreserving` ✅ 整備済み

`.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:45`:

```lean
structure MeasurePreserving (f : α → β)
  (μa : Measure α := by volume_tac) (μb : Measure β := by volume_tac) : Prop where
  protected measurable : Measurable f
  protected map_eq : map f μa = μb
```

- 246 declarations mention `MeasurePreserving` (loogle 確認)。`iterate`, `comp`,
  `congr`, `measure_preimage` 一式揃う。
- `MeasurePreserving.iterate` で `T^n` も `MeasurePreserving` (i.i.d. 特殊化で必須)。

#### 3. Birkhoff 個別エルゴード定理 ⚠️ **Mathlib 未整備**

- `Dynamics/BirkhoffSum/Basic.lean`: `birkhoffSum f g n x := ∑ i < n, g (f^[i] x)` 定義のみ。
- `Dynamics/BirkhoffSum/Average.lean:46`: `birkhoffAverage R f g n x := (n : R)⁻¹ • birkhoffSum f g n x`
  定義 + 算法プロパティのみ。
- `Dynamics/BirkhoffSum/NormedSpace.lean`: 固定点での収束 `IsFixedPt.tendsto_birkhoffAverage`、
  Cauchy 差 `tendsto_birkhoffAverage_apply_sub_birkhoffAverage` (= 一様等連続性ベース)、
  `isClosed_setOf_tendsto_birkhoffAverage` (収束集合は閉) のみ。
- `Analysis/InnerProductSpace/MeanErgodic.lean`: **Hilbert 空間 mean ergodic** のみ
  (`LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure`, `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`)。
- **Birkhoff 個別エルゴード定理 (a.s. 収束)**: `rg "ae_tendsto.*birkhoff\|individual_ergodic"` で 0 件、未整備。
- **影響**: Phase C で `(1/n) ∑ f(T^i x) → ∫ f dμ a.s.` を自前で書くか、Mathlib に
  別途寄与する必要あり。**本 plan の最大リスク要因**。

#### 4. 定常確率過程 (`stationaryProcess` 等) ⚠️ **Mathlib 未整備**

- `rg "stationary\|Stationary" Mathlib/Probability/` で 0 件。
- 代替: **`Ω = ℕ → α`, `T = shift`, `μ` が `T`-invariant** という standard formulation を
  自前で組み立てる (Phase A)。これは Mathlib の `MeasurePreserving` で十分表現可能、
  独立な新規 type を切る必要なし。

#### 5. Entropy rate (`entropyRate`) ⚠️ **Mathlib 未整備**

- `rg "entropyRate\|entropy_rate" Mathlib/` で 0 件、自前定義必要 (Phase B)。

#### 6. 条件付期待値 + Levy's upward theorem ✅ 整備済み (SMB の核心)

`.lake/packages/mathlib/Mathlib/Probability/Martingale/Convergence.lean`:

- `Integrable.tendsto_ae_condExp` (`Convergence.lean:360`):
  ```lean
  theorem Integrable.tendsto_ae_condExp (hg : Integrable g μ)
      (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
      ∀ᵐ x ∂μ, Tendsto (fun n => (μ[g | ℱ n]) x) atTop (𝓝 (g x))
  ```
- `tendsto_ae_condExp` (`Convergence.lean:426`): **Levy's upward theorem**
  ```lean
  theorem tendsto_ae_condExp (g : Ω → ℝ) :
      ∀ᵐ x ∂μ, Tendsto (fun n => (μ[g | ℱ n]) x) atTop (𝓝 ((μ[g | ⨆ n, ℱ n]) x))
  ```
- これは SMB の **per-i log-likelihood の a.s. 収束** の鍵 (Cover-Thomas 16.8 主定理
  の中核): `f_i(ω) := -log μ(X_0 = X_0 ω | X_{-1}, X_{-2}, …, X_{-(i-1)})` が
  `i → ∞` で `f_∞(ω) := -log μ(X_0 = X_0 ω | X_{-1}, X_{-2}, …)` に a.s. 収束。

#### 7. Sandwich lemma / dominated convergence for a.s.

Mathlib `MeasureTheory.Integrable.aestronglyMeasurable_*` + `tendsto_*_of_dominated` 系
で SMB の sandwich argument (Cover-Thomas Lemma 16.8.1 の upper / lower bound) は
取れる見込み。**詳細裏取りは Phase C 着手時** (起草時はスキップ)。

### Phase 0 結論

- **Mathlib 不在 (Phase C で自前必須)**: Birkhoff 個別エルゴード定理 (a.s. 収束版)。
- **Mathlib 不在だが軽量 (自前定義)**: stationary process predicate (= `MeasurePreserving T μ μ`),
  entropy rate (`entropyRate`)。
- **Mathlib 整備済み**: `MeasurePreserving` / `Ergodic` 構造 + 基本 API、Levy's upward theorem
  (`tendsto_ae_condExp`)、`condExp` + martingale convergence。
- **撤退ライン候補**: Phase C で Birkhoff 自前実装が 2 週超で詰まる場合、SMB 主定理を
  「Birkhoff を仮定として受ける」形に弱体化、Mathlib 寄与は別 plan に分離。

---

## Phase A — 定常エルゴード過程の Lean 表現 📋

### スコープ

```lean
namespace InformationTheory.Shannon

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                     [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A stationary process: a measure-preserving transformation `T : Ω → Ω` on `(Ω, μ)`
together with an observable `X : Ω → α`. The time-`i` observation is `X ∘ T^[i]`. -/
structure StationaryProcess (μ : Measure Ω) (α : Type*) [MeasurableSpace α] where
  T : Ω → Ω
  X : Ω → α
  measurePreserving : MeasurePreserving T μ μ
  measurable_X : Measurable X

/-- Time-`i` observation. -/
def StationaryProcess.obs (p : StationaryProcess μ α) (i : ℕ) : Ω → α :=
  p.X ∘ p.T^[i]

/-- An ergodic stationary process is a stationary process with `Ergodic T μ`. -/
structure ErgodicProcess (μ : Measure Ω) (α : Type*) [MeasurableSpace α]
    extends StationaryProcess μ α where
  ergodic : Ergodic T μ

/-- Block joint observation `(X_0, X_1, …, X_{n-1}) : Ω → (Fin n → α)`. -/
def StationaryProcess.blockRV (p : StationaryProcess μ α) (n : ℕ) : Ω → (Fin n → α) :=
  fun ω i => p.obs i ω

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(A.1) `StationaryProcess` 構造体** + 基本 measurability
  - `measurable_obs (i : ℕ)` (= `measurable_X` + `MeasurePreserving.iterate.measurable` の合成)
  - `measurable_blockRV (n : ℕ)`
- [ ] **(A.2) `ErgodicProcess` 構造体** + `toStationaryProcess` 自動 coercion
- [ ] **(A.3) 定常性のラベルづけ**: `IdentDistrib (obs i) (obs 0) μ μ` を `MeasurePreserving.iterate`
  + `Measure.map_comp` で導出。20〜30 行
- [ ] **(A.4) i.i.d. 特殊化への橋頭**: Phase E で使用する
  `iid_of_pi : (μ_0 : Measure α) → ErgodicProcess (Measure.pi (fun _ : ℕ => μ_0)) α` の
  shape sketch (本体は Phase E)。

### Done 条件

- 上記 4 項目が `lake env lean InformationTheory/Shannon/Stationary.lean` で silent
- `InformationTheory.lean` に `import` 行追記

### 工数感

0.5〜1 週、~150 行。**最大リスク**: `MeasurePreserving T^[n]` を `μ.map (T^[n] ω) =
μ.map ω` 形に展開して `IdentDistrib (obs i) (obs 0)` を引き出す chain rule の plumbing。
`MeasurePreserving.iterate` は既存だが、`map_comp` で `X ∘ T^[i]` の像測度を扱う段で
`measurable_comp` の引数渡しが煩雑。

### 撤退ライン (Phase A 内)

- 構造体形 (`StationaryProcess` / `ErgodicProcess`) で型推論が重い場合 → **structure をやめて
  bare-fields 渡し** (`(T : Ω → Ω) (X : Ω → α) (hT : MeasurePreserving T μ μ)
  (hX : Measurable X)` を毎定理で受け取る形) に切り替え。
  この場合 Phase E の i.i.d. instance 化はパッケージ化なしで bare arguments のまま。

---

## Phase B — Entropy rate 定義 + 単調収束による存在 📋

### スコープ

```lean
namespace InformationTheory.Shannon

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                     [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Block entropy: `H(X_0, X_1, …, X_{n-1})` for a stationary process. -/
noncomputable def blockEntropy (p : StationaryProcess μ α) (n : ℕ) : ℝ :=
  entropy μ (p.blockRV n)

/-- Entropy rate (definition 1, Cover-Thomas 4.2.1): `lim H(X_0, …, X_{n-1}) / n`.

Existence proven separately via `entropyRate_exists_of_stationary`. -/
noncomputable def entropyRate (p : StationaryProcess μ α) : ℝ :=
  Filter.atTop.limUnder (fun n : ℕ => blockEntropy μ p n / n)

/-- Per-conditional form (Cover-Thomas 4.2.1 alternative):
`H(X_n | X_0, X_1, …, X_{n-1})`. Decreasing in `n` by stationarity + chain rule. -/
noncomputable def conditionalEntropyTail (p : StationaryProcess μ α) (n : ℕ) : ℝ :=
  InformationTheory.MeasureFano.condEntropy μ (p.obs n) (p.blockRV n)

/-- Existence: `blockEntropy p n / n` converges. -/
theorem entropyRate_exists_of_stationary (p : StationaryProcess μ α) :
    ∃ H : ℝ, Tendsto (fun n => blockEntropy μ p n / n) atTop (𝓝 H)

/-- Equality of two definitions: `lim H_n/n = lim H(X_n | X_0,…,X_{n-1})`. -/
theorem entropyRate_eq_lim_condEntropy (p : StationaryProcess μ α) :
    Tendsto (fun n => conditionalEntropyTail μ p n) atTop (𝓝 (entropyRate μ p))

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(B.1) `blockEntropy` 定義** + `blockEntropy μ p (n+1) - blockEntropy μ p n =
      conditionalEntropyTail μ p n` (chain rule、既存 `entropy_pair_eq_entropy_add_condEntropy` 流用)。
      30〜50 行
- [ ] **(B.2) `conditionalEntropyTail` の単調非増 (定常性で)**: 凸性
      `H(X_n | X_0, …, X_{n-1}) ≤ H(X_{n-1} | X_0, …, X_{n-2})` を `condEntropy_le_condEntropy_of_pair`
      (`CondMutualInfo.lean:240`) + 定常性の `IdentDistrib (X_{n-1}, X_0…X_{n-2}) (X_n, X_1…X_{n-1})` で
      取る。40〜80 行
- [ ] **(B.3) `entropyRate_exists_of_stationary`**: 単調非増数列 `conditionalEntropyTail μ p n`
      は下に有界 (`0 ≤ condEntropy`) なので極限を持つ、Cesàro で `H_n / n` も同極限。
      `tendsto_Cesaro_of_tendsto` (Mathlib 既存) を呼ぶ。30〜60 行
- [ ] **(B.4) `entropyRate_eq_lim_condEntropy`**: Cesàro 補題で B.3 と同値、または直接
      `H_n / n` と `conditionalEntropyTail μ p (n-1)` の差が `o(1)` を取る。30〜50 行

### Done 条件

- 上記 4 項目が silent
- proof-log + metrics 取得

### 工数感

1〜1.5 週、~250 行。**最大リスク**: (B.2) で **定常性の起動** が定理単位で必要、
`IdentDistrib (X_{n-1}, X_0,…,X_{n-2}) (X_n, X_1,…,X_{n-1})` を `MeasurePreserving T^[1]`
から導く plumbing (`Measure.map_comp` + `IdentDistrib.comp` でカスケード) が
50〜100 行で詰まる可能性。

### 撤退ライン (Phase B 内)

- (B.2) 凸性 plumbing で 5〜7 日溶ける → `entropyRate` を直接 `lim H_n / n` の
  `liminf` 形で定義し、`liminf = limsup` (= 収束) を `B.3` 後付けで取る経路に変更。
- (B.4) 同値性が plumbing-heavy → Phase D の主定理は `blockEntropy / n` 経由形で
  steeple、conditional 形は別補題に分離。

---

## Phase C — Birkhoff 接続 (個別エルゴード定理 + log-likelihood per-i 分解) 📋

### スコープ (本 plan **最大の山場**)

```lean
namespace InformationTheory.Shannon

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                     [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Per-symbol log-likelihood for a stationary process:
`pmfLogCond p i ω := -log μ(X_i = X_i ω | X_0, …, X_{i-1})`.

This is the per-step contribution to `-log p^n(X^n)`. -/
noncomputable def pmfLogCond (p : StationaryProcess μ α) (i : ℕ) : Ω → ℝ :=
  fun ω => -Real.log ((condDistrib (p.obs i) (p.blockRV i) μ (p.blockRV i ω)).real {p.obs i ω})

/-- Block log-likelihood decomposition (chain rule for log-prob):
`-log p^n(X^n ω) = ∑_{i < n} pmfLogCond p i ω`. -/
theorem log_block_eq_sum_condLog (p : StationaryProcess μ α) (n : ℕ) :
    ∀ᵐ ω ∂μ,
      -Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})
        = ∑ i ∈ Finset.range n, pmfLogCond μ p i ω

/-- Limit conditional log-likelihood:
`pmfLogCondInfty p ω := -log μ(X_0 = X_0 ω | X_{-1}, X_{-2}, …)`.

Implemented via Levy's upward theorem with filtration `ℱ_n := σ(X_1, …, X_n)`
applied to the natural one-sided extension. -/
noncomputable def pmfLogCondInfty (p : StationaryProcess μ α) : Ω → ℝ

/-- Levy convergence: `pmfLogCond p i ω → pmfLogCondInfty p ω` as `i → ∞` a.s.

Direct application of `MeasureTheory.tendsto_ae_condExp`. -/
theorem pmfLogCond_tendsto_pmfLogCondInfty (p : StationaryProcess μ α) :
    ∀ᵐ ω ∂μ, Tendsto (fun i => pmfLogCond μ p i ω) atTop (𝓝 (pmfLogCondInfty μ p ω))

/-- Birkhoff individual ergodic theorem (a.s. version):
For ergodic `T` and integrable `f : Ω → ℝ`,
`(1/n) ∑_{i < n} f (T^i ω) → ∫ f dμ` a.s.

**Mathlib gap — proof from scratch in this Phase**.
-/
theorem birkhoff_ergodic_ae (p : ErgodicProcess μ α) (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (∑ i ∈ Finset.range n, f (p.T^[i] ω)) / n)
      atTop (𝓝 (∫ ω', f ω' ∂μ))

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(C.1) `pmfLogCond` 定義 + measurability**: `condDistrib` (Mathlib
      `Probability/Kernel/Disintegration/CondDistrib.lean`) を経由。`(condDistrib …).real {x}`
      で `α : Fintype` から有限関数。30〜50 行
- [ ] **(C.2) `log_block_eq_sum_condLog`**: 連鎖律 `μ(X^n = x^n) = μ(X_0) · ∏_{i ≥ 1}
      μ(X_i = x_i | X^{<i})` の log 取り。`Real.log_prod` + `condDistrib_compProd_eq` 系で
      40〜80 行
- [ ] **(C.3) `pmfLogCondInfty` 定義 + measurability**: フィルトレーション `ℱ_i :=
      MeasurableSpace.comap (blockRV i) inferInstance` 経由で `condExp` から
      `-log μ(X_0 ∈ · | ℱ_i)` を taking the limit; 定義可能性は `tendsto_ae_condExp` が
      存在保証。30〜60 行
- [ ] **(C.4) `pmfLogCond_tendsto_pmfLogCondInfty`**: Levy's upward theorem
      (`tendsto_ae_condExp`) を `g = -log μ(X_0 = · | ·)` の `α : Fintype` 個別関数化で
      適用、`α : Fintype` の各 atom `a` ごとに `1_{X_0 = a}` の condExp を取って和。
      80〜120 行
- [ ] **(C.5) `birkhoff_ergodic_ae`** ─ **Mathlib gap、自前で書く**:
      - 標準証明 (Garsia 1965 / Katznelson-Weiss 1982): maximal ergodic inequality →
        `limsup birkhoffAverage f ≤ ∫ f` a.s. (上限) と `liminf birkhoffAverage f ≥ ∫ f`
        a.s. (下限) の 2 方向、`Ergodic.aeconst_preimage` で `limsup` と `liminf` が
        a.s. 定数、定数値の同一性は積分の `dominated convergence` で `∫ f dμ` に固定。
      - **Mathlib 既存 `Submartingale.ae_tendsto_limitProcess` 流用が現実的か検討の余地**:
        Birkhoff sum を martingale 関連の収束に reduce する経路 (Lalley exposition):
        `M_n := ∑ i < n, (f - condExp f F_i)` が martingale で、`|M_n|/n → 0` a.s. が
        Lévy + `condExp f F_i → 0` (= invariant σ-algebra trivial で `f - 0 = f`)
        から取れる。**Mathlib API で書くなら本経路**、 200〜400 行。
      - 注: 既存 Mathlib `MeanErgodic.lean` は Hilbert 空間 `L²` 形のみで、a.s. には
        直接展開できない。
      - **撤退**: Phase C 全体で 3 週超なら、SMB を「Birkhoff を仮定として受ける」
        形に弱体化、Phase E は Birkhoff 自前のかわりに Mathlib の strong law (i.i.d.
        特殊化) で済ます。

### Done 条件

- 上記 5 項目が silent
- proof-log + metrics 取得
- (C.5) は Mathlib 寄与候補としても整形 (将来別 PR)

### 工数感

**2〜3 週、~500〜700 行**。**Phase C.5 が本 plan の最大の不確実性**。

- C.1〜C.4: ~250 行、Levy + condDistrib の plumbing、Mathlib 既存で書ける見込み。
- C.5: **200〜400 行**、maximal ergodic inequality + martingale 経路の自前実装。
  Mathlib `Submartingale.ae_tendsto_limitProcess` 流用度次第。

### 撤退ライン (Phase C 内)

- (C.5) で 2 週溶ける → **`birkhoff_ergodic_ae` を hypothesis として受ける**形に
  Phase D 主定理を弱体化、自前実装は別 plan `docs/dynamics/birkhoff-individual-ergodic-plan.md`
  に切り出し。
- (C.4) Levy 適用で `α : Fintype` atom-wise condExp の handling で詰まる →
  `α := {0, 1}` (binary alphabet) 限定 MVP に縮退、一般 finite alphabet は次セッション。

---

## Phase D — 主定理 `-(1/n) log p^n(X^n) → H a.s.` 📋

### スコープ

```lean
namespace InformationTheory.Shannon

/-- Shannon–McMillan–Breiman theorem (Cover-Thomas 16.8.1):
For a stationary ergodic process `p`,
`-(1/n) log p^n(X^n) → entropyRate μ p` almost surely. -/
theorem shannon_mcmillan_breiman
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                 [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => -(1 / (n : ℝ)) * Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω}))
      atTop (𝓝 (entropyRate μ p.toStationaryProcess))

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(D.1) `-(1/n) ∑ pmfLogCond μ p i ω → ∫ pmfLogCondInfty μ p dμ a.s.`**:
  Birkhoff 個別エルゴード (C.5) を `f := pmfLogCondInfty μ p` で適用するが、
  和は `pmfLogCond i` (時刻依存) で取られているので、**(a) `pmfLogCond i → pmfLogCondInfty`
  (Phase C.4)** + **(b) Birkhoff on the limit** + **(c) Cesàro sandwich** の 3 段
  組み合わせ。Cover-Thomas 16.8 の核心ステップ。100〜150 行
- [ ] **(D.2) `∫ pmfLogCondInfty μ p dμ = entropyRate μ p`**: Phase B `entropyRate_eq_lim_condEntropy`
  + `pmfLogCondInfty` の積分 = `conditionalEntropyTail` の極限。50〜80 行
- [ ] **(D.3) `log_block_eq_sum_condLog` (Phase C.2) で `-(1/n) log p^n(X^n) =
  -(1/n) ∑ pmfLogCond μ p i ω` に展開**、(D.1) + (D.2) で結論。30〜50 行

### Done 条件

- 上記 3 項目が silent
- proof-log + metrics 取得済み、Cover-Thomas 16.8.1 主定理と statement 一致

### 工数感

0.5〜1 週、~250 行。Phase C が片付けば組み立てのみ。

### 撤退ライン (Phase D 内)

- (D.1) sandwich argument で詰まる (`pmfLogCond i ≠ pmfLogCondInfty` の誤差が
  Birkhoff の収束で吸収できることの plumbing) → SMB を **convergence in probability**
  に弱体化、a.s. 主形は次セッションに保留。

---

## Phase E — i.i.d. AEP との接続 📋

### スコープ

```lean
namespace InformationTheory.Shannon

/-- i.i.d. specialization: SMB recovers the i.i.d. AEP of `AEP.lean`. -/
theorem aep_of_smb_iid
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                 [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ_0 : Measure α) [IsProbabilityMeasure μ_0] :
    ∀ᵐ ω ∂(Measure.pi (fun _ : ℕ => μ_0)), Tendsto
      (fun n => -(1 / (n : ℝ)) *
        ∑ i ∈ Finset.range n, Real.log (μ_0.real {ω i}))
      atTop (𝓝 (entropy μ_0 id))

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(E.1) i.i.d. instance**: `Ω := ℕ → α`, `T := fun ω => ω ∘ (· + 1)` (shift),
      `X := fun ω => ω 0`, `μ := Measure.pi (fun _ => μ_0)`。`MeasurePreserving T μ μ`
      は `Measure.pi_shift_eq_pi` 系 (Mathlib 既存) で取れる。50〜100 行
- [ ] **(E.2) `Ergodic T μ` for i.i.d. shift**: Kolmogorov 0-1 law 経由、または
      `Ergodic.iid_shift` の整備度を Phase E 着手時に確認。**Mathlib 整備度未確認、Phase 0
      の 0.5 ターン枠で追加調査が必要**。100〜200 行 (Mathlib 不在なら自前)
- [ ] **(E.3) `entropyRate (iid_process μ_0) = entropy μ_0 id`**: i.i.d. では
      `H(X_0, …, X_{n-1}) = n · H(X_0)` (Phase A の `entropy_jointRV_eq_n_smul` の
      対形)、`H_n / n = H(X_0)` 定数 → 極限も `H(X_0)`。30〜50 行
- [ ] **(E.4) `aep_of_smb_iid` 主定理**: Phase D の SMB を i.i.d. instance に適用、
      `pmfLogCond i = -log μ_0(X_i ω)` (i.i.d. では condition 不要) で書き換え、
      既存 `AEP.lean:aep_ae` と statement 比較で整合性確認。50〜100 行

### Done 条件

- 上記 4 項目が silent
- 既存 `AEP.lean:aep_ae` から `aep_of_smb_iid` 経由の **2 通り証明** が成立
  (実装は Phase E に集中、re-derive のみ)
- proof-log + metrics 取得済み

### 工数感

0.5〜1 週、~250〜400 行。**最大リスク**: (E.2) `Ergodic T μ` for i.i.d. shift の Mathlib
整備度。未整備なら自前 (= Kolmogorov 0-1 + tail σ-algebra のスケッチ) で +200 行。

### 撤退ライン (Phase E 内)

- (E.2) Mathlib に i.i.d. shift の ergodicity 不在 → 自前 200 行で書くか、SMB を
  「ergodic を仮定として受ける」形 (= `ErgodicProcess` を直接受け取り、i.i.d. 特殊化は
  別 plan) で fallback。

---

## 失敗判定 / 撤退ライン (全体)

| 撤退ポイント | 判定基準 | アクション |
|---|---|---|
| Phase 0 で Birkhoff 個別エルゴードが Mathlib にあった | 起草時 0 件確認済み | 不該当 (Phase C 自前確定) |
| Phase A の `StationaryProcess` 構造体で型推論重 | (A.1)〜(A.3) で 5 日溶ける | bare-fields 渡しに切り替え、structure 化は Phase E に後送 |
| Phase B (B.2) 凸性 plumbing で 5〜7 日溶ける | 定常性経由の `IdentDistrib` chain が plumbing-heavy | `entropyRate` を `liminf` 形定義に変更、existence は post-hoc |
| **Phase C (C.5) Birkhoff 自前で 2 週超** | maximal ergodic inequality の Mathlib API 不足 | **SMB を `birkhoff_ergodic_ae` 仮定受け取り形に弱体化**、自前実装は別 plan に切り出し |
| Phase D (D.1) sandwich argument 詰まり | `pmfLogCond i ↔ pmfLogCondInfty` の Cesàro 誤差吸収 plumbing | SMB を **convergence in probability** に弱体化 |
| Phase E (E.2) i.i.d. shift ergodicity の Mathlib 不在 | Phase E 着手時 loogle 再確認 | 自前 +200 行 or SMB を ergodic 仮定で受け取り、i.i.d. 接続は別 plan |

**全体撤退ライン**: Phase A〜C 完了 (= Birkhoff 含む基盤完成) で SMB 主定理は届く位置に。
Phase C.5 (Birkhoff 自前) が長引けば、SMB 主定理を「Birkhoff を仮定として受ける」弱形で
publish + Mathlib 寄与 PR (Birkhoff 個別エルゴード a.s.) を別 plan に分離。

---

## 工数見積もり総括

| 経路 | 工数 | 行数 | リスク |
|---|---|---|---|
| Phase A〜C (基盤完成、Birkhoff 自前含む) | **3.5〜5.5 週** | **900〜1250 行** | **高** (C.5 Birkhoff) |
| Phase A〜E (i.i.d. 特殊化込み 主定理) | **5〜7 週** | **~1500 行 (シード一致)** | 高 |
| Phase D 単独 (Phase C 後の主定理組み立て) | 0.5〜1 週 | 250 行 | 低 (組み立てのみ) |
| Phase E 単独 (i.i.d. 接続) | 0.5〜1 週 | 250〜400 行 | 中 (E.2 ergodicity 依存) |

**Mathlib 整備度に応じた行数変動**:
- Birkhoff 個別エルゴードを Mathlib 寄与で先取得できれば: **Phase C −300 行** で
  合計 1200 行程度。
- 定常過程 / entropy rate の自前定義は不可避 (Mathlib 不在確定)。

**i.i.d. AEP (`AEP.lean`) との比較**: i.i.d. AEP は `strong_law_ae_real` 1 発で済むが、
SMB は強法則の代替として **Birkhoff 個別エルゴード + Levy's upward theorem** の 2 段を
必要とし、Phase C が AEP 全体の 1.5〜2 倍の規模。`AEP.lean` (Phase A〜C で ~800 行) と
本 SMB (Phase A〜E で ~1500 行) の差はほぼ全部 Phase C (Birkhoff 自前 + Levy 接続)。

---

## 当面の next step

1. **Phase 0 (本起草) — 完了 (2026-05-13)**
2. **Phase A skeleton** — `InformationTheory/Shannon/Stationary.lean` を sorry-driven で書き始め、
   `StationaryProcess` / `ErgodicProcess` 構造体 + 基本 `measurable_obs` を sorry 割る ← **次これ**
3. **Phase A 完で Phase B 着手判定** — entropy rate 定義 + 単調性
4. **Phase B 完で Phase C 着手判定** — **Phase C は山場、ここで Birkhoff 自前の plumbing
   状況を見て撤退判定**
5. **Phase C 完 = 撤退ライン到達**: proof-log + metrics 取得、Phase D 着手か別 plan 分離か判断
6. **Phase D 完で Phase E 着手判定** — i.i.d. 接続
7. **Phase E 完 = 主目標完了** — 既存 `AEP.lean` から `aep_of_smb_iid` 経由の 2 通り証明、
   audit-2026-05 ベース 4 ペア完結 (Pinsker / Stein / Sanov / ChannelCoding) + AEP の
   i.i.d./stationary ペアで Cover-Thomas 16 章基盤完成

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-13 — 起草 (subagent)

**1. 経路選択**:
- Cover-Thomas 16.8 の標準証明経路 (Algoet-Cover 1988 sandwich argument) を採用。
  Birkhoff 個別エルゴード + Levy's upward theorem の組み合わせで attack。
- 代替経路 (Breiman original / Ornstein-Weiss subsequence) は plumbing 多、却下。

**2. 構造体 (`StationaryProcess` / `ErgodicProcess`) を切る**:
- bare-fields 渡しだと Phase D 主定理の引数列が肥大化 (Ω, μ, α, T, X, hT, hX, hErg
  の 8 引数)。構造体で `p : ErgodicProcess μ α` 1 引数に圧縮。
- ただし Phase A の plumbing 状況で structure 化が重い場合、Phase A 内撤退ラインで
  bare-fields に切り替え。

**3. Mathlib 整備度未確認の段階での見積**:
- 起草時 (Phase 0) Mathlib 整備度: `MeasurePreserving` / `Ergodic` ✅、Levy ✅、
  Birkhoff 個別エルゴード ❌、stationary process ❌、entropy rate ❌。
- (E.2) i.i.d. shift ergodicity の Mathlib 整備度は Phase E 着手時に再確認 (本起草では
  未確認、`Kolmogorov_zero_one_law` の loogle 確認は Phase A 完了後)。
- 本見積 (5〜7 週) は **Phase 0 完了後の暫定値**。Phase C 着手時に Birkhoff 自前の
  実装 detail を再評価し、撤退ラインで本 plan のスコープ縮小判定。

**4. Phase 0 完了後の更新枠 (空白、Phase A 着手時に追記)**:
- Phase A.3 着手時に `IdentDistrib (obs i) (obs 0)` の plumbing 量再評価
- Phase C 着手時に Mathlib `Submartingale.ae_tendsto_limitProcess` の流用度評価
- Phase E 着手時に `Ergodic T (Measure.pi μ_0)` の Mathlib 整備度再確認

**5. 撤退ラインの優先順位**:
1. **Phase C 完 (基盤完成)** で `birkhoff_ergodic_ae` を含む基盤 publish、SMB 主定理は
   仮定受け取り形でも publish 価値 (定常過程の Cover-Thomas 4 章基盤として独立価値)。
2. **Phase D 完 (主定理 a.s.)** = Cover-Thomas 16.8.1 完全形 publish。
3. **Phase E 完 (i.i.d. 特殊化)** = 既存 `AEP.lean` との 2 通り証明統合、audit
   4 ペア完結。

各撤退ラインで proof-log + metrics を取得、Mathlib の薄い箇所 (= Birkhoff 個別エルゴード
a.s. 版の不在) を可視化したという結果自体が公的なデータポイントとして残る。

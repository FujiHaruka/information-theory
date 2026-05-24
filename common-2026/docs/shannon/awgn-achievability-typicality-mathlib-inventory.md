# AWGN Achievability Typicality — Mathlib + Common2026 在庫 master synthesis

> **親 plan**: [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md)
>
> **Status**: Phase 0 完了 (2026-05-24)。判断 #1 / #2 / #3 確定、Phase A 着手 GO。
>
> **per-lemma 詳細データ**: 5 軸別ファイル (合計 2968 行) を参照。本 master は
> cross-axis consistency analysis と判断確定 + trap warning 集約のみ。

## 5 軸別ファイル (per-lemma 構造化 inventory)

| 軸 | スコープ | 行数 | 結論 |
|---|---|---|---|
| [軸 1 codebook 測度](awgn-achievability-typicality-mathlib-inventory-axis1-codebook.md) | `Measure.pi (gaussianReal)`, IndepFun, marginal | 593 | **判断 #2 Option A** (2 段 `Measure.pi`)、T-1 不発動、Mathlib 既存 100% |
| [軸 2 continuous AEP](awgn-achievability-typicality-mathlib-inventory-axis2-aep.md) | n-dim Gaussian SLLN, log composition, continuous AEP | 652 | **判断 #1 T-2 採用** (`IsContinuousAEPGaussian` regularity hyp 化)、AEP 本体 / n-d differentialEntropy / continuous SMB は 🔴 不在 |
| [軸 3 joint density](awgn-achievability-typicality-mathlib-inventory-axis3-density.md) | rnDeriv / differentialEntropy / klDiv | 554 | **判断 #3 Option γ** (`klDiv` 形)、Option β は既存 `audit:suspect(differential-entropy-plan)` 負債継承で却下 |
| [軸 4 expurgation](awgn-achievability-typicality-mathlib-inventory-axis4-expurgation.md) | exists-le-lintegral, worst-half throw away, power bridge | 579 | **T-3 不採用**、Phase D ~50 行 |
| [軸 5 decoder measurability](awgn-achievability-typicality-mathlib-inventory-axis5-decoder.md) | argmin / indicator / Set / `measurable_to_countable'` | 590 | **Option A** (`Classical.choose` + `measurable_to_countable'`)、`argmin` ルートは `ℝ <` non-WellFounded で詰む |

## 確定判断

### 判断 #1 — **T-2 採用** (`IsContinuousAEPGaussian` regularity hyp 化)

**根拠** (Axis 2):

- ✅ Mathlib 既存: `strong_law_ae_real` / `_Lp` (SLLN)、`memLp_id_gaussianReal'` / `variance_fun_id_gaussianReal` (1-d Gaussian moments)、`Filter.Tendsto.log`、`iIndepFun_pi`
- 🔴 Mathlib + Common2026 ともに不在: **continuous AEP 本体** / **n-d differentialEntropy** / **continuous SMB (Shannon-McMillan-Breiman)**
- 規模影響: T-2 不採用ルート → Phase B 単独 ~390 行、Phase A-E 合計 750-810 行で T-4 (plan 2 分割) を高確率発動
- T-2 採用ルート → Phase B ~50 行 (predicate のみ)、achievability core (codebook + union bound + expurgation) は Phase C-D で本物 discharge を維持

**honesty 規律 (Phase B 着手時の必須条件、CLAUDE.md「Mathlib 壁の 4 分類」)**:

- (a) `IsContinuousAEPGaussian P N` の型 ≠ `IsAwgnTypicalityHypothesis` 結論型
- (b) docstring で "Mathlib gap (continuous SMB / n-d differentialEntropy 不在)、NOT load-bearing for achievability core" 明示
- (c) Phase C-D で `IsContinuousAEPGaussian` を仮定の下に codebook + union bound + expurgation を本物 discharge
- (d) 監査タグ `@audit:staged(continuous-aep-gaussian)` を付与 (parallel-gaussian / EPI と同型 staged pattern)

### 判断 #2 — **Option A** (2 段 `Measure.pi`)

**採用形** (Axis 1):

```lean
noncomputable def gaussianCodebook (M n : ℕ) (σ² : ℝ≥0) :
    Measure (Fin M → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σ²))
```

**根拠** (Axis 1):

- `AwgnCode.encoder : Fin M → (Fin n → ℝ)` と型 defeq (`Fin M → Fin n → ℝ`)、追加 instance 不要
- `iIndepFun_pi` (Basic.lean:784) + `measurePreserving_eval` (Pi.lean:407) が 2-3 行で fire
- T-1 (Measure.pi 型クラス壁) 不発動
- T-2 採用ルートでは Phase B で SLLN を使わないため、`strong_law_ae` (Banach 版) の `[BorelSpace E]` 要求 (Axis 2 警告) は無関係 → Axis 1 と Axis 2 の推奨整合

### 判断 #3 — **Option γ** (`klDiv` 形)

**採用形** (Axis 3):

typical set / AEP bound を `klDiv` 形で書く。具体的には:

- joint $(X, Y)$ の typical set を `klDiv (joint^n) (marginal X ⊗ₘ Kernel)` 経由で表現
- `klDiv_compProd_eq_add` (無条件等号) + Common2026 既存 `klDiv_pi_eq_sum` / `klDiv_gaussianReal_gaussianReal_eq` を活用
- `mutualInfo := klDiv (joint) (prod marginal)` の Common2026 既存定義と直結

**根拠** (Axis 3):

- Option α (`rnDeriv` 形): `Measure.pi × Measure.rnDeriv` は loogle **0 declarations** → bridge 大量自作
- Option β (`differentialEntropy` 形): 既存 `jointDifferentialEntropyPi_le_sum` が load-bearing `h_llr_split` (`@audit:suspect(differential-entropy-plan)`) を含む → 負債継承
- **Option γ**: Mathlib + Common2026 既存で完全に乗る、負債を完全に断ち切れる唯一の経路

## Cross-axis consistency analysis (T-2 採用ルート確認)

5 軸の judgments が T-2 採用ルートで全て整合:

| 矛盾候補 | 判定 |
|---|---|
| Axis 1 "raw `Fin n → ℝ` で OK" vs Axis 2 "`EuclideanSpace` flatten 推奨" | Axis 2 推奨は T-2 不採用ルート前提 (Phase B で SLLN 使う場合)。T-2 採用なら Phase B 内 SLLN 不要 → Axis 1 Option A (raw `Fin n → ℝ`) で整合維持。**矛盾なし** |
| Axis 3 Option γ vs `multivariateGaussian` の `PosSemidef` 要件 | T-2 採用で Phase B 内完結により回避可能 (joint $(X, X+N)$ を直接構成しない)。**矛盾なし** |
| Axis 5 `argmin` 不可 vs 親 plan の `argmin_set` 言及 | 親 plan の言及は failure case 仮想、Axis 5 結論で `Classical.choose` + `measurable_to_countable'` ルート確定。**plan 更新で解消** |

## Phase A 着手前 trap warning (重要)

実装 agent (`lean-implementer`) に Phase A 委譲する際の必須前提:

### 軸 1 から

- **`iIndepFun_pi` (Basic.lean:784)** の `[∀ i, IsProbabilityMeasure (μ i)]` がファイルレベル `variable` 継承で signature に現れないが必須。`νₙ` (内側 `Measure.pi`) を prob measure のまま維持必要、もし途中で非正規化版に書き換えると静かに unify failure
- **`pi_map_eval` (Pi.lean:379)** は一般版で `(∏ μ j univ) • μ i` scalar を返す → prob でない測度で projection を取ると trap。**必ず `measurePreserving_eval` (line 407、prob 専用、scalar が消える形) を選ぶ**

### 軸 2 から (T-2 採用で大半は回避だが Axis 1 への波及あり)

- `strong_law_ae` (Banach 版) の `[BorelSpace E]` 要求は Phase A の codebook 型選定に影響しない (T-2 採用で Phase B では使わない)
- ただし将来 T-2 不採用に転換する場合は `EuclideanSpace ℝ (Fin n)` flatten 必須

### 軸 3 から

- `Measure.pi × Measure.rnDeriv` (loogle 0 declarations) → typical set 定義で `rnDeriv` 形を一切使わない。**Option γ (`klDiv` 形) で統一**
- `differentialEntropy_pi` の equality 版は不在、`klDiv_pi_eq_sum` を使う

### 軸 4 から

- **`exists_le_lintegral` (Average.lean:738)** は `AEMeasurable` のみで OK。`exists_le_integral` (Bochner、Average.lean:594) は `Integrable` 要求
- → **Pe を `ℝ≥0∞` 値で定義** することを Phase A 着手時に確定 (Phase D-1 の 1 行 discharge を保証)

### 軸 5 から

- `Function.argmin` は `WellFounded (·<·)` 要求 → `ℝ` の `<` は well-founded ではない、**Mathlib `Measurable.argmin` は不在**
- decoder は **`Fin.find` / `Classical.choose` + `measurable_to_countable'`** で構成、`argmin` ルートは plan の `argmin_set` 言及含めて使えない

## Phase 規模再見積もり (T-2 採用ルート確定後)

| Phase | 計画見積 | 在庫確認後の更新 |
|---|---|---|
| Phase 0 | 0 (MD のみ) | ✅ 完了 |
| Phase A | 80-150 | **100-140 行** (Mathlib 既存 100%、plumbing 中心) |
| Phase B | 50 (T-2 採用) | **50-70 行** (predicate + docstring + audit:staged タグ) |
| Phase C | 100-150 | **100-130 行** (decoder ~20 軽い、union bound 中心) |
| Phase D | 50-80 | **50-60 行** (`exists_le_lintegral` 1-2 行 + worst-half 算術 10 行) |
| Phase E | 30-50 | **30-50 行** |
| skeleton + plumbing | 50-80 | **50-70 行** |
| **合計** | ~360-560 | **~380-520 行** (中央 ~450) |

plan §「規模見積もり」の T-2 採用時下限値内、~500 行中央予測と整合。

## 親 plan 更新差分 (判断ログ + 文言修正)

判断ログ #1 / #2 / #3 / 関連修正は親 plan に append:

- 判断ログ #1: T-2 採用、根拠 = Axis 2 で AEP 本体 / n-d differentialEntropy / continuous SMB 全て不在
- 判断ログ #2: Option A (2 段 `Measure.pi`)、根拠 = Axis 1 で T-1 不発動 + `AwgnCode.encoder` と型 defeq
- 判断ログ #3: Option γ (`klDiv` 形)、根拠 = Axis 3 で Option β 既存負債回避 + Mathlib + Common2026 完全 cover
- Phase C 失敗時 fallback の文言更新: 「`Classical.choice` 使用、measurability 別途 hyp 化」→「`Classical.choose` + `measurable_to_countable'` で genuine discharge」(Axis 5 結論)

## Phase A 着手判定

GO 判定。理由:

1. 3 判断全て確定、cross-axis 整合
2. Mathlib 在庫 100% (Phase A は plumbing 中心、Phase B-D-E も Mathlib + Common2026 既存で乗る)
3. 規模見積 ~450 行 (中央)、plan T-4 (2 分割) 不発動
4. trap warning 5 件は全て identified、Phase A 実装 agent への前提として明示可能
5. honest 維持: T-2 採用は `IsContinuousAEPGaussian` の (a)/(b)/(c)/(d) 4 条件を満たす staged pattern

# Birkhoff 個別エルゴード定理 a.s. 自前実装計画 (E-8'' 経路 A)

> **Status**: 2026-05-16 起草。
> Phase C 撤退ログ (`shannon-mcmillan-breiman-phase-c-plan.md` §11) を受け、**経路 A (backward martingale 自前)** を採用。SMB 主定理仮説なし形への昇格を最終目標とする。

## 1. ゴール

```lean
theorem birkhoff_ergodic_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f (T^[i] ω)) / n)
      atTop (𝓝 (∫ x, f x ∂μ))
```

完成後、`shannon_mcmillan_breiman_of_sandwich` (`ShannonMcMillanBreiman.lean:85`) の 4 仮説を全部供給し SMB を仮定なし形 `shannon_mcmillan_breiman` へ昇格。

## 2. Mathlib 現状調査 (2026-05-16)

### 2.1 既存基盤 (流用可)

| API | パス | 状態 | 役割 |
|---|---|---|---|
| `Ergodic` / `PreErgodic` | `Dynamics/Ergodic/Ergodic.lean:50` | ✅ | エルゴード性定義 |
| `Ergodic.ae_eq_const_of_ae_eq_comp_ae` | `Dynamics/Ergodic/Function.lean:103` | ✅ | **γ 段で決定的** (T-invariant ⟹ a.e. const) |
| `MeasureTheory.condExp` | `MeasureTheory/Function/ConditionalExpectation/Basic.lean:129` | ✅ | 条件期待値 |
| `setIntegral_condExp` | 同上 :223 | ✅ | 定義性 `∫_A f = ∫_A 𝔼[f|m]` |
| `MeasureTheory.Filtration` (Preorder ι) | `Probability/Process/Filtration.lean:50` | ✅ | `ℕᵒᵈ` で型化可 |
| `MeasureTheory.Martingale` (Preorder ι) | `Probability/Martingale/Basic.lean:53` | ✅ | `ι := ℕᵒᵈ` で backward 型化可 |
| `MeasurePreserving.iterate` | `Dynamics/Ergodic/MeasurePreserving.lean` | ✅ | `Stationary.lean` で使用済 |

### 2.2 Mathlib gap (自前要)

| 目的 | 結果 | 影響 |
|---|---|---|
| Backward / reversed martingale convergence | Mathlib 0 件 | β 段の核心、自前要 |
| Antitone filtration の `iInf` σ-algebra | Filtration.lean で `⨅` 未定義 | α/β 段で自前 |
| `Submartingale.ae_tendsto_limitProcess` を `ℕᵒᵈ` で使う | `Upcrossing.lean:221+315` `ℕ` ハードコード | 自前 backward upcrossing 写経要 |
| Birkhoff a.s. 版 | 0 件 (fixed point / mean ergodic のみ) | 本実装の主目標 |
| `condExp` × `MeasurePreserving` 不変性 | 0 件 | γ 段で自前 |
| `strong_law_ae` (i.i.d. 専用) | 完備、ergodic 流用不能 | — |

### 2.3 構造判断

`ι := ℕᵒᵈ` で `Martingale` を借りる路線は型は通るが、Doob upcrossing が `Filtration ℕ` ハードコードのため `ae_tendsto_limitProcess` の再利用不可。自前で書く backward martingale convergence は Mathlib 既存 `Submartingale.ae_tendsto_limitProcess` (Convergence.lean:209) を時刻反転して写経 (~280 行)。

## 3. Lalley 標準証明の Lean 化分解

### (a) Backward filtration `ℋ_n`

`ℋ_n := T⁻ⁿ(ℬ) = MeasurableSpace.comap (T^[n]) ℬ`、antitone in `n`。

### (b) Backward martingale `M_n := 𝔼[f | ℋ_n]`

Petersen *Ergodic Theory* (2.2) Theorem: Birkhoff average `g_n := (1/n) S_n` 自身が `ℕᵒᵈ` 上の reverse martingale で、`g_{n+1} = (n/(n+1)) g_n ∘ T + f/(n+1)`。`f ∘ T^[i]` の `ℋ_n` (n≥i) 条件付期待値は Hopf rearrangement で `g_n` に揃う。

### (c) Ergodicity discharge

`⋂_n ℋ_n` は invariant σ-algebra。`Ergodic.ae_eq_const_of_ae_eq_comp_ae` で `g_∞ =ᵐ const = ∫ f dμ`。

## 4. 実装方針 (3 Phase 分解)

### Phase α: Backward filtration + 基本 API (~80 行)

新規 file: `Common2026/Shannon/BackwardFiltration.lean`

```lean
def backwardFiltration (T : Ω → Ω) (hT : Measurable T) : Filtration ℕᵒᵈ m₀ where
  seq n := MeasurableSpace.comap (T^[OrderDual.ofDual n]) m₀
  mono' := by ...  -- ℕᵒᵈ の Monotone = ℕ 上の Antitone、comap_comp で
  le' := ...

def tailSigma (T : Ω → Ω) (hT : Measurable T) : MeasurableSpace Ω :=
  ⨅ n : ℕ, backwardFiltration hT (OrderDual.toDual n)
```

補題: `backwardFiltration_apply`, `stronglyMeasurable_iff` (factor through `T^[n]`), `tailSigma_invariant`.

### Phase β: Backward martingale convergence (~250-300 行)

新規 file: `Common2026/Shannon/BackwardMartingale.lean`

**判断**: `ℕᵒᵈ` filtration 経路を採用 (Mathlib `Martingale` 定義を `ι := ℕᵒᵈ` で借用、~50 行節約)。

- **β.1** 定義: `Martingale f (ℋ : Filtration ℕᵒᵈ m₀) μ` (Mathlib 既存)。
- **β.2** Backward upcrossing inequality (~80-150 行): `Upcrossing.lean:617+` の reverse 写経。
- **β.3** L¹ 自動有界性 (~30 行): backward martingale 固有、`‖𝔼[f|ℋ_n]‖_1 ≤ ‖f‖_1`。
- **β.4** 主定理 (~80 行):
  ```lean
  theorem BackwardMartingale.ae_tendsto
      [IsProbabilityMeasure μ] {f : ℕᵒᵈ → Ω → ℝ}
      {ℋ : Filtration ℕᵒᵈ m₀} (hf : Martingale f ℋ μ)
      (hf_int : Integrable (f (OrderDual.toDual 0)) μ) :
      ∃ g, StronglyMeasurable[⨅ n, ℋ (OrderDual.toDual n)] g ∧
        ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f (OrderDual.toDual n) ω) atTop (𝓝 (g ω))
  ```

Mathlib gap: なし (全部 Mathlib 内補題で組める)。実装難易度: **高** (backward upcrossing 写経が山場)。

### Phase γ: Birkhoff 主定理 + ergodic discharge (~150-200 行)

新規 file: `Common2026/Shannon/BirkhoffErgodic.lean`

- **γ.1** Birkhoff average が backward martingale (~70 行): Petersen (2.2)。
  - 核心: `(f ∘ T^[i])` の `ℋ_n` (n≥i) 条件付期待値 → Hopf rearrangement で `g_n` に揃う。
  - 補助補題: `condExp_comp_T` (新規、~30 行、`(𝔼[h|comap T m]) ∘ T =ᵐ 𝔼[h ∘ T | m]`)。
- **γ.2** Backward martingale convergence 適用 (~30 行)。
- **γ.3** Ergodic discharge (~40 行): `Ergodic.ae_eq_const_of_ae_eq_comp_ae`。
- **γ.4** 主定理組立て (~30 行)。

Mathlib gap: `condExp_comp_T_lemma` (新規 PR 候補)。

## 5. 規模見積 + Risk

| 部分 | Optimistic | Likely | Pessimistic |
|---|---|---|---|
| α | 60 | 80 | 120 |
| β | 200 | 280 | 400 |
| γ | 120 | 180 | 280 |
| **合計** | **380** | **540** | **800** |

**Risk**:
- 🔴 **高**: β.2 backward upcrossing 写経。Mathlib forward 版 (`Upcrossing.lean` 830 行) の主要 8-10 lemma 移植。
- 🟡 **中**: γ.1 Birkhoff = backward martingale 同型 (Hopf 整列、教科書 5 行が Lean で 50 行)。
- 🟢 **低**: α, γ.3 (既存 Ergodic API hit), γ.4。

**撤退ライン**:

| 段 | 撤退基準 | アクション |
|---|---|---|
| β.2 | 1.5 週超 | β 単独 Mathlib PR 候補化、SMB は仮説形のまま |
| γ.1 | 1 週超 | 経路 B (maximal ergodic) に変更検討、Garsia 経路で β 迂回 |

## 6. 経路比較表

| 経路 | 規模 | Mathlib gap | 単独 PR 価値 | 採否 |
|---|---|---|---|---|
| **A backward martingale (本 plan)** | **380-800** | backward upcrossing | **高** | ✅ |
| B maximal ergodic ineq (Garsia) | 400-600 | Hopf maximal + dynamics 拡張 | 高 | ⏸ 撤退時予備 |
| C 仮説形 SMB | 150-200 | なし | 低 | ⏸ 全撤退 fallback |

採用理由: (1) Mathlib gap が明確で各 Phase が Mathlib PR 化可能、(2) forward 版 `Submartingale.ae_tendsto_limitProcess` の証明が手本、(3) `Ergodic.ae_eq_const_of_ae_eq_comp_ae` が ergodic discharge を 5 行で済ませる **致命的に幸運な hit**。

## 7. 実装 file 構成

```
Common2026/Shannon/
  Stationary.lean                  ← 既存 119 行
  EntropyRate.lean                 ← 既存 498 行
  ShannonMcMillanBreiman.lean      ← 既存 179 行 (sandwich 形)
  BackwardFiltration.lean          ← 新規 Phase α (~80 行)
  BackwardMartingale.lean          ← 新規 Phase β (~280 行)
  BirkhoffErgodic.lean             ← 新規 Phase γ (~180 行)
  ShannonMcMillanBreimanFinal.lean ← 新規 仮定なし形 SMB (~50 行、γ 後)
```

## 8. 判断ログ (2026-05-16 起草)

1. **経路選択**: A (backward martingale)。Phase C plan §11 撤退時に把握されていなかった事実:
   - `Filtration` は `Preorder ι` 一般 ⟹ `ℕᵒᵈ` で即型化
   - `Ergodic.ae_eq_const_of_ae_eq_comp_ae` が ergodic discharge を 5 行
   この 2 つから A が **数学的に最短経路**。
2. **`Filtration ℕᵒᵈ` 借用**: 自前 `BackwardMartingale` 構造体を新規定義せず、Mathlib `Martingale` 定義を `ι := ℕᵒᵈ` で借用 (~10 個の API 工数節約)。
3. **Doob upcrossing**: 写経 (~80-150 行) は本質的に避けられない。**この部分単独で Mathlib PR の価値**。
4. **`condExp_comp_T_lemma`**: Mathlib 不在、独立 PR 候補。
5. **撤退時 publish 戦略**: β 単独 PR、γ 単独 PR、いずれも `共通-2026` スピンオフとして残せる。

## 9. 着手チェックリスト

- [ ] α.1: `BackwardFiltration.lean` 新規、`backwardFiltration` + mono'/le'
- [ ] α.2: `tailSigma` + invariance
- [ ] β.1: `BackwardMartingale.lean` 新規、`Martingale (ι := ℕᵒᵈ)` API 確認
- [ ] β.2: backward upcrossing inequality
- [ ] β.3: L¹ 自動有界
- [ ] β.4: `BackwardMartingale.ae_tendsto` 主定理
- [ ] γ.1: `condExp_comp_T_lemma`
- [ ] γ.2: Birkhoff average = `Martingale (ι := ℕᵒᵈ)`
- [ ] γ.3: backward convergence 適用
- [ ] γ.4: Ergodic discharge
- [ ] γ.5: `birkhoff_ergodic_ae` 主定理
- [ ] 昇格: `shannon_mcmillan_breiman_of_sandwich` → 仮定なし形 `ShannonMcMillanBreimanFinal.lean`

## 10. 参考

- 親 plan: `shannon-mcmillan-breiman-phase-c-plan.md` §11 撤退ログ
- 既存 SMB sandwich: `Common2026/Shannon/ShannonMcMillanBreiman.lean:85`
- Mathlib forward convergence: `Mathlib/Probability/Martingale/Convergence.lean:209`
- Mathlib forward upcrossing: `Mathlib/Probability/Martingale/Upcrossing.lean:617-800`
- Ergodic discharge: `Mathlib/Dynamics/Ergodic/Function.lean:103`
- 数学的参照: Lalley "Stat 313 Lectures", Petersen *Ergodic Theory* (2.2), Durrett *Probability* (4.7)

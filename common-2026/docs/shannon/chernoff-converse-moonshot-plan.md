# Chernoff converse (L-Ch1) discharge ムーンショット計画 🌙 (T1-B follow-up)

> 実態整合 (2026-05-20): **DONE-HONEST-HYPS (per-tilt 縮減形、L-CC2 着地)** — 計画通り完了。
> `InformationTheory/Shannon/ChernoffConverse.lean` (0 sorry) に `chernoffMediator` (:101) +
> `chernoff_rate_isBoundedUnder_le` (:149, internal discharge) + `chernoff_converse_from_per_tilt`
> (:270) + `chernoff_converse_discharged` (:400) + `chernoff_lemma_tendsto_from_per_tilt` (:432) を全 publish。
> `h_per_tilt` は honest な指数下界仮定 (`∃ lam ∈ Icc 0 1, chernoffInfo = -log Z(lam) ∧ ∃ C>0, ∀ᶠ n,
> C·Z^n ≤ 2·bayesErrorMinPmf`、ChernoffConverse.lean:403-407) で `:=True` でも vacuous でもない。
> `h_bdd_le` は internal discharge 済 (hypothesis 2→1)。完全 discharge (Sanov LDP per-tilt 起動で
> `h_per_tilt` を消す) は依然未着手 (別 plan)。**進捗ブロックの Phase 1-6 が全 [ ] のままだが実態は全完了。**

> **Parent**: [`chernoff-moonshot-plan.md`](chernoff-moonshot-plan.md) §撤退ライン L-Ch1 +
> [`chernoff-mathlib-inventory.md`](chernoff-mathlib-inventory.md)
>
> **Status (2026-05-20)**: 着手。親 ChernoffInformation plan は **L-Ch1 退避形**で
> 0 sorry 完了済 (`InformationTheory/Shannon/ChernoffInformation.lean` 241 行)。本 plan は
> その `h_converse` (Phase B converse `limsup rate ≤ chernoffInfo`, Sanov LDP per-tilt 経由)
> を **partial discharge** する。完全 discharge (Mathlib `sanov_ldp_equality` 起動) は
> Cramér L-C2 と同種の `IsProbabilityMeasure (Measure.infinitePi ...)` instance 詰まり
> + ~1000 行案件のため 1 session 不可と判断。
>
> **Goal target (partial discharge 採用)**:
>
> `InformationTheory/Shannon/ChernoffConverse.lean` (~200-300 行) で:
>
> 1. `chernoffMediator P₁ P₂ λ` (tilted pmf `α → ℝ`) + 諸性質
>    (`_sum_eq_one`, `_pos`, `_nonneg`)
> 2. tilted-Z **per-tilt** lower-bound wrapper:
>    > `chernoff_converse_from_per_tilt`
>    > — per-tilt hypothesis `h_per_tilt : ∀ᶠ n in atTop, C * Z(λ)^n ≤ 2 · bayesErrorMinPmf P₁ P₂ n`
>    > から `limsup rate ≤ -log Z(λ)`を導出
> 3. 主定理 `chernoff_converse_discharged`:
>    > 撤退ライン L-Ch1-reduced (per-tilt 形に縮減した hypothesis 一本) から
>    > `limsup rate ≤ chernoffInfo P₁ P₂`
> 4. `chernoff_lemma_tendsto_from_per_tilt` (wrapper):
>    > 親 ChernoffInformation の `chernoff_lemma_tendsto` を **per-tilt 形 hypothesis 一本**
>    > にさらに縮減した形で再 publish (hypothesis count: 2 → 1)
>
> **撤退ライン**: [L-CC1] Phase A scaffolding (chernoffMediator + 性質 4 本) のみ publish して
> Phase B (per-tilt Sanov LDP 起動) は別 plan defer / [L-CC2] per-tilt hypothesis 形へ縮減した
> 最終 wrapper のみ publish (hypothesis 一本残し、`sanov_ldp_equality` 経由完全 discharge は別 plan)。

## 進捗

- [x] Phase 0 — Mathlib + InformationTheory API 在庫再確認 ✅ (既存
  [`chernoff-mathlib-inventory.md`](chernoff-mathlib-inventory.md) + Sanov LDP 出力形式確認)
- [ ] Phase 1 — `ChernoffConverse.lean` skeleton (sorries 4-6 個) 📋
- [ ] Phase 2 — `chernoffMediator` pmf + 性質 ✅ target
- [ ] Phase 3 — `chernoff_converse_from_per_tilt` per-tilt wrapper ✅ target
- [ ] Phase 4 — `chernoff_converse_discharged` 主定理 (per-tilt 縮減形) ✅ target
- [ ] Phase 5 — `chernoff_lemma_tendsto_from_per_tilt` (親 ChernoffInformation wrapper 再 publish) ✅ target
- [ ] Phase 6 — verify + InformationTheory 編入 + roadmap 更新 (judgement log) ✅ target

## ゴール / Approach

### 最終定理 signature

Cover-Thomas Theorem 11.9.1 converse は `limsup rate ≤ chernoffInfo`、これを **per-tilt hypothesis 縮減形**で publish:

```lean
/-- **L-Ch1 partial discharge** (per-tilt 形 hypothesis 縮減):
λ-tilt 毎の Sanov LDP lower bound を hypothesis として取り、
`limsup rate ≤ chernoffInfo` を導出。-/
theorem chernoff_converse_discharged
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_per_tilt : ∃ lam ∈ Set.Icc (0:ℝ) 1,
        chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ᶠ n : ℕ in atTop,
            C * (chernoffZSum P₁ P₂ lam) ^ n ≤ 2 * bayesErrorMinPmf P₁ P₂ n) :
    Filter.limsup
      (fun n : ℕ => -((1:ℝ)/n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop
        ≤ chernoffInfo P₁ P₂
```

### Approach (中核 4 ピース)

#### Phase A scaffolding — tilted pmf `chernoffMediator`

Cover-Thomas (11.9.7): tilted (mediating) pmf

```
chernoffMediator P₁ P₂ λ (a) := P₁(a)^{1-λ} · P₂(a)^λ / Z(λ)
```

を pmf として publish。性質:

- `chernoffMediator_sum_eq_one` (∑ = 1)
- `chernoffMediator_pos` (full support 0 < ...)
- `chernoffMediator_nonneg`

**Mathlib-shape**: `chernoffZSum_pos` (既存) + `Finset.sum_div` で `_sum_eq_one`、
`Real.rpow_pos_of_pos` + `div_pos` で `_pos`。

#### Phase B per-tilt wrapper — `chernoff_converse_from_per_tilt`

Per-tilt hypothesis (Sanov LDP lower bound on bayesErrorMinPmf via tilted distribution):

```
∀ᶠ n in atTop, C · Z(λ)^n ≤ 2 · bayesErrorMinPmf P₁ P₂ n
```

から `limsup rate ≤ -log Z(λ)` を導出。これは pure algebraic:

```
bayesErrorMinPmf ≥ (C/2) · Z(λ)^n
⇒ log bayesErrorMinPmf ≥ log(C/2) + n · log Z(λ)
⇒ -(1/n) log bayesErrorMinPmf ≤ -log(C/2)/n - log Z(λ)
⇒ limsup ≤ -log Z(λ)  (since -log(C/2)/n → 0)
```

`Filter.limsup_le_of_le` (Mathlib) + `IsCoboundedUnder (· ≤ ·)` (achievability + `chernoffInfo_nonneg`
から `IsBoundedUnder (· ≥ ·)` ⇒ cobounded で取れる) で sandwich。

#### Phase C 主定理 — `chernoff_converse_discharged`

`chernoffInfo_attained` (既存) で λ\* を取り、Phase B wrapper を `λ := λ*` で起動して
`limsup rate ≤ -log Z(λ*) = chernoffInfo` を出す。

#### Phase D sandwich Tendsto wrapper — `chernoff_lemma_tendsto_from_per_tilt`

親 `chernoff_lemma_tendsto` (`ChernoffInformation.lean:124`) は 2 hypothesis 要求
(`h_converse` + `h_bdd_le`)。本 plan の主定理が `h_converse` を per-tilt 形へ縮減するので、
**`h_bdd_le` も internal discharge** すれば最終 wrapper が **hypothesis 1 本** (per-tilt) で済む。

- `h_bdd_le` (`IsBoundedUnder (· ≤ ·)`): `chernoff_rate_le_aux_upper` (Chernoff.lean:898) は
  `private` だが、その出力形 `∃ M, ∀ᶠ n, rate n ≤ M` から `IsBoundedUnder (· ≤ ·)` 直接。
  **問題**: `private` なので外部から呼べない。再構築する: bayesErrorMinPmf の lower bound
  `≥ (1/2) · p_min^n` (Chernoff.lean:953 構成) を InformationTheory 内で再現する短い lemma
  `chernoff_rate_isBoundedUnder_le` (~40 行) を本 plan で publish。

これで **`chernoff_lemma_tendsto_from_per_tilt`** は hypothesis 1 本 (per-tilt):

```lean
theorem chernoff_lemma_tendsto_from_per_tilt
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_per_tilt : ∃ lam ∈ Set.Icc (0:ℝ) 1, ...) :
    Tendsto rate atTop (𝓝 (chernoffInfo P₁ P₂))
```

### Approach 図

```
Phase 0  : 在庫確認 (chernoffInfo_attained, bayesErrorMinPmf_pos, chernoffZSum_pos)  ← 完了済
Phase 1  : Skeleton (sorries 4-6 個)                            ← ~0.15 セッション
Phase 2  : chernoffMediator pmf + 性質 4 本                       ← ~0.2 セッション (~80 行)
Phase 3  : chernoff_converse_from_per_tilt (per-tilt wrapper)    ← ~0.25 セッション (~70 行)
Phase 4  : chernoff_converse_discharged (主定理)                  ← ~0.1 セッション (~30 行)
Phase 5  : chernoff_lemma_tendsto_from_per_tilt (再 publish)      ← ~0.15 セッション (~50 行)
            ← chernoff_rate_isBoundedUnder_le internal discharge  ← ~0.15 セッション (~40 行)
Phase 6  : verify + InformationTheory 編入 + roadmap 更新 (~10 行)        ← ~0.05 セッション
```

### 規模見積もり (中央予測 ~250-300 行)

| 自作要素 | 想定行数 | Phase |
|---|---|---|
| `chernoffMediator` 定義 + 3 性質 | ~80 行 | A |
| `chernoff_converse_from_per_tilt` (per-tilt wrapper) | ~70 行 | B |
| `chernoff_converse_discharged` (主定理) | ~30 行 | C |
| `chernoff_rate_isBoundedUnder_le` (internal discharge) | ~40 行 | D pre |
| `chernoff_lemma_tendsto_from_per_tilt` (sandwich wrapper) | ~50 行 | D |
| skeleton + imports + docstring + namespace | ~40 行 | A-E |
| **合計** | **~310 行** | |

撤退ライン L-CC1 (Phase A scaffolding only) なら ~120 行で着地、L-CC2 (per-tilt 形維持で
Phase D 不参) なら ~210 行で着地。

### ファイル構成

```
InformationTheory/Shannon/
  Chernoff.lean                  ← 既存 (1066 行, 0 sorry, 変更なし)
  ChernoffInformation.lean       ← 既存 (241 行, 0 sorry, 変更なし)
  ChernoffConverse.lean          ← 新規 (~250-310 行, 0 sorry, 本 plan の publish 場所)
InformationTheory.lean                  ← `import InformationTheory.Shannon.ChernoffConverse` 追記
docs/shannon/
  chernoff-mathlib-inventory.md  ← 既存 (本 plan の predecessor)
  chernoff-converse-moonshot-plan.md  ← 本ファイル (新規)
```

---

## 撤退ライン

**L-CC1**: Phase A scaffolding (chernoffMediator + 3 性質) のみ publish, Phase B-D は別 plan defer。
着地 ~120 行。撤退判断条件: Phase B の `limsup_le_of_le` 起動で boundedness defaults
(`IsCoboundedUnder (· ≤ ·)`) の internal discharge が ~80 行を超える場合、または
`chernoff_rate_le_aux_upper` の `private` 再構築が `Chernoff.lean` への変更を要求する場合。

**L-CC2**: per-tilt 形 hypothesis 縮減で publish, `sanov_ldp_equality` 経由完全 discharge は別 plan defer。
着地 ~210 行。撤退判断条件: Sanov LDP per-tilt 経路を本 plan で試行して
`IsProbabilityMeasure (Measure.pi (fun _ : Fin n => pmfToMeasure (chernoffMediator ... λ*)))`
instance synthesis で詰まる場合 (Cramer L-C2 と同種、§判断ログ #1)。

**現時点判断**: **L-CC2 採用 (per-tilt 形縮減で publish, 完全 discharge 別 plan)**。

---

## 依存関係

完了済 / 利用可:

- [x] **InformationTheory/Shannon/Chernoff.lean** (1066 行, 0 sorry):
  - `chernoffZSum`, `chernoffZSum_pos`, `chernoffInfo`, `chernoffInfo_attained`,
    `chernoffInfo_nonneg`, `bayesErrorMinPmf`, `bayesErrorMinPmf_pos`,
    `bayesErrorMinPmf_le_half_Z_pow`, `chernoff_lemma_achievability`
- [x] **InformationTheory/Shannon/ChernoffInformation.lean** (241 行, 0 sorry):
  - `chernoff_rate_isBoundedUnder_ge`, `chernoff_lemma_tendsto` (L-Ch1+L-Ch2 hypothesis 形)
- [x] **Mathlib `Filter.limsup_le_of_le`** (`Order/LiminfLimsup.lean:140`)
- [x] **Mathlib `Filter.IsBoundedUnder.isCoboundedUnder_flip`** (cobounded conversion)
- [x] **Mathlib `tendsto_of_le_liminf_of_limsup_le`** (`Topology/Order/LiminfLimsup.lean:306`)
- [x] **Mathlib `Real.rpow_pos_of_pos`** (chernoffMediator positivity 用)

利用なし (defer):

- `InformationTheory/Shannon/SanovLDP.lean` / `SanovLDPEquality.lean` (per-tilt Sanov LDP 完全 discharge
  は L-CC2 撤退で別 plan)
- `pmfToMeasure` bridge (pmf → Measure α、Sanov に渡すのに必要、完全 discharge で要)

---

## 判断ログ

> 書く頻度: Phase 終了時 / 設計変更 / 撤退判定。append-only。

1. **2026-05-20 起草** (本セッション): 親 ChernoffInformation plan §撤退ライン L-Ch1 +
   親 Chernoff.lean §Phase B docstring「`pmfToMeasure` bridge + Sanov LDP per-tilt 起動」
   を受けて本 plan を新規。完全 discharge は Cramér L-C2 と同種の `IsProbabilityMeasure
   (Measure.infinitePi ...)` 詰まり ~1000 行案件 (Cramer LC2 Discharge plan §判断ログ #1 と
   同型の risk) と判定、**partial discharge L-CC2 採用**: per-tilt 形 hypothesis 縮減で
   主定理 `chernoff_converse_discharged` + 親 ChernoffInformation wrapper 再 publish
   `chernoff_lemma_tendsto_from_per_tilt` (hypothesis 2 → 1 削減) を target。
   規模 ~250-310 行、Mathlib gap 想定なし。

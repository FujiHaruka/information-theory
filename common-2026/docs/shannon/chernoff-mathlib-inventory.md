# Chernoff Information (T1-B, sandwich Tendsto) Mathlib + Common2026 inventory

> Source materials: `docs/textbook-roadmap.md` §T1-B (lines 126–133).
> Predecessor inventories: `docs/shannon/chernoff-hoeffding-mathlib-inventory.md`
> (T1-B/D 合同, ~652 行) — 本 inventory はそこから **T1-B 独立 sandwich Tendsto publish** に
> 必要な範囲だけを抽出 + 本セッション固有の項目を追補する。
> Predecessor plan: `docs/shannon/chernoff-hoeffding-moonshot-plan.md` (T1-B/D 合同, archive 化済)。
> Predecessor publish: `Common2026/Shannon/Chernoff.lean` (1066 行, 0 sorry, **achievability side まで完了**, converse defer)。

## 一行サマリ

**T1-B 独立 sandwich Tendsto** (`Tendsto rate (𝓝 chernoffInfo)`) を publish するために必要な API は
`Common2026.Shannon.Chernoff` 既存 publish (Phase A + D + C achievability) に **Mathlib
`tendsto_of_le_liminf_of_limsup_le` 1 本 + hypothesis pass-through (converse + boundedness)** を
追加するだけで完結。自前 plumbing 不要 (`chernoffInfo` / `bayesErrorMinPmf` /
`chernoff_lemma_achievability` を黒箱で再利用)。**撤退ライン L-Ch1〜L-Ch3** は converse side の
論証を hypothesis として外出しする pass-through 設計に対応。**`HoeffdingTradeoff.lean:296`
`hoeffding_tradeoff_with_hypothesis` と同型の sandwich 構造**。

| 数値 | 値 |
|---|---|
| 既存 API カバレッジ (sandwich Tendsto に限る) | **100%** (Mathlib + Common2026 既存 publish) |
| 自作必要な top-level | **1 種** (`chernoff_lemma_tendsto`, sandwich hypothesis pass-through wrapper) |
| 規模見積もり | **~500 行** (撤退ライン L-Ch1+L-Ch2+L-Ch3 全採用形) |
| 撤退ライン発動 (現時点) | **No** (Mathlib gap なし) |

---

## 主定理 (T1-B 独立 sandwich Tendsto 目標形)

教科書 statement (Cover-Thomas 11.9.1):

```
P_e^{(n)} ≐ exp(-n · C(P₁, P₂))
where C(P₁, P₂) := -min_{λ ∈ [0,1]} log ∑_x P₁(x)^{1-λ} · P₂(x)^λ
```

Lean signature (本 plan の publish 目標):

```lean
/-- **Cover-Thomas Theorem 11.9.1** (sandwich Tendsto, hypothesis pass-through form):
the optimal Bayesian error rate `-(1/n) log bayesErrorMinPmf` converges to `chernoffInfo P₁ P₂`,
given (i) achievability `liminf ≥ chernoffInfo` (provided by `Chernoff.chernoff_lemma_achievability`)
and (ii) converse `limsup ≤ chernoffInfo` (deferred hypothesis, expanded in
`chernoff-converse-moonshot-plan.md`).

The boundedness hypotheses bridge `IsBoundedUnder` requirements of
`tendsto_of_le_liminf_of_limsup_le`. -/
theorem chernoff_lemma_tendsto
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_converse : Filter.limsup
        (fun n : ℕ => -((1:ℝ)/n) * Real.log (Chernoff.bayesErrorMinPmf P₁ P₂ n))
        atTop ≤ Chernoff.chernoffInfo P₁ P₂)
    (h_bdd_le : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => -((1:ℝ)/n) * Real.log (Chernoff.bayesErrorMinPmf P₁ P₂ n)))
    (h_bdd_ge : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => -((1:ℝ)/n) * Real.log (Chernoff.bayesErrorMinPmf P₁ P₂ n))) :
    Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (Chernoff.bayesErrorMinPmf P₁ P₂ n))
      atTop (𝓝 (Chernoff.chernoffInfo P₁ P₂))
```

## ファイル構成

```
Common2026/Shannon/
  Chernoff.lean                ← 既存 (1066 行, 変更なし — 黒箱で再利用)
  ChernoffInformation.lean     ← 新規 (sandwich Tendsto publish, ~500 行)
  HoeffdingTradeoff.lean       ← 既存 (sandwich pattern の雛形)
Common2026.lean                ← `import Common2026.Shannon.ChernoffInformation` を追記
docs/shannon/
  chernoff-mathlib-inventory.md      ← 本ファイル (新規)
  chernoff-moonshot-plan.md          ← 新規 (T1-B 独立 plan)
  chernoff-hoeffding-mathlib-inventory.md ← 既存 (T1-B/D 合同, archive 扱い)
  chernoff-hoeffding-moonshot-plan.md ← 既存 (T1-B/D 合同, archive 扱い)
```

---

## A. 既存 Common2026 publish 再利用枠 (黒箱)

| Symbol | file:line | full signature | conclusion (verbatim) |
|---|---|---|---|
| `Chernoff.chernoffZSum` | `Common2026/Shannon/Chernoff.lean:63` | `noncomputable def chernoffZSum (P₁ P₂ : α → ℝ) (lam : ℝ) : ℝ` (`variable [Fintype α] [DecidableEq α]`) | `∑ a : α, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam` |
| `Chernoff.chernoffInfo` | `Common2026/Shannon/Chernoff.lean:69` | `noncomputable def chernoffInfo (P₁ P₂ : α → ℝ) : ℝ` (`variable [Fintype α] [DecidableEq α]`) | `-(sInf ((fun lam : ℝ => Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1))` |
| `Chernoff.chernoffInfo_attained` | `Common2026/Shannon/Chernoff.lean:163` | `theorem chernoffInfo_attained (P₁ P₂ : α → ℝ) [Nonempty α] (hP₁ : ∀ a, 0 < P₁ a) (hP₂ : ∀ a, 0 < P₂ a) : ...` | `∃ lam ∈ Set.Icc (0:ℝ) 1, chernoffInfo P₁ P₂ = -(Real.log (chernoffZSum P₁ P₂ lam))` |
| `Chernoff.chernoffInfo_nonneg` | `Common2026/Shannon/Chernoff.lean:183` | `theorem chernoffInfo_nonneg ...` | `0 ≤ chernoffInfo P₁ P₂` |
| `Chernoff.chernoffInfo_symm` | `Common2026/Shannon/Chernoff.lean:234` | `theorem chernoffInfo_symm (P₁ P₂ : α → ℝ) : ...` | `chernoffInfo P₁ P₂ = chernoffInfo P₂ P₁` (with the standard convention swap) |
| `Chernoff.bayesErrorMinPmf` | `Common2026/Shannon/Chernoff.lean:691` | `noncomputable def bayesErrorMinPmf (P₁ P₂ : α → ℝ) (n : ℕ) : ℝ` (`variable [Fintype α] [DecidableEq α]`) | `(1/2) * ∑ x : Fin n → α, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i))` |
| `Chernoff.bayesErrorMinPmf_pos` | `Common2026/Shannon/Chernoff.lean:807` | `lemma bayesErrorMinPmf_pos (P₁ P₂ : α → ℝ) [Nonempty α] (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (n : ℕ) : ...` | `0 < bayesErrorMinPmf P₁ P₂ n` |
| `Chernoff.bayesErrorMinPmf_le_half_Z_pow` | `Common2026/Shannon/Chernoff.lean:779` | `theorem bayesErrorMinPmf_le_half_Z_pow ... (lam_mem : lam ∈ Set.Icc (0:ℝ) 1) (n : ℕ) : ...` | `bayesErrorMinPmf P₁ P₂ n ≤ (1/2) * chernoffZSum P₁ P₂ lam ^ n` |
| `Chernoff.chernoffZSum_pos` | `Common2026/Shannon/Chernoff.lean:112` | `lemma chernoffZSum_pos (P₁ P₂ : α → ℝ) [Nonempty α] (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (lam : ℝ) : ...` | `0 < chernoffZSum P₁ P₂ lam` |
| `Chernoff.chernoff_achievability` | `Common2026/Shannon/Chernoff.lean:1004` | `theorem chernoff_achievability (P₁ P₂ : α → ℝ) [Nonempty α] (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) : ...` | `chernoffInfo P₁ P₂ ≤ Filter.liminf (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop` |
| `Chernoff.chernoff_lemma_achievability` | `Common2026/Shannon/Chernoff.lean:1059` | (alias of `chernoff_achievability`, same signature) | (alias, same conclusion) |
| `Chernoff.chernoff_rate_ge_chernoffInfo_eventually` | `Common2026/Shannon/Chernoff.lean:883` | `lemma chernoff_rate_ge_chernoffInfo_eventually (P₁ P₂ : α → ℝ) [Nonempty α] (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) : ...` | `∀ᶠ n : ℕ in atTop, -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n) ≥ chernoffInfo P₁ P₂ + Real.log 2 / n` |

注: `Chernoff.chernoff_rate_le_aux_upper` (`Chernoff.lean:898`) は **`private`** で公開されないが、その中身
(uniform upper bound: `∃ M, ∀ᶠ n, rate n ≤ M`) を本 plan 内で再構築可能 (撤退ライン L-Ch2 自前再構築路線)。

---

## B. Mathlib `tendsto_of_le_liminf_of_limsup_le` family

| Symbol | file:line | full signature | conclusion (verbatim) |
|---|---|---|---|
| `tendsto_of_le_liminf_of_limsup_le` | `Mathlib/Topology/Order/LiminfLimsup.lean:306` | `theorem tendsto_of_le_liminf_of_limsup_le {f : Filter β} {u : β → α} {a : α} (hinf : a ≤ liminf u f) (hsup : limsup u f ≤ a) (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) : ...` (`variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]`) | `Tendsto u f (𝓝 a)` |
| `Filter.IsBoundedUnder.isCoboundedUnder_flip` | `Mathlib/Order/Filter/IsBounded.lean` | `theorem Filter.IsBoundedUnder.isCoboundedUnder_flip {f : Filter β} {u : β → α} [...] (h : f.IsBoundedUnder (· ≤ ·) u) : f.IsCoboundedUnder (· ≥ ·) u` (auxiliary) | (auxiliary; used in `Chernoff.lean:1018` to convert `IsBoundedUnder ≤` into the `IsCobounded ≥` needed by `Filter.le_liminf_of_le`) |
| `Filter.IsBoundedUnder` | `Mathlib/Order/Filter/Defs.lean` | `def Filter.IsBoundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) : Prop` | `(f.map u).IsBounded r` |

`tendsto_of_le_liminf_of_limsup_le` の signature が **sandwich Tendsto wrapper にそのまま使える**。
`IsBoundedUnder ≤` と `IsBoundedUnder ≥` の両方が hypothesis (default-supplied tactic `isBoundedDefault`
が `ℝ` filter `atTop` でも明示供給推奨)。

---

## C. 撤退ライン構造表 (L-Ch1 / L-Ch2 / L-Ch3)

| ライン名 | 内容 | hypothesis として外出しする命題 |
|---|---|---|
| **L-Ch1** (converse) | Phase B converse (`limsup ≤ chernoffInfo`, Sanov LDP per-tilt 経由) は hypothesis | `h_converse : Filter.limsup rate atTop ≤ chernoffInfo P₁ P₂` |
| **L-Ch2** (bdd-le) | uniform upper bound (`IsBoundedUnder (· ≤ ·)`) は hypothesis | `h_bdd_le : Filter.IsBoundedUnder (· ≤ ·) atTop rate` |
| **L-Ch3** (bdd-ge) | uniform lower bound (`IsBoundedUnder (· ≥ ·)`) は hypothesis | `h_bdd_ge : Filter.IsBoundedUnder (· ≥ ·) atTop rate` |

注: L-Ch3 (bdd-ge) は achievability (`chernoffInfo ≤ liminf`) + `chernoffInfo_nonneg` から **本セッション内で discharge 可能**
(`liminf ≥ chernoffInfo ≥ 0` ⇒ `IsBoundedUnder (· ≥ ·)`)。L-Ch1 (converse) と L-Ch2 (bdd-le) は hypothesis のまま残す。

具体的に本 plan で discharge する補題:

- `chernoff_rate_isBoundedUnder_ge` — `chernoffInfo_nonneg` + `chernoff_lemma_achievability` から `IsBoundedUnder (· ≥ ·)`
  を導出 (~25 行)
- `chernoff_rate_isBoundedUnder_le_of_pmin` — `chernoff_rate_le_aux_upper` を再構築して
  `IsBoundedUnder (· ≤ ·)` を導出 (~80-120 行、L-Ch2 を内部 discharge する optional 補題)

L-Ch2 を内部 discharge できれば、本 plan の sandwich Tendsto wrapper は **converse hypothesis 1 本のみ**
で publish 可能 (hypothesis count を 3 → 1 に削減)。

---

## D. 副産物候補 (Mathlib PR / 後継 plan)

### 後継 plan 候補

1. **`chernoff-converse-moonshot-plan.md`** (新規) — Phase B converse (rate-side upper bound,
   Sanov LDP per-tilt + tilted LRT) を Sanov LDP per-tilt 経路で discharge。`pmfToMeasure`
   bridge を `HoeffdingTradeoff.lean` から再利用、`sanov_ldp_equality` を `chernoffMediator T_λ*`
   で起動。規模 ~400-600 行。

### Mathlib PR 候補

- 該当なし (`tendsto_of_le_liminf_of_limsup_le` は既存、sandwich Tendsto pattern も標準)。

---

## E. proof-log 主張との突合

- 「Stein/Sanov plumbing から 70-80% 再利用」: 本 plan では **achievability side は再利用済 (`chernoff_lemma_achievability`)**。
  sandwich Tendsto 部分は **既存 publish + Mathlib 1 本** で完結し、自前 plumbing 不要。
- 「~400-600 行 (Chernoff exponent 定義 + 凸性 ~150 + tilted distribution + Sanov 経由 lower bound ~200 + upper bound ~150)」:
  既存 `Chernoff.lean` で **achievability 側 (~400 行) は publish 済**。本 plan の sandwich wrapper は **+~500 行**
  (撤退ライン全採用形: converse pass-through + bdd 構造の整理 + n=0 edge case + docstring) で T1-B Tendsto 形を publish。

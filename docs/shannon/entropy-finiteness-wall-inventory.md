# Entropy-finiteness wall — closure feasibility inventory

> Scope: the 3 `sorry + @residual(wall:entropy-finiteness)` lemmas in
> `InformationTheory/Shannon/EntropyConvFinite.lean` (de Bruijn per-time row, system W).
> Goal: decide the **signature** (do they need a finite-variance hypothesis?) and inventory
> the Mathlib + repo API available for closing them. **Inventory only — no implementation, no plan.**

## ⚠ Orchestrator 訂正 (2026-06-01, 独立 wall re-check) — wall A も `hpX_mom` 必要

下表は wall A を「bare で真」と結論しているが、**これは誤り**。独立反例で否定:
**pX(y) ~ 1/(y·(log y)²)** (large y) は integrable (`∫ 1/(y(log y)²) = [-1/log y] < ∞`、正当な density、heavy-tail) だが、
Gaussian convolution は polynomial-ish tail を保つので `p_t(x) ~ 1/(x(log x)²)`、よって
`negMulLog p_t = p_t·|log p_t| ~ [1/(x(log x)²)]·(2 log x) = 2/(x log x)`、`∫ 1/(x log x) = log log x → ∞` で **発散**。
→ **wall A も bare では偽**。`negMulLog_le_one_sub_self` (= `negMulLog u ≤ 1-u`) は正の部分を pointwise bound するが
`∫(1-p_t)` が ℝ 上で発散するので integrability を与えない (本文の wall-A 根拠の穴)。

**統一された正しい構造**: 3 本すべてに `hpX_mom : Integrable (fun y => y^2 * pX y)` を追加し、**単一の共有 `wall:` 核**
`convDensityAdd_negLog_poly_majorant : -Real.log (p_t x) ≤ A + B·x²` (Jensen: `log p_t(x) = log ∫ pX(y) g_t(x-y) dy
≥ ∫ pX(y) log g_t(x-y) dy = -log√(2πt) - ∫ pX(y)(x-y)²/2t dy`、E[X²]<∞ で `A + B x²`) に帰着させる。
この共有核があれば 3 本とも genuine plumbing で閉じる (A: `|negMulLog p_t| ≤ p_t·(A+Bx²) + 有界部`、`∫ p_t(A+Bx²) = A + B·E[(X+√tZ)²] < ∞`; B/C: それに deriv majorant を掛ける)。
共有核の証明自体は **Jensen for concave log against probability measure `pX dy`** が要 (Mathlib `ConcaveOn.le_map_integral` 系 — 要確認、無ければ核は `wall:` のまま 1 本残す)。

以下の本文は wall-A=bare 前提なので、その部分は上記訂正で上書きされる。B/C の `hpX_mom` + envelope 機械の inventory は有効。

## 一行サマリ

決定的 Mathlib 補題 (`differentialEntropy (conv …)` の有限性) は **不在** (`differentialEntropy` 自体が Mathlib に無く、repo 自前)。3 本のうち wall A (negMulLog) は **bare hyp で真**、wall B/C (log-factor × ∂p_t / ∂²p_t) は **有限分散 `hpX_mom : Integrable (y²·pX)` を追加した方が安全 (結論 B)** — consumer 全段で `hpX_mom` は既に scope 内 (機械的 thread のみ)。残る最小 `wall:` 核は「Gaussian convolution density の log-factor 積分可能性 = differential-entropy finiteness」で、Mathlib PR 候補。

---

## 最重要 question の結論: **(B) `hpX_mom` 追加が安全 (推奨)** — ただし限定付き

| Wall | 現 signature で真か | 推奨 signature |
|---|---|---|
| A `_negMulLog_integrable` (`:95`) | **真 (bare で可)** ※下記根拠 | bare 維持可。ただし B/C と統一して `hpX_mom` 追加でも害なし |
| B `_logFactor_deriv_integrable` (`:72`) | bare では未保証 | **`hpX_mom` 追加** |
| C `_logFactor_deriv2_integrable` (`:50`) | bare では未保証 | **`hpX_mom` 追加** |

### 根拠 (数学的吟味)

被積分関数の構造:
- A: `negMulLog p_t = - p_t · log p_t`。
- B: `(- log p_t - 1) · ∂_x p_t`。
- C: `(- log p_t - 1) · ∂²_x p_t`。

1. **p_t は常に有界 (bare hyp で成立)。** 既存資産 `convDensityAdd_le_prefactor` (Assembly:163, `@audit:ok`):
   `convDensityAdd pX g_s x ≤ (√(2π·s))⁻¹`、かつ `convDensityAdd_pos` (PerTime:784) で `0 < p_t x`。
   よって `0 < p_t ≤ C_t := (√(2πt))⁻¹` 一様。**この上界は `hpX_int + hpX_mass` のみ要求 (有限分散不要)**。
   したがって `log p_t ≤ log C_t` (上から有界)。**`log p_t` の発散は下側 (tail で p_t → 0) でのみ起こる**。

2. **A (negMulLog) は bare で真。** `-p_t log p_t` は上有界 `p_t ≤ C_t` より
   `negMulLog p_t ≤ negMulLog`-的に押さえられ、tail では `p_t·|log p_t|` の質量は
   `∫ p_t = 1` (有限質量) と `negMulLog_le_one_sub_self` (Mathlib, 下記) の組合せで制御可能。
   差分エントロピー `h(X+√t Z) = -∫ negMulLog p_t` は **integrable density (有限質量) かつ有界
   density なら常に有限** (上界 max-entropy `≤ ½log(2πe Var)` は分散∞でも `-∫negMulLog` の
   **有限性**は壊れにくい — 発散するのは値が `+∞` 側、ここで欲しいのは integrable=可積分性で、
   `p_t ≤ C_t` 有界 + `∫p_t=1` で `∫ p_t|log p_t| < ∞` は heavy-tail でも成り立つ。
   反例を作るには `p_t` が `0` 近傍に質量を溜めつつ `log` が積分不能なほど暴れる必要があるが、
   `p_t` は Gaussian convolution で `C^∞`・下側 Gaussian-tail を持つため `∫ p_t|log p_t|` は収束)。
   → **wall A の bare signature は honest。`hpX_mom` 不要**。

3. **B/C は ∂p_t / ∂²p_t を掛けるので別物。** `∂²_x p_t` の tail 挙動は
   既存 envelope 機械 `convKernel_envelope_integrable` (Assembly:784) + `gaussHessMaj` (`:477`) が
   **`hpX_mom = Integrable(y²·pX)` を使って** `∂²p_t` の可積分 majorant を作っている
   (`_chain_domination`:1196, `_chain_hdiff`:2121 が現に `hpX_mom` を消費)。
   `(- log p_t - 1)` 因子は上有界 (`log p_t ≤ log C_t`) だが下側 `|log p_t|` が tail で増大するため、
   `|log p_t| · |∂²p_t|` の積分可能性には `∂²p_t` 側の tail 減衰 (= envelope 機械, `hpX_mom` 依存) が要る。
   → **heavy-tail pX (分散∞, Cauchy 等) では `∂²p_t` の poly-moment majorant が作れず B/C は危うい**。
   `hpX_mom` は **regularity precondition (有限分散)** であり load-bearing core ではない
   (de Bruijn / Fisher の結論を hyp に bundle していない、結論は concrete integrand の `Integrable`)。

**結論 (B)**: B/C に `hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume` を追加。A は bare 維持可だが
3 本統一のため追加しても honesty 上問題なし (precondition の追加は禁止事項に当たらない)。

### consumer 整合性 (rg + Read 確認済)

EntropyConvFinite 3 本を呼ぶのは `FisherInfoV2DeBruijnAssembly.lean` のみ:

| 呼出箇所 | 呼ぶ wall | 呼出元 theorem | 呼出元に `hpX_mom` 有? |
|---|---|---|---|
| `:1973` | C `_deriv2` | `_chain_ibp_fisher_ibp_step` (`:1930`) | **無** (hpX_nn/meas/int/mass のみ) |
| `:1978` | B `_deriv` | 同上 (`:1930`) | **無** |
| `:2432` | A `_negMulLog` | `_chain_parametric` (`:2399`) | **有** (`:2402`) |

→ A の呼出元は `hpX_mom` 保持済。B/C の呼出元 `_ibp_step` (`:1930`) と中継 `_ibp_fisher` (`:2043`) は
`hpX_mom` を **持っていない**。ただし最終呼出元 `_chain_parametric` (`:2399`, `hpX_mom` 保持) → `_ibp_fisher`
(`:2503`) は `hpX_mom` を scope に持ちながら現状 thread していない (`pX hpX_nn hpX_meas hpX_int hpX_mass ht`
のみ渡す)。**よって B/C に `hpX_mom` を追加する場合、`_ibp_step` と `_ibp_fisher` の signature に
`hpX_mom` を 1 引数追加し、`:2503` の呼出に `hpX_mom` を 1 個追加するだけ** (全箇所で scope 内、機械的)。
top-level assembled theorem群 (`:1202/:1325/:2124/:2402/:2539`) は既に `hpX_mom` 保持。

---

## 主定理の最終形 (3 本, 推奨 signature)

```lean
-- wall A (bare 維持可)
theorem convDensityAdd_negMulLog_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume

-- wall B / C (hpX_mom 追加推奨)
theorem convDensityAdd_logFactor_deriv_integrable      -- (deriv2 版は deriv→deriv(deriv))
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)   -- ★ 追加
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x) volume
```

証明戦略 (pseudo-Lean, B/C 共通骨格):

```
set p_t := convDensityAdd pX (gaussianPDFReal 0 ⟨t,ht.le⟩)
have hub  : ∀ x, p_t x ≤ C_t           := convDensityAdd_le_prefactor …   -- log p_t ≤ log C_t
have hpos : ∀ x, 0 < p_t x             := convDensityAdd_pos …            -- log p_t well-def
have henv : Integrable (∂²-envelope)   := convKernel_envelope_integrable … (hpX_mom)  -- Assembly:784/1216
-- domination: |(-log p_t -1)·∂²p_t| ≤ (A + B·|log p_t|)·envelope ; |log p_t| ≤ A'+B'·x² tail
exact Integrable.mono' henv … (a.e. bound via hub + Gaussian-tail of p_t)   -- ★ wall 残核
```

---

## API 在庫テーブル

### A. 差分エントロピー / 有限性 (Mathlib 不在の核)

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| `differentialEntropy` (測度版) | — | — | ❌ **Mathlib 不在** (loogle: `unknown identifier 'MeasureTheory.differentialEntropy'`) | repo 自前 `InformationTheory/Shannon/DifferentialEntropy.lean` のみ。Mathlib に有限性補題無し |
| `differentialEntropy (conv …)` 有限性 | — | — | ❌ **不在** (`wall:entropy-finiteness` の本体) | 自作核。PR 候補 |
| max-entropy bound `h ≤ ½log(2πe Var)` | — | — | ❌ 不在 | 本 wall では使わない (可積分性が目的, 値上界でない) |

### B. negMulLog の正値性・有界性・連続性 (Mathlib 完備)

| 概念 | Mathlib API (完全 namespace) | file:line | signature / 結論 verbatim |
|---|---|---|---|
| 連続性 | `Real.continuous_negMulLog` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean` | `Continuous negMulLog` (loogle Found one) |
| 零点 | `Real.negMulLog_zero` | `…/NegMulLog.lean:170` | `@[simp] lemma negMulLog_zero : negMulLog (0 : ℝ) = 0` |
| 零点 | `Real.negMulLog_one` | `…/NegMulLog.lean:172` | `@[simp] lemma negMulLog_one : negMulLog (1 : ℝ) = 0` |
| 非負 | `Real.negMulLog_nonneg` | `…/NegMulLog.lean:174` | `lemma negMulLog_nonneg {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ negMulLog x` |
| 上界 (growth) | `Real.negMulLog_le_one_sub_self` | `…/NegMulLog.lean:234` | `lemma negMulLog_le_one_sub_self {x : ℝ} (h0 : 0 ≤ x) : x.negMulLog ≤ 1 - x` (verbatim, tail 質量制御に有用) |
| 上界 strict | `Real.negMulLog_lt_one_sub_self` | `…/NegMulLog.lean` | 同上 strict |
| 凹性 | `Real.concaveOn_negMulLog` | `…/NegMulLog.lean:227` | `ConcaveOn ℝ (Set.Ici 0) negMulLog` (Fano inventory 既出) |

注: `negMulLog_zero = 0` verbatim 確認済 (`negMulLog 0 = 0`、tail で `p_t→0` でも被積分関数は 0 に連続)。

### C. Gaussian-tail / モーメント積分 (Mathlib + repo, B/C の majorant 部品)

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| `gaussianPDFReal` 定義 | `ProbabilityTheory.gaussianPDFReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:48` | ✅ | `(√(2πv))⁻¹ · rexp(-(x-μ)²/(2v))` verbatim |
| `x^k·exp(-bx²)` 可積分 | `integrable_rpow_mul_exp_neg_mul_sq` | Mathlib (repo:Assembly:128 で利用済) | ✅ | `(hb : 0<b) (hk : -1<k) → Integrable (x ↦ x^k·exp(-b·x²))` (Gaussian moment) |
| `exp(-bx²)` 可積分 | `integrable_exp_neg_mul_sq` | Mathlib (Assembly:550 利用) | ✅ | base Gaussian |
| 分散加法 | `ProbabilityTheory.variance_add` | `Mathlib/Probability/Moments/Variance.lean` | ✅ (loogle Found) | `Var(X+Y)` (独立時 `Var X + Var Y`) — 参考のみ、本 wall では直接不要 |
| Gaussian の任意モーメント有限 | `…gaussianReal` `MemLp id p` 系 | `…/Gaussian/Real.lean` (loogle: `MemLp id p (gaussianReal μ v)`) | ✅ | √t·Z 側の分散有限 (B/C で陰に使用) |

### D. repo 内資産 (在庫として記録 — B/C の主要部品)

| 補題 | file:line | 状態 | signature 要点 | B/C での役割 |
|---|---|---|---|---|
| `convDensityAdd` 定義 | `EPIConvDensity.lean:40` | — | `fun z => ∫ x, pX x * pY (z-x) ∂volume` | p_t の定義 |
| `convDensityAdd_le_prefactor` | `Assembly:163` | ✅ `@audit:ok` | `(hpX_nn)(hpX_int)(hpX_mass:∫pX=1)(hs:0<s) → p_s x ≤ (√(2π·s))⁻¹` | **`log p_t` 上界 = log C_t** (bare hyp) |
| `convDensityAdd_pos` | `PerTime:784` | ✅ | `(hpX_nn)(hpX_int)(hpX_mass:0<∫pX)(hs:0<s) → 0 < p_s x` | `log p_t` well-def |
| `convKernel_envelope_integrable` | `Assembly:784` | ✅ (proof-done) | `(pX K)(hpX_int)(hpX_meas)(hK_int)(hK_meas) → Integrable (x ↦ ∫ y, pX y·K(x-y))` | **∂p_t / ∂²p_t の envelope 可積分性 (kernel K = Gaussian deriv)** |
| `gaussHessMaj` / `gaussHessMaj_integrable` | `Assembly:477 / :545` | ✅ | `Integrable (gaussHessMaj t)` (Gaussian × quadratic) | ∂²p_t の majorant kernel |
| `integrable_natPow_mul_exp_neg_mul_sq` | `Assembly:123` | ✅ | `(hb:0<b)(k:ℕ) → Integrable (x ↦ x^k·exp(-b·x²))` (ℕ-pow bridge) | poly-moment majorant |
| `convDensityAdd_fisher_integrable` | `Assembly:1561` | ✅ (0 sorry, **bare hyp**) | `(hpX_nn)(hpX_meas)(hpX_int)(ht) → Integrable ((logDeriv p_t)²·p_t)` | **兄弟 wall 解決済**: Fisher integrand は bare で可積分 (Stam 経由) |
| `convDensityAdd_hasDerivAt_self` | `Assembly:1636` | ✅ | `→ HasDerivAt p_t (deriv p_t x) x` | ∂p_t 存在 |
| `convDensityAdd_deriv_hasDerivAt_self` | `Assembly:1748` | ✅ | `→ HasDerivAt (deriv p_t) (deriv(deriv p_t) x) x` | ∂²p_t 存在 |
| `_chain_domination` | `Assembly:1196` | ✅ (`hpX_mom` 消費) | `(…hpX_mom…) → ∃ bound, Integrable bound ∧ a.e. ∂²-bound` | **`hpX_mom`-依存 envelope の前例** |

### E. 兄弟 wall (同系統)

| wall | lemma | file:line | 状態 |
|---|---|---|---|
| `wall:fisher-finiteness` | `gaussianConv_fisher_le_inv_var` | `FisherConvBound.lean:68` | `sorry + @residual(wall:fisher-finiteness)` — `J(p_t) ≤ 1/s` (Stam 壁) |

注: `convDensityAdd_fisher_integrable` (Fisher integrand 可積分) は `gaussianConv_fisher_le_inv_var` 経由で
**0 sorry 達成済**。entropy-finiteness wall (log-factor) は Fisher 壁とは別核 (score 側でなく entropy 側)。

---

## 主要前提条件ボックス

- **`convDensityAdd_le_prefactor`** (`log p_t` 上界の源): 要 `hpX_nn` / `hpX_int` / `hpX_mass : ∫pX=1`
  (有限分散**不要**)。→ A の bare 可、B/C の `log` 因子上界も bare。
- **`convKernel_envelope_integrable`** (∂²p_t envelope): 要 kernel `K` の `Integrable + Measurable`。
  K に poly-moment kernel (`y²·…`) を入れる版は **`hpX_mom`** が `pX` 側に必要 (`_chain_domination` の前例)。
- **`integrable_rpow_mul_exp_neg_mul_sq`**: `(hb : 0 < b)` + `(hk : -1 < k)` — 後者は `rpow` 指数の下限制約。
  ℕ 乗は `integrable_natPow_mul_exp_neg_mul_sq` (repo bridge) で吸収済。
- **`ConcaveOn.le_map_integral`** (もし値上界を使うなら): `[IsProbabilityMeasure μ]` + `ContinuousOn` +
  `IsClosed` + a.e. domain + `Integrable f` / `Integrable (g∘f)`。**本 wall では不使用** (可積分性が目的)。

---

## 自作が必要な要素 (優先度順)

1. **(最優先) `(- log p_t - 1)·∂²p_t` の domination 補題 (= wall C)。**
   推奨: `convKernel_envelope_integrable` で得る `∂²p_t` の Gaussian-tail majorant `M(x)` と、
   `|log p_t x| ≤ A + B·x²` (← p_t の下側 Gaussian-tail; `hpX_mom` 依存) を組み、
   `|(- log p_t -1)·∂²p_t| ≤ (A+1+B·x²)·M(x)` を a.e. で立て `Integrable.mono'`。
   工数: 中 (~80-120 行)。落とし穴: **`|log p_t x| ≤ A + B·x²` の Gaussian-tail 下界**が真の残核 (下記 wall)。
2. **wall B (∂p_t 版)**: C と同型、kernel を `gaussHessMaj` → Gaussian 1st-deriv majorant に差替えるのみ。
   C の補助補題を共有可能。
3. **wall A (negMulLog)**: bare で `p_t ≤ C_t` 有界 + `∫p_t=1` + `negMulLog_le_one_sub_self` で
   `∫ p_t|log p_t| < ∞`。tail は p_t→0 で `negMulLog→0` (連続)。最も軽い (~40-60 行)。
4. **共有補助補題 (3 本横断)**: (i) `0 < p_t x ∧ p_t x ≤ C_t` (既存 2 補題の合成)、
   (ii) **`|log (p_t x)| ≤ A_t + B_t·x²`** (Gaussian-tail 下界 → log 上界)。これが B/C の心臓部、
   wall A には不要。(ii) を 1 本切り出せば B/C が薄くなる。

---

## Mathlib 壁の列挙 (`@residual(wall:entropy-finiteness)` 対象)

真に Mathlib 不在で残る最小核:

1. **`differentialEntropy (Gaussian convolution density) < ∞`** = 「Gaussian convolution density の
   log-factor 積分可能性」。loogle 確認:
   - `MeasureTheory.differentialEntropy` → `unknown identifier` (**Mathlib 不在**, repo 自前のみ)
   - `Integrable (fun _ => Real.negMulLog _)` (conv 形) → Mathlib に該当宣言なし (`integrable_rnDeriv_mul_log_iff`
     = KL 形のみ、off-target)
2. **`|log (convDensityAdd pX g_t x)| ≤ A + B·x²`** (p_t の下側 Gaussian-tail から来る log 上界) —
   Mathlib に convolution density の pointwise log 下界補題は無い。これが B/C 共有の真の残核。

→ **shared sorry 補題化推奨**: 上記 (2) を 1 本の補助補題に集約し、B/C がそれを呼ぶ形。
A はそれ無しで閉じるので別。`docs/audit/audit-tags.md`「共有 Mathlib 壁」パターン。
現状 3 本が同一 `wall:entropy-finiteness` slug で正しく分類済 (兄弟 `wall:fisher-finiteness` と語彙分離済)。

---

## 撤退ラインへの距離

親計画 (de Bruijn per-time row, system W) の撤退ラインへの抵触: **発動しない見込み**。

- de Bruijn 同定の数学的本筋 (IBP + Fisher = `½J(p_t)`) は `_ibp_step` / `_chain_ibp_fisher` で既に組上済。
  本 wall は **integrability precondition** であり、撤退ライン (定理の数学的内容の縮退) には触れない。
- 縮退案 (もし B/C が `hpX_mom` でも閉じない場合): pX を **compact-support** に制限する版を新規撤退ラインに。
  compact-support なら p_t は厳密 Gaussian-tail を持ち log 上界が容易。ただし これは family 全体の
  `hpX_mom` 路線より強い制約なので **最後の砦** (撤退口は sorry + `@residual`、仮説束化は禁止)。

---

## 着手 skeleton (signature 確定版)

```lean
import InformationTheory.Shannon.EPIConvDensity
-- 既存資産は同一 family file 群 (Assembly / PerTime / FisherConvBound) に存在。
-- shared 補助補題を本 file に置くか Assembly に置くかは実装判断。

namespace InformationTheory.Shannon.EntropyConvFinite

open MeasureTheory Real ProbabilityTheory
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)

-- wall A: bare 維持 (signature 変更なし)
theorem convDensityAdd_negMulLog_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume := by
  sorry -- @residual(wall:entropy-finiteness)

-- wall B: hpX_mom 追加
theorem convDensityAdd_logFactor_deriv_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x) volume := by
  sorry -- @residual(wall:entropy-finiteness)

-- wall C: hpX_mom 追加 (deriv(deriv …) 版)
theorem convDensityAdd_logFactor_deriv2_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x) volume := by
  sorry -- @residual(wall:entropy-finiteness)

end InformationTheory.Shannon.EntropyConvFinite
```

**consumer 側で要る付随変更** (B/C に `hpX_mom` を足した場合): `Assembly:1930 _ibp_step` と
`:2043 _ibp_fisher` の signature に `hpX_mom` を 1 引数追加、`:2070` / `:2503` の呼出に `hpX_mom` を渡す。
全箇所で `hpX_mom` は scope 内 (最終呼出元 `_chain_parametric` が保持)。

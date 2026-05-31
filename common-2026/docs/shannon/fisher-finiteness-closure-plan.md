# Shannon EPI: `wall:fisher-finiteness` closure 計画

> **Parent**: per-time de Bruijn line (`FisherInfoV2DeBruijnAssembly.lean`).
> 関連 wall register: `docs/audit/audit-tags.md:70` (`fisher-finiteness`)。
> 隣接 plan: `epi-debruijn-pertime-closure` (IBP step / tsupport)、`stam`/`stam-step2-density` walls (semantic 区別あり、後述)。

<!--
記法は moonshot/subplan template と同じ:
- 状態絵文字 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更
- 廃止 step は ~~取り消し線~~
- 判断ログ append-only
-->

## 進捗

- [ ] M0 在庫調査 (本計画起草で大半完了、下記「M0 確定事項」参照) 🚧
- [ ] R-A skeleton: shared sorry 補題 `gaussianConv_fisher_le_inv_var` を立てる 📋
- [ ] R-A Step 1: 凸 Fisher 上界 `J(p_t) ≤ λ²J(pX) + (1-λ)²·(1/t)` を density-level で確立 📋
- [ ] R-A Step 2: λ→0 極限で `J(p_t) ≤ 1/t` を取り出す 📋
- [ ] R-A Step 3: `J(p_t) < ∞ → Integrable ((logDeriv p_t)²·p_t)` を `fisherInfoOfDensity` 有限性から復元 📋
- [ ] R-A wire-up: `convDensityAdd_fisher_integrable` 本体を shared 補題呼出に置換 📋
- [ ] proof-log: yes (`docs/shannon/proof-log-fisher-finiteness.md`)

## 対象 wall (context)

### 現状

`Common2026/Shannon/FisherInfoV2DeBruijnAssembly.lean:177-182` の private theorem:

```lean
private theorem convDensityAdd_fisher_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => (logDeriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x)^2
      * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) volume := by
  sorry -- @residual(wall:fisher-finiteness)
```

数学的内容: 畳み込み密度 `p_t = pX ∗ g_t` (g_t = `gaussianPDFReal 0 ⟨t, ht.le⟩`, **分散 t**) の被積分関数
`(logDeriv p_t)² · p_t` が Lebesgue 可積分。積分値は `∫ (logDeriv p_t)²·p_t = J(p_t) = J(X+√t·Z)`。
真命題 (Stam/Blachman の score-of-convolution 単調性): 任意確率密度 pX で
`J(X+√t·Z) ≤ J(√t·Z) = J(𝒩(0,t)) = 1/t < ∞`。Cauchy 等の重い裾でも有限。

### 分類根拠 (`wall:` であって `plan:` でない理由 — M0 で再確認済)

- **Mathlib gap (verbatim 確認)**: loogle (`.lake/build/loogle.index`):
  - `"Fisher"` (name 検索) → **Found 0 declarations**。
  - `"Blachman"` (name 検索) → **Found 0 declarations**。
  - `"score"` (name 検索) → 132 件すべて無関係 (`Nat.toDigitsCore` 等の string/parser、Fisher score なし)。
  - `HasDerivAt (MeasureTheory.convolution _ _ _ _)` → Found 2、いずれも `HasCompactSupport.hasDerivAt_convolution_{right,left}` で **compact support 前提**。g_t は compact support でないので Mathlib convolution-微分 API は直接適用不可。
  → Mathlib に Fisher 情報そのものが存在せず、畳み込み Fisher bound も皆無。
- **repo Stam 機械は predicate pass-through のみ (verbatim 確認)**: `EPIStamInequalityBody.lean` /
  `EPIStamStep3Body.lean` の `IsStamScoreConvolution` / `IsStamCauchySchwarz` / `IsStamInequalityHyp`
  はいずれも **load-bearing predicate を仮説に取る** wrapper (Step 1-4 の核を仮説 bundle)。
  `J(X+Z) ≤ J(Z)` を density-level で genuine に証明している補題は **repo に存在しない**。
  唯一 genuine な Fisher-convolution 不等式は `StamGaussianBound.lean:77`
  `stam_convex_fisher_bound_gaussian` だが、これは **両被加数とも Gaussian** の instance であり
  一般 pX には使えない (後述、ただし R-A の上界 step に部分流用できる)。
- したがって closure は same-family closure plan ではなく **self-written 補題セット (PR 級)** を要する
  → `wall:` 分類は正しい。本計画は「その PR の最小補題セットと撤退ラインを確定する」もの。

**重要 (orchestrator への報告)**: 調査の結果「実は repo に genuine bound が既に在る」「plan 1 つで閉じる」は
**否定された**。wall 分類は誤りでない。ただし `StamGaussianBound` の凸 Fisher 上界算術 (`stam_fisher_arith`)
と V2 Gaussian 閉形 `J(𝒩(0,t))=1/t` が **building block として再利用可能**で、PR は完全 from-scratch ではない。

### 数値 verbatim 確認 (CLAUDE.md「具体的数値・型予測」)

- **`g_t` の分散 = t** (t² でない): `FisherInfoV2DeBruijnAssembly.lean` 全体が `gaussianPDFReal 0 ⟨t, ht.le⟩`
  を `⟨t, _⟩ : ℝ≥0` の分散として使い、`FisherInfoV2DeBruijn.lean:100`
  `fisherInfoOfMeasureV2_gaussianReal m {v} (hv : v ≠ 0) : fisherInfoOfMeasureV2 (gaussianReal m v) (gaussianPDFReal m v) = ENNReal.ofReal (1/(v:ℝ))`
  で分散 `v` の Gaussian の Fisher が `1/v`。よって noise の Fisher = `J(𝒩(0,t)) = 1/t`。
- **境界値 `1/t`**: `FisherInfoV2DeBruijn.lean:109` `fisherInfoOfMeasureV2Real_gaussianReal ... = 1/(v:ℝ)`
  (Real 形)。`v = t`, `t > 0` なので `1/t` は有限・正。退化 case (`t = 0`) は仮説 `ht : 0 < t` で排除済、
  退化境界処理は不要。
- **`fisherInfoOfDensity` は `ℝ≥0∞`**: `FisherInfoV2.lean:89`
  `fisherInfoOfDensity f := ∫⁻ x, ENNReal.ofReal ((logDeriv f x)^2) * ENNReal.ofReal (f x) ∂volume`。
  「有限性」は `fisherInfoOfDensity p_t < ∞` (= `≠ ⊤`) として `ℝ≥0∞` で述べるのが自然 (R-A Step 3 で活用)。

## Approach (解の全体形)

ゴール: `convDensityAdd_fisher_integrable` の `sorry` を genuine 化する。
2 つのルート候補を比較し、**(A) Stam 凸 Fisher 上界経由**を推奨、(B) 直接裾評価を撤退ラインとする。

### 推奨ルート (A): Stam 凸 Fisher 上界 → 有限性 → 可積分性

3 段:

1. **凸 Fisher 上界 (density-level)**: 任意 λ∈[0,1] で
   `fisherInfoOfDensity p_t ≤ ENNReal.ofReal (λ²·J(pX) + (1-λ)²·(1/t))`
   を立てる。これが本 PR の **真の核 (genuine Mathlib gap)**。Step 1 の score-of-convolution
   Cauchy-Schwarz が density 上で必要 (repo の `IsStamScoreConvolution`/`IsStamCauchySchwarz`
   predicate が仮説 bundle していた中身を、ここで density-level に genuine 化する)。
2. **λ 最適化 / λ→0 極限**: pX が重い裾 (`J(pX) = ∞`) でも成立させるため、`λ → 0` を取って
   `fisherInfoOfDensity p_t ≤ ENNReal.ofReal (1/t)` を得る。`λ=0` 代入だと `0·∞` の不定形
   (pX 側 `J(pX)=∞`) に当たるため、`λ→0⁺` の極限 / 不等式の右連続性で処理する。
   有限 `J(pX)` の場合は `stam_fisher_arith` の λ 最適化 (`λ* = J(pX)⁻¹/(J(pX)⁻¹+t)`) でも可。
3. **有限性 → 可積分性**: `fisherInfoOfDensity p_t = ∫⁻ ofReal((logDeriv p_t)²) · ofReal(p_t) < ∞`
   から、被積分関数 `(logDeriv p_t)²·p_t ≥ 0` (a.e.) の `Integrable` を
   `MeasureTheory.integrable_iff_lintegral_ofReal_lt_top` 系で復元する。これは純 measure-theory
   plumbing (Mathlib 既存)。

利点: Step 1 の Cauchy-Schwarz 核を 1 度 density-level で証明すれば、repo の predicate pass-through
(`stam`/`stam-step2-density`) も将来 genuine 化できる方向性と整合。`stam_fisher_arith` (算術核) と
V2 Gaussian 閉形を再利用でき、from-scratch でない。

欠点: Step 1 (score-of-convolution の条件付き Cauchy-Schwarz を density 上で) が PR の最重量部。
これは `stam-step2-density` wall (audit-tags.md:57) の核そのもの。本 wall closure が
`stam-step2-density` の上流を巻き込む可能性 → **撤退ライン**: Step 1 が当該 PR で重すぎる場合、
Step 1 を `@residual(wall:stam-step2-density)` の shared sorry 補題に逃がし、本 wall の補題は
「Step 1 を仮定 (regularity でなく core なので NG) ではなく」**Step 2-3 plumbing のみ genuine 化** ……
ではなく (それは load-bearing になる)、**本 wall 全体を `stam-step2-density` 経由の shared sorry**
として残し、本 wall の `@residual` を `wall:stam-step2-density` に **再分類**する (下記「撤退ライン」)。

### 撤退ライン (A): self-written PR が当該セッションで完遂できない場合

- **第一撤退**: shared sorry 補題 `gaussianConv_fisher_le_inv_var` (下記) を立て、その body を
  `sorry` + `@residual(wall:fisher-finiteness)` のまま残す (= 現状の集約形を 1 段精緻化しただけ)。
  `convDensityAdd_fisher_integrable` は Step 3 の plumbing (有限性→可積分性) を genuine 化し、
  「有限性」だけを shared 補題から受ける。**注意**: 「有限性」は core (load-bearing) なので、
  これを `convDensityAdd_fisher_integrable` の **仮説に bundle してはならない**。shared sorry 補題
  `gaussianConv_fisher_le_inv_var` (regularity 引数のみ、結論 = 有限上界) として **別補題に集約**し、
  `convDensityAdd_fisher_integrable` の body 内で **呼び出す** (仮説でなく lemma call)。
  これにより consumer 側 (`convDensityAdd_fisher_integrable`) の Step 3 plumbing は genuine、
  壁は shared 補題 1 件に局所化される (audit-tags.md「共有 Mathlib 壁」パターン)。
- **第二撤退 (再分類)**: Step 1 が `stam-step2-density` の核と完全一致と判明したら、shared 補題の
  `@residual` を `@residual(wall:fisher-finiteness)` から `@residual(wall:stam-step2-density)`
  へ書換える (divergence 防止: 同じ density-level Cauchy-Schwarz 核が 2 wall 名で重複しないように)。
  この判定は Step 1 着手時に行う (判断ログに記録)。

### 比較ルート (B): 直接裾評価 (Stam 非経由)

`(∂_x p_t)²/p_t` を直接 x→±∞ で評価し integrability を示す。Gaussian smoothing で
`logDeriv p_t (x) → -x/t` (大 x で Gaussian score 支配)、`(logDeriv p_t)²·p_t ~ (x/t)²·p_t`、
`p_t` は Gaussian 裾で `≤ C·exp(-x²/(2t·(1+ε)))` 程度に減衰 → `x²·(Gaussian 裾)` は可積分。

- 利点: Stam 凸不等式 (Step 1 の条件付き Cauchy-Schwarz) を回避、measure-theory + tail 評価のみ。
- 欠点: `logDeriv p_t (x) → -x/t` の漸近を pX の裾に一様でない形で出すのが厄介
  (重い裾 pX で `p_t` の裾が pX 支配になり Gaussian 裾より重くなる領域の扱い)。
  実際には `J(p_t) ≤ 1/t` (ルート A の結論) は B では出ず、有限性だけが目標になるが、その有限性証明も
  pX 裾依存の評価を要し、**ルート A の `J(p_t)≤1/t` のほうが pX に一様で clean**。
- 判定: **B は撤退用 backup**。A の Step 1 が `stam-step2-density` 巻き込みで重すぎ、かつ
  Step 1 を shared sorry に逃がすのも望ましくない場合のみ B を検討。ただし B も PR 級なので
  通常は A の第一撤退 (shared sorry 補題) を選ぶ。

### 全体結論

**推奨 = ルート A**。最小成果は「shared sorry 補題 `gaussianConv_fisher_le_inv_var` を立て、
`convDensityAdd_fisher_integrable` の Step 3 plumbing を genuine 化、壁を 1 補題に局所化」
(= 第一撤退ライン)。完全 closure は A Step 1 (density-level score Cauchy-Schwarz) の self-written PR。

## Phase 詳細 (per-step + 必要補題)

### R-A skeleton: shared sorry 補題を立てる

新規 shared sorry 補題 (集約先、`FisherInfoV2DeBruijnAssembly.lean` 内 or 新 file
`Common2026/Shannon/FisherConvBound.lean`):

```lean
/-- Gaussian 畳み込み密度の Fisher 有限上界 `J(pX ∗ g_t) ≤ 1/t`。
任意確率密度 pX (重い裾含む) で成立。Stam convolution Fisher monotonicity。
@residual(wall:fisher-finiteness) -/
theorem gaussianConv_fisher_le_inv_var
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      ≤ ENNReal.ofReal (1 / t) := by
  sorry -- @residual(wall:fisher-finiteness)
```

- 引数は **regularity precondition のみ** (`hpX_nn`/`hpX_meas`/`hpX_int`/`ht`)。結論 `≤ 1/t` が core。
  load-bearing hypothesis なし (honesty OK)。
- 結論型を `fisherInfoOfDensity ... ≤ ENNReal.ofReal (1/t)` (`ℝ≥0∞`) にしたのは、`fisherInfoOfDensity`
  が `ℝ≥0∞` 値 (`FisherInfoV2.lean:89`) で、有限性 (`< ⊤`) を `≤ ofReal(1/t) < ⊤` から直に出すため
  (CLAUDE.md「Mathlib-shape-driven Definitions」: Step 3 の consumer 補題が欲しい結論形に合わせる)。

### R-A Step 1: 凸 Fisher 上界 (density-level) — PR の核

目標 (shared 補題 body 内 or 補助補題):
`fisherInfoOfDensity p_t ≤ ENNReal.ofReal (lam^2 * J(pX) + (1-lam)^2 * (1/t))` (任意 lam∈[0,1])。

必要 building block (verbatim):

- **score-of-convolution 表現** (repo, `@audit:ok`):
  `Common2026/Shannon/EPIConvDensity.lean:113`
  ```
  theorem convDensityAdd_logDeriv
      (pX pY : ℝ → ℝ) (z₀ : ℝ) {s : Set ℝ} {bound : ℝ → ℝ}
      (hs : s ∈ nhds z₀)
      (hF_meas : ∀ᶠ z in nhds z₀, AEStronglyMeasurable (fun x => pX x * pY (z - x)) volume)
      (hF_int : Integrable (fun x => pX x * pY (z₀ - x)) volume)
      (hF'_meas : AEStronglyMeasurable (fun x => convDensityAddDeriv pX pY z₀ x) volume)
      (h_bound : ∀ᵐ x ∂volume, ∀ z ∈ s, ‖convDensityAddDeriv pX pY z x‖ ≤ bound x)
      (bound_integrable : Integrable bound volume)
      (h_diff : ∀ᵐ x ∂volume, ∀ z ∈ s, HasDerivAt (fun z => pX x * pY (z - x)) (convDensityAddDeriv pX pY z x) z) :
      logDeriv (convDensityAdd pX pY) z₀ = (∫ x, convDensityAddDeriv pX pY z₀ x ∂volume) / convDensityAdd pX pY z₀
  ```
  これで `logDeriv p_t (z) = (∫ pX x · g_t'(z-x)) / p_t(z)` を得る (Blachman 接続点)。
- **算術核** (repo): `Common2026/Shannon/StamGaussianBound.lean:58`
  ```
  theorem stam_fisher_arith (a b lam : ℝ) (ha : 0 < a) (hb : 0 < b) (hlo : 0 ≤ lam) (hhi : lam ≤ 1) :
      1 / (a + b) ≤ lam ^ 2 / a + (1 - lam) ^ 2 / b
  ```
  `a = J(pX)⁻¹` 形へ持っていく際の凸不等式算術 (有限 J(pX) case)。
- **詰まる箇所**: score の条件付き Cauchy-Schwarz
  `s_{p_t}(z)² ≤ E[(λ s_X + (1-λ) s_g)² | X+√tZ = z]` を density-level (条件付き期待値を
  `∫ pX x · g_t(z-x) (...) / p_t(z)` の形で) で書き下し、`p_t` に対し積分して
  `J(p_t) ≤ λ²J(X)+(1-λ)²J(noise)` を出す部分。**Mathlib に score-of-convolution の
  condExp 表現も Fisher info 畳み込みも無い** (audit-tags.md:57 `stam-step2-density` の (a)+(b) 混合壁)。
  → ここが本 wall の self-written 核。この sorry を `gaussianConv_fisher_le_inv_var` の body に残すなら
  `@residual(wall:fisher-finiteness)`、`stam-step2-density` と同一核と確定したら再分類
  (Approach「撤退ライン (A) 第二撤退」)。

### R-A Step 2: λ→0 で `J(p_t) ≤ 1/t`

- 重い裾 (`J(pX)=∞`) でも `1/t` を出すため `λ → 0⁺` の極限。
  `fun lam => ENNReal.ofReal (lam^2·J(pX) + (1-lam)^2·(1/t))` は `lam→0` で `ENNReal.ofReal (1/t)` に収束
  (`J(pX)=∞` でも `lam²·∞` を ℝ≥0∞ で扱う; `lam=0` 直接代入は `0·∞` 不定形なので極限 or 右連続性で)。
- 有限 `J(pX)` の場合は `stam_fisher_arith` の λ 最適化 (`stam_convex_fisher_bound_gaussian` の
  証明構造 `StamGaussianBound.lean:86-98` を density 一般へ移植) で `J(p_t) ≤ J(pX)·(1/t)/(J(pX)+1/t) ≤ 1/t`。
- 必要 Mathlib: `ENNReal.ofReal` の単調性 / 極限補題 (`ENNReal.tendsto_ofReal`,
  `le_of_tendsto`)。loogle で個別確認 (PR 着手時)。

### R-A Step 3: 有限性 → 可積分性 (純 plumbing, Mathlib 既存)

`convDensityAdd_fisher_integrable` の body をこれで genuine 化:

```lean
private theorem convDensityAdd_fisher_integrable ... := by
  -- p_t ≥ 0
  have hp_nn : ∀ x, 0 ≤ convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x := fun x =>
    integral_nonneg fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  -- 被積分関数 ≥ 0 (a.e.)
  -- fisherInfoOfDensity p_t = ∫⁻ ofReal((logDeriv p_t)²)·ofReal(p_t) ≤ ofReal(1/t) < ⊤
  have hfin : fisherInfoOfDensity (convDensityAdd ...) < ⊤ :=
    lt_of_le_of_lt (gaussianConv_fisher_le_inv_var pX hpX_nn hpX_meas hpX_int ht) (by simp [...])
  -- ∫⁻ ofReal(g) < ⊤ ∧ g ≥ 0 ∧ AEMeasurable g → Integrable g
  sorry  -- ← plumbing, NOT a wall: Mathlib integrable_iff_lintegral 系
```

- `fisherInfoOfDensity` unfold は `FisherInfoV2.lean:89` のとおり
  `∫⁻ ofReal((logDeriv p_t x)²) * ofReal(p_t x)`。被積分関数の `ENNReal.ofReal` 一体化は
  `fisher_from_logDeriv` (`FisherInfoV2DeBruijnPerTime.lean:721`, `@audit:ok`) が使う
  `← ENNReal.ofReal_mul (sq_nonneg _)` と同手 → `∫⁻ ofReal((logDeriv p_t)²·p_t)`。
- 有限性 → Integrable: Mathlib `MeasureTheory.integrable_iff_lintegral_ofReal_lt_top` 系
  (`∫⁻ ofReal f < ⊤ ∧ f ≥0 ∧ AEMeasurable f → Integrable f`)。**PR 着手時 loogle で正確な名前確認**
  (`integrable_iff` / `Integrable` + `lintegral` + `ofReal` パターン)。AEMeasurable は
  `logDeriv p_t` の可測性 (= `deriv p_t / p_t`、`convDensityAdd_hasDerivAt` 経由) と
  `convDensityAdd` の可測性から。
- **この Step 3 が genuine plumbing**: 壁は Step 1-2 (= shared 補題 `gaussianConv_fisher_le_inv_var`)
  に局所化され、`convDensityAdd_fisher_integrable` 自身は **0 sorry / 壁呼出のみ** にできる
  (audit-tags.md「共有 Mathlib 壁」: consumer は proof done、壁 file だけ未完)。
  → これが第一撤退ラインの **最小成果物** (type-check done、壁 1 件局所化)。

### R-A wire-up

- `convDensityAdd_fisher_integrable` の body を Step 3 の形に置換。
- `gaussianConv_fisher_le_inv_var` を新規追加 (同 file `FisherInfoV2DeBruijnAssembly.lean` 上部、
  または新 file `FisherConvBound.lean` + `Common2026.lean` import 1 行)。
- 既存 docstring (`:146-176`) の wall 説明・honesty audit note は維持 (壁 slug 不変)。
- **独立 honesty audit 必須** (CLAUDE.md「Independent honesty audit」): 新規 shared sorry 補題追加 +
  既存 declaration の body 変更で起動条件該当。`gaussianConv_fisher_le_inv_var` が
  load-bearing でない (regularity 引数のみ) こと、`convDensityAdd_fisher_integrable` が壁呼出を
  仮説 bundle でなく lemma call で受けていることを fresh auditor が確認。

## PR 級判定 (最小 self-written 補題セット)

真の Mathlib gap は **R-A Step 1 (density-level score-of-convolution Cauchy-Schwarz → 凸 Fisher 上界)**。
最小補題セット (signature、`[...]` 込み):

1. `gaussianConv_fisher_le_inv_var (pX) (hpX_nn) (hpX_meas) (hpX_int) {t} (ht : 0 < t) : fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨t,ht.le⟩)) ≤ ENNReal.ofReal (1/t)`
   — 壁集約点 (`@residual(wall:fisher-finiteness)`)。型クラス前提なし (すべて explicit hyp)。
2. (Step 1 内部補助) `convScore_condCauchySchwarz` 系 — score `s_{p_t}(z)²` の条件付き Cauchy-Schwarz
   density 形。これが `stam-step2-density` 核と同一なら shared 補題化 + 再分類。
3. (Step 2 内部補助) λ最適化 / λ→0 極限補題 — `stam_fisher_arith` の density 一般化版。

repo 既存で再利用 (新規不要):
- `convDensityAdd_logDeriv` / `convDensityAdd_hasDerivAt` (`EPIConvDensity.lean:86,113`, `@audit:ok`)
- `stam_fisher_arith` (`StamGaussianBound.lean:58`)
- `fisherInfoOfMeasureV2{Real}_gaussianReal` (`FisherInfoV2DeBruijn.lean:100,109`) = noise の `1/t`
- `gaussianPDFReal_nonneg` / `integrable_gaussianPDFReal` / `differentiable_gaussianPDFReal` /
  `deriv_gaussianPDFReal` / `logDeriv_gaussianPDFReal` (Mathlib + `FisherInfoGaussian.lean`)
- `fisher_from_logDeriv` (`FisherInfoV2DeBruijnPerTime.lean:721`, `@audit:ok`) — 有限性↔可積分性 round-trip の手本

Mathlib plumbing (Step 3、新規証明だが gap でない):
- `integrable_iff_lintegral_ofReal_lt_top` 系 (正確名 PR 時 loogle)
- `ENNReal.ofReal_mul` / `ENNReal.toReal_ofReal` / `lintegral` 単調性

## 残不確実性

1. **Step 1 と `stam-step2-density` の核重複度**: density-level score Cauchy-Schwarz が
   audit-tags.md:57 `stam-step2-density` 壁の核とどこまで一致するか、Step 1 着手時に判定。
   一致なら shared 補題 1 件で 2 wall を閉じられ (再分類)、別物なら本 wall 独自の補助が要る。
   → これが PR スコープ (1 補題 vs 2-3 補題) を左右する最大の不確実性。
2. **λ→0 極限の ℝ≥0∞ 取り扱い**: `J(pX)=∞` (Cauchy 等) で `0·∞` 不定形を ℝ≥0∞ 上で極限/右連続性の
   どちらで処理するのが Mathlib で軽いか未確定 (`ENNReal.tendsto_ofReal` の前提)。PR 時に loogle。
3. **Step 3 plumbing の正確な Mathlib 名**: `integrable_iff_lintegral_ofReal_lt_top` の存在・正確名は
   未確定 (本計画では存在前提)。不在なら `MeasureTheory.Integrable` 定義 + `hasFiniteIntegral_iff`
   経由で自前構成 (それでも gap でなく plumbing)。
4. **AEMeasurable `logDeriv p_t`**: `deriv p_t / p_t` の可測性。`convDensityAdd_hasDerivAt` は
   点ごとの regularity 仮説を要するため、全 x での `Measurable (logDeriv p_t)` を出すのに
   追加の domination/measurability 補題が要る可能性 (Step 3 内)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-31, 計画起草) wall 分類は正しい (誤分類でない) と M0 で確定**: loogle `"Fisher"`/`"Blachman"`
   = Found 0、repo Stam 機械 (`EPIStam*`) は predicate pass-through のみ、genuine `J(X+Z)≤J(Z)` 補題は
   repo 不在。`StamGaussianBound.stam_convex_fisher_bound_gaussian` は両被加数 Gaussian instance で
   一般 pX 不可。→ self-written PR 必要、`wall:` 妥当。ただし `stam_fisher_arith` (算術核) +
   V2 Gaussian 閉形 `J(𝒩(0,t))=1/t` は building block 再利用可、完全 from-scratch でない。
2. **(2026-05-31) 推奨 = ルート A (Stam 凸 Fisher 上界経由)**、B (直接裾評価) は backup。
   理由: A の `J(p_t)≤1/t` が pX に一様で clean、B は重い裾 pX で `p_t` 裾が pX 支配になり
   tail 評価が pX 依存で煩雑。第一撤退 = shared sorry 補題 `gaussianConv_fisher_le_inv_var` 局所化 +
   Step 3 plumbing genuine 化 (consumer proof done、壁 1 件)。
3. **(2026-05-31) 結論型を `fisherInfoOfDensity ... ≤ ENNReal.ofReal (1/t)` (ℝ≥0∞) に設計**:
   `fisherInfoOfDensity` が `ℝ≥0∞` 値 (`FisherInfoV2.lean:89`)、有限性 `< ⊤` を `≤ ofReal(1/t)` から
   直接出すため (Mathlib-shape-driven)。`g_t` 分散 = t (t² でない)、noise Fisher = `1/t` を
   `fisherInfoOfMeasureV2_gaussianReal` で verbatim 確認済 (退化 case は `ht : 0<t` で排除、処理不要)。

# EPI case-1 `wall:blachman-general-density` 独立再確認 inventory

> 独立壁再確認 (read-only)。対象: EPI 無条件化 moonshot case-1 (両 a.c. = 古典 EPI) が
> `wall:blachman-general-density` で block されているという判定の過大評価チェック。
> 親計画: `docs/shannon/epi-csiszar-ratio-reframe-plan.md` 事実 3(b) / 真の残壁 (2)。

## 一行サマリ (verdict 先出し)

**壁は genuine ではない。FALSE WALL。** 「一般 density 用 `IsBlachmanConvReady` producer は in-house 不在
(rg/loogle Found 0)」という親計画の判定 (`epi-csiszar-ratio-reframe-plan.md:93, 113`) は**実コードと矛盾**する。
一般密度 producer `isBlachmanConvReady_convDensityAdd_gaussian` が
`InformationTheory/Shannon/EPIBlachmanGeneralDensity.lean:224` に**既に存在し、19/19 field genuine、
`lake env lean` clean、`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)** で
machine 確認済み。核心仮説 (path 密度 = 任意密度 ⊛ Gaussian なので Gaussian 平滑から全 field 出る) は
**正しく、しかも既に実装されている**。

- 既存率: `IsBlachmanConvReady (convDensityAdd pX g_t) (convDensityAdd pY g_t)` の 19/19 field = **100% 既存・genuine**
- 自作必要: **0 件** (`IsBlachmanConvReady` 供給に限れば)
- 撤退ライン発動: **no** (むしろ撤退の前提が消える)
- 最も危険な発見: 親計画の `wall:blachman-general-density` は false wall。これに基づく case-1 park / `@residual(wall:blachman-general-density)` 計画は誤った前提に立っている。**残る真の gap は供給ではなく consumer 配線 + `IndepFun path_X path_Y` の under-hyp 側**。

---

## §1 `IsBlachmanConvReady` 全 19-field 表

定義: `InformationTheory/Shannon/EPIBlachmanDensity.lean:712-761` (`structure IsBlachmanConvReady (fX fY : ℝ → ℝ) : Prop`)。

各 field の右端「conv-with-Gaussian (= 任意密度 ⊛ Gaussian) から出るか」を判定。
`fX := convDensityAdd pX g_t`, `fY := convDensityAdd pY g_t`, `g_t = gaussianPDFReal 0 ⟨t, ht.le⟩`, `t > 0`。

| # | field | 要求内容 (verbatim型) | smoothness/integ/pos 分類 | Gaussian 平滑から出るか | 供給 lemma (file:line) |
|---|---|---|---|---|---|
| 1 | `int_fX` | `Integrable fX volume` | integrability | ✅ | `convDensityAdd_gaussian_integrable` (`EPIBlachmanGeneralDensity.lean:140`) |
| 2 | `int_fY` | `Integrable fY volume` | integrability | ✅ | 同上 (pY) |
| 3 | `bdd_fX` | `∃ M, ∀ w, \|fX w\| ≤ M` | boundedness | ✅ (Gaussian sup × ∫pX) | `convDensityAdd_gaussian_bdd` (`:114`) |
| 4 | `bdd_fX'` | `∃ M, ∀ w, \|deriv fX w\| ≤ M` | boundedness of deriv | ✅ (deriv fX = pX ⊛ deriv g_t, bounded) | `convDensityAdd_gaussian_deriv_bdd` (`:156`) |
| 5 | `bdd_fY` | `∃ M, ∀ w, \|fY w\| ≤ M` | boundedness | ✅ | `convDensityAdd_gaussian_bdd` (pY) |
| 6 | `bdd_fY'` | `∃ M, ∀ w, \|deriv fY w\| ≤ M` | boundedness of deriv | ✅ | `convDensityAdd_gaussian_deriv_bdd` (pY) |
| 7 | `pos_pZ` | `∀ z, 0 < convDensityAdd fX fY z` | positivity (conv-of-conv) | ✅ (fX,fY 連続 strictly pos → conv pos) | `convDensityAdd_pos_of_pos_cont` (`:191`) + `isRegularDensityV2_convDensityAdd_gaussian` |
| 8 | `int_X` | `∀ z, Integrable (fun x => deriv fX x * fY (z-x))` | per-z integ (int × bdd) | ✅ | inline (`:252`) `Integrable.bdd_mul` |
| 9 | `int_Y` | `∀ z, Integrable (fun x => fX x * deriv fY (z-x))` | per-z integ | ✅ | inline (`:262`) `Integrable.mul_bdd` |
| 10 | `cond_int` | `∀ z, Integrable (condDensityX fX fY z)` | per-z integ (/pZ) | ✅ | inline (`:271`) |
| 11 | `int_W` | `∀ lam∈[0,1] z, Integrable (scoreWeight·condDensityX)` | per-(lam,z) integ | ✅ (logDeriv f·f = deriv f cancellation) | inline (`:285`) |
| 12 | `int_Wsq` | `∀ lam∈[0,1] z, Integrable (scoreWeight²·condDensityX)` | per-(lam,z) integ | ✅ (3-term (a+b)² 展開) | inline (`:327`) |
| 13 | `int_inner` | `∀ lam∈[0,1], Integrable (z ↦ (∫…)·pZ)` | per-lam integ (Tonelli marginal) | ✅ (`Integrable.integral_prod_left`) | inline (`:379`) |
| 14 | `int_fisherX` | `Integrable ((logDeriv fX)²·fX)` | Fisher integrand finite | ✅ (J(p_t) ≤ 1/t < ⊤) | `convDensityAdd_fisher_integrand_integrable` (`:68`) |
| 15 | `int_fisherY` | `Integrable ((logDeriv fY)²·fY)` | Fisher integrand finite | ✅ | 同上 (pY) |
| 16 | `int_fisherZ` | `Integrable ((logDeriv (convDensityAdd fX fY))²·convDensityAdd fX fY)` | Fisher integrand of conv-of-conv | ✅ (4-fold interchange → conv with g_{2t}) | inline (`:507`) + `convDensityAdd_convGaussian_interchange` |
| 17 | `int_prod1` | `Integrable (uncurry (z,x)↦(logDeriv fX x)²·fX x·fY(z-x)) (volume.prod volume)` | 2D Tonelli prod-integ | ✅ (shear `measurePreserving_prod_sub_swap`) | inline (`:529`) |
| 18 | `int_prod2` | `Integrable (uncurry (z,x)↦(logDeriv fY(z-x))²·fX x·fY(z-x)) (vol.prod vol)` | 2D Tonelli prod-integ | ✅ (shear) | inline (`:540`) |
| 19 | `int_prod3` | `Integrable (uncurry (z,x)↦ logDeriv fX x·fX x·(logDeriv fY(z-x)·fY(z-x))) (vol.prod vol)` | 2D Tonelli cross prod-integ | ✅ (shear, deriv fX/deriv fY 分離) | inline (`:551`) |

**全 19/19 が Gaussian 平滑 (= conv-with-Gaussian) から genuine に出る。**「出ない field」は **存在しない**。

key reduction (file docstring `:29-31`): `fX > 0` (strictly, via `isRegularDensityV2_convDensityAdd_gaussian.pos`) で
`logDeriv fX · fX = deriv fX` が成立し、linear-score field が integrable·bounded 積に、Fisher field が
shift/shear copy に落ちる。

---

## §2 producer の供給機構 (Gaussian 平滑が何を効かせているか)

### §2.1 一般密度 producer (本命、壁を打ち砕く lemma)

`isBlachmanConvReady_convDensityAdd_gaussian`
(`InformationTheory/Shannon/EPIBlachmanGeneralDensity.lean:224-568`)

```
theorem isBlachmanConvReady_convDensityAdd_gaussian (pX pY : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX) (hpX_int : Integrable pX volume)
    (hpX_mass : 0 < ∫ x, pX x ∂volume) (hpX_norm : (∫ x, pX x ∂volume) = 1)
    (hpY_nn : ∀ x, 0 ≤ pY x) (hpY_meas : Measurable pY) (hpY_int : Integrable pY volume)
    (hpY_mass : 0 < ∫ x, pY x ∂volume) (hpY_norm : (∫ x, pY x ∂volume) = 1) :
    IsBlachmanConvReady
      (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      (convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩))
```

- `[...]` 型クラス前提: **無し** (ℝ→ℝ 関数 + `ℝ≥0` の standard、暗黙の `MeasurableSpace ℝ` 等は Mathlib default)。
- 引数前提 (explicit) は全て **input 密度 pX/pY 側の regularity** (nonneg / Measurable / Integrable / `0 < mass` / `mass = 1`)。conv 後の fX/fY に直接前提を課していない。**StandardBorel / Countable 系の隠れ前提は無い** (実 signature 確認済み)。
- 結論形 verbatim: 上記 `IsBlachmanConvReady (convDensityAdd pX g_t) (convDensityAdd pY g_t)`。これが case-1 で必要な path 密度の形そのもの。

機械検証 (本 inventory 著者が verbatim 実行):
- `lake env lean InformationTheory/Shannon/EPIBlachmanGeneralDensity.lean` → **silent (0 errors, 0 sorry warnings)**
- `#print axioms isBlachmanConvReady_convDensityAdd_gaussian` → `[propext, Classical.choice, Quot.sound]` (**sorryAx-free, transitive**)
- ファイルは `InformationTheory.lean:234` に import 済み (= ライブラリ正規メンバ)。
- git: `b3b0356` "19/19 genuine" → `84ecb97` "@audit:ok on (4) producer ... int_fisherZ genuine" で独立 honesty 監査も完了済み。

### §2.2 Gaussian 平滑が効く 3 つの分析資産 (Gaussian の性質をどう使うか)

| 資産 | file:line | Gaussian の何を使うか |
|---|---|---|
| `isRegularDensityV2_convDensityAdd_gaussian` | `EPIConvDensityRegular.lean:202` | g_t が C¹ + bounded + bounded deriv + ∫deriv=0 + tail→0。これで conv の `diff`/`pos`/`tail`/`integrable_deriv`/`integral_deriv=0` を任意 pX に伝播。`pos` は `convDensityAdd_pos` (正質量 ⇒ strictly pos)。**滑らかさは差分の下では g_t 側のみが担保** (差分を gateway `convDensityAdd_hasDerivAt_of_regular` 経由で pX に被せる) |
| `gaussianConv_fisher_le_inv_var` | `FisherConvBound.lean:405` | J(p_t = pX ⊛ g_t) ≤ 1/t < ⊤ (Fisher info 有限性)。これで `int_fisherX/Y/Z` の積分可能性が `lintegral_ofReal_ne_top_iff_integrable` 経由で出る |
| `convDensityAdd_convGaussian_interchange` | `EPIConvDensityAssoc.lean:199` | (pX⊛g_t)⊛(pY⊛g_t) = (pX⊛pY)⊛g_{2t} (畳み込み結合律 + 分散倍化 g_t⊛g_t=g_{2t})。conv-of-conv を再び conv-with-Gaussian (分散 2t) に帰着し `int_fisherZ` を閉じる |

### §2.3 既存 Gaussian-only producer (親計画が「唯一」と誤認したもの)

`isBlachmanConvReady_gaussianPDFReal`
(`EPIBlachmanGaussianWitness.lean:344`):
```
theorem isBlachmanConvReady_gaussianPDFReal
    {mX mY : ℝ} {vX vY : ℝ≥0} (hvX : vX ≠ 0) (hvY : vY ≠ 0) :
    IsBlachmanConvReady (gaussianPDFReal mX vX) (gaussianPDFReal mY vY)
```
これは確かに**両 factor が Gaussian PDF 限定**。親計画はこれを「唯一の producer」と判定したが、§2.1 の一般版を見落としている。

---

## §3 Mathlib 在庫 (convolution smoothness / Gaussian Schwartz / moment) — structured per-lemma

核心問いの傍証として Mathlib 側を loogle 確認。結論: **Mathlib 側の汎用 convolution-smoothness は使えないが、in-house の parametric-integral route が既にこれを迂回完了している** (下記)。

### §3.1 convolution smoothness (Mathlib) — 全て HasCompactSupport 要求 (Gaussian 不適合)

loogle `MeasureTheory.convolution, ContDiff` → **Found 6 declarations**、全て `HasCompactSupport.*`:

- `HasCompactSupport.contDiff_convolution_right` (`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`)
- `HasCompactSupport.contDiff_convolution_left` (同)
- `HasCompactSupport.hasDerivAt_convolution_right` / `_left` (同)
- `HasCompactSupport.hasFDerivAt_convolution_right` / `_left` (同)

`[...]` 前提に `HasCompactSupport g` を含む。Gaussian heat kernel は compact support でないので **直接適用不可**。`EPIConvDensity.lean:18-26` docstring が明記する通り、in-house は `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`Mathlib/Analysis/Calculus/ParametricIntegral.lean:289`) でこの壁を**既に迂回**している (gateway `convDensityAdd_hasDerivAt`, `EPIConvDensity.lean:88`, `@audit:ok`)。

### §3.2 Gaussian Schwartz / ContDiff (Mathlib) — 直接の橋渡し不在

- loogle `ProbabilityTheory.gaussianPDFReal, ContDiff` → **Found 0 declarations**
- loogle `ProbabilityTheory.gaussianPDFReal, SchwartzMap` → **Found 0 declarations**
- loogle `SchwartzMap, MeasureTheory.convolution` → Found 2 (`SchwartzMap.convolution_apply`, `SchwartzMap.fourier_convolution_apply`, `Mathlib/Analysis/Fourier/Convolution.lean`) — Schwartz の convolution-apply はあるが `gaussianPDFReal` と Schwartz の橋渡し lemma が無いため接続不能。

**含意**: 「Mathlib に density ⊛ gaussian は smooth がある」ルートは Found 0 で**取れない**。だが in-house は smoothness を C∞ 一括では証明せず、**必要な階数 (1階 deriv + bounded)** だけを parametric-integral で供給して用が足りている (§3.3)。`IsBlachmanConvReady` は C∞ を要求せず、`deriv` (1階) + bounded + integrability しか要求しない (§1 全 field は 1階どまり)。

### §3.3 in-house smoothness 供給 (Mathlib 汎用の代替、実在 verbatim)

- `differentiable_gaussianPDFReal (m : ℝ) (v : ℝ≥0) : Differentiable ℝ (gaussianPDFReal m v)`
  (`FisherInfoGaussian.lean:68`) — 1階 `Differentiable` (C∞ ではない、`EPIVitaliAE.lean:33` に「gaussianPDFReal は ContDiffBump でない」明記)。`IsBlachmanConvReady` は 1階で足りるので問題なし。
- gateway `convDensityAdd_hasDerivAt_of_regular` (`EPIBlachmanDensity.lean` 経由 / def in `EPIConvDensity.lean:191`) — conv の 1階 deriv を parametric-integral で供給。`@audit:ok`。
- `deriv_convDensityAdd_eq` (`EPIConvDensityRegular.lean:117`) — `deriv (convDensityAdd pX g_t) = convDensityAdd pX (deriv g_t)`。`@audit:ok`。

### §3.4 convolution の moment / decay / Fisher finiteness (in-house で完備)

- `gaussianPDFReal_abs_le (v : ℝ≥0) : ∀ w, |gaussianPDFReal 0 v w| ≤ (Real.sqrt (2*π*v))⁻¹` (`EPIConvDensityRegular.lean:42`, `@audit:ok`) — Gaussian sup bound。
- `deriv_gaussianPDFReal_abs_le {v : ℝ≥0} (hv : v ≠ 0) : ∃ M, ∀ w, |deriv (gaussianPDFReal 0 v) w| ≤ M` (`:64`, `@audit:ok`) — deriv の global sup。
- `gaussianConv_fisher_le_inv_var` (`FisherConvBound.lean:405`) — J(pX⊛g_t) ≤ 1/t (Fisher 有限性、moment 系の代替で十分)。
- `tendsto_convDensityAdd_gaussian_zero` (`EPIConvDensityRegular.lean:148`) — conv の tail vanishing (dominated convergence)。

### §3.4 `convDensityAdd` と Mathlib `MeasureTheory.convolution` の関係

`convDensityAdd pX pY := fun z => ∫ x, pX x * pY (z - x) ∂volume` (`EPIConvDensity.lean:42`)。
Mathlib の `⋆[L,μ]` / `⋆ₗ` ではなく **Bochner `∫` 直書き** (Mathlib-shape-driven: parametric-integral gateway の結論形に合わせた、`EPIConvDensity.lean:27-32` docstring)。よって §3.1 の `HasCompactSupport.*_convolution_*` は型が合わず適用不能 (これも迂回理由の一部)。in-house は `convDensityAdd_convGaussian_interchange` で結合律だけ Mathlib `convolution_assoc` 経由で借り、smoothness は parametric-integral で自前供給する分離設計。

---

## §4 verdict — 壁は genuine か

### FALSE WALL 確定

**`wall:blachman-general-density` は genuine wall ではない。** 親計画の判定根拠
「一般 density 用 `IsBlachmanConvReady` producer は in-house 不在 (rg/loogle Found 0)」
(`epi-csiszar-ratio-reframe-plan.md:93, 113`) は**実コードと直接矛盾**:

1. producer `isBlachmanConvReady_convDensityAdd_gaussian` が `EPIBlachmanGeneralDensity.lean:224` に実在。
2. 19/19 field genuine、`lake env lean` clean、`#print axioms` sorryAx-free (本 inventory 著者が再現確認)。
3. `InformationTheory.lean:234` に import 済みで独立 honesty 監査 (`@audit:ok`, commit `84ecb97`) も完了。
4. 核心仮説 (path 密度 = 任意密度 ⊛ Gaussian → Gaussian 平滑から全 field 出る) は**正しく、かつ既に実装済み**。

→ 親計画の `@residual(plan:epi-csiszar-ratio-reframe-plan,wall:blachman-general-density)` compound 書換計画
(`:227, :623, :699, :806`) は**前提が消えるので不要**。case-1 park の理由のうち「Blachman 一般密度壁」は撤回されるべき。

「出ない field」は **0 個**。回避不能な field は**存在しない** (← 課題で求められた「回避不能ならどの field か 1 つ以上」への回答: 該当無し)。

### 回避に必要な新規補題

**0 件。** `IsBlachmanConvReady` 供給に限れば新規補題は不要。すべて既存。

### ただし — 真の残 gap は別の場所 (壁ではない)

本再確認のスコープ外だが、親計画 `:93` 「真の残壁 2 つ」のうち **(a)** は本物の構造的 gap として残る:

- **(a) path 独立性欠落 (under-hyp)**: `h_stam` から core 不等式 (`1/J_sum ≥ 1/J_X + 1/J_Y`) を取り出すには
  `fXY = convDensityAdd fX fY` 同定が要り、それは `IndepFun path_X path_Y P` (path_X⊥path_Y、X⊥Y も要する) を要する。
  R-3 signature / 上流チェーンに `IndepFun path_X path_Y P` が無い。これは Mathlib 壁ではなく
  **signature の under-hypothesis** であり、`IsBlachmanConvReady` 供給とは独立の問題。

- producer の consumer 配線: `isBlachmanConvReady_convDensityAdd_gaussian` を実際に case-1 の Stam apply 地点
  (R-3 の `IsBlachmanConvReady` precondition、`epi-csiszar-ratio-reframe-plan.md:22` で caller 供給扱い)
  に **wire するだけ** で `IsBlachmanConvReady` 引数は閉じる。これは plan 作業 (lean-planner / lean-implementer) であり Mathlib 壁ではない。

**結論**: case-1 を block しているのは「Blachman 一般密度 Mathlib 壁」ではなく、
(i) `IndepFun path_X path_Y` の signature under-hyp と (ii) 既存 producer の consumer 配線未了。
両者とも genuine Mathlib wall ではない (前者は honesty/signature 問題、後者は plumbing)。

### shared sorry 補題化

`wall:blachman-general-density` 名の shared sorry 補題が他 file に散在していれば、producer 実在により
**全て撤回可能** (sorry → `isBlachmanConvReady_convDensityAdd_gaussian` 呼び出しに置換)。
`EPIStamInequalityBody.lean:279` 等の「CAVEAT: in-tree witness yet (Gaussian only)」コメントは
**stale** (一般版が後から landing したため未更新) — incidental に訂正候補。

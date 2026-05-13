# Csiszár I-projection ムーンショット計画 🌙

Common2026 moonshot seed **E-6** ([docs/moonshot-seeds.md:125](../moonshot-seeds.md)).

> Cover-Thomas 11.6.1, 11.6.4。凸閉集合 `Π ⊆ Δ(α)` 上で
> `Q* := argmin_{P ∈ Π} D(P‖Q)` の存在 + 一意性 +
> `P ∈ Π ⟹ D(P‖Q) ≥ D(P‖Q*) + D(Q*‖Q)` Pythagorean inequality。

## 進捗

- [x] Phase A — Real-valued KL functional `klDivPmf` + 連続性 + 厳密凸性 ✅
- [x] Phase B — 存在 (extreme value theorem 経由) ✅
- [x] Phase C — 一意性 (strict convexity 経由) ✅
- [x] Phase D — Pythagorean inequality (1 次条件) ✅
- [ ] Phase E — linear-family 等号 (Cover-Thomas 11.6.4 系) 📋 (scope-deferred)

## ゴール / Approach

**最終定理 3 本**:

1. `csiszar_projection_exists`: 任意の閉凸非空 `Π ⊆ stdSimplex ℝ α` と full-support
   reference `Q : α → ℝ` (`Q ∈ stdSimplex ℝ α`, `∀ a, 0 < Q a`) に対して
   `∃ Qstar ∈ Π, IsMinOn (klDivPmf · Q) Π Qstar`。

2. `csiszar_projection_unique`: 上の 2 つの最小化元は等しい。

3. `csiszar_pythagoras_inequality`: `Q* ∈ Π` が極小化元、`P ∈ Π`、`Q*, Q` full support
   なら `klDivPmf P Q ≥ klDivPmf P Q* + klDivPmf Q* Q`。

**Approach (全体戦略)**:

- **表現の選択**: 確率測度ではなく **`Q : α → ℝ` (pmf 直接)** として `stdSimplex ℝ α`
  上で working する。理由:
  - Mathlib `stdSimplex` は `isCompact` / `convex` / `isClosed` が off-the-shelf。
  - `klDivPmf P Q := ∑ Q(a) · klFun(P(a) / Q(a))` で `Sanov.klDivSumForm` と shape 一致 +
    `klFun_nonneg` / `strictConvexOn_klFun` を直接呼べる。
  - `Measure α` 版へは Sanov の `klDivSumForm_eq_toReal_klDiv` 経由で後付け bridge 可能
    (本 plan の scope 外、必要なら deferred 補題)。
- **3 主結果の戦略**:
  - **存在 (B)**: `IsCompact.exists_isMinOn` を使う。`stdSimplex` 部分集合 (`Π`) も閉
    + bounded ⟹ コンパクト。`klDivPmf · Q` の **連続性** を要する (`klFun`
    `continuous` + Q full support で `P(a)/Q(a)` 連続)。
  - **一意性 (C)**: `klFun` の `StrictConvexOn (Ici 0)` (Mathlib `strictConvexOn_klFun`)
    から `klDivPmf · Q` の strict convexity。2 最小化元 `Qstar, Qstar'` があれば
    mid-point `P_t := (1-t)Qstar + t·Qstar'` が `Π` (凸) かつ厳密凸性 ⟹
    `klDivPmf P_t Q < min(klDivPmf Qstar Q, klDivPmf Qstar' Q)` で矛盾。
  - **Pythagorean (D)**: アルゴリズムは古典的に
    1. **代数恒等式**: `klDivPmf P Q = klDivPmf P Q* + ∑ P(a) log(Q*(a)/Q(a))`
       (support 整合下で常に成立)
    2. ゆえに Pythagorean ⟺ `∑ (P(a) - Q*(a)) log(Q*(a)/Q(a)) ≥ 0` (**1 次条件**)
    3. 1 次条件は **`t = 0` での右微分が ≥ 0**: `φ(t) := klDivPmf ((1-t)Q* + tP) Q`
       が `φ(0) ≤ φ(t)` (`t ∈ [0,1]`) ゆえ `φ'(0+) ≥ 0`。`hasDerivAt_klFun` で
       per-summand 微分 + `Finset.sum` linearity。

- **shape-driven 設計判断**:
  - `klFun` の `StrictConvexOn ℝ (Ici 0)` が Mathlib 既存 (`strictConvexOn_klFun`、
    `Mathlib.InformationTheory.KullbackLeibler.KLFun`)。**PinskerSharp の `klFun_sharp_lower`
    refactor は不要**。
  - `IsCompact.exists_isMinOn` の signature: `(hs : IsCompact s) (ne_s : s.Nonempty)
    (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x` — そのまま使う。
  - `klDivPmf` 連続性は full-support Q が必要、よって全主定理に `hQ_pos : ∀ a, 0 < Q a`
    仮説を入れる。
  - **Pythagorean は inequality**: 一般 closed convex Π では equality は成立しない
    (Cover-Thomas 11.6.4 等式形は **linear family** `Π = {P : ∑ P(a) g(a) = c}` 限定)。
    Phase E で linear family の場合の equality を別補題 `csiszar_pythagoras_linear_family`
    として publish (optional)。

- **見積**: ~600 行 (Phase A ~150, B ~80, C ~120, D ~200, E ~50)。

## Phase A - Real-valued KL functional + 連続性 + 厳密凸性 📋

- [ ] `klDivPmf P Q := ∑ a, Q a * klFun (P a / Q a)` 定義 (Real)
- [ ] `klDivPmf_nonneg`: `∀ a ∈ univ, 0 ≤ P a → 0 ≤ Q a → 0 ≤ klDivPmf P Q`
- [ ] `continuous_klDivPmf_left`: full-support Q 下で `P ↦ klDivPmf P Q` 連続
  (`klFun` `continuous` + `P(a)/Q(a)` 連続 + finite sum)
- [ ] `klDivPmf_strictConvex_left`: full-support Q 下で `P ↦ klDivPmf P Q` は
  `Convex.StrictConvexOn (stdSimplex ℝ α) ...` (per-coordinate `strictConvexOn_klFun`
  経由)

## Phase B - 存在 📋

- [ ] `Pi_isCompact`: `IsCompact Π` (`stdSimplex` 部分閉集合の閉包 ⟹ コンパクト) —
  `Π ⊆ stdSimplex` + `IsClosed Π` + `isCompact_stdSimplex` で `IsCompact.of_isClosed_subset`
- [ ] `csiszar_projection_exists`:
  `(hΠ_conv : Convex ℝ Π) (hΠ_closed : IsClosed Π) (hΠ_sub : Π ⊆ stdSimplex ℝ α)
   (hΠ_ne : Π.Nonempty) (hQ : Q ∈ stdSimplex ℝ α) (hQ_pos : ∀ a, 0 < Q a) :
   ∃ Qstar ∈ Π, IsMinOn (fun P => klDivPmf P Q) Π Qstar`
  — `IsCompact.exists_isMinOn` を直接呼ぶ + Phase A 連続性

## Phase C - 一意性 📋

- [ ] `csiszar_projection_unique`: 上仮説のもとで 2 最小化元 `Qstar Qstar' ∈ Π` で
  `klDivPmf Qstar Q = klDivPmf Qstar' Q = inf` なら `Qstar = Qstar'`。
  - 戦略: `Qstar ≠ Qstar'` を仮定 ⟹ mid-point `P_½ := (1/2)Qstar + (1/2)Qstar' ∈ Π`
    (凸) で `klDivPmf P_½ Q < (1/2)(klDivPmf Qstar Q + klDivPmf Qstar' Q) = inf`
    (strict convexity) で `IsMinOn` と矛盾

## Phase D - Pythagorean inequality 📋

- [ ] `klDivPmf_algebraic_identity`:
  `P ∈ stdSimplex, Q* ∈ stdSimplex, Q ∈ stdSimplex` (full support Q, Q*),
  `P ≪ Q*` (i.e., P(a) = 0 ⟹ Q*(a) = 0、本plan では Q* full support ゆえ vacuous で
  P, Q* full support 想定でいい) のもとで
  `klDivPmf P Q = klDivPmf P Q* + ∑ a, P a * (log (Q* a) - log (Q a))`
  — 純代数 (`log_div` 展開)
- [ ] `klDivPmf_self_form`:
  `klDivPmf Q* Q = ∑ a, Q* a * (log (Q* a) - log (Q a))`
  — 定義展開 (`klFun (Q*/Q) = (Q*/Q) log (Q*/Q) + 1 - Q*/Q` + ∑ Q* = ∑ Q = 1)
- [ ] `pythagoras_iff_first_order`:
  Pythagorean inequality `klDivPmf P Q ≥ klDivPmf P Q* + klDivPmf Q* Q`
  ⟺ first-order `∑ a, (P a - Q* a) * (log (Q* a) - log (Q a)) ≥ 0`
  — 2 つの代数恒等式を引き算
- [ ] `first_order_condition`:
  `Qstar` が最小化元なら、任意 `P ∈ Π` で
  `∑ a, (P a - Qstar a) * (log (Qstar a) - log (Q a)) ≥ 0`
  — `φ(t) := klDivPmf ((1-t)Qstar + tP) Q` の右微分 `φ'(0+) ≥ 0` 経由
  - 補題 `hasDerivAt_klDivPmf_segment`:
    `HasDerivAt (fun t => klDivPmf ((1-t)Qstar + tP) Q)
       (∑ a, (P a - Qstar a) * (log (Qstar a) - log (Q a))) 0`
    — Phase A 連続性 + `hasDerivAt_klFun` + `Finset.sum` linearity
- [ ] `csiszar_pythagoras_inequality`:
  最小化元 `Qstar` + `P ∈ Π` ⟹
  `klDivPmf P Q ≥ klDivPmf P Qstar + klDivPmf Qstar Q`
  — 上の 3 つの合成

## Phase E - linear-family equality (任意 / corollary) 📋

- [ ] `csiszar_pythagoras_linear_family_equality`:
  `Π := {P : ∀ i, ∑ a, P a * g i a = c i}` (linear constraint family) のもとで
  Pythagorean は **equality** で成立。
  - 戦略: `P ∈ Π, Q* ∈ Π` ⟹ `P + s(Q* - P) ∈ Π` for all `s ∈ ℝ` (constraint は
    linear だから `(1-s)·c + s·c = c`) ⟹ first-order 両側で `≥ 0`、ゆえに `= 0`、
    ゆえに equality。
  - Cover-Thomas 11.6.4 直接。**任意 / 後回し可能**。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **`Π` (大文字パイ) → `K`** (2026-05-13): Lean が `Π` を dependent product 用 reserved token として扱い、binder 名に使えない。`K` (closed convex set の慣習) に rename。docstring の Π → K に合わせる。

2. **`Measure α` 不採用、`α → ℝ` (pmf) + `stdSimplex ℝ α` 採用** (2026-05-13、Approach 確立時): Mathlib `stdSimplex ℝ α` (`Mathlib.Analysis.Convex.StdSimplex`) が `Convex` / `IsClosed` / `IsCompact` を off-the-shelf 提供。`Measure α` 上の同等性質は finite-alphabet で derive 可能だが topology 設定や `IsProbabilityMeasure` instance 経由で重く、scope に対して overengineer。`(klDiv P Q).toReal` 形への bridge は `Sanov.klDivSumForm_eq_toReal_klDiv` テンプレで後付け可能 (現 plan scope 外)。

3. **`klFun_sharp_lower` (PinskerSharp) refactor 不要** (2026-05-13、loogle 確認時): Mathlib `strictConvexOn_klFun : StrictConvexOn ℝ (Ici 0) klFun` (`Mathlib.InformationTheory.KullbackLeibler.KLFun:62`) が既存。Phase A `klDivPmf_strictConvexOn_left` で **per-coordinate** に直接適用、`PinskerSharp.lean` 内 helper の昇格不要。

4. **Pythagorean は inequality** (`≥`、Cover-Thomas 11.6.1) で実装、equality 形 (11.6.4) は **scope-deferred** (2026-05-13、設計時): 一般 closed convex `K` では equality は成立せず inequality のみ。equality 形は linear-family `K := {P : ∀ i, ∑ P g_i = c_i}` 限定で、`P + s(P - Qstar) ∈ K` (∀ `s ∈ ℝ`) から両方向 first-order `≥ 0` ⟹ `= 0` で取得可能。Phase E として保留、必要時に E-6.1 として追加 plan。

5. **`csiszar_first_order_condition` の `hK_sub` 不要** (2026-05-13、実装時に発覚): 1 次条件の証明は `K` のコンパクト性を要さず、凸性 (`hK_conv`) + minimality (`hmin`) + Qstar/Q full support だけで完結。`hK_sub` を signature から除去。Pythagorean 主定理側で `hP_sum = (hK_sub hP).2` を抽出する形に整理。

6. **derivative 経路を採用** (subgradient/secant 経路は不採用、2026-05-13): subgradient 不等式 `klFun(v) ≥ klFun(u) + log(u)(v-u)` を直接和をとると `klDivPmf P Q ≥ klDivPmf Q* Q + ∑ (P - Q*) log(Q*/Q)` を得るが、これは minimality を **使っていない** (`klDivPmf Q* Q ≤ klDivPmf P Q` の自明再導出に縮退、`∑ (P - Q*) log(Q*/Q) ≥ -klDivPmf Q* Q` という弱い情報しか出ない)。Pythagorean inequality は本質的に Q* の minimality を消費する 1 次条件 `∑ (P - Q*) log(Q*/Q) ≥ 0` を要し、これは `t ↦ klDivPmf ((1-t)Q* + tP) Q` の右微分 `≥ 0` でしか取れない。Mathlib `hasDerivAt_iff_tendsto_slope_left_right` + `ge_of_tendsto` + per-summand chain rule の組合せで `~80` 行で完結。

## 実装完了 (2026-05-13)

`Common2026/Shannon/CsiszarProjection.lean` (487 行) で 3 主定理 + 1 補助補題を publish:

### 主定理

- `csiszar_projection_exists` (Phase B):
  ```
  (hK_closed : IsClosed K) (hK_sub : K ⊆ stdSimplex ℝ α)
  (hK_ne : K.Nonempty) (hQ_pos : ∀ a, 0 < Q a) :
  ∃ Qstar ∈ K, IsMinOn (fun P => klDivPmf P Q) K Qstar
  ```
- `csiszar_projection_unique` (Phase C):
  ```
  (hK_conv : Convex ℝ K) (hK_sub : K ⊆ stdSimplex ℝ α)
  (hQ_pos : ∀ a, 0 < Q a)
  {Qstar Qstar'} (hQs : Qstar ∈ K) (hQs' : Qstar' ∈ K)
  (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar)
  (hmin' : IsMinOn (fun P => klDivPmf P Q) K Qstar') :
  Qstar = Qstar'
  ```
- `csiszar_pythagoras_inequality` (Phase D):
  ```
  (hK_conv : Convex ℝ K) (hK_sub : K ⊆ stdSimplex ℝ α)
  (hQ_sum : ∑ a, Q a = 1) (hQ_pos : ∀ a, 0 < Q a)
  {Qstar} (hQs : Qstar ∈ K) (hQs_pos : ∀ a, 0 < Qstar a)
  (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar)
  {P} (hP : P ∈ K) (hP_pos : ∀ a, 0 < P a) :
  klDivPmf P Q ≥ klDivPmf P Qstar + klDivPmf Qstar Q
  ```

### 補助補題 (再利用候補)

- `klDivPmf` 定義 (`∑ a, Q a * klFun (P a / Q a)`)
- `klDivPmf_nonneg` (任意の non-negative P, Q)
- `continuous_klDivPmf_left` (full-support Q 下で P ↦ klDivPmf P Q 連続)
- `klDivPmf_strictConvexOn_left` (full-support Q 下で stdSimplex 上厳密凸)
- `klDivPmf_eq_log_diff_sum` (`= ∑ P (log P - log Q)` 標準和形、probability + full support)
- `klDivPmf_decomp_via_intermediate` (`= klDivPmf P Qstar + ∑ P (log Qstar - log Q)`、中間点)
- `klDivPmf_self_expand` (`klDivPmf Q* Q = ∑ Q* (log Q* - log Q)`)
- `csiszar_first_order_condition` (∑ (P - Q*) (log Q* - log Q) ≥ 0、`HasDerivAt` 経由)
- `isCompact_of_subset_stdSimplex` (汎用、`stdSimplex` 部分閉集合のコンパクト性)

### Mathlib gap

- Mathlib `klDiv` の `StrictConvexOn` (ENNReal-level) は不在。`(klDiv P Q).toReal` 形で
  finite-measure 上に書く場合は Bochner 経由の連続性証明が必要 (`MaxEntropy.klDiv_uniformOn_univ_toReal_eq`
  template)。本 plan は `klDivPmf` 経由で迂回。
- Mathlib `IsLocalMinOn` 周辺に「`HasDerivAt + IsMinOn on [0, ε]` ⟹ derivative ≥ 0」の直接補題は
  なし (1-d only)。`fderivWithin_nonneg` は `posTangentConeAt` 経由で heavy。本 plan は
  `hasDerivAt_iff_tendsto_slope_left_right` + `ge_of_tendsto` で elementary に組む。

### Downstream 利用時の注意

- **`Measure α` 経由で使う場合**: `Sanov.klDivSumForm_eq_toReal_klDiv` テンプレ
  (`MaxEntropy.klDiv_uniformOn_univ_toReal_eq` も同類) を組合せて `(klDiv P Q).toReal` 形に
  bridge する。klDiv の `IsProbabilityMeasure` 仮説 + AC + `Integrable (llr ...)` 整備が要る。
- **E-1 (channel coding strong converse) / E-3 (rate-distortion)**: I-projection の幾何 (Pythagorean
  inequality) を `Π` を rate-distortion 制約集合に取って使う場面が想定される。E-3 plan 起草時に
  「`klDivPmf` のシンプレックス vs `Measure` ambient の経路選択」を再確認。
- **`klDivPmf_eq_log_diff_sum` の独立 utility**: Sanov の `klDivSumForm` と shape 一致 (定義は
  `∑ Q a * klFun (P a / Q a)`、展開後は `∑ P (log P - log Q)`)。`Sanov.lean` への refactor 候補
  (片方を deprecate して unify) は scope-deferred (両者並立で API 重複は小)。
- **linear-family equality (11.6.4)**: 必要なら E-6.1 として追加 plan。`first_order_condition` を
  両方向 (P と 2·Qstar - P) で適用するだけ、見積 ~50 行。

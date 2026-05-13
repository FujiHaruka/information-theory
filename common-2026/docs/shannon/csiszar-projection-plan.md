# Csiszár I-projection ムーンショット計画 🌙

Common2026 moonshot seed **E-6** ([docs/moonshot-seeds.md:125](../moonshot-seeds.md)).

> Cover-Thomas 11.6.1, 11.6.4。凸閉集合 `Π ⊆ Δ(α)` 上で
> `Q* := argmin_{P ∈ Π} D(P‖Q)` の存在 + 一意性 +
> `P ∈ Π ⟹ D(P‖Q) ≥ D(P‖Q*) + D(Q*‖Q)` Pythagorean inequality。

## 進捗

- [ ] Phase A — Real-valued KL functional `klDivPmf` + 連続性 + 厳密凸性 📋
- [ ] Phase B — 存在 (extreme value theorem 経由) 📋
- [ ] Phase C — 一意性 (strict convexity 経由) 📋
- [ ] Phase D — Pythagorean inequality (1 次条件) 📋
- [ ] Phase E — linear-family 等号 (Cover-Thomas 11.6.4 系) 📋

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

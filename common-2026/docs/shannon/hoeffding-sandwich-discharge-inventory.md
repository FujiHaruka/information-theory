# Hoeffding tradeoff sandwich discharge — 既存資産在庫調査

> 対象: `HoeffdingTradeoff.hoeffding_tradeoff_with_hypothesis` (`Common2026/Shannon/HoeffdingTradeoff.lean:296`)
> の hypothesis-free 化に残る 2 本の漸近不等式 `h_liminf` (achievability) / `h_limsup` (converse) を
> discharge するための **既存プロジェクト資産 (Sanov/Stein/Csiszar/AEP)** の再利用可能 API 在庫。
> 親計画: [`hoeffding-tradeoff-moonshot-plan.md`](hoeffding-tradeoff-moonshot-plan.md) (Phase C/D + 撤退ライン L-H4, L-HP1〜3)。

## 一行サマリ

**achievability `h_liminf` は Sanov LDP equality (`sanov_ldp_equality`) が "union-of-type-classes-near-Qstar" 形でほぼそのまま起動でき、KL 二形は finite-support で逐語一致 (`klDivPmf_eq_log_diff_sum` = `klDivSumForm_ofVec` の def) なので橋は薄い。最大の gap は (1) Qstar full-support `hQs_pos` が依然 hypothesis (L-H4, 30-50 行)、(2) acceptance region `E_n*` の Finset 化 + Type I 制御 (自前 AEP ~30-50 行)。converse `h_limsup` は Stein/StrongStein converse template (`steinOptimalBeta_log_le_of_strong_converse` / `stein_strong_lemma`) を Qstar 流用 + pmf↔Measure bridge で起動でき、Pythagoras (`csiszar_pythagoras_inequality`) で任意 test を Qstar の β に支配させる。** 既存実体率: achievability ~75% / converse ~80%。自作必要 6 件。撤退ライン L-H4 (Qstar full-support) は **既に発動済で本 discharge でも継続**、ただし新規縮退案 (boundary α 域への限定) を提示。

---

## 主定理の最終形 (再掲)

```lean
-- 現状 (hypothesis 形, HoeffdingTradeoff.lean:296)
theorem hoeffding_tradeoff_with_hypothesis (P₁ P₂ : α → ℝ) ...
    (h_liminf : hoeffdingE2 P₁ P₂ alpha ≤ liminf (fun n => -(1/n) * log (steinTypeII_at_level_pmf P₁ P₂ n alpha)) atTop)
    (h_limsup : limsup (fun n => -(1/n) * log (steinTypeII_at_level_pmf P₁ P₂ n alpha)) atTop ≤ hoeffdingE2 P₁ P₂ alpha)
    ... : Tendsto (...) atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha))

-- 目標 (hypothesis-free, plan §Phase C/D の Done 条件)
theorem hoeffding_tradeoff (P₁ P₂ : α → ℝ)
    (hP₁_pos hP₂_pos : ∀ a, 0 < ·) (hP₁_sum hP₂_sum : ∑ = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂) :
    Tendsto (fun n => -(1/n) * log (steinTypeII_at_level_pmf P₁ P₂ n alpha)) atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha))
```

discharge 戦略 (pseudo-Lean):

```
-- 共通: Qstar 取り出し
obtain ⟨Qstar, hQs_mem, hQs_min⟩ := hoeffdingE2_attained P₁ P₂ hP₁_pos hP₂_pos hP₁_sum alpha h_alpha_nn
have hQs_pos := hoeffdingE2_minimizer_full_support ...   -- ⚠ L-H4: 依然 sorry/hypothesis

-- achievability h_liminf:
let E n := type classes c with (c/n) ∈ hoeffdingConstraintSet P₁ alpha       -- C-3 (Finset 化)
have h_in_E : ∀ᶠ n, roundedTypeIndex Qstar n ∈ E n                            -- C-4
have h_minimizer : ∀ n, ∀ c ∈ E n, klDivSumForm_ofVec Qstar P₂ ≤ klDivIndex c n P₂_meas
                                                                              -- = hoeffding_minimizer_ge + sum bridge
have := sanov_ldp_equality P₂_meas hQpos Qstar hP_prob hQs_pos E h_in_E h_minimizer   -- C-4: Sanov 起動
-- ⇒ (1/n) log P₂^n(⋃ T_c) → -klDivSumForm_ofVec Qstar P₂ = -hoeffdingE2
have h_typeI : ∀ᶠ n, P₁^n(⋃ T_c) ≥ 1 - alpha                                 -- C-5: 自前 AEP 必要
-- steinTypeII ≤ P₂^n(⋃)  (s := ⋃ T_c が test) ⇒ liminf rate ≥ E2

-- converse h_limsup:
-- 任意 test s with Type I ≤ alpha: P₂^n s を steinTypicalSet Qstar_meas P₂_meas で支配
-- + csiszar_pythagoras_inequality で klDivPmf Q P₂ ≥ E2 (Q ∈ K)
have := stein_strong_lemma (P := Qstar_meas) (Q := P₂_meas) ...               -- D-2: Stein converse 起動
-- ⇒ limsup rate ≤ klDiv Qstar_meas P₂_meas = E2 (klDivSumForm_eq_toReal_klDiv bridge)
```

---

## A. Sanov LDP 漸近 (achievability `h_liminf` の主軸)

| 概念 | 既存 API (file:line) | 完全 signature `[...]` verbatim | 結論 verbatim | discharge での扱い |
|---|---|---|---|---|
| Sanov LDP **equality** (Tendsto) | `sanov_ldp_equality` (`SanovLDPEquality.lean:1243`) | `(Q : Measure α) [IsProbabilityMeasure Q] (hQpos : ∀ a, 0 < Q.real {a}) (P : α → ℝ) (hP_prob : ∑ a, P a = 1) (hP_full : ∀ a, 0 < P a) (E : ∀ n, Finset (TypeCountIndex α n)) (h_in_E : ∀ᶠ n in atTop, roundedTypeIndex P n ∈ E n) (h_minimizer : ∀ n, ∀ c ∈ E n, klDivSumForm_ofVec P (fun a => Q.real {a}) ≤ klDivIndex (fun a => (c a : ℕ)) n Q)` | `Tendsto (fun n => (1/n) * Real.log ((Measure.pi (fun _:Fin n => Q)) (⋃ c ∈ E n, typeClassByCount (fun a => (c a:ℕ)))).toReal) atTop (𝓝 (-(klDivSumForm_ofVec P (fun a => Q.real {a}))))` | **achievability の中核**. `Q := pmfToMeasure P₂`, `P := Qstar`. 結論を `-(1/n) log` に符号反転 + `.eventually_ge` で `h_liminf` を作る |
| Sanov LDP **lower** (liminf) | `sanov_ldp_lower_bound_pointwise` (`SanovLDPEquality.lean:1071`) | `(Q : Measure α) [IsProbabilityMeasure Q] (hQpos : ∀ a, 0 < Q.real {a}) (P : α → ℝ) (hP_prob : ∑ a, P a = 1) (hP_full : ∀ a, 0 < P a) (E : ∀ n, Finset (TypeCountIndex α n)) (h_in_E : ∀ᶠ n in atTop, roundedTypeIndex P n ∈ E n)` | `-klDivSumForm_ofVec P (fun a => Q.real {a}) ≤ Filter.liminf (fun n => (1/n) * Real.log ((Measure.pi (fun _:Fin n => Q)) (⋃ c ∈ E n, typeClassByCount (fun a=>(c a:ℕ)))).toReal) atTop` | `h_minimizer` 不要版. **achievability に直接これで足りる** (equality より弱いが liminf 側だけ要るので最小依存) |
| Sanov LDP **upper** | `sanov_ldp_upper_bound` (`SanovLDP.lean:471`) | `(Q : Measure α) [IsProbabilityMeasure Q] (hQpos : ∀ a, 0 < Q.real {a}) (E : ∀ n, Finset (TypeCountIndex α n)) (D : ℝ) (hD : ∀ n, ∀ c ∈ E n, D ≤ klDivIndex (fun a => (c a:ℕ)) n Q) {ε : ℝ} (hε : 0 < ε)` | `∃ N, ∀ n ≥ N, 0 < n → 0 < (Q^n(⋃ T_c)).toReal → (1/n) * Real.log (Q^n(⋃ T_c)).toReal ≤ -D + ε` | converse 側の per-type 上界に流用可 (Stein 経路を使うなら不要) |
| 経験型クラス | `typeClassByCount {n} (c : α → ℕ) : Set (Fin n → α)` (`SanovLDP.lean:82`) | `{ x | ∀ a, typeCount x a = c a }` | — | acceptance region `s_n = ⋃ T_c` の構成要素 |
| 型 index 型 | `TypeCountIndex (α) [Fintype α] (n) : Type _` (`SanovLDP.lean:55`) | `:= α → Fin (n+1)` (`abbrev`) | — | `E : ∀ n, Finset (TypeCountIndex α n)` の要素型 |
| 達成型列 | `roundedTypeIndex (P : α → ℝ) (n) : TypeCountIndex α n` (`SanovLDPEquality.lean:111`) | (no extra TC) | `c a := ⌊nP a⌋ (a≠a₀), c a₀ := n - Σ` | `h_in_E : roundedTypeIndex Qstar n ∈ E n` を満たす Qstar 近似型 |
| 型列の和制約 | `roundedTypeIndex_sum` (`SanovLDPEquality.lean:121`) | `(P : α → ℝ) (hP : ∑ a, P a = 1) (hP_nn : ∀ a, 0 ≤ P a) (n : ℕ) (_hn : 0 < n)` | `(∑ a, (roundedTypeIndex P n a : ℕ)) = n` | C-4 の補助 |
| KL@型 (index 形) | `klDivIndex (c : α → ℕ) (n) (Q : Measure α) : ℝ` (`SanovLDP.lean:97`) | — | `:= ∑ a, ((c a:ℝ)/n) * (log ((c a:ℝ)/n) - log (Q.real {a}))` | `h_minimizer` の右辺 |

**注**: 親 plan §Phase C は `sanov_ldp_equality` を起動して両側 sandwich で `Tendsto` を取る前提だったが、achievability の `h_liminf` (片側 liminf) だけなら `sanov_ldp_lower_bound_pointwise` で済み、`h_minimizer` 仮定 (= Pythagoras minimizer) すら不要になる。**ただし `sanov_ldp_lower_bound_pointwise` は `⋃ T_c` の P₂ 質量の liminf を `-klDivSumForm_ofVec Qstar P₂` 以上にするだけで、`-D` が `E2` に一致するには `Qstar` が真の minimizer であることが別途要る** (steinTypeII ≤ P₂^n(⋃) と組む際の loose 化の方向に効く)。

---

## B. KL 二形の橋 (Csiszar `klDivPmf` ↔ Sanov `klDivSumForm_ofVec` / `klDivIndex` ↔ Mathlib `klDiv`)

| 概念 | 既存 API (file:line) | 完全 signature `[...]` verbatim | 結論 verbatim | 評価 |
|---|---|---|---|---|
| `klDivPmf` def | `klDivPmf (P Q : α → ℝ) : ℝ` (`CsiszarProjection.lean:55`) | (no extra TC) | `:= ∑ a : α, Q a * klFun (P a / Q a)` | hoeffdingE2 / Pythagoras 側の KL |
| `klDivPmf` の log-diff 展開 | `klDivPmf_eq_log_diff_sum` (`CsiszarProjection.lean:231`) | `{P Q : α → ℝ} (hP_sum : ∑ a, P a = 1) (hQ_sum : ∑ a, Q a = 1) (hP_pos : ∀ a, 0 < P a) (hQ_pos : ∀ a, 0 < Q a)` | `klDivPmf P Q = ∑ a : α, P a * (Real.log (P a) - Real.log (Q a))` | **🟢 鍵**: 右辺が `klDivSumForm_ofVec P Q` の def と**逐語一致** |
| `klDivSumForm_ofVec` def | `klDivSumForm_ofVec (p q : α → ℝ) : ℝ` (`KLDivContinuous.lean:31`) | (no extra TC) | `:= ∑ a : α, p a * (Real.log (p a) - Real.log (q a))` | Sanov 結論側の KL. **full support 下で `klDivPmf = klDivSumForm_ofVec` (橋 = `klDivPmf_eq_log_diff_sum` を rfl で噛ませるだけ、~3 行)** |
| `klDivIndex` ↔ `klDivSumForm_ofVec` | `klDivIndex_eq_ofVec` (`KLDivContinuous.lean:68`) | `(c : α → ℕ) (n : ℕ) (Q : Measure α)` | `klDivIndex c n Q = klDivSumForm_ofVec (fun a => (c a:ℝ)/n) (fun a => Q.real {a})` (`:= rfl`) | C-2 の `h_minimizer` 右辺整形 |
| `klDivSumForm` (Measure 形) ↔ `klDiv` | `klDivSumForm_eq_toReal_klDiv` (`Sanov.lean:252`) | `(P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQpos : ∀ a, 0 < Q.real {a})` | `klDivSumForm P Q = (klDiv P Q).toReal` | **converse の橋**: Stein は `(klDiv P Q).toReal` 形で結論するので、`E2 = klDivPmf Qstar P₂` を `(klDiv Qstar_meas P₂_meas).toReal` に渡す (3 段橋: `klDivPmf → klDivSumForm_ofVec → klDivSumForm(Measure) → klDiv.toReal`) |
| pmf→Measure singleton 値 | `pmfToMeasure_real_singleton` (`HoeffdingTradeoff.lean:85`) | `(P : α → ℝ) (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1) (a : α)` | `(pmfToMeasure P hP_nn hP_sum).real {a} = P a` | `Q.real {a} = P₂ a` 整合 (Sanov/Stein の `Q.real {a}` ↔ pmf 値) |
| pmf→Measure 確率測度性 | `pmfToMeasure_isProbabilityMeasure` (`HoeffdingTradeoff.lean:72`, instance) | `(P : α → ℝ) (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1)` | `IsProbabilityMeasure (pmfToMeasure P hP_nn hP_sum)` | Sanov/Stein の `[IsProbabilityMeasure Q]` 充足 |

**🟢 橋全体の評価**: 二つの KL がともに finite-support で `∑ p (log p - log q)` 形に潰れるため、橋は **代数的でなく定義的** (≤ 5 行/橋)。親 plan の懸念 (50 行超で L-H1 発動) は杞憂。**ただし `pmfToMeasure P₂` を経由する都度 `Q.real {a} = P₂ a` の rewrite が散布する** (singleton 値の橋を `simp only` で集約すれば ~10 行)。

---

## C. Stein converse template (converse `h_limsup` の主軸)

| 概念 | 既存 API (file:line) | 完全 signature `[...]` verbatim | 結論 verbatim | discharge での扱い |
|---|---|---|---|---|
| **strong** converse 上界 | `steinOptimalBeta_log_le_of_strong_converse` (`StrongStein.lean:395`) | `(μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (hMap : μ.map (Xs 0) = P) (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _:Fin n => P)) (hPpos : ∀ x, 0 < P.real {x}) (hPQ : P ≪ Q) (hQpos : ∀ x, 0 < Q.real {x}) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)` | `∀ᶠ n in atTop, -(1/n)*log (steinOptimalBeta P Q n ε) ≤ (klDiv P Q).toReal + δ - (1/n)*log ((Measure.pi (fun _:Fin n => P)) (steinTypicalSet P Q n δ)).toReal - ε)` | **converse の中核**. `P := Qstar_meas`, `Q := P₂_meas`. `1/(1-ε)` 因子なしの strict 形 (在庫 §危険 4 回避) |
| strong Stein sandwich | `stein_strong_lemma` (`StrongStein.lean:498`) | `(μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (Xs : ℕ → Ω → α) (hXs) (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (hMap : μ.map (Xs 0) = P) (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _:Fin n => P)) (hPpos : ∀ x, 0 < P.real {x}) (hPQ : P ≪ Q) (hQpos : ∀ x, 0 < Q.real {x}) {ε} (hε : 0 < ε) (hε1 : ε < 1)` | `Tendsto (fun n => -((1:ℝ)/n) * Real.log (steinOptimalBeta P Q n ε)) atTop (𝓝 (klDiv P Q).toReal)` (**strict Tendsto, `1/(1-ε)` 因子なし, ε→0 外側ループ不要**) | **converse `limsup ≤ E2` の最良エンジン**. `P := Qstar_meas`, `Q := P₂_meas`. `.eventually_le` で `∀ᶠ n, rate ≤ K + δ` ⇒ `limsup ≤ K = E2` |
| (弱) converse 上界 | `steinOptimalBeta_log_le_of_converse` (`Stein.lean:1286`) | `(P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPpos : ∀ x, 0 < P.real {x}) (hPQ : P ≪ Q) (hQpos : ∀ x, 0 < Q.real {x}) {ε} (hε : 0 < ε) (hε1 : ε < 1) {n} (hn : 0 < n)` | `-(1/n)*log (steinOptimalBeta P Q n ε) ≤ (klDiv P Q).toReal/(1-ε) + log 2/(n*(1-ε))` | fallback (L-HP3): `1/(1-ε)` 因子を ε→0 外側ループで吸収 |
| (弱) Stein sandwich | `stein_lemma` (`Stein.lean:1390`) | (同上 + `{ε} (hε) (hε1)`) | `(klDiv P Q).toReal ≤ liminf rate ∧ limsup rate ≤ (klDiv P Q).toReal/(1-ε)` | fallback |
| Stein β-set (Measure 形) | `steinBetaSet (P Q : Measure α) (n) (ε) : Set ℝ` (`Stein.lean:1139`) | (no extra TC) | `{ β | ∃ s, MeasurableSet s ∧ (P^n sᶜ).toReal ≤ ε ∧ β = (Q^n s).toReal }` | **`steinBetaSet_pmf` (HoeffdingTradeoff.lean:109) と同型** (Type I `1-Σ_s P₁ = P₁^n sᶜ` ↔ ε, Σ_s P₂ ↔ Q^n s) |
| Stein opt β | `steinOptimalBeta (P Q) (n) (ε) := sInf (steinBetaSet …)` (`Stein.lean:1146`) | — | `:= sInf (steinBetaSet P Q n ε)` | `steinTypeII_at_level_pmf` の Measure 版. 両者の橋が converse で要 (§E gap) |
| typical set Q 質量上界 | `steinTypicalSet_Q_prob_le` (`Stein.lean:341`) | `(P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPpos : ∀ x, 0 < P.real {x}) (hQpos : ∀ x, 0 < Q.real {x}) (n : ℕ) (ε : ℝ)` | `((Measure.pi (fun _:Fin n => Q)) (steinTypicalSet P Q n ε)).toReal ≤ Real.exp (-((n:ℝ) * ((klDiv P Q).toReal - ε)))` | converse の per-type 支配 (Stein 内部で既使用) |

---

## D. Pythagoras / minimizer (両側で `Q ∈ K ⇒ klDivPmf Q P₂ ≥ E2` を供給)

| 概念 | 既存 API (file:line) | 完全 signature `[...]` verbatim | 結論 verbatim | 扱い |
|---|---|---|---|---|
| Csiszar Pythagoras | `csiszar_pythagoras_inequality` (`CsiszarProjection.lean:449`) | `{K : Set (α → ℝ)} {Q : α → ℝ} (hK_conv : Convex ℝ K) (hK_sub : K ⊆ stdSimplex ℝ α) (hQ_sum : ∑ a, Q a = 1) (hQ_pos : ∀ a, 0 < Q a) {Qstar : α → ℝ} (hQs : Qstar ∈ K) (hQs_pos : ∀ a, 0 < Qstar a) (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar) {P : α → ℝ} (hP : P ∈ K) (hP_pos : ∀ a, 0 < P a)` | `klDivPmf P Q ≥ klDivPmf P Qstar + klDivPmf Qstar Q` | converse D-3 で `Q ∈ K ⇒ klDivPmf Q P₂ ≥ E2` を生成。**全引数 full-support 要求 (`hQ_pos` `hQs_pos` `hP_pos`)** ← L-H4 の波及源 |
| minimizer 集約 (済) | `hoeffding_minimizer_ge` (`HoeffdingTradeoff.lean:236`) | `(P₁ P₂ : α → ℝ) (hP₁_pos hP₂_pos : ∀ a, 0 < ·) (_hP₁_sum hP₂_sum : ∑ = 1) (alpha) (_h_alpha_nn) {Qstar} (hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha) (hQs_pos : ∀ a, 0 < Qstar a) (hQs_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂) {P} (hP_mem : P ∈ hoeffdingConstraintSet P₁ alpha) (hP_pos : ∀ a, 0 < P a)` | `klDivPmf Qstar P₂ ≤ klDivPmf P P₂` | **既に publish 済 0-sorry**. C-2 の `h_minimizer` (型 c に対し) はこれを `P := (c/n)` で呼ぶだけ |
| minimizer 達成性 (済) | `hoeffdingE2_attained` (`Chernoff.lean:310`) | `(P₁ P₂ : α → ℝ) (hP₁_pos hP₂_pos : ∀ a, 0 < ·) (hP₁_sum : ∑ = 1) (alpha) (h_alpha_nn : 0 ≤ alpha)` | `∃ Qstar ∈ hoeffdingConstraintSet P₁ alpha, hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂` | Qstar 取り出し |
| constraint set 凸 (済) | `hoeffdingConstraintSet_convex` (`HoeffdingTradeoff.lean:193`) | `(P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (alpha)` | `Convex ℝ (hoeffdingConstraintSet P₁ alpha)` | Pythagoras `hK_conv` |
| ⊆ simplex (済) | `hoeffdingConstraintSet_subset_stdSimplex` (`Chernoff.lean:286`) | `(P₁ : α → ℝ) (alpha)` | `hoeffdingConstraintSet P₁ alpha ⊆ stdSimplex ℝ α` | Pythagoras `hK_sub` |
| **Qstar full-support** | — (`hoeffdingE2_minimizer_full_support`) | ❌ **不在** (L-H4) | — | **両側必須の `hQs_pos`. 自作 #1 (最大 gap)** |
| boundary 域での Qstar 構成 | `hoeffdingE2_minimizer_at_boundary_alpha_ge_kl` (`HoeffdingSandwichBody.lean:228`) | `(P₁ P₂) (hP₁_pos hP₂_pos hP₁_sum hP₂_sum) {alpha} (h_alpha_nn) (h_alpha_ge : klDivPmf P₂ P₁ ≤ alpha)` | `∃ Qstar ∈ K, hoeffdingE2 = klDivPmf Qstar P₂ ∧ IsHoeffdingMinimizerFullSupport Qstar` | **🟢 α ≥ klDivPmf P₂ P₁ 域では Qstar = P₂ full-support 確定済** → L-H4 縮退案の足場 |

---

## E. AEP / Type I 制御 (achievability C-5 の自前要素) + Tendsto 整地

| 概念 | 既存 API (file:line) | signature 要点 | discharge での扱い |
|---|---|---|---|
| iid joint typical 質量→1 | `typicalSet_prob_tendsto_one` (`AEP.lean:375`) | `μ.map (jointRV Xs n) = P^n` 形の AEP, `μ {typical} → 1` | Type I 制御 (`P₁^n(⋃ T_c) ≥ 1-alpha`) の参照テンプレ. **Sanov の type-class union とは set 形が違う** (typicalSet は entropy band, 我々は KL≤alpha union) ので**直接流用不可、自作 ~30-50 行** |
| typical 質量下界 | `typicalSet_prob_ge` (`AEP.lean:1403`) | (P^n(typical) ≥ 1-δ 系) | 同上参照 |
| Stein typical P 質量→1 | `steinTypicalSet_P_prob_tendsto_one` (`Stein.lean:275`) | `[…IID setup…]` `Tendsto (μ {jointRV ∈ steinTypicalSet}) atTop (𝓝 1)` | converse 側で既に `steinOptimalBeta_log_le_of_strong_converse` 内部が使用 |
| liminf 下界化 | `Filter.Tendsto.eventually_ge` / `tendsto_of_le_liminf_of_limsup_le` (Mathlib `Topology.Order.LiminfLimsup`) | — | 既に `hoeffding_tradeoff_with_hypothesis` で使用済 |
| 両 boundedness (済) | `hoeffding_rate_isBoundedUnder_le/ge` (`HoeffdingSandwich.lean:195, 90`) | `(P₁ P₂) (full support / sum / alpha 域)` | 既に内部 discharge 済 (`hoeffding_tradeoff_sandwich` が両 boundedness 供給) |
| `Σ ∏ P (x i) = (Σ P)^n` | `sum_prod_pi_eq_pow_sum` (`HoeffdingTradeoff.lean:120`) | `(P : α → ℝ) (n)` | acceptance region の Type I/II 和の整形 |
| Measure.pi singleton | `Measure.pi_singleton` (Mathlib) + `ENNReal.toReal_prod` | — | `P₂^n {x} = ∏ P₂(x i)` 整形 (Sanov 結論 `P₂^n(⋃)` ↔ `steinBetaSet_pmf` の `Σ ∏`) |

---

## 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`sanov_ldp_equality` / `sanov_ldp_lower_bound_pointwise`** (`SanovLDPEquality.lean:1243, 1071`):
  - `[IsProbabilityMeasure Q]` — `pmfToMeasure P₂` で自動充足 (instance あり)
  - `hQpos : ∀ a, 0 < Q.real {a}` — `pmfToMeasure_real_singleton` + `hP₂_pos` で `0 < P₂ a`
  - `hP_full : ∀ a, 0 < P a` — **`P := Qstar` の full-support が要る ⇒ L-H4 の `hQs_pos` がここに直撃**
  - `E : ∀ n, Finset (TypeCountIndex α n)` — acceptance region の Finset 化が必須 (Decidable 性は classical で逃げる)
  - `h_in_E : ∀ᶠ n, roundedTypeIndex P n ∈ E n` — Qstar∈K の rounding 誤差クリア (~10-20 行, **`(roundedTypeIndex Qstar n / n) ∈ K` の eventually 性が非自明: KL の連続性 + roundedTypeIndex_tendsto_vec 経由**)
  - `h_minimizer` (equality 版のみ) — `hoeffding_minimizer_ge` で供給

- **`csiszar_pythagoras_inequality`** (`CsiszarProjection.lean:449`):
  - `hQ_pos : ∀ a, 0 < Q a` (= P₂ full-support, OK), `hQs_pos` (= Qstar full-support, **L-H4**), `hP_pos` (= 対象 Q full-support)
  - `hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar` — `hoeffding_minimizer_ge` の証明内で既に構築済 (`hQs_isMinOn`)
  - **3 つの `*_pos` が全部 full-support 要求** → converse 側で「任意 test の Q が full-support」を要する箇所で plumbing 注意

- **`steinOptimalBeta_log_le_of_strong_converse` / `stein_strong_lemma`** (`StrongStein.lean:395, 498`):
  - 巨大な IID プロセス setup: `(μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : ℕ → Ω → α) (hXs) (hindep : Pairwise … ⟂ᵢ[μ] …) (hident : ∀ i, IdentDistrib …) (hMap : μ.map (Xs 0) = P) (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi …)` — **`Ω`/`Xs` の標準 IID プロセスを自前で供給する必要** (`Measure.pi` を Ω に取れば canonical に作れるが ~20-30 行の boilerplate)
  - `hPQ : P ≪ Q` (= Qstar_meas ≪ P₂_meas, full-support 同士なら `AbsolutelyContinuous` 自明だが要証明 ~5 行)
  - `hPpos hQpos : ∀ x, 0 < ·.real {x}`

- **`klDivSumForm_eq_toReal_klDiv`** (`Sanov.lean:252`): `hPQ : P ≪ Q` + `hQpos`. converse で `E2 = (klDiv Qstar_meas P₂_meas).toReal` を作る橋に必須。

---

## 自作が必要な要素 (優先度順)

1. **`hoeffdingE2_minimizer_full_support`** (Qstar full-support) — **最大 gap, L-H4**
   - 推奨: log-singularity gradient 引数 (atom 0 で `klDivPmf · P₂` の方向微分が `-∞` → Qstar が min なら全 atom 正)。
   - 工数: 30-50 行 (`HasDerivAt` + `negMulLog` の 0 近傍劣微分)。
   - 落とし穴: `klFun` の `x log x` 項の x→0+ 劣微分。Mathlib `Real.hasDerivAt_negMulLog` 系を当てる。
   - **代替**: §撤退ライン参照 (boundary α 域に限定すれば `hoeffdingE2_minimizer_at_boundary_alpha_ge_kl` で full-support 確定済、L-H4 を回避)。

2. **acceptance region `E_n*` の Finset 構成 + `h_in_E`** (achievability C-3/C-4)
   - 推奨: `E_n* := (univ : Finset (TypeCountIndex α n)).filter (fun c => decide ((c/n) ∈ K))` (classical decidable)。
   - `h_in_E`: `roundedTypeIndex Qstar n ∈ E_n*` を `(roundedTypeIndex Qstar n / n) ∈ K` の eventually 性 (KL 連続 + `roundedTypeIndex_tendsto_vec` `SanovLDPEquality.lean:297`) から。
   - 工数: 20-40 行。落とし穴: `K` membership の decidable が `Real` で構造的に出ない → `Classical.dec` + `noncomputable` 伝播。

3. **Type I 制御** `∀ᶠ n, P₁^n(⋃ T_c) ≥ 1 - alpha` (achievability C-5) — **自前 AEP**
   - `⋃ T_c` (KL(·‖P₁)≤alpha union) の補集合が `D(K^c‖P₁) ≥ alpha` 域 → Sanov 上界で `P₁^n((⋃)^c) → 0` 以下。
   - 既存 `typicalSet_prob_*` は entropy-band 形で set が違うので**直接流用不可**。
   - 工数: 30-50 行。落とし穴: alpha 厳密下界 (`alpha < klDivPmf P₁ P₂`) と Type I の `≥ 1-alpha` の方向整合。**最も非自明な数学的 step**。

4. **`steinTypeII_at_level_pmf` ↔ `steinOptimalBeta` (Measure 形) の橋** (converse E)
   - pmf 形の `s : Finset` test ↔ Measure 形の `s : Set + MeasurableSet` test、Type I/II の `Σ∏` ↔ `(·^n ·).toReal`。
   - 工数: 15-30 行。`steinBetaSet` ⊆ `steinBetaSet_pmf` 経由の sInf 単調性。**finite 上は MeasurableSet 自明 (`Set.toFinite`)** なので両 set は実質一致。

5. **Sanov 結論 `P₂^n(⋃ T_c)` ↔ `steinTypeII_at_level_pmf` の値整合** (achievability C-6/C-7)
   - `P₂^n(⋃ T_c).toReal = Σ_{x∈(⋃ T_c を Finset 化)} ∏ P₂(x i)` (Measure.pi_singleton 経由) + steinTypeII ≤ それ。
   - 工数: 15-25 行。落とし穴: `⋃ (Set)` ↔ `Finset.biUnion` の lift。

6. **IID プロセス boilerplate** (converse の Stein setup `μ, Xs, hMap, hMapJoint`)
   - `Ω := ℕ → α`, `μ := Measure.pi Qstar_meas`, `Xs i := fun ω => ω i` の canonical 構成。
   - 工数: 20-30 行。**他の Stein 利用箇所 (例: `ChernoffPerTiltSanov`) に同型 boilerplate がある可能性 → 流用調査推奨**。

**推定合計 Lean 行数**: achievability ~120-180 行 (#1 共有 + #2,3,5) / converse ~80-120 行 (#1 共有 + #4,6 + Pythagoras 適用)。**主定理 wrapper は既存** (`hoeffding_tradeoff_sandwich` `HoeffdingSandwich.lean:290`)。

---

## 撤退ラインへの距離

親 plan ([hoeffding-tradeoff-moonshot-plan.md](hoeffding-tradeoff-moonshot-plan.md)) の撤退ライン:

- **L-H1** (pmf↔Measure bridge > 50 行で Measure 経路統一にピボット): **発動しない**。§B で橋は定義的・薄い (各 ≤ 5 行)。
- **L-H4** (variational hypothesis 形に縮退 = Qstar full-support `hQs_pos` を hypothesis に残す): **既に発動済、本 discharge でも継続**。自作 #1 が書けない限り `h_liminf`/`h_limsup` は full-support を hypothesis で取らざるを得ない。
- **L-HP1** (Type I 制御 自作 plumbing > 30 行): **発動リスク高** (自作 #3 が 30-50 行見込み)。
- **L-HP2** (Type I 自前 AEP > 50 行 → `stein_achievability` Qstar 流用に縮退): #3 が 50 行超なら発動。
- **L-HP3** (`stein_strong_lemma` Qstar 流用 + bridge > 30 行 → 弱 `stein_lemma` + ε 外側ループ): #4,#6 が 30 行超なら発動。

**新規縮退案 (撤退ライン L-H4-FB: boundary α 域への限定)**:
- `hoeffdingE2_minimizer_at_boundary_alpha_ge_kl` (`HoeffdingSandwichBody.lean:228`) が **α ≥ klDivPmf P₂ P₁ 域で Qstar = P₂ full-support を無条件で供給済**。
- ⇒ 自作 #1 (L-H4) を**回避**して、`alpha ∈ [klDivPmf P₂ P₁, 1)` の **boundary 域に限定した hypothesis-free `hoeffding_tradeoff`** を先に publish できる。
- この域では `hoeffdingE2 = klDivPmf P₂ P₂ = 0` (or boundary 値) で achievability/converse が degenerate に簡単化する可能性あり (`hoeffdingE2_eq_zero_at_alpha_ge_kl` `HoeffdingSandwichBody.lean:194` 参照)。
- **推奨**: full 域の `h_liminf`/`h_limsup` discharge を狙う前に、まず boundary 域 unconditional 版で Sanov/Stein 起動 plumbing を検証 (#2〜#6 を full-support 確定の下で先に書ける) → L-H4 を最後に残す。

---

## 着手 skeleton

```lean
-- Common2026/Shannon/HoeffdingSandwichDischarge.lean
import Common2026.Shannon.HoeffdingTradeoff
import Common2026.Shannon.HoeffdingSandwich
import Common2026.Shannon.HoeffdingSandwichBody
import Common2026.Shannon.Chernoff
import Common2026.Shannon.CsiszarProjection
import Common2026.Shannon.SanovLDPEquality
import Common2026.Shannon.StrongStein
import Common2026.Shannon.KLDivContinuous
import Mathlib.Topology.Order.LiminfLimsup

namespace InformationTheory.Shannon.HoeffdingSandwichDischarge

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter MeasureTheory
open InformationTheory.Shannon InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.CsiszarProjection
open InformationTheory.Shannon.HoeffdingTradeoff
open scoped BigOperators Topology ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- 自作 #1 (L-H4): Hoeffding minimizer の full-support 性. log-singularity gradient 引数. -/
lemma hoeffdingE2_minimizer_full_support
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha)
    {Qstar : α → ℝ} (hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha)
    (hQs_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂) :
    ∀ a, 0 < Qstar a := by
  sorry

/-- achievability: liminf rate ≥ E2 (Sanov LDP lower bound per-Qstar). -/
theorem hoeffding_tradeoff_achievability
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂) :
    hoeffdingE2 P₁ P₂ alpha ≤
      Filter.liminf (fun n : ℕ =>
        -((1:ℝ)/n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha)) atTop := by
  sorry

/-- converse: limsup rate ≤ E2 (Stein strong converse template + Pythagoras). -/
theorem hoeffding_tradeoff_converse
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂) :
    Filter.limsup (fun n : ℕ =>
        -((1:ℝ)/n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha)) atTop
      ≤ hoeffdingE2 P₁ P₂ alpha := by
  sorry

/-- headline: hypothesis-free Hoeffding tradeoff (achievability + converse を sandwich). -/
theorem hoeffding_tradeoff
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < 1)
    (h_alpha_lt_kl : alpha < klDivPmf P₁ P₂) :
    Tendsto (fun n : ℕ =>
        -((1:ℝ)/n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha)) :=
  HoeffdingSandwich.hoeffding_tradeoff_sandwich P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
    h_alpha_nn h_alpha_lt
    (hoeffding_tradeoff_achievability P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum h_alpha_nn h_alpha_lt_kl)
    (hoeffding_tradeoff_converse P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum h_alpha_nn h_alpha_lt_kl)

end InformationTheory.Shannon.HoeffdingSandwichDischarge
```

> 注: 主定理 `hoeffding_tradeoff` の組み立て (sandwich wrapper) は既存 `hoeffding_tradeoff_sandwich` で完成済なので、残りは **`hoeffding_tradeoff_achievability` / `hoeffding_tradeoff_converse` の 2 本 + L-H4 補題 `hoeffdingE2_minimizer_full_support`** の 3 sorry を埋めるだけ。

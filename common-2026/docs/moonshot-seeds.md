# Moonshot シードカード集

> **Status (2026-05-13)**: 5 シード本体 + A 節 deferred 全件 + C 節 横断改善 全件 + **B 節 (B-1〜B-9 + 全 deferred B-1'/B-1''/B-2'/B-2''/B-5'/B-8'/B-3 Phase A+B/B-3'' Phase C+D) 完全完了**。audit-2026-05 棚卸し完了 (40🟢 / 9🟡 / 0🔴) + reuse-test-2026-05 (n-channel converse 再利用テスト、bridge ゼロ) 合格、両アーカイブは `docs/archive/`。Loomis–Whitney → Slepian–Wolf → AEP (Phase A〜F unified) → Stein (achievability + converse 半分 + liminf/limsup sandwich) → Polymatroid (structure 化込) → MaxEntropy → Pinsker (弱形 + シャープ形) → Brascamp–Lieb (組合せ形) + Hypercube product projection bound + Hypercube edge-boundary (AM-GM + entropy-sharp) → MI chain rule (n 変数 + i.i.d. corollary) → **Channel coding achievability (Cover-Thomas 7.7.1 半分、`R < I ⟹ ∃ code, P_err → 0`)** → Sanov A 形 → Sanov LDP B 形 (upper + equality 形双方向) → Strong Stein → Shannon code per-symbol (sandwich + Kraft 逆向き) → **AEP 完全形 D-3 (Cover-Thomas 3.1.2 完全 4 帰結)** → **Type-class size 下界 E-2 (Cover-Thomas 11.1.3 entropy 形、bridge `n^n/∏c^c = exp(n·H(c/n))`)** を **すべて 0 sorry** で通過。完了済みカードは本ファイルから撤去し、各 plan ファイル (`docs/<family>/*-plan.md`) に履歴を残置。**deferred 全件閉鎖**。未着手 seed は **D 節 (D-1, D-2、D-3 完了)** と **E 節 (E-1, E-3〜E-10、E-2 完了、2026-05-13 起草)**。
>
> 起草時 (2026-05-10): Fano (測度論版) → Shannon converse (3 形) → Han 補集合形 → Han Phase D (subset average / Shearer) まで通った状態を起点に、次のムーンショット候補 5 本をシード化。
>
> ここに書いてあるのは **着手前の seed**。実装着手の判断 = 該当シードを `docs/<family>/<topic>-moonshot-plan.md` に複製 + `docs/moonshot-plan-template.md` で膨らませる。本ファイル自体はカード一覧として保ち、選定が確定したら該当カードに `→ <plan path>` のポインタを書き加える。

---

## 次のシード候補

### D. audit-2026-05 由来 (棚卸し 2026-05-13 起草、未着手)

`docs/audit-2026-05.md` の §4 で 🟡 判定された主定理のうち、scope 拡張が **moonshot 規模**
(数日以上) のものを seed 化。小規模な statement 修復 (full support 除去等) は分岐 B 修復 plan
側の管轄で、本シードには含めない。

- **D-1. Shannon noisy channel coding theorem (capacity reach + max error)** ⏸️ —
  Cover-Thomas 7.7.1 **完全形**。既存 `channel_coding_achievability` (固定 `p`, average error,
  `hp_pos` + `hW_pos`) を出発点に、以下 3 段を載せる:
  1. **入力分布最大化**: `C := sup_p I(p;W)` の存在 (有限 alphabet なら `Continuous` + `IsCompact`
     による max 達成、`I(·;W)` 連続性は `entropy` の連続性 + `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ`
     から導出) + capacity 到達 `R < C ⟹ ∃ p, R < I(p; W)`。
  2. **expurgation (average → max error)**: 既存 codebook `c : Fin M → α^n` の `c.averageErrorProb ≤ ε`
     から、Markov inequality で「上位半分の messages が max error ≤ 2ε」を取り、code の半分
     `M' := M / 2` を捨てて max error 化。rate 微減 `log M' = log M - log 2` は `n → ∞` で吸収。
  3. **full support 仮定の除去** (`hp_pos`, `hW_pos`): 0 確率 atom を持つ p / W に対しても random
     coding を回す。`klDiv = ∞` の場合の縮退ケースで bound が自明成立する形に再定式化、
     または full support な近似列 `p_k → p` で連続性を取る。
  - 既存資産: `ChannelCoding.lean` (706 行、定義) + `ChannelCodingAchievability.lean` (1890 行、
    achievability 半分) + `MIChainRule.lean` (`mutualInfo_iid_eq_nsmul`)。
  - 候補プラン: `docs/shannon/channel-coding-shannon-theorem-plan.md` (新規、`moonshot-plan-template.md`
    で起草)。
  - 関連: 4 つの "弱形 / 強形ペア" (Pinsker / Stein / Sanov / **ChannelCoding ← ここだけ強形未**)
    のうち最後の未充足。audit-2026-05 §4 🟡 #9 として記録。

- **D-2. Channel coding converse (general input form)** ⏸️ —
  Cover-Thomas 7.9 **完全形**。既存 `shannon_converse_single_shot` (uniform input only) を出発点に、
  任意の入力分布で `R > I(p; W) ⟹ ∃ error floor` を示す。expurgation/Fano + `mutualInfo_iid_eq_nsmul`
  で n-channel 形にスケール。audit-2026-05 §4 🟡 #8 として記録。

  **先行成果 (reuse-test-2026-05, 2026-05-13 完了)**: i.i.d. 入力下の converse n-variable 化を
  bridge ゼロで実装、`Common2026/Shannon/ChannelCodingConverse.lean`
  (`channel_coding_converse_iid` 1 本) として publish。`shannon_converse_single_shot_markov_encoder`
  + `mutualInfo_iid_eq_nsmul` の合成だけで到達。これは D-2 plan の出発点として直接利用可能。

  reuse-test 由来の設計判断:
  - **uniform input 仮定の緩和は scope 縮小可**: n-channel スケーリングは single-shot 段で
    uniform を消費し、iid 段は入力分布非依存。general input への拡張は per-symbol I(p; W) の
    取り方 (任意 input law p) のみで、n-channel 部分は uniform から自由 → D-2 で本質的に
    新規となるのは expurgation (uniform 仮定除去) 段のみで、n-channel 段は既存 API 流用で済む。
  - **`mutualInfo_chain_rule_fin` は非 iid 入力で初めて出番**: iid 入力なら `iid_eq_nsmul` が
    直接 `n · I(X_0; Y_0)` を返すため chain rule + per-summand memoryless bound は不要。
    D-2 で general input (averaged distribution) を扱うときに `chain_rule_fin` + memoryless
    channel での per-summand `I(X_i; Y_i | X^{<i}) ≤ I(X_i; Y_i)` 追加段が必要になる。
    audit §4 🟡 で flag されていた "uniform input scope" が n-channel に本質ではないという
    意味では、修復優先度はむしろ低い (他の 🟡 案件先行が合理的)。

- **D-3. AEP 完全形 (lower bound + 確率収束)** ✅ (2026-05-13) →
  [docs/shannon/aep-full-form-plan.md](shannon/aep-full-form-plan.md) — Cover-Thomas
  3.1.2 **完全 4 帰結** を `Common2026/Shannon/AEP.lean` 末尾 (Phase H, 211 行追加) で
  publish。3 補題:
  - `typicalSet_prob_ge`: 点別下界 `exp(-n(H+ε)) ≤ (μ.map (jointRV Xs n)).real {x}`
    for `x ∈ T_ε^n` (既存 `typicalSet_prob_le` の方向反転鏡像、上側不等式
    `(∑ pmfLog)/n - H < ε` を使用)
  - `typicalSet_card_ge`: サイズ下界 `(1-η)·exp(n(H-ε)) ≤ |T_ε^n|` whenever
    `μ.real(T) ≥ 1-η` (`typicalSet_prob_le` + 確率質量保存 `μ(T) = ∑_{x∈T} p(x)`
    via `sum_measureReal_singleton`)
  - `typicalSet_card_ge_eventually`: eventually-large-n 形
    `∃ N, ∀ n ≥ N, (1-η)·exp(n(H-ε)) ≤ |T_ε^n|` (上記 + `typicalSet_prob_tendsto_one`
    + `ENNReal.continuousAt_toReal` で ℝ≥0∞ → ℝ bridge)

  既存 `typicalSet_prob_le` / `typicalSet_card_le` / `typicalSet_prob_tendsto_one`
  と合わせ Cover-Thomas 3.1.2 (a)(1)(2) + (b)(3)(4) を完全充足。**full support 仮定の
  除去は scope deferred** (`Real.exp_log (hpos x)` で本質的に使用、`log 0 = 0` 規約では
  `exp 0 = 1 ≠ 0` で形式統一不能、判断ログ参照)。audit-2026-05 §4 🟡 #4 解消。

### E. Cover-Thomas 系列拡張 (2026-05-13 起草、未着手)

`B 節 + D 節` 完了後の自然な次の伸び代を「強形/弱形ペア完結」「achievability/converse ペア完結」
「i.i.d. → stationary 一般化」「discrete → continuous 枝分かれ」「横断 utility」の 5 軸で 10 本。
先行 utility 群 (E-2, E-6, E-7) を置くと後続 (E-1, E-3, E-5) が大幅短縮される依存関係。

- **E-1. Channel coding strong converse (Wolfowitz)** ⏸️ —
  Cover-Thomas 7.9 strong form。既存 `shannon_converse_single_shot` (`Converse.lean` 240 行) は
  **弱形** (`R > C ⟹ liminf P_err > 0`) のみ。`R > C ⟹ ∀ ε, eventually P_err > 1-ε` の
  strong 形を追加。Strong Stein (`StrongStein.lean` 641 行) の channel coding 対形 — これで
  4 つの弱形/強形ペア (Pinsker / Stein / Sanov / **ChannelCoding**) のうち最後が揃う (D-1
  achievability 強形と相補)。経路: Strong typicality (E-7 依存) または LLR-typicality
  (Strong Stein 経路の再利用)。見積 中量 (~800 行)。

- **E-2. Method of types: type-class size lower bound** ✅ (2026-05-13) →
  [docs/shannon/type-class-lower-bound-plan.md](shannon/type-class-lower-bound-plan.md) —
  `typeClassByCount_card_ge_entropy`: `(n+1)^{-|α|} · exp(n · H(c/n)) ≤ |T_c|`
  (Cover-Thomas 11.1.3 size 下界、`H(c/n) := -∑ (c/n)·log(c/n)` 経験分布 entropy)。
  既存 `SanovLDPEquality.lean:705` `typeClassByCount_card_ge` (生形 `n^n / ∏ c^c`) に
  bridge identity `n^n / ∏ c^c = exp(n · H(c/n))` を加えるだけで取得。
  `Common2026/Shannon/TypeClassLowerBound.lean` (181 行)、新規定義 `entropyByCount` 含む。
  per-atom `c · log(c/n) = c · log c - c · log n` を `Nat.eq_zero_or_pos` 分岐 (`c = 0` で
  両辺 0、`c > 0` で `Real.log_div`) で proof、Stirling 依存なし。
  **横断 utility** として E-1 / E-5 / E-3 の前段に置く価値あり、`SanovLDPEquality`
  Stein 経路を直接 multinomial 経路で書き直す独立代替路の出発点としても再利用可。

- **E-3. Rate-distortion theorem (achievability)** ⏸️ —
  Cover-Thomas 10.5。`R(D) := inf {I(X; X̂) : 𝔼 d(X, X̂) ≤ D}` を新規定義 + 達成可能性
  `R > R(D) ⟹ ∃ code, 𝔼 d ≤ D + ε`。distortion measure `d : α → β → ℝ≥0` を導入。
  Random codebook + joint typical encoder (B-3'' lossy mirror)。
  `ChannelCodingAchievability.lean` (1890 行) の probabilistic-method 機構を
  **そのまま流用可** (codebook = β^M、ambient = α-source、encoder の選択 ≠ decoder)。
  候補プラン: `docs/shannon/rate-distortion-achievability-plan.md`。見積 重量 (~2000 行 / 4-6 週)。

- **E-4. Rate-distortion converse** ⏸️ —
  Cover-Thomas 10.4。`𝔼 d(X^n, X̂^n) ≤ D ⟹ rate ≥ R(D)`。Fano 経路 + DPI on `d` + MI chain rule
  (`MIChainRule.lean`)。E-3 と pair で完結。`Converse.lean` のパターン再利用。
  見積 軽量 (~500 行)。E-3 とどちらを先にしても独立。

- **E-5. Slepian–Wolf achievability** ⏸️ —
  Cover-Thomas 15.4。既存 `SlepianWolf.lean` (496 行) は **single-shot converse の 3 bound のみ**。
  `R_X > H(X|Y), R_Y > H(Y|X), R_X + R_Y > H(X, Y)` の rate region に対する
  **random binning + joint typicality decoder** 達成可能性を追加。E-7 (strong typicality) があると
  素直、weak typicality 経路でも書ける。`CondMutualInfo.lean` + `MIChainRule.lean` を再利用。
  見積 中量強形 (~800 行)。

- **E-6. Csiszár I-projection / Pythagorean identity** ⏸️ —
  Cover-Thomas 11.6.1, 11.6.4。凸閉集合 `Π ⊆ Δ(α)` 上で `Q* := argmin_{P ∈ Π} D(P‖Q)` の存在
  + 一意性 + `P ∈ Π ⟹ D(P‖Q) = D(P‖Q*) + D(Q*‖Q)` Pythagorean identity。
  `klDiv` の strict convexity (現状 sharp Pinsker の `klFun_sharp_lower` 延長) +
  Mathlib `IsClosed.exists_forall_le` (compact 上 inf 達成)。**Sanov LDP / Gibbs / hypothesis testing
  の統一幾何**で、`SanovLDP` / `Stein` / `MaxEntropy` への横断 corollary 群を吐ける。
  見積 中量 (~600 行)、**横断 utility**。

- **E-7. Strong typicality** ⏸️ —
  Cover-Thomas 11.2。`A^{*n}_ε := {x^n : ∀ a, |(1/n) N(a|x^n) - P(a)| ≤ ε}` 定義 + 3 主定理
  (`P^n(A^*) → 1`、size sandwich、joint version)。既存 weak typicality (`AEP.lean` 1388 行) と
  並立。`SanovLDP.lean` の `TypeCountIndex` (`α → Fin (n+1)`) を流用、`A^*` は `∥c/n - P∥_∞ ≤ ε` 形。
  Slepian–Wolf achievability (E-5) / Channel coding strong converse (E-1) の前段。
  見積 中量 (~700 行)、**横断 utility**。

- **E-8. Shannon–McMillan–Breiman theorem (stationary ergodic AEP)** ⏸️ —
  Cover-Thomas 16.8。定常エルゴード過程で `-(1/n) log P(X_1,…,X_n) → H(𝒳)` a.s.。既存
  i.i.d. AEP (`AEP.lean`) を一般化。Mathlib `MeasureTheory.Ergodic` + Birkhoff (`ergodic_iff_ae_tendsto`)
  + entropy rate `H(𝒳) := lim H(X_n | X_1, …, X_{n-1})` (定常性で存在) の machinery。
  重量、Mathlib stationary process の整備度に依存 (~1500 行)。Lempel–Ziv (将来 seed) の前段。

- **E-9. Differential entropy + Gaussian max-entropy** ⏸️ —
  Cover-Thomas 8.1, 8.6.1, 9.6 setup。`h(X) := -∫ f log f dx` 定義 + 基本性質
  (translation invariance / scaling) + 与えられた分散下で Gaussian `𝒩(μ, σ²)` が h を最大化
  (Lagrange / KL ≥ 0)。Mathlib `ProbabilityTheory.entropy` は `klDiv μ counting` 経由で
  **discrete 専用**、`differentialEntropy` は新規定義 (`MeasureTheory.gaussianReal` 上に)。
  **現プロジェクトの discrete 一辺倒からの最大の枝分かれ**で、Gaussian channel capacity
  (Cover-Thomas 9.1) への入り口。見積 重量 (~1500 行)、Mathlib 上流 PR 候補多数。

- **E-10. DMC capacity is unchanged by feedback (C_FB = C)** ⏸️ —
  Cover-Thomas 7.12。feedback あり DMC (`X_i = f_i(M, Y_1, …, Y_{i-1})`) でも capacity は同じ。
  Converse 段で `I(M; Y^n) ≤ n·C` を chain rule + memoryless 性で示すが、**feedback 下でも**
  `I(X_i; Y_i | X^{<i}, Y^{<i}) ≤ I(X_i; Y_i)` が memoryless 性から従う点が key。
  `MIChainRule.lean` の feedback-version 派生。**驚き定理**かつ軽量 (~400 行)。
  D-2 (channel coding general converse) と組み合わせると "feedback も使えない" が出る。

### B. 新シード入口 (5 シード完了で開いた)

- **Sanov の定理** ✅ (A 形 2026-05-12) → [docs/shannon/sanov-moonshot-plan.md](shannon/sanov-moonshot-plan.md) — `typeClass_Qn_le` / `typeClass_Qn_le_klDiv`: 有限アルファベット上で `Q^n(T(P)) ≤ exp(-n · klDivSumForm P Q)` (Cover-Thomas 11.1.4)。`klDivSumForm` 形と `(klDiv P Q).toReal` 形両方を publish。`Common2026/Shannon/Sanov.lean` (319 行)。Stein converse `steinTypicalSet_Q_prob_le` の特化 (片側 inequality → 両側 equality) で多項係数 / `|T(P)| ≤ exp(n·H(P))` を回避。
- **B-1'. Sanov LDP B 形 upper bound** ✅ (2026-05-12) → [docs/shannon/sanov-ldp-b-plan.md](shannon/sanov-ldp-b-plan.md) — `sanov_ldp_upper_bound`: 任意 `E : ∀ n, Finset (TypeCountIndex α n)` で各 `c ∈ E n` が `D ≤ klDivIndex c n Q` を満たすとき、任意 `ε > 0` で eventually `(1/n) log Q^n(⋃ c ∈ E n, typeClassByCount c) ≤ -D + ε` (Cover-Thomas Theorem 11.4.1 main statement)。`Common2026/Shannon/SanovLDP.lean` (550 行)。`TypeCountIndex α n := α → Fin (n+1)` で polynomial bound `|·| = (n+1)^|α|`、`typeClassByCount_Qn_le` (index 形 A、A 形 `typeClass_Qn_le` の Stein 経路書き直し)、`typeClassByCount_union_Qn_le_inf` (union 形)、`log_succ_div_tendsto_zero` (`Real.isLittleO_log_id_atTop` 経由) を経由。多項係数 `Nat.multinomial` 経路は不採用、A 形と整合 (`c (x_i) ≥ 1` 観察で `hPpos` 仮定回避)。**LDP equality 形** (`lim (1/n) log Q^n = -inf D` の双方向) は **B-1'' で完了** (2026-05-12、行 `B-1''` 参照)。
- **B-2. Hypercube edge isoperimetry / Han-Bregman bound** ✅ (singleton-cover 形) → [docs/shannon/shearer-cover-bundle-plan.md](shannon/shearer-cover-bundle-plan.md) — `hypercube_product_projection_bound`: 任意 `A ⊆ α^n` (`A.Nonempty`) で `|A| ≤ ∏ i, |π_{{i}}(A)|`。Brascamp–Lieb の `S i := {i}` / `k := 1` 特殊形として Phase C corollary。
- **B-2'. Hypercube edge-boundary 形 (Han-Bregman AM-GM 形)** ✅ (2026-05-12) → [docs/shannon/hypercube-edge-boundary-plan.md](shannon/hypercube-edge-boundary-plan.md) — Boolean cube `Fin n → Bool` 上の coordinate-flip pair で `edgeBoundaryCount A` を直接定義 (Mathlib `SimpleGraph.edgeBoundary` 既存なく `Sym2` 回避)。`Common2026/Shannon/HypercubeEdgeBoundary.lean` (692 行)。主結果 `edgeBoundary_ge_AMGM`: `A.Nonempty` のもとで `2n · |A|^{(n-1)/n} ≤ |∂_e A| + n · |A|` (ℝ, 整数差を `+` で回避)。鍵 counting identity `edgeBoundary_count_eq`: `|∂_e A| + n |A| = 2 Σ_i |π_{≠i}(A)|` を, 各 `i` での fibre size ∈ {1,2} 分類 (`Finset.card_eq_sum_card_fiberwise`) + 4-case 結合 (membership of two extensions in `A`) で proof。Phase B は LW (`loomis_whitney`) + AM-GM (`Real.geom_mean_le_arith_mean_weighted` + `Real.finsetProd_rpow`) の corollary。entropy-sharp 形 (`|∂_e A| ≥ |A|(n - log₂ |A|)`) は **B-2'' で完了** (2026-05-12、行 `B-2''` 参照)。`SimpleGraph` 構造 + `boxProd` n-fold は本 plan で **持ち込まず**, 上流 Mathlib PR (Boolean cube as `K_2 □ K_2 □ ...`) に分離可能。
- **Channel coding theorem (achievability)** ✅ (2026-05-12 完全閉鎖、Phase A〜D 全段) → [docs/shannon/channel-coding-achievability-plan.md](shannon/channel-coding-achievability-plan.md) + [docs/shannon/channel-coding-phase-cd-plan.md](shannon/channel-coding-phase-cd-plan.md) — DMC = `Kernel α β` (alias) + `Code` structure + `errorProb` / `averageErrorProb` / `mutualInfoOfChannel` を Phase A で publish。Phase B-(a, b, c) 全 3 bound 完了。**B-3'' (Phase C+D)**: `Common2026/Shannon/ChannelCodingAchievability.lean` (1890 行) で Phase C-(b) `errorProbAt_le_E1_plus_E2` + Phase C-(c) `random_codebook_average_le` (probabilistic-method 形、`codebookMeasure p M n := Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))` + 仮説 `h_match_X` / `h_match_Z` / `hindepZ_full` で abstract ambient と codebook law を coupling、内部で `codebook_marginal_one` / `codebook_marginal_two` Fubini-collapse 補題経由) + Phase C-(d) `exists_codebook_le_avg` (probabilistic-method 形 pigeonhole) + Phase D-(b) 主定理 `channel_coding_achievability` (Cover-Thomas Theorem 7.7.1 achievability 半分) を **すべて 0 sorry** で publish。precursor として `Common2026/Shannon/IIDProductInput.lean` (399 行、`Ω := ℕ → α × β` 上の `Measure.infinitePi (jointDistribution p W)` i.i.d. ambient bundle を ready-made instance として publish) と entropy-MI bridge (`MIChainRule.lean` + `ChannelCoding.lean` 拡張で `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ` を publish) を新規追加。channel positivity 仮説 `∀ a y, 0 < (W a).real {y}` を主定理 signature に追加。Phase B 全 3 bound は Slepian-Wolf strong typicality 派生に **単独で再利用可能**。
- **Strong Stein** ✅ (2026-05-12) → [docs/shannon/strong-stein-moonshot-plan.md](shannon/strong-stein-moonshot-plan.md) — `stein_strong_lemma`: 任意 `ε ∈ (0,1)` で `Tendsto (-(1/n) * log (steinOptimalBeta P Q n ε)) atTop (𝓝 (klDiv P Q).toReal)`。`Common2026/Shannon/StrongStein.lean` (641 行)。Pinsker / Sanov / information spectrum を **どれも使わず**、既存 `stein_inProbability` (WLLN on LLR) + `steinTypicalSet` plumbing 上に **LLR-typicality (上側)** 経路で構築。鍵: 既存 `steinTypicalSet_Q_prob_le` (LLR 下側で `Q^n(T) ≤ exp(-n(K-δ))`) の **symmetric 対形** `steinTypicalSet_Q_prob_ge` (LLR 上側で `Q^n(T) ≥ exp(-n(K+δ)) · P^n(T)`) を新規構築 → 任意 α-level test に `s ∩ T` 経由で集合論的に延長 → `inf_s` で `steinOptimalBeta` の lower bound → log + 1/n + δ → 0 で `limsup ≤ K`、既存 achievability で `liminf ≥ K`、`tendsto_of_le_liminf_of_limsup_le` で締める。既存 `stein_lemma` (sandwich) は維持、新 file 並立で downstream 影響なし。

### B 追加 (2026-05-11 起草、既存 5 シード + B-1〜B-4 を踏まえた後続)

- **B-5. Pinsker 不等式** ✅ (弱形) → [docs/shannon/pinsker-moonshot-plan.md](shannon/pinsker-moonshot-plan.md) — Bretagnolle-Huber 経路で `tvNorm P Q ≤ √(klDiv P Q).toReal` (定数 1、シャープ Pinsker の定数 1/√2 の √2 倍ゆるい)。有限 alphabet 上で `tvNorm` を新規定義 + `klFun_ge_sub_sqrt_sq` 点別補題 + Cauchy-Schwarz on `|p-q|=|√p-√q|·(√p+√q)`。310 行。
- **B-5'. シャープ Pinsker 不等式** ✅ (2026-05-12) → [docs/shannon/pinsker-sharp-moonshot-plan.md](shannon/pinsker-sharp-moonshot-plan.md) — `tvNorm_le_sqrt_klDiv_div_two`: 有限 alphabet 上で `tvNorm P Q ≤ √((klDiv P Q).toReal / 2)` (Cover-Thomas 11.6 strict 形、定数 1/√2)。`Common2026/Shannon/PinskerSharp.lean` (429 行) を新規追加、弱形 (`Pinsker.lean`) は touch せず並立 publish (`tvNorm` 定義は共有)。鍵は点別 `klFun_sharp_lower`: `3·(t-1)² ≤ 2·(t+2)·klFun(t)` for `t ≥ 0` を **`H(t) := 2(t+2)·klFun(t) - 3(t-1)²` の 3 段微分サインチェイン** (`H''(t) = 4(log t + 1/t - 1) ≥ 0` を `Real.one_sub_inv_le_log_of_pos` 一行で潰す → `H'(1)=0` と `MonotoneOn` で `H'` sign-change at `t=1` → `H(1)=0` と双方向 monotone/antitone で `H ≥ 0` on `(0, ∞)`、`t=0` は別途)。Phase B は per-element `q · klFun(p/q) ≥ 3(p-q)²/(2(p+2q))` + Cauchy-Schwarz on `r := |p-q|`, `f := (p-q)²/(p+2q)`, `g := p+2q` で `(2 TV)² ≤ 3 · Σ f ≤ 2 · KL` を取り、`Σ g = 1 + 2 = 3` を使用。Mathlib に sharp bound 既存なく独立 PR 候補。
- **B-6. 最大エントロピー** ✅ → [docs/shannon/max-entropy-moonshot-plan.md](shannon/max-entropy-moonshot-plan.md) (有限アルファベット上の Gibbs 不等式): `entropy μ X ≤ Real.log (Fintype.card α)`、等号 iff `μ.map X` 一様。Mathlib `klDiv_eq_zero_iff` + identity `klDiv P (uniform) = log|α| - H(P)` だけで終わる軽量シード。LoomisWhitney の `entropy_le_log_image_card` (uniformOn-specific) の **一般 measure 版** で、Shannon converse・LoomisWhitney 両方で暗黙に効いている identity を独立補題として publish。Cover-Thomas 2.6.4。見積 2〜3 日 / 50〜100 行 / 低リスク。**最軽量シード**、Pinsker / Sanov の前段補題としても再利用可。
- **B-7. 相互情報量 chain rule** ✅ → [docs/shannon/mi-chain-rule-moonshot-plan.md](shannon/mi-chain-rule-moonshot-plan.md) — `mutualInfo_chain_rule_fin`: `I(X_0, …, X_{n-1}; Y) = ∑ I(X_i; Y | X_{<i})` の n 変数 chain rule + `mutualInfo_iid_eq_nsmul`: 独立同分布 (Xs, Ys) で `I(X^n; Y^n) = n · I(X_0; Y_0)` (B-3 用 corollary)。Phase A (`mutualInfo` の MeasurableEquiv reshape 不変性、`mutualInfo_map_left/right_measurableEquiv`) + Phase B (Han Phase B と対称な induction、既存 2 変数 `mutualInfo_chain_rule` + `MeasurableEquiv.piFinSuccAbove` + prodComm reshape + `Fin.sum_univ_castSucc`) + Phase C (chain rule 経由ではなく `klDiv_compProd_eq_add` + `measurePreserving_arrowProdEquivProdArrow` で直接 product joint 加法性 + 新規補題 `klDiv_pi_eq_sum`) で 418 行。`Common2026/Shannon/MIChainRule.lean` 新規。B-3 (Channel coding achievability) の前段補題として publish 済。
- **B-8. Shannon コード** ✅ (期待長 sandwich、語長水準) → [docs/shannon/shannon-code-moonshot-plan.md](shannon/shannon-code-moonshot-plan.md) — `shannonCode_expected_length_bounds`: 有限アルファベット上の確率測度 `P` (full support) で、Shannon 語長 `l(a) := ⌈-logb D P(a)⌉₊` が `H_D(P) ≤ E[L_Shannon] < H_D(P) + 1` を達成 (Cover-Thomas 5.4 + 5.8.1)。`Common2026/Shannon/ShannonCode.lean` (354 行)。Phase A 定義 (`entropyD` / `shannonLength` / `expectedLength` / `kraftSum`) + Phase B Kraft 充足 (`shannonLength_kraft_le_one`: 各 `a` で `D^{-l(a)} ≤ P(a)` から Σ ≤ 1) + Phase C Gibbs 下界 (`entropyD_le_expectedLength_of_kraft`: 任意 lengths が Kraft 充足 ⟹ `H_D ≤ E[L]`、`Real.log_le_sub_one_of_pos` 経路で Jensen 回避) + Phase D Shannon 上界 (`expectedLength_shannon_lt_entropyD_add_one`: `Nat.ceil_lt_add_one` で `l(a) < -logb P(a) + 1` を Σ) + Phase E sandwich の 5 段。**Kraft 逆向きは B-8' で別 plan として完了** (下参照)。Mathlib `kraft_mcmillan_inequality` (UD code → Σ D^{-|w|} ≤ 1) は **本シードで直接呼ばず** Shannon 語長の Kraft 充足を独立に証明 (下界に十分)。block source coding theorem (既存 `source_coding_theorem`、AEP Phase F) の **per-symbol 相補形**。
- **B-8'. Shannon コード Kraft 逆向き (prefix code 存在構成)** ✅ (2026-05-12) → [docs/shannon/shannon-code-kraft-reverse-plan.md](shannon/shannon-code-kraft-reverse-plan.md) — `exists_prefix_code_of_kraft`: 任意の `l : α → ℕ` (`∀ a, 0 < l a`) が Kraft 不等式 `Σ_a D^{-l(a)} ≤ 1` (`D ≥ 2`) を充足するとき、長さ `l(a)` の prefix code (injective + prefix-free) が存在 (Cover-Thomas 5.2.1 reverse / McMillan の逆形)。`Common2026/Shannon/ShannonCodeKraftReverse.lean` (498 行)。**Shannon-Fano D-進数構成**を採用 (Greedy with state 不採用): `List.mergeSort` で sort-by-length → 累積和 `slotStart k := Σ_{j<k} D^(L - l(as[j]))` → 各 code-word を `toBaseDLen D (l a) (slot/D^(L-l a))` で定義 (`toBaseDLen` は自前の MSB-first 固定長 base-`D` エンコーダ、Mathlib `Nat.digits` は LSB-first / 可変長で不向き)。Kraft 充足 ⟹ `slotStart |α| ≤ D^L`、prefix-free は `slotStart` の累積 gap + `toBaseDLen_injOn_lt` (digit-by-digit 帰納 with `Nat.mod_pow_succ`) で。Mathlib に prefix code 構造体は **無く** (`UniquelyDecodable` + `kraft_mcmillan_inequality` のみ)、独立 implementation。B-8 (`ShannonCode.lean` 354 行) は touch せず並立 publish。`toBaseDLen` と核補題 (`toBaseDLen_take` / `toBaseDLen_injOn_lt`) は Mathlib 上流 PR 切り出し候補。
- **B-9. Brascamp–Lieb 不等式** ✅ (組合せ形) → [docs/shannon/shearer-cover-bundle-plan.md](shannon/shearer-cover-bundle-plan.md) — `brascamp_lieb_finset`: 任意の cover `(S_i)_{i ∈ ι} ⊆ 𝒫(Fin n)` が各 `j` を `k` 回覆うとき `|A|^k ≤ ∏ i, |π_{S_i}(A)|`。Shearer engine (`HanDShearer.shearer_inequality`) + `entropy_le_log_image_card` + `entropy_uniformOn_eq_log_card` の 3 つを **任意 cover** で並べるだけ。B-2 と engine 共有で bundle 実装、`Common2026/Shannon/BrascampLieb.lean` (198 行)。LW は `S i := univ.erase i` 特殊形だが既存 `LoomisWhitney.lean` 維持 (refactor 見送り)。

### 横断観察 (B 追加シード間)

- **Pinsker → Strong Stein のショートカット** ✅ (B-4 完了で結論 2026-05-12): Pinsker 経由は **不採用**。strong converse の `1/(1-ε)` factor は KL 値の精度ではなく現行 converse の DPI on Bool reduction 構造 (`Pn(s) * (-log Qn s) ≥ (1-ε) * (-log Qn s)`) から来るため、Pinsker `TV ≤ √KL` を使っても解消しない。代わりに **LLR-typicality (上側)** で `Q^n(s) ≥ exp(-n(K+δ)) · (P^n(T) - ε)` を直接取り、既存 `stein_inProbability` (WLLN on LLR) で `P^n(T) → 1` を渡すだけで `limsup ≤ K` が出る。Pinsker / Sanov / information spectrum **どれも不要**で完成 (641 行)。
- **B-2 + B-9 の bundle 化** ✅ (2026-05-11 完了): どちらも Shearer を「異なる cover ファミリ」で呼ぶだけ。実装結果: **`structure ShearerCover` 抽象化は不要だった** — `shearer_inequality` が既に任意 `ι`/`S`/`k` に対して汎用なため、新規定義 `projectionSubset S A` + reshape lemma 1 つ (`jointEntropySubset_le_log_projectionSubset_card`) だけで BL が書ける。LW は既存形を維持 (refactor 見送り、新規 `BrascampLieb.lean` と並立)。Hypercube は singleton cover corollary `hypercube_product_projection_bound` 形のみ提供、edge-boundary 形は **B-2' deferred** に切り出し。
- **B-7 → B-3 短縮化** ✅ (2026-05-12 B-7 完了で実証): 最大の seed B-3 (Channel coding achievability、4〜6 週) を一括着手するより、B-7 (MI chain rule) を独立 plan として先に完了 → B-3 を「jointly typical decoder + 既存 MI chain rule + i.i.d. corollary」の短縮形に再見積もる方が手戻りリスクが低い。実装: chain rule 経路 (Phase B) ≠ i.i.d. corollary 経路 (Phase C、`klDiv_pi_eq_sum` 直接) と判明、Phase C は chain rule に依存せず独立 publish した方が短い (B-3 では i.i.d. corollary 単独で十分)。

- **B-3 i.i.d. product factorization の欠落** ✅ (2026-05-12 Phase B-(c) 完了で解決): Phase B-(c) `jointlyTypicalSet_indep_prob_le` を立てる際の point-wise probability `(μ.map (jointRV Xs n)) {x} = ∏ P(x_i)` を、新規 AEP 補題 `typicalSet_prob_le` (Phase G 節、~100 行) として publish 済。`iIndepFun_iff_map_fun_eq_pi_map` + `iIndepFun.precomp Fin.val_injective` + `Measure.pi_singleton` の 3 つを順に呼ぶだけで Mathlib 既存 API のみで完了。AEP の `Pairwise IndepFun` ベースの既存補題は touch せず並立 publish。本来の見積 200-400 行は ~100 行に縮減 (Mathlib 既存 `iIndepFun_iff_map_fun_eq_pi_map` が想定より直接使えたため)。

### 横断観察 (E 節シード間)

- **E-2 / E-6 / E-7 を先行 utility として**: 軽中量 (~500–700 行) のこの 3 本は単独で publish 価値を持ちつつ、後続 (E-1 / E-3 / E-5) の前段補題として直接効く。順序最適化: **E-2 → E-7 → E-6 → E-1 → E-5 → E-3 → E-4**。
  - E-2 (type-class lower bound) は Sanov LDP equality (`SanovLDPEquality.lean`) の Stein 経由を**直接経路に置き換える**機会で、横断改善 C と同質の整理効果。
  - E-7 (strong typicality) は E-1 (channel coding strong converse) と E-5 (Slepian–Wolf achievability) の **共通前段**。両方を予定するなら E-7 単独 plan を独立に切る方がトータル短い (B-7 → B-3 の前例)。
  - E-6 (Csiszár I-projection) は `klDiv` strict convexity 整備に効く。sharp Pinsker (`PinskerSharp.lean`) の `klFun_sharp_lower` を ConvexOn / StrictConvexOn 形に refactor する機会。
- **強形/弱形ペア 4 種が E-1 で完結**: Pinsker (弱 B-5 / 強 B-5') / Stein (弱 + 強 B-4) / Sanov (A 形 B-1 + LDP B-1'/B-1'') / **ChannelCoding (achievability B-3'' + converse D-2、強形 D-1 + E-1 で完結)**。D-1 (capacity 到達 achievability 強形) と E-1 (capacity 越え converse 強形) を pair で同時着手すると n-channel 設備 (`mutualInfo_iid_eq_nsmul`) を共有して効率的。
- **discrete → continuous の最大ジャンプ (E-9)**: 現状 42 本中 0 本が微分エントロピーに触れていない。Mathlib `MeasureTheory.gaussianReal` 整備度は読み込み未確認、Mathlib に `differentialEntropy` 自体が存在しないため**新規 Mathlib 上流 PR の母体**になりやすい。E-9 単独 publish → Gaussian channel capacity (将来 seed) → EPI (Cover-Thomas 17、将来 seed) の **3 段ロケット**で discrete 集から脱却。
- **E-3 の機構流用 (Channel coding probabilistic-method)**: `ChannelCodingAchievability.lean` の `codebookMeasure` + `codebook_marginal_*` Fubini-collapse 補題群は **lossy source code の rate-distortion (E-3)** に **そのまま**転用可能 (codebook 上の random selection は同じ構造)。E-3 plan 起草時は plumbing を library 化 (`Common2026/Shannon/RandomCodebookProbMethod.lean` 抽出) するか直接 import するか方針判断。

---

## 参照

- 既存 plan:
  - [Fano moonshot](fano/fano-moonshot-plan.md)
  - [Shannon moonshot](shannon/shannon-moonshot-plan.md)
  - [Shannon encoder extensions](shannon/shannon-encoder-extensions-plan.md)
  - [Han moonshot](han/han-moonshot-plan.md)
  - [Han Phase D (subset average / Shearer)](han/han-phase-d-plan.md)
- 5 シード plan + deferred (2026-05-10 / 2026-05-11、全て完了):
  - [Loomis–Whitney moonshot](shannon/loomis-whitney-moonshot-plan.md) ✅
  - [Slepian–Wolf moonshot](shannon/slepian-wolf-moonshot-plan.md) ✅
  - [AEP moonshot](shannon/aep-moonshot-plan.md) ✅ (Phase A〜C)
  - [AEP source coding (Phase D)](shannon/aep-source-coding-plan.md) ✅
  - [AEP achievability (Phase E)](shannon/aep-achievability-plan.md) ✅
  - [Stein moonshot](shannon/stein-moonshot-plan.md) ✅ (Phase A〜B achievability)
  - [Stein converse (Phase A〜C)](shannon/stein-converse-plan.md) ✅
  - [Polymatroid moonshot](han/polymatroid-moonshot-plan.md) ✅ (Phase A〜C)
  - [Polymatroid structure (Phase D)](han/polymatroid-structure-plan.md) ✅
  - [HanD Pi refactor](han/hand-pi-refactor-plan.md) ✅
  - [Max Entropy moonshot (B-6)](shannon/max-entropy-moonshot-plan.md) ✅
  - [Pinsker moonshot (B-5)](shannon/pinsker-moonshot-plan.md) ✅ (弱形 `TV ≤ √KL`)
  - [Pinsker sharp moonshot (B-5')](shannon/pinsker-sharp-moonshot-plan.md) ✅ (シャープ形 `TV ≤ √(KL/2)`)
  - [Shearer cover bundle (B-2 + B-9)](shannon/shearer-cover-bundle-plan.md) ✅
  - [Hypercube edge-boundary (B-2')](shannon/hypercube-edge-boundary-plan.md) ✅ (Han-Bregman AM-GM 形)
  - [Hypercube edge-boundary entropy-sharp (B-2'')](shannon/hypercube-edge-boundary-sharp-plan.md) ✅ (`|∂_e A| ≥ |A|(n − log₂ |A|)`)
  - [MI chain rule (B-7)](shannon/mi-chain-rule-moonshot-plan.md) ✅
  - [Channel coding achievability (B-3)](shannon/channel-coding-achievability-plan.md) ✅ (Phase A + Phase B)
  - [Channel coding Phase C+D (B-3'')](shannon/channel-coding-phase-cd-plan.md) ✅ (Phase C-(a)-(d) + D-(a)-(b) 全段、`channel_coding_achievability` Cover-Thomas 7.7.1 半分)
  - [Sanov moonshot (B-1)](shannon/sanov-moonshot-plan.md) ✅ (A 形 `Q^n(T(P)) ≤ exp(-n·D)`)
  - [Sanov LDP B 形 (B-1')](shannon/sanov-ldp-b-plan.md) ✅ (upper bound `(1/n) log Q^n ≤ -inf D + ε` eventually)
  - [Sanov LDP equality 形 (B-1'')](shannon/sanov-ldp-equality-plan.md) ✅ (`Tendsto (1/n) log Q^n → -inf D` 双方向、`klDivSumForm_ofVec` 経由で Mathlib gap 回避)
  - [Strong Stein moonshot (B-4)](shannon/strong-stein-moonshot-plan.md) ✅ (`Tendsto → K` strict)
  - [Shannon code moonshot (B-8)](shannon/shannon-code-moonshot-plan.md) ✅ (期待長 sandwich、語長水準)
  - [Shannon code Kraft 逆向き (B-8')](shannon/shannon-code-kraft-reverse-plan.md) ✅ (prefix code 存在構成、Shannon-Fano D-進数)
  - [AEP 完全形 (D-3)](shannon/aep-full-form-plan.md) ✅ (Cover-Thomas 3.1.2 完全 4 帰結、`typicalSet_prob_ge` + `typicalSet_card_ge` + eventually-N corollary)
  - [Type-class size lower bound (E-2)](shannon/type-class-lower-bound-plan.md) ✅ (Cover-Thomas 11.1.3 size 下界 entropy 形、`typeClassByCount_card_ge_entropy` via bridge `n^n / ∏ c^c = exp(n·H(c/n))`)
- 雛形:
  - [moonshot-plan-template.md](moonshot-plan-template.md)
  - [subplan-template.md](subplan-template.md)

# Ch.7 Channel coding asymptotic strong converse (Wolfowitz) — Mathlib/in-project 資産インベントリ

> 親計画: [`docs/shannon/channel-coding-strong-converse-plan.md`](channel-coding-strong-converse-plan.md)（単発下界は CLOSED、asymptotic `Pe → 1` は scope-deferred）。本ファイルは asymptotic 接続のための資産棚卸し（docs-only）。
> SoT: `docs/textbook-roadmap.md` Ch.7。実体存在は `#print axioms` / loogle で都度再導出（プローズにキャッシュしない）。

## 一行サマリ

**漸近接続（情報密度の集中ステップ）で使う API のうち、ツールキット（単発下界・Chebyshev・積測度分散加法性・有界 MemLp・pi 因数分解）は ~80% が Mathlib/in-project に既存。自作が必要なのは 2 件のみ — (A) capacity 鞍点 `∀ a, D(W(a)‖q*) ≤ C`（in-project KKT 開発、~200–350 行、Mathlib 壁ではない）、(B) 非 iid・有界分散列の Chebyshev 集中の組み立て（既存 primitive の配線、~150–250 行）。** 真の Mathlib 壁は **0 件**（非 iid WLLN は単発の既製補題が無い＝loogle Found 0 だが、`meas_ge_le_variance_div_sq` + `variance_sum_pi` で組める）。最危険な発見: **`strong_law_ae` / `steinTypicalSet_P_prob_tendsto_one` はともに `hident`（同分布）を要求し、チャネル出力（独立・非同分布）には流用不可** — 既存 iid AEP/LLN 路は使えず、Chebyshev 直叩き路へ切替が必須。

---

## 主定理の最終形（漸近強逆 = Wolfowitz）

memoryless channel `W : Channel α β`（α, β finite）について、message rate `log(M n)/n → R > capacity W` のとき、ブロック長 `n → ∞` で平均誤り確率 `avgPe → 1`。

想定シグネチャ（rate gap は `R > capacity W + δ` 形で固定すると扱いやすい）:

```lean
theorem channelCoding_strong_converse_asymptotic
    {α β : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W]
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n)
    (c : ∀ n, Code (M n) n α β)
    {δ : ℝ} (hδ : 0 < δ)
    -- rate strictly above capacity, eventually:
    (hrate : ∀ᶠ n in atTop, capacity W + δ ≤ Real.log (M n) / n) :
    Tendsto (fun n ↦ ((c n).averageErrorProb W).toReal) atTop (𝓝 1)
```

証明戦略（既存 `channelCoding_average_success_le` に乗せる、6–10 行 pseudo-Lean）:

```
-- p* := capacity achiever (exists_capacity_achiever), q* := outputDistribution p* W, Q := q*^n
-- threshold_n := n*(C + δ/2);  highLLR_m ⟺ (1/n)∑_i [log W(c m i)(y_i) − log q*(y_i)] > C + δ/2
have base := channelCoding_average_success_le (hM n) W (c n) (Q n) threshold_n
-- 1 − avgPe ≤ exp(threshold_n)/M_n + (1/M_n)∑_m Pm(highLLR_m)
have exp_to_0 : exp(threshold_n)/M_n = exp(n(C+δ/2) − log M_n) → 0   -- ∵ log M_n/n ≥ C+δ ⟹ 指数 ≤ −nδ/2
have mean_le_C : ∀ m i, E_{W(c m i)}[llr_i] = D(W(c m i)‖q*) ≤ C       -- ★ capacity 鞍点 (自作 A)
have tail_to_0 : Pm(highLLR_m) ≤ Var/(n(δ/2))² ≤ V_max/(n δ²/4) → 0    -- ★ Chebyshev + variance_sum_pi (自作 B)
-- 1 − avgPe → 0  ⟹  avgPe → 1
```

---

## API 在庫テーブル

### A. 単発下界の土台（in-project、完成済・これに乗せる）

| 概念 | API（file:line） | シグネチャ要点（型クラス前提 verbatim / 結論形 verbatim） | 状態 | 漸近段での扱い |
|---|---|---|---|---|
| 単発成功確率下界 | `channelCoding_average_success_le` (`InformationTheory/Shannon/ChannelCoding/StrongConverse.lean:248`) | 前提（変数ブロック）: `[Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]`。明示引数: `{M : ℕ} (hM : 0 < M) {n : ℕ} (W : Channel α β) [IsMarkovKernel W] (c : Code M n α β) (Q : Measure (Fin n → β)) [IsProbabilityMeasure Q] (threshold : ℝ)`。結論: `(1 - (c.averageErrorProb W).toReal) ≤ Real.exp threshold / M + (1 / M : ℝ) * ∑ m : Fin M, (Measure.pi (fun i ↦ W (c.encoder m i))).real (highLLRSet W c Q threshold m)` | ✅ 既存 | **出発点**。`Q := q*^n`, `threshold := n*(C+δ/2)` を代入 |
| highLLR 集合 | `highLLRSet` (`StrongConverse.lean:43`) | `{M n : ℕ} (W : Channel α β) (c : Code M n α β) (Q : Measure (Fin n → β)) (threshold : ℝ) (m : Fin M) : Set (Fin n → β)` := `{ y | (Measure.pi (fun i ↦ W (c.encoder m i))).real {y} > Real.exp threshold * Q.real {y} }` | ✅ 既存 | log を取り per-letter 和へ落とす対象（下記 C） |
| per-codeword 分解 | `channelCoding_per_codeword_decomposition` (`StrongConverse.lean:121`) | `… (s : Set (Fin n → β)) (hs : MeasurableSet s) : (Measure.pi (fun i ↦ W (c.encoder m i))).real s ≤ Real.exp threshold * Q.real s + (Measure.pi (fun i ↦ W (c.encoder m i))).real (highLLRSet W c Q threshold m)` | ✅ 既存 | 単発下界の内部。直接は再利用しないが highLLR の意味付けの根拠 |
| 平均誤り確率 | `Code.averageErrorProb` (`ChannelCoding/Basic.lean:198`) | `(c : Code M n α β) (W : Channel α β) : ℝ≥0∞` := `if M = 0 then 0 else (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, c.errorProbAt W m` | ✅ 既存 | 結論の `.toReal` 対象 |

### B. capacity 周辺（in-project）

| 概念 | API（file:line） | シグネチャ要点（型クラス前提 verbatim / 結論形 verbatim） | 状態 | 漸近段での扱い |
|---|---|---|---|---|
| 容量 | `capacity` (`ChannelCoding/ShannonTheorem.lean:103`) | `(W : Channel α β) : ℝ` := `sSup ((fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal) '' stdSimplex ℝ α)` | ✅ 既存 | `C := capacity W`。`R > C` の C |
| 容量達成 input 存在 | `exists_capacity_achiever` (`ShannonTheorem.lean:326`) | 前提: `(W : Channel α β) [IsMarkovKernel W]`（`omit [DecidableEq α] [DecidableEq β]`）。結論: `∃ p ∈ stdSimplex ℝ α, IsMaxOn (fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal) (stdSimplex ℝ α) p` | ✅ 既存 | **鞍点自作 (A) の起点**。`p*` を取り `q* := outputDistribution (pmfToMeasure p*) W` |
| `R < C ⟹ ∃p` | `capacity_lt_implies_exists_pmf` (`ShannonTheorem.lean:338`) | `(W : Channel α β) [IsMarkovKernel W] {R : ℝ} (hR : R < capacity W) : ∃ p ∈ stdSimplex ℝ α, R < (mutualInfoOfChannel (pmfToMeasure p) W).toReal` | ✅ 既存 | achievability 側の補題。strong 逆では直接使わない（reference のみ） |
| 出力分布 | `outputDistribution` (`ChannelCoding/Basic.lean:68`) | `(p : Measure α) (W : Channel α β) : Measure β` := `(jointDistribution p W).snd`。inst `IsProbabilityMeasure (outputDistribution p W)`（`Basic.lean:71`、`[IsProbabilityMeasure p] [IsMarkovKernel W]`） | ✅ 既存 | `q* := outputDistribution (pmfToMeasure p*) W`。reference `Q := q*^n = Measure.pi (fun _ ↦ q*)` |
| チャネル相互情報 | `mutualInfoOfChannel` (`ChannelCoding/Basic.lean:81`) | `(p : Measure α) (W : Channel α β) : ℝ≥0∞` := `klDiv (jointDistribution p W) (p.prod (outputDistribution p W))` | ✅ 既存 | 鞍点 = この functional の simplex 上方向微分 ≤ 0 |

### C. 漸近接続ツールキット（Mathlib、情報密度集中の本体）

| 概念 | Mathlib API（file:line） | シグネチャ verbatim（型クラス前提・結論形を括弧含め保持） | 状態 | 扱い |
|---|---|---|---|---|
| **Chebyshev 不等式** | `ProbabilityTheory.meas_ge_le_variance_div_sq` (`Mathlib/Probability/Moments/Variance.lean:397`) | `[IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ} (hc : 0 < c) : μ {ω \| c ≤ \|X ω - μ[X]\|} ≤ ENNReal.ofReal (variance X μ / c ^ 2)` | ✅ 既存 | **集中の主役**。`μ := Pm = Measure.pi (W ∘ encoder)`, `X := (1/n)∑llr`, `c := δ/2` |
| **積測度・分散加法性** | `ProbabilityTheory.variance_sum_pi` (`Variance.lean:447`) | `[Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)} {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] {X : Π i, Ω i → ℝ} (h : ∀ i, MemLp (X i) 2 (μ i)) : Var[∑ i, fun ω ↦ X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i]` | ✅ 既存 | **非 iid 対応の鍵**。`μ i := W (c.encoder m i)`, `X i := llrPmf (W (encoder m i)) q*`。各 `Var ≤ V_max` で `∑ ≤ n·V_max` |
| 独立和・分散加法性（一般） | `ProbabilityTheory.IndepFun.variance_sum` (`Variance.lean:422`) | `{ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} (hs : ∀ i ∈ s, MemLp (X i) 2 μ) (h : Set.Pairwise ↑s fun i j => X i ⟂ᵢ[μ] X j) : variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ` | ✅ 既存 | `variance_sum_pi` のバックエンド。pi で書けないとき用 |
| 有界 ⟹ MemLp | `MeasureTheory.MemLp.of_bound` (`Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:553`) | `[IsFiniteMeasure μ] {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : MemLp f p μ` | ✅ 既存 | `MemLp (llr) 2` を有界性（finite alphabet・`q* > 0` 仮定）から discharge |
| 積測度・singleton 評価 | `MeasureTheory.Measure.pi_singleton` (`Mathlib/MeasureTheory/Constructions/Pi.lean:301`) | `[∀ i, SigmaFinite (μ i)] (f : ∀ i, α i) : Measure.pi μ {f} = ∏ i, μ i {f i}` | ✅ 既存 | highLLR の `Pm.real{y}` / `Q.real{y}` を `∏` に。log で per-letter 和へ（StrongStein:65–76 の既存 template） |
| 座標射影の独立性 | `ProbabilityTheory.iIndepFun_pi` (`Mathlib/Probability/Independence/Basic.lean:784`) | 前提（変数）: `[Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)} {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)] {X : (i : ι) → Ω i → 𝓧 i}`。明示: `(mX : ∀ i, AEMeasurable (X i) (μ i))`。結論: `iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ)` | ✅ 既存 | `variance_sum_pi` 内部で使用済み。明示には不要（pi 版が吸収） |
| 分散の定義 | `ProbabilityTheory.variance` (`Variance.lean:63`) | `(X : Ω → ℝ) (μ : Measure Ω) : ℝ` := `(evariance X μ).toReal` | ✅ 既存 | 表記 `Var[X; μ]` の実体 |

### D. iid 限定で**流用不可**な既存資産（重要な落とし穴）

| 概念 | API（file:line） | シグネチャ verbatim | 状態 | 漸近段での判定 |
|---|---|---|---|---|
| 大数の強法則（a.s.） | `ProbabilityTheory.strong_law_ae` (`Mathlib/Probability/StrongLaw.lean:788`) | `(X : ℕ → Ω → E) (hint : Integrable (X 0) μ) (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) atTop (𝓝 μ[X 0])` | ✅ 存在するが ❌ **流用不可** | `hident`（同分布）必須。チャネル出力 `Y_i ~ W(c(m)_i)` は非同分布なので適用不可 |
| iid LLR-typicality 集中 | `steinTypicalSet_P_prob_tendsto_one` (`InformationTheory/Shannon/Stein/Achievability.lean:278`) | `… (Xs : ℕ → Ω → α) … (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (hMap : μ.map (Xs 0) = P) … : Tendsto (fun n ↦ μ {ω \| jointRV Xs n ω ∈ steinTypicalSet P Q n ε}) atTop (𝓝 1)` | ✅ 存在するが ❌ **流用不可** | 同上 `hident` 必須。Ch.3 AEP 路全体が iid 前提。**非 iid 版は Chebyshev 直叩き（C）で代替** |
| LLR-typicality 下界（per-point exp 因数分解） | `steinTypicalSubset_Q_prob_ge` (`InformationTheory/Shannon/StrongStein.lean:46`) | `(P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPpos …) (hQpos …) {n : ℕ} {δ : ℝ} (A : Set (Fin n → α)) (hAsub : A ⊆ steinTypicalSet P Q n δ) : Real.exp (-((n : ℝ) * ((klDiv P Q).toReal + δ))) * ((Measure.pi (fun _ : Fin n ↦ P)) A).toReal ≤ ((Measure.pi (fun _ : Fin n ↦ Q)) A).toReal` | ✅ 既存（iid product `P^n`） | **テンプレートとしては有用**（pi_singleton→∏→log→∑ の per-point 計算の写経元、StrongStein:65–163）。ただし `P^n`（同分布積）専用、非同分布 `∏ W(c m i)` には直接適用不可 |

### E. 鞍点自作のための隣接機械（in-project、テンプレート）

| 概念 | API（file:line） | シグネチャ verbatim | 状態 | 鞍点 (A) での扱い |
|---|---|---|---|---|
| 離散 KL（PMF） | `klDivPmf` (`InformationTheory/Shannon/CsiszarProjection.lean:61`) | `(P Q : α → ℝ) : ℝ` := `∑ a, Q a * klFun (P a / Q a)`（実体は `klFun` 経由、`klDivPmf_eq_log_diff_sum:240` で log 差和形に） | ✅ 既存 | `D(W(a)‖q*)` の離散表現 |
| セグメント方向微分（固定 Q） | `csiszar_segment_hasDerivAt` (`CsiszarProjection.lean:299`) | `{Q Qstar P : α → ℝ} (hQ_pos : ∀ a, 0 < Q a) (hQs_pos : ∀ a, 0 < Qstar a) : HasDerivAt (fun t : ℝ ↦ klDivPmf ((1 - t) • Qstar + t • P) Q) (∑ a : α, (P a - Qstar a) * (Real.log (Qstar a) - Real.log (Q a))) 0` | ✅ 既存（**固定** reference Q） | **写経元**。鞍点は I(p;W) の方向微分（reference q_p が p と共に動く）なので新計算が要る — テンプレートは強いが直接不可 |
| 1 階最適性条件 | `csiszar_first_order_condition` (`CsiszarProjection.lean:389`) | I-projection 最小化点での `∑ a, (P a − Q* a)(log Q* a − log Q a) ≥ 0`（minimality `φ(0) ≤ φ(t)` から） | ✅ 既存 | **写経元**。`IsMaxOn` ⟹ 方向微分 ≤ 0 の論法をそのまま転用（不等号の向きのみ反転） |

---

## Key-preconditions box（前提事故が起きやすい補題）

- **`meas_ge_le_variance_div_sq`（Chebyshev）**
  - `[IsFiniteMeasure μ]`: `Pm = Measure.pi (W ∘ encoder)` は `IsMarkovKernel W` から `IsProbabilityMeasure`（StrongConverse:70 で既証）⟹ finite。OK
  - `MemLp X 2 μ`: `X = (1/n)∑ llr` の MemLp が必要。**`MemLp.of_bound` で有界性から discharge** だが、有界性には **`q* > 0`（`∀ b, 0 < q*.real {b}`）が必須** — `llr = log W(a)(·) − log q*(·)` の log が `−∞` に飛ばない条件。`q*` は capacity achiever の出力なので **support 全域でなければこの仮定が落ちる**（degenerate チャネルで `q*(b)=0` の b があると llr 未定義）。→ **`q*` 正値性は別途証明 or 仮定として明示が必要**（後述の落とし穴）
  - 結論の `μ[X]`（= 積分 = 平均）は **per-codeword で異なる**: `μ[X] = (1/n)∑_i D(W(c m i)‖q*)`。これが ≤ C であることが鞍点 (A)
- **`variance_sum_pi`**
  - `[∀ i, IsProbabilityMeasure (μ i)]`: `μ i = W (c.encoder m i)`、`IsMarkovKernel W` から各 `W a` は probability。OK
  - `(h : ∀ i, MemLp (X i) 2 (μ i))`: 各 per-letter llr の MemLp（有界、上と同じ `q* > 0` 依存）
  - 形が `∑ i, fun ω ↦ X i (ω i)` 固定 — highLLR の和 `∑_i llr(y_i)` をこの形に整形する糊が要る（`Finset.sum_apply` 系）
- **鞍点 (A) の方向微分（自作）**
  - `IsMaxOn (I(·;W)) (stdSimplex) p*` を **simplex 内部点でない場合に注意**（p* が境界 = ある input の確率 0）。`csiszar_first_order_condition` 同様、片側微分 `t ∈ [0,1]` での `φ(0) ≥ φ(t)` を使い境界を回避できる（segment `(1−t)p* + t δ_a` は t∈[0,1] で simplex 内）
  - `I(p;W) = ∑_x p(x) D(W(x)‖q_p)` 恒等式 + その方向微分が `D(W(a)‖q*) − C` になる計算（q_p の p-依存の微分が相殺する envelope 性）が新規

---

## 自作が必要な要素（優先度順）

### (A) capacity 鞍点 `∀ a : α, (klDivPmf (W a の pmf) (q* の pmf)) ≤ capacity W` 【最重要・load-bearing】

- **推奨実装**: `exists_capacity_achiever` で `p*` を取得 → `q* := outputDistribution (pmfToMeasure p*) W` → セグメント `p_t := (1−t)•p* + t•(Pi.single a 1)` 上で `g(t) := (mutualInfoOfChannel (pmfToMeasure p_t) W).toReal` の `HasDerivAt g (D(W(a)‖q*) − C) 0` を示す → `IsMaxOn` ⟹ 右微分 ≤ 0 ⟹ `D(W(a)‖q*) ≤ C`。
- **テンプレート（gateway-atom 候補）**: `csiszar_segment_hasDerivAt`（CsiszarProjection.lean:299、**固定** reference の klDivPmf 方向微分）+ `csiszar_first_order_condition`（:389、`IsMaxOn`/`IsMinOn` ⟹ 微分符号）。論法骨格はそのまま、不等号の向きを反転。
- **自作行数見積もり**: ~200–350 行。内訳: (i) `I(p;W) = ∑_x p(x)·klDivPmf (W x) q_p` 恒等式（~60 行、`mutualInfoOfChannel_eq_HX_add_HY_sub_HZ`:122 を経由 or klDiv 直接展開）、(ii) 方向微分 `D(W(a)‖q*) − C`（~120 行、q_p の動きを含む chain rule。`csiszar_segment_hasDerivAt` は q 固定なのでこの部分が新規・最難）、(iii) `IsMaxOn` ⟹ ≤ 0（~30 行）。
- **落とし穴**:
  - **`q* > 0`（出力 support 全域）**: 鞍点の log・llr の well-defined 性に必須だが、一般チャネルでは保証されない（degenerate output）。鞍点を `q*(b) = 0` の b で扱うには `D(W(a)‖q*)` の `+∞` 規約と整合させるか、`q* > 0` を仮定として持ち上げる必要。**主定理の hypothesis に `∀ b, 0 < (outputDistribution (pmfToMeasure p*) W).real {b}` を足すのが現実的**（regularity 前提＝OK、load-bearing ではない）。
  - 方向微分の envelope 相殺（q_p の p-依存分の微分が消える）を Lean で出すのが計算重い。`HasDerivAt.sum` + `klFun` の `hasDerivAt_klFun`（CsiszarProjection で使用済）を流用。
- **判定**: **Mathlib 壁ではない**（in-project 機械が揃っている＝「choice (big)」）。`@residual(plan:capacity-saddle-point)` で deferred 化が honest な退避。

### (B) 非 iid・有界分散列の Chebyshev 集中（per-codeword highLLR → 0）【plumbing】

- **推奨実装**: highLLR を `pi_singleton` で `∏` に開き log で `S_m(y) := ∑_i llrPmf (W (c m i)) q* (y_i) > n(C+δ/2)` 形へ（StrongStein:65–163 が写経元）→ `X := fun y ↦ S_m(y)/n`、`μ := Pm`、`μ[X] = (1/n)∑_i D(W(c m i)‖q*) ≤ C`（鞍点 A）→ `meas_ge_le_variance_div_sq` で `Pm{X − μ[X] ≥ δ/2} ≤ Var/(n²(δ/2)²)`、`variance_sum_pi` で `Var = ∑_i Var[llr_i] ≤ n·V_max` ⟹ `≤ 4V_max/(n δ²) → 0`。
- **テンプレート（gateway-atom 候補）**: per-point 整形は `steinTypicalSubset_Q_prob_ge`（StrongStein:46）の `pi_singleton`→`ENNReal.toReal_prod`→`Real.exp_sum`/`Real.log` 系の写経。集中は `meas_ge_le_variance_div_sq` + `variance_sum_pi` 直叩き。
- **自作行数見積もり**: ~150–250 行。内訳: highLLR→LLR 和の同値（~70 行）、per-letter mean=`D`・var 有界（~60 行）、Chebyshev 適用 + `n→∞` で `→0`（~60 行、`tendsto_const_div_atTop_nhds_zero` 系）。
- **落とし穴**:
  - `meas_ge_le_variance_div_sq` は **片側でなく `|·|` 両側**（`{c ≤ |X − μ[X]|}`）。highLLR は片側 `X − μ[X] ≥ δ/2` なので `{X − μ[X] ≥ δ/2} ⊆ {|X − μ[X]| ≥ δ/2}` の包含で繋ぐ（mono、自明）。
  - 平均 `μ[X]` が **per-codeword で動く** ので「全 m 一様に ≤ C」が鞍点 (A) に依存。鞍点なしには tail→0 が出ない（false statement になる）。
  - `V_max`（per-letter LLR 分散の上界）は finite alphabet + `q* > 0` から定数として取れるが、`n` 非依存の一様上界であることを明示要（`Var[llr_i] ≤ (log の値域)²` 型）。
- **判定**: **Mathlib 壁ではない**（全 primitive 既存）。鞍点 (A) を仮定すれば純配線。

### (C) 指数項 `exp(threshold_n)/M_n → 0`【自明・最小】

- `threshold_n = n(C+δ/2)`, `log M_n/n ≥ C+δ` ⟹ `threshold_n − log M_n ≤ −nδ/2` ⟹ `exp(threshold_n)/M_n = exp(threshold_n − log M_n) ≤ exp(−nδ/2) → 0`。`Real.exp` 単調 + `Real.tendsto_exp_atBot` 系。~30 行。落とし穴なし。

### (D) `1 − avgPe → 0 ⟹ avgPe → 1` + `.toReal` 整形【自明】

- 単発下界の左辺は `1 − (avgPe).toReal`。`exp_to_0` と `tail_to_0` で右辺 → 0、`squeeze`（`0 ≤ 1 − avgPe.toReal ≤ →0`）で `1 − avgPe.toReal → 0` ⟹ `avgPe.toReal → 1`。`Tendsto` の算術。~30 行。

**工数感**: (A) が支配的（~1–2 週間、新規 KKT 開発）。(B)(C)(D) は鞍点が出れば ~3–5 日の配線。**親計画の単発下界（CLOSED）に完全に上乗せ可能** — 単発下界の signature 変更は不要。

---

## Mathlib 壁の列挙（`@residual(wall:…)` 候補）

**真の Mathlib 壁は 0 件。** 以下は「単発の既製補題が無い」が、既存 primitive の組み立てで解消する＝壁ではない（過大評価ガード）。

| 想定壁 | loogle 確認 | 判定 | 代替 route |
|---|---|---|---|
| 非 iid（独立・非同分布）有界分散列の WLLN（単発補題） | `"weak_law_of_large_numbers"` → **Found 0**；`"law_of_large"` → `strong_law_ae`（iid 専用）のみ；`"tendsto_average"` → Vitali/density 系のみ（LLN 無し） | **壁ではない（配線）** | `meas_ge_le_variance_div_sq`（Variance.lean:397）+ `variance_sum_pi`（Variance.lean:447）で組む。両者 verbatim 確認済 |
| capacity 鞍点 `∀a, D(W(a)‖q*) ≤ C`（Mathlib 既製） | Mathlib に channel-capacity KKT は不在（`mutualInfoOfChannel` 自体が in-project 定義） | **壁ではない（in-project 自作、template 有）** | `csiszar_segment_hasDerivAt` + `csiszar_first_order_condition` + `exists_capacity_achiever` の写経・転用 |

→ **共有 sorry-lemma 化の推奨**: 鞍点 (A) は「Wolfowitz 強逆」以外にも、将来の channel 系（max-error 強逆、feedback 強逆、type-counting 路）で再利用が見込まれる **唯一の load-bearing 補題**。`InformationTheory/Shannon/ChannelCoding/` 直下に `theorem klDiv_channel_le_capacity (… ) : … ≤ capacity W := by sorry` + `@residual(plan:capacity-saddle-point)` の **単一補題として切り出し**、(B) 以降はそれを呼ぶ構成を推奨（`docs/audit/audit-tags.md`「Shared Mathlib walls: the shared sorry-lemma pattern」に倣う）。ただし wall ではなく **plan** 分類（self-buildable なので）。

---

## 撤退ラインからの距離

親計画 [`channel-coding-strong-converse-plan.md`](channel-coding-strong-converse-plan.md) の状態:

> - asymptotic `Pe → 1` (WLLN-on-LLR 接続) は **scope-deferred**。`highLLRSet` の補集合が `steinTypicalSet` 系に reduce する経路で後続 plan に接続可能。

**plan line 8「highLLRSet の補集合が steinTypicalSet 系に reduce」の verbatim 評価**:
- **部分的に成立、ただし額面どおりではない**。highLLR の補集合 `{y | (1/n)∑llr ≤ (1/n)threshold}` と `steinTypicalSet`（`{x | |(1/n)∑llr − K| < ε}`、両側・中心 `K=klDiv`）は **「LLR 和の集中集合」という形は一致**するが、(i) highLLR は**片側**閾値（`threshold/n ≈ C+δ/2`）、steinTypicalSet は**両側**（中心 `K`）、(ii) steinTypicalSet の中心 `K=klDiv P Q` は **単一の固定 mean**だが、チャネルの per-codeword mean は `(1/n)∑D(W(c m i)‖q*)`（codeword 依存・非同分布）。
- **橋になる StrongStein 補題**: `steinTypicalSubset_Q_prob_ge`（StrongStein:46）の **per-point exp 因数分解計算**（`pi_singleton`→`∏`→`Real.log`→`∑`、StrongStein:65–163）は**整形テンプレートとして再利用可**。ただし収束ステップ（`steinTypicalSet_P_prob_tendsto_one`:278）は **iid `hident` 専用で流用不可** → ここを Chebyshev 直叩き (B) に差し替える。
- **結論**: reduce 経路は「整形は再利用、収束は新規（非 iid Chebyshev）」。額面の「steinTypicalSet にそのまま reduce」は不可だが、**部分写経 + Chebyshev 差し替え**で接続可能（plan の楽観評価をやや下方修正）。

**撤退ライン抵触判定**: 親計画に明示的な撤退ライン（L-* 等）の記載は無く、asymptotic は「後続 plan へ deferred」状態。**新規撤退ラインを提案**:

- **新規撤退ライン R-SC1**: 鞍点 (A) の方向微分（envelope 相殺）が **着手 1 週間以内に `HasDerivAt` 形で出せない**場合 → 主定理シグネチャ（`R > capacity W ⟹ Pe → 1`）は**そのまま維持**し、鞍点補題 `klDiv_channel_le_capacity` のみ `sorry` + `@residual(plan:capacity-saddle-point)` で deferred 化。残り (B)(C)(D) は鞍点を黒箱として配線完了させ、type-check done で commit。
  - **退避出口は sorry + @residual のみ**（鞍点を `*Hypothesis` predicate にバンドルして主定理の前提に積むのは **禁止** = load-bearing hypothesis bundling）。
  - 縮退版の代替主張は作らない（degenerate fallback としては「`q*` 正値・有限 support のチャネルに限定」だが、これは regularity 前提なので主定理 hypothesis に足すだけで縮退ではない）。

---

## 着手のための skeleton

`InformationTheory/Shannon/ChannelCoding/StrongConverseAsymptotic.lean`（新規）の出だし:

```lean
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.StrongConverse
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- ★ load-bearing 自作 (A): capacity 鞍点。容量達成 input `p*` の出力 `q*` に対し、
任意の入力記号 `a` で `D(W(a)‖q*) ≤ capacity W`。共有 sorry-lemma として切り出す。 -/
theorem klDiv_channel_le_capacity
    (W : Channel α β) [IsMarkovKernel W]
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (hp_max : IsMaxOn (fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) p)
    (hq_pos : ∀ b : β, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    (a : α) :
    klDivPmf (fun b ↦ (W a).real {b})
        (fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b})
      ≤ capacity W := by
  sorry -- @residual(plan:capacity-saddle-point)

/-- ★ 配線 (B): 固定 codeword `m` 下の per-codeword highLLR 質量が `n→∞` で 0 へ
（非 iid Chebyshev: meas_ge_le_variance_div_sq + variance_sum_pi）。 -/
theorem channelCoding_highLLR_tendsto_zero
    (W : Channel α β) [IsMarkovKernel W] {δ : ℝ} (hδ : 0 < δ)
    (p : α → ℝ) (hp : p ∈ stdSimplex ℝ α) (hp_max : IsMaxOn _ _ p)
    (hq_pos : ∀ b : β, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    (M : ℕ → ℕ) (c : ∀ n, Code (M n) n α β) :
    -- ∀ ε>0, ∀ᶠ n, ∀ m, Pm(highLLR_m) < ε  （一様、threshold = n(capacity W + δ/2)）
    True := by
  sorry -- @residual(plan:capacity-saddle-point)  -- (A) に依存

/-- 漸近強逆（Wolfowitz）: `log(M n)/n ≥ capacity W + δ` eventually なら `avgPe → 1`。 -/
@[entry_point]
theorem channelCoding_strong_converse_asymptotic
    (W : Channel α β) [IsMarkovKernel W]
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (c : ∀ n, Code (M n) n α β)
    {δ : ℝ} (hδ : 0 < δ)
    (hrate : ∀ᶠ n in atTop, capacity W + δ ≤ Real.log (M n) / n) :
    Tendsto (fun n ↦ ((c n).averageErrorProb W).toReal) atTop (𝓝 1) := by
  sorry -- @residual(plan:capacity-saddle-point)

end InformationTheory.Shannon.ChannelCoding
```

最初の `sorry` を `klDiv_channel_le_capacity`（鞍点）から割り、(B)(C)(D) を鞍点を黒箱として配線するのが着手 M1。鞍点が出れば残りは `channelCoding_average_success_le` への純上乗せ。

---

## まとめ

- インベントリは **`docs/shannon/channel-coding-strong-converse-asymptotic-inventory.md`**（本ファイル）
- 漸近接続ツールキットは ~80% 既存（単発下界・Chebyshev・`variance_sum_pi`・`MemLp.of_bound`・`pi_singleton`）
- 自作 2 件: (A) capacity 鞍点（load-bearing、~200–350 行、`csiszar_*` template 有、**Mathlib 壁ではない**）、(B) 非 iid Chebyshev 集中（plumbing、~150–250 行、鞍点に依存）
- 真の Mathlib 壁 **0 件**（非 iid WLLN は `meas_ge_le_variance_div_sq` + `variance_sum_pi` で組める）
- 最危険: **`strong_law_ae` / `steinTypicalSet_P_prob_tendsto_one` は `hident` 必須でチャネル出力（非同分布）に流用不可** — iid AEP/LLN 路は全面的に使えず、Chebyshev 直叩きへ切替必須
- 撤退ライン R-SC1（鞍点が出ないとき）を新規提案: 主定理シグネチャ維持・鞍点のみ `sorry`+`@residual(plan:capacity-saddle-point)`・hypothesis バンドル禁止
- 着手 ready（単発下界 CLOSED に上乗せ、signature 変更不要）

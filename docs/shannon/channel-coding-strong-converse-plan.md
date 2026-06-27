# Ch.7 Channel coding strong converse (Wolfowitz asymptotic) ムーンショット計画 🌙

**Status**: 漸近版 skeleton commit 済 🚧 — `StrongConverseAsymptotic.lean`（4 sorry、type-check done、commit 6fba2555）。**Phase A は R-SC1 行使 → 子 plan [`capacity-saddle-point.md`](capacity-saddle-point.md) で追跡**。Phase B/C は本 plan 内（`@residual(plan:channel-coding-strong-converse-plan)`）。
**SoT / Parent**: `docs/textbook-roadmap.md` Ch.7 行（"strong converse asymptotic (`Pe → 1`, R > C) は未着手 deferred" を本 plan で active 化）。
**Inventory (SoT, 資産根拠)**: [`channel-coding-strong-converse-asymptotic-inventory.md`](channel-coding-strong-converse-asymptotic-inventory.md)。
実体存在（sorryAx / decl 有無）はプローズにキャッシュせず `#print axioms` / loogle / `rg` で都度再導出。

## Sub-plan 一覧

| 子 plan | 担当 Phase | 状態 |
|---|---|---|
| [`capacity-saddle-point.md`](capacity-saddle-point.md) | Phase A（capacity 鞍点 core） | R-SC1 行使 → 移管 🔄 |

## 進捗

- [x] Phase 0 — Mathlib/in-project API 在庫 ✅ → [inventory](channel-coding-strong-converse-asymptotic-inventory.md)（真壁 0 件、自作 2 件確定）
- [x] 基盤 — 単発 Verdú-Han 下界 `channelCoding_average_success_le` CLOSED ✅（`StrongConverse.lean:248`、signature 変更なしで上載せ可）
- [ ] Phase A — capacity 鞍点 `klDiv_channel_le_capacity` 🔄 **R-SC1 行使 → 子 plan [`capacity-saddle-point.md`](capacity-saddle-point.md)**（body sorry + `@residual(plan:capacity-saddle-point)`、proof-log: yes）
- [ ] Phase B — 非 iid Chebyshev 集中（highLLR 質量 → 0）📋（proof-log: no、Phase A を黒箱配線。`channelCoding_highLLR_tendsto_zero` body sorry）
- [ ] Phase C — 単発下界 + 集中の配線 → headline closure 📋（proof-log: no、`channelCoding_strong_converse_asymptotic` body sorry）

## ゴール / target statement

memoryless channel `W`（α, β finite）で `log(M n)/n ≥ capacity W + δ`（eventually）なら、ブロック長 `n → ∞` で平均誤り確率 `avgPe → 1`（Wolfowitz の強逆）。inventory §主定理の最終形を採用:

```lean
-- 推奨形（容量達成 input p* + その full-support 出力を explicit 引数で受ける）
@[entry_point]
theorem channelCoding_strong_converse_asymptotic
    {α β : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W]
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (c : ∀ n, Code (M n) n α β)
    {δ : ℝ} (hδ : 0 < δ)
    -- ★ regularity precondition（load-bearing でない）: 容量達成 input p* とその full-support 出力
    (p : α → ℝ) (hp : p ∈ stdSimplex ℝ α)
    (hp_max : IsMaxOn (fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) p)
    (hq_pos : ∀ b : β, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    (hrate : ∀ᶠ n in atTop, capacity W + δ ≤ Real.log (M n) / n) :
    Tendsto (fun n ↦ ((c n).averageErrorProb W).toReal) atTop (𝓝 1)
```

- **`p, hp, hp_max`（容量達成 input）の存在は `exists_capacity_achiever`（`ShannonTheorem.lean:326`）で常に保証**されるので、これを explicit に受けるのは scope を狭めない（cleaner-headline 版＝内部で `obtain` し regularity だけ `∃`-形で受ける形は Phase C polish、下記）。
- **`hq_pos`（full-support 出力）が唯一の実質的 regularity 制限**: `llr := log W(a)(·) − log q*(·)` が well-defined（log が `−∞` に飛ばない）ために必須。degenerate 出力（ある `b` で `q*(b)=0`）を除く precondition で、proof の核を仮説に encode していない＝**load-bearing でなく honest**（CLAUDE.md「検証の誠実性」の precondition 側）。

### 退化境界 sanity（statement が偽にならないか先に検討、CLAUDE.md「Verbatim 確認」）

- **M=1**: `log 1 / n = 0`。`capacity W + δ ≤ 0` は `capacity_nonneg`（`ShannonTheorem.lean:145`、`capacity ≥ 0`）+ `δ>0` で偽 → `hrate` 充足不能 → **vacuously true**（avgPe=0 でも矛盾なし）。✅ 生存。
- **zero-capacity channel（C=0、離散版「N=0」相当の useless channel）**: `hrate` は `δ ≤ log(M n)/n`（M 増大で充足可）→ `avgPe → 1` 主張は正しい（入力を判別不能）。✅ 生存。逆の極（noiseless、C=log|α|）も `M > |α|^n` で pigeonhole 衝突 → `avgPe → 1`。✅ 生存。
- **定数符号語（encoder ≡ const）**: 全 message が同一入力 → 出力同分布 → 判別不能 → `avgPe ≥ 1 − 1/M → 1`。✅ 強逆と整合。
- **非 full-support 出力（`q*(b)=0`）**: `llr` が `+∞` で未定義 → `hq_pos` が排除する唯一の境界。これが regularity 仮説が guard する点。

## Approach

解の全体像（per-file breakdown の前の戦略の形）:

> **単発 Verdú-Han 下界（CLOSED）に 3 ピースを上載せして `1 − avgPe → 0` を出す。**
> 単発下界 `channelCoding_average_success_le` は free な reference `Q` + free な `threshold` を取る。
> そこに `Q := q*^n = Measure.pi (fun _ ↦ q*)`（q* = capacity 達成出力）、`threshold := n·(C + δ/2)`
> を代入すると `1 − avgPe ≤ exp(n(C+δ/2))/M_n + (1/M_n)∑_m P_m^n(highLLR_m)`。
> 右辺第1項は `hrate`（rate ≥ C+δ）で `exp(−nδ/2) → 0`。第2項は **情報密度
> `(1/n)∑_i [log W(c m i)(y_i) − log q*(y_i)]` の集中**問題で、(i) per-codeword 平均が
> `(1/n)∑_i D(W(c m i)‖q*)`、(ii) これが **capacity 鞍点** `∀a, D(W(a)‖q*) ≤ C` により一様に
> `≤ C < C+δ/2` なので、Chebyshev で `P_m^n(highLLR_m) → 0`。両項 → 0 を squeeze して `avgPe → 1`。
>
> **危険は 1 点に集中** = 鞍点 `D(W(a)‖q*) ≤ C`（Phase A）。これは Mathlib 壁ではなく
> in-project の方向微分（KKT、envelope cancellation）の新規開発で、`csiszar_*` テンプレートが効く。
> 鞍点が割れれば残り（Phase B/C）は単発下界への純配線。

iid 路は使えない（重要な落とし穴、inventory §D）: `strong_law_ae` / `steinTypicalSet_P_prob_tendsto_one` は
ともに `hident`（同分布）必須で、チャネル出力 `Y_i ~ W(c(m)_i)`（独立だが**非同分布**）に流用不可。
非 iid WLLN は単発の既製補題が無い（loogle Found 0）が、`meas_ge_le_variance_div_sq`
（`Variance.lean:397`）+ `variance_sum_pi`（`Variance.lean:447`）で組める＝壁ではない。

## Phase 0 — API 在庫 ✅（compressed）

完了。資産棚卸しは inventory が SoT。確定事項: 真の Mathlib 壁 **0 件**、自作は (A) capacity 鞍点
（load-bearing、~200–350 行、template 有）+ (B) 非 iid Chebyshev 集中（plumbing、~150–250 行、(A) 依存）の 2 件のみ。
単発下界 signature 変更不要。着手 skeleton（新規 `StrongConverseAsymptotic.lean`）も inventory §着手 skeleton に有り。

## 基盤 — 単発 Verdú-Han 下界 ✅（compressed）

`channelCoding_average_success_le`（`StrongConverse.lean:248`、`@[entry_point]`、CLOSED）:
`(1 − avgPe.toReal) ≤ exp(threshold)/M + (1/M)·∑_m (Measure.pi (fun i ↦ W (c.encoder m i))).real (highLLRSet W c Q threshold m)`。
free `Q`（IsProbabilityMeasure）+ free `threshold` を取る → 漸近版は **代入のみで上載せ**。

## Phase A — capacity 鞍点 `klDiv_channel_le_capacity` 🔄（R-SC1 行使 → 移管）

**移管済**: 詳細（目標補題 signature / gateway-atom-first / 補助 step (i)(ii)(iii) / 退化境界 / 撤退ライン）は
子 plan [`capacity-saddle-point.md`](capacity-saddle-point.md) が SoT。本節は進捗キャッシュのみ（衝突時は子が SoT）。

- **状態**: R-SC1 行使。code 側 `klDiv_channel_le_capacity`（`StrongConverseAsymptotic.lean:54`）+ gateway atom
  `mutualInfo_segment_hasDerivAt`（`:86`）の body が `sorry` + `@residual(plan:capacity-saddle-point)`。type-check done で commit 済（6fba2555）。
- **役割**: Phase B の per-codeword 平均一様上界 `μ[X] ≤ C` を供給する load-bearing core。Phase B/C は本補題を **黒箱**として呼び出す（仮説に積まない）。
- **gateway atom は片側形に訂正**: `HasDerivWithinAt (Set.Ici 0) 0`（two-sided `HasDerivAt` は境界達成点で偽、判断ログ #4・子 plan §Approach）。

## Phase B — 非 iid Chebyshev 集中（highLLR 質量 → 0）📋（Phase A 依存）

**proof-log: no**（既存 primitive の配線。ただし下記落とし穴は本文に残す）。

目標: 固定 codeword 群につき、threshold `= n(C+δ/2)` で `P_m^n(highLLRSet) → 0` を **m について一様** に。

### gateway-atom 候補

- 整形: `Measure.pi_singleton`（`Pi.lean:301`）で `P_m.real{y}`/`Q.real{y}` を `∏` に → `Real.log` で per-letter 和 `S_m(y) := ∑_i llrPmf (W (c m i)) q* (y_i)` へ。**写経元 = `steinTypicalSubset_Q_prob_ge`（`StrongStein.lean:46`、:65–163 の `pi_singleton`→`∏`→`log`→`∑` 計算）**。
- 集中: `X := fun y ↦ S_m(y)/n`、`μ := P_m`。`μ[X] = (1/n)∑_i D(W(c m i)‖q*) ≤ C`（**鞍点 A**）→ `meas_ge_le_variance_div_sq`（`Variance.lean:397`）で `P_m{X−μ[X] ≥ δ/2} ≤ Var/(n²(δ/2)²)`、`variance_sum_pi`（`Variance.lean:447`）で `Var = ∑_i Var[llr_i] ≤ n·V_max` → `≤ 4V_max/(nδ²) → 0`。

### 退化境界 / 前提事故 verify ポイント

- **`meas_ge_le_variance_div_sq` は両側 `|·|`**（`{c ≤ |X−μ[X]|}`）。highLLR は片側 `X−μ[X] ≥ δ/2` → 包含 `{X−μ ≥ δ/2} ⊆ {|X−μ| ≥ δ/2}`（mono、自明）で繋ぐ。
- **平均 `μ[X]` が per-codeword で動く** → 「全 m 一様に ≤ C」は鞍点 (A) に依存。鞍点なしには tail→0 が出ない（false statement になる）。
- `MemLp X 2` は `MemLp.of_bound`（`LpSeminorm/Basic.lean:553`）で有界性から discharge。有界性は **finite alphabet + `hq_pos`** 依存（log の値域有界）。`V_max`（per-letter LLR 分散の上界）は `n` 非依存の一様定数であることを明示要。
- `variance_sum_pi` は形が `∑ i, fun ω ↦ X i (ω i)` 固定 → `S_m` をこの形に整形する糊（`Finset.sum_apply` 系）が要る。

### 撤退ライン R-SC2

Phase A を黒箱とした純配線なので、特定 sub-step（整形 or Chebyshev 適用）が詰まったら **その `have` のみ** `sorry` + `@residual(plan:channel-coding-strong-converse-plan)`（本 plan を指す）。bundling 禁止。鞍点 (A) 由来の `μ[X] ≤ C` は Phase A の補題呼び出しで受ける（仮説に積まない）。

## Phase C — 配線 + headline closure 📋

**proof-log: no**（最終 assembly、自明）。

- [ ] (C-0) `Q := Measure.pi (fun _ ↦ q*)`（`IsProbabilityMeasure` は `outputDistribution` の inst `Basic.lean:71` + `Measure.pi`）、`threshold := n(C+δ/2)` を `channelCoding_average_success_le` に代入。
- [ ] (C-1) exp 項 `exp(n(C+δ/2))/M_n = exp(n(C+δ/2) − log M_n) ≤ exp(−nδ/2) → 0`（`hrate` で指数 ≤ −nδ/2）。~30 行、`Real.tendsto_exp_atBot` 系。
- [ ] (C-2) tail 項 `(1/M_n)∑_m P_m^n(highLLR_m) → 0`（Phase B を m 一様で適用）。
- [ ] (D) squeeze: `0 ≤ 1 − avgPe.toReal ≤ (→0)` → `1 − avgPe.toReal → 0` → `avgPe.toReal → 1`。~30 行、`Tendsto` 算術。
- [ ] (任意 polish) cleaner-headline 版: `p, hp, hp_max` を内部 `exists_capacity_achiever` で `obtain` し、regularity を `(hreg : ∃ p ∈ stdSimplex ℝ α, IsMaxOn … p ∧ ∀ b, 0 < q_p.real {b})` の `∃`-形で受ける variant を別 wrapper として用意。

### 退化境界 verify

target statement §退化境界 sanity（M=1 vacuous / zero-cap・noiseless 両極生存 / 定数符号語整合）を最終形で再確認。`(c n).averageErrorProb W).toReal`（`Basic.lean:198`、`if M=0 then 0 else …`）が `.toReal` 対象であることを確認（`hM` で `M n > 0` なので `if` の else 枝）。

### 撤退ライン R-SC3

最終 assembly は自明なので、詰まったら該当 step を `sorry` + `@residual(plan:channel-coding-strong-converse-plan)`。

## 規模見積 + リスク

| Phase | 内容 | 規模 | リスク |
|---|---|---|---|
| A | capacity 鞍点（KKT、envelope cancellation） | ~200–350 行 / ~1–2 週 | **支配的・最高**。新規方向微分。gateway atom `mutualInfo_segment_hasDerivAt` が割れれば残りは薄い |
| B | 非 iid Chebyshev 集中 | ~150–250 行 / ~3–5 日 | 中。鞍点を黒箱化すれば純配線。両側`|·|`/per-codeword mean/MemLp 有界性が前提事故源 |
| C | 単発下界への配線 + squeeze | ~60 行 / ~1–2 日 | 低。代入 + 極限算術 |

**リスクは Phase A に集中**。A が割れれば B/C は単発下界（CLOSED）への純上乗せ。**R-SC1 行使済**（A を子 plan [`capacity-saddle-point.md`](capacity-saddle-point.md) へ移管、body sorry）→ B/C は鞍点を黒箱として配線、headline は type-check done で commit 可。

## 判断ログ

1. **iid 路 流用不可（確定）**: `strong_law_ae`（`StrongLaw.lean:788`）/ `steinTypicalSet_P_prob_tendsto_one`（`Achievability.lean:278`）はともに `hident`（同分布）必須。チャネル出力は独立だが**非同分布** → 既存 iid AEP/LLN 路は全面不可、**Chebyshev 直叩き（`meas_ge_le_variance_div_sq` + `variance_sum_pi`）へ確定切替**（inventory §D）。
2. **親 plan の楽観評価 訂正**: 旧「`highLLRSet` の補集合が `steinTypicalSet` 系に reduce」は額面誤り。整形（`pi_singleton`→`∏`→`log`→`∑`）は `StrongStein` 写経可だが、**収束 step は iid `hident` 専用で流用不可** → Phase B は Chebyshev 差替（inventory §撤退ラインからの距離）。
3. **`hq_pos`（full-support 出力）を headline regularity hyp として明示**: `llr` well-defined のため必須、proof 核を encode しない＝**load-bearing でない precondition**（honest）。non-full-support 出力が唯一 guard する退化境界。
4. **R-SC1 行使済（Phase A 移管）**: gateway atom が `HasDerivWithinAt` 形で出せず、`klDiv_channel_le_capacity` + `mutualInfo_segment_hasDerivAt` の body を `sorry` + `@residual(plan:capacity-saddle-point)` 化、type-check done で commit（6fba2555）。closure は子 plan [`capacity-saddle-point.md`](capacity-saddle-point.md)。退避口は sorry + @residual のみ（鞍点を `*Hypothesis` predicate に bundle するのは禁止＝load-bearing bundling）。
5. **gateway atom two-sided → 片側 訂正（auditor 検証済）**: `mutualInfo_segment_hasDerivAt` を two-sided `HasDerivAt … 0` で計画していたが機械的に偽（境界達成点 `p a = 0` で `pmfToMeasure` の `ENNReal.ofReal` 負座標クランプにより `t<0` で非確率測度化、corner が立つ。反例 `α=β=Bool, p=δ_false, a=true`）→ 片側 `HasDerivWithinAt (Set.Ici 0) 0` に訂正（code 側 + honesty-auditor 検証済）。target statement §退化境界 sanity の「片側（右）微分 `t=0⁺`」と整合。詳細は子 plan。

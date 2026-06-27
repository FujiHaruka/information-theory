# Ch.7 Channel coding strong converse (Wolfowitz asymptotic) ムーンショット計画 🌙

**Status**: moonshot 完遂 ✅ — headline `channelCoding_strong_converse_asymptotic`（`StrongConverseAsymptotic.lean`）proof done + audited（`@audit:ok`、ファイル全体 0 sorry / 0 @residual、commit `08d18601` headline → `bb21942a` certify）。Phase A/B/C 全 closure。実体（sorryAx-free 等）は `#print axioms` で都度再導出。
**SoT / Parent**: `docs/textbook-roadmap.md` Ch.7 行（"strong converse asymptotic (`Pe → 1`, R > C)" を本 plan で active 化 → 完遂同期済）。
**Inventory (SoT, 資産根拠)**: [`channel-coding-strong-converse-asymptotic-inventory.md`](channel-coding-strong-converse-asymptotic-inventory.md)。
実体存在（sorryAx / decl 有無）はプローズにキャッシュせず `#print axioms` / loogle / `rg` で都度再導出。

## Sub-plan 一覧

| 子 plan | 担当 Phase | 状態 |
|---|---|---|
| [`capacity-saddle-point.md`](capacity-saddle-point.md) | Phase A（capacity 鞍点 core） | done ✅（鞍点 + gateway atom genuine closure） |

## 進捗

- [x] Phase 0 — Mathlib/in-project API 在庫 ✅ → [inventory](channel-coding-strong-converse-asymptotic-inventory.md)（真壁 0 件、自作 2 件確定）
- [x] 基盤 — 単発 Verdú-Han 下界 `channelCoding_average_success_le` CLOSED ✅（`StrongConverse.lean:248`、signature 変更なしで上載せ可）
- [x] Phase A — capacity 鞍点 `klDiv_channel_le_capacity` ✅（子 plan [`capacity-saddle-point.md`](capacity-saddle-point.md) で genuine closure、commit `3db9d443`、proof-log: yes）
- [x] Phase B — 非 iid Chebyshev 集中 `channelCoding_highLLR_tendsto_zero` ✅（Phase A を黒箱配線、commit `9ad30170`）
- [x] Phase C — 単発下界 + 集中の配線 → headline `channelCoding_strong_converse_asymptotic` closure ✅（commit `08d18601`）

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

## Phase A — capacity 鞍点 `klDiv_channel_le_capacity` ✅（compressed）

子 plan [`capacity-saddle-point.md`](capacity-saddle-point.md) が SoT（詳細・退化境界・経緯）。gateway atom
`mutualInfo_segment_hasDerivAt`（片側 `HasDerivWithinAt (Set.Ici 0) 0`、two-sided は境界達成点で偽）の
envelope cancellation が genuine に出て鞍点 `∀a, D(W(a)‖q*) ≤ C` を closure、`klDiv_channel_le_capacity` の `sorry`
除去（commit `3db9d443`）。Phase B はこれを **黒箱**として呼ぶ（仮説に積まない）。

## Phase B — 非 iid Chebyshev 集中 `channelCoding_highLLR_tendsto_zero` ✅（compressed）

固定 codeword 群で threshold `= n(C+δ/2)` の `P_m^n(highLLRSet) → 0` を m 一様に。整形（`pi_singleton`→`∏`→`log`→
per-letter 和）+ 集中（`meas_ge_le_variance_div_sq` + `variance_sum_pi`、両側 `|·|` を片側包含で繋ぐ、`MemLp` は
finite alphabet + `hq_pos` の有界性から）。per-codeword 平均一様上界 `μ[X] ≤ C` は Phase A 鞍点を黒箱で受けた
（仮説に積まず）。commit `9ad30170`。

## Phase C — 配線 + headline closure ✅（compressed）

`Q := Measure.pi (fun _ ↦ q*)` + `threshold := n(C+δ/2)` を単発下界 `channelCoding_average_success_le` に代入 →
exp 項を `hrate` で `exp(−nδ/2) → 0`、tail 項を Phase B で → 0、squeeze で `avgPe.toReal → 1`。headline
`channelCoding_strong_converse_asymptotic` proof done（commit `08d18601`、certify `bb21942a`）。退化境界（M=1
vacuous / zero-cap・noiseless 両極生存 / 定数符号語整合）は target statement §退化境界 sanity が記録。

## 判断ログ

moonshot 完遂につき active な判断は無し。下記は machine-再導出不能な設計/誠実性の記録（残置）:

1. **iid 路 流用不可（設計記録）**: `strong_law_ae` / `steinTypicalSet_P_prob_tendsto_one` はともに `hident`（同分布）必須。チャネル出力は独立だが**非同分布** → 既存 iid AEP/LLN 路は全面不可、Phase B は **Chebyshev 直叩き（`meas_ge_le_variance_div_sq` + `variance_sum_pi`）** で組んだ（inventory §D）。整形（`pi_singleton`→`∏`→`log`→per-letter 和）は `StrongStein` 写経可だが収束 step だけは iid 専用で流用不可だった点が核。
2. **`hq_pos`（full-support 出力）は load-bearing でない precondition（誠実性記録）**: headline regularity hyp。`llr` well-defined のため必須だが proof 核を encode しない＝honest precondition（non-full-support 出力が唯一 guard する退化境界）。headline 監査時の確認点。
3. **退避ライン R-SC1/2/3 は全て決着（行使せず closure）**: Phase A の鞍点を `*Hypothesis` predicate に bundle する load-bearing bundling は禁止（CLAUDE.md「検証の誠実性」）だったが、gateway atom が genuine に出たため退避口は不要、3 Phase とも sorry を残さず closure（commit `3db9d443`/`9ad30170`/`08d18601`）。gateway atom の two-sided→片側 訂正の詳細は子 plan [`capacity-saddle-point.md`](capacity-saddle-point.md) 判断ログ #1 が SoT。

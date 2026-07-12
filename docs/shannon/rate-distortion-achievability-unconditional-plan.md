# Rate-distortion achievability — 無条件 operational form サブ計画

> **Parent**: [`rate-distortion-achievability-plan.md`](rate-distortion-achievability-plan.md) §Phase E (strong-typicality variant)

**Status**: CLOSED ✅ — Piece B/C/A + Wrapper `rate_distortion_achievability_operational` (`@[entry_point]`) genuine sorryAx-free、独立 honesty 監査 `@audit:ok` (全仮説 regularity/operational、load-bearing ゼロ)。roadmap Ch.10 / README 反映済。

## 要点 (≤5 行)
- 既存 headline `rate_distortion_achievability` (`AchievabilityStrongTypicality.lean:185`, `@entry_point`, 0 sorry) は honest pass-through 仮説付き。本 plan はそれらを discharge して **クリーンな operational 文**「`R > R(D)` なら大 n で `distortion ≤ D+ε` の lossy code が存在」を publish する。
- 攻略単位は 3 piece: **B (摂動)** = `hqStar_pos` を full-support 摂動で消す / **C (jts⊆dts 包含)** = `h_jts_subset_dts` を genuine 解析補題化 / **A (slack 存在ラッパー)** = 残る slack 仮説群 (`h_rate_gap`/`h_slack`/`h_dist_slack`/`hδ_kl_dominates`/qZ_min) を existential で選択。
- full-support source `∀ a, 0 < P_X a` を **regularity precondition** として置く (CLAUDE.md で OK な regularity、load-bearing でない。marginal 保存摂動が strict-positive に着地するのに必要な唯一の restriction)。
- 既存 `rate_distortion_achievability` の直接 consumer は **0 decl** (`dep_consumers.sh` 確認) — 本 plan は新規 wrapper theorem を追加するだけで既存 signature に ripple なし。

## 進捗

- [x] M0 — Mathlib/in-project API 在庫確認 ✅ (Piece C 実装中に完了、strong⟹weak bridge 再利用確認)
- [x] Piece C — `jointStronglyTypicalSet ⊆ distortionTypicalSet` 包含補題 ✅ (`jts_subset_dts_of_dist_slack`, genuine sorryAx-free, commit 47417b9f)
- [x] Piece B — full-support 摂動 (`hqStar_pos` + `hI_lt_R` + `E[d] ≤ D+ε/4`) ✅ (`rdPerturb` + 5 補題, genuine sorryAx-free, commit 079babcc)
- [x] Piece A — slack 存在ラッパー (残 slack 仮説群) ✅ (`rdSlack_exists`, 15-conjunct existential, genuine, commit 16c3d391)
- [x] Wrapper — `rate_distortion_achievability_operational` 組立 + source-law bridge ✅ (`@[entry_point]`, source を `pmfToMeasure P_X` に bridge, genuine sorryAx-free, commit 16c3d391)
- [x] 独立 honesty audit (headline signature の load-bearing-free 判定、特に `hP_supp` regularity) ✅ (all OK、`@audit:ok` 付与、`hP_supp` は over-hyp regularity と確認)

## ゴール / Approach

**最終目標**: full-support source `P_X` を仮定し、`R(D) < R` かつ `ε > 0` の下で、大きい n で期待 block distortion が `D + ε` 以下になる lossy code の存在を、slack 仮説なしの operational 文として証明する。既存 `rate_distortion_achievability_strong` を内部で呼び、その 3 群の honest pass-through 仮説を全て内部で discharge する。

### 全体戦略 (Approach)

**形 (shape)**: 既存 strong theorem は「最適 `qStar` (strict-positive) + rate/distortion slack を全部 caller 供給」の形で 0 sorry。本 plan は **その caller を書く** — すなわち slack を内部で選び、strict-positive な摂動測度を内部で構成する wrapper。核となる数学は 3 つに分かれる。

**Piece B (摂動)** — `rateDistortionFunctionPmf_attained` で `RDConstraint P_X d D` 上の最小点 `qStar` を取る (`mutualInfoPmf qStar = R(D) < R`)。marginal を保存する方向 `P_X ⊗ unif_β` (成分 `P_X(a)/|β|`) へ
```
q'(a,b) := (1-λ)·qStar(a,b) + λ·P_X(a)/(Fintype.card β)
```
と摂動する。full-support P_X より `P_X(a)/|β| > 0`、よって `λ > 0` で **全点 `0 < q'`**。`marginalFst (P_X⊗unif_β) = P_X` かつ `marginalFst qStar = P_X` なので `marginalFst q' = P_X` 保存、`q' ∈ stdSimplex`。`continuous_mutualInfoPmf` / `continuous_expectedDistortionPmf` で λ→0 のとき `I(q') → I(qStar) < R`、`E[d](q') → E[d](qStar) ≤ D`。十分小さい λ で同時に `mutualInfoPmf q' < R` かつ `expectedDistortionPmf d q' ≤ D + ε/4` を確保する (後者は下流の D-緩和のため)。

**D-緩和の要点**: strong theorem は `hqStar_mem : q' ∈ RDConstraint P_X d D_strong` を要求し、これは `E[d](q') ≤ D_strong` を含む。摂動は境界点 (`E[d](qStar) = D`) では `E[d](q')` を D 上へ押し得るので、strong を **`D_strong := D + ε/4`** で instantiate し、`E[d](q') ≤ D + ε/4` (Piece B) で membership を満たす。strong の内部 `ε'_strong := ε/2` を選ぶと結論は `≤ D_strong + ε'_strong = D + 3ε/4 ≤ D + ε`。

**Piece C (jts⊆dts 包含)** — `distortionTypicalSet = jointlyTypicalSet ∩ {blockDistortion ≤ expectedJointDistortion + δ}` (`AchievabilityJointTypicalEncoder.lean:97`)。よって包含は 2 本:
- (i) **strong ⟹ weak**: `jointStronglyTypicalSet ⊆ jointlyTypicalSet` (強 typical の per-symbol empirical type 偏差 ≤ ε_join から entropy 版 typical を導く)。
- (ii) **distortion 上界**: strong typical 上で `blockDistortion d n x y = ∑_{a,b} (typeCount/n)·d(a,b)` は `E_{q'}[d] = ∑_{a,b} q'(a,b)·d(a,b) = expectedJointDistortion` から高々 `ε_join·∑|d|` しか離れない。よって `δ_typ ≥ ε_join·∑d` (= `h_dist_slack` 型条件) の下で `≤ E[d]+δ_typ`。

これが `h_jts_subset_dts` の中身。**Piece B/A に依存しない純解析** ゆえ gateway として最初に単独で閉じる。

**Piece A (slack 存在ラッパー)** — strict-positive `q'` と `I(q')<R`, `E[d](q')≤D+ε/4` を所与に、残る slack を存在選択する。`qZ_min := ⨅ p, (pmfToMeasure q').real {p} > 0` (strict-positive → 正、`pmfToMeasure_real_singleton_pos`)。`logSumAbs` 3 項は q' 固定で有限定数。よって: `ε_X` 小 → `h_rate_gap` (I(q')<R に有限定数 ε_X-項 + δ_kl を足しても < R)、`δ_typ` 小 → `h_slack` (`E[d](q')+δ_typ ≤ D_strong+ε'_strong/2`) と `h_dist_slack` (`ε_join·∑d ≤ δ_typ`)、`hδ_kl_dominates` (`8|α||β|ε_X² ≤ δ_kl·qZ_min`) は `ε_X² / δ_kl` の順序で満たす。選択順は下記 Piece A 詳細。

**Wrapper** — 上記を束ね `rate_distortion_achievability_strong` に流し、結論の source law `(rdAmbient q').map (iidXs 0)` を `pmfToMeasure P_X` に橋渡し (`rdAmbient_map_iidXs` + `pmfToMeasure_map_fst_real_singleton` + `marginalFst q' = P_X`)、`D + 3ε/4 ≤ D + ε` を `le_trans` で weaken。

## Piece 分解表

| Piece | 新規 declaration (見込み) | 使う既存資産 | 撤退ライン (sorry + tag) |
|---|---|---|---|
| **C** | `jts_subset_dts_of_dist_slack` (h_jts_subset_dts の中身) | `jointStronglyTypicalSet` / `stronglyTypicalSet` + `mem_stronglyTypicalSet_iff` (`StrongTypicality.lean:58`) / `distortionTypicalSet` + `blockDistortion_le_of_mem_distortionTypicalSet` (`AchievabilityJointTypicalEncoder.lean:109`) / `jointlyTypicalSet` (`ChannelCoding/Basic.lean:281`) / `blockDistortion` / `typeCount` / `expectedJointDistortion` | (i) or (ii) が詰まったら当該 `have` を `sorry` + `@residual(plan:rate-distortion-achievability-unconditional-plan)`。**`h_jts_subset_dts` を operational theorem の仮説へ再露出しない** (再バンドル禁止) |
| **B** | `rdPerturb` (def) + `rdPerturb_pos` / `rdPerturb_marginalFst` / `rdPerturb_mem_stdSimplex` / `rdPerturb_mutualInfo_lt` / `rdPerturb_expectedDist_le` | `rateDistortionFunctionPmf_attained` (`Achievability.lean:239`) / `continuous_mutualInfoPmf` (`:204`) / `continuous_expectedDistortionPmf` (`:129`) / `continuous_marginalFst` (`:137`) / `stdSimplex` machinery / `RDConstraint` (`:155`) | 摂動連続性補題が詰まったら当該補題 body を `sorry` + `@residual(plan:rate-distortion-achievability-unconditional-plan)`。q' の def 自体は sorry 不要 (閉形) |
| **A** | `rdSlack_exists` (5 slack + qZ_min を返す existential) | `pmfToMeasure_real_singleton_pos` (`AchievabilityAmbientMeasure.lean:139`) / `logSumAbs` (有限定数) / `Finset.inf'` (qZ_min) | slack 選択が詰まったら当該不等式を `sorry` + `@residual(plan:rate-distortion-achievability-unconditional-plan)` |
| **Wrapper** | `rate_distortion_achievability_operational` (`@entry_point`) | `rate_distortion_achievability_strong` (`:97`) / `rdAmbient_map_iidXs` (`:165`) / `pmfToMeasure_map_fst_real_singleton` (`:57`) | source-law bridge が詰まったら bridge の `have` を `sorry` + 上記 tag |

## ターゲット文 (proposed shape、調整余地あり)

```lean
@[entry_point]
theorem rate_distortion_achievability_operational
    (P_X : α → ℝ) (hP_pmf : P_X ∈ stdSimplex ℝ α) (hP_supp : ∀ a, 0 < P_X a)
    (d : DistortionFn α β) {D : ℝ}
    (h_ne : (RDConstraint P_X d D).Nonempty)
    {R : ℝ} (hR : rateDistortionFunctionPmf P_X d D < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (_hM_ub : (M : ℝ) ≤ Real.exp ((n : ℝ) * R) + 1)
        (c : LossyCode M n α β),
        c.expectedBlockDistortion (ChannelCoding.pmfToMeasure P_X) d ≤ D + ε
```

**調整余地 (Wrapper で verbatim 確認)**:
- **source law**: 結論の source を `pmfToMeasure P_X` で書く案。strong は `(rdAmbient q').map (iidXs 0)` を返すので `rdAmbient_map_iidXs` (→ `(pmfToMeasure q').map Prod.fst`) + `pmfToMeasure_map_fst_real_singleton` (→ `.real {a} = marginalFst q' a = P_X a`) + finite-support の singleton 決定性で `= pmfToMeasure P_X` を橋渡し。橋が重ければ結論を `(rdAmbient q').map (iidXs 0)` のまま残し `= pmfToMeasure P_X` を別 lemma で提供する fallback も可 (どちらでも load-bearing でない)。
- **rate 境界 M の形**: R 不変ゆえ既存 strong と同一 (`Nat.ceil (exp(nR)) ≤ M ≤ exp(nR)+1`)。揃える。
- **`rateDistortionFunctionPmf P_X d D < R` の P_X 引数**: strong の `hI_lt_R` は摂動 q' に対する `mutualInfoPmf q' < R`。R(D) = `mutualInfoPmf qStar` (attained) < R を Piece B の連続性で q' へ伝播。

### full-support regularity の honesty 判断

`hP_supp : ∀ a, 0 < P_X a` は **regularity precondition (load-bearing でない)**。理由: (a) 結論 (operational achievability) の核を仮説に encode していない — 摂動・包含・slack 選択の実質を全て内部で証明する。(b) full-support は CLAUDE.md「Verification honesty」で明示的に OK とされる regularity 型 (full-support / `IsFiniteMeasure` / measurability と同類)。(c) それが必要な理由が明確: marginal を保存する摂動方向は `P_X ⊗ unif_β` に限られ (global uniform だと `marginalFst` が P_X からずれ制約破綻)、この方向が strict-positive に着地するのは `P_X` が全点正のときだけ。よって full-support は「なぜこの regularity か」を名指せる honest な scoping restriction であって、証明の核 (=結論そのもの) を渡す bundling ではない。**docstring に 1 行「full-support は marginal 保存摂動の strict-positive 着地に要る regularity precondition、load-bearing でない」を明記する。**

## 実装順 (gateway-atom-first)

1. **M0 在庫確認** — Piece C の (i) strong⟹weak / (ii) type-deviation distortion bound に使える in-project 補題を確認 (既存 strong track が同種の empirical-type 評価を持つ可能性: `AchievabilityStrongTypicality/SupportingBounds.lean` 周辺を読む)。Mathlib gap は想定なし (量の壁クラス)。proof-log: no。
2. **Piece C を単独で閉じる (gateway)** — `jts_subset_dts_of_dist_slack` を Piece B/A に依存せず先に genuine 化。これで「包含機構が本当に in-project asset で閉じる」を検証してから B/A へ進む (壁誤認の early 検出)。proof-log: yes。
3. **Piece B** — `rdPerturb` def + 5 補題 (pos / marginalFst / stdSimplex / mutualInfo_lt / expectedDist_le)。連続性で λ 選択。proof-log: yes。
4. **Piece A** — `rdSlack_exists`。B の strict-positive q' を受けて slack existential。proof-log: no。
5. **Wrapper** — 全部束ね strong に流し source-law bridge + budget weaken。proof-log: no。
6. **独立 honesty audit** — 新 sorry があれば `@residual` 分類検証、`rdPerturb` 系 signature が regularity のみで load-bearing でないこと、full-support 判断の honesty を確認。

## Piece 詳細

### Piece C — `jts_subset_dts_of_dist_slack`

目標 (h_jts_subset_dts と同型):
```
∀ {n}, 0 < n → ∀ x y,
  (x,y) ∈ jointStronglyTypicalSet (rdAmbient q') iidXs iidYs n ε_join →
  (x,y) ∈ distortionTypicalSet (rdAmbient q') iidXs iidYs d n ε_dist δ_typ
```
- [ ] (i) `jointStronglyTypicalSet ... ε_join ⊆ jointlyTypicalSet ... ε_dist`: `jointStronglyTypicalSet` は `stronglyTypicalSet (jointSequence ..)` (per-symbol type 偏差 ≤ ε_join)。weak `jointlyTypicalSet` (entropy 版) を強 typical から導く。`ε_join`↔`ε_dist` の関係を明示 (strong が weak を含意する ε 対応)。
- [ ] (ii) strong typical 上で `blockDistortion d n x y ≤ expectedJointDistortion (rdAmbient q') (iidXs 0) (iidYs 0) d + δ_typ`: `blockDistortion = ∑_{a,b}(typeCount/n)·d`、`expectedJointDistortion = E_{q'}[d]`、`|typeCount/n − q'(a,b)| ≤ ε_join` を各 (a,b) で足し上げて偏差 `≤ ε_join·∑|d|`。`δ_typ ≥ ε_join·∑d` (Piece A で確保、= h_dist_slack) で締める。
- [ ] `distortionTypicalSet = (i) ∩ (ii)` の `Set.mem_inter` で結論。

### Piece B — `rdPerturb` と連続性

- [ ] `def rdPerturb (qStar P_X) (λ) : α×β → ℝ := fun p ↦ (1-λ)·qStar p + λ·P_X p.1/(Fintype.card β)` (閉形、sorry 不要)。
- [ ] `rdPerturb_mem_stdSimplex`: `0 ≤ λ ≤ 1` + `qStar ∈ stdSimplex` + `P_X ∈ stdSimplex` から convex 結合として simplex。
- [ ] `rdPerturb_pos`: `0 < λ` + `hP_supp` から全点 `0 < rdPerturb ..` (`P_X p.1/|β| > 0` が下支え)。
- [ ] `rdPerturb_marginalFst`: `marginalFst (rdPerturb ..) = P_X` (`marginalFst qStar = P_X` かつ `∑_b P_X(a)/|β| = P_X(a)`)。
- [ ] `rdPerturb_mutualInfo_lt`: `continuous_mutualInfoPmf` + `mutualInfoPmf qStar < R` で λ→0 連続、∃λ₀>0 s.t. `mutualInfoPmf (rdPerturb .. λ) < R` for `λ ≤ λ₀`。
- [ ] `rdPerturb_expectedDist_le`: `continuous_expectedDistortionPmf` + `E[d](qStar) ≤ D` で ∃λ₁>0 s.t. `≤ D + ε/4`。
- [ ] 実装で `λ := min λ₀ λ₁` (と `≤1` clamp) を取る。

### Piece A — `rdSlack_exists`

strict-positive q' + `I(q')<R` + `E[d](q')≤D+ε/4` を所与に、以下を満たす `(ε_X, ε_join, ε_dist, δ_kl, δ_typ, qZ_min)` を存在構成:
- [ ] `qZ_min := Finset.inf' (univ) _ (fun p ↦ (pmfToMeasure q').real {p})`、`0 < qZ_min` (`pmfToMeasure_real_singleton_pos` + strict-positive)。`hqZ_min_le` は inf' の下界性。
- [ ] `ε_X` 小: `h_rate_gap` = `I(q') + (有限定数·ε_X + δ_kl) < R`。`I(q')<R` の gap を有限 `logSumAbs` 定数で割り ε_X を選ぶ。
- [ ] `δ_kl` を `hδ_kl_dominates` (`8|α||β|ε_X² ≤ δ_kl·qZ_min`) と `h_rate_gap` の両立で選ぶ (`ε_X` 決定後、`δ_kl := 8|α||β|ε_X²/qZ_min` で等号、それが rate_gap を壊さないよう ε_X をさらに小さく)。
- [ ] `ε_join` は `hε_X_lt_ε_join` (`ε_X < ε_join`) を満たしつつ小さく (Piece C の ε 対応 + `h_dist_slack` に使う)。
- [ ] `δ_typ := ε_join·∑d` で `h_dist_slack` 等号、`h_slack` (`E[d](q')+δ_typ ≤ D_strong+ε'_strong/2 = D+ε/4+ε/4`) は `E[d](q')≤D+ε/4` + `δ_typ ≤ ε/4` (ε_join さらに小) で。
- [ ] `ε_dist` は Piece C (i) の strong⟹weak 対応が要求する下界を満たすだけ (自由、小さく)。
- **選択順**: `ε_X → δ_kl → ε_join → δ_typ → ε_dist`。各段で上流を壊さない strict 不等号余裕を残す。

## 想定リスク

各 piece は**量の壁クラス** (finite-sum の連続性・不等式評価) で **Mathlib gap は無い**と判断済。壁と誤認しそうな点:

1. **Piece C (i) strong⟹weak**: 「per-symbol type 偏差 ≤ ε_join ⟹ entropy 版 jointlyTypical」の ε 対応を、既存 strong track (`SupportingBounds.lean`) が既に持っている可能性大。M0 で grep して再利用 (自作重複を避ける)。無ければ finite-sum 評価で self-build、壁ではない。
2. **Piece A の slack 連立**: 5 パラメータの相互制約 (特に `ε_X²/δ_kl·qZ_min` の順序) は「大 (choice) であって難 (blocked) でない」。詰まっても壁ではなく、選択順を変えるか strict 余裕を増やす。壁タグは付けない。
3. **source-law bridge**: finite discrete で「singleton 値一致 → measure 一致」は plumbing (`Measure.ext` + finite)。詰まったら結論を `(rdAmbient q').map (iidXs 0)` 形のまま残す fallback があるので closure を止めない。
4. **D-緩和の budget 算術**: `D_strong = D+ε/4`, `ε'_strong = ε/2` → `D+3ε/4 ≤ D+ε`。取り違えると budget が閉じないので Wrapper で verbatim に `linarith` 検証 (数値予測の verbatim 確認)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)、active な判断のみ残す。プラン予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。

1. **摂動方向を `P_X ⊗ unif_β` に固定** (起草時): global uniform だと `marginalFst` が P_X からずれ RDConstraint marginal 制約を破る。marginal 保存には source-side を P_X に、reconstruction-side だけ uniform に散らす `P_X(a)/|β|` 方向が必須。これが full-support P_X (regularity) を要求する根拠。
2. **strong を `D_strong := D+ε/4` で instantiate (D-緩和)** (起草時): strong の `hqStar_mem` は `E[d](q') ≤ D_strong` を含み、境界点 (`E[d](qStar)=D`) では摂動が D 上へ出得る。原 D のままだと membership 不成立。緩和 D + 内部 `ε'_strong=ε/2` で最終 `D+3ε/4 ≤ D+ε`。
3. **Piece C を gateway (最初)** (起草時): C は B/A 非依存の純解析で、包含機構が in-project asset で閉じるかを最速で検証できる。C が閉じれば残 B/A は選択問題なので、壁誤認リスクの高い C を先に潰す。

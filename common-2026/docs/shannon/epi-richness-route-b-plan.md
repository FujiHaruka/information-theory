# EPI richness 壁 (G4/W2) — route B (lift-and-transport) genuine closure サブ計画

> **Parent**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md)
>   §Phase A-close G4/W2 行 + 撤退ライン L-Concl-A-richness / L-Concl-A-γ。
> **消費 inventory**: [`epi-richness-noise-inventory.md`](epi-richness-noise-inventory.md)
>   (構成 primitive Mathlib 在庫 100% + 4 lemma skeleton + 依存 DAG + 主要前提条件ボックス verbatim 済)。
> **slug**: `epi-richness-route-b-plan` (新規導入する全 lift lemma の `@residual` slug をこれに揃える)。

<!--
記法: moonshot-plan-template と同じ (状態絵文字 📋/🚧/✅/🔄、~~取り消し線~~、判断ログ append-only)。
proof-log: no (本計画は設計のみ。実装着手時に proof-log を別途起こす)。
-->

## 進捗

> **B1 DONE (2026-06-04、commit `8431a20` + audit commit)**: lift machinery 4 lemma 全て
> genuine 0 sorry / `@audit:ok` (`#print axioms` sorryAx-free 機械確認、独立 honesty-auditor pass)。
> Phase 4 は予測 (`iIndepFun_pi` + 因子化) より大幅に軽く `indepFun_prod` 直接 1 行で閉じた。
> 偽 in-place W2 は `@audit:defect(false-statement) @audit:closed-by-successor(epi-richness-route-b-plan)`
> でマーク (dirac 反例で独立検証済)。wall register 追記は**しない** (false-statement を wall と誤分類しないため)。
> **残**: B2 (in-place re-wire で偽 lemma 完全除去) は headline を塞ぐ G2 待ちで保留。lift machinery は
> G2 closure まで live consumer 0 (dead-code、docstring 正当化 3 点 + future B2 foundation)。

- [x] Phase 0 — 在庫照合 + 設計凍結 (B1 採用) ✅ → [`epi-richness-noise-inventory.md`](epi-richness-noise-inventory.md)
- [x] Phase 1 — `EPINoiseExtension.lean` skeleton 着地 ✅
- [x] Phase 2 — lift law 保存補題 `entropyPower_map_comp_fst_eq` ✅ **genuine, `@audit:ok`**
- [x] Phase 3 — lift noise 構成補題 `stamScalingNoise_exists_on_lift` ✅ **genuine, `@audit:ok`**
- [x] Phase 4 — sum-vs-sum 独立補題 `indepFun_add_add_on_lift` ✅ **genuine, `@audit:ok`** (`indepFun_prod` 直接 1 行)
- [x] Phase 5 — EPI transport 本体 `entropy_power_inequality_via_lift` ✅ **genuine (conditional transport 形), `@audit:ok`**
- [x] Phase 6 — 偽 in-place `stamScalingNoise_exists` の honest マーク ✅ (wall register 追記は意図的に不実施)
- [x] Phase 7 — verify (0 errors) + `InformationTheory.lean` 編入 + 独立 honesty audit (全 OK) ✅

proof-log: no (設計のみ。実装 Phase で `docs/shannon/proof-log-epi-richness-route-b-*.md` を別途起こす)

---

## ゴール / Approach

### ゴール

EPI richness sub-wall (親 §Phase A-close の **G4** = `IndepFun (X+Y) (Z_X+Z_Y) P` joint indep `sorry`
`EPIStamToBridge.lean:1360` / **W2** = `stamScalingNoise_exists` in-place existential `sorry` `:388`) を
**route B (lift-and-transport)** で genuine (0 sorry) に閉じる。具体的には lift 空間 `Ω × ℝ × ℝ`
(`Z_X, Z_Y` 因子 = `gaussianReal 0 1`) 上で 4-tuple joint independence を Mathlib product-measure API のみ
から構成し、`entropyPower` の law-only 性 + `IsStamInequalityResidual` の carrier-free 性を使って
`(Ω, P)` に EPI を transport する。**真の Mathlib 壁 (`wall:in-place-noise-extension`) は route B では踏まない**
(在庫総合 verdict)。

### Load-bearing context (scope の境界 — 必読)

- richness closure は headline `stamToEPIBridge_holds` (`EntropyPowerInequality.lean:249`) を
  **proof-done にしない**。headline は transitive に **G2 heat-flow-continuity**
  (`heatFlowEntropyPower_continuousOn`、真 Mathlib 壁、2026-06-03 GATE NO-GO 確定 + 独立 audit OK、
  `@residual(wall:heatflow-continuity)`) を別途要する。richness は **G2 とは独立に閉じられる**が、
  headline の sorryAx-free 化には G2 が残る。**本計画の scope は richness sub-wall のみ** (確定事実 C)。
- route B が産むのは lift 空間 `Ω×ℝ²` 上の genuine な EPI + transport。in-place existential を捨て、
  偽の in-place `stamScalingNoise_exists` (確定事実 A) は honest にマークして置換する。

### Approach — B1 (lift machinery のみ) vs B2 (full re-wire) の比較

在庫は 4 lemma skeleton を出しているが、**最大の未決定は「lift lemma を建てた後、既存 consumer
`isStamToEPIScalingHyp_of_stam_debruijn` (`EPIStamToBridge.lean:1291`) にどう wire するか」**。
2 案を比較する。

| 観点 | 案 B1 (最小 scope、lift machinery のみ) | 案 B2 (full re-wire) |
|---|---|---|
| 閉じる sorry | G4 (`:1360`) を lift 上で genuine、W2 (`:388`) を偽として除去 (Phase 6 で defect マーク → lift 形 `_on_lift` に置換)。`EPINoiseExtension.lean` の 4 lemma を 0 sorry で着地 | 上記 + 既存 bridge chain (`isStamToEPIScalingHyp_of_stam_debruijn` 以降) を lift 空間 `P' = P.prod (ν.prod ν)` 上で回し `(Ω,P)` に transport。in-place 偽 lemma を完全除去 |
| 残る sorry | G2 (`wall:heatflow-continuity`、headline transitive、本計画 scope 外) | 同左 (G2 は re-wire しても transitive に残る) |
| 触る file | `EPINoiseExtension.lean` (新規) + `EPIStamToBridge.lean` (W2 docstring マーク + register 訂正) | 上記 + `EPIStamToBridge.lean` 本体 (`:1291-1374` bridge chain) + `EntropyPowerInequality.lean` (headline transport 経路) を大改修 |
| 工数見積 | lift law 保存 ~40-60 / lift 構成 ~40-80 / sum-vs-sum ~10-30 / transport 本体 ~50-100、計 **~150-270 行** | B1 + bridge chain の lift 化 + transport plumbing、計 **~350-550 行** (consumer ripple 含む) |
| dead-code リスク | **あり** — lift 4 lemma が live consumer ゼロになる (現 consumer は in-place `IsStamScalingNoiseHyp` を取る)。正当化が必要 (下記) | なし (全 chain が lift を通る) |
| G2 との関係 | richness を G2 と分離して閉じる。G2 残存は honest に明示 | re-wire しても headline は G2-blocked のまま。**richness closure の ROI を G2 が打ち消す** |
| honesty 効果 | 偽 W2 を honest マーク + lift machinery で「richness は closable」を実証 + wall register 訂正 | 偽 W2 を完全除去 + richness genuine + chain 全体が lift 経由 |

#### 推奨: **案 B1**

**理由 (planner 独立判断、orchestrator の in-mind 仮定と一致)**:

1. **G2 が headline を塞ぐ以上、B2 の追加投資 (~+200-280 行 + consumer ripple) はリターンを生まない**。
   B2 が達成するのは「chain が lift を通る」だが、headline の proof-done には G2 (真 Mathlib 壁) が
   別途必要で、B2 をやっても headline は sorryAx-free にならない。richness を閉じる目的に対し、chain 全体の
   lift 化は over-engineering。
2. **B1 の dead-code リスクは正当化可能** (下記 3 点)。lift machinery は将来 re-wire の foundation /
   wall register 訂正の根拠 / 偽 statement 置換の代替提示として価値を持つ。
3. **honesty の本丸 = 偽 W2 のマーク**は B1 で達成できる。確定事実 A の通り `stamScalingNoise_exists` は
   atomic measure で偽 (`false-statement` defect) であり、docstring の「Mathlib upstream constructor 待ち」は
   誤誘導。B1 はこれを `@audit:defect(false-statement)` + `@audit:closed-by-successor(epi-richness-route-b-plan)`
   でマークし、honest な lift 形 `stamScalingNoise_exists_on_lift` を併置する。

**B1 の dead-code 正当化 (Phase 1 設計時に docstring へ明記する 3 点)**:

- **(a) future re-wire foundation**: lift 4 lemma は B2 (full re-wire) に着手する後続セッションの
  building block。in-place 偽 lemma を除去する唯一の honest 経路は lift 経由であり、その機材を先に genuine
  化しておく。
- **(b) wall register 訂正の根拠**: `wall:in-place-noise-extension` (在庫が唯一の真壁と判定) は route B で
  踏まないことを実証する。在庫の「richness は閉じられる」主張を機械検証済の lemma で裏付け、`audit-tags.md`
  の wall register に「route B で回避可能」注記を追加する根拠を提供。
- **(c) 偽 statement 置換の代替提示**: 偽 W2 を単に削除/defect マークするだけでなく、**honest な代替
  (`_on_lift` 形)** を同 file に提示することで、撤退ではなく置換であることを示す。

> **B2 への昇格 trigger**: G2 (`wall:heatflow-continuity`) が将来 genuine 化された場合、headline が
> richness 以外で sorryAx-free になり得るので、その時点で B2 (full re-wire で偽 W2 を完全除去) の ROI が
> 立つ。本計画は B1 で着地し、B2 は G2 closure 後の後続 plan に委ねる (判断ログに記録)。

---

## 確定事実 (orchestrator + planner verbatim 確認済、計画前提)

### 確定事実 A — in-place `stamScalingNoise_exists` は as-stated で偽 (honesty 発見)

`IsStamScalingNoiseHyp X Y P := ∃ Z_X Z_Y, … ∧ P.map Z_X = gaussianReal 0 1 ∧ …`
(`EPIStamToBridge.lean:358-363`、verbatim 確認済) は **atomic な P で偽**。例: `Ω = Unit`,
`P = Measure.dirac ()` は `[IsProbabilityMeasure P]` を満たすが、任意の可測 `Z_X : Unit → ℝ` は定数 →
`P.map Z_X = dirac (Z_X ())` ≠ `gaussianReal 0 1`。よって `stamScalingNoise_exists` (`:388`、body `sorry`)
の `sorry` は「難しい (hard)」ではなく **証明不能 (false-statement)**。docstring (`:375-381`) の
「Mathlib upstream noise-extension constructor 待ち」は誤誘導 (偽の文はどんな constructor でも証明不能)。
これは tier-5 honesty defect 寄り (誤分類された wall)。正しい honest closure は route B (lift 空間への
張り替え) であり、in-place existential を捨て lift 空間 `Ω×ℝ²` 上の genuine な existential に置換する。
→ Phase 6 で `@audit:defect(false-statement)` + `@audit:closed-by-successor(epi-richness-route-b-plan)`
でマークし lift 形に置換。

### 確定事実 B — `IsStamInequalityResidual` は carrier-free (transport defeq)

`IsStamInequalityResidual X Y P` の body (`EntropyPowerInequality.lean:209-222`、verbatim 確認済) は
抽象密度 `fX fY fXY` と Fisher info 値 `J_X J_Y J_sum` のみを `∀` 量化し、`X / Y / P` を一切参照しない。
よって `IsStamInequalityResidual X Y P` と `IsStamInequalityResidual X' Y' P'` は **defeq**。transport で
仮説書換不要 (在庫「主要前提条件ボックス」)。かつ upstream `stam_step2_density_wall` で genuine discharge 済
(`@audit:ok`、`:208`)。load-bearing bundle ではない (regularity-gated、conclusion `1/J_sum ≥ 1/J_X+1/J_Y` は
upstream genuine)。

### 確定事実 C — G2 は本計画 scope 外 (真 Mathlib 壁、残置)

headline `stamToEPIBridge_holds` (`EntropyPowerInequality.lean:249`、body `sorry`) は transitive に
G2 heat-flow-continuity (`heatFlowEntropyPower_continuousOn`、真 Mathlib 壁、2026-06-03 NO-GO 確定 +
独立 audit OK、`@residual(wall:heatflow-continuity)`) を要する。**richness closure は headline を
proof-done にしない** — G2 が残る。route B の scope は **richness sub-wall のみ**。headline closure には
G2 が別途必要 (親 §Phase A-close G2 行 + `epi-g2-continuity-plan.md`)。

---

## Phase 詳細

> **slug 統一指示 (実装者向け)**: 本計画で新規導入する全 lift lemma の `@residual` slug は
> `epi-richness-route-b-plan` に揃える (誤分類防止)。ただし lift lemma は genuine closable (0 sorry 目標)
> なので、原則 sorry なしで着地し、`@residual` は撤退時のみ付与する。Phase 6 の偽 W2 マークは defect 系タグ
> (`@audit:defect` + `@audit:closed-by-successor`) を使う (sorry の residual ではなく signature defect)。

### Phase 0 — 在庫照合 + 設計凍結 📋

proof-log: no (調査のみ)

- [ ] 在庫 (`epi-richness-noise-inventory.md`) の軸 1-5 Mathlib API を loogle で再照合 (rev drift 確認、
      特に「sum-vs-sum 補題 source 不在」= 軸 2 注意 / Mathlib 壁列挙の和 vs 和行)。
- [ ] B1/B2 推奨 (= B1) を凍結。dead-code 正当化 3 点を Phase 1 docstring に転記する準備。
- [ ] consumer `isStamToEPIScalingHyp_of_stam_debruijn` (`:1291-1374`) の現 wiring を verbatim 確認済
      (本計画起草時に Read 済): `h_noise : IsStamScalingNoiseHyp X Y P` を destructure し、G4 sorry
      (`:1360`) で `IndepFun (X+Y) (Z_X+Z_Y) P` を捏出している。B1 では **この consumer は触らない**
      (lift lemma は別 file に live、consumer は in-place のまま、偽 W2 は defect マーク)。

### Phase 1 — `EPINoiseExtension.lean` skeleton 着地 📋

proof-log: no (skeleton)

- [ ] 在庫「着手 skeleton」(inventory `:273-318`) をコピーして `EPINoiseExtension.lean` を新規作成。
      import: `Mathlib.Probability.Distributions.Gaussian.Real` /
      `Mathlib.Probability.Independence.Basic` / `Mathlib.MeasureTheory.Measure.Prod` /
      `Mathlib.MeasureTheory.Measure.Map` / `InformationTheory.Shannon.EntropyPowerInequality` /
      `InformationTheory.Shannon.EPIStamToBridge`。
- [ ] 4 lemma を `:= by sorry` で stub 化:
  - `liftMeasure P := P.prod ((gaussianReal 0 1).prod (gaussianReal 0 1))` (`noncomputable abbrev`)
  - `entropyPower_map_comp_fst_eq` (Phase 2)
  - `stamScalingNoise_exists_on_lift` (Phase 3)
  - `indepFun_add_add_on_lift` (Phase 4)
  - `entropy_power_inequality_via_lift` (Phase 5)
- [ ] skeleton が type-check (sorry warning のみ) を確認。各 stub の docstring に dead-code 正当化 3 点
      (a)(b)(c) と slug 注記を記載。
- [ ] LSP `<new-diagnostics>` 待ち → 0 errors 確認。

### Phase 2 — `entropyPower_map_comp_fst_eq` (lift law 保存、transport linchpin) 📋

proof-log: yes

**結論形** (在庫 `:294-296`):
`entropyPower ((liftMeasure P).map (fun p => X p.1)) = entropyPower (P.map X)` (要 `hX : Measurable X`)。

**当て先 Mathlib lemma** (在庫軸 4、完全 namespace):
- `MeasureTheory.Measure.map_map` (`Map.lean:202`) — `(μ.map f).map g = μ.map (g ∘ f)`
- `MeasureTheory.measurePreserving_fst` (`Prod.lean:258`、`[IsProbabilityMeasure ν]` 要) —
  `(P.prod ν).map fst = P` (`.map_eq`)
- 核 1 行: `P'.map (X∘fst) = (P'.map fst).map X = P.map X`。両因子が `[IsProbabilityMeasure]` (P + gaussian
  product) で `measurePreserving_fst` が `one_smul` 済形を供給。

### Phase 3 — `stamScalingNoise_exists_on_lift` (lift noise 構成、W2 の honest 後継) 📋

proof-log: yes

**結論形** (在庫 `:299-301`):
`IsStamScalingNoiseHyp (fun p => X p.1) (fun p => Y p.1) (liftMeasure P)`。
これは **lift 空間上の genuine な existential** (in-place の偽 W2 を置換)。witness は座標射影
`Z_X' := (·.2.1)`, `Z_Y' := (·.2.2)`。

**当て先 Mathlib lemma** (在庫軸 1-3、完全 namespace):
- `ProbabilityTheory.indepFun_prod` (`Basic.lean:751`、`[IsProbabilityMeasure μ] [IsProbabilityMeasure ν]`
  両方要) ×2 — `Z_X ⊥ Z_Y` (2 つの ℝ 因子) / `(X,Y)∘fst ⊥ (Z_X,Z_Y)` (Ω 因子 vs ℝ² 因子)
- `ProbabilityTheory.IndepFun.comp` (`Basic.lean:799`) — pair を 1 座標に潰す射影
- `MeasureTheory.Measure.map_snd_prod` (`Prod.lean:262`) + `one_smul` — 座標 law `(liftMeasure).map Z_X' =
  gaussianReal 0 1`
- `ProbabilityTheory.instIsProbabilityMeasureGaussianReal` (`Gaussian/Real.lean:209`) — lift 因子が確率測度

設計注意 (在庫軸 5 末尾): 3 因子 `Ω × ℝ × ℝ` (Ω に `(X,Y)` 同居)。`X ⊥ Y` は供給しない (caller の `hXY`
が別物)。pairwise 3 つのみ構成。

### Phase 4 — `indepFun_add_add_on_lift` (sum-vs-sum 独立、G4 の honest 後継) 📋

proof-log: yes

**結論形** (在庫 `:304-306`):
`IndepFun (fun p => X p.1 + Y p.1) (fun p => p.2.1 + p.2.2) (liftMeasure P)` (要 `hX hY : Measurable`)。
これは **lift 空間上で** G4 (`:1360` の in-place joint indep `sorry`) に対応する量を genuine に供給する。

**当て先 Mathlib lemma** (在庫軸 2):
- `ProbabilityTheory.iIndepFun_pi` (`Basic.lean:784`、`[Fintype ι]` + `[∀ i, IsProbabilityMeasure (μ i)]`) —
  4-tuple joint indep の核 (`[X∘fst, Y∘fst, Z_X, Z_Y]`)
- `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map` (`[IsFiniteMeasure μ]`) — 結合分布因子化
- **在庫の穴 1 個 (軸 2 注意 + Mathlib 壁列挙の和 vs 和行)**: 現コンパイル対象 source rev `043e9e04` には
  `(X+Y) vs (Z_X+Z_Y)` の **和 vs 和直接補題が不在** (`indepFun_add_add` は loogle index の新 rev のみ、
  grep 0 hit)。→ `indepFun_iff_map_prod_eq_prod_map_map` + `iIndepFun_pi` の結合分布因子化から **self-derive**
  (10-30 行)。**これは Mathlib 壁ではない** (在庫判定)。Phase 0 で rev を再照合し、もし現 source に
  `indepFun_add_add` が入っていれば self-derive 不要。

### Phase 5 — `entropy_power_inequality_via_lift` (transport 本体) 📋

proof-log: yes

**結論形** (在庫 `:310-314`):
```
entropy_power_inequality_via_lift (hX hY : Measurable) (hXY : IndepFun X Y P)
    (h_stam : IsStamInequalityResidual X Y P) :
  entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)
```

**構成** (在庫「自作必要 3」):
1. lift 空間 `P' = liftMeasure P` 上で EPI を得る (lift 上の noise = Phase 3、joint indep = Phase 4、
   既存 EPI chain を `P'` で回す)。
2. `entropyPower (P'.map (X∘fst)) = entropyPower (P.map X)` (Phase 2) を X / Y / X+Y の 3 箇所に適用。
   関数等式 `(X∘fst) + (Y∘fst) = (X+Y)∘fst` の整理が落とし穴 (在庫「落とし穴」)。
3. `IsStamInequalityResidual X Y P = IsStamInequalityResidual X' Y' P'` を **defeq** で transport
   (確定事実 B、書換不要)。
4. transport で `(Ω,P)` 版 EPI を結論。

**当て先 Mathlib lemma**: Phase 2 (`map_map` / `measurePreserving_fst`) + `entropyPower` law-only 性
(`EntropyPowerInequality.lean:101` 近傍、measure を引数に取る量)。

> **B1 dead-code 注記**: Phase 5 の `entropy_power_inequality_via_lift` は B1 では既存 headline
> `entropy_power_inequality` (`:287`) に wire しない (B2 の領分)。**lift 経由 EPI が genuine に組める**ことを
> 実証する live でない demo lemma として置く。docstring に「foundation for B2 re-wire / route B 実証」と明記。

### Phase 6 — 偽 in-place `stamScalingNoise_exists` の honest マーク + wall register 訂正 📋

proof-log: no (マーク作業)

- [ ] `stamScalingNoise_exists` (`EPIStamToBridge.lean:388`) の docstring を訂正:
  - 現 docstring (`:375-381`) の「Mathlib upstream noise-extension constructor 待ち」(誤誘導) を削除。
  - `@audit:defect(false-statement)` + `@audit:closed-by-successor(epi-richness-route-b-plan)` を付与。
  - 確定事実 A の反例 (`Ω = Unit`, `P = Measure.dirac ()` で任意可測 `Z_X` が定数 →
    `P.map Z_X ≠ gaussianReal 0 1`) を docstring に 1-2 行で記載。
  - 「第一選択 (定義書換で sorry を proof body に逃がす) が当該 declaration には適用できない理由 =
    `IsStamScalingNoiseHyp` の in-place existential 自体が偽なので、honest 後継は lift 形
    `stamScalingNoise_exists_on_lift` (別 file)」を 1 行で明記 (CLAUDE.md「sorry を書けない箇所」第二選択の
    必須条件 (a)(b))。
  - **注意**: `stamScalingNoise_exists` は theorem (body sorry) なので sorry 自体は書ける。ただし statement が
    偽なので sorry は false-statement defect。signature を偽のまま残すか body を `sorry` のまま defect マーク
    するかは tier-5 暫定 (CLAUDE.md 第二選択)。**signature 改変 (in-place → lift) は consumer
    `:1291` の destructure に波及する** ため B1 では signature を据置 (defect マーク) し、lift 形は別 file の
    新 lemma として併置 (置換ではなく追加 = honest な代替提示、確定事実 A の closure 方針)。
- [ ] G4 sorry (`EPIStamToBridge.lean:1360`) の inline コメント (`:1347-1359`) を確認: 既に
  `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` で honest にマーク済 + 「load-bearing でない genuine
  gap」と注記済。B1 では **この consumer は触らない** (lift 形は別 file に live)。slug を本計画に付け替えるかは
  Phase 7 audit で判断 (誤分類なら `epi-richness-route-b-plan` に統一)。
- [ ] `docs/audit/audit-tags.md` の Wall name register `wall:in-place-noise-extension` 行 (在庫が唯一の真壁と
  判定) に「route B (`epi-richness-route-b-plan`) で genuine に回避可能、in-place existential は atomic measure
  で偽 (false-statement)」注記を追記 (在庫総合 verdict の register 反映)。

> **編集境界注意**: 本 Phase は実装者 (lean-implementer) が `EPIStamToBridge.lean` docstring + 
> `audit-tags.md` を編集する作業。planner (本ファイル) は計画記述のみ。

### Phase 7 — verify + InformationTheory.lean 編入 + 独立 honesty audit 📋

proof-log: no

- [ ] `EPINoiseExtension.lean` を `lake env lean` で silent (0 errors、4 lemma が 0 sorry 目標)。
- [ ] `InformationTheory.lean` に `import InformationTheory.Shannon.EPINoiseExtension` を 1 行追加。
- [ ] `EPIStamToBridge.lean` を `lake build InformationTheory.Shannon.EPIStamToBridge` で olean refresh
      (docstring マーク変更のみだが consumer 参照のため)。
- [ ] **独立 honesty-auditor 起動** (CLAUDE.md 必須): lift 4 lemma の genuine 性 (0 sorry / 0 @residual、
      load-bearing bundle 無し)、Phase 6 の `@audit:defect(false-statement)` 分類の正しさ、wall register 訂正の
      整合を独立検証。fresh subagent (実装非関与)。
- [ ] 親計画 §Phase A-close G4/W2 行を更新 (richness は route B で B1 closure、headline は G2 残存)。

---

## 撤退ライン

全撤退口は **sorry のみ** (仮説束化・退化定義悪用・`*Hypothesis` bundling 禁止、CLAUDE.md 検証の誠実性)。
lift lemma は genuine closable (0 sorry 目標) なので、撤退は想定外に重い場合のみ。

- **L-RouteB-2-α** (Phase 2、許容): `entropyPower (P'.map (X∘fst)) = entropyPower (P.map X)` の
  `measurePreserving_fst.map_eq` rewrite が `one_smul` 係数で割れない場合 → `sorry` +
  `@residual(plan:epi-richness-route-b-plan)` 継続。lift law 保存は in-place 壁ではないので closure 見込みは高い。

- **L-RouteB-4-α** (Phase 4、許容): sum-vs-sum 独立の self-derive (`indepFun_iff_map_prod_eq_prod_map_map`
  経由因子化) が 30 行超で `simp`/`fun_prop` が割れない場合 → 該当 `have` を `sorry` +
  `@residual(plan:epi-richness-route-b-plan)`。**禁止**: `IndepFun (X+Y) (Z_X+Z_Y)` を caller hypothesis に
  bundling して抜く (load-bearing、退化)。あくまで lift 空間上の sorry で残す。

- **L-RouteB-5-α (= 在庫の縮退案 L-Concl-A-richness')** (Phase 5、許容): EPI transport の関数等式整理
  (`(X∘fst)+(Y∘fst) = (X+Y)∘fst` の `P'.map` rewrite チェーン) が `simp`/`fun_prop` で割れない場合 →
  **lift 空間版 EPI (`entropy_power_inequality_on_product`、結論を `P'.map` 形で述べる) を honest な中間定理
  として publish**し、`(Ω,P)` 版への降下を `sorry` + `@residual(plan:epi-richness-route-b-plan)` で残す
  (在庫 `:266-267`)。撤退口は sorry のみ。仮説束化はしない。

- **L-RouteB-6-α** (Phase 6、許容): `stamScalingNoise_exists` の signature 改変 (in-place → lift) の
  consumer 波及 (`:1291` destructure) が file scope を膨らませる場合 → signature 据置 + defect マークのみ
  (B1 既定)。lift 形は別 file 追加 (置換せず併置)。これは撤退ではなく B1 の標準動作。

**共通禁止** (CLAUDE.md 検証の誠実性): `Prop := True` / `:= h` 循環 / load-bearing `*Hypothesis` bundle /
退化定義悪用 (`Z_Y := 0` 等 trivial 化)。撤退時 docstring に「NOT a discharge」明示。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-06-04 起草**: 在庫 (`epi-richness-noise-inventory.md`、構成 primitive Mathlib 在庫 100% +
   4 lemma skeleton) を出発点に route B closure plan を起草。orchestrator + planner で確定事実 A/B/C を
   verbatim 確認 (A: `EPIStamToBridge.lean:358-363` + `:375-391` / B: `EntropyPowerInequality.lean:209-222` /
   C: `:249-252`、consumer `:1291-1374`)。**B1 (lift machinery のみ) を推奨確定** — G2
   (`wall:heatflow-continuity`、真 Mathlib 壁) が headline を塞ぐ以上、B2 (full re-wire) の追加投資は headline
   proof-done に寄与せず ROI が立たない。B1 の dead-code リスクは (a) future re-wire foundation /
   (b) wall register 訂正の根拠 / (c) 偽 statement 置換の代替提示 の 3 点で正当化。偽 in-place W2
   (`stamScalingNoise_exists`、atomic measure で false-statement、確定事実 A) は Phase 6 で
   `@audit:defect(false-statement)` + `@audit:closed-by-successor(epi-richness-route-b-plan)` マーク。
   **B2 昇格 trigger**: G2 が将来 genuine 化したら headline が richness 以外で sorryAx-free になり得るので、
   その時点で B2 (偽 W2 完全除去) の ROI が立つ — 後続 plan に委ねる。

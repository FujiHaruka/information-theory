# EPI de Bruijn integration — Phase D mini-plan (`IsStamToEPIBridgeHyp` 入口形式整形)

> **Parent**: [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md) §Phase D
> **Sister consumer**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §Phase A
> **Mathlib inventory (上流)**: [`epi-debruijn-integration-mathlib-inventory.md`](epi-debruijn-integration-mathlib-inventory.md)
> **Status**: 設計起草 (2026-05-25)。実装着手前提条件はすべて満たし済 (sister 2 unblock 完了、`IsDeBruijnTailHyp` honest 再導入完了、`IsDeBruijnRegularityHyp` density_t_eq 確定、`IsStamToEPIScalingHyp` AntitoneOn signature 確定)。

## Position

- 親 sub-plan: `epi-debruijn-integration-plan.md` (Phase A〜C-5 closure 完了、本 mini-plan は Phase D を委任受け)
- 親 moonshot: `epi-moonshot-plan.md` (PASS-THROUGH publish、L-EPI2 = de Bruijn integration discharge は親 sub-plan が担当)
- sister consumer: `epi-stam-to-conclusion-plan.md` §Phase A (Csiszár scaling argument 合流、`IsStamToEPIBridgeHyp` を genuine 化する側) — 本 mini-plan の D-4 export 出力を入口として受ける
- 直前依存 (Phase C-5): `epi-debruijn-tail-reintroduction-plan.md` (`IsDeBruijnTailHyp` EReal lift + Z_law、Gaussian discharge `isDeBruijnTailHyp_of_gaussian` 提供)
- 直前依存 (Phase B): `epi-debruijn-regularity-refactor-plan.md` (`IsDeBruijnRegularityHyp` density_t_eq pinned)

### 親 plan の Phase D 暫定記述との差分

親 plan `epi-debruijn-integration-plan.md` §Phase D (line 393-453) は 4 step (D-1〜D-4) を暫定列挙していたが、本 mini-plan で以下のように再定義する:

| 親 plan step | 本 mini-plan での扱い | 理由 |
|---|---|---|
| D-1: `g(t)` 定義 + 基本性質 | **D-1 として継承**、規模上方修正 (~40-70 行) | `entropyPower` 経由の gap 関数、Mathlib `Monotone`/`AntitoneOn` の結論形整合確認が必要 |
| D-2: Phase C 出力を `g(t)` 積分表現に reshape | **D-2 として継承**、規模据置 (~20-30 行) | bounded-T `IsDeBruijnIntegrationHyp` を Csiszár scaling 引数 `gap_s` に変換する bridge |
| D-3: 14 件 `@audit:suspect` 降格 | **本 mini-plan から削除**、sister Phase A 完了後 cleanup task に移管 (本 plan 責務外、§Phase D-3 の扱い 参照) | `EPIL3Integration.lean:547-557` §12 honesty note 3 が「14 件降格は sister 完了後の `closed-by-successor` 付与で本 plan 責務外」と明示 |
| D-4: sister export | **D-4 として継承**、規模据置 (~10-20 行) | sister Phase A 入口に渡す bridge lemma signature 確定 |

加えて本 mini-plan で以下 2 step を追加する:

| 新 step | 内容 | 規模 |
|---|---|---|
| D-0 | Mathlib `entropyPower` / `Monotone` / `MonotoneOn` / `AntitoneOn` の結論形再確認 (Mathlib-shape-driven; inventory に追記する形) | ~20-30 行 (docs 追記) |
| D-V | `lake env lean` silent 確認 + 親 plan 進捗ブロック更新 + `InformationTheory.lean` import 確認 | ~5-10 行 |

## ゴール / Approach

### 全体戦略

Phase C 出力 (`IsDeBruijnIntegrationHyp X Z P T` の bounded-T genuine discharge、Gaussian 限定 + `IsDeBruijnTailHyp` honest hypothesis 経由) と Phase B 出力 (`IsHeatFlowFamilyHyp` regularity) を、**sister Phase A の `IsStamToEPIScalingHyp` AntitoneOn signature が消費しやすい入口形式**に整形する。

Csiszár scaling argument 全体 (gap monotonicity → EPI 結論) は sister 担当、本 mini-plan は **de Bruijn 側の reshape のみ**:

```
[Phase C 出力 (bounded-T 積分恒等式)]    [Phase B 出力 (heat-flow regularity)]
       │                                      │
       └──────────────┬───────────────────────┘
                      ▼
         D-1: gap 関数 g(t) 定義 + 基本性質 (entropyPower gap 形)
                      ▼
         D-2: 積分表現 (gap'(t) を Phase C の積分恒等式と Stam から導く形)
                      ▼
         D-4: sister Phase A の AntitoneOn 入口 lemma (export)
                      ▼
        [sister Phase A: Csiszár scaling argument 全体]
                      ▼
        [IsStamToEPIBridgeHyp X Y P genuine 化]
                      ▼
        [14 件 @audit:closed-by-successor 降格 — sister Phase A 完了後 cleanup]
```

### 鍵となる構造選択 (Mathlib-shape-driven)

D-1 の `g(t)` 定義は **sister `IsStamToEPIScalingHyp` の `AntitoneOn (fun s => ...) (Set.Icc 0 1)` body と shape を揃える** ことが最優先:

```lean
-- sister `EPIStamToBridge.lean:210-216` の AntitoneOn 引数:
AntitoneOn
  (fun s : ℝ =>
    entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s))
      - entropyPower (P.map (heatFlowPath2 X Z_X s))
      - entropyPower (P.map (heatFlowPath2 Y Z_Y s)))
  (Set.Icc (0 : ℝ) 1)
```

本 mini-plan の `g(t)` (または `gap_s`) を **同形式で記述**することで D-4 export lemma が型レベルで sister に直接渡る。親 plan §Phase D の暫定スケッチでは `g(t) := entropyPower (X+Y+√t·Z) - entropyPower (X+√t·Z) - entropyPower (Y+√t·Z)` (`√t · Z` 形) を採用していたが、これは sister の `heatFlowPath2 _ Z _ s = √(1-s) · _ + √s · Z` 形 (`InformationTheory/Shannon/HeatFlowPath.lean`) と shape が異なる。**本 mini-plan は sister 形 (`heatFlowPath2`) を採用** (Mathlib-shape-driven: 下流の `AntitoneOn` 結論形に直接合うように上流を選ぶ)。

Phase C の bounded-T 積分恒等式は `√t · Z` 形 (`gaussianConvolution X Z T`) で書かれているため、D-2 で **`gaussianConvolution → heatFlowPath2` の shape 変換 bridge** が 1 件必要 (規模 ~10 行、`Real.sqrt_one_sub_sq` 系 reparametrization、または事実上 reparametrization なしに別 path として並走させる戦略も可)。

### 段階的 ship 設計

本 mini-plan は単一 ship (Tier 区分なし)。理由: 規模が小さく (~100-150 行)、partial ship の価値が薄い。Phase D 完了 = 全 step 完了で 1 commit に集約。

### 規模見積もり

| step | 内容 | 想定行数 | 中央予測 |
|---|---|---|---|
| D-0 | Mathlib shape 在庫確認 (`entropyPower` / `AntitoneOn` / `MonotoneOn`) | ~20-30 (docs) | 25 |
| D-1 | `g(t)` 定義 + 基本性質 (`g(0)`, `g(1)`, measurability, continuity, gap shape == sister `AntitoneOn` 引数) | ~40-70 | 55 |
| D-2 | Phase C 出力を `g(t)` の積分表現に reshape (`gaussianConvolution ↔ heatFlowPath2` shape 変換 + Stam 入力点の bridge) | ~20-30 | 25 |
| D-4 | sister export lemma (`bridge_input_for_csiszar_scaling` 等の入口 lemma + docstring) | ~10-20 | 15 |
| D-V | `lake env lean` silent + 親 plan 進捗ブロック更新 | ~5-10 | 7 |
| **合計** | | **~95-160** | **~127** |

中央予測 **~130 行**。`EPIL3Integration.lean` に §13 として追加するか、新規 file `InformationTheory/Shannon/EPIDeBruijnBridgeInput.lean` を切るかは D-0 の規模確認後に判断 (現状 `EPIL3Integration.lean` は 1104 行で更に追加するか分離するかは閾値判断、本 mini-plan の素朴な default は **`EPIL3Integration.lean` §13 として追加**)。

---

## 進捗

- [x] D-0 — Mathlib shape 在庫確認 ✅ 2026-05-25 (inventory +175 行、5 section: `entropyPower`/`AntitoneOn`/`heatFlowPath2`/sister AntitoneOn lambda verbatim/`Y:=0` 退化検算結果)
- [x] D-1 — `csiszarGap` 定義 + 2 endpoint lemma ✅ 2026-05-25 (`csiszarGap`/`csiszarGap_at_zero`/`csiszarGap_at_one_eq_zero_of_gaussian_pair`、shape verbatim 一致、Gaussian saturation 経由 genuine 証明)
- [x] D-2 — Phase C → csiszarGap bridge → **L-DBD-2-α 発火** ✅ 2026-05-25 (戦略 β 不可: `entropyPower (Dirac 0) = 1` (plan 予測 `0` は誤り) → 退化 gap = -1 定数 trivially `AntitoneOn` → degenerate-definition exploitation 直撃)、戦略 γ (docs-only sister 委譲 stub) に honest 降格
- [x] D-4 — sister export `rfl` lemma ✅ 2026-05-25 (`csiszarGap_shape_for_sister` で `rfl` 通過確認、shape verbatim 一致 D-0 で防御)
- [x] D-V — `lake env lean` silent + 親 plan / 本 mini-plan 進捗ブロック更新 ✅ 2026-05-25 (commit `15684b0` worktree → main merge silent)

proof-log: yes (Phase D 完了時に `docs/shannon/proof-log-epi-debruijn-integration-phaseD.md` を残す)

> **Phase D-3 (14 件 `@audit:suspect` 降格) は本 mini-plan の責務外**。sister `epi-stam-to-conclusion-plan` Phase A 完了 (Csiszár scaling argument による `IsStamToEPIBridgeHyp` genuine 化) の post-merge cleanup task として、当該 sister plan Phase A Done 条件に「14 件 `@audit:suspect(epi-debruijn-integration-plan)` → `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` 一括書換 (位置: `EPIL3Integration.lean` line 120 / 134 / 210 / 224 / 239 / 253 / 268 / 283 / 316 / 365 / 378 / 401 / 458 / 485)」を明文化する。本 mini-plan の Done 条件には含めない (sister 完了に依存する task を本 plan closure 基準に入れると Phase D 完了不能になる)。詳細 → §「Phase D-3 の扱い」参照。

---

## D-0 — Mathlib shape 在庫確認 📋

### スコープ

D-1 着手前に Mathlib + 既存 `InformationTheory/Shannon/` ファイルから以下 3 件の verbatim 確認:

1. **`InformationTheory.Shannon.EntropyPowerInequality.entropyPower`** — `EntropyPowerInequality.lean:80` 前後の verbatim 定義 + sister `IsStamToEPIScalingHyp` body 内での使い方 (`EPIStamToBridge.lean:202-216`)
2. **`Monotone` / `MonotoneOn` / `AntitoneOn` / `AntitoneOn.le_of_le_endpoint`** — Mathlib 結論形 verbatim、特に `AntitoneOn` の引数順 (`s ∈ Set.Icc 0 1`、`t ∈ Set.Icc 0 1`、`s ≤ t → f t ≤ f s`)
3. **`heatFlowPath2`** — `InformationTheory/Shannon/HeatFlowPath.lean` の verbatim signature + `heatFlowPath2_zero` / `heatFlowPath2_one` lemma 群 + 既存 simp set

### Approach

D-0 はコード書込なし、`docs/shannon/epi-debruijn-integration-mathlib-inventory.md` に **「Phase D 補遺」section を追加**して 3 件の verbatim を記録 (`mathlib-inventory` agent に dispatch する選択も可)。`[...]` typeclass prerequisites verbatim、`Conclusion form` verbatim を CLAUDE.md `Subagent Inventory of Mathlib Lemmas` 規律に従って記載。

### ステップ

- [ ] **D-0-1**: `entropyPower` 定義 verbatim (`EntropyPowerInequality.lean:80` 付近、`entropyPower μ := Real.exp (2 * differentialEntropy μ)` 形を確認)、`Real.exp_pos` / `Real.exp_log` 等の同伴 lemma も verbatim
- [ ] **D-0-2**: `AntitoneOn` Mathlib verbatim (`Mathlib/Order/Monotone/Basic.lean` 周辺)、特に `Set.Icc 0 1` 限定の reuse 補題 (`AntitoneOn.le_of_le_endpoint` 等)
- [ ] **D-0-3**: `heatFlowPath2` (`InformationTheory/Shannon/HeatFlowPath.lean`) verbatim + 6 lemma (`heatFlowPath2_zero`, `heatFlowPath2_one`, `heatFlowPath2_law_of_gaussian` 等の F.1 6 件、Phase 0 `0d54e89` で landing) verbatim

### Done 条件

- `epi-debruijn-integration-mathlib-inventory.md` に「Phase D shape inventory」section 追加 (~20-30 行)
- D-1 / D-2 / D-4 着手時に「lemma X が見つからない」「結論形が違う」で逆戻りしない状態
- 特に sister `IsStamToEPIScalingHyp` body の `AntitoneOn` 引数と本 mini-plan の `g(t)` の shape が **lambda-by-lambda で一致**することを紙の上で確認

### 撤退ライン

なし (在庫確認のみ、撤退する性質の作業ではない)。仮に **既存** `entropyPower` / `heatFlowPath2` / `AntitoneOn` のいずれかに defect を発見した場合は **D-0-defect** として `CLAUDE.md` 「検証の誠実性」inline 検出を発動、その場で `@audit:suspect(...)` タグを docstring に直書きし orchestrator に報告。defect の上に積み上げない。

---

## D-1 — `g(t)` 定義 + 基本性質 📋

### スコープ

`InformationTheory/Shannon/EPIL3Integration.lean` §13 (or 新規 file) に Csiszár scaling gap 関数 `g(s)` を定義 + 基本性質を準備:

```lean
/-- **Csiszár scaling gap function**.

`csiszarGap X Y Z_X Z_Y P s` is the EPI gap at heat-flow path parameter
`s ∈ [0, 1]` along the path `heatFlowPath2`:

  `gap_s := entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s))
            - entropyPower (P.map (heatFlowPath2 X Z_X s))
            - entropyPower (P.map (heatFlowPath2 Y Z_Y s))`

Shape: matches verbatim the lambda body of `IsStamToEPIScalingHyp`'s
`AntitoneOn` argument (`EPIStamToBridge.lean:210-216`). -/
noncomputable def csiszarGap {Ω : Type*} [MeasurableSpace Ω]
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) (s : ℝ) : ℝ :=
  entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s))
    - entropyPower (P.map (heatFlowPath2 X Z_X s))
    - entropyPower (P.map (heatFlowPath2 Y Z_Y s))
```

基本性質:
- `csiszarGap_at_zero` (`s = 0` で `heatFlowPath2 _ _ 0 = _`、gap が `entropyPower (X+Y) - entropyPower X - entropyPower Y` に等しい)
- `csiszarGap_at_one` (`s = 1` で `heatFlowPath2 _ Z _ 1 = Z`、Gaussian saturation で gap = 0)
- (`measurability` / `continuity` は sister Phase A の AntitoneOn 証明で要求されるが、本 mini-plan では statement のみ用意し proof は Gaussian limited で停止許容)

### Approach

`entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s))` の項を **3 分割せず構造体形に保つ** ことで sister `AntitoneOn` 引数と type-level に一致させる。`s = 0` / `s = 1` の値は既存 `heatFlowPath2_zero` / `heatFlowPath2_one` (Phase 0 で landing 済) で expand。Gaussian saturation `gap_1 = 0` は既存 `entropy_power_inequality_gaussian_saturation` で discharge (sister `EPIStamToBridge.lean:298-306` で同じ pattern が使われている、参照: `isStamToEPIBridgeHyp_of_scaling_limit`)。

### ステップ

- [ ] **D-1-1**: `csiszarGap` 定義 (`noncomputable def`, ~5-10 行)
- [ ] **D-1-2**: `csiszarGap_at_zero` (`s = 0` で X+Y 形に reduce、~10-15 行)
- [ ] **D-1-3**: `csiszarGap_at_one_eq_zero_of_gaussian_pair` (Gaussian saturation で gap = 0、`entropy_power_inequality_gaussian_saturation` 経由、~15-25 行)
- [ ] **D-1-4** (任意 stretch): `csiszarGap` の continuity on `Set.Icc 0 1` (sister Phase A で要求される場合のみ追加、本 mini-plan の default では statement のみ stub、proof は sister 担当)

### Done 条件

- `csiszarGap` 定義が `EPIL3Integration.lean` §13 (or 新規 file) に存在
- `csiszarGap_at_zero` / `csiszarGap_at_one_eq_zero_of_gaussian_pair` が genuine 証明 (Gaussian discharge を `entropy_power_inequality_gaussian_saturation` 経由で経由、sister body のパターンと同形)
- `@audit:ok` (genuine + load-bearing でない、Mathlib pass-through)、または partial 化した場合は `@audit:suspect(epi-debruijn-integration-phaseD-plan)` で sister 完了待ち明示

### 撤退ライン (honest 限定)

- **L-DBD-1-α** (許容): `csiszarGap_at_one_eq_zero_of_gaussian_pair` で要求される `Z_X`, `Z_Y` 独立性 + Gaussian law 仮定が `entropy_power_inequality_gaussian_saturation` の signature と不一致 (例えば `IndepFun Z_X Z_Y P` の証明が必要) の場合、**sister Phase A 入口 lemma に統合**して D-4 で扱う形に降格 (D-1 では statement only)。`@audit:suspect(epi-debruijn-integration-phaseD-plan)` 付与で honest 明示。
- **L-DBD-1-β** (許容): continuity proof が本格化した場合 (~50 行以上)、**sister Phase A に委譲**。本 mini-plan の D-1 は `csiszarGap` 定義 + 2 件 endpoint lemma のみ。

---

## D-2 — Phase C bounded-T 積分恒等式 → `g(t)` 積分表現の reshape 📋

### スコープ

Phase C-1 `bounded_T_ftc_gaussian` (`EPIL3Integration.lean:1037-1085`) は **`√T · Z` 形 (`gaussianConvolution X Z T`)** で書かれている:

```lean
differentialEntropy (P.map (gaussianConvolution X Z T)) - differentialEntropy (P.map X)
  = ∫ t in Set.Ioo 0 T, 1 / (2 * ((v : ℝ) + t)) ∂volume
```

一方 D-1 `csiszarGap` は **`heatFlowPath2 _ _ s = √(1-s) · _ + √s · _` 形 (`s ∈ [0, 1]`)** で書かれている。**両者の shape は同じ heat-flow path だが parameterization が異なる**。

D-2 では Phase C bounded-T 出力を D-1 `csiszarGap` で消費しやすい形に reshape する。具体的には:

- **戦略 α (reparametrization bridge)**: `T = s / (1 - s)` or `T = tan(π s / 2)` 等で `[0, 1]` ↔ `[0, ∞)` を結ぶ reparametrization bridge を 1 件追加 (~15-25 行)
- **戦略 β (両 path 並走)**: D-1 `csiszarGap` (heat-flow path 2 sources) と Phase C `bounded_T_ftc_gaussian` (heat-flow path 1 source) は厳密には異なる path family であり、reparametrization で繋がらない。本 mini-plan では **`gap_s` の `s` 微分を Stam + de Bruijn 経由で直接計算する**形に置き換え、Phase C 出力は「heat-flow path 1 source の積分恒等式が手元にある」という事実のみ参照 (~5-15 行)
- **戦略 γ (sister 委譲)**: 完全に sister Phase A に委譲、本 mini-plan D-2 は statement only (~5 行)

### 推奨 = 戦略 β

理由:
- 戦略 α (reparametrization) は path family が異なる (1-source vs 2-source) ため繋がらない、または繋ぐのに大幅な reparametrization tech が必要 (~50 行以上)
- 戦略 γ は本 mini-plan の独立 deliverable 価値を薄める (D-2 が空に近くなる)
- 戦略 β は **「Phase C 出力 = bounded-T 1-source 積分恒等式 (Gaussian 限定)」「sister Phase A = 2-source heat-flow path の Csiszár scaling argument 全体」** という責務分界を明示し、D-2 を「Phase C の 1-source 結果を sister 入口に渡す形に整形する小規模 bridge」として位置付ける

### ステップ

- [ ] **D-2-1**: `bounded_T_ftc_gaussian` (1-source) を **`csiszarGap` 評価 1 点 (`Y := 0`、`Z_Y := 0` 退化) と比較する補題** を 1 件追加 (Gaussian 限定、~10-15 行) — sister Phase A が 2-source scaling 全体を扱う際、1-source 縮退でこの Phase C 結果を参照できる形を提供
- [ ] **D-2-2**: 上記の `Y := 0` 退化が **honest 退化** (degenerate exploitation でない) であることを docstring で明示。`Y := 0` で `entropyPower (P.map 0) = entropyPower (Dirac 0) = 0` 等の境界処理を確認 (Defect prevention checklist 項目 1 適用: 退化機構の検算)

### Done 条件

- D-2 bridge lemma 1 件 (`bounded_T_ftc_gaussian` → `csiszarGap`-compatible 形) が genuine 証明
- `Y := 0` 退化使用箇所に docstring で「honest 退化、`entropy_power_inequality_gaussian_saturation` の境界形」明示
- `@audit:suspect(epi-debruijn-integration-phaseD-plan)` (sister Phase A 完了待ち)

### 撤退ライン (honest 限定)

- **L-DBD-2-α** (許容): `Y := 0` 退化が `entropyPower (Dirac 0)` の境界値で破綻 (`entropyPower` が `-∞` で `Real.exp` outside) の場合、**戦略 γ (sister 委譲)** に降格。D-2 は statement only に削減。
- **L-DBD-2-β** (許容): Phase C `bounded_T_ftc_gaussian` の `gaussianConvolution X Z T` 形と D-1 `csiszarGap` の `heatFlowPath2` 形が **path family レベルで互換不能**と判明した場合、本 mini-plan の D-2 を「sister Phase A への形式整理メモ」(docs-only 追記) に降格、Lean 実装は sister 担当。

---

## D-4 — sister export lemma 確定 + docstring 📋

### スコープ

sister `epi-stam-to-conclusion-plan` Phase A の Csiszár scaling argument が消費する入口 lemma を 1〜2 件 publish:

```lean
/-- **Bridge input for Csiszár scaling argument** (sister `epi-stam-to-conclusion-plan` Phase A の入口).

D-1 `csiszarGap` の shape は `IsStamToEPIScalingHyp` body 内の `AntitoneOn`
引数と verbatim 一致するため、本 lemma は `csiszarGap` を sister 入口に渡す
formal handoff として機能。

Phase D D-1 / D-2 から sister Phase A への形式 contract:
* Input: `IsStamInequalityHyp X Y P` + `IsDeBruijnIntegrationHyp X Z_X P T`
         (Gaussian 限定) + `IsDeBruijnTailHyp X Z_X P` (honest hypothesis、
         `EReal` lift + `Z_law` 経由)
* Output: `AntitoneOn (csiszarGap X Y Z_X Z_Y P ·) (Set.Icc 0 1)` (証明は sister 担当)

本 lemma は **shape contract のみ** であり、`AntitoneOn` の証明本体は sister が
書く。本 mini-plan の出力は「sister が consume する型と用語が確定済」状態。

`@audit:suspect(epi-debruijn-integration-phaseD-plan)` -/
theorem csiszarGap_shape_for_sister
    {Ω : Type*} [MeasurableSpace Ω]
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) :
    (fun s : ℝ => csiszarGap X Y Z_X Z_Y P s)
      = (fun s : ℝ =>
          entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s))
            - entropyPower (P.map (heatFlowPath2 X Z_X s))
            - entropyPower (P.map (heatFlowPath2 Y Z_Y s))) :=
  rfl
```

つまり D-4 は **type-level handoff** であって本格的な theorem ではない。D-1 で `csiszarGap` を定義した時点で sister の `AntitoneOn` 引数と shape が verbatim 一致 (これは Mathlib-shape-driven 設計の本旨) しているため、`rfl` で渡る (Mathlib `rfl` lemma を 1 件公開して sister 側から `simp [csiszarGap_shape_for_sister]` で書換可能にする)。

### ステップ

- [ ] **D-4-1**: `csiszarGap_shape_for_sister` `rfl` lemma 公開 (~5 行)
- [ ] **D-4-2**: sister 入口 docstring (本 lemma + `IsStamToEPIScalingHyp` への consume path 案内、~10-15 行 docs)
- [ ] **D-4-3** (任意 stretch): sister Phase A が Gaussian 限定で先行 closure 可能なら、本 mini-plan で **`AntitoneOn (csiszarGap ...) (Set.Icc 0 1)` の Gaussian 限定 discharge** を 1 件追加 (sister `InformationTheory/Shannon/EPIStamToBridge.lean:359-370` `isStamToEPIBridgeHyp_of_gaussian_via_scaling` の Gaussian path を borrow、~20-40 行) — これは sister Phase A の Gaussian 枝を本 mini-plan 内で先行 close する選択

### Done 条件

- `csiszarGap_shape_for_sister` lemma が `@audit:suspect(epi-debruijn-integration-phaseD-plan)` 付与で publish
- sister `epi-stam-to-conclusion-plan` Phase A の A-1〜A-6 step (現在 sister 待ち state) が本 lemma を入口として記述できる状態
- sister Phase A 担当 agent が「Phase D 出力が型レベルで sister AntitoneOn と一致」を確認できる

### 撤退ライン

- **L-DBD-4-α** (許容、本来不要): D-1 `csiszarGap` の shape が sister `AntitoneOn` 引数と verbatim 一致しない (Mathlib-shape-driven 設計失敗) と判明した場合、D-1 に戻って shape pivoting。これは D-0 の在庫確認で防ぐべき failure mode、D-0 完了時点で防がれている前提。

---

## D-V — 検証 + 親 plan 進捗ブロック更新 📋

### スコープ

- `lake env lean InformationTheory/Shannon/EPIL3Integration.lean` silent (0 error / 0 sorry / 警告最小限)
- (新規 file を切った場合) `lake env lean InformationTheory/Shannon/EPIDeBruijnBridgeInput.lean` silent + `InformationTheory.lean` import 1 行追加
- `docs/shannon/epi-debruijn-integration-plan.md` Phase D 進捗ブロックを `[x]` に更新、判断ログに「Phase D は本 mini-plan に委任」+「実装完了 commit hash」を追記
- sister `docs/shannon/epi-stam-to-conclusion-plan.md` Phase A 進捗ブロックの「sister 待ち」status を更新 (本 mini-plan の D-4 出力が利用可能になった旨)、判断ログに 1 件追記
- `docs/textbook-roadmap.md` T2-D de Bruijn 行を本 mini-plan 完了で進捗更新 (14 件降格は sister 完了後の cleanup なので **ここでは更新しない**)

### Done 条件

- `EPIL3Integration.lean` (+ optionally 新規 file) `lake env lean` silent
- 親 plan + sister plan の進捗ブロック / 判断ログ更新
- Independent honesty audit (新規 staged predicate が出る場合のみ): D-1 `csiszarGap` は **新規 def だが staged predicate ではなく `noncomputable def + theorem` の通常出力**のため独立 audit 起動条件 (`@audit:staged(<slug>)` predicate 新規導入) には該当しない。`@audit:suspect(epi-debruijn-integration-phaseD-plan)` 付与のみで OK (sister 完了で `@audit:closed-by-successor(...)` に降格)

---

## Phase D-3 の扱い (本 mini-plan 責務外)

### 親 plan §Phase D の暫定 D-3 (14 件降格) を本 mini-plan から削除する理由

1. **`EPIL3Integration.lean:547-557` §12 honesty note 3 の明示** — 14 件は「`IsStamToEPIBridgeHyp` field が load-bearing で sister 担当」「de Bruijn integration は scaling の input であって discharge ではないので本 plan で降格不可」と既に code 内に明記 (code が SoT)
2. **`EPIL3Integration.lean:1087-1102` Phase D section closure note の明示** — 同 file の Phase D section が「14 件降格は sister 完了後の `closed-by-successor(epi-stam-to-conclusion-plan)` 付与」と既に書いている
3. **honest closure 基準の維持** — 14 件降格を本 mini-plan の Done 条件に含めると Phase D は sister Phase A 完了まで closure 不能、これは本 mini-plan を「sister 待ち plan」に降格させる。一方 14 件を sister の post-merge cleanup に外出しすれば、本 mini-plan は D-1 / D-2 / D-4 (gap 関数 + reshape + sister export) の 3 deliverable で単独 closure 可能

### 14 件の post-merge cleanup task を sister plan に明文化する補完作業

本 mini-plan 起草と同時に、sister `docs/shannon/epi-stam-to-conclusion-plan.md` Phase A の Done 条件 (line 507-517 付近) に以下 1 行を追記する補完 task が発生する:

> **Phase A 完了後 post-merge cleanup**: `EPIL3Integration.lean` の 14 件 `@audit:suspect(epi-debruijn-integration-plan)` を `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` に一括書換 (位置: line 120 / 134 / 210 / 224 / 239 / 253 / 268 / 283 / 316 / 365 / 378 / 401 / 458 / 485)。書換コマンド sketch: `sed -i 's/@audit:suspect(epi-debruijn-integration-plan)/@audit:closed-by-successor(epi-stam-to-conclusion-plan)/g'` (slug 末尾 `-plan` の有無は `docs/audit/audit-tags.md` 語彙に合わせる)。`lake env lean InformationTheory/Shannon/EPIL3Integration.lean` silent 確認。

これは本 mini-plan 内で記述する必要はなく、sister plan 編集として 1 turn で完了する補完 task。**本 mini-plan の Done 条件には含めない**。

---

## 撤退ライン総覧 (本 mini-plan、honest 限定)

| slug | step | 内容 | hypothesis 名 (例) | 解除条件 |
|---|---|---|---|---|
| L-DBD-1-α | D-1 | `csiszarGap_at_one_eq_zero_of_gaussian_pair` で `Z_X` / `Z_Y` 独立性が要求された場合の sister 統合 | (D-4 に統合) | sister Phase A 着手 |
| L-DBD-1-β | D-1 | continuity proof 本格化時の sister 委譲 | (statement only に降格) | sister Phase A 着手 |
| L-DBD-2-α | D-2 | `Y := 0` 退化境界破綻時の戦略 γ 降格 | (D-2 statement only) | sister Phase A 着手 |
| L-DBD-2-β | D-2 | Phase C `gaussianConvolution` 形と D-1 `heatFlowPath2` 形の path 互換不能 | (docs-only 降格) | sister Phase A 着手 |
| L-DBD-4-α | D-4 | D-1 shape が sister AntitoneOn と verbatim 一致しない (D-0 で防ぐべき) | (D-1 reshape) | D-0 完了時点で防がれている前提 |

**全撤退ライン共通規律** (CLAUDE.md `検証の誠実性`):

- **`Prop := True` placeholder 禁止**
- **結論型 ≡ 仮説型 + `body := h` (循環) 禁止**
- **load-bearing hypothesis を完成と称する name laundering 禁止** (`*_discharged` / `*_full` 命名禁止、`csiszarGap_shape_for_sister` は `rfl` lemma で genuine、name laundering ではない)
- 撤退ライン発動時は docstring で「NOT a discharge / load-bearing on <sister Phase A 出力>」を必ず明示
- **退化機構の検算**: D-2 で `Y := 0` 退化を採用する場合、`fisherInfoOfDensity 0 = 0` 退化機構 (defect #1 / #3 と同根) を必ず紙の上で検算 (Defect prevention checklist 項目 1)

---

## 実装着手前提条件 (すべて満たし済、2026-05-25 現在)

| 前提 | 状態 | 関連 commit / plan |
|---|---|---|
| sister 1 (`epi-stam-discharge-plan`) Phase D 出力 | 38/39 ok (unblock) | sister plan §Phase D |
| sister 2 (`epi-stam-to-conclusion-plan`) Phase 0 (scaling refactor) | 完了 (AntitoneOn signature 確定) | commits `0d54e89` / `78cf2ec` / `2809168` |
| `IsDeBruijnTailHyp` honest 再導入 | 完了 (EReal lift + Z_law) | sub-plan `epi-debruijn-tail-reintroduction-plan.md` |
| `IsDeBruijnRegularityHyp` density_t_eq pinned | 完了 (caveat 解消) | sub-plan `epi-debruijn-regularity-refactor-plan.md` |
| Phase C-1 `bounded_T_ftc_gaussian` | 完了 (`EPIL3Integration.lean:1037-1085`) | Wave 3 second batch `0fe2ad4` |
| `heatFlowPath2` + 6 lemma | 完了 (`HeatFlowPath.lean` F.1 6 件) | commit `0d54e89` |

すべて満たされている → **本 mini-plan は実装着手可能状態**。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 mini-plan 起草**: 親 plan `epi-debruijn-integration-plan.md` §Phase D (line 393-453) の暫定記述を本 mini-plan に委任。option 2 (mini-plan 新規作成) を採用 (option 1 = 親 plan 内処理は同 family の 4 件 mini-plan 前例 (Phase 0, C-5 tail-reintroduction, regularity-refactor, integration phaseD) との整合性で却下)。Phase D-3 (14 件降格) は案 α (本 plan から削除、sister cleanup task に移管) を採用、理由は `EPIL3Integration.lean:547-557` §12 honesty note 3 が code 内 SoT で「14 件降格は sister 完了後の `closed-by-successor` 付与で本 plan 責務外」と既に明示しているため。D-1 の `csiszarGap` shape は親 plan 暫定の `√t · Z` 形ではなく sister `IsStamToEPIScalingHyp` の `heatFlowPath2` 形を採用 (Mathlib-shape-driven: 下流 sister の `AntitoneOn` 引数と type-level に一致させる)。新 step D-0 (Mathlib shape 在庫確認) + D-V (検証) を追加、合計 5 step (D-0/D-1/D-2/D-4/D-V) 構成、中央予測 ~130 行。実装着手前提条件はすべて満たし済 (sister 2 unblock 完了、Phase C-5 tail honest 再導入完了、Phase B regularity-refactor 完了、Phase 0 AntitoneOn signature 確定)。

2. **2026-05-25 実装完了 + L-DBD-2-α 発火 (戦略 β → γ honest 降格)**: commit `15684b0` (worktree) で D-0 / D-1 / D-2 statement-only / D-4 / D-V を実装、`lake env lean InformationTheory/Shannon/EPIL3Integration.lean` silent。**Plan 予測誤り発見 (重要、sister Phase A 設計時参照)**: D-0 inventory で `differentialEntropy (Measure.dirac 0)` の Mathlib 値を verbatim 確認 → `differentialEntropy_dirac = 0` (`DifferentialEntropy.lean:147`、`-∞` ではない)、よって `entropyPower (Measure.dirac 0) = Real.exp (2 * 0) = 1` (Plan §D-2-2 の予測「`0`」は誤り)。これにより D-2 戦略 β `Y := 0` 退化検算: `heatFlowPath2 0 0 s = 0 pointwise` → `P.map (heatFlowPath2 0 0 s) = Measure.dirac 0` → `entropyPower (Dirac 0) = 1`、`csiszarGap X 0 Z_X 0 P s = entropyPower(...) - entropyPower(...) - 1 = -1` (定数!) → 定数関数は trivially `AntitoneOn` → **degenerate-definition exploitation 直撃** (CLAUDE.md「退化定義の悪用」defect tells) → 戦略 β 不可、戦略 γ (docs-only sister 委譲 stub) に honest 降格。L-DBD-2-α 発火条件は plan 想定 (`entropyPower (Dirac 0) = -∞` で `Real.exp` outside) と異なるが、撤退ライン slug は同じ。**sister Phase A 担当 implementer に申し送り**: 2-source 退化境界 (`Y := 0`、`Z_Y := 0` 等) の取扱いで `entropyPower (Dirac 0) = 1` を前提に設計すること。実装中 D-2 marker として `example : True := trivial` を一度書き出したが、CLAUDE.md `:True` defect tells に該当するため即削除し `/-! ... -/` 文書ブロックに置換 (honest 自己訂正)。新規 staged predicate なし → independent audit 起動条件非該当。実測行数 360 行 (Lean 185 + docs 175、見積 ~130 の +177%、D-0 完全 verbatim inventory + D-2 戦略 γ docstring 詳細化のため)。

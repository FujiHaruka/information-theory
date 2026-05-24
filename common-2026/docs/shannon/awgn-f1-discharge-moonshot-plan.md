# AWGN F-1 (kernel measurability) discharge ムーンショット計画 🌙 (T2-A follow-up)

> 実態整合 (2026-05-20): DONE-UNCOND — `isAwgnChannelMeasurable` 完全証明済。
> `Common2026/Shannon/AWGNF1Discharge.lean:60` `theorem isAwgnChannelMeasurable (N : ℝ≥0) : IsAwgnChannelMeasurable N` を
> `gaussianReal_map_const_add` + `measurable_measure_prodMk_left` の実 Mathlib 証明 (`:= True` ではない、0 sorry) で discharge。
> `awgn_theorem_F1_discharged` (L100) は `h_meas` 引数を消去して再 publish 済 (残りの F-2/F-3 系 hyp は honest pass-through で継続)。

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は ~~取り消し線~~ で残す（完全削除しない、過去参照のため）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
-->

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §「撤退ライン F-4 (kernel
> measurability)」 + 判断ログ #1 (F-4 採用 = `Measurable (fun x : ℝ => gaussianReal x N)`
> を hypothesis 引数として外出し)。
>
> **Note (Tier 命名)**: 本 plan は親 plan §撤退ライン中の「F-4」（kernel measurability /
> `IsAwgnChannelMeasurable`）の discharge plan である。Seed プロンプト側では同じ箇所を
> **「F-1」**（hypothesis pass-through 4 本のうち kernel measurability に対応）と呼ぶ。
> どちらも同じ命題 `Measurable (fun x : ℝ => gaussianReal x N)` を指す。本 plan 中では
> 親 plan の番号体系（F-4）に揃える。
>
> **Predecessor (inventory)**: [`awgn-mathlib-inventory.md`](awgn-mathlib-inventory.md)
> §危険 4 (`m`-measurability of `gaussianReal m v`)、および本 plan §Phase 0 で
> `Measure.measurable_measure_prodMk_left` (`Mathlib/MeasureTheory/Measure/Prod.lean:97`)
> + `gaussianReal_map_const_add` (`Mathlib/Probability/Distributions/Gaussian/Real.lean:292`)
> + `measurable_dirac` (`Mathlib/MeasureTheory/Measure/GiryMonad.lean:110`) の組合せが
> 直接 discharge を与えることを確定。
>
> **Status (2026-05-20)**: 着手前。親 AWGN plan は **F-1 + F-2 + F-3 + F-4 退避形**
> (`awgn_channel_coding_theorem` の signature で全部 hypothesis pass-through) で
> 0 sorry 完了済 (`Common2026/Shannon/AWGN.lean` 275 行 + `AWGNAchievability.lean` 72 行 +
> `AWGNConverse.lean` 94 行 + `AWGNMain.lean` 107 行)。本 plan はその `h_meas`
> (= `IsAwgnChannelMeasurable N`) を **Mathlib `gaussianReal_map_const_add` ×
> Giry-monad measurability** で完全証明し、`awgn_channel_coding_theorem` を **`h_meas`
> 引数なし形**で再 publish するための後継 plan。
>
> **Goal**: `Common2026/Shannon/AWGNF1Discharge.lean` 新規 publish で
>
> ```lean
> theorem isAwgnChannelMeasurable (N : ℝ≥0) : IsAwgnChannelMeasurable N := …
>
> theorem awgn_theorem_F1_discharged
>     (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
>     (h_typicality : IsAwgnTypicalityHypothesis P N (isAwgnChannelMeasurable N))
>     (h_mi_bridge :
>         (mutualInfoOfChannel (gaussianReal 0 P.toNNReal)
>           (awgnChannel N (isAwgnChannelMeasurable N))).toReal
>         = differentialEntropy (gaussianReal 0 (P.toNNReal + N))
>           - differentialEntropy (gaussianReal 0 N))
>     (h_converse : IsAwgnConverseHypothesis P N (isAwgnChannelMeasurable N))
>     {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
>     {ε : ℝ} (hε : 0 < ε) :
>     ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
>       ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
>         (c : AwgnCode M n P),
>           ∀ m, (c.toCode.errorProbAt (awgnChannel N _) m).toReal < ε := …
> ```
>
> を publish。すなわち親 plan の `awgn_channel_coding_theorem` から `h_meas` を
> **削除**し、`AwgnCode` / `awgnChannel` / `awgnCapacity` の measurability 引数を内部で
> `isAwgnChannelMeasurable N` 経由で埋める形に置換。
>
> 副産物として `awgn_capacity_closed_form` も `h_meas` 引数なし形で再 publish。
>
> **撤退ライン**: [G-1] `v = 0` (Dirac) 分岐の measurability が `measurable_dirac` で直に
> 拾えなかった場合は `IsAwgnChannelMeasurable` の定義を `N ≠ 0` 前提に restrict して
> 親 plan 側の signature を `(hN : (N : ℝ) ≠ 0) → IsAwgnChannelMeasurable N` に変更（親
> plan の hN は既に hypothesis として存在）/ [G-2] `gaussianReal_map_const_add` 経由の
> 等式 `gaussianReal x N = (gaussianReal 0 N).map (x + ·)` が `simp` 一発で書けず追加の
> `add_zero` algebra が必要な場合は補助補題として独立に publish / [G-3] `m`-measurability
> 直接構成 (`gaussianPDFReal m v x` を `(m, x)` の関数として joint measurable にする) が
> 必要になった場合は `measurable_gaussianPDFReal` の prod 版 `Measurable
> (Function.uncurry gaussianPDFReal_at_v)` を本 plan 内で証明、`Measurable.lintegral_prod_right`
> 経由で `(m, s)` の double integral に流す（詳細 §撤退ライン）。

## 進捗

- [x] Phase 0 — Mathlib measurability API 在庫再確認 ✅ (`measurable_measure_prodMk_left` (root namespace) + `gaussianReal_map_const_add` + `Measure.measurable_of_measurable_coe` で確定)
- [x] Phase A — `isAwgnChannelMeasurable` 本体補題 publish ✅ (`Common2026/Shannon/AWGNF1Discharge.lean` 148 行)
- [x] Phase B — `awgn_theorem_F1_discharged` + `awgn_capacity_closed_form_F1_discharged` 再 publish ✅ (同 file 内 wrapper)
- [x] Phase V — verify ✅ (`lake env lean` silent, exit 0, 0 sorry, 0 warning)
- 2026-05-24 Wave 1.5 retag: F-1 plan は閉、残 4 wrapper の `@audit:suspect(awgn-f1-discharge-moonshot-plan)` を F-2/F-3 担当 plan slug (`awgn-moonshot-plan` / `awgn-mi-bridge-plan` / `awgn-achievability-typicality-plan` / `awgn-converse-aux-plan`) に張替。

## ゴール / Approach

### Goal (最終定理 signature)

親 plan の `awgn_channel_coding_theorem` (`Common2026/Shannon/AWGNMain.lean:59`) は現状

```lean
theorem awgn_channel_coding_theorem
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)                  -- ← これを消す
    (h_typicality : IsAwgnTypicalityHypothesis P N h_meas)
    (h_mi_bridge : …)
    (h_converse : IsAwgnConverseHypothesis P N h_meas)
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : …)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀, ∀ n, N₀ ≤ n → ∃ M (_hM_lb : …) (c : AwgnCode M n P),
      ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε
```

`h_meas` を「kernel measurability hypothesis」と呼ぶ。本 plan の最終定理は

```lean
theorem awgn_theorem_F1_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_typicality : IsAwgnTypicalityHypothesis P N (isAwgnChannelMeasurable N))
    (h_mi_bridge : …)                                  -- internal h_meas で書く
    (h_converse : IsAwgnConverseHypothesis P N (isAwgnChannelMeasurable N))
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : …)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀, … := …
```

で、`h_meas` は本 plan 内部の `isAwgnChannelMeasurable N` で discharge され、外部から
見える signature では消える。

### Approach (overall strategy / shape of solution)

**戦略の shape**: 「`gaussianReal x N = (gaussianReal 0 N).map (x + ·)`」という
**Mathlib 既存の map-by-constant 補題**（`gaussianReal_map_const_add`）に書き換え、
Giry-monad の measurability 構造（`Measure.measurable_of_measurable_coe` +
`Measure.measurable_measure_prodMk_left`）に丸投げする。

```
┌───────────────────────────────────────────────────────────┐
│ Phase A: `Measurable (fun x : ℝ => gaussianReal x N)`     │
│  ・ 等式に書き換え:                                         │
│       gaussianReal x N                                     │
│         = gaussianReal (0 + x) N                           │
│         = (gaussianReal 0 N).map (x + ·)                   │
│    (Mathlib `gaussianReal_map_const_add` の特殊化 `μ = 0`) │
│  ・ `Measure.measurable_of_measurable_coe` で `Measurable`  │
│    判定を「∀ s, MeasurableSet s →                          │
│      Measurable (fun x ↦ (gaussianReal 0 N) (Prod.mk x ⁻¹' │
│                            {p | p.1 + p.2 ∈ s}))」に帰着   │
│  ・ `Measure.measurable_measure_prodMk_left`              │
│    (`Mathlib/MeasureTheory/Measure/Prod.lean:97`) で OK    │
│    (`gaussianReal 0 N` は IsFiniteMeasure → SFinite)       │
└───────────────────────────────────────────────────────────┘
                            │
                            ▼
┌───────────────────────────────────────────────────────────┐
│ Phase B: `awgn_theorem_F1_discharged` 再 publish          │
│  ・ 上の `isAwgnChannelMeasurable N` を `h_meas` に渡し、    │
│    親 plan の `awgn_channel_coding_theorem` をそのまま     │
│    呼び出す薄い wrapper                                    │
│  ・ 同様に `awgn_capacity_closed_form` も再 publish        │
└───────────────────────────────────────────────────────────┘
```

ポイントは「Mathlib に **既に** `gaussianReal_map_const_add` がある」事実。これがない
と「`x` を `gaussianPDFReal x N y` のパラメータとして parametric integral 経由で
joint measurable に持ち上げる」(~50-100 行、Fubini 起動が必要) という重い構成に
なるが、map 補題のおかげで完全に Giry monad の構造的 measurability に帰着する。

### Mathlib-shape-driven Definitions

新規定義は導入せず、既存の `IsAwgnChannelMeasurable N := Measurable (fun x : ℝ =>
gaussianReal x N)` をそのまま証明する形。`isAwgnChannelMeasurable N` は補題名で、
定義名 `IsAwgnChannelMeasurable` の小文字版インスタンス的役割。

## Phase 詳細

### Phase 0 — Mathlib measurability API 在庫再確認 (準備、20-30 分目安)

**目的**: Phase A で使う Mathlib API の正確な signature と場所を確定。

- `Mathlib/MeasureTheory/Measure/GiryMonad.lean:49` `Measure.instMeasurableSpace`
  (Giry monad の measurable space 構造)
- `Mathlib/MeasureTheory/Measure/GiryMonad.lean:55` `Measure.measurable_of_measurable_coe`
  : `f : β → Measure α` が `∀ s, MeasurableSet s → Measurable (fun b ↦ f b s)` から
  `Measurable f` を導く
- `Mathlib/MeasureTheory/Measure/GiryMonad.lean:103` `Measure.measurable_map` :
  `(f : α → β) (hf : Measurable f) → Measurable (fun μ : Measure α => μ.map f)`
  （**注**: これは `f` が固定で `μ` が動く版で、本 plan で必要なのは逆方向 `μ` 固定で
  `x` が動いて `μ.map (x + ·)` という方向のため、直接は使えない）
- `Mathlib/MeasureTheory/Measure/Prod.lean:97`
  `Measure.measurable_measure_prodMk_left [SFinite ν] {s : Set (α × β)}
   (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻¹' s)`
  → これが本 plan のキーレンマ
- `Mathlib/Probability/Distributions/Gaussian/Real.lean:292`
  `gaussianReal_map_const_add (y : ℝ) :
    (gaussianReal μ v).map (y + ·) = gaussianReal (μ + y) v`
  → `μ = 0` で `gaussianReal y v = (gaussianReal 0 v).map (y + ·)` (`zero_add`)
- `Mathlib/Probability/Distributions/Gaussian/Real.lean:209`
  `instIsProbabilityMeasureGaussianReal` → `IsFiniteMeasure (gaussianReal 0 N)` → SFinite

### Phase A — `isAwgnChannelMeasurable` 本体補題 (証明本体、〜200 行)

**目的**: `theorem isAwgnChannelMeasurable (N : ℝ≥0) : IsAwgnChannelMeasurable N` を
publish。中身は

```lean
theorem isAwgnChannelMeasurable (N : ℝ≥0) :
    IsAwgnChannelMeasurable N := by
  -- unfold IsAwgnChannelMeasurable
  unfold IsAwgnChannelMeasurable
  -- 等式 `gaussianReal x N = (gaussianReal 0 N).map (x + ·)`
  have h_eq : ∀ x : ℝ,
      gaussianReal x N = (gaussianReal 0 N).map (x + ·) := by
    intro x
    rw [gaussianReal_map_const_add x]
    congr 1
    ring  -- 0 + x = x
  -- 関数等式 `fun x => gaussianReal x N = fun x => (gaussianReal 0 N).map (x + ·)`
  rw [show (fun x : ℝ => gaussianReal x N)
        = (fun x : ℝ => (gaussianReal 0 N).map (x + ·)) by
        funext x; exact h_eq x]
  -- Giry monad の measurability 判定に分解
  refine Measure.measurable_of_measurable_coe _ ?_
  intro s hs
  -- (gaussianReal 0 N).map (x + ·) s
  --   = (gaussianReal 0 N) ((x + ·)⁻¹' s)
  --   = (gaussianReal 0 N) {y | x + y ∈ s}
  --   = (gaussianReal 0 N) (Prod.mk x ⁻¹' {p | p.1 + p.2 ∈ s})
  have h_meas_add : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ∈ s} :=
    (measurable_fst.add measurable_snd) hs
  -- `Prod.mk x ⁻¹' {p | p.1 + p.2 ∈ s} = (x + ·)⁻¹' s`
  -- → `(gaussianReal 0 N).map (x + ·) s = (gaussianReal 0 N) ((x + ·)⁻¹' s)`
  --                                      = (gaussianReal 0 N) (Prod.mk x ⁻¹' …)
  -- 後者は `Measure.measurable_measure_prodMk_left` で `x` について measurable
  -- `(gaussianReal 0 N)` は IsProbabilityMeasure → IsFiniteMeasure → SFinite
  have h_meas_x : Measurable (x + · : ℝ → ℝ) := measurable_const.add measurable_id
  conv =>
    ext x
    rw [show ((gaussianReal 0 N).map (x + ·)) s
          = (gaussianReal 0 N) (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ∈ s})
          from by
            rw [Measure.map_apply (measurable_const.add measurable_id) hs]
            congr 1
            ext y
            simp]
  exact Measure.measurable_measure_prodMk_left h_meas_add
```

（実装時は微調整 — 特に `conv` ブロックは `funext` + `rw` で展開できる可能性 / Mathlib
の `Measure.map_apply` の名前空間に注意）

**Skeleton-driven Development** に従って以下の順で fill:

1. **Skeleton**: 上記補題を `:= by sorry` 形で `AWGNF1Discharge.lean` 雛形 (imports +
   namespace + 1 補題 + Phase B 補題 2 本も :=by sorry) として `Write`。LSP 診断
   ("only sorry warnings") を確認。
2. **Fill 1**: `h_eq` 補題（`gaussianReal x N = (gaussianReal 0 N).map (x + ·)`）を
   独立に切り出して fill。`rw [gaussianReal_map_const_add]` + `simp` または `ring` で
   `0 + x = x` を畳む。
3. **Fill 2**: `funext` で関数等式に書き換え、`Measure.measurable_of_measurable_coe`
   を起動。
4. **Fill 3**: 内側の `Measurable (fun x ↦ (gaussianReal 0 N).map (x + ·) s)` を
   `Measure.map_apply` で書き換え。`(x + ·) ⁻¹' s = Prod.mk x ⁻¹' {p | p.1 + p.2 ∈ s}`
   は `Set.ext` + `Set.mem_preimage` + `Set.mem_setOf_eq` で示す。
5. **Fill 4**: `Measure.measurable_measure_prodMk_left h_meas_add` で結ぶ。

### Phase B — `awgn_theorem_F1_discharged` + capacity 再 publish (薄い wrapper、〜80 行)

**目的**: 親 plan の主定理 + capacity 系を「`h_meas` 引数なし」形で再 publish。

```lean
theorem awgn_theorem_F1_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_typicality : IsAwgnTypicalityHypothesis P N (isAwgnChannelMeasurable N))
    (h_mi_bridge :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal)
            (awgnChannel N (isAwgnChannelMeasurable N))).toReal
          = Common2026.Shannon.differentialEntropy
              (gaussianReal 0 (P.toNNReal + N))
            - Common2026.Shannon.differentialEntropy (gaussianReal 0 N))
    (h_converse : IsAwgnConverseHypothesis P N (isAwgnChannelMeasurable N))
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt
                  (awgnChannel N (isAwgnChannelMeasurable N)) m).toReal < ε :=
  awgn_channel_coding_theorem P hP N hN (isAwgnChannelMeasurable N)
    h_typicality h_mi_bridge h_converse hR_pos hR_lt_C hε

theorem awgn_capacity_closed_form_F1_discharged
    (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_bridge_gauss : …)
    (h_bdd : …)
    (h_max_ent : …) :
    awgnCapacity P N (isAwgnChannelMeasurable N)
      = (1/2) * Real.log (1 + P / (N : ℝ)) :=
  awgn_capacity_closed_form P hP N hN (isAwgnChannelMeasurable N)
    h_bridge_gauss h_bdd h_max_ent
```

各定理は親 plan の対応する定理に `isAwgnChannelMeasurable N` を渡す **1 行 wrapper**
なので `:= …` 直書きで OK。

### Phase V — verify + 親 plan 反映

- [x] `lake env lean Common2026/Shannon/AWGNF1Discharge.lean` silent ✅
- [x] `wc -l` 148 行 (Phase A 本体 + Phase B + Header 内訳) ✅
- [ ] 親 `awgn-moonshot-plan.md` §撤退ライン F-4 に「discharge 完了 → 本 plan」追記
- [ ] `Common2026.lean` への import 追加は **seed 制約により defer**
  (`Common2026.lean` 不変。downstream で必要になった時点で別 commit)

## 撤退ライン

### G-1: `v = 0` 分岐の measurability 詰まり

`gaussianReal x 0 = Measure.dirac x` で、`measurable_dirac` (`Mathlib/MeasureTheory/Measure/
GiryMonad.lean:110`) で `Measurable (Measure.dirac : ℝ → Measure ℝ)` がある。本 plan の
approach（map-by-const 経由）は `v = 0` の場合も `gaussianReal_map_const_add` が `simp
[hv, gaussianReal_zero_var]` で簡約されて Mathlib 側で吸収されるため、本来は分岐不要。
詰まった場合は `IsAwgnChannelMeasurable` の定義を `(hN : N ≠ 0) → Measurable …` に
restrict し、親 plan の signature を変更（親 plan の `hN : (N : ℝ) ≠ 0` は既存）。

### G-2: `gaussianReal_map_const_add` 経由の等式書き換え詰まり

`gaussianReal x N = (gaussianReal 0 N).map (x + ·)` の証明で `rw
[gaussianReal_map_const_add x]` 後に `0 + x = x` の処理が `simp` で吸収されない場合、
補助補題 `gaussianReal_eq_zero_map (x : ℝ) (N : ℝ≥0) : gaussianReal x N =
(gaussianReal 0 N).map (x + ·)` を独立に publish して `by rw
[gaussianReal_map_const_add, zero_add]` で固める。

### G-3: `m`-measurability 直接構成（重い fallback）

Map 補題が想定外に使えない場合（特に Mathlib 側で signature 変更があった場合）の
fallback は、`gaussianPDFReal m v y` を `(m, y) : ℝ × ℝ` の関数として joint
measurable に持ち上げる構成。

```lean
lemma measurable_gaussianPDFReal_joint (v : ℝ≥0) :
    Measurable (Function.uncurry (fun m y => gaussianPDFReal m v y)) := by
  -- gaussianPDFReal m v y = (√(2πv))⁻¹ * exp(-(y - m)² / (2v))
  -- (m, y) ↦ y - m が jointly measurable → ²/2v measurable → exp measurable → ×const
  unfold gaussianPDFReal
  fun_prop
```

これを `Measurable.lintegral_prod_right` (`Mathlib/MeasureTheory/Measure/Prod.lean:145`)
に通すと `Measurable (fun m => ∫⁻ y in s, gaussianPDF m v y ∂volume)` が出る。
`gaussianReal_apply` で `gaussianReal m v s = ∫⁻ y in s, gaussianPDF m v y` なので、
これを各 `s` について示せば `measurable_of_measurable_coe` で完成。Phase 0 の比較で
**まず G-3 でなく approach を試す**ことを徹底（map 補題の方が ~5x 短い）。

## 危険箇所

### 危険 1: `IsFiniteMeasure ↛ SFinite` の型クラス検索

`Measure.measurable_measure_prodMk_left` は `[SFinite ν]` 必要。`gaussianReal 0 N` は
`IsProbabilityMeasure` だが、`SFinite` インスタンスは Mathlib 側で
`IsProbabilityMeasure → IsFiniteMeasure → SFinite` を自動で拾うはず。詰まったら
`haveI : SFinite (gaussianReal 0 N) := inferInstance` で明示注入。

### 危険 2: `Measure.map_apply` の `Measurable` 引数

`Measure.map_apply (hf : Measurable f) (hs : MeasurableSet s) : (μ.map f) s = μ (f ⁻¹' s)`。
`(x + ·)` の measurability は `measurable_const.add measurable_id` で出す。

### 危険 3: `Prod.mk x ⁻¹' {p | p.1 + p.2 ∈ s}` の Set 等式書換

```lean
-- 示す: Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ∈ s} = (x + ·) ⁻¹' s
-- 証明: ext y; simp [Set.mem_preimage, Set.mem_setOf_eq]
```

これは `Set.ext` + `Set.mem_preimage` 一発で抜けるが、`Prod.mk x y = (x, y)` が `simp`
で展開されることを確認。

### 危険 4: `IsAwgnChannelMeasurable` の unfold タイミング

定義は `def IsAwgnChannelMeasurable (N : ℝ≥0) : Prop := Measurable (fun x : ℝ =>
gaussianReal x N)` で、`unfold` で開く。`@[reducible]` でないので明示 `unfold` 必須。

### 危険 5: `0 + x = x` の rewrite

`gaussianReal_map_const_add x : (gaussianReal μ v).map (y + ·) = gaussianReal (μ + y) v`
を `μ = 0, y = x` で適用すると `(gaussianReal 0 N).map (x + ·) = gaussianReal (0 + x)
N`。これを `gaussianReal x N` に揃えるため `zero_add` か `simp` で `0 + x = x` を畳む。

## 判断ログ

### #1 (2026-05-20): `congr 1` の代わりに `rfl` で済んだ

Phase A 実装中、`Measure.map_apply h_meas_x hs` で
`(gaussianReal 0 N).map (x + ·) s = (gaussianReal 0 N) ((x + ·) ⁻¹' s)` に書き換わった後、
RHS は **definitionally equal** to `(gaussianReal 0 N) (Prod.mk x ⁻¹' {p | p.1 + p.2 ∈ s})`
(`Prod.mk x ⁻¹' {p | p.1 + p.2 ∈ s} = {y | x + y ∈ s} = (x + ·) ⁻¹' s` は `rfl` 等価)。
そのため当初予定の `congr 1; ext y; simp` ではなく `rfl` 一発で抜けた。
`congr 1` を入れると "No goals to be solved" になっていた。

### #2 (2026-05-20): `measurable_measure_prodMk_left` の正しい qualified name

当初 `Measure.measurable_measure_prodMk_left` と書いたが unknown constant。
`Mathlib/MeasureTheory/Measure/Prod.lean` で当該補題は line 97 にあるが、
`namespace MeasureTheory` の **外** (line 165 開始) のため、qualified name は
**root namespace の `measurable_measure_prodMk_left`**。loogle で確定。

## 関連ファイル

- `Common2026/Shannon/AWGN.lean` (`IsAwgnChannelMeasurable` 述語、`awgnChannel` 定義、
  `awgnCapacity` + `awgnCapacity_eq` (F-2 退避形))
- `Common2026/Shannon/AWGNAchievability.lean` (`IsAwgnTypicalityHypothesis` + 親
  achievability)
- `Common2026/Shannon/AWGNConverse.lean` (`IsAwgnConverseHypothesis` + 親 converse)
- `Common2026/Shannon/AWGNMain.lean` (`awgn_channel_coding_theorem` + `awgn_capacity_
  closed_form` — 親主定理 2 本)
- `Mathlib/Probability/Distributions/Gaussian/Real.lean` (`gaussianReal_map_const_add`
  + `instIsProbabilityMeasureGaussianReal`)
- `Mathlib/MeasureTheory/Measure/Prod.lean` (`Measure.measurable_measure_prodMk_left`)
- `Mathlib/MeasureTheory/Measure/GiryMonad.lean` (`Measure.measurable_of_measurable_coe`
  + `Measure.measurable_map`)

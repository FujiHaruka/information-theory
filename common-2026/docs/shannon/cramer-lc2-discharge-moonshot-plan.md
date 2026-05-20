# Cramér L-C2 discharge ムーンショット計画 🌙 (T1-C follow-up)

> 実態整合 (2026-05-20): **本 plan は Phase A まで (L-D3 撤退) で正確 — 進捗ブロック記載どおり**。
> `Common2026/Shannon/CramerLC2Discharge.lean` (0 sorry) に Phase A plumbing 6 補題 publish 済
> (`cgf_eval_eq_cgf_base`:63 / `iIndepFun_tilted_ambient`:85 / `identDistrib_tilted_ambient`:98 等)。
> 本 plan の `cramer_lower_discharged` (Phase C 完全 discharge) は**未 publish のまま**だが、後継チェーンで
> 実質達成: Phase B は `cramer-lc2-ext` (`CramerLC2DischargeExt.lean` tilted LLN)、Phase C change-of-measure は
> `infinitepi-tilted` (`MeasurePiTiltedFactorization` + `InfinitePiTiltedChangeOfMeasure`)、最終 unconditional 化は
> `cramer-chernoff-clt-closure` (`CramerCLTClosure.cramer_lower_at_cgfDeriv_unconditional`) で完了済。

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は ~~取り消し線~~ で残す（完全削除しない、過去参照のため）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
-->

> **Parent**: [`cramer-moonshot-plan.md`](cramer-moonshot-plan.md) §Phase C (L-C2 撤退記録) + §撤退ライン L-C2
>
> **Predecessor (inventory)**: [`cramer-mathlib-inventory.md`](cramer-mathlib-inventory.md) §K LLN + §危険 4 (tilted 下 n-IID 再構築)
>
> **Status (2026-05-19)**: 着手前。親 Cramér plan は **L-C2 退避形** (`cramer_lower` の `h_tilted_lower` を hypothesis 引数として publish) で 0 sorry 完了済 (`Common2026/Shannon/Cramer.lean` 637 行)。本 plan はその `h_tilted_lower` を **Mathlib 標準 LLN + tilted IID plumbing** で完全証明し、`cramer_lower` / `cramer_lower_legendre` / `cramer_tendsto` を **hypothesis なし形** で再 publish するための後継 plan。
>
> **Goal**: `Common2026/Shannon/Cramer.lean`（または分離ファイル）で
>
> ```lean
> theorem cramer_lower_discharged [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
>     (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
>     (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
>     (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
>     (a : ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
>     (h_deriv : deriv (cgf (X 0) μ) lam = a)
>     (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop …) :
>     -(lam * a - cgf (X 0) μ lam)
>       ≤ liminf (fun n : ℕ =>
>           (1 / (n : ℝ)) * Real.log
>             (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop
> ```
>
> を publish。すなわち親 plan の `cramer_lower` から `h_tilted_lower` を **削除**し、その代わり「`lam` が `Λ'(lam) = a` を満たす」だけを要求する形に置換える。`cramer_lower_legendre` / `cramer_tendsto` も対応して hypothesis 引数を縮小し再 publish。
>
> **撤退ライン**: [L-D1] tilted LLN を弱形 (`tendstoInProbability`, Chebyshev 経由) で済ませて `h_deriv` のみ要求形で publish / [L-D2] tilted IID 再構築を `Measure.pi (fun _ : Fin n => μ)` 有限 IID 形で代替 / [L-D3] Phase A (tilted IID plumbing) のみ publish して discharge は後継 plan へ (詳細 §撤退ライン)。

## 進捗

- [x] Phase 0 — Mathlib LLN + tilted IID API 在庫再確認 ✅ (`strong_law_ae_real`, `iIndepFun_infinitePi`, `infinitePi_map_eval`, `mgf_map`, `tendstoInMeasure_of_tendsto_ae` 等を `Mathlib/Probability/StrongLaw.lean:598`, `Mathlib/Probability/Independence/InfinitePi.lean:103`, `Mathlib/Probability/ProductMeasure.lean:478`, `Mathlib/Probability/Moments/Basic.lean:214`, `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:223` で確認)
- [x] Phase A — tilted measure 下 n-IID 構成 + IdentDistrib 継承 ✅ (`Common2026/Shannon/CramerLC2Discharge.lean` 171 行 publish)
- [ ] Phase B — Mathlib LLN を tilted ambient で起動 🔄 **L-D3 撤退** (型クラス検索詰まりで defer、§判断ログ #1)
- [ ] Phase C — `cramer_lower` 再 publish (hypothesis なし形) + downstream wrapper 更新 🔄 **L-D3 撤退** (Phase B 撤退に伴い defer、§判断ログ #1)
- [x] Phase V — verify + 親 plan L-C2 退避記録の discharge 完了反映 ✅ (Phase A までを publish、Phase B-C は後続 plan へ defer)

## ゴール / Approach

### Goal (最終定理 signature)

親 plan の `cramer_lower` (`Common2026/Shannon/Cramer.lean:448`) は現状

```lean
theorem cramer_lower [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (_h_indep …) (_h_meas …) (_h_ident …) (_h_bdd …)
    (a : ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop …)
    (h_tilted_lower : ∀ ε > 0,                                       -- ← これを消す
      ∃ C > 0, ∀ᶠ n : ℕ in atTop,
        C * Real.exp (-(n : ℝ) * (lam * a - cgf (X 0) μ lam + lam * ε))
          ≤ μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}) :
    -(lam * a - cgf (X 0) μ lam) ≤ liminf … atTop
```

`h_tilted_lower` を「tilted-下 Chernoff lower bound」と呼ぶ。これは「tilted ambient で `(infinitePi μ).tilted (∑ lam · X i)` の下で `S_n / n → a`（in-probability LLN）が成立する」ことが本質的に必要十分。本 plan の最終定理は

```lean
theorem cramer_lower_discharged …
    (h_deriv : deriv (cgf (X 0) μ) lam = a) :   -- ← これだけを要求
    -(lam * a - cgf (X 0) μ lam) ≤ liminf … atTop
```

で、`h_deriv` は Legendre 最適性条件（既に `cramer_lower_legendre` の `hlam_opt` から取れる近い情報）と一致。`h_tilted_lower` は本 plan 内部で **Mathlib `strong_law_ae_real` + tilted IID plumbing** から構成され、外部から見える形では消える。

### Approach (overall strategy / shape of solution)

**戦略の shape**: 親 plan の `h_tilted_lower` を「tilted ambient 下の n-IID 確率測度 + Mathlib 強収束 LLN + Chernoff 流の change-of-measure（既に `klDiv_tilted_eq` で書けている）」の 3 段に分解して埋める。

```
┌──────────────────────────────────────────────────────────────┐
│ Phase A: tilted ambient と n-IID の繋ぎを作る                  │
│  ・ Mathlib 不在の `(infinitePi μ).tilted (∑ lam · X i)` を    │
│    `infinitePi (fun _ => μ.tilted (lam * X 0 ·))` と等号で結ぶ │
│    （AC + RN 微分が乗積形 ⇒ 帰納的に乗積測度に分解）           │
│  ・ tilted single μ 上で X 0 が `IdentDistrib`（mgf 経由）     │
│  ・ tilted ambient 上で `(eval i) ~ tilted single` が          │
│    `IdentDistrib` + `iIndepFun_infinitePi`                     │
└──────────────────────────────────────────────────────────────┘
                              ↓
┌──────────────────────────────────────────────────────────────┐
│ Phase B: Mathlib `strong_law_ae_real` を tilted ambient で起動 │
│  ・ Phase A で IID 性を確保した family `Yi := X i (∘ eval)`に  │
│    `strong_law_ae_real Y …` で a.s. `S_n / n → 𝔼_{tilted}[X 0]`│
│  ・ `integral_tilted_mul_self` (Mathlib `Tilted.lean:132`,     │
│    bounded RV ⇒ `interior = univ` 自明化済) で                 │
│    `𝔼_{tilted}[X 0] = deriv (cgf (X 0) μ) lam = a`             │
│  ・ a.s. → in-probability で `μ_tilted^∞({|S̄_n - a| < ε}) → 1` │
└──────────────────────────────────────────────────────────────┘
                              ↓
┌──────────────────────────────────────────────────────────────┐
│ Phase C: `h_tilted_lower` を Phase B の出力から構成し          │
│  `cramer_lower` を hypothesis 引数なしで再 publish              │
│  ・ Cramér change-of-measure (RN deriv from tilted) で        │
│    μ-side の {n·a ≤ S_n} に下界 `(1 - δ) · exp(-n · …)` を貼る │
│  ・ Phase B の `μ_tilted^∞({|S̄_n - a| < ε}) → 1` を使えば      │
│    `1 - δ ≥ 1/2` 等の eventually 形で `C := 1/2` などが取れる  │
│  ・ 親 plan の `cramer_lower_legendre` / `cramer_tendsto` の   │
│    `h_tilted_lower` 引数を全削除（または internal lemma に    │
│    隠蔽）し、`hlam_opt` (Legendre 最適性) のみ要求する形に    │
└──────────────────────────────────────────────────────────────┘
```

**核心**: Mathlib `strong_law_ae_real` (`StrongLaw.lean:598`) は **`Pairwise ((· ⟂ᵢ[μ] ·) on X)`**（pairwise independent）+ `Integrable (X 0) μ` + `∀ i, IdentDistrib (X i) (X 0) μ μ` のみを要求し、Etemadi 形のため `iIndepFun` の格上げ不要。tilted ambient で **`Pairwise IndepFun`** さえ取れれば `S_n / n → 𝔼[X 0]` が a.s. で出る。これを in-probability に弱めた形が `h_tilted_lower` 構成に必要十分。

**Mathlib-shape-driven**: 親 plan の `h_tilted_lower` は **change-of-measure 後の μ-side の下界**形（「`C · exp(-n·…) ≤ μ.real {...}`」）になっている。これは Mathlib 標準 LLN の出力（「a.s. `S_n / n → a`」）と直接結びつかない。Phase B-C の境界（in-probability 形から μ-side 下界への変換）で **Cramér 流の change-of-measure 一段**を挿むのが本 plan の山場。具体的には:

```
strong_law_ae_real      μ-side
   (tilted ambient)        ↓ change-of-measure (RN deriv = exp(lam·S_n - n·Λ(lam)))
   S_n / n → a (a.s.)  ─→  μ.real {n·a ≤ S_n} ≥ exp(-n·(lam·a - Λ(lam) + lam·ε)) · μ_tilted({|S̄_n - a| ≤ ε})
                                                                                      └──── Phase B 出力で `→ 1` ─┘
```

最終的に `cramer_lower_discharged` の証明は親 plan 既存 `cramer_lower` を呼ぶだけ（`h_tilted_lower` を本 plan 内部で構成して渡す）。

### 規模見積もり (中央予測)

| 自作要素 | 想定行数 | Phase |
|---|---|---|
| Phase 0 在庫差分（tilted ↔ infinitePi の補題探索 + Pairwise.indepFun 構築方針） | ~0 行 (調査のみ、別 inventory) | 0 |
| `tilted_infinitePi_eq` (tilted ambient 分解、AC + RN 微分の乗積形) | ~60-100 行 | A |
| `pairwise_indepFun_tilted_ambient` (Pairwise indep on tilted ambient) | ~30-50 行 | A |
| `identDistrib_tilted_eval` (各 `eval i` が tilted single と同分布) | ~30-50 行 | A |
| `tilted_lln_in_probability` (a.s. LLN から in-probability LLN 取り出し) | ~40-60 行 | B |
| `tilted_mean_eq_deriv_cgf` (既存 `integral_tilted_eq_deriv_cgf` から引いて起動) | ~15-25 行 | B |
| `h_tilted_lower_from_lln` (Cramér change-of-measure 一段、RN deriv 経由) | ~80-120 行 | C |
| `cramer_lower_discharged` / `cramer_lower_legendre_discharged` / `cramer_tendsto_discharged` (wrapper, hypothesis 引数削除版) | ~30-50 行 | C |
| skeleton + imports + docstring | ~20-30 行 | A |
| **合計** | **~300-500 行** | |

**中央予測 ~400 行**（親 plan §規模見積もり「~400 行」と同オーダー）。Phase A だけで止まれば ~200 行（L-D3 撤退で publish 価値あり、tilted IID plumbing は単独 publish に値する infrastructure）。

### ファイル構成 (Phase C 完了時の判断分岐)

#### option (i) — `Common2026/Shannon/Cramer.lean` 末尾追記

- 既存 637 行に + ~300-500 行で合計 ~950-1100 行
- 利点: `cramer_lower` から `cramer_lower_discharged` への internal callsite が同ファイル内、`private` helper を共有可能
- 欠点: 1 ファイルがやや長大、編集時の olean rebuild が重い

#### option (ii, **推奨**) — `Common2026/Shannon/CramerLC2Discharge.lean` 新規

```
Common2026/Shannon/
  Cramer.lean                 ← 既存、変更最小（`cramer_lower_discharged` 等を
                                  別ファイルで定義し、re-export なしの素朴 publish）
  CramerLC2Discharge.lean     ← 新規 (~300-500 行)
Common2026.lean               ← `import Common2026.Shannon.CramerLC2Discharge` 追記
```

- 利点: 既存 Cramer.lean の olean を不変に保てる、L-C2 discharge を独立 module として概念的にも分離（後続 plan が import しやすい）
- 欠点: tilted ambient plumbing helper を `Cramer.lean` から `CramerLC2Discharge.lean` に移植する場合 cross-file refactor が必要（最小限に留める）

**判断**: 着手時 Phase A-1 で確定。default は option (ii)、`Cramer.lean` の既存 helper (`klDiv_tilted_eq` / `mem_interior_integrableExpSet_of_bounded` / `isProbabilityMeasure_tilted_of_bounded` / `integral_tilted_eq_deriv_cgf`) を **import して** 再利用する形を取る（再定義しない）。

### 規模 / risk vs L-C2 退避時の追加コスト

| metric | 親 plan L-C2 退避形 (現状) | 本 plan discharge 完了形 |
|---|---|---|
| `Cramer.lean` 行数 | 637 | 637 (unchanged) |
| 新規 module 行数 | — | ~300-500 |
| `cramer_lower` の signature 引数 | `h_tilted_lower` 含む 8 引数 | `h_deriv` のみ追加 (1 引数増) して `h_tilted_lower` 削除 = 実質 -1 引数 |
| Mathlib 直接依存 | `Probability.Moments.*` + `MeasureTheory.Measure.Tilted` | + `Probability.StrongLaw` + `Probability.Independence.InfinitePi` + `Probability.ProductMeasure` |
| 0 sorry 維持 | ✅ | 目標 ✅ |

---

## 依存関係

完了済 / 利用可:

- [x] **Mathlib `Probability.StrongLaw`**: `strong_law_ae_real` (`StrongLaw.lean:598`)、`strong_law_ae` (`StrongLaw.lean:788`)
- [x] **Mathlib `Probability.Independence.InfinitePi`**: `iIndepFun_infinitePi` (`InfinitePi.lean:103`)
- [x] **Mathlib `Probability.ProductMeasure`**: `Measure.infinitePi`, `Measure.infinitePi_map_eval`
- [x] **Mathlib `Probability.IdentDistrib`**: `IdentDistrib`, `IdentDistrib.integrable_iff`
- [x] **Mathlib `Probability.Moments.Tilted`**: `tilted_mul_apply_cgf`, `integral_tilted_mul_self`, `variance_tilted_mul`
- [x] **Mathlib `MeasureTheory.Measure.Tilted`**: `Measure.tilted`, `isProbabilityMeasure_tilted`, `tilted_absolutelyContinuous`, `absolutelyContinuous_tilted`, `rnDeriv_tilted_left_self`, `log_rnDeriv_tilted_left_self`
- [x] **`Common2026/Shannon/Cramer.lean`** 既存補題（本 plan で **import + re-use**、再定義しない）:
  - `legendre`, `cramerRate`, `legendre_apply_le`, `legendre_nonneg`, `cramerRate_apply_le`, `cramerRate_nonneg`
  - `integrable_exp_mul_of_bounded` (Phase A-1 / B-1 で tilted ambient 構築時に必須)
  - `cgf_sum_eq_nsmul`
  - `mem_interior_integrableExpSet_of_bounded` (bounded RV ⇒ `interior = univ` 自明化、Phase B-2 で `integral_tilted_mul_self` 起動時に必須)
  - `isProbabilityMeasure_tilted_of_bounded` (Phase A で tilted single の確率測度性を取る)
  - `integral_tilted_eq_deriv_cgf` (Phase B-2 で `𝔼_{tilted}[X 0] = Λ'(lam)` を取る)
  - `klDiv_tilted_eq` (Phase C で change-of-measure の指数 factor 確認に使うかもしれない、必須ではない)
  - `chernoff_bound_n_iid` / `cramer_log_bound_n_iid` (upper bound 側、本 plan の lower bound と直接交わらないが parallel 構造の参考)
  - `cramer_lower` / `cramer_lower_legendre` / `cramer_tendsto` (本 plan の discharge 後継 wrapper で **これらを呼ぶ** 形 = 「`h_tilted_lower` を本 plan 内部で構成して既存 `cramer_lower` に渡す」)

**参考 (import しない)**:

- `Common2026/Shannon/SanovLDPEquality.lean` (親 plan 判断ログ #1 で Sanov 経由を不採用、本 plan も継承)
- `Common2026/Shannon/IIDProductInput.lean` (より軽い `Measure.infinitePi (fun _ : ℕ => μ)` を直接使う、親 plan 判断ログ #4 と整合)

---

## Phase 0 — Mathlib LLN + tilted IID API 在庫再確認 📋

### スコープ

親 plan 着手時の `cramer-mathlib-inventory.md` §K（LLN）と §F（Tilted）は 6 ヶ月前のスナップショット。L-C2 discharge に必要な **新規軸 3 つ**を改めて inventory：

1. **tilted ↔ infinitePi の直接補題探索**: Mathlib 最新で `MeasureTheory.Measure.infinitePi (fun _ => μ.tilted f) = (Measure.infinitePi μ).tilted (∑ f ∘ eval i)` 風の compatibility lemma が追加されていないか確認（`rg "pi.*tilted|tilted.*pi"` で予備調査済 → **不在**確認、Phase 0 で再 verify）
2. **`Pairwise ((· ⟂ᵢ[μ] ·) on X)` 構築の API**: `iIndepFun → Pairwise IndepFun` の格下げ lemma、または `iIndepFun_infinitePi` の結果をそのまま `Pairwise` に格下げできる短い path（`iIndepFun.pairwise_indepFun` 風）が Mathlib にあるか
3. **bounded RV の Integrable plumbing on tilted ambient**: `Integrable ((fun ω => Real.exp (lam * X 0 ω)) ∘ eval i) (Measure.infinitePi (fun _ => μ.tilted ...))` のような複合 integrability が Mathlib で自動 dispatch されるか、自前で 30 行書くか

### 成果物

- `docs/shannon/cramer-lc2-discharge-mathlib-inventory.md` — 上記 3 軸の調査結果 + Phase A 着手時の不確実性ランク（CLAUDE.md "Subagent Inventory of Mathlib Lemmas" 規約に従い、`file:line` + 完全 signature verbatim + 型クラス前提 `[...]` 全角括弧引用）
- 本計画書への反映（Approach / Phase A 節）

### Done 条件

- 「Mathlib に tilted-infinitePi 直接 compatibility は無い」を loogle + rg ダブル裏取り済み（既に予備調査済、Phase 0 で正式 record）
- `strong_law_ae_real` の **正確な前提リスト**（`Pairwise IndepFun`, `IdentDistrib`, `Integrable (X 0) μ`, **`IsProbabilityMeasure μ` は内部で auto-derive される** ことの確認）を verbatim signature 記録
- Phase A skeleton（後述）が書ける状態

### 工数感

0.5 セッション（1-1.5h）。subagent 1 本 + ローカル `loogle` / `rg`。**proof-log**: no（調査のみ）

### 失敗時 fallback

- Phase 0 で「Mathlib に tilted-infinitePi 直接 compatibility が **新規追加されていた**」と判明した場合 → 本 plan の Phase A は大幅縮退、`Measure.tilted` の n-letter 化 plumbing を Mathlib 直呼びで済ませる。規模見積もり ~200 行に圧縮、Phase A 終了で publish 達成。

---

## Phase A — tilted measure 下 n-IID 構成 + IdentDistrib 継承 📋

### スコープ

tilted single `μ_lam := μ.tilted (lam * X 0 ·)`（既に `isProbabilityMeasure_tilted_of_bounded` で確率測度性確立済）の **infinitePi 乗積測度** `μ_lam^∞ := Measure.infinitePi (fun _ : ℕ => μ_lam)` を構築し、その上で:

- 各 `eval i : (ℕ → Ω) → Ω` を経由した RV `Y i := X 0 ∘ eval i` が `Pairwise IndepFun` + `∀ i, IdentDistrib (Y i) (Y 0) μ_lam^∞ μ_lam^∞`
- `μ_lam^∞[Y 0] = μ_lam[X 0] = deriv (cgf (X 0) μ) lam`

までを確立。これは Mathlib `strong_law_ae_real` の **3 前提** + 結論計算の前提 を tilted ambient で揃える作業。

**proof-log**: yes (Phase A 完了で `proof-log-cramer-lc2-discharge-phaseA.md` を append)。

### Done 条件

- `Common2026/Shannon/CramerLC2Discharge.lean` 新規作成（または `Cramer.lean` 末尾追記、Phase A-1 で確定）+ skeleton 全 `sorry` で type-check
- `tilted_ambient` (`μ_lam^∞`) の `IsProbabilityMeasure` instance 自動 dispatch 確認
- `pairwise_indepFun_tilted_ambient` ( `Pairwise ((· ⟂ᵢ[μ_lam^∞] ·) on Y)`)
- `identDistrib_tilted_ambient` (`∀ i, IdentDistrib (Y i) (Y 0) μ_lam^∞ μ_lam^∞`)
- `integrable_tilted_ambient` (`Integrable (Y 0) μ_lam^∞`)（bounded RV ⇒ 自動）
- `lake env lean Common2026/Shannon/CramerLC2Discharge.lean` で Phase A 本体 + Phase B-C `sorry` skeleton が clean

### ステップ

- [ ] **A-0 ファイル配置判断 + skeleton**: option (i)（Cramer.lean 末尾）か option (ii)（CramerLC2Discharge.lean 新規）かを確定。default option (ii)。全主定理 + 補助補題を `:= by sorry` で並べた skeleton を Write、LSP 診断で type-check OK 確認（CLAUDE.md "Skeleton-driven Development"）。imports は §依存関係 の Mathlib リスト + `import Common2026.Shannon.Cramer`。

- [ ] **A-1 tilted single の確率測度性 + 平均 (既存補題で済む)**:
  ```lean
  have h_tilted_prob : IsProbabilityMeasure (μ.tilted (lam * X 0 ·)) :=
    isProbabilityMeasure_tilted_of_bounded h_meas_0 h_bdd_0 lam
  have h_tilted_mean : (μ.tilted (lam * X 0 ·))[X 0] = deriv (cgf (X 0) μ) lam :=
    integral_tilted_eq_deriv_cgf h_meas_0 h_bdd_0 lam
  ```
  既存 `Cramer.lean` の `isProbabilityMeasure_tilted_of_bounded` / `integral_tilted_eq_deriv_cgf` を import して 0 行で完了。

- [ ] **A-2 tilted ambient `μ_lam^∞` 構築**:
  ```lean
  noncomputable def tiltedAmbient (μ : Measure Ω) (X : Ω → ℝ) (lam : ℝ) :
      Measure (ℕ → Ω) :=
    Measure.infinitePi (fun _ : ℕ => μ.tilted (lam * X ·))
  ```
  `IsProbabilityMeasure (tiltedAmbient μ (X 0) lam)` instance は `Measure.infinitePi` の標準 instance + A-1 から自動 dispatch（Mathlib `Probability.ProductMeasure` で `[∀ i, IsProbabilityMeasure (P i)] → IsProbabilityMeasure (Measure.infinitePi P)`）。
  - ~10-20 行

- [ ] **A-3 `iIndepFun_infinitePi` 起動 → `Pairwise IndepFun` 格下げ**:
  ```lean
  -- Mathlib `iIndepFun_infinitePi` (InfinitePi.lean:103):
  --   iIndepFun (fun i ω ↦ X i (ω i)) (Measure.infinitePi P)
  -- ここで `P i := μ.tilted (lam * X 0 ·)` 一定（i 非依存）、
  -- `X i := id` で `Y i ω := X 0 (ω i)` を直接構成。
  have h_iIndep : iIndepFun (fun i ω => X 0 (ω i)) (tiltedAmbient μ (X 0) lam) :=
    iIndepFun_infinitePi (mX := fun _ => h_meas_0)
  -- `iIndepFun → Pairwise IndepFun`:
  have h_pairwise : Pairwise ((· ⟂ᵢ[tiltedAmbient μ (X 0) lam] ·) on
      (fun i ω => X 0 (ω i))) :=
    h_iIndep.pairwise   -- Mathlib `iIndepFun.pairwise` 候補、Phase 0 で正式名確認
  ```
  - `iIndepFun_infinitePi` の前提は `[∀ i, IsProbabilityMeasure (P i)]` + `∀ i, Measurable (X i)`。A-2 + h_meas_0 で揃う。
  - `iIndepFun.pairwise` (`iIndepFun → Pairwise IndepFun`) は Mathlib `Probability.Independence.Basic` あたりにある想定（Phase 0 で正式名確認）。無ければ自前 5-10 行（任意の `i ≠ j` で `iIndepFun.indepFun` を呼ぶ）
  - ~20-30 行

- [ ] **A-4 `IdentDistrib` for tilted ambient evaluations**:
  ```lean
  have h_ident_tilted : ∀ i,
      IdentDistrib (fun ω : ℕ → Ω => X 0 (ω i))
                   (fun ω : ℕ → Ω => X 0 (ω 0))
                   (tiltedAmbient μ (X 0) lam) (tiltedAmbient μ (X 0) lam) := by
    intro i
    -- `Measure.infinitePi_map_eval` で `(tiltedAmbient ...).map (eval i) = μ.tilted ...`
    -- 両方の側で push-forward が同じ ⇒ IdentDistrib 自動
    …
  ```
  - Mathlib `Measure.infinitePi_map_eval` で各座標の周辺が一定 `μ.tilted ...` ⇒ `IdentDistrib.of_map_eq` または直接 `IdentDistrib` 定義の `Measure.map` 一致から導出
  - ~20-30 行

- [ ] **A-5 tilted-ambient 上の bounded + integrable**:
  ```lean
  have h_int_tilted : Integrable (fun ω : ℕ → Ω => X 0 (ω 0))
                                 (tiltedAmbient μ (X 0) lam) := by
    -- bounded RV ⇒ `|X 0 (ω 0)| ≤ M` for all ω
    -- `IsProbabilityMeasure` + bounded ⇒ integrable
    …
  ```
  - bounded ⇒ `(integrable_const M).mono'` で integrable、Mathlib 標準 5-10 行
  - ~10-15 行

- [ ] **A-6 verify**: `lake env lean Common2026/Shannon/CramerLC2Discharge.lean` で Phase A 本体が 0 sorry、Phase B-C は `sorry` 残し。

### 工数感

~150-250 行 (skeleton ~30 + A-2 ~15 + A-3 ~25 + A-4 ~25 + A-5 ~15 + plumbing/imports ~30)。0.75-1 セッション。proof-log `yes`。

### 失敗時 fallback

- **A-3 `iIndepFun.pairwise` が Mathlib に名前変更で見つからない**: 自前 5-10 行で `Pairwise ((· ⟂ᵢ[μ] ·) on Y)` を `iIndepFun.indepFun` (任意 2 引数版) から組み立てる。
- **A-4 `IdentDistrib.of_map_eq` が Mathlib に無い**: `IdentDistrib` 定義（`Measurable f₁ ∧ Measurable f₂ ∧ Measure.map f₁ μ₁ = Measure.map f₂ μ₂`）から直接展開、`Measure.infinitePi_map_eval` で push-forward 一致を直書き。+10-20 行。
- **A-2 で `Measure.infinitePi` の `IsProbabilityMeasure` instance が dispatch しない**: `instance : IsProbabilityMeasure (Measure.infinitePi P)` を明示 `haveI` で名前付き hint。dispatch 失敗が深ければ Mathlib 側 instance attribute を要確認。

---

## Phase B — Mathlib LLN を tilted ambient で起動 📋

### スコープ

Phase A で揃えた 3 前提（`Pairwise IndepFun`, `IdentDistrib`, `Integrable`）を `strong_law_ae_real` に渡し、tilted ambient 上で a.s. LLN `S_n / n → 𝔼_{tilted}[X 0] = a` を取り、in-probability 形 `μ_lam^∞({|S̄_n - a| < ε}) → 1` に弱める。

**proof-log**: yes (Phase B 完了で `proof-log-cramer-lc2-discharge-phaseB.md` を append)。

### Done 条件

- `tilted_lln_almost_sure` (`∀ᵐ ω ∂tiltedAmbient, Tendsto (S_n / n) atTop (𝓝 a)`)
- `tilted_lln_in_probability` (`∀ ε > 0, Tendsto (fun n => tiltedAmbient({|S̄_n - a| < ε})) atTop (𝓝 1)`)
- `tilted_mean_eq_a` (`(μ.tilted (lam * X 0 ·))[X 0] = a`、`h_deriv` 仮定下、A-1 + h_deriv で 1 行)

### ステップ

- [ ] **B-1 `strong_law_ae_real` 起動**:
  ```lean
  have h_lln_ae :
      ∀ᵐ ω ∂tiltedAmbient μ (X 0) lam,
        Tendsto (fun n => (∑ i ∈ Finset.range n, X 0 (ω i)) / n) atTop
          (𝓝 ((μ.tilted (lam * X 0 ·))[X 0])) := by
    exact strong_law_ae_real (fun i ω => X 0 (ω i)) h_int_tilted h_pairwise h_ident_tilted
  ```
  - `strong_law_ae_real` (`Mathlib/Probability/StrongLaw.lean:598`) の前提 `Pairwise`, `IdentDistrib`, `Integrable (X 0)` を Phase A の出力で起動
  - 結論は `∀ᵐ ω, Tendsto ((∑ X i ω) / n) atTop (𝓝 μ[X 0])` — μ-side の積分 `μ[X 0]` は `(tilted ambient)[Y 0]` で、`Y 0 ω := X 0 (ω 0)`、その積分は `Measure.infinitePi` の標準性 + A-1 から `μ.tilted ...[X 0] = deriv (cgf X μ) lam`
  - ~20-30 行

- [ ] **B-2 `tilted_mean = a`**:
  ```lean
  have h_mean_eq_a : (μ.tilted (lam * X 0 ·))[X 0] = a := by
    rw [integral_tilted_eq_deriv_cgf h_meas_0 h_bdd_0 lam, h_deriv]
  ```
  - 既存 `Cramer.lean:integral_tilted_eq_deriv_cgf` で `𝔼_{tilted}[X 0] = Λ'(lam)`、`h_deriv : Λ'(lam) = a` で書き換え
  - ~2-5 行

- [ ] **B-3 a.s. → in-probability 形変換**:
  ```lean
  have h_lln_in_prob : ∀ ε > 0,
      Tendsto (fun n : ℕ =>
          (tiltedAmbient μ (X 0) lam).real
            {ω | |(∑ i ∈ Finset.range n, X 0 (ω i)) / n - a| < ε})
        atTop (𝓝 1) := by
    intro ε hε
    -- a.s. convergence → in-probability convergence
    -- Mathlib `MeasureTheory.tendstoInMeasure_of_tendsto_ae` or similar
    …
  ```
  - Mathlib `tendstoInMeasure_of_tendsto_ae` (`MeasureTheory.Function.ConvergenceInMeasure` 周辺) で a.s. → in-measure（≃ in-probability for prob measure）
  - alternatively, dominated convergence + bounded indicator で直接 `tilted({|S̄_n - a| ≥ ε}) → 0`
  - ~30-50 行

- [ ] **B-4 verify**: `lake env lean Common2026/Shannon/CramerLC2Discharge.lean` で Phase B 本体が 0 sorry、Phase C は `sorry` 残し。

### 工数感

~80-130 行 (B-1 ~30 + B-2 ~5 + B-3 ~40 + plumbing ~20)。0.5-0.75 セッション。proof-log `yes`。

### 失敗時 fallback

- **B-3 a.s. → in-probability の Mathlib lemma 名が変わっている**: 自前 ~20 行で書く（`ε`-neighborhood の indicator `1_{|S̄_n - a| < ε}` に dominated convergence、bounded ⇒ `IsFiniteMeasure` ⇒ DCT 自動 dispatch）
- **B-1 `strong_law_ae_real` の signature が `Integrable (X 0)` でなく `MemLp 1`**: 結論は同等、bridge ~5 行

---

## Phase C — `cramer_lower` 再 publish (hypothesis なし形) + downstream wrapper 更新 📋

### スコープ

Phase B の出力 `tilted_lln_in_probability` を Cramér change-of-measure で μ-side に戻し、`h_tilted_lower` を **構成**する。これを既存 `cramer_lower` に渡し、`cramer_lower_discharged` / `cramer_lower_legendre_discharged` / `cramer_tendsto_discharged` の 3 つを **`h_tilted_lower` 引数なしで** publish。

**proof-log**: yes (Phase C 完了で `proof-log-cramer-lc2-discharge-phaseC.md` を append)。

### Done 条件

- `h_tilted_lower_from_lln` 内部補題が `tilted_lln_in_probability` から `h_tilted_lower` を構成
- `cramer_lower_discharged` 主定理 (signature §Goal 参照、`h_deriv : Λ'(lam) = a` のみ仮定形)
- `cramer_lower_legendre_discharged` (Legendre 形 wrapper)
- `cramer_tendsto_discharged` (`Tendsto` 形 main、`h_deriv` のみ追加引数、`h_tilted_lower` 削除)
- 親 plan `Cramer.lean:cramer_lower` / `cramer_lower_legendre` / `cramer_tendsto` の **既存 signature は変更しない**（後方互換、Phase C は新規 wrapper として publish）

### ステップ

- [ ] **C-1 change-of-measure の n-letter 化**: Cramér lower bound の核心、`(infinitePi μ).tilted (∑ lam · X i)` のRN deriv 形に乗らず、**代わりに `tiltedAmbient μ (X 0) lam = infinitePi (fun _ => μ.tilted ...)` の側で議論**（Phase A で構築済）。具体的には:

  ```lean
  -- μ-side {n·a ≤ S_n} の下界を tiltedAmbient 経由で書く。
  -- Mathlib `Measure.infinitePi (fun _ => μ.tilted ...)` と
  -- `(Measure.infinitePi (fun _ => μ)).tilted ?` の AC 関係を
  -- 各座標の RN deriv 乗積で組み立てる。
  --
  -- 具体: 任意の measurable set S ⊆ ℕ → Ω に対し
  --   (Measure.infinitePi (fun _ => μ)).real S
  --   ≥ ∫_S exp(-∑_{i ∈ range n} (lam · X 0 (ω i) - Λ(lam))) ∂(tiltedAmbient ...)
  --   ＝ exp(n · Λ(lam)) · ∫_S exp(-lam · ∑ X 0 (ω i)) ∂(tiltedAmbient ...)
  --
  -- S を `{ω | n·a ≤ ∑ X i ω}` の cylinder 形に取り、ε-neighborhood
  -- `{ω | |S̄_n - a| < ε}` ⊆ {ω | n·(a-ε) ≤ ∑ X i ω} ⊆ … で挟む
  ```
  - ~50-80 行（最大の山場、判断 candidate あり）
  - **代替** (L-D2 fallback): `Measure.infinitePi` を `Measure.pi (fun _ : Fin n => μ)` 有限 IID に置換し、各 `n` で独立に RN deriv 構築、asymptotic 結果は不変

- [ ] **C-2 `h_tilted_lower_from_lln` 構成**:
  ```lean
  lemma h_tilted_lower_from_lln
      [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
      (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
      (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
      (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
      (a : ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
      (h_deriv : deriv (cgf (X 0) μ) lam = a) :
      ∀ ε > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
        C * Real.exp (-(n : ℝ) * (lam * a - cgf (X 0) μ lam + lam * ε))
          ≤ μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω} := by
    intro ε hε
    -- Phase B `tilted_lln_in_probability` で
    --   tiltedAmbient ({ω | |S̄_n - a| < ε/2}) → 1
    -- だから ∀ᶠ n, tiltedAmbient ({…}) ≥ 1/2
    -- C-1 の change-of-measure で μ-side に戻して
    --   μ.real {n·a ≤ S_n} ≥ exp(n · Λ(lam) - n · lam · (a + ε/2)) · (1/2)
    --                       = (1/2) · exp(-n · (lam · a - Λ(lam) + lam · ε/2))
    -- ε/2 ≤ ε で結論
    refine ⟨1/2, by norm_num, ?_⟩
    …
  ```
  - C-1 + Phase B で組み立て
  - **判断 candidate**: `μ` の n-fold product を本 plan の `Ω` の上に直接構築するか、`X : ℕ → Ω → ℝ` の `Ω` を `ℕ → Ω₀` 形に取り換えるか。後者は親 plan の `X : ℕ → Ω → ℝ` signature と齟齬を生む可能性、Phase C 着手時に判断
  - ~40-60 行

- [ ] **C-3 `cramer_lower_discharged` publish**:
  ```lean
  theorem cramer_lower_discharged
      [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
      (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
      (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
      (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
      (a : ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
      (h_deriv : deriv (cgf (X 0) μ) lam = a)
      (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
        (fun n : ℕ => (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}))) :
      -(lam * a - cgf (X 0) μ lam) ≤ liminf … atTop := by
    have h_tilted_lower :=
      h_tilted_lower_from_lln h_indep h_meas h_ident h_bdd a lam hlam h_deriv
    exact cramer_lower h_indep h_meas h_ident h_bdd a lam hlam h_coboundedBelow
      h_tilted_lower
  ```
  - 親 plan 既存 `cramer_lower` を内部で呼ぶだけ、外側 signature は `h_deriv` のみ追加（`h_tilted_lower` 削除）
  - ~10-15 行

- [ ] **C-4 `cramer_lower_legendre_discharged` + `cramer_tendsto_discharged` wrapper**:
  - 親 plan `cramer_lower_legendre` / `cramer_tendsto` を base に、`h_tilted_lower` 引数を `h_deriv` 仮定 + 内部 `h_tilted_lower_from_lln` 起動で置き換え
  - ~20-30 行

- [ ] **C-5 verify**: `lake env lean Common2026/Shannon/CramerLC2Discharge.lean` で Phase C 本体が 0 sorry。`Common2026.lean` に `import Common2026.Shannon.CramerLC2Discharge` を追記。

### 工数感

~120-200 行 (C-1 ~70 + C-2 ~50 + C-3 ~15 + C-4 ~25 + verify ~5)。1-1.5 セッション。proof-log `yes`。

### 失敗時 fallback

- **C-1 のRN deriv n-letter 化が `infinitePi` 上で詰まる**: L-D2 発動。`Measure.pi (fun _ : Fin n => μ)` 有限 IID 形に縮退。各 `n` で独立に RN deriv 構築できれば asymptotic 結果は変わらない（`ℕ → Ω` 形と `Fin n → Ω` 形は asymptotic に等価）
- **C-2 で「`h_tilted_lower` の C の取り方が `1/2` で済まない、`ε`-依存」と判明**: `C := tiltedAmbient ({|S̄_n₀ - a| < ε/2})` を `n₀ := ⌈ε`-時刻」で取って具体化。+15-20 行
- **L-D3 (Phase C 全体撤退)**: Phase A + B のみで publish。`cramer_lower_discharged` は本 plan では出さず、`tilted_lln_in_probability` を補助 publish（後続 plan で C をやる）。proof-log にデータを残す

---

## Phase V — verify + 親 plan L-C2 退避記録の discharge 完了反映 📋

### スコープ

- `lake env lean Common2026/Shannon/CramerLC2Discharge.lean` clean（0 sorry, 0 warning）
- `lake env lean Common2026/Shannon/Cramer.lean` clean（変更ないが olean rebuild 後の retest）
- `lake env lean Common2026.lean` clean
- 親 plan `cramer-moonshot-plan.md` の Phase C 状態絵文字を **🔄 L-C2 縮退 publish** から **✅ L-C2 discharge 完了 (本 plan 参照)** に更新（取り消し線で旧記録残す、本 plan のリンク追加）
- 親 plan §判断ログ #5（L-C2 退避記録）の直後に「discharge 完了 (本 plan)」を judgement #6 として **append-only** 追記
- 本 plan の §進捗ブロックを全 ✅ に更新

**proof-log**: no（最終整地）

### Done 条件

- 全 phase ✅ 状態絵文字、判断ログに discharge 完了記録
- 親 plan も discharge 完了反映済
- final verify silent

### ステップ

- [ ] **V-1 lake env lean 全体 verify**: 3 ファイル全て clean
- [ ] **V-2 親 plan 更新**: 状態絵文字 + 判断ログ append
- [ ] **V-3 本 plan 更新**: 進捗 ✅ + 判断ログ append
- [ ] **V-4 (任意) commit 分割**: Phase A / B / C / V の 4 コミットで切るか 1 コミットでまとめるかは autonomous 判断

### 工数感

~10-20 行 / 編集のみ。0.1-0.25 セッション。proof-log `no`。

---

## 撤退ライン

### Scope 縮小ライン (発動時に T1-C L-C2 discharge を縮小して publish)

- **L-D1**: **tilted LLN を弱形 (in-probability, Chebyshev 経由) で済ませて publish**
  - 発動条件: Phase B-1 で `strong_law_ae_real` の前提 `Pairwise IndepFun` 構築（Phase A-3）が **1 セッション以上**詰まる、または `strong_law_ae_real` の結論を tilted ambient の `μ_lam^∞`-積分形に持ち上げる plumbing が 50 行を超える
  - 縮退後: Mathlib LLN 直呼びでなく **Chebyshev 直接** で `μ_lam^∞({|S̄_n - a| ≥ ε}) ≤ Var / (n · ε²) → 0`。`variance_tilted_mul` (Mathlib `Tilted.lean:159`) + `iIndepFun.variance_sum` (要 loogle 確認、無ければ自前 ~20-30 行) で取れる。**Phase B が ~40 行縮減、Phase A の `Pairwise` plumbing も不要**（`iIndepFun_infinitePi` の `iIndepFun` 結論を Chebyshev 起動の `iIndepFun.variance_sum` 直渡しできるため）

- **L-D2**: **tilted IID 再構築を `Measure.pi (fun _ : Fin n => μ)` 有限 IID 形で代替**
  - 発動条件: Phase A-2 / C-1 で `Measure.infinitePi (fun _ => μ.tilted ...)` の RN deriv n-letter 化が **2 セッション以上**詰まる、または `infinitePi` ↔ `Measure.pi (Fin n)` の bridge plumbing が 80 行を超える
  - 縮退後: 各 `n` で `Measure.pi (fun _ : Fin n => μ.tilted ...)` を直接構築、`X` の `Ω` を `Fin n → Ω₀` 形に specialise。asymptotic 結果は不変（`ℕ → Ω` と `Fin n → Ω` の独立 family は同じ rate function を出す）。Phase A が ~60 行縮減、ただし `cramer_lower_discharged` の signature が `(X : Fin n → Ω₀ → ℝ)` 形 family に変更 ⇒ 親 plan `cramer_lower` の `(X : ℕ → Ω → ℝ)` 形と直接互換が崩れ、wrapper bridge 必要

- **L-D3**: **Phase A (tilted IID plumbing) のみ publish して discharge は後継 plan へ**
  - 発動条件: Phase B-3 / C-1 で **3 セッション以上**詰まる、または Phase B 完了時点で総行数が 600 行を超える見込み
  - 縮退後: Phase A の `tiltedAmbient` / `pairwise_indepFun_tilted_ambient` / `identDistrib_tilted_ambient` を独立 infrastructure として publish（後続 plan `cramer-lc2-discharge-phase-bc-plan.md` で B/C をやる）。本 plan は Phase A + V のみで close、proof-log で「Phase A の plumbing 完了 / discharge 未完」を明示

### 自作 plumbing 肥大ライン

- **L-DP1**: **`Measure.infinitePi (fun _ => μ.tilted)` の RN-deriv 公式が散らかる**
  - 縮退案: 各 cylinder set `{ω | (ω 0, …, ω (n-1)) ∈ S}` 上で RN deriv を **明示** （`∏ i ∈ range n, exp(lam · X 0 (ω i) - Λ(lam))` 形）に展開する。汎用 lemma 化せず inline で書く ~30-40 行（C-1 の山場を縮小）

- **L-DP2**: **`Pairwise ((· ⟂ᵢ[μ_lam^∞] ·) on Y)` で `Y i = X 0 ∘ eval i` の measurability チェイン**
  - 縮退案: `eval i` の measurability は Mathlib `Measure.infinitePi` で自動だが、`X 0 ∘ eval i` の composite measurability が dispatch しない場合は `(h_meas_0).comp (measurable_apply i)` を明示。+5-10 行

- **L-DP3**: **`Cramer.lean` 末尾追記 (option (i)) で olean rebuild が遅い**
  - 縮退案: option (ii)（`CramerLC2Discharge.lean` 新規）に確定（default option を採用、Phase A-1 で議論なしで decide）

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **Mathlib `iIndepFun.pairwise` 名称未確認** | 中 | 低 (自前 5-10 行で書ける) | Phase 0 で正式名確認、無ければ自前 helper |
| **`Measure.infinitePi (μ.tilted)` RN-deriv 公式が Mathlib に直接なし** | **高** (親 plan §危険 で特定済) | **高** (Phase C +50-80 行 or L-D2 発動) | L-D2 発動で `Measure.pi (Fin n)` 有限 IID 形に縮退、L-DP1 で inline 展開 |
| **`strong_law_ae_real` の `Pairwise` 前提が tilted ambient で取りにくい** | 中 | 中 (Phase A-3 +20-30 行 or L-D1 発動) | L-D1 発動で Chebyshev 直接路、`Pairwise` 不要 |
| **a.s. → in-probability の Mathlib lemma 名変更** | 低 | 低 (自前 ~20 行) | Phase 0 で確認、不在なら DCT で直書き |
| **C-1 change-of-measure n-letter 化が想定 80 行を超える** | 中-高 | 中-高 (L-D2 発動) | inline 展開（L-DP1）+ ε-neighborhood ⊆ {n·a ≤ S_n} の containment 順序を Phase C 着手時に確定 |
| **`integral_tilted_eq_deriv_cgf` の signature が Phase A で渡せない (前提が違う)** | 低 (既存 `Cramer.lean` で動作確認済) | 低 | A-1 で既存補題そのまま起動、signature 一致確認 |
| **Phase A の `Measure.infinitePi` 上の Pi instance auto-derive 不発** | 低-中 | 低 (haveI 明示で 1-2 行) | Phase A-2 着手時に確認、不発なら `instance` 明示 |
| **1 セッションで Phase A + B 完遂不能** | 中 | 中 (next session に持ち越し) | Phase A で 1 セッション、Phase B + C で 1-2 セッションを想定、合計 2-3 セッション計画 |
| **proof 規模が roadmap 上限 (500 行) を超える** | 中 | 中 | L-D1 / L-D2 / L-D3 を Phase 単位で発動可能に設計済 |
| **`h_deriv : Λ'(lam) = a` 仮定が caller-side で取りにくい** | 低 | 低 (親 plan `hlam_opt : lam · a - Λ(lam) = cramerRate` から導出可、wrapper で吸収) | Phase C-4 で `cramer_lower_legendre_discharged` の signature 設計時に検討、必要なら Legendre 達成性補題（親 plan Tier 3 想定）を兄弟 plan として切り出し |

---

## 危険箇所（実装着手時に注意）

CLAUDE.md "Mathlib-shape-driven Definitions" + "Subagent Inventory of Mathlib Lemmas" 規約に従い、本 plan で着手時に **特に注意すべき**箇所を明示:

1. **`Measure.infinitePi (fun _ => μ.tilted f)` ≠ `(Measure.infinitePi μ).tilted (f ∘ eval i 各座標)`**:
   - 一般には等しくない可能性あり (`tilted` の `f` は **全体測度** の上の density、ambient `infinitePi` 形だと座標ごとの tilting と integrability に整合性問題)
   - **本 plan は前者 (`Measure.infinitePi (fun _ => μ.tilted ...)`) を直接構築** = Phase A-2 の `tiltedAmbient` 定義
   - 後者を経由する誘惑は L-DP1 で回避（inline 展開）

2. **`iIndepFun_infinitePi` の前提**:
   - **`[∀ i, IsProbabilityMeasure (P i)]`** 必須。本 plan では `P i := μ.tilted (lam * X 0 ·)` 一定、A-1 の `isProbabilityMeasure_tilted_of_bounded` で確保
   - `∀ i, Measurable (X i)` は本 plan では `X i := id` (`Y i ω := X 0 (ω i)`) で自動 (`measurable_id`)

3. **`Measure.tilted` の `IsProbabilityMeasure` instance 連鎖**:
   - `μ.tilted f` の `IsProbabilityMeasure` は `[NeZero μ]` + `Integrable (exp ∘ f) μ` を要求 (Mathlib `Tilted.lean:126`)
   - bounded RV で `Integrable` は自動 (`integrable_exp_mul_of_bounded`, Cramer.lean 既存)、`NeZero` は `IsProbabilityMeasure` 自動
   - **本 plan で危険なのは `tiltedAmbient` の方の `IsProbabilityMeasure` instance**: `Measure.infinitePi (fun _ => prob)` が `IsProbabilityMeasure` であることを auto-derive できるかは Mathlib instance attribute 次第。Phase A-2 着手時に `#check (inferInstance : IsProbabilityMeasure (tiltedAmbient μ (X 0) lam))` で early verify

4. **`strong_law_ae_real` 結論の `μ[X 0]` を tilted ambient で何に解釈するか**:
   - 結論は `∀ᵐ ω ∂μ, Tendsto (S_n / n) atTop (𝓝 μ[X 0])`
   - 本 plan の `μ` 位置は `tiltedAmbient μ (X 0) lam`、`X 0` 位置は `fun ω => X 0 (ω 0)`
   - したがって `μ[X 0]` 位置の積分は `(tiltedAmbient μ (X 0) lam)[fun ω => X 0 (ω 0)]`
   - これを `(μ.tilted (lam * X 0 ·))[X 0]` に潰す bridge が要 = `Measure.infinitePi_map_eval` + `integral_map`、Phase B-1 内で完結
   - **危険**: bridge を踏まないと結論の極限値 `a` でなく謎の `tiltedAmbient[fun ω => X 0 (ω 0)]` 形で残り、後段に進めない

5. **`h_tilted_lower` の `C` の正符号**:
   - 親 plan `cramer_lower` の signature は `∃ C > 0, ∀ᶠ n, C · exp(…) ≤ μ.real {…}`
   - `C := 1/2` で取れる想定（Phase B-3 で `tiltedAmbient({|S̄_n - a| < ε/2}) ≥ 1/2` が eventually 成立）
   - **危険**: `C` が `ε`-依存に膨らむ場合（e.g. `C := tiltedAmbient({|S̄_{n₀} - a| < ε/2})` for some fixed `n₀(ε)`）、親 plan `cramer_lower` の `∃ C > 0` を満たすが asymptotic 議論に影響なし

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-19) L-D3 撤退発動 / Phase A のみ publish、Phase B-C は後続 plan へ defer**:
   - 当初: Phase A → B → C を 1 セッションで完遂、`cramer_lower_discharged` を hypothesis なし形で publish (中央予測 ~400 行)。
   - 実態: Phase A の主要 helper (`cgf_eval_eq_cgf_base`, `iIndepFun_tilted_ambient`, `identDistrib_tilted_ambient`, `iIndepFun_eval_under_infinitePi`, `identDistrib_eval_under_infinitePi`, `bounded_eval_family`) を `Common2026/Shannon/CramerLC2Discharge.lean` 171 行で publish 達成 (0 sorry, 0 errors, 0 warnings)。
   - 撤退理由: Phase B の `tilted_lln_ae` 内 `strong_law_ae_real` 起動で **`IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => μ₀.tilted ...))` instance の型クラス検索が repeatedly stuck**。`haveI` で `IsProbabilityMeasure (μ₀.tilted ...)` および `∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ => μ₀.tilted ...) i)` を provide しても、`Measure.infinitePi` の Mathlib instance (`[hμ : ∀ i, IsProbabilityMeasure (μ i)]` 要求) との unification で metavariable が解消せず、複数の caller (`integrable_tilted_ambient`, `tilted_lln_ae`, `tilted_lln_in_probability`) で stuck が transient に伝播。Lean 4 の instance synthesis が `(fun _ : ℕ => ...) i` の beta reduction を一貫して走らせない動作と思われる。
   - 同 stuck を解消するには (a) `tiltedAmbient_isProbabilityMeasure` を `instance` 宣言として登録するための専用 type-class (e.g., `BoundedMeasurable Y`) を導入、または (b) `tilted_lln_ae` 全体を inline で書き下す、(c) Mathlib 側に `tilted` + `infinitePi` の compatibility instance を追加、のいずれかが必要。本セッションでは Phase A 完成段階で着地し、Phase B-C は後続 plan に持ち越し。
   - publish 範囲: 計画 §撤退ライン L-D3 (Phase A のみ独立 infrastructure として publish) と整合。`cramer_lower_discharged` / `cramer_lower_legendre_discharged` / `cramer_tendsto_discharged` は本 plan では publish せず、親 `cramer_lower` の L-C2 退避形 (hypothesis 引数あり) を継続。
   - 残作業: Phase B (LLN 起動 + in-probability LLN) + Phase C (change-of-measure + wrapper) を後続 plan `cramer-lc2-discharge-phase-bc-plan.md` で実施。本 plan の Phase A scaffolding を import して continue 可。


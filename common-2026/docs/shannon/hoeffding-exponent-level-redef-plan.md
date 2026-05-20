# Hoeffding tradeoff: 指数 level 再定義による full genuine closure 計画 🌙

> **Parent**: [`hoeffding-tradeoff-moonshot-plan.md`](hoeffding-tradeoff-moonshot-plan.md) §Phase C/D /
> [`hoeffding-tradeoff-sandwich-plan.md`](hoeffding-tradeoff-sandwich-plan.md) 判断ログ #4 (DEF-FLAW)
> **在庫**: [`hoeffding-sandwich-discharge-inventory.md`](hoeffding-sandwich-discharge-inventory.md),
> [`hoeffding-tradeoff-mathlib-inventory.md`](hoeffding-tradeoff-mathlib-inventory.md)

<!--
記法は moonshot-plan-template / subplan-template と同じ:
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)`
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止 Phase は ~~取り消し線~~ で残す（過去参照のため）
- 判断ログは append-only
-->

## 進捗

> 🎯 **本筋修正計画**: 現 headline `rate → hoeffdingE2 P₁ P₂ alpha` は operational 量
> `steinTypeII_at_level_pmf` が **定数** Type-I 確率 level (`(1-P₁ⁿ(s)) ≤ alpha`) を焼き込んでおり
> tradeoff 曲線 `E₂(r)` を実現しないため数学的に偽 (sandwich plan 判断ログ #4 = DEF-FLAW)。
> 本計画は operational 量を **指数 level** (= 経験分布の KL-sublevel acceptance region `E_r n`) に
> 再定義し、genuine な Sanov 機構 (両側 LDP) でそのまま閉じる。**feasibility CONDITIONAL-YES,
> Mathlib 壁なし**。残リスクは統合 2 点 (Phase 3 complement rewrite + Phase 2/3 `h_in_E` の
> closed/strict 整合) に局所化、各 ~15-30 行。

- [ ] Phase 0 — signature / Sanov 結論形確認 + skeleton 配置 📋
- [ ] Phase 1 — `steinTypeII_exp` 定義 + 基本性質 📋
- [ ] Phase 2 — `E_r n` Finset + `h_in_E` 連続性 📋
- [ ] Phase 3 — complement type-union + Sanov-upper で Type-I → 0 📋
- [ ] Phase 4 — `sanov_ldp_equality` 配線 + KL 橋 + sign flip 📋
- [ ] Phase 5 — Qstar via `exists_hoeffding_minimizer_full_support` 📋
- [ ] Phase 6 — headline Tendsto 統合 📋
- [ ] Phase V — clean check + `Common2026.lean` 編入 📋

proof-log: Phase 3 (complement type-union + Type-I) のみ yes (最大の novel piece)。
他 Phase は既存資産 reuse 中心のため no。

## ゴール / Approach

### ゴール

operational 量を指数 level で再定義した上で、**hypothesis-free** な headline

```lean
theorem hoeffding_tradeoff_exp
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {r : ℝ} (h_r_pos : 0 < r) (h_r_lt : r < klDivPmf P₂ P₁) :
    Tendsto (fun n : ℕ => -((1 : ℝ) / n) * Real.log (steinTypeII_exp P₁ P₂ n r))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ r))
```

を publish する。`hoeffdingE2 P₁ P₂ r` (`Chernoff.lean:265`、制約 `klDivPmf Q P₁ ≤ r` =
KL-sublevel) は **再定義後の acceptance region `E_r n` (= `klDivIndex c n (pmfToMeasure P₁) ≤ r`)
と同じ KL 閾値**を共有するので、target 量がそのまま噛む (旧 plan で `alpha` (確率) と
`hoeffdingE2 P₁ P₂ alpha` (KL) が別物だった DEF-FLAW がここで消える)。

`r` の域: 第一目標は **interior** `0 < r < klDivPmf P₂ P₁` (Qstar が tilt で full-support
構成的)。境界 `r ≥ klDivPmf P₂ P₁` (E2 = 0 collapse) と `r = 0` は撤退ライン側で別 corollary。

### Approach (中核設計: type-index Finset 直定義 + Sanov 両側 collapse)

**設計原則 (CLAUDE.md「Mathlib-shape-driven Definitions」)**: 抽象 Finset `s` で
`-(1/n) log (1 - P₁ⁿ(s)) ≥ r` 形 (textbook 指数 level) を定義に使うと、`sanov_ldp_equality` /
`sanov_ldp_lower_bound_pointwise` の結論形 (`⋃ c ∈ E n, typeClassByCount`) との間に欠落 bridge を
再導入する赤フラグになる。よって **type-index Finset で直接定義**し、Sanov 補題群の結論形
(`SanovLDPEquality.lean:1253-1257`, `SanovLDP.lean:478-483`) がそのまま usable な shape を選ぶ。

#### 定義 (Phase 1/2、Sanov 結論形に直接噛む形)

```lean
-- acceptance region: 経験分布が P₁ から KL r 以内の type のみ受理
noncomputable def E_r (P₁ : α → ℝ) (n : ℕ) (r : ℝ) : Finset (TypeCountIndex α n) :=
  (Finset.univ).filter (fun c => klDivIndex (fun a => (c a : ℕ)) n (pmfToMeasure P₁ ..) ≤ r)
  -- Decidable は Classical.dec で供給 (noncomputable 伝播)

-- Type-II error of the exponential-level test (受理域の P₂ⁿ 質量)
noncomputable def steinTypeII_exp (P₁ P₂ : α → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  ((Measure.pi (fun _ : Fin n => pmfToMeasure P₂ ..))
    (⋃ c ∈ E_r P₁ n r, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal
```

`klDivIndex c n Q` (`SanovLDP.lean:97`、`∑ a, (c a/n)·(log(c a/n) - log Q.real{a})`) と
`typeClassByCount` (`SanovLDP.lean:82`)・`TypeCountIndex` (`SanovLDP.lean:55`) は Sanov 機構の
ネイティブ型なので、`steinTypeII_exp` は `sanov_ldp_equality` の measure 引数とそのまま一致する。

> **設計上の collapse (旧 plan からの最大の単純化)**: 旧 sandwich plan は achievability の liminf と
> converse の limsup を独立に sandwich していたが、`sanov_ldp_equality` (`SanovLDPEquality.lean:1243`)
> が **既に liminf 下界 (`sanov_ldp_lower_bound_pointwise`) + limsup 上界 (`sanov_ldp_upper_bound`) を
> `tendsto_of_le_liminf_of_limsup_le` で 1 本の Tendsto に sandwich 済**。よって achievability+converse は
> **単一 `sanov_ldp_equality` 呼び出しに collapse** し、両側不等式を別々に組む必要が消える。

#### discharge 経路 (genuine 既存資産、file:line verbatim)

| piece | 既存資産 | file:line | 役割 |
|---|---|---|---|
| **Tendsto sandwich (両側 collapse)** | `sanov_ldp_equality` | `SanovLDPEquality.lean:1243` | `(1/n) log P₂ⁿ(⋃_{E_r} T_c) → -klDivSumForm_ofVec Qstar (P₂.real∘singleton)`。liminf+limsup を内部で sandwich 済 |
| **`h_minimizer` premise** | `hoeffding_minimizer_ge` | `HoeffdingSandwichDischarge.lean:236` | `sanov_ldp_equality` の `h_minimizer : ∀ c ∈ E_r, klDivSumForm_ofVec Qstar (..) ≤ klDivIndex c n P₂`。既 0-sorry |
| **`h_in_E` (eventually 受理)** | `roundedTypeIndex_tendsto_vec` + `klDivSumForm_ofVec_continuous` | `SanovLDPEquality.lean:297` / `KLDivContinuous.lean:45` | `roundedTypeIndex Qstar n ∈ E_r n` eventually |
| **Type-I (H₀ error → 0)** | `sanov_ldp_upper_bound` を complement に | `SanovLDP.lean:471` | `(⋃_{E_r}T_c)ᶜ = ⋃_{c∉E_r,∑=n}T_c` の各 c で `klDivIndex c n P₁ > r` ⟹ Type-I rate ≥ r。**自作 AEP 不要** |
| **Qstar full-support** | `exists_hoeffding_minimizer_full_support` | `HoeffdingSandwichDischarge.lean:56` | genuine 3-case (interior は tilt)。L-H4 は gap でない |
| **KL 橋** | `klDivPmf_eq_log_diff_sum` + `klDivSumForm_ofVec` def | `CsiszarProjection.lean:231` / `KLDivContinuous.lean:31` | `klDivPmf = klDivSumForm_ofVec` 定義的、Sanov rate = `klDivSumForm_ofVec` |
| **rate ↔ E2 化** | `hQs_realises` (= `hoeffdingE2 = klDivPmf Qstar P₂`) | Phase 5 output | `-(-klDivSumForm_ofVec Qstar P₂) = klDivPmf Qstar P₂ = hoeffdingE2` |

#### 旧偽 headline との関係 (DEF-FLAW の解消)

旧 `steinTypeII_at_level_pmf` (定数 α 確率 level) を殺した gap は **Type-I AEP**
(`P₁ⁿ(⋃ T_c) ≥ 1-α`) だった — 定数 α では Sanov lower が tradeoff 曲線に接続しなかった。
指数 level では Type-I 制御が **`sanov_ldp_upper_bound` を complement に当てる genuine な
LDP** に置き換わり (`P₁ⁿ((⋃ T_c)ᶜ) ≤ exp(-n·r)` で Type-I rate ≥ r)、自作 AEP の rabbit hole が
消える。旧 plan の `steinTypeII_at_level_pmf` 関連は本計画では一切触らない (deprecated 据え置き)。

### Approach 図

```
Phase 0 : signature / Sanov 結論形確認 + skeleton (def 2 本 + 主定理 := by sorry)   ← 0.25 セッション (~70 行)
Phase 1 : steinTypeII_exp 定義 + 基本性質 (nonneg / le_one / pos)                  ← 0.25 セッション (~40 行)
Phase 2 : E_r n Finset + h_in_E 連続性 (rounded → Qstar、KL 連続)                  ← 0.5 セッション (40-60 行) ★統合リスク2
Phase 3 : complement type-union + Sanov-upper で Type-I → 0                        ← 0.75 セッション (50-80 行) ★統合リスク1, proof-log
Phase 4 : sanov_ldp_equality 配線 + KL 橋 + sign flip                              ← 0.5 セッション (40-60 行)
Phase 5 : Qstar via exists_hoeffding_minimizer_full_support                        ← 0.25 セッション (15-25 行)
Phase 6 : headline Tendsto 統合 (Type-II rate Tendsto から E2 へ整地)              ← 0.25 セッション (20-30 行)
Phase V : clean check + Common2026.lean 編入 (オーケストレータ)                    ← 5 分
```

合計見積もり **1-2 セッション**。Phase 2/3 が統合リスク 2 点を抱えるが各々壁ではない。

### ファイル構成

新規 `Common2026/Shannon/HoeffdingTradeoffExp.lean`。import:
`SanovLDPEquality` (sanov_ldp_equality / lower / roundedTypeIndex), `SanovLDP`
(sanov_ldp_upper_bound / typeClassByCount / klDivIndex / TypeCountIndex),
`HoeffdingSandwichDischarge` (exists_hoeffding_minimizer_full_support / hoeffding_minimizer_ge),
`KLDivContinuous` (klDivSumForm_ofVec / _continuous), `CsiszarProjection` (klDivPmf 橋),
`HoeffdingTradeoff` (pmfToMeasure family), `Chernoff` (hoeffdingE2)。

旧 `HoeffdingSandwichDischarge.lean` / `HoeffdingTradeoff.lean` は **拡張せず新規ファイル**:
(1) Phase 単位で分離検証、(2) 旧定数 α 系統と指数 level 系統を物理分離し DEF-FLAW 混入を防ぐ。

---

## Phase 0 — signature / Sanov 結論形確認 + skeleton 配置 📋

### スコープ

実装着手前に、Approach §discharge 経路の 7 資産が olean レベルで実在し、結論形が想定通りかを
確認 (skeleton が通れば自動確認)。skeleton: `E_r` / `steinTypeII_exp` の 2 def +
`hoeffding_tradeoff_exp` 主定理 + 補助 3 本 (`steinTypeII_exp_*` 基本性質, `h_in_E`, Type-I) を
`:= by sorry` で配置。

### ステップ

- [ ] 0-1 以下 7 本を skeleton の参照点として signature 確認:
  - `sanov_ldp_equality` (`SanovLDPEquality.lean:1243`) — 結論形
    `Tendsto (fun n => (1/n)·log (Q^n(⋃ c∈E n, T_c)).toReal) atTop (𝓝 (-(klDivSumForm_ofVec P (Q.real∘singleton))))`、
    premise `h_in_E : ∀ᶠ n, roundedTypeIndex P n ∈ E n` + `h_minimizer : ∀ n, ∀ c ∈ E n, klDivSumForm_ofVec P (Q.real∘·) ≤ klDivIndex c n Q`
  - `sanov_ldp_upper_bound` (`SanovLDP.lean:471`) — 結論
    `∃ N, ∀ n ≥ N, 0 < n → 0 < Q^n(⋃) → (1/n)·log Q^n(⋃ c∈E n, T_c) ≤ -D + ε` (∀ c∈E n, D ≤ klDivIndex c n Q)
  - `sanov_ldp_lower_bound_pointwise` (`SanovLDPEquality.lean:1071`、`sanov_ldp_equality` 内部呼び — 直接使わず可)
  - `roundedTypeIndex_tendsto_vec` (`SanovLDPEquality.lean:297`) — `Tendsto (fun n => fun a => (roundedTypeIndex P n a)/n) atTop (𝓝 P)`
  - `klDivSumForm_ofVec_continuous` (`KLDivContinuous.lean:45`)
  - `exists_hoeffding_minimizer_full_support` (`HoeffdingSandwichDischarge.lean:56`) + `hoeffding_minimizer_ge` (`:236`)
  - `klDivPmf_eq_log_diff_sum` (`CsiszarProjection.lean:231`), `klDivIndex` (`SanovLDP.lean:97`), `typeClassByCount` (`SanovLDP.lean:82`)
- [ ] 0-2 skeleton を Write。namespace `InformationTheory.Shannon` + `variable` 群
  (`[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`、
  `SanovLDP.lean:46-47` と一致させる)。`classical` を def に。
- [ ] 0-3 LSP `<new-diagnostics>` で sorry warning のみ (error 0) を確認。

### 依存補題 (file:line)

上記 0-1 の 7 本 + `pmfToMeasure` family (`HoeffdingTradeoff.lean:65/85/92`)。

### Done 条件

skeleton が `lake env lean Common2026/Shannon/HoeffdingTradeoffExp.lean` で sorry warning のみ
(error 0)。残 sorry は基本性質 3 本 + `h_in_E` + Type-I + 主定理。

### 撤退条件

`sanov_ldp_equality` の結論形が想定 (`(1/n)·log` の正符号、`-(klDivSumForm_ofVec ..)` の負号) と
食い違う場合: 在庫を再確認し sign convention を skeleton に正しく反映 (Phase 6 の sign flip 設計を
ここで確定)。それでも食い違えば該当 Phase の整地手順を判断ログに記録。

---

## Phase 1 — `steinTypeII_exp` 定義 + 基本性質 📋

### スコープ

`E_r` / `steinTypeII_exp` を確定し (Phase 0 で skeleton 配置済の def 本体)、
nonneg / le_one / (Qstar 受理 eventually 下での) pos の基本性質を確立。

### ステップ

- [ ] 1-1 `E_r P₁ n r := Finset.univ.filter (fun c => klDivIndex (fun a => (c a:ℕ)) n (pmfToMeasure P₁ ..) ≤ r)`。
  Decidable は `Classical.dec` (noncomputable)。`pmfToMeasure P₁` の引数 (`hP₁_nn`, `hP₁_sum`) を
  def 引数に通すか section variable に。
- [ ] 1-2 `steinTypeII_exp` = `(Measure.pi (fun _ => pmfToMeasure P₂ ..) (⋃ c ∈ E_r P₁ n r, typeClassByCount ..)).toReal`。
- [ ] 1-3 `steinTypeII_exp_nonneg`: `ENNReal.toReal_nonneg` で即。
- [ ] 1-4 `steinTypeII_exp_le_one`: `measureReal_le_one` (`SanovLDPEquality.lean:1203` 同型) +
  `IsProbabilityMeasure (Measure.pi ..)` (instance 自動)。
- [ ] 1-5 `steinTypeII_exp_pos` (eventually、`roundedTypeIndex Qstar n ∈ E_r n` 仮定下): `T_{roundedTypeIndex}`
  nonempty (`typeClassByCount_nonempty_of_sum`, `SanovLDPEquality.lean:310`) ⊆ ⋃ ⟹ singleton 質量 > 0
  (`Measure.pi_singleton` + `ENNReal.toReal_prod` + `Finset.prod_pos`、`SanovLDPEquality.lean:1288-1300` 同型)。
  ※ pos は Phase 4 で log を取るのに必要、`h_in_E` 確立後 (Phase 2) に依存するので skeleton では仮定形でよい。

### 依存補題 (file:line)

- `klDivIndex` (`SanovLDP.lean:97`), `typeClassByCount` (`SanovLDP.lean:82`), `TypeCountIndex` (`SanovLDP.lean:55`)
- `pmfToMeasure` family (`HoeffdingTradeoff.lean:65/85/92`)
- `typeClassByCount_nonempty_of_sum` (`SanovLDPEquality.lean:310`)
- `Measure.pi_singleton` + `ENNReal.toReal_prod` (Mathlib)

### Done 条件

2 def + 基本性質 3 本が 0-sorry。推定 ~40 行。

### 撤退条件

1-1 の Decidable / noncomputable 伝播が想定外に絡む (`filter` が型検査を通らない):
`Finset.univ.filter (fun c => decide (..))` を `@Finset.filter _ (Classical.decPred _) ..` で明示。
それでも詰まれば在庫 §自作 (旧 plan Phase 3-2 の Finset 化メモ) を参照。

---

## Phase 2 — `E_r n` Finset + `h_in_E` 連続性 📋

### スコープ

`sanov_ldp_equality` の premise `h_in_E : ∀ᶠ n, roundedTypeIndex Qstar n ∈ E_r P₁ n r` を確立。
**統合リスク2 (closed/strict sublevel 整合) の本体**。

### ステップ

- [ ] 2-1 Qstar (interior tilt, `klDivPmf Qstar P₁ ≤ r`、Phase 5 から) を所与とし、
  `klDivIndex (roundedTypeIndex Qstar n) n (pmfToMeasure P₁) → klDivSumForm_ofVec Qstar (P₁.real∘singleton)`
  を示す。`roundedTypeIndex_tendsto_vec` (`SanovLDPEquality.lean:297`) で
  `(roundedTypeIndex Qstar n)/n → Qstar` (Pi-topology) + `klDivSumForm_ofVec_continuous` (`KLDivContinuous.lean:45`)
  + `klDivIndex c n Q = klDivSumForm_ofVec (c/n) (Q.real∘singleton)` の定義一致 (要確認: `klDivIndex` の
  shape `∑ (c a/n)(log(c a/n) - log Q{a})` と `klDivSumForm_ofVec p q := ∑ p a (log p a - log q a)` は
  `p := c/n`, `q := Q.real∘singleton` で一致)。
- [ ] 2-2 `klDivSumForm_ofVec Qstar (P₁.real∘singleton) = klDivPmf Qstar P₁`
  (`pmfToMeasure_real_singleton` `HoeffdingTradeoff.lean:85` で `P₁.real{a} = P₁ a` + `klDivPmf` def 一致)。
- [ ] 2-3 **統合リスク2**: Qstar interior では `klDivPmf Qstar P₁ ≤ r` (closed sublevel、`hoeffdingConstraintSet`
  の `≤ alpha=r`)。`r` を **strict interior** `r < klDivPmf P₂ P₁` に取ると Qstar=tilt は制約を等号で
  満たす (`klDivPmf Qstar P₁ = r`、active constraint) 可能性が高く、`klDivIndex (rounded) → r` への
  収束だと `≤ r` の eventually 性が境界張り付きで微妙になる。**対策**: (i) Qstar が制約を strict に
  満たす内点 (`klDivPmf Qstar P₁ < r`) を取れるか確認 — interior tilt が active constraint を等号で
  満たすなら strict でない。(ii) その場合は `klDivIndex → klDivPmf Qstar P₁ = r` の収束に対し
  `E_r` を **closed sublevel `≤ r`** で定義しているので、`klDivIndex (rounded) ≤ r + o(1)` でなく
  `= r ± rounding` となり eventually `≤ r` が成立しない懸念。→ `E_r` を `≤ r` でなく
  **active 制約に合わせた等号近傍** にするのでなく、Qstar を `klDivPmf Qstar P₁ < r` の内点に
  わずかにずらす (連続性で E2 への影響は ε)、または **下記 撤退ライン L-EXP-IN** 発動。
- [ ] 2-4 (ii) が解ければ `klDivIndex (rounded Qstar) n P₁ → (< r)` から eventually `< r ≤ r` で
  `roundedTypeIndex Qstar n ∈ E_r n`。`Tendsto.eventually` (`< r` は開条件) で close。

### 依存補題 (file:line)

- `roundedTypeIndex_tendsto_vec` (`SanovLDPEquality.lean:297`)
- `klDivSumForm_ofVec_continuous` (`KLDivContinuous.lean:45`), `klDivSumForm_ofVec` def (`KLDivContinuous.lean:31`)
- `klDivIndex` def (`SanovLDP.lean:97`), `klDivPmf` def (`CsiszarProjection.lean:55`)
- `pmfToMeasure_real_singleton` (`HoeffdingTradeoff.lean:85`)
- Qstar の制約 strict 性: `hoeffdingConstraintSet` membership (`HoeffdingSandwichDischarge.lean:56` output)

### Done 条件

`h_in_E : ∀ᶠ n, roundedTypeIndex Qstar n ∈ E_r P₁ n r` が 0-sorry。推定 40-60 行。

### 撤退条件 (統合リスク2)

- **L-EXP-IN**: 2-3 の closed/strict 整合が解けない (Qstar=tilt が `klDivPmf Qstar P₁ = r` 等号で
  張り付き、`klDivIndex (rounded) ≤ r` の eventually 性が境界で破れる) 場合:
  `E_r` を `klDivIndex c n P₁ < r + δ_n` (rounding 誤差 `δ_n = O(log n / n)` を陽に許容) に緩める。
  Type-I (Phase 3) には `klDivIndex > r + δ_n ⟹ rate ≥ r` の閾値も連動して移す (収束先は同じ `r`)。
  これは Cover-Thomas の標準 LDP plumbing (acceptance region に rounding margin を持たせる) で
  Mathlib 壁ではない。判断ログに記録。
- それでも詰まれば `r` の域を `0 < r < klDivPmf P₂ P₁` の **strict 部分集合** (Qstar が内点で取れる
  範囲) に縮退し、その旨を headline 仮定に明示 (honest narrowing、`:= True` 不使用)。

---

## Phase 3 — complement type-union + Sanov-upper で Type-I → 0 📋

### スコープ

H₀ error (Type-I, 受理域外への P₁ 質量) が指数的に 0 に行くこと
`P₁ⁿ((⋃_{E_r} T_c)ᶜ) → 0` を `sanov_ldp_upper_bound` を complement に当てて示す。
**統合リスク1 (complement-as-type-union rewrite) の本体。本計画最大の novel piece、proof-log: yes。**

### ステップ

- [ ] 3-1 **complement = 反 type-union** (統合リスク1):
  `(⋃ c ∈ E_r P₁ n r, T_c)ᶜ = ⋃ c ∈ (E_r P₁ n r)ᶜ ∩ {c | ∑ c = n}, T_c`。
  `typeClassByCount` が `Fin n → α` を type で partition する (`∑ c ≠ n` の type は空
  `typeClassByCount_eq_empty_of_sum_ne`、`SanovLDP.lean` Phase A コメント参照) ことから、
  全空間 = `⋃_{∑c=n} T_c` の disjoint union。よって補集合 = 残りの type の union。
  `Finset.compl` + `Set.compl_iUnion` 系で rewrite (~15-25 行)。
- [ ] 3-2 反 type-union の各 c (`c ∉ E_r`, `∑ c = n`) で `klDivIndex c n (pmfToMeasure P₁) > r`
  (E_r の filter 否定 = `¬ (klDivIndex ≤ r)` = `> r`)。よって complement の Finset
  `E_r' n := (E_r n)ᶜ` (with `∑=n`) に対し `∀ c ∈ E_r', r ≤ klDivIndex c n P₁`
  (実際は strict `>` だが `sanov_ldp_upper_bound` の `D ≤ klDivIndex` premise には `r` を D に取る)。
- [ ] 3-3 `sanov_ldp_upper_bound (Q := pmfToMeasure P₁) (E := E_r') (D := r) ..` で
  `(1/n)·log P₁ⁿ(⋃_{E_r'} T_c) ≤ -r + ε` eventually ⟹ `P₁ⁿ((⋃_{E_r} T_c)ᶜ) ≤ exp(-n(r-ε)) → 0`。
- [ ] 3-4 **statement 化**: 本 plan の headline は Type-II rate Tendsto そのもの (Phase 4) なので
  Type-I は厳密には headline に**直接は不要**だが、operational に「これは指数 level α_n = exp(-nr) の
  genuine な test」であることを保証する補題として残す (`steinTypeII_exp_isTypeI_exp_level :
  ∀ᶠ n, P₁ⁿ((⋃ T_c)ᶜ) ≤ exp(-n(r-ε))`)。**旧定数 α 版を殺した gap (Type-I AEP) がここで genuine に
  埋まる**ことの証跡。proof-log に per-step (complement rewrite + Sanov upper の D=r 整合) を記録。

### 依存補題 (file:line)

- `sanov_ldp_upper_bound` (`SanovLDP.lean:471`)
- `typeClassByCount` partition / `typeClassByCount_eq_empty_of_sum_ne` (`SanovLDP.lean` Phase A, `:54` コメント)
- `klDivIndex` (`SanovLDP.lean:97`)
- `Set.compl_iUnion` / `Finset.compl` 系 (Mathlib)

### Done 条件

complement rewrite + `steinTypeII_exp_isTypeI_exp_level` が 0-sorry。推定 50-80 行。

### 撤退条件 (統合リスク1)

- **L-EXP-CMP**: 3-1 の `(⋃_E T)ᶜ = ⋃_{Eᶜ∩{∑=n}} T` rewrite が 30 行超 →
  全空間 partition `⋃_{∑c=n} T_c = univ` を補助補題に切り出し (`Fin n → α` の各点が唯一の type に
  属する)。`typeClassByCount_nonempty_of_sum` の逆 (各 x の type は `typeCount x`) を使う。
- それでも詰まれば Type-I 補題 (3-4) を headline から切り離し (headline は Type-II rate のみで
  閉じるので必須でない)、Type-I は「指数 level であることの注釈補題」として `∀ᶠ` のまま据え置き、
  judgement log に「operational 正当性は注釈、headline は Type-II rate で genuine」と記録。

---

## Phase 4 — `sanov_ldp_equality` 配線 + KL 橋 + sign flip 📋

### スコープ

Type-II rate の Tendsto を `sanov_ldp_equality` から取り出し、収束先を `klDivSumForm_ofVec` から
`klDivPmf Qstar P₂ = hoeffdingE2` に橋渡し、最後に `-(1/n) log` の sign flip を整地。

### ステップ

- [ ] 4-1 `sanov_ldp_equality (Q := pmfToMeasure P₂) (P := Qstar) (E := E_r P₁) h_in_E h_minimizer` で
  `Tendsto (fun n => (1/n)·log (steinTypeII_exp ..)) atTop (𝓝 (-(klDivSumForm_ofVec Qstar (P₂.real∘singleton))))`。
  `steinTypeII_exp` の def が `sanov_ldp_equality` の measure 引数と syntactic に一致することを確認
  (Phase 1 の def を Sanov shape に合わせた成果)。
- [ ] 4-2 `h_minimizer` 供給: `∀ n, ∀ c ∈ E_r P₁ n r, klDivSumForm_ofVec Qstar (P₂.real∘singleton) ≤
  klDivIndex c n (pmfToMeasure P₂)`。これは `hoeffding_minimizer_ge` (`HoeffdingSandwichDischarge.lean:236`)
  の per-type 形。`c/n` を pmf `P_c` とみなし `klDivIndex c n P₂ = klDivPmf P_c P₂`、`P_c ∈ K` (∵ c∈E_r ⟹
  `klDivPmf P_c P₁ ≤ r`) で `klDivPmf Qstar P₂ ≤ klDivPmf P_c P₂` を `hoeffding_minimizer_ge` から。
  ※ `P_c` の full-support は一般に成り立たない (count 0 の letter) → `hoeffding_minimizer_ge` の
  `hP_pos` 前提と衝突する懸念。**注意点**: 在庫で `hoeffding_minimizer_ge` の `hP_pos` を要求している。
  count-0 letter を持つ `c` への対応は撤退ライン L-EXP-MIN を参照。
- [ ] 4-3 **KL 橋**: `klDivSumForm_ofVec Qstar (P₂.real∘singleton) = klDivPmf Qstar P₂`
  (`pmfToMeasure_real_singleton` + `klDivPmf_eq_log_diff_sum` `CsiszarProjection.lean:231` +
  `klDivSumForm_ofVec` def 一致)。
- [ ] 4-4 収束先 `-(klDivSumForm_ofVec Qstar (P₂.real∘singleton)) = -klDivPmf Qstar P₂`。

### 依存補題 (file:line)

- `sanov_ldp_equality` (`SanovLDPEquality.lean:1243`)
- `hoeffding_minimizer_ge` (`HoeffdingSandwichDischarge.lean:236`)
- `klDivPmf_eq_log_diff_sum` (`CsiszarProjection.lean:231`), `klDivSumForm_ofVec` (`KLDivContinuous.lean:31`)
- `pmfToMeasure_real_singleton` (`HoeffdingTradeoff.lean:85`)
- `klDivIndex` (`SanovLDP.lean:97`)

### Done 条件

Type-II rate Tendsto (収束先 `-klDivPmf Qstar P₂`) が 0-sorry。推定 40-60 行。

### 撤退条件

- **L-EXP-MIN**: 4-2 の `h_minimizer` で `c/n` が count-0 letter を持ち `hoeffding_minimizer_ge` の
  `hP_pos` が供給できない場合: `sanov_ldp_equality` の `h_minimizer` は `klDivSumForm_ofVec Qstar (..) ≤
  klDivIndex c n P₂` の **直接形** (full-support 不要、`klDivIndex` は count-0 letter で項が 0 寄与)。
  `hoeffding_minimizer_ge` を経由せず、`klDivSumForm_ofVec` の凸性 / Pythagoras (`csiszar_pythagoras_inequality`,
  `CsiszarProjection.lean`) を `c/n` (boundary of simplex 可) に直接当てる経路に切替。`klDivPmf_nonneg` で
  `klDivPmf (c/n) Qstar ≥ 0` が count-0 でも成り立つことを利用 (`klDivPmf` の項は `p log(p/q)`、p=0 で 0)。
  判断ログに記録。

---

## Phase 5 — Qstar via `exists_hoeffding_minimizer_full_support` 📋

### スコープ

Phase 2/4 が要求する Qstar (interior tilt, full-support, `hoeffdingE2 = klDivPmf Qstar P₂`,
`klDivPmf Qstar P₁ ≤ r`) を `exists_hoeffding_minimizer_full_support`
(`HoeffdingSandwichDischarge.lean:56`) から供給。

### ステップ

- [ ] 5-1 `obtain ⟨Qstar, hQs_mem, hQs_realises, hQs_pos⟩ :=
  exists_hoeffding_minimizer_full_support P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum (le_of_lt h_r_pos)`。
- [ ] 5-2 `hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ r` から `klDivPmf Qstar P₁ ≤ r`
  (constraint set 定義) を抽出 (Phase 2 の `h_in_E` 用)。
- [ ] 5-3 `hQs_realises : hoeffdingE2 P₁ P₂ r = klDivPmf Qstar P₂` (Phase 6 の収束先一致用)。
- [ ] 5-4 `hQs_pos : ∀ a, 0 < Qstar a` (Phase 4 の minimizer / sanov_ldp_equality の `hP_full` 用)。
  interior case (`0 < r < klDivPmf P₂ P₁`) では Qstar = tilt で genuine full-support。

### 依存補題 (file:line)

- `exists_hoeffding_minimizer_full_support` (`HoeffdingSandwichDischarge.lean:56`)
- `hoeffdingConstraintSet` membership unfold (`Chernoff.lean` 周辺 / `HoeffdingSandwichDischarge.lean:67`)

### Done 条件

Qstar の 4 性質が取り出せ、Phase 2/4/6 に渡る。推定 15-25 行。

### 撤退条件

interior tilt の制約が等号 active (`klDivPmf Qstar P₁ = r`) で Phase 2 の strict 性が破れる場合は
Phase 2 §L-EXP-IN に合流。Phase 5 自体は既存補題 reuse なので壁なし。

---

## Phase 6 — headline Tendsto 統合 📋

### スコープ

Phase 4 の Type-II rate Tendsto (`(1/n) log steinTypeII_exp → -klDivPmf Qstar P₂`) を
`-(1/n) log` 形に sign flip し、収束先を `hoeffdingE2 P₁ P₂ r` に一致させて headline
`hoeffding_tradeoff_exp` を組む。

### ステップ

- [ ] 6-1 Phase 4 の `Tendsto (fun n => (1/n)·log (steinTypeII_exp ..)) atTop (𝓝 (-klDivPmf Qstar P₂))`
  を `Tendsto.neg` (`fun n => -(1/n)·log (..)`) で `𝓝 (klDivPmf Qstar P₂)` に。
  `-((1:ℝ)/n)·log x = -(((1:ℝ)/n)·log x)` の整地 (`neg_mul` / `ring_nf`)。
- [ ] 6-2 `hQs_realises : hoeffdingE2 P₁ P₂ r = klDivPmf Qstar P₂` で収束先を `hoeffdingE2 P₁ P₂ r` に rewrite。
- [ ] 6-3 `hoeffding_tradeoff_exp` を `:= ` 直接定義で close。境界条件は `0 < r < klDivPmf P₂ P₁` (interior)。

### 依存補題 (file:line)

- Phase 4 output (Type-II rate Tendsto)
- Phase 5 output (`hQs_realises`)
- `Tendsto.neg`, `neg_mul` (Mathlib)

### Done 条件

`hoeffding_tradeoff_exp` が 0-sorry hypothesis-free (interior 域)。推定 20-30 行。

### 撤退条件

sign flip / 整地が想定外に絡む: `Filter.Tendsto.congr'` で eventually 等式
(`-(1/n)log x = -(1/n · log x)`) を噛ませる。壁ではない。

---

## Phase V — clean check + `Common2026.lean` 編入 (オーケストレータ) 📋

- [ ] V-1 `lake env lean Common2026/Shannon/HoeffdingTradeoffExp.lean` silent (0 sorry / 0 error)。
- [ ] V-2 `Common2026.lean` に `import Common2026.Shannon.HoeffdingTradeoffExp` 追記
  (既存 Hoeffding import 群の直後)。
- [ ] V-3 `lake env lean Common2026.lean` で全体 silent 確認。
- [ ] V-4 本 plan 進捗ブロックを `✅` に更新、判断ログに publish 完了 append。
  親 plan `hoeffding-tradeoff-moonshot-plan.md` / `hoeffding-tradeoff-sandwich-plan.md` 判断ログ #4 に
  「指数 level 再定義で full genuine closure 達成」の cross-pointer を append。

---

## 撤退ライン

第一目標は **interior `0 < r < klDivPmf P₂ P₁` で hypothesis-free な指数 level full closure**。
段階的着地点:

- **L-EXP-IN** (Phase 2、統合リスク2): closed/strict sublevel 整合 → acceptance region に rounding
  margin `δ_n` を陽に許容、または `r` 域を Qstar 内点取得可能な strict 部分集合に honest narrowing。
- **L-EXP-CMP** (Phase 3、統合リスク1): complement type-union rewrite 肥大 → 全空間 partition を
  補助補題化、最悪 Type-I 補題を headline から切り離し注釈据え置き (headline は Type-II rate で genuine)。
- **L-EXP-MIN** (Phase 4): `h_minimizer` で count-0 letter による `hP_pos` 不足 →
  `csiszar_pythagoras_inequality` を `c/n` (simplex boundary 可) に直接当てる経路に切替。
- **最終 fallback**: interior が rabbit hole 化した場合、少なくとも **boundary `r ≥ klDivPmf P₂ P₁`**
  (E2 = 0、`hoeffding_tradeoff_achievability_at_boundary` `HoeffdingSandwichDischarge.lean:105` の
  指数 level 類似で genuine) を hypothesis-free で publish し、interior は honest 仮定
  (明示 signature pass-through、`:= True` 不使用) で残す。

**本計画が genuine closure 可能な鍵**: (1) achievability+converse が `sanov_ldp_equality` 単一呼び出しに
collapse、(2) Type-I が `sanov_ldp_upper_bound` complement で genuine (旧版を殺した自作 AEP gap が消滅)、
(3) Qstar / minimizer は既 0-sorry の `exists_hoeffding_minimizer_full_support` /
`hoeffding_minimizer_ge` reuse。残リスクは統合 2 点 (Phase 2/3) のみで Mathlib 壁なし。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(計画起草) 指数 level を type-index Finset で直定義する設計を採用 (textbook 抽象 Finset 形を回避)** —
   sandwich plan 判断ログ #4 (DEF-FLAW) で旧 `steinTypeII_at_level_pmf` (定数 α 確率 level) が tradeoff
   曲線を実現せず headline が偽と判明。本計画は operational 量を指数 level に再定義するが、textbook 形
   `-(1/n)log(1-P₁ⁿ(s)) ≥ r` (抽象 Finset `s`) では `sanov_ldp_equality` の結論形 (`⋃ c∈E n, typeClassByCount`)
   との間に欠落 bridge を再導入する (CLAUDE.md「Mathlib-shape-driven Definitions」の赤フラグ)。よって
   acceptance region を `E_r n := univ.filter (klDivIndex c n P₁ ≤ r)` の **type-index Finset で直接定義**し、
   `steinTypeII_exp` を `(P₂ⁿ(⋃_{E_r} T_c)).toReal` で Sanov ネイティブ shape に合わせる。
2. **(計画起草) achievability+converse を `sanov_ldp_equality` 単一呼び出しに collapse** — 旧 sandwich plan は
   liminf (achievability) と limsup (converse) を独立に sandwich していたが、`sanov_ldp_equality`
   (`SanovLDPEquality.lean:1243`) が `sanov_ldp_lower_bound_pointwise` + `sanov_ldp_upper_bound` を
   `tendsto_of_le_liminf_of_limsup_le` で 1 本の Tendsto に内部 sandwich 済。両側不等式を別々に組む工程
   (旧 plan Phase 2/3) が消え、Phase 4 単一配線に集約。
3. **(計画起草) Type-I 制御を `sanov_ldp_upper_bound` complement に置換 (旧版の自作 AEP gap が消滅)** —
   旧定数 α plan の最大 gap は Type-I AEP `P₁ⁿ(⋃ T_c) ≥ 1-α` の自作 (~30-50 行 rabbit hole)。指数 level では
   受理域外 `(⋃_{E_r} T_c)ᶜ = ⋃_{c∉E_r,∑=n} T_c` の各 c で `klDivIndex c n P₁ > r` なので
   `sanov_ldp_upper_bound (D := r)` がそのまま `P₁ⁿ(complement) ≤ exp(-n(r-ε)) → 0` を与える genuine LDP に
   置換される。残る統合作業は complement-as-type-union rewrite (統合リスク1) のみ。
4. **(計画起草) headline 域を interior `0 < r < klDivPmf P₂ P₁` に確定** — Qstar が tilt で構成的
   full-support になる域。`r = 0` (E2 = D > 0、`steinTypeII_exp` の受理域が極小) と boundary
   `r ≥ klDivPmf P₂ P₁` (E2 = 0 collapse) は撤退ライン側の別 corollary。`hoeffdingE2 P₁ P₂ r` の制約閾値
   (`klDivPmf Q P₁ ≤ r`) と `E_r n` の閾値 (`klDivIndex c n P₁ ≤ r`) が同じ KL-sublevel を共有するので、
   旧 plan の `alpha` (確率) ↔ `hoeffdingE2 alpha` (KL) の DEF-FLAW がここで構造的に解消される。

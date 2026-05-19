# Chernoff Information sandwich Tendsto ムーンショット計画 🌙 (T1-B 独立)

> **Status (2026-05-19)**: T1-B (Chernoff information, Cover-Thomas Theorem 11.9.1) 独立で
> **sandwich `Tendsto` 形** を publish するための plan。先行 plan
> [`chernoff-hoeffding-moonshot-plan.md`](chernoff-hoeffding-moonshot-plan.md) が T1-B/D 合同で
> Phase A残 + D残 + Phase C achievability まで完了させた (`Common2026/Shannon/Chernoff.lean`,
> 1066 行, 0 sorry) ところを、本 plan で **converse を hypothesis として外出し** して
> sandwich `Tendsto` を publish する。スコープは新規 file `Common2026/Shannon/ChernoffInformation.lean`
> (~500 行) に閉じ込め、既存 `Chernoff.lean` を黒箱で再利用する `HoeffdingTradeoff.lean`
> (`hoeffding_tradeoff_with_hypothesis`) と同型の publish pattern を採用する。
>
> **Predecessor**: [`chernoff-mathlib-inventory.md`](chernoff-mathlib-inventory.md) (本セッション
> 新規, T1-B 独立 sandwich Tendsto に絞った既存 API 在庫)。
>
> **Goal**: `chernoff_lemma_tendsto` の publish — `Tendsto (rate n) atTop (𝓝 (chernoffInfo P₁ P₂))`
> を、achievability (既存) + converse (hypothesis) + boundedness 2 本 (1 本 internal discharge / 1 本 hypothesis)
> から sandwich する `Tendsto` 形 wrapper として publish。
>
> **撤退ライン**: [L-Ch1] converse を hypothesis に / [L-Ch2] bdd-le を hypothesis に /
> [L-Ch3] bdd-ge も hypothesis に (一斉採用なら hypothesis count = 3、internal discharge 採用なら hypothesis count = 1 or 2)。

## 進捗

- [x] Phase 0 — Mathlib + Common2026 API 在庫 ✅ → [`chernoff-mathlib-inventory.md`](chernoff-mathlib-inventory.md)
- [ ] Phase 1 — `ChernoffInformation.lean` skeleton (sorries) 📋
- [ ] Phase 2 — bdd-ge internal discharge (`IsBoundedUnder (· ≥ ·)`) 📋
- [ ] Phase 3 — bdd-le internal discharge (`IsBoundedUnder (· ≤ ·)`, optional, L-Ch2 解除) 📋
- [ ] Phase 4 — sandwich Tendsto wrapper (`chernoff_lemma_tendsto`) 📋
- [ ] Phase 5 — DotEq corollary + Common2026 編入 + roadmap 更新 📋

## ゴール / Approach

### 最終到達点

新規 file `Common2026/Shannon/ChernoffInformation.lean` で:

```lean
/-- **Cover-Thomas Theorem 11.9.1** (sandwich Tendsto, hypothesis pass-through form).
撤退ライン L-Ch1 採用 (converse hypothesis), L-Ch2 hypothesis as-is. -/
theorem chernoff_lemma_tendsto
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_converse : Filter.limsup
        (fun n : ℕ => -((1:ℝ)/n) * Real.log (Chernoff.bayesErrorMinPmf P₁ P₂ n))
        atTop ≤ Chernoff.chernoffInfo P₁ P₂)
    (h_bdd_le : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => -((1:ℝ)/n) * Real.log (Chernoff.bayesErrorMinPmf P₁ P₂ n))) :
    Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (Chernoff.bayesErrorMinPmf P₁ P₂ n))
      atTop (𝓝 (Chernoff.chernoffInfo P₁ P₂))
```

(`IsBoundedUnder (· ≥ ·)` は内部 discharge し hypothesis から消す。)

### Approach (中核 3 ピース)

**hypothesis pass-through pattern** (`HoeffdingTradeoff.lean:296`
`hoeffding_tradeoff_with_hypothesis` と同型)。

1. **既存 publish を黒箱再利用**:
   - achievability `chernoff_lemma_achievability` (`Chernoff.lean:1059`) から
     `chernoffInfo ≤ liminf rate atTop`
   - 定義 `chernoffInfo` / `bayesErrorMinPmf` を `Chernoff.lean` から open

2. **converse は hypothesis pass-through** (撤退ライン L-Ch1):
   - `h_converse : limsup rate atTop ≤ chernoffInfo P₁ P₂` を hypothesis として取る
   - 次セッション (`chernoff-converse-moonshot-plan.md`) で `pmfToMeasure` bridge + Sanov LDP per-tilt
     で discharge 予定 (本セッション scope 外)

3. **boundedness 2 本の扱い**:
   - `IsBoundedUnder (· ≥ ·)` は achievability + `chernoffInfo_nonneg` から
     **internal discharge** (`chernoff_rate_isBoundedUnder_ge` ~25 行)
   - `IsBoundedUnder (· ≤ ·)` は hypothesis pass-through (撤退ライン L-Ch2)。
     **Optional**: `chernoff_rate_le_aux_upper` の中身を再構築すれば internal discharge 可能だが、
     ~120 行追加で本セッションのスコープを膨らませる。本セッションでは hypothesis pass-through とし、
     n=0 / n≥1 の edge case を含む構造補題 (`bayesErrorMinPmf` の n=0 退化)
     のみ publish (撤退ライン L-Ch2 採用)。

### Approach 図

```
Phase 0  : Mathlib + Common2026 API 在庫          ← 完了済 (in inventory)
           ────────────────────────────────────────────
Phase 1  : Skeleton (sorries 6-8 個)              ← 0.15 セッション (~10 min)
Phase 2  : bdd-ge internal discharge              ← 0.1 セッション (~10 min)
            ← 撤退ライン L-Ch3 解除 (bdd-ge は hypothesis を取らない)
Phase 3  : bdd-le internal discharge (optional)   ← 0.3 セッション (~30 min)
            ← 撤退ライン L-Ch2 を opt-out するルート (本セッションは取らない)
Phase 4  : sandwich Tendsto wrapper               ← 0.1 セッション (~10 min)
Phase 5  : DotEq corollary + library 編入         ← 0.1 セッション (~10 min)
```

### 規模見積 (再掲)

- 自作 1 (`chernoff_rate_isBoundedUnder_ge`): ~30 行
- 自作 2 (`chernoff_lemma_tendsto` sandwich wrapper): ~30 行
- 自作 3 (achievability re-export wrapper): ~20 行
- 自作 4 (limsup `eventually` 形 helper, n=0 edge case 用): ~50 行
- 自作 5 (`chernoff_dotEq` corollary): ~30 行
- skeleton / imports / docstring / namespace / Approach 説明: ~150 行
- 追加 helper (`bayesErrorMinPmf_lt_one` 等, conservative): ~80 行
- 余裕分 (proof body 短縮失敗 buffer): ~110 行
- **合計**: ~500 行 (撤退ライン L-Ch1+L-Ch2 全採用形)

### ファイル構成

```
Common2026/Shannon/
  Chernoff.lean                ← 既存 (1066 行, 0 sorry, 変更なし)
  ChernoffInformation.lean     ← 新規 (~500 行, 0 sorry)
  HoeffdingTradeoff.lean       ← 既存 (sandwich pattern 雛形)
Common2026/InformationTheory/
  Asymptotic.lean              ← 既存 (`DotEq` notation 利用)
Common2026.lean                ← `import Common2026.Shannon.ChernoffInformation` 追記
docs/shannon/
  chernoff-mathlib-inventory.md ← 新規
  chernoff-moonshot-plan.md     ← 本ファイル (新規)
```

---

## 依存関係

完了済 (再利用可、本 plan 直接依存):

- [x] `Common2026/Shannon/Chernoff.lean` (`chernoffInfo`, `chernoffInfo_attained`,
  `chernoffInfo_nonneg`, `chernoffInfo_symm`, `bayesErrorMinPmf`, `bayesErrorMinPmf_pos`,
  `bayesErrorMinPmf_le_half_Z_pow`, `chernoffZSum`, `chernoffZSum_pos`,
  `chernoff_achievability`, `chernoff_lemma_achievability`,
  `chernoff_rate_ge_chernoffInfo_eventually`)
- [x] `Common2026/Shannon/HoeffdingTradeoff.lean` (sandwich Tendsto pattern 雛形,
  `hoeffding_tradeoff_with_hypothesis`)
- [x] `Common2026/InformationTheory/Asymptotic.lean` (`DotEq`, `dotEq_iff_tendsto_log_div`)
- [x] Mathlib `Mathlib.Topology.Order.LiminfLimsup.tendsto_of_le_liminf_of_limsup_le`
- [x] Mathlib `Mathlib.Order.Filter.IsBounded.IsBoundedUnder`

---

## Phase 1 — Skeleton 📋

### スコープ

`ChernoffInformation.lean` の全主定理 + 補助補題を `:= by sorry` (skeleton 段階)
で並べた file を Write、LSP 診断で type-check OK 確認。

### ステップ

- [ ] **1-1 imports + namespace**:
  ```lean
  import Common2026.Shannon.Chernoff
  import Common2026.InformationTheory.Asymptotic
  import Mathlib.Topology.Order.LiminfLimsup
  import Mathlib.Order.Filter.IsBounded
  namespace InformationTheory.Shannon.ChernoffInformation
  open InformationTheory.Shannon.Chernoff Filter Real
  open scoped Topology
  ```

- [ ] **1-2 skeleton (sorries)**:
  - `chernoff_rate_isBoundedUnder_ge` (Phase 2)
  - `chernoff_lemma_tendsto` (Phase 4)
  - `chernoff_dotEq` (Phase 5, optional)

### Done 条件

skeleton (sorry のみ) で `lake env lean ChernoffInformation.lean` clean (sorry 警告のみ)。

---

## Phase 2 — bdd-ge internal discharge 📋

### スコープ

`Filter.IsBoundedUnder (· ≥ ·) atTop rate` を、`chernoffInfo_nonneg` + `chernoff_lemma_achievability`
から導出する補題 `chernoff_rate_isBoundedUnder_ge` (~25-30 行)。

### ステップ

- [ ] **2-1 statement 確定**:
  ```lean
  lemma chernoff_rate_isBoundedUnder_ge
      (P₁ P₂ : α → ℝ) [Nonempty α]
      (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
      Filter.IsBoundedUnder (· ≥ ·) atTop
        (fun n : ℕ => -((1:ℝ)/n) * Real.log (bayesErrorMinPmf P₁ P₂ n))
  ```

- [ ] **2-2 proof**:
  - **直接路線**: `chernoff_rate_ge_chernoffInfo_eventually` で `rate n ≥ chernoffInfo + log 2 / n ≥ chernoffInfo`
    を `∀ᶠ n, rate n ≥ chernoffInfo` の形で取り、`Filter.isBoundedUnder_of_eventually_ge` で結論。
  - **fallback**: `Filter.isBoundedUnder_const (chernoffInfo P₁ P₂)` + 直接 `filter_upwards` 経路。

### 工数感

~25-30 行 (`filter_upwards` + `linarith` 系で短い)。proof-log `no`。

### 失敗時 fallback

- **`Filter.isBoundedUnder_of_eventually_ge` の名前が違う / 存在しない場合**: `Filter.IsBoundedUnder`
  の定義 (`(f.map u).IsBounded r`) を unfold して直接 `⟨chernoffInfo P₁ P₂, ...⟩` を構築 (~10 行追加)。

---

## Phase 3 — bdd-le internal discharge (optional, L-Ch2 解除ルート) 📋

### スコープ

`Filter.IsBoundedUnder (· ≤ ·) atTop rate` を、既存 `Chernoff.lean` の `private`
`chernoff_rate_le_aux_upper` を再構築して導出する補題 `chernoff_rate_isBoundedUnder_le`
(~80-120 行)。

**本セッションでは取らない (L-Ch2 採用)**。本 Phase は将来 plan の reference。

### ステップ (将来用)

- [ ] **3-1 `p_min`-based lower bound**: `bayesErrorMinPmf ≥ (1/2) · p_min^n` を再構築
  (既存 `Chernoff.lean:898-1000` の中身を再現)。

- [ ] **3-2 log 変換**: `-(1/n) log bayesErrorMinPmf ≤ -log p_min + log 2`。

- [ ] **3-3 wrap**: `Filter.IsBoundedUnder.of_eventually_le` で結論。

### 工数感 (将来用)

~80-120 行。proof-log `no` (既存 implementation の transliteration)。

---

## Phase 4 — sandwich Tendsto wrapper 📋

### スコープ

`chernoff_lemma_tendsto` を `tendsto_of_le_liminf_of_limsup_le` 1 発で publish。

### ステップ

- [ ] **4-1 statement**:
  ```lean
  theorem chernoff_lemma_tendsto
      (P₁ P₂ : α → ℝ) [Nonempty α]
      (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
      (h_converse : Filter.limsup
          (fun n : ℕ => -((1:ℝ)/n) * Real.log (bayesErrorMinPmf P₁ P₂ n))
          atTop ≤ chernoffInfo P₁ P₂)
      (h_bdd_le : Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun n : ℕ => -((1:ℝ)/n) * Real.log (bayesErrorMinPmf P₁ P₂ n))) :
      Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (bayesErrorMinPmf P₁ P₂ n))
        atTop (𝓝 (chernoffInfo P₁ P₂))
  ```

- [ ] **4-2 proof**:
  ```lean
  refine tendsto_of_le_liminf_of_limsup_le ?_ h_converse h_bdd_le ?_
  · exact chernoff_lemma_achievability P₁ P₂ hP₁_pos hP₂_pos
  · exact chernoff_rate_isBoundedUnder_ge P₁ P₂ hP₁_pos hP₂_pos
  ```

### 工数感

~10-30 行 (proof body は 3-5 行、docstring が大半)。proof-log `no`。

---

## Phase 5 — DotEq corollary + library 編入 📋

### スコープ

`bayesErrorMinPmf P₁ P₂ n ≐ exp(-n · chernoffInfo P₁ P₂)` の `DotEq` 形を corollary として publish。
`Common2026.lean` に `import` 追加、`textbook-roadmap.md` Ch.11 行更新。

### ステップ

- [ ] **5-1 DotEq corollary**:
  ```lean
  theorem chernoff_dotEq
      ... (sandwich Tendsto hypotheses 全部) :
      DotEq (fun n : ℕ => bayesErrorMinPmf P₁ P₂ n)
        (fun n : ℕ => Real.exp (-(n : ℝ) * chernoffInfo P₁ P₂))
  ```
  証明は `dotEq_iff_tendsto_log_div` (`Asymptotic.lean:116`) 経由。

- [ ] **5-2 `Common2026.lean` 編入**:
  ```lean
  import Common2026.Shannon.ChernoffInformation
  ```
  を `Chernoff.lean` の直下 (line 91 付近) に追記。

- [ ] **5-3 `textbook-roadmap.md` 更新**:
  Ch.11 行の「代表定理」欄に `chernoff_lemma_tendsto` を append、Tier 1 §T1-B カードに
  publish 情報 (`Common2026/Shannon/ChernoffInformation.lean` / 行数 / 0 sorry) を append。

- [ ] **5-4 `moonshot-seeds.md` Status 更新**:
  T1-B Chernoff Tendsto 形 publish について 1 段落 (行数 / 主定理 / 採用撤退ライン) を append。

### 工数感

~30-50 行 (DotEq corollary 30 + Common2026 編入 5 + roadmap 更新 docs 側)。proof-log `no`。

---

## 撤退ライン

### Scope 縮小ライン (T1-B sandwich Tendsto)

- **L-Ch1**: converse (`limsup ≤ chernoffInfo`) を hypothesis として外出し
  - 発動条件: Sanov LDP per-tilt + `pmfToMeasure` bridge による discharge が 1 セッション内で困難
  - 縮退形: `chernoff_lemma_tendsto` を `h_converse` hypothesis 付きで publish
  - **本セッション**: **採用**

- **L-Ch2**: bdd-le (`IsBoundedUnder (· ≤ ·)`) を hypothesis として外出し
  - 発動条件: `chernoff_rate_le_aux_upper` 再構築が ~120 行を超え、セッション規模を膨らませる
  - 縮退形: `chernoff_lemma_tendsto` を `h_bdd_le` hypothesis 付きで publish
  - **本セッション**: **採用** (sandwich Tendsto に focus、bdd-le 再構築は future plan)

- **L-Ch3**: bdd-ge (`IsBoundedUnder (· ≥ ·)`) を hypothesis として外出し
  - 発動条件: `chernoff_rate_ge_chernoffInfo_eventually` から bdd-ge への変換補題が組めない
  - 縮退形: `chernoff_lemma_tendsto` を `h_bdd_ge` hypothesis 付きで publish
  - **本セッション**: **不採用** (Phase 2 で internal discharge する)

### 自前 plumbing 肥大ライン

- **L-P1**: Phase 2 `chernoff_rate_isBoundedUnder_ge` が `Filter.isBoundedUnder_of_eventually_ge`
  の API 不在で詰まる場合
  - 縮退: `Filter.IsBoundedUnder` を直接 unfold して `⟨chernoffInfo, ...⟩` を構築 (~10 行追加)

- **L-P2**: Phase 5 DotEq corollary の `dotEq_iff_tendsto_log_div` が `bayesErrorMinPmf` の正値性
  要求と衝突する場合
  - 縮退: DotEq corollary を skip、`Tendsto` 形のみ publish

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| `tendsto_of_le_liminf_of_limsup_le` の `IsBoundedUnder` 既定 tactic `isBoundedDefault` が `ℝ`-on-`atTop` で fire しない | 中 | 低 (Phase 4 で +5 行) | Phase 4 で hypothesis を 4 個全部明示的に渡す (default tactic を起こさない)。 |
| Phase 2 bdd-ge で `n = 0` での `1/n = 0` 退化 で `rate 0 = 0 * log _ = 0` 経路が `chernoffInfo ≥ 0` と整合しなくなる | 低 | 低 (eventually-form で済む) | `filter_upwards [eventually_gt_atTop 0]` で `n ≥ 1` 制限。 |
| `chernoff_rate_ge_chernoffInfo_eventually` のorientation (`≥` vs `≤`) が想定と逆 | 低 | 低 (~5 行) | Inventory で signature verbatim 確認済、`≥` orientation で確定。 |
| DotEq corollary `dotEq_iff_tendsto_log_div` の signature が `bayesErrorMinPmf > 0` を要求 | 中 | 低 (`bayesErrorMinPmf_pos` から既知) | Phase 5 で `bayesErrorMinPmf_pos` を hypothesis に渡す。 |

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-19) T1-B 独立 plan で `Chernoff.lean` の sandwich Tendsto を publish**:
   先行 plan `chernoff-hoeffding-moonshot-plan.md` (T1-B/D 合同) が **achievability side** までで
   close (Phase B converse + Phase E full Tendsto は L-S1+L-S2 で defer) されている状況に対し、
   converse + 2 つの bdd を hypothesis として取る形で **sandwich Tendsto wrapper を独立に publish**
   する設計とする。`HoeffdingTradeoff.lean:296` `hoeffding_tradeoff_with_hypothesis` と同型 pattern。
   converse の中身は次セッション `chernoff-converse-moonshot-plan.md` で
   `pmfToMeasure` bridge + Sanov LDP per-tilt 経路で discharge する想定。

2. **(2026-05-19) bdd-ge は本セッションで internal discharge、bdd-le は hypothesis に**:
   `chernoff_rate_ge_chernoffInfo_eventually` (`Chernoff.lean:883`) + `chernoffInfo_nonneg`
   が既に揃っており、bdd-ge は ~25 行で internal discharge 可能 (L-Ch3 不採用)。一方 bdd-le
   は `private` `chernoff_rate_le_aux_upper` (~120 行) の transliteration が必要で、本セッション
   scope (~500 行) では撤退ライン L-Ch2 を採用 (hypothesis pass-through)。bdd-le internal discharge は
   future plan で `chernoff-converse-moonshot-plan.md` と一緒に処理する可能性あり。

3. **(2026-05-19) DotEq corollary は Phase 5 で publish 試行**:
   `dotEq_iff_tendsto_log_div` (`Asymptotic.lean:116`) が `bayesErrorMinPmf > 0` を要求する想定
   (Stein/Hoeffding 等で同 pattern 使用済)。`bayesErrorMinPmf_pos` (`Chernoff.lean:807`) で
   discharge 可能。signature 衝突時は L-P2 (DotEq skip) を発動。

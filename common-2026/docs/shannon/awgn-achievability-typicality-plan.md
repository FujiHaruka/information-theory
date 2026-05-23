# AWGN Achievability — typicality discharge ムーンショット計画 🌙 (T2-A Tier-3 follow-up)

<!--
雛形メモ (moonshot-plan-template.md):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)`
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更
- 判断ログは append-only
-->

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §「撤退ライン F-1
> (continuous achievability)」 + 判断ログ #1 (F-1 採用 = `IsAwgnTypicalityHypothesis`
> を hypothesis predicate として外出し)。
>
> **Sibling plans (scope 直交)**:
> [`awgn-f1-discharge-moonshot-plan.md`](awgn-f1-discharge-moonshot-plan.md) — 親 plan の
> **F-4** (kernel measurability、seed 名 F-1)、`AWGNF1Discharge.lean` 148 行で完了。
> 本 plan は親 plan の **F-1** (typicality / achievability core) を扱う別物。
> 未起草の `awgn-mi-bridge-plan.md` (F-2) / `awgn-converse-aux-plan.md` (F-3) は
> 本 plan と独立。
>
> **Status (2026-05-24)**: 未着手。`AWGNAchievability.lean:43-90` の
> `IsAwgnTypicalityHypothesis` は conclusion-as-hypothesis (predicate が universal-
> `R, ε` quantified achievability statement そのもの、body は 1 行 passthrough)。
> これが現存唯一の defect。本 plan で Cover-Thomas 9.2 の解析 (random Gaussian
> codebook + continuous AEP + union bound + expurgation) を Lean 化して discharge。
>
> **Goal**: `Common2026/Shannon/AWGNAchievabilityDischarge.lean` 新規 publish:
>
> ```lean
> theorem isAwgnTypicalityHypothesis (P : ℝ) (hP : 0 < P) (N : ℝ≥0)
>     (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N) :
>     IsAwgnTypicalityHypothesis P N h_meas
>
> theorem awgn_theorem_F1F4_discharged …      -- 主定理 wrapper、残 hyp は F-2 + F-3
> ```
>
> **撤退ライン (本 plan 内)**: [T-1] random codebook の `Measure.pi` 型クラス壁 →
> `EuclideanSpace ℝ (Fin (M*n))` flatten / [T-2] continuous AEP for n-dim Gaussian
> が Mathlib 不在 → AEP 1 本を `IsContinuousAEPGaussian` regularity hyp に外出し
> (achievability core は本物 discharge を維持) / [T-3] expurgation の Mathlib lemma
> 不在 → 手書き ~30 行 / [T-4] 全体 700 行超 → AEP plan と coding plan に 2 分割。
> **詳細 §撤退ライン**。
>
> **honesty 規律**: 本 plan は「load-bearing hyp」状態を analytic discharge に
> 置換することが目的。T-2 採用時の `IsContinuousAEPGaussian` 残置は **regularity
> hyp (Mathlib gap)** の条件 ((a) 結論型と異なる、(b) docstring で "NOT load-
> bearing" 明示、(c) achievability core 自体は Phase C-D で本物 discharge) を全て
> 満たすこと。CLAUDE.md「検証の誠実性」「Mathlib 壁の 4 分類」適用、parallel-
> gaussian / EPI と同型 staged pattern。

## 進捗

- [ ] Phase 0 — Mathlib + Common2026 在庫 (codebook 測度 / continuous AEP / 球殻 volume / expurgation) 📋 → `awgn-achievability-typicality-mathlib-inventory.md` (新規予定)
- [ ] Phase A — `gaussianCodebook` 測度 + IndepFun + marginal lemma 📋
- [ ] Phase B — Continuous joint-typical set + AEP 3 bounds (T-2 採用なら hyp 化) 📋
- [ ] Phase C — Random coding error bound (union bound) 📋
- [ ] Phase D — Expurgation (avg → exists individual + power constraint bridge) 📋
- [ ] Phase E — `isAwgnTypicalityHypothesis` 統合 + main wrapper 📋
- [ ] Phase V — verify (lake env lean clean + honesty 再 audit)

## ゴール / Approach

### Goal (最終定理 signature)

現状の defect (`AWGNAchievability.lean:43-90`):

```lean
def IsAwgnTypicalityHypothesis (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {R}, 0 < R → R < (1/2) * Real.log (1 + P / N) → ∀ {ε}, 0 < ε →
    ∃ N₀, ∀ n ≥ N₀, ∃ M (_hM_lb : Nat.ceil (Real.exp (n*R)) ≤ M) (c : AwgnCode M n P),
      ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε
-- ↑ predicate そのものが universal achievability conclusion
-- ↓ body は 1 行 passthrough (load-bearing hyp)
theorem awgn_achievability … (h_typicality : …) … := h_typicality hR_pos hR hε
```

本 plan の最終形:

```lean
namespace InformationTheory.Shannon.AWGN

/-- F-1 撤退ラインの本物 discharge (Cover-Thomas 9.2 の Lean 化)。 -/
theorem isAwgnTypicalityHypothesis (P : ℝ) (hP : 0 < P) (N : ℝ≥0)
    (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N) :
    IsAwgnTypicalityHypothesis P N h_meas := …

/-- `awgn_achievability` から `h_typicality` を消した形。 -/
theorem awgn_achievability_F1_discharged … : … :=
  awgn_achievability P hP N hN h_meas
    (isAwgnTypicalityHypothesis P hP N hN h_meas) hR_pos hR hε

/-- 主定理 wrapper: F-1 + F-4 を discharge、残 hyp は F-2 + F-3。 -/
theorem awgn_theorem_F1F4_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_mi_bridge : …)                           -- 残 F-2
    (h_converse : IsAwgnConverseHypothesis P N (isAwgnChannelMeasurable N))  -- 残 F-3
    {R} (hR_pos) (hR_lt_C) {ε} (hε) :
    ∃ N₀, … :=
  awgn_channel_coding_theorem P hP N hN (isAwgnChannelMeasurable N)
    (isAwgnTypicalityHypothesis _ hP _ hN _) h_mi_bridge h_converse hR_pos hR_lt_C hε

end InformationTheory.Shannon.AWGN
```

T-2 採用時の最終形は `isAwgnTypicalityHypothesis` の signature に
`(h_aep : IsContinuousAEPGaussian P N)` が 1 本残るが、これは achievability core
ではなく n-dim Gaussian SLLN の Mathlib gap のみを切り出した regularity hyp。

### Approach (overall strategy / shape of solution)

**戦略**: Cover-Thomas 9.2 (Theorem 9.1.1 achievability) の 4 段 (random codebook
→ continuous joint AEP → union bound → expurgation) をそのまま Lean に転写。各段
を独立 Phase に割り当て、Phase 間の界面型は Phase 0 inventory で先に確定する
(skeleton-driven, CLAUDE.md)。

```
(a) Random Gaussian codebook                            [Phase A]
    X(m,i) ~ i.i.d. 𝒩(0, P-δ), m=1..M, i=1..n
    → gaussianCodebook M n σ² : Measure (Fin M → Fin n → ℝ)
       + IndepFun across codewords + each codeword law

(b) Continuous joint AEP                                [Phase B]
    P[(X,Y) ∈ A_ε^{(n)}] → 1
    |A_ε^{(n)}|_Leb ≤ exp(n(h(X,Y)+ε))
    For (X',Y) indep: P[(X',Y) ∈ A_ε^{(n)}] ≤ exp(-n(I-3ε))
    → continuousJointTypical p W ε n : Set (ℝⁿ × ℝⁿ)
       + 3 つの AEP bound
       (Mathlib gap 大 → T-2 で `IsContinuousAEPGaussian P N` hyp 化が現実解)

(c) Joint typical decoder + union bound                 [Phase C]
    Pe_avg ≤ P[(X(1),Y) ∉ A_ε] + (M-1) · exp(-n(I-3ε)) ≤ 2ε
    → randomCodingErrorBound + decoder measurability

(d) Expurgation                                         [Phase D]
    E_codebook[Pe_avg] ≤ 2ε ⇒ ∃ codebook with Pe_avg ≤ 2ε
    Throw away worst half ⇒ ∃ codebook with max Pe ≤ 4ε
    + power constraint への bridge
    → AwgnCode M' n P (M' = M/2) を exists 抽出

(e) 統合                                                [Phase E]
    → isAwgnTypicalityHypothesis + main wrapper
```

**Mathlib-shape-driven definitions** (CLAUDE.md):

- **`gaussianCodebook`**: 2 段 `Measure.pi` (or T-1 で flatten した
  `stdGaussian (EuclideanSpace ℝ (Fin (M*n)))`)。Phase 0 判断 #2 で確定。
- **`continuousJointTypical`**: textbook 流の `|(1/n) log p - h| < ε` を、Phase B/C
  bound lemma の結論形に合わせて `rnDeriv` / `differentialEntropy` / `klDiv` の
  いずれの形で書くかを Phase 0 判断 #3 で確定 (CLAUDE.md「`f (compProd ...)` の
  reshape bridge」レッドフラグ回避)。
- **`expurgation`**: Mathlib `MeasureTheory.exists_le_of_integral_le_...` 系を
  Phase 0 で在庫確認、不在なら T-3 手書き。

### 規模見積もり

| Phase | 内容 | T-2 採用時 | T-2 不採用時 |
|---|---|---|---|
| Phase 0 | inventory (別 file) | 0 行 (Lean) | 0 行 (Lean) |
| Phase A | gaussianCodebook + IndepFun + marginal | 80-150 | 同 |
| Phase B | continuous AEP 3 bound | 50 (hyp 化) | 200-400 |
| Phase C | union bound + decoder | 100-150 | 同 |
| Phase D | expurgation | 50-80 | 同 |
| Phase E | 統合 + wrapper | 30-50 | 同 |
| skeleton + plumbing | | 50-80 | 同 |
| **合計** | | **~360-560** | **~510-810** |

中央予測 **~500 行** (T-2 採用、最有力)。親 plan §D.4 の見積 500-800 行と整合
(本 plan は T-2 採用で下限寄りに収束する想定)。

### ファイル構成

```
Common2026/Shannon/
  AWGNAchievabilityDischarge.lean   ← 新規 (本 plan 出力、~500 行)
                                       Phase A-E を 1 file 集約
  AWGNAchievability.lean (既存)     ← 本 plan の import 元 (IsAwgnTypicalityHypothesis 定義)
  AWGNMain.lean (既存)              ← 主定理 wrapper の import 元
  AWGNF1Discharge.lean (既存)       ← F-4 discharge、本 plan の import 元
Common2026.lean                     ← 1 行 import 追加 (Phase V、オーケストレータ実施)
docs/shannon/
  awgn-achievability-typicality-mathlib-inventory.md  ← Phase 0 出力
  awgn-achievability-typicality-plan.md               ← 本 plan
  proof-log-awgn-typicality-phase[A-D].md             ← Phase 単位 (yes 指定 Phase のみ)
```

**imports** (CLAUDE.md `Import Policy` 厳守、`import Mathlib` 禁止):

```lean
import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNAchievability
import Common2026.Shannon.AWGNMain
import Common2026.Shannon.AWGNF1Discharge
import Common2026.Shannon.DifferentialEntropy
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.IdentDistrib
-- 追加 import は Phase 0 inventory + Phase 着手時 loogle で確定
```

## 依存関係 (Mathlib + Common2026 既存)

完了済 / 利用可:

- 親 AWGN 4 file (`AWGN.lean` 275 / `AWGNAchievability.lean` 93 / `AWGNConverse.lean`
  94 / `AWGNMain.lean` 107) + `AWGNF1Discharge.lean` 148 (F-4 done)
- Mathlib `Probability.Distributions.Gaussian.Real` + `.Multivariate` + `.Basic`
- `Common2026/Shannon/DifferentialEntropy.lean` (entropy + max-entropy)
- `Common2026/Shannon/ChannelCoding.lean` (`Code.errorProbAt`, `averageErrorProb`)
- `Common2026/Shannon/AEP.lean` (discrete AEP の schema 参考のみ、continuous 直 reuse 不可)

**Phase 0 で裏取り必要**:

- `Measure.pi (gaussianReal 0 σ²)` の型クラス自動推論
- `Measure.pi_indep` 系 lemma (codewords IndepFun)
- `(p ⊗ₘ W^{⊗n}).rnDeriv (volume.prod volume)` の closed form
- n-dim Gaussian SLLN / WLLN (Mathlib `MeasureTheory.LLN` 系) — **T-2 採用判断の根拠**
- `MeasureTheory.exists_le_of_integral_le_...` 系 (expurgation 用)
- `Argmin` / `Set.indicator` 系の measurability (decoder 用)

## Phase 0 — Mathlib + Common2026 API 在庫 📋

### スコープ

`docs/shannon/awgn-achievability-typicality-mathlib-inventory.md` 新規 (~300-500 行
MD)。本 plan 固有の 5 軸 (codebook 測度 / continuous AEP / union bound / expurgation
/ 球殻 volume) について Mathlib + Common2026 在庫を **per-lemma 構造化形式** で裏取り
(CLAUDE.md「Subagent Inventory of Mathlib Lemmas」: `file:line` + 完全 signature +
`[...]` type-class verbatim + 結論形 verbatim 厳守)。

### Done 条件

- [ ] inventory file 新規作成
- [ ] 5 軸ごとに「既存 / 部分既存 / 不在」を判定
- [ ] **判断 #1 (T-2 採用 or 不採用)** — Mathlib に n-dim Gaussian AEP が無いと
  確認できたら T-2 採用 (`IsContinuousAEPGaussian` hyp 化)
- [ ] **判断 #2 (codebook 測度 type)** — `Measure.pi` 2 段 vs `EuclideanSpace`
  flatten、Mathlib AEP 在庫の入力形に合わせる
- [ ] **判断 #3 (typical set 定義形)** — `rnDeriv` / `differentialEntropy` / `klDiv`
  のいずれの形で書くか、Phase B/C bound の結論形に合わせる

### proof-log

no (inventory MD のみ)。

### 工数感

0.5-1 session。失敗時 fallback: inventory を軸別 file に分割。

---

## Phase A — `gaussianCodebook` 測度 + IndepFun 📋

### スコープ

`Common2026/Shannon/AWGNAchievabilityDischarge.lean` 新規作成 (skeleton + Phase A
本体)。

- A-0 skeleton write (Phase A-E 全主定理を `:= by sorry` で並べる)
- A-1 `gaussianCodebook M n σ² : Measure (Fin M → Fin n → ℝ)` 定義 (判断 #2 適用)
- A-2 `IsProbabilityMeasure` instance
- A-3 各 codeword の marginal が i.i.d. Gaussian
- A-4 異なる codeword `IndepFun`
- A-5 (optional) power constraint の確率版 (Phase D の前段)

### 入出力型 (key)

```lean
noncomputable def gaussianCodebook (M n : ℕ) (σ² : ℝ≥0) :
    Measure (Fin M → Fin n → ℝ)

instance : IsProbabilityMeasure (gaussianCodebook M n σ²)

theorem gaussianCodebook_codeword_law (M n : ℕ) (σ² : ℝ≥0) (m : Fin M) :
    (gaussianCodebook M n σ²).map (· m) = Measure.pi (fun _ : Fin n => gaussianReal 0 σ²)

theorem gaussianCodebook_indepFun_codewords (M n : ℕ) (σ² : ℝ≥0)
    {m m' : Fin M} (hmm' : m ≠ m') :
    IndepFun (fun c => c m) (fun c => c m') (gaussianCodebook M n σ²)
```

### 必要 Mathlib API / Common2026 既存補題

- `Measure.pi` + `Measure.pi.instIsProbabilityMeasure` (Phase 0 で確定)
- Mathlib `Measure.pi_indep` / `iIndepFun.pi` 系 (lemma 名は Phase 0)
- `gaussianReal` + `instIsProbabilityMeasureGaussianReal` (既存)

### Done 条件

- [ ] `AWGNAchievabilityDischarge.lean` 新規作成、skeleton 全 sorry で type-check
- [ ] A-1 ~ A-4 本体 0 sorry、Phase B-E は sorry 残し OK
- [ ] `lake env lean Common2026/Shannon/AWGNAchievabilityDischarge.lean` clean
- [ ] 判断ログ #4 (codebook 型詳細 + Mathlib lemma 名) append

### proof-log

yes (`proof-log-awgn-typicality-phaseA.md`)。

### 工数感

~80-150 行、1-2 session。

### 失敗時 fallback

- 2 段 `Measure.pi` の型クラス壁 → T-1 で `EuclideanSpace` flatten (判断ログ更新)
- `IndepFun` lemma 不在 → `Kernel.iIndep` 経由手書き +30 行

---

## Phase B — Continuous joint-typical set + AEP 3 bounds 📋

### スコープ

Cover-Thomas 9.2 の解析の核心。Phase 0 判断 #1 に従って T-2 採用 or 直接 discharge。

**T-2 採用時 (Mathlib n-dim AEP 不在を確認した場合、最有力)**:

- B-0 `IsContinuousAEPGaussian P N` predicate 定義 (3 つの AEP bound を 1 つの
  bundle に packing、honesty 規律で type ≠ 結論 + docstring 明示)

**T-2 不採用時 (Mathlib AEP を本物に流用できる場合)**:

- B-1 `continuousJointTypical P N ε n : Set (ℝⁿ × ℝⁿ)` 定義 (判断 #3 適用)
- B-2 AEP bound 1: `P[typical] → 1` (1-d SLLN を coordinate-wise + union bound)
- B-3 AEP bound 2: `|typical|_Leb ≤ exp(n(h+ε))` (differentialEntropy 経由)
- B-4 AEP bound 3: indep marginal の typical pair 確率 ≤ `exp(-n(I-3ε))`

### 入出力型 (key、T-2 採用時)

```lean
/-- **Continuous AEP for n-dim Gaussian under AWGN** (Mathlib gap predicate).
NOT load-bearing for achievability — the codebook + union bound + expurgation
core is genuinely discharged in Phase C-D. This predicate only packages the 3
classical AEP bounds whose direct Lean discharge is blocked by the absence of
n-dim Gaussian SLLN in Mathlib (see Phase 0 inventory §B). -/
def IsContinuousAEPGaussian (P : ℝ) (N : ℝ≥0) : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
      (… joint prob ≥ 1 - ε …) ∧
      (… volume ≤ exp(n*(h+ε)) …) ∧
      (… indep-product prob ≤ exp(-n*(I-3ε)) …)
```

正確な statement は Phase 0 判断 #3 + Phase B 着手時に確定。

### 必要 Mathlib API

- Mathlib `MeasureTheory.LLN` (1-d SLLN、coordinate-wise 起動の base)
- `differentialEntropy_gaussianReal` (既存)
- `gaussianReal_conv_gaussianReal` (joint output law)
- (B-4 のみ) Markov-type 不等式 (`MeasureTheory.lintegral_le_meas` 等)

### Done 条件

- [ ] T-2 採用なら B-0 のみ、不採用なら B-1 ~ B-4 全 publish
- [ ] `lake env lean ...` clean
- [ ] 判断ログ #5 (T-2 採用結果 + AEP bound 3 本の状況) append

### proof-log

yes (`proof-log-awgn-typicality-phaseB.md`)。

### 工数感

- T-2 採用: ~50 行 (B-0 のみ)、1 session
- T-2 不採用: ~200-400 行 (B-1 ~50 + B-2 ~150 + B-3 ~80 + B-4 ~80)、2-3 session

### 失敗時 fallback

- B-2 ~ B-4 のいずれか個別に壁 → 該当 bound のみ hyp 化 (T-2 の細分版)
- Phase B 全体 400 行超 → T-4 で本 plan を 2 分割

---

## Phase C — Random coding error bound (union bound) 📋

### スコープ

Phase A の codebook + Phase B の AEP (or hyp) を結んで average error bound を構築:

```
P_avg(error | w=1)
  ≤ P[(X(1), Y) ∉ A_ε]                          -- AEP bound 1 で δ_n
  + ∑_{m=2}^M P[(X(m), Y) ∈ A_ε]                 -- AEP bound 3 で M-1 倍
  ≤ ε + (M-1) · exp(-n(I-3ε))
  ≤ 2ε                                           -- M ≤ exp(n(I-4ε)) と n 大
```

### 入出力型 (key)

```lean
/-- Joint typical decoder: pick the unique m with (X(m), y) typical. -/
noncomputable def jointTypicalDecoder
    (P : ℝ) (N : ℝ≥0) (ε : ℝ) (n M : ℕ)
    (codebook : Fin M → Fin n → ℝ) : (Fin n → ℝ) → Fin M

theorem jointTypicalDecoder_measurable …

theorem awgn_avg_error_union_bound
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_aep : … {- T-2 採用なら IsContinuousAEPGaussian -})
    (R ε : ℝ) (hR : R < (1/2) * Real.log (1 + P / N)) (hε : 0 < ε) :
    ∃ N₀, ∀ n ≥ N₀, ∀ M ≤ Nat.ceil (Real.exp (n*R)),
      ∫⁻ codebook, … avg_error … ∂(gaussianCodebook M n …) ≤ ENNReal.ofReal (2*ε)
```

### 必要 Mathlib API / Common2026 既存

- Phase B の `IsContinuousAEPGaussian` (T-2 採用) or AEP 3 bound (不採用)
- `MeasureTheory.measure_iUnion_le` / `Finset.sum_le_card_nsmul`
- `Real.exp` 単調性 + `Real.log` 算術 (`R < C` から指数の絶対値関係)
- `awgnChannel`, `AwgnCode`, `Code.errorProbAt` (既存)
- decoder measurability: `Set.indicator` + `argmin_set` (Phase 0 確定)

### Done 条件

- [ ] union bound 本補題 publish (T-2 採用なら `h_aep` 引数経由)
- [ ] decoder measurability proof 完了
- [ ] `lake env lean ...` clean

### proof-log

yes (`proof-log-awgn-typicality-phaseC.md`)。

### 工数感

~100-150 行 (decoder ~30 + bound ~100)、1-2 session。

### 失敗時 fallback

- 和不等式 plumbing で型整合崩れ → 手書き chain +30 行
- decoder measurability の壁 → 判断ログで決定論的 fallback (e.g., `Classical.choice`
  使用、measurability 別途 hyp 化)

---

## Phase D — Expurgation 📋

### スコープ

Phase C の average bound から個別 codebook の存在を抽出 + power constraint との
合成 + `AwgnCode` 型への変換。

- D-1 `E_codebook[Pe] ≤ 2ε ⇒ ∃ codebook with Pe ≤ 2ε`
- D-2 throw away worst half (`Pe_avg ≤ 2ε ⇒ ∃ subcodebook with max Pe ≤ 4ε`)
- D-3 power constraint への bridge (Phase A-5 の確率版 + D-1/D-2 を結ぶ)

### 入出力型 (key)

```lean
theorem awgn_exists_codebook_le_avg
    {M n : ℕ} (h_avg : ∫⁻ c, Pe c ∂(gaussianCodebook M n σ²) ≤ ENNReal.ofReal (2*ε)) :
    ∃ c_specific : Fin M → Fin n → ℝ, Pe c_specific ≤ 2*ε

theorem awgn_expurgate_worst_half {M n : ℕ} (h_avg : … Pe_avg ≤ 2*ε) :
    ∃ (M' : ℕ) (subcodebook : Fin M' → Fin n → ℝ),
      M' = M / 2 ∧ ∀ m, individual_error m ≤ 4*ε

-- 最終 bridge: 個別 codebook + power constraint → AwgnCode
theorem awgn_extract_AwgnCode … : ∃ c : AwgnCode (M/2) n P, …
```

### 必要 Mathlib API

- `MeasureTheory.exists_le_of_integral_le_of_isProbabilityMeasure` 系 (Phase 0 で
  確定。不在なら T-3 手書き)
- `Finset` 順序統計 (`Finset.exists_max` 等、半分の throw away)
- `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` 系 (power constraint の確率評価)

### Done 条件

- [ ] D-1 ~ D-3 publish
- [ ] `lake env lean ...` clean

### proof-log

yes (`proof-log-awgn-typicality-phaseD.md`)。

### 工数感

~50-80 行、1 session。

### 失敗時 fallback

- T-3 採用で D-1 手書き ~30 行
- power constraint の確率評価が肥大 → D-3 を Phase A-5 と統合して再構成

---

## Phase E — 統合 + main wrapper 📋

### スコープ

Phase A-D を組み立てて `isAwgnTypicalityHypothesis` 完成、wrapper を publish。

- E-1 `isAwgnTypicalityHypothesis` 本体 (Phase A-D 補題を順に invoke)
- E-2 `awgn_achievability_F1_discharged` (親 `awgn_achievability` の `h_typicality`
  を埋める薄い wrapper)
- E-3 `awgn_theorem_F1F4_discharged` (主定理 wrapper、残 hyp は F-2 + F-3)

### Done 条件

- [ ] E-1 ~ E-3 publish
- [ ] T-2 採用なら最終 signature に `IsContinuousAEPGaussian` 1 hyp が残る (regularity 限定)
- [ ] T-2 不採用なら hyp なし完全 discharge
- [ ] `lake env lean Common2026/Shannon/AWGNAchievabilityDischarge.lean` clean
  (0 sorry / 0 warning)

### proof-log

no (整地のため)。

### 工数感

~30-50 行、0.5 session。

---

## Phase V — verify + Common2026.lean 編入準備 📋

### スコープ

最終 verify + honesty 再 audit + Common2026.lean 編入位置確定。

### Done 条件

- [ ] `lake env lean Common2026/Shannon/AWGNAchievabilityDischarge.lean` silent
- [ ] **honesty 再 audit** (`scripts/audit_db.ts`): T-2 採用時の
  `IsContinuousAEPGaussian` が **regularity hyp** (NOT conclusion-as-hypothesis)
  と判定される
- [ ] `Common2026.lean` に 1 行追加 (オーケストレータ実施):
  ```lean
  import Common2026.Shannon.AWGNAchievabilityDischarge
  ```

### proof-log

no。

### 工数感

0.25 session。

---

## 撤退ライン

### Scope 縮小ライン

- **T-1: `Measure.pi` 型クラス壁** (Phase A-1)
  - 縮退案: `EuclideanSpace ℝ (Fin (M*n))` flatten + `stdGaussian` 流用
  - 判定: Phase 0 判断 #2

- **T-2: continuous AEP for n-dim Gaussian の Mathlib 不在** (Phase B、**最有力**)
  - 縮退案: `IsContinuousAEPGaussian P N` を **regularity hyp** として外出し、
    achievability core (codebook + union bound + expurgation) は本物 discharge
    のまま publish。parallel-gaussian / EPI と同型 staged pattern。
  - **honesty 必須条件**: (a) 結論型と異なる、(b) docstring で "Mathlib gap, NOT
    load-bearing" 明記、(c) Phase C-D で achievability core が genuinely discharge
    されている
  - 判定: Phase 0 判断 #1

- **T-3: expurgation lemma の Mathlib 不在** (Phase D-1)
  - 縮退案: `by_contra` 経由 ~30 行手書き
  - 判定: Phase 0 inventory

- **T-4: 全体 700 行超 + Phase B/D の壁同時発生**
  - 縮退案: 本 plan を 2 分割
    - `awgn-achievability-typicality-aep-plan.md` (Phase A + B)
    - `awgn-achievability-typicality-coding-plan.md` (Phase C + D + E)

### honesty 撤退ライン (常時)

本 plan の goal は `IsAwgnTypicalityHypothesis` を analytic discharge に置換する
こと。以下の rebrand は本 plan の **失敗**:

- ❌ name laundering (`IsAwgnTypicalityHypothesis_with_M_bounds` 等の別名 passthrough)
- ❌ T-2 採用時の `IsContinuousAEPGaussian` 中身が conclusion-as-hypothesis
  (`∃ N₀, ∀ n, ∃ codebook, ∀ m, errorProb < ε`) を含む
- ❌ Phase E の `awgn_theorem_F1F4_discharged` 本体が `h_aep …` 1 行に縮退
  (Phase A-D が integrate されていない)

CLAUDE.md「検証の誠実性」tells、`scripts/audit_db.ts` 再 audit で機械的に検出。

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **n-dim Gaussian AEP の Mathlib 不在** | **高** | **中** (T-2 採用、achievability core は genuine) | Phase 0 inventory で確定、T-2 撤退ライン |
| **`Measure.pi` 型クラス整合** (Phase A) | 中 | 中 | T-1 で EuclideanSpace flatten |
| **`(p ⊗ₘ W^{⊗n}).rnDeriv` の Mathlib-shape mismatch** (Phase B) | 中 | 中 (typical set 定義書き直し +30-50 行) | Phase 0 判断 #3 で結論形に合わせて定義 |
| **expurgation lemma 不在** (Phase D-1) | 中 | 低 (T-3、+30 行) | Phase 0 で確定 |
| **decoder measurability** (Phase C-1) | 中 | 中 (Phase C +20-40 行) | Phase 0 で `argmin_set` measurability を inventory |
| **全体 500 行超過** | 中 (T-2 不採用なら確定) | 中 | T-4 で 2 分割 |
| **honesty defect 混入** (T-2 採用時の rebrand 等) | 低-中 | **高** (plan goal 失う) | §「honesty 撤退ライン」3 条件、Phase V re-audit |

---

## 親 plan / 兄弟 plan との scope 区別

| Plan | スコープ | 出力 | 状態 |
|---|---|---|---|
| `awgn-moonshot-plan.md` (親) | T2-A 全体 (capacity + achiev + converse + main) | AWGN.lean + 3 sibling | DONE (4 撤退ライン honest pass-through) |
| `awgn-f1-discharge-moonshot-plan.md` (兄弟) | **F-4** (kernel measurability、seed 名 F-1) | AWGNF1Discharge.lean (148) | DONE |
| **本 plan** | **F-1** (typicality / achievability core) | AWGNAchievabilityDischarge.lean (~500) | **起草中** |
| `awgn-mi-bridge-plan.md` (未起草、兄弟) | F-2 (MI bridge) | TBD | 未起草 |
| `awgn-converse-aux-plan.md` (未起草、兄弟) | F-3 (per-letter integrability) | TBD | 未起草 |

**重要**: `awgn-f1-discharge-moonshot-plan.md` は seed の番号体系で「F-1」と呼ばれ
ていたが、親 plan の番号体系では **F-4** (kernel measurability)。本 plan は親 plan
の番号体系の **F-1** (typicality)。完全に別物 — 一方の完了は他方に影響しない。
本 plan 完了後も親主定理 signature に F-2 + F-3 hyp が残る (それぞれ別 plan で
順次 discharge 予定)。

---

## オーケストレータ注記

- 実装 agent は `Common2026.lean` を編集しない (Phase V でオーケストレータが 1 行追加)
- 実装 agent はコミットしない (Phase 単位で orchestrator が commit + push)
- **Phase 0 で T-2 採用判断を確定**してから Phase A 着手。判断ログ #1 必須
- **Phase B が最大の山場**。T-2 採用なら ~50 行、不採用なら ~200-400 行
- Phase 単位 proof-log は実装 agent が `docs/shannon/` 直下に append
  (Phase A-D: yes、Phase E/V: no)
- **honesty 再 audit**: Phase V で `scripts/audit_db.ts` 等で T-2 採用時の中間 hyp
  が regularity 判定されることを確認。defect 混入時は §「honesty 撤退ライン」に従い
  再起草

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- Phase 着手時に append される予定の judgement log (現時点では未確定、skeleton):

### #1 (YYYY-MM-DD) Phase 0 完了時、T-2 (n-dim Gaussian AEP の hyp 化) 採用 or 不採用

Phase 0 inventory で Mathlib `MeasureTheory.LLN` の n-dim Gaussian 適用在庫を確認。
在庫有 → 不採用 (本物 discharge)。在庫無 → 採用 (`IsContinuousAEPGaussian P N`
regularity hyp で外出し、achievability core は Phase C-D で genuine 維持)。

### #2 (YYYY-MM-DD) Phase 0 完了時、codebook 測度 type

`Measure.pi` 2 段形 vs `stdGaussian (EuclideanSpace ℝ (Fin (M*n)))` flatten。
Mathlib AEP 在庫 (#1) の入力形に合わせる。

### #3 (YYYY-MM-DD) Phase 0 完了時、typical set 定義形

`rnDeriv` 形 vs `differentialEntropy` 形 vs `klDiv` 形。Phase B/C bound の結論形に
合わせる (Mathlib-shape-driven, CLAUDE.md)。

### #4 (YYYY-MM-DD) Phase A 完了時、`gaussianCodebook` 詳細

採用 type と Mathlib lemma 名 (`Measure.pi_indep` 系 / `iIndepFun` 系) 確定。

### #5 (YYYY-MM-DD) Phase B 完了時、AEP bound 3 本の状況

T-2 採用なら predicate のみ、不採用なら 3 bound 本物 discharge の達成状況。
-->

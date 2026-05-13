# Rate-distortion theorem achievability ムーンショット計画 🌙

(E-3 / [docs/moonshot-seeds.md](../moonshot-seeds.md), 2026-05-13 起草)

> Cover-Thomas 10.5 achievability 半分。`R(D) := inf {I(X; X̂) : 𝔼 d(X, X̂) ≤ D}`
> を新規定義し、`R > R(D) ⟹ ∃ code, 𝔼 d(X, X̂) ≤ D + ε` を formalize する。
> Random codebook + joint typical encoder を **lossy mirror** で構成し、既存
> `Common2026/Shannon/ChannelCodingAchievability.lean` (1890 行) の
> `codebookMeasure` + Fubini-collapse 補題群 (`codebook_marginal_one` /
> `codebook_marginal_two` / `random_codebook_average_le`) を流用する。
> **最難関シード** (見積 ~2000 行 / 4-6 週)。

## 進捗

- [ ] Phase 0 — 経路選択 + Codebook 機構の流用 vs 抽出判断 📋
- [ ] Phase A — 定義 (`distortion`, `expectedDistortion`, `LossyCode`, `R(D)`) 📋
- [ ] Phase B — Joint typical lossy encoder + decoder 📋
- [ ] Phase C — Random codebook + probabilistic method (codebookMeasure lossy mirror) 📋
- [ ] Phase D — Error event analysis (Cover-Thomas 10.5 (10.85) bound) 📋
- [ ] Phase E — 主定理 `rate_distortion_achievability` 📋

## ゴール / Approach

**最終定理 (Cover-Thomas Theorem 10.5 achievability 半分)**:

任意の i.i.d. source `X^n ∼ P_X^n` と単一文字 distortion `d : α → β → ℝ≥0`
について、`R > R(D)` ならば各 `ε > 0` に対し十分大きな `n` で
ある `(2^{nR}, n)`-lossy code `(f : α^n → Fin M, g : Fin M → β^n)` が存在し、
`𝔼[d^n(X^n, g(f(X^n)))] ≤ D + ε`。
ここで `R(D) := inf {I(X; X̂) : (X, X̂) joint with marginal X = P_X, 𝔼 d(X, X̂) ≤ D}`。

### Approach (経路、3 段)

**1. R(D) を「sup of test channel I」 vs 「inf over joint dist」のどちらで定義するか**:
Cover-Thomas は textbook 形 `R(D) := inf_{p(x̂|x): 𝔼 d ≤ D} I(X; X̂)` (条件分布側
の inf)。Lean では **joint dist `q ∈ stdSimplex ℝ (α × β)` 側で書く方が短い**:
- 制約集合 `RDConstraint P_X D := {q : stdSimplex ℝ (α × β) | q.fst = P_X ∧ ∑ a b, q(a,b) · d(a,b) ≤ D}`
- `rateDistortionFunction P_X D := iInf_{q ∈ RDConstraint} I(q)`
  (`I(q) := mutualInfo` of `q` viewed as joint dist on `α × β`)。
- 利点: `stdSimplex ℝ (α × β)` は finite-dim compact + convex、`I` は連続、constraint は
  linear (`q.fst = P_X` も `∑ q(a,b) g_i(a,b) = c_i` も linear)。
  - 既存 `Common2026/Shannon/CsiszarProjection.lean` の `stdSimplex` machinery
    (`isCompact_of_subset_stdSimplex`、`Convex` / `IsClosed` の plumbing) が直接
    使える。
  - **shape-driven**: `RDConstraint` を closed convex subset として書けば
    `IsCompact.exists_isMinOn` で **inf が達成される** ことを E-6 と同じ pattern で
    取得 (Phase A.5)。

**2. 経路 (本 plan 採用)**: Cover-Thomas 10.5 流の random codebook + joint typical
encoder の **lossy mirror**:
- codebook `c : Fin M → β^n` (β 側、reconstruction 側) を i.i.d. random
  with marginal `Q* := argmin I(q)` の reconstruction marginal `q.snd` から
  生成。具体的には `Q^n := Measure.pi (fun _ : Fin n => q*.snd)`。
- encoder `f(x^n) := first m such that (x^n, c(m)) ∈ jointlyTypicalSet`、
  存在しなければ任意の fallback (e.g., `m = 0`)。
- decoder `g(m) := c(m)`。
- error event `E := {no m makes (x^n, c(m)) typical}` ⟹ distortion bounded by
  `D + ε` on `E^c`、`d_max` on `E`、確率 `P(E) → 0`。

**3. 横断観察 (オーケストレータ指示)**: `ChannelCodingAchievability.lean` の
`codebookMeasure p M n := Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))`
+ Fubini-collapse 補題 (`codebook_marginal_one` / `codebook_marginal_two` /
`random_codebook_E1_swap` / `_E2_swap`) は **encoder の選択 vs decoder の選択**
の差を modulo して **lossy source code に対称的に転用可**。
- 採用形: `codebookMeasure q*.snd M n` (codebook 上の law を `β^n` の i.i.d. に
  置き換え)、ambient `μ := Measure.pi (P_X)^n` (source 側 i.i.d.)。
- ChannelCoding では (codebook 側 = X-input、ambient 側 = (X, Y) joint) の
  marginal coupling だった。E-3 では (codebook 側 = β reconstruction、
  ambient 側 = X source) で **marginal coupling は不要**: encoder の random
  codebook 側を `β^n` の i.i.d.、ambient を source `α^n` i.i.d.、両者は独立
  (= joint dist `P_X^n ⊗ Q_n` 形)、joint typicality は `(x^n, c(m))` で
  `q*` 形を取る。

### 経路の代替案と却下理由

1. **(却下) 直接 `R(D) := sup_{p(x̂|x)} I` 形**: テキストの「test channel」形は
   conditional dist 側に inf を取るが、Lean では `Kernel α β` を `stdSimplex` 形に
   transport する plumbing が ~200 行余分。joint dist 側で `q.fst = P_X` の linear
   constraint を立てれば等価で、stdSimplex machinery 再利用可。
2. **(却下) Strong typicality (E-7) joint form**: textbook 10.5 は weak (entropy-typical)
   joint set 経由が標準。`StrongTypicality.lean` (614 行) を joint 化する追加 plumbing
   200-400 行が overhead。本 plan は **既存 weak joint typical set
   (`jointlyTypicalSet`)** をそのまま流用。
3. **(却下) Encoder の確率測度を立てない (deterministic enumeration)**: channel
   coding (B-3) で `(C2) concrete pigeonhole` を最初に試して結局 `codebookMeasure`
   に切り替えた経緯 (B-3 親 plan 判断ログ #5 / B-3'' R1 fallback)。本 plan は
   最初から probabilistic method `codebookMeasure` 形で commit。

### 規模見積

| Phase | 内訳 | 行数見積 |
|---|---|---|
| Phase 0 | 経路選択 + 流用 vs 抽出判断、inventory | ~80 |
| Phase A | 定義 (`distortion`, `expectedDistortion`, `LossyCode`, `R(D)` + `R(D)` 達成性) | ~300 |
| Phase B | Joint typical lossy encoder + decoder + 1 codeword fail prob bound | ~400 |
| Phase C | Random codebook + probabilistic method (codebookMeasure lossy mirror + Fubini) | ~500 |
| Phase D | Error event analysis ((10.85) bound: `M · (1 - p_typ)^M → 0`) | ~300 |
| Phase E | 主定理 `rate_distortion_achievability` 組立 | ~250 |
| precursor (Mathlib gap が出た場合) | 60–250 (e.g. iInf 達成性、stdSimplex 上 MI 連続性) | ~150 |
| **合計** | | **~1980** |

## Phase 0 — 経路選択 + Codebook 機構の流用 vs 抽出判断 📋

### 流用方針

**採用: (B) `ChannelCodingAchievability.lean` を import + 黒箱再利用、抽出しない**:
- `codebookMeasure` は alphabet が `α` か `β` か (source / reconstruction) に
  依存しないため、E-3 では `codebookMeasure q*.snd M n : Measure (Fin M → Fin n → β)`
  形でそのまま呼べる。
- `codebook_marginal_one` / `codebook_marginal_two` は **i.i.d. codebook 上の
  per-row 平均 = single-row 平均** の Fubini collapse で、再利用にはこれら 2 本の
  signature が**`α` polymorphic** であることが前提。本 plan は Phase 0 末で
  signature を verbatim 確認、`Type*` 直してあれば import only、そうでなければ
  precursor refactor (~100 行) で抽出。
- 並立 publish: `Common2026/Shannon/RateDistortionAchievability.lean` を新規作成、
  `Common2026/Shannon/ChannelCodingAchievability.lean` は touch しない。
  B-3'' / B-1' / B-5' / B-8' の前例どおり「親 file 不変 + 子 file 並立」。

### 代替: (A) precursor で `Common2026/Shannon/RandomCodebookProbMethod.lean` を抽出

`ChannelCodingAchievability` 内の private `codebookMeasure` + 3 Fubini-collapse
補題 (~400 行) を独立 file に refactor し、E-1 / E-3 / E-5'-deferred (binning) /
B-3'' から共通 import。

- **採用判断のトリガ**: `codebook_marginal_one` / `codebook_marginal_two` の
  signature が `α` polymorphic でなかった or `Fintype α` 仮定が hard-coded で
  E-3 (β 側 codebook) に直接適用できなかった場合のみ抽出する。
- 抽出するなら ~300-400 行 refactor + B-3'' の reverify cost (`lake build`)。
- Phase 0 の `lake env lean` 実走で signature 確認を済ませて判断。

### Inventory チェックリスト

- [ ] `codebookMeasure` (`ChannelCodingAchievability.lean:239`) の `α` polymorphic 性確認
- [ ] `codebook_marginal_one` / `codebook_marginal_two` (Phase C-(c) 内 private) の signature 確認、`β` 側 codebook での再呼び出し可能性
- [ ] `random_codebook_E1_swap` / `random_codebook_E2_swap` の Fubini structure が
      lossy 側 (encoder 探索失敗 / encoder alias 衝突) の event に流用可能か
- [ ] `IIDProductInput.lean` (399 行) の `iidAmbientMeasure` を **source-only**
      `Measure.pi (fun _ => P_X)` 形に simplify する必要性 (joint distribution
      が不要になる、source 側のみ i.i.d.)

## Phase A — 定義 📋

### A.1 distortion + expectedDistortion

```lean
/-- 単文字 distortion 関数 `d : α → β → ℝ≥0`. -/
abbrev DistortionFn (α β : Type*) := α → β → NNReal

/-- ブロック distortion `d^n((x_i), (y_i)) := (1/n) ∑ d(x_i, y_i)`. -/
noncomputable def blockDistortion {α β : Type*} (d : DistortionFn α β) (n : ℕ)
    (x : Fin n → α) (y : Fin n → β) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (d (x i) (y i) : ℝ)

/-- joint dist `q : α × β → ℝ` 上の 𝔼 d. -/
noncomputable def expectedDistortion
    {α β : Type*} [Fintype α] [Fintype β]
    (d : DistortionFn α β) (q : α × β → ℝ) : ℝ :=
  ∑ a, ∑ b, q (a, b) * (d a b : ℝ)
```

ステップ:
- [ ] A.1.1 `DistortionFn` `abbrev`
- [ ] A.1.2 `blockDistortion` + `blockDistortion_nonneg`
- [ ] A.1.3 `expectedDistortion` + linearity / nonneg

### A.2 LossyCode structure

```lean
structure LossyCode (M n : ℕ) (α β : Type*)
    [MeasurableSpace α] [MeasurableSpace β] where
  encoder : (Fin n → α) → Fin M
  decoder : Fin M → (Fin n → β)
```

`Code` (`ChannelCoding.lean:151`) と **encoder / decoder の値域が逆 + decoder の
codomain が β^n に**: encoder は source `α^n → Fin M`、decoder は `Fin M → β^n`
(reconstruction)。

ステップ:
- [ ] A.2.1 `LossyCode` structure
- [ ] A.2.2 `LossyCode.expectedBlockDistortion μ d c : ℝ` (i.i.d. source `μ`上の
       `𝔼[d^n(X^n, decoder(encoder X^n))]`)
- [ ] A.2.3 `expectedBlockDistortion_le_dmax`: 自明上界

### A.3 RDConstraint + rateDistortionFunction

```lean
/-- 制約集合: `q.fst = P_X` (source marginal) + `∑ q(a,b) d(a,b) ≤ D`. -/
def RDConstraint
    {α β : Type*} [Fintype α] [Fintype β]
    (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) :
    Set (α × β → ℝ) :=
  {q ∈ stdSimplex ℝ (α × β) |
      (fun a => ∑ b, q (a, b)) = P_X ∧
      expectedDistortion d q ≤ D}

/-- R(D) := inf_{q ∈ RDConstraint} I(q). MI は joint pmf `q` から直接. -/
noncomputable def rateDistortionFunction
    {α β : Type*} [Fintype α] [Fintype β]
    (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) : ℝ :=
  ⨅ q ∈ RDConstraint P_X d D, mutualInfoPmf q
```

ここで `mutualInfoPmf q := ∑ a b, q(a,b) · log(q(a,b) / (q.fst a · q.snd b))`
は pmf 直接形 (CsiszarProjection の `klDivPmf` shape をミラー)。
**Mathlib-shape-driven**: `mutualInfoPmf` は MutualInfo.lean の
`InformationTheory.Shannon.mutualInfo (P : Measure (α × β))` と等価だが、
`stdSimplex ℝ (α × β)` 上で書くと連続性 / 凸性が直接取れる。

ステップ:
- [ ] A.3.1 `RDConstraint` 定義 + `IsClosed` / `Convex` (linear constraints)
- [ ] A.3.2 `RDConstraint_isCompact` (E-6 の `isCompact_of_subset_stdSimplex` 直
       適用)
- [ ] A.3.3 `RDConstraint_nonempty`: trivially `(P_X(a) · 𝟙[b = b₀])` (constant
       reconstruction) は constraint を満たす一定範囲の `D` で in、または
       `D ≥ D_max` で全て in
- [ ] A.3.4 `rateDistortionFunction` 定義 + `mutualInfoPmf` 連続性
       (`MutualInfo.lean` `klDiv_compProd_eq_add` の pmf 形)
- [ ] A.3.5 `rateDistortionFunction_attained`:
       `∃ q* ∈ RDConstraint, mutualInfoPmf q* = R(D)` (`IsCompact.exists_isMinOn`)
- [ ] A.3.6 `rateDistortionFunction_nonneg`、`rateDistortionFunction_antitone` (`D`
       増 ⟹ `R(D)` 減、constraint 集合の単調性)

### A.5 自然性 lemma (使う分だけ)

- [ ] `rateDistortionFunction_lt_iff`: `R(D) < r ↔ ∃ q ∈ RDConstraint, mutualInfoPmf q < r`
- [ ] `RDConstraint.fst_eq_PX`: marginal 取り出し
- [ ] `mutualInfoPmf_eq_mutualInfo_of_pmf`: pmf 形 ↔ Measure 形 bridge

## Phase B — Joint typical lossy encoder + decoder 📋

### B.1 lossy encoder + decoder skeleton

```lean
/-- 与えられた codebook `c : Fin M → β^n` に対し joint-typicality 探索 encoder.
fallback は `⟨0, hM⟩`. -/
noncomputable def jointTypicalLossyEncoder
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β) :
    (Fin n → α) → Fin M := fun x =>
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  if h : ∃ m : Fin M, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε
    then Classical.choose h else ⟨0, hM⟩

noncomputable def lossyCodeOfCodebook
    ... : LossyCode M n α β where
  encoder := jointTypicalLossyEncoder μ Xs Ys hM ε c
  decoder := c
```

注: ChannelCoding の `jointTypicalDecoder` (decoder 側、unique match) と異なり、
こちらは encoder 側で **first match**。unique 要求は不要 (任意の typical-match
で `d^n` は ε 制御下に入る)。

ステップ:
- [ ] B.1.1 `jointTypicalLossyEncoder` definition
- [ ] B.1.2 `lossyCodeOfCodebook` bundling
- [ ] B.1.3 `encoder_returns_typical_match_iff` (Classical.choose の spec)

### B.2 distortion bound on `E^c`

- [ ] B.2.1 `mem_jointlyTypicalSet_implies_blockDistortion_le`:
       `(x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε ⟹
        blockDistortion d n x (c m) ≤ expectedDistortion d (μ.map (jointSequence Xs Ys 0)) + δ`
       (δ は ε 関数、Cover-Thomas 3.5 流の "joint typical sequences have empirical
       distortion close to expected" 補題)。
- [ ] B.2.2 `single_codeword_typical_match_prob`:
       random codebook 上 `P[∃ m, (x, c m) ∈ jointlyTypicalSet] ≥ 1 - (1 - p_typ)^M`
       (single-codeword fail prob `(1 - p_typ)^M`、`p_typ` は Phase B-(c)
       `jointlyTypicalSet_indep_prob_le` の逆方向 lower bound)。

**Mathlib gap**: B.2.1 (joint typical ⟹ empirical 距離 ≤ 期待値) は新規補題。
`jointlyTypicalSet` の定義 (`mem_jointlyTypicalSet_iff`, ChannelCoding.lean:311)
が entropy-typical 3 条件のみで、empirical mean は明示的に含まれない。**経路**:
- (a) `jointlyTypicalSet` の定義を **拡張**: 4 条件目「empirical d ≤ 𝔼 d + δ」追加。
      ⟹ ChannelCoding.lean の改変必要、**却下**。
- (b) 新規 `distortionTypicalSet d μ Xs Ys n ε := jointlyTypicalSet μ Xs Ys n ε ∩
      {(x, y) | blockDistortion d n x y ≤ 𝔼 d + δ_ε}` を定義し、Phase B-(c)
      `jointlyTypicalSet_indep_prob_le` の **slightly 改変版**を新規。これは
      `iIndepFun (d ∘ jointSequence)` + WLLN で `n → ∞` で確率 → 1。**採用**。

### B.3 distortionTypicalSet

```lean
/-- `jointlyTypicalSet` に「empirical d ≤ 𝔼 d + δ」条件を交叉した集合. -/
noncomputable def distortionTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε : ℝ) (δ : ℝ) :
    Set ((Fin n → α) × (Fin n → β)) :=
  jointlyTypicalSet μ Xs Ys n ε ∩
    {(x, y) | blockDistortion d n x y ≤ expectedDistortion ... + δ}
```

- [ ] B.3.1 `distortionTypicalSet_prob_tendsto_one`: WLLN on `d(X_i, Y_i)` の和
       + `jointlyTypicalSet_prob_tendsto_one` を `Filter.Tendsto.add` で結合
- [ ] B.3.2 `distortionTypicalSet_indep_prob_le`: Phase B-(c) `jointlyTypicalSet_indep_prob_le`
       を逆向き lower bound (⟹ `≥ 1 - exp(-n(I-3ε)) · (1 - δ_term)`)
       — これは `single_codeword_typical_match_prob` で使う

## Phase C — Random codebook + probabilistic method (lossy mirror) 📋

### C.1 codebook measure (β 側)

`codebookMeasure (q*.snd) M n : Measure (Codebook M n β)`. `ChannelCodingAchievability`
の `codebookMeasure` を `α` polymorphic に流用 (Phase 0 で signature 確認済)。

- [ ] C.1.1 `codebookMeasure` インスタンス確認 (`IsProbabilityMeasure`)
- [ ] C.1.2 `iidAmbientSourceMeasure P_X : Measure (ℕ → α)` を新規追加 (joint
       distribution `Measure.infinitePi (jointDistribution p W)` ではなく、
       source-only `Measure.infinitePi P_X`)。`IIDProductInput.lean` の simplify
       版で ~80 行。

### C.2 random codebook 上の average distortion bound

```lean
theorem random_codebook_avg_distortion_le
    (P_X : Measure α) [IsProbabilityMeasure P_X]
    (q* : α × β → ℝ) (hq* : q* ∈ RDConstraint P_X d D)
    (hq*_min : mutualInfoPmf q* = rateDistortionFunction P_X d D)
    {M n : ℕ} (hM : 0 < M) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) ... :
    ∑ codebook : Codebook M n β,
      (codebookMeasure (Q_snd q*) M n).real {codebook} *
      ((lossyCodeOfCodebook μ Xs Ys hM ε codebook).expectedBlockDistortion P_X).toReal
    ≤ (1 - (1 - p_typ_lower)^M) * (D + δ + δ')
      + (1 - (1 - p_typ_lower)^M)^complement * d_max
```

ここで `p_typ_lower := Real.exp (- (n : ℝ) * (mutualInfoPmf q* + 3 * ε))` は
Phase B (c) lossy mirror 形からの per-codeword fail-not lower bound。

**戦略**: `ChannelCodingAchievability.random_codebook_average_le` の Fubini-collapse
構造を **lossy mirror** で再利用:
- ChannelCoding: ambient = `iidAmbientMeasure p W` on `ℕ → α × β`,
  codebook 上の `Measure.pi p^{Mn}`、E1 / E2 events に decompose。
- E-3: ambient = `Measure.pi P_X` on `ℕ → α`,
  codebook 上の `Measure.pi (q*.snd)^{Mn}`、両者 **独立** (codebook は source
  と独立)。`(x, c(m))` joint distribution = `P_X^n ⊗ (q*.snd)^n` (product) ≠
  `(q*)^n`。Cover-Thomas 10.5 のキー: independent product 上で joint typical
  ⟹ `(M-1)·exp(-n·R(D))` 形を `(1-p_typ)^M` 形に変換。
- 流用補題: `random_codebook_E2_swap` (alias-codeword 衝突確率の Fubini swap、
  本 plan では「encoder 探索成功確率」が dual 形で出る) と
  `codebook_marginal_one` / `_two`。

ステップ:
- [ ] C.2.1 `codebookMeasure_marginal_lossy`: `β^n` polymorphic 版確認 / 抽出
- [ ] C.2.2 `lossy_codebook_no_match_prob_eq` (Fubini swap、`(1 - p_typ)^M` 形):
       random codebook 上の「source x^n に対し全 m で typical match なし」確率
       = `(1 - p_typ_x)^M` (各 m が独立)。
- [ ] C.2.3 source 期待値: `∫ (1 - p_typ_x)^M dP_X^n(x) ≤ (1 - p_typ_avg)^M`
       (Jensen on log, optional) or directly bound by `M · (1 - p_typ_avg)` —
       Cover-Thomas 10.5 (10.85) は `(1-x)^M ≤ exp(-Mx)` 形を使う。
- [ ] C.2.4 main bound: 期待 distortion ≤ `(1 - P(match)) · d_max + P(match) · (D + δ)`,
       both decay/converge appropriately as `n → ∞`.

### C.3 pigeonhole

```lean
theorem exists_codebook_low_distortion
    ... (h_avg : ... ≤ B) :
    ∃ codebook : Codebook M n β,
      ((lossyCodeOfCodebook μ ... codebook).expectedBlockDistortion P_X).toReal ≤ B
```

`ChannelCodingAchievability.exists_codebook_le_avg:1477` の verbatim mirror。
`codebookMeasure` weighted sum 上の classical contradiction。

## Phase D — Error event analysis ((10.85) bound) 📋

Cover-Thomas 10.5 主不等式:
```
P[encoder 失敗] = ∫ (1 - P[(x, C) typical])^M dP_X^n(x)
≤ (1 - exp(-n(I(q*) + 3ε)))^M
≤ exp(-M · exp(-n(I + 3ε)))
```

ステップ:
- [ ] D.1 `(1-x)^M ≤ exp(-Mx)` for `0 ≤ x ≤ 1` (`Real.one_sub_le_exp_neg`、Mathlib
       既存)
- [ ] D.2 `M · exp(-n(I + 3ε)) → ∞` の指数増大: `M = ⌈exp(nR)⌉`, `R > I + 3ε`
       (slack `ε := (R - I)/6` 取得)、`M · exp(-n(I+3ε)) ≥ exp(n·(R - I - 3ε)/2)`
- [ ] D.3 `exp(-M·exp(-n(I+3ε))) → 0` from D.1 + D.2 + `Real.tendsto_exp_neg_atTop_nhds_zero`
- [ ] D.4 distortion expectation decomposition:
       `𝔼[d^n] ≤ P(encoder ok) · (D + δ + δ') + P(encoder 失敗) · d_max`
- [ ] D.5 `n → ∞` 極限: 第 2 項 → 0、第 1 項 → `D + δ + δ'`、ε / δ / δ' を統合
       `≤ D + ε'`

## Phase E — 主定理 📋

```lean
theorem rate_distortion_achievability
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]
    (P_X : Measure α) [IsProbabilityMeasure P_X]
    (hPX_pos : ∀ a : α, 0 < P_X.real {a})
    (d : DistortionFn α β)
    {D : ℝ} (hD_nonneg : 0 ≤ D)
    {R : ℝ} (hR : R > rateDistortionFunction (toFun P_X) d D)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : LossyCode M n α β),
        (c.expectedBlockDistortion P_X d).toReal ≤ D + ε'
```

ステップ:
- [ ] E.1 `R > R(D)` ⟹ `∃ q* ∈ RDConstraint, mutualInfoPmf q* < R` (Phase A.5)
- [ ] E.2 slack `ε := (R - mutualInfoPmf q*) / 6 > 0` 取得
- [ ] E.3 i.i.d. ambient `μ := iidAmbientSourceMeasure P_X` (Phase C.1) +
       `Ys` ambient (random codebook 上の RV としては不要だが、
       `jointlyTypicalSet` の signature 整合用に dummy `Ys`)
- [ ] E.4 Phase C.2 main bound + Phase D 極限 + Phase C.3 pigeonhole で
       `∃ codebook, ... ≤ D + ε'` を結ぶ
- [ ] E.5 `Nat.ceil` の cast plumbing (B-3'' 主定理と同型、verbatim 流用可)

## Mathlib API inventory (loogle 確認、subagent 構造化形式)

### 既存 (流用)

- `IsCompact.exists_isMinOn` (`Mathlib/Topology/Order/Compact.lean`):
  - sig: `(hs : IsCompact s) (ne_s : s.Nonempty) (hf : ContinuousOn f s) :`
    `∃ x ∈ s, IsMinOn f s x`
  - 用途: Phase A.3.5 `rateDistortionFunction_attained`、E-6 と同形式
- `iInf_lt_iff` (`Mathlib/Order/CompleteLattice/Defs.lean`):
  - sig: `⨅ i, f i < a ↔ ∃ i, f i < a` (complete lattice)
  - 用途: Phase A.5 `rateDistortionFunction_lt_iff` (但 `R(D)` が `Real` 値で `iInf`
    は `ConditionallyCompleteLattice`、`ciInf_lt_iff` 系を使う)
- `ciInf_lt_iff` (`Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`):
  - sig: BddBelow 仮定 + nonempty で `⨅ i, f i < a ↔ ∃ i, f i < a`
  - 用途: Phase A.5、conditional complete lattice (Real) 用
- `Real.one_sub_le_exp_neg` (Mathlib):
  - sig: `∀ x : ℝ, 1 - x ≤ Real.exp (-x)`
  - 用途: Phase D.1
- `Real.tendsto_exp_neg_atTop_nhds_zero`:
  - sig: `Filter.Tendsto (fun x => Real.exp (-x)) atTop (𝓝 0)`
  - 用途: Phase D.3

### 既存 Common2026 (流用、verbatim 確認済)

- `Common2026/Shannon/ChannelCoding.lean`:
  - `Channel α β := Kernel α β` (l. 49)
  - `jointlyTypicalSet μ Xs Ys n ε` (l. 301)
  - `mem_jointlyTypicalSet_iff` (l. 311)
  - `jointlyTypicalSet_prob_tendsto_one` (l. 402): `Pairwise … ⟂ᵢ[μ] …` 形仮定
  - `jointlyTypicalSet_indep_prob_le` (l. 573): independent product 上の typical
    集合確率 `≤ exp(-n(I - 3ε))`、本 plan で **lossy version** に転用 (cf. B.3.2)
- `Common2026/Shannon/ChannelCodingAchievability.lean`:
  - `Codebook M n α := Fin M → (Fin n → α)` (l. 70、`α` polymorphic、Phase 0 で再確認)
  - `codebookMeasure p M n := Measure.pi (fun _ => Measure.pi (fun _ => p))` (l. 239)
  - `random_codebook_average_le` (l. 1229): channel coding 形だが Fubini-collapse
    structure は lossy mirror で再利用可。signature 内 private 補題
    `codebook_marginal_one` / `_two` も polymorphic か Phase 0 で要確認
  - `exists_codebook_le_avg` (l. 1477): verbatim mirror で Phase C.3 に再利用
- `Common2026/Shannon/IIDProductInput.lean`:
  - `iidAmbientMeasure p W` (l. 48): joint distribution 上の i.i.d. ambient。本 plan
    では source-only `Measure.infinitePi P_X` 版が必要 (Phase C.1)
- `Common2026/Shannon/MutualInfo.lean`:
  - `mutualInfo` (l. 36): `klDiv ((μ.map (Xs, Yo)) ((μ.map Xs).prod (μ.map Yo)))` 形
  - `mutualInfo_nonneg` (l. 42)
  - `mutualInfo_ne_top` (l. 192)
  - `mutualInfo_comm` (l. 93)
- `Common2026/Shannon/CsiszarProjection.lean`:
  - `stdSimplex` machinery (compactness / closed / convex)
  - `isCompact_of_subset_stdSimplex` (汎用、Phase A.3.2 で直接使用)

### Mathlib gap (新規必要)

- [ ] **Gap 1**: `jointlyTypicalSet` ⟹ `blockDistortion ≤ 𝔼 d + δ` 補題
       (Phase B.2.1): 新規 `distortionTypicalSet` を定義し、`jointlyTypicalSet`
       本体は touch しない (`Common2026/Shannon/ChannelCoding.lean` 不変)。
- [ ] **Gap 2**: `mutualInfoPmf q` (pmf 直接形) と `MutualInfo.mutualInfo
       (joint dist measure)` の bridge: ~80 行、`klDivPmf_eq_log_diff_sum` の MI 対形。
       `Common2026/Shannon/MutualInfo.lean` 拡張 (E-6 CsiszarProjection が
       `klDivPmf` で書いた前例に整合)。
- [ ] **Gap 3**: `iidAmbientSourceMeasure P_X` (source-only) を `IIDProductInput.lean`
       に追加、または **新規** `Common2026/Shannon/IIDSourceInput.lean` (~80 行)。
- [ ] **Gap 4**: `expectedDistortion` の連続性 / 凸性 (Phase A.3.1 で `RDConstraint`
       が closed を取るため、linear functional 連続性は自明)。

## 撤退ライン / 部分完了境界

- **Phase A 完了で commit 可**: `R(D)` definition + 達成性 publish。後段 deferred、
  E-3' / E-3'' 後継 plan に切り出し。E-1 (strong converse) で `R(D)` の rate-distortion
  逆形が出れば再利用価値あり。
- **Phase A + B 完了で commit 可**: 単発 distortion typical set + per-codeword fail
  prob bound 単独 publish。
- **Phase C 完了で commit 可**: random codebook averaging publish。Phase D の
  asymptotic finalize は別 plan。
- **Phase E 完了で commit**: 主定理 publish、E-3 完成。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 例 (起草時、未確定):
1. **Phase 0 で `codebookMeasure` の α polymorphic 性が崩れていた場合**:
   precursor refactor `Common2026/Shannon/RandomCodebookProbMethod.lean`
   抽出に switch、B-3'' (1890 行) の reverify を `lake build` で実走確認。
2. **`R(D)` の定義 shape の最終確定**: `joint dist q ∈ stdSimplex` 形 vs
   `Kernel α β` 形 vs Cover-Thomas textbook conditional dist 形。stdSimplex 採用
   理由 = E-6 `CsiszarProjection.lean` machinery 流用。Kernel 形に switch する場合は
   precursor 補題が ~200 行追加で必要。
3. **`distortionTypicalSet` を `ChannelCoding.lean` の `jointlyTypicalSet` 内に
   merge するか、別 set として並立するか**: 並立採用、`ChannelCoding.lean`
   不変原則 (B-3'' 親 plan 不変 + 子 plan 並立) に整合。
-->

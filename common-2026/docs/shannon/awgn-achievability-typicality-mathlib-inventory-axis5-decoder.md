# AWGN Achievability Typicality — Mathlib inventory **Axis 5: decoder measurability**

> **親 plan**: [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md) Phase C
> (random coding error bound + jointly typical decoder)。
> 本ファイルは Phase 0 inventory のうち **軸 5 (decoder measurability)** 専担。
> 5 軸全体は plan §「Phase 0 — Mathlib + Common2026 API 在庫」を参照。
>
> **担当 scope**: Phase C で構成する `jointTypicalDecoder` 関数 `(Fin n → ℝ) → Fin M` の
> `Measurable` 性。これは Phase C-1 の `awgn_avg_error_union_bound` が
> `Code.errorProbAt` (= `Measure.pi (W ∘ encoder m) (errorEvent m)`) を取るうえで
> `AwgnCode.decoder_meas` を埋めるのに必須。

## 一行サマリ

**`jointTypicalDecoder` の measurability は Mathlib 既存 API のみで完全 discharge 可能。
鍵は `measurable_to_countable'` (codomain が `Fin M` で countable) + `Measurable.exists` /
`Measurable.and` (typicality 述語の組み立て) + `Measurable.indicator` (joint set への
indicator)。自作必要 0 件。Phase C measurability proof は ~15-25 行で済む見込み。**

**最有力**: **Option A** (`Fin.find` decoder + `measurable_to_countable'`)。理由は §「推奨判断」。

---

## Phase C 該当箇所 (再掲)

`docs/shannon/awgn-achievability-typicality-plan.md` Phase C より:

```lean
/-- Joint typical decoder: pick the unique m with (X(m), y) typical. -/
noncomputable def jointTypicalDecoder
    (P : ℝ) (N : ℝ≥0) (ε : ℝ) (n M : ℕ)
    (codebook : Fin M → Fin n → ℝ) : (Fin n → ℝ) → Fin M

theorem jointTypicalDecoder_measurable …

theorem awgn_avg_error_union_bound … : … :=
  -- requires AwgnCode の decoder_meas field を埋める
```

既存の `AwgnCode` 構造 (`Common2026/Shannon/AWGN.lean:97`) が
**`decoder_meas : Measurable decoder` を field として要求** しているので、
Phase D の expurgation で `Fin M → Fin n → ℝ` を `AwgnCode M n P` に持ち上げるには
ここで `Measurable (jointTypicalDecoder …)` を供給する必要がある。

```lean
-- Common2026/Shannon/AWGN.lean:97-102
structure AwgnCode (M n : ℕ) (P : ℝ) where
  encoder : Fin M → (Fin n → ℝ)
  decoder : (Fin n → ℝ) → Fin M
  decoder_meas : Measurable decoder
  power_constraint : ∀ m : Fin M,
    (∑ i : Fin n, (encoder m i)^2) ≤ (n : ℝ) * P
```

---

## API 在庫 (per-lemma 構造化)

### 5.1 Argmin / argmax measurability

#### `Function.argmin` (Mathlib にあるが measurability ラッパは **不在**)

- **file:line**: `Mathlib/Order/WellFounded.lean:159` 周辺 (`WellFounded.min` の wrapper)
- **signature** (verbatim):
  ```lean
  noncomputable def Function.argmin (f : α → β) (h : WellFounded ((· < ·) : β → β → Prop))
      [Nonempty α] : α
  ```
- **type-class prerequisites**: `[Nonempty α]`、結論側に `WellFounded (·<·)` が要る。
- **explicit args**: `f : α → β`, `h : WellFounded (· < · : β → β → Prop)`
- **conclusion**: `α`
- **applicability to 軸 5**: ⚠️ **`Measurable.argmin` lemma は Mathlib 不在**
  (loogle `Found 0 declarations`)。`Function.argmin` は (a) **`WellFounded (·<·) on β`** を要求
  (連続なスコア空間には不向き、`ℝ` の `<` は well-founded ではない)、(b) 一意性ではなく最小化を返す。
  典型的な decoder 設計 (「typical な m が唯一存在すれば返す、なければ任意」) には不適。
  → **decoder には使わない**。

#### `Function.argmin_set_measurable` (Mathlib **不在**)

- loogle 確認: `Found 0 declarations`。`Measurable.argmin` / `argmin_set` / `MeasurableSet.argminSet`
  系の lemma は Mathlib に存在しない。
- → **自作 or 別アプローチ必須**。Option A (`measurable_to_countable'`) で迂回する。

#### `Finset.argmin` / `Finset.argmax` (Mathlib **不在**、`Finset.min` のみあり)

- `Finset.argmin`/`Finset.argmax` は Mathlib に同名定義なし (loogle: `unknown identifier 'Finset.argmin'`)。
- `Finset.min'` / `Finset.max'` は存在 (返り値は要素型自身、index ではない)。

#### List.argmin

- `List.argmin` は `Mathlib/Data/List/MinMax.lean` 存在。`Decidable` instance 経由で computable。
- → 本タスクでは index 取り出しに使えるが、`(Fin n → ℝ) → Fin M` の measurability は
  別途必要 (→ Option A で済むので不要)。

### 5.2 `Set.indicator` + measurability

#### `Measurable.indicator`

- **file:line**: `Mathlib/MeasureTheory/MeasurableSpace/Basic.lean:309`
- **signature** (verbatim):
  ```lean
  @[fun_prop]
  theorem Measurable.indicator [Zero β] (hf : Measurable f) (hs : MeasurableSet s) :
      Measurable (s.indicator f)
  ```
- **type-class prerequisites**: `[Zero β]` (codomain に `0` が要る、`ℝ`/`ℝ≥0∞`/`ℕ` 全部 OK)。
  暗黙の `[MeasurableSpace α]`, `[MeasurableSpace β]` は `f s` の sort から来る。
- **explicit args**: `hf : Measurable f`, `hs : MeasurableSet s`
- **conclusion**: `Measurable (s.indicator f)`
- **applicability to 軸 5**: ✅ 直接 reusable。Option B の場合「`f(m, y) := if (X(m), y) ∈ A_ε then 1 else 0`」
  の measurability を組むのに使う。Option A では使わない (typicality 述語を直接
  `Measurable.and` で組むため)。

#### `MeasurableSet.indicator` (`MeasurableSet → Measurable (indicator)` の別シノニム)

- 上記 `Measurable.indicator` を `f = const 1` に特殊化したものと等価。同 file の周辺に存在。

#### `measurable_indicator_const_iff`

- **file:line**: `Mathlib/MeasureTheory/MeasurableSpace/Basic.lean:315`
- **signature** (verbatim):
  ```lean
  lemma measurable_indicator_const_iff [Zero β] [MeasurableSingletonClass β] (b : β) [NeZero b] :
      Measurable (s.indicator (fun (_ : α) ↦ b)) ↔ MeasurableSet s
  ```
- **type-class prerequisites**: `[Zero β] [MeasurableSingletonClass β]` + `[NeZero b]`。
- **applicability**: indicator の measurability ↔ set の measurability。
  Phase C で `Pe_avg` を integral として書く際、`{(X, Y) ∈ A_ε^{(n)}}` の indicator が
  measurable なら set 自体も measurable、というのが暗黙に必要 (逆も)。

### 5.3 Jointly typical set の MeasurableSet

#### `MeasurableSet.inter` / `MeasurableSet.union` / `MeasurableSet.compl`

- **file:line**: `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:169` (`inter`),
  `:163` (`union`), `:83` (`compl`)
- **signature** (verbatim):
  ```lean
  protected theorem MeasurableSet.compl : MeasurableSet s → MeasurableSet sᶜ
  protected theorem MeasurableSet.union {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
      (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∪ s₂)
  protected theorem MeasurableSet.inter {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
      (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∩ s₂)
  ```
- **type-class prerequisites**: 全て `{m : MeasurableSpace α}` のみ。追加は不要。
- **applicability**: Phase B の `continuousJointTypical` 集合が
  3 つの `|·| < ε` 条件の交差で書けるなら、各条件が measurable であれば全体も measurable。

#### `Measurable.and` / `Measurable.or` / `Measurable.not`

- **file:line**: `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:867` (`and`),
  `:871` (`or`), `:863` (`not`)
- **signature** (verbatim):
  ```lean
  @[fun_prop]
  lemma Measurable.and (hp : Measurable p) (hq : Measurable q) :
      Measurable fun a ↦ p a ∧ q a
  @[fun_prop]
  lemma Measurable.or (hp : Measurable p) (hq : Measurable q) :
      Measurable fun a ↦ p a ∨ q a
  @[fun_prop]
  lemma Measurable.not (hp : Measurable p) : Measurable (¬ p ·)
  ```
- **type-class prerequisites**: `{_ : MeasurableSpace α}` のみ。`p q : α → Prop` は `Bool`
  値ではなく `Prop` 値だが、`measurableSet_setOf` で `Set` に落ちる。
- **applicability**: 「jointly typical な唯一の m」述語
  `Φ(codebook, y, m) := (X(m), y) ∈ A_ε ∧ ∀ m' ≠ m, (X(m'), y) ∉ A_ε`
  を組む際の論理結合子。

#### `Measurable.forall` / `Measurable.exists`

- **file:line**: `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:884` (`forall`),
  `:889` (`exists`)
- **signature** (verbatim):
  ```lean
  @[fun_prop]
  lemma Measurable.forall [Countable ι] {p : ι → α → Prop} (hp : ∀ i, Measurable (p i)) :
      Measurable fun a ↦ ∀ i, p i a
  @[fun_prop]
  lemma Measurable.exists [Countable ι] {p : ι → α → Prop} (hp : ∀ i, Measurable (p i)) :
      Measurable fun a ↦ ∃ i, p i a
  ```
- **type-class prerequisites**: `[Countable ι]`。`Fin M` は当然 `Countable` (`Finite` から `Countable`)。
- **applicability**: ✅ **Option A の中核**。`∃! m, (X(m), y) ∈ A_ε` の述語の measurability を
  `Measurable.exists` + `Measurable.forall` + `Measurable.and` で組む。

#### `Real.measurable_log` / `Measurable.log`

- **file:line (raw)**: `Mathlib/MeasureTheory/Function/SpecialFunctions/Basic.lean:39`
- **file:line (compositional)**: `Mathlib/MeasureTheory/Function/SpecialFunctions/Basic.lean:138`
- **signature** (verbatim, raw):
  ```lean
  theorem measurable_log : Measurable log
  ```
- **signature** (verbatim, compositional, `Real.` namespace 内):
  ```lean
  @[fun_prop]
  protected theorem Measurable.log : Measurable fun x => log (f x)
  ```
  (この `hf : Measurable f` は `variable` で引っ張られている。実態は
  `measurable_log.comp hf`。)
- **type-class prerequisites**: none。`f : α → ℝ` は `variable`、`[MeasurableSpace α]` も同様。
- **applicability**: typical-set 条件
  `|(1/n) · log ((p ⊗ₘ W^{⊗n}).rnDeriv (volume.prod volume) (x, y)) - h(...)| < ε`
  の `log` 部分の measurability。`log 0 = 0` (Mathlib 規約) なので preimage は singleton 0 で
  例外なく measurable。

#### `MeasureTheory.Measure.measurable_rnDeriv`

- **file:line**: `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:100`
- **signature** (verbatim):
  ```lean
  @[fun_prop]
  theorem measurable_rnDeriv (μ ν : Measure α) : Measurable <| μ.rnDeriv ν
  ```
- **type-class prerequisites**: `{m0 : MeasurableSpace α}` のみ (open namespace
  `MeasureTheory.Measure`)。**`HaveLebesgueDecomposition` は不要** (内部 `by_cases` で
  分岐、なければ `0` を返す)。
- **applicability**: typical-set の `rnDeriv` 因子 (Phase 0 判断 #3 で
  `rnDeriv` 形を採用するなら) の measurability。

#### `measurable_gaussianPDFReal` / `measurable_gaussianPDF`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Real.lean:72` (Real-valued),
  `:186` (ENNReal-valued)
- **signature** (verbatim):
  ```lean
  @[fun_prop]
  lemma measurable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
      Measurable (gaussianPDFReal μ v)
  @[fun_prop]
  lemma measurable_gaussianPDF (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPDF μ v)
  ```
- **type-class prerequisites**: none。
- **applicability**: typical-set を `rnDeriv` ではなく **明示的 Gaussian PDF**
  で書く Phase 0 判断 #3 の選択肢を取った場合、joint PDF
  `∏ i, gaussianPDF (X m i) N (y i)` の measurability を組むのに使える。

### 5.4 `Fin M` 上の choice / decision

#### `Fin.find`

- **file:line**: `Mathlib/Data/Fin/Tuple/Basic.lean:1100`
- **signature** (verbatim):
  ```lean
  set_option backward.privateInPublic true in
  set_option backward.privateInPublic.warn false in
  protected def find {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
      (h : ∃ k, p k) : Fin n
  ```
- **type-class prerequisites**: `[DecidablePred p]` + **存在証明 `h : ∃ k, p k`** が **explicit arg**。
- **explicit args**: `p : Fin n → Prop`, `h : ∃ k, p k`
- **conclusion**: `Fin n` (最小の `k` で `p k` を満たすもの)
- **applicability to 軸 5**: ⚠️ **存在証明を毎入力 `y` に依存して与える必要がある**。decoder は
  「typical な唯一 m が無いとき error を返す」必要があるので、`Fin.find` の素朴使用は不適。
  → `Option (Fin M)` 経由か、`Classical.choice` + fallback で迂回 (詳細は推奨判断参照)。

#### `Nat.find` 系

- `Nat.find` は `∃ n, p n` 必須、本タスクには `Fin.find` 同様の制約。
- 派生 `Nat.findX` 等も同じ。

#### `decide` / `Decidable` instance

- `Classical.dec` を `open Classical` で発動すれば全 `Prop` が `Decidable` になる。
- typicality 述語は連続な不等式 (`|·| < ε`) なので `Decidable` instance は `Classical` に頼る。
- → noncomputable `def` で構成可能 (Phase A の `gaussianCodebook` も `noncomputable` なので整合)。

### 5.5 `Code.errorProbAt` の measurability 要件

#### 既存 `Common2026/Shannon/ChannelCoding.lean:204` `errorProbAt` の sigature

```lean
noncomputable def errorProbAt
    (c : Code M n α β) (W : Channel α β) (m : Fin M) : ℝ≥0∞ :=
  (Measure.pi (fun i => W (c.encoder m i))) (c.errorEvent m)
```

- **decoder の measurability 要件**:
  - `c.errorEvent m = (decodingRegion m)ᶜ = {y | decoder y = m}ᶜ`
  - `MeasurableSet (errorEvent m)` が要る → `MeasurableSet (decodingRegion m)` 経由
  - `decodingRegion m = decoder ⁻¹' {m}` なので
    `Measurable decoder` + `MeasurableSet {m}` から従う。
  - `MeasurableSet {m}` は `Fin M` が `MeasurableSingletonClass` (finite + discrete) なので自動。

- **既存 `measurableSet_decodingRegion` (`ChannelCoding.lean:168`) は
  `[Fintype β] [MeasurableSingletonClass β]`** を要求 (この場合「全集合が measurable」で済む)。
  AWGN の場合は `β = ℝ` で `MeasurableSingletonClass` は **無い** (singleton は Lebesgue measure 0)。
  → **decoder の measurability を経由する必要がある**。

- これが `AwgnCode.decoder_meas` field 必須化の根拠。

#### `awgnChannel N h_meas` 出力空間の `MeasurableSpace`

- `Common2026/Shannon/AWGN.lean:73-79`:
  ```lean
  noncomputable def awgnChannel (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) :
      Channel ℝ ℝ := ⟨fun x => gaussianReal x N, h_meas⟩
  ```
- 出力 alphabet = `ℝ` の `MeasurableSpace` (Borel)。`Measure.pi (fun i => awgnChannel N h_meas (X m i))`
  の支持は `Fin n → ℝ` の standard pi `MeasurableSpace` (Borel pi)。
- `MeasurableSingletonClass (Fin n → ℝ)` は **無い** ので、各 `errorEvent` の MeasurableSet 性は
  `Measurable decoder` + `Fin M` の `MeasurableSingletonClass` 経由 (上記)。

### 5.6 関数空間 `(Fin n → ℝ) → α` の measurability

#### `measurable_pi_iff`

- **file:line**: `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:568`
- **signature** (verbatim):
  ```lean
  theorem measurable_pi_iff {g : α → ∀ a, X a} :
      Measurable g ↔ ∀ a, Measurable fun x => g x a
  ```
- **type-class prerequisites**: `[∀ a, MeasurableSpace (X a)]` + `[MeasurableSpace α]`
  (variable で導入)。
- **applicability**: 主に **逆方向** が必要 — codomain が `(Fin n → ℝ)` ではなく **domain** が
  `(Fin n → ℝ)` なので、`measurable_pi_apply` (= 「`y ↦ y i`」の measurability) が
  各座標へのアクセスに使える。

#### `measurable_pi_apply`

- **file:line**: `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:572`
- **signature** (verbatim):
  ```lean
  @[fun_prop]
  theorem measurable_pi_apply (a : δ) : Measurable fun f : ∀ a, X a => f a
  ```
- **type-class prerequisites**: `[∀ a, MeasurableSpace (X a)]`。
- **applicability**: ✅ `y : Fin n → ℝ` から座標 `y i : ℝ` を取り出すのが measurable。
  typical-set 条件の `y i` 経由の評価で使う。

#### `Measurable.eval`

- **file:line**: `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:580`
- **signature** (verbatim):
  ```lean
  theorem Measurable.eval {a : δ} {g : α → ∀ a, X a} (hg : Measurable g) :
      Measurable fun x => g x a
  ```
- **applicability**: 上記 `measurable_pi_apply` の compositional 版。

### 5.7 Random codebook + decoder の合成

#### `Measurable.prodMk`

- **file:line**: `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:405`
- **signature** (verbatim):
  ```lean
  @[fun_prop]
  theorem Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : MeasurableSpace γ}
      {f : α → β} {g : α → γ} (hf : Measurable f) (hg : Measurable g) :
      Measurable fun a : α => (f a, g a)
  ```
- **applicability**: `(X(m), y)` の組み合わせを `(Fin M → Fin n → ℝ) × (Fin n → ℝ)` から
  作るのに使う (codebook を parameter として fix した上での `y` ↦ `(X(m), y)`)。

#### `measurable_uncurry`

- **file:line**: `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:972`
- **signature** (verbatim):
  ```lean
  lemma measurable_uncurry : Measurable (@uncurry ι κ X)
  ```
- **applicability**: codebook と y を **両方** measurable に動かす場面 (e.g., `∫ codebook, …`
  の integrand) で使う。Phase C の `awgn_avg_error_union_bound` で integral 内側の
  `(codebook, y) ↦ (X(m), y)` の measurability。

#### `Measurable.comp`

- (基本 lemma、`Mathlib/MeasureTheory/MeasurableSpace/Basic.lean` 内)
- decoder = (typicality 判定) ∘ (y) の連鎖を組むのに使う。

#### `measurable_to_countable'` (**Option A の核**)

- **file:line**: `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:42`
- **signature** (verbatim):
  ```lean
  theorem measurable_to_countable' [MeasurableSpace α] [Countable α]
      [MeasurableSpace β] {f : β → α}
      (h : ∀ x, MeasurableSet (f ⁻¹' {x})) : Measurable f
  ```
- **type-class prerequisites**: `[MeasurableSpace α]` (codomain), `[Countable α]`,
  `[MeasurableSpace β]` (domain)。**`α` (codomain) に `MeasurableSingletonClass` は不要**
  (preimage を直接要求するので)。
- **explicit args**: `h : ∀ x, MeasurableSet (f ⁻¹' {x})`
- **conclusion**: `Measurable f`
- **applicability to 軸 5**: ✅ **Option A の核**。`f : (Fin n → ℝ) → Fin M` の measurability を
  示すには各 `m : Fin M` について `{y | decoder y = m}` が `MeasurableSet` であることを
  示せばよい。これは typical 述語 + uniqueness の論理結合だから 5.3 の API で組める。

#### `measurable_of_countable`

- **file:line**: `Mathlib/MeasureTheory/MeasurableSpace/Basic.lean:268`
- **signature** (verbatim):
  ```lean
  theorem measurable_of_countable [Countable α] [MeasurableSingletonClass α] (f : α → β) :
      Measurable f
  ```
- **type-class prerequisites**: `[Countable α] [MeasurableSingletonClass α]`。**`α` は domain**
  (これは「離散 domain からの任意の関数は measurable」)、逆方向 → 軸 5 では使えない。

---

## 主要前提条件ボックス

`measurable_to_countable'` を使う際の type-class 整合チェック:

- ✅ `Fin M` は `Countable` (自動、`Finite → Countable`)
- ✅ `Fin M` は `MeasurableSpace` (`Pi.measurableSpace` 等、`Fin` 上は discrete)
- ✅ `Fin n → ℝ` は `MeasurableSpace` (`MeasurableSpace.pi`)
- ✅ `MeasurableSpace.pi` は `Fin n → ℝ` 上で Borel-pi、Lebesgue measurable 集合と整合

`Measurable.exists` / `Measurable.forall` を使う際:

- ✅ `Fin M` は `Countable` (`[Countable ι]` 仮定を満たす)
- ⚠️ 述語 `p : Fin M → (Fin n → ℝ) → Prop` の **各 `m` ごとの** measurability を示す必要。
  典型述語 `p m y := (X(m), y) ∈ A_ε` の measurability は 5.3 で組める。

`Measurable.indicator` / `Measurable.and` 等を使う際:

- ✅ 全部 `[MeasurableSpace α]` のみ要求、追加 type-class なし。

**`StandardBorelSpace` の登場有無**: 軸 5 の lemma 群には **`StandardBorelSpace` 仮定は出てこない**。
これは `Fin n → ℝ` 上の Borel-pi が `StandardBorelSpace` であることを使わずに済む、ということ。
(`rnDeriv` の `HaveLebesgueDecomposition` 由来の `StandardBorel` 仮定は Phase B/D の rnDeriv
側で別途処理。軸 5 単独では発火しない。)

---

## 自作が必要な要素

**0 件**。Mathlib 既存 API のみで Phase C の decoder measurability は組める。

(参考: もし `Measurable.argmin` 系を真っ向から実装する場合 ~50-80 行と推定したが、
Option A 採用で完全に回避できる。)

---

## 撤退ラインへの距離

親 plan の撤退ラインのうち軸 5 に関わるのは:

- **T-1 (`Measure.pi` 型クラス壁)**: 軸 5 とは独立 (codebook の方の話)。
- **T-2 (`IsContinuousAEPGaussian` 外出し)**: 軸 5 とは独立 (AEP は Phase B)。
- **T-3 (expurgation lemma 不在)**: 軸 5 とは独立 (Phase D)。
- **T-4 (全体 700 行超)**: 軸 5 の貢献は ~15-25 行なので影響軽微。

親 plan §「Phase C 失敗時 fallback」:

> decoder measurability の壁 → 判断ログで決定論的 fallback (e.g., `Classical.choice` 使用、
> measurability 別途 hyp 化)

→ **本 inventory の結論**: この fallback は **不要**。Mathlib 既存 API で完全 discharge できる。
撤退ライン発動: **No**。

(縮退案を新規撤退ラインとして提案する必要なし。)

---

## 推奨判断 (Option A 採用)

### Option A (推奨): `Fin.find` + `measurable_to_countable'`

**構成**:

```lean
-- Phase C で書く形 (pseudo-Lean)
open scoped Classical

noncomputable def jointTypicalDecoder
    (P : ℝ) (N : ℝ≥0) (ε : ℝ) (n M : ℕ)
    (codebook : Fin M → Fin n → ℝ) : (Fin n → ℝ) → Fin M :=
  fun y =>
    if h : ∃! m : Fin M, (codebook m, y) ∈ continuousJointTypical P N ε n
    then Classical.choose h.exists  -- 唯一存在する m を取り出す
    else 0                          -- error: 任意の固定値 (Fin M nonempty 仮定下)
    -- 注: M = 0 のとき jointTypicalDecoder は呼ばれない (Phase C 全体で M ≥ 1)

theorem jointTypicalDecoder_measurable
    (P : ℝ) (N : ℝ≥0) (ε : ℝ) (n M : ℕ) [NeZero M]
    (codebook : Fin M → Fin n → ℝ) :
    Measurable (jointTypicalDecoder P N ε n M codebook) := by
  refine measurable_to_countable' fun m => ?_
  -- {y | decoder y = m} の measurability を示す
  -- = {y | (∃! m', typical m') ∧ Classical.choose = m} ∪ {y | (¬ ∃!) ∧ m = 0}
  -- これを Measurable.and / Measurable.exists / Measurable.forall で組む
  sorry  -- 15-20 行
```

**鍵 lemma**:

1. `measurable_to_countable'` (codomain `Fin M` → fiber ごとの MeasurableSet 確認に縮約)
2. `Measurable.exists` + `Measurable.forall` + `Measurable.and` + `Measurable.not`
   (`∃!` 述語の組み立て)
3. `measurable_pi_apply` (座標アクセス `y i`)
4. `Measurable.log` / `measurable_rnDeriv` (typical-set 述語の中身)

**判定根拠**:

- `measurable_to_countable'` は codomain が `Fin M` (countable) だから直撃で使える。
  これが最大の決め手。
- Option B (`Set.indicator` 経由) は **integral を組むときには必要** だが、
  「decoder の measurability」を示すだけなら Option A の方が **直接的で短い**。
- Option C (decoder 自体を hyp として外出し) は honesty 規律違反 (load-bearing hyp 化)
  なので採用不可。

**Phase C measurability 工数見積**: **15-25 行**

- decoder 定義: ~5 行
- `jointTypicalDecoder_measurable` proof: ~15-20 行 (`measurable_to_countable'` 1 行
  + fiber 分解 + 各 fiber の MeasurableSet 組立)

### Option B (代替): `Set.indicator` ベース

`Pe_avg` を `∫ ... · (1 - 𝟙_{(X(1), y) ∈ A_ε}) ...` のように **integrand に直接書く** 流派。
decoder を陽に定義せず、error event の indicator 関数で計算する。

- ✅ Mathlib lemma の組立が `Measurable.indicator` 一発で済む
- ❌ `AwgnCode.decoder_meas` field をどう埋めるかは別問題 (構造体定義で要求されているので、
  陽な decoder が必要)
- ❌ Phase D の expurgation で「個別 codebook + 個別 decoder」のペアを返す必要があるので
  decoder を陽に取り出せた方が良い

→ Option A の方が AwgnCode 構造と整合的。

### Option C (撤退): decoder 全体を hyp 化

`(h_decoder : ∀ codebook, ∃ d, Measurable d ∧ Pe_avg c d ≤ 2ε)` のような形で外出し。

- ❌ **honesty 規律違反**: 結論の核心 (decoder の存在) を hyp 化することになる
- ❌ 親 plan §「honesty 撤退ライン」の禁止リストに該当
- → **採用不可**。

---

## 着手 skeleton (Phase C で使う部分のみ抜粋)

`Common2026/Shannon/AWGNAchievabilityDischarge.lean` の Phase C 部 ~30 行 skeleton:

```lean
import Common2026.Shannon.AWGN
import Common2026.Shannon.ChannelCoding
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal

variable (P : ℝ) (N : ℝ≥0) (ε : ℝ) (n M : ℕ)

/-- Phase B (or T-2 hyp) で定義される continuous joint-typical set。 -/
opaque continuousJointTypical : Set ((Fin n → ℝ) × (Fin n → ℝ))
-- 実体は Phase B で確定

/-- Joint typical decoder: pick the unique m with (X(m), y) typical, else fall back to 0.
Phase C-1 で使う decoder 構成。 -/
noncomputable def jointTypicalDecoder [NeZero M]
    (codebook : Fin M → Fin n → ℝ) : (Fin n → ℝ) → Fin M := fun y =>
  if h : ∃! m : Fin M, (codebook m, y) ∈ continuousJointTypical P N ε n then
    Classical.choose h.exists
  else
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩

/-- `jointTypicalDecoder` is measurable in `y`. **Core: `measurable_to_countable'`
+ logical-combinator measurability**. -/
theorem jointTypicalDecoder_measurable [NeZero M]
    (codebook : Fin M → Fin n → ℝ) :
    Measurable (jointTypicalDecoder P N ε n M codebook) := by
  sorry

end InformationTheory.Shannon.AWGN
```

(`continuousJointTypical` の `MeasurableSet` 性は Phase B 側で供給される前提。
Phase C ではそれを `axiom` あるいは Phase B の export 補題として import する。)

---

## 結論

- 軸 5 (decoder measurability) は **Mathlib 既存 API のみで discharge 可能** (自作 0 件)
- 推奨は **Option A** (`Fin.find` 風 + `Classical.choose` + `measurable_to_countable'`)
- 工数 ~15-25 行、Phase C の他 ~100 行と合わせて plan の見積もり (Phase C 100-150 行) 内
- 撤退ライン T-1/T-2/T-3/T-4 のいずれも発動 No

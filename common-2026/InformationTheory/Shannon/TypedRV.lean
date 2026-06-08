import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Bridge
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.SlepianWolf.Basic
import InformationTheory.Fano.Measure
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Typed Random Variable API (I-1)

教科書 (Cover & Thomas) の `H(X)`, `H(X|Y)`, `I(X;Y)`, `I(X;Y|Z)`, `D(X‖Y)` を
そのまま書けるようにする、opt-in な notation + 薄い alias 層。

設計判断 (詳細は `docs/api/typed-rv-plan.md` §C):

- internal 表現は変えない (`entropy`, `mutualInfo`, `condMutualInfo`,
  `MeasureFano.condEntropy`, `differentialEntropy`, `klDiv` はそのまま)
- 新規 `def` は 2 個 (`klDivRV`, `differentialEntropyRV`)、新規 `abbrev` は 1 個
  (`condEntropy` を `MeasureFano` → `Shannon` namespace へ再エクスポート)、
  新規 `lemma` は 2 個 (`*_def`、いずれも `rfl`)、notation は 5 個
- notation は `scoped[InformationTheory.Shannon]` 限定。Mathlib `IndepFun` の
  `⟂ᵢ[μ]` notation precedent に倣う
- `klDivRV` は **1 測度版のみ**採用 (`klDiv (μ.map X) (μ.map Y)`)

**型クラス制約 (notation 経由で要求される)**:

- `H(X)` / `H(X|Y)` は値域 `α` に `[Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]` を要求
- `I(X;Y)` は `[MeasurableSpace α] [MeasurableSpace β]` のみ
- `I(X;Y|Z)` は追加で `[StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β]
  [Nonempty β]` を要求
- `D(X‖Y)` は `[MeasurableSpace α]` のみ

callsite migration は本タスクの範囲外。後続 seed が `open InformationTheory.Shannon`
で取り込む。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Re-export: `MeasureFano.condEntropy` -/

/-- Re-export `InformationTheory.MeasureFano.condEntropy` into the
`InformationTheory.Shannon` namespace, so the notation `H(X | Y)` resolves here.
Internal definition is unchanged. -/
@[entry_point, reducible] noncomputable def condEntropy
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : Type*} [MeasurableSpace β]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → α) (Yo : Ω → β) : ℝ :=
  InformationTheory.MeasureFano.condEntropy μ Xs Yo

/-! ## KL divergence (typed RV form, 1-measure) -/

/-- KL divergence between two random variables on a common ambient measure `μ`:
`klDivRV μ X Y := klDiv (μ.map X) (μ.map Y)`.

教科書 `D(X‖Y)` の 1 測度版。2 測度版 (`klDiv (μ.map X) (ν.map Y)`) は採用しない
(`docs/api/typed-rv-plan.md` §C-1)。 -/
@[entry_point]
noncomputable def klDivRV
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure Ω) (X Y : Ω → α) : ℝ≥0∞ :=
  klDiv (μ.map X) (μ.map Y)

/-- `klDivRV` は定義通り `klDiv (μ.map X) (μ.map Y)` に展開できる。 -/
@[entry_point]
lemma klDivRV_def
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure Ω) (X Y : Ω → α) :
    klDivRV μ X Y = klDiv (μ.map X) (μ.map Y) := rfl

/-! ## Differential entropy (typed RV form) -/

/-- Differential entropy of a real-valued random variable on ambient `(Ω, μ)`:
`differentialEntropyRV μ X := differentialEntropy (μ.map X)`. -/
@[entry_point]
noncomputable def differentialEntropyRV
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  InformationTheory.Shannon.differentialEntropy (μ.map X)

/-! ## Notation

教科書 (Cover & Thomas) の `H(X)`, `H(X | Y)`, `I(X ; Y)`, `I(X ; Y | Z)`,
`D(X ‖ Y)` に **`μ` 明示** 1 つだけ縮退した形 `H(μ; X)` / `H(μ; X | Y)` /
`I(μ; X ; Y)` / `I(μ; X ; Y | Z)` / `D(μ; X ‖ Y)` を採用する。すべて
`scoped[InformationTheory.Shannon]` で限定し、`open scoped InformationTheory.Shannon`
した callsite だけが見る。

**設計判断の履歴** (`docs/api/typed-rv-plan.md` 判断ログ参照):

- **precedence `:max`** — 当初は Mathlib `IndepFun` の `⟂ᵢ[μ]` precedent (50) に倣う
  計画だったが、50 だと `0 ≤ H(...)` のように `≤` (precedence 50) の右辺で notation を
  使うと「unexpected token at this precedence level」エラーになる。`:max` で atomic
  な高 precedence term として扱う (Mathlib 内も `Norm.norm` 等で採用)
- **`μ` 明示** — 当初は `notation3` の anonymous placeholder `_` で `μ` を隠せると
  推定 (`H(X)` 形) だったが、実機確認で **`_` placeholder は body 評価時に context
  推論できない** ことが判明 (`don't know how to synthesize placeholder for argument
  μ`)。撤退ライン §H-3 に従い `μ` 明示形に縮退。Mathlib `IndepFun` の `X ⟂ᵢ[μ] Y` と
  同じ流儀
- **丸括弧 `( )`** — `[X]` 系は `arr[i]` array index と token 衝突可能性があるが、
  `:max` precedence と `(` 開始リテラルで衝突を回避できる (実機確認済み)

各 notation を展開した結果が要求する型クラス制約はそのまま呼び出し元に伝搬する
(notation は型クラスを「忘れる」のではなく「展開後に必要なものを要求する」)。
特に `I(μ; X ; Y | Z)` は `[StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y]
[Nonempty Y]` を必要とする。 -/

scoped[InformationTheory.Shannon] notation3:max "H(" μ "; " X ")" =>
  entropy μ X
scoped[InformationTheory.Shannon] notation3:max "H(" μ "; " X " | " Y ")" =>
  InformationTheory.Shannon.condEntropy μ X Y
scoped[InformationTheory.Shannon] notation3:max "I(" μ "; " X " ; " Y ")" =>
  mutualInfo μ X Y
scoped[InformationTheory.Shannon] notation3:max
  "I(" μ "; " X " ; " Y " | " Z ")" =>
  condMutualInfo μ X Y Z
scoped[InformationTheory.Shannon] notation3:max "D(" μ "; " X " ∥ " Y ")" =>
  klDivRV μ X Y
-- 補足: `D(μ; X ∥ Y)` の中央セパレータは **`∥` (U+2225 Parallel To)** であり、
-- norm 記法 `‖x‖` で使う **`‖` (U+2016 Double Vertical Line)** とは別文字 (norm token
-- との衝突回避のため)。Lean editor 上では見分けがつきにくいが、教科書 `D(X‖Y)` の意味は
-- 完全に保存されている。

/-! ## Sanity examples

5 つの notation が elaborate に通ることを示す。internal 表現に降りる補題
(`entropy_nonneg`, `mutualInfo_nonneg`, `condMutualInfo_nonneg`) を notation 経由で
直接呼び出せることを確認する。 -/

section Examples

open scoped InformationTheory.Shannon

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : Ω → α) (hX : Measurable X) :
    0 ≤ H(μ; X) :=
  entropy_nonneg μ X hX

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : Type*} [MeasurableSpace β]
    (X : Ω → α) (Y : Ω → β) :
    H(μ; X | Y) = InformationTheory.MeasureFano.condEntropy μ X Y :=
  rfl

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β]
    (X : Ω → α) (Y : Ω → β) :
    0 ≤ I(μ; X ; Y) :=
  mutualInfo_nonneg μ X Y

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {β : Type*} [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    {γ : Type*} [MeasurableSpace γ]
    (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    0 ≤ I(μ; X ; Y | Z) :=
  condMutualInfo_nonneg μ X Y Z

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {α : Type*} [MeasurableSpace α]
    (X Y : Ω → α) :
    D(μ; X ∥ Y) = klDiv (μ.map X) (μ.map Y) :=
  klDivRV_def μ X Y

end Examples

/-! ## Phase 5 — Typed-form main lemmas

教科書本文と一対一対応する RV-form 主補題層 (`docs/api/typed-rv-plan.md` 判断ログ #5)。
全て既存 measure-form 補題への 1 行 alias (新数学ゼロ)。`_rv` suffix で既存無印名との
衝突を回避。 -/

section MainLemmasRV

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Entropy -/

/-- `H(X) ≥ 0` (typed RV form): `entropy_nonneg` の RV-form alias. -/
@[entry_point]
theorem entropy_nonneg_rv
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X) :
    0 ≤ entropy μ X :=
  entropy_nonneg μ X hX

/-! ### Mutual information -/

/-- `I(X; Y) = I(Y; X)` (typed RV form): `mutualInfo_comm` の RV-form alias.

Cover-Thomas (2.4.1) "Mutual information is symmetric." -/
@[entry_point]
theorem mutualInfo_comm_rv
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y) :
    mutualInfo μ X Y = mutualInfo μ Y X :=
  mutualInfo_comm μ X Y hX hY

/-! ### Data processing inequality -/

/-- Data processing inequality (typed RV form):
post-processing `Y ↦ f(Y)` cannot increase mutual information.

`I(X; f(Y)) ≤ I(X; Y)` — Cover-Thomas (2.8.1). -/
@[entry_point]
theorem mutualInfo_le_of_postprocess_rv
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β]
    {γ : Type*} [MeasurableSpace γ]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    {f : β → γ} (hf : Measurable f) :
    mutualInfo μ X (f ∘ Y) ≤ mutualInfo μ X Y :=
  mutualInfo_le_of_postprocess μ X Y hX hY hf

end MainLemmasRV

/-! ## Phase 5 — Sanity examples for typed-form main lemmas -/

section MainLemmasExamples

open scoped InformationTheory.Shannon

/-- Notation `H(μ; X) ≥ 0` 経由で `entropy_nonneg_rv` を呼び出せる。 -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : Ω → α) (hX : Measurable X) :
    0 ≤ H(μ; X) :=
  entropy_nonneg_rv μ X hX

/-- Notation `I(μ; X ; Y) = I(μ; Y ; X)` 経由で `mutualInfo_comm_rv` を呼び出せる。 -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β]
    (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y) :
    I(μ; X ; Y) = I(μ; Y ; X) :=
  mutualInfo_comm_rv μ X Y hX hY

/-- DPI (typed): post-processing cannot increase MI. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β]
    {γ : Type*} [MeasurableSpace γ]
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    {f : β → γ} (hf : Measurable f) :
    mutualInfo μ X (f ∘ Y) ≤ I(μ; X ; Y) :=
  mutualInfo_le_of_postprocess_rv μ X Y hX hY hf

end MainLemmasExamples

end InformationTheory.Shannon

import Common2026.Shannon.Bridge
import Common2026.Shannon.MutualInfo
import Common2026.Shannon.CondMutualInfo
import Common2026.Fano.Measure
import Common2026.Shannon.DifferentialEntropy
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
@[reducible] noncomputable def condEntropy
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
noncomputable def klDivRV
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure Ω) (X Y : Ω → α) : ℝ≥0∞ :=
  klDiv (μ.map X) (μ.map Y)

/-- `klDivRV` は定義通り `klDiv (μ.map X) (μ.map Y)` に展開できる。 -/
lemma klDivRV_def
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure Ω) (X Y : Ω → α) :
    klDivRV μ X Y = klDiv (μ.map X) (μ.map Y) := rfl

/-! ## Differential entropy (typed RV form) -/

/-- Differential entropy of a real-valued random variable on ambient `(Ω, μ)`:
`differentialEntropyRV μ X := differentialEntropy (μ.map X)`. -/
noncomputable def differentialEntropyRV
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  Common2026.Shannon.differentialEntropy (μ.map X)

/-- `differentialEntropyRV` は定義通り `differentialEntropy (μ.map X)` に展開できる。 -/
lemma differentialEntropyRV_def
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) :
    differentialEntropyRV μ X = Common2026.Shannon.differentialEntropy (μ.map X) :=
  rfl

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

end InformationTheory.Shannon

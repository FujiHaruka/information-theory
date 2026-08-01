# BC S8 逆包含の組み立て + headline 等号 — M0 在庫

> 親 plan (SoT): [`bc-general-region-plan.md`](bc-general-region-plan.md) §Phase 5「等号 (less
> noisy)」S8 / §撤退ライン **L-BCO9** / §後続作業 **F-19 · F-21 · F-22** / §判断ログ 20–23。
> 前段の在庫: [`bc-s7-fullsupport-inventory.md`](bc-s7-fullsupport-inventory.md) /
> [`bc-s6-timesharing-inventory.md`](bc-s6-timesharing-inventory.md) /
> [`bc-s5-quantization-inventory.md`](bc-s5-quantization-inventory.md)。
> probe は scratchpad の `ProbeS8{Setup,All,Degenerate}.lean` (計 295 行)。
> **`ProbeS8All.lean` (146 行 / 8 decl / sorry 0) が S8 を端から端まで通しており、到達点 3 本は
> `#print axioms` が `[propext, Classical.choice, Quot.sound]`** (sorryAx 無し)。しかも
> **`lake build` と同じ linter 設定 (`linter.mathlibStandardSet=true`) で warning 0**。
> ⚠ **改名**: 本ファイル中の `bc_uv_subset_superposition` は現行名 `bc_lessNoisy_uv_subset_superposition` (親 plan 判断ログ 25)。以下は改名前の履歴記録なので本文は訂正しない。

## 結論サマリ

- **S8 の到達点は真。probe で全証明が通っている** — 量子化 → 3 不等式の付け替え → S6+S7 への受け渡し
  → 2 重極限 → closure → 逆包含 → headline 等号まで、`lake env lean` がエラー 0 で通過済。
  実装 leg は **転記 + module doc + docstring** に縮む。
- **plan の見立て「残っているのは 2 重極限 + closure だけ」は正しい。ただし部品が 1 つ足りない**
  — `uvInfo₁` (第 1 受信者の corner) を量子化の下で運ぶ補題が S5 に無い。**しかし自作は不要**:
  `uvInfo₁_map_uvRelabel` (`OuterBoundUV/Assembly.lean:143`) が**そのまま当たり、しかも不等式ではなく
  等式**で通る (量子化は第 1 補助しか触らず `uvInfo₁ = I(V;Y₁)` は第 2 補助側だから)。**1 行**。
- **2 重極限は対角線 1 本で足りる** — `m → ∞` と `δ → 0` は独立で、同じ添字 `k` で走らせられる
  (`δ := 1/(k+1)`、`m := k`)。誤差の帳簿は §3。
- **第一象限の暗黙仮定は S8 でも構造的に不発火**。しかも**負レートの枝は空でない**
  (`(-1,-1) ∈ uvRegion ν` が任意の有限 `ν` で成り立つことを probe で機械確認) にもかかわらず、
  証明はどこでも符号場合分けをしない。
- **`ProbabilityMeasure` ↔ `Measure` の往復コストは 0 行** — `Set.iUnion_subset` で取り出した
  `ν : ProbabilityMeasure …` はそのまま coe され、`IsProbabilityMeasure ↑ν` は instance 探索で出る。
- **Mathlib の壁 0 件 / プロジェクト側の壁も 0 件** (BC 家系 8 leg 連続)。**L-BCO9 は不発動**。
- **行数見積り ~190 行 (数学 143 = probe 実測 + 散文・section 46)**。親 plan の `~90 行` は
  **約 2.1 倍への上方修正**が要る (S7 の 6.5 倍ほどではない)。

### 最も危ない発見 (1 行)

**S5 の 3 本だけでは S6/S7 の入口 3 本が揃わない** — S5 は `uvInfo₂` / `uvInfoSum₂` しか運ばず、
S6/S7 が要求する `h₁ : R₁ ≤ (uvInfo₁ ν').toReal` の担い手が S5 に居ない。これを「S5 の穴」と読むと
自作見積りが立つが、実際には**別ファイルの既存資産が等式で埋める** (§Q2-1)。
親 plan §S8 の擬似 Lean は「量子化 → 裾を ε で払う」しか書いておらず、**スロット 1 の扱いが落ちていた**。

## Q1 到達点の署名案

### 逆包含 (probe で証明済) — **`hW` を要求しない**

```lean
theorem bc_uv_subset_superposition (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hln : IsBCLessNoisy W) :
    bcOuterRegionUV W ⊆ bcSuperpositionRegionNoSumRate.{u} W
```

型クラス前提は逐語 (probe の section 変数、`α` は universe `u`、**`DecidableEq` は 1 本も要らない**):

```
{α : Type u} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [StandardBorelSpace α]
{β₁ : Type*} [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [StandardBorelSpace β₁]
{β₂ : Type*} [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
  [StandardBorelSpace β₂]
```

⚠ **`hW : ∀ a b, 0 < (W a).real {b}` はこの包含に要らない** (plan の想定と一致するが、
plan は「逆包含側だけに要る」と書いており、正確には「**逆包含そのものではなく
`bcSuperpositionRegionNoSumRate ⊆ bcCapacityRegion` の側**にだけ要る」)。⟹ 逆包含は
**外界 ⊆ 内界**という純粋に情報量レベルの主張で、達成可能性の regularity から独立している。

### headline (probe で証明済)

```lean
@[entry_point]
theorem bc_lessNoisy_capacity_eq_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hln : IsBCLessNoisy W) :
    bcCapacityRegion W = bcOuterRegionUV W
```

⚠ **headline 側だけ `[DecidableEq α] [DecidableEq β₁] [DecidableEq β₂]` が要る**
(`bcSuperpositionRegionNoSumRate_subset_capacity` 経由。実測: `DecidableEq α` と `DecidableEq β₁`
の 2 本が instance 解決で必要、`DecidableEq β₂` は束の対称性で足す)。**型には現れない**ので
`linter.unusedDecidableInType` が鳴る ⟹ **`by classical exact …` にすると variable 束から
`DecidableEq` を落とせて warning 0 になる** (probe で実測、§Q6)。

### `@[entry_point]` は 2 本を推奨 (3 本目は bare)

| 宣言 | 提案 | 理由 |
|---|---|---|
| `bc_uv_subset_superposition` | **`@[entry_point]` + docstring** | S5–S8 の 4 段が存在する唯一の理由。しかも `hW` 非依存で headline より真に一般。家系の既定 (`exists_fullSupport_bcInfo_ge` 等の中間到達点にも付いている) と整合 |
| `bc_lessNoisy_capacity_eq_uv` | **`@[entry_point]` + docstring** | Phase 5 の headline。README 登録候補 (F-5 の判断待ち) |
| `bc_lessNoisy_superposition_eq_capacity` | **bare** (`## Main statements` には載せる) | 上 2 本の 3 行系。名前が命題を運ぶので `docs/rules/docstrings.md` の name-adequacy で bare |

3 本目は「superposition 内界が less noisy BC の容量領域そのもの」という別命題で、
**捨てるには惜しいが `@[entry_point]` を増やすほどではない**。

```lean
theorem bc_lessNoisy_superposition_eq_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hln : IsBCLessNoisy W) :
    bcSuperpositionRegionNoSumRate.{u} W = bcCapacityRegion W
```

## Q2 目標の真偽判定 (brief の 1–5)

### Q2-1 `uvInfo₁` は量子化で保たれるか — **保たれる。等式。既存資産 1 行** ★最重要

`uvInfo₁ ν = mutualInfo ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.1)` = `I(V; Y₁)`
(`OuterBoundUV/Bridge.lean:777`、**第 2 補助 `V` の側**) であり、
`uvQuantizeLaw ν m = ν.map (uvRelabel (uvQuantize m) id)` (`Quantization.lean:196`) は
**第 1 補助しか触らない** (`uvRelabel e₁ e₂ q = (e₁ q.1, e₂ q.2.1, q.2.2)`、`Assembly.lean:134`)。
⟹ `uvInfo₁_map_uvRelabel` (`Assembly.lean:143`) を `e₂ := id` / `d₂ := id` / `h₂ := fun _ ↦ rfl` で
叩くと **`uvInfo₁ (uvQuantizeLaw ν m) = uvInfo₁ ν`** が出る (probe 実測、1 行)。

⚠ **これが無いと命題が閉じない**: S6 の到達点は `h₁` を第 3 引数で要求し、S6 は `R₂ ≤ 0` の枝で
実際に `h₁` を使う (判断ログの既知事項)。S8 は `h₁ := hb₁` (外界の `bound₁`) をそのまま渡すので、
量子化の下でスロット 1 が動かないことが**帳簿の前提**になっている。

**引き直しの記録** (7 leg 連続で発火している規律):

| 軸 | クエリ | 結果 |
|---|---|---|
| 名前 (in-project) | `rg 'uvInfo₁'` | `Assembly.lean:143` の `uvInfo₁_map_uvRelabel` が唯一の運搬補題。**S5 の兄弟 `uvInfo₂_uvQuantizeLaw:226` / `condMutualInfo_uvQuantizeLaw:234` には `uvInfo₁` 版が無い** |
| 結論形 (in-project) | `rg 'uvInfo₁ \(.*map'` | 同上 1 件 |
| Mathlib | 対象外 (BC 固有語) | — |

⟹ **`uvInfo₁_uvQuantizeLaw` を新設して `Quantization.lean` の `### The slots of the truncated law`
節 (`:217`–`:243`) に置く**のが筋 (3 兄弟が揃う)。S8 のファイルに置くと「次に探す人が
`Quantization.lean` を見て空振りする」。

### Q2-2 第一象限の暗黙仮定 — **構造的に不発火。ただし負レートの枝は空でない**

- **枝は実在する** (probe 機械確認): `((-1,-1) : ℝ × ℝ) ∈ uvRegion ν` が**任意の有限測度 `ν`** で
  成り立つ (4 不等式すべてが `-1 ≤ 0 ≤ (…).toReal` / `-2 ≤ 0 ≤ (…).toReal` に潰れる)。
  さらに `(-1,-1) ∈ bcOuterRegionUV W` を `uvConstLaw` 経由で機械確認済。
  ⟹ S6 が実際に使った `R₂ ≤ 0` の枝は S8 でも**通る**。
- **にもかかわらず S8 の証明は符号場合分けをしない**: S8 が渡す `R₂ := p.2 - slack` は
  S6 の内部で `rcases le_or_gt R₂ 0` に食われ、S7 は `R₁ R₂` の符号を一切使わない (S7 在庫 §Q2-A)。
  S8 自身は `linarith` 4 発だけで、符号仮説をどこにも要求しない (probe 実測)。
- ⟹ **S6 = 実発火 / S7 = 構造的に不発火 / S8 = 「枝は実在するが S8 の層では不発火」**。

### Q2-3 2 重極限の順序 — **対角線 1 本。交互列も部分列選択も要らない**

`m → ∞` (S5 の裾) と `δ → 0` (S7 の摂動) は**互いに依存しない**:

- `uvQuantizeSlack ν m` は `δ` を含まない (`= ν {q | m ≤ q.1} * ofReal (log |β₂|)`、`:202`)。
- S7 の `δ` は「任意の正数」で、`m` にも `ν` にも依存しない (`hδ : 0 < δ` だけ)。

⟹ 同じ添字 `k : ℕ` で `m := k`, `δ := 1/(k+1)` と取れば

```
q k := (p.1 - 1/(k+1), p.2 - (uvQuantizeSlack ν k).toReal - 1/(k+1)) ∈ 内界   (∀ k)
q k → p                                                                      (k → ∞)
内界は closure なので閉  ⟹  p ∈ 内界
```

`IsClosed.mem_of_tendsto` + `Filter.Tendsto.prodMk_nhds` で 3 行。**Phase 4b の
`bc_uv_quadrant_mem_of_achievable` (`Assembly.lean:821`–`:828`) と逐語同型の骨格**なので、
そこを写経するのが最短 (判断ログ 20-(b) の「骨格は再利用可」の 3 度目)。

### Q2-4 `ProbabilityMeasure` ↔ `Measure` の往復 — **書換コスト 0 行**

`bcOuterRegionUV W = closure (⋃ (ν : ProbabilityMeasure (ℕ×ℕ×α×β₁×β₂)) (_ : IsUVChannelLaw W ↑ν),
uvRegion ↑ν)` (`Region.lean:373`) に対し、

```lean
refine closure_minimal ?_ (bcSuperpositionRegionNoSumRate_isClosed W)
refine Set.iUnion_subset fun ν ↦ Set.iUnion_subset fun hν ↦ fun p hp ↦ ?_
exact mem_bcSuperpositionRegionNoSumRate_of_mem_uvRegion W hln hν hp
```

の 3 行で通る (probe 実測)。`hν : IsUVChannelLaw W ↑ν` と `hp : p ∈ uvRegion ↑ν` が
`Measure` 版の補題にそのまま食われ、**`[IsProbabilityMeasure ↑ν]` は Mathlib の
`ProbabilityMeasure.lean:121` の instance が出す**。coe の明示的な `rw` / `show` は 1 本も要らない。

⚠ 唯一の落とし穴は**逆向き**: `↑⟨uvConstLaw W x₀, _⟩` の形に降りたときは `linarith` の
ヒント項が syntactic に一致しない (probe で 1 度踏んだ)。`le_trans (by norm_num)
ENNReal.toReal_nonneg` のように**項を書かない形**にすると通る。

### Q2-5 等号の組み立て — 3 本立てだが `@[entry_point]` は 2 本 (§Q1)

`bcSuperpositionRegionNoSumRate ⊆ bcCapacityRegion ⊆ bcOuterRegionUV ⊆
bcSuperpositionRegionNoSumRate` の 3 本が揃うと 3 集合が一致する。左 2 本は既存
(`SuperpositionRegion.lean:189` / `OuterBoundUV/Assembly.lean:839`)、3 本目が S8。
`Set.Subset.antisymm` 2 発 (各 4 行) で 2 つの等式が出る。

### Q2-6 退化境界 2 つ (構造の違うもの) + 最も一般な反例 class

| 軸 | 設定 | 予測 | 実際 (probe) |
|---|---|---|---|
| 符号 | `p = (-1,-1)` | 4 不等式が自明に成立し、枝が実発火 | ✅ `(-1,-1) ∈ uvRegion ν` が**任意の**有限 `ν` で成立。`bcOuterRegionUV` への所属も機械確認 |
| 裾がゼロ | `Fintype.card β₂ = 1` | `log 1 = 0` ゆえ `uvQuantizeSlack ≡ 0` | ✅ `uvQuantizeSlack ν m = 0` を機械確認 ⟹ `m → ∞` の極限が縮退しても `δ → 0` だけで閉じる (2 つの極限が独立であることの逆向きの証拠) |

**最も一般な対象の再検査**: `bc_uv_subset_superposition` の仮説は `[IsMarkovKernel W]` と
`hln : IsBCLessNoisy W` のみ。`IsBCLessNoisy` (`Classes.lean:63`) は
`∀ (U : Type u) [Fintype U] … (pU) (K), mutualInfo (bcJointDistribution pU K W) Prod.fst (·.2.2.2)
≤ mutualInfo (bcJointDistribution pU K W) Prod.fst (·.2.2.1)` で、**どちらの領域も参照しない
チャネルレベルの述語** ⟹ load-bearing ではない (CLAUDE.md tier 5 に該当しない)。
仮説を満たす最も一般な対象 = 任意の less noisy Markov カーネルであり、probe はその一般形で通っている
⟹ under-hyp の余地なし。

### Q2-7 ⚠ 外界の 4 制約のうち **`sumBound₁` は使わない**

`uvRegion ν` は `InBCOuterRegionUV` の 4 field (`bound₁` / `bound₂` / `sumBound₂` / `sumBound₁`、
`OuterBoundUV.lean:735`–`:743`) だが、S8 が消費するのは**前 3 本だけ**で、
`sumBound₁ : R₁ + R₂ ≤ (uvInfoSum₁ ν).toReal` は `obtain ⟨hb₁, hb₂, hs₂, -⟩` で捨てる。

- **偽にはならない** — 仮説を使わないのは結論を強めるだけで、probe が通っている。
- **意味**: less noisy BC では **`sumBound₁` は冗長** (残り 3 本から出る)。これは
  S6 が `hcJ : (uvInfo₁ ν).toReal ≤ I(X;Y₁)` を DPI で作って `sumBound₂` 側だけで線分を
  張っていることの帰結。⟹ 「4 制約版の外界 = 3 制約版の外界」が less noisy では成り立つ、
  という副産物 (取りに行くなら別 leg。**S8 の scope には入れない**)。

## Q3 誤差の帳簿表 (何がどの誤差を吸収し、どの順で 0 に飛ぶか)

| 記号 | 導入元 | 何を吸収するか | どのレートから引かれるか | 0 への飛ばし方 |
|---|---|---|---|---|
| — (ゼロ) | S5 の量子化 | **スロット 1 `I(V;Y₁)` の損失** | **引かれない** (等式で保存、§Q2-1) | 不要 |
| `(uvQuantizeSlack ν m).toReal` | S5 (`Quantization.lean:202`) | 可算補助 `U` を `m` で切り詰めたときの **`I(U;Y₂)` の損失**と、それを含む **`I(U;Y₂)+I(X;Y₁∣U)` の損失** | **`R₂` からだけ** 1 回 | `m → ∞`。`tendsto_uvQuantizeSlack` (`:363`) を `ENNReal.tendsto_toReal` で `ℝ` に降ろす |
| `δ` | S7 (`SuperpositionFullSupport.lean:786`) | 全支持への摂動: 2 スロットの乗法損失 `(1-ε)` + スロット 2 の加法罰則 `Real.binEntropy ε` | **`R₁` と `R₂` の両方**から | `δ := 1/(k+1) → 0` |
| — | closure | 内界の union が閉じていないこと | — | `bcSuperpositionRegionNoSumRate` が定義上 `closure` なので `IsClosed` は無料 |

**帳簿の要点 (これが S8 を短くしている)**: 裾 `slack` を **`R₂` にだけ 1 回**課すと、
和制約 `R₁ + (R₂ - slack) ≤ (uvInfoSum₂ ν_m).toReal` も**同じ 1 回で払える**
(`uvInfoSum₂ ν ≤ uvInfoSum₂ ν_m + slack` が S5 の 2 本目そのもの)。⟹ `R₁` 側に
量子化の誤差を回す必要がなく、`R₁` から引かれるのは S7 の `δ` だけになる。

極限の並べ方 (同じ `k`):

```
(p.1 - 1/(k+1),  p.2 - slack_k - 1/(k+1))  →  (p.1, p.2)      -- k → ∞
       ↑ S7 の δ           ↑ S5 の裾   ↑ S7 の δ
```

## Q4 資産表

### 4-1 Mathlib (**すべて既存、追加 import 0 本**)

| 用途 | 宣言 | 逐語署名 | file:line |
|---|---|---|---|
| 閉集合への極限の回収 | `IsClosed.mem_of_tendsto` | `theorem IsClosed.mem_of_tendsto {f : α → X} {b : Filter α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : ∀ᶠ x in b, f x ∈ s) : x ∈ s` | `Mathlib/Topology/Neighborhoods.lean:348` |
| 2 成分の同時収束 | `Filter.Tendsto.prodMk_nhds` | `theorem Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : Y} {f : Filter γ} {mx : γ → X} {my : γ → Y} (hx : Tendsto mx f (𝓝 x)) (hy : Tendsto my f (𝓝 y)) : Tendsto (fun c => (mx c, my c)) f (𝓝 (x, y))` | `Mathlib/Topology/Constructions/SumProd.lean:329` |
| `δ` の列 | `tendsto_one_div_add_atTop_nhds_zero_nat` | `theorem tendsto_one_div_add_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] : Tendsto (fun n : ℕ ↦ 1 / ((n : 𝕜) + 1)) atTop (𝓝 0)` | `Mathlib/Analysis/SpecificLimits/Basic.lean:69` |
| 裾を `ℝ` に降ろす | `ENNReal.tendsto_toReal` | `theorem tendsto_toReal {a : ℝ≥0∞} (ha : a ≠ ∞) : Tendsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal)` | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean:103` |
| closure の最小性 | `closure_minimal` | `theorem closure_minimal (h₁ : s ⊆ t) (h₂ : IsClosed t) : closure s ⊆ t` | `Mathlib/Topology/Closure.lean:199` |
| union への着地 | `subset_closure` | `theorem subset_closure : s ⊆ closure s` | 同 `:193` |
| union の分解 | `Set.iUnion_subset` | `theorem iUnion_subset {s : ι → Set α} {t : Set α} (h : ∀ i, s i ⊆ t) : ⋃ i, s i ⊆ t` | `Mathlib/Data/Set/Lattice.lean:142` |
| 等号の組み立て | `Set.Subset.antisymm` | `theorem Subset.antisymm {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b` | `Mathlib/Data/Set/Basic.lean:278` |
| `≤` を `ℝ` で読む | `ENNReal.toReal_mono` | `theorem toReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toReal ≤ b.toReal` | `Mathlib/Data/ENNReal/Real.lean:67` |
| 和を `ℝ` で読む | `ENNReal.toReal_add` | `theorem toReal_add (ha : a ≠ ∞) (hb : b ≠ ∞) : (a + b).toReal = a.toReal + b.toReal` | 同 `:41` |
| 有限性 | `ENNReal.add_ne_top` / `ENNReal.mul_ne_top` | `theorem add_ne_top : a + b ≠ ∞ ↔ a ≠ ∞ ∧ b ≠ ∞` / `theorem mul_ne_top : a ≠ ∞ → b ≠ ∞ → a * b ≠ ∞` | `Mathlib/Data/ENNReal/Operations.lean:176` / `:199` |
| `ProbabilityMeasure` の coe | (無名 instance) | `instance (μ : ProbabilityMeasure Ω) : IsProbabilityMeasure (μ : Measure Ω)` | `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean:121` |

### 4-2 in-project (**S8 の核はすべて既存資産の合成**)

| 用途 | 宣言 | 逐語署名 / 結論形 | file:line |
|---|---|---|---|
| **S7 の着地点 (S8 の入口)** | `sub_mem_bcSuperpositionRegionNoSumRate_of_lessNoisy_of_isUVChannelLaw` | `(W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hln : IsBCLessNoisy W) {m : ℕ} {ν : Measure (Marton.bcAuxAlphabet.{u} m × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) {R₁ R₂ δ : ℝ} (hδ : 0 < δ) (h₁ : R₁ ≤ (uvInfo₁ ν).toReal) (h₂ : R₂ ≤ (uvInfo₂ ν).toReal) (hsum : R₁ + R₂ ≤ (uvInfoSum₂ ν).toReal) : ((R₁ - δ, R₂ - δ) : ℝ × ℝ) ∈ bcSuperpositionRegionNoSumRate.{u} W`。section 変数は `{α : Type u} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]` + β₁ β₂ 同型 + `{V : Type*} [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]` (`:756`–`:762`) | `SuperpositionFullSupport.lean:786` |
| ★ **スロット 1 の運搬** | `uvInfo₁_map_uvRelabel` | `(ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν] {e₁ : U → U'} {e₂ : V → V'} {d₂ : V' → V} (he₁ : Measurable e₁) (he₂ : Measurable e₂) (hd₂ : Measurable d₂) (h₂ : ∀ v, d₂ (e₂ v) = v) : uvInfo₁ (ν.map (uvRelabel e₁ e₂)) = uvInfo₁ ν`。型クラスは `{U V U' V' : Type*} [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace U'] [MeasurableSpace V']` + `{α β₁ β₂ : Type*} [MeasurableSpace _]` のみ (**`StandardBorelSpace` / `Fintype` を要求しない**、probe 実測) | `OuterBoundUV/Assembly.lean:143` |
| S5 裾評価 (corner) | `uvInfo₂_le_uvQuantizeLaw_add_slack` | `(ν : Measure (ℕ × ℕ × α × β₁ × β₂)) [IsProbabilityMeasure ν] (m : ℕ) : uvInfo₂ ν ≤ uvInfo₂ (uvQuantizeLaw.{u} ν m) + uvQuantizeSlack ν m`。**`W` も `h : IsUVChannelLaw` も取らない** (意図的な非対称、plan §S5) | `OuterBoundUV/Quantization.lean:341` |
| S5 裾評価 (和) | `uvInfoSum₂_le_uvQuantizeLaw_add_slack` | `(W : BCChannel α β₁ β₂) [IsMarkovKernel W] {ν : Measure (ℕ × ℕ × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) (m : ℕ) : uvInfoSum₂ ν ≤ uvInfoSum₂ (uvQuantizeLaw.{u} ν m) + uvQuantizeSlack ν m` | 同 `:347` |
| S5 裾の消滅 | `tendsto_uvQuantizeSlack` | `(ν : Measure (ℕ × ℕ × α × β₁ × β₂)) [IsProbabilityMeasure ν] : Tendsto (uvQuantizeSlack ν) atTop (𝓝 0)`。**`W` も `h` も取らない** | 同 `:363` |
| 量子化が channel law を保つ | `uvQuantizeLaw_isUVChannelLaw` | `(W : BCChannel α β₁ β₂) [IsMarkovKernel W] {ν : Measure (ℕ × ℕ × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) (m : ℕ) : IsUVChannelLaw W (uvQuantizeLaw.{u} ν m)` | 同 `:212` |
| 量子化の定義 / 裾 | `uvQuantizeLaw` / `uvQuantizeSlack` / `measurable_uvQuantize` | `uvQuantizeLaw ν m = ν.map (uvRelabel (uvQuantize.{u} m) id) : Measure (ULift.{u} (Fin (m+1)) × ℕ × α × β₁ × β₂)` / `uvQuantizeSlack ν m = ν {q \| m ≤ q.1} * ENNReal.ofReal (Real.log (Fintype.card β₂))` / `Measurable (uvQuantize.{u} m)` | 同 `:196` / `:202` / `:189` |
| スロットの有限性 | `uvInfo₂_ne_top` / `uvInfoSum₂_ne_top` | `(ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν] : uvInfo₂ ν ≠ ∞` / 同型。`{U V : Type*} [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U] [MeasurableSpace V]` | 同 `:104` / `:108` |
| 外界の領域 | `bcOuterRegionUV` / `uvRegion` | `closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂)) (_ : IsUVChannelLaw W ↑ν), uvRegion ↑ν)` / `{p \| InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}` | `OuterBoundUV/Region.lean:373` / `:361` |
| 外界の 4 制約 | `InBCOuterRegionUV` | `structure InBCOuterRegionUV (R₁ R₂ I₁ I₂ J₂ J₁ : ℝ) : Prop where bound₁ : R₁ ≤ I₁; bound₂ : R₂ ≤ I₂; sumBound₂ : R₁ + R₂ ≤ J₂; sumBound₁ : R₁ + R₂ ≤ J₁` | `OuterBoundUV.lean:735` |
| 4 スロットの定義 | `uvInfo₁` / `uvInfo₂` / `uvInfoSum₂` / `uvInfoSum₁` | `I(V;Y₁)` / `I(U;Y₂)` / `uvInfo₂ ν + condMutualInfo ν X Y₁ U` / `uvInfo₁ ν + condMutualInfo ν X Y₂ V` | `OuterBoundUV/Bridge.lean:777` / `:782` / `:787` / `:792` |
| 内界の union | `bcSuperpositionRegionNoSumRate` | `closure (⋃ (k : ℕ) (pU : Measure (Marton.bcAuxAlphabet.{u} k)) (_ : IsProbabilityMeasure pU) (_ : ∀ x, 0 < pU.real {x}) (K : Kernel (Marton.bcAuxAlphabet.{u} k) α) (_ : IsMarkovKernel K) (_ : ∀ x a, 0 < (K x).real {a}), {p \| p.1 ≤ bcInfo₁ pU K W ∧ p.2 ≤ bcInfo₂ pU K W})` | `SuperpositionRegion.lean:178` |
| 内界 ⊆ 容量領域 | `bcSuperpositionRegionNoSumRate_subset_capacity` | `(W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hln : IsBCLessNoisy W) : bcSuperpositionRegionNoSumRate W ⊆ bcCapacityRegion W` (`@[entry_point]`)。**`[DecidableEq α]` を instance で要求する** (probe 実測) | 同 `:189` |
| 順包含 | `bc_capacity_subset_uv` | `(W : BCChannel α β₁ β₂) [IsMarkovKernel W] : bcCapacityRegion W ⊆ bcOuterRegionUV W` (`@[entry_point]`、**明示仮説ゼロ**) | `OuterBoundUV/Assembly.lean:839` |
| 極限の骨格の雛形 | `bc_uv_quadrant_mem_of_achievable` の末尾 | `(bcOuterRegionUV_isClosed W).mem_of_tendsto (h1.prodMk_nhds h2) (Filter.Eventually.of_forall fun k ↦ key _ (by positivity))` | 同 `:821`–`:828` |
| クラス述語 | `IsBCLessNoisy` | `def IsBCLessNoisy (W : BCChannel α β₁ β₂) : Prop := ∀ (U : Type u) [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U] (pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K], mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.2) ≤ mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.1)` | `Classes.lean:63` |
| 退化境界の証拠 | `uvConstLaw` / `uvConstLaw_isUVChannelLaw` | `Measure (ℕ × ℕ × α × β₁ × β₂)` / `IsUVChannelLaw W (uvConstLaw W x₀)` | `OuterBoundUV/Region.lean:401` / `:424` |

### 4-3 自作が要るもの (**計 5 本 / 実測 40 行、すべて probe で証明済**)

| # | 宣言 | 内容 | 行数 | 置き場 |
|---|---|---|---|---|
| 1 | `bcSuperpositionRegionNoSumRate_isClosed` | `IsClosed (bcSuperpositionRegionNoSumRate.{u} W) := isClosed_closure` | **2** | `SuperpositionRegion.lean` (`bcOuterRegionUV_isClosed:379` と対になる位置) |
| 2 | `uvQuantizeSlack_ne_top` | `uvQuantizeSlack ν m ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top` | **2** | `Quantization.lean` (`uvQuantizeSlack:202` の直後) |
| 3 | ★ `uvInfo₁_uvQuantizeLaw` | `uvInfo₁ (uvQuantizeLaw.{u} ν m) = uvInfo₁ ν` | **3** | `Quantization.lean` `### The slots of the truncated law` (`:217`–`:243`、兄弟 2 本の隣) |
| 4 | `uvInfo₂_toReal_sub_slack_le` | `(uvInfo₂ ν).toReal - (uvQuantizeSlack ν m).toReal ≤ (uvInfo₂ (uvQuantizeLaw.{u} ν m)).toReal` | **9** | S8 のファイル (または `Quantization.lean` の `### The truncation estimates` 節) |
| 5 | `uvInfoSum₂_toReal_sub_slack_le` | 同型 (`uvInfoSum₂`、`h : IsUVChannelLaw W ν` を取る) | **10** | 同上 |

⚠ **1–3 は S8 のファイルではなく上流に置くのを推す** — いずれも S8 固有の語を持たない
「S5/S2 の API の欠けた兄弟」で、次に探す人は S8 のファイルを見ない
(CLAUDE.md「In-repo asset search」の失敗モード)。ただし `Quantization.lean` を触ると
S6/S7 が再ビルドされるので、**leg の実装順としては S8 のファイルに書いて通してから上流へ移す**
のが安全 (F-19 のディレクトリ移動と同 leg なのでどのみち全再ビルドになる)。

## Q5 前提が事故りやすい箇所 (key-preconditions box)

- **`ENNReal.toReal_mono` は右辺の有限性を要求する** ⟹ `uvInfo₂ ν ≤ uvInfo₂ ν_m + slack` を `ℝ` に
  降ろすには `uvInfo₂ ν_m ≠ ∞` (`uvInfo₂_ne_top`) と `slack ≠ ∞` (自作 #2) の**両方**が要る。
  `ENNReal.toReal_add` も同じ 2 本を要求する。左辺 `uvInfo₂ ν` の有限性は**要らない**
  (`toReal_mono` は左辺に条件を課さない)。
- **`ENNReal.tendsto_toReal` は合成形を返す** ⟹ `simpa using ((ENNReal.tendsto_toReal h).comp ht)`
  は `ENNReal.toReal ∘ f` と `fun m ↦ (f m).toReal` の不一致で落ちる。
  **`simpa [Function.comp_def] using …`** が正解 (probe で 1 度踏んだ。`Function.comp` では通らない)。
- **`uvInfoSum₂_le_uvQuantizeLaw_add_slack` だけ `W` と `h : IsUVChannelLaw W ν` を取る**
  (`uvInfo₂` 版と `tendsto` 版は取らない)。**揃えないこと** (plan の明示的な設計判断)。
- **`Marton.bcAuxAlphabet.{u} m` は `abbrev` で `ULift.{u} (Fin (m+1))`** (`MartonUnion.lean:52`)
  ⟹ `uvQuantizeLaw ν m : Measure (ULift.{u} (Fin (m+1)) × ℕ × α × β₁ × β₂)` は S7 の入口の型と
  **defeq どころか syntactic に一致**する。型合わせの再ラベルは 1 行も要らない (probe 実測)。
- **第 2 補助は `V := ℕ` で通る** — S6/S7 が要求する `[MeasurableSpace V] [StandardBorelSpace V]
  [Nonempty V]` はすべて `ℕ` の既存 instance で埋まる (probe で `inferInstance` を機械確認)。
- **`DecidableEq` の非対称** (実測): 逆包含側は 1 本も要らないが、headline は
  `bcSuperpositionRegionNoSumRate_subset_capacity` 経由で `DecidableEq α` / `DecidableEq β₁` を
  instance 解決に要求する。**variable 束に足すと `linter.unusedDecidableInType` が鳴る**
  (型に現れないため) ⟹ **束からは落とし、headline の証明を `by classical exact …` にする**と
  `lake build` 相当の linter でも warning 0 (probe 実測)。
- **`uvRegion` の分解は 4 field**: `obtain ⟨hb₁, hb₂, hs₂, -⟩ := hp` (4 本目は捨てる、§Q2-7)。
- **coe が付いた `ProbabilityMeasure` に `linarith` のヒント項を渡すと syntactic に一致しない**
  ⟹ 項を書かない `le_trans (by norm_num) ENNReal.toReal_nonneg` 形にする (probe で 1 度踏んだ)。
- S6/S7 申し送りの**測度書換 `rw` の motive not type correct は S8 では発火しない** —
  S8 は `condMutualInfo` の中の測度を書き換えないため (すべて S5/S6/S7 の中に閉じている)。

## Q6 probe (すべて `lake env lean` がエラー 0)

scratchpad =
`/private/tmp/claude-502/-Users-haruka-dev-lean-projects/40d6cc1b-8a8b-4830-b6ad-cabfa161585a/scratchpad`
(`InformationTheory/` は 1 バイトも触っていない)。

| probe | 内容 | 結果 | 行数 |
|---|---|---|---|
| **P0** `ProbeS8Setup` | import 閉包 + `StandardBorelSpace ℕ` / `IsProbabilityMeasure ↑ν` / `uvQuantizeLaw` の型 / **`uvInfo₁` の量子化不変性** / S7 入口が `V := ℕ` を受けること / slack の有限性 | ✅ | 60 |
| **P1** `ProbeS8All` | S8 全体 (自作 5 本 + 着地 + 2 重極限 + 逆包含 + headline 2 本) | ✅ **8 decl / sorry 0 / `#print axioms` に sorryAx 無し / `linter.mathlibStandardSet` で warning 0** | **146** |
| **P2** `ProbeS8Degenerate` | 退化境界 2 つ (負レート / `card β₂ = 1`) + **F-21 / F-22 の重複同定 4 本** | ✅ 全証明 | 89 |
| 計 | | | **295** |

**通らなかったもの (逐語エラー、実装時に再発する)**:

1. `simpa [Function.comp] using ((ENNReal.tendsto_toReal _).comp _)` → `Function.comp_def` が要る。
2. `linarith [ENNReal.toReal_nonneg (a := uvInfo₁ (uvConstLaw W x₀))]` が
   `↑⟨uvConstLaw W x₀, _⟩` の coe と一致せず失敗 → `le_trans (by norm_num) ENNReal.toReal_nonneg`。
3. `example … := uvQuantizeLaw ν m` に `noncomputable` が要る (probe 固有、実装には出ない)。
4. `bcSuperpositionRegionNoSumRate` の variable 束を削りすぎて `Fintype α` の instance 解決失敗。
5. headline の `DecidableEq α` / `DecidableEq β₁` 解決失敗 → §Q5 の `classical` 解。

**linter 検証コマンド** (親 plan F-20 = 「`lake env lean` は一部 linter に盲目」への対応):

```bash
lake env lean -D linter.mathlibStandardSet=true -D linter.unusedFintypeInType=false <file>
```

`lakefile.toml` の `leanOptions` を再現するので、`lake build` を回さずに linter 差分が取れる。
**S8 の probe はこの設定で warning 0** ⟹ 実装 leg は F-20 の後始末を持ち込まない。

## Q7 壁 / 撤退ライン

### Mathlib の壁 — **0 件** (8 leg 連続) / プロジェクト側の壁も **0 件**

| クエリ | 結果 | 影響 |
|---|---|---|
| loogle `IsClosed.mem_of_tendsto` | `Found one declaration` | 閉集合への極限回収は既存。しかも `OuterBoundUV/Assembly.lean:827` が先例として使用中 |
| loogle `tendsto_one_div_add_atTop_nhds_zero_nat` | `Found one declaration` | `δ` の列は既存 |
| loogle `ENNReal.Tendsto.toReal` | **`Found 0 declarations`** | dot-notation 版は無い。**しかし壁ではない** — 結論形検索 `\|- Filter.Tendsto (fun _ => ENNReal.toReal _) _ _` で `ENNReal.tendsto_toReal` が 1 件出て、`.comp` 1 発で足りる (probe 通過)。**0-hit は検索軸の問題**、判断ログ 16 の 4 度目 |
| loogle `ENNReal.tendsto_toReal` | `Found one declaration` | 同上 |
| `rg 'bcSuperpositionRegionNoSumRate'` (in-project) | 定義 1 + 消費 3 | `_isClosed` は未存在 (自作 2 行) |
| `rg 'IsClosed \(bc'` (in-project) | 3 件 (`bcOuterRegionUV` / `bcCapacityRegion` / `bcOuterRegionCoop`) | 内界版だけが欠けている ⟹ 自作 #1 は重複ではない |
| `rg 'uvInfo₁'` (in-project) | `uvInfo₁_map_uvRelabel` が唯一の運搬補題 | **自作予定を 1 件取り消した** (§Q2-1) |

⚠ **0-hit は 1 件だけで、それは「1 段分解した各辺」で引き直したら埋まった**。
「dot-notation が無いから自作」という見積りは**誤り**なので立てないこと。

### L-BCO9 との距離 — **不発動**

発動条件 (凍結文言の読み替え後) は「**逆包含が閉じない**」。
`bc_uv_subset_superposition` が probe で `#print axioms = [propext, Classical.choice, Quot.sound]`
(sorryAx 無し) を出しているので、**閉じている**。⟹ 退避
(`bc_uv_subset_superposition` を署名保持で `sorry` + `@residual(plan:bc-lessnoisy-converse-quantization)`)
は**要らない**。**S5 / S6 / S7 / S8 の 4 段連続で不発動**、これで L-BCO9 は判定の担い手を失う
(等号が閉じるので line 自体が retire できる)。

**本在庫のどの補題にも `@residual` を付けない** — probe で全証明が compile 通過しており、
埋まらない穴は 1 つも残っていない。

## Q8 行数見積り (**数学と散文を別枠**、判断ログ 20-(a) / 23)

| step | 内容 | 数学 (probe 実測) | 散文・section | 計 |
|---|---|---|---|---|
| **S8-a** | 自作 3 本 (closed / slack 有限 / `uvInfo₁` 不変) + `omit` 束 | 24 | 8 | ~32 |
| **S8-b** | S5 の 2 本を `.toReal` で読む 2 本 | 24 | 6 | ~30 |
| **S8-c** ★gateway | 1 つの四辺形の 1 点を 2 段ずらして内界へ着地 | 20 | 6 | ~26 |
| **S8-d** | 2 重極限 (対角線列 + `IsClosed.mem_of_tendsto`) | 24 | 6 | ~30 |
| **S8-e** | 逆包含 (`closure_minimal` + union 分解) | 9 | 8 | ~17 |
| **S8-f** | headline 2 本 (`classical` 版) | 20 | 12 | ~32 |
| variable 束 / section / import / namespace | | 22 | — | ~22 |
| module doc | `## Main statements` + 設計 3 段落 | — | 34 | ~34 |
| 計 | | **143** | **80** | **~190** |

帯は **175–215**。S7 (probe 745 → 実測 802、+8%) と同じく、本 probe は**配線と到達点と headline まで
覆っている**ので上振れは module doc と docstring に限られる。S6 のような +85% は期待しない。

**同 leg の F-19 / F-21 / F-22 を足した差分** (§Q10 / §Q11):

| 項目 | 行数の増減 | 触るファイル |
|---|---|---|
| S8 本体 | **+190** | 新規 1 |
| F-19 ディレクトリ昇格 | ±0 (純粋な移動) + **import 行 5 本の書換 + 1 本の追加** | 3 ファイル移動 + `InformationTheory.lean` |
| F-21 `uvConstLaw` の畳み込み | **−40** | `Region.lean` / `SuperpositionFullSupport.lean` |
| F-22 分岐クラスタの畳み込み | **−55** | `SuperpositionTimeShare.lean` / `SuperpositionFullSupport.lean` |
| 差引 | **+95** | |

**ファイル配置**: 新規 `InformationTheory/Shannon/BroadcastChannel/Superposition/Assembly.lean`
(F-19 を同 leg でやる前提。やらないなら `BroadcastChannel/SuperpositionAssembly.lean`)。
import は `…Superposition.FullSupport` の **1 本だけ** (probe で cycle 無しを機械確認)。

## Q9 実装 leg への申し送り

### 着手順 (gateway atom = **S8-c**)

**`sub_mem_bcSuperpositionRegionNoSumRate_of_mem_uvRegion` (S8-c) を最初に切る**。理由:

- (a) ここが **S5 の帳簿と S6/S7 の入口の唯一の接点**で、`h₁` / `h₂` / `hsum` の 3 本を
  どの誤差でずらすかが決まる。ここが通れば残りは極限の取り回しと 3 行の組み立てだけ。
- (b) S8-a の 3 本 (とくに `uvInfo₁_uvQuantizeLaw`) は S8-c の前提としてしか意味を持たないので、
  S8-c を目標に置くと自然に順序が決まる。
- (c) probe でも最初に型が合ったのがここで、以降は機械的だった。

順序: **S8-a → S8-c → S8-b (a と c の間に必要な分だけ) → S8-d → S8-e → S8-f**。

### 親 plan で書き換えが要る箇所 (編集は plan の担当)

1. **§Phase 5 S8 の行数 `(残り ~90 行)` → `~190 行 (数学 143 + 散文 47、probe 実測 146 行)`**。
2. **§Phase 5 S8 の擬似 Lean にスロット 1 の行を足す** — 現状は「`uvInfo₂` の裾を `ε_m` で払う」
   しか書いておらず、`h₁` の担い手 (`uvInfo₁` が量子化で不変であること) が落ちている。
3. **§Phase 5 の到達目標の但し書き**: 「`hW` は逆包含側だけに要る」→ 正確には
   「**逆包含そのものには要らず、`bcSuperpositionRegionNoSumRate ⊆ bcCapacityRegion` にだけ要る**」。
4. **§撤退ライン L-BCO9**: **S8 でも不発動が確定**した (逆包含が probe で sorryAx-free)。
   4 段連続不発動で判定の担い手が居なくなる ⟹ 等号が landing したら retire できる。
5. **§在庫 に新規行 1 本**: `Superposition/Assembly.lean` (F-19 後の位置、import 1 本)。
6. **§後続作業 F-19 / F-21 / F-22 を「S8 と同 leg で実施」に更新** (§Q10 / §Q11 に手順)。
7. **§後続作業に 1 件追加候補**: less noisy BC では `uvRegion` の 4 制約のうち `sumBound₁` が
   冗長 (§Q2-7)。「3 制約版の外界 = 4 制約版の外界」を別 leg で取りに行けるが**任意**。
8. **§判断ログに 1 件** — 「**plan の擬似 Lean が『残るのは X だけ』と書いたら、
   前 step の到達点が要求する仮説を 1 本ずつ数えて突き合わせる**」: S8 の擬似 Lean は
   S5 の 2 本 (`uvInfo₂` / `uvInfoSum₂`) しか見ておらず、S6/S7 の入口が要求する 3 本目
   (`uvInfo₁`) の担い手を書いていなかった。実害は無かった (既存資産が等式で埋めた) が、
   **在庫が引き直さなければ「S5 の穴」として自作見積りが立っていた**。

### 命名の提案 (`docs/rules/naming.md` に合わせる)

`bcSuperpositionRegionNoSumRate_isClosed` / `uvQuantizeSlack_ne_top` / `uvInfo₁_uvQuantizeLaw`
(兄弟 `uvInfo₂_uvQuantizeLaw` に揃える) / `uvInfo₂_toReal_sub_slack_le` /
`uvInfoSum₂_toReal_sub_slack_le` / `sub_mem_bcSuperpositionRegionNoSumRate_of_mem_uvRegion` /
`mem_bcSuperpositionRegionNoSumRate_of_mem_uvRegion` / `bc_uv_subset_superposition` /
`bc_lessNoisy_capacity_eq_uv` / `bc_lessNoisy_superposition_eq_capacity`。

## Q10 F-19 — `Superposition*` のサブディレクトリ昇格

### 発火条件

3 ファイル **1556 行** (`SuperpositionRegion` 209 / `SuperpositionTimeShare` 545 /
`SuperpositionFullSupport` 802)。S8 を足すと 4 ファイル 1746 行。
`docs/rules/module-structure.md` §「適用 / ターゲット形」の
「ファイル名の接頭辞クラスタを `<Topic>/` に昇格し、冗長な接頭辞をファイル名から落とす」に該当。

### ディレクトリ名と配置 (**推奨**)

```
InformationTheory/Shannon/BroadcastChannel/Superposition/
  Region.lean      ← SuperpositionRegion.lean
  TimeShare.lean   ← SuperpositionTimeShare.lean
  FullSupport.lean ← SuperpositionFullSupport.lean
  Assembly.lean    ← S8 の新規ファイル
```

- **umbrella ファイルは作らない**。先例は `BroadcastChannel/Marton/` (8 ファイル、`Marton.lean` 無し)。
  `OuterBoundUV.lean` + `OuterBoundUV/` の形は**中身のある top-level ファイルがある場合**の先例で、
  `Superposition` にはそれに当たる内容が無い。
- **S8 のファイル名は `Assembly.lean`** — `OuterBoundUV/Assembly.lean` (その Phase の最終組み立て) と
  同じ役割語。`Converse.lean` は `BroadcastChannel/Converse.lean` (degraded converse) と衝突し、
  かつ S8 は逆包含 = 達成側なので誤誘導になる。
- **namespace は不変** (`InformationTheory.Shannon.BroadcastChannel`)。module-structure.md の
  移行方針どおり「ファイル移動 + import パス書換のみ」。
- **依存方向は一方向**: `Superposition/` → `OuterBoundUV/` + top-level (`Classes` / `MartonUnion`)。
  逆向きは 0 件 ⟹ §5 (ディレクトリ間依存を一方向に保つ) を満たす。

### import 書換の実測 (`rg` 実測、**計 6 行**)

| ファイル | 行 | 現状 | 変更後 |
|---|---|---|---|
| `SuperpositionTimeShare.lean` | `:2` | `import …BroadcastChannel.SuperpositionRegion` | `import …BroadcastChannel.Superposition.Region` |
| `SuperpositionFullSupport.lean` | `:1` | `import …BroadcastChannel.SuperpositionTimeShare` | `import …BroadcastChannel.Superposition.TimeShare` |
| `InformationTheory.lean` | `:128` `:129` `:130` | `…SuperpositionRegion` / `…SuperpositionTimeShare` / `…SuperpositionFullSupport` | `…Superposition.Region` / `.TimeShare` / `.FullSupport` |
| `InformationTheory.lean` | (追加 1 行) | — | `import …BroadcastChannel.Superposition.Assembly` |

**外部から `Superposition*` を import しているファイルは 0 件** (`rg 'BroadcastChannel\.Superposition'`
の全ヒットが上記 2 本)。⟹ **波及は事実上ゼロ**。

⚠ `docs/` 側の散文には旧パス参照が残る (module-structure.md の「残作業」に既に立っている項目)。
**S8 の leg では docs の sweep はやらない**。

## Q11 F-21 / F-22 — 機械確認済の重複 2 件の解消手順

4 本の同定をすべて probe で機械確認済 (`ProbeS8Degenerate.lean` §Dedup)。

### F-21 `uvConstLaw` は `uvLawOfInput` の dirac 特殊化

**機械確認**: `uvConstLaw W x₀ = uvLawOfInput W (Measure.dirac ((0:ℕ), (0:ℕ), x₀))` が **`rfl`**。

**どちらを残すか**: **`uvLawOfInput` (一般形) を残し、`uvConstLaw` をその特殊化にする**。

**手順**:

1. `SuperpositionFullSupport.lean` の `section Law` (`:55`–`:111`、57 行 = `measurable_uvUnassoc`
   private / `uvLawOfInput` / `_isProbabilityMeasure` / `_isUVChannelLaw` / `_map_aux_input`) を
   **逐語で `OuterBoundUV/Region.lean` の `IsUVChannelLaw` 定義 (`:110`) より後・
   `## The UV outer region` 節 (`:349`) より前**へ移す。
2. `Region.lean` の private `measurable_uvUnassoc` (`:407`–`:414`、`omit` 込み 8 行) を削除
   (S7 版が一般形で**証明項まで逐語同一**)。
3. `uvConstLaw` (`:398`–`:405`) を `uvLawOfInput W (Measure.dirac ((0:ℕ),(0:ℕ),x₀))` に置換 (2 行)。
4. `uvConstLaw_isProbabilityMeasure` (`:416`–`:419`) / `uvConstLaw_isUVChannelLaw` (`:421`–`:442`)
   を `inferInstance` / `uvLawOfInput_isUVChannelLaw W _` に置換 (計 4 行)。

**削減**: `Region.lean` の `:398`–`:442` 45 行 → 約 10 行 ⟹ **−35 行**。
`SuperpositionFullSupport.lean` からは 57 行が移動 (差引 0)。合計 **約 −40 行**
(private の逐語重複 8 行を含む)。

**波及 (`dep_consumers.sh` 実測)**:

| 対象 | direct consumers |
|---|---|
| `uvConstLaw` | **3 decl / 1 file** — `Region.lean:416` `:423` `:444` (すべて同ファイル) |
| `uvLawOfInput` | **9 decl / 1 file** — `SuperpositionFullSupport.lean:73` `:79` `:98` `:172` `:179` `:218` `:703` `:709` `:717` (すべて同ファイル) |

移動先 `Region.lean` は `SuperpositionFullSupport.lean` の import 閉包内なので、
**9 本の consumer は 1 行も書き換えなくてよい**。⟹ **import 変更 0 / 外部波及 0**。

### F-22 S6 の分岐クラスタは S7 の一般混合の特殊化

**機械確認 3 本** (`σ := ν.map (uvRelabel (fun _ ↦ u₀) (id : V → V))` と置く):

```
uvTagConst ν u₀      = uvTagFalse σ                    -- Measure.map_map 1 行 + rfl
uvBranchKernel ν u₀  = uvMixKernel ν σ                 -- 上を rw
uvTimeShareLaw ν u₀ lam = uvMixLaw ν σ lam             -- 上を rw
```

**どちらを残すか**: **`uvMixKernel` / `uvMixLaw` (2 引数の一般形) を残す**。
S6 側は `σ` を渡す薄いラッパにする (S6 の到達点の署名は不変)。

**手順**:

1. `SuperpositionFullSupport.lean` の `section Mix` (`:275`–`:395`、121 行) を
   **逐語で `SuperpositionTimeShare.lean` の `section Mixture` 内、`uvTagTrue` (`:83`) より後**へ移す
   (`boolLaw` `:58` / `uvTagTrue` `:83` / `uvRelabel` はすべて上流に揃っている)。
2. S6 の `uvBranchKernel` (`:102`–`:105`) + `_isMarkovKernel` (`:107`–`:111`) を削除し、
   `uvTimeShareLaw ν u₀ lam := uvMixLaw ν (ν.map (uvRelabel (fun _ ↦ u₀) id)) lam` に置換。
3. `uvTimeShareLaw_isProbabilityMeasure` (`:118`–`:121`) → `inferInstance`。
4. `uvTimeShareLaw_eq` (`:123`–`:129`) → `uvMixLaw_eq` + `uvTagConst = uvTagFalse σ` の 3 行。
5. `uvBranchKernel_ae_tag` (`:131`–`:156`、**26 行**) を削除し `uvMixKernel_ae_tag` の
   特殊化 1–2 行に置換 (**最大の削減点**)。
6. `uvTimeShareLaw_isUVChannelLaw` (`:158`–`:167`) → `uvMixLaw_isUVChannelLaw` +
   `h.map_auxiliaries measurable_const measurable_id` の 2–3 行。
7. `uvTagConst` (`:88`–`:90`) と `uvTagConst_isProbabilityMeasure` (`:97`–`:100`) は
   `uvTagFalse σ` の別名になるので削除するか、`σ` を書く手間を省く 2 行の `abbrev` に留める。

**削減**: `SuperpositionTimeShare.lean` の `:88`–`:167` 約 80 行 → 約 25 行 ⟹ **約 −55 行**。
`SuperpositionFullSupport.lean` からは 121 行が移動 (差引 0)。

**波及 (`dep_consumers.sh` 実測、すべて同ファイル内で外部 0)**:

| 対象 | direct consumers |
|---|---|
| `uvTimeShareLaw` | **6 decl / 1 file** — `SuperpositionTimeShare.lean:118` `:123` `:158` `:216` `:266` `:471` |
| `uvBranchKernel` | **7 decl / 1 file** — 同 `:107` `:113` `:118` `:123` `:131` `:216` `:266` |
| `uvMixLaw` | **9 decl / 1 file** — `SuperpositionFullSupport.lean:310` `:315` `:363` `:370` `:382` `:411` `:437` `:567` `:592` |
| `uvMixKernel` | **8 decl / 1 file** — 同 `:295` `:305` `:310` `:315` `:323` `:382` `:411` `:437` |
| `uvTagFalse` | **9 decl / 1 file** — 同 `:285` `:290` `:295` `:315` `:323` `:357` `:363` `:370` `:437` |

移動は**上流方向**なので、`SuperpositionFullSupport.lean` の 26 本の consumer は書き換え不要。
書き換えが要るのは `SuperpositionTimeShare.lean` の 6–7 本 (同ファイル内) だけ。

### 実施順 (同 leg 内)

**S8 本体 → F-19 (移動) → F-21 → F-22** を推す。理由: S8 は既存署名を 1 本も変えないので
先に通せる。F-19 の移動を先にやると S8 のファイル配置が確定する。F-21 / F-22 は
どちらも**上流方向の移設 + 下流の削除**で、F-19 後のパスで一度に書ける。
**F-21 と F-22 は独立** (触るファイルが `Region.lean` と `TimeShare.lean` で交わらない)。

## 着手のための skeleton

```lean
import InformationTheory.Shannon.BroadcastChannel.Superposition.FullSupport

/-!
# Broadcast channel — the UV outer region of a less noisy channel is achievable

The outer region is indexed by five-tuple laws over a countable auxiliary, the inner one by
achievability pairs over a finite one.  Truncating the auxiliary at a level `m` moves a law of
the outer region onto a finite alphabet at a cost the tail alone carries, and perturbing the
resulting pair toward the uniform law repairs the support at a cost any positive slack covers.
Both costs vanish along one sequence, and the inner bound is a closure, so the point itself is
recovered …
(`## Main statements` は §Q1 / §Q9 の名前をそのまま並べる)
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon Filter
open scoped ENNReal Topology

universe u

section Converse

variable {α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [StandardBorelSpace α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
    [StandardBorelSpace β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
    [StandardBorelSpace β₂]

/-- The UV outer region of a less noisy broadcast channel is contained in the superposition
inner bound over the full-support achievability pairs.  No support hypothesis on the channel is
needed: this inclusion is the information-theoretic half of the equality. -/
@[entry_point]
theorem bc_uv_subset_superposition (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hln : IsBCLessNoisy W) :
    bcOuterRegionUV W ⊆ bcSuperpositionRegionNoSumRate.{u} W := by
  refine closure_minimal ?_ (bcSuperpositionRegionNoSumRate_isClosed W)
  refine Set.iUnion_subset fun ν ↦ Set.iUnion_subset fun hν ↦ fun p hp ↦ ?_
  exact mem_bcSuperpositionRegionNoSumRate_of_mem_uvRegion W hln hν hp

end Converse

end InformationTheory.Shannon.BroadcastChannel
```

⚠ skeleton に `sorry` は無く、**本在庫のどの補題にも `@residual` を付けない** — probe で全証明が
compile 通過しており、埋まらない穴は 1 つも残っていない。

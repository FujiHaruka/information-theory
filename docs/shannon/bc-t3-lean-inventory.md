# T3 層 3 のための Lean 在庫棚卸し

> **Parent**: [`bc-open-problem-t3-plan.md`](bc-open-problem-t3-plan.md)

対象: `InformationTheory/Shannon/BroadcastChannel/`（下位 `Marton/` `Superposition/` `OuterBoundUV/`
`Achievability/` を含む、35 ファイル）。

本書の §1–§6 は**逐語**（`#check` で elaborate した署名、`rg` の出力、`#print axioms` の出力）に限る。
そこから導いた判断は §7 にのみ書く。

---

## §1 主要な領域定義の対応表

署名はすべて `import InformationTheory` したスクラッチファイルを `lake env lean` で通した
`#check @<完全修飾名>` の出力（逐語）。`variable` ブロック由来のインスタンス引数を含む。

### 1.1 `C(W)` 操作的容量領域 — **在る**

| 項目 | 内容 |
|---|---|
| decl | `InformationTheory.Shannon.BroadcastChannel.bcCapacityRegion` |
| file:line | `InformationTheory/Shannon/BroadcastChannel/Operational.lean:68` |
| 意味 | 到達可能レート対の集合の位相的閉包 |

```
@bcCapacityRegion : {α : Type u_1} →
  {β₁ : Type u_2} →
    {β₂ : Type u_3} →
      [inst : MeasurableSpace α] →
        [inst_1 : MeasurableSpace β₁] → [inst_2 : MeasurableSpace β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)
```

本体（`Operational.lean:68`、逐語）:

```lean
def bcCapacityRegion (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure {p | BCAchievable W p.1 p.2}
```

土台の `BCAchievable`（`Operational.lean:53`、逐語）— **符号・平均誤り確率から定義された操作的述語**:

```lean
def BCAchievable (W : BCChannel α β₁ β₂) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∃ N : ℕ, ∀ n, N ≤ n →
    ∃ (M₁ M₂ : ℕ) (_ : ⌈Real.exp ((n : ℝ) * R₁)⌉₊ ≤ M₁) (_ : ⌈Real.exp ((n : ℝ) * R₂)⌉₊ ≤ M₂)
      (c : BroadcastCode M₁ M₂ n α β₁ β₂),
      (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε'
```

`BCChannel`（`Basic.lean:39`）の署名:

```
BCChannel : (α : Type u_1) →
  (β₁ : Type u_2) →
    (β₂ : Type u_3) → [MeasurableSpace α] → [MeasurableSpace β₁] → [MeasurableSpace β₂] → Type (max u_1 u_3 u_2)
```

### 1.2 Marton 内界 — **在る（2 補助変数版）**

チャネル単位の領域（合併をとったもの）と、補助変数を固定した四辺形の 2 段になっている。

| 項目 | 内容 |
|---|---|
| decl（チャネル単位） | `…BroadcastChannel.Marton.martonRegionUnion` |
| file:line | `MartonUnion.lean:71` |
| decl（補助変数固定） | `…BroadcastChannel.Marton.martonRegion` |
| file:line | `Operational.lean:127` |
| decl（full-support 制限版） | `…BroadcastChannel.Marton.martonRegionUnionFullSupport` (`MartonUnion.lean:81`) |

```
@martonRegionUnion : {α : Type u_1} →
  {β₁ : Type u_2} →
    {β₂ : Type u_3} →
      [inst : MeasurableSpace α] →
        [Fintype β₁] →
          [inst_2 : MeasurableSpace β₁] → [Fintype β₂] → [inst_4 : MeasurableSpace β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)
```

```
@martonRegion : {V₁ : Type u_1} →
  {V₂ : Type u_2} →
    {α : Type u_3} →
      {β₁ : Type u_4} →
        {β₂ : Type u_5} →
          [Fintype V₁] →
            [inst : MeasurableSpace V₁] →
              [Fintype V₂] →
                [inst_2 : MeasurableSpace V₂] →
                  [inst_3 : MeasurableSpace α] →
                    [Fintype β₁] →
                      [inst_5 : MeasurableSpace β₁] →
                        [Fintype β₂] →
                          [inst_7 : MeasurableSpace β₂] →
                            MeasureTheory.Measure (V₁ × V₂) →
                              ProbabilityTheory.Kernel (V₁ × V₂) α → BCChannel α β₁ β₂ → Set (ℝ × ℝ)
```

本体（`MartonUnion.lean:71`、逐語）:

```lean
noncomputable def martonRegionUnion (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k₁ : ℕ) (k₂ : ℕ)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂))
    (_ : IsProbabilityMeasure pV)
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α)
    (_ : IsMarkovKernel K), martonRegion pV K W)
```

```lean
def martonRegion (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) :
    Set (ℝ × ℝ) :=
  {p | InMartonRegion p.1 p.2 (martonInfo₁ pV K W) (martonInfo₂ pV K W) (martonInfoV₁V₂ pV K W)}
```

`InMartonRegion`（`Marton/Basic.lean:40`、逐語）:

```lean
structure InMartonRegion (R₁ R₂ I₁ I₂ I₁₂ : ℝ) : Prop where
  bound₁ : R₁ ≤ I₁
  bound₂ : R₂ ≤ I₂
  boundSum : R₁ + R₂ ≤ I₁ + I₂ - I₁₂
```

**補助変数の本数 = 2**（`V₁`, `V₂`）。共通補助変数 `U` / タイムシェアリング変数 `W₀` に当たる引数は
`martonRegion` の署名にも `InMartonRegion` のフィールドにも**現れない** ⟹ 3 補助変数 `(U,V,W)` 版
ではない。三つの情報量は `martonInfo₁ = I(V₁;Y₁)` / `martonInfo₂ = I(V₂;Y₂)` /
`martonInfoV₁V₂ = I(V₁;V₂)`（`Marton/Setup.lean:244,252,262` にエントロピー差として定義）。

### 1.3 UV 外界 — **在る**

| 項目 | 内容 |
|---|---|
| decl（チャネル単位） | `…BroadcastChannel.bcOuterRegionUV` (`OuterBoundUV/Region.lean:425`) |
| decl（法を固定した四辺形） | `…BroadcastChannel.uvRegion` (`OuterBoundUV/Region.lean:413`) |
| decl（法の制約） | `…BroadcastChannel.IsUVChannelLaw` (`OuterBoundUV/Region.lean:116`) |
| 不等式の形 | `…BroadcastChannel.InBCOuterRegionUV` (`OuterBoundUV.lean:735`) |

```
@bcOuterRegionUV : {α : Type u_1} →
  [inst : MeasurableSpace α] →
    {β₁ : Type u_2} →
      [inst_1 : MeasurableSpace β₁] →
        {β₂ : Type u_3} →
          [inst_2 : MeasurableSpace β₂] →
            [StandardBorelSpace α] →
              [Nonempty α] →
                [StandardBorelSpace β₁] →
                  [Nonempty β₁] → [StandardBorelSpace β₂] → [Nonempty β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)
```

```
@IsUVChannelLaw : {α : Type u_1} →
  [inst : MeasurableSpace α] →
    {β₁ : Type u_2} →
      [inst_1 : MeasurableSpace β₁] →
        {β₂ : Type u_3} →
          [inst_2 : MeasurableSpace β₂] →
            {U : Type u_4} →
              {V : Type u_5} →
                [inst_3 : MeasurableSpace U] →
                  [inst_4 : MeasurableSpace V] → BCChannel α β₁ β₂ → MeasureTheory.Measure (U × V × α × β₁ × β₂) → Prop
```

本体（`OuterBoundUV/Region.lean:413,425`、逐語）:

```lean
def uvRegion {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] : Set (ℝ × ℝ) :=
  {p | InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal
    (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}

def bcOuterRegionUV (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂))
    (_ : IsUVChannelLaw W (ν : Measure (ℕ × ℕ × α × β₁ × β₂))),
      uvRegion (ν : Measure (ℕ × ℕ × α × β₁ × β₂)))
```

```lean
structure InBCOuterRegionUV (R₁ R₂ I₁ I₂ J₂ J₁ : ℝ) : Prop where
  bound₁ : R₁ ≤ I₁
  bound₂ : R₂ ≤ I₂
  sumBound₂ : R₁ + R₂ ≤ J₂
  sumBound₁ : R₁ + R₂ ≤ J₁
```

docstring 逐語（`Region.lean:421-423`）: "Both auxiliary alphabets are fixed to `ℕ`, which
quantifies over every countable auxiliary without quantifying over types."

### 1.4 重ね合わせ (superposition) 内界 — **在る（2 種）**

| 項目 | 内容 |
|---|---|
| decl | `…BroadcastChannel.bcSuperpositionRegionNoSumRate` (`Superposition/Region.lean:187`) |
| decl | `…BroadcastChannel.bcSuperpositionRegionSumRate` (`Superposition/Region.lean:241`) |

```
@bcSuperpositionRegionNoSumRate : {α : Type u_1} →
  {β₁ : Type u_2} →
    {β₂ : Type u_3} →
      [Fintype α] →
        [inst : MeasurableSpace α] →
          [Fintype β₁] →
            [inst_2 : MeasurableSpace β₁] →
              [Fintype β₂] → [inst_4 : MeasurableSpace β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)
```

`bcSuperpositionRegionSumRate` も同一のインスタンス列。⚠ **定義それ自身には degraded /
less-noisy の仮定は入っていない**。クラス仮定は定義ではなく**定理側の明示引数**として現れる（→ §2.4）。

### 1.5 auxiliary-receiver 外界（[auxrec] Theorem 7）— **無い**

再検証コマンドと出力:

```
rg -ni 'auxiliary receiver|auxrec|auxiliary-receiver|Nair.*Gamal|Theorem 7' \
  InformationTheory/Shannon/BroadcastChannel/
```

ヒットはすべて `Nair–El Gamal`（= UV 外界の別名）を指す docstring 行のみで、
補助受信者（auxiliary receiver）を導入した `∀J` 形の外界に当たる decl は 0 件。

**近縁だが別物**（混同注意）: `…BroadcastChannel.bcOuterRegionCoop`
(`OuterBound.lean:375`) は**協調 (cooperative / genie) 外界**であって auxiliary-receiver 外界
ではない。

```
@bcOuterRegionCoop : {α : Type u_1} →
  {β₁ : Type u_2} →
    {β₂ : Type u_3} →
      [Fintype α] →
        [inst : MeasurableSpace α] →
          [inst_1 : MeasurableSpace β₁] → [inst_2 : MeasurableSpace β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)
```

---

## §2 一般 BC か degraded か

判定はすべて §1 の `#check` 逐語署名に基づく。「一般」と書けるのは、署名に `IsBCDegraded` /
`IsBCLessNoisy` / `IsBCMoreCapable` のいずれの引数も現れず、かつ型が特別な形に固定されていない場合。

### 2.1 判定表

| 定義 | 判定 | 署名に現れる非 regularity 仮定 |
|---|---|---|
| `bcCapacityRegion` | **一般 BC** | 無し（`[MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]` のみ） |
| `BCAchievable` | **一般 BC** | 同上 |
| `martonRegion` | **一般 BC** | 無し（`[Fintype …] [MeasurableSpace …]` のみ） |
| `martonRegionUnion` | **一般 BC** | 無し（`[MeasurableSpace α] [Fintype β₁] [MeasurableSpace β₁] [Fintype β₂] [MeasurableSpace β₂]`） |
| `uvRegion` / `bcOuterRegionUV` / `IsUVChannelLaw` | **一般 BC** | 無し（`[StandardBorelSpace …] [Nonempty …]` の可測論的 regularity のみ） |
| `bcSuperpositionRegionNoSumRate` / `…SumRate` | **一般 BC**（定義として） | 無し（`[Fintype …] [MeasurableSpace …]` のみ） |
| auxiliary-receiver 外界 | — | 定義が存在しない |

### 2.2 クラス述語そのものの署名（逐語）

```
@IsBCDegraded : {α : Type u_1} →
  {β₁ : Type u_2} →
    {β₂ : Type u_3} →
      [inst : MeasurableSpace α] →
        [inst_1 : MeasurableSpace β₁] → [inst_2 : MeasurableSpace β₂] → BCChannel α β₁ β₂ → Prop
```

`IsBCLessNoisy` / `IsBCMoreCapable` も同一のインスタンス列。⟹ **3 つとも一般の `W` 上の述語**であり、
「degraded 専用の型」は存在しない。関係は `IsBCDegraded.isBCLessNoisy` (`Classes.lean:133`) /
`IsBCLessNoisy.isBCMoreCapable` (`Classes.lean:219`)。

### 2.3 領域定義の側に degraded は**入っていない**

§2.1 のとおり、§1 の 5 種の領域定義はどれも一般 BC に対して定義されている。⟹ **層 3 でそのまま
使える**（degraded 専用で使えない領域定義は在庫に存在しない）。

### 2.4 クラス仮定が入るのは「一致定理」の側だけ

以下は `bcCapacityRegion W = bcOuterRegionUV W` を主張する既存定理で、**クラス仮定を明示引数として
取る**（`#check` 逐語、`Superposition/Assembly.lean:142` / `Superposition/MoreCapable.lean:643,656`）:

```
@bc_lessNoisy_capacity_eq_uv : ∀ {α : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} [Fintype α] [inst : Nonempty α]
  [inst_1 : MeasurableSpace α] [MeasurableSingletonClass α] [inst_3 : StandardBorelSpace α] [Fintype β₁]
  [inst_5 : Nonempty β₁] [inst_6 : MeasurableSpace β₁] [MeasurableSingletonClass β₁] [inst_8 : StandardBorelSpace β₁]
  [Fintype β₂] [inst_10 : Nonempty β₂] [inst_11 : MeasurableSpace β₂] [MeasurableSingletonClass β₂]
  [inst_13 : StandardBorelSpace β₂] (W : BCChannel α β₁ β₂) [ProbabilityTheory.IsMarkovKernel W],
  (∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) → IsBCLessNoisy W → bcCapacityRegion W = bcOuterRegionUV W
```

`bc_moreCapable_capacity_eq_uv` / `bc_degraded_capacity_eq_uv` は最後の仮定がそれぞれ
`IsBCMoreCapable W` / `IsBCDegraded W` に替わるだけで、他は逐語同一。

---

## §3 サンドイッチ `Marton ⊆ C ⊆ UV` の Lean 上の現状

**両方向とも在る。両方とも一般 BC 版。両方とも sorry-free。**

### 3.1 `Marton ⊆ C`（achievability）

| 項目 | 内容 |
|---|---|
| decl | `…BroadcastChannel.Marton.martonRegionUnion_subset_capacity` |
| file:line | `MartonFullSupport.lean:231` |
| 属性 | `@[entry_point]` |

```
@martonRegionUnion_subset_capacity : ∀ {α : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} [Fintype α] [Nonempty α]
  [inst : MeasurableSpace α] [MeasurableSingletonClass α] [inst_2 : Fintype β₁] [Nonempty β₁]
  [inst_4 : MeasurableSpace β₁] [MeasurableSingletonClass β₁] [inst_6 : Fintype β₂] [Nonempty β₂]
  [inst_8 : MeasurableSpace β₂] [MeasurableSingletonClass β₂] (W : BCChannel α β₁ β₂)
  [ProbabilityTheory.IsMarkovKernel W],
  (∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) → martonRegionUnion W ⊆ bcCapacityRegion W
```

補助変数固定版: `Marton.marton_region_subset_capacity_of_channel_fullSupport`
(`MartonFullSupport.lean:170`, `@[entry_point]`) — 仮定は同じく `hW` のみ。旧版
`Marton.marton_region_subset_capacity` (`Operational.lean:154`) は `hpV` / `hK` も要求する。

### 3.2 `C ⊆ UV`（converse）

| 項目 | 内容 |
|---|---|
| decl | `…BroadcastChannel.bc_capacity_subset_uv` |
| file:line | `OuterBoundUV/Assembly.lean:852` |
| 属性 | `@[entry_point]` |

```
@bc_capacity_subset_uv : ∀ {α : Type u_1} [inst : MeasurableSpace α] {β₁ : Type u_2} [inst_1 : MeasurableSpace β₁]
  {β₂ : Type u_3} [inst_2 : MeasurableSpace β₂] [Fintype α] [MeasurableSingletonClass α] [inst_5 : StandardBorelSpace α]
  [inst_6 : Nonempty α] [Fintype β₁] [MeasurableSingletonClass β₁] [inst_9 : StandardBorelSpace β₁]
  [inst_10 : Nonempty β₁] [Fintype β₂] [MeasurableSingletonClass β₂] [inst_13 : StandardBorelSpace β₂]
  [inst_14 : Nonempty β₂] (W : BCChannel α β₁ β₂) [ProbabilityTheory.IsMarkovKernel W],
  bcCapacityRegion W ⊆ bcOuterRegionUV W
```

⚠ **明示引数の仮定はゼロ**（`W` と `IsMarkovKernel W` 以外に何もない）。full-support すら要らない。

### 3.3 `Marton ⊆ UV`（内界と外界の直接比較、参考）

```
@martonRegionUnion_subset_uv : ∀ {α : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3} [inst : Fintype α] [inst_1 : Nonempty α]
  [inst_2 : MeasurableSpace α] [inst_3 : MeasurableSingletonClass α] [inst_4 : Fintype β₁] [inst_5 : Nonempty β₁]
  [inst_6 : MeasurableSpace β₁] [inst_7 : MeasurableSingletonClass β₁] [inst_8 : Fintype β₂] [inst_9 : Nonempty β₂]
  [inst_10 : MeasurableSpace β₂] [inst_11 : MeasurableSingletonClass β₂] (W : BCChannel α β₁ β₂)
  [ProbabilityTheory.IsMarkovKernel W], martonRegionUnion W ⊆ bcOuterRegionUV W
```

`MartonUnion.lean:94`, `@[entry_point]`。仮定は `IsMarkovKernel W` のみ（full-support 不要）。

### 3.4 誠実性の状態

**`sorry` はディレクトリ全体で 0 件。** 再検証コマンドと出力:

```
$ for f in $(find InformationTheory/Shannon/BroadcastChannel -name '*.lean'); do \
    scripts/sig_view.ts --sorry "$f"; done
（出力なし = sorry を含む decl 0 件）

$ rg -c 'sorry' InformationTheory/Shannon/BroadcastChannel/
（ヒットなし）

$ rg -n '@residual' InformationTheory/Shannon/BroadcastChannel/
（ヒットなし）

$ rg -n '@audit:' InformationTheory/Shannon/BroadcastChannel/ | rg -v '@audit:ok'
（ヒットなし = 非 ok の @audit タグは 0 件）
```

`#print axioms` の逐語出力（`import InformationTheory` したスクラッチファイルを `lake env lean`）:

```
'InformationTheory.Shannon.BroadcastChannel.Marton.martonRegionUnion_subset_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InformationTheory.Shannon.BroadcastChannel.bc_capacity_subset_uv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InformationTheory.Shannon.BroadcastChannel.Marton.martonRegionUnion_subset_uv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InformationTheory.Shannon.BroadcastChannel.bc_moreCapable_capacity_eq_uv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

⟹ 4 本とも sorryAx-free。

タグの逐語（`bc_capacity_subset_uv` の docstring 末尾, `Assembly.lean:850`）: `@audit:ok`。
`martonRegionUnion_subset_capacity` の docstring（`MartonFullSupport.lean:227-229`）には
`@audit:*` タグが付いていない（`@residual` も無い）。

### 3.5 load-bearing hypothesis の疑い — **該当なし**

再検証コマンドと出力:

```
$ rg -n 'Hypothesis|Reduction\b|IsBCClaim|Claim' InformationTheory/Shannon/BroadcastChannel/ --glob '*.lean'
InformationTheory/Shannon/BroadcastChannel/Converse.lean:497:Reduction: independence gives …   （散文コメント）
InformationTheory/Shannon/BroadcastChannel/OuterBound.lean:40:section Reduction              （section 名）
InformationTheory/Shannon/BroadcastChannel/OuterBound.lean:264:end Reduction                  （section 名）
```

⟹ `*Hypothesis` / `*Reduction` / `IsXxxClaim` **型の引数を取る decl は 0 件**。
サンドイッチ 2 本の明示引数は、`hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}`（チャネルの
full support = regularity precondition）1 つのみ（converse 側はそれすら無い）。

---

## §4 補助変数の基数境界

### 4.1 Marton 内界 — **基数無境界**

`bcAuxAlphabet` の署名と本体（`MartonUnion.lean:65`、逐語）:

```
bcAuxAlphabet : ℕ → Type u_1
```

```lean
abbrev bcAuxAlphabet (k : ℕ) : Type u := ULift.{u} (Fin (k + 1))
```

各インデックス `k` の補助アルファベットは基数 `k+1` の有限型だが、`martonRegionUnion` の本体
（§1.2 逐語再掲）は `⋃ (k₁ : ℕ) (k₂ : ℕ) …` と **`k₁`, `k₂` を `ℕ` 全体にわたって走らせている**。
⟹ 合併全体としては **補助変数の基数に上限が無い**。

`martonRegion` 側も `[Fintype V₁] [Fintype V₂]` という**一般の有限型変数**であり
（§1.2 の `#check` 逐語）、`Fintype.card V₁ ≤ Fintype.card α + 1` のような制約は署名に無い。

### 4.2 UV 外界 — **基数無境界（可算無限に固定）**

`bcOuterRegionUV` の本体（§1.3 逐語再掲）は補助アルファベットを `ℕ × ℕ` に固定している。
⟹ 有限基数への上限は無い（docstring 逐語: "quantifies over every countable auxiliary"）。

### 4.3 Carathéodory 型の基数境界補題 — **無い**

再検証コマンドと出力:

```
$ rg -n 'Fintype.card' InformationTheory/Shannon/BroadcastChannel/
```

ヒット全 20 行の内訳（逐語確認済）:
`Classes.lean:238`（`1 < Fintype.card β₁` = semi-deterministic の非自明性条件）/
`MartonFullSupport.lean:161`（`Fintype.card_pos`、一様分布の正値性）/
`Converse.lean:99,114,118,132,145,149,164,165,578,579`（`Fintype.card (Fin M₁)` =
**メッセージ数**であって補助変数ではない）/
`OuterBoundUV.lean:822-861`（`Fintype.card ξ₁` = 同じくメッセージアルファベット）/
`Marton/MarkovCore/Receiver1.lean:552`, `Receiver2.lean:481`（典型性半径の分母）/
`Superposition/TimeShare.lean:486`（タイムシェアリング用の型同値）。

```
$ rg -ni 'carath|cardinality bound' InformationTheory/Shannon/BroadcastChannel/
InformationTheory/Shannon/BroadcastChannel/Achievability/Setup.lean:425:  Slice-cardinality bound: …（典型集合のスライス濃度、補助変数の基数ではない）
InformationTheory/Shannon/BroadcastChannel/Achievability/Setup.lean:593:  -- The slice-cardinality bound.
InformationTheory/Shannon/BroadcastChannel/MartonUnion.lean:16:  bcAuxAlphabet k — the auxiliary alphabet of cardinality k + 1.
InformationTheory/Shannon/BroadcastChannel/MartonUnion.lean:62:  The auxiliary alphabet of cardinality k + 1, …
```

⟹ **`|V₁| ≤ f(|X|)` の形の Carathéodory 型境界を述べた補題は在庫に 0 件**。
`bcAuxAlphabet` の 2 ヒットは「`k` 番目のアルファベットの基数は `k+1`」という定義の説明であって、
合併を有限個の `k` に切り詰める補題ではない。

---

## §5 `t3-marton-uv-coincidence-class` を Lean で言うのに要るもの

標的の命題:「Marton 内界と UV 外界が一致するチャネル族に限れば `C(W)` は effectively compact」。
その**前段**（`C(W) = Marton(W)` を一致クラス上で言う部分）に必要な 3 点。

### 5.1 ギャップ表

| # | 要るもの | 判定 | 根拠 |
|---|---|---|---|
| 1 | 「`Marton(W) = UV(W)` なるチャネル `W`」を述べる述語 | **無い（要自作、1–4 行）** | `martonRegionUnion` と `bcOuterRegionUV` はともにチャネル単位で定義済（§1.2 / §1.3）なので `def IsBCMartonUVTight (W) : Prop := martonRegionUnion W = bcOuterRegionUV W` が書ける。既存の同形述語 `IsBCLessNoisy` (`Classes.lean:63`) は本体 3 行 |
| 2 | サンドイッチ 2 本の一般 BC 版 | **在る** | `Marton.martonRegionUnion_subset_capacity` (`MartonFullSupport.lean:231`) / `bc_capacity_subset_uv` (`OuterBoundUV/Assembly.lean:852`)。§3 のとおり両方 sorryAx-free・一般 BC・load-bearing hyp なし |
| 3 | 結論 `C(W) = Marton(W)`（一致クラス上） | **無い（要自作、5–8 行）** | 同形の既存定理 `bc_lessNoisy_capacity_eq_uv` (`Superposition/Assembly.lean:142`) の**本体が 4 行**（`classical` + `Set.Subset.antisymm` に 2 本の包含を渡すだけ）。ここも `Set.Subset.antisymm (h.symm ▸ ...) (...)` の形で同じ骨格になる |

### 5.2 #1 / #3 を書くときに詰まる既知の 1 点（配線、壁ではない）

⚠ **インスタンス列が 2 本で一致していない**（§3.1 / §3.2 の `#check` 逐語より）:

- `martonRegionUnion_subset_capacity` が要求: `[Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]` +（β₁, β₂ につき同様）
- `bc_capacity_subset_uv` が要求: 上に加えて `[StandardBorelSpace α] [StandardBorelSpace β₁]
  [StandardBorelSpace β₂]`

⟹ 両者を合成する定理は **`StandardBorelSpace` を含む和集合**を宣言する必要がある。
先例は §2.4 の `bc_lessNoisy_capacity_eq_uv` で、実際に
`[Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]`
（β₁, β₂ も同様）を並べている。⟹ **同じ列をそのまま写せばよい**（新規の型クラス設計は不要）。

さらに `martonRegionUnion_subset_capacity` は `hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}`
を要求するので、#3 の結論定理も同じ full-support 仮定を引き継ぐ（`bc_lessNoisy_capacity_eq_uv`
も同一の `hW` を取っており、先例と一致する）。

### 5.3 「effectively compact」まで含めた全体 — **前段のみ在庫で届く**

§5.1 の 3 点は `C(W) = Marton(W)` までであって、そこから先の「effectively compact」の主張は
§6 のとおり定式化そのものが在庫に無い。

---

## §6 計算可能性まわり

### 6.1 in-project 探索（指示された 1 回の走査）

```
$ rg -i 'computab|semicomput|effectiv' InformationTheory/ --glob '*.lean' | wc -l
683
```

⚠ **683 のほぼ全部が `noncomputable section` / `noncomputable def`** で、計算可能性の概念とは無関係。
語を絞った再走査:

```
$ rg -ni 'semicomput|effectively compact|computably|effective compact' InformationTheory/ --glob '*.lean'
InformationTheory/Shannon/Kolmogorov/OmegaNoncomputable.lean:5:# Chaitin's constant is not computably approximable
InformationTheory/Shannon/Kolmogorov/OmegaNoncomputable.lean:35:* `chaitinOmega_not_computable` — `Ω` is not computably approximable.
InformationTheory/Shannon/Kolmogorov/OmegaNoncomputable.lean:537:/-! ### The halting probability is not computably approximable -/
InformationTheory/Shannon/Kolmogorov/OmegaNoncomputable.lean:572:/-- Chaitin's constant is not computably approximable: no computable sequence of
```

⟹ **`semicomputable` / `effectively compact` は in-project に 0 件**。

### 6.2 in-project に実在する計算可能性の資産（`InformationTheory/Shannon/Kolmogorov/`）

⚠ ここは `BroadcastChannel/` ではなく **Kolmogorov 家系**にある（BC 側からの探索では出てこない）。

| decl | file:line | 署名（逐語） |
|---|---|---|
| `InformationTheory.Kolmogorov.IsComputableENNReal` | `OmegaNoncomputable.lean:78` | `IsComputableENNReal : ENNReal → Prop` |
| `InformationTheory.Kolmogorov.IsFloorComputableENNReal` | `OmegaNoncomputable.lean:89` | 同形（`ENNReal → Prop`） |
| `InformationTheory.Kolmogorov.chaitinOmega_not_computable` | `OmegaNoncomputable.lean:589` | `¬InformationTheory.Kolmogorov.IsComputableENNReal InformationTheory.Kolmogorov.chaitinOmega` |
| `InformationTheory.Kolmogorov.complexity_not_computable` | `Noncomputable.lean:83` | — |
| `InformationTheory.Kolmogorov.condComplexity_not_computable` | `Noncomputable.lean:40` | — |

`IsComputableENNReal` の本体（`OmegaNoncomputable.lean:78`、逐語）:

```lean
def IsComputableENNReal (x : ℝ≥0∞) : Prop :=
  ∃ a : ℕ → ℕ, Computable a ∧ ∀ n : ℕ,
    x ≤ (a n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n + (2 : ℝ≥0∞)⁻¹ ^ n ∧
      (a n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n ≤ x + (2 : ℝ≥0∞)⁻¹ ^ n
```

さらに `InformationTheory/Shannon/Kolmogorov/PrefixComputability.lean` が
`Nat.Partrec.Code` / `Primrec` / `Computable` の層を実際に使っている（`open Nat.Partrec
Nat.Partrec.Code`, `:24`）。⟹ **チューリング機械層の配線先は in-project に存在する**。

⚠ ただし `IsComputableENNReal` は**単一のスカラー**（1 個の `ℝ≥0∞`）の計算可能性であり、
**平面の部分集合**（`Set (ℝ × ℝ)`）の計算可能性・effective compactness ではない。
在庫にある最も近い形はこれで、標的との差は「スカラー ⟹ 集合」1 段。

### 6.3 Mathlib 側（loogle、指示どおり）

```
$ ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Computable, Real"
Found 0 declarations mentioning Real and Computable.
```

参考にもう 1 クエリ（範囲確認）— `"Computable (Set _)"` は
`Found 71 declarations mentioning Computable. Of these, 70 match your pattern(s).` を返し、
一覧はすべて `Mathlib.Computability.Partrec` 由来（`Computable.nat_bodd` / `Computable.id` 等）。

⟹ Mathlib の `Computable` は `Primcodable` 型（`ℕ` / `List` 等）上のものだけで、
**`Real` に触れる宣言は 0**。計算可能解析（computable metric space / effectively compact set）の
層は Mathlib に無い。

---

## §7 我々の演繹（§1–§6 の逐語から導いた判断。逐語ではない）

1. **層 3 の「サンドイッチ」部分は既に完成している** — §3 の 2 本は一般 BC 版で、sorry 0 /
   residual 0 / sorryAx-free / load-bearing hyp なし。⟹ 層 3 の最初の候補
   `t3-marton-uv-coincidence-class` は、**サンドイッチの構築から始める必要がない**。

2. **`t3-marton-uv-coincidence-class` の前段（`C = Marton` on 一致クラス）は在庫的にほぼ ready** —
   §5 の 3 点のうち #2 は在り、#1 #3 は先例をなぞる 10 行前後。実質の作業は**型クラス列の配線**で、
   数学的な穴ではない。

3. **穴は 2 つに分かれている** — (a) §4 の**基数境界の欠如**（P4 の条件 (i) が要求する
   「基数有界」に対応する補題が在庫に 0 件）、(b) §6 の**計算可能性の定式化の欠如**
   （`Set (ℝ × ℝ)` の effectively compact が in-project にも Mathlib にも無い）。
   (a) と (b) は独立で、(a) は BC 家系の話、(b) は Kolmogorov 家系＋新規定式化の話。

4. **(a) は「壁」ではなく「未着手」の可能性が高い** — Marton 内界は `⋃ (k₁ k₂ : ℕ)` の合併なので、
   Carathéodory 型の境界補題（`k` を `|α|` 程度で切っても合併が変わらない）を足せば基数有界版に
   なる形をしている。⚠ **これは形の観察であって、その補題が証明できるという主張ではない**
   （実際に証明を試みていない）。

5. **(b) の出発点は Kolmogorov 家系にある** — §6.2 の `IsComputableENNReal` が「`2^{-n}` 精度の
   計算可能近似列」という [N13] 語義そのものの形をしており、`chaitinOmega_not_computable` は
   **否定側 (T3-β) の証明テンプレートが in-project に実物として存在する**ことを意味する。
   ⚠ 差は「スカラー ⟹ 平面集合」1 段だが、その 1 段が effectively compact の定義そのものである。

6. **auxiliary-receiver 外界（[auxrec] Thm 7）が無いことは、L2 の成果の形式化に直接効く** —
   L2 は「`Thm7(W)` の一様 effective compactness」を証明済としているが、その `Thm7` に当たる
   Lean の定義が在庫に無い（§1.5）。⟹ L2 の成果を層 3 に載せるには**定義から新規**になる。
   ⚠ 一方 `t3-marton-uv-coincidence-class` は `Thm7` を経由しないので、この欠落に阻まれない。

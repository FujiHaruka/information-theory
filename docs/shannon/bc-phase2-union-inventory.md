# BC Phase 2 — 内界の補助変数 union — 在庫調査

> 親 plan: [`bc-general-region-plan.md`](bc-general-region-plan.md) §Phase 2 / §Phase 5 等号 /
> §撤退ライン **L-BCO2** **L-BCO8**。直前 leg の在庫:
> [`bc-inner-outer-bridge-inventory.md`](bc-inner-outer-bridge-inventory.md)。
>
> 本ファイルは在庫のみ。`InformationTheory/` と plan は 1 バイトも編集していない。
> probe は scratchpad (`probe1`–`probe6`) で、記載の EXIT=0 はすべて `lake env lean` の実測。
>
> ⚠ **改名**: 本ファイル中の `martonRegionUnionFS` は現行名 `martonRegionUnionFullSupport`、
> `martonRegionUnionFS_subset_union` は `martonRegionUnionFullSupport_subset_union`。
> `martonRegionUnionFS_subset_capacity` に対応する現行宣言は `martonRegionUnion_subset_capacity`
> (`Shannon/BroadcastChannel/MartonFullSupport.lean`) で、全支持に限らない union 全体について
> 成立する真に一般な形で入った。以下は着地前の提案記録なので本文は訂正しない。

## 一行サマリ

**Phase 2 の中核 (union の定義 + 橋の持ち上げ + 達成側の持ち上げ) は Mathlib の壁 0 件で、
probe6 が `sorry` ゼロ・EXIT=0 で全部通した (計 62 行)。** 自作が要るのは union 本体ではなく
その周辺 3 件 (補助アルファベットの付け替え / 全支持仮説の除去 / 逆包含の量子化) で、
うち 1 件は 48 行を実測済。**撤退ライン L-BCO2 は「解けた」でも「回避された」でもなく、
定義側では回避され消費側 (Phase 5 の less noisy) で再出現する** — これが本 leg の最重要所見。

## plan / 前 leg の記述で覆ったもの (冒頭に明記)

| # | 覆った記述 | 出所 | 実測 |
|---|---|---|---|
| 1 | 「L-BCO2 は実質的に前倒しで解けている公算」(plan §撤退ライン L-BCO2) | plan `:441` | **半分誤り**。濃度固定 (`Fin`) を採ると定義側では universe 量化が消えるので L-BCO2 の発動条件に触れない = 回避。しかし `IsBCLessNoisy` は `U : Type u` (α と同 universe) を量化するので、**`Fin (k+1) : Type 0` を渡せない** (probe5 逐語エラー、§3)。`ULift.{u}` で完全に消せることも機械確認 (§3-C) |
| 2 | 「内界 union は外界と同じ添字 (`ℕ` の 5 つ組法) に載せれば等号が並ぶ」(本 leg のブリーフが §1 で誘導している設計) | ブリーフ §1 | **採ってはいけない**。`ℕ` 補助では `I(V₁;V₂) = ⊤` が起き `.toReal = 0` で**和レート制約が消える** ⟹ 内界が容量領域を超える (§2 案 C の反例)。**`.toReal` の危険の向きは判断ログ 11-(m) が言う「無限アルファベット拡張の 1 軸」だけではなく、内界を `ℕ` に載せた瞬間に発火する** |
| 3 | plan §在庫 の `Region.lean` 行番号 (`uvRegion:233` / `bcOuterRegionUV:245` / `_isClosed:251` / `_isLowerSet:265` / `_nonempty:317`) | plan `:39` `:157` | 実測は `:259` / `:271` / `:277` / `:291` / `:343` (約 +26 行のドリフト)。plan の編集は本 leg の権限外なので記録のみ |
| 4 | 「convex hull が要るなら `MultipleAccess/TimeSharingConverse/` の資産を参照」(plan §Phase 2) | plan `:105` | **要らない**。各 `martonRegion` は凸 (probe3 で 15 行・EXIT=0)、union は非凸だが**相手側 `bcOuterRegionUV` も非凸のまま**なので等号は並ぶ。MAC の convexHull 資産は converse 側の道具で、BC 4b は既に不採用 (plan `:53`) |
| 5 | 「Carathéodory 型の濃度上界は **Mathlib にも** in-repo にも無い」(plan §Phase 2) | plan `:103` | **半分誤り**。情報理論側の support lemma (補助変数の濃度上界) は確かに無いが、その土台の**凸幾何の Carathéodory は Mathlib にある** (`Mathlib/Analysis/Convex/Caratheodory.lean:124` / `:149`、loogle 実測)。⟹ 「自作コストが読めない」の根拠は弱まる。ただし濃度固定版で止める結論自体は変わらない (Phase 2 の到達目標には不要) |

---

## 1. 外界 union の形 (逐語) — 内界 union の設計を縛る 4 点

### 1-A. `IsUVChannelLaw` (`OuterBoundUV/Region.lean:104`)

section 変数 (`Region.lean:78`–`:80`, `:86`):
`{α : Type*} [MeasurableSpace α]` / `{β₁ : Type*} [MeasurableSpace β₁]` /
`{β₂ : Type*} [MeasurableSpace β₂]` / `{U V : Type*} [MeasurableSpace U] [MeasurableSpace V]`

```lean
def IsUVChannelLaw (W : BCChannel α β₁ β₂) (ν : Measure (U × V × α × β₁ × β₂)) : Prop :=
  ν.map (fun q ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2))
    = (ν.map fun q ↦ (q.1, q.2.1, q.2.2.1)) ⊗ₘ
        W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)
```

`Fintype` / `DecidableEq` / `StandardBorelSpace` / `Nonempty` を**一切要求しない**。

### 1-B. `uvRegion` (`Region.lean:259`) と `bcOuterRegionUV` (`Region.lean:271`)

section 変数 (`Region.lean:251`–`:253`) が追加で効く:
`[StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β₁] [Nonempty β₁] [StandardBorelSpace β₂] [Nonempty β₂]`

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

**内界 union の設計を縛る 4 点 (逐語確認)**:

| 軸 | 外界の実装 | 内界への含意 |
|---|---|---|
| 補助変数の添字 | **`ℕ` 固定**。型の量化も `Fin k` の union もしていない (`Type 0`) | 内界は `ℕ` を採れない (§2 案 C の反例)。⟹ **添字が一致しないのは避けられない**。等号は「両辺とも `Set (ℝ × ℝ)`」で並べる |
| 束縛の形 | `ProbabilityMeasure` の**束ね型**で確率性を担保し、構造条件は `⋃ (_ : IsUVChannelLaw W ν)` の Prop binder | 内界も同じ `⋃ (_ : Prop)` パターンが使える。in-project 先例は MAC (`TimeSharingConverse/Assembly.lean:308` の `⋃ (q₁ : Measure α₁) (q₂ : Measure α₂) (_ : IsProbabilityMeasure q₁) (_ : IsProbabilityMeasure q₂), macPentagon q₁ q₂ W`) |
| closure の位置 | union の**外側 1 回だけ**。`uvRegion` 自体は取らない | 内界も外側 1 回。理由も同じ (半平面交差の union は閉じない + 操作的領域が closure) |
| 位相 | `Set (ℝ × ℝ)` の標準位相 (`closure` は `Mathlib/Topology/Closure.lean` の一般形) | 同じ |

`IsUVChannelLaw` の量化は **union の添字の側** に入る (`⋃ ν, ⋃ (_ : IsUVChannelLaw W ν), …`)。
定義本体 `uvRegion` はチャネルを引数に取らない (判断ログ 9 の反例 class を閉じるための設計)。

---

## 2. 内界 union の定義候補と判定

`martonRegion` の実測インスタンス要求 (`Operational.lean:109`–`:114` の section 変数):
`{V₁ V₂ α β₁ β₂ : Type*}` の 5 本すべてに
`[Fintype _] [DecidableEq _] [Nonempty _] [MeasurableSpace _] [MeasurableSingletonClass _]`。
ただし **elaborate 後に実際に効くのは少ない** — probe1 の `#check` 実測:

```
@martonRegionUnion : {α : Type u_4} → {β₁ : Type u_5} → {β₂ : Type u_6} →
  [inst : MeasurableSpace α] → [Fintype β₁] → [inst_2 : MeasurableSpace β₁] →
  [Fintype β₂] → [inst_4 : MeasurableSpace β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)
```

⟹ **union の定義そのものが要求するのは `[MeasurableSpace α]` + `[Fintype β₁] [MeasurableSpace β₁]`
+ `[Fintype β₂] [MeasurableSpace β₂]` の 5 本だけ** (`α` の `Fintype` すら不要)。
定理の側で 5×5 が要るのは `marton_region_subset_capacity` / `marton_region_subset_uv` の都合。

### 案 A — 濃度固定 `Fin (k+1)` + `k` について union (plan §Phase 2 が推す形)

```lean
noncomputable def martonRegionUnion (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k₁ : ℕ) (k₂ : ℕ) (pV : Measure (Fin (k₁ + 1) × Fin (k₂ + 1)))
    (_ : IsProbabilityMeasure pV) (K : Kernel (Fin (k₁ + 1) × Fin (k₂ + 1)) α)
    (_ : IsMarkovKernel K), martonRegion pV K W)
```

| 判定軸 | 結果 |
|---|---|
| インスタンスは自動で付くか | **付く** (probe1 EXIT=0)。`Fintype` / `DecidableEq` / `Nonempty` / `MeasurableSpace` / `MeasurableSingletonClass` の 5 本すべてが `Fin (k+1)` に対して `inferInstance` で通る |
| `k = 0` で壊れるか | **`Fin (k+1)` 形にすれば壊れない**。`Nonempty (Fin 0)` は偽なので `Fin k` 素形は不可 — 添字を `k` にして `Fin (k+1)` と書くこと |
| 等号で型が並ぶか | 並ぶ (両辺 `Set (ℝ × ℝ)`) |
| 橋の持ち上げコスト | **6 行** (probe2 / probe6 で `sorry` ゼロ実測) |
| closure は要るか | **要る** (相手が closure。取らないと等号が型としては並んでも成立しえない) |
| ⚠ 弱点 | `Fin (k+1) : Type 0`。`α : Type u` のとき `IsBCLessNoisy` に渡せない (§3、probe5 逐語エラー) |

### 案 A′ — 案 A の補助アルファベットを `ULift.{u}` で α の universe に載せる ★**推奨**

```lean
/-- Auxiliary alphabet of cardinality `k + 1`, in the universe of the input alphabet. -/
abbrev bcAuxAlphabet.{v} (k : ℕ) : Type v := ULift.{v} (Fin (k + 1))

noncomputable def martonRegionUnion (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k₁ : ℕ) (k₂ : ℕ)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂))
    (_ : IsProbabilityMeasure pV)
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α)
    (_ : IsMarkovKernel K), martonRegion pV K W)
```
(`universe u` + `variable {α : Type u}`、`Classes.lean:45`–`:47` と同じ宣言の仕方)

案 A の全長所を保ったまま弱点が消える。**probe6 が EXIT=0 / `sorry` 0 で 4 本まとめて確認**:
`martonRegionUnion_subset_uv` / `martonRegionUnionFS_subset_capacity` /
`martonRegionUnionFS_subset_union` / `hln (bcAuxAlphabet.{u} k) pU K` の適用。
ULift のインスタンス 5 本 (`Fintype` / `DecidableEq` / `Nonempty` / `MeasurableSpace` /
`MeasurableSingletonClass`) はすべて `inferInstance` で出る (probe5-b、EXIT=0)。
`ULift.fintype` は `Mathlib/Data/Fintype/Basic.lean:160`、
`ULift.instMeasurableSpace` は `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:63`。

### 案 B — 型の量化 `⋃ (V₁ V₂ : Type u) …`

**不採用**。`Set.iUnion` は `ι : Sort*` に対して universe 多相なので elaborate 自体は通るが、
`u` を固定した瞬間「`Type u` の有限型についての union」でしかなく、任意 universe 版との一致に
`ULift` 経由の付け替え不変性が要る = L-BCO2 そのもの。案 A′ は**同じ結論をより安く**得る
(`ULift` を定義に組み込むので付け替え不変性の証明が不要)。加えて binder が
`[Fintype V] [DecidableEq V]` という Prop でないデータを含むので、`iUnion_subset` 系の分解が
案 A′ より一段深くなる。

### 案 C — 外界と同じ `ℕ` 添字の 5 つ組法に内界も載せる ❌ **数学的に偽**

「等号の両辺を同じ添字集合に載せる」という点では最も魅力的で、しかも
`martonInfo*` → `uvInfo*` の同定 3 本 (`MartonBridge.lean:228` / `:240` / `:252`) が既にあるので
安そうに見える。**が、順包含が偽になる**。

反例 class (`.toReal` の退化を突く。判断ログ 9 の外界側の反例 class の内界版):

- `α = β₁ = β₂ = Bool`、`W a = dirac (a, a)` (両受信機が `X` を無損失で受ける)
- `N : ℕ` を `H(N) = ∞` の分布とし `X` と独立にとる。`U = V = (X, N)` を `ℕ` に符号化
- `IsUVChannelLaw W ν` は成立 (出力は `X` からしか作られない)
- `uvInfo₁ ν = I(V;Y₁) = log 2`、`uvInfo₂ ν = I(U;Y₂) = log 2`
- 補助間依存 `I(U;V) = H(U) = ∞` ⟹ **`.toReal = 0`** (`ENNReal.toReal_top = 0`)
- ⟹ 内界の和レート制約が `R₁ + R₂ ≤ log 2 + log 2 - 0` に緩む
- 一方 `uvInfoSum₂ ν = I(U;Y₂) + I(X;Y₁ ∣ U) = log 2 + 0 = log 2`
- ⟹ 点 `(log 2, log 2)` は内界に入り外界に入らない。**しかもこの点は容量領域外**
  (この BC の容量は合計 1 bit) ⟹ 内界ですらない

**構造的な理由 (これが案 C を殺す一般則)**: 外界の 4 スロットは**すべて出力との情報量**なので
有限出力アルファベットの下で自動的に有限。内界の 3 スロットのうち `I(V₁;V₂)` **だけが
補助 × 補助**で、補助が無限アルファベットだと発散しうる。⟹ **外界は `ℕ` に載せられるが内界は
載せられない。この非対称性は `.toReal` 規約の帰結であって設計の選択ではない。**

裏づけの機械確認: `mutualInfo_ne_top` (`InformationTheory/Shannon/MutualInfo.lean:174`) は
`[Fintype X] [MeasurableSingletonClass X] [Fintype Y] [MeasurableSingletonClass Y]` を要求
(probe1 の `#check` 逐語)。`condMutualInfo_ne_top` (`Shannon/CondMutualInfo.lean:320`) は
3 アルファベット全部に `[Fintype _] [MeasurableSingletonClass _]` + 2 本に
`[StandardBorelSpace _] [Nonempty _]`。⟹ `ℕ` 補助では S5 の有限性補題が 1 本も使えない。

### 判定表

| | 案 A | **案 A′ (推奨)** | 案 B | 案 C |
|---|---|---|---|---|
| (i) 等号で外界と型が並ぶ | ○ | ○ | ○ | ○ |
| (ii) 橋 `marton_region_subset_uv` の持ち上げ | 6 行 (実測) | **6 行 (実測)** | 6 行 + universe 転送 | 偽 |
| (iii) closure が要る | 要る | 要る | 要る | — |
| `IsBCLessNoisy` の適用 | ✗ (probe5 逐語エラー) | **○ (probe6 実測)** | ○ | — |
| 判定 | 消費側で詰む | **採用** | 高い | **偽** |

---

## 3. L-BCO2 の再検証 — 「解けた」ではなく「定義側で回避・消費側で再出現」

### 3-A. plan の記述

plan `:441` は L-BCO2 に「実質的に前倒しで解けている公算。honesty 監査が `Type u` 版 ⟹
任意 universe 版を probe のコンパイルで確認 (`Fintype.equivFin` + `Equiv.ulift` +
`compProd_comap_map_prodMap` 2 回 + `mutualInfo_map_comp`)。**この probe は in-tree に落ちていない**」
と書いている。

### 3-B. 判定 (機械確認)

**案 A / A′ を採るなら、universe 量化そのものが定義に現れないので L-BCO2 の発動条件
「Phase 2 の型量化 union が universe 問題で詰む」には到達しない = 回避。**
ただし *解けた* ではない。理由は次の 2 点で、どちらも本 leg で機械確認した。

1. **消費側で同じ問題が出る (逐語エラー、probe5)**。`α : Type u` の下で
   `hln : IsBCLessNoisy W` を `Fin (k+1)` に当てると:

   ```
   probe5.lean:21:6: error: Application type mismatch: The argument
     Fin (k + 1)
   has type
     Type
   of sort `Type 1` but is expected to have type
     Type u
   of sort `Type (u + 1)` in the application
     @hln (Fin (k + 1))
   ```

   ⟹ **L-BCO2 の本体は「union の添字を何にするか」ではなく「`IsBCLessNoisy` が
   `U : Type u` を量化していること」だった** (`Classes.lean:63`–`:68`)。

2. **`ULift.{u}` を定義に組み込めば 0 行で消える (probe6 EXIT=0)**。
   `hln (bcAuxAlphabet.{u} k) pU K` がそのまま型検査を通る。
   ⟹ plan が言う「probe を書き下し直す」作業は**不要になる** — `Fintype.equivFin` +
   `Equiv.ulift` による付け替え不変性を証明する代わりに、**最初から `ULift` の側で定義する**。

### 3-C. 残る 1 点 — 「`Fin` の union は型量化の union と同じ強さか」

案 A′ の union は「濃度 `k+1` の ULift された補助」を走る。任意の有限 `V₁ V₂` (ULift でない、
別 universe の型) についての `martonRegion pV K W` がこの union に入ることは**自明ではない**。
必要なのは補助アルファベットの付け替え不変性で、**その中核は本 leg で 48 行・EXIT=0 で実測済**
(§9-1)。⟹ この 1 本を書けば「回避」は「答えた」になる。**Phase 2 の必須項目ではない**
(Phase 5 は補助を自分で構成するので `Fin` 形に取れる) が、API としては推奨。

---

## 4. gateway atom — 実測 (両向き)

すべて `lake env lean <probe>` の実測。probe は scratchpad。

### 4-A. 順向き — **`sorry` ゼロで通った (probe2 / probe6、EXIT=0)**

```lean
theorem martonRegionUnion_subset_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonRegionUnion W ⊆ bcOuterRegionUV W := by
  refine closure_minimal ?_ (bcOuterRegionUV_isClosed W)
  refine Set.iUnion_subset fun k₁ ↦ Set.iUnion_subset fun k₂ ↦ Set.iUnion_subset fun pV ↦
    Set.iUnion_subset fun hpV ↦ Set.iUnion_subset fun K ↦ Set.iUnion_subset fun hK ↦ ?_
  exact marton_region_subset_uv pV K W
```

使った Mathlib は `closure_minimal` (`Mathlib/Topology/Closure.lean:199`) と
`Set.iUnion_subset` (`Mathlib/Data/Set/Lattice.lean:142`) の 2 本だけ。
**`⋃ (_ : IsProbabilityMeasure pV)` の Prop binder は `Set.iUnion_subset` がそのまま剥がす**
(binder を `fun hpV ↦` で受けると instance がスコープに入るので `haveI` も不要 — 実測)。

### 4-B. 達成側の持ち上げ — **`sorry` ゼロで通った (probe3 / probe6、EXIT=0)**

全支持を添字に入れた版 `martonRegionUnionFS` に対して:

```lean
theorem martonRegionUnionFS_subset_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) :
    martonRegionUnionFS W ⊆ bcCapacityRegion W := by
  refine closure_minimal ?_ (bc_capacityRegion_isClosed W)
  refine Set.iUnion_subset fun k₁ ↦ … fun hKpos ↦ ?_
  exact marton_region_subset_capacity pV K W hpVpos hKpos hW
```

`martonRegionUnionFS ⊆ martonRegionUnion` も 9 行で通る
(`closure_mono` + `Set.subset_iUnion_of_subset` 6 段、`Mathlib/Data/Set/Lattice.lean:186`)。

**⚠ ここが Phase 2 の本当の設計判断**: `marton_region_subset_capacity` (`Operational.lean:154`) は
`hpV` / `hK` / `hW` の全支持 3 本を要求する。`hW` はチャネル側なので定理の明示仮説にできるが、
**`hpV` / `hK` は union の binder の内側**なので、無制約 union に対しては当てられない。
⟹ 「無制約 union ⊆ 容量領域」は**摂動 (全支持への近似) が要る** (§9-2)。

### 4-C. 逆向き — **型では塞がっていない (案 A / A′ で `Fintype ℕ` 閉塞が消えた)**

```lean
theorem uv_subset_martonRegionUnion (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    bcOuterRegionUV W ⊆ martonRegionUnion W := by sorry
```

probe2 で **elaborate する** (警告は `declaration uses sorry` のみ)。
前 leg の逐語エラー `failed to synthesize instance of type class Fintype ℕ`
(`bc-inner-outer-bridge-inventory.md` §4-B) は**再現しない**。理由: 前 leg は `ℕ` 添字の法を
`martonInfo*` に直接食わせようとしたが、案 A / A′ では `ℕ` 添字の法から**有限補助を構成する**
向きになるので、`martonInfo*` が `ℕ` に触れない。

⟹ **L-BCO8 の形は変わる**。詳細は §11。

### 4-D. その他の実測

| 主張 | 判定 |
|---|---|
| `⋃ (k₁ k₂ : ℕ)` と 1 binder に 2 名前 | **構文エラー** `unexpected identifier; expected ')'`。`⋃ (k₁ : ℕ) (k₂ : ℕ)` と分ける (実測) |
| `Convex ℝ (martonRegion pV K W)` | **通る。15 行** (probe3 EXIT=0)。`[IsProbabilityMeasure pV]` も `[IsMarkovKernel K]` も**不要** |
| `Fin 0` の `Nonempty` | 出ない ⟹ 添字は `Fin (k+1)` 形 |
| ULift の 5 インスタンス | 全部 `inferInstance` (probe5-b EXIT=0) |
| 補助付け替えの中核 `martonJointDistribution_map_relabel` | **48 行・EXIT=0・`sorry` 0** (probe4、§9-1) |

---

## 5. less noisy の等号から見た要求

### 5-A. `IsBCLessNoisy` (逐語、`Classes.lean:63`)

section 変数 (`Classes.lean:45`–`:50`): `universe u` / `variable {α : Type u} {β₁ β₂ : Type*}` +
`α β₁ β₂` それぞれに `[Fintype _] [DecidableEq _] [Nonempty _] [MeasurableSpace _] [MeasurableSingletonClass _]`

```lean
def IsBCLessNoisy (W : BCChannel α β₁ β₂) : Prop :=
  ∀ (U : Type u) [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U]
      [MeasurableSingletonClass U] (pU : Measure U) [IsProbabilityMeasure pU]
      (K : Kernel U α) [IsMarkovKernel K],
    mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.2)
      ≤ mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.1)
```

**`U : Type u` が §3 の全て**。案 A′ を採ればここは無傷で通る (probe6)。

### 5-B. degraded の既存の等号 — **存在しない**

`rg` 実測: `Set (ℝ × ℝ)` レベルの degraded 容量領域は in-repo に**無い**。あるのは
点ごとの述語 `InBCCapacityRegion` (`BroadcastChannel/Basic.lean:200`、2 field) と、
それを使う floating 形の `bc_degraded_converse` (`Converse.lean:571`) / `bc_achievability`
(`Achievability/Assembly.lean:1093`)。両者とも direct consumer 0 (plan 判断ログ 11-(p))。
⟹ **「degraded の形をそのまま一般化する」道は存在しない**。等号は Phase 4b/5 の集合語彙で
新規に立てるしかない (plan 判断ログ 11-(p) の「接続ではなく新規実装」がここでも当てはまる)。

### 5-C. union の定義は等号を述べるのに十分か — **十分。ただし残る 1 本が全部**

Phase 2 完了後に成立する挟み込み (すべて §4 で実測):

```
martonRegionUnionFS W ⊆ martonRegionUnion W ⊆ bcOuterRegionUV W
martonRegionUnionFS W ⊆ bcCapacityRegion W ⊆ bcOuterRegionUV W     (右は Phase 4b)
```

⟹ **less noisy の等号に残るのは 1 本の包含だけ**:

```lean
theorem bc_lessNoisy_uv_subset_marton (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hln : IsBCLessNoisy W) (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) :
    bcOuterRegionUV W ⊆ martonRegionUnionFS W
```

これが入れば 4 つの集合が一斉に等しくなる:

```lean
theorem bc_lessNoisy_capacity_eq (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hln : IsBCLessNoisy W) (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) :
    bcCapacityRegion W = bcOuterRegionUV W
```

**`hW` は正則性前提 (全支持) で load-bearing ではない**が、less noisy クラスとの両立は
確認済 — degraded の全支持例が存在する (plan `:212`)。semi-deterministic (L-BCO7) と違い
定義上破れることはない。

⚠ `hW` を消したいなら L-BCO7 の後継 plan `bc-semideterministic-fullsupport` と同じ軸。

---

## 6. 時分割 / 凸包 — **要らない (根拠つき)**

| 問い | 判定 | 根拠 |
|---|---|---|
| 各 `martonRegion` は凸か | **凸** | probe3 EXIT=0、15 行。3 本の線形不等式の交差なので測度仮説すら不要 |
| union は凸か | **一般には非凸** | 四辺形の和集合。時分割変数 `Q` を補助に吸収する標準手は Marton では効かない — `V₁' = (Q,V₁)`, `V₂' = (Q,V₂)` とすると `I(V₁';V₂') = H(Q) + I(V₁;V₂ ∣ Q)` で**罰則項が `H(Q)` だけ増える** (human-judgment) |
| convex hull を定義に入れるべきか | **入れない** | (a) hull の達成側が無い — BC の時分割は in-repo に不在。MAC の `mac_avgPentagon_mem_convexHull` (`TimeSharingConverse/Bridge.lean:99`) は **converse 側**の道具で、BC 4b は既に不採用 (plan `:53`)。(b) 相手側 `bcOuterRegionUV` も非凸のままなので両辺が並ぶ。(c) less noisy の 2 制約領域は `U' = (Q,U)` で `Q` を吸収できる (corner 制約しかないので罰則項が出ない) ⟹ 第一目標では不要 |

⚠ **正直な限界の明記**: この `martonRegionUnion` は**時分割変数を持たない Marton 内界**で、
EGK Thm 8.3 の `⋃ p(q,u,v,x)` 版より (一般には真に) 小さい。plan にこの一行を残すべき。

MAC 側の資産の所在だけ記録する (**BC では不採用なので逐語展開はしない** — 必要になったら
`MultipleAccess/TimeSharingConverse/Bridge.lean:99`–`:207` = `mac_avgPentagon_mem_convexHull` +
補助 `convexHull_mem_of_le:30` を Read すること)。

---

## 7. API 在庫テーブル

### 7-A. 内界側 (union が包む対象)

| 概念 | API | file:line | 状態 | Phase 2 での扱い |
|---|---|---|---|---|
| 内界の点ごと述語 | `structure InMartonRegion (R₁ R₂ I₁ I₂ I₁₂ : ℝ) : Prop` — field `bound₁ : R₁ ≤ I₁` / `bound₂ : R₂ ≤ I₂` / `boundSum : R₁ + R₂ ≤ I₁ + I₂ - I₁₂` | `Marton/Basic.lean:40` | ✅ 既存 | union の被 union 側の中身。**触らない** |
| 内界の集合版 | `def martonRegion (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ)` | `Operational.lean:127` | ✅ 既存 | union の被 union 項。**触らない** |
| 3 つの情報量 | `noncomputable def martonInfo₁ / martonInfo₂ / martonInfoV₁V₂ (pV) (K) (W) : ℝ` (entropy 差、`ℝ` 値) | `Marton/Setup.lean:244` / `:252` / `:262` | ✅ 既存 | `ℝ` 値ゆえ `[Fintype]` 必須 — 案 C を殺す根源 |
| 達成側 | `theorem marton_region_subset_capacity (pV) [IsProbabilityMeasure pV] (K) [IsMarkovKernel K] (W) [IsMarkovKernel W] (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a}) (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) : martonRegion pV K W ⊆ bcCapacityRegion W` (`@[entry_point]`) | `Operational.lean:154` | ✅ 既存 | 全支持 3 本が union 化の唯一の障害 (§9-2) |
| 操作的領域 | `def bcCapacityRegion (W) : Set (ℝ × ℝ) := closure {p | BCAchievable W p.1 p.2}` / `theorem bc_capacityRegion_isClosed` | `Operational.lean:68` / `:102` | ✅ 既存 | `closure_minimal` の第 2 引数 |

section 変数 (`Operational.lean:109`–`:114`、`martonRegion` / `marton_region_subset_capacity` 共通):
`{V₁ V₂ α β₁ β₂ : Type*}` の 5 本すべてに
`[Fintype _] [DecidableEq _] [Nonempty _] [MeasurableSpace _] [MeasurableSingletonClass _]`

### 7-B. 橋 (union へ持ち上げる対象)

| 概念 | API | file:line | 状態 | Phase 2 での扱い |
|---|---|---|---|---|
| 順包含 (橋 S6) | `theorem marton_region_subset_uv (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV] (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] : martonRegion pV K W ⊆ bcOuterRegionUV W` (`@[entry_point]`) | `OuterBoundUV/MartonBridge.lean:530` | ✅ 既存 | **そのまま `exact` で使う** (§4-A)。全支持仮説を 1 本も要求しない (判断ログ 15) |
| `ℕ` 化した Marton 法 | `noncomputable def martonUVLaw (pV) (K) (W) : Measure (ℕ × ℕ × α × β₁ × β₂)` + `theorem martonUVLaw_isUVChannelLaw` (`@[entry_point]`) | `MartonBridge.lean:160` / `:177` | ✅ 既存 | 橋の内部。Phase 2 は触らない |
| 補助の `ℕ` 符号化 | `noncomputable def natIndex (X : Type*) [Fintype X] (x : X) : ℕ := Fintype.equivFin X x` / `natIndex_injective` | `Shannon/BroadcastChannel/OuterBoundUV/MartonBridge.lean` | ✅ 既存 | `ULift (Fin (k+1))` に対しても `[Fintype]` だけで通る |
| 情報量の同定 3 本 | `martonInfo₁_eq_uvInfo₁_toReal` / `martonInfo₂_eq_uvInfo₂_toReal` / `martonInfoV₁V₂_eq_mutualInfo_toReal` | `MartonBridge.lean:228` / `:240` / `:252` | ✅ 既存 | 案 C が「安そうに見えた」原因。Phase 2 では使わない |
| 和レート 2 本 (橋 S5) | `martonInfoSum_le_uvInfoSum₂_toReal` / `…₁_toReal` | `MartonBridge.lean:493` / `:509` | ✅ 既存 | 同上 |

section 変数 (`MartonBridge.lean:143`–`:148`): `Operational.lean` と同じ 5×5。

### 7-C. 外界側 (union の相手)

| 概念 | API | file:line | 状態 | Phase 2 での扱い |
|---|---|---|---|---|
| チャネル法の述語 | `def IsUVChannelLaw (W) (ν : Measure (U × V × α × β₁ × β₂)) : Prop` (§1-A に逐語) | `Region.lean:104` | ✅ 既存 | 内界 union の binder 設計の雛形 |
| 特徴づけ | `lemma isUVChannelLaw_iff (W) (ν) : IsUVChannelLaw W ν ↔ ν = ((ν.map fun q ↦ (q.1, q.2.1, q.2.2.1)) ⊗ₘ W.comap … ).map (fun z ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2))` | `Region.lean:125` | ✅ 既存 | 逆包含 (L-BCO8) で ν を分解するときの入口 |
| 外界 | `def bcOuterRegionUV (W) : Set (ℝ × ℝ)` (§1-B に逐語) | `Region.lean:271` | ✅ 既存 | 等号の右辺 |
| 閉性 | `theorem bcOuterRegionUV_isClosed (W) : IsClosed (bcOuterRegionUV W)` | `Region.lean:277` | ✅ 既存 | `closure_minimal` の第 2 引数 (§4-A) |
| 下方集合性 | `theorem bcOuterRegionUV_isLowerSet (W) : IsLowerSet (bcOuterRegionUV W)` | `Region.lean:291` | ✅ 既存 | 退化レート被覆。Phase 2 では未使用 |
| 非空 | `theorem bcOuterRegionUV_nonempty (W) [IsMarkovKernel W] : (bcOuterRegionUV W).Nonempty` | `Region.lean:343` | ✅ 既存 | union が空でない証拠の雛形 (内界にも同型の `martonRegionUnion_nonempty` を作れる) |
| 補助入替不変 | `lemma IsUVChannelLaw.swap_auxiliaries {W} [IsMarkovKernel W] {ν} [SFinite ν] (h) : IsUVChannelLaw W (ν.map fun q ↦ (q.2.1, q.1, q.2.2))` | `Region.lean:203` | ✅ 既存 | 橋の内部 |
| 4 スロット | `uvInfo₁ / uvInfo₂ (ν : Measure (U × V × α × β₁ × β₂)) : ℝ≥0∞` / `uvInfoSum₂ / uvInfoSum₁ (ν) [IsFiniteMeasure ν] : ℝ≥0∞` | `OuterBoundUV/Bridge.lean:777` / `:782` / `:787` / `:792` | ✅ 既存 | 全部「補助 × 出力」or「入力 × 出力 ∣ 補助」= 有限出力なら有限 (§2 案 C) |
| 補助の付け替え不変 4 本 | `uvInfo₁_map_uvRelabel` / `uvInfo₂_map_uvRelabel` / `uvInfoSum₂_map_uvRelabel` / `uvInfoSum₁_map_uvRelabel` | `OuterBoundUV/Assembly.lean:143` / `:155` / `:175` / `:195` | ✅ 既存 | §9-1 で内界版を作るときの終盤で使える |

### 7-D. クラス側 (Phase 5 の入口)

| 概念 | API | file:line | 状態 | Phase 2 での扱い |
|---|---|---|---|---|
| less noisy | `def IsBCLessNoisy (W) : Prop` (§5-A に逐語、`∀ (U : Type u) …`) | `Classes.lean:63` | ✅ 既存 | **union の補助を `Type u` に置く理由そのもの** |
| more capable | `def IsBCMoreCapable (W) : Prop := ∀ (p : Measure α) [IsProbabilityMeasure p], mutualInfoOfChannel p (Kernel.snd W) ≤ mutualInfoOfChannel p (Kernel.fst W)` | `Classes.lean:75` | ✅ 既存 | universe 問題なし (`Measure α` を量化) |
| 包含鎖 | `IsBCDegraded.isBCLessNoisy` / `IsBCLessNoisy.isBCMoreCapable` (両方 `@[entry_point]`) | `Classes.lean:133` / `:218` | ✅ 既存 | Phase 5 |
| 重ね合わせ和 | `theorem bc_lessNoisy_infoJoint_ge {U : Type u} [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U] (pU) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K] (W) [IsMarkovKernel W] (hln : IsBCLessNoisy W) : bcInfo₁ pU K W + bcInfo₂ pU K W ≤ bcInfoJoint pU K W` (`@[entry_point]`) | `Classes.lean:95` | ✅ 既存 | **`{U : Type u}` — ここも ULift が要る側** |

### 7-E. Mathlib 側 (Phase 2 が実際に使ったもの)

| 概念 | Mathlib API | file:line | 状態 | Phase 2 での扱い |
|---|---|---|---|---|
| closure の最小性 | `theorem closure_minimal (h₁ : s ⊆ t) (h₂ : IsClosed t) : closure s ⊆ t` | `Mathlib/Topology/Closure.lean:199` | ✅ 既存 | 順包含・達成側の両方の骨格 |
| closure の単調性 | `theorem closure_mono (h : s ⊆ t) : closure s ⊆ closure t` | `Mathlib/Topology/Closure.lean:232` | ✅ 既存 | FS 版 ⊆ 無制約版 |
| closure への包含 | `theorem subset_closure : s ⊆ closure s` | `Mathlib/Topology/Closure.lean:193` | ✅ 既存 | 単一領域 ⊆ union |
| iUnion の消去 | `theorem iUnion_subset {s : ι → Set α} {t : Set α} (h : ∀ i, s i ⊆ t) : ⋃ i, s i ⊆ t` | `Mathlib/Data/Set/Lattice.lean:142` | ✅ 既存 | binder 6 段を `fun … ↦` で剥がす。**Prop binder (`IsProbabilityMeasure`) もそのまま剥がれる (実測)** |
| iUnion への包含 | `theorem subset_iUnion_of_subset {s : Set α} {t : ι → Set α} (i : ι) (h : s ⊆ t i) : s ⊆ ⋃ i, t i` | `Mathlib/Data/Set/Lattice.lean:186` | ✅ 既存 | FS 版 ⊆ 無制約版 |
| ULift の Fintype | `instance ULift.fintype (α : Type*) [Fintype α] : Fintype (ULift α)` | `Mathlib/Data/Fintype/Basic.lean:160` | ✅ 既存 | 案 A′ |
| ULift の可測構造 | `instance _root_.ULift.instMeasurableSpace : MeasurableSpace (ULift α) := ‹MeasurableSpace α›.map ULift.up` | `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:63` | ✅ 既存 | 案 A′ |
| ULift の可測同値 | `MeasurableEquiv` between `ULift α` and `α` | `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:353` | ✅ 既存 | §9-1 (付け替え不変性) を書くなら使う |
| `negMulLog` の連続性 | `@[fun_prop] lemma Real.continuous_negMulLog : Continuous negMulLog` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:186` | ✅ 既存 | §9-2 (a) の摂動で entropy の連続性を組むときの原子 |
| 凸幾何の Carathéodory | `theorem Caratheodory.convexHull_eq_union : convexHull 𝕜 s = ⋃ …` / `theorem Caratheodory.minCardFinsetOfMemConvexHull_card_le_card {t : Finset E} (ht₁ : ↑t ⊆ s) …` | `Mathlib/Analysis/Convex/Caratheodory.lean:149` / `:124` | ✅ 既存 | L-BCO8 の route (i) (補助変数の濃度上界) の土台。**Phase 2 では使わない** |
| 合成積と comap の交換 | `lemma compProd_comap_map_prodMap {A A' B : Type*} [MeasurableSpace A] [MeasurableSpace A'] [MeasurableSpace B] (μ : Measure A) [SFinite μ] (κ : Kernel A' B) [IsMarkovKernel κ] {g : A → A'} (hg : Measurable g) : (μ ⊗ₘ κ.comap g hg).map (fun z ↦ (g z.1, z.2)) = (μ.map g) ⊗ₘ κ` | `InformationTheory/Shannon/ChannelCoding/CodeToAmbient.lean:346` (in-project) | ✅ 既存 | §9-1 の中核。**2 回使う** |

---

## 8. 要注意の前提 (事故りやすい順)

- **`marton_region_subset_capacity` の全支持 3 本 `hpV` / `hK` / `hW`** —
  `hW` はチャネル側なので定理の明示仮説にできるが、`hpV` / `hK` は **union の binder の内側**。
  無制約 union に対して当てられない。これが Phase 2 の唯一の実質的な設計判断 (§9-2)。
- **`marton_region_subset_uv` は全支持を 1 本も要求しない** (判断ログ 15、S6 まで不変)。
  ⟹ **順包含の持ち上げは無条件**。達成側だけが条件付き。左右で条件が非対称なことを
  等号の署名に忘れず反映すること。
- **`IsBCLessNoisy` の `U : Type u`** — §3。union の補助を `Type 0` に置くと Phase 5 で詰む。
- **`uvRegion` / `martonRegion` の `.toReal`** — `⊤ ↦ 0`。**外界では安全 (スロットが全部
  出力との情報量なので有限)、内界では危険 (`I(V₁;V₂)` が補助 × 補助)**。判断ログ 11-(m) が
  「危険は無限アルファベット拡張の 1 軸だけ」としたのは外界についてのみ正しい。
- **`⋃` の binder は 1 グループ 1 名前** — `⋃ (k₁ k₂ : ℕ)` は構文エラー (実測)。
- **`Fin k` ではなく `Fin (k+1)`** — `Nonempty` が `k = 0` で出ない。
- **union に `IsProbabilityMeasure` / `IsMarkovKernel` の binder を入れ忘れないこと** —
  入れないと `pV` が確率測度でない添字まで走り、内界が容量領域を超えうる
  (外界側の同型の事故 = 判断ログ 9 の反例 class の内界版)。

---

## 9. 自作が要るもの (優先度順)

### 9-1. 補助アルファベットの付け替え不変性 (**中核 48 行を実測済 / 残り ~60 行**)

Phase 2 の必須項目ではない (§3-C) が、これを書くと L-BCO2 が「回避」から「答えた」になる。

**中核は EXIT=0 / `sorry` 0 で通った (probe4、48 行)**:

```lean
theorem martonJointDistribution_map_relabel
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K' : Kernel (V₁' × V₂') α) [IsMarkovKernel K']
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (e₁ : V₁ → V₁') (e₂ : V₂ → V₂') (he₁ : Measurable e₁) (he₂ : Measurable e₂) :
    martonJointDistribution (pV.map (fun v ↦ (e₁ v.1, e₂ v.2))) K' W
      = (martonJointDistribution pV
          (K'.comap (fun v ↦ (e₁ v.1, e₂ v.2)) …) W).map (fun q ↦ (e₁ q.1, e₂ q.2.1, q.2.2))
```

要求インスタンスは `[MeasurableSpace _]` 5 本と `[IsProbabilityMeasure pV] [IsMarkovKernel K']
[IsMarkovKernel W]` だけ。**`Fintype` も全支持も不要**。機構は `compProd_comap_map_prodMap`
(`CodeToAmbient.lean:346`) を 2 回 + `Kernel.ext fun _ ↦ rfl` + `Measure.map_map` の押し出し。
**落とし穴 (実測)**: 最後の `Measure.map_map` は `prodAssoc ∘ prodAssoc` を**付け替え前と
付け替え後の 2 つの型で別々に**用意しないと `Application type mismatch` になる。

残り: 3 スロットの不変性 (`martonInfo₁/₂/V₁V₂` が付け替えで変わらない) と、
`Fintype.equivFin` + `MeasurableEquiv.ulift` で任意有限型を `ULift (Fin (k+1))` へ運ぶ組み立て。
`uvInfo*_map_uvRelabel` (`Assembly.lean:143`–`:199`) と同定 3 本 (`MartonBridge.lean:228`–`:260`)
を経由すれば **~60 行**。⟹ **合計 ~110 行**。

### 9-2. 全支持仮説の除去 (**Phase 2 の唯一の実質判断。~120–200 行、または撤退**)

無制約 union に達成側を持ち上げるには次のどちらかが要る:

- **(a) 単一領域レベルで強める** — `marton_region_subset_capacity` から `hpV` / `hK` を落とす。
  機構: `pVε = (1-ε)·pV + ε·uniform`、`Kε = (1-ε)·K + ε·uniform` は全支持で、
  `ε → 0` で `martonInfo*` が収束 ⟹ `bcCapacityRegion` が閉なので極限点が入る。
  必要な自作は**有限アルファベット上の entropy の測度についての連続性**。
  in-repo 検索 (`rg "Continuous.*entropy|Tendsto.*entropy"`) では**該当なし** —
  出てくるのは LZ78 / EPI / EntropyRate の別軸の Tendsto のみ。Mathlib 側は
  `@[fun_prop] lemma Real.continuous_negMulLog : Continuous negMulLog`
  (`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:186`) があるので、
  有限和に持ち込めれば素直。**~120–200 行**。
  **波及は実測ゼロ**: `scripts/dep_consumers.sh
  InformationTheory.Shannon.BroadcastChannel.Marton.marton_region_subset_capacity` は
  **direct consumer 0 decl / 0 file** (4826 decl を逆引き)。⟹ 署名を強める (仮説を落とす)
  変更で touch が要る宣言は 1 本も無い。
- **(b) union に全支持を入れる** — `martonRegionUnionFS` (§4-B、**7 行で実測済**)。
  ただし逆包含 (L-BCO8) が「全支持な有限補助を構成せよ」に強まる。

**推奨: 定義は無制約 1 本 (`martonRegionUnion`) とし、達成側は
`martonRegionUnionFS` を経由する 2 段で出す**。無制約版の達成側が閉じない間は
`sorry` + `@residual(plan:bc-marton-fullsupport-perturbation)` が正直な出口
(署名は証明したい形のまま。述語束ねは禁止)。

### 9-3. union の非空性 / 下方集合性 (**各 ~10 行、任意**)

外界に `bcOuterRegionUV_nonempty` (`Region.lean:343`) / `_isLowerSet` (`Region.lean:291`) が
あるので対を作れる。`martonRegion` の下方集合性は `InMartonRegion` の 3 field から 3 行。
非空性は `pV = dirac`、`K = const` の定数法で証拠を出す (`uvConstLaw` `Region.lean:299` が雛形)。

---

## 10. Mathlib の壁 — **0 件**

`@residual(wall:…)` を立てる対象は**無い**。根拠は「探して 0 hit」ではなく
**「Phase 2 の到達目標を probe が実際に通した」** (§4-A / 4-B / 4-D、いずれも EXIT=0 / `sorry` 0)。
CLAUDE.md の壁ガード (loogle 0-hit は必要条件にすぎない / 二段階の結論形検索 /
テンプレ補題の名指し) を通す必要のある主張が本 leg には 1 件も残らなかった。

§9 の 3 件はいずれも **in-project の自作**であって Mathlib の欠落ではない:

- 9-1 は `compProd_comap_map_prodMap` (in-project) + `Measure.map_map` (Mathlib) の組み立て
  ⟹ **plumbing**。中核 48 行が既に通っている
- 9-2 の entropy 連続性は「Mathlib に `entropy` の定義自体が無い」(本 project の自作語彙) ので
  Mathlib の壁ではなく**自作語彙の未整備**。`Real.negMulLog` の連続性は Mathlib にある
- 9-3 は 10 行の定型

**共有 sorry 補題は不要** (同じ穴が複数ファイルに散る構図が無い)。

---

## 11. 撤退ラインとの距離

| slug | 触れるか | 発動するか | 判定の根拠 |
|---|---|---|---|
| **L-BCO2** (Phase 2 の型量化 union が universe 問題で詰む) | **触れる** | **不発動** | 案 A′ は型量化を持たないので発動条件に到達しない。ただし plan の「実質的に解けている」は誤り — 問題は定義側ではなく**消費側 (`IsBCLessNoisy` の `U : Type u`)** にあり、probe5 が逐語エラーで機械確認。`ULift.{u}` を定義に組み込むことで **0 行で解消** (probe6 EXIT=0)。⟹ plan が要求する「probe の書き下し直し」は**不要**。文言は凍結なので残し、判定は「回避 + 消費側を ULift で吸収」と読み替える |
| **L-BCO8** (逆包含で `ℕ` 補助を `[Fintype]` に合わせられない) | **触れる** | **形が変わる (発動判定は Phase 5 に持ち越し)** | 前 leg の逐語エラー `failed to synthesize instance of type class Fintype ℕ` は**再現しない** (§4-C、probe2 で elaborate)。案 A′ では `ℕ` 添字の法から**有限補助を構成する**向きになるので型では塞がらない。残るのは数学: (i) Carathéodory 型の濃度上界、または (ii) **`ℕ` 補助の有限量子化 + 内界 union の `closure` による極限回収**。(ii) は内界が closure である以上**構造的に可能な形**で、前 leg には無かった選択肢。⟹ **L-BCO8 は「型で不可能」から「近似の宿題」に降格**。(i) の土台は Mathlib にある — 凸幾何の Carathéodory (`Caratheodory.convexHull_eq_union`, `Mathlib/Analysis/Convex/Caratheodory.lean:149` / `Caratheodory.minCardFinsetOfMemConvexHull_card_le_card`, `:124`) が存在し、情報理論側の補助変数濃度上界 (Ahlswede–Körner の support lemma) はこれの上に載る。ただし (i)(ii) いずれも本 leg では未検証 (human-judgment) |
| **L-BCO3** (Phase 5 の等号が外界の形と噛み合わない) | 触れる | **不発動** | 在庫 §7 の指摘どおり噛み合わなさの本体は内界の形で、その 3 点のうち union 欠如が本 leg で解消する。残りは符号制約 (解消済 `2c938fe0`) と全支持 (L-BCO7 / §9-2) |
| **L-BCO7** (semi-deterministic の全支持) | 触れない | 不発動 | Phase 2 は `hW` を定義に入れないので無関係。§9-2 の (a) が閉じれば `hpV` / `hK` は消えるが `hW` は残る |

**新しい撤退ラインの提案は無し**。§9-2 が閉じない場合の出口は
`sorry` + `@residual(plan:bc-marton-fullsupport-perturbation)` で、これは L-BCO7 の退避先
(`@residual(plan:bc-semideterministic-fullsupport)`) と**同じ軸の別 plan**。
「全支持を消す」を 1 本の後継 plan にまとめる選択肢もある (オーケストレーター判断)。

**禁止事項の再掲**: どの退避でも「union が取れる」「摂動で近似できる」を `*Hypothesis` 述語に
束ねて仮説として渡す形は取らない (CLAUDE.md tier 5)。署名は証明したい形のまま。

---

## 12. 攻略順と行数見積り

S1–S6 の実績 (予想 50/30/40/25/150-250/40 → 実測 45/22/95/35/257/29、判断ログ 14 の
「超過は数学ではなく署名の反復」) を踏まえ、**署名の反復ぶんを +50% 見込んだ**値。

| step | 何を示すか | 予想行数 | 依存 | 実測状況 |
|---|---|---|---|---|
| **P1** | `bcAuxAlphabet` + `martonRegionUnion` の定義 | 12 | — | **probe6 で elaborate 確認済** |
| **P2** | `martonRegionUnion_subset_uv` (順包含の持ち上げ) | 10 | P1 | **probe6 で EXIT=0 / `sorry` 0 実測 (6 行)** |
| **P3** | `martonRegionUnionFS` の定義 + `_subset_union` + `_subset_capacity` | 30 | P1 | **probe6 で EXIT=0 / `sorry` 0 実測 (計 25 行)** |
| **P4** | `martonRegionUnion_isLowerSet` / `_nonempty` (外界と対を作る) | 30 | P1 | 未実測。`Region.lean:291` / `:343` が雛形 |
| **P5** | `Convex ℝ (martonRegion pV K W)` (§6 の記録として残すなら) | 20 | — | **probe3 で EXIT=0 実測 (15 行)** |
| **P6** | 付け替え不変性 (§9-1、L-BCO2 を「答えた」にする) | 110 | P1 | 中核 48 行が **probe4 で EXIT=0 / `sorry` 0 実測** |
| **P7** | 全支持の除去 (§9-2 (a)) | 180 | P3 | 未着手。閉じなければ `sorry` + `@residual` |

**P1–P3 (60 行) が Phase 2 の最小完遂**で、これは既に probe6 が丸ごと通している。
P4–P5 は安い付け足し。**P6 / P7 は独立に価値が出る別 step** で、park 可
(P6 は API の完全性、P7 は Phase 5 の等号を無条件にするため)。

**Phase 5 (less noisy) に渡す残り 1 本**は `bcOuterRegionUV W ⊆ martonRegionUnionFS W`
(§5-C)。これは Phase 2 の範囲外。

**壁ガードについて**: 本 leg は壁を 1 件も宣言していない (§10) ので、
「loogle 0-hit → 二段階の結論形検索 → テンプレ補題の名指し」を通す必要のある主張が無い。
§9-2 の entropy 連続性だけは「in-repo に無い」を `rg` の 2 軸 (名前 `Continuous.*entropy` /
結論形 `Tendsto.*entropy`) で確認したが、これは**壁ではなく自作語彙の未整備**なので
`@residual(wall:…)` の対象にはしない。

---

## 13. 出発点の骨格 (`InformationTheory/Shannon/BroadcastChannel/MartonUnion.lean`)

配置の判断: `martonRegion` (`Operational.lean`) と `bcOuterRegionUV` / `marton_region_subset_uv`
(`OuterBoundUV/MartonBridge.lean`) の**両方**を引くので、`MartonBridge.lean` の下流に置く。
`MartonBridge.lean` は `OuterBoundUV/Assembly.lean` 経由で `Operational.lean` に届いている
(import 閉包で確認済 — probe6 は `MartonBridge` + `Classes` の 2 本だけで全部通った)。
新規ファイルは `InformationTheory.lean` に import 行を追加すること。

```lean
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Classes
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.MartonBridge

/-!
# Broadcast channel — Marton's inner bound as a union over auxiliary alphabets

`martonRegion` is the quadrilateral of one fixed pair of auxiliary alphabets, whereas the UV
outer region is a union over five-tuple laws.  This file takes the union on the inner side, so
that the two regions can be compared as sets.

The auxiliaries range over `ULift (Fin (k + 1))`, one cardinality at a time, in the universe of
the input alphabet: fixing the cardinality avoids quantifying over types, and the universe lift
is what lets the comparison classes be applied at a member of the union.  A countable auxiliary
alphabet is not available here, unlike on the outer side: the dependence between the two
auxiliaries is the one information slot reading no output letter, so it is the one that can be
infinite, and the `toReal` convention would then drop the sum-rate penalty.

## Main definitions

* `bcAuxAlphabet k` — the auxiliary alphabet of cardinality `k + 1`.
* `martonRegionUnion W` — Marton's inner bound, as the closure of the union of `martonRegion`
  over the auxiliary laws on those alphabets.
* `martonRegionUnionFS W` — the same union restricted to the full-support indices, which is the
  form the achievability theorem applies to.

## Main statements

* `martonRegionUnion_subset_uv` — the union sits inside the UV outer region.
* `martonRegionUnionFS_subset_capacity` — the full-support union sits inside the operational
  capacity region.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The auxiliary alphabet of cardinality `k + 1`, in the universe of the input alphabet. -/
abbrev bcAuxAlphabet (k : ℕ) : Type u := ULift.{u} (Fin (k + 1))

/-- Marton's inner bound as a subset of the plane: the closure of the union of the
quadrilaterals `martonRegion pV K W` over the auxiliary laws on `bcAuxAlphabet`. -/
noncomputable def martonRegionUnion (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k₁ : ℕ) (k₂ : ℕ)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂))
    (_ : IsProbabilityMeasure pV)
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α)
    (_ : IsMarkovKernel K), martonRegion pV K W)

/-- The union restricted to the indices on which the achievability theorem applies. -/
noncomputable def martonRegionUnionFS (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k₁ : ℕ) (k₂ : ℕ)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂))
    (_ : IsProbabilityMeasure pV) (_ : ∀ v, 0 < pV.real {v})
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α)
    (_ : IsMarkovKernel K) (_ : ∀ v a, 0 < (K v).real {a}), martonRegion pV K W)

@[entry_point]
theorem martonRegionUnion_subset_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonRegionUnion W ⊆ bcOuterRegionUV W := by
  sorry

theorem martonRegionUnionFS_subset_union (W : BCChannel α β₁ β₂) :
    martonRegionUnionFS W ⊆ martonRegionUnion W := by
  sorry

@[entry_point]
theorem martonRegionUnionFS_subset_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) :
    martonRegionUnionFS W ⊆ bcCapacityRegion W := by
  sorry

end InformationTheory.Shannon.BroadcastChannel.Marton
```

3 本の `sorry` はいずれも probe6 が実際に埋めている (順に 6 / 9 / 7 行) ので、
**この骨格は 1 回の fill で proof done に到達する**見込み。
`@[entry_point]` を 2 本に付けているのは、`## Main statements` 掲載定理を裸にしないため
(plan §後続作業 C-5 / F-8 の `internal-doc` ratchet 衝突を、`Classes.lean` と同じ既定手で回避)。

# BC「degraded との接続」— M0 在庫

> **親計画**: [`bc-general-region-plan.md`](bc-general-region-plan.md)（SoT）。該当は §推奨実行順 #3 /
> §Phase 5「残るクラス」/ §存在しないもの (d) / 判断ログ 11-(n)。
> 本ファイルは在庫のみ。`.lean` と plan は編集していない。

## 結論サマリ

- **主目標は実現可能。Mathlib の壁 0 件 / in-project の壁 0 件**（BC 家系 10 leg 連続 → 11 leg 目）。
- 使う API のうち **Mathlib 側は 100% 既存**。ただし「per-letter の二段分解を pi 積の外に出す」補題は
  **Mathlib に無い**（`Measure.pi` × `Measure.compProd` の照会は `Found 0 declarations`）。これが本 leg の
  **新しい数学 1 本**で、**probe で証明済（78 行、warning 0）**。
- **ただし `h_deg_block` は「1 本」では着地しない**。probe で分解した結果、
  **自作 6 本 + 既存 private 2 本の移設** が要る（内訳は §Q4-3）。
  「新しい数学 1 本 + 配線」というブリーフの構図自体は正しいが、
  **配線の中身が pi 積の再結合で、親 plan の粗見積り `~120 行` は下振れ**（2 枠見積りで **帯 350–480**、§Q8）。
- 既存資産の再利用可否は**ブリーフの想定と 1 点ずれた**（§Q3-2）:
  `bcConverse_memoryless₁` の骨格（`isMarkovChain_of_compProd_pi` 一族）は **効かない**。
  効くのは**達成側の degradedness 雛形** `bcMarkovChain_UX_Y₁_Y₂` / `bcDegraded_append` /
  `isMarkovChain_of_append`（`Achievability/Assembly.lean`）で、**後 2 者は `private`** ⟹ **移設が要る**。
- 型クラス前提は **`bc_degraded_converse` の束（Converse.lean:39–48）のままで足りる**。
  `IsBCDegraded` は `[MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]` **だけ**を要求する
  （`#check` 実測。`Fintype` / `DecidableEq` / `Nonempty` は**混入しない**）。
  `[StandardBorelSpace β₁]` 等の追加も**不要**。

### 最も危ない発見（1 行）

**`isMarkovChain_of_append`（`Achievability/Assembly.lean:814`）と
`kernel_compProd_prodMkRight_eq_prod`（同 `:801`）は `private`**。
`private` は **file-scoped**（CLAUDE.md §Project Layout）なので、新規ファイルからは import しても呼べない。
この 2 本こそが degradedness → Markov 鎖の唯一の橋なので、
**移設（public 化 + 上流ファイルへ移動）を実装 leg の最初の 1 手に入れないと、45 行の再実装（重複）に化ける**。
direct consumer は `rg` 実測で **各 1 箇所**（`Assembly.lean:853` / `:958`）＝ 今が最安。

---

## Q1 到達点の署名案（すべて probe で elaborate 済 = §Q6）

### Q1-1 主目標（新しい数学 + 配線の終点）

`bc_degraded_converse` の `h_deg_block`（`Converse.lean:588`–`:592` の逐語）を ambient で担う 1 本:

```lean
lemma bcConverse_degBlock
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (hdeg : IsBCDegraded W) (i : Fin n) :
    IsMarkovChain (bcConverseAmbient c W) (bcConverseY₁s i)
      (fun ω ↦ (bcConverseMsg₂ ω,
        fun (j : Fin i.val) ↦ bcConverseY₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      (fun ω (j : Fin i.val) ↦ bcConverseY₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω)
```

**逐語確認**（`Converse.lean:588`–`:592`、ブリーフの概形と一致）:

```lean
    (h_deg_block : ∀ i : Fin n,
      IsMarkovChain μ (Y₁s i)
        (fun ω ↦ (W₂ ω,
          fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
        (fun ω (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
```

`IsMarkovChain μ Xs Zc Yo`（`Shannon/CondMutualInfo.lean:90`）は **`Xs ⫫ Yo ∣ Zc`**（第 2 引数が条件付け）
なので、意味は **`Y₁ᵢ ⫫ Y₂^{<i} ∣ (W₂, Y₁^{<i})`**。

### Q1-2 配線（第 2 目標）

`bc_uv_converse_from_code`（`Bridge.lean:567`）を逐語の雛形にした ambient 版:

```lean
theorem bc_converse_from_code
    [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hdeg : IsBCDegraded W) (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    InBCCapacityRegion (Real.log (M₁ : ℝ)) (Real.log (M₂ : ℝ))
      ((∑ i : Fin n,
          condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i) (bcConverseY₁s i)
            (fun ω ↦ (bcConverseMsg₂ ω,
              fun (j : Fin i.val) ↦ bcConverseY₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))).toReal
        + bcConverseFanoSlack₁ c W)
      ((∑ i : Fin n,
          mutualInfo (bcConverseAmbient c W)
            (fun ω ↦ (bcConverseMsg₂ ω,
              fun (j : Fin i.val) ↦ bcConverseY₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
            (bcConverseY₂s i)).toReal
        + bcConverseFanoSlack₂ c W)
```

**probe で確認した当たり**（見積りを 1 段下げる）: `bc_degraded_converse` の結論に出る Fano 項

```lean
MeasureFano.errorProb μ W₁ (fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω)) (fun p ↦ c.decoder₁ p.2)
```

は ambient で **`bcConverseFanoSlack₁ c W`（`Bridge.lean:537`）の中身と `rfl` で一致する**
（`errorProb μ Xs Yo dec = μ.real {ω | Xs ω ≠ dec (Yo ω)}`（`Fano/Measure.lean:89`）なので、
観測が対 `(W₂, Y₁ⁿ)` でも decoder が第 2 成分しか見ないなら**集合が literally 同じ**）。
probe `example … := rfl` が通っている（§Q6 probe 3）⟹ **Fano 項の橋渡し補題は 0 本**。
さらに `bcConverse_errorProb₁_eq`（`Bridge.lean:470`）で符号の平均誤り確率まで落とせる（本 leg の必須ではない）。

### Q1-3 スコープの提案（ブリーフの問い「どこまでを本 leg にするか」）

| 段 | 内容 | 推奨 | 理由 |
|---|---|---|---|
| (a) | `bcConverse_degBlock` のみ | ❌ | consumer 0 のまま。`bc_degraded_converse` は今も direct consumer **0 decl / 0 file**（`dep_consumers.sh` 実測）で、それが解消しない |
| (b) | (a) + `bc_converse_from_code` | ✅ **本 leg のスコープ** | `bc_uv_converse_from_code` と同じ高さに degraded 版が並ぶ。`bc_degraded_converse` に consumer が 1 本付く |
| (c) | (b) + レート抽出 `bc_converse_rate_extract` | ⚠ 見送り推奨 | 雛形の `bc_uv_rate_extract` が**現に dead**（親 plan §後続作業 B-1、direct consumer 0）。**dead な双子を増やすだけ** |
| (d) | (b) + `bcCapacityRegion` への着地 | ❌ 別 leg | 領域レベルは **more capable で既に閉じている**（下記） |

**重要（本 leg の位置づけの正確な把握）**: 領域レベルの degraded 等号は**すでに手に入っている**。
`IsBCDegraded.isBCLessNoisy`（`Classes.lean:133`）+ `IsBCLessNoisy.isBCMoreCapable`（`:218`）で
`bc_moreCapable_capacity_eq_uv` の系になる。**probe で 2 行で通ることを実測済**（§Q6 probe 6）:

```lean
theorem bc_degraded_capacity_eq_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hdeg : IsBCDegraded W) :
    bcCapacityRegion W = bcOuterRegionUV W := by
  classical
  exact bc_moreCapable_capacity_eq_uv W hW hdeg.isBCLessNoisy.isBCMoreCapable
```

`classical` で `DecidableEq` が埋まる（親 plan 判断ログ 28-(b) の再現）ので、
**署名に `[DecidableEq _]` は要らない**（`IsBCDegraded.isBCLessNoisy` は `[DecidableEq α] [DecidableEq β₁]
[DecidableEq β₂]` を要求する＝`#check` 実測、それでも corollary 側には漏れない）。

⟹ **本 leg の価値は「領域の等号」ではなく「Cover–Thomas Thm 15.6.2 の古典形 converse
（`U = (W₂, Y₂^{i-1})`）を操作的に着地させること」**。この 1 点を実装 brief に明記すること
（親 plan §Phase 5「残るクラス」の文言「degraded との接続は『新規配線の作成』」と整合）。

---

## Q2 目標の真偽判定

**真**。degradedness `W a = ((W a).map fst).bind (fun y₁ ↦ (Q y₁).map (y₁, ·))`
（`Achievability/Setup.lean:45`–`:47` 逐語）から、ambient では
`Y₂^{<i}` の条件付き法が `∏_{j<i} Q(Y₁ⱼ)`＝**`Y₁^{<i}` だけの関数**になる。
条件付け側 `(W₂, Y₁^{<i})` は `Y₁^{<i}` を含むので、`Y₁ᵢ` を足しても条件付き法が変わらない
⟹ `Y₁ᵢ ⫫ Y₂^{<i} ∣ (W₂, Y₁^{<i})`。

### Q2-1 退化境界 2 つ（構造の違うもの）+ 最も一般な対象の再検査

| 退化 | 挙動 | 判定 |
|---|---|---|
| `i = 0`（前置きが空） | `Fin 0 → β₂` は subsingleton。条件付き独立は自明に真 | 生存（反証にならない）|
| `Q = Kernel.const _ ν`（degrading が入力を見ない） | `Y₂ⁿ` は独立ノイズ。鎖は自明に真 | 生存 |
| 最も一般な対象（全仮説を満たす一般形）: 任意の `W` で `Q` が非自明、符号 `c` が `W₁` を `Xᵢ` に強く結合 | `Y₂^{<i}` は `Y₁^{<i}` 経由でしか `W₁` を見ない ⟹ 依然成立 | 生存 |

### Q2-2 仮説が load-bearing でないことの確認（逆向きの検算）

**degradedness を外すと偽**: 一般 BC では `Y₂ⱼ` が `Y₁ⱼ` を超えて `Xⱼ` を見るので、
`Y₂^{<i}` → `X^{<i}` → `W₁` → `Xᵢ` → `Y₁ᵢ` の情報経路が残り、条件付き独立は破れる。
⟹ `hdeg` は**チャネルの構造前提**であって「証明の核を束ねた仮説」ではない
（`IsBCDegraded` の docstring も "A structural precondition … not a load-bearing hypothesis" と明言）。
`bc_degraded_converse` 側も `h_deg_block` を precondition として受けており（`@audit:ok`）、本 leg はその
**担い手を実際に構成する**側なので、誠実性の階層は Tier 1 を狙える（`sorry` 不要の見込み）。

---

## Q3 ブリーフの 3 つの核心的な問いへの回答

### Q3-1 「pi 積の外に二段分解を出す」補題は Mathlib / in-project にあるか → **無い（自作 = 本 leg の新しい数学）**

- Mathlib: `MeasureTheory.Measure.pi` と `MeasureTheory.Measure.compProd` を**両方**言及する宣言は
  **`Found 0 declarations`**。`Measure.pi` × `Measure.bind` も **`Found 0 declarations`**（§Q7 に逐語）。
- in-project: `.bind` の出現は `Achievability/Setup.lean:47`（定義）と
  `Achievability/Assembly.lean:865`（`bcDegraded_append` の仮説）の **2 箇所のみ**（`rg` 実測）。
  pi 積レベルの二段分解は**存在しない**。
- ⟹ 自作。**ただし結論形を `bind` ではなく `⊗ₘ` で書くと下流が全部つながる**
  （CLAUDE.md「Mathlib-shape-driven Definitions」）:

```lean
lemma pi_unzip_eq_compProd {k : ℕ} (Q : Kernel β₁ β₂) [IsMarkovKernel Q]
    (ρ : Fin k → Measure (β₁ × β₂)) [∀ j, IsProbabilityMeasure (ρ j)]
    (hρ : ∀ j, ρ j = ((ρ j).map Prod.fst).bind fun y₁ ↦ (Q y₁).map fun y₂ ↦ (y₁, y₂)) :
    (Measure.pi ρ).map (fun y ↦ ((fun j ↦ (y j).1), (fun j ↦ (y j).2)))
      = (Measure.pi fun j ↦ (ρ j).map Prod.fst) ⊗ₘ qBlock Q
```

**probe 実測 39 行（+ 補助 `degraded_singleton` 28 行 + `qBlock` 定義と instance 9 行 = 78 行）で証明済**。
攻略路は **singleton 評価**（有限アルファベットなので `Measure.ext_of_singleton` が使える）:
`Measure.pi_singleton` で両辺を `∏ⱼ` に落とし、per-letter の degradedness を singleton で使って
`Finset.prod_mul_distrib` で畳む。**box（`Measure.pi_eq`）路も lintegral 路も要らなかった**。

### Q3-2 ★既存 Markov 資産は効くか → **`isMarkovChain_of_compProd_pi` 一族は効かない**（ブリーフ想定との差分）

| 資産 | file:line | 本 leg で効くか | 理由 |
|---|---|---|---|
| `isMarkovChain_of_compProd_pi` | `CodeToAmbient.lean:210` | ❌ **効かない** | 結論が `IsMarkovChain (ν ⊗ₘ κ) F (fun ω ↦ x ω.1 i) (fun ω ↦ ω.2 i)` に**固定**。中央（条件付け）が**入力文字 `Xᵢ`**、右端が**文字 `i` の出力**。本 leg の鎖は中央が `(W₂, Y₁^{<i})`、右端が**他文字のブロック** `Y₂^{<i}` で形が違う |
| `compProd_pi_map_pair_eq_of_update_invariant` | `CodeToAmbient.lean:396` | ❌ | 同じ「文字 `i` の update 不変性」枠。`W` を**不透明なカーネル**として扱うので degradedness を一切見ない ⟹ 本 leg の核（`Q` の存在）を出せない |
| `isMemorylessChannel_of_compProd_pi` | `CodeToAmbient.lean:322` | ❌ | 同上 |
| `isMarkovChain_swap` | `CondEntropyMemoryless.lean:330` | ✅ 端点入替に使う（使うなら） | 汎用 |
| `isMarkovChain_map_left` | `CondMutualInfo.lean:578` | ✅ 端点の後処理に使う（使うなら） | 汎用 |
| `isMarkovChain_map_comp` | `CodeToAmbient.lean:496` | △ 使わない見込み | ambient を map で移す必要が無い |
| **`isMarkovChain_of_append`** | **`Achievability/Assembly.lean:814`（`private`）** | ✅ **これが本命** | 「`Bs` が `Zc` からカーネル `Q` で append される」なら `As → Zc → Bs`。degradedness 専用の入口 |
| **`kernel_compProd_prodMkRight_eq_prod`** | **同 `:801`（`private`）** | ✅ 上の内部で必須 | 同上 |
| `bcDegraded_append` / `bcMarkovChain_UX_Y₁_Y₂` | 同 `:859` / `:941` | ✅ **証明骨格の雛形**（宣言は再利用不可） | **一文字版**の同じ命題。ブロック版が本 leg |

**`bcConverse_memoryless₁`（`Bridge.lean:306`–`:345`、40 行）との 1 行ずつの突き合わせ結果**:
骨格は `isMarkovChain_of_compProd_pi` → `swap` → `map_left` → `swap` の 4 段だが、
**第 1 段が使えない**時点で骨格ごと不成立。残る 3 段（`swap` / `map_left`）は端点の整形にすぎず、
本 leg で節約できるのは数行。⟹ **雛形は `bcConverse_memoryless₁` ではなく `bcMarkovChain_UX_Y₁_Y₂`**
（親 plan 判断ログ 11-(f)「雛形を却下するときは宣言と証明骨格のどちらを却下したかまで書く」に従い明記:
`bcConverse_memoryless₁` は**証明骨格を却下**、`bcDegraded_append` は**宣言を却下・証明骨格を採用**）。

### Q3-3 型クラス前提の差分 → **増えない**

- `IsBCDegraded` の `#check` 実測:
  `{α β₁ β₂} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] → BCChannel α β₁ β₂ → Prop`。
  置き場の `variable` 束（`Setup.lean:31`–`:35` の `Fintype`/`DecidableEq`/`Nonempty`/
  `MeasurableSingletonClass`）は**この def には 1 つも含まれない**。
- `bc_degraded_converse` 側は α / β₁ / β₂ すべてに
  `[Fintype _] [MeasurableSpace _] [MeasurableSingletonClass _] [StandardBorelSpace _] [Nonempty _]`
  （`Converse.lean:39`–`:48` 逐語）。**`bcConverse_degBlock` はこの束のままで elaborate する**（probe 1）。
- `[StandardBorelSpace β₁]` 等の**追加は不要**。`Q : Kernel β₁ β₂` を扱うが、
  β₁ が `Fintype + MeasurableSingletonClass` なので **`Kernel.ofFunOfCountable` で可測性が無料**になり、
  disintegration 系の前提は要らない。
- `IsMarkovChain` 自体が `[StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]`
  （X = `β₁`、Y = `Fin i.val → β₂`）を要求するが、`Pi.instMeasurableSingletonClass`
  （`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:726`）と有限性から**自動で埋まる**（probe 1 で確認）。

---

## Q4 資産表

### Q4-1 Mathlib（**すべて既存**、`[...]` は逐語）

| 概念 | Mathlib API | file:line | 結論形（逐語） | 本 leg での扱い |
|---|---|---|---|---|
| 可算空間の測度の外延性 | `MeasureTheory.Measure.ext_of_singleton [Countable α] {μ ν : Measure α} (h : ∀ a, μ {a} = ν {a}) : μ = ν` | `Mathlib/MeasureTheory/Measure/Dirac.lean:111` | `μ = ν` | ★ `pi_unzip_eq_compProd` の入口。有限アルファベットだから使える |
| 積測度の点質量 | `MeasureTheory.Measure.pi_singleton [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i)` | `Mathlib/MeasureTheory/Constructions/Pi.lean:300` | `Measure.pi μ {f} = ∏ i, μ i {f i}` | ★ 両辺を `∏` に落とす |
| 積測度の箱 | `MeasureTheory.Measure.pi_pi [∀ i, SigmaFinite (μ i)] (s : (i : ι) → Set (α i))` | 同 `:292` | `Measure.pi μ (pi univ s) = ∏ i, μ i (s i)` | P1（部分族への射影）で使う |
| 積測度の特徴づけ | `MeasureTheory.Measure.pi_eq [∀ i, SigmaFinite (μ i)] {μ' : Measure (∀ i, α i)} (h : ∀ s, (∀ i, MeasurableSet (s i)) → μ' (pi univ s) = ∏ i, μ i (s i))` | 同 `:280` | `Measure.pi μ = μ'` | P1 の骨格 |
| 座標ごと push-forward | `MeasureTheory.Measure.pi_map_pi [∀ i, MeasurableSpace (Y i)] {f} [hμ : ∀ i, SigmaFinite ((μ i).map (f i))] (hf : ∀ i, AEMeasurable (f i) (μ i))` | 同 `:389` | `(Measure.pi μ).map (fun x i ↦ (f i (x i))) = Measure.pi (fun i ↦ (μ i).map (f i))` | P3 で `Y₁` 周辺法の積を出す |
| 有限空間の lintegral | `MeasureTheory.lintegral_fintype [MeasurableSingletonClass α] [Fintype α] (f : α → ℝ≥0∞)` | `Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean:153` | `∫⁻ x, f x ∂μ = ∑ x, f x * μ {x}` | ★ compProd / bind を有限和に落とす |
| compProd の値 | `MeasureTheory.Measure.compProd_apply [SFinite μ] [IsSFiniteKernel κ] {s} (hs : MeasurableSet s)` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:61` | `(μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ` | ★ 同上 |
| bind の値 | `MeasureTheory.Measure.bind_apply {m f s} (hs : MeasurableSet s) (hf : AEMeasurable f m)` | `Mathlib/MeasureTheory/Measure/GiryMonad.lean:235` | `bind m f s = ∫⁻ a, f a s ∂m` | ★ degradedness を singleton で開く |
| compProd の第 2 成分 map | `MeasureTheory.Measure.compProd_map [SFinite μ] [IsSFiniteKernel κ] {f : β → γ} (hf : Measurable f)` | `Mathlib/Probability/Kernel/Composition/Lemmas.lean:120` | `μ ⊗ₘ (κ.map f) = (μ ⊗ₘ κ).map (Prod.map id f)` | ★ P0 の核 |
| compProd の結合律 | `MeasureTheory.Measure.compProd_assoc {η : Kernel (α × β) γ}` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:230` | `(μ ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm = μ ⊗ₘ κ ⊗ₘ η` | P3 で `(m, Y₁ⁿ)` を条件付けに繰り上げる |
| 可算空間のカーネル生成 | `ProbabilityTheory.Kernel.ofFunOfCountable [MeasurableSpace α] {_ : MeasurableSpace β} [Countable α] [MeasurableSingletonClass α] (f : α → Measure β)` | `Mathlib/Probability/Kernel/Basic.lean:237` | `Kernel α β` | ★ `qBlock` の構成（**`Kernel.pi` 不在の回避路**）|
| カーネルの comap 版 | `ProbabilityTheory.Kernel.prodMkRight (γ) (κ : Kernel α β) : Kernel (α × γ) β` / `prodMkLeft` | `Mathlib/Probability/Kernel/Composition/MapComap.lean:241` / `:237` | — | `isMarkovChain_of_append` の要求形 |
| condDistrib の一意性 | `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd (X) (hY : AEMeasurable Y μ) {κ} [IsFiniteKernel κ] (hκ : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ)` | `Mathlib/Probability/Kernel/CondDistrib.lean:163` | `condDistrib Y X μ =ᵐ[μ.map X] κ` | `isMarkovChain_of_append` の内部（移設先で import 必須）|
| pi の singleton class | `Pi.instMeasurableSingletonClass [Countable δ] [∀ a, MeasurableSingletonClass (X a)]` | `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:726` | — | `Fin i → β₂` に自動発火 |

**照会したが使わなかったもの（記録）**: `ProbabilityTheory.iIndepFun_pi`
（`Mathlib/Probability/Independence/Basic.lean:892`）+
`ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun`（`Independence/Integration.lean:135`）で
「`∫⁻ ∏ⱼ fⱼ(yⱼ) ∂(Measure.pi ν) = ∏ⱼ ∫⁻ fⱼ ∂νⱼ`」は組めるが、**singleton 路が通ったので不要**。
lintegral 版の `integral_fintype_prod_eq_prod`（`Mathlib/MeasureTheory/Integral/Pi.lean:106` は Bochner のみ）は
**Mathlib に無い**が、本 leg では迂回できた。

### Q4-2 in-project（既存、逐語再利用）

| 資産 | file:line | 本 leg での役割 |
|---|---|---|
| `bc_degraded_converse` | `Converse.lean:571` | 配線先。**direct consumer 0 decl / 0 file**（`dep_consumers.sh` 実測）|
| `bcConverseAmbient` / `bcConverseInput` / `bcConverseKernel` | `Bridge.lean:146` / `:117` / `:128` | ambient 本体。`bcConverseKernel c W m = Measure.pi (fun i ↦ W (c.encoder m i))`（`:131` 逐語）|
| `bcConverseMsg₁/₂` `bcConverseY₁s/Y₂s` + 可測性 5 本 | `Bridge.lean:160`–`:195` | 射影 |
| `bcConverseMsg₁_uniform` / `bcConverseMsg₂_uniform` | `Bridge.lean:234` / `:246` | `hW₁_uniform` / `hW₂_uniform` の担い手 ✅ |
| `bcConverse_mutualInfo_eq_zero` | `Bridge.lean:258` | `h_indep` ✅ |
| `bcConverse_memoryless₁` | `Bridge.lean:306` | `h_memo` ✅（骨格は本 leg では**流用不可**、§Q3-2）|
| `bcConverse_isMarkovChain₁` | `Bridge.lean:399` | `hmarkov` ✅ |
| `bcConverse_msgPair_eq_fst` | `Bridge.lean:229` | `(Msg₁ ω, Msg₂ ω) = ω.1` の書換（配線で使う）|
| `bcConverseFanoSlack₁` / `₂` | `Bridge.lean:537` / `:546` | 配線先の結論に出る Fano 項（`rfl` 一致、§Q1-2）|
| `bcConverse_errorProb₁_eq` / `₂_eq` | `Bridge.lean:470` / `:501` | 符号の平均誤り確率への落とし（任意）|
| `bc_uv_converse_from_code` | `Bridge.lean:567` | 配線の**逐語の雛形**（46 行）|
| `compProd_comap_map_prodMap` | `CodeToAmbient.lean:346` | ★ P0 の相方（第 1 成分側の map）|
| `isMarkovChain_of_append` / `kernel_compProd_prodMkRight_eq_prod` | `Achievability/Assembly.lean:814` / `:801`（**private**）| ★ 本命の入口。**移設が要る** |
| `bcDegraded_append` / `bcMarkovChain_UX_Y₁_Y₂` | 同 `:859`（82 行）/ `:941`（19 行）| 一文字版の**証明骨格の雛形**＋行数の較正錘 |
| `IsBCDegraded` | `Achievability/Setup.lean:45` | 仮説。direct consumer **4 decl / 2 file**（`dep_consumers.sh` 実測）|
| `IsBCDegraded.isBCLessNoisy` / `IsBCLessNoisy.isBCMoreCapable` | `Classes.lean:133` / `:218` | 任意の系（§Q1-3）|

### Q4-3 自作が要るもの（**6 本 + 移設 2 本**、優先度順）

| # | 名前（案） | 内容 | 状態 | 見積り |
|---|---|---|---|---|
| 1 | `degraded_singleton` | per-letter degradedness を singleton で読む | ✅ **probe 証明済** | 28（実測）|
| 2 | `qBlock` + `IsMarkovKernel` instance | ブロック degrading カーネル `u ↦ Measure.pi (fun j ↦ Q (u j))` | ✅ **probe 証明済** | 9（実測）|
| 3 | **`pi_unzip_eq_compProd`（★ gateway atom）** | pi 積の二段分解を `⊗ₘ` 形で出す（**本 leg の新しい数学**）| ✅ **probe 証明済** | 39（実測）|
| 4 | `compProd_map_prodMap`（P0、汎用） | `(ρ ⊗ₘ κ).map (Prod.map f g) = (ρ.map f) ⊗ₘ κ'`（カーネルの依存が `f` を経由するとき）| ✅ **probe 証明済** | 14（実測、証明本体は 4 行）|
| 5 | `pi_map_comp_injective`（P1、汎用） | `(Measure.pi ν).map (fun y j ↦ y (e j)) = Measure.pi (fun j ↦ ν (e j))`（`e` 単射）| 署名のみ elaborate | 25–35 |
| 6 | `bcConverse_block_append`（P3） | ambient のブロック append（`(m, Y₁ⁿ)` に `Y₂ⁿ` が `qBlock` で付く）| 署名のみ elaborate | 60–90 |
| 7 | `bcConverse_prefix_append`（P4） | 文字 `i` の前置きへの射影（#4 を 1 回叩く）| 署名のみ elaborate | 35–50 |
| 8 | **`bcConverse_degBlock`（P5、主目標）** | `isMarkovChain_of_append` + 可測性 | 署名のみ elaborate | 25–35 |
| 9 | `bc_converse_from_code`（P6、配線） | `bc_degraded_converse` の instantiate | 署名のみ elaborate | 50–65 |
| M | **移設**: `isMarkovChain_of_append` + `kernel_compProd_prodMkRight_eq_prod` | `private` を外して上流へ | — | 移動 58 行（**純増 0**）+ import 調整 |

---

## Q5 前提が事故りやすい箇所（key-preconditions box）

- **`isMarkovChain_of_append` の `h_app` は「条件付けが第 1 成分」の形**:
  `μ.map (fun ω ↦ ((Zc ω, As ω), Bs ω)) = (μ.map (fun ω ↦ (Zc ω, As ω))) ⊗ₘ (Kernel.prodMkRight A' Q)`。
  `Zc` と `As` の**順序を取り違えると別の命題**になる（`prodMkRight` は第 1 成分だけ見る）。
- **`IsMarkovChain μ Xs Zc Yo` の第 2 引数が条件付け**（`CondMutualInfo.lean:90`–`:95`）。
  `bc_degraded_converse` の `h_deg_block` は `(Y₁s i) (W₂, Y₁^{<i}) (Y₂^{<i})` の順で、**中央が条件**。
- **`Measure.compProd_map` は第 2 成分だけ**（`Prod.map id f`）。第 1 成分は
  in-project の `compProd_comap_map_prodMap` が要る。**両方を合成して初めて `Prod.map f g` になる**（= P0）。
- **`Measure.pi_singleton` / `pi_pi` は `[∀ i, SigmaFinite (μ i)]`**。probability measure なら自動だが、
  `Kernel` の値に対して instance を出す局面では `IsMarkovKernel` から `IsProbabilityMeasure` を
  経由させること（`qBlock` の instance がその形）。
- **`Kernel.ofFunOfCountable` は `[Countable α] [MeasurableSingletonClass α]`**。
  `Fin k → β₁` に対しては β₁ の `Fintype` + `MeasurableSingletonClass` から自動。
  **β₁ を無限にした瞬間に `qBlock` が作れなくなる**（Mathlib に `Kernel.pi` が無いため、§Q7）。
- **`condDistrib_ae_eq_of_measure_eq_compProd` は `[IsFiniteKernel κ]`**。
  `isMarkovChain_of_append` の内部要求なので、移設先ファイルの import 閉包に
  `Mathlib/Probability/Kernel/CondDistrib.lean` が届いている必要がある。
- **`Fin i.val` の埋め込みは `⟨j.val, j.isLt.trans i.isLt⟩`**。`bc_degraded_converse` の逐語と 1 文字でも違うと
  `exact` が落ちる。P4 / P5 の署名は `Converse.lean:588`–`:592` からコピーすること。

---

## Q6 probe（すべて `lake env lean -D linter.mathlibStandardSet=true -D linter.unusedFintypeInType=false` で **exit 0 / error 0**）

置き場: `/private/tmp/claude-502/-Users-haruka-dev-lean-projects/39804b59-31a6-47a9-a7fa-f8b77dbd80cc/scratchpad/`
（session scratchpad。`InformationTheory/` は 1 行も触っていない）

| probe | 内容 | 結果 |
|---|---|---|
| `Probe1.lean` | `#check @IsBCDegraded` / 主目標の署名 elaborate | ✅ sorry 警告のみ。**`IsBCDegraded` の型クラス束が `MeasurableSpace` 3 本だけ**と判明 |
| `Probe2.lean` | **gateway atom** `pi_unzip_eq_compProd` + `degraded_singleton` + `qBlock` | ✅ **証明完了、warning 0**（78 行）|
| `Probe3.lean` | P0–P6 の全署名 + Fano 項 `rfl` の `example` | ✅ 全署名 elaborate、`rfl` **通過**（= Fano 橋 0 本）|
| `Probe4.lean` | P0 `compProd_map_prodMap` | ✅ **証明完了、warning 0**（証明本体 4 行）|
| `Probe6.lean` | 任意の系 `bc_degraded_capacity_eq_uv` | ✅ **証明完了、warning 0**（`classical` + `exact` の 2 行）|

**style ゲートで実際に出た警告（実装時に潰す 3 種）**: `unusedSectionVars`（→ `omit … in`）/
`linter.style.longLine`（100 字）/ `linter.style.show`（`show` → `change`）。
probe では全部潰して warning 0 まで持っていった（親 plan 判断ログ 20 / F-20 の「probe 段階から linter 条件」）。

---

## Q7 壁 / 撤退ライン

### Mathlib の壁 — **0 件**（BC 家系 10 leg 連続 → 本 leg で 11 leg 目）

「無い」ものはあるが、いずれも**有限アルファベットの回避路が実測で通っている**ので壁ではない。
**loogle の応答は 3 種を区別して記録する**（ブリーフの★指示）:

| 照会 | loogle 応答（逐語） | 判定 |
|---|---|---|
| `ProbabilityTheory.Kernel.pi` | `unknown identifier 'ProbabilityTheory.Kernel.pi'` / `Maybe you meant: "ProbabilityTheory.Kernel.pi"` | ⚠ **否定的回答ではない**（クエリが走っていない）|
| `ProbabilityTheory.Kernel.pi _ _` | `Unknown constant 'ProbabilityTheory.Kernel.pi'` | ✅ 定数が**実在しない**。`rg 'Kernel\.pi\b'`（Mathlib 全体）も **0 hit** で裏取り |
| `MeasureTheory.Measure.pi, MeasureTheory.Measure.compProd` | `Found 0 declarations mentioning MeasureTheory.Measure.pi and MeasureTheory.Measure.compProd.` | ✅ 真の 0 hit ⟹ **自作 #3** |
| `MeasureTheory.Measure.pi, MeasureTheory.Measure.bind` | `Found 0 declarations mentioning MeasureTheory.Measure.bind and MeasureTheory.Measure.pi.` | ✅ 真の 0 hit |
| `MeasureTheory.Measure.map (MeasureTheory.Measure.compProd _ _) _` | `Found 0 declarations mentioning … Of these, 0 match your pattern(s).` | ✅ 0 hit（ただし §Q4-1 の `compProd_map` は別綴りで拾えた ⟹ **パターン検索の 0 hit は名前検索で裏を取ること**）|
| `MeasureTheory.Measure.compProd, Prod.map` | `Found one declaration …` → `MeasureTheory.Measure.compProd_map` | ✅ **これが P0 の鍵**。上の 0 hit を覆した |
| `MeasureTheory.Measure.pi, MeasureTheory.Measure.map` | `Found 19 declarations …`（`pi_map_pi` / `pi_map_eval` を含む）| ✅ P3 の材料 |

**`Kernel.pi` 不在の射程（過小評価を防ぐための明記）**: β₁ が**可算でない**場合、
`u ↦ Measure.pi (fun j ↦ Q (u j))` の可測性が出せず `qBlock` が構成できない。
本 leg は `bc_degraded_converse` の型クラス束（β₁ は `Fintype`）に居るので**発火しない**が、
将来 BC を連続アルファベットに広げるときは**ここが最初に壊れる**（自作見積り: 有限次元 `Kernel.pi` の
自作は Mathlib PR 級で 150–300 行）。共有 sorry 補題は**不要**（本 leg に `sorry` は入らない見込み）。

### プロジェクト側の壁 — **0 件**（ただし `private` の壁が 1 つ）

`isMarkovChain_of_append` / `kernel_compProd_prodMkRight_eq_prod` の `private` は
**数学の壁ではなく配線の壁**（CLAUDE.md「blocker が『命題が無い』か『既存資産への配線』か」の後者）。
移設で解消。

### 撤退ラインとの距離 — **既存 6 本すべて不発動**

| slug | 本 leg との関係 |
|---|---|
| L-BCO1 / L-BCO4 / L-BCO5 / L-BCO6 | 既に不発動で retire 済。本 leg は判定対象を持たない |
| L-BCO2（active）| Phase 2 union の universe 問題。本 leg は union を触らない ⟹ **無関係** |
| L-BCO3 / L-BCO9（retire 済）| 内界・逆包含の話。本 leg は converse 側 ⟹ **無関係** |
| L-BCO7（active）| semi-deterministic の全支持仮説。本 leg は全支持を要求しない（`hdeg` のみ）⟹ **無関係**。⚠ **ただし §Q1-3 の任意の系 `bc_degraded_capacity_eq_uv` は `hW`（全支持）を要求する**。degraded かつ全支持でないチャネルでは系が使えない — これは L-BCO7 と**同じ機構**（内界の regularity 前提）だが、本 leg の主目標（古典形 converse）は `hW` を 1 本も要求しない |
| L-BCO8 | 無効化済 ⟹ 無関係 |

**新規撤退ラインの提案（L-BCO10）**:

> **発動条件**: `bcConverse_block_append`（自作 #6）が閉じない（pi 積 → compProd の再結合が
> `Measure.compProd_assoc` / `Kernel.compProd` の形合わせで詰む）。
> **退避先**: `bcConverse_degBlock`（自作 #8）の**署名を逐語で保ったまま** body を
> `sorry` + `@residual(plan:bc-degraded-block-append)` にし、配線 `bc_converse_from_code`（#9）は
> **そのまま完成させる**。命題は真（§Q2 で退化境界 2 つ + 反例探索を実施済）なので、
> L-BCO8 が禁じた「偽の署名に `sorry`」には当たらない。
> **禁止**: degradedness を `*Hypothesis` 述語に束ねて `bc_converse_from_code` の仮説に足す形は取らない
> （CLAUDE.md tier 5 / 親 plan §撤退ライン 禁止事項）。
> **さらに縮退させる場合**: 主目標を捨て、§Q1-3 の 2 行の系 `bc_degraded_capacity_eq_uv` だけを
> 入れて「degraded は more capable の系として閉じている」を機械可読にする（実測 6 行、probe 済）。
> 古典形 converse の着地は後続 leg へ defer。

---

## Q8 行数見積り（**数学と散文・section を別枠**、親 plan 判断ログ 23 / F-26）

### 較正（自分で測った実測値のみ）

- **一文字版の degradedness クラスタ**（本 leg のブロック版の直接の較正錘）:
  `Achievability/Assembly.lean:801`–`:959` = **159 行**。内訳は汎用の append 機械 58 行
  （`:801`–`:858`、= 本 leg が移設する分）+ 一文字の append 恒等式 82 行（`:859`–`:940`）+
  鎖の組み立て 19 行（`:941`–`:959`）。本 leg のブロック版（#6–#8）はこの 101 行（82+19）の
  ブロック一般化なので、1.2–1.7 倍を見込む。
- **配線の雛形** `bc_uv_converse_from_code`（`Bridge.lean:559`–`:604`）= **46 行**
  （docstring 8 + 署名 21 + 証明 17）。
- **probe 実測**（本在庫で書いて通したもの）: 78 + 14 + 6 = **98 行**。

### 見積り表（probe 行数は**下限**であって予測ではない）

| # | 項目 | 数学（probe 実測 = 下限）| 数学（追加見積り）| 散文・section |
|---|---|---|---|---|
| 1–3 | `degraded_singleton` / `qBlock` / **`pi_unzip_eq_compProd`** | **78** | 0 | 6（module doc 断片 + `###`）|
| 4 | `compProd_map_prodMap`（P0）| **14** | 0 | 2 |
| 5 | `pi_map_comp_injective`（P1）| 0 | 25–35 | 2 |
| 6 | `bcConverse_block_append`（P3）| 0 | 60–90 | 4 |
| 7 | `bcConverse_prefix_append`（P4）| 0 | 35–50 | 4 |
| 8 | **`bcConverse_degBlock`（P5、主目標）** | 0 | 25–35 | 6（docstring）|
| 9 | `bc_converse_from_code`（P6、配線）| 0 | 50–65 | 10（docstring）|
| — | module doc / import / namespace / `variable` / `omit` | — | — | 40–55 |
| **計** | | **92** | **195–275** | **74–89** |

- **数学 合計 帯: 287–367**（下限 92 は確定）
- **散文・section 合計 帯: 74–89**
- **総計 帯: 361–456**（点推定 **~410**）
- 別枠: **移設 58 行（純増 0、2 ファイル touch）**

⚠ **親 plan §推奨実行順 #3 の `~120 行` は下振れ**（probe を持たない見積り）。
判断ログ 23 の「probe を持たない見積りは桁で外れうる」が本 leg でも再現した。
plan 側の数値の更新は plan の担当（本在庫は編集しない）。

---

## Q9 実装 leg への申し送り

### 推奨実装順（gateway atom 先頭）

1. **G1 = `pi_unzip_eq_compProd`（自作 #1–#3）** — probe をそのまま移植（78 行、warning 0）。
   **ここが通れば数学の山は越えている**。
2. **移設 M** — `isMarkovChain_of_append` + `kernel_compProd_prodMkRight_eq_prod` を
   `Achievability/Assembly.lean` から取り出し public 化。**移動先の第一候補は
   `Shannon/CondEntropyMemoryless.lean`**（`isMarkovChain_comp_conditioner_right:371` の隣。
   `isMarkovChain_of_append` の docstring 自身が "This is the stochastic analogue of
   `isMarkovChain_comp_conditioner_right`" と名指している）。
   ⚠ **判断ログ 11-(i)**: 移動先は consumer 表ではなく**依存の閉包**で決まる。
   要確認は 1 点 — 移動先の import 閉包に `Mathlib/Probability/Kernel/CondDistrib.lean`
   （`condDistrib_ae_eq_of_measure_eq_compProd`）と `Measure.compProd_assoc'` が届くか。
   届かなければ第 2 候補は `Shannon/CondMutualInfo.lean`（`IsMarkovChain` の定義元）。
   移設後 `lake build InformationTheory.Shannon.BroadcastChannel.Achievability.Assembly` で olean 更新。
3. `compProd_map_prodMap`（#4）— 置き場は `CodeToAmbient.lean`（相方 `compProd_comap_map_prodMap:346` の隣）。
   BC 固有語ゼロの汎用 API なので **親 plan §後続作業 F-15 の軸に合致**。
4. `pi_map_comp_injective`（#5）— 雛形は Mathlib の `isProjectiveMeasureFamily_pi`
   （`Mathlib/Probability/ProductMeasure.lean:65`、8 行。`Function.extend` +
   `Finset.prod_subset_one_on_sdiff` の型）。**Finset 添字版をそのまま使うと `Fin k ≃ {j // j < i}` の
   piCongrLeft が要って高くつく**ので、単射 `e : Fin k → Fin m` 版を直接書くのが安い。
5. `bcConverse_block_append`（#6）→ `bcConverse_prefix_append`（#7）→ `bcConverse_degBlock`（#8）。
6. `bc_converse_from_code`（#9）。雛形は `bc_uv_converse_from_code`（`Bridge.lean:567`）を逐語で。
7. （任意）`bc_degraded_capacity_eq_uv`（6 行、probe 済）。**入れるなら置き場は `Classes.lean` ではなく
   `Superposition/MoreCapable.lean`**（`bc_moreCapable_capacity_eq_uv` の隣）。
   ⚠ 親 plan §後続作業 G-1 が「`bc_lessNoisy_*` の畳み直しは意図的に未実施」としているので、
   **degraded の系を足すかは orchestrator の判断**（数学は 0 行、純粋に API 面の判断）。

### 配置

**第 1 候補（推奨）**: 新規 `InformationTheory/Shannon/BroadcastChannel/DegradedConnection.lean`。

```lean
import InformationTheory.Shannon.BroadcastChannel.Converse
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Bridge
import InformationTheory.Shannon.BroadcastChannel.Achievability.Setup
```

- **import 循環なし**を実測（probe 1 / 3 がこの 3 本で elaborate、`lake env lean` 5.3 s）。
  `Achievability/Setup.lean` は `OuterBoundUV` を一切 import しないので逆向きも安全。
- `InformationTheory.lean` への import 行追加を忘れないこと（pre-commit が WARN する）。
- ❌ **`Bridge.lean` に同居させるのは不可**: `IsBCDegraded` のために `Achievability/Setup.lean`
  （MAC の JointTypicality / IIDAmbient / SlepianWolf を引く重い閉包）を UV 連鎖全体に流し込むことになる。
- 💡 **flag（本 leg の必須ではない）**: `IsBCDegraded` は `[MeasurableSpace]` 3 本しか要らない軽い def なのに
  最も重いファイルの 1 つ（`Achievability/Setup.lean`）に居る。`BroadcastChannel/Basic.lean` へ
  移設すれば本 leg の import は 2 本で済む。direct consumer **4 decl / 2 file**（実測、名前不変なので
  import 行の調整だけ）。親 plan §後続作業 F への起票候補。

### 命名（`docs/rules/naming.md`）

- `bcConverse_degBlock` は `bc_degraded_converse` の仮説名 `h_deg_block` と対応が読めるので可。
  ただし family 既定は `bcConverse_<性質>`（`bcConverse_memoryless₁` / `bcConverse_isMarkovChain₁`）なので、
  **`bcConverse_isMarkovChain_degraded` も候補**。判断ログ 25「クラス限定の定理は名前にクラスを入れる」に従うなら
  degraded を名前に入れる方が筋。
- `qBlock` は BC 固有語ゼロの汎用名。**BC namespace に置くなら `bcDegradingBlockKernel` 等に寄せるか、
  最初から `Shannon/` 側に出す**（F-15 の軸。移設と改名は同時が筋）。
- `pi_unzip_eq_compProd` / `compProd_map_prodMap` / `pi_map_comp_injective` はいずれも汎用。
  **BC namespace に置くと「次に同じ補題を探す人は `BroadcastChannel/` を見ない`」**（F-15 の本文）。

### 検証バー（親 plan F-20 / 判断ログ 28）

- 内ループ: `lake env lean -D linter.mathlibStandardSet=true -D linter.unusedFintypeInType=false <file>`
- leg 終了時: `lake build InformationTheory.Shannon.BroadcastChannel.DegradedConnection`
- 既存ファイルを触る場合（移設 M）は **HEAD 版を `git show` で取り出して同一設定で lint し、
  warning 集合が完全一致すること**を見る（件数の暗記ではない）。
- ゲート: 新規 `sorry` を入れないなら honesty は launch 条件外。**style は必ず launch**（新規 decl 多数）。

### 親 plan 側で更新が要る点（編集は plan の担当）

1. §推奨実行順 #3 の見積り `~120 行` → **帯 361–456**（本在庫 §Q8）。
2. §存在しないもの (d) は「補題 1 本」ではなく **自作 6 本 + 移設 2 本**。
3. 判断ログ 11-(n) の「対応版は 0 hit、新規 ~120 行」の**理由**を更新:
   0 hit なのは事実だが、効かない理由は「仮説の表現が違う」だけでなく
   **`isMarkovChain_of_compProd_pi` が `W` を不透明カーネルとして扱い degradedness を見ないから**
   （§Q3-2）。判断ログ 11-(o)「在庫の *順序* は引き継ぎ *理由* は引き直す」の再現。
4. §在庫の `Bridge.lean` 行番号が docstring 行と decl 行で混在している（`bcConverseAmbient:141` は
   decl が `:146`、`bcConverseFanoSlack₁:532` は `:537`、`bc_uv_converse_from_code:562` は `:567`、
   `bc_uv_rate_extract:602` は `:607`、構造前提 4 本 `:301`–`:428` は `:306`/`:353`/`:399`/`:433`）。
   `uvInfo₁:782` 等は decl 行で一致しているので**規約の不統一**であってファイルの drift ではない。優先度低。
5. §Phase 5「残るクラス」に **「領域レベルの degraded 等号は more capable の系として既に取れている
   （実測 2 行）。本 leg の価値は古典形 converse の操作的着地」** を 1 行足すと、
   後続セッションが「degraded の等号がまだ無い」と誤読しない。

---

## 付録: 着手のための skeleton

```lean
import InformationTheory.Shannon.BroadcastChannel.Converse
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Bridge
import InformationTheory.Shannon.BroadcastChannel.Achievability.Setup

/-!
# Broadcast channel — the degraded converse at the ambient of a code

The block-degradedness Markov chain read off `bcConverseAmbient`, and the degraded converse
`bc_degraded_converse` instantiated there.

## Main statements

* `bcConverse_degBlock` — under physical degradedness the letter-`i` output of receiver 1 is
  conditionally independent of the receiver-2 prefix given message 2 and the receiver-1 prefix.
* `bc_converse_from_code` — the degraded outer bound at a bare broadcast code.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {α : Type*}
  [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [StandardBorelSpace α] [Nonempty α]
variable {β₁ : Type*}
  [Fintype β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [StandardBorelSpace β₁] [Nonempty β₁]
variable {β₂ : Type*}
  [Fintype β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
  [StandardBorelSpace β₂] [Nonempty β₂]
variable {M₁ M₂ n : ℕ}

lemma bcConverse_degBlock
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (hdeg : IsBCDegraded W) (i : Fin n) :
    IsMarkovChain (bcConverseAmbient c W) (bcConverseY₁s i)
      (fun ω ↦ (bcConverseMsg₂ ω,
        fun (j : Fin i.val) ↦ bcConverseY₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      (fun ω (j : Fin i.val) ↦ bcConverseY₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω) := by
  sorry

end InformationTheory.Shannon.BroadcastChannel
```

（P0–P4 の署名は probe `Probe3.lean` に逐語で置いてある。実装 leg はそこからコピーできる。）

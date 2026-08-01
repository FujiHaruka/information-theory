# BC more capable の等号 — M0 在庫

> 親 plan (SoT): [`bc-general-region-plan.md`](bc-general-region-plan.md) §Phase 5「残る 2 クラス」/
> §推奨実行順 **#2** / §撤退ライン **L-BCO3** / §設計上の未決事項 2 / §判断ログ 11-(l) · 23 · 24。
> 前段の在庫: [`bc-s8-assembly-inventory.md`](bc-s8-assembly-inventory.md) /
> [`bc-s7-fullsupport-inventory.md`](bc-s7-fullsupport-inventory.md) /
> [`bc-s6-timesharing-inventory.md`](bc-s6-timesharing-inventory.md) /
> [`bc-s5-quantization-inventory.md`](bc-s5-quantization-inventory.md) /
> [`bc-phase5-class-inventory.md`](bc-phase5-class-inventory.md)。
> proof-log: [`proof-log-bc-lessnoisy-equality.md`](../proof-logs/proof-log-bc-lessnoisy-equality.md)。
> probe は scratchpad の `ProbeMC{0Setup,1TimeShare,2CondMoreCapable,3SumBound,4Perturb,5Region,6Corner}.lean`
> (計 935 行、重複を除いた実装相当は約 525 行)。**7 本すべて
> `lake env lean -D linter.mathlibStandardSet=true -D linter.unusedFintypeInType=false` で
> エラー 0**。`InformationTheory/` は 1 バイトも触っていない。
> ⚠ **較正基準の注意**: `bc-s6-timesharing-inventory.md:338` / `bc-s7-fullsupport-inventory.md:306`
> の「S5 は 280→289 で的中」は誤り (親 plan F-26)。本在庫は自分で測った実測値だけを使う (§Q8)。

---

## 結論サマリ

- **目標は真。しかも新しい数学の中核 5 本すべてが probe で証明済** — 条件付き more capable /
  `uvInfoSum₁ ≤ I(X;Y₁)` / `uvInfo₂ ≤ I(X;Y₁)` / 3 スロット版の時分割 / 摂動下の `I(X;Y₁)` の凹性。
  いずれも `sorry` 0 でコンパイル通過。
- **plan の「3 field の新 `structure` が要る」は誤り** — less noisy の内界
  `bcSuperpositionRegionNoSumRate` (`Superposition/Region.lean`) は `InBCCapacityRegion` を
  **使っていない**。素の `{p | p.1 ≤ … ∧ p.2 ≤ …}` である。more capable も 3 連言の集合内包で足り、
  **新 `structure` は 1 本も要らない** (§Q1、probe MC5 で機械確認)。
- **第 3 制約は `p.1 + p.2 ≤ bcInfoJoint` ではなく `max p.1 0 + p.2 ≤ bcInfoJoint` と書く**
  (CLAUDE.md「Mathlib-shape-driven Definitions」)。到達点 `bc_achievability_of_rate_lt`
  (`Achievability/Assembly.lean:1103`) の仮説が逐語で `hJlt : max R₁ 0 + R₂ < bcInfoJoint` だから。
  この形にすると **内界の達成可能性が比較クラス仮説をまったく要求しない**
  (`bcSuperpositionRegionSumRate_subset_capacity` は `hW` のみ、probe MC5 で機械確認)。素直な
  `p.1 + p.2` 形にすると負レート枝で `bcInfo₂ ≤ bcInfoJoint` が必要になり、クラス仮説が達成側に漏れる。
- **plan の「`uvInfoSum₁` の `V = X` 特殊化で到達可能」は方向が逆** — `V = X` 特殊化は
  「内界 ⊆ 外界」を示す道具で、headline (`bcCapacityRegion = bcOuterRegionUV`) の
  クリティカルパス (**外界 ⊆ 内界**) には乗らない。外界側から要るのは
  `uvInfoSum₁ ν ≤ I(X;Y₁)`、すなわち **more capable の条件付き版** (§Q2-1)。これが本 leg の
  唯一の新しい数学の核。
- **S3 / S4 / S5 はそのまま再利用、S6 / S7 / S8 は変種が要る** (§Q3)。S6 の変種は
  **クラス仮説を持たない** (less noisy 版より真に一般)。
- **Mathlib の壁 0 件 / プロジェクト側の壁も 0 件** (BC 家系 9 leg 連続)。**L-BCO3 は不発動**。
- **行数見積り ~880 行 (数学 735 = probe 実測 525 + 未 probe 210、散文・section 145)**、帯 **820–980**。

### 最も危ない発見 (1 行)

**`IsBCMoreCapable` の条件付き版を出すのに `[Countable V] [MeasurableSingletonClass V]` が要る** —
`condMutualInfo_compProd_fst_eq_lintegral` (`Shannon/CondMutualInfoMixture.lean:102`) が tag 型に
これを課すため。外界の第 2 補助は `ℕ` なので実害は 0 だが、**型クラス前提として headline まで
上がってこないことを確認済** (probe MC3/MC6: `ν : Measure (U × V × α × β₁ × β₂)` の `V` に付き、
`bcOuterRegionUV` の `V := ℕ` で `inferInstance` が埋める)。もし外界の補助型を一般化する将来の leg が
あれば、この 2 本が最初に効く。

---

## Q1 到達点の署名案

### Q1-1 内界 (新規 def、**`structure` は不要**)

```lean
noncomputable def bcSuperpositionRegionSumRate (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k : ℕ) (pU : Measure (Marton.bcAuxAlphabet.{u} k))
    (_ : IsProbabilityMeasure pU) (_ : ∀ x : Marton.bcAuxAlphabet.{u} k, 0 < pU.real {x})
    (K : Kernel (Marton.bcAuxAlphabet.{u} k) α) (_ : IsMarkovKernel K)
    (_ : ∀ (x : Marton.bcAuxAlphabet.{u} k) (a : α), 0 < (K x).real {a}),
    {p : ℝ × ℝ | p.1 ≤ bcInfo₁ pU K W ∧ p.2 ≤ bcInfo₂ pU K W
      ∧ max p.1 0 + p.2 ≤ bcInfoJoint pU K W})
```

型クラス前提は `bcSuperpositionRegionNoSumRate` と**逐語同一**
(`Superposition/Region.lean`):

```
{α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
```

**Mathlib-shape 検討 (CLAUDE.md の 3 手順を実施)**:

| # | 支配する補題 | 逐語の結論 / 仮説形 | 定義への効き方 |
|---|---|---|---|
| 1 | `bc_achievability_of_rate_lt` (`Achievability/Assembly.lean:1103`) | 仮説 `(hR₁lt : R₁ < bcInfo₁ pU K W) (hR₂lt : R₂ < bcInfo₂ pU K W) (hJlt : max R₁ 0 + R₂ < bcInfoJoint pU K W)` | **第 3 field を `max p.1 0 + p.2` にする**。`p.1 + p.2` だと負レート枝で追加補題が要る |
| 2 | `bc_mem_closure_of_strictly_below` (`Operational.lean:86`) | 「任意の `ε > 0` で `(p.1-ε, p.2-ε)` が達成可能なら `p ∈ closure`」 | `max (p.1-ε) 0 ≤ max p.1 0` が単調性 1 行で出る形にしておく (`max_le_max`) |
| 3 | `isClosed_closure` | `IsClosed (closure s)` | 外側 `closure` を保つ (less noisy と同じ) |

⟹ **3 本とも書いた形のまま当たる** (probe MC5 で 3 本すべて機械確認)。

### Q1-2 達成側 (**比較クラス仮説なし**、probe で証明済)

```lean
theorem bcSuperpositionRegionSumRate_isClosed (W : BCChannel α β₁ β₂) :
    IsClosed (bcSuperpositionRegionSumRate.{u} W) := isClosed_closure

@[entry_point]
theorem bcSuperpositionRegionSumRate_subset_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) :
    bcSuperpositionRegionSumRate.{u} W ⊆ bcCapacityRegion W
```

⚠ less noisy 版 `bcSuperpositionRegionNoSumRate_subset_capacity` (`Superposition/Region.lean`)
は `hln : IsBCLessNoisy W` を要求するが、**3 制約版は要求しない**。第 3 制約を領域が自分で
持つようになったので、`bc_lessNoisy_infoJoint_ge` を呼ぶ必要が消えた (probe MC5 実測)。

### Q1-3 逆包含と headline (提案)

```lean
@[entry_point]
theorem bc_moreCapable_uv_subset_superposition (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hmc : IsBCMoreCapable W) :
    bcOuterRegionUV W ⊆ bcSuperpositionRegionSumRate.{u} W

@[entry_point]
theorem bc_moreCapable_capacity_eq_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hmc : IsBCMoreCapable W) :
    bcCapacityRegion W = bcOuterRegionUV W

theorem bc_moreCapable_superposition_eq_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hmc : IsBCMoreCapable W) :
    bcSuperpositionRegionSumRate.{u} W = bcCapacityRegion W
```

`hW` の要る場所は less noisy とまったく同じ = **逆包含ではなく内界を符号に落とす段だけ**
(`bc_achievability_of_rate_lt` の regularity)。`@[entry_point]` は 2 本、3 本目は bare
(S8 の判断をそのまま踏襲)。

### Q1-4 ⚠ 本 leg は landed 済の less noisy headline を**包含する**

`IsBCLessNoisy.isBCMoreCapable` (`Classes.lean:218`) があるので

```lean
bc_lessNoisy_capacity_eq_uv W hW hln
  = bc_moreCapable_capacity_eq_uv W hW hln.isBCMoreCapable   -- 2 行
```

が成り立つ。さらに less noisy では 3 制約集合 = 2 制約集合 (probe MC5 の `example`、
`bc_lessNoisy_infoJoint_ge` + `bcInfo₁_nonneg` で 5 行) なので
`bc_lessNoisy_uv_subset_superposition` も系になる。
**本 leg では配線し直さない**ことを推す (S5–S8 の機械は 3 スロット版が再利用するので消せず、
書き換えは純粋な churn)。ただし**新ファイルの module doc に包含関係を書く**のと、
親 plan §後続作業に 1 件立てるのが筋。

---

## Q2 目標の真偽判定 (brief の 2)

### Q2-1 ★核心 — `uvInfoSum₁ ν ≤ I(X; Y₁)` は more capable で成り立つ (probe MC3 で証明済)

外界の 4 制約 (`InBCOuterRegionUV`、`OuterBoundUV.lean:735`) のうち、less noisy の逆包含が
**捨てていた** `sumBound₁` が more capable では主役になる。

```
uvInfoSum₁ ν = I(V;Y₁) + I(X;Y₂ ∣ V)        (def, Bridge.lean:792)
I(X;Y₁)      = I(V;Y₁) + I(X;Y₁ ∣ V)        (連鎖律 + V → X → Y₁)
⟹ uvInfoSum₁ ν ≤ I(X;Y₁)  ⟺  I(X;Y₂ ∣ V) ≤ I(X;Y₁ ∣ V)   ← **more capable の条件付き版**
```

条件付き版は無条件版から **V での分解 (disintegration) + 各成分への適用 + 積分の単調性**で出る:

```lean
theorem IsBCMoreCapable.condMutualInfo_le {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    (hmc : IsBCMoreCapable W) (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K] :
    condMutualInfo (bcJointDistribution pU K W) (fun q ↦ q.2.1) (fun q ↦ q.2.2.2) (fun q ↦ q.1)
      ≤ condMutualInfo (bcJointDistribution pU K W) (fun q ↦ q.2.1) (fun q ↦ q.2.2.1)
          (fun q ↦ q.1)
```

証明の骨 (probe MC2、90 行):
`bcJointDistribution pU K W = pU ⊗ₘ (K ⊗ₖ W.comap Prod.snd)` (`Measure.compProd_assoc'` **1 行**)
→ `condMutualInfo_compProd_fst_eq_lintegral` で `∫⁻ u, mutualInfo ((K u) ⊗ₘ W) …`
→ `Kernel.compProd_apply_eq_compProd_sectR` でスライス
→ `mutualInfoOfChannel` へ翻訳 → `lintegral_mono fun u ↦ hmc (K u)`。

**仮説が固定している不変量 (CLAUDE.md「Name the pinned invariant」)**: `IsBCMoreCapable` は
**「`α` 上の *すべての* 入力法 `p` について `I(X;Y₂) ≤ I(X;Y₁)`」**を固定する。結論が要求するのは
「`V = v` 条件付き入力法 `p(·∣v)` について同じ不等式」で、**条件付き法もまた `α` 上の入力法**
だから、仮説は結論が要求するちょうどの粒度である (粗くも細かくもない)。⟹ under-hyp の余地なし。
これは less noisy (`∀ (U : Type u) …` と補助変数を量化する形) との**構造的な差**で、
less noisy では条件付き化が定義に内蔵されているぶん、more capable では 90 行の分解が要る。

### Q2-2 負レート枝には `uvInfo₂ ν ≤ I(X;Y₁)` が要る (probe MC6 で証明済)

`max R₁ 0 + R₂ ≤ I(X;Y₁)` を外界の点から作るとき、`R₁ < 0` の枝では
`R₂ ≤ uvInfo₂ ν = I(U;Y₂)` しか使えない。よって

```
I(U;Y₂) ≤ I(X;Y₂)     (DPI、U → X → Y₂)
I(X;Y₂) ≤ I(X;Y₁)     (more capable を ν の X 周辺法に当てる)
```

の 2 段が要る。1 段目のために **`IsUVChannelLaw.isMarkovChain_U_X_Y₂` を新設**する
(既存の `_U_X_Y₁` (`OuterBoundUV/Region.lean:311`) の逐語ミラー、出力の取り出しが
`Prod.fst` → `Prod.snd` になるだけ。probe 実測 18 行)。2 段目は
`IsUVChannelLaw.map_input_output` (`:240`) が `ν.map (X, Y) = (ν.map X) ⊗ₘ W` を直接くれるので
15 行。

⚠ **plan にも S8 在庫にもこの obligation は書かれていない**。「第 3 制約を足すだけ」と読むと
落ちる (判断ログ 24 の再発 — 4 leg 連続)。

### Q2-3 退化境界 2 つ (構造の違うもの) + 最も一般な対象の再検査

| 軸 | 設定 | 予測 | 実際 |
|---|---|---|---|
| **クラスの退化** | `IsBCLessNoisy W` (more capable の真部分クラス) | 第 3 制約が前 2 本から出て 3 制約領域 = 2 制約領域に潰れる | ✅ probe MC5 の `example` で機械確認 (`bc_lessNoisy_infoJoint_ge` + `bcInfo₁_nonneg`、`↔` を両向き)。⟹ **新定義は landed 済の定義の真の一般化で、退化させると一致する** |
| **レートの退化** | `p = (-1, -1)` | 3 制約すべてが自明に成立 (符号場合分けは不発火) | ✅ probe MC5 で機械確認。`max (-1) 0 = 0` に潰れ `0 + (-1) ≤ bcInfoJoint` が `bcInfoJoint ≥ 0` から出る。**第一象限の暗黙仮定は 3 制約版でも入らない** |

**最も一般な対象の再検査**: `bc_moreCapable_uv_subset_superposition` の明示仮説は
`[IsMarkovKernel W]` と `hmc : IsBCMoreCapable W` のみ。`IsBCMoreCapable`
(`Classes.lean:75`) は `∀ (p : Measure α) [IsProbabilityMeasure p], mutualInfoOfChannel p
(Kernel.snd W) ≤ mutualInfoOfChannel p (Kernel.fst W)` で、**どちらの領域も、どの補助変数も
参照しないチャネルレベルの述語** ⟹ load-bearing ではない (CLAUDE.md tier 5 に該当しない)。
probe は一般形 (任意の `U`/`V`、任意の `IsUVChannelLaw` な `ν`) で通っている。

**非空性 (vacuous でないこと)**: `IsBCDegraded → IsBCLessNoisy → IsBCMoreCapable` の鎖
(`Classes.lean:133` / `:218`) があり、[`bc-facts.md`](bc-facts.md) が全支持の劣化 BSC 対
(`q = 0.1`, `p = 0.25`) を数値実験の題材に使っている ⟹ `hW` と `hmc` を同時に満たす `W` は実在する。
**semi-deterministic と違って `hW` と構造的に非両立ではない** (判断ログ 13 の罠は本クラスでは
発火しない)。「more capable だが less noisy でない」チャネルの存在は文献 (El Gamal 1979) の
主張で、in-project の証拠は無い (`human-judgment`)。**headline の真偽には効かない**。

### Q2-4 文献帰属 (brief の指示による照合)

| クラス | 帰属 | 照合先 |
|---|---|---|
| less noisy | **Körner–Marton 1975/1977** | [`bc-phase5-class-inventory.md:262`](bc-phase5-class-inventory.md) / 親 plan 判断ログ 11-(l) |
| **more capable** | **El Gamal 1979** | 同 `:263` / `:282`。教科書位置は El Gamal–Kim *Network Information Theory* §5.6 |
| semi-deterministic | Marton 1979 | 同 `:264` |

親 plan `:210` / `:510` の現行記述は**正しい** (誤帰属は判断ログ 11-(l) で既に訂正済)。
本在庫で新たに訂正すべき帰属は無い。

⚠ **文献の領域の形は in-project の内界の形と違う**: EGK §5.6 の more capable 容量領域は
`R₂ ≤ I(U;Y₂)`, `R₁+R₂ ≤ I(X;Y₁∣U)+I(U;Y₂)`, `R₁+R₂ ≤ I(X;Y₁)` の **和形**で、
`R₁ ≤ I(X;Y₁∣U)` を単独では持たない。in-project の内界 (superposition) は
`R₁ ≤ I(X;Y₁∣U)` を持つ**分離形**で、固定の `p(u,x)` では真に小さい。両者は
`p(u,x)` についての和集合を取ると一致し、**その一致を与えるのが S6 の時分割**
(probe MC1 で機械確認、§Q3)。⟹ 「文献の形をそのまま def にしない」= CLAUDE.md
「Mathlib-shape-driven Definitions」の教科書ケース。

---

## Q3 S0–S8 の再利用可否 (brief の 3)

| step | 資産 | 判定 | 変更点 |
|---|---|---|---|
| **S0** 達成側の factor out | `bc_achievability_of_rate_lt` (`Achievability/Assembly.lean:1103`) | **逐語再利用** | **すでに第 3 仮説 `hJlt : max R₁ 0 + R₂ < bcInfoJoint` を持っている** (probe MC0 で機械確認)。more capable のために新しい達成側の数学は **0 行** |
| **S1** less noisy 接続 | `bc_lessNoisy_infoJoint_ge` (`Classes.lean:95`) | **使わない** | more capable では `bcInfo₁ + bcInfo₂ ≤ bcInfoJoint` が**偽になりうる**。代わりに第 3 制約を領域が持つ |
| **S2** 内界の集合化 | `bcSuperpositionRegionNoSumRate` (`Superposition/Region.lean`) | **変種** | 第 3 連言を足すだけ。`_isClosed` は `isClosed_closure` のまま (2 行)。`_subset_capacity` は**クラス仮説が落ちる** (§Q1-2) |
| **S3** スロット同定 3 本 | `bcInfo₂_eq_mutualInfo_toReal:78` / `bcInfoJoint_eq_mutualInfo_toReal:90` / `bcInfo₁_eq_condMutualInfo_toReal:110` (`Superposition/Region.lean`) | **逐語再利用** ✅ | `{U : Type*}` 総称。probe MC0 で `bcInfoJoint_eq_mutualInfo_toReal` を実際に適用して確認。型クラス前提は逐語 `[Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]` + `[IsProbabilityMeasure pU]` / `[IsMarkovKernel K]` / `[IsMarkovKernel W]` |
| **S4** 四つ組法 + Markov 鎖 | `IsUVChannelLaw.map_auxiliary_input_output:257` / `.isMarkovChain_UV_X_Y:293` / `_U_X_Y₁:311` / `_V_X_Y₁:331` (`OuterBoundUV/Region.lean`) | **逐語再利用 + 1 本追加** | 既存 3 本はそのまま。**`_U_X_Y₂` を新設**(§Q2-2、既存 `_U_X_Y₁` の逐語ミラー 18 行)。`section Transport` の前提 `[StandardBorelSpace _] [Nonempty _]` × 5 型 + `[IsProbabilityMeasure ν]` は変わらない |
| **S5** 有限量子化 | `uvQuantizeLaw:196` / `_isUVChannelLaw:212` / `uvInfo₁_uvQuantizeLaw:225` / `uvQuantizeSlack_ne_top:251` / 裾 3 本 `:352` `:358` `:374` (`OuterBoundUV/Quantization.lean`) | **逐語再利用 + 1 本追加** | 既存はすべてそのまま。第 3 スロットは **`uvInfoJoint (uvQuantizeLaw ν m) = uvInfoJoint ν` (等式)** で運ばれる。量子化は第 1 補助しか触らず `I(X;Y₁)` は補助を見ないため。probe MC1 の `uvInfoJoint_map_uvRelabel` を `e₁ := uvQuantize m`, `e₂ := id` で叩く **3 行**。裾 `uvQuantizeSlack` は第 3 スロットには**課されない** |
| **S6** 時分割 | `exists_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw` (`Superposition/TimeShare.lean:571`) | **変種 (クラス仮説が落ちる)** | 元の証明は `hab : a + b ≤ J` を `bc_lessNoisy_infoJoint_ge` から作る。変種は `hab` を捨て、代わりに仮説 `hs₁ : max R₁ 0 + R₂ ≤ (uvInfoJoint ν).toReal` を受け、`lam·(a+b) + (1-lam)·J ≥ min (a+b) J ≥ R₁+R₂` の**凸結合 1 本**で閉じる。⟹ **`hln` も `hmc` も要らない**。装置 (`uvTimeShareLaw:253` / `condMutualInfo_uvTimeShareLaw:366` / `mul_uvInfo₂_le_uvInfo₂_uvTimeShareLaw:315` / `exists_bcInfo_ge_of_tagged:546` の骨格 / `boolProdAuxEquiv:501`) は**逐語再利用**。probe MC1 で全証明通過 |
| **S7** 全支持摂動 | `exists_fullSupport_bcInfo_ge_of_isUVChannelLaw` (`Superposition/FullSupport.lean:460`) | **変種 (第 3 スロットの下界を 1 本追加)** | 2 スロットの損失評価 (`mul_condMutualInfo_le_condMutualInfo_uvPerturbLaw:380` / `mul_uvInfo₂_sub_binEntropy_le_uvInfo₂_uvPerturbLaw:405`) はそのまま。**`lam * uvInfoJoint ν ≤ uvInfoJoint (uvPerturbLaw W ν v₀ lam)` を新設** (= `I(X;Y₁)` の入力法についての凹性、probe MC4 で証明済 55 行)。`exists_perturb_weight:429` は **2 引数のまま `A := A + J` で流用でき、新設不要** |
| **S8** 逆包含 + 等号 | `Superposition/Assembly.lean` 7 本 | **変種 (逐語再利用は 0 本、骨格は逐語)** | 裾の `.toReal` 引き算 2 本 (`:54` `:64`) はそのまま使える。点レベル 2 本 (`:74` `:92`) と逆包含 (`:117`) と headline 2 本 (`:142` `:150`) は 3 スロット版を書き直す。**2 重極限の対角線 1 本 (`m := k`, `δ := 1/(k+1)`) はそのまま**、第 3 スロットは量子化で不変・摂動で `δ` 1 回なので帳簿は増えない |

**`hW` の要る場所は less noisy と同一** (brief の問い): 逆包含側には 1 本も要らず、
`bcSuperpositionRegionSumRate ⊆ bcCapacityRegion` (内界を符号に落とす段) にだけ要る。probe MC5 の
`bcSuperpositionRegionSumRate_subset_capacity` が `hW` だけを取ることで機械確認済。

---

## Q4 資産表

### 4-1 Mathlib (**すべて既存、`Superposition/` の現在の import 閉包内**)

| 用途 | 宣言 | 逐語署名 | file:line |
|---|---|---|---|
| ★ `bcJointDistribution` を tag 付き compProd に開く | `MeasureTheory.Measure.compProd_assoc'` | `lemma compProd_assoc' {γ : Type*} {mγ : MeasurableSpace γ} {η : Kernel (α × β) γ} : (μ ⊗ₘ κ ⊗ₘ η).map MeasurableEquiv.prodAssoc = μ ⊗ₘ (κ ⊗ₖ η)` (section 変数 `{α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α} {κ η : Kernel α β}`) | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:250` |
| ★ カーネルのスライス | `ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR` | `lemma compProd_apply_eq_compProd_sectR {γ : Type*} {mγ : MeasurableSpace γ} (κ : Kernel α β) (η : Kernel (α × β) γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] (a : α) : (κ ⊗ₖ η) a = (κ a) ⊗ₘ (Kernel.sectR η a)` | 同 `:95` |
| 出力の周辺化 | `MeasureTheory.Measure.compProd_map` | `lemma compProd_map [SFinite μ] [IsSFiniteKernel κ] {f : β → γ} (hf : Measurable f) : μ ⊗ₘ (κ.map f) = (μ ⊗ₘ κ).map (Prod.map id f)` | `Mathlib/Probability/Kernel/Composition/Lemmas.lean:120` |
| 周辺チャネル | `ProbabilityTheory.Kernel.fst_eq` / `Kernel.snd_eq` | `theorem fst_eq (κ : Kernel α (β × γ)) : fst κ = map κ Prod.fst` / `theorem snd_eq (κ : Kernel α (β × γ)) : snd κ = map κ Prod.snd` | `Mathlib/Probability/Kernel/Composition/MapComap.lean:412` / `:478` |
| 積分の単調性 | `MeasureTheory.lintegral_mono` | `theorem lintegral_mono {f g : α → ℝ≥0∞} (hfg : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ` | `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean` |
| 閉集合への極限回収 | `IsClosed.mem_of_tendsto` | `theorem IsClosed.mem_of_tendsto {f : α → X} {b : Filter α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : ∀ᶠ x in b, f x ∈ s) : x ∈ s` | `Mathlib/Topology/Neighborhoods.lean:348` |
| 2 成分の同時収束 | `Filter.Tendsto.prodMk_nhds` | `theorem Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : Y} {f : Filter γ} {mx : γ → X} {my : γ → Y} (hx : Tendsto mx f (𝓝 x)) (hy : Tendsto my f (𝓝 y)) : Tendsto (fun c => (mx c, my c)) f (𝓝 (x, y))` | `Mathlib/Topology/Constructions/SumProd.lean:329` |
| closure の最小性 / 包含 | `closure_minimal` / `subset_closure` | `theorem closure_minimal (h₁ : s ⊆ t) (h₂ : IsClosed t) : closure s ⊆ t` / `theorem subset_closure : s ⊆ closure s` | `Mathlib/Topology/Closure.lean:199` / `:193` |
| union の分解 | `Set.iUnion_subset` | `theorem iUnion_subset {s : ι → Set α} {t : Set α} (h : ∀ i, s i ⊆ t) : ⋃ i, s i ⊆ t` | `Mathlib/Data/Set/Lattice.lean:142` |
| 等号の組み立て | `Set.Subset.antisymm` | `theorem Subset.antisymm {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b` | `Mathlib/Data/Set/Basic.lean:278` |
| `max` の単調性 | `max_le_max` | `theorem max_le_max (h₁ : a ≤ b) (h₂ : c ≤ d) : max a c ≤ max b d` | `Mathlib/Order/Lattice.lean` |
| 摂動重みの連続性 | `Real.binEntropy_continuous` / `Real.binEntropy_nonneg` | (S7 が既に消費、署名は `bc-s7-fullsupport-inventory.md` が SoT) | `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean` |

⚠ **Mathlib には相互情報量が無い** (`rg 'def mutualInfo' Mathlib/` は **0 件**、
`Mathlib/InformationTheory/` は `Coding` / `Hamming.lean` / `KullbackLeibler` の 3 つのみ)。
したがって「入力法についての `I(X;Y)` の凹性」も Mathlib には無いが、**これは壁ではない** (§Q7)。

### 4-2 in-project (既存、逐語再利用)

| 用途 | 宣言 | 逐語署名 / 結論形 | file:line |
|---|---|---|---|
| ★ クラス述語 | `IsBCMoreCapable` | `def IsBCMoreCapable (W : BCChannel α β₁ β₂) : Prop := ∀ (p : Measure α) [IsProbabilityMeasure p], mutualInfoOfChannel p (Kernel.snd W) ≤ mutualInfoOfChannel p (Kernel.fst W)`。section 変数は `{α : Type u} {β₁ β₂ : Type*}` + `[Fintype _] [DecidableEq _] [Nonempty _] [MeasurableSpace _] [MeasurableSingletonClass _]` を 3 型に (`Classes.lean:47`–`:50`) | `Classes.lean:75` |
| 包含鎖 | `IsBCLessNoisy.isBCMoreCapable` | `theorem IsBCLessNoisy.isBCMoreCapable {W : BCChannel α β₁ β₂} [IsMarkovKernel W] (hln : IsBCLessNoisy W) : IsBCMoreCapable W` (`@[entry_point]`) | `Classes.lean:218` |
| ★ 達成側の入口 | `bc_achievability_of_rate_lt` | `(pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a}) (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) {R₁ R₂ : ℝ} (hR₁lt : R₁ < bcInfo₁ pU K W) (hR₂lt : R₂ < bcInfo₂ pU K W) (hJlt : max R₁ 0 + R₂ < bcInfoJoint pU K W) {ε' : ℝ} (hε' : 0 < ε') : ∃ N : ℕ, ∀ n, N ≤ n → ∃ (M₁ M₂ : ℕ) (_hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁) (_hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂) (c : BroadcastCode M₁ M₂ n α β₁ β₂), (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε'` | `Achievability/Assembly.lean:1103` |
| 3 情報量 | `bcInfo₂` / `bcInfo₁` / `bcInfoJoint` | `entropy μ Prod.fst + entropy μ Y₂ - entropy μ (U,Y₂)` / `entropy μ (U,X) + entropy μ (U,Y₁) - entropy μ (U,X,Y₁) - entropy μ U` / `entropy μ (U,X) + entropy μ Y₁ - entropy μ (U,X,Y₁)` (`μ := bcJointDistribution pU K W`) | `Achievability/Setup.lean:100` / `:111` / `Achievability/ErrorAnalysis.lean:929` |
| 結合法 | `bcJointDistribution` | `noncomputable def bcJointDistribution (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) : Measure (U × α × β₁ × β₂) := ((pU ⊗ₘ K) ⊗ₘ (W.comap Prod.snd measurable_snd)).map MeasurableEquiv.prodAssoc` | `Achievability/Setup.lean:54` |
| S3 スロット同定 | `bcInfo₂_eq_mutualInfo_toReal` / `bcInfoJoint_eq_mutualInfo_toReal` / `bcInfo₁_eq_condMutualInfo_toReal` | `= (mutualInfo (bcJointDistribution pU K W) (fun q ↦ q.1) (fun q ↦ q.2.2.2)).toReal` / `= (mutualInfo … (fun q ↦ (q.1, q.2.1)) (fun q ↦ q.2.2.1)).toReal` / `= (condMutualInfo … (fun q ↦ q.2.1) (fun q ↦ q.2.2.1) (fun q ↦ q.1)).toReal` | `Superposition/Region.lean:78` / `:90` / `:110` |
| 非負性 | `bcInfo₁_nonneg` | `(pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] : 0 ≤ bcInfo₁ pU K W` | `Superposition/Region.lean:50` |
| 操作的側 | `bc_capacityRegion_isClosed` / `bc_mem_closure_of_strictly_below` / `bc_capacity_subset_uv` | `IsClosed (bcCapacityRegion W)` / 「厳密に下にある点が全部達成可能なら closure に入る」/ `bcCapacityRegion W ⊆ bcOuterRegionUV W` (**明示仮説ゼロ**) | `Operational.lean:102` / `:86` / `OuterBoundUV/Assembly.lean:839` |
| ★ 外界の 4 制約 | `InBCOuterRegionUV` | `structure InBCOuterRegionUV (R₁ R₂ I₁ I₂ J₂ J₁ : ℝ) : Prop where bound₁ : R₁ ≤ I₁; bound₂ : R₂ ≤ I₂; sumBound₂ : R₁ + R₂ ≤ J₂; sumBound₁ : R₁ + R₂ ≤ J₁` | `OuterBoundUV.lean:735` |
| 外界の領域 | `uvRegion` / `bcOuterRegionUV` | `{p | InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}` / `closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂)) (_ : IsUVChannelLaw W ↑ν), uvRegion ↑ν)` | `OuterBoundUV/Region.lean:413` / `:425` |
| 4 スロット | `uvInfo₁` / `uvInfo₂` / `uvInfoSum₂` / `uvInfoSum₁` | `mutualInfo ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.1)` / `mutualInfo ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.2)` / `uvInfo₂ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)` / `uvInfo₁ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.1)` | `OuterBoundUV/Bridge.lean:777` / `:782` / `:787` / `:792` |
| チャネル法の定義と特徴づけ | `IsUVChannelLaw` / `isUVChannelLaw_iff` | `ν.map (fun q ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) = (ν.map fun q ↦ (q.1, q.2.1, q.2.2.1)) ⊗ₘ W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)` | `OuterBoundUV/Region.lean:116` / `:137` |
| ★ 入出力の周辺化 | `IsUVChannelLaw.map_input_output` | `{W : BCChannel α β₁ β₂} [IsMarkovKernel W] {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) : ν.map (fun q ↦ (q.2.2.1, q.2.2.2)) = (ν.map fun q ↦ q.2.2.1) ⊗ₘ W` | `OuterBoundUV/Region.lean:240` |
| 補助の swap | `IsUVChannelLaw.swap_auxiliaries` | `… (h : IsUVChannelLaw W ν) : IsUVChannelLaw W (ν.map fun q ↦ (q.2.1, q.1, q.2.2))` | 同 `:215` |
| 補助の付け替え | `IsUVChannelLaw.map_auxiliaries` | `{U' V' : Type*} [MeasurableSpace U'] [MeasurableSpace V'] … {f : U → U'} {g : V → V'} (hf : Measurable f) (hg : Measurable g) : IsUVChannelLaw W (ν.map fun q ↦ (f q.1, g q.2.1, q.2.2))` | 同 `:189` |
| Markov 鎖 3 本 | `.isMarkovChain_UV_X_Y` / `_U_X_Y₁` / `_V_X_Y₁` | `IsMarkovChain ν (fun q ↦ (q.1, q.2.1)) (fun q ↦ q.2.2.1) (fun q ↦ (q.2.2.2.1, q.2.2.2.2))` / `IsMarkovChain ν (fun q ↦ q.1) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)` / 同 `q.2.1` 版。**`section Transport` が `[StandardBorelSpace _] [Nonempty _]` を 5 型すべてに + `[IsProbabilityMeasure ν]` を要求** | 同 `:293` / `:311` / `:331` |
| ★ 混合の平均化 | `condMutualInfo_compProd_fst_eq_lintegral` | `lemma condMutualInfo_compProd_fst_eq_lintegral [Countable T] [MeasurableSingletonClass T] (μ : Measure T) [IsProbabilityMeasure μ] (κ : Kernel T S) [IsMarkovKernel κ] {f : S → A} {g : S → B} (hf : Measurable f) (hg : Measurable g) : condMutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) Prod.fst = ∫⁻ t, mutualInfo (κ t) f g ∂μ`。section 変数 `{T S A B : Type*} [MeasurableSpace T] [MeasurableSpace S] [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]` | `Shannon/CondMutualInfoMixture.lean:102` |
| ★ tag 付き混合の分解 | `mutualInfo_compProd_eq_add_lintegral` | `… {tag : A → T} (htag : Measurable tag) (hrec : ∀ᵐ p ∂(μ ⊗ₘ κ), tag (f p.2) = p.1) : mutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) = mutualInfo (μ ⊗ₘ κ) Prod.fst (fun p ↦ g p.2) + ∫⁻ t, mutualInfo (κ t) f g ∂μ` | 同 `:142` |
| 再符号化不変 | `mutualInfo_eq_of_leftInverse` | `(μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → A) (Yo : Ω → γ) (hU : Measurable U) (hYo : Measurable Yo) {f : A → B} {g : B → A} (hf : Measurable f) (hg : Measurable g) (hgf : ∀ a, g (f a) = a) : mutualInfo μ (fun ω ↦ f (U ω)) Yo = mutualInfo μ U Yo` | 同 `:40` |
| pushforward 不変 | `mutualInfo_map_comp` / `condMutualInfo_map_comp` / `condMutualInfo_map_comp'` | `mutualInfo (μ.map T) f g = mutualInfo μ (fun ω ↦ f (T ω)) (fun ω ↦ g (T ω))` / 条件付き版 / `(ρ : Measure Ω') [IsFiniteMeasure ρ] (hρ : ρ = μ.map T) : condMutualInfo ρ f g h = condMutualInfo μ (f∘T) (g∘T) (h∘T)` | `ChannelCoding/CodeToAmbient.lean:435` / `:465` / `:527` |
| 連鎖律 / DPI / 消失 | `mutualInfo_chain_rule` / `mutualInfo_le_of_markov` / `condMutualInfo_eq_zero_of_markov` | `mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc` / DPI / Markov 鎖なら条件付き相互情報量 0 | `Shannon/CondMutualInfo.lean:214` / `:356` / `:339` |
| Markov 鎖の付け替え | `isMarkovChain_map_left` / `isMarkovChain_swap` | (`_U_X_Y₂` の自作で逐語に使う) | `Shannon/CondMutualInfo.lean:570` / `Shannon/CondEntropyMemoryless.lean:330` |
| チャネル情報量 | `mutualInfoOfChannel` / `jointDistribution` / `mutualInfoOfChannel_eq_mutualInfo_prod` | `klDiv (jointDistribution p W) (p.prod (outputDistribution p W))` / `p ⊗ₘ W` / `mutualInfoOfChannel p W = mutualInfo (jointDistribution p W) Prod.fst Prod.snd` | `ChannelCoding/Basic.lean:81` / `:51` / `:92` |
| S5 量子化一族 | `uvQuantizeLaw` / `_isUVChannelLaw` / `uvInfo₁_uvQuantizeLaw` / `uvQuantizeSlack_ne_top` / 裾 3 本 | `ν.map (uvRelabel (uvQuantize.{u} m) id)` / … / `uvInfo₁ (uvQuantizeLaw.{u} ν m) = uvInfo₁ ν` / … | `OuterBoundUV/Quantization.lean:196` / `:212` / `:225` / `:251` / `:352` `:358` `:374` |
| スロットの有限性 | `uvInfo₂_ne_top` / `uvInfoSum₂_ne_top` / `mutualInfo_ne_top_of_fintype_right` | `≠ ∞` | 同 `:104` / `:108` / `:59` |
| 再ラベル | `uvRelabel` / `measurable_uvRelabel` / `uvInfo₁_map_uvRelabel` / `uvInfo₂_map_uvRelabel` | `fun q ↦ (e₁ q.1, e₂ q.2.1, q.2.2)` / … | `OuterBoundUV/Assembly.lean:134` / `:138` / `:143` / `:155` |
| S6 混合一族 | `boolLaw:70` / `lintegral_boolLaw:82` / `uvMixLaw:130` / `uvMixLaw_eq:139` / `uvMixKernel_ae_tag:147` / `uvMixLaw_map_forget:187` / `uvMixLaw_isUVChannelLaw:194` / `uvCollapse:227` / `uvTimeShareLaw:253` / `_isUVChannelLaw:267` | (§Q5 に前提の注意) | `Superposition/TimeShare.lean` |
| S6 スロットの補間 | `mul_uvInfo₂_le_uvInfo₂_uvTimeShareLaw:315` / `condMutualInfo_uvTimeShareLaw:366` | 後者の結論は `= lam * condMutualInfo ν X Y₁ U + (1 - lam) * mutualInfo ν X Y₁` (**第 3 スロットが素の項として既に現れている**) | 同 |
| S6 対の取り出し | `uvCloudLaw:409` / `uvSatelliteKernel:414` / `bcJointDistribution_uvCloudLaw:431` / `bcInfo₂_uvCloudLaw:459` / `bcInfo₁_uvCloudLaw:466` / `bcInfoJoint_uvCloudLaw:475` | `bcInfoJoint (uvCloudLaw ν) (uvSatelliteKernel ν) W = (mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)).toReal` | 同 |
| S6 着地 | `boolProdAuxEquiv:501` / `condMutualInfo_map_uvRelabel:517` / `exists_bcInfo_ge_of_tagged:546` | `Bool × bcAuxAlphabet m ≃ bcAuxAlphabet (2*m+1)` | 同 |
| S7 摂動一族 | `uvUniformLaw:111` / `_isUVChannelLaw:121` / `uvPerturbLaw:127` / `_isUVChannelLaw:142` / `_map_aux_input_pos:174` / `exists_perturb_weight:429` / `uvCloudLaw_real_singleton_pos:84` / `uvSatelliteKernel_real_singleton_pos:59` | `exists_perturb_weight {A B δ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ε * A + Real.binEntropy ε < δ ∧ ε * B + Real.binEntropy ε < δ` | `Superposition/FullSupport.lean` |
| S7 スロットの損失 | `mul_condMutualInfo_le_condMutualInfo_uvPerturbLaw:380` / `mul_uvInfo₂_sub_binEntropy_le_uvInfo₂_uvPerturbLaw:405` / 一般混合版 `:224` `:250` | (§Q5) | 同 |
| S8 裾の `.toReal` | `uvInfo₂_toReal_sub_slack_le:54` / `uvInfoSum₂_toReal_sub_slack_le:64` | `(uvInfo₂ ν).toReal - (uvQuantizeSlack ν m).toReal ≤ (uvInfo₂ (uvQuantizeLaw.{u} ν m)).toReal` | `Superposition/Assembly.lean` |
| 補助アルファベット | `Marton.bcAuxAlphabet` | `abbrev`、`= ULift.{u} (Fin (m+1))` | `MartonUnion.lean:52` |

### 4-3 自作が要るもの (**計 12 本 / probe 実測 525 行、すべて probe で証明済**)

| # | 宣言 | 内容 | probe 実測 | 置き場 (推奨) |
|---|---|---|---|---|
| 1 | `condMutualInfo_congr_measure` | `(h : μ = ρ) : condMutualInfo μ Xs Yo Zc = condMutualInfo ρ Xs Yo Zc`。`subst h; rfl` **2 行**。⚠ `rw` では `motive is not type correct` (`condMutualInfo` が `[IsFiniteMeasure μ]` を持つ) | **8** | 汎用 ⟹ `Shannon/CondMutualInfo.lean` (F-15 の轍を踏まない)。✅ **採用 `:76`** (`730844a1`。移設前に結論形でも検索し同等物の不在を確認 — 最近縁は `mutualInfo_congr_ae` / `entropy_eq_of_identDistrib` でどちらも包含しない) |
| 2 | `mutualInfo_congr_pair` | 結合周辺分布が一致すれば `mutualInfo` が一致 | **18** | 汎用 ⟹ `Shannon/MutualInfo.lean`。✅ **採用 `:46`** (同上) |
| 3 | `mutualInfo_compProd_out₁` / `_out₂` | `mutualInfo (p ⊗ₘ W) Prod.fst (fun s ↦ s.2.1) = mutualInfoOfChannel p (Kernel.fst W)` / `snd` 版 | **20** | 汎用寄り ⟹ `ChannelCoding/Basic.lean` か BC 側 (判断は F-15 と同軸)。✅ **BC 側に留置** (`MoreCapable.lean:97` / `:106`) — 結論が `mutualInfoOfChannel` × BC の出力射影という組で、単独の汎用 API にならない |
| 4 | `bcJointDistribution_eq_compProd` + `kernel_slice` | `bcJointDistribution pU K W = pU ⊗ₘ (K ⊗ₖ W.comap Prod.snd)` (`Measure.compProd_assoc'` **1 行**) + スライス | **12** | `Classes.lean` |
| 5 | ★ `condMutualInfo_bcJoint_out₁` / `_out₂` + **`IsBCMoreCapable.condMutualInfo_le`** | §Q2-1。`IsBCMoreCapable` の条件付き版 | **40** | `Classes.lean` (`IsBCMoreCapable` の隣)。**`import InformationTheory.Shannon.CondMutualInfoMixture` を 1 行追加** |
| 6 | `uvInfoJoint` (def) + `uvInfoJoint_map_uvRelabel` | `mutualInfo ν X Y₁` に名前を付ける + 補助の付け替え不変性 | **14** | `OuterBoundUV/Bridge.lean` の 4 スロットの隣 (def) / `OuterBoundUV/Assembly.lean:143` の隣 (不変性)。⚠ 現状この項は **`TimeShare.lean` の 5 箇所でベタ書き**されており (`:357` `:371` `:478` `:585` `:589`)、def が無い = F-6「`martonInfoSum` が実在しない識別子」と同じ失敗モード。**実測では置換対象が 7 箇所**だった — この 5 箇所に加え、**def を作った leg 自身が `MoreCapable.lean` に 2 箇所ベタ書きを残した** ⟹ 「def 化 leg」のチェックリストは既存箇所だけでなく**同 leg の新規コードも走査対象**にする |
| 7 | `uvInfoJoint_smul_add_smul` + `uvInfoJoint_uvTimeShareLaw` | 時分割は `I(X;Y₁)` を**等式で**保つ | **35** | 上と同じ束 (混合を使うので `Superposition/TimeShare.lean` 側) |
| 8 | `mutualInfo_pair_out₁_eq_uvInfoJoint` | 「`X` に何を足しても `Y₁` への情報は増えない」(`bcInfoJoint_uvCloudLaw:481`–`:494` の中身を総称化) | **20** | `OuterBoundUV/Region.lean` の `section Transport` の隣。**`bcInfoJoint_uvCloudLaw` はこれを使う形にリファクタできる** |
| 9 | `IsUVChannelLaw.isMarkovChain_U_X_Y₂` | `_U_X_Y₁:311` の逐語ミラー | **18** | `OuterBoundUV/Region.lean` `_U_X_Y₁` の直後 |
| 10 | ★ `uvInfoJoint_eq_uvInfo₁_add_cond` + `condMutualInfo_out₂_le_out₁_of_moreCapable` + **`uvInfoSum₁_le_uvInfoJoint_of_moreCapable`** | §Q2-1 の ν レベル | **85** | 新ファイル |
| 11 | `mutualInfo_out₂_le_out₁_of_moreCapable` + **`uvInfo₂_le_uvInfoJoint_of_moreCapable`** | §Q2-2 の ν レベル | **45** | 新ファイル |
| 12 | ★ `mul_uvInfoJoint_le_uvInfoJoint_uvMixLaw` + `_uvPerturbLaw` | `I(X;Y₁)` の入力法についての凹性 (tag の連鎖律経由)。`mul_uvInfo₂_le_uvInfo₂_uvMixLaw:224` と**骨格が逐語** | **55** | 新ファイル (`uvMixLaw` の下流) |
| 13 | S6 変種 `exists_bcInfo_ge_sumRate_of_tagged` + `exists_bcInfo_ge_sumRate_of_isUVChannelLaw` | §Q3 の S6 行 | **95** | 新ファイル |
| 14 | 領域 `bcSuperpositionRegionSumRate` + `_isClosed` + `_subset_capacity` | §Q1-1 / Q1-2 | **45** | 新ファイル |

**未 probe (見積りのみ)**: S7 変種の組み立て (~45) / S7 の pair-level + compose (~35) /
S8 変種一式 (`uvInfoJoint_uvQuantizeLaw` 3 行 + `.toReal` 橋 + 点レベル 2 本 + 2 重極限 +
逆包含 + headline 2 本、~130)。計 **~210 行**。

---

## Q5 前提が事故りやすい箇所 (key-preconditions box)

- ★ **`condMutualInfo` の中の測度を `rw` で書き換えると `motive is not type correct`**
  (`[IsFiniteMeasure μ]` が測度に依存するため)。`Prop` クラスなので **`subst` 経由の
  `condMutualInfo_congr_measure` (自作 #1、2 行) で通る**。probe で 1 度踏んだ。
  S7 が同じ罠を `condMutualInfo_le_condMutualInfo_of_isUVChannelLaw_of_map_forget`
  (`FullSupport.lean:298`–`:304`) の「測度をパラメータで受ける」設計で回避している。
- ★ **`condMutualInfo_compProd_fst_eq_lintegral` は tag 型に `[Countable T]
  [MeasurableSingletonClass T]` を課す**。more capable の条件付き化では `T` = 補助変数の型。
  外界の第 2 補助は `ℕ` なので埋まるが、**headline の型クラス束には現れない**ことを probe で確認。
- ★ **`IsUVChannelLaw` の Markov 鎖 3 本 (`section Transport`) は 5 型すべてに
  `[StandardBorelSpace _] [Nonempty _]` + `[IsProbabilityMeasure ν]` を要求する**
  (四つ組法 `map_auxiliary_input_output:257` は要求しない)。自作 #9 `_U_X_Y₂` も同じ束に入る。
- **`Measure.compProd_assoc'` は `MeasurableEquiv.prodAssoc` の向きに敏感**。
  `bcJointDistribution` は `.map MeasurableEquiv.prodAssoc` なので `'` 付き (順方向) が当たる。
  `'` 無しは逆向き (`prodAssoc.symm`) なので `rw` が空振りする。
- **`Kernel.compProd_apply_eq_compProd_sectR` の後は `congr 1` だけで閉じる**
  (`Kernel.sectR (W.comap Prod.snd _) u = W` が定義的に成り立つ)。`Kernel.ext fun _ ↦ rfl` を
  足すと `No goals` で落ちる (probe で 1 度踏んだ)。
- **`mutualInfo_map_comp` の後に `rfl` が要る場合がある** — `Prod.map id f` を噛ませた形は
  射影が syntactic に一致しない。probe で 2 箇所。
- **`uvPerturbLaw W ν v₀ lam` は `(lam ⊓ 1) • ν + (1 - lam) • uvUniformLaw W v₀` と `rfl` で等しい**
  が syntactic には別。`uvMixLaw_map_forget` を当てるには
  `have hflat : … = uvPerturbLaw … := rfl` を挟む (`FullSupport.lean:421` と同じ手)。
- **`exists_perturb_weight` は 2 引数のまま `A := A + J` で 3 量に流用できる**
  (`ε*A + h(ε) ≤ ε*(A+J) + h(ε) < δ` と `ε*J + h(ε) < δ` が同時に出る)。**3 引数版を新設しない**。
- ★ **`add_le_add_left` / `add_le_add_right` は 2 本とも名前から期待する向きの逆** (`#check` で逐語
  確認: `add_le_add_left : b ≤ c → ∀ a, b + a ≤ c + a` / `add_le_add_right : b ≤ c → ∀ a, a + b ≤ a + c`)。
  **本在庫は当初 `add_le_add_left` の側だけを注記しており、実装 leg は逆側で同じ罠を踏んだ**。
  回避は向きを問わず **`add_le_add le_rfl h`** (左固定) / **`add_le_add h le_rfl`** (右固定)。
- **S6 変種の凸結合は `nlinarith` に 2 本のヒントが要る**:
  `mul_le_mul_of_nonneg_left hsum' hlam0.le` と `mul_le_mul_of_nonneg_left hs₁' (1-lam ≥ 0)`。
  `linarith` 単独では通らない (積が入るため)。
- **`max R₁ 0 + R₂ ≤ J ⟹ R₁ + R₂ ≤ J`** は `le_max_left` 1 本。逆は成り立たない。
  S6 変種の内部では弱い方 (`R₁+R₂ ≤ J`) しか使わないので、入口で 1 行落とす。

---

## Q6 probe (すべて `lake env lean -D linter.mathlibStandardSet=true -D linter.unusedFintypeInType=false` で **exit 0 / error 0**)

scratchpad = `/private/tmp/claude-502/-Users-haruka-dev-lean-projects/7f8f7cc1-41d3-4825-81dd-c7d104369c95/scratchpad`
(`InformationTheory/` は 1 バイトも触っていない)。

| probe | 内容 | 結果 | 行数 / decl |
|---|---|---|---|
| **MC0** `ProbeMC0Setup` | S3 の逐語再利用 / 3 制約領域の型 / `bc_achievability_of_rate_lt` の第 3 仮説 / headline の形 / `max` 版の下方集合性 | ✅ | 78 / 6 |
| **MC1** `ProbeMC1TimeShare` | `uvInfoJoint` + 再ラベル不変 + **時分割不変 (等式)** + **S6 変種 2 本 (クラス仮説なし)** | ✅ | 214 / 7 |
| **MC2** `ProbeMC2CondMoreCapable` | ★ **`IsBCMoreCapable.condMutualInfo_le`** (条件付き more capable) | ✅ | 108 / 8 |
| **MC3** `ProbeMC3SumBound` | ★ **`uvInfoSum₁_le_uvInfoJoint_of_moreCapable`** (MC2 を内包) | ✅ | 210 / 13 |
| **MC4** `ProbeMC4Perturb` | ★ `I(X;Y₁)` の混合下の凹性 + 摂動版 | ✅ | 131 / 5 |
| **MC5** `ProbeMC5Region` | ★ 3 制約領域 + 閉性 + **クラス仮説なしの達成可能性** + less noisy 退化 + 負レート点 | ✅ | 89 / 5 |
| **MC6** `ProbeMC6Corner` | ★ `isMarkovChain_U_X_Y₂` + `uvInfo₂_le_uvInfoJoint_of_moreCapable` | ✅ | 105 / 5 |
| 計 | | | **935 / 49** (重複を除いた実装相当 **約 525 行**) |

**通らなかったもの (逐語エラー、実装時に再発する)**:

1. `rw [bcJointDistribution_eq_compProd …]` → `motive is not type correct` (§Q5 の 1 本目)。
2. `rw [← Measure.map_map measurable_fst (hf.prodMk hg)]` が `Prod.fst ∘ (f, g)` の形で空振り
   → `have e1 : (μ.map (f,g)).map Prod.fst = μ.map f := Measure.map_map …` を先に立てる。
3. `Kernel.compProd_apply_eq_compProd_sectR` の後の `exact Kernel.ext fun _ ↦ rfl` が `No goals`。
4. `measurable_const (b := u₀)` は名前付き引数が違う → `(a := u₀)`。
5. `add_le_add_left` の向き (§Q5)。
6. `rw [← uvMixLaw_map_forget …]` が `uvPerturbLaw` の形で空振り → `hflat : … := rfl` を挟む。

⚠ **CLAUDE.md / 判断ログ 26 の但し書き**: 「probe で機械確認済」が保証するのは
**probe が確かめた等式だけ**で、重複の個数にも instance 探索の透明度にも及ばない。とくに
自作 #6 `uvInfoJoint` は非 reducible な `def` になるので、`condMutualInfo_uvTimeShareLaw` の
ベタ書き項との照合は **`have hexp : … := condMutualInfo_uvTimeShareLaw …` と明示型で受ける**
必要がある (probe で 1 度踏んだ。`rw` の pattern match は通らない)。

⚠ **その `rw` 失敗リスクは実測で向きが逆だった** — 本在庫は「**consumer** が旧ベタ書き形に `rw`
していると落ちる」と予測したが、F-28 の実測では **consumer 側の修正は 0 箇所**で、落ちたのは
`bcInfoJoint_uvCloudLaw` **自身の証明本文** (`rfl` 1 行で解決)。逆に副産物として、leg B が置いた
`show … from rfl` 2 箇所が不要になり削除された。⟹ **予測が及ばないのは「個数」と「自動性」だけで
なく「波及の向き」も**であり、非 reducible 化の影響範囲は下流とは限らない。

---

## Q7 壁 / 撤退ライン

### Mathlib の壁 — **0 件** (BC 家系 9 leg 連続) / プロジェクト側の壁も **0 件**

| クエリ (軸) | 結果 | 影響 |
|---|---|---|
| loogle `MeasureTheory.Measure.compProd_assoc'` | `Found one declaration` | `bcJointDistribution` を tag 付き compProd に開く鍵。**1 行** |
| loogle `ProbabilityTheory.Kernel.sectR` | `Found 15 declarations` (含 `compProd_apply_eq_compProd_sectR`) | カーネルのスライスは既存 |
| loogle `MeasureTheory.mutualInfo` / `InformationTheory.Shannon.mutualInfo` | **`unknown identifier`** | **Mathlib に相互情報量は無い** (loogle は Mathlib しか見ない) |
| `rg 'def mutualInfo\|mutualInformation' .lake/packages/mathlib/Mathlib/` | **0 件** (`Mathlib/InformationTheory/` は `Coding` / `Hamming.lean` / `KullbackLeibler` のみ) | ⟹ 「入力法についての `I(X;Y)` の凹性」も Mathlib に**無い** |
| 結論形の再検索 (二段目): `rg 'ConcaveOn\|ConvexOn' Mathlib/InformationTheory/` | 5 件、すべて `klFun` の凸性 (`KLFun.lean:62`–`:71`) | 凹性の**部品**はある (`klDiv` の凸性) が、`mutualInfo` が無い以上そのままでは当たらない |
| in-project 結論形: `rg 'mutualInfo \S+ \(fun q ↦ q\.2\.2\.1\) \(fun q ↦ q\.2\.2\.2\.1\)'` | **5 件** (`TimeShare.lean:357` `:371` `:478` `:585` `:589`) | **第 3 スロットは既にベタ書きで在る。def が無いだけ** ⟹ 自作 #6 は「新しい数学」ではなく命名 |
| in-project 名前: `rg 'IsBCMoreCapable'` | 定義 1 + 消費 1 (`Classes.lean:218`)。`dep_consumers.sh` 実測 **direct 1 decl / 1 file** | クラスは実質未使用。本 leg が最初の本格的な消費者 |
| in-project: `rg 'isMarkovChain.*Y₂\|_X_Y₂'` | ν レベルは **0 件** (ヒットは `Bridge.lean` の符号側 ambient のみ) | 自作 #9 は重複ではない |
| in-project: `rg 'condMutualInfo_congr'` | **0 件** | 自作 #1 は重複ではない |

**「Mathlib に無い」を壁と呼ばない根拠 (CLAUDE.md の 2 条件)**:
(a) 二段目の結論形検索を実施 (上表)。(b) **期待する結論形に近い template lemma を名指しできる** —
`mul_uvInfo₂_le_uvInfo₂_uvMixLaw` (`FullSupport.lean:224`) が**骨格まで逐語**で、
`tag` を回収する変数を `q.1` から `(q.1, q.2.2.1)` に替えるだけ。自作見積り **55 行**、
**probe MC4 で実際に 55 行で通った**。⟹ 分類は「Mathlib 不在の gap」ではなく
**既存資産への配線 (plumbing)**。

### L-BCO3 との距離 — **不発動**

発動条件は「**Phase 5 の等号が Phase 4 の外界の形と噛み合わない**」で、残る判定対象は
more capable のみ (親 plan `:442`)。

- **外界の形との噛み合い: 問題なし。むしろ逆** — less noisy の逆包含が
  `obtain ⟨hb₁, hb₂, hs₂, -⟩` で**捨てていた** 4 本目 `sumBound₁` が、more capable では
  第 3 制約の担い手そのものになる (§Q2-1)。外界は既に必要な制約を持っている。
- **内界の形との噛み合い: 定義の拡張が要るが、追加の数学は 0 行** — plan が記録するとおり
  less noisy での噛み合わなさの本体は内界側だったが、more capable では
  `bc_achievability_of_rate_lt` が**すでに第 3 仮説を持っている** (S0 の factor out の副産物) ので、
  内界の 3 制約化は def の 1 連言追加で済む (probe MC5)。⟹ **どちらの側にもリスクは残らない**。
- **仮に発動したときの退避先 (提案、今回は使わない)**: 逆包含
  `bc_moreCapable_uv_subset_superposition` を**署名を保ったまま** `sorry` +
  `@residual(plan:bc-morecapable-converse)` で残す。**`IsMoreCapableTight` のような
  「等号が成り立つ」を束ねる述語は作らない** (L-BCO9 が後続クラスへ引き継いだ禁止)。
  今回は逆包含の 5 本すべてが probe で通っているので**退避の必要が無い**。

**L-BCO7 (semi-deterministic の全支持) との関係**: more capable は
`hW : ∀ a b, 0 < (W a).real {b}` と**構造的に非両立ではない** (§Q2-3)。判断ログ 13 の罠は
本クラスでは発火しない。

**本在庫のどの補題にも `@residual` を付けない** — probe で全証明が compile 通過しており、
埋まらない穴は 1 つも残っていない。

---

## Q8 行数見積り (**数学と散文・section を別枠**、親 plan 判断ログ 23 / F-26)

### 較正 (自分で測った実測値のみ、`git show <commit>:<path> | wc -l`)

| step | probe | as-landed | 差 | 見積り法 |
|---|---|---|---|---|
| S5 | 147 | **382** (`47933abd`) | **+160%** | 1 列 |
| S6 | 295 | **545** (`dd981e01`) | **+85%** | 1 列 |
| S7 | 745 | **802** (`069c6016`) | **+8%** | **2 列** |
| S8 | 146 (本体 probe) | **163** (`558b3fca`) | 見積り 190 に対し **−14%** | **2 列** |

⟹ **2 列見積りに切り替えた S7 / S8 は ±15% に収まっている**。本在庫も 2 列で積む。
親 plan F-26 が禁じた 2 文はどちらも引かない。

### 見積り表

| 区分 | 内容 | 数学 (probe 実測 / 見積り) | 散文・section | 計 |
|---|---|---|---|---|
| **A. `Classes.lean` 追記** | 自作 #4 #5 (+ 汎用 #1–#3 をどこに置くかで ±) | 62 | 14 | ~76 |
| **B. 汎用 3 本の移設先** | 自作 #1 #2 #3 | 46 | 10 | ~56 |
| **C. `OuterBoundUV/` 追記** | 自作 #6 (def + 不変性) #8 #9 | 52 | 14 | ~66 |
| **D. 新ファイル: スロットと比較** | 自作 #7 #10 #11 #12 | 220 | 30 | ~250 |
| **E. 新ファイル: S6 変種** | 自作 #13 | 95 | 12 | ~107 |
| **F. 新ファイル: S7 変種** | 未 probe (組み立て + pair-level + compose) | 80 | 14 | ~94 |
| **G. 新ファイル: 領域 + S8 変種 + headline** | 自作 #14 (45、probe 実測) + 未 probe S8 一式 (130) | 175 | 26 | ~201 |
| variable 束 / section / import / namespace | | 30 | — | ~30 |
| module doc (新ファイル 1–2 本) | `## Main statements` + 設計 4 段落 (包含関係の説明を含む) | — | 45 | ~45 |
| **計** | | **760** | **165** | **~925** |

**帯は 820–980**。probe が覆っているのは 525 行で、**未 probe が 210 行 (S7 の組み立てと S8 一式)**。
S7 / S8 の組み立ては less noisy 版の**逐語同型**なので上振れは限定的と見るが、
**probe 行数は下限であって予測ではない** (判断ログ 23) — 上限側に S8 変種のスロット 1 本増が効く。

✅ **as-landed 909 行 = 帯の中** (leg A +8% / leg B +17%)。2 列見積りは 3 leg 連続で ±20% 以内。

**ファイル配置の提案**: 新規は 1 本 (`Superposition/MoreCapable.lean`、区分 D–G で ~650 行)。
import は `Superposition.FullSupport` の **1 本**で足りる (`Classes` / `OuterBoundUV/*` は推移的)。

⚠ **本節にあった「600 行を超えたら 2 分割」は無効 (自前ルールの誤り)** — `docs/rules/module-structure.md`
§3 の拘束条件は行数ではなく**関心の混在**で、閾値も 1500 行。909 行の as-landed は module doc が
1 本の筋として書けているため style ゲートが**分割不要**と判定した。規約の SoT は `docs/rules/` 側。
**将来の切れ目だけ決定済**: `MoreCapable/{Comparison,Equality}.lean`
(`{Region,Assembly}` は `Superposition/Region.lean` / `Superposition/Assembly.lean` と
紛らわしいので使わない)。

⚠ **`Classes.lean` を触ると BC 族がほぼ全再ビルドになる** (`Superposition/*` / `OuterBoundUV/*`
の全部が下流)。実装順としては**新ファイルに全部書いて通してから上流へ移す**のが安全
(S8 が `Quantization.lean` に対して採った手と同じ)。

---

## Q9 実装 leg への申し送り

### gateway atom = **`uvInfoSum₁_le_uvInfoJoint_of_moreCapable` (自作 #10)**

**最も決定的な原子。probe MC3 で通過済 (exit 0 / error 0 / sorry 0)**。理由:

- (a) **ここが「more capable で等号が閉じるか」の唯一の分岐点**。ここが通らなければ
  外界の 4 本目から第 3 制約が出ず、L-BCO3 が発動する。
- (b) この 1 本が `IsBCMoreCapable` の条件付き化 (自作 #5、90 行) を丸ごと要求するので、
  ここを目標に置くと自作 #1–#5 #8 #9 の順序が自然に決まる。
- (c) probe でも最初に型が合ったのがここで、以降は機械的だった。

**着手順**: 自作 #1–#5 (条件付き more capable) → **#10 (gateway)** → #6 #7 #8 #9 (スロット API) →
#11 → #12 → #13 (S6 変種) → #14 (領域) → S7 変種 → S8 変種 → headline。

### 親 plan で書き換えが要る箇所 (編集は plan の担当) — ✅ **8 件すべて反映済** (`9eb87b38` / 本 leg)

1. **§残る 2 クラス / §設計上の未決事項 2 / §撤退ライン L-BCO3 の「3 field の新 structure が要る」を撤回** —
   内界は `InBCCapacityRegion` を使っていないので **`structure` は不要**、3 連言の集合内包で足りる
   (§Q1-1、probe MC5)。
2. **§残る 2 クラスの「`uvInfoSum₁` の `V = X` 特殊化で到達可能」を訂正** — `V = X` は
   「内界 ⊆ 外界」の道具であって headline のクリティカルパス (外界 ⊆ 内界) には乗らない。
   実際に要るのは **more capable の条件付き版** (§Q2-1)。
3. **§残る 2 クラスの「S3 / S4 / S5 はそのまま再利用」に注記** — S3 は逐語、S4 と S5 は
   **1 本ずつ追加が要る** (`isMarkovChain_U_X_Y₂` / `uvInfoJoint_uvQuantizeLaw`)。§Q3 が SoT。
4. **§推奨実行順 #2 に見積りを入れる**: `~925 行 (数学 760 + 散文 165)`、帯 820–980。
5. **§撤退ライン L-BCO3 を「不発動」に更新** — 判定の担い手 (more capable) が閉じるので
   L-BCO9 と同じく retire できる。
6. **§在庫に新規行 1 本** (`Superposition/MoreCapable.lean`、import 1 本)。
7. **§後続作業に 3 件追加候補**: (a) `bc_lessNoisy_capacity_eq_uv` を
   `bc_moreCapable_capacity_eq_uv` の系に畳む (§Q1-4、**本 leg ではやらない**)。
   (b) `bcInfoJoint_uvCloudLaw` を自作 #8 の総称形で書き直す (重複 15 行)。
   (c) S6 の `exists_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw` をクラス free な変種の系に畳む。
   ⟹ 親 plan §後続作業 **G-1 / G-3 / G-4**。実測でさらに 3 件増えた (**G-2** `FullSupport` の誤称 /
   **G-5** 規約衝突の起票 / **G-6** ファイル移動を伴う leg は `gen_readme_table.ts --write` を回す)。
8. **§判断ログに 1 件** — 「**plan が『既存の structure では受けきれない』と書いたら、
   その structure を実際に消費しているのが誰かを `rg` で確かめる**」: 内界
   `bcSuperpositionRegionNoSumRate` は `InBCCapacityRegion` を使っておらず、
   `InBCCapacityRegion` の消費者は converse 側 2 箇所 (`Converse.lean:167` / `:596`) だけだった。
   ⟹ 「受け皿の structure が新設で要る」という plan の見立ては**消費者を確認していれば消えていた**。

### 命名の提案 (`docs/rules/naming.md` に合わせる)

`bcSuperpositionRegionSumRate` / `_isClosed` / `_subset_capacity` /
`bc_moreCapable_uv_subset_superposition` / `bc_moreCapable_capacity_eq_uv` /
`bc_moreCapable_superposition_eq_capacity` (クラス限定の定理は名前にクラスを入れる = 判断ログ 25) /
`uvInfoJoint` / `uvInfoJoint_map_uvRelabel` / `uvInfoJoint_uvQuantizeLaw` /
`uvInfoJoint_uvTimeShareLaw` / `mul_uvInfoJoint_le_uvInfoJoint_uvMixLaw` /
`IsBCMoreCapable.condMutualInfo_le` / `uvInfoSum₁_le_uvInfoJoint_of_moreCapable` /
`uvInfo₂_le_uvInfoJoint_of_moreCapable` / `IsUVChannelLaw.isMarkovChain_U_X_Y₂` /
`exists_bcInfo_ge_sumRate_of_isUVChannelLaw`。

⚠ **決着 (style ゲート判定、`506c5184`)**: 旧名 `bcSuperposition3Region` の `3` は制約の本数という
**statement に現れないメタデータ**で `docs/rules/naming.md` 逸脱 ⟹ 一族 **10 本**を
`bcSuperpositionRegionSumRate` / `exists_bcInfo_ge_sumRate_*` へ改名した (本在庫の記述は追随済)。
上で挙げた代案 `bcSuperpositionRegionFullSupportSum` / `bcSuperpositionSumRegion` は
**どちらも不採用**。旧名 `bcSuperpositionRegionFullSupport` が「全支持」を名乗って本質は 2 制約という
指摘は**別 leg (親 plan §後続作業 G-2) で決着し、現行名は `bcSuperpositionRegionNoSumRate`**。
⚠ **本節が名指した `3` 入りの名は 5 本、実測の改名は 10 本** — S7 変種 / `sub_mem_*` / `mem_*` が
「同様に追随」で暗黙に改名された分は数から漏れる。再導出と一般則は親 plan F-26-(c)。

### 検証バー (親 plan F-20)

実装 leg は `lake env lean -D linter.mathlibStandardSet=true -D linter.unusedFintypeInType=false`
を内ループに使い、leg の締めに `lake build InformationTheory.Shannon.BroadcastChannel.Superposition.MoreCapable`
を回す。**本在庫の probe 7 本はこの設定で warning 0**
(`unusedSectionVars` / `unusedDecidableInType` の指摘は probe の variable 束が広すぎるだけで、
実装時は束を絞れば消える — 該当は 12 件、すべて「使っていない `[DecidableEq _]` /
`[StandardBorelSpace _]` を落とせ」)。

⚠ **「warning 0」を実装 leg のバーにしてはいけない (実測が本節を訂正)** — 本在庫が想定していない
既存 warning が BC 家系の他ファイルに実在する (`Superposition/TimeShare.lean` /
`Shannon/CondMutualInfo.lean` / `OuterBoundUV/Bridge.lean`)。**正しいバーは「既存からの増分 0」**で、
確認手順は **HEAD 版を `git show` で取り出して同一設定で lint し、warning 集合が完全一致することを
見る** (件数は触るたび動く機械再導出可能値なので暗記しない)。

**probe の型クラス束は広すぎた (実測が 6 宣言で狭化)** — 例: gateway 中段
`condMutualInfo_out₂_le_out₁_of_moreCapable` は `[Countable V] [MeasurableSingletonClass V]` だけで
足り、`U` / `V` の `[StandardBorelSpace _]` / `[Nonempty _]` は要らない。⟹ 実務則 2 つ:
(a) **`set_option linter.unusedSectionVars false` で抑止せず section を入れ子に割って消す** —
抑止と分割は warning が消える点では同じでも、後者は**必要な型クラス束の実測値が副産物として残る**。
(b) **証明冒頭に `classical` を置けば `DecidableEq` は埋まる** (`bcInfo₁_uvCloudLaw` /
`bc_achievability_of_rate_lt` 側)。実測では新規 12 宣言の型クラス束から `DecidableEq` が完全に消え、
`set_option` 0 行 / `omit` 2 箇所で済んだ。

# BC S6 時分割の補助への吸収 — M0 在庫

> 親 plan (SoT): [`bc-general-region-plan.md`](bc-general-region-plan.md) §Phase 5「等号 (less
> noisy)」S6 / §撤退ライン **L-BCO9** / §後続作業 F-15 F-16。前段の在庫:
> [`bc-s5-quantization-inventory.md`](bc-s5-quantization-inventory.md) /
> [`bc-lessnoisy-equality-inventory.md`](bc-lessnoisy-equality-inventory.md) §Q2-3 §E。
> probe は scratchpad の `ProbeS6{Setup,Mix,Const,Slots,Bridge,Assembly}.lean`
> (6 本すべて `lake env lean` がエラー 0、警告は未使用 section variable のみ)。

## 結論サマリ

- **Q1 = 真。ただしブリーフの設計は 1 本足りない** — 外界の 4 不等式のうち **`bound₁`
  (`R₁ ≤ I(V;Y₁)`) が load-bearing** で、落とすと命題は**偽**になる (§Q1-B に機械確認済の反例)。
  発火するのは `R₂ < 0` の枝だけだが外界も内界も第一象限制約を持たないので**必ず通る枝**。
  埋め方は既存資産 1 本 (`IsUVChannelLaw.isMarkovChain_V_X_Y₁` + DPI) で **3 行**。
- **ブリーフの `I(tag;Y₂) = 0` は不要** — スロット 2 は `≥` で足りるので、混合法が吐く
  `I(tag;Y₂)` 項は `le_add_left` で捨てる。真偽の議論そのものが要らなくなる (§Q1-C)。
- **場合分けは 3 本ではなく 2 本** (`R₂ ≤ 0` / `0 < R₂`)。`b = 0` は前者に吸収され `λ = 1` は
  後者に入る (Lean の `0/0 = 0` がそのまま正しい値、§Q1-D)。
- **Mathlib の壁 0 件 / プロジェクト側の壁も 0 件** (BC 家系 6 leg 連続)。
- **行数見積り ~440 行 (帯 380–480)。うち ~295 行は probe で実測済**。親 plan の `~180 行` は
  **約 2.4 倍への上方修正**が要る (step 内分割は §Q5)。**L-BCO9 は不発動の見込み**。
- **最初に切るべきは S6-a (チャネル法 → 達成側の対 `(pU, K)` の橋、~90 行)** — less noisy を
  `ν` 側に持ち込む唯一の入口で、S6-e / S7 / S8 のすべてが前提にする。

### 最も危ない発見 (1 行)

**`bound₁` を落とすと逆包含は偽**: `a = b = J = 0`, `R₁ = 1`, `R₂ = -2` は `R₂ ≤ b` と
`R₁ + R₂ ≤ a + b` を満たすのに `R₁ > J`。ブリーフの設計 (この 2 本だけ) はこの点を被覆できない
(反例は Lean で機械確認済、§Q4 P5)。親 plan の擬似 Lean にも同じ穴が開いている。

## Q1 設計の真偽 — **真 (1 点補正のうえで)**

### Q1-A 実 def との照合 (逐語)

| 記号 | 実体 | file:line |
|---|---|---|
| `b` | `uvInfo₂ ν = mutualInfo ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.2)` | `OuterBoundUV/Bridge.lean:782` |
| `a` | `uvInfoSum₂ ν = uvInfo₂ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)` の第 2 項 | `Bridge.lean:787` |
| `c` | `uvInfo₁ ν = mutualInfo ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.1)` (= `I(V;Y₁)`) | `Bridge.lean:777` |
| 外界の点 | `structure InBCOuterRegionUV (R₁ R₂ I₁ I₂ J₂ J₁ : ℝ) : Prop where bound₁ : R₁ ≤ I₁ ; bound₂ : R₂ ≤ I₂ ; sumBound₂ : R₁ + R₂ ≤ J₂ ; sumBound₁ : R₁ + R₂ ≤ J₁` | `OuterBoundUV.lean:735` |
| 内界の矩形 | `{p : ℝ × ℝ \| p.1 ≤ bcInfo₁ pU K W ∧ p.2 ≤ bcInfo₂ pU K W}` の全支持 union の closure | `Shannon/BroadcastChannel/Superposition/Region.lean` |

⟹ ブリーフの `a := I(X;Y₁∣U)` / `b := I(U;Y₂)` は実 def と逐語一致 ✅。外界の点が持つ 4 本のうち
S6 が使うのは `bound₁` / `bound₂` / `sumBound₂` の 3 本 (`sumBound₁` は使わない)。

### Q1-B **補正**: `bound₁` が load-bearing

`R₂ < 0` のとき `sumBound₂` は `R₁ ≤ a + b - R₂` しか与えず、右辺は `I(X;Y₁)` を**超えうる**。
内界側は `bcInfo₁ ≤ log |β₁|` で有界なので `bound₁` なしでは被覆できない
(反例 `a = b = J = 0, R₁ = 1, R₂ = -2`、§Q4 P5 の 3 本目が `norm_num` で通過)。
埋め方は `bound₁` から `R₁ ≤ (uvInfo₁ ν).toReal` を取り **DPI 1 発** (`V → X → Y₁`、probe 通過):

```lean
mutualInfo_le_of_markov ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
  (by fun_prop) (by fun_prop) (by fun_prop) h.isMarkovChain_V_X_Y₁
```

### Q1-C **`I(tag;Y₂) = 0` は真だが不要**

両枝の `X` 周辺を揃えれば `tag ⊥ X` で、`tag → X → Y₂` の DPI から `I(tag;Y₂) ≤ I(tag;X) = 0`
は確かに出る。**しかし S6 は要求しない**: 必要なのは `p.2 ≤ bcInfo₂(U')` の一方向だけで、混合法が
吐く `I(U';Y₂) = I(tag;Y₂) + λ·I_枝1(U';Y₂) + (1-λ)·I_枝0(U';Y₂)` の第 1 項と第 3 項をどちらも
捨てて `≥ λ·b` にすればよい (`le_add_left le_self_add`、probe で 1 行) ⟹ **`tag ⊥ Y₂` の証明を
書かない**。一方 **スロット 1 は等式が要る**が、条件付け変数 `U'` が tag を復元するので
`condMutualInfo_compProd_snd_eq_lintegral` が**等式のまま**通る (§Q2-1)。

### Q1-D 場合分けと退化 (**構造の違う 3 軸**、値はすべて逐語確認済)

| 軸 | 設定 | 予測 | 実際 (機械確認) |
|---|---|---|---|
| **λ = 1** (`R₂ = b`) | `boolLaw 1` | `= dirac true` ⟹ 時分割法 = 枝 1 そのもの。`bcInfo₂ = b`, `bcInfo₁ = a` | `simp [boolLaw]` で `boolLaw 1 = Measure.dirac true` ✅。全支持は破れる (S7 の担当) |
| **λ = 0** (`R₂ = 0`) | `boolLaw 0` | `= dirac false` ⟹ 補助は定数。`bcInfo₂ = 0`, `bcInfo₁ = I(X;Y₁)` | `boolLaw 0 = Measure.dirac false` ✅。`R₁ ≤ a+b ≤ I(X;Y₁)` と整合 |
| **b = 0** (`β₂` が 1 点 / `U` が 1 点) | `λ := R₂ / b = 0/0` | Lean の `0/0 = 0` ⟹ **λ = 0 の枝と一致し、正しい** | `R₂ ≤ 0` の枝に吸収され division が出ない (§Q4 P5) ✅ |

⟹ **場合分けは `R₂ ≤ 0` と `0 < R₂` の 2 本**。後者では `0 < R₂ ≤ b` から `b > 0` が出るので
`λ = R₂/b ∈ (0,1]` が定義でき、`div_le_one` / `div_mul_cancel₀` がそのまま効く。

### Q1-E 混合の 2 等式 (probe で全証明が compile、`λ : ℝ≥0∞`)

```
uvInfo₂ (時分割法) ≥ λ · uvInfo₂ ν                                                    -- 22 行
condMutualInfo (時分割法) X Y₁ U' = λ · condMutualInfo ν X Y₁ U + (1-λ) · mutualInfo ν X Y₁  -- 28 行
```

`≥` と `=` の非対称は意図的 (§Q1-C)。

## Q2 資産表 (**凡例**: ✅ 既存 / 🔧 既存部品の合成、行数は probe 実測 / ❌ 不在)

### 1. 混合法 3 本 — ✅ **2 本が当たる。当たり方が S5 と違う**

| 宣言 | 逐語署名 | file:line | S6 での役割 |
|---|---|---|---|
| `mutualInfo_compProd_eq_add_lintegral` | `lemma mutualInfo_compProd_eq_add_lintegral [Countable T] [MeasurableSingletonClass T] (μ : Measure T) [IsProbabilityMeasure μ] (κ : Kernel T S) [IsMarkovKernel κ] {f : S → A} {g : S → B} (hf : Measurable f) (hg : Measurable g) {tag : A → T} (htag : Measurable tag) (hrec : ∀ᵐ p ∂(μ ⊗ₘ κ), tag (f p.2) = p.1) : mutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) = mutualInfo (μ ⊗ₘ κ) Prod.fst (fun p ↦ g p.2) + ∫⁻ t, mutualInfo (κ t) f g ∂μ`。変数束は `{T S A B : Type*} [MeasurableSpace T] [MeasurableSpace S] [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]` | `Shannon/CondMutualInfoMixture.lean:142` | **スロット 2**。`A := Bool × U` / `B := β₂` / `tag := Prod.fst` |
| `condMutualInfo_compProd_snd_eq_lintegral` | `lemma condMutualInfo_compProd_snd_eq_lintegral [Countable T] [MeasurableSingletonClass T] {C : Type*} [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C] (μ : Measure T) [IsProbabilityMeasure μ] (κ : Kernel T S) [IsMarkovKernel κ] {f : S → A} {g : S → B} {h : S → C} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) {tag : C → T} (htag : Measurable tag) (hrec : ∀ᵐ p ∂(μ ⊗ₘ κ), tag (h p.2) = p.1) (htagfin : mutualInfo (μ ⊗ₘ κ) Prod.fst (fun p ↦ g p.2) ≠ ∞) (hmargfin : (∫⁻ t, mutualInfo (κ t) h g ∂μ) ≠ ∞) : condMutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) (fun p ↦ h p.2) = ∫⁻ t, condMutualInfo (κ t) f g h ∂μ` | 同 `:164` | **スロット 1**。`A := α` / `B := β₁` / `C := Bool × U` |

⟹ plan の「効くのはこの 3 本」は **2/3 が正しい**。3 本目
`condMutualInfo_compProd_fst_eq_lintegral` (`:102`、tag を**条件**に置く形) は S6 に出ないので不要。

### 2. `bcInfo₁` / `bcInfo₂` / `bcInfoJoint` の定義本体 — ✅ **`ℝ` 値のエントロピー差。`.toReal` は無い**

`μ := bcJointDistribution pU K W` として (すべて `(pU : Measure U) (K : Kernel U α) (W : BCChannel
α β₁ β₂) : ℝ`、型クラス前提は `variable` 束由来で宣言行には出ない):

```lean
bcInfo₂    = entropy μ Prod.fst + entropy μ (fun q ↦ q.2.2.2)
               - entropy μ (fun q ↦ (q.1, q.2.2.2))                       -- Setup.lean:100
bcInfo₁    = entropy μ (fun q ↦ (q.1, q.2.1)) + entropy μ (fun q ↦ (q.1, q.2.2.1))
               - entropy μ (fun q ↦ (q.1, q.2.1, q.2.2.1)) - entropy μ Prod.fst  -- Setup.lean:111
bcInfoJoint = entropy μ (fun q ↦ (q.1, q.2.1)) + entropy μ (fun q ↦ q.2.2.1)
               - entropy μ (fun q ↦ (q.1, q.2.1, q.2.2.1))          -- ErrorAnalysis.lean:929
```

`mutualInfo` 形ではないので、S3 の 3 本 (`Shannon/BroadcastChannel/Superposition/Region.lean`) が
`.toReal` 形へ橋渡しする — S6 はこの 3 本を**全部使う**。型クラス前提は 3 本とも逐語
`[Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]` +
`[IsProbabilityMeasure pU]` / `[IsMarkovKernel K]` / `[IsMarkovKernel W]`。

### 3. 「索引を補助に埋めて tag で復元する」先例 — **plan の判定は宣言については正しく、証明骨格については誤り**

| 宣言 | 逐語署名 | file:line |
|---|---|---|
| `bcUVTimeShare` | `noncomputable def bcUVTimeShare (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) : Measure (…) := ((bcUVLetterIndexLaw n) ⊗ₘ bcUVLetterKernel c W).map Prod.snd` | `OuterBoundUV/Assembly.lean:258` |
| `bcUVLetterKernel` | `noncomputable def bcUVLetterKernel (c) (W) : Kernel (Fin n) (…) := Kernel.ofFunOfCountable (bcUVJointDistribution c W)` | 同 `:228` |
| `bcUVLetterKernel_ae_tag` | `lemma bcUVLetterKernel_ae_tag (c) (W) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] : ∀ᵐ p ∂((bcUVLetterIndexLaw n) ⊗ₘ bcUVLetterKernel c W), p.2.1.1 = p.1 ∧ p.2.2.1.1 = p.1` | 同 `:296` |
| `bcUVTimeShare_uvInfo₂_ge` | `lemma bcUVTimeShare_uvInfo₂_ge (c) (W) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] : (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, uvInfo₂ (bcUVJointDistribution c W i) ≤ uvInfo₂ (bcUVTimeShare c W)` | 同 `:333` |
| `bcUVTimeShare_eq_sum` | `lemma bcUVTimeShare_eq_sum (c) (W) […] : bcUVTimeShare c W = ∑ i : Fin n, (n : ℝ≥0∞)⁻¹ • bcUVJointDistribution c W i` | 同 `:272` |

**plan の「写経できない」は宣言については正しい** (`BroadcastCode` の `Fin n` 一様混合に張り付き
重み `λ` が取れない)。**しかし証明骨格は逐語で効く**: `(重みの法) ⊗ₘ (枝 kernel) |>.map Prod.snd`
→ `mutualInfo_map_comp` → `mutualInfo_compProd_eq_add_lintegral` → `lintegral_<重みの法>` →
`le_add_self` の 5 手が、`bcUVLetterIndexLaw`→`boolLaw` / `bcUVLetterKernel`→2 枝 kernel の
差し替えだけで通った。`bcUVTimeShare_eq_sum` の証明も `IsUVChannelLaw` 保存にそのまま流用できる。
⟹ **本 leg で最も時間を節約した資産**。

### 4. `Bool × U` 上の測度・カーネルを組む道具 — 🔧 **全部既存部品、自作は `boolLaw` の 4 行だけ**

| 用途 | 宣言 | 逐語署名 / 形 | file:line |
|---|---|---|---|
| 可算添字の kernel | `Kernel.ofFunOfCountable` | `def ofFunOfCountable [MeasurableSpace α] {_ : MeasurableSpace β} [Countable α] [MeasurableSingletonClass α] (f : α → Measure β) : Kernel α β` | `Mathlib/Probability/Kernel/Basic.lean:237` |
| 混合の a.e. 展開 | `MeasureTheory.Measure.ae_compProd_iff` | `lemma ae_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {p : α × β → Prop} (hp : MeasurableSet {x \| p x}) : (∀ᵐ x ∂(μ ⊗ₘ κ), p x) ↔ ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b)` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:123` |
| 混合の和形 | `Measure.snd_compProd` + `Measure.bind_apply` | `bcUVTimeShare_eq_sum` と同じ 4 手 | `Assembly.lean:272` が雛形 |
| 混合の `IsUVChannelLaw` | `IsUVChannelLaw.smul` / `.add` | `lemma IsUVChannelLaw.smul {W : BCChannel α β₁ β₂} [IsMarkovKernel W] {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) (a : ℝ≥0∞) : IsUVChannelLaw W (a • ν)` / `lemma IsUVChannelLaw.add … [SFinite ν₁] [SFinite ν₂] (h₁ …) (h₂ …) : IsUVChannelLaw W (ν₁ + ν₂)` | `OuterBoundUV/Region.lean:153` / `:160` |
| 枝の構成 | `IsUVChannelLaw.map_auxiliaries` | `lemma IsUVChannelLaw.map_auxiliaries {U' V' : Type*} [MeasurableSpace U'] [MeasurableSpace V'] {W : BCChannel α β₁ β₂} [IsMarkovKernel W] {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) {f : U → U'} {g : V → V'} (hf : Measurable f) (hg : Measurable g) : IsUVChannelLaw W (ν.map fun q ↦ (f q.1, g q.2.1, q.2.2))` | 同 `:183` |
| 再ラベルの器 | `uvRelabel` / `measurable_uvRelabel` | `def uvRelabel (e₁ : U → U') (e₂ : V → V') : U × V × α × β₁ × β₂ → U' × V' × α × β₁ × β₂ := fun q ↦ (e₁ q.1, e₂ q.2.1, q.2.2)` | `Assembly.lean:134` / `:138` |
| 2 点測度 | ❌ 不在 (loogle 0 件) | 自作 `boolLaw lam := (lam ⊓ 1) • Measure.dirac true + (1 - lam) • Measure.dirac false` (**4 行**) + `lintegral_boolLaw` (**3 行**) | — |

**プロジェクト内の先例**: `RateDistortion/Convexity.lean:155` / `:234` が
`(dirac true).prod μ + (dirac false).prod σ` の Bool タグ混合を使う (器は `.prod`、S6 は `⊗ₘ`)。

⚠ **`⊓ 1` は必須の設計判断**: 素の `lam • dirac true + (1-lam) • dirac false` は `lam > 1` で全質量
が 1 を超え `IsProbabilityMeasure` が **instance にできない** (`hlam` は instance 引数になれない)。
`condMutualInfo` は `[IsFiniteMeasure μ]` を**署名で要求する**ので、instance にできないと
**定理の文が書けない** (probe で発火)。clamp すれば `hlam` は値が要る補題だけが持つ。

### 5. less noisy から `I(X;Y₁) ≥ a + b` — 🔧 **地雷は実在したが 12 行で埋まる (probe 全証明通過)**

| 部品 | 逐語署名 | file:line |
|---|---|---|
| 出発点 | `theorem bc_lessNoisy_infoJoint_ge {U : Type u} [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U] (pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hln : IsBCLessNoisy W) : bcInfo₁ pU K W + bcInfo₂ pU K W ≤ bcInfoJoint pU K W` (`@[entry_point]`) | `Classes.lean:95` |
| 差 (**地雷本体**) | `bcInfoJoint = I((U,X);Y₁)` であって `I(X;Y₁)` ではない | — |
| 埋め方 1 | `theorem mutualInfo_chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) (hXs hYo hZc) : mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc` を `Zc := X` / `Xs := U` で | `CondMutualInfo.lean:214` |
| 埋め方 2 | `theorem condMutualInfo_eq_zero_of_markov (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (hXs) (_hZc) (hYo) (hmarkov : IsMarkovChain μ Xs Zc Yo) : condMutualInfo μ Xs Yo Zc = 0` (`@[entry_point]`) | `CondMutualInfo.lean:339` |
| 供給元 | `lemma IsUVChannelLaw.isMarkovChain_U_X_Y₁ {W : BCChannel α β₁ β₂} [IsMarkovKernel W] {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) : IsMarkovChain ν (fun q ↦ q.1) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)` | `Region.lean:305` (S4 の成果) |
| 対の入替 | `mutualInfo_eq_of_leftInverse` を `f = g = Prod.swap` で | `CondMutualInfoMixture.lean:40` |

⟹ **`bcInfoJoint (uvCloudLaw ν) (uvSatelliteKernel ν) W = (mutualInfo ν X Y₁).toReal`** が
**12 行**で通った (§Q4 P3)。plan の「一番の地雷候補」は正しい見立てだが **部品は全部在り、
S4 の Markov 鎖がそのまま鍵**だった (判断ログ 16-(c) の 4 度目)。**橋そのもの**も既存 2 本の合成:

| 部品 | 逐語署名 | file:line |
|---|---|---|
| 四つ組法 | `lemma IsUVChannelLaw.map_auxiliary_input_output {W : BCChannel α β₁ β₂} [IsMarkovKernel W] {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) : ν.map (fun q ↦ (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) = ((ν.map fun q ↦ (q.1, q.2.2.1)) ⊗ₘ (W.comap (Prod.snd : U × α → α) measurable_snd)).map MeasurableEquiv.prodAssoc` | `Region.lean:251` |
| 分解 | `lemma compProd_map_condDistrib (hY : AEMeasurable Y μ) : (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a)`。変数束は `{α β Ω F : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [NormedAddCommGroup F] {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ] {X : α → β} {Y : α → Ω}` + `{mβ : MeasurableSpace β}` | `Mathlib/Probability/Kernel/CondDistrib.lean:82` |
| Markov 性 | `instance [MeasurableSpace β] : IsMarkovKernel (condDistrib Y X μ)` | 同 `:68` |

⚠ **`condDistrib` は定義そのものが `[IsFiniteMeasure μ]` を要求する** (`:64`) ⟹ 衛星カーネルを
`def uvSatelliteKernel (ν) [IsFiniteMeasure ν] : Kernel U α` と**instance 引数付きで宣言する**
(probe で発火)。`IsFiniteMeasure` は `Prop` クラスなので diamond は起きない。

### 6. 全支持要求 — **S6 は作らない。S7 の担当**

`bcSuperpositionRegionNoSumRate` (`Shannon/BroadcastChannel/Superposition/Region.lean`) の union 添字は
`∀ x, 0 < pU.real {x}` と `∀ x a, 0 < (K x).real {a}` を要求する。時分割法は**枝 0 の補助を
定数に潰す**設計なので `pU'` は構造的に全支持を破る (潰さなくても `λ = 1` で破れる)
⟹ **S6 の署名に全支持を混ぜない**。**責任分界の提案 (これが一番安い)**:

- **S6** は全支持を主張しない存在命題まで出す
  (§Q3 の `exists_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw`)。
- **S7 は `(pU, K)` ではなく `ν'` (時分割済の五つ組法) を摂動する**。理由は 3 つ:
  (a) `IsUVChannelLaw` が `.smul` / `.add` で閉じるので摂動後も channel law のまま、(b) S6-a の橋を
  そのまま再利用でき `(pU, K)` を作り直さずに済む、(c) 連続性の議論が `ℝ≥0∞` の `uvInfo₂` /
  `condMutualInfo` の上で閉じ `bcInfo*` のエントロピー差 4 本を個別に扱わずに済む。全支持の確認には
  `condDistrib_apply_of_ne_zero` (`Mathlib/…/CondDistrib.lean:75`、`[MeasurableSingletonClass β]`)。
- **摂動は時分割の後**。前に置いても枝 0 の定数補助で全支持が壊れるので 1 度で済まない。

## 前提が事故りやすい箇所 (key-preconditions box)

- **`condMutualInfo` は `[IsFiniteMeasure μ]` を署名で要求する** ⟹ 重み `lam` を `⊓ 1` で clamp し
  `IsProbabilityMeasure` を **instance にする**。しないと**定理の文が書けない**。
- **`condMutualInfo_compProd_snd_eq_lintegral` は有限性を 2 本要求** (`htagfin` / `hmargfin`)。
  両方 S5 の `mutualInfo_ne_top_of_fintype_right` (`Quantization.lean:59`) で出る。
  **`mutualInfo_ne_top` は両側 `[Fintype]` を要求するので当たらない**。
- **`Region.lean` の `section Transport` (Markov 鎖 3 本) は 5 型すべてに
  `[StandardBorelSpace _] [Nonempty _]` + `[IsProbabilityMeasure ν]` を要求**。S6 は `U_X_Y₁` と
  `V_X_Y₁` の両方を使うので `U` にも `V` にも要る。
- **`bc_lessNoisy_infoJoint_ge` の `U` は `α` と同じ universe** (`#check` 実測)。
  `Bool × ULift.{u} (Fin (m+1))` は `Type (max 0 u) = Type u` で通る。**universe を浮かせない**。
- **`Measure.ae_compProd_iff` / `ae_map_iff` の `{p}` は暗黙** ⟹ `(p := fun p : … ↦ …)` と
  型を明示する (S5 在庫の同型トラップの 2 度目)。**`Measurable` 項も syntactic に一致させる** —
  `measurable_const.prodMk measurable_id` は `fun a ↦ (?c, id a)` になり目標と一致しない。
- **`condMutualInfo_map_comp` は motive not type correct になる** ⟹ **`condMutualInfo_map_comp'`
  (`CodeToAmbient.lean:527`、`ρ` と `hρ : ρ = μ.map T` を取る形)**。3 箇所すべてで発火。
- **`rw [uvInfo₂]` は片側しか展開しない** ⟹ `simp only [uvInfo₂, uvTimeShareLaw]`。
  **`rw [← inf_of_le_left hlam]` を先頭に置くと `uvTimeShareLaw ν u₀ lam` の `lam` まで書き換わる**
  ⟹ `lintegral_boolLaw` の**後**に順方向で当てる。

## Q3 署名案と置き場所

### 置き場所: **`InformationTheory/Shannon/BroadcastChannel/SuperpositionTimeShare.lean` (トップ直下)**

import は `OuterBoundUV.Quantization` と `SuperpositionRegion` の 2 本
(**probe で cycle 無しを機械確認**、両家系の 15 宣言が同時に見えた)。

- **`OuterBoundUV/` の下には置けない** — 達成側 (`SuperpositionRegion` ⊃ `Classes` ⊃
  `Achievability/`) を import するので `OuterBoundUV/` から達成側への依存が生まれ、
  `module-structure.md` §5 の双方向依存になる。`MartonUnion.lean` をトップ直下にした判断
  (plan §Phase 2) と同じ理由・同じ解。`Shannon/BroadcastChannel/Superposition/Region.lean` に足すのも不可 (上流)。
- S7 / S8 が乗ると 600 行級になるので、S8 着手時に
  `BroadcastChannel/SuperpositionConverse/` への昇格を判定する。

### `λ` の型: **`ℝ≥0∞`**、`.toReal` は S6-e の 1 箇所だけ

スロットは `ℝ≥0∞`、`bcInfo*` は `ℝ`。S6-a〜d を `ℝ≥0∞` で閉じ、**S6-e が `ENNReal.toReal_mul` /
`toReal_add` で 1 回だけ降ろす**。`λ := ENNReal.ofReal (R₂ / b)`。

### 署名案 (S7/S8 が消費する形。S6-a の 2 def + 1 定理は §skeleton に逐語)

```lean
theorem bcInfo₂_uvCloudLaw    … : bcInfo₂ … = (uvInfo₂ ν).toReal
theorem bcInfo₁_uvCloudLaw    … : bcInfo₁ … = (condMutualInfo ν X Y₁ U).toReal
theorem bcInfoJoint_uvCloudLaw … : bcInfoJoint … = (mutualInfo ν X Y₁).toReal   -- 地雷を潰す 1 本

-- S6-b/c  時分割 (`uvTimeShareLaw ν u₀ lam := ((boolLaw lam) ⊗ₘ 2 枝 kernel).map Prod.snd`)
noncomputable def boolLaw (lam : ℝ≥0∞) : Measure Bool
noncomputable def uvTimeShareLaw (ν : Measure (U × V × α × β₁ × β₂)) (u₀ : U) (lam : ℝ≥0∞) :
    Measure ((Bool × U) × V × α × β₁ × β₂)

theorem uvTimeShareLaw_isUVChannelLaw (W) [IsMarkovKernel W] {ν} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) (u₀ : U) (lam : ℝ≥0∞) : IsUVChannelLaw W (uvTimeShareLaw ν u₀ lam)
theorem uvInfo₂_uvTimeShareLaw_ge … (hlam : lam ≤ 1) :
    lam * uvInfo₂ ν ≤ uvInfo₂ (uvTimeShareLaw ν u₀ lam)
theorem condMutualInfo_uvTimeShareLaw … (hlam : lam ≤ 1) :
    condMutualInfo (uvTimeShareLaw ν u₀ lam) X Y₁ U'
      = lam * condMutualInfo ν X Y₁ U + (1 - lam) * mutualInfo ν X Y₁

-- S6-d  内界の補助アルファベットへの着地 / S6-e  まとめ (S7 が全支持、S8 が closure と m → ∞)
noncomputable def boolProdAuxEquiv (m : ℕ) :
    Bool × ULift.{u} (Fin (m + 1)) ≃ Marton.bcAuxAlphabet.{u} (2 * m + 1)

theorem exists_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hln : IsBCLessNoisy W) {m : ℕ}
    {ν : Measure (Marton.bcAuxAlphabet.{u} m × V × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) {R₁ R₂ : ℝ}
    (h₁ : R₁ ≤ (uvInfo₁ ν).toReal) (h₂ : R₂ ≤ (uvInfo₂ ν).toReal)
    (hsum : R₁ + R₂ ≤ (uvInfoSum₂ ν).toReal) :
    ∃ (k : ℕ) (pU : Measure (Marton.bcAuxAlphabet.{u} k)) (_ : IsProbabilityMeasure pU)
      (K : Kernel (Marton.bcAuxAlphabet.{u} k) α) (_ : IsMarkovKernel K),
      R₁ ≤ bcInfo₁ pU K W ∧ R₂ ≤ bcInfo₂ pU K W
```

⚠ **`h₁` (= `bound₁`) を署名から落とさないこと** (§Q1-B)。
⚠ **全支持を署名に入れないこと** — S7 の担当 (§Q2-6)。

## Q4 probe (機械確認、すべて `lake env lean` がエラー 0)

scratchpad =
`/private/tmp/claude-502/-Users-haruka-dev-lean-projects/abc83ceb-84f8-4f9f-b0e9-c9408d308cfe/scratchpad`
(`InformationTheory/` は 1 行も触っていない)。

| probe | 内容 | 結果 | 実測行数 |
|---|---|---|---|
| **P0** `ProbeS6Setup` | 2 家系同時 import の cycle 無し + `Bool × ULift (Fin (m+1))` の 5 instance + `Marton.bcAuxAlphabet m = ULift (Fin (m+1))` が `rfl` | ✅ | — |
| **P1** `ProbeS6Mix` | `boolLaw` / 2 枝 / `uvBranchKernel` / `uvTimeShareLaw` + `IsProbabilityMeasure` / `IsMarkovKernel` / **`uvTimeShareLaw_eq` (和形)** / **`IsUVChannelLaw` 保存** | ✅ 全部 | **75** |
| **P2a** `ProbeS6Const` | `condMutualInfo μ X Y Z = mutualInfo μ X Y` (`Z` が a.e. 定数) **完全証明** | ✅ | **15** |
| **P2b** `ProbeS6Slots` | tag 復元 `∀ᵐ p, (p.2.1).1 = p.1` / **スロット 2 の `≥`** / **スロット 1 の等式** (枝 2 本の同定込み) **完全証明** | ✅ | **185** |
| **P3** `ProbeS6Bridge` | `bcJointDistribution_uvCloudLaw` + 3 スロット同定 (**地雷 `bcInfoJoint = I(X;Y₁)` 込み**) **完全証明** | ✅ | **70** |
| **P4/P5** `ProbeS6Assembly` | `boolProdAuxEquiv` + 再ラベル不変 2 本 + **DPI `I(V;Y₁) ≤ I(X;Y₁)`** + **場合分け 2 本の算術** + **`bound₁` が load-bearing であることの反例** + `boolLaw` の境界値 3 本 | ✅ | **40** |
| 計 | | | **~295** |

**落ちた probe (逐語エラー、実装時に再発する)** — 順に (1) `measurable_const.prodMk
measurable_id` を直書きせず名前付き補題に切り出す / (2) `condMutualInfo_map_comp` ではなく
`condMutualInfo_map_comp'` (`CodeToAmbient.lean:527`) / (3) `boolLaw` の重みを `⊓ 1` で clamp する
/ (4) `condDistrib` は**定義が** `[IsFiniteMeasure μ]` を要求する ⟹ def に instance 引数を足す:

```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  @Filter.Eventually … (ae (Measure.map (uvRelabel (fun a => (?m.397, id a)) id) ?m.415))
in the target expression
  @Filter.Eventually … (ae (Measure.map (uvRelabel (fun u => (true, u)) id) ν))
error: Tactic `rewrite` failed: motive is not type correct
error(lean.synthInstanceFailed): failed to synthesize IsFiniteMeasure (uvTimeShareLaw ν u₀ lam)
error(lean.synthInstanceFailed): failed to synthesize IsFiniteMeasure ν  (uvSatelliteKernel の def)
```

## Q5 壁 / 撤退ライン / 行数

### Mathlib の壁 — **0 件** (6 leg 連続) / プロジェクト側の壁も **0 件**

| クエリ | 結果 | 影響 |
|---|---|---|
| loogle `PMF.bernoulli` | `Found 6 declarations` (すべて `PMF` 側) | `Measure` 版の 2 点分布は無い。`PMF.toMeasure` 経由より `dirac` の和が短い |
| loogle `MeasureTheory.Measure.dirac _ + MeasureTheory.Measure.dirac _` | `Found 10 … Of these, 0 match your pattern(s)` | 2 点測度の補題は不在 ⟹ **自作 4 行** (壁ではない) |
| loogle `ProbabilityTheory.condDistrib, MeasureTheory.Measure.compProd` | `Found 4` (`compProd_map_condDistrib` ほか) | 橋の分解は Mathlib 既存 |
| `rg -B4 'condMutualInfo .* = mutualInfo'` (結論形、in-project) | `lemma\|theorem` 行 0 件 | 「定数で条件付け」は不在 ⟹ **自作 15 行** (probe 済) |
| `rg 'dirac true\|dirac false\|bernoulli'` (in-project) | `RateDistortion/Convexity.lean:155` `:234` | Bool タグ混合の先例あり。器が違うので直接再利用は不可 |

### L-BCO9 との距離 — **不発動の見込み**

発動条件は「S6 が閉じない」。**核の 2 等式・地雷 (`bcInfoJoint = I(X;Y₁)`)・場合分けの算術・
再ラベルの equiv がすべて probe で compile 通過**しており閉塞要因は 0 件。残るのは `.toReal` の
往復と存在命題への包装だけ ⟹ **S6 は sorry 無しで閉じられる見込み**。
⚠ **ただし §Q1-B の `bound₁` 補正を入れ忘れると S6-e は閉じない** (命題が偽になる)。実装時に
`h₁ : R₁ ≤ (uvInfo₁ ν).toReal` が署名に居るかを最初に確認すること。
**本在庫は S7 の判定材料を 1 件も持たない** (全支持への摂動の連続性)。

### 行数見積り (step 内分割、**実測ベース**)

| step | 内容 | 見積り | 根拠 |
|---|---|---|---|
| **S6-a** | 橋 `uvCloudLaw` / `uvSatelliteKernel` + `bcJointDistribution_uvCloudLaw` + スロット同定 3 本 (地雷込み) | ~90 | **probe 実測 70 行** + docstring |
| **S6-b** | `boolLaw` / 2 枝 / `uvBranchKernel` / `uvTimeShareLaw` + instance 4 本 + 和形 + `IsUVChannelLaw` + tag 復元 | ~120 | **probe 実測 100 行** |
| **S6-c** | 定数条件付け補題 + 枝 2 本の同定 + スロット 1 の等式 + スロット 2 の `≥` | ~90 | **probe 実測 75 行** |
| **S6-d** | `boolProdAuxEquiv` + 時分割法の再ラベルとスロット輸送 | ~50 | probe 実測 20 行 (equiv) + 既存 `uvInfo₂_map_uvRelabel` 一族への配線 ~30 |
| **S6-e** | 存在命題 (場合分け 2 本 / `λ := ofReal (R₂/b)` / `.toReal` の往復 / less noisy の適用 / DPI) | ~90 | 算術は probe 実測 20 行。残りは未実測の配線 |
| 計 | | **~440** | うち **~295 行が probe 実測済** |

親 plan の `~180 行` は **約 2.4 倍への上方修正**、帯は **380–480 行**。S3 (90→41) / S4 (140→74)
のような下振れは**期待できない** — 下振れの原因は「自作予定が既存だった」ことで、S6 は既存資産を
全部当て込んだ後の数字だから (S5 が 280→289 で的中したのと同じ構造)。**最初に切るべきは S6-a**:
S6-e / S7 / S8 のすべてが前提にし、しかも地雷がここに居る ⟹ gateway-atom の価値が最も高い。
**S6-e を S8 に寄せる分割も可** (S6 = a–d で ~350 行、S8 が +90 行) だが、**設計の正しさが宿るのは
e** なので S6 に置いて L-BCO9 の判定を S6 内で完結させるほうを推す。

## 親 plan で書き換えが要る箇所 (編集は plan の担当)

1. **§Phase 5 S6 の行数 `(在庫見積 ~180 行)` → `~440 行 (probe 実測 295 行 + 配線)`**
   (step 内分割 S6-a〜e は §Q5)。
2. **§S6 の証明戦略に `bound₁` が抜けている** — 擬似 Lean は `b`/`a` しか名前を付けておらず
   `R₂ < 0` の枝を被覆できない。`R₁ ≤ I(V;Y₁) ≤ I(X;Y₁)` (DPI、`isMarkovChain_V_X_Y₁`) を
   1 行足すこと。**落とすと逆包含は偽** (§Q1-B に反例)。
3. **§S6 の材料「効くのは混合法 3 本」→ 2 本** (`CondMutualInfoMixture.lean:142` `:164`)。
4. **§S6 の材料「`bcUVTimeShare` の写経ではない」に補足** — 宣言は再利用不可で正しいが、
   **証明骨格 (`(重みの法) ⊗ₘ (枝 kernel) |>.map Prod.snd` → `mutualInfo_map_comp` → 混合法 →
   重みの lintegral → `le_add_self`) は逐語で効いた** = 本 leg で最も効いた資産。判断ログ 11-(f)
   の「再発が予告されている」は**半分だけ発火**した、と記録するのが正確。
5. **§S6 の材料「`IsUVChannelLaw.condMutualInfo_le_map_cond` が `Bool × U_m` でも当たる見込み」
   は外れ** — S6 の補助は `f : U → U'` の粗視化ではなく `U → Bool × U` の**細密化**で、当てても
   `condMutualInfo ν' X Y₁ U' ≤ condMutualInfo ν' X Y₁ (U 成分)` = **欲しい向きと逆の不等式**しか
   出ない (S6 が要るのは LHS の下界)。使うのは `IsUVChannelLaw.map_auxiliaries` (`Region.lean:183`)。
6. **§撤退ライン L-BCO9**: S6 側も**不発動の見込み**が立った (核が全部 probe 通過)。
   残る判定は S7 (全支持への摂動の連続性)。判定粒度を S7 に降ろすかは plan の判断。
7. **§後続作業 F-16 の判定** — S6 が `Quantization.lean` から消費するのは
   `mutualInfo_ne_top_of_fintype_right` (`:59`) / `uvInfo₂_ne_top` (`:104`) /
   `uvInfoSum₂_ne_top` (`:108`) / `mutualInfo_eq_zero_of_ae_const` (`:81`) で、
   **S5 の 3 本 (スラック不等式 2 本 + `tendsto`) を消費するのは S8** ⟹ orphan 状態は
   **S6 では解消せず S8 で解消する**。`@[entry_point]` の判定は S8 まで持ち越すのが正しい
   (F-15 の汎用 3 本には S6-c が消費者として付くが、BC 外からの消費者の見込みは変わらない)。
8. **§在庫 に新規行 1 本**: `SuperpositionTimeShare.lean` (トップ直下、import 2 本)。
   `OuterBoundUV/` の下に置けない理由は `MartonUnion.lean` と同じ (双方向依存)。
9. **§後続作業に 1 件追加候補** — `condMutualInfo_map_comp` (`CodeToAmbient.lean:465`) は
   motive not type correct で**実質使えない場面が多い** (S6 で 3 箇所すべて `'` 版に退避)。
   docstring に「条件付き版は `'` を使う」旨の 1 行を足すか、無印を private にする判断。

## 着手のための skeleton

```lean
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Quantization
import InformationTheory.Shannon.BroadcastChannel.SuperpositionRegion

/-!
# Broadcast channel — absorbing a time-sharing variable into the superposition cloud
(`## Main definitions` / `## Main statements` は §Q3 の署名をそのまま並べる)
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal Topology

universe u

-- α β₁ β₂ U は [Fintype] [DecidableEq] [Nonempty] [MeasurableSpace] [MeasurableSingletonClass]
-- [StandardBorelSpace]、V は後ろ 3 つ。α と U は同じ universe u (`bc_lessNoisy_infoJoint_ge`)。
variable {α : Type u} {β₁ β₂ : Type*} {U : Type u} {V : Type*}

/-- The cloud law read off a five-tuple channel law. -/
noncomputable def uvCloudLaw (ν : Measure (U × V × α × β₁ × β₂)) : Measure U :=
  ν.map (fun q ↦ q.1)

/-- The satellite kernel read off a five-tuple channel law. -/
noncomputable def uvSatelliteKernel (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] :
    Kernel U α :=
  condDistrib (fun q ↦ q.2.2.1) (fun q ↦ q.1) ν

/-- The Bernoulli tag law, clamped so that it is a probability measure for every weight. -/
noncomputable def boolLaw (lam : ℝ≥0∞) : Measure Bool :=
  (lam ⊓ 1) • Measure.dirac true + (1 - lam) • Measure.dirac false

theorem bcJointDistribution_uvCloudLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) :
    bcJointDistribution (uvCloudLaw ν) (uvSatelliteKernel ν) W
      = ν.map (fun q ↦ (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) := by
  rw [h.map_auxiliary_input_output, bcJointDistribution, uvCloudLaw, uvSatelliteKernel,
    compProd_map_condDistrib (X := fun q : U × V × α × β₁ × β₂ ↦ q.1) (by fun_prop)]

end InformationTheory.Shannon.BroadcastChannel
```

⚠ skeleton に `sorry` は無い — 上の定理は probe で本体まで compile 通過している。
実装時に `@residual` を付けないこと。

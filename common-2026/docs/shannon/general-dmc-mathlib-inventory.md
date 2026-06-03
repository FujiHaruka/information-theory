# I-2 General DMC capacity (limit form) — Mathlib / Project Inventory

> Pre-implementation inventory for the I-2 seed of `docs/textbook-roadmap.md`
> (Tier ∞ — Infrastructure). 出力規約は `docs/shannon/shannon-mathlib-inventory.md`
> と同形。

## 一行サマリ

**`Channel = Kernel α β` で memoryless 単一 letter 形は完備、`capacity` も
`sup over stdSimplex` 形で 0-sorry。一方、 `BlockwiseChannel` / `capacity_lim`
(`lim (1/n) max_{p^n} I(X^n;Y^n)`) は project / Mathlib 両方とも完全不在。
**`Kernel.pi` (`Π i, α i → Π i, β i`) も Mathlib 不在** が最大の発見。block-wise
extension は `Measure.pi (i ↦ p ⊗ₘ W) ↔ p^n ⊗ₘ W^n` の手作り経路で繋ぐしかない
(`IIDProductInput.lean` で既出の `Measure.pi (fun i => W (x i))` ad-hoc shape を
abstraction 層に昇格させる plumbing が中心)。 既存 0-sorry callsite (`capacity W`
13 箇所) は **書き換えない** 方針が前提されているため、新規 `capacity_lim` を並置
し `capacity_lim = capacity (memoryless)` の同値補題で接続する形が最低コスト。

撤退ラインは「`BlockwiseChannel` の自然な signature が `(n : ℕ) → Kernel (Fin n → α)
(Fin n → β)` でいいのか、それとも cylinder 整合性 axiom 付き structure にすべきか」
の判断で 2 分岐:
- 軽量経路 (関数形): refactor ~0、新 API ~300 行で `capacity_lim` 定義 +
  memoryless specialization が到達可能。撤退ライン非発動。
- structure 形 (整合性 axiom 付き): refactor ~0、新 API ~600-1000 行 (roadmap 上限)。
  整合性証明が `IIDProductInput.lean` 既存 lemma で discharge できる範囲なので
  撤退ライン非発動だが、後続 informationally stable 拡張の見通しが立ちやすい。

---

## 主定理の最終形 (roadmap I-2 抜粋 + 推定 signature)

I-2 が publish すべき定理候補 (project 側に新規追加、Mathlib に対応 API なし):

```lean
-- 関数形候補 (軽量)
noncomputable def BlockwiseChannel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
  : Type _ :=
  (n : ℕ) → Kernel (Fin n → α) (Fin n → β)

noncomputable def BlockwiseChannel.capacityN
    (W : BlockwiseChannel α β) (n : ℕ) [hn : Fact (0 < n)] : ℝ :=
  sSup ((fun p : Measure (Fin n → α) =>
    (mutualInfoOfChannelBlock p (W n)).toReal) '' { p | IsProbabilityMeasure p })

noncomputable def BlockwiseChannel.capacity_lim (W : BlockwiseChannel α β) : ℝ :=
  Filter.atTop.limUnder (fun n : ℕ => W.capacityN n / n)

theorem capacity_lim_eq_capacity_of_memoryless
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W] :
    (BlockwiseChannel.ofMemoryless W).capacity_lim
      = InformationTheory.Shannon.ChannelCoding.capacity W
```

ここで `BlockwiseChannel.ofMemoryless W n := Kernel.pi (fun _ : Fin n => W)` だが、
**`Kernel.pi` は Mathlib 不在**。代替として `IIDProductInput.lean` 既出の
`fun (x : Fin n → α) => Measure.pi (fun i => W (x i))` を `Kernel` に lift する自作補題が要る (1 件、20-40 行)。

memoryless 等式の証明 sketch (~7 行 pseudo-Lean):
```lean
-- capacity_lim W := lim_n (sup_{p^n} I(X^n;Y^n)) / n
-- = lim_n (n * capacity W) / n     -- mutualInfo_iid_eq_nsmul (既存)
-- = capacity W                       -- limit of constant sequence
```

ただし `sup_{p^n} I(X^n;Y^n) = n · capacity W` 上界は **non-trivial** で、
任意 `p^n` (i.i.d. に限らない一般 product input) からの bound 化が必要 (Cover-Thomas
Thm 7.7.3 / 7.7.5、Mathlib 不在)。

---

## API 在庫テーブル

### A. 既存 `InformationTheory/Shannon/` channel 抽象

| 概念 | API (project 内) | file:line | 状態 | I-2 での扱い |
|---|---|---|---|---|
| `Channel α β := Kernel α β` (abbrev) | `InformationTheory.Shannon.ChannelCoding.Channel` | `ChannelCoding.lean:49` | ✅ 既存 (abbrev) | `BlockwiseChannel` の構成要素として **再利用** |
| `jointDistribution (p : Measure α) (W : Channel α β) : Measure (α × β) := p ⊗ₘ W` | `ChannelCoding.lean:54` | `ChannelCoding.lean:54` | ✅ 既存 | n-letter `p^n ⊗ₘ W^n` 形への一般化が必要 |
| `outputDistribution (p : Measure α) (W : Channel α β) := (jointDistribution p W).snd` | `ChannelCoding.lean:71` | `ChannelCoding.lean:71` | ✅ 既存 | 同上 |
| `mutualInfoOfChannel (p : Measure α) (W : Channel α β) : ℝ≥0∞` | `ChannelCoding.lean:84` | `ChannelCoding.lean:84` | ✅ 既存 (`klDiv (p ⊗ₘ W) (p.prod (outputDistribution p W))`) | n-letter 形 `mutualInfoOfChannelBlock` が要る (~10 行 plumbing) |
| `Code (M n : ℕ) (α β : Type*)` (structure: encoder/decoder) | `ChannelCoding.lean:151` | `ChannelCoding.lean:151` | ✅ 既存 | そのまま再利用 (block-length パラメタ `n` 既に bundle) |
| `Code.errorProbAt (c : Code M n α β) (W : Channel α β) (m : Fin M) : ℝ≥0∞ := (Measure.pi (fun i => W (c.encoder m i))) (c.errorEvent m)` | `ChannelCoding.lean:204` | `ChannelCoding.lean:204` | ✅ 既存 (**ここに memoryless 仮定が暗黙に埋まっている**) | 一般 channel では `W_n (c.encoder m) (c.errorEvent m)` に書き換え必要 |
| `Code.averageErrorProb` | `ChannelCoding.lean:210` | `ChannelCoding.lean:210` | ✅ 既存 | 同上 |
| `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ` (3-entropy form) | `ChannelCoding.lean:129` | `ChannelCoding.lean:129` | ✅ 既存 | memoryless 限定、一般化は不要 |
| `jointDistribution.instIsProbabilityMeasure` | `ChannelCoding.lean:62` | `ChannelCoding.lean:62` | ✅ 既存 | 再利用 |

**Memoryless 仮定がどこに埋まっているか**:

- `Code.errorProbAt` の `Measure.pi (fun i => W (c.encoder m i))` は **memoryless DMC の出力分布** をハードコード (Channel W が i.i.d. に各座標へ独立適用)。これは block channel `W^n` を **明示的に構築せず** product measure として書く既存方針 (`ChannelCoding.lean:33-34` の設計判断コメント参照)。
- `capacity W` (`ChannelCodingShannonTheorem.lean:102`) 単一 letter `I(p;W)` を `stdSimplex ℝ α` 上で sup。block-wise でないため inherently memoryless。

### B. capacity 定義 + 周辺 (memoryless 単一 letter 形)

| 概念 | API | file:line | 状態 | I-2 での扱い |
|---|---|---|---|---|
| `noncomputable def capacity (W : Channel α β) : ℝ := sSup ((fun p : α → ℝ => (mutualInfoOfChannel (pmfToMeasure p) W).toReal) '' stdSimplex ℝ α)` | `ChannelCodingShannonTheorem.lean:102` | `ChannelCodingShannonTheorem.lean:102` | ✅ 既存 | **memoryless 単一 letter form**。`capacity_lim` の specialization 目標 |
| `pmfToMeasure (p : α → ℝ) : Measure α := ∑ a, ENNReal.ofReal (p a) • Measure.dirac a` | `ChannelCodingShannonTheorem.lean:54` | `ChannelCodingShannonTheorem.lean:54` | ✅ 既存 | 一般化形は `stdSimplex (Fin n → α)` 上の pmf。新規 `pmfToMeasure_block` が要る |
| `theorem capacity_image_nonempty (W : Channel α β) : (... '' stdSimplex ℝ α).Nonempty` | `ChannelCodingShannonTheorem.lean:109` | `ChannelCodingShannonTheorem.lean:109` | ✅ 既存 | block 形対応物が要る |
| `theorem capacity_bddAbove (W : Channel α β) [IsMarkovKernel W] : BddAbove (...)` | `ChannelCodingShannonTheorem.lean:115` | `ChannelCodingShannonTheorem.lean:115` | ✅ 既存 (上界 `log |α| + log |β|`) | block 形は `log |α^n| + log |β^n| = n(log|α| + log|β|)`、自明拡張 |
| `theorem capacity_nonneg (W : Channel α β) [IsMarkovKernel W] : 0 ≤ capacity W` | `ChannelCodingShannonTheorem.lean:139` | `ChannelCodingShannonTheorem.lean:139` | ✅ 既存 | `capacity_lim_nonneg` は新規必要 |
| `theorem capacity_lt_implies_exists_pmf (W : Channel α β) [IsMarkovKernel W] {R : ℝ} (hR : R < capacity W) : ∃ p ∈ stdSimplex ℝ α, R < (mutualInfoOfChannel (pmfToMeasure p) W).toReal` | `ChannelCodingShannonTheorem.lean:329` | `ChannelCodingShannonTheorem.lean:329` | ✅ 既存 | shannon theorem 主定理の主軸。`capacity_lim` 版要 |
| `theorem continuous_mutualInfoOfChannel_left (W : Channel α β) [IsMarkovKernel W] : ContinuousOn (fun p => (mutualInfoOfChannel (pmfToMeasure p) W).toReal) (stdSimplex ℝ α)` | `ChannelCodingShannonTheorem.lean:281` | `ChannelCodingShannonTheorem.lean:281` | ✅ 既存 | block 形は新規必要 (任意 `n` で uniform にできるかは別問題) |
| `theorem exists_capacity_achiever (W : Channel α β) [IsMarkovKernel W] : ∃ p ∈ stdSimplex ℝ α, IsMaxOn ... p` | `ChannelCodingShannonTheorem.lean:317` | `ChannelCodingShannonTheorem.lean:317` | ✅ 既存 | block 形未定義 (`stdSimplex (α^n)` のコンパクト性 + 連続性) |

**`capacity W` callsite (`rg "capacity W"` で 13 件確認、すべて memoryless 単一 letter 依存)**:
- `ChannelCodingShannonTheorem.lean:20, 1014` (`shannon_noisy_channel_coding_theorem`, 主定理)
- `ChannelCodingShannonTheorem.lean:331` (`capacity_lt_implies_exists_pmf`)
- `ChannelCodingShannonTheoremGeneral.lean:17, 307` (`smooth` chain)
- `ChannelCodingShannonTheoremFull.lean:54` (hypothesis-form D-1'')
- `ChannelCodingShannonTheoremFullDischarge.lean:55, 111, 978, 1590` (D-1'' full discharge)

**前提条件と書き換えコスト**: 既存ユーザー指定通り「**書き換えない**」方針。`capacity = capacity_lim ∘ BlockwiseChannel.ofMemoryless` 同値補題で `R < capacity W → R < capacity_lim (ofMemoryless W)` の rewriting で接続できる。書き換え対象 0 件。

### C. block-wise (n-letter) extension の現状

| 概念 | API | file:line | 状態 | I-2 での扱い |
|---|---|---|---|---|
| `iidAmbientMeasure (p : Measure α) (W : Channel α β) : Measure (ℕ → α × β) := Measure.infinitePi (fun _ : ℕ => jointDistribution p W)` | `IIDProductInput.lean:48` | `IIDProductInput.lean:48` | ✅ 既存 (∞-letter 形、IID joint distribution from p ⊗ W) | block-wise extension 自体は **`Measure.pi` 形 / `Measure.infinitePi` 形 の 2 経路** で実装済み。`BlockwiseChannel` 抽象には plumbing 経路として再利用 |
| `iidAmbientJointMeasure (joint : Measure (α × β)) : Measure (ℕ → α × β) := Measure.infinitePi (fun _ : ℕ => joint)` | `IIDProductInputJoint.lean:33` | `IIDProductInputJoint.lean:33` | ✅ 既存 (rate-distortion 用、IID joint 直接形) | 一般 channel における **block 入力 → block 出力 joint** の構成参考形 |
| `iidXs i ω := (ω i).1`, `iidYs i ω := (ω i).2` (coordinate RVs) | `IIDProductInput.lean:60-63` | `IIDProductInput.lean:60-63` | ✅ 既存 | n-letter RV の取り出し plumbing |
| `iidAmbient_map_iidXs`, `iidAmbient_map_iidYs`, `iidAmbient_map_jointSequence` (marginal identifications) | `IIDProductInput.lean:91-132` | `IIDProductInput.lean:91-132` | ✅ 既存 | marginal 法則。`Measure.infinitePi_map_eval` (Mathlib) ベース |
| `iidAmbient_iIndepFun_iidXs/iidYs/joint` (mutual independence) | `IIDProductInput.lean:169-205` | `IIDProductInput.lean:169-205` | ✅ 既存 | i.i.d. 性。`iIndepFun_infinitePi` ベース |
| `Code.errorProbAt` (前述、 memoryless extension `Measure.pi (i ↦ W (x i))` 形) | `ChannelCoding.lean:204` | `ChannelCoding.lean:204` | ✅ 既存 (**memoryless 暗黙仮定**) | `BlockwiseChannel` 抽象では `W_n (x : Fin n → α) (error)` に書き換え |
| `mutualInfo_iid_eq_nsmul` (`I(X^n; Y^n) = n · I(X_0; Y_0)` 等式) | `MIChainRule.lean:392` | `MIChainRule.lean:392` | ✅ 既存 (**memoryless capacity vs general capacity 接続の核補題**) | `capacity_lim = capacity` 同値補題の主軸 |
| `mutualInfo_pi_eq_sum` (`I(X^n; Y^n) = ∑ I(X_i; Y_i)` 等式) | `MIChainRule.lean:341` | `MIChainRule.lean:341` | ✅ 既存 | 同上、一般 product 入力 (非 i.i.d.) では additivity が崩れる注意 |
| `mutualInfo_chain_rule_fin` (`I(X^n;Y) = ∑ I(X_i; Y | X^{<i})` 等式) | `MIChainRule.lean:117` | `MIChainRule.lean:117` | ✅ 既存 | block input の MI 上界 derivation で使う候補 |
| `klDiv_pi_eq_sum` (`klDiv (Measure.pi μs) (Measure.pi νs) = ∑ klDiv (μs i) (νs i)`) | `MIChainRule.lean:273` | `MIChainRule.lean:273` | ✅ 既存 | block additivity 系統 |

**重要**: I-2 で必要な `(1/n) sup_{p^n} I(X^n; Y^n)` の `sup` 部分は **一般 product 入力** に渡る。memoryless 時の equality `sup_{p^n} I(X^n; Y^n) = n · sup_p I(X;Y)` は Cover-Thomas Thm 7.7.3 に対応するが、**項目 (Thm 7.7.3 の上界 `I(X^n;Y^n) ≤ ∑ I(X_i; Y_i) ≤ n · capacity W`) は project に未整備** (`mutualInfo_chain_rule_fin` で和形まで取れるが、各 summand を `capacity W` で押さえる sup-over-marginal の boilerplate がない)。`channel_coding_converse_general_chainRule` (`ChannelCodingConverseGeneral.lean`) はこの和形を converse の枠で publish 済 (Markov encoder 制約付き) が、capacity との接続まではいっていない。

### D. Mathlib 側 Kernel / Product Measure API

| API | file:line | signature | I-2 での扱い |
|---|---|---|---|
| `Measure.compProd (μ : Measure α) (κ : Kernel α β) : Measure (α × β)` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:43` | `(μ : Measure α) → (κ : Kernel α β) → Measure (α × β)` (notation `μ ⊗ₘ κ`) | block joint `p^n ⊗ₘ W_n` の構成基盤 |
| `Measure.compProd_apply [SFinite μ] [IsSFiniteKernel κ] {s} (hs : MeasurableSet s) : (μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:61` | 同上 | block channel 出力分布の評価 |
| `Measure.compProd_apply_prod [SFinite μ] [IsSFiniteKernel κ] {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) : (μ ⊗ₘ κ) (s ×ˢ t) = ∫⁻ a in s, κ a t ∂μ` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:69` | 同上 | block product set 評価 |
| `ProbabilityTheory.Kernel.prod (κ : Kernel α β) (η : Kernel α γ) : Kernel α (β × γ)` (`κ ×ₖ η`) | `Mathlib/Probability/Kernel/Composition/Prod.lean:50` | `(κ : Kernel α β) → (η : Kernel α γ) → Kernel α (β × γ)` | **2 つの kernel** の積。`Kernel.pi` の代用 (再帰的に積を取る) には使えるが boilerplate が増える |
| `MeasureTheory.Measure.infinitePi (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)] : Measure (Π i, X i)` | `Mathlib/Probability/ProductMeasure.lean:355` | `(μ : ∀ i, Measure (X i)) → [∀ i, IsProbabilityMeasure (μ i)] → Measure (∀ i, X i)` | block input distribution `p^∞` の構成。`Measure.pi` 用無限版 |
| `MeasureTheory.Measure.infinitePi_map_eval (i : ι) : (infinitePi μ).map (fun x ↦ x i) = μ i` | `Mathlib/Probability/ProductMeasure.lean:478` | 同上 | coordinate projection identification |
| `MeasureTheory.Measure.infinitePi_pi {s : Finset ι} {t : (i : ι) → Set (X i)} (mt : ∀ i ∈ s, MeasurableSet (t i)) : infinitePi μ (Set.pi s t) = ∏ i ∈ s, μ i (t i)` | `Mathlib/Probability/ProductMeasure.lean:402` | 同上 | cylinder 形の評価 |
| `MeasureTheory.Measure.pi (μ : (i : ι) → Measure (α i)) : Measure (Π i, α i)` (Fintype 版) | `Mathlib/MeasureTheory/Constructions/Pi.lean` | `[Fintype ι] [∀ i, SigmaFinite (μ i)] → Measure (∀ i, α i)` | n-letter `p^n` の構成 (`Fin n` index) |
| `MeasureTheory.Measure.pi_pi`, `MeasureTheory.Measure.pi.instIsProbabilityMeasure` | `Mathlib/MeasureTheory/Constructions/Pi.lean` | finite product instances | `BlockwiseChannel.ofMemoryless` での block 構成基盤 |
| `MeasurableEquiv.piEquivPiSubtypeProd` | `Mathlib/MeasureTheory/MeasurableSpace/Embedding` 周辺 | `(∀ i, α i) ≃ᵐ ({i // p i} → α i) × ({i // ¬p i} → α i)` | `Fin n → α` の subtype 分解 (既存 `measurableEquivExtract` で使用済) |
| `MeasurableEquiv.piFinSuccAbove` | Mathlib | `(∀ i : Fin (n+1), α i) ≃ᵐ α (Fin.last n) × (∀ j : Fin n, α (Fin.last n).succAbove j)` | block 帰納の主軸 |

**否定的発見**: 
- **`ProbabilityTheory.Kernel.pi` (`(∀ i, Kernel (α i) (β i)) → Kernel (∀ i, α i) (∀ i, β i)`) は Mathlib 不在**。`rg` で project / Mathlib 両方とも 0 件。memoryless block channel `W^n = Kernel.pi (fun _ => W)` の構成は **手作り plumbing が必要** (~20-40 行)。素材は揃っている (各 `x : Fin n → α` に対し `Measure.pi (fun i => W (x i))` という measure-valued 関数の Kernel への lift)。
- **`InformationTheory.Shannon.Channel` / DMC / channel capacity の Mathlib 既存 API は 0 件** (`rg` で `MemorylessChannel`, `channel_capacity`, `DiscreteMemoryless` をすべて検索、全て 0 件)。Mathlib `InformationTheory/` 名前空間に Shannon 系 channel theory は完全不在 (前回の `docs/shannon/shannon-mathlib-inventory.md` の発見と整合)。

### E. 既存 `InformationTheory/Shannon/` の MI / chain rule API (block input MI bound 用)

| API | file:line | signature | I-2 での扱い |
|---|---|---|---|
| `mutualInfo (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ := klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))` | `MutualInfo.lean:36` | `[MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] → (μ : Measure Ω) → (Xs : Ω → X) → (Yo : Ω → Y) → ℝ≥0∞` | 主役定義。`I(X^n; Y^n)` は `Xs := fun ω i => Xs i ω` の形で取る |
| `mutualInfo_iid_eq_nsmul {n : ℕ} (hn : 0 < n) (μ) [IsProbabilityMeasure μ] (Xs Ys : Fin n → Ω → α) (...) : mutualInfo μ (fun ω i => Xs i ω) (fun ω i => Ys i ω) = n • mutualInfo μ (Xs ⟨0, hn⟩) (Ys ⟨0, hn⟩)` | `MIChainRule.lean:392` | i.i.d. 仮定 (`h_iid_joint`, `h_iid_X`, `h_iid_Y`, `h_copy`, `h_copy_X`, `h_copy_Y` の 6 個) | **`capacity_lim = capacity` 同値補題の核**。memoryless 入力 `p^n` 下で `I(X^n;Y^n) = n · I(X_0;Y_0)` を提供 |
| `mutualInfo_pi_eq_sum {n : ℕ} (μ) [IsProbabilityMeasure μ] (Xs Ys : Fin n → Ω → α) (...) : mutualInfo μ (fun ω i => Xs i ω) (fun ω i => Ys i ω) = ∑ i : Fin n, mutualInfo μ (Xs i) (Ys i)` | `MIChainRule.lean:341` | product 仮定 (`h_iid_joint`, `h_iid_X`, `h_iid_Y` の 3 個、ただし全 i 共通分布の `h_copy` は不要) | 非 i.i.d. block input でも product joint なら和に分解。`I(X^n;Y^n) ≤ n · capacity W` 上界の途中段 |
| `mutualInfo_chain_rule_fin {n : ℕ} (μ) [IsProbabilityMeasure μ] [StandardBorelSpace Y] [Nonempty Y] (Xs : Fin n → Ω → α) (hXs) (Yo : Ω → Y) (hYo) : mutualInfo μ (fun ω i => Xs i ω) Yo = ∑ i : Fin n, condMutualInfo μ (Xs i) Yo (fun ω j : Fin i.val => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)` | `MIChainRule.lean:117` | `[Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]`, `[StandardBorelSpace Y] [Nonempty Y]` | 一般 input chain rule。memoryless 仮定で each summand `≤ I(X_i; Y_i)` まで圧縮できる (`channel_coding_converse_general_memoryless` で証明済) |
| `klDiv_prod_eq_add {α' β'} [MS α'] [MS β'] (μ₁ μ₂ : Measure α') [IPM μ₁] [IPM μ₂] (ν₁ ν₂ : Measure β') [IPM ν₁] [IPM ν₂] : klDiv (μ₁.prod ν₁) (μ₂.prod ν₂) = klDiv μ₁ μ₂ + klDiv ν₁ ν₂` | `MIChainRule.lean:254` | 全て `IsProbabilityMeasure` 要求 | 2-letter block の MI 上界に直結 |
| `klDiv_pi_eq_sum {n : ℕ} {α' : Fin n → Type*} [∀ i, MS (α' i)] (μs νs : ∀ i, Measure (α' i)) [∀ i, IPM (μs i)] [∀ i, IPM (νs i)] : klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i : Fin n, klDiv (μs i) (νs i)` | `MIChainRule.lean:273` | 全 i で `IsProbabilityMeasure` | n-letter block product の KL 分解 |

### F. memoryless converse 系 (D-2'' 経路、roadmap I-2 でも再利用可能)

| API | file:line | signature 要点 | I-2 での扱い |
|---|---|---|---|
| `structure IsMemorylessChannelStrong (μ) [IsFM μ] (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β) : Prop where per_letter_markov, outputs_cond_indep` | `ChannelCodingConverseGeneralStrong.lean:64` | 2 軸の Markov chain axiom (per-letter + outputs conditional independence) | memoryless DMC の **kernel-free** 述語。`BlockwiseChannel.ofMemoryless` の characterization にそのまま使える |
| `def IsMemorylessChannel (μ) [IsFM μ] (Xs Ys) : Prop := ∀ i, IsMarkovChain μ (Xother, Yother) (Xs i) (Ys i)` | `ChannelCodingConverseGeneralComplete.lean:92` | 1 軸 Markov chain (γ-form) | より単純な形 |
| `theorem mutualInfo_le_sum_per_letter_of_memoryless_strong` | `CondEntropyMemoryless.lean:546` | `IsMemorylessChannelStrong` 仮定 + entropy 劣加法経路で `I(X^n;Y^n).toReal ≤ ∑ I(X_i;Y_i).toReal` | **`capacity_lim ≤ capacity`** の主軸 (memoryless 時の上界) |
| `entropy_pi_le_sum_entropy` | `CondEntropyMemoryless.lean:63` | `H(Y^n) ≤ ∑ H(Y_i)` (subadditivity, encoder-agnostic) | 同上 |
| `condEntropy_pi_eq_sum_of_memoryless_strong` | `CondEntropyMemoryless.lean:398` | `H(Y^n|X^n) = ∑ H(Y_i|X_i)` (strong memoryless 下) | 同上 |
| `channel_coding_converse_general_memoryless_pure` | `ChannelCodingConverseMemorylessPure.lean:650` | memoryless DMC converse 完全形 (`IsMemorylessChannel` のみ仮定) | I-2 の publish ターゲットには直接は使わないが、`capacity_lim_eq_capacity` 同値補題で `capacity_lim ≥ capacity` 不等式 (n=1 から trivial) のテンプレに使える |

### G. limit form の参考: `entropyRate` (`EntropyRate.lean`)

| API | file:line | signature | I-2 での扱い |
|---|---|---|---|
| `noncomputable def blockEntropy (μ) (p : StationaryProcess μ α) (n : ℕ) : ℝ := entropy μ (p.blockRV n)` | `EntropyRate.lean:58` | `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]` | I-2 の `capacityN W n` の form 参照点 |
| `noncomputable def entropyRate (μ) (p : StationaryProcess μ α) : ℝ := Filter.atTop.limUnder (fun n : ℕ => blockEntropy μ p n / n)` | `EntropyRate.lean:69` | 同上 | **I-2 `capacity_lim W := atTop.limUnder (fun n => capacityN W n / n)` のテンプレ** |
| `theorem entropyRate_exists_of_stationary` | `EntropyRate.lean:432` | `blockEntropy / n` の収束 | `capacity_lim` の存在証明テンプレ。stationary + antitone tail の Cesàro 経路 |
| `theorem conditionalEntropyTail_antitone` | `EntropyRate.lean:264` | stationarity + conditioning monotonicity | `capacity` の場合は **stationary 性に対応する subadditivity** (`f(n+m) ≤ f(n) + f(m)`、Fekete's subadditive lemma) を経由する形 |

**重要な相違点**: `entropyRate` は **stationary process** に対する limit。一方 `capacity_lim` は **任意 channel** に対して `(1/n) capacityN W n` の `n → ∞` 極限なので、stationary 性ではなく **`capacityN` の `n` に関する subadditivity** に立脚する。これは Cover-Thomas 7.7.3 の核。

### H. Mathlib limit / sSup API (`capacity_lim` 構成用)

| API | file:line | signature | I-2 での扱い |
|---|---|---|---|
| `Filter.atTop.limUnder : (ℕ → ℝ) → ℝ` | Mathlib | `(f : ℕ → ℝ) → ℝ` (極限が存在しないときは `0`) | `capacity_lim` の定義そのもの |
| `Filter.Tendsto.limUnder_eq` | Mathlib | `Tendsto f atTop (𝓝 ℓ) → atTop.limUnder f = ℓ` | 既存 `entropyRate_eq_lim_condEntropy` で使用済 |
| `Filter.Tendsto.div_atTop`, etc. | Mathlib | 様々な limit の代数 | Cesàro 系で必要 |
| **Fekete's subadditive lemma** | **Mathlib 不在** | `(a : ℕ → ℝ) → (∀ m n, a (m+n) ≤ a m + a n) → Tendsto (fun n => a n / n) atTop (𝓝 (sInf {a n / n | 0 < n}))` | I-2 の `capacity_lim` 存在証明に必要 (subadditivity)。**自作必須 ~50-80 行**。`rg "Fekete\|subadditive_lim\|infimum.*div" Mathlib/` で 0 件確認 |

`Filter.Tendsto` 系は plumbing 完備、唯一の本質的欠落は **subadditivity ⇒ limit 存在** の Fekete lemma。

---

## 主要前提条件ボックス

I-2 で使う API のうち前提事故が起きやすい lemma:

- **`Measure.compProd_apply`** は `[SFinite μ]` + `[IsSFiniteKernel κ]` 要求。`[IsProbabilityMeasure p]` + `[IsMarkovKernel W]` で自動。
- **`klDiv_compProd_eq_add`** (`Mathlib.InformationTheory.KullbackLeibler.ChainRule:204`) は `{μ ν : Measure X} {κ η : Kernel X Y}` + **`[IsFiniteMeasure μ]` + `[IsFiniteMeasure ν]` + `[IsMarkovKernel κ]` + `[IsMarkovKernel η]`**。block channel が markov でない場合に詰むが、本 I-2 では block channel は markov 維持で問題なし。
- **`Measure.infinitePi`** は `[hμ : ∀ i, IsProbabilityMeasure (μ i)]` 要求。block input が probability measure である必要。
- **`mutualInfo_iid_eq_nsmul`** は 6 個の i.i.d. 仮説 (`h_iid_joint`, `h_iid_X`, `h_iid_Y`, `h_copy`, `h_copy_X`, `h_copy_Y`) + `hn : 0 < n` を要求。memoryless DMC × IID input で全て discharge できるが、call site で plumbing が必要。
- **`mutualInfo_chain_rule_fin`** は `[StandardBorelSpace Y] [Nonempty Y]` + `[Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]` を要求。**`Fin n → α` 上の `StandardBorelSpace` instance は finite alphabet では auto-derive**だが、`Fin n → α × β` 等の入れ子で詰まることがある。
- **`entropy_pi_le_sum_entropy`**, **`mutualInfo_le_sum_per_letter_of_memoryless_strong`** (`CondEntropyMemoryless.lean`) は `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]` を `α` 両側に要求。block alphabets `Fin n → α` が `MeasurableSingletonClass` を保つかは要確認 (Mathlib auto-derive 期待)。

---

## 自作が必要な要素 (優先度順)

1. **`Kernel.pi` lift (~20-40 行)**: `(W : Channel α β) → Channel (Fin n → α) (Fin n → β)` のような `Channel.toBlock` を **`Measure.pi (fun i => W (x i))` 経由で関数として** 構成。Markov 性は instance で auto。**最大の落とし穴**: `Kernel.pi` が Mathlib 不在 (本調査での確定発見) のため、自作補題で `Measure` を返す関数を `Kernel.mk` で kernel に lift する必要。
2. **`BlockwiseChannel α β` 抽象 (関数形軽量経路) + `ofMemoryless : Channel α β → BlockwiseChannel α β` (~20 行)**: 上の `Kernel.pi` lift を関数 `(n : ℕ) → Kernel ...` に巻く。
3. **`mutualInfoOfChannelBlock (p : Measure (Fin n → α)) (W_n : Kernel (Fin n → α) (Fin n → β)) : ℝ≥0∞` (~5 行)**: 単に `mutualInfoOfChannel p W_n` の rename だが、signature 揃え用。
4. **`capacityN (W : BlockwiseChannel α β) (n : ℕ) : ℝ` + `capacityN_nonneg`, `capacityN_bddAbove` (~40-60 行)**: 既存 `capacity_image_nonempty`, `capacity_bddAbove` の block 版。stdSimplex over `Fin n → α` は finite なので `IsCompact` auto-derive 可。
5. **`capacityN_subadditive : ∀ m n, capacityN W (m + n) ≤ capacityN W m + capacityN W n` (~50-100 行)**: I-2 の **数学的に最重要な性質**。chain rule (`mutualInfo_chain_rule_fin`) と sup の合成で示すが、各 summand を per-input-block の sup で押さえる careful な argument が要る。Cover-Thomas 7.7.3 の formalization、project に未整備。
6. **Fekete's subadditive limit lemma (~50-80 行)**: `(a : ℕ → ℝ) → (∀ m n, a (m+n) ≤ a m + a n) → Tendsto (fun n => a n / n) atTop (𝓝 (sInf {a n / n | 0 < n}))`。Mathlib 不在 (再確認)。`capacity_lim` の existence の核。
7. **`capacity_lim (W : BlockwiseChannel α β) : ℝ` 定義 + `capacity_lim_exists` (~10-20 行)**: 上の Fekete 適用で `Filter.atTop.limUnder` を `entropyRate` テンプレに従って巻く。
8. **`capacity_lim_eq_capacity_of_memoryless : capacity_lim (BlockwiseChannel.ofMemoryless W) = capacity W` (~50-150 行)**: I-2 の中核同値補題。`capacity_lim ≤ capacity` 方向は `mutualInfo_le_sum_per_letter_of_memoryless_strong` + sup 監視、`capacity_lim ≥ capacity` 方向は n=1 evaluation + Fekete monotonicity (limit ≥ 任意 term)。
9. **(オプション) informationally stable channel 経由 spectral form (~100-300 行)**: roadmap 上限ケース。`Han-Verdu` の framework を本格的に組むなら追加。本 I-2 scope では deferred 推奨。

**自作合計見積もり**: 軽量経路 (関数形、step 1-8 のみ) **~300-500 行**、roadmap 上限 (informationally stable 拡張含む step 9 まで) **~600-1000 行**。

---

## 撤退ラインへの距離

roadmap I-2 自体の scope は ~600-1000 行と推定されており、**撤退ラインは明示されていない** が、実装難度上の 2 つの分岐点を I-2 サブシードとして提案する:

### 撤退ライン候補 1: `Kernel.pi` lift がうまく書けない

- **発動条件**: `Channel.toBlock` の Markov 性 instance が Mathlib `IsMarkovKernel` で auto-derive できず、手動構成が `Measure.pi` の `IsProbabilityMeasure` 経由で 100 行越え。
- **発動可能性**: 中程度。`Measure.pi` の `IsProbabilityMeasure` instance は揃っているので、関数 `(x : Fin n → α) ↦ Measure.pi (fun i => W (x i))` を `Kernel.mk` で巻くだけのはず。Markov 性は `Kernel` の Markov 述語が `∀ a, IsProbabilityMeasure (κ a)` であることから auto。
- **縮退案**: `BlockwiseChannel` を **関数 `(n : ℕ) → (Fin n → α) → Measure (Fin n → β)`** に変更 (kernel を介さない)。MI 計算は `Measure.compProd` の `IsSFiniteKernel` instance を逐次手作りすることになるが、I-2 の publish 内容は同等。

### 撤退ライン候補 2: Fekete subadditive lemma 自作で詰まる

- **発動条件**: subadditive limit lemma の証明 (cf. Steele "Cauchy's Functional Equation and Extensions") が project 内 Mathlib 範囲で 150 行越え (期待は 50-80 行)。
- **発動可能性**: 低。古典的補題で、`liminf`/`limsup` の simple argument。Mathlib に `Real.bddAbove_sInf` / `csInf_le_csInf` 系が揃っている。
- **縮退案**: `capacity_lim_exists` を「**limit が存在することは hypothesis として受け取る**」hypothesis-form に倒し、 `capacity_lim` の定義を `Filter.atTop.limUnder` (極限が存在しない場合 0) のままにする。memoryless specialization では limit が存在することが `mutualInfo_iid_eq_nsmul` から直接出る (constant sequence) ので publish 内容は維持。

### 撤退ライン非発動の最尤シナリオ

`BlockwiseChannel := (n : ℕ) → Kernel (Fin n → α) (Fin n → β)` の関数形 + Fekete を自前で書いた `capacity_lim` で、step 1-8 を **~400 行 + 0 sorry**。memoryless specialization は既存 `mutualInfo_le_sum_per_letter_of_memoryless_strong` + `mutualInfo_iid_eq_nsmul` の合成で **~50 行 + 0 sorry**。total **~450 行**。

---

## `BlockwiseChannel` 抽象の自然な形 (候補 3 つ、コスト評価)

### 候補 A: 関数形 (軽量、推奨)

```lean
noncomputable def BlockwiseChannel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
  : Type _ :=
  (n : ℕ) → Kernel (Fin n → α) (Fin n → β)

class BlockwiseChannel.IsMarkov (W : BlockwiseChannel α β) : Prop where
  isMarkov : ∀ n, IsMarkovKernel (W n)

noncomputable def BlockwiseChannel.ofMemoryless
    (W : Channel α β) [IsMarkovKernel W] : BlockwiseChannel α β :=
  fun n => -- self-built Kernel.pi via Measure.pi
    ⟨fun x => Measure.pi (fun i => W (x i)), measurability_proof⟩
```

- **既存 callsite への影響**: 0 (新規 namespace、既存 `Channel` / `capacity` は触らない)
- **新規 API 行数見積**: ~300-500 (step 1-8)
- **撤退ライン発動可能性**: 低

### 候補 B: structure 形 (整合性 axiom 付き)

```lean
structure BlockwiseChannel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  channel : (n : ℕ) → Kernel (Fin n → α) (Fin n → β)
  /-- Marginal consistency: 出力の i 成分は前 i+1 個の入力のみに依存。
      この axiom があると一般 (non-memoryless) channel の formal 整理が容易。 -/
  marginal_consistency : ∀ {n m : ℕ} (h : m ≤ n) (x : Fin n → α) (s : Set (Fin m → β)),
    (channel n x).map (fun y i => y ⟨i.val, i.isLt.trans_le h⟩) s
      = (channel m (fun i => x ⟨i.val, i.isLt.trans_le h⟩)) s
  isMarkov : ∀ n, IsMarkovKernel (channel n)
```

- **既存 callsite への影響**: 0
- **新規 API 行数見積**: ~600-900 (consistency axiom の plumbing 増)
- **撤退ライン発動可能性**: 中。`marginal_consistency` を memoryless 場合に discharge する補題が `Kernel.pi` 形の積分操作で 50-100 行になる懸念。
- **メリット**: 後続 informationally stable channels / Han-Verdu spectral form 拡張への入り口になる。

### 候補 C: 単純 `Kernel` 列挙 (定義最小、整合性なし)

```lean
def BlockwiseChannel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Type _ :=
  (n : ℕ) → (Fin n → α) → Measure (Fin n → β)
```

- **既存 callsite への影響**: 0
- **新規 API 行数見積**: ~200-300 (`Kernel` を介さないので measurability plumbing が手作りに)
- **撤退ライン発動可能性**: 高。MI 計算の `compProd` が `Kernel` を要求するため、各 `n` 毎に kernel-form rewriting が必要で boilerplate が増殖する懸念。**非推奨**。

---

## memoryless ↔ 一般の接続補題の signature 候補

I-2 の中核は「**memoryless 単一 letter capacity = block-wise limit capacity**」の同値補題。新規追加候補:

### 候補 1: `capacity = capacity_lim ∘ ofMemoryless` (mathematically natural)

```lean
theorem capacity_lim_eq_capacity_of_memoryless
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : InformationTheory.Shannon.ChannelCoding.Channel α β) [IsMarkovKernel W] :
    BlockwiseChannel.capacity_lim (BlockwiseChannel.ofMemoryless W)
      = InformationTheory.Shannon.ChannelCoding.capacity W
```

- 証明: `≤` 方向は `mutualInfo_le_sum_per_letter_of_memoryless_strong` (`CondEntropyMemoryless.lean:546`) + sup の monotonicity、`≥` 方向は IID `p^n := pmf^⊗n` を入力にとると `mutualInfo_iid_eq_nsmul` で `(1/n) I(X^n;Y^n) = I(X;Y)` (constant in `n`) なので Fekete limit の `≥` から従う。
- 既存補題で plumbing できる範囲: 80-90%。
- 必要新規補題: `BlockwiseChannel.ofMemoryless` の specifications 2-3 件、`capacityN_ofMemoryless_eq_n_mul_capacity` (`(1/n) capacityN (ofMemoryless W) n = capacity W` for all `n ≥ 1`)。

### 候補 2: `capacity ≤ capacity_lim ∘ ofMemoryless` の片側だけ先 publish

```lean
theorem capacity_le_capacity_lim_ofMemoryless
    (W : Channel α β) [IsMarkovKernel W] :
    capacity W ≤ (BlockwiseChannel.ofMemoryless W).capacity_lim
```

- 軽量、`≥` 方向だけ先に。`capacity W = capacityN (ofMemoryless W) 1` から trivial に出るので 10 行。

### 候補 3: per-`n` 不等式形 (limit を経由しない)

```lean
theorem capacityN_ofMemoryless_eq (W : Channel α β) [IsMarkovKernel W] (n : ℕ) (hn : 0 < n) :
    (BlockwiseChannel.ofMemoryless W).capacityN n = (n : ℝ) * capacity W
```

- IID input が optimal であることを言う形。Cover-Thomas Thm 7.7.3 そのもの。`mutualInfo_iid_eq_nsmul` で `≥` 方向、`mutualInfo_le_sum_per_letter_of_memoryless_strong` で `≤` 方向、各 input pmf に対して bound。**~80-150 行**。

**推奨**: 候補 3 → 候補 1 の順で publish。候補 3 が **mathematically the key lemma** で、候補 1 は単に `lim_n (n · C) / n = C` の trivial corollary。

---

## I-2 着手 skeleton

新規ファイル `InformationTheory/Shannon/BlockwiseChannel.lean` の出だし:

```lean
import InformationTheory.Shannon.ChannelCoding
import InformationTheory.Shannon.ChannelCodingShannonTheorem
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.CondEntropyMemoryless
import InformationTheory.Shannon.EntropyRate -- for limit form template
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProductMeasure

/-!
# Blockwise channel + capacity limit form (I-2 seed)

A `BlockwiseChannel α β` is a sequence of channels
`W_n : Kernel (Fin n → α) (Fin n → β)` (block-length n channel). The "general"
DMC capacity is

  capacity_lim W := lim_{n → ∞} (1/n) · sup_{p^n} I(X^n; Y^n)

For memoryless DMC (W_n := ⊗_n W₁), this reduces to the single-letter
formula capacity W₁ via `mutualInfo_iid_eq_nsmul` + Fekete's subadditive lemma.

## Main definitions

* `BlockwiseChannel α β := (n : ℕ) → Kernel (Fin n → α) (Fin n → β)`
* `BlockwiseChannel.ofMemoryless (W : Channel α β) [IsMarkovKernel W]
    : BlockwiseChannel α β` — memoryless block extension
* `BlockwiseChannel.capacityN W n` — per-block capacity (1-letter sup analog)
* `BlockwiseChannel.capacity_lim W` — limit form

## Main results

* `capacityN_subadditive` — `capacityN W (m+n) ≤ capacityN W m + capacityN W n`
* `capacity_lim_eq_of_subadditive` — Fekete limit existence
* `capacity_lim_eq_capacity_of_memoryless` — bridge to existing `capacity W`
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}

/-! ## Definition -/

/-- A **blockwise channel** is a sequence of (Markov) kernels, one per block
length. `BlockwiseChannel.ofMemoryless W` provides the i.i.d. extension of a
single-letter DMC. -/
noncomputable def BlockwiseChannel (α β : Type*)
    [MeasurableSpace α] [MeasurableSpace β] : Type _ :=
  (n : ℕ) → Kernel (Fin n → α) (Fin n → β)

variable [MeasurableSpace α] [MeasurableSpace β]

/-- Memoryless block extension: `W_n x := Measure.pi (i ↦ W (x i))`. -/
noncomputable def BlockwiseChannel.ofMemoryless
    (W : Channel α β) [IsMarkovKernel W] : BlockwiseChannel α β := by
  sorry

instance BlockwiseChannel.ofMemoryless_isMarkov
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) :
    IsMarkovKernel ((BlockwiseChannel.ofMemoryless W) n) := by
  sorry

/-! ## Per-block capacity -/

/-- Per-block capacity: `(1/n) · sup_{p^n} I(X^n; Y^n)`. Defined as the `sSup`
over all probability measures on `Fin n → α`. -/
noncomputable def BlockwiseChannel.capacityN
    (W : BlockwiseChannel α β) (n : ℕ) : ℝ := by
  sorry

theorem BlockwiseChannel.capacityN_nonneg (W : BlockwiseChannel α β) (n : ℕ)
    [IsMarkovKernel (W n)] : 0 ≤ W.capacityN n := by sorry

theorem BlockwiseChannel.capacityN_subadditive
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : BlockwiseChannel α β) [∀ n, IsMarkovKernel (W n)] (m n : ℕ) :
    W.capacityN (m + n) ≤ W.capacityN m + W.capacityN n := by
  sorry

/-! ## Capacity limit form -/

/-- The asymptotic capacity: `lim_{n → ∞} capacityN W n / n`. Existence
provided by `capacity_lim_exists` (Fekete subadditive lemma). -/
noncomputable def BlockwiseChannel.capacity_lim (W : BlockwiseChannel α β) : ℝ :=
  Filter.atTop.limUnder (fun n : ℕ => W.capacityN n / n)

theorem BlockwiseChannel.capacity_lim_exists
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : BlockwiseChannel α β) [∀ n, IsMarkovKernel (W n)] :
    ∃ ℓ : ℝ, Filter.Tendsto (fun n : ℕ => W.capacityN n / n) Filter.atTop (𝓝 ℓ) := by
  sorry -- Fekete

/-! ## Bridge to single-letter `capacity W` -/

theorem capacityN_ofMemoryless_eq
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) (hn : 0 < n) :
    (BlockwiseChannel.ofMemoryless W).capacityN n = (n : ℝ) * capacity W := by
  sorry

theorem capacity_lim_eq_capacity_of_memoryless
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W] :
    (BlockwiseChannel.ofMemoryless W).capacity_lim = capacity W := by
  sorry

end InformationTheory.Shannon.ChannelCoding
```

---

## I-2 在庫まとめ

- インベントリは `docs/shannon/general-dmc-mathlib-inventory.md` (本ファイル)
- 既存率 (素材レベル): **~70%**
  - 単一 letter `Channel` / `capacity` / `mutualInfoOfChannel` / `Code` / `errorProbAt`: ✅ 完備
  - block-wise extension の素材 (`Measure.pi`, `Measure.infinitePi`, `iidAmbientMeasure`): ✅ 完備
  - i.i.d. の MI 等式 (`mutualInfo_iid_eq_nsmul`, `mutualInfo_pi_eq_sum`): ✅ 完備
  - memoryless converse 系 (`mutualInfo_le_sum_per_letter_of_memoryless_strong`): ✅ 完備
- 既存率 (主役定理レベル): **0%**
  - `BlockwiseChannel`, `capacity_lim`, `capacity_lim_eq_capacity_of_memoryless`: ❌ project / Mathlib 両方とも完全不在
- **新規必要件数**: 主要 8 件 (`Kernel.pi` lift / `BlockwiseChannel` / `capacityN` / `capacityN_subadditive` / Fekete lemma / `capacity_lim` / `capacityN_ofMemoryless_eq` / `capacity_lim_eq_capacity_of_memoryless`)
- **撤退ライン発動**: なし (軽量経路の `BlockwiseChannel := (n : ℕ) → Kernel ...` で step 1-8 を ~400 行 + 0 sorry が見込み)。Fekete lemma で詰まる場合は hypothesis-form に倒す縮退案を準備
- **最大の発見**: **`ProbabilityTheory.Kernel.pi` が Mathlib 不在**。memoryless block channel `W^n = Kernel.pi (fun _ => W)` の構成は自前 plumbing が必要 (素材は `Measure.pi` + `IsProbabilityMeasure` で揃っている、~20-40 行見込み)。これは前回 `docs/shannon/shannon-mathlib-inventory.md` の "Mathlib InformationTheory に Shannon 系の中核は完全不在" と整合する Mathlib 側 channel API の薄さの再確認。

着手準備 OK。新規ファイル `InformationTheory/Shannon/BlockwiseChannel.lean` (400-500 行見込み) + 既存 `InformationTheory/Shannon/ChannelCoding.lean` 系の 0-sorry 維持 (callsite 13 箇所は touch しない方針)。

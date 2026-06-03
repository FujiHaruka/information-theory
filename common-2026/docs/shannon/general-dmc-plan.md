# I-2 General DMC capacity (limit form) サブ計画 🌙

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier ∞ — Infrastructure / I-2」
> **Inventory**: [`general-dmc-mathlib-inventory.md`](./general-dmc-mathlib-inventory.md)
> **先行**: I-1 (`InformationTheory/Shannon/TypedRV.lean`) / I-3 (`InformationTheory/Asymptotic.lean`)
>
> Cover & Thomas 7.7 (information capacity の operational definition と memoryless 場合の
> 単一 letter 形への一致) の formalization。後続の T2-A AWGN / T3-B MAC / T3-C BC が
> 「memoryless 限定でない一般 channel」を前提に capacity を扱うため、Tier 2 以降に着手する
> **前** に block-wise abstraction を確立しておく。
>
> 既存 0-sorry callsite (`capacity W` 13 箇所) は **書き換えない**。新規 namespace
> `BlockwiseChannel` / `capacity_lim` を並置し、`capacity_lim_eq_capacity_of_memoryless` で
> 接続する形をとる。

## 進捗

- [x] Phase 0 — `Kernel.pi` / Fekete の Mathlib 在庫再確認 ✅
- [x] Phase 1 — skeleton (`BlockwiseChannel.lean` 新規ファイル) ✅
- [x] Phase 2 — `Channel.toBlock` (`Kernel.pi` 自前 lift) ✅
- [x] Phase 3 — `capacityN` / `capacity_lim` 定義充填 + 基本性質 ✅
- [x] Phase 4 — `ofMemoryless` 構成 + 主接続補題 `capacity_lim_eq_capacity_of_memoryless` ✅
  - [x] Phase 4-α — per-`n` 等式 `capacityN_ofMemoryless_eq` ✅
  - [x] Phase 4-β — `Subadditive.tendsto_lim` (memoryless は constant 列で Fekete 不要) ✅
- [x] Phase 5 — verify + regression check ✅
- [ ] Phase 6 (optional) — 支援補題 `capacityN.mono` / `capacityN.nonneg` 等 📋

> 実態整合 (2026-05-20): DONE-UNCOND — 進捗マーカーが起草時の `[ ]` のまま、判断ログも "Phase 4-α 1 sorry 残" (Session 1/2) で stop していたが、`InformationTheory/Shannon/BlockwiseChannel.lean` (64 KB) は real-sorry **ゼロ**。`capacityN_ofMemoryless_eq` (`:1165`、両側 `_le:1007` / `_ge:1100` 含め 0 sorry、bridge `toBlock_compProd_pi_factor:149` も完成) + 主接続補題 `capacity_lim_eq_capacity_of_memoryless` (`:1181`、std typeclass binders + `[StandardBorelSpace α/β]` のみ) が完走。`InformationTheory.lean:64` に import 済。再 export 層 `InformationTheory/Shannon/GeneralDMC.lean` も 0 sorry。判断ログ Session 2 の `proof-pivot-advisor` エスカレーション (`Channel.toBlock` を `Kernel.mk` 直接定義へ再定義) は実行され bridge が閉じた模様。

## ゴール / Approach

### Goal (最終定理 signature)

```lean
-- 新規定義 (`InformationTheory/Shannon/BlockwiseChannel.lean`)
def BlockwiseChannel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Type _ :=
  (n : ℕ) → Kernel (Fin n → α) (Fin n → β)

namespace BlockwiseChannel
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

noncomputable def capacityN (W : BlockwiseChannel α β) (n : ℕ) : ℝ≥0∞
noncomputable def capacity_lim (W : BlockwiseChannel α β) : ℝ

noncomputable def ofMemoryless (W : Kernel α β) [IsMarkovKernel W] :
    BlockwiseChannel α β

-- 主接続補題
theorem capacity_lim_eq_capacity_of_memoryless
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W] :
    (ofMemoryless W).capacity_lim
      = InformationTheory.Shannon.ChannelCoding.capacity W
```

### Approach (overall strategy / shape of solution)

**戦略の shape**: I-2 は既存の単一 letter `capacity W` を **書き換えず**、その上に
**並置 layer** を積む形をとる。新規 `BlockwiseChannel` namespace を作って `capacity_lim` を
publish し、最後に **memoryless 場合の specialization 補題 1 本** で既存 `capacity` と接続する。

4 段で展開する:

1. **`BlockwiseChannel` 抽象 (関数形)**: 在庫の候補 A (`(n : ℕ) → Kernel (Fin n → α) (Fin n → β)`)
   を採用。structure 形は marginal consistency axiom の plumbing コスト (600-900 行) が割に合わない、
   かつ後続 seed (AWGN / MAC) はどれも memoryless の specialization で十分。
2. **`capacityN` の定義**: `mutualInfoOfChannel : ℝ≥0∞` をそのまま再利用、`ℝ≥0∞`-値の
   `sSup` over `{ p : Measure (Fin n → α) | IsProbabilityMeasure p }` で定義。`.toReal` は
   `capacity_lim` 側に押し付ける (既存 `capacity : ℝ` と signature を揃えるための最小変換)。
3. **`capacity_lim` を `Filter.atTop.limUnder` で定義**し、Fekete (subadditive limit) で
   存在を確保する。Mathlib に `Subadditive.tendsto_lim` の有無を **Phase 0 で再確認**し、
   なければ 50-80 行の自作 (撤退ライン §H-2)。
4. **`ofMemoryless` + `capacity_lim_eq_capacity_of_memoryless`**: `ofMemoryless W n` は
   `Measure.pi (fun i => W (x i))` を `Kernel.mk` で kernel に lift する自前 plumbing
   (Mathlib に `Kernel.pi` 不在、~20-40 行)。接続補題は
   **(α)** `capacityN (ofMemoryless W) n = n · capacity W` (Cover-Thomas 7.7.3) +
   **(β)** constant sequence の limit 評価、の合成。

**Bridge と既存資産の関係**:

- 既存 `ChannelCoding.lean` / `ChannelCodingShannonTheorem.lean` / `ChannelCodingShannonTheoremFull.lean`
  系は **不変**。`capacity W` 13 callsite の regression check は Phase 5 で実施。
- `mutualInfo_iid_eq_nsmul` (`MIChainRule.lean:392`) と
  `mutualInfo_le_sum_per_letter_of_memoryless_strong` (`CondEntropyMemoryless.lean:546`) が
  Phase 4-α の主軸。前者で `≥` (IID input で達成)、後者で `≤` (任意 product input の上界)。
- `Measure.pi`, `Measure.infinitePi`, `IIDProductInput.lean` の ad-hoc 形は **再利用しないで**
  新規 `Kernel.mk`-based lift を書く (在庫 §C 既存 plumbing は `Measure.pi` 形のまま、kernel 化が
  未実装なため)。

### 規模見積

| Phase | 内容 | 行数 |
|---|---|---|
| 0 | Mathlib 在庫再確認 (`Kernel.pi`, `Subadditive.tendsto_lim`) | 0 |
| 1 | skeleton (全 sorry) | ~80 |
| 2 | `Channel.toBlock` / `Kernel.mk` lift + Markov instance | ~50-80 |
| 3 | `capacityN` / `capacity_lim` 定義 + nonneg / bddAbove | ~80-120 |
| 4-α | `capacityN_ofMemoryless_eq` | ~80-150 |
| 4-β | Fekete + `capacity_lim_eq_capacity_of_memoryless` | ~80-150 (Fekete 自作なら +50-80) |
| 5 | verify + regression check | 0 (実証のみ) |
| 6 | optional 支援補題 | ~30-50 |
| **合計** | | **~400-630 行** |

軽量経路で在庫の見積もり (~400-500 行) と整合。Fekete 自作 + optional Phase 6 込みで上振れすると ~630 行。

## 設計判断 (確定事項)

C-1〜8 は計画起草時 (2026-05-18) の確定。Phase 0 / Phase 4 着手時の発見で覆る場合は判断ログに append。

### C-1. `BlockwiseChannel` の表現 — **候補 A (関数形) 採用**

```lean
def BlockwiseChannel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Type _ :=
  (n : ℕ) → Kernel (Fin n → α) (Fin n → β)
```

**理由**: 後続 seed (T2-A AWGN / T3-B MAC / T3-C BC) はすべて memoryless extension での
specialization で十分。structure 形 (候補 B、marginal consistency axiom 付き) は
informationally stable channel 系の拡張に有用だが、本 I-2 scope では deferred。候補 C
(kernel を介さない `Measure` 列挙) は MI 計算で `compProd` の `IsSFiniteKernel` を毎回
手作りする boilerplate が増えるため非推奨。

### C-2. `capacityN` の型 — **`ℝ≥0∞`**

`mutualInfoOfChannel : Measure α → Channel α β → ℝ≥0∞` (既存) と signature を揃え、
`.toReal` の押し付けは `capacity_lim : ℝ` の定義側で一度だけ行う。`sSup` を `ℝ≥0∞`
で取ることで `IsProbabilityMeasure` でない辺 (空集合) 起因の `-∞` 処理を回避。

接続補題で `capacity W : ℝ` と比較する際は `ENNReal.toReal_eq_iff` 系で 1 段橋渡し。

### C-3. `capacity_lim` の lim 形 — **`Filter.atTop.limUnder` (= Tendsto 結果の取り出し)**

```lean
noncomputable def capacity_lim (W : BlockwiseChannel α β) : ℝ :=
  Filter.atTop.limUnder (fun n : ℕ => (W.capacityN n).toReal / n)
```

**理由**:
- 既存 `entropyRate` (`EntropyRate.lean:69`) が同じ形を採用、template として直接使える。
- `Tendsto` 形は `Filter.Tendsto.limUnder_eq` で再利用しやすい (後続 seed が
  `capacity_lim = ℓ` を hypothesis として受け取る場合の使い勝手が良い)。
- `limsup` 形にすると Phase 4-β の Fekete 経路が `Tendsto` 結果を limsup に再変換する
  ペナルティが付くため不採用。

### C-4. `ofMemoryless` のコンストラクタ — **`Kernel.mk` で自前 lift**

```lean
noncomputable def Channel.toBlock (W : Kernel α β) [IsMarkovKernel W] (n : ℕ) :
    Kernel (Fin n → α) (Fin n → β) :=
  { toFun := fun x => Measure.pi (fun i => W (x i))
    measurable' := /- Measure.pi measurability via finite product -/ }

noncomputable def BlockwiseChannel.ofMemoryless (W : Kernel α β) [IsMarkovKernel W] :
    BlockwiseChannel α β :=
  fun n => W.toBlock n
```

`Mathlib` に `ProbabilityTheory.Kernel.pi` は不在 (在庫 §D 確定発見)。
**配置**: 自前 lift は `BlockwiseChannel.lean` 内に置く (~30-50 行)。`Kernel.pi` を独立
helper として `InformationTheory/Probability/KernelPi.lean` に切り出す案も検討したが、本 I-2
範囲では呼び出し点が 1 箇所 (`ofMemoryless`) のみで pre-mature abstraction、独立 helper
昇格は **Phase 2 で 30 行を超える兆候があれば** 撤退ライン §H-1 に従って分離する。

Markov 性は `IsMarkovKernel.mk' : (∀ a, IsProbabilityMeasure (κ a)) → IsMarkovKernel κ` で
auto-derive (各 `Measure.pi` は `IsProbabilityMeasure` instance を持つ)。

### C-5. Fekete's lemma の調達 — **Phase 0 で Mathlib 確認 → なければ自作 50-80 行**

在庫 §H で `rg "Fekete|subadditive_lim|infimum.*div" Mathlib/` が 0 件であることを確認済。
**ただし** `Mathlib.Analysis.SpecificLimits.Subadditive` 等の存在を `loogle "Subadditive.*Tendsto"`
+ `rg "structure Subadditive"` で **Phase 0 着手時に再確認** する。

- **見つかった場合**: 直接 `Subadditive.tendsto_lim` を call、`capacityN_subadditive`
  (新規補題、~50-80 行) を渡して `Tendsto` を取り出す。
- **見つからない場合**: 自作 (~50-80 行)。古典的 argument:
  - subadditivity から `a_n / n` が `n` に関して bounded below by `inf_k (a_k / k)`、
    bounded above by `a_1` (= 1 letter).
  - Cesàro 経路で `limsup (a_n / n) ≤ inf_k (a_k / k) ≤ liminf (a_n / n)`、squeeze で
    `Tendsto (a_n / n) atTop (𝓝 (sInf {a_n / n | 0 < n}))`.
  - Mathlib 既存の `Filter.limsup_le_iInf` / `Filter.iInf_le_liminf` 系で plumbing。

撤退ライン §H-2: 自作で 100 行を超えたら `capacity_lim` を `limsup` 定義に倒し、
`Tendsto → limsup` 変換を後続 seed に委ねる。

### C-6. 主接続補題の signature と前提

```lean
theorem capacity_lim_eq_capacity_of_memoryless
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W] :
    (BlockwiseChannel.ofMemoryless W).capacity_lim
      = InformationTheory.Shannon.ChannelCoding.capacity W
```

**前提の根拠**:
- `Fintype α / β` + `DecidableEq` + `MeasurableSingletonClass`: `pmfToMeasure`
  (`ChannelCodingShannonTheorem.lean:54`) の前提と一致。
- `Nonempty α / β`: `uniformMeasureβ` 系 / `Fin n → α` の inhabit 用。
- `IsMarkovKernel W`: 既存 `capacity_bddAbove` (`ChannelCodingShannonTheorem.lean:115`) と
  `mutualInfo_iid_eq_nsmul` の前提から共通。
- **`StandardBorelSpace` は不要**: 有限 alphabet なので auto-derive 範囲外、`mutualInfo_chain_rule_fin`
  の前提だが Phase 4-α では `mutualInfo_le_sum_per_letter_of_memoryless_strong` を使うので
  StandardBorelSpace 要求は出ない (在庫 §F 確認済)。

`Fin n → α` 側の `MeasurableSingletonClass` instance は Mathlib auto-derive
(`Pi.measurableSingletonClass` 経由) を期待、Phase 1 skeleton で確認。

### C-7. 支援補題のスコープ — **Phase 6 (optional) に逃がす**

`capacityN.mono`, `capacityN.nonneg`, `capacityN_bddAbove`, `capacityN_le_log_card` 等の
基本性質は **Phase 6 (optional)** に分離。Phase 4 で必要なものだけ Phase 3 内に inline
で書く (`capacityN_nonneg`, `capacityN_le_log_card` の 2 件のみ)。

後続 seed が `capacityN.mono` を要求した時点で Phase 6 を起こす方針。本 I-2 範囲で
publish 必須なのは **`capacity_lim` の存在 + memoryless specialization** のみ。

### C-8. ファイル配置 — **1 ファイル `InformationTheory/Shannon/BlockwiseChannel.lean`**

- 新規ファイル: `InformationTheory/Shannon/BlockwiseChannel.lean` (~400-500 行見込み)
- `InformationTheory.lean` に import 1 行追加 (`ChannelCodingShannonTheoremFullDischarge` 系の後、
  `IIDProductInput` 等の周辺、具体的位置は Phase 1 で確定)
- `Kernel.pi` 自前 lift も同ファイル内 (撤退ライン §H-1 発動時のみ別ファイル分離)

**分割案の却下理由**: `BlockwiseChannel.lean` (定義 + `capacityN`/`capacity_lim`) と
`BlockwiseChannelMemoryless.lean` (specialization) の 2 ファイル案は、Phase 4-α/β が
具体的構成 (`ofMemoryless`) と密結合で順序逆転による olean refresh 必要性が出るため、
1 ファイル維持。Phase 6 を起こす場合のみ `BlockwiseChannelSupport.lean` に切り出す。

## File / module layout

### 新規ファイル: `InformationTheory/Shannon/BlockwiseChannel.lean`

import 一覧 (`import Mathlib` 禁止):

```lean
import InformationTheory.Shannon.ChannelCoding
import InformationTheory.Shannon.ChannelCodingShannonTheorem
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.CondEntropyMemoryless
import InformationTheory.Shannon.EntropyRate -- limit form template
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.Algebra.Order.LiminfLimsup -- Subadditive / Tendsto
```

`Subadditive.tendsto_lim` の Mathlib path は Phase 0 で確定 (`loogle` で再検索)。
不在なら本 file 内に自前 + 上記 import 削除。

### `InformationTheory.lean` への追加

```diff
 import InformationTheory.Shannon.EntropyRate
+import InformationTheory.Shannon.BlockwiseChannel
```

`EntropyRate` の直後に挿入予定 (Phase 1 で具体位置確定)。

## Phase 0 — Mathlib API inventory 再確認 📋

在庫作成時 (2026-05 直前) からの Mathlib 更新を反映する gap-check 1 ターン。

- [ ] **0.1** `loogle "ProbabilityTheory.Kernel.pi"` で `Kernel.pi` の Mathlib 追加を再確認。
  あれば Phase 2 を skip、なければ自前 lift 継続。
- [ ] **0.2** `loogle "Subadditive.*Tendsto"` + `rg "structure Subadditive" .lake/packages/mathlib/Mathlib`
  で Fekete's lemma の Mathlib 在庫確認。あれば Phase 4-β で直接 call、なければ自前 50-80 行。
- [ ] **0.3** `loogle "Measure.pi (fun _ => _) _"` で `Measure.pi` の measurability 補題
  (`Kernel.mk` lift に必要) を再確認。

Phase 0 で 0.1 / 0.2 が positive ヒットした場合は、判断ログに記録し Phase 2 / 4-β の
規模を縮小。

## Phase 1 — skeleton 📋

新規ファイル `InformationTheory/Shannon/BlockwiseChannel.lean` を Write、全 sorry で
LSP silent (sorry warning のみ) を確認。

- [ ] **1.1** ファイル冒頭 (module doc + import + open namespace)。
- [ ] **1.2** `def BlockwiseChannel`.
- [ ] **1.3** `Channel.toBlock`, `BlockwiseChannel.ofMemoryless` (全 sorry).
- [ ] **1.4** `BlockwiseChannel.capacityN`, `capacity_lim`, `capacityN_nonneg`,
  `capacity_lim_nonneg` (全 sorry).
- [ ] **1.5** `capacityN_ofMemoryless_eq`, `capacity_lim_eq_capacity_of_memoryless` (sorry).
- [ ] **1.6** `InformationTheory.lean` に `import InformationTheory.Shannon.BlockwiseChannel` 追記、
  `lake env lean InformationTheory.lean` silent を確認。

skeleton 全体は ~80 行見込み。在庫 §「I-2 着手 skeleton」をそのまま採用。

## Phase 2 — `Channel.toBlock` + `Kernel.mk` lift 📋

`Kernel.pi` 自前 lift。`(W : Kernel α β) → (n : ℕ) → Kernel (Fin n → α) (Fin n → β)`
を `Measure.pi` 経由で構成。

- [ ] **2.1** `Channel.toBlock` の `toFun` 部 (`fun x => Measure.pi (fun i => W (x i))`)
  + measurability proof. measurability は `Kernel.measurable_kernel_prod_mk_iff` 系で
  `Measure.pi` の measurability に reduce。
- [ ] **2.2** `IsMarkovKernel` instance: 各 `x` で `Measure.pi (fun i => W (x i))` が
  `IsProbabilityMeasure` であることから auto-derive (`Measure.pi.instIsProbabilityMeasure`).
- [ ] **2.3** `BlockwiseChannel.ofMemoryless_eq` (`(ofMemoryless W) n = W.toBlock n`) — `rfl`.
- [ ] **2.4** `lake env lean InformationTheory/Shannon/BlockwiseChannel.lean` silent.

**撤退ライン §H-1 ガード**: 2.1 の measurability proof が 30 行を超えたら、
`InformationTheory/Probability/KernelPi.lean` に切り出して helper 化。本 I-2 plan の subgoal を
**Phase 4 まで暫定 axiom 化** で延命する分岐は §H-1 参照。

## Phase 3 — `capacityN` / `capacity_lim` 定義充填 + 基本性質 📋

- [ ] **3.1** `capacityN (W : BlockwiseChannel α β) (n : ℕ) : ℝ≥0∞`:
  ```lean
  sSup ((fun p : Measure (Fin n → α) =>
    mutualInfoOfChannel p (W n)) ''
    { p | IsProbabilityMeasure p })
  ```
- [ ] **3.2** `capacityN_nonneg : 0 ≤ capacityN W n` — `sSup` of nonneg-valued (`ℝ≥0∞`).
- [ ] **3.3** `capacityN_le_log_card`: `Fintype` alphabet 上の上界 `n · (log |α| + log |β|)`.
  既存 `capacity_bddAbove` の block 拡張、`log |α^n| = n · log |α|` で展開。
- [ ] **3.4** `capacity_lim (W : BlockwiseChannel α β) : ℝ`:
  ```lean
  Filter.atTop.limUnder (fun n : ℕ => (W.capacityN n).toReal / n)
  ```
- [ ] **3.5** `capacity_lim_nonneg`: `Tendsto` が確立した後で 0 ≤ limit (Phase 4-β で
  Fekete から `capacityN` が `nonneg` × `n` 単調 → limit nonneg).

## Phase 4 — `ofMemoryless` + 主接続補題 📋

### Phase 4-α — `capacityN_ofMemoryless_eq` (per-`n` 等式)

**主役**: `(BlockwiseChannel.ofMemoryless W).capacityN n = (n : ℝ≥0∞) * (capacity W : ℝ≥0∞)`
(または `.toReal` 経由で `= n * capacity W : ℝ`).

- [ ] **4-α.1** `≥` 方向: IID input `p^n := Measure.pi (fun _ => pmfToMeasure p_opt)` で達成。
  `mutualInfo_iid_eq_nsmul` (`MIChainRule.lean:392`) を 1 回 invoke。
  `p_opt` は `exists_capacity_achiever` (`ChannelCodingShannonTheorem.lean:317`) で取得。
- [ ] **4-α.2** `≤` 方向: 任意 product input `p^n` で `I(X^n; Y^n) ≤ n · capacity W` を示す。
  `mutualInfo_le_sum_per_letter_of_memoryless_strong` (`CondEntropyMemoryless.lean:546`) で
  `I(X^n; Y^n) ≤ ∑_i I(X_i; Y_i)`、各 summand を `capacity W` で押さえる。**ただし**
  product input 制約 (`p^n = ∏_i p_i`) の有無で扱いが分岐: 任意 `p` (non-product) 形を
  扱う場合は `mutualInfo_chain_rule_fin` (`MIChainRule.lean:117`) で chain 化、conditional
  MI の各 summand を sup で押さえる。
- [ ] **4-α.3** sSup の monotonicity (`sSup_le`, `le_sSup`) + 既存 `capacity` の
  `sup` 定義との変換。
- [ ] **4-α.4** `lake env lean` silent.

**規模**: ~80-150 行。Cover-Thomas 7.7.3 (single-input optimal の上界) の formalization。

### Phase 4-β — Fekete + `capacity_lim_eq_capacity_of_memoryless`

- [ ] **4-β.1** Phase 0.2 結果に従い、Fekete の本体を呼ぶ:
  - Mathlib にあれば `Subadditive.tendsto_lim` を直接 call。
  - なければ自前 `BlockwiseChannel.capacityN_subadditive` (`(m+n) ≤ m + n` 上界) +
    自前 Fekete (`tendsto_subadditive_div`).
- [ ] **4-β.2** `ofMemoryless W` の sequence `n ↦ capacityN (ofMemoryless W) n / n`
  は **constant** (`= capacity W` for all `n ≥ 1`)、よって `Tendsto`. Phase 4-α
  の per-`n` 等式から直接。
- [ ] **4-β.3** `capacity_lim_eq_capacity_of_memoryless` 完成. `Filter.Tendsto.limUnder_eq`
  で `atTop.limUnder = capacity W`.
- [ ] **4-β.4** `lake env lean` silent.

**規模**: ~80-150 行 (Fekete 自作で +50-80 行).

**撤退ライン §H-4 ガード**: 主接続補題で 5 ターン進まない場合、
`capacity_le_capacity_lim` と `capacity_lim_le_capacity` の 2 不等式に **分割 publish**。
片方が limit の `n=1` evaluation + Fekete monotonicity で trivial、片方が
Phase 4-α の sup-monotonicity だけで decompose 可能。

## Phase 5 — verify + regression check 📋

- [ ] **5.1** `lake env lean InformationTheory/Shannon/BlockwiseChannel.lean` で 0 sorry / 0 error.
- [ ] **5.2** 在庫 §D の既存 0-sorry ファイル全 silent 確認:
  - `InformationTheory/Shannon/ChannelCoding.lean`
  - `InformationTheory/Shannon/ChannelCodingAchievability.lean`
  - `InformationTheory/Shannon/ChannelCodingShannonTheorem.lean`
  - `InformationTheory/Shannon/ChannelCodingShannonTheoremFull.lean`
  - `InformationTheory/Shannon/ChannelCodingShannonTheoremFullDischarge.lean`
  - `InformationTheory/Shannon/ChannelCodingShannonTheoremGeneral.lean`
  - `InformationTheory/Shannon/ChannelCodingConverse*.lean`
  - `InformationTheory/Shannon/MIChainRule.lean`
  - `InformationTheory/Shannon/CondEntropyMemoryless.lean`
  - `InformationTheory/Shannon/EntropyRate.lean`
  - `InformationTheory/Shannon/IIDProductInput.lean`
- [ ] **5.3** サンプル `example`: `BlockwiseChannel ℝ ℝ` (AWGN dummy) で
  `(ofMemoryless W).capacity_lim` が型として通ることを確認 (compile only、値は計算不要).
- [ ] **5.4** `InformationTheory.lean` の全体 silent (= `lake build InformationTheory` 1 回).

## Phase 6 (optional) — 支援補題 📋

後続 seed (T2-A AWGN / T3-B MAC 等) で要求が出た時点で起こす。**Phase 5 完了 = I-2 publish**。

- [ ] **6.1** `capacityN.mono` (channel monotonicity).
- [ ] **6.2** `capacity_lim_nonneg`.
- [ ] **6.3** `capacityN_zero` (n = 0 の degenerate case).

## 判定条件 (Definition of Done)

`lake env lean InformationTheory/Shannon/BlockwiseChannel.lean` が **0 sorry / 0 error / 最小 warning**
で pass、かつ以下が全て満たされる:

- [ ] `BlockwiseChannel α β`, `BlockwiseChannel.capacityN`, `BlockwiseChannel.capacity_lim`,
  `BlockwiseChannel.ofMemoryless` の 4 つの新規定義が publish 済.
- [ ] `capacity_lim_eq_capacity_of_memoryless` が 0 sorry で publish 済.
- [ ] 在庫 §D の既存 0-sorry ファイル全てで regression なし (Phase 5.2 全 silent).
- [ ] `InformationTheory.lean` に `import InformationTheory.Shannon.BlockwiseChannel` 追記済.

## 撤退ライン

### §H-1. `Kernel.pi` 自作 lift で Phase 2 が 30 行 → helper 切り出し

- **発動条件**: Phase 2.1 の `Channel.toBlock` の measurability proof が `BlockwiseChannel.lean`
  内で 30 行を超える、または Markov instance derivation が 1 ターンで通らない。
- **対応**: `InformationTheory/Probability/KernelPi.lean` を独立 helper ファイルとして新規生成、
  `Kernel.pi : (∀ i, Kernel (α i) (β i)) → Kernel (∀ i, α i) (∀ i, β i)` (Fintype `Finset` 版)
  を publish。I-2 plan の **Phase 4 接続補題は ofMemoryless の暫定 axiom 化または
  `noncomputable def := sorry` で延命**、`BlockwiseChannel.lean` 内では `Kernel.pi` を
  使用する形に書き換え。Phase 4 の signature 変更は最小。

### §H-2. Fekete 自作で Phase 4-β が 100 行越え

- **発動条件**: Phase 4-β.1 で自前 `tendsto_subadditive_div` の proof が 100 行を超える、
  または `Subadditive.tendsto_lim` の Mathlib 存在を Phase 0.2 で確認できず自作も詰まる。
- **対応**: `capacity_lim` の定義を **`limsup` 形**に倒す:
  ```lean
  noncomputable def capacity_lim (W : BlockwiseChannel α β) : ℝ :=
    (Filter.atTop.limsup (fun n : ℕ => (W.capacityN n).toReal / n))
  ```
  `Tendsto → limsup` 変換は trivial (`Tendsto.limsup_eq`)。Fekete は **subadditivity から
  limsup ≤ inf 経路** に弱化、Cesàro 上界のみで `≤` 方向を取り、`≥` 方向は
  `iInf ≤ limsup` (Mathlib 既存) で取る。proof は ~30 行に縮小。
- **コスト**: 後続 seed が `Tendsto` 結果を直接欲しい場合に `Tendsto.limsup_eq` 経由の
  1 段橋渡しが要るが、boilerplate は最小。

### §H-3. 主接続補題の型クラス前提が `mutualInfo_iid_eq_nsmul` と合わない

- **発動条件**: Phase 4-α.1 で `mutualInfo_iid_eq_nsmul` の 6 個の i.i.d. 仮説 (在庫 §E)
  を `ofMemoryless W` の `Measure.pi` 構成から discharge できない。
- **対応**: 型クラス前提を 1 つずつ列挙 (`[Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]` + 同 β + `[IsMarkovKernel W]`)。
  各仮説の satisfiable 性を `iidAmbientMeasure` (`IIDProductInput.lean:48`) 構成と
  対照、最小集合を確定して Phase 4-α の補題に注入。最悪、`mutualInfo_iid_eq_nsmul` を
  本 plan 用に再 specialize した自前 lemma (~30-50 行) を Phase 4-α 前段に追加。

### §H-4. 主接続補題で 5 ターン進まない

- **発動条件**: Phase 4-β.3 着手後、`capacity_lim_eq_capacity_of_memoryless` の
  main proof で 5 ターン経過しても 0 sorry に至らない。
- **対応**: 主補題を **片側不等式 2 本に分割**:
  - `capacity_le_capacity_lim_ofMemoryless : capacity W ≤ (ofMemoryless W).capacity_lim`
    (n = 1 evaluation + Fekete monotonicity、~10-20 行).
  - `capacity_lim_ofMemoryless_le_capacity : (ofMemoryless W).capacity_lim ≤ capacity W`
    (Phase 4-α 上界 + limit monotonicity、~30-50 行).
  - 等式は `le_antisymm` で再合成 (~5 行). publish は 2 不等式 + 等式の 3 つ。

## 規模見積もり / 想定ターン数

- 行数: **~400-630 行** (軽量経路下限 400、Fekete 自作 + optional Phase 6 込み上限 630).
- ターン数: **~12-18 ターン** (Phase 0 ×1, Phase 1 ×1, Phase 2 ×2-3, Phase 3 ×2-3, Phase 4-α ×3-5,
  Phase 4-β ×2-4, Phase 5 ×1, Phase 6 optional ×1-2).
- 想定実装時間: **2-3 セッション** (1 セッションあたり ~4-6 ターン進む前提).

## 後続 seed への影響

I-2 publish 後、以下の Tier 2/3 seed が `BlockwiseChannel` namespace を前提に着手できる:

- **T2-A AWGN**: `BlockwiseChannel ℝ ℝ` で AWGN channel `Y_i = X_i + Z_i` を
  `Measure.pi (fun _ => W (x i))` (Gaussian convolution) で memoryless construction。
  `capacity_lim_eq_capacity_of_memoryless` で existing `capacity` 形 (Cover-Thomas 9.1.3)
  と接続。
- **T3-B MAC**: `BlockwiseChannel (α₁ × α₂) β` で MAC `(X_1, X_2) → Y`。`ofMemoryless`
  が ×₁ 直接形か × tuple の分解形かで設計分岐。
- **T3-C BC**: `BlockwiseChannel α (β₁ × β₂)` で broadcast channel `X → (Y_1, Y_2)`.
- **T3-F Relay**: `BlockwiseChannel` で cut-set bound の n-letter 化を 1 段抽象で書ける。

I-2 の `capacity_lim` 形 publish により、これら seed の **converse 経路 (n-letter 化)** が
`capacity_lim ≥ R` の形で statement 可能になる (現状は `capacity W ≥ R` 単一 letter 形で
擬似的に表現していた)。

## 参考

- Parent roadmap: [`textbook-roadmap.md`](../textbook-roadmap.md)
- Inventory: [`general-dmc-mathlib-inventory.md`](./general-dmc-mathlib-inventory.md)
- 先行 I-1: `InformationTheory/Shannon/TypedRV.lean`
- 先行 I-3: `InformationTheory/Asymptotic.lean`
- 既存 `capacity W`: `InformationTheory/Shannon/ChannelCodingShannonTheorem.lean:102`
- 既存 i.i.d. MI 等式: `InformationTheory/Shannon/MIChainRule.lean:392`
- 既存 memoryless MI 上界: `InformationTheory/Shannon/CondEntropyMemoryless.lean:546`
- limit 形 template: `InformationTheory/Shannon/EntropyRate.lean:69`
- フォーマット参考: [`channel-coding-shannon-theorem-general-plan.md`](./channel-coding-shannon-theorem-general-plan.md)
- 雛形: [`subplan-template.md`](../subplan-template.md)

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-18 起草**: 在庫 (`general-dmc-mathlib-inventory.md`) 完成 + ユーザー確認済み
   設計判断 (「並置 + memoryless specialization で接続」「既存 0-sorry ファイルは書き換えない」)
   を受けて本 plan を起草。`BlockwiseChannel` 表現は候補 A (関数形) で確定 (C-1)。
   Fekete は Phase 0 で Mathlib 確認 → なければ自作 50-80 行 (C-5 / §H-2)。
   `Kernel.pi` 自前 lift は同ファイル内 (C-4)、30 行越えで helper 切り出し (§H-1)。
   主接続補題は per-`n` 等式 (4-α) + Fekete (4-β) の 2 段、5 ターンで進まなければ
   片側不等式 2 本に分割 (§H-4)。

3. **2026-05-18 実装 (Session 2)**: Phase 4-α attempt → §H-4 発動 → split のみ、3 sorry。
   - **発見**: `Channel.toBlock` の inductive 定義 (`Kernel.prod` + `Kernel.comap` + `Kernel.map`
     再帰) と `Measure.pi`/`compProd` の構造的接続が完全に未整備。在庫 §C 既存補題
     (`mutualInfo_iid_eq_nsmul`, `mutualInfo_le_sum_per_letter_of_memoryless_strong`) は
     どちらも **`Measure.pi`-pushforward された joint distribution が前提** だが、
     `(p^n) ⊗ₘ (W.toBlock n)` を `Measure.pi (fun i => p ⊗ₘ W)` (経由 `(Fin n→α)×(Fin n→β) ≃ᵐ Fin n → α × β`)
     に factorize する補題が **Mathlib にも project にも 0 件** (`loogle "MeasureTheory.Measure.compProd, MeasureTheory.Measure.pi"` 0 hit)。
   - **対応 (§H-4 発動)**: Phase 4-α の単一 sorry を 3 つに split:
     - `toBlock_compProd_pi_factor` (構造的橋渡し、~80-150 行見込み、sorry)
     - `capacityN_ofMemoryless_le` (≤ 方向、sorry、bridge を使う proof skeleton コメント付)
     - `capacityN_ofMemoryless_ge` (≥ 方向、sorry、同上)
     main theorem `capacityN_ofMemoryless_eq` は `le_antisymm` のみで **0 sorry** に再構成。
   - **regression check**: 9 既存 0-sorry ファイル全 silent (Phase 5 部分達成)。
   - **次セッション推奨**: `proof-pivot-advisor` にエスカレーション。`Channel.toBlock` を
     `Kernel.mk` + `fun x => Measure.pi (fun i => W (x i))` の直接定義に **再定義** すれば
     `toBlock_compProd_pi_factor` が definitional に近づき、ボトルネック解消。§H-1 撤退ライン
     の発動 (Phase 2 で 30 行越えなく避けていた measurability proof) を **後追い的に発動** する
     形になる。試算: measurability ~30-50 行追加、bridge facts ~30-50 行、両側 ~100-150 行
     合計 ~150-250 行で Phase 4-α 0 sorry 到達見込み。

2. **2026-05-18 実装 (Session 1)**: Phase 0〜3 + Phase 4-β 完了 / Phase 4-α は 1 sorry 残し。
   - Phase 0: 確認結果 — `ProbabilityTheory.Kernel.pi` Mathlib 不在 (loogle / rg 双方 0 件),
     `Subadditive.tendsto_lim` Mathlib 在 (`Mathlib/Analysis/Subadditive.lean:87`,
     hypothesis: `BddBelow (range fun n => u n / n)`).
   - Phase 1: skeleton 80 行で Write, LSP silent (sorry warning のみ).
   - Phase 2: `Channel.toBlock` を **`Kernel.prod` + `Kernel.comap` + `Kernel.map` の inductive
     recursion** で構成 (`piFinSuccAbove 0` を使った `Fin (n+1) → α ≃ᵐ α × (Fin n → α)` 分解,
     ~15 行)。`Measure.pi` の直接 lift は measurability 補題が Mathlib 不在のため断念し、
     再帰版を採用。Markov instance は `Kernel.IsMarkovKernel.map` + `infer_instance` の 2 行で
     auto-derive。撤退ライン §H-1 非発動 (30 行未満)。
   - Phase 3: `capacityN W n : ℝ≥0∞ = sSup ((p ↦ mutualInfoOfChannel p (W n)) ''
     { p | IsProbabilityMeasure p })`, `capacity_lim W : ℝ = Filter.atTop.limUnder ...`,
     `capacityN_nonneg = bot_le` で完了。
   - Phase 4-β: `capacity_lim_eq_capacity_of_memoryless` を Phase 4-α を仮定して完成。
     `(capacityN (ofMemoryless W) n).toReal = n * capacity W` for `n ≥ 1` から
     `(...).toReal / n = capacity W` の eventually-const 経由で `tendsto_const_nhds.congr'`
     → `Tendsto.limUnder_eq`。Fekete 不要 (memoryless の場合 sequence が constant)、
     §C-5 / §H-2 撤退ライン非発動。
   - Phase 4-α: **1 sorry 残**。`(ofMemoryless W).capacityN n = ENNReal.ofReal (n * capacity W)`。
     次セッション持ち越し。`mutualInfo_iid_eq_nsmul` (6 仮説) + IID input の `Measure.pi` 構成
     から `≥`, `mutualInfo_le_sum_per_letter_of_memoryless_strong` から `≤`。
   - Phase 5: regression check 9 ファイル + 全 library build (`lake build InformationTheory`) silent.
   - 採用形は計画通り (C-1 候補 A 関数形)。Subadditive 自作不要。最大の発見:
     `Measure.pi` の measurability 補題が Mathlib 不在 → inductive recursion 経路が正解。

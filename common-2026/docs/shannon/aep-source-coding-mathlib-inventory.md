# Shannon: AEP Phase D (源符号化定理 weak converse) Mathlib インベントリ サブ計画

> **Parent**: [`aep-source-coding-plan.md`](aep-source-coding-plan.md) §Phase 0
>
> 親 inventory: [`aep-mathlib-inventory.md`](aep-mathlib-inventory.md) (AEP Phase A〜C 用、6 軸)
>
> 本 inventory はその **delta** に絞る。Phase A〜C で確定済みの
> `strong_law_ae_real` / `IdentDistrib` / `pmfLog` 周辺 plumbing は再記載しない。
> Phase D で **新たに必要 / 親で未確定** の 5 軸のみを以下に記録。
>
> Track 3 (Stein converse) の inventory [`stein-converse-mathlib-inventory.md`](stein-converse-mathlib-inventory.md)
> の軸 4 (`Tendsto` squeeze API) は本 plan の軸 4 (`Filter.liminf` API) と直接重なるため
> 同所からの再利用ポインタを記載する。

<!--
雛形メモ: CLAUDE.md「Subagent Inventory of Mathlib Lemmas」規約に従う
- file:line / 完全署名 / 引数型 / 結論形 verbatim
- `[..]` プレリク鍵括弧は **必ず** verbatim 保持 (paraphrase 禁止)
- "無し" でも探索した query を記録 (negative grep / loogle 結果は資産)
-->

## 進捗

- [x] 軸 1: `Filter.liminf` API (`Tendsto.liminf_eq` / `le_liminf_of_le` 系)
- [x] 軸 2: i.i.d. 仮定の強化 (`iIndepFun` ↔ `Pairwise IndepFun` の関係 + `Measure.pi` 化)
- [x] 軸 3: Pi 化 entropy chain rule (`H(X^n) = n · H(X)` for i.i.d.)
- [x] 軸 4: ソース符号化 formalism (encoder/decoder/error rate predicate) の Mathlib 既存
- [x] 軸 5: 既存 Common2026 資産の再利用判定 (`shannon_converse_single_shot` 3 形 / `entropy_le_log_card` / Han chain rule)

## ゴール / Approach

AEP Phase D (源符号化定理 weak converse) 着手前に、5 軸で **新規自前構築量 vs Mathlib / Common2026 既存資産** を固定する。

**結論先取り**:

- **軸 1 (`Filter.liminf` API) は完備** ─ `Filter.Tendsto.liminf_eq` (`Mathlib/Topology/Order/LiminfLimsup.lean:196`)、`Filter.le_liminf_of_le` (`Mathlib/Order/LiminfLimsup.lean:145`)、`Filter.liminf_le_liminf` (`:205`)、`liminf_const` (`:289`) で **「`∀ᶠ n, log M_n / n ≥ H(X) − δ_n` + `δ_n → 0` ⟹ `liminf ≥ H(X)`」** の組成は 20〜40 行 plumbing で書ける。Mathlib の薄さは無し。
- **軸 2 (i.i.d. 強化) は確認必須の判断点** ─ AEP Phase A〜C は `Pairwise IndepFun` で済んでいる (強法則がそれだけで動く) が、Phase D の `H(X^n) = n · H(X)` は **真の (mutual) 独立性 = `iIndepFun`** が必要。Mathlib に `Pairwise IndepFun → iIndepFun` 一般変換は **不在** (Pairwise は弱い)。したがって **Phase D は `iIndepFun` 仮定を Phase A〜C と独立に追加で受ける** 設計。
- **軸 3 (Pi 化 entropy chain rule) は 完全不在** ─ `entropy μ (jointRV Xs n) = n · entropy μ (Xs 0)` 形は Common2026 にも Mathlib にも無し。Han `jointEntropy_chain_rule` は `H(X_0,...,X_{n-1}) = ∑ H(X_i | prefix)` を提供するが、i.i.d. への閉じ込みには **`condEntropy_eq_entropy_of_indepFun`** (1 段補題、自前 30〜50 行) を別途要する。あるいは Stein の `klDiv_pi_eq_n_smul` と平行な induction を直接書く (40〜80 行)。
- **軸 4 (ソース符号化 formalism) は 完全不在** ─ encoder `c : (Fin n → α) → Fin M`、decoder `d : Fin M → (Fin n → α)`、error rate `μ {ω | d (c (X^n ω)) ≠ X^n ω}` は **すべて自前で書き下す**。既存の `MeasureFano.errorProb` は `decoder : Y → X` 形なので、`X^n` の自己復号にそのまま `Yo := c ∘ X^n` で当てはめられる。`SourceCode` 構造体は導入せず、Phase D では **直接 `c`, `d`, `Pe_n` を引数で渡す** 形 (Slepian–Wolf converse の流儀と一致)。
- **軸 5 (既存資産の再利用判定)** ─ `shannon_converse_single_shot` は **uniform `Msg` 仮定** で立っており、X^n は uniform でないため **直接呼べない**。したがって Phase D は `shannon_converse_single_shot` を **呼ばず**、その証明骨格 (`entropy = mutualInfo + condEntropy`、Fano、DPI、`entropy_le_log_card`) を `X^n` 上で **再演** する (= SlepianWolf converse の流儀)。再利用するのは **Phase 4-β bridge** (`mutualInfo_eq_entropy_sub_condEntropy`)、**`entropy_le_log_card`** (SlepianWolf.lean)、**`fano_inequality_measure_theoretic`** (Fano/Measure.lean)、**`mutualInfo_le_of_postprocess`** (DPI.lean) の 4 本。

---

## 軸 1: `Filter.liminf` API (`Tendsto → liminf_eq`、`le_liminf_of_le`)

### `Filter.Tendsto.liminf_eq` (Tendsto から liminf 値を取り出す)

- **file:line**: `Mathlib/Topology/Order/LiminfLimsup.lean:196`
- **完全署名 verbatim**:
  ```lean
  theorem Filter.Tendsto.liminf_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
      (h : Tendsto u f (𝓝 a)) : liminf u f = a
  ```
- **`[..]` プレリク verbatim**: `[NeBot f]` (+ section: `[ConditionallyCompleteLinearOrder α]` `[TopologicalSpace α]` `[OrderTopology α]`)
- **本 plan での用途**: `δ_n → 0` の `Tendsto` を `liminf δ atTop = 0` に変換する補助 (Phase D の `entropy μ (Xs 0) - δ_n ≥ entropy μ (Xs 0)` への積み換え)。`atTop` は `NeBot` 自動。

### `Filter.le_liminf_of_le` (eventually 下界から liminf 下界へ)

- **file:line**: `Mathlib/Order/LiminfLimsup.lean:145`
- **完全署名 verbatim**:
  ```lean
  theorem le_liminf_of_le {f : Filter β} {u : β → α} {a}
      (hf : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
      (h : ∀ᶠ n in f, a ≤ u n) : a ≤ liminf u f
  ```
- **`[..]` プレリク verbatim**: namespace `Filter`、(+ section: `[ConditionallyCompleteLattice α]`)
- **本 plan での用途**: 「`∀ᶠ n in atTop, H − δ_n ≤ log M_n / n`」+「`H − δ_n → H`」+「`liminf (H − δ_n) atTop = H`」(Tendsto.liminf_eq) を組み合わせて **`H ≤ liminf (log M_n / n) atTop`** を直接出すか、または `liminf_le_liminf` を経由するかの 2 ルート。**主路線は `liminf_le_liminf` 経由 (下記)**。

### `Filter.liminf_le_liminf` (point-wise eventually から liminf monotone)

- **file:line**: `Mathlib/Order/LiminfLimsup.lean:205`
- **完全署名 verbatim**:
  ```lean
  theorem liminf_le_liminf {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
      (h : ∀ᶠ a in f, u a ≤ v a)
      (hu : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
      (hv : f.IsCoboundedUnder (· ≥ ·) v := by isBoundedDefault) :
      liminf u f ≤ liminf v f
  ```
- **`[..]` プレリク verbatim**: `[ConditionallyCompleteLattice β]` (+ namespace `Filter`)
- **本 plan での用途**: `∀ᶠ n in atTop, H − δ_n ≤ log M_n / n` ⟹ `liminf (fun n => H − δ_n) atTop ≤ liminf (fun n => log M_n / n) atTop`。LHS は `Tendsto (H − δ_n) atTop (𝓝 H)` から `Tendsto.liminf_eq` で `H` に潰す。

### `Filter.liminf_const` (定数の liminf)

- **file:line**: `Mathlib/Order/LiminfLimsup.lean:289` (`@[simp]`)
- **完全署名 verbatim**:
  ```lean
  @[simp]
  theorem liminf_const {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
      (b : β) : liminf (fun _ => b) f = b
  ```
- **`[..]` プレリク verbatim**: `[ConditionallyCompleteLattice β]` `[NeBot f]`
- **本 plan での用途**: 補助。Phase D 主路線では `Tendsto.liminf_eq` で代替可。

### Tendsto 構成補助 (Phase D で `δ_n → 0` を組むのに必要)

- **`Filter.Tendsto.div_const`** (`Mathlib/Topology/Algebra/GroupWithZero.lean` 周辺): `Tendsto u atTop (𝓝 a) → Tendsto (u / c) atTop (𝓝 (a / c))` (定数除算)
- **`Filter.tendsto_const_div_atTop_nhds_zero_nat`** / `tendsto_one_div_atTop_nhds_zero_nat`: `1/n → 0`、`c/n → 0`
- **`Filter.Tendsto.const_mul`** / `Filter.Tendsto.mul_const`: 定数倍
- **`Filter.Tendsto.add`** / `.sub`: 和/差
- **本 plan での用途**: `δ_n := (1 + Pe_n · n · log |α|) / n → 0` の組成。`Pe_n → 0` (仮定) + `1/n → 0` + `log |α|` 定数 で plumbing 4〜6 行。

### 結論

**`Filter.liminf` API は完備、自前補題は不要**。Phase D の liminf plumbing は `Tendsto.liminf_eq` + `liminf_le_liminf` + 標準 Tendsto algebra で 30〜50 行見積。Track 3 Stein converse の Phase C plumbing と同形 (向きが `liminf` vs `Tendsto squeeze` の差のみ)。

---

## 軸 2: i.i.d. 仮定の強化 — `iIndepFun` vs `Pairwise IndepFun`

### AEP Phase A〜C の現行仮定

- **`Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j`** (= 二元独立性のみ) + **`∀ i, IdentDistrib (Xs i) (Xs 0) μ μ`**
- 強法則 `strong_law_ae_real` (`Mathlib/Probability/StrongLaw.lean:598`) は **これだけで動く** (pairwise 独立で十分、Etemadi の SLLN 定理ライン)

### Phase D で必要となる強化

`H(X^n) = n · H(X)` を確立するには **mutual independence (`iIndepFun`)** が必要。これは:

```
iIndepFun (fun i (ω : Ω) => Xs i ω) μ
```

または同値の `iIndepFun (fun i => Xs i) μ` (Common2026 内の流儀に合わせる)。

### Mathlib に `Pairwise IndepFun → iIndepFun` 変換は 不在

- **rg**: `Pairwise.*iIndep|iIndep.*Pairwise|iIndepFun.*pairwise` in `Mathlib/Probability/Independence/` → 0 件
- **loogle**: `ProbabilityTheory.iIndepFun, Pairwise` → 0 件

**理由**: 一般に Pairwise 独立 ⊊ Mutual 独立 (Bernstein の counterexample)。よって変換補題は **存在し得ない**。Phase D は **新規仮定として `hindep_full : iIndepFun (fun i => Xs i) μ` を追加**する以外にない。

### Mathlib に既存の有用な逆向き補題

- **`ProbabilityTheory.iIndepFun.indepFun`** (`Mathlib/Probability/Independence/Basic.lean:447`):
  ```lean
  theorem iIndepFun.indepFun {β : ι → Type*}
      [m : ∀ x : ι, MeasurableSpace (β x)]
      {f : ∀ x : ι, Ω → β x} (hf_Indep : iIndepFun f μ) {i j : ι} (hij : i ≠ j) :
      IndepFun (f i) (f j) μ
  ```
  ─ `iIndepFun → Pairwise IndepFun` の自動 lift。**Phase D では `hindep_full` から AEP Phase B/C の `Pairwise IndepFun` を再構成**できる (Pairwise は条件として捨てられる)。

- **`ProbabilityTheory.iIndepFun.indepFun_finset`** (`Mathlib/Probability/Independence/Basic.lean:839`):
  ```lean
  lemma iIndepFun.indepFun_finset (S T : Finset ι) (hST : Disjoint S T) (hf_Indep : iIndepFun f μ)
      (hf_meas : ∀ i, Measurable (f i)) :
      IndepFun (fun a (i : S) => f i a) (fun a (i : T) => f i a) μ
  ```
  ─ **Disjoint Finset の積成分独立**。Phase D の `H(X_i | prefix) = H(X_i)` で `S = {i}`、`T = Finset.range i` (= `{0,...,i-1}`) に適用。**直接効く**。

- **`ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`** (`Mathlib/Probability/Independence/Basic.lean:706`):
  ```lean
  theorem iIndepFun_iff_map_fun_eq_pi_map [Fintype ι] {β : ι → Type*}
      {m : ∀ i, MeasurableSpace (β i)} {f : Π i, Ω → β i} [IsProbabilityMeasure μ]
      (hf : ∀ i, AEMeasurable (f i) μ) :
      iIndepFun f μ ↔ μ.map (fun ω i ↦ f i ω) = Measure.pi (fun i ↦ μ.map (f i))
  ```
  - **`[..]` プレリク verbatim**: `[Fintype ι]` `[IsProbabilityMeasure μ]`
  - **本 plan での用途**: 副次 (Phase D 主路線では使わない、`Measure.pi` への翻訳が必要なら使用可)

### Phase D 設計判断

- **判断**: Phase D の statement に **`hindep_full : iIndepFun (fun i => Xs i) μ` を追加仮定として受ける**。
- **副次効果**: `iIndepFun.indepFun` で AEP Phase A〜C の Pairwise 仮定は **自動派生** (caller が `hindep_full` だけ渡せば、Phase A〜C 補題への `hindep` は内部で `(fun i j hij => hindep_full.indepFun hij)` で生成)。**Phase D の caller 負担は Pairwise 1 本 → iIndepFun 1 本に置換のみ**。
- **後続 Phase E (achievability) も同様** (typicality 構成は Pi 形 `Measure.pi` を扱うので iIndepFun が自然)

### 結論

**Mathlib に Pairwise → iIndepFun 変換は存在しない**ので、Phase D は **iIndepFun を新規仮定として追加**する。逆向き (`iIndepFun.indepFun`) は完備で AEP Phase A〜C 補題への lift も自動。

---

## 軸 3: Pi 化 entropy chain rule (`H(X^n) = n · H(X)` for i.i.d.)

### Mathlib 不在 (negative confirmation)

- **rg**: `entropy.*Pi\.|entropy_pi|jointEntropy.*iid|entropy.*nsmul|entropy.*n_smul` in `Common2026/` and `.lake/packages/mathlib/` → 0 件 (Common2026 内に `klDiv_pi_eq_n_smul` (Stein converse 由来) はあるが entropy 版は無し)
- **loogle**: Common2026 内 `entropy` 系で `Pi` を含む補題は `entropy_measurableEquiv_comp` のみ (= reshape のみ、加法則無し)

**結論**: Pi 化 entropy chain rule は **完全不在**。自前構築。

### 構築素材

#### 既存 Common2026 補題

- **`InformationTheory.Shannon.jointEntropy_chain_rule`** (`Common2026/Shannon/Han.lean:56`):
  ```lean
  theorem jointEntropy_chain_rule
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
      jointEntropy μ Xs
        = ∑ i : Fin n,
            InformationTheory.MeasureFano.condEntropy μ (Xs i)
              (fun ω (j : Fin i.val) =>
                Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
  ```
  - **note**: `Fin n → Ω → α` indexing (= AEP の `ℕ → Ω → α` を `n` で truncate して使う)。i.i.d. では各 summand を `H(X_0)` に潰すのが目標

- **`InformationTheory.Shannon.entropy_pair_eq_entropy_add_condEntropy`** (`Common2026/Shannon/Entropy.lean:41`):
  ```lean
  theorem entropy_pair_eq_entropy_add_condEntropy
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : Ω → X) (Yo : Ω → Y)
      (hXs : Measurable Xs) (hYo : Measurable Yo) :
      entropy μ (fun ω => (Xs ω, Yo ω))
        = entropy μ Xs + InformationTheory.MeasureFano.condEntropy μ Yo Xs
  ```

#### Mathlib 既存補題

- **`ProbabilityTheory.iIndepFun.indepFun_finset`** (前述軸 2): 「`{i}` 単独」と「`Finset.range i.val`」の Disjoint 独立を導出
- **`ProbabilityTheory.IdentDistrib.comp`** (`Mathlib/Probability/IdentDistrib.lean:109`): `Xs i ~ Xs 0` から `entropy μ (Xs i) = entropy μ (Xs 0)` を導出 (`entropy_measurableEquiv_comp` か `IdentDistrib.entropy_eq` 系を要確認)

### Phase D 自前補題の見積

```lean
-- 補題 1 (新規): 独立条件付き ⇒ condEntropy = entropy
lemma condEntropy_eq_entropy_of_indepFun
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    (hindep : X ⟂ᵢ[μ] Y) :
    InformationTheory.MeasureFano.condEntropy μ X Y = entropy μ X
```

戦略: `mutualInfo_eq_entropy_sub_condEntropy μ X Y hX hY` + `mutualInfo_eq_zero_iff_indep` (`Common2026/Shannon/MutualInfo.lean:109`、両方向) で `mutualInfo = 0` → `condEntropy = entropy`。30〜50 行。

```lean
-- 補題 2 (新規): identDistrib ⇒ entropy 等
lemma entropy_eq_of_identDistrib
    (μ : Measure Ω) (X Y : Ω → α)
    (h : IdentDistrib X Y μ μ) :
    entropy μ X = entropy μ Y
```

戦略: `entropy μ X` の定義は `∑ x, negMulLog ((μ.map X).real {x})`、`IdentDistrib` から `μ.map X = μ.map Y`、点ごと書き換え。10〜20 行。**`IdentDistrib` から AEMeasurable しか出ないので `Measurable` 経由の補題は使えない可能性あり** → `entropy_measurableEquiv_comp` ではなく直接 `μ.map X = μ.map Y` を unfold する戦略が安全。

```lean
-- 主補題 (新規): i.i.d. block entropy = n · H(X)
theorem entropy_jointRV_eq_n_smul
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (n : ℕ) :
    entropy μ (jointRV Xs n) = (n : ℝ) * entropy μ (Xs 0)
```

戦略 (主路線):
1. `jointEntropy_chain_rule` の `Fin n` 版で `entropy μ (jointRV Xs n) = ∑ i : Fin n, condEntropy μ (Xs i) prefix_i` (= `jointEntropy μ Xs|_{Fin n}` を AEP の `jointRV` 形と同一視; `jointRV` の定義 `fun ω i => Xs i ω` と `jointEntropy` の `entropy μ (fun ω i => Xs i ω)` は defeq)
2. 各 summand: `condEntropy μ (Xs i) prefix_i = entropy μ (Xs i)` を補題 1 で (`Xs i ⟂ᵢ prefix_i` を `iIndepFun.indepFun_finset` で `S = {i}`, `T = Finset.range i` から導出)
3. `entropy μ (Xs i) = entropy μ (Xs 0)` を補題 2 で (`hident i`)
4. `∑ i : Fin n, entropy μ (Xs 0) = n · entropy μ (Xs 0)` (`Finset.sum_const` + `Finset.card_fin`)

**行数**: 補題 1 (30〜50 行) + 補題 2 (10〜20 行) + 主補題 (40〜80 行) = **80〜150 行**。シード見積 300〜500 行のうち最大ブロック。

**リスク**:
- `prefix_i` の Pi 値の型 (`Fin i.val → α`) と `iIndepFun.indepFun_finset` の `(i : Finset.range i) → Ω → α` 形の型整合 ─ `Finset.range` vs `Fin` の reshape が薄い `MeasurableEquiv` で済むか、自前 funext が要るか
- `IdentDistrib.entropy_eq` (補題 2) の plumbing 量 ─ `μ.map X = μ.map Y` から entropy 等は素直だが、`AEMeasurable` のみで `Measurable` がない場合、`entropy_measurableEquiv_comp` 経路は不可、unfold 直撃

---

## 軸 4: ソース符号化 formalism (encoder / decoder / error rate)

### Mathlib 不在 (negative confirmation)

- **rg**: `SourceCode|sourceCoding|source_coding|encoder.*decoder` in `Mathlib/InformationTheory/` → 0 件
- **rg**: `SourceCode|sourceCoding` in `.lake/packages/mathlib/` → 0 件 (情報源符号化の formalism は Mathlib に皆無)

### 既存 Common2026 / 親 inventory での近似形

- **`InformationTheory.MeasureFano.errorProb`** (`Common2026/Fano/Measure.lean:73`):
  ```lean
  def errorProb (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X) : ℝ
  ```
  ─ 定義: `μ {ω | decoder (Yo ω) ≠ Xs ω}` (`.real` で実数化)。**ソース符号化の `Pe_n` にそのまま流用可**: `Xs := jointRV Xs n`、`Yo := c n ∘ jointRV Xs n`、`decoder := d n` で `errorProb μ (jointRV Xs n) (c n ∘ jointRV Xs n) (d n) = μ {ω | d n (c n (jointRV Xs n ω)) ≠ jointRV Xs n ω}`

### 設計判断

**`SourceCode` 構造体は導入しない**。Phase D の statement は以下の引数形 (Slepian–Wolf converse 流儀):

```lean
theorem source_coding_converse
    {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] [DecidableEq α] [Nonempty α]
                  [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (M : ℕ → ℕ) (hM_pos : ∀ n, 0 < M n)
    (c : ∀ n, (Fin n → α) → Fin (M n))
    (d : ∀ n, Fin (M n) → (Fin n → α))
    (hPe_to_zero :
      Tendsto (fun n => InformationTheory.MeasureFano.errorProb μ
                          (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
              atTop (𝓝 0))
    (hcard : 2 ≤ Fintype.card α) :
    entropy μ (Xs 0)
      ≤ Filter.liminf (fun n : ℕ => Real.log (M n : ℝ) / n) atTop
```

**理由**:
- 既存 `errorProb` を直接呼べる (`SourceCode` ラッパーは plumbing コスト + 命名衝突リスク)
- caller 側も Cover-Thomas の natural definition と読みやすい
- **`c n`, `d n` の measurability は自動派生** (`Fin (M n)` も `Fin n → α` も Fintype + MeasurableSingletonClass、`measurable_of_countable` で 1 行)

**判定**: ソース符号化 formalism は **新規導入物ゼロ、既存 `errorProb` を引数形で受ける**。

---

## 軸 5: 既存 Common2026 資産の再利用判定

### `shannon_converse_single_shot` (3 形)

- **file:line**: `Common2026/Shannon/Converse.lean:81` (基本) / `:141` (injective encoder) / `:207` (Markov encoder)
- **共通仮定**: **`hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count`** (= `Msg` が uniform on `M`)
- **判定**: **直接呼べない**。`X^n` の分布は `(μ.map (Xs 0))^⊗ⁿ` で、一般には **uniform でない** (Xs 0 が uniform でなければ)。この uniform 仮定は `entropy_of_uniform_msg` で `entropy μ Msg = log |M|` を使うため取り外し不可。
- **代替 (再利用範囲)**: 3 つの `shannon_converse_single_shot` は **使わず**、それらの **証明骨格** (Fano + DPI + bridge) を `X^n` 上で再演する。再演に必要な部品は以下 4 本、**すべて既存**:

### 再演に再利用する 4 部品

#### `entropy_le_log_card` (SlepianWolf.lean)

- **file:line**: `Common2026/Shannon/SlepianWolf.lean:45`
- **完全署名 verbatim**:
  ```lean
  theorem entropy_le_log_card
      {Ω : Type*} [MeasurableSpace Ω]
      {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
        [MeasurableSpace α] [MeasurableSingletonClass α]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : Ω → α) (hXs : Measurable Xs) :
      entropy μ Xs ≤ Real.log (Fintype.card α)
  ```
- **`[..]` プレリク verbatim**: `[MeasurableSpace Ω]` `[Fintype α]` `[DecidableEq α]` `[Nonempty α]` `[MeasurableSpace α]` `[MeasurableSingletonClass α]` `[IsProbabilityMeasure μ]`
- **本 plan での用途**: `H(c n ∘ X^n) ≤ log (M n)` ─ `c n ∘ X^n : Ω → Fin (M n)` で適用、`Fintype.card (Fin (M n)) = M n` (`Fintype.card_fin`)。**Slepian–Wolf converse とまったく同じ使い方**。

#### `mutualInfo_eq_entropy_sub_condEntropy` (Bridge.lean)

- **file:line**: `Common2026/Shannon/Bridge.lean:579`
- **本 plan での用途**: `H(X^n) = I(X^n; Z) + H(X^n | Z)` の bridge (`Z = c n ∘ X^n` または `Z = d n ∘ c n ∘ X^n`)

#### `mutualInfo_le_of_postprocess` (DPI.lean)

- **file:line**: `Common2026/Shannon/DPI.lean:139`
- **本 plan での用途**: `I(X^n; d (c (X^n))) ≤ I(X^n; c (X^n))` ─ deterministic decoder = postprocess

#### `fano_inequality_measure_theoretic` (Fano/Measure.lean)

- **file:line**: `Common2026/Fano/Measure.lean:224`
- **完全署名 verbatim**:
  ```lean
  theorem fano_inequality_measure_theoretic
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X)
      (hXs : Measurable Xs) (hYo : Measurable Yo) (hdec : Measurable decoder)
      (hcard : 2 ≤ Fintype.card X) :
      condEntropy μ Xs Yo ≤
        Real.binEntropy (errorProb μ Xs Yo decoder)
          + errorProb μ Xs Yo decoder * Real.log ((Fintype.card X : ℝ) - 1)
  ```
- **`[..]` プレリク verbatim** (上の section variable + 引数):
  - `[Ω : Type*]` `[MeasurableSpace Ω]` (section)
  - `[X : Type*]` `[Fintype X]` `[DecidableEq X]` `[Nonempty X]` `[MeasurableSpace X]` `[MeasurableSingletonClass X]` (section)
  - `[Y : Type*]` `[MeasurableSpace Y]` (section)
  - `[IsProbabilityMeasure μ]`
- **本 plan での用途**: `X := Fin n → α` (Pi 値、`Fintype.card (Fin n → α) = (Fintype.card α)^n`)、`Y := Fin (M n)`、`decoder := d n` で適用。**Fintype + MeasurableSingletonClass の自動 derive 確認 (Han Phase D の前例より GO 見込み)**。`hcard : 2 ≤ (Fintype.card α)^n` は `n ≥ 1` + `2 ≤ Fintype.card α` から `2 ≤ 2^n ≤ |α|^n` で導出 (5〜10 行 plumbing)、**`n = 0` は Phase D の主張が trivial (LHS = 0) なので別ケースで処理**

### 結論

**Phase D の主証明骨格は 4 部品の組成 + 軸 3 の n·H(X) + 軸 1 の liminf 化**。`shannon_converse_single_shot` 直接呼びは不可だが、その骨格は本 project 内に **すでに存在**しており再演コストは小さい。Slepian–Wolf converse の流儀 (4 step assembly + Fano) と完全に並行。

---

## 結論サマリ (各軸 1 行)

| 軸 | 結論 | Phase 影響 |
|---|---|---|
| 1 `Filter.liminf` | **Mathlib 完備** (`Filter.Tendsto.liminf_eq` / `liminf_le_liminf` / `liminf_const`) | Phase D 終段 plumbing 30〜50 行 |
| 2 i.i.d. 強化 | **Pairwise → iIndepFun 変換は不可** (Bernstein counterexample)、Phase D は `iIndepFun` 仮定を新規追加 | Phase D 入口の statement 変更、caller 側仮定形のみ影響 |
| 3 Pi 化 entropy | **完全不在**、自前 80〜150 行 (補題 1: condEntropy=entropy of indep + 補題 2: identDistrib entropy + 主補題: induction or 直接 `jointEntropy_chain_rule` 経由) | Phase D の山場 1 |
| 4 ソース符号化 formalism | **既存 `errorProb` を直接利用**、`SourceCode` 構造体は不要 | 新規定義ゼロ、引数形で受ける |
| 5 既存資産 (4 部品) | **`entropy_le_log_card` / `mutualInfo_eq_entropy_sub_condEntropy` / `mutualInfo_le_of_postprocess` / `fano_inequality_measure_theoretic` の 4 本で骨格再演可**、`shannon_converse_single_shot` は uniform 仮定により直接呼び不可 | Phase D 中段 plumbing は Slepian–Wolf converse (`SlepianWolf.lean`) と同形 |

---

## Phase D 着手判定

**GO**:

- 唯一の **不確実性** は **軸 3 (Pi 化 entropy chain rule の自前 80〜150 行)**。これは Phase D 内の独立補題として skeleton-driven で書ける (依存補題が明確)
- 軸 2 で `iIndepFun` 仮定を追加することは Phase A〜C の Pairwise 仮定と矛盾せず (`iIndepFun.indepFun` で自動 lift)
- 軸 4 (ソース符号化 formalism) は新規導入ゼロ、軸 5 (既存資産) は 4 部品すべて公開
- 全体として **新規 plumbing は entropy 化 chain rule (1 本) + ソース符号化 converse 主定理 (1 本)**、残りは既存資産の組成

## Definition of Done (本 inventory)

- [x] 5 軸全て調査完了
- [x] `Filter.Tendsto.liminf_eq` / `Filter.le_liminf_of_le` / `Filter.liminf_le_liminf` / `liminf_const` の verbatim 署名 + `[..]` プレリク確定
- [x] `iIndepFun.indepFun` / `iIndepFun.indepFun_finset` / `iIndepFun_iff_map_fun_eq_pi_map` の verbatim 署名確定、Pairwise → iIndepFun 不可を裏取り
- [x] Pi 化 entropy chain rule (`H(X^n) = n · H(X)`) は Common2026 / Mathlib 共に不在を裏取り
- [x] ソース符号化 formalism (encoder / decoder / error rate) は Mathlib 不在を裏取り、既存 `errorProb` 流用方針確定
- [x] `shannon_converse_single_shot` は uniform 仮定により直接呼び不可、骨格再演に必要な 4 部品 (`entropy_le_log_card` / `mutualInfo_eq_entropy_sub_condEntropy` / `mutualInfo_le_of_postprocess` / `fano_inequality_measure_theoretic`) の verbatim 署名確認済
- [x] Phase D skeleton (`Common2026/Shannon/AEP.lean` 末尾 append、または `Common2026/Shannon/SourceCoding.lean` 新ファイル) が書ける状態

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 本 inventory はまだ起草段階。本体着手で発見があれば追記。 -->

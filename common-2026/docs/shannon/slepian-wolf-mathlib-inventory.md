# Slepian–Wolf: Mathlib インベントリ サブ計画 (Phase 0)

> **Parent**: [`slepian-wolf-moonshot-plan.md`](slepian-wolf-moonshot-plan.md) §Phase 0
>
> **Status (2026-05-10):** 起草。loogle index (`.lake/build/loogle.index`) + Mathlib / InformationTheory 直 grep
> でホットスポット 5 軸を機械的に確認。各候補補題は **CLAUDE.md「Subagent Inventory of
> Mathlib Lemmas」規約** (位置 / 完全シグネチャ / 引数 / 結論形 / 使い所) に従って記録する。

## 進捗

- [x] 軸 1: `shannon_converse_single_shot` 既存形 + `δ(ε)` 取り扱い ✅
- [x] 軸 2: side info 入り Fano (paired conditioner ルート) ✅
- [x] 軸 3: chain rule (`H(X,Y) = H(X) + H(Y|X)`) 既存補題 ✅
- [x] 軸 4: encoder 形式 (`e : X → Fin M`) と `entropy_le_log_card` 系 ✅
- [x] 軸 5: 二者ペア確率変数の plumbing (`Measure.prod` / `condDistrib_fst_prod` 系) ✅

## ゴール / Approach

5 軸の調査結果を **Phase A skeleton (`InformationTheory/Shannon/SlepianWolf.lean` の sorry-driven 出だし) が書ける状態** に持っていく。各軸で「Mathlib にあるか / ないか / 既存補題で代用可」の 1 行結論 + 採用する具体補題シグネチャを verbatim 記録。

## 結論サマリ

| 軸 | 結果 | Phase A〜C への影響 |
|---|---|---|
| (1) `shannon_converse_single_shot` 既存 | uniform `Msg` 前提の formulation。Slepian–Wolf は **直流用しない**。chain rule + Fano の組み立てを **新規に行う** | Phase B で converse 全体を書き下す。既存定理は参考のみ |
| (2) side info 入り Fano | **新規補題不要**。既存 `fano_inequality_measure_theoretic` の `Yo` を `(Yo, sideInfo) : Ω → Y × S` で呼ぶだけで成立 | Phase A は thin wrapper 1 本のみ (~10〜15 行) |
| (3) chain rule | 2 変数版 `entropy_pair_eq_entropy_add_condEntropy` ✅、`condEntropy_le_condEntropy_of_pair` ✅ ともに `InformationTheory/Shannon/Entropy.lean` 既存 | そのまま流用 |
| (4) encoder + log-card | `entropy_le_log_image_card` は uniform 専用、**任意 μ 形は不在**。一般「`H(W) ≤ log Fintype.card`」を新規補題で立てる必要あり | Phase A で 30〜50 行の新規補題追加 |
| (5) ペア plumbing | `Measure.map_prod_map`、`condDistrib_fst_prod` 等 Mathlib 完備、`Measurable.prodMk` で paired RV 作成 | plumbing コストは小、~10 行レベル |

---

## 軸 1: `shannon_converse_single_shot` 既存形

### 結論 (1 行)

**既存 `shannon_converse_single_shot` は `Msg` uniform を要求するため、Slepian–Wolf converse へは直接転用できない。Phase B で chain rule + side info Fano を組み合わせて新規に書き下す。**

### 採用候補

#### `InformationTheory.Shannon.shannon_converse_single_shot`
- **位置**: `InformationTheory/Shannon/Converse.lean:81`
- **完全シグネチャ**:
  ```lean
  theorem shannon_converse_single_shot
      {Ω : Type*} [MeasurableSpace Ω]
      {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
        [MeasurableSpace M] [MeasurableSingletonClass M]
      {Y : Type*} [MeasurableSpace Y]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Msg : Ω → M) (Yo : Ω → Y) (decoder : Y → M)
      (hMsg : Measurable Msg) (hYo : Measurable Yo) (hdecoder : Measurable decoder)
      (hMsg_uniform :
        μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
      (hcard : 2 ≤ Fintype.card M)
      (hMI_finite : mutualInfo μ Msg Yo ≠ ∞) :
      Real.log (Fintype.card M) ≤
        (mutualInfo μ Msg Yo).toReal +
          Real.binEntropy
            (InformationTheory.MeasureFano.errorProb μ Msg Yo decoder) +
          InformationTheory.MeasureFano.errorProb μ Msg Yo decoder *
            Real.log ((Fintype.card M : ℝ) - 1)
  ```
- **引数 (順)**: `Msg`, `Yo`, `decoder` + 3 measurability + `hMsg_uniform` (uniform 仮定) + `hcard` + `hMI_finite`
- **結論形** (verbatim): `Real.log (Fintype.card M) ≤ (mutualInfo μ Msg Yo).toReal + Real.binEntropy (errorProb …) + errorProb … * Real.log ((Fintype.card M : ℝ) - 1)`
- **使い所**: Slepian–Wolf には **直接呼ばない**。理由: Slepian–Wolf の source `(Xs, Ys)` は uniform を仮定しないため `hMsg_uniform` が立たない。代わりに同型の論法 (entropy → MI/Fano 分解) を side info 入りで再演する

#### `δ(ε) := h(ε) + ε · log(|X| - 1)` の取り扱い

- 本 project では `δ` を独立の関数で導入していない。`shannon_converse_single_shot` は RHS に `Real.binEntropy Pe + Pe * Real.log ((Fintype.card M : ℝ) - 1)` を **inline** で書いている
- Slepian–Wolf でも同形式で 3 bound を表現する方針 (`δ` 関数を新設しない)。`|X × Y| - 1` で書くため alphabet sizes は `Fintype.card (X × Y) - 1 = Fintype.card X * Fintype.card Y - 1` を `Fintype.card_prod` で展開して使う
- alphabet `(X × Y)` の `Fintype` instance は `Prod.fintype` で自動

### Phase 影響

Phase B は **既存 `shannon_converse_single_shot` を写経しない**。`fano_inequality_measure_theoretic` を side info 形で 3 回 (X bound / Y bound / 合計 bound) 呼ぶ流儀に切り替え。**3 bound を 1 statement にまとめるか別 theorem にするかは Phase B 着手時に判断**、ただし inventory 段階の予測は「3 別 theorem + 共通 lemma 1 本」が plumbing 量最小。

---

## 軸 2: side info 入り Fano

### 結論 (1 行)

**新規補題不要。既存 `fano_inequality_measure_theoretic` を `Yo := (Yo, sideInfo) : Ω → Y × S`、`decoder : Y × S → X` で呼ぶだけで成立。Phase A の側 info Fano は thin wrapper 1 本 (~15 行)。**

### 採用候補

#### `InformationTheory.MeasureFano.fano_inequality_measure_theoretic`
- **位置**: `InformationTheory/Fano/Measure.lean:224`
- **完全シグネチャ**:
  ```lean
  theorem fano_inequality_measure_theoretic
      {Ω : Type*} [MeasurableSpace Ω]
      {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
        [MeasurableSpace X] [MeasurableSingletonClass X]
      {Y : Type*} [MeasurableSpace Y]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X)
      (hXs : Measurable Xs) (hYo : Measurable Yo) (hdec : Measurable decoder)
      (hcard : 2 ≤ Fintype.card X) :
      condEntropy μ Xs Yo ≤
        Real.binEntropy (errorProb μ Xs Yo decoder)
          + errorProb μ Xs Yo decoder * Real.log ((Fintype.card X : ℝ) - 1)
  ```
- **引数 (順)**: `Xs`, `Yo`, `decoder` + 3 measurability + `hcard`
- **結論形** (verbatim): `condEntropy μ Xs Yo ≤ Real.binEntropy (errorProb …) + errorProb … * Real.log ((Fintype.card X : ℝ) - 1)`
- **使い所**: side info `S` 入り Fano は `Yo' := fun ω => (Yo ω, sideInfo ω) : Ω → Y × S`、`decoder' : Y × S → X` でこの定理をそのまま呼ぶ。`Y` は型 class 上「任意の `MeasurableSpace`」なので `Y × S` でも適用可。`Y × S` の `MeasurableSpace` は自動 derive

### 設計判断: paired conditioner ルート vs 独立 lemma

候補 (i): `(Yo, sideInfo)` で paired RV にして既存定理を呼ぶ ─ **採用**
候補 (ii): 別 lemma `fano_inequality_with_side_info μ Xs Yo Si decoder` を立てる ─ **却下**

採用理由:
- (i) は 0 新規補題 + thin wrapper のみ。既存テンプレ流用最大化
- (ii) は signature が 2 個に増えるが内容は (i) と同型 (paired type を unfold するだけ)。重複コスト > 抽象化メリット
- 利用側 (Slepian–Wolf 主定理 3 本) は decoder 引数を `decoder : Fin Mx × Fin My → X × Y` で受けるので、conditioner 型と decoder 入力型を揃える必要がある。`Yo' := (eX∘Xs, eY∘Ys)` の形が自然

ただし **Phase A wrapper として `fano_inequality_with_side_info` を 1 本書く価値はある** — 利用側の signature が読みやすくなる + Slepian–Wolf の 3 bound 全部で同じ wrapper を呼べる

### `errorProb` 既存形

#### `InformationTheory.MeasureFano.errorProb`
- **位置**: `InformationTheory/Fano/Measure.lean:73`
- **完全シグネチャ**:
  ```lean
  def errorProb (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X) : ℝ :=
    μ.real {ω | Xs ω ≠ decoder (Yo ω)}
  ```
- **使い所**: Slepian–Wolf の `Pe = μ {ω | (Xs ω, Ys ω) ≠ decoder (eX (Xs ω), eY (Ys ω))}` をこの `errorProb` の形で書く。`Xs := fun ω => (Xs ω, Ys ω) : Ω → X × Y`、`Yo := fun ω => (eX (Xs ω), eY (Ys ω))`、`decoder` はそのまま

### Phase 影響

Phase A の `fano_inequality_with_side_info` wrapper を 15〜20 行で書く。Phase B はこの wrapper を 3 回呼ぶ。

---

## 軸 3: chain rule + conditioning monotonicity

### 結論 (1 行)

**既存 `InformationTheory/Shannon/Entropy.lean` の `entropy_pair_eq_entropy_add_condEntropy` + `condEntropy_le_condEntropy_of_pair` でカバー。新規補題不要。**

### 採用候補

#### `InformationTheory.Shannon.entropy_pair_eq_entropy_add_condEntropy`
- **位置**: `InformationTheory/Shannon/Entropy.lean:41`
- **完全シグネチャ**:
  ```lean
  theorem entropy_pair_eq_entropy_add_condEntropy
      {Ω : Type*} [MeasurableSpace Ω]
      {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
        [MeasurableSpace X] [MeasurableSingletonClass X]
      {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
        [MeasurableSpace Y] [MeasurableSingletonClass Y]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : Ω → X) (Yo : Ω → Y)
      (hXs : Measurable Xs) (hYo : Measurable Yo) :
      entropy μ (fun ω => (Xs ω, Yo ω))
        = entropy μ Xs + InformationTheory.MeasureFano.condEntropy μ Yo Xs
  ```
- **引数**: `Xs`, `Yo` + 2 measurability
- **結論形**: `entropy μ (Xs, Yo) = entropy μ Xs + condEntropy μ Yo Xs`
- **使い所**: Slepian–Wolf 主定理で `H(Xs, Ys) = H(Ys) + H(Xs | Ys) = H(Xs) + H(Ys | Xs)` の両形式をこの定理 1 本から取り出す

#### `InformationTheory.Shannon.condEntropy_le_condEntropy_of_pair`
- **位置**: `InformationTheory/Shannon/Entropy.lean:240`
- **完全シグネチャ**:
  ```lean
  theorem condEntropy_le_condEntropy_of_pair
      {Ω : Type*} [MeasurableSpace Ω]
      {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
        [MeasurableSpace X] [MeasurableSingletonClass X]
      {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
        [MeasurableSpace Y] [MeasurableSingletonClass Y]
      {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
        [MeasurableSpace Z] [MeasurableSingletonClass Z]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
      (hXs : Measurable Xs) (hYo : Measurable Yo) (hZo : Measurable Zo) :
      InformationTheory.MeasureFano.condEntropy μ Xs (fun ω => (Yo ω, Zo ω))
        ≤ InformationTheory.MeasureFano.condEntropy μ Xs Yo
  ```
- **引数**: `Xs`, `Yo`, `Zo` + 3 measurability
- **結論形**: `H(Xs | Yo, Zo) ≤ H(Xs | Yo)`
- **使い所**: Slepian–Wolf の「conditioning が増えるとエントロピーは減る」を直接適用。例: `H(Xs | eY∘Ys) ≥ H(Xs | eY∘Ys, Ys)` (= `H(Xs | Ys, eY∘Ys)` を `eY∘Ys` だけに条件付け)

### 制限事項 (採用時の注意)

- `condEntropy_le_condEntropy_of_pair` は **`Y, Z` ともに Fintype** を要求。これは Slepian–Wolf の文脈で `Fin Mx`, `Fin My`, `A`, `B` が全部 Fintype なので問題なし
- ただし conditioner の **順序** に注意 — `(Yo, Zo)` の `Yo` が monotone で残るほうの引数。Slepian–Wolf で「`H(Xs | Ys, eY∘Ys)` を `H(Xs | Ys)` に上から押さえる」場合は `Yo := Ys`, `Zo := eY∘Ys` でこの定理を呼ぶ

### Phase 影響

Phase B で chain rule を 2〜3 回、conditioning monotonicity を 2〜3 回呼ぶ想定。新規補題不要。

---

## 軸 4: encoder 形式 + `entropy_le_log_card`

### 結論 (1 行)

**`entropy μ (e ∘ Xs) ≤ log (Fintype.card (Fin M))` の任意 μ 版は Mathlib・InformationTheory 両方に不在。Phase A で 30〜50 行の新規補題として立てる必要あり。** Loomis–Whitney の `entropy_le_log_image_card` は uniform 専用で代用不可。

### 必要となる補題 (新規)

```lean
/-- Any random variable on a finite alphabet has entropy bounded by `log (Fintype.card)`. -/
theorem entropy_le_log_card
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → α) (hXs : Measurable Xs) :
    entropy μ Xs ≤ Real.log (Fintype.card α)
```

### 証明戦略 (新規)

`entropy μ Xs = ∑ x, negMulLog (μ.map Xs).real {x}` を `negMulLog` の凹性 (`Real.strictConcaveOn_negMulLog` あるいは Jensen) で `negMulLog (∑ x, p_x / N) · N = log N` 形に押し上げる。具体的には:

```
entropy μ Xs = -∑ p_x log p_x
            ≤ -log (∑ p_x · (1 / Fintype.card)) · 1  -- 反転 Jensen (negMulLog 凸性 → log の凹性)
            = -log (1 / Fintype.card)
            = log (Fintype.card)
```

代替ルート (より素直): **Gibbs 不等式** `KL(P ‖ Q_uniform) ≥ 0` から `H(P) ≤ log |support|`。`klDiv (μ.map Xs) (Fintype.card α)⁻¹ • Measure.count ≥ 0` を展開して `entropy μ Xs ≤ log (Fintype.card α)`。`klDiv_nonneg` ([`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`]) を使えば 30 行程度。

### 既存材料 (採用候補)

#### `InformationTheory.Shannon.entropy_le_log_image_card` (uniform 専用、代用不可)
- **位置**: `InformationTheory/Shannon/LoomisWhitney.lean:125`
- **完全シグネチャ**:
  ```lean
  theorem entropy_le_log_image_card
      {β γ : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
        [MeasurableSpace β] [MeasurableSingletonClass β]
      [Fintype γ] [DecidableEq γ] [Nonempty γ]
        [MeasurableSpace γ] [MeasurableSingletonClass γ]
      {A : Finset β} (hA : A.Nonempty)
      (f : β → γ) (hf : Measurable f) :
      entropy (uniformOn (A : Set β)) f ≤ Real.log (A.image f).card
  ```
- **使い所**: uniform `μ` 専用なので Slepian–Wolf には **代用不可**。ただし証明戦略 (Gibbs の負エントロピー上界) は同じので、`entropy_le_log_card` の証明で参考にする
- 注意: uniform 形式 `μ.map Xs ≤ |α|⁻¹ • Measure.count` が成り立つので、loomis-whitney の証明の **uniform 仮定を外す** 段だけが追加コスト。`klDiv` 経由なら `IsProbabilityMeasure (μ.map Xs)` だけで `klDiv (μ.map Xs) (uniform on α) ≥ 0` から自動

### Phase 影響

**Phase A で `entropy_le_log_card` を 30〜50 行で立てる**。Slepian–Wolf 主定理 3 本のうち 2 本 (X bound, Y bound) で `log Mx ≥ H(eX ∘ Xs)` の形でこの補題を呼ぶ。3 本目 (sum bound) はペア encoder 出力 `(eX ∘ Xs, eY ∘ Ys) : Ω → Fin Mx × Fin My` に同じ補題を適用。

---

## 軸 5: 二者ペア確率変数の plumbing

### 結論 (1 行)

**Mathlib 完備。`Measurable.prodMk` で paired RV を作り、`Measure.map_prod_map` でペア push-forward を分解、`Fintype.card_prod` で alphabet size を展開。新規補題不要。**

### 採用候補

#### `Measurable.prodMk`
- **位置**: `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean` (Mathlib core)
- **完全シグネチャ**:
  ```lean
  theorem Measurable.prodMk {f : α → β} {g : α → γ}
      (hf : Measurable f) (hg : Measurable g) :
      Measurable fun a => (f a, g a)
  ```
- **使い所**: Slepian–Wolf で `fun ω => (Xs ω, Ys ω) : Ω → X × Y`、`fun ω => (eX (Xs ω), eY (Ys ω)) : Ω → Fin Mx × Fin My` の measurability を 1 行で取る

#### `MeasureTheory.Measure.map_prod_map`
- **位置**: `Mathlib/MeasureTheory/Measure/Prod.lean:825`
- **完全シグネチャ**:
  ```lean
  theorem map_prod_map {δ} [MeasurableSpace δ]
      {f : α → β} {g : γ → δ} (μa : Measure α) (μc : Measure γ)
      [SFinite μa] [SFinite μc]
      (hf : Measurable f) (hg : Measurable g) :
      (map f μa).prod (map g μc) = map (Prod.map f g) (μa.prod μc)
  ```
- **引数**: `μa`, `μc` + `[SFinite μa] [SFinite μc]` + 2 measurability
- **結論形**: `(μa.map f).prod (μc.map g) = (μa.prod μc).map (Prod.map f g)`
- **使い所**: encoder push-forward を独立成分に分解する場面で有効 (今回の Slepian–Wolf 直接定理証明では使わなくても可、ただし MI plumbing で出る可能性あり)

#### `ProbabilityTheory.condDistrib_fst_prod` / `condDistrib_snd_prod`
- **位置**: `Mathlib/Probability/Kernel/CondDistrib.lean:225` / `:237`
- **完全シグネチャ**:
  ```lean
  lemma condDistrib_fst_prod {γ : Type*} {mγ : MeasurableSpace γ}
      (X : α → β) (hY : AEMeasurable Y μ) (ν : Measure γ) [IsProbabilityMeasure ν] :
      condDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) (μ.prod ν) =ᵐ[μ.map X] condDistrib Y X μ
  ```
- **使い所**: 直接 Slepian–Wolf の主定理証明では呼ばない見込み。side info Fano で conditioner pair を分解する場合に 1 段あると便利だが、上記 paired conditioner ルート (軸 2) で **不要**

#### `Fintype.card_prod`
- **位置**: `Mathlib/Data/Fintype/Prod.lean` (Mathlib core)
- **完全シグネチャ**:
  ```lean
  @[simp] theorem Fintype.card_prod (α β : Type*) [Fintype α] [Fintype β] :
      Fintype.card (α × β) = Fintype.card α * Fintype.card β
  ```
- **使い所**: Slepian–Wolf の 3 本目 (sum bound) で `log (|X × Y| - 1) = log (|X| · |Y| - 1)` の整形

### Phase 影響

軸 5 関係の plumbing は **既存 API 流用のみ**、新規補題ゼロ。Phase B で `Measurable.prodMk` を 4〜5 回、`Fintype.card_prod` を 1〜2 回呼ぶ想定。

---

## 工数感 (Phase 0 後の見立て)

| Phase | 当初見積 (seed) | Phase 0 後の見立て | 差分 |
|---|---|---|---|
| Phase 0 (M0) | 1 ターン | 完了 (1 ターン) | 計画通り |
| Phase A (side info Fano + entropy_le_log_card) | 不確実 | 1〜2 セッション (~80〜120 行) | wrapper 軽い + entropy_le_log_card 30〜50 行 + 細かい helper |
| Phase B (3 bound, X / Y / sum) | 不確実 | 2〜3 セッション (~150〜250 行) | 1 本目 (X bound) を写経 + 2 本目 (Y bound) は対称 (~30 行) + 3 本目 (sum bound) は chain rule で展開 (~80 行) |
| Phase C (3 bound 統合 + publish 形整理) | 不確実 | 1 セッション (~50〜80 行) | 1 statement にまとめるか 3 別 theorem は判断保留、いずれにせよ wrapper 級 |

**累計**: **~280〜450 行 / 4〜6 セッション (実質 2 週間以内)**。シードの「2〜3 週間 / 400〜600 行」より **下方修正** (側 info Fano が paired conditioner で済むため + chain rule 既存補題流用)。

ただし Phase B 着手時に「3 bound を 1 statement にまとめるか」の formulation 設計に **追加 1 セッション** 必要になる可能性あり (記事化価値の調整含む)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

# LZ78 M3 achievability 壁 (`ziv_aseventual_le_blockLogAvg₂`) のための構造化在庫

> 対象壁: `ziv_aseventual_le_blockLogAvg₂`
> (`InformationTheory/Shannon/LZ78/GreedyParsingImpl.lean:557`, `@residual(wall:lz78-aseventual-ziv)`)
> 親計画: [`lz78-m2-plan.md`](lz78-m2-plan.md) (route A) / [`lz78-ziv-treenode-plan.md`](lz78-ziv-treenode-plan.md) (route B) / roadmap [`lz78-completion-roadmap.md`](lz78-completion-roadmap.md) M3
> 本ファイルは **在庫専任**。plan 作成・実装はしない。
>
> 全数値・consumer 数・loogle Found 0 は本セッション機械裏取り (loogle index `2026-06-05` ビルド / `dep_consumers.sh` / verbatim Read)。

## 一行サマリ

**M3 achievability の壁を組むのに必要な API のうち「素材レイヤ」(packing / log-sum / convexity / Finset grouping / SMB-in-bits / `-log Pₙ` 接続) は ~85% が既存** (Mathlib + in-project sorryAx-free)。**未充足は 3 種** — (1) `c·log c ≤ ∑(per-group entropy) + o(n)` の grouping 不等式そのもの (genuine missing core, codebase + Mathlib 不在), (2) per-group sub-distribution の **fixed-tuple parametrize 版** (現 `condPhraseProb` は観測 `ω` 依存に固定されており route B が要求する node-context 横断形ではない), (3) **max phrase length = O(log n)** lemma (route A の #groups=O(log n) に必須、未存在)。**在庫ベースの route 確定: route A (length-grouping) が既存資産で組みやすく、route B (node-grouping) は D3 trap (overhead `c·log c` 非vanish) が実際に殺す** (下記 §総合所見、機械裏取り)。

---

## 壁の最終形 (再掲)

```lean
theorem ziv_aseventual_le_blockLogAvg₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n => (lz78GreedyImplEncodingLength n
          (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ)) Filter.atTop
      ≤ Filter.limsup (fun n => blockLogAvg₂ μ p.toStationaryProcess n ω) Filter.atTop
```

証明戦略 (pseudo-Lean, route A = length-grouping):

```
filter_upwards [a.s. 正質量 regularity hPn]                        -- ∀ᵐ ω
gateway: lz/n ≤ (c·log c)/(log2·n) + overhead(n)                  -- Phase 1 ✅ sorryAx-free
genuine core (★): c·log c ≤ -log Pₙ + o(n)  =  n·blockLogAvg·log2  -- M3 missing core
  分解: phrase を 長さ ℓ 別 group → 同じ ℓ の distinct phrase ≤ |α|^ℓ 個
        per-length sub-distribution → log-sum (log_sum_inequality) を -log Pₙ に直接乗せる
overhead → 0: overhead = c·log(maxlen)/n, maxlen=O(log n), c=O(n/log n)  -- (c·log log n)/n → 0
limsup 合成: Filter.limsup_le_limsup で err(n)→0 を吸収               -- ∀ᶠ n の per-n 比較
```

(route B = node-grouping は §総合所見で在庫ベースに殺される。)

---

## §A — per-group sub-distribution の素材 (measure-theoretic 核)

旧名 (`extendCylinder` / `extendCylinder_measureReal_sum_eq` / `extendCylinder_pairwiseDisjoint` / `iUnion_extendCylinder` / `condNextSymbol_sum_eq_one`) は **全て obsolete = 現行 codebase に存在しない** (rg 0-hit、本セッション)。現行の対応物は `condPhraseProb` 系 (path-prefix ratio 形) のみ。**fixed-tuple `v` parametrize 版の sub-distribution `∑_a P(prefix·a) = P(prefix)` は存在しない** (`condNextSymbol_sum_eq_one` の対応 decl 不在)。

| 概念 | 現行 file:line | verbatim signature (`[...]` 込み) | 結論形 verbatim | consumer | route |
|---|---|---|---|---|---|
| per-phrase 条件付き確率 (path-prefix ratio, **`ω` 依存固定**) | `ZivEntropyBridge.lean:167` | `noncomputable def condPhraseProb (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) (j : ℕ) : ℝ` | `prefixBlockProb μ p ω (parsingBoundary μ p n ω (j + 1)) / prefixBlockProb μ p ω (parsingBoundary μ p n ω j)` | 3 (内部のみ: telescope/factor/neg_log_ge_sum) | A/B 両方の素材だが node 横断不可 |
| prefix block 確率 | `ZivEntropyBridge.lean:150` | `noncomputable def prefixBlockProb (μ : Measure Ω) (p : StationaryProcess μ α) (ω : Ω) (m : ℕ) : ℝ` | `(μ.map (p.blockRV m)).real {p.blockRV m ω}` | — | A/B |
| prefix monotonicity (sub-distribution 核の代替) | `Kernel.lean:134` | `theorem prefixBlockProb_antitone (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (ω : Ω) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :` | `prefixBlockProb μ p ω m₂ ≤ prefixBlockProb μ p ω m₁` | (telescope chain 内部) | A/B (`Pₙ ≤ ∏ qⱼ` の核) |
| telescoping | `Kernel.lean:75` | `theorem prod_condPhraseProb_telescope (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) (c : ℕ) (hpos : ∀ j ≤ c, prefixBlockProb μ p ω (parsingBoundary μ p n ω j) ≠ 0) :` | `∏ j ∈ Finset.range c, condPhraseProb μ p n ω j = prefixBlockProb μ p ω (parsingBoundary μ p n ω c)` | (factor 内部) | B (tree-node telescoping) |
| `Pₙ ≤ ∏ qⱼ` factorization | `Kernel.lean:179` | `theorem blockProb_le_prod_condPhraseProb (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) (hpos : ∀ j ≤ (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length, prefixBlockProb μ p ω (parsingBoundary μ p n ω j) ≠ 0) :` | `(μ.map (p.blockRV n)).real {p.blockRV n ω} ≤ ∏ j ∈ Finset.range (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length, condPhraseProb μ p n ω j` | **0** (dead-start) | B 路の上端 |
| `∑ⱼ -log qⱼ ≤ -log Pₙ` (path-prefix 加法 log) | `ZivEntropyBridge.lean:229` | `theorem blockProb_neg_log_ge_sum (μ : Measure Ω) (p : StationaryProcess μ α) (h : IsLZ78PerPathParsingFactorization μ p) (n : ℕ) (ω : Ω) (hPn : 0 < (μ.map (p.blockRV n)).real {p.blockRV n ω}) :` | `∑ j ∈ Finset.range (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length, - Real.log (condPhraseProb μ p n ω j) ≤ - Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})` | **0** (dead-start, D4) | B 路の素材 (D4 trap) |
| `n·blockLogAvg = -log Pₙ` (Ziv chain 消費形) | `ZivEntropyBridge.lean:126` | `theorem blockLogAvg_eq_neg_log_blockProb (μ : Measure Ω) (p : StationaryProcess μ α) {n : ℕ} (hn : 0 < n) (ω : Ω) :` | `(n : ℝ) * blockLogAvg μ p n ω = - Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})` | — | **A/B 両方 (target 接続点)** |

**重要 finding (§A)**:

1. **`condPhraseProb` は観測 `ω` 依存に固定**。signature `(μ, p, n, ω, j)` で固定 tuple `v` で parametrize できない。各 `j` は「観測 path の `j` 番目 boundary における prefix ratio」であって、node-context 横断 (同一 node の異なる child を集約する) 形ではない。→ **route B (node-grouping) が要求する「per-node sub-distribution `∑_a q(node·a|node) ≤ 1`」を現 `condPhraseProb` から直接は取り出せない** (`condPhraseProb` は path-prefix ratio で、telescoping すると `∏ = prefixBlockProb` になり、`∑qⱼ≈1` ではなく `∑qⱼ≈c`)。
2. **`blockProb_le_prod_condPhraseProb` (route B 上端) は 0 consumers = dead-start**。`blockProb_neg_log_ge_sum` (D4 path-prefix log) も **0 consumers** (本セッション `dep_consumers.sh` 機械裏取り)。両者とも握るのは `∑ⱼ -log qⱼ ≤ -log Pₙ` であって、missing core の `c·log c ≤ ∑ⱼ -log qⱼ + o(n)` ではない (D4 `∑qⱼ≈c` trap)。
3. **`isLZ78PerPathParsingFactorization_of_pos` は phantom**: `ZivEntropyBridge.lean` / `Kernel.lean` docstring が複数箇所参照しているが、**decl として存在しない** (rg 0-hit、本セッション)。route B が「positivity から factorization を構築」する際にこの constructor が要るが未実装 (= self-build 要、route B コストに加算)。
4. **A/B 共通の target 接続点 = `blockLogAvg_eq_neg_log_blockProb`** (`ZivEntropyBridge.lean:126`)。`-log Pₙ = n·blockLogAvg` を `blockLogAvg₂ = blockLogAvg/log 2` (`GreedyParsingImpl.lean:502`) に乗せる橋。これは存在し sorryAx-free。

---

## §B — log-sum + convexity (grouping 組立の核)

| 概念 | 現行 file:line | verbatim signature (`[...]` 込み) | 結論形 verbatim | 状態 | route |
|---|---|---|---|---|---|
| **log-sum 不等式 (finite, in-project)** | `ZivEntropyBridge.lean:71` | `theorem log_sum_inequality {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :` | `(∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤ ∑ i ∈ s, a i * Real.log (a i / b i)` | ✅ sorryAx-free | **A/B 両方の grouping log-sum 核** |
| `x·log x` の凸性 | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:144` | `lemma Real.convexOn_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x)` | `ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x)` | ✅ 既存 | A/B (`log_sum_inequality` の中で既使用) |
| 凸 Jensen (Finset.sum 版) | `Mathlib/Analysis/Convex/Jensen.lean:67` | `theorem ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :` <br> `[...]`: `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 E] [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]` | `f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i)` | ✅ 既存 | A/B (`log_sum_inequality` の中で既使用) |
| 凹 Jensen (Finset.sum 版) | `Mathlib/Analysis/Convex/Jensen.lean:73` | `theorem ConcaveOn.le_map_sum (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :` (同 `[...]`) | `(∑ i ∈ t, w i • f (p i)) ≤ f (∑ i ∈ t, w i • p i)` | ✅ 既存 | バックアップ |

**finding (§B)**: `Real.convexOn_xlogx` / `ConvexOn.inner_smul_le_map_sum` は **loogle unknown identifier (= 不在)**。正しい正式名は `Real.convexOn_mul_log` (`NegMulLog.lean:144`) と `ConvexOn.map_sum_le` (`Jensen.lean:67`)。`Real.add_pow_le_pow_mul_pow_of_sq_le_sq` / `inner_le_nnorm` 系の誤ヒット懸念は無関係 — **`∑ pᵢ log pᵢ` 形の log-sum は in-project `log_sum_inequality` が既に sorryAx-free で握っている** (Mathlib の生 Jensen を直接叩く必要なし)。grouping 不等式 (`c log c ≤ ∑_g c_g log c_g + c log(#groups)`) を出すには `log_sum_inequality` を **group 集合に 1 回適用** する (`aᵢ ≡ c_g`, `bᵢ ≡ 1`)。

---

## §C — Ziv counting / packing template + c=O(n/log n)

| 概念 | 現行 file:line | verbatim signature (`[...]` 込み) | 結論形 verbatim | consumer | route |
|---|---|---|---|---|---|
| length-stratification 単射 (packing template の核) | `ZivCountingBody.lean:81` | `def toOptTuple (L : ℕ) (w : List α) : Fin (L + 1) → Option α` | `fun i => w[(i : ℕ)]?` | — | **A (length-group packing template)** |
| 同じ長さ ≤L の distinct string は ≤ `(|α|+1)^(L+1)` 個 | `ZivCountingBody.lean:111` | `theorem card_short_le (ws : List (List α)) (hnodup : ws.Nodup) (hlen : ∀ w ∈ ws, w.length ≤ L) :` <br> section `[Fintype α]` | `ws.length ≤ (Fintype.card α + 1) ^ (L + 1)` | — | **A (「同じ ℓ の distinct phrase ≤ |α|^ℓ」を握る既存核)** |
| nat-level packing | `ZivCountingBody.lean:138` | `theorem packing_nat (ws : List (List α)) (hnodup : ws.Nodup) (L : ℕ) :` <br> section `[Fintype α] [Nonempty α]` | `(L + 1) * (ws.length - (Fintype.card α + 1) ^ (L + 1)) ≤ (ws.map List.length).sum` | — | A |
| **packing 核 `c·log c ≤ 8·log(|α|+1)·T`** | `ZivCountingBody.lean:190` | `theorem total_length_ge_count_mul_log (ws : List (List α)) (hnodup : ws.Nodup) (hne : ∀ w ∈ ws, w ≠ []) :` <br> section `[Fintype α] [Nonempty α]` | `(ws.length : ℝ) * Real.log (ws.length : ℝ) ≤ 8 * Real.log (Fintype.card α + 1) * ((ws.map List.length).sum : ℝ)` | 1 (`lz78PhraseStrings_mul_log_le`) | A (length-group packing の証明済 template) |
| 文字列ファミリ版 `c·log c ≤ K·n` | `ZivCountingBody.lean:357` | `theorem lz78PhraseStrings_mul_log_le [Nonempty α] (input : List α) :` | `((lz78PhraseStrings input).length : ℝ) * Real.log ((lz78PhraseStrings input).length : ℝ) ≤ 8 * Real.log (Fintype.card α + 1) * (input.length : ℝ)` | 2 (`lz78_impl_rate_le_const`, `_of_length`) | A/B (gateway 経由で既使用) |
| `c = O(n/log n)` (envelope) | `ZivCountingBody.lean:410` | `theorem lz78PhraseStrings_count_isBigO (input : ℕ → List α) (hlen : ∀ n, (input n).length = n) :` <br> section `[Fintype α] [DecidableEq α] [Nonempty α]` | `(fun n => ((lz78PhraseStrings (input n)).length : ℝ)) =O[atTop] (fun n => (n : ℝ) / Real.log (n : ℝ))` | — | **A/B (overhead → 0 の分母、envelope = `n/Real.log n`)** |

**finding (§C)**:

1. **`total_length_ge_count_mul_log` の packing 証明は「同じ長さの distinct phrase は高々 `(|α|+1)^(L+1)` 個」(`card_short_le`、length-stratification `toOptTuple`) を直接使う** — これは **length-grouping packing の証明済 template そのもの**。route A の Step 2a (length-grouped packing) は `total_length_ge_count_mul_log` の packing を「長さ別 entropy 形」に拡張する形で、既存資産を流用できる (`card_short_le` が長さ別 group の cardinality 上界を握る)。
2. envelope は **`n/Real.log n`** (verbatim 確認、`lz78PhraseStrings_count_isBigO`)。`(c·log log n)/n = O((log log n)/log n) → 0` の overhead vanish は `c = O(n/log n)` から従う。
3. **max phrase length = O(log n) lemma は存在しない** (rg `max.*length`/`maxLength`/`maximal phrase` 0-hit、本セッション)。route A の #groups = O(log n) (= maxlen の bound) に必須。**self-build 要**。ただし `card_short_le` の対偶 (「長さ `> L` の phrase が存在 → `(|α|+1)^(L+1) ≤` total count」)、または `(|α|+1)^maxlen ≤ phrase count ≤ n` から `maxlen ≤ log_{|α|+1} n` を出すのは中規模 (既存 `card_short_le` + `Nat.log` API で組める見込み)。

---

## §D — Finset grouping API (二重和)

全て Mathlib に存在 (loogle 全 hit)。`sum_*` は `prod_*` から `@[to_additive]` 生成 (source の verbatim を併記)。

| 概念 | 現行 file:line | verbatim signature (additive / source prod, `[...]` 込み) | 結論形 verbatim | route |
|---|---|---|---|---|
| 単射像上の和 | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:95` (source `prod_image`) | `theorem prod_image [DecidableEq ι] {s : Finset κ} {g : κ → ι} : Set.InjOn g s → ∏ x ∈ s.image g, f x = ∏ x ∈ s, f (g x)` <br> section `[CommMonoid M] {f g : ι → M}` | (additive) `∑ x ∈ s.image g, f x = ∑ x ∈ s, f (g x)` (InjOn 前提) | A/B (phrase→length or node の像へ) |
| fiberwise 和 (maps_to) | `Basic.lean:255` (source `prod_fiberwise_of_maps_to`) | `lemma prod_fiberwise_of_maps_to {g : ι → κ} (h : ∀ i ∈ s, g i ∈ t) (f : ι → M) :` <br> section `[DecidableEq κ] [CommMonoid M]` | `∏ j ∈ t, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s, f i` (additive: `∑ j ∈ t, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i`) | **A/B (二重和: phrase を group key で fiber 化)** |
| card の fiberwise 分解 | `Basic.lean:979` | `theorem card_eq_sum_card_fiberwise [DecidableEq M] {f : ι → M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t) :` | `#s = ∑ b ∈ t, #{a ∈ s | f a = b}` | A/B (#group ごとの member count) |
| card の image-fiber 分解 | `Basic.lean:983` (`card_eq_sum_card_image`) | `theorem card_eq_sum_card_image [DecidableEq M] (f : ι → M) (s : Finset ι) :` | `#s = ∑ b ∈ s.image f, #{a ∈ s | f a = b}` | A/B |
| sigma 和 | `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` | `Finset.sum_sigma` (loogle 確認、Sigma.lean 由来) | (dependent 二重和) | A/B (length 別 group の入れ子) |

**finding (§D)**: 二重和変換 (phrase を (length) / (length,state) / node でグルーピング) の Finset API は **完備**。route A は `c = #phrases = ∑_ℓ #{phrase | length = ℓ}` を `card_eq_sum_card_fiberwise` (group key = `List.length`) で分解し、`prod_fiberwise_of_maps_to`/`sum_fiberwise_of_maps_to` で `∑ phrase f = ∑_ℓ ∑_{phrase: len=ℓ} f` に展開する。これは plumbing 級 (既存 API、self-build 不要)。

---

## §E — worker 不変条件の抽出可否 (route B のみ必要、判定材料)

worker `lz78PhraseStringsAux` (`GreedyLongestPrefix.lean:77`) を精読した結果:

| 不変条件 | 現状 | route B での要否 |
|---|---|---|
| `dict.Nodup` 保存 | ✅ lemma `lz78PhraseStringsAux_nodup` (`GreedyLongestPrefix.lean:104`) | A/B 両方 (既存) |
| emit phrase 非空 | ✅ lemma `lz78PhraseStringsAux_forall_ne_nil` (`:209`) → `lz78PhraseStrings_forall_ne_nil` (`:231`) | A/B (既存) |
| 総長 ≤ input.length | ✅ `lz78PhraseStringsAux_total_length` (`:151`) → `lz78PhraseStrings_total_length_le` (`:191`) | A/B (既存) |
| count ≤ n | ✅ `lz78PhraseStrings_count_le` (`:261`) | A/B (既存) |
| **emit 時 `cur ∈ dict` (parent context が dict に居る)** | ❌ **docstring (`:69`, `:73`) にのみ「Invariant maintained」と書かれているが、lemma として証明されていない** | **B 必須 (T1 の parent-prefix 抽出の核)** |
| **phrase `w = cur ++ [s]` の `cur = w.dropLast` が emit 時 dict に居る** | ❌ **不在** (`lz78PhraseStringsAux_emit_dropLast_mem` 系 0-hit、`dropLast.*mem`/`cur.*dict` の lemma 無し) | **B 必須** |
| node-context / treeNode モデル | ❌ **不在** (`nodeContext`/`treeNode`/per-node sub-distribution 0-hit) | B 必須 |

**finding (§E、定性評価)**: route B が要求する「phrase `w = cur ++ [s]` の `cur` (= parent context) が emit 時の dict に居る不変条件」は、**現 worker 定義から原理的には取り出せる** (worker は `if w ∈ dict then grow else emit` で、emit 直前の `cur` は前ステップで `cur ∈ dict` を guard で通過しているか `cur = []`)。ただし:

1. **その不変条件は現在 lemma 化されていない** (docstring の prose のみ)。worker は `cur` を引数として再帰で持ち回るので、`lz78PhraseStringsAux_nodup` と同型の帰納で「`cur ∈ dict ∨ cur = []`」を補題化することは可能だが、**reset 後の `cur = []` から次の emit までに `cur` を再構築する path を追う必要があり、`Nodup` 証明より重い** (worker は `cur ++ [s]` を test するが、`cur` 自体が前回 emit された entry である保証は guard の連鎖を辿らないと取れない)。
2. 取り出せたとしても、**per-node sub-distribution `∑_a q(node·a|node) ≤ 1` (T2 crux) と node-context telescoping (T4) は別途 measure-theoretic に self-build** が要る (現 `condPhraseProb` は path-prefix ratio で node 横断形でない、§A finding 1)。
3. **総合判定: route B = 「worker 不変条件の lemma 化 (中規模) + per-node sub-distribution (T2 crux, 大規模 measure-theoretic) + node-context telescoping (T4) + `isLZ78PerPathParsingFactorization_of_pos` 実装 + headline 再配線」で大規模化。** route A が要求しない node-context 基盤を丸ごと建てる必要がある。

---

## Key-preconditions box (事故りやすい前提)

- **`ziv_aseventual_le_blockLogAvg₂` の `0 < Pₙ` (observed cylinder 正質量)**: `blockProb_neg_log_ge_sum` / `blockLogAvg_eq_neg_log_blockProb` 経由で `-log Pₙ` を扱う全 path が `0 < Pₙ` を要求 (`hPn` / `field_simp`)。これは **a.s. regularity** (`∀ᵐ ω` の中で供給)。per-block `∀ω` では成立しない (`Pₙ = 0` の null set がある)。
- **`ConvexOn.map_sum_le` の weight 正規化 `∑ w i = 1`**: log-sum 適用時、weights は `bᵢ/(∑b)` 形にして `∑ = 1` を満たす (in-project `log_sum_inequality` が既に処理済 — Mathlib Jensen を直接叩かず `log_sum_inequality` を使えばこの前提は隠蔽される)。
- **per-block 形 (`∀n∀ω`) は FALSE** (D1: 反例 `a^16`, c=5, -log Pₙ=0; D2: overhead 定数版も `Pₙ→1` family で FALSE)。**limsup 形で o(n) を吸収して初めて成立** — clean `c·log c ≤ -log Pₙ` (∀n∀ω) や定数 overhead 付き (∀n∀ω) を書いた瞬間に即撤退。
- **`Filter.limsup_le_limsup` (`Mathlib/Order/LiminfLimsup.lean:198`) の cobounded/bounded witness**: `[ConditionallyCompleteLattice β]`、引数 `(hu : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)` / `(hv : f.IsBoundedUnder (· ≤ ·) v := by isBoundedDefault)` は autoparam だが、`atTop` + 非自明列で発火しないことがある。witness = `lz78_impl_rate_le_const` (上界) + `per_symbol_nonneg` (下界)、headline `h_bdd_above` の実証手法を流用。

---

## Elements that need self-building (優先度順)

1. **genuine core (★) `c·log c ≤ -log Pₙ + o(n)` の grouping 不等式** (route A: length-grouping)
   - 推奨実装: phrase を `List.length` で fiber 化 (`card_eq_sum_card_fiberwise` / `sum_fiberwise_of_maps_to`) → 各長さ ℓ group に per-length sub-distribution → `log_sum_inequality` (`ZivEntropyBridge.lean:71`) を group 集合に適用 → `-log Pₙ = n·blockLogAvg` (`blockLogAvg_eq_neg_log_blockProb`) に **直接** 乗せる (`∑qⱼ` path-prefix を経由しない、D4 trap 回避)。
   - 工数感: **最大の難所 (genuine novel, codebase + Mathlib 不在)**。`total_length_ge_count_mul_log` の length-stratification packing (`card_short_le`) が証明済 template になるが、「packing (count 上界)」から「entropy 形 (`∑ -log q`)」への橋は新規。m2-plan の見積りで「single in-session plan では閉じない genuine research-level scope」。
   - 地雷: per-block 形にしない (D1/D2)。`∑qⱼ` path-prefix route (D4 `∑qⱼ≈c` trap) を経由しない。
2. **max phrase length = O(log n) lemma** (route A の #groups=O(log n) に必須)
   - 推奨実装: `card_short_le` の対偶 + `(|α|+1)^maxlen ≤ (lz78PhraseStrings input).length ≤ n` から `maxlen ≤ Nat.log (|α|+1) n`。
   - 工数感: 中規模 (既存 `card_short_le` + `Nat.log` API で組める)。
3. **overhead → 0 の合成** (`(c·log(maxlen))/n → 0`)
   - 推奨実装: max phrase length (上 2) + `c = O(n/log n)` (`lz78PhraseStrings_count_isBigO`, envelope `n/Real.log n`) → `O((log log n)/log n) → 0`。
   - 工数感: 中規模 (Asymptotics API 流用、~30–60 行)。
4. **limsup 合成** (`Filter.limsup_le_limsup` + err(n)→0 吸収)
   - 工数感: 低〜中 (~20–40 行、cobounded/bounded witness は headline 流用)。
5. **(route B を選ぶ場合のみ) node-context 基盤一式**: worker 不変条件 lemma 化 (§E) + per-node sub-distribution (T2 crux) + node-context telescoping (T4) + `isLZ78PerPathParsingFactorization_of_pos` 実装 (§A finding 3、phantom 解消)。
   - 工数感: **大規模** (route A の数倍、measure-theoretic node 基盤を丸ごと新設)。

---

## Enumeration of Mathlib walls (`@residual(wall:...)` targets)

| wall | loogle confirmation | 判定 |
|---|---|---|
| LZ78 / Lempel-Ziv 漸近最適性 (Mathlib 不在) | `loogle "\"Lempel\""` → `Found 0 declarations whose name contains "Lempel"`。`"Ziv"` の 4 hit は `Int.erdos_ginzburg_ziv` 系 (Erdős–Ginzburg–Ziv、無関係) | **genuine wall** (Mathlib に LZ78 系一切なし) |
| 可変深さ length-grouping AEP `c·log c ≤ ∑(per-group entropy) + o(n)` | `loogle "?c * Real.log ?c ≤ Finset.sum _ _"` → `Of these, 0 match your pattern(s)` (Real×log×Finset.sum 6 decl 中 0 match) | **genuine missing core** (codebase + Mathlib 不在、= 壁 `lz78-aseventual-ziv` の核) |
| limsup over per-symbol rate の AEP bridge | `loogle "Filter.limsup (fun _ => _ / _), Real.log"` → `Found 0 declarations`; `loogle "Filter.limsup, Nat.log"` → `Found 0 declarations` | **genuine wall** (Mathlib 不在) |

**shared sorry-lemma 推奨**: `ziv_aseventual_le_blockLogAvg₂` の壁は **既に単一の sorry に集約済** (`GreedyParsingImpl.lean:557`、`@residual(wall:lz78-aseventual-ziv)`)。`lz78GreedyImpl_achievability_ae` (`:637`) は `shannon_mcmillan_breiman₂` (sorryAx-free) + `ziv_aseventual_le_blockLogAvg₂` の合成で **body は sorry-free** (W1/W2 decomposition、`876bcd0`)。よって **wall は 1 箇所のみで散在していない** — これ以上の consolidation は不要 (新たな shared sorry lemma の追加は逆に冗長)。D4 path-prefix の `blockProb_neg_log_ge_sum` (0 consumers) は壁の核ではない dead-start なので、これを shared lemma 化する必要もない。

---

## 距離 — 親計画の撤退ライン (発動 yes/no)

親計画 ([`lz78-m2-plan.md`](lz78-m2-plan.md)) の撤退ライン:

> **Phase 2 (length-grouping log-sum 核 2a/2b) が通らない** → `ziv_aseventual_le_blockLogAvg₂` を `sorry` + `@residual(wall:lz78-aseventual-ziv)` 維持

**判定: 既に発動済 (leg 3, commit `7171707`)**。本在庫はこの判定を **覆さない** (= 在庫ベースでも genuine 壁を確認):

- 本在庫の機械裏取り (loogle Found 0 × 3 / `c·log c ≤ ∑` grouping AEP の 0 match / `blockProb_neg_log_ge_sum` 0 consumers) は m2-plan leg 3 の「Phase 2b = single in-session plan で閉じない genuine research-level 壁」を **再確認** する。
- gateway (Phase 1 = `lz78_impl_bitrate_le_clogc_plus_overhead`, sorryAx-free) は GO のままで「gateway 不通」撤退条件には該当しない。
- **ripple ゼロ (機械裏取り)**: `ziv_aseventual_le_blockLogAvg₂` の direct consumer は `lz78GreedyImpl_achievability_ae` 1 decl (同 file、statement 依存のみ)。W2 body を埋めるだけで signature 不変 → 配線変更不要。

**現状の撤退 exit は honest (tier 2)**: `sorry` + `@residual(wall:lz78-aseventual-ziv)`、hypothesis bundling なし、signature は source data (`μ`, `p`) + `[IsProbabilityMeasure μ]` regularity のみ。**新たな degenerate fallback の追加は不要** (既存 exit が正しい retreat 形)。在庫は「壁を縮退させる degenerate boundary」ではなく「route A が route B より既存資産で組みやすい」という攻略 path 選定材料を供給する。

---

## Starting skeleton (route A での攻略開始点)

`ziv_aseventual_le_blockLogAvg₂` の body を埋める方向の skeleton (signature 不変、helper を sorry で stub):

```lean
-- InformationTheory/Shannon/LZ78/GreedyParsingImpl.lean (既存 file への追補)
-- imports は既存 (ZivEntropyBridge / ZivCountingBody / Stationary.Kernel / Mathlib.Order.LiminfLimsup
--   / Mathlib.Analysis.Convex.Jensen は ZivEntropyBridge 経由で取得済)

namespace InformationTheory.Shannon
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace Ω]

/-- (self-build 1) max phrase length = O(log n): `(|α|+1)^maxlen ≤ c ≤ n` から. -/
theorem lz78_maxPhraseLength_le_log
    (input : List α) :
    -- maxlen = (lz78PhraseStrings input).map List.length |>.maximum 形
    True := by sorry  -- @residual(wall:lz78-aseventual-ziv)

/-- (self-build 2, genuine core ★) length-grouping `c·log c ≤ -log Pₙ + o(n)`,
    a.s.-eventual + overhead 項込みの per-n 形 (per-block 形 D1/D2 は FALSE). -/
theorem lz78_clogc_le_neg_log_blockProb_aseventual
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ((lz78PhraseStrings (List.ofFn (p.toStationaryProcess.blockRV n ω))).length : ℝ)
          * Real.log (_ : ℝ) / (Real.log 2 * n)
        ≤ blockLogAvg₂ μ p.toStationaryProcess n ω + _err_n := by
  sorry  -- @residual(wall:lz78-aseventual-ziv) — length-grouping AEP (codebase+Mathlib 不在)

-- 既存 (body を上の 2 + gateway + Filter.limsup_le_limsup で組む):
theorem ziv_aseventual_le_blockLogAvg₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n => (lz78GreedyImplEncodingLength n
          (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ)) Filter.atTop
      ≤ Filter.limsup
          (fun n => blockLogAvg₂ μ p.toStationaryProcess n ω) Filter.atTop := by
  sorry  -- @residual(wall:lz78-aseventual-ziv)

end InformationTheory.Shannon
```

---

## 総合所見 — route A vs route B (在庫ベース、機械裏取り)

**route A (length / (length,state)-grouping) が既存資産で組みやすく、route B (node-grouping) は D3 trap (overhead 非vanish) が実際に殺す。** 在庫ベースの根拠 (憶測でなく):

- **route A の素材は揃っている**: length-grouping packing の証明済 template (`total_length_ge_count_mul_log` が `card_short_le` の length-stratification を直接使用、§C finding 1)、log-sum 核 (`log_sum_inequality` sorryAx-free、§B)、二重和 Finset API 完備 (`card_eq_sum_card_fiberwise` / `sum_fiberwise_of_maps_to`、§D)、`c = O(n/log n)` envelope (`lz78PhraseStrings_count_isBigO`、§C)、target 接続 (`blockLogAvg_eq_neg_log_blockProb`、§A)。未充足は (genuine core ★ + max-length lemma + 合成) の 3 種で、**いずれも既存 length-stratification 資産の延長線上**。#groups = O(log n) なので overhead `c·log(#groups) = c·log log n` は `(c·log log n)/n = O((log log n)/log n) → 0` で **vanish する** (D3 をクリア)。

- **route B は基盤を丸ごと欠く + D3 trap が殺す**: (1) 現 `condPhraseProb` は **観測 `ω` 依存固定の path-prefix ratio** で、route B が要求する node-context 横断 sub-distribution `∑_a q(node·a|node) ≤ 1` を取り出せない (§A finding 1)。(2) worker の「emit 時 `cur ∈ dict`」不変条件は **docstring の prose のみで未 lemma 化** (§E)、node-context モデル (`treeNode`/`nodeContext`) は **0-hit で完全不在**。(3) `isLZ78PerPathParsingFactorization_of_pos` (route B 上端の constructor) は **phantom = 未実装** (§A finding 3)。(4) 決定的に — treenode-plan T3 自身が「node-grouping は `c·log c ≤ ∑_v k_v log(k_v) + c·log(#nodes)` 形」と記し、**#nodes ≈ c** なので overhead `c·log(#nodes) ≈ c·log c` は分母 `n` に対し **vanish しない** (D3 trap)。`c = O(n/log n)` を入れても `(c·log c)/n = O((c·log c)/n)` は `entropyRate₂` の order で残る → **genuine に不十分**。

**結論**: D3 trap は **route B を実際に殺す** (overhead `c·log(#nodes)` が `#nodes≈c` で非vanish、定数 limsup を超えて `entropyRate₂` order の誤差を残す)。route A の length-grouping は #groups=O(log n) で overhead が vanish するので **唯一の genuine route**。ただし route A でも genuine core ★ (`c·log c ≤ -log Pₙ + o(n)` の length-grouping AEP) は codebase + Mathlib 不在 (loogle `?c * Real.log ?c ≤ Finset.sum _ _` → 0 match) で、これが壁 `lz78-aseventual-ziv` の核として残る — 撤退ラインは正しく発動済 (tier-2 honest)、本在庫は「route A を resurrect する複数 leg セッション」の素材確定を供給する。

---

## 気づき

- `ZivEntropyBridge.lean` / `Kernel.lean` の docstring が複数箇所で `isLZ78PerPathParsingFactorization_of_pos` を「genuine 構築済」と参照しているが、その decl は **codebase に存在しない (phantom)**。route B を選ぶ際にこの constructor の self-build が暗黙コストとして加算されるほか、現状の docstring が「構築済」と誤主張している点は honesty 観点で訂正候補 (本タスク外、`@audit:suspect` 級ではないが docstring の事実誤認)。

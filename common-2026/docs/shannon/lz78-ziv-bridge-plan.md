# T4-A LZ78 Ziv-inequality entropy bridge — final discharge サブ計画 🌙

> **Parent**:
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md) §「撤退ライン L-LZ1 (Ziv's inequality) / L-LZ3 (chain hyps)」
> - [`lz78-achievability-converse-plan.md`](./lz78-achievability-converse-plan.md) (chain hyp predicate の出自)
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. LZ78 漸近最適性」 (Cover–Thomas Ch.13.5)
>
> **Inventory (必読、設計確定済)**: [`lz78-ziv-bridge-inventory.md`](./lz78-ziv-bridge-inventory.md)
> — 「VERDICT (C): per-path Ziv inequality + その下の per-path parsing factorization が不在。
> log-sum 原始子 (convexity + finset Jensen) は在庫あり。既存 entropy chain rule
> (`jointEntropy_chain_rule`) は **expectation-level** で per-path Ziv に流用不可」と結論済。
> 全 signature・前提条件ボックス・着手 skeleton まで確定。
>
> **Predecessor / 再利用基盤** (publish 済、本 plan からは黒箱 reuse、GENUINE):
> - `Common2026/Shannon/LZ78ZivInequality.lean` — 組み合わせ counting 層: `LZ78Parsing.card_phraseSet_le_pow` (`:204`), `card_phraseSet_le_count` (`:161`), `ZivCountingBound` (`:280`)。**counting は genuine、`IsZivInequalityPassthrough.of*` constructor は `True.intro` placeholder (本 plan の headline path は通らない)**。
> - `Common2026/Shannon/LZ78ConverseAsymptotic.lean` — `IsLZ78PhraseCountAsymptotic` (`:120`), `lz78_phrase_count_asymptotic` (`:378`), `_n_div_log` (`:387`) — `c = O(n/log n)` 漸近 envelope、GENUINE。
> - `Common2026/Shannon/LZ78PhraseCountAsymptoticBody.lean` — `IsZivCountingMulLogBound` (`:192`) `:= ∀ n, c·log c ≤ K·n`、`IsLZ78PhraseCountAsymptotic.of_mul_log_bound` (`:198`) — `c·log c ≤ Kn → c = O(n/log n)` 反転、GENUINE。
> - `Common2026/Shannon/ShannonMcMillanBreiman.lean` — `blockLogAvg` def (`:55`) `:= -(1/n)·log Pₙ{block ω}`、`measurable_blockLogAvg` (`:61`)、`expected_blockLogAvg_eq` (`:116`)。`shannon_mcmillan_breiman` (`SMBAlgoetCover.lean:2840`) — `blockLogAvg → entropyRate` a.s.、GENUINE。
> - `Common2026/Shannon/LZ78DistinctEncoding.lean` — `lz78DistinctEncodingLength` (`:128`), `lz78DistinctEncodingLength_eq` (`:133`) `:= c·bitLength c |α|`, `lz78Distinct_count_ofFn_le` (`:143`) `c ≤ n`, headline `lz78_two_sided_optimality_distinct_bdd_free` (`:412`) — GENUINE、本 plan の合流先。
> - Mathlib `Real.convexOn_mul_log` (`NegMulLog.lean:144`), `ConvexOn.map_sum_le` (`Jensen.lean:67`), `Real.strictConvexOn_mul_log` (`:137`)。
>
> **Pattern 雛形**:
> - [`lz78-ziv-inequality-discharge-moonshot-plan.md`](./lz78-ziv-inequality-discharge-moonshot-plan.md) (同 T4-A の partial discharge plan、撤退ライン英字記号 L-LZ1-X の流儀、規模見積 table)
> - [`arithmetic-coding-discharge-plan.md`](./arithmetic-coding-discharge-plan.md) (per-phase 撤退ライン + proof-log フラグ + honest brick 縮退の流儀)
>
> **Goal (短形)**: `lz78_two_sided_optimality_distinct_bdd_free` (`LZ78DistinctEncoding.lean:412`)
> が現在 honest hypothesis として受けている `h_achiev : IsLZ78AchievabilityChainHyp`
> (Eq. 13.124) と `h_converse : IsLZ78ConverseChainHyp` (Eq. 13.130) の **両方を genuine 構成で discharge**。
> 新規 1 ファイル `Common2026/Shannon/LZ78ZivEntropyBridge.lean` (~300–500 行) に
> per-path Ziv 不等式 `c·log c ≤ -log Pₙ{block ω}` を構築し、SMB-level `blockLogAvg`
> へ橋渡し → 2 述語を `theorem` として返す。**0 sorry / 0 warning**。
>
> **撤退ライン (本 plan、詳細は §撤退ライン)**:
> [L-LZ-Z1 解除目標] per-path Ziv `ziv_per_path_mul_log_le` を full genuine 構成。
> [L-LZ-Z2 解除] log-sum `log_sum_inequality` を `ConvexOn.map_sum_le` から導出。
> [L-LZ-Z3 解除] `blockLogAvg_eq_neg_log_blockProb` 自明 restate。
> [L-LZ-Z4 解除目標] assembly → `h_achiev` / `h_converse` 両 discharge。
> [L-LZ-Z5 新設・条件付き] per-path parsing factorization (`Pₙ{block} = Πⱼ cond phrase prob`)
>   が intractable なら、それを **唯一の isolated honest hypothesis** として明示 signature で残す
>   (現 `blockLogAvg`-level の `h_achiev`/`h_converse` より厳密に primitive な縮退)。`sorry` は使わない。

## Status (2026-05-21)

> 実態整合 (2026-05-21): headline `lz78_two_sided_optimality_distinct_bdd_free` (`:412`) は
> **DONE-HONEST-HYPS**: `h_bdd_above`/`h_bdd_below` は内部 discharge 済 (counting envelope)、
> 残る honest 入力は Cover–Thomas chain 2 述語 `h_achiev`/`h_converse` のみ。両者は **honest
> signature** (実 `∀ᵐ … ≤ …` body、`True`/`sorry` ではない) — inventory が「現状は意図された
> 撤退状態 = retreat line 上、本 plan の discharge は line を越える前進」と判定済。本 plan は
> その 2 述語を proving する後続 (= retreat line を越える)。**Phase 0 起草中**。inventory で
> 設計確定 (per-path factorization が真の crux、log-sum 原始子は在庫あり、既存 chain rule は
> expectation-level で流用不可)。

## 進捗

- [ ] Phase 0 — 設計確定 + 着手前 signature / 前提条件 再確認 (本 plan + inventory) 📋 → [lz78-ziv-bridge-inventory.md](./lz78-ziv-bridge-inventory.md)
- [ ] Phase 1 — `LZ78ZivEntropyBridge.lean` skeleton (全 def/定理 `:= by sorry`) + imports 📋
- [ ] Phase 2 — `log_sum_inequality` (L-LZ-Z2、`ConvexOn.map_sum_le` から導出、独立) 📋
- [ ] Phase 3 — `blockLogAvg_eq_neg_log_blockProb` (L-LZ-Z3、自明 restate、独立) 📋
- [ ] Phase 4 — per-path parsing factorization `blockProb_eq_prod_condPhraseProb` (真の crux、L-LZ-Z5 判定点) 📋
- [ ] Phase 5 — `ziv_per_path_mul_log_le` (L-LZ-Z1、factorization + log-sum + counting bound) 📋
- [ ] Phase 6 — assembly `isLZ78AchievabilityChainHyp_distinct` (L-LZ-Z4、limsup) 📋
- [ ] Phase 7 — assembly `isLZ78ConverseChainHyp_distinct` (L-LZ-Z4、liminf 双対) 📋
- [ ] Phase V — `Common2026.lean` 編入 + headline rewire + clean check 📋

## ゴール / Approach

### 最終到達点 (Phase 7 完成形)

新規 1 ファイル `Common2026/Shannon/LZ78ZivEntropyBridge.lean` の主合流 (signature は inventory「着手 skeleton」line 384–414 と整合):

```lean
namespace InformationTheory.Shannon

/-- **L-LZ-Z4 (achievability、Eq. 13.124)**: chain hyp を genuine 構成で返す。 -/
theorem isLZ78AchievabilityChainHyp_distinct
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    IsLZ78AchievabilityChainHyp μ p.toStationaryProcess
      (@lz78DistinctEncodingLength α _ _ _) := ...

/-- **L-LZ-Z4 (converse、Eq. 13.130)**: 双対 chain hyp を genuine 構成で返す。 -/
theorem isLZ78ConverseChainHyp_distinct
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    IsLZ78ConverseChainHyp μ p.toStationaryProcess
      (@lz78DistinctEncodingLength α _ _ _) := ...

end InformationTheory.Shannon
```

これで headline (`LZ78DistinctEncoding.lean:412`) の `h_achiev`/`h_converse` 引数を
`isLZ78AchievabilityChainHyp_distinct μ p` / `isLZ78ConverseChainHyp_distinct μ p` で供給した
**hypothesis-free 系** が新たに publish 可能になる (Phase V で wire)。

### Approach (overall strategy / shape of solution)

**核心の構造 (Cover–Thomas Lemma 13.5.5 = per-path / per-realization argument)**:
既存 entropy 機構 (`jointEntropy_chain_rule` 等) は **expectation-level** (`entropy μ = ∫ … ∂μ`、
固定 `Fin n`、固定 component family) で、Ziv 不等式が要求する **per-sample level**
(`-(1/n)·log Pₙ{block ω}`、ランダム個数 `c(ω)` のランダム長 phrase) と **交換不可**。
inventory DANGER の通り既存 chain rule は再利用できない。よって per-path で新規に組む。

```
Cover–Thomas Lemma 13.5.5 (per-path Ziv 不等式)
   │
   ├── [L-LZ-Z3] blockLogAvg ↔ block-prob (自明 restate、Phase 3、独立)
   │     n·blockLogAvg μ p n ω = -log Pₙ{block ω},  Pₙ := μ.map (blockRV n)
   │     def から直 (1/n 因子・log を展開)。~5 行。
   │
   ├── [L-LZ-Z2] log-sum 不等式 (Phase 2、独立)
   │     (Σ aₖ) log(Σaₖ / Σbₖ) ≤ Σ aₖ log(aₖ/bₖ)
   │     ← ConvexOn.map_sum_le (Real.convexOn_mul_log、weights bₖ/Σb、points aₖ/bₖ)
   │     0·log0 / bₖ=0 edge を pointwise 処理。~30–60 行。
   │
   ├── [L-LZ-Z5 = 真の crux] per-path parsing factorization (Phase 4)
   │     Pₙ{block ω} = Πⱼ (conditional phrase prob)
   │     ── これが MISSING の primitive。下記「factorization の正体」参照。
   │     full 試行 → intractable なら honest hypothesis に分離 (L-LZ-Z5 発動)。
   │
   ├── [L-LZ-Z1] per-path Ziv 不等式 (Phase 5)
   │     c·log c ≤ -log Pₙ{block ω}
   │     ← factorization (Z5) で Pₙ を per-phrase 積に分解
   │       → -log Pₙ = -Σⱼ log P{phraseⱼ|prefix}
   │       → distinct-phrase 数 c の log-sum (Z2) で c·log c で下から押さえる
   │       → distinct count `card_phraseSet_le_pow` (既存 genuine) で項数を c に縛る
   │     ~150–300 行 (Z5 を除いた assembly 部分)。
   │
   └── [L-LZ-Z4] assembly → chain hyps (Phase 6,7)
         per-symbol bridge: (lz n x)/n = c·bitLength(c,|α|)/n  (lz78DistinctEncodingLength_eq)
           bitLength(c,|α|) ≈ log₂ c + O(log|α|) ⟹ (lz n x)/n ≤ (c log c)/n·C + o(1)
           ≤ (-log Pₙ{block})/n · C + o(1) = blockLogAvg·C + o(1)   (Z1 + Z3)
           c = O(n/log n) (既存 envelope) で o(1) 項を 0 に落とす
         limsup を取って h_achiev (Phase 6)、liminf 双対で h_converse (Phase 7)
         ~80–150 行 (filter / o(1) plumbing、achiev/converse collapse 既存補題を一部流用)
```

**factorization の正体 (Phase 4 の最重要設計判断)** — `Pₙ{block ω} = μ.map(blockRV n) {x}`
は length-`n` block 上の **pushforward 測度の singleton 質量**。これを LZ78 parsing の
distinct phrase ごとの **条件付き確率の積** に分解するのが Z5。在庫テーブル Q4 が確認した通り
**`blockLogAvg` ↔ parsing の橋は project に 0%、Mathlib に Shannon entropy 自体が無い** ため、
これは **新規の measure-theoretic 補題**になる。設計の二択:

1. **stationary process の compProd / 条件付き構造から導く (full genuine 目標)**:
   `StationaryProcess` (`Stationary.lean`) が block を逐次条件付けで生成する構造 (Markov kernel /
   `Measure.compProd` 連鎖) を持つなら、`x` の parsing 切れ目に沿った prefix で `Pₙ{x}` を
   telescoping product に展開できる。**着手前に `Stationary.lean` で `blockRV` が compProd /
   kernel で定義されているか確認必須** (Phase 0)。compProd なら `Measure.compProd_apply` /
   `lintegral` 系で singleton 質量を逐次条件確率の積に開ける見込み。
2. **factorization を新規 def + 補題で project 内に建てる**: 上記が `blockRV` の def 形と噛み合わ
   なければ、parsing の prefix に沿った conditional phrase probability を新規 def
   (`condPhraseProb p x j`) で導入し、`blockProb_eq_prod_condPhraseProb` を chain rule 風に証明。
   inventory の警告通り **これは expectation-level chain rule とは別物**で、telescoping は
   per-path の集合分解 (`{x}` を prefix が一致する cylinder の交わりで書く) から手で組む。

どちらでも **Mathlib-shape-driven** を厳守: factorization の結論形を、Z1 で log を取って
log-sum (Z2) に流し込める形 (`Pₙ{x} = ∏ⱼ qⱼ`、`qⱼ ≥ 0`) に固定してから着手。
教科書 literal の `P(phrase|context)` 形を先に書かない。

**direction の非対称 (Phase 6 vs 7)** — Ziv 不等式 `c·log c ≤ -log Pₙ{block}` は
**achievability (limsup、上界) を直接与える**: `(lz n)/n ≲ (c log c)/n ≤ blockLogAvg + o(1)`。
converse (`h_converse`、liminf 下界 `blockLogAvg ≤ (lz n)/n`) は **逆向きの per-path 不等式**
(`bitLength` の **下界** `lz n ≥ c·log₂ c` 形 + Ziv の逆向き or 直接の coding 下界) が要る。
inventory は「converse = matching liminf reading」と書くが、**逆向きが Ziv の単純な liminf 化で
済むか、追加の coding 下界補題 (`lz78DistinctEncodingLength` の下界、`bitLength_ge` 系) が要るかは
Phase 0 で確認**。済まない場合 Phase 7 を Phase 6 と同格の独立 discharge とする
(下記「規模見積」で Phase 7 を 80–120 行に見積もる理由)。

### 規模見積

| Phase | 中央 | 出力 | proof-log |
|---|---|---|---|
| Phase 1 | **60 行** | skeleton (全 def/定理 `:= by sorry`) + imports + namespace + variable | no |
| Phase 2 | **30–60 行** | `log_sum_inequality` (Jensen 適用、0·log0 edge) | yes |
| Phase 3 | **5–10 行** | `blockLogAvg_eq_neg_log_blockProb` (def 展開) | no |
| Phase 4 | **80–200 行 / 撤退時 ~10 行** | `blockProb_eq_prod_condPhraseProb` (真の crux、full or honest hyp L-LZ-Z5) | yes |
| Phase 5 | **150–300 行** | `ziv_per_path_mul_log_le` (factorization + log-sum + counting) | yes |
| Phase 6 | **60–100 行** | `isLZ78AchievabilityChainHyp_distinct` (limsup assembly) | yes |
| Phase 7 | **40–120 行** | `isLZ78ConverseChainHyp_distinct` (liminf 双対 or 独立下界) | yes |
| Phase V | **5–15 行** | `Common2026.lean` import + headline rewire (hyp-free 系 publish) + clean check | no |
| **累計** | **~430–800 行** | 1 ファイル (Phase 4 が intractable なら ~280 行 + isolated honest hyp 1 本) | — |

### ファイル構成

```
Common2026/Shannon/
  LZ78ZivEntropyBridge.lean   ← 新規 (~430–800 行)
                                ・log_sum_inequality                     (Z2、独立)
                                ・blockLogAvg_eq_neg_log_blockProb       (Z3、独立)
                                ・(def condPhraseProb? — Phase 4 設計次第)
                                ・blockProb_eq_prod_condPhraseProb       (Z5、crux)
                                ・ziv_per_path_mul_log_le                (Z1)
                                ・lz_per_symbol_le_blockLogAvg_add_smallo (Z4 helper)
                                ・isLZ78AchievabilityChainHyp_distinct   (Z4、limsup)
                                ・isLZ78ConverseChainHyp_distinct        (Z4、liminf)
  LZ78DistinctEncoding.lean   ← (Phase V) hyp-free headline 系を追記 (任意、既存定理は不変)
  Common2026.lean             ← `import Common2026.Shannon.LZ78ZivEntropyBridge` 追記
```

**既存 genuine 補題の signature は一切変更しない** (詳細 §Blast radius)。本 plan は新規補題の
追加のみ。headline `lz78_two_sided_optimality_distinct_bdd_free` (`:412`) も signature 不変
(Phase V の hyp-free 系は **別名の新 theorem**、既存定理は残す)。

## Phase 0 - 設計確定 + 着手前 signature / 前提条件 再確認 📋

inventory で大枠確定済。**着手前に必ず実装者が確認する事項** (signature drift / 仮定漏れ / 設計分岐):

- [ ] **`blockRV` / `StationaryProcess` の生成構造** (`Stationary.lean:81`)。`blockRV p n ω` が
      compProd / Markov kernel で逐次生成されているか、単なる射影かを確認 → Phase 4 の二択
      (compProd 経由 full genuine か、新規 factorization 補題か) を確定。**factorization が全体の crux**。
- [ ] **`Pₙ.real {x}` の measurable / singleton 質量の扱い**。`(μ.map (blockRV n)).real {x}` =
      `Measure.real` = `ENNReal.toReal ∘ μ.map(blockRV n)`。`MeasurableSingletonClass (Fin n → α)`
      が instance 解決されるか (有限 alphabet × 有限 index で自動の見込み、要確認)。
- [ ] **`bitLength` の上界・下界**。`LZ78Phrase.bitLength c |α|` の正確な形と、`log₂` への上下界補題
      (`bitLength_eq` / `bitLength_le` / `bitLength_ge` が `LempelZiv78.lean` にあるか)。converse
      (Phase 7) は下界 `lz n ≥ c·log₂ c - O(...)` が要るので **下界補題の有無で Phase 7 規模が決まる**。
- [ ] **`c = O(n/log n)` envelope の正確な適用形** (`lz78_phrase_count_asymptotic_n_div_log`
      `LZ78ConverseAsymptotic.lean:387`)。Phase 6/7 の o(1) 落としで `(c log c)/n → 0` 余剰項を
      消すのにどの形 (`IsBigO` / `IsLittleO` / 明示 `B n`) で供給されるか。
- [ ] **`convexOn_mul_log` の domain** (`Set.Ici 0`) と `ConvexOn.map_sum_le` の weights 制約
      (`∑ w = 1`, `0 ≤ wᵢ`)。Z2 で weights `bₖ/Σb`、points `aₖ/bₖ` を入れる際の `Σb > 0` /
      `bₖ ≥ 0` / `aₖ ≥ 0` 前提を block-prob の文脈で discharge 可能か (前提条件ボックス: `Pₙ{phrase}` は
      未出現 phrase で 0 になりうる → `0·log0` landmine)。
- [ ] **`blockLogAvg` の `n=0` edge** (因子 `1/0 = 0` で `blockLogAvg = 0`)。per-path Ziv 補題は
      `n=0` と `log0` (`Pₙ{x}=0`) branch を special-case する (前提条件ボックス末尾)。

## Phase 1 - skeleton + imports 📋

skeleton-driven (CLAUDE.md): 全 def/定理を `:= by sorry` で並べ、namespace / imports / variable 確定。
inventory「着手 skeleton」line 366–414 をベースに、factorization def/補題 (Phase 4) と converse 定理
(Phase 7) と per-symbol helper (Z4) を追加。

- [ ] imports (inventory line 367–372): `Common2026.Shannon.LZ78ZivInequality`,
      `LZ78ConverseAsymptotic`, `LZ78DistinctEncoding`, `ShannonMcMillanBreiman`,
      `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`, `Mathlib.Analysis.Convex.Jensen`。
      Phase 4 の compProd 経路を採るなら `Mathlib.Probability.Kernel.Composition.*` 系を追加。`import Mathlib` 禁止。
- [ ] namespace `InformationTheory.Shannon`、`open MeasureTheory ProbabilityTheory Filter Topology`、
      `open scoped ENNReal NNReal BigOperators` (inventory line 374–377)。
- [ ] variable 行 (inventory line 379–382): `{α Ω}` + 有限 alphabet instances + `[MeasurableSpace Ω]`。
- [ ] 全 7 declaration を `:= by sorry` で stub: `log_sum_inequality`, `blockLogAvg_eq_neg_log_blockProb`,
      `blockProb_eq_prod_condPhraseProb` (+ 必要なら `condPhraseProb` def), `ziv_per_path_mul_log_le`,
      `lz_per_symbol_le_blockLogAvg_add_smallo`, `isLZ78AchievabilityChainHyp_distinct`, `isLZ78ConverseChainHyp_distinct`。
- [ ] **検証**: `lake env lean Common2026/Shannon/LZ78ZivEntropyBridge.lean` が sorry warning のみで type-check。LSP `<new-diagnostics>` を待つ。
- **撤退ライン**: なし (skeleton のみ、確実)。

## Phase 2 - `log_sum_inequality` (L-LZ-Z2、独立) 📋

`(Σ aₖ) log(Σaₖ / Σbₖ) ≤ Σ aₖ log(aₖ/bₖ)` を `ConvexOn.map_sum_le` から導出。Z1 から独立に landable。

- [ ] target (inventory line 392–397):
      `(∑ i ∈ s, a i) * log((∑ a)/(∑ b)) ≤ ∑ i ∈ s, a i * log(a i / b i)`、前提 `0 ≤ aᵢ`, `0 < bᵢ`。
- [ ] `Real.convexOn_mul_log : ConvexOn ℝ (Set.Ici 0) (fun x ↦ x*log x)` (`NegMulLog.lean:144`) を
      weights `wₖ = bₖ/Σb`、points `pₖ = aₖ/bₖ` で `ConvexOn.map_sum_le` (`Jensen.lean:67`) に適用。
- [ ] weights 検証: `∑ wₖ = ∑ bₖ/Σb = 1` (`Finset.sum_div`)、`0 ≤ wₖ` (`hb` から)、`pₖ ∈ Set.Ici 0` (`ha`/`hb`)。
- [ ] `f(∑ wₖ•pₖ) ≤ ∑ wₖ•f(pₖ)` を `wₖ pₖ = aₖ/Σb`、`∑ aₖ/Σb` を代入して整理 → 両辺 `Σb` 倍で目標形へ。
- **依存補題**: `Real.convexOn_mul_log` (`:144`), `ConvexOn.map_sum_le` (`Jensen.lean:67`), `Finset.sum_div`, `Finset.mul_sum`。
- **proof-log: yes** — 0·log0 / `bₖ=0` (本 lemma は `0 < bᵢ` 前提だが Z1 で zero-mass phrase を渡す際の橋で edge 再燃)、weights 正規化の cast。
- **撤退ライン**: Jensen の weights/points 代入が詰まったら、2 項版 (`a₁ log(a₁/b₁) + a₂ log(a₂/b₂) ≥ (a₁+a₂)log((a₁+a₂)/(b₁+b₂))`) を `convexOn_mul_log` の `ConvexOn` 2 点定義から直接示し `Finset.sum` 帰納で一般化 (~+30 行)。full discharge 維持。

## Phase 3 - `blockLogAvg_eq_neg_log_blockProb` (L-LZ-Z3、独立) 📋

`n · blockLogAvg μ p n ω = -log Pₙ{block ω}` (`0 < n`)。def からの自明 restate。

- [ ] target (inventory line 385–388):
      `(n:ℝ) * blockLogAvg μ p n ω = -Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})`。
- [ ] `blockLogAvg` def (`ShannonMcMillanBreiman.lean:55`) を unfold: `= n * (-(1/n)*log(…))`、
      `n * (1/n) = 1` (`0 < n` で `mul_one_div_cancel`)。
- **依存補題**: `blockLogAvg` def、`mul_one_div_cancel` / `field_simp`。
- **撤退ライン**: なし (~5 行、確実)。

## Phase 4 - per-path parsing factorization (真の crux、L-LZ-Z5 判定点) 📋

`Pₙ{block ω} = Πⱼ (conditional phrase prob)`。**本 plan 全体の crux**。Phase 0 の `blockRV` 構造確認結果で経路確定。

- [ ] **target (経路 1、compProd)**: `blockRV` が `Measure.compProd` / kernel 連鎖で生成されているなら、
      `{x}` を parsing 切れ目 prefix の cylinder 交わりで分解 → `Measure.compProd_apply` を逐次適用し
      `Pₙ{x} = ∏ⱼ qⱼ(x)` の telescoping product。`qⱼ ≥ 0` の形で結論 (Mathlib-shape-driven: Z1/Z2 が
      log を取れる積形に固定)。
- [ ] **target (経路 2、新規 def)**: compProd と噛み合わなければ `condPhraseProb p x j` を新規 def 導入し、
      `blockProb_eq_prod_condPhraseProb` を per-path 集合分解 (`{x} = ⋂ⱼ {y | y の j-prefix = x の j-prefix}`)
      から手で証明。**inventory DANGER 厳守: これは expectation-level chain rule とは別物、`jointEntropy_chain_rule` は使えない**。
- [ ] zero-mass edge: 未出現 prefix で `qⱼ = 0` → `Pₙ{x} = 0`、`log0 = 0` 規約で Z1 の log-sum に矛盾なく渡る branch を確保。
- **依存補題**: (経路1) `Measure.compProd_apply`, `Measure.map_apply`, `lintegral` 系; (経路2) parsing prefix の集合代数 + `Measure.real` の有限加法性。`lz78PhraseStrings` の prefix 構造 (`LempelZiv78.lean`)。
- **proof-log: yes** — 経路選択の判断、telescoping の集合分解、zero-mass branch を記録。
- **撤退ライン [L-LZ-Z5 新設・条件付き発動]**: factorization が **~1 セッション / ~200 行で閉じない見込み**なら
  **isolated honest hypothesis として分離** (§撤退ライン詳細)。Z2/Z3/Z5以外/Z1 assembly/Z4 を genuine に残し、
  factorization のみを明示 signature の honest 入力にする。`sorry` は使わない。**この縮退でも現状 (`h_achiev`/`h_converse`
  という blockLogAvg-level の 2 述語) より厳密に primitive で小さい deferral になる**。

## Phase 5 - `ziv_per_path_mul_log_le` (L-LZ-Z1) 📋

`c·log c ≤ -log Pₙ{block ω}` (`c := (lz78PhraseStrings (List.ofFn x)).length`)。factorization + log-sum + counting の合流。

- [ ] target (inventory line 400–404):
      `(c:ℝ) * log c ≤ -Real.log ((μ.map (p.blockRV n)).real {x})`、`c := (lz78PhraseStrings (List.ofFn x)).length`。
- [ ] factorization (Phase 4) で `-log Pₙ{x} = -Σⱼ log qⱼ` に開く。
- [ ] log-sum (Phase 2) を `aₖ ≡ 1` (各 distinct phrase に均等重み) / `bₖ ≡ qⱼ` で適用 → `c·log c ≤ -Σⱼ log qⱼ` の下界形を得る (Cover–Thomas Eq. 13.122–13.124 の log-sum step)。
- [ ] distinct-phrase 数 `c` を `card_phraseSet_le_pow` (`LZ78ZivInequality.lean:204`、既存 genuine) で項数に縛る。
- [ ] zero-mass / `c=0` / `n=0` の edge を special-case (前提条件ボックス)。
- **依存補題**: Phase 4 factorization, Phase 2 `log_sum_inequality`, `card_phraseSet_le_pow` (`:204`), `card_phraseSet_le_count` (`:161`)。
- **proof-log: yes** — log-sum の weight 選択 (`aₖ≡1`)、counting bound の項数縛り、edge case を記録。
- **撤退ライン**: log-sum の weight 設計が合わなければ Cover–Thomas の uniform-distribution 版 (`Σ qⱼ ≤ 1` を使った `c log c ≤ -Σ log qⱼ`) を `convexOn_mul_log` 直適用で再構成。Phase 4 が L-LZ-Z5 で honest 化された場合は本 Phase の factorization 入力が honest hyp になるだけで、残りは genuine。

## Phase 6 - `isLZ78AchievabilityChainHyp_distinct` (L-LZ-Z4、limsup) 📋

per-path Ziv → per-symbol bridge → limsup で `h_achiev`。

- [ ] **per-symbol helper** `lz_per_symbol_le_blockLogAvg_add_smallo`:
      `(lz78DistinctEncodingLength n x : ℝ)/n ≤ blockLogAvg μ p n (witness) + ε n`、`ε → 0`。
      `lz78DistinctEncodingLength_eq` (`:133`) で `lz n x = c·bitLength(c,|α|)`、`bitLength ≈ log₂ c + O(log|α|)`
      (Phase 0 確認の上界補題) → `(lz n x)/n ≤ C·(c log c)/n + o(1)`、Ziv (Phase 5) + Z3 (Phase 3) で
      `≤ C·blockLogAvg + o(1)`、`c = O(n/log n)` (`LZ78ConverseAsymptotic.lean:387`) で余剰項 → 0。
- [ ] target: `IsLZ78AchievabilityChainHyp μ p.toStationaryProcess (@lz78DistinctEncodingLength α _ _ _)`
      = `∀ᵐ ω, limsup ((lz n (blockRV n ω))/n) ≤ limsup (blockLogAvg μ p n ω)` (body verbatim `LZ78FinalGlue.lean:118`)。
- [ ] `Filter.Eventually.of_forall` で a.s. 化 → per-ω で per-symbol helper を `limsup` に持ち上げ (`Filter.limsup_le_limsup` + o(1) を `Filter.Tendsto` で吸収)。既存 achiev collapse 補題 (`lz78_achievability_upper_bound_ergodic` 系) の limsup plumbing を流用。
- **依存補題**: Phase 5 Ziv, Phase 3 Z3, `lz78DistinctEncodingLength_eq` (`:133`), `lz78_phrase_count_asymptotic_n_div_log` (`:387`), `bitLength` 上界 (Phase 0), `Filter.limsup_le_limsup`。
- **proof-log: yes** — o(1) 項の Tendsto 吸収、limsup 持ち上げの filter 補題選択。
- **撤退ライン**: limsup plumbing が重ければ既存 `lz78_achievability_upper_bound_ergodic` の collapse パターンを直接 instantiate (per-symbol helper を hypothesis として渡す形)。helper 自体が genuine なら full discharge。

## Phase 7 - `isLZ78ConverseChainHyp_distinct` (L-LZ-Z4、liminf 双対) 📋

`h_converse` = liminf 下界。Phase 6 の双対 + (要すれば) 独立 coding 下界。

- [ ] target: `∀ᵐ ω, liminf (blockLogAvg μ p n ω) ≤ liminf ((lz n (blockRV n ω))/n)` (body verbatim `LZ78ConverseDischarge.lean:106`)。
- [ ] **Phase 0 で「逆向きが Ziv の liminf 化で済む」と判明した場合**: Phase 6 の helper を逆不等号 (`blockLogAvg ≤ (lz n)/n + o(1)`) で得て liminf 化。`bitLength` の **下界** (`lz n ≥ c·log₂ c`) が要る。
- [ ] **済まない場合 (独立 discharge)**: Cover–Thomas Eq. 13.130 の converse coding 下界
      (任意 prefix-free / LZ78 code は negative log-likelihood を下回れない) を Kraft 系 / 既存 source-coding 下界
      (`ShannonCode.entropyD_le_expectedLength_of_kraft` 等) から per-path で再構成。
- **依存補題**: Phase 5/6 の双対, `bitLength` 下界 (Phase 0), `Filter.liminf_le_liminf`, (独立時) source-coding 下界。
- **proof-log: yes** — 双対 vs 独立の判断点、coding 下界の出所、`bitLength` 下界の有無を記録。
- **撤退ライン**: converse の coding 下界が Mathlib gap (Shannon entropy 不在) で重い場合、Phase 7 のみ
  honest hypothesis pass-through に縮退 (achiev = Phase 6 は full genuine を維持)。これは L-LZ-Z5 とは別の
  部分縮退で、`h_converse` を「per-path coding 下界 (genuine、Cover–Thomas 13.130) を仮定して liminf 結論を返す」
  明示 signature にする。`Prop := True` は使わない。

## Phase V - `Common2026.lean` 編入 + headline rewire + clean check 📋

- [ ] `Common2026.lean` に `import Common2026.Shannon.LZ78ZivEntropyBridge` を追記 (`LZ78DistinctEncoding` import の後ろ)。
- [ ] **headline rewire**: `lz78_two_sided_optimality_distinct_bdd_free` の `h_achiev`/`h_converse` 引数を
      `isLZ78AchievabilityChainHyp_distinct μ p` / `isLZ78ConverseChainHyp_distinct μ p` で供給した
      **hyp-free 新 theorem** (`lz78_two_sided_optimality_distinct` 等の別名) を publish。**既存 `_bdd_free` 定理は signature 不変で残す** (下流 caller 互換)。
- [ ] `lake env lean Common2026/Shannon/LZ78ZivEntropyBridge.lean` silent (0 error / 0 sorry / 0 warning)。
- [ ] 既存 genuine 補題 (`card_phraseSet_le_pow`, `lz78DistinctEncodingLength_eq`, `blockLogAvg`, SMB 系) の
      signature が無変更であることを `rg` で横断確認 (新規追加のみ、§Blast radius)。
- [ ] upstream olean refresh: 新 public symbol を `LZ78DistinctEncoding` 等が拾うなら `lake build Common2026.Shannon.LZ78ZivEntropyBridge` 一回。

## Blast radius

- **新規 lemma 投入先**: `Common2026/Shannon/LZ78ZivEntropyBridge.lean` (新規 1 ファイル) に全 7 declaration。
  Phase 4 経路 2 を採ると `condPhraseProb` def も同ファイル。
- **編集される既存ファイル**: `Common2026.lean` (import 1 行追記)。`LZ78DistinctEncoding.lean` は
  **任意** (Phase V の hyp-free 系を別名で追記する場合のみ、既存定理は不変)。
- **signature 変更ゼロ確認**: 再利用する既存 genuine 補題 (`card_phraseSet_le_pow` `LZ78ZivInequality.lean:204`,
  `lz78DistinctEncodingLength_eq` `:133`, `lz78_phrase_count_asymptotic_n_div_log` `LZ78ConverseAsymptotic.lean:387`,
  `blockLogAvg` `ShannonMcMillanBreiman.lean:55`, `shannon_mcmillan_breiman` `SMBAlgoetCover.lean:2840`,
  `IsLZ78AchievabilityChainHyp` `LZ78FinalGlue.lean:118`, `IsLZ78ConverseChainHyp` `LZ78ConverseDischarge.lean:106`)
  は **全て黒箱 reuse、signature 不変**。本 plan は新規補題追加のみで既存の証明・型を触らない。
- **placeholder への影響なし**: `IsZivInequalityPassthrough.of*` の `True.intro` 群 (`LZ78ZivInequality.lean:325`,
  `LZ78ConverseAsymptotic.lean:230`) は headline path を通らない (inventory Q3 確認済) ため本 plan は触らない。

## 撤退ライン

- **L-LZ-Z2 / L-LZ-Z3 (解除目標)**: log-sum 不等式 (Jensen から導出) と blockLogAvg restate。
  原始子在庫あり、独立に full discharge 可能。最低限の確実な前進。
- **L-LZ-Z1 / L-LZ-Z4 (解除目標)**: per-path Ziv 本体と chain hyp assembly。Phase 4 が通れば達成。
- **L-LZ-Z5 (新設・条件付き発動、最重要)**: per-path parsing factorization
  `Pₙ{block ω} = Πⱼ (cond phrase prob)` が **~1 セッション / ~200 行で閉じない**見込みなら
  **isolated honest hypothesis として分離**。具体的に残す述語の形:

  ```lean
  /-- **Isolated honest input (L-LZ-Z5)**: stationary process の per-path block 確率が
  LZ78 parsing の per-phrase 条件付き確率の積に分解する (Cover–Thomas 13.5、chain rule の per-path 形)。
  expectation-level の `jointEntropy_chain_rule` とは別物で、本 wave では未 discharge。 -/
  def IsLZ78PerPathParsingFactorization
      (μ : Measure Ω) (p : StationaryProcess μ α) : Prop :=
    ∀ (n : ℕ) (x : Fin n → α),
      (μ.map (p.blockRV n)).real {x}
        = ∏ j ∈ Finset.range (lz78PhraseStrings (List.ofFn x)).length,
            condPhraseProb p x j
  ```

  この縮退で `h_achiev`/`h_converse` (現状の **blockLogAvg-level** 2 述語) を **より primitive な
  factorization 1 述語**に置き換える。Z2/Z3/Z1(assembly)/Z4 は全て genuine、factorization のみ honest。
  **`sorry` / `Prop := True` は使わない** (明示 signature の honest hypothesis pass-through)。
  これは現状より厳密に小さく primitive な deferral (1 述語 vs 2 述語、parsing-level vs blockLogAvg-level)。

- **L-LZ-Z6 (Phase 7 部分縮退、独立)**: converse の coding 下界が Shannon-entropy 不在で重い場合、
  **Phase 7 (`h_converse`) のみ** honest hypothesis pass-through に縮退 (achiev = Phase 6 は full genuine)。
  per-path coding 下界 (Cover–Thomas 13.130) を明示 signature で仮定する。`Prop := True` は使わない。

- **all-or-nothing 注記 (CRITICAL)**: headline `lz78_two_sided_optimality_distinct_bdd_free` の
  `h_achiev`/`h_converse` は、**chain 全体 (Z2→Z3→Z4(factorization)→Z1→Z4 assembly) が genuine に
  なって初めて discharged に flip する**。部分進捗 (Z2/Z3 だけ、または Z1 まで factorization が honest)
  では 2 述語は依然 honest 入力のまま — headline は引数として受け取り続ける。L-LZ-Z5 発動時は
  factorization 1 述語が、L-LZ-Z6 発動時は converse 1 述語が、honest 入力として明示的に残る
  (現状より小さい deferral だが **完全 discharge ではない**)。

## 当面の next step

1. Phase 0 着手前確認 (`blockRV`/`StationaryProcess` の compProd 構造 ← factorization 経路を決める最重要、`bitLength` 上下界、`c=O(n/log n)` 適用形、Jensen 前提、`n=0`/`log0` edge)
2. Phase 1 skeleton (全 7 declaration `:= by sorry`) → type-check 確認
3. Phase 2 (log-sum) + Phase 3 (restate) を独立に full discharge — 確実な前進を先取り
4. Phase 4 (factorization、crux) full 試行 → ~200 行 / 1 セッションで判定 → 閉じなければ L-LZ-Z5 (isolated honest hyp) 発動
5. Phase 5 (Ziv 本体) → Phase 6 (achiev limsup) → Phase 7 (converse liminf、双対 or 独立 / L-LZ-Z6 判定)
6. Phase V `Common2026.lean` 編入 + hyp-free headline 系 publish + clean check

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 起草時点の確定事項 (実装中の方針変更があればここに追記):
1. **既存 chain rule は流用不可と確定 (inventory DANGER)**: `jointEntropy_chain_rule` (Han.lean:56) は
   expectation-level (固定 Fin n、固定 component、∫ negMulLog)。Ziv は per-path (ランダム c・ランダム長
   phrase、-(1/n)log Pₙ{block ω})。両者交換不可、bridge 不在。per-path で新規に組む。
2. **真の crux = per-path parsing factorization (Phase 4 / L-LZ-Z5)**: log-sum 原始子は在庫あり (Z2 確実)、
   blockLogAvg restate は自明 (Z3 確実)。全体の難所は `Pₙ{block} = Πⱼ cond phrase prob` の新規構築。
   閉じなければこれ 1 本を isolated honest hyp に分離 (現状 2 述語より小さい deferral)。
3. **direction 非対称を Phase 6/7 で分離**: Ziv は achiev (limsup 上界) を直接与える。converse (liminf 下界) は
   逆向きの per-path 不等式 / coding 下界が要る可能性あり。Phase 0 で bitLength 下界の有無を確認、
   済まなければ Phase 7 を独立 discharge (L-LZ-Z6 で部分縮退可)。
4. **既存 genuine は黒箱 reuse、signature 変更ゼロ**: 本 plan は新規 1 ファイル + import 1 行のみ。
   headline `_bdd_free` も不変、hyp-free 系は別名で publish。
-->

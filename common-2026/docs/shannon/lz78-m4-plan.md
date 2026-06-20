# LZ78: M4 converse (Barron a.s. lift) サブ計画

> **Parent**: [`lz78-completion-roadmap.md`](lz78-completion-roadmap.md) §1 M4 / M5
> （M4 converse residual `plan:lz78-m4-plan`、ゴール = `lz78GreedyImpl_converse_ae`）

🔄 **verdict OVERTURNED (2026-06-21、gateway-atom-first 読み取り在庫)**: parent roadmap §1 M4 と
コード docstring (`GreedyParsingImpl.lean:484`) は M4 を「research-level エルゴード壁、codebase +
Mathlib 不在」と framing するが、本セッションの読み取り在庫が **反証**: M4 は **既存 sorry-free
資産の配線 + 1 つの genuine 組合せ brick で closeable**。dominant 残作業は polynomial n-block Kraft
(G2、~150–300 行の genuine LZ78 組合せ) のみで、ergodic machinery (SMB-liminf / Q_k AEP) は
**全て既存 sorry-free**。「research-level wall / scope-out」は **過大評価** (cause:single-route /
gateway-atom-untried)。confidence は依然 `human-judgment` (機械裏取り前) なので独立 pivot で再確認。

## 進捗

- [ ] Phase 0 — M0 在庫確認（流用 + Kraft 用 Mathlib API 追補）📋
- [ ] G4 — liminf assembly + SMB-liminf 配線（PURE WIRING、high confidence）📋
- [ ] G3 — Barron a.s.-eventual lift（Z-side テンプレ複写、medium confidence）📋
- [ ] G2 — polynomial n-block Kraft（THE GENUINE NEW BRICK、medium）📋
- [ ] G1 — encoder / injectivity scaffolding（G2 の支援）📋
- [ ] M5 — 最終合成 + headline sorryAx-free 判定（capstone、低リスク）📋

## ゴール

唯一の残 headline 壁 `lz78GreedyImpl_converse_ae`（`GreedyParsingImpl.lean:484`、唯一の live bare
sorry、Cover–Thomas Thm 13.5.3 lower bound）の sorry を discharge し、headline
`lz78_asymptotic_optimality_with_greedy_impl`（`:1090`、`@[entry_point]`）を sorryAx-free 化する
（achievability = upper half は leg 11 で既に sorryAx-free、本 plan が lower half を閉じれば squeeze
完成）。verbatim 確認済の goal signature（`GreedyParsingImpl.lean:484`、`@residual(plan:lz78-m4-plan)`、honesty-auditor が overturn された `wall:` 判定から本 plan-class へ reclassify 済）:

```lean
theorem lz78GreedyImpl_converse_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      entropyRate₂ μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n =>
            (lz78GreedyImplEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop := by
  sorry
```

**signature 不変（ripple ゼロ前提）**: target は source data (`μ`, `p`) + `[IsProbabilityMeasure μ]`
regularity のみ。本 plan は body を埋めるだけで signature を変えない（hypothesis bundling 禁止 →
G2 は **shared sorry lemma** として別に切り出し、forward reference で消費する。後述 G2 §honesty 注記）。

## Approach

標準 Barron a.s. source-coding converse: a.s. に
`liminf L_n/n ≥ liminf (-log₂ P_n)/n = entropyRate₂`（`L_n = lz78GreedyImplEncodingLength`）。
構成要素は (a) `∑ 2^{-L_n}` 上の Kraft 型上界、(b) Markov + Borel–Cantelli の a.s. lift、(c) SMB の
liminf。**ergodic machinery は全て既存 sorry-free** なので、新規 genuine は (a) の polynomial Kraft
1 brick に絞られる。4 brick に分解（leg ordering: leg 1 = G4 配線 + G3 テンプレ複写、G2 を sorry brick
として isolate → 後続 leg で G2 を discharge）:

- **G4 — liminf assembly + SMB-liminf 配線（PURE WIRING、high confidence）**。既存
  `algoet_cover_liminf_bound`（`SMB/AlgoetCover/Liminf.lean:384`、`@[entry_point]`、verbatim 確認済）が
  `∀ᵐ ω, entropyRate μ p.toStationaryProcess ≤ liminf (fun n => blockLogAvg μ p.toStationaryProcess n ω)`
  （**nat 単位**）を供給。両辺を `Real.log 2 > 0` で割り `entropyRate₂ ≤ liminf blockLogAvg₂` を得る
  （`blockLogAvg₂`（`:503`）/ `entropyRate₂`、`shannon_mcmillan_breiman₂`（`:521`、`@audit:ok`、
  sorryAx-free）と同じ unit rescaling）。次に `Filter.liminf_le_liminf` で G3 と連鎖。
  Z-side 先例 `liminf_blockLogAvgZ_ge_entropyRate`（`Liminf.lean:334`）と同型。
- **G3 — Barron a.s.-eventual lift（Z-side テンプレ複写、medium confidence）**。
  `MRatioLowerZ_le_sq_eventually`（`Liminf.lean:25`）+ `blockLogAvgZ_ge_negLogQInftyZ_minus_error`
  （`Liminf.lean:98`）を複写: 尤度比 `2^{-L_n}/P_n` の Markov bound + first Borel–Cantelli
  (`MeasureTheory.ae_eventually_notMem`) + p-series 総和可能 ⟹
  `∀ᵐ ω, ∀ᶠ n, blockLogAvg₂ n ω - error_n ≤ L_n/n`、ここで
  `error_n = (2 log n + log poly)/(n log 2) → 0`。**G3 の唯一の外部入力は G2（Kraft bound）**。
- **G2 — polynomial n-block Kraft（THE GENUINE NEW BRICK）**。
  `∑ x : Fin n → α, (1/2 : ℝ)^(lz78GreedyImplEncodingLength n x) ≤ (n+1)^K`（固定の小さい `K`）。
  **在庫が見つけた微妙な点**: parse は **complete でない**（`lz78PhraseStrings_flatten_prefix`
  （`GreedyLongestPrefix.lean:243`）: `flatten ++ tail = input`、tail は既存 phrase の非空 prefix に
  なりうる（`lz78PhraseStrings_flatten_tail_mem`、`:290`））。よって
  `lz78GreedyImplEncodingLength = c · bitLength c |α|` は tail を支払わない = lossless code length では
  なく、`∑ 2^{-lz} ≤ 1`（exact Kraft）は **likely FALSE**。正しい bound は polynomial:
  tail-multiplicity ≤ (n+1)、structure-Kraft `∑_{c phrases の LZ78 structures} 2^{-c·bitLength(c,|α|)}`
  は収束（structure count ≤ c!·|α|^c、term `≈ c!/(c+1)^c · 4^{-c} → 0`、sum = O(1)）→ total = O(n) ⟹
  `(n+1)^K`、K 小（K=2 で確実、解析的には O(n) すなわち K=1 でも足りうる）。polynomial slack は G3 の
  `log poly/n → 0` error 項で吸収される（標準的な Barron-with-polynomial-slack）。~150–300 行の genuine
  LZ78 組合せ、**NOT a wall**。
- **G1 — encoder / injectivity scaffolding（G2 の支援）**。G2 が要求する phrase-structure counting /
  `bitLength` decay 補題。既存 `lz78PhraseStrings_nodup`（`GreedyLongestPrefix.lean:125`）/
  `lz78PhraseStrings_flatten_prefix`（`:243`）/ `lz78PhraseStrings_flatten_tail_mem`（`:290`）/
  `LZ78Phrase.bitLength_eq`（`GreedyParsing.lean:115`）を再利用。

### G2 の honesty 配置（load-bearing hypothesis bundling との区別、必読）

G2 は **shared sorry lemma**（honest signature `∑ x, (1/2)^(lz78GreedyImplEncodingLength n x) ≤ (n+1)^K`
を持つ stated-but-unproven 補題、body = `sorry` + `@residual(plan:lz78-m4-plan)`）として
**独立に切り出す**。G3 はこれを **forward reference で消費** する。これは sanctioned
tier-2 パターン（CLAUDE.md「検証の誠実性」+ audit-tags.md tier 2）であって、**load-bearing hypothesis
bundling では断じてない**: 核（Kraft bound）は main theorem `lz78GreedyImpl_converse_ae` の **仮説に
encode されない**（main の signature は `(μ, p)` のまま不変、G2 は独立 lemma の結論であって main の引数では
ない）。各 leg で G2 が sorry のまま残る間も main は `(μ, p)` 仮説のみ — auditor が「結論型 ≡ 仮説型」
循環や `*Hypothesis` predicate を見ない。M1 既存 UD-object converse（`lz78TokenCode_entropyD_le_expectedLength`、
`ConverseUDObject.lean:256`、`entropyD 2 P ≤ E[L] = K`）は **期待値層**で、G2 とは別物（G2 は
per-codeword Kraft の pointwise sum）。

## Phase 詳細

### Phase 0 — M0 在庫確認（流用 + Kraft 用 Mathlib API 追補、proof-log: no）

M2/M3 在庫（`lz78-m3-inventory.md` §A SMB / §B 符号長 / §E Mathlib limsup API）+ achievability で
建った threading / Q_k 資産（[lz78-facts.md](lz78-facts.md) 達成テーブル）が大半を流用可能。**新規在庫は
Kraft brick (G2) 専用の Mathlib API 追補のみ**（`mathlib-inventory` agent に委任、ファイルは
`docs/shannon/*-inventory.md` で本 planner の編集対象外）:

- **first Borel–Cantelli**: `MeasureTheory.ae_eventually_notMem`（verbatim signature + type-class
  prerequisites を要確認）— G3 の a.s. lift の核。
- **Markov / Chebyshev**: 尤度比の期待値上界 → tail 確率（`MeasureTheory.measure_ge_le_lintegral_div`
  系の verbatim 形）。
- **p-series 総和可能**: `Real.summable_one_div_nat_rpow` / `summable_one_div_pow` 系（`∑ 1/n^p` for
  `p > 1`）— Borel–Cantelli の summability 入力。
- **factorial / structure count 上界**: `c! ≤ c^c`、`Nat.factorial` 単調、`(1/2)^…` の幾何級数
  （`tsum_geometric_…`）— G2 structure-Kraft 収束（`∑ c!/(c+1)^c · 4^{-c} = O(1)`）の解析。

**Mathlib-shape-driven 注意**: G2 の結論形は G3 が消費しやすい形（`∑ x : Fin n → α, (1/2:ℝ)^… ≤ (n+1)^K`、
`Finset.sum` over `Fintype (Fin n → α)`、RHS は `(n+1)^K` の plain real）で建てる。`ℝ≥0∞` vs `ℝ` の
unit は G3 の Markov bound（尤度比 = real）に合わせ `ℝ` で統一。

### G4 — liminf assembly + SMB-liminf 配線（leg 1 前半、PURE WIRING、high confidence、proof-log: no）

`algoet_cover_liminf_bound`（nat）を bit 化し、G3 と `Filter.liminf_le_liminf` で連鎖して goal を組む配線。

仮 signature（中間補題、bit 化した liminf 下界）:

```lean
-- bit 化: entropyRate₂ ≤ liminf blockLogAvg₂（nat 版を /log 2 で複写）
theorem entropyRate₂_le_liminf_blockLogAvg₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      entropyRate₂ μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n => blockLogAvg₂ μ p.toStationaryProcess n ω) Filter.atTop := by
  sorry
```

- **供給資産**: `algoet_cover_liminf_bound`（`Liminf.lean:384`、verbatim 確認: 結論 = nat 版 `entropyRate ≤ liminf blockLogAvg`）。`Real.log 2 > 0`（`Real.log_pos`）で両辺除算 → `liminf` を `Filter.liminf_div_const`（または `Tendsto.div_const` 系の liminf 版）で `blockLogAvg₂` の liminf に書換。`shannon_mcmillan_breiman₂`（`:521`）が同じ /log 2 rescaling の先例（手法流用）。
- **最終連鎖**: G3 (`∀ᵐ ω, ∀ᶠ n, blockLogAvg₂ n ω - error_n ≤ L_n/n`) + error_n → 0 + 本補題で `Filter.liminf_le_liminf`（`Mathlib/Order/LiminfLimsup.lean`、verbatim 在庫済 — achievability で `limsup_le_limsup` を使った双対）に乗せ goal `entropyRate₂ ≤ liminf (L_n/n)` を閉じる。cobounded/bounded auto 引数は `lz78_impl_rate_le_const`（上界）+ per-symbol nonneg（下界）で供給（headline `h_bdd_above` 既実証手法、`a1ae108`）。
- **gateway 判定**: G4 が通れば nat↔bit 配線 + liminf 連鎖に想定外コストが無い = M4 tractable のシグナル。**retreat line**: G4 が想定外に詰まった場合のみ goal を `sorry` + `@residual(plan:lz78-m4-plan)` で維持（既存 plan slug 継承、新規 sorry 導入なしなので独立監査不要）。

### G3 — Barron a.s.-eventual lift（leg 1 後半、Z-side テンプレ複写、medium confidence、proof-log: yes）

Z-side の `MRatioLowerZ_le_sq_eventually`（`Liminf.lean:25`）+
`blockLogAvgZ_ge_negLogQInftyZ_minus_error`（`Liminf.lean:98`）の構造を複写。

仮 signature（a.s.-eventual per-n 比較）:

```lean
theorem blockLogAvg₂_le_lz78_rate_plus_error_eventually
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      blockLogAvg₂ μ p.toStationaryProcess n ω
        - errorₙ n   -- = (2 * Real.log n + Real.log poly) / (n * Real.log 2), → 0
      ≤ (lz78GreedyImplEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ) := by
  sorry
```

- **構造（テンプレ複写）**: (1) 尤度比 `R_n(ω) := 2^{-L_n} / P_n(ω)` の Markov bound — `E[R_n] = ∑_x 2^{-L_n(x)} ≤ (n+1)^K`（= G2 を消費）→ `μ(R_n ≥ (n+1)^{K+1}) ≤ (n+1)^{-1}` 等の tail。(2) summable `∑_n (n+1)^{-p}`（p>1、Phase 0 p-series 在庫）→ first Borel–Cantelli（`ae_eventually_notMem`）で `∀ᵐ ω, ∀ᶠ n, R_n(ω) < (n+1)^{K+1}`。(3) log を取り `n` で割って `-log₂ P_n/n - L_n/n ≤ error_n`、すなわち `blockLogAvg₂ - error_n ≤ L_n/n`（`blockLogAvg₂ = (-log₂ P_n)/n` は `ZivEntropyBridge.lean` の `n·blockLogAvg = -log P_n` を /log 2、achievability で verbatim 使用済）。
- **唯一の外部入力 = G2**: 本 brick は G2 の Kraft bound `∑_x 2^{-L_n} ≤ (n+1)^K` だけを forward reference で消費する。それ以外は Z-side テンプレ + Phase 0 Mathlib 在庫。
- **D6 不変条件（再探索禁止、parent §2）**: pointwise `2^{-L_n} ≤ P_n`（Shannon-code 補題、`L_n ≥ shannonLength`）は pointwise FALSE = LZ78 universality の核心。G3 は **期待値（Markov）→ a.s. lift** で、pointwise 不等式を建てない（D6 準拠）。limsup ではなく liminf 形で、error_n を吸収して成立。
- **retreat line**: G3 の Markov/BC 配線が詰まったら、G3 補題の body を `sorry` + `@residual(plan:lz78-m4-plan)` で維持。**G2 は別 lemma として既に sorry を持つので、G3 が一時 sorry でも honesty は G2 の独立 sorry に集約される（bundling 回避）**。

### G2 — polynomial n-block Kraft（後続 leg、THE GENUINE NEW BRICK、medium、proof-log: yes）

`∑ x : Fin n → α, (1/2:ℝ)^(lz78GreedyImplEncodingLength n x) ≤ (n+1)^K`。**shared sorry lemma として
独立切り出し**（honesty 配置 → Approach §G2 honesty 注記）。

仮 signature（shared sorry lemma、honest 結論）:

```lean
/-- Polynomial n-block Kraft bound for the greedy-LZ78 encoding length.
The parse is NOT prefix-complete (`lz78PhraseStrings_flatten_prefix`), so the
exact Kraft sum `≤ 1` is FALSE; tail-multiplicity ≤ (n+1) gives a polynomial
slack absorbed by the Barron error term.
@residual(plan:lz78-m4-plan) -/
theorem lz78_block_kraft_poly [Fintype α] (n : ℕ) :
    ∃ K : ℕ, ∑ x : Fin n → α,
        (1 / 2 : ℝ) ^ (lz78GreedyImplEncodingLength n x) ≤ ((n : ℝ) + 1) ^ K := by
  sorry
```

（`K` を `∃` で持つか固定値 `K=2` で持つかは G1/G2 実装時に確定。G3 が消費しやすいのは固定 `K` 形なので
G3 wiring の都合で `K=2` 固定に振る可能性が高い。）

- **証明戦略（在庫の微妙点を踏まえる）**: (i) Kraft sum を **distinct-phrase 数 `c` でグループ化**: `∑_x 2^{-c(x)·bitLength(c(x),|α|)}`、各 `x` の符号長は `c(x)` のみに依存。(ii) **tail-multiplicity ≤ (n+1)**: parse が complete でないため、同一 phrase structure を持つ input は tail（≤ n+1 通り）の選び方だけ多重度を持つ（`lz78PhraseStrings_flatten_tail_mem` で tail は既存 phrase の prefix = 高々 (n+1) 通り）。(iii) **structure-Kraft 収束**: c phrases を持つ LZ78 structure の数 ≤ `c!·|α|^c`、term `≈ c!/(c+1)^c · 4^{-c} → 0`、`∑_c` は O(1)（幾何級数 + factorial decay、Phase 0 在庫）。(iv) 合成 `total ≤ (n+1)·O(1) = O(n) ⟹ (n+1)^K`（K=2 で確実）。
- **D1/D2/D3 不変条件（parent §2、抵触チェック）**: G2 は Kraft sum 上界であって per-block `c·log c ≤ -log P_n`（D1/D2 FALSE）でも node-position-grouping（D3）でもない。structure count `c!·|α|^c` は LZ tree node 数とは別軸（symbol-by-symbol structure enumeration）なので D3 trap（#nodes≈c）に該当しない。
- **数値予測の verbatim 確認義務（CLAUDE.md）**: `lz78GreedyImplEncodingLength = c · bitLength c |α|` と `bitLength_eq`（`GreedyParsing.lean:115`、`bitLength c a = Nat.log 2 (c+1) + Nat.log 2 a + 2`）は verbatim 確認済。structure count `c!·|α|^c` と term decay `c!/(c+1)^c·4^{-c}` は **G2 実装の最初の step で small-case（n=2,3）数値裏取り**してから本証明に入る（in-tree `lz78PhraseStrings` を `decide`/`#eval` で小ケース展開、`(n+1)^K` の K=1 で足りるか K=2 必要かを実測で確定）。`∑ 2^{-lz} ≤ 1`（exact Kraft）が FALSE という在庫主張も同じ small-case で counterexample 確認（n=2, A=2 で parse incomplete を実演）。
- **retreat line**: G2 が ~300 行を超えても閉じない場合のみ `sorry` + `@residual(plan:lz78-m4-plan)` で tier-2 維持（shared sorry lemma として既に切り出し済なので structural retreat は確保）。**新規 sorry 導入時は独立 honesty audit を起動**（CLAUDE.md「Independent honesty audit」: G2 は新 shared sorry lemma、orchestrator は honesty-auditor を dispatch）。

### G1 — encoder / injectivity scaffolding（G2 と並行、G2 支援、proof-log: no）

G2 が要求する phrase-structure counting / `bitLength` decay 補題群。スコープは G2 実装中に確定するが、
想定される atom:

- structure enumeration injection: c phrases を持つ parse の数え上げ（`lz78PhraseStrings_nodup`、
  `GreedyLongestPrefix.lean:125` を再利用 — distinct phrases は injective enumeration の必要条件）。
- tail-multiplicity bound: `lz78PhraseStrings_flatten_prefix`（`:243`）+ `lz78PhraseStrings_flatten_tail_mem`
  （`:290`）から tail ∈ {既存 phrase の prefix} ⟹ 多重度 ≤ (n+1)。
- `bitLength` 単調 / decay: `LZ78Phrase.bitLength_eq`（`GreedyParsing.lean:115`）+ `c·bitLength c |α|` の
  `c` 単調（achievability `lz78_impl_rate_le_const` の手法流用）。

**novel か**: 大半は achievability で建った List 補助 + 既存 phrase 不変量の組み合わせ。genuine な新規は
structure-count enumeration の injection 構成のみ（G2 と同 leg で扱う）。

### M5 — 最終合成 + headline sorryAx-free 判定（capstone、低リスク、proof-log: no）

G4 が goal `lz78GreedyImpl_converse_ae` を sorryAx-free 化（G2/G3/G1 が全 sorryAx-free 前提）した時点で、
headline `lz78_asymptotic_optimality_with_greedy_impl`（`:1090`、`@[entry_point]`）の squeeze が完成。
`#print axioms lz78_asymptotic_optimality_with_greedy_impl = [propext, Classical.choice, Quot.sound]`
（sorryAx 非依存）を確認 = **標準B 完遂**。`h_bdd_above` 内製化は済（`a1ae108`、完遂条件から除外）。
配線のみ（~50–100 行、parent §1 M5）。

## leg ordering（推奨着手順）

1. **leg 1 = G4 配線 + G3 テンプレ複写 + G2 isolate**: G4（high）で nat↔bit 配線が plumbing 級か gateway
   確認。G3（medium）を Z-side テンプレ複写で建て、**G2 は shared sorry lemma として isolate**（body sorry +
   `@residual`、forward reference）。この leg 終了時点で goal は G2 1 本の sorry に transitive 依存する状態
   （main signature 不変、honest tier-2）。
2. **leg 2+ = G2 discharge**（G1 scaffolding 並行）: polynomial Kraft brick の genuine 証明。small-case
   数値裏取り → structure-Kraft 収束 → tail-multiplicity → 合成。新規 shared sorry なので独立 honesty
   audit 起動。
3. **leg 最終 = M5 capstone**: G2 sorryAx-free 後、headline `#print axioms` で完遂判定。

## 地雷の不変条件（再探索禁止、parent §2 から本 plan 関連分）

- **D6**: converse の pointwise `2^{-L_n} ≤ P_n`（`L_n ≥ shannonLength`）は **pointwise FALSE** =
  LZ78 universality の核心。→ G3 は **期待値（Markov）→ a.s. lift**、pointwise 不等式を建てない。
- **D1/D2**: per-block `c·log c ≤ -log P_n`（clean / overhead）は **FALSE**（反例 `a^16` / `P_n→1`）。→
  G2 は Kraft sum 上界（per-codeword 和）であって per-block combinatorial bound ではない（別物、抵触なし）。
- **D3**: node-position-grouping overhead 非 vanish。→ G2 の structure count は symbol-by-symbol
  enumeration（`c!·|α|^c`）であって LZ tree node-position grouping ではない（抵触なし）。
- **exact Kraft `∑ 2^{-lz} ≤ 1` は likely FALSE（在庫発見、新地雷候補）**: parse が complete でない
  （`lz78PhraseStrings_flatten_prefix`: `flatten ++ tail = input`、tail 非空ありうる）ため、tail を支払わない
  符号長で exact Kraft を狙うと詰まる。→ G2 は **polynomial Kraft `≤ (n+1)^K`** で建てる（slack は G3 の
  `log poly/n → 0` で吸収）。G2 実装の最初に small-case で exact Kraft の counterexample を確認すること。

## 撤退ライン（honest tier-2 退出口、hypothesis bundling 禁止）

- **唯一の sanctioned 退出口 = `sorry` + `@residual(plan:lz78-m4-plan)`**（本 plan で closure 予定の
  plan-class residual、achievability 完遂後 headline 残課題の SoT）。G4/G3 が詰まれば該当 brick の body を
  sorry で維持、G2 が ~300 行超で閉じなければ G2 shared sorry lemma を tier-2 維持。
- **bundling 禁止（CLAUDE.md「検証の誠実性」）**: G2 の核（Kraft bound）を main `lz78GreedyImpl_converse_ae`
  の `*Hypothesis` 仮説に encode しない。main の signature は `(μ, p)` + `[IsProbabilityMeasure μ]` regularity
  のみ不変。G2 は **独立 lemma の結論** であって main の引数ではない（forward reference 消費）。
- **slug 整合**: コード側の `@residual` は honesty-auditor が overturn された旧 wall 判定（converse
  a.s.-eventual の壁分類）から `plan:lz78-m4-plan` へ reclassify 済（wall ではなく plan-tracked
  combinatorial residual）。plan-class slug は本 plan filename stem `lz78-m4-plan` と一致する（CLAUDE.md
  closure plan 規約）。G2 が genuine に sorryAx-free で閉じれば residual は除去され `@audit:ok` 化される。

## 規模・リスク総括

- **総計**: G4（high、~30–60 行配線）+ G3（medium、~80–150 行テンプレ複写）+ G2（medium、~150–300 行
  genuine Kraft）+ G1（~50–100 行 scaffolding）+ M5（低、~50–100 行）。dominant 残作業 = G2 のみ。
- **最大リスク = G2 polynomial Kraft の structure-count enumeration**（medium）。在庫が parse incomplete を
  踏まえた polynomial slack 設計を提示済なので、exact Kraft の dead-end は回避済。ergodic machinery は
  全て既存（リスク無し）。
- **verdict 再確認義務**: 本 plan は読み取り在庫（`human-judgment`）に基づく overturn なので、leg 1 で
  G4 gateway（nat↔bit 配線 = plumbing か）+ G2 small-case 数値裏取り（exact Kraft FALSE / polynomial K の
  実測）の 2 点で機械裏取りし、`human-judgment` を `machine` 系に格上げする（[lz78-facts.md](lz78-facts.md)
  壁テーブルの再評価注記と同期）。

## 判断ログ

1. **M4 verdict OVERTURN（2026-06-21、読み取り在庫）**: parent §1 M4 / コード docstring の
   「research-level エルゴード壁・scope-out」を反証。M4 = **既存 sorry-free 資産配線（G4 SMB-liminf / G3
   Z-side テンプレ）+ 1 genuine brick（G2 polynomial Kraft）で closeable**。ergodic machinery
   （`algoet_cover_liminf_bound`、Z-side Barron テンプレ、Q_k AEP）は全て既存。dominant 残 = G2 のみ
   （~150–300 行）。cause:single-route（「Barron lift 全体が research-level」という単一 framing 過大評価）+
   gateway-atom-untried（G4 配線 atom も G2 brick も未 dispatch のまま壁宣言されていた）。confidence は
   依然 `human-judgment` → leg 1 で機械裏取り予定。
2. **exact Kraft `∑ 2^{-lz} ≤ 1` は likely FALSE（在庫発見）**: parse incomplete
   （`lz78PhraseStrings_flatten_prefix`: `flatten ++ tail = input`、tail 非空ありうる）ゆえ符号長は tail を
   支払わない = lossless でない。→ polynomial Kraft `≤ (n+1)^K` に設計し、slack を G3 error 項
   `log poly/n → 0` で吸収（標準 Barron-with-polynomial-slack）。G2 実装の最初に small-case で counterexample
   確認（CLAUDE.md 数値予測 verbatim 確認義務）。
3. **G2 は shared sorry lemma で isolate（bundling 回避）**: G2 を main の `*Hypothesis` 仮説に入れず、
   独立 lemma `lz78_block_kraft_poly` の結論として切り出し G3 が forward reference で消費。main signature は
   `(μ, p)` 不変。これは tier-2 sanctioned（stated-but-unproven lemma）であって load-bearing bundling では
   ない（auditor 区別軸: 核が main の仮説に乗るか否か → 乗らない）。
4. **ripple ゼロ（要・leg 1 機械確認）**: `lz78GreedyImpl_converse_ae` の direct consumer は headline
   `lz78_asymptotic_optimality_with_greedy_impl`（`:1090`）の squeeze 下半分のみと想定。leg 1 着手時に
   `scripts/dep_consumers.sh InformationTheory.Shannon.lz78GreedyImpl_converse_ae` で機械確認し、本 plan が
   body を埋めるだけで signature 不変 = ripple ゼロを裏取りする（achievability W2 と同型の運用）。

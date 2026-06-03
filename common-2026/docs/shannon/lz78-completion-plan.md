# T4-A LZ78 漸近最適性 — 標準B完遂 実装サブ計画 🌙

> **Parent**:
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md) §「撤退ライン L-LZ1 (Ziv inequality) / L-LZ2 (converse)」
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. LZ78 漸近最適性」(Cover–Thomas Ch.13.5, Thm 13.5.3)
>
> **Supersedes (一部)**: [`lz78-residual-discharge-plan.md`](./lz78-residual-discharge-plan.md)
> — 当該 plan の Phase Z4 (parsing factorization) と Phase C2/C3 (Kraft) は本セッションの Read 確認で
> **既に genuine 完成済** と確定 (下記 §Context)。残るのは当該 plan が想定していなかった精緻な 2 core
> (distinct-phrase 組合せ Ziv + averaged Kraft converse) のみ。residual-discharge plan は archive 扱い
> (削除しない、設計の prior として参照)。
>
> **Goal (短形)**: base-2 distinct headline `lz78_two_sided_optimality_distinct_genuine`
> (`InformationTheory/Shannon/LZ78AchievabilityLimsup.lean:233`) が現在 honest 入力として受ける
> **2 named primitive** を genuine に discharge し、無仮定の base-2 headline を publish。
> **標準B (無条件機械検証)**、**0 sorry / 0 warning**、`#print axioms` で sorryAx 非依存維持。

## Status (2026-05-21)

> **本 plan 起草時の実態整合 (Read 確認済)**:
>
> 1. **foundation は genuine 完成済 (sorryAx 非依存)**。base-2 headline
>    `lz78_two_sided_optimality_distinct_genuine` (`LZ78AchievabilityLimsup.lean:233`) は **2 named
>    honest primitive を引数に取る** 形で既に組まれ、limsup/liminf assembly・base-2 SMB・sandwich
>    (`tendsto_of_le_liminf_of_limsup_le`)・boundedness は全 genuine。残りは **2 primitive のみ**:
>    - **Core 1** `IsLZ78AchievabilityZivUpperBound` (`LZ78AchievabilityLimsup.lean:114`, structure)
>    - **Core 2** `IsLZ78ConverseCodingLowerBound` (`LZ78ConverseKraft.lean:107`, structure)
>
> 2. **telescoping 層は完成済**。`StationaryKernel.lean` の `prod_condPhraseProb_telescope` (`:73`)
>    + `blockProb_le_prod_condPhraseProb` (`:200`、Ziv 方向不等式 `Pₙ ≤ ∏ⱼ qⱼ`、prefix monotonicity
>    `prefixBlockProb_antitone` `:157` で無条件) + `isLZ78PerPathParsingFactorization_of_pos` (`:255`、
>    a.s. regularity から factorization 構成) は全 genuine。**residual-discharge plan の Phase Z4
>    (cylinder 手組み factorization) は不要 — 既に解決済**。
>
> 3. **factorization → 加法 log 形も genuine**。`blockProb_neg_log_ge_sum`
>    (`LZ78ZivEntropyBridge.lean:225`) が `∑ⱼ -log(condPhraseProb) ≤ -log Pₙ` を `0 < Pₙ` (regularity)
>    の下で genuine に与える。
>
> 4. **base-2 単位訂正は完了済 (弱化でない)**。`entropyRate₂ = entropyRate/Real.log 2`,
>    `blockLogAvg₂ = blockLogAvg/Real.log 2` (`LZ78ZivEntropyBridge.lean:267,:274`)。LZ78 code 長は
>    bit (`LZ78Phrase.bitLength` は `Nat.log 2`)、SMB は nat-log。**係数 1/log2 の単位修正であり、
>    弱化ではない**。`shannon_mcmillan_breiman₂` (`LZ78ConverseKraft.lean:133`) は base-2 SMB 収束を
>    genuine に与える。
>
> 5. **counting 層は genuine、ただし `c·log c ≤ K·n` であり `-log Pₙ` ではない**。
>    `lz78PhraseStrings_mul_log_le` (`LZ78ZivCountingBody.lean:353`) が `c·log c ≤ 8·log(|α|+1)·n` を
>    genuine に与える (constant rate `K`)。**これは Ziv 上界 `c·log c ≤ -log Pₙ` ではない** —
>    Core 1 の crux は両者を繋ぐ組合せ論 (下記 §Approach Core 1)。

## 進捗

- [ ] Phase 0 — 着手前 signature / 既存 genuine 資産の verbatim 再確認 📋
- [ ] Phase C1 — `IsLZ78ConverseCodingLowerBound` skeleton + averaged-Kraft 設計確定 📋
- [ ] Phase C2 — block pushforward の Kraft 充足 `blockKraftSum_le_one` (Core 2 crux 1) 📋
- [ ] Phase C3 — averaged converse coding 下界 (expectation-level Kraft → Birkhoff a.s. lift, Core 2 真の crux) 📋
- [ ] Phase C4 — `isLZ78ConverseCodingLowerBound_distinct` (per-path slack 形 assembly, Core 2 解除目標) 📋
- [ ] Phase Z1 — `IsLZ78AchievabilityZivUpperBound` skeleton + distinct-stratum 設計確定 📋
- [ ] Phase Z2 — per-stratum sub-distribution `condPhraseProb_stratumSum_le_one` (Core 1 真の crux) 📋
- [ ] Phase Z3 — distinct-phrase Ziv 核心 `ziv_count_mul_log_le_neg_log_blockProb` (`c·log₂c ≤ -log₂Pₙ`) 📋
- [ ] Phase Z4 — `isLZ78AchievabilityZivUpperBound_distinct` (per-path slack 形 assembly, Core 1 解除目標) 📋
- [ ] Phase V — 無仮定 base-2 headline publish + `#print axioms` + clean check 📋

## ゴール / Approach

### 最終到達点 (Phase V 完成形)

base-2 headline (`LZ78AchievabilityLimsup.lean:233`) の 2 primitive を genuine 定理で供給した
無仮定系を新規 publish (slack 関数は内部構成):

```lean
namespace InformationTheory.Shannon

/-- **T4-A 無仮定 base-2 distinct headline (Cover–Thomas Thm 13.5.3, 標準B)**: ergodic process on
a finite alphabet について、distinct LZ78 encoding の per-symbol bit-rate は a.s. base-2 entropy
rate `entropyRate₂ = entropyRate / log 2` に収束する。2 primitive (bit-based Ziv 上界 Eq.13.124 /
averaged converse 下界 Eq.13.130) は内部で genuine discharge 済。 -/
theorem lz78_two_sided_optimality_distinct
    {α Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α)
    (hreg : ∀ (n : ℕ) (ω : Ω) (m : ℕ), m ≤ n → 0 < prefixBlockProb μ p.toStationaryProcess ω m) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n => (lz78DistinctEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 (entropyRate₂ μ p.toStationaryProcess)) :=
  lz78_two_sided_optimality_distinct_genuine μ p _ _
    (isLZ78AchievabilityZivUpperBound_distinct μ p hreg)   -- Phase Z4
    (isLZ78ConverseCodingLowerBound_distinct μ p hreg)     -- Phase C4

end InformationTheory.Shannon
```

**許容仮説の判定** — `hreg` (full-support cylinder 正値) は **regularity 仮説** であり標準B で許容
(CLAUDE.md「regularity hyp (full-support / `IsFiniteMeasure` 等) は OK」)。既に
`isLZ78PerPathParsingFactorization_of_pos` (`StationaryKernel.lean:255`) が同型の `hreg` を取る
genuine 定理として publish 済 — 同じ regularity 入力を headline まで透過させるだけ。**これは load-bearing
ではない** (full-support は ergodic source の典型的整合条件、証明の核心を肩代わりしない)。Core 1/Core 2 の
真の核心 (組合せ Ziv / averaged Kraft) は `hreg` の有無に関わらず証明が要る。

> **設計上の分岐 (Phase 0 で確定)**: `hreg` を headline 引数に残すか、`isLZ78PerPathParsingFactorization_of_pos`
> 同様 a.s. 化 (`∀ᵐ ω, ...`) して `μ`/ergodicity から内部 discharge するか。後者が可能なら無条件 headline。
> ただし full-support は a.s. でも一般には成り立たない (退化分布で 0 質量 cylinder あり) ため、**`hreg` を
> 明示 regularity 仮説として残すのが honest** (退化 source を除外する整合条件)。Phase 0 で a.s. 化の
> 可否を判定し、不可なら `hreg` 明示を確定。

### Approach (overall strategy / shape of solution)

**全体戦略 = 既存 genuine foundation (telescoping + base-2 + SMB + assembly) の上に、2 primitive を
それぞれの真の crux で genuine 構成して headline に注入**。2 primitive は完全独立 (Core 1 = 組合せ Ziv、
Core 2 = averaged Kraft、共有 crux なし)。着手順は **Core 2 (converse) 先行を推奨** (Kraft + Birkhoff
資産が厚い、ROI が高い、honest 入力を確実に 2→1)。

```
        lz78_two_sided_optimality_distinct (Phase V, 無仮定 + hreg regularity)
                          │
        ┌──────────────────┴──────────────────┐
   Core 1 (Eq.13.124)                  Core 2 (Eq.13.130)
   IsLZ78AchievabilityZivUpperBound    IsLZ78ConverseCodingLowerBound
   upper: lz/n ≤ blockLogAvg₂ + slack  lower: blockLogAvg₂ − slack ≤ lz/n
        │ Phase Z2–Z4                       │ Phase C2–C4
        │                                  │
   ┌────┴──────────────┐            ┌──────┴───────────────────┐
 distinct-stratum Ziv   既存 genuine  averaged Kraft 下界        既存 genuine
 c·log₂c ≤ -log₂Pₙ      foundation:  -log₂Pₙ 期待値 ≤ E[lz]      foundation:
 (sub-distrib が crux)  ・telescoping (expectation→a.s. が crux) ・Birkhoff a.s.
        │              ・blockProb_neg_log     │               ・base-2 SMB
        │               _ge_sum (genuine)      │               ・shannon_mcmillan
 per-stratum            ・log_sum_inequality    │                _breiman₂ (genuine)
 ∑ qⱼ ≤ 1 (Z2, ★crux)  ・c·log c ≤ K·n         block Kraft 充足 (C2)
        │               (counting, genuine)    + Birkhoff lift (C3, ★crux)
        └─ Z3: 組合せ Ziv 合流 ──┘
```

#### なぜ telescoping の罠が回避されているか (起草時の重要確認)

タスク記述の「telescoping の条件付き `qⱼ = condPhraseProb` は path 沿いの和が ≈ c (1 でない) ため
`Pₙ ≤ ∏qⱼ` から log-sum で直接は出ない」という罠は **既に foundation で正しく扱われている**:

- foundation が与えるのは `∑ⱼ -log qⱼ ≤ -log Pₙ` (`blockProb_neg_log_ge_sum`, genuine)。これは
  **積方向の telescoping** であり、Ziv 不等式 `c·log c ≤ -log Pₙ` を直接出すものではない。
- Ziv 不等式の真の核心は「**distinct phrases を SET として扱う組合せ論**」: c 個の phrase が distinct
  (`lz78PhraseStrings_nodup`) であることを使い、各 stratum (= 同じ context prefix を持つ phrase の集合)
  内で `∑ qⱼ ≤ 1` (sub-distribution) を立て、log-sum 不等式 (`log_sum_inequality`,
  `LZ78ZivEntropyBridge.lean:69`、genuine) を **stratum 別に** 適用する。これが Cover–Thomas 13.5.5 の
  original argument。
- **罠の正体**: 全 path 沿いに 1 本の log-sum を打つと `∑ qⱼ ≈ c ≠ 1` で破綻する。**stratum 別に
  分解してから** log-sum を打てば各 stratum で `∑ qⱼ ≤ 1` が立ち破綻しない。Core 1 の Phase Z2 が
  この per-stratum sub-distribution を立てる唯一の crux。

#### Core 1 の証明 route 判定 (最重要報告事項)

タスクが提示した route 候補 (a)/(b)/(c) を支配補題の conclusion form verbatim 確認に基づき判定:

- **route (b) 「既存 counting `c·log c ≤ K·n` を `-log Pₙ` に接続する bridge」は不採用**。
  `lz78PhraseStrings_mul_log_le` (`LZ78ZivCountingBody.lean:353`) の conclusion は verbatim
  `(↑c) * Real.log ↑c ≤ 8 * Real.log (↑(Fintype.card α) + 1) * ↑input.length`。RHS は **`K·n`
  (constant rate K)** であり `-log Pₙ` ではない。`-log Pₙ` は分布依存量、`K·n` は分布非依存の最悪値。
  両者を等式/不等式で繋ぐ bridge は **存在しない** (異なる量)。counting 層は `c = O(n/log n)` envelope
  (boundedness、既に headline で使用済) には効くが、Ziv 上界の主項には効かない。

- **route (a)/(c) 「distinct phrases を stratum 別に log-sum」が genuine route**。これが Cover–Thomas
  13.5.5 の original argument (route (c)) と log-sum 評価 (route (a)) の合流。foundation の
  `log_sum_inequality` (genuine) + `blockProb_neg_log_ge_sum` (genuine) を、**per-stratum
  sub-distribution `∑ qⱼ ≤ 1` (Phase Z2、未構築)** で繋ぐ。Phase Z2 が成れば Z3 は既存 genuine 資産の
  合流で閉じる。

- **`Pₙ ≤ ∏qⱼ` は使える**。foundation が `∑ⱼ -log qⱼ ≤ -log Pₙ` (= `Pₙ ≤ ∏qⱼ` の log 形) を
  genuine に与えており、これは Z3 で消費する。**別の decomposition は要らない** — 必要なのは
  右辺 `∑ⱼ -log qⱼ` を下から `c·log c` で評価する per-stratum log-sum のみ。

**判定 (feasibility)**: Core 1 の真の crux は **Phase Z2 の per-stratum sub-distribution
`∑_{j∈stratum} condPhraseProb ≤ 1` 一点**。これは「同じ context を持つ次 symbol 候補は alphabet 上の
条件付き分布 → 和 ≤ 1」という測度論的事実。`condPhraseProb = prefixBlockProb(b(j+1))/prefixBlockProb(b(j))`
の定義 (`LZ78ZivEntropyBridge.lean:164`) から、同 context の分子 cylinder 群が互いに素で union が
分母 cylinder に含まれる (`measureReal` の有限加法性 + monotonicity) ことで立つ見込み。**genuine に
閉じる確度は中** — cylinder の互いに素性を `blockRV` 射影の prefix 構造から組む必要があり、~150-300 行。
閉じなければ Phase Z2 を isolated honest hyp に縮退 (撤退ライン [L-Z2])、その場合 Core 1 全体が honest
入力 1 本として明示的に残る (現状の `IsLZ78AchievabilityZivUpperBound` より primitive な deferral)。

#### Core 2 の converse chain (averaged Kraft + Birkhoff lift)

`IsLZ78ConverseCodingLowerBound` (`LZ78ConverseKraft.lean:107`) の `lower` field
`∀ᵐ ω, ∀ᶠ n, blockLogAvg₂ μ p n ω − slack n ≤ (lz n (blockRV n ω))/n` を genuine 構成。
**chain は具体補題列で**:

1. **block pushforward の Kraft 充足** (Phase C2): LZ78 distinct encoding が prefix-free
   (uniquely decodable) であることから、block 測度 `Pₙ = μ.map (blockRV n)` 上で codeword 長が
   Kraft を充足。**設計選択 (Phase 0 で確定)**: McMillan (uniquely decodable → Kraft) は Mathlib 不在
   なので、`shannonLength_kraft_le_one` (`ShannonCode.lean:129`) を block pushforward に適用する
   Shannon-code 代用で Kraft 充足を確保 (residual-discharge plan の L-LZ2-K1 と同設計)。
2. **expectation-level converse coding** (Phase C3 前半): `entropyD_le_expectedLength_of_kraft`
   (`ShannonCode.lean:164`) — verbatim conclusion `entropyD D P ≤ expectedLength P l`、前提
   `[IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a}) (h_kraft : kraftSum D l ≤ 1)`。block
   pushforward `Pₙ` に適用すると `H_D(Pₙ) ≤ E_x∼Pₙ[lz(x)]` (期待値版下界)。`H_D(Pₙ)` は
   `∑ -log₂ Pₙ{x}·Pₙ{x}` = block entropy in bits。
3. **Birkhoff a.s. lift** (Phase C3 後半、★crux): 期待値版 `H_D(Pₙ)/n ≤ E[lz/n]` を a.s.
   pointwise `blockLogAvg₂ − slack ≤ lz/n` に持ち上げる。**観測量の選択**: `f(ω) = lz_1(blockRV_1 ω)`
   (1-block coding 長) ではなく、`blockLogAvg₂` 自体が SMB で a.s. 収束する事実 + 期待値下界の
   Cesàro/Birkhoff 平均で繋ぐ。具体的には Cover–Thomas 13.130 の averaged form を、`birkhoff_ergodic_ae`
   (`BirkhoffErgodic.lean:1031`、verbatim `∀ᵐ ω, Tendsto (birkhoffAverageReal T f n ω) atTop (𝓝 (∫ f))`)
   で時間平均に lift。**重要 honesty 注記**: pointwise `2^{-lz}≤Pₙ` (Shannon-code 補題) は
   **不健全につき不採用** (`lz≥shannonLength` は pointwise 偽、LZ78 は Shannon code を pointwise で破る)。
   採るのは **averaged (expectation→a.s.) 経路一択**。

> **Core 2 の Birkhoff 適用形 (Phase 0 で精密化)**: averaged converse は本質的に「`E[lz_n/n] ≥ H_D(Pₙ)/n
> = E[blockLogAvg₂]」(expectation-level) + 「lz/n と blockLogAvg₂ が共に a.s. 収束 (boundedness 既知)」
> の組合せ。最も筋が良いのは:
> (i) C2/C3 で各 n の expectation-level `E[blockLogAvg₂_n] ≤ E[lz_n/n] + O(1/n)` を Kraft から立て、
> (ii) lz/n の a.s. limit (= entropyRate₂, headline の他半分から) と blockLogAvg₂ の a.s. limit (SMB) の
>      一致を Fatou/Birkhoff で繋ぎ per-path slack 形に落とす。
> あるいは Birkhoff を **直接** `f = -log₂(1-block 条件付き確率)` に当てる per-letter 経路。Phase 0 で
> どちらが既存資産 (`shannon_mcmillan_breiman₂` + `entropyD_le_expectedLength_of_kraft` + `birkhoff_ergodic_ae`)
> で gap 最少かを確定。

**判定 (feasibility)**: Core 2 の真の crux は Phase C3 の **expectation→a.s. lift** (averaged Kraft 下界の
per-path slack 化)。Kraft 充足 (C2) は Shannon-code 代用で確実、expectation-level 下界
(`entropyD_le_expectedLength_of_kraft`) は genuine reuse。a.s. lift は Birkhoff + base-2 SMB が揃って
おり **genuine に閉じる確度は中〜高** (~200-400 行)。full-support hyp は `hreg`/a.s. で regularity 範疇。
閉じなければ C3 を isolated honest hyp に縮退 (撤退ライン [L-C3])。

#### Mathlib-shape-driven の設計選択 (結論側を変えない)

2 primitive の structure 定義 (`IsLZ78AchievabilityZivUpperBound` の `upper`/`slack_tendsto` field、
`IsLZ78ConverseCodingLowerBound` の `lower`/`slack_tendsto` field) と headline
`lz78_two_sided_optimality_distinct_genuine` の signature は **一切変えない**。本 plan は新規 primitive を
導入せず、これら structure の field を満たす定理を distinct encoding について genuine に構成し、headline
引数から外す。`slack` 関数は本 plan 内で具体構成 (Core 1 は bit-length O(1) 項 + counting envelope、
Core 2 は Kraft の O(1/n) 整数化 gap)。

### 規模見積

| Phase | 中央 | 範囲 | 出力 | proof-log |
|---|---|---|---|---|
| Phase 0 | — | — | 着手前確認 (新規 file 起草なし) | no |
| Phase C1 | **60 行** | 40–90 | `LZ78ConverseAveraged.lean` skeleton (converse 群 `:= by sorry`) | no |
| Phase C2 | **120 行** | 80–200 | `blockKraftSum_le_one` (Shannon-code 代用 block Kraft 充足) | yes |
| Phase C3 | **300 行** | 200–450 / 撤退時 ~15 行 | averaged Kraft → Birkhoff a.s. lift (★crux) | yes |
| Phase C4 | **100 行** | 60–160 | `isLZ78ConverseCodingLowerBound_distinct` (per-path slack assembly) | yes |
| Phase Z1 | **60 行** | 40–90 | `LZ78ZivCombinatorics.lean` skeleton (achiev 群 `:= by sorry`) | no |
| Phase Z2 | **220 行** | 150–350 / 撤退時 ~15 行 | `condPhraseProb_stratumSum_le_one` (per-stratum sub-distrib、★crux) | yes |
| Phase Z3 | **180 行** | 120–300 | `ziv_count_mul_log_le_neg_log_blockProb` (組合せ Ziv 合流) | yes |
| Phase Z4 | **120 行** | 80–200 | `isLZ78AchievabilityZivUpperBound_distinct` (per-path slack assembly) | yes |
| Phase V | **30 行** | 20–50 | headline publish + `#print axioms` + import | no |
| **累計** | **~1190 行** | **790–1890** | 2 新規 file + import + headline | — |

### ファイル構成

```
InformationTheory/Shannon/
  LZ78ConverseAveraged.lean    ← 新規 (~580 行) — Core 2 群
                                 ・blockKraftSum_le_one                        (C2, Shannon-code 代用)
                                 ・(def blockShannonLength? — C2/C3 設計次第)
                                 ・averaged converse coding 下界 + Birkhoff lift (C3, ★crux)
                                 ・isLZ78ConverseCodingLowerBound_distinct      (C4, per-path slack)
  LZ78ZivCombinatorics.lean    ← 新規 (~580 行) — Core 1 群
                                 ・(def parsingStratum? — Z2 stratum 構造次第)
                                 ・condPhraseProb_stratumSum_le_one             (Z2, ★crux)
                                 ・ziv_count_mul_log_le_neg_log_blockProb       (Z3, 組合せ Ziv)
                                 ・isLZ78AchievabilityZivUpperBound_distinct    (Z4, per-path slack)
  LZ78AchievabilityLimsup.lean ← (Phase V) 無仮定 headline 別名を追記 (任意、既存定理は不変)
  InformationTheory.lean              ← import 2 行追記
```

---

## Phase 0 — 着手前 signature / 既存 genuine 資産の verbatim 再確認 📋

本 plan + Read で大枠確定済。**着手前に実装者が再確認する事項** (signature drift / 仮定漏れ / honesty):

- [ ] **2 primitive structure の field verbatim** (Phase Z4 / C4 の target):
      - `IsLZ78AchievabilityZivUpperBound` (`LZ78AchievabilityLimsup.lean:114`): field
        `upper : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, (lz n (blockRV n ω))/n ≤ blockLogAvg₂ μ p n ω + slack n` +
        `slack_tendsto : Tendsto slack atTop (𝓝 0)`。
      - `IsLZ78ConverseCodingLowerBound` (`LZ78ConverseKraft.lean:107`): field
        `lower : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, blockLogAvg₂ μ p n ω − slack n ≤ (lz n (blockRV n ω))/n` +
        `slack_tendsto`。
- [ ] **既存 genuine foundation の verbatim conclusion (黒箱 reuse、signature 不変)**:
      - `blockProb_neg_log_ge_sum` (`LZ78ZivEntropyBridge.lean:225`): `∑ⱼ -log(condPhraseProb …) ≤
        -log Pₙ{block ω}` (前提 `IsLZ78PerPathParsingFactorization μ p` + `0 < Pₙ`)。
      - `isLZ78PerPathParsingFactorization_of_pos` (`StationaryKernel.lean:255`): 前提
        `hreg : ∀ n ω m, m ≤ n → 0 < prefixBlockProb μ p ω m` → `IsLZ78PerPathParsingFactorization μ p`。
      - `blockLogAvg_eq_neg_log_blockProb` (`LZ78ZivEntropyBridge.lean:123`): `0 < n` で
        `(n:ℝ)·blockLogAvg μ p n ω = -log Pₙ{block ω}`。
      - `log_sum_inequality` (`LZ78ZivEntropyBridge.lean:69`): 前提 `(∀ i∈s, 0 ≤ a i) (∀ i∈s, 0 < b i)`、
        結論 `(∑ a)·log((∑a)/(∑b)) ≤ ∑ aᵢ·log(aᵢ/bᵢ)`。
      - `condPhraseProb` def (`LZ78ZivEntropyBridge.lean:164`): `prefixBlockProb (b(j+1)) /
        prefixBlockProb (b j)`。`parsingBoundary` (`:139`) / `prefixBlockProb` (`:147`)。
      - base-2 層: `blockLogAvg₂` (`:267`) / `entropyRate₂` (`:274`) / `shannon_mcmillan_breiman₂`
        (`LZ78ConverseKraft.lean:133`) / `log_two_pos` (`LZ78ZivEntropyBridge.lean:261`)。
- [ ] **counting 層 (boundedness 専用、Ziv 主項には効かない)**: `lz78PhraseStrings_mul_log_le`
      (`LZ78ZivCountingBody.lean:353`) の conclusion verbatim `↑c·log↑c ≤ 8·log(↑|α|+1)·↑input.length`
      = **`K·n`、`-log Pₙ` ではない** ことを再確認 (route (b) 不採用の根拠)。
      `lz78DistinctEncodingLength_eq` (`LZ78DistinctEncoding.lean:133`): `lz n x = c·bitLength c |α|`。
      `lz78PhraseStrings_nodup` (`LZ78GreedyLongestPrefix.lean:126`) / `_count_le` (`:260`、`c ≤ input.length`)。
- [ ] **Kraft 資産 3 件の verbatim signature + `[...]` typeclass + full-support hyp** (Phase C2/C3):
      - `entropyD_le_expectedLength_of_kraft` (`ShannonCode.lean:164`):
        `{D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
        (l : α → ℕ) (h_kraft : kraftSum D l ≤ 1) : entropyD D P ≤ expectedLength P l`
        — **expectation-level + full-support `hP`**。a.s.-lift が C3 の crux。
      - `shannonLength_kraft_le_one` (`ShannonCode.lean:129`): `{D} (hD : 1 < D) (P) [IsProbabilityMeasure P]
        (hP : ∀ a, 0 < P.real {a}) : kraftSum D (shannonLength D P) ≤ 1`。
      - `rpow_neg_shannonLength_le_real` (`ShannonCode.lean:106`): `(D) (hD : 1 < D) (P) {a} (ha : 0 < P.real {a})
        : D^(-(shannonLength D P a)) ≤ P.real {a}` (**pointwise だが Shannon-code、converse pointwise には
        使わない**)。`kraftSum`/`expectedLength`/`entropyD`/`shannonLength` def (`:59,:55,:45,:51`)。
- [ ] **Birkhoff main の verbatim** (Phase C3): `birkhoff_ergodic_ae` (`BirkhoffErgodic.lean:1031`):
      `{μ} [IsProbabilityMeasure μ] {T} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ) {f}
      (hf : Integrable f μ) : ∀ᵐ ω, Tendsto (fun n => birkhoffAverageReal T f n ω) atTop (𝓝 (∫ f))`。
      `ErgodicProcess` の shift T / ergodicity instance の取り出し方を確認。
- [ ] **`hreg` の a.s. 化可否判定** (Phase V signature 確定): `∀ᵐ ω, ∀ m, 0 < prefixBlockProb …` が
      ergodicity から導けるか。**導けない見込み** (退化分布で 0 質量 cylinder) → `hreg` を明示 regularity
      仮説として headline に残す (honest)。導ければ無条件 headline。
- [ ] **既存 honest primitive を本 plan の構成が circular にしないことの確認**: Phase Z4 / C4 の構成定理は
      `IsLZ78AchievabilityZivUpperBound` / `IsLZ78ConverseCodingLowerBound` を **構成 (∧ field を proving)**
      するのであって、`:= h` で受け流さない。型 ≠ 結論、`:True` slot 禁止 (CLAUDE.md 検証の誠実性)。

---

## Phase C1 — `LZ78ConverseAveraged.lean` skeleton + averaged-Kraft 設計確定 📋

skeleton-driven (CLAUDE.md): Core 2 群の全 def/定理を `:= by sorry` で並べ、namespace/imports/variable 確定。

- [ ] imports: `InformationTheory.Shannon.ShannonCode` (Kraft 資産), `LZ78ConverseKraft`
      (`IsLZ78ConverseCodingLowerBound` structure + `shannon_mcmillan_breiman₂`),
      `LZ78ZivEntropyBridge` (`blockLogAvg₂`/`prefixBlockProb`/`entropyRate₂`),
      `LZ78DistinctEncoding` (`lz78DistinctEncodingLength`), `BirkhoffErgodic` (`birkhoff_ergodic_ae`),
      `SMBAlgoetCover` (`shannon_mcmillan_breiman`), `Mathlib.Analysis.SpecialFunctions.Log.Base`。
      **`import Mathlib` 禁止、pinpoint**。
- [ ] namespace `InformationTheory.Shannon`、`open MeasureTheory ProbabilityTheory Filter Topology`,
      `open scoped ENNReal NNReal BigOperators`。
- [ ] variable: `{α Ω}` + 有限 alphabet instances + `[MeasurableSpace Ω]`。
- [ ] 全 declaration を `:= by sorry` で stub: `blockKraftSum_le_one`, (必要なら `blockShannonLength` def),
      averaged 下界 lemma, `isLZ78ConverseCodingLowerBound_distinct`。
- [ ] **検証**: `lake env lean InformationTheory/Shannon/LZ78ConverseAveraged.lean` が sorry warning のみ。
- **撤退ライン**: なし (skeleton のみ)。proof-log: no。

---

## Phase C2 — `blockKraftSum_le_one` (Core 2 crux 1) 📋

block pushforward 測度 `Pₙ = μ.map (blockRV n)` 上で codeword 長が Kraft を充足。

- [ ] **設計判断 (Phase 0 確定): Shannon-code 代用一択**。McMillan (uniquely decodable → Kraft) は
      Mathlib 不在。`shannonLength_kraft_le_one` (`ShannonCode.lean:129`) を block 測度 `Pₙ` に適用し
      `kraftSum D (shannonLength D Pₙ) ≤ 1` を確保。LZ78 codeword 長 `lz` 自体の Kraft 充足は McMillan
      が要るので**避ける** — C3 で `lz ≥ shannonLength` ではなく averaged 下界 `H_D(Pₙ) ≤ E[lz]` で繋ぐ。
- [ ] target: `kraftSum (Fintype.card α : ℝ) (shannonLength (Fintype.card α) Pₙ) ≤ 1`
      (or D=2 ベース、bit 整合は C3/C4 で `/log 2`)。前提 `[IsProbabilityMeasure Pₙ]` (block pushforward の
      確率測度性は `Measure.isProbabilityMeasure_map` で、`prefixBlockProb_zero` の手口) + full-support
      `∀ x, 0 < Pₙ{x}` (= `hreg` の n-block 形)。
- **依存補題**: `shannonLength_kraft_le_one` (`ShannonCode.lean:129`), `kraftSum`/`shannonLength` def
      (`:59,:51`), `Measure.isProbabilityMeasure_map`。
- **proof-log: yes** — Shannon-code 代用の選択理由、full-support の `hreg` 由来、D の取り方を記録。
- **撤退ライン [L-C2]**: Shannon-code 代用が block 測度の `MeasurableSingletonClass (Fin n → α)` /
      `Fintype` instance 解決で詰まれば、`shannonLength_kraft_le_one` の前提を満たす `Pₙ` の instance を
      `Fintype (Fin n → α)` (有限 alphabet × 有限 index、自動) で補強。full discharge 維持。

---

## Phase C3 — averaged converse coding 下界 + Birkhoff a.s. lift (Core 2 真の crux) 📋

expectation-level Kraft 下界 `H_D(Pₙ) ≤ E[lz]` を a.s. pointwise `blockLogAvg₂ − slack ≤ lz/n` に持ち上げ。

- [ ] **expectation-level 下界** (前半): `entropyD_le_expectedLength_of_kraft` (`ShannonCode.lean:164`) を
      block 測度 `Pₙ` + LZ78 codeword 長 `l_n(x) = lz78DistinctEncodingLength n x` に適用。**ただし** LZ78
      codeword 長が Kraft を充足する保証 (McMillan) を避けるため、`l = shannonLength D Pₙ` で適用して
      `H_D(Pₙ) ≤ E_Pₙ[shannonLength]` を得、別途 `E_Pₙ[shannonLength] ≤ E_Pₙ[lz] + O(1)` を立てる経路、
      または `entropyD_le_expectedLength_of_kraft` を **LZ78 が prefix code である事実** (Kraft 充足を
      McMillan なしで block pushforward の単射性 + prefix-free 性から立てる) で直接 `l = lz` に適用する経路。
      **Phase 0 で経路確定** (Shannon-code 代用なら前者、prefix-free 直接なら後者)。
- [ ] **a.s. lift** (後半、★真の crux): expectation `H_D(Pₙ)/n ≤ E[lz_n/n]` を per-path eventual
      `blockLogAvg₂ − slack ≤ lz/n` に持ち上げ。**不健全経路は採らない**: pointwise `2^{-lz}≤Pₙ`
      (Shannon-code) は `lz ≥ shannonLength` が pointwise 偽なので**不採用** (docstring で明記)。採る経路:
      `H_D(Pₙ)/n = E[blockLogAvg₂_n]` (block entropy in bits の per-symbol) + `blockLogAvg₂ → entropyRate₂`
      a.s. (SMB) + `lz/n → entropyRate₂` a.s. (headline の Z 側、circular 回避のため Z と独立に
      boundedness のみ使う) を **Fatou / Birkhoff** で繋ぐ。最も筋が良いのは Birkhoff を per-letter
      観測量 `f = -log₂ P(X_0 | X_{-∞..−1})` (条件付きエントロピー密度) に当て、時間平均が `entropyRate₂` に
      a.s. 収束する事実と Kraft 期待値下界を per-path で合わせる経路。
- [ ] slack `slack n` の a.s. → 0: Kraft の整数化 gap (`⌈⌉` の +1) を `/n` で消す。`Tendsto slack atTop (𝓝 0)`
      を構成。
- **依存補題**: `entropyD_le_expectedLength_of_kraft` (`ShannonCode.lean:164`), C2 `blockKraftSum_le_one`,
      `birkhoff_ergodic_ae` (`BirkhoffErgodic.lean:1031`), `shannon_mcmillan_breiman₂`
      (`LZ78ConverseKraft.lean:133`), `blockLogAvg₂`/`entropyRate₂` def, `entropyD` def (`ShannonCode.lean:45`)。
- **proof-log: yes** — expectation→a.s. の経路 (Birkhoff 観測量の選択)、不健全経路の回避、full-support の
      a.s. 範疇、slack→0 を記録。
- **撤退ライン [L-C3、最重要]**: averaged Kraft の a.s. lift が `~1.5 セッション / ~450 行`で閉じない
      見込みなら **`IsLZ78ConverseCodingLowerBound` を isolated honest hyp として残す** (現状の headline
      引数のまま、本 plan では構成しない)。明示 structure (型 ≠ 結論)、docstring で「Cover–Thomas 13.130
      averaged coding 下界、未 discharge、load-bearing」明示。`Prop := True` / `:= h` 循環は禁止。
      **この場合でも Core 1 (Z) が genuine に閉じれば headline の honest 入力は 2→1**。

---

## Phase C4 — `isLZ78ConverseCodingLowerBound_distinct` (per-path slack assembly, Core 2 解除目標) 📋

C3 の per-path eventual 下界 + slack→0 を structure に詰め、`IsLZ78ConverseCodingLowerBound` を genuine 構成。

- [ ] target: `IsLZ78ConverseCodingLowerBound μ p.toStationaryProcess (@lz78DistinctEncodingLength α _ _ _)
      slackLow` (structure、field `lower` + `slack_tendsto`、verbatim `LZ78ConverseKraft.lean:107`)。
- [ ] `⟨h_lower_ae, h_slack_tendsto⟩` で構成。`h_lower_ae` は C3 の per-path eventual 下界、
      `h_slack_tendsto` は C3 の slack→0。
- **依存補題**: C3 averaged 下界 + slack。
- **proof-log: yes** — structure 構成、slack の Tendsto を記録。
- **撤退ライン**: C3 が genuine なら本 Phase は機械的詰め。C3 が L-C3 で honest 化されたら本 Phase は不発
      (headline で `IsLZ78ConverseCodingLowerBound` を引数のまま残す)。

---

## Phase Z1 — `LZ78ZivCombinatorics.lean` skeleton + distinct-stratum 設計確定 📋

skeleton-driven: Core 1 群の全 def/定理を `:= by sorry` で並べ、namespace/imports/variable 確定。

- [ ] imports: `InformationTheory.Shannon.LZ78ZivEntropyBridge` (`condPhraseProb`/`prefixBlockProb`/
      `parsingBoundary`/`log_sum_inequality`/`blockProb_neg_log_ge_sum`/base-2 層),
      `StationaryKernel` (`isLZ78PerPathParsingFactorization_of_pos`/`prefixBlockProb_antitone`),
      `LZ78ZivCountingBody` (boundedness envelope), `LZ78GreedyLongestPrefix` (`lz78PhraseStrings_nodup`),
      `LZ78DistinctEncoding` (`lz78DistinctEncodingLength_eq`),
      `LZ78AchievabilityLimsup` (`IsLZ78AchievabilityZivUpperBound` structure),
      `Mathlib.Analysis.Convex.Jensen`。**`import Mathlib` 禁止**。
- [ ] namespace / open / variable (Phase C1 と同形)。
- [ ] 全 declaration を `:= by sorry` で stub: (必要なら `parsingStratum` def),
      `condPhraseProb_stratumSum_le_one`, `ziv_count_mul_log_le_neg_log_blockProb`,
      `isLZ78AchievabilityZivUpperBound_distinct`。
- [ ] **検証**: `lake env lean InformationTheory/Shannon/LZ78ZivCombinatorics.lean` が sorry warning のみ。
- **撤退ライン**: なし (skeleton のみ)。proof-log: no。

---

## Phase Z2 — `condPhraseProb_stratumSum_le_one` (Core 1 真の crux) 📋

**Core 1 全体の crux**。distinct phrases を SET として扱う組合せ論の核心 = **per-stratum sub-distribution**。

- [ ] **設計 (Mathlib-shape-driven、結論形を log_sum_inequality に流せる形で固定してから着手)**:
      同じ context prefix を共有する phrase 群 (stratum) について、その条件付き確率 `condPhraseProb` の
      和が `≤ 1`。`condPhraseProb = prefixBlockProb(b(j+1))/prefixBlockProb(b(j))` の定義から、同 context
      (同分母 cylinder) の分子 cylinder 群が **互いに素で union ⊆ 分母 cylinder** であることを `measureReal`
      の有限加法性 + monotonicity で立てる。結論形は `∑_{j∈stratum} condPhraseProb μ p n ω j ≤ 1`。
- [ ] cylinder の互いに素性: 異なる next-symbol で延長された prefix cylinder は disjoint
      (`blockRV` 射影の prefix 構造、`prefixBlockProb_antitone` `StationaryKernel.lean:157` の手口を流用)。
- [ ] zero-mass / `n=0` edge を special-case (`hreg` 正値で回避、support 外は `log0=0` 規約)。
- **依存補題**: `condPhraseProb`/`prefixBlockProb`/`parsingBoundary` def (`LZ78ZivEntropyBridge.lean:139–167`),
      `prefixBlockProb_antitone` (`StationaryKernel.lean:157`), `measureReal` 有限加法性 + monotonicity,
      `lz78PhraseStrings_nodup` (`LZ78GreedyLongestPrefix.lean:126`)。
- **proof-log: yes** — stratum 構造の定義、cylinder disjoint の集合代数、sub-distribution 不等式を記録。
- **撤退ライン [L-Z2、最重要]**: per-stratum sub-distribution が `~1.5 セッション / ~350 行`で閉じない
      見込みなら **`IsLZ78AchievabilityZivUpperBound` を isolated honest hyp として残す** (現状の headline
      引数のまま、本 plan では構成しない)。明示 structure (型 ≠ 結論)、docstring で「Cover–Thomas 13.5.5
      distinct-phrase sub-distribution、未 discharge、load-bearing」明示。`Prop := True` / `:= h` 循環禁止。
      **この場合でも Core 2 (C) が genuine に閉じれば headline の honest 入力は 2→1**。

---

## Phase Z3 — `ziv_count_mul_log_le_neg_log_blockProb` (組合せ Ziv 合流) 📋

`c·log₂c ≤ -log₂Pₙ{block ω}` (Cover–Thomas Eq.13.122–124)。Z2 sub-distribution + 既存 genuine 合流。

- [ ] target: `(c:ℝ)·Real.logb 2 c ≤ -Real.logb 2 ((μ.map (p.blockRV n)).real {p.blockRV n ω})`,
      `c := (lz78PhraseStrings (List.ofFn (blockRV n ω))).length`。
- [ ] **合流 (罠回避の正しい decomposition)**: foundation `blockProb_neg_log_ge_sum`
      (`LZ78ZivEntropyBridge.lean:225`) が `∑ⱼ -log qⱼ ≤ -log Pₙ` (積方向、genuine) を与える。残りは
      右辺 `∑ⱼ -log qⱼ` を下から `c·log c` で評価する **per-stratum log-sum**: Z2 sub-distribution
      `∑_{stratum} qⱼ ≤ 1` を `log_sum_inequality` (`:69`、`aₖ≡1`/`bₖ≡qⱼ`) に **stratum 別に** 適用 →
      各 stratum で `c_s·log c_s ≤ ∑_{stratum} -log qⱼ`、stratum 横断で `∑_s c_s·log c_s ≥ c·log c`
      (convexity / `c = ∑_s c_s`) を合わせ `c·log c ≤ ∑ⱼ -log qⱼ ≤ -log Pₙ`。
- [ ] base-2 化: `Real.logb 2 = Real.log / Real.log 2`、`log_two_pos` (`LZ78ZivEntropyBridge.lean:261`)。
- [ ] zero-mass / `c=0` / `n=0` edge を special-case。
- **依存補題**: Z2 `condPhraseProb_stratumSum_le_one`, `log_sum_inequality` (`:69`),
      `blockProb_neg_log_ge_sum` (`:225`), `isLZ78PerPathParsingFactorization_of_pos`
      (`StationaryKernel.lean:255`, factorization 入力), `Real.logb`/`log_two_pos`。
- **proof-log: yes** — per-stratum log-sum の重み選択 (`aₖ≡1`)、stratum 横断の凸性、罠回避の
      decomposition を記録。
- **撤退ライン**: per-stratum log-sum の合成が詰まれば 1-stratum (全 phrase が distinct = 各 stratum 1 元)
      の degenerate 評価から始め `Finset` 帰納で一般化。Z2 が L-Z2 で honest 化されたら本 Phase の
      sub-distribution 入力が honest hyp になるだけで残りは genuine。

---

## Phase Z4 — `isLZ78AchievabilityZivUpperBound_distinct` (per-path slack assembly, Core 1 解除目標) 📋

Z3 の `c·log₂c ≤ -log₂Pₙ` を per-symbol `lz/n ≤ blockLogAvg₂ + slack` 形に落とし structure 構成。

- [ ] **per-symbol bridge**: `lz78DistinctEncodingLength_eq` (`LZ78DistinctEncoding.lean:133`) で
      `lz n x = c·bitLength c |α|`、`bitLength c |α| = log₂(c+1) + log₂|α| + 2` (`bitLength_eq`,
      `LZ78GreedyParsing.lean:110`)。`lz/n = (c/n)·bitLength ≈ (c·log₂c)/n + (c/n)·O(log|α|)`、Z3 で
      `c·log₂c ≤ -log₂Pₙ = n·blockLogAvg₂` (`blockLogAvg_eq_neg_log_blockProb` `:123` の base-2 形)、
      余剰 `(c/n)·O(log|α|)` は counting envelope `c = O(n/log n)`
      (`lz78PhraseStrings_count_isBigO`, `LZ78ZivCountingBody.lean:405`) で `slack n → 0`。
- [ ] target: `IsLZ78AchievabilityZivUpperBound μ p.toStationaryProcess (@lz78DistinctEncodingLength α _ _ _)
      slackUp` (structure、field `upper` + `slack_tendsto`、verbatim `LZ78AchievabilityLimsup.lean:114`)。
      `⟨h_upper_ae, h_slack_tendsto⟩` で構成。
- **依存補題**: Z3 Ziv, `lz78DistinctEncodingLength_eq` (`:133`), `bitLength_eq`
      (`LZ78GreedyParsing.lean:110`), counting envelope (`LZ78ZivCountingBody.lean:405`),
      `blockLogAvg_eq_neg_log_blockProb` (`:123`)。
- **proof-log: yes** — slack の構成 (bit-length O(log|α|) 項 + counting envelope)、Tendsto を記録。
- **撤退ライン**: per-symbol bridge の slack→0 が詰まれば既存 limsup assembly
      (`lz78_achievability_limsup_le₂`, `LZ78AchievabilityLimsup.lean:153`) の slack 吸収 pattern を
      参照。Z3 が genuine なら full discharge。

---

## Phase V — 無仮定 base-2 headline publish + `#print axioms` + clean check 📋

- [ ] **headline publish**: `lz78_two_sided_optimality_distinct` (新 theorem) を
      `lz78_two_sided_optimality_distinct_genuine μ p slackUp slackLow
      (isLZ78AchievabilityZivUpperBound_distinct μ p hreg) (isLZ78ConverseCodingLowerBound_distinct μ p hreg)`
      で publish (`LZ78AchievabilityLimsup.lean` 末尾 or 新 file)。`hreg` は明示 regularity 仮説
      (Phase 0 の判定通り)。**既存 `_genuine` 定理は signature 不変で残す** (下流互換)。
      段階着地時 (片方の core のみ genuine) は、残った honest primitive を正直に明記した中間 headline を publish。
- [ ] **`#print axioms lz78_two_sided_optimality_distinct`** で **sorryAx 非依存** を確認
      (`propext`/`Classical.choice`/`Quot.sound` のみ許容)。これが標準B の機械検証バー。
- [ ] `InformationTheory.lean` に `import InformationTheory.Shannon.LZ78ConverseAveraged` と
      `import InformationTheory.Shannon.LZ78ZivCombinatorics` を追記 (`LZ78AchievabilityLimsup` import の前後、
      依存順に)。
- [ ] **検証**: `lake env lean` で 2 新規 file + headline file が silent (0 error / 0 sorry / 0 warning)。
      最後に `lake build` 一回で project-wide sanity (upstream olean refresh 兼)。
- [ ] 既存 genuine 補題 (foundation 全般、Kraft 資産, SMB/Birkhoff) の signature 無変更を `rg` で横断確認
      (新規追加のみ)。

---

## Blast radius

- **新規 lemma 投入先**: `InformationTheory/Shannon/LZ78ConverseAveraged.lean` (新規, ~580 行, Core 2 群) +
  `InformationTheory/Shannon/LZ78ZivCombinatorics.lean` (新規, ~580 行, Core 1 群)。
- **編集される既存ファイル**: `InformationTheory.lean` (import 2 行追記)。`LZ78AchievabilityLimsup.lean` は
  **任意** (Phase V の無仮定 headline を別名で追記する場合のみ、既存定理は不変)。
- **signature 変更ゼロ確認**: 再利用する既存 genuine 補題はすべて **黒箱 reuse、signature 不変**:
  - foundation: `blockProb_neg_log_ge_sum` (`LZ78ZivEntropyBridge.lean:225`), `log_sum_inequality` (`:69`),
    `blockLogAvg_eq_neg_log_blockProb` (`:123`), `condPhraseProb`/`prefixBlockProb`/`parsingBoundary` def,
    `blockLogAvg₂`/`entropyRate₂`/`log_two_pos` (`:267,:274,:261`)
  - telescoping: `isLZ78PerPathParsingFactorization_of_pos` / `prefixBlockProb_antitone` /
    `prod_condPhraseProb_telescope` / `blockProb_le_prod_condPhraseProb` (`StationaryKernel.lean:255,157,73,200`)
  - counting: `lz78PhraseStrings_mul_log_le` (`LZ78ZivCountingBody.lean:353`), envelope (`:405`),
    `lz78PhraseStrings_nodup`/`_count_le` (`LZ78GreedyLongestPrefix.lean:126,260`)
  - encoding: `lz78DistinctEncodingLength_eq` (`LZ78DistinctEncoding.lean:133`), `bitLength_eq`
    (`LZ78GreedyParsing.lean:110`)
  - Kraft: `entropyD_le_expectedLength_of_kraft` (`ShannonCode.lean:164`), `shannonLength_kraft_le_one`
    (`:129`), `kraftSum`/`expectedLength`/`entropyD`/`shannonLength` def (`:59,:55,:45,:51`)
  - SMB/Birkhoff: `shannon_mcmillan_breiman` (`SMBAlgoetCover.lean:2840`), `shannon_mcmillan_breiman₂`
    (`LZ78ConverseKraft.lean:133`), `birkhoff_ergodic_ae` (`BirkhoffErgodic.lean:1031`)
  - primitive structure: `IsLZ78AchievabilityZivUpperBound` (`LZ78AchievabilityLimsup.lean:114`),
    `IsLZ78ConverseCodingLowerBound` (`LZ78ConverseKraft.lean:107`), headline `_genuine` (`:233`)
  本 plan は新規補題追加のみで既存の証明・型を触らない。

---

## 撤退ライン (本 plan)

各 Phase は **独立撤退可能**。撤退時も honest 限定 (名前付き仮説、型 ≠ 結論、docstring で
load-bearing 明示)。`Prop := True` / 結論同型述語への `:= h` 循環 / `sorry` は **禁止**
(CLAUDE.md 検証の誠実性)。

| ID | 対象 | 発動条件 | 撤退後の着地 |
|---|---|---|---|
| **L-C2** | block Kraft 充足 (Phase C2) | block 測度の instance 解決が重い | `Fintype (Fin n → α)` で instance 補強。full discharge 維持 |
| **L-C3** | averaged Kraft a.s. lift (Phase C3、最重要) | expectation→a.s. >450 行 | `IsLZ78ConverseCodingLowerBound` を isolated honest hyp で残す。Core 1 が通れば 2→1 |
| **L-Z2** | per-stratum sub-distribution (Phase Z2、最重要) | cylinder disjoint + sub-distrib >350 行 | `IsLZ78AchievabilityZivUpperBound` を isolated honest hyp で残す。Core 2 が通れば 2→1 |
| **L-hreg** | `hreg` a.s. 化 (Phase V) | ergodicity から a.s. full-support 出ない | `hreg` を明示 regularity 仮説として headline に残す (honest、load-bearing でない) |
| (Z3/Z4/C4 解除目標) | 組合せ Ziv 合流 / per-path assembly | — | Z2/C3 が通れば達成 (既存 genuine 資産の合流) |

**all-or-nothing 注記**: 2 core は独立。**Core 2 (C2→C3→C4) が genuine になれば `IsLZ78ConverseCodingLowerBound`
が headline 引数から外れ、Core 1 (Z2→Z3→Z4) が genuine になれば `IsLZ78AchievabilityZivUpperBound` が外れる**。
片方だけ genuine でも honest 入力数を 2→1 に確実に減らせる (Core 2 先行推奨の主因)。両方 genuine で完全
無仮定 (+ `hreg` regularity) headline。L-C3 / L-Z2 発動時は当該 1 primitive が isolated honest 入力として
明示的に残る (現状と同じ deferral 数だが、片方は genuine に置換済)。

---

## 当面の next step

1. **Phase 0** 着手前確認 (2 primitive structure field verbatim、foundation/Kraft/Birkhoff の verbatim
   signature、`hreg` a.s. 化可否、counting `K·n ≠ -log Pₙ` の route (b) 不採用根拠、circular 回避)。
2. **Phase C1 → C2 → C3 → C4** (converse 先行、Core 2)。最初に着手すべきは **Phase C1 (skeleton)**、
   その後 **C2 (Shannon-code 代用 block Kraft 充足)**。**C3 (averaged Kraft → Birkhoff a.s. lift) が
   Core 2 の真の crux**。converse 完了で headline honest 入力が **確実に 2→1**。
3. **Phase Z1 → Z2 → Z3 → Z4** (achiev、Core 1)。**Z2 (per-stratum sub-distribution) が Core 1 の真の
   crux**。Z2 が成れば Z3/Z4 は既存 genuine 資産の合流で閉じる。
4. **Phase V** 無仮定 headline publish + `#print axioms` (sorryAx 非依存確認) + clean check。

**並行実行の余地**: Core 2 群 (C1–C4) と Core 1 群 (Z1–Z4) は別ファイル・独立 crux なので並列 agent で
同時着手可。各群内は逐次依存。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 起草時点の確定事項 (実装中の方針変更があればここに追記):
1. **(2026-05-21) foundation は genuine 完成済 — 残りは 2 named primitive のみ** —
   base-2 headline `lz78_two_sided_optimality_distinct_genuine` (`LZ78AchievabilityLimsup.lean:233`) が
   `IsLZ78AchievabilityZivUpperBound` / `IsLZ78ConverseCodingLowerBound` の 2 structure を引数に取る形で
   既に sorryAx 非依存。telescoping/factorization/base-2/SMB/assembly は全 genuine。residual-discharge
   plan の Phase Z4 (cylinder factorization) / C2-C3 (Kraft) の crux 認識は古く、Z4 は既に解決済
   (`StationaryKernel.lean`)。本 plan は精緻な 2 core (distinct 組合せ Ziv + averaged Kraft) に絞る。
2. **(2026-05-21) Core 1 route 判定: route (b) 不採用、route (a)/(c) per-stratum log-sum が genuine** —
   `lz78PhraseStrings_mul_log_le` (`LZ78ZivCountingBody.lean:353`) の conclusion は `c·log c ≤ K·n`
   (constant rate、分布非依存) であり `-log Pₙ` (分布依存) ではない。両者を繋ぐ bridge は存在しない
   (異なる量)。Ziv 上界 `c·log₂c ≤ -log₂Pₙ` の真の route は distinct phrases を SET として stratum 別に
   log-sum を打つ組合せ論 (Cover–Thomas 13.5.5 original)。telescoping の罠 (path 沿い `∑ qⱼ ≈ c ≠ 1`) は
   **stratum 別分解** で回避 (各 stratum で `∑ qⱼ ≤ 1`)。foundation `blockProb_neg_log_ge_sum` +
   `log_sum_inequality` は genuine、残り crux は per-stratum sub-distribution `∑_{stratum} qⱼ ≤ 1`
   (Phase Z2) 一点。
3. **(2026-05-21) Core 2 は averaged Kraft + Birkhoff lift、pointwise 不健全経路は不採用** —
   `2^{-lz}≤Pₙ` (Shannon-code 補題) は `lz≥shannonLength` が pointwise 偽 (LZ78 universality) のため
   不健全、不採用。採るのは expectation-level `entropyD_le_expectedLength_of_kraft` (`ShannonCode.lean:164`)
   → Birkhoff (`birkhoff_ergodic_ae` `BirkhoffErgodic.lean:1031`) + base-2 SMB
   (`shannon_mcmillan_breiman₂`) で a.s. lift する averaged 経路一択。block Kraft 充足は McMillan
   (Mathlib 不在) を避け Shannon-code 代用 (`shannonLength_kraft_le_one` `ShannonCode.lean:129`)。
4. **(2026-05-21) `hreg` (full-support cylinder 正値) は許容 regularity 仮説** —
   `isLZ78PerPathParsingFactorization_of_pos` (`StationaryKernel.lean:255`) が既に同型の `hreg` を取る
   genuine 定理。退化分布で a.s. full-support は一般に成り立たないため、`hreg` を明示 regularity 仮説として
   headline に残すのが honest (load-bearing でない、証明の核心を肩代わりしない)。Phase 0 で a.s. 化の
   可否を最終判定。
5. **(2026-05-21) Core 2 先行を推奨** — Kraft + Birkhoff + base-2 SMB 資産が厚く ROI が高い。両 core 独立。
   片方 genuine で honest 入力 2→1 確実。最初の着手は Phase C1 skeleton → C2 block Kraft 充足。
6. **(2026-05-21) [defect 報告] L-LZ4 実装版の greedy は trivial one-symbol parse** —
   `lz78GreedyEncodingLength` (`LZ78GreedyParsing.lean:270`) は `lz78OneSymbolParsing` (count=n の最悪
   one-symbol form) ベースで、genuine longest-prefix `lz78PhraseStrings` ではない。本 plan の対象 headline
   は `lz78DistinctEncodingLength` (distinct count、genuine) を使うので影響なし。ただし旧 placeholder
   path (`LempelZiv78.lean` の `Is*Passthrough := True` + `lz78Greedy*_is*Passthrough := True.intro`,
   `LZ78GreedyParsing.lean:428,434`) は依然 vacuous。本 plan の genuine path とは別経路 (本 plan は触らない)。
-->

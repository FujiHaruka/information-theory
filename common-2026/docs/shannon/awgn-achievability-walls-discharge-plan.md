# AWGN achievability — 3 shared 壁 discharge + statement-fix サブ計画

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) F-1 (achievability typicality)。
> **Sibling (history)**: [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md) (DONE、3 壁を staged/shared sorry 化した元 plan) / [`awgn-power-constraint-realizable-pivot-plan.md`](awgn-power-constraint-realizable-pivot-plan.md) (judgment #7 = 1 回目の power-constraint pivot)。
> **Facts ledger**: [`awgn-facts.md`](awgn-facts.md) (壁 overturn / 残存壁 / 確定事実の SoT)。

## 進捗

- [x] M0 — decomposition 再設計の feasible 確定 (D1-D4、2 subagent 独立検証) ✅
- [x] Phase 1 — Wall 1 (D1): (ii)/(iii) statement-fix (4件目 false-statement 発見) + (i)/(iii)/joint measure-identity genuine、**type-check done、deep atom 2 件 deferred** 🚧 (commit eab36aa)
- [x] Phase 4 — Wall 2 (D2): 新 lemma `awgn_random_coding_union_bound` 新設 (AEP thread)、**gateway 達成 + 監査 all-OK、type-check done、5/7 atom genuine、measure-identity sorry 2 件** 🚧 (commit 7c26322)
- [x] Phase 5a — Wall 3 (D3): 新 lemma `awgnPowerConstraintPerCodeword_holds` (per-codeword 形) **proof done (sorryAx-free)** + slack form 修正 ✅
- [ ] D4 — consumer rewire: 旧 Wall2/3 retire + consumer を新 lemma 2 本に rewire + per-codeword barrier 再構築 📋
- [ ] deep atoms — Wall1 MemLp / Wall1 change-of-measure / Wall2 term1 / Wall2 term2 (全 plan: plumbing、各 ~50行) 📋
- [ ] Phase V — verify + 親 plan / facts ledger 同期 + 独立 honesty 監査 📋

> 旧 Phase 2 (Wall 1 (iii) 単独) は Phase 1 に統合。旧 Phase 3 (Wall 1 (ii) statement-fix to `jointDifferentialEntropyPi`) は **削除** に置換 (consumer が破棄済 + 第2項 mass は (iii) が担当ゆえ load-bearing でない、§Approach D1 参照)。
> Phase 5 (旧 Wall 3 + D4 一体) は **Phase 5a (D3 = 新 lemma genuine、commit e4587aa)** と **D4 (consumer rewire、pending)** に分割。新 lemma 2 本 (Wall2/3) は旧 false 補題と **並存**、retire は D4 で一括実施。

## ゴール / Approach

### Goal

`AWGN/Walls.lean` の achievability 側 3 shared sorry 補題 (`continuousAepGaussian_holds` /
`awgnRandomCodingBound_holds` / `awgnPowerConstraintHonest_holds`) を **genuine closure** し、
親 plan F-1 の headline `awgn_achievability_F1_via_staged_hyps` /
`awgn_theorem_F4_discharged_F1_via_staged` (`AchievabilityDischarge.lean`) を transitively
sorryAx-free にする。converse は既に genuine 完了済 (`awgn_converse`)。本 plan 完走で AWGN
channel coding theorem 全体 (achievability + converse) が genuine。

**✅ ORCHESTRATOR UPDATE (2026-06-12、Phase 1/4/5a 実装後)**: 3 補題の **3 つすべて**が
false/mis-stated と判明 (Wall 1 (ii) klDiv-to-volume 退化 / Wall 2 `∀decoder` 過大 / Wall 3
`∀m` 指数 rate、各 `@audit:retract-candidate(false-statement)`) → 本 plan は「3 壁 discharge」から
**「decomposition 再設計 + statement-fix」へ escalation 済**。その再設計 (D1-D4) を M0 で
2 subagent の独立検証により feasible 確定 (NO-GO なし)、**Phase 1/4/5a を実装済**:
- **Phase 1 (D1) = type-check done** (commit eab36aa): (ii) 削除に加え **(iii) も false-statement と
  判明し statement-fix 済 (4件目の false-statement、指数 `−n²I+3nε` → `−n(I−3ε)` に修正)**。
  (i)/(iii)/joint measure-identity は genuine、残 2 deep atom (`hφ_memLp` / (iii) change-of-measure) を
  honest sorry で deferred。
- **Phase 4 (D2) = type-check done + gateway 達成 + 監査 all-OK** (commit 7c26322): 新 lemma
  `awgn_random_coding_union_bound` (`AchievabilityDischarge.lean:475`)、union bound が壁でなく
  (i)/(iii) から組み上がることを type-check で確証。AEP thread = modular composition (監査確定)。
  5/7 atom genuine、残 2 measure-identity sorry。
- **Phase 5a (D3) = proof done (sorryAx-free)** (commit e4587aa): 新 lemma
  `awgnPowerConstraintPerCodeword_holds` (`Walls.lean:370`)、engine φ=x² で genuine。slack form 修正
  (`(P_cb.toNNReal:ℝ) < P_target` = 分散値ベースが honest)。

genuine な核 = (a) 質量集中エンジン (✅) + (b) jointTypicalDecoder 結合の正しい union bound (D2、新
lemma type-check done) + (c) per-codeword expurgation 形 power 制約 (D3、✅ sorryAx-free)。残 = D4
consumer rewire + deep atom 4 件 (全 plumbing) + Phase V。Wall 1 (ii) volume bound は **削除**、
新 lemma 2 本は旧 false 補題と並存 (retire は D4)。

### Approach (overall strategy / shape of solution)

**全体の形**: 3 壁を「個別に discharge」するのではなく、AEP engine を最上流に置いた **modular
decomposition (D1-D4)** に組み替える。確定した依存鎖 (M0 で import cycle 不在を検証済):

```
AchievabilityAEP.lean (engine、Mathlib のみ依存、AWGN 依存ゼロ)
  └→ Walls.lean        (D1 Wall 1 + D3 Wall 3、engine を import)
       └→ AchievabilityDischarge.lean (D2 union-bound lemma + D4 consumer、kernel/decoder が local)
```

`Walls.lean` に `import InformationTheory.Shannon.AWGN.AchievabilityAEP` を追加可 (cycle なし、検証済)。
`awgnCodebookKernel` / `jointTypicalDecoder` / `gaussianCodebook` は **下流 `AchievabilityDischarge.lean`**
にあるため、kernel/decoder を参照する新 lemma (D2) は relocate 不要でそこに置く。

#### D1 — Wall 1 `continuousAepGaussian_holds` (Walls.lean に残す)

`∃` 可測 A + **2 bounds のみ**に縮小:

- **(i) joint codebook+noise mass `≥ 1−ε`** = engine `pi_empirical_mean_typical_mass` で genuine。
  joint AWGN i.i.d. 法則 + per-letter log-density `φ` を engine の abstract `μ`/`φ` に wiring、
  `MemLp φ 2` を確認 (Gaussian 有限モーメント)。
- **(iii) indep-pair product-mass `≤ exp(−n(I−3ε))`** = sound (両 prob measure ゆえ真 MI)。
  `klDiv_pi_eq_sum` / `klDiv_prod_eq_add` / `klDiv_gaussianReal_gaussianReal_eq` で per-letter MI を
  積分解、engine + `ENNReal.toReal_nonneg`。
- **(ii) volume bound は削除** (statement-fix でなく **削除**)。理由: ① consumer が `_hA_vol` で
  破棄済 + ② **Wall 2 第2項 mass は (iii) から出る** (volume counting とは別軸) ゆえ (ii) は
  **load-bearing でない**。false klDiv-to-volume statement を「削除」で honest 化する。
  **結果として `jointDifferentialEntropyPi` 系資産は achievability では不要** (これらは (ii)
  statement-fix 専用だった、converse 側資産)。

#### D2 — Wall 2 = AchievabilityDischarge.lean に置く genuine lemma

Walls の false `awgnRandomCodingBound_holds` は **retire/削除**。新 lemma (仮称
`awgn_random_coding_union_bound`) を **AchievabilityDischarge.lean** に置く (kernel/decoder が local
ゆえ relocate 不要):

- **signature**: A + (i)mass + (iii)indep-pair を **hypothesis として受け取り**、decoder =
  `jointTypicalDecoder A` 固定、`∫⁻ codebook, Pe(jointTypicalDecoder A, m) ≤ 2ε` を結論。
- **Cover-Thomas 9.2 union bound**: `P(error|m) ≤ P((X(m),Y)∉A) + ∑_{m'≠m} P((X(m'),Y)∈A)`、
  第1項 ≤ ε は (i)、第2項は `X(m')⊥Y` で product-mass ≤ (iii) bound、`M≈exp(nR)` 個和 ≤ ε (R<I)。
- **honesty**: AEP bounds を hypothesis に thread するのは genuine な Wall 1 (D1) output の
  **modular composition** であり、**load-bearing bundling 非該当** (証明の核を `*Hypothesis`
  predicate に encode していない。条件: (i)(iii) が sorryAx-free で閉じてから thread。閉じる前でも
  sorry が compiler-visible に残るので tier 2 honest)。AEP の (i)/(iii) は **regularity precondition
  でなく Wall 1 の証明済 output** であり、それを別 lemma が consume する標準的な layering。
- **kernel 可測性は壁でない**: 残存壁 `IsParallelGaussianKernelMeasurable` (location-varying
  Gaussian mean の x-可測性) とは別物。Wall 2 の `c ↦ Measure.pi (awgnChannel N (c m i))` 可測性は
  既存 `awgnCodebookKernel` + `Kernel.measurable_kernel_prodMk_left` で discharge 済 (consumer
  `AchievabilityDischarge.lean:998-1028` で既にコンパイル通過)。

#### D3 — Wall 3 `awgnPowerConstraintHonest_holds` (Walls.lean に残す)

`mass{∀m power-OK} ≥ 1−ε` (false `∀m` 形) から **per-codeword expurgation 形**に再 state:

- `∀m, mass{c | ∑ᵢ (c m i)² > nP} ≤ ε` (各 codeword 周辺の chi-square 上裾、engine を `φ=x²` で
  適用、`P'<P` slack で4次モーメント有限ゆえ WLLN/Markov、**指数 rate 不要**)。
- 2-stage `Measure.pi` 形を維持 (`gaussianCodebook` def を参照しない) ゆえ Walls.lean に残せる。
- `φ=x²` は4次モーメント有限で素直 (Wall 1 (i) の log-density `φ` より bottleneck 軽い)。

#### D4 — consumer restructure (`AchievabilityDischarge.lean` の `awgn_avg_error_union_bound:462` + `isAwgnTypicalityHypothesis:744`)

- **Wall 1 destructure** を (i)mass + (iii)indep-pair **保持**に変更 (現 `⟨A,hA_meas,_,_,_⟩` →
  `⟨A,hA_meas,hA_mass,hA_indep⟩`)、新 union-bound lemma (D2) に渡す。
- **barrier 再構築**: `g c := ∑_m Pe + M·𝟙_{∃m violate}` (all-or-nothing、`∀m` mass に直結) から
  `g c := ∑_m (Pe c m + 𝟙_{violate m}(c))` (per-codeword 合算) に再構築。`lintegral_finsetSum'` /
  `Finset.sum_le_sum` (既使用) で各 m 独立。
- **worst-half**: combined penalty `≤ 4ε_d2 < 1` が同一 m で `𝟙_violate=0` (power-OK) ∧
  `Pe≤4ε_d2` (error小) を強制。`awgn_expurgate_worst_half` (`:526`) は signature 不変で combined
  penalty を ℝ 化して渡せば再利用可。reindex 機構不変。

**Phase 依存順** (D1 engine+klDiv → D2 union-bound → D3+D4 power+consumer): D1 で engine wiring +
klDiv 積分解を確立すると D2 がその output を thread でき、D3 は同じ engine を `φ=x²` で再利用、
D4 は D2/D3 を consumer に配線する。Phase V で verify + 親同期 + 監査。

## 既存資産インベントリ (M0 で再確認、file:line)

新規 inventory は不要。本 plan が依拠する現存資産:

| 資産 | file:line | 用途 | sorryAx 状態 |
|---|---|---|---|
| `pi_empirical_mean_concentration` | `AWGN/AchievabilityAEP.lean:38` | (i)/(D3) engine: 有限-n Chebyshev 集中 (abstract μ+φ) | sorryAx-free (facts ledger) |
| `pi_empirical_mean_typical_mass` | `AWGN/AchievabilityAEP.lean:130` | (i)/(D3) engine: ∃N₀ で mass `≥ 1−η` の存在形 | sorryAx-free |
| `klDiv_pi_eq_sum` | `Shannon/MIChainRule.lean:249` | (iii): `klDiv (pi P) (pi Q) = ∑ klDiv P Q` (型クラス前提 = `IsProbabilityMeasure` のみ、M0 確認) | sorryAx-free (M0 確認) |
| `klDiv_prod_eq_add` | `Shannon/MIChainRule.lean:230` | (iii): prod の KL 加法分解 (型クラス前提 = `IsProbabilityMeasure` のみ、M0 確認) | sorryAx-free (M0 確認) |
| `klDiv_gaussianReal_gaussianReal_eq` | `Shannon/DifferentialEntropy.lean:672` | 1-D Gaussian KL closed form | (既存) |
| `awgnCodebookKernel` (+ `Kernel.measurable_kernel_prodMk_left`) | `AWGN/AchievabilityDischarge.lean:998-1028` | D2: `c ↦ Measure.pi (awgnChannel N (c m i))` の x-可測性 (壁でない、既コンパイル通過) | (既存、通過済) |
| `jointTypicalDecoder` (def) | `AWGN/AchievabilityDischarge.lean` (local) | D2: union-bound lemma が固定する decoder | (既存) |
| `awgn_expurgate_worst_half` | `AWGN/AchievabilityDischarge.lean:526` | D4: 既存 worst-half throwaway (`∑ Pe ≤ M·2ε ⇒ M/2 個が ≤ 4ε`)、signature 不変で combined penalty に再利用 | `@audit:ok` |
| `awgn_exists_codebook_le_avg` | `AWGN/AchievabilityDischarge.lean:509` | D4: codebook-average → ∃ codebook 抽出 | (既存) |
| `awgnPowerWitness_exists` | `AWGN/AchievabilityDischarge.lean:614` | D3: strict slack `P' < P` witness (4次モーメント有限) | `@audit:ok` |

> **converse 側資産 (achievability では不要)**: `jointDifferentialEntropyPi` 系
> (`Draft/Shannon/MultivariateDiffEntropy.lean:77`/`:542`/`:467`、`ParallelGaussian/Converse/Core.lean:145`)
> は旧 Phase 3 = Wall 1 (ii) statement-fix 専用だった。**D1 で (ii) を削除したため achievability
> では参照不要**。これらは converse line の資産として維持 (削除しない)。

**M0 で確定済 numeric/型予測** (verbatim 検証済 → facts ledger に再検証コマンド付きで記録):

- `jointDifferentialEntropyPi_pi_eq_sum` 結論形 = heterogeneous `∑ i, differentialEntropy (μ i)`
  (i.i.d. 特殊形でない)、sorryAx-free。**ただし (ii) 削除により achievability では不要化**。
- `klDiv_pi_eq_sum` / `klDiv_prod_eq_add` の型クラス前提 = `IsProbabilityMeasure` のみ
  (SigmaFinite/IsFiniteMeasure 不要)、両者 sorryAx-free → engine の `IsProbabilityMeasure` 維持要件と整合。
- (i) の `φ` = per-letter log-density の `MemLp φ 2`: Mathlib 直接補題なし (`memLp_id_gaussianReal`
  は id のみ)。in-project `integrable_density_log_density_of_gaussian`
  (`DifferentialEntropy.lean:86`) の二次多項式分解スタイルで自家製 wiring 要 = **Phase 1 (i) の
  bottleneck**。Wall 3 (D3) の `φ=x²` は4次モーメント有限で素直。
- 退化境界: `P=0` (Dirac) は `≪volume` を破る、`N=0` は `hv₂≠0` (klDiv closed form) を破る。両方とも
  既存 precondition (`hN:(N:ℝ)≠0` / `P>0`、`awgnPowerWitness_exists`) で吸収済。

## consumer restructure の影響範囲 (blast radius、`scripts/dep_consumers.sh` 実測)

3 壁すべて consumer は **`AchievabilityDischarge.lean` 1 file のみ**。`--transitive` で full blast
radius も 1 file 内 3 decl (他 family / lineage への波及なし)。主たる touch 先 = D4 の 2 consumer
`awgn_avg_error_union_bound:462` + `isAwgnTypicalityHypothesis:744`、wrapper
`awgn_achievability_F1_via_staged_hyps` → `awgn_theorem_F4_discharged_F1_via_staged` は signature
不変なら 1 行 pass-through で自動追従。

**重要な consumer 構造所見** (D1 (ii) 削除 / D2 retire / D3 再 state の波及を de-risk):

1. **Wall 1 (ii)/(iii) は現状 consumer で discard 済**。call site は AEP を
   `obtain ⟨A, hA_meas, _, _, _⟩` で destructure し (ii)/(iii) を捨てている。D4 では destructure を
   **(i)mass + (iii)indep-pair 保持**に変更 (`⟨A,hA_meas,hA_mass,hA_indep⟩`) し、新 union-bound
   lemma (D2) に渡す。**(ii) 削除は consumer 証明義務に波及しない** (もともと破棄されており、
   union bound 第2項 mass は (iii) が担うため)。
2. **Wall 2 (`awgnRandomCodingBound_holds`) は false ゆえ retire**。union bound の analytic content は
   D2 の新 genuine lemma `awgn_random_coding_union_bound` (AchievabilityDischarge.lean に新設) が
   担う。consumer は false lemma 呼出を新 lemma 呼出に差し替え。
3. **Wall 3 の barrier 再構築**。現状 consumer は power-OK mass を
   `g c := ∑_m Pe + M·𝟙_{∃m violate}` (all-or-nothing barrier) に畳んでいるが、D3 の per-codeword
   再 state に合わせて `g c := ∑_m (Pe c m + 𝟙_{violate m}(c))` (per-codeword 合算) に再構築。
   `lintegral_finsetSum'` / `Finset.sum_le_sum` (既使用) で各 m 独立、`awgn_expurgate_worst_half`
   (`:526`) は signature 不変で combined penalty を ℝ 化して渡せば再利用、reindex 機構不変。

**工数感**: 主たる実 touch は D4 = `isAwgnTypicalityHypothesis:744` の destructure 更新 + barrier
再構築 (Phase 5)、+ D2 新 lemma の新設 (Phase 4)。blast radius が 1 file 3 decl に限定 + worst-half
/ reindex 機構は不変ゆえ既存資産再利用が効く。

## Phase 詳細

### M0 — decomposition 再設計の feasible 確定 ✅ (proof-log: no)

**完了済 (2026-06-12、2 subagent 独立検証で feasible 確定、NO-GO なし)**:

- [x] import 構造の検証: `AchievabilityAEP` (AWGN 依存ゼロ) → `Walls.lean` → `AchievabilityDischarge.lean`、
      `Walls.lean` に `import ...AchievabilityAEP` を追加可 (cycle なし)
- [x] decomposition D1-D4 の確定 (Approach §D1-D4)、各要素の honesty (D2 thread = modular composition、
      bundle 非該当) を確認
- [x] M0 numeric/型予測の verbatim 確認 (`klDiv_*` 型クラス前提 = `IsProbabilityMeasure` のみ /
      `jointDifferentialEntropyPi_pi_eq_sum` 結論形 = heterogeneous sum (achievability では不要) /
      `MemLp φ 2` の自家製 wiring 要 = Phase 1 bottleneck / 退化境界 `P=0`/`N=0` は既存 precondition で吸収)
      → facts ledger に再検証コマンド付きで記録
- 撤退ライン: なし (確定済)

### Phase 1 — Wall 1 (D1): engine mass (i) + klDiv indep-pair (iii)、(ii) 削除 🚧 type-check done (commit eab36aa) (proof-log: yes)

**状態 (type-check done、deep atom 2 件 deferred)**:

- [x] `Walls.lean` に `import InformationTheory.Shannon.AWGN.AchievabilityAEP` を追加
- [x] `continuousAepGaussian_holds` を **∃可測A + bounds** に縮小、**(ii) volume bound を削除**。
      **加えて (iii) も false-statement と判明し statement-fix 済**: 旧指数 `−n·(klDiv_n−3ε)` が
      n を二重計上 `−n²I+3nε` になっていた → 監査確定の正しい形 `−(klDiv_n−n·3ε)=exp(−n(I−3ε))`
      に修正。これが本 line の **4 件目の false-statement 発見** (独立 honesty 監査 PASS、
      `@audit:retract-candidate(false-statement)` は fix で除去済、`wall:` → `plan:` 再分類済)。
- [x] genuine 済: `MeasurableSet A` / joint measure-identity (`arrowProdEquivProdArrow` + `pi_map_pi`) /
      (i) joint-mass (engine、`MemLp` 依存)。(iii) も engine + klDiv 積分解で結線。
- [ ] **deep atom ① `hφ_memLp`** (`MemLp φ 2`、honest sorry + `@residual(plan:awgn-achievability-walls-discharge-plan)`):
      **insight = dJ₁/dQ₁ = f_Z(y−x)/f_Y(y) で f_X が相殺 → φ は 1-D Gaussian 密度の比 (log)、
      2-D Gaussian 不要**。`integrable_density_log_density_of_gaussian` 風の二次多項式分解で閉じる見込み。
- [ ] **deep atom ② (iii) change-of-measure** (RN-deriv tensorize + setLIntegral、honest sorry +
      `@residual(plan:awgn-achievability-walls-discharge-plan)`)。
- 退化 (P=0/N=0) は **内部 branch (φ=0 a.e.) で処理**、precondition 不要 (M0 の「既存 precondition で
      吸収」より honest)。
- 撤退ライン (達成済): deep atom 2 件は `sorry + @residual(plan:awgn-achievability-walls-discharge-plan)`
      で deferred。engine は genuine、(i)/(iii) は `*Hypothesis` に bundle せず engine の abstract 形を維持
      (監査 PASS)。(ii)/(iii) の false-statement 除去は完遂済。

### Phase 4 — Wall 2 (D2): genuine union-bound lemma を AchievabilityDischarge に新設 🚧 gateway 達成 + 監査 all-OK + type-check done (commit 7c26322) (proof-log: yes)

**状態 (gateway 達成、新 lemma genuine、measure-identity sorry 2 件)**:

- [x] **gateway-atom-first 達成**: codebook-kernel 可測性は `awgnCodebookKernel` +
      `Kernel.measurable_kernel_prodMk_left` で discharge 済 (壁でない、consumer `:998-1028` 通過済)。
      **union bound 自体が壁でなく (i)/(iii) から組み上がることを type-check で確証** (gateway)。
- [x] 新 lemma `awgn_random_coding_union_bound` を **`AchievabilityDischarge.lean:475`** に新設:
      Wall 1 (i)/(iii) を hypothesis に thread + decoder = `jointTypicalDecoder A` 固定、
      union bound `∫⁻ Pe ≤ 2ε`。
- [x] **独立 honesty 監査 all-OK**: (i)/(iii)-as-hypotheses は **modular composition** (Wall1 conjunct と
      逐語一致の bare measure 不等式、core は body 側、load-bearing bundle 非該当)。
- [x] 5/7 atom genuine。
- [ ] **残 2 sorry** (`@residual(plan:awgn-achievability-walls-discharge-plan)`、各 ~50行 plumbing、
      監査が wall でなく plan と確認): **term1** (J marginal `J(Aᶜ)≤ε`、μX⊗channel=J) / **term2**
      (Q marginal + 和 + exp 算術)。
- [ ] 旧 false `awgnRandomCodingBound_holds` (Walls.lean) の retire は **D4 に繰延** (現状 並存)。
- 撤退ライン (達成済): union bound の measure-identity 2 件は `sorry +
      @residual(plan:awgn-achievability-walls-discharge-plan)` で deferred。**AEP thread は load-bearing
      bundle でない** (監査確定の modular composition、decoder は `jointTypicalDecoder A` 固定で
      `*Hypothesis` 化しない)。

### Phase 5a — Wall 3 (D3): per-codeword expurgation 形を新 lemma で genuine ✅ proof done / sorryAx-free (commit e4587aa) (proof-log: yes)

**状態 (proof done、sorryAx-free)**:

- [x] 新 lemma `awgnPowerConstraintPerCodeword_holds` (`Walls.lean:370`) を **genuine sorryAx-free** で追加:
      per-codeword 形 `∀m, mass{c | n·P_target < ∑ᵢ(c m i)²} ≤ ε`、engine φ=x² (MemLp 4次モーメント素直)
      + per-codeword marginal 同定 (`measurePreserving_eval`) + variance 同定。
- [x] **slack form 修正**: `P_cb<P_target` → **`(P_cb.toNNReal:ℝ)<P_target`** (分散値ベースが honest、
      D4 で `awgnPowerWitness_exists` の `0<P'<P` から導出可)。
- [x] 旧 false `awgnPowerConstraintHonest_holds` は **未 retire** (現状 並存、retire は D4)。

### D4 — consumer rewire (proof-log: yes)

旧 Wall2/3 (false) を retire + consumer を新 lemma 2 本に rewire + per-codeword barrier 再構築。
完了で headline が新 honest decomposition のみ依存。

- [ ] 旧 false `awgnRandomCodingBound_holds` (Walls.lean) + `awgnPowerConstraintHonest_holds` (Walls.lean)
      を **retire/削除**、consumer 呼出を新 lemma 2 本 (`awgn_random_coding_union_bound` /
      `awgnPowerConstraintPerCodeword_holds`) に差替
- [ ] **Wall 1 destructure** を (i)mass + (iii)indep-pair **保持**に変更 (`⟨A,hA_meas,_,_,_⟩` →
      `⟨A,hA_meas,hA_mass,hA_indep⟩`)、`awgn_random_coding_union_bound` に渡す
      (`AchievabilityDischarge.lean` の `awgn_avg_error_union_bound:462` + `isAwgnTypicalityHypothesis:744`)
- [ ] **per-codeword barrier 再構築** (`isAwgnTypicalityHypothesis:744` body): all-or-nothing
      barrier `g c := ∑_m Pe + M·𝟙_{∃m violate}` を per-codeword 合算 `g c := ∑_m (Pe c m + 𝟙_{violate m}(c))`
      に再構築。`lintegral_finsetSum'` / `Finset.sum_le_sum` (既使用) で各 m 独立
- [ ] worst-half: combined penalty `≤ 4ε_d2 < 1` が同一 m で power-OK ∧ error小 を強制。
      `awgn_expurgate_worst_half` (`:526`) は signature 不変で combined penalty を ℝ 化して渡す (reindex 機構不変)
- [ ] wrapper `awgn_achievability_F1_via_staged_hyps` / `awgn_theorem_F4_discharged_F1_via_staged` が
      signature 不変で自動追従することを確認 (pass-through 1 行)
- 撤退ライン: per-codeword barrier 再構築 / 旧 false 補題 retire は完遂必須 (false-statement 解消)。
      barrier 再構築 / consumer wiring が詰まる場合、consumer body のみ
      `sorry + @residual(plan:awgn-achievability-walls-discharge-plan)`。**旧 `∀m`/`∀decoder` false
      statement を残さない** (新 lemma が genuine output を供給済)。

### deep atoms — Phase 1/4 で deferred した plumbing sorry 4 件 (proof-log: yes)

全 `@residual(plan:awgn-achievability-walls-discharge-plan)`、各 ~50行 plumbing (監査が wall でなく plan と確認):

- [ ] Wall1 `hφ_memLp` (`MemLp φ 2`、insight = 1-D Gaussian 密度の比に因子化、f_X 相殺)
- [ ] Wall1 (iii) change-of-measure (RN-deriv tensorize + setLIntegral)
- [ ] Wall2 term1 (J marginal `J(Aᶜ)≤ε`、μX⊗channel=J)
- [ ] Wall2 term2 (Q marginal + 和 + exp 算術)

### Phase V — verify + 同期 + 監査 (proof-log: no)

- [ ] `lake env lean InformationTheory/Shannon/AWGN/Walls.lean` + `AchievabilityDischarge.lean` silent
- [ ] `#print axioms` で `awgn_achievability_F1_via_staged_hyps` / `awgn_theorem_F4_discharged_F1_via_staged`
      が sorryAx-free (= `[propext, Classical.choice, Quot.sound]`) を確認
- [ ] 親 `awgn-moonshot-plan.md` の進捗ブロック (Phase B / F-1 撤退ライン) の DAG/sub-plan 状態を
      更新 (本 Phase でのみ親に触れる、child SoT) + facts ledger 残存壁テーブルを更新
      (3 壁 → genuine: D1 (ii) 削除 / D2 false lemma retire / D3 per-codeword 再 state の経緯を 1 行ずつ)。
      **親子 co-stage** (pre-commit WARN)
- [ ] 独立 honesty 監査 (`honesty-auditor`): D1 (ii)削除 + (iii) statement-fix 後の縮小 signature が
      honest (4件目 false-statement 除去 + 残 bounds が真) + D2 新 lemma の AEP thread が load-bearing
      bundle 非該当 (modular composition、Phase 4 で all-OK 済 → deep atom closure 後の再確認) + D3 新
      lemma の honest 性 (Phase 5a で sorryAx-free) + `@residual` 分類正当性 + D4 consumer barrier
      再構築の sufficiency を検査

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。決着済 entry は削除 (git が履歴)。

### #4 (2026-06-12) Phase 1-5a の実装所見

- **(iii) indep-pair も false-statement (4 件目)**: M0 では (iii) を sound と判断していたが、実装時に
  指数 `−n·(klDiv_n−3ε)` が n を二重計上して `−n²I+3nε` になっていたと判明 → 監査確定の正しい形
  `exp(−n(I−3ε))` に statement-fix。**consumer に消費されない bound は型圧 (downstream type pressure)
  が不在ゆえ scaling error が生存し続けた** (achievability 3 補題が staged migration で個別検証されな
  かった足場であることの 4 件目の現れ)。これで Wall 1 由来の false-statement = (ii)/(iii) の 2 件。
- **Wall 2 = gateway 達成 (壁でなく plumbing)**: union bound は (i)/(iii) から組み上がり、kernel 可測性も
  既存 `awgnCodebookKernel` で discharge 済。新 lemma `awgn_random_coding_union_bound`
  (`AchievabilityDischarge.lean:475`) を type-check done で確証、AEP thread = modular composition (監査
  all-OK)。残 2 measure-identity sorry は wall でなく plan plumbing (各 ~50行)。
- **Wall 3 = genuine (sorryAx-free)**: 新 lemma `awgnPowerConstraintPerCodeword_holds` (`Walls.lean:370`)
  は engine φ=x² で素直に閉じた。
- **slack form 修正**: `P_cb<P_target` → `(P_cb.toNNReal:ℝ)<P_target` (分散値ベースが honest)。
- 新 lemma 2 本は旧 false 補題と **並存**、retire は D4 で一括。

### #3 (2026-06-12) M0 で decomposition 再設計を feasible 確定 (NO-GO なし)

2 subagent の独立検証で D1-D4 が feasible と確定。確定した 4 つの要:

- **(ii) volume bound は削除** (statement-fix でなく削除)。consumer が破棄済 + **union bound 第2項
  mass は (iii) が担当** (volume counting とは別軸) ゆえ load-bearing でない。
  `jointDifferentialEntropyPi` 系資産は achievability では不要化 (converse 側資産)。
- **Wall 2 は壁でない**。kernel 可測性 (`c ↦ Measure.pi (awgnChannel N (c m i))`) は既存
  `awgnCodebookKernel` + `Kernel.measurable_kernel_prodMk_left` で discharge 済 (consumer `:998-1028`
  で通過済)。残存壁 `IsParallelGaussianKernelMeasurable` (x-可測性) とは別物。genuine union-bound
  lemma を AchievabilityDischarge に新設し、AEP output を thread (modular composition、bundle 非該当)。
- **Wall 3 = per-codeword expurgation**。`∀m`-mass false 形 → `∀m, mass{∑ᵢ(c m i)²>nP}≤ε`、engine を
  `φ=x²` で適用 (4次モーメント有限、指数 rate 不要)。
- **per-codeword barrier は既存機構の微修正**。all-or-nothing → per-codeword 合算 barrier、worst-half
  / reindex 機構は signature 不変で再利用。

import 構造 (`AchievabilityAEP` → `Walls.lean` → `AchievabilityDischarge.lean`、cycle なし) +
退化境界 (`P=0`/`N=0` は既存 precondition で吸収) も verbatim 検証済 → facts ledger に確定事実記録。

### #2 (起草) judgment #3 / #7 の盲点を継承しない

judgment #3 (typicality plan、`klDiv` 形採用) は (ii) を `klDiv`-to-`volume` で書いたが、無限参照
`volume` の `ν.real univ = 0` 退化を見落とした (false statement)。judgment #7 (power-constraint
realizable pivot) は `P_cb < P_target` slack で `P_cb = P_target` 退化のみ patch し、
`∀m`-over-`exp(nR)` の指数 rate 障害を見落とした (false statement)。本 plan の statement-fix は
両盲点を解消する形 ((ii) = 真の `jointDifferentialEntropyPi` / Wall 3 = expected-fraction
expurgation) を採り、honest signature に置換する。

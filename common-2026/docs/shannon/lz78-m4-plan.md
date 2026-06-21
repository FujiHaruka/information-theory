# LZ78: M4 converse (Barron a.s. lift) サブ計画

> **Parent**: [`lz78-completion-roadmap.md`](lz78-completion-roadmap.md) §1 M4 / M5
> （M4 converse residual、ゴール = `lz78GreedyImpl_converse_ae`）

✅ **CLOSED (2026-06-21、commit `bd28e0e`、headline sorryAx-free、独立監査 PASS)**.
M4 converse `lz78GreedyImpl_converse_ae`（`GreedyParsingImpl.lean:1309`）は **genuine に
sorryAx-free で discharge 済**。`#print axioms lz78_asymptotic_optimality_with_greedy_impl
= [propext, Classical.choice, Quot.sound]`（sorryAx 非依存）。converse の唯一の
combinatorial 残作業だった G2 polynomial Kraft brick とその Part B 計数核は閉じた。
**verdict OVERTURN の教訓**: parent / コード docstring が当初 M4 を「research-level
エルゴード壁・scope-out」と framing していたが、gateway-atom-first 在庫が反証
（cause:single-route / gateway-atom-untried）し、本セッションの実装 3 leg で closed。

## 進捗

- [x] Phase 0 — M0 在庫確認（流用 + Kraft 用 Mathlib API 追補）✅
- [x] G4 — liminf assembly + SMB-liminf 配線（PURE WIRING）✅ sorryAx-free
- [x] G3 — Barron a.s.-eventual lift（Z-side テンプレ複写）✅ sorryAx-free
- [x] G2 — polynomial n-block Kraft（THE GENUINE NEW BRICK）✅ sorryAx-free
- [x] G1 — encoder / injectivity scaffolding（G2 の支援）✅ sorryAx-free
- [x] M5 — 最終合成 + headline sorryAx-free 判定（capstone）✅ `bd28e0e`

## ゴール（達成）

唯一の残 headline 壁 `lz78GreedyImpl_converse_ae`（`GreedyParsingImpl.lean:1309`、
Cover–Thomas Thm 13.5.3 lower bound、target = `entropyRate₂`）の sorry を discharge し、
headline `lz78_asymptotic_optimality_with_greedy_impl`（`:1943`、`@[entry_point]`）を
sorryAx-free 化する。achievability = upper half は leg 11 で既に sorryAx-free だったので、
本 plan が lower half を閉じた時点で squeeze（両半分 sorryAx-free）が完成し、
**LZ78 漸近最適性が標準B で完遂**。signature は source data（`μ`, `p`）+
`[IsProbabilityMeasure μ]` regularity のみ不変（hypothesis bundling なし）。

## Approach（達成形の記録）

標準 Barron a.s. source-coding converse: a.s. に
`liminf L_n/n ≥ liminf (-log₂ P_n)/n = entropyRate₂`（`L_n = lz78GreedyImplEncodingLength`）。
ergodic machinery（SMB-liminf / Q_k AEP / Z-side Barron テンプレ）は全て既存 sorry-free
だったので、新規 genuine は polynomial Kraft 1 brick（G2）に絞られた。4 brick の closure:

- **G4 — liminf assembly + SMB-liminf 配線** ✅ 既存 `algoet_cover_liminf_bound`（nat）を
  `Real.log 2 > 0` で bit 化し、`Filter.liminf_le_liminf` で G3 と連鎖して goal を組んだ
  （PURE WIRING、想定外コストなし = gateway 通過のシグナル）。
- **G3 — Barron a.s.-eventual lift** ✅ Z-side テンプレ複写。尤度比 `2^{-L_n}/P_n` の Markov
  bound + first Borel–Cantelli + p-series 総和可能 → `∀ᵐ ω, ∀ᶠ n, blockLogAvg₂ - error_n ≤ L_n/n`。
  唯一の外部入力 G2 を forward reference で消費。pointwise `2^{-L_n} ≤ P_n`（D6 FALSE）を
  建てない期待値→a.s. lift で成立（D6 準拠）。
- **G2 — polynomial n-block Kraft（THE GENUINE NEW BRICK）** ✅ `∑_x (1/2)^{L_n(x)} ≤ (n+1)²`
  （`lz78_block_kraft_poly`、`:956`）。在庫予測どおり parse は complete でなく
  （`lz78PhraseStrings_flatten_prefix`: `flatten ++ tail = input`）exact Kraft `∑ 2^{-lz} ≤ 1`
  は不成立 → polynomial slack `(n+1)²` を G3 の `log poly/n → 0` で吸収。Part A+C
  （Kraft sum を fiber count に reduce）を先に閉じ、最後の Part B 計数核を closure。
- **G1 — encoder / injectivity scaffolding** ✅ G2 の phrase-structure counting / `bitLength`
  decay。既存 phrase 不変量（`lz78PhraseStrings_nodup` 等）の再利用 + 新規計数 injection。

### 最後の counting fact closure（本 plan の核心成果）

Part B の有限計数核 `lz78_phrase_count_fiber_card_le`（`GreedyParsingImpl.lean:802`、
`#fiber(c) ≤ (n+1)·c!·|α|^c`）が converse の最後の open piece だった。これを
**新規 parent-extension 不変量 `lz78PhraseStrings_dropLast_earlier`**
（`GreedyLongestPrefix.lean:419` = 各 phrase の `dropLast` は LZ78 tree 上の earlier phrase）
を建て、その不変量を使った **injection cardinality bound**（fiber を「親 + 末尾シンボル」
へ写す単射の像 cardinality 上界）で genuine に discharge した。これにより G2 が、
従って converse `lz78GreedyImpl_converse_ae` が sorryAx-free 化し、headline の squeeze
（commit `bd28e0e`）が完成した。

### G2 の honesty 配置（達成形）

G2 は **shared sorry lemma として独立切り出し**（honest signature を持つ独立 lemma、
G3 が forward reference で消費）の方針で建て、closure 後は body genuine + `@audit:ok` 化。
核（Kraft bound）は main `lz78GreedyImpl_converse_ae` の仮説に encode されず、main の
signature は `(μ, p)` + regularity のみ不変。load-bearing bundling ではなく sanctioned
tier-2 → tier-1 への昇格（auditor 区別軸: 核が main の仮説に乗らない）。

## Phase 詳細（圧縮、各 1 行 CLOSED サマリ）

git が per-brick の証明設計詳細を持つ。以下は CLOSED 後の 1 行記録（commit は §進捗 / parent）。

- **Phase 0（M0 在庫）** ✅ M2/M3 在庫 + achievability threading / Q_k 資産を流用、Kraft
  brick 専用 Mathlib API（Borel–Cantelli / Markov / p-series / factorial 上界）を追補。
- **G4（liminf assembly）** ✅ `algoet_cover_liminf_bound`（nat）→ /log 2 bit 化 →
  `Filter.liminf_le_liminf` 連鎖で goal 組立、sorryAx-free（commit `81b2d56`）。
- **G3（Barron lift）** ✅ Z-side テンプレ（`MRatioLowerZ_le_sq_eventually` /
  `blockLogAvgZ_ge_negLogQInftyZ_minus_error`）複写、Markov + first Borel–Cantelli +
  p-series で a.s.-eventual per-n 比較を sorryAx-free（commit `81b2d56`）。
- **G2 Part A+C（Kraft → fiber count reduction）** ✅ Kraft sum を distinct-phrase 数 `c`
  でグループ化し fiber count に reduce、structure-Kraft 収束で `(n+1)²` 上界（commit `6dfff8f`、
  独立監査 PASS `65a4fd9`、single residual に確定）。
- **G2 Part B（fiber 計数核）** ✅ `lz78_phrase_count_fiber_card_le` を parent-extension
  不変量 `lz78PhraseStrings_dropLast_earlier` + injection cardinality bound で genuine
  closure（commit `bd28e0e`）→ G2 / converse sorryAx-free。
- **G1（scaffolding）** ✅ phrase-structure counting / `bitLength` decay、既存 phrase 不変量
  再利用 + 計数 injection 構成（G2 と同 leg）。
- **M5（capstone）** ✅ converse sorryAx-free 化で headline squeeze 完成、
  `#print axioms lz78_asymptotic_optimality_with_greedy_impl = [propext, Classical.choice,
  Quot.sound]` 確認 = 標準B 完遂（commit `bd28e0e`）。

## 地雷の不変条件（遵守確認、再探索禁止、parent §2）

- **D6** converse pointwise `2^{-L_n} ≤ P_n`（FALSE = LZ78 universality 核心）→ G3 は
  期待値（Markov）→ a.s. lift で建て、pointwise 不等式を建てなかった（遵守）。
- **D1/D2** per-block `c·log c ≤ -log P_n` FALSE → G2 は Kraft sum 上界（per-codeword 和）
  であって per-block combinatorial bound ではない（別物、抵触なし）。
- **D3** node-position-grouping 非 vanish → G2 の structure count は symbol-by-symbol
  enumeration（`c!·|α|^c`）であって LZ tree node-position grouping ではない（抵触なし）。
- **exact Kraft `∑ 2^{-lz} ≤ 1` 不成立（在庫予測が的中）**: parse incomplete ゆえ exact
  Kraft を狙わず polynomial `(n+1)²` で建て、slack を G3 error 項で吸収（遵守）。

## 判断ログ

1. **M4 CLOSED（2026-06-21、`bd28e0e`、verdict OVERTURN の決着）**: M4 を「research-level
   エルゴード壁・scope-out」とした旧 framing は **過大評価**だった（cause:single-route +
   gateway-atom-untried）。gateway-atom-first 在庫で反証 → 実装 3 leg（G4/G3 配線 + G2 Part
   A+C → G2 Part B）で closeable と判明し、本セッションで genuine sorryAx-free に閉じた。
   ergodic machinery（`algoet_cover_liminf_bound`、Z-side Barron テンプレ、Q_k AEP）は全て
   既存 sorry-free で、dominant 残は G2 polynomial Kraft 1 本のみだった（読み筋的中）。
2. **exact Kraft `∑ 2^{-lz} ≤ 1` 不成立（在庫予測が的中）**: parse incomplete
   （`lz78PhraseStrings_flatten_prefix`: `flatten ++ tail = input`）ゆえ符号長は tail を
   支払わない = lossless でなく、exact Kraft は狙えない。polynomial Kraft `(n+1)²` に設計し、
   slack を G3 error 項 `log poly/n → 0` で吸収する標準 Barron-with-polynomial-slack で closure。
3. **最後の counting fact = parent-extension 不変量 + injection で closure**: G2 Part B の
   `lz78_phrase_count_fiber_card_le`（fiber cardinality 上界）が converse 最後の open piece
   だったが、新規 `lz78PhraseStrings_dropLast_earlier`（各 phrase の `dropLast` が earlier
   phrase）+ fiber を「親 + 末尾シンボル」に写す injection の像 cardinality bound で genuine
   discharge。これで G2 / converse / headline が sorryAx-free 化。

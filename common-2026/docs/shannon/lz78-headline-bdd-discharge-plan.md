# LZ78 headline: boundedness 2 件 internal discharge サブ計画

> **Parent**: `docs/textbook-roadmap.md` §13 Ch.13 LZ78 (line 14 / 48 / 97 で
> M3/M4 scope-out + headline 2 satisfiable load-bearing hyp 言及)
> **Sibling (archive)**: `docs/shannon/lz78-residual-discharge-plan.md`
> (旧 successor 計画 = `Is*Passthrough` 述語の M3/M4 経由 discharge、本 plan は
> その scope を **継承しない**)
> **Created**: 2026-05-27 (`docs/shannon/awgn-f1-f3-peer-simultaneous-migration-plan.md`
> 完走後の honest tightening sweep の一環、planner 起草)
> **Status**: 設計起草、Phase 0 未着手

## Position

- **Headline (改善対象)**: `lz78_asymptotic_optimality`
  (`Common2026/Shannon/LempelZiv78.lean:382-419`) — Cover-Thomas Theorem
  13.5.3 の 2-sided sandwich form、現状 4 hypothesis (`h_lower` /
  `h_upper` / `h_bdd_above` / `h_bdd_below`)。
- **Goal**: 4 hyp → 2 hyp に削減した中間 headline
  `lz78_asymptotic_optimality_bdd_free` を新規 publish。`h_bdd_above` /
  `h_bdd_below` は LZ78 distinct-encoding の bit-layer counting envelope
  (`lz78PhraseStrings_count_isBigO` `Common2026/Shannon/LZ78ZivCountingBody.lean:408`、
  既に main 在庫) で **internal discharge**。`h_lower` / `h_upper`
  (Cover-Thomas Eq. 13.124 / 13.130) は M3/M4 research-level として
  textbook-roadmap で scope-out 確定済のため **本 plan では維持** (本 plan は
  scope-out 撤回を一切意図しない)。
- **下流効果**: external caller は `h_bdd_*` 2 件の boundedness 雑用 (Mathlib
  `Filter.IsBoundedUnder` の plumbing) を抱える必要がなくなり、純粋な
  Cover-Thomas Eq. 13.124 / 13.130 の 2 つの sandwich 不等式だけを供給すれば
  asymptotic optimality `Tendsto … (𝓝 entropyRate)` a.s. を得る形に簡素化。
  外形は「2 hypothesis 残存だが boundedness 雑用を内部消化した中間 headline」
  であり、honesty 階層 (`docs/audit/audit-tags.md` Tier 1)。

## Motivation

`lz78_asymptotic_optimality` (`LempelZiv78.lean:382`) は §3 の **genuine
non-circular** 2-sided sandwich form として publish 済 (`tendsto_of_le_liminf_of_limsup_le`
で genuine combine、body は `lz78_asymptotic_optimality_two_sided` /
`lz78_asymptotic_optimality_of_bounds` で alias)。しかし 4 hypothesis
中 2 件 (`h_bdd_above` / `h_bdd_below`) は **bit-layer counting で elementary
discharge 可能** な雑用であり、external caller に押し付ける形は honesty バーを
最大化していない。

archeology で確認 — 削除済 `Common2026/Draft/Shannon/LZ78DistinctEncoding.lean`
(commit `f67ec8a^`、433 行) には `lz78DistinctEncodingLength_isBoundedUnder_le`
(`:331`) + `_ge` (`:374`) の **genuine 実装** が存在し、`lz78PhraseStrings_count_isBigO`
(Cover-Thomas Eq. 13.124 の `c(n) = O(n / log n)` 計数包絡) + `LZ78Phrase.bitLength`
plumbing で elementary に通っていた。これらが scope-out された理由は §4 の
headline `lz78_two_sided_optimality_distinct_bdd_free` (`:414`) が
`Is*ChainHyp` 述語に **load-bearing hypothesis bundling** していた tier-5
defect 側であり、§1-§3 (boundedness 2 件 + counting envelope の wrapper) 自体は
無罪。

更に重要な事実 — 当時 §1-§3 が依存していた `lz78PhraseStrings_count_isBigO` /
`LZ78Phrase.bitLength` / `LZ78Parsing.encodingLength` の供給元 (`LZ78GreedyParsing.lean`
544 行、`LZ78ZivCountingBody.lean` 420 行、`LZ78PhraseCountAsymptoticBody.lean`
243 行、`LZ78GreedyLongestPrefix.lean` 271 行、計 1478 行) は **すべて現存
`Common2026/Shannon/` 配下に sorry なし live**。scope expansion (削除済
infrastructure の連鎖復活) は不要、§1-§3 単体 (~150 行) を `LempelZiv78.lean`
配下に再構築して boundedness 2 件を internal discharge + 中間 headline 1 件を
combine するだけで本 plan は閉じる。

## 前提条件 verbatim 照合 (CLAUDE.md「具体的数値・型予測の verbatim 確認」)

Plan 設計時点で照合済の事実 (Phase 0 で再確認の対象):

| 確認対象 | 実コード location | verbatim 値 |
|---|---|---|
| `lz78_asymptotic_optimality` 結論型 | `LempelZiv78.lean:410-416` | `∀ᵐ ω ∂μ, Filter.Tendsto (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ)) Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess))` |
| `lz78_asymptotic_optimality` body | `LempelZiv78.lean:417-419` | `filter_upwards [h_lower, h_upper, h_bdd_above, h_bdd_below] with ω hl hu hba hbb; exact tendsto_of_le_liminf_of_limsup_le hl hu hba hbb` (genuine combine、本 plan の中間 headline はこれを internal call) |
| `tendsto_of_le_liminf_of_limsup_le` Mathlib signature | Mathlib `Topology/Order/LiminfLimsup.lean` (LempelZiv78.lean:6 で import 済) | 結論 `Tendsto f l (𝓝 x)`、hypothesis `liminf ≤ x`、`limsup ≤ x` から `Tendsto`、加えて `IsBoundedUnder (· ≤ ·)` + `IsBoundedUnder (· ≥ ·)` 必要 (Mathlib `liminf` / `limsup` の定義域条件) |
| `lz78PhraseStrings_count_isBigO` 結論型 | `LZ78ZivCountingBody.lean:408-411` | `(fun n => ((lz78PhraseStrings (input n)).length : ℝ)) =O[atTop] (fun n => (n : ℝ) / Real.log (n : ℝ))` (Cover-Thomas Eq. 13.124、`O(n / log n)` 計数包絡、`@[entry_point]`、main 在庫、sorry なし) |
| `lz78PhraseStrings_count_le` 結論型 | `LZ78GreedyLongestPrefix.lean:260` (再確認: 旧 `f67ec8a^` 形式から現行 lookup) | `(lz78PhraseStrings input).length ≤ input.length` (Phase A の `c(n) ≤ n` bound、main 在庫、sorry なし) |
| `LZ78Phrase.bitLength` def | `LZ78GreedyParsing.lean:108`-`:113` | `Nat.log 2 (c + 1) + Nat.log 2 a + 2`、定義 + `_eq` + `_mono_left` + `_pos` 既存 |
| `LZ78Parsing.encodingLength` def | `LZ78GreedyParsing.lean:143-144` | `p.count * LZ78Phrase.bitLength p.count a` |
| 削除済 `lz78DistinctEncodingLength` 旧 def | `git show "f67ec8a^:common-2026/Common2026/Draft/Shannon/LZ78DistinctEncoding.lean":128-129` | `noncomputable def lz78DistinctEncodingLength (n : ℕ) (x : Fin n → α) : ℕ := (lz78DistinctParsing (List.ofFn x)).encodingLength (Fintype.card α)` |
| 削除済 `lz78DistinctEncodingLength_isBoundedUnder_le` 旧 body サイズ | `git show "f67ec8a^:common-2026/Common2026/Draft/Shannon/LZ78DistinctEncoding.lean":331-372` | 41 行 (`Filter.Eventually.of_forall` + `lz78DistinctEncodingLength_rate_isBigO_one` 経由)、sorry なし |
| 削除済 `lz78DistinctEncodingLength_isBoundedUnder_ge` 旧 body サイズ | `git show "f67ec8a^:common-2026/Common2026/Draft/Shannon/LZ78DistinctEncoding.lean":374-388` | 14 行 (`isBoundedUnder_of_eventually_ge (a := 0)` + `_per_symbol_nonneg`)、sorry なし |
| 旧 §4 headline (load-bearing bundling defect、本 plan は復活させない) | `git show "f67ec8a^:common-2026/Common2026/Draft/Shannon/LZ78DistinctEncoding.lean":414-432` | `IsLZ78AchievabilityChainHyp` + `IsLZ78ConverseChainHyp` 述語を hypothesis に取って body `sorry`、tier-5 load-bearing hypothesis bundling defect。本 plan は **代わりに `h_lower` / `h_upper` 直接 hyp 形** で再構築 |
| 計数包絡が main で live | `rg -c sorry` × 6 files | `LZ78GreedyLongestPrefix.lean` (271 行) / `LZ78ZivCountingBody.lean` (420 行) / `LZ78GreedyParsing.lean` (544 行) / `LZ78GreedyParsingImpl.lean` (474 行) / `LZ78PhraseCountAsymptoticBody.lean` (243 行) / `LZ78ZivInequality.lean` (307 行) **全 0 sorry**、合計 2,259 行 |

**重要**: 旧 §4 headline は load-bearing hypothesis bundling (tier-5 defect、
CLAUDE.md「検証の誠実性」) のため、本 plan では **`Is*ChainHyp` 述語を一切
復活させない**。本 plan の中間 headline は `h_lower` / `h_upper` を述語で
bundle せず生の `∀ᵐ ω ∂μ, ...` hypothesis として残し、boundedness 2 件だけを
internal discharge する形に変える。これにより旧 §4 の defect を継承せず、
かつ本 plan の追加 hypothesis 数は **0** (4 → 2 削減のみ)。

## Scope

担当範囲:

| 対象 | 役割 | 行数見積もり |
|---|---|---|
| `Common2026/Shannon/LempelZiv78.lean` (既存拡張) or `Common2026/Shannon/LZ78DistinctEncoding.lean` (新規) | (A) `lz78DistinctEncodingLength` 定義復活 (削除済 `Draft/.../LZ78DistinctEncoding.lean:128` から cherry-pick) + (B) Phase B 計数包絡経由の rate `=O 1` 補題 + (C) `_isBoundedUnder_le` / `_ge` 補題 2 件 + (D) 中間 headline `lz78_asymptotic_optimality_bdd_free` | ~250-350 (削除済 §1-§3 ~280 行 + 中間 headline ~30 行) |
| `Common2026.lean` | 新規 file 追加時のみ import 1 行追加 | +1 |
| `Common2026/Shannon/LempelZiv78.lean` 既存 (line 380-529) | 変更なし (`lz78_asymptotic_optimality` / `_two_sided` / `_of_bounds` は不変、本 plan は **新規 headline** を追加するだけ) | 0 |

**file 配置の判断**: §3 章末「Phase 0 — Mathlib-shape-driven 設計選択」で
新規 file `LZ78DistinctEncoding.lean` 路線 vs `LempelZiv78.lean` 拡張路線を
確定 (判断ログ #1 の対象)。現時点予測: 新規 file 路線 (削除済 file との対応が
取りやすく、`LempelZiv78.lean` の §3 (Main theorem) が「distinct」に固定されない
ことを保ちたい、`LZ78ZivCountingBody.lean` を新 import 経路にせず既存 import
グラフを乱さない)。

新規 file 不要となる条件 — `LempelZiv78.lean` 末尾に §4 として追記し、削除済
file の docstring / 命名を `LZ78DistinctEncoding` namespace 配下で `LempelZiv78.lean`
内に押し込む。判断ログ #1 で確定。

合計 ~250-350 行。新規 `@residual` 0 件 (proof done 達成可能)、ただし
boundedness 2 件以外の中間補題 (例えば `bitCost_isBigO_log`, `natLog_succ_isBigO_log`)
で Mathlib 計算が引っかかった場合は撤退ライン L-BDD-1 で `sorry + @residual`
ルートに切替 (詳細 §「撤退ライン」)。

## ゴール / Approach

### Goal の verbatim 形

```lean
@[entry_point]
theorem lz78_asymptotic_optimality_bdd_free
    {α Ω : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (h_lower : ∀ᵐ ω ∂μ,
        entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n =>
              (lz78DistinctEncodingLength n
                  (p.toStationaryProcess.blockRV n ω) : ℝ)
                / (n : ℝ))
            Filter.atTop)
    (h_upper : ∀ᵐ ω ∂μ,
        Filter.limsup
          (fun n =>
            (lz78DistinctEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78DistinctEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) := by
  exact lz78_asymptotic_optimality μ p lz78DistinctEncodingLength
    h_lower h_upper
    (lz78DistinctEncodingLength_isBoundedUnder_le μ p)
    (lz78DistinctEncodingLength_isBoundedUnder_ge μ p)
```

**注**: `lz78EncodingLength` を `lz78DistinctEncodingLength` に **specialization**
する選択を Phase 0 / 判断ログ #2 で確定する。Phase 0 で外形互換性の検討
(`lz78EncodingLength` 抽象維持 vs `lz78DistinctEncodingLength` 固定) を行い、
固定路線を採用する見込み (理由は §「Approach (全体戦略)」)。

### Approach (全体戦略)

```
[既存 main 在庫 (sorry 0)]                    [削除済 §1-§3 から cherry-pick]    [既存 main headline]
  LZ78Phrase.bitLength                          lz78DistinctRootPhrases (def)     lz78_asymptotic_optimality
  LZ78Phrase.bitLength_eq                       lz78DistinctParsing (def)         (LempelZiv78.lean:382)
  LZ78Phrase.bitLength_mono_left                lz78DistinctParsing_count
  LZ78Phrase.bitLength_pos                      lz78DistinctEncodingLength (def)
  LZ78Parsing.encodingLength                    lz78DistinctEncodingLength_eq
  lz78PhraseStrings_count_le                    lz78Distinct_count_ofFn_le
   (= c(n) ≤ n、Eq. 13.124 前段)                lz78DistinctEncodingLength_le
  lz78PhraseStrings_count_isBigO                lz78DistinctEncodingLength_per_symbol_nonneg
   (= c(n) =O n/log n、Eq. 13.124、main 在庫)   lz78DistinctEncodingLength_real_per_symbol_le
  isBigO_natCast_div_log_of_mul_log_le          natLog_succ_isBigO_log
   (genuine inversion lemma)                    bitCost_isBigO_log
  Real.log / Nat.log Mathlib API                lz78DistinctEncodingLength_rate_isBigO_one
                                                lz78DistinctEncodingLength_isBoundedUnder_le
                                                lz78DistinctEncodingLength_isBoundedUnder_ge
       │                                                            │                       │
       └──────────────────────────────┬─────────────────────────────┘                       │
                                      ▼                                                     │
       Phase 0  archeology 再確認 + file 配置確定 + `lz78EncodingLength` specialization 判断 │
       Phase 1  cherry-pick + 既存 main lemma との signature align + 計数包絡 chaining       │
       Phase 2  boundedness 2 件 (`_le` / `_ge`) genuine 復活、internal call で 0 hyp        │
       Phase 3  中間 headline `lz78_asymptotic_optimality_bdd_free` ───────────────────────► (既存 internal call)
                  body: `lz78_asymptotic_optimality μ p lz78DistinctEncodingLength
                          h_lower h_upper
                          (lz78DistinctEncodingLength_isBoundedUnder_le μ p)
                          (lz78DistinctEncodingLength_isBoundedUnder_ge μ p)`
                  → 4 hyp form の `h_bdd_*` 2 件を internal discharge、`h_lower` / `h_upper` 残存
       Phase V  lake env lean silent + `Common2026.lean` 編入 + honesty audit + proof-log
```

### Mathlib-shape-driven 設計選択

**選択 1: `lz78EncodingLength` 抽象維持 vs `lz78DistinctEncodingLength` 固定**
(Phase 0 / 判断ログ #2 で確定):

- **抽象維持**: 中間 headline も `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ`
  を parameter のまま受け、boundedness 2 件は **追加 hypothesis** として
  残す形 (4 hyp → やはり 4 hyp、削減効果なし、本 plan の意義喪失)。
- **`lz78DistinctEncodingLength` 固定** (推奨): 削除済 §1-§3 で実装されていた
  bit-layer counting envelope は **distinct 形に対してのみ** elementary な
  `=O 1` envelope を返す (一般 `lz78EncodingLength` は `lz78GreedyParse` で
  worst-case `count = n` になり per-symbol rate が log で発散 — 削除済
  `LZ78FinalGlue.lean` で観測された問題、archeology の docstring が
  `lz78DistinctEncoding.lean:30-37` で明記)。よって boundedness 2 件を internal
  discharge するには distinct 形に固定する必要があり、本 plan の中間 headline は
  `lz78DistinctEncodingLength` 固定で publish する。
  **trade-off**: 抽象 `lz78EncodingLength` 形での `lz78_asymptotic_optimality`
  は既に main で publish 済 (`LempelZiv78.lean:382`)、本 plan の中間 headline は
  並列に publish (既存を変更しない)。external caller は (a) 抽象 4 hyp 形を
  使うか (b) 本 plan の distinct 固定 2 hyp 形を使うかを選べる。

**選択 2: file 配置** (Phase 0 / 判断ログ #1 で確定):

- **新規 file `LZ78DistinctEncoding.lean`** (推奨): 削除済 file との対応が
  archeology cherry-pick で再現しやすく、`LempelZiv78.lean` の §3 (Main
  theorem) が「distinct」に bind されない (抽象 form の publish 性質を保つ)。
  `Common2026.lean` に新 import 1 行追加、依存は `LempelZiv78.lean` + 既存
  `LZ78GreedyParsing.lean` + `LZ78ZivCountingBody.lean` + `LZ78GreedyLongestPrefix.lean`。
- **`LempelZiv78.lean` 拡張**: §4 として追記。新規 file 不要だが、§3 の
  「抽象 form」と §4 の「distinct 固定 form」が同じ file 内で混在し、
  `LempelZiv78.lean` が `LZ78ZivCountingBody.lean` 等の下流 file に依存する
  形に変わる (現状は import なし)。下流 file 依存の追加は import graph の
  cycle 可能性を Phase 0 で verbatim 確認する必要があり、リスクあり。

**選択 3: `Filter.IsBoundedUnder` Mathlib shape**:
`tendsto_of_le_liminf_of_limsup_le` (Mathlib `Topology/Order/LiminfLimsup.lean`)
が要求する hypothesis 形は `IsBoundedUnder (· ≤ ·) atTop f` + `IsBoundedUnder
(· ≥ ·) atTop f`。これは既存 `lz78_asymptotic_optimality` の `h_bdd_above` /
`h_bdd_below` と verbatim 同形 (`LempelZiv78.lean:400-409`)、よって Phase 2 の
boundedness 2 件はこの形を **直接** 生成する。削除済 file の
`Filter.isBoundedUnder_of_eventually_le (a := C)` / `Filter.isBoundedUnder_of_eventually_ge (a := 0)`
(`LZ78DistinctEncoding.lean:354` / `:387`) を再利用、Mathlib lookup 不要。

### 段階的 ship 設計

本 plan は **atomic ではない** — Phase 1 (cherry-pick) 完了時点で
`lz78DistinctEncodingLength` 定義 + 計数包絡が main で publish 済になり、中間
ship として価値あり (将来 boundedness 2 件以外の応用 e.g. Cover-Thomas
Eq. 13.130 lower bound 形にも使える)。Phase 2 (boundedness 2 件) 完了時点で
本来の goal `lz78_asymptotic_optimality_bdd_free` (Phase 3) が組める。

partial ship: Phase 1 完了 → commit / push、Phase 2 完了 → commit / push、
Phase 3 完了 → 最終 commit + Common2026.lean 編入 + honesty audit。

### 規模見積もり

| Sub-step | 内容 | 行数 | 依存 | Mathlib / Common2026 在庫 |
|---|---|---|---|---|
| Phase 0 | archeology 再確認 + file 配置確定 + `lz78EncodingLength` specialization 判断 | 0 (docs 更新 / 判断ログ #1 #2 のみ) | — | — |
| Phase 1-A | `lz78DistinctRootPhrases` def + `_length` simp 補題 (削除済 `:82-95`) | ~15 | Phase 0 | `LZ78Phrase` `LempelZiv78.lean:135` 在庫済 |
| Phase 1-B | `lz78DistinctParsing` def + `_count` 補題 (削除済 `:97-125`) | ~20 | Phase 1-A | `LZ78Parsing` `LempelZiv78.lean:177` 在庫済 |
| Phase 1-C | `lz78DistinctEncodingLength` def + `_eq` + `_le` (削除済 `:128-163`) | ~30 | Phase 1-B + `LZ78GreedyParsing.encodingLength` | 在庫済 |
| Phase 1-D | `lz78Distinct_count_ofFn_le` + `_per_symbol_nonneg` (削除済 `:143-167`) | ~15 | Phase 1-C + `lz78PhraseStrings_count_le` `LZ78GreedyLongestPrefix.lean` | 在庫済 |
| Phase 1-E | `lz78DistinctEncodingLength_real_per_symbol_le` (削除済 `:180-202`) | ~25 | Phase 1-D | Real arithmetic + `bitLength_eq` |
| Phase 1-F | `natLog_succ_isBigO_log` + `bitCost_isBigO_log` (削除済 `:205-271`) | ~70 | Phase 1-E + Mathlib `Real.log` API | `Real.log_le_log` / `Real.logb` / `Real.natLog_le_logb` (削除済 file で使用済、Mathlib 在庫確認は Phase 0 で再 verify) |
| Phase 1-G | `lz78DistinctEncodingLength_rate_isBigO_one` (削除済 `:273-329`) | ~50 | Phase 1-F + `lz78PhraseStrings_count_isBigO` `LZ78ZivCountingBody.lean:408` | 在庫済 |
| Phase 2-A | `lz78DistinctEncodingLength_isBoundedUnder_le` (削除済 `:331-372`) | ~30 | Phase 1-G | `Filter.isBoundedUnder_of_eventually_le` Mathlib 在庫 |
| Phase 2-B | `lz78DistinctEncodingLength_isBoundedUnder_ge` (削除済 `:374-388`) | ~12 | Phase 1-D | `Filter.isBoundedUnder_of_eventually_ge` Mathlib 在庫 |
| Phase 3 | 中間 headline `lz78_asymptotic_optimality_bdd_free` | ~25 | Phase 2-A + Phase 2-B + 既存 `lz78_asymptotic_optimality` | 既存 internal call のみ |
| Phase V | lake env lean silent + `Common2026.lean` 編入 + honesty audit dispatch + proof-log | 0-10 | Phase 3 | — |

**合計**: 自作 ~292 行 (中央予測)、削除済 file の §1-§3 (~315 行) からの
cherry-pick が大半、新規実装は中間 headline (Phase 3 ~25 行) のみ。
1 session で closure 見込み。`@residual` 0 件 (proof done 直行)。

## 進捗

- [ ] Phase 0 — archeology 再確認 + file 配置確定 + specialization 判断 📋
- [ ] Phase 1-A — `lz78DistinctRootPhrases` def + `_length` 📋
- [ ] Phase 1-B — `lz78DistinctParsing` def + `_count` 📋
- [ ] Phase 1-C — `lz78DistinctEncodingLength` def + `_eq` + `_le` 📋
- [ ] Phase 1-D — `lz78Distinct_count_ofFn_le` + `_per_symbol_nonneg` 📋
- [ ] Phase 1-E — `_real_per_symbol_le` 📋
- [ ] Phase 1-F — `natLog_succ_isBigO_log` + `bitCost_isBigO_log` 📋
- [ ] Phase 1-G — `_rate_isBigO_one` 📋
- [ ] Phase 2-A — `_isBoundedUnder_le` 📋
- [ ] Phase 2-B — `_isBoundedUnder_ge` 📋
- [ ] Phase 3 — 中間 headline `lz78_asymptotic_optimality_bdd_free` 📋
- [ ] Phase V — verify + `Common2026.lean` 編入 + honesty audit + proof-log 📋

**proof-log**: `proof-log: yes` (`docs/proof-logs/proof-log-lz78-headline-bdd-discharge.md`、
Phase 1 cherry-pick + Phase 2 boundedness + Phase 3 headline の per-step
diagnostic 記録、特に Phase 1-F の Mathlib `Real.natLog_le_logb` lookup 結果)。

## Phase 詳細

### Phase 0 — archeology 再確認 + file 配置確定 + specialization 判断

- [ ] (P0-1) `git show "f67ec8a^:common-2026/Common2026/Draft/Shannon/LZ78DistinctEncoding.lean"`
      を再 archeology、`:82-388` の verbatim を Read で記録 (Phase 1 の cherry-pick source)
- [ ] (P0-2) 削除済 file が依存していた imports
      (`LZ78GreedyParsing` / `LZ78GreedyParsingImpl` / `LZ78GreedyLongestPrefix` /
      `LZ78ZivCountingBody`) の現行 main signature を `rg`/`loogle` で verbatim
      確認 — 特に `lz78PhraseStrings_count_isBigO` (`LZ78ZivCountingBody.lean:408`)
      と `lz78PhraseStrings_count_le` (`LZ78GreedyLongestPrefix.lean:260`) の
      signature が削除済 file 当時と整合するか
- [ ] (P0-3) Mathlib `Real.natLog_le_logb` / `Real.log_pos` / `Real.log_le_log` /
      `Real.logb` / `isBigO` API の在庫を loogle で再 verify
      (削除済 file は当時の Mathlib バージョン依存、現行 Mathlib で named
      が変わっている可能性をチェック)
- [ ] (P0-4) **判断ログ #1 (file 配置)**: 新規 `LZ78DistinctEncoding.lean` vs
      `LempelZiv78.lean` 拡張。新規 file 路線で `Common2026.lean` に import 1 行
      追加、`LempelZiv78.lean` は変更なし
- [ ] (P0-5) **判断ログ #2 (specialization)**: 中間 headline で
      `lz78EncodingLength` 抽象維持 vs `lz78DistinctEncodingLength` 固定。
      boundedness 2 件の elementary discharge には distinct 形固定が必須
      (Approach §「Mathlib-shape-driven 設計選択」選択 1)、よって固定路線
- [ ] (P0-6) `LempelZiv78.lean` → 新 file の import 方向確認 (新 file が
      `LempelZiv78.lean` を import する形、逆ではない)。`LZ78ZivCountingBody.lean`
      自体が `LempelZiv78.lean` を import していないか追加確認 (循環防止)

### Phase 1 — distinct encoding length + counting envelope cherry-pick

(削除済 `LZ78DistinctEncoding.lean:60-329` の §1-§3 をほぼ verbatim 復活、
Phase 0 で確認した API 変動分のみ手動修正)

- [ ] (P1-A) `lz78DistinctRootPhrases` (削除済 `:82-89`) + `_length` (削除済 `:90-95`)
- [ ] (P1-B) `lz78DistinctParsing` (削除済 `:97-110`) + `_count` (削除済 `:111-126`)
- [ ] (P1-C) `lz78DistinctEncodingLength` def (削除済 `:128-130`) + `_eq` (削除済
      `:132-141`) + `_le` (削除済 `:151-163`)
- [ ] (P1-D) `lz78Distinct_count_ofFn_le` (削除済 `:143-149`) +
      `_per_symbol_nonneg` (削除済 `:165-167`)
- [ ] (P1-E) `lz78DistinctEncodingLength_real_per_symbol_le` (削除済 `:180-202`)
- [ ] (P1-F) `natLog_succ_isBigO_log` (削除済 `:205-237`) + `bitCost_isBigO_log`
      (削除済 `:239-271`)
- [ ] (P1-G) `lz78DistinctEncodingLength_rate_isBigO_one` (削除済 `:273-329`)
- [ ] (P1-V) lake env lean silent on 新 file (Phase 2 着手前の checkpoint)

### Phase 2 — boundedness 2 件 internal discharge

- [ ] (P2-A) `lz78DistinctEncodingLength_isBoundedUnder_le` (削除済 `:331-372`)
- [ ] (P2-B) `lz78DistinctEncodingLength_isBoundedUnder_ge` (削除済 `:374-388`)
- [ ] (P2-V) lake env lean silent on 新 file

### Phase 3 — 中間 headline

- [ ] (P3-1) `lz78_asymptotic_optimality_bdd_free` を新 file 末尾に publish
      (signature は §「Goal の verbatim 形」、body は 既存
      `lz78_asymptotic_optimality` を `h_bdd_*` 2 件分を Phase 2 出力で internal
      discharge して呼出すだけ ~25 行)
- [ ] (P3-2) `@[entry_point]` マーキング (`Common2026/Meta/EntryPoint.lean`)
- [ ] (P3-V) lake env lean silent + `Common2026.lean` 編入 (新 file の import 1 行追加)

### Phase V — 検証 + closure

- [ ] (PV-1) lake env lean 新 file silent (0 errors / 0 sorry warning、proof done
      直行を verify)
- [ ] (PV-2) `Common2026.lean` 編入後、`lake env lean Common2026.lean` または
      `lake build Common2026.<new-file>` で olean refresh
- [ ] (PV-3) **honesty audit dispatch** (orchestrator が `honesty-auditor` subagent
      を起動、起動条件は新規 `@residual` 導入なし + signature 改変なしなので任意だが、
      新規 file 1 件 publish + 中間 headline 新規 publish のため preventive audit を
      推奨)
- [ ] (PV-4) proof-log `docs/proof-logs/proof-log-lz78-headline-bdd-discharge.md`
      に Phase 1 / 2 / 3 の diagnostic 記録 (特に Phase 1-F の Mathlib lookup 結果と
      Phase 0 archeology 差分)
- [ ] (PV-5) 本 plan 進捗 ✅ + handoff close

## 撤退ライン

各 L-BDD-* は **L-BDD-1 → L-BDD-3** の優先度順で発火。発火時は当該 Phase で
`sorry + @residual(plan:lz78-headline-bdd-discharge-plan)` で抜き、signature は
本来の hypothesis-free 形 (boundedness 2 件削減) を保つ。

### L-BDD-1: Mathlib API 変動による `natLog_succ_isBigO_log` / `bitCost_isBigO_log` 不通

**発火条件**: Phase 1-F で削除済 file の `Real.natLog_le_logb` / `Real.logb` /
`Real.log_pos` 使用箇所が現行 Mathlib で named 変動 / 廃止されており、loogle で
代替が見つからない (Phase 0-3 で予測済の場合は事前回避、想定外発火時のみ)。

**対処**:
- (a) loogle で代替 lemma を 15 分以内に探す
- (b) 見つからない場合 → 当該 sub-step を `sorry + @residual(wall:mathlib-real-log)` で
      抜き、中間 headline は **本 Phase の `_isBigO_one` 出力に依存する Phase 2** まで
      `sorry` が伝播する形で stage。Phase 3 の中間 headline 自体は genuine combine
      (`lz78_asymptotic_optimality` の internal call) のため `sorry` を含まないが、
      boundedness 2 件の internal discharge が `sorry` 経由になる
- (c) この場合の `@residual` class は `wall:mathlib-real-log`、slug は
      `lz78-headline-bdd-discharge-plan-P1F`

**規模**: 最悪 Phase 1-F の ~70 行が `sorry` 化、Phase 1-G 以降も伝播 sorry 化、
Phase 2 / 3 は genuine。本 plan の proof done 取得は遅延、type-check done で
commit + ship。

### L-BDD-2: 削除済 file の他依存先連鎖復活が必要 (現実化リスク低、Phase 0 で除外確認)

**発火条件**: Phase 0-2 の verbatim 確認で削除済 `LZ78DistinctEncoding.lean` が
**実際には現存 main 在庫以外** (例えば削除済の `LZ78FinalGlue.lean` の
`IsLZ78AchievabilityChainHyp` などの load-bearing 述語) を陽に / 暗に depend
していたことが判明、§1-§3 単独の cherry-pick が closed not。

**対処**:
- (a) 削除済 §1-§3 のうち他依存箇所を **明示的に取り除いた縮小版** を Phase 1 で
      再構築 (load-bearing 述語への参照を切り、boundedness 2 件に必要最低限の
      補題だけを移植) — 規模 ~20-50 行削減
- (b) それでも閉じない場合 → 本 plan 全体を partial ship に縮小、Phase 3 中間
      headline は publish せず Phase 1 完了 (= `lz78DistinctEncodingLength` 単体
      publish + counting envelope) で commit、Phase 2 以降は別 plan に分離
- (c) 最悪 case: 本 plan 全体撤退、`lz78_asymptotic_optimality` の 4 hyp form を
      そのまま据置 (現状維持)、改善なし。`docs/textbook-roadmap.md` §13 に
      「boundedness 2 件 internal discharge は L-BDD-2 発火で断念」記録追記

**予測**: Phase 0 で `git show "f67ec8a^"` archeology + main 在庫 6 file 0 sorry を
確認済のため発火確率 < 5%。

### L-BDD-3: `lz78EncodingLength` 抽象維持の外形互換性要求が後発で発生

**発火条件**: 本 plan の中間 headline `lz78_asymptotic_optimality_bdd_free` を
`lz78DistinctEncodingLength` 固定で publish した後、external caller が
「抽象 `lz78EncodingLength` 形の boundedness internal discharge も欲しい」と
要求した場合 (現時点では caller 不在、textbook-roadmap §13 にもそのような
caller の言及なし、本 plan 起草時点で発火確率 ≈ 0)。

**対処**:
- (a) 中間 headline 2 種 publish (抽象 + specialized)。抽象形は本 plan の対象
      ではないため別 plan として起こす
- (b) 本 plan 内では specialized 形のみで closure、L-BDD-3 を retract-candidate
      として記録だけ残す

**honesty 撤退の全般原則**:

- 行き詰まった場合は **`sorry + @residual(<class>:<slug>)`** で signature を
  保ったまま抜く (CLAUDE.md「検証の誠実性 → sorry を書けない箇所での対処順序」)
- **禁止**: `IsLZ78BoundednessHyp` / `IsLZ78DistinctEncodingBoundedness` のような
  `*Hypothesis` predicate に bound 核を bundling する撤退 (削除済 §4 headline で
  発生していた tier-5 defect)。本 plan は当該 defect を継承しないため、新規述語の
  導入を一切しない (中間 headline は raw `∀ᵐ ω ∂μ, ...` hypothesis 形のみ)
- **禁止**: load-bearing hypothesis を `IsXxxClaim` 述語に bundle / `Prop := True`
  placeholder / 仮説型≡結論の `:= h` 循環 / 退化定義悪用 (CLAUDE.md「検証の誠実性」)

## Approach vs M3/M4 の境界

本 plan は **M3/M4 scope-out を維持** (textbook-roadmap §13 line 14 / 48 / 97):

- `h_lower` (Cover-Thomas Eq. 13.130 converse、`entropyRate ≤ liminf (lz/n)` a.s.)
  は M3 (variable-depth tree AEP) / M4 (Barron a.s. lift) 経由でしか discharge
  できず、Mathlib 測度論基盤の新規研究貢献を要する。本 plan の中間 headline でも
  hypothesis のまま、external caller (research-level 完成時 or specific use case
  提供) から受ける
- `h_upper` (Ziv inequality、`limsup (lz/n) ≤ entropyRate` a.s.) も同じく M3/M4
  scope-out 対象、本 plan の中間 headline でも hypothesis のまま

本 plan の意義 = **boundedness が機械的に elementary discharge できる事実
(bit-layer counting envelope `c(n) =O n/log n` × per-phrase `bitLength = O(log n)`
= rate `=O 1`、削除済 file で genuine 実装済) を internal 化して、hypothesis
表面積を 4 → 2 に縮小**。M3/M4 scope-out 撤回は本 plan の scope 外。

**外形互換性の保証**:
- `lz78_asymptotic_optimality` (4 hyp form、`LempelZiv78.lean:382`) は変更なし、
  既存 caller の breaking change なし
- `lz78_asymptotic_optimality_bdd_free` (2 hyp form、distinct 固定) は **新規追加**、
  既存 file に追加 import が入る (`Common2026.lean` に 1 行) のみ
- 旧 `Is*ChainHyp` predicate (削除済 `LZ78FinalGlue.lean`) は復活させない、tier-5
  defect 継承を回避

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(Phase 0 で確定予定) file 配置**: 新規 `Common2026/Shannon/LZ78DistinctEncoding.lean`
   vs `LempelZiv78.lean` 拡張。起草時点での仮確定 = 新規 file 路線
   (Approach §「Mathlib-shape-driven 設計選択」選択 2 推奨理由参照)、Phase 0
   で import graph 循環不在を verbatim 確認後に確定。
2. **(Phase 0 で確定予定) specialization**: 中間 headline で `lz78EncodingLength`
   抽象維持 vs `lz78DistinctEncodingLength` 固定。起草時点での仮確定 = 固定路線
   (Approach §「Mathlib-shape-driven 設計選択」選択 1、抽象では boundedness の
   elementary discharge が不可能)。Phase 0 で削除済 file docstring (旧 `:30-37`)
   の再 archeology で再確認。
3. **(Phase 0 で確定予定) shared sorry 補題化判断**: Phase 1-F で Mathlib
   `Real.natLog_le_logb` 等の lookup 結果次第で、`natLog_succ_isBigO_log` /
   `bitCost_isBigO_log` を `wall:mathlib-real-log` の **shared sorry 補題**
   (`docs/audit/audit-tags.md`「共有 Mathlib 壁」) に集約するか、本 file 内 inline で
   genuine 実装するかを決定 (削除済 file は inline genuine 実装、現行 Mathlib で
   同様に inline 可能なら shared 化不要)。

## 主要設計判断 (起草時点 summary)

1. **scope expansion 回避** — 削除済 §1-§3 (~315 行) のみ cherry-pick、§4 の
   load-bearing predicate bundling 形 headline は復活させない。依存 infrastructure
   は main 在庫済 (2,259 行 0 sorry) のため連鎖復活は不要 (`LZ78GreedyParsing.lean`
   / `LZ78ZivCountingBody.lean` / `LZ78GreedyLongestPrefix.lean` /
   `LZ78PhraseCountAsymptoticBody.lean` 等)。
2. **M3/M4 scope-out 維持** — `h_lower` / `h_upper` は本 plan の中間 headline でも
   hypothesis のまま、textbook-roadmap §13 の M3/M4 scope-out 判定を撤回しない。
3. **`*Hypothesis` predicate 新規導入禁止** — 削除済 §4 で行われていた
   `IsLZ78AchievabilityChainHyp` / `IsLZ78ConverseChainHyp` bundling は tier-5
   load-bearing hypothesis defect (CLAUDE.md「検証の誠実性」)、本 plan の中間
   headline は raw `∀ᵐ ω ∂μ, ...` hypothesis 形のみで構成。
4. **proof done 直行** — 本 plan の中間 headline + 補助補題群は新規 `@residual`
   を導入しない設計 (L-BDD-1 発火時のみ stage、その場合は明示的に `wall:mathlib-real-log`
   slug)。Phase V で honesty audit pass 後 `@audit:ok` 取得を目標。

## 残 open questions (Phase 0 archeology 待ち)

- (Q1) 削除済 file の Mathlib `Real.natLog_le_logb` 使用箇所が現行 Mathlib API で
  通るか (Phase 0-3 で loogle 再確認)
- (Q2) `lz78PhraseStrings_count_isBigO` (`LZ78ZivCountingBody.lean:408`) の
  signature が削除済 file 当時 (`f67ec8a^`) と現行 main で verbatim 一致するか
  (Phase 0-2 で `git show` × 2 比較)
- (Q3) `Common2026.lean` の現行 import 順序に新規 `LZ78DistinctEncoding.lean` を
  どこに挿入するか (Phase V-2 で確定、`LempelZiv78.lean` 直後が自然)

## 削除済 file 群の archeology 結果 (起草時点 summary)

| 削除済 file (`f67ec8a^`) | 行数 | sorry 数 | 本 plan で必要? | 現状 |
|---|---|---|---|---|
| `LZ78DistinctEncoding.lean` | 433 | 1 (§4 headline のみ、load-bearing defect) | **§1-§3 のみ必要** (§4 復活せず) | 削除済、本 plan で §1-§3 cherry-pick |
| `LZ78ZivCombinatorics.lean` | 528 | — | 不要 (Ziv combinatorics は M3/M4 path、本 plan scope 外) | 削除済据置 |
| `LZ78ZivTreeNode.lean` | 570 | — | 不要 (同上) | 削除済据置 |
| `LZ78FinalGlue.lean` | 374 | — | 不要 (`Is*ChainHyp` predicate 供給元、tier-5 defect 含む) | 削除済据置 |
| `LZ78AchievabilityLimsup.lean` | 233 | — | 不要 (M3/M4 scope-out) | 削除済据置 |
| `LZ78AsEventualAchievability.lean` | 401 | — | 不要 (同上、textbook-roadmap で名前変動) | 削除済据置 |
| `LZ78ConverseDischarge.lean` | 328 | — | 不要 (M3/M4 scope-out) | 削除済据置 |
| `LZ78ConverseKraft.lean` | 190 | — | 不要 (同上) | 削除済据置 |
| `LZ78SMBSandwich.lean` | 500 | — | 不要 (`IsSMBSandwichPassthrough` body 経由は M3/M4 scope-out) | 削除済据置 |
| `LZ78TreeInducedAEP.lean` | 288 | — | 不要 (`Common2026/Shannon/` 直下から削除) | 削除済据置 |
| `LZ78ZivTreeBridge.lean` | 158 | — | 不要 (同上) | 削除済据置 |

| 現存 main file (依存先) | 行数 | sorry 数 | 本 plan で参照 |
|---|---|---|---|
| `Common2026/Shannon/LempelZiv78.lean` | 532 | 0 | 既存 `lz78_asymptotic_optimality` を Phase 3 で internal call、変更なし |
| `Common2026/Shannon/LZ78GreedyParsing.lean` | 544 | 0 | `LZ78Phrase.bitLength` / `LZ78Parsing.encodingLength` 経由参照 |
| `Common2026/Shannon/LZ78GreedyParsingImpl.lean` | 474 | 0 | 直接参照なし (delete file 当時の import) |
| `Common2026/Shannon/LZ78GreedyLongestPrefix.lean` | 271 | 0 | `lz78PhraseStrings_count_le` 経由参照 |
| `Common2026/Shannon/LZ78ZivCountingBody.lean` | 420 | 0 | `lz78PhraseStrings_count_isBigO` 経由参照 (Cover-Thomas Eq. 13.124、本 plan の Phase 1-G の鍵) |
| `Common2026/Shannon/LZ78PhraseCountAsymptoticBody.lean` | 243 | 0 | 間接参照 (`LZ78ZivCountingBody.lean` 経由) |
| `Common2026/Shannon/LZ78ZivInequality.lean` | 307 | 0 | 直接参照なし |

scope expansion なし、cherry-pick のみで closure 可能 (起草時点予測、Phase 0-2 で
再確認)。

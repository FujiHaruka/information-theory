# Shannon: Chernoff legacy-tag → sorry-based migration plan

> **Parent**: [`chernoff-moonshot-plan.md`](chernoff-moonshot-plan.md)
> + [`chernoff-converse-moonshot-plan.md`](chernoff-converse-moonshot-plan.md)
> + [`chernoff-converse-sanov-discharge-plan.md`](chernoff-converse-sanov-discharge-plan.md)
> + 関連 [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) /
>   [`audit/audit-tags.md`](../audit/audit-tags.md)。
>
> 本 plan は **proof completion ではなく legacy tag (`@audit:closed-by-successor`
> 主体 + 散文 🟢ʰ) → `sorry + @residual` への honesty 強化** (`audit-tags.md`
> 「Deprecated」表 + 「移行レシピ」) を目的とする独立 workstream。
>
> Pilot references:
> - [`hoeffding-sorry-migration-plan.md`](hoeffding-sorry-migration-plan.md)
>   (pure suspect pilot、Pattern B constructive recovery 起源)
> - [`cramer-sorry-migration-plan.md`](cramer-sorry-migration-plan.md)
>   (chain sweep with P/V/C 全 P)
> - [`relay-sorry-migration-plan.md`](relay-sorry-migration-plan.md)
>   (Round 2 直近、cross-family + closed-by-successor 部分扱い)
>
> **本 plan の追加目的 (Round 3 pilot)**: `@audit:closed-by-successor(<slug>)`
> migration の recipe を確立する。Chernoff は **19 closed-by-successor + 9 散文
> 🟢ʰ = 28 declaration**、suspect / staged 0 件 / wall slug 不在の bookkeeping
> 系典型。LZ78 / InfinitePiTiltedChangeOfMeasure 等 closed-by-successor 残存
> family の sweep 前に recipe を確立する。

## Context

### 計数 (verbatim 確認、2026-05-26)

`rg -n '@audit:closed-by-successor|@audit:suspect|@audit:staged|@audit:defer|@audit:retract-candidate|@audit:defect|🟢ʰ'`
+ 各タグ周辺 docstring / signature / body 1-3 行を Read で照合した実数値:

| file | closed-by-successor | 🟢ʰ (散文) | 既存 `@audit:defect` (tier 5 既存マーカー) | 既存 sorry (`rg -nwc`) | ⚠/HONESTY ALERT/FALSE |
|---|---:|---:|---:|---:|---:|
| `ChernoffSanovDischarge.lean` | **3** | 0 | 0 | 0 | 1 (`⚠️ Plan-level finding` docstring、honest 注記) |
| `ChernoffPerTiltDischarge.lean` | **5** | 3 | 1 (`IsBayesErrorPerTiltLowerBound` def `:147`、`false-statement` + retract-candidate) | 0 | 2 (`FALSE in general` docstring 注記) |
| `ChernoffPerTiltSanov.lean` | **6** | 1 | 2 (`IsChernoffNLetterRN` def `:147`、`false-statement` + retract-candidate; `chernoff_per_tilt_via_RN` `:180`、`launder` + retract-candidate `circular-between-false-predicates`) | 0 | 0 |
| `ChernoffConverse.lean` | **3** | 5 | 0 | 0 | 0 |
| `ChernoffInformation.lean` | **2** | 0 | 0 | 0 | 1 (`FALSE per-tilt predicate vs.` docstring 注記) |
| **合計** | **19** | **9** | **3** | **0** | **4** |

**計数の verbatim 確認結果は orchestrator brief「19 closed / 9 🟢ʰ」と一致**
(suspect / staged 0 件も brief 通り)。**追加発見** (brief 在庫表に未掲載):
- 既存 `@audit:defect` 3 件 (全て `ChernoffPerTilt*` 系 predicate def に著者明示
  済、retract-candidate と併用)。本 plan の sweep scope **には含めない** —
  既に最 honest 形態 (`@audit:defect(<kind>)` + `@audit:retract-candidate(<reason>)`)
  でマーク済の tier 5 既存マーカーであり、本 sweep は consumer 側 wrapper のみ扱う。
- ⚠ / FALSE 散文 4 hits は **全て honest 注記** (predicate が FALSE であることを
  著者が docstring 内で明示)、Pattern H 該当だが「既存 honest 表現を維持」が
  正しい扱い (新規 sweep 対象ではない)。

### scope 外 file

以下 3 file は legacy tag 0 件で本 plan の sweep scope 外。touch しない:
- `Chernoff.lean` (1066 行、0 legacy tag、`chernoffZSum` / `chernoffInfo` /
  `bayesErrorMinPmf` / `chernoff_lemma_achievability` の base implementation)
- `ChernoffBandMassDischarge.lean` (574 行、0 legacy tag、**successor file**
  本人 — `chernoff_lemma_tendsto_holds` / `chernoff_converse_holds` を
  regularity-only で genuine discharge 済)
- `ChernoffNLetterZSum.lean` (51 行、0 legacy tag、n-letter Z-sum scaffolding)

### なぜ Chernoff が Round 3 pilot か (closed-by-successor recipe 確立)

`docs/audit/sorry-migration-runbook.md`「並列実行候補 family (2026-05-25 集計)」
で Chernoff は **Round 3 (大規模 + dependency 注意)** の「bookkeeping 系、
`@audit:closed-by-successor` migration の pilot」と分類されている。Round 1/2
の sweep は suspect / staged / 🟢ʰ が主対象で、`closed-by-successor` migration
の recipe は Hoeffding pilot 終了時点 (2026-05-25) で「依存先の sorry は依存先で
`@residual` 管理 (sorry-based ではタグ不要、type-check 経由で transitive 追跡)」
と `audit-tags.md`「Deprecated」表に書かれているのみ。Round 3 で recipe を本 plan
内 **Phase Z** として明文化する。

Chernoff の特徴:
1. **19 closed-by-successor の slug は全件単一** (`chernoff-converse-sanov-discharge`)。
   successor file `ChernoffBandMassDischarge.lean` が `chernoff_lemma_tendsto_holds` /
   `chernoff_converse_holds` を **regularity-only で genuine discharge 済** (0 sorry)。
   後継版が既に存在する典型的 bookkeeping パターン。
2. **3 sub-pattern が共存**:
   - **CS-honest**: load-bearing hyp が **honest band-mass hypothesis**
     (`IsChernoffBandMassToOne`、type ≠ conclusion、`audit-tags.md` tier 4 ではなく
     tier 2 寄り)。`ChernoffSanovDischarge.lean` の 3 件。
   - **CS-false**: load-bearing hyp が **FALSE-in-general な predicate**
     (`IsBayesErrorPerTiltLowerBound` / `IsChernoffNLetterRN` /
     `IsChernoffPerTiltDischargeable`、著者が docstring で明示済)。
     `ChernoffPerTiltDischarge` 5 / `ChernoffPerTiltSanov` 6 / `ChernoffConverse` 3 件。
   - **CS-genuine-hyps**: load-bearing hyp が **per-tilt 経路と独立の hyp**
     (`h_converse` / `h_bdd_le`、regularity-only でなく hypothesis pass-through)。
     `ChernoffInformation.lean` の 2 件。
3. **shared wall lemma は不要**。`audit-tags.md`「Wall name register」表に
   Chernoff 系 wall は **未登録**。本 sweep では `plan:chernoff-converse-sanov-discharge`
   slug に揃え、新規 wall name を register しない (詳細: Approach §「共有 wall lemma 集約の要否」)。
4. **cross-family entanglement は 2 件**:
   - `ChernoffBandMassDischarge.lean:7` の `import CramerLC2Discharge` (sweep scope **外**、
     successor file 本人)
   - 本 sweep scope 内: `ChernoffPerTiltSanov.lean:5` + `ChernoffPerTiltDischarge.lean:4`
     の `import InformationTheory.InformationTheory.Asymptotic` (= utility import、family
     entanglement ではない)
   - **family 外 (Cramér) との結合は本 sweep scope 外 file (`ChernoffBandMassDischarge`)
     にのみ存在** → 本 plan の Phase 2.x ripple では考慮不要、未決事項 escalate 不要。

### 上位 moonshot との関係

`chernoff-converse-moonshot-plan.md` (T1-B follow-up) は **2026-05-26 時点で
T1-B closure 完了** (load-bearing per-tilt route の `closed-by-successor` 化 +
`ChernoffBandMassDischarge` の `ε`-relaxed route で genuine 完成)。本 plan は
**その closure 状態を変えない** — specifically:

- **load-bearing wrapper の sorry 化**: 19 closed-by-successor-tagged
  declaration の signature から load-bearing hypothesis を削除し body を `sorry`
  に置換。`@audit:closed-by-successor(chernoff-converse-sanov-discharge)` タグを
  `@residual(plan:chernoff-converse-sanov-discharge)` に書換。
- **predicate 定義側**: 3 つの load-bearing predicate (`IsBayesErrorPerTilt-
  LowerBound` / `IsChernoffNLetterRN` / `IsChernoffPerTiltDischargeable`) は
  既存 `@audit:defect(false-statement)` + `@audit:retract-candidate(false-
  replaced-by-eps-relaxed)` マーカー (tier 5 既存マーカー、最も honest 形態)
  **維持** — 本 plan で touch しない (本 sweep の任務は consumer wrapper のみ)。
- **honest band-mass hyp `IsChernoffBandMassToOne`** (`ChernoffSanovDischarge.lean:243`)
  は **regularity ではなく load-bearing だが honest** (type ≠ conclusion、
  successor の `isChernoffBandMassToOne_of_interior_optimal` で genuine discharge
  済)。Phase 2.1 の 3 declaration で hyp 削除 + sorry 化対象 (consumer side)、
  predicate def 自体は **touch しない** (successor が live consumer)。
- **successor file `ChernoffBandMassDischarge.lean`** (regularity-only 完成版)
  は **本 plan で touch しない** — 既に 0 sorry / 0 legacy tag で proof done 寄り。

**proof completion** (`chernoff_lemma_tendsto_holds` の Q-LLN + first-order
interior optimality discharge 等) は successor file 内で完成済、本 plan は
honesty 強化のみ。

### Honesty workflow と DoD

本 plan の DoD は `CLAUDE.md`「Definition of Done — 2 段階」の **type-check done**:
- 各 file `lake env lean InformationTheory/Shannon/Chernoff<X>.lean` が 0 errors、
- 各新規 `sorry` に `@residual(<class>:<slug>)` タグ、
- 各 Phase 完了時に `honesty-auditor` を起動して classification + signature
  honesty を独立検証 (CLAUDE.md「Independent honesty audit」)。

`@audit:ok` (proof done) は本 plan の出力にはならない — wrapper 側 file は本来
load-bearing で publish されており、proof done は successor file
`ChernoffBandMassDischarge` 経由で別 plan の評価範囲。

### Tier 5 defect — inline 検出 (planner 段階)

CLAUDE.md「検証の誠実性」"見つけた側" inline policy に従い、planner 段階で
verbatim 確認した tier 5 既存マーカー + 構造的観察:

| file:line | decl 名 | 構造的観察 | verbatim 根拠 |
|---|---|---|---|
| `ChernoffPerTiltDischarge.lean:148` | `IsBayesErrorPerTiltLowerBound` (def) | **既存 tier 5 マーカー: `@audit:defect(false-statement)` + `@audit:retract-candidate(false-replaced-by-eps-relaxed)`** | docstring `:137-147` で「Cramér Θ(1/√n) prefactor が constant C を排除、FALSE in general」を著者明示。本 sweep で **touch しない** — 既に最 honest 形 |
| `ChernoffPerTiltSanov.lean:148` | `IsChernoffNLetterRN` (def) | 同上 (`false-statement` + `false-replaced-by-eps-relaxed`) | docstring `:141-147`、同様の FALSE 明示 + `ChernoffSanovDischarge` の `ε`-relaxed pivot 経由を指示 |
| `ChernoffPerTiltSanov.lean:181-185` | `chernoff_per_tilt_via_RN` (lemma) | **既存 tier 5 マーカー: `@audit:defect(launder)` + `@audit:retract-candidate(circular-between-false-predicates)`**。body `:= h_RN` (`IsChernoffNLetterRN → IsBayesErrorPerTiltLowerBound`、両者の body が同一なので literal alias) | docstring `:172-180`、「name laundering between two false predicates」を著者明示。本 sweep で **touch しない** — 既に最 honest 形 |
| `ChernoffPerTiltSanov.lean:192-196` | `isChernoffNLetterRN_of_isBayesErrorPerTiltLowerBound` (lemma) | body `:= h_pred`、上の逆方向。closed-by-successor タグ付きだが、構造的に上の `chernoff_per_tilt_via_RN` と同じ名前変え defect | docstring `:187-191`、`@audit:closed-by-successor(chernoff-converse-sanov-discharge)` のみ。**本 plan の Phase 2.3 で sorry 化対象**、ただし body `:= h_pred` の defect 性も同時に annotate (新規 `@audit:defect(launder)` 付与候補) |

これらの 3 件 (predicate def 2 + launder lemma 1) は **本 plan で touch しない**
(既に最 honest 形)。4 件目 `isChernoffNLetterRN_of_isBayesErrorPerTiltLowerBound`
は本 plan の Phase 2.3 で sorry 化対象 — signature 改変 (hyp 削除) + body sorry
で literal alias 性は解消される (新規 `@audit:defect` 付与は不要)。

### load-bearing hypothesis chain 構造 (planner 段階の依存図)

```
ChernoffInformation.lean   (closed-by-successor 2)
  ├── chernoff_lemma_tendsto             (h_converse + h_bdd_le pass-through、CS-genuine-hyps)
  └── chernoff_dotEq_tendsto             (同上、DotEq 変種)
       (successor: ChernoffBandMassDischarge.chernoff_lemma_tendsto_holds, regularity-only, 0 sorry)

ChernoffConverse.lean   (closed-by-successor 3 + 🟢ʰ 5)
  ├── chernoff_converse_from_per_tilt    (h_lb pass-through、CS-false 経由 wrapper)
  ├── chernoff_converse_of_per_tilt_existential   (h_per_tilt existence-bundle、CS-false、🟢ʰ load-bearing)
  └── chernoff_lemma_tendsto_from_per_tilt        (h_per_tilt sandwich、CS-false、🟢ʰ load-bearing)
       (successor: 同上、ε-relaxed route 経由)

ChernoffPerTiltDischarge.lean   (closed-by-successor 5 + 🟢ʰ 3)
  ├── chernoff_converse_from_predicate              (CS-false、h_pred : IsBayesErrorPerTiltLowerBound)
  ├── chernoff_converse_discharged_from_predicate   (CS-false、h_predicate existence-bundle)
  ├── chernoff_lemma_tendsto_from_predicate         (CS-false、同上 sandwich)
  ├── chernoff_lemma_tendsto_of_per_tilt            (CS-false、🟢ʰ、IsChernoffPerTiltDischargeable bundle)
  └── chernoff_dotEq_tendsto_of_per_tilt            (CS-false、🟢ʰ、DotEq 変種)
       (successor: 同上)

ChernoffPerTiltSanov.lean   (closed-by-successor 6 + 🟢ʰ 1)
  ├── isChernoffNLetterRN_of_isBayesErrorPerTiltLowerBound  (CS-false-laundered、body := h_pred、tier 5 触れる箇所)
  ├── chernoff_lemma_tendsto_via_RN                          (CS-false、h_predicate via RN predicate)
  ├── isChernoffPerTiltDischargeable_of_RN                   (CS-false、RN → pre-existing)
  ├── chernoff_converse_via_RN_forall                        (CS-false、∀ λ form)
  ├── chernoff_lemma_tendsto_via_RN_forall                   (CS-false、Tendsto ∀ λ form)
  └── chernoff_dotEq_tendsto_via_RN                          (CS-false、DotEq via RN)
       (successor: 同上)

ChernoffSanovDischarge.lean   (closed-by-successor 3)
  ├── bayesErrorMinPmf_ge_exp_neg_mul_Z_pow   (CS-honest、h_band : IsChernoffBandMassToOne pass-through)
  ├── chernoff_converse_from_eps_relaxed       (CS-honest、h_eps : ε-relaxed bound family)
  └── chernoff_converse_of_bandMass            (CS-honest、h_band existence-bundle、honest band-mass)
       (successor: ChernoffBandMassDischarge.chernoff_converse_holds, regularity-only, 0 sorry)
```

**注意**: 上記の `(successor: ...)` 注記は **全 file で同じ successor file
`ChernoffBandMassDischarge.lean`** を指す。19 closed-by-successor の slug は
全て `chernoff-converse-sanov-discharge` で単一。

## Approach

**file 単位 sweep を 3 sub-pattern に分岐**、共有 wall lemma は集約しない、
cross-family ripple は不要 (本 sweep scope 内に family 外 import 0 件)。
Hoeffding pilot (P/V/C パターン) + Relay pilot (上流→下流 chain 順序) の延長で、
Chernoff 固有の **CS-honest / CS-false / CS-genuine-hyps の 3 sub-pattern 区別**
を加味する。

### 戦略 (上流 → 下流 chain 順序)

```
Phase 0    inventory (本 plan 内 inline 表、Phase 別 patch 順序)
   │
Phase 1    V/C cleanup
   │      ├─ V (variational pass-through)     ← 該当 0 件 (実質 skip)
   │      └─ C (in-tree constructive primitive 経由)  ← 該当 0 件 (実質 skip)
   │      Phase 1 はゼロ件、Cramér / Relay pilot と同じく **空処理で記録のみ**
   │
Phase Z    closed-by-successor migration recipe (本 plan の追加目的)
   │      → 3 sub-pattern (CS-honest / CS-false / CS-genuine-hyps) の決定木 +
   │        各 sub-pattern 単位の書換 recipe を inline で確立
   │
Phase 2.1  CS-honest retreat — ChernoffSanovDischarge.lean (3 件、honest band-mass hyp)
   │
Phase 2.2  CS-genuine-hyps retreat — ChernoffInformation.lean (2 件、h_converse + h_bdd_le pass-through)
   │
Phase 2.3  CS-false retreat — ChernoffConverse.lean (3 件、🟢ʰ 5 件併存)
   │
Phase 2.4  CS-false retreat — ChernoffPerTiltDischarge.lean (5 件、🟢ʰ 3 件併存)
   │
Phase 2.5  CS-false-laundered retreat — ChernoffPerTiltSanov.lean (6 件、🟢ʰ 1 件併存)
   │
Phase 2.x  ripple — caller drift 散文化 (Pattern C: 即興 vocabulary 禁止)
   │
Phase 2.6  predicate retract-candidate 付与 (3 既存 tier 5 マーカー維持、新規付与は 0 件)
   │      → 既存 `@audit:defect(false-statement)` + `@audit:retract-candidate`
   │        は維持、新規付与なし (predicate 側は既に最 honest 形)
   │
Phase 2.7  audit-2 (honesty-auditor 起動、全 19 件 + 9 散文 🟢ʰ refine 確認)
   │
Phase V    verify (全 5 file lake env lean 0 errors + 集計 + 親 plan banner 更新 +
            handoff 反映 + Phase Z recipe を runbook に reflect 提案)
```

**Phase 順 (上流 → 下流) を選んだ理由**:

Relay pilot で実証済の「上流 sorry を先に確定させると olean refresh + 下流
transitive sorry の散文化が一括で扱える」パターン。Chernoff の依存図は **上流
ほど load-bearing が honest** (CS-honest の `ChernoffSanovDischarge` が最上流、
CS-false の `ChernoffPerTiltSanov` が最下流) なので、CS-honest → CS-genuine-hyps →
CS-false → CS-false-laundered の順に処理することで、各 sub-pattern の recipe を
段階的に確立できる。

**特例**: 依存図上 `ChernoffSanovDischarge` は `ChernoffPerTiltSanov` / `ChernoffPerTiltDischarge` /
`ChernoffConverse` を import しており **dependent**。しかし sweep 順序を CS-pattern
別に分けるため、Phase 2.1 で先に CS-honest を処理する。olean refresh 順序は
Phase 2.5 完了後に Phase V で **逆 import 順** (最も dependent から build) で
verify する (詳細 Phase V.1)。

### closed-by-successor migration recipe (Phase Z 詳細、本 plan の追加目的)

`@audit:closed-by-successor(<plan-slug>)` は `audit-tags.md`「Deprecated」表で
**tier 4 legacy** に分類済 (Hoeffding pilot 終了時、2026-05-25)。移行先は:

> wrapper 自身に sorry があれば `@residual(plan:<SLUG>)` に置換、依存先の
> sorry は依存先で `@residual` 管理 (sorry-based ではタグ不要、type-check 経由で
> transitive 追跡)

本 Chernoff sweep は上記原則を **3 sub-pattern に分岐させる decision tree** を
確立する:

#### Decision tree (各 closed-by-successor-tagged declaration に対して)

```
[Step 1] declaration の load-bearing hypothesis を verbatim 確認
  │
  ├── (a) hyp が **honest** (type ≠ conclusion、successor で genuine discharge 済)
  │    → **CS-honest pattern**
  │    → Recipe A (hyp 削除 + body sorry + @residual(plan:<slug>))
  │
  ├── (b) hyp が **FALSE-in-general predicate** (predicate def に既存
  │        @audit:defect(false-statement) 付き、または著者が docstring で
  │        明示済)
  │    → **CS-false pattern**
  │    → Recipe B (hyp 削除 + body sorry + @residual(plan:<slug>)、predicate
  │      def 側は既存 tier 5 マーカー維持)
  │
  └── (c) hyp が **per-tilt 経路と独立の regularity-寄り hyp**
        (`h_converse` / `h_bdd_le` 等で、successor で別経路 discharge 済)
        → **CS-genuine-hyps pattern**
        → Recipe C (hyp 削除 + body sorry + @residual(plan:<slug>)、successor
          headline への forward redefinition も検討可)

[Step 2] body の構造を verbatim 確認
  │
  ├── body 純構成的 (1-3 行 modus ponens / forward / arithmetic、Hoeffding pilot
  │    Pattern B 該当)
  │    → 各 Recipe の sorry 化を pre-empt して **constructive recovery** に格上げ
  │      可能か検証 (auditor 委任)
  │
  └── body が hyp 経由の本質的 derivation (Phase 結合 / 複数 hyp の chain)
        → 各 Recipe そのまま適用

[Step 3] declaration が wrapper signature compatibility を提供しているか
  │
  ├── Yes (downstream call site が現役、変動 hyp を underscore 化で残す必要あり)
  │    → signature の load-bearing hyp のみ削除、他 hyp は underscore 化で残す
  │      (Relay pilot Pattern E 同形)
  │
  └── No (本 declaration は別 declaration から forward されるだけ)
        → signature 縮小、不要 hyp は完全削除
```

#### Recipe A — CS-honest (honest band-mass hyp 経由)

具体例: `ChernoffSanovDischarge.bayesErrorMinPmf_ge_exp_neg_mul_Z_pow` (`:295`)

```lean
-- 旧
/-- ... -/
@[ ... ]
lemma bayesErrorMinPmf_ge_exp_neg_mul_Z_pow
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1)
    (h_band : IsChernoffBandMassToOne P₁ P₂ lam)        -- ← load-bearing honest hyp
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-((n : ℝ) * ε)) * (chernoffZSum P₁ P₂ lam) ^ n
        ≤ 4 * bayesErrorMinPmf P₁ P₂ n := by
  -- 旧 body (filter_upwards 経由の constructive proof)
  sorry  -- @audit:closed-by-successor(chernoff-converse-sanov-discharge)

-- 新
/-- ...
@residual(plan:chernoff-converse-sanov-discharge) -/
lemma bayesErrorMinPmf_ge_exp_neg_mul_Z_pow
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1)
    -- h_band : IsChernoffBandMassToOne P₁ P₂ lam を削除
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-((n : ℝ) * ε)) * (chernoffZSum P₁ P₂ lam) ^ n
        ≤ 4 * bayesErrorMinPmf P₁ P₂ n := by
  sorry
```

**重要な備考**: 上の例は **既に旧 body は genuine な proof** (verbatim 確認、
`:303-359` で `filter_upwards [h_band ε hε]` 経由の constructive derivation)。
sorry 化で genuine proof を消すのは **大きな後退** に見えるが:
- 本 plan の DoD は type-check done であり、honesty 強化が目的。
- 旧 body が genuine だった理由は `h_band` の load-bearing 性に依存していたため
  (h_band を取れば constructive)。本 sweep の目的は load-bearing hyp を signature
  から外すこと → body は **本来の (`h_band` 不在の) unconditional 命題に対して**
  sorry を残す。
- 既存の genuine proof は successor file (`ChernoffBandMassDischarge.lean`) で
  `isChernoffBandMassToOne_of_interior_optimal` + `bayesErrorMinPmf_ge_exp_neg_mul_Z_pow`
  を呼び出す形で **保全されている** (verbatim 確認、`:548`)。

**Recipe A の判定基準**: hyp の predicate に `@audit:defect` がない、かつ
docstring で「honest load-bearing」「type ≠ conclusion」が明示されている。

#### Recipe B — CS-false (FALSE predicate 経由)

具体例: `ChernoffPerTiltDischarge.chernoff_converse_from_predicate` (`:175`)

```lean
-- 旧
/-- ... `@audit:closed-by-successor(chernoff-converse-sanov-discharge)` -/
theorem chernoff_converse_from_predicate
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ)
    (h_pred : IsBayesErrorPerTiltLowerBound P₁ P₂ lam) :       -- ← FALSE predicate
    Filter.limsup ... ≤ -Real.log (chernoffZSum P₁ P₂ lam) := by
  obtain ⟨C, hC_pos, h_lb⟩ := h_pred
  exact chernoff_converse_from_per_tilt P₁ P₂ hP₁_pos hP₂_pos lam C hC_pos h_lb

-- 新
/-- ...
@residual(plan:chernoff-converse-sanov-discharge) -/
theorem chernoff_converse_from_predicate
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    -- h_pred : IsBayesErrorPerTiltLowerBound P₁ P₂ lam を削除
    Filter.limsup ... ≤ -Real.log (chernoffZSum P₁ P₂ lam) := by
  sorry
```

**Recipe B の判定基準**: hyp の predicate に既存 `@audit:defect(false-statement)`
が付いている、または docstring で「FALSE in general」を著者明示している。
predicate def 側は本 sweep で **touch しない** — 既に最 honest 形 (tier 5
acknowledged) — wrapper だけが consumer として load-bearing 経由していた。

**重要な備考**: 旧 body の `obtain ⟨C, hC_pos, h_lb⟩ := h_pred` は **FALSE
predicate を unfold するだけ**。本 plan の sorry 化で「FALSE predicate を経由
した modus ponens」が消えるため、honesty audit の意味で **明確な前進**
(`audit-tags.md`「Honesty 階層」表で tier 4 → tier 2)。

#### Recipe C — CS-genuine-hyps (hypothesis pass-through)

具体例: `ChernoffInformation.chernoff_lemma_tendsto` (`:135`)

```lean
-- 旧
/-- ... `@audit:closed-by-successor(chernoff-converse-sanov-discharge)` -/
theorem chernoff_lemma_tendsto
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_converse : Filter.limsup ... ≤ chernoffInfo P₁ P₂)     -- ← L-Ch1 hyp (successor で別経路で討議)
    (h_bdd_le : Filter.IsBoundedUnder (· ≤ ·) atTop ...) :    -- ← L-Ch2 hyp
    Tendsto ... atTop (𝓝 (chernoffInfo P₁ P₂)) :=
  tendsto_of_le_liminf_of_limsup_le
    (chernoff_lemma_achievability P₁ P₂ hP₁_pos hP₂_pos)
    h_converse h_bdd_le
    (chernoff_rate_isBoundedUnder_ge P₁ P₂ hP₁_pos hP₂_pos)

-- 新
/-- ...
@residual(plan:chernoff-converse-sanov-discharge) -/
theorem chernoff_lemma_tendsto
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    -- h_converse + h_bdd_le を削除
    Tendsto ... atTop (𝓝 (chernoffInfo P₁ P₂)) := by
  sorry
```

**Recipe C の判定基準**: hyp が `h_converse` / `h_bdd_le` 等の **claim そのもの**
(load-bearing)、successor headline で別経路 (regularity-only) で discharge 済。
hyp の type は **claim** であって predicate / def ではないため、Recipe B のような
「predicate def を touch しない」考慮は不要。

**alternative — successor forward redefinition** (Recipe C の variant):
declaration 自体を sorry 化せず、successor の `chernoff_lemma_tendsto_holds`
(regularity-only) を forward する形に書き換える選択肢もある:

```lean
-- alternative (sorry 化せず successor へ forward)
theorem chernoff_lemma_tendsto
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)       -- ← 追加 hyp (regularity)
    (hne : P₁ ≠ P₂) :                                          -- ← 追加 hyp (regularity)
    Tendsto ... atTop (𝓝 (chernoffInfo P₁ P₂)) :=
  InformationTheory.Shannon.ChernoffBandMassDischarge.chernoff_lemma_tendsto_holds
    P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum hne
```

ただしこの alternative は **本 declaration の signature を変える** (新規
`hP₁_sum` / `hP₂_sum` / `hne` を要求) ため、downstream API 互換性が壊れる。
本 plan のデフォルトは **sorry 化を採用**、alternative は未決事項 #2 で
escalate (Phase 2.7 auditor 委任 / user 確認)。

#### Phase Z 完了時の handoff: recipe を runbook に反映提案

Phase V で本 plan の Phase Z recipe (3 sub-pattern decision tree + Recipe A/B/C)
を `docs/audit/sorry-migration-runbook.md`「失敗パターン」section に **新 Pattern J
(closed-by-successor migration)** として inline 提案する。runbook 拡張は本 plan
内で別 patch にせず、handoff `.claude/handoff-sorry-migration.md` に「次の sweep
session で runbook に Pattern J を追加」として委ねる。

### 共有 wall lemma 集約の要否

**集約しない**。`docs/audit/audit-tags.md`「Wall name register」表に Chernoff 系
wall は **未登録**。本 sweep では `plan:chernoff-converse-sanov-discharge` 単一
slug に揃え、新規 wall name を register しない。

検証: register 登録済の 10 wall (`stam` / `csiszar` / `n-dim-gaussian-aep` /
`sphere-volume` / `continuous-aep` / `nyquist-2w-dof` / `multivariate-mi` /
`joint-typicality-multi` / `epi-n-dim` / `fourier`) のうち、Chernoff 文脈に
直接該当する候補は **無い**。closure 担当の `chernoff-converse-sanov-discharge`
plan は既に existing で、Mathlib gap (`isChernoffBandMassToOne_of_interior_optimal`
の Q-LLN + first-order interior optimality 系) は family 固有。

### Pattern G (cross-family unified predicate) 判定

本 sweep scope (5 file) 内の cross-family import:

| file:line | import 文 | Stage (runbook S1/S2/S3) | 影響 |
|---|---|---|---|
| `ChernoffConverse.lean:1` | `import InformationTheory.Shannon.Chernoff` | family 内 (S0) | scope 内 |
| `ChernoffConverse.lean:2` | `import InformationTheory.Shannon.ChernoffInformation` | family 内 (S0) | scope 内 |
| `ChernoffPerTiltDischarge.lean:1-4` | family 内 + `import InformationTheory.InformationTheory.Asymptotic` | family 内 + S1 (utility) | scope 内 (DotEq) |
| `ChernoffPerTiltSanov.lean:1-5` | family 内 + `InformationTheory.InformationTheory.Asymptotic` | 同上 | scope 内 |
| `ChernoffSanovDischarge.lean:1-5` | family 内 + Mathlib のみ | scope 内 | scope 内 |
| `ChernoffInformation.lean:1-2` | family 内 + `InformationTheory.InformationTheory.Asymptotic` | 同上 | scope 内 |
| (scope 外参考) `ChernoffBandMassDischarge.lean:7` | `import InformationTheory.Shannon.CramerLC2Discharge` | **S2 (cross-family Cramér)** | **本 sweep scope 外** — successor file で sweep 対象外 |

**結論**: 本 sweep scope (5 file) 内に **family 外 import 0 件** (utility import
`InformationTheory.Asymptotic` を除く)。Pattern G escalate は **不要**。
scope 外 (`ChernoffBandMassDischarge`) には Cramér family との S2 dependency が
あるが本 plan で touch しない。

### constructive recovery 候補 (Pilot Pattern B)

planner 段階で各 declaration の **結論型 + body 構造を verbatim 確認**し、
constructive 化可能な候補を flag:

| file:line | decl 名 | 結論型 | body 構造 | 構成的回復可能性 |
|---|---|---|---|---|
| `ChernoffSanovDischarge.lean:295` | `bayesErrorMinPmf_ge_exp_neg_mul_Z_pow` | `∀ᶠ n, exp(-nε) · Z^n ≤ 4 · bayesError` | `filter_upwards [h_band ε hε]` + 56 行 constructive derivation | **No** — `h_band : IsChernoffBandMassToOne` が **本質的に load-bearing** (band mass → 1 の existence)、`h_band` 削除で constructive route 不可 |
| `ChernoffSanovDischarge.lean:369` | `chernoff_converse_from_eps_relaxed` | `limsup rate ≤ -log Z(λ)` | `filter_upwards` + 60 行 constructive (rate 不等式 chain) | **No** — `h_eps : ε-relaxed bound family` が本質的に load-bearing |
| `ChernoffSanovDischarge.lean:469` | `chernoff_converse_of_bandMass` | `limsup rate ≤ chernoffInfo` | `obtain` + `chernoff_converse_from_eps_relaxed` への forward | **No** (transitive、本来は constructive だが上流 sorry 化で transitive sorry) |
| `ChernoffInformation.lean:135` | `chernoff_lemma_tendsto` | `Tendsto rate atTop (𝓝 chernoffInfo)` | `tendsto_of_le_liminf_of_limsup_le` 4 hyp forward | **No** — `h_converse` + `h_bdd_le` が claim そのもの (Recipe C alternative での successor forward は可、ただし signature 変更を伴う) |
| `ChernoffInformation.lean:214` | `chernoff_dotEq_tendsto` | `bayesError ≐ exp(-n · chernoffInfo)` | `chernoff_lemma_tendsto` forward + `dotEq_iff_tendsto_log_div` | 同上 |
| `ChernoffConverse.lean:274` | `chernoff_converse_from_per_tilt` | `limsup rate ≤ -log Z(λ)` | 90 行 constructive (rate chain analysis) | **No** — `h_lb : C · Z^n ≤ 2 · bayesError` が **本質的に FALSE predicate のコア** (Recipe B 直接) |
| `ChernoffConverse.lean:411` | `chernoff_converse_of_per_tilt_existential` | 同上 | 5 行 `obtain` + forward | **No** (Recipe B、🟢ʰ load-bearing) |
| `ChernoffConverse.lean:447` | `chernoff_lemma_tendsto_from_per_tilt` | `Tendsto` | 1 行 forward to `chernoff_lemma_tendsto` | transitive、Phase 2.2 後に transitive sorry |
| `ChernoffPerTiltDischarge.lean:175/195/225` | 3 wrappers | (limsup / Tendsto 系) | 1-2 行 forward | transitive |
| `ChernoffPerTiltDischarge.lean:301/338` | `chernoff_lemma_tendsto_of_per_tilt` / `chernoff_dotEq_tendsto_of_per_tilt` | (Tendsto / DotEq) | 1-3 行 forward to `chernoff_lemma_tendsto_from_predicate` 等 | transitive |
| `ChernoffPerTiltSanov.lean:192/277/295/309/326/373` | 6 wrappers | (各種 limsup / Tendsto / DotEq) | 1-3 行 forward | **5 件 transitive** + 1 件 (`isChernoffNLetterRN_of_isBayesErrorPerTiltLowerBound:192`) が `:= h_pred` literal (Phase 0 tier 5 inline 検出済) |

→ **constructive recovery 候補は 0 件**。Hoeffding pilot の 1 件
(`isHoeffdingMinimizerFullSupport_of_lagrange`) / Relay pilot の 4 候補
(`relayDFRateWitness_*`) のような「結論型が `∀ a, 0 < · a` / `RateWitness ∃ N, ∀ n ≥ N, ...` の
regularity 形」が Chernoff には存在しない。全 19 declaration が closed-by-successor
で、結論型は全て **load-bearing claim** (limsup / Tendsto / DotEq の rate
inequality)。

### transitive sorry の handling 方針 (Pilot Pattern C)

Phase 2 で上流 (`ChernoffSanovDischarge` / `ChernoffInformation`) を sorry 化すると、
下流 (`ChernoffConverse` / `ChernoffPerTiltDischarge` / `ChernoffPerTiltSanov`)
が transitive sorry を引き継ぐ。**即興 vocabulary 禁止** (Pattern C)。

具体的な caller chain (verbatim 確認、import 図 + body Read):

```
ChernoffSanovDischarge.bayesErrorMinPmf_ge_exp_neg_mul_Z_pow  (Phase 2.1 で sorry 化)
  ←─ ChernoffSanovDischarge.chernoff_converse_from_eps_relaxed   (Phase 2.1 で sorry 化)
  ←─ ChernoffSanovDischarge.chernoff_converse_of_bandMass        (Phase 2.1 で sorry 化)

ChernoffInformation.chernoff_lemma_tendsto  (Phase 2.2 で sorry 化)
  ←─ ChernoffConverse.chernoff_lemma_tendsto_from_per_tilt       (Phase 2.3、transitive、ただし自身も Phase 2.3 で sorry 化)
  ←─ ChernoffPerTiltDischarge.chernoff_lemma_tendsto_of_per_tilt (Phase 2.4、transitive、🟢ʰ)
  ←─ ChernoffPerTiltSanov.chernoff_lemma_tendsto_via_RN          (Phase 2.5、transitive、🟢ʰ)

ChernoffInformation.chernoff_dotEq_tendsto  (Phase 2.2 で sorry 化)
  ←─ ChernoffPerTiltDischarge.chernoff_dotEq_tendsto_of_per_tilt (Phase 2.4、transitive、🟢ʰ)
  ←─ ChernoffPerTiltSanov.chernoff_dotEq_tendsto_via_RN          (Phase 2.5、transitive)

ChernoffConverse.chernoff_converse_from_per_tilt  (Phase 2.3 で sorry 化)
  ←─ ChernoffPerTiltDischarge.chernoff_converse_from_predicate   (Phase 2.4、transitive、ただし自身も sorry 化)
  ←─ ChernoffPerTiltDischarge.chernoff_converse_discharged_from_predicate (Phase 2.4、transitive、ただし自身も sorry 化)
  ←─ ChernoffPerTiltSanov.chernoff_converse_via_RN_forall        (Phase 2.5、transitive、ただし自身も sorry 化)
```

**注意**: 本 sweep では **全 19 declaration が直接 sorry 化対象** (constructive
recovery 候補 0 件、Recipe A/B/C のいずれかで signature 改変 + body sorry)。
そのため transitive sorry は **発生しない** — 各 declaration は自身の `@residual`
タグを持つ。Hoeffding / Relay pilot のような「上流 sorry → 下流 wrapper が
transitive sorry を継承 + docstring 散文」は本 sweep では発生しない。

Pattern C 散文化が必要な唯一のケース: **scope 外 file (`ChernoffBandMassDischarge`)
が本 sweep scope 内の sorry-化 declaration を呼び出している場合**。`rg` 確認:

```bash
rg -l 'chernoff_lemma_tendsto|chernoff_dotEq_tendsto|chernoff_converse_of_per_tilt_existential|bayesErrorMinPmf_ge_exp_neg_mul_Z_pow|chernoff_converse_from_eps_relaxed|chernoff_converse_of_bandMass|chernoff_converse_from_predicate|chernoff_converse_discharged_from_predicate|chernoff_lemma_tendsto_from_predicate|chernoff_lemma_tendsto_of_per_tilt|chernoff_dotEq_tendsto_of_per_tilt|isChernoffNLetterRN_of_isBayesErrorPerTiltLowerBound|chernoff_lemma_tendsto_via_RN|isChernoffPerTiltDischargeable_of_RN|chernoff_converse_via_RN_forall|chernoff_lemma_tendsto_via_RN_forall|chernoff_dotEq_tendsto_via_RN|chernoff_converse_from_per_tilt|chernoff_lemma_tendsto_from_per_tilt' InformationTheory/Shannon/Chernoff*.lean | sort -u
```

期待値: family 内 5 file (sweep scope 内) + `ChernoffBandMassDischarge.lean`
(scope 外、本 sweep の transitive caller 候補)。
**Phase 2.x ripple step で `ChernoffBandMassDischarge.lean` 内の transitive
caller を確認 + Pattern C 散文化**を実施 (touch しない代わりに docstring に
transitive 性散文を追加するか判定、auditor 委任)。

### ⚠ HONESTY ALERT / FALSE 検出 (Pattern H、R8)

`rg '⚠|HONESTY ALERT|FALSE' InformationTheory/Shannon/Chernoff{SanovDischarge,PerTilt-
Discharge,PerTiltSanov,Converse,Information}.lean` 結果:

- `ChernoffSanovDischarge.lean:18`: `## ⚠️ Plan-level finding (honesty alert)`
  → predicate `IsBayesErrorPerTiltLowerBound` が FALSE in general を明示する module
  docstring (著者 honest 注記)。**Pattern H 該当だが既存 honest 表現** — 本 plan
  Phase V で文言維持を確認。
- `ChernoffPerTiltDischarge.lean:291`: `IsChernoffPerTiltDischargeable` is **FALSE in general**
  → docstring 内散文 (`chernoff_lemma_tendsto_of_per_tilt` の 🟢ʰ block 内)、
  既存 honest 表現。
- `ChernoffPerTiltDischarge.lean:330`: `IsBayesErrorPerTiltLowerBound` is **FALSE in general**
  → 同上 (`chernoff_dotEq_tendsto_of_per_tilt` の 🟢ʰ block 内)。
- `ChernoffInformation.lean:129/210`: `FALSE per-tilt predicate vs.`、`FALSE in general — Cramér`
  → docstring 内散文 (`chernoff_lemma_tendsto` / `chernoff_dotEq_tendsto` の
  successor discharge 注記)、既存 honest 表現。

**全 4 hits = 既存 honest 表現** (predicate FALSE を著者明示)、本 plan の sweep
scope **には影響しない** — predicate def 側は既存 tier 5 マーカー (Recipe B 参照)
で touch しない、consumer wrapper 側の docstring 散文は Phase 2.3-2.5 で sorry 化
する際に **honest 表現として維持** (新 `@residual` タグと併存)。

## 在庫: 19 件 (closed-by-successor) + 散文 🟢ʰ 9 件 の verbatim 分類

verbatim 確認方法: 各 `@audit:closed-by-successor` / `🟢ʰ` 周辺 docstring + theorem
signature + body 1-3 行を実コードから読込、Recipe A/B/C を判定。各 declaration
の `path:line` は **タグ行**、declaration 名はその直後。

### `ChernoffSanovDischarge.lean` — 3 closed-by-successor (CS-honest)

| file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|
| `ChernoffSanovDischarge.lean:295` | `bayesErrorMinPmf_ge_exp_neg_mul_Z_pow` | `h_band : IsChernoffBandMassToOne` (honest, type ≠ conclusion) | `∀ᶠ n, exp(-nε)·Z^n ≤ 4·bayesError` | CS-honest | A | `@residual(plan:chernoff-converse-sanov-discharge)` | No (h_band load-bearing) | S0 (family 内) | h_band 削除 + body sorry。既存 56-line genuine proof は successor `ChernoffBandMassDischarge:548` で保全 |
| `ChernoffSanovDischarge.lean:369` | `chernoff_converse_from_eps_relaxed` | `h_eps : ∀ ε > 0, ∀ᶠ n, …` (ε-relaxed bound family) | `limsup rate ≤ -log Z(λ)` | CS-honest | A | 同上 | No | S0 | h_eps 削除 + body sorry |
| `ChernoffSanovDischarge.lean:469` | `chernoff_converse_of_bandMass` | `h_band : ∃ lam ∈ Icc 0 1, … ∧ IsChernoffBandMassToOne` (existence-bundle) | `limsup rate ≤ chernoffInfo` | CS-honest | A | 同上 | No | S0 | existence-bundle 削除 + body sorry |

**predicate `IsChernoffBandMassToOne` (`:243`) は touch しない** — successor
file (`ChernoffBandMassDischarge.lean:395-400`) で `isChernoffBandMassToOne_of_interior_optimal`
が **live consumer** として依存しており、predicate 削除は successor を壊す。
本 plan の Phase 2.6 で **`@audit:retract-candidate` 付与もしない** (live
consumer がある predicate に retract-candidate を付与すると意味矛盾)。

### `ChernoffInformation.lean` — 2 closed-by-successor (CS-genuine-hyps)

| file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|
| `ChernoffInformation.lean:135` | `chernoff_lemma_tendsto` | `h_converse` (claim そのもの) + `h_bdd_le` (boundedness claim) | `Tendsto rate atTop (𝓝 chernoffInfo)` | CS-genuine-hyps | C | `@residual(plan:chernoff-converse-sanov-discharge)` | No (claim そのもの) | S0 | 2 hyp 削除 + body sorry。alternative (successor forward) は未決事項 #2 で escalate |
| `ChernoffInformation.lean:214` | `chernoff_dotEq_tendsto` | 同上 (`h_converse` + `h_bdd_le`) | `bayesError ≐ exp(-n·chernoffInfo)` | CS-genuine-hyps | C | 同上 | No | S0 | 同上 |

### `ChernoffConverse.lean` — 3 closed-by-successor + 散文 🟢ʰ 5

| file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|
| `ChernoffConverse.lean:274` | `chernoff_converse_from_per_tilt` | `C` (positive constant) + `hC_pos` (positivity) + `h_lb : ∀ᶠ n, C·Z^n ≤ 2·bayesError` (FALSE predicate のコア) | `limsup rate ≤ -log Z(λ)` | CS-false | B | `@residual(plan:chernoff-converse-sanov-discharge)` | No (FALSE predicate コア) | S0 | h_lb は predicate `IsBayesErrorPerTiltLowerBound` の destructure。3 引数全削除 |
| `ChernoffConverse.lean:411` | `chernoff_converse_of_per_tilt_existential` | `h_per_tilt : ∃ lam ∈ Icc 0 1, … ∧ ∃ C > 0, …` (existence-bundle of FALSE) | `limsup rate ≤ chernoffInfo` | CS-false | B | 同上 | No | S0 | existence-bundle 削除。🟢ʰ load-bearing 散文 docstring → 「load-bearing FALSE per-tilt hyp」表現に refine |
| `ChernoffConverse.lean:447` | `chernoff_lemma_tendsto_from_per_tilt` | 同上 (`h_per_tilt`) | `Tendsto rate atTop (𝓝 chernoffInfo)` | CS-false | B | 同上 | No | S0 | 同上、Tendsto 変種 |

**散文 🟢ʰ 5 件**: module docstring (`:49/68`) + 3 declaration の docstring 内
形容詞 (`:382/384/439`)。**Phase 2.3 で sorry 化と同時に refine** (Relay pilot
の 「🟢ʰ load-bearing hypothesis」散文 → 「load-bearing FALSE per-tilt
hypothesis (successor で `ε`-relaxed route 経由 discharge 済)」表現に書換)。

### `ChernoffPerTiltDischarge.lean` — 5 closed-by-successor + 散文 🟢ʰ 3

| file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|
| `ChernoffPerTiltDischarge.lean:175` | `chernoff_converse_from_predicate` | `h_pred : IsBayesErrorPerTiltLowerBound P₁ P₂ lam` (FALSE predicate) | `limsup rate ≤ -log Z(λ)` | CS-false | B | `@residual(plan:chernoff-converse-sanov-discharge)` | No | S0 | h_pred 削除 + body sorry。obtain destructure で旧 body は `chernoff_converse_from_per_tilt` への forward だった |
| `ChernoffPerTiltDischarge.lean:195` | `chernoff_converse_discharged_from_predicate` | `h_predicate : ∃ lam ∈ Icc 0 1, … ∧ IsBayesErrorPerTiltLowerBound …` | `limsup rate ≤ chernoffInfo` | CS-false | B | 同上 | No | S0 | existence-bundle 削除 |
| `ChernoffPerTiltDischarge.lean:225` | `chernoff_lemma_tendsto_from_predicate` | 同上 (existence-bundle) | `Tendsto rate atTop (𝓝 chernoffInfo)` | CS-false | B | 同上 | No | S0 | 同上、Tendsto |
| `ChernoffPerTiltDischarge.lean:301` | `chernoff_lemma_tendsto_of_per_tilt` | `h_per_tilt : IsChernoffPerTiltDischargeable P₁ P₂` (FALSE bundle predicate) | `Tendsto` | CS-false | B | 同上 | No | S0 | 🟢ʰ 散文 `:274` を refine。body 1 行 forward |
| `ChernoffPerTiltDischarge.lean:338` | `chernoff_dotEq_tendsto_of_per_tilt` | 同上 | DotEq | CS-false | B | 同上 | No | S0 | 同上、🟢ʰ 散文 `:313` refine |

**散文 🟢ʰ 3 件**: 2 declaration docstring 内 (`:274/313`) + module docstring 1
件 (`:191`)。Phase 2.4 で refine。

**touch しない declaration** (本 plan scope 外、既存 tier 5 マーカー維持):
- `IsBayesErrorPerTiltLowerBound` (`:148`) — `@audit:defect(false-statement)` +
  `@audit:retract-candidate(false-replaced-by-eps-relaxed)` 維持。

### `ChernoffPerTiltSanov.lean` — 6 closed-by-successor + 散文 🟢ʰ 1

| file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|
| `ChernoffPerTiltSanov.lean:192` | `isChernoffNLetterRN_of_isBayesErrorPerTiltLowerBound` | `h_pred : IsBayesErrorPerTiltLowerBound …` (FALSE predicate) | `IsChernoffNLetterRN …` (FALSE predicate alias) | CS-false-laundered (Phase 0 tier 5 inline 検出済) | B | `@residual(plan:chernoff-converse-sanov-discharge)` | No (body `:= h_pred` の literal alias 解消) | S0 | hyp 削除 + body sorry。body `:= h_pred` の launder defect は signature 改変で解消、新規 `@audit:defect` 付与不要 |
| `ChernoffPerTiltSanov.lean:277` | `chernoff_lemma_tendsto_via_RN` | `h_predicate : ∃ lam ∈ Icc 0 1, … ∧ IsChernoffNLetterRN …` | `Tendsto` | CS-false | B | 同上 | No | S0 | existence-bundle 削除 |
| `ChernoffPerTiltSanov.lean:295` | `isChernoffPerTiltDischargeable_of_RN` | 同上 | `IsChernoffPerTiltDischargeable P₁ P₂` | CS-false | B | 同上 | No | S0 | conclusion type が FALSE predicate bundle (本 plan で touch しない `IsChernoffPerTiltDischargeable`)、結論型は維持 |
| `ChernoffPerTiltSanov.lean:309` | `chernoff_converse_via_RN_forall` | `h_forall : ∀ lam ∈ Icc 0 1, IsChernoffNLetterRN P₁ P₂ lam` (∀ form) | `limsup rate ≤ chernoffInfo` | CS-false | B | 同上 | No | S0 | ∀ form hyp 削除 + body sorry |
| `ChernoffPerTiltSanov.lean:326` | `chernoff_lemma_tendsto_via_RN_forall` | 同上 (`h_forall`) | `Tendsto` | CS-false | B | 同上 | No | S0 | ∀ form Tendsto |
| `ChernoffPerTiltSanov.lean:373` | `chernoff_dotEq_tendsto_via_RN` | `h_predicate` existence-bundle (RN form) | DotEq | CS-false | B | 同上 | No | S0 | DotEq 変種 |

**散文 🟢ʰ 1 件**: module docstring (`:75`、`chernoff_lemma_tendsto_of_per_tilt`
の 🟢ʰ load-bearing 言及)。Phase 2.5 で refine。

**touch しない declaration** (本 plan scope 外、既存 tier 5 マーカー維持):
- `IsChernoffNLetterRN` (`:148`) — `@audit:defect(false-statement)` +
  `@audit:retract-candidate(false-replaced-by-eps-relaxed)` 維持。
- `chernoff_per_tilt_via_RN` (`:181-185`) — `@audit:defect(launder)` +
  `@audit:retract-candidate(circular-between-false-predicates)` 維持。**body
  `:= h_RN` は literal alias defect (tier 5 既存マーカー)** であり、本 plan で
  sorry 化すると既存マーカーと衝突する。**touch しない**。

## Phase 詳細

### Phase 0 — Inventory (本 plan 内 inline、完了) 📋 ✅

- [x] 5 file の 19 closed-by-successor + 9 散文 🟢ʰ を verbatim 確認
  (`rg -n '@audit:closed-by-successor|🟢ʰ'` + 該当 docstring + signature 1-3 行)
- [x] Recipe A / B / C への分類 (CS-honest 3 / CS-genuine-hyps 2 / CS-false 11 /
  CS-false-laundered 1 / touch-しない既存 tier 5 マーカー 3)
- [x] cross-family dependency 確認 (sweep scope 内: utility import のみ、
  S2 cross-family は scope 外 `ChernoffBandMassDischarge` のみ → Pattern G
  escalate 不要)
- [x] 既存 `sorry` word-boundary 計数 `0` 件確定 (Pilot Pattern D 適用済、全 file 0)
- [x] ⚠ / HONESTY ALERT / FALSE 検出: 4 件 (全件既存 honest 注記、新規 honesty
  alert 該当なし)
- [x] tier 5 inline 検出: 3 件 (predicate def 2 + launder lemma 1) は touch せず、
  4 件目 `isChernoffNLetterRN_of_isBayesErrorPerTiltLowerBound` (`:192`) は
  Phase 2.5 で sorry 化対象 (signature 改変で literal alias 解消)
- [x] **closed-by-successor migration recipe (Phase Z) の 3 sub-pattern 分類確立**
  (本 plan の追加目的、Approach §「closed-by-successor migration recipe」)
- [x] constructive recovery 候補: 0 件 (全 19 declaration が load-bearing claim、
  Hoeffding / Relay pilot のような regularity-form は存在しない)

**proof-log**: no (mechanical 在庫確認、interesting なし)。

### Phase 1 — V/C cleanup (実質 skip) 📋

- [ ] **1.1** V/C 該当 declaration の legacy tag 削除 — 該当ゼロ件、**実質作業なし**。
  Cramér / Relay pilot と同じ skip 記録のみ。

**Phase 1 DoD**: 該当作業なし。Phase 2 に直接進む。constructive recovery 候補も
0 件 (Approach §「constructive recovery 候補」参照)。

**proof-log**: no。

### Phase Z — closed-by-successor migration recipe 確立 (本 plan 追加目的) 📋

- [ ] **Z.1** Approach §「closed-by-successor migration recipe」の 3 sub-pattern
  decision tree + Recipe A/B/C を **本 plan 内 inline で完結**。Phase Z は文書
  確立のみで実コード touch なし。
- [ ] **Z.2** Phase V.4 で本 recipe を `docs/audit/sorry-migration-runbook.md`
  「失敗パターン」section に **Pattern J (closed-by-successor migration)** として
  追加する提案を handoff に書き出す (runbook 拡張は別 session、本 plan で commit
  しない)。
- [ ] **Z.3** 後続 family (LZ78 / InfinitePiTiltedChangeOfMeasure 等
  `@audit:closed-by-successor` 残存) で本 recipe を参照する形を確認。LZ78 plan
  (`docs/shannon/lz78-sorry-migration-plan.md`) は既に存在するため本 plan の
  recipe 適用は **後続 family** から。

**Phase Z DoD**: 文書のみ、commit 単位は本 plan の他 Phase と一括。

**proof-log**: no (文書 establishment、特筆 finding なし)。

### Phase 2.1 — CS-honest retreat — `ChernoffSanovDischarge.lean` (3 件、Recipe A) 📋

- [ ] **2.1.1** `bayesErrorMinPmf_ge_exp_neg_mul_Z_pow` (`:295`)
  - signature 改変: `h_band : IsChernoffBandMassToOne P₁ P₂ lam` を **削除** (honest load-bearing hyp、successor で genuine discharge 済)。
  - 残す: `(P₁ P₂ : α → ℝ) [Nonempty α]` + `(hP₁_pos hP₂_pos : ∀ a, 0 < · a)` + `(lam : ℝ) (hlam_nn hlam_le : ...)` + `{ε : ℝ} (hε : 0 < ε)`。
  - 結論型 `∀ᶠ n, exp(-nε) · Z^n ≤ 4 · bayesError` 維持。
  - body: 旧 56-line `filter_upwards [h_band ε hε]` 経由 constructive proof → `by sorry`。
  - docstring: 旧 `@audit:closed-by-successor(chernoff-converse-sanov-discharge)` → `@residual(plan:chernoff-converse-sanov-discharge)`。
- [ ] **2.1.2** `chernoff_converse_from_eps_relaxed` (`:369`)
  - signature 改変: `h_eps : ∀ ε : ℝ, 0 < ε → ∀ᶠ n, exp(-nε)·Z^n ≤ 4·bayesError` を **削除**。
  - 残す: `(P₁ P₂ : α → ℝ) [Nonempty α]` + `(hP₁_pos hP₂_pos : ...)` + `(lam : ℝ)`。
  - 結論型 `limsup rate ≤ -log Z(λ)` 維持。
  - body → `by sorry`、tag 置換。
- [ ] **2.1.3** `chernoff_converse_of_bandMass` (`:469`)
  - signature 改変: `h_band : ∃ lam ∈ Icc 0 1, chernoffInfo = -log Z(λ) ∧ IsChernoffBandMassToOne P₁ P₂ lam` (existence-bundle) を **削除**。
  - 残す: `(P₁ P₂ : α → ℝ) [Nonempty α]` + `(hP₁_pos hP₂_pos : ...)`。
  - 結論型 `limsup rate ≤ chernoffInfo` 維持。
  - body → `by sorry`、tag 置換。
- [ ] **2.1.4** **`IsChernoffBandMassToOne` predicate def (`:243`) は touch しない**。
  successor `ChernoffBandMassDischarge.isChernoffBandMassToOne_of_interior_optimal:395`
  が live consumer (本 plan scope 外、依然として依存)。
- [ ] **2.1.5** Phase 2.1 完了時 olean refresh + verify:
  ```bash
  lake build InformationTheory.Shannon.ChernoffSanovDischarge
  lake env lean InformationTheory/Shannon/ChernoffSanovDischarge.lean
  # downstream verification (Phase V で全 file 一括だが暫定確認):
  lake env lean InformationTheory/Shannon/ChernoffBandMassDischarge.lean
  ```
  Phase 2.1 で touch する `ChernoffSanovDischarge.lean` の downstream は **scope 外 1 file
  (`ChernoffBandMassDischarge.lean`)** のみ。scope 内の他 4 file (`ChernoffPerTiltSanov` 等) は
  import 元として独立 (import 元 5 件すべてが Chernoff family の他 file、scope 内では
  `ChernoffSanovDischarge` の上流に位置しない、verbatim 確認: ChernoffSanovDischarge は
  ChernoffPerTiltSanov / ChernoffPerTiltDischarge / ChernoffConverse / Chernoff /
  ChernoffNLetterZSum を import している = downstream ではなく **upstream consumer**)。

**Phase 2.1 DoD**:
- `ChernoffSanovDischarge.lean` で `@audit:closed-by-successor(chernoff-converse-sanov-discharge)` 0 件、
  `@residual(plan:chernoff-converse-sanov-discharge)` 3 件、sorry 3 件、
- `lake env lean InformationTheory/Shannon/ChernoffSanovDischarge.lean` 0 errors。

**proof-log**: yes (`docs/proof-logs/proof-log-chernoff-sorry-migration-phase-2.1.md`)。
理由: 3 件で 56-line genuine proof を意図的に sorry 化する判断 (successor で
genuine proof 保全済) を記録。

### Phase 2.2 — CS-genuine-hyps retreat — `ChernoffInformation.lean` (2 件、Recipe C) 📋

- [ ] **2.2.1** `chernoff_lemma_tendsto` (`:135`)
  - signature 改変: `h_converse : limsup rate ≤ chernoffInfo` (L-Ch1 claim 自身) + `h_bdd_le : IsBoundedUnder (· ≤ ·) atTop ...` (L-Ch2 claim 自身) を **両方削除**。
  - 残す: `(P₁ P₂ : α → ℝ) [Nonempty α]` + `(hP₁_pos hP₂_pos : ...)`。
  - 結論型 `Tendsto rate atTop (𝓝 chernoffInfo)` 維持。
  - body: 旧 4-line `tendsto_of_le_liminf_of_limsup_le` forward → `by sorry`。
  - docstring tag 置換 + 「Successor discharge」散文を「`@residual` で closure 待ち」表現に refine。
- [ ] **2.2.2** `chernoff_dotEq_tendsto` (`:214`)
  - 同上 (`h_converse` + `h_bdd_le` 両削除)。
  - 結論型 `bayesError ≐ exp(-n·chernoffInfo)` 維持。
  - body → `by sorry`。
- [ ] **2.2.3** Phase 2.2 完了時 olean refresh + verify:
  ```bash
  lake build InformationTheory.Shannon.ChernoffInformation
  for f in InformationTheory/Shannon/ChernoffPerTiltDischarge.lean \
           InformationTheory/Shannon/ChernoffPerTiltSanov.lean \
           InformationTheory/Shannon/ChernoffConverse.lean \
           InformationTheory/Shannon/ChernoffSanovDischarge.lean \
           InformationTheory/Shannon/ChernoffBandMassDischarge.lean; do
    lake env lean "$f"
  done
  ```
  `ChernoffInformation.lean` を import する 5 file (scope 内 4 + scope 外 1) 全件で
  signature 改変による type drift を確認。

**Phase 2.2 DoD**:
- `ChernoffInformation.lean` で `@audit:closed-by-successor` 0 件、`@residual` 2 件、sorry 2 件、
- `lake env lean InformationTheory/Shannon/ChernoffInformation.lean` 0 errors。

**proof-log**: yes。理由: Recipe C alternative (successor forward redefinition)
を採用しない判断境界を記録 (signature 変更による downstream API 互換性破壊回避)。

### Phase 2.3 — CS-false retreat — `ChernoffConverse.lean` (3 件、Recipe B + 🟢ʰ 5 refine) 📋

- [ ] **2.3.1** `chernoff_converse_from_per_tilt` (`:274`)
  - signature 改変: `(lam : ℝ) (C : ℝ) (hC_pos : 0 < C) (h_lb : ∀ᶠ n, C·Z^n ≤ 2·bayesError)` の 4 引数を **削除** (C / hC_pos / h_lb は `IsBayesErrorPerTiltLowerBound` の destructure、`lam` は引数として残す)。
  - 残す: `(P₁ P₂ : α → ℝ) [Nonempty α]` + `(hP₁_pos hP₂_pos : ...)` + `(lam : ℝ)`。
  - 結論型 `limsup rate ≤ -log Z(λ)` 維持。
  - body: 旧 90-line constructive proof → `by sorry`。
  - docstring tag 置換 + 「Hypothesis shape」散文を `@residual` 説明に refine。
- [ ] **2.3.2** `chernoff_converse_of_per_tilt_existential` (`:411`)
  - signature 改変: `h_per_tilt : ∃ lam ∈ Icc 0 1, … ∧ ∃ C > 0, ∀ᶠ n, …` (existence-bundle of FALSE) を **削除**。
  - 残す: `(P₁ P₂ : α → ℝ) [Nonempty α]` + `(hP₁_pos hP₂_pos : ...)`。
  - 結論型 `limsup rate ≤ chernoffInfo` 維持。
  - body: 旧 5-line `obtain` + forward → `by sorry`。
  - docstring 🟢ʰ 散文 (`:382/384`) refine: 「🟢ʰ load-bearing hypothesis — NOT a discharge」
    → 「load-bearing FALSE per-tilt hypothesis (successor `ChernoffBandMassDischarge` で
    `ε`-relaxed route 経由 genuine discharge 済) — sorry-based migrated」表現に書換。
- [ ] **2.3.3** `chernoff_lemma_tendsto_from_per_tilt` (`:447`)
  - 同上 (`h_per_tilt` 削除、Tendsto 変種)。
  - docstring 🟢ʰ 散文 (`:439`) refine。
- [ ] **2.3.4** module docstring (`:49/68`) の 🟢ʰ 散文 refine: 「🟢ʰ load-bearing
  hypothesis」表現を「load-bearing FALSE per-tilt hypothesis (sorry-based migrated)」
  に書換。
- [ ] **2.3.5** Phase 2.3 完了時 olean refresh + verify:
  ```bash
  lake build InformationTheory.Shannon.ChernoffConverse
  for f in InformationTheory/Shannon/ChernoffPerTiltDischarge.lean \
           InformationTheory/Shannon/ChernoffPerTiltSanov.lean \
           InformationTheory/Shannon/ChernoffSanovDischarge.lean \
           InformationTheory/Shannon/ChernoffBandMassDischarge.lean; do
    lake env lean "$f"
  done
  ```

**Phase 2.3 DoD**:
- `ChernoffConverse.lean` で `@audit:closed-by-successor` 0 件、`@residual` 3 件、sorry 3 件、
- 散文 🟢ʰ 5 件 → 0 件 (refine 完了)、
- `lake env lean InformationTheory/Shannon/ChernoffConverse.lean` 0 errors。

**proof-log**: yes。理由: 🟢ʰ 散文 refine の表現境界 + Recipe B (FALSE predicate
consumer) sorry 化が honesty 階層で tier 4 → tier 2 移行であることの記録。

### Phase 2.4 — CS-false retreat — `ChernoffPerTiltDischarge.lean` (5 件、Recipe B + 🟢ʰ 3 refine) 📋

- [ ] **2.4.1** `chernoff_converse_from_predicate` (`:175`)
  - signature 改変: `h_pred : IsBayesErrorPerTiltLowerBound P₁ P₂ lam` を **削除**。
  - 残す: `(P₁ P₂ : α → ℝ) [Nonempty α]` + `(hP₁_pos hP₂_pos : ...)` + `(lam : ℝ)`。
  - body 旧 2-line forward → `by sorry`、tag 置換。
- [ ] **2.4.2** `chernoff_converse_discharged_from_predicate` (`:195`)
  - signature 改変: `h_predicate : ∃ lam ∈ Icc 0 1, … ∧ IsBayesErrorPerTiltLowerBound …` を **削除**。
  - body → `by sorry`、tag 置換。
- [ ] **2.4.3** `chernoff_lemma_tendsto_from_predicate` (`:225`)
  - 同上 (existence-bundle 削除、Tendsto 変種)。
- [ ] **2.4.4** `chernoff_lemma_tendsto_of_per_tilt` (`:301`)
  - signature 改変: `h_per_tilt : IsChernoffPerTiltDischargeable P₁ P₂` を **削除**。
  - body 1-line forward → `by sorry`。
  - docstring 🟢ʰ 散文 (`:274`) refine。
- [ ] **2.4.5** `chernoff_dotEq_tendsto_of_per_tilt` (`:338`)
  - 同上 (DotEq 変種、🟢ʰ 散文 `:313` refine)。
- [ ] **2.4.6** module docstring (`:191`) の 🟢ʰ 散文 refine。
- [ ] **2.4.7** **`IsBayesErrorPerTiltLowerBound` predicate def (`:148`) は touch しない**。
  既存 `@audit:defect(false-statement)` + `@audit:retract-candidate(false-replaced-by-eps-relaxed)`
  維持 — 既に最 honest 形 (tier 5 acknowledged)。
- [ ] **2.4.8** **`IsChernoffPerTiltDischargeable` (`:260-264`) は touch しない**。
  predicate def 自身は `@audit:defect` マーカー無し (FALSE 性は依存先 predicate
  経由) だが、本 plan で deprecation すると downstream broken。Phase 2.6 で
  `@audit:retract-candidate` 付与候補 (詳細 Phase 2.6)。
- [ ] **2.4.9** Phase 2.4 完了時 olean refresh:
  ```bash
  lake build InformationTheory.Shannon.ChernoffPerTiltDischarge
  for f in InformationTheory/Shannon/ChernoffPerTiltSanov.lean \
           InformationTheory/Shannon/ChernoffSanovDischarge.lean \
           InformationTheory/Shannon/ChernoffBandMassDischarge.lean; do
    lake env lean "$f"
  done
  ```

**Phase 2.4 DoD**:
- `ChernoffPerTiltDischarge.lean` で `@audit:closed-by-successor` 0 件、`@residual` 5 件、sorry 5 件、
- 散文 🟢ʰ 3 件 → 0 件、
- 既存 tier 5 マーカー (`IsBayesErrorPerTiltLowerBound`) 維持 (1 件)、
- `lake env lean InformationTheory/Shannon/ChernoffPerTiltDischarge.lean` 0 errors。

**proof-log**: yes。理由: Phase 2.4 は CS-false migration の中核 (5 件、最大)、
🟢ʰ 散文 refine の境界判定 + `IsChernoffPerTiltDischargeable` への
`@audit:retract-candidate` 付与判断境界 (Phase 2.6 連動) を記録。

### Phase 2.5 — CS-false-laundered retreat — `ChernoffPerTiltSanov.lean` (6 件、Recipe B + 🟢ʰ 1 refine + tier 5 launder 解消 1 件) 📋

- [ ] **2.5.1** `isChernoffNLetterRN_of_isBayesErrorPerTiltLowerBound` (`:192`)
  - **Phase 0 tier 5 inline 検出済 launder 解消 — 重要**: 旧 body `:= h_pred`
    (`IsBayesErrorPerTiltLowerBound → IsChernoffNLetterRN` の literal alias、
    両 predicate の body が同一) は本 sweep の Phase 2.5.1 で **signature 改変**
    により解消される。
  - signature 改変: `h_pred : IsBayesErrorPerTiltLowerBound P₁ P₂ lam` を **削除**。
  - 結論型 `IsChernoffNLetterRN P₁ P₂ lam` 維持。
  - body `:= h_pred` → `by sorry`。
  - docstring: 旧 `@audit:closed-by-successor(chernoff-converse-sanov-discharge)`
    → `@residual(plan:chernoff-converse-sanov-discharge)`。新規 `@audit:defect`
    付与は **不要** (literal alias defect は signature 改変で構造的に解消)。
- [ ] **2.5.2** `chernoff_lemma_tendsto_via_RN` (`:277`)
  - signature 改変: `h_predicate : ∃ lam ∈ Icc 0 1, … ∧ IsChernoffNLetterRN …` を **削除**。
  - body → `by sorry`、tag 置換。
- [ ] **2.5.3** `isChernoffPerTiltDischargeable_of_RN` (`:295`)
  - 同上 (existence-bundle 削除)。
  - 結論型 `IsChernoffPerTiltDischargeable P₁ P₂` 維持 (predicate 自身は本 plan で touch しないが、結論型として使用は問題なし)。
- [ ] **2.5.4** `chernoff_converse_via_RN_forall` (`:309`)
  - signature 改変: `h_forall : ∀ lam ∈ Icc 0 1, IsChernoffNLetterRN P₁ P₂ lam` (∀ form) を **削除**。
  - body → `by sorry`。
- [ ] **2.5.5** `chernoff_lemma_tendsto_via_RN_forall` (`:326`)
  - 同上 (∀ form Tendsto)。
- [ ] **2.5.6** `chernoff_dotEq_tendsto_via_RN` (`:373`)
  - signature 改変: `h_predicate` existence-bundle (RN form) を **削除**。
  - body → `by sorry`。
- [ ] **2.5.7** module docstring (`:75`) の 🟢ʰ 散文 refine。
- [ ] **2.5.8** **`IsChernoffNLetterRN` (`:148`) は touch しない**。既存
  `@audit:defect(false-statement)` + `@audit:retract-candidate(false-replaced-by-eps-relaxed)` 維持。
- [ ] **2.5.9** **`chernoff_per_tilt_via_RN` (`:181-185`) は touch しない**。
  既存 `@audit:defect(launder)` + `@audit:retract-candidate(circular-between-false-predicates)` 維持。
  body `:= h_RN` は literal alias で tier 5 既存マーカー、本 plan で sorry 化
  すると既存マーカーと衝突 (定義済の defect 表記が壊れる)。
- [ ] **2.5.10** **`chernoffMediatorMeasure` Phase C plumbing (`:218-267`、suspect 無し)** は touch しない。
  pi-measure 関連の constructive lemma で legacy tag 無し。
- [ ] **2.5.11** Phase 2.5 完了時 olean refresh:
  ```bash
  lake build InformationTheory.Shannon.ChernoffPerTiltSanov
  for f in InformationTheory/Shannon/ChernoffSanovDischarge.lean \
           InformationTheory/Shannon/ChernoffBandMassDischarge.lean; do
    lake env lean "$f"
  done
  ```

**Phase 2.5 DoD**:
- `ChernoffPerTiltSanov.lean` で `@audit:closed-by-successor` 0 件、`@residual` 6 件、sorry 6 件、
- 散文 🟢ʰ 1 件 → 0 件、
- 既存 tier 5 マーカー (`IsChernoffNLetterRN` + `chernoff_per_tilt_via_RN`) 維持 (2 件)、
- launder lemma `isChernoffNLetterRN_of_isBayesErrorPerTiltLowerBound` の `:= h_pred` body は signature 改変で解消 (新規 `@audit:defect` 付与不要)、
- `lake env lean InformationTheory/Shannon/ChernoffPerTiltSanov.lean` 0 errors。

**proof-log**: yes。理由: launder lemma の signature 改変による defect 解消判断 +
既存 tier 5 マーカー (predicate def + launder lemma 2 件) を **意図的に touch
しない** 判断境界を記録。

### Phase 2.x — ripple (caller drift handling) 📋

- [ ] **2.x.1** **family 内 caller**: 本 plan は **全 19 declaration が直接 sorry 化対象**
  なので、family 内 transitive caller は発生しない (各 declaration が自身の
  `@residual` タグ持ち)。Hoeffding / Relay pilot のような「上流 sorry → 下流 wrapper
  が transitive sorry を継承 + docstring 散文」は本 sweep では skip。
- [ ] **2.x.2** **family 外 caller (scope 外 `ChernoffBandMassDischarge.lean`)**:
  下記 `rg` で本 sweep が sorry 化する 19 declaration を呼び出す行を確認:
  ```bash
  rg -n 'chernoff_lemma_tendsto|chernoff_dotEq_tendsto|chernoff_converse_of_per_tilt_existential|bayesErrorMinPmf_ge_exp_neg_mul_Z_pow|chernoff_converse_from_eps_relaxed|chernoff_converse_of_bandMass|chernoff_converse_from_predicate|chernoff_converse_discharged_from_predicate|chernoff_lemma_tendsto_from_predicate|chernoff_lemma_tendsto_of_per_tilt|chernoff_dotEq_tendsto_of_per_tilt|isChernoffNLetterRN_of_isBayesErrorPerTiltLowerBound|chernoff_lemma_tendsto_via_RN|isChernoffPerTiltDischargeable_of_RN|chernoff_converse_via_RN_forall|chernoff_lemma_tendsto_via_RN_forall|chernoff_dotEq_tendsto_via_RN|chernoff_converse_from_per_tilt|chernoff_lemma_tendsto_from_per_tilt' InformationTheory/Shannon/ChernoffBandMassDischarge.lean
  ```
  expected: `chernoff_converse_holds` (`:536`) が
  `bayesErrorMinPmf_ge_exp_neg_mul_Z_pow` を呼出 (Phase 2.1 で sorry 化)、
  `chernoff_lemma_tendsto_holds` (`:560`) が `chernoff_converse_holds` を経由して
  transitive に依存。
  - 予想 transitive: `ChernoffBandMassDischarge.chernoff_converse_holds` /
    `chernoff_lemma_tendsto_holds` が **transitive sorry** に降格する。
- [ ] **2.x.3** scope 外 transitive caller の処理判断 (Pattern C):
  - `ChernoffBandMassDischarge.lean` は本 plan の sweep scope **外**、touch しない方針が原則。
  - ただし scope 外で transitive sorry が顕在化する場合、docstring に散文追加するか
    auditor 委任 (未決事項 #3)。
  - 本 plan のデフォルト: **scope 外 file には散文追加 しない** — `ChernoffBandMassDischarge`
    は successor file 本人 (regularity-only completion を担っている)、transitive
    sorry が顕在化したら独立 audit + 別 session で対応 (本 plan を超えた scope)。

**Phase 2.x DoD**: family 内 caller 0 件、scope 外 transitive は本 plan
touch せず handoff で次 session に明示。

**proof-log**: no (mechanical 散文追加なし、空 phase)。

### Phase 2.6 — predicate retract-candidate 付与 📋

family 内の load-bearing predicate / hypothesis に
`@audit:retract-candidate(load-bearing-predicate)` を付与:

| file:line | predicate | 既存 tag | retract-candidate 付与方針 |
|---|---|---|---|
| `ChernoffPerTiltDischarge.lean:148` | `IsBayesErrorPerTiltLowerBound` (FALSE def) | `@audit:defect(false-statement)` + `@audit:retract-candidate(false-replaced-by-eps-relaxed)` | **付与しない** (既存 `retract-candidate(false-replaced-by-eps-relaxed)` で十分、新規付与は redundant) |
| `ChernoffPerTiltDischarge.lean:260-264` | `IsChernoffPerTiltDischargeable` (FALSE bundle predicate、predicate def 自身は tier 5 マーカー無し) | (なし) | **付与候補** — 全 consumer 削除済 (Phase 2.4 で 2 件、Phase 2.5 で 1 件)。`@audit:retract-candidate(load-bearing-predicate)` を新規付与 + docstring 散文に「FALSE bundle of `IsBayesErrorPerTiltLowerBound` (本 plan で全 consumer sorry-based 移行済)」を明示 |
| `ChernoffPerTiltSanov.lean:148` | `IsChernoffNLetterRN` (FALSE def) | `@audit:defect(false-statement)` + `@audit:retract-candidate(false-replaced-by-eps-relaxed)` | **付与しない** (既存) |
| `ChernoffPerTiltSanov.lean:181-185` | `chernoff_per_tilt_via_RN` (literal alias lemma) | `@audit:defect(launder)` + `@audit:retract-candidate(circular-between-false-predicates)` | **付与しない** (既存) |
| `ChernoffSanovDischarge.lean:243` | `IsChernoffBandMassToOne` (honest predicate、live consumer あり) | (なし) | **付与しない** — successor file `ChernoffBandMassDischarge:395` が live consumer、retract-candidate 付与は意味矛盾 (削除候補 ≠ live consumer 持ち) |

- [ ] **2.6.1** `IsChernoffPerTiltDischargeable` (`ChernoffPerTiltDischarge.lean:260-264`) のみ新規付与:
  ```lean
  -- 旧 docstring 末尾追加
  /-- ...
  @audit:retract-candidate(load-bearing-predicate) -/
  def IsChernoffPerTiltDischargeable (P₁ P₂ : α → ℝ) : Prop := ...
  ```
  docstring 散文に「**Note**: FALSE bundle of `IsBayesErrorPerTiltLowerBound`
  (本 sorry-based migration で全 consumer wrapper が sorry 化済、本 predicate は
  load-bearing 経路として残置されているが本 plan で deprecate 候補)」を追記。
- [ ] **2.6.2** 他 predicate (`IsBayesErrorPerTiltLowerBound` / `IsChernoffNLetterRN` /
  `chernoff_per_tilt_via_RN` / `IsChernoffBandMassToOne`) は **touch しない**
  (既存マーカー維持 or live consumer 持ち)。

**Phase 2.6 DoD**: 新規 `@audit:retract-candidate(load-bearing-predicate)` 1 件
(`IsChernoffPerTiltDischargeable`) 付与、既存 tier 5 マーカー 3 件維持。

**proof-log**: no (mechanical 付与 1 件、判断境界は本 Phase 文書内で完結)。

### Phase 2.7 — audit-2 (independent honesty audit) 📋

- [ ] **2.7.1** Fresh `honesty-auditor` を起動 (CLAUDE.md「Independent honesty
  audit」、`.claude/agents/honesty-auditor.md` 既存)。対象:
  - Phase 2.1 (ChernoffSanovDischarge 3 件、CS-honest Recipe A)
  - Phase 2.2 (ChernoffInformation 2 件、CS-genuine-hyps Recipe C)
  - Phase 2.3 (ChernoffConverse 3 件、CS-false Recipe B + 🟢ʰ 5 件 refine)
  - Phase 2.4 (ChernoffPerTiltDischarge 5 件、CS-false Recipe B + 🟢ʰ 3 件 refine + `IsChernoffPerTiltDischargeable` retract-candidate 付与判定)
  - Phase 2.5 (ChernoffPerTiltSanov 6 件、CS-false-laundered Recipe B + 🟢ʰ 1 件 refine + launder body 解消判定)
  - Phase 2.6 (1 件 retract-candidate 付与)
- [ ] **2.7.2** verdict 受領 + 修正対応:
  - `ok` → Phase V 着手。
  - `questionable` → docstring refine or 散文追記、Phase V 進行。
  - `defect` → 当該 declaration を撤回 / 修正、Phase V 進行前に解決。
- [ ] **2.7.3** **Recipe A/B/C 判定の妥当性確認**: auditor が 3 sub-pattern 分類を
  独立検証 (Phase Z の decision tree が正しく適用されたか)。
- [ ] **2.7.4** **既存 tier 5 マーカー保護確認**: `IsBayesErrorPerTiltLowerBound` /
  `IsChernoffNLetterRN` / `chernoff_per_tilt_via_RN` の 3 既存マーカーが本 plan で
  touch されていないことを auditor が確認。

**proof-log**: yes (verdict + 対応記録)。

### Phase V — verify + 計画反映 📋

- [ ] **V.1** 全 5 file (+ scope 外 transitive 受け先 `ChernoffBandMassDischarge.lean`) で `lake env lean` 確認:
  ```bash
  # signature 改変があった file (5 file 全件) は事前に olean refresh:
  lake build InformationTheory.Shannon.ChernoffInformation
  lake build InformationTheory.Shannon.Chernoff   # base, scope 外だが downstream の base
  lake build InformationTheory.Shannon.ChernoffConverse
  lake build InformationTheory.Shannon.ChernoffPerTiltDischarge
  lake build InformationTheory.Shannon.ChernoffPerTiltSanov
  lake build InformationTheory.Shannon.ChernoffSanovDischarge
  lake build InformationTheory.Shannon.ChernoffBandMassDischarge   # scope 外 + transitive

  # 逆 import 順で verify (最 dependent から):
  for f in InformationTheory/Shannon/ChernoffBandMassDischarge.lean \
           InformationTheory/Shannon/ChernoffSanovDischarge.lean \
           InformationTheory/Shannon/ChernoffPerTiltSanov.lean \
           InformationTheory/Shannon/ChernoffPerTiltDischarge.lean \
           InformationTheory/Shannon/ChernoffConverse.lean \
           InformationTheory/Shannon/ChernoffInformation.lean; do
    echo "=== $f ==="
    lake env lean "$f"
  done
  ```
  - signature 改変 file: 5 件 (Phase 2.1-2.5)、Pilot Pattern A の olean refresh
    必須。
  - scope 外 `ChernoffBandMassDischarge.lean` で transitive sorry が顕在化する
    可能性 (詳細 Phase 2.x、未決事項 #3)。

- [ ] **V.2** 集計コマンド実行:
  ```bash
  rg -c '@audit:closed-by-successor' InformationTheory/Shannon/Chernoff{SanovDischarge,PerTiltDischarge,PerTiltSanov,Converse,Information}.lean | awk -F: '{s+=$2} END {print "closed-by-successor:", s}'   # = 0
  rg -c '🟢ʰ' InformationTheory/Shannon/Chernoff{SanovDischarge,PerTiltDischarge,PerTiltSanov,Converse,Information}.lean | awk -F: '{s+=$2} END {print "🟢ʰ:", s}'   # = 0
  rg -c '@residual\(plan:chernoff-converse-sanov-discharge\)' InformationTheory/Shannon/Chernoff{SanovDischarge,PerTiltDischarge,PerTiltSanov,Converse,Information}.lean | awk -F: '{s+=$2} END {print "residual:", s}'   # = 19
  rg -c '@audit:retract-candidate' InformationTheory/Shannon/Chernoff{SanovDischarge,PerTiltDischarge,PerTiltSanov,Converse,Information}.lean | awk -F: '{s+=$2} END {print "retract-candidate:", s}'   # = 3 (既存 2 + 新規 1)
  rg -c '@audit:defect' InformationTheory/Shannon/Chernoff{SanovDischarge,PerTiltDischarge,PerTiltSanov,Converse,Information}.lean | awk -F: '{s+=$2} END {print "defect (existing tier 5 markers):", s}'   # = 3 (既存維持)
  rg -nw 'sorry' InformationTheory/Shannon/Chernoff{SanovDischarge,PerTiltDischarge,PerTiltSanov,Converse,Information}.lean | wc -l   # = 19
  ```
  期待値: closed-by-successor 0、🟢ʰ 0、residual 19、retract-candidate 3 (既存
  `IsBayesErrorPerTiltLowerBound:147` + `IsChernoffNLetterRN:147` + 新規
  `IsChernoffPerTiltDischargeable`)、defect 3 (既存 `IsBayesErrorPerTiltLowerBound` +
  `IsChernoffNLetterRN` + `chernoff_per_tilt_via_RN`)、sorry 19。

- [ ] **V.3** 親 plan banner 更新:
  - `chernoff-converse-moonshot-plan.md` 冒頭 banner に「sorry-based 移行完了
    (本 plan 参照)、19 declaration を `@residual(plan:chernoff-converse-sanov-discharge)`
    に書換、既存 tier 5 マーカー 3 件は維持」を追記。
  - `chernoff-converse-sanov-discharge-plan.md` 冒頭 banner に同様
    (closure plan slug が本 plan からの参照先となる)。
  - `chernoff-moonshot-plan.md` 冒頭 banner に「Round 3 pilot として
    closed-by-successor migration recipe を確立」を追記 (本 plan の追加目的)。

- [ ] **V.4** **Phase Z recipe を runbook に反映** — handoff `.claude/handoff-sorry-migration.md`
  に次を書き出す:
  - 本 plan で確立した closed-by-successor migration recipe (3 sub-pattern decision tree +
    Recipe A/B/C) を `docs/audit/sorry-migration-runbook.md`「失敗パターン」section に
    **Pattern J (closed-by-successor migration)** として追加する提案。
  - runbook 拡張は別 session (本 plan の commit 範囲外)。

- [ ] **V.5** Pilot 知見を `.claude/handoff-sorry-migration.md` に反映:
  - **Round 3 pilot 完了**: closed-by-successor migration の 3 sub-pattern recipe
    確立、後続 family (LZ78 / InfinitePiTiltedChangeOfMeasure 等) は本 recipe を
    参照可能。
  - **constructive recovery 候補 0 件** (Hoeffding 1 + Relay 4 と異なり、Chernoff
    は全 19 件 load-bearing claim)。Pattern B (overcorrect risk) は本 sweep には
    適用されない pattern。
  - **既存 tier 5 マーカー保護パターン**: predicate def に既存 `@audit:defect` +
    `@audit:retract-candidate` がある場合、consumer wrapper の sorry 化と predicate
    def の維持を **明確に分離** する必要があることを recipe に記録 (`IsBayesErrorPerTiltLowerBound` /
    `IsChernoffNLetterRN` / `chernoff_per_tilt_via_RN` の 3 件で実証)。
  - **scope 外 transitive sorry の handling** は本 sweep で 触れず、次 session 委任。
    `ChernoffBandMassDischarge.lean` (successor file 本人) は本 plan の sorry 化で
    transitive sorry が顕在化する可能性 (Phase V.1 で確認)。

## 撤退ライン

- **L-MIG-1 (Phase 2.2 Recipe C alternative 採用判定)**: planner default は Recipe C
  (sorry 化)。auditor が「Recipe C alternative (successor `chernoff_lemma_tendsto_holds`
  への forward redefinition) を採用すべき」と判定したら、signature 変更を伴う
  forward redefinition に切替 (downstream API 互換性破壊リスクを承知の上)。
  alternative 判断は Phase 2.7 で確定、未決事項 #2 で escalate。

- **L-MIG-2 (既存 tier 5 マーカー touch 禁止違反)**: 本 plan は `IsBayesErrorPerTiltLowerBound` /
  `IsChernoffNLetterRN` / `chernoff_per_tilt_via_RN` の 3 既存マーカーを **touch
  しない** ことが原則。implementer / auditor が既存マーカーを sorry-based に
  「移行」しようとしたら **即停止** + L-MIG-2 発動 (既存マーカーは tier 5
  acknowledged、本 plan の sweep scope 外)。

- **L-MIG-3 (Phase Z recipe の sub-pattern 誤分類)**: 19 declaration の Recipe A/B/C
  分類が auditor で覆ったら (例: CS-honest と分類した `ChernoffSanovDischarge:295`
  が実は CS-false 寄り、または逆)、本 plan の Phase 2.1-2.5 を分類見直し後に
  再実行。分類の根拠は本 plan の在庫表 + Approach decision tree、auditor は
  各 declaration の **hypothesis predicate に既存 `@audit:defect` があるか** を
  独立確認。

- **L-MIG-4 (scope 外 transitive sorry が auditor で DEFECT 判定)**:
  `ChernoffBandMassDischarge.lean` で transitive sorry が顕在化 + auditor が
  「scope 外 file に散文追加すべき」と判定したら、本 plan の scope を拡大
  (`ChernoffBandMassDischarge` の transitive caller 2-3 件に Pattern C 散文追加)。
  ただし本 plan のデフォルトは scope 維持 (`ChernoffBandMassDischarge` は
  proof done 寄りで保護)。

- **L-MIG-5 (Approach 変更: pilot scope を縮める)**: Phase 2 全体 (19 件 sorry 化 +
  1 件 retract-candidate 付与) が 1 session で完走しない / honesty-auditor が
  DEFECT を多発させる場合、3 sub-pattern のうち **CS-honest (Phase 2.1) + CS-genuine-hyps
  (Phase 2.2) の 5 件のみで pilot を close** し、CS-false (Phase 2.3-2.5) の 14 件は
  後続 session に分離。Phase Z recipe は CS-honest / CS-genuine-hyps の 2 sub-pattern で
  示されれば後続適用可能 (CS-false は最も多いが Recipe B 自体は最も単純で
  recipe 確立は CS-honest / CS-genuine-hyps で十分)。

## 未決事項

planner が判断つかない事項を列挙。auditor 委任 / user 確認に区分:

1. **`IsChernoffPerTiltDischargeable` (`ChernoffPerTiltDischarge.lean:260-264`) の
   `@audit:retract-candidate` 付与判断** (auditor 判定対象):
   本 predicate は FALSE bundle (`IsBayesErrorPerTiltLowerBound` の existence
   bundle) で、本 plan の Phase 2.4 + 2.5 で **全 consumer wrapper を sorry-based
   migrate**。残る use site は predicate def 自身のみ。本 plan のデフォルトは
   Phase 2.6 で `@audit:retract-candidate(load-bearing-predicate)` 新規付与。
   auditor 判断対象:
   - (a) 新規付与 (本 plan default)、
   - (b) 既存 `@audit:defect(false-statement)` を新規付与 (predicate def 自身を
     tier 5 マーカー化、`IsBayesErrorPerTiltLowerBound` と同等扱い)、
   - (c) 付与せず維持 (consumer は全て sorry 化済、predicate def は live consumer なし
     で API 残置)。

2. **Phase 2.2 Recipe C alternative の採用判断** (user 確認):
   `chernoff_lemma_tendsto` / `chernoff_dotEq_tendsto` の 2 件で sorry 化 (default)
   と successor forward redefinition (alternative) のどちらを採用するか:
   - (a) sorry 化 (default): signature 維持、`h_converse` + `h_bdd_le` 削除、body sorry。
   - (b) successor forward: signature 拡張 (新規 `hP₁_sum` / `hP₂_sum` / `hne`)、
     body は `ChernoffBandMassDischarge.chernoff_lemma_tendsto_holds` への forward。
     downstream API 互換性が壊れるが genuine proof を維持。
   user 確認待ち。

3. **scope 外 `ChernoffBandMassDischarge.lean` の transitive sorry handling**
   (auditor 判定対象 / 次 session 委任):
   Phase V.1 で `lake env lean InformationTheory/Shannon/ChernoffBandMassDischarge.lean`
   実行時に transitive sorry warning が増える可能性 (詳細 Phase 2.x.2)。本 plan
   default は **scope 外で touch しない**、auditor が「scope 拡大すべき」と判定
   したら L-MIG-4 発動。実 sweep は次 session 委任候補。

4. **`closed-by-successor` migration recipe (Phase Z) の `audit-tags.md` /
   `sorry-migration-runbook.md` への formal 反映** (user 確認 / 後続 PR):
   本 plan で確立した 3 sub-pattern decision tree + Recipe A/B/C を:
   - (a) `audit-tags.md`「Deprecated」表に Recipe A/B/C 注記追加、
   - (b) `sorry-migration-runbook.md`「失敗パターン」に Pattern J (closed-by-successor
     migration) として追加、
   - (c) 両方、
   - (d) 本 plan 内 inline 維持 (formal 反映なし) — 後続 family 適用時に
     plan ごとに参照。
   本 plan のデフォルトは (b) (Phase V.4 で handoff に書き出す)、(a) (c) は
   後続 PR で検討。

5. **proof done を本 plan で目指さない方針の明示確認** (user 確認):
   本 plan の DoD は **type-check done** のみ。Cover-Thomas Theorem 11.9.1 の
   analytical closure は successor file `ChernoffBandMassDischarge.lean` で
   regularity-only 完成済 (0 sorry)、本 plan の sweep は **wrapper 側 file の
   honesty 強化** のみ。`chernoff-{converse-,converse-sanov-discharge-,}moonshot-plan.md`
   の closure 状態は変えない。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-26 plan 起草**: lean-planner (本 session、docs-only) が
   `InformationTheory/Shannon/Chernoff{SanovDischarge,PerTiltDischarge,PerTiltSanov,Converse,Information}.lean`
   5 file の legacy tag 28 件 (closed-by-successor 19 + 散文 🟢ʰ 9) を verbatim
   読込で per-declaration 分類。
   - **既存 sorry 計数**: word-boundary `rg -nwc 'sorry'` で **5 file 全て 0 hit**
     (Pilot Pattern D 適用済)。
   - **⚠ / HONESTY ALERT / FALSE 検出**: 4 hits、全件既存 honest 注記 (predicate
     FALSE の著者明示)、Pattern H 該当だが新規 honesty alert は無し。
   - **既存 tier 5 マーカー検出**: 3 件 (`IsBayesErrorPerTiltLowerBound:147` +
     `IsChernoffNLetterRN:147` + `chernoff_per_tilt_via_RN:181`)、全件本 plan
     scope **外** (既に最 honest 形、touch しない)。
   - **cross-family entanglement**: 本 sweep scope 内 0 件 (utility import のみ)、
     scope 外 `ChernoffBandMassDischarge` に Cramér family S2 dependency あり (本 plan
     touch しない)。
   - **constructive recovery 候補**: 0 件 (全 19 declaration が load-bearing claim、
     Hoeffding 1 / Relay 4 と異なり)。
   - **戦略確定**:
     - 上流 → 下流 chain 順序 (CS-honest → CS-genuine-hyps → CS-false → CS-false-laundered)、
     - shared wall 集約なし (`plan:chernoff-converse-sanov-discharge` slug 揃え)、
     - 既存 tier 5 マーカー保護 (3 件 touch しない)、
     - Phase Z で closed-by-successor migration recipe (3 sub-pattern decision tree +
       Recipe A/B/C) を establish (本 plan の追加目的、Round 3 pilot)、
     - proof done は範囲外。

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
2. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->

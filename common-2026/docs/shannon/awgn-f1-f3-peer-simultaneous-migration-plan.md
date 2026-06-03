# AWGN F-1/F-3 撤退ライン peer 同時第一選択 migration plan 🌙 (Round 4 escalate #1)

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §「撤退ライン F-1/F-3」
> + [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md) (F-1 analytic discharge plan、未着手)
> + [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md) (F-3 analytic discharge plan、stub)
> + [`awgn-sorry-migration-plan.md`](awgn-sorry-migration-plan.md) (Round 4 Wave A、tier 5 既存維持で signature 改変 scope 外)
> + [`audit/audit-tags.md`](../audit/audit-tags.md) — 語彙 SoT
>   (`name-laundering-alias` + `closure-plan-completed` + tier 2 `sorry+@residual` 第一選択)
> + [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) — Step 1-4 + Pattern A-J
>
> **Status (2026-05-26)**: 起草中 (起草者 = `lean-planner`、本 plan は Lean code を書かず Phase
> 構造のみを定義)。Wave 4-D audit cluster 1 + cluster 3 で「F-1/F-3 撤退ライン peer の構造的対称性」
> が verbatim 観察済 + Round 4 escalate #1 として handoff 登録済。
>
> **Goal (1 行)**: `IsAwgnTypicalityHypothesis` (F-1) + `IsAwgnConverseHypothesis` (F-3) を
> **1 PR で同時に第一選択 migration** (predicate 削除 + `awgn_achievability` / `awgn_converse`
> body `sorry` + `@residual(plan:<analytic-plan-slug>)`、Tier 2)。peer の構造的対称性により
> 1 PR 統合で整合性が上がり、F-2 alias 2 件 (`IsAwgnF2DecodingHypothesis` /
> `IsAwgnF3ChainHypothesis`、verbatim-equivalent body redefinition) も自動消失候補。
>
> **honesty 規律**: 本 plan は tier 5 既存マーカー
> (`@audit:defect(circular)` `@audit:closed-by-successor(...)`)
> を **Tier 2 (`sorry + @residual(plan:...)`)** に昇格させることが目的。
> CLAUDE.md「sorry を書けない箇所での対処順序」第一選択 = 定義書換 → predicate 削除 →
> 結論型を直接 theorem signature に → body `sorry` + `@residual`。
>
> **撤退ライン**: L-FFP-1 (downstream consumer 5+ file 横断で大量 drift → 個別 family sweep
> に降格) / L-FFP-2 (F-1 と F-3 で hyp shape が異なり 1 PR 統合困難 → 2 PR 分離)。
> §「撤退ライン」参照。

## 進捗

- [ ] Phase 0 — 規模見積もり + 4 predicate verbatim 確認 + 全 consumer rg + scope 判定 + sub-bound 引数表 📋
- [ ] Phase 1 — F-1 predicate (+ F-2 alias) 削除 + `awgn_achievability` body sorry + `@residual` 📋
- [ ] Phase 2 — F-3 predicate (+ F-3 alias) 削除 + `awgn_converse` body sorry + `@residual` 📋
- [ ] Phase V — verify (全 8 file lake env lean 0 errors + honesty-auditor 必須起動 + Round 4 escalate #1 closure) 📋

## ゴール / Approach

### 最終形 (signature 改変後)

```lean
-- AWGNAchievability.lean
namespace InformationTheory.Shannon.AWGN

-- 旧 def IsAwgnTypicalityHypothesis (P N h_meas) : Prop := ∀ {R} ... を **削除**

/-- **AWGN achievability theorem (Cover-Thomas 9.1.1)**.
…(載せ替えた docstring は load-bearing hyp / circular def を消した形)…
@residual(plan:awgn-achievability-typicality-plan) -/
theorem awgn_achievability
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε := by
  sorry

end InformationTheory.Shannon.AWGN
```

```lean
-- AWGNConverse.lean (mirror for F-3)
namespace InformationTheory.Shannon.AWGN

-- 旧 def IsAwgnConverseHypothesis (P N h_meas) : Prop := ∀ {M n} ... を **削除**

/-- **AWGN converse theorem (Cover-Thomas 9.1.2)**.
…(load-bearing bundle / circular def を消した形)…
@residual(plan:awgn-converse-aux-plan) -/
theorem awgn_converse
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (hM : 2 ≤ M)
    (c : AwgnCode M n P)
    (Pe : ℝ)
    (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  sorry

end InformationTheory.Shannon.AWGN
```

### Approach (overall strategy)

**戦略**: peer の構造的対称性を活かし 1 PR 統合 sweep。

1. **predicate 削除を先に**: `IsAwgnTypicalityHypothesis` (`AWGNAchievability.lean:47`) +
   `IsAwgnConverseHypothesis` (`AWGNConverse.lean:69`) の `def` を file から削除。これは
   `@audit:defect(circular)` + `@audit:closed-by-successor(...)` 既存マーカーの tier 5
   昇格元 = Tier 2 への第一選択 migration の本体。
2. **wrapper body を sorry 化**: `awgn_achievability` (`AWGNAchievability.lean:86`) +
   `awgn_converse` (`AWGNConverse.lean:105`) の hyp `h_typicality` / `h_converseBound_lbh`
   を signature から削除、body を `sorry` + `@residual(plan:<analytic-plan-slug>)` に。
3. **F-2 / F-3 alias の同時消失判定**:
   - `IsAwgnF2DecodingHypothesis` (`AWGNF2F3Discharge.lean:194`) ≡ `IsAwgnTypicalityHypothesis`
     body verbatim → predicate 削除と同時に **alias 自動消失候補** (Wave 4-D で
     `@audit:retract-candidate(name-laundering-alias)` 付与済)。
   - `IsAwgnF3ChainHypothesis` (`AWGNF2F3Discharge.lean:253`) ≡ `IsAwgnConverseHypothesis`
     body verbatim → 同上 mirror。
   - alias を削除すると `awgn_theorem_of_F2F3_hypotheses` (`AWGNF2F3Discharge.lean:288`) の
     signature 大幅縮約 (`h_F2` / `h_F3_chain` 2 hyp 不要)、`awgn_theorem_F4_discharged_F1_via_staged`
     経由の cascade migration が必要。
4. **downstream consumer 全 8 file の wrapper signature 連動修正**: 全 wrapper の
   `(h_typicality : IsAwgnTypicalityHypothesis P N h_meas)` / `(h_converse : IsAwgnConverseHypothesis P N h_meas)`
   hyp 引数を**削除** + body の引数 thread を消す + tag `@audit:closed-by-successor` → 維持
   (sorry-based migration 完了後の bookkeeping、`@residual` は wrapper 側にも追加判定)。
5. **F-1 と F-3 を別 Phase に分割**: 1 Phase 内で 1 predicate 削除 + 全 consumer 連動修正 +
   verify、Phase 1 (F-1) → Phase 2 (F-3) の順次。LSP 第 1 戻りでの型 mismatch を**Phase 単位**
   で隔離 (Phase 1 完了 = F-1 関連 olean refresh + 0 errors、Phase 2 で F-3 を独立 sweep)。
6. **Phase V で 1 commit 集約 (1 PR、Round 4 escalate #1 closure)**: Phase 1 + Phase 2 を
   squash commit、honesty-auditor 必須起動 (新規 `sorry` + `@residual` 2 件 + alias 2 削除
   + downstream wrapper 14+ signature 改変)。

### Mathlib-shape-driven 視点 (CLAUDE.md)

本 plan は predicate **削除**が中心 (新規 def の formulation 選択は無し)、結論型は既存の
`∃ N₀, ∀ n ≥ N₀, ∃ M ..., ∀ m, errorProb < ε` / `Real.log M ≤ ...` 形を維持する。
predicate 削除後の結論型は **Mathlib 形式に依存しない theorem statement** で、analytic
discharge plan (`awgn-achievability-typicality-plan` Phase E / `awgn-converse-aux-plan`
未着手) が `sorry` を埋めるときに Mathlib 結論形へ揃える設計責任を継承。

### 規模見積もり

| 項目 | F-1 (Phase 1) | F-3 (Phase 2) | 合計 |
|---|---|---|---|
| predicate 削除 | 1 (`IsAwgnTypicalityHypothesis`) | 1 (`IsAwgnConverseHypothesis`) | 2 |
| alias 削除 (verbatim-equivalent) | 1 (`IsAwgnF2DecodingHypothesis`) | 1 (`IsAwgnF3ChainHypothesis`) | 2 |
| wrapper signature 改変 (hyp 削除 + body sorry) | 1 (`awgn_achievability`) | 1 (`awgn_converse`) | 2 |
| downstream wrapper hyp pass-through 連動修正 | ~7 wrapper (8 file) | ~7 wrapper (8 file) | ~14 wrapper |
| 新規 `sorry` 件数 | 1 | 1 | **2** |
| 新規 `@residual(plan:...)` 件数 | 1 (plus 連動 1-2 wrapper) | 1 (plus 連動 1-2 wrapper) | **2-4** |
| 中央予測 diff 行数 | ~80-150 行 | ~80-150 行 | **~160-300 行** |
| 並列度 | Phase 1 → Phase 2 (sequential) | (同上) | 単独 implementer dispatch |
| Mathlib re-build | `lake build InformationTheory.Shannon.AWGNAchievability` 1 回 + dependent | `lake build InformationTheory.Shannon.AWGNConverse` 1 回 + dependent | 2 回 |

中央予測 **~200 行** (predicate 削除 + 14 wrapper の hyp 1 本ずつ削除 + body 改変 + tag refine)。

### ファイル構成 + scope (verbatim 確認、2026-05-26)

| file | 触る種別 | 内容 | Phase |
|---|---|---|---|
| `InformationTheory/Shannon/AWGNAchievability.lean` | predicate 削除 + wrapper sorry 化 | F-1 primary | Phase 1 |
| `InformationTheory/Shannon/AWGNConverse.lean` | predicate 削除 + wrapper sorry 化 | F-3 primary | Phase 2 |
| `InformationTheory/Shannon/AWGNF2F3Discharge.lean` | F-2 + F-3 alias 削除 + cascade wrapper signature 縮約 | F-1 + F-3 cascade | Phase 1 + Phase 2 |
| `InformationTheory/Shannon/AWGNMain.lean` | `awgn_channel_coding_theorem` の `h_typicality` + `h_converse` 削除 | downstream | Phase 1 + Phase 2 |
| `InformationTheory/Shannon/AWGNF1Discharge.lean` | `awgn_theorem_F1_discharged` の 2 hyp 削除 | downstream | Phase 1 + Phase 2 |
| `InformationTheory/Shannon/AWGNBindConvBody.lean` | `awgn_theorem_of_typicality_converse_bindconv_discharged` の 2 hyp 削除 | downstream | Phase 1 + Phase 2 |
| `InformationTheory/Shannon/AWGNMIBridge.lean` | `awgn_theorem_F2_discharged` の 2 hyp 削除 | downstream | Phase 1 + Phase 2 |
| `InformationTheory/Shannon/AWGNMIBridgeDischarge.lean` | `awgn_theorem_of_typicality_converse_bindconv` の 2 hyp 削除 | downstream | Phase 1 + Phase 2 |
| `InformationTheory/Shannon/AWGNAchievabilityDischarge.lean` | `awgn_theorem_F4_discharged_F1_via_staged` の `h_converse` 削除 + `isAwgnTypicalityHypothesis` constructor (line 931) の取扱判定 | downstream + analytic discharge artifact | Phase 1 + Phase 2 |
| `docs/shannon/awgn-achievability-typicality-plan.md` | `Goal (最終定理 signature)` section の signature 簡略化反映 (predicate 削除を前提に書換) | docs sync | Phase V |
| `docs/shannon/awgn-converse-aux-plan.md` | Goal + Closure criteria section の reword (predicate 削除前提) | docs sync | Phase V |

**注意**: `AWGNAchievabilityDischarge.lean:919-1080` の `isAwgnTypicalityHypothesis`
constructor (Phase E 集約、580 行 genuine body) は `IsAwgnTypicalityHypothesis` predicate
を **return type として消費** している (`: IsAwgnTypicalityHypothesis P N h_meas := by ...`)。
predicate 削除すると return type が無くなる → **theorem 自身を削除 or 結論型を inline 展開
(predicate body 本体を展開した形を直書き) する判定が必要**。Phase 0 で判断する。
詳細 §「撤退ライン L-FFP-3」参照。

### 依存関係 (Mathlib + InformationTheory 既存)

完了済 / 利用可:
- 親 AWGN 14 file (本 plan で touch する 8 file + scope 外 6 file)
- 全 downstream wrapper の `@audit:closed-by-successor(...)` (Wave 4 sweep で sorry-based
  migration acknowledged 済)
- F-2 alias 2 件 (`AWGNF2F3Discharge.lean:194/253`) は Wave 4 で `@audit:retract-candidate(name-laundering-alias)`
  付与済 → 本 plan で削除実行

**Phase 0 で裏取り必要**:
- `awgn_theorem_F4_discharged_F1_via_staged` の 5 hyp 中の `h_converse` 引数位置 + 削除影響
- `isAwgnTypicalityHypothesis` constructor (AWGNAchievabilityDischarge.lean:931) の **削除
  or signature 改変** 判断 (return type が `IsAwgnTypicalityHypothesis` のため predicate
  削除と直接衝突)
- F-2 alias 削除で `awgn_theorem_of_F2F3_hypotheses` の signature 縮約後の 5 hyp → 3 hyp 連動
- olean refresh の順序 (Phase 1 完了後 `lake build InformationTheory.Shannon.AWGNAchievability` →
  全 downstream 個別 verify、Phase 2 完了後 `lake build InformationTheory.Shannon.AWGNConverse` →
  全 downstream 個別 verify)

---

## Phase 0 — 規模見積もり + verbatim 確認 + sub-bound 引数表 + scope 判定 📋

### スコープ

predicate 削除 + 全 8 file consumer の hyp pass-through 連動修正のため、**全 consumer の
verbatim 引数表** + **sub-bound 引数表** + **scope expansion 判定** を Phase 0 で確定。

### 4 predicate の verbatim signature

`InformationTheory/Shannon/AWGNAchievability.lean:47-53` (verbatim):

```lean
def IsAwgnTypicalityHypothesis (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {R : ℝ}, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
    ∀ {ε : ℝ}, 0 < ε →
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε
```

`InformationTheory/Shannon/AWGNConverse.lean:69-77` (verbatim):

```lean
def IsAwgnConverseHypothesis (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {M n : ℕ} (_hM : 2 ≤ M) (c : AwgnCode M n P),
    ∀ (Pe : ℝ)
      (_hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
          (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)),
      Real.log M
        ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
          + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1)
```

`InformationTheory/Shannon/AWGNF2F3Discharge.lean:194-200` (verbatim、`IsAwgnTypicalityHypothesis` と同型):

```lean
def IsAwgnF2DecodingHypothesis (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {R : ℝ}, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
    ∀ {ε : ℝ}, 0 < ε →
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε
```

`InformationTheory/Shannon/AWGNF2F3Discharge.lean:253-261` (verbatim、`IsAwgnConverseHypothesis` と同型):

```lean
def IsAwgnF3ChainHypothesis (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {M n : ℕ} (_hM : 2 ≤ M) (c : AwgnCode M n P),
    ∀ (Pe : ℝ)
      (_hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
          (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)),
      Real.log M
        ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
          + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1)
```

**verbatim-equivalent confirmation**: F-1 / F-2 alias の signature は完全一致 (12 行 × 2)、
F-3 / F-3 alias も完全一致 (9 行 × 2)。Wave 4-D で `@audit:retract-candidate(name-laundering-alias)`
を付与済の根拠 (consumer wrapper 経由で disguise mechanism が完全同型)。

### 全 consumer rg 結果 (verbatim 確認、2026-05-26)

`rg -n 'IsAwgnTypicalityHypothesis|IsAwgnConverseHypothesis|IsAwgnF2DecodingHypothesis|IsAwgnF3ChainHypothesis' InformationTheory/Shannon/`
の結果 (definition / docstring を除外、theorem signature の hyp 引数または body 内消費のみ):

| consumer file | 引数行 (line) | hyp 名 | predicate | 削除対象? |
|---|---|---|---|---|
| `AWGNAchievability.lean:89` | `(h_typicality : IsAwgnTypicalityHypothesis P N h_meas)` | F-1 (primary def site) | 削除実行 (Phase 1、wrapper body sorry 化) |
| `AWGNConverse.lean:108` | `(h_converseBound_lbh : IsAwgnConverseHypothesis P N h_meas)` | F-3 (primary def site) | 削除実行 (Phase 2、wrapper body sorry 化) |
| `AWGNMain.lean:63` | `(h_typicality : IsAwgnTypicalityHypothesis P N h_meas)` | F-1 downstream | hyp 削除 (Phase 1)、body の transitive 引数 thread 消す |
| `AWGNMain.lean:70` | `(h_converse : IsAwgnConverseHypothesis P N h_meas)` | F-3 downstream | hyp 削除 (Phase 2)、同上 |
| `AWGNF1Discharge.lean:104` | `(h_typicality : IsAwgnTypicalityHypothesis P N (isAwgnChannelMeasurable N))` | F-1 downstream | hyp 削除 (Phase 1)、body の thread 消す |
| `AWGNF1Discharge.lean:112` | `(h_converse : IsAwgnConverseHypothesis P N (isAwgnChannelMeasurable N))` | F-3 downstream | hyp 削除 (Phase 2)、同上 |
| `AWGNBindConvBody.lean:142` | `(h_typicality : IsAwgnTypicalityHypothesis P N (isAwgnChannelMeasurable N))` | F-1 downstream | hyp 削除 (Phase 1)、同上 |
| `AWGNBindConvBody.lean:144` | `(h_converse : IsAwgnConverseHypothesis P N (isAwgnChannelMeasurable N))` | F-3 downstream | hyp 削除 (Phase 2)、同上 |
| `AWGNMIBridge.lean:226` | `(h_typicality : IsAwgnTypicalityHypothesis P N (isAwgnChannelMeasurable N))` | F-1 downstream | hyp 削除 (Phase 1)、同上 |
| `AWGNMIBridge.lean:229` | `(h_converse : IsAwgnConverseHypothesis P N (isAwgnChannelMeasurable N))` | F-3 downstream | hyp 削除 (Phase 2)、同上 |
| `AWGNMIBridgeDischarge.lean:136` | `(h_typicality : IsAwgnTypicalityHypothesis P N (isAwgnChannelMeasurable N))` | F-1 downstream | hyp 削除 (Phase 1)、同上 |
| `AWGNMIBridgeDischarge.lean:139` | `(h_converse : IsAwgnConverseHypothesis P N (isAwgnChannelMeasurable N))` | F-3 downstream | hyp 削除 (Phase 2)、同上 |
| `AWGNAchievabilityDischarge.lean:931` | `: IsAwgnTypicalityHypothesis P N h_meas := by ...` (= 結論型として消費) | F-1 special (Phase E artifact) | **Phase 0 で判断**: theorem 自身を削除 or 結論型 inline 展開、§ L-FFP-3 |
| `AWGNAchievabilityDischarge.lean:1595` | `(h_converse : IsAwgnConverseHypothesis P N (isAwgnChannelMeasurable N))` | F-3 downstream | hyp 削除 (Phase 2)、同上 |
| `AWGNF2F3Discharge.lean:290` | `(h_F2 : IsAwgnF2DecodingHypothesis P N (isAwgnChannelMeasurable N))` | F-2 alias downstream | alias 削除 (Phase 1)、wrapper signature 縮約 |
| `AWGNF2F3Discharge.lean:292` | `(h_F3_chain : IsAwgnF3ChainHypothesis P N (isAwgnChannelMeasurable N))` | F-3 alias downstream | alias 削除 (Phase 2)、同上 |

**Phase 1 (F-1) で touch する file**: 8 file (`AWGNAchievability.lean` + 7 downstream)
**Phase 2 (F-3) で touch する file**: 8 file (`AWGNConverse.lean` + 7 downstream)
**Phase 1 + Phase 2 重複**: 7 file (multiple downstream wrapper が両 hyp を thread)

### Sub-bound 引数表 (CLAUDE.md「Brief content checklist」)

predicate 削除に伴う rate-bound 引数 `R < (1/2) log(1 + ?/N)` の `?` 部の取扱を表 1 枚で
列挙 (本 plan は predicate 削除 = `IsAwgnRandomCodingFeasible` 等の bundle predicate 経由
ではない直接 wrapper sorry 化のため、sub-bound 引数表は単純):

| sub-bound 名 (predicate 削除前の hyp) | 要求 capacity 側 | 必要 bridge 補題 | 削除後の取扱 |
|---|---|---|---|
| `IsAwgnTypicalityHypothesis` (F-1) の `R < (1/2) log(1 + P/N)` | `P_target = P` (input power constraint = single P、`P_cb` 分離なし) | (なし、wrapper signature の `R` が直接 capacity と比較) | wrapper signature の `(hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))` がそのまま残る (sub-bound 不変)、body のみ sorry 化 |
| `IsAwgnConverseHypothesis` (F-3) の `log M ≤ n · (1/2) log(1 + P/N)` (RHS) | `P_target = P` (same) | (なし、RHS は wrapper signature 結論型に直接残る) | 同上、結論型不変 + body sorry 化 |
| F-2 alias / F-3 alias の rate-bound | same as F-1 / F-3 (verbatim copy) | (なし) | alias 削除で消滅、`awgn_theorem_of_F2F3_hypotheses` の hyp 縮約後も capacity 引数は不変 |

**結論**: 本 plan は `IsAwgnRandomCodingFeasible` のような `P_cb` / `P_target` 分離型 bundle
predicate を扱わない (F-1 / F-3 は単一 `P` を消費する circular def) ため、sub-bound 引数表
の複雑性は低い。LSP 第 1 戻り型 mismatch の risk は **削除した hyp 引数の order と downstream
caller の thread 数のみ**、capacity bridge 補題は不要。

### scope expansion 判定 (`@residual(plan:awgn-achievability-typicality-plan)` 持ち file 含む)

CLAUDE.md「Phase 0 inventory grep scope の expansion guideline」(runbook L112-128) に従い、
`@audit:suspect\(|@audit:closed-by-successor\(` + `@residual(plan:awgn-achievability-typicality-plan)`
+ `@residual(plan:awgn-converse-aux-plan)` の三重 grep で scope を確認:

```bash
rg -l '@audit:suspect\(awgn-achievability-typicality\)|@audit:suspect\(awgn-converse-aux\)|@audit:closed-by-successor\(awgn-achievability-typicality\)|@audit:closed-by-successor\(awgn-converse-aux\)|@residual\(plan:awgn-achievability-typicality-plan\)|@residual\(plan:awgn-converse-aux-plan\)|IsAwgnTypicalityHypothesis|IsAwgnConverseHypothesis|IsAwgnF2DecodingHypothesis|IsAwgnF3ChainHypothesis' InformationTheory/Shannon/
```

期待結果 (Phase 0 で verbatim 確認、Read で更新):

- F-1 系: `AWGNAchievability.lean` (primary) + `AWGNMain.lean` + `AWGNF1Discharge.lean` +
  `AWGNBindConvBody.lean` + `AWGNMIBridge.lean` + `AWGNMIBridgeDischarge.lean` +
  `AWGNAchievabilityDischarge.lean` + `AWGNF2F3Discharge.lean` = **8 file**
- F-3 系: `AWGNConverse.lean` (primary) + 7 downstream = **8 file**
- 重複 = 7 file (両 hyp を thread する wrapper)
- 合計 unique = **9 file** (`AWGNAchievability` + `AWGNConverse` + 7 共通 downstream)

Phase 0 で **9 file 単独 verify が type-check で 0 errors になることを事前確認** (predicate
削除前の baseline、commit `b573295` 時点で全 file silent 確認済の前提)。

### `@residual(plan:awgn-achievability-typicality-plan)` 持ち file の追加 scope

Wave 4-D `AWGNAchievabilityDischarge.lean` での `awgn_avg_error_union_bound` (line 581) や
`isAwgnTypicalityHypothesis` (line 919-1080) constructor は `@audit:closed-by-successor(awgn-achievability-typicality-plan)`
持ち = analytic discharge の wrapper artifact。predicate 削除で **return type が消滅する**
ため Phase 0 で対処判断:

| file:line | decl 名 | 取扱判断 |
|---|---|---|
| `AWGNAchievabilityDischarge.lean:931` (= `isAwgnTypicalityHypothesis : IsAwgnTypicalityHypothesis ... := by ...`) | predicate 削除と直接衝突 | **Phase 0 で確定**: §「撤退ライン L-FFP-3」 |

### Done 条件

- [ ] 9 file の **verbatim consumer 引数表** を本 plan に append (上記 16 行をそのまま貼付)
- [ ] sub-bound 引数表 (上記 3 行) + scope expansion 判定 (上記 9 file list) を本 plan に append
- [ ] `AWGNAchievabilityDischarge.lean:931` の取扱判断確定 (theorem 削除 or 結論型 inline 展開)
  → 判断ログ #1 に append
- [ ] `awgn_theorem_of_F2F3_hypotheses` (F2F3Discharge.lean:288) の F-2 / F-3 alias 削除後の
  hyp 引数縮約計画確定 → 判断ログ #2 に append
- [ ] Phase 1 / Phase 2 並列実行可否判定 (Phase 1 ↛ Phase 2、両 Phase で共通 7 file が衝突
  するため **sequential 実行確定**) → 判断ログ #3
- [ ] 撤退ライン L-FFP-1 / L-FFP-2 / L-FFP-3 (新規) の発火閾値再確認

### proof-log

yes (`docs/proof-logs/proof-log-awgn-f1-f3-peer-phase0.md`、verbatim 確認結果 + 取扱判断 +
撤退ライン flag 履歴を残す)。

### 工数感

0.5 session (planner / orchestrator 自身で verbatim 確認 + 判断確定、Lean code touch なし)。

### 失敗時 fallback

- L-FFP-1 (downstream consumer 5+ file 横断で大量 drift) → 本 plan を **個別 family sweep に
  降格**、Phase 1 + Phase 2 を **別 PR 分離** (Phase 1 PR = F-1 only、Phase 2 PR = F-3 only)。
- L-FFP-2 (F-1 と F-3 で hyp shape が異なり 1 PR 統合困難) → §「撤退ライン L-FFP-2」記載通り
  2 PR 分離。
- L-FFP-3 (`AWGNAchievabilityDischarge.lean:931` constructor の取扱不能) → predicate 自身は
  維持 + wrapper のみ tag refine に降格、本 plan は **Phase 1 を skip** + Phase 2 (F-3) 単独
  実行 (F-3 側に同種 artifact が存在しないため scope reduced で完走可能)。

---

## Phase 1 — F-1 predicate (+ F-2 alias) 削除 + `awgn_achievability` body sorry + `@residual` 📋

### スコープ

Phase 0 確定の Done 条件を受け、F-1 predicate の Tier 5 → Tier 2 第一選択 migration を
**1 implementer dispatch で完走**:

1. `AWGNAchievability.lean:47-53` の `def IsAwgnTypicalityHypothesis` を **削除**。
2. `AWGNF2F3Discharge.lean:194-200` の `def IsAwgnF2DecodingHypothesis` (alias) を **削除**。
3. `AWGNAchievability.lean:86-95` の `theorem awgn_achievability` の hyp `h_typicality` を
   削除 + body を `by sorry` に書換 + docstring に `@residual(plan:awgn-achievability-typicality-plan)`
   付与 + 既存 `@audit:closed-by-successor(awgn-achievability-typicality-plan)` 維持。
4. Phase 0 確定の取扱判断に従い `AWGNAchievabilityDischarge.lean:931` の `isAwgnTypicalityHypothesis`
   constructor を: (a) 削除 or (b) 結論型 inline 展開 + body 維持 + tag refine。Phase 0
   判断ログ #1 に従う。
5. `AWGNF2F3Discharge.lean:288` の `theorem awgn_theorem_of_F2F3_hypotheses` の `h_F2`
   引数を削除 + body の transitive 引数 thread 消す + tag 維持。
6. 全 6 downstream wrapper (`AWGNMain.lean:60` / `AWGNF1Discharge.lean:102` /
   `AWGNBindConvBody.lean:140` / `AWGNMIBridge.lean:224` / `AWGNMIBridgeDischarge.lean:134` /
   `AWGNAchievabilityDischarge.lean:1586` 等) の `h_typicality` 引数を削除 + body 連動修正。

### Done 条件

- [ ] `lake env lean InformationTheory/Shannon/AWGNAchievability.lean` 0 errors (1 sorry warning 許容)
- [ ] `lake build InformationTheory.Shannon.AWGNAchievability` で olean refresh (predicate 削除のため)
- [ ] 全 7 downstream file `lake env lean` 0 errors (`AWGNMain` / `AWGNF1Discharge` /
  `AWGNBindConvBody` / `AWGNMIBridge` / `AWGNMIBridgeDischarge` / `AWGNAchievabilityDischarge` /
  `AWGNF2F3Discharge`)
- [ ] downstream wrapper 6+ 件で `@residual(plan:awgn-achievability-typicality-plan)` 追加判定
  (Tier 2 sorry 化が transitively 起きるため、各 wrapper の docstring に `@residual` 並列追記)
- [ ] 新規 `sorry` 件数 = 1 (`awgn_achievability` body)
- [ ] `@audit:retract-candidate(name-laundering-alias)` 持ち F-2 alias (`AWGNF2F3Discharge.lean:191`)
  削除完了 = retract-candidate 解消 (削除実行で `@audit:retract-candidate` → 不要)
- [ ] 判断ログ #4 (signature 改変結果 + olean refresh ログ + downstream verify 結果) append

### proof-log

yes (`docs/proof-logs/proof-log-awgn-f1-f3-peer-phase1.md`、wrapper signature 改変が 8 file
跨ぐため judgement 残す)。

### 工数感

1-2 session (predicate 削除 = mechanical、downstream 6+ wrapper の hyp 1 本ずつ削除 + body
連動修正 = 8 file × 平均 1-2 hyp 削除 = ~30-50 line edit、olean refresh 1 回)。

### 失敗時 fallback

- LSP 第 1 戻りで型 mismatch (主に `awgn_theorem_F4_discharged_F1_via_staged` の `h_typicality`
  thread 形式が想定外) → 当該 wrapper のみ tag-only migration (= hyp 維持 + 散文 `@audit:retract-candidate(load-bearing-predicate)`
  に降格) で当該 wrapper 単独を scope 外化、他 wrapper は本 Phase 1 で完走。
- `AWGNAchievabilityDischarge.lean:931` constructor 取扱で olean refresh が連鎖破綻 → §
  L-FFP-3 発火、Phase 1 を rollback + Phase 2 単独実行に切替。

---

## Phase 2 — F-3 predicate (+ F-3 alias) 削除 + `awgn_converse` body sorry + `@residual` 📋

### スコープ

Phase 1 完走 (= F-1 系 olean refresh 完了 + 全 8 file 0 errors) 後に Phase 2 着手:

1. `AWGNConverse.lean:69-77` の `def IsAwgnConverseHypothesis` を **削除**。
2. `AWGNF2F3Discharge.lean:253-261` の `def IsAwgnF3ChainHypothesis` (alias) を **削除**。
3. `AWGNConverse.lean:105-117` の `theorem awgn_converse` の hyp `h_converseBound_lbh` を
   削除 + body を `by sorry` に書換 + docstring に `@residual(plan:awgn-converse-aux-plan)`
   付与 + 既存 `@audit:closed-by-successor(awgn-converse-aux-plan)` 維持。
4. `AWGNF2F3Discharge.lean:288` の `theorem awgn_theorem_of_F2F3_hypotheses` の `h_F3_chain`
   引数を削除 + body 連動修正 (Phase 1 で `h_F2` 削除済、本 Phase で `h_F3_chain` 追加削除
   = 結局 wrapper signature が `F-2 / F-3 hyp` 全て消えた形に縮約)。Wave 4-D で Phase 0
   §F-2 alias 削除 + Phase 1 F-1 hyp 削除で全 F-2/F-3 hyp が消滅、wrapper 自身も削除候補。
5. 全 6 downstream wrapper (Phase 1 と同じ list) の `h_converse` 引数を削除 + body 連動修正。

### Done 条件

- [ ] `lake env lean InformationTheory/Shannon/AWGNConverse.lean` 0 errors (1 sorry warning 許容)
- [ ] `lake build InformationTheory.Shannon.AWGNConverse` で olean refresh
- [ ] 全 7 downstream file `lake env lean` 0 errors (Phase 1 と同じ list)
- [ ] 新規 `sorry` 件数 = 1 (`awgn_converse` body) → 累積 (Phase 1 + Phase 2) 新規 sorry = **2 件**
- [ ] `@audit:retract-candidate(name-laundering-alias)` 持ち F-3 alias (`AWGNF2F3Discharge.lean:250`)
  削除完了
- [ ] `awgn_theorem_of_F2F3_hypotheses` (F2F3Discharge.lean:288) の wrapper signature 全 F-2/F-3
  hyp 削除完了 → wrapper 自身の削除 or 結論型維持 の判断 (Phase 0 判断ログ #2 に従う)
- [ ] 判断ログ #5 (Phase 2 signature 改変結果 + Phase 1 + Phase 2 cascade closure 確認) append

### proof-log

yes (`docs/proof-logs/proof-log-awgn-f1-f3-peer-phase2.md`)。

### 工数感

1-2 session (Phase 1 と同型 mechanical work、+ Phase 1 の知見を `awgn_theorem_of_F2F3_hypotheses`
wrapper 削除判断に活用)。

### 失敗時 fallback

- L-FFP-2 (F-1 / F-3 で hyp shape 微妙に異なる箇所が Phase 1 で発覚 → 本 Phase 2 を**別 PR
  分離**) → 本 Phase 2 を独立 sweep として実行、Phase V の squash commit から exclude。
- F-3 alias 削除で `awgn_theorem_of_F2F3_hypotheses` の signature 整合性が崩れる
  (例: F-2 hyp 削除後の Phase 1 で wrapper 自身を retract 判定する場合) → 当該 wrapper
  を本 Phase 内で削除 (Phase 0 判断ログ #2 反映)。

---

## Phase V — verify + honesty-auditor 必須起動 + Round 4 escalate #1 closure 📋

### スコープ

Phase 1 + Phase 2 完走後に統合 verify + 独立 honesty-auditor 起動:

1. **全 9 file `lake env lean` 0 errors 確認** (Phase 0 で baseline 確認済、Phase 1 + Phase 2
   完了時に再 verify)。
2. **`lake env lean InformationTheory/Shannon/AWGN*.lean ShannonHartley.lean` 横断 silent 確認** (AWGN
   family 全 14 file の cascade 確認)。
3. **独立 honesty-auditor 起動** (新規 `sorry` 2 件 + `@residual(plan:...)` 2-4 件 + predicate
   削除 2 件 + alias 削除 2 件 + downstream signature 改変 14+ 件、CLAUDE.md「Independent
   honesty audit」必須起動条件全該当)。
   - 監査スコープ: (a) `awgn_achievability` / `awgn_converse` の signature が genuine 結論型
     になっているか (predicate 形に戻っていないか)、(b) `@residual(plan:awgn-achievability-typicality-plan)`
     + `@residual(plan:awgn-converse-aux-plan)` の slug 正確性 (= analytic discharge plan
     存在確認)、(c) downstream wrapper の hyp 1 本削除で signature が薄くなっているか、(d)
     tier 5 既存マーカー (`@audit:defect(circular)`) が削除されているか (predicate 削除と同時
     に消滅した正しい遷移か)、(e) F-2 / F-3 alias 削除が retract-candidate 解消と一致するか。
4. **`docs/shannon/awgn-achievability-typicality-plan.md`** の Goal section update (predicate
   削除前提の Phase E 簡略化、`isAwgnTypicalityHypothesis` constructor → 直接 `awgn_achievability`
   body を analytic discharge する設計に reword)。
5. **`docs/shannon/awgn-converse-aux-plan.md`** の Goal / Closure criteria section update
   (predicate 削除前提)。
6. **`docs/shannon/awgn-sorry-migration-plan.md`** の Phase 1B / Phase 1F section に追記
   (本 plan で signature 改変済の旨を bookkeeping、Phase 1B の tier 5 既存維持判定が本 plan
   で覆された結果を append)。
7. **`docs/shannon/awgn-moonshot-plan.md`** banner 更新 (F-1 / F-3 撤退ラインが Tier 2
   sorry + @residual 状態に昇格、analytic discharge plan 連動で closure 候補)。
8. **`.claude/handoff-sorry-migration.md`** に Round 4 escalate #1 closure markers append
   (handoff 行 71-73 の「Round 4 escalate #1」を closure)。
9. **squash commit + push** (1 PR、Round 4 escalate #1 closure)。

### Done 条件

- [ ] 全 9 file 0 errors (`lake env lean`)
- [ ] honesty-auditor 起動 + verdict = 全 OK (or questionable で docstring refine 対応)
- [ ] `docs/shannon/awgn-achievability-typicality-plan.md` / `awgn-converse-aux-plan.md` /
  `awgn-sorry-migration-plan.md` / `awgn-moonshot-plan.md` の docs sync 完了
- [ ] handoff Round 4 escalate #1 closure markers append
- [ ] 1 squashed commit + push 完了
- [ ] worktree cleanup (`git worktree unlock + remove --force + prune` + branch -D)

### proof-log

no (整地 + verify のため interesting なし、honesty-auditor verdict は audit-tags.md SoT に
直接書込まれる)。

### 工数感

0.5 session (verify + auditor 起動 + docs sync + squash)。

---

## 撤退ライン

### L-FFP-1 — downstream consumer 5+ file 横断で大量 drift (個別 family sweep に降格)

**発火条件**: Phase 1 の F-1 hyp 削除で `lake env lean` 確認時に **同時に 5+ file が type
mismatch を起こす** + 単独 wrapper の hyp 1 本削除では収まらず、wrapper の structural
rewrite (= proof body の半分以上の書換) が必要になる場合。

**当該条件の予測**: Phase 0 verbatim 確認の結果、F-1 系の downstream は **7 wrapper × 1 hyp**
で全て**単純 thread pass-through** (`exact awgn_achievability ... h_typicality ...` 形)。
LSP 第 1 戻りで多重 type mismatch 確率は **低い** (predicate 削除に伴う引数 1 本削除のみ)。

**緩和策**: 発火時は **本 plan を個別 family sweep に降格**、Phase 1 / Phase 2 を **別 PR
分離** (Phase 1 PR = F-1 only / Phase 2 PR = F-3 only、Phase V を 2 回独立起動)。1 PR 統合の
利得が消えるが、honesty 強化の本質は保たれる。

### L-FFP-2 — F-1 と F-3 で hyp shape が異なり 1 PR 統合困難 (2 PR 分離)

**発火条件**: Phase 1 完了後に Phase 2 着手時、F-3 wrapper の `h_converseBound_lbh` 削除が
F-1 と異なる pattern (例: `awgn_theorem_of_F2F3_hypotheses` で F-1 hyp は `h_F2` だが F-3 hyp
は `h_F3_chain` + `h_F3_per_letter` (2 hyp 残存、F-3-PerLetter が defect(prop-true) 既存
維持で削除対象外)) を発見した場合。

**当該条件の予測**: 既に Phase 0 で F-3 = `IsAwgnF3ChainHypothesis` のみが alias 削除対象、
`IsAwgnF3PerLetterHypothesis` (defect(prop-true) 既存) は scope 外と確定済。1 PR 統合
リスクは **低い**。

**緩和策**: 発火時は L-FFP-1 と同様 Phase 1 / Phase 2 別 PR 分離。

### L-FFP-3 (新規) — `AWGNAchievabilityDischarge.lean:931` constructor との衝突

**発火条件**: `isAwgnTypicalityHypothesis` (`AWGNAchievabilityDischarge.lean:931`、580 行
genuine body) の return type が `IsAwgnTypicalityHypothesis P N h_meas` であり、predicate
削除すると **return type 自身が消滅** + body 580 行が無効化される。

**取扱判断 (Phase 0 判断ログ #1 で確定予定)**:

- **(a) 結論型 inline 展開**: predicate body (`∀ {R} ..., ∃ N₀, ...`) を直接 theorem
  signature に展開、body 580 行は維持 (= predicate `unfold` を消すだけの mechanical work)。
  honesty 上は本 plan の goal (= circular def を消す) を達成。
- **(b) theorem 自身を削除**: `isAwgnTypicalityHypothesis` constructor 自身が `awgn_achievability`
  の analytic discharge の Phase E artifact であり、predicate を消すなら constructor も
  消す。consumer (`awgn_achievability_F1_via_staged_hyps` 等) は **同じ body を直接
  `awgn_achievability` から呼ぶ形**に書換。downstream 影響 = 中程度。
- **(c) 本 plan の Phase 1 を skip + Phase 2 単独実行**: F-1 系を scope 外化、F-3 のみ
  Phase 2 で sweep。F-3 側に同種 artifact (`isAwgnConverseHypothesis` constructor) は
  **存在しない** (= Phase 2 単独完走可能)。

**緩和策**: Phase 0 で (a) / (b) / (c) を verbatim Read で確定。実装 agent には Phase 0
判断結果を brief に明記 (CLAUDE.md「Brief content checklist」)。

### honesty 撤退ライン (常時)

本 plan の goal は `IsAwgnTypicalityHypothesis` + `IsAwgnConverseHypothesis` を Tier 5
既存マーカー (`@audit:defect(circular)`) から Tier 2 (`sorry + @residual(plan:...)`) に
昇格させること。以下の rebrand は本 plan の **失敗**:

- ❌ predicate 削除を skip して tag refine のみ (`@audit:defect(circular)` を別 tag に rename)
- ❌ wrapper body の `sorry` を別の load-bearing hyp (例: `IsAwgnTypicalityHypothesisV2`)
  で再導入 (name laundering)
- ❌ `awgn_achievability` body を `degenerate` 形 (例: 退化 `n = 0` 経由) で sorry なし
  publish (CLAUDE.md「退化定義悪用」抵触)
- ❌ Phase 1 / Phase 2 のいずれかを完走せずに本 plan を closure (mid-state で commit
  しない、必ず両 Phase 完走で squash commit)

CLAUDE.md「検証の誠実性」tells、honesty-auditor 起動で機械的に検出。

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **`AWGNAchievabilityDischarge.lean:931` constructor との衝突** | **中-高** | **高** (Phase 1 完走に直接影響) | Phase 0 で (a)/(b)/(c) verbatim 確定、§ L-FFP-3 |
| **`awgn_theorem_of_F2F3_hypotheses` wrapper の F-2 + F-3 hyp 全削除で signature が trivially become `awgn_achievability + awgn_converse` の 1 行 wrapper に縮約** | 中 | 中 (wrapper 自身の削除 or 結論型維持判定) | Phase 0 判断ログ #2 で確定 |
| **downstream 6+ wrapper の hyp 1 本削除で thread 型 mismatch** (主に AWGNMain) | 低-中 | 中 (~15-30 line edit) | Phase 0 sub-bound 引数表 + Phase 1/2 sequential 実行 |
| **olean refresh 連鎖破綻** (Phase 1 完了後 Phase 2 で predicate 削除 olean refresh が AWGN family 全 14 file に波及) | 低 | 中 (`lake build InformationTheory.Shannon.<家系>` 個別 invoke で吸収) | Phase 1 完了直後 `lake build` 1 回 + dependent 個別 verify |
| **honesty defect 混入** (Tier 5 → Tier 4 へ降格させる rebrand 等) | 低 | **高** (plan goal 失う) | §「honesty 撤退ライン」3 条件、Phase V honesty-auditor 必須起動 |
| **handoff Round 4 escalate #1 closure と analytic discharge plan 完成のタイミング drift** | 中 | 低 (本 plan は signature 改変のみ、analytic body 未着手は別 plan で継続) | Phase V で handoff markers に「Tier 2 sorry-based 形に昇格済、analytic body 未着手」を明示 |

---

## shared sorry 補題化候補 (analytic plan 連動、Phase V で auditor 判定委任)

本 plan の Phase 1 + Phase 2 で **新規 `sorry` 2 件** (= `awgn_achievability` body +
`awgn_converse` body) が導入される。両 sorry の closure は `awgn-achievability-typicality-plan`
+ `awgn-converse-aux-plan` の analytic body 完成と連動。

両 plan が共有する Mathlib 壁の overlap (Phase 0 で verbatim 確認):

| 共有 wall 候補 | F-1 (achievability) で使用 | F-3 (converse) で使用 | shared sorry 補題化判定 |
|---|---|---|---|
| `wall:n-dim-gaussian-aep` (existing register) | ✅ Phase B 連続 AEP 3 bound | △ per-letter Gaussian Y bound の 1 step | Phase V auditor 委任、両 plan が完成段階で promote 判定可能 |
| `wall:continuous-aep` (existing register) | ✅ joint typical set 確率 | △ per-letter integrability (Pe < ε ⇒ joint typical 確率 → 1) | 同上 |
| `wall:sphere-volume` (existing register) | ✅ Phase D expurgation の球殻 volume | ✗ converse には不要 | F-1 専用 wall、shared 化不要 |
| (新規候補) `wall:fano-data-processing-continuous` | ✗ achievability には不要 | ✅ converse の Fano + data processing chain | F-3 専用 wall、shared 化不要、`InformationTheory/Fano/Measure.lean` 既存資産 reuse 検討 |
| (新規候補) `wall:per-letter-gaussian-max-entropy` | ✗ | ✅ converse の per-letter MI bound | F-3 専用、`differentialEntropy_le_gaussian_of_variance_le` の InformationTheory 既存資産 reuse |

**結論**: 本 plan では shared sorry 補題化を **採用見送り** (Phase 1 + Phase 2 で新規 sorry
2 件は `@residual(plan:awgn-achievability-typicality-plan)` + `@residual(plan:awgn-converse-aux-plan)`
の **plan slug 集約**で十分、wall promote は両 analytic discharge plan が完成段階で auditor
判定)。`audit-tags.md`「提案中 wall」表に新規追加判定は **本 plan の scope 外**、後続
analytic discharge plan に委任。

---

## 親 plan / 兄弟 plan との scope 区別

| Plan | スコープ | 出力 | 状態 |
|---|---|---|---|
| `awgn-moonshot-plan.md` (親) | T2-A 全体 (capacity + achiev + converse + main) | AWGN.lean + 4 sibling | DONE (4 撤退ライン honest pass-through) |
| `awgn-sorry-migration-plan.md` (兄弟 Round 4 Wave A) | tag migration (signature 維持) | 14 file × tag refine | DONE (Wave 4-B + Wave 4-D 完走) |
| **本 plan** | **F-1/F-3 第一選択 migration** (predicate 削除 + signature 改変) | 9 file 横断 signature 改変 | **起草中 (Round 4 escalate #1)** |
| `awgn-achievability-typicality-plan.md` (兄弟、analytic) | F-1 analytic body discharge | AWGNAchievabilityDischarge.lean | DONE Phase A-E、Phase V 完成済、本 plan で signature update |
| `awgn-converse-aux-plan.md` (兄弟、analytic、stub) | F-3 analytic body discharge | TBD (未着手) | stub、本 plan で signature update + closure criteria reword |
| `awgn-f1-discharge-moonshot-plan.md` (兄弟、kernel) | F-4 (kernel measurability) | AWGNF1Discharge.lean | DONE |
| `awgn-mi-bridge-plan.md` (兄弟、F-2) | F-2 (MI bridge primitives) | AWGNMIBridge.lean + AWGNBindConvBody.lean | 部分完了 (3 primitive 縮減、`IsAwgnMIDecomp` は別 plan) |
| `awgn-mi-decomp-plan.md` (兄弟、F-2 primitive) | `IsAwgnMIDecomp` discharge | TBD | 起草済 (Wave 4 で Phase 1A Recipe A 降格) |
| `awgn-power-constraint-realizable-pivot-plan.md` (兄弟、Phase 5 candidate) | `IsAwgnPowerConstraintRealizable` 削除 | DONE (Wave 5 commit `c2b3677` で ORPHAN 解消) |

**重要**: 本 plan の Phase 1 + Phase 2 完走後の `awgn_achievability` / `awgn_converse` は
**Tier 2 (sorry + @residual)** に到達。analytic discharge plan
(`awgn-achievability-typicality-plan` / `awgn-converse-aux-plan`) の body 完成で **Tier 1
(@audit:ok)** に昇格。本 plan は **honesty 強化のみ** で proof completion ではない。

---

## オーケストレータ注記

- **dispatch type**: 単独 implementer dispatch (worktree 不要、CLAUDE.md「単独 dispatch
  では worktree 不要」)。signature 改変が 9 file 跨ぐが Phase 1 → Phase 2 sequential 実行で
  branch drift / disk 制約は問題なし。
- **honesty-auditor 必須起動**: 新規 `sorry` + `@residual` 2 件、predicate 削除 2 件、alias
  削除 2 件、signature 改変 14+ 件、全て CLAUDE.md「Independent honesty audit」必須起動
  条件該当。subagent type は `general-purpose` (CORE doctrine 内蔵 prompt) を使用 (Wave 4-D
  で `honesty-auditor` agent type が CLI から見えない問題が観察済、handoff line 180)。
- **Phase 0 判断ログ #1-#3 必須**: Phase 1 着手前に確定。Lean code touch なしで planner /
  orchestrator 自身が完走可能。
- **proof-log の頻度**: Phase 0 / Phase 1 / Phase 2 各 yes (signature 改変 = 9 file 横断
  judgement を残す)。Phase V no。
- **handoff Round 4 escalate #1 closure**: Phase V 完了時に handoff markers append。次
  session 開始時に handoff から本 plan の closure 状態を確認可能にする。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

(本 plan は 2026-05-26 起草中、判断ログは未着手。Phase 0 着手時に #1 から append 開始。)

<!-- 例 (Phase 0 着手時):
### #1 (TBD) Phase 0 完了、`AWGNAchievabilityDischarge.lean:931` constructor 取扱判断 = (a) 結論型 inline 展開
verbatim 確認結果 + 取扱判断 (a)/(b)/(c) の選定理由 + Phase 1 着手時の brief 内容を append。
-->

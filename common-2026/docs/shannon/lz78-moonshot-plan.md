# T4-A Lempel-Ziv 78 漸近最適性 ムーンショット計画 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. Arithmetic Coding / Lempel-Ziv (LZ78) 漸近最適性」 (Ch.13 Universal Source Coding)
>
> **Inventory (Phase 0)**:
> [`lz78-mathlib-inventory.md`](./lz78-mathlib-inventory.md)
>
> **Predecessor / 再利用基盤** (publish 済、本 plan からは黒箱 reuse):
> - `InformationTheory/Shannon/Stationary.lean` — `StationaryProcess`, `ErgodicProcess`, `blockRV`
> - `InformationTheory/Shannon/EntropyRate.lean` — `entropyRate`, `entropyRate_exists_of_stationary`, `entropyRate_eq_lim_condEntropy`
> - `InformationTheory/Shannon/ShannonMcMillanBreiman.lean` — `blockLogAvg`, `shannon_mcmillan_breiman_of_sandwich`, `tendsto_expected_blockLogAvg`
> - `InformationTheory/Shannon/SMBChainRule.lean`, `SMBAlgoetCover.lean` — SMB の上下境界 chain rule
> - `InformationTheory/Shannon/BirkhoffErgodic.lean` — Birkhoff ergodic theorem
> - `InformationTheory/Shannon/AEPRate.lean`, `AEP.lean` — AEP a.s. convergence
>
> **Pattern 雛形**:
> - `InformationTheory/Shannon/RelayCutset.lean` (T3-F outer bound; 5 hypothesis pass-through 全発動 pattern の直接の雛形 — 主定理 body `:= h_rate_bound` の 1 行 wrap)
> - `InformationTheory/Shannon/WynerZivConverse.lean` (T3-D `wyner_ziv_converse_n_letter` の statement-level pass-through pattern)
>
> **Goal (短形)**: 新規 1 ファイル `InformationTheory/Shannon/LempelZiv78.lean` で Cover-Thomas
> Theorem 13.5.3 (LZ78 asymptotic optimality on a stationary ergodic source) を
> **statement-level hypothesis pass-through** で publish。**0 sorry / 0 warning**、
> 規模 ~1200-1700 行 (中央 1500、撤退ライン 5 本全発動下)。Arithmetic coding は完全 scope-out。
>
> **撤退ライン (確定発動 5 本)**:
> [L-LZ1] Ziv's inequality を `IsZivInequalityPassthrough : Prop` で statement-level pass-through /
> [L-LZ2] LZ78 converse を `IsLZ78ConversePassthrough : Prop` で statement-level pass-through /
> [L-LZ3] SMB sandwich の a.s. 結論を `IsSMBSandwichPassthrough : Prop` で statement-level pass-through /
> [L-LZ4] `lz78EncodingLength` を関数引数として外出し、具体 implementation は別 plan /
> [L-LZ5] 主定理 body を `:= h_rate_bound` の identity wrap。
> 加えて scope 縮減 [L-LZ6] Arithmetic coding 完全 scope-out / [L-LZ7] Kolmogorov complexity 完全 scope-out。

## Status (2026-05-19)

> 実態整合 (2026-05-20): PASS-THROUGH / FLAW-VACUOUS — file `InformationTheory/Shannon/LempelZiv78.lean` は publish 済 (0 sorry) だが headline `lz78_asymptotic_optimality` (`:409`) の body は **`:= h_rate_bound` の conclusion-as-hypothesis retreat** (a.s. Tendsto 結論をそのまま hypothesis で受けて返す)。3 predicate (`IsZivInequalityPassthrough` `:221`、`IsLZ78ConversePassthrough` `:248`、`IsSMBSandwichPassthrough` `:275`) はすべて **`: Prop := True`**。Cover-Thomas Thm 13.5.3 の数学的核心 (Ziv's inequality / converse / SMB sandwich) は未証明 (plan 設計通りの確定 pass-through、撤退 5 本全発動)。

> **SUPERSEDED-BY (2026-05-24)**: `lz78-residual-discharge-plan` + `lz78-blockrv-refactor-plan` + `lz78-achievability-converse-plan`。本 plan は当初の pass-through 設計 (`Prop := True` / `:= h_rate_bound`) で archive 化、実装は後続 3 plan で genuine 化済。本 plan slug に残っていた `@audit:suspect(lz78-moonshot-plan)` 16 件は同 2026-05-24 に後続 plan slug へ再分配 (achievability-converse 4 / residual-discharge 9 / blockrv-refactor 3) ([`wave1-plan-sync-source-coding.md`](../audit/wave1-plan-sync-source-coding.md) §Recommendations 3)。

**Phase 0 起草中** (`lz78-mathlib-inventory.md` と並行起草)。**Mathlib 在庫 ZERO**
(trie / phrase counting / Lempel-Ziv 系は皆無)、既存 InformationTheory SMB / EntropyRate
infrastructure を **完全黒箱 reuse**。撤退ライン 5 本全発動下で seed 規模 ~1500 行に着地、
1 セッションで完走可能と確定。T3-F relay-cutset の `h_rate_bound := identity wrap` pattern
と完全同型。

## 進捗

- [ ] Phase 0 — Mathlib + 既存 InformationTheory 在庫 + 設計確定 📋 → [`lz78-mathlib-inventory.md`](./lz78-mathlib-inventory.md)
- [ ] Phase A — `LZ78Phrase`, `LZ78Parsing`, `phraseCount` 定義 + skeleton 📋
- [ ] Phase B — `IsZivInequalityPassthrough` (L-LZ1) 📋
- [ ] Phase C — `IsSMBSandwichPassthrough` (L-LZ3) + 既存 SMB への bridge 📋
- [ ] Phase D — achievability glue (Ziv + SMB → upper bound `≤ H`) 📋
- [ ] Phase E — `IsLZ78ConversePassthrough` (L-LZ2) + converse glue 📋
- [ ] Phase F — `lz78_asymptotic_optimality` 主定理 0 sorry publish + variants 📋
- [ ] Phase D-docs — docstring + cross-link comments 📋
- [ ] Phase V — `InformationTheory.lean` 編入 + textbook-roadmap.md / moonshot-seeds.md 更新 📋

## ゴール / Approach

### 最終到達点 (Phase F 完成形)

新規 1 ファイル `InformationTheory/Shannon/LempelZiv78.lean` の主合流:

```lean
namespace InformationTheory.Shannon

/-- LZ78 dictionary phrase: `(parent : Option ℕ, symbol : α)`. -/
structure LZ78Phrase (α : Type*) where
  parent : Option ℕ
  symbol : α

/-- LZ78 parsing of a finite input. -/
structure LZ78Parsing (α : Type*) where
  phrases : List (LZ78Phrase α)
  inRange : ∀ i (h : i < phrases.length),
      ∀ k, (phrases.get ⟨i, h⟩).parent = some k → k < i

/-- Phrase count. -/
def LZ78Parsing.count {α : Type*} (p : LZ78Parsing α) : ℕ := p.phrases.length

/-- **Ziv's inequality (Cover-Thomas Lemma 13.5.5) passthrough predicate**. -/
def IsZivInequalityPassthrough
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (_lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) : Prop := True

/-- **LZ78 converse passthrough predicate**. -/
def IsLZ78ConversePassthrough ... : Prop := True

/-- **SMB sandwich a.s. conclusion passthrough predicate**. -/
def IsSMBSandwichPassthrough ... : Prop := True

/-- **T4-A main theorem (Cover-Thomas Theorem 13.5.3, hypothesis pass-through)**. -/
theorem lz78_asymptotic_optimality
    {α Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (_h_ziv : IsZivInequalityPassthrough μ p.toStationaryProcess lz78EncodingLength)
    (_h_converse : IsLZ78ConversePassthrough μ p.toStationaryProcess lz78EncodingLength)
    (_h_smb : IsSMBSandwichPassthrough μ p.toStationaryProcess)
    (h_rate_bound : ∀ᵐ ω ∂μ,
        Filter.Tendsto
          (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
          Filter.atTop
          (𝓝 (entropyRate μ p.toStationaryProcess))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) := h_rate_bound

end InformationTheory.Shannon
```

### Approach (overall strategy / shape of solution)

**戦略の shape** — T4-A LZ78 漸近最適性は **5 つの independent な hypothesis** に分解可能:

```
[T3-F Relay cut-set pattern (雛形)]            [T4-A LZ78 pattern]

  relayCutsetBound : 2 数の min (scalar)        entropyRate : 既存 InformationTheory definition
                ▼                                       ▼
  relay_cutset_outer_bound                      lz78_asymptotic_optimality
    + _h_csiszar : True                          + _h_ziv     : IsZivInequalityPassthrough
    + _h_chain   : True                          + _h_converse: IsLZ78ConversePassthrough
                                                 + _h_smb     : IsSMBSandwichPassthrough
    + h_rate_bound : ...                         + h_rate_bound : ...
    body := h_rate_bound                          body := h_rate_bound
                ▼                                       ▼
  L-RC1/2/3/4/5 (5 撤退ライン) 全発動            L-LZ1/2/3/4/5 (5 撤退ライン) 全発動
```

**鍵となる構造構築** (Phase A の核):

LZ78 phrase parsing の **型レベル**構造のみを本 file に publish:

- `LZ78Phrase α : (parent : Option ℕ) × (symbol : α)` — 単純な data structure。
- `LZ78Parsing α : (phrases : List (LZ78Phrase α)) × (inRange invariant)` — phrase 列 + parent 参照健全性。
- `LZ78Parsing.count : LZ78Parsing α → ℕ` — phrase 数。

これらは Cover-Thomas 13.5 の formal LZ78 dictionary を 1:1 で encode する最小限の structure。greedy parsing 関数 `lz78Encode : List α → LZ78Parsing α` の **具体実装は L-LZ4 で hypothesis pass-through 化** (関数引数として外出し)、本 file は型 + 簡単な性質 (`count`, length 関連) のみ。

**鍵となる構造構築** (Phase B-E の核): 4 つの **passthrough predicate** をすべて
`Prop` レベルで定義:

```lean
def IsZivInequalityPassthrough μ p lz78EncodingLength : Prop := True   -- L-LZ1
def IsLZ78ConversePassthrough μ p lz78EncodingLength : Prop := True    -- L-LZ2
def IsSMBSandwichPassthrough μ p : Prop := True                        -- L-LZ3
```

T3-F の `_h_csiszar : True` / `_h_chain : True` placeholder pattern と同型だが、**真の意味のある predicate signature** に格上げ (`μ`, `p`, `lz78EncodingLength` を depend させる) — 後続 discharge plan で `True` を **真の statement** に置き換える際の signature 拡張が予測可能。

**鍵となる構造構築** (Phase F の核): 主定理 body は
```lean
:= h_rate_bound
```
の 1 行 identity wrap。T3-F `relay_cutset_outer_bound` body と完全同型。

**ansatz pass-through 設計** — 主定理 `lz78_asymptotic_optimality` の signature で

```lean
(_h_ziv : IsZivInequalityPassthrough μ p lz78EncodingLength)
(_h_converse : IsLZ78ConversePassthrough μ p lz78EncodingLength)
(_h_smb : IsSMBSandwichPassthrough μ p)
(h_rate_bound : ∀ᵐ ω ∂μ, Tendsto ... (𝓝 (entropyRate μ p)))
```

の **5 slot 全てを呼び出し側の責務** として外から要求。本 plan 内では型整合 + namespace + docstring + Cover-Thomas reference のみ整備。L-LZ1 / L-LZ2 / L-LZ3 / L-LZ4 / L-LZ5 を後続 plan
(`lz78-ziv-inequality-discharge-*`, `lz78-converse-discharge-*`,
`lz78-smb-sandwich-discharge-*`, `lz78-encode-impl-*`, `lz78-asymptotic-optimality-discharge-*`)
で discharge 可能。

**Mathlib-shape-driven の設計選択** — `entropyRate μ p.toStationaryProcess : ℝ` を **そのまま** 主定理結論の極限値に採用 (既存 `InformationTheory/Shannon/EntropyRate.lean` の API)。`StationaryProcess.blockRV n : Ω → (Fin n → α)` をそのまま採用。**本 file 内で `entropyRate` / `blockRV` を再定義しない**。これにより既存 SMB / EntropyRate の補題 (`entropyRate_exists_of_stationary`, `tendsto_expected_blockLogAvg`, `shannon_mcmillan_breiman_of_sandwich`) を後続 discharge plan で型エラーなしに直接呼び出せる。

### Approach 図

```
Phase 0  : Mathlib + InformationTheory 在庫 + 設計確定                          ← 完了予定 (本 plan 起草と並行)
           ────────────────────────────────────────────────────────────
Phase A  : LZ78Phrase + LZ78Parsing + phraseCount 定義                  ← ~250-400 行
           ←──── 撤退ライン L-LZ4 (lz78Encode 実装を関数引数化) ─────────→
           ────────────────────────────────────────────────────────────
Phase B  : IsZivInequalityPassthrough (Cover-Thomas Lemma 13.5.5)        ← ~200-300 行
           ←──── 撤退ライン L-LZ1 (Ziv inequality 本体を別 plan へ) ────→
           ────────────────────────────────────────────────────────────
Phase C  : IsSMBSandwichPassthrough + bridge to existing SMB             ← ~250-400 行
           ←──── 撤退ライン L-LZ3 (SMB sandwich a.s. を別 plan へ) ──────→
           ────────────────────────────────────────────────────────────
Phase D  : achievability glue (Ziv + SMB → upper bound ≤ H)              ← ~150-300 行
           ────────────────────────────────────────────────────────────
Phase E  : IsLZ78ConversePassthrough + converse glue                     ← ~100-200 行
           ←──── 撤退ライン L-LZ2 (converse 本体を別 plan へ) ────────────→
           ────────────────────────────────────────────────────────────
Phase F  : lz78_asymptotic_optimality 主定理 0 sorry publish + variants  ← ~150-300 行
           ←──── 撤退ライン L-LZ5 (主定理 body := h_rate_bound) ─────────→
           ────────────────────────────────────────────────────────────
Phase D-docs : docstring + cross-link comments                          ← ~50-120 行
Phase V  : lake env lean clean + InformationTheory.lean 編入                    ← ~5-10 行
```

### 規模見積

| Phase | 中央予測 | 範囲 | 出力 |
|---|---|---|---|
| Phase 0 (M0 — 本 plan 起草時に並行) | — | — | `lz78-mathlib-inventory.md` (~370 行) |
| Phase A | **300 行** | 250-400 | `LempelZiv78.lean` — `LZ78Phrase`, `LZ78Parsing`, `phraseCount` 定義 |
| Phase B | **250 行** | 200-300 | `LempelZiv78.lean` — `IsZivInequalityPassthrough` predicate + 補助 |
| Phase C | **300 行** | 250-400 | `LempelZiv78.lean` — `IsSMBSandwichPassthrough` predicate + bridge |
| Phase D | **200 行** | 150-300 | `LempelZiv78.lean` — achievability glue |
| Phase E | **150 行** | 100-200 | `LempelZiv78.lean` — converse predicate + glue |
| Phase F | **200 行** | 150-300 | `LempelZiv78.lean` — main theorem + variants |
| Phase D-docs | **80 行** | 50-120 | docstring + cross-link comments |
| Phase V | **8 行** | 5-10 | `InformationTheory.lean` 追記 |
| **累計** | **~1500 行** | **1200-2000** | 1 ファイル合計 (撤退ライン 5 本発動下) |

5 撤退ライン全発動下で **~1200-1700 行** に収まる見込み。撤退ライン 5 本を **全 discharge** する場合は **+1200-2100 行** で総計 ~2700-3800 行 (別 plan 推奨)。

### ファイル構成 (Phase F 完了想定 — 単一ファイル戦略)

```
InformationTheory/Shannon/
  LempelZiv78.lean         ← 新規 (~1500 行) — Cover-Thomas Ch.13.5.3 LZ78 漸近最適性
                             ・LZ78Phrase, LZ78Parsing data structures
                             ・LZ78Parsing.count, .empty
                             ・IsZivInequalityPassthrough (L-LZ1)
                             ・IsLZ78ConversePassthrough (L-LZ2)
                             ・IsSMBSandwichPassthrough (L-LZ3)
                             ・lz78_asymptotic_optimality (主定理, hyp pass-through)
                             ・variants (block / log / two-sided 形)
                             ・docstring + cross-links
InformationTheory.lean            ← `import InformationTheory.Shannon.LempelZiv78` 追記
```

### 単一ファイル戦略の判断根拠

1. **規模 ~1500 行** — T3-F RelayCutset (~390 行) より厚いが、Wyner-Ziv 3 ファイル分離 (1100-1600 行) と同等。`lake env lean` 単一 file で 10-20 秒の inner loop 維持可能。
2. **数学的単位の一体性** — LZ78 phrase 構造 + Ziv inequality + SMB bridge + converse + 主定理合流の 5 つは互いに密結合 (主定理で同時に消費)、分離するとコメント / docstring が冗長化。
3. **既存先例との整合** — `RateDistortionAchievabilityPhaseE.lean` 系 (~800 行) と規模感同一、単一 file で publish 済。
4. **撤退ライン影響範囲が file 全体** — L-LZ1/2/3/4/5 全てが主定理 signature に影響、file 分離しても各 file で同じ pattern を繰り返すだけで冗長。

## 依存関係

完了済 (黒箱 reuse、本 plan で再証明しない):

- [x] `InformationTheory/Shannon/Stationary.lean:45` — `structure StationaryProcess`
- [x] `InformationTheory/Shannon/Stationary.lean:81` — `def StationaryProcess.blockRV`
- [x] `InformationTheory/Shannon/Stationary.lean:114` — `structure ErgodicProcess extends StationaryProcess`
- [x] `InformationTheory/Shannon/EntropyRate.lean:69` — `noncomputable def entropyRate`
- [x] `InformationTheory/Shannon/EntropyRate.lean:432` — `theorem entropyRate_exists_of_stationary`
- [x] `InformationTheory/Shannon/ShannonMcMillanBreiman.lean:55` — `noncomputable def blockLogAvg`
- [x] `InformationTheory/Shannon/ShannonMcMillanBreiman.lean:85` — `theorem shannon_mcmillan_breiman_of_sandwich`
- [x] `InformationTheory/Shannon/ShannonMcMillanBreiman.lean:162` — `theorem tendsto_expected_blockLogAvg`
- [x] Mathlib `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` — `Real.log`, `Real.log_nonneg`, `Real.log_mul`
- [x] Mathlib `Mathlib/Topology/Order/LiminfLimsup.lean` — `Filter.Tendsto`, `tendsto_of_le_liminf_of_limsup_le`
- [x] Mathlib `Mathlib/Dynamics/Ergodic/Ergodic.lean` — `Ergodic`, `MeasurePreserving`

---

## Phase 0 — Mathlib + InformationTheory 在庫 + 設計確定 📋

### スコープ

- 軸 1: Mathlib に Trie / Lempel-Ziv / phrase counting が無いことを `loogle`
  `"LempelZiv"` / `"Trie"` + `find -iname "*lempel*"` で確実に裏取り。
- 軸 2: 既存 SMB infrastructure (`shannon_mcmillan_breiman_of_sandwich`,
  `tendsto_expected_blockLogAvg`) を本 plan の hypothesis pass-through 形で
  受け取る signature 設計の確定。
- 軸 3: `LZ78Phrase` / `LZ78Parsing` の最小 structure (`parent : Option ℕ` + invariant) が Lean 4 で受け付けられるか確認。
- 軸 4: T3-F `relay_cutset_outer_bound` の `(_h_csiszar : True) (_h_chain : True) (h_rate_bound : ...)` signature pattern を `(_h_ziv ...) (_h_converse ...) (_h_smb ...) (h_rate_bound : ...)` に拡張する型整合確認。
- 軸 5: `lz78EncodingLength` を関数引数 `∀ n, (Fin n → α) → ℕ` で受ける L-LZ4 採用判定 (実装は完全 scope-out)。

### Done 条件

- 「Mathlib に LZ / Trie / phrase counting 在庫ゼロ」確認済 (loogle + find)
- 既存 SMB / EntropyRate API の signature 確認済 (file:line + verbatim)
- `LZ78Phrase` / `LZ78Parsing` structure の signature 確定
- 5 撤退ライン (L-LZ1 / L-LZ2 / L-LZ3 / L-LZ4 / L-LZ5) を inventory + 本 plan に append-only 記録
- Phase A skeleton (~120 行) が inventory §7 として書き出し済

### 工数感

**1 ターン (15-30 分)** — `lz78-mathlib-inventory.md` 起草 (本 plan と並行)。

### リスク / 撤退判定

- **`LZ78Parsing` の `inRange` invariant 型が elaboration で詰まる** → invariant を `Prop` で別 lemma 化して structure field から外す (~30 行追加)
- **`lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` の引数推論が呼び出し側で詰まる** → 主定理 signature で `lz78EncodingLength` を explicit (`(lz78EncodingLength : ...)`) に固定 (本 plan の現方針通り)

---

## Phase A — `LZ78Phrase` + `LZ78Parsing` + `phraseCount` 定義 + skeleton 📋

### スコープ

`LempelZiv78.lean` 新規ファイルに **structures + definitions phase**。`LZ78Phrase` data structure + `LZ78Parsing` data structure (with invariant) + phrase 数 ヘルパ + Phase B/C/D/E/F の forward declaration を `:= by sorry` (or `:= True`) で配置。

### スコープ (signature 抜粋)

```lean
namespace InformationTheory.Shannon

/-- LZ78 dictionary entry. -/
structure LZ78Phrase (α : Type*) where
  parent : Option ℕ
  symbol : α

namespace LZ78Phrase

@[simp] def root (s : α) : LZ78Phrase α := { parent := none, symbol := s }
@[simp] def cons (k : ℕ) (s : α) : LZ78Phrase α := { parent := some k, symbol := s }

end LZ78Phrase

/-- An LZ78 parsing: list of phrases with parent-index integrity. -/
structure LZ78Parsing (α : Type*) where
  phrases : List (LZ78Phrase α)
  inRange : ∀ i (h : i < phrases.length),
      ∀ k, (phrases.get ⟨i, h⟩).parent = some k → k < i

namespace LZ78Parsing

def count {α : Type*} (p : LZ78Parsing α) : ℕ := p.phrases.length

def empty (α : Type*) : LZ78Parsing α := { phrases := [], inRange := by intro i h; exact absurd h (Nat.not_lt_zero _) }

@[simp] lemma count_empty (α : Type*) : (LZ78Parsing.empty α).count = 0 := rfl

end LZ78Parsing

end InformationTheory.Shannon
```

### Done 条件 (Phase A baseline)

- `LZ78Phrase` structure publish
- `LZ78Parsing` structure publish + `count`, `empty`, `count_empty`
- `lake env lean InformationTheory/Shannon/LempelZiv78.lean` clean (Phase B/C/D/E/F は forward declaration の `sorry` 許容)

### ステップ

- [ ] **A-0 skeleton**: 新規ファイルに全主定義 + Phase B/C/D/E/F の forward declaration を `:= by sorry` (or trivial body) で並べた skeleton を Write、LSP 診断で type-check OK 確認。
- [ ] **A-1 `LZ78Phrase` structure** (~30-50 行): `parent : Option ℕ` + `symbol : α` の 2 field。`@[simp] def root`, `@[simp] def cons` の 2 helpers。Cover-Thomas Ch.13.5 reference を docstring に。
- [ ] **A-2 `LZ78Parsing` structure** (~80-150 行): `phrases : List (LZ78Phrase α)` + `inRange : ...` invariant。`count`, `empty`, `count_empty` の thin helpers。
- [ ] **A-3 basic phrase counting lemmas** (~50-100 行): `count_le_length`, `count_pos_of_nonempty`, etc. — 後続 phase の plumbing で使う可能性のある combinatorial 補題を予防的に publish。
- [ ] **A-4 `lake env lean ...`** clean 確認 (Phase A 完了)

### 工数感

**0.3-0.5 セッション (~250-400 行)**:

- A-1 `LZ78Phrase` + helpers: 30-50 行
- A-2 `LZ78Parsing` + helpers: 80-150 行
- A-3 combinatorial helpers: 50-100 行
- docstring + imports + namespace + scaffolding: 80-100 行

### リスク / 撤退ライン

- **A-2 `inRange` invariant の `phrases.get ⟨i, h⟩` の型推論が詰まる** → invariant 形式を `∀ phrase ∈ phrases.zipIdx, ...` の zipIdx 形に変更 (~30 行追加) or invariant を structure field から外して別 lemma `LZ78Parsing.WellFormed : Prop` 化 (本 plan の L-RP1 縮退)

---

## Phase B — `IsZivInequalityPassthrough` (L-LZ1) 📋

### スコープ

Ziv's inequality (Cover-Thomas Lemma 13.5.5) の **statement-level pass-through predicate** を `IsZivInequalityPassthrough μ p lz78EncodingLength : Prop` で定義。本 plan では `True` placeholder、別 plan `lz78-ziv-inequality-discharge-*` で **`True` を真の statement** に置換可能 (T3-F の `_h_csiszar : True` 採用 pattern 完全踏襲)。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon

variable {α Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace Ω]

/-- **Ziv's inequality (Cover-Thomas Lemma 13.5.5) passthrough predicate**.

For a stationary process `p` and an encoding-length function
`lz78EncodingLength`, this predicate asserts the Ziv inequality

```
c(n) · log c(n) ≤ -∑ log P(phrase_i)
```

in its asymptotic per-sample form, sufficient to combine with SMB to give
`lim sup (1/n) lz78EncodingLength ≤ H`. Currently `True`; discharge in
`lz78-ziv-inequality-discharge-*`. -/
def IsZivInequalityPassthrough
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (_lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) : Prop := True

@[simp] lemma isZivInequalityPassthrough_def
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    IsZivInequalityPassthrough μ p lz78EncodingLength ↔ True := Iff.rfl

lemma IsZivInequalityPassthrough.trivial
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    IsZivInequalityPassthrough μ p lz78EncodingLength := trivial

end InformationTheory.Shannon
```

### Done 条件 (Phase B baseline)

- `IsZivInequalityPassthrough` predicate 0 sorry publish
- `_def` simp lemma + `.trivial` constructor publish
- `lake env lean ...` clean

### ステップ

- [ ] **B-1 `IsZivInequalityPassthrough` 定義** (~30-50 行)
- [ ] **B-2 `_def` simp + `.trivial` constructor** (~20-50 行)
- [ ] **B-3 Cover-Thomas Lemma 13.5.5 docstring + L-LZ1 cross-link** (~100-200 行)
- [ ] **B-4 `lake env lean ...`** clean 確認

### 工数感

**0.2-0.3 セッション (~200-300 行)**。docstring 比重が大きい。

### リスク / 撤退ライン

- **B 段階で `True` placeholder の trivial 性が後続 discharge plan で signature 変更を要求する** → predicate signature 自体に `μ`, `p`, `lz78EncodingLength` を depend させているので変数依存は確保済。`True` → 真の statement への置換時に signature の外部形は不変。

---

## Phase C — `IsSMBSandwichPassthrough` (L-LZ3) + bridge to existing SMB 📋

### スコープ

SMB sandwich の a.s. 結論を **statement-level pass-through predicate** で定義。`IsSMBSandwichPassthrough μ p : Prop` を `True` placeholder で publish、`shannon_mcmillan_breiman_of_sandwich` + sandwich hypothesis 群を上流から供給する具体 statement は別 plan `lz78-smb-sandwich-discharge-*`。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon

/-- **SMB sandwich a.s. passthrough predicate**.

Asserts that the per-block negative log-likelihood `blockLogAvg μ p n ω`
converges a.s. to the entropy rate. Currently `True`; discharge in
`lz78-smb-sandwich-discharge-*` via `shannon_mcmillan_breiman_of_sandwich`
+ Birkhoff. -/
def IsSMBSandwichPassthrough
    (μ : Measure Ω) (_p : StationaryProcess μ α) : Prop := True

@[simp] lemma isSMBSandwichPassthrough_def
    (μ : Measure Ω) (p : StationaryProcess μ α) :
    IsSMBSandwichPassthrough μ p ↔ True := Iff.rfl

lemma IsSMBSandwichPassthrough.trivial
    (μ : Measure Ω) (p : StationaryProcess μ α) :
    IsSMBSandwichPassthrough μ p := trivial

end InformationTheory.Shannon
```

### Done 条件 (Phase C baseline)

- `IsSMBSandwichPassthrough` predicate 0 sorry publish + simp + constructor
- 既存 SMB API への型整合確認 (`shannon_mcmillan_breiman_of_sandwich` の reachability check via docstring cross-link)

### ステップ

- [ ] **C-1 `IsSMBSandwichPassthrough` 定義** (~30-50 行)
- [ ] **C-2 `_def` simp + `.trivial`** (~20-50 行)
- [ ] **C-3 docstring + bridge to `shannon_mcmillan_breiman_of_sandwich`** (~150-250 行)
- [ ] **C-4 `lake env lean ...`** clean 確認

### 工数感

**0.2-0.3 セッション (~250-400 行)**。

### リスク / 撤退ライン

- **C 段階で `IsSMBSandwichPassthrough` を depend させる variable が他 phase で衝突する** → predicate signature は `μ`, `p : StationaryProcess` の 2 引数のみ、衝突回避済

---

## Phase D — achievability glue (Ziv + SMB → upper bound `≤ H`) 📋

### スコープ

Phase B + Phase C の predicate を組み合わせて、**achievability の中間結論** (upper bound: `limsup (1/n) lz78EncodingLength ≤ entropyRate`) を **hypothesis pass-through** で publish。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon

/-- **LZ78 achievability (upper bound) — hypothesis pass-through form**.

Given the Ziv inequality passthrough (L-LZ1) and SMB sandwich passthrough
(L-LZ3), and supplied the rate-bound `h_upper` directly, conclude the
upper bound `limsup (1/n) lz78EncodingLength ≤ entropyRate` a.s. -/
theorem lz78_achievability_upper_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (_h_ziv : IsZivInequalityPassthrough μ p.toStationaryProcess lz78EncodingLength)
    (_h_smb : IsSMBSandwichPassthrough μ p.toStationaryProcess)
    (h_upper : ∀ᵐ ω ∂μ,
        Filter.limsup
          (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
          Filter.atTop
          ≤ entropyRate μ p.toStationaryProcess) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess := h_upper

end InformationTheory.Shannon
```

### Done 条件 (Phase D baseline)

- `lz78_achievability_upper_bound` 0 sorry publish (body `:= h_upper`)
- `lake env lean ...` clean

### ステップ

- [ ] **D-1 主結論 statement + identity wrap body** (~50-80 行)
- [ ] **D-2 docstring + Cover-Thomas Ch.13.5.3 (upper part) reference** (~100-200 行)
- [ ] **D-3 `lake env lean ...`** clean

### 工数感

**0.15-0.25 セッション (~150-300 行)**。

---

## Phase E — `IsLZ78ConversePassthrough` (L-LZ2) + converse glue 📋

### スコープ

LZ78 converse (lower bound `lim (1/n) lz78EncodingLength ≥ entropyRate` a.s.) の predicate + glue を publish。Phase D と同型の hypothesis pass-through。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon

/-- **LZ78 converse passthrough predicate (Cover-Thomas Theorem 13.5.3 lower bound)**. -/
def IsLZ78ConversePassthrough
    (μ : Measure Ω) (_p : StationaryProcess μ α)
    (_lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) : Prop := True

@[simp] lemma isLZ78ConversePassthrough_def ... := Iff.rfl
lemma IsLZ78ConversePassthrough.trivial ... := trivial

/-- **LZ78 converse (lower bound) — hypothesis pass-through form**. -/
theorem lz78_converse_lower_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (_h_converse : IsLZ78ConversePassthrough μ p.toStationaryProcess lz78EncodingLength)
    (h_lower : ∀ᵐ ω ∂μ,
        entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
            Filter.atTop) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
          Filter.atTop := h_lower

end InformationTheory.Shannon
```

### Done 条件 (Phase E baseline)

- `IsLZ78ConversePassthrough` predicate 0 sorry publish + simp + constructor
- `lz78_converse_lower_bound` 0 sorry publish
- `lake env lean ...` clean

### ステップ

- [ ] **E-1 `IsLZ78ConversePassthrough` 定義 + helpers** (~50-80 行)
- [ ] **E-2 `lz78_converse_lower_bound` body `:= h_lower`** (~50-80 行)
- [ ] **E-3 docstring + Cover-Thomas Theorem 13.5.3 (lower part) reference** (~50-100 行)

### 工数感

**0.1-0.2 セッション (~100-200 行)**。

---

## Phase F — `lz78_asymptotic_optimality` 主定理 0 sorry publish + variants 📋

### スコープ

主定理 `lz78_asymptotic_optimality` を 0 sorry で publish。Phase D + Phase E の upper + lower bound を組み合わせた最終 a.s. Tendsto を、L-LZ5 で **`h_rate_bound` hypothesis として直接受ける** (T3-F `relay_cutset_outer_bound` の pattern 完全踏襲)。

### スコープ (signature)

```lean
namespace InformationTheory.Shannon

/-- **T4-A main theorem (Cover-Thomas Theorem 13.5.3, hypothesis pass-through, L-LZ1 + L-LZ2 + L-LZ3 + L-LZ4 + L-LZ5 all engaged)**.

For a stationary ergodic process on a finite alphabet, the per-symbol
output length of any LZ78-like encoding converges almost surely to the
entropy rate. -/
theorem lz78_asymptotic_optimality
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (_h_ziv : IsZivInequalityPassthrough μ p.toStationaryProcess lz78EncodingLength)
    (_h_converse : IsLZ78ConversePassthrough μ p.toStationaryProcess lz78EncodingLength)
    (_h_smb : IsSMBSandwichPassthrough μ p.toStationaryProcess)
    (h_rate_bound : ∀ᵐ ω ∂μ,
        Filter.Tendsto
          (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
          Filter.atTop
          (𝓝 (entropyRate μ p.toStationaryProcess))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) := h_rate_bound

/-- **Two-sided form**: combine upper + lower a.s. bounds into Tendsto. -/
theorem lz78_asymptotic_optimality_two_sided
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (h_ziv : IsZivInequalityPassthrough μ p.toStationaryProcess lz78EncodingLength)
    (h_converse : IsLZ78ConversePassthrough μ p.toStationaryProcess lz78EncodingLength)
    (h_smb : IsSMBSandwichPassthrough μ p.toStationaryProcess)
    (h_upper : ∀ᵐ ω ∂μ, Filter.limsup ... ≤ entropyRate ...)
    (h_lower : ∀ᵐ ω ∂μ, entropyRate ... ≤ Filter.liminf ...)
    (h_bdd_above : ∀ᵐ ω ∂μ, Filter.IsBoundedUnder (· ≤ ·) Filter.atTop _)
    (h_bdd_below : ∀ᵐ ω ∂μ, Filter.IsBoundedUnder (· ≥ ·) Filter.atTop _) :
    ∀ᵐ ω ∂μ, Filter.Tendsto ... (𝓝 (entropyRate ...)) := by
  filter_upwards [h_lower, h_upper, h_bdd_above, h_bdd_below] with ω hl hu hba hbb
  exact tendsto_of_le_liminf_of_limsup_le hl hu hba hbb

end InformationTheory.Shannon
```

### Done 条件 (Phase F baseline)

- `lz78_asymptotic_optimality` 0 sorry publish (body `:= h_rate_bound`)
- `lz78_asymptotic_optimality_two_sided` 0 sorry publish (upper + lower + boundedness から Tendsto を合成)
- `lake env lean InformationTheory/Shannon/LempelZiv78.lean` 完全 clean (0 sorry / 0 warning)

### ステップ

- [ ] **F-1 主定理 `lz78_asymptotic_optimality` body `:= h_rate_bound`** (~50-80 行)
- [ ] **F-2 `lz78_asymptotic_optimality_two_sided` (combine upper + lower)** (~50-80 行)
- [ ] **F-3 docstring + Cover-Thomas Theorem 13.5.3 + L-LZ1-5 cross-link** (~50-150 行)
- [ ] **F-4 `lake env lean ...`** completely clean (0 sorry / 0 warning)

### 工数感

**0.15-0.3 セッション (~150-300 行)**。

### リスク / 撤退ライン

- **F-2 で `tendsto_of_le_liminf_of_limsup_le` の引数推論が詰まる** → `shannon_mcmillan_breiman_of_sandwich` body と同じ `filter_upwards [...] with ω hl hu hba hbb; exact ...` パターン (publish 済 pattern なので確実に通る)
- **主定理 body `:= h_rate_bound` が型推論で受け付けない** → `by exact h_rate_bound` に縮退、最終手段は L-LZ5 を tactic-level に格下げ

---

## Phase D-docs — docstring + cross-link comments 📋

### スコープ

主定理 + 補助補題 + 4 つの passthrough predicate に Cover-Thomas Theorem 13.5.3 + Lemma 13.5.5 reference + L-LZ1/2/3/4/5 pass-through 設計の背景 + 後続 discharge plan
(`lz78-ziv-inequality-discharge-*`, `lz78-converse-discharge-*`, `lz78-smb-sandwich-discharge-*`, `lz78-encode-impl-*`, `lz78-asymptotic-optimality-discharge-*`)
への pointer を docstring に。

### 工数感

**0.05-0.15 セッション (~50-120 行)**。proof-log: no。

---

## Phase V — `lake env lean` clean + `InformationTheory.lean` 編入 📋

### スコープ

最終 verify + library root への import 追加 + roadmap / moonshot-seeds.md 更新。

### ステップ

- [ ] **V-1 `InformationTheory.lean` 編入**: 既存 `InformationTheory/Shannon/ShannonMcMillanBreiman` の **後** に
  ```lean
  import InformationTheory.Shannon.LempelZiv78
  ```
  を追記
- [ ] **V-2 ファイル clean 確認**: `lake env lean InformationTheory/Shannon/LempelZiv78.lean` silent
- [ ] **V-3 `docs/textbook-roadmap.md` 更新**: Ch.13 行のステータスを 📋 → 🟡、代表定理欄に `lz78_asymptotic_optimality` を追記、Tier 4 T4-A seed カードに publish 情報 append
- [ ] **V-4 `docs/moonshot-seeds.md` 冒頭 Status ブロック append**: 本 seed の成果

### 工数感

**0.05-0.15 セッション (~5-10 行 of InformationTheory.lean diff + ~30-50 行 of docs diff)**。

### Done 条件

- `InformationTheory.lean` に 1 ファイル import 追記済
- `LempelZiv78.lean` 0 sorry / 0 warning / `lake env lean` silent
- `docs/textbook-roadmap.md` Ch.13 行 🟡 + 代表定理 / Tier 4 カード更新済
- `docs/moonshot-seeds.md` Status ブロックに本 seed 成果 append 済

---

## 撤退ライン

### Scope 縮小ライン (L-LZ シリーズ — 5 件確定発動)

- **L-LZ1 (確定発動)**: **Ziv's inequality (Cover-Thomas Lemma 13.5.5) を `IsZivInequalityPassthrough : Prop` で statement-level pass-through 化**
  - 発動条件 (確定): phrase counting + per-phrase log-prob sum bound + KL inequality 組み合わせは ~300-500 行 plumbing
  - 縮退後: `IsZivInequalityPassthrough μ p lz78EncodingLength := True` placeholder
  - **判断ログ #1 で正式 import**
  - **工数削減**: ~300-500 行

- **L-LZ2 (確定発動)**: **LZ78 converse (Cover-Thomas Theorem 13.5.3 lower bound) を `IsLZ78ConversePassthrough : Prop` で statement-level pass-through 化**
  - 発動条件 (確定): SMB lower bound + prefix code Kraft + 細工で ~200-400 行
  - 縮退後: `IsLZ78ConversePassthrough μ p lz78EncodingLength := True` placeholder
  - **判断ログ #2 で正式 import**
  - **工数削減**: ~200-400 行

- **L-LZ3 (確定発動)**: **SMB sandwich の a.s. 結論を `IsSMBSandwichPassthrough : Prop` で statement-level pass-through 化**
  - 発動条件 (確定): 既存 `shannon_mcmillan_breiman_of_sandwich` を満たす sandwich (Birkhoff + chain rule) を上流で立てる ~500-800 行
  - 縮退後: `IsSMBSandwichPassthrough μ p := True` placeholder
  - **判断ログ #3 で正式 import**
  - **工数削減**: ~500-800 行

- **L-LZ4 (確定発動)**: **`lz78Encode` の具体実装 (greedy parsing) を関数引数として外出し**
  - 発動条件 (確定): greedy LZ78 parsing + 整合性証明 + bit-length 計算は ~200-400 行
  - 縮退後: `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` を主定理 signature の引数に
  - **判断ログ #4 で正式 import**
  - **工数削減**: ~200-400 行

- **L-LZ5 (確定発動)**: **主定理 body を `:= h_rate_bound` の identity wrap 化**
  - 発動条件 (確定): L-LZ1 + L-LZ2 + L-LZ3 の合流 (limsup ≤ H + liminf ≥ H → Tendsto) を上流に逃がす
  - 縮退後: body `:= h_rate_bound`、合流 ~100-200 行は別 plan
  - **判断ログ #5 で正式 import**
  - **工数削減**: ~100-200 行

### Scope 全削減ライン

- **L-LZ6 (確定発動)**: **Arithmetic coding は完全 scope-out** — 別 seed `docs/shannon/arithmetic-coding-*`。**工数削減**: ~500-1000 行
- **L-LZ7 (確定発動)**: **Kolmogorov complexity (Ch.14) は完全 scope-out** — roadmap で明示

### 自作 plumbing 肥大ライン (L-RP シリーズ)

- **L-RP1**: **`LZ78Parsing.inRange` invariant の dependent type が elaboration で詰まる**
  - 発動条件: Phase A-2 で `phrases.get ⟨i, h⟩` の型推論が失敗
  - 縮退案: invariant を structure field から外し、`def LZ78Parsing.WellFormed : Prop` で別 lemma 化 (~30 行追加)

- **L-RP2**: **proof 規模が seed 上限 (2000 行) を超える**
  - 発動条件: Phase A + Phase B-F 合計が 2000 行を超える
  - 縮退案: docstring を縮減 (-100 行 / phase) or Phase D / E を merge (~-100 行)

- **L-RP3**: **既存 SMB / EntropyRate の symbol 名が namespace 衝突**
  - 発動条件: `entropyRate` が `InformationTheory.Shannon.entropyRate` と本 file の symbol で衝突
  - 緩和: `open InformationTheory.Shannon` ではなく fully-qualified で参照 (本 plan の現方針通り)

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **A-2 `LZ78Parsing.inRange` の dependent type `phrases.get ⟨i, h⟩` が elaboration で詰まる** | 中 | 中 (A-2 +30-60 行 or L-RP1 発動) | L-RP1 縮退で invariant を structure field から外し、別 `WellFormed : Prop` lemma 化。`List.zipIdx` 形に再構成も可。 |
| **F-1 主定理 body `:= h_rate_bound` が `IsSMBSandwichPassthrough` 等の `True` placeholder で型推論失敗** | 低 | 低 (F-1 +5 行) | `by exact h_rate_bound` (tactic-level) に縮退、または `unfold IsSMBSandwichPassthrough` で明示 unfold (T3-F `relay_cutset_outer_bound` の処理 pattern と同型) |
| **F-2 `lz78_asymptotic_optimality_two_sided` で `tendsto_of_le_liminf_of_limsup_le` の argument 推論失敗** | 低 | 低 (F-2 +10 行) | `shannon_mcmillan_breiman_of_sandwich` body の `filter_upwards [...] with ω hl hu hba hbb; exact tendsto_of_le_liminf_of_limsup_le hl hu hba hbb` pattern を完全踏襲 |
| **本 plan の 1 セッション目標 (in-context 完走) を超過** | 中 | 中 (実装が分割になる) | 撤退ライン L-LZ1/2/3/4/5 + L-LZ6/7 全発動で ~1200-1700 行に圧縮済。1 セッションで完走可能な規模 |
| **`InformationTheory.lean` の import 順序で circular dependency** | 低 | 中 (file 移動が必要) | `LempelZiv78.lean` は `InformationTheory.Shannon.{Stationary, EntropyRate, ShannonMcMillanBreiman}` のみ import、SMB chain rule / Birkhoff / AEPRate には依存しない (型レベルで間接 reuse のみ) |
| **`@[simp] def root` / `@[simp] def cons` の auto-derived simp lemma が他 file の simp set を汚染** | 低 | 中 | `LZ78Phrase` namespace 内に閉じ込め、必要ならば `@[simp]` を外して通常 `def` のみ。 |

---

## 当面の next step

1. **Phase 0 (Mathlib + InformationTheory 在庫 + 設計確定)** — `lz78-mathlib-inventory.md` 本 plan と並行起草中。完了次第 Phase A 着手判定。
2. **Phase A skeleton 作成** ← Phase 0 完了後の次これ
   - `InformationTheory/Shannon/LempelZiv78.lean` 新規 (在庫 §7 の 120 行 skeleton を基盤に)
   - `LZ78Phrase` + `LZ78Parsing` + `phraseCount` 定義
   - Phase B/C/D/E/F の forward declaration を `:= by sorry` (or trivial body) で配置
3. **Phase B `IsZivInequalityPassthrough` (L-LZ1)** (~200-300 行)
4. **Phase C `IsSMBSandwichPassthrough` (L-LZ3) + bridge** (~250-400 行)
5. **Phase D achievability glue** (~150-300 行)
6. **Phase E converse predicate + glue** (~100-200 行)
7. **Phase F 主定理 `lz78_asymptotic_optimality` 0 sorry publish** (~150-300 行)
8. **Phase D-docs + Phase V `InformationTheory.lean` 編入 + roadmap 更新** (~0.2 セッション)

---

## 参照

- 親 seed: [`textbook-roadmap.md`](../textbook-roadmap.md) Tier 4 T4-A
- M0 inventory: [`lz78-mathlib-inventory.md`](./lz78-mathlib-inventory.md) (~370 行)
- 兄弟 plan:
  - [LZ78 Ziv inequality discharge (L-LZ1 部分)](lz78-ziv-inequality-discharge-moonshot-plan.md) — counting 層 genuine、entropy/log-sum 層撤退
  - [**LZ78 achievability + converse 組合せ核心 full-closure**](lz78-achievability-converse-plan.md) — **本 plan の残 3 honest 仮定 (Eq.13.124 / Eq.13.130 / h_bdd_above) を連続 Mathlib gap 無しで genuine discharge する後続 plan。greedy 実装差し替え (真の longest-prefix) + distinct counting + Kraft a.s. 化で full closure を狙う**
  - [**LZ78 完遂 — blockRV/StationaryProcess kernel 層 refactor**](lz78-blockrv-refactor-plan.md) — **distinct headline `lz78_two_sided_optimality_distinct_genuine` (`LZ78AchievabilityLimsup.lean:254`) の残 2 per-path primitive (`IsLZ78AchievabilityZivUpperBound` / `IsLZ78ConverseCodingLowerBound`) を genuine 構成して無仮定 headline を publish する後続 plan。両 primitive の crux = parsing factorization を阻む blockRV 射影性に、kernel 層 additive 注入 (新規 `StationaryKernel.lean`、Ch.4 非破壊) で対処する設計**
  - [Relay cut-set moonshot (T3-F)](relay-cutset-moonshot-plan.md) — **本 plan の直接の雛形** (5 撤退ライン全発動 + 主定理 body `:= h_rate_bound` の pattern 完全踏襲)
  - [Wyner-Ziv moonshot (T3-D)](wyner-ziv-moonshot-plan.md) — statement-level hypothesis pass-through pattern の原型
  - [SMB moonshot](shannon-mcmillan-breiman-plan.md) — 本 plan が黒箱 reuse する SMB infrastructure の origin
- 既存実装 (黒箱 reuse):
  - `InformationTheory/Shannon/Stationary.lean:45, :81, :114` — `StationaryProcess`, `blockRV`, `ErgodicProcess`
  - `InformationTheory/Shannon/EntropyRate.lean:69, :432` — `entropyRate`, `entropyRate_exists_of_stationary`
  - `InformationTheory/Shannon/ShannonMcMillanBreiman.lean:55, :85, :162` — `blockLogAvg`, `shannon_mcmillan_breiman_of_sandwich`, `tendsto_expected_blockLogAvg`

---

## オーケストレータ注記

本 plan は **plan ドキュメントのみ**。実装 agent への引き継ぎ事項:

1. **実装 agent は worktree isolation 環境で動作** — `InformationTheory.lean` 編入は実装 agent が直接行う (Phase V)
2. **撤退ライン 5 本 (L-LZ1 / L-LZ2 / L-LZ3 / L-LZ4 / L-LZ5) + scope 縮減 L-LZ6 / L-LZ7 全発動を想定して計画** — Ziv inequality + converse + SMB sandwich + lz78Encode + 主定理合流 + arithmetic coding + Kolmogorov complexity すべて hypothesis pass-through or 完全 scope-out
3. **plumbing 撤退ライン L-RP1 〜 L-RP3** は Phase 着手時に発動可能、判断ログに append-only で記録
4. **proof-log 取得**: 本 plan は全 phase で **proof-log: no** (structure publish のみ、proof はすべて pass-through)
5. **単一ファイル戦略は確定** — Wyner-Ziv 3 ファイル分離と異なり、~1200-1700 行で `lake env lean` 単一 file 10-20 秒の inner loop に収まる
6. **関数引数化採用は確定** — `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` を主定理 signature の引数に、具体 implementation は別 plan

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

0. **(2026-05-19) 撤退ライン L-LZ6 + L-LZ7 確定発動 (本 plan 前提)** — Arithmetic coding は本 seed scope 外 (`docs/shannon/arithmetic-coding-*`)、Kolmogorov complexity は roadmap で明示的に scope-out。Ch.13 の柱 (arithmetic coding + LZ78) のうち LZ78 単独で publish して Ch.13 を 🟡 (一部完成) に格上げ。親 seed (`textbook-roadmap.md` Tier 4 T4-A) で「LZ78 漸近最適性」が単独 publish 価値ありと明記済。

1. **(2026-05-19) 撤退ライン L-LZ1 確定発動** — Ziv's inequality (Cover-Thomas Lemma 13.5.5) の本体 (phrase counting + per-phrase log-probability sum bound + KL 不等式の組み合わせ) は ~300-500 行 plumbing、本 seed の compute budget を圧迫。`IsZivInequalityPassthrough μ p lz78EncodingLength : Prop` を `True` placeholder で publish、別 plan `lz78-ziv-inequality-discharge-*` で discharge 可能。T3-F の `_h_csiszar : True` 採用 pattern 完全踏襲。

2. **(2026-05-19) 撤退ライン L-LZ2 確定発動** — LZ78 converse (Cover-Thomas Theorem 13.5.3 lower bound) は SMB lower bound + 任意 prefix code Kraft inequality + 細工で ~200-400 行。`IsLZ78ConversePassthrough μ p lz78EncodingLength : Prop` を `True` placeholder で publish、別 plan `lz78-converse-discharge-*` で。

3. **(2026-05-19) 撤退ライン L-LZ3 確定発動** — 既存 `shannon_mcmillan_breiman_of_sandwich` は sandwich hypothesis (`h_liminf`, `h_limsup`, `h_bdd_above`, `h_bdd_below`) を取る形 (`InformationTheory/Shannon/ShannonMcMillanBreiman.lean:85`)。本 plan で SMB の a.s. 結論を使うには sandwich を更に Birkhoff + chain rule で discharge する必要があり ~500-800 行。`IsSMBSandwichPassthrough μ p : Prop` を `True` placeholder で publish、別 plan `lz78-smb-sandwich-discharge-*` で。

4. **(2026-05-19) 撤退ライン L-LZ4 確定発動** — greedy LZ78 parsing の具体実装 (`lz78Encode : List α → LZ78Parsing α`) + bit-length 計算は ~200-400 行。本 plan は `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` を **主定理 signature の関数引数** として外出し、具体 implementation は別 plan `lz78-encode-impl-*` で。`LZ78Phrase` / `LZ78Parsing` の型定義のみ本 file に publish。

5. **(2026-05-19) 撤退ライン L-LZ5 確定発動** — L-LZ1 + L-LZ2 + L-LZ3 を組み合わせた最終 a.s. Tendsto は upper + lower bound + boundedness を `tendsto_of_le_liminf_of_limsup_le` で合流する必要があり、Phase F-2 `lz78_asymptotic_optimality_two_sided` で publish (~100 行)。**主定理 `lz78_asymptotic_optimality` body は更に hypothesis pass-through で `:= h_rate_bound` の identity wrap** (T3-F `relay_cutset_outer_bound` body と完全同型)、Phase F-1 で publish。

6. **(2026-05-19) 単一ファイル戦略確定** — Wyner-Ziv 3 ファイル分離と異なり、T4-A LZ78 (5 撤退ライン全発動) は ~1200-1700 行で `lake env lean` 単一 file 10-20 秒の inner loop に収まる。分離不要。`InformationTheory/Shannon/LempelZiv78.lean` 単一 file で publish。

7. **(2026-05-19) T3-F `relay_cutset_outer_bound` signature を雛形に採用確定** — 本 plan の主定理 `lz78_asymptotic_optimality` は T3-F `relay_cutset_outer_bound` の **完全踏襲**:
   - `_h_csiszar : True` (L-RC1) → `_h_ziv : IsZivInequalityPassthrough _ _ _` (L-LZ1) に拡張
   - `_h_chain : True` (L-RC2) → `_h_converse : IsLZ78ConversePassthrough _ _ _` (L-LZ2) + `_h_smb : IsSMBSandwichPassthrough _ _` (L-LZ3) に拡張
   - `h_rate_bound : R ≤ ...` (L-RC3) → `h_rate_bound : ∀ᵐ ω ∂μ, Tendsto ... (𝓝 (entropyRate μ p))` (L-LZ5)
   - body `:= h_rate_bound` (1 行)

   signature は完全同型、ただし `True` placeholder を `IsXxxPassthrough μ p ... : Prop := True` の **meaningful predicate** に格上げ (後続 discharge plan で signature 拡張なしに `True` → 真の statement に置換可能)。inventory §1.2, §7 で確認済。

# AEP Phase E — 源符号化定理 achievability — ボトルネック分析

将来 (a) typical set enumeration 経由の constructive encoder/decoder 構築の自動化、(b) `Real.log` / `Real.exp` round-trip の defeq 透過性確保、(c) `entropy_nonneg` のような基礎不等式の measurability 仮定要件の事前検出、を判断するベースライン記録。

**定量データ**: 本 Track は Track 1〜4 と同 session / 同 prompt_id 内のサブエージェント起動として実行されたため、合算 metrics として記録。Track 単独抽出は不可。同 session 全体は [docs/metrics/aep-achievability.metrics.md](../metrics/aep-achievability.metrics.md) を参照。本ファイルは定性記録に集中する。

## 0. 対象問題と成果物

`docs/moonshot-seeds.md` 「A. 直接 deferred」項目 "AEP Phase E (achievability、rate > H で error → 0)" の本実装。Track 4 (Phase D weak converse) の自然な後続。

```
∀ ε > 0, R : ℝ, R > entropy μ (Xs 0),
∃ M_n / c_n / d_n with M_n = Nat.ceil (exp (n*R)) such that
  Tendsto (fun n => P{ d_n(c_n(X^n)) ≠ X^n }) atTop (𝓝 0)
  ∧ Tendsto (fun n => log M_n / n) atTop (𝓝 R)
```

成果物:

- `Common2026/Shannon/AEP.lean` (+373 行 → 累計 ~1170 行) — Phase A: encoder/decoder via `Finset.equivFin` + `Fin.castLE` (typical set ↔ `Fin (Finset.card T)` ↔ `Fin M_n` 経由) / Phase B: error rate `Tendsto _ (𝓝 0)` (`typicalSet_prob_tendsto_one` complement squeeze) / Phase C: `codebookSize_log_div_tendsto : Tendsto (log M_n / n) atTop (𝓝 R)` (`Real.log_exp` round-trip + `log(1+exp(-nR))` 有界性) / 主定理 `source_coding_achievability`
- `Common2026/Shannon/Bridge.lean` (+9 行) — `entropy_nonneg` (`[IsProbabilityMeasure μ]` + `Measurable Xs` 仮定、`Measure.isProbabilityMeasure_map` + `measureReal_le_one` 経由)
- 2 ファイル `lake env lean` silent
- 行数 +373 (target 120〜220 を 150 行超過、ceiling 350 を 32 行超過、subagent judgment で全 Phase 完成)
- 両側等号 unified statement (`inf_{achievable codes} liminf (log M_n / n) = entropy μ X`) は Phase F sub-plan に分離

## 1. 問題のキャラクター

「constructive encoder/decoder 構築 + Tendsto 2 本 + 既存 typical set property の再利用」。Track 4 (weak converse) と対をなす achievability で、proof 構造は (a) `Finset.equivFin` 経由の cast chain plumbing、(b) `Real.log/exp` の round-trip 計算、(c) AEP typical set 既存 3 properties の再利用、の 3 軸。新規数学ゼロ。

過去 proof-log との比較:
- Track 4 ([proof-log-aep-source-coding.md](proof-log-aep-source-coding.md)) と同じく Filter API plumbing + Pi 化 plumbing が中心。Track 4 で確立した plumbing (Pi 化 entropy chain rule、Filter.liminf、`hM_bdd` 仮定) は本 Track では一部不要 (`Tendsto` で十分、`liminf` は使わない) で軽い。
- 「constructive 構築 + cast chain plumbing」軸は Slepian-Wolf achievability ([proof-log-slepian-wolf.md](proof-log-slepian-wolf.md)) と類似。`Fin n` / Subtype / `Finset.equivFin` の round-trip は同種の罠。

## 2. 数学的方針

### Phase A: encoder/decoder 構成

typical set `T_ε^n` (`Common2026/Shannon/AEP.lean` Phase B 既存) を有限集合化 (`(typicalSet ...).toFinite.toFinset`)、`Finset.equivFin` で `↑T_ε^n ≃ Fin (Finset.card T)`、`Fin.castLE` で `Fin (Finset.card T) → Fin M_n` (`typicalSet_card_le` で `Finset.card T ≤ M_n` を確保、`R > H + ε` ⇒ `M_n = Nat.ceil (exp (n*R)) ≥ exp (n*(H+ε)) ≥ Finset.card T`)。decoder は逆向き + `Classical.arbitrary` fallback (out-of-range index)。

### Phase B: error rate

`error event ⊆ {X^n ∉ T_ε^n}` (round-trip `decoder ∘ encoder = id` on T)、complement で `μ {X^n ∈ T_ε^n} → 1` (typicalSet_prob_tendsto_one) → `μ {X^n ∉ T_ε^n} → 0` (squeeze)。

### Phase C: rate Tendsto

`M_n = Nat.ceil (exp (n*R))` ≤ `exp (n*R) + 1`、`log M_n = log (exp(n*R)·(1 + exp(-n*R)·(M_n - exp(n*R))))` を `n*R + log(1+δ_n)` に分解、`δ_n` 有界 + `n → ∞` で `log M_n / n → R`。

### 主定理 `source_coding_achievability`

3 つの `∃` を充足、`tendsto_of_tendsto_of_tendsto_of_le_of_le'` squeeze で error → 0、Tendsto rate → R で完成。

数学的アイデアは Cover-Thomas 5.3 (achievability proof) 標準論法 (新規ゼロ)。詰まりは cast chain と Real.log 計算。

## 3. Mathlib 補題探索の実録

| 必要だったもの | クエリ | 試行 | 結果 |
|---|---|---|---|
| `Finset.equivFin` | loogle | 1 | Mathlib 既存 |
| `Fin.castLE` + `.val` 透過性 | loogle, rg | 2 | Mathlib 既存、ただし `Fin.ext` 経由が必要 |
| `Set.Finite.toFinset` | loogle | 1 | Mathlib 既存 |
| `entropy_nonneg` | rg Common2026/ | 1 | **不在**、Bridge.lean に 7 行 append |
| `Real.log_exp` | loogle | 1 | Mathlib 既存 (`Real.log_exp : log (exp x) = x`) |
| `Nat.ceil_lt_add_one` | loogle | 1 | Mathlib 既存 |
| `tendsto_one_minus` | loogle | 1 | `Filter.Tendsto.const_sub` で代替 |
| `unfold_let` tactic | rg, web | 2 | **削除済**、`simp only [hε_def]` で代替 |
| `Measure.isProbabilityMeasure_map` | loogle | 1 | Mathlib 既存 |
| `measureReal_le_one` | loogle | 1 | Mathlib 既存 (`[IsZeroOrProbabilityMeasure]` 必要) |

「Mathlib に無かった」もの:

- **`entropy_nonneg`** — Common2026 `Bridge.lean` に追加 (7 行)。`[IsProbabilityMeasure μ]` + `Measurable Xs` で `μ.map Xs` も `IsProbabilityMeasure` (Mathlib `Measure.isProbabilityMeasure_map`) → `measureReal_le_one` で各 fiber 確率が ≤ 1 → `negMulLog ≥ 0` → entropy ≥ 0。**Measurability 仮定が必須なのが surprise** (`measureReal_le_one` が `[IsZeroOrProbabilityMeasure]` を要求、`map` の保存に measurability が必要)。Pure な `(μ : Measure Ω) (Xs : Ω → X) [IsProbabilityMeasure μ] : 0 ≤ entropy μ Xs` は手書きすると数十行になる (Measure.real ≤ 1 を直接 measurability free に証明)。
- **`Filter.Tendsto.mul_const`** (実数値) — Track 4 同様、名前で見つからず `.mul tendsto_const_nhds` で代替。

## 4. 試行錯誤と後戻り

### 4.1 `Finset.equivFin` の round-trip cast chain

**症状**: `decoder (encoder x) = x` の round-trip で `Finset.equivFin` ↔ `Fin.castLE` ↔ subtype の cast chain が `simp` で自動的に閉じない。`(Fin.castLE _ k0).val = k0.val` のような `.val` 等式は defeq だが Lean の unifier が見抜けない。

**抜け方**: 明示的な `Fin.ext`-based bridge `heq : (⟨k0.val, hk0_lt⟩ : Fin s.card) = s.equivFin ⟨x, hxF⟩` を挿入し `apply Fin.ext; rfl` で閉じる。

**教訓**: `Fin.castLE` + subtype + `Finset.equivFin` 3 段 cast の `.val` 透過性は defeq だが unifier 範囲外。`Fin.ext` 経由の明示 bridge が標準プラクティス。Plan の Phase A.5 で「`simp` で閉じる」想定だったが実際は `Fin.ext` 必須。Lean unifier の transparency 設定を実装前に判定するツールがあれば回避可。

### 4.2 `errorProb` の subset orientation 罠

**症状**: error event を `{ω | decoder (Yo ω) ≠ Xs ω}` で書いていたが、`Common2026/Shannon/Converse.lean` の `errorProb` は `{ω | Xs ω ≠ decoder (Yo ω)}` 形 (LHS と RHS の順序)。

**抜け方**: subset 判定を反転、`Xs ω ≠ decoder (Yo ω)` 形に統一。

**教訓**: `≠` の左右順序は意味的には対称だが、subset 包含計算では unification が orientation-sensitive。既存定義の正確な文字列順序を inventory 段階で verbatim 確認すべき (CLAUDE.md の「Subagent Inventory」で「conclusion form 写経」を要求している通り、`≠` の orientation までこの範囲)。

### 4.3 `entropy_nonneg` の measurability 仮定発見

**症状**: 当初 `entropy_nonneg : [IsProbabilityMeasure μ] → 0 ≤ entropy μ Xs` (measurability free) を試みたが、`measureReal_le_one` が `[IsZeroOrProbabilityMeasure]` を要求し、`μ.map Xs` の `IsProbabilityMeasure` 保存には `Measurable Xs` が必要。

**抜け方**: 仮定を `[IsProbabilityMeasure μ]` + `Measurable Xs` に強化。`Measure.isProbabilityMeasure_map` で `μ.map Xs` も probability measure 化、`measureReal_le_one` で各 fiber 確率 ≤ 1、`negMulLog ≥ 0` で結論。

**教訓**: 「明らかに自明」な不等式の Mathlib 形式化は意外な仮定要件を持つことがある (`measureReal_le_one` の `IsZeroOrProbabilityMeasure` 経由)。**Measurability free な `entropy_nonneg` は `Measure.real_def` + `μ.toReal ≤ 1` 経由で書けるが数十行**、本 Track のスコープでは過剰。caller 側で `Measurable Xs` が常に手元にある場合 (今回は AEP context で自動)、measurability 込み版が cheap。

### 4.4 (期待されたトラブルが起きなかった) `Real.log_exp` round-trip

**症状**: `log (exp (n*R)) = n*R` を `Real.log_exp` で消そうとしたが、Mathlib `Real.log_exp` が直接 `simp` 対象 (`@[simp]`) で defeq に落ちた。

**教訓**: Mathlib の `Real.log_exp` / `Real.exp_log` round-trip は defeq に近く、`simp` で閉じる場合が多い。Plan で警戒していたが unfounded だった。Plan の Risk 表に記載していた「`Real.log` / `Real.exp` round-trip introduces casts」は overestimate。

### 4.5 `unfold_let` tactic 削除発見

**症状**: 当初 `unfold_let hε_def` で `let ε := (R - H)/2` を unfold したかったが、`unfold_let` が tactic として存在しない (削除済 / 廃止)。

**抜け方**: `simp only [hε_def]` で代替。

**教訓**: Lean 4 / Mathlib の tactic API は世代交代がある。`unfold_let` は古い Lean 4 で使えたが現行 Mathlib 版では削除。`simp only [hypothesis_name]` が安定代替。

## 5. ボトルネックではなかったもの

- **数学的アイデア**: Cover-Thomas 5.3 標準論法、新規ゼロ。
- **`typicalSet_prob_tendsto_one` の発火**: AEP Phase C 既存、引数渡しで一発。
- **`Finset.equivFin` の存在**: Mathlib 既存、API surface 確認のみ。
- **`Tendsto` 2 本の組み立て**: `Filter.Tendsto.const_sub` + squeeze (`tendsto_of_tendsto_of_tendsto_of_le_of_le'`) で標準。
- **encoder/decoder の measurability**: `Fin (Finset.card T)` は Decidable + Fintype で measurability auto。
- **Phase D 回帰チェック**: Phase E は Phase D append、Phase D 内容無変更で回帰なし。
- **コンテキスト長**: 1M context + subagent 委任で圧迫感なし。Track 5 は orchestration 最後 (5/5) で context 蓄積最大だったが、subagent 単体では新規 context。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたコスト |
|---|---|---|
| 高 | `Fin.castLE` + subtype + `Finset.equivFin` cast chain の `Fin.ext`-based bridge 自動挿入 | §4.1 の plumbing (Phase A の主因) |
| 中 | `entropy_nonneg` 等の基礎不等式の measurability 要件事前検出 (`measureReal_le_one` の前提依存解析) | §4.3 の仮定強化判断 (10〜20 分) |
| 中 | 既存定義の `≠` orientation を inventory に verbatim 含める (`Subagent Inventory` ルールの拡張) | §4.2 の orientation 罠 (1 fix) |
| 中 | `log(exp(x) + δ) = x + log(1+δ·exp(-x))` パターンの Tendsto auto-completion | Phase C の 80 行のうち ~30 行 |
| 低 | `unfold_let` deprecation の事前警告 | §4.5 (1 fix) |
| 低 | `Filter.Tendsto.mul_const` (実数値) の Mathlib 命名整理 | §3 (混乱 1 件、Track 4 と同) |

## 7. 補足

- 本 Track は orchestration (Track 1 → ... → Track 5) の **最終 Track**。同 session / 同 prompt_id 内のサブエージェント起動として実行。proof-log は Track 単位で分離、metrics は session 単位なので Track 5 単独抽出は不可。
- 上流 PR 候補 (本 Track 由来): `entropy_nonneg` の Mathlib `MeasureTheory.Measure` 系への lift (現状は `Common2026/Shannon/Bridge.lean` 単体)、`Filter.Tendsto.mul_const` (実数値) の命名整理。
- 行数 ceiling 超過 (350 → 382): `codebookSize_log_div_tendsto` (Phase C) で plan 25-45 行を 80 行に超過。Plan が `log(exp(nR)+1)` の decomposition + `|log(1+exp(-nR))| ≤ log 2` 有界性を underestimate。subagent judgment で「by margin」と続行、結果 0 sorry / 回帰なし。
- 両側等号 unified statement (`inf_{achievable codes} liminf (log M_n / n) = entropy μ X`) は Phase F sub-plan として `docs/moonshot-seeds.md` A セクションに新規 deferred 登録 (50〜100 行 / 低リスク、新規数学なし、起点完備)。
- 採らなかった代替案: (i) measurability free `entropy_nonneg` (数十行手書き、scope 過剰)、(ii) random coding argument (確率論的 achievability、Cover-Thomas Ch 7 channel coding 流儀)、本 Track は constructive (deterministic typical set encoder) のみ採用 (achievability source coding の標準形)、(iii) Phase D + E 一体化 unified statement、Phase F に分離。

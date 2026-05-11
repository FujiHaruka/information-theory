# AEP Phase D — 源符号化定理 weak converse — ボトルネック分析

将来 (a) Mathlib `Filter.liminf` の `IsCoboundedUnder` 要件を事前検出するツール、(b) `iIndepFun` ⟷ `Pairwise IndepFun` の lift 自動判定、(c) Pi 化情報量補題 (entropy / KL の i.i.d. n 倍) ファミリの上流 PR 提案、を判断するベースライン記録。

**定量データ**: 本 Track は Track 1〜3 と同 session / 同 prompt_id 内のサブエージェント起動として実行されたため、合算 metrics として記録。Track 単独抽出は不可。同 session 全体は [docs/metrics/aep-source-coding.metrics.md](../metrics/aep-source-coding.metrics.md) を参照。本ファイルは定性記録に集中する。

## 0. 対象問題と成果物

`docs/moonshot-seeds.md` 「A. 直接 deferred」項目 "AEP Phase D (源符号化定理 weak converse)" の本実装。AEP Phase A〜C (`aep_inProbability` / `aep_ae` / typical set 3 性質) を起点に源符号化定理の weak converse 半分:

```
∀ ε > 0, X i.i.d. base, c_n / d_n が P{ d_n(c_n(X^n)) ≠ X^n } → 0 を満たすなら
  liminf_n (log M_n / n) ≥ entropy μ X
  -- 仮定: hM_bdd : ∃ R, ∀ n, log M_n / n ≤ R (rate-bounded、実用 trivial)
  -- 仮定: iIndepFun (Phase A〜C の Pairwise IndepFun から強化)
```

成果物:

- `Common2026/Shannon/AEP.lean` (+368 行 → 累計 ~800 行) — Phase A: `entropy_jointRV_eq_n_smul` (Pi 化 entropy chain rule、Han route) / Phase B: Slepian-Wolf 流儀 4-step skeleton 再演 (Step C DPI 省略) / Phase C: `source_coding_weak_converse_aep` (`Filter.liminf` 形主定理)
- `lake env lean Common2026/Shannon/AEP.lean` silent / `lake build Common2026.Shannon.AEP` 緑
- 行数 +368 は plan target 210〜350 を 18 行超過、ceiling 450 内 (主因は §4.1 の `IsCoboundedUnder` discharge plumbing)

## 1. 問題のキャラクター

「Mathlib Filter API の semantics 罠 (`IsCoboundedUnder`)」+「Pi 化情報量補題系の自前構築」+「Mathlib に直接 callable な single-shot converse がないため skeleton 再演」の 3 軸。Track 3 (Stein converse) と類似構造だが、本 Track は Filter API plumbing が中心 (Stein は log-sum 下界 + DPI が中心)。

過去 proof-log との比較:
- 「Pi 化 chain rule の自前 induction」軸は Track 3 ([proof-log-stein-converse.md](proof-log-stein-converse.md) の `klDiv_pi_eq_n_smul` 98 行) と完全に並ぶ。**Pi 化 entropy chain rule + Pi 化 KL chain rule はペアで上流 PR 化候補**。
- 「single-shot converse 直接 callable でない、骨格再演」軸は Track 3 と Slepian-Wolf converse ([proof-log-slepian-wolf.md](proof-log-slepian-wolf.md))（同セッション外）の流れに乗る。
- 「`Filter.liminf` の cobounded 罠」軸は本 Track で初出。Track 5 (AEP Phase E) や別 deferred (Stein Tendsto 統合) でも再発する見込み。

## 2. 数学的方針

### Phase A: Pi 化 entropy chain rule

`entropy μ (fun ω i : Fin n => Xs i ω) = n • entropy μ (Xs 0)` を i.i.d. 仮定下で。Han route (`Han.jointEntropy_chain_rule_finRange` で n 個の `condEntropy` 和に展開 → 各 `condEntropy` を `condEntropy_eq_entropy_of_indepFun` (mutualInfo bridge + `mutualInfo_eq_zero_iff_indep`) で marginal entropy に collapse → `entropy_eq_of_identDistrib` で `entropy μ (Xs i) = entropy μ (Xs 0)` に統一) で構築。direct `MeasurableEquiv.piFinSuccAbove` induction は撤退ライン準備のみで不要だった。

### Phase B: Slepian-Wolf 流儀 4-step skeleton

`shannon_converse_single_shot` 3 form は uniform `Msg` 仮定が `X^n` で破綻。代わりに `slepian_wolf_converse_X` (`Common2026/Shannon/SlepianWolf.lean:217`) と同形の 4-step を `X^n` 上で再演:

1. `H(X^n) ≤ H(Y^n) + H(X^n | Y^n)` — `mutualInfo_eq_entropy_sub_condEntropy` bridge
2. `H(Y^n) ≤ log M_n` — `entropy_le_log_card`
3. `H(X^n | Y^n) ≤ Fano(Pe_n)` — `fano_inequality_measure_theoretic`
4. assembly: `n · entropy ≤ log M_n + Fano(Pe_n)` → `entropy ≤ log M_n / n + δ_n` where `δ_n := h(Pe_n)/n + Pe_n · log|α|`

Slepian-Wolf converse とは bound 形が異なり、**Step C (DPI postprocess) は不要** (source coding は単一 RV で完結、Slepian-Wolf は side info reshape で必要)。

### Phase C: `Filter.liminf` 形主定理

`δ_n → 0` を `binEntropy_continuous` + `tendsto_one_div_atTop_nhds_zero_nat` で構築、`Filter.liminf_le_liminf` + `IsCoboundedUnder.of_frequently_le` (`hM_bdd` で discharge) で `entropy ≤ liminf (log M_n / n)` に。

数学的アイデアは Cover-Thomas 5.4.1 の標準論法 (新規ゼロ)。詰まりは Mathlib Filter API の semantics と Pi 値 reshape。

## 3. Mathlib 補題探索の実録

| 必要だったもの | クエリ | 試行 | 結果 |
|---|---|---|---|
| Pi 化 entropy chain rule (`H(X^n) = n · H(X)`) | loogle `entropy.*Measure.pi`, rg | 3 | **Mathlib + Common2026 両方不在**。自前構築 |
| `Filter.liminf_le_liminf` | loogle `Filter.liminf_le_liminf` | 1 | `Mathlib/Order/LiminfLimsup.lean:205` |
| `IsCoboundedUnder.of_frequently_le` | loogle `IsCoboundedUnder.of_frequently` | 1 | 既存 |
| `iIndepFun.indepFun_finset` | loogle | 1 | `Mathlib/Probability/Independence/Basic.lean:839` |
| `entropy_eq_of_identDistrib` | rg Common2026 | 1 | 既存 (`MeasureFano.entropy_eq_of_identDistrib`) |
| `condEntropy_eq_entropy_of_indepFun` | rg Common2026 | 1 | 不在、Phase A で自前構築 (mutualInfo bridge + `mutualInfo_eq_zero_iff_indep`) |
| `Tendsto.mul_const` (real) | loogle, rg | 2 | `Filter.Tendsto.mul_const` 不在 (`ENNReal.Tendsto.mul_const` のみ)、`.mul tendsto_const_nhds` で代替 |
| `binEntropy_continuous` | loogle | 1 | Mathlib 既存 |

「Mathlib に無かった」もの:

- **Pi 化 entropy chain rule** (`H((Xs i)_{i:Fin n}) = n · H(Xs 0)` for i.i.d.) — Mathlib + Common2026 両方不在。Han route (既存 `jointEntropy_chain_rule_finRange` + `condEntropy_eq_entropy_of_indepFun` 自前 + `entropy_eq_of_identDistrib` 既存) で 80 行構築。**Track 3 の `klDiv_pi_eq_n_smul` (98 行) とペアで上流 PR 候補** (両者とも `MeasurableEquiv.piFinSuccAbove` + Pi reshape を使う)。
- **`condEntropy_eq_entropy_of_indepFun`** (X ⫫ Y ⇒ `H(X | Y) = H(X)`) — Common2026 不在、Phase A で自前構築。`mutualInfo_eq_zero_iff_indep` + `mutualInfo_eq_entropy_sub_condEntropy` で 10 行。**上流 PR 候補**。
- **`Filter.Tendsto.mul_const`** (実数値) — `ENNReal.Tendsto.mul_const` は存在するが実数値版は名前で見つからず。`.mul tendsto_const_nhds` で組成可能なため critical ではないが、混乱 source。

## 4. 試行錯誤と後戻り

### 4.1 `Filter.liminf` の `IsCoboundedUnder` 罠

**症状**: `Filter.liminf_le_liminf` を呼ぶと `IsCoboundedUnder (· ≥ ·) atTop f` を要求される。実数値 `f := log M_n / n` の場合これは auto では通らない (`f` が unbounded above なら `liminf` は `sSup ℝ = 0` 規約により collapse、`cobounded` 仮定が structural に必要)。

**原因**: Mathlib の `Filter.liminf` は完備束で定義され、`ℝ` は `sSup ∅ = 0` のような pathological semantics を持つ。`IsCoboundedUnder (· ≥ ·)` は「無限に下から bound されない」を排除する条件で、実数値 atTop sequence では auto 合成不可。

**抜け方**: theorem signature に `hM_bdd : ∃ R, ∀ n, log M_n / n ≤ R` (rate-bounded 仮定) を追加し、`IsCoboundedUnder.of_frequently_le` で discharge。

**教訓**: Mathlib `Filter.liminf` の cobounded semantics は plan inventory 段階で見落とされやすい。Plan の Phase 0 inventory 軸 1 「Filter.liminf 完備」記述は cobounded condition を言及していなかった (本 proof-log 執筆時に plan 判断ログに amend 追記済)。代案 `EReal.liminf` 化 (`EReal` は完備順序で `sSup ℝ = +∞`) は statement 全体に coercion 波及するため不採用。**実用 (`M_n = 2^⌈nR⌉` rate-bounded codes) では `hM_bdd` は caller 1 行で trivial に提供可**。Common2026 既存の Slepian-Wolf converse / Stein converse も同様に rate-bounded 仮定下の statement で一貫する形式化スタイル。

### 4.2 Pi 値 reshape を `ℕ`-indexed `Xs` 上で実施

**症状**: Phase A で `iIndepFun.indepFun_finset` を `Fin n` 内インデックスで使おうとすると `S = {↑i}, T = (Finset.range i).image (Fin.castLE _)` のような Fin reshape が plumbing-heavy。

**原因**: `iIndepFun` の sub-family extraction は `Finset` 上の disjoint partition で動く。`Fin n` 内 reshape は `Fin.castLE` 経由の Finset 構築で軽くない。

**抜け方**: 元 `ℕ`-indexed `Xs` に戻り、`S = {i}, T = Finset.range i` という `ℕ` 上の Finset で `iIndepFun.indepFun_finset` を呼ぶ。`Finset.range i` の disjoint from `{i}` は `Finset.disjoint_singleton` で 1 行、`Finset` 内 Pi 値の reshape は不要 (各 indep block を `IndepFun.comp` で `(Xs i, prefix)` に投影するだけ)。

**教訓**: `iIndepFun` の sub-family extraction は **`Fin n` 内ではなく原 `ℕ`-indexed family 上で `Finset.range i` を使う** のが軽い。Han Phase D の自前 `MeasurableEquiv` (`fullSplitMEquiv` 等) より大幅に短い、後続 moonshot (Sanov / channel coding) で再利用候補。Plan の Phase A は `Fin n` 内 reshape を主路線にしていたが、実装中に subagent が反転判断。

### 4.3 Step C (DPI postprocess) の不要発見

**症状**: Plan は Slepian-Wolf converse の 4-step (`H = mI + condE` bridge → `mI ≤ log M` → `mI` の DPI postprocess → `condE` の Fano) を踏襲する想定だった。実装中に Step C (DPI postprocess) を assembly 上不要と判定。

**原因**: Slepian-Wolf converse は side info で reshape するため `mI(X; (Y_X, Y_Y))` の DPI postprocess (`mI(X; Y_X) ≤ mI(X; (Y_X, Y_Y))`) が必要。Source coding は単一 RV `X^n` で完結、`H(X^n) = mI(X^n; Y^n) + condE(X^n | Y^n)` の bridge から直接 `H(X^n) ≤ H(Y^n) + Fano` で済む (`mI(X^n; Y^n) ≤ H(Y^n)` は `entropy_le_log_card` 経由)。

**抜け方**: Step C を assembly から外し、`fano_inequality_measure_theoretic` を `condEntropy μ Xn Yn` に直接当てる。

**教訓**: Slepian-Wolf converse の skeleton を「鵜呑み写経」せず、source coding の RV 構造 (単一 vs multi-source) に応じて assembly を簡略化する判断が必要。Plan が「Slepian-Wolf 流儀 4-step」と書いていても、実装中に 3-step に減らせるかを確認すべき。

### 4.4 `Pairwise IndepFun → iIndepFun` の不可

**症状**: AEP Phase A〜C は `Pairwise IndepFun` (Etemadi SLLN に十分) を仮定。Phase D は `H(X^n) = n · H(X)` のため `iIndepFun` (mutual) が必須。逆方向 lift `Pairwise IndepFun → iIndepFun` を試したが Mathlib 不在 + 数学的に不可能 (Bernstein counterexample: pairwise indep だが mutual indep でない famous 3-RV 構成あり)。

**抜け方**: theorem entry point の hypothesis を `iIndepFun` に強化。`iIndepFun.indepFun` で AEP Phase A〜C の `Pairwise IndepFun` 形は auto derive できるため、AEP Phase A〜C の callers は影響なし。Phase D 単体の caller burden は仮定 1 本の置換のみ。

**教訓**: i.i.d. 仮定の強化は「statement 上の 1 ヶ所変更で auto derive 可能なら caller 全体への影響なし」が確認できれば許容。Mathlib `iIndepFun.indepFun` のような lift があるかの事前 inventory が plan 段階で重要 (今回は plan 段階で確認済、blocker としては事前 surfaced)。

## 5. ボトルネックではなかったもの

- **数学的アイデア**: Cover-Thomas 5.4.1 の標準論法、新規ゼロ。
- **AEP Phase A〜C plumbing 再利用**: `aep_ae` / typical set 3 性質は Phase D で直接呼ばず、`H(X^n) = n · H(X)` から組み立てたため独立に動いた。
- **`fano_inequality_measure_theoretic` の発火**: Common2026 既存、引数 4 つで一発。
- **`binEntropy_continuous` + `tendsto_one_div_atTop_nhds_zero_nat`**: Mathlib に揃っており `δ_n → 0` の証明は標準パーツの組み合わせで済んだ。
- **Han route の選択**: 撤退ライン準備していた direct 帰納より plumbing が薄く第一選択になった (実装前判断は Phase A 着手後に subagent が即決)。
- **コンテキスト長**: 1M context + subagent 委任で圧迫感なし。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたコスト |
|---|---|---|
| 高 | Pi 化情報量補題ファミリ (entropy / KL / mutualInfo の i.i.d. n 倍) の Mathlib 不在検出 + 自動 induction skeleton 生成 | Phase A 全体 (~80 行 / 数時間) |
| 高 | Mathlib `Filter.liminf` の `IsCoboundedUnder` 要件の事前検出 (実数値 atTop sequence で `liminf_le_liminf` 呼び出しを risky として flag) | §4.1 の design 判断、`hM_bdd` 仮定追加で済むがインベントリ段階で surface すべき |
| 中 | `iIndepFun` ⟷ `Pairwise IndepFun` の lift 自動判定 (`iIndepFun.indepFun` 既存、逆は数学的不可) | §4.4 の事前確認 (plan 段階) |
| 中 | `iIndepFun.indepFun_finset` の `Fin n` 内 reshape vs `ℕ`-indexed `Finset.range` の plumbing コスト比較ヒント | §4.2 の方針反転判断 |
| 中 | Slepian-Wolf converse skeleton の RV 構造 (単一 vs multi-source) に応じた assembly 簡略化提案 | §4.3 (Step C 削除) |
| 低 | `Filter.Tendsto.mul_const` (実数値) の Mathlib 命名 hint (`ENNReal` 版のみある混乱回避) | §3 表内の混乱 1 件 |

## 7. 補足

- 本 Track は orchestration (Track 1 → Track 2 → Track 3 → Track 4) の 4 番目で、同 session / 同 prompt_id 内のサブエージェント起動として実行。proof-log は Track 単位で分離、metrics は session 単位なので Track 4 単独抽出は不可。
- 上流 PR 候補 (本 Track 由来): `entropy_jointRV_eq_n_smul` (Pi 化 entropy chain rule、Track 3 の `klDiv_pi_eq_n_smul` とペア)、`condEntropy_eq_entropy_of_indepFun`、`Filter.Tendsto.mul_const` の実数値版命名整理。
- Plan ファイル (`docs/shannon/aep-source-coding-plan.md`) の判断ログは本 proof-log 執筆時に追記済 (Han route 採用 / Step C 不要 / `hM_bdd` 仮定追加の 4 件)。
- 採らなかった代替案: (i) `EReal.liminf` 化で `hM_bdd` 仮定を削除 — statement 全体に EReal coercion が波及して可読性低下、不採用、(ii) AEP Phase A〜C の `Pairwise IndepFun` を `iIndepFun` に強化 — 既存 callers (`aep_inProbability` 系) への波及範囲が読みにくく、Phase D 単体強化で済むため不採用、(iii) Pi 化 entropy chain rule の direct `MeasurableEquiv.piFinSuccAbove` induction — Han route の方が plumbing が薄く第一選択になった。
- Track 4 は本セッション最大の単一 Track (+368 行)。ceiling 450 内で収まったのは subagent の (a) Han route 即決、(b) Step C 省略判定、(c) `ℕ`-indexed reshape 反転判断の 3 つの設計判断による。

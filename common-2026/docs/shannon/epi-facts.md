# EPI 確定事実台帳

> family `epi` の確定事実の**単一の真実源**。フォーマット規約 → `CLAUDE.md`「Plan / docs hygiene」。
> プラン本文に同じ事実を再記述しない (散在防止)。プランからはこの台帳の行にリンクする。
> **確信度**: `machine` (機械検証可、コマンド併記) / `loogle-neg` (Found 0、query 併記) / `human-judgment` (解析的壁判断、**過大/過小評価しうる低信頼**)。

## 壁 (未解消、コード `@residual(wall:slug)` が SoT)

slug が code に存在する = 壁未解消。`plan_lint` はこれを照合し「plan が壁扱いだが slug 消失」を STALE 判定する。壁の真偽 (本当に Mathlib 壁か / 実は通れるか) は `human-judgment` なので独立 pivot で再確認する (→ CLAUDE.md「Verification」)。

| 壁 (slug) | 確信度 | 再検証コマンド (slug 存在 = 未解消) | last-verified | 場所 / 備考 |
|---|---|---|---|---|
| `wall:debruijn-integration` | human-judgment | `rg '@residual\(wall:debruijn-integration\)' InformationTheory/` | — | `FisherInfoV2DeBruijn.lean` de Bruijn 恒等式の genuine discharge |
| `wall:fisher-finiteness` | human-judgment | `rg '@residual\(wall:fisher-finiteness\)' InformationTheory/` | — | `FisherInfoV2DeBruijnAssembly.lean`(8) + `FisherConvBound.lean`(1)。**shared wall (9 consumer)**、集約済 |
| `wall:entropy-finiteness` | human-judgment | `rg '@residual\(wall:entropy-finiteness\)' InformationTheory/` | — | `FisherInfoV2DeBruijnAssembly.lean` |
| `wall:stam-blachman` | human-judgment | `rg '@residual\(wall:stam-blachman\)' InformationTheory/` | — | `EPIScoreCrossTermOrth.lean` score cross-term 直交 |

## 達成 (proof-done / sorryAx-free — キャッシュでなく再導出レシピ)

P1 規約により「X は sorryAx-free」を prose で確定キャッシュしない。下の行は**再検証レシピ + 最後に通った commit**であって、信用する代わりに必要時に再実行する。

| 主張 | 確信度 | 再検証コマンド | last-verified | 備考 |
|---|---|---|---|---|
| 密度+正則性つき EPI (`entropy_power_inequality_of_density`) が sorryAx-free | machine | `#print axioms entropy_power_inequality_of_density` (経由 `EPIDensityForm.lean`) | 991a718 | two-time 3-noise route、独立監査済 (`@audit:ok`) |
| 無条件 dispatch headline (`entropyPowerExt_add_ge_dispatch_skeleton`) は **sorryAx-free (全 4 枝 proof-done)**。`wall:epi-finite-entropy-ac-classical` は**解消済** (case-1 `entropyPowerExt_add_ge_finite_ac` が有限分散=smoothing / 無限分散=route T で両枝 closure) | machine | `#print axioms entropyPowerExt_add_ge_dispatch_skeleton` = `[propext, Classical.choice, Quot.sound]`、`rg '@residual\(wall:epi-finite-entropy-ac-classical\)' InformationTheory/` = Found 0 | 9163283 | 2026-06-08 機械確認で旧「sorryAx 残」記述が STALE と判明し訂正。ただし dispatch は依然 21 precondition (16 integrability for case2/2symm + 5 finite-entropy) を持つ。**無条件化 = method-Y gateway で singular cases (case2/2symm) の 16 integrability を除去 + 有限枝 bridge で case-1 を split** が Phase 5 endgame |
| `debruijnIdentityV2_holds_assembled` は 6 genuine atom + named gap (`wall:fisher-finiteness` 等) に構造化、sorryAx-free では**ない** | human-judgment | `rg 'wall:' InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean` | — | atom file は genuine、assembly は壁残 |
| route β' (W-Y2) gateway ⊤ 枝 `differentialEntropyExt_top_of_indep_add_unconditional` (`h(W)=⊤ ⟹ h(W+V)=⊤`、a.c.+独立) が sorryAx-free **かつ (i-a) `differentialEntropyExt_indep_add_eq_add_klDiv` を非継承** | machine | `#print axioms differentialEntropyExt_top_of_indep_add_unconditional` = `[propext, Classical.choice, Quot.sound]`、対して `#print axioms differentialEntropyExt_indep_add_eq_add_klDiv` は `sorryAx` 保持 (経由 `EPIUncondTruncationLimit.lean`) | 803e489 | truncation 近似が無条件版②を genuine 迂回。独立 honesty-auditor all-OK (under-hyp 反例試行 PASS、`_unconditional` 命名 NOT name-laundering)。ファイル全体 0 sorry/0 @residual |
| **full 無条件 gateway** `entropyPowerExt_mono_add_unconditional` (`W a.c. ∧ W⊥V ⟹ N(W+V)≥N(W)`) + `differentialEntropyExt_mono_add_unconditional` (`h(W)≤h(W+V)`) が sorryAx-free **かつ (i-a) 非継承** | machine | `#print axioms entropyPowerExt_mono_add_unconditional` / `differentialEntropyExt_mono_add_unconditional` = `[propext, Classical.choice, Quot.sound]` (経由 `EPIUncondTruncationLimit.lean`) | 9163283 | 3 枝 assembly (⊥=bot_le / ⊤=route β' / 有限=un-truncated per-fibre Gibbs `differentialEntropyExt_mono_add_of_integrable`)。有限枝 bridge `differentialEntropyExt_integrable_of_finite` (有限 h+a.c.⟹integrable) 新規。3 補題とも独立 honesty-auditor all-OK (`@audit:ok`)。**S5 = 方針 Y gateway 完全 proof-done**。残 = headline wire (Phase 5/S4) |

## Mathlib 不在 (loogle Found 0 / 注意付き)

| 主張 | 確信度 | query | last-verified | 備考 |
|---|---|---|---|---|
| `BrascampLieb` 名の宣言は Mathlib に無い | loogle-neg | `loogle "BrascampLieb"` → Found 0 | 2026-06-07 | 無限分散 EPI 経路で必要な sharp 畳み込み不等式の一部 |
| 無限分散 classical EPI = genuine Mathlib 壁 (sharp Young / Brascamp-Lieb 畳み込み不等式) | human-judgment | — (bare name 検索では判定不能) | 2026-06-07 | **注意**: `loogle "Lieb"` は 128 件返す (Lieb 凹性等、**無関係**)。bare-identifier 失敗 ≠ 不在の逆で、bare-identifier ヒット ≠ 必要 lemma 存在。sharp 畳み込み版は要 targeted 検索。低信頼 |
| Mathlib の Jensen は全て `Integrable (g∘f)` 要求 (「φ 下に有界 → RHS +∞ 許容」版は不在) | machine | `ConvexOn.map_integral_le` (`Mathlib/Analysis/Convex/Integral.lean:199`) / `map_average_le:130` verbatim に `hgi : Integrable (g∘f)` | 2026-06-07 | W-Y1 +∞ 伝播の B_{W+V}<⊤ を ⊤ 枝 (A_W=⊤) で出せない根拠。affine-minorant 自作 `ConvexOn.exists_affine_le_real` (`Approximation.lean:98`) で Jensen-下界を組むのが回避路 (§7-3 T1) |
| `Measure.conv` の entropy-monotone / essSup peak bound / lintegral Jensen は Mathlib 不在 | loogle-neg | `loogle '"MeasureTheory.Measure.conv", \|- _ ≤ _'` → 0、`'"MeasureTheory.essSup", "…conv"'` → 0、`"MeasureTheory.lintegral, Convex, \|- _ ≤ _"` → 0 | 2026-06-07 | W-Y1 の A_{W+V}=⊤ (裾発散伝播) に off-the-shelf な conv-entropy-monotone が無い根拠。攻略は EReal-conditioning (§7-2 route α) |

## 判断ログ (この台帳固有)

1. **seed 作成 (2026-06-07)**: P2 実装の worked example。`loogle "Lieb"` 128件 / `"BrascampLieb"` 0件で「bare name 検索の罠」を確認、無限分散壁を `loogle-neg` でなく `human-judgment` に分類。

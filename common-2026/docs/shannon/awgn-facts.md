# AWGN family — settled-facts ledger

> family `awgn` の確定事実の**単一の真実源**。フォーマット規約 → `CLAUDE.md`「Plan / docs hygiene」。
> 列 = claim / confidence / 再検証コマンド / last-verified (commit) / notes。
> confidence: `machine` (axiom/sorry 機械検証、再検証コマンド必須) / `loogle-neg` (Found 0、query 併記) / `human-judgment` (解析的壁/overturn 判断、低信頼、独立 pivot で再確認)。
> プラン散文に settled fact をキャッシュせず、ここにリンクする (re-derive > cache)。

## 達成 (proof-done / sorryAx-free — キャッシュでなく再導出レシピ)

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| `awgn_converse` (`AWGN/Converse.lean`) は **完全 transitively sorryAx-free** | machine | `#print axioms InformationTheory.Shannon.AWGN.awgn_converse` (= `[propext, Classical.choice, Quot.sound]`) + `lake env lean InformationTheory/Shannon/AWGN/Converse.lean` (silent) | `61b32e6` | converse の 3 Mathlib 壁すべて genuine closure 後の到達状態。Cover-Thomas 9.1.2 converse の headline |
| achievability **continuous-AEP 集中エンジン** `pi_empirical_mean_concentration` / `pi_empirical_mean_typical_mass` (`AWGN/AchievabilityAEP.lean`) sorryAx-free | machine | `#print axioms InformationTheory.Shannon.AWGN.pi_empirical_mean_concentration` (= `[propext, Classical.choice, Quot.sound]`) + `lake env lean InformationTheory/Shannon/AWGN/AchievabilityAEP.lean` (silent) | `(本セッション)` | **Wall 1 false-wall overturn の gateway atom**。inventory axis2 の T-2 判断は「SLLN (a.s. 収束=無限積測度) で 200-400 行 → 撤退」だったが、**AEP 質量集中には Chebyshev 弱法則 (有限 n、無限積不要) で十分**。`variance_sum_pi` + `meas_ge_le_variance_div_sq` で組成。inventory はこの経路を見落としていた。abstract (一般 μ + L² 統計量 φ) ゆえ Wall 1 (ii)(iii)・Wall 3 にも再利用可 |

## 壁 false-wall overturn (human-judgment overturn — 記録価値大)

3 壁とも当初 Mathlib 壁と判断されたが、独立 pivot で false-wall と判明し genuine closure。overturn の論理を 1 行ずつ残す (同型の overturn を他家系で再利用するため)。

| 壁 (slug) | overturn の論理 (覆した route) | 後継 decl (genuine) | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|---|
| `awgn-mi-bridge` (per-letter MI = h(Y_i) − h(noise)) | mixture→compProd 因子分解 + generic continuous-channel MI chain rule asset (上流 relocate 済) + 混合 log-density 可積分性 + fibre entropy 平行移動不変 | `awgn_per_letter_mi_bridge_genuine` (`AWGN/Converse.lean:549`、`@audit:ok`) | `#print axioms InformationTheory.Shannon.AWGN.awgn_per_letter_mi_bridge_genuine` | `61b32e6` | commit `9d5edf1` + 監査 `34e58e7` |
| `multivariate-mi` (I(W;Y^n)/I(X^n;Y^n) finiteness) | ENNReal chain rule 循環は **Real-form を経由した場合の話**で、直接 `klDiv_ne_top` (discrete-input compProd chain rule) で回避 | `awgnConverseJoint_pair_mi_ne_top` (`AWGN/ConverseDischarge.lean:933`、`@audit:ok`) | `rg '@audit:ok' InformationTheory/Shannon/AWGN/ConverseDischarge.lean` (該当 private lemma が genuine) | `61b32e6` | commit `0b71235` + 監査 `a6dc973` |
| `awgn-continuous-mi-chain-rule` (I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)) | chain rule は **X-input 連続 kernel measurability が真の gap** だが、**W-input route (離散 Fin M)** で kernel measurability を自由化 (決定的 DPI) して回避 | `awgnContinuousMIChainRule_holds` (`AWGN/Walls.lean:2074`、`@audit:ok`) | `#print axioms InformationTheory.Shannon.AWGN.awgnContinuousMIChainRule_holds` | `61b32e6` | gateway atom = generic n-D MI 分解 `mutualInfoOfChannel_toReal_eq_log_density_sub` (`ChannelCoding/MIDecomp.lean:457`)。commit `b95e788`〜`534f884` + 監査 `61b32e6`。`hN` / `NeZero M` は regularity precondition (監査確認) |

## 残存壁 (未解消、コード `@residual` が SoT)

| 壁 (slug / 定義) | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| X-input kernel measurability gap (`Measure.pi (gaussian (x i) N)` の x 可測性、`IsParallelGaussianKernelMeasurable`) | loogle-neg | `loogle "MeasureTheory.Measure.pi, Measurable"` → 5 hits (lintegral/marginal 系のみ、parallel Gaussian kernel の x-measurability は該当 0) | `61b32e6` | `ParallelGaussian/Basic.lean:84` で deferred (`IsParallelGaussianKernelMeasurable` hyp 形)。chain-rule の X-input route はこれに当たるため **W-input route (離散 Fin M) で回避済** (converse は無影響)。真の Mathlib gap |
| `awgn-continuous-aep-gaussian` (Wall 1, `continuousAepGaussian_holds`) | human-judgment | `rg '@residual\(wall:awgn-continuous-aep-gaussian\)' InformationTheory/Shannon/AWGN/Walls.lean` | `61b32e6` | **sub-bound (i) のエンジンは genuine 化済 (下記 achievability gateway 参照)**。残るは joint AWGN 法則への wiring + klDiv (ii)(iii) bound。inventory の T-2 判断は category-(b) "writable but long" のスコープ判断であり hard 壁ではない |
| `awgn-random-coding-bound` (Wall 2, `awgnRandomCodingBound_holds`) | human-judgment | `rg '@residual\(wall:awgn-random-coding-bound\)' InformationTheory/Shannon/AWGN/Walls.lean` | `61b32e6` | union bound + Fubini。Wall 1 の AEP に依存 |
| `awgn-power-constraint-honest` (Wall 3, `awgnPowerConstraintHonest_holds`) | **machine (refuted)** | numeric: `N=1,P_target=3,R=0.5 ⇒ P'≈2.359, ψ(chi-sq LD rate)≈0.016 ≪ R` (docstring の FALSE-STATEMENT FINDING 参照) | `(本セッション)` | **⚠️ slug 誤分類: wall でなく false-statement**。`∀m`-over-`M=⌈exp(nR)⌉` 形は独立積で `q^M ≈ exp(-exp(n(R-ψ)))`、`R>ψ` で `→0`。R が capacity 近傍で `ψ≪R` ゆえ充足不能。`@audit:retract-candidate(false-statement)` 付与済。標準解は expurgation (期待割合 → 0、指数 rate 不要)。statement-fix 要 |

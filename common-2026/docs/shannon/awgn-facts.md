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
| X-input kernel measurability gap (`Measure.pi (gaussian (x i) N)` の x 可測性、`IsParallelGaussianKernelMeasurable`) | loogle-neg | `loogle "MeasureTheory.Measure.pi, Measurable"` → 5 hits (lintegral/marginal 系のみ、parallel Gaussian kernel の x-measurability は該当 0) | `61b32e6` | `ParallelGaussian/Basic.lean:84` で deferred (`IsParallelGaussianKernelMeasurable` hyp 形)。chain-rule の X-input route はこれに当たるため **W-input route (離散 Fin M) で回避済** (converse は無影響)。真の Mathlib gap。**Wall 2 の codebook-kernel 可測性とは別物** (後者は location-varying でなく `awgnCodebookKernel` で discharge 済) |

> **achievability 3 壁 (Wall 1/2/3) は壁でなく statement-fix/削除と確定** (M0、2026-06-12)。残存壁
> テーブルから除外し、下記「achievability decomposition の確定 (D1-D4)」に移管。3 壁の `@residual(wall:…)`
> はいずれも閉じる壁を指さない (D1=(ii)削除/D2=false lemma retire/D3=per-codeword 再 state)。コード側の
> `@audit:retract-candidate(false-statement)` が SoT。

## achievability decomposition の確定 (D1-D4、2026-06-12、M0 で feasible 確定)

「achievability 3 壁に挑戦」した結果、**3 壁すべてが hard な Mathlib gap ではなく、staged
migration で検証されなかった足場であり、個別に false/mis-stated** と判明した (converse の
false-wall overturn の逆向き = 「壁と思ったら statement が偽だった」)。M0 で **正しい
true-statement 集合 (D1-D4) を 2 subagent の独立検証により feasible 確定** (NO-GO なし)。

- **D1 — Wall 1 `continuousAepGaussian_holds`**: ∃可測A + **2 bounds のみ** ((i)mass + (iii)indep-pair)
  に縮小。**(ii) volume bound は削除** — consumer が破棄済 + union bound 第2項 mass は (iii) が担当
  (volume counting とは別軸) ゆえ load-bearing でない。false klDiv-to-volume を削除で honest 化。
  `jointDifferentialEntropyPi` 系資産は achievability 不要化 (converse 側資産)。
- **D2 — Wall 2 `awgnRandomCodingBound_holds` は壁でなく false lemma**: retire/削除。genuine
  union-bound lemma (仮称 `awgn_random_coding_union_bound`) を `AchievabilityDischarge.lean` に新設し、
  decoder = `jointTypicalDecoder A` 固定、AEP output (i)(iii) を hyp に thread (modular composition、
  load-bearing bundle 非該当)。**kernel 可測性は壁でない** (既存 `awgnCodebookKernel` で discharge 済、
  consumer `:998-1028` 通過済)。
- **D3 — Wall 3 `awgnPowerConstraintHonest_holds`**: `∀m`-mass false 形 → **per-codeword expurgation 形**
  `∀m, mass{c | ∑ᵢ(c m i)²>nP}≤ε`、engine を `φ=x²` で適用 (4次モーメント有限、指数 rate 不要)。
  2-stage `Measure.pi` 形維持で Walls.lean に残せる。
- **D4 — consumer restructure**: Wall 1 destructure を (i)(iii) 保持に変更、all-or-nothing barrier
  `g c := ∑_m Pe + M·𝟙_{∃m violate}` → per-codeword 合算 `g c := ∑_m (Pe c m + 𝟙_violate m)` に再構築。
  worst-half / reindex 機構は signature 不変で再利用。
- **headline は converse のみ genuine**。achievability headline `awgn_achievability` は F-1 park
  (`sorry + @residual(plan:…)`) のまま。3 壁の `@residual(wall:…)` は全て
  `@audit:retract-candidate(false-statement)` 併記済 (slug は wall でなく false-statement が正)。
- 詳細 plan → [`awgn-achievability-walls-discharge-plan.md`](awgn-achievability-walls-discharge-plan.md)
  (escalation 済: 「3 壁 discharge」→「decomposition 再設計」、M0 で D1-D4 feasible 確定)。

## M0 確定事実 (2026-06-12、decomposition 再設計の verbatim 検証、再検証コマンド付き)

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| import 構造に cycle なし: `AchievabilityAEP` (AWGN 依存ゼロ) → `Walls.lean` → `AchievabilityDischarge.lean`、`Walls.lean` に `import ...AchievabilityAEP` 追加可 | human-judgment | `lake env lean InformationTheory/Shannon/AWGN/Walls.lean` (import 追加後 silent) で確認 | `(本セッション)` | D1/D2 配置の前提 (engine を Walls に import、union-bound lemma は kernel/decoder が local な AchievabilityDischarge に新設) |
| `klDiv_pi_eq_sum` (`MIChainRule.lean:249`) / `klDiv_prod_eq_add` (:230) の型クラス前提 = **`IsProbabilityMeasure` のみ** (SigmaFinite/IsFiniteMeasure 不要)、両者 sorryAx-free | machine | `#print axioms InformationTheory.Shannon.klDiv_pi_eq_sum` + 同 `klDiv_prod_eq_add` (= `[propext, Classical.choice, Quot.sound]`) + signature Read で `[...]` 前提確認 | `(本セッション)` | D1 (iii) indep-pair の klDiv 積分解。engine の `IsProbabilityMeasure` 維持要件と整合 |
| `jointDifferentialEntropyPi_pi_eq_sum` (`ParallelGaussian/Converse/Core.lean:145`) 結論形 = heterogeneous `jointDifferentialEntropyPi (Measure.pi μ) = ∑ i, differentialEntropy (μ i)` (i.i.d. 特殊形でない)、sorryAx-free | machine | `#print axioms InformationTheory.Shannon.ParallelGaussian.jointDifferentialEntropyPi_pi_eq_sum` (= `[propext, Classical.choice, Quot.sound]`) | `(本セッション)` | **D1 で (ii) 削除につき achievability では不要化** (converse 側資産)。記録は (ii) 旧 statement-fix の検証履歴 |
| `MemLp φ 2` (per-letter log-density が L²): Mathlib 直接補題なし (`memLp_id_gaussianReal` は id のみ)。in-project `integrable_density_log_density_of_gaussian` (`DifferentialEntropy.lean:86`) の二次多項式分解スタイルで自家製 wiring 要 | loogle-neg | `loogle "MeasureTheory.MemLp, Real.log, MeasureTheory.gaussianReal"` (log-density 直接補題 0) + `rg "integrable_density_log_density_of_gaussian" InformationTheory/` | `(本セッション)` | **Phase 1 (i) の bottleneck**。Wall 3 (D3) の `φ=x²` は4次モーメント有限で素直 |
| 退化境界: `P=0` (Dirac) は `≪volume` を破る、`N=0` は `hv₂≠0` (klDiv closed form) を破る。両方とも既存 precondition (`hN:(N:ℝ)≠0` / `P>0`、`awgnPowerWitness_exists`) で吸収済 | human-judgment | docstring の precondition Read (`hN` / `P>0` / `awgnPowerWitness_exists` の存在) で確認 | `(本セッション)` | degenerate-boundary 過小評価の予防確認。statement は退化境界で死なない |

# Audit tags — code-as-source-of-truth 規約

honesty audit の状態 (genuine 完成 / 残課題 / 移行履歴) を **コード内に構造化マーカーで埋め込む** ことで、`rg` が単一の source of truth になる。snapshot 文書ではなく、コード自身が「現状どうなっているか」を答える。

## SoT 階層

1. **`sorry`** — primary residual marker。compiler-visible。「ここはまだ証明していない」を一語で表現する正直な道具。
2. **`@residual(<class>:<slug>)`** — 当該 `sorry` の分類補助。docstring または近接コメント。
3. **`@audit:*`** — bookkeeping (audit pass 済 / 別 plan に移管 / 後続版に置換済) 専用。残課題マーカーではない。

実装中に詰まったら **`sorry` + `@residual` で抜ける**。仮説束 (`*Hypothesis` predicate で結論型と同等の核を抱えさせる) や `:True` slot で `sorry` を回避するのは禁止 → CLAUDE.md「検証の誠実性」。

## Honesty 階層 (high → low)

honesty audit が評価する「正直さ」の階層。auditor の verdict 序列 + 実装側の選好順位はこの順で決まる。**一番 honest なのは `sorry`** — コンパイラ可視 + 「ごめんね」と明示している、隠蔽しようがない正直な未完成マーカー。

| Tier | 形態 | 含意 |
|---|---|---|
| **1** | `@audit:ok` (0 sorry / 0 @residual、auditor pass) | proof done、最高 honest |
| **2** | `sorry` + `@residual(<class>:<slug>)` | type-check done、新規実装の唯一の honest 撤退口 |
| **3** | bookkeeping (`@audit:superseded-by(slug)` / `@audit:retract-candidate(reason)`) | honest: 履歴 record / 削除候補。残課題マーカーではなく audit pass / 履歴のための metadata |
| **4** ⚠ | **legacy** `@audit:suspect(plan)` / `@audit:staged(wall)` / `@audit:defer(plan)` / `@audit:closed-by-successor(slug)` / 散文 `🟢ʰ` | 旧方針で「honest 残課題」として許容されていた load-bearing hypothesis / predicate bundling / 重複 closure 追跡形態。**新方針では defect 寄り** — tier 2 (`@residual(plan:<slug>)` 等) に書換待ち (移行レシピは下記)。auditor は発見しても即時 alert せず、incidental migration を推奨する程度の severity |
| **5** | `@audit:defect(*)` / 仮説型 ≡ 結論 (`:= h` 循環) / `:True` slot / 退化定義悪用 / name laundering / mathlib wall misuse | 真の honesty defect、即修正必要 |

**重要な含意**:

- **tier 2 (sorry + @residual) は tier 4 (suspect/staged) より strictly honest**。旧方針で「honest 名前付き仮説で抜く」と書かれていた撤退口は tier 4 で、新方針ではより上位の tier 2 に置き換える。
- **tier 4 (legacy) は無期限放置を意味しない**。新規実装で tier 4 declarations を touch するときに incidental に tier 2 へ migrate する (移行レシピ → 本ファイル下部 + [[sorry-based-migration]])。
- **auditor の verdict**: tier 5 を見つけたら即 rewrite recommend (commit revert)。tier 4 を見つけたら incidental migration recommend (緊急性低)。tier 2 の `@residual` 分類検証が主たる仕事。
- **実装側の選好**: 詰まったら必ず tier 2 を選ぶ。tier 4 を新規作成するのは禁止 (CLAUDE.md「検証の誠実性」)。

## 監査スコープ — honesty の 4 check (SoT)

honesty audit は declaration の signature + body に対し以下 4 つを独立に検査する。`honesty-auditor-core.md` の判定 doctrine もこの 4 check を実装する (二重定義せず本節を SoT とする)。

1. **非循環 check**: 仮説型 ≡ 結論型で body が `:= h` (循環) になっていないか。
2. **非バンドル check** (load-bearing): 証明の核心を `*Hypothesis` / `*Reduction` / `IsXxxClaim` predicate にまとめて仮説で渡し、body は機械的展開だけ、という構造になっていないか (regularity hyp は precondition なので OK)。
3. **退化/`:True` check**: vacuous shape / `:True` slot / 退化定義悪用で意味を空にしていないか。
4. **sufficiency check** (仮説 ⊢ 結論): 仮説群から結論が **semantic に follow** するか。最低でも反例構成を 1 つ試みて棄却できるか確認する。derivative-of-gap / 不等式系の結論では特に「**差分形 `g'` か、比 (log) `g'` か**」を Stam 等の出口形と照合する (出口形を取り違えると非循環・非バンドルでも偽の含意を主張しうる)。

**非循環・非バンドル (check 1-2) は honesty の必要条件であって十分条件ではない**。両者を通っても check 4 (sufficiency) で結論が仮説から follow しなければ **false-as-framed** = tier 5 (`false_statement` / `false-hypothesis`)。CLAUDE.md「検証の誠実性」の tell「under-hypothesized / insufficient signature」に対応。

cross-ref (false-negative 事例): `csiszarGap1Source_deriv_le_zero` は audit:PASS 2026-05-27 を check 1-3 のみで通過したが、差分形 gap derivative が plain Stam から出ない false-as-framed で、check 4 欠落による false negative だった (closure → `epi-csiszar-ratio-reframe-plan`)。

## 動機

- snapshot 文書 (defect-101 report 等) は **書いた瞬間から陳腐化** する。defect 数が変わっても文書は更新されない。
- 散文表現 (`🟢ʰ`, `(未着手)`, "NOT a discharge", "load-bearing hypothesis") が併存していると **集計不能** + 表現ゆれで grep 信頼度が落ちる。
- 監査で発見した新規 issue を「次セッションのタスク」に保管するのではなく、**発見した場所 (= 当該 docstring)** に埋め込めば、タスクリストが肥大化しない。

## 語彙

### `@residual(<class>:<slug>)` — 残課題分類 (sorry に併走)

各 `sorry` には対応する `@residual(...)` タグを 1 つ持たせる。

| Class | 意味 | Slug 規約 | 例 |
|---|---|---|---|
| `plan` | 別 plan で closure 予定 | plan filename stem (no `.md`) | `@residual(plan:epi-stam-closure)` |
| `wall` | Mathlib に未整備の壁。長期残課題 | wall name (下記 register) | `@residual(wall:stam)`、`@residual(wall:n-dim-gaussian-aep)` |
| `defect` | 旧 defect の fix 待ち残置 (signature は honest 化済、body だけ `sorry`) | defect kind (下記語彙) | `@residual(defect:circular)` |

#### Wall name register

`@residual(wall:<name>)` の `<name>` は以下から選ぶ。新規追加時は本 register に直接追記 (divergence 防止: 「stam」と「stam-inequality」が併存しないように)。

| Wall name | 意味 | 関連 textbook 節 |
|---|---|---|
| `stam` | Stam の不等式 (Blachman score-of-convolution identity)、Fisher 情報の畳み込み | Ch.17 EPI |
| `stam-step2-density` | Stam 不等式 Step 2-3 の density-level 解析核: 条件付き Cauchy-Schwarz (`s_Z(z)² ≤ E[(λ s_X + (1-λ) s_Y)² \| X+Y=z]`) を `p_Z` に対し積分して凸 Fisher 上界 `J(Z) ≤ λ² J(X) + (1-λ)² J(Y)` を得る部分 (λ 最適化で `IsStamCauchySchwarzOptimal` 形 `J(Z) ≤ J(X)J(Y)/(J(X)+J(Y))`)。Mathlib に score-of-convolution の condExp 表現も Fisher info 畳み込みも無い (a)+(b) 混合壁。`stam` (inverse harmonic-mean 結論形 `IsStamInequalityResidual`) と semantic 区別: 本壁は λ ごとの凸上界 = 結論の上流。`EPIStamInequalityBody.stam_step2_density_wall` で集約、旧 load-bearing hyp `IsStamCauchySchwarzOptimal` を `entropy_power_inequality_via_body` から除去した置換先。**[CLOSED 2026-06-04 (2026-05-31 owner-level pivot `epi-wall-reattack-plan`): genuine, no longer a wall]**。`IsStamInequalityHyp`/`IsStamInequalityResidual` を pointwise convolution 制約 + `IsBlachmanConvReady` bundle 同期 pivot した結果、`stam_step2_density_wall` (`EPIStamInequalityBody.lean:349`) が `convex_fisher_bound_of_ready` (genuine `convex_fisher_bound`) + `stam_lambda_min` + linarith で genuine に閉じた。`#print axioms isStamInequalityHyp_via_step3` (= `isStamInequalityHyp_via_body (stam_step2_density_wall ...)` の一行、`EPIStamStep3Body.lean:119`) = `[propext, Classical.choice, Quot.sound]` (sorryAx-free、本監査 2026-06-04 機械確認、chain `stam_step2_density_wall`/`isStamInequalityHyp_via_body`/`convex_fisher_bound_of_ready` も全て sorryAx-free)。active `@residual(wall:stam-step2-density)` 0 件 (この class を持つ実 sorry tactic トークンは 0、散文中の言及のみ) | Ch.17 EPI (Step 2-3, `stam_step2_density_wall`) |
| `csiszar` | Csiszár projection 系の Mathlib 未整備部 | Ch.11 |
| `n-dim-gaussian-aep` | n 次元 Gaussian 上の AEP / typicality | Ch.9 AWGN |
| `sphere-volume` | 高次元球の体積 + thin shell concentration | Ch.9 AWGN |
| `continuous-aep` | 連続分布上の典型集合 / AEP の Mathlib 不在部 | Ch.9 |
| `nyquist-2w-dof` | 帯域制限信号の 2W サンプル/秒 (prolate-spheroidal 次元定理) | Ch.9 Shannon-Hartley |
| `multivariate-mi` | 連続 `mutualInfo_pi_eq_sum` (多変量 MI 加法性) | Ch.9 ParallelGaussian |
| `joint-typicality-multi` | 多変数 joint typicality / Fano | Ch.15 MAC/BC/Relay |
| `epi-n-dim` | 多次元 EPI / n-dim Prékopa-Leindler の slice 解析的 readiness | Ch.17 BM |
| `uniform-max-entropy-on-convex-body` | 凸体上 uniform 分布 = max entropy の characterization (n-dim) | Ch.17.9.4 BM |
| `bm-additive-convex-body` | 凸体の Brunn-Minkowski 加法形 `vol(A) + vol(B) ≤ vol(A + B)` | Ch.17.9 BM |
| `fourier` | Fourier 解析の Mathlib 不在部 (帯域制限 / sinc 完全性等) | Ch.9 Shannon-Hartley |
| `epi-finite-entropy-ac-classical` | 無条件 EPI (`entropyPowerExt`, ℝ≥0∞) の case-1 残核: **両 a.c. + 両有限微分エントロピー** での古典 entropy power inequality `N(X+Y) ≥ N(X) + N(Y)`。集約先 `entropyPowerExt_add_ge_finite_ac` (`EPIUncondMixedCase.lean`)。2026-06-06 def-fix (`differentialEntropyExt` を正部・負部 EReal 差に訂正、false-statement defect 解消) 後の唯一の dispatch transitive sorry。**正則密度 sub-case は Phase A `entropy_power_inequality_of_density` (`EPIDensityForm.lean`, sorryAx-free) が genuine discharge 済** → 残るは (i) 一般有限分散 a.c. = smoothing→正則化 + endpoint 連続性 `heatFlowEntropyPower_continuousWithinAt_zero` の方針 X (`epi-case1-difference-g3-closure-plan`、closeable plan)、(ii) 無限分散 a.c. = Lieb-Young (sharp Young / Brascamp-Lieb) Mathlib 完全不在の genuine 壁 (`epi-uncond-truncation-lsc-inventory.md` thread D、loogle Found 0 機械裏取り)。`stam` (Fisher inverse superadditivity = EPI の Fisher 側 residual) と semantic 区別: 本 wall は entropyPowerExt-level の古典 EPI 結論そのもの (一般 a.c. 密度、Fisher 経由しない直接形も含む)。compound でなく `wall:` 単独が妥当 (独立 honesty audit 2026-06-06 PASS): 正則=closed/有限分散=plan/無限分散=wall を 1 named wall に集約、dominant 残核が無限分散 genuine 壁。infinite-entropy (±∞) 入力の `entropyPowerExt` 単調性 (+∞ 伝播) は別 residual `plan:epi-uncond-deffix-monotone-plan` (dispatch は finite-entropy precondition で scope、本 wall には含めない) | Ch.17 EPI (無条件化 case-1, `entropyPowerExt_add_ge_finite_ac`) |
| `epi-infinite-variance-classical` | 無限分散 a.c. 古典 EPI `N(X+Y) ≥ N(X) + N(Y)` (X, Y 両 a.c. + 両有限微分エントロピーだが **2次モーメント無限**)。**[CLOSED 2026-06-07: FALSE WALL、route T で genuine closure、no longer a wall]**。当初「Lieb-Young sharp Young / Brascamp-Lieb / Rényi-Lp 必須、Mathlib 完全不在の genuine 壁」と判定 (loogle Found 0 機械裏取り) だったが **FALSE WALL** と判明: route T (両成分同時 conditioning による compact-support 切詰 `condTrunc` → 有限分散 EPI 黒箱 `entropyPowerExt_add_ge_of_finite_variance` 再利用 → R→∞ で Gibbs + cross-entropy DCT による usc + per-n EPI 下界) で sharp Young を経ずに closure。集約先は `EPIInfiniteVarianceCapstone.lean` の `EPIInfiniteVarianceTruncation.entropyPowerExt_add_ge_infinite_variance` (case split: hent_sum 成立=route T headline / 非成立=`entropyPowerExt=⊤` で `le_top`、後者は P 版負部可積分 `integrable_negPart_negMulLog_map_sum` で h=−∞ 退化を回避)。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free、独立 honesty audit 2026-06-07 PASS、capstone 2 decl + 無条件 dispatch `entropyPowerExt_add_ge_dispatch_skeleton` まで sorryAx-free 機械確認)。旧 sorry wall (`EPICase1SmoothingLimit.lean:1407`) は削除済、dispatch は capstone に rewire 済。教訓: 「壁判定は反証を 1 度試みる」(CLAUDE.md Verification) — 当初の loogle Found 0 (ルート A の部品不在) は **別ルート (route T = truncation) の存在を否定しない**、conclusion-shape 検索でなく単一ルート想定で過大評価した典型。`stam` (Fisher 側 residual) と semantic 区別。 | Ch.17 EPI (無条件化 case-1 無限分散部, **CLOSED**) |
| `debruijn-integration` | de Bruijn identity の heat-flow path 経由積分形 (`derivAt_entropy_eq_half_fisher_v2`)、Stam (score-of-convolution Fisher 加法形) と semantic 区別。**[CLOSED 2026-06-04: genuine, no longer a wall]**。旧 sorry 壁 `debruijnIdentityV2_holds` を削除 (declaration として既に存在せず、`rg "theorem debruijnIdentityV2_holds\b"` = 0 件)、同 signature の genuine `debruijnIdentityV2_holds_assembled` (`FisherInfoV2DeBruijnAssembly.lean:3535`、6 atom 組立) に置換、consumer (`deBruijn_identity_v2` `FisherInfoV2DeBruijnGenuine.lean:51` / `csiszarLogRatioGap_hasDerivAt` `EPIStamToBridge.lean:697`) は genuine 結線。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free、本監査 2026-06-04 機械確認、3 declaration 全て)。active `@residual(wall:debruijn-integration)` 0 件 (この class を持つ実 sorry tactic トークンは 0、散文中の言及のみ) | Ch.17 EPI |
| `fisher-finiteness` | Gaussian convolution density `pX ∗ g_t` (t>0) の Fisher 情報有限性 `J(pX∗g_t) < ∞` (= `Integrable ((logDeriv (pX∗g_t))²·(pX∗g_t))`)、任意確率密度 pX で成立 (`J(X+√t·Z) ≤ J(√t·Z) = 1/t`、convolution は Fisher を減らす)。**[CLOSED 2026-06-01 (commit `b5e13e2`): genuine, no longer a wall]**。`gaussianConv_fisher_le_inv_var` (`FisherConvBound.lean:385`) で genuine 証明完成: closure plan の conditional-expectation/disintegration framing を経由せず、各 `x` 固定の elementary pointwise Cauchy-Schwarz (Hölder p=q=2) で `(logDeriv p_s x)²·p_s x ≤ (1/s²)·∫(x-y)²pX g_s` を出し、Tonelli + Gaussian 2次モーメント `∫u²g_s = s` で `J(p_s) ≤ 1/s`。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free、独立 honesty audit 2026-06-01 機械確認、7 補助補題も全て sorryAx-free)。loogle `fisherInfo`/`Blachman` = unknown identifier (Mathlib gap honest だった)。consumer `convDensityAdd_fisher_integrable` (Assembly:1560) は genuine 呼出に書換済、per-time de Bruijn `debruijnIdentityV2_holds_assembled` (Assembly:3514) は end-to-end sorryAx-free。active `@residual(wall:fisher-finiteness)` 0 件 (Assembly の 6 stale marker は除去 → `@audit:ok`)。`hpX_mass : ∫pX=1` は probability density 正規化 (regularity precondition、load-bearing でない)。`stam` (Fisher inverse の superadditivity = EPI 結論形) と semantic 区別: 本 wall は **convolution Fisher の有限上界** のみ | Ch.17 EPI (per-time de Bruijn `_chain_ibp_fisher`) |
| `entropy-finiteness` | Gaussian convolution density `pX ∗ g_t` (t>0) の **微分エントロピー有限性** 系 integrand integrability: `Integrable (negMulLog (pX∗g_t))` (= `∫ -p log p < ∞`、`h(X+√t·Z) < ∞`) および IBP の log-factor integrability `Integrable ((-log p_t -1)·∂_x p_t)` / `Integrable ((-log p_t -1)·∂²_x p_t)`、任意確率密度 pX で成立 (smoothed density は bounded + Gaussian-tail)。**[CLOSED 2026-06-01 (commits `a28430e` + `8eea6b7`): genuine, no longer a wall]**。orchestrator の独立検算で「真の Mathlib 壁ではなく既存 `@audit:ok` 資産への plumbing、唯一の障害は import cycle」と判明 (`EntropyConvFinite.lean` が `Assembly` を import 不能で closure 資産にアクセスできなかった)。3 lemma を `FisherInfoV2DeBruijnAssembly.lean` に移設し genuine closure、`EntropyConvFinite.lean` は削除。`convDensityAdd_logFactor_deriv2_integrable` (:2286、`_chain_domination` envelope `s=t` から)、`convDensityAdd_logFactor_deriv_integrable` (:2361、`convDensityAdd_logFactor_poly_majorant` + 新規 `gaussGradMaj` gradient envelope)、`convDensityAdd_negMulLog_integrable` (:2516、majorant + conv 2次モーメント `hpX_mom`)、いずれも `@audit:ok` (独立 honesty audit 2026-06-01: sorryAx-free `[propext, Classical.choice, Quot.sound]` 機械確認、signature は `Integrable (...)` regularity output で de Bruijn/Fisher 核を bundle せず、`hpX_mass`/`hpX_mom` は regularity precondition)。active `@residual(wall:entropy-finiteness)` 0 件 (consumer 5 箇所の compound tag から除去済、`wall:fisher-finiteness` 単独残存)。`fisher-finiteness` (`J(p_t)<∞` = score の 2乗可積分) と semantic 区別: 本 wall は **log-factor (entropy) 側** の可積分性 (score 側ではない) — fisher-finiteness は別 genuine Mathlib 壁で残存 | Ch.17 EPI (per-time de Bruijn `_chain_ibp_fisher_ibp_step` の IBP integrability + `_chain_parametric` の `hint`) |
| `awgn-continuous-aep-gaussian` | Gaussian joint codebook+noise 上の AEP / typical set existence (mass / volume / independent-pair upper bound の 3 sub-bound、`klDiv` 形)。既存 `continuous-aep` の Gaussian specialization 形 (3 sub-bound を bundle した concrete shape、AWGN achievability core 専用) | Ch.9 AWGN (Phase B-0 = `IsContinuousAEPGaussian` body) |
| `awgn-random-coding-bound` | Gaussian random codebook 上の union bound + Fubini + IndepFun + AEP-chain (analytic content、average-over-codebook integral bound) | Ch.9 AWGN (Phase C-3 = `IsAwgnRandomCodingBound` body) |
| `awgn-power-constraint-honest` | chi-square SLLN on `gaussianCodebook` の analytic content (`P_cb < P_target` slack で SLLN 経由 mass concentration `≥ 1 - ε`、`gaussianCodebook M n P_cb` 上で `{c | ∀ m, ∑ᵢ (c m i)² ≤ n · P_target}`) | Ch.9 AWGN (Phase D-pivot = `IsAwgnPowerConstraintHonest` body) |
| `awgn-per-letter-integrability` | AWGN converse の per-letter output-law `negMulLog (rnDeriv) ` integrability (旧 `PerLetterIntegrabilityForConverse` body、`perLetterYLaw` 上の `Integrable`) | Ch.9 AWGN (Phase 3-α converse) |
| `awgn-continuous-mi-chain-rule` | non-iid AWGN codebook 上の continuous MI chain rule `I(X^n;Y^n) ≤ ∑ᵢ I(X_i;Y_i)` (旧 `ContinuousMIChainRuleForConverse` body)。既存 `multivariate-mi` と semantic 区別: `multivariate-mi` は iid joint 前提の `mutualInfo_pi_eq_sum`、本 wall は AWGN code が non-iid codebook のため iid 不要形 | Ch.9 AWGN (Phase 3-α converse) |
| `awgn-converse-markov-regularity` | AWGN converse joint 上の `IsMarkovChain W → encoder∘W → Y^n` (旧 `MarkovChainForConverse`)。Route B 撤退 (L-AWGNM5-1-α): encoder 非単射時の condDistrib factorization が genuine 化に measure-theoretic 構成を要するため shared sorry 化。**[CLOSED 2026-06-04: 独立壁再評価で「真の Mathlib 不在ではなく plumbing 過大評価」と判定 → `awgnConverseMarkov_holds` を `BlockwiseChannel.isMarkovChain_per_letter_input` template + message-space marginal `μ = (μ.map fst) ⊗ₘ (W.comap encoder)` 経由で genuine 化。非単射 encoder の難所は `compProd_map_condDistrib` に吸収され Route B fallback 不要。`#print axioms awgnConverseMarkov_holds = [propext, Classical.choice, Quot.sound]` (sorryAx-free、fresh olean で機械確認)。consumer `AWGNConverseDischarge.lean:455` clean 再コンパイル]** | Ch.9 AWGN (Phase 3-α converse) |
| `awgn-capacity-converse-maxent` | **single-letter** AWGN capacity converse: `∀ p : Measure ℝ` (任意 input 分布、second moment `≤ P`) で `(mutualInfoOfChannel p (awgnChannel N)).toReal ≤ (1/2) log(1 + P/N)` (Gaussian max-entropy 上界、`awgnCapacity` の sSup を closed form と sandwich する converse 方向)。general chain rule `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` が任意入力で `Integrable (fun z => log ((outputDistribution p W).rnDeriv volume z.2).toReal)` を free でない hyp として要求し、mixture-of-Gaussians 出力ではこの可積分性が Mathlib 不在 (loogle: `Integrable (log ∘ rnDeriv) (compProd _ _)` 0 件、in-tree `AwgnWalls.lean:246-248` も corroborate)。**[CLOSED 2026-05-29 (commit `f8549b9`): `AwgnCapacityConverseMaxent.lean` で genuine 証明完成 (Phase 6 mixture log-density integrability を convolution density 表示 `q = vol.withDensity (∫⁻ gaussianPDF ∂p)` + Gaussian upper bound (6a) + Chebyshev concentration `p({|x|≤R})≥1/2` + Gaussian tail 下界 (6b `output_logDensity_lower_bound`) + finite-second-moment domination (6c/6d) で in-tree 構成、計画の `rnDeriv_conv` ルートを使わず withDensity 直接構成に pivot)。最終定理 `awgn_capacity_closed_form_genuine` + 全 Phase 補題は `#print axioms` で `[propext, Classical.choice, Quot.sound]` のみ依存 = `sorryAx` 非依存 (transitive 0 sorry 機械確認済、独立 honesty audit OK / `@audit:ok`)。loogle 裏取り: convolution に対する `Integrable (log ...)` 直接 lemma は Mathlib 不在を再確認 (`integrable_conv_iff` / `integral_conv` の一般形のみヒット、wall 主張 honest だった)。**旧 wrapper `ContChannelMIDecomp.awgn_capacity_closed_form_of_out` (`:683`) は import cycle (successor が当該 file を import) のため successor を呼べず body `h_max_ent` `sorry` + `@residual(wall:awgn-capacity-converse-maxent)` 残置 = この active `@residual` は閉じた壁を指す stale 状態。実コード consumer 0 件 (`rg` で declaration + docstring 言及のみ)。stale residual の処理 (residual 外し / wrapper 削除 / 許容) は orchestrator 判断]**。隣接 converse 壁 3 件 (`awgn-per-letter-integrability` / `awgn-continuous-mi-chain-rule` / `awgn-converse-markov-regularity`) は全て `AwgnCode M n P` codebook + `converseJointInline` (n-letter `Fin n → ℝ` joint) の **channel-coding converse** で対象が別: 本 wall は codebook 無しの **single-letter capacity** 側 (Cover-Thomas 9.1)。`awgn-converse-aux-plan` / c1b mini-plan (`awgn_per_letter_mi_le_log_var`) も `X := Fin M, Y := Fin n → ℝ` の coding converse 対象で本 wall を closure しない | Ch.9 AWGN (9.1 single-letter capacity converse, `awgn_capacity_closed_form_of_out` の `h_max_ent`) |
| `awgn-mi-decomp` | continuous-channel MI chain rule (per-channel decomposition) `(mutualInfoOfChannel p W).toReal = differentialEntropy (outputDistribution p W) − ∫ x, differentialEntropy (W x) ∂p`、i.e. `I(X;Y) = h(Y) − h(Y\|X)` の density-level 形。**[CLOSED 2026-05-28: `ContChannelMIDecomp.lean` `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` で genuine 証明完成 (local helper assembly: `toReal_klDiv_of_measure_eq` + `llr_compProd_prod_split` (linchpin `rnDeriv_compProd_fibre`) + `integral_compProd` Fubini + `integral_log_rnDeriv_eq_neg_diffEntropy` で fibre/output 同定)、0 sorry。shared wall `AwgnWalls.contChannelMIDecomp_holds` は削除、active `@residual(wall:awgn-mi-decomp)` 0 件]**。隣接 `awgn-continuous-mi-chain-rule` (converse の `I(X^n;Y^n) ≤ ∑ I(X_i;Y_i)` sum 形) と semantic 区別: 本 wall は **per-channel decomposition** 形 (単一 channel の entropy 差分解、sum 形ではない) | Ch.9 AWGN (9.2.1 MI bridge) |
| `heatflow-continuity` | heat-flow entropy-power の端点連続性: `t ↦ entropyPower (P.map (X + √t·Z))` の `ContinuousWithinAt (Set.Ici 0) 0` (t=0⁺ への収束)。`MeasureTheory.continuousWithinAt_of_dominated` の唯一の欠落前提 = **t=0⁺ 近傍 一様 integrable pointwise majorant** `‖negMulLog (f_t x)‖ ≤ g x` (∀ small t)。`IsDeBruijnRegularityHyp` の field (`pX_nn`/`pX_meas`/`pX_law` = L¹ 密度、`pX_mom` = 有限2次モーメント) からは組めない: 既存 envelope (`convDensityAdd_logFactor_poly_majorant` / `_chain_domination` / `gaussGradMaj`、全て Assembly 内 `private`) は **fixed-`t`** で定数が t→0⁺ で発散 (`A_up ⊃ (1/2)log(4πt)+2R²/t`、slope `B=2/t`) かつ `s∈Ioo(t/2,2t)` (0 から離れた範囲) 限定。一般 L¹+2次モーメント密度 `pX` (例: 可積分特異点持ち) で `negMulLog (pX∗g_t)` の t-一様 pointwise envelope は不在。loogle: `entropyPower`/`differentialEntropy` の連続性は Mathlib・InformationTheory 双方 0 件。shared sorry 補題 `EPIG2HeatFlowContinuity.heatFlowEntropyPower_continuousWithinAt` で集約、consumer `csiszarLogRatioGap_continuousOn` (live) / `csiszarGap1Source_continuousOn` (dead, 差分版) が呼出。**DCT 機構 (`continuousWithinAt_of_dominated`) は既存**なので壁は majorant 構成のみ。隣接 `debruijn-integration` (積分形) / `fisher-finiteness` (score 2乗可積分、CLOSED) / `entropy-finiteness` (固定 t の log-factor 可積分、CLOSED) と semantic 区別: 本壁は **conv 密度の時間一様 pointwise integrable envelope** (端点連続性専用)。**[SUPERSEDED 2026-06-04: Vitali ルート再攻略で層2 (`differentialEntropy` 積分収束 machinery) を genuine 化 — `differentialEntropy_convDensity_integral_tendsto` (`EPIG2HeatFlowContinuity.lean`、own sorry 0、`tendsto_Lp_of_tendsto_ae` 無限測度版 + `tendsto_integral_of_L1'`、`#print axioms` で transitive sorryAx のみ確認)。GATE の DCT-uniform-majorant 想定は誤り: UnifIntegrable/UnifTight は majorant 不要かつ無限測度 `volume` で使える (`tendsto_Lp_of_tendsto_ae` は `[IsFiniteMeasure]` 非要求)。壁は (a) `approx-identity-L1` (層1 L¹収束、下記新行) + (b) 密度同定ブリッジ gap (`IsDeBruijnRegularityHyp` に `Measurable X/Z`・`IndepFun X Z` が不在で `pPath_eq_convDensityAdd` を呼べない → `@residual(plan:epi-g2-layer2-moonshot-plan)`、signature 設計課題) に分解。active `@residual(wall:heatflow-continuity)` 0 件 (壁補題 `heatFlowEntropyPower_continuousWithinAt_zero` は compound `wall:approx-identity-L1,plan:epi-g2-layer2-moonshot-plan` に置換)。独立 honesty audit 2026-06-04 OK (0 defect、signature honest、false-bridge 回避正当)。**[UPDATE 2026-06-04 Phase 5-B/5-D/5-E/5-F: (b) 密度同定ブリッジ gap closure 済 — 新 precondition `IsHeatFlowEndpointRegular` (全 field regularity: measurability/indep/Z_law `gaussianReal 0 v_Z`/密度witness pX/entropy 有限性 hpX_ent) を導入し壁補題 `key` を genuine 化 (helper `heatFlowDifferentialEntropy_continuousWithinAt_zero`、own sorry 0)。層2 plan: 2件も closure: 5-E `convDensityAdd_negMulLog_integrable_pub` を Assembly genuine asset の public 化で sorryAx-free delegation 化、5-F under-hypothesized `negMulLog_integrable_of_density` (L¹+2次モーメント⊬h(X)有限、false-as-stated) を削除し h(X) 有限性を `hpX_ent` precondition 化。**壁補題 `heatFlowEntropyPower_continuousWithinAt_zero` の `@residual` は `wall:approx-identity-L1` 単独に縮小** (`#print axioms` で transitive sorryAx が層1 のみ確認)。密度witness/entropy 有限性は site (`isStamToEPIScalingHyp_of_stam_debruijn`) で `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` park (上流 EPI precondition、joint-indep gap と同 owner)。pPath atom は v_Z 一般化 (N(0,2) 和 instance 対応)。独立 honesty audit 2026-06-04 (5-B/5-D 4観点 + 5-E/5-F 7観点) 全 PASS]**]** | Ch.17 EPI (G2 端点連続性、`csiszarLogRatioGap_antitoneOn_Ici_zero` R-5-c live 消費) |
| `approx-identity-L1` | 近似単位元の L¹ 収束: 一般 L¹ 密度 `pX` (非負可測 + 有限2次モーメント) に対し、消えゆくガウス核との畳み込み `convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩)` が `t→0⁺` で `pX` に **L¹ 収束** (`eLpNorm (conv − pX) 1 volume → 0`)。G2 端点連続性 (`heatflow-continuity` の後継入力壁) を Vitali ルートで攻める際の真の入力。Mathlib の近似単位元 L¹ 収束一般定理は不在 (loogle 2026-06-04 裏取り: `convolution_tendsto_right` は bump/compact-support 限定、一般 L¹ 不可; `MeasureTheory.Integrable, Real.negMulLog` も 0 件)。`gaussianPDFReal` は compact support でない (ContDiffBump 不可) ため tail 評価が要る。shared sorry 補題 + UI/UT/ae witness 3 本 (`negMulLog_convDensity_unifIntegrable`/`_unifTight`/`_tendsto_ae`) に集約。`heatflow-continuity` (DCT majorant 形、superseded) との区別: 本 wall は UnifIntegrable/UnifTight (majorant 不要・無限測度可) ベースの Vitali 入力 = より弱く標準的で上流 Mathlib PR 化しやすい命題。**[UPDATE 2026-06-04: 密度 L¹ 収束 `convDensityAdd_tendsto_L1_zero` CLOSED — 孤児を削除し新 file `InformationTheory/Shannon/EPIApproxIdentityL1.lean` で genuine 化 (11 decl 全 `@audit:ok`、sorryAx-free、独立 honesty audit PASS)。L¹ 平行移動連続性 (`Lp.compMeasurePreserving_continuous` 翻訳) + 連続版 Minkowski (Fubini 迂回) + Gauss 集中 DCT (二次モーメント Chebyshev) の genuine 組上げ。ただし密度 L¹ 収束は `negMulLog` 非Lipschitz ゆえ negMulLog 合成の L¹ 収束を自動では与えない (在庫が Vitali を選んだ真因)。**残る `wall:approx-identity-L1` の active residual = `EPIG2HeatFlowContinuity.lean` の UI/UT/ae witness 3 本のみ** (`:159`/`:176`/`:194`)。closure 計画は `docs/shannon/epi-g2-vitali-closure-plan.md` (Phase A=ae/B=UT/C=UI、難易度 ae≪UT<UI、UI は maxent 上界 `differentialEntropy_le_gaussian_of_variance_le` の確率測度 framing が鍵)。]** **[CLOSED 2026-06-05 (commit `b8ee036`): wall 完全消滅。Vitali ルートを放棄し、層2 `differentialEntropy_convDensity_integral_tendsto` を一般形サンドイッチ ((α) 上界 + (β) 下界) に載せ替え。(α) = KL 下半連続性を **DV 双対 hard direction でなく klFun 積分表現 (`klDiv_eq_lintegral_klFun_of_ac`) + klFun≥0 + Fatou (`lintegral_liminf_le`)** で genuine 化 (`EPIG2KLFatouLSC.lean`、W1-W4 + assembly 全 `@audit:ok`、固定ガウス参照測度 γ 上で Fatou を取るため負部一様可積分 majorant 不要 = 無限測度 Lebesgue で生じた障害が消える)。(β) = 密度形下界 `negMulLog_convDensity_entropy_ge_density` (`EPIG2ConvEntropyDensity.lean`、canonical Ω=ℝ×ℝ instantiation で 8 regularity 前提全 discharge、`@audit:ok`)。boundedness は genuine maxent 上界 (`negMulLog_convDensityAdd_gaussian_entropy_upper`) で供給 (壁非経由)。UI/UT witness 3 本削除、`@residual(wall:approx-identity-L1)` active = **0 件** (`rg` 確認)。層2 + 下流 `heatFlowEntropyPower_continuousWithinAt_zero` 共に `#print axioms` sorryAx-free (独立 honesty audit 2026-06-05 PASS)。一般形 (有限 2 次モーメント + `h(X)>−∞`) でスコープ犠牲なく完成。在庫 `epi-g2-general-sandwich-inventory.md` の DV 双対 moonshot 判定は **単一ルート過大評価** (klFun-Fatou 間接経路を未探索) と判明。]** closure 計画: `docs/shannon/epi-g2-general-sandwich-moonshot-plan.md` (達成)。旧計画: `docs/shannon/epi-g2-vitali-closure-plan.md`。 | Ch.17 EPI (G2 層2、`differentialEntropy_convDensity_integral_tendsto` の入力) |
| `cond-diff-entropy` | 連続版 **条件付き微分エントロピー** + **conditioning-reduces-entropy** の Mathlib 未整備部。`condDifferentialEntropy X Z μ := ∫ z, differentialEntropy ((condDistrib X Z μ) z) ∂(μ.map Z)` (Mathlib `condDistrib` ベースで定義は genuine) に対し、2 つの結論が in-tree 不在: (a) **conditioning 減少** `h(X\|Z) ≤ h(X)` (`condDifferentialEntropy_le`、微分版 `I(X;Z) = h(X) − h(X\|Z) = KL(joint‖product) ≥ 0`。`klDiv` は `ℝ≥0∞`-値で非負は型自明だが、`I = h − h(·\|·)` の微分エントロピーレベル bridge が未組立)、(b) **独立和 fibre 同定** `h(X+c·Z\|Z) = h(X)` (`condDifferentialEntropy_indep_add_eq`、`condDistrib (X+c·Z) Z μ z =ᵐ (μ.map X).map(·+c·z)` の disintegration 同定。`indepFun_iff_map_prod_eq_prod_map_map` + compProd-vs-prod の affine reparam + kernel `κ z := (μ.map X).map(·+c·z)` の可測性構成が必要)。loogle 裏取り (2026-06-04): `ProbabilityTheory.condDistrib, InformationTheory.klDiv` = Found 0、`ProbabilityTheory.IndepFun, ProbabilityTheory.condDistrib` = Found 0、in-tree `condDifferentialEntropy` grep = 0。**不在 ≠ 真壁** — conditioning-reduces-entropy は古典定理で `condDistrib` 基盤は Mathlib 既存、closeable 見込み高 (genuine 自作で閉じる)。**EPI line / 教科書全体で再利用可能な独立資産**。EPI G2 一般形サンドイッチ (β) 下界 `h(f_n) ≥ h(pX)` を非循環 (EPI 迂回) に供給。`approx-identity-L1` / `heatflow-continuity` (層1/層2 の L¹ 収束・端点連続性) と semantic 区別: 本 wall は **条件付けエントロピー単調 + fibre 同定** (収束解析ではない)。集約先 `EPIG2ConvEntropyMonotone.lean`。device 形 `differentialEntropy_indep_gaussian_add_ge` + 密度形 `negMulLog_convDensity_entropy_ge` は wall 補題への plumbing (自 body sorry 無しだが `condDifferentialEntropy_le` を transitive 継承するため `@residual(wall:cond-diff-entropy)` 付与)。**[UPDATE 2026-06-04: 補題 (b) fibre 同定 `condDifferentialEntropy_indep_add_eq` を genuine CLOSED (`@audit:ok`、sorryAx-free)。z 依存アフィン kernel `affineShiftKernel` + `prod_map_affine_eq_compProd` + `condDistrib_ae_eq_of_measure_eq_compProd` 一意性で在庫の「(b) wall 誤分類」を解消。**active wall = (a) conditioning 減少 `condDifferentialEntropy_le` (`:104`) のみ**。独立 honesty audit 2026-06-04: 補題 (b) + 補助 genuine、補題 (a) wall 分類 honest (mutualInfo Mathlib Found 0 再確認)。]** **[CLOSED 2026-06-05 (commits `465dcc8` + `f5d39a5`): wall 残 (a) `condDifferentialEntropy_le` を genuine CLOSED — bridge `differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv` を 3 成分 (a) `klDiv_compProd_const_toReal_integral` (`CondKLIntegral.lean`、Mathlib `ChainRule.lean` TODO 充足) + (b) `klDiv_toReal_eq_neg_differentialEntropy_sub_cross` + (c) `integral_condDistrib_density_marginal_eq` (`EPIG2BridgeDensityHelpers.lean`) で組立、`h(X)−h(X\|Z) = (klDiv joint product).toReal ≥ 0` (klDiv は `ℝ≥0∞`-値、`ENNReal.toReal_nonneg` type-trivial) で `condDifferentialEntropy_le` genuine 化。下流 device 形 `differentialEntropy_indep_gaussian_add_ge` + 密度形 `negMulLog_convDensity_entropy_ge` も genuine。threading した precondition 群 (joint≪product / per-fibre 絶対連続 / llr 可積分 = KL 有限性 / fibre entropy・cross-term・marginal log-density 可積分性) は全て regularity precondition で load-bearing でない (結論 = entropy 差 = KL 恒等式を仮説に encode していない)。`#print axioms` = `[propext, Classical.choice, Quot.sound]` (12+ declaration 全て sorryAx-free、独立 honesty audit 2026-06-05 機械確認 + load-bearing/vacuity/sufficiency 全 PASS)。**active `@residual(wall:cond-diff-entropy)` 0 件、wall CLOSED**。loogle `condDistrib`+`klDiv` Found 0 再確認 (gap 主張 honest)。集約先 `EPIG2ConvEntropyMonotone.lean` 全 `@audit:ok`、(a)/(b)/(c) 成分も全 `@audit:ok`]** closure 計画: `docs/shannon/epi-g2-general-sandwich-moonshot-plan.md` Phase 1 | Ch.17 EPI (G2 (β) 下界、`negMulLog_convDensity_entropy_ge`) |
| `minkowski-det-posdef` | Cover-Thomas 17.9.1: `det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)` for PosDef A B。**[CLOSED 2026-05-28: `MinkowskiDet.lean` で genuine 証明完成 (同時対角化 + AM-GM)、active `@residual` 0 件、`@audit:ok`。wall 主張 (Mathlib 0件) は loogle で裏取り済 honest だった]**。隣接 `epi-n-dim` (entropic 形) / `bm-convex-body-sqrt` (geometric 形) と semantic 区別: 本 wall は algebraic 形 | Ch.17 EPI / 17.9 BM |
| `lz78-aseventual-ziv` | LZ78 a.s.-eventual Ziv inequality `limsup (lz/n) ≤ entropyRate` (achievability 上界、Cover-Thomas Lemma 13.5.5)。discharge = M3 (variable-depth tree-node AEP) research-level scope-out、codebase + Mathlib 不在。active = `lz78GreedyImpl_achievability_ae` (`GreedyParsingImpl.lean`)。2026-06-20: 符号長 def-fix 後の **genuine 壁** — ダミー1シンボル parse (rate 発散) 時代は achievability sorry が degenerate defect だったが、`lz78GreedyImplEncodingLength` を genuine longest-prefix parse (`lz78PhraseStrings`、`c·bitLength c |α|`、rate `O(1)`) に書換 (commit `5d08566`) 後は genuine 命題に。Ziv 組合せ核 (`c·log c ≤ K·n`、`lz78PhraseStrings_mul_log_le`) は sorryAx-free 確立済、残るは entropyRate との接続 (M3)。独立監査 PASS (commit `9b09790`)。cause:false-statement (過小評価系、ダミー parse 時代の誤分類は def-fix で解消) | Ch.13 LZ78 (achievability) |
| `lz78-converse-aseventual` | LZ78 a.s.-eventual converse 下界 `entropyRate ≤ liminf (lz/n)` (Cover-Thomas Thm 13.5.3 lower bound、harder SMB-lower + Kraft 方向)。discharge = M4 (Barron a.s. lift、期待値 converse `H_D ≤ E[lz]` を a.s.-eventual pointwise `liminf` に持ち上げ) research-level scope-out、codebase + Mathlib 不在。active = `lz78GreedyImpl_converse_ae` (`GreedyParsingImpl.lean`)。2026-06-20: 符号長 def-fix 後の **genuine 壁** — ダミー parse 時代は converse sorry が false-statement defect (rate 発散で結論偽) だったが、genuine longest-prefix def-fix (commit `5d08566`、rate `O(1)`) 後は genuine 命題に。独立監査 PASS (commit `9b09790`) | Ch.13 LZ78 (converse) |

新規 wall を追加する時は: (1) loogle で 0件確認 (本当に Mathlib 不在か。**0件は必要条件であって十分条件でない** — 判定プロトコル詳細は CLAUDE.md「Verification」の壁判定 反証義務)、(2) 既存 register に類似がないか確認、(3) 本表に直接追記してコミット。

**壁判定の必須メタデータ** (判定コミット docstring or plan 判断ログに記録。覆り時の「最初の判定根拠」を後追いでなく判定時に固定する。書く過程そのものが自己反証になる):

- **試したルート ≥2** (各 1 行: どの lemma chain で、どこで詰まったか)
- **gateway atom**: この壁 family の決定的 1 補題は何か / 実装して試したか (Y/N)。family 丸ごとの壁判定前に atom 1 本を実装 dispatch する
- **反証試行**: small-case + 退化境界 (`=0` / Dirac / 非可積分 / `N=0`) で statement が生きるか (Y/N + 結果)。non-wall / 仮説 OK と断じる側で必須
- **plumbing vs gap**: 詰まりは「命題が Mathlib に無い (真の gap)」か「既存 asset への配線 (import cycle 含む)」か

**覆し時の `cause:` タグ** (calibration、施策6): wall を CLOSED / defect を判明させたとき、注記末尾に根本原因カテゴリを 1 語で残す → `cause:single-route` / `cause:plumbing` / `cause:loogle-blind` / `cause:gateway-atom-untried` / `cause:layering-bundled` (以上 過大評価系) / `cause:false-statement` / `cause:signature-drops-constraint` / `cause:degenerate-boundary` / `cause:numeric-mispredict` (以上 過小評価系)。過大評価 (本 register) と過小評価 (`defect-inventory-*.md`) が別台帳に散るのを cause タグで横断集計可能にする。下表が現状スナップショット (~40 件の覆し分析、2026-06-07):

| cause | 系統 | 件数感 | 代表 slug / 補題 |
|---|---|---|---|
| `loogle-blind` | 過大 | 最多 | `withDensity_map` (multivariate subadd), multivariate-mi, condExp_indep (bare-query false-neg) |
| `single-route` | 過大 | 多 | stam-step2-density, fisher-finiteness, awgn-capacity-converse-maxent, Chernoff(Sanov), approx-identity-L1 (DCT/Vitali のみ) |
| `plumbing` | 過大 | 中 | debruijn-integration, entropy-finiteness, awgn-mi-decomp, awgn-converse-markov-regularity |
| `gateway-atom-untried` | 過大 | 中 | stam-blachman, convDensity_add_differentiable |
| `layering-bundled` | 過大 | 少 | epi-finite-entropy-ac-classical (有限/無限分散 束ね) |
| `false-statement` | 過小 | 最多 | Huffman merged-identity/collapse-label, LZ78 Ziv core |
| `signature-drops-constraint` | 過小 | 多 | IsStamCauchySchwarzOptimal 系 (`fisherInfoOfMeasureV2` が measure 引数を捨てる) |
| `degenerate-boundary` | 過小 | 中 | awgn N=0 channel, parallel Gaussian 非可積分入力 |
| `numeric-mispredict` | 過小 | 中 | entropyPower(Dirac 0)=1 (0 と誤予測), Phase D 退化境界 |

#### 提案中 wall (Proposed — 後続セッションで promote 判断)

以下の wall 候補は Round 2 sweep (2026-05-25) で識別されたが、各 plan のデフォルト方針
「plan-slug で揃え、wall 化は後続 PR」に従い register 追加は留保。後続 family sweep で
shared sorry 補題化の必要が浮上したら本表から上の正式 register に格上げ。

| 候補 wall name | 由来 plan | promote trigger 条件 |
|---|---|---|
| `relay-block-markov-aep` | `relay-sorry-migration-plan` | Relay block-Markov + sliding-window decoder の shared sorry 補題化が必要になったとき |
| `relay-cf-wz-binning` | `relay-sorry-migration-plan` + `wyner-ziv-discharge-moonshot-plan` | Relay CF と WynerZiv binning を 1 補題で共有したいとき |
| `csiszar-sum-conditional` | `relay-sorry-migration-plan` | 既存 `csiszar` (projection) と区別された conditional sum identity 系補題が複数 family で再出現したとき |
| `n-dim-prekopa-leindler` | `brunn-minkowski-sorry-migration-plan` + `prekopa-leindler-induction-plan` | n-dim PL Fubini induction を shared sorry 化したいとき (現状 BM closure plan が 1D PL hyp を honest hyp で保持中) |
| `bm-convex-body-sqrt` | `brunn-minkowski-sorry-migration-plan` + `brunn-minkowski-closure-plan` | 凸体 BM sqrt 形 `volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)` を BM 外の family が参照するようになったとき |
| `lz78-combinatorial-core` | `lz78-sorry-migration-plan` | Cover-Thomas Lemma 13.5.5 distinct-phrase 核を LZ77 / 他 universal coding family が参照するとき |

promote 判定基準: (1) 該当 declaration が shared sorry 補題として 2+ family で再利用される、
または (2) `plan:<slug>` 集約より wall 化のほうが closure 計画と整合する。両条件いずれかが
満たされたタイミングで上記行を Wall name register 本表に移し、当該 declaration の
`@residual` を `@residual(plan:<slug>)` から `@residual(wall:<name>)` に書換。

**Round 3 escalate #4 — `bm-convex-body-sqrt` promote 再判定 (2026-05-26)**: BM Wave 6
で隣接 wall 2 件 (`uniform-max-entropy-on-convex-body` + `bm-additive-convex-body`、
commit `fe28966`) を正式 register 入りさせた折に本候補も再評価したが、現状 consumer
は `BrunnMinkowskiClosure.lean` 1 file 内 docstring 言及 4 件のみ
(`rg 'bm-convex-body-sqrt' InformationTheory/` で in-file 限定)、active
`@residual(wall:bm-convex-body-sqrt)` は **0 件** (load-bearing
`IsBMEntropyPowerVolumeHyp` predicate が closure plan §G で honest hyp として保持中、
sqrt 形 sorry はまだ書かれていない)。`cramer-sorry-migration-plan.md:722` での言及も
「同型の trigger 条件あり」という meta 比較で、Cramer family が sqrt 形を直接参照する
構造ではない。trigger 条件 (2+ family 参照 or 1 family 複数 file 参照) **不達**、Round 4
持ち越し。次回 trigger 候補: EPI route (`brunn-minkowski-from-epi-discharge-plan`) または
n-dim PL route (`prekopa-leindler-induction-plan`) で sqrt 形 sorry を新規導入したとき
(closure plan が委任先として両 plan を明示、`BrunnMinkowskiClosure.lean:548`)。

**隣接 wall との semantic 区別** (Wave 6 で正式 register 入りした 2 件 vs 本候補):

- `bm-additive-convex-body` (Wave 6 promote): 凸体の Brunn-Minkowski **加法形**
  `vol(A) + vol(B) ≤ vol(A + B)` — 体積の plain な和形、1 次元類比。
- `uniform-max-entropy-on-convex-body` (Wave 6 promote): 凸体上 **uniform 分布 = max
  entropy** の characterization (n-dim) — uniform measure の microstate count
  特徴づけ、entropy 側の statement。
- `bm-convex-body-sqrt` (本候補、保留): 凸体 BM の **sqrt 形**
  `volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)` — Cover-Thomas 17.9.4 で entropy power
  Brunn-Minkowski に持ち上げる橋。加法形より strong (additive form は sqrt form の
  弱形)、entropy power lifting に直接乗る形。3 件は **互いに非重複**: 加法形 ⇐ sqrt 形
  (Minkowski 不等式 / Hölder 経由)、uniform max entropy は分布特徴づけで対象が違う。

#### Defect kind 語彙

`@residual(defect:<kind>)` の `<kind>`:

| Kind | 由来 defect | 典型例 |
|---|---|---|
| `circular` | 仮説型 ≡ 結論型 で body が `:= h` (旧 `@audit:defect(circular)`) | WynerZiv `wyner_ziv_achievability_rate` |
| `prop-true` | `:True` slot に実 residual を隠す (旧 `@audit:defect(prop-true)`) | (旧 6 件、移行済) |
| `launder` | name laundering (`*_discharged` / `*_full` / `_bridge` 等で完成偽装、旧 `@audit:defect(launder)`) | LZ78 `def IsSMBToLZ78ConverseChainBridge := IsLZ78ConverseChainHyp` (literal alias) |
| `degenerate` | 退化定義悪用 (predicate 自身は FALSE ではないが、vacuous shape / operational discard で意味を空にしている、旧 `@audit:defect(degenerate)`) | MAC/BC `bc_random_codebook_markov_of_ensemble` (本体は genuine averaging だが `obtain ⟨_C₀, _hC₀⟩` で operational witness を discard、constructor だけ満たす) |
| `false-statement` | mathlib_wall_misuse / 実は偽の statement | (旧 EPI/DeBruijn 系) |
| `false-hypothesis` | **仮説 (predicate) 自身が機械検証可能に FALSE** (反例構成済 or refutation 補題あり); 当該 wrapper の含意は vacuously-true | Huffman `EqualizingPermHypothesis` / `MergedHuffmanAuxIdentHypothesis`; LZ78 `IsLZ78ZivCombinatorialCoreOverhead` (反例 `n=16, Pₙ=1, c=5` あり、`not_isLZ78ZivCombinatorialCoreOverhead` で refutation 済) |

**`degenerate` vs `false-hypothesis` の使い分け** (Round 2 LZ78 L-MIG-3 由来の clarification):

- 「predicate が機械検証可能に FALSE」(反例構成 / refutation 補題が in-tree 存在) → **`false-hypothesis`** を使う
- 「predicate 自身は FALSE ではないが、operational witness が discard される / vacuous shape で意味を空にしている」 → **`degenerate`** を使う
- 両方該当する境界例 (predicate FALSE かつ意味も空) → `false-hypothesis` を優先 (より精確な根本原因)

新規 kind を追加する場合も本表に追記する。

**運用上の位置付け**: `@residual(defect:<kind>)` および対応する `@audit:defect(<kind>)` は次の 2 用途で使う。

1. **旧 `@audit:defect(*)` の sorry-based 後継** として既存 defect を移行するマーカー (本ファイル下部「Deprecated」表)。
2. **`def` / `Prop := ...` RHS / `inductive` constructor 等 `sorry` を書けない箇所での暫定撤退口**。`sorry` は proof body にしか書けないため、signature 自体が詰まったときは以下の順で対処する:
   - **第一選択 — 定義書換** (CLAUDE.md「Mathlib-shape-driven Definitions」)。textbook の formulation を結論形に合わせて再定義 → 性質を別 `theorem` で述べる → body `sorry` + `@residual(<class>:<slug>)` という basic route に持ち込めるなら、それが正解。shared sorry 補題化 (本ファイル下部「共有 Mathlib 壁」) も同種の手法。
   - **第二選択 (暫定)** — 当該セッションで定義書換が無理 (循環構造解消に上流再設計必要 / signature 改変の影響範囲が大 / vacuously-true wrapper として acknowledged 等) な場合は signature を defect 形のまま残し、docstring に `@audit:defect(<kind>)` + `@audit:retract-candidate(<reason>)` または `@audit:closed-by-successor(<plan-slug>)` を併記する。これは **後で第一選択に migrate する暫定マーカー** であり stable な resting state ではない (honesty audit は tier 5 として detect)。

第二選択を残す場合の必須条件 2 点: (a) docstring に「なぜ第一選択が当該セッションで無理だったか」を 1 行散文で説明、(b) 後続 plan の slug を `@audit:closed-by-successor(<plan-slug>)` で指す。両方欠けたまま tier 5 を残置するのは silent defect とほぼ同等 (auditor が即時 alert)。

**配置**: 1 sorry / 1 theorem の場合は docstring 末尾、複数 sorry の場合は各 sorry の直前行コメント。

```lean
-- パターン A: 単一 sorry → docstring に
/-- Stam の不等式の本体。
@residual(plan:epi-stam-closure) -/
theorem stamInequality_body : ... := by
  sorry

-- パターン B: 複数 sorry → 各 sorry 直前
theorem foo : ... := by
  have h1 : ... := by
    -- @residual(wall:stam)
    sorry
  have h2 : ... := by
    -- @residual(plan:foo-step-2)
    sorry
  ...
```

#### Compound syntax (Round 2 残課題 → Round 4 正式提案)

1 つの `sorry` が **複数の独立した closure 担当** (例: 別 plan + 別 wall、または 2 つの上流 plan の合流点) を持つときは、`@residual(...)` の引数に **comma-separated** で列挙してよい。Round 2 sweep で Chernoff L-MIG-4 / Cramer CLT closure 系で必要性が浮上し、Round 4 で正式登録。

**EBNF 拡張** (既存 single 形と後方互換):

```ebnf
residual-tag    = "@residual(" residual-list ")"
residual-list   = residual-item { "," residual-item }    (* NEW: comma list, 1 以上 *)
residual-item   = class ":" slug
class           = "plan" | "wall" | "defect"
slug            = kebab-identifier
```

例:

```lean
-- 単一 (既存、変更なし)
@residual(plan:awgn-mi-bridge-plan)

-- compound (NEW): 2 つの plan を AND 結合
@residual(plan:awgn-mi-bridge-plan,plan:awgn-mi-decomp-plan)

-- compound: plan + wall を AND 結合
@residual(plan:cramer-cltclosure-rewrite-recovery-plan,wall:characteristic-fn-clt)
```

**semantic (AND 限定)**: compound `@residual` は **論理 AND**。**両方** の plan / wall が closure されない限り、当該 `sorry` は解消不能。

**OR semantic は未予約**: 「どちらか一方の plan で closure 可能」を表現する `@residual-or(...)` のような alternation syntax は **現状未予約 + unsupported**。OR が必要になったタイミングで別 syntax として議題化する (本 syntax を流用しない)。

**適用シナリオ**:

1. **transitive sorry の正式表現** (Round 3 Wave 3-B Chernoff L-MIG-4 expansion で発見) — downstream wrapper が upstream の sorry + 別 plan の壁を両方 thread する場合。従来は runbook L518-521 の「タグ付与せず散文で明示」(Pattern C) で回避していたが、家族間で再帰使用が増えると散文 divergence の懸念。compound `@residual` で構造化。
2. **cross-family plumbing** — 例: Cramer の CLT closure 系で characteristic function + Stam 不等式の両方が壁、`@residual(plan:cramer-cltclosure-rewrite-recovery-plan,wall:stam)`。
3. **active consumer の bookkeeping 代替** — Round 3 BMClosure 系 escalate #2 が `closure-plan-completed` という新 reason vocab で対処したが、compound `@residual` で代替できれば retract-candidate semantic 拡張は不要だった可能性。後発の同パターン (load-bearing wall + active consumer) では compound `@residual` を先に検討すること推奨。

**transitive suffix `:transitive` との関係** (runbook L518-521): runbook 旧提案は `@residual(<class>:<slug>:transitive)` という suffix 形だったが、本 compound syntax で意図を吸収可能 (transitive 上流 sorry を closure する plan / wall を直接列挙すれば良い、suffix で「上流依存」を明示する必要は機械的には無い)。Pattern C の散文明示も引き続き許容 — `@residual` タグ無し + docstring 散文で transitive 性を表す形式は当面残す。

**registry / migration**:

- 既存 single `@residual(<class>:<slug>)` declarations はそのまま (本拡張は **strict superset**、backward-compatible)。
- 新規 compound 適用は本 vocab register 後に発生したタイミングで採用 (Round 5 以降の sweep で出現を想定)。
- 既存 sweep で散文 transitive (runbook Pattern C) として書かれているものを compound に書換える retroactive migration は **任意** (運用上の利得 = grep 集計の精度向上が見えてから判断)。

**grep recipe との整合**: compound `@residual` は既存「class 別ヒストグラム」recipe (`rg -o "@residual\([a-z]+:" ...`) では先頭 item のみカウントされる。compound 件数集計は別 pattern で行う (下記 grep recipe section 末尾 canonical pattern 追記参照)。

### `@audit:*` — bookkeeping (audit pass / 履歴 / 削除候補)

`@audit:*` は **残課題マーカーではない** (残課題は `sorry` + `@residual`)。audit 結果 + history record + 削除候補のみ。

| Tag | 意味 | Slug の中身 | sorry 持ち可? | 例 |
|---|---|---|---|---|
| `@audit:ok` | 独立 auditor が honesty pass 判定。genuine 完成 (0 sorry / 0 @residual) | (なし) | NO (定義上) | `@audit:ok` |
| `@audit:superseded-by(SLUG)` | 当該 declaration は後続版に置き換え済 (`_unconditional` 版が併存している `_of_condEntDiff` conditional 版等)。history record / API 後方互換のため削除しない | 後続 declaration / plan filename stem | YES (旧版が未完のまま残置可) | `@audit:superseded-by(wyner-ziv-convexity-unconditional)` |
| `@audit:retract-candidate(REASON)` | 削除候補。circular passthrough で honest 経路が他にあるケース等 | REASON 短文 (kebab-case、下記 Reason 語彙) | YES | `@audit:retract-candidate(circular-passthrough)` |

#### Reason 語彙 (`@audit:retract-candidate(<reason>)`)

| Reason | 意味 | 典型例 |
|---|---|---|
| `circular-passthrough` | 仮説型 ≡ 結論型の循環で、honest な代替経路が他に存在 | (新規 registration、現在使用 0 件) |
| `load-bearing-predicate` | predicate を hypothesis 形に取る load-bearing wrapper の **default reason**。active consumer 1+ あり (hypothesis-form / `.field` extract / bridge passthrough) で、当該セッションでは predicate 削除 + shared sorry 補題への migrate がまだ完了していない (tier 3 bookkeeping)。tier 2 sorry-based migration を待つ暫定状態。**「全 consumer 削除済」を意味しない** — その特殊形は下記 `-empty-consumers` で表す | EPIL3Integration (15 件) / AWGNConverseDischarge (5 件、`37284f1`) / EPIStamToBridge (4 件) / EPIStamDeBruijnConclusion (4 件) / AWGNAchievabilityDischarge (4 件、`37284f1`) / EPIStamDischarge (2 件、`34e17bc`) 他、sister `34e17bc` + `37284f1` precedent |
| `load-bearing-predicate-empty-consumers` | `load-bearing-predicate` の中でも active consumer **0 件** であるもの (純粋削除可能、history record として残置)。default `load-bearing-predicate` の特殊形 | EPIL3Integration:1588 (`IsCsiszarGap1SourceTendsToZeroAtInfinity`、`34e17bc` migration) / BirkhoffErgodic:1006 (`birkhoff_ergodic_ae_of_limit`、in-file successor `birkhoff_ergodic_ae` が unconditional) / EPIL3Integration:507 (`IsHeatFlowFamilyHyp`、構造 inhabitation source は Gaussian constructor `isHeatFlowFamilyHyp_of_gaussian` のみ、非 Gaussian 拡張余地として残置) |
| `load-bearing-predicate-extract-only` | `load-bearing-predicate` の中でも `.field` 抽出 / bridge 経由の extract-only consumer (pass-through、load-bearing claim を inject しない) **のみ** が残存しているもの (hypothesis-form consumer は 0 件)。default `load-bearing-predicate` の特殊形 | Round 3 Wave 3-D Audit-A で initial use 達成 (ChernoffPerTiltDischarge:252)、複数 family 横断 use の集計は今後継続 |
| `single-line-wrapper` | 1-line `def` で他 declaration を wrapping するだけの shim | WynerZivPackingBody |
| `name-laundering-alias` | `def X := Y` 形の literal alias で、`X` という名前にすることで discharge を偽装している (`launder` defect の def 版) | LZ78 `IsSMBToLZ78ConverseChainBridge := IsLZ78ConverseChainHyp` (`LZ78SMBSandwich.lean:307/319`) |
| `false-hypothesis` | `def` / `Prop` 自身が機械検証可能に FALSE (CLAUDE.md「sorry を書けない箇所での対処順序」第二選択)。`@audit:closed-by-successor` と併用して後継 plan を指す | LZ78 `def IsLZ78ZivCombinatorialCoreOverhead` (`LZ78ZivTreeNode.lean:403`、`not_isLZ78ZivCombinatorialCoreOverhead` で refutation 済) |
| `false-replaced-by-eps-relaxed` | false predicate を ε-relaxed 形に置き換えた場合の旧 declaration retract マーカー | ChernoffPerTiltDischarge:147 + ChernoffPerTiltSanov:148 (Round 2 commit `d83e45b`、Round 3 で usage 検出) |
| `circular-between-false-predicates` | 2 つ以上の false predicate の循環的 self-reference を解消する一方向だけを残し他方を retract | ChernoffPerTiltSanov:181 (Round 2 commit `d83e45b`) |
| `closure-plan-completed` | load-bearing wall を closure plan で acknowledged 済として bookkeeping (active consumer あり、削除候補ではない例外的用法)。tier 3 retract-candidate の semantic 拡張 (tier 階層は本ファイル上部 L17-23 参照)。default `load-bearing-predicate` との差は **closure plan で wall が明示的に acknowledge 済かどうか** — closure plan 未策定なら `load-bearing-predicate`、closure plan 着地済なら `closure-plan-completed`。後発の同パターン (LZ78 / Huffman / EPI 等) でも適用可 | BMClosure.lean L379 + L514 の active consumer 例 (escalate #2 採用判断、Round 3) |
| `degenerate-constraint-set-missing-integrability` | Bochner `∫` の `integral_undef` (非可積分 → 0) 慣行により、moment 制約 `∫ f ∂p ≤ P` を素朴に書いた set / predicate が degenerate input (moment 無限大なのに `= 0 ≤ P`) を許し statement が universally false 化。定義 pivot (lintegral `∫⁻ ... ≤ P` or `Integrable f p` 追加) 待ちの defect retract marker | AWGN `awgnCapacity` (`AWGN.lean:195`) / `awgn_capacity_closed_form_of_out` の `h_max_ent` (`ContChannelMIDecomp.lean:670`) / `awgn_per_input_mi_le_log` (`AwgnCapacityConverseMaxent.lean`、2026-05-29 audit) |
| `superseded-by-memoryless-form` | MVP/pre-discharge 形が後続 memoryless 形に置換済 | ChannelCodingFeedback (3 件) |
| `superseded-by-full-discharge` | 完全 discharge 形が別 file で publish 済 | ChannelCodingShannonTheoremFull |
| `general-alpha-rate-≠-E₂` | 固定 `alpha` の rate 列 (`-(1/n) log steinTypeII_at_level_pmf`) が Hoeffding tradeoff curve `E₂(alpha)` を一般に target しない (Stein's lemma の反例: `alpha = 0` で `rate ≡ 0 ≠ E₂(0) = D(P₁‖P₂) > 0`、`0 < alpha < 1` で `rate → D(P₁‖P₂) > E₂(α)`)。genuine 後継は exponential-level `hoeffding_tradeoff_exp` (`HoeffdingTradeoffExp.lean`) | **FULLY DISCHARGED / HISTORICAL** — **全 carrier 撤回済、live carrier 0 件** (`hoeffding_tradeoff_exp` で置換)。reason-kind 語彙定義 (左列) は同型 false fixed-`alpha` 結論を将来再判定する語彙として残置するが、現時点で active な declaration carrier は無い。撤回履歴: **2026-05-28 (1)** 旧 5 declarations (HoeffdingTradeoff / HoeffdingSandwich / HoeffdingSandwichDischarge / HoeffdingSandwichBody) を un-instantiable + 後継置換済のため削除。**2026-05-28 (2) Draft sweep** Draft interior wrapper 3 件 (`HoeffdingInteriorBody.lean`: `hoeffding_tradeoff_sandwich_at_interior_via_predicate` / `_via_gradient`、`HoeffdingInteriorGradientBody.lean`: `hoeffding_tradeoff_sandwich_at_lagrange`、いずれも sorry body の同型 false fixed-`alpha` 結論) を削除。interior-minimizer scaffolding (`IsHoeffdingInteriorMinimizer` 等、下流 consumer あり) は保持 |

新規 reason を追加する時は本表に直接追記してコミット (divergence 防止: 「superseded」と「superseded-by」が併存しないように)。kebab-case で短く (3-4 単語以内推奨)。

### 複数タグの併用

1 つの def/theorem に `@residual` と bookkeeping `@audit:*` が同居しうる。例: 旧版で残置している wrapper:

```lean
/-- 旧 conditional 版、history record のため残置。
@residual(plan:wyner-ziv-convexity-unconditional) @audit:superseded-by(wyner-ziv-convexity-unconditional) -/
theorem wynerZivConvexity_of_condEntDiff : ... := by sorry
```

意味: 「sorry は新 unconditional 版で closure 予定 (`@residual(plan:...)`)、当該 declaration は後続版に置換済の旧 wrapper (`@audit:superseded-by`)」。

### 解除

状態が変わったら **タグ自体を編集する** (`@residual(wall:stam)` → `@audit:ok` 等)。タグは 1 declaration につき可能な限り 1 行にまとめて、`rg -A1` で前後文脈付きレビューしやすくする。

## 配置ルール

- **`@residual`**: docstring 末尾 (単一 sorry) または sorry 直前のラインコメント (複数 sorry)。
- **`@audit:*`**: 必ず docstring 内 (line comment ではなく `/-- ... -/`)。理由: docstring は declaration とライフサイクルが揃っており、grep で declaration と pair で取れる。
- **`@param` `@field` のような Lean doc-tools の予約形式とは衝突しない** (`@residual` / `@audit:` は Lean が解釈しない、純粋にコメント文字列)。

## grep レシピ

### 残課題集計

```bash
# residual 全件 (= sorry の分類済件数の下限)
rg "@residual" InformationTheory/ | wc -l

# class 別ヒストグラム
rg -o "@residual\([a-z]+:" InformationTheory/ | sort | uniq -c | sort -rn

# compound @residual (comma-separated 2 件以上) の件数集計 (Round 4 正式提案)
rg '@residual\([^)]*,[^)]*\)' InformationTheory/ | wc -l

# 特定壁の影響範囲

# 特定 plan の closure 待ち件数
rg "@residual\(plan:epi-stam-closure\)" InformationTheory/

# tag 無し sorry (= 分類漏れ、CI で検出すべき)
# ファイル単位: sorry を含むが @residual を 1 つも持たない file を列挙
for f in $(rg -l "\bsorry\b" InformationTheory/); do
  rg -q "@residual" "$f" || echo "$f"
done

# 行レベル: 各 sorry の直前 3 行に @residual が無いものを抽出
awk '
  FNR==1 { delete prev; pn=0 }
  /^[[:space:]]*sorry/ {
    f=0; for (i in prev) if (prev[i] ~ /@residual/) f=1
    if (!f) print FILENAME":"FNR":"$0
  }
  { prev[(pn++) % 3]=$0 }
' $(rg -l "\bsorry\b" InformationTheory/)
```

### 完成状態の確認

```bash
# audit pass 済件数
rg "@audit:ok" InformationTheory/ | wc -l

# 残課題総数 (sorry + residual の整合確認用)
rg "\bsorry\b" InformationTheory/ | wc -l
rg "@residual" InformationTheory/ | wc -l
```

### plan からの逆検索

```bash
# AWGN typicality plan は何件を抱えるか
rg "@residual\(plan:awgn-achievability-typicality\)" InformationTheory/

# 後続版に置き換え済の旧 declaration
rg "@audit:superseded-by\(" InformationTheory/

# 削除候補
rg "@audit:retract-candidate\(" InformationTheory/
```

### declaration-direct タグ検索の canonical pattern (Pattern D 発展形)

`@audit:suspect` / `@audit:staged` / `@audit:closed-by-successor` を **bareword** で
grep すると docstring sign-off note の **文字列リテラル参照** (例: "...の旧
`@audit:suspect` 解消...") を false positive ヒットする。declaration-direct タグの
件数集計には **必ずパーレン付き pattern** を使う:

```bash
# canonical per-family 件数集計 (推奨 one-liner)
rg -c '@audit:suspect\(|@audit:staged\(|@audit:closed-by-successor\(' InformationTheory/<family pattern>

# 個別タグの canonical pattern
rg '@audit:suspect\('             InformationTheory/
rg '@audit:staged\('              InformationTheory/
rg '@audit:closed-by-successor\(' InformationTheory/
rg '@audit:retract-candidate\('   InformationTheory/
```

**Pattern D 発展形の実例 4 件** (Round 3 Wave 3-A、各 planner が独立に発見):

| family / file | bareword grep ヒット | パーレン付き (実 declaration) |
|---|---:|---:|
| BMFunctional | 4 | 0 |
| WynerZiv | 2 | 0 |
| EPIL3Integration | 2 | 0 |
| InfinitePiTiltedChangeOfMeasure | 1 | 0 |

**影響範囲**: orchestrator brief の per-family 計数 drift の根本原因。
planner / inventory に渡す前段の per-family 件数集計で必ず canonical pattern
(パーレン付き) を使う。Round 3 では全 4 planner が verbatim 確認で false positive
を独立に検出したため誤伝播は防がれたが、計数のみで判断する設計だと sweep
スコープが drift する。

## 運用ルール

### 残課題の埋め方 (実装中)

実装中に dead-end に遭遇したら:

1. 仮説束 (`(h : <core claim>) → conclusion`) で核を bundling **しない**
2. signature を本来証明したい形に保つ
3. body を `sorry` にする
4. 直近 docstring/コメントに `@residual(<class>:<slug>)` を書く

これだけ。「honest 名前付き仮説」「`*Hypothesis` predicate」等の語彙は不要。

### 監査時の発見 → 即タグ付け

監査中に honesty issue を発見したら **その場で `sorry` 化 + `@residual` または `@audit:*` を docstring に書き込む**。次セッションのタスクリストやハンドオフに「これも audit したい」と書かない。

なぜ:
- タスクリストは current session 内で消える / ハンドオフは多重化して読み逃す。docstring は declaration とともに永続。
- 発見場所 = 修正場所なので、置き場が決定論的。
- レビュー時に diff で見える。

## 共有 Mathlib 壁: shared sorry 補題パターン

同じ壁 (例: Stam の不等式) を複数 file から参照する場合、**各 use site で個別に `sorry` を書かない**。1 ヶ所に「shared sorry 補題」を立て、他は normal な lemma 呼び出しで使う:

```lean
-- InformationTheory/Shannon/EPIStamWalls.lean
/-- Stam の不等式。Mathlib 未収録、closure 待ち。
@residual(wall:stam) -/
theorem stamInequality
    (μ : Measure ℝ) [...] :
    fisherInfo μ ≥ ... := by
  sorry

-- 各 consumer は普通に呼ぶ
theorem foo : ... := by
  have h := stamInequality μ ...
  ...
```

これにより:
- 壁 1 件 = `sorry` 1 件。重複しない。
- consumer 側 file は `@residual` を持たず、proof done 判定可能 (壁 file だけが未完成)。
- 壁 closure 時は shared 補題 1 件を埋めれば全 consumer が genuine 化。

**⚠️ consolidate 時に regularity 前提を壁から落とさないこと** (2026-05-28 `contChannelMIDecomp_holds` 実例、`docs/shannon/awgn-mi-decomp-plan.md` 判断ログ #4)。複数 use-site の壁を 1 ヶ所に集約する際、各 use-site が持っていた絶対連続性 / 可積分性 / 可測性などの前提を壁の引数から削って「全称的に量化された hyp-free 補題」に弱めると、**壁が over-general 化して偽になりうる** (例: `contChannelMIDecomp_holds` を全 Markov channel で hyp なし主張 → 決定論チャネルで反例 → tier-5 `@audit:defect(false-statement)`)。`sorry` 壁は「真だが Mathlib に無いので未証明」であるべきで、「偽なので証明不能」では honest な撤退口にならない。**前提は壁の引数として残し**、consumer 側でそれらを genuine に discharge する (落とした前提が consumer にアンダースコアで取り残されていたら laundering の兆候)。

## Deprecated (移行対象 — 別セッションで sweep)

以下のタグは旧 honesty workflow (load-bearing hyp 容認) の名残。新規導入禁止、既存は sorry-based に移行。

| 旧タグ | 移行先 |
|---|---|
| `@audit:suspect(PLAN)` (≒ 🟢ʰ load-bearing hyp) | 仮説解除 → signature を本来の形に → body `sorry` → `@residual(plan:<PLAN>)` |
| `@audit:staged(WALL)` (Mathlib 壁 predicate bundling) | predicate 削除 → 共有 sorry 補題に置換 → `@residual(wall:<WALL>)` |
| `@audit:defect(circular)` | 仮説解除 → signature 修正 → body `sorry` → `@residual(defect:circular)` |
| `@audit:defect(prop-true)` | `:True` slot 削除 → 該当 residual を sorry 化 → `@residual(defect:prop-true)` |
| `@audit:defect(launder)` | rename → signature が claim 通り → `sorry` + 適切な `@residual` |
| `@audit:defect(degenerate)` | 退化定義削除 / 修正 → `sorry` + `@residual` |
| `@audit:defer(PLAN)` | sorry が同 file にあれば `@residual(plan:<PLAN>)` に置換、無ければタグ削除 (declaration 完成) |
| `@audit:closed-by-successor(SLUG)` | wrapper 自身に sorry があれば `@residual(plan:<SLUG>)` に置換、依存先の sorry は依存先で `@residual` 管理 (sorry-based ではタグ不要、type-check 経由で transitive 追跡) |
| 散文 `🟢ʰ` / `🟢ʰ load-bearing hypothesis` | 上記 `@audit:suspect` と同じ移行 |
| 散文 `**NOT a discharge**` / `**load-bearing — NOT a discharge.**` | 同上 |
| 散文 `⚠️ OPEN — conclusion-as-hypothesis` | `@audit:defect(circular)` と同じ移行 |

`@audit:defer` / `@audit:closed-by-successor` の deprecation 理由: 新方針では sorry の closure 担当 plan は `@residual(plan:<slug>)` で一元的に表現するため、別 tag で重ねて記録する必要が無い。依存先の sorry は Lean の type-check が transitive に追跡するので、wrapper 側に「後続が closure する予定」と明示する必要も無い (依存先の `@residual` を grep すれば十分)。

### 移行レシピ (suspect 1 件あたり)

```lean
-- 旧
/-- Stam ineq 経由の EPI step.
@audit:suspect(epi-stam-closure) -/
theorem epiStep
    (hStam : StamInequalityHolds μ ν)  -- ← load-bearing hyp
    (h... : ...) :  -- 残りは regularity
    epi μ ν := by
  exact ... hStam ...

-- 新
/-- Stam ineq 経由の EPI step.
@residual(plan:epi-stam-closure) -/
theorem epiStep
    (h... : ...) :  -- regularity だけ残す
    epi μ ν := by
  sorry
```

ポイント:
- `StamInequalityHolds` のような **core を抱える predicate hypothesis を削除**
- regularity (`IsFiniteMeasure`, full-support 等) は precondition なので残す
- body は `sorry` だけ
- tag を `@residual(plan:...)` に書換

shared sorry 補題化する場合は `StamInequalityHolds` を削除した代わりに `stamInequality μ ...` を body で呼び出し、補題側に `sorry` + `@residual(wall:stam)` を集約。

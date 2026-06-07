# 無限分散 a.c. 古典 EPI 構築 — truncation ルート moonshot 計画 🌙

> ## ✅ CLOSED 2026-06-07 — route T で genuine closure 完了 (sorryAx-free)
> 無限分散 a.c. 古典 EPI `entropyPowerExt_add_ge_infinite_variance` を route T で **sorryAx-free
> genuine closure**。`wall:epi-infinite-variance-classical` は FALSE WALL (sharp Young/Brascamp-Lieb
> 不要)。実装: `EPIInfiniteVarianceTruncation.lean` (全 sub-lemma A/B/C'/D/bdd/neg genuine + 監査
> PASS) + capstone `EPIInfiniteVarianceCapstone.lean` (P 版負部可積分 + wall の hent_sum case split)。
> dispatch `entropyPowerExt_add_ge_dispatch_skeleton` まで sorryAx-free、独立 honesty audit PASS
> (defect 0)。旧 sorry wall (`EPICase1SmoothingLimit.lean:1407`) 削除済、dispatch を capstone へ rewire 済。
> 主要発見: bdd cobound は compact support でなく per-n EPI 下界 (`Nₑ(μ_R)≥Nₑ(X_R)→Nₑ(X)>0`)、neg は
> `hX_ent/hY_ent` を crux-usc chain に threading 要 (a.c.+独立だけでは畳込み密度負部有限性が出ない)。
> 以下は計画立案時の記録 (履歴)。

> **親**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) §sub-plan 一覧 (S6)。
> **対象壁**: `@residual(wall:epi-infinite-variance-classical)` =
> `entropyPowerExt_add_ge_infinite_variance` (`InformationTheory/Shannon/EPICase1SmoothingLimit.lean:1407`)。
> **slug**: `epi-infinite-variance-truncation-plan` (← `@residual(plan:epi-infinite-variance-truncation-plan)` と一致)。
> **owner 確定 (2026-06-07)**: 無条件 EPI が究極ゴール。park でなく **genuine 構築**。Mathlib 不在は自前で建てる。
> 在庫: [`epi-infinite-variance-inventory.md`](epi-infinite-variance-inventory.md) / [`epi-uncond-truncation-lsc-inventory.md`](epi-uncond-truncation-lsc-inventory.md)。

## 規模見積りサマリ

> **Phase 0 feasibility gate 実行済 (2026-06-07): route T GO + crux usc は FALSE WALL (genuine 閉じる)。**
> 詳細は判断ログ 4。crux は標準ツール (Gibbs + DCT) で閉じる buildable 補題に降格。route Y (sharp Young)
> は deep-fallback のみ。

| 項目 | 見積り |
|---|---|
| primary ルート | **T (conditioning truncation)** — 確定 GO。有限分散 EPI 黒箱 (`entropyPowerExt_add_ge_of_finite_variance`, `:1351`, sorryAx-free) を `X_R = X\|{\|X\|≤R}` に適用 → R→∞。**無限分散 EPI を sorryAx-free で genuine 閉じる見込み** |
| deep-fallback ルート | **Y (sharp Young / Lieb 1978)**: Mathlib 0% (Riesz rearrangement + Brascamp-Lieb)、research-grade。**T が予期せぬ Lean 化障害で詰まった場合のみ** (Phase 0 で usc 数値確認 + 機構あり → 発動可能性極小) |
| 新規行数オーダー (T) | **~350-500 行** (moderate、research-grade でない): P1 skeleton + usc signature ~80 / P2 優関数+a.c.+Gibbs usc 本体 ~150 / P3 RHS 収束 + per-R 供給 ~150 / P4 assembly ~80 |
| touch file | 新 file `InformationTheory/Shannon/EPIInfiniteVarianceTruncation.lean` + `EPICase1SmoothingLimit.lean:1407` (wall body 差替) + `InformationTheory.lean` (import 1 行) |
| crux 補題の難易度 | **buildable** (Mathlib 壁でない)。Gibbs step は in-tree template `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`) の Gaussian 参照 → 一般参照 (p∗q) generalize、cross-entropy は DCT (`tendsto_integral_of_dominated_convergence`)、優関数 `p_R∗q_R ≤ C²(p∗q)` |
| 新 wall の要否 | **不要見込み** (`wall:entropy-usc-truncation` は降格、register 追記しない)。Lean 化で予期せず詰まった場合のみ named wall 残置 (L-IVT-2、発動可能性極小) |

## 進捗

- [x] Phase 0 — feasibility gate ✅ **GO (2026-06-07)**: usc 数値反例ゼロ + Gibbs+DCT 機構確定 → crux false-wall 降格 (判断ログ 4)
- [ ] Phase 1 — 全体 skeleton + crux usc 補題 signature 📋
- [ ] Phase 2 — 優関数 `p_R∗q_R ≤ C²(p∗q)` + a.c. + Gibbs usc 補題本体 📋
- [ ] Phase 3 — RHS 収束 `h(p_R) → h(p)` + per-R 有限分散/有限エントロピー供給 📋
- [ ] Phase 4 — R→∞ 極限 assembly → wall body 差替 + honesty-auditor 📋

## ゴール / Approach

**ゴール**: `entropyPowerExt_add_ge_infinite_variance` (`:1407`) の body `sorry` を genuine に消す。
両 a.c. + 両有限微分エントロピー (`hX_ent`/`hY_ent`) + 無限分散 (`h_infvar`) で
`Nₑ(X+Y) ≥ Nₑ(X) + Nₑ(Y)` を証明する。

**Approach (全体戦略、Phase 0 で route T 確定)**:

- **route T (conditioning truncation) = 採用ルート**。なぜ T か: **有限分散 EPI が既に genuine
  closure 済 (`entropyPowerExt_add_ge_of_finite_variance`, sorryAx-free)** で、これを黒箱再利用
  できる。`X_R := X conditioned on {\|X\|≤R}` は compact support ゆえ有限分散 + 有限エントロピー +
  a.c.(`cond_absolutelyContinuous` で保存) を満たすので、各 R で黒箱 EPI が立つ。残るは R→∞ の極限
  制御だけ。**Phase 0 で唯一の懸念だった crux usc が false-wall と判明** (Gibbs + DCT、標準ツールのみ)
  ので、T は無限分散 EPI を **sorryAx-free で genuine 閉じる**。sharp Young 不要。
- **route Y (sharp Young / Lieb 1978) = deep-fallback のみ**。分散非依存の確実路だが Mathlib 0%
  (Riesz 対称減少再配置・Brascamp-Lieb・sharp Young 定数 全不在、在庫 §A、loogle Found 0 × 7)。
  research-grade。**T が予期せぬ Lean 化障害で詰まった場合のみ** (発動可能性極小、Phase 0 で
  usc 数値確認済 + 機構あり)。

**crux usc の証明機構 (Phase 0-B 確定、Gibbs + DCT)** — 分散発散は red herring:
1. **優関数**: `p_R = p·1_{[-R,R]}/m_R ≤ p/m_R ≤ C·p` (`m_R ↑ 1`、下界 `m_3 > 0`、`C := 1/m_3`)。
   ⟹ `p_R∗q_R ≤ C²·(p∗q)` pointwise。これが (a) `law(X_R+Y_R) ≪ law(X+Y)` (p∗q=0 → p_R∗q_R=0) と
   (b) DCT の優関数の両方を供給。
2. **Gibbs step**: `h(X_R+Y_R) = -∫(p_R∗q_R)log(p_R∗q_R) ≤ -∫(p_R∗q_R)log(p∗q)` を
   `(klDiv (law X_R+Y_R) (law X+Y)).toReal ≥ 0` から (klDiv は ℝ≥0∞ 値 → 非負は `ENNReal.toReal_nonneg`
   で型自明)。in-tree template = `differentialEntropy_le_gaussian_of_variance_le`
   (`DifferentialEntropy.lean:520`、Gaussian 参照での同じ Gibbs+llr 分解、`toReal_klDiv_of_measure_eq`
   経由) を **Gaussian → 一般参照 (p∗q) に generalize するだけ**。`toReal_klDiv_of_measure_eq` は
   プロジェクト多用 (Sanov/Stein/MaxEntropy/ParallelGaussianConverse/EPIG2KLVariationalLower)。
3. **cross-entropy DCT**: `-∫(p_R∗q_R)log(p∗q) → -∫(p∗q)log(p∗q) = h(X+Y)`。優関数 `C²·(p∗q)|log(p∗q)|`
   は和の有限微分エントロピー (`Integrable(negMulLog(p∗q))` = 絶対可積分) で可積分。
   `MeasureTheory.tendsto_integral_of_dominated_convergence`。
4. ⟹ `limsup_R h(X_R+Y_R) ≤ h(X+Y)`。

**向きの注意 (在庫 §B / `epi-uncond-truncation-lsc-inventory.md` §1-B と逆)**: 方針 Y (Gaussian
smoothing t→0⁺) は entropy の **LSC (liminf ≤)** を要求、本ルート T は **usc (limsup ≤)** で逆。
既存 `negMulLog_convDensity_limsup_le` (`EPIG2KLFatouLSC.lean:360`) は向き一致だが `hpX_mom`
(有限2次モーメント) + Gaussian 固定相手ゆえ直接流用不可。本 T は上記 Gibbs+DCT (固定参照 = p∗q)
で moment 非依存に閉じる別機構。

## Phase 0 - feasibility gate ✅ 実行済 GO (2026-06-07)

> **結果**: route T GO + crux usc は **FALSE WALL** (標準ツール Gibbs+DCT で genuine 閉じる)。
> 詳細根拠は判断ログ 4。以下は確定事実の要約。

- [x] **0-A 数値反例探索 (反例ゼロ)**: heavy-tail 3 ケース (Cauchy [無限分散+無限平均、裾 x⁻²] /
      peaked [高ピーク~8000、entropy 整数関数両符号 h<0] / asymmetric [左右裾指数違い]) で
      `h(X_R+Y_R)` は全例 **`h(X+Y)` へ下から単調収束** (overshoot 常に負 → 0)。`Var(X_R)` は発散継続
      (Cauchy で R=3000 時 Var=1909) するのに和エントロピーは収束 → crux usc は数値的に robust に真。
      退化境界 (Dirac 近傍 / m_R→0) も暴れず。スクリプト `/tmp/epi_usc_test.py` `/tmp/epi_usc_test2.py`。
- [x] **0-B 機構確定 (Gibbs + DCT、標準ツールのみ)**: §Approach「crux usc の証明機構」4 step。
      分散発散は red herring。優関数 `p_R∗q_R ≤ C²(p∗q)` + Gibbs (`toReal_klDiv_of_measure_eq`、
      template `DifferentialEntropy.lean:520`) + cross-entropy DCT で閉じる。
- [x] **0-B a.c. 保存確認**: `ProbabilityTheory.cond_absolutelyContinuous`
      (`Mathlib/Probability/ConditionalProbability.lean:183`, `μ[\|s] ≪ μ`) で conditioning の a.c. 保存。
      さらに上記優関数 1 が `law(X_R+Y_R) ≪ law(X+Y)` を直接供給 (p∗q=0 → p_R∗q_R=0)。
- [x] **判定**: **T GO**。crux usc は buildable 補題に降格 (Mathlib 壁でない)。Y は deep-fallback。

proof-log: no (調査 phase、判断は判断ログ 4 に記録済)。

## Phase 1 - 全体 skeleton + crux usc 補題 signature 📋

> 新 file `EPIInfiniteVarianceTruncation.lean` の skeleton。全補題を `:= by sorry` で立て type-check
> 確認 (skeleton-driven)。crux usc 補題の signature を honest に固定する (核を仮説に bundle しない)。

- [ ] **conditioning 構成の def**: `X_R := X` on `P_R := P[·\|{\|X\|≤R} ∩ {\|Y\|≤R}]` (X,Y 同時
      conditioning、独立性保存を狙う) or 各々別 conditioning。設計判断: `IndepFun X_R Y_R P_R` が
      立つ方を選ぶ (skeleton で両 candidate を並べ通る方を残す)。
- [ ] **crux usc 補題 signature** `entropyPower_sum_truncation_limsup_le` :
      `limsup_R Nₑ(P_R.map(X_R+Y_R)) ≤ Nₑ(P.map(X+Y))`。**honest signature 規律 (CLAUDE.md)**:
      usc/EPI の核を `*Hypothesis` predicate に bundle しない。仮説は regularity precondition のみ
      (a.c. / measurable / `hW_ent` = 和の有限微分エントロピー)。`hW_ent` は DCT 優関数可積分性に
      load-bearing でなく precondition (結論の不等式を encode しない)。
- [ ] **per-R 黒箱 EPI 補題 signature** + RHS 収束補題 signature + assembly 主補題 signature を skeleton。
- [ ] type-check 確認 (`lake env lean`、sorry warning のみ)。

proof-log: yes。

## Phase 2 - 優関数 + a.c. + Gibbs usc 補題本体 📋

> crux の核 (旧「genuine 難所」、Phase 0 で false-wall 確定)。Gibbs + DCT を埋める。

- [ ] **優関数補題**: `m_R ↑ 1` (確率密度の growing-set 積分)、下界 `m_{R₀} > 0` 固定 → `C := 1/m_{R₀}`、
      `p_R ≤ C·p` pointwise → `p_R∗q_R ≤ C²·(p∗q)` pointwise (畳込みの monotone)。
- [ ] **a.c. 補題**: `law(X_R+Y_R) ≪ law(X+Y)` (上の優関数: `p∗q=0 → p_R∗q_R=0`)。
- [ ] **Gibbs step**: `h(X_R+Y_R) ≤ -∫(p_R∗q_R)log(p∗q)` を `(klDiv (law X_R+Y_R)(law X+Y)).toReal ≥ 0`
      から。template `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`、
      Gaussian 参照) を **一般参照 (p∗q) に generalize**。`toReal_klDiv_of_measure_eq` を使う
      (プロジェクト多用 decl)。klDiv ℝ≥0∞ 値 → 非負 `ENNReal.toReal_nonneg` 型自明。
- [ ] **cross-entropy DCT**: `-∫(p_R∗q_R)log(p∗q) → -∫(p∗q)log(p∗q) = h(X+Y)`。優関数
      `C²·(p∗q)|log(p∗q)|` は `hW_ent` (= `Integrable(negMulLog(p∗q))`) で可積分。
      `MeasureTheory.tendsto_integral_of_dominated_convergence`。a.e. 各点収束は `p_R∗q_R → p∗q`
      (優収束 + m_R→1) から。
- [ ] **合成**: `limsup_R h(X_R+Y_R) ≤ h(X+Y)` → entropyPower 側 `Nₑ` に exp 単調で持ち上げ。

proof-log: yes (本 phase が実装の核)。

## Phase 3 - RHS 収束 + per-R 供給 📋

> 黒箱 EPI を per-R で立てる前提供給 + RHS の R→∞ 収束。

- [ ] **per-R 有限分散**: `Integrable ((X_R)²) P_R` (compact support [-R,R] で有界 → 全 moment 自明)。
      `IndepFun.variance_add` の `MemLp 2` 要求 (在庫 §D ★最危険) は compact support で自動充足、明示確認。
- [ ] **per-R 有限エントロピー 3 本** `hX_ent`/`hY_ent`/**`hent_sum`** を `X_R, Y_R, X_R+Y_R` で再供給。
      **verbatim 確認済**: 黒箱 `entropyPowerExt_add_ge_of_finite_variance` (`:1351`) は `hent_sum`
      (和の有限微分エントロピー) を**明示引数として要求**するが wall theorem 側には**無い**。global
      `hX_ent` を growing set で X_R に降ろす + 和は compact support の有界密度で integrable。
- [ ] **黒箱 per-R EPI**: 上記 threading で `Nₑ(X_R+Y_R) ≥ Nₑ(X_R)+Nₑ(Y_R)` を各 R で得る。
- [ ] **RHS 収束 `h(p_R) → h(p)`** (moment 非経由、無限分散でも効く): `-∫p_R log p_R =
      -(1/m_R)∫_{[-R,R]} p log p + log m_R`。第1項は固定可積分 `p log p` (= `hX_ent`) の growing-set
      DCT (`tendsto_integral_of_dominated_convergence`)、第2項 `log m_R → 0` (m_R→1)。`Nₑ(X_R) → Nₑ(X)`
      へ `entropyPowerExt_of_ac_integrable` で持ち上げ。

proof-log: yes。

## Phase 4 - R→∞ 極限 assembly + wall body 差替 📋

- [ ] **clean limsup chain**: per-R `Nₑ(X_R+Y_R) ≥ Nₑ(X_R)+Nₑ(Y_R)` (P3) + RHS 収束
      `Nₑ(X_R)+Nₑ(Y_R) → Nₑ(X)+Nₑ(Y)` (P3) + usc `Nₑ(X+Y) ≥ limsup Nₑ(X_R+Y_R)` (P2)。
      合成: `Nₑ(X+Y) ≥ limsup Nₑ(X_R+Y_R) ≥ limsup[Nₑ(X_R)+Nₑ(Y_R)] = Nₑ(X)+Nₑ(Y)`。
      Mathlib `le_of_tendsto` / `Filter.limsup_le_limsup` / `Tendsto.add`。
- [ ] **wall body 差替**: `entropyPowerExt_add_ge_infinite_variance` (`:1407`) body の `sorry` を
      assembly に置換。docstring の `@residual(wall:epi-infinite-variance-classical)` 除去。
      `#print axioms` で **transitive sorry 0** (genuine close) を確認。
- [ ] **import 追加**: `InformationTheory.lean` に新 file 1 行。dispatch
      `entropyPowerExt_add_ge_dispatch_skeleton` (`EPIUncondDispatch.lean`) の唯一の transitive sorry
      が消えたことを `#print axioms` で確認 (= 無条件 EPI case 1 完成)。
- [ ] **honesty-auditor 起動 (必須)**: (a) wall slug 除去が genuine (transitive 0 sorry) か、
      (b) Phase 1-4 が load-bearing hyp を作っていないか (per-R regularity / `hW_ent` は precondition、
      usc 核は Gibbs+DCT で body 内、bundle 不可)、(c) `h_infvar`/`hX_ent`/`hY_ent` が precondition
      であって結論を encode していないか、(d) crux usc 補題の signature honest check。

proof-log: yes。

## 自作する補題 (genuine、Mathlib 壁でない)

| 補題 | 内容 | Mathlib/in-tree template | 状態 |
|---|---|---|---|
| crux usc `entropyPower_sum_truncation_limsup_le` | `limsup h(p_R∗q_R) ≤ h(p∗q)`、Gibbs+DCT | template `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`) を一般参照 generalize + `toReal_klDiv_of_measure_eq` + `tendsto_integral_of_dominated_convergence` | **buildable** (Phase 0 で false-wall 確定、register 追記しない) |

**新 wall `wall:entropy-usc-truncation` は降格 (register 追記しない)**: Phase 0 で usc が標準ツール
で閉じる buildable 補題と判明したため、genuine Mathlib 壁ではない。**Lean 化で予期せず詰まった
場合のみ** named wall として残置 (L-IVT-2、発動可能性極小)。その場合の semantic 区別 (方針 Y の
`wall:entropy-lsc-weak` [LSC, Gaussian] / `wall:gaussian-approx-identity-weak` [弱収束] と逆方向 +
別切詰機構) は L-IVT-2 発動時に register へ記録。

## 撤退ライン

honest 撤退口 = `sorry` + `@residual(<class>:<slug>)`。**禁止 (CLAUDE.md 共通規律)**: load-bearing
hypothesis の bundling (`*Hypothesis` predicate に usc/EPI の核を抱えさせる) / `Prop := True`
placeholder / 仮説型≡結論の `:= h` 循環 / 退化定義悪用。

> **発動可能性 (Phase 0 後)**: L-IVT-1/2 はともに **発動可能性極小に降格** (usc 数値確認済 +
> Gibbs+DCT 機構あり)。保持はするが想定外の Lean 化障害が出た場合のみ。

- **L-IVT-1 (usc 偽、発動可能性極小)**: 万一 Lean 化中に usc が偽と判明 (Phase 0 の数値 robust 性に
  反する) → **T 放棄、route Y (sharp Young) へ縮退**。Y 着手は別 plan/Phase で sizing
  (sharp Young の Mathlib 不在 0% を 0 から建てる research-grade、本 plan の scope 外)。
- **L-IVT-2 (Gibbs/DCT の Lean 化が予期せず詰まる、発動可能性極小)**: Phase 1/3/4 は genuine に組み、
  Phase 2 crux usc のみ `sorry` + `@residual(wall:entropy-usc-truncation)` で named wall に**当座
  退避**。その時点で register 追記 + 壁判定メタデータ記録。**Phase 0 で false-wall 確定済**なので
  これは一時退避であり恒久壁でない (機構は分かっている、Lean plumbing だけの問題のはず)。
- **L-IVT-3 (当座着地、最終手段)**: 万一 T も Y も当座 close 不能なら wall body を現状の
  `@residual(wall:epi-infinite-variance-classical)` で honest tier-2 park 継続。owner 確定 (genuine
  構築方針) に反するので **最終手段** — Phase 0 で T が GO ゆえ発動見込みなし。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正。決着済 entry は削除 (git が履歴)。

1. **route T 確定、Y は deep-fallback (2026-06-07)**: owner が genuine 構築方針を確定 + Phase 0 で
   T GO 判明。有限分散 EPI 黒箱 (`entropyPowerExt_add_ge_of_finite_variance`, sorryAx-free 確認済) の
   再利用 leverage + crux usc false-wall (判断ログ 4) が T 採用の決め手。Y (sharp Young) は Mathlib
   0% ゆえ T が予期せず詰まった場合のみの deep-fallback。
2. **conditioning を構成手段に採択 (在庫 §E #2 の a.c. 破壊回避)**: 素朴 indicator truncation
   `1_{\|X\|≤R}·X` は law に atom を作り a.c. を壊す (在庫 §E #2 隠れ難所)。`cond_absolutelyContinuous`
   (`ConditionalProbability.lean:183`) が conditioning の a.c. 保存を供給 → conditioning
   `P[·\|{\|·\|≤R}]` を採る。加えて crux 優関数 `p_R∗q_R ≤ C²(p∗q)` が `law(X_R+Y_R) ≪ law(X+Y)` も
   直接供給。
3. **crux usc を方針 Y の壁と分離 (在庫 §F「同核共有」への修正)**: 在庫 §F は方針 Y の
   `wall:entropy-lsc-weak` と本ルートが同核共有と示唆したが、**本 crux は向きが逆 (limsup ≤) + 切詰
   機構が別 (conditioning vs Gaussian smoothing) + moment 非依存の Gibbs+DCT で閉じる**ので別物。
   shared sorry 補題化しない (そもそも本 crux は壁でない)。
4. **Phase 0 feasibility gate 実行 → route T GO + crux usc は FALSE WALL に降格 (2026-06-07)**:
   - **数値反証ゼロ**: heavy-tail 3 ケース (Cauchy 無限分散+無限平均 / peaked h<0 / asymmetric) で
     `h(X_R+Y_R)` が全例 `h(X+Y)` へ下から単調収束 (overshoot 負→0)。`Var(X_R)` 発散継続 (Cauchy
     R=3000 で Var=1909) でも和エントロピーは収束 → 分散発散は red herring。`/tmp/epi_usc_test*.py`。
   - **clean 証明機構確定 (Gibbs+DCT、標準ツール)**: 優関数 `p_R∗q_R ≤ C²(p∗q)` (m_R↑1, C=1/m_{R₀}) →
     (a) a.c. + (b) DCT 優関数。Gibbs `h(X_R+Y_R) ≤ -∫(p_R∗q_R)log(p∗q)` は klDiv≥0
     (`toReal_klDiv_of_measure_eq`、template `DifferentialEntropy.lean:520` を一般参照 generalize)。
     cross-entropy `→ h(X+Y)` は `hW_ent` 優関数で DCT。
   - **降格**: crux は genuine Mathlib 壁でなく buildable 補題。route T は無限分散 EPI を sorryAx-free
     で genuine 閉じる。**新 wall `wall:entropy-usc-truncation` は register 追記しない** (L-IVT-2
     発動時のみ当座退避)。Y (sharp Young) は deep-fallback に降格。

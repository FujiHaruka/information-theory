# EPI per-time de Bruijn identity — closure サブ計画

> **Parent**: [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md) §Phase B
> (撤退ライン L-EPI2 = de Bruijn integration の genuine discharge)。grandparent: [`epi-moonshot-plan.md`](epi-moonshot-plan.md)。
> **Inventory**: [`epi-debruijn-pertime-reattack-inventory.md`](epi-debruijn-pertime-reattack-inventory.md)、案B 在庫 [`epi-debruijn-gap2-caseB-joint-domination-inventory.md`](epi-debruijn-gap2-caseB-joint-domination-inventory.md)。
> **Wall SoT**: `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:245` (`debruijnIdentityV2_holds`)。
> **slug**: `epi-debruijn-pertime-closure` (= `@residual(plan:epi-debruijn-pertime-closure)`)。

**ゴール**: EPI moonshot の残壁 `debruijnIdentityV2_holds` を一般 `X` で genuine 化し `@audit:ok`
へ (Gaussian case は `deBruijn_identity_v2_gaussian` で既 genuine)。assembly は新 file
`FisherInfoV2DeBruijnAssembly.lean` (import 循環回避)。

## 進捗

- [x] Phase 0 — signature pivot (false→true) ✅ (commit `138bc49`/`42f8a85`、独立監査 honest、wall→plan 再分類)。`IsRegularDeBruijnHypV2` に density-pin field、`debruijnIdentityV2_holds` に `_hX/_hZ/_hXZ`。
- [x] Phase 1 — density 同定 ✅ (`gaussianConvolution_law_conv` / `pPath_eq_convDensityAdd`、`@audit:ok`、commit `6f675ca`)。
- [x] Phase 2 — heat equation per-density ✅ (kernel 群 7 件 + `heatFlow_density_heat_equation` main、`@audit:ok`、commit `68f80e2`)。
- [x] Phase 3 — entropy parametric diff ✅ (`entropy_hasDerivAt_via_parametric`、`@audit:ok`)。
- [x] Phase 4 — 無限区間 IBP ✅ (`debruijn_ibp_step` + `fisher_from_logDeriv`、`@audit:ok`)。
- [x] Phase 5-F — `density_t_eq` rnDeriv-pin defect → conv pin 差替 ✅ (commit `9de3c02`、`_fisher_match` genuine、Gaussian constructor `density_t_eq` genuine via `convDensityAdd_gaussian_closed_form`)。判断ログ #9。
- [~] Phase 5 — capstone assembly 🔄: `debruijnIdentityV2_holds_assembled` は 6 genuine atom 合成で配線済、`_entropy_eq` genuine。`_chain` (段2-7 解析核) を 5 sub-lemma に分割 (#1 `_chain_entDeriv_formula` genuine)。**残 = 案B 実装 (§Phase 5-G case B)**。

> **残課題 (proof done まで)**: 6 atom は全 genuine。残るは `_chain` の解析核を **案B (joint
> domination)** で閉じること — (1) GAP② を polynomial-moment envelope に restate、(2)
> `_chain_domination` を joint envelope (Tonelli+moment 正路) に、(3) 共有壁
> `gaussianConv_fisher_le_inv_var` (新 file `FisherConvBound.lean`) を `convDensityAdd_fisher_integrable`
> + `_chain_ibp_fisher` の 2 consumer で共有、(4) `hpX_mom` + `IsRegularDeBruijnHypV2.pX_mom` threading。
> 詳細 → §Phase 5-G case B。両 gap closure → `#print axioms` sorryAx 非依存 → 独立監査 → `@audit:ok`
> で EPI moonshot per-time 壁 proof done。

### Approach (解の全体形)

density-route 経由の解析核を atom 分解で積む: pushforward density = `convDensityAdd pX (Gaussian
density at √s)` の同定 (Phase 1) → 時刻微分 `∂_s pPath` の heat equation (Phase 2、軸2 Gaussian
heat semigroup は Mathlib 全不在ゆえ density-route 自作で迂回) → entropy 積分の parametric diff
(Phase 3) → 無限区間 IBP で logDeriv→Fisher (Phase 4) → 最終 congr (Phase 5)。解析核に真の
Mathlib 壁 (分類 c) は **Fisher integrability 1 本のみ** (Stam convolution Fisher bound、判断ログ
#12) で、共有壁 `gaussianConv_fisher_le_inv_var` に局所化。他は全て in-tree atom への plumbing。

**honesty 制約 (全 Phase 共通)**: `IsRegularDeBruijnHypV2` の追加 field (`pX` 系 / `pX_mom`) と各
atom の domination hyp は **regularity precondition** (密度 witness の外形等式 + 被積分関数の
微分・有界性) であって load-bearing でない。`HasDerivAt`/Fisher/heat eq の **結論を hyp に bundle
しない** (L-PT-α 禁止事項)。詰まったら `sorry` + `@residual(plan:epi-debruijn-pertime-closure)`
(tier 2)。

---

## Phase 0-4 (完了済、anchor)

> 全て `@audit:ok` sorryAx-free。詳細手順は完了済のため anchor のみ。再検証は各 declaration の
> `#print axioms` で都度。

- **Phase 0** signature pivot: `density_t := 0` 反例を排除する density-pin field 追加 + `_hX/_hZ/_hXZ`
  復元 (underscore-prefixed args、判断ログ #3)。pin は外形等式に留め core を bundle しない (判断ログ #2)。
- **Phase 1** `pPath_eq_convDensityAdd` (`FisherInfoV2DeBruijnPerTime.lean`): pushforward density =
  `convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩)`。
- **Phase 2** `heatFlow_density_heat_equation`: `∂_s pPath = (1/2)∂²_x pPath`。kernel 群で
  `∂_σ g_σ = (1/2)∂²_u g_σ` genuine、∫越し lift も genuine 化済 (domination は per-y 被積分関数
  regularity、判断ログ #6)。
- **Phase 3** `entropy_hasDerivAt_via_parametric`: parametric integral diff。**注**: `hb`/`hdiff` は
  `∀ s ∈ Set.Ioo (t/2)(2t)` 量化 (univ 量化は s→∞/0+ 発散で instantiate 不能、判断ログ #11 で弱化)。
- **Phase 4** `debruijn_ibp_step` (無限区間 IBP、境界項消去版) + `fisher_from_logDeriv`
  (`∫(logDeriv p)²·p = fisherInfoOfDensityReal p`)。

---

## Phase 5 — capstone assembly 🔄

> proof done 到達点。`debruijnIdentityV2_holds_assembled` (`FisherInfoV2DeBruijnAssembly.lean`、元
> wall と同 signature) を 6 atom 合成で配線済。assembly 段構成: density 同定 → entropy=∫negMulLog →
> parametric diff → heat eq → IBP → fisher congr → value match。
>
> structure 拡張 (`pX`/`pX_nn`/`pX_meas`/`pX_law` の 4 field、全 regularity) + `density_t` conv pin は
> **コード上 closed** (Phase 0/5-F)。`density_t_conv` は field 化せず assembly body で
> `pPath_eq_convDensityAdd` を直接呼んで導出 (Phase 1b 結論を bundle しない、判断ログ #5)。consumer
> ripple は Gaussian constructor (`isRegularDeBruijnHypV2_family_of_gaussian`) 1 点に集約 (判断ログ #7)。
>
> **残 = `_chain` (段2-7 解析核)**。5 sub-lemma に分割: #1 `_chain_entDeriv_formula` (entDeriv 閉形
> `(-log p-1)·(1/2)·∂²_x p`、genuine) / #2 `_chain_domination` (joint envelope、L-PT-γ′) / #3
> `_chain_parametric` (段3+4 合成、#2 供給後 genuine) / #4 `_chain_ibp_fisher` (段5+6 IBP+fisher、
> 既に IBP→Fisher genuine plumbing 化、Fisher integrability は共有壁経由) / #5 `_chain` 本体 (段7+
> `max s 0` 近傍補正、plumbing genuine)。全 sub-lemma 同一 file ゆえ並列不可、単一 implementer 逐次。
> 実装 brief は **§Phase 5-G case B** (active)。

---

## 撤退ライン (L-* マーカー)

各 Phase の honest 撤退口。すべて **sorry + `@residual(plan:epi-debruijn-pertime-closure)`** 維持、
仮説束化禁止。

| マーカー | Phase | 発動条件 |
|---|---|---|
| **L-PT-β** | 1 | density 同定 repo bridge ~60 行超 → 別 lemma 切出し独立 residual |
| **L-PT-α** | 2 | heat eq per-density ~120 行超 → Gaussian case genuine + 一般 X は sorry 維持 |
| **L-PT-γ** | 3 | Gaussian-tail dominating function `Integrable` が PR 級 → bound 補題を別 residual |
| **L-PT-δ** | 4 | `tsupport` 全域 `HasDerivAt` / tail decay の一般 X 証明 ~50 行超 → 別 residual |
| **L-PT-γ′** | 5 (案B) | `_chain_domination` joint envelope integrability (Tonelli+moment) が ~80 行超 → 第1 sorry 据置、GAP② restate + body wiring 型整合で defect 解消 |
| **L-PT-ε** | 5 (案B) | 共有壁 `gaussianConv_fisher_le_inv_var` R-A route が genuine 化不能 → body sorry + `@residual(wall:fisher-finiteness)`。最小成果 = defect 解消 + 全 sorry tier 2 化 |

**全 Phase 共通禁止**: `IsRegularDeBruijnHypV2` に `HasDerivAt`/Fisher core を bundle (load-bearing、
`density_t` を証明の核心化) / `:True` slot / 循環 `:= h` / 退化定義悪用 (rnDeriv pin 等)。

## 検証

| Phase | 完了基準 | 独立監査 |
|---|---|---|
| 0 | type-check done、命題 false→true、wall→plan 再分類 | **要** |
| 1-4 | type-check done (各 atom)、残 sorry は `@residual` タグ付き | 新規 shared sorry 補題追加時のみ |
| 5 | proof done (`debruijnIdentityV2_holds` 0 sorry/0 @residual、`#print axioms` sorryAx 非依存) | **要** |

inner loop = `lake env lean InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean` + ripple
file 個別。structure field 追加時は `lake build InformationTheory.Shannon.FisherInfoV2DeBruijn` 1 回
で olean refresh。`lake build` は使わない (CLAUDE.md「Verification」)。

---

## §Phase 5-G case B: joint domination 実装 brief 〔ACTIVE〕

> 判断ログ #16 (案B 採用) + #17 (route 訂正) の実装 brief。在庫 SoT:
> `epi-debruijn-gap2-caseB-joint-domination-inventory.md`。case A (finite-2nd-moment で GAP②
> Gaussian-tail true 化) は判断ログ #15 で REJECT 済 (polynomial-tail finite-variance 反例)。
> scope = finite-2nd-moment pX (polynomial-tail `(2/π)/(1+y²)²` は対象内、Cauchy `∫y²=∞` は honest
> exclusion)。

### Approach (案B)

分離積 (GAP① log-factor × GAP② Hessian) は GAP② に Gaussian-tail を要求し polynomial-tail
finite-variance pX で FALSE (判断ログ #15)。案B は joint domination に切替:

1. **GAP② を polynomial-moment envelope に restate** (撤回でなく書換)。`convDensityAdd_deriv2_tail_majorant`
   → `convDensityAdd_deriv2_poly_moment_majorant`、結論を Gaussian-tail `≤C(1+x²)exp(-x²/c')` (false)
   から **`∃ bound, Integrable bound ∧ ‖∂²_x p_s‖ ≤ bound`** (true、`g_s` Gaussian を畳込内保持) に。
   polynomial-tail 反例は Gaussian-tail を主張しない restate には反例にならない。`@audit:defect(false-statement)`
   + `@audit:retract-candidate` を除去。
2. **`_chain_domination` body を joint envelope に書換**。pointwise envelope `(A+Bx²)·(1/2)hessBound(x)`
   (A,B = GAP① log majorant 係数、hessBound = GAP② envelope) を gateway に渡し、その `Integrable` を
   **Tonelli で外積分側に流す** (正路、判断ログ #17): `∫(A+Bx²)·hessBound dx = ∫pX(y)·K(y)dy`、
   K(y) は y の degree-2 多項式 → `c0+c1·E[X]+c2·E[X²] < ∞` (mass+1st+2nd moment、1st は `2|y|≤1+y²`
   で従属)。**❌ route I 禁止**: hessBound を `x^k·exp(-x²/c)` Gaussian 形に取り
   `integrable_natPow_mul_exp_neg_mul_sq` で閉じるのは案A defect 再来 (heavy-tail pX が x-tail を支配し
   Gaussian 因子が消える、mpmath 検算 `x⁴·hessBound→0.616`)。
3. **共有壁 `gaussianConv_fisher_le_inv_var`** (新 file `FisherConvBound.lean`、結論
   `fisherInfoOfDensity (convDensityAdd pX g_s) ≤ ENNReal.ofReal (1/s)`) を `convDensityAdd_fisher_integrable`
   + `_chain_ibp_fisher` の **2 consumer** で共有 (`_chain_domination` は moment route で Fisher 壁不要、
   判断ログ #17 で「1壁3consumer」→「1壁2consumer」訂正)。

honesty 要: GAP② を false 結論のまま残して joint を積むと vacuous-genuine 罠を再発 (判断ログ #15)。
**GAP② の結論型を polynomial-moment 形に書換える (Gaussian-tail 結論削除) が必須前提**。

### 実装 step (skeleton-driven)

| step | 作業 | file |
|---|---|---|
| 0 | 新 file `FisherConvBound.lean` skeleton: `gaussianConv_fisher_le_inv_var` (honest sorry `@residual(wall:fisher-finiteness)`) + import + namespace。`InformationTheory.lean` に import 1 行 | `InformationTheory/Shannon/FisherConvBound.lean` (新) |
| 1 | GAP② restate: rename + 結論型を integrable envelope に書換 + defect タグ除去 | `FisherInfoV2DeBruijnAssembly.lean` (GAP②) |
| 2 | `_chain_domination` body 書換: GAP② restate を obtain + joint envelope (Tonelli+moment) の integrability/domination。defect タグ除去、docstring を joint-domination note に | 同上 (`_chain_domination`) |
| 3 | `convDensityAdd_fisher_integrable` body の `sorry` を `gaussianConv_fisher_le_inv_var` 呼出 + R-A Step 3 plumbing に置換。`_chain_ibp_fisher` は transitive、変更不要 | 同上 + import `FisherConvBound` |
| 4 | `hpX_mom` threading: `_chain_parametric`/`_chain`/top assembled + `IsRegularDeBruijnHypV2` に `pX_mom` field 新規追加。top body は `h_reg.pX_mom` 直渡し (`pX_law` から導出不能 = 確率測度は有限分散を含意しない) | `FisherInfoV2DeBruijnAssembly.lean` + `FisherInfoV2DeBruijn.lean` + 全 constructor ripple |

> **step 4 ripple**: 全 constructor (`rg 'IsRegularDeBruijnHypV2' InformationTheory/`) が `pX_mom`
> 不足になる。Gaussian constructor は Gaussian source が有限分散ゆえ充足可 (新規 sorry になるなら
> `@residual(plan:epi-debruijn-pertime-closure)`)。波及範囲は implementer が確認・報告。

### honest sorry vs genuine plumbing 区分

| 箇所 | 状態 |
|---|---|
| `gaussianConv_fisher_le_inv_var` (壁 body) | **honest sorry** `@residual(wall:fisher-finiteness)` (R-A = density-level score Cauchy-Schwarz、Mathlib/repo 不在) |
| GAP② `_poly_moment_majorant` body | **honest sorry** `@residual(plan:...)` (STEP D bridge + moment 展開) |
| `_chain_domination` 第1 sorry (joint envelope integrability) | **honest sorry** `@residual(plan:...)` (Tonelli+moment core) |
| `_chain_domination` 第2 sorry (norm_mul domination) | **genuine plumbing** (現 body 流用、最終 0 sorry) |
| `convDensityAdd_fisher_integrable` body | **genuine plumbing** (壁の有限上界を消費、`integrable_iff_lintegral_ofReal_lt_top` 系) |
| `_chain_ibp_fisher` | **genuine plumbing 既存** (変更不要) |
| `hpX_mom` threading / `pX_mom` field | **genuine plumbing** (regularity 配線、load-bearing でない) |

### 独立 honesty audit 起動条件

新規 shared sorry 補題追加 + GAP②/`_chain_domination` signature/body 変更 (defect 除去) + structure
field 追加 → 実装後 `honesty-auditor` 起動必須。スコープ: (i) `gaussianConv_fisher_le_inv_var` が
load-bearing でない・2 consumer が壁を lemma call で受ける、(ii) GAP② restate が polynomial-tail
finite-variance で true (defect 除去整合)、(iii) `_chain_domination` joint-wiring が vacuous-genuine
でない、(iv) `hpX_mom`/`pX_mom` が regularity field、(v) `@residual` classification。

実装後 `rg -n '@audit:|@residual|🟢ʰ' InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean`
+ `FisherConvBound.lean` で deprecated タグ / 語彙外 slug を列挙し報告。

---

## 判断ログ

決着済 entry (Phase 0 先行 / density-pin 外形等式 / underscore-args / §5A-5F structure 設計 / case A
案A の採否) は削除 (git 履歴 + コード SoT)。active な lesson + 撤退判断のみ残す。

9. **`density_t_eq` rnDeriv pin = false-statement defect、conv pin への差替で fix (Phase 5-F)**
   (2026-05-31): rnDeriv 代表元は `Classical.choose` で co-null 非可微 → `logDeriv(rnDeriv.toReal)=0`
   a.e. → Fisher=0 → RHS 0 固定 → Gaussian 真値 `1/(2(v+t))≠0` と矛盾 (V1 Fisher flaw の再導入)。
   **採用 = `density_t_eq` を conv pin `density_t = convDensityAdd pX g_t` に差替** (案1)。ripple
   localize (`density_t` field 残存で外向き API 不変)、`_fisher_match` を両辺 pointwise 一致で genuine
   closure、Gaussian constructor は `convDensityAdd_gaussian_closed_form` (`@audit:ok`) で新規 sorry 0。
   conv pin は smooth explicit 関数への外形等式で degenerate でなく load-bearing でない。
12. **`_chain` 解析核の真壁は Fisher integrability 1 本のみ (「真壁 0 件」評価を訂正)** (2026-05-31,
   proof-pivot-advisor): #2/#4 statement は general pX で true (Cauchy `pX~x⁻²` でも `(∂_x p)²/p~x⁻⁴`
   integrable、convolution が Fisher を減らす `J(X+√t·Z)≤1/t<∞`)。**ただし** この convolution Fisher
   bound (Stam) は Mathlib/repo 皆無 (loogle Found 0、repo は predicate pass-through)。`fisherInfoOfDensityReal`
   は発散時 0 を返すため値の well-definedness には有限性不要だが、IBP/logDeriv 経由で実数積分と等式接続する
   瞬間に integrability が load-bearing で復活 (値の定義可能性 ≠ 等式の証明可能性)。**採用**: Fisher
   integrability を共有 sorry 補題 `convDensityAdd_fisher_integrable` に切出し、#4 を genuine plumbing
   over named wall に。
15. **案A (finite-2nd-moment) は誤り → user fork で案B 採用** (2026-05-31, honesty-auditor):
   `gaussianPDFReal_le_prefactor` は `g_s(x-y) ≤ pref(s)` = **x について定数**に bound し exp 因子を捨てる
   → prefactor ルートは多項式 majorant しか出さず Gaussian-tail 結論を満たさない。反例 = polynomial-tail
   finite-variance `(2/π)/(1+y²)²` (全 hyp 充足、`∫y²pX=π/2<∞`、真の `∂²ₓp_s` は ~const/x² 減衰)。
   finite-2nd-moment は Cauchy を除外しても polynomial-tail が反例。正しい precondition は
   sub-Gaussian/finite-MGF (一般性大損)。fork = 案A′ (sub-Gaussian cheap) vs 案B (joint general PR 級)
   → user が **案B** 選択。**教訓**: lemma 結論形の verbatim 確認は数式論法にも必須 (CLAUDE.md「具体的
   数値・型予測の verbatim 確認」)。監査 checklist の反例セットに Cauchy + polynomial-tail finite-variance
   を追加。sorry 分割は honesty を上げるが分割先が false だと「genuine plumbing 化」ラベルが defect を隠蔽
   する逆効果になり得る。
16. **案B 採用確定 + 共有壁集約** (2026-05-31, lean-planner): 実装 brief = §Phase 5-G case B。GAP② を
   polynomial-moment restate、`_chain_domination` を joint-wiring、共有壁 `gaussianConv_fisher_le_inv_var`
   (新 file `FisherConvBound.lean`) を立てて consumer を gate。type-check done 到達可 (残 sorry は共有壁
   R-A core + GAP② STEP D bridge + joint envelope integrability の 3 箇所に局所化、すべて tier 2)。
17. **案B route I は案A defect 再来 (FALSE)、正路 = Tonelli+moment、Fisher 壁不要** (2026-05-31,
   proof-pivot-advisor mpmath 検算): route I (hessBound を Gaussian 形に取り
   `integrable_natPow_mul_exp_neg_mul_sq` で閉じる) は polynomial-tail pX で FALSE (hessBound は x について
   多項式減衰 ~const/x⁴、Gaussian 因子は heavy-tail pX が支配して消える)。**正路 = Tonelli で外積分
   (moment) 側に流す** (§Approach 2)。`_chain_domination` は moment route ゆえ `J(p_s)≤1/s` を経由せず
   Fisher 壁不要 → 共有壁 consumer は 2 件 (在庫訂正済)。finite-2nd-moment で genuine closable (隠れ壁なし)。
   **教訓**: convolution envelope の integrability は Tonelli で moment 側に流すのが正路、pointwise
   closed-form (`x^k·exp(-x²/c)`) を経由しない。設計の closure mechanism は実装前に proof-pivot-advisor で
   numerics 検算する (analytic 壁の標準手順)。

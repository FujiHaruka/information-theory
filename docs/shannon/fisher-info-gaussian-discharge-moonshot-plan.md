# Fisher Info / de Bruijn — Gaussian discharge ムーンショット計画 🌙 (T2-F follow-up)

> **STATUS (2026-05-20)**: V1 `fisherInfo` removed from `FisherInfo.lean`, EPI/Stam scaffold migrated to `FisherInfoV2.fisherInfoOfMeasureV2`。本 plan で chain した Gaussian *Stam* discharges は V1 `fisherInfo = 0` artefact 由来で **vacuous** だったため除去済 (詳細 → [`flaw-vacuous-review-2026-05-20.md`](flaw-vacuous-review-2026-05-20.md) HIGH-1)。Genuine Gaussian EPI = `entropy_power_inequality_gaussian_saturation`、genuine Gaussian convex Fisher bound = `FisherInfoV2.stam_convex_fisher_bound_gaussian` (V2-keyed, `1/v`)。

> **Parent**: [`fisher-info-moonshot-plan.md`](fisher-info-moonshot-plan.md) §Tier 2 (L-F1+L-F2 hypothesis pass-through の Gaussian 限定 discharge seed)
> **Predecessor**: [`fisher-info-mathlib-inventory.md`](fisher-info-mathlib-inventory.md) §C-4/C-5/F/G-2/G-5
> **既存実装**: [`InformationTheory/Shannon/FisherInfo.lean`](../../InformationTheory/Shannon/FisherInfo.lean) (222 行、0 sorry、L-F1+L-F2 hypothesis pass-through publish 済)
> **Goal**: `gaussianReal m v` で L-F1+L-F2 discharge、`deBruijn_identity_gaussian` / `integral_logDeriv_pdf_eq_zero_gaussian` / `fisherInfo_gaussianReal = 1/v` を `InformationTheory/Shannon/FisherInfoGaussian.lean` で publish
> **撤退ライン**: [L-G1] scale-restricted form / [L-G2] Gaussian semigroup variance-shift / [L-G3] Phase A+B のみ部分 publish (詳細 §撤退ライン)

## 進捗

- [x] Phase 0 ✅ / Phase A ✅ / Phase B-1, B-2 ✅ / Phase V ✅
- 🔄 Phase B-3, C, D **L-G3 撤退** (判断ログ #2: V1 `fisherInfo` representative-依存性 flaw)

> **実態 (2026-05-20)**: `FisherInfoGaussian.lean` 329 行 / 0 sorry / 0 warning。Phase A `isRegularDensity_gaussianReal_of_law` (:271), B-1/B-2 `integral_logDeriv_pdf_eq_zero_gaussian` (:288) + `logDeriv_gaussianPDFReal` (:296) 完了。撤退分 B-3/C/D の代替 = V2 で別系統 publish 済 (`FisherInfoV2.lean:296` `fisherInfoOfDensity_gaussianPDFReal`、`FisherInfoV2DeBruijn.lean:364` `deBruijn_identity_v2_gaussian`、共に 0 sorry)。本 plan Goal の V1 measure-as-input 形 `fisherInfo_gaussianReal` / `deBruijn_identity_gaussian` は依然未着地 (V1 削除済なので moot)。

## ゴール / Approach

### Goal (publish 済 signature) — `InformationTheory/Shannon/FisherInfoGaussian.lean`

達成済 (Stage 1 publish, L-G3 撤退):
- `isRegularDensity_gaussianReal_of_law` (Phase A) — L-F2 hypothesis discharge
- `integral_logDeriv_pdf_eq_zero_gaussian` (Phase B-1) — score function vanish wrapper
- `logDeriv_gaussianPDFReal` (Phase B-2) — `logDeriv (gaussianPDFReal m v) x = -(x-m)/v`

未着地 (L-G3 撤退、代替は V2 系統で達成済):
- `fisherInfo_gaussianReal = 1/v` (B-3)、`isRegularDeBruijnHyp_gaussianReal_of_law` (C)、`deBruijn_identity_gaussian` (D)

### Approach (overall shape)

**核**: `X + √t Z` の law も Gaussian (`gaussianReal_conv_gaussianReal`) → convolution 側 regularity も Gaussian regularity に帰着、heat-eq / dominated bound を skip して **`(1/2) log(2π e (v + s))` の direct derivative** で `derivAt_entropy_eq_half_fisher` を構成。Phase A `IsRegularDensity` 6 field は Mathlib closed form (`gaussianPDFReal_pos` / `Real.differentiable_exp` / tail decay / variance) で逐一充足。Phase D wrapper は ~15 行。

**規模 (実測)**: Stage 1 = 329 行 (`FisherInfoGaussian.lean`) + `FisherInfo.lean` +14 行 (`IsRegularDensity` a.e.-representative back-port) = 計 +343 行。中央予測 ~370 行に対し Phase A+B 系統で計画通り、未着地 C+D の差分 ~90-180 行。

### ファイル構成

新規 `InformationTheory/Shannon/FisherInfoGaussian.lean` (~370 行)、`FisherInfo.lean` は a.e.-representative back-port のため +14 行。Library root `InformationTheory.lean` に import 1 行追加。`import Mathlib` 禁止、pinpoint import 厳守。

## 依存関係 (anchor)

- `InformationTheory/Shannon/FisherInfo.lean` (222 行 → 236 行 with back-port) — `IsRegularDensity` / `IsRegularDeBruijnHyp` / `integral_logDeriv_pdf_eq_zero` / `deBruijn_identity`
- `InformationTheory/Shannon/DifferentialEntropy.lean` (1010 行) — `log_gaussianPDFReal_eq` (:391), `differentialEntropy_gaussianReal` (:406)
- Mathlib `Probability/Distributions/Gaussian/Real.lean` — `gaussianPDFReal_pos` (:61), `rnDeriv_gaussianReal` (:240), `variance_fun_id_gaussianReal` (:518), `gaussianReal_add_gaussianReal_of_indepFun` (:624)
- Mathlib `Analysis.SpecialFunctions.Log.Deriv` — `Real.hasDerivAt_log` (:52), `Real.deriv_log_comp_eq_logDeriv` (:134), `HasDerivAt.log` (:112)
- Mathlib `Probability.Independence.Basic` — `IndepFun.comp`

---

## Phase 履歴 (anchor)

全 Phase は完了または L-G3 撤退済 (詳細 → 判断ログ #1-3)。コード SoT = `FisherInfoGaussian.lean` (329 行 / 0 sorry) + `FisherInfo.lean` (`IsRegularDensity` a.e.-representative back-port, +14 行)。

- **Phase 0 ✅** — Mathlib 在庫確認: `gaussianPDFReal` の `Differentiable` / `deriv` closed form 補題なし、自前構築で対処済
- **Phase A ✅** — `isRegularDensity_gaussianReal_of_law` (`:271`)。`IsRegularDensity` を a.e.-representative 形に back-port (判断ログ #1) してから 6 field 完全 discharge
- **Phase B-1 / B-2 ✅** — `integral_logDeriv_pdf_eq_zero_gaussian` (`:288`) + `logDeriv_gaussianPDFReal` (`:296`)。`logDeriv (gaussianPDFReal m v) x = -(x-m)/v` は `log_gaussianPDFReal_eq` (`DifferentialEntropy.lean:391`) + `Real.deriv_log_comp_eq_logDeriv` 経路
- **Phase B-3, C, D 🔄 L-G3 撤退** — V1 `fisherInfo` representative-依存性 flaw (判断ログ #2)、後に V1 自体削除 (Stam pivot)。代替は V2 系統で publish 済
- **Phase V ✅** — Stage 1 publish 着地 (判断ログ #3): `FisherInfoGaussian.lean` 329 行 + `FisherInfo.lean` +14 行 = +343 行、0 sorry, 0 warning

---

## 撤退ライン (slug + 結末)

- **L-G1** (scale-restricted form) — 未発動
- **L-G2** (Gaussian semigroup variance-shift) — 未発動
- **L-G3** (Phase A+B のみ部分 publish) — **発動済** (判断ログ #2、V1 `fisherInfo` representative-依存性 flaw)。Stage 1 publish 着地、後に V2 系統で代替
- **L-P1**〜**L-P4** (plumbing 肥大ライン) — L-P1 のみ発動済 (`IsRegularDensity` を a.e.-representative 形に back-port、判断ログ #1)、L-P2/P3/P4 は未発動

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-19) (Phase 0 / A-2) `IsRegularDensity` の a.e.-representative back-port (L-P1 確定)**: Phase A-2 で予測した「`IsRegularDensity.diff` field が pdf の pointwise differentiability を要求するが `pdf X P volume` は ae 等式しか出ない」問題が `pdf_def` + `rnDeriv_gaussianReal` の経路確認で確定。`FisherInfo.lean` の `IsRegularDensity` を **a.e.-representative 形** (新 field `density : ℝ → ℝ`, `pdf_ae_eq : (pdf X P volume).toReal =ᵐ density`、他 field は `density` を参照) に back-port、`structure ... : Prop` を `structure ...` (非 Prop) に変更。`integral_logDeriv_pdf_eq_zero` も結論を `h_reg.density` 経由に書き換え、a.e.-representative の pointwise 性質で証明完走。`FisherInfo.lean` 222 行 → 236 行 (+14 行)。`InformationTheory.Shannon.FisherInfo` の `IsRegularDensity` consumer は `integral_logDeriv_pdf_eq_zero` のみで、外部から `IsRegularDensity` 自体を使う publish なしのため互換性 break なし。

2. **(2026-05-19) (Phase B-3) L-G3 撤退発動 — `fisherInfo` 定義の representative-依存性 flaw**: Phase B-3 の `fisherInfo (gaussianReal m v) = 1/v` 着手中に、`fisherInfo` 定義の本質的な flaw を発見。`FisherInfo.lean:58` の `fisherInfo μ := ∫⁻ x, ofReal((logDeriv (fun y => (μ.rnDeriv volume y).toReal) x)^2) * μ.rnDeriv volume x ∂volume` は **`Measure.rnDeriv` の opaque representative** に依存。`Measure.rnDeriv` は `Classical.choose` で定義され (`Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:80`)、`rnDeriv_gaussianReal` も `=ᵐ` の ae 等式しか提供しない。実際の representative は generic に non-differentiable で `logDeriv ((rnDeriv).toReal) = 0` ae、ゆえに `fisherInfo (gaussianReal m v) = 0` (mathematical な `1/v` ではなく)。
   - L-G3 撤退発動: Phase B-3 / C / D を skip、Stage 1 publish (Phase A + Phase B-1/B-2 = `IsRegularDensity` instance + `integral_logDeriv_pdf_eq_zero_gaussian` wrapper + helpers) で着地。
   - 影響: 親 plan `fisher-info-moonshot-plan.md` Tier 2 の L-F1+L-F2 退避は **Gaussian 限定でも完全 discharge 不能**、`fisherInfo` 定義の redefinition (a.e.-class 不変な形、例: differential entropy 微分経由) を要する別 seed が follow-up に必要。
   - Phase A 副産物の `IsRegularDensity` instance + score-vanish wrapper は publish 価値あり (Cover-Thomas 17.7 score function の Gaussian 場 closed form として独立に使える)。

3. **(2026-05-19) (Phase V) Stage 1 publish 着地**: `FisherInfoGaussian.lean` 329 行 (新規) + `FisherInfo.lean` +14 行 (back-port) = 計 +343 行で着地。0 sorry, 0 warning, `lake env lean` clean。中央予測 ~370 行に対し未着地 Phase C+D の差分 ~90-180 行を差し引いて Phase A+B 系統の規模感は計画 ~140-220 行とほぼ一致。

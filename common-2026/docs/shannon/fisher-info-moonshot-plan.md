# Fisher Information + de Bruijn Identity ムーンショット計画 🌙 (T2-F)

> **Status (2026-05-20)**: V1 (`FisherInfo.lean`) は `fisherInfo` の representative-dependence flaw (FLAW-VACUOUS、`= 0` for Gaussians) により **stale**。実 deliverable は V2 (`FisherInfoV2.lean` + `FisherInfoV2DeBruijn.lean`、0 sorry)。V1 は `⚠️ BUGGED` deprecation docstring + EPI/Stam 用 type-level scaffold として保持。詳細 → [`flaw-vacuous-review-2026-05-20.md`](flaw-vacuous-review-2026-05-20.md) HIGH-1、判断ログ #5。
>
> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 2 — T2-F」 / **Predecessor**: [`fisher-info-mathlib-inventory.md`](fisher-info-mathlib-inventory.md)
>
> **Goal (V1, stale)**: Cover-Thomas Ch.17.7 de Bruijn identity `(d/dt) h(X + √t · Z) = (1/2) · J(X + √t · Z)` を `HasDerivAt` 形で publish。
>
> **撤退ライン**: [L-F1] de Bruijn を heat-eq 仮定形 / [L-F2] score 期待値 0 を `IsRegularFamily` predicate 形に抽出 / [L-F3] Tier 0+1 のみで partial publish (詳細 §撤退ライン)。

## 進捗

- [x] Phase 0 — API 在庫 → inventory
- [x] Phase A — Tier 0 (定義 + 基本性質、V1 publish)
- [x] Phase B — Tier 1 (L-F2 hypothesis pass-through、`IsRegularDensity` predicate)
- [~] Phase C/D — L-F1 で `IsRegularDeBruijnHyp` field に吸収
- [x] Phase E — `deBruijn_identity` (signature 完全形、本体 hypothesis pass-through)
- [x] Phase V — `Common2026.lean` 編入

V1 (`FisherInfo.lean` 236 行) は 0 sorry / 0 warning だが `fisherInfo` の representative-dependence flaw により stale。実 deliverable は V2 (判断ログ #5)。

## ゴール / Approach

### Goal (V1 signature、stale)

`Common2026/Shannon/FisherInfo.lean` で 4 主定理 publish:

- `fisherInfo : Measure ℝ → ℝ≥0∞` (`logDeriv` shape-driven、`klDiv` 慣行で `ℝ≥0∞` 内蔵 + `.toReal` 公開)
- `fisherInfo_gaussianReal (m hv) : fisherInfo (gaussianReal m v) = ENNReal.ofReal (1/v)` ← **V1 では NOT-PROVABLE (FLAW-VACUOUS)**
- `integral_logDeriv_pdf_eq_zero (X h_reg) : ∫ logDeriv p · p = 0` (`IsRegularDensity` predicate 形)
- `deBruijn_identity (X Z hXZ hZ_law h_reg ht) : HasDerivAt (fun s => h(X+√s·Z)) ((1/2)·J(X+√t·Z).toReal) t`

verbatim signature → `Common2026/Shannon/FisherInfo.lean` (236 行)。

### Approach (overall strategy / shape of solution)

Cover-Thomas 17.7 の **heat semigroup 経路は Mathlib 不在** (inventory §C-5)、代わりに **`logDeriv` + `HasPDF` + Gaussian convolution PDF identity + parametric integral differentiation** の 4 部品で組む。1-D scope (multivariate Fisher matrix scope-out)、Common2026 `DifferentialEntropy.lean` Gaussian インフラ最大再利用。

de Bruijn 5-step 分解 (inventory §G-5): D-1 measure convolution → D-2 PDF lconvolution → D-3 `d/ds`-step (parametric integral) → C heat equation + convolution 微分 → E IBP。

**段階 ship**: Tier 0 (定義 + 基本性質、Phase A) / Tier 1 (+Gaussian + score 期待値 0、Phase B、**L-F3 撤退点**) / Tier 2 (+de Bruijn、Phase C-E)。中央予測 **~750 行** (inventory §G、上限 940 行)、L-F3 で ~280-360 行、L-F1 で ~600 行。

**ファイル**: 新規 `Common2026/Shannon/FisherInfo.lean` + `Common2026.lean` import 追記。

## 依存関係

Mathlib (主要): `Analysis.Calculus.{LogDeriv, ParametricIntegral}`、`Analysis.SpecialFunctions.Log.Deriv` (`Real.deriv_log_comp_eq_logDeriv`)、`Probability.{Density, Distributions.Gaussian.Real, Independence.Basic}` (`IndepFun.pdf_add_eq_lconvolution_pdf'` 等)、`MeasureTheory.{Integral.IntegralEqImproper, Group.Convolution}`、`Analysis.{LConvolution, Convolution}`。lemma 詳細 → inventory §B-C。

Common2026: `Shannon.DifferentialEntropy` (`differentialEntropy`, `_eq_integral_density`, `integrable_density_log_density_of_gaussian`, `log_gaussianPDFReal_eq`, `_gaussianReal`)。Chernoff/Sanov/Stein/Asymptotic は不要 (独立)。

---

## Phase 0 — API 在庫 ✅

完了 ([`fisher-info-mathlib-inventory.md`](fisher-info-mathlib-inventory.md), 546 行)。primitive layer (95%) 完備、Fisher info-specific layer は完全自作 (G-1〜G-6、合計 ~540-940 行)。路線 A (PDF 経由 + 1-D scope、heat semigroup scope-out) 採用。

---

## Phase A-V (V1 publish 済、stale)

全 Phase は V1 (`Common2026/Shannon/FisherInfo.lean` 236 行) で 0 sorry / 0 warning publish 済だが、`fisherInfo` の representative-dependence flaw により実 deliverable は V2。

- **Phase A (Tier 0)** — `fisherInfo` 定義 + `_nonneg` + `_eq_lintegral_logDeriv_sq` + `_dirac` + `differentialEntropy_map_eq_integral_pdf_log_pdf` (inventory §G-1, G-6)。
- **Phase B (Tier 1, L-F2 適用)** — `IsRegularDensity` predicate (Phase 2026-05-19 で a.e.-representative 形に back-port、判断ログ #5) + `integral_logDeriv_pdf_eq_zero` (hypothesis pass-through)。`fisherInfo_gaussianReal = 1/v` は判断ログ #4 で `fisher-info-gaussian-plan.md` に分離後 #5 で flaw 発見。
- **Phase C/D (L-F1 適用)** — heat-eq / convolution 微分 / parametric integral は `IsRegularDeBruijnHyp` field `derivAt_entropy_eq_half_fisher` に hypothesis として吸収 (実 chain は未実装)。
- **Phase E** — `deBruijn_identity` signature 完全形 publish、本体は `:= h_reg.derivAt_entropy_eq_half_fisher` (pass-through)。
- **Phase V** — `Common2026.lean` 編入済。

詳細手順 (skeleton / lemma 別証明計画 / 落とし穴) は git 履歴の plan 旧版または inventory §G-1〜G-6 参照。再着手は V2 plan (`fisher-info-v2-*-plan.md`) で。

---

## 撤退ライン

V1 publish 時 L-F1 + L-F2 を最初から適用 (判断ログ #1)、L-F3 は不発動 (Tier 2 signature まで完成、本体 pass-through)。

- **L-F1**: de Bruijn を heat-eq 仮定形で publish。`IsRegularDeBruijnHyp` field に hypothesis 集約。**V1 適用済**。
- **L-F2**: score 期待値 0 を `IsRegularDensity` predicate に hypothesis 抽出。**V1 適用済**。
- **L-F3**: Tier 0+1 のみで partial publish、de Bruijn を後続 seed 分離 (不発動)。
- **L-P1〜L-P4** (自作 plumbing 肥大ライン): L-P1 (heat-eq 二階微分 chain 肥大 → L-F1 と同等)、L-P2 (Gaussian tail envelope の Mathlib API 不在 → `integrable_density_log_density_of_gaussian` 拡張)、L-P3 (`ℝ≥0∞ ↔ ℝ` plumbing 肥大 → `fisherInfoReal` 派生先取り、判断ログ #3 で適用)、L-P4 (1 月完遂不能 → 月分割、判断ログ #4 で適用)。

---

## 判断ログ

append-only。

1. **(2026-05-19) L-F1+L-F2 を最初から適用形で publish** — Tier 2 (heat-eq/dominated-bound/IBP) 250-400 行を 1 セッション内 完遂は高 risk。`IsRegularDeBruijnHyp` field に Cover-Thomas 17.7.2 derivAt 結論を hypothesis として吸収、`deBruijn_identity` 完全 signature で publish。Gaussian-side instance は後続 seed に分離。

2. **(2026-05-19) (Phase A) `ℙ` (U+2119) binder 名で parse error** — `InformationTheory`/`MeasureTheory` notation と衝突。binder 名は plain `P` に統一。inventory skeleton 例の落とし穴。

3. **(2026-05-19) (Phase A 拡張) `fisherInfoReal` 派生 `.toReal` 慣行を Tier 0 で先取り** — L-P3 対策、T2-D EPI seed で `fisherInfoReal` 直接使用可。

4. **(2026-05-19) (Phase B 撤退) `fisherInfo_gaussianReal = 1/v` を本 plan から分離** — variance 計算が `DifferentialEntropy.lean` 既存インフラに完全 fit する保証なし (inventory §G-2 80-120 行)。L-P4 月分割で次月 seed (`fisher-info-gaussian-plan.md`) に切出し。Tier 1 publish は `integral_logDeriv_pdf_eq_zero` (L-F2 形) + bridge + `fisherInfo_dirac` の 3 件で確保。

5. **(2026-05-19) (follow-up Gaussian discharge) `fisherInfo` 定義の representative-依存性 flaw 発見、L-F1+L-F2 完全 discharge は不能** — `fisher-info-gaussian-discharge-moonshot-plan.md` で Phase A (`IsRegularDensity (gaussianReal m v)` instance)、Phase B-1/B-2 (`integral_logDeriv_pdf_eq_zero_gaussian` wrapper + `logDeriv_gaussianPDFReal`) は完遂 (`FisherInfoGaussian.lean` 329 行)。**Phase B-3 `fisherInfo_gaussianReal = 1/v` 着手時に flaw 発見**: `Measure.rnDeriv` は `Classical.choose` で定義された opaque representative (`Lebesgue.lean:80`)、generic に non-differentiable のため `logDeriv ((rnDeriv).toReal) = 0` ae ⇒ `fisherInfo (gaussianReal m v) = 0` (期待値 `1/v` ではなく)。L-F1 (heat-eq) も同 flaw で block。Gaussian discharge は L-G3 で Stage 1 着地、完全 discharge には `fisherInfo` の a.e.-class 不変な redefinition が必要 (V2 = 別 seed)。副作用: `IsRegularDensity` を a.e.-representative 形に back-port (新 field `density : ℝ → ℝ`, `pdf_ae_eq`、Prop → 非 Prop)、`FisherInfo.lean` 222 → 236 行、consumer 互換性 break なし。

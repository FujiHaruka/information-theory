import Common2026.Shannon.EPIConvDensity
import Common2026.Shannon.FisherInfoV2
import Common2026.Shannon.FisherInfoV2DeBruijn   -- V2 Gaussian 閉形 J(𝒩(0,s))=1/s
import Common2026.Shannon.StamGaussianBound       -- stam_fisher_arith

/-!
# Shared Mathlib wall — Stam convolution Fisher bound `J(pX ∗ g_s) ≤ 1/s`

EPI per-time de Bruijn line の shared 壁集約点 (`wall:fisher-finiteness`,
`docs/audit/audit-tags.md:70`)。Stam/Blachman の score-of-convolution monotonicity
`J(X + √s·Z) ≤ J(√s·Z) = J(𝒩(0,s)) = 1/s` を任意確率密度 `pX` (重い裾含む) で述べる。

## なぜ壁か (Mathlib gap, M0 verbatim)

- loogle: `"Fisher"` / `"Blachman"` → Found 0。Mathlib に Fisher 情報そのものが無く、
  convolution Fisher bound も皆無。
- repo の Stam 機械 (`EPIStam*`) は predicate pass-through のみ。genuine な density-level
  `J(X+Z) ≤ J(Z)` 補題は repo 不在。`stam_convex_fisher_bound_gaussian` は両被加数 Gaussian
  instance で一般 `pX` 不可。
- closure には self-written PR (density-level score-of-convolution 条件付き Cauchy-Schwarz,
  `stam-step2-density` 核) を要する → `wall:` 分類は正しい (closure plan
  `docs/shannon/fisher-finiteness-closure-plan.md` 判断ログ #1)。

## consumer (2 件、`FisherInfoV2DeBruijnAssembly.lean`)

`convDensityAdd_fisher_integrable` (Step 3 plumbing で有限上界を `< ⊤` に使う) と、
それ経由の `_chain_ibp_fisher` (de Bruijn IBP→Fisher の `fisher_from_logDeriv` hint)。
壁 1 件局所化により、closure 時に両 consumer が一斉 genuine 化する。

注: closure plan は「1壁3consumer」と記すが、`_chain_domination` は Fisher 壁を要さず
(Tonelli+moment で独立 closure、`epi-debruijn-pertime-closure-plan.md` 判断ログ #17)、
実 consumer は 2 件。
-/

namespace Common2026.Shannon.FisherInfoV2

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)

/-- **Shared Mathlib wall: Stam convolution Fisher bound** `J(pX ∗ g_s) ≤ 1/s`.
任意確率密度 pX (重い裾含む) で成立。EPI per-time line の 2 consumer を gate
(`convDensityAdd_fisher_integrable` / `_chain_ibp_fisher` via それ)。

Independent honesty audit (2026-05-31, fresh auditor, FisherConvBound 新規 shared wall):
verdict honest_residual. @residual(wall:fisher-finiteness) 維持。
- signature honesty: body は `sorry` のみ、結論 `J(p_s) ≤ 1/s` は仮説に bundle されていない。
  4 仮説 `hpX_nn`/`hpX_meas`/`hpX_int`/`hs` は全て pX regularity precondition (非負/可測/
  可積分/`0<s`)。`:= h` 循環なし、`:True` slot なし、`*Hypothesis` predicate 核 bundling なし、
  退化定義悪用なし。core-reconstruction test: 4 仮説を grant しても結論は手に入らない (load-bearing でない)。
- statement-truth: TRUE。Stam/Blachman convolution Fisher monotonicity
  `J(X+√s·Z) ≤ J(√s·Z) = J(𝒩(0,s)) = 1/s`、任意確率密度 pX で成立 (重い裾 Cauchy 含む、
  Gaussian smoothing で score `(∂p)²/p ~ x⁻⁴` 可積分)。退化 case `s=0` は `hs:0<s` で排除済。
  universally false ではない。
- classification `wall:fisher-finiteness` 正しい: loogle `"Fisher"`/`"Blachman"`/`"fisherInfo"`
  = Found 0 (Mathlib に Fisher 情報そのものが不在、convolution Fisher bound 皆無)。repo
  `StamGaussianBound.stam_convex_fisher_bound_gaussian` は両被加数 Gaussian instance
  (`gaussianReal m₁ v₁` + `gaussianReal m₂ v₂`) 限定で一般 pX に乗らない (verbatim 確認済) →
  closure には density-level score-of-convolution PR を要する genuine gap。register entry
  (audit-tags.md L70) 整合、`stam` (superadditivity = EPI 結論形) との semantic 区別も保持。
- shared 壁集約: `wall:fisher-finiteness` を持つ declaration は本壁 +
  `FisherInfoV2DeBruijnAssembly.convDensityAdd_fisher_integrable` の 2 件。後者は consumer で
  rewire 前 (= 同 slug 保持、次 wave で本壁 call に置換予定) = 移行途上、defect ではない。
- deprecated タグ残置: 本 file に `@audit:suspect`/`@audit:staged`/散文 `🟢ʰ` なし。
@residual(wall:fisher-finiteness) -/
theorem gaussianConv_fisher_le_inv_var
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {s : ℝ} (hs : 0 < s) :
    fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))
      ≤ ENNReal.ofReal (1 / s) := by
  sorry -- @residual(wall:fisher-finiteness)

end Common2026.Shannon.FisherInfoV2

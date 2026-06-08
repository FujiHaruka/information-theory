import InformationTheory.Shannon.FisherInfo.V2DeBruijnAssembly.Core
import InformationTheory.Shannon.FisherInfo.V2DeBruijnAssembly.Domination
import InformationTheory.Shannon.FisherInfo.V2DeBruijnAssembly.Derivatives
import InformationTheory.Shannon.FisherInfo.V2DeBruijnAssembly.Assembly

/-!
# per-time de Bruijn identity — Phase 5 capstone assembly

per-time de Bruijn identity を一般 `X` で genuine 化する
**Phase 5 assembly** (`epi-debruijn-pertime-closure-plan.md` §Phase 5 詳細設計 §5C)。

## import cycle 回避 (新 file 方式) — 解決済 (2026-06-01)

`FisherInfoV2DeBruijnPerTime.lean` (atom 供給元) は
`import InformationTheory.Shannon.FisherInfoV2DeBruijn` している (atom が wall file の
`gaussianConvolution` 等を使うため)。assembly は逆に atom を使うので、
`FisherInfoV2DeBruijn.lean` の本体に直接書くと **import 循環**。
→ 本 file (`FisherInfoV2DeBruijnAssembly.lean`) を atom file の下流に置き
(`import FisherInfoV2DeBruijnPerTime` 合法、循環なし)、ここで genuine theorem
`debruijnIdentityV2_holds_assembled` を証明する。

**シム削除 (2026-06-01)**: 旧 per-time shim `debruijnIdentityV2_holds`
(`FisherInfoV2DeBruijn.lean` の `sorry` body) は **削除済**。その 2 consumer
(`deBruijn_identity_v2`, `debruijnIntegrationIdentity_holds`) は本 assembly の下流の
新 file `FisherInfoV2DeBruijnGenuine.lean` に移設し、本 file の genuine sorryAx-free
`_assembled` に delegate するよう書換 (Strategy B — relocate consumers downstream)。
これで per-time de Bruijn の `sorry` はパイプラインから消えた。

## assembly 7 段 (plan §5C)

`debruijnIdentityV2_holds_assembled` body を 6 genuine atom で組む:

1. **density 同定** (`pPath_eq_convDensityAdd`、`h_reg.pX`/`pX_law` 等) +
   `density_t_eq` (rnDeriv pin) + `toReal_ofReal` で `density_t =ᵐ pPath t`。
2. **entropy = ∫ negMulLog pPath** (`differentialEntropy_eq_integral_density`)。
3. **parametric diff** (`entropy_hasDerivAt_via_parametric`)。
4. **heat eq** (`heatFlow_density_heat_equation`、∂_σ pPath = (1/2)∂²_x pPath)。
5. **IBP** (`debruijn_ibp_step`)。
6. **fisher congr** (`fisher_from_logDeriv`)。
7. **最終 congr** で RHS を `(1/2)*fisherInfoOfDensityReal h_reg.density_t` に一致。

## 残 regularity gap (named private lemma に factor out、honest sorry)

各 atom は genuine だが、atom を呼ぶための具体的 regularity discharge (Gaussian-tail
domination の `Integrable`、被積分関数 ae-measurability、`tsupport` 全域 C¹、chain-rule
plumbing) は PR 級 (plan §5C 表 L-PT-γ/δ + §5B-4)。これらは named private lemma に分離し
`sorry` + `@residual(plan:epi-debruijn-pertime-closure)` で残す (monolithic wall →
構造化 + 名前付き regularity gap)。**仮説束化・load-bearing 禁止** — gap lemma は全て
regularity precondition (被積分関数の微分・有界性・可測性) であって結論 (`HasDerivAt` /
heat eq) を bundle しない。
-/

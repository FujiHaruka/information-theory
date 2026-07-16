# Shannon-Hartley family — settled-facts ledger

> family `shannon-hartley` (operational continuous-time AWGN capacity, Phase 2/3 の `nyquist-2w-dof`
> 壁核) の確定事実の**単一の真実源**。フォーマット規約 → `CLAUDE.md`「Plan / docs hygiene」。
> 列 = claim / confidence / 再検証コマンド / last-verified (commit) / notes。
> confidence: `machine` (axiom/sorry 機械検証、再検証コマンド必須) / `loogle-neg` (Found 0、query 併記) /
> `numerical` (安定な数値検証、スクリプト再現コマンド必須、低〜中信頼) / `human-judgment` (解析的壁判断、低信頼、
> 独立 pivot で再確認)。プラン散文に settled fact をキャッシュせず、ここにリンクする (re-derive > cache)。

## WSEB (window sample-energy bound) の真偽 — 数値決着

BddAbove (`contAwgnMaxMessages_bddAbove`) は中心問題 verdict により **スカラー WSEB 不等式**
`E_s(f,n) = (T/n)∑_{i<n} f(iT/n)² ≤ C(T,W)·∫₀ᵀf²` に還元される (band-limited `[-W,W]` 連続 L² f、n 一様)。
その単標本 gateway atom `T·f(0)² ≤ C(T,W)·∫₀ᵀf²` の真偽が Phase 3 achievability の make-or-break だった
(plan では long-standing UNKNOWN、r8 で armchair 分析が TRUE⟷FALSE 複数回振れた)。**leg 9 で数値決着。**

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| **WSEB 単標本 atom は TRUE** (`sup_f \|f(0)\|²/∫₀ᵀf²` は**有限**、FALSE ではない) | numerical (2 独立法一致) | `python3 docs/shannon/wseb-numerical-probe.py` + `python3 docs/shannon/wseb-numerical-crosscheck.py` (numpy 要) | `(leg 9)` | **2 つの完全独立な離散化が高精度一致**。(A) sinc/prolate 還元 (W=1/2、Nyquist 格子): `f(0)=c_0`、`∫₀ᵀf²=cᵀGc` (G=sinc window Gram)、`sup=(G⁻¹)₀₀`。**SVD/最小二乗** (min window energy = L²([0,T]) 上で sinc_0 を他 sinc の張る空間へ射影した残差) で悪条件回避、N=16→128 + grid 細分で**収束**。(B) spectral 側 (変数=スペクトル `F` on `[-W,W]`、双対): 同 `sup=1/min(F*QF s.t. ∫F=1)`、K=41→321 で収束。**両者一致**: T=4→sup 76.1 (A) / 76.1 (B) ; T=8→62.4 / 62.3 ; T=16→57.5 / 57.5。min window energy が **0 から下限を持つ**ため sup 有限。境界 t=0 が最悪ケース (sup~68) だが有限、内点 (t=T/4,T/2) はより小 (sup 2–4)。**⟹ def-fix 案件 (FALSE 分岐) は排除。BddAbove は false-as-framed ではない** |
| WSEB の定数は W=1/2 で `sup~57–76` (T=4..16、緩やかに減少)、WSEB 形では `C(T,W) ~ T·sup` (T に依存、各 (T,W) で有限) | numerical | 同上 | `(leg 9)` | BddAbove 応用には `C` の (T,W)-依存で十分 (`E_s ≤ C·∫₀ᵀf² ≤ C·T·P`)。EXACT `⌊2WT⌋` は不要 (C3 循環回避と整合) |

## WSEB の self-build 可否 (Lean/Mathlib) — leg 9 gateway-atom-first probe = **GENUINE WALL 確定**

WSEB は TRUE だが、**Lean/Mathlib で self-build は genuine wall**（`lean-implementer` probe が machine-grounded で確定、
orchestrator 解析・既存 docstring と三重一致）。`contAwgnMaxMessages_bddAbove` の `sorry + @residual(wall:nyquist-2w-dof)`
は正しく分類されており維持。**(b) 壁の正面突破は失敗**（WSEB は真だが irreducible な prolate 理論を要す）。

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| WSEB self-build は genuine wall (Mathlib に必要な spectral/complex-analysis 理論が完全不在) | loogle-neg | 下記 loogle two-stage を再走 (`.lake/build/loogle.index`) | `(leg 9)` | 自家製見積 **~800–1500 行**の新規 spectral/complex-analysis 理論 (bridge 閾値 30–50 行を大幅超過 = plumbing でなく true gap) |

- **loogle two-stage (verbatim、implementer probe)**:
  - **name substring 全て Found 0**: `Prolate` / `Slepian` / `Logvinenko` / `Remez` / `Nikolskii` / `Nikolsky` /
    `reverseBernstein` / `bandlimited` / `Bandlimited` / `bandLimit` / `PaleyWiener` / `paleyWiener` /
    `concentration` / `reproducingKernel` / `ReproducingKernel` / `sampling` / `Sampling` / `exponentialType` /
    `ExponentialType`。**false friend** (非ゼロだが無関係): `"Bernstein"`=41 (全て Schröder-Bernstein +
    `bernsteinPolynomial.*` 近似論、harmonic-analysis の band-limited Bernstein は無)、`"Turan"`=37
    (全て graph theory `SimpleGraph.turanGraph`/`IsTuranMaximal`、`"Turán"`=0)。
  - **conclusion-shape 全て 0-match**: `|- |_| ≤ _ * ∫ _ in _, _` (0 match) / `|- _ ^ 2 ≤ _ * ∫ _ in _.._, _`
    (0 match) / `|- ‖_‖ ≤ _ * MeasureTheory.eLpNorm _ _ (MeasureTheory.Measure.restrict _ _)` (Found 0) /
    `MeasureTheory.eLpNorm _ _ (MeasureTheory.Measure.restrict _ _), Set.Icc` (Found 0)。
- **closest template**: 全直線 `bandlimited_sup_bound` (`ShannonHartleyOperational.lean:241`、`@audit:ok`)
  `|f t| ≤ √(2W)·(eLpNorm f 2 volume).toReal` — RHS が**全直線** `‖f‖_{L²(ℝ)}`、これを**窓に局所化**するのが WSEB。
  self-build は (i) `timeBandLimitingOp` の spectral 分解 + ≈2WT plunge 後の固有値減衰 (Leg A は self-adjoint/positive/‖A‖≤1
  のみで**スペクトル無し**)、または (ii) exponential-type 整関数の Nikolskii/Turán/Remez 不等式 のいずれか。
- **genuinely absent object**: PW_W 上で点評価 `f↦f(0)` が L²[0,T] 半ノルムで有界 ⟺ 境界 reproducing kernel
  `k₀(t)=2W·sinc(2Wt)` が `range(A^{1/2})` に属し `‖A^{-1/2}k₀‖<∞` (`A=P_W Q_{[0,T]} P_W`、`⟨Af,f⟩=∫₀ᵀ|f|²`)。
  **prolate-spheroidal / Landau-Pollak-Slepian の spectral fact** (固有値が ≈2WT plunge 後 →0、WSEB=`k₀` の係数が
  逆固有値に対し square-summable)。spectral 分解も固有値減衰も Turán/Remez/Logvinenko-Sereda 代替も Mathlib 不在。
- **routes 1/2 の失敗確認 (refutation-before-wall)**: (1) RK 分割 = 窓内項 OK だが leakage `∫_{outside} f·k₀` が
  窓外 f 無制約 + sinc `~1/t` tail で `f(0)` に還流 → 制御不能。(2) Sobolev trace 半分は Mathlib 到達可だが局所逆
  Bernstein `∫₀ᵀ(f')²≤C∫₀ᵀf²` が**偽** (窓外エネルギー由来の窓内 zero-crossing で `∫₀ᵀ(f')²/∫₀ᵀf²` 非有界)。
  verdict 方向 refutation: `bandlimited_sup_bound` 連鎖には `‖f‖²_{L²(ℝ)}≤C∫₀ᵀf²` (全直線≤C·窓) が要り、A の
  固有値→0 ゆえ偽。⟹ sup bound 単独では WSEB に届かない。

## ~~Mathlib の L² Fourier 変換はブラックボックス~~ → **REVOKED (2026-07-17、同 leg 内で反証)。`cause:loogle-blind` の教訓として保存**

**この節は 2026-07-17 に自分で書き、同じ leg の次の dispatch が反証した。** 欠落と宣言した「L¹∩L² 橋」は
**プロジェクト内に既に存在**していた: `ShannonHartley.l2FourierInv_eq_fourierIntegralInv`
(`ShannonHartleyOperational.lean:179`、sorryAx-free、既存 consumer 2)。一般 L¹∩L² 形そのもので、
しかも「閉じている」と記録した **`𝓢'` 迂回を実際に通っている**。Leaf 2 はこれを消費して ~125 行で閉じた
(d16a74e1、`timeBandLimitingOp_isCompact` = sorryAx-free)。

**失敗モード (再発防止の本体)**: 3 つの loogle-neg は**逐語的に真**だった (`Lp.fourierTransformₗᵢ` の
Mathlib 内 consumer は実際 0)。真だが**的外れ**だった — 検索範囲が Mathlib に限定され、**同じ family の
2 file 隣を誰も grep しなかった**。implementer と honesty-auditor の**独立 2 者が同じ穴に落ちた**
(独立性は共通の盲点を救わない)。台帳が「Mathlib に無い ⟹ 自前構築」と結論する形式そのものが罠。

**⟹ 標準手順**: 「Mathlib に無い」を欠落の根拠にする前に、**必ず in-project を先に grep する**
(`rg` + `scripts/dep_consumers.sh`)。壁宣言・self-build 見積の前提条件。行数見積が両者とも高かった
(~150-300 / ~350-600 vs 実測 ~125) のも、既に払い済みの橋を予算計上したため。

## コード側 SoT (壁の真実源はコードの `@residual`)

| decl | 状態 | notes |
|---|---|---|
| `contAwgnMaxMessages_bddAbove` (`ShannonHartleyAchievability.lean:481`) | `sorry + @residual(wall:nyquist-2w-dof)` | route (provable/wall) に関わらず honest sorry 維持。WSEB=TRUE でも **self-build が wall なら sorry 継続** |
| `contAwgn_eq_shannonHartley` (`ShannonHartleyOperational.lean:433`) | `sorry + @residual(wall:nyquist-2w-dof)` | Phase 4 main converse。tight ≈2WT カウント (prolate concentration) 経由、irreducible 壁 |
| `contAwgn_ge_shannonHartley` (`ShannonHartleyAchievability.lean:506`) | `sorry + @residual(plan:shannon-hartley-operational-moonshot-plan)` | leg 2 `BddAbove` を `le_csSup` で消費、transitive に wall-gated |

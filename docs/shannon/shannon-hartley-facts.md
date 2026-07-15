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
| **WSEB 単標本 atom は TRUE** (`sup_f \|f(0)\|²/∫₀ᵀf²` は**有限**、FALSE ではない) | numerical | `python3 docs/shannon/wseb-numerical-probe.py` (numpy 要) | `(leg 9)` | sinc/prolate 還元 (W=1/2、Nyquist 格子): `f(0)=c_0`、`∫₀ᵀf²=cᵀGc` (G=sinc window Gram)、`sup = (G⁻¹)₀₀`。**SVD/最小二乗** (min window energy = L²([0,T]) 上で sinc_0 を他 sinc の張る空間へ射影した残差) で悪条件を回避し、N=16→128 + grid 細分で**収束**: T=4→0.01313 (sup=76.1) / T=8→0.01604 (sup=62.4) / T=16→0.01738 (sup=57.5)。min window energy が **0 から下限を持つ**ため sup 有限。境界 t=0 が最悪ケース (sup~68) だが有限、内点 (t=T/4,T/2) はより小 (sup 2–4)。**⟹ def-fix 案件 (FALSE 分岐) は排除。BddAbove は false-as-framed ではない** |
| WSEB の定数は W=1/2 で `sup~57–76` (T=4..16、緩やかに減少)、WSEB 形では `C(T,W) ~ T·sup` (T に依存、各 (T,W) で有限) | numerical | 同上 | `(leg 9)` | BddAbove 応用には `C` の (T,W)-依存で十分 (`E_s ≤ C·∫₀ᵀf² ≤ C·T·P`)。EXACT `⌊2WT⌋` は不要 (C3 循環回避と整合) |

## WSEB の self-build 可否 (Lean/Mathlib) — leg 9 gateway-atom-first probe

WSEB は TRUE と確定したが、**Lean/Mathlib で self-build 可能か genuine wall かは別問**。
（この節は leg 9 の lean-implementer probe 結果で更新する。probe pending 中は下記の orchestrator 解析が暫定。）

- orchestrator 解析 (暫定、implementer probe で machine 確認予定): 2 ルートとも wall に底打ちの公算。
  1. **reproducing-kernel 分割** `f(0)=∫_ℝ f·k_0` (`k_0=2W·sincN(2W·)`)、`∫_ℝ=∫₀ᵀ+∫_{outside}`。窓内項は
     Cauchy-Schwarz で OK だが **leakage 項 `∫_{outside} f k_0`** が窓外 f 無制約ゆえ窓エネルギーで制御不能
     (= concentration/prolate 構造が要る)。
  2. **Sobolev-trace + 局所逆 Bernstein**: 端点 trace `f(0)²≤(1/T)∫₀ᵀf²+2‖f‖‖f'‖_{L²[0,T]}` は初等
     (Mathlib 可)。だが **局所逆 Bernstein `∫₀ᵀ(f')²≤C∫₀ᵀf²`** を要し、これは band-limited でも**局所版は偽**
     (大域 Bernstein `∫_ℝ(f')²≤(2πW)²∫_ℝf²` は真だが窓版は leakage で破綻)。⟹ route 死。
- Mathlib は band-limited sampling / Bernstein / Paley-Wiener / prolate / Slepian を **0 hit** (2026-07-14 確認)。
  全直線 `bandlimited_sup_bound` (`ShannonHartleyOperational.lean:241`) は**窓エネルギー制御を与えない**。

## コード側 SoT (壁の真実源はコードの `@residual`)

| decl | 状態 | notes |
|---|---|---|
| `contAwgnMaxMessages_bddAbove` (`ShannonHartleyAchievability.lean:481`) | `sorry + @residual(wall:nyquist-2w-dof)` | route (provable/wall) に関わらず honest sorry 維持。WSEB=TRUE でも **self-build が wall なら sorry 継続** |
| `contAwgn_eq_shannonHartley` (`ShannonHartleyOperational.lean:433`) | `sorry + @residual(wall:nyquist-2w-dof)` | Phase 4 main converse。tight ≈2WT カウント (prolate concentration) 経由、irreducible 壁 |
| `contAwgn_ge_shannonHartley` (`ShannonHartleyAchievability.lean:506`) | `sorry + @residual(plan:shannon-hartley-operational-moonshot-plan)` | leg 2 `BddAbove` を `le_csSup` で消費、transitive に wall-gated |

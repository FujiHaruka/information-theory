# Shannon-Hartley family — settled-facts ledger

> family `shannon-hartley` (operational continuous-time AWGN capacity, Phase 2/3 の `nyquist-2w-dof`
> 壁核) の確定事実の**単一の真実源**。フォーマット規約 → `CLAUDE.md`「Plan / docs hygiene」。
> 列 = claim / confidence / 再検証コマンド / last-verified (commit) / notes。
> confidence: `machine` (axiom/sorry 機械検証、再検証コマンド必須) / `loogle-neg` (Found 0、query 併記) /
> `numerical` (安定な数値検証、スクリプト再現コマンド必須、低〜中信頼) / `human-judgment` (解析的壁判断、低信頼、
> 独立 pivot で再確認)。プラン散文に settled fact をキャッシュせず、ここにリンクする (re-derive > cache)。

## §OBSERVATION-MAP — 欠陥は入力クラスでなく**観測写像**にある (leg 13, Leg 0 gateway)

Leg 0 (実装前 gateway) の verdict。**Proposal A (`encoder_power` を全直線エネルギーに def-fix) は FAIL**、
**Proposal O (点標本を正規直交テスト関数に差し替え) は PASS**。台帳の他節と違い、この節は**修正案の真偽**を固定する。

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| **Proposal A では `contAwgn_eq_shannonHartley` は依然 FALSE** (sub-Nyquist 漏れ、`s := P/(W·N₀) < 2` の全てで超過) | machine (**有理数の厳密算術に還元**、浮動小数点ゼロ) + 独立再導出 (`proof-pivot-advisor` が周波数領域から sinc 公式を一切使わず再導出、Gram 一致 1.6e-15) | `python3 docs/shannon/leg0-gateway-probe.py` (表 7) | leg 13 | `sampleCount` は**自由フィールド** (C4) ゆえ code は **Nyquist より粗く**標本できる。`Δ = m/(2W)` (整数 `m ≥ 2`、`n = 2WT/m`) で再生核 `K_{t_i}` は**直交** (`2W·sinc(m(i-j)) = 0`)、各 `‖K_t‖² = 2W` ⟹ min-norm 補間子は `‖f‖² = ‖x‖²/m` ⟹ 全直線予算 `‖f‖² ≤ TP` が `‖x‖² ≤ m·TP` を許す = **m 倍のエネルギーを同じ雑音で**。`sampledSignal` の `√(T/n)` は **`Δ = 1/(2W)` (m=1) でのみ等長**、`errorProbAt` の per-sample 分散は `Δ` に依らず `N₀/2` 固定。⟹ rate `= (W/m)·ln(1+m²s)` vs SH `= W·ln(1+s)`。**厳密証明は整数事実に落ちる**: 超過 ⟺ `(1+m²s) > (1+s)^m`、`m=2, s=1` で **`5 > 4`**。`sup_m (1/m)ln(1+m²s) ≈ 0.8·√s` (s→0) vs SH `≈ s` ⟹ **比は非有界** (s=0.001 で 25×)。`m` は `T` に非依存の自由整数、`limsup` は上極限点の sup ゆえ部分列 `T_k = n_k·m/(2W)` で生存 (`liminf` 定義だったら死んでいた)。`⨅_{ε∈(0,1)}` も生存 |
| **Proposal C (Landau-Pollak = 時間制限 + 帯域集中) も同じ欠陥を継承** ⟹ plan の指定退避先は**誤り** | machine (min-norm 補間子のエネルギー局在を直接測定) | 同上 | leg 13 | 反例の min-norm 補間子は**エネルギーの 99.76% が `[0,T]` 内** ⟹ 時間制限/集中の制約で死なない。**欠陥は入力クラスの軸にない** |
| **Proposal A は `contAwgnMaxMessages_bddAbove` は TRUE にする** (`eq` は FALSE のまま) | machine (`bandlimited_sup_bound` は `@audit:ok`、sorry-free) | `rg -n 'bandlimited_sup_bound' InformationTheory/Shannon/ShannonHartleyOperational.lean` | leg 13 | `\|f t\| ≤ √(2W)·‖f‖₂` ⟹ 標本エネルギー `E_s ≤ 2WT²P` が **n 一様** ⟹ `log M ≤ 2WT²P/N₀`。1 つの定理を直し、もう 1 つを直さない = **修正案の部分性のシグナル** |
| **Proposal O では `contAwgn_eq_shannonHartley` は TRUE** (gateway PASS) | numerical (収束テスト + 敵対的探索、下記) + human-judgment (Cauchy interlacing + Bessel) | `python3 docs/shannon/leg0-gateway-probe.py` (Leg 0' 節) | leg 13 | code が `φ : Fin k → (ℝ → ℝ)` を持ち、フィールドで「`φᵢ` は `[0,T]` に台を持つ」+「`∫ φᵢφⱼ = δᵢⱼ`」を課す。観測 `yᵢ = ∫ (encoder m)·φᵢ + zᵢ`、`zᵢ ~ N(0,N₀/2)` iid。**正規直交 ⟹ 白色雑音係数 `⟨ξ,φᵢ⟩` は厳密に iid** ⟹ `Measure.pi` が代用でなく**厳密**。教科書の Karhunen-Loève / 整合フィルタ離散化そのもの。`f ∈ PW_W` に対し `⟨f,φᵢ⟩ = ⟨f, P_W φᵢ⟩` ⟹ Gram `Gᵢⱼ = ⟨φᵢ, A φⱼ⟩` = **prolate 作用素 A の compression** (= `TimeBandLimiting.lean` の作用素) |
| Proposal O は C1/C3/C4 を全て保つ | human-judgment | — | leg 13 | C1 (符号語は関数) ✓ / C3 (どの def にも `2W` が現れない) ✓ / C4 (`k` は自由) ✓。**`2WT` カウントは prolate 固有値分布からのみ出現** ⟹ `wall:nyquist-2w-dof` は dormant のまま Leg E で復活 = plan の意図通り |
| Proposal O では `BddAbove` が **Bessel 単独で壁非依存に閉じる** | human-judgment (`Σᵢ⟨f,φᵢ⟩² ≤ ‖f‖² ≤ TP`、正規直交族の Bessel 不等式、k 一様) | — | leg 13 | 計画中の `bandlimited_sup_bound` 経由より単純。**循環警報は鳴らない**: crude 経路が閉じる rate は `≤ P/N₀` (広帯域極限) であって SH ではない (`ln(1+x) ≤ x` ゆえ `P/N₀ ≥ W ln(1+P/(WN₀))`) |

**Proposal O gateway の数値** (`C(T)/SH(T) → 1` が判定条件。プラトーが 1 超なら漏れ = FAIL):

| s | T=8 | 16 | 32 | 64 | 128 | 判定 |
|---|---|---|---|---|---|---|
| 10 | 1.0023 | 1.0011 | 1.0007 | 1.0004 | **1.0002** | → 1 ✓ (上から) |
| 1 | 0.9816 | 0.9898 | 0.9944 | 0.9969 | **0.9983** | → 1 ✓ (下から) |
| 0.1 | 0.9925 | 0.9961 | 0.9979 | 0.9989 | **0.9994** | → 1 ✓ (下から) |

`excess/T` が `T` 倍化ごとに約半減 = 超過は `O(log T)` (prolate cliff の遷移帯) ⟹ `limsup_T (·)/T` で消える。
**敵対的 φ 探索** (T=32, ランダム ONB 200 試行、k を 4–200 で振る): 最良 `C/SH = 0.3250`、prolate 最適
(`0.9944`) を破るものなし ⟹ **Cauchy interlacing が保持** ✓。`k ≫ 2WT` は飽和 (oversampling 漏れなし) /
`k ≪ 2WT` は厳密に劣る。Proposal A の「比が 1.77〜25 倍でプラトー」と**定性的に逆**。

**構造不変量 (数値プロトコルの assert、全て保持)**: `trace(ΔG) = 2WT` が全 `n` で厳密 / `m=1` が SH を厳密再現 /
`‖A‖ ≤ 1` (Leg A で証明済) / oversampling は SH に収束し漏れない / `s=2` の交叉が厳密有理数 TIE (`9 vs 9`)。

**leg 9 との決定的分離**: leg 9 は不良条件方向が発散を担い `lstsq(rcond=None)` がそれを捨てた (「収束は正則化子
についての証拠だった」)。本反証は**漏れ間隔での Gram が厳密に `2W·I`、条件数 1.000000**、`G⁻¹ = I/(2W)` が閉形式。
**load-bearing な議論に逆行列・正則化・固有分解が一切ない**。漏れは**最良条件**方向に乗る。

### §OBSERVATION-MAP の教訓 (leg 9 の教訓の一段深い版)

> **leg 9 は「どれくらい難しいか」を問い「そもそも真か」を落とした。Leg 0 は「そもそも真か」を問うたが、
> それを*入力クラス*にだけ問い、欠陥が*観測写像*にあることを危うく見落とすところだった。**

`encoder_power` (入力クラス) も Proposal C (入力クラス) も**軸が違う**。答えを決めているのは
`sampledSignal` + `errorProbAt` (観測写像) の側。plan の名指し攻撃 4 本は**全て入力クラス軸**であり、
攻撃 1 は oversampling (`n → ∞`) のみを名指していた — **実際の漏れは真逆の向き** (under-sampling) で、
どの名指し攻撃もカバーしていなかった。かつ oversampling は**実際には漏れない**ことが確認された。

**転用可能な tell**: **モデルがちょうど 1 つのパラメータ値でのみ較正されており (ここでは `m=1`)、
その値が定理の証明すべき当の量であるとき、そのモデルは定義でなく代用 (surrogate) である。**
`sampledSignal` は Nyquist 間隔でのみ等長 = Nyquist を仮定して Nyquist を証明する構図だった。

**修正案自身に gateway をかけよ (無限後退しない打ち切り)**: Proposal A を反証した同じ turn で、
私 (orchestrator) が提示した代替 (per-sample 分散を `(N₀/2)·2W·Δ` にスケール) は独立チェッカーに
**逆向き (oversampling) で非有界に漏れる**と反証された (`ν → 0` かつ信号部分空間は `≈2WT` 次元固定 ⟹
部分空間内の総雑音 `2WT·ν → 0`)。真の雑音共分散は `cov(sᵢ,sⱼ) = (N₀/2)·(ΔG)ᵢⱼ` で、**対角なのは
`2WΔ` が整数のときのみ** ⟹ `Measure.pi` (独立) で表せるのは Proposal O の正規直交フィールドを課したときだけ。
**打ち切り基準**: gateway は「新 def が代用でなく定義か」を問う 1 段のみ。Proposal O は `Measure.pi` を
**厳密**にする (代用でなくする) ので、この軸での後退は止まる。

## WSEB (window sample-energy bound) の真偽 — **解析決着 = FALSE** (leg 12、leg 9 の数値 TRUE を overturn)

BddAbove (`contAwgnMaxMessages_bddAbove`) は中心問題 verdict により **スカラー WSEB 不等式**
`E_s(f,n) = (T/n)∑_{i<n} f(iT/n)² ≤ C(T,W)·∫₀ᵀf²` に還元される (band-limited `[-W,W]` 連続 L² f、n 一様)。
その単標本 gateway atom `T·f(0)² ≤ C(T,W)·∫₀ᵀf²` の真偽が Phase 3 achievability の make-or-break だった。
leg 9 は数値 2 法で **TRUE** と決着させたが、**leg 12 が解析証明 + 任意精度再計算で FALSE と確定** (下記 §REVOKED)。

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| **WSEB 単標本 atom は FALSE** (`sup_f \|f(0)\|²/∫₀ᵀf² = +∞`) | human-judgment (解析証明、独立 `proof-pivot-advisor` が反証を試みて失敗) + numerical (任意精度が整合) | `python3 docs/shannon/wseb-highprec-probe.py` (mpmath 要) | `d2938749` (leg 12) | **6 行の解析証明**: 有界と仮定 → Hahn-Banach + Riesz で `g ∈ L²[0,T]`、`f(0)=∫₀ᵀ f g` (∀`f ∈ PW_W`、density 不要)。再生核 `h_a(t)=2W sinc(2W(t-a))` でテスト ⟹ `P_W(g·1_{[0,T]}) = k₀` ⟹ `û ≡ 1` on `[-W,W]` (`u := g·1_{[0,T]}`)。しかし `u` はコンパクト台 `L²` ⟹ `û` は整関数かつ `û ∈ L²(ℝ)` (Plancherel)、区間上 `≡1` ⟹ 一致の定理で `û ≡ 1` on `ℂ` ⟹ `û ∉ L²(ℝ)`。矛盾。**任意精度も整合**: 各精度が固有のプラトーを持ち、精度を上げると天井が上がる (dps=15→~54 / 30→~116 / 60→~280 / 120→~718 / 480→5680 @N=96、T=4)。内点 `a=T/2` でも同様 (旧「2–4」は dps=15/30 のプラトー)。**証明は任意の評価点で成立** (境界点に限らない) |
| **`contAwgnMaxMessages_bddAbove` / `contAwgn_eq_shannonHartley` / `contAwgn_ge_shannonHartley` は false-as-framed** (`P > 0` の全てで) | machine (反例構成 + junk chain の両補題を verbatim 確認) | `rg '@audit:defect\(false-statement\)' InformationTheory/Shannon/` | `d2938749` (leg 12) | 根本原因 = `ContAwgnCode.encoder_power` が**窓 `[0,T]` のエネルギーのみ**を拘束 (全直線拘束なし・時間制限なし)。WSEB=FALSE ⟹ ∀`A` ∃`f ∈ PW_W`: `∫₀ᵀf²=T·P` かつ `f(0)≥A`。`sampleCount:=1`、`encoder m := cₘ • f` (`cₘ = -1+2m/(M-1) ∈ [-1,1]`) で power 制約充足 (`cₘ²≤1`、band-limited/continuous/MemLp はスケール閉)、観測間隔 `2√T·A/(M-1) → ∞` ⟹ 任意の `M` が達成可能 ⟹ `¬BddAbove`。junk chain: `Nat.sSup_of_not_bddAbove` ⟹ `contAwgnMaxMessages=0` ⟹ `Real.log_zero` ⟹ 容量 `=0`、他方 `bandlimitedAwgnCapacity W N₀ P = W*log(1+P/(N₀*W)) > 0`。**⟹ 古典的な超指向性/超振動パラドックス。標準的定式化 (Wyner=全直線エネルギー / Landau-Pollak=時間制限+帯域集中) はいずれもこの class を使わない** |
| `wall:nyquist-2w-dof` は **live consumer ゼロ (dormant)** だが壁自体は実在 | machine | `rg 'nyquist-2w-dof' InformationTheory/` (3 hit = すべて散文、live residual なし) | `d2938749` (leg 12) | 上記 3 宣言は壁 consumer ではなく false-statement 欠陥だった。**def-fix 後の converse には prolate/LPS の `≈2WT` DOF カウントが依然必要**ゆえ slug は retire しない。2026-07-14 の loogle `Found 0` (`prolate`/`Slepian`/`Bandlimited`) は無効化されていない |

### §REVOKED (leg 9 の WSEB 数値 verdict) — 撤回理由

| 撤回された claim | 撤回理由 |
|---|---|
| ~~WSEB 単標本 atom は TRUE (`sup` 有限、2 独立法一致、T=4→76.1)~~ | **倍精度の切り詰めアーティファクト**。両スクリプトとも `np.linalg.lstsq(..., rcond=None)` = 機械 eps 未満の特異値を破棄。窓 sinc グラムの特異値は超指数的に減衰 (`λ_min` = 3.8e-10 / 1.9e-25 / 2.3e-44 @ N=4/8/12、T=4) ゆえ実効ランクが `≈2WT+O(log)` で頭打ち → N を増やしても追加モードが全て破棄され値が**凍結** → それを「収束」と誤読した。**記録された 76.1 はちょうど N=8 の値** (倍精度が凍結した点)。**「2 独立法」は独立でない**: 時間格子 vs 周波数格子は同一切り詰めの双対 = 共有盲点。**決定的反証**: 逆行列を一切通さない forward-evaluated witness (実関数を直接求積) が T=4 で比 **276.29** を達成 = 記録 sup を 3.6× 超過する明示的証拠。さらに dps=30 で `sup_N` が N=12→16 で 144.57→**114.92** と減少 = 部分空間単調性 (定理) の破れ = 数値破綻の**証明** |
| ~~WSEB 定数 `sup~57–76`、`C(T,W) ~ T·sup` 有限~~ | 同上 (有限値自体が存在しない) |
| ~~`BddAbove` は false-as-framed ではない / def-fix 案件は排除~~ | 完全に逆。上表の通り false-as-framed であり def-fix 案件そのもの |

## ~~WSEB の self-build 可否 — leg 9 probe = GENUINE WALL 確定~~ → **REVOKED (leg 12)。節全体が moot**

> **撤回 (leg 12, `d2938749`)**: WSEB は FALSE ゆえ「self-build できるか」という問い自体が消滅した (偽の命題に
> 自前構築すべき理論はない)。以下は **leg 9 当時の記録**として保存する。教訓 → §NUMERIC-TRUE-ARTIFACT。
> 三重一致 (implementer probe / orchestrator 解析 / 既存 docstring) は **3 つとも「真偽」でなく「難度」を問うていた**
> ため、全員が同じ軸で一致して外した。以下の "TRUE" は誤り。

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

**この節に状態を再キャッシュしない** — 3 宣言のタグは leg 12 で `wall:nyquist-2w-dof` から
`defect:false-statement` へ再分類済。ここに転記した表は一度 stale 化した (leg 13 で削除)。
現状は毎回 `rg '@residual' InformationTheory/Shannon/` で再導出せよ (CLAUDE.md「re-derive > cache」)。

## §ROUTE-FALSE — 「実在する Mathlib 補題を route に名指しする」は健全性を保証しない (2026-07-17, Leg C)

| claim | confidence | 再検証 | last-verified | notes |
|---|---|---|---|---|
| Leg C 列挙は `orthogonalComplement_iSup_eigenspaces_eq_bot` (`Spectrum.lean:443`) を要する | **REVOKED (machine)** | `rg 'orthogonalComplement_iSup' InformationTheory/` → 0 hit | 77a5fdf2 | plan/inventory が route として名指ししたが**一度も使わない**。列挙に要るのは「`c` 超の固有値有限」+「固有空間有限次元」のみ。固有基底の完全性は **Leg D/E の債務** |
| `_tendsto_zero` は Fredholm `antilipschitz_of_not_hasEigenvalue` machinery を要する | **REVOKED (machine)** | 同上 (`:54` / `:220` とも 0 hit) | 77a5fdf2 | 実際は atom + def から 8 行。`spectralRadius_eq_nnnorm` (`Rayleigh.lean:182`) も不使用 |
| Leg C の 4 無条件 headline はスペクトル内容を pin する | **REVOKED (machine)** | probe: `W<0`/`T<0` で `prolateEigenvalues ≡ 0` が実際の値 | 77a5fdf2 | 定数ゼロ列で全充足 = 空虚。gap 全体 = 1 atom `timeBandLimitingOp T W ≠ 0`（壁ではない、下流 ~35 行は machine 検証済） |

**⟹ 標準手順（壁プロトコルの対称版）**: 壁側は「**否定した asset は compiler で否定するまで否定にならない**」(§REVOKED)。
route 肯定側も同型で、「**名指しした route asset は、実際に使われたことを compiler で確認するまで route の裏付けにならない**」。
補題の**実在**を verbatim で確認しても、その補題に**至る手順の健全性**は一切保証されない — 実在確認が検証の外観だけを与える。
この inventory で **2 度目の同型失敗**（1 度目 = Leg B「simple function ⟹ finite rank」、実在資産を挙げつつ中間段が偽）。
事後照合の最安手段: closure 後に `rg '<named-route-asset>' InformationTheory/` を打ち、0 hit なら route 記述を訂正する。

## §SELF-REPORT-DRIFT — 自己申告は「機械が検査しない境界」で正確にドリフトする (2026-07-17, Leg C')

| claim | confidence | 再検証 | last-verified | notes |
|---|---|---|---|---|
| Leg C' 実装者が `timeLimitSubspace 0 = ⊥` / `bandLimitSubspace 0 = ⊥` を証明し tightness を machine 検証した | **FALSE (machine)** | `rg 'eq_bot' InformationTheory/Shannon/TimeBandLimiting.lean` | 569c48f0 | **その 2 補題は commit にもファイルにも project 全体にも存在しなかった**。監査が `rg` で捕捉。コードは主張していないので code defect ではないが、orchestrator が自己申告を転記して user に報告済だった（訂正済）。後に a7595371 で `_of_nonpos` 形として実際に landing |
| `prolateEigenvalues_hasEigenvalue` の `≠0` 仮説は「rank 超で entry `0` が固有値とは限らない」ため必要 | **FALSE (machine)** | `ker A ⊇ ker P_W = (bandLimitSubspace W)ᗮ ≠ ⊥` ⟹ `0` は常に固有値 | 569c48f0 | 仮説は**実は除去可能**。ただし除去は**空虚さを増やす**（`λ n = 0` かつ `0` が固有値なら結論自明）。残す理由は「必要」ではなく **content** |

**⟹ 標準手順**: 実装者の自己申告は、**機械が検査する項目**（`#print axioms`、compile、仮説の discharge）では正確だったが、
**何も検査しない項目**（「書いた」と主張する補題の実在、仮説が必要な *理由* の prose）でのみ不正確だった。ドリフトは
無作為ではなく**検証境界に沿って**起きる。⟹ 監査側は「claimed artifact を読んで done と受け取る」のではなく
**`rg` で再導出する**。orchestrator 側は「report の内容を user に転記する前に、機械が検査していない主張を切り分ける」。

## §NUMERIC-TRUE-ARTIFACT — 数値が「TRUE」と言うとき、それは正則化子についての証拠かもしれない (2026-07-17, leg 12)

**事件**: leg 9 が WSEB を「2 独立数値法が高精度一致 ⟹ TRUE」と決着させ、`wall:nyquist-2w-dof` を
`contAwgnMaxMessages_bddAbove` に貼り、3 leg 分の prolate 理論構築 (Legs B/C、~2000 行) がその上に積まれた。
leg 12 の **6 行の解析証明**が FALSE を確定 — 命題は偽、壁は最初から存在しなかった。

**なぜ全ての既存ガードをすり抜けたか**:

- CLAUDE.md のシミュレータ規則は **FALSE verdict 側にしか無い**（「小ケース sim で FALSE と判断する前に sim を実 def と
  照合せよ」）。**TRUE verdict 側に鏡像が無かった**。そして TRUE verdict は over-estimation（偽の命題への壁タグ =
  無限の作業を正当化する）を生むので、実は FALSE verdict より高くつく。
- 欠けていた検査は「sim vs Lean def の忠実性」では**ない**（sim は数学的に正しい量を計算していた）。欠けていたのは
  **sim vs 数値そのもの** = 条件数監査だった。
- **有限性 (`sup < ∞`) の問いは、正則化子が捨てる方向にこそ答えが住む**。`lstsq(rcond=None)` は機械 eps 未満の
  特異値を破棄し、窓 sinc グラムの特異値は超指数的に減衰する ⟹ 発散を担う超振動解が体系的に削除される。
  「収束」は**対象についてではなく正則化子についての証拠**だった。
- **「2 独立法の一致」は独立性の証拠にならない**（`cause:loogle-blind` と同型の共有盲点）。時間格子と周波数格子は
  同一切り詰めの双対。両スクリプトはヘッダで自らの健全性を宣伝していた（"robust to the prolate ill-conditioning" /
  "Computed stably via lstsq"）— 共有盲点が**強みとして文書化**されていたため相互チェックが機能しなかった。

**次回のためのプロトコル**（有限性 / 有界性の数値 verdict に限らず、任意の sim-backed verdict に適用）:

1. **どちらの向きの verdict でも sim の検証が要る**。TRUE 側の検証項目は「報告値が精度アーティファクトでないこと」。
2. **精度を振る**（`dps` を 2 倍ずつ）。プラトーが精度とともに動くなら、それは数学ではなく丸めを測っている。
   プラトーが動かないことを確認して初めて「収束」と言える。
3. **単調性など既知の構造不変量を assert する**。ここでは `sup_N` の N 単調性は**定理**で、dps=30 が
   144.57→114.92 と破っていた = 数値破綻の症状ではなく**証明**。1 行の assert で leg 9 に検出できた。
4. **forward-evaluated certificate を要求する**（逆行列 / 解 / 正則化を一切通さない経路で下界を作る）。
   ここでは実関数を直接求積して比 276.29 = 記録 sup 76.1 を 3.6× 超過 — これ単体で verdict を殺せた。
5. **解析証明を先に試す**。反証は 6 行だった。2 本の数値スクリプトを書く前に試すべきだった。
   armchair 分析が TRUE⟷FALSE に振れた (r8) ことは「数値に逃げよ」ではなく「もっと良い解析を探せ」の合図。

**メタ教訓 (§ROUTE-FALSE / §SELF-REPORT-DRIFT と同じ形)**: leg 9 は「self-build は何行か」を三者に問い、三者が
一致した。誰も「命題は真か」を問わなかった。**一致は、全員が同じ問いを間違えているとき最も説得力に見える。**
docstring は反証の機構（窓外に無限のエネルギーを置ける / sinc 尾が窓内標本に漏れ戻す）を**正しく記述した上で**
「ゆえに難しい」と結論していた — 正しい推論は「ゆえに非有界」。**「制御できない」は *難度* と読めてしまうが、
実際には *非有界性* を意味していた。**

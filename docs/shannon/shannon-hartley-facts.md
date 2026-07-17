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
| Proposal O は C1/C3/C4 を全て保つ | **machine (leg 14 で実装 + 独立監査が再導出。`rg` で「どの def / field にも `2W`/`⌊2WT⌋`/`⌈2WT⌉` なし」= 0 hit を確認、`bandlimited_sup_bound`/`synthSignal_bandlimited` の `2W` は**定理**ゆえ C3 対象外)** | `rg -n '2\s*\*\s*W\|⌈\|⌊' InformationTheory/Shannon/ShannonHartleyOperational.lean`（def / field 内 0 hit）+ `lake env lean` | **leg 14 (`4fd8a47c`)** | C1 (符号語は関数) ✓ / C3 (どの def にも `2W` が現れない) ✓ / C4 (`k` は自由) ✓。**`2WT` カウントは prolate 固有値分布からのみ出現** ⟹ `wall:nyquist-2w-dof` は dormant のまま Leg E で復活 = plan の意図通り |
| ~~⚠️ **`contAwgn_ge_shannonHartley` の Proposal A 下での真偽 = 未検証の開問**~~ → **MOOT (leg 14)**。Proposal A は破棄済で採用されたのは Proposal O。**Proposal O 下で `ge` は TRUE だが壁ブロック**（achievability = 利得 ≈1 の次元を ≈2WT 本構成 = 固有値カウントを**下から**読む ⟹ `wall:nyquist-2w-dof`）。実装・監査が独立に同結論、コード側タグも一致。**この行は根拠に使われなかった**（leg 14 で明示チェック済） | 未確定のまま棚上げ (Proposal A 自体が破棄ゆえ実務上不要) | — | leg 13 → moot at leg 14 | Leg 0 は `eq` (FALSE) と `bddAbove` (TRUE) の verdict を固定したが **`ge` は検査していない**。sub-Nyquist 漏れは容量を閉形式より**上**へ押すので `ge` は Proposal A 下でも生存しそうだが、**これは推論であって probe で確かめていない**。Proposal A は破棄済ゆえ実務上は moot だが、Leg P で `ge` の tag を触るときに**この行を根拠に使わないこと** — 要るなら probe を回して確定させよ。**検出経路**: 実装 subagent が「台帳が沈黙している」と自主申告した (自己申告が正しく効いた稀な例) |
| **修理後 `ContAwgnCode` は非退化に inhabited** ⟹ `bddAbove`/`ge` は空虚に真ではない | machine (leg 14 の**独立 2 監査**が別々に sorry-free 構成: Leg P 監査 = `probeRichCode`、Leg D' 監査 = `zeroCode` で `Nonempty (ContAwgnCode 1 1 1 2)`) | **⚠️ どちらの probe も未コミット** ⟹ `rg` で辿れない。要れば再構築（Leg D' 監査は実際にそうした） | leg 14 | `k=1` / `testFn = 𝟙_{[0,T]}/√T`（`∫φ² = 1` を証明）/ `encoder = synthSignal T 1 (fun _ => √P)` が `encoder_power` を**等号 `T·P`** で満たし、`P > 0` で `encoder 0 ≠ 0`。要 `1 ≤ 2WT`。**副産物**: `ContAwgnCode T W P 0` は `IsEmpty`（`decoder` が `Fin 0` へ写れない）— 無害（`sSup` の集合が `0` を含まないだけ）。**ファイルに実数版 `synthSignal_memLp` が無く**（複素版のみ）監査は `Complex.reCLM` 経由を強いられた = Leg D' も同じ穴に当たる |
| Proposal O では `BddAbove` が **Bessel 単独で壁非依存に閉じる** | human-judgment → **leg 14 の独立監査が再導出して裏付け** (`Σᵢ⟨f,φᵢ⟩² ≤ ‖f‖² ≤ TP` → 離散 converse `(k/2)log(1+2TP/(kN₀)) ≤ TP/N₀`、**k 一様・帯域入力を一切使わない**。Mathlib に `Orthonormal.sum_inner_products_le` / 在庫に `awgn_converse` = 配線のみ) ⟹ `plan:` は正当で壁ではない | — | leg 14 | **pin された不変量**: 修理後 `encoder_power` は**厳密に** `‖f‖²_{L²(ℝ)}` を pin し、これは Bessel の RHS と**同じ粒度**（粗くない）。旧欠陥は `∫₀ᵀf²` しか pin しないのに議論が全直線を要した点 ⟹ 反例**クラス**（超振動で窓外にエネルギーを退避）は根で閉じており、instance patch ではない | 計画中の `bandlimited_sup_bound` 経由より単純。**循環警報は鳴らない**: crude 経路が閉じる rate は `≤ P/N₀` (広帯域極限) であって SH ではない (`ln(1+x) ≤ x` ゆえ `P/N₀ ≥ W ln(1+P/(WN₀))`) |

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

**leg 14 の追加教訓 — 「正しい結論 + 破れた論拠」は監査でしか捕まらない**: Leg P の実装側は
`encoder_continuous` の除去を「クラスが広がる ⟹ converse が厳密に難しくなる ⟹ 救済ではない」と正当化した。
**結論は正しいが論拠は `ge` 方向で破れている**（クラスを広げると achievability は*易しく*なる = 逆向きに救済に
なりうる）。実際に成り立つ論拠は監査が出した**観測可能量の a.e. 不変性**（`observation` は Bochner 積分ゆえ
a.e. クラスにしか依存せず、他の全 field も a.e. 不変 ⟹ 代表元固定 field の除去は**両方向に inert**）。
`0 sorry` も `lake env lean` もこの差を検出しない。**片方向でしか成り立たない論拠で両方向の主張を通すのは、
「両方向 doctrine」の未適用そのもの**（Ch.10 RD と同じ軸）。同 leg で実装側の
「`IsBandlimited 0 W` は自明に真」という**未検証の否定的主張**も監査が機械で閉じた（結果は真だったが、
報告時点では未検証 = CLAUDE.md の名指しする失敗形）。

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

---

## §SPECTRAL-ASSETS — Mathlib の無限次元スペクトル資産は「有る」。壁論拠が誤っていた (2026-07-17, leg 15, Leg E atom)

`wall:nyquist-2w-dof` の旧論拠は「`≈2WT` DOF カウントには無限次元スペクトル理論が要るが Mathlib に無い」だった。
**後半が誤り**。grep で機械確認した実際の在庫:

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| Mathlib に trace-class / Schatten / Hilbert-Schmidt **作用素論は不在** | machine | `grep -n "FiniteDimensional" .lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/{Trace,SingularValues}.lean` → 両者とも有限次元前提 | `7c43417a` | `find Mathlib -iname "*Schatten*" -o -iname "*TraceClass*"` = 0 hit |
| Mathlib に**コンパクト自己共役の無限次元スペクトル定理は存在** | machine | `grep -n "orthogonalComplement_iSup_eigenspaces_eq_bot" .lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean` → `:443` | `7c43417a` | 「固有空間の iSup の直交補 = `⊥`」形。`:464` `finite_dimensional_eigenspace` は本 family が既に消費中 |
| crude trace bound `c·#{λ>c} ≤ 2WT` は**壁非依存**で closure 可能 | machine | `#print axioms InformationTheory.Shannon.TimeBandLimiting.prolateCount_mul_le` → sorryAx-free | `7c43417a` | Bessel + 既存 `bandLimitProj_apply_ae`。有限直交族しか要らず無限次元 trace 理論を経由しない |
| **厳密 trace 等式** `∑' i, ⟪A bᵢ, bᵢ⟫ = 2WT`（任意の `HilbertBasis b`）は closure 済 | machine | `#print axioms InformationTheory.Shannon.TimeBandLimiting.tsum_inner_timeBandLimitingOp_eq` → sorryAx-free + `lake env lean InformationTheory/Shannon/TimeBandLimiting.lean` | `21981fc8` | leg 15 (E-trace)。**Parseval は任意の完全基底で効くのでスペクトル定理すら不要だった** = 旧壁論拠の二重の誤り |
| ~~**tight LPS 集中は依然未証明**（本 slug の本体）。**残渣は第 2 モーメント `tr A − tr A²` に絞られた**~~ | ~~human-judgment~~ | — | `21981fc8` | **leg 16 で決着 → 下行**。leg 15 の判断自体は正しかった（残渣の同定は当たっていた）が、**その残渣が壁だという含意が誤り**だった |
| **第 2 モーメント `tr A − tr A² ≤ 2 + log(1+2WT)` は closure 済** = 本 slug の名指す残渣は消滅 | machine | `#print axioms InformationTheory.Shannon.TimeBandLimiting.tsum_inner_sub_norm_sq_timeBandLimitingOp_le` → sorryAx-free（**olean が stale だと phantom `unknown constant` が出る。先に `lake build InformationTheory.Shannon.TimeBandLimiting`**） | `00cb1c8b` | leg 16 (E-sharp)、監査 all OK。任意 `HilbertBasis`、仮説は regularity のみ。2 段: (a) `bandKernel_window_deficit_le` = 純 calculus（`k(u)=sin(2πWu)/(πu)` ゆえ `k²≤1/(π²u²)`）、(b) `tsum_norm_timeBandLimitingOp_sq_eq` = `tr A² = ∫₀ᵀ∫₀ᵀ|k|²`（Parseval テンプレの polarize、`A↔B` bridge も三重 Fubini も不要） |
| `P_W k_t = k_t`（再生核は自身が帯域制限）は in-tree・~35 行で導出可能 | machine | `#print axioms InformationTheory.Shannon.TimeBandLimiting.bandLimitProj_bandKernelLp` → sorryAx-free | `00cb1c8b` | leg 16 の scouting 回答。`bandKernel_eq_smul_shiftSinc` + `fourier_shiftSinc_toLp` → `𝓕(k_t) = 2W·specBoxcar`、`specBoxcar c Δ` は定義上 `Icc (-(1/(2Δ))) (1/(2Δ))` 上の指示関数 = `Δ=1/(2W)` で `Icc (-W) W`。**再利用可能** |
| Mathlib に `HasSum (fun i => ‖⟪x, b i⟫‖²) (‖x‖²)`（norm² 形の Parseval）は**無い**が、`lp.hasSum_norm` 経由の代替路が**ある** | machine | `grep -n "hasSum_inner_mul_inner\|hasSum_norm" .lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/l2Space.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean` | `00cb1c8b` | 監査が実装者の否定的主張を検証して**確認 + caveat 追加**: `l2Space.lean:457-469` は `hasSum_inner_mul_inner` 系のみ。だが `lpSpace.lean:468` `lp.hasSum_norm` + `HilbertBasis.repr` で同値に到達可（rpow/npow cast 除く）。どちらも ~12 行なので self-build (`hasSum_norm_inner_sq`) で可。**誠実性には無影響**（この主張に `@residual` も壁 verdict も乗っていない）が、本 family は「Mathlib に無い」主張で 3 度焼かれているので記録 |

**教訓 1 — `cause:weaker-relative`（CLAUDE.md「textbook-object strength diff」の実発火）**: 実装者は
gateway atom が通ったことから「`wall:nyquist-2w-dof` は genuine でない・`cause:single-route`」と結論した。
**閉じたのは弱い親戚**（crude trace bound）であって slug が名指す tight LPS ではない。
**弱い命題を閉じても、強い命題についての壁 verdict は覆らない。** 監査が逐語根拠（consumer が要する強度 =
`ShannonHartleyOperational.lean:461-462`「converse は上半分、achievability は下半分」）で訂正した。
**問いの立て方が誤っていた**: 実装者は「Bessel は `2WT` 上界に届くか」(yes) を問い、
「**Bessel が届く上界は、壁が名指す上界か**」(no) を問わなかった。

**教訓 1' — 同じ軸の逆向き発火。strength diff は壁の側にも適用せよ（leg 16, E-sharp）**:
教訓 1 は「**実装者**が弱い親戚を閉じて過大主張した」形だった。leg 16 で**同じ軸が逆向きに発火**した —
**壁の側**が、consumer の要求より**強い親戚**で枠付けされていた。`wall:nyquist-2w-dof` の残渣は
「Landau-Widom」= 鋭い漸近**等式** `tr A − tr A² ~ (1/π²)log(2WT)` として記述されていたが、
consumer が実際に要するのは**緩い片側上界** `tr A − tr A² ≤ C₁ + C₂·log(1+2WT)` のみだった。
差は決定的で、後者は `|sin| ≤ 1` と `∫1/u` だけで出る初等 calculus（前者は特殊関数論）。
**なぜ両半分が片側上界だけで出るか**（監査が独立再導出、これが判定の核）: `0 ≤ λ ≤ 1` と
`tr A = 2WT`（厳密値、E-trace）があれば、上半分は `#{λ>c} − ∑_{λ>c}λ = ∑_{λ>c}(1−λ) ≤ D/c`、
下半分は `∑_{λ≤c}λ ≤ D/(1−c)` ⟹ `2WT − D/(1−c) ≤ #{λ>c} ≤ 2WT + D/c`。
**鋭い定数も第 2 モーメントの下界も要らない。**
⟹ **運用ルール**: 残渣を**教科書の名前**（Landau-Widom / Fano / Sanov …）で記述したら、
その名前が指す標準対象の強度と、**consumer の docstring が要求する強度**を diff せよ。
CLAUDE.md「textbook-object strength diff」は *reframe 時* の規則として書かれているが、
**壁を継承する各 leg でも再適用すべき**（強度は名前に張り付いて leg 間を drift する）。
**メタ所見**: E-atom を正しく refute した規律と、E-sharp を正しく是認した規律は**同一**。
strength diff は「壁を守る道具」でも「壁を壊す道具」でもなく、**強度を測る道具**である。

**教訓 1'' — 指示対象なき名前は残渣の強度を drift させる（leg 16 監査の気づき）**:
`prolate_eigenvalue_count` は plan 散文 + 3 つの docstring（`ShannonHartleyOperational.lean:460` /
`ShannonHartleyAchievability.lean:698,708`）が資産であるかのように参照しているが、
**宣言として一度も書かれたことがない**。壁の headline に指示対象が無いまま 16 leg 推論してきた =
**残渣の強度が leg 間で気づかれず drift しうる条件そのもの**（実際 3 度 drift した）。
⟹ 壁を building する前に **headline を実不等式として書き下ろす**（`sorry` + `@residual` でよい）。
名前でなく型が SoT なら、強度の diff は grep でなく**コンパイラ**が担う。

**教訓 2 — 否定的主張はコンパイラに退けさせるまで退けたことにならない（3 度目の近接事例）**: 
「無限次元スペクトル理論が Mathlib に無い」は**誰も検証していない否定的主張**として壁論拠に居座っていた。
1 回の grep で反証された。`cause:loogle-blind` の親戚 — loogle は Mathlib しか見ないが、
**この事例は loogle すら引かれていなかった**。壁の**論拠**は壁の**結論**とは別に検証が要る:
結論（tight LPS は未証明）が正しいままでも、論拠が誤っていればコスト見積が丸ごと狂う。

**§SELF-REPORT-DRIFT の 3 度目の再現（同じ形）**: 実装者の申告のうち機械が検査した項目（sorryAx-free /
0 sorry / 署名）は**全部正確**で、機械が検査しなかった 3 項目（非空虚性 probe の存在 / tightness witness /
壁 verdict）が**すべてドリフト**した。うち唯一 `rg` でなく判断を要した壁 verdict が**最も遠くまでドリフト**した。
probe と witness は監査が自分で書いてコンパイルし直し、主張自体は CONFIRMED（結論は正しく、根拠が tree に無かった）。

**教訓 3 — drift パターンは法則ではない（leg 15 E-trace = 初の negative data point）**: §SELF-REPORT-DRIFT は
「判断を要する主張ほど遠くドリフトする」を 3 度観測してきたが、E-trace の実装者は**自分の結果に対して
第 2 の問い**（「Parseval が届く等式は、壁が名指す等式か」）**を自分で立て**、scope 主張・未検証行数見積の
フラグ立て・probe の tree への landing をすべて自発的に行った。独立監査は**反例クラスを自作して再導出**した上で
CONFIRM した。**差分は brief 側にある**: E-atom の brief は「壁か否かを判別せよ」と問い、E-trace の brief は
**先行 leg の失敗形を名指しして「同じ誤りを繰り返すな・自分の結果に第 2 の問いを立てよ」と明示**した。
⟹ drift は実装者の属性ではなく**問いの設計の関数**。brief に失敗形を逐語で埋め込むのは有効な介入。

**教訓 4 — `plan:<slug>` の slug は機械解決されない（leg 15 監査の発見）**: E-trace は retreat を
`@residual(plan:shannon-hartley-phase2-spectral)` とタグ付けしたが、実在する plan は
`...-phase2-spectral-plan.md`。**`rg "plan:shannon-hartley-phase2-spectral-plan"`（= plan 自身が実装者に
書けと指示している逐語文字列）はこの residual を取りこぼす** — コードタグが SoT であるのに、その grep が
答えられない。既存 slug は両規約が混在（`epi-wall-reattack-plan` vs `wz-binning-covering`）。
`plan:<slug>` を `docs/**/<slug>.md` に解決する linter 規則があれば沈黙の grep miss が WARN になる。

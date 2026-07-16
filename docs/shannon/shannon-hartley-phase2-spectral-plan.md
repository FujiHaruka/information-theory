# Shannon-Hartley Phase 2 — 時間帯域制限作用素のスペクトル理論 サブ計画 🌙

> **Parent**: [`shannon-hartley-operational-moonshot-plan.md`](shannon-hartley-operational-moonshot-plan.md) §Phase 2（prolate-DOF 壁核）
> **Inventory (SoT)**: [`shannon-hartley-phase2-spectral-inventory.md`](shannon-hartley-phase2-spectral-inventory.md)
> **関連**: [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md)（sinc/sampling = CLOSED、kernel 資産）/ [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)（`awgn_converse` = leg D の trace 境界を供給）

## 進捗

- [x] M0 在庫調査 ✅（`shannon-hartley-phase2-spectral-inventory.md`、3 GATING verdict 確定）
- [x] Leg A — 作用素 + subspace + 自己共役 + 正 + `‖A‖≤1` ✅（genuine、commit 4d848a53）
- [x] **Leg B — コンパクト性** `timeBandLimitingOp_isCompact` ✅ **PROOF-DONE（d16a74e1、file 内 0 sorry / 0 residual、headline sorryAx-free 機械確認済）**。4 leaf 全て genuine:
  - **Leaf 2** `bandLimitProj_apply_ae`（make-or-break 橋 = 抽象 `P_W` ↔ sinc 畳み込み）🔄 **唯一の残 sorry**（`@residual(plan:shannon-hartley-phase2-spectral-plan)`、slug は子 plan = 本ファイルが SoT）。署名は **`(W : ℝ) (hW : 0 ≤ W) (f : E)`** — 元の framing は `W<0` で **FALSE**（`sincN` 偶ゆえ提示 kernel は `|W|` low-pass の符号反転、一方 LHS は `bandLimitSubspace W = ⊥` で 0）。48e499e2 で修正・監査 PASS（98d4da6c）。**scope 不変**: 両 headline は `(T W : ℝ)` のまま（`W<0` 枝を genuine に閉じた）。
    - **(a) 完了 + 抽象半分 全部 genuine**（b77bae8c/dec34988/48e499e2、`@audit:ok`）: `starProjection_comap_linearIsometryEquiv`（~15 行、見積 40-80 より安い）/ `zeroOnLp_starProjection_apply_ae`（Leaf 1 を任意可測 `S` に一般化、Leaf 1 は署名・sorryAx-free 不変）/ `bandLimitProj_eq_fourier_conj` / `fourier_bandLimitProj_apply_ae`（= `𝓕(P_W f) =ᵐ 𝟙_[-W,W]·𝓕f`）。
    - **(b) ✅ 完了（d16a74e1、~125 行）**。`bandLimitSpec`(+`_eq_indicator`/`_memLp_one`/`_memLp_two`) / `bandLimitProj_coeFn_ae_eq_fourierInv` / `inner_two_mul_specBoxcar_apply` / `fourierInv_bandLimitSpec_eq`（boxcar に対する Plancherel）+ `NormalizedSinc.sincN_neg`。`W=0` は null-band として genuine 処理、`0<W` は `Δ=1/(2W)` の boxcar 経由。
    - **(b) の教訓 = `cause:loogle-blind`（family 標準手順に昇格）**。旧記述の 2 段（「`integral_exp_boxcar_eq_sincN` 経由の Lp² 畳み込み定理」route WRONG → 「真の blocker = L¹∩L² 橋、Mathlib 不在ゆえ self-build ~150-600 行」）のうち **後段が偽**だった: その橋は**プロジェクト内に既存**（`ShannonHartley.l2FourierInv_eq_fourierIntegralInv`、`ShannonHartleyOperational.lean:179`、一般 L¹∩L² 形・sorryAx-free・既存 consumer 2、しかも「閉じている」と記録した `𝓢'` 迂回を実際に通る）。loogle-neg 3 本は**逐語的に真だが的外れ**（検索範囲が Mathlib 限定、2 file 隣を grep せず）。implementer と auditor の**独立 2 者が同じ盲点**に落ちた。⟹ **「Mathlib に無い」を欠落の根拠にする前に必ず in-project を grep**（`rg` + `dep_consumers.sh`）。詳細 → `shannon-hartley-facts.md` §REVOKED。
  - **Leaf 3** `sincConvKernel_memLp`（kernel ∈ L²(ℝ²)）✅ genuine（679c954a / 6104d26b）。
  - **Leaf 4** `l2KernelOperator_isCompact`（generic L²-kernel⟹compact、存在形）✅ **genuine（e619b06c、~500 行、監査 PASS a04b1cec）**。HS bound `l2KernelApply_eLpNorm_le` + **閉部分加群 + π-λ 生成**（inventory の「simple function ⟹ finite rank」は**偽**だったので backtrack、`isCompactOperator_of_tendsto` は不要だった）。reusable。
- [x] Leg C — 固有値降順列挙 `prolateEigenvalues` ✅ **framework は genuine（de758f19、243 行、監査 PASS 77a5fdf2、14 decls ok / defect 0）**。**ただし spectral content は未達（下記 Leg C' が残債）**。
  - 実測 route（**plan/inventory の旧記述「構造的 spectral thm 経由」は偽 — 訂正済**）: 要ったのは **(i) atom `prolateEigenvalueSet_finite`（`c` 超の固有値は有限個 = 0 以外に集積しない、Mathlib 不在ゆえ self-build ~40 行、Cauchy-Schwarz + `IsCompact.tendsto_subseq`）+ (ii) `finite_dimensional_eigenspace`（`:463`）** の 2 つだけ。**`orthogonalComplement_iSup_eigenspaces_eq_bot`（`:443`、固有基底の完全性）は一度も使わない** — 完全性は **Leg D/E の債務**（trace / MI capture でスペクトル内容が入る所）であって Leg C のものではない。Fredholm `:220` / `antilipschitz_of_not_hasEigenvalue`（`:54`）も不使用（inventory の「`_tendsto_zero` は Fredholm machinery を要す」は**偽**、atom から 8 行）。
  - def 形 = **counting-function の一般逆**（`prolateCount c := finrank (⨆ μ ∈ eigenvalueSet c, eigenspace μ)`、`λ n := sInf {c | 0 < c ∧ prolateCount c ≤ n}`）。`Antitone` が集合包含で 3 行、Leg E の橋 `#{n | c < λ n} = prolateCount c` が re-shaping bridge 無しで statable。
  - **guard は `0 < c` 必須（`0 ≤ c` は degenerate）**: `c=0` では span が無限次元 → `finrank` が junk `0` → `0` が全 `n` の制約集合に入り `λ ≡ 0` に潰れる。5 定理すべてが自明に真かつ空虚になる = tier-5「degenerate 定義の悪用」。implementer が compiler で捕捉（orchestrator ブリーフの `0 ≤ c` 推奨が誤り）。
- [x] **Leg C' — 非空虚性** ✅ **CLOSED（a040a456、監査 PASS 569c48f0、8 decls ok / defect 0）**。`prolateEigenvalues_zero_pos : 0<T → 0<W → 0 < prolateEigenvalues T W 0` が sorryAx-free。ゼロ列排除を監査が独立に machine 再検証（`¬ ∃ T W, 0<T ∧ 0<W ∧ ∀ n, λ n = 0` が compile）。**Leg C framework は今や spectral content を運ぶ**。
  - 実測 route（**想定通り**）: 証人 `𝟙_[0,T]` → `𝓕(𝟙_[0,T])(0) = T > 0` + 連続性 → band `[-W,W]` は `0` の近傍。**forward 橋は in-project に既存**（`ShannonHartley.l2Fourier_eq_fourierIntegral`、`ShannonHartleyOperational.lean:122`、`@audit:ok`、cycle 無し）= また「in-project 先行 grep」が効いた。
  - 非自明だったのは `P_W g ≠ 0 ⟹ A ≠ 0` の橋（証人は**外側の `P_W` しか生き残らない**）: `⟪Ag,g⟫ = ‖Q_T P_W g‖²` → `Q_T P_W g = 0`、次に `‖P_W g‖² = ⟪Q_T g, P_W g⟫ = ⟪g, Q_T P_W g⟫ = 0`。証人の**時間制限性** `Q_T g = g` はここで消費される（監査がトレースし real content と確認）。
- [x] **境界補題 + 退化物語の統合** ✅ **CLOSED（a7595371、9 decls、0 sorry 維持）**。tightness が prose → **compiler-backed fact** に:
  `timeLimitSubspace_eq_bot_of_nonpos` / `bandLimitSubspace_eq_bot_of_nonpos`（旧 `_of_neg` を subsume、consumer 1 = `timeBandLimitingComp_isCompact` を更新、旧名は project 内 0 hit）/ `timeBandLimitingOp_eq_zero_of_{band,time}_nonpos` / `prolateEigenvalues_eq_zero_of_{op_eq_zero,band_nonpos,time_nonpos}`。
  **両仮説は tight**（時間軸 vs 帯域軸 × strict-negative vs boundary の 4 退化クラス）: `0 ≤ T` / `0 ≤ W` への緩和は**反証可能**（単に未証明ではない）。co-null route（`restrict_eq_self_of_ae_mem` → `Lp.eq_zero_iff_ae_eq_zero`）が `<0` と `=0` を一様に覆うため subsume はコスト 0 だった。
- [ ] **残債 — `∀ n, prolateEigenvalues T W n ≠ 0`（infinite rank、壁ではない、未着手）**。`λ 0` の atom より**厳密に大きい obligation**。`A` が無限 rank であることを要す。
  - ✅ **退化側は解決済**（a7595371 の副産物）: `prolateEigenvalues_eq_zero_of_*` は **全 `n`** で成立（零作用素は任意の正閾値を超える固有値を持たない）ので、この債務を攻める leg は **`0<T`, `0<W` の regime だけ**見ればよい。
  - ⚠️ **罠（採るな）**: 「`_hasEigenvalue` の `≠ 0` 仮説は除去可能（0 が固有値だから）」— **監査により実際に除去可能と確定**（`ker A ⊇ ker P_W ≠ ⊥` ゆえ `0` は常に固有値。Leg C' 実装者が書いた「rank を超えると固有値とは限らない」という理由は**偽**、569c48f0 で訂正済）。だが**除去してはいけない**: `λ n = 0` かつ `0` が固有値なら結論は自明成立 = 無条件形は pin する内容が**厳密に少ない**。仮説は「必要だから」ではなく **content のため**に残す。「仮説が消せる＝前進」に見えて後退する under-estimation 形。
- [ ] **WSEB**（achievability の勝ち筋）📋 **[`∑ψ_k(0)²/λ_k<∞` = 境界 reproducing kernel `k₀∈range(A^{1/2})`。Legs B/C 完了後に assess: constructible なら BddAbove `contAwgnMaxMessages_bddAbove` closure → Phase 3 achievability（LPS wall 無し）。second wall の可能性も要確認]**
- [ ] Leg E — tight concentration `prolate_eigenvalue_count`（LPS）📋 **[converse exact 定数用、genuine wall 公算大（研究フロンティア、loogle Found 0）]**

## ゴール / Approach

### Goal

親 §Phase 2 の壁核 `wall:nyquist-2w-dof` を self-build する。**2 消費点がこのセッションの検証で 2 本の独立サブ線に分裂した**:

1. **Phase 3 achievability leg 2** `contAwgnMaxMessages_bddAbove`（`ShannonHartleyAchievability.lean:481`、現状
   `sorry + @residual(wall:nyquist-2w-dof)`）⟸ **スカラー WSEB 不等式**（Leg W → Leg D、`awgn_converse` の trace 境界経由）。
   **作用素論を経由しない**。
2. **Phase 4 main converse** `contAwgn_le_shannonHartley` の tight 固有値カウント `prolate_eigenvalue_count`
   ⟸ **作用素スペクトル鎖**（Leg A ✅ → B → C → E、LPS concentration）。

**中心問題 verdict はこの分裂**（下記）: BddAbove は compactness / effective-rank で **届かない**（tail-eigenvalue /
trace gap）。BddAbove の唯一の壁核は WSEB スカラー不等式で、その真偽 / 壁性は probe 保留中。

### Approach（解の全体形 — 2 本の独立鎖）

**Chain 1（Phase 3 BddAbove、スカラー・新 critical path）**:

```
awgn_converse（Converse.lean:607、scalar trace 境界）
      │  標本 codeword を AwgnCode に載せ P' = E_s/n、log(1+x)≤x で RHS を E_s/N₀ に潰す（n 一様、固有値不要）
      ▼
BddAbove ⟸ WSEB: E_s(f,n) = (T/n)∑_{i<n} f(iT/n)² ≤ C(T,W)·∫₀ᵀ f²   ← Leg W（make-or-break、probe 保留中）
      │  + ~150–250 行の壁非依存 plumbing（ContAwgnCode→AwgnCode 配線 / errorProbAt 等式 / Fano / edge case）
      ▼
contAwgnMaxMessages_bddAbove（Phase 3 leg 2）= Leg D
```

**Chain 2（Phase 4 tight count、作用素・BddAbove から独立）**:

```
A = P_W Q_T P_W  ✅（self-adjoint, positive, ‖A‖≤1、commit 4d848a53）        ← Leg A（DONE）
      │  compact
      ▼  IsCompactOperator A                                                  ← Leg B（Phase-4 のみ）
      │  spectral thm → 降順固有値列 + #{k|λ_k>θ}<∞
      ▼  prolateEigenvalues + qualitative effective-rank                      ← Leg C（Phase-4 のみ）
      │  tight ≈2WT concentration（LPS）
      ▼  prolate_eigenvalue_count                                             ← Leg E（irreducible wall）
      ▼  contAwgn_le_shannonHartley（Phase 4 converse）
```

**なぜ Chain 2 が BddAbove（Chain 1）に届かないか — tail-eigenvalue / trace gap**（下記 中心問題で詳述）:
effective-rank の **カウント** `#{k|λ_k>θ}<∞` は **大きい固有値だけ** を抑える。MI は
`I ≤ (1/2)∑_k log(1+λ_k/N)`。小固有値 **tail** `∑_{λ_k≤θ} log(1+λ_k/N) ≈ (2/N)∑_{small}λ_k` は依然 ~n 項あり、
**trace** `∑_k λ_k` が有界でない限り発散する。**trace = E_s = WSEB**。つまり count は red herring で、
必要なのは trace = WSEB そのもの。それを `awgn_converse` が直接与える。

### route（次アクション）= **Option 1 選択済（user 指示: 全理論を自前構築して main theorem を genuine 証明）**

leg 9 で WSEB gateway 決着（TRUE + genuine wall）後、**user が PAUSE を override し「構築すべき理論は全部自前で構築、
誤魔化しなくメイン定理を証明」を指示**。→ prolate/LPS スペクトル理論を Lean で自前構築する build order を実行:

1. **Leg B — コンパクト性** `timeBandLimitingOp_isCompact`（`A=C†C`, `C=Q_T P_W` は HS、finite-rank 近似）。~500–900 行、
   NOT a wall。make-or-break = 抽象 `P_W` ↔ 具体 sinc convolution の橋。**[dispatch 済 `compact-legB`]**
2. ~~**Leg C — 固有値列挙**~~ ✅ **framework CLOSED（de758f19、243 行、監査 PASS）**。実測 route = atom「`c` 超の固有値有限」+ `finite_dimensional_eigenspace` のみ（**構造的 spectral thm は不使用** = 旧記述は偽）。→ **残債 Leg C'（非空虚性、1 atom `timeBandLimitingOp T W ≠ 0`、壁ではない）が次の一手**。
3. **WSEB**（achievability の勝ち筋）: `∑ψ_k(0)²/λ_k<∞`（境界 reproducing kernel `k₀∈range(A^{1/2})`）。**constructible
   なら achievability は LPS wall 無しで閉じる**（要 assess: 列挙 + soft 減衰で summability が出るか / second wall か）。
   → BddAbove closure → Phase 3 achievability。
4. **Leg E — tight count** `prolate_eigenvalue_count`（LPS ≈2WT）。converse の exact 定数に必須、**genuine wall 公算大**
   （研究フロンティア）。全 foundation を積んで正面確認、詰めば honest sorry + 報告。
5. **組立** — converse + achievability → main theorem `contAwgn_eq_shannonHartley`。

**見通し**: achievability chain（1→2→3）は constructible 公算、converse exact 定数は LPS（4）依存で wall 公算大。
各 leg で genuine 進捗を commit、wall は honest sorry + 報告し constructible を最大化。**Legs B/C は Phase 3/4 両方の
foundation ゆえ「Phase-4 専用」ではなくなった**（WSEB も列挙を要すため）。

---

## 中心問題 verdict — BddAbove はスカラー WSEB に還元される（作用素コンパクト性でない）

**タスク指定の決定的問い**。旧 verdict「BddAbove は定性コンパクト性 + effective-rank で閉じ tight LPS 不要」は
**HALF-RIGHT**（tight LPS 不要は正しい）だが **route が WRONG**（compactness / count は届かない — tail-eigenvalue /
trace gap）。新 verdict で置換する。

### verdict（証拠付き）

**BddAbove（leg 2）は `awgn_converse` の trace 境界経由で単一 SCALAR 標本エネルギー不等式（WSEB）に還元される。
Legs B/C/E（作用素スペクトル理論）は BddAbove critical path から外れ、Phase-4 tight-count 専用。**

### 決定的理由（reduction を trace、全て本セッション verbatim 確認済）

1. **`awgn_converse`**（`InformationTheory/Shannon/AWGN/Converse.lean:607`、`@[entry_point]`）が scalar 境界を供給:
   `log M ≤ n·(1/2)·log(1 + P/N) + binEntropy(Pe) + Pe·log(M-1)`、`AwgnCode.power_constraint : ∑ᵢ xᵢ² ≤ n·P`
   （`AWGN/Basic.lean:95`）に keyed。`N = N₀/2`。
2. **標本 ContAwgnCode codeword を載せる**: `∑ᵢ (sampledSignalᵢ)² = (T/n)∑ᵢ f(iT/n)² =: E_s`
   （verbatim: `sampledSignal f T n i = √(T/n)·f(iT/n)`、`Operational.lean:364`）。よって per-sample power
   `P' = E_s/n`。`log(1+x)≤x` で RHS を `n·(1/2)·(E_s/n)/(N₀/2) = E_s/N₀` に潰す — **n 一様、固有値なし**。
3. **BddAbove ⟸ WSEB**: `E_s(f,n) = (T/n)∑_{i<n} f(iT/n)² ≤ C(T,W)·∫₀ᵀ f²`（band-limited `[-W,W]` 連続 L² f、
   n 一様）。加えて **~150–250 行の壁非依存 plumbing**（`ContAwgnCode→AwgnCode` 配線 / `errorProbAt` 等式 /
   Fano 再配置（`ε<1` 使用）/ edge case `n=0` / `M<2`）。

### なぜ compactness route（Legs B/C/E）が BddAbove に届かないか — genuine GAP

effective-rank の **カウント** `#{k|λ_k>θ}<∞` は **大きい固有値のみ** を抑える。MI は
`I ≤ (1/2)∑_k log(1+λ_k/N)`。小固有値 **tail** `∑_{λ_k≤θ} log(1+λ_k/N) ≈ (2/N)∑_{small}λ_k` は依然 ~n 項あり、
**trace** `∑_k λ_k` が有界でなければ発散する。**trace = E_s = WSEB**。したがって count は red herring で、
必要なのは trace = WSEB そのもの — それを `awgn_converse` が直接与える。連続コンパクト作用素
`A = P_W Q_T P_W`（L²(ℝ) 上）は連続的な事実だが、BddAbove の障害は **離散標本境界** で、作用素がそこに届くのは
（mis-specified な）gateway frame bound 経由だけ。

### WSEB 自体の status は RESOLVED（leg 9 probe で trichotomy 決着 = **TRUE + genuine wall**）

3 択（trichotomy）は leg 9 gateway-atom probe で決着（詳細 settled-facts → `shannon-hartley-facts.md`）:

- ~~**WSEB は FALSE**~~（def-fix）→ **排除**。単標本 atom `T·f(0)²≤C∫₀ᵀf²` を **2 独立数値法**（sinc/prolate 側
  SVD 最小二乗 + Fourier スペクトル側双対）で検証、`sup|f(0)|²/∫₀ᵀf²` は**有限に収束**（T=8 で ~62、境界 t=0 が最悪
  だが有限、n=1 が標本数最悪）。BddAbove は **false-as-framed ではない**。
- ~~**WSEB は provable（~200 行、作用素論不要）**~~ → **排除**。`lean-implementer` probe が machine-grounded で
  **GENUINE WALL** 確定（loogle two-stage 全 0-hit / conclusion-shape 0-match、routes 1/2 とも失敗）。
- ✅ **WSEB は TRUE だが self-build は GENUINE WALL**（~800–1500 行 prolate/LPS spectral 理論、Mathlib 完全不在）。
  存在するのは **全直線** `bandlimited_sup_bound` のみ = 窓エネルギー制御を与えない。核心的不在物 = 境界 reproducing
  kernel `k₀` が `range(A^{1/2})` に属す（prolate-spheroidal / LPS の spectral fact）。

**⟹ (b) 壁の正面突破は失敗**。WSEB は真だが irreducible な prolate 理論を要し、`contAwgnMaxMessages_bddAbove` は
`sorry + @residual(wall:nyquist-2w-dof)` を維持（正しく分類、コード SoT 不変）。**次の一手は user-decision**（下記
「撤退 / 次アクション」）。

### honest hedge + gateway atom + 撤退

- **コード側 SoT は変えない**: `contAwgnMaxMessages_bddAbove` は `sorry + @residual(wall:nyquist-2w-dof)` のまま
  — leg 9 probe で WSEB=TRUE+wall と決着後も honest（wall 確定ゆえ sorry 継続が正しい）。settled-facts は
  `shannon-hartley-facts.md`（プランに「壁である/ない」をキャッシュせずリンク）。
- **gateway atom（旧 frame bound を置換）**: 決定的 atom は WSEB スカラー不等式の単標本 case
  `T·f(0)² ≤ C·∫₀ᵀf²`。two-directional: (prove) band-limited f への restricted RKHS/Bernstein 境界、
  (refute) 小窓エネルギーで `f(0)` 大な band-limited f を sinc-tail 漏れで構成。旧 gateway `‖A_n‖≤1`（frame bound）は
  **mis-specified**（下記 判断ログ #3）。
- **UNDERSAMPLING 領域（n<2WT）が WORST case**: `E_s/∫₀ᵀf²` の sup は **小 n** で最大化され、`n=1` で `≈2WT`。
  旧 plan の oversampling 懸念は反転する。
- **撤退**: WSEB が壁 → honest `sorry + @residual(wall:nyquist-2w-dof)`（既 in place、`:484`）。WSEB が false →
  def-fix に escalate。**BddAbove を `≥` 定理へ hyp 化 / `ContAwgnCode` へ全直線エネルギー field 追加は禁止**
  （load-bearing tier-5、壁の偽装、下記 誠実性制約）。

---

## Leg A — 作用素 + subspace + 自己共役 + 正 + `‖A‖≤1` ✅ DONE（commit 4d848a53）

genuine 着地済。`E := Lp ℂ 2 (volume)` 上に `A := P_W ∘L Q_T ∘L P_W`（`Q_T`/`P_W` = 閉部分空間への
`starProjection`）を建て、`timeBandLimitingOp_isSelfAdjoint` / `_isPositive` / `_norm_le_one` を genuine 証明。
**この作用素 object は Phase-4 スペクトル鎖（Legs B/C/E）専用**で、Phase-3 BddAbove path からは外れた
（中心問題 verdict: BddAbove はスカラー WSEB 経由で、作用素を経由しない）。新 file
`InformationTheory/Shannon/TimeBandLimiting.lean`（`InformationTheory.lean` に import 登録済）。

---

## Leg W — WSEB スカラー標本エネルギー不等式 📋 **[NEW make-or-break・probe 保留中]**

**目的**: band-limited 連続 L² 信号の in-window 標本エネルギーを窓エネルギーで n 一様に抑える単一スカラー不等式。
**BddAbove（Leg D）の唯一の壁核**。proof-log: yes。

**signature スケッチ**:

```lean
theorem wseb (T W : ℝ) (hT : 0 < T) (hW : 0 < W) (f : ℝ → ℝ)
    (hf_bl : IsBandlimited W f) (hf_L2 : MemLp f 2 volume) (hf_cont : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      (T / n) * ∑ i : Fin n, f ((i : ℝ) * (T / n)) ^ 2
        ≤ C * ∫ t in Set.Icc (0 : ℝ) T, f t ^ 2
  -- C = C(T,W)（n に依らない）
```

**probe（次アクション、gateway-atom-first）**: 単標本 `n=1` case `T·f(0)² ≤ C·∫₀ᵀf²` を two-directional で settle。
- **prove 方向**: band-limited f に対する reproducing-kernel / Bernstein 型点値境界（窓エネルギー版）。~200 行見込み。
- **refute 方向**: 小窓エネルギー `∫₀ᵀf²` で `f(0)` を大きくできる band-limited f を sinc-tail 漏れで構成
  （全ての標本点 `iT/n` は `[0,T)` 内部 = out-of-window sampling ではない。gap は quadrature/aliasing +
  reproducing-kernel coupling）。

**feasibility**: **UNKNOWN（probe 保留中）**。Mathlib は band-limited sampling / Bernstein / Paley-Wiener を 0 hit
（`prolate`/`Slepian`/`Mercer` も 0、2026-07-14 確認）。全直線 `bandlimited_sup_bound`（`Operational.lean:241`）は
窓エネルギー制御を与えない。
**retreat line**: WSEB が壁と判明 → Leg D は transitively `sorry + @residual(wall:nyquist-2w-dof)`（既 in place）。
WSEB が false → **`ContAwgnCode` / 容量 def の def-fix に escalate**（`≥` 定理への hyp 化・全直線エネルギー
field 追加は禁止 = 壁偽装 tier-5）。
**循環チェック**: `wseb` の統計に `2W`/`⌊2WT⌋` は入らない（`W` は物理帯域幅 = 入力、C3 ✓）。
**def body 不可 sorry**: `wseb` は theorem（proof body に sorry 可、tier-2 撤退口）。

---

## Leg D — `contAwgnMaxMessages_bddAbove` closure（Phase 3 leg 2）📋 **[Leg W に gated]**

**目的**: 既存 sorry `contAwgnMaxMessages_bddAbove`（`ShannonHartleyAchievability.lean:481`、現
`@residual(wall:nyquist-2w-dof)`）を **Leg W（WSEB）経由で** genuine 化。中心問題 verdict の実装 = スカラー
WSEB reduction。**Legs B/C（作用素論）に gated ではない — reduction はスカラー**。proof-log: yes。
**概算 150–250 行の壁非依存 plumbing（WSEB に gated）**。

**target signature**（既存、変更なし = signature ripple 無し）:

```lean
theorem contAwgnMaxMessages_bddAbove (T W N₀ P ε : ℝ)
    (hT : 0 < T) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) (hε0 : 0 < ε) (hε1 : ε < 1) :
    BddAbove { M : ℕ | ∃ c : ContAwgnCode T W P M, (c.averageError N₀).toReal ≤ ε }
```

**構成（中心問題 verdict step 1–3 の実装）**:
- **`ContAwgnCode → AwgnCode` 配線**: 標本 codeword から per-sample power `P' = E_s/n` の `AwgnCode M n P'` を構成。
  `power_constraint : ∑ᵢ (sampledSignalᵢ)² ≤ n·P'` は構成から成立。
- **`errorProbAt` 等式**: `ContAwgnCode.errorProbAt`（`Operational.lean:373`、`Measure.pi` の per-sample AWGN）=
  `AwgnCode` 側の離散 `errorProbAt`（`sampledSignal = cᵢ` で一致、親 Phase 3 で verbatim 確認済）。
- **`awgn_converse` + `log(1+x)≤x`**: RHS を `E_s/N₀ + Fano` に潰す（n 一様）。
- **WSEB（Leg W）**: `E_s ≤ C(T,W)·∫₀ᵀf² ≤ C·T·P`（窓エネルギー `∫₀ᵀf² ≤ T·P` は `ContAwgnCode` の
  `encoder_power` が課す）→ `E_s` 一様上界 → `log M` 一様上界 → `BddAbove`。
- **Fano 再配置**（`ε<1` 使用）+ edge case（`n=0` / `M<2`）。
- **ℕ-sSup 罠**: unbounded `sSup` は junk `0`（repo は `Cramer.lean` / `ParallelGaussian/PerCoord.lean` で既遭遇）→
  `BddAbove` が `le_csSup`（leg 3）の前提。

**再利用資産**: `awgn_converse`（AWGN、genuine）+ Leg W `wseb` + `bandlimited_sup_bound`
（`Operational.lean:241`、point-value 補助）。**Legs B/C/E は参照しない**（作用素論を経由しないため）。
**feasibility**: **self-buildable — Leg W（WSEB）が provable な条件付き**。WSEB が壁化すれば Leg D も transitive に壁。
**循環チェック**: サンプリング rate は achievability の構成選択で def 入力でない（C3 ✓）。BddAbove の core を hyp 化しない
（C1/C2 ✓）。
**retreat line**: WSEB が壁 → `sorry + @residual(wall:nyquist-2w-dof)`（既 verdict へ fall back）。**禁止**: `BddAbove` を
`≥` 定理へ hyp 化、`ContAwgnCode` に全直線エネルギー field 追加（壁偽装）。
**consumer wiring**: `contAwgn_ge_shannonHartley`（`ShannonHartleyAchievability.lean:506`）が `le_csSup` で消費。
Leg D genuine 化で leg 3 も transitive に closure（tag は `plan:` のまま、Phase 3 assembly work）。

**code-TODO（`sampledSignal` docstring overstatement）**: `Operational.lean:361–363` の docstring は `√(T/n)`
正規化が離散エネルギーを連続積分に「equal」にすると述べるが、その等号は **n→∞ のみ** で、有限 n の quadrature gap
（= sinc-tail leakage）こそが本壁。当該 file を次に触るとき「equal」を「approximate（n→∞ で一致、有限 n では
WSEB gap）」に軟化する（本 plan は docs-only ゆえコードは触らない）。

---

## Legs B/C/E — Phase-4 tight-count 専用（OFF the BddAbove critical path）📋

**3 leg とも Phase 4 main converse の tight ≈2WT カウント専用**で、中心問題 verdict により **Phase 3 BddAbove の
make-or-break ではない**（それは Leg W = WSEB）。Leg A（DONE）の作用素 object の上に建てる。

- **Leg B — コンパクト性** `IsCompactOperator (timeBandLimitingOp T W)`。HS/Schatten 不在（inventory Q2、Found 0）
  ゆえ finite-rank kernel（sinc 積分作用素）極限で self-build（`isCompactOperator_of_tendsto`、`Compact/Basic.lean:459`）。
  ~500–900 行 zero-scaffolding。**Phase-4 専用**。proof-log: yes。
- **Leg C — 固有値降順列挙 + qualitative effective-rank** `prolateEigenvalues : ℕ → ℝ`（降順）+ `#{k|λ_k>θ}<∞`。
  ✅ **framework CLOSED（de758f19、実測 243 行 vs 見積 ~200–400、監査 PASS 77a5fdf2）**。**Phase-4 専用**。
  **route 訂正（実測）**: `finite_dimensional_eigenspace`（`:463`）+ self-build atom `prolateEigenvalueSet_finite` の 2 つのみ。
  **`orthogonalComplement_iSup_eigenspaces_eq_bot`（`:443`）と Fredholm（`:220` / `:54`）は不使用** — 旧記述が挙げた 3 資産のうち 2 つは無関係だった（実在する Mathlib 補題を route に名指しすることは、その補題に至る手順の健全性を一切保証しない。同 inventory で 2 度目の同型失敗 → Leg B「simple function ⟹ finite rank」）。固有基底の完全性は **Leg D/E の債務**。
  **注意**: effective-rank の **count は BddAbove に対し
  red herring**（tail-eigenvalue / trace gap、中心問題 verdict）— Phase 4 の tight count に属し Phase 3 ではない。
  proof-log: yes。
- **Leg C' — 非空虚性（残債、壁ではない）** `timeBandLimitingOp T W ≠ 0`（`0<T`, `0<W`）→ `0 < prolateEigenvalues T W 0`。
  Leg C の 4 無条件 headline は定数ゼロ列で充足されるため、この atom 無しではスペクトル内容ゼロ。下流 ~35 行は監査が
  machine 検証済（`eq_zero_of_forall_hasEigenvalue_eq_zero` `Spectrum.lean:433` 経由）。`∀ n, λ n ≠ 0` には別途 infinite rank。
- **Leg E — tight concentration** `prolate_eigenvalue_count`: `#{n|1/2<prolateEigenvalues T W n}` の
  `⌊2WT⌋ + O(log WT)` 集中（Landau-Pollak-Slepian）。**genuine irreducible 壁**（loogle `prolate`/`Slepian`/`Mercer`
  Found 0、2026-07-14 確認）。body `sorry + @residual(wall:nyquist-2w-dof)`。**Phase-4 専用**。proof-log: yes（撤退 rationale）。
  **循環チェック（最重要）**: `2WT` は本カウントの **結論** としてのみ現れる（`prolateEigenvalues` / `timeBandLimitingOp`
  の def に `2W`/`⌊2WT⌋` は入らない、C3 ✓）。**statement は `True` placeholder でなく実不等式で書く**。

**共通 retreat line**: Leg B/C の個別補題が Mathlib 不足で詰まれば `sorry + @residual(wall:nyquist-2w-dof)`
（同 wall 集約、compound 化しない）。**hyp bundling 禁止**（compact/count を `*Hypothesis` predicate で渡す = tier-5）。
**def body（`prolateEigenvalues`）は sorry 不可** — real def。

---

## 誠実性制約（explicit）

- **`contAwgnMaxMessages_bddAbove` は route に関わらず `sorry + @residual(wall:nyquist-2w-dof)` のまま**（コード側
  SoT 不変）。WSEB status（provable / 壁 / false）は probe 保留中で、**prose に「壁でない」をキャッシュしない**。
- **tight concentration `prolate_eigenvalue_count`（Leg E）= sanctioned `@residual(wall:nyquist-2w-dof)` 撤退口**。
- **load-bearing hyp bundling 禁止**: WSEB / concentration / compact / BddAbove を `*Hypothesis`/`*Reduction`/`IsXxxClaim`
  predicate に束ねて仮説で渡さない。**`ContAwgnCode` に「全直線エネルギー field」を足して壁を回避しない**
  （窓外 sinc tail の抑制を field 化 = 壁偽装 tier-5）。**`≥` 定理へ `BddAbove` を hyp 化しない**。
- **WSEB が false と判明したら def-fix に escalate**（`ContAwgnCode` / 容量 def）、hyp 化で誤命題を回避しない。
- **compact（Leg B）は GENUINE か honest sorry の二択、fake 禁止**。degenerate 定義悪用 / `:True` slot も禁止。
- **Leg B/C/D/W が詰まった時の honest exit も `wall:nyquist-2w-dof`**（同一 family 集約、compound 化しない）。
  **新 slug は** loogle-0 + two-stage conclusion-shape 検索 + template lemma 行数見積が揃った時のみ。
- **def body に sorry 不可**: `prolateEigenvalues` は commit 前に real def。`wseb` は theorem（proof body に sorry 可）。
- 実装 owner が新 sorry + `@residual` を commit したら **独立 honesty audit を同セッションで起動**（CLAUDE.md）。

---

## feasibility ledger（Leg 別、inventory 引用）

| Leg | target | 判定 | 根拠 |
|---|---|---|---|
| A | 作用素 + 自己共役 + 正 + `‖A‖≤1` | **✅ DONE（genuine、commit 4d848a53）** | `Lp.fourierTransformₗᵢ` + `Submodule.starProjection` + `conj_starProjection` / `of_isStarProjection`。Phase-4 専用 |
| **W** | **WSEB スカラー不等式** | **TRUE + GENUINE WALL（leg 9 決着）** | 単標本 atom は数値 2 独立法で TRUE 確定（FALSE 排除）。self-build は machine-grounded で wall（loogle two-stage 全 0-hit、~800–1500 行 prolate 理論不在）。→ `shannon-hartley-facts.md` |
| D | `contAwgnMaxMessages_bddAbove` | **self-buildable（Leg W 条件付き）** | 中心問題 verdict: `awgn_converse` trace 境界 + `log(1+x)≤x` + WSEB + Fano plumbing（~150–250 行）。作用素論不要 |
| B | コンパクト性 | **self-buildable（~500–900 行）・Phase-4 専用** | HS/Schatten 不在（Q2、Found 0）→ finite-rank sinc kernel 近似 |
| C | 固有値列挙 + qualitative rank | **self-buildable（~200–400 行）・Phase-4 専用** | 構造的 spectral thm + Fredholm。count は BddAbove に対し red herring |
| E | tight concentration | **genuine wall・Phase-4 専用** | LPS asymptotic、Mathlib 完全不在（`prolate`/`Slepian`/`Mercer` Found 0）|

---

## 循環チェック（C3 受入基準・全 Leg 集約）

**C3**: 定数 `2W`/`⌊2WT⌋` は **`prolate_eigenvalue_count`（Leg E）の結論としてのみ** 現れ、どの def の入力にも現れない。
- `timeBandLimitingOp T W` の `W` = 物理帯域幅（入力）≠ DOF カウント `2W`。✓
- `wseb` の統計に `2W`/`⌊2WT⌋` 非入力（`W` は帯域幅、C は n 非依存の定数）。✓
- `prolateEigenvalues` = spectrum から定義、`2WT` 非入力。✓
- Leg D `BddAbove` = WSEB `E_s ≤ C·∫₀ᵀf²` で bound（EXACT `⌊2WT⌋` 不要）、code def をサンプルベクトルに制限しない
  （C1 維持）。✓
- Leg E で初めて `2WT` が **カウントの結論** として出る。✓
tell（循環兆候）: `contAwgn_eq_shannonHartley` が `rfl`/`unfold` のみ、`prolateEigenvalues` def に `2WT` 出現、
reduction が per-sample capacity をそのまま返す — いずれも本 plan の設計では発生しない。

---

## ripple / import

- **signature 変更なし**: Phase 2 は Leg A（新 file `TimeBandLimiting.lean` ADD、DONE）+ Leg D で既存 sorry
  `contAwgnMaxMessages_bddAbove` を **fill**（signature 不変）→ `dep_consumers` blast-radius 不要。
- **consumer**: leg 2 `contAwgnMaxMessages_bddAbove` の消費者は同 file `contAwgn_ge_shannonHartley`
  （`ShannonHartleyAchievability.lean:506`、`le_csSup` 経由、親 plan leg 3）+ Phase 4 main converse（Leg E 経由）。
- **import cycle なし**: `TimeBandLimiting.lean`（Leg A/B/C/E）は Mathlib spectral/Fourier + `NormalizedSinc`/
  `WhittakerShannon` を import。Leg W/D は `ShannonHartleyAchievability.lean` 内（`AWGN.Converse` の `awgn_converse`
  + WSEB 補助を消費、作用素 file `TimeBandLimiting` に依存しない）。

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active な判断のみ（≤ 10 entry）。

1. **中心問題 verdict（NEW）— BddAbove ⟸ スカラー WSEB（旧 compactness verdict を置換）**: 旧 verdict
   「定性コンパクト性 + effective-rank で閉じる」は HALF-RIGHT（tight LPS 不要は正しい）だが route が WRONG。
   effective-rank の count は **大固有値のみ** を抑え、小固有値 tail `≈(2/N)∑_{small}λ_k` は ~n 項で **trace** が
   有界でなければ発散 → count は red herring、必要なのは **trace = E_s = WSEB**（`awgn_converse` が直接供給）。
   よって BddAbove ⟸ スカラー WSEB `E_s ≤ C(T,W)·∫₀ᵀf²`、Legs B/C/E は BddAbove path から外れ Phase-4 専用。
   **コード側 SoT は `contAwgnMaxMessages_bddAbove` = `@residual(wall:nyquist-2w-dof)` 維持**（leg 9 で WSEB=TRUE+wall
   決着後も同じ、settled-facts は `shannon-hartley-facts.md`）。
2. **`√(T/n)` 正規化で `E_s` は Riemann/quadrature 和、`∝ nP` **ではない** — 旧 step-1 の「`I ≲ nP/N₀` が n で発散」
   機構は WRONG**: `sampledSignal = √(T/n)·f(iT/n)` ゆえ `E_s = (T/n)∑f(iT/n)²` は `∫₀ᵀf²` の quadrature 近似で、
   per-sample power `P' = E_s/n`。`awgn_converse` は `I ≤ E_s/N₀`（n 一様）を与える。真の障害は **窓 vs 標本エネルギー
   gap**（sinc-tail leakage、`ShannonHartleyAchievability.lean:461–478` の code docstring が正しく記述）。全標本点
   `iT/n` は `[0,T)` **内部**（out-of-window sampling でない）— gap は quadrature/aliasing + reproducing-kernel coupling。
3. **旧 gateway `‖A_n‖≤1`（frame bound）は mis-specified、WSEB atom で置換**: 全直線エネルギーに対しては誤った量、
   窓エネルギーに対しては honest 定数が `≈2WT`（`≤1` でない）、`√Δ`-Bessel-`≤1` は **undersampling `Δ>1/2W` で FAIL**。
   真の gateway atom は WSEB 単標本 case `T·f(0)² ≤ C·∫₀ᵀf²`。**undersampling `n<2WT` が WORST case**
   （`E_s/∫₀ᵀf²` の sup は小 n で最大、`n=1` で `≈2WT`）= 旧 plan の oversampling 懸念を反転。
4. **WSEB gateway probe 決着（leg 9、ACTIVE user-decision）**: 単標本 atom を数値 2 独立法で **TRUE 確定**（FALSE/def-fix
   排除）+ `lean-implementer` probe で **self-build = GENUINE WALL 確定**（loogle two-stage 全 0-hit、~800–1500 行
   prolate 理論不在）。⟹ **(b) 壁の正面突破は失敗**、`contAwgnMaxMessages_bddAbove` は honest sorry 維持。**次は
   user-decision**（上記「route」3 択: (1) prolate 理論 build ~800–1500 行 moonshot / (2) capacity def を achievable-rate
   形へ refactor で BddAbove 回避 / (3) park）。relay stop #2 で PAUSED。Leg A（DONE）+ Legs B/C/E は Phase 4 に defer。

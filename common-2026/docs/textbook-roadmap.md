# Verified Information Theory Textbook ロードマップ 📚

> **目的**: 本プロジェクトの最終アウトプットを「形式証明済み定理から生成される情報理論の教科書」とする。
> Cover & Thomas *Elements of Information Theory* を骨格に、Lean 4 + Mathlib で 0 sorry に着地した
> 主定理群を一次資料として、**reference library** と **読み物としての教科書原稿** の両方を publish する。
> 単発 seed の `docs/moonshot-seeds.md` がカード一覧、本ファイルは **章単位の完成判定 + 残ギャップを束ねる
> 上位ロードマップ**。

<!--
雛形メモ:
- 本ファイルは複数 moonshot seed を束ねる上位ロードマップ。個別 seed は `docs/moonshot-seeds.md`
  にカード化し、本ファイルからは「章単位の完成判定」「seed ↔ 章のマッピング」で参照する。
- 章単位の進捗表は append-only 更新。状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更
- 各 seed は `→ <plan path>` ポインタを書き、計画着手時に該当 plan ファイルを生やす
- 「教科書として穴がない」基準で seed を選定。Cover-Thomas Ch.6 / 13 / 14 / 16 は明示的に scope-out
-->

## ゴール / Approach

**最終ゴール**: Cover & Thomas *Elements of Information Theory* (2nd ed.) の Ch.2–12, 15, 17 を骨格
として、**Lean 形式化された定理から生成される教科書**を publish する。本プロジェクトの主成果物は
3 層に分かれる:

1. **Verified library** (`Common2026/`): 主定理が 0 sorry で publish 済みの Lean モジュール群。
2. **Typed RV API**: 教科書として読める書き味 (`entropy X`, `mutualInfo X Y`, `H(X|Y)`) を支える
   外向き API 層。internal 証明は measure-theoretic 表現で良いが、教科書本文と一対一対応する
   notation / 補助 lemma を確立する。
3. **教科書原稿**: 上記 2 層を一次資料として、各章の定理ステートメントと証明ハイライトを Lean
   定義へ link した markdown / LaTeX / 製本物。

**Approach**: 既に完成している discrete core (Ch.2–5, 7, 10, 11 大部分) を起点に、`Tier 1 → Tier 4`
の順で seed 化 + 着手する。各 seed は **`docs/moonshot-seeds.md` にカード追加**して個別計画
(`docs/<family>/<topic>-moonshot-plan.md`) に展開、本ロードマップでは **章単位の完成判定 + seed
依存関係** だけを管理する。

## 完成判定

「Lean で verified な Cover & Thomas」を名乗るための必要条件:

- **Ch.2–5, 7–12, 15, 17 の主定理が 0 sorry で publish 済み** (詳細は下記章対応表)
- **Typed RV API** が外向き API として揃い、教科書本文の statement が形式化版に直接対応する
- 各 seed が `docs/<family>/<topic>-moonshot-plan.md` で計画化され、phase 単位で archive 可能
- 主成果物 3 層 (library / API / 原稿) の各層に index と cross-link がある

**scope-out (専門性が異なるため別 library 化)**:

- Ch.6 Gambling and Data Compression (Kelly criterion / doubling rate)
- Ch.13 Universal Source Coding の一部 (LZ78 漸近最適性は scope-in、Lempel-Ziv complexity は out)
- Ch.14 Kolmogorov Complexity (計算可能性論との接合点、別 library)
- Ch.16 Information Theory and Portfolio Theory

## 章対応進捗

| Ch. | 章タイトル | 状態 | 代表定理 (済) | 必要追加 seed | 規模 |
|---|---|---|---|---|---|
| 2 | Entropy, Relative Entropy, Mutual Information | ✅ | `Shannon/Entropy`, `MutualInfo`, `MIChainRule`, DPI | — | — |
| 3 | AEP | ✅ | `AEP.aep_ae`, `aep_inProbability`, `typicalSet_*` | — | — |
| 4 | Entropy Rates of Stochastic Processes | ✅ | `EntropyRate.entropyRate_exists_of_stationary`, `_eq_lim_condEntropy`, `ShannonMcMillanBreiman`, `BirkhoffErgodic` | — | — |
| 5 | Data Compression | 🟡 | `ShannonCode.shannonCode_expected_length_bounds`, Kraft 逆, **`Huffman.huffmanLength_kraft_le_one` + `exists_huffman_prefix_code` + T1-A' `huffmanLength_optimal_with_hypotheses` (weak form)** | **T1-A'' 2 hypothesis discharge** (swap normalization + identification), **T4-A Arithmetic / LZ78** | ~2.5-4k |
| 6 | Gambling and Data Compression | ✖ scope-out | — | — | — |
| 7 | Channel Capacity | ✅ | `shannon_noisy_channel_coding_theorem_general_full`, `_strong_converse`, `_feedback_complete` | — | — |
| 8 | Differential Entropy | ✅ | `DifferentialEntropy.differentialEntropy_gaussianReal`, `_le_gaussian_of_variance_le` | — | — |
| 9 | Gaussian Channel | 🟡 | `AWGN.awgn_channel_coding_theorem` (F-1+F-2+F-3+F-4 pass-through), `AWGN.awgn_capacity_closed_form = (1/2) log(1 + P/N)` | **T2-A discharge** (kernel measurability + continuous typicality + MI bridge + per-letter converse 本体), **T2-B Parallel Gaussian**, **T2-C Bandlimited / Shannon-Hartley** | ~2-3.5k |
| 10 | Rate Distortion | ✅ | `rate_distortion_achievability`, `_converse_*`, `_convexity`, n-letter converse | — | — |
| 11 | Information Theory and Statistics | 🟡 | `stein_strong_law`, `sanov_ldp_equality`, `Pinsker`, `CsiszarProjection` | **T1-B Chernoff**, **T1-C Cramér**, **T1-D Hoeffding tradeoff** | ~1-1.7k |
| 12 | Maximum Entropy | 🟡 | `entropy_le_log_card`, `entropy_eq_log_card_iff` | **T3-A Constrained MaxEnt (Lagrange / exponential family)** | ~400-700 |
| 13 | Universal Source Coding | 📋 | — | **T4-A LZ78 漸近最適性** (Kolmogorov complexity 部分は scope-out) | ~1.5-2.5k |
| 14 | Kolmogorov Complexity | ✖ scope-out | — | — | — |
| 15 | Network Information Theory | 🟡 | `SlepianWolf*` 完備 | **T3-B MAC**, **T3-C Broadcast (degraded)**, **T3-D Wyner-Ziv**, **T3-E Joint source-channel coding (separation)**, **T3-F Relay + cut-set** | ~5-9k |
| 16 | Information Theory and Portfolio Theory | ✖ scope-out | — | — | — |
| 17 | Inequalities in Information Theory | 🟡 | `Han`, `Shearer`, `LoomisWhitney`, `BrascampLieb`, `HypercubeEdgeBoundary`, `Pinsker`, `_sharp` | **T2-D EPI**, **T2-E Brunn-Minkowski**, **T2-F Fisher info / de Bruijn identity** | ~1.8-2.6k |

状態: ✅ = 主定理 publish 済 / 🟡 = 部分達成、追加 seed 要 / 📋 = 未着手 / ✖ = scope-out / 🔄 = 方針変更

**規模の単位**: Lean 行数。±50% 程度の幅で見積もる。基準: `ChannelCodingShannonTheorem.lean` 918 行 / `DifferentialEntropy.lean` 1010 行 / `BirkhoffErgodic.lean` 920 行 / `AEPRate.lean` 831 行 / `ShannonCode*.lean` 系合計 ~700 行。**章別合計 + Infrastructure ~1.3-2.3k = 全体 ~16-25k 行**。

## seed カード (未着手分)

> ここから下は **追加すべき seed 一覧**。優先度ではなく Tier (穴の深さ) で分類。すべて 📋 未着手。
> 着手判断 = 該当 seed を `docs/moonshot-seeds.md` のカード一覧にコピー + `docs/<family>/<topic>-moonshot-plan.md`
> を生成して `moonshot-plan-template.md` で膨らませる。本ロードマップにはポインタ `→ <plan path>` を追記する。

### Tier 1 — discrete core の穴 (教科書として必須)

#### T1-A. Huffman 最適性 (Phase 3 完遂) ✅ (2026-05-19) → [docs/shannon/huffman-moonshot-plan.md](shannon/huffman-moonshot-plan.md)

- **publish**: `Common2026/Shannon/Huffman.lean` (953 行、0 sorry / 0 warning) で 4 件:
  - `huffmanLength : Measure α → α → ℕ` (`Multiset (Finset α × ℝ)` 上の `Nat.strongRec on s.card` で再帰、`huffmanStep` を Subtype 化して spec 焼き込み)
  - `huffmanLength_pos`
  - `huffmanLength_kraft_le_one` (`kraftPerGroup` weighted sum invariant 経路、~310 行核)
  - `exists_huffman_prefix_code` (`ShannonCodeKraftReverse.exists_prefix_code_of_kraft` 経由副系)
- **scope**: amend 後 plan の Phase 3 完遂形 (`huffmanLength` 構成 + Kraft 充足 + prefix code 副系)。
- **scope-out → T1-A'**: Cover-Thomas Theorem 5.8.1 の主定理 (任意 Kraft-feasible `l` との比較形) は分離 (sibling property + n → n-1 induction)。Ch.5 行は T1-A' 完了で 🟢 へ昇格。
- **判断ログ**: §C-5 `Multiset.strongInductionOn` → `Nat.strongRec on s.card` pivot (Session 2)、§C-6 `huffmanStep` Subtype + `HuffmanGrouping` invariant 強化 (Session 4) で Phase 3 着地 (詳細は plan §判断ログ #1-#5)。

#### T1-A'. Huffman 最適性 (sibling property + 任意 `l` 比較、weak form) ✅ (2026-05-19) → [docs/shannon/huffman-optimality-moonshot-plan.md](shannon/huffman-optimality-moonshot-plan.md)

- **publish**: `Common2026/Shannon/HuffmanOptimality.lean` (1054 行、0 sorry / 0 warning) で
  `huffmanLength_optimal_with_hypotheses` — Cover-Thomas Theorem 5.8.1 の主定理を
  **2 hypothesis pass-through 形** (`SwapNormalizationHypothesis` + `HuffmanMergedIdentificationHypothesis`、
  `abbrev Prop` で universe-polymorphic) で publish。証明骨格 (Phase 4 strong induction +
  Bridge L/R + `swap_step_le` ~96 行 helper) は完成。
- **副産物**: `Common2026/Shannon/Huffman.lean` (953 → 961 行) に `huffmanLength_kraft_eq_one`
  (Kraft `= 1` 等号版、~14 行) を追加 publish。
- **判断ログ要点**: Phase 2 sibling 最深性 → 案 B pivot (Phase 4 で `l` 側 swap)、Phase 3.3
  type 不一致 → bridge L sibling-driven 化、Phase 3.4 `0 < l'` 反例 → `card = 2` を Phase 4
  base case 吸収、Phase 4 swap normalization で 2-step swap 不十分 (Kraft = 1 が要) + Sorry #2
  signature バグ発見 → 案 Y (weak form) 採用 (plan 判断ログ #2-#7 参照、proof-pivot-advisor
  相談 2 回)。
- **scope-out → T1-A''**: 2 hypothesis 完全 discharge は分離。Ch.5 🟢 昇格は T1-A'' 完了後。

#### T1-A''. Huffman 最適性 (2 hypothesis 完全 discharge) 📋

- **目的**: T1-A' で hypothesis pass-through 化された 2 件 (`SwapNormalizationHypothesis` +
  `HuffmanMergedIdentificationHypothesis`) を完全証明し、強形 `huffmanLength_optimal`
  (引数 hypothesis なし) を publish。Cover-Thomas Theorem 5.8.1 真の主定理を fully discharged
  形で達成。
- **statement**: `∀ (l : α → ℕ), (∀ a, 0 < l a) → kraftSum 2 l ≤ 1 →
  expectedLength P (huffmanLength P) ≤ expectedLength P l` を **hypothesis なし**で。
- **基盤**: T1-A' で確立した骨格 + `swap_step_le` helper + `huffmanLength_kraft_eq_one`。
- **依存**: T1-A' 完了済。
- **想定 family**: `docs/shannon/huffman-optimality-t1apprime-*`.
- **規模**: ~300-400 行 (swap normalization + Kraft=1 shortening ~150-200 + α/α'
  structural correspondence identification ~150-200)。

#### T1-B. Chernoff Information 📋

- **目的**: Bayesian 仮説検定の指数。Stein と並ぶ Ch.11 の柱の片側。
- **statement**: `P_e^{(n)} \doteq \exp(-n \cdot C(P_1, P_2))` where `C(P_1, P_2) := -\min_{λ ∈ [0,1]} \log \sum_x P_1(x)^λ P_2(x)^{1-λ}`。
- **基盤**: `Stein.lean`, `StrongStein.lean`, `Pinsker.lean`。proof-log で「Stein/Sanov plumbing から 70-80% 再利用可」と記録。
- **依存**: T1-D (Hoeffding tradeoff) との補間関係。
- **想定 family**: `docs/shannon/chernoff-*`。
- **規模**: ~400-600 行 (Chernoff exponent 定義 + 凸性 ~150 + tilted distribution + Sanov 経由 lower bound ~200 + upper bound ~150)。

#### T1-C. Cramér's Theorem 📋

- **目的**: IID 和の LDP。large deviations の独立 statement。
- **statement**: 独立同分布 `X_i` に対し、`(1/n) \log P[\bar{S}_n \in A] \to -\inf_{x \in A} I(x)` where `I = Λ^*`。
- **基盤**: `SanovLDPEquality.lean` (Sanov の上下完成) からほぼ含意可。
- **依存**: 独立形 statement への reshape。
- **想定 family**: `docs/shannon/cramer-*`。
- **規模**: ~300-500 行 (Sanov LDP からの contraction principle 経由 reshape ~200 + Legendre transform + Λ^* 同一視 ~100-200)。

#### T1-D. Hoeffding bound (Type I/II tradeoff exponent) 📋

- **目的**: Stein (Type II 固定) と Chernoff (Bayesian) の補間。
- **statement**: 任意の `α ∈ [0, D(P_1\|P_2)]` に対し、`E_2(α) := \min_{Q : D(Q\|P_1) ≤ α} D(Q\|P_2)`。
- **基盤**: T1-B Chernoff と一括で進めるのが自然。
- **想定 family**: `docs/shannon/hoeffding-tradeoff-*`。
- **規模**: ~200-300 行追加 (T1-B と一括着手で 600-900 行)。

### Tier 2 — continuous / Gaussian theory の完成

#### T2-A. AWGN Channel Capacity 📋

- **目的**: Ch.9 開通。Gaussian channel `Y = X + Z`, `Z ∼ 𝒩(0, N)` の容量 `C = (1/2)\log(1 + P/N)`。
- **statement**: 出力電力制約 `𝔼[X^2] ≤ P` の下で `C = (1/2)\log(1 + P/N)` が達成 + converse。
- **基盤**: `DifferentialEntropy.lean` (Gaussian entropy + max entropy 完成)。
- **依存**: typed RV API 経路の continuous 版整備。
- **想定 family**: `docs/shannon/awgn-*`。
- **規模**: ~1000-1500 行 (continuous channel 抽象 ~300 + achievability sphere packing / joint typicality ~400-600 + converse ~300-400 + capacity-cost wrapping ~100)。 `moonshot-seeds.md` で既に「~1000 行」と見積もり済み。

#### T2-B. Parallel Gaussian Channels + Water-filling 📋

- **目的**: Ch.9 を AWGN 単独で終わらせない。容量領域の制約付き最大化。
- **statement**: 並列 AWGN `Y_i = X_i + Z_i`, `Z_i ∼ 𝒩(0, N_i)` の総電力制約下の容量と water-filling 解。
- **依存**: T2-A AWGN。
- **想定 family**: `docs/shannon/parallel-gaussian-*`。
- **規模**: ~400-600 行 (KKT 条件 + Lagrange 最適化 ~250 + 一意性 + monotonicity ~150-300)。

#### T2-C. Bandlimited Channel / Shannon-Hartley 📋

- **目的**: 連続時間 AWGN への接続。
- **statement**: 帯域 `W`, 雑音電力密度 `N_0` の bandlimited AWGN の容量 `C = W \log(1 + P/(N_0 W))`。
- **依存**: T2-A + 連続時間版の sampling theorem (Mathlib gap 調査要)。
- **想定 family**: `docs/shannon/shannon-hartley-*`。
- **規模**: ~600-1000 行 (Whittaker-Shannon sampling Mathlib gap 埋め ~400-600 + bandlimited from AWGN ~200-400)。Mathlib 上流調査次第で +500 行。

#### T2-D. Entropy Power Inequality 📋

- **目的**: Ch.17 の頂点。Gaussian theory の閉じ。
- **statement**: 独立 `X, Y` に対し `e^{2h(X+Y)} ≥ e^{2h(X)} + e^{2h(Y)}`。
- **基盤**: `DifferentialEntropy.lean`, T2-F Fisher info + de Bruijn 経由が標準。
- **依存**: T2-A / T2-F。
- **想定 family**: `docs/shannon/epi-*`。
- **規模**: ~800-1200 行。`moonshot-seeds.md` で「~2000 行」見積もり済みだが、T2-F (Fisher) を独立 seed 化したので本 seed は EPI 本体に集中。Stam の inequality + 1-parameter ODE 積分。

#### T2-E. Brunn-Minkowski (entropy form) 📋

- **目的**: EPI と表裏。`LoomisWhitney` の系譜で自然な後続。
- **statement**: 凸体 `A, B ⊂ ℝ^n` に対し `|A + B|^{1/n} ≥ |A|^{1/n} + |B|^{1/n}` の entropy 形。
- **依存**: T2-D EPI と相互強化。
- **想定 family**: `docs/shannon/brunn-minkowski-*`。
- **規模**: ~400-600 行 (EPI からの specialization + 凸体測度との橋渡し)。

#### T2-F. Fisher Information + de Bruijn Identity 📋

- **目的**: T2-D EPI の証明経路として標準。
- **statement**: `(d/dt) h(X + \sqrt{t} Z) = (1/2) J(X + \sqrt{t} Z)` where `J` は Fisher information。
- **依存**: なし (T2-A 後、T2-D の前)。
- **想定 family**: `docs/shannon/fisher-info-*`。
- **規模**: ~600-800 行 (Fisher info 定義 + score function 性質 ~250 + de Bruijn identity (Mathlib にあるか調査要、無ければ Stein's identity + ガウス convolution 経由) ~350-550)。

### Tier 3 — Maximum Entropy + Network IT

#### T3-A. Constrained Maximum Entropy (Lagrange / exponential family) 📋

- **目的**: Ch.12 を実質化。`entropy_le_log_card` 単独では薄い。
- **statement**: 制約 `𝔼[f_i(X)] = c_i` 下で max entropy 分布が exponential family `p^*(x) = \exp(\sum \lambda_i f_i(x) - \psi(\lambda))` となる characterization。
- **基盤**: `MaxEntropy.lean`, `CsiszarProjection.lean` (I-projection との対応)。
- **依存**: なし。
- **想定 family**: `docs/shannon/max-entropy-constrained-*`。
- **規模**: ~400-700 行 (Lagrange 双対性 + KKT ~200 + exponential family characterization + uniqueness ~200-300 + Csiszar projection 経由 alternative proof ~100-200)。

#### T3-B. Multiple Access Channel (MAC) 📋

- **目的**: network IT の最初の柱。Ch.15 の入口。
- **statement**: MAC `(X_1, X_2) \to Y` の capacity region characterization (`R_1 ≤ I(X_1; Y | X_2)`, `R_2 ≤ I(X_2; Y | X_1)`, `R_1 + R_2 ≤ I(X_1, X_2; Y)`)。
- **基盤**: `ChannelCoding*` 系の単一ユーザ achievability / converse、`SlepianWolf*` の region 表現。
- **依存**: typed RV API (multi-user 表現)。
- **想定 family**: `docs/shannon/mac-*`。
- **規模**: ~1500-2500 行 (multi-user channel 抽象 ~300 + region 定義 + convexity ~300 + achievability (joint typicality multi-user) ~600-1000 + converse (Fano + chain rule multi-user) ~300-500 + corner-point 経由形 ~100-200)。単一ユーザ channel coding の 2-3 倍。

#### T3-C. Broadcast Channel (degraded) 📋

- **目的**: Ch.15 の第 2 柱。superposition coding。
- **statement**: degraded BC `X \to Y_1 \to Y_2` の capacity region。
- **依存**: T3-B MAC で multi-user API 整備後。
- **想定 family**: `docs/shannon/broadcast-channel-*`。
- **規模**: ~1500-2500 行。MAC と同等規模。superposition coding 構造で achievability は MAC とパターン共有可能。

#### T3-D. Wyner-Ziv 📋

- **目的**: lossy distributed (decoder-side info)。Slepian-Wolf plan で対象外と明記された箇所を回収。
- **statement**: side info `Y` (at decoder only) で `X` を distortion `D` 以下で再現する rate `R_{WZ}(D) = \min_{p(u|x)} \min_{f} [I(X; U) - I(Y; U)]`。
- **基盤**: `SlepianWolf*` + `RateDistortion*`。
- **依存**: 既存 RD + SW で十分。
- **想定 family**: `docs/shannon/wyner-ziv-*`。
- **規模**: ~1000-1500 行 (rate function 定義 + 凸性 ~250 + achievability binning + jointly typical ~500-800 + converse ~250-450)。

#### T3-E. Joint Source-Channel Coding (Separation Theorem) 📋

- **目的**: Ch.5 (source) と Ch.7 (channel) を統合する meta-定理。教科書として章間統合が要る。
- **statement**: stationary ergodic source の entropy rate `H(\mathcal{X}) < C` ⟺ source を error 0 で channel 経由再現可能。
- **基盤**: `source_coding_theorem` + `shannon_noisy_channel_coding_theorem_general_full` + `EntropyRate.lean`。
- **依存**: T3-B MAC 不要、独立。
- **想定 family**: `docs/shannon/separation-theorem-*`。
- **規模**: ~300-500 行 (既存 source + channel の composition で新数学なし、achievability ~150 + converse ~150-200 + ergodic source 対応 ~50-100)。

#### T3-F. Relay Channel + Cut-set bound 📋

- **目的**: Ch.15 の第 3 柱。outer bound でも publish 価値あり。
- **statement**: relay channel の cut-set outer bound。
- **依存**: T3-B / T3-C 後。
- **想定 family**: `docs/shannon/relay-channel-*`。
- **規模**: ~600-1000 行 (cut-set 定義 + outer bound のみ。inner bound (decode-and-forward / compress-and-forward) は scope-out で半分)。フル形 (inner + outer) は ~1500-2500 行。

### Tier 4 — Universal coding

#### T4-A. Arithmetic Coding / Lempel-Ziv (LZ78) 漸近最適性 📋

- **目的**: Ch.13 の柱。stationary ergodic source に対する universal coding。
- **statement**: LZ78 圧縮率が entropy rate に a.s. 収束 `\lim (1/n) \ell(LZ(X^n)) = H(\mathcal{X})`。
- **基盤**: `EntropyRate.lean`, `ShannonMcMillanBreiman.lean`, `BirkhoffErgodic.lean`。
- **依存**: なし (Ch.4 完成済みで足場 OK)。
- **想定 family**: `docs/shannon/lz78-*`, `docs/shannon/arithmetic-coding-*`。
- **規模**: ~1500-2500 行 (LZ78 phrase 木構造 ~300 + Ziv's inequality + phrase counting ~500-800 + SMB 経由 entropy rate 上界 ~400-600 + arithmetic coding (precision + intervals) ~300-500 + 漸近最適性合流 ~200)。

### Tier ∞ — Infrastructure (専用 family)

#### I-1. Typed Random Variable API 📋

- **目的**: 教科書本文と一対一対応する `entropy X`, `mutualInfo X Y`, `H(X|Y)`, `D(X \| Y)` の書き味確立。
  本ロードマップの 3 層成果物の真ん中。
- **scope**: 既存 `Common2026/Shannon/Entropy.lean`, `MutualInfo.lean`, `Fano/CondEntropy.lean` 等の
  外向き wrapping。internal の measure-theoretic 表現は不変、bridge lemma + notation のみ追加。
- **想定 family**: `docs/api/typed-rv-*`。
- **規模**: ~400-800 行 (wrapper def + 既存 measure-theoretic 補題への bridge ~300-500 + notation + 簡易書き換え `simp` set ~100-300)。新数学なし。

#### I-2. General DMC capacity (limit form) 📋

- **目的**: 現状 memoryless 限定の channel coding を `lim (1/n) max_{p^n} I(X^n; Y^n)` 一般形へ。
- **scope**: `IIDProductInput*` を `BlockwiseChannel` 抽象に持ち上げる refactor + 一般 channel での
  capacity 定義 + memoryless 場合の specialization。
- **依存**: T2-A / T3-B 着手前に整備したい (channel 抽象を後から変えると下流大改修)。
- **想定 family**: `docs/shannon/general-dmc-*`。
- **規模**: ~600-1000 行 (`BlockwiseChannel` 抽象 + `capacity_lim` 定義 + 存在・凸性 ~300 + memoryless specialization (既存 capacity と一致) ~200-400 + informationally stable channels 経由 spectral form ~100-300)。

#### I-3. Asymptotic / exponent framework 📋

- **目的**: 各 proof で inline に書いている exponent / rate 表現を集約。
- **scope**: `\doteq` (exponent equality), `o(n)` notation, exponent function 共通 API。
- **想定 family**: `docs/api/asymptotic-*`。
- **規模**: ~300-500 行 (notation 定義 + 基本性質 (transitivity, scalar) + `Tendsto.metric_atTop` の closed-form 抽出パターンの一般化 wrapper)。

## 推奨着手順

依存関係に従う場合の自然な順序 (実装コストではなく **正しさ起点**):

1. **I-1 Typed RV API** + **I-2 General DMC** + **I-3 Asymptotic framework**
   — 後続 seed が全部この上に乗るため、最初に整備しないと後で大改修コスト。
2. **T1-A Huffman**, **T1-B Chernoff**, **T1-C Cramér**, **T1-D Hoeffding** (discrete core 穴埋め、並列着手可)。
3. **T2-A AWGN** → **T2-B Parallel Gaussian** → **T2-C Shannon-Hartley** (Gaussian channel 三段)。
4. **T2-F Fisher** → **T2-D EPI** → **T2-E Brunn-Minkowski** (inequalities 三段)。
5. **T3-A Constrained MaxEnt** (Ch.12 独立完成)。
6. **T3-E Separation theorem** (Ch.5 + Ch.7 統合、独立着手可)。
7. **T3-B MAC** → **T3-C BC** → **T3-D Wyner-Ziv** → **T3-F Relay** (network IT 段階的)。
8. **T4-A LZ78 + Arithmetic** (Ch.13 仕上げ、Ch.4 基盤完成済みで独立)。

## 規模の総計

| 層 | 規模 (±50%) |
|---|---|
| Tier 1 (discrete 穴埋め: Huffman / Chernoff / Cramér / Hoeffding) | ~1.4-2.1k 行 |
| Tier 2 (Gaussian channel + EPI 系: T2-A〜F) | ~3.8-5.6k 行 |
| Tier 3 (MaxEnt + Network IT: T3-A〜F) | ~5.3-8.8k 行 |
| Tier 4 (Universal coding: T4-A) | ~1.5-2.5k 行 |
| Infrastructure (I-1〜3) | ~1.3-2.3k 行 |
| **追加合計** | **~13.3-21.3k 行** |
| (参考) 既存 `Common2026/Shannon/` 完成分 | ~30k 行強 |

「Cover-Thomas Ch.2-12+15+17 を verified library で代替」する規模は、現状の Shannon 配下 (~30k 行) に
**追加で ~15-20k 行** の見立て。proof-log の自己評価 (「派生定理の 70-80% は plumbing 再利用」) を踏まえ、
T1-B/C/D の Sanov plumbing 再利用、T2-D の T2-F 再利用、T3-C の T3-B 再利用、T3-F の T3-B/C 再利用で、
**実質的な「新規証明 onset」は ~10-13k 行程度**と推定。

## 教科書原稿 (層 3) の方針

- **形式**: markdown 原稿 → LaTeX → 製本 PDF。各定理は Lean 定義 (`Common2026/...`) へ permalink。
- **対象読者**: 学部 4 年生〜大学院初年度。Cover-Thomas を読みながら横で開ける形式化版を想定。
- **構成**: 章は Cover-Thomas の章番号に追従。`scope-out` 章 (Ch.6/13 部分/14/16) は省略。
- **執筆判断**: 各章は対応する Lean 定理がすべて 0 sorry になった時点で初稿着手。1 章完成 →
  cross-link 整備 → publish の段階管理。
- **layout**: `docs/textbook/` 下に章別 markdown を生やす想定 (本ロードマップ完成時点では未生成)。

## 判断ログ

書く頻度: seed 追加/撤退、Tier 移動、章ステータス変更、scope-out 判定の修正があったとき。append-only。

1. **2026-05-18 起草**: ユーザー指示「教科書化を最終目的に据えてロードマップを書く」を受けて
   `docs/textbook-roadmap.md` 新規作成。Cover-Thomas Ch.2–17 のうち Ch.6 / 14 / 16 を scope-out、
   Ch.13 を partial scope-in (LZ78 のみ) と確定。Tier 1–4 + Infrastructure として 18 seed を登録。
   既存 `docs/moonshot-seeds.md` は単発 seed カード一覧として残置、本ファイルは章単位の上位
   ロードマップとして並置する役割分担とする。
2. **2026-05-18 サイズ見積もり追記**: 各 seed カードに「規模」行を追加 (±50% 精度)、章対応表に
   「規模」列、規模の総計節を追加。基準は既存ファイル行数 (`ChannelCodingShannonTheorem.lean` 918,
   `DifferentialEntropy.lean` 1010, `BirkhoffErgodic.lean` 920, `AEPRate.lean` 831)。追加合計
   ~13-21k 行 (実質新規 ~10-13k)、既存 ~30k に対し 1/3-2/3 規模の増分。
3. **2026-05-19 並列 5-seed 着地** (orchestrator session): 5 seed を並列 subagent chain で
   駆動して合計 **+1975 行 / 0 sorry / 0 warning** で publish。シード別:
   - **T1-D Hoeffding** (L-H4 variational scaffolding 形): `HoeffdingTradeoff.lean` +316 行。
     `hoeffding_tradeoff_with_hypothesis` (`hQs_pos` 仮定形 Tendsto) + 14 declarations
     (pmf↔Measure bridge + Type II + 凸性 + Pythagoras)。`hoeffdingE2_minimizer_full_support`
     の log-singularity gradient 引数 (~30-50 行) を要するため Phase C/D sandwich Tendsto は
     後継 plan `hoeffding-tradeoff-sandwich-plan.md` に分離。Ch.11 行は 🟡 のまま。
   - **T2-A AWGN** (F-1+F-2+F-3+F-4 hypothesis pass-through): `AWGN.lean` 275 +
     `AWGNAchievability.lean` 72 + `AWGNConverse.lean` 94 + `AWGNMain.lean` 107 = +548 行。
     `awgn_channel_coding_theorem` 主定理 + `awgn_capacity_closed_form` corollary publish。
     新規 F-4 (kernel measurability、Mathlib に `Measurable (fun x => gaussianReal x N)` の
     直接 lemma がない) を本実装で発見。Ch.9 行は 🟡 昇格 (主定理 hypothesis 形で publish)。
   - **T2-F Fisher Gaussian discharge** (L-G3 Stage 1): `FisherInfoGaussian.lean` 329 新規
     + `FisherInfo.lean` 14 back-port = +343 行。Phase A (`IsRegularDensity gaussianReal m v`
     instance) + Phase B-1/B-2 完了。`fisherInfo` 定義に representative-dependence flaw
     (`Measure.rnDeriv` の `Classical.choose` 経由で Gaussian の場合 `fisherInfo = 0`) を発見、
     parent plan Tier 2 publish 形を破壊するため後継 plan で fisherInfo 再定義 + Phase B-3/C/D
     を扱う。Ch.17 行は 🟡 のまま。
   - **T1-C Cramér L-C2 (部分 discharge)** (L-D3 撤退): `CramerLC2Discharge.lean` +171 行。
     Phase A tilted IID plumbing 6 補題 (`cgf_eval_eq_cgf_base`, `iIndepFun_tilted_ambient`,
     `identDistrib_tilted_ambient`, `iIndepFun_eval_under_infinitePi`,
     `identDistrib_eval_under_infinitePi`, `bounded_eval_family`) を独立 infrastructure publish。
     `cramer_lower_discharged` (hypothesis-free) は未達 — `IsProbabilityMeasure
     (Measure.infinitePi (fun _ : ℕ => μ₀.tilted ...))` instance synthesis の beta-reduction
     不一致で Phase B 詰まり (Mathlib PR 候補)。Ch.11 行は 🟡 のまま。
   - **T3-D Wyner-Ziv** (L-WZ1/2/3 + L-WP-statement-pass): `WynerZiv.lean` 366 +
     `WynerZivAchievability.lean` 99 + `WynerZivConverse.lean` 132 = +597 行。Phase A 完全実装
     (`WynerZivCode` + `wzMarginal*` + `wzMutualInfo*` + `WynerZivConstraint` + `wynerZivRatePmf` +
     attained_slice 形)。Phase B/C/D は statement-level pass-through で publish — random binning +
     三項 jointly typical decoder + n-letter chain rule の本体 discharge は別 plan defer。
     Ch.15 行は 🟡 のまま (statement-level の Wyner-Ziv は publish 済、本体 discharge は別 plan)。
   - **T1-A'' Huffman 2-hypothesis discharge** (no-op 再判定): judgement log #3 で前回 no-op 判定
     (~550 行 / 4-6 セッション、1 セッション完遂不可) を再確認、Phase 0 probe のみ実施で着手前撤退。
     Ch.5 行は 🟡 のまま (T1-A' weak form publish 済、T1-A'' 完全 discharge は未達)。
   <br>**集計**: 11 ファイル新規 + 1 ファイル back-port 修正、全 `lake env lean` clean。今回は
   parent definition flaw 発見 (T2-F の `fisherInfo` representative-dependence) と Mathlib 上流
   PR 候補 2 件 (`Measure.infinitePi_const_isProbabilityMeasure`, `Measurable (fun x => gaussianReal x N)`)
   が副産物。

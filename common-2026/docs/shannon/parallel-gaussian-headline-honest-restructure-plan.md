# Parallel Gaussian: ② headline load-bearing-hyp → sorry+@residual honest restructure サブ計画

> **Parent**: [`parallel-gaussian-l-pg1-discharge-plan.md`](parallel-gaussian-l-pg1-discharge-plan.md) — Phase 4 で着地した
> `parallel_gaussian_capacity_formula_minimal` が独立 honesty 監査で tier 5 (load-bearing-hyp) 判定されたことを受けた後続。

<!--
記法: 状態絵文字 📋/🚧/✅/🔄、取り消し線で廃止 Phase、判断ログ append-only。
本 plan は docs-only。Lean 実装は lean-implementer に dispatch。
plan filename stem = `parallel-gaussian-headline-honest-restructure-plan` →
@residual(plan:...) で参照される slug。
-->

## 進捗

- [ ] M0 在庫調査 — 現 signature verbatim 確認 + genuine reduction chain の到達点確定 📋
- [ ] R1 `isParallelGaussianPerCoordRegularity_of_pieces` honest restructure 📋
- [ ] R2 `parallel_gaussian_capacity_formula_minimal` honest restructure 📋
- [ ] R3 `@[entry_point]` 再判定 + caller 影響確認 📋
- [ ] R4 独立 honesty 監査 (sorry+@residual classification 検証) 📋
- [ ] R5 converse 2 件 (`bddAbove`/`max_ent`) genuine closure → 子 plan [`parallel-gaussian-converse-closure-plan.md`](parallel-gaussian-converse-closure-plan.md) 📋

## ゴール / Approach

### ゴール

`InformationTheory/Shannon/ParallelGaussianPerCoordRegularity.lean` の 2 declaration を、現状の
**load-bearing hypothesis packaging** (tier 5) から **sorry + `@residual`** (tier 2) に書き換え、
プロジェクトの honesty バー (標準B、proof done = 0 sorry かつ 0 residual) と整合する正直な中間状態に落とす。

監査結論 (verbatim、ファイル docstring に既に記録済):

- `isParallelGaussianPerCoordRegularity_of_pieces` (`:104`): body に sorry 無いが、結論
  `IsParallelGaussianPerCoordRegularity` を open hyp `h_bdd_global` / `h_multivar_decomp` に丸ごと帰着。
  これらは regularity precondition ではなく analytic 核心 (`bddAbove` field の global MI 上界 +
  `max_ent` field の per-coord max-entropy converse split) = load-bearing。
- `parallel_gaussian_capacity_formula_minimal` (`:165`): body に sorry 無いが、water-filling
  capacity 等式を `h_bdd_global` + `h_perCoordMI` + `h_multivar_decomp` に帰着。`h_kkt`/`h_opt` は
  genuine (water-filling 最適性) だが 3 つの MI-analysis hyp は load-bearing。

### Approach (solution の shape)

**「genuine な所まで進めて、本当の壁でだけ sorry」** が本 restructure の核心方針。3 つの load-bearing hyp を
ただ drop して全 body を `sorry` にするのではなく、**file 内に既に存在する genuine reduction chain を body
で本当に呼び出し**、Mathlib/未証明の核心部分でだけ sorry を立てる。

決定的な観察: 親ファイル `InformationTheory/Draft/Shannon/ParallelGaussianPerCoord.lean` には
**load-bearing hyp の 3 つ全てを genuine に供給できる reduction chain が既に揃っている**:

| 現 headline の load-bearing hyp | 親ファイルの genuine reduction で何に帰着するか |
|---|---|
| `h_perCoordMI` (per-coord AWGN achiever closed form) | `awgn_mi_gaussian_closed_form_of_primitives` (`AWGNMIBridge.lean:264`、**genuine**、active @residual 0 件) — 入力 `gaussianReal 0 (Q i)`、結論 `(1/2)log(1+Qᵢ/Nᵢ)` が hyp と verbatim 一致。`h_out`/`h_decomp` を要求するが、それらは `awgn-mi-decomp-plan` で discharge 済の AWGN residual chain (`@audit:closed-by-successor(awgn-mi-decomp-plan)`) |
| achiever bundle 化 (`h_bridge_per_coord`) | `parallelGaussianCapacity_achiever_mi` (`PerCoord.lean:809`、**genuine 構造的 reduction**) — per-coord 値から bundle sum へ。内部 `parallelGaussian_achiever_mi_eq_sum_perChannel` (`:789`) は `wall:multivariate-mi` を **closed** にした上で per-coord 有限性 `awgn_mutualInfoOfChannel_ne_top` (`:716`、`hN` 付きで genuine) を使う |
| `max_ent` field の subadditivity | `parallelGaussian_max_ent_le_of_subadditivity` (`PerCoord.lean:292`、**genuine** — `jointDifferentialEntropyPi_le_sum` で出力エントロピー subadditivity が 0 sorry 化済) |
| sup-sandwich の組立 | `isParallelGaussianPerCoordReduction_discharged` (`:338`) → `parallel_gaussian_capacity_formula` (`:404`、genuine `le_antisymm`) |

したがって本当に残る「壁」は **2 種類だけ**:

1. **`wall:multivariate-mi`** — `h_bdd_global` (converse の global MI 上界) と `h_multivar_decomp`
   (任意 feasible 入力の per-coord max-entropy converse split)。両者とも correlated-input
   max-entropy converse の analytic 核心であり、`multivariate-mi` wall register
   (`audit-tags.md:62`、「連続 `mutualInfo_pi_eq_sum` 多変量 MI 加法性」、Ch.9 ParallelGaussian) に属する。
   監査 advisor も「`h_multivar_decomp` と同種の correlated-input max-entropy content」と評価。
   ※注意: achiever 側の `parallelGaussian_achiever_mi_eq_sum_perChannel_enn` が closed にしたのは
   **product (independent) input** 上の加法性。converse 側は **correlated input** 上の不等式なので、
   同じ `wall:multivariate-mi` slug 下だが achiever closure では片付かない (下記 M0 で verbatim 確認)。

2. **AWGN single-channel 側の residual** — `h_perCoordMI` を `awgn_mi_gaussian_closed_form_of_primitives`
   で genuine に供給する経路。この lemma は `IsAwgnOutputGaussian` / `IsAwgnMIDecomp` を hyp に取り、
   それらは `awgn-mi-decomp-plan` で discharge される。`wall:multivariate-mi` ではない。

**結論として 2 declaration の honest 形は**:

- `isParallelGaussianPerCoordRegularity_of_pieces`: `bddAbove` / `max_ent` の 2 field を genuine
  reduction で進められる所まで進め、**converse の `wall:multivariate-mi` 核でだけ sorry**。`achiever_mi`
  field は `parallelGaussianCapacity_achiever_mi` 経由で genuine (per-coord AWGN は `h_perCoordMI` を
  別 sorry で立てるか、constructor 引数として regularity 的に残すかは R1 で確定)。
- `parallel_gaussian_capacity_formula_minimal`: genuine な sup-sandwich (`parallel_gaussian_capacity_formula`)
  を呼び、その `h_reg` を上記 constructor で供給。最終的に立つ sorry は (a) converse の
  `wall:multivariate-mi`、(b) per-coord AWGN closed form (`h_perCoordMI` 供給) の 2 種。

複数の独立 sorry に分かれるので、各 sorry に適切な `@residual` を **sorry 直前行コメント** で付ける
(`audit-tags.md` 配置ルール: 複数 sorry → 各 sorry 直前)。

## Phase 詳細

### M0 — 在庫調査 / genuine reduction chain の到達点 verbatim 確認 📋

実装前に **verbatim Read で確定** する (勘で sorry 配置を決めない):

- [ ] **achiever 側 closure の対象を確認**: `parallelGaussian_achiever_mi_eq_sum_perChannel_enn`
  (`PerCoord.lean:588`) が closed にしたのは **product input `gaussianProductInput Q`** 上の加法性
  (`compProd`-of-`Measure.pi` factorization 経由)。converse の `h_bdd_global` / `h_multivar_decomp` は
  **任意 feasible 入力 `p`** (相関あり) 上の不等式 → achiever closure では供給されない。この区別を verbatim 確認し、
  converse sorry を「achiever closure で消える」と誤判定しないこと (drift 防止)。
- [ ] **`h_perCoordMI` の供給経路を確認**: `awgn_mi_gaussian_closed_form_of_primitives`
  (`AWGNMIBridge.lean:264`) の結論 `(mutualInfoOfChannel (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal = (1/2) log(1 + P/N)` と、headline の `h_perCoordMI i` 結論
  `(mutualInfoOfChannel (gaussianReal 0 ((waterFillingPower ν N i).toNNReal)) (awgnChannel (N i) (h_meas i))).toReal = (1/2) log(1 + (waterFillingPower ν N i).toNNReal/(N i))` を照合。
  入力 `P := waterFillingPower ν N i` (`waterFillingPower_nonneg` で `0 ≤`、`hP_pos` は active coord でのみ
  `0 <`)、`P.toNNReal` の coe 一致を確認。inactive coord (`waterFillingPower = 0`) で `gaussianReal 0 0 = dirac 0` →
  MI 0 = `(1/2)log 1` の退化 case を verbatim 確認 (CLAUDE.md「具体的数値・型予測の verbatim 確認」)。
- [ ] **finiteness の `hN` 経路を確認**: `awgn_mutualInfoOfChannel_ne_top` (`PerCoord.lean:716`) は現状
  `(N : ℝ≥0) (hN : N ≠ 0) (h_meas) (P : ℝ≥0)` 形 (session 内 `N ≠ 0` 追加済)。headline は `hN : ∀ i, (N i : ℝ) ≠ 0`
  を持つので thread 可能。R2 で `∀ i, (N i : ℝ) ≠ 0` ↔ `N i ≠ 0` の coe 変換を確認。
- [ ] **AWGN closed-form の transitive residual を確認**: `awgn_mi_gaussian_closed_form_of_primitives` が取る
  `IsAwgnOutputGaussian` / `IsAwgnMIDecomp` (`AWGNMIBridge.lean:123,135`) の discharge 元 lemma 名と residual class を
  確認 (`@audit:closed-by-successor(awgn-mi-decomp-plan)`)。`h_perCoordMI` 用 sorry の `@residual` を
  `wall:multivariate-mi` ではなく **AWGN 側 slug** にする根拠を固める (下記 R2 の分類決定参照)。
- [ ] **converse の genuine 到達点を確認**: `parallelGaussian_max_ent_le_of_subadditivity` (`PerCoord.lean:292`) が
  取る hyp (`h_decomp` = 多変量 channel↔RV MI 分解、`h_perCoord` = per-coord max-entropy) のうち、subadditivity
  本体 (`jointDifferentialEntropyPi_le_sum`) は genuine。残る load-bearing は `h_decomp` (= correlated-input
  channel↔RV decomp) + `h_perCoord` の per-coord max-entropy 値。これらが `wall:multivariate-mi` 核であることを確認。

### R1 — `isParallelGaussianPerCoordRegularity_of_pieces` honest restructure 📋

target signature (load-bearing hyp drop、regularity precondition のみ保持):

- [ ] **drop**: `h_bdd_global` / `h_multivar_decomp` (load-bearing converse 核)。
- [ ] **achiever_mi field の扱いを R1 で確定** — 2 案:
  - **案 A (推奨)**: `h_perCoordMI : ∀ i, (mutualInfoOfChannel (gaussianReal 0 (Q i)) (awgnChannel (N i) (h_meas i))).toReal = (1/2) log(1 + Qᵢ/Nᵢ)` を **per-coord regularity-shaped hyp として残す** (これは「per-coord AWGN closed form」= 単一チャネルの解析的事実で、`p` に依存しない pin-down ＝ load-bearing ではなく channel の固定値特性。判定軸: 結論等式の核心を inject していない、単一チャネルの値)。body は `achiever_mi := parallelGaussianCapacity_achiever_mi Q N h_meas h_parallel_meas hN h_perCoordMI` で genuine。
    - ※判定の境界事例。`h_perCoordMI` を残すと「per-coord 値を仮定」に見えるが、これは **product input** の achiever 値であり結論 (`max_ent`/`bddAbove` の converse) とは別 field。監査 R4 で「regularity か load-bearing か」を独立判定させる。境界が load-bearing 寄りと判定されたら案 B に倒す。
  - **案 B**: `h_perCoordMI` も drop し、`achiever_mi` field 自体を sorry にして `@residual(plan:awgn-mi-decomp-plan)` (AWGN single-channel closed form の discharge 待ち)。
- [ ] **`bddAbove` field**: `h_bdd_global` を drop した代わりに body で sorry。
  `@residual(wall:multivariate-mi)` (converse global MI 上界、correlated-input max-entropy 核)。
- [ ] **`max_ent` field**: `h_multivar_decomp` を drop した代わりに body で sorry。
  `@residual(wall:multivariate-mi)` (correlated-input per-coord max-entropy converse split)。
  - genuine に進められる範囲: `parallelGaussian_max_ent_le_of_subadditivity` の subadditivity 部分は呼べるが、
    その `h_decomp` (correlated channel↔RV 分解) が壁。**ここまで進めて壁で sorry** を試みる。subadditivity を
    呼ぶには `μY` (joint output law) の構成が要るので、R1 では「subadditivity を呼べる形まで進めたら呼ぶ、
    呼べなければ field 全体を `sorry + @residual(wall:multivariate-mi)`」を許容 (撤退ライン §1 参照)。

restructure 後の docstring: 監査が書いた honest note を残し、`@audit:ok` は付けない (sorry が残るため tier 2)。
docstring 末尾に「load-bearing hyp を drop、converse 核は `wall:multivariate-mi` で sorry 化」を 1 段で明記。

### R2 — `parallel_gaussian_capacity_formula_minimal` honest restructure 📋

- [ ] **drop**: `h_bdd_global` / `h_multivar_decomp`。
- [ ] **`h_perCoordMI` の扱いは R1 案 A/B と整合させる**:
  - 案 A 採用時: `h_perCoordMI` は残す (per-coord AWGN closed form、regularity-shaped)。body は現状どおり
    `parallelGaussianCapacity_achiever_mi` 経由で genuine、constructor に渡す。
  - 案 B 採用時: `h_perCoordMI` も drop、body 内で per-coord achiever 値を sorry。
    `@residual(plan:awgn-mi-decomp-plan)`。
- [ ] **保持**: `h_kkt` (L-WF1) / `h_opt` (L-WF2) — genuine water-filling 最適性 (regularity ではないが
  conclusion の核心でもない、IVT/concavity で discharge 可能な genuine 入力。drop しない)。`hP` / `hN` /
  `h_meas` / `h_parallel_meas` は regularity precondition、保持。
- [ ] **body**: `parallel_gaussian_capacity_formula` (`PerCoord.lean:404`、genuine `le_antisymm` sup-sandwich) を
  呼び、その `h_reg` を R1 の constructor `isParallelGaussianPerCoordRegularity_of_pieces` で供給。
  constructor 側に sorry が立つので headline 自体は body に直接 sorry を持たず、**transitive sorry** になる
  (constructor の `wall:multivariate-mi` を継承)。
  - ※transitive sorry は Lean の type-check が追跡するので headline 側に `@residual` を重複付与しない
    (`audit-tags.md`: 依存先の sorry は依存先で `@residual` 管理)。ただし headline docstring に
    「transitive に `wall:multivariate-mi` (+ 案 B 時 `plan:awgn-mi-decomp-plan`) に依存」を散文で明記。

**`@residual` 分類決定 (verbatim 照合済 slug)**:

| sorry 箇所 | `@residual` 分類 | 根拠 (audit-tags register) |
|---|---|---|
| `h_bdd_global` 由来 (constructor `bddAbove`) | `@residual(wall:multivariate-mi)` | register `:62` 「連続 `mutualInfo_pi_eq_sum` 多変量 MI 加法性」Ch.9 ParallelGaussian。converse の correlated-input global 上界はこの wall の converse 側 |
| `h_multivar_decomp` 由来 (constructor `max_ent`) | `@residual(wall:multivariate-mi)` | 同上。`1527f2c` commit が「wall:multivariate-mi isolated」と主張、整合 |
| `h_perCoordMI` 由来 (案 B 時のみ) | `@residual(plan:awgn-mi-decomp-plan)` | AWGN single-channel closed form。`awgn_mi_gaussian_closed_form_of_primitives` が `@audit:closed-by-successor(awgn-mi-decomp-plan)`。`wall:multivariate-mi` ではない |

- [ ] 分類 verbatim 確認: `wall:multivariate-mi` は register に登録済 (新規追加不要)。`plan:awgn-mi-decomp-plan` は
  `docs/shannon/awgn-mi-decomp-plan.md` が実在することを確認 (`@residual(plan:...)` slug = plan filename stem)。

### R3 — `@[entry_point]` 再判定 + caller 影響確認 📋

- [ ] **`@[entry_point]` の意味を確認済**: `InformationTheory/Meta/EntryPoint.lean` より、`@[entry_point]` は
  **orphan-detection の BFS root マーカーのみ**。coverage / completion metric ではない (監査の「coverage metric
  inflation」懸念は EntryPoint の役割誤認、ただし sorry-based 後も entry_point の妥当性は判断する)。
- [ ] **caller 確認済 (verbatim)**: `rg` で両 declaration の external caller は **0 件**
  (`isParallelGaussianPerCoordRegularity_of_pieces` / `parallel_gaussian_capacity_formula_minimal` は
  `ParallelGaussianPerCoordRegularity.lean` 内自己参照のみ、他 file からの呼び出し無し)。→ signature から
  load-bearing hyp を drop しても **下流 caller は壊れない**。
- [ ] **entry_point 判定**:
  - 両 declaration が L-PG1 discharge の headline (file の存在理由) なので、**`@[entry_point]` は維持**が妥当
    (sorry-based になっても「この family の到達目標 declaration」として orphan BFS root に値する。
    維持しないと依存 declaration が orphan 報告される)。
  - sorry が残る間は「entry_point だが proof done ではない」状態。これは honesty workflow 上問題ない
    (entry_point ≠ 完成マーカー)。docstring の honest note で「conditional / sorry 残置」を明示すれば十分。

### R4 — 独立 honesty 監査 📋

- [ ] R1/R2 commit 後、**fresh `honesty-auditor` subagent** を 1 件起動 (実装 agent の self-audit 不可)。
  渡す入力: file path + 2 declaration 名 + line 番号 + commit hash + 本 plan path。
- [ ] 監査スコープ: (a) sorry+`@residual` の classification 正しさ (`wall:multivariate-mi` /
  `plan:awgn-mi-decomp-plan` の妥当性)、(b) R1 案 A 採用時 `h_perCoordMI` が「regularity か load-bearing か」の
  独立判定、(c) signature が genuine reduction を本当に呼んでいるか (全 body sorry の手抜きでないか)、
  (d) entry_point 維持の妥当性。
- [ ] verdict 全 OK → proof done ではないが type-check done + honest (tier 2) で closure。handoff に明記。
  DEFECT → sorry-based に再修正。

## 撤退ライン + honesty 撤退口

1. **converse を genuine に進めるのが想定以上に重い場合** (例: `parallelGaussian_max_ent_le_of_subadditivity` を
   呼ぶための `μY` joint output law の構成が `wall:multivariate-mi` 自身に依存して循環する): R1 の `bddAbove` /
   `max_ent` field を **field 全体 `sorry + @residual(wall:multivariate-mi)`** に倒す。genuine subadditivity を
   呼べる所まで進める努力目標は放棄してよい — 重要なのは load-bearing hyp を drop して sorry+@residual に
   置き換える honesty 改善であり、reduction chain の最大活用は二次目標。
2. **R1 案 A の `h_perCoordMI` が R4 で load-bearing 判定された場合**: 案 B に倒し、`h_perCoordMI` も drop して
   `achiever_mi` field を `sorry + @residual(plan:awgn-mi-decomp-plan)` 化。
3. **achiever finiteness `hN` thread が型 mismatch する場合** (`∀ i, (N i : ℝ) ≠ 0` ↔ `N i ≠ 0` の coe 変換):
   M0 で verbatim 確認済の coe 補題を body で挟む。解決不能なら finiteness 部分を独立 sorry +
   `@residual(wall:multivariate-mi)` (achiever closure の finiteness slug は親 plan で `l-pg1-discharge-plan`
   に統合済、CLAUDE.md commit `b1e57e8` 参照)。
4. **`*Hypothesis` predicate bundling 禁止**: 詰まっても load-bearing hyp を `IsXxxHypothesis` predicate に
   束ねて回避しない (tier 5)。必ず sorry + `@residual` (tier 2) で抜ける。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-29 起草**: 独立 honesty 監査が 2 declaration を tier 5 (load-bearing-hyp packaging) 判定し
   `@audit:ok` 除去 + honest note 追記済 (ファイル `:93-103`, `:153-164`)。本 plan は監査結論を受けた
   sorry-based restructure。verbatim Read で確認した重要事実: (a) 両 declaration の external caller 0 件
   (signature 変更が下流を壊さない)、(b) 親ファイル `ParallelGaussianPerCoord.lean` に genuine reduction
   chain が既存 (`parallelGaussianCapacity_achiever_mi` / `parallelGaussian_max_ent_le_of_subadditivity` /
   `parallel_gaussian_capacity_formula` いずれも genuine、active @residual 0 件)、(c) achiever 側
   `wall:multivariate-mi` は **product input** 上で closed だが converse は **correlated input** 上の別不等式
   なので同 slug 下でも achiever closure で消えない、(d) `h_perCoordMI` は `wall:multivariate-mi` ではなく
   AWGN single-channel closed form (`awgn_mi_gaussian_closed_form_of_primitives`、`plan:awgn-mi-decomp-plan`)。
   `@[entry_point]` は orphan BFS root マーカーで完成 metric ではないため sorry-based 後も維持が妥当。

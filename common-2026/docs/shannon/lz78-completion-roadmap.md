# LZ78 漸近最適性 完遂ロードマップ (incremental)

> 派生元: `docs/textbook-roadmap.md` 判断ログ #6 (詳細経緯は `git log -- docs/textbook-roadmap.md` の 2026-05-26 ロードマップ整理前 commit、特に旧 #17–#26 の Huffman/LZ78 grind 履歴)。
> 目的: **T4-A LZ78 (Cover–Thomas Thm 13.5.3) を標準B (無条件機械検証) で完遂**。
> 方針: `/goal` 一発完遂ループではなく、**各マイルストーンが genuine・committable・verifiable な単独 deliverable** となる少しずつ確実な進行。M1→M5 の順で、前段が次段の足場になる。

主定理: stationary ergodic source に対し圧縮率 `(1/n)·lz(X^n) → H` (base-2 entropy rate) a.s.

---

## 0. 現状 (2026-06-20、符号長 def-fix 後)

**headline は type-check done であって proof done でない。** entry_point
`lz78_asymptotic_optimality_with_greedy_impl`
(`InformationTheory/Shannon/LZ78/GreedyParsingImpl.lean`) は genuine 命題だが、
`#print axioms` は genuine M3/M4 壁 2本経由で sorryAx 依存。SoT はコード側タグ
(`@residual(wall:...)`)、本節は二次。

### 確定事実 (符号長 def-fix、commit `5d08566` + 監査注記 `9b09790`)

1. **符号長 = genuine longest-prefix parse 化済**。`lz78GreedyImplEncodingLength n x`
   = genuine distinct phrase count `c = (lz78PhraseStrings (List.ofFn x)).length` を
   語数とする `c · bitLength c |α|`。以前のダミー1シンボル parse (count=n, rate 発散)
   は削除済。`c ≤ n`、genuine Ziv `c·log c ≤ K·n` (`lz78PhraseStrings_mul_log_le`、
   sorryAx-free) で rate は `O(1)`。
2. **2 headline sorry = genuine M3/M4 壁** (`GreedyParsingImpl.lean §3`):
   - `lz78GreedyImpl_converse_ae` = `@residual(wall:lz78-converse-aseventual)`
     (M4 Barron a.s. lift)。
   - `lz78GreedyImpl_achievability_ae` = `@residual(wall:lz78-aseventual-ziv)`
     (M3 variable-depth tree-node AEP)。
   - いずれも符号データ (`μ`, `p`) のみを取る genuine 命題 (load-bearing hyp なし)。
     ダミー parse 時代の converse=false-statement / achievability=degenerate defect
     は def-fix で解消 (commit `caba26c` で旧 defect タグ済、その後 def-fix で消滅)。
3. **`h_bdd_above` = 小さい open precondition**。headline は rate の
   `IsBoundedUnder (·≤·)` を仮説で取る。def-fix で **TRUE-satisfiable な honest
   regularity 仮説** (rate `O(1)`、core-reconstruction test PASS = limit 値 entropyRate
   の情報を運ばないので load-bearing でない)。ただし discharge には `Nat.log↔Real.log`
   bridge が要り、これが loogle Found 0 で self-build 要 → honest に open
   (`docs/shannon/lz78-headline-bdd-discharge-plan.md`)。
4. **完遂条件 = headline sorryAx-free** (M3 + M4 discharge + `h_bdd_above` 内製化)。

### genuine 済の足場 (sorryAx 非依存・commit 済)

| 層 | file | 内容 |
|---|---|---|
| 符号長 + parent bridge | `GreedyParsingImpl.lean` §1-§2 | genuine longest-prefix 符号長 + CT 13.5.2 bit-length 上界 (`c ≤ n` × `bitLength` 単調)、per-symbol rate 上界・非負 |
| Ziv 組合せ核 | `ZivCountingBody.lean` §4 | `lz78PhraseStrings_mul_log_le` (`c·log c ≤ K·n`)、`lz78PhraseStrings_count_isBigO` (`c = O(n/log n)`) |
| base-2 単位 | `LZ78ZivEntropyBridge.lean` | `entropyRate₂ = entropyRate / Real.log 2`, `blockLogAvg₂` (lz=bit / entropy=nat 単位整合) |
| tree-node 基盤 | `LZ78ZivTreeNode.lean` | T3 `node_logsum_step` (`∑_v k_v log k_v ≤ -log Q_c^{tree}`) 他 (M3 入力) |
| converse UD-object (M1 済) | `LZ78ConverseUDObject.lean` | 汎用 `uniquelyDecodable_of_constantLength` + 実 LZ78 token code UD → McMillan 期待値 converse `entropyD 2 P ≤ E[L]=K` (M4 入力) |
| 固定深さ k AEP (再利用元) | `SMBAlgoetCover.lean` / `EntropyRate.lean` | `negLogQk_div_tendsto_condEntropyTail` (`-log qk/n → H_k`)、`conditionalEntropyTail_tendsto_entropyRate` (`H_k → H`) (M3 入力) |

### 旧 Phase 履歴 (圧縮)
- 旧 `IsLZ78*` load-bearing 仮説路 (`IsLZ78ZivAsEventual` / `IsLZ78ConverseCodingLowerBound`
  / passthrough predicate 3本) は def-fix + dead scaffolding 削除 (commit `602b1ad`)
  で消滅、現在の SoT は `GreedyParsingImpl.lean` の wall sorry lemma 2本。
- 旧 FALSE per-block `IsLZ78ZivCombinatorialCore` (反例 `a^16`) は撤回済 (§2 D1/D2)。

---

## 1. 残る4部品 + 推奨着手順 (tractable 順)

### M1 — converse UD-object 【✅ 済 (2026-05-21)】
- **内容**: LZ78 符号化 (index, symbol) ストリームを定義し、**uniquely-decodable であることを証明** → Mathlib McMillan (`McMillanKraftBridge`) を**実 LZ78 code に適用** → 実コードの**期待値 converse `H_D ≤ E[lz]`** を genuine に。
- **注意**: `lz78PhraseStrings` 自体は **prefix-complete で UD でない**。真の UD object は encoded stream (別構造、新規構築要)。`_nodup` は UD の必要条件にすぎず不十分。
- **deliverable (実装済)**: `InformationTheory/Shannon/LZ78ConverseUDObject.lean` (sorryAx 非依存、`lake env lean` silent)。
  - `uniquelyDecodable_of_constantLength` — 定長コード ⟹ UD (汎用、Mathlib 未収録、本 M1 の数学的核)。
  - `boolEncode`/`finBoolCode` — fixed-width binary code、`m < 2^K` で injective。
  - `lz78TokenCode c : Fin (c+1) × α → List Bool` (width `K = bitLength c |α|`) の injective + UD + `lz78TokenCode_kraftSum_le_one` + `lz78TokenCode_entropyD_le_expectedLength` (= `entropyD 2 P ≤ E[L] = K`)。
  - McMillanKraftBridge §3 Residual 1 (「UD object 未構築」) を解消。
- **残**: `IsLZ78ConverseCodingLowerBound` (block-rate, Cover–Thomas Eq. 13.130) は **未着手のまま** — token-level Kraft → block-rate a.s.-eventual `liminf` は **averaged⟶a.s. lift (= M4)** が必要。M1 は converse の**期待値層を実コードに接続**した段階。
- **規模 (実績)**: ~270 行。**リスク: 低〜中 (組合せ的)** — 想定通り、初回 skeleton がほぼそのまま通過。

### M2 — length-grouping Ziv 組合せ核 【確度高】
- **内容**: tree-node T3 (`∑_v k_v log k_v ≤ -log Q_c^{tree}`) を **長さ別グルーピング**で `c·log c ≤ -log Q_c^{tree} + c·H(length-dist)` に。overhead `c·H(length-dist) ≤ c·log(maxlen)`、`maxlen ≤ log_b n`、`(c·log log n)/n → 0` を `c/n` envelope (`lz78Distinct_count_div_le_envelope`) と合成。
- **deliverable**: achievability の**組合せ部分** (非エルゴード) の genuine 不等式。これで残るは M3 のエルゴード一点に。
- **規模**: ~200–400 行。**リスク: 中** (正確な overhead 形・maxlen bound)。**必ず length-grouping で** (node-grouping は §2 D3 で偽)。

### M3 — 可変depth tree-node AEP 【支配項・要・腰据え】
- **内容**: `-log₂ Q_c^{tree}(x^n)/n → H` a.s. を、固定深さ k AEP (`negLogQk_div_tendsto_condEntropyTail`, SMB 内) + `H_k → H` を **k↔n 連動の対角線/カットオフ論法** (CT 13.5.3 核心) で繋ぐ。`birkhoffAverage` (固定 f Cesàro) は直接効かない。
- **deliverable**: M2 と合成して `lz78GreedyImpl_achievability_ae` (`@residual(wall:lz78-aseventual-ziv)`、`GreedyParsingImpl.lean`) の sorry を discharge → **achievability 完遂**。
- **規模**: ~600–1200 行。**リスク: 高**。対角線論法に **Mathlib 測度論基盤の新規追加 (upstream 級)** が要る可能性 — 最大の不確実要因。route C (k-Markov sandwich) の誤差項 `δ_k(n)/n→0` の ω-uniform 性が crux (要・最初の手計算 gate)。

### M4 — converse Barron a.s. lift 【要・腰据え】
- **内容**: M1 の期待値 converse `H_D ≤ E[lz]` を **a.s.-eventual pointwise `liminf lz/n ≥ entropyRate₂`** に持ち上げる (competitive-optimality / Barron 型エルゴード論法)。LZ78 は pointwise で Shannon code を破れるので **期待値↛pointwise**。
- **deliverable**: `lz78GreedyImpl_converse_ae` (`@residual(wall:lz78-converse-aseventual)`、`GreedyParsingImpl.lean`) の sorry を discharge → **converse 完遂**。
- **規模**: ~300–700 行。**リスク: 高** (a.s. エルゴード)。

### M5 — 最終合成 + 完遂判定 【capstone】
- **内容**: M3 + M4 で両 wall sorry lemma discharge + `h_bdd_above` を内製 (`Nat.log↔Real.log` bridge self-build、`lz78-headline-bdd-discharge-plan.md`) → headline `lz78_asymptotic_optimality_with_greedy_impl` を無条件化、`#print axioms = [propext, Classical.choice, Quot.sound]` (sorryAx 非依存) 確認 = 標準B 完遂。
- **規模**: ~100–200 行 (配線 + bridge)。**リスク: 低** (M3/M4 が閉じれば)。

---

## 2. 既知の地雷 (machine-disproof / 確定済み — 再探索禁止)

- **D1**: per-block `c·log c ≤ -log Pₙ` (∀n∀ω, clean) は **FALSE**。反例 constant process `a^16` (c=5, `-log Pₙ=0`)。
- **D2**: overhead 版 `c·log c ≤ -log Pₙ + c·log(\|α\|+1)` も **FALSE** (`Pₙ→1` family)。machine-disproof `not_isLZ78ZivCombinatorialCoreOverhead` (`LZ78ZivTreeBridge.lean`)。**per-block universal Ziv は誤った formulation** — genuine は a.s.-eventual のみ。
- **D3**: node-grouping overhead `(c·log D)/n` は D≈c で**定数収束 (vanish しない)**。**正しいのは length-grouping** (overhead が `c·log(maxlen)`, support が指数的に小さく vanish)。`log D=log c` を `log(n/c)≈log log n` と取り違えない。
- **D4**: path-prefix `Q_c = ∏ condPhraseProb` の AEP は genuine (M0 で trivial と判明) **だが achievability に繋がらない** (`∑ⱼqⱼ≈c` の罠)。tree-node `Q_c^{tree}` (M3) が必要。
- **D5**: McMillan は **Mathlib 既存** (`InformationTheory.kraft_mcmillan_inequality`)。再発明不要、wire 済 (M1 で使う)。
- **D6**: converse の pointwise `2^{-lz} ≤ Pₙ` 経路は**不健全** (Shannon-code 補題、`lz ≥ shannonLength` は pointwise 偽 = LZ78 universality の核心)。M4 は期待値→a.s. lift で。
- **D7**: Huffman 系の `mergedMeasure` 偽 core 等は別件 (本 roadmap 対象外、textbook-roadmap 判断ログ #6 + `huffman-fullB-structure-plan.md` 参照)。

---

## 3. 校正・規模・リスク総括

- **校正**: 既存 SMB (`SMBAlgoetCover.lean`) = 約 2800 行。M3/M4 のエルゴード持ち上げは各々 SMB の一部分〜同等規模。直感: **「LZ78 完遂 ≈ もう一本 SMB を建てる」**。
- **総計**: おおよそ **~1300–2600 行** (桁感、構造を固めるまで上振れ得る)。
- **数学的位置づけ**: LZ78 最適性は**標準教科書定理 (深い/未解決ではない)**。難しさの大半は「**既知だが Mathlib に無いエルゴード定理を一から建てる**」基盤コスト + 「形式化が容赦なく教科書の手抜きを露呈する」層。`/goal` 反復では届かず、**腰を据えた数学的形式化**が要る。
- **進め方の推奨**: **M1 → M2** をまず確実に閉じて足場を固める (低〜中リスク、組合せ的)。**M3 → M4** はそれぞれ独立した dedicated セッションで (高リスク、エルゴード、各々 M0 feasibility gate 先行推奨)。M3 着手時はまず対角線/sandwich 誤差項の手計算 gate で go/no-go を取る。

---

## 4. cross-link
- main: `docs/textbook-roadmap.md` 判断ログ #6 (現行サマリ、~35 エージェントの経緯・全 disproof・honest frontier の記録は `git log -- docs/textbook-roadmap.md` の 2026-05-26 整理前 commit に旧 #17–#26 として残置)
- 既存 plan (本 roadmap が incremental master として統合): `lz78-completion-plan.md`, `lz78-treeinduced-aep-plan.md`, `lz78-aseventual-achievability-plan.md`, `lz78-ziv-treenode-plan.md`, `lz78-blockrv-refactor-plan.md` + `-inventory.md`
- 完遂判定: `GreedyParsingImpl.lean` の wall sorry lemma 2本 (M3/M4) が discharge され + `h_bdd_above` が内製化され、headline `lz78_asymptotic_optimality_with_greedy_impl` が `#print axioms` で sorryAx 非依存になった時点 = 標準B 完遂。

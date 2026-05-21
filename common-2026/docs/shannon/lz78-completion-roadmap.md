# LZ78 漸近最適性 完遂ロードマップ (incremental)

> 派生元: `docs/textbook-roadmap.md` 判断ログ #17–#26。
> 目的: **T4-A LZ78 (Cover–Thomas Thm 13.5.3) を標準B (無条件機械検証) で完遂**。
> 方針: `/goal` 一発完遂ループではなく、**各マイルストーンが genuine・committable・verifiable な単独 deliverable** となる少しずつ確実な進行。M1→M5 の順で、前段が次段の足場になる。

主定理: stationary ergodic source に対し圧縮率 `(1/n)·lz(X^n) → H` (base-2 entropy rate) a.s.

---

## 0. 現状 (2026-05-21、~35 エージェントの徹底診断後に確定)

### genuine 済 (全て sorryAx 非依存・commit 済・`lake build` clean)
| 層 | file | 内容 |
|---|---|---|
| base-2 単位 | `LZ78ZivEntropyBridge.lean` | `entropyRate₂ = entropyRate / Real.log 2`, `blockLogAvg₂`。lz=bit / entropy=nat の単位バグ訂正 (= CT 13.5.3 の真 statement) |
| telescoping | `StationaryKernel.lean` | `prod_condPhraseProb_telescope`, `blockProb_le_prod_condPhraseProb` (`Pₙ ≤ ∏ⱼ qⱼ`, prefix monotonicity で無条件) |
| tree-node 基盤 | `LZ78ZivTreeNode.lean` | T1 worker 不変 `lz78PhraseStringsAux_emit_context_mem` / T2 per-node sub-dist `condNode_sum_eq_one` (`∑_s q(node·s\|node) ≤ 1`) / T3 `node_logsum_step` (`∑_v k_v log k_v ≤ -log Q_c^{tree}`) |
| path-prefix AEP | `LZ78TreeInducedAEP.lean` | `treeInducedProb_negLogb_div_limsup_le_entropyRate₂` (`Pₙ≤Q_c`+SMB)。**genuine だが achievability に直接効かない** (§2 D4) |
| achievability frontier | `LZ78AsEventualAchievability.lean` | envelope reduction `lz78DistinctRate_le_countLogRate₂_add_slack` (**FALSE core 非依存**) + satisfiable hyp `IsLZ78ZivAsEventual` + headline `lz78_two_sided_optimality_distinct_aseventual` |
| converse 期待値層 | `McMillanKraftBridge.lean` | `entropyD_le_expectedLength_of_uniquelyDecodable` (Mathlib `InformationTheory.kraft_mcmillan_inequality` を project Kraft/Gibbs に wire) |
| **converse UD-object (M1 済)** | `LZ78ConverseUDObject.lean` | 汎用 `uniquelyDecodable_of_constantLength` (定長コード⟹UD、Mathlib 未収録) + 実 LZ78 `(parent,symbol)` token code (fixed-width `K=bitLength c \|α\|`, `(c+1)·\|α\| ≤ 2^K`) の UD 証明 → McMillan で `kraftSum 2 (fun _=>K) ≤ 1` + 期待値 converse `entropyD 2 P ≤ E[L]=K`。`#print axioms` sorryAx 非依存 |
| 固定深さ k AEP (再利用元) | `SMBAlgoetCover.lean` | `qkSingleton`, `sum_qkSingleton_le_one`, `negLogQk_div_tendsto_condEntropyTail` (`-log qk/n → H_k`); `EntropyRate.lean` `conditionalEntropyTail_tendsto_entropyRate` (`H_k → H`) |

### honest frontier (= 残る load-bearing 仮説、これらを discharge すれば完遂)
- **achievability**: `IsLZ78ZivAsEventual` (satisfiable, a.s.-eventual `limsup (c·log₂c)/n ≤ entropyRate₂`)。
- **converse**: `IsLZ78ConverseCodingLowerBound` (a.s.-eventual `liminf ... ≥ ...`)。

---

## 1. 残る4部品 + 推奨着手順 (tractable 順)

### M1 — converse UD-object 【✅ 済 (2026-05-21)】
- **内容**: LZ78 符号化 (index, symbol) ストリームを定義し、**uniquely-decodable であることを証明** → Mathlib McMillan (`McMillanKraftBridge`) を**実 LZ78 code に適用** → 実コードの**期待値 converse `H_D ≤ E[lz]`** を genuine に。
- **注意**: `lz78PhraseStrings` 自体は **prefix-complete で UD でない**。真の UD object は encoded stream (別構造、新規構築要)。`_nodup` は UD の必要条件にすぎず不十分。
- **deliverable (実装済)**: `Common2026/Shannon/LZ78ConverseUDObject.lean` (sorryAx 非依存、`lake env lean` silent)。
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
- **deliverable**: M2 と合成して `IsLZ78ZivAsEventual` を discharge → **achievability 完遂**。
- **規模**: ~600–1200 行。**リスク: 高**。対角線論法に **Mathlib 測度論基盤の新規追加 (upstream 級)** が要る可能性 — 最大の不確実要因。route C (k-Markov sandwich) の誤差項 `δ_k(n)/n→0` の ω-uniform 性が crux (要・最初の手計算 gate)。

### M4 — converse Barron a.s. lift 【要・腰据え】
- **内容**: M1 の期待値 converse `H_D ≤ E[lz]` を **a.s.-eventual pointwise `liminf lz/n ≥ entropyRate₂`** に持ち上げる (competitive-optimality / Barron 型エルゴード論法)。LZ78 は pointwise で Shannon code を破れるので **期待値↛pointwise**。
- **deliverable**: `IsLZ78ConverseCodingLowerBound` を discharge → **converse 完遂**。
- **規模**: ~300–700 行。**リスク: 高** (a.s. エルゴード)。

### M5 — 最終合成 【capstone】
- **内容**: M3 + M4 で両 primitive discharge → 無引数 base-2 LZ78 optimality を publish、`#print axioms = [propext, Classical.choice, Quot.sound]` 確認。
- **規模**: ~100–200 行 (配線)。**リスク: 低** (M3/M4 が閉じれば)。

---

## 2. 既知の地雷 (machine-disproof / 確定済み — 再探索禁止)

- **D1**: per-block `c·log c ≤ -log Pₙ` (∀n∀ω, clean) は **FALSE**。反例 constant process `a^16` (c=5, `-log Pₙ=0`)。
- **D2**: overhead 版 `c·log c ≤ -log Pₙ + c·log(\|α\|+1)` も **FALSE** (`Pₙ→1` family)。machine-disproof `not_isLZ78ZivCombinatorialCoreOverhead` (`LZ78ZivTreeBridge.lean`)。**per-block universal Ziv は誤った formulation** — genuine は a.s.-eventual のみ。
- **D3**: node-grouping overhead `(c·log D)/n` は D≈c で**定数収束 (vanish しない)**。**正しいのは length-grouping** (overhead が `c·log(maxlen)`, support が指数的に小さく vanish)。`log D=log c` を `log(n/c)≈log log n` と取り違えない。
- **D4**: path-prefix `Q_c = ∏ condPhraseProb` の AEP は genuine (M0 で trivial と判明) **だが achievability に繋がらない** (`∑ⱼqⱼ≈c` の罠)。tree-node `Q_c^{tree}` (M3) が必要。
- **D5**: McMillan は **Mathlib 既存** (`InformationTheory.kraft_mcmillan_inequality`)。再発明不要、wire 済 (M1 で使う)。
- **D6**: converse の pointwise `2^{-lz} ≤ Pₙ` 経路は**不健全** (Shannon-code 補題、`lz ≥ shannonLength` は pointwise 偽 = LZ78 universality の核心)。M4 は期待値→a.s. lift で。
- **D7**: Huffman 系の `mergedMeasure` 偽 core 等は別件 (本 roadmap 対象外、textbook-roadmap #19/#20 参照)。

---

## 3. 校正・規模・リスク総括

- **校正**: 既存 SMB (`SMBAlgoetCover.lean`) = 約 2800 行。M3/M4 のエルゴード持ち上げは各々 SMB の一部分〜同等規模。直感: **「LZ78 完遂 ≈ もう一本 SMB を建てる」**。
- **総計**: おおよそ **~1300–2600 行** (桁感、構造を固めるまで上振れ得る)。
- **数学的位置づけ**: LZ78 最適性は**標準教科書定理 (深い/未解決ではない)**。難しさの大半は「**既知だが Mathlib に無いエルゴード定理を一から建てる**」基盤コスト + 「形式化が容赦なく教科書の手抜きを露呈する」層。`/goal` 反復では届かず、**腰を据えた数学的形式化**が要る。
- **進め方の推奨**: **M1 → M2** をまず確実に閉じて足場を固める (低〜中リスク、組合せ的)。**M3 → M4** はそれぞれ独立した dedicated セッションで (高リスク、エルゴード、各々 M0 feasibility gate 先行推奨)。M3 着手時はまず対角線/sandwich 誤差項の手計算 gate で go/no-go を取る。

---

## 4. cross-link
- main: `docs/textbook-roadmap.md` 判断ログ #17–#26 (経緯・全 disproof・honest frontier の記録)
- 既存 plan (本 roadmap が incremental master として統合): `lz78-completion-plan.md`, `lz78-treeinduced-aep-plan.md`, `lz78-aseventual-achievability-plan.md`, `lz78-ziv-treenode-plan.md`, `lz78-blockrv-refactor-plan.md` + `-inventory.md`
- 完遂判定: 全 `IsLZ78*` 仮説が discharge され、headline が `#print axioms` で sorryAx 非依存になった時点 = 標準B 完遂。

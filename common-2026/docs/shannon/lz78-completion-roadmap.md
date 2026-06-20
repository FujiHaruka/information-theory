# LZ78 漸近最適性 完遂ロードマップ (incremental)

> 派生元: `docs/textbook-roadmap.md` 判断ログ #6 (詳細経緯は `git log -- docs/textbook-roadmap.md` の 2026-05-26 ロードマップ整理前 commit、特に旧 #17–#26 の Huffman/LZ78 grind 履歴)。
> 目的: **T4-A LZ78 (Cover–Thomas Thm 13.5.3) を標準B (無条件機械検証) で完遂**。
> 方針: `/goal` 一発完遂ループではなく、**各マイルストーンが genuine・committable・verifiable な単独 deliverable** となる少しずつ確実な進行。M1→M5 の順で、前段が次段の足場になる。

主定理: stationary ergodic source に対し圧縮率 `(1/n)·lz(X^n) → H` (base-2 entropy rate) a.s.

---

## 0. 現状 (2026-06-20、符号長 def-fix + units-mismatch fix 後)

**headline は type-check done であって proof done でない。** entry_point
`lz78_asymptotic_optimality_with_greedy_impl`
(`InformationTheory/Shannon/LZ78/GreedyParsingImpl.lean`) は genuine 命題で、
仮説引数は `μ`, `p` のみ。`#print axioms` の sorryAx 依存は genuine M3/M4 壁 2本
経由のみ (`h_bdd_above` は内製 discharge 済 = 引数から除去、commit `a1ae108`)。
**headline + 2壁の target は base-2 (bit) entropy rate `entropyRate₂` であって
nat 単位の `entropyRate` ではない** (units-mismatch defect 修正後、下記確定事実)。
SoT はコード側タグ (`@residual(wall:...)`)、本節は二次。

### 確定事実 (符号長 def-fix `5d08566` → units-mismatch fix `55e1cd9`)

1. **符号長 = genuine longest-prefix parse 化済**。`lz78GreedyImplEncodingLength n x`
   = genuine distinct phrase count `c = (lz78PhraseStrings (List.ofFn x)).length` を
   語数とする `c · bitLength c |α|`。以前のダミー1シンボル parse (count=n, rate 発散)
   は削除済。`c ≤ n`、genuine Ziv `c·log c ≤ K·n` (`lz78PhraseStrings_mul_log_le`、
   sorryAx-free) で rate は `O(1)`。符号長は **base-2 code** (`bitLength = Nat.log 2 …`)
   ゆえ per-symbol rate `lz78GreedyImplEncodingLength/n` は **bit 単位**。
2. **bit-vs-nat units defect を発見・`entropyRate₂` 化で修正** (commit `55e1cd9`、
   再監査 PASS)。符号長 def-fix 後、独立監査が **second defect = bit-vs-nat units
   mismatch** を発覚: `lz78GreedyImplEncodingLength/n` は bit-rate だが、headline +
   2壁の sandwich target が nat 単位の `entropyRate` のままで、正entropy源 A≥2 では
   `limsup = log₂A > logA` = **false-statement** (prior audit `9b09790` はこの units
   ずれを見落とし overturn された)。`99acb58` で `@audit:defect(false-statement)`
   確定 → `55e1cd9` で headline + 2壁の target を `entropyRate₂ = entropyRate/Real.log 2`
   (bit) に置換し TRUE-as-framed に修正、再監査 PASS。**sandwich target は `entropyRate₂`**
   で、`lz78GreedyImplEncodingLength/n` (bit) の真の極限 (`A=2` で `→ 1` 等) と整合する。
3. **2 headline sorry = genuine M3/M4 壁** (`GreedyParsingImpl.lean §3`、target =
   `entropyRate₂`):
   - `lz78GreedyImpl_converse_ae` (`entropyRate₂ ≤ liminf (lz/n)`)
     = `@residual(wall:lz78-converse-aseventual)` (M4 Barron a.s. lift)。
   - `lz78GreedyImpl_achievability_ae` (`limsup (lz/n) ≤ entropyRate₂`)
     = `@residual(wall:lz78-aseventual-ziv)` (M3 variable-depth tree-node AEP)。
   - いずれも符号データ (`μ`, `p`) のみを取る genuine 命題 (load-bearing hyp なし)。
     `entropyRate₂` target で **TRUE-as-framed** (units fix で TRUE 化しただけで
     discharge ではない、a.s.-eventual Ziv/converse 内容は未証明)。ダミー parse 時代の
     defect は def-fix で、bit-vs-nat units defect は `entropyRate₂` 化で解消済。
4. **M3 framing 訂正 (leg 3、2026-06-20、commit `7171707`)**: r2 realign が「可変深さ
   AEP は SMB で蒸発」と書いたのは **source entropy limit (`-log₂Pₙ/n → H₂`) と LZ 固有の
   combinatorial→conditional 橋 (`c·log₂c ≤ ∑ⱼ -log₂qⱼ + o(n)`、可変深さ tree-node AEP)
   の混同による過小評価** だった。SMB が蒸発させたのは source-limit のみで、橋は genuine に
   残る (gateway-atom-first probe で machine-disproof)。gateway (単位整合) は **plumbing で
   closed** (`lz78_impl_bitrate_le_clogc_plus_overhead`、sorryAx-free)、残る genuine 核 =
   可変深さ tree-node AEP は **research-level self-build** (旧 treenode plan T1-T5 路、§3 + §1 M3)。
   壁 `wall:lz78-aseventual-ziv` は不変 (over-estimate でなく under-estimate 側 = plumbing 誤認を是正)。
5. **`h_bdd_above` = 内製 discharge 済** (commit `a1ae108`、独立監査 all OK)。
   rate の `IsBoundedUnder (·≤·)` witness を proof body 内の `have` で構成し、
   **headline の仮説引数から除去した** (引数は `μ`, `p` のみ)。`O(1)` per-symbol
   rate 上界 `lz78_impl_rate_le_const` (sorryAx-free) を内製。当初 self-build 要と
   見ていた `Nat.log↔Real.log` bridge は Mathlib 既存 `Real.natLog_le_logb` で
   解決 (loogle Found 0 は誤判定、`docs/shannon/lz78-headline-bdd-discharge-plan.md`)。
6. **完遂条件 = headline sorryAx-free** (M3 + M4 discharge で達成)。

### genuine 済の足場 (sorryAx 非依存・commit 済)

| 層 | file | 内容 |
|---|---|---|
| 符号長 + parent bridge | `GreedyParsingImpl.lean` §1-§2 | genuine longest-prefix 符号長 + CT 13.5.2 bit-length 上界 (`c ≤ n` × `bitLength` 単調)、per-symbol rate 上界・非負 |
| Ziv 組合せ核 | `ZivCountingBody.lean` §4 | `lz78PhraseStrings_mul_log_le` (`c·log c ≤ K·n`)、`lz78PhraseStrings_count_isBigO` (`c = O(n/log n)`) |
| base-2 単位 | `EntropyRate.lean` + `LZ78/ZivEntropyBridge.lean` | `entropyRate₂ = entropyRate / Real.log 2` を `EntropyRate.lean` に `@[entry_point]` def 化 (units fix `55e1cd9` で旧 prose のみ → 実 def 化、headline + 2壁の target)。`ZivEntropyBridge.lean` は `blockLogAvg₂ = blockLogAvg / log 2` 等の unit-conversion prose (lz=bit / entropy=nat 単位整合) |
| 無条件 SMB AEP (M3 限界供給) | `SMB/AlgoetCover/Liminf.lean` | `shannon_mcmillan_breiman` (`∀ᵐ ω, blockLogAvg μ p n ω → entropyRate μ p`、sorry-free entry_point)。M3 の **新たな限界対象** — `-log₂Pₙ/n → H₂` を free で供給 (旧 tree-node 基盤を obsolete 化、§3 校正参照) |
| converse UD-object (M1 済) | `LZ78/ConverseUDObject.lean` | 汎用 `uniquelyDecodable_of_constantLength` + 実 LZ78 token code UD → McMillan 期待値 converse `entropyD 2 P ≤ E[L]=K` (M4 入力) |
| 固定深さ k AEP (SMB 内部足場) | `SMB/AlgoetCover/Core.lean` / `EntropyRate.lean` | `negLogQk_div_tendsto_condEntropyTail` (`-log qk/n → H_k`)、`conditionalEntropyTail_tendsto_entropyRate` (`H_k → H`)。`shannon_mcmillan_breiman` の内部足場 (M3 が直接持ち上げる必要は無くなった) |

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
- **deliverable (実装済)**: `InformationTheory/Shannon/LZ78/ConverseUDObject.lean` (sorryAx 非依存、`lake env lean` silent)。
  - `uniquelyDecodable_of_constantLength` — 定長コード ⟹ UD (汎用、Mathlib 未収録、本 M1 の数学的核)。
  - `boolEncode`/`finBoolCode` — fixed-width binary code、`m < 2^K` で injective。
  - `lz78TokenCode c : Fin (c+1) × α → List Bool` (width `K = bitLength c |α|`) の injective + UD + `lz78TokenCode_kraftSum_le_one` + `lz78TokenCode_entropyD_le_expectedLength` (= `entropyD 2 P ≤ E[L] = K`)。
  - McMillanKraftBridge §3 Residual 1 (「UD object 未構築」) を解消。
- **残**: `IsLZ78ConverseCodingLowerBound` (block-rate, Cover–Thomas Eq. 13.130) は **未着手のまま** — token-level Kraft → block-rate a.s.-eventual `liminf` は **averaged⟶a.s. lift (= M4)** が必要。M1 は converse の**期待値層を実コードに接続**した段階。
- **規模 (実績)**: ~270 行。**リスク: 低〜中 (組合せ的)** — 想定通り、初回 skeleton がほぼそのまま通過。

### M2 — length-grouping Ziv 組合せ核 【確度高】
- **内容**: distinct-phrase log-sum を **長さ別グルーピング** (D3: node-grouping は偽、必ず length-grouping) で `c·log c ≤ -log Pₙ + c·H(length-dist)` に。overhead `c·H(length-dist) ≤ c·log(maxlen)`、`maxlen ≤ log_b n`、`(c·log log n)/n → 0` を `c/n` envelope (`lz78Distinct_count_div_le_envelope`) と合成。**M3 framing realign 後はこの組合せ不等式が a.s.-eventual Ziv 核そのもの** — 旧 `Q_c^{tree}` tree-node T3 は obsolete (実 decl 不在)、`-log Pₙ` (= SMB が握る `blockLogAvg₂`) を直接 RHS に置く。
- **deliverable**: achievability の**組合せ部分** (非エルゴード) の genuine a.s.-eventual 不等式。これを既証明 SMB に乗せる接続が M3。
- **規模**: ~200–400 行。**リスク: 中** (正確な overhead 形・maxlen bound)。**必ず length-grouping で** (node-grouping は §2 D3 で偽)。

### M3 — a.s.-eventual Ziv 不等式を既証明 SMB に乗せる 【支配項・要・腰据え】
> **2026-06-20 framing realign (r2)**: 旧 framing の **エルゴード対角線持ち上げ**
> (固定深さ k AEP `negLogQk_div_…` からの k↔n 連動 対角線/カットオフ) は **obsolete** —
> 無条件・sorry-free な Shannon–McMillan–Breiman AEP `shannon_mcmillan_breiman`
> (`SMB/AlgoetCover/Liminf.lean`、`∀ᵐ ω, blockLogAvg μ p n ω → entropyRate μ p`)
> が `-log₂Pₙ/n → H₂` を free で供給するため。
>
> **ただし r2 realign は過小評価だった (2026-06-20 leg 3 で machine-disproof)**:
> SMB が蒸発させたのは **source entropy limit** (`-log₂Pₙ/n → H₂`、
> `blockLogAvg₂ → entropyRate₂`) **だけ**。LZ 固有の **combinatorial→conditional 橋**
> `c·log₂c ≤ ∑ⱼ -log₂qⱼ + o(n)` (= 可変深さ tree-node AEP、`∑qⱼ≈c` の D4 trap を含む)
> は **蒸発していない** — gateway (Phase 1、closed) と SMB の **間** に genuine に残る。
> r2 が「可変深さ AEP 持ち上げ sub-problem は SMB 完成で蒸発した」と書いたのは
> **source-limit と combinatorial-bridge の混同** (§3 校正・判断ログ #1 参照)。
- **genuine な残ギャップ (leg 3 で pinpoint)**: **a.s.-eventual な Ziv 不等式**
  `c·log₂c ≤ -log₂Pₙ + o(n)` のうち、**combinatorial→conditional 橋**
  `c·log₂c ≤ ∑ⱼ -log₂qⱼ + o(n)` (可変深さ tree-node AEP) が **single in-session plan
  では閉じない genuine research-level scope**。leg 3 gateway-atom-first probe
  (commit `7171707`) の決定的判定: Phase 2b の直接 `-log Pₙ` route も `∑qⱼ` route と
  **同じ** genuine AEP で塞がれ、可変深さ tree-node AEP に shortcut は無い。
  接続後は `-log₂Pₙ/n = blockLogAvg₂ → H₂ = entropyRate₂` (`shannon_mcmillan_breiman`、
  済) で `limsup (c·log₂c)/n ≤ entropyRate₂` (= 壁補題 `lz78GreedyImpl_achievability_ae`
  の RHS) に乗る。**gateway (単位整合) は plumbing で closed** (`lz78_impl_bitrate_le_clogc_plus_overhead`、
  sorryAx-free)、**残る genuine 核は combinatorial→conditional 橋のみ**。
- **refutation (leg 3、mandated)**: sorryAx-free 組合せ核
  `c·log c ≤ 8·log(|α|+1)·n` (`lz78PhraseStrings_mul_log_le`) は **constant** limsup
  `≤ 8·log(|α|+1)/log 2` しか出さず、低エントロピー源で `entropyRate₂` を超過 = genuine
  に不十分。壁確定 (plumbing でない、単一 combinatorial bound では届かない)。
- **D1/D2 (§2) との整合 — 真の難所**: この Ziv 不等式は **a.s.-eventual / limsup 形で
  なければならない**。per-block universal な clean 形 (`c·log c ≤ -log Pₙ` ∀n∀ω、D1)
  も overhead 形 (D2) も **machine-disproof で FALSE** (反例 `a^16`)。genuine な
  statement は a.s.-eventual のみ。crux は **可変深さ tree-node AEP** (各深さで
  conditional 積 `∏qⱼ` を取り `c·log c` に下から押さえる) であって、`shannon_mcmillan_breiman`
  が握る source-limit ではない。
- **攻略 path**: 旧 `lz78-ziv-treenode-plan.md` の T1-T5 (tree-node sub-distribution →
  per-node 条件付き積 → `c log c ≤ ∑ -log q` log-sum → telescoping → `-log Pₙ` 接続) が
  **obsolete でなく genuine な攻略 path** (ただし末尾で SMB に接続する点だけ r2 realign 後の形)。
- **deliverable**: M2 (a.s.-eventual Ziv 組合せ) と合成して `lz78GreedyImpl_achievability_ae`
  (`@residual(wall:lz78-aseventual-ziv)`、`GreedyParsingImpl.lean`) の sorry を
  discharge → **achievability 完遂**。
- **規模/リスク**: gateway (単位整合) は plumbing で **closed**。残る genuine 核 =
  可変深さ tree-node AEP `c·log₂c ≤ ∑ⱼ -log₂qⱼ + o(n)` は **research-level self-build**
  (旧 treenode plan T1-T5 路、**~数 leg**)。**feared upstream ergodic addition は不要**
  (source-limit 次元は SMB が握る) だが、combinatorial→conditional 橋は単一 in-session plan
  で閉じない genuine scope。`wall:lz78-aseventual-ziv` は正しい genuine 壁 (leg 3 で
  over-estimate でなく **under-estimate 側 = plumbing 誤認** が判明 = 是正済)。

### M4 — converse Barron a.s. lift 【要・腰据え】
- **内容**: M1 の期待値 converse `H_D ≤ E[lz]` を **a.s.-eventual pointwise `liminf lz/n ≥ entropyRate₂`** に持ち上げる (competitive-optimality / Barron 型エルゴード論法)。LZ78 は pointwise で Shannon code を破れるので **期待値↛pointwise**。
- **deliverable**: `lz78GreedyImpl_converse_ae` (`@residual(wall:lz78-converse-aseventual)`、`GreedyParsingImpl.lean`) の sorry を discharge → **converse 完遂**。
- **規模**: ~300–700 行。**リスク: 高** (a.s. エルゴード)。

### M5 — 最終合成 + 完遂判定 【capstone】
- **内容**: M3 + M4 で両 wall sorry lemma discharge → headline `lz78_asymptotic_optimality_with_greedy_impl` を無条件化、`#print axioms = [propext, Classical.choice, Quot.sound]` (sorryAx 非依存) 確認 = 標準B 完遂。`h_bdd_above` 内製化は済 (commit `a1ae108`、`lz78-headline-bdd-discharge-plan.md` ✅ CLOSED)、もう完遂条件ではない。
- **規模**: ~50–100 行 (配線のみ)。**リスク: 低** (M3/M4 が閉じれば)。

---

## 2. 既知の地雷 (machine-disproof / 確定済み — 再探索禁止)

- **D1**: per-block `c·log c ≤ -log Pₙ` (∀n∀ω, clean) は **FALSE**。反例 constant process `a^16` (c=5, `-log Pₙ=0`)。
- **D2**: overhead 版 `c·log c ≤ -log Pₙ + c·log(\|α\|+1)` も **FALSE** (`Pₙ→1` family)。当初 machine-disproof `not_isLZ78ZivCombinatorialCoreOverhead` で裏取り済 (反例 `n=16, Pₙ=1, c=5`)。**verdict は不変** だが、その refutation decl + 旧 FALSE predicate は def-fix cleanup (§0 旧 Phase 履歴、commit `602b1ad` 系) で in-tree 削除済 (現在 codebase 不在)。**per-block universal Ziv は誤った formulation** — genuine は a.s.-eventual のみ。**D1/D2 の per-block 偽性ゆえ M3 の Ziv 不等式は a.s.-eventual / limsup 形でなければならない** (§1 M3 realign 参照)。
- **D3**: node-grouping overhead `(c·log D)/n` は D≈c で**定数収束 (vanish しない)**。**正しいのは length-grouping** (overhead が `c·log(maxlen)`, support が指数的に小さく vanish)。`log D=log c` を `log(n/c)≈log log n` と取り違えない。
- **D4**: path-prefix `Q_c = ∏ condPhraseProb` の AEP は genuine (M0 で trivial と判明) **だが achievability に繋がらない** (`∑ⱼqⱼ≈c` の罠)。**裏付け (2026-06-20)**: path-prefix route の decl (`condPhraseProb` / `blockProb_neg_log_ge_sum`、`LZ78/ZivEntropyBridge.lean`) は `dep_consumers.sh` で **0 direct consumers** = orphan 確認済 → D4 dead-start (`∑ⱼqⱼ≈c` trap) が機械裏取りされた。gateway atom はこの route を素通り (`∑qⱼ≈c` を経由せず length-grouping log-sum を直接 SMB の `-log Pₙ` に乗せる) こと。旧 framing が要求した tree-node `Q_c^{tree}` は M3 realign で obsolete (実 decl 不在)。
- **D5**: McMillan は **Mathlib 既存** (`InformationTheory.kraft_mcmillan_inequality`)。再発明不要、wire 済 (M1 で使う)。
- **D6**: converse の pointwise `2^{-lz} ≤ Pₙ` 経路は**不健全** (Shannon-code 補題、`lz ≥ shannonLength` は pointwise 偽 = LZ78 universality の核心)。M4 は期待値→a.s. lift で。
- **D7**: Huffman 系の `mergedMeasure` 偽 core 等は別件 (本 roadmap 対象外、textbook-roadmap 判断ログ #6 + `huffman-fullB-structure-plan.md` 参照)。

---

## 3. 校正・規模・リスク総括

- **校正 (2026-06-20 realign r2 → leg 3 訂正)**: 既存 SMB (`SMB/AlgoetCover/` = `Core.lean` + `Liminf.lean` + `TwoSidedRatio.lean`、計 ~2800 行) は **完成済・sorry-free** で、headline `shannon_mcmillan_breiman` が `-log₂Pₙ/n → H₂` を free で供給する。**ただし SMB が握るのは source entropy limit (`-log₂Pₙ/n → H₂`、`blockLogAvg₂ → entropyRate₂`) だけ** — r2 realign が「M3 のエルゴード次元は plumbing 級、SMB が握っている」と書いたのは **source-limit と LZ 固有の combinatorial→conditional 橋 (`c·log₂c ≤ ∑ⱼ -log₂qⱼ + o(n)`、可変深さ tree-node AEP) の混同で、後者を過大に蒸発させた過小評価** (leg 3 gateway-atom-first probe `7171707` で machine-disproof)。**M3 risk 再評価 (leg 3)**: gateway (単位整合、`lz78_impl_bitrate_le_clogc_plus_overhead`) は **plumbing で closed (sorryAx-free)**。残る genuine 核 = 可変深さ tree-node AEP `c·log₂c ≤ ∑ⱼ -log₂qⱼ + o(n)` は **research-level self-build** (single in-session plan で閉じない、旧 treenode plan T1-T5 路、~数 leg)。`c·log c ≤ K·n` 単一組合せ bound は constant limsup しか出さず低エントロピー源で不十分 (refutation 済)。**M4 (converse Barron a.s. lift) は別途** (SMB-lower + 期待値→a.s. lift、本 realign の対象外、依然 high risk)。
- **総計**: おおよそ **~500–1500 行** (M3 = 可変深さ tree-node AEP 数 leg + M4 + M2 + 配線が主)。
- **数学的位置づけ**: LZ78 最適性は**標準教科書定理 (深い/未解決ではない)**。**SMB が source entropy limit を握っている** ので残りの難しさは「組合せ Ziv 不等式 self-build + 形式化が教科書の手抜きを露呈する」層に絞られるが、M3 の genuine 核 (combinatorial→conditional 橋 = 可変深さ tree-node AEP) は **plumbing でなく research-level self-build** (旧 treenode plan T1-T5、leg 3 で plumbing 誤認を是正)。M4 は依然エルゴード a.s. lift が残る。
- **進め方の推奨**: **M1 → M2** をまず確実に閉じて足場を固める (低〜中リスク、組合せ的)。**M2 gateway (Phase 1) は leg 3 で GO (closed)**、続く **M2 Phase 2b で genuine 壁 (可変深さ tree-node AEP) に到達 = STALL** (sub-plan 参照)。M3 攻略は旧 `lz78-ziv-treenode-plan.md` T1-T5 路 (tree-node sub-distribution → per-node 条件付き積 → log-sum → telescoping → `-log Pₙ` 接続、末尾のみ SMB 接続に realign) を resurrect する dedicated 複数 leg セッションで。**M4** (converse Barron a.s. lift) は独立した dedicated セッションで (依然 high risk、エルゴード a.s.)。

---

## 4. cross-link
- **sub-plan**: [`lz78-m2-plan.md`](lz78-m2-plan.md) — M2 length-grouping Ziv 組合せ核 = W2 `ziv_aseventual_le_blockLogAvg₂` (`@residual(wall:lz78-aseventual-ziv)`) discharge 計画。W1 SMB-in-bits は leg 3 で閉鎖済。**leg 3 status: Phase 1 gateway = GO (`lz78_impl_bitrate_le_clogc_plus_overhead` sorryAx-free、commit `7171707`)、Phase 2 = STALL at 2b** (可変深さ tree-node AEP、single in-session plan で閉じない genuine research-level 壁)。W2 は `sorry` + `@residual` 維持 (撤退ライン該当、達成済)。
- main: `docs/textbook-roadmap.md` 判断ログ #6 (現行サマリ、~35 エージェントの経緯・全 disproof・honest frontier の記録は `git log -- docs/textbook-roadmap.md` の 2026-05-26 整理前 commit に旧 #17–#26 として残置)
- **M3 攻略 path (leg 3 で resurrect)**: [`lz78-ziv-treenode-plan.md`](lz78-ziv-treenode-plan.md) T1-T5 (tree-node sub-distribution → per-node 条件付き積 → `c log c ≤ ∑ -log q` log-sum → telescoping → `-log Pₙ` 接続)。obsolete でなく M3 の genuine 核 (可変深さ tree-node AEP) の攻略 path (末尾の `-log Pₙ` 接続のみ r2 realign 後の SMB 接続形)。
- 既存 plan (本 roadmap が incremental master として統合): `lz78-completion-plan.md`, `lz78-treeinduced-aep-plan.md`, `lz78-aseventual-achievability-plan.md`, `lz78-blockrv-refactor-plan.md` + `-inventory.md`
- 完遂判定: `GreedyParsingImpl.lean` の wall sorry lemma 2本 (M3/M4) が discharge され、headline `lz78_asymptotic_optimality_with_greedy_impl` が `#print axioms` で sorryAx 非依存になった時点 = 標準B 完遂 (`h_bdd_above` 内製化は commit `a1ae108` で済、完遂条件から除外)。

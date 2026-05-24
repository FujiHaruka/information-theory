# DMC feedback capacity (E-10) ムーンショット計画 🌙

E-10 シードカード ([`docs/moonshot-seeds.md` 行 243-248](../moonshot-seeds.md))。
Cover-Thomas Theorem 7.12 — feedback あり DMC (`X_i = f_i(M, Y_1, …, Y_{i-1})`) でも
capacity は同じ。converse 段で `I(M; Y^n) ≤ n·C` を chain rule + memoryless 性で示す
"驚き定理" のうち、**chain rule 段** を本 plan の MVP scope として 0 sorry で publish。

## 進捗

- [x] Phase 0 — 経路選択判断 (per-letter step を hypothesis 形に分離して MVP 化) ✅
- [x] Phase A — `FeedbackCode` 構造 + 因果的 (causal) 符号化規約定義 ✅
- [x] Phase B — chain-rule 形 converse: `I(M; Y^n) ≤ ∑ I(X_i; Y_i)` (per-letter bound 仮定) ✅
- [x] Phase C — capacity 上界: `I(M; Y^n) ≤ n·C` (per-letter bound + 各 i での `I(X_i;Y_i) ≤ C` 仮定) ✅
- [x] Phase D — Fano と合成して `log|M| ≤ n·C + h(Pe) + Pe·log(|M|-1)` ✅
- [x] **後継 (E-10')** — `feedback_per_letter_bound` (memoryless ⇒
      `I(M; Y_i | Y^{<i}) ≤ I(X_i; Y_i)`) の純粋証明 ✅ (E-10' で完成、下記参照)

> 実態整合 (2026-05-20): DONE — 本 plan (E-10 MVP, chain-rule + Fano 合成) は `channel_coding_feedback_converse` (`Common2026/Shannon/ChannelCodingFeedback.lean:244`、0 sorry) で完成。`h_per_letter` を pass-through 仮説に取る MVP 形だが、後継 E-10' (`channel-coding-feedback-per-letter-bound-plan.md` の実体 `ChannelCodingFeedbackComplete.lean`) が `feedback_per_letter_bound` (`:116`、`IsMemorylessFeedback` から派生、0 sorry) でこれを剥がし、`channel_coding_feedback_converse_memoryless` (`:171`) が完全形を結論済。
>
> 2026-05-24 Wave 1.5 retract: MVP 3 件 (`channel_coding_feedback_converse_chain` / `_capacity` / `_converse`) を `@audit:retract-candidate(superseded-by-memoryless-form)` に再分類。`_memoryless` 完全形が無条件 publish 済の事実をタグ側に明示。

## ゴール / Approach

**ゴール** (本 plan MVP scope):

Feedback あり DMC で、**per-letter inequality `I(M; Y_i | Y^{<i}) ≤ I(X_i; Y_i)`** を
hypothesis 形で抽出した上で、chain rule + Fano 合成により

```
log |M| ≤ n · C + h(Pe) + Pe · log(|M| - 1)
```

を 0 sorry で publish する。per-letter inequality の純粋証明 (memoryless 性 + 因果性から
従う) は **E-10' deferred** に切り出す (判断ログ 1)。

### Approach (経路)

**Cover-Thomas 7.12 標準証明 (5 段)**:

```
log M = H(M)                                                                   -- (a) uniform
      = I(M; Y^n) + H(M | Y^n)                                                 -- (b) MI ↔ H definition
      = ∑_i I(M; Y_i | Y^{<i}) + H(M | Y^n)                                    -- (c) chain rule on Y axis
      ≤ ∑_i I(X_i; Y_i) + H(M | Y^n)                                           -- (d) per-letter bound  ← 本 plan で hypothesis 化
      ≤ n · C + H(M | Y^n)                                                     -- (e) I(X_i; Y_i) ≤ C
      ≤ n · C + 1 + Pe · log M                                                 -- (f) Fano
```

本 plan は **(c)+(e)+(f) を 0 sorry で publish**、(d) は仮定形 (`h_per_letter`)。

### Approach の代替経路と却下理由

1. **完全形 (d) を含めた 0 sorry 統合**: per-letter bound の Lean 証明は
   - `condMutualInfo μ Msg (Ys i) (Y^{<i})` を `H(Y_i|Y^{<i}) - H(Y_i|Y^{<i}, Msg)` に
     展開する補題が `CondMutualInfo.lean` に未整備 (現状 chain rule 形の klDiv 表現のみ)。
   - memoryless 性 `Y_i ⊥ (M, Y^{<i}) | X_i` を condDistrib equality に翻訳 + `H(Y_i|X_i) = H(Y_i|Y^{<i},X_i,M)` の処理を要する。これは Han chain rule + condDistrib 操作で
     ~500 行規模。
   - 本 plan budget (~400-600 行) を超過。**却下** (E-10' deferred、判断ログ 1)。

2. **MIChainRule.lean に Y 軸の chain rule を直接追加**: 既存
   `mutualInfo_chain_rule_fin` は X 軸 (左引数) 形:
   `I(X_0,…,X_{n-1}; Y) = ∑ I(X_i; Y | X^{<i})`。本 plan の (c) は Y 軸版:
   `I(M; Y_0,…,Y_{n-1}) = ∑ I(M; Y_i | Y^{<i})`。`mutualInfo_comm` で X 軸版に交換し、
   `condMutualInfo_comm` で各項も交換すれば直接導出可能。**採用** (Phase B)。

3. **既存 `channel_coding_converse_iid` を流用**: 不可。`mutualInfo_iid_eq_nsmul` は
   joint i.i.d. 仮定 `(X_i, Y_i) ∼ p ⊗ W` を要するが、feedback では `X_i` が prior `Y` に
   依存するため `X^n` は i.i.d. ではない。converse の構造自体が変わる。**却下**。

### 規模見積

- **Phase A**: `FeedbackCode` 構造 + `encodeAt` + 因果性記述 ~150 行。
- **Phase B**: Y 軸 chain rule corollary `mutualInfo_chain_rule_Y_axis_fin` ~150 行 (mutualInfo_comm + 既存 chain rule 経由)。
- **Phase C**: hypothesis-form 合成 `channel_coding_feedback_converse_chain` ~80 行。
- **Phase D**: Fano 合成 `channel_coding_feedback_converse` ~50 行 (既存 single-shot converse 経由)。
- 合計 ~400-500 行、新規 `Common2026/Shannon/ChannelCodingFeedback.lean`。
- 既存 `Converse.lean` / `MIChainRule.lean` / `CondMutualInfo.lean` 改変なし。

## Phase 0 — 経路選択判断

判定結論 (上記 Approach 節と同期):

1. **MVP scope: chain rule 段 + per-letter bound hypothesis 化 (採用)**: Cover-Thomas 7.12
   の核心ロジック (chain rule + per-letter bound + Fano 合成) を、per-letter bound を
   仮定形に抽出した上で 0 sorry 完走する。
2. **完全形 (per-letter bound 内部証明)**: E-10' deferred。`CondMutualInfo.lean` への
   `condEntropy` 展開系補題追加が必要 (~500 行)、本 plan budget 外。
3. **既存 `channel_coding_converse_iid` 流用**: 不可 (feedback で X^n が i.i.d. でない)。

主要 Mathlib API + 既存補題 (loogle 確認):

- `mutualInfo_chain_rule_fin` (`MIChainRule.lean:117`) — X 軸 n-変数 chain rule。
- `mutualInfo_comm` (`MutualInfo.lean`) — MI の対称性。
- `condMutualInfo_comm` (`CondMutualInfo.lean:295`) — 条件付き MI の対称性。
- `shannon_converse_single_shot` (`Converse.lean:81`) — Fano + DPI 合成済み単発 converse。
- `Real.binEntropy` (`Mathlib.Analysis.SpecialFunctions.BinaryEntropy`) — Fano `h(Pe)`。

## Phase A — `FeedbackCode` 構造

- [x] **A.1** `FeedbackCode M n α β`: `encoder : ∀ i : Fin n, (Fin M) → (Fin i.val → β) → α`
      (各時刻 i で `M` と過去 outputs `Y^{<i}` を入力に `X_i ∈ α` を出力) + `decoder : (Fin n → β) → Fin M`。
- [x] **A.2** `encodeAt`: `FeedbackCode → Fin n → Fin M → (Fin n → β) → α`
      (出力 `y : Fin n → β` のうち前置 `Fin i.val → β` を `y ∘ Fin.castLT` で取り出し、
      `encoder i m (Fin i.val → β prefix)` を呼ぶ)。
- [x] **A.3** decoder 部分は `Code` と同一: `decodingRegion`, `errorEvent` を rebuild。

## Phase B — Y 軸 chain rule corollary

- [x] **B.1** `mutualInfo_chain_rule_Y_axis_fin`:
      ```
      mutualInfo μ Msg (fun ω i => Ys i ω)
        = ∑ i : Fin n, condMutualInfo μ Msg (Ys i)
            (fun ω (j : Fin i.val) => Ys ⟨j.val, ...⟩ ω)
      ```
      mutualInfo_comm で左右を入れ替えて X 軸 chain rule に帰着 + condMutualInfo_comm
      で各項を本来の形に戻す。 ~100 行。

## Phase C — chain rule converse (hypothesis 形)

- [x] **C.1** `channel_coding_feedback_converse_chain`:
      仮定 `h_per_letter : ∀ i, condMutualInfo μ Msg (Ys i) (Y^{<i}) ≤ mutualInfo μ (Xs i) (Ys i)`
      で `mutualInfo μ Msg (fun ω i => Ys i ω) ≤ ∑ i, mutualInfo μ (Xs i) (Ys i)`。
      Phase B chain rule の各項を `h_per_letter` で押さえ Finset.sum_le_sum。
- [x] **C.2** `channel_coding_feedback_converse_capacity`:
      C.1 + 各 i で `mutualInfo μ (Xs i) (Ys i) ≤ C` を仮定して
      `mutualInfo μ Msg (fun ω i => Ys i ω) ≤ n • C`。

## Phase D — Fano 合成 main theorem

- [x] **D.1** `channel_coding_feedback_converse`:
      `shannon_converse_single_shot` (`Converse.lean:81`) を `Y := Fin n → β` 引数で
      呼び、Phase C 結果と組み合わせて
      ```
      log |M| ≤ n · C + h(Pe) + Pe · log(|M| - 1)
      ```
      を Fano 合成形で publish。Markov chain (`Msg → (encoder ∘ Msg) → Y^n`) 仮定は
      **不要** (feedback 下では成立しない)。直接 single-shot converse を `Msg, Yo := Y^n`
      で呼び、`I(Msg; Y^n) ≤ I(X^n; Y^n)` の DPI 等は使わない (feedback ではこの DPI
      自体が成立しない;代わりに per-letter `condMutualInfo` 経由)。
- [x] **D.2** 系として "feedback achievability" (`C_FB ≥ C`): degenerate feedback
      encoder (Y inputs を ignore する `encoder i m _ := f m i` 形) に対して、
      標準 `Code` と等価 ⇒ 達成可能 capacity は同じ ≥ `C`。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **per-letter bound (`feedback_per_letter_bound`) を hypothesis 形に分離** (Phase 0):
   `I(M; Y_i | Y^{<i}) ≤ I(X_i; Y_i)` の純粋証明は memoryless 性 + 因果性 + condEntropy
   展開を要し、現状 `CondMutualInfo.lean` には `condEntropy` 形展開補題が不在 (`condMutualInfo`
   は klDiv 形定義で、`H(Y|Z) - H(Y|Z,M)` 形変換は別途自前)。完全形は ~500 行追加で
   本 plan budget 外。**MVP**: per-letter bound を仮定形に抽出、chain rule + Fano 合成段は
   0 sorry で publish。後継 plan で per-letter bound 内部証明を E-10' deferred として
   切り出す。

2. **Y 軸 chain rule は MIChainRule 既存補題で導出可能** (Phase B):
   既存 `mutualInfo_chain_rule_fin` は X 軸形 `I(X_0,…,X_{n-1}; Y) = ∑ I(X_i; Y | X^{<i})`。
   `mutualInfo_comm` で左右入替後、`condMutualInfo_comm` で各項も swap すれば Y 軸形が
   出る。MIChainRule.lean に新規補題追加せず本 plan 内で局所証明 (~100 行)。

3. **Markov chain `Msg → X^n → Y^n` は feedback 下で成立しない** (Phase D):
   `channel_coding_converse_iid` の Markov chain 仮定 (`hmarkov`) は feedback 下で
   一般に偽 (`X_i` が prior `Y` に依存するため joint `(M, X^n, Y^n)` factorization が
   崩れる)。**本 plan は `shannon_converse_single_shot` (Markov chain 仮定なしの
   single-shot 版) を直接 `Msg, Yo := Y^n` で呼ぶ**。DPI による `I(Msg; Y^n) ≤ I(X^n; Y^n)`
   経路は使わず、代わりに per-letter `I(M; Y_i | Y^{<i})` 経由で n·C bound を取る。

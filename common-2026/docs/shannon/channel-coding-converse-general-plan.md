# Channel coding converse (general input form, D-2) ムーンショット計画 🌙

(D-2 / moonshot-seeds.md, 2026-05-13 起草)

## 進捗

- [x] Phase 0 — Scope 決定 (chain rule 1 段に縮小) ✅
- [x] Phase A — Skeleton + finiteness lemma ✅
- [x] Phase B — chain rule 代入 + toReal 分配 ✅
- [x] Phase C — 主定理 `channel_coding_converse_general_chainRule` 完成 ✅

> 実態整合 (2026-05-20): DONE (chain-rule scope) — `channel_coding_converse_general_chainRule` (`InformationTheory/Shannon/ChannelCodingConverseGeneral.lean:73`、0 sorry) が IID 仮定なしの一般入力 chain-rule 形 `log|M| ≤ ∑ I(X_i; Y^n | X^{<i}).toReal + Fano` を結論。memoryless per-summand bound は予定どおり後継 D-2' / D-2'' (`ChannelCodingConverseGeneralComplete.lean` / `ChannelCodingConverseMemorylessPure.lean`) で完成済。

## ゴール / Approach

**最終ゴール (D-2 完全形、Cover-Thomas 7.9 一般入力 converse)**:
```
任意 input distribution p、memoryless channel W、Markov encoder で:
  log |M| ≤ n · I(p_avg; W) + h(Pe) + Pe · log(|M| − 1)
```
ここで `p_avg := (1/n) ∑ p_{X_i}` は経験的 average input distribution、`I(p_avg; W)` は
concavity of `I(·; W)` で `(1/n) ∑ I(X_i; Y_i)` の上界。

**本セッションの scope (最小一歩)**:
seed の reuse-test 由来判断
> iid 入力なら `iid_eq_nsmul` が直接 `n · I(X_0; Y_0)` を返す
> 一般 input では `chain_rule_fin` + memoryless で per-summand `I(X_i; Y_i | X^{<i}) ≤ I(X_i; Y_i)`

から、**chain rule 1 段** だけを完全に通す。即ち:

```
log |M| ≤ ∑ I(X_i; Y^n | X^{<i}).toReal + h(Pe) + Pe · log(|M| − 1)
```

**この form の意義**:
- 入力 iid 仮定を捨てた general input で成立。
- 既存 `channel_coding_converse_iid` の出発点 `shannon_converse_single_shot_markov_encoder`
  と同じ。違いは「`I(X^n; Y^n)` を `iid_eq_nsmul` で `n · I(X_0; Y_0)` に圧縮する」段を
  「`chain_rule_fin` で `∑ I(X_i; Y^n | X^{<i})` に分解する」段に **置換** した形。
- memoryless property に基づく per-summand bound `I(X_i; Y^n | X^{<i}) ≤ I(X_i; Y_i)` は
  scope-deferred。本 plan の主定理に hypothesis として乗らない。
- IID 仮定を外しているのが本質的に新規 (既存 `channel_coding_converse_iid` は IID 必須)。

### Approach (経路)

3 段の合成、bridge ゼロ:

1. **Step 1**: `shannon_converse_single_shot_markov_encoder` で
   `log|M| ≤ I(X^n; Y^n).toReal + Fano(Pe)` を取得。
2. **Step 2**: `mutualInfo_chain_rule_fin` で
   `I(X^n; Y^n) = ∑_i I(X_i; Y^n | X^{<i})` (ENNReal 等式)。
3. **Step 3**: `ENNReal.toReal_sum` で和を `.toReal` に分配:
   `(∑ I(X_i; Y^n | X^{<i})).toReal = ∑ (I(X_i; Y^n | X^{<i})).toReal`。
   各 summand 有限性は `condMutualInfo_ne_top` (有限 alphabet) で確保。
4. **Step 4**: `linarith` で閉じる。

### 既存資産の流用

- `InformationTheory/Shannon/ChannelCodingConverse.lean` (122 行): 既存 IID 版の n-channel
  scaling 構造をそのまま流用。Step 1 は完全同形。
- `InformationTheory/Shannon/Converse.lean` `shannon_converse_single_shot_markov_encoder`: Step 1。
- `InformationTheory/Shannon/MIChainRule.lean` `mutualInfo_chain_rule_fin`: Step 2。
- `InformationTheory/Shannon/CondMutualInfo.lean` `condMutualInfo_ne_top`: Step 3 の summand 有限性。

### 規模見積

- 新規 `InformationTheory/Shannon/ChannelCodingConverseGeneral.lean` ~120-150 行。
- 主定理 1 本: `channel_coding_converse_general_chainRule`。
- 既存 `ChannelCodingConverse.lean` (122 行) と並立、touch なし。

### Approach の代替経路と却下理由

1. **memoryless per-summand bound を本 plan で同梱**: `I(X_i; Y^n | X^{<i}) ≤ I(X_i; Y_i)`
   を実装する場合、memoryless 性の formal 定式化 + chain rule on `Y^n` (右 RV の n 変数 chain rule)
   + per-letter DPI など ~500-1000 行追加。今 session の budget 外、**却下** (deferred 後継 plan)。
2. **入力分布 averaging + concavity**: `(1/n) ∑ I(X_i; Y_i) ≤ I(p_avg; W)` の concavity 不等式は
   `mutualInfoOfChannel` の concavity を要し、Mathlib 未整備、~300 行追加。**却下** (deferred)。
3. **expurgation で uniform input 緩和**: `channel_coding_achievability` 側で扱う pattern。
   converse 側の uniform input は **single-shot 段で消費するだけ** (`hMsg_uniform`)、`Msg` の
   uniform 性のみで n-channel 段は入力分布非依存 (seed 注記参照)。本 plan で扱う必要なし。

## Phase 0 — Scope 決定

**判断**: chain rule 1 段で general input への一段拡張を pin down する。

- iid 仮定を **完全に外す** ことが本質的な新規性。
- memoryless per-summand bound は **本 plan の主定理 RHS には現れない** (chain rule で conditional
  MI の和まで分解した形が最終形)。これで「general input への第一歩」として self-contained に
  publish 可能。
- 後続 plan (memoryless per-summand) で `∑ I(X_i; Y^n | X^{<i}) ≤ ∑ I(X_i; Y_i)` を加えれば、
  Cover-Thomas 7.9 完全形まで合成 1 段で到達。

## Phase A — Skeleton + finiteness lemma

- [x] 新規ファイル `InformationTheory/Shannon/ChannelCodingConverseGeneral.lean` 雛形 (import + namespace
  + 主定理 signature `:= by sorry`)。
- [x] Lean が compile 通る (sorry warning のみ) ことを確認。
- [x] `condMutualInfo_ne_top` の prerequisites (StandardBorel / Nonempty for `Fin i.val → α`
  prefix RV) を予め整える。

## Phase B — chain rule 代入 + toReal 分配

- [x] Step 1 (single-shot Markov encoder converse) 代入。
- [x] Step 2 (`mutualInfo_chain_rule_fin`) 代入、`I(X^n; Y^n) = ∑ I(X_i; Y^n | X^{<i})` 形に書換。
- [x] Step 3 (`ENNReal.toReal_sum`) で和の `.toReal` 分配、summand 有限性は per-i
  `condMutualInfo_ne_top`。
- [x] `linarith` で閉じる。

## Phase C — 主定理完成

- [x] 主定理名: `channel_coding_converse_general_chainRule`。
- [x] signature: 既存 IID 版から `h_iid_*` / `h_copy_*` 系の IID 仮説を **全削除**、Markov encoder
  仮説と uniform Msg 仮説のみ残す。
- [x] `lake env lean InformationTheory/Shannon/ChannelCodingConverseGeneral.lean` で silent output。

## 判断ログ

1. **chain rule 1 段に scope を絞った理由**: D-2 完全形 (memoryless per-summand bound +
   concavity of `I(·; W)`) は ~1000-1500 行規模で、`mutualInfoOfChannel_concave` などの
   Mathlib gap が複数。本セッション (~200 行 budget) では届かない。一方、chain rule 1 段は
   既存 `mutualInfo_chain_rule_fin` の直接呼び出しで ~100 行、確実に commit 可能。
2. **`condMutualInfo` 引数のprefix型**: `chain_rule_fin` は per-i prefix を
   `fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω` という `Fin i.val → α` 型で
   返す。これに対する `condMutualInfo_ne_top` 適用は `Fintype (Fin i.val → α)` /
   `StandardBorelSpace (Fin i.val → α)` / `Nonempty (Fin i.val → α)` を要するが、`α` が
   `Fintype + MeasurableSingletonClass + Nonempty` なら全て auto-derive。
3. **`mutualInfo_ne_top` 適用に必要な型**: per-i は `Y^n = Fin n → β`、`X_i = α`、prefix
   `Fin i.val → α`。すべて Fintype + MeasurableSingletonClass で `mutualInfo_ne_top` が通る。
   StandardBorelSpace は Fintype + MeasurableSingletonClass + Nonempty から自動 derive。

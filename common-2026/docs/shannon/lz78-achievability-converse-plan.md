# T4-A LZ78 achievability + converse 組合せ核心 full-closure ムーンショット計画 🌙

> **Parent**:
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md) §「撤退ライン L-LZ1 / L-LZ2」 + Status (3 honest 仮定残)
> - [`lz78-ziv-inequality-discharge-moonshot-plan.md`](./lz78-ziv-inequality-discharge-moonshot-plan.md) §「L-LZ1-A/B counting 層は genuine、L-LZ1-C/D 撤退」
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A LZ78 漸近最適性」(Ch.13)
>
> **Inventory (Phase 0 で参照、新規 inventory は M0 で起草)**:
> [`lz78-mathlib-inventory.md`](./lz78-mathlib-inventory.md)
>
> **Goal (短形)**: headline `lz78_two_sided_optimality_greedy_impl_bdd_below_free`
> (`LZ78FinalGlue.lean:385`) が現在背負う **3 本の honest 仮定**
> (`IsLZ78AchievabilityChainHyp` Eq.13.124 / `IsLZ78ConverseChainHyp` Eq.13.130 /
> `h_bdd_above`) を、**連続 Mathlib gap の無い離散・組合せ・実解析**で genuine discharge
> し、`lz78_two_sided_optimality_greedy_impl` を **無仮定** (ergodic process + finite
> alphabet のみ) で publish する。SMB sandwich (L-LZ3) は既に無条件 genuine、greedy 構成
> (L-LZ4) も genuine。本 plan は **残る 3 仮定の組合せ核心** に集中する。

## Status (2026-05-21)

> 着手前。3 honest 仮定はいずれも `Prop := True` ではなく **数学的に意味のある述語/不等式**
> (`LZ78FinalGlue.lean:118` `IsLZ78AchievabilityChainHyp` は genuine な `∀ᵐ ω, limsup(lz/n)
> ≤ limsup blockLogAvg`、`LZ78ConverseDischarge.lean:106` `IsLZ78ConverseChainHyp` は genuine
> な `∀ᵐ ω, liminf blockLogAvg ≤ liminf(lz/n)`)。**本 plan は `True.intro` bridge を本物の証明に
> 置換するのではなく、これらの仮定を結論側 (headline) から外して内部で genuine 供給する。**

## 進捗

- [ ] Phase 0 / M0 — 既存 Body genuine 状態確定 + greedy 実装差し替え判定 + Mathlib 在庫 📋 → [`lz78-mathlib-inventory.md`](./lz78-mathlib-inventory.md)
- [ ] Phase A — 真の longest-prefix greedy parsing への実装差し替え + distinct phrase 不変量 📋
- [ ] Phase B — distinct-phrase counting `c(n) ≤ n` から `c(n)·log c(n) ≤ Kn` (★) genuine 供給 📋
- [ ] Phase C — `h_bdd_above` の genuine discharge (★ + inversion 経由) 📋
- [ ] Phase D — achievability chain Eq.13.124 の entropy-level 接続 📋
- [ ] Phase E — converse chain Eq.13.130 の Kraft → a.s. liminf 接続 📋
- [ ] Phase F — headline 無仮定 publish `lz78_two_sided_optimality_greedy_impl_unconditional` 📋
- [ ] Phase V — `InformationTheory.lean` 編入 + roadmap 更新 📋

## ゴール / Approach

### 最終到達点 (Phase F 完成形)

```lean
namespace InformationTheory.Shannon

/-- **T4-A 無仮定 headline**: ergodic process on a finite alphabet について、genuine
greedy LZ78 encoding の per-symbol rate は a.s. entropy rate に収束する。3 honest 仮定
(Eq.13.124 / Eq.13.130 / h_bdd_above) はすべて内部で genuine discharge 済。 -/
theorem lz78_two_sided_optimality_greedy_impl_unconditional
    {α Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n => (lz78GreedyImplEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) := ...

end InformationTheory.Shannon
```

### Approach (overall strategy / shape of solution)

**戦略の shape** — headline は `LZ78FinalGlue.lean` で既に
`tendsto_of_le_liminf_of_limsup_le` への合流に還元され、SMB sandwich が無条件 genuine に
組み込まれている。残る 3 仮定の依存構造は以下:

```
                  lz78_two_sided_optimality_greedy_impl_unconditional (Phase F, 無仮定)
                                         │
        ┌────────────────────────────────┼────────────────────────────────┐
   h_achiev (Eq.13.124)            h_converse (Eq.13.130)            h_bdd_above
   limsup(lz/n) ≤ limsup blk      liminf blk ≤ liminf(lz/n)         IsBoundedUnder(·≤·)
        │ Phase D                       │ Phase E                        │ Phase C
        │                              │                                │
   ┌────┴─────┐                  ┌──────┴───────┐                  ┌────┴─────┐
 (★) c·logc≤Kn  entropy-link    Kraft 下界     blockLogAvg-link    (★) → c=O(n/log n)
   Phase B    ┌───────────────┐  ShannonCode    既存 SMB           Phase B → 上界 const
              │ 既存 inversion │  reuse?         (genuine)
              │  isBigO ... ✅  │
              └───────────────┘
        │
   distinct-phrase counting (Phase A: 真の greedy 実装差し替え)
        │
   card_phraseSet_le_pow ✅ (既存 genuine, count→distinct 接続が核心)
```

**全工程の最深部 = Phase A の実装差し替え**。現 `lz78GreedyParseAux`
(`LZ78GreedyParsingImpl.lean:192`) は **one-symbol-per-step** 近似であり、各 phrase が
1 記号しか消費しないため `count = input.length = n` (`lz78GreedyParse_count` `:277`)。
この実装のままでは Ziv 主不等式 `c(n)·log c(n) ≤ Kn` (★) は **数学的に false**
(`c=n` を入れると `n log n ≤ Kn` は不成立)。**(★) が genuine に成り立つには、phrases が
distinct (= LZ78 dictionary は一意な文字列) で n 記号を非冗長に消費する真の
longest-prefix-match greedy parsing への差し替えが必須**。これが本 plan の最重リスクであり、
着手の起点。

**Phase B の核心** — distinct phrase 数 `c(n)` について Cover-Thomas Lemma 13.5.2 の
counting 議論: 長さ `n` の文字列を distinct phrase に分割すると、長さ `ℓ` 以下の distinct
phrase は高々 `|α|^1 + ... + |α|^ℓ = O(|α|^ℓ)` 個、ゆえに `c(n)` 個の distinct phrase の
総文字数 `n ≥ Σ (phrase 長)` から `c(n)·log_|α| c(n) ≤ n·(1+o(1))`、すなわち
`c(n)·log c(n) ≤ K·n` (★)。**inversion (★) ⟹ c=O(n/log n) は既存 genuine**
(`isBigO_natCast_div_log_of_mul_log_le` `LZ78PhraseCountAsymptoticBody.lean:107`)、
本 plan は (★) 自体を供給する `IsZivCountingMulLogBound` (`:192`) の genuine 化に集中。

**Phase C — `h_bdd_above` の genuine discharge**。greedy bit-length bound は
`lz78_impl_encoding_length_per_symbol_le` (`LZ78GreedyParsingImpl.lean:336`) で
`(lz/n) ≤ log(n+1)+log|α|+2` だが、これは `n→∞` で発散し uniform 上界を与えない
(headline docstring `:378` がこれを honest に明言)。**だが (★)/inversion から
`c(n) ≤ C·n/log n` が出れば、bit-length は `c(n)·(log(n+1)+log|α|+2)` 形に書き換えられ、
`/n` で `≤ C·(log n / log n)·(1+o(1)) = O(1)`、すなわち uniform 上界 → `IsBoundedUnder(·≤·)`
が genuine に出る**(これは親 plan の調査が指摘した「lz/n ≤ ln + o(1) が出れば h_bdd_above
も落ちる」点)。Phase B が前提。

**Phase D — achievability chain Eq.13.124 の entropy-level 接続**。Ziv inequality の
本来の形は `(1/n)·lz_length(X^n) ≤ -(1/n) log P(X^n) + (counting slack)` であり、右辺第1項が
`blockLogAvg`、第2項が `c(n)/n·log(...)` = (★/inversion から) `o(1)`。limsup を取ると
`limsup(lz/n) ≤ limsup blockLogAvg + 0`、すなわち `IsLZ78AchievabilityChainHyp`
(`LZ78FinalGlue.lean:118`)。本 plan の **measure-theoretic に最も重い部分**: per-block
log-likelihood `blockLogAvg` と greedy bit-length の pmf-level 連結。

**Phase E — converse chain Eq.13.130 の Kraft → a.s. liminf 接続**。任意 prefix code の
codeword 長は Kraft 不等式から `E[length] ≥ H(X^n)`、これを a.s.-pointwise (block-level
n→∞) に橋渡しして `liminf blockLogAvg ≤ liminf(lz/n)` (`IsLZ78ConverseChainHyp`
`LZ78ConverseDischarge.lean:106`)。**project 既存 Kraft 資産** (`ShannonCode.lean`
`entropyD_le_expectedLength_of_kraft` / `kraftSum`、`ShannonCodeKraftReverse`) の
expectation-level を a.s.-pointwise に変換する部分が核心 (~200-300 行)。

**Mathlib-shape-driven の設計選択** — 結論側の `blockLogAvg` / `entropyRate` / `limsup` /
`liminf` の shape は既存 `LZ78FinalGlue.lean` / `LZ78ConverseDischarge.lean` の述語定義を
**一切変えない**。本 plan は新しい述語を導入せず、既存の `IsLZ78AchievabilityChainHyp` /
`IsLZ78ConverseChainHyp` の **body を満たす定理を greedy 実装について genuine に証明**し、
headline の引数から外す。phrase 経験分布を新規定義する場合は (Phase B/D)、
`MeasureTheory.Measure.map` の push-forward 結論形 + `Finset.sum` の log-sum 結論形に
合わせ、`blockLogAvg μ p n ω = -(1/n)·log (P_n {block})` (`ShannonMcMillanBreiman.lean:55`)
の shape を再利用する (新規 reshaping bridge を書かない)。

### Approach 図 (規模 + 撤退条件)

```
Phase 0/M0 : 既存 genuine 確定 + greedy 差し替え判定 + Kraft reuse 在庫        ← inventory 起草
             ──────────────────────────────────────────────────────────────
Phase A  : 真の longest-prefix greedy + distinct phrase 不変量                ← ~250-400 行
           撤退: distinct 不変量証明が >300 行 → one-symbol 実装維持 + (★) を
                 honest 仮定に残し achievability/converse のみ部分 discharge
             ──────────────────────────────────────────────────────────────
Phase B  : (★) c·log c ≤ Kn を distinct-counting から genuine 供給             ← ~200-350 行
           撤退: counting 議論が >300 行 → IsZivCountingMulLogBound を honest 仮定維持
                 (inversion は既存 genuine なので下流は壊れない)
             ──────────────────────────────────────────────────────────────
Phase C  : h_bdd_above genuine discharge (★+inversion → bit-rate O(1))         ← ~100-200 行
           撤退: Phase B 未達なら自動撤退 (★ 依存)。単独では落ちない
             ──────────────────────────────────────────────────────────────
Phase D  : achievability chain Eq.13.124 entropy-level 接続                    ← ~250-400 行
           撤退: blockLogAvg ↔ greedy bit-length の pmf 連結が >300 行 →
                 IsLZ78AchievabilityChainHyp を honest 仮定維持
             ──────────────────────────────────────────────────────────────
Phase E  : converse chain Eq.13.130 Kraft → a.s. liminf 接続                   ← ~200-350 行
           撤退: Kraft expectation → a.s. 変換が >300 行 →
                 IsLZ78ConverseChainHyp を honest 仮定維持
             ──────────────────────────────────────────────────────────────
Phase F  : headline 無仮定 publish                                            ← ~50-150 行
Phase V  : InformationTheory.lean 編入 + roadmap                                     ← ~10-30 行
```

### 規模見積

| Phase | 中央 | 範囲 | proof-log | 出力 |
|---|---|---|---|---|
| Phase 0 / M0 | — | — | no | inventory 追補 (Kraft reuse, Mathlib log-sum) |
| Phase A | **320 行** | 250-400 | yes | `LZ78GreedyParsingImpl.lean` 拡張 (or 新規 `LZ78GreedyLongestPrefix.lean`) |
| Phase B | **280 行** | 200-350 | yes | `LZ78ZivCountingBody.lean` 新規 ((★) genuine 供給) |
| Phase C | **150 行** | 100-200 | yes | `LZ78FinalGlue.lean` 拡張 (h_bdd_above discharge) |
| Phase D | **320 行** | 250-400 | yes | `LZ78AchievabilityChain.lean` 新規 (Eq.13.124) |
| Phase E | **280 行** | 200-350 | yes | `LZ78ConverseChain.lean` 新規 (Eq.13.130) |
| Phase F | **100 行** | 50-150 | no | `LZ78FinalGlue.lean` 拡張 (無仮定 headline) |
| Phase V | **20 行** | 10-30 | no | `InformationTheory.lean` + roadmap |
| **累計** | **~1470 行** | **1060-1880** | — | 3 新規 file + 2 拡張 |

---

## Phase 0 / M0 — 既存 Body genuine 状態確定 + 実装差し替え判定 + Mathlib 在庫 📋

### スコープ

- 軸 1: 本 plan 起草時に Read 済の既存 genuine 状態を inventory に固定:
  - SMB sandwich `lz78_smb_sandwich_ergodic` (`LZ78SMBSandwich.lean:388`) 無条件 genuine。
  - counting `card_phraseSet_le_pow` (`LZ78ZivInequality.lean:204`): `card ≤ (count+1)·|α|` Nat genuine。
  - inversion `isBigO_natCast_div_log_of_mul_log_le` (`LZ78PhraseCountAsymptoticBody.lean:107`):
    `(★) ⟹ c=O(n/log n)` real-analysis genuine。
  - greedy `lz78GreedyParse` (`LZ78GreedyParsingImpl.lean:233`): 有効 parsing genuine、
    **ただし one-symbol step ゆえ `count = n` (`:277`)** — (★) を満たさない。
- 軸 2: **greedy 実装差し替え判定**。真の longest-prefix-match に差し替えるか
  (Phase A)、one-symbol 維持で (★) を honest 仮定に残すか。差し替え版の distinct 不変量
  (= dictionary entry の一意性) が Lean で何行になるか見積。
- 軸 3: **Kraft reuse 在庫**。`ShannonCode.lean` の `entropyD_le_expectedLength_of_kraft`
  / `kraftSum` / `ShannonCodeKraftReverse.exists_prefix_code_of_kraft` の verbatim signature
  + `[...]` typeclass を inventory に記録 (Phase E が expectation-level を a.s.-pointwise に
  橋渡しできるか判定)。
- 軸 4: **Mathlib log-sum 在庫**。`Finset.inner_le_nnorm` 系ではなく、`Real.add_pow_le_pow_mul_pow_of_sq_le_sq`
  ではなく、Cover-Thomas counting で要る `Σ log` / `log Σ` / Jensen 系
  (`Real.add_log_le`, `StrictConcaveOn Real.log`, `inner_le_iff`) を loogle 裏取り。
- 軸 5: phrase 経験分布を定義する必要があるか (Phase B/D)、それとも `blockLogAvg` の
  既存 shape で足りるかの確定。**Mathlib-shape-driven**: `blockLogAvg μ p n ω =
  -(1/n)·log (P_n {block_n ω})` (`ShannonMcMillanBreiman.lean:55`) の結論形に合わせる。

### Done 条件

- 既存 5 genuine 資産 + 4 honest gap を inventory に file:line + verbatim で固定。
- greedy 差し替え判定 (差し替え or 維持) + distinct 不変量の行数見積。
- Kraft reuse 3 lemma の verbatim signature + `[...]` typeclass 記録。
- Mathlib log-sum / Jensen 在庫の loogle 裏取り (`Found N declarations`)。
- 撤退ライン (L-AC1 〜 L-AC5) を本 plan + inventory に append-only。

### 工数感

**1 ターン (20-40 分)**。inventory 追補 (新規 file 起草でなく既存 `lz78-mathlib-inventory.md`
への append、ただし inventory は `mathlib-inventory` 担当の責務 — 本 plan からは「inventory に
記録すべき項目リスト」を提示し、実際の追記は orchestrator 経由)。

### リスク / 撤退判定

- **Kraft 既存資産が expectation-level のみで a.s.-pointwise 化に追加 ~200 行要る** → Phase E の
  撤退条件 L-AC5 に直結。M0 で行数見積を確定。

---

## Phase A — 真の longest-prefix greedy + distinct phrase 不変量 📋

### スコープ

現 `lz78GreedyParseAux` (`LZ78GreedyParsingImpl.lean:192`) は one-symbol-per-step で
`count = n`。**(★) `c·log c ≤ Kn` を genuine に成立させるには distinct phrase 不変量が必須**。
本 Phase で真の longest-prefix-match 実装に差し替え、**dictionary entry が distinct** (一意な
文字列) であることと、**phrases の総消費文字数 = n** であることを証明する。

### novel な自作補題 (statement 案)

```lean
/-- **真の greedy parse**: 各ステップで dictionary の最長一致 prefix `w` を消費し、
`w ++ [s]` を新規 phrase として emit (これは必ず dictionary に未登録 = distinct)。 -/
def lz78LongestPrefixParseAux :
    ℕ → List (List α) → List α → List (LZ78Phrase α) → List (LZ78Phrase α) := ...

/-- **distinct 不変量**: emit された phrase 文字列 (dictionary entry) は全て相異なる。
本 plan の最深部。`w ++ [s]` が常に dictionary に未登録であることを step 不変量で保つ。 -/
def lz78ParsePhraseStrings (l : List (LZ78Phrase α)) : List (List α) := ...

theorem lz78LongestPrefixParse_phraseStrings_nodup (input : List α) :
    (lz78ParsePhraseStrings (lz78LongestPrefixParse input)).Nodup := ...

/-- **消費文字数保存**: phrase 文字列の総長 = 入力長 `n` (partial last phrase は別扱い)。
distinct counting の分母 `n` を与える。 -/
theorem lz78LongestPrefixParse_total_length (input : List α) :
    (lz78ParsePhraseStrings (lz78LongestPrefixParse input)).foldr
        (fun w acc => w.length + acc) 0 = input.length := ...
```

### Done 条件

- 真の greedy 実装 `lz78LongestPrefixParse` が有効 `LZ78Parsing` (inRange genuine)。
- distinct (`Nodup` on phrase strings) genuine。
- 総消費文字数 = `n` genuine。
- `lake env lean` clean。

### ステップ

- [ ] **A-1** longest-prefix-match worker `lz78LongestPrefixParseAux` 実装 + fuel termination
- [ ] **A-2** inRange 不変量保存 (既存 `isWellFormedPhrases_snoc` `:92` 再利用)
- [ ] **A-3** phrase 文字列 `Nodup` 不変量 (step ごとに新規文字列が dict 未登録) ← **最深部**
- [ ] **A-4** 総消費文字数 = `n` の length 保存補題
- [ ] **A-5** `lake env lean` clean

### 工数感

**~250-400 行**。proof-log: yes (distinct 不変量の step 帰納が詰まりやすい)。

### リスク / 撤退ライン (L-AC1)

- **A-3 distinct 不変量証明が >300 行**: longest-prefix-match の正当性 (matched prefix が
  必ず dict 内、emit 文字列が必ず未登録) の帰納が重い → **L-AC1 撤退**: one-symbol 実装を
  維持し、`IsZivCountingMulLogBound` (★) を honest 仮定に残す。下流 (inversion) は genuine の
  まま、Phase C/D の (★) 依存部分も honest 仮定経由で繋ぐ。**この場合 full closure は届かず、
  achievability は「(★) を仮定すれば genuine」の段階着地**。

---

## Phase B — (★) `c·log c ≤ Kn` を distinct-counting から genuine 供給 📋

### スコープ

Phase A の distinct 不変量 + 総文字数 = n から、Cover-Thomas Lemma 13.5.2 の counting 議論で
`IsZivCountingMulLogBound` (`LZ78PhraseCountAsymptoticBody.lean:192`) を genuine に discharge。
inversion `isBigO_natCast_div_log_of_mul_log_le` (`:107`) は既存 genuine なので、本 Phase が
通れば `c(n) = O(n/log n)` が自動で genuine 化。

### novel な自作補題 (statement 案)

```lean
/-- **distinct phrase の長さ別個数上界**: 長さ `ℓ` の distinct phrase は高々 `|α|^ℓ` 個
(distinct な長さ-ℓ 文字列の総数)。`Fintype.card (Fin ℓ → α) = |α|^ℓ` から。 -/
theorem card_distinctPhrases_len_le {ℓ : ℕ} (ws : List (List α))
    (hnodup : ws.Nodup) (hlen : ∀ w ∈ ws, w.length = ℓ) :
    ws.length ≤ Fintype.card α ^ ℓ := ...

/-- **総文字数下界**: `c` 個の distinct phrase の総文字数は、最短の埋め方
(長さ 1,2,... を順に使う) で下から評価して `≥ c·log_|α| c · (1+o(1))`。
counting 議論の核心: `n = Σ phrase 長 ≥ (短い方から詰める) ≥ c·log_|α| c / ...`。 -/
theorem total_length_ge_count_mul_log (ws : List (List α)) (hnodup : ws.Nodup) :
    (ws.foldr (fun w acc => w.length + acc) 0 : ℝ)
      ≥ (ws.length : ℝ) * Real.logb (Fintype.card α) (ws.length) - (ws.length : ℝ) := ...

/-- **(★) genuine 供給**: Phase A の distinct 不変量 + 総文字数 = n を上の counting に
代入して `c(n)·log c(n) ≤ K·n` (K = log|α| + 定数)。 -/
theorem lz78GreedyImpl_isZivCountingMulLogBound (input : ℕ → List α)
    (hlen : ∀ n, (input n).length = n) :
    IsZivCountingMulLogBound (fun n => lz78LongestPrefixParse (input n)) (Real.log (Fintype.card α) + 1) := ...
```

### Done 条件

- 長さ別個数上界 `card_distinctPhrases_len_le` genuine。
- 総文字数下界 `total_length_ge_count_mul_log` genuine (Cover-Thomas counting の核心)。
- `IsZivCountingMulLogBound` discharge genuine → inversion 経由で `IsLZ78PhraseCountAsymptotic`
  も自動 genuine。
- `lake env lean` clean。

### ステップ

- [ ] **B-1** 長さ別 distinct 文字列個数上界 (`Fintype.card (Fin ℓ → α)` 再利用)
- [ ] **B-2** distinct phrase を長さ昇順に並べる + 「短い方から詰める」最小総長補題 ← **核心**
- [ ] **B-3** `n = Σ phrase 長 ≥ c·log_|α| c - c` の real 不等式
- [ ] **B-4** `IsZivCountingMulLogBound` discharge + inversion 接続確認
- [ ] **B-5** `lake env lean` clean

### 工数感

**~200-350 行**。proof-log: yes (B-2/B-3 の counting 不等式が Mathlib に直接なく自作)。

### リスク / 撤退ライン (L-AC2)

- **B-2/B-3 の counting 議論が >300 行**: 「短い方から詰める」議論 (rearrangement/sorting +
  log-sum 下界) が Mathlib 不在で重い → **L-AC2 撤退**: `IsZivCountingMulLogBound` を honest
  仮定に残す。inversion は既存 genuine なので、Phase C/D は (★) を仮定して genuine に繋ぐ。
  **段階着地: 「Ziv counting (★) を仮定すれば achievability + h_bdd_above が genuine」**。

---

## Phase C — `h_bdd_above` の genuine discharge 📋

### スコープ

headline `lz78_two_sided_optimality_greedy_impl_bdd_below_free` (`LZ78FinalGlue.lean:385`) が
唯一残す boundedness 仮定 `h_bdd_above`。greedy bit-rate は
`lz78_impl_encoding_length_per_symbol_le` (`LZ78GreedyParsingImpl.lean:336`) で
`(lz/n) ≤ log(n+1)+log|α|+2` だが発散。**Phase B の `c(n) ≤ C·n/log n` を使うと、bit-length は
`c(n)·(log(n+1)+log|α|+2)`、`/n` で `≤ C·(log(n+1)/log n)·(1+...) → C·(定数)`、すなわち
uniform 上界**。

### novel な自作補題 (statement 案)

```lean
/-- **bit-rate を distinct count で書き換え**: `lz/n = c(n)/n·(phrase 当たり平均 bit)`。
真の greedy では各 phrase が `≤ log(c+1)+log|α|+2` bit。 -/
theorem lz78LongestPrefix_per_symbol_via_count (n : ℕ) (hn : 0 < n) (x : Fin n → α) :
    (lz78GreedyImplEncodingLength n x : ℝ) / n
      ≤ ((lz78LongestPrefixParse (List.ofFn x)).count : ℝ) / n
          * (Real.log (n + 1) + Real.log (Fintype.card α) + 2) := ...

/-- **uniform 上界 → IsBoundedUnder(·≤·)**: `c(n) ≤ C·n/log n` と上の書き換えから
`lz/n ≤ C·(log(n+1)+...)/log n → 定数` で eventually 有界。 -/
theorem lz78GreedyImpl_isBoundedUnder_le
    (μ : Measure Ω) (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n => (lz78GreedyImplEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / n) := ...
```

### Done 条件

- bit-rate を count 経由で書き換えた補題 genuine。
- `IsBoundedUnder(·≤·)` genuine discharge (Phase B の `c=O(n/log n)` を `log(n+1)/log n → 1`
  と組合せ、`lz/n` の eventual 上界定数を構成)。
- `lz78GreedyImpl_isBoundedUnder_ge` (`LZ78FinalGlue.lean:311`) と対をなす genuine 補題。

### ステップ

- [ ] **C-1** bit-rate ↔ count 書き換え
- [ ] **C-2** `log(n+1)/log n → 1` の eventual 上界 (Mathlib `Real.log` 比 limit)
- [ ] **C-3** `c=O(n/log n)` (Phase B inversion) と組合せて `lz/n` の eventual 定数上界
- [ ] **C-4** `IsBoundedUnder(·≤·)` 形に詰める

### 工数感

**~100-200 行**。proof-log: yes (C-2/C-3 の asymptotic 上界詰め)。

### リスク / 撤退ライン (L-AC3)

- **Phase B 未達 (L-AC2 撤退)**: 自動的に L-AC3 も (★) 依存で撤退。h_bdd_above は honest 仮定
  維持。**ただし単独では落ちない gap ではない** — Phase B が通れば確実に落ちる。

---

## Phase D — achievability chain Eq.13.124 entropy-level 接続 📋

### スコープ

`IsLZ78AchievabilityChainHyp` (`LZ78FinalGlue.lean:118`):
`∀ᵐ ω, limsup(lz/n) ≤ limsup blockLogAvg` を greedy 実装について genuine 化。Ziv inequality の
本来形 `(1/n)·lz(X^n) ≤ blockLogAvg + (counting slack o(1))` を pmf-level で立て、limsup を取る。
**本 plan の measure-theoretic 最重部**。

### novel な自作補題 (statement 案)

```lean
/-- **Ziv inequality pmf-level (Cover-Thomas Eq.13.124 本体)**: 各 ω, n について
`(1/n)·lz_greedy(block_n ω) ≤ blockLogAvg μ p n ω + slack n`、
slack n = (c(n)/n)·log(...) → 0 (Phase B 経由)。
phrase 経験分布と P_n {block} の log の関係 (各 phrase の確率の積 ≤ block 確率)。 -/
theorem lz78_ziv_pmf_inequality
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) :
    (lz78GreedyImplEncodingLength n (p.blockRV n ω) : ℝ) / n
      ≤ blockLogAvg μ p n ω + lz78ZivSlack μ p n ω := ...

/-- **slack の a.s. 消失**: `lz78ZivSlack μ p n ω → 0` a.s. (Phase B counting + Real.log 比)。 -/
theorem lz78_ziv_slack_tendsto_zero
    (μ : Measure Ω) (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => lz78ZivSlack μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 0) := ...

/-- **achievability chain genuine 化**: pmf 不等式 + slack→0 で limsup を取る。 -/
theorem lz78GreedyImpl_achievabilityChainHyp
    (μ : Measure Ω) (p : ErgodicProcess μ α) :
    IsLZ78AchievabilityChainHyp μ p.toStationaryProcess
      (@lz78GreedyImplEncodingLength α _ _) := ...
```

### Done 条件

- Ziv pmf 不等式 genuine (各 phrase 確率の積 ≤ block 確率の log-likelihood 連結が核心)。
- slack a.s. → 0 genuine (Phase B 依存)。
- `IsLZ78AchievabilityChainHyp` greedy genuine。

### ステップ

- [ ] **D-1** phrase 経験分布 / per-phrase log-prob と block log-likelihood の連結
      (**Mathlib-shape-driven**: `MeasureTheory.Measure.map` push-forward + `blockLogAvg` shape)
- [ ] **D-2** Ziv pmf 不等式本体 `lz/n ≤ blockLogAvg + slack`
- [ ] **D-3** slack a.s. → 0 (Phase B counting)
- [ ] **D-4** limsup + `Filter.limsup_le_limsup` で chain genuine 化

### 工数感

**~250-400 行**。proof-log: yes (D-1/D-2 が pmf-level で最も重い)。

### リスク / 撤退ライン (L-AC4)

- **D-1/D-2 の pmf 連結が >300 行**: per-phrase 確率積 ≤ block 確率の measure-theoretic 連結
  (経験分布の定義 + push-forward + log-sum) が Mathlib 不在で肥大 → **L-AC4 撤退**:
  `IsLZ78AchievabilityChainHyp` を honest 仮定に残す。**段階着地: 「Eq.13.124 chain を仮定すれば
  headline は無仮定」(残り converse + h_bdd_above のみ genuine)**。

---

## Phase E — converse chain Eq.13.130 Kraft → a.s. liminf 接続 📋

### スコープ

`IsLZ78ConverseChainHyp` (`LZ78ConverseDischarge.lean:106`):
`∀ᵐ ω, liminf blockLogAvg ≤ liminf(lz/n)` を genuine 化。任意 prefix code の Kraft 下界
`E[length] ≥ H` を block-level (n→∞) で a.s.-pointwise に橋渡しする。**project 既存 Kraft 資産を
reuse**。

### 既存資産との接続点 (file:line)

- `ShannonCode.lean` `entropyD_le_expectedLength_of_kraft` / `kraftSum` — expectation-level 下界。
- `ShannonCodeKraftReverse.exists_prefix_code_of_kraft` — prefix code 存在。
- `LZ78ConverseDischarge.lean:201` `lz78_converse_lower_bound_pmfBased` — chain hyp + SMB liminf
  から結論を出す既存 genuine wrapper (本 Phase は chain hyp 自体を供給)。

### novel な自作補題 (statement 案)

```lean
/-- **codeword 長下界の pmf 形 (Cover-Thomas Eq.13.130)**: greedy LZ78 は prefix code なので、
各 block について `lz_length(block) ≥ -log P(block) - (定数)`、すなわち
`(lz/n) ≥ blockLogAvg - o(1)`。Kraft 不等式の pointwise 版。 -/
theorem lz78_kraft_pointwise_lower
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) :
    blockLogAvg μ p n ω - lz78ConverseSlack μ p n ω
      ≤ (lz78GreedyImplEncodingLength n (p.blockRV n ω) : ℝ) / n := ...

/-- **converse chain genuine 化**: pointwise 下界 + slack→0 で liminf を取る。 -/
theorem lz78GreedyImpl_converseChainHyp
    (μ : Measure Ω) (p : ErgodicProcess μ α) :
    IsLZ78ConverseChainHyp μ p.toStationaryProcess
      (@lz78GreedyImplEncodingLength α _ _) := ...
```

### Done 条件

- Kraft pointwise 下界 genuine (expectation-level Kraft の a.s.-pointwise 化が核心)。
- `IsLZ78ConverseChainHyp` greedy genuine。

### ステップ

- [ ] **E-1** greedy LZ78 が prefix code (uniquely decodable) であることの利用 (Kraft 前提)
- [ ] **E-2** Kraft expectation 下界 → block pointwise 下界の変換 ← **核心**
      (`entropyD_le_expectedLength_of_kraft` reuse 可否を M0 で確定)
- [ ] **E-3** slack a.s. → 0
- [ ] **E-4** liminf + `Filter.liminf_le_liminf` で chain genuine 化

### 工数感

**~200-350 行**。proof-log: yes (E-2 の Kraft 変換が核心)。

### リスク / 撤退ライン (L-AC5)

- **E-2 の expectation → a.s.-pointwise 変換が >300 行** (Kraft が block 全体の期待値でしか
  成立せず pointwise 化に大きな bridge): → **L-AC5 撤退**: `IsLZ78ConverseChainHyp` を honest
  仮定に残す。**段階着地: 「Eq.13.130 chain を仮定すれば headline 無仮定」**。
- **M0 で Kraft 既存資産が pointwise 化に追加 ~200 行要ると判明したら、Phase E を最後に回す**
  (achievability + h_bdd_above が先に落ちる方が headline の honest 仮定数を減らせる)。

---

## Phase F — headline 無仮定 publish 📋

### スコープ

Phase C + D + E がすべて genuine discharge できた場合、
`lz78_two_sided_optimality_greedy_impl_unconditional` を **ergodic process + finite alphabet
のみ** で publish。`lz78_two_sided_optimality_greedy_impl` (`LZ78FinalGlue.lean:335`) に
- `h_achiev := lz78GreedyImpl_achievabilityChainHyp` (Phase D)
- `h_converse := lz78GreedyImpl_converseChainHyp` (Phase E)
- `h_bdd_above := lz78GreedyImpl_isBoundedUnder_le` (Phase C)
- `h_bdd_below := lz78GreedyImpl_isBoundedUnder_ge` (既存 `:311`)
を供給するだけ。

### Done 条件

- 無仮定 headline 0 sorry / 0 warning publish。
- 段階着地時 (一部 Phase 撤退): 残った honest 仮定を **正直に明記** した中間 headline を publish
  (例: `..._converse_hyp_only` = converse のみ仮定)。

### 工数感

**~50-150 行**。proof-log: no (合流のみ)。

---

## Phase V — `InformationTheory.lean` 編入 + roadmap 更新 📋

- [ ] 新規 file (`LZ78ZivCountingBody.lean` / `LZ78AchievabilityChain.lean` /
      `LZ78ConverseChain.lean`) の import を `InformationTheory.lean` に追記。
- [ ] 各 file `lake env lean` clean 確認。
- [ ] `docs/textbook-roadmap.md` Ch.13 行を 🟡 → 🟢 (full closure 達成時) or honest 仮定数を更新。

**工数感**: ~10-30 行。proof-log: no。

---

## 撤退ライン (本 plan — L-AC シリーズ)

| ID | 対象 | 発動条件 | 撤退後の着地 |
|---|---|---|---|
| **L-AC1** | 真の greedy 実装差し替え (Phase A) | distinct 不変量証明 >300 行 | one-symbol 維持 + (★) honest 仮定。achievability/converse のみ部分 |
| **L-AC2** | (★) `c·log c≤Kn` (Phase B) | counting 不等式 >300 行 | `IsZivCountingMulLogBound` honest 仮定。「(★) 仮定すれば genuine」着地 |
| **L-AC3** | `h_bdd_above` (Phase C) | Phase B 未達で自動 | h_bdd_above honest 仮定維持 (単独 gap ではない) |
| **L-AC4** | achievability chain Eq.13.124 (Phase D) | pmf 連結 >300 行 | `IsLZ78AchievabilityChainHyp` honest 仮定。converse + h_bdd_above のみ genuine |
| **L-AC5** | converse chain Eq.13.130 (Phase E) | Kraft a.s. 化 >300 行 | `IsLZ78ConverseChainHyp` honest 仮定。achievability + h_bdd_above のみ genuine |

**撤退の独立性**: 5 Phase は **互いに独立に撤退可能**。Phase D (achievability) と Phase E
(converse) は別ファイル・別仮定で、片方が撤退しても他方は genuine で publish できる。最悪でも
**SMB sandwich + greedy 構成 + (片側 chain) は genuine で残り、headline の honest 仮定数を
3 → 1〜2 に確実に減らせる**。

---

## 当面の next step

1. **Phase 0 / M0** — 既存 genuine 状態固定 (本 plan に Read 済反映済) + greedy 差し替え判定
   + Kraft reuse 在庫。inventory 追補項目を orchestrator に提示。
2. **Phase A** — 真の longest-prefix greedy 実装差し替え (最深部、distinct 不変量) ← 着手起点。
3. **Phase B** — (★) counting genuine 供給。
4. **Phase C** — h_bdd_above genuine discharge (Phase B 依存)。
5. **Phase D / Phase E** — achievability / converse chain (独立、並行可)。
6. **Phase F / Phase V** — 無仮定 headline + 編入。

**並行実行の余地**: Phase D と Phase E は別ファイル・独立仮定なので並列 agent で同時着手可。
Phase A → B → C は逐次依存。

---

## 参照

- 親 seed: [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md)
- 兄弟 discharge: [`lz78-ziv-inequality-discharge-moonshot-plan.md`](./lz78-ziv-inequality-discharge-moonshot-plan.md)
- 既存 genuine 資産 (file:line):
  - `InformationTheory/Shannon/LZ78SMBSandwich.lean:388` — `lz78_smb_sandwich_ergodic` (無条件 SMB)
  - `InformationTheory/Shannon/LZ78ZivInequality.lean:204` — `card_phraseSet_le_pow` (counting Nat genuine)
  - `InformationTheory/Shannon/LZ78PhraseCountAsymptoticBody.lean:107` — `isBigO_natCast_div_log_of_mul_log_le` (inversion genuine)
  - `InformationTheory/Shannon/LZ78GreedyParsingImpl.lean:233, :277, :311` — greedy parse / count=n / bdd_below genuine
  - `InformationTheory/Shannon/LZ78ConverseDischarge.lean:106, :201` — `IsLZ78ConverseChainHyp` / pmfBased wrapper
  - `InformationTheory/Shannon/LZ78FinalGlue.lean:118, :385` — `IsLZ78AchievabilityChainHyp` / headline
- Kraft reuse 候補: `InformationTheory/Shannon/ShannonCode.lean` (`entropyD_le_expectedLength_of_kraft`,
  `kraftSum`), `InformationTheory/Shannon/ShannonCodeKraftReverse.lean`

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

0. **(2026-05-21) 本 plan 起草: full closure 狙い、連続 Mathlib gap なし確定** — 既存 Body 全 8
   ファイルを Read で確認した結果、headline `lz78_two_sided_optimality_greedy_impl_bdd_below_free`
   (`LZ78FinalGlue.lean:385`) が残す 3 honest 仮定はすべて **離散・組合せ・実解析** で、連続
   measure-theoretic な Mathlib gap (積分・Radon-Nikodym 等の壁) は無い。SMB sandwich は無条件
   genuine、inversion `(★)⟹c=O(n/log n)` も genuine 済。**ゆえに複数セッションかければ full
   closure 可能** と判定 (詳細は最終要約)。

1. **(2026-05-21) Phase A が最深部 = 実装差し替え必須と確定** — 現 `lz78GreedyParseAux`
   (`LZ78GreedyParsingImpl.lean:192`) は **one-symbol-per-step** 近似で `count = n`
   (`lz78GreedyParse_count` `:277`)。この実装では (★) `c·log c ≤ Kn` が **数学的に false**
   (`c=n` で `n log n ≤ Kn` 不成立)。(★) を genuine に成立させるには **真の longest-prefix-match
   greedy への差し替え + distinct phrase 不変量** が必須。これが本 plan の最重リスクであり、
   着手起点 (Phase A)。撤退時 (L-AC1) は one-symbol 維持で (★) を honest 仮定に残す段階着地。

2. **(2026-05-21) 新規述語を導入せず既存 chain hyp を greedy について genuine 化する方針** —
   `IsLZ78AchievabilityChainHyp` / `IsLZ78ConverseChainHyp` は既に `Prop := True` ではなく
   genuine な limsup/liminf 不等式。本 plan はこれらの **body を満たす定理を greedy 実装について
   証明し headline 引数から外す** (述語定義は一切変えない)。これにより `LZ78FinalGlue.lean` /
   `LZ78ConverseDischarge.lean` の下流が型エラーなしに無仮定 headline へ繋がる。

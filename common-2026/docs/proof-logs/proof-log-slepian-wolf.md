# Slepian–Wolf 単発 converse Lean 形式化 — ボトルネック分析

Slepian–Wolf single-shot converse ムーンショット (`docs/shannon/slepian-wolf-moonshot-plan.md`) の Phase A〜C を 1 セッションで完走した記録。質的観察中心 (CLAUDE.md `proof-log` 規約準拠)。

## 0. 対象問題と成果物

Cover & Thomas, 15.4 の single-shot 形:

```
2 ソース (Xs, Ys) : Ω → α × β を独立 encoder eX, eY で圧縮、joint decoder dec で復号。
Pe ≤ ε のもとで:
  log Mx        ≥ H(X | Y)   - h(Pe_X) - Pe_X · log(|α| - 1)
  log My        ≥ H(Y | X)   - h(Pe_Y) - Pe_Y · log(|β| - 1)
  log Mx+log My ≥ H(X, Y)    - h(Pe)   - Pe   · log(|α × β| - 1)
```

成果物:

- `Common2026/Shannon/SlepianWolf.lean` — 511 行、0 errors / 0 sorry
  - Phase A: `entropy_le_log_card`、`fano_inequality_with_side_info`、`entropy_ge_condEntropy`、`condEntropy_nonneg` (新規 helper)
  - Phase B: `slepian_wolf_converse_X / _Y / _sum`
  - Phase C: `slepian_wolf_converse_single_shot` (3 bound `And` 統合)
- `Common2026.lean` に `import Common2026.Shannon.SlepianWolf` 追記

`lake env lean Common2026/Shannon/SlepianWolf.lean` silent、`lake build` 全体緑通過。

## 1. 質的観察 3 点

### (A) 「条件付き chain rule の山場」が `condMutualInfo` 経由で蒸発

計画 (Phase B-3) は X bound 派生で「`H(X, Z | Y) = H(Z | Y) + H(X | Y, Z)` (条件付き chain rule)」を新規補題 ~50 行で立てる必要がある、と見積もっていた。

実際に書き始めて気付いたのは、**既存 `condMutualInfo_eq_condEntropy_sub_condEntropy` が `H(X | Y) - H(X | Y, Z) = (condMI X Z Y).toReal` を提供しており、`condMutualInfo_comm` で `(condMI X Z Y) = (condMI Z X Y)` に swap できる** こと。これで:

```
H(X | Ys) - H(X | Ys, EX) = H(EX | Ys) - H(EX | Ys, Xs) ≤ H(EX | Ys) ≤ H(EX) ≤ log Mx
```

の 5 段が、新規補題 `condEntropy_nonneg` 5 行のみで通る。**条件付き chain rule という新規補題そのものを書かずに済んだ**。

なぜ重要か: 「定義 A の chain rule」を新たに書き下すと、measurability + integrability + Tonelli の plumbing で 50 行はかかる。一方「同等の identity を別経路で組み立てる」と既存 5 行で済むことがある。**Mathlib 既存 API で「同等変形」を探す習慣** が、新規補題コストを 1/10 に圧縮しうる。

### (B) 「conditioner の order」 が証明の plumbing コストを支配する

side info Fano wrapper を書いたとき、`fano_inequality_with_side_info μ Xs Yo Si decoder` の paired conditioner は `(Yo, Si)` の順で固定した。これにより利用側 (X bound) で `Yo := Ys, Si := EX` と渡せば conditioner `(Ys, EX)` が得られ、`condMutualInfo_eq_condEntropy_sub_condEntropy μ Xs Ys EX` の RHS `H(X | Ys, EX)` (= `condEntropy μ Xs (fun ω => (Ys ω, EX ω))`) と **直接マッチ**する。

最初は theorem 文を `(eX (Xs ω), Ys ω)` 順 (= `(EX, Ys)`) で書いていて、Fano は `(Ys, EX)` を返すため prodComm 経由で order swap が必要になった。`condEntropy μ Xs (Ys, EX) = condEntropy μ Xs (EX, Ys)` の証明は condDistrib の MeasurableEquiv 不変性を要し、~30 行 + 2 sorry になりそうだった。

**そこで theorem 文の Pe_X を `(Ys, EX)` 順に書き換え**、Fano / bridge / 主張の 3 者で conditioner 順を一貫させた。これで swap 不要、proof body 60 行に収束。

教訓: **plumbing-heavy な定理では、定理文の引数順 / pair 順を「証明で使う既存補題の順」に合わせる** のが最も安い。「教科書の表記」に律儀に合わせると plumbing 30 行を払うことになる。CLAUDE.md「Mathlib-shape-driven Definitions」の延長で、**定理文も Mathlib-shape-driven** にすべき。

### (C) `entropy_le_log_card` (任意 μ 版) の Mathlib・project 不在、Jensen で 50 行

Mathlib `Mathlib.InformationTheory.KullbackLeibler.*` には Gibbs 不等式 (`klDiv ≥ 0`) はあるが、それを「`entropy ≤ log |α|`」に翻訳した補題は不在。Common2026 にも `entropy_le_log_image_card` (uniform 専用、`Common2026/Shannon/LoomisWhitney.lean:125`) しか無い。

**戦略採用**: uniform 版の証明を写経し、uniform 仮定だけ落とす。具体的には `Real.concaveOn_negMulLog` を `Fintype.univ` 全域で `ConcaveOn.le_map_sum` に適用、weights = `1 / N`、mean = `(∑ p) / N = 1 / N` (∑ p = 1 from `IsProbabilityMeasure`)、`negMulLog (1/N) = log N / N` で整形。50 行で通った。

引っかかりポイント: `simp [Fintype.card]` で `Fintype.card.eq_1` が looping。`rw [Finset.card_univ]` 直接呼びに変えて回避 (1 行差し替え)。

将来の refactor 候補: `entropy_le_log_image_card` をこの一般版から導出する形に再構成すれば LoomisWhitney.lean 側も短くなる。だが今回は時間優先で別補題として並列維持。

## 2. ピボット履歴

1. **X bound 派生ルートを `condMutualInfo` 経由に切り替え** (山場の条件付き chain rule を回避)
2. **theorem 文の conditioner 順を `(Ys, EX)` に固定** (prodComm swap の 30 行を回避)
3. **`condEntropy_nonneg` を新規追加** (~5 行、Mathlib・project 不在)

## 3. 工数感 (実績)

| Phase | 計画見積 | 実績 |
|---|---|---|
| Phase A (entropy_le_log_card + Fano wrapper + helpers) | 80〜120 行 | 約 130 行 |
| Phase B (X / Y / sum bound) | 150〜250 行 | 約 230 行 (うち統合形 60 行) |
| Phase C (統合形) | 50〜80 行 | 約 60 行 |
| **合計** | **280〜450 行** | **511 行** |

シード見積 (400〜600 行) のレンジ上端、インベントリ後見積 (280〜450 行) のやや上。Phase C 統合形を `slepian_wolf_converse_single_shot_X / Y / sum` 3 個別 + tuple 化したため、tuple 部分の docstring / 引数列で 60 行使った。

## 4. 詰まらなかった理由 (寄与の大きい既存資産)

- `Common2026/Shannon/Bridge.lean` の `mutualInfo_eq_entropy_sub_condEntropy` (588 行投入済)
- `Common2026/Shannon/Entropy.lean` の `condMutualInfo_eq_condEntropy_sub_condEntropy` + `condMutualInfo_comm` (条件付き chain rule の代替)
- `Common2026/Fano/Measure.lean` の `fano_inequality_measure_theoretic` (Yo 引数の任意 MeasurableSpace 性が paired conditioner ルートの根拠)
- `Common2026/Shannon/LoomisWhitney.lean` の `entropy_le_log_image_card` (証明テンプレを写経できた)

これらが揃っていなかったら Phase B だけで数日かかる規模。**「依存資産が手に入ったタイミング」が新規 moonshot の着手判定に最も効く** という観察は、Han / Loomis-Whitney の各 proof-log でも同様に出ている。

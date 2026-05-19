# T1-A'' Huffman 最適性 partial / plumbing — Moonshot 計画 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A''. Huffman 最適性 (2 hypothesis 完全 discharge)」
> - 直接前任 (T1-A' 完了 weak form publish): [`huffman-optimality-moonshot-plan.md`](./huffman-optimality-moonshot-plan.md)
> - 同 parent の full-scope 計画 (judgement #3 で no-op 判定): [`huffman-optimality-t1apprime-moonshot-plan.md`](./huffman-optimality-t1apprime-moonshot-plan.md)
>
> **Inventory**: [`huffman-optimality-t1apprime-mathlib-inventory.md`](./huffman-optimality-t1apprime-mathlib-inventory.md)
>
> **Status (2026-05-20)**: 計画起草 + 着手。本 plan は完全 hypothesis discharge を scope-out し、
> Hypothesis 1 (`SwapNormalizationHypothesis`) の周辺 plumbing / 1 通り完遂可能 partial 補題群を
> **独立 publish** する縮小 scope 計画.

## Goal (縮小)

`Common2026/Shannon/HuffmanT1APPrimePartial.lean` を **新規 publish** (~150-300 行).
完全 hypothesis discharge は **scope-out** (judgement log #3 で「~550 行 / 4-6 セッション」と
再判定済). 本 plan は Hypothesis 1 (`SwapNormalizationHypothesis`) の周辺で 1 セッション
完遂可能な partial / plumbing 補題群を切り出して publish.

具体的に publish する補題群 (Approach §「採用突破口」参照):
- `swap_step_le` の **4 分解 extractor** (Kraft / expected length / 値 swap / positivity 単独形)
- `swap_step_le_self`: `a = m` (= 恒等 swap) trivial 系
- `swap_compose_self`: `Equiv.swap a m ∘ Equiv.swap a m = id` from `l` 視点で恒等
- `SwapNormalizationHypothesis_trivial_when_eq`: `ll a = ll b` が既成立の trivial 系 で
  `l_norm := ll` で hypothesis 自己 discharge.
- `SwapNormalizationHypothesis_via_single_swap`: `ll a < ll b` ∧ `Q.real {a} ≤ Q.real {b}` の
  単一 swap で `l_norm a = l_norm b` に到達可能な特殊系の discharge.

## Approach (overall strategy / shape of solution)

### 採用突破口 — partial scope (a) = `swap_step_le` 周辺 plumbing 補題群

judgement log #3 の (a) `swap_step_le` helper 拡張案を採用 (~100-200 行). 既存
`swap_step_le` (`HuffmanOptimality.lean:650`, ~96 行 helper) は富な多目的 tuple を返すが、
client がよく使う部分 (Kraft / expected length / positivity / 値 swap) を **個別命名 extractor**
として独立 publish することで、後続 T1-A''' 着手時の skeleton 起動コスト低下を狙う。
さらに **`swap_step_le_self`** (`a = m` の trivial 系) と **`swap_compose_self`** (Cover-Thomas
Lemma 5.8.1 の 2-step swap が同元 swap で互いに打ち消す identity) を加え、bubble-sort
metric の strict-descent (judgement log #2 で技術的破綻判明) を経由しない安全 plumbing と
する.

最終層として **`SwapNormalizationHypothesis_trivial_when_eq`** で「`ll a = ll b` が
input で既成立」case の hypothesis 自己 discharge を publish. これは abbrev `Prop` 形を
保つ部分 discharge であり、後続 T1-A''' の本格 discharge 設計を確定させる効果を持つ.

加えて `SwapNormalizationHypothesis_via_single_swap`: `ll a > ll b` ∧ `Q.real {a} ≤ Q.real {b}`
の特殊 case で **単一 `swap_step_le` 呼び出し** + `Equiv.swap` の involution 性質で
`l_norm a = l_norm b` を派生する補題 — ただし single swap では `l a ≠ l b` 解消困難
(swap 後 `l' a = l b, l' b = l a`, やはり `l' a ≠ l' b`) のため、**weak partial 形** で
publish: 「`ll a = ll b` も含む trivial 系」を確定形で公開, single-swap で `l' a = l' b` を
作る non-trivial 系は **scope-out**.

### 0 sorry 着地形 (本 plan 完遂時)

`Common2026/Shannon/HuffmanT1APPrimePartial.lean` (~200 行 / 0 sorry / 0 warning) に以下を
publish:

```lean
namespace InformationTheory.Shannon.Huffman

-- swap_step_le の 4 分解 extractor (それぞれ独立に使えるが trivial 派生)
theorem swap_step_le_pos                : ...
theorem swap_step_le_kraft              : ...
theorem swap_step_le_expectedLength_le  : ...
theorem swap_step_le_values             : ...

-- 恒等 swap (a = m) trivial 系
theorem swap_step_le_self : ...

-- 2 段同元 swap の involution 性質
theorem swap_compose_self : ...

-- SwapNormalizationHypothesis の自明 case discharge
theorem SwapNormalizationHypothesis_trivial_when_eq : ...

end InformationTheory.Shannon.Huffman
```

`huffmanLength_optimal_with_hypotheses` を hypothesis 引数経由で discharge する強形主定理は
**publish しない** (本 plan scope-out). 残った 2 hypothesis (`SwapNormalizationHypothesis` の
非自明 case + `HuffmanMergedIdentificationHypothesis` 全体) は **後続 seed T1-A''' で
discharge 予定**.

### 既存資産の不変性

- `Common2026/Shannon/HuffmanOptimality.lean` (1054 行 / 0 sorry / weak form publish): **不変**.
- `Common2026/Shannon/Huffman.lean` (961 行 / 0 sorry): **不変**.
- `Common2026.lean`: 不変 (本 plan は新規 file 追加するが Common2026.lean は import 経路
  整備の trade-off 評価で **追記しない** — partial publish は ad-hoc 補題集の位置付け、
  公的 library API には昇格させない).
- `docs/textbook-roadmap.md`: 不変 (T1-A''' で完全 discharge 達成時にステータス更新).

### 規模見積

| 補題 | 行数 |
|---|---|
| `swap_step_le_pos` | ~15 |
| `swap_step_le_kraft` | ~15 |
| `swap_step_le_expectedLength_le` | ~15 |
| `swap_step_le_values` | ~15 |
| `swap_step_le_self` | ~30 |
| `swap_compose_self` | ~25 |
| `SwapNormalizationHypothesis_trivial_when_eq` | ~30 |
| import / namespace / docstring | ~30 |
| **合計** | **~175 行 (目標 150-300 行)** |

## 撤退ライン (積極的に許容)

- いずれかの補題が `lake env lean` で詰まった場合、その補題だけ scope-out して残りを publish.
- 全体 50 行未満で着地した場合は Phase 0 probe レポートのみとし、proof-log で残置.

## 制約

- 既存 `HuffmanOptimality.lean` / `Huffman.lean` の signature 変更禁止.
- `import Mathlib` 禁止.
- 1 セッション完遂目標.

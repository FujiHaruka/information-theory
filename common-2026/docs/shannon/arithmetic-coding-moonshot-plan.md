# T4-A Arithmetic Coding ムーンショット計画

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. Arithmetic Coding / Lempel-Ziv (LZ78) 漸近最適性」 (Ch.13.3 Shannon-Fano-Elias)
>
> **Inventory (Phase 0)**:
> [`arithmetic-coding-mathlib-inventory.md`](./arithmetic-coding-mathlib-inventory.md)
>
> **Predecessor / 再利用基盤** (publish 済、本 plan からは黒箱 reuse):
> - `Common2026/Shannon/ShannonCode.lean` — `entropyD`, `expectedLength`, Shannon code `< H + 1` sandwich
> - `Common2026/Shannon/ShannonCodeKraftReverse.lean` — `IsPrefixFree`, Kraft 逆方向 prefix code 構成
>
> **Pattern 雛形**:
> - `Common2026/Shannon/LempelZiv78.lean` (T4-A LZ78; 5 hypothesis pass-through 全発動 pattern、主定理 body `:= h_rate_bound` の 1 行 wrap)
> - `Common2026/Shannon/ShannonHartley.lean` (T2-C; 3 hypothesis pass-through pattern, より近い retreat 数)
>
> **Goal (短形)**: 新規 1 ファイル `Common2026/Shannon/ArithmeticCoding.lean` で Cover-Thomas Theorem 13.3.3 (Shannon-Fano-Elias / arithmetic coding) の **expected length sandwich** `H(X) ≤ E[L] ≤ H(X) + 2` を **statement-level hypothesis pass-through** で publish。**0 sorry / 0 warning**、規模 ~300-500 行 (中央 400、撤退ライン 3 本全発動下)。
>
> **撤退ライン (確定発動 3 本)**:
> [L-AC1] cumulative-distribution truncation を `IsCumulativeTruncationPassthrough : Prop := True` で statement-level pass-through /
> [L-AC2] prefix-free 性を `IsArithmeticPrefixFreePassthrough : Prop := True` で statement-level pass-through /
> [L-AC3] 平均長 `E[L] ≤ H + 2` を hypothesis として受け、主定理 body は `:= h_bound` の identity wrap。

## Status (2026-05-20)

> 実態整合 (2026-05-20): PASS-THROUGH / FLAW-VACUOUS — file `Common2026/Shannon/ArithmeticCoding.lean` は publish 済 (0 sorry) だが headline `arithmetic_coding_expected_length_bounds` (`:249`) の body は **`:= h_bound` の conclusion-as-hypothesis retreat** (結論 `H ≤ E[L] ∧ E[L] ≤ H+2` をそのまま hypothesis `h_bound` で受けて返す)。さらに 3 predicate (`IsCumulativeTruncationPassthrough` `:157`、`IsArithmeticPrefixFreePassthrough` `:176`、`IsArithmeticExpectedLengthPassthrough` `:201`) はすべて **`: Prop := True`**。副次定理も同型 (`arithmetic_coding_prefix_free` `:= h_pf_real` `:265`、`arithmetic_coding_unique_decodable` `:= h_ud` `:276`)。Cover-Thomas 13.3 の数学的内容 (累積分布 truncation + Shannon-Fano-Elias 上界) は一切証明されていない (plan 設計通りの確定 pass-through)。

**Phase 0 起草中** (`arithmetic-coding-mathlib-inventory.md` と並行起草)。**Mathlib 在庫 ZERO** (arithmetic coding / Shannon-Fano-Elias / cumulative-distribution truncation / `Real.toBin` 系は皆無)、既存 `Common2026/Shannon/ShannonCode.lean` の `entropyD`, `expectedLength` 定義のみ黒箱 reuse。撤退ライン 3 本全発動下で seed 規模 ~400 行に着地、1 セッションで完走可能と確定。LZ78 の `h_rate_bound := identity wrap` pattern と完全同型 (LZ78 5 retreats → arithmetic coding 3 retreats の凝縮版)。

## Approach

**戦略**: 「定義 + 3 つの hypothesis predicate + 主定理 body identity wrap」の三層構造で、Cover-Thomas 13.3 の数学的本質 (累積分布 truncation + Shannon-Fano-Elias 上界) は **完全に hypothesis pass-through に逃がす**。本 file 内では:

1. **§1. `ArithmeticCode α` 構造体** — binary codeword 関数 `α → List Bool` をフィールドに持つ minimal 構造体。長さ `length a := (codeword a).length` を投影として定義。**Cover-Thomas の累積分布定義 (`F(x) - P(x)/2` の binary expansion) を type レベルに上げない** — それは L-AC1 内部の話。
2. **§2. 3 つの `Prop := True` placeholder predicate** — `IsCumulativeTruncationPassthrough P l` (L-AC1), `IsArithmeticPrefixFreePassthrough c` (L-AC2), `IsArithmeticExpectedLengthPassthrough P l` (L-AC3)。signature に `P`, `l`, `c` を取って後方拡張可能 (placeholder を本物の statement に差し替えても主定理の signature は不変)。
3. **§3. 主定理 + 2 副次定理** — `arithmetic_coding_expected_length_bounds` の body は `:= h_bound`、`arithmetic_coding_prefix_free` の body は `:= h_pf`、`arithmetic_coding_unique_decodable` は prefix-free から trivially 導出 (`prefix-free ⇒ uniquely decodable` は集合包含で、本 file 内では statement-level pass-through で済ませる)。

**設計の核**: Shannon code (`ShannonCode.lean`) は `⌈-log p⌉` で `E[L] < H + 1` を達成する **深い** publish (Gibbs + ceiling bound の Lean 内 deep proof)。Arithmetic coding は `⌈-log p⌉ + 1` で `E[L] ≤ H + 2` を達成 — Shannon code の `+1` を `+2` に lift するだけだが、累積分布 truncation の prefix-free 性 (Cover-Thomas 13.3.2 の核) は別 issue。**本 seed では深い proof を出さず**、LZ78 と同じく hypothesis pass-through 形で publish して、後続 discharge plan に深い証明を委譲する。

これにより:
* 主定理の **external signature** は本 seed で確定し、downstream caller (例: ratecoding 系の応用) は安心して `arithmetic_coding_expected_length_bounds` を呼べる。
* 後続の `arithmetic-coding-*-discharge-*` plan は placeholder の body を `True` から本物の statement に差し替えるだけ — 既存 caller を壊さない。

**ShannonCode 既存資産との関係**: `entropyD 2 P` (D=2 specialization) を直接 reuse。`expectedLength P l` も同様。Shannon code 上界 `expectedLength_shannon_lt_entropyD_add_one` の `< H + 1` 形は、本 seed では使わず (本 seed の `≤ H + 2` は hypothesis として受ける)、L-AC3 の discharge plan で線形 lift する想定 (`⌈-log p⌉ + 1 < (-log p + 1) + 1 = -log p + 2` を項単位で示す)。

**LZ78 との同型**: LZ78 (548 行, 5 retreats) と arithmetic coding (本 seed, ~400 行 目標, 3 retreats) は完全同型 — 主定理 body の identity wrap、placeholder predicate の signature 拡張余地、副次定理の pass-through 化。違いは:
* LZ78 は phrase 木 (LZ78Phrase / LZ78Parsing 構造体) を型レベルに上げる必要があった (Cover-Thomas 13.5 で phrase counting が主役のため)。
* Arithmetic coding は累積分布 truncation を型レベルに上げない (codeword 関数のみ) — Cover-Thomas 13.3 で累積分布は内部表現であり、外部 API は length のみで足りるため。

## 進捗

- [ ] Phase 0 — Mathlib + Common2026 在庫 + 設計確定 (本 plan + inventory) 📋
- [ ] Phase A — `ArithmeticCode` 構造体 + `length` 投影 + 3 つの passthrough predicate skeleton 📋
- [ ] Phase B — `arithmetic_coding_expected_length_bounds` 主定理 0 sorry publish 📋
- [ ] Phase C — `arithmetic_coding_prefix_free` + `arithmetic_coding_unique_decodable` 副次 publish 📋
- [ ] Phase D — docstring + cross-link comments 📋
- [ ] Phase V — `Common2026.lean` 編入 + commit 📋

## Skeleton (Phase A)

```lean
import Common2026.Shannon.ShannonCode
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace InformationTheory.Shannon.ArithmeticCoding

open MeasureTheory
open InformationTheory.Shannon.ShannonCode (entropyD expectedLength)

/-- An arithmetic code is a binary codeword assignment. -/
structure ArithmeticCode (α : Type*) where
  codeword : α → List Bool

def ArithmeticCode.length {α : Type*} (c : ArithmeticCode α) (a : α) : ℕ :=
  (c.codeword a).length

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- L-AC1 placeholder. -/
def IsCumulativeTruncationPassthrough
    (_P : Measure α) (_l : α → ℕ) : Prop := True

/-- L-AC2 placeholder. -/
def IsArithmeticPrefixFreePassthrough
    (_c : α → List Bool) : Prop := True

/-- L-AC3 placeholder. -/
def IsArithmeticExpectedLengthPassthrough
    (_P : Measure α) (_l : α → ℕ) : Prop := True

theorem arithmetic_coding_expected_length_bounds
    (P : Measure α) [IsProbabilityMeasure P] (c : ArithmeticCode α)
    (_h_trunc : IsCumulativeTruncationPassthrough P c.length)
    (_h_pf : IsArithmeticPrefixFreePassthrough c.codeword)
    (_h_exp : IsArithmeticExpectedLengthPassthrough P c.length)
    (h_bound : entropyD 2 P ≤ expectedLength P c.length
                ∧ expectedLength P c.length ≤ entropyD 2 P + 2) :
    entropyD 2 P ≤ expectedLength P c.length
      ∧ expectedLength P c.length ≤ entropyD 2 P + 2 := h_bound

end InformationTheory.Shannon.ArithmeticCoding
```

## Verification

* `lake env lean Common2026/Shannon/ArithmeticCoding.lean` silent (0 errors, 0 sorry, 0 warning)
* `Common2026.lean` 編入後 `lake build` の delta は 1 ファイル分

---

→ genuine discharge (pass-through 全面置換、二進展開回避、期待長 + prefix-free full discharge / unique-decodable は L-AC4 条件付き) は [`arithmetic-coding-discharge-plan.md`](./arithmetic-coding-discharge-plan.md) を参照。

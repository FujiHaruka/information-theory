import InformationTheory.Shannon.AEP.Basic.Core
import InformationTheory.Shannon.AEP.Basic.Converse
import InformationTheory.Shannon.AEP.Basic.Achievability

/-!
# AEP — Asymptotic Equipartition Property (Phase A〜C)

漸近等分配性の形式化。Cover-Thomas 教科書 Theorem 3.1.1〜3.1.2 の Phase A〜C
(AEP 本体 + typical set の 3 主定理) をスコープとし、Phase D / E (源符号化定理)
は別ファイル。

## 構成

* **Phase A** — i.i.d. 列 `Xs : ℕ → Ω → α` から block `jointRV : Ω → (Fin n → α)`
  の定義 + 基本 measurability
* **Phase B** — probability AEP:
  `(1/n) ∑ i, (-Real.log ((μ.map (Xs 0)).real {Xs i ω}))` が `entropy μ (Xs 0)`
  に a.s. / 確率収束 (`strong_law_ae_real` を `Y i := −log P(Xs i ω)` で適用)
* **Phase C** — typical set `T_ε^n` の measurability + size bound + 確率 → 1

## i.i.d. 仮定の流儀

Mathlib に `IsIID` predicate は無いため、`strong_law_ae_real` と同じ 2 仮定形
`Pairwise (fun i j => Xs i ⟂ᵢ[μ] Xs j)` + `∀ i, IdentDistrib (Xs i) (Xs 0) μ μ`
を直接受ける。`(· ⟂ᵢ[μ] ·) on Xs` 形の `(· · ·)` anonymous lambda は `on` と
組み合わさったときに parsing 失敗するので、明示的な `fun i j => …` で書く。

## 撤退ライン (本シード)

Phase A〜C 緑通過 = AEP 単体 publish ライン。Phase D / E は次セッション。
-/


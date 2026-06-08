import InformationTheory.Shannon.ConditionalMethodOfTypes.Core
import InformationTheory.Shannon.ConditionalMethodOfTypes.Mass

/-!
# Conditional method of types — `conditionalStronglyTypicalSlice_mass_ge`

タスク: rate-distortion strong achievability (Phase 3) を unblock するための
**Cover-Thomas 10.6.1 (method-of-types, conditional form)** publishable form。

For a fixed X-strongly-typical `x : Fin n → α`, lower-bound the Y-product mass of
the conditional strongly-typical slice
`{y | (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε}` under `μ_Y^n`:

  `exp(-n · (entropy μ (Z₀) - entropy μ (X₀) + slack))
     ≤ (Measure.pi (μ.map (Ys 0))^n).real (conditionalStronglyTypicalSlice ...)`

ここで `entropy μ Z₀ - entropy μ X₀ = H(Y|X)` (条件付きエントロピー、joint - marginal
の chain-rule 形)、`slack = O(ε)`。

## 戦略

直接の経路 (Cover-Thomas 10.6.1) は **conditional type-class** を中心にした multinomial
counting。本ファイルは Phase A-E の inventory を確立 (定義 + 関連補題)。
最終 Phase E の per-x deterministic bound は次セッションでの assembly target として
statement のみ publish (sorry で残す)。

## 設計判断

* Final form expresses `H(Y|X)` as `entropy μ Z₀ - entropy μ X₀` (the chain-rule form),
  which is what the inventory comment in `RateDistortionAchievabilityPhaseEStrong.lean`
  promises and what downstream (rate-distortion achievability assembly) consumes.
* Avoids `mutualInfoOfChannel` reshape — that bridge is a separate concern.
-/

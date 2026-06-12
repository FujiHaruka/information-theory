# Birkhoff 個別エルゴード定理 a.s. 自前実装計画 (E-8'' 経路 A)

**Status**: CLOSED ✅ — headline `birkhoff_ergodic_ae` 完成 (標準 typeclass のみ: `IsProbabilityMeasure` + `MeasurePreserving` + `Ergodic` + `Integrable`、pass-through なし)。無条件 `shannon_mcmillan_breiman` への昇格も達成。
**SoT**: `docs/textbook-roadmap.md` Ch.4 (SMB / Birkhoff)。詳細履歴は git。

## 要点 (≤5 行)
- 経路 A (backward martingale 自前)。`Filtration` は `Preorder ι` 一般なので `ℕᵒᵈ` で型化し Mathlib `Martingale` 定義を借用。backward upcrossing 不等式は Mathlib forward 版の時刻反転写経が山場。
- ergodic discharge は `Ergodic.ae_eq_const_of_ae_eq_comp_ae` (`Dynamics/Ergodic/Function.lean`) で短く済む。
- `condExp_comp_T` (`𝔼[h|comap T m] ∘ T =ᵐ 𝔼[h∘T|m]`) は Mathlib 不在で自前、上流 PR 候補。

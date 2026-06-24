# T3-A Constrained Maximum Entropy ムーンショット計画 🌙

**Status**: CLOSED ✅ — `gibbsPmf` + `entropy_le_gibbs_of_constraints` (Tier 1 上界) + `entropy_eq_gibbs_iff_of_constraints` (Tier 2 一意性) を genuine publish。Tier 3 特例 (uniform / 2-point exponential / geometric) も達成。
**SoT**: `docs/textbook-roadmap.md` Ch.12。詳細履歴は git。

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-A. Constrained Maximum Entropy (Lagrange / exponential family)」

## 要点

- 設計の core: KKT / Lagrange duality は Mathlib 不在 (`LagrangeMultipliers.lean` で TODO)。これを回避し、Gibbs `klDivPmf ≥ 0` 直接ルート + 算術 identity で証明。`Measure.tilted` は使わず pmf 形 `gibbsPmf` (`exp⟨λ,f⟩ / Z`) で閉じる。
- 重力中心は核 identity `klDivPmf Q (gibbsPmf f λ) = -H(Q) - ⟨λ, 𝔼_Q[f]⟩ + log Z(λ)` の 1 本。Q := P と Q := gibbs の 2 回呼び出しで Tier 1 / Tier 2 が完結。
- ansatz `λ` は主定理 signature の hypothesis として外から取る (pass-through)。ψ(λ) 凸性 / Lagrange parameter の存在性は scope 外。
- Tier 2 一意性は strict convexity 経由ではなく `klFun_eq_zero_iff` の per-term 適用が直接で済んだ。

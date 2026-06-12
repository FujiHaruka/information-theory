# Cover & Thomas Ch.2 未形式化ギャップ closure 計画

**Status**: CLOSED ✅ — 充足統計量 (2.9) 新規実装 `SufficientStatistic.lean` (主定理 `mutualInfo_eq_of_sufficient` + Neyman-Fisher 因子分解同値、`@audit:ok`)。Gibbs/情報不等式 (2.6) と対数和不等式 (2.7) は既存資産への再リンクで closure。ch02 未形式化リストから 2.6/2.7/2.9 削除済。
**SoT**: `docs/textbook-roadmap.md` Ch.2 (基本 Entropy)。詳細履歴は git。

## 要点 (≤5 行)
- 2.9 は markov-form (`IsMarkovChain μ Xs (f∘Xs) θ`) で定義し、主定理は既存 DPI 資産 (`mutualInfo_le_of_postprocess` + `mutualInfo_le_of_markov` + `mutualInfo_comm`) の `le_antisymm` で閉じる。教科書因子分解形を直接 def 化すると 50〜100 行 bridge を誘発するので回避。
- 因子分解同値は当初 Mathlib 壁を予測したが壁ではなかった (2026-06-02): 密度でなく `condDistrib` の θ-非依存性 (β-form) でエンコードし、Mathlib condIndepFun ⟺ 各分解形補題の 3 段 chain で閉じた。唯一の追加前提は `[StandardBorelSpace Ω]`。壁判定を別エンコードで再確認した実例。

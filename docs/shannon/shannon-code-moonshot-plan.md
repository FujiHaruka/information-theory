# Shannon コード (B-8) ムーンショット計画 🌙

**Status**: CLOSED ✅ — 期待長 sandwich `H_D(P) ≤ E[L_Shannon] < H_D(P) + 1` (`shannonCode_expected_length_bounds` ほか Kraft 充足 / Gibbs 下界 / `⌈⌉` 上界) を genuine publish (語長水準)。Kraft 逆向き (prefix code 構成) は別 plan で完了 → [`shannon-code-kraft-reverse-plan.md`](./shannon-code-kraft-reverse-plan.md) (B-8')。
**SoT**: `docs/textbook-roadmap.md` Ch.5。詳細履歴は git。

## 要点

- 設計の core: prefix code の存在を仮定しない語長水準 (`α → ℕ`) で完結。Shannon 語長 `⌈-log_D P(x)⌉` の Kraft 充足は順向きに独立証明、`kraft_mcmillan_inequality` (Mathlib、`Finset (List α)` 形) は不要。
- Gibbs 下界は `Real.log_le_sub_one_of_pos` で Jensen / 積分を回避。D-ary log は `Real.logb D` で書き `log D` 因子を局所化。
- support 仮定: 下界 (Phase C) は full support 不要 (`P(a)=0` 項は 0 で消える)。上界 (Phase D、厳密不等式) は `∀ a, P(a) > 0` が本質的に必要。

# Stein 補題 converse (Phase C/D) ムーンショット計画 🌙

**Status**: CLOSED ✅ — Stein converse + `stein_lemma` を liminf/limsup sandwich 形 (`K ≤ liminf ∧ limsup ≤ K/(1-ε)`) で discharge。Pi 化 KL chain rule `klDiv_pi_eq_n_smul` + DPI + log-sum 下界 + sInf squeeze の 3 層。
**SoT**: `docs/textbook-roadmap.md` Ch.11。詳細履歴は git。
> **親 plan**: [`stein-moonshot-plan.md`](stein-moonshot-plan.md) — Phase A〜B (achievability) は親で完了、Phase C/D を本 plan に切り出し。

## 要点 (任意)
- strict `Tendsto → K` 形は strong converse を要し本経路では構造的に不可 → strong 版は [`strong-stein-moonshot-plan.md`](strong-stein-moonshot-plan.md) で別途達成。
- `klDiv_pi_eq_n_smul` (i.i.d. 設定の汎用 chain rule) は Mathlib 上流 PR 候補。

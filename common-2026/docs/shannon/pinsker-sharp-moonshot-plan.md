# シャープ Pinsker 不等式 ムーンショット計画 🌙 (B-5')

**Status**: CLOSED ✅ — sharp Pinsker (`tvNorm P Q ≤ √((klDiv P Q).toReal / 2)`、定数 `1/√2`、Csiszár-Kullback-Topsøe 経路) を有限 alphabet 上 `P ≪ Q` 確率測度に対し discharge。点別 sharp 不等式 `3(t-1)² ≤ 2(t+2)·klFun t` も独立に証明。
**SoT**: `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。
> **Parent**: [`pinsker-moonshot-plan.md`](pinsker-moonshot-plan.md) — 弱形 (定数 1) を温存し並列 publish、本 plan は定数を `1/√2` まで強化。

## 要点 (任意)
- 弱形ファイルの `tvNorm` を import + re-use (名前衝突回避)。`tvNorm` 定義そのものは Mathlib 不在。
- 点別 sharp 補題は `klFun` のみに依存し、Mathlib 上流 PR 候補 (`Real.one_sub_inv_le_log_of_pos` で `H''≥0` が短く出る)。

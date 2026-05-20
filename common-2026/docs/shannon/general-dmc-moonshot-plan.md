# General DMC capacity (moonshot) 🌙

> 実態整合 (2026-05-20): このファイルは空の placeholder だった (0 行)。General DMC capacity (limit form) の実装計画・実態は同 namespace のサブ計画 [`general-dmc-plan.md`](./general-dmc-plan.md) (I-2) に集約されている。

## ステータス

DONE-UNCOND — General DMC capacity の limit 形は実装済。

- 中核実体: `Common2026/Shannon/BlockwiseChannel.lean` (0 sorry) — `BlockwiseChannel` / `capacityN` / `capacity_lim` / `ofMemoryless` + 主接続補題 `capacity_lim_eq_capacity_of_memoryless` (`:1181`、std typeclass binders + `[StandardBorelSpace α/β]` のみ、pass-through Prop なし)。
- 再 export 層: `Common2026/Shannon/GeneralDMC.lean` (0 sorry) — `capacity_lim_eq_capacity_of_memoryless` (`:156`)、`capacityRate_ofMemoryless_eq` (`:170`) 等の memoryless flavour。
- 両ファイルとも `Common2026.lean` に import 済。

詳細な Phase 分解・判断ログは [`general-dmc-plan.md`](./general-dmc-plan.md) を参照。

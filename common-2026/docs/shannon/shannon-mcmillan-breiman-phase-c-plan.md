# Shannon–McMillan–Breiman Phase C+D+E (E-8') 計画 🌙

**Status**: CLOSED ✅ — 無条件 `shannon_mcmillan_breiman` 完成 (Algoet–Cover sandwich 経路、標準 `ErgodicProcess μ α` 仮定のみ)。Phase C Birkhoff a.s. (`birkhoff_ergodic_ae`) も done。例外: Phase E の i.i.d. 特殊化 `aep_strong_of_smb` は UNSTARTED (主定理は Birkhoff per-i 分解でなく Algoet–Cover で先に閉じたため不要化)。
**SoT**: `docs/textbook-roadmap.md` Ch.4 (SMB)。詳細履歴は git。

## 要点 (≤5 行)
- Phase 0' で martingale 経路 (Lalley) が Mathlib API では不成立と判明: `Submartingale.ae_tendsto_limitProcess` は `M_n` の収束を与え `M_n/n → 0` ではない。reversed/backward martingale 収束も当時 Mathlib 不在。
- 撤退結果として Birkhoff 自前は別 plan (経路 A backward martingale、`birkhoff-ergodic-plan.md`) に切り出し、SMB 本体は Algoet–Cover 路で着地。

## 参考
- 親 plan: [`shannon-mcmillan-breiman-plan.md`](shannon-mcmillan-breiman-plan.md)

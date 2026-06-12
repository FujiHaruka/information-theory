# Shannon–McMillan–Breiman (E-8) ムーンショット計画 🌙

**Status**: CLOSED ✅ — 無条件 `shannon_mcmillan_breiman` 完成 (Algoet–Cover sandwich 経路、標準 `ErgodicProcess μ α` 仮定のみ)。4 sandwich 仮説 (`algoet_cover_liminf_bound` / `algoet_cover_limsup_bound` / `blockLogAvg_bddAbove_ae` / `blockLogAvg_bddBelow_ae`) は real discharge (pass-through でない)。Phase A〜D done、例外: Phase E i.i.d. 特殊化 `aep_strong_of_smb` は UNSTARTED。
**SoT**: `docs/textbook-roadmap.md` Ch.4 (SMB)。詳細履歴は git。

## 要点 (≤5 行)
- Cover-Thomas 16.8 SMB の Lean 形: 定常エルゴード過程 (`Stationary.lean`) + entropy rate 定義 (`EntropyRate.lean`) を基盤に、Algoet–Cover 1988 sandwich で `-(1/n) log p(X^n) → entropyRate` a.s. を確立。
- liminf 下界は 2-sided 定常拡張 `μZ` (`TwoSidedExtension.lean`、`ergodic_shiftZ` 経由) を使用。Levy upward を片側 shift に直接適用できない問題の解決経路。
- Mathlib 不在資産: Birkhoff 個別エルゴード a.s.・定常過程 predicate・entropy rate (いずれも自前、構造部分は上流 PR 候補)。Levy upward (`tendsto_ae_condExp`) は整備済を流用。

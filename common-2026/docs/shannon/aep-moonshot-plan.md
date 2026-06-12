# AEP + 源符号化定理 ムーンショット計画 🌙🌙

**Status**: CLOSED ✅ — 全 Phase 完了。probability AEP / typical set / 源符号化定理 weak converse (`source_coding_converse`) + achievability (`source_coding_achievability`) + 両側等号 (`source_coding_theorem`)。仮定は i.i.d. 標準形 (`iIndepFun`/`IdentDistrib`/`hpos`) のみ。
**SoT**: `docs/textbook-roadmap.md` Ch.3。詳細履歴は git。

## 要点 (任意, ≤5 行)
- i.i.d. predicate は自前構造体を作らず `Pairwise IndepFun + IdentDistrib` の 2 仮定形をそのまま使用。
- probability AEP は `−log P(Xⁿ)` に強法則 `strong_law_ae_real` を適用 (`IdentDistrib.comp` / `IndepFun.comp` で i.i.d. 性 lift)。support 外点 `P(x)=0` は積分計算では `Real.log 0 = 0` 規約で素通り。
- ただし `typicalSet_card_le` (card 下界方向) では log-0 規約が破綻するため `hpos` (full support) を追加 (`log` の和展開でなく `Real.exp_sum` で `∏ P(xᵢ)` 構成すると plumbing が軽い)。
- weak converse は uniform 不要の Fano + DPI + Bridge を per-n block 再演 (`shannon_converse_single_shot` は uniform 仮定依存のため直呼びせず骨格再演)。

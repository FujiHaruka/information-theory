# EPI/Stam + FisherInfo + EntropyPowerInequality — 統合 sweep ムーンショット計画

**Status**: CLOSED ✅ — 4 cluster 統合 sweep の tier 5 defect 全解消 (Cluster B/C/D 全件)、3 cluster 独立監査 all-PASS で統合 sweep 終了。EPI family の実 sorry は route-T 後継で 0。(Stam Step 2: re-scope candidate — see 要点)
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

**Parent (umbrella)**: family-level moonshot は存在せず、本 plan が integrated sweep の親計画として機能した。EPI/Stam family の従来 plan 群 (`epi-moonshot-plan` / `epi-stam-discharge-plan` / `epi-stam-to-conclusion-*-plan` / `epi-debruijn-integration-*-plan` / `fisher-info-*-plan` / `parallel-gaussian-moonshot-plan`) を upstream inputs / closure routes として参照。

## 要点

Cover-Thomas Ch.17 Inequalities + 部分 Ch.8 Differential Entropy を対象とした 4 cluster 統合 sweep。依存方向 (上流←下流): Cluster A (ParallelGaussianPerCoord、独立 candidate、default skip) → Cluster B (FisherInfo cluster) → Cluster C (EPI/Stam) → Cluster D (EntropyPowerInequality 主定理露出)。

**統合 sweep を選んだ理由 (再開時の判断軸)**: olean cascade (`IsRegularDeBruijnHypV2` structure refactor が Cluster C consumer に signature ripple、統合だと refresh 1 回)、wall 集約が cluster 横断、tier 5 defect が同一構造 family。Phase 順 = C → B → D sequential 必須 (cluster 跨ぎ並列禁止)、Phase 内部の独立 declaration は worktree 並列可。

**着地内容 (re-scope の足掛かり)**:
- Cluster B (FisherInfo): tier 5 defect 5 件 (`IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` field bundling / `IsIBPHypothesis` literal alias / `:= h_ibp` 循環 chain) を field 削除 + sorry-based migration で解消。判定軸 = load-bearing field (engine substitution のみで一致 → 削除) vs regularity 帰結 (non-trivial bridge あり → 現状維持)。
- Cluster C (EPI/Stam): suspect 17→4 縮減 (incidental migration)、残 tier 4 legacy は別 family sweep target。
- Cluster D (EntropyPowerInequality): `:= True` 2 件 (`IsStamInequalityHypothesis` / `IsDeBruijnIntegrationHypothesis`) retract、9 declaration を tier-1 昇格。`entropyPower_gaussian_additivity` rename は Ch.17 frontier sweep 別 plan に切出 (延期)。

**Stam Step 2 re-scope candidate**: Cluster C の `IsStamCauchySchwarzOptimal` convex Fisher bound は **Rioul 2011 §II-C** (score-conditional-mean identity + total variance decomposition) で ~100 行 density-level computation の見積りあり (従来 ~300 行 PR 級より小)、再見積もり後 keep scope へ戻す余地 → roadmap Ch.17 行。

撤退ライン (履歴): L-INT-0-α (Cluster A 統合) / L-INT-1〜3 (各 cluster の partial closure / 新規 defect 停止) / L-INT-V (1 cluster partial → 別 sweep 分割)。共通禁止: `Prop := True` placeholder / 循環 `:= h` / load-bearing hyp / 退化定義悪用。

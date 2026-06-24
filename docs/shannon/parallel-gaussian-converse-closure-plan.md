# Parallel Gaussian: ② converse genuine closure サブ計画

**Status**: CLOSED ✅ — correlated-input converse の 2 field (`bddAbove` / `max_ent`) を 1-D AWGN converse の `Fin n` lift で genuine 着地。capacity headline は genuine。

**SoT**: `docs/textbook-roadmap.md` Ch.9 (parallel-gaussian) + `docs/shannon/awgn-facts.md`。詳細履歴は git。

> **Parent**: [`parallel-gaussian-headline-honest-restructure-plan.md`](parallel-gaussian-headline-honest-restructure-plan.md)

## 要点 (再利用可能)
- core 戦略は 1-D AWGN converse (`awgn_per_input_mi_le_log`) の `Fin n` lift — 新規数学ゼロ、規模が大きいだけ。
- chain: channel↔RV MI decomp lift → 出力エントロピー subadditivity (`jointDifferentialEntropyPi_le_sum`、genuine) → per-coord Gaussian max-entropy → log-algebra。
- variance allocation `P'ᵢ := Var(Yᵢ) − Nᵢ` で per-coord 上界を束ねる。`P ≤ 0` 退化は両辺 0 / 入力 Dirac で genuine 処理 (exfalso 悪用しない)。
- decomp lift は `CountableOrCountablyGenerated (Fin n → ℝ)` instance (Pi/CountablyGenerated 継承) に依存。

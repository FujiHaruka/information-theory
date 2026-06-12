# EPI 無条件化 W-Y2 — route β' (truncation + monotone-limit) サブ計画

**Status**: CLOSED ✅ — route β' (truncation + monotone-limit、weak-conv LSC 非経由) で method-Y full gateway 完了 (proof-done + 独立監査 all-OK)。gateway ⊤ 枝 + full 無条件単調性 `differentialEntropyExt_mono_add_unconditional` / `entropyPowerExt_mono_add_unconditional` が無条件版② (i-a) 非継承で着地。残 = headline wire のみ (親 Phase 5/S4)。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) §Sub-plan 一覧 S5 (W-Y2)

## 要点

無限エントロピー a.c. 入力 (`h(W)=⊤`) で gateway ⊤ 枝 `h(W)=⊤ ⟹ h(W+V)=⊤` を無条件 (truncation 近似) で genuine 着地。無条件版② chain rule の finiteness-free 等式は証明不能と確定済 → ターゲットを等式②でなく ⊤ 枝不等式に据えた (EReal が ⊤ を表現でき極限と相性が良い)。

**route β' 機構 (再開時に再利用できる approach)**:
1. `W_n := W | {|W| ≤ n}` (conditioning truncation、route T 流用) で compact-support 近似 — 有限分散・有限エントロピー・a.c. を genuine 供給。
2. n→∞ で `h(W_n) ↑ ⊤` の単調発散 (weak-conv portmanteau 非経由、`tendsto_measure_iUnion_atTop` ベース + Fatou)。
3. per-n 単調性 `h(W_n) ≤ h(W_n+V)` と組み ⊤ 枝 closure。

**key route 転換 (judgment、再開時の判断軸)**: 当初の chain rule 等式路は `hκ_dens_meas` (joint 密度可測、Mathlib 真 gap) を必須仮説に持つため proof-done 不能だった → 単調性は等式不要・不等式で足ると確定し、場合分け + per-fibre translate Gibbs (`differentialEntropy_le_cross_entropy` を explicit 平行移動 fibre で適用 → μV 積分 → Tonelli collapse) にルート転換、chain-rule scaffolding を全廃。⊤ 枝 assembly = route (d'') (測度 domination + 有限性不要 ℝ≥0∞ Gibbs `klDiv_eq_lintegral_klFun_of_ac` + KL≥0)。教訓: moonshot の真の consumer が ⊤ 枝**不等式**なら、中間を chain rule **等式** (finite ②) で建てると condDistrib regularity stack を丸ごと背負う。

撤退ライン (履歴): L-Uncond-Y-roi (極限 step が弱収束 LSC に退化 → headline を a.c.+有限エントロピー版に確定) / L-WY2-trunc (per-n 単調性が truncation で供給不能 → 別構成)。L-Uncond-Y-roi は Phase 0 gate で回避確定 (density a.e. 収束で弱収束 LSC 不該当)。

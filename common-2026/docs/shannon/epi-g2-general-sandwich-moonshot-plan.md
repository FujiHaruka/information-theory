# EPI G2 端点連続性 — 一般形 genuine サンドイッチ moonshot 計画 🌙

**Status**: CLOSED ✅ 🎉 — EPI G2 heat-flow 端点連続性を一般の有限 2 次モーメント分布 + h(X)>−∞ のまま (スコープ犠牲なし) で完全 genuine 完成。(β) 畳み込みエントロピー非減少 + (α) KL 下半連続性 (klFun-Fatou ルート) のサンドイッチで層2 を Vitali から載せ替え、近似単位元 L¹ 壁の UI/UT witness を削除。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-g2-layer2-moonshot-plan.md`](epi-g2-layer2-moonshot-plan.md) §Phase 1/2

## 要点 (≤5 行)

- 核心 pivot (再利用判断軸): DV 双対 hard direction は単一ルート過大評価だった。`klDiv_eq_lintegral_klFun_of_ac` + klFun≥0 + Fatou (`lintegral_liminf_le`) で固定ガウス確率測度 γ 上の KL-LSC が直接出る (負部一様可積分 majorant 不要)。監査・在庫は単一ルート仮定で壁を過大評価しがち。
- サンドイッチの 2 刃は boundedness で交わる (entangled): (α) の ℝ≥0∞→toReal 変換に (β) 下界が本質的に要る。
- 再利用資産: 条件付き KL 積分形 (`CondKLIntegral`、Mathlib ChainRule TODO 充足) + klFun-Fatou KL-LSC は連続版 MI/DPI で再利用可、Mathlib upstream PR 候補。

# Shannon EPI: G2 連続性壁 攻略サブ計画

**Status**: CLOSED ✅ — heat-flow 端点連続性ルートの出発点。後続 layer2 / sandwich plan で一般形 genuine 完成に至り、本計画の壁表面積は層2 機構へ移送済。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §G2 / 撤退ライン **L-Concl-A-θ**

## 要点 (≤5 行)

- 再利用判断軸: 端点連続性は内部 derivative + 可積分性からは出ず追加解析内容が要る (FTC ショートカット否定)。
- 攻略は密度レベル L¹ 強収束ルート (de Bruijn 積分恒等式の `.cont` field が端点連続性を内包するため積分恒等式ルートは循環)。
- 「3 項 → sum 項 1 個」reduction (X/Y 項は単調性-LSC で free、sum 項のみ USC/連続性) は将来 EPI-隣接 closure 設計で再利用可。

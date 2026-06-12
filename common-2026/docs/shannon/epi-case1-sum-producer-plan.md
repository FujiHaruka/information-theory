# Shannon EPI: case-1 sum-instance de Bruijn producer サブ計画 (L-Sum-struct closure)

**Status**: CLOSED ✅ — sum noise `Z_X+Z_Y ∼ 𝒩(0,2)` と `IsRegularDeBruijnHypV2.Z_law` の unit-hardcode 型不一致を sum 専用 general-variance structure で解消する試み。後継の two-time restructure (`epi-case1-twotime-restructure-plan`) が variance-2 view を発生させずに sum EPI を genuine closure し、本 plan の producer は dead orphan として削除。structure surgery は不要化。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-case1-debruijn-producer-plan.md`](epi-case1-debruijn-producer-plan.md) §PB-4 / L-Sum-struct

## 要点 (再利用可能な判断軸)
- **path-identification は path (関数) のみ同一視し、noise law 主張は救えない**: `Z_law` field は `P.map (Z_X+Z_Y)` の law を直接主張するので、path を unit-W 形 (`W=(Z_X+Z_Y)/√2`) に書き換えても `gaussianReal 0 1 ≠ gaussianReal 0 2` の型不充足は残る。型レベル不一致は noise の law を直接触らない限り解消しない。
- **prior art の general-variance 共存は安全の証拠にならない (役割差)**: `IsHeatFlowEndpointRegular` の v_Z=2 は端点連続性専用で ratio core arith に到達しない。一方 de Bruijn `Z_law` の v_Z は微分値経由で arith に到達する。同名フィールドでも消費される役割 (連続性 vs 微分値) が違えば一般化の安全性は別判定。
- **dead orphan は structure surgery より file 全削除が clean**: defect の唯一の carrier が 0 consumer なら、想定された大規模 ripple (structure 一般化) は不要で file 削除だけで defect が消える。削除後は compile で裏取り。

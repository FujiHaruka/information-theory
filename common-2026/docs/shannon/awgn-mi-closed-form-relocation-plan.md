# AWGN: `mutualInfoOfChannel_gaussianInput_closed_form` の `h_bridge` 解消 (relocation plan)

**Status**: CLOSED ✅ — MI closed-form の opaque load-bearing 仮説 `h_bridge` を除去し、両 genuine producer (bind/conv bridge + MI 分解) を import できる最下流 file へ hypothesis-free 版を relocate 完了。sibling `awgn-mi-decomp-plan` の MI chain rule genuine 化により、AWGN MI closed-form ラインは capacity を除き genuine 着地。AWGN 形式化ラインは CLOSED。機械検証状態は SoT 参照。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §Phase A (MI closed-form bridge)
> **Sibling**: [`awgn-mi-decomp-plan.md`](awgn-mi-decomp-plan.md) (MI 分解の genuine discharge 側)

## 要点 (再利用可能な一行)

- 兄弟 producer (互いに非 import) を同時に見られる既存 file が無いとき、新規 file を 1 本立てて両者を import するのが責務分離的に正解 (Draft file への混入を避ける)。
- closed-form を AWGN.lean (import DAG の頂点) に置いたままだと discharge 補題呼出が import cycle になるため、downstream relocate が唯一の解。

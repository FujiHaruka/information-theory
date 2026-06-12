# 連続チャネル MI 分解 bridge discharge ムーンショット計画 🌙 (T2-A follow-up)

**Status**: CLOSED ✅ — 連続チャネル MI chain rule `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` を genuine に証明完成 (`@audit:ok`)。AWGN instance の `IsContChannelMIDecompHyp` を Gaussian 事実で全引数 discharge、共有壁は retire。AWGN(#5) / Parallel Gaussian(#6) 共有の foundational brick が genuine 着地し、AWGN 形式化ラインは CLOSED (残 MI 撤退口は capacity 側のみ、別件)。機械検証状態は SoT 参照。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §撤退ライン **F-2** (MI bridge hypothesis 外出し)
> **Sibling**: [`awgn-mi-closed-form-relocation-plan.md`](awgn-mi-closed-form-relocation-plan.md)

## 要点 (再利用可能な一行)

- 証明道筋: MI = klDiv を llr 積分に開き、`prod → compProd const` 書換 (★最初に置く gotcha) → rnDeriv 連鎖律で density 比に砕き → Fubini で 2 本の differential-entropy 積分に組替。山場は mixture 同定 (出力 marginal) で、measure-level 周辺化で density 陽展開を回避。
- AWGN instance discharge: honest 仮定を Gaussian 事実 (`gaussianReal_absolutelyContinuous` / `rnDeriv_gaussianReal` / `integrable_density_log_density_of_gaussian`) で全充足。
- rnDeriv joint-measurability は everywhere `=` で取れない (a.e.-determined) ため、measurable PDF proxy (`measurable_gaussianPDF_uncurry`) を per-fibre 経路に流して joint measurability の壁を回避 (Route B)。
- 教訓: shared sorry 補題化のとき regularity 前提を壁から落とすと over-general 化して偽になりうる (決定論チャネルで反例)。consolidate 時は regularity 前提を壁側に残すこと。

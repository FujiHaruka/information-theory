import InformationTheory.Draft.Shannon.RateDistortionConvexity
import InformationTheory.Shannon.Sanov
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# `klDiv` joint convexity discharge for E-4'' (E-4''')

[`docs/shannon/rate-distortion-convexity-plan.md`](../../../docs/shannon/rate-distortion-convexity-plan.md)
の **E-4'' Phase B core** が hypothesis 化していた `klDiv` joint convexity
(`h_klDiv_conv`) を **pmf 形 (per-atom log-sum inequality)** で discharge する予定だった。

## 現状 (orphan removal 後)

Step A〜E の補題群および主定理 `rateDistortionFunction_convexOn_pmf` は
すべて非参照だったため orphan として削除された。実体の凸性主定理は
`Common2026/Draft/Shannon/RateDistortionConvexity.lean` 側の
`rateDistortionFunction_convexOn` を参照のこと。
-/

namespace InformationTheory.Shannon

end InformationTheory.Shannon

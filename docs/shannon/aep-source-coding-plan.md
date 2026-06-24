# AEP Phase D — 源符号化定理 weak converse ムーンショット計画 🌙

**Status**: CLOSED ✅ — 源符号化定理 weak converse `source_coding_converse` 完成。仮定は `iIndepFun` / `IdentDistrib` / `2 ≤ Fintype.card α` + 誤り率→0 + rate 上界の honest 形のみ (pass-through なし)。
**SoT**: `docs/textbook-roadmap.md` Ch.3 (AEP / 源符号化)。詳細履歴は git。

## 要点 (≤5 行)
- i.i.d. block entropy chain rule `H(X^n) = n · H(X)` は Han `jointEntropy_chain_rule` 直接路線で着地 (`iIndepFun.indepFun_finset` で per-i 投影、`Fin n` 内 reshape を回避)。後続 moonshot で再利用候補。
- per-n converse は Slepian–Wolf 流儀 4-step を単一 RV で再演 (DPI postprocess は不要だった)。
- `Filter.liminf` 形は `IsCoboundedUnder (· ≥ ·)` が実数 unbounded 列で auto 解決せず、rate 上界仮定 `hM_bdd` を入口に追加して `IsCoboundedUnder.of_frequently_le` で discharge。

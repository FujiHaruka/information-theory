# AEP 完全形 (D-3) ムーンショット計画 🌙

**Status**: CLOSED ✅ — Cover-Thomas Theorem 3.1.2 完全 3 点セット完成。点別下界 `typicalSet_prob_ge` / サイズ下界 `typicalSet_card_ge` (+ `_eventually` 形) いずれも実証明、仮定は i.i.d. 標準形 (`iIndepFun`/`IdentDistrib`/`hpos`) のみ。
**SoT**: `docs/textbook-roadmap.md` Ch.3。詳細履歴は git。

## 要点 (任意, ≤5 行)
- 点別下界は `typicalSet_prob_le` の方向反転 (鏡像): typical 定義の上側を取り `exp(-(∑ pmfLog)) > exp(-n(H+ε))`、`∏ P(xᵢ) = exp(-(∑ pmfLog))` で結論。
- サイズ下界は確率質量保存 `μ(T) ≤ |T|·max p(x)` + `typicalSet_prob_tendsto_one` のサンドイッチ。主形は「`μ(T) ≥ 1-η` 仮定」版、eventually-N 形は corollary。
- `hpos` (full support) は維持 (除去は statement が a.s.-quantified 化、scope 外)。

# E-3' Phase B.2.2 — `jointlyTypicalSet_indep_prob_ge` 実装計画

**Status**: CLOSED ✅ — `jointlyTypicalSet_indep_prob_ge` (independent-product 下の joint-typical 確率下界) を実証明で publish 済。入力は joint-law 形の honest 仮定で、circular でない。
**SoT**: `docs/textbook-roadmap.md` Ch.10。詳細履歴は git。

## 要点 (任意, ≤5 行)
- `jointlyTypicalSet_indep_prob_le` の anti-direction (下界) ミラー: point-wise を `typicalSet_prob_ge`、size を新規 `jointlyTypicalSet_card_ge` で取り、product-law 上に合成。
- 当初 plan の `hμJTS` (product-law 下界) は circular。正しい入力は joint-law 形 `μ.real {ω | (jX, jY) ∈ JTS} ≥ 1 - η`。

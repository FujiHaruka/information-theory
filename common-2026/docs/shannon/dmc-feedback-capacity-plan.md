# DMC feedback capacity (E-10) ムーンショット計画 🌙

**Status**: CLOSED ✅ — Cover-Thomas 7.12 feedback converse を chain rule + Fano 合成で publish。per-letter bound を hypothesis 化した MVP 形は後継 E-10' が剥がして完全形を結論。
**SoT**: `docs/textbook-roadmap.md` Ch.7。詳細履歴は git。

## 要点 (任意, ≤5 行)
- 証明 5 段: `log M = H(M) = I(M;Y^n) + H(M|Y^n) = ∑ I(M;Y_i|Y^{<i}) + ... ≤ n·C + Fano`。本 plan で chain rule (c) + capacity bound (e) + Fano (f) を担い、per-letter bound (d) は E-10' へ。
- Y 軸 chain rule は既存 X 軸版 `mutualInfo_chain_rule_fin` を `mutualInfo_comm` + `condMutualInfo_comm` で交換して局所導出。
- feedback 下では Markov chain `Msg → X^n → Y^n` が成立しないため、DPI 経路でなく `shannon_converse_single_shot` を `Yo := Y^n` で直接呼ぶ。
- 後継: [`dmc-feedback-per-letter-bound-plan.md`](./dmc-feedback-per-letter-bound-plan.md) (E-10', per-letter bound 内部証明)。

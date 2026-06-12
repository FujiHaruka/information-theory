# Sanov の定理 (B-1) ムーンショット計画 🌙

**Status**: CLOSED ✅ — Sanov A 形 (`typeClass_Qn_le`, Cover-Thomas 11.1.4) を `InformationTheory/Shannon/Sanov.lean` で publish。LDP upper bound は [`sanov-ldp-b-plan.md`](sanov-ldp-b-plan.md)、LDP equality 形は [`sanov-ldp-equality-plan.md`](sanov-ldp-equality-plan.md) で完成済。
**SoT**: `docs/shannon/cramer-facts.md` + `docs/textbook-roadmap.md` Ch.11。詳細履歴は git。

## 要点 (≤5 行)
- 核アイデア (Stein 経路特化): 古典の多項係数評価 `|T(P)| ≤ exp(n·H(P))` を回避し、`Q^n(T) = exp(-n·D) · P^n(T) ≤ exp(-n·D)` で直接終わらせる (Stein converse `steinTypicalSet_Q_prob_le` の両側 equality 特殊形)。
- `klDivSumForm P Q := ∑ a, P(a)·(log P(a) − log Q(a))` を finite-alphabet textbook 定義に使い、`(klDiv P Q).toReal` との等値は別補題に切り出す。
- 実装上: combining-circumflex 変数名は Lean parser が拒否するため plain `P` に rename。aggregation は `sum_fiberwise_of_maps_to'` 直結で短縮。

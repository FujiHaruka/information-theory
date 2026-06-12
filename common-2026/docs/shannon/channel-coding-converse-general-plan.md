# Channel coding converse (general input form, D-2) ムーンショット計画 🌙

**Status**: CLOSED ✅ (chain-rule scope) — IID 仮定なしの一般入力 chain-rule 形 `log|M| ≤ ∑ I(X_i; Y^n | X^{<i}).toReal + Fano` を publish (`channel_coding_converse_general_chainRule`)。memoryless per-summand bound は後継 D-2' / D-2'' で完成。
**SoT**: `docs/textbook-roadmap.md` Ch.7。詳細履歴は git。
後継 (per-summand): [`channel-coding-converse-general-d2-prime-plan.md`](./channel-coding-converse-general-d2-prime-plan.md)

## 要点 (≤5 行)
- 本質的新規性 = IID 入力仮定を完全に外したこと (既存 `channel_coding_converse_iid` は IID 必須)。
- 出発点の single-shot 段 (`shannon_converse_single_shot_markov_encoder`) は IID 版と同形、`iid_eq_nsmul` を `chain_rule_fin` に置換しただけ。
- prefix RV `Fin i.val → α` 上の `condMutualInfo_ne_top` 適用は α が Fintype + MeasurableSingletonClass + Nonempty なら全 typeclass を auto-derive。

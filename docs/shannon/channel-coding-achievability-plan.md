# Channel coding achievability ムーンショット計画 (B-3) 🌙

**Status**: CLOSED ✅ — Cover-Thomas 7.7.1 achievability 半分。Phase A (Channel/Code 定義) + Phase B (jointly typical set + 3 joint AEP bound) を `ChannelCoding.lean` で publish。Phase C/D (random codebook + averaging + 主定理) は子 plan B-3'' で完成。
**SoT**: `docs/textbook-roadmap.md` Ch.7。詳細履歴は git。
子 plan (Phase C/D): [`channel-coding-phase-cd-plan.md`](./channel-coding-phase-cd-plan.md)

## 要点 (≤5 行)
- Channel は `Kernel α β` 表現を採用 — Mathlib の `klDiv` plumbing と整合。
- 3 つの joint AEP bound ((a) 確率→1 / (b) size / (c) independent pair) は Slepian-Wolf 等で再利用可能な独立資産。
- averaging は確率測度を立てず `Codebook` 有限集合上の `Finset` sum + pigeonhole (`Finset.exists_le_of_sum_le`) で処理。

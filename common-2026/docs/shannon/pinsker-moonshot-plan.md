# Pinsker 不等式 ムーンショット計画 🌙 (B-5)

**Status**: CLOSED ✅ — 弱形 Pinsker (`tvNorm P Q ≤ √(klDiv P Q).toReal`、定数 1、Bretagnolle-Huber 経路) を有限 alphabet 上 `P ≪ Q` 確率測度に対し discharge。
**SoT**: `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

## 要点 (任意)
- シャープ版 (定数 `1/√2`、`TV ≤ √(KL/2)`) は別 plan [`pinsker-sharp-moonshot-plan.md`](pinsker-sharp-moonshot-plan.md) で達成済。
- `tvNorm := (1/2)·Σ|p-q|` は Mathlib 不在 (loogle 0 件) のため自前定義。下流 Sanov/Strong Stein は定数の √2 差に依存しない (rate function 同一性のみ使う)。

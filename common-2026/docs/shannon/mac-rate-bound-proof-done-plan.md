# Shannon: MAC `mac_single_rate_bound₁/₂` + `mac_sum_rate_bound` proof done plan

**Status**: CLOSED ✅ — MAC 3 rate-bound declaration の body を同 file 内 `mac_rate_le_of_fano` arithmetic kernel 呼出に置換し proof done 到達。MAC / BC / Relay 系 main は scope-out (textbook-roadmap Ch.15)。
**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

> **Parent**:
> - [`mac-moonshot-plan.md`](mac-moonshot-plan.md) — T3-B MAC moonshot
> - [`mac-bc-sorry-migration-plan.md`](mac-bc-sorry-migration-plan.md) §Phase 2.1 — sorry 残置の起源
> - [`broadcast-channel-signature-rewrite-plan.md`](broadcast-channel-signature-rewrite-plan.md) — BC peer (構造模倣元)

## 要点 (再利用しうる観察)

- **kernel 既存で body 置換のみ**: divide-by-`n` arithmetic kernel `mac_rate_le_of_fano` (同 file `private theorem`) が既存だったため、3 declaration は body の `by sorry` を term-mode kernel 呼出 1 行に置換するだけで closure。signature は既に genuine entropy-level 形 (Phase 2.1 で rewrite 済) ゆえ無改変、consumer ripple なし。
- **sum-rate も kernel 直接適用可**: kernel の汎用 scalar signature `(R I_marg I Pe L ε : ℝ)` に `R := R₁ + R₂`, `L := Real.log (M₁ * M₂)` を bind すれば型一致。二段適用や `add_le_add` 結合の adaptation 不要。
- **BC peer との対称性**: BC は signature rewrite を要したが (`broadcast-channel-signature-rewrite-plan.md`)、MAC は kernel 既存 + signature genuine 済で更に scope 小。entropy-level Fano + chain + cleanup の 3 hypothesis は precondition (joint-typicality-multi wall への pass-through)、load-bearing core ではない。

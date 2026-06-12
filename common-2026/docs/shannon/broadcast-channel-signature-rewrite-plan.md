# Shannon: BC `bc_common_rate_bound` / `bc_private_rate_bound` signature rewrite plan

**Status**: CLOSED ✅ — BC 2 rate-bound declaration を tier-5 defect (false-statement) から MAC analogue 同型の genuine entropy-level signature に rewrite し、同 file 内 `bc_rate_le_of_fano` kernel 経由で proof done 到達。MAC / BC / Relay 系 main は scope-out (textbook-roadmap Ch.15)。
**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

> **Parent**:
> - [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) — T3-C BC moonshot
> - [`mac-bc-sorry-migration-plan.md`](mac-bc-sorry-migration-plan.md) §Phase 2.3.b — 本 plan の起源 (genuine 形再設計 step)

## 要点 (再利用しうる観察)

- **defect → genuine の rewrite ルート**: 旧 signature は `(R I : ℝ) : R ≤ I` (universally false counterexample `R:=1, I:=0`)。これを entropy-level Fano + chain + cleanup の 3 hypothesis を取る形に拡張し、結論を `R ≤ I + ε` に直して body を `bc_rate_le_of_fano` 呼出 1 行に。kernel は同 file `private theorem` で既存ゆえ visibility 変更不要、consumer 0 件で cross-file ripple なし。
- **MAC peer との asymmetry / 同型**: BC は kernel 既存ゆえ先行 proof done、MAC peer は子 plan [`mac-rate-bound-proof-done-plan.md`](mac-rate-bound-proof-done-plan.md) で同型 closure。entropy-level hypothesis は precondition (joint-typicality-multi wall pass-through)、load-bearing core ではない。
- outer-bound corner 系の constructive recovery は別手法 (Pattern B) で [`mac-bc-pattern-b-constructive-recovery-plan.md`](mac-bc-pattern-b-constructive-recovery-plan.md) が担当 — 本 plan の signature rewrite とは独立。

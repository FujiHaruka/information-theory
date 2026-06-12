# Shannon: AWGN family legacy-tag → sorry-based migration plan (Round 4 Wave A)

**Status**: CLOSED ✅ — AWGN family の legacy `@audit:suspect`/`staged`/`defer`/`defect`/散文 `🟢ʰ` タグ群を `sorry + @residual` ベースへ移行する sweep を完了。AWGN 形式化ライン (① single-letter capacity / ② parallel Gaussian / ③ operational coding theorem) は CLOSED。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)
> + [`awgn-mi-bridge-plan.md`](awgn-mi-bridge-plan.md)
> + [`awgn-mi-decomp-plan.md`](awgn-mi-decomp-plan.md)
> + [`awgn-f1-discharge-moonshot-plan.md`](awgn-f1-discharge-moonshot-plan.md)
> + [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md)
> + [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md)
> + [`awgn-power-constraint-realizable-pivot-plan.md`](awgn-power-constraint-realizable-pivot-plan.md)

## 要点 (再利用可能な一行)

- sweep recipe = Round 3 pilot (chernoff / brunn-minkowski / small-cluster / ratedistortion-pgpc) の継承。大規模 family でも「signature 改変なしの tag-only migration」が基本軸。
- 真の Tier 3 → Tier 2 (signature 改変を伴う sorry 化) は本 plan の scope 外で、後継 `awgn-m5-sorry-migration-plan.md` が担当。

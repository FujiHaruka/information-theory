# Shannon: Relay legacy-tag → sorry-based migration plan

**Status**: CLOSED ✅ — Relay family (RelayCutset / RelayInnerBound / RelayInnerBodyDischarge / RelayCFBinningBody / RelayDFBlockMarkovBody) は Ch.15 Relay main の scope-out に伴い flat ファイルごと削除済。legacy tag (suspect / 散文 🟢ʰ) → `sorry + @residual` の honesty 強化対象は消滅。

**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

> **Parent**: [`relay-inner-bound-moonshot-plan.md`](relay-inner-bound-moonshot-plan.md)
> + [`relay-cutset-moonshot-plan.md`](relay-cutset-moonshot-plan.md)
> + 関連 [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) /
>   [`audit/audit-tags.md`](../audit/audit-tags.md)。

## 要点 (将来再利用しうる手順のみ)

- file 単位 sweep を 上流 → 下流 chain 順で実施する設計だった (cutset primitive → DF/CF inner bound headline → witness-based wrapper → sub-hyp constructive bridge)。上流 sorry を先に確定させると olean refresh + 下流 transitive sorry の散文化が一括で扱える (Cramér pilot で実証)。
- cross-family entanglement (RelayCFBinningBody が WynerZiv binning predicate を re-namespacing import) は削除提案禁止、未決事項に escalate する方針だった。共有 predicate を一方の family だけで deprecate できない (Pattern G、本 family が初の本格適用例)。
- transitive sorry の caller には散文のみ追記し `@residual` は付けない (closure responsibility は upstream の `@residual` に帰属)。即興 vocabulary 禁止 (Pattern C)。
- alias を pure rename (`def := <core predicate>`) で立てるのは tier 5 borderline (`IsRelay*Witness` = `Relay*Achievable` の rename)。後続 deprecation で扱う候補という判断軸だった。

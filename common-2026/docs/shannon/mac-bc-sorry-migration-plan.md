# Shannon: MAC + BroadcastChannel legacy-tag → sorry-based migration plan

**Status**: CLOSED ✅ — MAC/BC family の legacy tag (suspect / 散文 `🟢ʰ` / tier-5 defect) を `sorry + @residual` の honesty-based 形に移行する 1-sweep workstream。MAC / BC / Relay 系 main は scope-out (textbook-roadmap Ch.15)。
**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

> **Parent**: [`mac-moonshot-plan.md`](mac-moonshot-plan.md) +
> [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) +
> [`mac-l1-discharge-moonshot-plan.md`](mac-l1-discharge-moonshot-plan.md)

## 要点 (再利用しうる観察)

- **MAC と BC を 1 plan に統合**した根拠: converse の divide-by-`n` arithmetic kernel が両 family で同型 + BC superposition body が MAC body discharge を import 再利用 (内部 cross-import 2 経路) + 共有 wall。1 sweep にすると transitive sorry を 1 Phase シーケンス内に吸収できる (MAC 先行 → BC 後追いの sweep 順)。
- **共有 wall は `joint-typicality-multi`** (register 既登録、SoT は `docs/audit/audit-tags.md`)。本 sweep の residual は `plan:` slug で揃え、shared sorry 補題化はしない (Hoeffding/Cramér/WynerZiv 踏襲)。
- **rate-bound 系は後続 plan で proof done 到達**: MAC は [`mac-rate-bound-proof-done-plan.md`](mac-rate-bound-proof-done-plan.md)、BC は [`broadcast-channel-signature-rewrite-plan.md`](broadcast-channel-signature-rewrite-plan.md)、outer-bound corner は [`mac-bc-pattern-b-constructive-recovery-plan.md`](mac-bc-pattern-b-constructive-recovery-plan.md)。いずれも同 file 内 `*_rate_le_of_fano` arithmetic kernel 経由。

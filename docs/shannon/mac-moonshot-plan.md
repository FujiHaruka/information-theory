# T3-B Multiple Access Channel (MAC) Capacity Region ムーンショット計画 🌙

**Status**: CLOSED ✅ — MAC capacity region (Cover–Thomas Ch.15.3, 2-user) を outer + inner bound 両側 statement-level pass-through で publish 済。MAC / BC / Relay 系 main は scope-out (textbook-roadmap Ch.15)。
**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-B. Multiple Access Channel (MAC) (Cover–Thomas Ch.15.3)」

## 要点 (再利用しうる設計判断)

- **両側 publish pattern**: converse 側は T3-F Relay の hypothesis pass-through、achievability 側は T3-D Wyner-Ziv の existence form pass-through を組合せる。両側同型ゆえ後続 multi-user region で再利用可。
- **撤退ライン L-MAC1〜L-MAC5** (frozen slug、他 plan が参照): L-MAC1 multi-user joint typicality body / L-MAC2 multi-user Fano + chain rule / L-MAC3 inner bound 全体 existence pass-through / L-MAC4 outer bound 全体 `InMACCapacityRegion` pass-through / L-MAC5 time-sharing convex hull は完全 scope-out (corner-point form のみ publish)。
- **設計判断**: `InMACCapacityRegion` を `structure ... : Prop` (3 projection field accessor) で書く。`MACChannel := Kernel (α₁ × α₂) β` は Relay channel の codomain-bare 版。`MACCode` は encoder × 2 + pair-output decoder。
- proof done 系の rate-bound closure は子 plan [`mac-rate-bound-proof-done-plan.md`](mac-rate-bound-proof-done-plan.md) 参照。

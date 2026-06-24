# T3-F Relay Inner Bound (DF/CF) ムーンショット計画 🌙

**Status**: CLOSED ✅ — Relay inner bound (Cover-Thomas 15.10.2 DF + 15.10.3 CF) は scope-out。textbook-roadmap Ch.15 で MAC/BC/Relay/Wyner-Ziv main は捨てると確定済、本 plan が前提とした `RelayInnerBound.lean` 系 flat ファイルは削除済。

**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-F. Relay
>   Channel + Cut-set bound」(inner bound 半部)

## 要点 (将来再利用しうる設計のみ)

- 採った形: DF/CF それぞれ rate region predicate (`InRelayDFRate` / `InRelayCFRate` を 2 不等式 structure) + existence form の statement-level hypothesis pass-through。雛形は T3-B MAC inner bound (`mac_capacity_region_inner_bound`) を単一-rate に縮退したもの。
- block Markov encoding / sliding-window decoder (DF) と Wyner-Ziv binning / side-info decoding (CF) は全て placeholder pass-through 化する判断だった (各々 combinatorial existence で大規模)。

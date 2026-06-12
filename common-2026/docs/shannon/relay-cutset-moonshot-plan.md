# T3-F Relay Channel + Cut-set Outer Bound ムーンショット計画 🌙

**Status**: CLOSED ✅ — Relay channel cut-set outer bound (Cover-Thomas Ch.15.10.1) は scope-out。MAC/BC/Relay/Wyner-Ziv main は textbook-roadmap Ch.15 で「Distributed Source Coding mini-chapter (Slepian-Wolf + Wyner-Ziv convexity body) として publish、Draft 本体は捨てる」と確定済。本 plan が前提とした `RelayCutset.lean` 系 flat ファイルは削除済。

**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-F. Relay Channel + Cut-set bound (Cover-Thomas Ch.15.7 / 15.10)」

## 要点 (将来再利用しうる設計のみ)

- 採った形: outer bound only + scalar form `relayCutsetBound (Ib Im : ℝ) := min Ib Im`。joint pmf 上の `sSup` (max over `p(x,x₁)`) は呼び出し側に外出しすることで `IsCompact + exists_isMaxOn` の plumbing を回避する設計。
- 雛形は T3-D Wyner-Ziv converse の statement-level hypothesis pass-through pattern。broadcast-cut / MAC-cut / composite rate bound / relay measurability / inner bound (DF/CF) を全て hypothesis pass-through ないし scope-out する判断だった。
- inner bound (decode-and-forward / compress-and-forward) は当初から完全 scope-out (random binning + jointly typical decoder + n-letter AEP で大規模)。

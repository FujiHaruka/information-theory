# T3-D Wyner–Ziv lossy distributed coding ムーンショット計画 🌙

**Status**: CLOSED ✅ — Wyner–Ziv main theorem (Cover-Thomas 15.9.1 achievability + converse) は scope-out。textbook-roadmap Ch.15 で MAC/BC/Relay/Wyner-Ziv main は捨て「Distributed Source Coding mini-chapter (Slepian-Wolf + Wyner-Ziv convexity body)」として publish と確定済。convexity body (`wynerZivCondEntDiffConvex_holds`、`InformationTheory/Shannon/WynerZiv/` 配下) は完成済。本 plan が前提とした `WynerZiv{,Achievability,Converse}.lean` 系 flat ファイルは削除済。

**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-D. Wyner–Ziv (Cover–Thomas Ch.15.9)」

## 要点 (将来再利用しうる設計のみ)

- 採った形: source-coding 系 (`R(D)`) と distributed-coding 系 (Slepian-Wolf) の hybrid。auxiliary alphabet `U` を `Fintype` として引数で受け、cardinality bound (`|U| ≤ |α|+1`、Carathéodory reduction) は別 plan へ分離する判断だった。
- converse は Csiszár's sum identity + `R_WZ(D)` 凸性を hypothesis pass-through 化 (`RateDistortionConverseNLetter` の `h_jensen_antitone` パターン踏襲)。
- `condMutualInfo` の `[StandardBorelSpace]` 要求は `[Fintype + MSC]` から自動で出ないため、`attribute [local instance]` で discrete-measurable-space instance を file 限定で有効化する設計 (既存 SW/RD への波及ゼロ)。
- 残った live asset は Wyner-Ziv convexity body のみ (上記 SoT)。

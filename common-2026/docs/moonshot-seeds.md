# Moonshot シードカード集

> **Status (2026-05-11)**: 5 シード本体 + A 節 deferred 全件 + C 節 横断改善 全件完了。Loomis–Whitney → Slepian–Wolf → AEP (Phase A〜F unified) → Stein (achievability + converse 半分 + liminf/limsup sandwich) → Polymatroid (structure 化込) を **すべて 0 sorry** で通過。完了済みカードは本ファイルから撤去し、各 plan ファイル (`docs/<family>/*-plan.md`) に履歴を残置。残る伸び代は B 節新シード (Sanov / Hypercube isoperimetry / Channel coding achievability) と Strong Stein (`Tendsto → K` strict 形、strong converse 経路の inventory が必要)。
>
> 起草時 (2026-05-10): Fano (測度論版) → Shannon converse (3 形) → Han 補集合形 → Han Phase D (subset average / Shearer) まで通った状態を起点に、次のムーンショット候補 5 本をシード化。
>
> ここに書いてあるのは **着手前の seed**。実装着手の判断 = 該当シードを `docs/<family>/<topic>-moonshot-plan.md` に複製 + `docs/moonshot-plan-template.md` で膨らませる。本ファイル自体はカード一覧として保ち、選定が確定したら該当カードに `→ <plan path>` のポインタを書き加える。

---

## 次のシード候補

### B. 新シード入口 (5 シード完了で開いた)

- **Sanov の定理** (Stein の自然な拡張): `klDiv` の operational meaning を別形 (large deviation principle の rate function) で Lean 化。Stein で立った plumbing (log-likelihood ratio plumbing + Pi 化 chain rule) がそのまま再利用可。
- **Hypercube edge isoperimetry / Han-Bregman bound**: Loomis–Whitney 完了で Shearer の組合せ応用 1 本立った状態。同じ engine (Shearer) を別 cover で適用するシリーズの第 2 弾。見積 1 週間 / 200〜300 行 / 低リスク。
- **Channel coding theorem (achievability)**: Shannon converse は完了済。achievability 半分 (Cover-Thomas Ch 7 strong typicality + jointly typical decoder) は AEP plumbing 上に構築可能。見積 4〜6 週間 / 800〜1500 行 / 高リスク。
- **Strong Stein** (`Tendsto → K` strict 形): 現行 Stein は `K ≤ liminf ≤ limsup ≤ K/(1-ε)` の sandwich 止まり。`1/(1-ε)` 補正を消すには strong converse (concrete bound に `1+o(1)` factor) が必要。新規 inventory: strong converse 経路 (information spectrum / Han-Verdú approach) の Mathlib delta 調査。見積 unknown (inventory 後判定)。

---

## 参照

- 既存 plan:
  - [Fano moonshot](fano/fano-moonshot-plan.md)
  - [Shannon moonshot](shannon/shannon-moonshot-plan.md)
  - [Shannon encoder extensions](shannon/shannon-encoder-extensions-plan.md)
  - [Han moonshot](han/han-moonshot-plan.md)
  - [Han Phase D (subset average / Shearer)](han/han-phase-d-plan.md)
- 5 シード plan + deferred (2026-05-10 / 2026-05-11、全て完了):
  - [Loomis–Whitney moonshot](shannon/loomis-whitney-moonshot-plan.md) ✅
  - [Slepian–Wolf moonshot](shannon/slepian-wolf-moonshot-plan.md) ✅
  - [AEP moonshot](shannon/aep-moonshot-plan.md) ✅ (Phase A〜C)
  - [AEP source coding (Phase D)](shannon/aep-source-coding-plan.md) ✅
  - [AEP achievability (Phase E)](shannon/aep-achievability-plan.md) ✅
  - [Stein moonshot](shannon/stein-moonshot-plan.md) ✅ (Phase A〜B achievability)
  - [Stein converse (Phase A〜C)](shannon/stein-converse-plan.md) ✅
  - [Polymatroid moonshot](han/polymatroid-moonshot-plan.md) ✅ (Phase A〜C)
  - [Polymatroid structure (Phase D)](han/polymatroid-structure-plan.md) ✅
  - [HanD Pi refactor](han/hand-pi-refactor-plan.md) ✅
- 雛形:
  - [moonshot-plan-template.md](moonshot-plan-template.md)
  - [subplan-template.md](subplan-template.md)

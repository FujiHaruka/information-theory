# EPI de Bruijn: `IsDeBruijnTailHyp` honest re-introduction mini-plan

**Status**: CLOSED ✅ — retract された `IsDeBruijnTailHyp` を EReal lift + `Z_law` field で honest 再導入し、`(0,T)→(0,∞)` tail externalization 経路を de Bruijn integration に供給。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。
**Parent**: [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md)
**Sister**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md)

## 要点 (≤5 行)
- slug `@audit:staged(epi-debruijn-tail-reintroduction)` はコード残存。
- honest 再導入の必須 2 条件 (再利用判断軸): (a) `h_inf : ℝ` → `EReal` lift で `+∞` 極限を表現可能化、(b) `Z_law : P.map Z = gaussianReal 0 1` field で `Z = 0` vacuous-bypass を構造的に封鎖。片方だけでは insufficient (`Z_law` のみだと predicate ≡ False、lift のみだと `Z=0` bypass survive)。
- 教訓: 「結合体に縛り field を 1 つ足せば vacuous-bypass が閉じる」は不十分 — field 間の独立 existential / `Z` 自体の制約 / 型の表現力 (ℝ vs EReal) の 3 軸を同時にチェック。

# Shannon: `IsDeBruijnRegularityHyp` honest refactor サブ計画

**Status**: CLOSED ✅ — `IsDeBruijnRegularityHyp` を共有 density witness 形に refactor し、`integrable_deriv` 単独の trivial 充足 (`density_path := 0`) を構造的に封鎖。de Bruijn integration の honest 化に寄与。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。
**Parent**: [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md)

## 要点 (≤5 行)
- slug `@audit:staged(epi-debruijn-regularity)` はコード残存 (predicate は依然 load-bearing、`reg_at` が genuine `HasDerivAt` content を保有)。
- honest 化パターン (再利用可): `density_path` を top-level field に昇格し `reg_at`/`integrable_deriv` を同一 witness で要求 + `density_t_eq` で内蔵 `density_t` を pin → 退化 witness が `reg_at` 側で真の derivative `1/(2(v+t))≠0` と矛盾して構成不能。prior art は `IsHeatFlowFamilyHyp`。

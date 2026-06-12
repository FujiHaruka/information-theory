# EPI Stam inequality — discharge plan

**Status**: CLOSED ✅ — Stam discharge chain は route-T 後継が完全 supersede、EPI family の実 sorry は 0。本 plan の Stam-bridge / Step3Body 系は履歴。(Stam Step 2: re-scope candidate — see 要点)
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

- 親: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md)
- sister: [`epi-stam-to-conclusion-plan.md`](./epi-stam-to-conclusion-plan.md) / [`epi-debruijn-integration-plan.md`](./epi-debruijn-integration-plan.md)

## 要点

Stam inequality `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)` の density-level discharge。Cover-Thomas Lemma 17.7.2 を 4 段で構成した route (再開時に再利用できる technical approach):

1. Blachman score-of-convolution identity: `s_{X+Y}(z) = E[s_X(X) | X+Y=z]`
2. Cauchy-Schwarz: `J(X+Y) ≤ λ² J(X) + (1-λ)² J(Y)` (`condVar_ae_le_condExp_sq`)
3. λ-optimization: `λ_min = J(Y)/(J(X)+J(Y))` 閉形 (`stam_lambda_min`)
4. inverse 形: `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)` (`stam_inverse_form_of_harmonic_mean`)

**Stam Step 2 re-scope candidate (再開の入口)**: Step 2 (Cauchy-Schwarz convex Fisher bound) は **Rioul 2011 §II-C** 経路 (score-conditional-mean identity + total variance decomposition) で **~100 行 density-level computation** と見積もり可能 (従来 ~300 行 PR 級見積りより小)。再見積もり後に keep scope へ戻す余地あり。詳細 → roadmap Ch.17 行 + `ch17-inequalities-status.md`。

Mathlib base (再利用補題): `IndepFun.pdf_add_eq_lconvolution_pdf` / `condExp_ae_eq_integral_condDistrib_id` / `hasDerivAt_integral_of_dominated_loc_of_deriv_le`。

撤退ライン (履歴、全 Phase 完了で発火なし): L-Stam-A-α (V1↔V2 bridge) / L-Stam-B-α (畳み込み smooth witness) / L-Stam-C-α (score L² integrability) / L-Stam-C-β (λ-opt IVT、`stam_lambda_min` 閉形で不要) / L-Stam-D-α (partial discharge)。

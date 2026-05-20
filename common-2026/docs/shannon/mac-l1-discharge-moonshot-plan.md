# T3-B L-MAC1 Partial Discharge (joint typicality multi-user) — Moonshot Plan

> **Parent**: T3-B Multiple Access Channel (`docs/textbook-roadmap.md` §Tier 3,
> Cover-Thomas Ch.15.3, MAC achievability).
>
> 実態整合 (2026-05-20): **DONE-HONEST-HYPS (計画通り、partial discharge) — plan の「Drafting」表記は STALE**。`Common2026/Shannon/MACL1Discharge.lean` (26337 B, 0 sorry) に L-MAC1-A/B/C 実装済: `macJointlyTypicalSet_card_le` (MACL1Discharge.lean:204、実証明 — φ-injection で 3-tuple JTS を α₁×α₂×β 上の joint typical set に埋め込み `typicalSet_card_le` 適用)、`macJointlyTypicalSet_prob_tendsto_one` (:281、実証明 — 4 single-axis good event の交差 → 各 `typicalSet_prob_tendsto_one`)。publish-layer hook `mac_capacity_region_inner_bound_with_joint_typ_aep` (:532) は親の `:= h_existence` pass-through (計画通り、4-error-event Bonferroni body = L-MAC1-D は deferred)。FLAW なし。Common2026.lean に import 済。
>
> **Status (2026-05-20):** Drafting. Parent file `MultipleAccessChannel.lean`
> (637 lines, 2026-05-19) is fully published in statement-level
> hypothesis pass-through form with `_h_joint_typ : True` placeholder for
> L-MAC1. This plan publishes a **partial discharge layer** —
> `Common2026/Shannon/MACL1Discharge.lean` (~400-700 lines) — that
> introduces a concrete **3-tuple joint typical set** and proves the
> AEP-style probability bound + cardinality bound for it, reusing the
> existing 2-user `jointlyTypicalSet` plumbing from `ChannelCoding.lean`.

## Approach (overall strategy / shape of solution)

The full L-MAC1 discharge (4 error events `E₁..E₄` + Bonferroni union bound
+ AEP-by-counting, ~500-800 lines, Cover-Thomas eqs. 15.65-15.84) is out
of reach in a single session. The partial discharge below targets the
**plumbing fragment** that the full proof depends on, which we can
quote-verbatim from `ChannelCoding.lean`'s existing 2-user plumbing by
**iterated pairing**:

> Define the 3-tuple joint sequence
> `macJointSequence X1s X2s Ys i ω := (X1s i ω, X2s i ω, Ys i ω)`,
> view it as a single-axis sequence over the product alphabet
> `α₁ × α₂ × β`, and instantiate the existing `typicalSet` plumbing on
> that. The resulting `macJointlyTypicalSet`'s **AEP probability bound**
> and **cardinality bound** then descend directly from
> `typicalSet_prob_tendsto_one` and `typicalSet_card_le`.

This is the **3-axis analogue** of the 2-user `jointlyTypicalSet`
construction (`ChannelCoding.lean:301`, defined as the intersection of
three single-axis predicates — X-, Y-, joint-axis typicality). Our
3-tuple version is the intersection of three single-axis predicates
projected onto the natural reshape `(Fin n → α₁ × α₂ × β) ≃
(Fin n → α₁) × (Fin n → α₂) × (Fin n → β)`.

This descends to **L-MAC1-A** (3-tuple JTS definition + basic properties),
**L-MAC1-B** (one-sided AEP `P → 1`), **L-MAC1-C** (SW-style conditional
slice X1-fiber for the (X1,X2,Y)-joint typical set). The full L-MAC1
discharge (4 error events + Bonferroni) is **deferred** — what this layer
publishes is the foundational **typical set machinery** that downstream
discharges can quote against.

The publish-layer hook is a new partial-discharge variant of
`mac_capacity_region_inner_bound`:

```lean
theorem mac_capacity_region_inner_bound_with_joint_typ_aep
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
    -- Concrete joint-typicality AEP, in place of `_h_joint_typ : True`:
    (h_aep : ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
              (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β),
              -- (standard i.i.d. + measurability) →
              -- Tendsto (fun n => μ {ω | (X1, X2, Y)_n ∈ macJointlyTypicalSet}) → 1
              True)  -- still abstract; the **layer** below this exposes the AEP statement concretely
    (h_existence : MACInnerBoundExistence ...) :
    MACInnerBoundExistence ... := h_existence
```

In practice we publish the **AEP statement** as a named theorem
`macJointlyTypicalSet_prob_tendsto_one` and the parent placeholder is
left as `True` (still pass-through) — the discharge is "partial" in the
sense that the typical-set machinery is now concretely defined and the
key AEP lemma is published, so the remaining work for full L-MAC1 is
restricted to the 4-error-event Bonferroni body which can sit *on top
of* the present file.

## Per-file breakdown

### File: `Common2026/Shannon/MACL1Discharge.lean`

Imports: `Common2026.Shannon.MultipleAccessChannel`
(brings `ChannelCoding` transitively).

Namespace: `InformationTheory.Shannon`.

#### Section 1 — 3-tuple joint sequence and basic measurability

- `macJointSequence X1s X2s Ys : ℕ → Ω → α₁ × α₂ × β`,
  `i ω ↦ (X1s i ω, X2s i ω, Ys i ω)`.
- `@[simp] macJointSequence_apply`.
- `measurable_macJointSequence` — from the three component measurabilities.

#### Section 2 — 3-tuple jointly typical set

- `macJointlyTypicalSet μ X1s X2s Ys n ε :
    Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β))` —
  defined as the intersection of:
  * `x1` is X1-typical,
  * `x2` is X2-typical,
  * `y` is Y-typical,
  * `(fun i => (x1 i, x2 i, y i))` is `(X1, X2, Y)`-joint typical.
- `mem_macJointlyTypicalSet_iff`.
- `measurableSet_macJointlyTypicalSet`, `macJointlyTypicalSet_finite`.

#### Section 3 — Cardinality bound (L-MAC1-A)

- `macJointlyTypicalSet_card_le` — via embedding into the joint
  single-axis typical set on `α₁ × α₂ × β` + `typicalSet_card_le`.
  Conclusion: `card ≤ exp(n · (H(X₁,X₂,Y) + ε))`.

#### Section 4 — AEP-style probability tendsto one (L-MAC1-B)

- `macJointlyTypicalSet_prob_tendsto_one` — Probability that the
  product block `(jointRV X1s, jointRV X2s, jointRV Ys)` lies in
  `macJointlyTypicalSet` tends to `1`. Proved by union-bounding the
  complement against four single-axis "bad" events (X1, X2, Y, joint),
  each `→ 0` by `typicalSet_prob_tendsto_one`.

#### Section 5 — Conditional X1-slice (L-MAC1-C, SW-style plumbing)

- `macConditionalTypicalSlice μ X1s X2s Ys n ε (x2, y)` —
  the X1-fiber at fixed `(x2, y)`. Concretely
  `{ x1 | (x1, x2, y) ∈ macJointlyTypicalSet … }`.
- Basic lemmas: `_finite`, `_subset_X1_typicalSet`,
  `_empty_of_not_jointly_typ` (i.e. when (x2, y) fails the
  (X2,Y)-joint axis condition, the slice is empty).

#### Section 6 — Publish-layer hook

- `mac_capacity_region_inner_bound_with_joint_typ_aep` — a thin
  partial-discharge wrapper that takes the concrete AEP statement
  on the caller side and routes it through `trivial` into the parent
  `mac_capacity_region_inner_bound`. Body: `:= h_existence` (verbatim
  identity wrap, matching the parent's pass-through pattern).

## 撤退ライン (確定発動)

- **L-MAC1-A** (3-tuple JTS definition + cardinality bound): publishable
  in this file as `macJointlyTypicalSet_card_le`.
- **L-MAC1-B** (one-sided AEP `P → 1`): publishable in this file as
  `macJointlyTypicalSet_prob_tendsto_one`.
- **L-MAC1-C** (SW-style conditional X1-slice): publishable as
  `macConditionalTypicalSlice` + basic finiteness/inclusion lemmas.
- **L-MAC1-D** (4-error-event Bonferroni body): **deferred**. The full
  Cover-Thomas eqs. 15.65-15.84 / Theorem 15.3.3 body would weld the
  cardinality + AEP into a `Pr[error] ≤ exp(-n(I - 3ε))` style bound,
  ~500-800 additional lines. Not in scope here.

## Constraints

- Do not modify `Common2026/Shannon/MultipleAccessChannel.lean`.
- Do not touch `Common2026.lean` (publish-via-`lake env lean` only).
- Do not touch `docs/textbook-roadmap.md`.
- No `import Mathlib`.
- 0 sorry / 0 warning / `lake env lean` silent.

## Definition of Done

- `lake env lean Common2026/Shannon/MACL1Discharge.lean` silent.
- 0 sorry, ≤ negligible warnings.
- `wc -l` reported in the parent commit message.

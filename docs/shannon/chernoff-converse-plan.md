# Chernoff converse — sub-plan

**Parent**: [`docs/textbook-roadmap.md`](../textbook-roadmap.md) (Ch.11 Hypothesis testing & large deviations)

## Context

Cover–Thomas Theorem 11.9.1 (Bayesian hypothesis testing). The **achievability** half is
done: `chernoff_lemma_achievability` (`Chernoff/Basic.lean:996`) gives
`chernoffInfo P₁ P₂ ≤ liminf_n -(1/n) log bayesErrorMinPmf` via `bayesErrorMinPmf_le_half_Z_pow`
(the `min(a,b) ≤ a^{1-λ}b^λ` upper bound). The **converse**
`limsup_n -(1/n) log bayesErrorMinPmf ≤ chernoffInfo P₁ P₂` (the optimal error exponent
cannot exceed the Chernoff information) is the missing half. Roadmap flagged it
"Sanov LDP ✅ から将来 1 段落 corollary 可能"; gateway evaluation (2026-06-27) reclassified it
as **tractable / moderate, not a wall and not a one-paragraph triviality**.

The hardest conceptual piece — the I-projection (Csiszár) Pythagorean theorem — is already
genuine in-project: `CsiszarProjection.csiszar_pythagoras_inequality`
(`klDivPmf P Q ≥ klDivPmf P Q* + klDivPmf Q* Q` for the I-projection `Q*` of `Q` onto convex `K`)
+ `csiszar_projection_exists` / `csiszar_projection_unique` / `csiszar_first_order_condition`.
This immediately yields `⨅_{p∈K} klDivPmf p Q = klDivPmf Q* Q`. The Sanov LDP equality
`Sanov.sanov_ldp_equality` (`TendstoSandwich.lean:128`) supplies the matching large-deviation
*lower* bound on a type-class union, with rate the I-projection divergence.

## Approach

Lower-bound the Bayes error by the `P₁`-probability of the error region (a likelihood-ratio
test region = a union of empirical type classes), then apply the Sanov LDP lower bound whose
rate equals the I-projection divergence, then identify that divergence with `chernoffInfo`
through the exponential-tilt mediator `chernoffMediator P₁ P₂ λ* = P₁^{1-λ*}P₂^{λ*}/Z(λ*)`,
which is exactly the I-projection of `P₁` onto the divergence-equalising half-space.

Shape so the existing assets are usable as-is:
- the Sanov side already returns `Tendsto … (𝓝 (-(klDivSumForm_ofVec P …)))` — keep the rate
  in that `klDivSumForm` shape and bridge to `klDivPmf` once (the bridge already exists in
  `Sanov.lean`);
- the I-projection side already returns the Pythagorean inequality — feed `chernoffMediator λ*`
  as `Qstar` and the half-space as `K`.

Key identity (machine-verified core atom, `lemma chernoffMediator_klDiv_eq`):
`klDivPmf (chernoffMediator P₁ P₂ λ) P₁ = λ · (∑ a, T_λ(a)·log(P₂ a/P₁ a)) - log Z(λ)`
for full-support pmfs. At the optimal `λ*` (where `d/dλ log Z = mean LLR = 0`, the interior
first-order condition of the `chernoffInfo` inf) the first term vanishes, giving
`klDivPmf (chernoffMediator λ*) P₁ = -log Z(λ*) = chernoffInfo P₁ P₂`.

## Phases

- **Phase A — pmf-level variational identity** (no Sanov, no n-letter). `chernoffMediator_klDiv_eq`
  (the closed form above) + `chernoffMediator_is_Iprojection` (T_λ* satisfies the first-order
  condition for the half-space, via `csiszar_first_order_condition`) + `chernoffInfo_eq_Iproj_div`
  (`chernoffInfo = ⨅_{p∈K} klDivPmf p P₁`). The interior-`λ*` balance `mean LLR = 0` is the one
  genuine analytic obligation (derivative of `log Z`); degenerate boundary `λ*∈{0,1}` (P₁,P₂
  too far apart) handled separately or excluded by a non-overlap regularity hyp.
- **Phase B — error region = type-class union + Sanov lower bound.** Express
  `{x : P₁ⁿ(x) ≤ P₂ⁿ(x)}` as `⋃ c∈E n, typeClassByCount c` with `E n` the discretised
  half-space. **Route corrected (2026-06-27 inventory)**: instantiate
  `sanov_ldp_lower_bound_pointwise` (`Sanov/LiminfBound.lean:132`, **no `h_minimizer` premise**),
  NOT `sanov_ldp_equality` — the converse only needs the liminf lower bound `-D ≤ liminf`, and
  `h_minimizer` is undischargeable because `chernoffHalfSpace` requires strict positivity while
  Sanov quantifies over boundary type-classes with zero entries. Closest precedent:
  `Hoeffding/TradeoffExp.lean` (`E_r` / `steinTypeII_exp` / `Qstar_perturb`) does the identical
  Sanov-instantiation; Phase B is largely a re-skin. Decomposition H1–H8 +
  the 2-world bridge facts → `docs/shannon/chernoff-converse-phaseB-inventory.md`.
  **Headline `chernoff_converse` must add `[Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]`** (Sanov demands them).
- **Phase C — assemble.** `bayesErrorMinPmf ≥ (1/2)·P₁ⁿ(region)` (easy: `∑ min ≥ ∑_region P₁ⁿ`);
  combine with Phase B limit and Phase A identity → `limsup -(1/n) log bayesError ≤ chernoffInfo`.
  Headline `chernoff_converse`.

## Status

- 2026-06-27: gateway evaluation done (tractable verdict). **Phase A core atom
  `chernoffMediator_klDiv_eq` DONE** (`Chernoff/Converse.lean`, sorryAx-free).
- **Phase A COMPLETE** (`Chernoff/Converse.lean`, all sorryAx-free, machine-verified
  `[propext, Classical.choice, Quot.sound]`). 5 decls added on top of the atom:
  `chernoffMediator_log_sub` (per-term log identity) · `chernoffLogZ_hasDerivAt`
  (`d/dλ log Z(λ) = ∑ a, T_λ(a)·log(P₂ a/P₁ a)`, the analytic core via `HasDerivAt.const_rpow`
  + `.log`) · `chernoffMediator_balance` (Fermat FOC at interior λ* ⟹ balance = 0) ·
  `def chernoffHalfSpace` + `chernoffInfo_eq_mediator_div` (`chernoffInfo = klDivPmf (T_λ*) P₁`) ·
  `chernoffMediator_isMinOn` (`IsMinOn (klDivPmf · P₁) K (T_λ*)`). Interiority `0 < λ* < 1` is the
  only non-degeneracy hyp (balance is *derived*, not assumed — Cramér-`Var>0` analogue). Selection
  facts `hlam_min`/`hinfo` discharge from `chernoffInfo_attained`. File still standalone (not
  root-wired; 0-`sorry` invariant — wire only once `chernoff_converse` headline is proven).
- **Next**: Phase B — Sanov lower bound (heaviest). Express error region
  `{x : P₁ⁿ(x) ≤ P₂ⁿ(x)}` as a type-class union and instantiate `sanov_ldp_equality`
  (`TendstoSandwich.lean:128`) with Q=P₁, P=T_λ*, minimiser condition from `chernoffMediator_isMinOn`
  / Pythagoras; rate `klDivSumForm_ofVec T_λ* (P₁.real∘singleton)` ↔ `klDivPmf (T_λ*) P₁ = chernoffInfo`.
  Then Phase C (assembly). Only commit a proven (sorryAx-free) `chernoff_converse` headline.

## Retreat lines

- If interior-`λ*` balance proves heavy (non-smooth `log Z` at boundary): state `chernoff_converse`
  under a regularity hyp `0 < λ* < 1` (the non-degenerate / overlapping-support case, which is the
  textbook setting) and leave the boundary case as honest `sorry + @residual`. Not a load-bearing
  hyp — it is a non-degeneracy precondition (cf. the `Var > 0` precedent in Cramér).

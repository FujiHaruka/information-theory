# Shannon-Hartley converse C2/C4 — design + inventory (leg 25, proof-pivot-advisor validated)

**Parent**: [shannon-hartley-phase2-spectral-plan.md](shannon-hartley-phase2-spectral-plan.md) (R4-CONV section).

Read-only design validation of the FINAL converse frontier (C2 Gauss rotation → C4 water-filling
→ C0/assembly), after C3 was FULLY CLOSED (leg 25). Verdict: **math SOUND + non-circular, but the
C3 headline is a WEAKER RELATIVE than C4 needs** — one real, in-tree-fixable design gap. No Mathlib gap.

## One-line verdict

C2/C4 is pure plumbing (no wall), BUT do the gateway atoms + the per-coordinate companion FIRST —
the current C3 headline exposes only `∑P'ᵢ ≤ T·P`, which is coarser than C4's water-filling needs.

## PROGRESS (leg 26, 2026-07-18) — gateway atoms + count-domination + per-coord exposure ALL CLOSED

The gateway-atom-first plan succeeded: both atoms passed ⇒ C2/C4 confirmed pure plumbing (no wall).
The highest-risk piece (count domination) is CLOSED sorry-free + honesty-auditor @audit:ok. Done this leg:

- **Gateway atom 1** `frame_form_le_op_form` (`TimeBandLimiting.lean`, after C1) — Bessel domination by
  operator form, sorry-free (`39d7e613`). Takes NO `hW`.
- **Gateway atom 2 / per-coord companion** `parallel_per_input_mi_le_sum_percoord`
  (`MixtureDensity.lean`, before the original) — exposes `∀ i, P'ᵢ ≤ ∫(xᵢ)²∂p`; original is now a thin
  corollary (`f87a9ee0`). sorry-free.
- **(a) Count domination CORE** `gram_high_eigen_finrank_le_prolateCount` + def `bandGramEigenvalues`
  (new file `ShannonHartleyConverseCount.lean`) — `#{band-Gram eigenvalues > c} ≤ prolateCount`,
  sorry-free (`c2d31b84`). Uses Mathlib `Matrix.gram`/`isHermitian_gram`/`eigenvalues` (NO
  linear-algebra self-build) + atom 1 + C1. **@audit:ok** (`0d2970f4`, def non-degeneracy confirmed).
- **Real→E wrapper** `gram_high_eigen_finrank_le_prolateCount_real` + def `testFnLift` (same file) —
  facade for real `ℝ→ℝ` testFn; extra hyp `hmem : ∀ i, MemLp (φ i) 2 volume` = genuine regularity
  (auditor built a Vitali-set counterexample confirming it is NOT derivable from `h_on`), sorry-free
  (`26466bb3`), **@audit:ok**.
- **Per-coord C3 headline** `contAwgn_operational_converse_percoord` (`ShannonHartleyConverse.lean`,
  before the original) — exposes `∀ i, P'ᵢ ≤ ∫ x, (x i)² ∂(contAwgnSignalLaw c N₀)`; original is a DRY
  corollary (`1db1370c`). sorry-free. **Closes the per-coord gap named below.**

**Remaining (fresh-judgment, intricate — leg 27+)**: (c) C2 rotation/ellipsoid (connect the observation
second moments `∫(xᵢ)²∂signalLaw` to `νᵢQᵢ` = `bandGramEigenvalues` via Gaussian rotation invariance)
→ C4 water-filling (head/tail split + double limits T→∞, c→0) → C0 `contAwgn_le_shannonHartley` (state
as real inequality) → `le_antisymm` assembly closing `contAwgn_eq_shannonHartley`.

## THE GAP (name-the-pinned-invariant guard fired)

`contAwgn_operational_converse` (`ShannonHartleyConverse.lean:593`, CLOSED) forwards only the
plain-sum constraint `∑ᵢ P'ᵢ ≤ T·P` in the ORIGINAL observation coordinates (body L646–651:
`obtain ⟨P', _, hP'sum, hP'bound⟩` — the per-coordinate second-moment bound is dropped at the
∃-boundary). With `c.k` a FREE field and only `∑P'ᵢ ≤ T·P`, the bound is genuinely wrong: maximizing
`∑ᵢ ½log(1+P'ᵢ/(N₀/2))` over a plain-sum budget with `c.k → ∞` gives `T·P/N₀` (W-independent) — NOT
Shannon-Hartley. The count `#{νᵢ>c} ≤ prolateCount` alone does not rescue it: a low-gain coord
(νᵢ≤c) may still carry `P'ᵢ = T·P` under a plain-sum budget, so the tail is unbounded.

**Root cause**: `parallel_per_input_mi_le_sum` (`MixtureDensity.lean:901`) sets `P'ᵢ := Var(Yᵢ)−Nᵢ`
and PROVES the per-coordinate bound `P'ᵢ ≤ ∫(xᵢ)²∂p` internally (`h_each`, ~L935) but discards it,
exposing only `∑P'ᵢ ≤ P`. **C4 must not consume the C3 headline** — it needs the per-coordinate
ellipsoid. Fix = a companion lemma exposing `h_each` (below). This is in-tree plumbing, not a wall.

## How the νᵢ enter (decisive — channel stays EQUAL-noise N₀/2)

νᵢ enter ONLY through the signal-power ellipsoid (log argument via signal power), never the noise:

1. Observation `S = Φ*f`, `Φ*f = (⟨f, P_W φᵢ⟩)ᵢ` (band-limited f ⇒ `⟨f,φᵢ⟩=⟨f,P_W φᵢ⟩`). Gram
   `Gᵢⱼ = ⟨P_W φᵢ, P_W φⱼ⟩`, eigenvalues νᵢ, ℝ^k eigenbasis uᵢ; E-space frame `eᵢ := Φuᵢ/√νᵢ`
   (orthonormal in E, band-limited).
2. Rotate the channel by orthogonal `U=(uᵢ)`. Isotropic Gaussian noise is INVARIANT under U
   (`stdGaussian_map` — keeps the rotated channel equal-noise so `parallel_per_input` still applies).
   Rotated signal `S̃=UᵀS`, `E[S̃ᵢ²]=νᵢQᵢ`, `Qᵢ:=E⟨f,eᵢ⟩²`, `∑Qᵢ = tr(R|span eᵢ) ≤ E‖f‖² ≤ T·P`.
3. Per-coord ellipsoid `P'ᵢ ≤ E[S̃ᵢ²] = νᵢQᵢ` (variance ≤ 2nd moment), then
   `∑½log(1+P'ᵢ/(N₀/2)) ≤ ∑½log(1+νᵢQᵢ/(N₀/2))` (log monotone in P'ᵢ).
4. C4 split `∑ = ∑_{νᵢ>c}+∑_{νᵢ≤c}`. Tail `∑_{νᵢ≤c}½log(1+νᵢQᵢ/(N₀/2)) ≤ c·T·P/N₀` (νᵢ≤c +
   ∑Qᵢ≤T·P — independent of the free c.k; this tames unbounded c.k). Head: `#{νᵢ>c} ≤ prolateCount
   ≤ 2WT + D/c` (C1 + `prolateCount_le`), water-fill ≤(2WT+D/c) coords with ∑Qᵢ≤T·P. Limits: fix c,
   T→∞ (prolateCount/T→2W, D/(cT)→0) ⇒ `W log(1+P/(N₀W))`, then c→0 kills the tail.
   Converse needs only the UPPER count half (`prolateCount_le`); `le_prolateCount` (achievability
   half) not needed. `νᵢ≤1` holds (`⟨ΦΦ*g,g⟩ ≤ ‖Q_T g‖² ≤ ‖g‖²`).

**Non-circular count bridge** (the real content — UNBUILT): for band-limited g,
`⟨ΦΦ*g,g⟩ = ∑ⱼ⟨Q_T g,φⱼ⟩² ≤ ‖Q_T g‖² = ⟨A g,g⟩` (Bessel on time-limited orthonormal φⱼ +
`inner_timeBandLimitingOp_self_eq`). On `S=span{eᵢ:νᵢ>c}`, `⟨ΦΦ*g,g⟩>c‖g‖²`, so A-Rayleigh>c on S
⇒ C1 gives `finrank S = #{νᵢ>c} ≤ prolateCount`. Dominates the arbitrary code's Gram spectrum by
the OPERATOR spectrum — genuinely non-circular (does NOT assume codewords = prolate basis).

## ⚠️ C1's role is under-represented in the C3 inventory

Inventory item 6 asserts `#{νᵢ>c}≤prolateCount "(C1)"` as if direct. It is NOT.
`finrank_le_prolateCount_of_form_gt` (C1, `TimeBandLimiting.lean:2617`, @audit:ok) is the ABSTRACT
lemma "any submodule S with A-Rayleigh>c has finrank≤prolateCount" — it names no Gram matrix. The
specialization (build Gram in E, Hermitian eigendecomp, realize E-space eᵢ, prove Bessel
domination, apply C1) is genuine unbuilt self-build (~60–120 lines) = **the mathematical heart of
C2 and the highest-risk piece, NOT the Gaussian rotation**.

## Concrete lemma statements (regularity hyps only — no bundling)

(a) **Count domination** (new core; reduces to C1):
```lean
theorem gram_high_eigen_finrank_le_prolateCount (T W c : ℝ) (hc : 0 < c)
    {k : ℕ} (φ : Fin k → ℝ → ℝ)                         -- the code's testFn
    (h_on : ∀ i j, ∫ t, φ i t * φ j t = if i = j then 1 else 0)
    (h_supp : ∀ i, Function.support (φ i) ⊆ Set.Icc 0 T) :
    #{ i | gramEigenvalue (P_W ∘ φ) i > c } ≤ prolateCount T W c
```
Body: Gram eigendecomp → `S=span{eᵢ:νᵢ>c} ⊆ bandLimitSubspace` → Bessel domination →
`finrank_le_prolateCount_of_form_gt`.

(b) **Per-coord operational converse** (companion to `parallel_per_input_mi_le_sum`; exposes the
internal `h_each`). **Do NOT edit `parallel_per_input_mi_le_sum` in place** — 3 direct consumers
(`parallel_bddAbove_miImage`, `isParallelGaussianPerCoordRegularity_of_pieces`, and the C3 headline).
A companion = 0 ripple. ~30-line near-clone:
```lean
theorem parallel_per_input_mi_le_sum_percoord {n} (P) (hP) (N) (hN) (h_meas) (h_pmeas)
    (p) [IsProbabilityMeasure p] (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    ∃ P', (∀ i, 0 ≤ P' i) ∧ (∀ i, P' i ≤ ∫ x, (x i)^2 ∂p)       -- NEW per-coord conjunct
        ∧ (mutualInfoOfChannel p (parallelGaussianChannel N ..)).toReal
            ≤ ∑ i, (1/2) * Real.log (1 + P' i / (N i))
```
(`∑P'ᵢ≤P` becomes a corollary.)

(c) **Rotation invariance + ellipsoid** (C4 input): given rotated signal law p̃,
`∫x̃ᵢ²∂p̃ = νᵢQᵢ`, `∑Qᵢ≤T·P`, `νᵢ≤1`, `#{νᵢ>c}≤prolateCount` (from (a)). Output for C4: ellipsoid + count.

## Asset inventory (file:line + verbatim sig where load-bearing; TC brackets verbatim)

**Gaussian rotation (Mathlib, present):**
- `ProbabilityTheory.stdGaussian_map` — `Mathlib/.../Gaussian/Multivariate.lean:128`.
  `(f : E ≃ₗᵢ[ℝ] F) → (stdGaussian E).map f = stdGaussian F`. TC on F:
  `[NormedAddCommGroup F][InnerProductSpace ℝ F][MeasurableSpace F][BorelSpace F]`; on E:
  `[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]`.
- `map_pi_eq_stdGaussian` — `Multivariate.lean:137`. ONLY `gaussianReal 0 1`. errorProbAt noise is
  `gaussianReal (obs) (N₀/2)` (mean≠0, var≠1) ⇒ affine split via `gaussianReal_map_const_mul` +
  `gaussianReal_map_add_const` (`Gaussian/Real.lean`) FIRST. NOT a one-line rw.
- `stdGaussian_eq_map_pi_orthonormalBasis` — `Multivariate.lean:146` (rotation to any ON eigenbasis).

**Domination / count bridge (in-tree, plumbing — NO Mathlib gap):**
- `finrank_le_prolateCount_of_form_gt` — `TimeBandLimiting.lean:2617` (C1, @audit:ok).
  `(hc:0<c)(S)(hS:∀x∈S,x≠0→c*‖x‖²<(inner ℂ (timeBandLimitingOp T W x) x).re) → finrank ℂ S ≤ prolateCount T W c`.
- `inner_timeBandLimitingOp_self_eq` — `TimeBandLimiting.lean:2086`.
  `(inner ℂ (A f) f).re = ∫ t in Icc 0 T, ‖inner ℂ (bandKernelLp W t) f‖²` (⟨Af,f⟩ = windowed energy).
- Bessel: Mathlib `Orthonormal.sum_inner_products_le` for `∑ⱼ⟨Q_T g,φⱼ⟩²≤‖Q_T g‖²`.
- Hermitian finite-dim eigendecomp: `LinearMap.IsSymmetric.eigenvectorBasis` /
  `Matrix.IsHermitian.spectral_theorem` — for the k×k Gram matrix.

**Real→E bridge (achievability built the FORWARD dir; converse needs REVERSE):**
- `isBandlimited_of_bandLimitSubspace_ae` — `TimeBandLimiting.lean:4346`;
  `exists_real_bandlimited_onb` — `:4368` (prolate eigenbasis → real band-limited ON). C2 needs the
  reverse: real testFn φᵢ → E-space `P_W φᵢ` + Gram. Pieces: `Complex.ofRealCLM`, `MemLp.toLp`,
  `bandLimitSubspace`, `bandLimitProj_apply_eq_inner` (`:2075`). Moderate plumbing, no gap.
- `parallel_per_input_mi_le_sum` — `MixtureDensity.lean:901` (needs companion (b)).

No genuine Mathlib gap (loogle-0 + in-project grep clear). Every atom is Mathlib (stdGaussian /
Hermitian spectral) or in-tree (C1 + self-inner + real↔E bridges).

## Recommended order (gateway-atom-first — de-risk BEFORE a full C2 leg)

1. **Gateway atom 1 (highest-risk de-risk)** — the domination inequality standalone:
```lean
lemma frame_form_le_op_form (T W : ℝ) (hW : 0 ≤ W) {k} (φ : Fin k → E)
    (h_on : Orthonormal ℂ φ) (h_tl : ∀ i, φ i ∈ timeLimitSubspace T)
    (g : E) (hg : g ∈ bandLimitSubspace W) :
    ∑ i, ‖inner ℂ g (φ i)‖^2 ≤ (inner ℂ (timeBandLimitingOp T W g) g).re
```
Body = Bessel + `inner_timeBandLimitingOp_self_eq`. If clean, the count-domination is de-risked and
C1 wires in. If it fights, the Gram construction in E is where a leg balloons — surface first.

2. **Gateway atom 2 (same session)** — companion (b) `parallel_per_input_mi_le_sum_percoord`,
   exposing the already-proven `h_each`. Confirms C4's per-coord input type-checks.

If both atoms pass ⇒ C2/C4 is pure plumbing with no wall. Then: (a) count domination → (c) rotation
+ ellipsoid → C4 water-filling + limits → C0 `contAwgn_le_shannonHartley` → `le_antisymm` assembly.

## Honesty / circularity

- Retreat line does NOT trigger; no new Mathlib gap. Only sanctioned exit remains
  `sorry + @residual(plan:shannon-hartley-phase2-spectral-plan)`; no wall slug warranted.
- Circularity guard respected: νᵢ/2WT appear only as C1's CONCLUSION, never a def input. The
  domination bridge dominates the code's Gram spectrum by the OPERATOR spectrum (non-circular).
- Building a new lemma that removes a sorry = proof-done → independent honesty-auditor per session.

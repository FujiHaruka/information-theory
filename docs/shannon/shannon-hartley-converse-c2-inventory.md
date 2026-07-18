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

## LEG 27 BUILD PLAN (proof-pivot-advisor-locked, 2026-07-18)

Independent advisor pass reconciled the leg-25 design with the leg-26 per-coord C3 headline +
achievability limit precedents. Verdicts:

**Q1 — rotation is UNAVOIDABLE + path (b) recommended**: the C3 headline exposes `P'ᵢ ≤ Rᵢᵢ`
(diagonal of `R = (1/M)∑ₘ obs obsᵀ`) in the ORIGINAL basis; `∑½log(1+Rᵢᵢ/N)` is Schur-concave so it
CANNOT be upper-bounded by the eigenvalue log-sum — you must rotate to the Gram eigenbasis. **Path (b)
= physically build a rotated `ContAwgnCode c̃`** (rotated `testFn`, `decoder∘U`, same encoder/W/P/M/k) +
prove `c̃.averageError = c.averageError`, then apply the audited C3 to `c̃` as a BLACK BOX (~265–365
lines). Beats path (a) MI-level reshape (~330–430, re-derives audited C3 abstractly). Lesson: when a
heavy audited theorem consumes the concrete object, rotate the concrete thing, not the abstract one.
Shared core (needed by either path): **S1** multivariate Gaussian rotation invariance
(`(Measure.pi gaussianReal).map U = Measure.pi (gaussianReal ∘ U)` via `gaussianReal_map_const_mul`/
`_add_const` + `stdGaussian_map`, ~60–90 lines); **S2** real orthogonal eigenbasis of the band-Gram
(`P_W φ` real ⇒ `Matrix.gram ℂ` is real-symmetric ⇒ real eigenbasis, eigenvalues = `bandGramEigenvalues`,
~40–70); **S3** second-moment identity `∫x̃ₐ²∂p̃ = νₐQₐ`, `Qₐ:=(1/M)∑⟨fₘ,eₐ⟩²`, `∑Qₐ = tr R ≤ T·P`,
`νₐ≤1` — **confirmed does NOT need R's eigenvalues**, only that U diagonalizes G (~60–100).

**File architecture (3 layers, avoids import cycle — Main does NOT import Converse/ConverseCount)**:
1. `ShannonHartleyWaterfill.lean` (imports Main): Q2 pure real-analysis. ← leg 27 initial dispatch.
2. `ShannonHartleyRotation.lean` (imports Converse+ConverseCount+Main): S1/S2/S3 → per-code ellipsoid+count.
3. `ShannonHartleyConverseFinal.lean` (imports Waterfill+Rotation): C0 `contAwgn_le_shannonHartley` +
   MOVE `contAwgn_eq_shannonHartley` here for `le_antisymm` (delete Main's copy; `@[entry_point]` +
   README self-heals by name; check `dep_consumers` first — likely a leaf).

**Q2 — fixed-T water-filling (pure real-analysis, no rotation; in Waterfill.lean)**: three lemmas —
`mul_log_one_add_div_monotone {a}(ha:0≤a) : MonotoneOn (fun x => x*log(1+a/x)) (Ioi 0)` (deriv≥0 via
`u/(1+u)≤log(1+u)`, short); `waterfill_head_tail_bound` (head/tail split: tail≤c₀TP/N₀ via log(1+x)≤x,
head≤B·½log(1+TP/(B·N₀/2)) via Jensen concavity + monotone K→B; abstract in count-bound B); and
`waterfill_head_div_tendsto : Tendsto (fun T => count·½log(1+TP/(count·N₀/2))/T) atTop
(𝓝 (bandlimitedAwgnCapacity W N₀ P))` via `prolateCount_div_tendsto` (count/T→2W) + continuity.

**Q3 — C0 (in ConverseFinal.lean)**: Fano REUSES the block in `contAwgn_log_le_of_pos_k`
(`ShannonHartleyAchievability.lean:577-591`): `(1-ε)·log M ≤ [waterfill] + log 2`. Then
`contAwgn_log_le_waterfill` (fixed-T, consumes rotation ellipsoid+count + Q2 split) →
`contAwgnRate_le : contAwgnRate W N₀ P ε ≤ bandlimitedAwgnCapacity W N₀ P / (1-ε)` (mirror
`contAwgnRate_isBoundedUnder`: extract maximizing code via `Nat.sSup_mem`+`contAwgnMaxMessages_bddAbove`,
k=0 via `contAwgn_averageError_of_k_eq_zero`, limsup via `waterfill_head_div_tendsto`, then c₀→0). C0
exact statement (hyps = achievability headline, ≤ reversed):
`theorem contAwgn_le_shannonHartley (W N₀ P : ℝ)(hW:0<W)(hN₀:0<N₀)(hP:0≤P) :
contAwgnOperationalCapacity W N₀ P ≤ bandlimitedAwgnCapacity W N₀ P` — proof `le_of_forall_pos_le_add` +
`ciInf_le_of_le` (BddBelow from `contAwgnRate_nonneg`) choosing ε with `RHS/(1-ε) ≤ RHS+δ`.

**Q4 — build DAG / order**: Q2 (all 3, independent, 0 rotation) FIRST → S1 → S2 → S3 → path-(b) rotated
code + averageError inv → `contAwgn_log_le_waterfill` → `contAwgnRate_le` → `contAwgn_le_shannonHartley`
→ `le_antisymm`. Mathlib atoms all located (`stdGaussian_map` Multivariate:128, `klDiv_map_measurableEquiv`
MutualInfo:47, `le_log_one_add_of_nonneg` Log/Basic:339, `prolateCount_le` TimeBandLimiting:4035) — no wall.

## S2 APPROACH LOCKED (leg 28, proof-pivot-advisor, 2026-07-18) — Approach B, ~80–130 lines, NO wall

The complex-vs-real tension dissolves via TWO facts: (1) `Matrix.IsHermitian.eigenvalues`/`eigenvectorUnitary`
are polymorphic over `[RCLike 𝕜]` ⇒ instantiate at `𝕜:=ℝ` verbatim; (2) `Matrix.orthogonalGroup n R` is a
bare `abbrev` for `unitaryGroup n R` (`UnitaryGroup.lean:295`) ⇒ real `eigenvectorUnitary.2` is DEFINITIONALLY
the `∈ orthogonalGroup` proof `ContAwgnCode.rotate` demands (no bridge lemma).

**Approach B (chosen)**: form real `Gᵣ i j := (gram ℂ v i j).re`, diagonalize over ℝ with
`IsHermitian.spectral_theorem` (`Analysis/Matrix/Spectrum.lean:141`, `Gᵣ = O·diag μ·Oᵀ`) → real `O`, real `μ`;
bridge `#{c<μ} = #{c<bandGramEigenvalues}` at the CHARPOLY level (NOT a direct eigenvalue-bridge lemma):
`charpoly_map` (`Charpoly/Basic.lean:173`) → `charpoly_eq`/`roots_charpoly_eq_eigenvalues`
(`Spectrum.lean:155/159`, both = `∏(X-C eigᵢ)`) → `Polynomial.map_prod` compares the ℝ vs ℂ products →
`roots` + cancel injective `ofReal` ⇒ `Multiset.map μ univ = Multiset.map bandGramEigenvalues univ` → `countP_map`
(`Multiset/Filter.lean:283`) + `countP_eq_card_filter` reduce both filter-cards to `countP (c<·)` on equal multisets.
So `#{c<μ} ≤ prolateCount` via the audited facade. (Rejected: A realify-complex-eigvecs = HIGH risk realification
trap 100–180+ lines; C real-Gram count re-proof = duplicates the @audit:ok 160-line theorem 120–200 lines.)

**GATEWAY ATOM B1 (only substantive content, dispatch FIRST)**: `bandGramReal` —
`gram ℂ (fun i => P_W (testFnLift φ hmem i)) = (fun i j => (gram ℂ v i j).re).map (algebraMap ℝ ℂ)`.
Proof: `testFnLift` is `ofReal`-valued ⇒ `star (testFnLift i) = testFnLift i`; `bandLimitProj_star`
(**already proven**, `TimeBandLimiting.lean:682`: `P_W (star f) = star (P_W f)`) ⇒ each `P_W ψᵢ` star-fixed;
L² inner product of two star-fixed elts = its own conjugate ⇒ each `gram` entry real (~25–40 lines). If B1 fights
>3 turns on `⟪star a, star b⟫ = conj⟪a,b⟫`, split out a named L²-conjugation lemma (don't pivot approaches).
Honesty: `νᵢ := hR.eigenvalues` is a CONCLUSION of spectral_theorem on the code's actual Gram, never a def input
(non-circular); noise stays equal N₀/2 (`rotate_averageError` reuses `(N₀/2).toNNReal`).

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

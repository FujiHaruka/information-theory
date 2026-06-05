# Proof-log — EPI case-1 sum-noise N(0,2) genvar-struct (route B-τ probe)

> Parent plan: `docs/shannon/epi-case1-debruijn-genvar-struct-plan.md`
> Predecessor: `docs/shannon/epi-case1-sum-producer-plan.md`
> Scope of this entry: **GS-0 inventory + GS-1 skeleton probe only** (go/no-go for route B-τ).
> NOT GS-2+ full implementation. Probe `example`s were reverted (file `ZZProbeBTau.lean` deleted).

## VERDICT (2026-06-06): route (B-τ) is **NO-GO as a wrapper-W substitution**

Route (B-τ) — "thread unit noise `W := (Z_X+Z_Y)/√2 ∼ 𝒩(0,1)` into the de Bruijn structure
and reparam time `τ = t·2`" — is **viable on the producer side** (W-law closes genuinely, the
W-producer constructs cleanly), but the **consumer side cannot accept it**. The reparam `τ = 2t`
needed to absorb the variance-2 carrier **desyncs the sum-term de Bruijn derivative from the
X/Y-term derivatives**, which the antitone proof takes at one shared time `t`. The `Z_law = unit`
defect is **load-bearing in the consumer's derivative arithmetic** (not merely a local producer
field), so substituting W does not remove the false statement — it relocates it into a
time-desync that breaks the ratio-Stam combination.

→ **Recommendation: maintain the `Z_law` defect park** (`@audit:defect(false-statement)` at
`EPICase1SumProducer.lean:166`). Genuine closure requires **general-variance de Bruijn
identity surgery** (route b-2: open `IsRegularDeBruijnHypV2.Z_law` to `gaussianReal 0 v_Z` AND
generalize `_entropy_eq` / `_fisher_match` to carrier `t·v_Z`, threading the chain-factor `v_Z`
into the consumer's ratio arithmetic), which is a **larger, separate wave**, not closeable by
the W-substitution shortcut. See "What genuine closure actually requires" below.

---

## Machine-verified probe results (GS-1)

Probe file `InformationTheory/Shannon/ZZProbeBTau.lean` (deleted post-probe), `lake env lean`
clean (only intended `sorry` obligations). Six `example`s:

### Item 1 — W-law closure: **GENUINE, ~15 lines, no new wall** ✅
`P.map (fun ω => (Z_X ω + Z_Y ω) / Real.sqrt 2) = gaussianReal 0 1` proven outright:
- `gaussianReal_add_gaussianReal_of_indepFun hZXZY_indep hZX_law hZY_law` → `P.map (Z_X+Z_Y) = gaussianReal 0 2`
- `Measure.map_map (·/√2) (hZX.add hZY)` → `P.map (S/√2) = (P.map S).map (·/√2)`
- `gaussianReal_map_div_const (√2)` → `(gaussianReal 0 2).map (·/√2) = gaussianReal (0/√2) (2 / mk((√2)²))`
- arith: `0/√2 = 0` (simp); `2 / mk((√2)²) = 2 / mk 2 = 1` via `Real.sq_sqrt` + `NNReal.eq` + `push_cast`/`norm_num`.

### Item 2 — W-producer type integrity: **type-checks clean** ✅
`IsDeBruijnRegularityHyp (X+Y) W P` constructs via the existing X/Y producer machine
`EPICase1RatioLimit.isDeBruijnRegularityHyp_of_methodX_unitnoise` with `S := X+Y`, `noise := W`.
No type mismatch; the producer accepts `W` exactly where it accepts a unit noise. (`noncomputable`
required; W-law fed as item-1 result.)

### Item 3a — `reg_at .Z_law` obligation under W: **`P.map W = gaussianReal 0 1`** ✅
`(h_reg.reg_at t ht).Z_law` has type `P.map (fun ω => (Z_X ω + Z_Y ω) / Real.sqrt 2) = gaussianReal 0 1`
— genuinely satisfiable (W truly unit). The producer-side defect IS removed for the W-structure.

### Item 4 — reparam path identity: **GENUINE, ~4 lines** ✅
`(fun ω => X ω + Y ω + √t · (Z_X ω + Z_Y ω)) = fun ω => X ω + Y ω + √(t*2) · ((Z_X ω + Z_Y ω)/√2)`
via `Real.sqrt_mul ht 2` + `field_simp`. Pointwise: sum path at time `t` = W-path at time `t*2`.

### Item 4b — W-path de Bruijn derivative at carrier-t (unit): **type-checks** ✅
`deBruijn_identity_v2 (X+Y) W ... (h_reg_W.reg_at t ht)` fires for path `(X+Y)+√s·W` giving
`(1/2)·J(density_t @ t)` at time `t` — but this is the path `X+Y+√t·W` (carrier t), NOT the
consumer's sum path `X+Y+√t·(Z_X+Z_Y) = X+Y+√(2t)·W` (carrier 2t).

### Item 4d — CARRIER MISMATCH (the make-or-break): **type-checks, exposes the desync** ⛔
The consumer's sum path `X+Y+√t·(Z_X+Z_Y)` re-expressed via W is the W-path at time `t*2`.
Its de Bruijn derivative therefore sits at `h_reg_W.reg_at (t*2)`, giving `(1/2)·J(density_t @ 2t)`
— evaluated at time `t*2`, **desynced from the X/Y derivatives at time `t`**. The antitone proof
(`csiszarLogRatioGap_hasDerivAt`, `EPIStamToBridge.lean:699`) takes all three derivatives at one
shared `t`. There is no way to feed the W-producer's reg_at-at-`2t` into a shared-`t` combination
without an additional `2·` chain factor that the consumer's `(1/2)·J` arithmetic does not carry.

### Item 4c — `h_conv_id` obligation shape: type-checks (left as sorry, records the obligation) ⛔
The ratio-Stam (`csiszarLogRatioGap_deriv_le_zero`, `:919-922`) requires
`(h_reg_sum.reg_at t ht).density_t x = convDensityAdd (X-dens@t) (Y-dens@t) x`. The RHS convolution
of two carrier-`t` densities has carrier `2t`; a W-producer's `density_t` is pinned (`density_t_eq`)
to carrier `t` (W treated as unit). So `h_conv_id` for a W-threaded sum demands carrier-t = carrier-2t,
unsatisfiable — same carrier drift, relocated.

---

## Why the `Z_law` defect is LOAD-BEARING in the consumer (not a local field)

Decisive trace (`EPIStamToBridge.lean:740-749`): the sum-term derivative in
`csiszarLogRatioGap_hasDerivAt` is
```
deBruijn_identity_v2 (X+Y) (Z_X+Z_Y) (hX.add hY) (hZX.add hZY) hXYZXY ht (h_reg_sum.reg_at t ht)
```
which delegates to `debruijnIdentityV2_holds_assembled` (`FisherInfoV2DeBruijnAssembly.lean:3543`).
That lemma consumes `h_reg.Z_law` via `_entropy_eq` (`:3437`, `hZ_law : gaussianReal 0 1` hardcoded
arg, internal `pPath_eq_convDensityAdd ... (1:ℝ≥0) ...` pins carrier `s·1 = s`, `:3460 hwit1`) and
`_fisher_match` (`:3485`). The conclusion `(d/ds) h((X+Y)+√s·(Z_X+Z_Y)) = (1/2)·J` holds **only if
`Z_X+Z_Y` is unit**. Since its true law is `gaussianReal 0 2`, the TRUE derivative is `(2/2)·J = J`
(carrier scales by 2). The consumer's `(1/2)` factor for the sum term is therefore obtained **by
asserting the false unit law**, which then `:773/785/799` cancels uniformly against the `2·` lift.
The defect is the lynchpin of the sum-term arithmetic; removing it (via W, which is genuinely unit)
forces the path to time `2t`, breaking the shared-`t` derivative combination (item 4d).

This is exactly the plan's Q-CORE conclusion ("v_Z reaches ratio core arith"), now machine-confirmed
on the consumer's actual `deBruijn_identity_v2` call site.

---

## Blast radius of wrapper-W (route c, measured)

`rg -c "Z_X ω + Z_Y ω|Z_X + Z_Y|Z_Y ω + Z_X ω"` (sum-noise path occurrences):

| file | count |
|---|---|
| `InformationTheory/Shannon/EPIStamToBridge.lean` | 39 |
| `InformationTheory/Shannon/EPICase1RatioLimit.lean` | 30 |
| `InformationTheory/Shannon/EPIL3Integration.lean` | 24 |
| `InformationTheory/Shannon/EPICase1SumProducer.lean` | 4 |

The antitone target itself, `csiszarLogRatioGap X Y Z_X Z_Y P t` (`EPIL3Integration.lean:1380`),
**hardcodes the sum noise as `Z_X+Z_Y`** (literally the sum of the two individual noises) with a
**single shared time `t`** across the sum path AND the X/Y paths:
```
log eP(X+Y+√t·(Z_X+Z_Y)) − log (eP(X+√t·Z_X) + eP(Y+√t·Z_Y))
```
W-substitution would require re-expressing the sum term with a *different* time (`2t`) than the X/Y
terms (`t`) — which `csiszarLogRatioGap`'s single-`t` signature cannot express. So route c is NOT a
mechanical noise rename; it requires restructuring the antitone object's time variable, which
propagates through ~93 sum-path sites across the 3 consumer files + the endpoint lemmas
(`csiszarLogRatioGap_at_zero` / `_at_one_eq_zero`) and the saturation pillar
(`csiszarLogRatioGap_tendsto_zero_atTop`). **Not a tractable wrapper rename.**

---

## What genuine closure actually requires (route b-2, the surviving path)

The honest closure is **general-variance de Bruijn identity surgery**, NOT W-substitution:

1. Open `IsRegularDeBruijnHypV2.Z_law` to `gaussianReal 0 v_Z` (+ a `v_Z` field), and open
   `density_t_eq`'s carrier to `⟨t·v_Z, _⟩` (`FisherInfoV2DeBruijn.lean:210, 260-261`).
2. Generalize `debruijnIdentityV2_holds_assembled_entropy_eq` / `_fisher_match`
   (`FisherInfoV2DeBruijnAssembly.lean:3437, 3485`) to call
   `pPath_eq_convDensityAdd ... v_Z ...` (already general-variance, `FisherInfoV2DeBruijnPerTime.lean:215`)
   so the de Bruijn derivative becomes `(v_Z/2)·J(convDensityAdd pX g_{t·v_Z})`.
3. Thread the chain factor `v_Z` into the consumer's ratio arithmetic
   (`csiszarLogRatioGap_hasDerivAt` `:740-749` + `csiszarLogRatioGap_deriv_le_zero` weights). The
   sum term gets factor `v_sum = 2`, X/Y get `v = 1`; the ratio-Stam `α²≤α` weights must be
   re-derived with the `2·J_sum` numerator. (This is the carrier drift the plan flagged; closing
   it genuinely means proving the ratio bound WITH the factor-2 sum term, not cancelling it.)
4. Blast radius of structure surgery: `IsRegularDeBruijnHypV2` consumer = 13 files / 50+ sites
   (`EPICase1SumProducer.lean:18` header, measured 2026-06-05). X/Y instances补完 `v_Z := 1`.

This is a **multi-file structural wave**, out of scope for a probe. Slug stays
`@audit:closed-by-successor(epi-case1-debruijn-genvar-struct-plan)` but the **route the plan
recommends (B-τ) is refuted**; the plan should be revised to route b-2 (general-variance surgery)
or the defect park maintained until that wave is scheduled.

---

## Inventory (GS-0, verbatim, mathlib-inventory format)

### Mathlib — W-law chain (all genuine, in `Mathlib/Probability/Distributions/Gaussian/Real.lean`)

- `ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun` (Real.lean:624)
  ```
  {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ}
    (hXY : IndepFun X Y P) (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) :
    P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)
  ```
  No `[...]` instance prerequisites.

- `ProbabilityTheory.gaussianReal_map_div_const` (Real.lean:334)
  ```
  (c : ℝ) : (gaussianReal μ v).map (· / c) = gaussianReal (μ / c) (v / .mk (c ^ 2) (sq_nonneg _))
  ```
  Implicit `{μ : ℝ} {v : ℝ≥0}` from section. No instance brackets.

- `ProbabilityTheory.gaussianReal_map_const_mul` (Real.lean:298) — sibling, `(c * ·)` form.
- `MeasureTheory.Measure.map_map` (Mathlib) — `P.map (g ∘ f) = (P.map f).map g` for measurable `f`, `g`;
  used as `Measure.map_map (·/√2 measurable) (hZX.add hZY)` with the `(fun x => x/√2) ∘ (Z_X+Z_Y)` reduction `rfl`.
- `Real.sq_sqrt` : `0 ≤ a → √a ^ 2 = a` — for `(√2)² = 2`.

### In-tree — path-id (PB-2), `@audit:ok`, `EPICase1RatioLimit.lean`

- `gaussianConvolution_rescale_eq` (:1766)
  ```
  {α : Type*} (X Z : α → ℝ) (v : ℝ) (hv : 0 < v) (t : ℝ) (ht : 0 ≤ t) :
    FisherInfoV2.gaussianConvolution X (fun ω => Z ω / Real.sqrt v) (t * v)
      = FisherInfoV2.gaussianConvolution X Z t
  ```
  i.e. `X + √(t·v)·(Z/√v) = X + √t·Z` pointwise. For W (`v:=2`):
  `gaussianConvolution X W (t*2) = gaussianConvolution X Z t` — confirms the reparam direction,
  BUT note it identifies the *carrier-2t W-path* with the *carrier-t Z-path*: the very desync of item 4d.
- `map_gaussianConvolution_rescale_eq` (:1779) — `P.map` form of the above, `@audit:ok`.

### In-tree — de Bruijn V2 (carrier mechanism)

- `IsRegularDeBruijnHypV2.Z_law` (`FisherInfoV2DeBruijn.lean:210`) : `P.map Z = gaussianReal 0 1` — **unit hardcode**.
- `IsRegularDeBruijnHypV2.density_t_eq` (:260-261) : `density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x` — **carrier `t` hardcode**.
- `debruijnIdentityV2_holds_assembled` (`FisherInfoV2DeBruijnAssembly.lean:3543`) — consumes `h_reg.Z_law` (unit) via `_entropy_eq` + `_fisher_match`.
- `debruijnIdentityV2_holds_assembled_entropy_eq` (:3437) — `hZ_law : P.map Z = gaussianReal 0 1` hardcoded arg; internal `pPath_eq_convDensityAdd ... (1:ℝ≥0) one_pos hZ_law` pins carrier `s·1 = s`.
- `pPath_eq_convDensityAdd` (`FisherInfoV2DeBruijnPerTime.lean:215`) — **general v_Z**: `(v_Z : ℝ≥0)` arg, carrier `s·v_Z`. The hook for route b-2.
- `deBruijn_identity_v2` (`FisherInfoV2DeBruijnGenuine.lean:51`) — consumer, returns `(1/2)·J(h_reg.density_t)`.

### In-tree — consumer chain (where v_Z reaches arith)

- `csiszarLogRatioGap` (`EPIL3Integration.lean:1380`) — antitone target, sum noise `Z_X+Z_Y` hardcoded, single shared `t`.
- `csiszarLogRatioGap_hasDerivAt` (`EPIStamToBridge.lean:699`) — calls `deBruijn_identity_v2 (X+Y) (Z_X+Z_Y) ...` (:747) with `h_reg_sum.reg_at` (carrying the false unit `Z_law`).
- `csiszarLogRatioGap_deriv_le_zero` (`EPIStamToBridge.lean:895`) — ratio-Stam; `h_conv_id` (:919-922) ties sum `density_t` to `convDensityAdd (X-dens) (Y-dens)`.
- `csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1085`) — assembles, consumes `h_reg_sum` + `h_endpt_sum`.
- `entropyPower_add_ge_case1_of_regular` (`EPICase1RatioLimit.lean:1343`) / `_of_methodX` (:1498) — wrappers; `h_pos_stam` (containing `h_conv_id`) is an **open hypothesis** (de Bruijn group, NOT discharged).
- Sum producer `isDeBruijnRegularityHyp_sum_of_methodX_unitnoise` (`EPICase1SumProducer.lean:88`) — `Z_law` field `@audit:defect(false-statement)` (:166); other fields genuine; `integrable_deriv` t-measurability park (:210).

---

## Notes for next wave

- The plan's route B-τ recommendation is **refuted by item 4d**. Update the plan to route b-2
  (general-variance structure surgery) as the surviving honest closure, or keep the defect park.
- Route b-2's hard math content is **re-deriving the ratio-Stam bound with the factor-2 sum term**
  (`2·J_sum` vs harmonic of `J_X, J_Y`), not just a mechanical v_Z thread. This is the genuine
  EPI-Stam content the defect currently hides — it should be scoped as its own analytic task, not
  assumed to fall out of plumbing.
- `pPath_eq_convDensityAdd` (general v_Z) being already in-tree is the one real asset for b-2.
- grep miss: `gaussianConvolution_rescale_eq` is at `:1766` (plan said `~:1769`); off by 3.

---

## GS-A0 probe (2026-06-06) — `J_sum` v_Z-invariance via `fisherInfoOfMeasureV2` measure-ignore

> Scope: the advisor's "first move" — machine-check whether the de Bruijn assembly,
> when v_Z-generalized, keeps the sum-term `J_sum` (Fisher value) **invariant** in v_Z
> via the `fisherInfoOfMeasureV2` measure-ignore at `FisherInfoV2DeBruijn.lean:81`.
> Probe file `InformationTheory/Shannon/ZZProbeGSA0.lean` (deleted post-probe),
> `lake env lean` clean (only 3 intended PROBE-FAIL `sorry`s). go/no-go only; no impl.

### VERDICT: **NO-GO** — the `fisherInfoOfMeasureV2` measure-ignore does NOT decouple `J_sum` from v_Z

The advisor's hypothesized rescue ("`J_sum` = `fisherInfoOfMeasureV2 (Z_law) density_t` and
`fisherInfoOfMeasureV2` ignores its measure arg, so `J_sum` is v_Z-independent") is **refuted
at the type level**. The measure-ignore is real (`rfl`-confirmed, claim a ✅) but **irrelevant
to the desync**: the de Bruijn derivative value and the ratio core both consume
`fisherInfoOfDensityReal` applied to the **density function `density_t` directly** — NOT
`fisherInfoOfMeasureV2 μ density_t`. The density function is carrier-pinned (`density_t_eq`,
carrier `t·v_Z`), so v_Z reaches `J_sum` through the **second (function) argument**, which the
`:81` measure-ignore does not touch. This **independently re-confirms** the prior item-4d VERDICT
(NO-GO for the wrapper-W/B-τ route) from the advisor's new angle, and additionally shows the
b-2 surgery's spurious-factor-2 desync is **machine-real**, not avoidable by the measure-ignore.

→ **Recommendation: maintain the `Z_law` defect park** (unchanged from the prior verdict). The
genuine-closure analytic core remains **factor-2 ratio-Stam re-derivation** (GS-A3), and this
probe sharpens *where* the desync lives: NOT in the ratio core (`csiszarLogRatioGap_deriv_le_zero`,
opaque density-Fisher values, v_Z-agnostic re-usable) but one level up in
`csiszarLogRatioGap_hasDerivAt`'s `hN_sum` entropy-power lift, where the `(1/2)·J` cancellation
against `2·` is hardcoded (`EPIStamToBridge.lean:790-803`).

### Machine-verified probe results (6 `example`s, type-level)

**PROBE 0 — de Bruijn derivative value dependence: type-checks ✅ (sets up the refutation)**
`deBruijn_identity_v2 X Z … h_reg` returns
`HasDerivAt (… differentialEntropy …) ((1/2) * fisherInfoOfDensityReal h_reg.density_t) t`
(`FisherInfoV2DeBruijnGenuine.lean:51`, verbatim). The Fisher value is
`fisherInfoOfDensityReal h_reg.density_t` — `fisherInfoOfDensityReal` applied to the **`ℝ → ℝ`
density function `density_t` DIRECTLY**, NOT via `fisherInfoOfMeasureV2 μ density_t`. So the
measure-keyed wrapper's `:81` ignore is **not on the path** of the derivative value.

**PROBE 1a — `fisherInfoOfMeasureV2 μ f = fisherInfoOfDensity f`: `rfl` ✅ (claim a verbatim)**
`example (μ : Measure ℝ) (f : ℝ → ℝ) : fisherInfoOfMeasureV2 μ f = fisherInfoOfDensity f := rfl`
type-checks. The measure-ignore at `FisherInfoV2DeBruijn.lean:81` is genuine. **But it ignores the
FIRST (measure) argument; the density witness `f` (2nd arg) is fully load-bearing.**

**PROBE 1b — `gaussianConvolution_rescale_eq` is PATH-function, not DENSITY-function ✅**
`EPICase1RatioLimit.gaussianConvolution_rescale_eq X Z v hv t ht` type-checks with conclusion
`gaussianConvolution X (Z/√v) (t·v) = gaussianConvolution X Z t` (path `X+√(t·v)·(Z/√v) = X+√t·Z`).
This is the *path random variable* `X+√t·Z`, NOT the *density* `convDensityAdd pX g_{carrier}` that
`fisherInfoOfDensityReal` consumes. The rescale never touches the density argument.

**PROBE 1c (claim 1 KEY) — carrier rescale does NOT reach the Fisher value level ⛔**
```
convDensityAdd pX (gaussianPDFReal 0 ⟨t, _⟩) = convDensityAdd pX (gaussianPDFReal 0 ⟨t*2, _⟩)
```
**`rfl` FAILS** (machine output: "carrier-t density is not definitionally equal to carrier-2t
density"). The general-v_Z density (v_Z=2) is `convDensityAdd pX g_{2t}` (carrier 2t, from
`pPath_eq_convDensityAdd … v_Z …`, `FisherInfoV2DeBruijnPerTime.lean:215` carrier `s·v_Z`), which is
**a different function** from the unit-carrier `convDensityAdd pX g_t`. `gaussianConvolution_rescale_eq`
(path-level) cannot bridge them — it identifies the carrier-2t *W-path* with the carrier-t *Z-path*
(the very desync of item 4d), not the two *densities*.

**PROBE 2 (claim 2) — `J_sum` is NOT v_Z-invariant ⛔**
```
fisherInfoOfDensityReal (convDensityAdd pX g_t) = fisherInfoOfDensityReal (convDensityAdd pX g_{2t})
```
left as `sorry` — **not closable by `rfl`/`simp`** (the two arguments are the PROBE-1c non-defeq
densities; the Fisher value of a Gaussian-convolved density genuinely depends on the carrier,
`J(pX∗g_t) ≤ 1/t` scales with carrier per `gaussianConv_fisher_le_inv_var`). `J_sum` v_Z-invariance
is **machine-refuted**.

**PROBE 3a — unit-carrier cancellation arithmetic: `ring` ✅ (the current mechanism)**
`eP * J_sum = eP * (2 * ((1/2) * J_sum))` closes by `ring`. This is the current
`csiszarLogRatioGap_hasDerivAt` `hN_sum` lift (`EPIStamToBridge.lean:794-801`): de Bruijn gives
`(1/2)·J_sum`, the entropy-power chain rule multiplies by `2·`, the `(1/2)` cancels → `eP·J_sum`.

**PROBE 3b (the make-or-break) — general-variance v_sum=2 breaks the cancellation ⛔**
`eP * J_sum = eP * (2 * ((2/2) * J_sum))`: **`ring` FAILS**, reducing the goal to
`eP * J_sum = eP * J_sum * 2` (machine output verbatim) — false unless `J_sum = 0`. With
general-variance, the de Bruijn derivative becomes `(v_sum/2)·J_sum = (2/2)·J_sum = J_sum`, so the
`2·` lift yields `eP · 2·J_sum` — a **spurious factor 2**. This is the item-4d desync, now confirmed
as a concrete `ring`-level contradiction in the consumer's hardcoded `(1/2)` arithmetic.

### Answers to the brief's completion questions

(a) **GO/NO-GO**: **NO-GO** (J_sum is v_Z-dependent; measure-ignore does not save it).
(b) **carrier rescale → Fisher value level**: **NO** (PROBE 1c `rfl` fails; rescale is path-level only,
    carrier-t and carrier-2t densities are not defeq, so `fisherInfoOfDensityReal` differs).
(c) **`J_sum` v_Z-invariant**: **NO, machine-refuted** (PROBE 2 + PROBE 3b: the v_Z=2 carrier produces
    a spurious factor 2 that `ring` rejects as `eP·J_sum = eP·J_sum·2`).
(d) **ratio core unchanged re-use**: **PARTIALLY YES but misleading** —
    `csiszarLogRatioGap_deriv_le_zero` (`:895`) takes `(h_reg_*.reg_at t ht).density_t` Fisher values
    as **opaque** function-Fisher-values and does NOT reference v_Z, so the *core itself* is reusable.
    BUT the desync is NOT in the ratio core; it is one level **up** in
    `csiszarLogRatioGap_hasDerivAt`'s `hN_sum` (`:790-803`), where the de Bruijn value `(1/2)·J_sum`
    is fed into an entropy-power lift whose `(1/2)`-cancellation is hardcoded. Re-using the ratio core
    unchanged is exactly what FAILS, because its inputs (the `hN_sum`-lifted derivative) carry the
    spurious factor 2.
(e) **residual障害の具体と sizing** (NO-GO): the genuine closure障害 is unchanged from item 4d =
    **factor-2 ratio-Stam re-derivation** (GS-A3 load-bearing analytic core). The probe adds: the
    surgery must rewrite `csiszarLogRatioGap_hasDerivAt`'s `hN_sum`/`hN_X`/`hN_Y` lifts
    (`EPIStamToBridge.lean:766-803`) to carry per-term `v_i` factors (sum: `(v_sum/2)·J`, X/Y:
    `(1/2)·J`), AND re-derive the harmonic-Stam `α²≤α` weights in `csiszar_ratio_deriv_le_zero_arith`
    with the factor-2 sum numerator. This is the genuine EPI math the defect hides — NOT plumbing.
(f) **GS-A1'〜A4' 機械的補完の感触** (13-file v_Z:=1): the structural plumbing (v_Z field +
    `density_t_eq` carrier `t·v_Z` general-ization, `_entropy_eq`/`_fisher_match` via
    `pPath_eq_convDensityAdd` general v_Z) IS mechanical — `pPath_eq_convDensityAdd` already takes
    `(v_Z : ℝ≥0)` (`FisherInfoV2DeBruijnPerTime.lean:215`), and X/Y instances `v_Z := 1` recover the
    current carriers definitionally (`s·1 = s` simp). The NON-mechanical part is concentrated in the
    **two `EPIStamToBridge.lean` consumer lemmas** (`csiszarLogRatioGap_hasDerivAt` `hN_sum` lift +
    `csiszarLogRatioGap_deriv_le_zero` arith weights), which carry load-bearing `(1/2)`/`α²≤α`
    arithmetic that the v_Z=2 sum term breaks. So GS-A1/A2 plumbing ≈ mechanical, but GS-A3 (the 2
    consumer lemmas) is the genuine analytic surgery and the actual sizing risk. **Confirms the
    plan's risk order**: gate GS-A3 tractability (`proof-pivot-advisor` on factor-2 ratio-Stam) BEFORE
    investing in the 13-file plumbing.

### Probe notes (proof-log素材)
- The brief's framing (claim 2: "`fisherInfoOfMeasureV2` measure-ignore ⟹ `J_sum` v_Z-invariant")
  conflates the measure-keyed wrapper `fisherInfoOfMeasureV2` (`:81`, ignores 1st arg) with the
  density-direct `fisherInfoOfDensityReal` actually used by the de Bruijn derivative and ratio core.
  The measure-ignore is real but on the wrong argument. This is the single load-bearing distinction.
- `rg` miss: no separate `J_sum`-as-`fisherInfoOfMeasureV2` call exists in the consumer chain; all
  three Fisher values (`J_X`/`J_Y`/`J_sum`) are `fisherInfoOfDensityReal ((h_reg_*.reg_at t ht).density_t)`
  applied to the density function directly (`EPIStamToBridge.lean:903-908`, `:938-943`).
- The docstring at `EPIStamToBridge.lean:892-893` ("the three Fisher `rfl` identifications hold since
  `fisherInfoOfMeasureV2` ignores its measure argument") refers to a deleted D3 difference-gap lemma
  context, NOT to `csiszarLogRatioGap_deriv_le_zero`'s actual `fisherInfoOfDensityReal` values — a
  possible source of the brief's misread.

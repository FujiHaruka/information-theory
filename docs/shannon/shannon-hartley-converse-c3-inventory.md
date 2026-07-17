# Shannon-Hartley converse C3 — asset inventory (operational parallel-Gaussian converse)

> Parent plan: [`shannon-hartley-phase2-spectral-plan.md`](shannon-hartley-phase2-spectral-plan.md) §R4-CONV, row **C3**.
> Scope: the operational converse chain `log M → I(W;Y) → I(S;Y) → mutualInfoOfChannel → ∑ᵢ ½log(1+P'ᵢ/(N₀/2))` for a `ContAwgnCode T W P M`.
> This file is a docs-only inventory. It touches no code and no plan.

## One-line summary

**Of the ~13 API pieces C3 needs, 100% of the mathematical substance already exists in-tree; there is NO genuine Mathlib gap.** Every link is either an existing sorryAx-free lemma (`shannon_converse_single_shot`, `mutualInfo_le_of_markov`, `mutualInfoOfChannel_eq_mutualInfo_prod`, `parallel_per_input_mi_le_sum`, `fano_inequality_measure_theoretic`) or a **direct clone of the discrete AWGN converse's wiring** (`awgnConverseJoint` / `awgn_converse_single_shot_call` / `awgnConverseMarkov_holds`). C3 is pure project-internal plumbing: **~7 self-build items, ~180–280 lines total**, with **the MI-finiteness discharge as the single highest-risk piece** (the discrete AWGN needed a ~900-line file for its analog, but the parallel family has already built the integrability machinery it reuses).

**Retreat line: does NOT trigger.** No new wall. If C3 balloons, the sanctioned exit is `sorry + @residual(plan:shannon-hartley-phase2-spectral-plan)` per the parent plan's honesty constraints — no wall slug is warranted.

**Most dangerous finding**: `map_pi_eq_stdGaussian` (the C2 rotation bridge) is stated **only for `gaussianReal 0 1`** (zero mean, unit variance). `ContAwgnCode.errorProbAt` uses `Measure.pi (gaussianReal (observation m i) (N₀/2).toNNReal)` — **nonzero mean and variance `N₀/2 ≠ 1`**. The rotation invariance applies to the *centered noise* `gaussianReal 0 (N₀/2)`, and reaching `stdGaussian` needs an affine pre/post-composition (`gaussianReal_map_const_mul` per coordinate). Assuming a direct application would be a mid-proof pivot.

---

## C3 final form (the shape the plan asks for)

The C3 obligation, restated from §R4-CONV row C3:

```
log M ≤ ∑ᵢ ½·log(1 + νᵢ·Qᵢ/(N₀/2)) + binEntropy(Pe) + Pe·log(M − 1)
```

The νᵢ (Gram / prolate eigenvalues) enter downstream (C2 rotation + C4 folding). The **C3 core itself produces the equal-noise form** (see reduction sketch), with the gains introduced later:

```lean
-- pseudo-Lean, C3 core, for c : ContAwgnCode T W P M, average error ≤ ε, N₀ > 0:
let joint : Measure (Fin M × (Fin c.k → ℝ)) :=      -- clone of awgnConverseJoint
  (M : ℝ≥0∞)⁻¹ • ∑ m, (Measure.dirac m).prod
      (Measure.pi (fun i => gaussianReal (c.observation m i) (N₀/2).toNNReal))
-- 1. Fano+DPI single-shot   (shannon_converse_single_shot, W = Prod.fst, Y = Prod.snd)
have h1 : log M ≤ (mutualInfo joint fst snd).toReal + binEntropy Pe + Pe·log (M−1)
-- 2. DPI up to the codeword (mutualInfo_le_of_markov, W → S=observation(W) → Y)
have h2 : mutualInfo joint fst snd ≤ mutualInfo joint (observation∘fst) snd
-- 3. RV-form ↔ channel-form (mutualInfoOfChannel_eq_mutualInfo_prod, joint = p_S ⊗ₘ W)
have h3 : (mutualInfo joint (observation∘fst) snd) = mutualInfoOfChannel p_S W
-- 4. parallel MI bound      (parallel_per_input_mi_le_sum, N i ≡ (N₀/2).toNNReal)
have h4 : (mutualInfoOfChannel p_S W).toReal ≤ ∑ᵢ ½·log (1 + P'ᵢ/(N₀/2))
-- assemble ⇒ log M ≤ ∑ᵢ ½·log(1 + P'ᵢ/(N₀/2)) + Fano
```

---

## Item 1 — Fano's inequality (in-project)

The single-shot converse (item 3) invokes measure-theoretic Fano. Both are in-tree.

| concept | asset | file:line | status | C3 handling |
|---|---|---|---|---|
| Fano (measure-theoretic, deterministic decoder) | `fano_inequality_measure_theoretic` | `InformationTheory/Fano/Measure.lean:269` | EXISTS `@[entry_point]`, sorryAx-free | consumed transitively via `shannon_converse_single_shot` — not called directly in C3 |
| decoding error probability | `errorProb` | `InformationTheory/Fano/Measure.lean:88` | EXISTS | the `Pe` term; `errorProb joint fst snd c.decoder` must be identified with `(c.averageError N₀).toReal` |
| measure-theoretic conditional entropy | `condEntropy` | `InformationTheory/Fano/Measure.lean:83` | EXISTS | internal to Fano |

Verbatim (message alphabet `X` context = `Fano/Measure.lean:70-73`):
```lean
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
variable {Y : Type*} [MeasurableSpace Y]

omit [DecidableEq X] in
@[entry_point]
theorem fano_inequality_measure_theoretic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hdec : Measurable decoder)
    (hcard : 2 ≤ Fintype.card X) :
    condEntropy μ Xs Yo ≤
      Real.binEntropy (errorProb μ Xs Yo decoder)
        + errorProb μ Xs Yo decoder * Real.log ((Fintype.card X : ℝ) - 1)

def errorProb (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X) : ℝ :=
  μ.real {ω | Xs ω ≠ decoder (Yo ω)}
```
Message alphabet in C3 is `Fin M`, which supplies `[Fintype] [DecidableEq] [Nonempty] [MeasurableSingletonClass]` automatically (finite). No extra typeclass leaks.

---

## Item 2 — Data processing inequality (in-project)

Two DPI forms exist; C3 uses both (postprocess inside the single-shot, Markov to climb from the message to the codeword).

| concept | asset | file:line | status | C3 handling |
|---|---|---|---|---|
| DPI (postprocess) `I(X;f(Y)) ≤ I(X;Y)` | `mutualInfo_le_of_postprocess` | `InformationTheory/Shannon/DPI.lean:123` | EXISTS `@[entry_point]`, sorryAx-free | used *inside* `shannon_converse_single_shot` (decoder postprocessing); not called directly |
| DPI (Markov) `I(X;Y) ≤ I(Z;Y)` under `X→Z→Y` | `mutualInfo_le_of_markov` | `InformationTheory/Shannon/CondMutualInfo.lean:356` | EXISTS, sorryAx-free | **C3 step 2**: climb `I(W;Y) ≤ I(S;Y)`, `S = observation ∘ W` |

Verbatim (`DPI.lean:121-127`; ambient `{Ω X Y Z}` all `[MeasurableSpace]`):
```lean
@[entry_point]
theorem mutualInfo_le_of_postprocess
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo)
    {f : Y → Z} (hf : Measurable f) :
    mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo
```
Verbatim (`CondMutualInfo.lean:356-363`):
```lean
theorem mutualInfo_le_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo
```
**Typeclass note for C3**: `mutualInfo_le_of_markov` needs `[StandardBorelSpace X]` on the *source* `X = Fin M` (auto, finite) and `[StandardBorelSpace Y]` on `Y = Fin c.k → ℝ`. The latter holds via `StandardBorelSpace.pi_countable` (`Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:151`: `Fin k` countable × `ℝ` standard Borel ⇒ `Fin k → ℝ` standard Borel). No `X = Fin c.k → ℝ` StandardBorel obligation is missed. **`IsMarkovChain joint W (observation∘W) Y` is the one nontrivial hypothesis** — SELF-BUILD (see item 8; clone of `awgnConverseMarkov_holds`).

---

## Item 3 — `shannon_converse_single_shot` (in-project) — the Fano+DPI bundle

| concept | asset | file:line | status |
|---|---|---|---|
| single-shot converse (uniform message) | `shannon_converse_single_shot` | `InformationTheory/Shannon/Converse.lean:70` | EXISTS, sorryAx-free |
| single-shot converse (Markov encoder) | `shannon_converse_single_shot_markov_encoder` | `InformationTheory/Shannon/Converse.lean:128` | EXISTS, sorryAx-free |

Verbatim (`Converse.lean:63-83`; `{M}` = `[Fintype][DecidableEq][Nonempty][MeasurableSpace][MeasurableSingletonClass]`, `{Y}` = `[MeasurableSpace]`):
```lean
omit [DecidableEq M] in
theorem shannon_converse_single_shot
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Yo : Ω → Y) (decoder : Y → M)
    (hMsg : Measurable Msg) (hYo : Measurable Yo) (hdecoder : Measurable decoder)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : mutualInfo μ Msg Yo ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (mutualInfo μ Msg Yo).toReal +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg Yo decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg Yo decoder *
          Real.log ((Fintype.card M : ℝ) - 1)
```
**Assessment**: this applies *directly* to the ContAwgnCode channel with `μ := contAwgnConverseJoint`, `Msg := Prod.fst : Fin M × (Fin k → ℝ) → Fin M`, `Yo := Prod.snd`, `decoder := c.decoder`. It is exactly what `awgn_converse_single_shot_call` (`AWGN/ConverseMutualInfoFiniteness.lean:932`) uses for the discrete AWGN block code — that call is the line-by-line template for C3's step 1. The `hMI_finite : mutualInfo μ Msg Yo ≠ ∞` slot is the load-bearing precondition and must be discharged (see item 6 / verdict).

The Markov-encoder form is an *alternative* to doing step 2 separately: it folds the `W → S → Y` Markov DPI into the converse, yielding `log M ≤ (mutualInfo μ (encoder∘Msg) Yo).toReal + Fano` directly. It requires `[StandardBorelSpace X]` (`X = Fin k → ℝ`, auto) and `IsMarkovChain μ Msg (encoder∘Msg) Yo`.

---

## Item 4 — `mutualInfoOfChannel` and the RV↔channel bridge

| concept | asset | file:line | status | C3 handling |
|---|---|---|---|---|
| channel MI (KL form) | `mutualInfoOfChannel` | `InformationTheory/Shannon/ChannelCoding/Basic.lean:81` | EXISTS | the object `parallel_per_input_mi_le_sum` bounds |
| RV↔channel MI bridge | `mutualInfoOfChannel_eq_mutualInfo_prod` | `InformationTheory/Shannon/ChannelCoding/Basic.lean:92` | EXISTS, sorryAx-free | **C3 step 3**: `I(S;Y) = mutualInfoOfChannel p_S W` |
| output distribution | `outputDistribution` | `InformationTheory/Shannon/ChannelCoding/Basic.lean:68` | EXISTS | internal to the bound |
| joint distribution | `jointDistribution` (`p ⊗ₘ W`) | `InformationTheory/Shannon/ChannelCoding/Basic.lean:51` | EXISTS | the `p_S ⊗ₘ W` identification |
| RV-form mutual information | `mutualInfo` | `InformationTheory/Shannon/MutualInfo.lean:36` | EXISTS | `= klDiv (μ.map (X,Y)) ((μ.map X).prod (μ.map Y))` |

Verbatim (`ChannelCoding/Basic.lean:41,81,92-97`; `{α β}` = `[MeasurableSpace]`, `Channel α β := Kernel α β`):
```lean
noncomputable def mutualInfoOfChannel (p : Measure α) (W : Channel α β) : ℝ≥0∞ :=
  klDiv (jointDistribution p W) (p.prod (outputDistribution p W))

theorem mutualInfoOfChannel_eq_mutualInfo_prod
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    mutualInfoOfChannel p W
      = InformationTheory.Shannon.mutualInfo (jointDistribution p W)
          Prod.fst Prod.snd
```
Verbatim (`MutualInfo.lean:30-39`; `{Ω X Y}` all `[MeasurableSpace]`):
```lean
noncomputable def mutualInfo
    (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ :=
  klDiv (μ.map (fun ω ↦ (Xs ω, Yo ω)))
        ((μ.map Xs).prod (μ.map Yo))
```
**Is there a ready-made "`log M ≤ mutualInfoOfChannel + Fano` for a general discrete-input channel"?** No — the closest is `channel_coding_converse_iid` (`ChannelCoding/Converse.lean:41`), but it assumes the channel is **i.i.d. memoryless** (`h_iid_joint`, `h_copy`, giving `log M ≤ n·I(X₀;Y₀) + Fano`). The parallel Gaussian channel has **non-identical** coordinates (different gains νᵢ), so that lemma does not apply. There is no packaged non-iid/parallel operational converse; that is exactly C3's self-build. The reusable packaging that *does* apply is the RV-form `shannon_converse_single_shot` (item 3) + the RV↔channel bridge (this item), assembled by hand as `awgn_converse_single_shot_call` does.

---

## Item 5 — `parallel_per_input_mi_le_sum` and its definitions (the in-tree core)

| concept | asset | file:line | status | C3 handling |
|---|---|---|---|---|
| **per-input parallel MI bound** | `parallel_per_input_mi_le_sum` | `InformationTheory/Shannon/ParallelGaussian/Converse/MixtureDensity.lean:901` | EXISTS, sorryAx-free, **0 current consumers** (`dep_consumers.sh` returns empty) | **C3 step 4 = the core**; C3 is the intended first consumer |
| parallel channel kernel | `parallelGaussianChannel` | `InformationTheory/Shannon/ParallelGaussian/Basic.lean:73` | EXISTS | its fibre = `Measure.pi (gaussianReal (x i) (N i))` = errorProbAt fibre |
| per-coord AWGN measurability | `IsParallelAwgnChannelMeasurable` | `ParallelGaussian/Basic.lean:61` | EXISTS (a `Prop` def) | discharge with `AWGN.isAwgnChannelMeasurable` per coord |
| parallel kernel measurability | `IsParallelGaussianKernelMeasurable` | `ParallelGaussian/Basic.lean:66` | EXISTS (a `Prop` def) | discharge (measurability of the product-Gaussian map) |
| power constraint set | `parallelGaussianPowerConstraintSet` | `ParallelGaussian/Basic.lean:130` | EXISTS | membership of `p_S` is a SELF-BUILD obligation |
| MI decomposition value | `parallel_mi_decomp_value` | `ParallelGaussian/Converse/MixtureDensity.lean:835` | EXISTS, sorryAx-free | internal to the bound |
| Markov-kernel instance | `parallelGaussianChannel.instIsMarkovKernel` | `ParallelGaussian/Basic.lean:89` | EXISTS | supplies `[IsMarkovKernel W]` for the bridge |

Verbatim (`MixtureDensity.lean:901-909`):
```lean
theorem parallel_per_input_mi_le_sum {n : ℕ}
    (P : ℝ) (hP : 0 ≤ P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (p : Measure (Fin n → ℝ)) [IsProbabilityMeasure p]
    (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    ∃ P' : Fin n → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ i : Fin n, P' i ≤ P) ∧
      (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
        ≤ ∑ i : Fin n, (1/2) * Real.log (1 + P' i / (N i : ℝ))
```
Verbatim (`ParallelGaussian/Basic.lean:61-78,130-132`):
```lean
def IsParallelAwgnChannelMeasurable {n : ℕ} (N : Fin n → ℝ≥0) : Prop :=
  ∀ i, InformationTheory.Shannon.AWGN.IsAwgnChannelMeasurable (N i)

def IsParallelGaussianKernelMeasurable {n : ℕ} (N : Fin n → ℝ≥0) : Prop :=
  Measurable (fun x : Fin n → ℝ ↦ Measure.pi (fun i ↦ gaussianReal (x i) (N i)))

noncomputable def parallelGaussianChannel {n : ℕ}
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    ...Channel (Fin n → ℝ) (Fin n → ℝ) where
  toFun x := Measure.pi (fun i ↦ gaussianReal (x i) (N i))
  measurable' := h_parallel_meas

def parallelGaussianPowerConstraintSet {n : ℕ} (P : ℝ) : Set (Measure (Fin n → ℝ)) :=
  { p : Measure (Fin n → ℝ) | IsProbabilityMeasure p ∧
      ∑ i : Fin n, ∫⁻ x : Fin n → ℝ, ENNReal.ofReal ((x i) ^ 2) ∂p ≤ ENNReal.ofReal P }
```
**Key match**: `parallelGaussianChannel N x` returns `Measure.pi (fun i => gaussianReal (x i) (N i))`. With `N i ≡ (N₀/2).toNNReal` and `x = c.observation m`, this is **definitionally equal** to the `errorProbAt` fibre `Measure.pi (fun i => gaussianReal (c.observation m i) (N₀/2).toNNReal)`. So the reverse bridge (item 6) is a `rfl`/`funext`-level identification, not an approximation.

**Typeclass audit** (does the ContAwgnCode setup satisfy the prereqs?):
- `[IsProbabilityMeasure p]` — `p_S` is a pushforward of a uniform probability measure ⇒ probability. **OK, auto.**
- `hp : p_S ∈ parallelGaussianPowerConstraintSet P₀` — needs `∑ᵢ ∫⁻ (x i)² ∂p_S ≤ ofReal P₀`. Here `∫⁻ (x i)² ∂p_S = (1/M)∑ₘ (observation m i)²`, so the sum is `(1/M)∑ₘ ‖s_m‖²`, and `‖s_m‖² = ∑ᵢ⟨encoder m, φᵢ⟩² ≤ ‖encoder m‖² ≤ T·P` (Bessel via orthonormal `testFn` + `encoder_power`). So membership holds with `P₀ = T·P`. **SELF-BUILD, dischargeable** (~20–40 lines, Bessel + lintegral bookkeeping).
- `hN i : (N i : ℝ) ≠ 0` — `(N₀/2).toNNReal ≠ 0` needs `N₀ > 0`. **OK** (`hN₀` is available in the converse regime).
- `h_meas`, `h_parallel_meas` — measurability `Prop`s; discharge via `AWGN.isAwgnChannelMeasurable` and the product-Gaussian measurability. **SELF-BUILD, routine.**

No StandardBorel / finiteness prereq on `parallel_per_input_mi_le_sum` that the ContAwgnCode setup cannot meet.

---

## Item 6 — Bridge question (CRUCIAL): `errorProbAt` fibre ↔ `parallelGaussianChannel`

`ContAwgnCode.errorProbAt` (`ShannonHartleyOperational.lean:411`) is:
```lean
Measure.pi (fun i : Fin c.k => gaussianReal (c.observation m i) (N₀ / 2).toNNReal)
  {y | c.decoder y ≠ m}
```
This is the memoryless per-observation AWGN law **inlined** (no `Channel`/`Kernel` object, no `IsAwgnChannelMeasurable` hypothesis inside the def).

**Can it be identified with `parallelGaussianChannel`?** Yes, definitionally. Set `N : Fin c.k → ℝ≥0 := fun _ => (N₀/2).toNNReal` (constant). Then
```lean
parallelGaussianChannel N h_meas h_parallel_meas (c.observation m)
  = Measure.pi (fun i => gaussianReal (c.observation m i) ((N₀/2).toNNReal))   -- rfl
```
matches the errorProbAt fibre exactly. This is the **same identity the achievability lift already proved in reverse** — `contAwgnMaxMessages_ge_of_awgnCode` (`ShannonHartleyMain.lean:617`, `herr`) shows `cc.errorProbAt N₀ m = d.toCode.errorProbAt (awgnChannel (N₀/2)) m` by `funext i; rw [hobs]; rfl`. The converse reuses this `funext … rfl` shape.

**Bridge lemma the converse needs = clone of `awgnConverseJoint`** (`AWGN/ConverseMutualInfoFiniteness.lean:63`):
```lean
noncomputable def awgnConverseJoint (h_meas) (c : AwgnCode M n P) :
    Measure (Fin M × (Fin n → ℝ)) :=
  ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) • ∑ m : Fin M,
    (Measure.dirac m).prod
      (Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i)))
```
The ContAwgn analog `contAwgnConverseJoint c N₀ : Measure (Fin M × (Fin c.k → ℝ))` is the same mixture with `Measure.pi (fun i => gaussianReal (c.observation m i) (N₀/2).toNNReal)` in place of the `awgnChannel` product. Then a `contAwgnConverseJoint_map_pair_eq_compProd` clone (of `AWGN/Converse.lean:99`) proves the joint equals `p_S ⊗ₘ (parallelGaussianChannel N₀/2)`, which feeds `mutualInfoOfChannel_eq_mutualInfo_prod`. **SELF-BUILD, ~30–50 lines, direct template.**

**How the gains νᵢ enter** (recorded per brief): the noise is **equal** (`N₀/2`) across all `c.k` coordinates in this channel — `parallel_per_input_mi_le_sum` is invoked with the *constant* `N i ≡ (N₀/2).toNNReal`, producing `∑ᵢ ½log(1 + P'ᵢ/(N₀/2))`. The Gram/prolate eigenvalues νᵢ are **not** in the channel; they enter through the **power-constraint side**:
- The achievable observation vector for a band-limited `f` with `∫ f² ≤ T·P` satisfies `s = A f` where `A` compresses the time-band-limiting operator `P_W` (since `⟨f, φᵢ⟩ = ⟨f, P_W φᵢ⟩` for band-limited `f`). After **C2's rotation to the Gram eigenbasis**, coordinate `i` of `s̃` has energy bounded by `νᵢ·Qᵢ` with `∑Qᵢ ≤ T·P` (the prolate ellipsoid constraint).
- So `P'ᵢ ≤ νᵢ·Qᵢ`, and the gains **fold into the signal power**, turning `∑ᵢ ½log(1 + P'ᵢ/(N₀/2))` into `∑ᵢ ½log(1 + νᵢQᵢ/(N₀/2))`. This folding + water-filling + the `T→∞`, `c→0` limits are **C4**, not C3.
- Consequently **C3's own MI bound is the equal-noise form**; C2 (rotation) supplies the eigenbasis in which the ellipsoid constraint is diagonal, and C4 introduces the νᵢ. C3 must not assume the eigenvalue count (parent plan circularity guard, §循環チェック).

---

## Item 7 — C2 Gauss rotation (Mathlib)

| concept | asset | file:line | status | C3/C2 handling |
|---|---|---|---|---|
| product-Gaussian → stdGaussian | `map_pi_eq_stdGaussian` | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:137` | EXISTS | bridges `Measure.pi (gaussianReal 0 1)` to `stdGaussian` — **only for mean 0, var 1** |
| isometry-invariance of stdGaussian | `stdGaussian_map` | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:128` | EXISTS | orthogonal transform preserves `stdGaussian` |
| basis-independence | `stdGaussian_eq_map_pi_orthonormalBasis` | `Multivariate.lean:146` | EXISTS | rotation to any orthonormal (eigen)basis |
| 1-D scaling | `gaussianReal_map_const_mul` | `Mathlib/Probability/Distributions/Gaussian/Real.lean` | EXISTS | scale variance `1 → N₀/2` per coordinate |
| 1-D translation | `gaussianReal_map_add_const` / `_const_add` | `Mathlib/Probability/Distributions/Gaussian/Real.lean` | EXISTS | mean shift (deterministic) |

Verbatim (`Multivariate.lean`; `namespace ProbabilityTheory`, `variable {ι} [Fintype ι]`; `stdGaussian` context `variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]` then `variable [BorelSpace E]`):
```lean
-- line 128
lemma stdGaussian_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] (f : E ≃ₗᵢ[ℝ] F) :
    haveI := f.finiteDimensional; (stdGaussian E).map f = stdGaussian F

-- line 137
lemma map_pi_eq_stdGaussian :
    (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace ℝ ι)
```
**⚠️ Precondition accident (see one-line summary)**: `map_pi_eq_stdGaussian` fixes `gaussianReal 0 1`. The errorProbAt noise is `gaussianReal (mean) (N₀/2)` with **nonzero mean and variance N₀/2**. C2 must:
1. split `Measure.pi (gaussianReal (obs i) (N₀/2)) = (translate by obs) ∘ (scale by √(N₀/2)) ∘ Measure.pi (gaussianReal 0 1)` — via `gaussianReal_map_const_mul` + `gaussianReal_map_add_const` per coordinate;
2. rotate the *centered, unit-variance* part with `stdGaussian_map` (isotropic invariance) and rotate the mean deterministically;
3. the error probability / MI is invariant because the decoding event and the isotropic noise both rotate consistently.
`stdGaussian_map` needs a **linear isometry equiv** `E ≃ₗᵢ[ℝ] F` (an orthogonal transform), and `[BorelSpace F]` on the target. All present. **C2 is plumbing (~40–80 lines), but NOT a one-line `rw` of `map_pi_eq_stdGaussian`.**

---

## Item 8 — How the achievability lift worked (reverse-informs C3)

`contAwgnMaxMessages_ge_of_awgnCode` (`ShannonHartleyMain.lean:523`, L7, sorryAx-free) bridged discrete `AwgnCode` ↔ `ContAwgnCode` as follows (mechanism, not full proof):

- **Codeword construction** (`ShannonHartleyMain.lean:594`): build `cc : ContAwgnCode T W P M` from the discrete `d : AwgnCode M k …` via the pre-equalizer (`ShannonHartleyPreequalizer.exists_preequalizer`), with `cc.encoder m t := ∑ⱼ bpre m j · h j t`.
- **Observation identity** (`hobs`, `ShannonHartleyMain.lean:612`): `cc.observation m i = d.encoder m i` — the continuous correlation reproduces the discrete codeword coefficient. Proof: `A (bpre m) i = observation`, `hAb`.
- **Error transport** (`herr`, `ShannonHartleyMain.lean:617`): `cc.errorProbAt N₀ m = d.toCode.errorProbAt (awgnChannel (N₀/2).toNNReal …) m`. Proof: `funext i; rw [hobs m i]; rfl` on the two `Measure.pi (gaussianReal …)` fibres, plus `{y | cc.decoder y ≠ m} = d.toCode.errorEvent m` (`rfl`).
- **Average-error transport** (`haverage`, `ShannonHartleyMain.lean:636`): pushes the per-message bound through the uniform mixture.

**Reverse for the converse**: the converse takes an arbitrary `c : ContAwgnCode` and treats `s_m := (c.observation m ·) ∈ ℝ^k` as the effective discrete codeword. The **same `funext … rfl` fibre identity** (herr, run in reverse) shows `c.errorProbAt N₀ m` = the `parallelGaussianChannel (N₀/2)` fibre at input `s_m`. The template files the converse clones are: `awgnConverseJoint` (`ConverseMutualInfoFiniteness.lean:63`), `awgn_converse_single_shot_call` (`ConverseMutualInfoFiniteness.lean:932`), `awgnConverseMarkov_holds` (the Markov discharge, in `AwgnWalls`/`ConverseMutualInfoFiniteness`), and `awgnConverseJoint_map_pair_eq_compProd` (`AWGN/Converse.lean:99`).

---

## C3 reduction sketch (chain-link status)

Given `c : ContAwgnCode T W P M`, `N₀ > 0`, `2 ≤ M`, average error `≤ ε`. Let `k := c.k`, `S := c.observation`, `N := fun _ : Fin k => (N₀/2).toNNReal`, `p_S := law of s_W under uniform W`, `W_chan := parallelGaussianChannel N …`.

| # | link | asset | status |
|---|---|---|---|
| 0 | build `contAwgnConverseJoint c N₀ : Measure (Fin M × (Fin k → ℝ))` + `IsProbabilityMeasure` | clone of `awgnConverseJoint` (`ConverseMutualInfoFiniteness.lean:63`) | **SELF-BUILD** ~20 |
| 1 | `log M ≤ (mutualInfo joint fst snd).toReal + binEntropy Pe + Pe·log(M−1)` | `shannon_converse_single_shot` (`Converse.lean:70`) + uniform/errorProb discharge (clone `awgn_converse_single_shot_call`) | **EXISTS** (lemma) + **SELF-BUILD** ~40 (wiring) |
| 2 | `mutualInfo joint fst snd ≤ mutualInfo joint (S∘fst) snd` | `mutualInfo_le_of_markov` (`CondMutualInfo.lean:356`) + `IsMarkovChain` discharge (clone `awgnConverseMarkov_holds`) | **EXISTS** (lemma) + **SELF-BUILD** ~30–50 (markov) |
| 3 | `mutualInfo joint (S∘fst) snd = mutualInfoOfChannel p_S W_chan` | `mutualInfoOfChannel_eq_mutualInfo_prod` (`ChannelCoding/Basic.lean:92`) + `joint = p_S ⊗ₘ W_chan` (clone `awgnConverseJoint_map_pair_eq_compProd`) | **EXISTS** (lemma) + **SELF-BUILD** ~30 |
| 4 | `(mutualInfoOfChannel p_S W_chan).toReal ≤ ∑ᵢ ½log(1 + P'ᵢ/(N₀/2))`, `∑P'ᵢ ≤ T·P` | `parallel_per_input_mi_le_sum` (`MixtureDensity.lean:901`) + constraint-set membership + measurability discharge | **EXISTS** (lemma) + **SELF-BUILD** ~30–50 (membership + `h_meas`/`h_parallel_meas`) |
| 5 | `mutualInfo joint fst snd ≠ ∞` (feeds link 1's `hMI_finite`) | derive from link 4's finite bound via links 3→2 (`toReal` finite + explicit ℝ≥0∞ upper bound); needs `mutualInfoOfChannel p_S W_chan ≠ ∞` | **SELF-BUILD** ~10–120 (**highest risk**, see verdict) |
| — | **assemble** links 1–4 + `errorProb ↔ averageError` identity ⇒ C3 conclusion | `linarith` chain (clone the `awgn_converse` assembly) | **SELF-BUILD** ~20 |

No link is a **GAP**. Every link is EXISTS (the lemma) or SELF-BUILD (the ContAwgn-specific wiring, all with named in-tree templates).

---

## Verdict

### Is any C3 piece a genuine Mathlib gap?
**No.** The mathematical substance is entirely in-tree and sorryAx-free:
- Fano + DPI + single-shot converse: `Fano/Measure.lean`, `DPI.lean`, `CondMutualInfo.lean`, `Converse.lean`.
- Channel-MI bridge: `ChannelCoding/Basic.lean`.
- The parallel MI bound: `ParallelGaussian/Converse/MixtureDensity.lean:901` (**0 consumers — C3 is its intended first consumer**).
- Gaussian rotation (C2): Mathlib `Multivariate.lean` + `Real.lean` (all present).

Every remaining piece is **project-internal plumbing with a named discrete-AWGN template**. No loogle-0 wall verdict is warranted; per the parent plan, a stuck point exits with `sorry + @residual(plan:shannon-hartley-phase2-spectral-plan)`, and a new slug is created only if a *genuine* Mathlib gap surfaces (none is visible now).

### Self-build line estimates (per link)
- Link 0 (joint measure + prob instance): **~20 lines** — direct `awgnConverseJoint` clone.
- Link 1 wiring (uniform-message + errorProb identity + apply): **~40 lines** — `awgn_converse_single_shot_call` clone.
- Link 2 Markov discharge (`IsMarkovChain joint W S Y`): **~30–50 lines** — `awgnConverseMarkov_holds` clone; the observation map is a deterministic function of the message so the Markov factorization is structural.
- Link 3 (`joint = p_S ⊗ₘ W_chan`): **~30 lines** — `awgnConverseJoint_map_pair_eq_compProd` clone.
- Link 4 (constraint-set membership `p_S ∈ …` via Bessel + `h_meas`/`h_parallel_meas`): **~30–50 lines**.
- Link 5 (**MI-finiteness**): **~10–120 lines, HIGHEST RISK.** `shannon_converse_single_shot` demands `hMI_finite : mutualInfo joint fst snd ≠ ∞` up front, and `.toReal ≤ finite` does *not* imply `≠ ∞`. The discrete AWGN needed a dedicated ~900-line file (`ConverseMutualInfoFiniteness.lean`) for its analog. **Mitigant**: that file's bulk is the per-letter mixture-density construction, which the ParallelGaussian family has **already built** (`MixtureDensity.lean` proves `parallelOutput_joint_logDensity_integrable`, `parallelFibre_logProxy_integrable_compProd`, etc.). MI-finiteness for the parallel joint should follow from those integrability facts + a Mathlib `klDiv_ne_top` criterion in a few dozen lines — but this is the piece most likely to balloon if the reuse is not clean.
- C2 rotation (feeds the exact-constant refinement in C4, not C3's core): **~40–80 lines** — affine split + `stdGaussian_map`, **not** a one-line `map_pi_eq_stdGaussian`.
- Assembly + `errorProb ↔ averageError`: **~20 lines**.

**Total C3 core (links 0–5 + assembly): ~180–280 lines**, dominated by the finiteness risk. C2's ~40–80 lines and C4's water-filling are separate rows in the parent plan.

### Typeclass prereq flags (leaks into the surrounding statement)
- `mutualInfo_le_of_markov` requires `[StandardBorelSpace Y]` for `Y = Fin k → ℝ` — holds via `StandardBorelSpace.pi_countable`; **no missed instance**, but must be `haveI`-supplied if not auto-inferred at the call site.
- `parallel_per_input_mi_le_sum` requires `[IsProbabilityMeasure p_S]` (auto) and `p_S ∈ parallelGaussianPowerConstraintSet` (SELF-BUILD, not a typeclass).
- `mutualInfoOfChannel_eq_mutualInfo_prod` requires `[IsProbabilityMeasure p]` and `[IsMarkovKernel W]` — the latter is `parallelGaussianChannel.instIsMarkovKernel` (`Basic.lean:89`), auto.
- **No `[StandardBorelSpace]` obligation is hidden on the message alphabet or on the channel input `Fin k → ℝ` beyond what the finite/pi instances discharge.**

### Distance to the parent plan's retreat lines
- Parent plan §残債 / §誠実性制約: the only listed retreat exit for C3 is `sorry + @residual(plan:shannon-hartley-phase2-spectral-plan)`; **no wall tag is permitted for C0/C2/C3/C4** unless C3 self-build exposes a genuine Mathlib gap. **This inventory finds no such gap ⇒ the retreat line does not trigger.**
- The parent plan's **circularity guard** (§循環チェック: `2W`/`⌊2WT⌋` may appear only as a *conclusion*, never as a def input, and the converse must *consume* the prolate count, not assume it) is respected by this reduction: C3's MI bound is the equal-noise form and does not mention νᵢ or `2WT`; the eigenvalue count enters via C2/C4 as the conclusion of the Leg E spectral work. **Bundling the converse core into a `*Hypothesis` predicate remains forbidden** (§誠実性制約) — every link above is a real lemma application, not a hypothesis slot.

---

## Starting skeleton

Opening of `InformationTheory/Shannon/ShannonHartley/Converse.lean` (or wherever C3 lands — likely a new `ShannonHartleyConverse.lean` importing `ShannonHartleyOperational` + `ParallelGaussian.Converse.MixtureDensity` + `Shannon.Converse`):

```lean
import InformationTheory.Shannon.ShannonHartleyOperational
import InformationTheory.Shannon.ParallelGaussian.Converse.MixtureDensity
import InformationTheory.Shannon.Converse          -- shannon_converse_single_shot
import InformationTheory.Shannon.CondMutualInfo    -- mutualInfo_le_of_markov
import InformationTheory.Shannon.ChannelCoding.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace InformationTheory.Shannon.ShannonHartley

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ParallelGaussian
open scoped ENNReal NNReal

/-- Canonical joint law of `(W, Y)` for a `ContAwgnCode` under a uniform message and the
inlined per-observation AWGN law — the ContAwgn analog of `AWGN.awgnConverseJoint`. -/
noncomputable def contAwgnConverseJoint {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (N₀ : ℝ) : Measure (Fin M × (Fin c.k → ℝ)) :=
  ((M : ℝ≥0∞)⁻¹) • ∑ m : Fin M,
    (Measure.dirac m).prod
      (Measure.pi (fun i : Fin c.k ↦ gaussianReal (c.observation m i) (N₀ / 2).toNNReal))

/-- **C3: operational parallel-Gaussian converse** (equal-noise form; gains νᵢ enter in C4).
For a `ContAwgnCode` with `2 ≤ M` and average error `Pe`, the log message count is bounded by
the per-coordinate parallel-Gaussian sum plus the Fano terms. -/
theorem contAwgn_operational_converse {T W P N₀ : ℝ} {M : ℕ}
    (hN₀ : 0 < N₀) (hP : 0 ≤ P) (hM : 2 ≤ M)
    (c : ContAwgnCode T W P M)
    (Pe : ℝ) (hPe : Pe = (c.averageError N₀).toReal) :
    ∃ P' : Fin c.k → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ i, P' i ≤ T * P) ∧
      Real.log M ≤ (∑ i : Fin c.k, (1/2) * Real.log (1 + P' i / (N₀ / 2)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  sorry -- @residual(plan:shannon-hartley-phase2-spectral-plan) — C3 links 0–5 + assembly

end InformationTheory.Shannon.ShannonHartley
```
(The exact statement shape — whether the `∃ P'` is exposed or already collapsed to a single `T·P/k`-style bound — is a definition-shaping choice for the implementer; keeping the `∃ P'` mirrors `parallel_per_input_mi_le_sum`'s conclusion form so no re-shaping bridge is needed. The νᵢ gains are introduced by C2/C4 refining the constraint `∑P'ᵢ ≤ T·P` into the eigenbasis ellipsoid.)

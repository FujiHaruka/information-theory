# LZ78 Ziv-inequality entropy layer — Mathlib / project API inventory

> Scope: discharging the two honest hypotheses of
> `lz78_two_sided_optimality_distinct_bdd_free`
> (`InformationTheory/Shannon/LZ78DistinctEncoding.lean:412`):
> `h_achiev : IsLZ78AchievabilityChainHyp` and
> `h_converse : IsLZ78ConverseChainHyp`.
> The SMB / ergodic layer (`blockLogAvg ↔ entropyRate`) is **already genuine**
> (`shannon_mcmillan_breiman`, `SMBAlgoetCover.lean:2840`) and the combinatorial
> phrase-count layer (`card_phraseSet_le_pow`, `IsLZ78PhraseCountAsymptotic`) is
> **already genuine** — not re-investigated here. Remaining gap = Cover–Thomas
> Lemma 13.5.5 + Eq. 13.124 / 13.130 = the **Ziv-inequality entropy layer**.

---

## 一行サマリ

**FEASIBILITY VERDICT: (C) — blocked on a missing primitive.** The two
hypotheses both reduce to the **per-realization Ziv inequality**
`Σⱼ log Pₙ{phraseⱼ} ≥ -c·log c` (Cover–Thomas Lemma 13.5.5), which is an
**entropy chain rule over a *random* number `c` of *random-length* phrases of a
single sample path**. Every existing entropy lemma in the project
(`jointEntropy_chain_rule`, `han_inequality`, `entropy_ge_condEntropy`) is at the
**expectation level** (`entropy μ = ∫ … ∂μ`, disintegration via `condDistrib`),
**not** the per-sample `-(1/n)·log Pₙ{block ω}` level that `blockLogAvg` and `lz n`
inhabit. **There is zero existing bridge between `blockLogAvg` and the parsing
structure** (`rg blockLogAvg` returns only SMB / LZ78-glue files; none touch
`LZ78Parsing`). The missing primitive is a **deterministic / per-path Ziv
inequality** (and its assembly with the SMB-level `blockLogAvg`). Convexity of
`x·log x` and finset-Jensen exist in Mathlib, so the *log-sum* sub-step is
supported; the chain-rule-over-random-parsing sub-step has **no analogue**
anywhere and must be built from scratch as a deterministic combinatorial lemma.

Existing-API coverage of the *sub-steps*: ~40% (log-sum primitive + counting
envelope present; the parsing-level entropy chain rule and the
`blockLogAvg`↔parsing bridge are 0% present). Self-build: 3–4 target lemmas.
**Retreat line: NOT triggered** — both predicates remain honest signatures (no
`sorry`, no `True.intro` in the headline path); they are *designed* as the
deferral boundary. But the work behind them is materially larger than "compose
existing pieces."

---

## 主定理の最終形（再掲）

`InformationTheory/Shannon/LZ78DistinctEncoding.lean:412`:

```lean
theorem lz78_two_sided_optimality_distinct_bdd_free
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (h_achiev : IsLZ78AchievabilityChainHyp μ p.toStationaryProcess
                  (@lz78DistinctEncodingLength α _ _ _))
    (h_converse : IsLZ78ConverseChainHyp μ p.toStationaryProcess
                  (@lz78DistinctEncodingLength α _ _ _)) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => (lz78DistinctEncodingLength n (p.toStationaryProcess.blockRV n ω):ℝ)/(n:ℝ))
      Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess))
```

The two hypotheses (bodies copied verbatim):

```lean
-- IsLZ78AchievabilityChainHyp (LZ78FinalGlue.lean:118)  -- Eq. 13.124
∀ᵐ ω ∂μ, Filter.limsup (fun n => (lz n (blockRV n ω):ℝ)/(n:ℝ)) atTop
       ≤ Filter.limsup (fun n => blockLogAvg μ p n ω) atTop

-- IsLZ78ConverseChainHyp (LZ78ConverseDischarge.lean:106)  -- Eq. 13.130
∀ᵐ ω ∂μ, Filter.liminf (fun n => blockLogAvg μ p n ω) atTop
       ≤ Filter.liminf (fun n => (lz n (blockRV n ω):ℝ)/(n:ℝ)) atTop
```

Pseudo-Lean discharge strategy that would be required (Cover–Thomas 13.5):

```text
-- per fixed sample path x = block ω, with parsing into c = c(x) distinct phrases:
1.  lz n x / n = (c · bitLength c |α|) / n            -- lz78DistinctEncodingLength_eq (HAVE)
2.  c · log c ≤ -Σⱼ log Pₙ{phraseⱼ}                  -- Ziv ineq, Lemma 13.5.5  (MISSING)
3.  -Σⱼ log Pₙ{phraseⱼ} ≤ -log Pₙ{block ω} (= n·blockLogAvg)  -- chain over parsing (MISSING)
4.  combine 1–3 → (lz n x)/n ≤ blockLogAvg + o(1)     -- (needs c=O(n/log n), HAVE asym)
5.  take limsup / liminf, push o(1) to 0              -- filter plumbing (mostly HAVE)
```

---

## API 在庫テーブル

### Q1 — discrete entropy chain rule / subadditivity

**Mathlib has NO Shannon entropy at all.** `ls
.lake/packages/mathlib/Mathlib/InformationTheory/` = `{Coding/, Hamming.lean,
KullbackLeibler/}`. `rg 'def (measureEntropy|entropy|condEntropy)'` over all of
Mathlib → **0 hits**. `loogle "ProbabilityTheory.entropy"` →
`unknown identifier`. All discrete-entropy infrastructure is **project-local**.

| 概念 | API | file:line | 状態 | LZ78-Ziv での扱い |
|---|---|---|---|---|
| base Shannon entropy `H(X)` (over μ) | `entropy` | `InformationTheory/Shannon/Entropy.lean` (def imported from `Pi`/`MeasureFano`; used `:20+`) | GENUINE | **expectation-level only** — wrong level for per-path Ziv |
| cond. entropy `H(X\|Y)` (over μ) | `MeasureFano.condEntropy` | `InformationTheory/Fano/Measure.lean:68` | GENUINE | expectation-level |
| 2-var chain rule `H(X,Y)=H(X)+H(Y\|X)` | `entropy_pair_eq_entropy_add_condEntropy` | `InformationTheory/Shannon/Entropy.lean:41` | GENUINE | base case of n-var chain |
| **n-var chain rule** `H(X₀,…,X_{n-1})=Σ H(Xᵢ\|X₀..X_{i-1})` | `jointEntropy_chain_rule` | `InformationTheory/Shannon/Han.lean:56` | GENUINE | **fixed `Fin n`, NOT random `c`; expectation-level** |
| Han subadditivity-family `(n-1)H(Xs)≤Σ H(Xs except i)` | `han_inequality` | `InformationTheory/Shannon/Han.lean:330` | GENUINE | wrong shape (Han, not `H≤ΣH`) |
| conditioning reduces entropy `H(X\|Y)≤H(X)` | `entropy_ge_condEntropy` | `InformationTheory/Shannon/SlepianWolf.lean:164` | GENUINE | the step that turns chain rule → subadditivity |
| `H(X\|Y,Z)≤H(X\|Y)` | `condEntropy_le_condEntropy_of_pair` | `InformationTheory/Shannon/Entropy.lean:240` | GENUINE | same |
| subset chain rule `H(X_S)=Σ_{i∈S} H(Xᵢ\|X_{S∩<i})` | `jointEntropySubset_chain_rule` | `InformationTheory/Shannon/HanD.lean:191` | GENUINE | over a `Finset`, still expectation-level + fixed index space |
| **per-sample subadditivity `H≤Σ Hᵢ` over RANDOM `c`** | — | — | ❌ **不在** | the core need |

#### `jointEntropy_chain_rule` (full signature, verbatim)

`InformationTheory/Shannon/Han.lean:56` — context vars at `:36-39`
`{n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
[MeasurableSingletonClass α] {Ω : Type*} [MeasurableSpace Ω]`:

```lean
theorem jointEntropy_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    jointEntropy μ Xs
      = ∑ i : Fin n,
          InformationTheory.MeasureFano.condEntropy μ (Xs i)
            (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
```
Args: `(μ : Measure Ω)`, inst `[IsProbabilityMeasure μ]`,
`(Xs : Fin n → Ω → α)`, `(hXs : ∀ i, Measurable (Xs i))`.
Conclusion (verbatim): see above — `jointEntropy μ Xs = ∑ i : Fin n, …condEntropy…`.

> **CRUCIAL Q1 answer**: the n-var chain rule **is** over a variable number `n`
> of components — **but `n` is a fixed `ℕ` parameter, not a random variable**, the
> components `Xs : Fin n → Ω → α` are a *fixed* family, and the entropy is the
> **expectation** `entropy μ (fun ω i => Xs i ω)` (= `∫ negMulLog … ∂(μ.map …)`).
> The Ziv inequality needs the **deterministic** statement
> `-log Pₙ{x} ≤ -Σⱼ log Pₙ{phraseⱼ(x)}` for a *single* point `x = block ω`, where
> the number of phrases `c(x)` and their lengths depend on `x`. This is a
> **conditional-probability / parsing** statement, not the μ-integrated entropy
> the existing chain rule produces. The two are **not interchangeable** and no
> conversion bridge exists.

#### `entropy_ge_condEntropy` (full signature, verbatim)

`InformationTheory/Shannon/SlepianWolf.lean:164`:
```lean
theorem entropy_ge_condEntropy
    {Ω : Type*} [MeasurableSpace Ω]
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
      [MeasurableSpace W] [MeasurableSingletonClass W]
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ws : Ω → W) (Yo : Ω → Y)
    (hWs : Measurable Ws) (hYo : Measurable Yo) :
    InformationTheory.MeasureFano.condEntropy μ Ws Yo ≤ entropy μ Ws
```
Conclusion (verbatim): `… condEntropy μ Ws Yo ≤ entropy μ Ws`.
Note `[MeasurableSingletonClass W]`, `[Fintype W]`, `[Nonempty W]` on the value
type of `Ws`; `Y` only needs `[MeasurableSpace Y]`.

#### `condEntropy_le_condEntropy_of_pair` (verbatim)

`InformationTheory/Shannon/Entropy.lean:240` — context `{X,Y,Z}` each
`[Fintype _] [DecidableEq _] [Nonempty _] [MeasurableSpace _]
[MeasurableSingletonClass _]`, `{Ω} [MeasurableSpace Ω]`:
```lean
theorem condEntropy_le_condEntropy_of_pair
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZo : Measurable Zo) :
    InformationTheory.MeasureFano.condEntropy μ Xs (fun ω => (Yo ω, Zo ω))
      ≤ InformationTheory.MeasureFano.condEntropy μ Xs Yo
```

### Q2 — log-sum inequality

| 概念 | API | file:line | 状態 |
|---|---|---|---|
| convexity of `x·log x` | `Real.strictConvexOn_mul_log` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:137` | GENUINE |
| convexity of `x·log x` (non-strict) | `Real.convexOn_mul_log` | `…/NegMulLog.lean:144` | GENUINE |
| concavity of `negMulLog` | `Real.concaveOn_negMulLog` | `…/NegMulLog.lean:227` | GENUINE |
| **finset Jensen (convex)** | `ConvexOn.map_sum_le` | `Mathlib/Analysis/Convex/Jensen.lean:67` | GENUINE |
| finset Jensen (concave) | `ConcaveOn.le_map_sum` | `Mathlib/Analysis/Convex/Jensen.lean:73` | GENUINE |
| **packaged log-sum ineq** `Σaᵢlog(aᵢ/bᵢ)≥(Σaᵢ)log(Σaᵢ/Σbᵢ)` | — | — | ❌ **不在 (Mathlib + project)** |
| project log-sum (`sum_negMulLog_…`) | `sum_negMulLog_sub_le_sum_mul_log_card` | `InformationTheory/Fano/Core.lean:85` | GENUINE but **different inequality** (entropy ≤ log card, not log-sum) |

`rg 'log_sum|logSum'` over Mathlib → 0 packaged lemmas; project hits
(`ConditionalMethodOfTypes.logSumAbs`, …) are unrelated `Σ\|log\|` magnitudes.

#### `Real.strictConvexOn_mul_log` (verbatim)
`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:137` (namespace `Real`):
```lean
lemma strictConvexOn_mul_log : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x)
```
No type-class prerequisites (concrete `ℝ`). Conclusion verbatim:
`StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x)`.

#### `ConvexOn.map_sum_le` (verbatim)
`Mathlib/Analysis/Convex/Jensen.lean:67` — section context (from file head)
`{𝕜 E β ι} [LinearOrderedField 𝕜] [AddCommGroup E] [OrderedAddCommMonoid β]
[Module 𝕜 E] [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E} {f : E → β} {t : Finset ι}
{w : ι → 𝕜} {p : ι → E}`:
```lean
theorem ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i)
```
Conclusion verbatim: `f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i)`.

> **Q2 answer**: the *primitive* (convexity + finset Jensen) is present, so a
> log-sum inequality is **derivable** (~30–60 lines: instantiate Jensen for
> `x↦x·log x` with weights `bₖ/Σb`, points `aₖ/bₖ`). No off-the-shelf log-sum
> lemma exists in Mathlib or the project.

### Q3 — what the project already has for the Ziv layer

`LZ78ZivInequality.lean` — **combinatorial layer only, GENUINE**:
- `LZ78Parsing.card_phraseSet_le_pow` (`:204`): `phraseSet.card ≤ (count+1)·|α|` — GENUINE.
- `LZ78Parsing.card_phraseSet_le_count` (`:161`), `card_phraseSet_le_succ_mul_card` (`:236`) — GENUINE.
- `ZivCountingBound` (`:280`) `:= (p.count : ℝ) ≤ B` — real-valued **counting** slot, GENUINE but only the count layer.
- `IsZivInequalityPassthrough.ofZivCountingBound` (`:325`) → `:= True.intro` — **PLACEHOLDER**.
- parent `IsZivInequalityPassthrough` (`LempelZiv78.lean:221`) `:= True` — **PLACEHOLDER**.

`LZ78ConverseAsymptotic.lean` — **asymptotic phrase-count layer, GENUINE**:
- `IsLZ78PhraseCountAsymptotic` (`:120`) + `.of_n_div_log` (`:342`), `lz78_phrase_count_asymptotic` (`:378`) — GENUINE (`c=O(n/log n)`).
- `IsZivInequalityPassthrough.ofAsymptotic` (`:230`) → `True.intro` — **PLACEHOLDER**.

`LZ78PhraseCountAsymptoticBody.lean` — **`c·log c ≤ K·n` inversion, GENUINE**:
- `IsZivCountingMulLogBound` (`:192`) `:= ∀ n, (p n).count · log (p n).count ≤ K·n`.
- `isBigO_natCast_div_log_of_mul_log_le` (`:107`), `IsLZ78PhraseCountAsymptotic.of_mul_log_bound` (`:198`) — GENUINE inversion `c·log c ≤ Kn → c = O(n/log n)`.

`LZ78SMBSandwich.lean` — **SMB layer GENUINE; the converse bridge is a re-export**:
- `lz78_smb_sandwich_ergodic` (`:388`), `_liminf`/`_limsup`/`_tendsto` (`:401-`) — GENUINE (chain to `shannon_mcmillan_breiman`).
- `IsSMBToLZ78ConverseChainBridge` (`:348`) `:= IsLZ78ConverseChainHyp …` — **definitional alias** (NOT a discharge); the substantive Eq. 13.130 (L-LZ3-D) is deferred. `IsLZ78ConverseChainHyp.ofSMBBridge` (`:362`) is the identity `:= h`.

**Genuine vs placeholder, in the achiev/converse chain:**
`h_achiev`/`h_converse` themselves are honest **signatures** (real `∀ᵐ … ≤ …`
bodies, not `True`). All `IsZivInequalityPassthrough.of*` constructors that
*would* feed the headline are `True.intro` placeholders, but the headline path
(`lz78_two_sided_optimality_distinct_bdd_free`) does **not** route through
`IsZivInequalityPassthrough` — it takes `h_achiev`/`h_converse` directly. So the
remaining work is **proving those two predicates**, not discharging a `True`.

**Precise target lemma whose proof discharges everything:** a per-path Ziv bound
```lean
-- DETERMINISTIC, for x : Fin n → α, with c := (lz78PhraseStrings (List.ofFn x)).length:
(c : ℝ) * Real.log c
  ≤ - Real.log ((μ.map (p.blockRV n)).real {x})        -- = n · blockLogAvg at x
```
(Cover–Thomas Eq. 13.122–13.124). Composed with the GENUINE `c=O(n/log n)`
envelope and `lz78DistinctEncodingLength_eq`, this yields
`(lz n x)/n ≤ blockLogAvg μ p n x + o(1)` pointwise, hence the limsup form
(`h_achiev`); the converse (`h_converse`) is the matching liminf reading.

### Q4 — `blockLogAvg` ↔ block-probability

`blockLogAvg` definition (verbatim), `InformationTheory/Shannon/ShannonMcMillanBreiman.lean:55`
— context `{Ω}[MeasurableSpace Ω] {α}[Fintype α][DecidableEq α][Nonempty α]
[MeasurableSpace α][MeasurableSingletonClass α]`:
```lean
noncomputable def blockLogAvg
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) : Ω → ℝ :=
  fun ω => -(1 / (n : ℝ)) * Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})
```
So `n · blockLogAvg μ p n ω = - log Pₙ{block ω}`, `Pₙ := μ.map (blockRV n)`,
`{block ω}` a singleton, `(·).real` = `Measure.real` = `ENNReal.toReal ∘ μ`.

| 概念 | API | file:line | 状態 |
|---|---|---|---|
| `blockLogAvg` def | `blockLogAvg` | `ShannonMcMillanBreiman.lean:55` | GENUINE (def) |
| `blockLogAvg` measurability | `measurable_blockLogAvg` | `ShannonMcMillanBreiman.lean:61` | GENUINE |
| `𝔼[blockLogAvg n] = blockEntropy/n` | `expected_blockLogAvg_eq` | `ShannonMcMillanBreiman.lean:116` | GENUINE — **the only link `blockLogAvg ↔ entropy`, and it is at the EXPECTATION level** |
| `blockLogAvg → entropyRate` a.s. (SMB) | `shannon_mcmillan_breiman` | `SMBAlgoetCover.lean:2840` | GENUINE |
| **`blockLogAvg` ↔ parsing / phrase structure** | — | — | ❌ **不在** |

> **Q4 answer**: `blockLogAvg` is per-sample `-(1/n)·log Pₙ{block ω}` via
> `Measure.real` on a **singleton** of the pushforward `μ.map (blockRV n)`. The
> only existing bridge to entropy is `expected_blockLogAvg_eq`, and it is
> **integrated** (`∫ blockLogAvg = blockEntropy/n`). **No lemma connects
> `blockLogAvg` to `LZ78Parsing` / `lz78PhraseStrings` / phrase probabilities.**
> The Ziv layer must build this bridge from scratch at the *per-sample* level.

---

## 主要前提条件ボックス（事故りやすい lemma の前提）

- **`jointEntropy_chain_rule`** (`Han.lean:56`): requires `[IsProbabilityMeasure μ]`
  and the value type `α` to carry `[Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]`; the **index space is a fixed
  `Fin n`** with `n : ℕ` a parameter. *Will not* accept a random/`ω`-dependent
  component count. Components must be a fixed `Xs : Fin n → Ω → α`. Conclusion is
  `entropy μ (…)`, i.e. **integrated over μ**.
- **`entropy_ge_condEntropy`** (`SlepianWolf.lean:164`): `[IsProbabilityMeasure μ]`;
  value type `W` needs `[Fintype][DecidableEq][Nonempty][MeasurableSingletonClass]`.
  Conditioning-side `Y` only `[MeasurableSpace Y]`. Used to drop conditioning →
  but again **expectation-level**.
- **`ConvexOn.map_sum_le`** (`Jensen.lean:67`): weights must satisfy `∑ w = 1`
  and `0 ≤ wᵢ`, points `pᵢ ∈ s = Set.Ici 0`. For the log-sum step, the
  positivity `pₖ = aₖ/bₖ ≥ 0` and `bₖ > 0` must be discharged pointwise — the
  phrase probabilities `Pₙ{phraseₖ}` can be **zero** for an unseen phrase, which
  is a genuine `0·log 0`/`log 0 = 0` edge-case landmine.
- **`expected_blockLogAvg_eq`** (`ShannonMcMillanBreiman.lean:116`): needs
  `[IsProbabilityMeasure μ]` and `0 < n`. It is **not** the per-sample identity;
  do not mistake it for a pointwise bridge.
- **`blockLogAvg` at `n = 0`** is `0` (factor `1/0 = 0`); any per-path Ziv lemma
  must special-case `n = 0` and the `log 0 = 0` (`Pₙ{x} = 0`) branches.

---

## 自作が必要な要素（優先度順）

1. **`ziv_per_path_mul_log_le` — deterministic Ziv inequality (Cover–Thomas
   Lemma 13.5.5).** Signature target:
   `(c : ℝ) · log c ≤ - log (Pₙ.real {x})` for `x : Fin n → α`,
   `c := (lz78PhraseStrings (List.ofFn x)).length`. *No analogue exists.*
   Requires: a per-path account of the distinct phrases as a product of
   conditional probabilities under the parsing, then a log-sum step. **Hardest
   item**; estimate **150–300 lines** plus possibly a new `LZ78Parsing`
   factorization lemma `Pₙ{x} = Πⱼ (conditional phrase probs)`. Pitfall: the
   parsing factorization `Pₙ{block} = Πⱼ P{phraseⱼ | prefix}` is **itself not in
   the project** and is the true crux — without it the chain rule has nothing to
   chain over.
2. **`log_sum_inequality` — derive from `ConvexOn.map_sum_le` + `convexOn_mul_log`.**
   `Σ aₖ log(aₖ/bₖ) ≥ (Σaₖ) log(Σaₖ/Σbₖ)`. All primitives present; estimate
   **30–60 lines**. Pitfall: `0·log 0` / zero-`bₖ` edge handling.
3. **`blockLogAvg_eq_neg_log_blockProb` (trivial restatement)** —
   `n · blockLogAvg μ p n ω = - log (Pₙ.real {block ω})` for `0 < n`. ~5 lines
   from the def; needed to phrase target 1 against `blockLogAvg`.
4. **`lz_per_symbol_le_blockLogAvg_add_smallo` — assembly.** Combine 1+3 with the
   GENUINE `lz78DistinctEncodingLength_eq` and the GENUINE `c=O(n/log n)`
   envelope to get `(lz n x)/n ≤ blockLogAvg + ε(n)` with `ε → 0`, then take
   `limsup`/`liminf`. Estimate **80–150 lines** of filter / `o(1)` plumbing
   (much of the `limsup` machinery is reusable from the existing achiev/converse
   collapse lemmas `lz78_achievability_upper_bound_ergodic`).

Total realistic estimate: **300–500 lines**, dominated by item 1 + the missing
parsing-factorization sub-lemma.

---

## 撤退ラインへの距離

Parent retreat line (`LZ78FinalGlue.lean:74-82`, `LZ78ZivInequality.lean:37-46`):
the two chain hypotheses `IsLZ78ConverseChainHyp` / `IsLZ78AchievabilityChainHyp`
are *the* designated deferral boundary (L-LZ1-C/D, L-LZ3-D); the headline is
"maximally discharged from the current wave's ingredients."

**判定: NOT triggered.** The headline already sits exactly on the retreat line —
both predicates are honest signatures (no `sorry`, no `True.intro`), so the
current state is the intended retreat state. **Discharging them is a forward
move past the line, not a retreat.** Nothing here forces a *new* retreat: no
hypothesis was found to require an unexpected `[StandardBorelSpace]` /
`[Countable]` / extra finiteness beyond `[IsProbabilityMeasure]` +
finite-alphabet instances already in scope.

**Proposed new (sub-)retreat line if item 1 stalls:** if the per-path
factorization `Pₙ{block} = Πⱼ (conditional phrase probs)` cannot be proved within
~1 week, retreat to publishing a **deterministic Ziv counting→log bridge as a
hypothesis-parameterized lemma** (take the factorization as an explicit honest
hypothesis `h_factor : Pₙ{x} = …`), discharging items 2–4 genuinely and leaving
*only* the factorization as the residual honest input — strictly more primitive
than the current `blockLogAvg`-level hypotheses, and a smaller deferral than the
status quo.

---

## 着手 skeleton

`InformationTheory/Shannon/LZ78ZivEntropyBridge.lean` の出だし:

```lean
import InformationTheory.Shannon.LZ78ZivInequality
import InformationTheory.Shannon.LZ78ConverseAsymptotic
import InformationTheory.Shannon.LZ78DistinctEncoding
import InformationTheory.Shannon.ShannonMcMillanBreiman
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Target 3 (trivial restatement).** `n · blockLogAvg = -log Pₙ{block ω}`. -/
theorem blockLogAvg_eq_neg_log_blockProb
    (μ : Measure Ω) (p : StationaryProcess μ α) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    (n : ℝ) * blockLogAvg μ p n ω
      = - Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω}) := by
  sorry

/-- **Target 2 (log-sum, from `ConvexOn.map_sum_le`).** -/
theorem log_sum_inequality
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  sorry

/-- **Target 1 (deterministic Ziv, Cover–Thomas Lemma 13.5.5).** -/
theorem ziv_per_path_mul_log_le
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) (x : Fin n → α) :
    ((lz78PhraseStrings (List.ofFn x)).length : ℝ)
        * Real.log ((lz78PhraseStrings (List.ofFn x)).length : ℝ)
      ≤ - Real.log ((μ.map (p.blockRV n)).real {x}) := by
  sorry  -- needs parsing-factorization sub-lemma (the true crux)

/-- **Target 4 (assembly) → `IsLZ78AchievabilityChainHyp`.** -/
theorem isLZ78AchievabilityChainHyp_distinct
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    IsLZ78AchievabilityChainHyp μ p.toStationaryProcess
      (@lz78DistinctEncodingLength α _ _ _) := by
  sorry

end InformationTheory.Shannon
```

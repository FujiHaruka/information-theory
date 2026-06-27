# Chernoff converse — Phase B (Sanov wiring) in-project inventory

> Parent sub-plan: [`docs/shannon/chernoff-converse-plan.md`](chernoff-converse-plan.md)
> (Parent of that: `docs/textbook-roadmap.md`, Ch.11). Phase A is **complete + sorryAx-free**
> in `InformationTheory/Shannon/Chernoff/Converse.lean`; this file inventories the assets Phase B
> needs to wire the Sanov LDP lower bound into `chernoff_converse`.
>
> Scope of this survey: **in-project** (`rg` + `Read`, not loogle). Only the small handful of
> Mathlib measure primitives at the very bottom were spot-checked against `.lake/packages/mathlib`.

---

## 1. The 2-world bridge — conclusion (the 3 highest risks resolved)

The brief named three make-or-break questions. All three are **answered in the favourable
direction** — every bridge already exists in-project (mostly via the `Hoeffding/Tradeoff*`
precedent, which does the *identical* Sanov-instantiation dance for the Hoeffding tradeoff).

| # | Question | Verdict | Asset |
|---|---|---|---|
| (i) | Is `bayesErrorMinPmf` measure-world or pmf-world? | **Real pmf world** — `(1/2)·∑ x:Fin n→α, min(∏P₁, ∏P₂)`, a finite real sum, **not** `Measure.pi`. | `bayesErrorMinPmf` (`Chernoff/Basic.lean:644`) |
| (ii) | Is there a `klDivSumForm_ofVec ↔ klDivPmf` bridge? | **Yes, 1-line.** Both unfold to `∑ a, P a·(log P a − log Q a)` once `∑P=∑Q=1` (+ Q full support). No single *named* lemma, but `klDivPmf_eq_log_diff_sum` / `klDivPmf_eq_log_diff_sum_of_Q_pos` + `unfold klDivSumForm_ofVec` give it. Used verbatim in `hoeffding_tradeoff_exp` (`h_lhs_bridge`). | `CsiszarProjection.lean:240`, `TradeoffExp.lean:97`, `KLDivContinuous.lean:34` |
| (iii) | Is the error region `{P₁ⁿ≤P₂ⁿ}` ↔ type-class union machinery present? | **The union shape + per-`c` measure decomposition exist** (`typeClassByCount`, `klDivIndex`, `E_r` filter pattern). The *specific* "`{∏P₁≤∏P₂}` = `⋃ c∈E n, T_c`" decomposition is **not yet written** but is a direct clone of `E_r` / `steinTypeII_exp`. | `LDP.lean:79/85`, `TradeoffExp.lean:62/75` |

**Bridge between the two worlds** (the crux): the measure `Q₁ := pmfToMeasure P₁` satisfies
`Q₁.real {a} = P₁ a` (`pmfToMeasure_real_singleton`), and for any finite set
`(Measure.pi (fun _ ↦ Q₁)) S).toReal = ∑ x∈S, ∏ i, Q₁.real {x i} = ∑ x∈S, ∏ i, P₁ (x i)`.
That measure→sum identity is **demonstrated inline** inside `typeClass_Qn_le`
(`Sanov/Basic.lean:181`, the `h_pi_real_eq_sum` block: `Measure.pi_singleton` + `ENNReal.toReal_prod`
+ `sum_measureReal_singleton`) but is **not extracted** as a reusable lemma — extracting it is
one of the Phase B helpers.

So `bayesErrorMinPmf` (pmf world) and `sanov_ldp_equality` (measure world) connect through
`Q₁ = pmfToMeasure P₁`, and Phase A's `chernoffInfo = klDivPmf (T_λ*) P₁` connects to the Sanov
rate `klDivSumForm_ofVec (T_λ*) (Q₁.real∘singleton)` by bridge (ii).

**Single most dangerous finding** (see §4-W1): Phase A's `chernoffMediator_isMinOn` minimizes over
`chernoffHalfSpace`, whose membership *requires strict positivity* `∀ a, 0 < p a`. The Sanov
`h_minimizer` premise quantifies over **all** `c ∈ E n`, whose empirical pmfs `c/n` may have
**zero entries** (boundary of the simplex). So `chernoffMediator_isMinOn` does **not** discharge
`h_minimizer` as-is — it needs extension to the *closed* half-space. This is the one genuine
self-build (moderate), not a wall.

---

## 2. The target headline (restated) + Phase B proof flow

Lives in `Chernoff/Converse.lean`'s closing docstring (kept out of code until proven, to preserve
the project 0-`sorry` invariant). Predicted final form:

```lean
theorem chernoff_converse
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]          -- ← NEW (Sanov demands these)
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (lam : ℝ)
    (hlam_min : IsMinOn (fun l ↦ Real.log (chernoffZSum P₁ P₂ l)) (Set.Icc 0 1) lam)
    (hlam_io  : lam ∈ Set.Ioo (0:ℝ) 1)                        -- ← interiority (retreat-line hyp)
    (hinfo    : chernoffInfo P₁ P₂ = -(Real.log (chernoffZSum P₁ P₂ lam))) :
    Filter.limsup (fun n : ℕ ↦ -((1:ℝ)/n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop
      ≤ chernoffInfo P₁ P₂
```

Proof flow (≈ Hoeffding-tradeoff-converse shape, but only the *lower* Sanov half is needed):

```
let Q₁ := pmfToMeasure P₁ ; Q₁.real{a} = P₁ a                                  -- measure lift
let T  := chernoffMediator P₁ P₂ lam ;  D := klDivPmf T P₁ = chernoffInfo      -- Phase A
let E n := { c : TypeCountIndex α n | ∑c=n ∧ ∏P₁^c ≤ ∏P₂^c }                   -- error region (clone E_r)
errReg n = ⋃ c∈E n, typeClassByCount c  = {x | ∏P₁(x_i) ≤ ∏P₂(x_i)}           -- region = union (build)
bayesErrorMinPmf ≥ (1/2)·(Measure.pi Q₁)(errReg).toReal                        -- min=∏P₁ on region (build)
sanov_ldp_lower_bound_pointwise Q₁ T E (h_in_E) :                              -- LiminfBound.lean:132
   -klDivSumForm_ofVec T (Q₁.real∘sing) ≤ liminf (1/n) log Q₁ⁿ(errReg)
klDivSumForm_ofVec T (Q₁.real∘sing) = klDivPmf T P₁ = D = chernoffInfo         -- bridge (ii) + Phase A
⟹ liminf (1/n) log bayesError ≥ -chernoffInfo ⟹ limsup -(1/n)log bayesError ≤ chernoffInfo
```

`h_in_E` (rounded type of `T` eventually in `E n`) and `h_minimizer` (`D ≤ klDivIndex c n Q₁` ∀c∈E n)
are the two non-trivial Sanov premises — see §4.

---

## 3. API inventory tables (structured, signatures verbatim)

### A. Chernoff side — `bayesErrorMinPmf` and friends (`InformationTheory/Shannon/Chernoff/Basic.lean`)

Variable context for the whole file: `variable {α : Type*} [Fintype α] [DecidableEq α]`.

| concept | decl | file:line | full signature (verbatim) | conclusion form (verbatim) |
|---|---|---|---|---|
| Bayes error (n-IID, equal prior) | `bayesErrorMinPmf` | `Chernoff/Basic.lean:644` | `noncomputable def bayesErrorMinPmf (P₁ P₂ : α → ℝ) (n : ℕ) : ℝ` | `(1 / 2 : ℝ) * ∑ x : Fin n → α, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i))` |
| per-point min bound | `min_le_rpow_mul_rpow` | `Chernoff/Basic.lean:652` | `(ha : 0 ≤ a) (hb : 0 ≤ b) {lam : ℝ} (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1)` [omit `DecidableEq`] | `min a b ≤ a ^ (1 - lam) * b ^ lam` |
| product factorisation | `prod_rpow_mul_rpow` | `Chernoff/Basic.lean:688` | `(P₁ P₂ : α → ℝ) (hP₁_nn : ∀ a, 0 ≤ P₁ a) (hP₂_nn : ∀ a, 0 ≤ P₂ a) {n : ℕ} (x : Fin n → α) (lam : ℝ)` | `∏ i, (P₁ (x i))^(1-lam) * (P₂ (x i))^lam = (∏ i, P₁ (x i))^(1-lam) * (∏ i, P₂ (x i))^lam` |
| n-IID partition fn | `sum_prod_rpow_eq_Z_pow` | `Chernoff/Basic.lean:705` | `(P₁ P₂ : α → ℝ) (hP₁_nn …) (hP₂_nn …) (lam : ℝ) (n : ℕ)` | `∑ x : Fin n → α, (∏ i, P₁ (x i))^(1-lam) * (∏ i, P₂ (x i))^lam = (chernoffZSum P₁ P₂ lam) ^ n` |
| Chernoff bound | `bayesErrorMinPmf_le_half_Z_pow` | `Chernoff/Basic.lean:732` `@[entry_point]` | `(P₁ P₂ : α → ℝ) (hP₁_nn …) (hP₂_nn …) (n : ℕ) {lam : ℝ} (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1)` | `bayesErrorMinPmf P₁ P₂ n ≤ (1 / 2 : ℝ) * (chernoffZSum P₁ P₂ lam) ^ n` |
| positivity | `bayesErrorMinPmf_pos` | `Chernoff/Basic.lean:761` | `(P₁ P₂ : α → ℝ) [Nonempty α] (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (n : ℕ)` | `0 < bayesErrorMinPmf P₁ P₂ n` |
| Chernoff info (def) | `chernoffInfo` | `Chernoff/Basic.lean:67` | `noncomputable def chernoffInfo (P₁ P₂ : α → ℝ) : ℝ` | `-(sInf ((fun lam : ℝ ↦ Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1))` |
| partition fn (def) | `chernoffZSum` | `Chernoff/Basic.lean:62` | `noncomputable def chernoffZSum (P₁ P₂ : α → ℝ) (lam : ℝ) : ℝ` | `∑ a : α, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam` |
| mediator pmf (def) | `chernoffMediator` | `Chernoff/Basic.lean:494` | `noncomputable def chernoffMediator (P₁ P₂ : α → ℝ) (lam : ℝ) : α → ℝ` | `fun a ↦ (P₁ a)^(1-lam) * (P₂ a)^lam / chernoffZSum P₁ P₂ lam` |
| min attained | `chernoffInfo_attained` | `Chernoff/Basic.lean:156` | `(P₁ P₂ : α → ℝ) [Nonempty α] (…full support…)` | `∃ lam ∈ Set.Icc (0:ℝ) 1, chernoffInfo P₁ P₂ = -(Real.log (chernoffZSum P₁ P₂ lam))` |

**Note (i)**: `bayesErrorMinPmf` is `∑ x : Fin n → α … min(∏…, ∏…)`, a **real-valued finite sum over
`Fin n → α`** — confirmed verbatim L644-645. It is NOT a `Measure.pi`. `min` is the binary
`min : ℝ → ℝ → ℝ`; the `(1/2)` prefactor is the equal-prior Bayes weight.
**Note**: `chernoffInfo_attained` only yields `lam ∈ Icc 0 1` (closed) — interiority `Ioo 0 1` is NOT
provided and must be a hypothesis (the retreat-line `hlam_io`).

### B. Phase A outputs already in `Chernoff/Converse.lean` (the bridge inputs)

Variable context: `variable {α : Type*} [Fintype α] [DecidableEq α]`; all carry `(P₁ P₂ : α → ℝ) [Nonempty α]`.

| concept | decl | file:line | conclusion form (verbatim) |
|---|---|---|---|
| half-space (def) | `chernoffHalfSpace` | `Converse.lean:183` | `{p \| (∀ a, 0 < p a) ∧ (∑ a, p a = 1) ∧ 0 ≤ ∑ a, p a * Real.log (P₂ a / P₁ a)}` |
| `chernoffInfo` = mediator div | `chernoffInfo_eq_mediator_div` | `Converse.lean:189` | `chernoffInfo P₁ P₂ = klDivPmf (chernoffMediator P₁ P₂ lam) P₁` (under `hlam_min`, `hlam_io`, `hinfo`) |
| mediator is I-projection | `chernoffMediator_isMinOn` | `Converse.lean:205` | `IsMinOn (fun p : α → ℝ ↦ klDivPmf p P₁) (chernoffHalfSpace P₁ P₂) (chernoffMediator P₁ P₂ lam)` (under `hlam_min`, `hlam_io`) |
| balance / FOC | `chernoffMediator_balance` | `Converse.lean:165` | `∑ a, chernoffMediator P₁ P₂ lam a * Real.log (P₂ a / P₁ a) = 0` |

`chernoffMediator_pos` (`Basic.lean:499`) gives `0 < T_λ a` and `chernoffMediator_sum_eq_one`
(`Basic.lean:510`) gives `∑ T_λ = 1` — both needed to satisfy `sanov`'s `hP_full`, `hP_prob` for `P := T_λ`.

### C. Sanov side — LDP statements (the consumers of the bridge)

Variable context: `variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`.

| concept | decl | file:line | full signature (verbatim, incl. `[...]`) | conclusion form (verbatim) |
|---|---|---|---|---|
| **LDP lower bound** (what Phase B needs) | `sanov_ldp_lower_bound_pointwise` | `Sanov/LiminfBound.lean:132` | `(Q : Measure α) [IsProbabilityMeasure Q] (hQpos : ∀ a : α, 0 < Q.real {a}) (P : α → ℝ) (hP_prob : (∑ a, P a) = 1) (hP_full : ∀ a, 0 < P a) (E : ∀ n, Finset (TypeCountIndex α n)) (h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P n ∈ E n)` | `-klDivSumForm_ofVec P (fun a ↦ Q.real {a}) ≤ Filter.liminf (fun n : ℕ ↦ (1 / (n : ℝ)) * Real.log (((Measure.pi (fun _ : Fin n ↦ Q)) (⋃ c ∈ E n, typeClassByCount (α := α) (fun a ↦ (c a : ℕ)))).toReal)) atTop` |
| LDP equality (full) | `sanov_ldp_equality` | `Sanov/TendstoSandwich.lean:128` `@[entry_point]` | adds to the above `(h_minimizer : ∀ n, ∀ c ∈ E n, klDivSumForm_ofVec P (fun a ↦ Q.real {a}) ≤ klDivIndex (fun a ↦ (c a : ℕ)) n Q)` | `Tendsto (fun n : ℕ ↦ (1/(n:ℝ)) * Real.log ((Measure.pi (fun _:Fin n↦Q)) (⋃ c∈E n, typeClassByCount … )).toReal) atTop (𝓝 (-(klDivSumForm_ofVec P (fun a ↦ Q.real {a}))))` |
| LDP upper bound | `sanov_ldp_upper_bound` | `Sanov/LDP.lean:442` | `(Q : Measure α) [IsProbabilityMeasure Q] (hQpos …) (E : ∀ n, Finset (TypeCountIndex α n)) (D : ℝ) (hD : ∀ n, ∀ c ∈ E n, D ≤ klDivIndex (fun a ↦ (c a : ℕ)) n Q) {ε : ℝ} (hε : 0 < ε)` | `∃ N, ∀ n ≥ N, 0 < n → 0 < (Measure.pi … (⋃ …)).toReal → (1/(n:ℝ)) * Real.log ((Measure.pi …)(⋃ …)).toReal ≤ -D + ε` |

**Decision**: the converse only needs the **lower** half. Use
`sanov_ldp_lower_bound_pointwise` (no `h_minimizer` premise → avoids wall W1 entirely if the
liminf bound is enough; but combining with the upper half via `sanov_ldp_equality` *also* avoids W1
only if we still must build `E n` correctly). For a *clean* converse, `sanov_ldp_lower_bound_pointwise`
is sufficient and **does not** require `h_minimizer` — so **W1 (closed-half-space isMinOn) may be
entirely avoidable**. Re-examine in §4.

### D. Sanov building blocks — defs the bridge instantiates

| concept | decl | file:line | full signature (verbatim) | conclusion / body (verbatim) |
|---|---|---|---|---|
| count-index type | `TypeCountIndex` | `Sanov/LDP.lean:59` | `abbrev TypeCountIndex (α : Type*) [Fintype α] (n : ℕ) : Type _` | `α → Fin (n+1)` |
| type class by counts | `typeClassByCount` | `Sanov/LDP.lean:79` | `def typeClassByCount {n : ℕ} (c : α → ℕ) : Set (Fin n → α)` | `{ x \| ∀ a, typeCount x a = c a }` |
| empirical KL (index) | `klDivIndex` | `Sanov/LDP.lean:85` | `noncomputable def klDivIndex (c : α → ℕ) (n : ℕ) (Q : Measure α) : ℝ` | `∑ a : α, ((c a : ℝ) / n) * (Real.log ((c a : ℝ) / n) - Real.log (Q.real {a}))` |
| rounded type seq | `roundedTypeIndex` | `Sanov/RoundedTypeSequence.lean:112` | `noncomputable def roundedTypeIndex (P : α → ℝ) (n : ℕ) : TypeCountIndex α n` | `fun a ↦ ⟨roundedTypeIndexNat P n a, …⟩` (absorber-letter rounding of `⌊n·P a⌋`) |
| rounded sum = n | `roundedTypeIndex_sum` | `Sanov/RoundedTypeSequence.lean:119` | `(P : α → ℝ) (hP : (∑ a, P a) = 1) (hP_nn : ∀ a, 0 ≤ P a) (n : ℕ) (_hn : 0 < n)` | `(∑ a, (roundedTypeIndex P n a : ℕ)) = n` |
| type class nonempty | `typeClassByCount_nonempty_of_sum` | `Sanov/RoundedTypeSequence.lean:306` | `{n : ℕ} (c : α → ℕ) (hc_sum : (∑ a, c a) = n)` | `(typeClassByCount (α := α) (n := n) c).Nonempty` |
| rounded KL → cts limit | `klDivIndex_rounded_tendsto` | `Sanov/RoundedTypeSequence.lean:356` | `(Q : Measure α) (hQpos …) (P : α → ℝ) (hP …) (hP_nn …)` | `Tendsto (fun n ↦ klDivIndex (fun a ↦ (roundedTypeIndex P n a : ℕ)) n Q) atTop (𝓝 (klDivSumForm_ofVec P (fun a ↦ Q.real {a})))` |

### E. KL bridges — `klDivPmf ↔ klDivSumForm_ofVec ↔ klDivIndex` (the rate-side wiring)

| concept | decl | file:line | full signature (verbatim) | conclusion form (verbatim) |
|---|---|---|---|---|
| pmf-form KL (def) | `klDivPmf` | `CsiszarProjection.lean:61` | `noncomputable def klDivPmf (P Q : α → ℝ) : ℝ` | `∑ a : α, Q a * klFun (P a / Q a)` |
| ofVec-form KL (def) | `klDivSumForm_ofVec` | `KLDivContinuous.lean:34` | `noncomputable def klDivSumForm_ofVec (p q : α → ℝ) : ℝ` | `∑ a : α, p a * (Real.log (p a) - Real.log (q a))` |
| **klDivPmf = log-diff sum** | `klDivPmf_eq_log_diff_sum` | `CsiszarProjection.lean:240` | `{P Q : α → ℝ} (hP_sum : ∑ a, P a = 1) (hQ_sum : ∑ a, Q a = 1) (hP_pos : ∀ a, 0 < P a) (hQ_pos : ∀ a, 0 < Q a)` | `klDivPmf P Q = ∑ a : α, P a * (Real.log (P a) - Real.log (Q a))` |
| **same, count-0 tolerant** | `klDivPmf_eq_log_diff_sum_of_Q_pos` | `TradeoffExp.lean:97` | `{P Q : α → ℝ} (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1) (hQ_sum : ∑ a, Q a = 1) (hQ_pos : ∀ a, 0 < Q a)` [omit `DecidableEq`] | `klDivPmf P Q = ∑ a : α, P a * (Real.log (P a) - Real.log (Q a))` |
| klDivIndex = ofVec | `klDivIndex_eq_ofVec` | `KLDivContinuous.lean:61` | `(c : α → ℕ) (n : ℕ) (Q : Measure α)` [omit `DecidableEq Nonempty MeasurableSingletonClass`] | `klDivIndex c n Q = klDivSumForm_ofVec (fun a ↦ (c a : ℝ) / n) (fun a ↦ Q.real {a})` (`:= rfl`) |
| **klDivIndex = klDivPmf empirical** | `klDivIndex_eq_klDivPmf_empirical` | `TradeoffExp.lean:127` | `(Q : Measure α) (hQ_pos : ∀ a, 0 < Q.real {a}) (hQ_sum : ∑ a, Q.real {a} = 1) {n : ℕ} (hn : 0 < n) {c : α → ℕ} (hc_sum : (∑ a, c a) = n)` [omit `DecidableEq`] | `klDivIndex c n Q = klDivPmf (fun a ↦ (c a : ℝ) / n) (fun a ↦ Q.real {a})` |
| decomp via intermediate | `klDivPmf_decomp_via_intermediate` | `CsiszarProjection.lean:269` | `{P Qstar Q} (hP_sum hQs_sum hQ_sum : …=1) (hP_pos hQs_pos hQ_pos : ∀ a, 0 < …)` | `klDivPmf P Q = klDivPmf P Qstar + ∑ a, P a * (Real.log (Qstar a) - Real.log (Q a))` |
| nonneg | `klDivPmf_nonneg` | `CsiszarProjection.lean:67` | `(P Q : α → ℝ) (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a)` | `0 ≤ klDivPmf P Q` |

The bridge (ii) `klDivSumForm_ofVec T (Q₁.real∘sing) = klDivPmf T P₁` is exactly the
`hoeffding_tradeoff_exp` `h_lhs_bridge` block (`TradeoffExp.lean:553-558`): `klDivSumForm_ofVec` unfold
→ `klDivPmf_eq_log_diff_sum_of_Q_pos` → `Finset.sum_congr` rewriting `Q₁.real{a} = P₁ a`.

### F. pmf → Measure lift + measure→sum bridge (the world-crossing)

| concept | decl | file:line | full signature (verbatim) | conclusion form (verbatim) |
|---|---|---|---|---|
| pmf → Measure (def) | `pmfToMeasure` | `Hoeffding/Tradeoff.lean:58` | `noncomputable def pmfToMeasure (P : α → ℝ) (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1) : Measure α` | `(PMF.ofFintype (fun a ↦ ENNReal.ofReal (P a)) …).toMeasure` |
| is prob measure (inst) | `pmfToMeasure_isProbabilityMeasure` | `Hoeffding/Tradeoff.lean:65` | `instance (P : α → ℝ) (hP_nn …) (hP_sum …)` | `IsProbabilityMeasure (pmfToMeasure P hP_nn hP_sum)` |
| real singleton value | `pmfToMeasure_real_singleton` | `Hoeffding/Tradeoff.lean:78` | `(P : α → ℝ) (hP_nn …) (hP_sum …) (a : α)` | `(pmfToMeasure P hP_nn hP_sum).real {a} = P a` |
| singleton (enn) | `pmfToMeasure_apply_singleton` | `Hoeffding/Tradeoff.lean:71` | `(P : α → ℝ) (hP_nn …) (hP_sum …) (a : α)` | `(pmfToMeasure P hP_nn hP_sum) {a} = ENNReal.ofReal (P a)` |
| measure→sum (inline only) | *(not extracted)* | demonstrated `Sanov/Basic.lean:181-191` | uses `Measure.pi_singleton`, `ENNReal.toReal_prod`, `MeasureTheory.sum_measureReal_singleton` | `(Measure.pi (fun _ ↦ Q)) S).toReal = ∑ x∈S.toFinset, ∏ i, Q.real {x i}` |

### G. E-region pattern to clone (`Hoeffding/TradeoffExp.lean`)

| concept | decl | file:line | shape to clone |
|---|---|---|---|
| KL-sublevel Finset | `E_r` | `TradeoffExp.lean:62` | `Finset.univ.filter (fun c : TypeCountIndex α n ↦ 0 < n ∧ (∑ a, (c a:ℕ)) = n ∧ klDivIndex … ≤ r)` |
| membership iff | `mem_E_r_iff` | `TradeoffExp.lean:83` | `c ∈ E_r … ↔ 0 < n ∧ ∑c=n ∧ klDivIndex … ≤ r` |
| n-IID test mass (def) | `steinTypeII_exp` | `TradeoffExp.lean:75` | `((Measure.pi (fun _ ↦ pmfToMeasure P₂ …)) (⋃ c ∈ E_r …, typeClassByCount (fun a ↦ (c a:ℕ)))).toReal` |
| rounded type ∈ E eventually | `roundedTypeIndex_mem_E_r_eventually` | `TradeoffExp.lean:147` | template for discharging `h_in_E` |
| full converse assembly | `hoeffding_tradeoff_exp` | `TradeoffExp.lean:525` `@[entry_point]` | structural blueprint for `chernoff_converse` (liminf + limsup via Sanov, perturbation) |

---

## 4. Mathlib / in-project walls + key-precondition box

### Key-precondition box (accident-prone premises)

- **`sanov_ldp_lower_bound_pointwise` / `sanov_ldp_equality`** require, on `α`:
  `[Fintype] [DecidableEq] [Nonempty] [MeasurableSpace] [MeasurableSingletonClass]`. The Chernoff
  `Converse.lean` block today is only `[Fintype α] [DecidableEq α]` — Phase B's headline **must add
  `[Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`** (honest preconditions; equipping
  a finite alphabet with the discrete σ-algebra — they leak into `chernoff_converse`'s signature).
- The minimizer arg `P` (here `T_λ*`) needs `hP_full : ∀ a, 0 < P a` (✓ `chernoffMediator_pos`) and
  `hP_prob : ∑ P = 1` (✓ `chernoffMediator_sum_eq_one`).
- `Q := pmfToMeasure P₁` needs `hQpos : ∀ a, 0 < Q.real {a}` — supplied by `pmfToMeasure_real_singleton`
  + `hP₁_pos`. Do **not** forget: `pmfToMeasure` itself needs `hP₁_nn` + `hP₁_sum` (so the lift is
  threaded with `(fun a ↦ (hP₁_pos a).le)` and `hP₁_sum`).
- **Interiority `lam ∈ Set.Ioo 0 1`** is *not* derivable from `chernoffInfo_attained` (which only gives
  `Icc`). It is the Phase A `hlam_io`; it persists into the converse as a non-degeneracy precondition
  (the retreat line — see §6). Balance (`∑ T·log(P₂/P₁) = 0`) is *derived* from it, not assumed.
- `klDivPmf_eq_log_diff_sum` needs **full support of BOTH** P and Q; the count-0-tolerant
  `klDivPmf_eq_log_diff_sum_of_Q_pos` relaxes the LEFT (P) to `∀ a, 0 ≤ P a`. Use the latter whenever
  the left argument is an empirical pmf `c/n` (which can have zeros).

### Wall enumeration

**W1 — closed-half-space I-projection (the §1 danger).** `chernoffMediator_isMinOn` minimizes
`klDivPmf · P₁` over `chernoffHalfSpace`, whose membership demands `∀ a, 0 < p a`. If Phase B routes
through `sanov_ldp_equality` (needs `h_minimizer : ∀ c ∈ E n, D ≤ klDivIndex c n Q₁`), then for
`c` with zero counts the empirical pmf `c/n` is on the simplex boundary and is **not** in
`chernoffHalfSpace`, so `isMinOn` does not apply. **NOT a genuine Mathlib wall** — it is a
moderate self-build: extend `isMinOn` to the *closed* half-space `{p | (∀ a, 0 ≤ p a) ∧ ∑p=1 ∧
0 ≤ ∑ p·log(P₂/P₁)}`. Two routes: (a) continuity/closure — `klDivPmf · P₁` is continuous, closed
half-space = closure of open one, inf over closure = inf over open (assets:
`continuous_klDivPmf_left` `CsiszarProjection.lean:77`); (b) re-prove the decomposition argument with
`klFun_zero` handling the zero terms (cf. `klDivPmf_eq_log_diff_sum_of_Q_pos`). **Recommended avoidance:
use `sanov_ldp_lower_bound_pointwise` (LiminfBound.lean:132), which has NO `h_minimizer` premise** —
the converse only needs the liminf lower bound, so W1 is *avoidable entirely*. Refutation done:
the lower-bound lemma's only region premise is `h_in_E`, confirmed verbatim at `LiminfBound.lean:138`.

**W2 — `h_in_E` at the boundary (rounded type of `T_λ*` ∈ E n eventually).** `T_λ*` lies on the
half-space boundary (`∑ T·log(P₂/P₁) = 0`, balance). Rounding `⌊n·T_λ* a⌋` can perturb the discretised
LLR-mean slightly negative, so `roundedTypeIndex T_λ* n` may fall *outside* `E n = {∑(c/n)log(P₂/P₁) ≥ 0}`
for infinitely many n. **NOT a Mathlib wall** — it is the same boundary issue `Hoeffding/TradeoffExp`
solves with the **perturbation trick** (`Qstar_perturb`, `TradeoffExp.lean:187/212/248`): push `T_λ*`
strictly into the open half-space (`∑ T_ε·log(P₂/P₁) > 0`), get `roundedTypeIndex T_ε ∈ E n` eventually
(`klDivIndex_rounded_tendsto` + `klDivSumForm_ofVec_continuous`), apply the Sanov lower bound, then take
ε→0 (continuity of `klDivPmf · P₁`). Effort: clone ~80-120 lines from TradeoffExp. Pitfall: must verify
`E n` is defined as the **closed** condition `∏P₁^c ≤ ∏P₂^c` (`≤`, not `<`) so the limit ε→0 stays
admissible.

**W3 — error region = type-class union, `{x | ∏P₁(x_i) ≤ ∏P₂(x_i)} = ⋃ c∈E n, typeClassByCount c`.**
The likelihood-ratio test region depends on `x` only through its count vector
(`∏ i P_k(x i) = ∏ a P_k(a)^{typeCount x a}`), so the region is a union of full type classes. **No
genuine wall** — clone the `E_r` / `steinTypeII_exp` pattern (`TradeoffExp.lean:62/75`) with
`E n := univ.filter (fun c ↦ ∑c=n ∧ ∏ a, P₁ a^(c a) ≤ ∏ a, P₂ a^(c a))`. Needed lemmas to self-build
(small): (a) `∏ i, P_k (x i) = ∏ a, P_k a^(typeCount x a)` for `x ∈ typeClassByCount c` — adapt the
fiberwise aggregation in `sum_const_aggr_of_mem_typeClassByCount` (`LDP.lean:89`); (b) the set-equality
of the region with the union. Effort: ~40-70 lines.

**W4 — measure→sum extraction `(Measure.pi Q)(S).toReal = ∑ x∈S, ∏ Q.real{x i}`.** Demonstrated inline
in `typeClass_Qn_le` (`Sanov/Basic.lean:181-191`) but not a standalone lemma. **No wall** — extract it
(or re-derive inline) from `Measure.pi_singleton` + `ENNReal.toReal_prod` + `sum_measureReal_singleton`.
Effort: ~15-25 lines.

No `@residual(wall:…)`-grade Mathlib gaps were found: **every Phase B obligation is plumbing on existing
in-project assets, not an absent Mathlib proposition.** (Consequently no loogle `Found 0` confirmations
are attached — the survey is in-project per the brief; the only Mathlib primitives used
— `Measure.pi_singleton`, `ENNReal.toReal_prod`, `sum_measureReal_singleton`, `PMF.ofFintype` — are all
present and already consumed elsewhere in the project.)

---

## 5. Elements to self-build (priority order) + recommended Phase B decomposition

Each commit unit **must be sorryAx-free** (the project's 0-`sorry` CI text-scans *every*
`InformationTheory/**.lean`, including the unwired `Converse.lean`; a `sorry` even in a helper trips
`gen_readme_table --check`). So land helpers bottom-up; do not commit a `sorry`-laden intermediate.
Wire `Converse.lean` into `InformationTheory.lean` only when `chernoff_converse` is fully proven.

| # | helper (sorryAx-free unit) | closes by | effort | depends on |
|---|---|---|---|---|
| H1 | `errorCount` Finset `E n := univ.filter (∑c=n ∧ ∏P₁^c ≤ ∏P₂^c)` + `mem` iff | existing assets (clone `E_r`) | XS | D, G |
| H2 | `∏ i, P_k (x i) = ∏ a, P_k a^(typeCount x a)` for `x ∈ typeClassByCount c` | self-build (fiberwise, clone `LDP.lean:89`) | S | D |
| H3 | region = union: `{x | ∏P₁(x_i) ≤ ∏P₂(x_i)} = ⋃ c∈E n, typeClassByCount c` (W3) | self-build (H2) | S–M | H1,H2 |
| H4 | measure→sum: `(Measure.pi Q)(S).toReal = ∑ x∈S, ∏ Q.real{x_i}` (W4) | extract from `Sanov/Basic.lean:181` | S | F |
| H5 | `bayesErrorMinPmf P₁ P₂ n ≥ (1/2)·(Measure.pi Q₁)(region).toReal` | self-build (`min=∏P₁` on region + H3,H4 + `pmfToMeasure_real_singleton`) | S–M | H3,H4,F |
| H6 | rate bridge: `klDivSumForm_ofVec T_λ* (Q₁.real∘sing) = chernoffInfo` | existing (bridge ii + Phase A `chernoffInfo_eq_mediator_div`) | XS | B,E,F |
| H7 | `h_in_E`: rounded type of perturbed `T_λ*` ∈ E n eventually (W2) | self-build (clone `Qstar_perturb` + `klDivIndex_rounded_tendsto`) | M | D,G |
| H8 | converse assembly → `chernoff_converse` (limsup ≤ chernoffInfo) | `sanov_ldp_lower_bound_pointwise` + H5,H6,H7 + ε→0 | M | all |

**Per-helper closure prognosis**: H1/H6 = existing-asset (closes immediately); H2/H4 = self-build,
straightforward; H3/H5 = self-build, moderate (set/sum bookkeeping); H7 = self-build, the perturbation
clone (heaviest single piece, ~80-120 lines); H8 = wiring + the `liminf ≥ ⟹ limsup ≤` flip
(`Filter.limsup`/`liminf` neg lemmas). **No helper is a "wall-likely" item** — W1 is bypassed by the
lower-bound route, so the residual risk is purely the H7 perturbation volume.

**Existing-ratio**: of the ~14 distinct API touch-points Phase B needs, **~10 already exist** (tables
A–G assets) and **~4 need self-building** (H2/H3/H4/H5; H7 is a clone of existing perturbation code, H1/H6/H8
are assembly). Call it **≈70% existing / 4 self-build helpers / W1 avoidable**.

---

## 6. Distance to the retreat lines

Parent plan retreat line (`chernoff-converse-plan.md:82-86`):

> If interior-`λ*` balance proves heavy (non-smooth `log Z` at boundary): state `chernoff_converse`
> under a regularity hyp `0 < λ* < 1` … and leave the boundary case as honest `sorry + @residual`.
> Not a load-bearing hyp — it is a non-degeneracy precondition (cf. `Var > 0` in Cramér).

**Does Phase B touch it? YES — and it is already absorbed, not triggered.** Phase A delivered balance
as *derived* from `hlam_io : lam ∈ Ioo 0 1` (`chernoffMediator_balance`), so the converse simply
carries `hlam_io` as a stated precondition (exactly the textbook overlapping-support case). This is a
**precondition, not load-bearing** (the core — the Sanov rate identity — is not bundled into it).
`chernoffInfo_attained` confirms the minimiser exists in `Icc 0 1`; only its *interiority* is assumed.

**New retreat line proposed for Phase B** (degenerate boundary of the *region*, not of λ*): if W2
(boundary rounding / perturbation, H7) proves heavier than the ~120-line estimate, land
`chernoff_converse` with the **liminf lower bound only** under an extra
`h_in_E : ∀ᶠ n, roundedTypeIndex T_λ* n ∈ E n` hypothesis is **forbidden** (that would bundle the core
region-membership as a load-bearing hyp). Instead, the honest retreat is: keep the full headline
signature, leave the H7 perturbation step as `sorry` + `@residual(plan:chernoff-converse-phaseB-Hin-E)`,
commit at type-check-done, and do **not** wire `Converse.lean` into the root until H7 lands. No
hypothesis bundling. (W1 needs no retreat — it is avoided by the lower-bound route.)

---

## 7. Starting skeleton for Phase B in `Chernoff/Converse.lean`

Phase A code stays; Phase B appends below the existing `Phase B/C` docstring section (`Converse.lean:251`).
Imports to add at the top of the file (all acyclic — `Hoeffding/Tradeoff` imports `Chernoff.Basic`, not
`Converse`; `Converse` → `Hoeffding/Tradeoff` is fine):

```lean
import InformationTheory.Shannon.Sanov.LiminfBound        -- sanov_ldp_lower_bound_pointwise
import InformationTheory.Shannon.Sanov.RoundedTypeSequence -- roundedTypeIndex, klDivIndex_rounded_tendsto
import InformationTheory.Shannon.KLDivContinuous          -- klDivSumForm_ofVec, klDivIndex_eq_ofVec
import InformationTheory.Shannon.Hoeffding.Tradeoff       -- pmfToMeasure (+ real_singleton, isProb inst)
-- NOTE: klDivIndex_eq_klDivPmf_empirical / klDivPmf_eq_log_diff_sum_of_Q_pos live in
-- Hoeffding/TradeoffExp.lean; either import it (acyclic) or relocate those 2 small bridges
-- into KLDivContinuous to keep Converse's import surface minimal (design choice for H6).
```

```lean
namespace InformationTheory.Shannon.Chernoff

open MeasureTheory ProbabilityTheory Real Filter
open InformationTheory.Shannon
open scoped BigOperators Topology

-- Phase B works under the measure-equipped alphabet (NEW instances vs. Phase A's [Fintype][DecidableEq]).
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Discretised error region: count vectors `c` (with `∑ c = n`) whose type class lands in the
likelihood-ratio test region `{x | ∏ P₁(x_i) ≤ ∏ P₂(x_i)}`. (Clone of `Hoeffding.E_r`.) -/
noncomputable def chernoffErrorCounts
    (P₁ P₂ : α → ℝ) (n : ℕ) : Finset (TypeCountIndex α n) := by
  sorry -- @residual(plan:chernoff-converse-phaseB-H1) -- def body: rewrite to a `filter` (no real sorry)

/-- Converse half (Cover–Thomas 11.9.1): the optimal Bayes error exponent cannot exceed the
Chernoff information. -/
theorem chernoff_converse
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (lam : ℝ)
    (hlam_min : IsMinOn (fun l : ℝ ↦ Real.log (chernoffZSum P₁ P₂ l)) (Set.Icc 0 1) lam)
    (hlam_io : lam ∈ Set.Ioo (0:ℝ) 1)
    (hinfo : chernoffInfo P₁ P₂ = -(Real.log (chernoffZSum P₁ P₂ lam))) :
    Filter.limsup (fun n : ℕ ↦ -((1:ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop
      ≤ chernoffInfo P₁ P₂ := by
  sorry -- @residual(plan:chernoff-converse-phaseB-H8)

end InformationTheory.Shannon.Chernoff
```

> Reminder: the skeleton above carries `sorry`s only as an illustration. **Do not commit this file
> with `sorry`** — the 0-`sorry` CI invariant fails. Land H1–H7 as sorryAx-free standalone helpers
> first (each compilable on its own), then fill H8 and wire the root in the same final commit.

---

## 8. One-line summary

Of the ~14 API touch-points Phase B needs, **≈70% already exist in-project** (all three world-bridge
risks are favourably resolved: `bayesErrorMinPmf` is real-pmf-world, `klDivPmf↔klDivSumForm_ofVec` is a
1-line bridge already used in `hoeffding_tradeoff_exp`, and `pmfToMeasure` + the measure→sum identity
cross the worlds), **4 helpers need self-building** (H2/H3/H4/H5 — region↔union + measure→sum + bayes≥region),
plus the H7 perturbation clone. **No genuine Mathlib wall** — the apparent W1 (closed-half-space
I-projection) is **avoided** by routing through `sanov_ldp_lower_bound_pointwise` (no `h_minimizer`
premise). The parent's interiority retreat line is **absorbed as a precondition, not triggered**.

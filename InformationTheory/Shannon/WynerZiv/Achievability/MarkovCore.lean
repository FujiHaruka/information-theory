import InformationTheory.Shannon.WynerZiv.Achievability.Concentration

/-!
# Wyner–Ziv achievability — the Markov core and Gateway atom 3 (covering side-information acceptance)
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {α β γ U : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [DecidableEq γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]

open ChannelCoding in
/-- **(L4 part 2 — THE MARKOV CORE) Correlated-joint conditional-typicality concentration.**
For `n` large the source-measure mass of {covering-success ∧ `(x,y)`-block jointly typical ∧
`(u,y)`-block jointly `(U,Y)`-atypical} is at most `tol/8`. This is the Markov lemma `U—X—Y`:
under SRC the pairs `(x_i,y_i)` are iid `~ P_XY` and `u = c.decoder(c.encoder x)` is a
deterministic function of the whole `x`-block, so `Y ⊥ U ∣ X`; given `(x,u)` typical (covering
success, empirical conditional `≈ κ'(·∣x)`) AND `(x,y)` typical, the empirical `(u,y)`-entropy
concentrates around `H(wzSideInfoMarginal)` (the consistent `(U,Y)`-marginal pinned by
`hqStar`/`hκ'_sum`), so `(u,y)`-atypicality has vanishing mass. Because `wzSideInfoMarginal(u,y)
= ∑ₓ κ'(x,u)·P_XY(x,y)` is a sum over `x`, the empirical `(u,y)`-entropy is NOT a linear
combination of the `(x,u)`- and `(x,y)`-empirical entropies, so this is genuinely probabilistic
(a conditional AEP), NOT a deterministic set-inclusion — the correlated-joint concentration is a
from-scratch in-project assembly, absent from Mathlib and the codebase (`plan`, not a Mathlib
wall). The consistency + full-support hyps (`hκ'_pos`, `hκ'_sum`, `hqStar`) are mandatory (pin
qStar's `U`-marginal `= P_U =` wzSideInfoMarginal's `U`-marginal; without them a constant-word
counterexample makes the statement false-as-framed). Left `sorry` — the residual Markov kernel.

AUDIT VERDICT 2026-07-12 (independent honesty audit, HEAD `845f523a`) [HISTORICAL — the "(3)
Sufficiency: RETRACTED … false-as-framed" finding below applied to the WEAK-only covering event and
is SUPERSEDED by the RESOLVED note at the end of this docstring; the covering event is now the strong
`wzCoveringSuccessStrong`]: PASS, HONEST tier-2 —
mainline target for the next build leg (Session C). (1) Signature honest: body is `sorry`, not
`:= h`; no `:True`/degenerate slot. (2) Non-bundled: the three threaded hyps are preconditions
(`hκ'_pos`/`hκ'_sum` = full-support proper-pmf regularity; `hqStar` = qStar–κ' definitional
consistency), NOT the acceptance conclusion — the core-reconstruction test fails to hand over the
`(u,y)`-typicality; the conditional-AEP (Markov-lemma) concentration stays entirely in the `sorry`.
(3) Sufficiency: RETRACTED (2026-07-12c independent re-audit) — this lemma is UNDER-HYPOTHESIZED
(false-as-framed) under the in-project WEAK (entropy-only) `typicalSet`/`jointlyTypicalSet`, whose
membership is the single scalar `|(∑ −log-mass)/n − H| < ε`, NOT a per-symbol type pin. The three
hyps pin qStar's U-marginal (killing the constant-word `c ≡ u₀ⁿ` case: `δ_{u₀}` fails the U-marginal
ENTROPY condition, empirical U-entropy 0 ≠ H(P_U) = log 2) but do NOT pin the empirical joint
conditional type in TOTAL VARIATION. LABEL-SWAP COUNTEREXAMPLE (independently recomputed 2026-07-12c):
α'=β={0,1}, k=2, P_X=(½,½), P(y|x)=BSC(0.9), full-support κ'(·|0)=(0.9,0.1)/κ'(·|1)=(0.1,0.9),
qStar(x,u)=κ'(x)(u)·P_X(x). Adversary picks M=2ⁿ, an injective encoder, and a decoder realizing
u=g(x-block) whose empirical conditional is label-swapped ν(·|0)=(0.1,0.9)/ν(·|1)=(0.9,0.1)
(realizable block-wise: within the x_i=0 coords assign u=1 to 90%/u=0 to 10%, symmetrically for
x_i=1). The swap is an ENTROPY-PRESERVING RELABELING: x-marginal, U-marginal (0.5,0.5) and joint (x,u)
type (same probability multiset {0.45,0.05,0.05,0.45} as qStar) are all preserved, so ALL THREE weak
covering-entropy conditions still pass → Ecov holds (∏P_X-mass→1); Exytyp (an (x,y)-only band) holds
regardless. Yet the (u,y) empirical type ρ_UY=∑ₓ ν(x)(u)P_XY(x,y)={0.09,0.41,0.41,0.09} has
cross-entropy CE(ρ_UY, wsm)≈2.135 nats ≠ H(wsm)≈1.165 nats → (u,y) atypical → Euy holds →
{Ecov ∩ Exytyp ∩ Euy}→1 ≫ tol/8. ROOT CAUSE: Atom C `wz_wsm_negLog_mean_eq_entropy` gives
⟨qStar-consistent-weight, g⟩ = H(wsm) (g(x,u)=∑_y P(y|x)(−log wsm(u,y))) only under the CONSISTENT
weight; weak Ecov pins only the ENTROPY of type_xu, not type_xu in TV, so M(xb)=⟨type_xu, g⟩ is NOT
pinned to H(wsm). The 2026-07-12/07-12b audits examined only the constant-word case and MISSED this
entropy-preserving relabel. (4) Class `plan` CORRECT: the correlated-joint conditional-AEP
UPPER concentration is a from-scratch in-project assembly, not a Mathlib wall — the nearest in-tree
ingredient `conditionalStronglyTypicalSlice_mass_ge` (`ConditionalMethodOfTypes/Mass.lean:1274`) is a
`_mass_ge` LOWER bound on the INDEPENDENT-product Ys law (wrong direction + measure, not a drop-in),
and `conditionalTypicalSlice_card_le` (SlepianWolf) is a slice-cardinality bound, not the SRC-measure
mass concentration. No deprecated tags; slug `wz-binning-covering` is the intended family-wide child.

RESOLVED 2026-07-12 (Proposal A applied, with a RADIUS SEPARATION — the false-statement DEFECT
discussed above is now HISTORICAL): the covering-success event is
`wzCoveringSuccessStrong P_XY κ' qStar c ε` = STRONG joint typicality (`jointStronglyTypicalSet`) at
the SMALLER radius `ε_cov = wzCoveringStrongRadius P_XY κ' ε = ε/(2(1 + C))`, intersected with weak
`jointlyTypicalSet` at radius `ε`. The strong conjunct at `ε_cov` pins the conditional-mean statistic
`M(xb) = ⟨type_xu, g⟩` to within `C·ε_cov < ε/2` of `H(wzSideInfoMarginal)` (gateway
`wz_wsm_negLog_mean_pin_of_stronglyTypical`, amplification constant `C = ∑_{x,u} |g(x,u)|`), so the
`(u,y)` empirical entropy — which concentrates about `M(xb)` within `< ε/2` for large `n` — stays
within `ε` of `H(wsm)`, i.e. NOT in the acceptance-atypical band `Euy`. Strong typicality at the
*same* radius `ε` would be INSUFFICIENT (only `|M − H| ≤ C·ε ≫ ε`, leaving an `O(ε)` partial-relabel
counterexample class open — a scaled-down label swap); the radius separation `ε_cov ≤ ε/(2C)` closes
that class and makes the statement TRUE-as-framed. The weak conjunct at `ε` is retained so the
`U`-typicality plumbing `wz_covering_success_subset_uTypical` keeps working at radius `ε`. The body
stays a genuine `sorry`: the from-scratch correlated-joint conditional-AEP concentration (recipe:
`wz_srcBlock_condMeasure_split` finite-Fubini split → `wz_wsm_negLog_mean_pin_of_stronglyTypical`
mean pin at radius `ε_cov` → `wz_pi_nonuniform_concentration_tendsto` conditional Chebyshev with
deviation `δ = ε/2`), then classified under the plan slug wz-binning-covering, NOT a Mathlib wall.

INDEPENDENT AUDIT 2026-07-12d (reframe commit `d8954711`, honesty-auditor): PASS, tier-2 HONEST —
the defect-tag removal is JUSTIFIED. The radius separation `ε_cov = ε/(2(1 + C))` closes the `O(ε)`
partial-relabel class at the CLASS level, not per-instance: the mean-pin `wz_wsm_negLog_mean_pin_of_type`
gives a UNIVERSAL bound `|M(t) − H| ≤ C·ε_cov` over the ENTIRE `ε_cov`-ball of types (triangle
inequality, valid for every strong-typical block), and `C·ε_cov = (C/(1 + C))·(ε/2) < ε/2` for all
`C ≥ 0`, `ε > 0`. Composed with the conditional-AEP concentration (`δ = ε/2`) via the strict triangle
`< ε/2 + ε/2 = ε`, the `(u,y)` empirical entropy lands strictly inside `typicalSet(wsm)`, i.e. NOT in
`Euy`. The pinned invariant is the per-symbol joint `(x,u)`-type in TV (finer than the entropy the weak
event pinned); the conclusion needs exactly the linear functional `M = ⟨type, g⟩` this TV pin controls,
no finer structure — so coarser-than-needed is repaired. `C = ∑_p |wzCondMeanKernel|` matches the
gateway amplification constant verbatim (same index type). No other counterexample class survives (the
mean-pin bound is universal over the `ε_cov`-ball); degenerate `C = 0` is consistent (`H(wsm) = 0 = M`,
non-vacuous). `ε_cov` is a computed `def` term of `(P_XY, κ', ε)`, NOT a smuggled hypothesis; file
type-checks, chain signatures fixed, headline `wyner_ziv_achievability` untouched.

BUILD 2026-07-12e: this wrapper is now `sorry`-free. Its body discharges the outer reduction
genuinely — Atom-A finite-Fubini split (`wz_srcBlock_condMeasure_split`), the total `x`-block mass
`∑ xb ∏ P_X = 1` (`Fintype.prod_sum` + source-pmf normalisation), and the good/bad `x`-block
dichotomy (bad `xb`: covering-success fails so the slice is empty; good `xb`: consumes the isolated
conditional-AEP kernel). The analytic core is the from-scratch conditional-AEP kernel
`wz_covering_uyBand_condSlice_le` (now CLOSED sorry-free, `e4490dbb`): for a
strong-covering `x`-block the conditional side-info mass of the `(U,Y)`-atypical slice is `≤ tol/8`
(mean-pin `< ε/2` + conditional Chebyshev `δ = ε/2`).

INDEPENDENT AUDIT 2026-07-12 (wrapper sorry-free build `b489d51f`, honesty-auditor): PASS — the
reduction is GENUINE, no hidden circular/vacuous step. Build confirms this wrapper emits NO `sorry`
warning; the SOLE new residual is the isolated kernel (honest split — analytic core pushed to a
kernel that is itself an honest statement, see its docstring audit). The body genuinely: (a) rewrites
via the sorry-free Atom-A Fubini split `wz_srcBlock_condMeasure_split`; (b) normalises total `x`-block
mass to `1` (`Fintype.prod_sum` + `wz_QXY_mem_stdSimplex`); (c) real good/bad dichotomy — good `xb`
(strongly typical) `measureReal_mono`-includes into the kernel's `(U,Y)`-atypical slice and consumes
`hN … xb hgood`, bad `xb` yields an EMPTY slice from `wzCoveringSuccessStrong`'s strong-conjunct
failure (`hgood hyb.1.1.1`); (d) weighted-sums `∑ (∏P_X)·(≤tol/8) ≤ 1·tol/8`.

CLOSURE 2026-07-12 (kernel closed `e4490dbb`): this wrapper and the entire Markov-core chain
(kernel/outer/inner/leaf) are now machine-verified sorryAx-free
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`). The covering atom
`wz_coveringFamily_of_testChannel` (Atom G) was subsequently closed sorry-free as well
(Atom H closure gate, `@audit:ok`), making the headline `wyner_ziv_achievability`
sorryAx-free.

Independent honesty audit 2026-07-13 (Atom H, Markov-core chain core): PASS — `@audit:ok`. Genuine
reduction: obtains the kernel `wz_covering_uyBand_condSlice_le`, applies the Atom-A finite-Fubini
split `wz_srcBlock_condMeasure_split`, normalises the total `x`-block mass to `1`, and dispatches the
good/bad `xb` dichotomy (bad `xb`: `wzCoveringSuccessStrong` strong-conjunct failure empties the
slice; good `xb`: consumes the kernel bound). Body sorry-free, no `:= h`/`:True`/degenerate slot. The
threaded `hκ'_pos`/`hκ'_sum`/`hqStar` are preconditions passed to the kernel, NOT the conclusion — not
load-bearing. The strong-Ecov radius separation `ε_cov = ε/(2(1+C))` documented above closes the
former label-swap false-as-framed class at the CLASS level; a sorry-free, sorryAx-free proof
machine-confirms the implication is TRUE-as-framed. `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (sorryAx-free). -/
private lemma wz_covering_jointBand_markov_core
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (ε : ℝ) (hε : 0 < ε) (tol : ℝ) (htol : 0 < tol)
    (hκ'_pos : ∀ x u, 0 < κ' x u)
    (hκ'_sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (M : ℕ)
        (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)),
        (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              P_XY.real {(p.1.1, p.2)}))).real
          ((wzCoveringSuccessStrong P_XY κ' qStar c ε
            ∩ typicalSet (rdAmbient
                (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
                (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n ε)
            ∩ { p | (fun i ↦ (c.decoder (c.encoder (fun j ↦ (p j).1)) i, (p i).2))
                ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
                    (ChannelCoding.jointSequence ChannelCoding.iidXs
                      (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                        ((ChannelCoding.iidYs i ω :
                            {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))) n ε })
          ≤ tol / 8 := by
  classical
  obtain ⟨N, hN⟩ :=
    wz_covering_uyBand_condSlice_le P_XY κ' qStar hκ'_pos hκ'_sum hqStar ε hε tol htol
  refine ⟨N, fun n hn M c ↦ ?_⟩
  set S : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    (wzCoveringSuccessStrong P_XY κ' qStar c ε
      ∩ typicalSet (rdAmbient
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
          (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n ε)
      ∩ { p | (fun i ↦ (c.decoder (c.encoder (fun j ↦ (p j).1)) i, (p i).2))
          ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
              (ChannelCoding.jointSequence ChannelCoding.iidXs
                (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                  ((ChannelCoding.iidYs i ω :
                      {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))) n ε } with hS_def
  rw [wz_srcBlock_condMeasure_split P_XY S]
  -- The total `x`-block mass is `1` (marginalisation of the source pmf over the `x`-alphabet).
  have hmass : ∑ xb : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}},
      ∏ i, (∑ y : β, P_XY.real {((xb i).1, y)}) = 1 := by
    have hg1 : ∑ x : {x : α // 0 < ∑ y, P_XY.real {(x, y)}},
        (∑ y : β, P_XY.real {(x.1, y)}) = 1 := by
      have hstd := (wz_QXY_mem_stdSimplex P_XY).2
      rwa [Fintype.sum_prod_type] at hstd
    have heq := Fintype.prod_sum
      (fun (_ : Fin n) (x : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) ↦
        ∑ y : β, P_XY.real {(x.1, y)})
    rw [← heq]
    simp only [hg1, Finset.prod_const_one]
  -- Per-`x`-block: the conditional side-info mass of the slice is `≤ tol/8` (good `xb`: the
  -- conditional AEP; bad `xb`: the slice is empty because covering-success fails).
  have hterm : ∀ xb : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}},
      (Measure.pi (fun i ↦ ChannelCoding.pmfToMeasure
          (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}))).real
          {yb | (fun i ↦ (xb i, yb i)) ∈ S} ≤ tol / 8 := by
    intro xb
    haveI hcondprob : IsProbabilityMeasure (Measure.pi (fun i ↦ ChannelCoding.pmfToMeasure
        (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')}))) := by
      haveI : ∀ i, IsProbabilityMeasure (ChannelCoding.pmfToMeasure
          (fun y : β ↦ P_XY.real {((xb i).1, y)} / ∑ y', P_XY.real {((xb i).1, y')})) := by
        intro i
        refine ChannelCoding.pmfToMeasure_isProbabilityMeasure ⟨fun y ↦ ?_, ?_⟩
        · exact div_nonneg measureReal_nonneg (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg)
        · rw [← Finset.sum_div, div_self (xb i).2.ne']
      infer_instance
    by_cases hgood : (fun i ↦ (xb i, c.decoder (c.encoder xb) i)) ∈
        stronglyTypicalSet (rdAmbient qStar)
          (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n
          (wzCoveringStrongRadius P_XY κ' ε)
    · -- Good `xb`: the slice lies in the `(U,Y)`-atypical set, bounded by the conditional AEP.
      refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hN n hn M c xb hgood)
      intro yb hyb
      simp only [hS_def, Set.mem_setOf_eq, Set.mem_inter_iff] at hyb
      exact hyb.2
    · -- Bad `xb`: covering-success fails, so the slice is empty.
      have hempty : {yb : Fin n → β | (fun i ↦ (xb i, yb i)) ∈ S} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro yb hyb
        simp only [Set.mem_setOf_eq, hS_def, wzCoveringSuccessStrong, Set.mem_inter_iff] at hyb
        exact hgood hyb.1.1.1
      rw [hempty, measureReal_empty]
      linarith
  refine (Finset.sum_le_sum (fun xb _ ↦
    mul_le_mul_of_nonneg_left (hterm xb)
      (Finset.prod_nonneg fun i _ ↦ Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg))).trans
    (le_of_eq ?_)
  rw [← Finset.sum_mul, hmass, one_mul]

open ChannelCoding in
/-- **(L4 — THE HARD KERNEL) Joint `(U,Y)`-band concentration.** For `n` large the
source-measure mass of the event {covering-success ∧ the chosen word `U` and the side
information `Y` are jointly `(U,Y)`-atypical} is at most `tol/4`. This is the correlated-joint
conditional-typicality concentration — the Markov lemma. `U = c.decoder (c.encoder x)` is a
function of the whole `x`-block, so `(U_i, Y_i)` is neither iid nor independent; the plain
`aep_chebyshev_bound` (`Rate.lean:108`) does not apply. From-scratch in-project assembly, absent
from Mathlib and the codebase. The consistency + full-support hypotheses (`hκ'_pos`, `hκ'_sum`,
`hqStar`) are mandatory: without them the statement is false-as-framed (a constant-word
counterexample; see the inner-lemma docstring). Left `sorry` — a separate leg builds it.

AUDIT VERDICT 2026-07-12 (independent honesty audit, HEAD `cca95d1c`): PASS, HONEST tier-2.
(1) Signature honest: body is `sorry`, not `:= h`; no `:True`/degenerate slot. (2) Non-bundled:
the three threaded hyps are preconditions (`hκ'_pos`/`hκ'_sum` = full-support proper pmf regularity;
`hqStar` = qStar–κ' definitional consistency), NOT the acceptance conclusion — granting them does
NOT hand over the correlated-joint concentration; the Markov-lemma content stays entirely in the
`sorry`. (3) Sufficiency: RETRACTED (2026-07-12c independent re-audit) — this outer lemma INHERITS the
core's false-as-framed defect. Its body is a genuine reduction (case split + union bound) consuming
`wz_covering_jointBand_markov_core` (whose `sorry` is the core bound) and `wz_covering_xyBand_aep`; it
is NOT `:= h` and NOT bundled — but the conclusion {Ecov ∩ Euy} ≤ tol/4 is derived from a
false-as-framed lemma, so it is itself false-as-framed under the WEAK (entropy-only) typicalSet. The
same LABEL-SWAP COUNTEREXAMPLE (see the core lemma docstring: BSC(0.9), full-support
κ'(·|0)=(0.9,0.1)/(·|1)=(0.1,0.9), adversary injective encoder + label-swap decoder ν=swap(κ')) is an
entropy-preserving relabel: Ecov holds (∏P_X-mass→1, all three weak covering entropies preserved) and
Euy holds ((u,y) empirical type ρ_UY has CE(ρ_UY,wsm)≈2.135 ≠ H(wsm)≈1.165) → {Ecov ∩ Euy}→1 ≫ tol/4.
The three hyps pin qStar's U-marginal (killing the constant-word case) but do NOT pin the empirical
joint conditional type in TV. The 2026-07-12 audit examined only the constant-word case and MISSED the
entropy-preserving relabel.
(4) Class `plan` CORRECT: the correlated-joint conditional-typicality (Markov-lemma) UPPER
concentration is a from-scratch in-project assembly, not a Mathlib wall; the only in-project
ingredient `conditionalStronglyTypicalSlice_mass_ge` (Mass.lean:1274) is a `_mass_ge` LOWER bound on
the INDEPENDENT-product Ys law (wrong direction + measure, not a drop-in).

RESOLVED 2026-07-12 (Proposal A applied — the false-statement DEFECT and the "(3) Sufficiency:
RETRACTED … false-as-framed" finding above are HISTORICAL, applying to the WEAK-only covering event):
the covering-success event is now `wzCoveringSuccessStrong P_XY κ' qStar c ε` (strong
`jointStronglyTypicalSet` ∩ weak `jointlyTypicalSet`), which excludes the entropy-preserving label-swap
counterexample via the strong per-symbol type pin (see the core lemma
`wz_covering_jointBand_markov_core`). This outer reduction (case split + union bound) now consumes the
TRUE-as-framed core bound, so {covering-success ∩ Euy} ≤ tol/4 is true-as-framed. The reduction body
is sorry-free, and the core `wz_covering_jointBand_markov_core` was subsequently closed sorry-free
(`e4490dbb`), so this lemma carries no residual.

Independent honesty audit 2026-07-13 (Atom H, Markov-core chain outer): PASS — `@audit:ok`. Genuine
reduction: obtains `wz_covering_xyBand_aep` (part-1) and the core `wz_covering_jointBand_markov_core`
(part-2), splits `Ecov ∩ Euy ⊆ Exytypᶜ ∪ (Ecov ∩ Exytyp ∩ Euy)` and union-bounds. Body sorry-free,
no `:= h`/`:True`/degenerate slot; the threaded regularity hyps are passed to the core, not the
conclusion. `#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free). -/
private lemma wz_covering_jointBand_concentration
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (ε : ℝ) (hε : 0 < ε) (tol : ℝ) (htol : 0 < tol)
    (hκ'_pos : ∀ x u, 0 < κ' x u)
    (hκ'_sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (M : ℕ)
        (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)),
        (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              P_XY.real {(p.1.1, p.2)}))).real
          (wzCoveringSuccessStrong P_XY κ' qStar c ε
            ∩ { p | (fun i ↦ (c.decoder (c.encoder (fun j ↦ (p j).1)) i, (p i).2))
                ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
                    (ChannelCoding.jointSequence ChannelCoding.iidXs
                      (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                        ((ChannelCoding.iidYs i ω :
                            {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))) n ε })
          ≤ tol / 4 := by
  classical
  obtain ⟨N1, hN1⟩ := wz_covering_xyBand_aep P_XY ε hε tol htol
  obtain ⟨N2, hN2⟩ :=
    wz_covering_jointBand_markov_core P_XY κ' qStar ε hε tol htol hκ'_pos hκ'_sum hqStar
  refine ⟨max N1 N2, fun n hn M c ↦ ?_⟩
  have hn1 : N1 ≤ n := (le_max_left _ _).trans hn
  have hn2 : N2 ≤ n := (le_max_right _ _).trans hn
  have hxy := hN1 n hn1
  have hmk := hN2 n hn2 M c
  haveI hQ_prob : IsProbabilityMeasure (ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure (wz_QXY_mem_stdSimplex P_XY)
  set SRC : Measure (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
    with hSRC_def
  haveI hSRC_prob : IsProbabilityMeasure SRC := by rw [hSRC_def]; infer_instance
  set Ecov : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    wzCoveringSuccessStrong P_XY κ' qStar c ε with hEcov_def
  set Exytyp : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    typicalSet (rdAmbient
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
      (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n ε with hExytyp_def
  set Euy : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    { p | (fun i ↦ (c.decoder (c.encoder (fun j ↦ (p j).1)) i, (p i).2))
        ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.jointSequence ChannelCoding.iidXs
              (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))) n ε }
    with hEuy_def
  -- Case split on the (X,Y)-joint typicality: atypical ↦ part-1, typical ↦ part-2 (Markov core).
  have hincl : Ecov ∩ Euy ⊆ Exytypᶜ ∪ (Ecov ∩ Exytyp ∩ Euy) := by
    rintro p ⟨hcov, huy⟩
    by_cases hxt : p ∈ Exytyp
    · exact Or.inr ⟨⟨hcov, hxt⟩, huy⟩
    · exact Or.inl hxt
  have hunion : SRC.real (Exytypᶜ ∪ (Ecov ∩ Exytyp ∩ Euy))
      ≤ SRC.real Exytypᶜ + SRC.real (Ecov ∩ Exytyp ∩ Euy) := measureReal_union_le _ _
  have hmono : SRC.real (Ecov ∩ Euy) ≤ SRC.real (Exytypᶜ ∪ (Ecov ∩ Exytyp ∩ Euy)) :=
    measureReal_mono hincl (measure_ne_top _ _)
  linarith [hxy, hmk, hunion, hmono]

/-! ## Gateway atom 3 (Leg F) — covering chosen-word side-information acceptance (Markov lemma)

The decisive covering-acceptance (`C2`) leaf of Wyner–Ziv achievability, isolated from the
covering atom `wz_coveringFamily_of_testChannel` (judgment log #8). For the covering `LossyCode`
`c`, the *correlated joint source* mass of the acceptance-failure event
`wzCoveringAcceptFailSet` — the event that the chosen covering word `c.decoder (c.encoder x)` is
NOT jointly typical with the side information `y` (with `(x, y)` drawn from the true joint
`P_XY`, so `x` and `y` are **correlated**) — is small, given only the covering-typicality success
precondition (the chosen word covers the source `x`, an S5a-supplied regularity/precondition on
the constructed code, NOT the acceptance conclusion).

Its analytic core is the **Markov lemma**: if the chosen word `u = c.decoder (c.encoder x)`
typically covers `x` and the source pair `(x, y)` is jointly typical, then `(u, y)` is jointly
typical — so acceptance fails only off the (exp-small) covering-failure ∪ source-atypicality set.
The measure is the *correlated* joint source
`Measure.pi (pmfToMeasure (fun (x', y) ↦ P_XY{(x'.1, y)}))`; crucially the covering word
`c.decoder (c.encoder x)` is a function of the source `x`, so the `u`–`y` correlation that makes
acceptance likely is inherited from the `x`–`y` correlation and is **destroyed by fixing `u`
independently**. Gateway-2 `wz_covering_sideInfo_mass_ge` (a *lower* bound on the *independent*
product-`Y`-law slice mass) and the broadcast confusion bound `bc_conditional_slice_prob_le`
(an *upper* bound on a *conditional-product* typical slice, the confusion/wrong-codeword
direction) are on the wrong measure/direction and do not supply this (Leg F verdict). -/

open ChannelCoding in
/-- **(Leg F inner concentration — the Markov-lemma core).** The correlated-joint-source mass
of the event that the chosen covering word `u = c.decoder (c.encoder x)` *typically covers* the
source `x` (jointly typical in the covering ambient `rdAmbient qStar`) yet *fails acceptance*
(`(u, y)` not jointly typical in the side-information ambient) is at most `tol/2` for `n` large.

This is the analytic core isolated from `wz_covering_chosenWord_sideInfo_typical`: the outer lemma
splits the acceptance-failure event along covering success/failure, sends the covering-failure part
to the supplied premise (`≤ tol/2`), and reduces the acceptance-failure-on-covering-success part to
this concentration bound. Unconditional in the covering premise: the intersection with the
covering-success set makes the statement self-contained.

CAVEAT (suspected under-hypothesis — flagged 2026-07-12, pending orchestrator re-audit): the
Markov-concentration truth REQUIRES `qStar` to be the `κ'`-consistent covering joint
`qStar (x', u) = κ' x'.1 u · (∑ y, P_XY{(x'.1, y)})` with `κ'` full-support
(`0 < κ' x u`, `∑ u κ' x u = 1`) — exactly the relations the covering atom
`wz_coveringFamily_of_testChannel` exports at its output but which the current signature (shared
with the outer leaf) does NOT thread (`qStar`, `κ'` are free, unrelated params). Without them the
statement is false-as-framed: for a constant-word code `c ≡ u₀` and the free choice
`qStar := P_X ⊗ δ_{u₀}`, covering-success has mass → 1 (premise holds) yet, for generic `κ'` with
`−log P_U(u₀) ≠ H(P_U)`, `u₀` is not `P_U`-typical so acceptance fails on the whole space
(mass → 1 > tol/2). The consistency relation kills this counterexample (it forces `qStar`'s
`U`-marginal `= P_U`, so a mismatched-`U`-marginal code fails covering-success). The fix is a
precondition-exposure (add the `qStar`–`κ'` consistency + full-support hypotheses, discharged by the
covering atom's construction), NOT bundling the acceptance conclusion.

Its body — the correlated-joint conditional-typicality concentration (the Markov lemma), given the
consistency hypotheses — is a from-scratch assembly absent from Mathlib and the codebase (`plan`,
not a Mathlib wall). Left `sorry` pending the signature fix above.

AUDIT VERDICT 2026-07-12b (independent re-audit): the CAVEAT is CONFIRMED. This inner lemma
inherits the SAME false-as-framed defect as the leaf: with free `qStar`/`κ'` its conclusion
(covering-success ∩ acceptance-failure ≤ tol/2) is universally false — the constant-word
`c ≡ u₀ⁿ` + `qStar := P_X ⊗ δ_{u₀}` counterexample (see the leaf docstring) makes covering-success
mass → 1 and, for `−log P_U(u₀) ≠ H(P_U)`, that entire covering-success set lies in
acceptance-failure, so the intersection → 1 > tol/2. Intersecting with covering-success does NOT
save it. REQUIRED FIX = thread the same `qStar`–`κ'` consistency + full-support hypotheses
(owner/planner boundary, deferred this session). RESIDUAL CLASSIFICATION `plan` is CORRECT (once
the signature is fixed): the correlated-joint conditional-typicality (Markov-lemma) concentration
is a from-scratch in-project assembly (loogle/grep 0-hit re-confirmed in-plan), NOT a Mathlib wall;
the only in-project ingredient `conditionalStronglyTypicalSlice_mass_ge` (Mass.lean:1274) is a
lower/independent-product bound.

FIX APPLIED 2026-07-12 — RETRACTED 2026-07-12c (independent re-audit): the "now HONEST tier-2 /
false-as-framed defect resolved" claim is WRONG. Threading the `qStar`–`κ'` consistency + full-support
hypotheses only kills the CONSTANT-WORD counterexample; it does NOT save the statement under the
in-project WEAK (entropy-only) `typicalSet`/`jointlyTypicalSet`. This inner lemma is a genuine
reduction (case split + union bound over the three bands, `Ecov ∩ Euf = ∅` via
`wz_covering_success_subset_uTypical`, then `linarith`) that consumes the OUTER
`wz_covering_jointBand_concentration` bound `hjf` on the joint (u,y)-band `Ecov ∩ Ejf` — which is
itself false-as-framed (root: `wz_covering_jointBand_markov_core`). So this lemma INHERITS the
false-as-framedness. LABEL-SWAP COUNTEREXAMPLE (see the core lemma docstring): the entropy-preserving
relabel keeps covering-success (Ecov mass→1, U-band preserved so `Euf` stays empty) yet drives the
chosen word into `wzCoveringAcceptFailSet` via the joint (u,y)-band (CE(ρ_UY,wsm)≈2.135 ≠
H(wsm)≈1.165) → {Ecov ∩ wzCoveringAcceptFailSet}→1 ≫ tol/2. The consistency hyps satisfy the premises
of the counterexample (they pin qStar's U-marginal only, not type_xu in TV), so it survives them.

RESOLVED 2026-07-12 (Proposal A applied — the false-statement DEFECT and the "AUDIT VERDICT 2026-07-12b
… CONFIRMED false-as-framed" narrative above are HISTORICAL, applying to the WEAK-only covering event):
the covering-success event is now `wzCoveringSuccessStrong P_XY κ' qStar c ε` (strong
`jointStronglyTypicalSet` ∩ weak `jointlyTypicalSet`). The strong conjunct excludes the label-swap
counterexample (its per-symbol joint type differs from `qStar`, see the core lemma), and the weak
conjunct keeps the `Ecov ∩ Euf = ∅` step (`wz_covering_success_subset_uTypical` via
`wzCoveringSuccessStrong_subset_weak`) working at radius `ε`. This inner reduction (De Morgan split +
union bound over the three acceptance bands) now consumes the TRUE-as-framed outer/core bounds, so
{covering-success ∩ acceptance-failure} ≤ tol/2 is true-as-framed. The reduction body is sorry-free,
and the core `wz_covering_jointBand_markov_core` was subsequently closed sorry-free (`e4490dbb`), so
this lemma carries no residual.

Independent honesty audit 2026-07-13 (Atom H, Markov-core chain inner): PASS — `@audit:ok`. Genuine
reduction: obtains `wz_covering_yBand_aep` and the outer `wz_covering_jointBand_concentration`,
De-Morgan-splits `Ecov ∩ acceptFail ⊆ (Ecov ∩ Euf) ∪ Eyf ∪ (Ecov ∩ Ejf)`, uses `Ecov ∩ Euf = ∅`
(via `wz_covering_success_subset_uTypical`) and union-bounds. Body sorry-free, no
`:= h`/`:True`/degenerate slot; threaded regularity hyps passed downstream, not the conclusion.
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free). -/
private lemma wz_covering_markov_concentration
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (ε : ℝ) (hε : 0 < ε) (tol : ℝ) (htol : 0 < tol)
    (hκ'_pos : ∀ x u, 0 < κ' x u)
    (hκ'_sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (M : ℕ)
        (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)),
        (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              P_XY.real {(p.1.1, p.2)}))).real
          (wzCoveringSuccessStrong P_XY κ' qStar c ε
            ∩ wzCoveringAcceptFailSet P_XY κ' c ε)
          ≤ tol / 2 := by
  classical
  obtain ⟨N_Y, hN_Y⟩ := wz_covering_yBand_aep P_XY κ' hκ'_pos hκ'_sum ε hε tol htol
  obtain ⟨N_J, hN_J⟩ :=
    wz_covering_jointBand_concentration P_XY κ' qStar ε hε tol htol hκ'_pos hκ'_sum hqStar
  refine ⟨max N_Y N_J, fun n hn M c ↦ ?_⟩
  have hn_Y : N_Y ≤ n := (le_max_left _ _).trans hn
  have hn_J : N_J ≤ n := (le_max_right _ _).trans hn
  have hyf := hN_Y n hn_Y
  have hjf := hN_J n hn_J M c
  haveI hQ_prob : IsProbabilityMeasure (ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure (wz_QXY_mem_stdSimplex P_XY)
  set SRC : Measure (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
    with hSRC_def
  haveI hSRC_prob : IsProbabilityMeasure SRC := by rw [hSRC_def]; infer_instance
  -- Name the covering-success event and the three band-failure witnesses.
  set Ecov : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    wzCoveringSuccessStrong P_XY κ' qStar c ε with hEcov_def
  set Euf : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    { p | c.decoder (c.encoder (fun j ↦ (p j).1))
        ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ')) ChannelCoding.iidXs n ε }
    with hEuf_def
  set Eyf : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    { p | (fun i ↦ (p i).2) ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
        (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
          ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) n ε }
    with hEyf_def
  set Ejf : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    { p | (fun i ↦ (c.decoder (c.encoder (fun j ↦ (p j).1)) i, (p i).2))
        ∉ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
            (ChannelCoding.jointSequence ChannelCoding.iidXs
              (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
                ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β))) n ε }
    with hEjf_def
  -- De Morgan: covering-success ∩ acceptance-failure splits along the three bands.
  have hincl : Ecov ∩ wzCoveringAcceptFailSet P_XY κ' c ε
      ⊆ (Ecov ∩ Euf) ∪ Eyf ∪ (Ecov ∩ Ejf) := by
    intro p hp
    obtain ⟨hcov, hfail⟩ := hp
    rw [wzCoveringAcceptFailSet, Set.mem_setOf_eq,
      ChannelCoding.mem_jointlyTypicalSet_iff] at hfail
    by_cases hu : c.decoder (c.encoder (fun j ↦ (p j).1))
        ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ')) ChannelCoding.iidXs n ε
    · by_cases hy : (fun i ↦ (p i).2) ∈ typicalSet (rdAmbient (wzSideInfoMarginal P_XY κ'))
          (fun (i : ℕ) (ω : ℕ → Fin k × {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) ↦
            ((ChannelCoding.iidYs i ω : {y : β // 0 < ∑ x, P_XY.real {(x, y)}}) : β)) n ε
      · exact Or.inr ⟨hcov, fun hjt ↦ hfail ⟨hu, hy, hjt⟩⟩
      · exact Or.inl (Or.inr hy)
    · exact Or.inl (Or.inl ⟨hcov, hu⟩)
  -- The `U`-band-failure part is empty on covering-success (L1).
  have hEmpty : Ecov ∩ Euf = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hcov, huf⟩
    exact huf (wz_covering_success_subset_uTypical P_XY κ' qStar hκ'_pos hκ'_sum hqStar ε n M c
      (wzCoveringSuccessStrong_subset_weak P_XY κ' qStar c ε hcov))
  have h1 : SRC.real (Ecov ∩ Euf) = 0 := by rw [hEmpty, measureReal_empty]
  have hunion1 : SRC.real ((Ecov ∩ Euf) ∪ Eyf ∪ (Ecov ∩ Ejf))
      ≤ SRC.real ((Ecov ∩ Euf) ∪ Eyf) + SRC.real (Ecov ∩ Ejf) := measureReal_union_le _ _
  have hunion2 : SRC.real ((Ecov ∩ Euf) ∪ Eyf)
      ≤ SRC.real (Ecov ∩ Euf) + SRC.real Eyf := measureReal_union_le _ _
  have hmono : SRC.real (Ecov ∩ wzCoveringAcceptFailSet P_XY κ' c ε)
      ≤ SRC.real ((Ecov ∩ Euf) ∪ Eyf ∪ (Ecov ∩ Ejf)) :=
    measureReal_mono hincl (measure_ne_top _ _)
  linarith [hyf, hjf, h1, hunion1, hunion2, hmono]

open ChannelCoding in
/-- **(Leg F gateway atom) Covering chosen-word side-information acceptance (Markov lemma).**
For every tolerance `tol > 0` there is an `N` such that for `n ≥ N` and every covering
`LossyCode` `c` whose chosen words typically cover the source (the S5a-style covering-success
premise, an implication hypothesis), the correlated-joint-source mass of the covering-acceptance
failure `wzCoveringAcceptFailSet P_XY κ' c ε` (the chosen word `c.decoder (c.encoder x)` is not
jointly typical, at radius `ε`, with the side information) is at most `tol`. This is the covering
half `C2` of the Wyner–Ziv error `E2` (`C2 ⊆ E2`), isolated from `wz_coveringFamily_of_testChannel`
to be self-built by the Markov lemma (a correlated-joint conditional-typicality concentration
bound absent from Mathlib and the codebase — `plan`, not a Mathlib wall).

Independent honesty audit 2026-07-12 (Leg F leaf, commit `5d3ecd81`): PASS [OVERTURNED
2026-07-12b — the "Sufficiency confirmed … TRUE-as-framed" claim below is WRONG; see AUDIT
VERDICT at the end of this docstring], tier-2
`@residual`. Non-circular (the premise is the `x`–`u` covering slice in ambient
`rdAmbient qStar`, the conclusion the `u`–`y` acceptance slice in a different ambient —
the Markov bridge is genuinely open, body is `sorry`, not `:= h`). Non-bundled: the
covering-typicality-success premise is a genuine regularity precondition on the constructed
code (S5a-suppliable, a property of the covering `LossyCode`), NOT the acceptance conclusion;
granting it does not hand over the `u`–`y` typicality — the Markov concentration
(covering-`x` typicality + source `(x,y)` typicality ⟹ `(u,y)` typicality) remains the sole
residual. Sufficiency confirmed by degenerate-boundary refutation: the coupled
correlated-joint-source form is TRUE-as-framed because `u = c.decoder (c.encoder x)` is a
function of the source, so under `Measure.pi (pmfToMeasure P_XY{(x'.1,y)})` the empirical
`(u,y)` law → `wzSideInfoMarginal` (acceptance-failure mass → 0) at every fixed `ε` and even
at `I(U;Y)>0`. The proof-pivot-advisor's rejected FIXED-word/INDEPENDENT-product shape
(`Measure.pi (μ.map (Ys 0))`) is FALSE-as-framed at `I(U;Y)>0` (independent empirical
`(u,y)` → `P_U × P_Y ≠ wzSideInfoMarginal`, acceptance-failure mass → 1, violating `≤ tol`);
it survives only at the degenerate `I(U;Y)=0` — so the implementer's override to the coupled
form is justified. Class `plan` correct: the concentration ingredient
`conditionalStronglyTypicalSlice_mass_ge` (`ConditionalMethodOfTypes/Mass.lean:1274`, a
lower/independent bound) exists in-project; the correlated-joint Markov-lemma assembly is
unbuilt in-project, not a Mathlib gap. [At that time the `sorry` still remained — see the final
2026-07-13 audit note below for the current sorry-free verdict.]

SUSPECTED UNDER-HYPOTHESIS (flagged 2026-07-12, implementation of the Markov-lemma leg —
supersedes the "Sufficiency confirmed" claim above, pending orchestrator re-audit): `qStar` and
`κ'` are FREE, unrelated parameters here, but the acceptance conclusion is FALSE-as-framed without
the covering-joint consistency relation `qStar (x', u) = κ' x'.1 u · (∑ y, P_XY{(x'.1, y)})` and the
full-support facts `0 < κ' x u`, `∑ u κ' x u = 1` — exactly the relations the covering atom
`wz_coveringFamily_of_testChannel` exports at its output (L1218-1224) but does NOT thread into this
leaf. Counterexample: a constant-word code `c ≡ u₀` with the free choice `qStar := P_X ⊗ δ_{u₀}`
satisfies the covering-success premise (covering-typicality mass → 1) yet, for generic `κ'` with
`−log P_U(u₀) ≠ H(P_U)` (`P_U := ∑ₓ κ'(x,·)·P_X(x)`), `u₀` is not `P_U`-typical so acceptance fails
on the whole space (mass → 1 > tol). The consistency relation kills the counterexample (`qStar`'s
`U`-marginal `= P_U`, so a mismatched code fails covering-success). The degenerate-boundary check
above only varied the measure coupling (independent vs coupled), not the code/`qStar` adversarially,
so it missed this axis. FIX = precondition-exposure (thread the `qStar`–`κ'` consistency +
full-support hypotheses into this leaf and `wz_covering_markov_concentration`, discharged by the
covering atom's construction; ripple to the single consumer `wz_coveringFamily_of_testChannel`);
this is a signature change reserved for the orchestrator/planner, NOT acceptance-conclusion bundling.

AUDIT VERDICT 2026-07-12b (independent re-audit, commits `9ecffb41`+`e1467fdd`): the
under-hypothesis finding is CONFIRMED — this leaf is FALSE-as-framed with free `qStar`/`κ'`.
Verbatim-reproduced counterexample: `typicalSet` bands the U-empirical-entropy against the
U-marginal of the ambient (`pmfLog`/`entropy` of `μ.map (iidXs/iidYs 0)`). The covering-success
premise measures U against `marginalSnd qStar` (qStar's `Fin k` marginal) whereas the acceptance
conclusion measures U against `marginalFst (wzSideInfoMarginal) = P_U` — decoupled because `qStar`
is a free param (signature demands NO stdSimplex/consistency on it). A constant-word `LossyCode`
`c ≡ u₀ⁿ` (legal, `M=1`) with `qStar := P_X ⊗ δ_{u₀}` makes covering-success mass → 1 (premise ✓,
qStar's U-marginal is `δ_{u₀}`, so `u₀ⁿ` is trivially U-typical there) while, for any `κ'` giving
non-uniform `P_U` with `−log P_U(u₀) ≠ H(P_U)`, `u₀ⁿ` is NOT `P_U`-typical ⟹ acceptance-failure =
whole space (mass 1 > tol), for arbitrarily large `n` ⟹ refutes the `∃ N` for every `N`. The prior
`d2e68b10` PASS is OVERTURNED: it varied only the measure coupling (independent-product vs coupled),
never `qStar`/the code adversarially, so it missed this axis. REQUIRED missing hypotheses (fix): the
`qStar`–`κ'` consistency `qStar (x',u) = κ' x'.1 u · (∑ y, P_XY{(x'.1,y)})` + full-support
(`0 < κ' x u`, `∑ u κ' x u = 1`) — both already exported by the sole (future) consumer
`wz_coveringFamily_of_testChannel` (L1249-1252). Fix assessment: HONEST precondition-exposure (Leg
C.5/C.6/E kind), NOT conclusion-bundling — granting consistency only aligns the two U-marginals
(`marginalSnd qStar = P_U`); the Markov concentration `covering-x-typical ⟹ (u,y)-typical w.h.p.`
stays genuinely open (the residual `sorry` in `wz_covering_markov_concentration`). SUFFICIENT —
under consistency the counterexample's `qStar := P_X⊗δ_{u₀}` forces `P_U = δ_{u₀}`, so
`−log P_U(u₀) = 0 = H(P_U)` and a mismatched constant word instead fails covering-success; no
residual counterexample survives. HEADLINE-SAFE — leaf still unconsumed (private); the fix stays on
this leaf + inner lemma, discharged at the covering atom, and does NOT propagate a
full-support/acceptance hypothesis to `wz_goodCode_exists_of_testChannel` / `wyner_ziv_achievability`.
FIX APPLIED 2026-07-12 — RETRACTED 2026-07-12c (independent re-audit): the "false-as-framed defect
resolved / leaf now HONEST tier-2" claim is WRONG. The threaded `qStar`–`κ'` consistency + full-support
hypotheses kill only the CONSTANT-WORD counterexample; they do NOT rescue the statement under the
in-project WEAK (entropy-only) typicality. This leaf is a genuine reduction (acceptance-failure ⊆
covering-failure ∪ (covering-success ∩ acceptance-failure), first part bounded by the S5a implication
premise `hprem`, second by the inner `wz_covering_markov_concentration` bound `hinner`) — no `:= h`,
no bundling — but `hinner` is false-as-framed, so the leaf INHERITS the defect (root:
`wz_covering_jointBand_markov_core`). Under the LABEL-SWAP COUNTEREXAMPLE (see the core lemma
docstring), the premise `hprem` is satisfiable (covering-failure mass→0 ≤ tol/2) yet the chosen word
lands in `wzCoveringAcceptFailSet` on mass→1 (joint (u,y)-band fails: CE(ρ_UY,wsm)≈2.135 ≠
H(wsm)≈1.165) ≫ tol. The consistency hyps pin qStar's U-marginal only, not the empirical joint type
in TV, so the entropy-preserving relabel survives them. The d2e68b10 PASS remains overturned.

RESOLVED 2026-07-12 (Proposal A applied — the false-statement DEFECT and all "false-as-framed /
LABEL-SWAP" narrative above are HISTORICAL, applying to the WEAK-only covering event): the leaf's
covering premise `hprem` is now the mass of the complement of `wzCoveringSuccessStrong P_XY κ' qStar c ε`
(strong `jointStronglyTypicalSet` ∩ weak `jointlyTypicalSet`), and the inner bound `hinner` it consumes
is TRUE-as-framed under the strong covering event (the strong per-symbol type pin excludes the label
swap; see the core lemma). So the leaf conclusion (acceptance-failure mass ≤ tol) is true-as-framed.
The reduction (acceptance-failure ⊆ covering-failure ∪ (covering-success ∩ acceptance-failure), union
bound) body is sorry-free, and the core `wz_covering_jointBand_markov_core` was subsequently closed
sorry-free (`e4490dbb`), so this lemma carries no residual. The strengthened premise is discharged
w.h.p. by the covering atom `wz_coveringFamily_of_testChannel` supplying strong covering-success
(Atom G, closed sorry-free).

Independent honesty audit 2026-07-13 (Atom H, Markov-core chain leaf): PASS — `@audit:ok`. Genuine
reduction: obtains the inner `wz_covering_markov_concentration`, splits acceptance-failure ⊆
`wzCoveringSuccessStrongᶜ ∪ (wzCoveringSuccessStrong ∩ acceptance-failure)`, bounds the first part by
the covering-success premise `hprem` and the second by the inner bound, union-bounds to `≤ tol`. Body
sorry-free, no `:= h`/`:True`/degenerate slot. The covering-success premise `hprem` is a genuine
precondition on the constructed code (covering-failure mass ≤ tol/2, discharged by Atom G) about a
DIFFERENT event (`x`–`u` covering slice) than the conclusion (`u`–`y` acceptance slice); granting it
does NOT hand over the acceptance bound (that stays in the inner Markov concentration) — not
load-bearing. `#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free). -/
lemma wz_covering_chosenWord_sideInfo_typical
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (ε : ℝ) (hε : 0 < ε) (tol : ℝ) (htol : 0 < tol)
    (hκ'_pos : ∀ x u, 0 < κ' x u)
    (hκ'_sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)}) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (M : ℕ)
        (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)),
        -- covering-typicality success (S5a-supplied premise): off a set of mass `≤ tol/2`,
        -- the chosen covering word `c.decoder (c.encoder x)` is jointly typical with the source
        -- `x` in the covering ambient `rdAmbient qStar`. NOT the acceptance conclusion (different
        -- ambient: covering is the `x`–`u` slice, acceptance the `u`–`y` slice).
        (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              P_XY.real {(p.1.1, p.2)}))).real
          ((wzCoveringSuccessStrong P_XY κ' qStar c ε)ᶜ)
          ≤ tol / 2 →
        (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              P_XY.real {(p.1.1, p.2)}))).real
          (wzCoveringAcceptFailSet P_XY κ' c ε)
          ≤ tol := by
  -- Obtain the threshold `N` from the inner Markov-lemma concentration bound.
  obtain ⟨N, hN⟩ :=
    wz_covering_markov_concentration P_XY κ' qStar ε hε tol htol hκ'_pos hκ'_sum hqStar
  refine ⟨N, fun n hn M c hprem ↦ ?_⟩
  -- The inner concentration: acceptance failure ON covering success has mass `≤ tol/2`.
  have hinner := hN n hn M c
  haveI hQ_prob : IsProbabilityMeasure
      (ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure (wz_QXY_mem_stdSimplex P_XY)
  set SRC : Measure (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β) :=
    Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)}))
    with hSRC_def
  haveI hSRC_prob : IsProbabilityMeasure SRC := by rw [hSRC_def]; infer_instance
  -- Acceptance failure is covered by covering-failure ∪ (covering-success ∩ acceptance failure).
  have hincl : wzCoveringAcceptFailSet P_XY κ' c ε
      ⊆ (wzCoveringSuccessStrong P_XY κ' qStar c ε)ᶜ
          ∪ (wzCoveringSuccessStrong P_XY κ' qStar c ε
              ∩ wzCoveringAcceptFailSet P_XY κ' c ε) := by
    intro p hp
    by_cases hc : p ∈ wzCoveringSuccessStrong P_XY κ' qStar c ε
    · exact Or.inr ⟨hc, hp⟩
    · exact Or.inl hc
  -- Union bound over the covering-failure / covering-success split.
  have hunion : SRC.real (wzCoveringAcceptFailSet P_XY κ' c ε)
      ≤ SRC.real ((wzCoveringSuccessStrong P_XY κ' qStar c ε)ᶜ)
        + SRC.real (wzCoveringSuccessStrong P_XY κ' qStar c ε
              ∩ wzCoveringAcceptFailSet P_XY κ' c ε) :=
    le_trans
      (measureReal_mono hincl
        (measure_union_ne_top (measure_ne_top _ _) (measure_ne_top _ _)))
      (measureReal_union_le _ _)
  -- Covering-failure part `≤ tol/2` (premise); covering-success ∩ acceptance-failure `≤ tol/2`
  -- (inner concentration). Their sum is `≤ tol`.
  linarith [hprem, hinner, hunion]

open ChannelCoding in
/-- **(Atom G — radius bridge.)** Strong joint typicality at the small encoder radius `ε_enc`
implies BOTH conjuncts of the covering-success event: the strong conjunct at the covering radius
`ε_cov` (via `ε_enc ≤ ε_cov` and radius monotonicity) and the weak conjunct at `ε` (via the
strong-to-weak inclusion `stronglyTypicalSet_subset_typicalSet`, whose widening constants are the
three `logSumAbs` bounds). No `T_X` restriction is needed — the bridge is a pure set inclusion.
Independent honesty audit 2026-07-13: PASS — `@audit:ok` (genuine set inclusion, sorry-free; hyps are
radius/regularity preconditions). -/
lemma wz_jointStrongly_mem_coveringSuccessJoint
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)] [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}]
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hmem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    {n : ℕ} (hn : 0 < n) {ε_enc ε_cov ε : ℝ} (hε_enc_nn : 0 ≤ ε_enc)
    (h_le_cov : ε_enc ≤ ε_cov)
    (hX : (Fintype.card (Fin k) : ℝ) * ε_enc
            * logSumAbs (rdAmbient qStar) ChannelCoding.iidXs < ε)
    (hY : (Fintype.card {x : α // 0 < ∑ y, P_XY.real {(x, y)}} : ℝ) * ε_enc
            * logSumAbs (rdAmbient qStar) ChannelCoding.iidYs < ε)
    (hJ : ε_enc * logSumAbs (rdAmbient qStar)
            (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) < ε)
    (x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (u : Fin n → Fin k)
    (hxu : (x, u) ∈ jointStronglyTypicalSet (rdAmbient qStar)
            ChannelCoding.iidXs ChannelCoding.iidYs n ε_enc) :
    (x, u) ∈ jointStronglyTypicalSet (rdAmbient qStar)
        ChannelCoding.iidXs ChannelCoding.iidYs n ε_cov
      ∧ (x, u) ∈ ChannelCoding.jointlyTypicalSet (rdAmbient qStar)
        ChannelCoding.iidXs ChannelCoding.iidYs n ε := by
  classical
  haveI : IsProbabilityMeasure (rdAmbient qStar) := rdAmbient_isProbabilityMeasure qStar hmem
  refine ⟨?_, ?_⟩
  · -- Strong conjunct at the larger radius `ε_cov` (radius monotonicity).
    rw [mem_jointStronglyTypicalSet_iff, mem_stronglyTypicalSet_iff] at hxu ⊢
    exact fun p ↦ le_trans (hxu p) h_le_cov
  · -- Weak conjunct: all three entropy bands via strong-to-weak inclusion.
    rw [ChannelCoding.mem_jointlyTypicalSet_iff]
    have hmarg_X := rdAmbient_map_fst_jointSequence qStar hmem
    have hmarg_Y := rdAmbient_map_snd_jointSequence qStar hmem
    refine ⟨?_, ?_, ?_⟩
    · -- X-band.
      have hXstrong : x ∈ stronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs n
          ((Fintype.card (Fin k) : ℝ) * ε_enc) :=
        jointStronglyTypicalSet_implies_X_stronglyTypical (rdAmbient qStar)
          ChannelCoding.iidXs ChannelCoding.iidYs
          (fun i ↦ ChannelCoding.measurable_iidXs i) (fun i ↦ ChannelCoding.measurable_iidYs i)
          hmarg_X hn hε_enc_nn x u hxu
      exact stronglyTypicalSet_subset_typicalSet (rdAmbient qStar) ChannelCoding.iidXs
        (fun i ↦ ChannelCoding.measurable_iidXs i) hn hX hXstrong
    · -- Y-band.
      have hYstrong : u ∈ stronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidYs n
          ((Fintype.card {x : α // 0 < ∑ y, P_XY.real {(x, y)}} : ℝ) * ε_enc) :=
        jointStronglyTypicalSet_implies_Y_stronglyTypical (rdAmbient qStar)
          ChannelCoding.iidXs ChannelCoding.iidYs
          (fun i ↦ ChannelCoding.measurable_iidXs i) (fun i ↦ ChannelCoding.measurable_iidYs i)
          hmarg_Y hn hε_enc_nn x u hxu
      exact stronglyTypicalSet_subset_typicalSet (rdAmbient qStar) ChannelCoding.iidYs
        (fun i ↦ ChannelCoding.measurable_iidYs i) hn hY hYstrong
    · -- Joint-band.
      have hJstrong : (fun i ↦ (x i, u i)) ∈ stronglyTypicalSet (rdAmbient qStar)
          (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) n ε_enc := hxu
      exact stronglyTypicalSet_subset_typicalSet (rdAmbient qStar)
        (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs)
        (fun i ↦ ChannelCoding.measurable_jointSequence ChannelCoding.iidXs ChannelCoding.iidYs
          ChannelCoding.measurable_iidXs ChannelCoding.measurable_iidYs i) hn hJ hJstrong

open ChannelCoding in
/-- **(Atom G — measure alignment.)** The covering source–side product measure `SRC`
pushes forward under the block `X`-projection `p ↦ (fun j ↦ (p j).1)` to the covering
ambient's block `X`-law `Measure.pi (fun _ ↦ (rdAmbient qStar).map (iidXs 0))`. The
per-coordinate map is `Prod.fst`, so `Measure.pi_map_pi` reduces the claim to the
single-coordinate marginal identity `(pmfToMeasure P_XY').map Prod.fst =
(rdAmbient qStar).map (iidXs 0)`, which holds because both marginals equal `x ↦
∑ y, P_XY(x.1, y)` (using `∑ u, κ' x u = 1` for the `qStar` side).
Independent honesty audit 2026-07-13: PASS — `@audit:ok` (genuine measure alignment via `Measure.pi_map_pi`,
sorry-free; hyps are simplex/sum regularity preconditions). -/
lemma wz_covering_SRC_map_Xproj_eq
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)] [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}]
    (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hqStar_mem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar_eq : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
    (n : ℕ) :
    (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
          P_XY.real {(p.1.1, p.2)}))).map
      (fun p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
        fun j ↦ (p j).1)
    = Measure.pi (fun _ : Fin n ↦
        (rdAmbient qStar).map (ChannelCoding.iidXs 0)) := by
  classical
  have hQmem := wz_QXY_mem_stdSimplex P_XY
  haveI hQprob : IsProbabilityMeasure (ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ P_XY.real {(p.1.1, p.2)})) :=
    ChannelCoding.pmfToMeasure_isProbabilityMeasure hQmem
  haveI : IsProbabilityMeasure (rdAmbient qStar) :=
    rdAmbient_isProbabilityMeasure qStar hqStar_mem
  haveI hmapfst_prob : IsProbabilityMeasure ((ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
        P_XY.real {(p.1.1, p.2)})).map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI hmux_prob : IsProbabilityMeasure ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) :=
    rdAmbient_iidXs_isProbabilityMeasure qStar hqStar_mem
  -- Single-coordinate marginal identity.
  have hmarg : (ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
        P_XY.real {(p.1.1, p.2)})).map Prod.fst
        = (rdAmbient qStar).map (ChannelCoding.iidXs 0) := by
    refine Measure.ext_of_singleton (fun a ↦ ?_)
    have hlhs : ((ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
          P_XY.real {(p.1.1, p.2)})).map Prod.fst).real {a}
          = ∑ y, P_XY.real {(a.1, y)} := by
      rw [pmfToMeasure_map_fst_real_singleton hQmem a]; rfl
    have hrhs : ((rdAmbient qStar).map (ChannelCoding.iidXs 0)).real {a}
          = ∑ y, P_XY.real {(a.1, y)} := by
      rw [rdAmbient_map_iidXs qStar hqStar_mem, pmfToMeasure_map_fst_real_singleton hqStar_mem a]
      simp only [marginalFst]
      calc (∑ u, qStar (a, u))
          = ∑ u, κ' a.1 u * ∑ y, P_XY.real {(a.1, y)} :=
            Finset.sum_congr rfl (fun u _ ↦ hqStar_eq (a, u))
        _ = (∑ u, κ' a.1 u) * ∑ y, P_XY.real {(a.1, y)} := by rw [Finset.sum_mul]
        _ = ∑ y, P_XY.real {(a.1, y)} := by rw [hκ'sum a.1, one_mul]
    have heq_real := hlhs.trans hrhs.symm
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp heq_real
  have key : (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
        P_XY.real {(p.1.1, p.2)}))).map (fun p (j : Fin n) ↦ Prod.fst (p j))
      = Measure.pi (fun _ : Fin n ↦ (ChannelCoding.pmfToMeasure
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
            P_XY.real {(p.1.1, p.2)})).map Prod.fst) :=
    MeasureTheory.Measure.pi_map_pi (fun _ ↦ measurable_fst.aemeasurable)
  calc (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
          P_XY.real {(p.1.1, p.2)}))).map (fun p ↦ fun j ↦ (p j).1)
      = Measure.pi (fun _ : Fin n ↦ (ChannelCoding.pmfToMeasure
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
            P_XY.real {(p.1.1, p.2)})).map Prod.fst) := key
    _ = Measure.pi (fun _ : Fin n ↦ (rdAmbient qStar).map (ChannelCoding.iidXs 0)) := by
        rw [hmarg]

end InformationTheory.Shannon

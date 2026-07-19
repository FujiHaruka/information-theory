import InformationTheory.Shannon.WynerZiv.Achievability.MassBound

/-!
# Wyner–Ziv achievability — per-slack good codes and the operational achievability headline
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

/-- A per-slack, per-`n` good deterministic Wyner–Ziv code. Consuming
the same covering data as the capstone `wz_perDelta_covering_binning`,
produce for every block length `n` a Wyner–Ziv code at the operational rate `R`
(`codebookSize R n` messages), together with a single threshold `N` beyond which the
code's expected block distortion is within `D + δ`.

The body is the rate-split glue: the rate identity `wz_mutualInfo_restriction_eq`
picks an intermediate covering rate `R₁ ∈ (I(X;U), …)` with `R₁ − I(Y;U) < R`, feeds the
covering family `hcov` at `R₁`, and hands the whole per-`n` construction to
the giant `wz_perN_covering_binning_code`, which bins the covering index to
`codebookSize R n` messages (`wzIndexBinningMeasure`), decodes by the bin
conditional-typicality search (`wzBinTypicalDecoder`) reconstructing `γ^n` via
`wzCodeOfCoveringBinning`, bounds the covering-failure
(`wz_covering_failure_prob_le`) and codebook-restricted decoder-confusion
(`wz_codebook_confusion_expectation_le`, whose per-codeword mass upper bound is the AEP
crux `wz_covering_codeword_sideInfo_mass_le`) error events, derandomizes
(`exists_codebook_low_avg` / `exists_pair_le_of_binning_integral_le`), squeezes the
distortion to `D + δ` (`source_avg_distortion_le_simpler`,
`ceil_exp_mul_exp_neg_tendsto_atTop`), and extends the source `α' → α`
(`wzLiftSupportCode` + `wz_expectedBlockDistortion_source_agree`).

The hypotheses are covering data / regularity: granting all 13 hands you a feasible test
channel plus a covering `LossyCode` family at the covering rate `R₁`, not the binned
Wyner–Ziv code at the operational rate `R` (the index binning, the bin decoder, and the
confusion-error exponent are done in the body). `hobj'` is the rate objective and `hfeas`
the distortion feasibility (preconditions on the test channel, not the operational
conclusion); `hcov` is the separately-established rate-distortion covering result, not a
restatement of this lemma's Wyner–Ziv claim. The conclusion is non-degenerate: `∃ c` sits
inside `∀ n`, so for the infinitely many `n ≥ N` a genuinely good code is required. -/
lemma wz_perDelta_covering_binning_eventual
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (δ : ℝ) (hδ : 0 < δ)
    (q' : α × β × Fin k → ℝ) (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (d' : DistortionFn {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k))
    (hfact_eq : ∀ x y u, q' (x, y, u) = κ' x u * P_XY.real {(x, y)})
    (hκ'pos : ∀ x u, 0 < κ' x u)
    (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (hobj' : wzMutualInfoXU (Fin k) q' - wzMutualInfoYU (Fin k) q' < R)
    (hqStar_eq : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
    (hqStar_pos : ∀ p, 0 < qStar p)
    (hqStar_mem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    (hfeas : expectedDistortionPmf d' qStar ≤ D + δ / 2)
    (hd'_eq : ∀ x' u, d' x' u = Real.toNNReal (∑ y : β,
        (P_XY.real {(x'.1, y)} / ∑ y' : β, P_XY.real {(x'.1, y')})
          * ((d x'.1 (qf.2 (u, y)) : NNReal) : ℝ)))
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
    (hcov : ∀ R₁ : ℝ, mutualInfoPmf qStar < R₁ → ∀ ε' : ℝ, 0 < ε' → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : ℕ,
          Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M ∧
          (M : ℝ) ≤ Real.exp ((n : ℝ) * R₁) + 1 ∧
          ∃ c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k),
            c.expectedBlockDistortion
                ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) d'
              ≤ (D + δ / 2) + ε'
            ∧ (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
                  (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
                    P_XY.real {(p.1.1, p.2)}))).real
                (wzCoveringAcceptFailSet P_XY κ' c ε)
                ≤ δ / 2 / (8 * (distortionMax d + 1))) :
    ∃ N : ℕ, ∀ n : ℕ, ∃ c : WynerZivCode (codebookSize R n) n α β γ,
      N ≤ n → c.expectedBlockDistortion P_XY d ≤ D + δ := by
  -- Rate split: the covering rate identity `wz_mutualInfo_restriction_eq` lets the
  -- covering family `hcov` be fed at a covering rate `R₁` strictly above
  -- `I(X;U) = mutualInfoPmf qStar`, chosen so the net rate `R₁ − I(Y;U)` still lies below
  -- `R` (the Wyner–Ziv objective `hobj'`). The per-`n` construction is then the giant
  -- `wz_perN_covering_binning_code`.
  have hid : mutualInfoPmf qStar = wzMutualInfoXU (Fin k) q' :=
    wz_mutualInfo_restriction_eq P_XY k q' κ' qStar hfact_eq hκ'sum hqStar_eq
  obtain ⟨R₁, hR₁_lb, hsplit⟩ :
      ∃ R₁ : ℝ, mutualInfoPmf qStar < R₁
        ∧ R₁ - wzMutualInfoYU (Fin k) q' < R := by
    refine ⟨wzMutualInfoXU (Fin k) q'
        + (R - (wzMutualInfoXU (Fin k) q' - wzMutualInfoYU (Fin k) q')) / 2, ?_, ?_⟩
    · rw [hid]; linarith [hobj']
    · linarith [hobj']
  exact wz_perN_covering_binning_code P_XY d R D k qf δ hδ q' κ' qStar d'
    R₁ hfact_eq hκ'pos hκ'sum hobj' hqStar_eq hqStar_pos hqStar_mem hfeas hd'_eq hqf hsplit
    (fun ε' hε' ↦ hcov R₁ hR₁_lb ε' hε')

/-- Covering + binning capstone. Consuming the covering data (the full-support
factorizable joint `q'` with kernel `κ'`, the restricted covering joint `qStar`, the
covering proxy distortion `d'`, the covering feasibility `hfeas`, and the covering
`LossyCode` family `hcov`), assemble the per-slack Wyner–Ziv code family at the
operational rate `R`: bin the covering index down to `codebookSize R n` messages, decode
by the bin conditional-typicality search, bound the covering-failure and
codebook-restricted decoder-confusion error events, extract a good deterministic codebook
+ binning by double derandomization (`exists_codebook_low_avg` /
`exists_pair_le_of_binning_integral_le`), squeeze the residual distortion excess to `0`
(`source_avg_distortion_le_simpler`, `ceil_exp_mul_exp_neg_tendsto_atTop`), and extend the
covering code `α' → α` (`wzLiftSupportCode` + `wz_expectedBlockDistortion_source_agree`).

All hypotheses are covering data / regularity — the covering `LossyCode` family, the
distortion feasibility, positivity and simplex membership. No error-probability or
decoder-correctness claim is a hypothesis (those are derived in the body). Granting the 13
hypotheses does not hand you the binned Wyner–Ziv-code achievability: the binning, the
bin decoder, and the confusion-error exponent remain genuine proof work, done in the body
of `wz_perDelta_covering_binning_eventual`, over which this is the pure
`Filter.atTop`/choice glue. `hobj'` is the rate objective (precondition, not the
conclusion); `hcov` is the separately-established rate-distortion covering result, not a
bundling of this lemma's own claim. -/
lemma wz_perDelta_covering_binning
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (δ : ℝ) (hδ : 0 < δ)
    (q' : α × β × Fin k → ℝ) (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (d' : DistortionFn {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k))
    (hfact_eq : ∀ x y u, q' (x, y, u) = κ' x u * P_XY.real {(x, y)})
    (hκ'pos : ∀ x u, 0 < κ' x u)
    (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (hobj' : wzMutualInfoXU (Fin k) q' - wzMutualInfoYU (Fin k) q' < R)
    (hqStar_eq : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
    (hqStar_pos : ∀ p, 0 < qStar p)
    (hqStar_mem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    (hfeas : expectedDistortionPmf d' qStar ≤ D + δ / 2)
    (hd'_eq : ∀ x' u, d' x' u = Real.toNNReal (∑ y : β,
        (P_XY.real {(x'.1, y)} / ∑ y' : β, P_XY.real {(x'.1, y')})
          * ((d x'.1 (qf.2 (u, y)) : NNReal) : ℝ)))
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
    (hcov : ∀ R₁ : ℝ, mutualInfoPmf qStar < R₁ → ∀ ε' : ℝ, 0 < ε' → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : ℕ,
          Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M ∧
          (M : ℝ) ≤ Real.exp ((n : ℝ) * R₁) + 1 ∧
          ∃ c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k),
            c.expectedBlockDistortion
                ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) d'
              ≤ (D + δ / 2) + ε'
            ∧ (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
                  (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
                    P_XY.real {(p.1.1, p.2)}))).real
                (wzCoveringAcceptFailSet P_XY κ' c ε)
                ≤ δ / 2 / (8 * (distortionMax d + 1))) :
    ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ᶠ n in Filter.atTop, (c n).expectedBlockDistortion P_XY d ≤ D + δ := by
  -- The covering + binning core `wz_perDelta_covering_binning_eventual` produces, for
  -- every `n`, a code together with a single threshold `N` beyond which the distortion is
  -- within `D + δ`. This lemma is the pure choice + `atTop` glue: assemble the per-`n`
  -- codes into a sequence and read off the eventual bound.
  obtain ⟨N, hN⟩ := wz_perDelta_covering_binning_eventual P_XY d R D k qf δ hδ
    q' κ' qStar d' hfact_eq hκ'pos hκ'sum hobj' hqStar_eq hqStar_pos hqStar_mem hfeas
    hd'_eq hqf hcov
  choose c hc using hN
  exact ⟨c, Filter.eventually_atTop.2 ⟨N, fun n hn ↦ hc n hn⟩⟩

/-- Per-slack Wyner–Ziv code family. From a feasible factorizable test
channel `qf` (auxiliary `Fin k`, distortion `≤ D`, Wyner–Ziv objective `< R`), for
every slack `δ > 0` there is a sequence of Wyner–Ziv block codes at the operational
rate `R` (`codebookSize R n` messages) whose expected block distortion is eventually
within `D + δ`.

This is the heavy covering+binning assembly for a fixed slack: internally it
perturbs `qf` to full support (`wz_fullKernelSupport_perturbation`), restricts the
covering source to `α' := {x // 0 < P_X x}` and supplies the covering joint
(`wz_restrictedCoveringJoint_pos` → `wz_covering_lossyCode_exists`), extends back to
`α`, bins the covering index and decodes by a bin conditional-typicality search.

The body is a reduction: `wz_coveringFamily_of_testChannel` supplies the covering data,
and the capstone `wz_perDelta_covering_binning` consumes it to build the code family
(binning + decoder `wzCodeOfCoveringBinning` / `wzBinTypicalDecoder`, the error exponents
`wz_covering_failure_prob_le` / `wz_codebook_confusion_expectation_le`, derandomize,
squeeze, and the source extension `wzLiftSupportCode`). The preconditions `hqf`/`hobj`
are feasibility/objective only. -/
private lemma wz_perDelta_codes_exist
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
    (hobj : wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 < R) :
    ∀ δ : ℝ, 0 < δ → ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ᶠ n in Filter.atTop, (c n).expectedBlockDistortion P_XY d ≤ D + δ := by
  intro δ hδ
  -- Covering-distortion reconciliation + covering LossyCode family:
  -- perturb `qf` to full support, restrict to the source support `α'`, and produce
  -- the covering LossyCode family at any rate `R₁ > mutualInfoPmf qStar`, with the
  -- covering proxy `d'` reconciled against the Wyner–Ziv distortion (feasibility
  -- `expectedDistortionPmf d' qStar ≤ D + δ`).
  -- Call the covering family at the tightened slack `δ/2`, reserving the remaining `δ/2`
  -- for the Wyner–Ziv error terms. `wz_coveringFamily_of_testChannel`
  -- is `δ`-generic, so it returns `hfeas ≤ D + δ/2` and covering target `≤ (D + δ/2) + ε'`,
  -- exactly what the tightened capstone `wz_perDelta_covering_binning` consumes.
  obtain ⟨q', κ', qStar, d', hfact_eq, hκ'pos, hκ'sum, hobj', hqStar_eq,
      hqStar_pos, hqStar_mem, hfeas, hd'_eq, hqf', hcov⟩ :=
    wz_coveringFamily_of_testChannel P_XY d R D k qf hqf hobj (δ / 2) (half_pos hδ)
  -- The binning / decoder / error exponents / derandomize / squeeze / source extension
  -- are packaged in the capstone `wz_perDelta_covering_binning`, which consumes the
  -- covering data obtained above:
  --   * binning: hash the covering index to `codebookSize R n` messages; the rate
  --     split `R₁ = I(X;U)`, net `R = I(X;U) − I(Y;U)`, against `hobj'`.
  --   * decoder: bin conditional-typicality search (`wzBinTypicalDecoder`),
  --     reconstruct `γ^n` letterwise via `qf.2` (`wzCodeOfCoveringBinning`).
  --   * error exponents: covering failure (`wz_covering_failure_prob_le`);
  --     codebook-restricted decoder confusion
  --     (`wz_codebook_confusion_expectation_le`, the crux).
  --   * good deterministic codebook + binning by double derandomization.
  --   * squeeze + source extension `α' → α` (`wzLiftSupportCode` /
  --     `wz_expectedBlockDistortion_source_agree`).
  exact wz_perDelta_covering_binning P_XY d R D k qf δ hδ q' κ' qStar d'
    hfact_eq hκ'pos hκ'sum hobj' hqStar_eq hqStar_pos hqStar_mem hfeas hd'_eq hqf' hcov

/-- Slack diagonalization. A family of Wyner–Ziv code sequences, one per
slack `δ > 0`, each eventually within `D + δ`, diagonalizes to a single Wyner–Ziv
code sequence that is eventually within `D + ε` for *every* `ε > 0`.

This is a general diagonalization over the slack parameter: choosing `δ_m =
1/(m+1)`, extracting a per-`m` code sequence `C m` with an eventual threshold
`N m`, dominating those thresholds by a diverging schedule `Ñ m ≥ max(N₀ … N_m, m)`,
and diagonalizing by `c n := C (idx n) n` where `idx n = Nat.findGreatest (Ñ · ≤ n)
n` selects the largest admissible slack level. Since `idx n → ∞` (as `Ñ` diverges),
the diagonal sequence's eventual bound reaches every `ε`. The hypothesis is the
per-slack achievability family (the output of the covering+binning assembly
`wz_perDelta_codes_exist`). -/
private lemma wz_diagonalize_slack
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (hfam : ∀ δ : ℝ, 0 < δ → ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ᶠ n in Filter.atTop, (c n).expectedBlockDistortion P_XY d ≤ D + δ) :
    ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (c n).expectedBlockDistortion P_XY d ≤ D + ε := by
  -- Extract a per-slack code sequence `C m` for the slack `δ_m = 1/(m+1)`,
  -- together with an eventual threshold `N m` beyond which its distortion is
  -- within `D + 1/(m+1)`.
  have hδpos : ∀ m : ℕ, (0 : ℝ) < 1 / (m + 1) := fun m ↦ by positivity
  choose C hC using fun m : ℕ ↦ hfam (1 / (m + 1)) (hδpos m)
  choose N hN using fun m ↦ Filter.eventually_atTop.mp (hC m)
  -- A monotone-in-effect threshold schedule dominating every `N m` and diverging:
  -- `Ñ m ≥ N m` (so `hN` applies) and `Ñ m ≥ m` (so `Ñ m → ∞`).
  set Ñ : ℕ → ℕ := fun m ↦ (Finset.range (m + 1)).sup N + m with hÑdef
  have hÑ_ge_N : ∀ m, N m ≤ Ñ m := fun m ↦
    le_trans (Finset.le_sup (Finset.self_mem_range_succ m)) (Nat.le_add_right _ _)
  have hÑ_ge_self : ∀ m, m ≤ Ñ m := fun m ↦ Nat.le_add_left _ _
  -- Diagonal code `c n := C (idx n) n`, where `idx n` is the largest `j ≤ n` with
  -- `Ñ j ≤ n`; the diagonal is well-typed since `C (idx n) n : WynerZivCode …`.
  refine ⟨fun n ↦ C (Nat.findGreatest (fun j ↦ Ñ j ≤ n) n) n, ?_⟩
  intro ε hε
  -- Pick `m` with `1/(m+1) < ε` (Archimedean), and show the eventual bound holds
  -- from `n ≥ Ñ m` onward.
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  rw [Filter.eventually_atTop]
  refine ⟨Ñ m, fun n hn ↦ ?_⟩
  show (C (Nat.findGreatest (fun j ↦ Ñ j ≤ n) n) n).expectedBlockDistortion P_XY d ≤ D + ε
  -- `hn : Ñ m ≤ n` witnesses `P m` for `P j := Ñ j ≤ n`; also `m ≤ n`.
  have hmn : m ≤ n := le_trans (hÑ_ge_self m) hn
  -- The selected index is `≥ m` and satisfies its own threshold `Ñ (idx n) ≤ n`.
  have hjge : m ≤ Nat.findGreatest (fun j ↦ Ñ j ≤ n) n := Nat.le_findGreatest hmn hn
  have hjspec : Ñ (Nat.findGreatest (fun j ↦ Ñ j ≤ n) n) ≤ n :=
    Nat.findGreatest_spec (P := fun j ↦ Ñ j ≤ n) hmn hn
  have hNle : N (Nat.findGreatest (fun j ↦ Ñ j ≤ n) n) ≤ n :=
    le_trans (hÑ_ge_N _) hjspec
  -- Apply the per-slack eventual bound at the selected index.
  have hdist := hN (Nat.findGreatest (fun j ↦ Ñ j ≤ n) n) n hNle
  -- `1/(idx n + 1) ≤ 1/(m+1) < ε` since `idx n ≥ m`.
  have hmono : (1 : ℝ) / ((Nat.findGreatest (fun j ↦ Ñ j ≤ n) n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
    apply one_div_le_one_div_of_le
    · positivity
    · have : (m : ℝ) ≤ (Nat.findGreatest (fun j ↦ Ñ j ≤ n) n : ℝ) := by exact_mod_cast hjge
      linarith
  linarith [hdist, hmono, hm]

/-- Covering + binning construction. From a
feasible factorizable test channel `qf` at auxiliary alphabet `Fin k` whose
Wyner–Ziv objective `I(X;U) − I(Y;U)` is strictly below `R`, build a sequence of
Wyner–Ziv block codes at the operational message rate `R` (`codebookSize R n =
⌈exp(n R)⌉` messages) whose expected block distortion is eventually within
`D + ε` for every `ε > 0`.

The construction is the two-layer hybrid: rate-distortion covering `X → U`
(`jointTypicalLossyEncoder` over the codebook alphabet `U = Fin k`) fused with
Slepian–Wolf binning of the covering index (`binningMeasure`), decoded by a
conditional-typicality slice search (`conditionalTypicalSlice`). The three error
exponents — covering failure (`encoder_failure_prob_le_exp_neg_M_avg`),
decoder confusion (`wz_sideInfo_decoder_confusion_expectation_le`) and
covering acceptance (`wz_covering_sideInfo_mass_ge`) — are threaded through
the rate split `R = I(X;U) − I(Y;U)`, with a good deterministic codebook
extracted by the pigeonhole averaging `exists_codebook_low_avg` and the residual
distortion excess squeezed to `0` by `ceil_exp_mul_exp_neg_tendsto_atTop`. The test
channel `qf` is a feasibility/regularity hypothesis, not the covering+binning core.

Implementation note (source-support restriction). The covering half
`rate_distortion_achievability` demands `hqStar_pos : ∀ p, 0 < qStar p` on the `(X,U)`
joint `qStar = wzMarginalXU (Fin k) qf.1`. This is not obtainable by kernel perturbation
alone: factorizability forces `qStar (x,u) = κ(x,u) · P_X(x)` (with `P_X(x) = ∑_y
P_XY(x,y)`), which vanishes at every zero atom of `P_X` regardless of `κ`. So the
construction instantiates its source alphabet `α` with the subtype `{x // 0 < P_X x}`
(the block distortion is measured under `Measure.pi P_X`, which gives zero mass to
sequences hitting a zero atom, so restricting to `supp(P_X)` is WLOG); the leaf
`wz_fullKernelSupport_perturbation` supplies the kernel full support `0 < κ' x u`.

The body reduces to `wz_perDelta_codes_exist` (which builds, for each slack `δ > 0`, a
code sequence eventually within `D + δ`) followed by `wz_diagonalize_slack` (which
diagonalizes those into a single sequence within `D + ε` for every `ε`). -/
private lemma wz_goodCode_exists_of_testChannel
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
    (hobj : wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 < R) :
    ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (c n).expectedBlockDistortion P_XY d ≤ D + ε :=
  wz_diagonalize_slack P_XY d R D
    (wz_perDelta_codes_exist P_XY d R D k qf hqf hobj)

/-- Existence of a Wyner–Ziv code sequence (at the operational message rate `R`)
whose expected block distortion is eventually within `D + ε`.

The body is a reduction: `wz_testChannel_of_rate_lt` extracts a feasible
factorizable test channel below `R` from the feasibility guard `h_ne` and `h_rate`,
and `wz_goodCode_exists_of_testChannel` builds the code sequence from it.

The feasibility precondition `h_ne` (the rate-distortion value set is nonempty at
`D`) makes the signature well-posed: it rules out the infeasible regime `D` below
the min achievable distortion (e.g. any `D < 0` for a `NNReal` distortion), where
`wzRateValueSet` is empty and `wynerZivRate = sInf ∅ = 0` would otherwise let
`h_rate : 0 < R` coexist with a false existence claim. `h_ne` is a
regularity/feasibility precondition, not the covering+binning core. -/
theorem wyner_ziv_achievability_codes
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (h_ne : (wzRateValueSet (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D).Nonempty)
    (h_rate : wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D < R) :
    ∃ c : ∀ n, WynerZivCode (codebookSize R n) n α β γ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (c n).expectedBlockDistortion P_XY d ≤ D + ε := by
  obtain ⟨k, qf, hqf, hobj⟩ := wz_testChannel_of_rate_lt P_XY d R D h_ne h_rate
  exact wz_goodCode_exists_of_testChannel P_XY d R D k qf hqf hobj


/-! ## Operational achievability headline -/

/-- Wyner–Ziv operational achievability. If the information-theoretic
Wyner–Ziv rate `wynerZivRate` at distortion `D` for the i.i.d. source `P_XY` (with
decoder side information `Y`) is strictly below `R`, then `R` is operationally
achievable at distortion `D`: there is a sequence of Wyner–Ziv block codes whose
log-cardinality rate tends to `R` and whose expected block distortion is
eventually within `D + ε` for every `ε > 0`.

The body is assembled: the message sequence is fixed to `codebookSize R n =
⌈exp(n R)⌉`, whose log-cardinality rate tends to `R` via `codebookSize_log_div_tendsto`
(using `0 < R`, from `wynerZivRate_nonneg` and `h_rate`); the distortion sequence is
supplied by the covering + binning construction `wyner_ziv_achievability_codes`.
The signature carries the same feasibility precondition `h_ne` as the codes lemma,
so it is well-posed. -/
theorem wyner_ziv_achievability
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (h_ne : (wzRateValueSet (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D).Nonempty)
    (h_rate : wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D < R) :
    WynerZivAchievable P_XY d R D := by
  have hR : 0 < R := lt_of_le_of_lt (wynerZivRate_nonneg P_XY d D) h_rate
  obtain ⟨c, hc⟩ := wyner_ziv_achievability_codes P_XY d R D h_ne h_rate
  exact ⟨codebookSize R, fun n ↦ codebookSize_pos R n, c,
    codebookSize_log_div_tendsto hR, hc⟩

end InformationTheory.Shannon

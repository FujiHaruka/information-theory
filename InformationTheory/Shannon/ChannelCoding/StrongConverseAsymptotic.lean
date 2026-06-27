import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.StrongConverse
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import InformationTheory.Shannon.CsiszarProjection
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Channel coding asymptotic strong converse (Wolfowitz)

Builds on the single-shot Verdú-Han lower bound `channelCoding_average_success_le`
(`StrongConverse.lean`) to prove the Wolfowitz strong converse: for a memoryless channel
`W` over finite alphabets, if the rate `log (M n) / n` eventually exceeds `capacity W + δ`,
then the average error probability tends to `1`.

The argument substitutes the i.i.d. reference `Q := q*^n` (with `q*` the capacity-achieving
output) and threshold `n·(C + δ/2)` into the single-shot bound, then drives both the exponential
term and the high-information-density tail term to `0`.

## Main statements

* `klDiv_channel_le_capacity` — the capacity saddle point `D(W(a)‖q*) ≤ capacity W`
  (Phase A, the load-bearing core).
* `mutualInfo_segment_hasDerivAt` — the one-sided directional derivative of `I(p_t; W)`
  along the segment towards the Dirac input `δ_a` (the gateway atom for Phase A).
* `channelCoding_highLLR_tendsto_zero` — the average high-LLR tail mass tends to `0`
  (Phase B; non-i.i.d. Chebyshev concentration).
* `channelCoding_strong_converse_asymptotic` — the Wolfowitz strong converse headline.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Theorem 7.9.1 (strong converse).
* J. Wolfowitz, *Coding Theorems of Information Theory*, Springer, 1978.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory Filter
open InformationTheory.Shannon.CsiszarProjection
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## Phase A self-build: keystone bridge + envelope directional derivative -/

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] [Nonempty β] in
/-- For a Markov channel each fiber `W x` is a probability measure, so its singleton masses
sum to `1` over the finite output alphabet. -/
lemma sum_channel_real_singleton_eq_one (W : Channel α β) [IsMarkovKernel W] (x : α) :
    ∑ b : β, (W x).real {b} = 1 := by
  haveI : IsProbabilityMeasure (W x) := inferInstance
  rw [show (∑ b : β, (W x).real {b}) = ∑ b ∈ (Finset.univ : Finset β), (W x).real {b} from rfl,
    sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

omit [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β] in
/-- Cross-entropy form of `klDivPmf`: for a sub-probability-free pmf `P` (only required
non-negative and summing to `1`) and a full-support pmf `Q`, `klDivPmf P Q` equals the
cross-entropy minus the entropy of `P`. Unlike `klDivPmf_eq_log_diff_sum`, `P` may vanish. -/
lemma klDivPmf_crossEntropy {P Q : β → ℝ}
    (hP_nn : ∀ b, 0 ≤ P b) (hP_sum : ∑ b, P b = 1)
    (hQ_sum : ∑ b, Q b = 1) (hQ_pos : ∀ b, 0 < Q b) :
    klDivPmf P Q
      = (∑ b : β, P b * Real.log (P b)) - ∑ b : β, P b * Real.log (Q b) := by
  unfold klDivPmf
  have hterm : ∀ b : β,
      Q b * klFun (P b / Q b)
        = P b * Real.log (P b) - P b * Real.log (Q b) + (Q b - P b) := by
    intro b
    rcases eq_or_lt_of_le (hP_nn b) with hPb | hPb
    · -- P b = 0
      rw [← hPb, zero_div, klFun_zero]
      simp
    · -- 0 < P b
      have hQb : 0 < Q b := hQ_pos b
      have h_log_div : Real.log (P b / Q b) = Real.log (P b) - Real.log (Q b) :=
        Real.log_div hPb.ne' hQb.ne'
      unfold klFun
      rw [h_log_div]
      field_simp
      ring
  have hsum0 : ∑ b : β, (Q b - P b) = 0 := by
    rw [Finset.sum_sub_distrib, hQ_sum, hP_sum]; ring
  calc ∑ b : β, Q b * klFun (P b / Q b)
      = ∑ b : β, (P b * Real.log (P b) - P b * Real.log (Q b) + (Q b - P b)) := by
        simp_rw [hterm]
    _ = (∑ b : β, (P b * Real.log (P b) - P b * Real.log (Q b))) + ∑ b : β, (Q b - P b) := by
        rw [Finset.sum_add_distrib]
    _ = ((∑ b : β, P b * Real.log (P b)) - ∑ b : β, P b * Real.log (Q b)) + 0 := by
        rw [Finset.sum_sub_distrib, hsum0]
    _ = (∑ b : β, P b * Real.log (P b)) - ∑ b : β, P b * Real.log (Q b) := by ring

omit [DecidableEq α] in
/-- Keystone bridge (`I = H(Y) − H(Y|X)`): for `p ∈ stdSimplex`, the channel mutual information
equals the output entropy minus the weighted conditional entropy of the fibers. -/
lemma mutualInfoOfChannel_toReal_eq_outputEntropy_sub
    [Nonempty α] {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (W : Channel α β) [IsMarkovKernel W] :
    (mutualInfoOfChannel (pmfToMeasure p) W).toReal
      = (∑ b : β, Real.negMulLog (∑ x : α, p x * (W x).real {b}))
        - ∑ x : α, p x * (∑ b : β, Real.negMulLog ((W x).real {b})) := by
  classical
  rw [mutualInfoOfChannel_toReal_eq_of_stdSimplex hp W]
  -- The 3-entropy form is `H(X) + H(Y) − H(X,Y)`; we collapse `H(X) − H(X,Y)` into the
  -- weighted fiber conditional entropy via `negMulLog_mul`.
  rw [Fintype.sum_prod_type
    (f := fun ab : α × β ↦ Real.negMulLog (p ab.1 * (W ab.1).real {ab.2}))]
  -- Per-input identity: negMulLog (p x) − ∑_b negMulLog (p x · W x b) = − p x · ∑_b negMulLog (W x b)
  have hper : ∀ x : α,
      Real.negMulLog (p x) - (∑ b : β, Real.negMulLog (p x * (W x).real {b}))
        = - (p x * ∑ b : β, Real.negMulLog ((W x).real {b})) := by
    intro x
    have hexpand : (∑ b : β, Real.negMulLog (p x * (W x).real {b}))
        = Real.negMulLog (p x) + p x * ∑ b : β, Real.negMulLog ((W x).real {b}) := by
      calc (∑ b : β, Real.negMulLog (p x * (W x).real {b}))
          = ∑ b : β, ((W x).real {b} * Real.negMulLog (p x)
              + p x * Real.negMulLog ((W x).real {b})) := by
            refine Finset.sum_congr rfl (fun b _ ↦ ?_)
            rw [Real.negMulLog_mul]
        _ = (∑ b : β, (W x).real {b}) * Real.negMulLog (p x)
              + p x * ∑ b : β, Real.negMulLog ((W x).real {b}) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
        _ = Real.negMulLog (p x) + p x * ∑ b : β, Real.negMulLog ((W x).real {b}) := by
            rw [sum_channel_real_singleton_eq_one W x, one_mul]
    rw [hexpand]; ring
  -- Combine: H(X) − H(X,Y) = ∑_x [negMulLog (p x) − ∑_b negMulLog (p x · W x b)]
  --                        = − ∑_x p x · ∑_b negMulLog (W x b).
  have hHX_sub : (∑ a : α, Real.negMulLog (p a))
        - (∑ a : α, ∑ b : β, Real.negMulLog (p a * (W a).real {b}))
      = - ∑ x : α, p x * ∑ b : β, Real.negMulLog ((W x).real {b}) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ ↦ hper x)
  -- Final rearrangement.
  have : (∑ a : α, Real.negMulLog (p a))
        + (∑ b : β, Real.negMulLog (∑ a : α, p a * (W a).real {b}))
        - (∑ a : α, ∑ b : β, Real.negMulLog (p a * (W a).real {b}))
      = (∑ b : β, Real.negMulLog (∑ x : α, p x * (W x).real {b}))
        - ∑ x : α, p x * ∑ b : β, Real.negMulLog ((W x).real {b}) := by
    linarith [hHX_sub]
  linarith [this]

/-- Gateway atom (Phase A): the one-sided (right) directional derivative of
`t ↦ I(p_t; W).toReal` at `t = 0` along the segment `p_t := (1 - t) • p + t • δ_a` towards the
Dirac input at `a`, equal to `D(W(a)‖q*) − I(p; W)` (the envelope/Danskin cancellation: the
moving reference `q_{p_t}` contributes nothing because `∑_b (dq/dt)(b) = 0`).

Stated as a `HasDerivWithinAt` over `Set.Ici 0` (right derivative), NOT a two-sided
`HasDerivAt`. The two-sided form is FALSE for boundary achievers: when `p a = 0`, for `t < 0`
the segment leaves the simplex (`p_t a = t < 0`), `pmfToMeasure` clamps the negative coordinate
via `ENNReal.ofReal` to `0`, giving the non-probability measure `(1 - t) • pmfToMeasure p`, so
`I(p_t; W).toReal` no longer follows the smooth simplex functional and develops a corner at `0`
(left derivative ≠ right derivative). Concrete refutation: `α = β = Bool`, `p = δ_false`,
`a = true`, any channel with `W false` full support and `W true ≠ W false`; the right derivative
is `D(W true‖W false) > 0`, but the left branch is the non-probability functional
`t ↦ (klDiv ((1-t) • J) ((1-t)² • (J)) ).toReal` (here the input-deterministic joint `J` equals
the product measure), whose derivative at `0` does not match. The one-sided form is also exactly
what the downstream first-order optimality argument consumes (cf. `csiszar_first_order_condition`,
which uses the `𝓝[>] 0` slope).
@audit:ok -/
theorem mutualInfo_segment_hasDerivAt
    (W : Channel α β) [IsMarkovKernel W]
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (hq_pos : ∀ b : β, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    (a : α) :
    HasDerivWithinAt
      (fun t : ℝ ↦
        (mutualInfoOfChannel (pmfToMeasure ((1 - t) • p + t • Pi.single a 1)) W).toReal)
      (klDivPmf (fun b ↦ (W a).real {b})
          (fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b})
        - (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (Set.Ici 0) 0 := by
  classical
  haveI : Nonempty α := ⟨a⟩
  set e : α → ℝ := Pi.single a (1 : ℝ) with he_def
  -- The explicit output pmf `q_p(b) = ∑_x p(x) W(x)(b)`.
  set qf : β → ℝ := fun b ↦ ∑ x : α, p x * (W x).real {b} with hqf_def
  have hqf_pos : ∀ b : β, 0 < qf b := by
    intro b
    have h := hq_pos b
    rw [outputDistribution_real_singleton_of_stdSimplex hp W b] at h
    exact h
  -- `qf` is itself a pmf.
  have hqf_sum : ∑ b : β, qf b = 1 := by
    have hswap : (∑ b : β, qf b)
        = ∑ x : α, p x * (∑ b : β, (W x).real {b}) := by
      show (∑ b : β, ∑ x : α, p x * (W x).real {b})
          = ∑ x : α, p x * (∑ b : β, (W x).real {b})
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun x _ ↦ (Finset.mul_sum _ _ _).symm)
    rw [hswap]
    simp_rw [sum_channel_real_singleton_eq_one W, mul_one]
    exact hp.2
  -- `e` selects the `a`-coordinate.
  have hsingle : ∀ f : α → ℝ, (∑ x : α, e x * f x) = f a := by
    intro f
    rw [Finset.sum_eq_single a]
    · rw [he_def, Pi.single_eq_same, one_mul]
    · intro x _ hx; rw [he_def, Pi.single_eq_of_ne hx, zero_mul]
    · intro h; exact absurd (Finset.mem_univ a) h
  -- The envelope difference `∑_x (e_x − p_x) W(x)(b) = W(a)(b) − q_p(b)`.
  have hΔ : ∀ b : β, (∑ x : α, (e x - p x) * (W x).real {b})
      = (W a).real {b} - qf b := by
    intro b
    have hsub : (∑ x : α, (e x - p x) * (W x).real {b})
        = (∑ x : α, e x * (W x).real {b}) - (∑ x : α, p x * (W x).real {b}) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ ↦ by ring)
    rw [hsub, hsingle (fun x ↦ (W x).real {b})]
  -- The keystone form applied to the convex segment `p_t := (1−t)•p + t•e`.
  set G : ℝ → ℝ := fun t ↦
    (∑ b : β, Real.negMulLog (∑ x : α, ((1 - t) • p + t • e) x * (W x).real {b}))
      - ∑ x : α, ((1 - t) • p + t • e) x * (∑ b : β, Real.negMulLog ((W x).real {b}))
    with hG_def
  set F : ℝ → ℝ := fun t ↦
    (mutualInfoOfChannel (pmfToMeasure ((1 - t) • p + t • e)) W).toReal with hF_def
  have he_mem : e ∈ stdSimplex ℝ α := single_mem_stdSimplex ℝ a
  have hconv := convex_stdSimplex ℝ α
  have hpt_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((1 - t) • p + t • e) ∈ stdSimplex ℝ α := by
    intro t ht
    exact hconv hp he_mem (by linarith [ht.2]) ht.1 (by ring)
  have hkey : ∀ t ∈ Set.Icc (0 : ℝ) 1, F t = G t := by
    intro t ht
    rw [hF_def, hG_def]
    exact mutualInfoOfChannel_toReal_eq_outputEntropy_sub (hpt_mem t ht) W
  -- Per-coordinate affine derivative.
  have haff : ∀ (x : α) (c : ℝ),
      HasDerivAt (fun t : ℝ ↦ ((1 - t) • p + t • e) x * c) ((e x - p x) * c) 0 := by
    intro x c
    have hpt : (fun t : ℝ ↦ ((1 - t) • p + t • e) x * c)
        = fun t : ℝ ↦ ((1 - t) * p x + t * e x) * c := by
      funext t; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hpt]
    have hA : HasDerivAt (fun t : ℝ ↦ (1 - t) * p x) (-(p x)) 0 := by
      have h0 : HasDerivAt (fun t : ℝ ↦ (1 : ℝ) - t) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
      have := h0.mul_const (p x)
      convert this using 1 <;> first | rfl | ring
    have hB : HasDerivAt (fun t : ℝ ↦ t * e x) (e x) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (e x)
    have hsum : HasDerivAt (fun t : ℝ ↦ (1 - t) * p x + t * e x) (e x - p x) 0 := by
      have h := hA.add hB; convert h using 1 <;> first | rfl | ring
    exact hsum.mul_const c
  -- Inner sum derivative for each output letter.
  have hSb : ∀ b : β,
      HasDerivAt (fun t : ℝ ↦ ∑ x : α, ((1 - t) • p + t • e) x * (W x).real {b})
        (∑ x : α, (e x - p x) * (W x).real {b}) 0 :=
    fun b ↦ HasDerivAt.fun_sum (fun x _ ↦ haff x ((W x).real {b}))
  -- `negMulLog`-composed derivative for each output letter (the moving reference contribution).
  have hcomp : ∀ b : β,
      HasDerivAt (fun t : ℝ ↦
          Real.negMulLog (∑ x : α, ((1 - t) • p + t • e) x * (W x).real {b}))
        ((-Real.log (qf b) - 1) * (∑ x : α, (e x - p x) * (W x).real {b})) 0 := by
    intro b
    have hbase : (∑ x : α, ((1 - (0 : ℝ)) • p + (0 : ℝ) • e) x * (W x).real {b}) = qf b := by
      show (∑ x : α, ((1 - (0 : ℝ)) • p + (0 : ℝ) • e) x * (W x).real {b})
          = ∑ x : α, p x * (W x).real {b}
      refine Finset.sum_congr rfl (fun x _ ↦ ?_)
      congr 1
      simp [Pi.add_apply]
    have hg : HasDerivAt Real.negMulLog (-Real.log (qf b) - 1)
        (∑ x : α, ((1 - (0 : ℝ)) • p + (0 : ℝ) • e) x * (W x).real {b}) := by
      rw [hbase]; exact Real.hasDerivAt_negMulLog (hqf_pos b).ne'
    have hcc := hg.comp (0 : ℝ) (hSb b)
    simpa [Function.comp_def] using hcc
  -- Assemble the two pieces of `G`.
  have hterm1 :
      HasDerivAt (fun t : ℝ ↦
          ∑ b : β, Real.negMulLog (∑ x : α, ((1 - t) • p + t • e) x * (W x).real {b}))
        (∑ b : β, (-Real.log (qf b) - 1) * (∑ x : α, (e x - p x) * (W x).real {b})) 0 :=
    HasDerivAt.fun_sum (fun b _ ↦ hcomp b)
  have hterm2 :
      HasDerivAt (fun t : ℝ ↦
          ∑ x : α, ((1 - t) • p + t • e) x * (∑ b : β, Real.negMulLog ((W x).real {b})))
        (∑ x : α, (e x - p x) * (∑ b : β, Real.negMulLog ((W x).real {b}))) 0 :=
    HasDerivAt.fun_sum (fun x _ ↦ haff x (∑ b : β, Real.negMulLog ((W x).real {b})))
  -- The directional derivative value equals the saddle gap (envelope cancellation).
  have hklqf : klDivPmf (fun b ↦ (W a).real {b}) qf
      = (∑ b : β, (W a).real {b} * Real.log ((W a).real {b}))
        - ∑ b : β, (W a).real {b} * Real.log (qf b) :=
    klDivPmf_crossEntropy (fun b ↦ measureReal_nonneg)
      (sum_channel_real_singleton_eq_one W a) hqf_sum hqf_pos
  have hWalog : (∑ b : β, (W a).real {b} * Real.log ((W a).real {b}))
      = - ∑ b : β, Real.negMulLog ((W a).real {b}) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun b _ ↦ ?_)
    rw [show Real.negMulLog ((W a).real {b}) = -(W a).real {b} * Real.log ((W a).real {b}) from rfl]
    ring
  have hqfneg : (∑ b : β, Real.negMulLog (qf b)) = - ∑ b : β, qf b * Real.log (qf b) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun b _ ↦ ?_)
    rw [show Real.negMulLog (qf b) = -qf b * Real.log (qf b) from rfl]
    ring
  have hI : (mutualInfoOfChannel (pmfToMeasure p) W).toReal
      = (∑ b : β, Real.negMulLog (qf b))
        - ∑ x : α, p x * (∑ b : β, Real.negMulLog ((W x).real {b})) := by
    rw [mutualInfoOfChannel_toReal_eq_outputEntropy_sub hp W]
  have hqref : (fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b}) = qf := by
    funext b; exact outputDistribution_real_singleton_of_stdSimplex hp W b
  have hV1 : (∑ b : β, (-Real.log (qf b) - 1) * (∑ x : α, (e x - p x) * (W x).real {b}))
      = (∑ b : β, qf b * Real.log (qf b)) - (∑ b : β, (W a).real {b} * Real.log (qf b)) := by
    have step1 : (∑ b : β, (-Real.log (qf b) - 1) * (∑ x : α, (e x - p x) * (W x).real {b}))
        = ∑ b : β, (-Real.log (qf b) - 1) * ((W a).real {b} - qf b) := by
      refine Finset.sum_congr rfl (fun b _ ↦ ?_); rw [hΔ b]
    rw [step1]
    have step2 : ∀ b : β, (-Real.log (qf b) - 1) * ((W a).real {b} - qf b)
        = (qf b * Real.log (qf b) - (W a).real {b} * Real.log (qf b))
          + (qf b - (W a).real {b}) := fun b ↦ by ring
    simp_rw [step2]
    have hsum0 : ∑ b : β, (qf b - (W a).real {b}) = 0 := by
      rw [Finset.sum_sub_distrib, hqf_sum, sum_channel_real_singleton_eq_one W a]; ring
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum0, add_zero]
  have hV2 : (∑ x : α, (e x - p x) * (∑ b : β, Real.negMulLog ((W x).real {b})))
      = (∑ b : β, Real.negMulLog ((W a).real {b}))
        - (∑ x : α, p x * (∑ b : β, Real.negMulLog ((W x).real {b}))) := by
    have hsub : (∑ x : α, (e x - p x) * (∑ b : β, Real.negMulLog ((W x).real {b})))
        = (∑ x : α, e x * (∑ b : β, Real.negMulLog ((W x).real {b})))
          - (∑ x : α, p x * (∑ b : β, Real.negMulLog ((W x).real {b}))) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ ↦ by ring)
    rw [hsub, hsingle (fun x ↦ ∑ b : β, Real.negMulLog ((W x).real {b}))]
  have hVD : (∑ b : β, (-Real.log (qf b) - 1) * (∑ x : α, (e x - p x) * (W x).real {b}))
              - (∑ x : α, (e x - p x) * (∑ b : β, Real.negMulLog ((W x).real {b})))
            = klDivPmf (fun b ↦ (W a).real {b})
                (fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b})
              - (mutualInfoOfChannel (pmfToMeasure p) W).toReal := by
    rw [hqref, hklqf, hI, hV1, hV2, hWalog, hqfneg]; ring
  have hG_deriv : HasDerivAt G
      (klDivPmf (fun b ↦ (W a).real {b})
          (fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b})
        - (mutualInfoOfChannel (pmfToMeasure p) W).toReal) 0 := by
    have h0 : HasDerivAt G
        ((∑ b : β, (-Real.log (qf b) - 1) * (∑ x : α, (e x - p x) * (W x).real {b}))
          - (∑ x : α, (e x - p x) * (∑ b : β, Real.negMulLog ((W x).real {b})))) 0 :=
      hterm1.sub hterm2
    rwa [hVD] at h0
  -- Transfer to the genuine mutual-information functional via local agreement on `[0, 1]`.
  have hIcc_mem : Set.Icc (0 : ℝ) 1 ∈ 𝓝[Set.Ici (0 : ℝ)] 0 := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio 1, isOpen_Iio, by norm_num, fun x hx ↦ ⟨hx.2, le_of_lt hx.1⟩⟩
  have hev : F =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0] G :=
    Filter.eventuallyEq_of_mem hIcc_mem (fun t ht ↦ hkey t ht)
  have hx0 : F 0 = G 0 := hkey 0 (by norm_num)
  exact (hG_deriv.hasDerivWithinAt).congr_of_eventuallyEq hev hx0

/-- Capacity saddle point (Phase A, load-bearing self-build): for a capacity-achieving input
`p` with full-support output `q* := outputDistribution (pmfToMeasure p) W`, every input symbol
`a` satisfies `D(W(a)‖q*) ≤ capacity W`. Carved out as a shared lemma for reuse across the
channel-coding converse family.
@audit:ok -/
theorem klDiv_channel_le_capacity
    (W : Channel α β) [IsMarkovKernel W]
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (hp_max : IsMaxOn (fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) p)
    (hq_pos : ∀ b : β, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    (a : α) :
    klDivPmf (fun b ↦ (W a).real {b})
        (fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b})
      ≤ capacity W := by
  classical
  haveI : Nonempty α := ⟨a⟩
  set e : α → ℝ := Pi.single a (1 : ℝ) with he_def
  set F : ℝ → ℝ := fun t ↦
    (mutualInfoOfChannel (pmfToMeasure ((1 - t) • p + t • e)) W).toReal with hF_def
  -- The gateway atom: the right derivative of `F` at `0` is the saddle gap.
  have hderiv : HasDerivWithinAt F
      (klDivPmf (fun b ↦ (W a).real {b})
          (fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b})
        - (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (Set.Ici 0) 0 :=
    mutualInfo_segment_hasDerivAt W hp hq_pos a
  -- `F` has a maximum at `t = 0` along the simplex segment.
  have he_mem : e ∈ stdSimplex ℝ α := single_mem_stdSimplex ℝ a
  have hconv := convex_stdSimplex ℝ α
  have hpt_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((1 - t) • p + t • e) ∈ stdSimplex ℝ α := by
    intro t ht
    exact hconv hp he_mem (by linarith [ht.2]) ht.1 (by ring)
  have hF0 : F 0 = (mutualInfoOfChannel (pmfToMeasure p) W).toReal := by
    show (mutualInfoOfChannel (pmfToMeasure ((1 - (0 : ℝ)) • p + (0 : ℝ) • e)) W).toReal = _
    simp
  have h_max_le : ∀ t ∈ Set.Icc (0 : ℝ) 1, F t ≤ F 0 := by
    intro t ht
    rw [hF0]
    exact hp_max (hpt_mem t ht)
  -- The right-derivative slope is non-positive, so the saddle gap is `≤ 0`.
  have hslope_tendsto : Tendsto (slope F 0)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 (klDivPmf (fun b ↦ (W a).real {b})
            (fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b})
          - (mutualInfoOfChannel (pmfToMeasure p) W).toReal)) := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp hderiv
    rwa [Set.Ici_sdiff_left] at h
  have h_gap_le : klDivPmf (fun b ↦ (W a).real {b})
        (fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b})
      - (mutualInfoOfChannel (pmfToMeasure p) W).toReal ≤ 0 := by
    refine le_of_tendsto hslope_tendsto ?_
    have h_event : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[Set.Ioi (0 : ℝ)] 0 := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio 1, isOpen_Iio, by norm_num, fun x hx ↦ ⟨hx.2, le_of_lt hx.1⟩⟩
    filter_upwards [h_event] with t ht
    rw [slope_def_field]
    have hF_le : F t ≤ F 0 := h_max_le t ⟨le_of_lt ht.1, ht.2⟩
    exact div_nonpos_iff.mpr (Or.inr ⟨by linarith, by linarith [ht.1]⟩)
  -- Hence `D(W(a)‖q*) ≤ I(p; W) ≤ capacity W`.
  have h1 : klDivPmf (fun b ↦ (W a).real {b})
        (fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b})
      ≤ (mutualInfoOfChannel (pmfToMeasure p) W).toReal := by linarith
  have h2 : (mutualInfoOfChannel (pmfToMeasure p) W).toReal ≤ capacity W :=
    le_csSup (capacity_bddAbove W) ⟨p, hp, rfl⟩
  exact le_trans h1 h2

/-! ## Phase B: non-i.i.d. Chebyshev concentration of the information density -/

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] [Nonempty β] in
/-- Singleton masses of a probability measure on the finite output alphabet sum to `1`. -/
lemma sum_prob_real_singleton_eq_one (μ : Measure β) [IsProbabilityMeasure μ] :
    ∑ b : β, μ.real {b} = 1 := by
  rw [show (∑ b : β, μ.real {b}) = ∑ b ∈ (Finset.univ : Finset β), μ.real {b} from rfl,
    sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] [Nonempty β] in
/-- The expectation of the per-letter log-likelihood ratio `log (W a)(·) − log q*(·)` under the
channel fiber `W a` is the discrete KL divergence `D(W a ‖ q*)`. -/
lemma integral_logRatio_eq_klDivPmf
    (W : Channel α β) [IsMarkovKernel W] (a : α) {qf : β → ℝ}
    (hqf_sum : ∑ b, qf b = 1) (hqf_pos : ∀ b, 0 < qf b) :
    ∫ b, (Real.log ((W a).real {b}) - Real.log (qf b)) ∂(W a)
      = klDivPmf (fun b ↦ (W a).real {b}) qf := by
  haveI : IsProbabilityMeasure (W a) := inferInstance
  rw [integral_fintype Integrable.of_finite,
    klDivPmf_crossEntropy (fun b ↦ measureReal_nonneg)
      (sum_channel_real_singleton_eq_one W a) hqf_sum hqf_pos]
  simp only [smul_eq_mul, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- Uniform bound on the per-letter log-likelihood ratio `log (W a)(b) − log q*(b)` across the
finite input/output alphabets; an `n`-independent variance bound for the information density. -/
noncomputable def llrUnifBound (W : Channel α β) (p : α → ℝ) : ℝ :=
  ∑ a : α, ∑ b : β,
    |Real.log ((W a).real {b}) - Real.log ((outputDistribution (pmfToMeasure p) W).real {b})|

/-- Per-codeword Chebyshev bound: for block length `n ≥ 1`, the channel-output mass of the
high-LLR set for codeword `m` is at most `B² / (δ/2)² · (1/n)`, where `B := llrUnifBound W p`
is an `n`-independent uniform bound on the per-letter log-likelihood ratios. Uses the saddle
point `klDiv_channel_le_capacity` for the uniform mean bound. -/
lemma highLLRSet_real_le
    (W : Channel α β) [IsMarkovKernel W] {δ : ℝ} (hδ : 0 < δ)
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (hp_max : IsMaxOn (fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) p)
    (hq_pos : ∀ b : β, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    {n : ℕ} (hn : 0 < n) {M : ℕ} (c : Code M n α β) (m : Fin M) :
    (Measure.pi (fun i ↦ W (c.encoder m i))).real
        (highLLRSet W c
          (Measure.pi (fun _ : Fin n ↦ outputDistribution (pmfToMeasure p) W))
          ((n : ℝ) * (capacity W + δ / 2)) m)
      ≤ (llrUnifBound W p) ^ 2 / (δ / 2) ^ 2 * (1 / (n : ℝ)) := by
  classical
  haveI : ∀ i, IsProbabilityMeasure (W (c.encoder m i)) := fun i ↦ inferInstance
  haveI hPmI : IsProbabilityMeasure (Measure.pi (fun i ↦ W (c.encoder m i))) := inferInstance
  haveI : IsProbabilityMeasure (pmfToMeasure p) := pmfToMeasure_isProbabilityMeasure hp
  haveI : IsProbabilityMeasure (outputDistribution (pmfToMeasure p) W) := inferInstance
  -- Abbreviations.
  set qf : β → ℝ := fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b} with hqf_def
  set L : α → β → ℝ := fun a b ↦ Real.log ((W a).real {b}) - Real.log (qf b) with hL_def
  set B : ℝ := llrUnifBound W p with hB_def
  set Pm : Measure (Fin n → β) := Measure.pi (fun i ↦ W (c.encoder m i)) with hPm_def
  set Q : Measure (Fin n → β) :=
    Measure.pi (fun _ : Fin n ↦ outputDistribution (pmfToMeasure p) W) with hQ_def
  set thr : ℝ := (n : ℝ) * (capacity W + δ / 2) with hthr_def
  set S : (Fin n → β) → ℝ := fun y ↦ ∑ i, L (c.encoder m i) (y i) with hS_def
  set cR : ℝ := (n : ℝ) * (δ / 2) with hcR_def
  haveI : IsProbabilityMeasure Pm := by rw [hPm_def]; infer_instance
  -- Basic pmf facts.
  have hqf_pos : ∀ b, 0 < qf b := hq_pos
  have hqf_sum : ∑ b, qf b = 1 := sum_prob_real_singleton_eq_one _
  have hWa_sum : ∀ a, ∑ b : β, (W a).real {b} = 1 := sum_channel_real_singleton_eq_one W
  have hLB : B = ∑ a : α, ∑ b : β, |L a b| := by
    rw [hB_def]; simp only [llrUnifBound, hL_def, hqf_def]
  have hB_nonneg : 0 ≤ B := by
    rw [hLB]; exact Finset.sum_nonneg (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ abs_nonneg _))
  have hL_bound : ∀ a b, |L a b| ≤ B := by
    intro a b
    rw [hLB]
    calc |L a b| ≤ ∑ b' : β, |L a b'| :=
          Finset.single_le_sum (f := fun b' ↦ |L a b'|) (fun b' _ ↦ abs_nonneg _)
            (Finset.mem_univ b)
      _ ≤ ∑ a' : α, ∑ b' : β, |L a' b'| :=
          Finset.single_le_sum (f := fun a' ↦ ∑ b' : β, |L a' b'|)
            (fun a' _ ↦ Finset.sum_nonneg (fun b' _ ↦ abs_nonneg _)) (Finset.mem_univ a)
  -- (H4) each per-letter ratio is in `L²`.
  have hX_memlp : ∀ i, MemLp (L (c.encoder m i)) 2 (W (c.encoder m i)) := by
    intro i
    have hbound : ∀ b', L (c.encoder m i) b' ∈ Set.Icc (-B) B := by
      intro b'
      rw [Set.mem_Icc]
      have h := hL_bound (c.encoder m i) b'
      rw [abs_le] at h
      exact ⟨h.1, h.2⟩
    exact memLp_of_bounded (Filter.Eventually.of_forall hbound)
      (measurable_of_finite _).aestronglyMeasurable 2
  -- (H4') the information density is in `L²`.
  have hS_memlp : MemLp S 2 Pm := by
    have hSbound : ∀ y, S y ∈ Set.Icc (-((n : ℝ) * B)) ((n : ℝ) * B) := by
      intro y
      rw [Set.mem_Icc]
      have habs : |S y| ≤ (n : ℝ) * B := by
        show |∑ i, L (c.encoder m i) (y i)| ≤ (n : ℝ) * B
        calc |∑ i, L (c.encoder m i) (y i)|
            ≤ ∑ i, |L (c.encoder m i) (y i)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum (fun i _ ↦ hL_bound _ _)
          _ = (n : ℝ) * B := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [abs_le] at habs
      exact ⟨habs.1, habs.2⟩
    exact memLp_of_bounded (Filter.Eventually.of_forall hSbound)
      (measurable_of_finite _).aestronglyMeasurable 2
  -- (H2) the mean of the information density is at most `n·C`.
  have hmean_le : (∫ x, S x ∂Pm) ≤ (n : ℝ) * capacity W := by
    have hint : ∀ i : Fin n, (∫ x, L (c.encoder m i) (x i) ∂Pm)
        = klDivPmf (fun b ↦ (W (c.encoder m i)).real {b}) qf := by
      intro i
      have hmp : MeasurePreserving (Function.eval i) Pm (W (c.encoder m i)) := by
        rw [hPm_def]; exact measurePreserving_eval (fun j ↦ W (c.encoder m j)) i
      have hmarg : (∫ x, L (c.encoder m i) (x i) ∂Pm)
          = ∫ b, L (c.encoder m i) b ∂(W (c.encoder m i)) := by
        rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
          (measurable_of_finite _).aestronglyMeasurable]
      rw [hmarg]
      exact integral_logRatio_eq_klDivPmf W (c.encoder m i) hqf_sum hqf_pos
    have hsum_eq : (∫ x, S x ∂Pm) = ∑ i, ∫ x, L (c.encoder m i) (x i) ∂Pm := by
      show (∫ x, ∑ i, L (c.encoder m i) (x i) ∂Pm) = ∑ i, ∫ x, L (c.encoder m i) (x i) ∂Pm
      exact integral_finsetSum Finset.univ (fun i _ ↦ Integrable.of_finite)
    rw [hsum_eq]
    calc ∑ i, ∫ x, L (c.encoder m i) (x i) ∂Pm
        = ∑ i, klDivPmf (fun b ↦ (W (c.encoder m i)).real {b}) qf :=
          Finset.sum_congr rfl (fun i _ ↦ hint i)
      _ ≤ ∑ _i : Fin n, capacity W :=
          Finset.sum_le_sum
            (fun i _ ↦ klDiv_channel_le_capacity W hp hp_max hq_pos (c.encoder m i))
      _ = (n : ℝ) * capacity W := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- (H3) the variance is at most `n·B²`.
  have hvar_le : variance S Pm ≤ (n : ℝ) * B ^ 2 := by
    have hSeq : S = ∑ i, fun ω ↦ L (c.encoder m i) (ω i) := by
      rw [hS_def]; funext y; rw [Finset.sum_apply]
    have hvar_eq : variance S Pm = ∑ i, variance (L (c.encoder m i)) (W (c.encoder m i)) := by
      rw [hSeq, hPm_def]; exact variance_sum_pi hX_memlp
    have hbi : ∀ i : Fin n, variance (L (c.encoder m i)) (W (c.encoder m i)) ≤ B ^ 2 := by
      intro i
      have hicc : ∀ b', L (c.encoder m i) b' ∈ Set.Icc (-B) B := by
        intro b'
        rw [Set.mem_Icc]
        have h := hL_bound (c.encoder m i) b'
        rw [abs_le] at h
        exact ⟨h.1, h.2⟩
      have hbound := variance_le_sq_of_bounded (μ := W (c.encoder m i))
        (Filter.Eventually.of_forall hicc) (measurable_of_finite _).aemeasurable
      calc variance (L (c.encoder m i)) (W (c.encoder m i)) ≤ ((B - (-B)) / 2) ^ 2 := hbound
        _ = B ^ 2 := by ring
    rw [hvar_eq]
    calc ∑ i, variance (L (c.encoder m i)) (W (c.encoder m i))
        ≤ ∑ _i : Fin n, B ^ 2 := Finset.sum_le_sum (fun i _ ↦ hbi i)
      _ = (n : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- (H1) the high-LLR set forces the information density above the threshold.
  have hincl1 : ∀ y, y ∈ highLLRSet W c Q thr m → thr < S y := by
    intro y hy
    simp only [highLLRSet, Set.mem_setOf_eq] at hy
    have hy' : Real.exp thr * Q.real {y}
        < (Measure.pi (fun i ↦ W (c.encoder m i))).real {y} := hy
    -- factorize both singleton masses into products
    have hPmr : (Measure.pi (fun i ↦ W (c.encoder m i))).real {y}
        = ∏ i, (W (c.encoder m i)).real {y i} := by
      show ((Measure.pi (fun i ↦ W (c.encoder m i))) {y}).toReal = ∏ i, (W (c.encoder m i)).real {y i}
      rw [Measure.pi_singleton, ENNReal.toReal_prod]; rfl
    have hQr : Q.real {y} = ∏ i, qf (y i) := by
      rw [hQ_def]
      show ((Measure.pi (fun _ : Fin n ↦ outputDistribution (pmfToMeasure p) W)) {y}).toReal
          = ∏ i, qf (y i)
      rw [Measure.pi_singleton, ENNReal.toReal_prod]; rfl
    have hexp_pos : 0 < Real.exp thr := Real.exp_pos _
    have hQr_pos : 0 < Q.real {y} := by
      rw [hQr]; exact Finset.prod_pos (fun i _ ↦ hqf_pos (y i))
    have hPmr_pos : 0 < (Measure.pi (fun i ↦ W (c.encoder m i))).real {y} :=
      lt_trans (mul_pos hexp_pos hQr_pos) hy'
    have hWfac_pos : ∀ i, 0 < (W (c.encoder m i)).real {y i} := by
      intro i
      by_contra h
      rw [not_lt] at h
      have hle : (W (c.encoder m i)).real {y i} = 0 := le_antisymm h measureReal_nonneg
      have hz : ∏ j, (W (c.encoder m j)).real {y j} = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hle
      rw [← hPmr] at hz
      linarith [hPmr_pos]
    -- take logs of the strict inequality
    have hloglt : Real.log (Real.exp thr * Q.real {y})
        < Real.log ((Measure.pi (fun i ↦ W (c.encoder m i))).real {y}) :=
      Real.log_lt_log (mul_pos hexp_pos hQr_pos) hy'
    rw [Real.log_mul (ne_of_gt hexp_pos) (ne_of_gt hQr_pos), Real.log_exp, hPmr, hQr,
      Real.log_prod (fun i _ ↦ (hWfac_pos i).ne'),
      Real.log_prod (fun i _ ↦ (hqf_pos (y i)).ne')] at hloglt
    -- conclude `thr < S y`
    have hSeq : S y = ∑ i, (Real.log ((W (c.encoder m i)).real {y i}) - Real.log (qf (y i))) := rfl
    rw [hSeq, Finset.sum_sub_distrib]
    linarith [hloglt]
  -- Chebyshev.
  have hcR_pos : 0 < cR := by rw [hcR_def]; positivity
  have hcheb : Pm {ω | cR ≤ |S ω - ∫ x, S x ∂Pm|}
      ≤ ENNReal.ofReal (variance S Pm / cR ^ 2) :=
    meas_ge_le_variance_div_sq hS_memlp hcR_pos
  have hsub_meas : Pm (highLLRSet W c Q thr m) ≤ ENNReal.ofReal (variance S Pm / cR ^ 2) := by
    refine le_trans (measure_mono fun y hy ↦ ?_) hcheb
    show cR ≤ |S y - ∫ x, S x ∂Pm|
    have h1 : thr < S y := hincl1 y hy
    have hgap : thr - (n : ℝ) * capacity W = cR := by rw [hthr_def, hcR_def]; ring
    have hlt : cR < S y - ∫ x, S x ∂Pm := by linarith [hmean_le, h1, hgap]
    exact le_of_lt (lt_of_lt_of_le hlt (le_abs_self _))
  -- Take real parts and finish the arithmetic.
  rw [measureReal_def]
  have hle1 : (Pm (highLLRSet W c Q thr m)).toReal ≤ variance S Pm / cR ^ 2 := by
    calc (Pm (highLLRSet W c Q thr m)).toReal
        ≤ (ENNReal.ofReal (variance S Pm / cR ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hsub_meas
      _ = variance S Pm / cR ^ 2 :=
          ENNReal.toReal_ofReal (div_nonneg (variance_nonneg S Pm) (by positivity))
  have hfin : variance S Pm / cR ^ 2 ≤ B ^ 2 / (δ / 2) ^ 2 * (1 / (n : ℝ)) := by
    have hnum : variance S Pm ≤ (n : ℝ) * B ^ 2 := hvar_le
    have hcR2_pos : (0 : ℝ) < cR ^ 2 := by positivity
    have step : variance S Pm / cR ^ 2 ≤ (n : ℝ) * B ^ 2 / cR ^ 2 := by gcongr
    have eq2 : (n : ℝ) * B ^ 2 / cR ^ 2 = B ^ 2 / (δ / 2) ^ 2 * (1 / (n : ℝ)) := by
      rw [hcR_def]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hδ2 : (δ / 2 : ℝ) ≠ 0 := (show (0 : ℝ) < δ / 2 by linarith).ne'
      rw [mul_pow]
      field_simp
    linarith [step, eq2.le, eq2.ge]
  exact le_trans hle1 hfin

/-- Phase B: the average high-LLR tail mass vanishes as the block length grows, using the
non-i.i.d. Chebyshev concentration (`meas_ge_le_variance_div_sq` + `variance_sum_pi`) with the
i.i.d. reference `q*^n` and threshold `n·(capacity W + δ/2)`. Depends on the saddle point
`klDiv_channel_le_capacity` for the uniform per-codeword mean bound. -/
theorem channelCoding_highLLR_tendsto_zero
    (W : Channel α β) [IsMarkovKernel W] {δ : ℝ} (hδ : 0 < δ)
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (hp_max : IsMaxOn (fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) p)
    (hq_pos : ∀ b : β, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    (M : ℕ → ℕ) (c : ∀ n, Code (M n) n α β) :
    Tendsto
      (fun n ↦ (1 / (M n : ℝ)) * ∑ m : Fin (M n),
        (Measure.pi (fun i ↦ W ((c n).encoder m i))).real
          (highLLRSet W (c n)
            (Measure.pi (fun _ : Fin n ↦ outputDistribution (pmfToMeasure p) W))
            ((n : ℝ) * (capacity W + δ / 2)) m))
      atTop (𝓝 0) := by
  set S0 : ℕ → ℝ := fun n ↦ (1 / (M n : ℝ)) * ∑ m : Fin (M n),
    (Measure.pi (fun i ↦ W ((c n).encoder m i))).real
      (highLLRSet W (c n)
        (Measure.pi (fun _ : Fin n ↦ outputDistribution (pmfToMeasure p) W))
        ((n : ℝ) * (capacity W + δ / 2)) m) with hS0_def
  set K : ℝ := (llrUnifBound W p) ^ 2 / (δ / 2) ^ 2 with hK_def
  have hK_nonneg : (0 : ℝ) ≤ K := by rw [hK_def]; positivity
  -- The dominating bound `K · (1/n)` tends to `0`.
  have hg : Tendsto (fun n : ℕ ↦ K * (1 / (n : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul K
    simpa using h
  -- Lower squeeze: the average tail mass is nonnegative.
  have hlow : ∀ n : ℕ, 0 ≤ S0 n := by
    intro n
    simp only [hS0_def]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun m _ ↦ measureReal_nonneg))
  -- Upper squeeze: for `n ≥ 1` the average tail mass is at most `K · (1/n)`.
  have hupp : ∀ᶠ n in atTop, S0 n ≤ K * (1 / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < n := hn
    simp only [hS0_def]
    set g : Fin (M n) → ℝ := fun m ↦
      (Measure.pi (fun i ↦ W ((c n).encoder m i))).real
        (highLLRSet W (c n)
          (Measure.pi (fun _ : Fin n ↦ outputDistribution (pmfToMeasure p) W))
          ((n : ℝ) * (capacity W + δ / 2)) m) with hg_def
    have hterm : ∀ m, g m ≤ K * (1 / (n : ℝ)) := by
      intro m
      have hb := highLLRSet_real_le W hδ hp hp_max hq_pos hnpos (c n) m
      rw [← hK_def] at hb
      exact hb
    have hRHS_nn : (0 : ℝ) ≤ K * (1 / (n : ℝ)) := mul_nonneg hK_nonneg (by positivity)
    rcases Nat.eq_zero_or_pos (M n) with hM0 | hMpos
    · haveI : IsEmpty (Fin (M n)) := by rw [hM0]; infer_instance
      rw [Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
      exact hRHS_nn
    · have hsum_le : (∑ m, g m) ≤ ∑ _m : Fin (M n), K * (1 / (n : ℝ)) :=
        Finset.sum_le_sum (fun m _ ↦ hterm m)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum_le
      have h1mnn : (0 : ℝ) ≤ 1 / (M n : ℝ) := by positivity
      have hmn : (M n : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
      calc (1 / (M n : ℝ)) * ∑ m, g m
          ≤ (1 / (M n : ℝ)) * ((M n : ℝ) * (K * (1 / (n : ℝ)))) :=
            mul_le_mul_of_nonneg_left hsum_le h1mnn
        _ = K * (1 / (n : ℝ)) := by rw [one_div, inv_mul_cancel_left₀ hmn]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Filter.Eventually.of_forall hlow) hupp

/-- **Wolfowitz strong converse (asymptotic)**: for a memoryless channel `W` over finite
alphabets, if the rate `log (M n) / n` eventually exceeds `capacity W + δ` (with `δ > 0`), then
the average error probability tends to `1`.

The capacity-achieving input `p` (existing by `exists_capacity_achiever`) is received explicitly
together with the regularity precondition `hq_pos` (full-support output, so the log-likelihood
ratios are well-defined); both are preconditions, not load-bearing hypotheses.
@audit:ok -/
@[entry_point]
theorem channelCoding_strong_converse_asymptotic
    (W : Channel α β) [IsMarkovKernel W]
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (c : ∀ n, Code (M n) n α β)
    {δ : ℝ} (hδ : 0 < δ)
    (p : α → ℝ) (hp : p ∈ stdSimplex ℝ α)
    (hp_max : IsMaxOn (fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) p)
    (hq_pos : ∀ b : β, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    (hrate : ∀ᶠ n in atTop, capacity W + δ ≤ Real.log (M n) / n) :
    Tendsto (fun n ↦ ((c n).averageErrorProb W).toReal) atTop (𝓝 1) := by
  -- Probability-measure instances for the i.i.d. reference `Q := q*^n`.
  haveI hPp : IsProbabilityMeasure (pmfToMeasure p) := pmfToMeasure_isProbabilityMeasure hp
  haveI hqProb : IsProbabilityMeasure (outputDistribution (pmfToMeasure p) W) := inferInstance
  -- (Phase B black box) the average high-LLR tail mass tends to `0`.
  have hT0 := channelCoding_highLLR_tendsto_zero W hδ hp hp_max hq_pos M c
  -- (C-1) the exponential term `exp (n·(C + δ/2)) / M n` tends to `0`.
  have hE0 : Tendsto (fun n : ℕ ↦ Real.exp ((n : ℝ) * (capacity W + δ / 2)) / (M n : ℝ))
      atTop (𝓝 0) := by
    -- The dominating sequence `exp (-n·δ/2)` tends to `0`.
    have hdom : Tendsto (fun n : ℕ ↦ Real.exp (-((n : ℝ) * (δ / 2)))) atTop (𝓝 0) := by
      have htop : Tendsto (fun n : ℕ ↦ (n : ℝ) * (δ / 2)) atTop atTop :=
        Filter.Tendsto.atTop_mul_const (by linarith : (0 : ℝ) < δ / 2)
          tendsto_natCast_atTop_atTop
      exact Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp htop)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdom
      (Filter.Eventually.of_forall (fun n ↦ by positivity)) ?_
    filter_upwards [hrate, eventually_ge_atTop 1] with n hr hn1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hMn_pos : (0 : ℝ) < (M n : ℝ) := by exact_mod_cast hM n
    -- From the rate gap: `(C + δ)·n ≤ log (M n)`.
    have hlog : (capacity W + δ) * (n : ℝ) ≤ Real.log (M n) := (le_div_iff₀ hn_pos).mp hr
    have hrw : Real.exp ((n : ℝ) * (capacity W + δ / 2)) / (M n : ℝ)
        = Real.exp ((n : ℝ) * (capacity W + δ / 2) - Real.log (M n)) := by
      rw [Real.exp_sub, Real.exp_log hMn_pos]
    rw [hrw]
    apply Real.exp_le_exp.mpr
    have h2 : (capacity W + δ) * (n : ℝ)
        = (n : ℝ) * (capacity W + δ / 2) + (n : ℝ) * (δ / 2) := by ring
    linarith [hlog, h2]
  -- The single-shot Verdú-Han bound, specialized to `Q := q*^n` and `threshold := n·(C + δ/2)`.
  have hbase : ∀ n : ℕ, 1 - ((c n).averageErrorProb W).toReal
      ≤ Real.exp ((n : ℝ) * (capacity W + δ / 2)) / (M n : ℝ)
        + (1 / (M n : ℝ)) * ∑ m : Fin (M n),
            (Measure.pi (fun i ↦ W ((c n).encoder m i))).real
              (highLLRSet W (c n)
                (Measure.pi (fun _ : Fin n ↦ outputDistribution (pmfToMeasure p) W))
                ((n : ℝ) * (capacity W + δ / 2)) m) := by
    intro n
    exact channelCoding_average_success_le (hM n) W (c n)
      (Measure.pi (fun _ : Fin n ↦ outputDistribution (pmfToMeasure p) W))
      ((n : ℝ) * (capacity W + δ / 2))
  -- The whole right-hand side tends to `0`.
  have hRHS0 : Tendsto (fun n : ℕ ↦
      Real.exp ((n : ℝ) * (capacity W + δ / 2)) / (M n : ℝ)
        + (1 / (M n : ℝ)) * ∑ m : Fin (M n),
            (Measure.pi (fun i ↦ W ((c n).encoder m i))).real
              (highLLRSet W (c n)
                (Measure.pi (fun _ : Fin n ↦ outputDistribution (pmfToMeasure p) W))
                ((n : ℝ) * (capacity W + δ / 2)) m)) atTop (𝓝 0) := by
    simpa using hE0.add hT0
  -- Lower squeeze: `1 - avgPe ≥ 0` because `avgPe ≤ 1`.
  have hlow : ∀ n : ℕ, 0 ≤ 1 - ((c n).averageErrorProb W).toReal := by
    intro n
    have h := (c n).averageErrorProb_le_one W
    have hle1 : ((c n).averageErrorProb W).toReal ≤ 1 := by
      calc ((c n).averageErrorProb W).toReal
          ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top h
        _ = 1 := ENNReal.toReal_one
    linarith
  -- Squeeze `1 - avgPe → 0`.
  have hsq : Tendsto (fun n : ℕ ↦ 1 - ((c n).averageErrorProb W).toReal) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hRHS0
      (Filter.Eventually.of_forall hlow) (Filter.Eventually.of_forall hbase)
  -- Hence `avgPe → 1`.
  have hgoal : Tendsto (fun n : ℕ ↦ 1 - (1 - ((c n).averageErrorProb W).toReal)) atTop
      (𝓝 (1 - 0)) := tendsto_const_nhds.sub hsq
  simpa using hgoal

end InformationTheory.Shannon.ChannelCoding

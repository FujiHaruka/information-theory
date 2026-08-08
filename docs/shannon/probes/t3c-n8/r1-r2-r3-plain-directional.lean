/-
PROBE — not an in-project asset.  Restores, as a file the compiler can check, the machine
tests that the N8 independent audit ran but left only inside its prose.

(a) What it reproduces:
    * `docs/shannon/bc-t3c-n8-audit.md` §7 row R1 — the hypothesis `0 ≤ t` is not decorative:
      at `t = -1` the inequality is false.
    * the same file §7 row R3 — the hypothesis `hmarkov` is not decorative: without it the
      equality between the two forms of the bound is false.
    * the same file §8 — the algebraic skeleton the auditor rebuilt from the definitions
      alone, which is what made §7 row R2 ("dropping `t ≤ 1` was wrong") fail, together with
      the difference identity quoted in §1.

(b) Source: `docs/shannon/bc-t3c-n8-audit.md`, sections §1, §7 and §8.

(c) Target declarations, all in the section
    `/-! ### A directional combination of the plain right-hand sides -/` of
    `InformationTheory/Shannon/BroadcastChannel/OuterBoundTransport.lean`:
      `plainDirectionalCombination`                              (L953)
      `plainDirectionalBound`                                    (L962)
      `plainDirectionalCombination_le_plainDirectionalBound`      (L975)
      `plainDirectionalBoundCondFree`                            (L1000)
      `plainDirectionalBound_eq_condFree`                        (L1011)
      `plainDirectionalCombination_le_plainDirectionalBoundCondFree` (L1033)

⚠ SCOPE — read this before citing the probe.  What is machine-checked below is algebra over
real variables.  Every information quantity of the real declarations is replaced by a free
real variable, so the probe does *not* refute the real `plainDirectional*` statements over
measure spaces: the step from those declarations down to this algebra is carried by the
transcription in the correspondence table below, which was copied by hand from the definition
bodies.  Machine-checked = the algebra; copied by hand = the fidelity of the transcription.

Correspondence with the definition bodies (copied verbatim from the target file):

  `plainFirstUserBound μ y z w u`  (L871)
    = min (mutualInfoReal μ w y) (mutualInfoReal μ w z) + condMutualInfoReal μ u y w
    ↦ min IWY IWZ + a

  `plainSumRateBound μ x y z w u v`  (L565)
    = min (mutualInfoReal μ w y) (mutualInfoReal μ w z)
        + min (condMutualInfoReal μ v z w + condMutualInfoReal μ x y (fun ω ↦ (w ω, v ω)))
            (condMutualInfoReal μ u y w + condMutualInfoReal μ x z (fun ω ↦ (w ω, u ω)))
    ↦ min IWY IWZ + min b1 (a + c)

  `plainDirectionalCombination μ x y z w u v t`  (L953)
    = (1 - t) * plainFirstUserBound μ y z w u + t * plainSumRateBound μ x y z w u v
    ↦ (1 - t) * (min IWY IWZ + a) + t * (min IWY IWZ + min b1 (a + c))

  `plainDirectionalBound μ x y z w u t`  (L962)
    = mutualInfoReal μ (fun ω ↦ (w ω, u ω)) y
        + t * condMutualInfoReal μ x z (fun ω ↦ (w ω, u ω))
    ↦ IWUY + t * c

  `plainDirectionalBoundCondFree μ x y z w u t`  (L1000)
    = mutualInfoReal μ (fun ω ↦ (w ω, u ω)) y
        + t * (mutualInfoReal μ x z - mutualInfoReal μ (fun ω ↦ (w ω, u ω)) z)
    ↦ IWUY + t * (IXZ - IWUZ)

Dictionary of the real variables:
  IWY  = I(W; Y)              IWZ  = I(W; Z)          a    = I(U; Y | W)
  b1   = I(V; Z | W) + I(X; Y | W, V)   (the first branch of the inner minimum)
  c    = I(X; Z | W, U)       IWUY = I(W, U; Y)       IXZ  = I(X; Z)
  IWUZ = I(W, U; Z)

One substitution is used and is not an assumption: `IWUY = IWY + a`, i.e. the chain rule
`I(W, U; Y) = I(W; Y) + I(U; Y | W)`.  In the real proof it is supplied by
`mutualInfoReal_pair_eq_add` (consumed at L981-983), so `bound` below carries it already and
`boundPair` is the same expression before it.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProbeN8

/-- Transcription of `plainDirectionalCombination`. -/
def combination (IWY IWZ a b1 c t : ℝ) : ℝ :=
  (1 - t) * (min IWY IWZ + a) + t * (min IWY IWZ + min b1 (a + c))

/-- Transcription of `plainDirectionalBound` with `I(W, U; Y)` expanded by the chain rule. -/
def bound (IWY a c t : ℝ) : ℝ :=
  IWY + a + t * c

/-- Transcription of `plainDirectionalBound` with `I(W, U; Y)` left as one variable. -/
def boundPair (IWUY c t : ℝ) : ℝ :=
  IWUY + t * c

/-- Transcription of `plainDirectionalBoundCondFree`. -/
def boundCondFree (IWUY IXZ IWUZ t : ℝ) : ℝ :=
  IWUY + t * (IXZ - IWUZ)

/-! ### §7 R1 — the hypothesis `0 ≤ t` is not decorative -/

/-- The audit's instance: `t = -1`, `I(W; Y) = I(W; Z) = I(U; Y | W) = b1 = 0`,
`I(X; Z | W, U) = 1`.  The audit also names a realization of those values by random
variables (`W`, `U`, `V` constant, `X = Z` a uniform bit, `Y` constant), which this probe
does not check. -/
example : ¬ combination 0 0 0 0 1 (-1) ≤ bound 0 0 1 (-1) := by
  norm_num [combination, bound]

/-- The same as a class rather than an instance: at those values the inequality fails for
every negative weight and every positive conditional tail. -/
example (c t : ℝ) (hc : 0 < c) (ht : t < 0) : ¬ combination 0 0 0 0 c t ≤ bound 0 0 c t := by
  have h2 : min (0 : ℝ) (0 + c) = 0 := min_eq_left (by linarith)
  simp only [combination, bound, min_self, h2, not_le]
  nlinarith

/-! ### §7 R3 — the hypothesis `hmarkov` is not decorative -/

/-- The audit's instance: `t = 1`, `I(X; Z | W, U) = 0`, `I(X; Z) = 0`, `I(W, U; Z) = 1`.
The two forms of the bound then differ for every value of `I(W, U; Y)`.  The audit also names
a realization (`X` constant, `Z = U` a uniform bit, `W` constant), which this probe does not
check. -/
example (IWUY : ℝ) : boundPair IWUY 0 1 ≠ boundCondFree IWUY 0 1 1 := by
  intro heq
  simp only [boundPair, boundCondFree] at heq
  linarith

/-- The same as a class: the two forms agree exactly when the conditional tail and the gap
carry the same weighted value, which is what the Markov hypothesis buys. -/
example (IWUY IXZ IWUZ c t : ℝ) (h : t * c ≠ t * (IXZ - IWUZ)) :
    boundPair IWUY c t ≠ boundCondFree IWUY IXZ IWUZ t := by
  intro heq
  simp only [boundPair, boundCondFree] at heq
  exact h (by linarith)

/-! ### §8 — the skeleton rebuilt from the definitions alone, and §1's difference identity -/

/-- Verbatim from `docs/shannon/bc-t3c-n8-audit.md` §8: nonnegativity of `t` is all the
skeleton needs, so there is no counterexample at `t > 1` to be had, which is how the
refutation attempt of §7 row R2 fell. -/
example (IWY IWZ a b1 c t : ℝ) (ht : 0 ≤ t) :
    (1 - t) * (min IWY IWZ + a) + t * (min IWY IWZ + min b1 (a + c)) ≤ IWY + a + t * c := by
  have h1 : min IWY IWZ ≤ IWY := min_le_left _ _
  have h2 : min b1 (a + c) ≤ a + c := min_le_right _ _
  nlinarith [mul_le_mul_of_nonneg_left h2 ht]

/-- The same statement through the transcriptions, which is the algebraic content of
`plainDirectionalCombination_le_plainDirectionalBound`. -/
example (IWY IWZ a b1 c t : ℝ) (ht : 0 ≤ t) :
    combination IWY IWZ a b1 c t ≤ bound IWY a c t := by
  have h1 : min IWY IWZ ≤ IWY := min_le_left _ _
  have h2 : min b1 (a + c) ≤ a + c := min_le_right _ _
  simp only [combination, bound]
  nlinarith [mul_le_mul_of_nonneg_left h2 ht]

/-- The difference identity quoted in §1: the coefficient of `t` cancels on the common
minimum, so the two remaining terms are nonnegative under `0 ≤ t` alone. -/
example (IWY IWZ a b1 c t : ℝ) :
    bound IWY a c t - combination IWY IWZ a b1 c t
      = (IWY - min IWY IWZ) + t * ((a + c) - min b1 (a + c)) := by
  simp only [combination, bound]
  ring

end ProbeN8

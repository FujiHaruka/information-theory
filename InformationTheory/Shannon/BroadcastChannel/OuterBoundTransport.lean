import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MutualInfoFiniteRange
import InformationTheory.Shannon.CondEntropyMemoryless
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Gateway
import InformationTheory.Shannon.ChannelCoding.ConverseMemoryless

/-!
# Comparing the one- and two-auxiliary-receiver outer bounds of a broadcast channel

Two genie-aided outer bounds for the two-receiver discrete memoryless broadcast channel are
compared constraint by constraint. The first bound hands a single auxiliary receiver output
`J` to the genie and constrains the rate triple `(R₀, R₁, R₂)` through three systems of
auxiliary variables — a plain one `(W, U, V)`, a first enhanced one `(W̃, Ũ, Ṽ)` and a second
enhanced one `(Ŵ, Û, V̂)`. The second bound uses two auxiliary receiver outputs, one per
receiver, and constrains the same triple through two systems.

The right-hand sides of the second bound are recorded here already specialized to the pair of
auxiliary receivers `(const, X)`, where the input itself is handed to the second receiver and
nothing to the first. Under that choice the first system of the two-receiver bound drops out
and each right-hand side collapses to a closed form in the second system alone. The
specialization is taken as a definition; deriving those closed forms from the general shape is
not done here. Besides the substitution itself, some of its steps use the conditional
independence of each system from the receiver outputs given the input, which the bound builds
into its witnesses; the comparisons that need that structure again carry it as an explicit
hypothesis.

The one-auxiliary-receiver bound constrains the sum rate twice over, once through the enhanced
systems together with `J` and once through the plain system alone. Those two right-hand sides
differ by exactly the slack in one of the compatibility conditions the same bound imposes on its
witnesses, so the first of the two constraints follows from the second and never binds.

The auxiliary receiver output can be eliminated altogether from the remaining right-hand sides.
Each of them opens with a minimum of two branches, one reading `J` and one not, and the
compatibility condition at the level of `W` forces the minimum onto the branch that does not; the
conditions at the level of `U` and of `V` then rewrite whatever tail still reads `J` in terms of
the plain system. So `J` survives only in the conditions that say which witnesses the bound
admits, not in the right-hand sides those witnesses produce.

Feeding one and the same system to the plain slot and to both enhanced slots is admissible for
these right-hand sides, none of which mixes the two enhanced systems, and collapses all of them
onto four: the three that are stated through the plain system alone, and the sum-rate one.

Everything below relates right-hand sides of constraints to one another. Turning such a relation
into a statement about the rate regions the two bounds cut out needs the constraints themselves,
and that step is not taken here.

## Main definitions

* `singleAuxCommonBound`, `singleAuxFirstUserBound`, `singleAuxSecondUserBound` — the
  right-hand sides of the one-auxiliary-receiver constraints on `R₀`, on `R₀ + R₁` and on
  `R₀ + R₂` that participate in the comparison.
* `singleAuxFirstUserBoundFromZ` and `singleAuxSecondUserBoundFromZ` — the companion constraints
  on `R₀ + R₁` and on `R₀ + R₂`, whose leading minimum opens at the first enhanced system rather
  than at the second.
* `singleAuxFirstUserBoundJFree`, `singleAuxFirstUserBoundFromZJFree`,
  `singleAuxSecondUserBoundJFree`, `singleAuxSecondUserBoundFromZJFree` — the same four
  right-hand sides written without the auxiliary receiver output.
* `plainCommonBound`, `plainFirstUserBound`, `plainSecondUserBound` — the right-hand sides of the
  one-auxiliary-receiver constraints on `R₀`, on `R₀ + R₁` and on `R₀ + R₂` that are stated
  through the plain system alone.
* `twoAuxCommonBound`, `twoAuxFirstUserBound`, `twoAuxFirstUserBoundInput`,
  `twoAuxSecondUserBound`, `twoAuxSecondUserBoundInput` — the five right-hand sides of the
  two-auxiliary-receiver bound at `(const, X)`. The `Input` suffix marks the two of them whose
  leading term reads the channel input `X` where its partner reads a receiver output.
* `enhancedSumRateBound` and `plainSumRateBound` — the two right-hand sides of the
  one-auxiliary-receiver bound on `R₀ + R₁ + R₂`.
* `secondUserSlack` — the slack in the upper half of the compatibility condition that ties the
  second user's tail in the first enhanced system to the input.

## Main statements

* `singleAuxCommonBound_le_twoAuxCommonBound` — the `R₀` constraint transports.
* `singleAuxFirstUserBound_le_twoAuxFirstUserBound` and
  `twoAuxFirstUserBound_le_twoAuxFirstUserBoundInput` — the two `R₀ + R₁` constraints.
* `singleAuxSecondUserBound_le_twoAuxSecondUserBound` and
  `twoAuxSecondUserBound_le_twoAuxSecondUserBoundInput` — the two `R₀ + R₂` constraints,
  the first of them at the single instance `J := X` of the auxiliary receiver.
* `condMutualInfoReal_sub_eq_condMutualInfoReal_prod` — the closed form
  `I(Ṽ; X | W̃) - I(Ṽ; Z | W̃) = I(Ṽ; X | W̃, Z)` of the tail that the `R₀ + R₂` comparison
  discards.
* `enhancedSumRateBound_sub_plainSumRateBound_eq_secondUserSlack` — the two sum-rate right-hand
  sides differ by `secondUserSlack`.
* `plainSumRateBound_le_enhancedSumRateBound` and
  `le_enhancedSumRateBound_of_le_plainSumRateBound` — the resulting order and the redundancy of
  the sum-rate constraint that carries `J`.
* `singleAuxFirstUserBound_eq_jFree`, `singleAuxFirstUserBoundFromZ_eq_jFree`,
  `singleAuxSecondUserBound_eq_jFree` and `singleAuxSecondUserBoundFromZ_eq_jFree` — the four
  right-hand sides that read the auxiliary receiver output equal ones that do not.
* `singleAuxCommonBound_diagonal_eq_plainCommonBound`,
  `singleAuxFirstUserBound_diagonal_eq_plainFirstUserBound`,
  `singleAuxFirstUserBoundFromZ_diagonal_eq_plainFirstUserBound`,
  `singleAuxSecondUserBound_diagonal_eq_plainSecondUserBound` and
  `singleAuxSecondUserBoundFromZ_diagonal_eq_plainSecondUserBound` — feeding one system to all
  three slots collapses five of the constraints onto the three stated through the plain system
  alone, whatever the auxiliary receiver output is.

None of the five comparisons uses the compatibility conditions tying the three systems of the
one-auxiliary-receiver bound together; the chain rule and the data processing inequality
suffice. The sum-rate identity is the opposite case: two of those conditions enter it, together
with a third that equates the two branches of the inner minimum of `plainSumRateBound`, and each
is carried as an explicit hypothesis.

## Implementation notes

The constraints mix mutual informations additively and subtractively, so they are stated over
`ℝ` rather than over `ℝ≥0∞`. Since `(⊤ : ℝ≥0∞).toReal = 0`, an infinite mutual information
would silently satisfy an inequality it violates; every bridge to the `ℝ≥0∞`-valued chain rule
therefore goes through an explicit finiteness fact, which the finite alphabets supply.

Every random variable is an explicit binder rather than a section variable: the alphabets are
free type variables, so auto-bound implicits would let a permuted application elaborate into a
different statement.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal

section RealValued

variable {Ω : Type*} [MeasurableSpace Ω]
variable {S T R : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace R]

/-- The mutual information `I(f; g)` as a real number, that is `(mutualInfo μ f g).toReal`. -/
noncomputable def mutualInfoReal (μ : Measure Ω) (f : Ω → S) (g : Ω → T) : ℝ :=
  (mutualInfo μ f g).toReal

/-- The conditional mutual information `I(f; g | h)` as a real number, that is
`(condMutualInfo μ f g h).toReal`. -/
noncomputable def condMutualInfoReal (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace S] [Nonempty S] [StandardBorelSpace T] [Nonempty T]
    (f : Ω → S) (g : Ω → T) (h : Ω → R) : ℝ :=
  (condMutualInfo μ f g h).toReal

end RealValued

section Bridges

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [StandardBorelSpace S] [Nonempty S]
variable {T : Type*} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [StandardBorelSpace T] [Nonempty T]
variable {R : Type*} [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [StandardBorelSpace R] [Nonempty R]

private lemma isMarkovChain_map_right (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S' : Type*} [MeasurableSpace S'] [StandardBorelSpace S'] [Nonempty S']
    (Xs : Ω → S) (Zc : Ω → R) (Yo : Ω → T)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    {f : T → S'} (hf : Measurable f)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    IsMarkovChain μ Xs Zc (fun ω ↦ f (Yo ω)) :=
  isMarkovChain_swap μ (fun ω ↦ f (Yo ω)) Zc Xs (hf.comp hYo) hZc hXs
    (isMarkovChain_map_left μ Yo Zc Xs hYo hZc hXs hf
      (isMarkovChain_swap μ Xs Zc Yo hXs hZc hYo hmarkov))

private lemma mutualInfoReal_pair_eq_add (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → S) (Yo : Ω → T) (Zc : Ω → R)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    mutualInfoReal μ (fun ω ↦ (Zc ω, Xs ω)) Yo
      = mutualInfoReal μ Zc Yo + condMutualInfoReal μ Xs Yo Zc := by
  unfold mutualInfoReal condMutualInfoReal
  rw [mutualInfo_chain_rule μ Xs Yo Zc hXs hYo hZc,
    ENNReal.toReal_add (mutualInfo_ne_top_of_fintype_right μ Zc Yo hZc hYo)
      (condMutualInfo_ne_top μ Xs Yo Zc hXs hYo hZc)]

private lemma mutualInfoReal_le_of_markov (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → S) (Zc : Ω → R) (Yo : Ω → T)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    mutualInfoReal μ Xs Yo ≤ mutualInfoReal μ Xs Zc := by
  unfold mutualInfoReal
  rw [mutualInfo_comm μ Xs Yo hXs hYo, mutualInfo_comm μ Xs Zc hXs hZc]
  exact ENNReal.toReal_mono (mutualInfo_ne_top_of_fintype_right μ Zc Xs hZc hXs)
    (mutualInfo_le_of_markov μ Yo Zc Xs hYo hZc hXs
      (isMarkovChain_swap μ Xs Zc Yo hXs hZc hYo hmarkov))

private lemma condMutualInfoReal_add_eq_of_markov (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Q : Type*} [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [StandardBorelSpace Q] [Nonempty Q]
    (Vs : Ω → S) (Xs : Ω → R) (Zs : Ω → T) (Ws : Ω → Q)
    (hVs : Measurable Vs) (hXs : Measurable Xs) (hZs : Measurable Zs) (hWs : Measurable Ws)
    (hmarkov : IsMarkovChain μ Vs (fun ω ↦ (Xs ω, Ws ω)) Zs) :
    condMutualInfoReal μ Vs Zs Ws + condMutualInfoReal μ Vs Xs (fun ω ↦ (Ws ω, Zs ω))
      = condMutualInfoReal μ Vs Xs Ws := by
  have hXW : Measurable (fun ω ↦ (Xs ω, Ws ω)) := hXs.prodMk hWs
  have hWZ : Measurable (fun ω ↦ (Ws ω, Zs ω)) := hWs.prodMk hZs
  have hzero : condMutualInfo μ Zs Vs (fun ω ↦ (Ws ω, Xs ω)) = 0 := by
    rw [condMutualInfo_comm μ Zs Vs (fun ω ↦ (Ws ω, Xs ω)) hZs hVs (hWs.prodMk hXs),
      show (fun ω ↦ (Ws ω, Xs ω))
          = (fun ω ↦ (MeasurableEquiv.prodComm : R × Q ≃ᵐ Q × R) (Xs ω, Ws ω)) from rfl,
      condMutualInfo_map_cond_measurableEquiv μ Vs Zs (fun ω ↦ (Xs ω, Ws ω)) hVs hZs hXW]
    exact condMutualInfo_eq_zero_of_markov μ Vs (fun ω ↦ (Xs ω, Ws ω)) Zs hVs hXW hZs hmarkov
  have hswap := condMutualInfo_add_condMutualInfo_swap μ Zs Xs Vs Ws hZs hXs hVs hWs
    (mutualInfo_ne_top_of_fintype_right μ Ws Vs hWs hVs)
  rw [hzero, add_zero, condMutualInfo_comm μ Zs Vs Ws hZs hVs hWs,
    condMutualInfo_comm μ Xs Vs Ws hXs hVs hWs,
    condMutualInfo_comm μ Xs Vs (fun ω ↦ (Ws ω, Zs ω)) hXs hVs hWZ] at hswap
  unfold condMutualInfoReal
  rw [← ENNReal.toReal_add (condMutualInfo_ne_top μ Vs Zs Ws hVs hZs hWs)
    (condMutualInfo_ne_top μ Vs Xs (fun ω ↦ (Ws ω, Zs ω)) hVs hXs hWZ), hswap]

private lemma mutualInfoReal_add_condMutualInfoReal_eq_of_markov (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Cs : Ω → R) (Xs : Ω → S) (Zs : Ω → T)
    (hCs : Measurable Cs) (hXs : Measurable Xs) (hZs : Measurable Zs)
    (hmarkov : IsMarkovChain μ Cs Xs Zs) :
    mutualInfoReal μ Cs Zs + condMutualInfoReal μ Xs Zs Cs = mutualInfoReal μ Xs Zs := by
  have hswap : mutualInfoReal μ (fun ω ↦ (Cs ω, Xs ω)) Zs
      = mutualInfoReal μ (fun ω ↦ (Xs ω, Cs ω)) Zs := by
    unfold mutualInfoReal
    rw [show (fun ω ↦ (Cs ω, Xs ω))
        = (fun ω ↦ (MeasurableEquiv.prodComm : S × R ≃ᵐ R × S) (Xs ω, Cs ω)) from rfl,
      mutualInfo_map_left_measurableEquiv μ (fun ω ↦ (Xs ω, Cs ω)) Zs (hXs.prodMk hCs) hZs
        MeasurableEquiv.prodComm]
  have hzero : condMutualInfoReal μ Cs Zs Xs = 0 := by
    unfold condMutualInfoReal
    rw [condMutualInfo_eq_zero_of_markov μ Cs Xs Zs hCs hXs hZs hmarkov, ENNReal.toReal_zero]
  rw [← mutualInfoReal_pair_eq_add μ Xs Zs Cs hXs hZs hCs, hswap,
    mutualInfoReal_pair_eq_add μ Cs Zs Xs hCs hZs hXs, hzero, add_zero]

private lemma condMutualInfoReal_le_of_markov (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Q : Type*} [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [StandardBorelSpace Q] [Nonempty Q]
    (Vs : Ω → S) (Xs : Ω → R) (Zs : Ω → T) (Ws : Ω → Q)
    (hVs : Measurable Vs) (hXs : Measurable Xs) (hZs : Measurable Zs) (hWs : Measurable Ws)
    (hmarkov : IsMarkovChain μ Vs (fun ω ↦ (Xs ω, Ws ω)) Zs) :
    condMutualInfoReal μ Vs Zs Ws ≤ condMutualInfoReal μ Vs Xs Ws := by
  rw [← condMutualInfoReal_add_eq_of_markov μ Vs Xs Zs Ws hVs hXs hZs hWs hmarkov]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

end Bridges

section Transport

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]

-- channel input `X`, receiver outputs `Y` and `Z`, auxiliary receiver output `J`
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [StandardBorelSpace A] [Nonempty A]
variable {B₁ : Type*} [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [StandardBorelSpace B₁] [Nonempty B₁]
variable {B₂ : Type*} [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]
  [StandardBorelSpace B₂] [Nonempty B₂]
variable {D : Type*} [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
  [StandardBorelSpace D] [Nonempty D]

-- the plain system `(W, U, V)`
variable {Wp : Type*} [Fintype Wp] [MeasurableSpace Wp] [MeasurableSingletonClass Wp]
  [StandardBorelSpace Wp] [Nonempty Wp]
variable {Up : Type*} [Fintype Up] [MeasurableSpace Up] [MeasurableSingletonClass Up]
  [StandardBorelSpace Up] [Nonempty Up]
variable {Vp : Type*} [Fintype Vp] [MeasurableSpace Vp] [MeasurableSingletonClass Vp]
  [StandardBorelSpace Vp] [Nonempty Vp]

-- the first enhanced system `(W̃, Ũ, Ṽ)`
variable {Wt : Type*} [Fintype Wt] [MeasurableSpace Wt] [MeasurableSingletonClass Wt]
  [StandardBorelSpace Wt] [Nonempty Wt]
variable {Ut : Type*} [Fintype Ut] [MeasurableSpace Ut] [MeasurableSingletonClass Ut]
  [StandardBorelSpace Ut] [Nonempty Ut]
variable {Vt : Type*} [Fintype Vt] [MeasurableSpace Vt] [MeasurableSingletonClass Vt]
  [StandardBorelSpace Vt] [Nonempty Vt]

-- the second enhanced system `(Ŵ, Û, V̂)`
variable {Wh : Type*} [Fintype Wh] [MeasurableSpace Wh] [MeasurableSingletonClass Wh]
  [StandardBorelSpace Wh] [Nonempty Wh]
variable {Uh : Type*} [Fintype Uh] [MeasurableSpace Uh] [MeasurableSingletonClass Uh]
  [StandardBorelSpace Uh] [Nonempty Uh]
variable {Vh : Type*} [Fintype Vh] [MeasurableSpace Vh] [MeasurableSingletonClass Vh]
  [StandardBorelSpace Vh] [Nonempty Vh]

/-! ### One auxiliary receiver -/

/-- Right-hand side of the one-auxiliary-receiver constraint on the common rate `R₀`:
`min {I(W; Y), I(Ŵ; Y), I(W; Z), I(W̃; Z)}`.

@audit:ok -/
noncomputable def singleAuxCommonBound (μ : Measure Ω)
    (y : Ω → B₁) (z : Ω → B₂) (w : Ω → Wp) (wt : Ω → Wt) (wh : Ω → Wh) : ℝ :=
  min (mutualInfoReal μ w y)
    (min (mutualInfoReal μ wh y)
      (min (mutualInfoReal μ w z) (mutualInfoReal μ wt z)))

/-- Right-hand side of the one-auxiliary-receiver constraint on `R₀ + R₁` that is centered on
the second enhanced system:
`min {I(Ŵ; Y) + min {0, I(W; Z) - I(W; Y)}, I(Ŵ; J) + I(W̃; Z) - I(W̃; J)} + I(Û; Y | Ŵ)`.

@audit:ok -/
noncomputable def singleAuxFirstUserBound (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (w : Ω → Wp) (wt : Ω → Wt) (wh : Ω → Wh) (uh : Ω → Uh) : ℝ :=
  min (mutualInfoReal μ wh y + min 0 (mutualInfoReal μ w z - mutualInfoReal μ w y))
      (mutualInfoReal μ wh j + mutualInfoReal μ wt z - mutualInfoReal μ wt j)
    + condMutualInfoReal μ uh y wh

/-- Right-hand side of the one-auxiliary-receiver constraint on `R₀ + R₂` that carries the
first enhanced system in its tail:
`min {I(Ŵ; Y) + min {0, I(W; Z) - I(W; Y)}, I(Ŵ; J) + I(W̃; Z) - I(W̃; J)}
  + I(V̂; J | Ŵ) + I(Ṽ; Z | W̃) - I(Ṽ; J | W̃)`.

@audit:ok -/
noncomputable def singleAuxSecondUserBound (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (w : Ω → Wp) (wt : Ω → Wt) (vt : Ω → Vt) (wh : Ω → Wh) (vh : Ω → Vh) : ℝ :=
  min (mutualInfoReal μ wh y + min 0 (mutualInfoReal μ w z - mutualInfoReal μ w y))
      (mutualInfoReal μ wh j + mutualInfoReal μ wt z - mutualInfoReal μ wt j)
    + condMutualInfoReal μ vh j wh
    + condMutualInfoReal μ vt z wt - condMutualInfoReal μ vt j wt

/-! ### Two auxiliary receivers, at `(const, X)` -/

/-- Right-hand side of the two-auxiliary-receiver constraint on the common rate `R₀`, at
`(const, X)`: `I(Ŵ; Y)`.

In general the constraint reads `min {I(W̃; J) + I(Ŵ; Y | J), I(W̃; Z | Ĵ) + I(Ŵ; Ĵ)}`; at
`(J, Ĵ) = (const, X)` the first system drops out, the second branch reads `I(Ŵ; X)` and the
`min` collapses to its first branch, which `I(Ŵ; X)` dominates.

@audit:ok -/
noncomputable def twoAuxCommonBound (μ : Measure Ω) (y : Ω → B₁) (wh : Ω → Wh) : ℝ :=
  mutualInfoReal μ wh y

/-- Right-hand side of the first two-auxiliary-receiver constraint on `R₀ + R₁`, at
`(const, X)`: `I(Ŵ, Û; Y)`.

In general the constraint reads `I(Ũ, W̃; J) + I(Û, Ŵ; Y | J)`, whose first summand vanishes
at `J = const`. The pair is written `(Ŵ, Û)` to match the conclusion of
`mutualInfo_chain_rule`, which puts the variable that becomes the conditioner first.

@audit:ok -/
noncomputable def twoAuxFirstUserBound (μ : Measure Ω)
    (y : Ω → B₁) (wh : Ω → Wh) (uh : Ω → Uh) : ℝ :=
  mutualInfoReal μ (fun ω ↦ (wh ω, uh ω)) y

/-- Right-hand side of the second two-auxiliary-receiver constraint on `R₀ + R₁`, at
`(const, X)`: `I(Ŵ; X) + I(Û; Y | Ŵ)`.

In general the constraint reads
`I(W̃; Z | Ĵ) + I(Ŵ, J; Ĵ) + I(Ũ; J | W̃, Ĵ) + I(Û; Y | Ŵ, J)`, whose first three summands
vanish at `(J, Ĵ) = (const, X)`.

@audit:ok -/
noncomputable def twoAuxFirstUserBoundInput (μ : Measure Ω) [IsFiniteMeasure μ]
    (x : Ω → A) (y : Ω → B₁) (wh : Ω → Wh) (uh : Ω → Uh) : ℝ :=
  mutualInfoReal μ wh x + condMutualInfoReal μ uh y wh

/-- Right-hand side of the first two-auxiliary-receiver constraint on `R₀ + R₂`, at
`(const, X)`: `I(Ŵ; Y) + I(V̂; X | Ŵ)`.

In general the constraint reads
`I(W̃, Ĵ; J) + I(Ŵ; Y | J) + I(Ṽ; Z | W̃, Ĵ) + I(V̂; Ĵ | Ŵ, J)`, whose first and third summands
vanish at `(J, Ĵ) = (const, X)`.

@audit:ok -/
noncomputable def twoAuxSecondUserBound (μ : Measure Ω) [IsFiniteMeasure μ]
    (x : Ω → A) (y : Ω → B₁) (wh : Ω → Wh) (vh : Ω → Vh) : ℝ :=
  mutualInfoReal μ wh y + condMutualInfoReal μ vh x wh

/-- Right-hand side of the second two-auxiliary-receiver constraint on `R₀ + R₂`, at
`(const, X)`: `I(Ŵ, V̂; X)`.

In general the constraint reads `I(V̂, Ŵ; Ĵ) + I(Ṽ, W̃; Z | Ĵ)`, whose second summand vanishes
at `Ĵ = X`.

@audit:ok -/
noncomputable def twoAuxSecondUserBoundInput (μ : Measure Ω)
    (x : Ω → A) (wh : Ω → Wh) (vh : Ω → Vh) : ℝ :=
  mutualInfoReal μ (fun ω ↦ (wh ω, vh ω)) x

/-! ### The five comparisons -/

/-- The common-rate constraint transports: the one-auxiliary-receiver bound on `R₀` is at most
the two-auxiliary-receiver one at `(const, X)`.

@audit:ok -/
@[entry_point]
theorem singleAuxCommonBound_le_twoAuxCommonBound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (w : Ω → Wp) (wt : Ω → Wt) (wh : Ω → Wh) :
    singleAuxCommonBound μ y z w wt wh ≤ twoAuxCommonBound μ y wh := by
  unfold singleAuxCommonBound twoAuxCommonBound
  exact le_trans (min_le_right _ _) (min_le_left _ _)

/-- The first `R₀ + R₁` constraint transports, for every auxiliary receiver output `j`.

@audit:ok -/
@[entry_point]
theorem singleAuxFirstUserBound_le_twoAuxFirstUserBound (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (w : Ω → Wp) (wt : Ω → Wt) (wh : Ω → Wh) (uh : Ω → Uh)
    (hy : Measurable y) (hwh : Measurable wh) (huh : Measurable uh) :
    singleAuxFirstUserBound μ y z j w wt wh uh ≤ twoAuxFirstUserBound μ y wh uh := by
  unfold singleAuxFirstUserBound twoAuxFirstUserBound
  rw [mutualInfoReal_pair_eq_add μ uh y wh huh hy hwh]
  have hmin : min (0 : ℝ) (mutualInfoReal μ w z - mutualInfoReal μ w y) ≤ 0 := min_le_left _ _
  have hbranch :
      min (mutualInfoReal μ wh y + min 0 (mutualInfoReal μ w z - mutualInfoReal μ w y))
          (mutualInfoReal μ wh j + mutualInfoReal μ wt z - mutualInfoReal μ wt j)
        ≤ mutualInfoReal μ wh y :=
    le_trans (min_le_left _ _) (by linarith)
  linarith

/-- The two `R₀ + R₁` constraints of the two-auxiliary-receiver bound are ordered, the gap
being `I(Ŵ; X | Y) ≥ 0`.

@audit:ok -/
@[entry_point]
theorem twoAuxFirstUserBound_le_twoAuxFirstUserBoundInput (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (x : Ω → A) (y : Ω → B₁) (z : Ω → B₂)
    (wh : Ω → Wh) (uh : Ω → Uh) (vh : Ω → Vh)
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
    (hwh : Measurable wh) (huh : Measurable uh) (hvh : Measurable vh)
    (hhat : IsMarkovChain μ (fun ω ↦ (wh ω, uh ω, vh ω)) x (fun ω ↦ (y ω, z ω))) :
    twoAuxFirstUserBound μ y wh uh ≤ twoAuxFirstUserBoundInput μ x y wh uh := by
  unfold twoAuxFirstUserBound twoAuxFirstUserBoundInput
  rw [mutualInfoReal_pair_eq_add μ uh y wh huh hy hwh]
  have hchain : IsMarkovChain μ wh x y :=
    isMarkovChain_map_right μ wh x (fun ω ↦ (y ω, z ω)) hwh hx (hy.prodMk hz) measurable_fst
      (isMarkovChain_map_left μ (fun ω ↦ (wh ω, uh ω, vh ω)) x (fun ω ↦ (y ω, z ω))
        (hwh.prodMk (huh.prodMk hvh)) hx (hy.prodMk hz) measurable_fst hhat)
  have := mutualInfoReal_le_of_markov μ wh x y hwh hx hy hchain
  linarith

/-- The `R₀ + R₂` constraint transports at the single auxiliary receiver `J := X`.

@audit:ok -/
@[entry_point]
theorem singleAuxSecondUserBound_le_twoAuxSecondUserBound (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (x : Ω → A) (y : Ω → B₁) (z : Ω → B₂)
    (w : Ω → Wp) (wt : Ω → Wt) (ut : Ω → Ut) (vt : Ω → Vt) (wh : Ω → Wh) (vh : Ω → Vh)
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
    (hwt : Measurable wt) (hut : Measurable ut) (hvt : Measurable vt)
    (htilde : IsMarkovChain μ (fun ω ↦ (wt ω, ut ω, vt ω)) x (fun ω ↦ (y ω, z ω))) :
    singleAuxSecondUserBound μ y z x w wt vt wh vh ≤ twoAuxSecondUserBound μ x y wh vh := by
  unfold singleAuxSecondUserBound twoAuxSecondUserBound
  have hyz : Measurable (fun ω ↦ (y ω, z ω)) := hy.prodMk hz
  have hpair : IsMarkovChain μ (fun ω ↦ (wt ω, vt ω)) x z :=
    isMarkovChain_map_right μ (fun ω ↦ (wt ω, vt ω)) x (fun ω ↦ (y ω, z ω))
      (hwt.prodMk hvt) hx hyz measurable_snd
      (isMarkovChain_map_left μ (fun ω ↦ (wt ω, ut ω, vt ω)) x (fun ω ↦ (y ω, z ω))
        (hwt.prodMk (hut.prodMk hvt)) hx hyz
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) htilde)
  have hdpi := condMutualInfoReal_le_of_markov μ vt x z wt hvt hx hz hwt
    (ChannelCodingConverseGeneral.isMarkovChain_weakUnion_left_to_conditioner
      μ wt vt x z hwt hvt hx hz hpair)
  have hmin : min (0 : ℝ) (mutualInfoReal μ w z - mutualInfoReal μ w y) ≤ 0 := min_le_left _ _
  have hbranch :
      min (mutualInfoReal μ wh y + min 0 (mutualInfoReal μ w z - mutualInfoReal μ w y))
          (mutualInfoReal μ wh x + mutualInfoReal μ wt z - mutualInfoReal μ wt x)
        ≤ mutualInfoReal μ wh y :=
    le_trans (min_le_left _ _) (by linarith)
  linarith

/-- The tail of the one-auxiliary-receiver constraint on `R₀ + R₂` at `J := X`, in closed form:
`I(Ṽ; X | W̃) - I(Ṽ; Z | W̃) = I(Ṽ; X | W̃, Z)`, which is what makes that tail nonpositive.

@audit:ok -/
@[entry_point]
theorem condMutualInfoReal_sub_eq_condMutualInfoReal_prod (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (x : Ω → A) (y : Ω → B₁) (z : Ω → B₂)
    (wt : Ω → Wt) (ut : Ω → Ut) (vt : Ω → Vt)
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
    (hwt : Measurable wt) (hut : Measurable ut) (hvt : Measurable vt)
    (htilde : IsMarkovChain μ (fun ω ↦ (wt ω, ut ω, vt ω)) x (fun ω ↦ (y ω, z ω))) :
    condMutualInfoReal μ vt x wt - condMutualInfoReal μ vt z wt
      = condMutualInfoReal μ vt x (fun ω ↦ (wt ω, z ω)) := by
  have hyz : Measurable (fun ω ↦ (y ω, z ω)) := hy.prodMk hz
  have hpair : IsMarkovChain μ (fun ω ↦ (wt ω, vt ω)) x z :=
    isMarkovChain_map_right μ (fun ω ↦ (wt ω, vt ω)) x (fun ω ↦ (y ω, z ω))
      (hwt.prodMk hvt) hx hyz measurable_snd
      (isMarkovChain_map_left μ (fun ω ↦ (wt ω, ut ω, vt ω)) x (fun ω ↦ (y ω, z ω))
        (hwt.prodMk (hut.prodMk hvt)) hx hyz
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) htilde)
  have hid := condMutualInfoReal_add_eq_of_markov μ vt x z wt hvt hx hz hwt
    (ChannelCodingConverseGeneral.isMarkovChain_weakUnion_left_to_conditioner
      μ wt vt x z hwt hvt hx hz hpair)
  linarith

/-- The two `R₀ + R₂` constraints of the two-auxiliary-receiver bound are ordered, the gap
being `I(Ŵ; X | Y) ≥ 0`.

@audit:ok -/
@[entry_point]
theorem twoAuxSecondUserBound_le_twoAuxSecondUserBoundInput (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (x : Ω → A) (y : Ω → B₁) (z : Ω → B₂)
    (wh : Ω → Wh) (uh : Ω → Uh) (vh : Ω → Vh)
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
    (hwh : Measurable wh) (huh : Measurable uh) (hvh : Measurable vh)
    (hhat : IsMarkovChain μ (fun ω ↦ (wh ω, uh ω, vh ω)) x (fun ω ↦ (y ω, z ω))) :
    twoAuxSecondUserBound μ x y wh vh ≤ twoAuxSecondUserBoundInput μ x wh vh := by
  unfold twoAuxSecondUserBound twoAuxSecondUserBoundInput
  rw [mutualInfoReal_pair_eq_add μ vh x wh hvh hx hwh]
  have hchain : IsMarkovChain μ wh x y :=
    isMarkovChain_map_right μ wh x (fun ω ↦ (y ω, z ω)) hwh hx (hy.prodMk hz) measurable_fst
      (isMarkovChain_map_left μ (fun ω ↦ (wh ω, uh ω, vh ω)) x (fun ω ↦ (y ω, z ω))
        (hwh.prodMk (huh.prodMk hvh)) hx (hy.prodMk hz) measurable_fst hhat)
  have := mutualInfoReal_le_of_markov μ wh x y hwh hx hy hchain
  linarith

/-! ### The two sum-rate constraints of the one-auxiliary-receiver bound -/

private lemma min_sub_right_eq_of_sub_eq {a b c d : ℝ} (h : a - b = c - d) :
    min a b - b = min c d - d := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, min_eq_left (show c ≤ d by linarith)]
    linarith
  · rw [min_eq_right hab, min_eq_right (show d ≤ c by linarith)]
    linarith

/-- Right-hand side of the one-auxiliary-receiver constraint on `R₀ + R₁ + R₂` that is stated
through the two enhanced systems and the auxiliary receiver output `J`:
`min {I(Ŵ; Y) - I(Ŵ; J), I(W̃; Z) - I(W̃; J)} + I(X; J) + I(Û; Y | Ŵ) - I(Û; J | Ŵ)
  + I(Ṽ; Z | W̃) - I(Ṽ; J | W̃)`.

@audit:ok -/
noncomputable def enhancedSumRateBound (μ : Measure Ω) [IsFiniteMeasure μ]
    (x : Ω → A) (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (wt : Ω → Wt) (vt : Ω → Vt) (wh : Ω → Wh) (uh : Ω → Uh) : ℝ :=
  min (mutualInfoReal μ wh y - mutualInfoReal μ wh j)
      (mutualInfoReal μ wt z - mutualInfoReal μ wt j)
    + mutualInfoReal μ x j
    + (condMutualInfoReal μ uh y wh - condMutualInfoReal μ uh j wh)
    + (condMutualInfoReal μ vt z wt - condMutualInfoReal μ vt j wt)

/-- Right-hand side of the one-auxiliary-receiver constraint on `R₀ + R₁ + R₂` that is stated
through the plain system alone:
`min {I(W; Y), I(W; Z)} + min {I(V; Z | W) + I(X; Y | W, V), I(U; Y | W) + I(X; Z | W, U)}`.

Each conditioning pair puts `W` first, so that the chain rule reads it as the conditioner.

@audit:ok -/
noncomputable def plainSumRateBound (μ : Measure Ω) [IsFiniteMeasure μ]
    (x : Ω → A) (y : Ω → B₁) (z : Ω → B₂)
    (w : Ω → Wp) (u : Ω → Up) (v : Ω → Vp) : ℝ :=
  min (mutualInfoReal μ w y) (mutualInfoReal μ w z)
    + min (condMutualInfoReal μ v z w + condMutualInfoReal μ x y (fun ω ↦ (w ω, v ω)))
        (condMutualInfoReal μ u y w + condMutualInfoReal μ x z (fun ω ↦ (w ω, u ω)))

/-- Slack in the upper half of the compatibility condition that ties the second user's tail in
the first enhanced system to the input:
`I(Ṽ; Z | W̃) - I(Ṽ; J | W̃) - (I(X; Z | W̃, Ũ) - I(X; J | W̃, Ũ))`.

The conditioning pair puts `W̃` first, so that the chain rule reads it as the conditioner.

@audit:ok -/
noncomputable def secondUserSlack (μ : Measure Ω) [IsFiniteMeasure μ]
    (x : Ω → A) (z : Ω → B₂) (j : Ω → D)
    (wt : Ω → Wt) (ut : Ω → Ut) (vt : Ω → Vt) : ℝ :=
  condMutualInfoReal μ vt z wt - condMutualInfoReal μ vt j wt
    - (condMutualInfoReal μ x z (fun ω ↦ (wt ω, ut ω))
        - condMutualInfoReal μ x j (fun ω ↦ (wt ω, ut ω)))

/-- The two sum-rate constraints of the one-auxiliary-receiver bound differ by exactly the
slack of the second user's compatibility condition.

`hcommon` and `hfirst` are the compatibility conditions tying the plain system to the two
enhanced ones at the level of `W` and of `U`, and `hbalance` is the one equating the two branches
of the inner minimum of `plainSumRateBound`. The slack is not assumed to be nonnegative, so the
identity holds on either side of the condition that bounds it.

@audit:ok -/
@[entry_point]
theorem enhancedSumRateBound_sub_plainSumRateBound_eq_secondUserSlack (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (x : Ω → A) (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (w : Ω → Wp) (u : Ω → Up) (v : Ω → Vp)
    (wt : Ω → Wt) (ut : Ω → Ut) (vt : Ω → Vt) (wh : Ω → Wh) (uh : Ω → Uh)
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z) (hj : Measurable j)
    (hw : Measurable w) (hu : Measurable u) (hv : Measurable v)
    (hwt : Measurable wt) (hut : Measurable ut) (hvt : Measurable vt)
    (hplain : IsMarkovChain μ (fun ω ↦ (w ω, u ω, v ω)) x (fun ω ↦ (y ω, z ω, j ω)))
    (htilde : IsMarkovChain μ (fun ω ↦ (wt ω, ut ω, vt ω)) x (fun ω ↦ (y ω, z ω, j ω)))
    (hcommon : mutualInfoReal μ wt z - mutualInfoReal μ wt j
        + (mutualInfoReal μ wh j - mutualInfoReal μ wh y)
      = mutualInfoReal μ w z - mutualInfoReal μ w y)
    (hfirst : condMutualInfoReal μ ut z wt - condMutualInfoReal μ ut j wt
        + (condMutualInfoReal μ uh j wh - condMutualInfoReal μ uh y wh)
      = condMutualInfoReal μ u z w - condMutualInfoReal μ u y w)
    (hbalance : condMutualInfoReal μ v z w + condMutualInfoReal μ x y (fun ω ↦ (w ω, v ω))
      = condMutualInfoReal μ u y w + condMutualInfoReal μ x z (fun ω ↦ (w ω, u ω))) :
    enhancedSumRateBound μ x y z j wt vt wh uh - plainSumRateBound μ x y z w u v
      = secondUserSlack μ x z j wt ut vt := by
  have hyzj : Measurable (fun ω ↦ (y ω, z ω, j ω)) := hy.prodMk (hz.prodMk hj)
  have hwu : Measurable (fun ω ↦ (w ω, u ω)) := hw.prodMk hu
  have hwtut : Measurable (fun ω ↦ (wt ω, ut ω)) := hwt.prodMk hut
  -- the two systems stay conditionally independent of the outputs after dropping a component
  have hplainPair : IsMarkovChain μ (fun ω ↦ (w ω, u ω)) x (fun ω ↦ (y ω, z ω, j ω)) :=
    isMarkovChain_map_left μ (fun ω ↦ (w ω, u ω, v ω)) x (fun ω ↦ (y ω, z ω, j ω))
      (hw.prodMk (hu.prodMk hv)) hx hyzj
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) hplain
  have htildePair : IsMarkovChain μ (fun ω ↦ (wt ω, ut ω)) x (fun ω ↦ (y ω, z ω, j ω)) :=
    isMarkovChain_map_left μ (fun ω ↦ (wt ω, ut ω, vt ω)) x (fun ω ↦ (y ω, z ω, j ω))
      (hwt.prodMk (hut.prodMk hvt)) hx hyzj
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) htilde
  have hplainZ : IsMarkovChain μ (fun ω ↦ (w ω, u ω)) x z :=
    isMarkovChain_map_right μ (fun ω ↦ (w ω, u ω)) x (fun ω ↦ (y ω, z ω, j ω))
      hwu hx hyzj (measurable_fst.comp measurable_snd) hplainPair
  have htildeZ : IsMarkovChain μ (fun ω ↦ (wt ω, ut ω)) x z :=
    isMarkovChain_map_right μ (fun ω ↦ (wt ω, ut ω)) x (fun ω ↦ (y ω, z ω, j ω))
      hwtut hx hyzj (measurable_fst.comp measurable_snd) htildePair
  have htildeJ : IsMarkovChain μ (fun ω ↦ (wt ω, ut ω)) x j :=
    isMarkovChain_map_right μ (fun ω ↦ (wt ω, ut ω)) x (fun ω ↦ (y ω, z ω, j ω))
      hwtut hx hyzj (measurable_snd.comp measurable_snd) htildePair
  -- each conditioning pair can be peeled off the input's mutual informations
  have hCz := mutualInfoReal_add_condMutualInfoReal_eq_of_markov μ (fun ω ↦ (wt ω, ut ω)) x z
    hwtut hx hz htildeZ
  have hCj := mutualInfoReal_add_condMutualInfoReal_eq_of_markov μ (fun ω ↦ (wt ω, ut ω)) x j
    hwtut hx hj htildeJ
  have hPz := mutualInfoReal_add_condMutualInfoReal_eq_of_markov μ (fun ω ↦ (w ω, u ω)) x z
    hwu hx hz hplainZ
  have hCchainZ := mutualInfoReal_pair_eq_add μ ut z wt hut hz hwt
  have hCchainJ := mutualInfoReal_pair_eq_add μ ut j wt hut hj hwt
  have hPchain := mutualInfoReal_pair_eq_add μ u z w hu hz hw
  -- the two leading minima cancel each other
  have hmin : min (mutualInfoReal μ wh y - mutualInfoReal μ wh j)
        (mutualInfoReal μ wt z - mutualInfoReal μ wt j)
      - (mutualInfoReal μ wt z - mutualInfoReal μ wt j)
      = min (mutualInfoReal μ w y) (mutualInfoReal μ w z) - mutualInfoReal μ w z :=
    min_sub_right_eq_of_sub_eq (by linarith)
  unfold enhancedSumRateBound plainSumRateBound secondUserSlack
  rw [min_eq_right hbalance.ge]
  linarith

/-- Under the second user's compatibility condition the sum-rate constraint carrying the
auxiliary receiver output is the weaker of the two.

@audit:ok -/
@[entry_point]
theorem plainSumRateBound_le_enhancedSumRateBound (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (x : Ω → A) (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (w : Ω → Wp) (u : Ω → Up) (v : Ω → Vp)
    (wt : Ω → Wt) (ut : Ω → Ut) (vt : Ω → Vt) (wh : Ω → Wh) (uh : Ω → Uh)
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z) (hj : Measurable j)
    (hw : Measurable w) (hu : Measurable u) (hv : Measurable v)
    (hwt : Measurable wt) (hut : Measurable ut) (hvt : Measurable vt)
    (hplain : IsMarkovChain μ (fun ω ↦ (w ω, u ω, v ω)) x (fun ω ↦ (y ω, z ω, j ω)))
    (htilde : IsMarkovChain μ (fun ω ↦ (wt ω, ut ω, vt ω)) x (fun ω ↦ (y ω, z ω, j ω)))
    (hcommon : mutualInfoReal μ wt z - mutualInfoReal μ wt j
        + (mutualInfoReal μ wh j - mutualInfoReal μ wh y)
      = mutualInfoReal μ w z - mutualInfoReal μ w y)
    (hfirst : condMutualInfoReal μ ut z wt - condMutualInfoReal μ ut j wt
        + (condMutualInfoReal μ uh j wh - condMutualInfoReal μ uh y wh)
      = condMutualInfoReal μ u z w - condMutualInfoReal μ u y w)
    (hbalance : condMutualInfoReal μ v z w + condMutualInfoReal μ x y (fun ω ↦ (w ω, v ω))
      = condMutualInfoReal μ u y w + condMutualInfoReal μ x z (fun ω ↦ (w ω, u ω)))
    (hsecond : condMutualInfoReal μ x z (fun ω ↦ (wt ω, ut ω))
        - condMutualInfoReal μ x j (fun ω ↦ (wt ω, ut ω))
      ≤ condMutualInfoReal μ vt z wt - condMutualInfoReal μ vt j wt) :
    plainSumRateBound μ x y z w u v ≤ enhancedSumRateBound μ x y z j wt vt wh uh := by
  have hid := enhancedSumRateBound_sub_plainSumRateBound_eq_secondUserSlack μ x y z j w u v
    wt ut vt wh uh hx hy hz hj hw hu hv hwt hut hvt hplain htilde hcommon hfirst hbalance
  have hnonneg : 0 ≤ secondUserSlack μ x z j wt ut vt := by
    unfold secondUserSlack
    linarith
  linarith

/-- The sum-rate constraint carrying the auxiliary receiver output is never binding: a rate that
meets the constraint stated through the plain system meets it too.

The two sides are right-hand sides of constraints of one and the same bound, so this says which
of the two constraints is redundant, not what the bound's rate region is.

@audit:ok -/
@[entry_point]
theorem le_enhancedSumRateBound_of_le_plainSumRateBound (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (x : Ω → A) (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (w : Ω → Wp) (u : Ω → Up) (v : Ω → Vp)
    (wt : Ω → Wt) (ut : Ω → Ut) (vt : Ω → Vt) (wh : Ω → Wh) (uh : Ω → Uh)
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z) (hj : Measurable j)
    (hw : Measurable w) (hu : Measurable u) (hv : Measurable v)
    (hwt : Measurable wt) (hut : Measurable ut) (hvt : Measurable vt)
    (hplain : IsMarkovChain μ (fun ω ↦ (w ω, u ω, v ω)) x (fun ω ↦ (y ω, z ω, j ω)))
    (htilde : IsMarkovChain μ (fun ω ↦ (wt ω, ut ω, vt ω)) x (fun ω ↦ (y ω, z ω, j ω)))
    (hcommon : mutualInfoReal μ wt z - mutualInfoReal μ wt j
        + (mutualInfoReal μ wh j - mutualInfoReal μ wh y)
      = mutualInfoReal μ w z - mutualInfoReal μ w y)
    (hfirst : condMutualInfoReal μ ut z wt - condMutualInfoReal μ ut j wt
        + (condMutualInfoReal μ uh j wh - condMutualInfoReal μ uh y wh)
      = condMutualInfoReal μ u z w - condMutualInfoReal μ u y w)
    (hbalance : condMutualInfoReal μ v z w + condMutualInfoReal μ x y (fun ω ↦ (w ω, v ω))
      = condMutualInfoReal μ u y w + condMutualInfoReal μ x z (fun ω ↦ (w ω, u ω)))
    (hsecond : condMutualInfoReal μ x z (fun ω ↦ (wt ω, ut ω))
        - condMutualInfoReal μ x j (fun ω ↦ (wt ω, ut ω))
      ≤ condMutualInfoReal μ vt z wt - condMutualInfoReal μ vt j wt)
    {r : ℝ} (hr : r ≤ plainSumRateBound μ x y z w u v) :
    r ≤ enhancedSumRateBound μ x y z j wt vt wh uh :=
  hr.trans (plainSumRateBound_le_enhancedSumRateBound μ x y z j w u v wt ut vt wh uh
    hx hy hz hj hw hu hv hwt hut hvt hplain htilde hcommon hfirst hbalance hsecond)

/-! ### Eliminating the auxiliary receiver output -/

private lemma min_add_min_zero_eq_left {a c d : ℝ} (h : c = a + d) :
    min (a + min 0 d) c = a + min 0 d :=
  min_eq_left (by have := min_le_right (0 : ℝ) d; linarith)

/-- Right-hand side of the one-auxiliary-receiver constraint on `R₀ + R₁` that is centered on
the second enhanced system, with the auxiliary receiver output eliminated:
`I(Ŵ; Y) + min {0, I(W; Z) - I(W; Y)} + I(Û; Y | Ŵ)`. -/
noncomputable def singleAuxFirstUserBoundJFree (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (w : Ω → Wp) (wh : Ω → Wh) (uh : Ω → Uh) : ℝ :=
  mutualInfoReal μ wh y + min 0 (mutualInfoReal μ w z - mutualInfoReal μ w y)
    + condMutualInfoReal μ uh y wh

/-- The auxiliary receiver output drops out of the `R₀ + R₁` constraint centered on the second
enhanced system: its leading minimum is attained at the branch that does not read `J`. -/
@[entry_point]
theorem singleAuxFirstUserBound_eq_jFree (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (w : Ω → Wp) (wt : Ω → Wt) (wh : Ω → Wh) (uh : Ω → Uh)
    (hcommon : mutualInfoReal μ wt z - mutualInfoReal μ wt j
        + (mutualInfoReal μ wh j - mutualInfoReal μ wh y)
      = mutualInfoReal μ w z - mutualInfoReal μ w y) :
    singleAuxFirstUserBound μ y z j w wt wh uh
      = singleAuxFirstUserBoundJFree μ y z w wh uh := by
  unfold singleAuxFirstUserBound singleAuxFirstUserBoundJFree
  rw [min_add_min_zero_eq_left (by linarith)]

/-- Right-hand side of the one-auxiliary-receiver constraint on `R₀ + R₁` that is centered on
the first enhanced system:
`min {I(W̃; Z) + min {0, I(W; Y) - I(W; Z)}, I(W̃; J) + I(Ŵ; Y) - I(Ŵ; J)}
  + I(Ũ; J | W̃) + I(Û; Y | Ŵ) - I(Û; J | Ŵ)`. -/
noncomputable def singleAuxFirstUserBoundFromZ (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (w : Ω → Wp) (wt : Ω → Wt) (ut : Ω → Ut) (wh : Ω → Wh) (uh : Ω → Uh) : ℝ :=
  min (mutualInfoReal μ wt z + min 0 (mutualInfoReal μ w y - mutualInfoReal μ w z))
      (mutualInfoReal μ wt j + mutualInfoReal μ wh y - mutualInfoReal μ wh j)
    + condMutualInfoReal μ ut j wt
    + condMutualInfoReal μ uh y wh - condMutualInfoReal μ uh j wh

/-- Right-hand side of the one-auxiliary-receiver constraint on `R₀ + R₁` that is centered on
the first enhanced system, with the auxiliary receiver output eliminated:
`I(W̃; Z) + min {0, I(W; Y) - I(W; Z)} + I(Ũ; Z | W̃) - I(U; Z | W) + I(U; Y | W)`.

Eliminating `J` from the tail trades the second enhanced system for the plain one, so this form
reads the first enhanced system and the plain system only. -/
noncomputable def singleAuxFirstUserBoundFromZJFree (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂)
    (w : Ω → Wp) (u : Ω → Up) (wt : Ω → Wt) (ut : Ω → Ut) : ℝ :=
  mutualInfoReal μ wt z + min 0 (mutualInfoReal μ w y - mutualInfoReal μ w z)
    + condMutualInfoReal μ ut z wt
    - condMutualInfoReal μ u z w + condMutualInfoReal μ u y w

/-- Right-hand side of the one-auxiliary-receiver constraint on `R₀ + R₂` that carries the
first enhanced system in its tail, with the auxiliary receiver output eliminated:
`I(Ŵ; Y) + min {0, I(W; Z) - I(W; Y)} + I(V̂; Y | Ŵ) + I(V; Z | W) - I(V; Y | W)`.

Eliminating `J` from the tail trades the first enhanced system for the plain one, so this form
reads the second enhanced system and the plain system only. -/
noncomputable def singleAuxSecondUserBoundJFree (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂)
    (w : Ω → Wp) (v : Ω → Vp) (wh : Ω → Wh) (vh : Ω → Vh) : ℝ :=
  mutualInfoReal μ wh y + min 0 (mutualInfoReal μ w z - mutualInfoReal μ w y)
    + condMutualInfoReal μ vh y wh
    + condMutualInfoReal μ v z w - condMutualInfoReal μ v y w

/-- Right-hand side of the one-auxiliary-receiver constraint on `R₀ + R₂` that is centered on
the first enhanced system:
`min {I(W̃; Z) + min {0, I(W; Y) - I(W; Z)}, I(W̃; J) + I(Ŵ; Y) - I(Ŵ; J)} + I(Ṽ; Z | W̃)`. -/
noncomputable def singleAuxSecondUserBoundFromZ (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (w : Ω → Wp) (wt : Ω → Wt) (vt : Ω → Vt) (wh : Ω → Wh) : ℝ :=
  min (mutualInfoReal μ wt z + min 0 (mutualInfoReal μ w y - mutualInfoReal μ w z))
      (mutualInfoReal μ wt j + mutualInfoReal μ wh y - mutualInfoReal μ wh j)
    + condMutualInfoReal μ vt z wt

/-- Right-hand side of the one-auxiliary-receiver constraint on `R₀ + R₂` that is centered on
the first enhanced system, with the auxiliary receiver output eliminated:
`I(W̃; Z) + min {0, I(W; Y) - I(W; Z)} + I(Ṽ; Z | W̃)`. -/
noncomputable def singleAuxSecondUserBoundFromZJFree (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (w : Ω → Wp) (wt : Ω → Wt) (vt : Ω → Vt) : ℝ :=
  mutualInfoReal μ wt z + min 0 (mutualInfoReal μ w y - mutualInfoReal μ w z)
    + condMutualInfoReal μ vt z wt

/-- The auxiliary receiver output drops out of the `R₀ + R₁` constraint centered on the first
enhanced system: its leading minimum is attained at the branch that does not read `J`, and the
compatibility condition at the level of `U` rewrites the tail. -/
@[entry_point]
theorem singleAuxFirstUserBoundFromZ_eq_jFree (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (w : Ω → Wp) (u : Ω → Up) (wt : Ω → Wt) (ut : Ω → Ut) (wh : Ω → Wh) (uh : Ω → Uh)
    (hcommon : mutualInfoReal μ wt z - mutualInfoReal μ wt j
        + (mutualInfoReal μ wh j - mutualInfoReal μ wh y)
      = mutualInfoReal μ w z - mutualInfoReal μ w y)
    (hfirst : condMutualInfoReal μ ut z wt - condMutualInfoReal μ ut j wt
        + (condMutualInfoReal μ uh j wh - condMutualInfoReal μ uh y wh)
      = condMutualInfoReal μ u z w - condMutualInfoReal μ u y w) :
    singleAuxFirstUserBoundFromZ μ y z j w wt ut wh uh
      = singleAuxFirstUserBoundFromZJFree μ y z w u wt ut := by
  unfold singleAuxFirstUserBoundFromZ singleAuxFirstUserBoundFromZJFree
  rw [min_add_min_zero_eq_left (by linarith)]
  linarith

/-- The auxiliary receiver output drops out of the `R₀ + R₂` constraint that carries the first
enhanced system in its tail: its leading minimum is attained at the branch that does not read
`J`, and the compatibility condition at the level of `V` rewrites the tail. -/
@[entry_point]
theorem singleAuxSecondUserBound_eq_jFree (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (w : Ω → Wp) (v : Ω → Vp) (wt : Ω → Wt) (vt : Ω → Vt) (wh : Ω → Wh) (vh : Ω → Vh)
    (hcommon : mutualInfoReal μ wt z - mutualInfoReal μ wt j
        + (mutualInfoReal μ wh j - mutualInfoReal μ wh y)
      = mutualInfoReal μ w z - mutualInfoReal μ w y)
    (hsecond : condMutualInfoReal μ vt z wt - condMutualInfoReal μ vt j wt
        + (condMutualInfoReal μ vh j wh - condMutualInfoReal μ vh y wh)
      = condMutualInfoReal μ v z w - condMutualInfoReal μ v y w) :
    singleAuxSecondUserBound μ y z j w wt vt wh vh
      = singleAuxSecondUserBoundJFree μ y z w v wh vh := by
  unfold singleAuxSecondUserBound singleAuxSecondUserBoundJFree
  rw [min_add_min_zero_eq_left (by linarith)]
  linarith

/-- The auxiliary receiver output drops out of the `R₀ + R₂` constraint centered on the first
enhanced system: its leading minimum is attained at the branch that does not read `J`. -/
@[entry_point]
theorem singleAuxSecondUserBoundFromZ_eq_jFree (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D)
    (w : Ω → Wp) (wt : Ω → Wt) (vt : Ω → Vt) (wh : Ω → Wh)
    (hcommon : mutualInfoReal μ wt z - mutualInfoReal μ wt j
        + (mutualInfoReal μ wh j - mutualInfoReal μ wh y)
      = mutualInfoReal μ w z - mutualInfoReal μ w y) :
    singleAuxSecondUserBoundFromZ μ y z j w wt vt wh
      = singleAuxSecondUserBoundFromZJFree μ y z w wt vt := by
  unfold singleAuxSecondUserBoundFromZ singleAuxSecondUserBoundFromZJFree
  rw [min_add_min_zero_eq_left (by linarith)]

/-! ### The diagonal witness -/

/-- Right-hand side of the one-auxiliary-receiver constraint on the common rate `R₀` stated
through the plain system alone: `min {I(W; Y), I(W; Z)}`. -/
noncomputable def plainCommonBound (μ : Measure Ω)
    (y : Ω → B₁) (z : Ω → B₂) (w : Ω → Wp) : ℝ :=
  min (mutualInfoReal μ w y) (mutualInfoReal μ w z)

/-- Right-hand side of the one-auxiliary-receiver constraint on `R₀ + R₁` stated through the
plain system alone: `min {I(W; Y), I(W; Z)} + I(U; Y | W)`. -/
noncomputable def plainFirstUserBound (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (w : Ω → Wp) (u : Ω → Up) : ℝ :=
  min (mutualInfoReal μ w y) (mutualInfoReal μ w z) + condMutualInfoReal μ u y w

/-- Right-hand side of the one-auxiliary-receiver constraint on `R₀ + R₂` stated through the
plain system alone: `min {I(W; Y), I(W; Z)} + I(V; Z | W)`. -/
noncomputable def plainSecondUserBound (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (w : Ω → Wp) (v : Ω → Vp) : ℝ :=
  min (mutualInfoReal μ w y) (mutualInfoReal μ w z) + condMutualInfoReal μ v z w

private lemma add_min_zero_sub (a b : ℝ) : a + min 0 (b - a) = min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left (by linarith : (0 : ℝ) ≤ b - a), min_eq_left h]
    ring
  · rw [min_eq_right (by linarith : b - a ≤ (0 : ℝ)), min_eq_right h]
    ring

/-- At the diagonal witness the `R₀` constraint of the one-auxiliary-receiver bound is the one
stated through the plain system alone. -/
@[entry_point]
theorem singleAuxCommonBound_diagonal_eq_plainCommonBound (μ : Measure Ω)
    (y : Ω → B₁) (z : Ω → B₂) (w : Ω → Wp) :
    singleAuxCommonBound μ y z w w w = plainCommonBound μ y z w := by
  simp [singleAuxCommonBound, plainCommonBound, min_self]

/-- At the diagonal witness the `R₀ + R₁` constraint centered on the second enhanced system is
the one stated through the plain system alone, for every auxiliary receiver output. -/
@[entry_point]
theorem singleAuxFirstUserBound_diagonal_eq_plainFirstUserBound (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D) (w : Ω → Wp) (u : Ω → Up) :
    singleAuxFirstUserBound μ y z j w w w u = plainFirstUserBound μ y z w u := by
  rw [singleAuxFirstUserBound_eq_jFree μ y z j w w w u (by ring)]
  unfold singleAuxFirstUserBoundJFree plainFirstUserBound
  rw [add_min_zero_sub]

/-- At the diagonal witness the `R₀ + R₁` constraint centered on the first enhanced system is
the one stated through the plain system alone, for every auxiliary receiver output. -/
@[entry_point]
theorem singleAuxFirstUserBoundFromZ_diagonal_eq_plainFirstUserBound (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D) (w : Ω → Wp) (u : Ω → Up) :
    singleAuxFirstUserBoundFromZ μ y z j w w u w u = plainFirstUserBound μ y z w u := by
  rw [singleAuxFirstUserBoundFromZ_eq_jFree μ y z j w u w u w u (by ring) (by ring)]
  unfold singleAuxFirstUserBoundFromZJFree plainFirstUserBound
  rw [add_min_zero_sub, min_comm (mutualInfoReal μ w z) (mutualInfoReal μ w y)]
  ring

/-- At the diagonal witness the `R₀ + R₂` constraint that carries the first enhanced system in
its tail is the one stated through the plain system alone, for every auxiliary receiver
output. -/
@[entry_point]
theorem singleAuxSecondUserBound_diagonal_eq_plainSecondUserBound (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D) (w : Ω → Wp) (v : Ω → Vp) :
    singleAuxSecondUserBound μ y z j w w v w v = plainSecondUserBound μ y z w v := by
  rw [singleAuxSecondUserBound_eq_jFree μ y z j w v w v w v (by ring) (by ring)]
  unfold singleAuxSecondUserBoundJFree plainSecondUserBound
  rw [add_min_zero_sub]
  ring

/-- At the diagonal witness the `R₀ + R₂` constraint centered on the first enhanced system is
the one stated through the plain system alone, for every auxiliary receiver output. -/
@[entry_point]
theorem singleAuxSecondUserBoundFromZ_diagonal_eq_plainSecondUserBound (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (y : Ω → B₁) (z : Ω → B₂) (j : Ω → D) (w : Ω → Wp) (v : Ω → Vp) :
    singleAuxSecondUserBoundFromZ μ y z j w w v w = plainSecondUserBound μ y z w v := by
  rw [singleAuxSecondUserBoundFromZ_eq_jFree μ y z j w w v w (by ring)]
  unfold singleAuxSecondUserBoundFromZJFree plainSecondUserBound
  rw [add_min_zero_sub, min_comm (mutualInfoReal μ w z) (mutualInfoReal μ w y)]

end Transport

end InformationTheory.Shannon.BroadcastChannel

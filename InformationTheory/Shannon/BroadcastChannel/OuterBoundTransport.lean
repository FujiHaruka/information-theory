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

## Main definitions

* `singleAuxCommonBound`, `singleAuxFirstUserBound`, `singleAuxSecondUserBound` — the
  right-hand sides of the one-auxiliary-receiver constraints on `R₀`, on `R₀ + R₁` and on
  `R₀ + R₂` that participate in the comparison.
* `twoAuxCommonBound`, `twoAuxFirstUserBound`, `twoAuxFirstUserBoundInput`,
  `twoAuxSecondUserBound`, `twoAuxSecondUserBoundInput` — the five right-hand sides of the
  two-auxiliary-receiver bound at `(const, X)`.

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

None of the five uses the compatibility conditions tying the three systems of the
one-auxiliary-receiver bound together; the chain rule and the data processing inequality
suffice.

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

/-- Mutual information as a real number. -/
noncomputable def mutualInfoReal (μ : Measure Ω) (f : Ω → S) (g : Ω → T) : ℝ :=
  (mutualInfo μ f g).toReal

/-- Conditional mutual information as a real number. -/
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

end Transport

end InformationTheory.Shannon.BroadcastChannel

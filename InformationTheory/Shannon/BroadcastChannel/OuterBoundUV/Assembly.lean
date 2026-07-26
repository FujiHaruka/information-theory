import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Operational
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Bridge
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Broadcast channel — the UV outer region as a subset of the plane

The four information slots of the UV outer bound are functionals of a five-tuple law
`(U, V, X, Y₁, Y₂)` and do not mention the channel.  A region defined as the union of the
resulting quadrilaterals over *all* five-tuple laws would therefore be the whole plane: a law
that copies the input into the outputs makes every slot as large as the input alphabet allows,
whatever the channel is.  The union is therefore indexed by the laws whose output pair is
generated from the input letter by the channel and by nothing else, which is one composition
product identity, `IsUVChannelLaw`.

## Main definitions

* `IsUVChannelLaw W ν` — the conditional law of the output pair `(Y₁, Y₂)` given the two
  auxiliaries and the input letter `(U, V, X)` is `W X`.  This says at once that the output law
  is the channel and that the auxiliaries reach the outputs only through the input letter.
* `uvRegion ν` — the quadrilateral cut out by the four information slots of a five-tuple law.
* `bcOuterRegionUV W` — the UV outer region: the closure of the union of `uvRegion ν` over the
  channel laws `ν` on a fixed pair of countable auxiliary alphabets.

## Main statements

* `bcOuterRegionUV_isClosed` — the region is closed.
* `bcOuterRegionUV_nonempty` — the region is nonempty, so the union is indexed by a nonempty
  family of channel laws.
* `IsUVChannelLaw.map_input_output` — a channel law has the channel joint `(ν.map X) ⊗ₘ W` as
  its input-output pair law, which is what a law copying the input into the output fails.
* `IsUVChannelLaw.smul`, `IsUVChannelLaw.add` — mixtures of channel laws are channel laws, so
  averaging the letter laws of a code stays inside the index of the union.
* `IsUVChannelLaw.map_auxiliaries` — re-encoding the two auxiliary alphabets keeps a channel
  law a channel law, which is how a law on the auxiliaries of a code reaches the fixed ones.
* `bcUVJointDistribution_isUVChannelLaw` — the letter-`i` law of a broadcast code is a channel
  law, so the letter laws of a code index the union.
* `bc_uv_shrunk_point_mem` — the rate pair of a code, shrunk by the Fano slack per letter, lies
  in the region.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α : Type*} [MeasurableSpace α]
variable {β₁ : Type*} [MeasurableSpace β₁]
variable {β₂ : Type*} [MeasurableSpace β₂]
variable {M₁ M₂ n : ℕ}

/-! ## Channel laws of a five-tuple -/

section ChannelLaw

variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]

/-- A five-tuple law `(U, V, X, Y₁, Y₂)` is a channel law for `W` when the conditional law of the
output pair given the two auxiliaries and the input letter is `W X`: pushing the law forward to
the pair `((U, V, X), (Y₁, Y₂))` gives the composition product of the `(U, V, X)` marginal with
`W` read at the input coordinate.

The identity carries both constraints that keep the region proper.  Taking the `(U, V)` component
of the first factor away leaves the input-output pair law `(ν.map X) ⊗ₘ W`, so the outputs are
distributed by the channel; keeping it says that the conditional law does not depend on the
auxiliaries, so they act on the outputs only through the input letter.

The identity pins the law exactly: it holds if and only if `ν` is the composition product of its
own `(U, V, X)` marginal with the channel read at the input letter, so the union is indexed by
the laws obtained from an arbitrary law of `(U, V, X)` through the channel and by nothing else.
@audit:ok -/
def IsUVChannelLaw (W : BCChannel α β₁ β₂) (ν : Measure (U × V × α × β₁ × β₂)) : Prop :=
  ν.map (fun q ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2))
    = (ν.map fun q ↦ (q.1, q.2.1, q.2.2.1)) ⊗ₘ
        W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)

/-- @audit:ok -/
lemma compProd_comap_map_prodMap {A A' B : Type*} [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] (μ : Measure A) [SFinite μ] (κ : Kernel A' B) [IsMarkovKernel κ]
    {g : A → A'} (hg : Measurable g) :
    (μ ⊗ₘ κ.comap g hg).map (fun z ↦ (g z.1, z.2)) = (μ.map g) ⊗ₘ κ := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hmap : Measurable (fun z : A × B ↦ (g z.1, z.2)) :=
    (hg.comp measurable_fst).prodMk measurable_snd
  have hin : Measurable (fun a : A' ↦ ∫⁻ b, f (a, b) ∂(κ a)) :=
    Measurable.lintegral_kernel_prod_right' (κ := κ) hf
  have hcomp : Measurable (fun z : A × B ↦ f (g z.1, z.2)) := hf.comp hmap
  rw [lintegral_map hf hmap, Measure.lintegral_compProd hcomp,
    Measure.lintegral_compProd hf, lintegral_map hin hg]
  rfl

private lemma measurable_uvFirstThree :
    Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.comp (measurable_snd.comp measurable_snd)))

private lemma measurable_uvSplit :
    Measurable (fun q : U × V × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) :=
  measurable_uvFirstThree.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))

/-- @audit:ok -/
lemma IsUVChannelLaw.smul {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)}
    [SFinite ν] (h : IsUVChannelLaw W ν) (a : ℝ≥0∞) : IsUVChannelLaw W (a • ν) := by
  unfold IsUVChannelLaw at h ⊢
  rw [Measure.map_smul, Measure.map_smul, h, Measure.compProd_smul_left]

/-- @audit:ok -/
lemma IsUVChannelLaw.add {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    {ν₁ ν₂ : Measure (U × V × α × β₁ × β₂)}
    [SFinite ν₁] [SFinite ν₂] (h₁ : IsUVChannelLaw W ν₁) (h₂ : IsUVChannelLaw W ν₂) :
    IsUVChannelLaw W (ν₁ + ν₂) := by
  unfold IsUVChannelLaw at h₁ h₂ ⊢
  rw [Measure.map_add _ _ measurable_uvSplit, Measure.map_add _ _ measurable_uvFirstThree,
    h₁, h₂, Measure.compProd_add_left]

/-- @audit:ok -/
lemma IsUVChannelLaw.map_auxiliaries {U' V' : Type*} [MeasurableSpace U'] [MeasurableSpace V']
    {W : BCChannel α β₁ β₂} [IsMarkovKernel W] {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν]
    (h : IsUVChannelLaw W ν) {f : U → U'} {g : V → V'} (hf : Measurable f) (hg : Measurable g) :
    IsUVChannelLaw W (ν.map fun q ↦ (f q.1, g q.2.1, q.2.2)) := by
  have hφ : Measurable (fun r : U × V × α ↦ (f r.1, g r.2.1, r.2.2)) :=
    (hf.comp measurable_fst).prodMk
      ((hg.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have hψ : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (f q.1, g q.2.1, q.2.2)) :=
    (hf.comp measurable_fst).prodMk
      ((hg.comp (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
  have hprod : Measurable (fun z : (U × V × α) × (β₁ × β₂) ↦
      ((f z.1.1, g z.1.2.1, z.1.2.2), z.2)) := (hφ.comp measurable_fst).prodMk measurable_snd
  have hkernel : W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)
      = (W.comap (fun r : U' × V' × α ↦ r.2.2) (measurable_snd.comp measurable_snd)).comap
        (fun r : U × V × α ↦ (f r.1, g r.2.1, r.2.2)) hφ := Kernel.ext fun _ ↦ rfl
  unfold IsUVChannelLaw at h ⊢
  rw [Measure.map_map measurable_uvSplit hψ, Measure.map_map measurable_uvFirstThree hψ]
  have hcong := congrArg (Measure.map (fun z : (U × V × α) × (β₁ × β₂) ↦
    ((f z.1.1, g z.1.2.1, z.1.2.2), z.2))) h
  rw [Measure.map_map hprod measurable_uvSplit, hkernel,
    compProd_comap_map_prodMap (ν.map fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1))
      (W.comap (fun r : U' × V' × α ↦ r.2.2) (measurable_snd.comp measurable_snd)) hφ,
    Measure.map_map hφ measurable_uvFirstThree] at hcong
  exact hcong

/-- @audit:ok -/
lemma IsUVChannelLaw.map_input_output {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) :
    ν.map (fun q ↦ (q.2.2.1, q.2.2.2)) = (ν.map fun q ↦ q.2.2.1) ⊗ₘ W := by
  have hg : Measurable (fun r : U × V × α ↦ r.2.2) := measurable_snd.comp measurable_snd
  have hπ : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hP : Measurable (fun q : U × V × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) :=
    hπ.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hmap : Measurable (fun z : (U × V × α) × (β₁ × β₂) ↦ (z.1.2.2, z.2)) :=
    (hg.comp measurable_fst).prodMk measurable_snd
  have hcong := congrArg (Measure.map (fun z : (U × V × α) × (β₁ × β₂) ↦ (z.1.2.2, z.2))) h
  rw [Measure.map_map hmap hP,
    compProd_comap_map_prodMap (ν.map fun q ↦ (q.1, q.2.1, q.2.2.1)) W hg,
    Measure.map_map hg hπ] at hcong
  exact hcong

end ChannelLaw

/-! ## The UV outer region -/

section Region

variable [StandardBorelSpace α] [Nonempty α]
variable [StandardBorelSpace β₁] [Nonempty β₁]
variable [StandardBorelSpace β₂] [Nonempty β₂]

/-- The quadrilateral of a five-tuple law: the rate pairs satisfying the two corner bounds and
the two sum-rate bounds of `InBCOuterRegionUV` at the four information slots of the law.  No sign
constraint is imposed, matching the operational region, which contains nonpositive rate pairs.
@audit:ok -/
def uvRegion {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] : Set (ℝ × ℝ) :=
  {p | InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal
    (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}

/-- The UV (Nair–El Gamal) outer region of a broadcast channel: the closure of the union of the
quadrilaterals `uvRegion ν` over the channel laws `ν` of `W`.

Both auxiliary alphabets are fixed to `ℕ`, which quantifies over every countable auxiliary
without quantifying over types.  The closure is taken because a union of closed half-plane
intersections need not be closed, and because the operational region is itself a closure.
@audit:ok -/
def bcOuterRegionUV (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂))
    (_ : IsUVChannelLaw W (ν : Measure (ℕ × ℕ × α × β₁ × β₂))),
      uvRegion (ν : Measure (ℕ × ℕ × α × β₁ × β₂)))

/-- @audit:ok -/
theorem bcOuterRegionUV_isClosed (W : BCChannel α β₁ β₂) : IsClosed (bcOuterRegionUV W) :=
  isClosed_closure

/-- The five-tuple law with constant auxiliaries and a constant input letter `x₀`, whose output
pair is drawn from `W x₀`.
@audit:ok -/
noncomputable def uvConstLaw (W : BCChannel α β₁ β₂) (x₀ : α) :
    Measure (ℕ × ℕ × α × β₁ × β₂) :=
  ((Measure.dirac ((0 : ℕ), (0 : ℕ), x₀)) ⊗ₘ
      W.comap (fun r : ℕ × ℕ × α ↦ r.2.2) (measurable_snd.comp measurable_snd)).map
    (fun z ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2))

omit [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β₁] [Nonempty β₁]
  [StandardBorelSpace β₂] [Nonempty β₂] in
private lemma measurable_uvUnassoc :
    Measurable (fun z : (ℕ × ℕ × α) × (β₁ × β₂) ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2)) :=
  (measurable_fst.comp measurable_fst).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))))

instance uvConstLaw_isProbabilityMeasure (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (x₀ : α) :
    IsProbabilityMeasure (uvConstLaw W x₀) := by
  unfold uvConstLaw
  exact Measure.isProbabilityMeasure_map measurable_uvUnassoc.aemeasurable

omit [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β₁] [Nonempty β₁]
  [StandardBorelSpace β₂] [Nonempty β₂] in
/-- @audit:ok -/
lemma uvConstLaw_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (x₀ : α) :
    IsUVChannelLaw W (uvConstLaw W x₀) := by
  have hg : Measurable (fun r : ℕ × ℕ × α ↦ r.2.2) := measurable_snd.comp measurable_snd
  have hπ : Measurable (fun q : ℕ × ℕ × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hP : Measurable (fun q : ℕ × ℕ × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) :=
    hπ.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hcomp₁ : (fun q : ℕ × ℕ × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) ∘
      (fun z : (ℕ × ℕ × α) × (β₁ × β₂) ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2)) = id := rfl
  have hcomp₂ : (fun q : ℕ × ℕ × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) ∘
      (fun z : (ℕ × ℕ × α) × (β₁ × β₂) ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2))
      = Prod.fst := rfl
  unfold IsUVChannelLaw uvConstLaw
  rw [Measure.map_map hP measurable_uvUnassoc, Measure.map_map hπ measurable_uvUnassoc,
    hcomp₁, hcomp₂, Measure.map_id,
    show (Measure.dirac ((0 : ℕ), (0 : ℕ), x₀) ⊗ₘ
        W.comap (fun r : ℕ × ℕ × α ↦ r.2.2) hg).map Prod.fst
      = Measure.dirac ((0 : ℕ), (0 : ℕ), x₀) from Measure.fst_compProd _ _]

/-- @audit:ok -/
theorem bcOuterRegionUV_nonempty (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (bcOuterRegionUV W).Nonempty := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty α)
  refine ⟨(0, 0), subset_closure (Set.mem_iUnion.mpr ⟨⟨uvConstLaw W x₀, inferInstance⟩,
    Set.mem_iUnion.mpr ⟨uvConstLaw_isUVChannelLaw W x₀, ?_, ?_, ?_, ?_⟩⟩)⟩ <;>
    simp

end Region

/-! ## The letter laws of a code are channel laws -/

section CodeLaw

/-- @audit:ok -/
lemma compProd_pi_map_pair_eq_of_update_invariant
    {M A B C : Type*} [MeasurableSpace M] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] {k : ℕ}
    (ν : Measure M) [IsProbabilityMeasure ν]
    (x : M → Fin k → A)
    (W : Kernel A B) [IsMarkovKernel W]
    (κ : Kernel M (Fin k → B)) [IsMarkovKernel κ]
    (hκ : ∀ m, κ m = Measure.pi (fun j ↦ W (x m j))) (i : Fin k)
    (G : M × (Fin k → B) → C) (hG : Measurable G)
    (hGupd : ∀ (m : M) (y : Fin k → B) (b : B), G (m, Function.update y i b) = G (m, y))
    (g : C → A) (hg : Measurable g) (hgG : ∀ ω, g (G ω) = x ω.1 i) :
    (ν ⊗ₘ κ).map (fun ω ↦ (G ω, ω.2 i)) = ((ν ⊗ₘ κ).map G) ⊗ₘ (W.comap g hg) := by
  have hYo : Measurable (fun ω : M × (Fin k → B) ↦ ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hpair : Measurable (fun ω : M × (Fin k → B) ↦ (G ω, ω.2 i)) := hG.prodMk hYo
  have hlhs : Measurable (fun ω : M × (Fin k → B) ↦ f (G ω, ω.2 i)) := hf.comp hpair
  have hin : Measurable (fun c : C ↦ ∫⁻ b, f (c, b) ∂((W.comap g hg) c)) :=
    Measurable.lintegral_kernel_prod_right' (κ := W.comap g hg) hf
  have hrhs : Measurable
      (fun ω : M × (Fin k → B) ↦ ∫⁻ b, f (G ω, b) ∂((W.comap g hg) (G ω))) := hin.comp hG
  rw [lintegral_map hf hpair, Measure.lintegral_compProd hf, lintegral_map hin hG,
    Measure.lintegral_compProd hlhs, Measure.lintegral_compProd hrhs]
  refine lintegral_congr fun m ↦ ?_
  rw [hκ]
  have hFm : Measurable (fun y : Fin k → B ↦ f (G (m, y), y i)) :=
    hf.comp ((hG.comp (measurable_const.prodMk measurable_id)).prodMk (measurable_pi_apply i))
  rw [lintegral_pi_reRandomize (fun j ↦ W (x m j)) i (fun y ↦ f (G (m, y), y i)) hFm]
  refine lintegral_congr fun y ↦ ?_
  have hker : (W.comap g hg) (G (m, y)) = W (x m i) := by
    rw [Kernel.comap_apply, hgG (m, y)]
  rw [hker]
  exact lintegral_congr fun b ↦ by rw [hGupd m y b, Function.update_self i b y]

variable [Nonempty β₁] [Nonempty β₂]

/-- @audit:ok -/
theorem bcUVJointDistribution_isUVChannelLaw
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    IsUVChannelLaw W (bcUVJointDistribution c W i) := by
  set U := Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂) with hU_def
  set V := Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂) with hV_def
  set G : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → U × V × α :=
    fun ω ↦ (uvAuxPad bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i ω,
      uvAuxPad bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i ω, c.encoder ω.1 i) with hG_def
  have hg : Measurable (fun r : U × V × α ↦ r.2.2) := measurable_snd.comp measurable_snd
  have hGm : Measurable G :=
    (measurable_uvAuxPad bcConverseMsg₂ bcConverseY₁s bcConverseY₂s measurable_bcConverseMsg₂
        measurable_bcConverseY₁s measurable_bcConverseY₂s i).prodMk
      ((measurable_uvAuxPad bcConverseMsg₁ bcConverseY₁s bcConverseY₂s measurable_bcConverseMsg₁
          measurable_bcConverseY₁s measurable_bcConverseY₂s i).prodMk
        ((measurable_pi_apply i).comp ((measurable_of_countable c.encoder).comp measurable_fst)))
  have hGupd : ∀ (m : Fin M₁ × Fin M₂) (y : Fin n → β₁ × β₂) (b : β₁ × β₂),
      G (m, Function.update y i b) = G (m, y) := by
    intro m y b
    have hpre : ∀ j : Fin i.val,
        bcConverseY₁s (M₁ := M₁) (M₂ := M₂) ⟨j.val, j.isLt.trans i.isLt⟩
            (m, Function.update y i b)
          = bcConverseY₁s ⟨j.val, j.isLt.trans i.isLt⟩ (m, y) := fun j ↦
      congrArg Prod.fst
        (Function.update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt j.isLt)) b y)
    have hsuf : ∀ j : {j : Fin n // i.val < j.val},
        bcConverseY₂s (M₁ := M₁) (M₂ := M₂) j.val (m, Function.update y i b)
          = bcConverseY₂s j.val (m, y) := fun j ↦
      congrArg Prod.snd
        (Function.update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt j.2).symm) b y)
    have haux₂ : uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i (m, Function.update y i b)
        = uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i (m, y) :=
      Prod.ext rfl (Prod.ext (funext hpre) (funext hsuf))
    have haux₁ : uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i (m, Function.update y i b)
        = uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i (m, y) :=
      Prod.ext rfl (Prod.ext (funext hpre) (funext hsuf))
    exact Prod.ext (congrArg (uvPadMap i) haux₂)
      (Prod.ext (congrArg (uvPadMap i) haux₁) rfl)
  have hπ : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hP : Measurable (fun q : U × V × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) :=
    hπ.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have key := compProd_pi_map_pair_eq_of_update_invariant (bcConverseInput M₁ M₂) c.encoder W
    (bcConverseKernel c W) (fun m ↦ rfl) i G hGm hGupd (fun r : U × V × α ↦ r.2.2) hg
    (fun _ ↦ rfl)
  unfold IsUVChannelLaw bcUVJointDistribution
  rw [Measure.map_map hP (measurable_bcUVTuple c i),
    Measure.map_map hπ (measurable_bcUVTuple c i)]
  exact key

end CodeLaw

/-! ## The channel constraint is not vacuous

The information slots do not mention the channel, so a five-tuple law that copies the input
letter into both outputs carries a full input alphabet of information in every slot no matter
which channel indexes the region.  Copying laws exist over every alphabet, so dropping the
constraint would let the union exhaust the plane.  The law below copies a uniform bit into both
outputs and is rejected over the channel that always outputs `(false, false)`. -/

example :
    ¬ IsUVChannelLaw (α := Bool) (β₁ := Bool) (β₂ := Bool)
        (Kernel.const Bool (Measure.dirac (false, false)))
        (((Fintype.card Bool : ℝ≥0∞)⁻¹ • Measure.count : Measure Bool).map
          fun b ↦ ((b, b, b, b, b) : Bool × Bool × Bool × Bool × Bool)) := by
  intro h
  set μ : Measure Bool := (Fintype.card Bool : ℝ≥0∞)⁻¹ • Measure.count with hμ_def
  have hcopy : Measurable fun b : Bool ↦ ((b, b, b, b, b) : Bool × Bool × Bool × Bool × Bool) :=
    measurable_of_countable _
  haveI : IsProbabilityMeasure (μ.map fun b : Bool ↦
      ((b, b, b, b, b) : Bool × Bool × Bool × Bool × Bool)) :=
    Measure.isProbabilityMeasure_map hcopy.aemeasurable
  have hout := h.map_input_output
  rw [Measure.map_map (measurable_of_countable _) hcopy,
    Measure.map_map (measurable_of_countable _) hcopy] at hout
  have hS : MeasurableSet {p : Bool × Bool × Bool | p.2 = (true, true)} :=
    measurable_snd (measurableSet_singleton (true, true))
  have hval := congrArg (fun ρ : Measure (Bool × Bool × Bool) ↦
    ρ {p : Bool × Bool × Bool | p.2 = (true, true)}) hout
  rw [Measure.map_apply (measurable_of_countable _) hS, Measure.compProd_apply hS] at hval
  simp only [Function.comp_def] at hval
  have hleft : μ ((fun b : Bool ↦ (b, b, b)) ⁻¹' {p : Bool × Bool × Bool | p.2 = (true, true)})
      = (2 : ℝ≥0∞)⁻¹ := by
    have hset : (fun b : Bool ↦ (b, b, b)) ⁻¹' {p : Bool × Bool × Bool | p.2 = (true, true)}
        = {true} := by
      ext b; cases b <;> simp
    rw [hset, hμ_def]
    simp
  have hright : ∫⁻ a : Bool, (Kernel.const Bool (Measure.dirac ((false, false) : Bool × Bool))) a
      (Prod.mk a ⁻¹' {p : Bool × Bool × Bool | p.2 = (true, true)})
      ∂(μ.map fun b : Bool ↦ b) = 0 := by
    simp [Kernel.const_apply, Measure.dirac_apply']
  rw [hleft, hright] at hval
  exact (ENNReal.inv_ne_zero.mpr (by norm_num)) hval

/-! ## Time sharing -/

section TimeSharing

variable [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
variable [Fintype β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁]
variable [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂]

/-- The rate pair of a broadcast code, shrunk by the per-letter Fano slack, lies in the UV outer
region.  The letter index is absorbed into the auxiliaries, which already carry it, so the
average of the letter laws is again a channel law and dominates the per-letter averages of all
four information slots.
@residual(plan:bc-general-region-plan) -/
theorem bc_uv_shrunk_point_mem
    [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) {R₁ R₂ : ℝ}
    (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
    (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂) :
    (R₁ - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) / (n : ℝ),
      R₂ - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) / (n : ℝ))
      ∈ bcOuterRegionUV W := by
  sorry

end TimeSharing

end InformationTheory.Shannon.BroadcastChannel

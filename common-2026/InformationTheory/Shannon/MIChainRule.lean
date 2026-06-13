import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.Entropy

/-!
# Mutual information chain rule (n-variable) and i.i.d. corollary

`MeasurableEquiv` invariance, the n-variable chain rule, additivity under product
distributions, and the entropy-MI bridge identity.

## Main statements

* `mutualInfo_map_left_measurableEquiv` — `I(e ∘ X; Y) = I(X; Y)`.
* `mutualInfo_chain_rule_fin` — `I(X_0, …, X_{n-1}; Y) = ∑ i, I(X_i; Y | X_0, …, X_{i-1})`.
* `mutualInfo_pi_eq_sum` — `I(X^n; Y^n) = ∑ I(X_i; Y_i)` under product joint distribution.
* `mutualInfo_iid_eq_nsmul` — `I(X^n; Y^n) = n · I(X_0; Y_0)` for i.i.d. pairs.
* `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy` — `I(X; Y) = H(X) + H(Y) − H(X, Y)`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-! ## `mutualInfo` invariance under `MeasurableEquiv` reshape -/

/-- Mutual information is invariant under a `MeasurableEquiv` reshape of the left
random variable: `I(e ∘ X; Y) = I(X; Y)`. Reduces to `klDiv_map_measurableEquiv`
applied to the product equivalence `e × id`. -/
@[entry_point]
theorem mutualInfo_map_left_measurableEquiv
    {X' : Type*} [MeasurableSpace X']
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo)
    (e : X ≃ᵐ X') :
    mutualInfo μ (fun ω => e (Xs ω)) Yo = mutualInfo μ Xs Yo := by
  unfold mutualInfo
  let eProd : X × Y ≃ᵐ X' × Y := MeasurableEquiv.prodCongr e (.refl Y)
  -- joint side
  have h_joint :
      (μ.map (fun ω => (Xs ω, Yo ω))).map eProd
        = μ.map (fun ω => (e (Xs ω), Yo ω)) := by
    rw [Measure.map_map eProd.measurable (hXs.prodMk hYo)]
    rfl
  -- marginal side: ((μ.map Xs).prod (μ.map Yo)).map (e × id) = (μ.map (e∘Xs)).prod (μ.map Yo)
  have h_marg :
      ((μ.map Xs).prod (μ.map Yo)).map eProd
        = (μ.map (fun ω => e (Xs ω))).prod (μ.map Yo) := by
    have h_e_Xs : (μ.map Xs).map e = μ.map (fun ω => e (Xs ω)) := by
      rw [Measure.map_map e.measurable hXs]; rfl
    have h_id : (μ.map Yo).map (id : Y → Y) = μ.map Yo := Measure.map_id
    -- (Measure.map_prod_map): (map f μa).prod (map g μc) = map (Prod.map f g) (μa.prod μc)
    have h_step : ((μ.map Xs).map e).prod ((μ.map Yo).map (id : Y → Y))
        = ((μ.map Xs).prod (μ.map Yo)).map (Prod.map e id) :=
      Measure.map_prod_map (μ.map Xs) (μ.map Yo) e.measurable measurable_id
    -- eProd as a function is Prod.map e id
    have h_eProd_eq : (eProd : X × Y → X' × Y) = Prod.map e id := rfl
    rw [h_eProd_eq, ← h_step, h_e_Xs, h_id]
  rw [← h_joint, ← h_marg, klDiv_map_measurableEquiv]


/-! ## n-variable chain rule -/

section ChainRuleFin

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Nonempty α]

/-- n-variable chain rule for mutual information:
`I(X_0, …, X_{n-1}; Y) = ∑ i, I(X_i; Y | (X_0, …, X_{i-1}))`.

Induction on `n`. base `n=0`: LHS = `mutualInfo` of a constant `Fin 0 → α`-valued RV,
which is independent of anything ⇒ 0; RHS is the empty sum. step `n+1`: split via
`MeasurableEquiv.piFinSuccAbove (Fin.last n)` so that `Fin (n+1) → α ≃ᵐ α × (Fin n → α)`,
then `prodComm` so we land on `(prefix, last)`, apply Phase A reshape, then the
2-variable `mutualInfo_chain_rule` (`CondMutualInfo.lean:219`) with `Zc := prefix`,
`Xs_arg := last`, then IH on the `Fin n` prefix, then `Fin.sum_univ_castSucc`. -/
@[entry_point]
theorem mutualInfo_chain_rule_fin
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (Yo : Ω → Y) (hYo : Measurable Yo) :
    mutualInfo μ (fun ω i => Xs i ω) Yo
      = ∑ i : Fin n,
          condMutualInfo μ (Xs i) Yo
            (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) := by
  induction n with
  | zero =>
    -- RHS: empty sum
    rw [Fin.sum_univ_zero]
    -- LHS: I(pi-X; Y) = 0 because pi-X is a Fin 0 → α constant (one-point space).
    have hjoint : Measurable (fun ω (i : Fin 0) => Xs i ω) :=
      measurable_pi_iff.mpr (fun i => Fin.elim0 i)
    haveI : Unique (Fin 0 → α) := Pi.uniqueOfIsEmpty _
    have h_indep : IndepFun (fun ω (i : Fin 0) => Xs i ω) Yo μ := by
      refine (indepFun_iff_map_prod_eq_prod_map_map hjoint.aemeasurable
        hYo.aemeasurable).mpr ?_
      apply Measure.ext
      intro s hs
      -- Slice by the unique element of (Fin 0 → α): s = {default} ×ˢ (slice).
      have h_eq_slice : ∀ s : Set ((Fin 0 → α) × Y),
          s = ({default} : Set (Fin 0 → α)) ×ˢ (Prod.mk (default : Fin 0 → α) ⁻¹' s) := by
        intro s
        ext ⟨f, y⟩
        have hf : f = default := Subsingleton.elim f default
        simp [hf, Set.mem_prod]
      have h_slice_meas : MeasurableSet ((Prod.mk (default : Fin 0 → α)) ⁻¹' s) :=
        measurable_prodMk_left hs
      have h_singleton : MeasurableSet ({default} : Set (Fin 0 → α)) :=
        measurableSet_singleton _
      conv_lhs => rw [h_eq_slice s]
      conv_rhs => rw [h_eq_slice s]
      rw [Measure.prod_prod]
      rw [Measure.map_apply (hjoint.prodMk hYo) (h_singleton.prod h_slice_meas)]
      have h_set_eq :
          (fun ω => ((fun (i : Fin 0) => Xs i ω), Yo ω)) ⁻¹'
              (({default} : Set (Fin 0 → α)) ×ˢ
                (Prod.mk (default : Fin 0 → α) ⁻¹' s))
            = Yo ⁻¹' (Prod.mk (default : Fin 0 → α) ⁻¹' s) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
        refine ⟨fun h => h.2, fun h => ⟨Subsingleton.elim _ _, h⟩⟩
      rw [h_set_eq, ← Measure.map_apply hYo h_slice_meas]
      have hjoint_singleton : (μ.map (fun ω (i : Fin 0) => Xs i ω)) {default} = 1 := by
        rw [Measure.map_apply hjoint h_singleton]
        have h_univ : (fun ω (i : Fin 0) => Xs i ω) ⁻¹' ({default} : Set (Fin 0 → α))
            = Set.univ := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
          exact Subsingleton.elim _ _
        rw [h_univ, measure_univ]
      rw [hjoint_singleton, one_mul]
    exact (mutualInfo_eq_zero_iff_indep μ _ Yo hjoint hYo).mpr h_indep
  | succ n IH =>
    -- Setup: split Xs : Fin (n+1) → Ω → α into prefix f and last g.
    set f : Ω → (Fin n → α) := fun ω j => Xs j.castSucc ω with hf_def
    set g : Ω → α := Xs (Fin.last n) with hg_def
    have hf : Measurable f := measurable_pi_iff.mpr (fun j => hXs j.castSucc)
    have hg : Measurable g := hXs (Fin.last n)
    -- piFinSuccAbove (Fin.last n) : (Fin (n+1) → α) ≃ᵐ α × (Fin n → α).
    -- For each ω: ePi (pi-X ω) = (Xs (last n) ω, fun j => Xs j.castSucc ω) = (g ω, f ω).
    let ePi : (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) (Fin.last n)
    have h_ePi_eq : ∀ ω, ePi (fun i : Fin (n + 1) => Xs i ω) = (g ω, f ω) := by
      intro ω
      apply Prod.ext
      · rfl
      · funext j
        show Xs ((Fin.last n).succAbove j) ω = Xs j.castSucc ω
        rw [Fin.succAbove_last]
    have hpi_meas : Measurable (fun ω (i : Fin (n + 1)) => Xs i ω) :=
      measurable_pi_iff.mpr (fun i => hXs i)
    -- Apply Phase A reshape and prodComm to land on (f, g) form.
    have h_reshape :
        mutualInfo μ (fun ω (i : Fin (n + 1)) => Xs i ω) Yo
          = mutualInfo μ (fun ω => (f ω, g ω)) Yo := by
      -- Step 1: reshape pi-X to (g, f) via ePi
      have h_step1 :
          mutualInfo μ (fun ω => ePi (fun i : Fin (n + 1) => Xs i ω)) Yo
            = mutualInfo μ (fun ω (i : Fin (n + 1)) => Xs i ω) Yo :=
        mutualInfo_map_left_measurableEquiv μ
          (fun ω (i : Fin (n + 1)) => Xs i ω) Yo hpi_meas hYo ePi
      have h_gf_eq : (fun ω => ePi (fun i : Fin (n + 1) => Xs i ω))
          = fun ω => (g ω, f ω) := funext h_ePi_eq
      rw [h_gf_eq] at h_step1
      -- Step 2: reshape (g, f) to (f, g) via prodComm
      have h_step2 :
          mutualInfo μ (fun ω => MeasurableEquiv.prodComm (g ω, f ω)) Yo
            = mutualInfo μ (fun ω => (g ω, f ω)) Yo :=
        mutualInfo_map_left_measurableEquiv μ
          (fun ω => (g ω, f ω)) Yo (hg.prodMk hf) hYo MeasurableEquiv.prodComm
      have h_prodComm_eq : (fun ω => MeasurableEquiv.prodComm (g ω, f ω))
          = fun ω => (f ω, g ω) := by
        funext ω; rfl
      rw [h_prodComm_eq] at h_step2
      rw [← h_step1, ← h_step2]
    rw [h_reshape]
    -- Apply 2-variable chain rule with Zc := f, Xs_arg := g:
    -- I((f, g); Y) = I(f; Y) + I(g; Y | f).
    rw [mutualInfo_chain_rule μ g Yo f hg hYo hf]
    -- Apply IH to the prefix f = fun ω j => Xs j.castSucc ω.
    have IH' := IH (fun i ω => Xs i.castSucc ω) (fun i => hXs i.castSucc)
    have h_mi_f : mutualInfo μ f Yo
        = ∑ i : Fin n,
            condMutualInfo μ (Xs i.castSucc) Yo
              (fun ω (j : Fin i.val) =>
                Xs ⟨j.val, j.isLt.trans i.castSucc.isLt⟩ ω) := by
      convert IH' using 2
    rw [h_mi_f]
    -- Rewrite RHS via Fin.sum_univ_castSucc.
    rw [Fin.sum_univ_castSucc]
    -- Now: (∑ i:Fin n, condMI (Xs i.castSucc) Yo prefix) + condMI g Yo f
    --   = (∑ i:Fin n, condMI (Xs i.castSucc) Yo (...))
    --     + condMI (Xs (Fin.last n)) Yo (last-prefix)
    -- The last summand of the RHS at i = Fin.last n is condMI of Xs(last) given a Fin n-prefix.
    -- After IH rewrite + Fin.sum_univ_castSucc, the LHS sum already matches the RHS's
    -- castSucc-indexed part exactly (modulo `Fin (Fin.last n).val = Fin n`-prefix defeq).
    -- The remaining `condMutualInfo μ g Yo f` matches `condMutualInfo μ (Xs (last n)) Yo (last-prefix)`
    -- by `hg_def` + the prefix definitional equality.
    congr 1

end ChainRuleFin

/-! ## Phase C — i.i.d. corollary -/

section IID

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- KL divergence of product measures is additive: if both `μ₁, μ₂` are probability
measures on `α` and `ν₁, ν₂` are finite measures on `β`, then
`klDiv (μ₁.prod ν₁) (μ₂.prod ν₂) = klDiv μ₁ μ₂ + klDiv ν₁ ν₂`. Derived from
`klDiv_compProd_eq_add` (Mathlib) with constant kernels + `klDiv_prod_const_left`. -/
theorem klDiv_prod_eq_add
    {α' β' : Type*} [MeasurableSpace α'] [MeasurableSpace β']
    (μ₁ μ₂ : Measure α') [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (ν₁ ν₂ : Measure β') [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod ν₁) (μ₂.prod ν₂) = klDiv μ₁ μ₂ + klDiv ν₁ ν₂ := by
  -- Express both prods as compProd with const kernel.
  rw [← Measure.compProd_const (μ := μ₁) (ν := ν₁),
      ← Measure.compProd_const (μ := μ₂) (ν := ν₂)]
  -- Apply klDiv_compProd_eq_add.
  rw [klDiv_compProd_eq_add μ₁ μ₂ (Kernel.const _ ν₁) (Kernel.const _ ν₂)]
  -- Rewrite second term: μ₁ ⊗ₘ const ν_i = μ₁.prod ν_i, then apply klDiv_prod_const_left.
  rw [Measure.compProd_const, Measure.compProd_const, klDiv_prod_const_left]

/-- KL divergence of `Measure.pi` measures is additive over the index set:
`klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i, klDiv (μs i) (νs i)`.

Proven by induction on `n` using `measurePreserving_piFinSuccAbove` (to split
`Measure.pi` of length `n+1` into `μ_{last} × Measure.pi prefix`) +
`klDiv_map_measurableEquiv` + `klDiv_prod_eq_add` + `Fin.sum_univ_castSucc`. -/
theorem klDiv_pi_eq_sum
    {n : ℕ} {α' : Fin n → Type*} [∀ i, MeasurableSpace (α' i)]
    (μs νs : ∀ i, Measure (α' i))
    [∀ i, IsProbabilityMeasure (μs i)] [∀ i, IsProbabilityMeasure (νs i)] :
    klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i : Fin n, klDiv (μs i) (νs i) := by
  induction n with
  | zero =>
    rw [Fin.sum_univ_zero]
    -- (Fin 0 → α' i) is a singleton type, so Measure.pi is a probability measure
    -- on a singleton, hence both pi are equal as point measures.
    haveI : IsProbabilityMeasure (Measure.pi μs) := by infer_instance
    haveI : IsProbabilityMeasure (Measure.pi νs) := by infer_instance
    -- Two probability measures on a Subsingleton type are equal.
    haveI : Subsingleton ((i : Fin 0) → α' i) := ⟨fun a b => funext (fun i => Fin.elim0 i)⟩
    have h_eq : Measure.pi μs = Measure.pi νs := by
      apply Measure.ext
      intro s _
      by_cases hs : s.Nonempty
      · obtain ⟨x, hx⟩ := hs
        have : s = Set.univ := by
          ext y
          simp only [Set.mem_univ, iff_true]
          rwa [Subsingleton.elim y x]
        rw [this, measure_univ, measure_univ]
      · rw [Set.not_nonempty_iff_eq_empty.mp hs, measure_empty, measure_empty]
    rw [h_eq, klDiv_self]
  | succ n IH =>
    -- Use piFinSuccAbove with i = Fin.last n to split.
    let e : (∀ j, α' j) ≃ᵐ α' (Fin.last n) × ∀ j : Fin n, α' ((Fin.last n).succAbove j) :=
      MeasurableEquiv.piFinSuccAbove α' (Fin.last n)
    -- Setup the pi measures over the "rest" indices.
    have h_succAbove : ∀ j : Fin n, (Fin.last n).succAbove j = j.castSucc := fun j =>
      Fin.succAbove_last_apply j
    -- Use measurePreserving_piFinSuccAbove to push pi measures through e.
    have hmp_μ := measurePreserving_piFinSuccAbove μs (Fin.last n)
    have hmp_ν := measurePreserving_piFinSuccAbove νs (Fin.last n)
    -- (Measure.pi μs).map e = (μs last).prod (Measure.pi (μs ∘ last.succAbove))
    have h_map_μ : (Measure.pi μs).map e
        = (μs (Fin.last n)).prod (Measure.pi (fun j : Fin n => μs ((Fin.last n).succAbove j))) :=
      hmp_μ.map_eq
    have h_map_ν : (Measure.pi νs).map e
        = (νs (Fin.last n)).prod (Measure.pi (fun j : Fin n => νs ((Fin.last n).succAbove j))) :=
      hmp_ν.map_eq
    -- klDiv is invariant under e.
    have h_kl :
        klDiv (Measure.pi μs) (Measure.pi νs)
          = klDiv ((Measure.pi μs).map e) ((Measure.pi νs).map e) :=
      (klDiv_map_measurableEquiv e _ _).symm
    rw [h_kl, h_map_μ, h_map_ν, klDiv_prod_eq_add]
    -- klDiv (μs last) (νs last) + klDiv (Measure.pi μs_rest) (Measure.pi νs_rest)
    -- Apply IH to the rest.
    have IH' := IH (fun j : Fin n => μs ((Fin.last n).succAbove j))
      (fun j : Fin n => νs ((Fin.last n).succAbove j))
    rw [IH']
    -- Goal: klDiv (μs last) (νs last) + ∑ j, klDiv (μs (last.succAbove j)) (νs (last.succAbove j))
    --     = ∑ i : Fin (n+1), klDiv (μs i) (νs i)
    rw [Fin.sum_univ_castSucc, add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_succAbove j]

/-- MI additivity under product joint distribution: if the joint
`μ.map (fun ω i => (X_i ω, Y_i ω))` factors as the product `Measure.pi (i ↦ μ.map (X_i, Y_i))`
and the marginals factor similarly, then `I(X^n; Y^n) = ∑ I(X_i; Y_i)`.

Strategy: reshape via `MeasurableEquiv.arrowProdEquivProdArrow` so that both joint and
product-of-marginals (defining `mutualInfo`) become `Measure.pi`-shaped, then apply
`klDiv_pi_eq_sum` to get the sum. -/
@[entry_point]
theorem mutualInfo_pi_eq_sum
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_iid_joint : μ.map (fun ω (i : Fin n) => (Xs i ω, Ys i ω))
                      = Measure.pi (fun i => μ.map (fun ω => (Xs i ω, Ys i ω))))
    (h_iid_X : μ.map (fun ω (i : Fin n) => Xs i ω)
                  = Measure.pi (fun i => μ.map (Xs i)))
    (h_iid_Y : μ.map (fun ω (i : Fin n) => Ys i ω)
                  = Measure.pi (fun i => μ.map (Ys i))) :
    mutualInfo μ (fun ω i => Xs i ω) (fun ω i => Ys i ω)
      = ∑ i : Fin n, mutualInfo μ (Xs i) (Ys i) := by
  unfold mutualInfo
  -- LHS: klDiv (μ.map (joint pair)) ((μ.map X^n).prod (μ.map Y^n))
  --   where joint pair = fun ω => (fun i => Xs i ω, fun i => Ys i ω) : Ω → (Fin n → α) × (Fin n → β)
  -- Reshape via arrowProdEquivProdArrow.
  let e : (Fin n → α × β) ≃ᵐ (Fin n → α) × (Fin n → β) :=
    MeasurableEquiv.arrowProdEquivProdArrow α β (Fin n)
  -- Joint side: μ.map (fun ω => ((fun i => Xs i ω), (fun i => Ys i ω)))
  --   = (μ.map (fun ω i => (Xs i ω, Ys i ω))).map e
  have h_joint_meas : Measurable (fun ω (i : Fin n) => (Xs i ω, Ys i ω)) :=
    measurable_pi_iff.mpr fun i => (hXs i).prodMk (hYs i)
  haveI : ∀ i, IsProbabilityMeasure (μ.map (fun ω => (Xs i ω, Ys i ω))) :=
    fun i => Measure.isProbabilityMeasure_map ((hXs i).prodMk (hYs i)).aemeasurable
  haveI : ∀ i, IsProbabilityMeasure (μ.map (Xs i)) :=
    fun i => Measure.isProbabilityMeasure_map (hXs i).aemeasurable
  haveI : ∀ i, IsProbabilityMeasure (μ.map (Ys i)) :=
    fun i => Measure.isProbabilityMeasure_map (hYs i).aemeasurable
  -- Lift joint via e: joint over Fin n → α × β reshapes to joint over (Fin n → α) × (Fin n → β)
  have h_joint_eq :
      μ.map (fun ω => ((fun i => Xs i ω), (fun i => Ys i ω)))
        = (μ.map (fun ω (i : Fin n) => (Xs i ω, Ys i ω))).map e := by
    rw [Measure.map_map e.measurable h_joint_meas]
    congr 1
  -- Marginal product via measurePreserving_arrowProdEquivProdArrow:
  -- (Measure.pi μ_i).prod (Measure.pi ν_i) = (Measure.pi (μ_i.prod ν_i)).map e
  have hmp := measurePreserving_arrowProdEquivProdArrow α β (Fin n)
    (fun i => μ.map (Xs i)) (fun i => μ.map (Ys i))
  have h_marg_prod_eq :
      (μ.map (fun ω (i : Fin n) => Xs i ω)).prod (μ.map (fun ω (i : Fin n) => Ys i ω))
        = (Measure.pi (fun i => (μ.map (Xs i)).prod (μ.map (Ys i)))).map e := by
    rw [h_iid_X, h_iid_Y, hmp.map_eq]
  -- Apply rewriting.
  rw [h_joint_eq, h_iid_joint, h_marg_prod_eq, klDiv_map_measurableEquiv]
  -- klDiv (Measure.pi joint_i) (Measure.pi marginal_prod_i) = ∑ klDiv joint_i marg_i
  rw [klDiv_pi_eq_sum]

/-- i.i.d. corollary: all `(X_i, Y_i)` jointly i.i.d. with common law implies
`I(X^n; Y^n) = n · I(X_0; Y_0)`. -/
@[entry_point]
theorem mutualInfo_iid_eq_nsmul
    {n : ℕ} (hn : 0 < n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_iid_joint : μ.map (fun ω (i : Fin n) => (Xs i ω, Ys i ω))
                      = Measure.pi (fun i => μ.map (fun ω => (Xs i ω, Ys i ω))))
    (h_iid_X : μ.map (fun ω (i : Fin n) => Xs i ω)
                  = Measure.pi (fun i => μ.map (Xs i)))
    (h_iid_Y : μ.map (fun ω (i : Fin n) => Ys i ω)
                  = Measure.pi (fun i => μ.map (Ys i)))
    (h_copy : ∀ i, μ.map (fun ω => (Xs i ω, Ys i ω))
                      = μ.map (fun ω => (Xs ⟨0, hn⟩ ω, Ys ⟨0, hn⟩ ω)))
    (h_copy_X : ∀ i, μ.map (Xs i) = μ.map (Xs ⟨0, hn⟩))
    (h_copy_Y : ∀ i, μ.map (Ys i) = μ.map (Ys ⟨0, hn⟩)) :
    mutualInfo μ (fun ω i => Xs i ω) (fun ω i => Ys i ω)
      = n • mutualInfo μ (Xs ⟨0, hn⟩) (Ys ⟨0, hn⟩) := by
  rw [mutualInfo_pi_eq_sum μ Xs Ys hXs hYs h_iid_joint h_iid_X h_iid_Y]
  -- Each summand equals mutualInfo μ (Xs ⟨0, hn⟩) (Ys ⟨0, hn⟩) by the copy hypotheses.
  have h_each : ∀ i : Fin n,
      mutualInfo μ (Xs i) (Ys i)
        = mutualInfo μ (Xs ⟨0, hn⟩) (Ys ⟨0, hn⟩) := by
    intro i
    unfold mutualInfo
    rw [h_copy i, h_copy_X i, h_copy_Y i]
  -- Sum of constant over Fin n.
  rw [Finset.sum_congr rfl (fun i _ => h_each i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end IID

/-! ## Phase D — entropy ↔ MI three-term bridge

For a joint probability measure on a finite-alphabet product space `α × β`, the standard
identity `I(X; Y) = H(X) + H(Y) − H(X, Y)` connects the `klDiv`-based `mutualInfo` to the
Shannon-entropy `entropy`. Used in B-3'' Phase D-(b) to rewrite the joint-AEP exponent
`H(X, Y) − H(X) − H(Y)` as `−I(p; W)`.
-/

section EntropyMIBridge

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

omit [DecidableEq α] [DecidableEq β] in
/-- **Mutual-information ↔ entropy three-term identity (joint-distribution level).**
For any probability measure `joint` on a finite-alphabet product `α × β`, the
`klDiv`-based mutual information of its coordinates equals the standard three-term
form `H(X) + H(Y) − H(X, Y)`, where `H(X, Y) := entropy joint id` is the joint
entropy on `α × β`.

Strategy: `mutualInfo_comm` to put `Prod.snd` first, then Bridge
`mutualInfo_eq_entropy_sub_condEntropy` to convert MI to entropy minus conditional
entropy; finally `entropy_pair_eq_entropy_add_condEntropy` applied to the identity
pair `(z.1, z.2) = z` to expand the joint entropy. -/
@[entry_point]
theorem mutualInfo_eq_entropy_add_entropy_sub_jointEntropy
    (joint : Measure (α × β)) [IsProbabilityMeasure joint] :
    (mutualInfo joint Prod.fst Prod.snd).toReal
      = entropy joint Prod.fst + entropy joint Prod.snd - entropy joint id := by
  classical
  -- Step 1: commute MI to put `Prod.snd` on the left.
  rw [mutualInfo_comm joint Prod.fst Prod.snd measurable_fst measurable_snd]
  -- Step 2: Bridge — (mutualInfo joint Prod.snd Prod.fst).toReal
  --   = entropy joint Prod.snd − condEntropy joint Prod.snd Prod.fst.
  rw [mutualInfo_eq_entropy_sub_condEntropy joint Prod.snd Prod.fst
        measurable_snd measurable_fst]
  -- Step 3: entropy chain rule — entropy joint id = entropy joint Prod.fst
  --   + condEntropy joint Prod.snd Prod.fst.
  have h_chain :
      entropy joint (fun z : α × β => (z.1, z.2))
        = entropy joint Prod.fst
          + InformationTheory.MeasureFano.condEntropy joint Prod.snd Prod.fst :=
    entropy_pair_eq_entropy_add_condEntropy joint Prod.fst Prod.snd
      measurable_fst measurable_snd
  -- `(fun z => (z.1, z.2)) = id` by η.
  have h_id : (fun z : α × β => (z.1, z.2)) = (id : α × β → α × β) := by
    funext z; rfl
  rw [h_id] at h_chain
  linarith

end EntropyMIBridge

end InformationTheory.Shannon

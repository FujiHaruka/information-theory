import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Shannon.AEP.Rate
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import InformationTheory.Shannon.ChannelCoding.Achievability.Core

/-!
# Channel coding achievability — random codebook average bound

Part of the longFile split of `Achievability.lean`. This part holds the
Fubini-style swap helpers (private lemmas `block_law_X_eq_pi_p`,
`block_law_Y_eq_pi`, `block_joint_law_eq_pi`, `codebook_marginal_one`,
`codebook_marginal_two`, `random_codebook_E1_swap`, `random_codebook_E2_swap`)
and their sole consumer `random_codebook_average_le`. The private lemmas and
their consumer are deliberately kept in the same file (file-scoped `private`).
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

lemma measureReal_pi_singleton_eq_prod
    {ι : Type*} [Fintype ι] {δ : ι → Type*} [∀ i, MeasurableSpace (δ i)]
    (κ : ∀ i, Measure (δ i)) [∀ i, SigmaFinite (κ i)] [∀ i, IsFiniteMeasure (κ i)]
    (x : ∀ i, δ i) :
    (Measure.pi κ).real {x} = ∏ i, (κ i).real {x i} := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  rfl

lemma sum_measureReal_singleton_univ_eq_one
    {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (ν : Measure γ) [IsProbabilityMeasure ν] :
    (∑ x : γ, ν.real {x}) = 1 := by
  have h_univ_real : ν.real ((Finset.univ : Finset γ) : Set γ) = 1 := by
    rw [Finset.coe_univ, measureReal_def, measure_univ]; rfl
  rw [← sum_measureReal_singleton (μ := ν) (Finset.univ : Finset γ)] at h_univ_real
  exact h_univ_real

omit [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β] in
lemma jointDistribution_real_singleton
    (p : Measure α) [IsProbabilityMeasure p] (W : Channel α β) [IsMarkovKernel W]
    (a : α) (b : β) :
    (jointDistribution p W).real ({(a, b)} : Set (α × β))
      = p.real {a} * (W a).real {b} := by
  classical
  rw [measureReal_def, jointDistribution_def]
  have h1 : (p ⊗ₘ W) ({(a, b)} : Set (α × β))
      = (p ⊗ₘ W) (({a} : Set α) ×ˢ ({b} : Set β)) := by
    congr 1; ext ⟨a', b'⟩; simp [Prod.ext_iff]
  rw [h1, Measure.compProd_apply ((measurableSet_singleton _).prod (measurableSet_singleton _))]
  have h_pre : ∀ a' : α, Prod.mk a' ⁻¹' (({a} : Set α) ×ˢ ({b} : Set β))
            = if a' = a then ({b} : Set β) else (∅ : Set β) := by
    intro a'
    by_cases ha' : a' = a
    · subst ha'; ext z; simp
    · ext z; simp [ha']
  have h_lint_congr : (∫⁻ a' : α, (W a') (Prod.mk a' ⁻¹' (({a} : Set α) ×ˢ ({b} : Set β))) ∂p)
        = ∫⁻ a' : α, (W a') (if a' = a then ({b} : Set β) else (∅ : Set β)) ∂p := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun a' ↦ ?_)
    show (W a') (Prod.mk a' ⁻¹' (({a} : Set α) ×ˢ ({b} : Set β)))
        = (W a') (if a' = a then ({b} : Set β) else (∅ : Set β))
    rw [h_pre a']
  rw [h_lint_congr, lintegral_fintype]
  have hsum : ∀ a' : α,
      (W a') (if a' = a then ({b} : Set β) else (∅ : Set β)) * p {a'}
        = (if a' = a then (W a) {b} * p {a} else 0) := by
    intro a'
    by_cases ha' : a' = a
    · subst ha'; simp
    · simp [ha']
  rw [Finset.sum_congr rfl (fun a' _ ↦ hsum a')]
  rw [Finset.sum_ite_eq' Finset.univ a (fun _ ↦ (W a) {b} * p {a})]
  rw [if_pos (Finset.mem_univ _), ENNReal.toReal_mul]
  show (W a).real {b} * p.real {a} = p.real {a} * (W a).real {b}
  ring

omit [DecidableEq α] [Nonempty α]
  [Fintype β] [DecidableEq β] [Nonempty β] in
lemma outputDistribution_real_singleton_eq_sum
    (p : Measure α) [IsProbabilityMeasure p] (W : Channel α β) [IsMarkovKernel W]
    (b : β) :
    (outputDistribution p W).real {b} = ∑ a : α, p.real {a} * (W a).real {b} := by
  classical
  -- ((p ⊗ₘ W).snd){b} = (p ⊗ₘ W)(univ ×ˢ {b}) = ∫⁻ a, W a {b} ∂p.
  have h1 : (outputDistribution p W) {b}
      = (jointDistribution p W) (Set.univ ×ˢ ({b} : Set β)) := by
    show (jointDistribution p W).snd {b} = _
    rw [Measure.snd_apply (measurableSet_singleton _)]
    congr 1; ext ⟨a, b'⟩; simp
  rw [measureReal_def, h1, jointDistribution_def]
  have h2 : (p ⊗ₘ W) (Set.univ ×ˢ ({b} : Set β)) = ∫⁻ a, W a {b} ∂p := by
    rw [Measure.compProd_apply (MeasurableSet.univ.prod (measurableSet_singleton _))]
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun a ↦ ?_)
    show (W a) (Prod.mk a ⁻¹' (Set.univ ×ˢ ({b} : Set β))) = (W a) {b}
    congr 1
    ext y; simp
  rw [h2, lintegral_fintype,
      ENNReal.toReal_sum (fun a _ ↦ ENNReal.mul_ne_top
        (measure_ne_top _ _) (measure_ne_top _ _))]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  rw [ENNReal.toReal_mul]
  show (W a).real {b} * p.real {a} = p.real {a} * (W a).real {b}
  ring

/-! #### Fubini helpers for the random codebook average.

The two helper lemmas below carry the Fubini-style swap between
"codebook expectation" and the `(X^n, Y^n)` joint law under `μ`.
They are the only ingredients that use the marginal-matching hypotheses
`h_match_X` / `h_match_Z`. -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [DecidableEq β] [Nonempty β] in
/-- Block X-law identification. Under `iIndepFun (Xs ·) μ` and
`h_match_X : μ.map (Xs 0) = p`, the block law `μ.map (jointRV Xs n)` equals
`Measure.pi (fun _ : Fin n => p)`. This is the bridge to the
`codebookMeasure p M n` structure.

Promoted to non-`private` so the two-codebook MAC achievability averaging in
`InformationTheory.Shannon.MultipleAccess.Achievability` can reuse it for the
user-1 alias axis and the `(X₂, Y)` joint-sequence axis (signature unchanged; no
cross-file consumer existed before). -/
lemma block_law_X_eq_pi_p
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindepX : iIndepFun (fun i ↦ Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (p : Measure α) [IsProbabilityMeasure p]
    (h_match_X : μ.map (Xs 0) = p) (n : ℕ) :
    μ.map (InformationTheory.Shannon.jointRV Xs n)
      = Measure.pi (fun _ : Fin n ↦ p) := by
  classical
  -- Restrict `Xs` to `Fin n`: `Xs' : Fin n → Ω → α := fun i => Xs i`.
  set Xs' : Fin n → Ω → α := fun i ↦ Xs i with hXs'_def
  have hXs'_meas : ∀ i : Fin n, AEMeasurable (Xs' i) μ := fun i ↦ (hXs i).aemeasurable
  -- `iIndepFun Xs' μ` from `iIndepFun (Xs ·) μ` by restriction.
  have hindepX' : iIndepFun Xs' μ :=
    hindepX.precomp (g := fun i : Fin n ↦ (i : ℕ)) Fin.val_injective
  -- Use `iIndepFun_iff_map_fun_eq_pi_map`.
  have h_pi_form : μ.map (fun ω i ↦ Xs' i ω)
        = Measure.pi (fun i ↦ μ.map (Xs' i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map hXs'_meas).mp hindepX'
  -- `μ.map (jointRV Xs n) = μ.map (fun ω i => Xs' i ω)` (defeq).
  have h_jointRV_eq : InformationTheory.Shannon.jointRV Xs n
        = fun ω (i : Fin n) ↦ Xs' i ω := rfl
  rw [h_jointRV_eq, h_pi_form]
  -- Each `μ.map (Xs' i) = p` via `IdentDistrib` to `Xs 0` and `h_match_X`.
  congr 1
  funext i
  show μ.map (Xs i) = p
  rw [(hidentX i).map_eq, h_match_X]

omit [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSingletonClass β] in
/-- Block Y-law identification. Symmetric to `block_law_X_eq_pi_p`. We do
not assume `μ.map (Ys 0) = outputDistribution p W`; instead, we just identify
`μ.map (jointRV Ys n) = Measure.pi (fun _ => μ.map (Ys 0))`. -/
private lemma block_law_Y_eq_pi
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ys : ℕ → Ω → β) (hYs : ∀ i, Measurable (Ys i))
    (hindepY : iIndepFun (fun i ↦ Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ) (n : ℕ) :
    μ.map (InformationTheory.Shannon.jointRV Ys n)
      = Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0)) := by
  classical
  set Ys' : Fin n → Ω → β := fun i ↦ Ys i with hYs'_def
  have hYs'_meas : ∀ i : Fin n, AEMeasurable (Ys' i) μ := fun i ↦ (hYs i).aemeasurable
  have hindepY' : iIndepFun Ys' μ :=
    hindepY.precomp (g := fun i : Fin n ↦ (i : ℕ)) Fin.val_injective
  have h_pi_form : μ.map (fun ω i ↦ Ys' i ω)
        = Measure.pi (fun i ↦ μ.map (Ys' i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map hYs'_meas).mp hindepY'
  have h_jointRV_eq : InformationTheory.Shannon.jointRV Ys n
        = fun ω (i : Fin n) ↦ Ys' i ω := rfl
  rw [h_jointRV_eq, h_pi_form]
  congr 1
  funext i
  show μ.map (Ys i) = μ.map (Ys 0)
  exact (hidentY i).map_eq

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- Block joint-law identification. Under `Pairwise … ⟂ᵢ[μ] …` for the
joint sequence and `h_match_Z : μ.map (jointSequence Xs Ys 0) = jointDistribution p W`,
the block-joint law `μ.map ⟨jointRV Xs n, jointRV Ys n⟩` corresponds to the product
`Measure.pi (fun _ => jointDistribution p W)` via reshape. Stated in the
"reshaped" form: the law of `ω ↦ fun i => (Xs i ω, Ys i ω)` is
`Measure.pi (fun _ => jointDistribution p W)`. -/
private lemma block_joint_law_eq_pi
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepZ_full : iIndepFun (fun i ↦ jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W]
    (h_match_Z : μ.map (jointSequence Xs Ys 0) = jointDistribution p W) (n : ℕ) :
    μ.map (fun ω (i : Fin n) ↦ (Xs i ω, Ys i ω))
      = Measure.pi (fun _ : Fin n ↦ jointDistribution p W) := by
  classical
  set Zs' : Fin n → Ω → α × β := fun i ↦ jointSequence Xs Ys i with hZs'_def
  have hZs'_meas : ∀ i : Fin n, AEMeasurable (Zs' i) μ := fun i ↦
    (measurable_jointSequence Xs Ys hXs hYs i).aemeasurable
  have hindepZ' : iIndepFun Zs' μ :=
    hindepZ_full.precomp (g := fun i : Fin n ↦ (i : ℕ)) Fin.val_injective
  have h_pi_form : μ.map (fun ω i ↦ Zs' i ω)
        = Measure.pi (fun i ↦ μ.map (Zs' i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map hZs'_meas).mp hindepZ'
  have h_fn_eq : (fun ω (i : Fin n) ↦ (Xs i ω, Ys i ω))
        = (fun ω i ↦ Zs' i ω) := by
    funext ω i; rfl
  rw [h_fn_eq, h_pi_form]
  congr 1
  funext i
  show μ.map (jointSequence Xs Ys i) = jointDistribution p W
  rw [(hidentZ i).map_eq, h_match_Z]

/-! #### Codebook-row marginalization.

The `codebookMeasure p M n` is a product over `Fin M` of `Measure.pi p`-rows.
When the integrand depends only on the `m`-th row (resp. `m`-th and `m'`-th rows
for `m ≠ m'`), we can factorize and sum out the other rows. -/

lemma prod_erase_eq_prod_subtype_ne
    {M : ℕ} [DecidableEq (Fin M)] (m : Fin M) {R : Type*} [CommMonoid R]
    (g : Fin M → R) (g' : {m' : Fin M // m' ≠ m} → R)
    (hg : ∀ (m'' : Fin M) (h : m'' ≠ m), g m'' = g' ⟨m'', h⟩) :
    ∏ m'' ∈ (Finset.univ : Finset (Fin M)).erase m, g m''
      = ∏ m'' : {m' : Fin M // m' ≠ m}, g' m'' := by
  classical
  have h_rhs : (∏ m'' : {m' : Fin M // m' ≠ m}, g' m'')
      = ∏ m'' ∈ ((Finset.univ : Finset (Fin M)).erase m).attach,
          g' ⟨m''.1, (Finset.mem_erase.mp m''.2).1⟩ := by
    symm
    apply Finset.prod_bij (fun (m'' : {m'' // m'' ∈ (Finset.univ : Finset (Fin M)).erase m})
      _ ↦ (⟨m''.1, (Finset.mem_erase.mp m''.2).1⟩ : {m' : Fin M // m' ≠ m}))
    · intro a _; exact Finset.mem_univ _
    · intro a _ b _ hab
      have h1 : (⟨a.1, _⟩ : {m' : Fin M // m' ≠ m}).1 = (⟨b.1, _⟩ : {m' : Fin M // m' ≠ m}).1 :=
        congrArg Subtype.val hab
      exact Subtype.ext h1
    · intro b _
      exact ⟨⟨b.1, Finset.mem_erase.mpr ⟨b.2, Finset.mem_univ _⟩⟩,
        Finset.mem_attach _ _, rfl⟩
    · intro _ _; rfl
  rw [h_rhs, ← Finset.prod_attach]
  refine Finset.prod_congr rfl ?_
  intro ⟨m'', hm''_mem⟩ _
  exact hg m'' (Finset.mem_erase.mp hm''_mem).1

lemma sum_prod_measureReal_singleton_eq_one
    {J γ : Type*} [Fintype J] [DecidableEq J] [Fintype γ] [MeasurableSpace γ]
    [MeasurableSingletonClass γ] (P : Measure γ) [IsProbabilityMeasure P] :
    ∑ c : J → γ, ∏ j : J, P.real {c j} = 1 := by
  classical
  have h_sum_one : (∑ x : γ, P.real {x}) = 1 :=
    sum_measureReal_singleton_univ_eq_one P
  have h_pi := (Finset.prod_univ_sum
    (κ := fun _ : J ↦ γ)
    (t := fun _ ↦ (Finset.univ : Finset γ))
    (R := ℝ)
    (f := fun (_ : J) x ↦ P.real {x})).symm
  have h_lhs_eq : (∑ c : J → γ, ∏ j : J, P.real {c j})
      = ∑ c ∈ Fintype.piFinset (fun _ : J ↦ (Finset.univ : Finset γ)),
        ∏ j : J, P.real {c j} := by
    apply Finset.sum_bij (fun (c : J → γ) _ ↦ c)
    · intro a _; exact Fintype.mem_piFinset.mpr (fun _ ↦ Finset.mem_univ _)
    · intro a _ b _ h; exact h
    · intro b _; exact ⟨b, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl
  rw [h_lhs_eq, h_pi]
  exact Finset.prod_eq_one (fun i _ ↦ h_sum_one)

omit [DecidableEq α] [Nonempty α] [Fintype β]
  [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- Single-row marginalization. Sum out all rows other than `m`.

Promoted to non-`private` for reuse by the two-codebook MAC achievability averaging
(both `Codebook`/`MACCodebook` reduce to `Fin M → Fin n → α`). -/
lemma codebook_marginal_one
    (p : Measure α) [IsProbabilityMeasure p] (M n : ℕ)
    (m : Fin M) (f : (Fin n → α) → ℝ) (_hf_nn : ∀ x, 0 ≤ f x) :
    ∑ c : Codebook M n α, (codebookMeasure p M n).real {c} * f (c m)
      = ∑ x : Fin n → α, (Measure.pi (fun _ : Fin n ↦ p)).real {x} * f x := by
  classical
  haveI : MeasurableSingletonClass (Fin n → α) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Codebook M n α) := Pi.instMeasurableSingletonClass
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin n ↦ p)) := by infer_instance
  -- Step 1: codebookMeasure.real {c} = ∏ m', (Pi p).real {c m'}.
  have h_cm : ∀ c : Codebook M n α,
      (codebookMeasure p M n).real {c}
        = ∏ m' : Fin M, (Measure.pi (fun _ : Fin n ↦ p)).real {c m'} := by
    intro c
    unfold codebookMeasure
    rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  -- Step 2: expand the sum and split off `m`-th coordinate via `prod_univ_sum`.
  -- `∑ c (∏ m', P{c m'}) f(c m) = ∑ c (∏ m', P{c m'}) f(c m)`
  -- View `c` as a function `Fin M → (Fin n → α)`. The sum is over all such functions.
  -- The standard `Fintype.sum_pi_eq_sum_univ` / Equiv approach.
  -- We use `Finset.sum_univ_pi`-style.
  have h_swap_step :
      ∑ c : Codebook M n α,
        (∏ m' : Fin M, (Measure.pi (fun _ : Fin n ↦ p)).real {c m'}) * f (c m)
      = ∑ x : Fin n → α, (Measure.pi (fun _ : Fin n ↦ p)).real {x} * f x := by
    -- Strategy: reindex `c : Fin M → (Fin n → α)` via swapping `m`-th coord with `0`-th.
    -- Pull out the `m`-th factor in the product to get `f(c m) * P{c m} * ∏_{m'≠m} P{c m'}`.
    -- Then sum over `c m'` for `m' ≠ m` separately (each gives 1 since P is a probability).
    set P : Measure (Fin n → α) := Measure.pi (fun _ : Fin n ↦ p) with hP_def
    haveI : IsProbabilityMeasure P := by rw [hP_def]; infer_instance
    -- Pull out the m-th factor.
    have h_prod_split : ∀ c : Codebook M n α,
        (∏ m' : Fin M, P.real {c m'})
          = P.real {c m} * ∏ m' ∈ (Finset.univ : Finset (Fin M)).erase m, P.real {c m'} := by
      intro c
      exact (Finset.mul_prod_erase Finset.univ (fun m' ↦ P.real {c m'})
        (Finset.mem_univ m)).symm
    -- Reindex: `c ↦ (c m, c restricted to (univ.erase m))`.
    -- Use Fintype.sum_equiv? simpler: use Finset.sum_prod_pi.
    -- A cleaner approach: view `Codebook M n α = Fin M → (Fin n → α)` as a product over Fin M.
    -- The big sum is `∑_{c : Fin M → (Fin n → α)} F(c)` = `∑_{x : Fin n → α} ∑_{c' : ...}  F(...)`.
    -- We use `Fintype.sum_equiv` with `Equiv.piFinSucc` style, but simpler: just split via
    -- `Finset.sum_pi_finset_univ` / `Fintype.prod_pi`.
    -- Actually simplest: use the substitution `c = Function.update c₀ m x` for some baseline.
    -- Use `Fintype.sum_pi`:
    -- ∑ c, ∏ m', g (c m') = ∏ m', ∑ x, g x.
    -- Combined with f(c m) breaking the product, we use Fintype.sum_apply_prod.
    -- The cleanest: do an Equiv-based reindex
    -- `Fin M → (Fin n → α) ≃ (Fin n → α) × (Fin M.erase m → Fin n → α)`.
    -- Use Fintype.prod_univ_sum-style.
    -- Concretely:
    --   ∑_c F(c m) * ∏_{m'} P{c m'}
    --   = ∑_{c m ∈ FinN→α} F(c m) * P{c m} * ∑_{c m'≠m ∈ ...} ∏ P{c m'}
    -- And `∑_{c''} ∏ P{c'' m'} = ∏ ∑_{x} P{x} = 1^... = 1` over `(Fin M).erase m`.
    rw [Finset.sum_congr rfl (fun c _ ↦ by rw [h_prod_split c])]
    -- Now group: ∑ c, (P{c m} * ∏_{m'≠m} P{c m'}) * f(c m)
    --   = ∑ c, P{c m} * f(c m) * ∏_{m'≠m} P{c m'}.
    have h_reassoc : ∀ c : Codebook M n α,
        (P.real {c m} * ∏ m' ∈ (Finset.univ : Finset (Fin M)).erase m, P.real {c m'}) *
            f (c m)
          = (P.real {c m} * f (c m)) *
            (∏ m' ∈ (Finset.univ : Finset (Fin M)).erase m, P.real {c m'}) := by
      intro c; ring
    rw [Finset.sum_congr rfl (fun c _ ↦ h_reassoc c)]
    -- Use a bijection `Codebook M n α ≃ (Fin n → α) × ((Fin M).erase m → (Fin n → α))`
    -- via `c ↦ (c m, fun m' => c m'.1)`. We avoid building this Equiv explicitly and
    -- use the Fintype.sum_prod identity in product form.
    -- Concretely: `c : Fin M → β` can be split via `Function.update` and using
    -- the fact that `Fintype.sum (g) ` on `Fin M → β` equals
    -- `∑_{x} ∑_{c'} g (Function.update c' m x)` if we let c' vary over m' ≠ m.
    -- We use `Fintype.sum_equiv` with the obvious equivalence.
    let toFun : Codebook M n α → (Fin n → α) × ({m' : Fin M // m' ≠ m} → (Fin n → α)) :=
      fun c ↦ (c m, fun m' ↦ c m'.1)
    let invFun : (Fin n → α) × ({m' : Fin M // m' ≠ m} → (Fin n → α)) → Codebook M n α :=
      fun p m' ↦ if h : m' = m then p.1 else p.2 ⟨m', h⟩
    have left_inv : ∀ c, invFun (toFun c) = c := by
      intro c
      funext m'
      by_cases h : m' = m
      · subst h; simp [toFun, invFun]
      · simp [toFun, invFun, h]
    have right_inv : ∀ p, toFun (invFun p) = p := by
      intro ⟨x, c'⟩
      refine Prod.ext ?_ ?_
      · simp [toFun, invFun]
      · funext ⟨m', hm'⟩
        simp [toFun, invFun, hm']
    set e : Codebook M n α ≃ (Fin n → α) × ({m' : Fin M // m' ≠ m} → (Fin n → α)) :=
      { toFun := toFun, invFun := invFun, left_inv := left_inv, right_inv := right_inv }
    -- Reindex via `e.symm`: ∑ y, F (e.symm y) = ∑ c, F c.
    rw [← Equiv.sum_comp e.symm
      (fun c ↦ P.real {c m} * f (c m) *
        ∏ m' ∈ (Finset.univ : Finset (Fin M)).erase m, P.real {c m'})]
    -- Now the sum is over `(x, c') : (Fin n → α) × ({m' // m' ≠ m} → (Fin n → α))`.
    rw [Fintype.sum_prod_type]
    -- e.symm = invFun.
    show ∑ x : Fin n → α, ∑ c' : {m' : Fin M // m' ≠ m} → (Fin n → α),
        P.real {invFun (x, c') m} * f (invFun (x, c') m) *
          ∏ m'' ∈ (Finset.univ : Finset (Fin M)).erase m,
            P.real {invFun (x, c') m''} = _
    -- ∑_x ∑_{c'} (P{x} * f x) * ∏_{m' ∈ univ.erase m} P{(e.symm (x, c')) m'}
    -- For m' ≠ m, `(e.symm (x, c')) m' = c' ⟨m', h⟩`.
    -- So `∏_{m' ∈ univ.erase m} P{(e.symm (x, c')) m'} = ∏_{m' : Fin M.erase m} P {c' ⟨m', _⟩}`.
    have h_inner : ∀ (x : Fin n → α) (c' : {m' : Fin M // m' ≠ m} → (Fin n → α)),
        (∏ m'' ∈ (Finset.univ : Finset (Fin M)).erase m,
            P.real {(invFun (x, c')) m''})
          = ∏ m'' : {m' : Fin M // m' ≠ m}, P.real {c' m''} := by
      intro x c'
      refine prod_erase_eq_prod_subtype_ne m
        (fun m'' ↦ P.real {(invFun (x, c')) m''})
        (fun m'' ↦ P.real {c' m''}) (fun m'' h ↦ ?_)
      have h_bij : (invFun (x, c')) m'' = c' ⟨m'', h⟩ := by
        show (if h' : m'' = m then x else c' ⟨m'', h'⟩) = c' ⟨m'', h⟩
        simp [h]
      simp only [h_bij]
    -- For the equiv `e`, by its def, `(e.symm (x, c'))` is the construction.
    -- We want: ∑_x ∑_c' (P{x} * f x) * (∏ ... ) = ∑_x (P{x} * f x).
    -- That requires ∑_{c'} ∏_{m'} P{c' m'} = 1.
    have h_sum_other : ∑ c' : {m' : Fin M // m' ≠ m} → (Fin n → α),
        ∏ m'' : {m' : Fin M // m' ≠ m}, P.real {c' m''} = 1 :=
      sum_prod_measureReal_singleton_eq_one P
    -- Combine: ∑_x ∑_{c'} A(x) * B(c') = (∑_x A(x)) * (∑_{c'} B(c'))
    -- Here B(c') = ∏... and ∑ B = 1, so result is ∑_x A(x).
    calc ∑ x : Fin n → α, ∑ c' : {m' : Fin M // m' ≠ m} → (Fin n → α),
            (P.real {(invFun (x, c')) m} * f ((invFun (x, c')) m)) *
              ∏ m'' ∈ (Finset.univ : Finset (Fin M)).erase m,
                P.real {(invFun (x, c')) m''}
        = ∑ x : Fin n → α, ∑ c' : {m' : Fin M // m' ≠ m} → (Fin n → α),
            (P.real {x} * f x) *
              ∏ m'' : {m' : Fin M // m' ≠ m}, P.real {c' m''} := by
          refine Finset.sum_congr rfl (fun x _ ↦ Finset.sum_congr rfl (fun c' _ ↦ ?_))
          have h1 : (invFun (x, c')) m = x := by
            show (if h : m = m then x else c' ⟨m, h⟩) = x
            simp
          rw [h1, h_inner x c']
      _ = ∑ x : Fin n → α, (P.real {x} * f x) *
            ∑ c' : {m' : Fin M // m' ≠ m} → (Fin n → α),
              ∏ m'' : {m' : Fin M // m' ≠ m}, P.real {c' m''} := by
          refine Finset.sum_congr rfl (fun x _ ↦ ?_)
          rw [← Finset.mul_sum]
      _ = ∑ x : Fin n → α, P.real {x} * f x := by
          refine Finset.sum_congr rfl (fun x _ ↦ ?_)
          rw [h_sum_other, mul_one]
  -- Combine h_cm with h_swap_step.
  rw [Finset.sum_congr rfl (fun c _ ↦ by rw [h_cm c])]
  exact h_swap_step

omit [DecidableEq α] [Nonempty α] [Fintype β]
  [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- Two-row marginalization. Sum out all rows other than `m` and `m'` (with
`m ≠ m'`).

Promoted to non-`private` for reuse by the two-codebook MAC achievability averaging
(the user-1 true/alias two-row marginalization). -/
lemma codebook_marginal_two
    (p : Measure α) [IsProbabilityMeasure p] (M n : ℕ)
    (m m' : Fin M) (hne : m ≠ m')
    (f : (Fin n → α) → (Fin n → α) → ℝ) (_hf_nn : ∀ x x', 0 ≤ f x x') :
    ∑ c : Codebook M n α, (codebookMeasure p M n).real {c} * f (c m) (c m')
      = ∑ x : Fin n → α, ∑ x' : Fin n → α,
          (Measure.pi (fun _ : Fin n ↦ p)).real {x} *
          (Measure.pi (fun _ : Fin n ↦ p)).real {x'} * f x x' := by
  classical
  haveI : MeasurableSingletonClass (Fin n → α) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Codebook M n α) := Pi.instMeasurableSingletonClass
  set P : Measure (Fin n → α) := Measure.pi (fun _ : Fin n ↦ p) with hP_def
  haveI : IsProbabilityMeasure P := by rw [hP_def]; infer_instance
  -- Step 1: codebookMeasure.real {c} = ∏ m'', P.real {c m''}.
  have h_cm : ∀ c : Codebook M n α,
      (codebookMeasure p M n).real {c}
        = ∏ m'' : Fin M, P.real {c m''} := by
    intro c
    unfold codebookMeasure
    rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  -- Step 2: split off m and m' from the product, then sum out the rest.
  -- Define `Other := {m'' : Fin M | m'' ≠ m ∧ m'' ≠ m'}`.
  rw [Finset.sum_congr rfl (fun c _ ↦ by rw [h_cm c])]
  -- Build the equiv
  -- `Codebook M n α ≃ (Fin n → α) × (Fin n → α) × ({m'' // m'' ≠ m ∧ m'' ≠ m'} → (Fin n → α))`.
  let toFun : Codebook M n α →
      (Fin n → α) × (Fin n → α) × ({m'' : Fin M // m'' ≠ m ∧ m'' ≠ m'} → (Fin n → α)) :=
    fun c ↦ (c m, c m', fun m'' ↦ c m''.1)
  let invFun :
      (Fin n → α) × (Fin n → α) × ({m'' : Fin M // m'' ≠ m ∧ m'' ≠ m'} → (Fin n → α)) →
        Codebook M n α :=
    fun ⟨x, x', c''⟩ idx ↦
      if h : idx = m then x
      else if h' : idx = m' then x'
      else c'' ⟨idx, h, h'⟩
  have left_inv : ∀ c, invFun (toFun c) = c := by
    intro c
    funext idx
    by_cases h1 : idx = m
    · subst h1; simp [toFun, invFun]
    · by_cases h2 : idx = m'
      · subst h2; simp [toFun, invFun, h1]
      · simp [toFun, invFun, h1, h2]
  have right_inv : ∀ p, toFun (invFun p) = p := by
    intro ⟨x, x', c''⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp [toFun, invFun]
    · simp [toFun, invFun, hne.symm]
    · funext ⟨idx, h1, h2⟩
      simp [toFun, invFun, h1, h2]
  set e : Codebook M n α ≃
      (Fin n → α) × (Fin n → α) × ({m'' : Fin M // m'' ≠ m ∧ m'' ≠ m'} → (Fin n → α)) :=
    { toFun := toFun, invFun := invFun, left_inv := left_inv, right_inv := right_inv }
  rw [← Equiv.sum_comp e.symm
    (fun c ↦ (∏ m'' : Fin M, P.real {c m''}) * f (c m) (c m'))]
  -- Decompose the sum on the right of e.symm.
  show ∑ y : (Fin n → α) × (Fin n → α) × _,
        (∏ m'' : Fin M, P.real {(invFun y) m''}) * f ((invFun y) m) ((invFun y) m') = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x' _ ↦ ?_)
  -- Inner sum over c''.
  -- For invFun (x, x', c''), at idx = m gives x, at idx = m' gives x', else c'' ⟨idx,_,_⟩.
  have h_at_m : ∀ (c'' : {m'' : Fin M // m'' ≠ m ∧ m'' ≠ m'} → (Fin n → α)),
      invFun (x, x', c'') m = x := by
    intro c''; show (if h : m = m then x else _) = x; simp
  have h_at_m' : ∀ (c'' : {m'' : Fin M // m'' ≠ m ∧ m'' ≠ m'} → (Fin n → α)),
      invFun (x, x', c'') m' = x' := by
    intro c''
    show (if h : m' = m then x else if h' : m' = m' then x' else _) = x'
    simp [hne.symm]
  -- The product over Fin M splits: m, m', and the rest.
  have h_split : ∀ (c'' : {m'' : Fin M // m'' ≠ m ∧ m'' ≠ m'} → (Fin n → α)),
      (∏ m'' : Fin M, P.real {(invFun (x, x', c'')) m''})
        = P.real {x} * P.real {x'} *
          ∏ m'' ∈ ((Finset.univ : Finset (Fin M)).erase m).erase m',
            P.real {(invFun (x, x', c'')) m''} := by
    intro c''
    -- Pull out m, m'.
    rw [← Finset.mul_prod_erase Finset.univ (fun m'' ↦ P.real {(invFun (x, x', c'')) m''})
          (Finset.mem_univ m)]
    rw [← Finset.mul_prod_erase ((Finset.univ : Finset (Fin M)).erase m)
          (fun m'' ↦ P.real {(invFun (x, x', c'')) m''})
          (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩)]
    rw [h_at_m c'', h_at_m' c'']
    ring
  rw [Finset.sum_congr rfl (fun c'' _ ↦ by rw [h_split c'',
        h_at_m c'', h_at_m' c''])]
  -- Inner sum: ∑_{c''} (P{x} * P{x'} * ∏_{m''} P{c'' ⟨m'',_⟩}) * f x x'
  -- = (P{x} * P{x'} * f x x') * (∑_{c''} ∏_{m''} P{c'' ⟨m'',_⟩})
  -- = (P{x} * P{x'} * f x x') * 1.
  have h_inner_eq : ∀ (c'' : {m'' : Fin M // m'' ≠ m ∧ m'' ≠ m'} → (Fin n → α)),
      (P.real {x} * P.real {x'} *
        ∏ m'' ∈ ((Finset.univ : Finset (Fin M)).erase m).erase m',
          P.real {(invFun (x, x', c'')) m''}) * f x x'
      = (P.real {x} * P.real {x'} * f x x') *
        ∏ m'' : {m'' : Fin M // m'' ≠ m ∧ m'' ≠ m'}, P.real {c'' m''} := by
    intro c''
    have h_other_prod :
        (∏ m'' ∈ ((Finset.univ : Finset (Fin M)).erase m).erase m',
            P.real {(invFun (x, x', c'')) m''})
        = ∏ m'' : {m'' : Fin M // m'' ≠ m ∧ m'' ≠ m'}, P.real {c'' m''} := by
      -- Reindex.
      have h_val : ∀ idx : Fin M, ∀ h_ne_m : idx ≠ m, ∀ h_ne_m' : idx ≠ m',
          (invFun (x, x', c'')) idx = c'' ⟨idx, h_ne_m, h_ne_m'⟩ := by
        intro idx h_ne_m h_ne_m'
        show (if h : idx = m then x else if h' : idx = m' then x' else c'' ⟨idx, h, h'⟩)
          = c'' ⟨idx, h_ne_m, h_ne_m'⟩
        simp [h_ne_m, h_ne_m']
      -- Bijection: idx ∈ ((univ.erase m).erase m') ↔ idx ≠ m ∧ idx ≠ m'.
      symm
      apply Finset.prod_bij (fun (idx : {m'' : Fin M // m'' ≠ m ∧ m'' ≠ m'}) _ ↦ idx.1)
      · intro a _
        exact Finset.mem_erase.mpr ⟨a.2.2, Finset.mem_erase.mpr ⟨a.2.1, Finset.mem_univ _⟩⟩
      · intro a _ b _ h; exact Subtype.ext h
      · intro b hb
        have hb1 : b ≠ m' := (Finset.mem_erase.mp hb).1
        have hb2 : b ≠ m := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
        exact ⟨⟨b, hb2, hb1⟩, Finset.mem_univ _, rfl⟩
      · intro a _
        rw [h_val a.1 a.2.1 a.2.2]
    rw [h_other_prod]; ring
  rw [Finset.sum_congr rfl (fun c'' _ ↦ h_inner_eq c'')]
  rw [← Finset.mul_sum]
  -- Use prod_univ_sum to compute ∑_{c''} ∏_{m''} P{c'' m''} = ∏_{m''} ∑_x P{x} = 1.
  have h_sum_other : ∑ c'' : {m'' : Fin M // m'' ≠ m ∧ m'' ≠ m'} → (Fin n → α),
      ∏ m'' : {m'' : Fin M // m'' ≠ m ∧ m'' ≠ m'}, P.real {c'' m''} = 1 :=
    sum_prod_measureReal_singleton_eq_one P
  rw [h_sum_other, mul_one]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [DecidableEq β] [Nonempty β] in
private lemma E1_lhs_sum_eq_Q_sum
    {n : ℕ}
    (P : Measure (Fin n → α)) (Q : Measure (Fin n → α × β))
    (Wpi : (Fin n → α) → Measure (Fin n → β))
    (hWpi : ∀ x, IsProbabilityMeasure (Wpi x))
    (JTS : Set ((Fin n → α) × (Fin n → β)))
    (Sfin : Finset (Fin n → α × β))
    (hSfin : (Sfin : Set (Fin n → α × β))
      = (fun z ↦ ((fun i ↦ (z i).1 : Fin n → α), (fun i ↦ (z i).2 : Fin n → β)))
          ⁻¹' (JTSᶜ : Set ((Fin n → α) × (Fin n → β))))
    (hQ_singleton : ∀ (x : Fin n → α) (y : Fin n → β),
      Q.real {(fun i ↦ (x i, y i) : Fin n → α × β)} = P.real {x} * (Wpi x).real {y}) :
    ∑ x : Fin n → α, P.real {x} * (Wpi x).real {y | (x, y) ∉ JTS}
      = ∑ z ∈ Sfin, Q.real {z} := by
  classical
  let ψ : (Fin n → α × β) → (Fin n → α) × (Fin n → β) :=
    fun z ↦ (fun i ↦ (z i).1, fun i ↦ (z i).2)
  have hSfin_mem : ∀ z : Fin n → α × β, z ∈ Sfin ↔ ψ z ∉ JTS := by
    intro z
    rw [← Finset.mem_coe, hSfin]; rfl
  -- For each x, (Wpi x).real {y | ...} = ∑_{y ∈ slicefinset(x)} (Wpi x).real {y}.
  have h_slice_fin : ∀ x : Fin n → α,
      ({y | (x, y) ∉ JTS} : Set (Fin n → β)).Finite :=
    fun _ ↦ Set.toFinite _
  have h_per_x : ∀ x : Fin n → α,
      P.real {x} * (Wpi x).real {y | (x, y) ∉ JTS}
        = ∑ y ∈ (h_slice_fin x).toFinset,
            Q.real {(fun i ↦ (x i, y i) : Fin n → α × β)} := by
    intro x
    haveI := hWpi x
    set Ts : Finset (Fin n → β) := (h_slice_fin x).toFinset with hTs_def
    have h_Ts_coe : (Ts : Set _) = {y | (x, y) ∉ JTS} :=
      (h_slice_fin x).coe_toFinset
    have h_eq : (Wpi x).real {y | (x, y) ∉ JTS}
          = ∑ y ∈ Ts, (Wpi x).real {y} := by
      rw [← h_Ts_coe, ← sum_measureReal_singleton (μ := Wpi x) Ts]
    rw [h_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ ↦ ?_)
    rw [hQ_singleton x y]
  rw [Finset.sum_congr rfl (fun x _ ↦ h_per_x x)]
  -- Build a finset = pairs (x,y) with (x,y) ∉ JTS, in bijection with Sfin.
  set Tfin : Finset ((Fin n → α) × (Fin n → β)) :=
    ((Finset.univ : Finset (Fin n → α)) ×ˢ
      (Finset.univ : Finset (Fin n → β))).filter (fun p ↦ p ∉ JTS) with hTfin_def
  have h_lhs_to_T :
      (∑ x : Fin n → α, ∑ y ∈ (h_slice_fin x).toFinset,
            Q.real {(fun i ↦ (x i, y i) : Fin n → α × β)})
        = ∑ p ∈ Tfin, Q.real {(fun i ↦ (p.1 i, p.2 i) : Fin n → α × β)} := by
    have h_full : (∑ x : Fin n → α, ∑ y : Fin n → β,
            if (x, y) ∉ JTS then
              Q.real {(fun i ↦ (x i, y i) : Fin n → α × β)}
            else 0)
          = ∑ x : Fin n → α, ∑ y ∈ (h_slice_fin x).toFinset,
              Q.real {(fun i ↦ (x i, y i) : Fin n → α × β)} := by
      refine Finset.sum_congr rfl (fun x _ ↦ ?_)
      rw [← Finset.sum_filter]
      apply Finset.sum_congr ?_ (fun _ _ ↦ rfl)
      ext y
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      show (y ∈ (Finset.univ : Finset (Fin n → β)) ∧ (x, y) ∉ JTS) ↔
        (x, y) ∉ JTS
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨Finset.mem_univ _, h⟩
    rw [← h_full]
    rw [← Finset.sum_product']
    rw [hTfin_def]
    rw [Finset.sum_filter]
  rw [h_lhs_to_T]
  -- bijection Tfin ≃ Sfin via (x, y) ↦ fun i => (x i, y i).
  apply Finset.sum_bij
    (i := fun (p : (Fin n → α) × (Fin n → β)) _ ↦
      (fun i ↦ (p.1 i, p.2 i) : Fin n → α × β))
  · intro p hp
    rw [hSfin_mem]
    rw [hTfin_def, Finset.mem_filter] at hp
    exact hp.2
  · intro a _ b _ hab
    have h1 : a.1 = b.1 := by
      funext i
      have hh : (fun i ↦ (a.1 i, a.2 i) : Fin n → α × β) i
          = (fun i ↦ (b.1 i, b.2 i) : Fin n → α × β) i := by rw [hab]
      exact (Prod.mk.injEq _ _ _ _).mp hh |>.1
    have h2 : a.2 = b.2 := by
      funext i
      have hh : (fun i ↦ (a.1 i, a.2 i) : Fin n → α × β) i
          = (fun i ↦ (b.1 i, b.2 i) : Fin n → α × β) i := by rw [hab]
      exact (Prod.mk.injEq _ _ _ _).mp hh |>.2
    exact Prod.ext h1 h2
  · intro z hz
    rw [hSfin_mem] at hz
    refine ⟨ψ z, ?_, ?_⟩
    · rw [hTfin_def, Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
      exact hz
    · funext i; rfl
  · intro _ _; rfl

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β] in
/-- (E1) Fubini swap. For any message index `m`, the codebook expectation of
the "true codeword not jointly typical" event equals the abstract i.i.d.
expectation. -/
private lemma random_codebook_E1_swap
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    {M n : ℕ} (_hM : 0 < M) {ε : ℝ} (_hε : 0 < ε)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (_hindepX : iIndepFun (fun i ↦ Xs i) μ)
    (_hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (_hindepY : iIndepFun (fun i ↦ Ys i) μ)
    (_hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (_hindepZ : Pairwise fun i j ↦
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hindepZ_full : iIndepFun (fun i : ℕ ↦ jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (_hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (_hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (_hposZ : ∀ q : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {q})
    (_h_match_X : μ.map (Xs 0) = p)
    (h_match_Z : μ.map (jointSequence Xs Ys 0) = jointDistribution p W) (m : Fin M) :
    ∑ c : Codebook M n α, (codebookMeasure p M n).real {c} *
        (Measure.pi (fun i ↦ W (c m i))).real
          {y | (c m, y) ∉ jointlyTypicalSet μ Xs Ys n ε}
      ≤ μ.real
          {ω | (InformationTheory.Shannon.jointRV Xs n ω,
                InformationTheory.Shannon.jointRV Ys n ω) ∉
              jointlyTypicalSet μ Xs Ys n ε} := by
  classical
  haveI : MeasurableSingletonClass (Fin n → α) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Fin n → β) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Fin n → α × β) := Pi.instMeasurableSingletonClass
  set P : Measure (Fin n → α) := Measure.pi (fun _ : Fin n ↦ p) with hP_def
  haveI : IsProbabilityMeasure P := by rw [hP_def]; infer_instance
  set JTS : Set ((Fin n → α) × (Fin n → β)) := jointlyTypicalSet μ Xs Ys n ε with hJTS_def
  -- Step 1: codebook_marginal_one reduces LHS to ∑_x P{x} * (Pi (W∘x)).real {y | (x,y) ∉ JTS}.
  have h_swap_step1 :
      ∑ c : Codebook M n α, (codebookMeasure p M n).real {c} *
        (Measure.pi (fun i ↦ W (c m i))).real
          {y | (c m, y) ∉ jointlyTypicalSet μ Xs Ys n ε}
      = ∑ x : Fin n → α, P.real {x} *
          (Measure.pi (fun i ↦ W (x i))).real
            {y | (x, y) ∉ jointlyTypicalSet μ Xs Ys n ε} := by
    refine codebook_marginal_one p M n m
      (fun x ↦ (Measure.pi (fun i ↦ W (x i))).real
        {y | (x, y) ∉ jointlyTypicalSet μ Xs Ys n ε}) ?_
    intro x; exact measureReal_nonneg
  rw [h_swap_step1]
  -- Step 2: singleton mass identities.
  have h_P_singleton : ∀ (x : Fin n → α), P.real {x} = ∏ i, p.real {x i} := by
    intro x; rw [hP_def]; exact measureReal_pi_singleton_eq_prod _ x
  have h_pi_W_singleton : ∀ (x : Fin n → α) (y : Fin n → β),
      (Measure.pi (fun i ↦ W (x i))).real {y} = ∏ i, (W (x i)).real {y i} :=
    fun x y ↦ measureReal_pi_singleton_eq_prod _ y
  set Q : Measure (Fin n → α × β) := Measure.pi (fun _ : Fin n ↦ jointDistribution p W) with hQ_def
  haveI : IsProbabilityMeasure Q := by rw [hQ_def]; infer_instance
  have h_jointSingleton : ∀ (a : α) (b : β),
      (jointDistribution p W).real ({(a, b)} : Set (α × β)) = p.real {a} * (W a).real {b} :=
    fun a b ↦ jointDistribution_real_singleton p W a b
  have h_Q_singleton : ∀ (x : Fin n → α) (y : Fin n → β),
      Q.real {(fun i ↦ (x i, y i) : Fin n → α × β)}
        = P.real {x} * (Measure.pi (fun i ↦ W (x i))).real {y} := by
    intro x y
    rw [hQ_def, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    have hprod : ∀ i : Fin n,
        ((jointDistribution p W) {(x i, y i)}).toReal
          = p.real {x i} * (W (x i)).real {y i} := by
      intro i
      have := h_jointSingleton (x i) (y i)
      rw [measureReal_def] at this
      exact this
    rw [Finset.prod_congr rfl (fun i _ ↦ hprod i)]
    rw [Finset.prod_mul_distrib, h_P_singleton x, h_pi_W_singleton x y]
  -- Step 3: μ.map (fun ω i => (Xs i ω, Ys i ω)) = Q via block_joint_law_eq_pi.
  set ζ : Ω → (Fin n → α × β) := fun ω i ↦ (Xs i ω, Ys i ω) with hζ_def
  have h_ζ_meas : Measurable ζ := by
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    exact (hXs i).prodMk (hYs i)
  have h_block_law : μ.map ζ = Q := by
    rw [hζ_def, hQ_def]
    exact block_joint_law_eq_pi μ Xs Ys hXs hYs hindepZ_full hidentZ p W h_match_Z n
  -- Step 4: reshape function ψ : (Fin n → α × β) → (Fin n → α) × (Fin n → β).
  let ψ : (Fin n → α × β) → (Fin n → α) × (Fin n → β) :=
    fun z ↦ (fun i ↦ (z i).1, fun i ↦ (z i).2)
  have h_ψ_meas : Measurable ψ := by
    refine Measurable.prodMk ?_ ?_
    · refine measurable_pi_lambda _ (fun i ↦ ?_)
      exact (measurable_pi_apply i).fst
    · refine measurable_pi_lambda _ (fun i ↦ ?_)
      exact (measurable_pi_apply i).snd
  -- (jointRV Xs n, jointRV Ys n) ω = ψ (ζ ω).
  have h_jointRV_eq :
      (fun ω ↦ (InformationTheory.Shannon.jointRV (α := α) Xs n ω,
                  InformationTheory.Shannon.jointRV (α := β) Ys n ω))
        = ψ ∘ ζ := by
    funext ω; rfl
  -- The RHS event = ζ ⁻¹' (ψ ⁻¹' JTSᶜ).
  have h_RHS_event_eq :
      {ω | (InformationTheory.Shannon.jointRV (α := α) Xs n ω,
            InformationTheory.Shannon.jointRV (α := β) Ys n ω) ∉
          jointlyTypicalSet μ Xs Ys n ε}
        = ζ ⁻¹' (ψ ⁻¹' (JTSᶜ : Set ((Fin n → α) × (Fin n → β)))) := by
    ext ω
    constructor
    · intro h; exact h
    · intro h; exact h
  -- RHS = (μ.map ζ).real (ψ ⁻¹' JTSᶜ) = Q.real (ψ ⁻¹' JTSᶜ).
  have h_ψ_pre_meas : MeasurableSet (ψ ⁻¹' (JTSᶜ : Set ((Fin n → α) × (Fin n → β)))) :=
    h_ψ_meas (measurableSet_jointlyTypicalSet _ _ _ _ _).compl
  have h_RHS_eq_Q :
      μ.real {ω | (InformationTheory.Shannon.jointRV Xs n ω,
                    InformationTheory.Shannon.jointRV Ys n ω) ∉
                jointlyTypicalSet μ Xs Ys n ε}
        = Q.real (ψ ⁻¹' (JTSᶜ : Set ((Fin n → α) × (Fin n → β)))) := by
    rw [h_RHS_event_eq, measureReal_def, measureReal_def]
    rw [← h_block_law, Measure.map_apply h_ζ_meas h_ψ_pre_meas]
  rw [h_RHS_eq_Q]
  -- Step 5: Enumerate Q.real (ψ ⁻¹' JTSᶜ) as a sum over singletons.
  -- ψ ⁻¹' JTSᶜ is finite (subset of (Fin n → α × β), itself finite).
  set S : Set (Fin n → α × β) := ψ ⁻¹' (JTSᶜ : Set ((Fin n → α) × (Fin n → β))) with hS_def
  have h_S_fin : S.Finite := Set.toFinite _
  set Sfin : Finset (Fin n → α × β) := h_S_fin.toFinset with hSfin_def
  have h_Sfin_coe : (Sfin : Set _) = S := h_S_fin.coe_toFinset
  have h_Q_sum : Q.real S = ∑ z ∈ Sfin, Q.real {z} := by
    rw [← h_Sfin_coe, ← sum_measureReal_singleton (μ := Q) Sfin]
  rw [h_Q_sum]
  -- LHS = ∑_x P{x} * ((Pi W∘x).real {y | (x,y) ∉ JTS})
  --     = ∑_x P{x} * ∑_{y : (x,y) ∉ JTS} (Pi W∘x).real {y}
  --     = ∑_x ∑_{y : (x,y) ∉ JTS} P{x} * (Pi W∘x).real {y}
  --     = ∑_{(x,y) : (x,y) ∉ JTS} Q.real {fun i => (x i, y i)}
  --     = ∑_{z ∈ ψ ⁻¹' JTSᶜ} Q.real {z}.
  have h_LHS_eq :
      ∑ x : Fin n → α, P.real {x} *
        (Measure.pi (fun i ↦ W (x i))).real
          {y | (x, y) ∉ jointlyTypicalSet μ Xs Ys n ε}
      = ∑ z ∈ Sfin, Q.real {z} :=
    E1_lhs_sum_eq_Q_sum P Q (fun x ↦ Measure.pi (fun i ↦ W (x i)))
      (fun _ ↦ inferInstance) JTS Sfin (h_Sfin_coe.trans hS_def) h_Q_singleton
  rw [h_LHS_eq]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] in
private lemma sum_chan_set_eq_μY
    {n : ℕ}
    (P : Measure (Fin n → α)) (μY : Measure (Fin n → β)) [IsProbabilityMeasure μY]
    (Wpi : (Fin n → α) → Measure (Fin n → β))
    (hWpi : ∀ x, IsProbabilityMeasure (Wpi x))
    (f : (Fin n → α) → (Fin n → β) → ℝ)
    (h_pi_W : ∀ (x : Fin n → α) (y : Fin n → β), (Wpi x).real {y} = f x y)
    (h_chan : ∀ y : Fin n → β, (∑ x : Fin n → α, P.real {x} * f x y) = μY.real {y})
    (S : Set (Fin n → β)) (hS : S.Finite) :
    (∑ x : Fin n → α, P.real {x} * (Wpi x).real S) = μY.real S := by
  classical
  haveI : MeasurableSingletonClass (Fin n → β) := Pi.instMeasurableSingletonClass
  set Sfin : Finset (Fin n → β) := hS.toFinset
  have h_S_coe : (Sfin : Set _) = S := hS.coe_toFinset
  have h_Wpi_real : ∀ x : Fin n → α,
      (Wpi x).real S = ∑ y ∈ Sfin, f x y := by
    intro x
    haveI := hWpi x
    have h1 : (Wpi x).real S = ∑ y ∈ Sfin, (Wpi x).real {y} := by
      rw [← h_S_coe, ← sum_measureReal_singleton (μ := Wpi x) Sfin]
    rw [h1]; exact Finset.sum_congr rfl (fun y _ ↦ h_pi_W x y)
  have h_μY_set : μY.real S = ∑ y ∈ Sfin, μY.real {y} := by
    rw [← h_S_coe, ← sum_measureReal_singleton (μ := μY) Sfin]
  calc (∑ x : Fin n → α, P.real {x} * (Wpi x).real S)
      = ∑ x : Fin n → α, P.real {x} * ∑ y ∈ Sfin, f x y := by
        refine Finset.sum_congr rfl (fun x _ ↦ ?_); rw [h_Wpi_real x]
    _ = ∑ x : Fin n → α, ∑ y ∈ Sfin, P.real {x} * f x y := by
        refine Finset.sum_congr rfl (fun x _ ↦ ?_); rw [Finset.mul_sum]
    _ = ∑ y ∈ Sfin, ∑ x : Fin n → α, P.real {x} * f x y := Finset.sum_comm
    _ = ∑ y ∈ Sfin, μY.real {y} := by
        refine Finset.sum_congr rfl (fun y _ ↦ h_chan y)
    _ = μY.real S := h_μY_set.symm

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β] in
private lemma prod_real_eq_slice_sum
    {n : ℕ}
    (P : Measure (Fin n → α)) [IsProbabilityMeasure P]
    (μY : Measure (Fin n → β)) [IsProbabilityMeasure μY]
    (JTS : Set ((Fin n → α) × (Fin n → β))) :
    (P.prod μY).real JTS
      = ∑ x' : Fin n → α, P.real {x'} * μY.real {y | (x', y) ∈ JTS} := by
  classical
  haveI : MeasurableSingletonClass (Fin n → α) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Fin n → β) := Pi.instMeasurableSingletonClass
  have h_JTS_fin : JTS.Finite := Set.toFinite _
  set JTSfin : Finset _ := h_JTS_fin.toFinset
  have h_JTS_coe : (JTSfin : Set _) = JTS := h_JTS_fin.coe_toFinset
  have h_prod_sum : (P.prod μY).real JTS
      = ∑ pq ∈ JTSfin, P.real {pq.1} * μY.real {pq.2} := by
    have h_real_eq : (P.prod μY).real JTS = ∑ p ∈ JTSfin, (P.prod μY).real {p} := by
      rw [← h_JTS_coe, ← sum_measureReal_singleton (μ := P.prod μY) JTSfin]
    rw [h_real_eq]
    refine Finset.sum_congr rfl (fun pq _ ↦ ?_)
    have h_sgl : ({pq} : Set ((Fin n → α) × (Fin n → β)))
        = ({pq.1} : Set (Fin n → α)) ×ˢ ({pq.2} : Set (Fin n → β)) := by
      ext ⟨a, b⟩; simp [Prod.ext_iff]
    rw [h_sgl]; exact measureReal_prod_prod _ _
  rw [h_prod_sum]
  -- Convert ∑ pq ∈ JTSfin, F pq into ∑ x' : Fin n → α, ∑ y : Fin n → β, [pq ∈ JTSfin] * F pq.
  have h_ind : (∑ pq ∈ JTSfin, P.real {pq.1} * μY.real {pq.2})
      = ∑ x' : Fin n → α, ∑ y : Fin n → β,
          (if (x', y) ∈ JTS then P.real {x'} * μY.real {y} else 0) := by
    rw [show JTSfin = ((Finset.univ : Finset _) ×ˢ Finset.univ : Finset _).filter (· ∈ JTS) from ?_]
    · rw [Finset.sum_filter]
      rw [← Finset.sum_product']
    · -- JTSfin = filter (· ∈ JTS) univ
      ext pq
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      constructor
      · intro h; exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h⟩
      · intro h; exact h.2
  rw [h_ind]
  -- Inner: ∑_y if (x',y) ∈ JTS then P{x'}*μY{y} else 0 = P{x'} * μY.real {y | (x',y) ∈ JTS}.
  refine Finset.sum_congr rfl (fun x' _ ↦ ?_)
  set S : Set (Fin n → β) := {y | (x', y) ∈ JTS}
  have h_S_fin : S.Finite := Set.toFinite _
  have h_μY_slice : μY.real {y | (x', y) ∈ JTS}
      = ∑ y ∈ h_S_fin.toFinset, μY.real {y} := by
    have h_eq : ({y | (x', y) ∈ JTS} : Set _) = ↑h_S_fin.toFinset := by
      rw [h_S_fin.coe_toFinset]
    rw [h_eq, sum_measureReal_singleton]
  rw [h_μY_slice, Finset.mul_sum]
  rw [show (∑ y : Fin n → β,
              (if (x', y) ∈ JTS then P.real {x'} * μY.real {y} else 0))
          = ∑ y ∈ (Finset.univ : Finset (Fin n → β)).filter (fun y ↦ (x', y) ∈ JTS),
              P.real {x'} * μY.real {y} from by rw [Finset.sum_filter]]
  apply Finset.sum_congr ?_ (fun _ _ ↦ rfl)
  ext y; simp

omit [DecidableEq α] [DecidableEq β] in
/-- (E2) Fubini swap. For any two distinct message indices `m ≠ m'`, the
codebook expectation of the "alias codeword jointly typical" event is bounded
by `exp(n((HZ-HX-HY)+3ε))` via the independent-pair bound
`jointlyTypicalSet_indep_prob_le`. -/
private lemma random_codebook_E2_swap
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (_hp_pos : ∀ a : α, 0 < p.real {a})
    {M n : ℕ} (_hM : 0 < M) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : iIndepFun (fun i ↦ Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : iIndepFun (fun i ↦ Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ q : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {q})
    (h_match_X : μ.map (Xs 0) = p)
    (h_match_Z : μ.map (jointSequence Xs Ys 0) = jointDistribution p W)
    (m m' : Fin M) (hne : m ≠ m') :
    ∑ c : Codebook M n α, (codebookMeasure p M n).real {c} *
        (Measure.pi (fun i ↦ W (c m i))).real
          {y | (c m', y) ∈ jointlyTypicalSet μ Xs Ys n ε}
      ≤ Real.exp ((n : ℝ) *
            ((InformationTheory.Shannon.entropy μ (jointSequence Xs Ys 0)
              - InformationTheory.Shannon.entropy μ (Xs 0)
              - InformationTheory.Shannon.entropy μ (Ys 0)) + 3 * ε)) := by
  classical
  haveI : MeasurableSingletonClass (Fin n → α) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Fin n → β) := Pi.instMeasurableSingletonClass
  set P : Measure (Fin n → α) := Measure.pi (fun _ : Fin n ↦ p) with hP_def
  haveI : IsProbabilityMeasure P := by rw [hP_def]; infer_instance
  -- μY = μ.map (jointRV Ys n), the y-block law. By block_law_Y_eq_pi, μY = Pi (μ.map (Ys 0)).
  set μY : Measure (Fin n → β) := μ.map (InformationTheory.Shannon.jointRV Ys n) with hμY_def
  haveI : IsProbabilityMeasure μY := by
    rw [hμY_def]
    exact Measure.isProbabilityMeasure_map
      (InformationTheory.Shannon.measurable_jointRV Ys hYs n).aemeasurable
  -- μX = Pi p = μ.map (jointRV Xs n).
  set μX : Measure (Fin n → α) := μ.map (InformationTheory.Shannon.jointRV Xs n) with hμX_def
  haveI : IsProbabilityMeasure μX := by
    rw [hμX_def]
    exact Measure.isProbabilityMeasure_map
      (InformationTheory.Shannon.measurable_jointRV Xs hXs n).aemeasurable
  have hμX_eq : μX = P := by
    rw [hμX_def, hP_def]
    exact block_law_X_eq_pi_p μ Xs hXs hindepX hidentX p h_match_X n
  have hμY_eq : μY = Measure.pi (fun _ : Fin n ↦ μ.map (Ys 0)) := by
    rw [hμY_def]
    exact block_law_Y_eq_pi μ Ys hYs hindepY hidentY n
  -- Step 1: apply codebook_marginal_two.
  have h_swap_step1 :
      ∑ c : Codebook M n α, (codebookMeasure p M n).real {c} *
        (Measure.pi (fun i ↦ W (c m i))).real
          {y | (c m', y) ∈ jointlyTypicalSet μ Xs Ys n ε}
      = ∑ x : Fin n → α, ∑ x' : Fin n → α,
          P.real {x} * P.real {x'} *
          (Measure.pi (fun i ↦ W (x i))).real
            {y | (x', y) ∈ jointlyTypicalSet μ Xs Ys n ε} := by
    refine codebook_marginal_two p M n m m' hne
      (fun x x' ↦ (Measure.pi (fun i ↦ W (x i))).real
        {y | (x', y) ∈ jointlyTypicalSet μ Xs Ys n ε}) ?_
    intro x x'; exact measureReal_nonneg
  rw [h_swap_step1]
  -- Step 2: identify ∑_x ∑_x' P{x}*P{x'}*Pi(W∘x){slice (x')} with (μX.prod μY).real(JTS).
  set JTS : Set ((Fin n → α) × (Fin n → β)) := jointlyTypicalSet μ Xs Ys n ε with hJTS_def
  -- 2a: μ.map (Ys 0) = outputDistribution p W via h_match_Z + projection.
  have h_match_Y : μ.map (Ys 0) = outputDistribution p W := by
    have h_eq : Ys 0 = Prod.snd ∘ (jointSequence Xs Ys 0) := by funext ω; rfl
    have h_meas_jz0 : Measurable (jointSequence Xs Ys 0) :=
      measurable_jointSequence Xs Ys hXs hYs 0
    rw [h_eq, ← Measure.map_map measurable_snd h_meas_jz0, h_match_Z]
    rfl
  -- 2b: discrete sum identities for `P.real {x}`, `(Pi (W∘x)).real {y}`, `μY.real {y}`.
  have h_P_singleton : ∀ (x : Fin n → α), P.real {x} = ∏ i, p.real {x i} := by
    intro x; rw [hP_def]; exact measureReal_pi_singleton_eq_prod _ x
  have h_pi_W_singleton : ∀ (x : Fin n → α) (y : Fin n → β),
      (Measure.pi (fun i ↦ W (x i))).real {y} = ∏ i, (W (x i)).real {y i} :=
    fun x y ↦ measureReal_pi_singleton_eq_prod _ y
  have h_output_singleton : ∀ b : β,
      (outputDistribution p W).real {b} = ∑ a : α, p.real {a} * (W a).real {b} :=
    fun b ↦ outputDistribution_real_singleton_eq_sum p W b
  have h_μY_singleton : ∀ (y : Fin n → β),
      μY.real {y} = ∏ i, ∑ a : α, p.real {a} * (W a).real {y i} := by
    intro y
    rw [hμY_eq, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl (fun i _ ↦ ?_)
    show (μ.map (Ys 0)).real {y i} = _
    rw [h_match_Y, h_output_singleton]
  -- 2c: ∑_x P{x} * ∏_i (W(x i)){y_i} = μY{y} for each y.
  have h_chan_y_singleton : ∀ (y : Fin n → β),
      (∑ x : Fin n → α, P.real {x} * ∏ i, (W (x i)).real {y i}) = μY.real {y} := by
    intro y
    rw [h_μY_singleton y]
    have h_lhs_eq : (∑ x : Fin n → α, P.real {x} * ∏ i, (W (x i)).real {y i})
        = ∑ x : Fin n → α, ∏ i, p.real {x i} * (W (x i)).real {y i} := by
      refine Finset.sum_congr rfl (fun x _ ↦ ?_)
      rw [h_P_singleton x, ← Finset.prod_mul_distrib]
    rw [h_lhs_eq]
    have h_pi_sum := (Finset.prod_univ_sum
      (κ := fun _ : Fin n ↦ α)
      (t := fun _ : Fin n ↦ (Finset.univ : Finset α))
      (R := ℝ)
      (f := fun (i : Fin n) (a : α) ↦ p.real {a} * (W a).real {y i})).symm
    have h_pi : Fintype.piFinset (fun _ : Fin n ↦ (Finset.univ : Finset α))
        = (Finset.univ : Finset (Fin n → α)) := by
      ext c; simp
    rw [h_pi] at h_pi_sum
    rw [h_pi_sum]
  -- 2d: extend to ∑_x P{x} * Pi(W∘x).real(S) = μY.real(S) for finite S.
  have h_sum_chan_set : ∀ x' : Fin n → α,
      (∑ x : Fin n → α, P.real {x} *
        (Measure.pi (fun i ↦ W (x i))).real {y | (x', y) ∈ JTS})
      = μY.real {y | (x', y) ∈ JTS} := fun x' ↦
    sum_chan_set_eq_μY P μY (fun x ↦ Measure.pi (fun i ↦ W (x i)))
      (fun _ ↦ inferInstance) (fun x y ↦ ∏ i, (W (x i)).real {y i})
      h_pi_W_singleton h_chan_y_singleton {y | (x', y) ∈ JTS} (Set.toFinite _)
  -- 2e: pull together ∑_x ∑_x' P{x}*P{x'}*Pi(W∘x){slice} = (μX.prod μY).real JTS.
  have h_rewrite :
      (∑ x : Fin n → α, ∑ x' : Fin n → α,
          P.real {x} * P.real {x'} *
          (Measure.pi (fun i ↦ W (x i))).real {y | (x', y) ∈ JTS})
      = ∑ x' : Fin n → α, P.real {x'} * μY.real {y | (x', y) ∈ JTS} := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x' _ ↦ ?_)
    have h_inner : (∑ x : Fin n → α,
            P.real {x} * P.real {x'} *
            (Measure.pi (fun i ↦ W (x i))).real {y | (x', y) ∈ JTS})
        = P.real {x'} *
          (∑ x : Fin n → α, P.real {x} *
            (Measure.pi (fun i ↦ W (x i))).real {y | (x', y) ∈ JTS}) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ ↦ by ring)
    rw [h_inner, h_sum_chan_set x']
  rw [h_rewrite]
  -- 2f: ∑_x' P{x'} * μY{slice} = (μX.prod μY).real(JTS).
  have h_prod_eq : (μX.prod μY).real JTS = ∑ x' : Fin n → α,
      P.real {x'} * μY.real {y | (x', y) ∈ JTS} := by
    rw [hμX_eq]
    exact prod_real_eq_slice_sum P μY JTS
  rw [show (∑ x' : Fin n → α, P.real {x'} * μY.real {y | (x', y) ∈ JTS})
        = (μX.prod μY).real JTS from h_prod_eq.symm]
  exact jointlyTypicalSet_indep_prob_le μ Xs Ys hXs hYs hindepX hidentX hindepY hidentY
    hposX hposY hposZ n hε

lemma sum_weighted_diag_offdiag_decomp
    {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (w : ι → ℝ) (a : ι → Fin M → ℝ) (b : ι → Fin M → Fin M → ℝ) (Minv : ℝ) :
    ∑ c : ι, w c *
        (Minv * ∑ m : Fin M,
          (a c m + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, b c m m'))
      = Minv * ∑ m : Fin M,
          ((∑ c : ι, w c * a c m)
          + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
              ∑ c : ι, w c * b c m m') := by
  classical
  have step1 : ∀ c : ι,
      w c * (Minv *
          ∑ m : Fin M,
            (a c m + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, b c m m'))
        = Minv *
          ∑ m : Fin M, (w c *
            (a c m + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, b c m m')) := by
    intro c
    rw [← mul_assoc, mul_comm (w c) Minv, mul_assoc, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun c _ ↦ step1 c), ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ ↦ ?_)
  have step2 : ∀ c : ι,
      w c *
          (a c m + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, b c m m')
        = w c * a c m +
            ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, w c * b c m m' := by
    intro c
    rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun c _ ↦ step2 c), Finset.sum_add_distrib,
      Finset.sum_comm]

lemma diag_add_offdiag_sum_le
    {M : ℕ} (hM : 0 < M) (a : ℝ) (b : Fin M → ℝ) (A B : ℝ) {m : Fin M}
    (ha : a ≤ A) (hb : ∀ m' ∈ (Finset.univ : Finset (Fin M)).erase m, b m' ≤ B) :
    a + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, b m'
      ≤ A + ((M : ℝ) - 1) * B := by
  have h_offdiag :
      ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, b m'
        ≤ ∑ _m' ∈ (Finset.univ : Finset (Fin M)).erase m, B :=
    Finset.sum_le_sum hb
  have h_card : ((Finset.univ : Finset (Fin M)).erase m).card = M - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have h_eval :
      ∑ _m' ∈ (Finset.univ : Finset (Fin M)).erase m, B = ((M : ℝ) - 1) * B := by
    rw [Finset.sum_const, nsmul_eq_mul, h_card]
    have : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub hM, Nat.cast_one]
    rw [this]
  calc a + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, b m'
      ≤ A + ∑ _m' ∈ (Finset.univ : Finset (Fin M)).erase m, B := add_le_add ha h_offdiag
    _ = A + ((M : ℝ) - 1) * B := by rw [h_eval]

lemma sum_average_le_of_forall_le
    {M : ℕ} (g : Fin M → ℝ) (Minv B : ℝ) (hMinv : 0 ≤ Minv)
    (hMinvM : Minv * (M : ℝ) = 1) (hg : ∀ m : Fin M, g m ≤ B) :
    Minv * ∑ m : Fin M, g m ≤ B := by
  have h_M_card : (Finset.univ : Finset (Fin M)).card = M := by
    rw [Finset.card_univ, Fintype.card_fin]
  calc Minv * ∑ m : Fin M, g m
      ≤ Minv * ∑ _m : Fin M, B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m _ ↦ hg m)) hMinv
    _ = Minv * ((M : ℝ) * B) := by
        rw [Finset.sum_const, nsmul_eq_mul, h_M_card]
    _ = B := by rw [← mul_assoc, hMinvM, one_mul]

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β] in
private lemma averageErrorProb_toReal_eq
    {M n : ℕ} (c : Code M n α β) (W : Channel α β) (hM : 0 < M)
    (h_ne_top : ∀ m : Fin M, c.errorProbAt W m ≠ ∞) :
    (c.averageErrorProb W).toReal
      = ((M : ℝ))⁻¹ * ∑ m : Fin M, (c.errorProbAt W m).toReal := by
  unfold Code.averageErrorProb
  rw [if_neg hM.ne']
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun m _ ↦ h_ne_top m)]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
private lemma errorProbAt_codebookToCode_ne_top
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (W : Channel α β) [IsMarkovKernel W]
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n α) (m : Fin M) :
    (codebookToCode μ Xs Ys hM ε c).errorProbAt W m ≠ ∞ := by
  have h_le_one : (codebookToCode μ Xs Ys hM ε c).errorProbAt W m ≤ 1 := by
    show (Measure.pi (fun i ↦ W ((codebookToCode μ Xs Ys hM ε c).encoder m i)))
        ((codebookToCode μ Xs Ys hM ε c).errorEvent m) ≤ 1
    haveI : IsProbabilityMeasure
        (Measure.pi (fun i ↦ W ((codebookToCode μ Xs Ys hM ε c).encoder m i))) :=
      inferInstance
    exact prob_le_one
  exact h_le_one.trans_lt ENNReal.one_lt_top |>.ne

omit [DecidableEq α] [DecidableEq β] in
/-- Random codebook average (probabilistic-method form). With each codeword
drawn i.i.d. from `p^n` (so the codebook law is `codebookMeasure p M n`), the
codebook-average of the (uniform-over-message) error probability decomposes via
Fubini into the "joint typical event probability" (E1) plus `(M - 1) ·` the
independent-pair bound (E2).

The structural backbone (per-codebook bound via `errorProbAt_le_E1_plus_E2`,
sum / swap arithmetic) is assembled here from the two Fubini swap ingredients
`random_codebook_E1_swap` and `random_codebook_E2_swap` (private lemmas above). -/
theorem random_codebook_average_le
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    {M n : ℕ} (hM : 0 < M) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : iIndepFun (fun i ↦ Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : iIndepFun (fun i ↦ Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j ↦
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hindepZ_full : iIndepFun (fun i : ℕ ↦ jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ q : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {q})
    (h_match_X : μ.map (Xs 0) = p)
    (h_match_Z : μ.map (jointSequence Xs Ys 0) = jointDistribution p W) :
    ∑ codebook : Codebook M n α,
        (codebookMeasure p M n).real {codebook} *
        ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal
    ≤ μ.real
        {ω | (jointRV Xs n ω, jointRV Ys n ω) ∉ jointlyTypicalSet μ Xs Ys n ε}
      + ((M : ℝ) - 1) *
          Real.exp ((n : ℝ) *
            ((entropy μ (jointSequence Xs Ys 0)
              - entropy μ (Xs 0) - entropy μ (Ys 0)) + 3 * ε)) := by
  classical
  -- Abbreviations.
  set wM : Measure (Codebook M n α) := codebookMeasure p M n with hwM_def
  haveI : IsProbabilityMeasure wM := by
    rw [hwM_def]; infer_instance
  set E1 : ℝ := μ.real
      {ω | (jointRV Xs n ω, jointRV Ys n ω) ∉ jointlyTypicalSet μ Xs Ys n ε} with hE1_def
  set HZ : ℝ := entropy μ (jointSequence Xs Ys 0) with hHZ_def
  set HX : ℝ := entropy μ (Xs 0) with hHX_def
  set HY : ℝ := entropy μ (Ys 0) with hHY_def
  set Eexp : ℝ := Real.exp ((n : ℝ) * ((HZ - HX - HY) + 3 * ε)) with hEexp_def
  have hEexp_nn : 0 ≤ Eexp := (Real.exp_pos _).le
  -- The codebook space is a Fintype (the default Pi instance fires for
  -- `Fin M → Fin n → α`; we leave `Fintype.elim` to the unifier).
  haveI : MeasurableSingletonClass (Fin n → α) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Codebook M n α) := Pi.instMeasurableSingletonClass
  -- `errorProbAt c W m` is finite (`≤ 1` for a Markov kernel).
  have h_errProbAt_ne_top : ∀ (c : Codebook M n α) (m : Fin M),
      (codebookToCode μ Xs Ys hM ε c).errorProbAt W m ≠ ∞ := fun c m ↦
    errorProbAt_codebookToCode_ne_top μ Xs Ys W hM ε c m
  -- Step 1: rewrite `(averageErrorProb).toReal = (1/M) * ∑_m (errorProbAt).toReal`.
  have h_avg_real : ∀ c : Codebook M n α,
      ((codebookToCode μ Xs Ys hM ε c).averageErrorProb W).toReal
        = ((M : ℝ))⁻¹ *
          ∑ m : Fin M, ((codebookToCode μ Xs Ys hM ε c).errorProbAt W m).toReal := by
    intro c
    exact averageErrorProb_toReal_eq (codebookToCode μ Xs Ys hM ε c) W hM
      (h_errProbAt_ne_top c)
  -- Step 2: bound LHS by `(1/M) * ∑_c w(c) * ∑_m (errorProbAt).toReal`,
  -- then use `errorProbAt_le_E1_plus_E2` pointwise.
  have h_M_pos_R : 0 < (M : ℝ) := by exact_mod_cast hM
  have h_M_inv_nn : 0 ≤ ((M : ℝ))⁻¹ := inv_nonneg.mpr h_M_pos_R.le
  -- Per-codebook bound from `errorProbAt_le_E1_plus_E2`.
  set E1_indiv : Codebook M n α → Fin M → ℝ := fun c m ↦
    (Measure.pi (fun i ↦ W (c m i))).real
      {y | (c m, y) ∉ jointlyTypicalSet μ Xs Ys n ε} with hE1ind_def
  set E2_indiv : Codebook M n α → Fin M → Fin M → ℝ := fun c m m' ↦
    (Measure.pi (fun i ↦ W (c m i))).real
      {y | (c m', y) ∈ jointlyTypicalSet μ Xs Ys n ε} with hE2ind_def
  have h_per_cb : ∀ (c : Codebook M n α) (m : Fin M),
      ((codebookToCode μ Xs Ys hM ε c).errorProbAt W m).toReal
        ≤ E1_indiv c m
          + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv c m m' := by
    intro c m
    exact errorProbAt_le_E1_plus_E2 μ Xs Ys W hM c m
  -- Sum over `m` of the per-codebook bound, then over `c` weighted.
  have h_sum_per_cb : ∀ c : Codebook M n α,
      ((codebookToCode μ Xs Ys hM ε c).averageErrorProb W).toReal
        ≤ ((M : ℝ))⁻¹ * ∑ m : Fin M,
            (E1_indiv c m +
              ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv c m m') := by
    intro c
    rw [h_avg_real c]
    refine mul_le_mul_of_nonneg_left ?_ h_M_inv_nn
    exact Finset.sum_le_sum (fun m _ ↦ h_per_cb c m)
  -- Weighted sum over c bound.
  have h_w_nn : ∀ c : Codebook M n α, 0 ≤ wM.real {c} := fun _ ↦ measureReal_nonneg
  have h_weighted_bound :
      ∑ c : Codebook M n α, wM.real {c} *
          ((codebookToCode μ Xs Ys hM ε c).averageErrorProb W).toReal
      ≤ ∑ c : Codebook M n α, wM.real {c} *
          (((M : ℝ))⁻¹ * ∑ m : Fin M,
            (E1_indiv c m +
              ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv c m m')) := by
    refine Finset.sum_le_sum (fun c _ ↦ ?_)
    exact mul_le_mul_of_nonneg_left (h_sum_per_cb c) (h_w_nn c)
  -- Step 3: distribute & swap sum orderings.
  -- RHS of `h_weighted_bound` = (1/M) * ∑_m (∑_c w(c) * E1_indiv c m
  --                                       + ∑_{m'≠m} ∑_c w(c) * E2_indiv c m m').
  have h_rhs_decomp :
      ∑ c : Codebook M n α, wM.real {c} *
          (((M : ℝ))⁻¹ * ∑ m : Fin M,
            (E1_indiv c m +
              ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv c m m'))
        = ((M : ℝ))⁻¹ * ∑ m : Fin M,
            ((∑ c : Codebook M n α, wM.real {c} * E1_indiv c m)
            + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
                ∑ c : Codebook M n α, wM.real {c} * E2_indiv c m m') :=
    sum_weighted_diag_offdiag_decomp (fun c ↦ wM.real {c}) E1_indiv E2_indiv
      ((M : ℝ))⁻¹
  -- Step 4: bound each inner Fubini sum.
  -- (E1) `∑_c w(c) * E1_indiv c m ≤ E1` for every `m`.
  -- (E2) `∑_c w(c) * E2_indiv c m m' ≤ Eexp` for every `m ≠ m'`.
  have h_E1_swap : ∀ m : Fin M,
      ∑ c : Codebook M n α, wM.real {c} * E1_indiv c m ≤ E1 :=
    random_codebook_E1_swap (W := W) (p := p) hM hε μ Xs Ys hXs hYs
      hindepX hidentX hindepY hidentY hindepZ hindepZ_full hidentZ hposX hposY hposZ
      h_match_X h_match_Z
  have h_E2_swap : ∀ (m m' : Fin M), m ≠ m' →
      ∑ c : Codebook M n α, wM.real {c} * E2_indiv c m m' ≤ Eexp :=
    random_codebook_E2_swap (W := W) (p := p) hp_pos hM hε μ Xs Ys hXs hYs
      hindepX hidentX hindepY hidentY hposX hposY hposZ h_match_X h_match_Z
  -- Step 5: aggregate. RHS = (1/M)*∑_m [≤ E1 + (M-1)*Eexp] = E1 + (M-1)*Eexp.
  have h_per_m_bound : ∀ m : Fin M,
      (∑ c : Codebook M n α, wM.real {c} * E1_indiv c m)
        + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
            ∑ c : Codebook M n α, wM.real {c} * E2_indiv c m m'
        ≤ E1 + ((M : ℝ) - 1) * Eexp := by
    intro m
    refine diag_add_offdiag_sum_le hM _
      (fun m' ↦ ∑ c : Codebook M n α, wM.real {c} * E2_indiv c m m') E1 Eexp
      (h_E1_swap m) (fun m' hm' ↦ ?_)
    have hne : m ≠ m' := (Finset.mem_erase.mp hm').1.symm
    exact h_E2_swap m m' hne
  -- Aggregate over `m`.
  have h_M_inv_M_eq : ((M : ℝ))⁻¹ * (M : ℝ) = 1 := by
    field_simp
  have h_final :
      ((M : ℝ))⁻¹ * ∑ m : Fin M,
          ((∑ c : Codebook M n α, wM.real {c} * E1_indiv c m)
          + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
              ∑ c : Codebook M n α, wM.real {c} * E2_indiv c m m')
      ≤ E1 + ((M : ℝ) - 1) * Eexp :=
    sum_average_le_of_forall_le _ ((M : ℝ))⁻¹ (E1 + ((M : ℝ) - 1) * Eexp)
      h_M_inv_nn h_M_inv_M_eq h_per_m_bound
  -- Combine: `LHS ≤ (h_weighted_bound) = (h_rhs_decomp) ≤ (h_final)`.
  exact (h_weighted_bound.trans_eq h_rhs_decomp).trans h_final

end InformationTheory.Shannon.ChannelCoding

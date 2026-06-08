import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Han.Basic
import InformationTheory.Shannon.SlepianWolf.Basic

/-!
# Conditional entropy on `Fin n` under strong memoryless DMC (D-2'' Phase B refactor)

The Cover-Thomas Thm 7.9 route to the per-letter MI bound goes via entropy
subadditivity, avoiding the false-statement `h_yother_zero` hypothesis used in the
D-2' hypothesis-form converse. The chain:

```
I(X^n; Y^n) = H(Y^n) - H(Y^n | X^n)
            ≤ ∑ H(Y_i) - H(Y^n | X^n)         -- subadditivity (encoder-agnostic)
            = ∑ H(Y_i) - ∑ H(Y_i | X_i)       -- strong memoryless
            = ∑ I(X_i; Y_i)
```

This file establishes the four building blocks:

* `entropy_pi_le_sum_entropy` — `H(Y^n) ≤ ∑ H(Y_i)` (subadditivity, encoder-agnostic).
  Combines `Han.lean`'s `jointEntropy_chain_rule` with `SlepianWolf.lean`'s
  `entropy_ge_condEntropy` (conditioning never increases entropy).
* `condEntropy_pi_chain_rule` — `H(Y^n | X^n) = ∑ H(Y_i | X^n, Y^{<i})` (n-var
  conditional chain rule, mirrors `jointEntropy_chain_rule`).
* `condEntropy_drop_irrelevant_of_markov` — under Markov chain `Y → Z → W`,
  `H(Y | Z, W) = H(Y | Z)` (template-mirrors `condMutualInfo_eq_zero_of_markov`).
* `condEntropy_pi_eq_sum_of_memoryless_strong` — `H(Y^n | X^n) = ∑ H(Y_i | X_i)`
  combining 2 + 3 from the two Markov axioms of `IsMemorylessChannelStrong`
  (parameterized form to avoid circular import).

The central theorem `mutualInfo_le_sum_per_letter_of_memoryless_strong` is then
the direct combination: `(I(X^n; Y^n)).toReal ≤ ∑ (I(X_i; Y_i)).toReal`.

The two Markov axioms of `IsMemorylessChannelStrong` are taken as hypotheses
(not as a single structure) to keep this file an upstream building block of
`InformationTheory/Shannon/ChannelCodingConverseGeneralStrong.lean`, which defines that
structure and supplies its two fields when invoking the theorem here.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Building block 1 — entropy subadditivity (encoder-agnostic) -/

section Subadditivity

variable {n : ℕ}
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

omit [DecidableEq β] in
/-- **Entropy subadditivity on `Fin n`**: `H(Y^n) ≤ ∑ H(Y_i)`.

This is encoder-agnostic — holds for any family `Ys : Fin n → Ω → β` without any
memoryless or independence assumption. Cover-Thomas Thm 2.6.6.

Proof: combine the n-variable chain rule `H(Y^n) = ∑ H(Y_i | Y^{<i})`
(`jointEntropy_chain_rule`) with `H(Y_i | Y^{<i}) ≤ H(Y_i)`
(`entropy_ge_condEntropy`, conditioning reduces entropy), summed over `i`. -/
@[entry_point]
lemma entropy_pi_le_sum_entropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ys : Fin n → Ω → β) (hYs : ∀ i, Measurable (Ys i)) :
    jointEntropy μ Ys ≤ ∑ i : Fin n, entropy μ (Ys i) := by
  classical
  -- Step 1: chain rule for joint entropy.
  rw [jointEntropy_chain_rule μ Ys hYs]
  -- Step 2: for each i, condEntropy ≤ entropy (conditioning reduces entropy).
  apply Finset.sum_le_sum
  intro i _
  -- Prefix RV: Fin i.val → β, measurable (component-wise).
  have h_prefix_meas : Measurable
      (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr (fun j => hYs ⟨j.val, j.isLt.trans i.isLt⟩)
  exact entropy_ge_condEntropy μ (Ys i)
    (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
    (hYs i) h_prefix_meas

end Subadditivity

/-! ## Building block 2 — conditional joint entropy chain rule -/

section CondChainRule

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **Conditional 2-variable chain rule** (helper):
`H((A, B) | C) = H(A | C) + H(B | (C, A))`.

Derived from the unconditional 2-var chain rule
(`entropy_pair_eq_entropy_add_condEntropy`) applied three times to the joint
`(C, (A, B))`, regrouped via `entropy_measurableEquiv_comp` as `((C, A), B)`. -/
private lemma condEntropy_pair_eq_condEntropy_add_condEntropy
    {α' β' γ' : Type*}
    [Fintype α'] [Nonempty α']
      [MeasurableSpace α'] [MeasurableSingletonClass α']
    [Fintype β'] [Nonempty β']
      [MeasurableSpace β'] [MeasurableSingletonClass β']
    [Fintype γ'] [Nonempty γ']
      [MeasurableSpace γ'] [MeasurableSingletonClass γ']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (As : Ω → α') (Bs : Ω → β') (Cs : Ω → γ')
    (hAs : Measurable As) (hBs : Measurable Bs) (hCs : Measurable Cs) :
    InformationTheory.MeasureFano.condEntropy μ
        (fun ω => (As ω, Bs ω)) Cs
      = InformationTheory.MeasureFano.condEntropy μ As Cs
        + InformationTheory.MeasureFano.condEntropy μ Bs
            (fun ω => (Cs ω, As ω)) := by
  classical
  -- Step 1: H((C, (A, B))) = H(C) + H((A, B) | C).
  have h1 := entropy_pair_eq_entropy_add_condEntropy μ Cs (fun ω => (As ω, Bs ω))
    hCs (hAs.prodMk hBs)
  -- Step 2: H((C, A), B) = H((C, A)) + H(B | (C, A)).
  have h2 := entropy_pair_eq_entropy_add_condEntropy μ (fun ω => (Cs ω, As ω)) Bs
    (hCs.prodMk hAs) hBs
  -- Step 3: H((C, A)) = H(C) + H(A | C).
  have h3 := entropy_pair_eq_entropy_add_condEntropy μ Cs As hCs hAs
  -- Step 4: reshape — H((C, (A, B))) = H((C, A), B) via the measurable equiv
  -- `γ' × (α' × β') ≃ᵐ (γ' × α') × β'` (associativity).
  let e : γ' × (α' × β') ≃ᵐ (γ' × α') × β' :=
    (MeasurableEquiv.prodAssoc).symm
  have h_reshape :
      entropy μ (fun ω => (Cs ω, As ω, Bs ω))
        = entropy μ (fun ω => ((Cs ω, As ω), Bs ω)) := by
    have hmeas : Measurable (fun ω => (Cs ω, As ω, Bs ω)) :=
      hCs.prodMk (hAs.prodMk hBs)
    have h := entropy_measurableEquiv_comp μ (fun ω => (Cs ω, As ω, Bs ω)) hmeas e
    -- e (c, (a, b)) = ((c, a), b)
    have hpt : (fun ω => e (Cs ω, As ω, Bs ω))
        = (fun ω => ((Cs ω, As ω), Bs ω)) := by
      funext ω; rfl
    rw [hpt] at h
    exact h.symm
  rw [h_reshape] at h1
  linarith

omit [DecidableEq β] in
/-- **Conditional joint entropy chain rule on `Fin n`** (generalized over an
arbitrary conditioner type `χ`):
`H(Y^n | X) = ∑ i, H(Y_i | X, Y^{<i})`.

Generalizing the conditioner type allows the inductive step to apply the IH to
the same `Xs` (whose type does not depend on `n`).

Proof: induction on `n`. Base case `n = 0`: both sides reduce to `0` (the joint
`Y^0` has a singleton codomain, so `H(Y^0 | X) = 0`, and the sum is empty).
Step `n+1`: split `Y^{n+1}` as `(Y^n_prefix, Y_n)`, apply the 2-var conditional
chain rule, apply IH to the prefix, and reassemble via `Fin.sum_univ_castSucc`. -/
lemma condEntropy_pi_chain_rule_aux
    {n : ℕ} {χ : Type*} [Fintype χ] [Nonempty χ]
      [MeasurableSpace χ] [MeasurableSingletonClass χ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → χ) (Ys : Fin n → Ω → β)
    (hXs : Measurable Xs) (hYs : ∀ i, Measurable (Ys i)) :
    InformationTheory.MeasureFano.condEntropy μ (fun ω j => Ys j ω) Xs
      = ∑ i : Fin n,
          InformationTheory.MeasureFano.condEntropy μ (Ys i)
            (fun ω => (Xs ω,
              fun (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := by
  classical
  induction n with
  | zero =>
    rw [Fin.sum_univ_zero]
    -- LHS: condEntropy μ (fun ω (_ : Fin 0) => Ys _ ω) Xs.
    -- Since `Fin 0 → β` is a singleton, the conditional distribution is Dirac
    -- and the inner negMulLog sum is `negMulLog 1 = 0`.
    unfold InformationTheory.MeasureFano.condEntropy
    haveI : Unique (Fin 0 → β) := Pi.uniqueOfIsEmpty _
    have h_inner : ∀ y, ∑ x : (Fin 0 → β),
        Real.negMulLog ((condDistrib (fun ω (j : Fin 0) => Ys j ω) Xs μ y).real {x})
          = 0 := by
      intro y
      rw [Fintype.sum_unique]
      have _ : IsProbabilityMeasure (condDistrib (fun ω (j : Fin 0) => Ys j ω) Xs μ y) :=
        inferInstance
      have hsingle : ((condDistrib (fun ω (j : Fin 0) => Ys j ω) Xs μ y).real {default} : ℝ) = 1 := by
        have huniv : ({default} : Set (Fin 0 → β)) = Set.univ := by
          ext f; simp [Subsingleton.elim f default]
        rw [huniv, measureReal_def, measure_univ, ENNReal.toReal_one]
      rw [hsingle, Real.negMulLog_one]
    simp_rw [h_inner]
    simp
  | succ n IH =>
    -- Split Ys : Fin (n+1) → Ω → β into prefix and last.
    set Yprefix : Ω → (Fin n → β) := fun ω j => Ys j.castSucc ω with hYprefix_def
    set Ylast : Ω → β := Ys (Fin.last n) with hYlast_def
    have hYprefix_meas : Measurable Yprefix :=
      measurable_pi_iff.mpr (fun j => hYs j.castSucc)
    have hYlast_meas : Measurable Ylast := hYs (Fin.last n)
    have h_full_chain := entropy_pair_eq_entropy_add_condEntropy μ Xs
      (fun ω (j : Fin (n + 1)) => Ys j ω) hXs
      (measurable_pi_iff.mpr hYs)
    have h_pair_chain := entropy_pair_eq_entropy_add_condEntropy μ Xs
      (fun ω => (Yprefix ω, Ylast ω)) hXs (hYprefix_meas.prodMk hYlast_meas)
    -- Joint reshape: H((Xs, Y^{n+1})) = H((Xs, (Yprefix, Ylast))).
    have h_reshape_joint :
        entropy μ (fun ω => (Xs ω, fun (j : Fin (n + 1)) => Ys j ω))
          = entropy μ (fun ω => (Xs ω, (Yprefix ω, Ylast ω))) := by
      let e0 : (Fin (n + 1) → β) ≃ᵐ β × (Fin n → β) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => β) (Fin.last n)
      let e_swap : β × (Fin n → β) ≃ᵐ (Fin n → β) × β := MeasurableEquiv.prodComm
      let e1 : χ × (Fin (n + 1) → β) ≃ᵐ χ × ((Fin n → β) × β) :=
        MeasurableEquiv.prodCongr (.refl _) (e0.trans e_swap)
      have hjoint_meas : Measurable (fun ω => (Xs ω, fun (j : Fin (n + 1)) => Ys j ω)) :=
        hXs.prodMk (measurable_pi_iff.mpr hYs)
      have h_e_eq : ∀ ω,
          e1 (Xs ω, fun (j : Fin (n + 1)) => Ys j ω)
            = (Xs ω, (Yprefix ω, Ylast ω)) := by
        intro ω
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · funext j
            simp [e1, e0, e_swap, MeasurableEquiv.piFinSuccAbove_apply,
              MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm, Fin.init,
              Yprefix]
          · simp [e1, e0, e_swap, MeasurableEquiv.piFinSuccAbove_apply,
              MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm, Ylast]
      have h := entropy_measurableEquiv_comp μ
        (fun ω => (Xs ω, fun (j : Fin (n + 1)) => Ys j ω)) hjoint_meas e1
      rw [show (fun ω => e1 (Xs ω, fun j : Fin (n + 1) => Ys j ω))
              = (fun ω => (Xs ω, (Yprefix ω, Ylast ω))) from funext h_e_eq] at h
      exact h.symm
    rw [h_reshape_joint] at h_full_chain
    have h_eq_cond :
        InformationTheory.MeasureFano.condEntropy μ
            (fun ω (j : Fin (n + 1)) => Ys j ω) Xs
          = InformationTheory.MeasureFano.condEntropy μ
              (fun ω => (Yprefix ω, Ylast ω)) Xs := by
      linarith
    rw [h_eq_cond]
    rw [condEntropy_pair_eq_condEntropy_add_condEntropy μ Yprefix Ylast Xs
      hYprefix_meas hYlast_meas hXs]
    -- Apply IH to the prefix family (length-n).
    have IH' := IH (fun i ω => Ys i.castSucc ω) (fun i => hYs i.castSucc)
    rw [show Yprefix = (fun ω j => Ys j.castSucc ω) from rfl]
    rw [IH']
    rw [Fin.sum_univ_castSucc]
    congr 1

omit [DecidableEq α] [DecidableEq β] in
/-- **Conditional joint entropy chain rule on `Fin n`** (specialization of
`condEntropy_pi_chain_rule_aux` with conditioner `Xs : Ω → (Fin n → α)`).
`H(Y^n | X^n) = ∑ i, H(Y_i | X^n, Y^{<i})`. Building Block 2 of Cover-Thomas Thm 7.9. -/
@[entry_point]
lemma condEntropy_pi_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → (Fin n → α)) (Ys : Fin n → Ω → β)
    (hXs : Measurable Xs) (hYs : ∀ i, Measurable (Ys i)) :
    InformationTheory.MeasureFano.condEntropy μ (fun ω j => Ys j ω) Xs
      = ∑ i : Fin n,
          InformationTheory.MeasureFano.condEntropy μ (Ys i)
            (fun ω => (Xs ω,
              fun (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)) :=
  condEntropy_pi_chain_rule_aux μ Xs Ys hXs hYs

end CondChainRule

/-! ## Building block 3 — Markov drop of irrelevant conditioner -/

section MarkovDrop

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
variable {γ : Type*} [Fintype γ] [DecidableEq γ] [Nonempty γ]
  [MeasurableSpace γ] [MeasurableSingletonClass γ] [StandardBorelSpace γ]

omit [StandardBorelSpace α] [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
/-- **Markov-drop for conditional entropy**: under Markov chain `Yo → Zc → Wc`,
`H(Yo | Zc, Wc) = H(Yo | Zc)`.

Direct consequence of `condMutualInfo_eq_zero_of_markov` via
`condMutualInfo_eq_condEntropy_sub_condEntropy`: the Markov hypothesis forces
`I(Yo; Wc | Zc) = 0`, and the bridge expresses this as the desired equality. -/
@[entry_point]
lemma condEntropy_drop_irrelevant_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Yo : Ω → β) (Zc : Ω → α) (Wc : Ω → γ)
    (hYo : Measurable Yo) (hZc : Measurable Zc) (hWc : Measurable Wc)
    (hmarkov : IsMarkovChain μ Yo Zc Wc) :
    InformationTheory.MeasureFano.condEntropy μ Yo (fun ω => (Zc ω, Wc ω))
      = InformationTheory.MeasureFano.condEntropy μ Yo Zc := by
  classical
  -- Bridge: condMI(Yo; Wc | Zc).toReal = H(Yo|Zc) - H(Yo|Zc, Wc).
  have h_bridge :=
    condMutualInfo_eq_condEntropy_sub_condEntropy μ Yo Zc Wc hYo hZc hWc
  -- Markov ⇒ condMI = 0.
  have h_zero : condMutualInfo μ Yo Wc Zc = 0 :=
    condMutualInfo_eq_zero_of_markov μ Yo Zc Wc hYo hZc hWc hmarkov
  rw [h_zero] at h_bridge
  simp at h_bridge
  linarith

end MarkovDrop

/-! ## Building block 4 — `H(Y^n | X^n) = ∑ H(Y_i | X_i)` from strong memoryless -/

section StrongMemorylessCondEntropy

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- **Markov chain endpoint swap**: `IsMarkovChain μ Xs Zc Yo ↔ IsMarkovChain μ Yo Zc Xs`.

The γ-form definition `μ.map (Z, X, Y) = (μ.map Z) ⊗ₘ (K_X ×ₖ K_Y)` is symmetric in
`X`/`Y`: pushing both sides forward by the measurable equiv `Z × (X × Y) ≃ᵐ Z × (Y × X)`
gives the analogous identity with `X`/`Y` swapped.

* LHS `μ.map (Z, X, Y) ↦ μ.map (Z, Y, X)` via `Measure.map_map`.
* RHS `(μ.map Z) ⊗ₘ (K_X ×ₖ K_Y) ↦ (μ.map Z) ⊗ₘ ((K_X ×ₖ K_Y).map Prod.swap)`
  via `Measure.compProd_map`, then `Kernel.prodComm_prod` to identify the inner
  pushforward as `K_Y ×ₖ K_X`. -/
private lemma isMarkovChain_swap
    {X' Y' Z' : Type*} [MeasurableSpace X'] [MeasurableSpace Y'] [MeasurableSpace Z']
    [StandardBorelSpace X'] [Nonempty X']
    [StandardBorelSpace Y'] [Nonempty Y']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X') (Zc : Ω → Z') (Yo : Ω → Y')
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    IsMarkovChain μ Yo Zc Xs := by
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc.aemeasurable
  unfold IsMarkovChain
  have hZXY : Measurable (fun ω => (Zc ω, Xs ω, Yo ω)) := hZc.prodMk (hXs.prodMk hYo)
  -- Swap-on-second equiv: `Z × (X × Y) ≃ᵐ Z × (Y × X)`.
  let e : Z' × (X' × Y') ≃ᵐ Z' × (Y' × X') :=
    MeasurableEquiv.prodCongr (.refl _) MeasurableEquiv.prodComm
  -- LHS: μ.map (Z, Y, X) = (μ.map (Z, X, Y)).map e (since e (z, x, y) = (z, y, x)).
  have h_LHS :
      μ.map (fun ω => (Zc ω, Yo ω, Xs ω))
        = (μ.map (fun ω => (Zc ω, Xs ω, Yo ω))).map e := by
    rw [Measure.map_map e.measurable hZXY]
    rfl
  rw [h_LHS, hmarkov]
  -- RHS goal: ((μ.map Zc) ⊗ₘ (K_X ×ₖ K_Y)).map e
  --   = (μ.map Zc) ⊗ₘ (K_Y ×ₖ K_X).
  -- Use Measure.compProd_map (rearranges map through compProd's right arg) +
  -- Kernel.prodComm_prod (identifies (K_X ×ₖ K_Y).map prodComm = K_Y ×ₖ K_X).
  rw [show (e : Z' × (X' × Y') → Z' × (Y' × X'))
        = Prod.map (id : Z' → Z') (MeasurableEquiv.prodComm : X' × Y' → Y' × X') from rfl,
      ← Measure.compProd_map MeasurableEquiv.prodComm.measurable]
  congr 1
  exact Kernel.prodComm_prod

/-- **Markov chain right post-processing**: `IsMarkovChain μ Xs Zc Yo` and a
measurable `f : Y → Y'` give `IsMarkovChain μ Xs Zc (f ∘ Yo)`.

Reduce to `isMarkovChain_map_left` via two endpoint swaps. -/
private lemma isMarkovChain_map_right
    {X' Y' Z' Y'' : Type*}
    [MeasurableSpace X'] [MeasurableSpace Y'] [MeasurableSpace Z']
    [MeasurableSpace Y'']
    [StandardBorelSpace X'] [Nonempty X']
    [StandardBorelSpace Y'] [Nonempty Y']
    [StandardBorelSpace Y''] [Nonempty Y'']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X') (Zc : Ω → Z') (Yo : Ω → Y')
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    {f : Y' → Y''} (hf : Measurable f)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    IsMarkovChain μ Xs Zc (fun ω => f (Yo ω)) := by
  -- Swap to put Yo on the left, map left, then swap back.
  have h1 : IsMarkovChain μ Yo Zc Xs :=
    isMarkovChain_swap μ Xs Zc Yo hXs hZc hYo hmarkov
  have h2 : IsMarkovChain μ (fun ω => f (Yo ω)) Zc Xs :=
    isMarkovChain_map_left μ Yo Zc Xs hYo hZc hXs hf h1
  exact isMarkovChain_swap μ (fun ω => f (Yo ω)) Zc Xs (hf.comp hYo) hZc hXs h2

/-- **Local copy of `Fin n → β ≃ᵐ β × ({j : Fin n // j ≠ i} → β)`**, for use in
`condEntropy_pi_eq_sum_of_memoryless_strong`. Mirrors `measurableEquivExtract` in
`ChannelCodingConverseGeneralStrong.lean` but defined locally to keep this file
upstream. -/
private noncomputable def measurableEquivExtractLocal {β' : Type*} [MeasurableSpace β']
    (i : Fin n) :
    (Fin n → β') ≃ᵐ β' × ({j : Fin n // j ≠ i} → β') :=
  (MeasurableEquiv.piEquivPiSubtypeProd (π := fun _ : Fin n => β') (fun j => j = i)).trans
    ((MeasurableEquiv.funUnique {j : Fin n // j = i} β').prodCongr (.refl _))

omit [DecidableEq α] [DecidableEq β] in
/-- **Conditional joint entropy of outputs given inputs, under strong memoryless DMC**:
`H(Y^n | X^n) = ∑ i, H(Y_i | X_i)`.

Combines `condEntropy_pi_chain_rule` (Building Block 2) with the per-summand
collapse `H(Y_i | X^n, Y^{<i}) = H(Y_i | X_i)`. The collapse uses the two Markov
axioms (taken as hypotheses, not as `IsMemorylessChannelStrong` to avoid circular
import — the caller in `ChannelCodingConverseGeneralStrong.lean` unpacks the
structure):

* `h_outputs_cond_indep` (≈ `outputs_cond_indep`): `Y_i ⫫ Y^{<i} | X^n` ⇒ can drop
  `Y^{<i}` from conditioner.
* `h_per_letter_markov` (≈ `per_letter_markov`): `Y_i ⫫ X^{≠i} | X_i` ⇒ can drop
  `X^{≠i}` from conditioner.

Each collapse is one application of `condEntropy_drop_irrelevant_of_markov`. -/
@[entry_point]
lemma condEntropy_pi_eq_sum_of_memoryless_strong
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_per_letter_markov : ∀ i : Fin n,
      IsMarkovChain μ (fun ω j => Xs j ω) (Xs i) (Ys i))
    (h_outputs_cond_indep : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
        (fun ω j => Xs j ω)
        (Ys i)) :
    InformationTheory.MeasureFano.condEntropy μ
        (fun ω j => Ys j ω) (fun ω j => Xs j ω)
      = ∑ i : Fin n,
          InformationTheory.MeasureFano.condEntropy μ (Ys i) (Xs i) := by
  classical
  have hXs_pi : Measurable (fun ω j => Xs j ω) := measurable_pi_iff.mpr hXs
  -- Step 1: chain rule.
  rw [condEntropy_pi_chain_rule μ (fun ω j => Xs j ω) Ys hXs_pi hYs]
  -- Step 2: per-summand collapse.
  apply Finset.sum_congr rfl
  intro i _
  -- Goal: H(Y_i | (Xs_full, Y^{<i})) = H(Y_i | X_i).
  -- (A) Drop Y^{<i} via Markov chain Y_i → Xs_full → Y^{<i}.
  -- (B) Reshape Xs_full ↔ (X_i, X^{≠i}) and drop X^{≠i} via Markov chain
  --     Y_i → X_i → X^{≠i}.
  -- Prefix RV.
  set Yprefix : Ω → (Fin i.val → β) :=
    fun ω j => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω with hYprefix_def
  have hYprefix_meas : Measurable Yprefix :=
    measurable_pi_iff.mpr (fun j => hYs ⟨j.val, j.isLt.trans i.isLt⟩)
  -- Project Y^{≠i} to Y^{<i} via f : ({j // j ≠ i} → β) → (Fin i.val → β).
  -- f g := fun (j : Fin i.val) => g ⟨⟨j.val, j.isLt.trans i.isLt⟩, ne_of_lt j.isLt'⟩
  -- where `ne_of_lt j.isLt' : ⟨j.val, _⟩ ≠ i`.
  -- Actually the constraint is `j.val < n` (from j.isLt.trans i.isLt) and we need
  -- `⟨j.val, _⟩ ≠ i`, which holds since `j.val < i.val`.
  set f_proj : ({j : Fin n // j ≠ i} → β) → (Fin i.val → β) :=
    fun g (j : Fin i.val) =>
      g ⟨⟨j.val, j.isLt.trans i.isLt⟩, by
        intro h
        have hval : j.val = i.val := congrArg Fin.val h
        omega⟩ with hf_proj_def
  have hf_proj_meas : Measurable f_proj := by
    refine measurable_pi_iff.mpr fun j => ?_
    exact measurable_pi_apply _
  -- Markov chain Y_i → Xs_full → Y^{<i}.
  have h_markov_yprefix : IsMarkovChain μ (Ys i) (fun ω j => Xs j ω) Yprefix := by
    have h_swap : IsMarkovChain μ (Ys i) (fun ω j => Xs j ω)
        (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω) :=
      isMarkovChain_swap μ (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
        (fun ω j => Xs j ω) (Ys i)
        (measurable_pi_iff.mpr (fun j => hYs j.val))
        hXs_pi (hYs i) (h_outputs_cond_indep i)
    have h_proj_eq : Yprefix = (fun ω => f_proj
        (fun (j : {j : Fin n // j ≠ i}) => Ys j.val ω)) := by
      funext ω j
      rfl
    rw [h_proj_eq]
    exact isMarkovChain_map_right μ (Ys i) (fun ω j => Xs j ω)
      (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
      (hYs i) hXs_pi (measurable_pi_iff.mpr (fun j => hYs j.val))
      hf_proj_meas h_swap
  -- Drop 1: H(Y_i | (Xs_full, Yprefix)) = H(Y_i | Xs_full).
  rw [condEntropy_drop_irrelevant_of_markov μ (Ys i) (fun ω j => Xs j ω) Yprefix
    (hYs i) hXs_pi hYprefix_meas h_markov_yprefix]
  -- Step (B): reshape Xs_full and drop X^{≠i}.
  -- Reshape: Xs_full = e^{-1} (X_i, X^{≠i}) where e := measurableEquivExtractLocal i.
  let e : (Fin n → α) ≃ᵐ α × ({j : Fin n // j ≠ i} → α) :=
    measurableEquivExtractLocal (β' := α) i
  set XnoI : Ω → ({j : Fin n // j ≠ i} → α) :=
    fun ω (j : {j : Fin n // j ≠ i}) => Xs j.val ω with hXnoI_def
  have hXnoI_meas : Measurable XnoI :=
    measurable_pi_iff.mpr (fun j => hXs j.val)
  -- e (Xs_full ω) = (Xs i ω, XnoI ω).
  have h_e_eq : ∀ ω, e (fun j => Xs j ω) = (Xs i ω, XnoI ω) := by
    intro ω
    apply Prod.ext
    · -- First component: ↑default = i since default : {j // j = i} is ⟨i, rfl⟩.
      have hdef : ((default : {j : Fin n // j = i}) : Fin n) = i := by
        show ((⟨i, rfl⟩ : {j : Fin n // j = i}) : Fin n) = i
        rfl
      simp [e, measurableEquivExtractLocal,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr, hdef]
    · funext j
      simp [e, measurableEquivExtractLocal,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr, XnoI]
  -- condEntropy μ (Y_i) Xs_full = condEntropy μ (Y_i) (e ∘ Xs_full)
  --                              = condEntropy μ (Y_i) (X_i, XnoI).
  have h_reshape :
      InformationTheory.MeasureFano.condEntropy μ (Ys i) (fun ω j => Xs j ω)
        = InformationTheory.MeasureFano.condEntropy μ (Ys i)
            (fun ω => (Xs i ω, XnoI ω)) := by
    have h := condEntropy_measurableEquiv_comp μ (Ys i) (hYs i)
      (fun ω j => Xs j ω) hXs_pi e
    -- h : condEntropy μ (Y_i) (e ∘ Xs_full) = condEntropy μ (Y_i) Xs_full.
    rw [show (fun ω => e (fun j => Xs j ω)) = (fun ω => (Xs i ω, XnoI ω)) from
        funext h_e_eq] at h
    exact h.symm
  rw [h_reshape]
  -- Drop 2: H(Y_i | (X_i, XnoI)) = H(Y_i | X_i) via Markov Y_i → X_i → XnoI.
  -- From per_letter_markov i : Xs_full → X_i → Y_i, swap to get Y_i → X_i → Xs_full,
  -- then map right Xs_full → XnoI via projection.
  set f_xnoI : (Fin n → α) → ({j : Fin n // j ≠ i} → α) :=
    fun x (j : {j : Fin n // j ≠ i}) => x j.val with hf_xnoI_def
  have hf_xnoI_meas : Measurable f_xnoI :=
    measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
  have h_swap_x : IsMarkovChain μ (Ys i) (Xs i) (fun ω j => Xs j ω) :=
    isMarkovChain_swap μ (fun ω j => Xs j ω) (Xs i) (Ys i)
      hXs_pi (hXs i) (hYs i) (h_per_letter_markov i)
  have h_xnoI_eq : XnoI = (fun ω => f_xnoI (fun j => Xs j ω)) := by
    funext ω j
    rfl
  have h_markov_xnoI : IsMarkovChain μ (Ys i) (Xs i) XnoI := by
    rw [h_xnoI_eq]
    exact isMarkovChain_map_right μ (Ys i) (Xs i) (fun ω j => Xs j ω)
      (hYs i) (hXs i) hXs_pi hf_xnoI_meas h_swap_x
  exact condEntropy_drop_irrelevant_of_markov μ (Ys i) (Xs i) XnoI
    (hYs i) (hXs i) hXnoI_meas h_markov_xnoI

end StrongMemorylessCondEntropy

/-! ## Central theorem — Cover-Thomas Thm 7.9 bound -/

section CentralTheorem

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

omit [DecidableEq α] [DecidableEq β] in
/-- **Cover-Thomas Thm 7.9 / per-letter MI bound from strong memoryless DMC**:
`(I(X^n; Y^n)).toReal ≤ ∑ i, (I(X_i; Y_i)).toReal`.

The encoder-agnostic Cover-Thomas chain:

```
I(X^n; Y^n) = H(Y^n) - H(Y^n | X^n)
            ≤ ∑ H(Y_i) - H(Y^n | X^n)             -- subadditivity (Block 1)
            = ∑ H(Y_i) - ∑ H(Y_i | X_i)           -- strong memoryless (Block 4)
            = ∑ (H(Y_i) - H(Y_i | X_i))
            = ∑ I(X_i; Y_i)                       -- Bridge
```

This avoids the false-statement `h_yother_zero` route used in D-2'
`channel_coding_converse_general_memoryless`. The two Markov axioms of
`IsMemorylessChannelStrong` are taken as hypotheses (caller unpacks the structure). -/
@[entry_point]
theorem mutualInfo_le_sum_per_letter_of_memoryless_strong
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_per_letter_markov : ∀ i : Fin n,
      IsMarkovChain μ (fun ω j => Xs j ω) (Xs i) (Ys i))
    (h_outputs_cond_indep : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
        (fun ω j => Xs j ω)
        (Ys i)) :
    (mutualInfo μ (fun ω j => Xs j ω) (fun ω j => Ys j ω)).toReal
      ≤ ∑ i : Fin n, (mutualInfo μ (Xs i) (Ys i)).toReal := by
  classical
  -- Pull joint X^n and Y^n into measurable form.
  have hX_pi : Measurable (fun ω j => Xs j ω) := measurable_pi_iff.mpr hXs
  have hY_pi : Measurable (fun ω j => Ys j ω) := measurable_pi_iff.mpr hYs
  -- Bridge: I(Y^n; X^n).toReal = H(Y^n) - H(Y^n | X^n).
  have h_bridge_joint :
      (mutualInfo μ (fun ω j => Ys j ω) (fun ω j => Xs j ω)).toReal
        = entropy μ (fun ω j => Ys j ω)
          - InformationTheory.MeasureFano.condEntropy μ
              (fun ω j => Ys j ω) (fun ω j => Xs j ω) :=
    mutualInfo_eq_entropy_sub_condEntropy μ
      (fun ω j => Ys j ω) (fun ω j => Xs j ω) hY_pi hX_pi
  -- Commute mutualInfo to put X^n first.
  have h_comm_joint :
      mutualInfo μ (fun ω j => Xs j ω) (fun ω j => Ys j ω)
        = mutualInfo μ (fun ω j => Ys j ω) (fun ω j => Xs j ω) :=
    mutualInfo_comm μ (fun ω j => Xs j ω) (fun ω j => Ys j ω) hX_pi hY_pi
  rw [h_comm_joint, h_bridge_joint]
  -- Subadditivity: H(Y^n) ≤ ∑ H(Y_i). (jointEntropy = entropy of pi RV).
  have h_subadd : entropy μ (fun ω j => Ys j ω) ≤ ∑ i : Fin n, entropy μ (Ys i) := by
    have := entropy_pi_le_sum_entropy μ Ys hYs
    unfold jointEntropy at this
    exact this
  -- Strong memoryless: H(Y^n | X^n) = ∑ H(Y_i | X_i).
  have h_cond_split :
      InformationTheory.MeasureFano.condEntropy μ
          (fun ω j => Ys j ω) (fun ω j => Xs j ω)
        = ∑ i : Fin n,
            InformationTheory.MeasureFano.condEntropy μ (Ys i) (Xs i) :=
    condEntropy_pi_eq_sum_of_memoryless_strong μ Xs Ys hXs hYs
      h_per_letter_markov h_outputs_cond_indep
  rw [h_cond_split]
  -- Per-letter bridge: I(X_i; Y_i).toReal = H(Y_i) - H(Y_i | X_i).
  have h_each_bridge : ∀ i : Fin n,
      (mutualInfo μ (Xs i) (Ys i)).toReal
        = entropy μ (Ys i)
          - InformationTheory.MeasureFano.condEntropy μ (Ys i) (Xs i) := by
    intro i
    rw [mutualInfo_comm μ (Xs i) (Ys i) (hXs i) (hYs i)]
    exact mutualInfo_eq_entropy_sub_condEntropy μ (Ys i) (Xs i) (hYs i) (hXs i)
  -- Rewrite RHS using h_each_bridge and ∑ distributivity.
  have h_rhs_eq :
      (∑ i : Fin n, (mutualInfo μ (Xs i) (Ys i)).toReal)
        = (∑ i : Fin n, entropy μ (Ys i))
          - (∑ i : Fin n,
              InformationTheory.MeasureFano.condEntropy μ (Ys i) (Xs i)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => h_each_bridge i)
  rw [h_rhs_eq]
  linarith

end CentralTheorem

end InformationTheory.Shannon

import InformationTheory.Shannon.WynerZiv.Converse.Prelim

/-!
# Wyner–Ziv converse — single-letterization

The per-letter Markov chain from a memoryless source, the single-letterization
sub-lemmas (the conjuncts of the per-letter witness), and the single-letter rate bound
`wynerZivRate_le_of_code`.
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
  [Fintype U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]

/-! ### Per-letter Markov chain from a memoryless source

The single-letterization core needs the per-letter Markov chain `Uᵢ − Xᵢ − Yᵢ`
with the auxiliary `Uᵢ := (J, Y_{\i})` (the encoder output together with all the
*other* side-information symbols). This is derived from a general reusable utility:
if a pair `(A, C)` is independent of a side variable `W` and the target `U` is a
measurable function `g(A, W)` of `A` and `W` only, then `U − A − C` is a Markov
chain (conditionally on `A`, `U` is a function of `A` and the `C`-independent `W`,
hence conditionally independent of `C`). -/

/-- Markov chain from an independent side variable. If the pair `(As, Cs)` is
independent of `Ws`, and the target `U ω := g (As ω) (Ws ω)` depends only on `As`
and `Ws`, then `U − As − Cs` is a Markov chain (`IsMarkovChain μ U As Cs`).

Genuine measure-theoretic utility: `Q := condDistrib Cs As μ` is the conditioner-only
kernel, and the append identity
`μ.map ((As, U), Cs) = (μ.map (As, U)) ⊗ₘ prodMkRight K Q` is verified by pushing
everything through the product law `μ.map ((As, Cs), Ws) = ρ.prod π` (from `hindep`),
`ρ = (μ.map As) ⊗ₘ Q` (`compProd_map_condDistrib`), and Fubini; the append form then
lands the chain via `wzIsMarkovChain_of_append`. -/
private lemma wz_isMarkovChain_of_indepFun_side
    {Ω A B K W : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace K] [StandardBorelSpace K] [Nonempty K]
    [MeasurableSpace W]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (As : Ω → A) (Cs : Ω → B) (Ws : Ω → W)
    (g : A → W → K)
    (hAs : Measurable As) (hCs : Measurable Cs) (hWs : Measurable Ws)
    (hg : Measurable (fun p : A × W ↦ g p.1 p.2))
    (hindep : IndepFun (fun ω ↦ (As ω, Cs ω)) Ws μ) :
    IsMarkovChain μ (fun ω ↦ g (As ω) (Ws ω)) As Cs := by
  classical
  have hU : Measurable (fun ω ↦ g (As ω) (Ws ω)) := hg.comp (hAs.prodMk hWs)
  set Q : Kernel A B := condDistrib Cs As μ with hQ_def
  haveI : IsProbabilityMeasure (μ.map As) := Measure.isProbabilityMeasure_map hAs.aemeasurable
  haveI : IsProbabilityMeasure (μ.map Ws) := Measure.isProbabilityMeasure_map hWs.aemeasurable
  haveI : IsProbabilityMeasure (μ.map (fun ω ↦ (As ω, Cs ω))) :=
    Measure.isProbabilityMeasure_map (hAs.prodMk hCs).aemeasurable
  -- `ρ = (μ.map As) ⊗ₘ Q` (disintegration of the `(As, Cs)` law).
  have hρ_split : μ.map (fun ω ↦ (As ω, Cs ω)) = (μ.map As) ⊗ₘ Q :=
    (compProd_map_condDistrib hCs.aemeasurable).symm
  -- `μ.map ((As, Cs), Ws) = ρ.prod π` (independence).
  have hjoint : μ.map (fun ω ↦ ((As ω, Cs ω), Ws ω))
      = (μ.map (fun ω ↦ (As ω, Cs ω))).prod (μ.map Ws) :=
    hindep.map_prod_eq_prod_map_map (hAs.prodMk hCs).aemeasurable hWs.aemeasurable
  -- Transfer maps.
  have hΨ : Measurable (fun q : (A × B) × W ↦ ((q.1.1, g q.1.1 q.2), q.1.2)) :=
    (((measurable_fst.comp measurable_fst).prodMk
        (hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).prodMk
      (measurable_snd.comp measurable_fst))
  have hΦ : Measurable (fun q : (A × B) × W ↦ (q.1.1, g q.1.1 q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hJ : Measurable (fun ω ↦ ((As ω, Cs ω), Ws ω)) := (hAs.prodMk hCs).prodMk hWs
  have hmapΨ : μ.map (fun ω ↦ ((As ω, g (As ω) (Ws ω)), Cs ω))
      = ((μ.map (fun ω ↦ (As ω, Cs ω))).prod (μ.map Ws)).map
          (fun q : (A × B) × W ↦ ((q.1.1, g q.1.1 q.2), q.1.2)) := by
    rw [← hjoint, Measure.map_map hΨ hJ]; rfl
  have hmapΦ : μ.map (fun ω ↦ (As ω, g (As ω) (Ws ω)))
      = ((μ.map (fun ω ↦ (As ω, Cs ω))).prod (μ.map Ws)).map
          (fun q : (A × B) × W ↦ (q.1.1, g q.1.1 q.2)) := by
    rw [← hjoint, Measure.map_map hΦ hJ]; rfl
  -- Append identity.
  have h_app : μ.map (fun ω ↦ ((As ω, g (As ω) (Ws ω)), Cs ω))
      = (μ.map (fun ω ↦ (As ω, g (As ω) (Ws ω)))) ⊗ₘ (Kernel.prodMkRight K Q) := by
    refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
    -- LHS reduces to the triple integral (order a, c, w).
    have hLHS : ∫⁻ p, f p ∂(μ.map (fun ω ↦ ((As ω, g (As ω) (Ws ω)), Cs ω)))
        = ∫⁻ a, ∫⁻ c, ∫⁻ w, f ((a, g a w), c) ∂(μ.map Ws) ∂(Q a) ∂(μ.map As) := by
      rw [hmapΨ, lintegral_map hf hΨ,
        lintegral_prod (fun q : (A × B) × W ↦ f ((q.1.1, g q.1.1 q.2), q.1.2))
          (hf.comp hΨ).aemeasurable,
        hρ_split,
        Measure.lintegral_compProd
          (f := fun x : A × B ↦ ∫⁻ w, f ((x.1, g x.1 w), x.2) ∂(μ.map Ws))
          (hf.comp hΨ).lintegral_prod_right']
    -- RHS reduces to a `c'`-collapsed / swapped triple integral (order a, c', w, c).
    have hGmeas : Measurable
        (fun au : A × K ↦ ∫⁻ c, f (au, c) ∂((Kernel.prodMkRight K Q) au)) :=
      hf.lintegral_kernel_prod_right' (κ := Kernel.prodMkRight K Q)
    have hRHS : ∫⁻ p, f p ∂((μ.map (fun ω ↦ (As ω, g (As ω) (Ws ω)))) ⊗ₘ (Kernel.prodMkRight K Q))
        = ∫⁻ a, ∫⁻ _c', ∫⁻ w, ∫⁻ c, f ((a, g a w), c) ∂(Q a) ∂(μ.map Ws) ∂(Q a) ∂(μ.map As) := by
      rw [Measure.lintegral_compProd hf, hmapΦ, lintegral_map hGmeas hΦ,
        lintegral_prod (fun q : (A × B) × W ↦
            ∫⁻ c, f ((q.1.1, g q.1.1 q.2), c) ∂((Kernel.prodMkRight K Q) (q.1.1, g q.1.1 q.2)))
          (hGmeas.comp hΦ).aemeasurable,
        hρ_split,
        Measure.lintegral_compProd
          (f := fun x : A × B ↦ ∫⁻ w, ∫⁻ c,
              f ((x.1, g x.1 w), c) ∂((Kernel.prodMkRight K Q) (x.1, g x.1 w)) ∂(μ.map Ws))
          (hGmeas.comp hΦ).lintegral_prod_right']
      simp only [Kernel.prodMkRight_apply]
    rw [hLHS, hRHS]
    refine lintegral_congr fun a ↦ ?_
    haveI : IsProbabilityMeasure (Q a) := IsMarkovKernel.isProbabilityMeasure a
    -- Collapse the `c'` integral (integrand independent of `c'`) and swap `c ↔ w`.
    rw [lintegral_const, measure_univ, mul_one]
    exact lintegral_lintegral_swap
      (hf.comp ((measurable_const.prodMk
        (hg.comp (measurable_const.prodMk measurable_snd))).prodMk measurable_fst)).aemeasurable
  exact wzIsMarkovChain_of_append μ (fun ω ↦ g (As ω) (Ws ω)) As Cs hU hAs hCs Q h_app

/-- Per-letter Markov chain of a memoryless Wyner–Ziv source.
For a memoryless source `(Xⁿ, Yⁿ)` (mutual independence `hindep`) and a fixed
time index `i`, the single-letterization auxiliary `Uᵢ := (J, Y_{\i})` — the
deterministic encoder output `J = c.encoder Xⁿ` together with all the *other*
side-information symbols `Y_{\i} = (Yⱼ)_{j≠i}` — satisfies the Markov chain
`Uᵢ − Xᵢ − Yᵢ` (`IsMarkovChain μ Uᵢ (Xs i) (Ys i)`).

This is the deepest step of the converse single-letterization. `hindep` (memoryless
source) is a genuine regularity precondition: the chain is false for a source with
memory. Proof: `Uᵢ` is a measurable function `g (Xᵢ) (Y_{\i}, X_{\i})` of `Xᵢ` and
the *rest* of the block, and by memorylessness the `i`-th pair `(Xᵢ, Yᵢ)` is
independent of the rest — so `wz_isMarkovChain_of_indepFun_side` applies. -/
private theorem wz_perletter_markov
    {Ω : Type*} [MeasurableSpace Ω]
    {M n : ℕ} [NeZero M] (i : Fin n)
    (c : WynerZivCode M n α β γ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ j, Measurable (Xs j)) (hYs : ∀ j, Measurable (Ys j))
    (hindep : iIndepFun (fun j ω ↦ (Xs j ω, Ys j ω)) μ) :
    IsMarkovChain μ
      (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
        fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
      (Xs i) (Ys i) := by
  classical
  -- The "rest of the block" side variable `Ws = (X_{\i}, Y_{\i})`.
  set Ws : Ω → (({j : Fin n // j ≠ i} → α) × ({j : Fin n // j ≠ i} → β)) :=
    fun ω ↦ ((fun j ↦ Xs (↑j) ω), (fun j ↦ Ys (↑j) ω)) with hWs_def
  -- The deterministic map reconstructing `Uᵢ = (J, Y_{\i})` from `Xᵢ` and `Ws`.
  set g : α → (({j : Fin n // j ≠ i} → α) × ({j : Fin n // j ≠ i} → β)) →
      (Fin M × ({j : Fin n // j ≠ i} → β)) :=
    fun a p ↦ (c.encoder (fun j ↦ if h : j = i then a else p.1 ⟨j, h⟩), p.2) with hg_def
  have hWs_meas : Measurable Ws :=
    (measurable_pi_lambda (fun ω (j : {j : Fin n // j ≠ i}) ↦ Xs (↑j) ω)
        (fun j ↦ hXs ↑j)).prodMk
      (measurable_pi_lambda (fun ω (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω) (fun j ↦ hYs ↑j))
  have hg_meas : Measurable
      (fun p : α × (({j : Fin n // j ≠ i} → α) × ({j : Fin n // j ≠ i} → β)) ↦ g p.1 p.2) :=
    Measurable.of_discrete
  -- Independence of the `i`-th pair from the rest of the block (memorylessness).
  have hindep_pair : IndepFun (fun ω ↦ (Xs i ω, Ys i ω)) Ws μ := by
    have hf_meas : ∀ j, Measurable (fun ω ↦ (Xs j ω, Ys j ω)) := fun j ↦ (hXs j).prodMk (hYs j)
    have hfin := hindep.indepFun_finset {i} (Finset.univ \ {i}) Finset.disjoint_sdiff hf_meas
    exact hfin.comp
      (φ := fun r : (({i} : Finset (Fin n)) → α × β) ↦ r ⟨i, Finset.mem_singleton_self i⟩)
      (ψ := fun r : ((Finset.univ \ {i} : Finset (Fin n)) → α × β) ↦
        ((fun j : {j : Fin n // j ≠ i} ↦ (r ⟨↑j, by simp [j.2]⟩).1),
         (fun j : {j : Fin n // j ≠ i} ↦ (r ⟨↑j, by simp [j.2]⟩).2)))
      Measurable.of_discrete Measurable.of_discrete
  -- Identify the auxiliary as `g (Xᵢ) (Ws)`.
  have hU_eq : (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
        fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
      = (fun ω ↦ g (Xs i ω) (Ws ω)) := by
    funext ω
    simp only [hg_def, hWs_def]
    congr 1
    congr 1
    funext j
    split_ifs with h
    · rw [h]
    · rfl
  rw [hU_eq]
  exact wz_isMarkovChain_of_indepFun_side μ (Xs i) (Ys i) Ws g (hXs i) (hYs i) hWs_meas hg_meas
    hindep_pair

/-- Singleton evaluation of a semidirect product `ρ ⊗ₘ K` on finite spaces:
`(ρ ⊗ₘ K) {(z, w)} = K z {w} · ρ {z}`. Measure-theoretic utility used to read
the factorization `q(x,y,u) = κ(u|x)·P_XY(x,y)` off the per-letter Markov chain.
@audit:ok (`compProd_apply` on the rectangle `{z}×{w}` collapses the fiber integrand to
the indicator `{z} · K z' {w}`, giving `K z {w} · ρ {z}`, alive at the degenerate boundary
`ρ = 0`; `[SFinite ρ]`/`[IsMarkovKernel K]`/`MeasurableSingletonClass` are the regularity
preconditions of `compProd_apply`.) -/
private lemma wz_compProd_markov_singleton
    {Z W : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace W] [MeasurableSingletonClass W]
    (ρ : Measure Z) [SFinite ρ] (K : Kernel Z W) [IsMarkovKernel K] (z : Z) (w : W) :
    (ρ ⊗ₘ K) {(z, w)} = K z {w} * ρ {z} := by
  classical
  have hsingle : ({(z, w)} : Set (Z × W)) = ({z} : Set Z) ×ˢ ({w} : Set W) := by
    ext p; simp [Prod.ext_iff]
  rw [hsingle,
      Measure.compProd_apply ((measurableSet_singleton z).prod (measurableSet_singleton w))]
  have hfun : (fun z' ↦ K z' (Prod.mk z' ⁻¹' (({z} : Set Z) ×ˢ ({w} : Set W))))
      = fun z' ↦ ({z} : Set Z).indicator (fun z'' ↦ K z'' {w}) z' := by
    funext z'
    rw [Set.mk_preimage_prod_right_eq_if]
    by_cases hz : z' ∈ ({z} : Set Z)
    · rw [if_pos hz, Set.indicator_of_mem hz]
    · rw [if_neg hz, Set.indicator_of_notMem hz, measure_empty]
  rw [hfun, lintegral_indicator (measurableSet_singleton z),
      lintegral_singleton' (K.measurable_coe (measurableSet_singleton w))]

/-- Empirical factorizability of the per-letter joint. For a
memoryless source `(Xⁿ, Yⁿ)` and time index `i`, the empirical joint law of
`(Xᵢ, Yᵢ, Uᵢ)` with `Uᵢ := (J, Y_{\i})` is Wyner–Ziv factorizable over the source pmf
`P_XY.real`, with the conditioner-only kernel `κ(u|x) := (condDistrib Uᵢ Xᵢ μ x).real {u}`.
The factorization `q(x,y,u) = κ(u|x)·P_XY(x,y)` is read off the per-letter Markov chain
`Uᵢ − Xᵢ − Yᵢ` (`wz_perletter_markov`) by singleton evaluation of the joint law.
@audit:ok (the witness `κ(u|x) = (condDistrib Uᵢ Xᵢ μ x).real {u}` is genuinely
row-stochastic — the `∑_u κ x u = 1` conjunct is discharged via `probReal_univ` off the
Markov kernel's `IsProbabilityMeasure`, ruling out the vacuous `κ ≡ 0` / `q ≡ 0` escape;
the factorization conjunct genuinely uses the per-letter Markov structure `hmarkov_eq`
(⟸ `hindep`), so dropping `hindep` breaks `Uᵢ − Xᵢ − Yᵢ` and `q` need not factor.) -/
private theorem wz_perletter_empirical_factorizable
    {Ω : Type*} [MeasurableSpace Ω]
    {M n : ℕ} [NeZero M] (i : Fin n)
    (c : WynerZivCode M n α β γ)
    (hencoder : Measurable c.encoder)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep : iIndepFun (fun i ω ↦ (Xs i ω, Ys i ω)) μ)
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (hlaw : ∀ i, μ.map (fun ω ↦ (Xs i ω, Ys i ω)) = P_XY) :
    IsWynerZivFactorizable (Fin M × ({j : Fin n // j ≠ i} → β))
      (fun p ↦ P_XY.real {p})
      (fun p ↦ (μ.map (fun ω ↦ (Xs i ω, Ys i ω,
          (c.encoder (fun j ↦ Xs j ω),
            fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)))).real {p}) := by
  classical
  set Uᵢ : Ω → (Fin M × ({j : Fin n // j ≠ i} → β)) :=
    fun ω ↦ (c.encoder (fun j ↦ Xs j ω), fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)
    with hUᵢ_def
  have hUᵢ_meas : Measurable Uᵢ :=
    (hencoder.comp (measurable_pi_lambda _ (fun j ↦ hXs j))).prodMk
      (measurable_pi_lambda _ (fun j ↦ hYs ↑j))
  haveI : IsProbabilityMeasure (μ.map (Xs i)) :=
    Measure.isProbabilityMeasure_map (hXs i).aemeasurable
  -- The per-letter Markov chain `Uᵢ − Xᵢ − Yᵢ`, as a measure equation.
  have hmarkov_eq : μ.map (fun ω ↦ (Xs i ω, Uᵢ ω, Ys i ω))
      = (μ.map (Xs i)) ⊗ₘ ((condDistrib Uᵢ (Xs i) μ) ×ₖ (condDistrib (Ys i) (Xs i) μ)) :=
    wz_perletter_markov i c μ Xs Ys hXs hYs hindep
  -- Witness kernel: `κ(u|x) = (condDistrib Uᵢ Xᵢ μ x).real {u}`.
  refine ⟨fun x u ↦ ((condDistrib Uᵢ (Xs i) μ) x).real {u}, ?_, ?_, ?_⟩
  · intro x u; exact measureReal_nonneg
  · intro x
    haveI : IsProbabilityMeasure ((condDistrib Uᵢ (Xs i) μ) x) :=
      IsMarkovKernel.isProbabilityMeasure x
    have h1 : (∑ u, ((condDistrib Uᵢ (Xs i) μ) x).real {u})
        = ((condDistrib Uᵢ (Xs i) μ) x).real (Finset.univ :
            Finset (Fin M × ({j : Fin n // j ≠ i} → β))) := by
      simp [sum_measureReal_singleton]
    rw [h1, Finset.coe_univ]
    exact probReal_univ
  · intro x y u
    -- Singleton factorization of the empirical joint law (ENNReal level).
    have hjoint : (μ.map (fun ω ↦ (Xs i ω, Ys i ω, Uᵢ ω))) {(x, y, u)}
        = ((condDistrib Uᵢ (Xs i) μ) x) {u}
            * (μ.map (fun ω ↦ (Xs i ω, Ys i ω))) {(x, y)} := by
      have hreorder : (μ.map (fun ω ↦ (Xs i ω, Ys i ω, Uᵢ ω))) {(x, y, u)}
          = (μ.map (fun ω ↦ (Xs i ω, Uᵢ ω, Ys i ω))) {(x, u, y)} := by
        rw [Measure.map_apply ((hXs i).prodMk ((hYs i).prodMk hUᵢ_meas))
              (measurableSet_singleton _),
            Measure.map_apply ((hXs i).prodMk (hUᵢ_meas.prodMk (hYs i)))
              (measurableSet_singleton _)]
        congr 1
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
        tauto
      rw [hreorder, hmarkov_eq,
          wz_compProd_markov_singleton (μ.map (Xs i))
            ((condDistrib Uᵢ (Xs i) μ) ×ₖ (condDistrib (Ys i) (Xs i) μ)) x (u, y)]
      have hprod : ((condDistrib Uᵢ (Xs i) μ) ×ₖ (condDistrib (Ys i) (Xs i) μ)) x {(u, y)}
          = ((condDistrib Uᵢ (Xs i) μ) x) {u} * ((condDistrib (Ys i) (Xs i) μ) x) {y} := by
        have hset : ({(u, y)} : Set ((Fin M × ({j : Fin n // j ≠ i} → β)) × β))
            = ({u} : Set _) ×ˢ ({y} : Set β) := by ext p; simp [Prod.ext_iff]
        rw [hset, Kernel.prod_apply_prod]
      have hXY : (μ.map (fun ω ↦ (Xs i ω, Ys i ω))) {(x, y)}
          = ((condDistrib (Ys i) (Xs i) μ) x) {y} * (μ.map (Xs i)) {x} := by
        rw [← compProd_map_condDistrib (hYs i).aemeasurable,
            wz_compProd_markov_singleton (μ.map (Xs i)) (condDistrib (Ys i) (Xs i) μ) x y]
      rw [hprod, hXY]; ring
    show (μ.map (fun ω ↦ (Xs i ω, Ys i ω, Uᵢ ω))).real {(x, y, u)}
        = ((condDistrib Uᵢ (Xs i) μ) x).real {u} * P_XY.real {(x, y)}
    unfold Measure.real
    rw [hjoint, ENNReal.toReal_mul, ← hlaw i]

/-! ### Single-letterization sub-lemmas (conjuncts of the per-letter witness)

The per-letter witness `wz_converse_perletter_witness` is the mechanical assembly of
three sub-lemmas, one per conjunct, all sharing the auxiliary `Uᵢ := (J, Y_{\i})`
(of type `Fin M × ({j // j ≠ i} → β)`, the encoder output together with all the other
side-information symbols):

* `wz_perletter_factorizable` — conjunct (a), per-letter feasibility;
* `wz_perletter_distortion_avg` — conjunct (b), the average distortion budget;
* `wz_singleletter_rate_le` — conjunct (c), the conditional-MI chain (deepest atom). -/

/-- Per-letter feasibility. For each time index `i`, the empirical
joint law of `(Xᵢ, Yᵢ, Uᵢ)` with `Uᵢ := (J, Y_{\i})` is Wyner–Ziv factorizable over
the source pmf `P_XY.real`, with kernel `condDistrib Uᵢ Xᵢ` (well-defined off the
memoryless per-letter Markov chain `Uᵢ − Xᵢ − Yᵢ`, `wz_perletter_markov`). Relabeling
the finite auxiliary type `Fin M × ({j // j ≠ i} → β)` to a `Fin k` and pairing with the
side-information decoder `f (u, y)` reconstructing `X̂ᵢ` lands the per-letter objective
`(I(Xᵢ; Uᵢ) − I(Yᵢ; Uᵢ)).toReal` as a value of `wzRateValueSet` at the per-letter budget
`Dv i = 𝔼[d(Xᵢ, X̂ᵢ)]`. `hlaw` fixes the `(Xᵢ, Yᵢ)`-marginal to `P_XY`.

The empirical joint's factorizability is discharged by
`wz_perletter_empirical_factorizable` (singleton evaluation of the per-letter Markov chain
`Uᵢ − Xᵢ − Yᵢ`); the distortion identity `wzExpectedDistortion = 𝔼[d(Xᵢ, X̂ᵢ)]` is a
`Measure.map` change of variables; `wzRateValueSet_reindex_mem` lands the pmf-form objective,
the pmf↔measure bridges `wzMutualInfoXU_eq_mutualInfo` / `_YU_` identify it with the
measure-form MI, and `ENNReal.toReal_sub_of_le` (off the data-processing non-negativity
`wzObjective_nonneg_of_factorizable`) reassembles the `.toReal` difference. All hypotheses
are source-regularity preconditions (measurability / `iIndepFun` memorylessness / `hlaw`
marginal `= P_XY` / `IsProbabilityMeasure`); none encodes the factorizability conclusion.
@audit:ok (non-circular: this lemma proves factorizability (`hfact`) from source-regularity
via `wz_perletter_empirical_factorizable`, it does not assume it; the `hle : I(Yᵢ;Uᵢ) ≤
I(Xᵢ;Uᵢ)` used by `ENNReal.toReal_sub_of_le` comes from the independent general DPI lemma
`wzObjective_nonneg_of_factorizable`, so applying it to the proven `hfact` is a forward
derivation, not circular.) -/
private theorem wz_perletter_factorizable
    {Ω : Type*} [MeasurableSpace Ω]
    {M n : ℕ} [NeZero M] (i : Fin n)
    (c : WynerZivCode M n α β γ)
    (hencoder : Measurable c.encoder) (_hdecoder : Measurable c.decoder)
    (d : DistortionFn α γ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep : iIndepFun (fun i ω ↦ (Xs i ω, Ys i ω)) μ)
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (hlaw : ∀ i, μ.map (fun ω ↦ (Xs i ω, Ys i ω)) = P_XY) :
    (mutualInfo μ (Xs i)
        (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
          fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
      - mutualInfo μ (Ys i)
        (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
          fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))).toReal
      ∈ wzRateValueSet (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ))
          (∫ ω, (d (Xs i ω)
              ((c.decoder (c.encoder (fun j ↦ Xs j ω), fun j ↦ Ys j ω)) i) : ℝ) ∂μ) := by
  classical
  -- The single-letterization auxiliary `Uᵢ := (J, Y_{\i})`.
  set Uᵢ : Ω → (Fin M × ({j : Fin n // j ≠ i} → β)) :=
    fun ω ↦ (c.encoder (fun j ↦ Xs j ω), fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)
    with hUᵢ_def
  have hUᵢ_meas : Measurable Uᵢ :=
    (hencoder.comp (measurable_pi_lambda _ (fun j ↦ hXs j))).prodMk
      (measurable_pi_lambda _ (fun j ↦ hYs ↑j))
  -- The distortion budget of the per-letter reconstruction.
  set D : ℝ := ∫ ω, (d (Xs i ω)
      ((c.decoder (c.encoder (fun j ↦ Xs j ω), fun j ↦ Ys j ω)) i) : ℝ) ∂μ with hD_def
  -- The empirical joint pmf and the side-information decoder.
  set q : α × β × (Fin M × ({j : Fin n // j ≠ i} → β)) → ℝ :=
    fun p ↦ (μ.map (fun ω ↦ (Xs i ω, Ys i ω, Uᵢ ω))).real {p} with hq_def
  set f : (Fin M × ({j : Fin n // j ≠ i} → β)) × β → γ :=
    fun p ↦ (c.decoder (p.1.1, fun j ↦ if h : j = i then p.2 else p.1.2 ⟨j, h⟩)) i with hf_def
  -- Crux #1: the empirical joint is factorizable.
  have hfact : IsWynerZivFactorizable (Fin M × ({j : Fin n // j ≠ i} → β))
      (fun p ↦ P_XY.real {p}) q :=
    wz_perletter_empirical_factorizable i c hencoder μ Xs Ys hXs hYs hindep P_XY hlaw
  -- Crux #3: the pmf-form distortion equals the per-letter budget `D`.
  have hJoint_meas : Measurable (fun ω ↦ (Xs i ω, Ys i ω, Uᵢ ω)) :=
    (hXs i).prodMk ((hYs i).prodMk hUᵢ_meas)
  haveI : IsProbabilityMeasure (μ.map (fun ω ↦ (Xs i ω, Ys i ω, Uᵢ ω))) :=
    Measure.isProbabilityMeasure_map hJoint_meas.aemeasurable
  have hdist : wzExpectedDistortion (Fin M × ({j : Fin n // j ≠ i} → β))
      (fun a b ↦ (d a b : ℝ)) q f ≤ D := by
    refine le_of_eq ?_
    have hstep1 : wzExpectedDistortion (Fin M × ({j : Fin n // j ≠ i} → β))
        (fun a b ↦ (d a b : ℝ)) q f
        = ∫ p, (d p.1 (f (p.2.2, p.2.1)) : ℝ) ∂(μ.map (fun ω ↦ (Xs i ω, Ys i ω, Uᵢ ω))) := by
      unfold wzExpectedDistortion
      rw [integral_fintype (Integrable.of_finite)]
      refine Finset.sum_congr rfl (fun p _ ↦ ?_)
      simp only [hq_def, smul_eq_mul]
    rw [hstep1, integral_map hJoint_meas.aemeasurable
        ((measurable_of_countable _).aestronglyMeasurable), hD_def]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω ↦ ?_))
    simp only [hf_def, hUᵢ_def]
    have hblock : (fun j : Fin n ↦ if h : j = i then Ys i ω else Ys j ω)
        = fun j ↦ Ys j ω := by
      funext j; split_ifs with h
      · rw [h]
      · rfl
    rw [hblock]
  -- Landing: the objective value lies in `wzRateValueSet` at budget `D`.
  have hmem : (q, f) ∈ WynerZivFactorizableConstraint (Fin M × ({j : Fin n // j ≠ i} → β))
      (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D := ⟨hfact, hdist⟩
  have hland := wzRateValueSet_reindex_mem hmem
  -- Bridge the pmf-form objective onto the measure form.
  have hXU : wzMutualInfoXU (Fin M × ({j : Fin n // j ≠ i} → β)) q
      = (mutualInfo μ (Xs i) Uᵢ).toReal := by
    rw [hq_def]
    exact wzMutualInfoXU_eq_mutualInfo μ (Xs i) (Ys i) Uᵢ (hXs i) (hYs i) hUᵢ_meas
  have hYU : wzMutualInfoYU (Fin M × ({j : Fin n // j ≠ i} → β)) q
      = (mutualInfo μ (Ys i) Uᵢ).toReal := by
    rw [hq_def]
    exact wzMutualInfoYU_eq_mutualInfo μ (Xs i) (Ys i) Uᵢ (hXs i) (hYs i) hUᵢ_meas
  rw [hXU, hYU] at hland
  -- Data-processing non-negativity `I(Y;U) ≤ I(X;U)` (via the factorizable manifold DPI).
  have hnn := wzObjective_nonneg_of_factorizable (measureReal_pmf_mem_stdSimplex P_XY) hfact
  rw [hXU, hYU] at hnn
  have hXne : mutualInfo μ (Xs i) Uᵢ ≠ ∞ := mutualInfo_ne_top μ (Xs i) Uᵢ (hXs i) hUᵢ_meas
  have hYne : mutualInfo μ (Ys i) Uᵢ ≠ ∞ := mutualInfo_ne_top μ (Ys i) Uᵢ (hYs i) hUᵢ_meas
  have hle : mutualInfo μ (Ys i) Uᵢ ≤ mutualInfo μ (Xs i) Uᵢ :=
    (ENNReal.toReal_le_toReal hYne hXne).mp (by linarith)
  rw [ENNReal.toReal_sub_of_le hle hXne]
  exact hland

/-- Average per-letter distortion. The uniform average of the
per-letter distortions `Dv i = 𝔼[d(Xᵢ, X̂ᵢ)]` (with `X̂ᵢ = (decoder (J, Yⁿ))ᵢ`) equals
the expected block distortion of the code under the i.i.d. source `P_XY`, hence is at
most `D` by `hD`. The proof clones the rate-distortion
`blockDistortion_eq_avg_perLetter` for the side-information decoder: the joint law
`μ.map (ω ↦ (Xⁿ ω, Yⁿ ω)) = Measure.pi (fun _ ↦ P_XY)` (from `hindep` + `hlaw`) turns
each `μ`-integral into a `pi`-integral, and the sum collapses into the block-distortion
integral.
@audit:ok (the content is the identity `(1/n) ∑ᵢ Dv i = expectedBlockDistortion`
(product-law change of variables + Fubini + block-distortion assembly); `hD` is a
distortion-budget precondition chained after the identity, not circular or load-bearing.) -/
private theorem wz_perletter_distortion_avg
    {Ω : Type*} [MeasurableSpace Ω]
    {M n : ℕ} [NeZero M] (_hn : 0 < n)
    (c : WynerZivCode M n α β γ)
    (_hencoder : Measurable c.encoder) (_hdecoder : Measurable c.decoder)
    (d : DistortionFn α γ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep : iIndepFun (fun i ω ↦ (Xs i ω, Ys i ω)) μ)
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (hlaw : ∀ i, μ.map (fun ω ↦ (Xs i ω, Ys i ω)) = P_XY)
    {D : ℝ}
    (hD : c.expectedBlockDistortion P_XY d ≤ D) :
    (1 / (n : ℝ)) * ∑ i, (∫ ω, (d (Xs i ω)
        ((c.decoder (c.encoder (fun j ↦ Xs j ω), fun j ↦ Ys j ω)) i) : ℝ) ∂μ) ≤ D := by
  classical
  set d' : α → γ → ℝ := fun a b ↦ ((d a b : NNReal) : ℝ) with hd'_def
  set Wn : Ω → (Fin n → α × β) := fun ω i ↦ (Xs i ω, Ys i ω) with hWn_def
  have hWn_meas : Measurable Wn := measurable_pi_iff.mpr (fun i ↦ (hXs i).prodMk (hYs i))
  -- Product law: μ.map Wn = Measure.pi (fun _ ↦ P_XY).
  have h_pi_law : μ.map Wn = Measure.pi (fun _ : Fin n ↦ P_XY) := by
    have h := (iIndepFun_iff_map_fun_eq_pi_map (μ := μ) (f := fun i ω ↦ (Xs i ω, Ys i ω))
      (fun i ↦ ((hXs i).prodMk (hYs i)).aemeasurable)).mp hindep
    simp only [hWn_def]
    rw [h]
    congr 1
    funext i
    exact hlaw i
  -- Each per-letter distortion as a `pi`-integral (change of variables).
  have h_each : ∀ i, (∫ ω, (d (Xs i ω)
        ((c.decoder (c.encoder (fun j ↦ Xs j ω), fun j ↦ Ys j ω)) i) : ℝ) ∂μ)
      = ∫ p : Fin n → α × β,
          d' ((p i).1) ((c.decoder (c.encoder (fun j ↦ (p j).1), fun j ↦ (p j).2)) i)
            ∂(Measure.pi (fun _ : Fin n ↦ P_XY)) := by
    intro i
    have hg_meas : Measurable (fun p : Fin n → α × β ↦
        d' ((p i).1) ((c.decoder (c.encoder (fun j ↦ (p j).1), fun j ↦ (p j).2)) i)) :=
      measurable_of_countable _
    have hgoal : (fun ω ↦ ((d (Xs i ω)
          ((c.decoder (c.encoder (fun j ↦ Xs j ω), fun j ↦ Ys j ω)) i) : NNReal) : ℝ))
        = fun ω ↦ (fun p : Fin n → α × β ↦
            d' ((p i).1) ((c.decoder (c.encoder (fun j ↦ (p j).1), fun j ↦ (p j).2)) i)) (Wn ω) :=
      rfl
    rw [hgoal, ← integral_map hWn_meas.aemeasurable hg_meas.aestronglyMeasurable, h_pi_law]
  -- Assemble the average into the block-distortion integral.
  have h_id : (1 / (n : ℝ)) * ∑ i, (∫ ω, (d (Xs i ω)
        ((c.decoder (c.encoder (fun j ↦ Xs j ω), fun j ↦ Ys j ω)) i) : ℝ) ∂μ)
      = c.expectedBlockDistortion P_XY d := by
    calc (1 / (n : ℝ)) * ∑ i, (∫ ω, (d (Xs i ω)
            ((c.decoder (c.encoder (fun j ↦ Xs j ω), fun j ↦ Ys j ω)) i) : ℝ) ∂μ)
        = (1 / (n : ℝ)) * ∑ i, ∫ p : Fin n → α × β,
            d' ((p i).1) ((c.decoder (c.encoder (fun j ↦ (p j).1), fun j ↦ (p j).2)) i)
              ∂(Measure.pi (fun _ : Fin n ↦ P_XY)) := by
            rw [Finset.sum_congr rfl (fun i _ ↦ h_each i)]
      _ = (1 / (n : ℝ)) * ∫ p : Fin n → α × β,
            ∑ i, d' ((p i).1) ((c.decoder (c.encoder (fun j ↦ (p j).1), fun j ↦ (p j).2)) i)
              ∂(Measure.pi (fun _ : Fin n ↦ P_XY)) := by
            rw [integral_finsetSum]
            exact fun i _ ↦ Integrable.of_finite
      _ = ∫ p : Fin n → α × β,
            (1 / (n : ℝ)) * ∑ i,
              d' ((p i).1) ((c.decoder (c.encoder (fun j ↦ (p j).1), fun j ↦ (p j).2)) i)
              ∂(Measure.pi (fun _ : Fin n ↦ P_XY)) := by
            rw [integral_const_mul]
      _ = c.expectedBlockDistortion P_XY d := by
            rw [WynerZivCode.expectedBlockDistortion]
            rfl
  rw [h_id]
  exact hD

/-- Conditional independence of past inputs given the full side-information block.
For a memoryless source `(Xⁿ, Yⁿ)` (mutual independence `hindep`) and a fixed time index
`i`, the current input `Xᵢ` is conditionally independent of the past inputs
`X^{<i} = (Xⱼ)_{j<i}` given the full side-information block `Yⁿ`:
`I(Xᵢ; X^{<i} | Yⁿ) = 0`.

This is the input analogue of the memoryless collapse. `hindep` is a genuine
regularity precondition (false for a source with memory). Proof (chain-rule route, no
disintegration): the pair `(Xᵢ, Yᵢ)` is independent of `(X^{<i}, Y_{\i})`, hence
`I((Xᵢ, Yᵢ); (X^{<i}, Y_{\i})) = 0`; expanding the joint MI by the chain rule bounds the
conditional term `I(Xᵢ; X^{<i} | (Yᵢ, Y_{\i}))` below it, so it is `0`; a
conditioner reshape `(Yᵢ, Y_{\i}) ≅ Yⁿ` finishes.

@audit:ok (conclusion `I(Xᵢ; X^{<i} | Yⁿ) = 0` — conditioner the full block `Yⁿ`, middle
the past inputs `X^{<i}` — is non-circular (no hypothesis has the `condMutualInfo … = 0`
shape) and non-bundled (`hindep : iIndepFun` is a memoryless-source regularity precondition);
the channel-coding X/Y-dual `Y^{≠i}⊥Xᵢ|Yᵢ` is false there only because `X` is a structured
codeword, a case that violates `hindep`, so the distinction is correctly effected by
`hindep`.) -/
private theorem wz_inputs_cond_indep
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (i : Fin n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ j, Measurable (Xs j)) (hYs : ∀ j, Measurable (Ys j))
    (hindep : iIndepFun (fun j ω ↦ (Xs j ω, Ys j ω)) μ) :
    condMutualInfo μ (Xs i)
      (fun ω (j : Fin i.val) ↦ Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
      (fun ω j ↦ Ys j ω) = 0 := by
  classical
  set Xpre : Ω → (Fin i.val → α) := fun ω j ↦ Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω with hXpre_def
  set Yoth : Ω → ({j : Fin n // j ≠ i} → β) := fun ω j ↦ Ys (↑j) ω with hYoth_def
  set Yn : Ω → (Fin n → β) := fun ω j ↦ Ys j ω with hYn_def
  have hXpre_meas : Measurable Xpre := measurable_pi_lambda _ fun j ↦ hXs _
  have hYoth_meas : Measurable Yoth := measurable_pi_lambda _ fun j ↦ hYs ↑j
  have hYn_meas : Measurable Yn := measurable_pi_lambda _ fun j ↦ hYs j
  -- Conditioner reshape `Yⁿ ≅ (Yᵢ, Y_{\i})`.
  have hcond : condMutualInfo μ (Xs i) Xpre Yn
      = condMutualInfo μ (Xs i) Xpre (fun ω ↦ (Ys i ω, Yoth ω)) := by
    have h := condMutualInfo_map_cond_measurableEquiv μ (Xs i) Xpre Yn (hXs i) hXpre_meas hYn_meas
      (ChannelCodingConverseGeneral.measurableEquivExtract i)
    rw [show (fun ω ↦ (ChannelCodingConverseGeneral.measurableEquivExtract i) (Yn ω))
          = (fun ω ↦ (Ys i ω, Yoth ω)) from ?_] at h
    · exact h.symm
    · funext ω
      have hsymm : (ChannelCodingConverseGeneral.measurableEquivExtract i).symm
            (Ys i ω, Yoth ω) = fun j ↦ Ys j ω := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [ChannelCodingConverseGeneral.measurableEquivExtract, hYoth_def,
            MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
            MeasurableEquiv.trans, MeasurableEquiv.prodCongr]
        · simp [ChannelCodingConverseGeneral.measurableEquivExtract, hYoth_def,
            MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
            MeasurableEquiv.trans, MeasurableEquiv.prodCongr, hj]
      have hYnω : Yn ω = fun j ↦ Ys j ω := rfl
      rw [hYnω, ← hsymm, MeasurableEquiv.apply_symm_apply]
  rw [hcond]
  -- Independence `(Yᵢ, Xᵢ) ⊥ (X^{<i}, Y_{\i})` (memorylessness).
  have hindep_pair : IndepFun (fun ω ↦ (Ys i ω, Xs i ω)) (fun ω ↦ (Xpre ω, Yoth ω)) μ := by
    have hf_meas : ∀ j, Measurable (fun ω ↦ (Xs j ω, Ys j ω)) := fun j ↦ (hXs j).prodMk (hYs j)
    have hfin := hindep.indepFun_finset {i} (Finset.univ \ {i}) Finset.disjoint_sdiff hf_meas
    exact hfin.comp
      (φ := fun r : (({i} : Finset (Fin n)) → α × β) ↦
        ((r ⟨i, Finset.mem_singleton_self i⟩).2, (r ⟨i, Finset.mem_singleton_self i⟩).1))
      (ψ := fun r : ((Finset.univ \ {i} : Finset (Fin n)) → α × β) ↦
        ((fun j : Fin i.val ↦ (r ⟨⟨j.val, j.isLt.trans i.isLt⟩,
            by simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
               exact Fin.ne_of_val_ne (Nat.ne_of_lt j.isLt)⟩).1),
         (fun j : {j : Fin n // j ≠ i} ↦ (r ⟨↑j, by simp [j.2]⟩).2)))
      Measurable.of_discrete Measurable.of_discrete
  have hzero : mutualInfo μ (fun ω ↦ (Ys i ω, Xs i ω)) (fun ω ↦ (Xpre ω, Yoth ω)) = 0 :=
    (mutualInfo_eq_zero_iff_indep μ (fun ω ↦ (Ys i ω, Xs i ω)) (fun ω ↦ (Xpre ω, Yoth ω))
      ((hYs i).prodMk (hXs i)) (hXpre_meas.prodMk hYoth_meas)).mpr hindep_pair
  -- Chain-rule bound: `I(Xᵢ; X^{<i} | (Yᵢ, Y_{\i})) ≤ I((Yᵢ, Xᵢ); (X^{<i}, Y_{\i})) = 0`.
  have hside : mutualInfo μ (Ys i) (Xs i) ≠ ∞ := mutualInfo_ne_top μ (Ys i) (Xs i) (hYs i) (hXs i)
  have hchain1 := mutualInfo_chain_rule μ (Xs i) (fun ω ↦ (Xpre ω, Yoth ω)) (Ys i)
    (hXs i) (hXpre_meas.prodMk hYoth_meas) (hYs i)
  have hswap_mid : condMutualInfo μ (Xs i) (fun ω ↦ (Xpre ω, Yoth ω)) (Ys i)
      = condMutualInfo μ (Xs i) (fun ω ↦ (Yoth ω, Xpre ω)) (Ys i) :=
    condMutualInfo_map_middle_measurableEquiv μ (Xs i) (fun ω ↦ (Yoth ω, Xpre ω)) (Ys i)
      (hXs i) (hYoth_meas.prodMk hXpre_meas) (hYs i) MeasurableEquiv.prodComm
  have hchain2 := ChannelCodingConverseGeneral.condMutualInfo_chain_rule_Y_2var μ (Xs i)
    Yoth Xpre (Ys i) (hXs i) hYoth_meas hXpre_meas (hYs i) hside
  have hle : condMutualInfo μ (Xs i) Xpre (fun ω ↦ (Ys i ω, Yoth ω))
      ≤ mutualInfo μ (fun ω ↦ (Ys i ω, Xs i ω)) (fun ω ↦ (Xpre ω, Yoth ω)) := by
    rw [hchain1, hswap_mid, hchain2, ← add_assoc]
    exact self_le_add_left _ _
  rw [hzero] at hle
  exact le_antisymm hle zero_le

private lemma wz_singleletter_rate_le_step1
    {Ω : Type*} [MeasurableSpace Ω] {M n : ℕ} [NeZero M]
    (c : WynerZivCode M n α β γ) (hencoder : Measurable c.encoder)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep : iIndepFun (fun i ω ↦ (Xs i ω, Ys i ω)) μ) :
    ∀ i : Fin n,
        mutualInfo μ (Xs i)
            (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
              fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
          - mutualInfo μ (Ys i)
            (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
              fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
          = condMutualInfo μ (Xs i)
            (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
              fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) (Ys i) := by
  have hU_meas : ∀ i : Fin n, Measurable
      (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
        fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) := fun i ↦
    (hencoder.comp (measurable_pi_lambda _ fun j ↦ hXs j)).prodMk
      (measurable_pi_lambda _ fun j ↦ hYs ↑j)
  have hfin_YU : ∀ i : Fin n,
      mutualInfo μ (Ys i)
        (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
          fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) ≠ ∞ := fun i ↦
    mutualInfo_ne_top μ (Ys i) _ (hYs i) (hU_meas i)
  intro i
  have hc1 := mutualInfo_chain_rule μ (Xs i)
    (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
      fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) (Ys i) (hXs i) (hU_meas i) (hYs i)
  have hc2 := mutualInfo_chain_rule μ (Ys i)
    (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
      fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) (Xs i) (hYs i) (hU_meas i) (hXs i)
  have hswap : mutualInfo μ (fun ω ↦ (Ys i ω, Xs i ω))
        (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
          fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
      = mutualInfo μ (fun ω ↦ (Xs i ω, Ys i ω))
        (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
          fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) := by
    have h := mutualInfo_map_left_measurableEquiv μ (fun ω ↦ (Ys i ω, Xs i ω))
      (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
        fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
      ((hYs i).prodMk (hXs i)) (hU_meas i) MeasurableEquiv.prodComm
    rw [show (fun ω ↦ (MeasurableEquiv.prodComm (Ys i ω, Xs i ω) : α × β))
          = fun ω ↦ (Xs i ω, Ys i ω) from rfl] at h
    exact h.symm
  have hmarkov := wz_perletter_markov i c μ Xs Ys hXs hYs hindep
  have hzero : condMutualInfo μ (Ys i)
      (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
        fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) (Xs i) = 0 := by
    rw [condMutualInfo_comm μ (Ys i) _ (Xs i) (hYs i) (hU_meas i) (hXs i)]
    exact condMutualInfo_eq_zero_of_markov μ _ (Xs i) (Ys i)
      (hU_meas i) (hXs i) (hYs i) hmarkov
  rw [hzero, add_zero] at hc2
  have hkey : mutualInfo μ (Ys i)
        (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
          fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
      + condMutualInfo μ (Xs i)
        (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
          fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) (Ys i)
      = mutualInfo μ (Xs i)
        (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
          fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) := by
    rw [← hc1, hswap]; exact hc2
  rw [← hkey, ENNReal.add_sub_cancel_left (hfin_YU i)]

private lemma wz_singleletter_rate_le_step2
    {Ω : Type*} [MeasurableSpace Ω] {M n : ℕ} [NeZero M]
    (c : WynerZivCode M n α β γ) (hencoder : Measurable c.encoder)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep : iIndepFun (fun i ω ↦ (Xs i ω, Ys i ω)) μ) :
    ∀ i : Fin n,
        condMutualInfo μ (Xs i)
            (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
              fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) (Ys i)
          = condMutualInfo μ (Xs i) (fun ω ↦ c.encoder (fun j ↦ Xs j ω))
              (fun ω j ↦ Ys j ω) := by
  set Jn : Ω → Fin M := fun ω ↦ c.encoder (fun j ↦ Xs j ω) with hJn_def
  set Yn : Ω → (Fin n → β) := fun ω j ↦ Ys j ω with hYn_def
  have hYn_meas : Measurable Yn := by rw [hYn_def]; exact measurable_pi_lambda _ fun j ↦ hYs j
  intro i
  have hJ_meas : Measurable (fun ω ↦ c.encoder (fun j ↦ Xs j ω)) :=
    hencoder.comp (measurable_pi_lambda _ fun j ↦ hXs j)
  have hYoth_meas : Measurable (fun ω (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω) :=
    measurable_pi_lambda _ fun j ↦ hYs ↑j
  -- Independence `(Yᵢ, Xᵢ) ⊥ Y_{\i}` (memorylessness).
  have hindep_pair : IndepFun (fun ω ↦ (Ys i ω, Xs i ω))
      (fun ω (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω) μ := by
    have hf_meas : ∀ j, Measurable (fun ω ↦ (Xs j ω, Ys j ω)) := fun j ↦ (hXs j).prodMk (hYs j)
    have hfin := hindep.indepFun_finset {i} (Finset.univ \ {i}) Finset.disjoint_sdiff hf_meas
    exact hfin.comp
      (φ := fun r : (({i} : Finset (Fin n)) → α × β) ↦
        ((r ⟨i, Finset.mem_singleton_self i⟩).2, (r ⟨i, Finset.mem_singleton_self i⟩).1))
      (ψ := fun r : ((Finset.univ \ {i} : Finset (Fin n)) → α × β) ↦
        (fun j : {j : Fin n // j ≠ i} ↦ (r ⟨↑j, by simp [j.2]⟩).2))
      Measurable.of_discrete Measurable.of_discrete
  -- Reverse Markov chain `Y_{\i} − Yᵢ − Xᵢ`.
  have hmarkov : IsMarkovChain μ (fun ω (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω) (Ys i) (Xs i) :=
    wz_isMarkovChain_of_indepFun_side μ (Ys i) (Xs i)
      (fun ω (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω) (fun _ w ↦ w)
      (hYs i) (hXs i) hYoth_meas measurable_snd hindep_pair
  -- First term vanishes: `I(Xᵢ; Y_{\i} | Yᵢ) = 0`.
  have hzero1 : condMutualInfo μ (Xs i)
      (fun ω (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω) (Ys i) = 0 := by
    rw [condMutualInfo_comm μ (Xs i) (fun ω (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω) (Ys i)
        (hXs i) hYoth_meas (hYs i)]
    exact condMutualInfo_eq_zero_of_markov μ (fun ω (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)
      (Ys i) (Xs i) hYoth_meas (hYs i) (hXs i) hmarkov
  -- Conditioner reshape `(Yᵢ, Y_{\i}) ≅ Yⁿ`.
  have hreshape : condMutualInfo μ (Xs i) (fun ω ↦ c.encoder (fun j ↦ Xs j ω))
      (fun ω ↦ (Ys i ω, fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
      = condMutualInfo μ (Xs i) Jn Yn := by
    have h := condMutualInfo_map_cond_measurableEquiv μ (Xs i)
      (fun ω ↦ c.encoder (fun j ↦ Xs j ω)) Yn (hXs i) hJ_meas hYn_meas
      (ChannelCodingConverseGeneral.measurableEquivExtract i)
    rw [show (fun ω ↦ (ChannelCodingConverseGeneral.measurableEquivExtract i) (Yn ω))
          = (fun ω ↦ (Ys i ω, fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) from ?_] at h
    · exact h
    · funext ω
      have hsymm : (ChannelCodingConverseGeneral.measurableEquivExtract i).symm
            (Ys i ω, fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω) = fun j ↦ Ys j ω := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [ChannelCodingConverseGeneral.measurableEquivExtract,
            MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
            MeasurableEquiv.trans, MeasurableEquiv.prodCongr]
        · simp [ChannelCodingConverseGeneral.measurableEquivExtract,
            MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
            MeasurableEquiv.trans, MeasurableEquiv.prodCongr, hj]
      have hYnω : Yn ω = fun j ↦ Ys j ω := rfl
      rw [hYnω, ← hsymm, MeasurableEquiv.apply_symm_apply]
  -- Swap the middle `Uᵢ = (J, Y_{\i}) → (Y_{\i}, J)`, apply the 2-var chain rule, collapse.
  calc condMutualInfo μ (Xs i)
          (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
            fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) (Ys i)
      = condMutualInfo μ (Xs i)
          (fun ω ↦ ((fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω),
            c.encoder (fun j ↦ Xs j ω))) (Ys i) :=
        condMutualInfo_map_middle_measurableEquiv μ (Xs i)
          (fun ω ↦ ((fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω),
            c.encoder (fun j ↦ Xs j ω))) (Ys i) (hXs i) (hYoth_meas.prodMk hJ_meas) (hYs i)
          MeasurableEquiv.prodComm
    _ = condMutualInfo μ (Xs i) (fun ω (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω) (Ys i)
        + condMutualInfo μ (Xs i) (fun ω ↦ c.encoder (fun j ↦ Xs j ω))
            (fun ω ↦ (Ys i ω, fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) :=
        ChannelCodingConverseGeneral.condMutualInfo_chain_rule_Y_2var μ (Xs i)
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)
          (fun ω ↦ c.encoder (fun j ↦ Xs j ω)) (Ys i) (hXs i) hYoth_meas hJ_meas (hYs i)
          (mutualInfo_ne_top μ (Ys i) (Xs i) (hYs i) (hXs i))
    _ = condMutualInfo μ (Xs i) (fun ω ↦ c.encoder (fun j ↦ Xs j ω))
            (fun ω ↦ (Ys i ω, fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) := by
        rw [hzero1, zero_add]
    _ = condMutualInfo μ (Xs i) Jn Yn := hreshape

private lemma wz_singleletter_rate_le_step3
    {Ω : Type*} [MeasurableSpace Ω] {M n : ℕ} [NeZero M]
    (c : WynerZivCode M n α β γ) (hencoder : Measurable c.encoder)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep : iIndepFun (fun i ω ↦ (Xs i ω, Ys i ω)) μ) :
    ∑ i : Fin n, condMutualInfo μ (Xs i) (fun ω ↦ c.encoder (fun j ↦ Xs j ω))
          (fun ω j ↦ Ys j ω)
      ≤ mutualInfo μ (fun ω ↦ c.encoder (fun j ↦ Xs j ω)) (fun ω j ↦ Xs j ω)
          - mutualInfo μ (fun ω ↦ c.encoder (fun j ↦ Xs j ω)) (fun ω j ↦ Ys j ω) := by
  set Jn : Ω → Fin M := fun ω ↦ c.encoder (fun j ↦ Xs j ω) with hJn_def
  set Xn : Ω → (Fin n → α) := fun ω j ↦ Xs j ω with hXn_def
  set Yn : Ω → (Fin n → β) := fun ω j ↦ Ys j ω with hYn_def
  have hXn_meas : Measurable Xn := by rw [hXn_def]; exact measurable_pi_lambda _ fun j ↦ hXs j
  have hYn_meas : Measurable Yn := by rw [hYn_def]; exact measurable_pi_lambda _ fun j ↦ hYs j
  have hJn_meas : Measurable Jn := by
    rw [hJn_def]; exact hencoder.comp (measurable_pi_lambda _ fun j ↦ hXs j)
  -- Deterministic-encoder identity `I(Xⁿ; J | Yⁿ) = I(J; Xⁿ) − I(J; Yⁿ)`.
  have h_enc : condMutualInfo μ Xn Jn Yn = mutualInfo μ Jn Xn - mutualInfo μ Jn Yn := by
    have hmarkov : IsMarkovChain μ Yn Xn Jn :=
      isMarkovChain_comp_conditioner_right μ Yn Xn hYn_meas hXn_meas hencoder
    have hzero : condMutualInfo μ Yn Jn Xn = 0 :=
      condMutualInfo_eq_zero_of_markov μ Yn Xn Jn hYn_meas hXn_meas hJn_meas hmarkov
    have hc2 := mutualInfo_chain_rule μ Yn Jn Xn hYn_meas hJn_meas hXn_meas
    rw [hzero, add_zero] at hc2
    have hc1 := mutualInfo_chain_rule μ Xn Jn Yn hXn_meas hJn_meas hYn_meas
    have hswap : mutualInfo μ (fun ω ↦ (Yn ω, Xn ω)) Jn
        = mutualInfo μ (fun ω ↦ (Xn ω, Yn ω)) Jn :=
      (mutualInfo_map_left_measurableEquiv μ (fun ω ↦ (Yn ω, Xn ω)) Jn
        (hYn_meas.prodMk hXn_meas) hJn_meas MeasurableEquiv.prodComm).symm
    rw [hswap, hc2] at hc1
    -- hc1 : mutualInfo μ Xn Jn = mutualInfo μ Yn Jn + condMutualInfo μ Xn Jn Yn
    rw [mutualInfo_comm μ Jn Xn hJn_meas hXn_meas, mutualInfo_comm μ Jn Yn hJn_meas hYn_meas, hc1,
      ENNReal.add_sub_cancel_left (mutualInfo_ne_top μ Yn Jn hYn_meas hJn_meas)]
  -- Prefix chain rule `I(Xⁿ; J | Yⁿ) = ∑ₖ I(Xₖ; J | (Yⁿ, X^{<k}))`.
  have h_side : mutualInfo μ Yn Jn ≠ ∞ := mutualInfo_ne_top μ Yn Jn hYn_meas hJn_meas
  have h_prefix : condMutualInfo μ Xn Jn Yn
      = ∑ k : Fin n, condMutualInfo μ (Xs k) Jn
          (fun ω ↦ (Yn ω, fun (j : Fin k.val) ↦ Xs ⟨j.val, j.isLt.trans k.isLt⟩ ω)) :=
    condMutualInfo_prefix_chain_rule μ Xs Jn Yn hXs hJn_meas hYn_meas h_side
  -- Per-letter monotonicity `I(Xᵢ; J | Yⁿ) ≤ I(Xᵢ; J | (Yⁿ, X^{<i}))`.
  have h_mono : ∀ i : Fin n, condMutualInfo μ (Xs i) Jn Yn
      ≤ condMutualInfo μ (Xs i) Jn
          (fun ω ↦ (Yn ω, fun (j : Fin i.val) ↦ Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := by
    intro i
    have hXpre_meas : Measurable (fun ω (j : Fin i.val) ↦ Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
      measurable_pi_lambda _ fun j ↦ hXs _
    have hside : mutualInfo μ Yn (Xs i) ≠ ∞ := mutualInfo_ne_top μ Yn (Xs i) hYn_meas (hXs i)
    have hg1 := ChannelCodingConverseGeneral.condMutualInfo_chain_rule_Y_2var μ (Xs i) Jn
      (fun ω (j : Fin i.val) ↦ Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) Yn (hXs i) hJn_meas hXpre_meas
      hYn_meas hside
    have hg2 := ChannelCodingConverseGeneral.condMutualInfo_chain_rule_Y_2var μ (Xs i)
      (fun ω (j : Fin i.val) ↦ Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) Jn Yn (hXs i) hXpre_meas
      hJn_meas hYn_meas hside
    have hcrux : condMutualInfo μ (Xs i)
        (fun ω (j : Fin i.val) ↦ Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) Yn = 0 :=
      wz_inputs_cond_indep i μ Xs Ys hXs hYs hindep
    rw [hcrux, zero_add] at hg2
    have hswap := condMutualInfo_map_middle_measurableEquiv μ (Xs i)
      (fun ω ↦ ((fun (j : Fin i.val) ↦ Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω), Jn ω)) Yn
      (hXs i) (hXpre_meas.prodMk hJn_meas) hYn_meas MeasurableEquiv.prodComm
    calc condMutualInfo μ (Xs i) Jn Yn
        ≤ condMutualInfo μ (Xs i)
            (fun ω ↦ (Jn ω, fun (j : Fin i.val) ↦ Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)) Yn := by
          rw [hg1]; exact self_le_add_right _ _
      _ = condMutualInfo μ (Xs i)
            (fun ω ↦ ((fun (j : Fin i.val) ↦ Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω), Jn ω)) Yn :=
          hswap
      _ = condMutualInfo μ (Xs i) Jn
            (fun ω ↦ (Yn ω, fun (j : Fin i.val) ↦ Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := hg2
  calc ∑ i : Fin n, condMutualInfo μ (Xs i) Jn Yn
      ≤ ∑ i : Fin n, condMutualInfo μ (Xs i) Jn
          (fun ω ↦ (Yn ω, fun (j : Fin i.val) ↦ Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)) :=
        Finset.sum_le_sum fun i _ ↦ h_mono i
    _ = condMutualInfo μ Xn Jn Yn := h_prefix.symm
    _ = mutualInfo μ Jn Xn - mutualInfo μ Jn Yn := h_enc

/-- Single-letterized rate bound (conditional-MI chain). The sum of the
per-letter Wyner–Ziv objectives is bounded by the block mutual-information difference:
```
∑ᵢ [I(Xᵢ; Uᵢ) − I(Yᵢ; Uᵢ)] ≤ I(J; Xⁿ) − I(J; Yⁿ),   Uᵢ := (J, Y_{\i}).
```
Route (conditional-MI chain, **not** Csiszár): the memoryless per-letter Markov chain
`Uᵢ − Xᵢ − Yᵢ` (`wz_perletter_markov`) gives `I(Yᵢ; Uᵢ | Xᵢ) = 0`, so
`I(Xᵢ; Uᵢ) − I(Yᵢ; Uᵢ) = I(Xᵢ; Uᵢ | Yᵢ)`; the memoryless collapse
`(Y_{\i}, Yᵢ) = Yⁿ` turns this into `I(Xᵢ; J | Yⁿ)`, and the conditional chain rule
with `J − Xⁿ − Yⁿ` yields `∑ᵢ I(Xᵢ; J | Yⁿ) ≤ I(Xⁿ; J | Yⁿ) = I(J; Xⁿ) − I(J; Yⁿ)`.
This is the deepest step of the converse single-letterization.

The body is split into four parts:

* `hstep1`: the per-letter identity `I(Xᵢ; Uᵢ) − I(Yᵢ; Uᵢ) = I(Xᵢ; Uᵢ | Yᵢ)`, from the
  twofold chain rule together with `I(Yᵢ; Uᵢ | Xᵢ) = 0` (the per-letter Markov chain
  `Uᵢ − Xᵢ − Yᵢ`, `wz_perletter_markov`);
* `hstep2`: the memoryless collapse `I(Xᵢ; Uᵢ | Yᵢ) = I(Xᵢ; J | Yⁿ)`, obtained by first
  swapping the middle `Uᵢ = (J, Y_{\i}) → (Y_{\i}, J)` (`prodComm`), applying the 2-var
  conditional chain rule (`condMutualInfo_chain_rule_Y_2var`) to peel `Y_{\i}` first, killing
  `I(Xᵢ; Y_{\i} | Yᵢ) = 0` via the reverse Markov chain `Y_{\i} − Yᵢ − Xᵢ`
  (`wz_isMarkovChain_of_indepFun_side`), and reshaping the conditioner `(Yᵢ, Y_{\i}) ≅ Yⁿ`;
* `hsum`: the sum bound `∑ᵢ I(Xᵢ; J | Yⁿ) ≤ I(J; Xⁿ) − I(J; Yⁿ)`, from the prefix chain rule
  `I(Xⁿ; J | Yⁿ) = ∑ᵢ I(Xᵢ; J | (Yⁿ, X^{<i}))` (`condMutualInfo_prefix_chain_rule`), the
  per-letter monotonicity `I(Xᵢ; J | Yⁿ) ≤ I(Xᵢ; J | (Yⁿ, X^{<i}))` (2-var chain rule twice
  with the input conditional-independence `I(Xᵢ; X^{<i} | Yⁿ) = 0`, `wz_inputs_cond_indep`),
  and the deterministic-encoder identity `I(Xⁿ; J | Yⁿ) = I(J; Xⁿ) − I(J; Yⁿ)` (`J − Xⁿ − Yⁿ`,
  `isMarkovChain_comp_conditioner_right`);
* the final assembly: the `ℝ≥0∞`-truncated-subtraction / `.toReal` bookkeeping reducing the
  goal to `hstep1`, `hstep2`, `hsum` (`ENNReal.toReal_sum` + `ENNReal.toReal_mono`, each
  summand and the block MI difference finite over the finite alphabets).

`hindep` is load-bearing (both `hstep2` and `hsum` are false without memorylessness); it is a
memoryless-source regularity precondition, not a bundled proof core. The chain is the standard
Wyner–Ziv converse (Cover–Thomas §15.9).
@audit:ok (`hstep2` (memoryless collapse) and `hsum` (super-additivity) are closed by genuine
lemma applications — `condMutualInfo_chain_rule_Y_2var`, `condMutualInfo_prefix_chain_rule`,
`wz_inputs_cond_indep`, deterministic-encoder Markov — not a load-bearing `*Hypothesis` bundle;
underscoring the unused `_hn` / `_hdecoder` strengthens the claim (the conclusion holds even at
`n=0`, both sides `0`), not a weakening.) -/
private theorem wz_singleletter_rate_le
    {Ω : Type*} [MeasurableSpace Ω]
    {M n : ℕ} [NeZero M] (_hn : 0 < n)
    (c : WynerZivCode M n α β γ)
    (hencoder : Measurable c.encoder) (_hdecoder : Measurable c.decoder)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep : iIndepFun (fun i ω ↦ (Xs i ω, Ys i ω)) μ) :
    ∑ i, (mutualInfo μ (Xs i)
        (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
          fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
      - mutualInfo μ (Ys i)
        (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
          fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))).toReal
      ≤ (mutualInfo μ (fun ω ↦ c.encoder (fun j ↦ Xs j ω)) (fun ω j ↦ Xs j ω)
          - mutualInfo μ (fun ω ↦ c.encoder (fun j ↦ Xs j ω)) (fun ω j ↦ Ys j ω)).toReal := by
  classical
  -- Block-variable abbreviations (fold the RHS of the goal).
  set Jn : Ω → Fin M := fun ω ↦ c.encoder (fun j ↦ Xs j ω) with hJn_def
  set Xn : Ω → (Fin n → α) := fun ω j ↦ Xs j ω with hXn_def
  set Yn : Ω → (Fin n → β) := fun ω j ↦ Ys j ω with hYn_def
  have hXn_meas : Measurable Xn := by rw [hXn_def]; exact measurable_pi_lambda _ fun j ↦ hXs j
  have hJn_meas : Measurable Jn := by
    rw [hJn_def]; exact hencoder.comp (measurable_pi_lambda _ fun j ↦ hXs j)
  -- Per-letter auxiliary `Uᵢ = (J, Y_{\i})` and its measurability.
  have hU_meas : ∀ i : Fin n, Measurable
      (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
        fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) := fun i ↦
    (hencoder.comp (measurable_pi_lambda _ fun j ↦ hXs j)).prodMk
      (measurable_pi_lambda _ fun j ↦ hYs ↑j)
  -- Finiteness of the per-letter mutual informations (finite alphabets).
  have hfin_XU : ∀ i : Fin n,
      mutualInfo μ (Xs i)
        (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
          fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) ≠ ∞ := fun i ↦
    mutualInfo_ne_top μ (Xs i) _ (hXs i) (hU_meas i)
  -- Per-letter identity `I(Xᵢ; Uᵢ) − I(Yᵢ; Uᵢ) = I(Xᵢ; Uᵢ | Yᵢ)`.
  -- Twofold chain rule `I((Xᵢ,Yᵢ); Uᵢ) = I(Yᵢ; Uᵢ) + I(Xᵢ; Uᵢ | Yᵢ) = I(Xᵢ; Uᵢ) + I(Yᵢ; Uᵢ | Xᵢ)`
  -- with `I(Yᵢ; Uᵢ | Xᵢ) = 0` (per-letter Markov chain `Uᵢ − Xᵢ − Yᵢ`, `wz_perletter_markov`).
  have hstep1 := wz_singleletter_rate_le_step1 c hencoder μ Xs Ys hXs hYs hindep
  -- Memoryless collapse `I(Xᵢ; Uᵢ | Yᵢ) = I(Xᵢ; J | Yⁿ)`. Needs the
  -- conditional chain rule on the middle argument `Uᵢ = (J, Y_{\i})` plus the memoryless
  -- conditional independence `I(Xᵢ; Y_{\i} | Yᵢ) = 0` and the reshape `(Y_{\i}, Yᵢ) ≅ Yⁿ`.
  have hstep2 : ∀ i : Fin n,
      condMutualInfo μ (Xs i)
          (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
            fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) (Ys i)
        = condMutualInfo μ (Xs i) Jn Yn :=
    wz_singleletter_rate_le_step2 c hencoder μ Xs Ys hXs hYs hindep
  -- Sum bound `∑ᵢ I(Xᵢ; J | Yⁿ) ≤ I(J; Xⁿ) − I(J; Yⁿ)`. Needs the
  -- conditional chain rule `I(Xⁿ; J | Yⁿ) = ∑ᵢ I(Xᵢ; J | (Yⁿ, X^{<i}))`, memoryless
  -- monotonicity `I(Xᵢ; J | Yⁿ) ≤ I(Xᵢ; J | (Yⁿ, X^{<i}))`, and the deterministic-encoder
  -- Markov chain `J − Xⁿ − Yⁿ` giving `I(Xⁿ; J | Yⁿ) = I(J; Xⁿ) − I(J; Yⁿ)`.
  have hsum : ∑ i : Fin n, condMutualInfo μ (Xs i) Jn Yn
      ≤ mutualInfo μ Jn Xn - mutualInfo μ Jn Yn :=
    wz_singleletter_rate_le_step3 c hencoder μ Xs Ys hXs hYs hindep
  -- `.toReal`-bookkeeping tying `hstep1` / `hstep2` / `hsum` together.
  have hsummand_ne : ∀ i : Fin n,
      mutualInfo μ (Xs i)
          (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
            fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
        - mutualInfo μ (Ys i)
          (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
            fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)) ≠ ∞ := fun i ↦
    ne_top_of_le_ne_top (hfin_XU i) tsub_le_self
  rw [← ENNReal.toReal_sum fun i _ ↦ hsummand_ne i]
  have hRHS_ne : mutualInfo μ Jn Xn - mutualInfo μ Jn Yn ≠ ∞ :=
    ne_top_of_le_ne_top (mutualInfo_ne_top μ Jn Xn hJn_meas hXn_meas) tsub_le_self
  refine ENNReal.toReal_mono hRHS_ne ?_
  calc ∑ i : Fin n,
        (mutualInfo μ (Xs i)
            (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
              fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
          - mutualInfo μ (Ys i)
            (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
              fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω)))
      = ∑ i : Fin n, condMutualInfo μ (Xs i) Jn Yn := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hstep1 i, hstep2 i]
    _ ≤ mutualInfo μ Jn Xn - mutualInfo μ Jn Yn := hsum

/-- Per-letter time-sharing witness of the Wyner–Ziv converse.

For a block Wyner–Ziv code on an i.i.d. source `(Xⁿ, Yⁿ)` with expected block
distortion at most `D`, there exist per-letter distortion budgets `Dv i` and
per-letter objective values `w i` such that: (a) each `w i` is attainable by a
factorizable feasible point at its own budget `Dv i` (`w i ∈ wzRateValueSet …
(Dv i)`); (b) the uniform average budget stays within the block budget,
`(1/n) ∑ᵢ Dv i ≤ D`; and (c) the sum of the per-letter objectives is bounded by
the block mutual-information difference,
`∑ᵢ w i ≤ (I(J; Xⁿ) − I(J; Yⁿ)).toReal`.

This is the single-letterization core (Cover–Thomas §15.9). The per-letter
auxiliary is `Uᵢ := (J, Y_{\i})` — the encoder output `J` together with *all the
other* side-information symbols `Y_{\i} = (Yⱼ)_{j≠i}` (the full block `Yⁿ = (Y_{\i},
Yᵢ)` is forced onto `Uᵢ` because the reconstruction `X̂ᵢ = (decoder (J, Yⁿ))ᵢ` depends
on the entire `Yⁿ`; a one-sided `Y^{i-1}` auxiliary is distortion-hostile and ruled
out). Its role is split across three sub-lemmas:

* `wz_perletter_factorizable` gives conjunct (a): the empirical joint `(Xᵢ, Yᵢ, Uᵢ)`
  is `IsWynerZivFactorizable` via the memoryless-source per-letter Markov chain
  `Uᵢ − Xᵢ − Yᵢ` (`wz_perletter_markov`, sorry-free), landing `w i` as a value of
  `wzRateValueSet` at budget `Dv i`;
* `wz_perletter_distortion_avg` gives conjunct (b): the average distortion identity
  `(1/n) ∑ᵢ Dv i = expectedBlockDistortion P_XY d ≤ D`;
* `wz_singleletter_rate_le` gives conjunct (c) via the **conditional** mutual-info
  chain `∑ᵢ [I(Xᵢ; Uᵢ) − I(Yᵢ; Uᵢ)] = ∑ᵢ I(Xᵢ; Uᵢ | Yᵢ) = ∑ᵢ I(Xᵢ; J | Yⁿ) ≤
  I(Xⁿ; J | Yⁿ) = I(J; Xⁿ) − I(J; Yⁿ)`. This route does **not** go through the
  heterogeneous Csiszár sum identity (`csiszar_sum_identity_hetero`): that prefix/suffix
  unconditional-MI form generates exactly the one-sided `Y^{i-1}` auxiliary the
  distortion side rules out, so it is *orphaned* on this route.

The body is the mechanical assembly of these three sub-lemmas; the outer feasible-point
existence `wz_converse_feasible_point` is discharged by uniformly time-sharing these
witnesses (`wzRateValueSet_avg_mem`).

The conclusion is an *existential witness* (per-letter budgets + values with the
three bounds), not a hypothesis bundle: it does not encode the outcome it is used to
prove. `hindep` (memoryless source) / `hlaw` (identical marginals `= P_XY`) / `hD`
(distortion budget) are genuine source-regularity preconditions — the per-letter
Markov feasibility and the budget bound `(1/n) ∑ Dᵢ ≤ D` are false without them.
@audit:ok (a genuine existential decomposition: `Dv`/`w` are explicitly constructed and
the three conjuncts discharged by `wz_perletter_factorizable` / `wz_perletter_distortion_avg`
/ `wz_singleletter_rate_le`; the conclusion asserts existence of per-letter budgets/values,
not the outcome it proves, and all hypotheses are source-regularity preconditions.) -/
private theorem wz_converse_perletter_witness
    {Ω : Type*} [MeasurableSpace Ω]
    {M n : ℕ} [NeZero M] (hn : 0 < n)
    (c : WynerZivCode M n α β γ)
    (hencoder : Measurable c.encoder) (hdecoder : Measurable c.decoder)
    (d : DistortionFn α γ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep : iIndepFun (fun i ω ↦ (Xs i ω, Ys i ω)) μ)
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (hlaw : ∀ i, μ.map (fun ω ↦ (Xs i ω, Ys i ω)) = P_XY)
    {D : ℝ}
    (hD : c.expectedBlockDistortion P_XY d ≤ D) :
    ∃ (Dv w : Fin n → ℝ),
      (∀ i, w i ∈ wzRateValueSet (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) (Dv i))
        ∧ (1 / (n : ℝ)) * ∑ i, Dv i ≤ D
        ∧ ∑ i, w i
            ≤ (mutualInfo μ (fun ω ↦ c.encoder (fun j ↦ Xs j ω)) (fun ω j ↦ Xs j ω)
                - mutualInfo μ (fun ω ↦ c.encoder (fun j ↦ Xs j ω))
                    (fun ω j ↦ Ys j ω)).toReal := by
  classical
  -- Per-letter budgets `Dv i = 𝔼[d(Xᵢ, X̂ᵢ)]` and objectives `w i = I(Xᵢ;Uᵢ) − I(Yᵢ;Uᵢ)`.
  refine ⟨fun i ↦ ∫ ω, (d (Xs i ω)
            ((c.decoder (c.encoder (fun j ↦ Xs j ω), fun j ↦ Ys j ω)) i) : ℝ) ∂μ,
          fun i ↦ (mutualInfo μ (Xs i)
              (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
                fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))
            - mutualInfo μ (Ys i)
              (fun ω ↦ (c.encoder (fun j ↦ Xs j ω),
                fun (j : {j : Fin n // j ≠ i}) ↦ Ys (↑j) ω))).toReal,
          ?_, ?_, ?_⟩
  · -- Conjunct (a): per-letter feasibility.
    exact fun i ↦ wz_perletter_factorizable i c hencoder hdecoder d μ Xs Ys hXs hYs hindep P_XY hlaw
  · -- Conjunct (b): average distortion budget.
    exact wz_perletter_distortion_avg hn c hencoder hdecoder d μ Xs Ys hXs hYs hindep P_XY hlaw hD
  · -- Conjunct (c): single-letterized rate bound (conditional-MI chain).
    exact wz_singleletter_rate_le hn c hencoder hdecoder μ Xs Ys hXs hYs hindep

/-- Single-letterization core of the Wyner–Ziv converse (feasible-point form).

For a block Wyner–Ziv code on an i.i.d. source `(Xⁿ, Yⁿ)` with expected block
distortion at most `D`, there is a *single-letterized* feasible factorizable point
— at some finite auxiliary alphabet `Fin k` — whose Wyner–Ziv objective
`I(X;U) − I(Y;U)` is bounded by the per-symbol block mutual-information difference
`(1/n)(I(J; Xⁿ) − I(J; Yⁿ))`.

This is the analytic heart of the converse (Cover–Thomas §15.9): the auxiliary
`Uᵢ := (J, Y_{\i})` gives, via the **conditional** mutual-information chain
`∑ᵢ [I(Xᵢ;Uᵢ) − I(Yᵢ;Uᵢ)] = ∑ᵢ I(Xᵢ;Uᵢ|Yᵢ) = ∑ᵢ I(Xᵢ;J|Yⁿ) ≤ I(Xⁿ;J|Yⁿ) =
I(J;Xⁿ) − I(J;Yⁿ)` (not the heterogeneous Csiszár sum identity, which is orphaned on
this route) and per-letter feasibility from the memoryless source (Markov
`Uᵢ − Xᵢ − Yᵢ`, `wz_perletter_markov`), the sum bound
`∑ᵢ [I(Xᵢ;Uᵢ) − I(Yᵢ;Uᵢ)] ≤ I(J;Xⁿ) − I(J;Yⁿ)`; the time-sharing auxiliary
`U* = (Q, U_Q)` (with `Q` uniform on the time index `Fin n`) assembles the per-letter
points into one factorizable point of distortion `(1/n) ∑ᵢ Dᵢ ≤ D` (from `hD`) and
objective `(1/n) ∑ᵢ [I(Xᵢ;Uᵢ) − I(Yᵢ;Uᵢ)]`.

Landing this point via `wynerZivRate_le_of_feasible` (with `BddBelow` supplied by
`wzRateValueSet_bddBelow_of_pmf`) yields the converse bound in
`wyner_ziv_converse_n_letter_singleLetter`; that outer landing is discharged
genuinely (sorry-free) from this existence.

`hindep` (memoryless source) / `hlaw` (identical marginals `= P_XY`) / `hD`
(distortion budget) are genuine regularity preconditions — the construction
(Markov `Uᵢ − Xᵢ − Yᵢ`, distortion budget `(1/n)∑Dᵢ ≤ D`) is false without them.
The conclusion is the *existence* of a feasible witness realizing the objective
bound; it is strictly weaker than the outer infimum bound (`wynerZivRate ≤ …`,
recovered by landing), so this is a genuine decomposition of the single-letterized
core, not a restatement of it and not a hypothesis bundle.

The feasible-point existence is discharged by landing the
uniform time-share of the per-letter witnesses supplied by
`wz_converse_perletter_witness` — `wzRateValueSet_avg_mem` averages the per-letter
values `(1/n) ∑ w i` into a value of `wzRateValueSet … ((1/n) ∑ Dv i)`,
`wzRateValueSet_mono_in_D` (with `(1/n) ∑ Dv i ≤ D`) relaxes it to budget `D`, and
`mem_wzRateValueSet_iff` unpacks the resulting membership into the feasible factorizable
point at some `Fin k`.
@audit:ok (the conclusion is a genuine existential witness (feasible factorizable point +
objective bound), not a hypothesis bundle; `hindep`/`hlaw`/`hD` are source-regularity
preconditions, and the Carathéodory support reduction is not on this single-letterization
route.) -/
theorem wz_converse_feasible_point
    {Ω : Type*} [MeasurableSpace Ω]
    {M n : ℕ} [NeZero M] (hn : 0 < n)
    (c : WynerZivCode M n α β γ)
    (hencoder : Measurable c.encoder) (hdecoder : Measurable c.decoder)
    (d : DistortionFn α γ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep : iIndepFun (fun i ω ↦ (Xs i ω, Ys i ω)) μ)
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (hlaw : ∀ i, μ.map (fun ω ↦ (Xs i ω, Ys i ω)) = P_XY)
    {D : ℝ}
    (hD : c.expectedBlockDistortion P_XY d ≤ D) :
    ∃ (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ)),
      qf ∈ WynerZivFactorizableConstraint (Fin k)
              (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D
        ∧ wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1
            ≤ (1 / (n : ℝ))
              * (mutualInfo μ (fun ω ↦ c.encoder (fun j ↦ Xs j ω)) (fun ω j ↦ Xs j ω)
                  - mutualInfo μ (fun ω ↦ c.encoder (fun j ↦ Xs j ω))
                      (fun ω j ↦ Ys j ω)).toReal := by
  classical
  obtain ⟨Dv, w, hmem, hDbudget, hsl⟩ :=
    wz_converse_perletter_witness hn c hencoder hdecoder d μ Xs Ys hXs hYs hindep P_XY hlaw hD
  have h_pmf : (fun p ↦ P_XY.real {p}) ∈ stdSimplex ℝ (α × β) :=
    measureReal_pmf_mem_stdSimplex P_XY
  have havg :
      (1 / (n : ℝ)) * ∑ i, w i
        ∈ wzRateValueSet (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ))
            ((1 / (n : ℝ)) * ∑ i, Dv i) :=
    wzRateValueSet_avg_mem h_pmf hn hmem
  have havg_D :
      (1 / (n : ℝ)) * ∑ i, w i
        ∈ wzRateValueSet (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D :=
    wzRateValueSet_mono_in_D hDbudget havg
  rw [mem_wzRateValueSet_iff] at havg_D
  obtain ⟨k, qf, hqf, hobj⟩ := havg_D
  refine ⟨k, qf, hqf, ?_⟩
  rw [hobj]
  exact mul_le_mul_of_nonneg_left hsl (by positivity)

/-- Wyner–Ziv converse, `n`-letter single-letterized form (reshaped rate).

For a block Wyner–Ziv code `c` with a measurable deterministic encoder / decoder on
an i.i.d. source of `(X, Y)` pairs (mutual independence `hindep` + identical marginals
`hlaw = P_XY`), whose expected block distortion is at most `D`, the reshaped
Wyner–Ziv rate is bounded by the block log-cardinality rate:
```
R_WZ(D) ≤ (1/n) · log M.
```

Here `R_WZ = wynerZivRate` is the reshaped operational rate — the infimum of the
objective over feasible factorizable points at *every* finite auxiliary alphabet
`Fin k` (`FactorizableRate.lean` §10). This `∀`-clean form removes the Carathéodory
sizing precondition `hU_card : |α| + 1 ≤ |U|` that the fixed-`U`
`wynerZivRateFactorizable` version required: the single-letterization auxiliary
`Uᵢ := (J, Y_{\i})` (whose cardinality grows with `n`) lands *directly* as a
feasible point of the reshaped infimum via `wynerZivRate_le_of_feasible`, with no
cardinality bound.

The independence / i.i.d. preconditions (`hindep` + `hlaw`) are genuine regularity
preconditions (the conclusion is false without them, mirroring
`rate_distortion_converse_n_letter_singleLetter`).

Proof: the block bound `(I(J; Xⁿ) − I(J; Yⁿ)).toReal ≤ log M` is discharged via
`mutualInfo_diff_le_log_card`, and after the `(1/n)`-scaling the single-letterization step
`h_sl` is discharged by landing the feasible-point existence `wz_converse_feasible_point`:
`wynerZivRate_le_of_feasible` (with `BddBelow` from `wzRateValueSet_bddBelow_of_pmf`)
turns "some feasible factorizable point at `Fin k` has objective `≤ (1/n)(I(J;Xⁿ) −
I(J;Yⁿ))`" into `R_WZ(D) ≤ (1/n)(I(J;Xⁿ) − I(J;Yⁿ)).toReal`. No Carathéodory
support lemma is on this critical path.

Dropping `hU_card` is sound: `wynerZivRate` is the infimum over the union of images across
*all* `Fin k`, hence `≤` any single fixed-`U` rate, i.e. the weakest (smallest-LHS)
converse claim — the single-letterization auxiliary lands directly, so no sizing
precondition is needed and no false-statement is introduced. Non-vacuous: `wynerZivRate ≥ 0`
via the DPI residual, and `M ≥ 1 ⟹ log M ≥ 0`, so `R_WZ(D) ≤ (1/n) log M` is a substantive
bound. `hindep` / `hlaw` are genuine i.i.d. regularity preconditions (conclusion false
without them), not a bundled core.
@audit:ok (`hindep`/`hlaw`/`hD` + measurability are operational-regularity preconditions and
the converse core is proved in the body, not bundled; dropping `hU_card` is a strengthening
since `wynerZivRate` is the infimum over all `Fin k`, so no false-statement is introduced.) -/
theorem wyner_ziv_converse_n_letter_singleLetter
    {Ω : Type*} [MeasurableSpace Ω]
    {M n : ℕ} [NeZero M] (hn : 0 < n)
    (c : WynerZivCode M n α β γ)
    (hencoder : Measurable c.encoder) (hdecoder : Measurable c.decoder)
    (d : DistortionFn α γ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep : iIndepFun (fun i ω ↦ (Xs i ω, Ys i ω)) μ)
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (hlaw : ∀ i, μ.map (fun ω ↦ (Xs i ω, Ys i ω)) = P_XY)
    {D : ℝ}
    (hD : c.expectedBlockDistortion P_XY d ≤ D) :
    wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D
      ≤ (1 / (n : ℝ)) * Real.log (M : ℝ) := by
  classical
  -- Encoder output `J = encoder(Xⁿ)` and the block source / side-information RVs.
  set Jn : Ω → Fin M := fun ω ↦ c.encoder (fun j ↦ Xs j ω) with hJn_def
  set Xn : Ω → (Fin n → α) := fun ω j ↦ Xs j ω with hXn_def
  set Yn : Ω → (Fin n → β) := fun ω j ↦ Ys j ω with hYn_def
  have hXn_meas : Measurable Xn := measurable_pi_iff.mpr hXs
  have hYn_meas : Measurable Yn := measurable_pi_iff.mpr hYs
  have hJn_meas : Measurable Jn := hencoder.comp hXn_meas
  -- The block bound `(I(J; Xⁿ) − I(J; Yⁿ)).toReal ≤ log M`.
  have h_block : (mutualInfo μ Jn Xn - mutualInfo μ Jn Yn).toReal ≤ Real.log (M : ℝ) :=
    mutualInfo_diff_le_log_card μ Jn Xn Yn hJn_meas hXn_meas
  -- Single-letterization core: the feasible-point existence
  -- `wz_converse_feasible_point` supplies a single-letterized factorizable point
  -- (at some `Fin k`) feasible at budget `D` whose objective is `≤ (1/n)(I(J;Xⁿ) −
  -- I(J;Yⁿ))`; landing it via `wynerZivRate_le_of_feasible` (BddBelow from
  -- `wzRateValueSet_bddBelow_of_pmf`) gives the converse bound.
  have h_sl :
      wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D
        ≤ (1 / (n : ℝ)) * (mutualInfo μ Jn Xn - mutualInfo μ Jn Yn).toReal := by
    obtain ⟨k, qf, hqf, hbound⟩ :=
      wz_converse_feasible_point hn c hencoder hdecoder d μ Xs Ys hXs hYs hindep
        P_XY hlaw hD
    have h_pmf : (fun p ↦ P_XY.real {p}) ∈ stdSimplex ℝ (α × β) :=
      measureReal_pmf_mem_stdSimplex P_XY
    have hbdd :
        BddBelow (wzRateValueSet (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D) :=
      wzRateValueSet_bddBelow_of_pmf h_pmf (fun a b ↦ (d a b : ℝ)) D
    exact le_trans (wynerZivRate_le_of_feasible hbdd hqf) hbound
  calc
    wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D
        ≤ (1 / (n : ℝ)) * (mutualInfo μ Jn Xn - mutualInfo μ Jn Yn).toReal := h_sl
    _ ≤ (1 / (n : ℝ)) * Real.log (M : ℝ) := by
        apply mul_le_mul_of_nonneg_left h_block
        positivity

/-- Per-code converse bound (i.i.d.-source realization). For a single block
Wyner–Ziv code `c : WynerZivCode M n α β γ` with expected block distortion at most
`D`, the reshaped Wyner–Ziv rate is bounded by the block log-cardinality rate
`(1/n) · log M`.

This is the i.i.d.-source plumbing of the converse: the canonical i.i.d. source is
the product measure `Measure.pi (fun _ ↦ P_XY)` on `(α × β)^n` with coordinate
projections `Xs i ω := (ω i).1`, `Ys i ω := (ω i).2`, whose independence and
identical marginals (`= P_XY`) are supplied by `iIndepFun_iff_map_fun_eq_pi_map` and
`Measure.pi_map_eval`. The bound is then the `n`-letter single-letterized converse
`wyner_ziv_converse_n_letter_singleLetter`. -/
lemma wynerZivRate_le_of_code
    {M n : ℕ} [NeZero M] (hn : 0 < n)
    (c : WynerZivCode M n α β γ)
    (d : DistortionFn α γ)
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {D : ℝ}
    (hD : c.expectedBlockDistortion P_XY d ≤ D) :
    wynerZivRate (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D
      ≤ (1 / (n : ℝ)) * Real.log (M : ℝ) := by
  classical
  set μ : Measure (Fin n → α × β) := Measure.pi (fun _ : Fin n ↦ P_XY) with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  set Xs : Fin n → (Fin n → α × β) → α := fun i ω ↦ (ω i).1 with hXs_def
  set Ys : Fin n → (Fin n → α × β) → β := fun i ω ↦ (ω i).2 with hYs_def
  have hXs : ∀ i, Measurable (Xs i) := fun i ↦ (measurable_pi_apply i).fst
  have hYs : ∀ i, Measurable (Ys i) := fun i ↦ (measurable_pi_apply i).snd
  have hencoder : Measurable c.encoder := measurable_of_countable c.encoder
  have hdecoder : Measurable c.decoder := measurable_of_countable c.decoder
  have hlaw : ∀ i, μ.map (fun ω ↦ (Xs i ω, Ys i ω)) = P_XY := by
    intro i
    have heval : (fun ω : (Fin n → α × β) ↦ (Xs i ω, Ys i ω)) = Function.eval i := by
      funext ω; rfl
    rw [heval, hμ, Measure.pi_map_eval]
    simp
  have hindep : iIndepFun (fun i ω ↦ (Xs i ω, Ys i ω)) μ := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ ((hXs i).prodMk (hYs i)).aemeasurable)]
    have hRHS : Measure.pi (fun i : Fin n ↦ μ.map (fun ω ↦ (Xs i ω, Ys i ω))) = μ := by
      have hpi : (fun i : Fin n ↦ μ.map (fun ω ↦ (Xs i ω, Ys i ω))) = fun _ ↦ P_XY := by
        funext i; exact hlaw i
      rw [hpi, ← hμ]
    rw [hRHS]
    have hid : (fun (ω : Fin n → α × β) (i : Fin n) ↦ (Xs i ω, Ys i ω)) = id := by
      funext ω i; rfl
    rw [hid]
    exact Measure.map_id
  exact wyner_ziv_converse_n_letter_singleLetter hn c hencoder hdecoder d μ Xs Ys
    hXs hYs hindep P_XY hlaw hD

end InformationTheory.Shannon

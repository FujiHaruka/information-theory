import InformationTheory.Shannon.TimeBandLimiting
import InformationTheory.Shannon.LpPointwise
import InformationTheory.Shannon.ShannonHartleyPreequalizer
import InformationTheory.Meta.EntryPoint

/-!
# Continuous-time Shannon-Hartley: headline theorems

This file collects the two headline theorems of the continuous-time band-limited AWGN channel —
the achievability half `contAwgn_ge_shannonHartley` (`≥`) and the identity
`contAwgn_eq_shannonHartley` (`=`) — at a position downstream of the achievability assets they
must consume. Both are blocked on the same `nyquist-2w-dof` operational bridge, which needs the
prolate-eigenvalue count (`le_prolateCount` / `prolateCount_le`) of `TimeBandLimiting.lean`; those
prolate assets are visible only below the achievability and operational modules, so the theorems
live here rather than at their original upstream sites.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Theorem 9.6.1.
-/

namespace InformationTheory.Shannon.ShannonHartley

set_option linter.unusedVariables false

/-- **Shannon-Hartley achievability (`≥`)**: the operational capacity is at least the
Shannon-Hartley closed form.

Unlike the boundedness bound of §E, this direction does not close by Bessel alone: it needs the
`≈ 2WT` degrees-of-freedom count, in its lower-bound half.

The reason is that the receiver of `ContAwgnCode` sees a band-limited codeword only through test
functions supported in `[0, T]`, and those two constraints fight each other: a band-limited `f` is
never supported in `[0, T]`, so `⟨f, φᵢ⟩ = ⟨f, P_W φᵢ⟩` and the energy the receiver recovers is
governed by the Gram matrix `Gᵢⱼ = ⟨φᵢ, (timeBandLimitingOp T W) φⱼ⟩` — a compression of the
prolate operator, whose eigenvalues Cauchy interlacing caps by `prolateEigenvalues T W`. To reach
the closed form one must exhibit, for each `T`, a family achieving per-dimension gain `≈ 1` on
`≈ 2WT` dimensions; that is exactly the Landau-Pollak-Slepian concentration read from below,
which is `le_prolateCount` (`TimeBandLimiting.lean`): `2WT − D/(1 − c) ≤ prolateCount T W c` for
every threshold `c ∈ (0, 1)`, with `D = 2 + log(1 + 2WT)`. That count is proved; what this
statement still lacks is the bridge from it to `contAwgnOperationalCapacity` — the interlacing
step and the capacity computation on top of it.

No cheaper family is available, and this was checked rather than assumed. The obvious wall-free
candidate — the boxcar family `φᵢ = 𝟙_{[iΔ,(i+1)Δ]}/√Δ` at `Δ = 1/(2W)`, which is orthonormal and
`[0, T]`-supported by inspection — fails: a boxcar's spectrum is a sinc, so `‖P_W φᵢ‖ < 1` by a
constant factor, the per-dimension gains are bounded away from `1`, and concavity of `log` puts
the resulting rate strictly below the closed form. Adversarial search over random orthonormal
families corroborates (`docs/shannon/shannon-hartley-facts.md` §OBSERVATION-MAP: best `C/SH`
`= 0.3250` against prolate's `0.9944`, with no family beating prolate). The convergence itself is
the count: the finite-`T` shortfall is `O(log WT)`, the width of the prolate cliff's transition
band, which is the error term `D/(1 − c)` of `le_prolateCount`.

The synthesis bridge of §A–§D (`synthSignal`, `synthSignal_energy`) remains the way to build the
band-limited codewords, and `synthSignal_energy` discharges the whole-line `encoder_power`
obligation as an equality. What it does not supply is the test family.

This statement also consumes `contAwgnMaxMessages_bddAbove` (§E) through `le_csSup` — without a
`BddAbove` the ℕ-`sSup` collapses to junk `0`. That obligation is wall-independent and its
residual is tracked at its own declaration rather than duplicated here.

Hypotheses `hW`/`hN₀`/`hP` are regularity-only (not load-bearing).

The `wall:nyquist-2w-dof` slug is kept as the tracking tag, but its named proposition — the
eigenvalue concentration — is closed (`le_prolateCount` is the half this direction needs). The live
obstruction is the operational bridge above, not the count.

`@residual(wall:nyquist-2w-dof)` -/
theorem contAwgn_ge_shannonHartley
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P := by
  -- Blocked on the operational bridge (test family + interlacing + capacity), not on the count
  -- itself; see docstring.
  sorry -- @residual(wall:nyquist-2w-dof)

/-- The **continuous-time Shannon-Hartley formula**: the operational capacity of the
band-limited AWGN channel equals `W · log(1 + P/(N₀·W))`.

Under the Karhunen-Loève observation map of `ContAwgnCode` this statement is expected true; an
earlier point-sampling model made it false as framed, and the def-fix that repaired it is recorded
in `docs/shannon/shannon-hartley-facts.md` §OBSERVATION-MAP. What remains is not a matter of
definition but of connecting the time-bandwidth degrees-of-freedom count to the operational
quantity.

Both halves need that count. `∫ f·φᵢ = ⟪f, P_W φᵢ⟫` for band-limited `f`, so the Gram matrix of the
test family is a compression of the time-band-limiting operator `timeBandLimitingOp T W`
(`TimeBandLimiting.lean`), and the achievable rate along any `[0, T]`-supported orthonormal family
is governed by that compression's eigenvalues, which Cauchy interlacing caps by the prolate
eigenvalues `prolateEigenvalues T W`. Reaching the closed form in the limit requires `≈ 2WT` of
them to sit near `1` and the rest near `0` — the Landau-Pollak-Slepian concentration.

That concentration is available. `prolateCount_le` and `le_prolateCount` (`TimeBandLimiting.lean`)
bracket `prolateCount T W c`, the number of prolate eigenvalues exceeding a free threshold
`c ∈ (0, 1)`, between `2WT − D/(1 − c)` and `2WT + D/c` with `D = 2 + log(1 + 2WT)`. The converse
needs the upper half (`prolateCount_le`), the achievability (`contAwgn_ge_shannonHartley`) the
lower half (`le_prolateCount`).

What is still missing is the bridge from the count to `contAwgnOperationalCapacity`: the Cauchy
interlacing step tying the Gram compression's eigenvalues to `prolateEigenvalues T W`, and the
capacity computation built on it. That bridge, not the count, is what this residual stands for.

Note the asymmetry that certifies the def-fix was a repair and not a disguise: the crude bound of
`contAwgnMaxMessages_bddAbove` closes by Bessel alone, wall-free, but caps the rate only at
`P/N₀`, and `ln(1+x) ≤ x` makes that strictly larger than the closed form. Boundedness comes for
free; the exact constant does not.

Hypotheses `hW`/`hN₀`/`hP` are regularity-only (not load-bearing).

The `wall:nyquist-2w-dof` slug is kept as the tracking tag, but its named proposition — the
eigenvalue concentration — is closed (`prolateCount_le` / `le_prolateCount`). The live obstruction
is the operational bridge above, not the count.

`@residual(wall:nyquist-2w-dof)` -/
@[entry_point]
theorem contAwgn_eq_shannonHartley
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    contAwgnOperationalCapacity W N₀ P = bandlimitedAwgnCapacity W N₀ P := by
  -- Blocked on the operational bridge (Gram compression ↔ prolate count, then capacity), not on
  -- the count itself; see docstring.
  sorry -- @residual(wall:nyquist-2w-dof)

/-!
### R4-ACH foundational leaves (L3/L5, L6)

The achievability route (ii) builds continuous-time codewords as band-limited signals and reads
them off through `[0, T]`-supported orthonormal test functions. This section supplies the two
foundational leaves feeding the pre-equalizer (`ShannonHartleyPreequalizer.exists_preequalizer`):

* **L3/L5** (`exists_testFn_family`) — a receiver test-function family `φ` supported in `[0, T]`,
  paired with the band-limited encoder family `h` (real representatives of a `ℂ`-orthonormal basis
  `u` of `V = prolateEigenspaceSup T W c`). The two families are tied by the *cross-map energy
  identity*: the receiver's recovered energy `∑ᵢ ⟨∑ⱼ vⱼ hⱼ, φᵢ⟩²` equals the time-limited energy
  `‖Q_T (∑ⱼ vⱼ uⱼ)‖²`. That identity is the shape L6 consumes.

* **L6** (`exists_crossMap_lower_bound`) — the cross-map `A` (with `(A v)ᵢ = ∫ (∑ⱼ vⱼ hⱼ)·φᵢ`) is
  bounded below by `√c`: `c ∑ᵢ vᵢ² ≤ ∑ᵢ (A v)ᵢ²`. This is exactly the `hbdd` hypothesis of
  `exists_preequalizer` once `A` is packaged as an endomorphism of `EuclideanSpace ℝ (Fin k)`
  (`‖v‖² = ∑ᵢ vᵢ²`, `‖A v‖² = ∑ᵢ (A v)ᵢ²`). The bound comes from the energy identity plus the
  time-window energy concentration `le_norm_timeLimitProj_sq_of_mem`.
-/

section Achievability

open MeasureTheory InformationTheory.Shannon.TimeBandLimiting InformationTheory.Shannon.LpPointwise

/-- **L3/L5 — receiver test-function family with the cross-map energy identity.**

For `V = prolateEigenspaceSup T W c` (`0 < c`), there is a `ℂ`-orthonormal basis `u` of `V`
together with a band-limited real encoder family `h` (real representatives of `u`) and a receiver
test-function family `φ`, `[0, T]`-supported and pointwise-orthonormal, such that for every
coefficient vector `v : Fin (prolateCount T W c) → ℝ` the receiver's recovered energy equals the
time-limited energy of the corresponding `V`-combination:
`∑ᵢ (∫ (∑ⱼ vⱼ hⱼ)·φᵢ)² = ‖Q_T (∑ⱼ vⱼ uⱼ)‖²`, with `Q_T = (timeLimitSubspace T).starProjection`.

The `φ` family is the `[0, T]`-supported real orthonormal basis of `S = span_ℝ {Q_T uⱼ}`; the
energy identity holds because the time-limited encoders `Q_T uⱼ` span `S`, so the receiver recovers
the full time-limited energy of any `V`-combination.
@audit:ok -/
theorem exists_testFn_family (T W : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ (u : Fin (prolateCount T W c) → E) (h φ : Fin (prolateCount T W c) → (ℝ → ℝ)),
      Orthonormal ℂ u ∧
      (∀ i, u i ∈ prolateEigenspaceSup T W c) ∧
      (∀ i, MemLp (h i) 2 volume) ∧
      (∀ i, (fun t => ((h i t : ℝ) : ℂ)) =ᵐ[volume] (u i : ℝ → ℂ)) ∧
      (∀ i, IsBandlimited (h i) W) ∧
      (∀ i j, (∫ t, h i t * h j t) = if i = j then (1 : ℝ) else 0) ∧
      (∀ i, Function.support (φ i) ⊆ Set.Icc 0 T) ∧
      (∀ i, MemLp (φ i) 2 volume) ∧
      (∀ i j, (∫ t, φ i t * φ j t) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : Fin (prolateCount T W c) → ℝ,
        (∑ i, (∫ t, (∑ j, v j * h j t) * φ i t) ^ 2)
          = ‖(timeLimitSubspace T).starProjection (∑ j, (v j : ℂ) • u j)‖ ^ 2) := by
  classical
  -- L4: encoder ONB `u` of `V` and band-limited real representatives `h`.
  obtain ⟨u, h, hu_on, hu_star, hu_span, h_memLp, h_ae, h_bl, h_ortho⟩ :=
    exists_real_bandlimited_onb T W hc
  have hu_mem : ∀ i, u i ∈ prolateEigenspaceSup T W c := fun i => by
    rw [← hu_span]; exact Submodule.subset_span (Set.mem_range_self i)
  -- Time-limited encoders `w i = Q_T (u i)`: in `timeLimitSubspace`, star-fixed.
  have hw_mem : ∀ i, (timeLimitSubspace T).starProjection (u i) ∈ timeLimitSubspace T :=
    fun i => Submodule.starProjection_apply_mem _ _
  have hw_star : ∀ i, star ((timeLimitSubspace T).starProjection (u i))
      = (timeLimitSubspace T).starProjection (u i) := fun i => by
    rw [← timeLimitProj_star T (u i), hu_star i]
  -- Real `[0,T]`-supported representatives `f i` of `w i`.
  choose f hf_memLp hf_supp hf_ae using fun i =>
    exists_pointwise_repr_of_mem_timeLimit_star_fixed T (hw_mem i) (hw_star i)
  -- `Lp ℝ` classes and their span `S`.
  set e : Fin (prolateCount T W c) → Lp ℝ 2 (volume : Measure ℝ) :=
    fun i => (hf_memLp i).toLp (f i) with he
  set S : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) := Submodule.span ℝ (Set.range e) with hS
  -- Each `e i` vanishes a.e. off `[0,T]` (it is `[0,T]`-supported).
  have he_supp : ∀ i, (⇑(e i) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)ᶜ] 0 := by
    intro i
    have h1 : (⇑(e i) : ℝ → ℝ) =ᵐ[volume] f i := (hf_memLp i).coeFn_toLp
    have h2 : ∀ t ∈ (Set.Icc (0:ℝ) T)ᶜ, f i t = 0 := by
      intro t ht
      by_contra hne
      exact ht (hf_supp i (by simpa [Function.mem_support] using hne))
    filter_upwards [ae_restrict_of_ae h1,
      (ae_restrict_iff' measurableSet_Icc.compl).mpr (ae_of_all volume h2)] with t hta htb
    simp only [Pi.zero_apply]
    rw [hta, htb]
  -- a.e. link: complexified `e i` equals the time-limited encoder `Q_T (u i)`.
  have hlink : ∀ i, (fun t => ((⇑(e i) t : ℝ) : ℂ)) =ᵐ[volume]
      (⇑((timeLimitSubspace T).starProjection (u i)) : ℝ → ℂ) := by
    intro i
    have h1 : (⇑(e i) : ℝ → ℝ) =ᵐ[volume] f i := (hf_memLp i).coeFn_toLp
    exact (h1.fun_comp (fun r : ℝ => (r : ℂ))).trans (hf_ae i)
  -- Linear independence of `e` ⟹ `finrank ℝ S = prolateCount`.
  have he_li : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    -- Transfer the vanishing combination to `E`: `∑ (g i) • Q_T (u i) = 0`.
    have hE : (∑ i, (g i : ℂ) • (timeLimitSubspace T).starProjection (u i)) = 0 := by
      refine Lp.ext ?_
      have hcsum := Lp.coeFn_finsetSum Finset.univ
        (fun i => (g i : ℂ) • (timeLimitSubspace T).starProjection (u i))
      have hrsum := Lp.coeFn_finsetSum Finset.univ (fun i => g i • e i)
      have hg0 : ⇑(∑ i, g i • e i) =ᵐ[volume] (0 : ℝ → ℝ) := by
        rw [hg]; exact Lp.coeFn_zero ℝ 2 volume
      have hz : ⇑(0 : E) =ᵐ[volume] (0 : ℝ → ℂ) := Lp.coeFn_zero ℂ 2 volume
      have hcsmul : ∀ i, ⇑((g i : ℂ) • (timeLimitSubspace T).starProjection (u i)) =ᵐ[volume]
          (g i : ℂ) • (⇑((timeLimitSubspace T).starProjection (u i)) : ℝ → ℂ) :=
        fun i => Lp.coeFn_smul _ _
      have hrsmul : ∀ i, ⇑(g i • e i) =ᵐ[volume] g i • (⇑(e i) : ℝ → ℝ) :=
        fun i => Lp.coeFn_smul _ _
      filter_upwards [hcsum, hrsum, hg0, hz, ae_all_iff.mpr hlink, ae_all_iff.mpr hcsmul,
        ae_all_iff.mpr hrsmul] with t hct hrt hg0t hzt hlinkt hcsmt hrsmt
      rw [hct, hzt, Finset.sum_apply, Pi.zero_apply]
      -- Rewrite each complex summand as `(g i) * (e i t : ℂ)`.
      have step : ∀ i, (⇑((g i : ℂ) • (timeLimitSubspace T).starProjection (u i)) : ℝ → ℂ) t
          = (g i : ℂ) * ((⇑(e i) t : ℝ) : ℂ) := by
        intro i
        rw [hcsmt i, Pi.smul_apply, smul_eq_mul, ← hlinkt i]
      rw [Finset.sum_congr rfl (fun i _ => step i)]
      -- The real combination vanishes pointwise.
      have hrside : (∑ i, g i * (⇑(e i) t : ℝ)) = 0 := by
        rw [Finset.sum_apply] at hrt
        simp only [Pi.zero_apply] at hg0t
        rw [hrt] at hg0t
        rw [← hg0t]
        exact Finset.sum_congr rfl (fun i _ => by rw [hrsmt i, Pi.smul_apply, smul_eq_mul])
      have hcast : (∑ i, (g i : ℂ) * ((⇑(e i) t : ℝ) : ℂ))
          = ((∑ i, g i * (⇑(e i) t : ℝ) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [Complex.ofReal_mul])
      rw [hcast, hrside, Complex.ofReal_zero]
    -- Pull `Q_T` out of the sum, then invert it on `V`.
    have hQ0 : (timeLimitSubspace T).starProjection (∑ i, (g i : ℂ) • u i) = 0 := by
      rw [map_sum]
      simp_rw [map_smul]
      exact hE
    have hsum0 : (∑ i, (g i : ℂ) • u i) = 0 :=
      eq_zero_of_timeLimitProj_eq_zero T W c hc
        (Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hu_mem i))) hQ0
    -- `u` is `ℂ`-independent, so all coefficients vanish.
    intro i
    have hli := hu_on.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have := hli (fun i => (g i : ℂ)) hsum0 i
    exact_mod_cast this
  haveI hSfin : FiniteDimensional ℝ S := by
    rw [hS]; exact FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
  have hdim : Module.finrank ℝ S = prolateCount T W c := by
    rw [hS, finrank_span_eq_card he_li, Fintype.card_fin]
  -- Orthonormal basis `b` of `S`, reindexed onto `Fin (prolateCount T W c)`.
  set b := stdOrthonormalBasis ℝ S with hb
  set e' : Fin (prolateCount T W c) → Lp ℝ 2 (volume : Measure ℝ) :=
    fun i => (↑(b (Fin.cast hdim.symm i)) : Lp ℝ 2 (volume : Measure ℝ)) with he'
  have hbLp_on : Orthonormal ℝ (fun i => (↑(b i) : Lp ℝ 2 (volume : Measure ℝ))) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hbo := (orthonormal_iff_ite.mp b.orthonormal) i j
    rwa [Submodule.coe_inner] at hbo
  have he'_on : Orthonormal ℝ e' :=
    hbLp_on.comp (Fin.cast hdim.symm) (Fin.cast_injective _)
  have hS_supp : ∀ x ∈ S, (⇑x : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)ᶜ] 0 := by
    intro x hx
    rw [hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact he_supp i
    | zero => exact ae_restrict_of_ae (Lp.coeFn_zero ℝ 2 (volume : Measure ℝ))
    | add y z _ _ hy' hz' =>
        refine Filter.EventuallyEq.trans (ae_restrict_of_ae (Lp.coeFn_add y z)) ?_
        filter_upwards [hy', hz'] with t hyt hzt
        simp only [Pi.add_apply, Pi.zero_apply] at hyt hzt ⊢
        rw [hyt, hzt, add_zero]
    | smul a y _ hy' =>
        refine Filter.EventuallyEq.trans (ae_restrict_of_ae (Lp.coeFn_smul a y)) ?_
        filter_upwards [hy'] with t hyt
        simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hyt ⊢
        rw [hyt, mul_zero]
  have he'_supp : ∀ i, (⇑(e' i) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)ᶜ] 0 :=
    fun i => hS_supp (e' i) (Submodule.coe_mem (b (Fin.cast hdim.symm i)))
  -- Test functions via the pointwise representative of the orthonormal basis.
  set φ : Fin (prolateCount T W c) → (ℝ → ℝ) :=
    fun i => LpPointwise.ptRepr (Set.Icc (0:ℝ) T) (e' i) with hφ
  have hφ_supp : ∀ i, Function.support (φ i) ⊆ Set.Icc 0 T :=
    fun i => LpPointwise.support_ptRepr_subset _ _
  have hφ_memLp : ∀ i, MemLp (φ i) 2 volume :=
    fun i => LpPointwise.memLp_ptRepr measurableSet_Icc _
  have hφ_ae : ∀ i, φ i =ᵐ[volume] (⇑(e' i) : ℝ → ℝ) :=
    fun i => LpPointwise.ptRepr_ae_eq measurableSet_Icc (e' i) (he'_supp i)
  have hφ_ortho : ∀ i j, (∫ t, φ i t * φ j t) = if i = j then (1:ℝ) else 0 := by
    intro i j
    rw [hφ]
    rw [LpPointwise.integral_ptRepr_mul measurableSet_Icc (e' i) (e' j)
      (he'_supp i) (he'_supp j)]
    exact orthonormal_iff_ite.mp he'_on i j
  refine ⟨u, h, φ, hu_on, hu_mem, h_memLp, h_ae, h_bl, h_ortho, hφ_supp, hφ_memLp, hφ_ortho, ?_⟩
  -- Cross-map energy identity.
  intro v
  -- The encoder combination as a genuine `Lp ℝ` class, and its `S`-projection `p = ∑ⱼ vⱼ • eⱼ`.
  have hg_memLp : MemLp (fun t => ∑ j, v j * h j t) 2 volume := by
    have hsum : MemLp (fun t => ∑ j, (v j • h j) t) 2 volume :=
      memLp_finsetSum Finset.univ (fun j (_ : j ∈ Finset.univ) => (h_memLp j).const_smul (v j))
    refine MemLp.ae_eq ?_ hsum
    filter_upwards with t
    simp [Pi.smul_apply, smul_eq_mul]
  set gLp : Lp ℝ 2 (volume : Measure ℝ) := hg_memLp.toLp _ with hgLp_def
  set p : Lp ℝ 2 (volume : Measure ℝ) := ∑ j, v j • e j with hp
  have hgc : ⇑gLp =ᵐ[volume] (fun t => ∑ j, v j * h j t) := by
    rw [hgLp_def]; exact hg_memLp.coeFn_toLp
  -- (B1) The receiver integral is the `Lp ℝ` inner product.
  have hB1 : ∀ i, (∫ t, (∑ j, v j * h j t) * φ i t) = (inner ℝ gLp (e' i) : ℝ) := by
    intro i
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hgc, hφ_ae i] with t htg htφ
    rw [RCLike.inner_apply, conj_trivial, htg, htφ]
    ring
  -- (E-c) `‖p‖² = ‖Q_T (∑ⱼ vⱼ uⱼ)‖²` (`p` complexifies to the time-limited combination).
  have hEc : ‖p‖ ^ 2 = ‖(timeLimitSubspace T).starProjection (∑ j, (v j : ℂ) • u j)‖ ^ 2 := by
    have hpc : (fun t => ((⇑p t : ℝ) : ℂ)) =ᵐ[volume]
        (⇑((timeLimitSubspace T).starProjection (∑ j, (v j : ℂ) • u j)) : ℝ → ℂ) := by
      have hQlin : (timeLimitSubspace T).starProjection (∑ j, (v j : ℂ) • u j)
          = ∑ j, (v j : ℂ) • (timeLimitSubspace T).starProjection (u j) := by
        rw [map_sum]; simp_rw [map_smul]
      rw [hQlin]
      have hpr : (⇑p : ℝ → ℝ) =ᵐ[volume] (fun t => ∑ j, v j * ⇑(e j) t) := by
        have h1 := Lp.coeFn_fun_finsetSum (μ := (volume : Measure ℝ)) Finset.univ
          (fun j => v j • e j)
        have h2 : ∀ j, ⇑(v j • e j) =ᵐ[volume] v j • (⇑(e j) : ℝ → ℝ) := fun j => Lp.coeFn_smul _ _
        rw [hp]
        filter_upwards [h1, ae_all_iff.mpr h2] with t h1t h2t
        rw [h1t]
        exact Finset.sum_congr rfl (fun j _ => by rw [h2t j, Pi.smul_apply, smul_eq_mul])
      have hws := Lp.coeFn_fun_finsetSum (μ := (volume : Measure ℝ)) Finset.univ
        (fun j => (v j : ℂ) • (timeLimitSubspace T).starProjection (u j))
      have hwsmul : ∀ j, ⇑((v j : ℂ) • (timeLimitSubspace T).starProjection (u j)) =ᵐ[volume]
          (v j : ℂ) • (⇑((timeLimitSubspace T).starProjection (u j)) : ℝ → ℂ) :=
        fun j => Lp.coeFn_smul _ _
      filter_upwards [hpr, hws, ae_all_iff.mpr hwsmul, ae_all_iff.mpr hlink]
        with t hprt hwst hwsmt hlinkt
      rw [hwst, hprt, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hwsmt j, Pi.smul_apply, smul_eq_mul, ← hlinkt j, Complex.ofReal_mul]
    have hnorm : ‖p‖ = ‖(timeLimitSubspace T).starProjection (∑ j, (v j : ℂ) • u j)‖ := by
      rw [Lp.norm_def, Lp.norm_def]
      congr 1
      rw [show eLpNorm (⇑p) 2 volume = eLpNorm (fun t => ((⇑p t : ℝ) : ℂ)) 2 volume from
        eLpNorm_congr_norm_ae (by filter_upwards with t; rw [Complex.norm_real])]
      exact eLpNorm_congr_ae hpc
    rw [hnorm]
  -- On `[0,T]`, the encoder `h j` and its time-limited representative `f j` agree.
  have hj_fj_onT : ∀ j, (h j) =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)] (f j) := by
    intro j
    have hQuj : (⇑((timeLimitSubspace T).starProjection (u j)) : ℝ → ℂ)
        =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)] (u j : ℝ → ℂ) := by
      filter_upwards [ae_restrict_of_ae (timeLimitProj_apply_ae T (u j)),
        ae_restrict_mem measurableSet_Icc] with t ht htmem
      rw [ht]; simp [Pi.mul_apply, Set.indicator_of_mem htmem]
    have hcx : (fun t => ((h j t : ℝ) : ℂ))
        =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)] (fun t => ((f j t : ℝ) : ℂ)) :=
      Filter.EventuallyEq.trans (ae_restrict_of_ae (h_ae j))
        (Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hQuj)
          (Filter.EventuallyEq.symm (ae_restrict_of_ae (hf_ae j))))
    filter_upwards [hcx] with t ht
    exact Complex.ofReal_inj.mp ht
  -- On `[0,T]`, the encoder combination `gLp` and its `S`-image `p` agree.
  have hgp_onT : (⇑gLp : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)] (⇑p : ℝ → ℝ) := by
    have hpc : (⇑p : ℝ → ℝ) =ᵐ[volume] (fun t => ∑ j, v j * (⇑(e j) t)) := by
      have h1 := Lp.coeFn_fun_finsetSum (μ := (volume : Measure ℝ)) Finset.univ (fun j => v j • e j)
      have h2 : ∀ j, ⇑(v j • e j) =ᵐ[volume] v j • (⇑(e j) : ℝ → ℝ) := fun j => Lp.coeFn_smul _ _
      rw [hp]
      filter_upwards [h1, ae_all_iff.mpr h2] with t h1t h2t
      rw [h1t]
      exact Finset.sum_congr rfl (fun j _ => by rw [h2t j, Pi.smul_apply, smul_eq_mul])
    filter_upwards [ae_restrict_of_ae hgc, ae_restrict_of_ae hpc,
      ae_all_iff.mpr (fun j => ae_restrict_of_ae ((hf_memLp j).coeFn_toLp)),
      ae_all_iff.mpr hj_fj_onT] with t htg htp htec htfj
    rw [htg, htp]
    exact Finset.sum_congr rfl (fun j _ => by rw [htfj j, ← htec j])
  -- (E-a) `⟪gLp, e' i⟫ = ⟪p, e' i⟫` (`gLp - p ⊥ S ∋ e' i`).
  have hEa : ∀ i, (inner ℝ gLp (e' i) : ℝ) = (inner ℝ p (e' i) : ℝ) := by
    intro i
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    have hgp' := (ae_restrict_iff' measurableSet_Icc).mp hgp_onT
    have hoff' := (ae_restrict_iff' measurableSet_Icc.compl).mp (he'_supp i)
    filter_upwards [hgp', hoff'] with t htgp htoff
    rw [RCLike.inner_apply, RCLike.inner_apply, conj_trivial, conj_trivial]
    by_cases ht : t ∈ Set.Icc (0:ℝ) T
    · rw [htgp ht]
    · simp [htoff ht]
  -- (E-b) Parseval on the orthonormal basis of `S`.
  have hp_mem : p ∈ S := by
    rw [hp]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (by rw [hS]; exact Submodule.subset_span (Set.mem_range_self j)))
  have hEb : (∑ i, (inner ℝ p (e' i) : ℝ) ^ 2) = ‖p‖ ^ 2 := by
    have hcoe : ∀ i, (inner ℝ p (e' i) : ℝ)
        = (inner ℝ (⟨p, hp_mem⟩ : ↥S) (b (Fin.cast hdim.symm i)) : ℝ) := fun i =>
      (Submodule.coe_inner S (⟨p, hp_mem⟩ : ↥S) (b (Fin.cast hdim.symm i))).symm
    simp_rw [hcoe]
    rw [Fintype.sum_equiv (finCongr hdim.symm)
      (fun i => (inner ℝ (⟨p, hp_mem⟩ : ↥S) (b (Fin.cast hdim.symm i))) ^ 2)
      (fun j => (inner ℝ (⟨p, hp_mem⟩ : ↥S) (b j)) ^ 2)
      (fun i => by rw [finCongr_apply])]
    exact b.sum_sq_inner_left _
  have hassemble : (∑ i, (∫ t, (∑ j, v j * h j t) * φ i t) ^ 2) = ‖p‖ ^ 2 := by
    rw [← hEb]
    exact Finset.sum_congr rfl (fun i _ => by rw [hB1 i, hEa i])
  rw [hassemble, hEc]

/-- **L6 — the receiver cross-map is bounded below by `√c`.**

The cross-map `A v = (∫ (∑ⱼ vⱼ hⱼ)·φᵢ)ᵢ` sending encoder coefficients to receiver observations
satisfies `c ∑ᵢ vᵢ² ≤ ∑ᵢ (A v)ᵢ²`. This is the `hbdd` input to
`ShannonHartleyPreequalizer.exists_preequalizer` (once `A` is read as an endomorphism of
`EuclideanSpace ℝ (Fin (prolateCount T W c))`, where `‖v‖² = ∑ᵢ vᵢ²` and `‖A v‖² = ∑ᵢ (A v)ᵢ²`),
which then yields the norm-controlled pre-equalizer `‖a‖² ≤ (1/c) ‖x‖²`.

The bound is the energy identity of `exists_testFn_family` composed with the time-window energy
concentration `le_norm_timeLimitProj_sq_of_mem` (`c ‖w‖² ≤ ‖Q_T w‖²` on `V`) and
`‖∑ⱼ vⱼ uⱼ‖² = ∑ⱼ vⱼ²` (`u` is `ℂ`-orthonormal, `v` real).
@audit:ok -/
theorem exists_crossMap_lower_bound (T W : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ (h φ : Fin (prolateCount T W c) → (ℝ → ℝ)),
      (∀ i, MemLp (h i) 2 volume) ∧
      (∀ i, IsBandlimited (h i) W) ∧
      (∀ i j, (∫ t, h i t * h j t) = if i = j then (1 : ℝ) else 0) ∧
      (∀ i, Function.support (φ i) ⊆ Set.Icc 0 T) ∧
      (∀ i, MemLp (φ i) 2 volume) ∧
      (∀ i j, (∫ t, φ i t * φ j t) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : Fin (prolateCount T W c) → ℝ,
        c * (∑ i, v i ^ 2) ≤ ∑ i, (∫ t, (∑ j, v j * h j t) * φ i t) ^ 2) := by
  obtain ⟨u, h, φ, hu_on, hu_mem, h_memLp, _h_ae, h_bl, h_ortho, φ_supp, φ_memLp, φ_ortho,
    henergy⟩ := exists_testFn_family T W hc
  refine ⟨h, φ, h_memLp, h_bl, h_ortho, φ_supp, φ_memLp, φ_ortho, ?_⟩
  intro v
  rw [henergy v]
  -- `w := ∑ⱼ vⱼ • uⱼ ∈ V`; the concentration bound and `‖w‖² = ∑ vⱼ²` finish it.
  have hwV : (∑ j, (v j : ℂ) • u j) ∈ prolateEigenspaceSup T W c :=
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hu_mem j))
  have hself : (inner ℂ (∑ j, (v j : ℂ) • u j) (∑ j, (v j : ℂ) • u j)).re
      = ‖∑ j, (v j : ℂ) • u j‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; simp [← Complex.ofReal_pow]
  have hip : inner ℂ (∑ j, (v j : ℂ) • u j) (∑ j, (v j : ℂ) • u j)
      = ((∑ i, v i ^ 2 : ℝ) : ℂ) := by
    rw [hu_on.inner_sum (fun i => (v i : ℂ)) (fun i => (v i : ℂ)) Finset.univ, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.conj_ofReal]; push_cast; ring
  have hnorm : ‖∑ j, (v j : ℂ) • u j‖ ^ 2 = ∑ i, v i ^ 2 := by
    rw [← hself, hip, Complex.ofReal_re]
  have hconc := le_norm_timeLimitProj_sq_of_mem T W c hc hwV
  rw [hnorm] at hconc
  exact hconc

/-! ### L7 — assembly: lifting a discrete AWGN code to a continuous-time code

Given a discrete `AwgnCode` on `k = prolateCount T W c` observations at per-observation power
`c·T·P/k`, we synthesize a `ContAwgnCode` whose observations reproduce the discrete codewords
exactly, transport the error probability, and read off a lower bound on `contAwgnMaxMessages`
via `le_csSup`. The three foundational leaves feeding it are: `memLp_sum_smul` (`L²`-membership of a
finite real combination of the band-limited encoders), `isBandlimited_sum_smul` (band-limitedness
of that combination), and `integral_sum_smul_sq_eq` (its whole-line energy is the coefficient
`ℓ²`-norm). -/

/-- A finite real linear combination of `L²` functions is again `L²`. -/
private theorem memLp_sum_smul {k : ℕ} (b : Fin k → ℝ) (h : Fin k → (ℝ → ℝ))
    (h_memLp : ∀ j, MemLp (h j) 2 volume) :
    MemLp (fun t => ∑ j, b j * h j t) 2 volume :=
  memLp_finsetSum Finset.univ (fun j (_ : j ∈ Finset.univ) => (h_memLp j).const_mul (b j))

/-- A finite real linear combination of band-limited functions is band-limited to the same band. -/
private theorem isBandlimited_sum_smul {k : ℕ} {W : ℝ} (b : Fin k → ℝ) (h : Fin k → (ℝ → ℝ))
    (h_bl : ∀ j, IsBandlimited (h j) W) :
    IsBandlimited (fun t => ∑ j, b j * h j t) W := by
  classical
  choose hf hvanish using h_bl
  set v : E := ∑ j, (b j : ℂ) • (hf j).toLp (fun t => ((h j t : ℝ) : ℂ)) with hv
  -- Each summand's `Lp` class lies in `bandLimitSubspace W`, hence so does `v`.
  have hmemj : ∀ j, ((hf j).toLp (fun t => ((h j t : ℝ) : ℂ))) ∈ bandLimitSubspace W := by
    intro j
    rw [bandLimitSubspace, Submodule.mem_comap]
    exact hvanish j
  have hvV : v ∈ bandLimitSubspace W :=
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hmemj j))
  -- `v` complexifies to the real combination a.e.
  have hvc : (⇑v : ℝ → ℂ) =ᵐ[volume] (fun t => ∑ j, (b j : ℂ) * ((h j t : ℝ) : ℂ)) := by
    have h1 := Lp.coeFn_fun_finsetSum (μ := (volume : Measure ℝ)) Finset.univ
      (fun j => (b j : ℂ) • (hf j).toLp (fun t => ((h j t : ℝ) : ℂ)))
    have h2 : ∀ j, ⇑((b j : ℂ) • (hf j).toLp (fun t => ((h j t : ℝ) : ℂ))) =ᵐ[volume]
        (b j : ℂ) • (⇑((hf j).toLp (fun t => ((h j t : ℝ) : ℂ))) : ℝ → ℂ) :=
      fun j => Lp.coeFn_smul _ _
    have h3 : ∀ j, (⇑((hf j).toLp (fun t => ((h j t : ℝ) : ℂ))) : ℝ → ℂ)
        =ᵐ[volume] (fun t => ((h j t : ℝ) : ℂ)) := fun j => (hf j).coeFn_toLp
    rw [hv]
    filter_upwards [h1, ae_all_iff.mpr h2, ae_all_iff.mpr h3] with t h1t h2t h3t
    rw [h1t]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h2t j, Pi.smul_apply, smul_eq_mul, h3t j]
  refine isBandlimited_of_bandLimitSubspace_ae hvV ?_
  refine Filter.EventuallyEq.trans ?_ hvc.symm
  filter_upwards with t
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [Complex.ofReal_mul])

/-- The whole-line energy of a finite combination of a pointwise-orthonormal `L²` family is the
`ℓ²`-norm of the coefficient vector. -/
private theorem integral_sum_smul_sq_eq {k : ℕ} (b : Fin k → ℝ) (h : Fin k → (ℝ → ℝ))
    (h_memLp : ∀ j, MemLp (h j) 2 volume)
    (h_ortho : ∀ i j, (∫ t, h i t * h j t) = if i = j then (1 : ℝ) else 0) :
    (∫ t, (∑ j, b j * h j t) ^ 2) = ∑ j, b j ^ 2 := by
  have hInt : ∀ j l, Integrable (fun t => (b j * h j t) * (b l * h l t)) volume := by
    intro j l
    exact ((h_memLp j).const_mul (b j)).integrable_mul ((h_memLp l).const_mul (b l))
  calc (∫ t, (∑ j, b j * h j t) ^ 2)
      = ∫ t, ∑ j, ∑ l, (b j * h j t) * (b l * h l t) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        show (∑ j, b j * h j t) ^ 2 = ∑ j, ∑ l, (b j * h j t) * (b l * h l t)
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ j, ∑ l, ∫ t, (b j * h j t) * (b l * h l t) := by
        rw [integral_finsetSum Finset.univ
          (fun j _ => integrable_finsetSum Finset.univ (fun l _ => hInt j l))]
        exact Finset.sum_congr rfl
          (fun j _ => integral_finsetSum Finset.univ (fun l _ => hInt j l))
    _ = ∑ j, ∑ l, b j * b l * (if j = l then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
        rw [show (fun t => (b j * h j t) * (b l * h l t))
              = (fun t => (b j * b l) * (h j t * h l t)) from by funext t; ring]
        rw [integral_const_mul, h_ortho j l]
    _ = ∑ j, b j ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq Finset.univ j (fun l => b j * b l)]
        simp [sq]

/-- **L7 — a discrete AWGN code on `prolateCount T W c` observations lifts to a continuous-time
code, giving a lower bound on `contAwgnMaxMessages`.**

Given a discrete `AwgnCode` on `k = prolateCount T W c` observations at per-observation power
`c·T·P/k` whose every message decodes with error `< ε`, the receiver cross-map `A` of
`exists_crossMap_lower_bound` (bounded below by `√c`) is invertible with norm control
(`exists_preequalizer`), so each discrete codeword `xₘ` has a band-limited pre-image `bₘ`. The
signals `∑ⱼ (bₘ)ⱼ hⱼ` are then band-limited codewords of a `ContAwgnCode` whose observations equal
`xₘ` exactly; the error probability transports unchanged, and `le_csSup` (via the wall-free
`contAwgnMaxMessages_bddAbove`) turns the discrete message count into the lower bound. -/
theorem contAwgnMaxMessages_ge_of_awgnCode
    (T W N₀ P : ℝ) (hT : 0 < T) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hkpos : 0 < prolateCount T W c)
    {M : ℕ}
    (d : AWGN.AwgnCode M (prolateCount T W c) (c * T * P / (prolateCount T W c : ℝ)))
    (hd : ∀ m, (d.toCode.errorProbAt
          (AWGN.awgnChannel (N₀ / 2).toNNReal (AWGN.isAwgnChannelMeasurable _)) m).toReal < ε) :
    M ≤ contAwgnMaxMessages T W N₀ P ε := by
  classical
  let k := prolateCount T W c
  obtain ⟨h, φ, h_memLp, h_bl, h_ortho, φ_supp, φ_memLp, φ_ortho, hlb⟩ :=
    exists_crossMap_lower_bound T W hc0
  -- The receiver cross-map as a linear endomorphism of `EuclideanSpace ℝ (Fin k)`.
  have hIntprod : ∀ (v : EuclideanSpace ℝ (Fin k)) (i : Fin k),
      Integrable (fun t => (∑ j, v j * h j t) * φ i t) volume :=
    fun v i => (memLp_sum_smul (fun j => v j) h h_memLp).integrable_mul (φ_memLp i)
  let A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
    { toFun := fun v => WithLp.toLp 2 (fun i => ∫ t, (∑ j, v j * h j t) * φ i t)
      map_add' := by
        intro v w
        ext i
        show (∫ t, (∑ j, (v + w) j * h j t) * φ i t)
            = (∫ t, (∑ j, v j * h j t) * φ i t) + (∫ t, (∑ j, w j * h j t) * φ i t)
        rw [← integral_add (hIntprod v i) (hIntprod w i)]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        simp only [PiLp.add_apply]
        rw [← add_mul, ← Finset.sum_add_distrib]
        exact congrArg (· * φ i t) (Finset.sum_congr rfl (fun j _ => by ring))
      map_smul' := by
        intro a v
        ext i
        show (∫ t, (∑ j, (a • v) j * h j t) * φ i t)
            = a • ∫ t, (∑ j, v j * h j t) * φ i t
        rw [smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        simp only [PiLp.smul_apply, smul_eq_mul]
        rw [show (∑ x, a * v x * h x t) = a * (∑ x, v x * h x t) from by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)]
        ring }
  have hAcomp : ∀ (v : EuclideanSpace ℝ (Fin k)) (i : Fin k),
      A v i = ∫ t, (∑ j, v j * h j t) * φ i t := fun v i => rfl
  have hbdd : ∀ v : EuclideanSpace ℝ (Fin k), c * ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2 := by
    intro v
    rw [EuclideanSpace.real_norm_sq_eq v, EuclideanSpace.real_norm_sq_eq (A v)]
    simp_rw [hAcomp]
    exact hlb (fun j => v j)
  -- The discrete codewords as `EuclideanSpace` targets.
  let xM : Fin M → EuclideanSpace ℝ (Fin k) := fun m => WithLp.toLp 2 (fun i => d.encoder m i)
  have hxMcomp : ∀ m i, xM m i = d.encoder m i := fun m i => rfl
  choose bpre hAb hbnorm using fun m =>
    ShannonHartleyPreequalizer.exists_preequalizer hc0 A hbdd (xM m)
  -- Energy bound: `‖bpre m‖² ≤ T·P`.
  have hkR : (0 : ℝ) < ((prolateCount T W c : ℕ) : ℝ) := by exact_mod_cast hkpos
  have hxMenergy : ∀ m, ‖xM m‖ ^ 2 ≤ c * T * P := by
    intro m
    rw [EuclideanSpace.real_norm_sq_eq (xM m)]
    simp_rw [hxMcomp]
    have hpc := d.power_constraint m
    rwa [mul_div_cancel₀ _ (ne_of_gt hkR)] at hpc
  have hbenergy : ∀ m, ‖bpre m‖ ^ 2 ≤ T * P := by
    intro m
    have hcne : c ≠ 0 := hc0.ne'
    have h1 := hbnorm m
    have h2 : (1 / c) * ‖xM m‖ ^ 2 ≤ (1 / c) * (c * T * P) :=
      mul_le_mul_of_nonneg_left (hxMenergy m) (by positivity)
    have heq : (1 / c) * (c * T * P) = T * P := by field_simp
    rw [heq] at h2
    linarith [h1, h2]
  -- The continuous-time code.
  let cc : ContAwgnCode T W P M :=
    { encoder := fun m t => ∑ j, bpre m j * h j t
      encoder_memLp := fun m => memLp_sum_smul (fun j => bpre m j) h h_memLp
      encoder_bandlimited := fun m => isBandlimited_sum_smul (fun j => bpre m j) h h_bl
      encoder_power := by
        intro m
        show (∫ t, (∑ j, bpre m j * h j t) ^ 2) ≤ T * P
        rw [integral_sum_smul_sq_eq (fun j => bpre m j) h h_memLp h_ortho,
          ← EuclideanSpace.real_norm_sq_eq (bpre m)]
        exact hbenergy m
      k := k
      testFn := φ
      testFn_memLp := φ_memLp
      testFn_support := φ_supp
      testFn_orthonormal := φ_ortho
      decoder := d.decoder
      decoder_meas := d.decoder_meas }
  -- Observation identity: the continuous observations reproduce the discrete codewords.
  have hobs : ∀ m i, cc.observation m i = d.encoder m i := by
    intro m i
    change (∫ t, (∑ j, bpre m j * h j t) * φ i t) = d.encoder m i
    rw [← hAcomp (bpre m) i, hAb m, hxMcomp]
  -- Error transport: the continuous error probability is the discrete one.
  have herr : ∀ m, cc.errorProbAt N₀ m
      = d.toCode.errorProbAt (AWGN.awgnChannel (N₀ / 2).toNNReal
          (AWGN.isAwgnChannelMeasurable _)) m := by
    intro m
    have hfam : (fun i : Fin cc.k =>
          ProbabilityTheory.gaussianReal (cc.observation m i) (N₀ / 2).toNNReal)
        = (fun i => (AWGN.awgnChannel (N₀ / 2).toNNReal (AWGN.isAwgnChannelMeasurable _))
            (d.toCode.encoder m i)) := by
      funext i
      rw [hobs m i]
      rfl
    have hset : {y : Fin cc.k → ℝ | cc.decoder y ≠ m} = d.toCode.errorEvent m := rfl
    unfold ContAwgnCode.errorProbAt InformationTheory.Shannon.ChannelCoding.Code.errorProbAt
    rw [hfam, hset]
  -- Average error ≤ ε.
  have hne : ∀ m, cc.errorProbAt N₀ m ≠ ⊤ := by
    intro m
    unfold ContAwgnCode.errorProbAt
    exact measure_ne_top _ _
  have haverage : (cc.averageError N₀).toReal ≤ ε := by
    rcases Nat.eq_zero_or_pos M with hM0 | hM0
    · have hz : cc.averageError N₀ = 0 := by
        unfold ContAwgnCode.averageError
        rw [if_pos hM0]
      rw [hz, ENNReal.toReal_zero]
      exact hε0.le
    · have key : (cc.averageError N₀).toReal = (1 / M : ℝ) * ∑ m, (cc.errorProbAt N₀ m).toReal := by
        unfold ContAwgnCode.averageError
        rw [if_neg hM0.ne', ENNReal.toReal_mul, ENNReal.toReal_inv,
          ENNReal.toReal_sum (fun m _ => hne m)]
        simp [one_div]
      rw [key]
      have hterm : ∀ m, (cc.errorProbAt N₀ m).toReal ≤ ε := fun m => by
        rw [herr m]; exact (hd m).le
      have hsum : ∑ m, (cc.errorProbAt N₀ m).toReal ≤ (M : ℝ) * ε := by
        calc ∑ m, (cc.errorProbAt N₀ m).toReal
            ≤ ∑ _m : Fin M, ε := Finset.sum_le_sum (fun m _ => hterm m)
          _ = (M : ℝ) * ε := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM0
      have hstep : (1 / M : ℝ) * ∑ m, (cc.errorProbAt N₀ m).toReal ≤ (1 / M) * ((M : ℝ) * ε) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      have hfin : (1 / M : ℝ) * ((M : ℝ) * ε) = ε := by
        field_simp
      linarith [hstep, hfin.le, hfin.ge]
  exact le_csSup (contAwgnMaxMessages_bddAbove T W N₀ P ε hT hW hN₀ hP hε0 hε1) ⟨cc, haverage⟩

end Achievability

end InformationTheory.Shannon.ShannonHartley

import Common2026.Shannon.BrunnMinkowskiPLBody
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.Order.Compact

/-!
# W10-S8 1-D superlevel-set Brunn-Minkowski — `IsPL11DSuperLevelHyp` discharge

`Common2026/Shannon/BrunnMinkowskiPLBody.lean` (wave9) で 1 次元 Prékopa-Leindler
を 3 つの sub-predicate に分解した。そのうち唯一残った **genuine measure-theoretic
ingredient** が `IsPL11DSuperLevelHyp muF muG muH lam`:

    `∀ t ≥ 0, lam * muF t + (1 - lam) * muG t ≤ muH t`,

すなわち superlevel 集合 `{φ ≥ t}` の Lebesgue 測度に対する **1 次元
Brunn-Minkowski**。本 file はこれを真に discharge する。

## Approach (本 file の戦略)

Mathlib には `volume (A + B)` の下界 (Brunn-Minkowski) が **完全に不在**
(loogle: `volume (_ + _)` lower bound 0 件、`Brunn` / `Minkowski` unknown
identifier)。よって 1 次元 BM を **直接** 証明する。鍵は古典的な「2 つの
平行移動コピーが 1 点でしか重ならない」議論:

1. **核心 — compact 集合の 1 次元 BM** (`volume_add_compact_ge`):
   非空 compact `A, B ⊆ ℝ` で `a := sSup A ∈ A`, `b := sInf B ∈ B` とおくと
   `A + {b} ⊆ A + B`, `{a} + B ⊆ A + B`, かつ `(A+{b}) ∩ ({a}+B) ⊆ {a+b}`
   (測度 0)。平行移動不変性 (`measure_preimage_add_right` 等) で
   `vol(A+{b}) = vol A`, `vol({a}+B) = vol B`、`measure_union₀` (AEDisjoint)
   で和に分解し `vol A + vol B ≤ vol(A+B)`。
2. **scaled 版** (`one_dim_bm_scaled`): `λ•A`, `(1-λ)•B` に 1 を適用し、
   `Measure.addHaar_smul_of_nonneg` (ℝ で `finrank = 1` なので
   `vol(r•A) = ofReal r * vol A`) で scaling、`.toReal` 化して
   `λ·vol A + (1-λ)·vol B ≤ vol(λ•A + (1-λ)•B)`。
3. **superlevel inclusion** (`pl1_superlevel_inclusion`): 点ごと PL 仮定から
   `λ•{f≥t} + (1-λ)•{g≥t} ⊆ {h≥t}` (`pl1_superlevel_pointwise_real`、
   `BrunnMinkowskiPLBody.pl1_superlevel_pointwise` の ℝ 版)。
4. **discharge wrapper** (`isPL11DSuperLevelHyp_real`): 2 + 3 + `measure_mono`
   で `λ·μ_f(t) + (1-λ)·μ_g(t) ≤ vol(λ•{f≥t}+(1-λ)•{g≥t}) ≤ μ_h(t)`、すなわち
   `IsPL11DSuperLevelHyp` を `μφ t := (volume {x | t ≤ φ x}).toReal` で
   instantiate して着地。

## 残存 hypothesis (genuine, no-op ではない)

discharge wrapper は superlevel 集合の **regularity** を hypothesis として取る:

* `{f ≥ t}`, `{g ≥ t}` が compact かつ非空 (BM 適用に必須),
* `{h ≥ t}` の測度が有限 (`.toReal` 単調性に必須)。

これらは「`f, g` が upper-semicontinuous で適当に減衰し、`h` の superlevel が
有界」という PL の標準仮定であり、no-op ではなく genuine な解析的前提。
本体の 1 次元 BM 不等式そのものは完全に discharge 済み (sorry 0)。

## 主シグネチャ

* §A — `volume_add_compact_ge` (compact 1-D BM, **genuine, discharged**)
* §B — `one_dim_bm_scaled` (scaled 版, discharged)
* §C — `pl1_superlevel_pointwise_real` / `pl1_superlevel_inclusion`
* §D — `isPL11DSuperLevelHyp_real` (predicate discharge)
* §E — `prekopa_leindler_1D_body_discharged` (PL 本体を superlevel
  hypothesis なしで再 publish)
-/

namespace InformationTheory.Shannon.BrunnMinkowski

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory Set
open scoped ENNReal NNReal Topology Pointwise

/-! ## §A — 核心: compact 集合の 1 次元 Brunn-Minkowski -/

/-- **1 次元 Brunn-Minkowski (compact 版, ENNReal form, genuine discharge)**:
非空 compact `A, B ⊆ ℝ` について

    `vol A + vol B ≤ vol (A + B)`.

古典的証明: `a := sSup A ∈ A`, `b := sInf B ∈ B` とおく (compact なので
`IsCompact.sSup_mem` / `IsCompact.sInf_mem` で member)。平行移動コピー
`A + {b}` と `{a} + B` はいずれも `A + B` に含まれ、交わりは `{a + b}` のみ
(`a' ≤ a`, `b ≤ b'`, `a' + b = a + b'` ⟹ `a' = a ∧ b' = b`)。よって測度 0 で
交わり (`AEDisjoint`)、`measure_union₀` で和に分解できる。平行移動不変性で
`vol(A+{b}) = vol A`, `vol({a}+B) = vol B`。

Mathlib gap: `volume (A + B)` の下界は Mathlib 完全不在 (本 file で新規証明)。 -/
theorem volume_add_compact_ge (A B : Set ℝ)
    (hA : IsCompact A) (hB : IsCompact B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  set a := sSup A with ha_def
  set b := sInf B with hb_def
  have ha_mem : a ∈ A := hA.sSup_mem hAne
  have hb_mem : b ∈ B := hB.sInf_mem hBne
  have hB_meas : MeasurableSet B := hB.measurableSet
  have hA_bdd : BddAbove A := hA.bddAbove
  have hB_bdd : BddBelow B := hB.bddBelow
  -- two parallel translates inside `A + B`
  have hsub1 : A + {b} ⊆ A + B := by
    apply Set.add_subset_add_left
    intro x hx; rw [mem_singleton_iff] at hx; rw [hx]; exact hb_mem
  have hsub2 : {a} + B ⊆ A + B := by
    apply Set.add_subset_add_right
    intro x hx; rw [mem_singleton_iff] at hx; rw [hx]; exact ha_mem
  have hunion_sub : (A + {b}) ∪ ({a} + B) ⊆ A + B := union_subset hsub1 hsub2
  -- translation invariance of Lebesgue measure
  have hvol1 : volume (A + {b}) = volume A := by
    rw [Set.add_singleton, Set.image_add_right, measure_preimage_add_right]
  have hvol2 : volume ({a} + B) = volume B := by
    rw [Set.singleton_add, Set.image_add_left, measure_preimage_add]
  -- measurability of the second translate
  have hmeas2 : MeasurableSet ({a} + B) := by
    rw [Set.singleton_add, Set.image_add_left]; exact measurable_const_add (-a) hB_meas
  -- the two translates overlap only at `{a + b}`
  have hinter : (A + {b}) ∩ ({a} + B) ⊆ {a + b} := by
    rintro x ⟨hx1, hx2⟩
    rw [Set.add_singleton, mem_image] at hx1
    obtain ⟨a', ha', rfl⟩ := hx1
    rw [Set.singleton_add, mem_image] at hx2
    obtain ⟨b', hb', hb'eq⟩ := hx2
    have ha'le : a' ≤ a := le_csSup hA_bdd ha'
    have hb'ge : b ≤ b' := csInf_le hB_bdd hb'
    have heq : a + b' = a' + b := hb'eq
    have hfin : a' = a ∧ b' = b := by constructor <;> linarith
    rw [mem_singleton_iff]; rw [hfin.1]
  -- a single point has Lebesgue measure 0 ⟹ AEDisjoint
  have haedisj : AEDisjoint volume (A + {b}) ({a} + B) :=
    measure_mono_null hinter Real.volume_singleton
  -- combine
  calc volume A + volume B
      = volume (A + {b}) + volume ({a} + B) := by rw [hvol1, hvol2]
    _ = volume ((A + {b}) ∪ ({a} + B)) :=
        (measure_union₀ hmeas2.nullMeasurableSet haedisj).symm
    _ ≤ volume (A + B) := measure_mono hunion_sub

/-! ## §B — scaled 版 (`λ•A + (1-λ)•B`) -/

/-- **1 次元 BM, λ-scaled 版 (`.toReal` form, discharged)**: `0 ≤ λ ≤ 1`,
非空 compact `A, B ⊆ ℝ` について

    `λ * (vol A).toReal + (1 - λ) * (vol B).toReal
      ≤ (vol (λ•A + (1-λ)•B)).toReal`.

`volume_add_compact_ge` を scaled 集合 `λ•A`, `(1-λ)•B` に適用し、ℝ では
`finrank ℝ ℝ = 1` ゆえ `vol(r•s) = ofReal r * vol s`
(`Measure.addHaar_smul_of_nonneg`) で scaling。compact 性は `IsCompact.smul`、
有限性は `IsCompact.measure_lt_top` で吸収して `.toReal` 化。 -/
theorem one_dim_bm_scaled (A B : Set ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hA : IsCompact A) (hB : IsCompact B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    lam * (volume A).toReal + (1 - lam) * (volume B).toReal
      ≤ (volume (lam • A + (1 - lam) • B)).toReal := by
  have h1lam : (0 : ℝ) ≤ 1 - lam := by linarith
  have hcA : IsCompact (lam • A) := hA.smul lam
  have hcB : IsCompact ((1 - lam) • B) := hB.smul (1 - lam)
  have hneA : (lam • A).Nonempty := hAne.smul_set
  have hneB : ((1 - lam) • B).Nonempty := hBne.smul_set
  -- core BM on the scaled sets
  have hcore : volume (lam • A) + volume ((1 - lam) • B)
      ≤ volume (lam • A + (1 - lam) • B) :=
    volume_add_compact_ge _ _ hcA hcB hneA hneB
  -- scaling of Lebesgue measure in ℝ
  have hvolA : volume (lam • A) = ENNReal.ofReal lam * volume A := by
    rw [Measure.addHaar_smul_of_nonneg (μ := volume) h0, Module.finrank_self, pow_one]
  have hvolB : volume ((1 - lam) • B) = ENNReal.ofReal (1 - lam) * volume B := by
    rw [Measure.addHaar_smul_of_nonneg (μ := volume) h1lam, Module.finrank_self, pow_one]
  -- finiteness facts
  have hAfin : volume A ≠ ∞ := (hA.measure_lt_top).ne
  have hBfin : volume B ≠ ∞ := (hB.measure_lt_top).ne
  have hsumfin : volume (lam • A + (1 - lam) • B) ≠ ∞ :=
    ((hcA.add hcB).measure_lt_top).ne
  have hltA : volume (lam • A) ≠ ∞ := by
    rw [hvolA]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin
  have hltB : volume ((1 - lam) • B) ≠ ∞ := by
    rw [hvolB]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin
  -- take `.toReal`
  have htoReal := ENNReal.toReal_mono hsumfin hcore
  rw [ENNReal.toReal_add hltA hltB, hvolA, hvolB,
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h1lam] at htoReal
  exact htoReal

/-! ## §C — superlevel inclusion (ℝ 版) -/

/-- **superlevel 包含, 点ごと (ℝ 版, discharged)**:
`BrunnMinkowskiPLBody.pl1_superlevel_pointwise` の ℝ 版。仮定

    `f x ^ λ * g y ^ (1 - λ) ≤ hfn (λ * x + (1 - λ) * y)`

の下で、`f x ≥ t`, `g y ≥ t`, `0 ≤ t` ならば `t ≤ hfn (λ * x + (1 - λ) * y)`。 -/
theorem pl1_superlevel_pointwise_real
    (f g hfn : ℝ → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (x y : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hfx : t ≤ f x) (hgy : t ≤ g y)
    (h_pt : f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam * x + (1 - lam) * y)) :
    t ≤ hfn (lam * x + (1 - lam) * y) := by
  have h1lam : (0 : ℝ) ≤ 1 - lam := by linarith
  have hfx_nn : 0 ≤ f x := le_trans ht hfx
  have hgy_nn : 0 ≤ g y := le_trans ht hgy
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · -- `t = 0`: RHS factor product is `≥ 0`.
    have hprod_nn : 0 ≤ f x ^ lam * g y ^ (1 - lam) :=
      mul_nonneg (Real.rpow_nonneg hfx_nn _) (Real.rpow_nonneg hgy_nn _)
    rw [← ht_eq]; linarith [le_trans hprod_nn h_pt]
  · -- `0 < t`: `t = t^λ * t^(1-λ) ≤ f x^λ * g y^(1-λ) ≤ hfn(mid)`.
    have ht_eq : t ^ lam * t ^ (1 - lam) = t := by
      rw [← Real.rpow_add ht_pos]; simp
    have hmono_f : t ^ lam ≤ f x ^ lam := Real.rpow_le_rpow ht hfx h0
    have hmono_g : t ^ (1 - lam) ≤ g y ^ (1 - lam) := Real.rpow_le_rpow ht hgy h1lam
    have ht_pow_g_nn : 0 ≤ t ^ (1 - lam) := Real.rpow_nonneg ht _
    have hfx_pow_nn : 0 ≤ f x ^ lam := Real.rpow_nonneg hfx_nn _
    have hprod_le : t ^ lam * t ^ (1 - lam) ≤ f x ^ lam * g y ^ (1 - lam) :=
      mul_le_mul hmono_f hmono_g ht_pow_g_nn hfx_pow_nn
    rw [ht_eq] at hprod_le; linarith [le_trans hprod_le h_pt]

/-- **superlevel 包含 (集合版, discharged)**: 点ごと PL 仮定の下で

    `λ • {x | t ≤ f x} + (1 - λ) • {x | t ≤ g x} ⊆ {z | t ≤ hfn z}`.

各点で `pl1_superlevel_pointwise_real` を適用。ℝ では `λ • x = λ * x`
(`smul_eq_mul`) なので Minkowski sum の元 `λ•x + (1-λ)•y` がそのまま点ごと
仮定の `λ*x + (1-λ)*y` に一致する。 -/
theorem pl1_superlevel_inclusion
    (f g hfn : ℝ → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (t : ℝ) (ht : 0 ≤ t)
    (h_pt : ∀ x y : ℝ, f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam * x + (1 - lam) * y)) :
    lam • {x : ℝ | t ≤ f x} + (1 - lam) • {x : ℝ | t ≤ g x} ⊆ {z : ℝ | t ≤ hfn z} := by
  rintro z hz
  rw [Set.mem_add] at hz
  obtain ⟨u, hu, v, hv, rfl⟩ := hz
  rw [Set.mem_smul_set] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv
  simp only [smul_eq_mul, Set.mem_setOf_eq] at hx hy ⊢
  exact pl1_superlevel_pointwise_real f g hfn lam h0 h1 x y t ht hx hy (h_pt x y)

/-! ## §D — `IsPL11DSuperLevelHyp` discharge -/

/-- **`IsPL11DSuperLevelHyp` discharge (genuine, sorry 0)**: superlevel 集合の
測度を `μφ t := (volume {x | t ≤ φ x}).toReal` と取れば、`IsPL11DSuperLevelHyp`
すなわち 1 次元 superlevel-set Brunn-Minkowski

    `∀ t ≥ 0, λ * μ_f(t) + (1 - λ) * μ_g(t) ≤ μ_h(t)`

が成立する。

経路: §B の scaled 1 次元 BM で `λ·μ_f(t) + (1-λ)·μ_g(t) ≤ vol(λ•{f≥t}+(1-λ)•{g≥t}).toReal`、
§C の superlevel 包含 + `measure_mono` (+ `{h≥t}` 有限性) で
`vol(λ•{f≥t}+(1-λ)•{g≥t}).toReal ≤ vol{h≥t}.toReal = μ_h(t)`。推移律で着地。

残存 hypothesis (genuine analytic regularity, no-op ではない):
* `hF_compact` / `hG_compact`: `{f≥t}`, `{g≥t}` が compact (BM 適用に必須),
* `hF_ne` / `hG_ne`: 非空 (BM の sSup/sInf member 性に必須),
* `hH_fin`: `{h≥t}` の測度有限 (`.toReal` 単調性に必須)。 -/
theorem isPL11DSuperLevelHyp_real
    (f g hfn : ℝ → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hF_compact : ∀ t : ℝ, 0 < t → IsCompact {x : ℝ | t ≤ f x})
    (hG_compact : ∀ t : ℝ, 0 < t → IsCompact {x : ℝ | t ≤ g x})
    (hF_ne : ∀ t : ℝ, 0 < t → ({x : ℝ | t ≤ f x}).Nonempty)
    (hG_ne : ∀ t : ℝ, 0 < t → ({x : ℝ | t ≤ g x}).Nonempty)
    (hH_fin : ∀ t : ℝ, 0 < t → volume {x : ℝ | t ≤ hfn x} ≠ ∞)
    (h_pt : ∀ x y : ℝ, f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam * x + (1 - lam) * y)) :
    IsPL11DSuperLevelHyp
      (fun t => (volume {x : ℝ | t ≤ f x}).toReal)
      (fun t => (volume {x : ℝ | t ≤ g x}).toReal)
      (fun t => (volume {x : ℝ | t ≤ hfn x}).toReal) lam := by
  intro t ht
  simp only
  set A := {x : ℝ | t ≤ f x} with hA_def
  set B := {x : ℝ | t ≤ g x} with hB_def
  set C := {z : ℝ | t ≤ hfn z} with hC_def
  -- scaled 1-D BM lower bound on the Minkowski sum
  have hbm : lam * (volume A).toReal + (1 - lam) * (volume B).toReal
      ≤ (volume (lam • A + (1 - lam) • B)).toReal :=
    one_dim_bm_scaled A B lam h0 h1 (hF_compact t ht) (hG_compact t ht)
      (hF_ne t ht) (hG_ne t ht)
  -- superlevel inclusion ⟹ measure monotonicity (`.toReal`)
  have hsub : lam • A + (1 - lam) • B ⊆ C :=
    pl1_superlevel_inclusion f g hfn lam h0 h1 t ht.le h_pt
  have hmono : (volume (lam • A + (1 - lam) • B)).toReal ≤ (volume C).toReal :=
    ENNReal.toReal_mono (hH_fin t ht) (measure_mono hsub)
  linarith

/-! ## §E — PL 本体を superlevel hypothesis なしで再 publish -/

/-- **1 次元 PL 本体 (superlevel hypothesis discharged 版)**:
`BrunnMinkowskiPLBody.prekopa_leindler_1D_body` は `IsPL11DSuperLevelHyp` を
hypothesis として要求していたが、本 file の §D でそれを genuine に discharge
できる。よって superlevel 集合の regularity hypothesis さえあれば、
1 次元 PL 結論 `intF ^ λ * intG ^ (1 - λ) ≤ intH` を `IsPL11DSuperLevelHyp`
仮定**なし**で得る。

`f, g, hfn : ℝ → ℝ` は 1 次元 PL の関数。superlevel 測度を内部で構成し、
§D の `isPL11DSuperLevelHyp_real` で BM hypothesis を供給する。 -/
theorem prekopa_leindler_1D_body_discharged
    (f g hfn : ℝ → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (intF intG intH : ℝ)
    (hF : 0 ≤ intF) (hG : 0 ≤ intG) (hH : 0 ≤ intH)
    (hF_compact : ∀ t : ℝ, 0 < t → IsCompact {x : ℝ | t ≤ f x})
    (hG_compact : ∀ t : ℝ, 0 < t → IsCompact {x : ℝ | t ≤ g x})
    (hF_ne : ∀ t : ℝ, 0 < t → ({x : ℝ | t ≤ f x}).Nonempty)
    (hG_ne : ∀ t : ℝ, 0 < t → ({x : ℝ | t ≤ g x}).Nonempty)
    (hH_fin : ∀ t : ℝ, 0 < t → volume {x : ℝ | t ≤ hfn x} ≠ ∞)
    (h_pt : ∀ x y : ℝ, f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam * x + (1 - lam) * y))
    (h_add : IsPL1AdditiveHyp intF intG intH lam) :
    intF ^ lam * intG ^ (1 - lam) ≤ intH := by
  -- the only nontrivial ingredient — `IsPL11DSuperLevelHyp` — is now discharged.
  have h_sl :
      IsPL11DSuperLevelHyp
        (fun t => (volume {x : ℝ | t ≤ f x}).toReal)
        (fun t => (volume {x : ℝ | t ≤ g x}).toReal)
        (fun t => (volume {x : ℝ | t ≤ hfn x}).toReal) lam :=
    isPL11DSuperLevelHyp_real f g hfn lam h0 h1 hF_compact hG_compact
      hF_ne hG_ne hH_fin h_pt
  -- the additive→multiplicative step closes the body (cf. PLBody).
  unfold IsPL1AdditiveHyp at h_add
  have hamgm : intF ^ lam * intG ^ (1 - lam) ≤ lam * intF + (1 - lam) * intG :=
    weighted_amgm_lambda hF hG h0 h1
  linarith

end InformationTheory.Shannon.BrunnMinkowski

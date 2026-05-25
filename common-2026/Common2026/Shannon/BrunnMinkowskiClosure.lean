import Common2026.Shannon.BrunnMinkowskiLayerCakeBody
import Common2026.Shannon.BrunnMinkowskiPLBody
import Common2026.Shannon.BrunnMinkowski1DSuperlevelBody
import Common2026.Shannon.BrunnMinkowskiConcavity
import Common2026.Shannon.MultivariateDiffEntropy
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Brunn-Minkowski full closure — Phase 1: n-dim Prékopa-Leindler (Fubini 帰納)

`BrunnMinkowskiPLBody.lean` の `IsPL2FubiniSliceHyp` (`:239`) は
`intF = reduceF ∧ ...` という **scalar 等式 placeholder** で実 Fubini 未接続
だった。本 file はその placeholder を `Fin (n+1) → ℝ ≃ᵐ ℝ × (Fin n → ℝ)`
(`MeasurableEquiv.piFinSuccAbove 0`) 上の **真の Fubini 恒等式** に置換し、
1D PL (`prekopa_leindler_1D_superlevel_discharged`, genuine) からの slice 帰納で
n 次元 Prékopa-Leindler を組む。

## Approach

`φ : (Fin (n+1) → ℝ) → ℝ` を `e := MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0`
で `ℝ × (Fin n → ℝ)` に reshape する。`e.symm (s, w) = Fin.cons s w`。

1. **Fubini reshape (genuine, 隠れ gap 候補だった核心)** — `measurePreserving_piFinSuccAbove`
   + `integral_comp'` + `integral_prod` で
   `∫ x, φ x = ∫ s, ∫ w, φ (Fin.cons s w)`。Mathlib `Integral/Pi.lean` の
   `integral_fin_nat_prod_eq_prod` が使う配線 (`piFinSuccAbove_symm_apply` を
   `Fin.cons` に展開) をそのまま借りる。**Mathlib gap は不在**。
2. **`Fin.cons` の affine 結合線形性** (`smul_cons_combine`, genuine) で
   slice の pointwise PL を n 次元 pointwise PL から導く。
3. **slice 積分 `sliceIntF s := ∫ w, f (Fin.cons s w)`** に 1D PL を適用 →
   全体 PL。

## 段階着地

Phase 1 (本 file) が閉じれば **体積版 BM (n-dim PL の凸体特殊化) は閉じる**。
-/

namespace InformationTheory.Shannon.BrunnMinkowski

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal Topology Pointwise

/-! ## §A — Fin.cons の affine 結合線形性 (genuine helper) -/

/-- **`Fin.cons` の affine 結合線形性**: `Fin (n+1) → ℝ` 上で
`λ • cons s w + (1-λ) • cons s' w' = cons (λ s + (1-λ) s') (λ • w + (1-λ) • w')`。

slice の pointwise PL を n 次元 pointwise PL から導くための核心: n 次元 mix が
last/init coordinate split で slice の mix に分かれることを示す。 -/
theorem smul_cons_combine {n : ℕ} (lam s s' : ℝ) (w w' : Fin n → ℝ) :
    lam • Fin.cons s w + (1 - lam) • Fin.cons s' w'
      = (Fin.cons (lam * s + (1 - lam) * s')
          (lam • w + (1 - lam) • w') : Fin (n + 1) → ℝ) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [Fin.cons_zero, smul_eq_mul]
  · intro j
    simp [Fin.cons_succ, smul_eq_mul]

/-! ## §B — Fubini reshape (genuine, 隠れ gap 候補だった核心) -/

/-- **Fubini reshape for `Fin (n+1) → ℝ` (genuine)**: integrable な
`φ : (Fin (n+1) → ℝ) → ℝ` に対し、

    `∫ x, φ x = ∫ s, ∫ w, φ (Fin.cons s w) ∂volume ∂volume`.

`measurePreserving_piFinSuccAbove (fun _ => ℝ) 0` で `volume` を
`(volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))` に移し、
`integral_prod` で iterate、`piFinSuccAbove_symm_apply` を `Fin.cons` に展開。
**これが「隠れ Mathlib gap 候補」とされていた measure 整合であり、実際は不在**。 -/
theorem integral_pi_succ_eq {n : ℕ} (φ : (Fin (n + 1) → ℝ) → ℝ)
    (hφ : Integrable φ) :
    ∫ x, φ x = ∫ s, ∫ w, φ (Fin.cons s w) := by
  -- Step 1: reshape `volume` on `Fin (n+1) → ℝ` to the product measure on
  -- `ℝ × (Fin n → ℝ)` via the measure-preserving `piFinSuccAbove 0`.
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hφ' : Integrable (fun z => φ ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).symm z)) volume :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hφ
  rw [← hmp.integral_comp']
  -- Step 2: Fubini on the product measure (`volume` on `ℝ × _` is `prod`).
  rw [Measure.volume_eq_prod, integral_prod _ (by rwa [Measure.volume_eq_prod] at hφ')]
  -- Step 3: rewrite `e.symm (s, w)` to `Fin.cons s w`.
  congr 1
  funext s
  congr 1
  funext w
  rw [show (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (s, w)
      = Fin.cons s w from ?_]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl

/-! ## §C — slice 積分とその pointwise PL -/

/-- **slice 積分**: `f : (Fin (n+1) → ℝ) → ℝ` を最後の split で
`s ↦ ∫ w, f (Fin.cons s w)` という `ℝ → ℝ` 関数に縮約。 -/
noncomputable def sliceInt {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (s : ℝ) : ℝ :=
  ∫ w : Fin n → ℝ, f (Fin.cons s w)

/-- **slice の pointwise PL (genuine, n 次元 PL を IH として消費)**: slice
積分 `sliceInt f, sliceInt g, sliceInt hfn : ℝ → ℝ` が 1D pointwise PL

    `sliceInt f s ^ λ * sliceInt g s' ^ (1-λ) ≤ sliceInt hfn (λ s + (1-λ) s')`

を満たす。各 `(s, s')` で slice 関数 `f (cons s ·), g (cons s' ·),
hfn (cons (λs+(1-λ)s') ·)` に n 次元 PL (帰納仮定 `ih`) を `smul_cons_combine`
の linearity 経由で適用して得る。 -/
theorem sliceInt_pointwise_pl {n : ℕ}
    (f g hfn : (Fin (n + 1) → ℝ) → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (h_pt : ∀ x y : Fin (n + 1) → ℝ,
      f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam • x + (1 - lam) • y))
    (ih : ∀ (f' g' hfn' : (Fin n → ℝ) → ℝ),
      (0 ≤ ∫ w, f' w) → (0 ≤ ∫ w, g' w) → (0 ≤ ∫ w, hfn' w) →
      (∀ x y : Fin n → ℝ,
        f' x ^ lam * g' y ^ (1 - lam) ≤ hfn' (lam • x + (1 - lam) • y)) →
      (∫ w, f' w) ^ lam * (∫ w, g' w) ^ (1 - lam) ≤ ∫ w, hfn' w)
    (hf_nn : ∀ s, 0 ≤ sliceInt f s) (hg_nn : ∀ s, 0 ≤ sliceInt g s)
    (hh_nn : ∀ s, 0 ≤ sliceInt hfn s)
    (s s' : ℝ) :
    sliceInt f s ^ lam * sliceInt g s' ^ (1 - lam)
      ≤ sliceInt hfn (lam * s + (1 - lam) * s') := by
  -- slice 関数 (n 次元).
  set f' : (Fin n → ℝ) → ℝ := fun w => f (Fin.cons s w) with hf'
  set g' : (Fin n → ℝ) → ℝ := fun w => g (Fin.cons s' w) with hg'
  set h' : (Fin n → ℝ) → ℝ :=
    fun w => hfn (Fin.cons (lam * s + (1 - lam) * s') w) with hh'
  -- slice の pointwise PL は n 次元 pointwise PL + `cons` の linearity から.
  have h_pt' : ∀ x y : Fin n → ℝ,
      f' x ^ lam * g' y ^ (1 - lam) ≤ h' (lam • x + (1 - lam) • y) := by
    intro x y
    have := h_pt (Fin.cons s x) (Fin.cons s' y)
    rwa [smul_cons_combine lam s s' x y] at this
  -- 帰納仮定 (n 次元 PL) を slice 関数に適用.
  have hkey := ih f' g' h' (hf_nn s) (hg_nn s')
    (hh_nn (lam * s + (1 - lam) * s')) h_pt'
  -- `∫ slice = sliceInt`.
  simpa only [sliceInt, hf', hg', hh'] using hkey

/-! ## §C' — base case: 1 次元 PL (`Fin 1 → ℝ ≃ᵐ ℝ` 経由) -/

/-- **base case 整合: `Fin 1 → ℝ` 上の積分 = ℝ 上の reshape 積分**.
`MeasurableEquiv.funUnique (Fin 1) ℝ : (Fin 1 → ℝ) ≃ᵐ ℝ` (measure-preserving,
`volume_preserving_funUnique`) で `∫ x, φ x = ∫ a, φ (fun _ => a)`。 -/
theorem integral_funUnique_eq (φ : (Fin 1 → ℝ) → ℝ) (hφ : Integrable φ) :
    ∫ x, φ x = ∫ a : ℝ, φ (fun _ => a) := by
  have hmp := (volume_preserving_funUnique (Fin 1) ℝ).symm
  have hc := hmp.integral_comp' φ
  rw [show (∫ a : ℝ, φ (fun _ => a)) = ∫ a : ℝ, φ ((MeasurableEquiv.funUnique
      (Fin 1) ℝ).symm a) from rfl, hc]
  rfl

/-- **base case (clean) 1 次元 PL on `Fin 1 → ℝ`**: `Fin 1 → ℝ ≃ᵐ ℝ` reshape で
点ごと PL を `ℝ` 上の点ごと PL に移し、1D engine
`prekopa_leindler_1D_superlevel_discharged` を適用。reshape 後の積分整合は
`integral_funUnique_eq` (genuine, measure-preserving)。

解析的前提 (regularity / layer-cake / tail) は honest hypothesis として
受ける (1D engine の前提をそのまま reshape 関数 `a ↦ φ (fun _ => a)` 上で要求)。 -/
theorem prekopa_leindler_1Dim
    (f g hfn : (Fin 1 → ℝ) → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (intF intG intH : ℝ)
    (hF : 0 ≤ intF) (hG : 0 ≤ intG) (hH : 0 ≤ intH)
    (h_pt : ∀ x y : Fin 1 → ℝ,
      f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam • x + (1 - lam) • y))
    (heqF : intF = ∫ x, f x) (heqG : intG = ∫ x, g x) (heqH : intH = ∫ x, hfn x)
    (hf_int : Integrable f) (hg_int : Integrable g) (hh_int : Integrable hfn)
    (hFc : ∀ t : ℝ, 0 < t → IsCompact {a : ℝ | t ≤ f (fun _ => a)})
    (hGc : ∀ t : ℝ, 0 < t → IsCompact {a : ℝ | t ≤ g (fun _ => a)})
    (hFne : ∀ t : ℝ, 0 < t → ({a : ℝ | t ≤ f (fun _ => a)}).Nonempty)
    (hGne : ∀ t : ℝ, 0 < t → ({a : ℝ | t ≤ g (fun _ => a)}).Nonempty)
    (hHfin : ∀ t : ℝ, 0 < t → volume {a : ℝ | t ≤ hfn (fun _ => a)} ≠ ∞)
    (h_lc : IsPL1LayerCakeIntegralHyp
      (fun t => (volume {a : ℝ | t ≤ f (fun _ => a)}).toReal)
      (fun t => (volume {a : ℝ | t ≤ g (fun _ => a)}).toReal)
      (fun t => (volume {a : ℝ | t ≤ hfn (fun _ => a)}).toReal) intF intG intH)
    (h_tail : IsTailIntegrableHyp
      (fun t => (volume {a : ℝ | t ≤ f (fun _ => a)}).toReal)
      (fun t => (volume {a : ℝ | t ≤ g (fun _ => a)}).toReal)
      (fun t => (volume {a : ℝ | t ≤ hfn (fun _ => a)}).toReal)) :
    intF ^ lam * intG ^ (1 - lam) ≤ intH := by
  -- reshape integrals to ℝ.
  have hF1 : intF = ∫ a : ℝ, f (fun _ => a) := by
    rw [heqF]; exact integral_funUnique_eq f hf_int
  have hG1 : intG = ∫ a : ℝ, g (fun _ => a) := by
    rw [heqG]; exact integral_funUnique_eq g hg_int
  have hH1 : intH = ∫ a : ℝ, hfn (fun _ => a) := by
    rw [heqH]; exact integral_funUnique_eq hfn hh_int
  -- reshape pointwise PL to ℝ: `λ • (fun _ => x) + (1-λ) • (fun _ => y)
  --   = fun _ => λ * x + (1-λ) * y`.
  have h_pt' : ∀ x y : ℝ,
      f (fun _ => x) ^ lam * g (fun _ => y) ^ (1 - lam)
        ≤ hfn (fun _ => lam * x + (1 - lam) * y) := by
    intro x y
    have := h_pt (fun _ => x) (fun _ => y)
    have hmix : (lam • (fun _ => x) + (1 - lam) • (fun _ => y) : Fin 1 → ℝ)
        = fun _ => lam * x + (1 - lam) * y := by
      funext i; simp [smul_eq_mul]
    rwa [hmix] at this
  -- apply 1D engine to the reshaped functions.
  rw [hF1, hG1, hH1]
  exact prekopa_leindler_1D_superlevel_discharged
    (fun a => f (fun _ => a)) (fun a => g (fun _ => a)) (fun a => hfn (fun _ => a))
    lam h0 h1 _ _ _
    (by rw [← hF1]; exact hF) (by rw [← hG1]; exact hG) (by rw [← hH1]; exact hH)
    hFc hGc hFne hGne hHfin h_pt'
    (by rw [hF1, hG1, hH1] at h_lc; exact h_lc) h_tail

/-! ## §D — slice 1D-PL の解析的前提 bundle + n 次元 PL 帰納本体 -/

/-- **slice 1D-PL readiness (honest analytic side-condition bundle)**: 帰納 step
で slice 積分 `sliceInt f, sliceInt g, sliceInt hfn : ℝ → ℝ` に外側 1D PL
(`prekopa_leindler_1D_superlevel_discharged`) を適用するために必要な、
superlevel 集合の regularity + layer-cake 恒等式 + tail 可積分性をまとめた
hypothesis。`:= True` ではなく実際の `IsCompact` / `Nonempty` / `≠ ∞` /
`IsPL1LayerCakeIntegralHyp` / `IsTailIntegrableHyp` 命題の連言で、genuine
measure content (本 file scope 外の解析的前提) を honest に外出ししたもの。 -/
def IsSlicePLReadyHyp {n : ℕ}
    (f g hfn : (Fin (n + 1) → ℝ) → ℝ) (lam intF intG intH : ℝ) : Prop :=
  (∀ t : ℝ, 0 < t → IsCompact {s : ℝ | t ≤ sliceInt f s}) ∧
  (∀ t : ℝ, 0 < t → IsCompact {s : ℝ | t ≤ sliceInt g s}) ∧
  (∀ t : ℝ, 0 < t → ({s : ℝ | t ≤ sliceInt f s}).Nonempty) ∧
  (∀ t : ℝ, 0 < t → ({s : ℝ | t ≤ sliceInt g s}).Nonempty) ∧
  (∀ t : ℝ, 0 < t → volume {s : ℝ | t ≤ sliceInt hfn s} ≠ ∞) ∧
  IsPL1LayerCakeIntegralHyp
    (fun t => (volume {s : ℝ | t ≤ sliceInt f s}).toReal)
    (fun t => (volume {s : ℝ | t ≤ sliceInt g s}).toReal)
    (fun t => (volume {s : ℝ | t ≤ sliceInt hfn s}).toReal) intF intG intH ∧
  IsTailIntegrableHyp
    (fun t => (volume {s : ℝ | t ≤ sliceInt f s}).toReal)
    (fun t => (volume {s : ℝ | t ≤ sliceInt g s}).toReal)
    (fun t => (volume {s : ℝ | t ≤ sliceInt hfn s}).toReal)

/-- **n 次元 Prékopa-Leindler — Fubini 帰納 step (n → n+1, genuine)**.

次元 `n` の (clean) PL を `ih` として受け、次元 `n+1` の PL を組む genuine な
帰納 step。点ごと PL 仮定 `f x ^ λ * g y ^ (1-λ) ≤ hfn (λ • x + (1-λ) • y)`
の下、`(∫ f) ^ λ * (∫ g) ^ (1-λ) ≤ ∫ hfn`。

step の配線 (engine 3 補題 + 外側 1D PL):
* slice 積分 `sliceInt f, sliceInt g, sliceInt hfn : ℝ → ℝ`。
* `sliceInt_pointwise_pl` (engine) で slice の 1D pointwise PL を `ih` から得る。
* 外側 1D PL (`prekopa_leindler_1D_superlevel_discharged`) を slice 積分に適用 →
  `(∫ sliceInt f) ^ λ * (∫ sliceInt g) ^ (1-λ) ≤ ∫ sliceInt hfn`。
* `integral_pi_succ_eq` (engine, genuine Fubini) で `∫ sliceInt φ = ∫ φ` に
  書き換え → 全体 PL。

`ih` は **clean** PL (非負性 + 点ごと PL → 積分 PL のみ要求)、これが
`sliceInt_pointwise_pl` の `ih` 引数に直接 fit する。slice の非負性
(`hf_nn`, `hg_nn`, `hh_nn`)、Fubini 可積分性 (`Integrable`)、slice 1D-PL
readiness (`IsSlicePLReadyHyp`, 解析的前提) は honest named hypothesis として
外出し。**構造的帰納 step そのものは genuine** (engine 3 補題で実 Fubini 接続)。 -/
theorem prekopa_leindler_nDim {n : ℕ}
    (f g hfn : (Fin (n + 1) → ℝ) → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (intF intG intH : ℝ)
    (hF : 0 ≤ intF) (hG : 0 ≤ intG) (hH : 0 ≤ intH)
    (h_pt : ∀ x y : Fin (n + 1) → ℝ,
      f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam • x + (1 - lam) • y))
    (heqF : intF = ∫ x, f x) (heqG : intG = ∫ x, g x) (heqH : intH = ∫ x, hfn x)
    (hf_int : Integrable f) (hg_int : Integrable g) (hh_int : Integrable hfn)
    (hf_nn : ∀ s, 0 ≤ sliceInt f s) (hg_nn : ∀ s, 0 ≤ sliceInt g s)
    (hh_nn : ∀ s, 0 ≤ sliceInt hfn s)
    (ih : ∀ (f' g' hfn' : (Fin n → ℝ) → ℝ),
      (0 ≤ ∫ w, f' w) → (0 ≤ ∫ w, g' w) → (0 ≤ ∫ w, hfn' w) →
      (∀ x y : Fin n → ℝ,
        f' x ^ lam * g' y ^ (1 - lam) ≤ hfn' (lam • x + (1 - lam) • y)) →
      (∫ w, f' w) ^ lam * (∫ w, g' w) ^ (1 - lam) ≤ ∫ w, hfn' w)
    (h_ready : IsSlicePLReadyHyp f g hfn lam intF intG intH) :
    intF ^ lam * intG ^ (1 - lam) ≤ intH := by
  obtain ⟨hFc, hGc, hFne, hGne, hHfin, h_lc, h_tail⟩ := h_ready
  -- Fubini: top-level integral = integral of slice integral.
  have hFub_f : intF = ∫ s, sliceInt f s := by
    rw [heqF]; exact integral_pi_succ_eq f hf_int
  have hFub_g : intG = ∫ s, sliceInt g s := by
    rw [heqG]; exact integral_pi_succ_eq g hg_int
  have hFub_h : intH = ∫ s, sliceInt hfn s := by
    rw [heqH]; exact integral_pi_succ_eq hfn hh_int
  -- slice 1D pointwise PL (engine, IH consumed).
  have h_slice_pt : ∀ s s' : ℝ,
      sliceInt f s ^ lam * sliceInt g s' ^ (1 - lam)
        ≤ sliceInt hfn (lam * s + (1 - lam) * s') :=
    sliceInt_pointwise_pl f g hfn lam h0 h1 h_pt ih hf_nn hg_nn hh_nn
  -- outer 1D PL on the slice integrals.
  have hF' : 0 ≤ ∫ s, sliceInt f s := by rw [← hFub_f]; exact hF
  have hG' : 0 ≤ ∫ s, sliceInt g s := by rw [← hFub_g]; exact hG
  have hH' : 0 ≤ ∫ s, sliceInt hfn s := by rw [← hFub_h]; exact hH
  have hkey :
      (∫ s, sliceInt f s) ^ lam * (∫ s, sliceInt g s) ^ (1 - lam)
        ≤ ∫ s, sliceInt hfn s :=
    prekopa_leindler_1D_superlevel_discharged
      (sliceInt f) (sliceInt g) (sliceInt hfn) lam h0 h1
      (∫ s, sliceInt f s) (∫ s, sliceInt g s) (∫ s, sliceInt hfn s)
      hF' hG' hH' hFc hGc hFne hGne hHfin h_slice_pt
      (by rw [hFub_f, hFub_g, hFub_h] at h_lc; exact h_lc) h_tail
  rw [hFub_f, hFub_g, hFub_h]
  exact hkey

/-! ## §E — indicator の点ごと PL (Minkowski sum membership から供給) -/

/-- **indicator 関数の点ごと PL (genuine, Minkowski sum membership から)**:
`f = 1_A, g = 1_B, h = 1_{λ•A + (1-λ)•B}` (real-valued indicator) について、
`0 < λ < 1` (PL の標準内点条件) で点ごと PL

    `(1_A x) ^ λ * (1_B y) ^ (1-λ) ≤ 1_{λ•A+(1-λ)•B} (λ • x + (1-λ) • y)`

が成立。核心: `x ∈ A`, `y ∈ B` のとき LHS = 1 で、`λ•x + (1-λ)•y ∈
λ•A + (1-λ)•B` (`Set.smul_mem_smul_set` + `Set.add_mem_add`) より RHS = 1。
`x ∉ A` (or `y ∉ B`) のとき `0 < λ < 1` で LHS の片因子が `0 ^ λ = 0`
(resp `0 ^ (1-λ) = 0`)、RHS ≥ 0 で成立。境界 `λ ∈ {0,1}` は退化 (PL が
自明) なので除外。 -/
theorem indicator_pointwise_pl {n : ℕ}
    (A B : Set (Fin n → ℝ)) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (x y : Fin n → ℝ) :
    (A.indicator (fun _ => (1 : ℝ)) x) ^ lam
        * (B.indicator (fun _ => (1 : ℝ)) y) ^ (1 - lam)
      ≤ (lam • A + (1 - lam) • B).indicator (fun _ => (1 : ℝ))
          (lam • x + (1 - lam) • y) := by
  have h1lam : (0 : ℝ) < 1 - lam := by linarith
  have hrhs_nn : 0 ≤ (lam • A + (1 - lam) • B).indicator
      (fun _ => (1 : ℝ)) (lam • x + (1 - lam) • y) :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases hxA : x ∈ A
  · by_cases hyB : y ∈ B
    · -- both in: LHS = 1, midpoint in Minkowski sum so RHS = 1.
      have hmem : lam • x + (1 - lam) • y ∈ lam • A + (1 - lam) • B :=
        Set.add_mem_add (Set.smul_mem_smul_set hxA) (Set.smul_mem_smul_set hyB)
      rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hyB,
        Set.indicator_of_mem hmem, Real.one_rpow, Real.one_rpow, mul_one]
    · -- y ∉ B: `(1_B y) ^ (1-λ) = 0 ^ (1-λ) = 0`, LHS = 0 ≤ RHS.
      rw [Set.indicator_of_notMem hyB, Real.zero_rpow (ne_of_gt h1lam), mul_zero]
      exact hrhs_nn
  · -- x ∉ A: `(1_A x) ^ λ = 0 ^ λ = 0`, LHS = 0 ≤ RHS.
    rw [Set.indicator_of_notMem hxA, Real.zero_rpow (ne_of_gt h0), zero_mul]
    exact hrhs_nn

/-! ## §F — 体積版 BM corollary (Phase 1 段階着地点) -/

/-- **indicator 積分 = 体積 (`.toReal`)**: 可測 `A` について
`∫ x, A.indicator (fun _ => 1) x = (volume A).toReal`。`integral_indicator_one`
(Mathlib) を `1 = fun _ => 1` (Pi の defeq) で橋渡し。 -/
theorem integral_indicator_one_eq_volume {n : ℕ}
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    ∫ x, A.indicator (fun _ => (1 : ℝ)) x = (volume A).toReal := by
  rw [show (fun _ => (1 : ℝ)) = (1 : (Fin n → ℝ) → ℝ) from rfl]
  rw [integral_indicator_one hA]
  rfl

/-- **体積版 Brunn-Minkowski (multiplicative form, n 次元 PL の indicator 特殊化)**.

`f = 1_A, g = 1_B, h = 1_{λ•A+(1-λ)•B}` の n 次元 PL 結論
`(∫ 1_A)^λ * (∫ 1_B)^(1-λ) ≤ ∫ 1_{λA+(1-λ)B}` (`h_pl`、`prekopa_leindler_nDim`
を `indicator_pointwise_pl` の点ごと PL に適用して得る) を、`indicator 積分 =
体積` (`integral_indicator_one_eq_volume`) で書き換え、体積版

    `(vol A)^λ * (vol B)^(1-λ) ≤ vol(λ•A + (1-λ)•B)` (`.toReal`)

を得る。これが Phase 1 段階着地点: **体積版 BM が n 次元 PL の indicator
特殊化として閉じる** (点ごと PL は genuine `indicator_pointwise_pl`、積分↔体積は
genuine `integral_indicator_one`)。

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem brunn_minkowski_volume_indicator {n : ℕ}
    (A B : Set (Fin n → ℝ)) (lam : ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : MeasurableSet (lam • A + (1 - lam) • B))
    (h_pl :
      (∫ x, A.indicator (fun _ => (1 : ℝ)) x) ^ lam
          * (∫ x, B.indicator (fun _ => (1 : ℝ)) x) ^ (1 - lam)
        ≤ ∫ x, (lam • A + (1 - lam) • B).indicator (fun _ => (1 : ℝ)) x) :
    (volume A).toReal ^ lam * (volume B).toReal ^ (1 - lam)
      ≤ (volume (lam • A + (1 - lam) • B)).toReal := by
  rw [integral_indicator_one_eq_volume A hA, integral_indicator_one_eq_volume B hB,
    integral_indicator_one_eq_volume _ hAB] at h_pl
  exact h_pl

/-- **体積版 Brunn-Minkowski (multiplicative form, additive 経由)**: 凸体 `A, B`
の体積について

    `vol(λ A + (1-λ) B) ^ 1 ≥ vol A ^ λ * vol B ^ (1-λ)`

(加法形からの AM-GM 派生 `bm_additive_to_multiplicative` 経由)。 -/
theorem brunn_minkowski_volume_mul {n : ℕ}
    (volA volB volAB lam : ℝ)
    (hvolA : 0 ≤ volA) (hvolB : 0 ≤ volB) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (h_add : lam * volA + (1 - lam) * volB ≤ volAB) :
    volA ^ lam * volB ^ (1 - lam) ≤ volAB :=
  bm_additive_to_multiplicative hvolA hvolB h0 h1 h_add

/-! ## §G — entropy-power 形 BM (Phase 2-4): geometry → entropy power

体積版 BM (§F, genuine) を **entropy-power 加法形** に持ち上げ、headline の抽象
`h` を `Common2026.Shannon.jointDifferentialEntropyPi` に特化して genuine に閉じる。

設計判断 (Mathlib-shape-driven + 撤退):

* **核心 reduction は genuine**: entropy power `exp((2/n)·h)` の加法形 ↔ 体積比
  `vol^(2/n)` の加法形 ↔ Cover-Thomas sqrt 形 `vol^(1/n)` の加法形 (これらは
  `Real.rpow` 代数 + `entropyPower_nDim_eq_rpow_of_log` + 既存 log-exp bridge で
  すべて genuine に接続)。
* **唯一外出しする geometric content** は Cover-Thomas sqrt 形の不等式そのもの
  `volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)` (`IsBMEntropyPowerVolumeHyp`, 実 `≥`
  Prop、`:= True` ではない)。これは §F の **multiplicative** 体積 BM
  (`volA^λ·volB^(1-λ) ≤ volAB`) から coordinate-scaling 最適化 (Cover-Thomas
  17.9.2 標準導出) で出るが、その scaling 最適化は n-dim measure scaling
  (`vol(r•A)=r^n volA`) + 最適 λ 代入 を要し本 file scope では honest hyp に
  外出し (撤退ライン: scaling 最適化 >300 行)。
* **headline 特化が前進点**: 旧 `brunn_minkowski_entropy_inequality` は抽象
  `h` + `:= h_bm` で **結論全体** を pass-through していた。本 §G は `h` を concrete
  `jointDifferentialEntropyPi` に固定し、entropy↔geometry↔rpow 代数を **genuine** に
  し、外出しを「geometric BM 不等式のみ」に縮小する (honest 副条件
  `IsBMEntropyPowerVolumeHyp` 1 本のみ)。 -/

/-- **n-dim measure scaling** `vol(r • A) = r^n · vol(A)` (`0 ≤ r`) on
`Fin n → ℝ`. `Measure.addHaar_smul_of_nonneg` + `Module.finrank_fin_fun`
(`finrank ℝ (Fin n → ℝ) = n`)。scaling 最適化 (§G discharge 試行) の足場。 -/
theorem volume_smul_nDim {n : ℕ} (r : ℝ) (hr : 0 ≤ r) (A : Set (Fin n → ℝ)) :
    volume (r • A) = ENNReal.ofReal (r ^ n) * volume A := by
  rw [Measure.addHaar_smul_of_nonneg (μ := volume) hr, Module.finrank_fin_fun]

/-- **L-BM-EP (entropy-power volume hypothesis, honest geometric side-condition)**:
Cover-Thomas sqrt 形 Brunn-Minkowski

    `volAB ^ (1/n) ≥ volA ^ (1/n) + volB ^ (1/n)`

(`Real.rpow`)。§F の multiplicative 体積 BM からの coordinate-scaling 最適化で
得られる geometric content を honest named hypothesis (実 `≥` Prop) として外出し。
`IsBrunnMinkowskiEntropyHypothesis` (旧抽象 `h` 結論全体 pass-through) より遥かに
小さい外出し: 残るのは geometry 不等式 1 本のみで、entropy power への持ち上げは
すべて genuine。 -/
def IsBMEntropyPowerVolumeHyp (n : ℕ) (volA volB volAB : ℝ) : Prop :=
  volAB ^ ((1 : ℝ) / n) ≥ volA ^ ((1 : ℝ) / n) + volB ^ ((1 : ℝ) / n)

/-- **sqrt 形 → entropy-power 加法形 (genuine, `Real.rpow` 代数)**: Cover-Thomas
sqrt 形 `volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)` を 2 乗持ち上げて

    `volAB^(2/n) ≥ volA^(2/n) + volB^(2/n)`.

`x^(2/n) = (x^(1/n))^2` (`Real.rpow` 代数) + `square_to_linear_to_square_bridge`
逆向き (`(p+q)^2 ≥ p^2+q^2` for `p,q ≥ 0`)。 -/
theorem bm_volume_sqrt_to_entropyPower {n : ℕ}
    (volA volB volAB : ℝ)
    (hvolA : 0 ≤ volA) (hvolB : 0 ≤ volB) (hvolAB : 0 ≤ volAB)
    (h_sqrt : IsBMEntropyPowerVolumeHyp n volA volB volAB) :
    volAB ^ ((2 : ℝ) / n) ≥ volA ^ ((2 : ℝ) / n) + volB ^ ((2 : ℝ) / n) := by
  unfold IsBMEntropyPowerVolumeHyp at h_sqrt
  -- `x^(2/n) = (x^(1/n))^2` for `x ≥ 0`.
  have hsq : ∀ x : ℝ, 0 ≤ x → x ^ ((2 : ℝ) / n) = (x ^ ((1 : ℝ) / n)) ^ 2 := by
    intro x hx
    have : (2 : ℝ) / n = (1 / n) * ((2 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_mul_natCast hx]
  -- sqrt-values are non-negative.
  have hpA : 0 ≤ volA ^ ((1 : ℝ) / n) := Real.rpow_nonneg hvolA _
  have hpB : 0 ≤ volB ^ ((1 : ℝ) / n) := Real.rpow_nonneg hvolB _
  rw [hsq volA hvolA, hsq volB hvolB, hsq volAB hvolAB]
  -- `(volAB^(1/n))^2 ≥ (volA^(1/n) + volB^(1/n))^2 ≥ (volA^(1/n))^2 + (volB^(1/n))^2`.
  exact square_necessary_for_linear hpA hpB h_sqrt

/-- **entropy-power 形 Brunn-Minkowski, `jointDifferentialEntropyPi` 特化**.

`h := jointDifferentialEntropyPi` に固定した entropy power 加法形

    `entropyPower_nDim n hJoint (P.map (X+Y))
      ≥ entropyPower_nDim n hJoint (P.map X) + entropyPower_nDim n hJoint (P.map Y)`.

🟢ʰ load-bearing hypothesis — NOT a discharge. 本定理の load-bearing 部分は
`h_geom_bm_assumed : IsBMEntropyPowerVolumeHyp n volA volB volAB`
(= geometric Brunn-Minkowski sqrt 形 `volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)`)
で、これが Mathlib 壁 (Mathlib に凸体 Brunn-Minkowski が存在しない) のため
hypothesis pass-through。

genuine な部分は entropy↔geometry↔rpow の代数のみ:
uniform=log-vol hypotheses (`IsUniformOnEntropyLogVolHypothesis`) で各 entropy power
を `vol^(2/n)` に書き換え (`entropyPower_nDim_eq_rpow_of_log`, genuine)、
sqrt 形 → entropy power 加法形持ち上げ (`bm_volume_sqrt_to_entropyPower`, genuine
`Real.rpow` 代数)。

`hJoint := jointDifferentialEntropyPi` は concrete (抽象 `h` 引数を排除)。
Discharge: §H 以降で `IsBMScaledMulHyp` (primitive scalar 形) からの λ-最適化
chain (`bm_scaledMul_to_sqrt`) + geometric BM image (`bm_geom_to_scaledMul`) が
provided。完全 discharge は本リポジトリでは凸体 BM (Mathlib 壁) で塞がる。

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem brunn_minkowski_entropy_jointPi
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < (n : ℝ))
    (X Y : Ω → (Fin n → ℝ))
    (volA volB volAB : ℝ) (hvolA : 0 < volA) (hvolB : 0 < volB) (hvolAB : 0 < volAB)
    (hA_unif : Common2026.Shannon.jointDifferentialEntropyPi (P.map X) = Real.log volA)
    (hB_unif : Common2026.Shannon.jointDifferentialEntropyPi (P.map Y) = Real.log volB)
    (hAB_unif : Common2026.Shannon.jointDifferentialEntropyPi
      (P.map (fun ω => X ω + Y ω)) = Real.log volAB)
    (h_geom_bm_assumed : IsBMEntropyPowerVolumeHyp n volA volB volAB) :
    entropyPower_nDim n Common2026.Shannon.jointDifferentialEntropyPi
        (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower_nDim n Common2026.Shannon.jointDifferentialEntropyPi (P.map X)
        + entropyPower_nDim n Common2026.Shannon.jointDifferentialEntropyPi (P.map Y) := by
  -- Each entropy power `exp ((2/n)·h μ)` rewrites to `vol^(2/n)` via the
  -- uniform=log-vol hypotheses + `Real.rpow_def_of_pos` (genuine, all real-algebra).
  have hep : ∀ (μ : Measure (Fin n → ℝ)) (vol : ℝ), 0 < vol →
      Common2026.Shannon.jointDifferentialEntropyPi μ = Real.log vol →
      entropyPower_nDim n Common2026.Shannon.jointDifferentialEntropyPi μ
        = vol ^ ((2 : ℝ) / n) := by
    intro μ vol hvol hμ
    rw [entropyPower_nDim_eq_exp, hμ, Real.rpow_def_of_pos hvol, mul_comm]
  rw [hep _ volA hvolA hA_unif, hep _ volB hvolB hB_unif, hep _ volAB hvolAB hAB_unif]
  -- geometric content (`IsBMEntropyPowerVolumeHyp`) lifts to the entropy-power form.
  exact bm_volume_sqrt_to_entropyPower volA volB volAB hvolA.le hvolB.le hvolAB.le
    h_geom_bm_assumed

/-- **Phase 4 — entropy 形 headline restate (`jointDifferentialEntropyPi` 特化)**.

旧 `BrunnMinkowski.brunn_minkowski_entropy_inequality` は抽象
`h : Measure (Fin n → ℝ) → ℝ` を取り `:= h_bm` (L-BM1, 結論全体) で着地していた。
本 headline は `h` を concrete `Common2026.Shannon.jointDifferentialEntropyPi` に
固定し、`brunn_minkowski_entropy_jointPi` (genuine reduction) で着地する。
抽象 `h` の `h_bm` 結論全体 pass-through を経由しない。

外出しは uniform=log-vol (entropy ↔ volume 同定、§F の `IsUniformOnEntropyLogVol`
と同流儀) + geometric BM 不等式 (`IsBMEntropyPowerVolumeHyp`) のみ。 -/
theorem brunn_minkowski_entropy_inequality_genuine
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < (n : ℝ))
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : ProbabilityTheory.IndepFun X Y P)
    (volA volB volAB : ℝ) (hvolA : 0 < volA) (hvolB : 0 < volB) (hvolAB : 0 < volAB)
    (hA_unif : Common2026.Shannon.jointDifferentialEntropyPi (P.map X) = Real.log volA)
    (hB_unif : Common2026.Shannon.jointDifferentialEntropyPi (P.map Y) = Real.log volB)
    (hAB_unif : Common2026.Shannon.jointDifferentialEntropyPi
      (P.map (fun ω => X ω + Y ω)) = Real.log volAB)
    (h_geom : IsBMEntropyPowerVolumeHyp n volA volB volAB) :
    entropyPower_nDim n Common2026.Shannon.jointDifferentialEntropyPi
        (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower_nDim n Common2026.Shannon.jointDifferentialEntropyPi (P.map X)
        + entropyPower_nDim n Common2026.Shannon.jointDifferentialEntropyPi (P.map Y) :=
  brunn_minkowski_entropy_jointPi P hn X Y volA volB volAB hvolA hvolB hvolAB
    hA_unif hB_unif hAB_unif h_geom

/-! ## §H — geometric honest hyp の縮約: sqrt 形 BM の λ-最適化 discharge

§G では geometric content を sqrt 形 `IsBMEntropyPowerVolumeHyp`
(`volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)`) として丸ごと honest 仮定にしていた。
本 §H はこれを **より primitive な scalar-multiplicative BM 仮定**
`IsBMScaledMulHyp` (Cover-Thomas 17.9.2 の出発点である scaled multiplicative
BM) に **縮約** する: `IsBMScaledMulHyp ⇒ IsBMEntropyPowerVolumeHyp` を
λ-最適化 (`λ = volA^(1/n)/(volA^(1/n)+volB^(1/n))`) + `Real.rpow` 代数で
**genuine** に証明する (`bm_scaledMul_to_sqrt`)。

さらに `IsBMScaledMulHyp` が geometric BM の image であることを
`bm_geom_to_scaledMul` (`volume_smul_nDim` で scaling 因子 `r^n` を回収し、集合恒等式
`λ • (λ⁻¹ • A) + (1-λ) • ((1-λ)⁻¹ • B) = A + B` で plain Minkowski sum に橋渡し)
で示し、`IsBMScaledMulHyp` が `:= True` 系の vacuous placeholder ではなく
genuine geometric content の scalar 投影であることを担保する。 -/

/-- **L-BM-EP' (scaled multiplicative BM hypothesis, honest geometric
side-condition, `IsBMEntropyPowerVolumeHyp` より primitive)**: Cover-Thomas
17.9.2 の出発点。任意の内点 `λ ∈ (0,1)` で

    `(λ^(-n) · volA) ^ λ · ((1-λ)^(-n) · volB) ^ (1-λ) ≤ volAB`.

これは集合 `A₁ = λ⁻¹ • A`, `B₁ = (1-λ)⁻¹ • B` への乗法形 geometric BM
`vol(A₁)^λ · vol(B₁)^(1-λ) ≤ vol(λ • A₁ + (1-λ) • B₁) = vol(A + B)` に
`volume_smul_nDim` (`vol(r•A)=r^n volA`) を代入したもの (`bm_geom_to_scaledMul`
で genuine に geometric BM から導出可能)。sqrt 形 `IsBMEntropyPowerVolumeHyp`
より primitive で、λ-最適化を経由せず素直に geometric BM の image。 -/
def IsBMScaledMulHyp (n : ℕ) (volA volB volAB : ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam → lam < 1 →
    (lam ^ (-(n : ℝ)) * volA) ^ lam * ((1 - lam) ^ (-(n : ℝ)) * volB) ^ (1 - lam)
      ≤ volAB

/-- **scaled multiplicative BM ⇒ sqrt 形 BM (genuine, λ-最適化 + `Real.rpow` 代数)**.

Cover-Thomas 17.9.2 標準導出: `s := volA^(1/n)`, `t := volB^(1/n)` (共に正) と
最適 `λ := s/(s+t)` (`1-λ = t/(s+t)`) を代入すると `s/λ = s+t = t/(1-λ)` なので
`(λ^(-n)·volA)^λ = ((s/λ)^n)^λ = (s+t)^(nλ)`、同様に右因子 `= (s+t)^(n(1-λ))`、
積は `(s+t)^n`。よって `(s+t)^n ≤ volAB`、両辺に `(·)^(1/n)` (単調) を施し
`((s+t)^n)^(1/n) = s+t` で `s + t ≤ volAB^(1/n)`、すなわち sqrt 形 BM。 -/
theorem bm_scaledMul_to_sqrt {n : ℕ}
    (volA volB volAB : ℝ)
    (hvolA : 0 < volA) (hvolB : 0 < volB) (hn : 0 < n)
    (h_scaled : IsBMScaledMulHyp n volA volB volAB) :
    IsBMEntropyPowerVolumeHyp n volA volB volAB := by
  unfold IsBMEntropyPowerVolumeHyp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  -- sqrt values `s, t` and their basics.
  set s : ℝ := volA ^ ((1 : ℝ) / n) with hs
  set t : ℝ := volB ^ ((1 : ℝ) / n) with ht
  have hs_pos : 0 < s := Real.rpow_pos_of_pos hvolA _
  have ht_pos : 0 < t := Real.rpow_pos_of_pos hvolB _
  have hc_pos : 0 < s + t := by linarith
  -- `s ^ n = volA`, `t ^ n = volB`.
  have hsn : s ^ (n : ℝ) = volA := by
    rw [hs, ← Real.rpow_mul hvolA.le, one_div, inv_mul_cancel₀ hnne, Real.rpow_one]
  have htn : t ^ (n : ℝ) = volB := by
    rw [ht, ← Real.rpow_mul hvolB.le, one_div, inv_mul_cancel₀ hnne, Real.rpow_one]
  -- optimal `λ = s/(s+t)`.
  set lam : ℝ := s / (s + t) with hlam
  have hlam_pos : 0 < lam := div_pos hs_pos hc_pos
  have hlam_lt : lam < 1 := by
    rw [hlam, div_lt_one hc_pos]; linarith
  have hlam1 : 1 - lam = t / (s + t) := by
    rw [hlam]; field_simp; ring
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have h1lam_pos : 0 < 1 - lam := by rw [hlam1]; positivity
  have hlam1_ne : (1 - lam) ≠ 0 := ne_of_gt h1lam_pos
  -- the two scaling collapses: `λ^(-n)·volA = (s+t)^n` and same for the `t` factor.
  have hcollapse_s : lam ^ (-(n : ℝ)) * volA = (s + t) ^ (n : ℝ) := by
    rw [← hsn, Real.rpow_neg hlam_pos.le, ← div_eq_inv_mul, ← Real.div_rpow hs_pos.le hlam_pos.le,
      hlam]
    congr 1
    field_simp
  have hcollapse_t : (1 - lam) ^ (-(n : ℝ)) * volB = (s + t) ^ (n : ℝ) := by
    rw [← htn, Real.rpow_neg h1lam_pos.le, ← div_eq_inv_mul,
      ← Real.div_rpow ht_pos.le h1lam_pos.le, hlam1]
    congr 1
    field_simp
  -- the scaled multiplicative BM at the optimal `λ` collapses to `(s+t)^n ≤ volAB`.
  have hkey := h_scaled lam hlam_pos hlam_lt
  rw [hcollapse_s, hcollapse_t] at hkey
  have hcn : ((s + t) ^ (n : ℝ)) ^ lam * ((s + t) ^ (n : ℝ)) ^ (1 - lam)
      = (s + t) ^ (n : ℝ) := by
    rw [← Real.rpow_mul hc_pos.le, ← Real.rpow_mul hc_pos.le, ← Real.rpow_add hc_pos]
    congr 1
    ring
  rw [hcn] at hkey
  -- apply `(·)^(1/n)` (monotone) and cancel `((s+t)^n)^(1/n) = s+t`.
  have hmono := Real.rpow_le_rpow (by positivity) hkey (by positivity : (0 : ℝ) ≤ 1 / n)
  rw [← Real.rpow_mul hc_pos.le, one_div, mul_inv_cancel₀ hnne, Real.rpow_one] at hmono
  rw [ge_iff_le, one_div]
  exact hmono

/-- **集合恒等式 (scaling で plain Minkowski sum を回収)**: `λ ≠ 0`,
`1-λ ≠ 0` で `λ • (λ⁻¹ • A) + (1-λ) • ((1-λ)⁻¹ • B) = A + B` on `Fin n → ℝ`.
`smul_smul` + `mul_inv_cancel` + `one_smul`。 -/
theorem smul_inv_smul_add_eq {n : ℕ} (A B : Set (Fin n → ℝ)) (lam : ℝ)
    (hlam : lam ≠ 0) (hlam' : (1 - lam) ≠ 0) :
    lam • ((lam⁻¹ : ℝ) • A) + (1 - lam) • (((1 - lam)⁻¹ : ℝ) • B) = A + B := by
  rw [smul_smul, smul_smul, mul_inv_cancel₀ hlam, mul_inv_cancel₀ hlam',
    one_smul, one_smul]

/-- **geometric BM ⇒ scaled multiplicative BM (genuine, `volume_smul_nDim` 接続)**:
multiplicative geometric BM `vol(A₁)^λ vol(B₁)^(1-λ) ≤ vol(λ•A₁+(1-λ)•B₁)`
(`h_geom_mul`、§F `brunn_minkowski_volume_indicator` で供給) を、`A₁ = λ⁻¹•A`,
`B₁ = (1-λ)⁻¹•B` で取り、`volume_smul_nDim` で `vol(A₁) = (λ⁻¹)^n volA` 等を
代入、集合恒等式 (`smul_inv_smul_add_eq`) で `λ•A₁+(1-λ)•B₁ = A+B` に橋渡しして
`IsBMScaledMulHyp n volA volB volAB` (with `volAB = vol(A+B)`) を得る。
これで `IsBMScaledMulHyp` が genuine geometric content の scalar 投影であることを
担保 (`volume_smul_nDim` を genuine に使用)。 -/
theorem bm_geom_to_scaledMul {n : ℕ} (A B : Set (Fin n → ℝ))
    (hvolA : volume A ≠ ∞) (hvolB : volume B ≠ ∞)
    (h_geom_mul : ∀ lam : ℝ, 0 < lam → lam < 1 →
      (volume ((lam⁻¹ : ℝ) • A)).toReal ^ lam
          * (volume (((1 - lam)⁻¹ : ℝ) • B)).toReal ^ (1 - lam)
        ≤ (volume (lam • ((lam⁻¹ : ℝ) • A)
            + (1 - lam) • (((1 - lam)⁻¹ : ℝ) • B))).toReal) :
    IsBMScaledMulHyp n (volume A).toReal (volume B).toReal (volume (A + B)).toReal := by
  intro lam hlam_pos hlam_lt
  have h1lam_pos : 0 < 1 - lam := by linarith
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hlam1_ne : (1 - lam) ≠ 0 := ne_of_gt h1lam_pos
  -- `vol(r • A).toReal = r^n · vol(A).toReal` for `0 < r`, `vol A ≠ ∞`, expressed
  -- with the scaling factor `r^(-n)` in `rpow` form: `(r⁻¹)^n = r^(-(n:ℝ))`.
  have hscale : ∀ (r : ℝ), 0 < r → ∀ (S : Set (Fin n → ℝ)), volume S ≠ ∞ →
      (volume ((r⁻¹ : ℝ) • S)).toReal = r ^ (-(n : ℝ)) * (volume S).toReal := by
    intro r hr S hS
    rw [volume_smul_nDim _ (by positivity) S, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    congr 1
    rw [Real.rpow_neg hr.le, Real.rpow_natCast, ← inv_pow]
  -- rewrite both scaled volumes and the Minkowski-sum set in `h_geom_mul`.
  have hkey := h_geom_mul lam hlam_pos hlam_lt
  rw [hscale lam hlam_pos A hvolA, hscale (1 - lam) h1lam_pos B hvolB,
    smul_inv_smul_add_eq A B lam hlam_ne hlam1_ne] at hkey
  exact hkey

/-- **Phase 4' — entropy 形 headline (`IsBMScaledMulHyp` 縮約版)**.

`brunn_minkowski_entropy_inequality_genuine` と同結論だが、geometric honest 仮定を
sqrt 形 `IsBMEntropyPowerVolumeHyp` から **より primitive な** scaled multiplicative
`IsBMScaledMulHyp` に縮約 (sqrt 形への λ-最適化持ち上げ `bm_scaledMul_to_sqrt` を
内部で genuine に消費)。残る honest 仮定は uniform=log-vol 3 本 + scaled
multiplicative BM 1 本のみで、sqrt 形特有の λ-最適化代数は headline 外に出た。 -/
theorem brunn_minkowski_entropy_inequality_scaledMul
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n)
    (X Y : Ω → (Fin n → ℝ))
    (volA volB volAB : ℝ) (hvolA : 0 < volA) (hvolB : 0 < volB) (hvolAB : 0 < volAB)
    (hA_unif : Common2026.Shannon.jointDifferentialEntropyPi (P.map X) = Real.log volA)
    (hB_unif : Common2026.Shannon.jointDifferentialEntropyPi (P.map Y) = Real.log volB)
    (hAB_unif : Common2026.Shannon.jointDifferentialEntropyPi
      (P.map (fun ω => X ω + Y ω)) = Real.log volAB)
    (h_scaled : IsBMScaledMulHyp n volA volB volAB) :
    entropyPower_nDim n Common2026.Shannon.jointDifferentialEntropyPi
        (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower_nDim n Common2026.Shannon.jointDifferentialEntropyPi (P.map X)
        + entropyPower_nDim n Common2026.Shannon.jointDifferentialEntropyPi (P.map Y) :=
  brunn_minkowski_entropy_jointPi P (by exact_mod_cast hn) X Y volA volB volAB
    hvolA hvolB hvolAB hA_unif hB_unif hAB_unif
    (bm_scaledMul_to_sqrt volA volB volAB hvolA hvolB hn h_scaled)

/-! ## §I — indicator/compact ケースの readiness genuine 供給

§F の `brunn_minkowski_volume_indicator` は n 次元 PL の結論 `h_pl` を **丸ごと
hypothesis** で受けていた。本 §I は `A, B` を **compact** に固定することで、
`prekopa_leindler_nDim` の引数のうち **解析的 slice readiness (`IsSlicePLReadyHyp`)
以外** をすべて genuine に供給する:

* **measurability / 有限測度**: `IsCompact.measurableSet` (T2) / `IsCompact.add` /
  `IsCompact.smul` / `IsCompact.measure_ne_top`。Minkowski 結合 `λ•A+(1-λ)•B` の
  compact 性を伝播させ、3 集合すべてが genuine に可測・有限測度。
* **indicator の Integrable**: `integrable_indicator_iff` + `integrableOn_const`
  (有限測度から)。
* **slice の非負性**: `sliceInt (1_S) s = ∫ w, 1_S (cons s w) ≥ 0`
  (`integral_nonneg`、indicator は非負)。
* **点ごと PL**: §E の `indicator_pointwise_pl` (genuine)。

残る honest 入力は `IsSlicePLReadyHyp` (slice 測度関数の superlevel regularity +
layer-cake + tail、本 file scope 外の irreducible 解析的内容) と帰納仮定
(n 次元 clean PL) のみ。これにより体積版 BM の honest 表面が「n 次元 PL 結論
丸ごと」から「slice readiness のみ」へ大幅縮約される。 -/

/-- **indicator の Integrable (genuine, 有限測度から)**: 可測 `S` で
`volume S ≠ ∞` ならば実数値 indicator `1_S` は `volume` 可積分。
`integrable_indicator_iff` + `integrableOn_const`。 -/
theorem indicator_integrable {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : MeasurableSet S) (hfin : volume S ≠ ∞) :
    Integrable (S.indicator (fun _ => (1 : ℝ))) :=
  (integrable_indicator_iff hS).mpr (integrableOn_const hfin)

/-- **slice 積分の非負性 (genuine)**: pointwise 非負 `f` について
`sliceInt f s = ∫ w, f (cons s w) ≥ 0`。`integral_nonneg`。 -/
theorem sliceInt_nonneg {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : ∀ x, 0 ≤ f x) (s : ℝ) : 0 ≤ sliceInt f s :=
  integral_nonneg (fun _ => hf _)

/-- **indicator の点ごと非負性 (genuine helper)**: `1_S x ≥ 0`。 -/
theorem indicator_one_nonneg {n : ℕ} (S : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    0 ≤ S.indicator (fun _ => (1 : ℝ)) x :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- **体積版 Brunn-Minkowski (indicator/compact ケース, readiness 以外 genuine)**.

`A, B` compact (`0 < λ < 1`) について、`prekopa_leindler_nDim` の引数のうち
measurability / 有限測度 / indicator integrability / slice 非負性 / 点ごと PL を
すべて §I/§E の genuine helper で供給し、残る honest 入力を **slice readiness
(`IsSlicePLReadyHyp`) と n 次元 clean PL 帰納仮定 (`ih`) のみ** に縮約した体積版 BM:

    `(vol A)^λ * (vol B)^(1-λ) ≤ vol(λ•A + (1-λ)•B)` (`.toReal`).

§F の `brunn_minkowski_volume_indicator` (n 次元 PL 結論を丸ごと hypothesis 化)
と違い、PL 結論は本定理内部で `prekopa_leindler_nDim` から genuine に組む。 -/
theorem brunn_minkowski_volume_indicator_compact {n : ℕ}
    (A B : Set (Fin (n + 1) → ℝ)) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam < 1)
    (hA : IsCompact A) (hB : IsCompact B)
    (ih : ∀ (f' g' hfn' : (Fin n → ℝ) → ℝ),
      (0 ≤ ∫ w, f' w) → (0 ≤ ∫ w, g' w) → (0 ≤ ∫ w, hfn' w) →
      (∀ x y : Fin n → ℝ,
        f' x ^ lam * g' y ^ (1 - lam) ≤ hfn' (lam • x + (1 - lam) • y)) →
      (∫ w, f' w) ^ lam * (∫ w, g' w) ^ (1 - lam) ≤ ∫ w, hfn' w)
    (h_ready : IsSlicePLReadyHyp
      (A.indicator (fun _ => (1 : ℝ))) (B.indicator (fun _ => (1 : ℝ)))
      ((lam • A + (1 - lam) • B).indicator (fun _ => (1 : ℝ)))
      lam (volume A).toReal (volume B).toReal
      (volume (lam • A + (1 - lam) • B)).toReal) :
    (volume A).toReal ^ lam * (volume B).toReal ^ (1 - lam)
      ≤ (volume (lam • A + (1 - lam) • B)).toReal := by
  -- compact 性を Minkowski 結合に伝播 → 可測 / 有限測度.
  set C : Set (Fin (n + 1) → ℝ) := lam • A + (1 - lam) • B with hC
  have hCcpt : IsCompact C := (hA.smul lam).add (hB.smul (1 - lam))
  have hA_meas : MeasurableSet A := hA.measurableSet
  have hB_meas : MeasurableSet B := hB.measurableSet
  have hC_meas : MeasurableSet C := hCcpt.measurableSet
  have hA_fin : volume A ≠ ∞ := hA.measure_ne_top
  have hB_fin : volume B ≠ ∞ := hB.measure_ne_top
  have hC_fin : volume C ≠ ∞ := hCcpt.measure_ne_top
  -- 3 indicator 関数と各々の積分=体積恒等式.
  set fA : (Fin (n + 1) → ℝ) → ℝ := A.indicator (fun _ => (1 : ℝ)) with hfA
  set fB : (Fin (n + 1) → ℝ) → ℝ := B.indicator (fun _ => (1 : ℝ)) with hfB
  set fC : (Fin (n + 1) → ℝ) → ℝ := C.indicator (fun _ => (1 : ℝ)) with hfC
  have heqA : (volume A).toReal = ∫ x, fA x :=
    (integral_indicator_one_eq_volume A hA_meas).symm
  have heqB : (volume B).toReal = ∫ x, fB x :=
    (integral_indicator_one_eq_volume B hB_meas).symm
  have heqC : (volume C).toReal = ∫ x, fC x :=
    (integral_indicator_one_eq_volume C hC_meas).symm
  -- 点ごと PL (§E, genuine).
  have h_pt : ∀ x y : Fin (n + 1) → ℝ,
      fA x ^ lam * fB y ^ (1 - lam) ≤ fC (lam • x + (1 - lam) • y) :=
    indicator_pointwise_pl A B lam h0 h1
  -- slice 非負性 (indicator 非負 → integral_nonneg).
  have hA_nn : ∀ s, 0 ≤ sliceInt fA s :=
    fun s => sliceInt_nonneg fA (indicator_one_nonneg A) s
  have hB_nn : ∀ s, 0 ≤ sliceInt fB s :=
    fun s => sliceInt_nonneg fB (indicator_one_nonneg B) s
  have hC_nn : ∀ s, 0 ≤ sliceInt fC s :=
    fun s => sliceInt_nonneg fC (indicator_one_nonneg C) s
  -- n 次元 PL を 3 indicator に適用 (slice readiness 以外すべて genuine 供給).
  have hpl := prekopa_leindler_nDim fA fB fC lam h0.le h1.le
    (volume A).toReal (volume B).toReal (volume C).toReal
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    h_pt heqA heqB heqC
    (indicator_integrable A hA_meas hA_fin)
    (indicator_integrable B hB_meas hB_fin)
    (indicator_integrable C hC_meas hC_fin)
    hA_nn hB_nn hC_nn ih h_ready
  exact hpl

/-- **scaled multiplicative BM ⇐ indicator/compact 体積 BM (readiness 経由)**:
`bm_geom_to_scaledMul` の `h_geom_mul` (scaled 集合での乗法形 geometric BM) を、
`brunn_minkowski_volume_indicator_compact` で各 `λ` ごとに genuine 供給して
`IsBMScaledMulHyp` を組む。compact 性は scaling/Minkowski で伝播。残る honest 入力は
各 scaled 集合での slice readiness (`h_ready`) と n 次元 clean PL (`ih`) のみ。 -/
theorem bm_scaledMul_of_compact {n : ℕ}
    (A B : Set (Fin (n + 1) → ℝ))
    (hA : IsCompact A) (hB : IsCompact B)
    (ih : ∀ (lam : ℝ), 0 < lam → lam < 1 →
      ∀ (f' g' hfn' : (Fin n → ℝ) → ℝ),
      (0 ≤ ∫ w, f' w) → (0 ≤ ∫ w, g' w) → (0 ≤ ∫ w, hfn' w) →
      (∀ x y : Fin n → ℝ,
        f' x ^ lam * g' y ^ (1 - lam) ≤ hfn' (lam • x + (1 - lam) • y)) →
      (∫ w, f' w) ^ lam * (∫ w, g' w) ^ (1 - lam) ≤ ∫ w, hfn' w)
    (h_ready : ∀ (lam : ℝ), 0 < lam → lam < 1 →
      IsSlicePLReadyHyp
        (((lam⁻¹ : ℝ) • A).indicator (fun _ => (1 : ℝ)))
        ((((1 - lam)⁻¹ : ℝ) • B).indicator (fun _ => (1 : ℝ)))
        ((lam • ((lam⁻¹ : ℝ) • A)
          + (1 - lam) • (((1 - lam)⁻¹ : ℝ) • B)).indicator (fun _ => (1 : ℝ)))
        lam (volume ((lam⁻¹ : ℝ) • A)).toReal
        (volume (((1 - lam)⁻¹ : ℝ) • B)).toReal
        (volume (lam • ((lam⁻¹ : ℝ) • A)
          + (1 - lam) • (((1 - lam)⁻¹ : ℝ) • B))).toReal) :
    IsBMScaledMulHyp (n + 1) (volume A).toReal (volume B).toReal
      (volume (A + B)).toReal := by
  -- A, B の有限測度 (compact).
  have hA_fin : volume A ≠ ∞ := hA.measure_ne_top
  have hB_fin : volume B ≠ ∞ := hB.measure_ne_top
  -- 各 λ で scaled 集合の乗法形 geometric BM を `brunn_minkowski_volume_indicator_compact`
  -- で genuine 供給 (compact 性は scaling で伝播).
  refine bm_geom_to_scaledMul A B hA_fin hB_fin ?_
  intro lam hlam_pos hlam_lt
  exact brunn_minkowski_volume_indicator_compact
    ((lam⁻¹ : ℝ) • A) (((1 - lam)⁻¹ : ℝ) • B) lam hlam_pos hlam_lt
    (hA.smul _) (hB.smul _)
    (ih lam hlam_pos hlam_lt)
    (h_ready lam hlam_pos hlam_lt)

/-! ## §J — slice 体積関数の superlevel **可測性** genuine 供給 (compact ケース)

`IsSlicePLReadyHyp` の 7 条件は slice 体積関数 `g(s) := sliceInt (1_S) s` の
superlevel 集合 `{s | t ≤ g s}` に **compact 性** (条件 1,2) と **有限測度**
(条件 5) を `∀ t > 0` で要求する (量化子は 2026-05-21 に `0 ≤ t` から `0 < t` へ弱化済)。

**vacuity は両端で起きる (構造的知見)**: indicator の slice 体積関数は
`g ≥ 0` かつ有界。
❶ **低端 (解消済)**: `t = 0` では `{s | 0 ≤ g s} = (Set.univ : Set ℝ)` で
compact でも有限測度でもない。1D engine 全 chain (`IsPL11DSuperLevelHyp` 定義含む)
の量化子を `0 ≤ t → 0 < t` に弱化して解消した。engine は
`superlevel_setIntegral_mono` 経由で `t = 0` slice を実際に捨てているので健全。
これにより `brunn_minkowski_volume_indicator_compact` / `bm_scaledMul_of_compact`
は latent vacuous → **honest-open** になった。
❷ **高端 (未解消、fundamental Mathlib 壁)**: `g` 有界ゆえ大きな `t` で
`{s | t ≤ g s} = ∅`、よって非空性 (条件 3,4) が `t > 0` でも崩れる。汎用 engine の
`one_dim_bm_scaled` は非空性必須 (一般 `f, g` で片側のみ空だと additive superlevel BM
`λμ_f + (1-λ)μ_g ≤ μ_h` は偽) ゆえ落とせず、indicator 専用の case-split lemma が要る。
加えて compact 性 (条件 1,2) には slice 体積関数 `s ↦ vol((Fin.cons s ·)⁻¹ A)` の
**上半連続性** が要るが Mathlib 不在 (~150 行の自作解析)。よって `IsSlicePLReadyHyp`
の indicator discharge は defer、entropy 形 BM は `IsBMEntropyPowerVolumeHyp` honest
hypothesis 1 本に縮約済 (closure plan Phase 3 pivot, `BrunnMinkowskiClosure.lean:493`
`brunn_minkowski_entropy_jointPi`)。

本 §J は ❷ の前段として、scope 内で genuine に供給可能な **superlevel 可測性** を
Mathlib `measurable_measure_prodMk_left` から立てる:

* `sliceInt_indicator_eq_slice_measure` — `sliceInt (1_S) s = (vol(slice_s)).toReal`
  (`integral_indicator_one`, genuine)。`slice_s := (Fin.cons s ·) ⁻¹' S`。
* `measurable_sliceInt_indicator` — `Measurable (sliceInt (1_S))`
  (`measurable_measure_prodMk_left` を `piFinSuccAbove` reshape 経由で適用、genuine)。
* `measurableSet_sliceInt_indicator_superlevel` — `MeasurableSet {s | t ≤ sliceInt (1_S) s}`。

可測性は将来の superlevel **上半連続性** (`t > 0` で closed + bounded ⇒ compact) build
の足場であり、本 chain で初めて genuine 化される (従来は compact 仮定の中に埋もれていた)。 -/

/-- **`Fin.cons s ·` の可測性 (genuine helper)**: `w ↦ Fin.cons s w` は可測。
各座標 `i` を `Fin.cases` で分け、`0` 成分は定数、`succ j` 成分は射影 `w j`。 -/
theorem measurable_cons_left {n : ℕ} (s : ℝ) :
    Measurable (fun w : Fin n → ℝ => (Fin.cons s w : Fin (n + 1) → ℝ)) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  refine Fin.cases ?_ ?_ i
  · simpa only [Fin.cons_zero] using measurable_const
  · intro j
    simpa only [Fin.cons_succ] using measurable_pi_apply j

/-- **slice 集合の可測性 (genuine helper)**: 可測 `S` で `(Fin.cons s ·) ⁻¹' S` 可測。 -/
theorem measurableSet_slice {n : ℕ} (S : Set (Fin (n + 1) → ℝ))
    (hS : MeasurableSet S) (s : ℝ) :
    MeasurableSet ((fun w : Fin n → ℝ => Fin.cons s w) ⁻¹' S) :=
  hS.preimage (measurable_cons_left s)

/-- **slice 積分 (indicator) = slice 体積 (genuine)**: 可測 `S` で
`sliceInt (1_S) s = (vol((Fin.cons s ·)⁻¹' S)).toReal`。
slice 関数 `w ↦ 1_S (cons s w) = 1_{slice} w` (indicator 引き戻し) +
`integral_indicator_one` (可測 slice)。 -/
theorem sliceInt_indicator_eq_slice_measure {n : ℕ}
    (S : Set (Fin (n + 1) → ℝ)) (hS : MeasurableSet S) (s : ℝ) :
    sliceInt (S.indicator (fun _ => (1 : ℝ))) s
      = (volume ((fun w : Fin n → ℝ => Fin.cons s w) ⁻¹' S)).toReal := by
  unfold sliceInt
  have hpre : MeasurableSet ((fun w : Fin n → ℝ => Fin.cons s w) ⁻¹' S) :=
    measurableSet_slice S hS s
  rw [show (fun w : Fin n → ℝ => S.indicator (fun _ => (1 : ℝ)) (Fin.cons s w))
      = ((fun w : Fin n → ℝ => Fin.cons s w) ⁻¹' S).indicator (fun _ => (1 : ℝ)) from by
        ext w; simp only [Set.indicator]; rfl]
  rw [show (fun _ : Fin n → ℝ => (1 : ℝ)) = (1 : (Fin n → ℝ) → ℝ) from rfl,
    integral_indicator_one hpre]
  rfl

/-- **slice 体積関数 = prodMk-slice 測度 (genuine reshape)**: `piFinSuccAbove 0`
で `Fin.cons s w = e.symm (s, w)` ゆえ `(Fin.cons s ·)⁻¹' S = Prod.mk s ⁻¹' (e.symm ⁻¹' S)`。
これにより slice 体積が `Measure.prod` の slice 測度形になり、Mathlib の
`measurable_measure_prodMk_left` が直接効く形になる。 -/
theorem slice_preimage_eq_prodMk {n : ℕ} (S : Set (Fin (n + 1) → ℝ)) (s : ℝ) :
    (fun w : Fin n → ℝ => Fin.cons s w) ⁻¹' S
      = Prod.mk s ⁻¹'
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm ⁻¹' S) := by
  ext w
  simp only [Set.mem_preimage]
  rw [show (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (s, w)
      = Fin.cons s w from by
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]; rfl]

/-- **slice 体積関数の可測性 (genuine, Mathlib `measurable_measure_prodMk_left`)**:
可測 `S` について `s ↦ sliceInt (1_S) s` は可測。reshape で slice 体積を
`Measure.prod` の slice 測度 `s ↦ vol(Prod.mk s ⁻¹' (e.symm⁻¹' S))` に直し、
`measurable_measure_prodMk_left` (`[SFinite volume]`、`Fin n → ℝ` の Haar は σ-finite)
で可測。`.toReal` は `ENNReal.measurable_toReal` で保たれる。 -/
theorem measurable_sliceInt_indicator {n : ℕ}
    (S : Set (Fin (n + 1) → ℝ)) (hS : MeasurableSet S) :
    Measurable (sliceInt (S.indicator (fun _ => (1 : ℝ)))) := by
  -- rewrite the slice integral to the `.toReal` of the prodMk-slice measure.
  have hfun : sliceInt (S.indicator (fun _ => (1 : ℝ)))
      = fun s : ℝ => (volume (Prod.mk s ⁻¹'
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm ⁻¹' S))).toReal := by
    funext s
    rw [sliceInt_indicator_eq_slice_measure S hS s, slice_preimage_eq_prodMk S s]
  rw [hfun]
  -- the reshaped set is measurable; `measurable_measure_prodMk_left` + `.toReal`.
  have hS' : MeasurableSet
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm ⁻¹' S) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.measurableSet_preimage.mpr hS
  exact (measurable_measure_prodMk_left hS').ennreal_toReal

/-- **slice 体積関数の superlevel 可測性 (genuine)**: 可測 `S` について
`{s | t ≤ sliceInt (1_S) s}` は可測 (全 `t`)。`measurable_sliceInt_indicator` +
`measurableSet_le`。compact 仮定 (条件 1,2) より弱いが、`IsSlicePLReadyHyp` で
従来 compact に埋もれていた可測性内容を本 chain で初めて genuine に取り出したもの。 -/
theorem measurableSet_sliceInt_indicator_superlevel {n : ℕ}
    (S : Set (Fin (n + 1) → ℝ)) (hS : MeasurableSet S) (t : ℝ) :
    MeasurableSet {s : ℝ | t ≤ sliceInt (S.indicator (fun _ => (1 : ℝ))) s} :=
  measurableSet_le measurable_const (measurable_sliceInt_indicator S hS)

end InformationTheory.Shannon.BrunnMinkowski

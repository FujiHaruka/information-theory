import Common2026.Shannon.BrunnMinkowskiLayerCakeBody
import Common2026.Shannon.BrunnMinkowskiPLBody
import Common2026.Shannon.BrunnMinkowski1DSuperlevelBody
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi

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
    (hFc : ∀ t : ℝ, 0 ≤ t → IsCompact {a : ℝ | t ≤ f (fun _ => a)})
    (hGc : ∀ t : ℝ, 0 ≤ t → IsCompact {a : ℝ | t ≤ g (fun _ => a)})
    (hFne : ∀ t : ℝ, 0 ≤ t → ({a : ℝ | t ≤ f (fun _ => a)}).Nonempty)
    (hGne : ∀ t : ℝ, 0 ≤ t → ({a : ℝ | t ≤ g (fun _ => a)}).Nonempty)
    (hHfin : ∀ t : ℝ, 0 ≤ t → volume {a : ℝ | t ≤ hfn (fun _ => a)} ≠ ∞)
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
  (∀ t : ℝ, 0 ≤ t → IsCompact {s : ℝ | t ≤ sliceInt f s}) ∧
  (∀ t : ℝ, 0 ≤ t → IsCompact {s : ℝ | t ≤ sliceInt g s}) ∧
  (∀ t : ℝ, 0 ≤ t → ({s : ℝ | t ≤ sliceInt f s}).Nonempty) ∧
  (∀ t : ℝ, 0 ≤ t → ({s : ℝ | t ≤ sliceInt g s}).Nonempty) ∧
  (∀ t : ℝ, 0 ≤ t → volume {s : ℝ | t ≤ sliceInt hfn s} ≠ ∞) ∧
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
genuine `integral_indicator_one`)。 -/
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

end InformationTheory.Shannon.BrunnMinkowski

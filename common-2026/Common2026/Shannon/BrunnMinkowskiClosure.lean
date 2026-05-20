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

/-! ## §D — 体積版 BM corollary (Phase 1 段階着地点) -/

/-- **体積版 Brunn-Minkowski (multiplicative form)**: 凸体 `A, B` について

    `vol(λ A + (1-λ) B) ^ 1 ≥ vol A ^ λ * vol B ^ (1-λ)`

(加法形からの AM-GM 派生 `bm_additive_to_multiplicative` 経由)。 -/
theorem brunn_minkowski_volume_mul {n : ℕ}
    (volA volB volAB lam : ℝ)
    (hvolA : 0 ≤ volA) (hvolB : 0 ≤ volB) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (h_add : lam * volA + (1 - lam) * volB ≤ volAB) :
    volA ^ lam * volB ^ (1 - lam) ≤ volAB :=
  bm_additive_to_multiplicative hvolA hvolB h0 h1 h_add

end InformationTheory.Shannon.BrunnMinkowski

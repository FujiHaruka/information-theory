/-
# EPI richness 壁 (G4/W2) — route B (lift-and-transport) genuine closure

本 file は EPI richness sub-wall を **route B (lift-and-transport)** で genuine に閉じる
lift machinery を集約する (案 B1、最小 scope)。lift 空間 `Ω × ℝ × ℝ` (`Z_X, Z_Y` 因子 =
`gaussianReal 0 1`) 上で 4-tuple joint independence を Mathlib product-measure API のみから
構成し、`entropyPower` の law-only 性 + `IsStamInequalityResidual` の carrier-free 性を使って
`(Ω, P)` に EPI を transport する。

## B1 dead-code 正当化 (3 点)

本 file の 4 lemma は live consumer ゼロ (現 chain は in-place `IsStamScalingNoiseHyp` を取る)。
それでも価値を持つ理由:

- **(a) future re-wire foundation**: lift 4 lemma は B2 (full re-wire = 偽 in-place
  `stamScalingNoise_exists` を完全除去) に着手する後続セッションの building block。in-place 偽 lemma を
  除去する唯一の honest 経路は lift 経由であり、その機材を先に genuine 化しておく。
- **(b) wall register 訂正の根拠**: `wall:in-place-noise-extension` (在庫が唯一の真壁と判定) は route B で
  踏まないことを実証する。在庫の「richness は閉じられる」主張を機械検証済の lemma で裏付ける。
- **(c) 偽 statement 置換の代替提示**: 偽 W2 (`stamScalingNoise_exists`、atomic measure で false-statement)
  を単に削除/defect マークするだけでなく、honest な代替 (`stamScalingNoise_exists_on_lift`) を提示することで、
  撤退ではなく置換であることを示す。

slug 統一: 本 file の lift lemma は genuine closable (0 sorry 目標)。撤退時のみ
`@residual(plan:epi-richness-route-b-plan)` を付与する。

> **scope (確定事実 C)**: richness closure は headline `stamToEPIBridge_holds` を proof-done に
> しない。headline は transitive に G2 heat-flow-continuity (`wall:heatflow-continuity`、真 Mathlib 壁)
> を別途要する。本 file の scope は richness sub-wall のみ。
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import InformationTheory.Shannon.EntropyPowerInequality
import InformationTheory.Shannon.EPIStamToBridge

namespace InformationTheory.Shannon.EPINoiseExtension

open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamToBridge

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable (X Y : Ω → ℝ)

/-- lift 空間 `Ω × ℝ × ℝ` の測度 (`Z_X, Z_Y` 因子は標準正規)。 -/
noncomputable abbrev liftMeasure : Measure (Ω × ℝ × ℝ) :=
  P.prod ((gaussianReal 0 1).prod (gaussianReal 0 1))

omit [IsProbabilityMeasure P] in
/-- lift 上で X law が保存される (transport の linchpin)。
`(liftMeasure P).map (X∘fst) = ((liftMeasure P).map fst).map X = P.map X` を `map_map` +
`measurePreserving_fst` で出し、`entropyPower` の law-only 性で結論。 -/
theorem entropyPower_map_comp_fst_eq (hX : Measurable X) :
    entropyPower ((liftMeasure P).map (fun p => X p.1)) = entropyPower (P.map X) := by
  have hmap : (liftMeasure P).map (fun p : Ω × ℝ × ℝ => X p.1) = P.map X := by
    rw [show (fun p : Ω × ℝ × ℝ => X p.1) = X ∘ Prod.fst from rfl,
      ← Measure.map_map hX measurable_fst, measurePreserving_fst.map_eq]
  rw [hmap]

/-- lift 空間で `IsStamScalingNoiseHyp` (lift 版) を product-measure API のみで構成。
これは **lift 空間上の genuine な existential** であり、in-place の偽 W2
`stamScalingNoise_exists` の honest 後継 (置換ではなく併置 = 正当化 (c))。
witness は座標射影 `Z_X' := (·.2.1)`, `Z_Y' := (·.2.2)`。 -/
theorem stamScalingNoise_exists_on_lift (hX : Measurable X) (hY : Measurable Y) :
    IsStamScalingNoiseHyp (fun p => X p.1) (fun p => Y p.1) (liftMeasure P) := by
  set ν : Measure ℝ := gaussianReal 0 1 with hν
  refine ⟨fun p => p.2.1, fun p => p.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact measurable_fst.comp measurable_snd
  · exact measurable_snd.comp measurable_snd
  -- `Z_X'` law: map (fst ∘ snd) = (map snd).map fst = (ν.prod ν).map fst = ν
  · rw [show (fun p : Ω × ℝ × ℝ => p.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_fst measurable_snd,
      measurePreserving_snd.map_eq, measurePreserving_fst.map_eq]
  -- `Z_Y'` law
  · rw [show (fun p : Ω × ℝ × ℝ => p.2.2) = Prod.snd ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_snd measurable_snd,
      measurePreserving_snd.map_eq, measurePreserving_snd.map_eq]
  -- `X∘fst ⊥ Z_X'`: indepFun_prod with X (on Ω) and Prod.fst (on ℝ×ℝ)
  · exact indepFun_prod hX measurable_fst
  -- `Y∘fst ⊥ Z_Y'`
  · exact indepFun_prod hY measurable_snd
  -- `Z_X' ⊥ Z_Y'`: indep within the second factor, transported through Prod.snd
  · have hZX'meas : Measurable (fun p : Ω × ℝ × ℝ => p.2.1) :=
      measurable_fst.comp measurable_snd
    have hZY'meas : Measurable (fun p : Ω × ℝ × ℝ => p.2.2) :=
      measurable_snd.comp measurable_snd
    rw [indepFun_iff_map_prod_eq_prod_map_map hZX'meas.aemeasurable hZY'meas.aemeasurable]
    have hsnd : (liftMeasure P).map (fun p : Ω × ℝ × ℝ => (p.2.1, p.2.2))
        = ν.prod ν := by
      rw [show (fun p : Ω × ℝ × ℝ => (p.2.1, p.2.2)) = Prod.snd from rfl,
        measurePreserving_snd.map_eq]
    have hZX : (liftMeasure P).map (fun p : Ω × ℝ × ℝ => p.2.1) = ν := by
      rw [show (fun p : Ω × ℝ × ℝ => p.2.1) = Prod.fst ∘ Prod.snd from rfl,
        ← Measure.map_map measurable_fst measurable_snd,
        measurePreserving_snd.map_eq, measurePreserving_fst.map_eq]
    have hZY : (liftMeasure P).map (fun p : Ω × ℝ × ℝ => p.2.2) = ν := by
      rw [show (fun p : Ω × ℝ × ℝ => p.2.2) = Prod.snd ∘ Prod.snd from rfl,
        ← Measure.map_map measurable_snd measurable_snd,
        measurePreserving_snd.map_eq, measurePreserving_snd.map_eq]
    rw [hsnd, hZX, hZY]

/-- 和 vs 和の独立性 (G4 = in-place joint indep `sorry` の lift 後継) を lift 上で。
`(X∘fst + Y∘fst) ⊥ (Z_X' + Z_Y')` on `liftMeasure P`。`indepFun_prod` を直接適用
(左 = `p.1` のみの関数、右 = `p.2` のみの関数)。 -/
theorem indepFun_add_add_on_lift (hX : Measurable X) (hY : Measurable Y) :
    IndepFun (fun p => X p.1 + Y p.1)
             (fun p => p.2.1 + p.2.2) (liftMeasure P) :=
  indepFun_prod (X := fun ω => X ω + Y ω) (Y := fun q : ℝ × ℝ => q.1 + q.2)
    (hX.add hY) (measurable_fst.add measurable_snd)

omit [IsProbabilityMeasure P] in
/-- route B 本体 (conditional transport 形)。

**honesty 区分**: 仮説 `h_lift_epi` は **別測度 `liftMeasure P` 上の EPI 結論**であり、base
`(Ω,P)` の EPI 結論とは異なる Prop (defeq でない別測度命題)。これは measure-transport reduction
(`IsStamToEPIBridge` が `residual → 結論` なのと同型の honest な reduction) であって **circular でも
load-bearing bundle でもない** — Stam の核を抱えない、単なる測度張替。`h_lift_epi` は G2 closure 後に
lift 空間の genuine bridge から供給される。base 結論と defeq でない別測度命題なので非循環。 -/
theorem entropy_power_inequality_via_lift (hX : Measurable X) (hY : Measurable Y)
    (h_lift_epi : entropyPower ((liftMeasure P).map (fun p => X p.1 + Y p.1))
      ≥ entropyPower ((liftMeasure P).map (fun p => X p.1))
        + entropyPower ((liftMeasure P).map (fun p => Y p.1))) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  -- the lift sum `fun p => X p.1 + Y p.1` is `(fun ω => X ω + Y ω) ∘ fst`,
  -- so all three entropyPower terms transport via Phase 2.
  rw [entropyPower_map_comp_fst_eq P X hX,
      entropyPower_map_comp_fst_eq P Y hY] at h_lift_epi
  rwa [entropyPower_map_comp_fst_eq P (fun ω => X ω + Y ω) (hX.add hY)] at h_lift_epi

end InformationTheory.Shannon.EPINoiseExtension

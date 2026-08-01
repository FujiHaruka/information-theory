import InformationTheory.Fano.Measure
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Bridge
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.Entropy
import InformationTheory.Shannon.MaxEntropy.Basic
import InformationTheory.Shannon.Pi
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Slepian–Wolf single-shot converse

Two sources `(Xs, Ys) : Ω → α × β` are compressed by independent encoders
`eX, eY` and reconstructed by a joint decoder `dec`. From an error probability
`Pe ≤ ε` one derives three rate lower bounds:

```
log Mx        ≥ H(X | Y)   - δ(Pe)
log My        ≥ H(Y | X)   - δ(Pe)
log Mx+log My ≥ H(X, Y)    - δ(Pe)
```

## Main statements

* `fano_inequality_with_side_info` — Fano with a paired conditioner `(Yo, Si)`.
* `entropy_ge_condEntropy` — conditioning never increases entropy, `H(W | Y) ≤ H(W)`.
* `slepian_wolf_converse_X` / `_Y` / `_sum` — the three rate lower bounds.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-! ## Fano with side information -/

/-- Fano with side information: `condEntropy μ Xs (Yo, Si) ≤ binEntropy(Pe) + Pe · log(|X|-1)`,
with the paired conditioner `(Yo, Si)`.

See also `fano_inequality_measure_theoretic`. -/
@[entry_point]
theorem fano_inequality_with_side_info
    {Ω : Type*} [MeasurableSpace Ω]
    {X : Type*} [Fintype X] [Nonempty X]
      [MeasurableSpace X] [MeasurableSingletonClass X]
    {Y S : Type*} [MeasurableSpace Y] [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Si : Ω → S)
    (decoder : Y × S → X)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hSi : Measurable Si)
    (hdec : Measurable decoder)
    (hcard : 2 ≤ Fintype.card X) :
    InformationTheory.MeasureFano.condEntropy μ Xs (fun ω ↦ (Yo ω, Si ω)) ≤
      Real.binEntropy
        (InformationTheory.MeasureFano.errorProb μ Xs
          (fun ω ↦ (Yo ω, Si ω)) decoder)
        + InformationTheory.MeasureFano.errorProb μ Xs
            (fun ω ↦ (Yo ω, Si ω)) decoder
          * Real.log ((Fintype.card X : ℝ) - 1) := by
  have hpair : Measurable (fun ω ↦ (Yo ω, Si ω)) := hYo.prodMk hSi
  exact InformationTheory.MeasureFano.fano_inequality_measure_theoretic
    μ Xs (fun ω ↦ (Yo ω, Si ω)) decoder hXs hpair hdec hcard

/-! ## Conditioning never increases entropy -/

/-- Conditioning never increases entropy: `H(W | Y) ≤ H(W)`. -/
@[entry_point]
theorem entropy_ge_condEntropy
    {Ω : Type*} [MeasurableSpace Ω]
    {W : Type*} [Fintype W] [Nonempty W]
      [MeasurableSpace W] [MeasurableSingletonClass W]
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ws : Ω → W) (Yo : Ω → Y)
    (hWs : Measurable Ws) (hYo : Measurable Yo) :
    InformationTheory.MeasureFano.condEntropy μ Ws Yo ≤ entropy μ Ws := by
  have h_bridge :
      (mutualInfo μ Ws Yo).toReal
        = entropy μ Ws - InformationTheory.MeasureFano.condEntropy μ Ws Yo :=
    mutualInfo_eq_entropy_sub_condEntropy μ Ws Yo hWs hYo
  have h_nn : 0 ≤ (mutualInfo μ Ws Yo).toReal := ENNReal.toReal_nonneg
  linarith

/-! ## The three rate lower bounds

Each bound chains `MaxEntropy.entropy_le_log_card`, `entropy_ge_condEntropy`, a
conditional mutual-information bridge, and `fano_inequality_with_side_info`.
The Fano penalty `δ(Pe)` is written inline as
`Real.binEntropy Pe + Pe · Real.log (|·| - 1)`, with the alphabet `|α|` for the
`X` bound, `|β|` for the `Y` bound, and `|α × β|` for the sum bound.
-/

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β : Type*} [Fintype β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Slepian–Wolf converse, X bound:
`log Mx ≥ H(X | Y) - h(Pe_X) - Pe_X · log(|α| - 1)`,
where `Pe_X = μ {ω | Xs ω ≠ decX (Ys ω, eX (Xs ω))}` is the marginal `X` error and
`decX : β × Fin Mx → α` is the `X` component of the joint decoder,
`decX(y, m) := (dec(m, eY y)).1`. -/
@[entry_point]
theorem slepian_wolf_converse_X
    {Mx My : ℕ} [NeZero Mx] [NeZero My]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → α) (Ys : Ω → β)
    (eX : α → Fin Mx) (eY : β → Fin My)
    (dec : Fin Mx × Fin My → α × β)
    (hXs : Measurable Xs) (hYs : Measurable Ys)
    (hcard : 2 ≤ Fintype.card α) :
    Real.log (Mx : ℝ) ≥
      InformationTheory.MeasureFano.condEntropy μ Xs Ys
        - Real.binEntropy
            (InformationTheory.MeasureFano.errorProb μ Xs
              (fun ω ↦ (Ys ω, eX (Xs ω)))
              (fun p : β × Fin Mx ↦ (dec (p.2, eY p.1)).1))
        - InformationTheory.MeasureFano.errorProb μ Xs
            (fun ω ↦ (Ys ω, eX (Xs ω)))
            (fun p : β × Fin Mx ↦ (dec (p.2, eY p.1)).1)
          * Real.log ((Fintype.card α : ℝ) - 1) := by
  -- Abbreviations.
  set EX : Ω → Fin Mx := fun ω ↦ eX (Xs ω) with hEX_def
  set decX : β × Fin Mx → α := fun p ↦ (dec (p.2, eY p.1)).1 with hdecX_def
  set Pe_X := InformationTheory.MeasureFano.errorProb μ Xs
    (fun ω ↦ (Ys ω, EX ω)) decX with hPe_def
  -- Measurability (all Fintype targets ⇒ auto-measurable).
  have hEX_aux : Measurable eX := measurable_of_countable _
  have hdec : Measurable decX := measurable_of_countable _
  have hEX : Measurable EX := hEX_aux.comp hXs
  -- Mx as positive cardinal: `Fintype.card (Fin Mx) = Mx`.
  have hcard_Fin : (Fintype.card (Fin Mx) : ℝ) = (Mx : ℝ) := by
    rw [Fintype.card_fin]
  -- Step A: log Mx ≥ H(EX) by MaxEntropy.entropy_le_log_card.
  have h_step_A : entropy μ EX ≤ Real.log (Mx : ℝ) := by
    have := MaxEntropy.entropy_le_log_card μ EX hEX
    rwa [hcard_Fin] at this
  -- Step B: H(EX) ≥ H(EX | Ys) by entropy_ge_condEntropy.
  have h_step_B :
      InformationTheory.MeasureFano.condEntropy μ EX Ys ≤ entropy μ EX :=
    entropy_ge_condEntropy μ EX Ys hEX hYs
  -- Step C (key): H(X | Ys) - H(X | Ys, EX) = H(EX | Ys) - H(EX | Ys, Xs)  ≤ H(EX | Ys).
  -- Use `condMutualInfo_eq_condEntropy_sub_condEntropy` twice + `condMutualInfo_comm`.
  have h_bridge_X :
      (condMutualInfo μ Xs EX Ys).toReal
        = InformationTheory.MeasureFano.condEntropy μ Xs Ys
          - InformationTheory.MeasureFano.condEntropy μ Xs (fun ω ↦ (Ys ω, EX ω)) :=
    condMutualInfo_eq_condEntropy_sub_condEntropy μ Xs Ys EX hXs hYs hEX
  have h_bridge_EX :
      (condMutualInfo μ EX Xs Ys).toReal
        = InformationTheory.MeasureFano.condEntropy μ EX Ys
          - InformationTheory.MeasureFano.condEntropy μ EX (fun ω ↦ (Ys ω, Xs ω)) :=
    condMutualInfo_eq_condEntropy_sub_condEntropy μ EX Ys Xs hEX hYs hXs
  have h_comm : condMutualInfo μ Xs EX Ys = condMutualInfo μ EX Xs Ys :=
    condMutualInfo_comm μ Xs EX Ys hXs hEX hYs
  have h_step_C :
      InformationTheory.MeasureFano.condEntropy μ Xs Ys
        - InformationTheory.MeasureFano.condEntropy μ Xs (fun ω ↦ (Ys ω, EX ω))
          ≤ InformationTheory.MeasureFano.condEntropy μ EX Ys := by
    have h_eq :
        InformationTheory.MeasureFano.condEntropy μ Xs Ys
          - InformationTheory.MeasureFano.condEntropy μ Xs (fun ω ↦ (Ys ω, EX ω))
            = InformationTheory.MeasureFano.condEntropy μ EX Ys
              - InformationTheory.MeasureFano.condEntropy μ EX (fun ω ↦ (Ys ω, Xs ω)) := by
      rw [← h_bridge_X, h_comm, h_bridge_EX]
    rw [h_eq]
    have h_nn := condEntropy_nonneg μ EX (fun ω ↦ (Ys ω, Xs ω))
    linarith
  -- Step D: side info Fano with Yo := Ys, Si := EX. Conditioner = (Ys, EX), decoder = decX.
  have h_step_D :
      InformationTheory.MeasureFano.condEntropy μ Xs (fun ω ↦ (Ys ω, EX ω))
        ≤ Real.binEntropy Pe_X + Pe_X * Real.log ((Fintype.card α : ℝ) - 1) :=
    fano_inequality_with_side_info μ Xs Ys EX decX hXs hYs hEX hdec hcard
  -- Final: chain Steps A-D.
  -- log Mx ≥ H(EX) ≥ H(EX | Ys) ≥ H(X | Ys) - H(X | Ys, EX) ≥ H(X | Ys) - δ(Pe_X)
  linarith

/-- Slepian–Wolf converse, Y bound (the `X`/`Y`-symmetric form):
`log My ≥ H(Y | X) - h(Pe_Y) - Pe_Y · log(|β| - 1)`. -/
@[entry_point]
theorem slepian_wolf_converse_Y
    {Mx My : ℕ} [NeZero Mx] [NeZero My]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → α) (Ys : Ω → β)
    (eX : α → Fin Mx) (eY : β → Fin My)
    (dec : Fin Mx × Fin My → α × β)
    (hXs : Measurable Xs) (hYs : Measurable Ys)
    (hcard : 2 ≤ Fintype.card β) :
    Real.log (My : ℝ) ≥
      InformationTheory.MeasureFano.condEntropy μ Ys Xs
        - Real.binEntropy
            (InformationTheory.MeasureFano.errorProb μ Ys
              (fun ω ↦ (Xs ω, eY (Ys ω)))
              (fun p : α × Fin My ↦ (dec (eX p.1, p.2)).2))
        - InformationTheory.MeasureFano.errorProb μ Ys
            (fun ω ↦ (Xs ω, eY (Ys ω)))
            (fun p : α × Fin My ↦ (dec (eX p.1, p.2)).2)
          * Real.log ((Fintype.card β : ℝ) - 1) := by
  -- Symmetric to X bound with X ↔ Y, Mx ↔ My.
  set EY : Ω → Fin My := fun ω ↦ eY (Ys ω) with hEY_def
  set decY : α × Fin My → β := fun p ↦ (dec (eX p.1, p.2)).2 with hdecY_def
  set Pe_Y := InformationTheory.MeasureFano.errorProb μ Ys
    (fun ω ↦ (Xs ω, EY ω)) decY with hPe_def
  have hEY_aux : Measurable eY := measurable_of_countable _
  have hdec : Measurable decY := measurable_of_countable _
  have hEY : Measurable EY := hEY_aux.comp hYs
  have hcard_Fin : (Fintype.card (Fin My) : ℝ) = (My : ℝ) := by
    rw [Fintype.card_fin]
  have h_step_A : entropy μ EY ≤ Real.log (My : ℝ) := by
    have := MaxEntropy.entropy_le_log_card μ EY hEY
    rwa [hcard_Fin] at this
  have h_step_B :
      InformationTheory.MeasureFano.condEntropy μ EY Xs ≤ entropy μ EY :=
    entropy_ge_condEntropy μ EY Xs hEY hXs
  have h_bridge_Y :
      (condMutualInfo μ Ys EY Xs).toReal
        = InformationTheory.MeasureFano.condEntropy μ Ys Xs
          - InformationTheory.MeasureFano.condEntropy μ Ys (fun ω ↦ (Xs ω, EY ω)) :=
    condMutualInfo_eq_condEntropy_sub_condEntropy μ Ys Xs EY hYs hXs hEY
  have h_bridge_EY :
      (condMutualInfo μ EY Ys Xs).toReal
        = InformationTheory.MeasureFano.condEntropy μ EY Xs
          - InformationTheory.MeasureFano.condEntropy μ EY (fun ω ↦ (Xs ω, Ys ω)) :=
    condMutualInfo_eq_condEntropy_sub_condEntropy μ EY Xs Ys hEY hXs hYs
  have h_comm : condMutualInfo μ Ys EY Xs = condMutualInfo μ EY Ys Xs :=
    condMutualInfo_comm μ Ys EY Xs hYs hEY hXs
  have h_step_C :
      InformationTheory.MeasureFano.condEntropy μ Ys Xs
        - InformationTheory.MeasureFano.condEntropy μ Ys (fun ω ↦ (Xs ω, EY ω))
          ≤ InformationTheory.MeasureFano.condEntropy μ EY Xs := by
    have h_eq :
        InformationTheory.MeasureFano.condEntropy μ Ys Xs
          - InformationTheory.MeasureFano.condEntropy μ Ys (fun ω ↦ (Xs ω, EY ω))
            = InformationTheory.MeasureFano.condEntropy μ EY Xs
              - InformationTheory.MeasureFano.condEntropy μ EY (fun ω ↦ (Xs ω, Ys ω)) := by
      rw [← h_bridge_Y, h_comm, h_bridge_EY]
    rw [h_eq]
    have h_nn := condEntropy_nonneg μ EY (fun ω ↦ (Xs ω, Ys ω))
    linarith
  have h_step_D :
      InformationTheory.MeasureFano.condEntropy μ Ys (fun ω ↦ (Xs ω, EY ω))
        ≤ Real.binEntropy Pe_Y + Pe_Y * Real.log ((Fintype.card β : ℝ) - 1) :=
    fano_inequality_with_side_info μ Ys Xs EY decY hYs hXs hEY hdec hcard
  linarith

/-- Slepian–Wolf converse, sum bound:
`log Mx + log My ≥ H(X, Y) - h(Pe) - Pe · log(|α × β| - 1)`,
where `Pe = μ {ω | (Xs ω, Ys ω) ≠ dec (eX (Xs ω), eY (Ys ω))}` is the joint error. -/
@[entry_point]
theorem slepian_wolf_converse_sum
    {Mx My : ℕ} [NeZero Mx] [NeZero My]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → α) (Ys : Ω → β)
    (eX : α → Fin Mx) (eY : β → Fin My)
    (dec : Fin Mx × Fin My → α × β)
    (hXs : Measurable Xs) (hYs : Measurable Ys)
    (hcard : 2 ≤ Fintype.card (α × β)) :
    Real.log (Mx : ℝ) + Real.log (My : ℝ) ≥
      entropy μ (fun ω ↦ (Xs ω, Ys ω))
        - Real.binEntropy
            (InformationTheory.MeasureFano.errorProb μ
              (fun ω ↦ (Xs ω, Ys ω))
              (fun ω ↦ (eX (Xs ω), eY (Ys ω))) dec)
        - InformationTheory.MeasureFano.errorProb μ
            (fun ω ↦ (Xs ω, Ys ω))
            (fun ω ↦ (eX (Xs ω), eY (Ys ω))) dec
          * Real.log ((Fintype.card (α × β) : ℝ) - 1) := by
  -- Joint source Z := (Xs, Ys) on α × β, joint encoder E := (EX, EY) : Ω → Fin Mx × Fin My.
  set Z : Ω → α × β := fun ω ↦ (Xs ω, Ys ω) with hZ_def
  set E : Ω → Fin Mx × Fin My := fun ω ↦ (eX (Xs ω), eY (Ys ω)) with hE_def
  set Pe := InformationTheory.MeasureFano.errorProb μ Z E dec with hPe_def
  -- Measurabilities.
  have hZ : Measurable Z := hXs.prodMk hYs
  have hE_aux : Measurable (fun p : α × β ↦ (eX p.1, eY p.2)) :=
    measurable_of_countable _
  have hE : Measurable E := hE_aux.comp hZ
  have hdec : Measurable dec := measurable_of_countable _
  -- Mx, My positive (so that log Mx, log My are well-defined real values).
  have hMx_pos : 0 < Mx := Nat.pos_of_ne_zero (NeZero.ne Mx)
  have hMy_pos : 0 < My := Nat.pos_of_ne_zero (NeZero.ne My)
  have hMx_pos_R : (0 : ℝ) < Mx := by exact_mod_cast hMx_pos
  have hMy_pos_R : (0 : ℝ) < My := by exact_mod_cast hMy_pos
  -- Fintype.card (Fin Mx × Fin My) = Mx * My.
  have hcard_prod_Fin : (Fintype.card (Fin Mx × Fin My) : ℝ) = (Mx : ℝ) * (My : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  -- log (Mx * My) = log Mx + log My.
  have h_log_split : Real.log (Mx : ℝ) + Real.log (My : ℝ)
      = Real.log ((Mx : ℝ) * My) := by
    rw [Real.log_mul hMx_pos_R.ne' hMy_pos_R.ne']
  -- Step A: log (Mx * My) ≥ H(E) by MaxEntropy.entropy_le_log_card.
  have h_step_A :
      entropy μ E ≤ Real.log ((Mx : ℝ) * (My : ℝ)) := by
    have := MaxEntropy.entropy_le_log_card μ E hE
    rwa [hcard_prod_Fin] at this
  -- Step B: H(E) ≥ H(Z) - H(Z | E) via bridge + nonneg mutualInfo.
  have h_bridge :
      (mutualInfo μ Z E).toReal
        = entropy μ Z - InformationTheory.MeasureFano.condEntropy μ Z E :=
    mutualInfo_eq_entropy_sub_condEntropy μ Z E hZ hE
  have h_mi_nn : 0 ≤ (mutualInfo μ Z E).toReal := ENNReal.toReal_nonneg
  -- Also need: H(E) ≥ H(Z) - H(Z | E)? Actually use I(Z; E) = H(Z) - H(Z | E)
  -- and I(Z; E) ≤ H(E) (since I(Z;E) = H(E) - H(E|Z) ≤ H(E)).
  have h_bridge_E :
      (mutualInfo μ E Z).toReal
        = entropy μ E - InformationTheory.MeasureFano.condEntropy μ E Z :=
    mutualInfo_eq_entropy_sub_condEntropy μ E Z hE hZ
  have h_comm : mutualInfo μ Z E = mutualInfo μ E Z :=
    mutualInfo_comm μ Z E hZ hE
  have h_mi_le_HE :
      entropy μ Z - InformationTheory.MeasureFano.condEntropy μ Z E
        ≤ entropy μ E := by
    rw [← h_bridge, h_comm, h_bridge_E]
    have h_nn := condEntropy_nonneg μ E Z
    linarith
  -- Step C: H(Z | E) ≤ binEntropy(Pe) + Pe * log (|α × β| - 1) via Fano (no side info needed,
  -- conditioner is just E on type Fin Mx × Fin My).
  have h_step_C :
      InformationTheory.MeasureFano.condEntropy μ Z E
        ≤ Real.binEntropy Pe + Pe * Real.log ((Fintype.card (α × β) : ℝ) - 1) :=
    InformationTheory.MeasureFano.fano_inequality_measure_theoretic
      μ Z E dec hZ hE hdec hcard
  -- Combine.
  rw [h_log_split]
  linarith

end InformationTheory.Shannon

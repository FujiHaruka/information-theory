import InformationTheory.Shannon.BroadcastChannel.Marton.RegionCardinality
import Mathlib.Probability.Independence.Conditional
open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon.BroadcastChannel.Marton
universe u
variable {α β₁ β₂ : Type u} [MeasurableSpace α] [StandardBorelSpace α]
  [MeasurableSpace β₁] [StandardBorelSpace β₁] [MeasurableSpace β₂] [StandardBorelSpace β₂]

-- (a) the Pi-compressed ambient, default budget
example (kv : Fin 3 × Fin 3 → ℕ) (kJ : ℕ) :
    StandardBorelSpace (((i : Fin 3 × Fin 3) → bcAuxAlphabet.{u} (kv i)) × α × β₁ × β₂ ×
      bcAuxAlphabet.{u} kJ) := inferInstance

-- (b) N2's flat right-nested 13-tuple, default budget (expected to be the hard one)
example (k1 k2 k3 k4 k5 k6 k7 k8 k9 kJ : ℕ) :
    StandardBorelSpace (bcAuxAlphabet.{u} k1 × bcAuxAlphabet.{u} k2 × bcAuxAlphabet.{u} k3 ×
      bcAuxAlphabet.{u} k4 × bcAuxAlphabet.{u} k5 × bcAuxAlphabet.{u} k6 ×
      bcAuxAlphabet.{u} k7 × bcAuxAlphabet.{u} k8 × bcAuxAlphabet.{u} k9 ×
      α × β₁ × β₂ × bcAuxAlphabet.{u} kJ) := inferInstance

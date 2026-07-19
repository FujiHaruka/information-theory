import InformationTheory.Shannon.ConditionalMethodOfTypes.Mass.Concentration
import InformationTheory.Shannon.ConditionalMethodOfTypes.Mass.SliceMass

/-!
# Conditional method of types — Mass assembly

Main assembly for the conditional method of types: the marginal-Y
identification and per-`y` Y-product mass lower bound, the entropy
concentration helper `conditional_KL_concentration_ge`, and the headline
theorem `conditionalStronglyTypicalSlice_mass_ge`.

This module proves the conditional slice-mass lower bound via the KL
concentration helper, split across `Mass.Concentration` (the entropy
concentration machinery) and `Mass.SliceMass` (the headline theorem).
-/

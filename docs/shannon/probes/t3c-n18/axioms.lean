/-
PROBE — the axiom audit of every declaration `Thm7Region.lean` gained or already carried.

Run:  lake env lean docs/shannon/probes/t3c-n18/axioms.lean
-/
import InformationTheory.Shannon.BroadcastChannel.Thm7Region

open InformationTheory.Shannon.BroadcastChannel

#print axioms thm7Region_nonempty
#print axioms origin_mem_thm7Region
#print axioms thm7Slots_thm7DegenerateLaw
#print axioms thm7DegenerateLaw_isThm7Law
#print axioms thm7DegenerateLaw_map_input
#print axioms thm7DegenerateLaw_map_outputs
#print axioms thm7DegenerateLaw_map_full
#print axioms thm7DegenerateLaw
#print axioms iCondIndepFun_of_subsingleton_codomain
#print axioms mutualInfo_eq_zero_of_ae_const
#print axioms condMutualInfo_eq_zero_of_ae_const
#print axioms ae_eq_const_of_map_eq_dirac
#print axioms isClosed_setOf_inThm7
#print axioms isClosed_thm7RegionOfLaw
#print axioms finite_setOf_lt_thm7Cap
#print axioms isClosed_iUnion_thm7RegionOfLaw
#print axioms isClosed_thm7RegionOfAuxReceiver
#print axioms isClosed_thm7RegionOfInput
#print axioms isClosed_thm7Region

import InformationTheory.Shannon.WynerZiv.Achievability.Covering
import InformationTheory.Shannon.WynerZiv.Achievability.Concentration
import InformationTheory.Shannon.WynerZiv.Achievability.MarkovCore
import InformationTheory.Shannon.WynerZiv.Achievability.ChosenWord
import InformationTheory.Shannon.WynerZiv.Achievability.Decomposition
import InformationTheory.Shannon.WynerZiv.Achievability.SourceTransport
import InformationTheory.Shannon.WynerZiv.Achievability.MassBound
import InformationTheory.Shannon.WynerZiv.Achievability.Headline

/-!
# Wyner–Ziv operational achievability (binning + covering)

This file assembles the operational achievability leg of the Wyner–Ziv theorem
(Cover–Thomas Theorem 15.9.1): a rate `R` above the information-theoretic rate
`wynerZivRate` is achievable at distortion `D` for the i.i.d. source `P_XY` with
decoder side information `Y`.

## Approach

Wyner–Ziv achievability is a two-layer hybrid: **rate-distortion covering** on the
`X → U` side and **Slepian–Wolf binning** on the side-information `Y` side.

* the encoder covers `X^n` by a codeword `U^n` drawn from an i.i.d. codebook
  (rate-distortion covering, `jointTypicalLossyEncoder`), then bins the codeword
  index (Slepian–Wolf binning, `binningMeasure`) down to rate `R ≈ I(X;U) −
  I(Y;U)`;
* the decoder receives `(bin index, Y^n)` and searches its bin for the unique
  codeword conditionally typical with `Y^n`.

The two error mechanisms decouple cleanly (see the *gateway atoms* below), each
living on its own conditional-typicality slice under the **common** alphabet
assignment "covering codeword `U` in the source role, side information `Y` as the
conditioning variable":

* **decoder confusion** — a wrong binned codeword `U'^n` shares the true bin and
  is conditionally typical with `Y^n`. Its expected mass over the random binning
  is bounded by (slice cardinality) `/` (bin count), via the Slepian–Wolf alias
  bound `swError_EX_expectation_le` (itself `binning_collision_prob` ∘
  `conditionalTypicalSlice_card_le`). This is the `Y`-fixed, `U`-counted slice.
* **covering acceptance** — the true covering codeword is itself conditionally
  typical with `Y^n` (not rejected), via the strong conditional-slice mass bound
  `conditionalStronglyTypicalSlice_mass_ge`. This is the `U`-fixed, `Y`-measured
  slice.

These are transposed fibers of the same joint typicality relation, but they never
need to be reconciled into one statement: they bound *independent* error events.
The apparent transposition between the strong slice (`conditionalStronglyTypical`,
`U`-fixed) and the weak slice (`conditionalTypical`, `Y`-fixed) is therefore not
an obstruction — it is exactly the decomposition the error analysis wants.

## Main statements

* `wyner_ziv_achievability` — the operational achievability headline.

## Gateway atoms (both reuse existing, proved in-project atoms)

* `wz_sideInfo_decoder_confusion_expectation_le` — the decoder-confusion bound,
  by instantiating the Slepian–Wolf alias bound with the covering codeword in the
  source role.
* `wz_covering_sideInfo_mass_ge` — the covering-acceptance mass bound, by
  instantiating the strong conditional-slice mass bound with the same alphabet
  assignment.

## Implementation notes

The construction threads these two exponents through the Wyner–Ziv error
decomposition, splits the rate as `R = I(X;U) − I(Y;U)`, and extracts a good
codebook by the pigeonhole averaging `exists_codebook_low_avg`. The headline
is proved sorry-free (`#print axioms wyner_ziv_achievability` =
`[propext, Classical.choice, Quot.sound]`).

## Module structure

Umbrella of the `Shannon/WynerZiv/Achievability/` family, re-exporting (in dependency order):

* `Achievability.Covering` — the gateway atoms, the covering + binning construction skeleton and
  its leaf atoms, the two-ambient regularity section, and the hoisted Markov-core helpers.
* `Achievability.Concentration` — the Leg F inner concentration sub-lemmas (L0–L5).
* `Achievability.MarkovCore` — the Markov core and Gateway atom 3 (covering side-information
  acceptance).
* `Achievability.ChosenWord` — covering chosen-word side-information typicality and the joint
  lossy code existence.
* `Achievability.Decomposition` — the Steps 3–7 distortion decomposition and the pmf-side
  product bounds.
* `Achievability.SourceTransport` — the source-measure change of variables and the
  distortion-decomposition bridge (Legs A–D).
* `Achievability.MassBound` — the source→ambient AEP mass transport and the entropy helpers.
* `Achievability.Headline` — the per-slack good codes and the operational achievability headline
  `wyner_ziv_achievability`.
-/

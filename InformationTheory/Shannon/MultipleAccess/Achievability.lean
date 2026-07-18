import InformationTheory.Shannon.MultipleAccess.Achievability.Codebook
import InformationTheory.Shannon.MultipleAccess.Achievability.RandomCoding

/-!
# Multiple access channel — achievability codebook, decoder, and Bonferroni bound

The two-user codebook plumbing for MAC achievability (Cover–Thomas §15.3.1): the
joint-typical pair decoder, the bundle of two codebooks into a `MACCode`, and the
four-event Bonferroni decomposition of the per-pair error probability.  This is the
two-codebook / four-event generalisation of the single-user
`InformationTheory.Shannon.ChannelCoding.errorProbAt_le_E1_plus_E2`.

This file aggregates the two submodules:

* `Achievability.Codebook` — the codebook type, the joint-typical pair decoder,
  the `MACCode` bundle, the four-event Bonferroni decomposition, the corner-point
  information quantities, and the block-law / channel-fold helpers.
* `Achievability.RandomCoding` — the per-event codebook-average swaps, the
  aggregating arithmetic, the two-codebook average bound, the random → deterministic
  pigeonhole, and the achievability headline `mac_achievability`.

## Main definitions

* `MACCodebook M n α := Fin M → (Fin n → α)` — a length-`n` codebook for one user.
* `macJointTypicalDecoder` — decodes `y` to the unique pair `(m₁, m₂)` whose codeword
  triple `(c₁ m₁, c₂ m₂, y)` is three-way jointly typical, falling back to
  `(⟨0, hM₁⟩, ⟨0, hM₂⟩)` when none / not-unique.
* `macCodebookToCode` — bundle two codebooks + the joint-typical decoder into a `MACCode`.

## Main results

* `mac_errorProbAt_le_bonferroni4` — the four-event union bound on the per-pair error
  probability: `E0` (the correct pair is not typical) plus the three alias sums
  `E1`/`E2`/`E3` (user 1 alias, user 2 alias, both alias).
-/

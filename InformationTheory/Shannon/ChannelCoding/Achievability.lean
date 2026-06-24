import InformationTheory.Shannon.ChannelCoding.Achievability.Core
import InformationTheory.Shannon.ChannelCoding.Achievability.RandomCodebook
import InformationTheory.Shannon.ChannelCoding.Achievability.Main

/-!
# Channel coding achievability theorem

Umbrella module re-exporting the three parts under `Achievability/`:

* `Achievability.Core` — codebook, joint typical decoder, and per-codeword error
  decomposition definitions.
* `Achievability.RandomCodebook` — Fubini swap helpers + `random_codebook_average_le`.
* `Achievability.Main` — pigeonhole argument + `channel_coding_achievability`.

## Implementation notes

* Codebook is `Fin M → (Fin n → α)` (abbrev).
* The codebook average is taken over the `p`-i.i.d. law
  `codebookMeasure p M n := Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))`
  on the finite space `Codebook M n α`. The probabilistic-method form matches
  Cover-Thomas Theorem 7.7.3-4.
* Decoder = `Classical.dec`-based "unique joint-typical `m`, else fallback `⟨0, hM⟩`".
* Rate slack `ε := (I - R) / 6`; `M := Nat.ceil (Real.exp (n · R))`.
-/

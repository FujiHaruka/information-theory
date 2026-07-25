import InformationTheory.Shannon.BroadcastChannel.Marton.MarkovCore.Prelim
import InformationTheory.Shannon.BroadcastChannel.Marton.MarkovCore.Receiver1
import InformationTheory.Shannon.BroadcastChannel.Marton.MarkovCore.Receiver2

/-!
# Marton's inner bound — the conditional AEP for the transmitted pair

The receiver-1 error event of the Marton ensemble opens with the transmitted auxiliary word failing
to be jointly typical with the received word.  The selection the encoder performs makes the law of
the transmitted auxiliary word depend on the whole pair of subcodebooks, so the transmitted word is
not distributed as an i.i.d. draw from the ambient and the ordinary AEP does not apply to it.  What
does apply is a conditional statement: for *whatever* auxiliary and input blocks the encoder ends
up transmitting, as long as their empirical type is close to the ambient `(V₁, X)`-law, the channel
output makes the pair `(V₁, Y₁)` weakly jointly typical with probability close to one.

The type closeness has to be at a radius strictly smaller than the band radius `ε`, because pinning
the conditional mean of the log-likelihood costs a Lipschitz factor; `martonStrongRadius` is that
smaller radius and `martonBandConst` the factor.  Weak typicality of the transmitted blocks at
radius `ε` is not enough: it pins an entropy alone, which leaves the conditional means free.

The type pin itself is supplied by the encoder's selection rule, which picks a *strongly* typical
auxiliary pair.  Passing that pin from the auxiliary pair to the transmitted `(V₁, X)` block costs
one more radius separation, because the conditional mean of a letter statistic of the input is the
auxiliary type averaged against the input kernel; `martonCoveringRadius` is the radius at which the
auxiliary pair has to be pinned for the transmitted block to be pinned at `martonStrongRadius`.

## Main definitions

* `martonBandConst` — the Lipschitz factor of the three band pins.
* `martonStrongRadius` — the type radius at which the transmitted blocks must be pinned.
* `martonCoveringRadius` — the radius at which the selected auxiliary pair must be pinned.
* `martonBandConst₂`, `martonStrongRadius₂` and `martonCoveringRadius₂` — the receiver-2 radii.
  The two receivers carry separate band constants because the bands they pin are the entropies of
  their own output, so the radii they induce are unrelated; an assembly consuming both takes their
  minimum, which `jointStronglyTypicalSet_mono_radius` turns back into either pin.

## Main statements

* `marton_condAEP_jointlyTypical` and `marton_condAEP_jointlyTypical_ge` — the conditional AEP:
  the channel output of a type-pinned `(V₁, X)`-block is jointly typical with the auxiliary word
  with probability `≥ 1 - tol`, stated on the failure event and on its complement.
* `marton_strongRadius_prob_tendsto_one` — the ambient ensemble meets the type pin with
  probability tending to one, so the conditional AEP is not vacuous.
* `marton_transmitted_stronglyTypical_le` — the input drawn from a type-pinned auxiliary pair
  inherits the pin.
* `marton_condAEP_selected_avg_le` — the two combined: the receiver-1 error term of a selected
  auxiliary pair, averaged over the input tier, is below any prescribed tolerance.
* `marton_condAEP_jointlyTypical₂`, `marton_transmitted_stronglyTypical₂_le` and
  `marton_condAEP_selected_avg₂_le` — the receiver-2 mirrors.  The broadcast channel is not
  degraded here, so the second receiver is an exact mirror of the first rather than a second tier.

## Module structure

Umbrella of the `Shannon/BroadcastChannel/Marton/MarkovCore/` family, re-exporting:

* `MarkovCore.Prelim` — the singleton masses and marginals of the per-coordinate law that both
  receivers consume, together with radius monotonicity of the strongly typical sets.
* `MarkovCore.Receiver1` — the receiver-1 radii, the three entropy bands, the conditional AEP and
  the transfer of the type pin to the transmitted pair.
* `MarkovCore.Receiver2` — the receiver-2 mirror of the same chain.
-/

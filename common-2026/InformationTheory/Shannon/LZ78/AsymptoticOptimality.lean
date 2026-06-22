import InformationTheory.Shannon.LZ78.AsymptoticOptimality.EncodingLength
import InformationTheory.Shannon.LZ78.AsymptoticOptimality.ParentBridgeConverse
import InformationTheory.Shannon.LZ78.AsymptoticOptimality.ParentBridgeAchievability

/-!
# LZ78 greedy-parse encoding length + asymptotic-optimality bridge

The genuine longest-prefix-match greedy LZ78 parse itself lives in
`InformationTheory/Shannon/LZ78/GreedyLongestPrefix.lean` as
`lz78PhraseStrings` (the ordered list of emitted phrase strings, with the
distinct-phrase invariants `lz78PhraseStrings_nodup` /
`lz78PhraseStrings_count_le`). This file builds the **encoding-length and
parent-theorem bridge** on top of that genuine parse:

* `lz78GreedyEncodingLength n x` charges `c · bitLength c |α|` bits
  against the genuine distinct phrase count
  `c = (lz78PhraseStrings (List.ofFn x)).length` (each of the `c` phrases
  costs at most `bitLength c |α|` bits at the final dictionary size);
* the Cover–Thomas Lemma 13.5.2 bit-length upper bound
  `n · (log(n+1) + log|α| + 2)` holds via `c ≤ n` and
  `bitLength`-monotonicity;
* the encoding length plugs into the parent
  `lz78_asymptotic_optimality` parameter slot, publishing the main theorem
  as `lz78_asymptotic_optimality_with_greedy`.

The two a.s.-eventual halves of the sandwich are the converse lower bound and
the Ziv achievability upper bound; both carry genuine ergodic content.

## File layout

* §1. Encoding length + parent-theorem bridge —
  `lz78GreedyEncodingLength`, its distinct-phrase count bound, and the
  Cover–Thomas bit-length / per-symbol-rate bounds.
* §2. `IsLZ78EncodingLengthBoundPassthrough` — the
  upper-bound pass-through predicate and its canonical discharge.
* §3. Parent-theorem bridge — the two a.s.-eventual halves and the
  `lz78_asymptotic_optimality_with_greedy` headline.

## Pattern source

The per-phrase bit cost is reused from `LZ78/GreedyParsing.lean`
(`LZ78Phrase.bitLength`); the parent-theorem bridge instantiates the
generic sandwich combinator `lz78_asymptotic_optimality` with the
genuine greedy encoding length and discharges its two a.s.-eventual
halves.
-/

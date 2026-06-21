import InformationTheory.Shannon.SMB.AlgoetCover.KMarkovApproximation
import InformationTheory.Shannon.SMB.AlgoetCover.MarkovLikelihoodRatio
import InformationTheory.Shannon.SMB.AlgoetCover.Limsup
import InformationTheory.Shannon.SMB.AlgoetCover.Boundedness
import InformationTheory.Shannon.SMB.AlgoetCover.TwoSidedRatio
import InformationTheory.Shannon.SMB.AlgoetCover.Liminf

/-!
# SMB Algoet–Cover sandwich

The Algoet–Cover sandwich discharges the four hypotheses of
`shannon_mcmillan_breiman_of_sandwich` (`liminf ≥ H`, `limsup ≤ H`, a.s.
boundedness above and below) to produce the hypothesis-free
`shannon_mcmillan_breiman` theorem. The proofs combine the chain rule
`log_block_eq_sum_pmfLogCond`, Birkhoff for the per-step conditional
log-likelihood, a `k`-Markov approximation with conditional entropy
`H_k = conditionalEntropyTail μ p k`, and a likelihood-ratio + Borel–Cantelli
bound to convert expected-value inequalities into a.s. bounds.
-/

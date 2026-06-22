import InformationTheory.Shannon.AWGN.ConverseMIChainRule.PerLetterIntegrability
import InformationTheory.Shannon.AWGN.ConverseMIChainRule.BlockMI
import InformationTheory.Shannon.AWGN.ConverseMIChainRule.PerLetterMI
import InformationTheory.Shannon.AWGN.ConverseMIChainRule.Markov

/-!
# Converse-side shared lemmas: integrability, MI chain rule, Markov factorization

The analytic facts consumed by the AWGN converse: per-letter log-density
integrability, the memoryless mutual-information chain rule, and the
deterministic-encoder Markov factorization.

## Main statements

* `awgnPerLetterIntegrability_holds` — per-letter output-law log-density integrability.
* `awgnContinuousMIChainRule_holds` — the memoryless continuous MI chain rule.
* `awgnConverseMarkov_holds` — the deterministic-encoder Markov factorization.
-/

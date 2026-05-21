# Proof log — LZ78 tree-induced `Q_c` AEP (route C, M0 gate + Q1–Q3)

Plan: `docs/shannon/lz78-treeinduced-aep-plan.md`. Output:
`Common2026/Shannon/LZ78TreeInducedAEP.lean` (genuine, sorryAx-free).

## M0 gate — verdict and the honesty finding (read first)

The M0 inventory found the plan's central premise to be **mathematically
false**, and simultaneously found a **cleaner genuine route** than the planned
route-C `qkSingleton` sandwich. Both points below are load-bearing.

### Finding 1 — `c·log c ≤ -log Q_c` is FALSE per-block for BOTH forms of `Q_c`

The plan (判断ログ 1, 現況 §「per-block ... TRUE」) asserts: "per-block
`c·log c ≤ -log Q_c` is TRUE — the `not_isLZ78ZivCombinatorialCoreOverhead`
disproof is `Pₙ`-only, so `Q_c` is outside it." This is **wrong**:

- **Path-prefix `Q_c`** (`∏ⱼ condPhraseProb`): the documented trap at
  `IsLZ78ZivCombinatorialCore`'s docstring (`LZ78ZivCombinatorics.lean:229-241`)
  is exactly that these conditionals do **not** sum to `≤ 1`
  (`∑ⱼ qⱼ ≈ c`), so the log-sum step `c·log c ≤ ∑ⱼ -log qⱼ` fails. The same
  constant-process witness as `not_isLZ78ZivCombinatorialCoreOverhead`
  (`X ≡ a`, `a^16`, `Pₙ = 1`) gives every conditional `= 1`, so
  `-log Q_c = 0` while `c·log c > 0` (c = 5). False.
- **Tree-node `Q_c^{tree}`** (`∑ q ≤ 1` per node, so `node_logsum_step`
  applies): here `node_logsum_step` gives only
  `∑_v k_v·log k_v ≤ -log Q_c^{tree}`, NOT `c·log c ≤ -log Q_c^{tree}`. The
  missing step `c·log c ≤ ∑_v k_v·log k_v` is the CT 13.5.5 *grouping* (Jensen
  over the tree), which carries a `c·log(D_c)` overhead (`D_c` ≈ distinct
  nodes ≈ c). For the constant process the tree is a single path, every
  `k_v = 1`, so `∑_v k_v log k_v = 0` and `c log c ≤ 0` is false. The genuine
  CT optimality is **a.s.-eventual** (`(c log D_c)/n → 0` since `c/n → 0`),
  not per-block.

**Consequence**: the LZ78 achievability gap is the **per-block combinatorial
Ziv core** (`IsLZ78ZivCombinatorialCore`), NOT the `Q_c` AEP. Building the
`Q_c` AEP — the plan's stated goal — does **not** discharge achievability. The
plan conflated the AEP (`-log Q_c/n → H`) with the combinatorial core
(`c log c ≤ -log Q_c`); only the latter is the open frontier.

### Finding 2 — route C `qkSingleton` sandwich does NOT close; a cleaner genuine route exists

The planned upper-half sandwich `Q_c ≥ qkSingleton(k)` (depth-`k` cutoff
widens the cylinder ⇒ probability increases) does **not** hold
factor-by-factor: conditional probabilities are not monotone in context depth
for general ergodic sources (a deeper context can give a larger *or* smaller
conditional). The error term `δ_k(n)` is genuinely ω-non-uniform (it depends on
the data-dependent realized phrase structure). So route C as planned is no-go.

**But** the codebase already has the right relation in the *opposite*,
genuine direction: `blockProb_le_prod_condPhraseProb` (`StationaryKernel.lean`)
gives `Pₙ ≤ Q_c` (path-prefix product) unconditionally under positivity, from
prefix monotonicity (`prefixBlockProb_antitone`) + `boundary c ≤ n`. Hence
`-log Q_c ≤ -log Pₙ = n·blockLogAvg`, i.e. `(-log Q_c)/n ≤ blockLogAvg`. The
path-block-law AEP limsup `algoet_cover_limsup_bound` /
`shannon_mcmillan_breiman₂` (already genuine, regularity-only, proved via the
fixed-`k` `qkSingleton` sandwich + `H_k → H` internally) then gives the
**upper half** directly. **No new ergodic content; the planned route-C error
term is bypassed entirely** by reducing to the existing `Pₙ` AEP.

## What was published (genuine, sorryAx-free)

`Common2026/Shannon/LZ78TreeInducedAEP.lean`:

- `treeInducedProb` (`Q_c`) = `∏ⱼ condPhraseProb` (path-prefix coding measure)
  + `negLogbTreeInducedRate` = `(-log₂ Q_c)/n`.
- `treeInducedProb_ge_blockProb`: `Pₙ ≤ Q_c` (from
  `blockProb_le_prod_condPhraseProb`).
- `negLogbTreeInducedRate_le_blockLogAvg₂`: per-`n` (`n ≥ 1`)
  `(-log₂ Q_c)/n ≤ blockLogAvg₂`.
- `treeInducedProb_negLogb_div_limsup_le_entropyRate₂` (main):
  `∀ᵐ ω, limsup (-log₂ Q_c/n) ≤ entropyRate₂`, via `limsup_le_limsup` +
  `shannon_mcmillan_breiman₂` (`limsup blockLogAvg₂ = entropyRate₂`). LHS
  coboundedness from `Q_c ≤ 1` (`prod_condPhraseProb_telescope` →
  `prefixBlockProb ≤ 1`); RHS boundedness from SMB₂ Tendsto.

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]`. Only
side condition is full-support regularity `hreg` (admissible, the same family
as `isLZ78PerPathParsingFactorization_of_pos`), used for `0 < Pₙ` and
parse-prefix positivity. No load-bearing hypothesis; no honest hyp needed.

## Frontier (unchanged by this file)

LZ78 achievability still rests on `IsLZ78ZivCombinatorialCore` (per-block
`c·log c ≤ ∑ⱼ -log qⱼ`) — the genuine, load-bearing combinatorial heart, which
this AEP does **not** touch. The genuine path forward (NOT route C, NOT this
AEP) is the a.s.-eventual Ziv grouping `c·log c ≤ -log Q_c^{tree} + c·log D_c`
with `(c log D_c)/n → 0`, built from `node_logsum_step` + a tree-grouping
Jensen step + `Pₙ ≤ Q_c^{tree}` (the latter not yet in the committed layer).
That is a separate build; the plan's Q4 (`c log c ≤ -log Q_c`) as stated is
false and should be retired in favour of the overhead-carrying eventual form.

## Stuck points / search misses (for metrics)

- No grep/loogle misses of consequence: every lemma needed (`Pₙ ≤ Q_c`,
  `prefixBlockProb_antitone`, `blockLogAvg_eq_neg_log_blockProb` analog,
  `shannon_mcmillan_breiman₂`, `algoet_cover_limsup_bound`) was already in the
  committed layer. `gcongr` discharged the div-monotone step (loogle for the
  named lemma `a≤b → 0<c → a/c≤b/c` returned 0 matches; `gcongr` is the right
  tool).
- Design backtrack: the entire plan route C (`Q_c` defined in `qkSingleton`
  markovFactor style + fixed-`k` sandwich, Q1–Q2 ~400–640 lines) was
  **abandoned at M0** in favour of the `Pₙ ≤ Q_c` reduction (~80 lines). The
  M0 analysis (not code) was the load-bearing work.

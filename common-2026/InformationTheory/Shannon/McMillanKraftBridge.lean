import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ShannonCode.Basic
import Mathlib.InformationTheory.Coding.KraftMcMillan
import Mathlib.InformationTheory.Coding.UniquelyDecodable

/-!
# McMillan → Kraft → Gibbs converse bridge (symbol-code level)

This file wires **Mathlib's genuine `InformationTheory.kraft_mcmillan_inequality`**
(uniquely-decodable code `⟹ ∑ D^{-|w|} ≤ 1`, a fully-proved counting theorem
in `Mathlib/InformationTheory/Coding/KraftMcMillan.lean`) into this project's
per-symbol Kraft / Gibbs framework (`InformationTheory/Shannon/ShannonCode.lean`).

The result is a genuine **expectation-level source-coding converse**: for any
finite-alphabet source `P` whose codeword assignment `c : α → List β` is
injective with a uniquely-decodable image, the entropy lower-bounds the
expected code length,

```
H_D(P) ≤ E[L]    where  D = |β|,  L a = |c a|.
```

## Honesty status (read before reusing)

* **McMillan itself is NOT reproved here.** Mathlib ships a genuine,
  unconditional `kraft_mcmillan_inequality`. This file is a *bridge*, not a
  re-derivation.

* The bridge is **genuine** (`#print axioms` clean, type ≠ conclusion, no
  `:= h` circularity, no `True` slot). The only inputs are:
  - Mathlib's McMillan,
  - this project's `entropyD_le_expectedLength_of_kraft` (genuine Gibbs),
  - regularity hypotheses (full support, `D > 1`, injectivity, UD of the
    image) — all genuine *preconditions of a code*, not load-bearing
    discharges of the theorem's content.

* **What this does NOT close for LZ78.** The LZ78 converse target
  `IsLZ78ConverseCodingLowerBound` (`LZ78ConverseKraft.lean`) is an
  **a.s.-eventual, per-realization** lower bound
  `blockLogAvg₂ n ω − slack ≤ lz/n`. McMillan supplies only an
  **expectation-level** Kraft/Gibbs bound `H ≤ E[L]`. The gap is the
  **a.s. lift** (averaged ⟶ pointwise eventual), which is the
  Barron / competitive-optimality argument and is genuinely separate from
  McMillan. See §3 for the precise statement of the residual gap. This file
  therefore does **not** discharge `IsLZ78ConverseCodingLowerBound`, and does
  not pretend to.

* Additionally, the **raw LZ78 phrase-string set is not a McMillan code**: the
  LZ78 dictionary is prefix-*complete* (closed under prefixes), so the phrase
  strings are not prefix-free / uniquely-decodable as a set. The
  uniquely-decodable object in LZ78 is the *encoded* (index, symbol) stream,
  a different structure than `lz78PhraseStrings`. See §3.

## File layout

* **§1.** `kraftSum_eq_sum_one_div_pow` — rewriting `kraftSum |β| (|c ·|)`
  into McMillan's `∑ (1/|β|)^{|w|}` shape.
* **§2.** `kraftSum_le_one_of_uniquelyDecodable` — McMillan ⟹ the project's
  `kraftSum ≤ 1`, then `entropyD_le_expectedLength_of_uniquelyDecodable`
  (genuine expectation-level converse `H_D(P) ≤ E[L]`).
* **§3.** Honest assessment of the LZ78 converse gap (documented residuals,
  no false discharge).
-/

namespace InformationTheory.Shannon.ShannonCode

open MeasureTheory Real Finset
open scoped ENNReal NNReal BigOperators

/-! ## §1. Rewriting `kraftSum` into the McMillan weight shape -/

section Rewrite

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `D ^ (-(n : ℤ)) = (1 / D) ^ n` for any real `D` (McMillan uses the
`(1/D)^{|w|}` weight; the project's `kraftSum` uses `D ^ (-(l a : ℤ))`). -/
lemma zpow_neg_natCast_eq_one_div_pow (D : ℝ) (n : ℕ) :
    (D : ℝ) ^ (-(n : ℤ)) = (1 / D) ^ n := by
  rw [div_pow, one_pow, zpow_neg, zpow_natCast, one_div]

omit [DecidableEq α] in
/-- `kraftSum D l = ∑ a, (1/D) ^ (l a)` — the McMillan-weight rewriting of
the project's `kraftSum`. -/
lemma kraftSum_eq_sum_one_div_pow (D : ℝ) (l : α → ℕ) :
    kraftSum D l = ∑ a : α, (1 / D) ^ (l a) := by
  unfold kraftSum
  exact Finset.sum_congr rfl (fun a _ => zpow_neg_natCast_eq_one_div_pow D (l a))

end Rewrite

/-! ## §2. McMillan ⟹ `kraftSum ≤ 1` ⟹ Gibbs converse -/

section McMillan

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β : Type*} [Fintype β] [Nonempty β] [DecidableEq β]

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Symbol-code Kraft from McMillan**: if the codeword assignment
`c : α → List β` is injective with uniquely-decodable image, then the
per-symbol Kraft sum `kraftSum |β| (|c ·|) ≤ 1`.

`D = Fintype.card β` is the alphabet size; the codeword lengths are
`l a = (c a).length`. The image `c '' univ` is a finite set of distinct
codewords; McMillan's `kraft_mcmillan_inequality` gives
`∑_{w ∈ image} (1/|β|)^{|w|} ≤ 1`, and reindexing by the injective `c`
recovers the per-symbol sum. -/
@[entry_point]
theorem kraftSum_le_one_of_uniquelyDecodable
    (c : α → List β) (hc : Function.Injective c)
    (hUD : UniquelyDecodable ((Finset.univ.image c : Finset (List β)) : Set (List β))) :
    kraftSum (Fintype.card β : ℝ) (fun a => (c a).length) ≤ 1 := by
  -- McMillan over the (distinct) codeword image.
  have hMcM := kraft_mcmillan_inequality (S := Finset.univ.image c) hUD
  -- Reindex `∑ w ∈ image c, (1/|β|)^|w|` back to `∑ a, (1/|β|)^|c a|`.
  have hReindex :
      (∑ w ∈ Finset.univ.image c, (1 / (Fintype.card β : ℝ)) ^ w.length)
        = ∑ a : α, (1 / (Fintype.card β : ℝ)) ^ (c a).length := by
    rw [Finset.sum_image (fun a _ b _ h => hc h)]
  rw [hReindex] at hMcM
  rw [kraftSum_eq_sum_one_div_pow]
  exact hMcM

omit [DecidableEq α] [Nonempty α] in
/-- **Expectation-level source-coding converse from McMillan** (genuine).

For a finite-alphabet source `P` (full support) and an injective codeword
assignment `c : α → List β` whose image is uniquely-decodable, the D-ary
entropy lower-bounds the expected code length:

```
H_D(P) ≤ E[L],   D = |β|,  L a = |c a|.
```

This is the genuine expectation-level converse: McMillan (Kraft) +
`entropyD_le_expectedLength_of_kraft` (Gibbs). The full-support hypothesis is
a regularity precondition (it makes the `logb` arguments positive), not a
load-bearing discharge.

**Note on `D > 1`.** The Gibbs lemma needs `1 < D = |β|`, i.e. at least a
binary alphabet. With a unary alphabet (`|β| = 1`) no uniquely-decodable code
of more than one nonempty word exists, so the hypothesis is the natural one. -/
@[entry_point]
theorem entropyD_le_expectedLength_of_uniquelyDecodable
    (hD : 1 < (Fintype.card β : ℝ))
    (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a : α, 0 < P.real {a})
    (c : α → List β) (hc : Function.Injective c)
    (hUD : UniquelyDecodable ((Finset.univ.image c : Finset (List β)) : Set (List β))) :
    entropyD (Fintype.card β : ℝ) P ≤ expectedLength P (fun a => (c a).length) :=
  entropyD_le_expectedLength_of_kraft hD P hP (fun a => (c a).length)
    (kraftSum_le_one_of_uniquelyDecodable c hc hUD)

end McMillan

/-! ## §3. Honest assessment of the LZ78 converse gap

This section is **documentation only** — it records, without any false
discharge, exactly how far the genuine §2 results (and Mathlib's McMillan)
get toward the LZ78 converse, and what residual remains.

### What §2 genuinely gives

For a *symbol code* `c : α → List β` (injective, UD image) over a finite
source `P`, §2 closes the **expectation-level converse**

```
H_D(P) ≤ E[L]          (D = |β|,  L a = |c a|),
```

unconditionally (modulo full-support / `D > 1` regularity). This is the
genuine Cover–Thomas 5.4 source-coding lower bound, now wired to Mathlib's
McMillan rather than carrying a Kraft hypothesis.

### Residual 1 — wrong code object for LZ78

`IsLZ78ConverseCodingLowerBound` (`LZ78ConverseKraft.lean`) compares the LZ78
**block** rate `lz n (block_n ω) / n` against the per-block negative
log-likelihood. McMillan applies to a *fixed* uniquely-decodable codeword set
`S : Finset (List β)`. The natural candidate `S = lz78PhraseStrings (...)`
is **NOT a McMillan code**: the LZ78 dictionary is prefix-*complete* (closed
under taking prefixes — `lz78PhraseStringsAux` grows `cur ++ [s]` only while
`cur ∈ dict`), so e.g. both `[a]` and `[a,b]` are dictionary entries and the
string set is far from prefix-free. `lz78PhraseStrings_nodup` gives
distinctness, which is *necessary but not sufficient* for `UniquelyDecodable`.
The uniquely-decodable object in LZ78 is the *encoded (parent-index, symbol)
stream*, a different structure from the phrase strings. That UD object **is
now built** (roadmap M1): `LZ78ConverseUDObject.lean` constructs the
fixed-width `(parent, symbol)` token code, proves its image
`UniquelyDecodable` (`uniquelyDecodable_of_constantLength`), and feeds it back
through §2 here to obtain a genuine `kraftSum ≤ 1` and `entropyD ≤ E[L]` for
the real token code. Residual 2 below (averaged⟶a.s. block-rate lift) remains.

### Residual 2 — averaged ⟶ a.s.-eventual lift

Even granting a Kraft bound for the per-block LZ78 code, McMillan/Gibbs yields
only the **expectation-level** statement `H(P_n) ≤ E[lz_n]` (or, per block,
`H_D(P_n) ≤ E[L_n]`). The converse target is the **a.s.-eventual,
per-realization** inequality

```
∀ᵐ ω, ∀ᶠ n,  blockLogAvg₂ μ p n ω − slack n ≤ (lz n (block_n ω)) / n.
```

This is strictly stronger than the averaged bound: per a fixed realization an
LZ78 codeword can be *shorter* than `−log₂ Pₙ{x}` (that is the universality of
LZ78). Closing this requires the **Barron / competitive-optimality a.s. lift**
(averaged Kraft + a `2^{−lz}`-is-a-sub-probability / Borel–Cantelli argument),
which is a separate, research-level ingredient that McMillan does **not**
supply. It matches the load-bearing `IsLZ78ConverseCodingLowerBound`
hypothesis already isolated in `LZ78ConverseKraft.lean`.

### Conclusion

* **Standalone McMillan**: genuine and present — *in Mathlib*
  (`InformationTheory.kraft_mcmillan_inequality`); this file wires it into the
  project's Kraft/Gibbs framework with a genuine expectation-level converse.
* **LZ78 converse `IsLZ78ConverseCodingLowerBound`**: **NOT discharged** by
  McMillan. Two genuine residuals remain (the LZ78-block UD code, and the
  averaged⟶a.s. lift); the latter is research-level. The honest named
  hypothesis in `LZ78ConverseKraft.lean` correctly stands.
-/

end InformationTheory.Shannon.ShannonCode

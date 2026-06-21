import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.Basic
import InformationTheory.Shannon.LZ78.ZivInequality
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range

/-!
# LZ78 greedy parsing — per-phrase bit length

This file publishes the **per-phrase bit-length cost** of an LZ78
phrase: the number of bits needed to encode one `(parent-index, symbol)`
pair given a dictionary size and an alphabet size. This is the
Cover–Thomas Ch.13.5 per-phrase cost form

```
LZ78Phrase.bitLength c a = Nat.log 2 (c + 1) + Nat.log 2 a + 2
```

(each phrase index needs `log(dictSize)` bits, each appended symbol
needs `log(|α|)` bits, plus a constant overhead). It is the shared
infrastructure consumed by the genuine longest-prefix greedy
encoding-length development
(`InformationTheory/Shannon/LZ78/AsymptoticOptimality.lean`) and by the
uniquely-decodable token code
(`InformationTheory/Shannon/LZ78/ConverseUDObject.lean`).

## File layout

* **§1. Per-phrase bit length** — `LZ78Phrase.bitLength`: the number
  of bits to encode one `(parent-index, symbol)` pair given a
  dictionary size and alphabet size, together with its `simp` normal
  form, monotonicity in the dictionary size, and positivity.
-/

namespace InformationTheory.Shannon

open scoped Topology

set_option linter.unusedSectionVars false

/-! ## §1. Per-phrase bit length -/

section PhraseBitLength

variable {α : Type*}

/-- **Bit length of a single LZ78 phrase**.

Given dictionary size `c` and alphabet size `a`, encoding one phrase
`(parent, symbol)` requires:

* `Nat.log 2 (c + 1) + 1` bits for the parent index (including the
  empty-prefix `none`, so the parent slot has `c + 1` possibilities;
  `+ 1` for the floor-vs-ceil `Nat.log` gap).
* `Nat.log 2 a + 1` bits for the alphabet symbol.

This is the Cover–Thomas Ch.13.5 per-phrase cost form. -/
def LZ78Phrase.bitLength (c a : ℕ) : ℕ :=
  (Nat.log 2 (c + 1) + 1) + (Nat.log 2 a + 1)

@[simp] lemma LZ78Phrase.bitLength_eq (c a : ℕ) :
    LZ78Phrase.bitLength c a = Nat.log 2 (c + 1) + Nat.log 2 a + 2 := by
  unfold LZ78Phrase.bitLength
  ring

/-- The per-phrase bit length is monotone in the dictionary size. -/
lemma LZ78Phrase.bitLength_mono_left {c c' a : ℕ} (h : c ≤ c') :
    LZ78Phrase.bitLength c a ≤ LZ78Phrase.bitLength c' a := by
  unfold LZ78Phrase.bitLength
  have hlog : Nat.log 2 (c + 1) ≤ Nat.log 2 (c' + 1) :=
    Nat.log_mono_right (by omega)
  omega

/-- The per-phrase bit length is positive. -/
@[simp] lemma LZ78Phrase.bitLength_pos (c a : ℕ) :
    0 < LZ78Phrase.bitLength c a := by
  unfold LZ78Phrase.bitLength
  omega

end PhraseBitLength

end InformationTheory.Shannon

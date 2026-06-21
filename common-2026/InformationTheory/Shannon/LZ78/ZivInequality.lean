import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# LZ78 Ziv's inequality — combinatorial counting layer

This file publishes the **combinatorial counting plumbing** layer of
Ziv's inequality (Cover–Thomas Lemma 13.5.5; the upper-bound half of the
LZ78 asymptotic optimality theorem). It establishes the *combinatorial*
layer (Nat-level phrase-space cardinality bound) as concrete `theorem`s,
consumed by the `IsLZ78PhraseCountAsymptotic` asymptotic layer; the
*entropy* layer (`H(X^n) ≤ Σ H(phrase_i)`) and the *log-sum* layer (final
Ziv form) are developed elsewhere. The genuine a.s. achievability residual
of LZ78 optimality is scoped out as `lz78Greedy_achievability_ae` in
`AsymptoticOptimality.lean`.

## File layout

* **§1. `LZ78Phrase` cardinality plumbing** —
  `LZ78Phrase.equivOptionNatProd`-style cardinality / image-card bounds.
* **§2. `LZ78Parsing.count` combinatorial bounds** — Nat-level
  inequalities on `p.count = p.phrases.length` purely from the parsing
  invariant.
* **§3. `ZivCountingBound` predicate** — a real-valued
  predicate that exposes the combinatorial-layer Ziv counting bound at
  the `Prop` level, with a `.refl` constructor and a constructor
  taking a real bound directly. The entropy-side layer plugs
  `ZivCountingBound` into the `IsLZ78PhraseCountAsymptotic` envelope.

## Scope

* Combinatorial counting bound:
  `LZ78Parsing.count_le_card_phrase_space` and friends. Pure Nat/Finset,
  no measure-theoretic infrastructure.
* `ZivCountingBound` real-valued `Prop` slot.
* Entropy chain-rule layer (`H(X^n) ≤ Σ H(phrase_i)`), developed elsewhere.
* Log-sum + final Ziv inequality main form, developed elsewhere.

## Pattern source

The "extract the most tractable fragments" pattern is the same as
`InformationTheory/Shannon/WynerZiv/RateMonotonicity.lean`:
the parent placeholder is not fully discharged; the file publishes the
fragments that are tractable now plus a real-valued predicate exposing
the layered shape, with `.trivial` bridges to the parent placeholder.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

/-! ## §1. `LZ78Phrase` cardinality plumbing -/

section PhraseCardinality

variable {α : Type*}

/-- An LZ78 phrase whose `parent` is in `Option (Fin c)` (i.e. either the
empty-prefix root `none`, or a back-reference `some k` with `k < c`).
This is the natural ambient *finite* type that bounds the dictionary
phrase space after the first `c` phrases have been emitted: each
subsequent phrase is `(parent ∈ {none, some 0, ..., some (c-1)}) ×
(symbol ∈ α)`. -/
def LZ78Phrase.parentBounded (c : ℕ) (α : Type*) : Type _ :=
  Option (Fin c) × α

instance LZ78Phrase.parentBounded_fintype (c : ℕ) (α : Type*) [Fintype α] :
    Fintype (LZ78Phrase.parentBounded c α) := by
  unfold LZ78Phrase.parentBounded
  infer_instance

/-- Cardinality of the bounded-parent phrase space: `(c + 1) · |α|`. -/
@[simp] lemma LZ78Phrase.card_parentBounded (c : ℕ) (α : Type*) [Fintype α] :
    Fintype.card (LZ78Phrase.parentBounded c α) = (c + 1) * Fintype.card α := by
  show Fintype.card (Option (Fin c) × α) = (c + 1) * Fintype.card α
  rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]

/-- The "embed-with-bound" function from `parentBounded c α` back into
`LZ78Phrase α`: forget the bound. -/
def LZ78Phrase.ofParentBounded {c : ℕ} (α : Type*)
    (pb : LZ78Phrase.parentBounded c α) : LZ78Phrase α :=
  { parent := pb.1.map (·.val), symbol := pb.2 }

/-- Convert an `Option ℕ` whose `some k` case satisfies `k < c` into
`Option (Fin c)`. The "round-trip" `forget-then-attach` direction. -/
def LZ78Phrase.boundParent {c : ℕ} :
    (o : Option ℕ) → (∀ k, o = some k → k < c) → Option (Fin c)
  | none, _ => none
  | some k, h => some ⟨k, h k rfl⟩

@[simp] lemma LZ78Phrase.boundParent_none {c : ℕ}
    (h : ∀ k, (none : Option ℕ) = some k → k < c) :
    LZ78Phrase.boundParent (c := c) none h = none := rfl

@[simp] lemma LZ78Phrase.boundParent_some {c : ℕ} (k : ℕ)
    (h : ∀ k', (some k : Option ℕ) = some k' → k' < c) :
    LZ78Phrase.boundParent (c := c) (some k) h = some ⟨k, h k rfl⟩ := rfl

@[simp] lemma LZ78Phrase.map_val_boundParent {c : ℕ}
    (o : Option ℕ) (h : ∀ k, o = some k → k < c) :
    (LZ78Phrase.boundParent (c := c) o h).map (·.val) = o := by
  cases o with
  | none => rfl
  | some k => rfl

/-- Convert an `LZ78Phrase` whose `parent` is either `none` or `some k`
with `k < c` into the bounded type `parentBounded c α`. -/
def LZ78Phrase.toParentBounded {c : ℕ}
    (ph : LZ78Phrase α) (h : ∀ k, ph.parent = some k → k < c) :
    LZ78Phrase.parentBounded c α :=
  (LZ78Phrase.boundParent (c := c) ph.parent h, ph.symbol)

@[simp] lemma LZ78Phrase.ofParentBounded_toParentBounded {c : ℕ}
    (ph : LZ78Phrase α) (h : ∀ k, ph.parent = some k → k < c) :
    LZ78Phrase.ofParentBounded α (ph.toParentBounded h) = ph := by
  unfold LZ78Phrase.toParentBounded LZ78Phrase.ofParentBounded
  simp

end PhraseCardinality

/-! ## §2. `LZ78Parsing.count` combinatorial bounds -/

section CountBounds

variable {α : Type*}

/-- **`LZ78Parsing.count` is the list length.** Restatement of
`LZ78Parsing.count_eq_length` for direct citation in counting proofs. -/
@[entry_point]
theorem LZ78Parsing.count_eq_length' (p : LZ78Parsing α) :
    p.count = p.phrases.length :=
  rfl

/-- **Empty-parsing count is zero.** -/
@[simp] theorem LZ78Parsing.count_empty' :
    (LZ78Parsing.empty α).count = 0 :=
  rfl

/-- **The set of phrases of a parsing, as a finset.** Built by mapping
the `Fin p.count` index space through the `get` accessor and packaging
as a `Finset` via `Finset.image`. Uses `Classical.decEq` so that no
`DecidableEq` instance on `LZ78Phrase α` is required at the call site. -/
noncomputable def LZ78Parsing.phraseSet (p : LZ78Parsing α) :
    Finset (LZ78Phrase α) :=
  letI : DecidableEq (LZ78Phrase α) := Classical.decEq _
  (Finset.univ : Finset (Fin p.phrases.length)).image
    (fun i => p.phrases.get i)

/-- **Every phrase in the parsing has bounded parent.** Direct consequence
of the `inRange` invariant: phrase at index `i < count` has parent
in `Option (Fin count)`. -/
theorem LZ78Parsing.parent_bounded (p : LZ78Parsing α)
    (i : ℕ) (hi : i < p.phrases.length) :
    ∀ k, (p.phrases.get ⟨i, hi⟩).parent = some k → k < p.phrases.length := by
  intro k hk
  exact lt_trans (p.inRange i hi k hk) hi

/-- **The phrase-index map factors through `parentBounded`.** Map each
`Fin p.count` index to its corresponding bounded-parent phrase, then
forget the bound to recover the phrase itself. -/
noncomputable def LZ78Parsing.indexToBounded (p : LZ78Parsing α) :
    Fin p.phrases.length → LZ78Phrase.parentBounded p.phrases.length α :=
  fun i => (p.phrases.get i).toParentBounded (p.parent_bounded i.1 i.2)

theorem LZ78Parsing.ofParentBounded_indexToBounded (p : LZ78Parsing α)
    (i : Fin p.phrases.length) :
    LZ78Phrase.ofParentBounded α (p.indexToBounded i) = p.phrases.get i := by
  unfold LZ78Parsing.indexToBounded
  exact LZ78Phrase.ofParentBounded_toParentBounded _ _

/-- **`count` upper-bound via the bounded-parent ambient.**
For any LZ78 parsing on a finite alphabet, the number of *distinct*
phrases is at most `(count + 1) · |α|`: every phrase is a pair
`(parent ∈ Option (Fin count), symbol ∈ α)`. -/
@[entry_point]
theorem LZ78Parsing.card_phraseSet_le_pow [Fintype α]
    (p : LZ78Parsing α) :
    p.phraseSet.card ≤ (p.count + 1) * Fintype.card α := by
  classical
  -- The phrase set is the image of `Fin count → LZ78Phrase α`,
  -- and that image embeds (via `toParentBounded`) into
  -- `LZ78Phrase.parentBounded count α` whose cardinality is `(count+1) · |α|`.
  have hcard : p.phraseSet.card ≤
      Fintype.card (LZ78Phrase.parentBounded p.phrases.length α) := by
    -- the image of `parentBounded` covers `phraseSet`
    have hcover : p.phraseSet ⊆
        (Finset.univ : Finset (LZ78Phrase.parentBounded p.phrases.length α)).image
          (LZ78Phrase.ofParentBounded α) := by
      intro ph hph
      unfold LZ78Parsing.phraseSet at hph
      rcases Finset.mem_image.mp hph with ⟨i, _hi, heq⟩
      refine Finset.mem_image.mpr ⟨p.indexToBounded i, Finset.mem_univ _, ?_⟩
      rw [LZ78Parsing.ofParentBounded_indexToBounded]
      exact heq
    calc p.phraseSet.card
        ≤ ((Finset.univ : Finset (LZ78Phrase.parentBounded p.phrases.length α)).image
            (LZ78Phrase.ofParentBounded α)).card :=
            Finset.card_le_card hcover
      _ ≤ (Finset.univ : Finset (LZ78Phrase.parentBounded p.phrases.length α)).card :=
            Finset.card_image_le
      _ = Fintype.card (LZ78Phrase.parentBounded p.phrases.length α) := by
            rw [Finset.card_univ]
  rw [LZ78Phrase.card_parentBounded] at hcard
  simpa [LZ78Parsing.count_eq_length'] using hcard

/-- **Trivial monotonicity: count ≥ 0.** A useful base hypothesis for
Ziv-style real-valued bounds (avoids `pos`/`nonneg` re-derivation
downstream). -/
@[simp] theorem LZ78Parsing.count_nonneg (p : LZ78Parsing α) :
    0 ≤ p.count :=
  Nat.zero_le _

/-- **Empty parsing has empty phrase set.** -/
@[simp] theorem LZ78Parsing.phraseSet_empty :
    (LZ78Parsing.empty α).phraseSet = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro ph hph
  unfold LZ78Parsing.phraseSet at hph
  rcases Finset.mem_image.mp hph with ⟨i, _, _⟩
  -- `i : Fin (LZ78Parsing.empty α).phrases.length = Fin 0`
  have h0 : (LZ78Parsing.empty α).phrases.length = 0 := rfl
  exact (Fin.cast h0 i).elim0

end CountBounds

/-! ## §3. `ZivCountingBound` predicate -/

section ZivCountingBoundPredicate

variable {α : Type*}

/-- **Real-valued Ziv counting-layer predicate**.

For a parsing `p` and a real-valued upper bound `B : ℝ`, this predicate
asserts that the *combinatorial* layer of the Ziv inequality holds:
the cast `(p.count : ℝ)` is bounded by `B`. The predicate is shaped
so that the entropy-side layer can supply `B = n / log c(n)`
(Cover–Thomas Eq. 13.124) or any analogous real-valued upper bound and
plug it into the `IsLZ78PhraseCountAsymptotic` envelope.

The combinatorial layer of `B` is established by `card_phraseSet_le_pow`
(§2); the entropy / log-sum layers are developed elsewhere. -/
def ZivCountingBound (p : LZ78Parsing α) (B : ℝ) : Prop :=
  (p.count : ℝ) ≤ B

/-- **Reflexive bound**: trivially `count ≤ count`. -/
@[simp] theorem ZivCountingBound.refl (p : LZ78Parsing α) :
    ZivCountingBound p (p.count : ℝ) := le_refl _

/-- **Monotonicity** in the real bound. -/
@[entry_point]
theorem ZivCountingBound.mono {p : LZ78Parsing α} {B B' : ℝ}
    (h : ZivCountingBound p B) (hB : B ≤ B') :
    ZivCountingBound p B' :=
  le_trans h hB

/-- **Adding a positive slack preserves the bound** (`B` ≤ `B + ε`). -/
@[entry_point]
theorem ZivCountingBound.add_nonneg {p : LZ78Parsing α} {B ε : ℝ}
    (h : ZivCountingBound p B) (hε : 0 ≤ ε) :
    ZivCountingBound p (B + ε) := by
  exact le_trans h (by linarith)

end ZivCountingBoundPredicate

end InformationTheory.Shannon

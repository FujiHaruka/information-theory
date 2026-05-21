# Network IT (Ch.15): de-circularize headline repair plan

> **Parent**: standalone repair plan (cross-cuts T3-B MAC / T3-E BC / T3-F Relay).
> Companion source-of-truth: `docs/shannon/flaw-vacuous-review-2026-05-20.md`
> (LOW/BY-DESIGN cluster), and the *precedent fix* for this exact pattern is the
> ShannonHartley / WhittakerShannon "circular → honest conditional pass-through"
> repair recorded there (§"Related: Shannon-Hartley", 2026-05-20).

## 進捗

- [ ] M0 在庫確認 (Fano/chain machinery, error-prob machinery) 📋
- [ ] Phase A — MAC outer + inner 📋
- [ ] Phase B — BC outer + inner 📋
- [ ] Phase C — Relay cutset outer + DF/CF inner 📋
- [ ] Phase D — caller migration + flaw-review update 📋

proof-log: yes (one `proof-log-network-it-decircularize.md` covering all 3 clusters; each
genuine-vs-honest verdict transition is logged).

## ゴール / Approach

Seven Ch.15 headlines are **circular**: body `:= h_hyp` where the consumed hypothesis
*is* the conclusion verbatim, and the real IT residual sits in inert `_h_… : True`
slots the proof never touches. Convert each into a **sound landing**:

- **(A) Outer bounds** (`mac_capacity_region_outer_bound`,
  `bc_capacity_region_outer_bound`, `relay_cutset_outer_bound`): make as **genuine**
  as the SlepianWolf converse already is — i.e. *derive* `R ≤ bound` from
  `MeasureFano.fano_inequality_measure_theoretic` + entropy chain steps — to the
  extent the per-direction reduction is single-user. Where the per-letter chain rule
  / joint-message Fano is not yet a Mathlib/project lemma, fall back to the **honest
  🟢ʰ** form: replace the circular `h_rate_bound : R ≤ bound` with a *non-circular*
  named hypothesis capturing the genuine Fano/chain step (e.g. an entropy-level
  `n·R ≤ I_marg + 1 + Pe·log M` plus a per-letter `I_marg ≤ n·I`), from which
  `R ≤ bound` is **derived by the body**, not assumed.

- **(B) Inner bounds** (`mac_capacity_region_inner_bound`,
  `bc_capacity_region_inner_bound`, `relay_df_inner_bound`, `relay_cf_inner_bound`):
  the joint-typicality random-coding core is a genuine Mathlib gap — keep honest,
  but **fix the circularity AND the missing error bound**. The current existence
  predicates `∃ M, exp(nR) ≤ M` omit any error-probability content, so they are
  satisfiable by *any* code at *any* rate. Redefine each existence predicate to embed
  the achievability error content (`averageErrorProb → 0`), make the redefined
  predicate the consumed *non-circular* named hypothesis, and have the headline
  **derive** the rate-region membership conclusion from it.

**The decisive prior art** (read before any edit):

1. `Common2026/Shannon/SlepianWolf.lean:217 / :293 / :361` —
   `slepian_wolf_converse_X/_Y/_sum` are **genuinely** proved (not `:= h`). The
   skeleton is: `entropy_le_log_card` (log M ≥ H(E)) → `entropy_ge_condEntropy`
   (H(E) ≥ H(E|Y)) → `condMutualInfo_eq_condEntropy_sub_condEntropy` ×2 +
   `condMutualInfo_comm` (bridge) → `fano_inequality_with_side_info` /
   `fano_inequality_measure_theoretic` (H(·|·) ≤ binEntropy Pe + Pe·log(card−1)).
   These are the composable lemmas for **(A)**.
2. `Common2026/Shannon/MACFanoConverseBody.lean:205` `macFanoEntropyData_of_measure`
   and `:236` `macSingleFanoBound_of_measure` — **the per-user MAC Fano bound is
   ALREADY genuinely discharged** through `MeasureFano.fano_inequality_measure_theoretic`.
   `:294 mac_capacity_region_outer_bound_with_per_user_fano` already builds a
   non-circular per-user-genuine outer-bound landing. The de-circularization for MAC
   per-user is largely *promotion of an existing companion to be THE headline*.
3. `Common2026/Shannon/MACL2Discharge.lean:132 MACSingleFanoBound`, `:169/:191
   MACPerLetterChain₁/₂`, `:456 mac_capacity_region_outer_bound_with_full_fano_body`
   — shows where the residual still sits: the **per-letter chain rule** (`chain :
   I_marg ≤ n·I`) and the **joint-message Fano** (`MACFanoBound`) are still
   *structural* Props whose field is assumed, NOT derived. These are the honest-🟢ʰ
   slots that remain after the per-user genuine step.
4. `Common2026/Shannon/ChannelCoding.lean:210 Code.averageErrorProb` (+ `:218
   averageErrorProb_le_one`) — the error-probability machinery for the inner-bound
   predicate redefinition exists for `Code`; the MAC/BC/Relay code structures
   (`MACCode`/`BroadcastCode`/`RelayCode`) need an analogous `averageErrorProb` field
   or a thin per-structure copy.

**IT residual is a real Mathlib gap** (audit-confirmed: 0 typicality lemmas, 0
IT-Fano in Mathlib). The genuine Fano + entropy-chain primitives live in the project
(`Common2026/Fano/Measure.lean`, `CondMutualInfo.lean`, `MIChainRule.lean`) and ARE
load-bearing in SlepianWolf — so outer bounds can be pushed to genuine where the
reduction is single-user; the joint-typicality core stays honest.

---

## Per-headline classification (verdict table)

| # | headline | file:line | target | replacement consumed hypothesis |
|---|----------|-----------|--------|---------------------------------|
| 1 | `mac_capacity_region_outer_bound` | MultipleAccessChannel.lean:464 | **genuine (per-user) + honest-🟢ʰ (chain/joint)** | `MACSingleFanoBound`×2 (genuine via `macFanoEntropyData_of_measure`) + `MACPerLetterChain₁/₂` + `MACFanoBound` (joint) + cleanup; **NO** `InMACCapacityRegion` hyp |
| 2 | `mac_capacity_region_inner_bound` | MultipleAccessChannel.lean:567 | **honest-🟢ʰ** | redefined `MACInnerBoundExistence` with error bound (see Phase A.4) |
| 3 | `bc_capacity_region_outer_bound` | BroadcastChannel.lean:472 | **genuine (R₂ via single-user Fano) + honest-🟢ʰ (R₁ conditional + chain)** | `BCFanoBound` (R₂; genuine via `fano_inequality_measure_theoretic` on W₂→Y₂) + `BCCondFanoBound` (R₁ conditional) + `BCPerLetterChain` + cleanup; **NO** `InBCCapacityRegion` hyp |
| 4 | `bc_capacity_region_inner_bound` | BroadcastChannel.lean:580 | **honest-🟢ʰ** | redefined `BCInnerBoundExistence` with error bound |
| 5 | `relay_cutset_outer_bound` | RelayCutset.lean:343 | **honest-🟢ʰ** (genuine *attempt* on each cut; see retreat) | `RelayBcastCutFano` + `RelayMacCutFano` (each: entropy-level non-circular Fano/Csiszár step) → `relay_cutset_combine`; **NO** `R ≤ relayCutsetBound` hyp |
| 6 | `relay_df_inner_bound` | RelayInnerBound.lean:419 | **honest-🟢ʰ** | redefined `RelayDFInnerBoundExistence` with error bound |
| 7 | `relay_cf_inner_bound` | RelayInnerBound.lean:531 | **honest-🟢ʰ** | redefined `RelayCFInnerBoundExistence` with error bound |

**Genuinely SlepianWolf-dischargeable?** Partially. The *single-user* directions
(MAC per-user R₁/R₂, BC R₂) ARE genuinely dischargeable by the exact SlepianWolf
recipe — and MAC's already is (`macFanoEntropyData_of_measure`). The directions that
require the per-letter chain rule (`I(X^n;Y^n) ≤ ∑ I(Xᵢ;Yᵢ)`) or the joint-message /
Csiszár sum identity are NOT yet project lemmas, so those slots land honest-🟢ʰ
(non-circular entropy-level hypothesis the body consumes and derives `R ≤ bound`
from). No headline lands as a circular `:= h`.

---

## M0 — 在庫確認 📋

- [ ] Confirm `MeasureFano.fano_inequality_measure_theoretic` and
  `fano_inequality_with_side_info` signatures (full `[...]` prereqs verbatim) from
  `Common2026/Fano/Measure.lean`; record arg order. These are the genuine-outer engine.
- [ ] Confirm `entropy_le_log_card`, `entropy_ge_condEntropy`,
  `condMutualInfo_eq_condEntropy_sub_condEntropy`, `condMutualInfo_comm`,
  `mutualInfo_eq_entropy_sub_condEntropy`, `condEntropy_nonneg` namespaces/sigs.
- [ ] Confirm `Code.averageErrorProb` shape (ℝ≥0∞-valued, uniform-message average)
  and whether `MACCode`/`BroadcastCode`/`RelayCode` already carry an error-prob
  helper. If not, scope a thin per-structure `averageErrorProb` def (M0 output:
  one def per structure or a shared one).
- [ ] loogle re-confirm IT gap (`jointly typical`, IT-Fano) returns 0 — gates the
  honest-vs-genuine boundary for the inner bounds. (Audit already says 0; record the
  exact loogle line in the proof-log for provenance.)
- [ ] Inventory delegation: emit findings to
  `docs/shannon/network-it-decircularize-mathlib-inventory.md` (owned by
  `mathlib-inventory`, NOT this plan) with per-lemma `file:line` + verbatim
  `[...]` prereqs + conclusion form.

---

## Phase A — MAC cluster (do first; most machinery already exists) 📋

### A.1 — MAC outer bound: promote genuine per-user + honest chain/joint
Target `mac_capacity_region_outer_bound` (MultipleAccessChannel.lean:464).

- [ ] **New signature** (replaces the circular one). Consume the genuine/honest
  pieces, derive `InMACCapacityRegion`:
  ```
  theorem mac_capacity_region_outer_bound
      {M₁ M₂ n : ℕ} (hn : 0 < n)
      (c : MACCode M₁ M₂ n α₁ α₂ β)
      (R₁ R₂ Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε : ℝ)
      (h_fano₁ : MACSingleFanoBound M₁ n R₁ Pe₁ I_marg₁)      -- GENUINE feeder available
      (h_fano₂ : MACSingleFanoBound M₂ n R₂ Pe₂ I_marg₂)      -- GENUINE feeder available
      (h_fano_joint : MACFanoBound M₁ M₂ n R₁ R₂ Pe_joint I_joint)  -- honest (structural)
      (h_chain₁ : MACPerLetterChain₁ n I_marg₁ I₁)            -- honest (structural)
      (h_chain₂ : MACPerLetterChain₂ n I_marg₂ I₂)            -- honest (structural)
      (h_chain_joint : I_joint ≤ (n:ℝ) * Iboth)               -- honest
      (h_cleanup₁ …) (h_cleanup₂ …) (h_cleanup_joint …) :
      InMACCapacityRegion R₁ R₂ (I₁ + ε) (I₂ + ε) (Iboth + ε)
  ```
- [ ] **Body**: this is *exactly* `mac_capacity_region_outer_bound_with_fano_body`
  (MACL2Discharge.lean:379), which already type-checks and derives the region from
  these slots via `mac_converse_fano_body_single₁/₂` + `mac_converse_fano_body`. The
  edit is: make the headline name BE that derivation (move/rename so the published
  name is non-circular), and delete the old `:= h_rate_bound` body + the `_h_fano/_h_chain
  : True` slots + the `InMACCapacityRegion` hyp.
- [ ] Keep a `…_corner_limit` variant (`h_ε : ε ≤ 0 → InMACCapacityRegion R₁ R₂ I₁ I₂
  Iboth`) mirroring `mac_capacity_region_outer_bound_with_fano_body_limit`
  (MACL2Discharge.lean:405).
- [ ] **Genuineness wiring**: provide `mac_capacity_region_outer_bound_of_measure`
  that builds `h_fano₁/₂` from `macFanoEntropyData_of_measure`
  (MACFanoConverseBody.lean:205) so the per-user directions are *genuinely* Fano,
  not assumed. (`mac_capacity_region_outer_bound_with_per_user_fano`,
  MACFanoConverseBody.lean:294, is the existing template.)
- [ ] Verify: `lake env lean Common2026/Shannon/MultipleAccessChannel.lean` then
  `lake build Common2026.Shannon.MultipleAccessChannel` (olean refresh for the
  MACL2Discharge / MACFanoConverseBody dependents that reference the renamed headline).

### A.2 — keep `mac_capacity_region_outer_bound_three_bounds` / `_log_rate` honest
- [ ] Re-point the `_log_rate` and `_three_bounds` wrappers (MultipleAccessChannel.lean:482/497)
  at the new signature; drop their `True` slots. `_three_bounds` already derives via
  `mac_region_combine` (genuine combine) — keep as the unbundled exit point.

### A.3 — Retreat line for A.1
- [ ] If renaming the headline to the discharge body breaks too many dependents at
  once, instead: keep the headline name, give it the **honest non-circular Fano
  signature** above, but with `h_fano₁/₂` as the *structural* `MACSingleFanoBound`
  (not the measure feeder) — still non-circular (it's an entropy-level inequality,
  not `InMACCapacityRegion`), still derives the conclusion. Genuineness is then a
  separate `_of_measure` corollary. (This is the minimal de-circularization.)

### A.4 — MAC inner bound: redefine existence with error bound + derive
Target `mac_capacity_region_inner_bound` (MultipleAccessChannel.lean:567),
`MACInnerBoundExistence` (:531).

- [ ] **Redefine** the predicate to embed achievability error content:
  ```
  def MACInnerBoundExistence (R₁ R₂ : ℝ) : Prop :=
    ∀ ε > (0:ℝ), ∃ N : ℕ, ∀ n ≥ N,
      ∃ (M₁ M₂ : ℕ) (c : MACCode M₁ M₂ n α₁ α₂ β),
        Real.exp ((n:ℝ)*R₁) ≤ (M₁:ℝ) ∧ Real.exp ((n:ℝ)*R₂) ≤ (M₂:ℝ)
        ∧ MACCode.averageErrorProb c W < ENNReal.ofReal ε     -- NEW: error → 0
  ```
  (`W : MACChannel α₁ α₂ β` becomes a parameter of the predicate; `averageErrorProb`
  is the M0 thin def for `MACCode`. This is the textbook achievability claim:
  vanishing error for all `ε`.)
- [ ] **New headline signature**: consume the *redefined* (error-carrying)
  existence as a **non-circular** named hyp `h_existence` AND derive the
  conclusion (the redefined existence) from it — but now the predicate is genuinely
  stronger than the rate, so the wrap is the honest landing of an undischarged
  achievability (the joint-typicality core remains the `_h_joint_typ` gap, restated
  as a real implication, not `True`):
  ```
  theorem mac_capacity_region_inner_bound
      (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
      (R₁ R₂ I₁ I₂ Iboth : ℝ)
      (h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
      (h_jt : MACJointTypicalityAchievable W R₁ R₂ I₁ I₂ Iboth) :  -- honest IT residual, REAL Prop
      MACInnerBoundExistence W R₁ R₂
  ```
  where `MACJointTypicalityAchievable … : Prop := h_strict → MACInnerBoundExistence W R₁ R₂`
  is the **honest open hypothesis** (NOT `True`, NOT identical to the conclusion
  because it is gated on `h_strict` and is the *implication*, mirroring the
  ShannonHartley `h_two_w` precedent). Body: `h_jt h_strict`.
- [ ] Drop `_h_joint_typ : True`. Update `_bundled_strict` variant (:586) to the new
  signature.
- [ ] Verify single-file + olean refresh for `MACL1Discharge.lean`,
  `MACBodyDischarge.lean`, `MACRandomCodebookAveraging.lean` (callers, see blast radius).

---

## Phase B — BC cluster 📋

### B.1 — BC outer bound: genuine R₂, honest R₁-conditional + chain
Target `bc_capacity_region_outer_bound` (BroadcastChannel.lean:472).

- [ ] **New signature** mirrors A.1 reduced to two directions. R₂ (`R₂ ≤ I_u =
  I(U;Y₂)`) is a *single-user* Fano direction → genuine via
  `fano_inequality_measure_theoretic` on `W₂ → Y₂^n` (same recipe as MAC per-user).
  R₁ (`R₁ ≤ I_xy = I(X;Y₁|U)`) is a *conditional* Fano direction → honest-🟢ʰ
  (conditional Fano + degradation Markov chain not yet a project lemma).
  ```
  theorem bc_capacity_region_outer_bound
      {M₁ M₂ n} (hn : 0 < n) (c : BroadcastCode M₁ M₂ n α β₁ β₂)
      (R₁ R₂ Pe₂ Pe₁ I_marg_u I_marg_xy I_u I_xy ε : ℝ)
      (h_fano₂ : BCSingleFanoBound M₂ n R₂ Pe₂ I_marg_u)        -- GENUINE (single-user, mirror MAC)
      (h_cond_fano₁ : BCCondFanoBound M₁ n R₁ Pe₁ I_marg_xy)    -- honest (conditional)
      (h_chain_u : I_marg_u ≤ (n:ℝ)*I_u)                        -- honest (per-letter chain)
      (h_chain_xy : I_marg_xy ≤ (n:ℝ)*I_xy)                     -- honest
      (h_cleanup₂ …) (h_cleanup₁ …) :
      InBCCapacityRegion R₁ R₂ (I_u + ε) (I_xy + ε)
  ```
- [ ] **New lemmas to author** (mirroring MACL2Discharge / MACFanoConverseBody for BC):
  `BCSingleFanoBound`, `BCCondFanoBound` structural Props; `bcFanoEntropyData_of_measure`
  genuine feeder for the R₂ direction (copy `macFanoEntropyData_of_measure`); a
  `bc_region_combine`-based body that derives `InBCCapacityRegion` from the two
  direction bounds + cleanup. Put these in a new `Common2026/Shannon/BCL2Discharge.lean`
  (do NOT bloat the headline file).
- [ ] Body of the headline: derive R₂ ≤ I_u+ε from `h_fano₂`+`h_chain_u`+cleanup,
  R₁ ≤ I_xy+ε from `h_cond_fano₁`+`h_chain_xy`+cleanup, combine via `bc_region_combine`.
- [ ] Drop `_h_fano/_h_chain : True` and the `InBCCapacityRegion` hyp. Re-point
  `_two_bounds`/`_log_rate` (BroadcastChannel.lean:489/504).
- [ ] Verify single-file + olean refresh for `BroadcastChannelSuperposition.lean`,
  `BroadcastChannel*Body.lean` dependents.

### B.2 — BC inner bound: redefine existence + derive
Target `bc_capacity_region_inner_bound` (BroadcastChannel.lean:580),
`BCInnerBoundExistence` (:539). Identical pattern to A.4:
- [ ] Redefine `BCInnerBoundExistence` to carry `averageErrorProb < ofReal ε` (∀ε>0).
- [ ] New headline consumes a non-circular `BCSuperpositionAchievable W R₁ R₂ … : Prop`
  (the honest open hyp = `h_strict → BCInnerBoundExistence …`) and derives the
  conclusion; drop `_h_joint_typ : True`.
- [ ] Update `_bundled_strict` (:599). Verify + olean refresh
  (`BroadcastChannelSuperposition.lean:548` caller).

---

## Phase C — Relay cluster 📋

### C.1 — Relay cutset outer bound
Target `relay_cutset_outer_bound` (RelayCutset.lean:343). `relayCutsetBound Ib Im =
min Ib Im` (RelayCutset.lean:188); `relay_cutset_combine` (:294) genuinely derives
`R ≤ min Ib Im` from the two cut bounds via `le_min`.

- [ ] **New signature** lands honest-🟢ʰ on each cut (broadcast cut `R ≤ Ib =
  I(X,X₁;Y)` and MAC cut `R ≤ Im = I(X;Y,Y₁|X₁)`), then combines genuinely:
  ```
  theorem relay_cutset_outer_bound
      {M n} (hn : 0 < n) (c : RelayCode M n α α₁ β β₁)
      (R Ib Im Pe I_marg_b I_marg_m ε : ℝ)
      (h_fano_b : RelayBcastCutFano M n R Pe I_marg_b)   -- entropy-level non-circular (broadcast cut)
      (h_fano_m : RelayMacCutFano M n R Pe I_marg_m)      -- entropy-level non-circular (MAC cut, Csiszár)
      (h_chain_b : I_marg_b ≤ (n:ℝ)*Ib) (h_chain_m : I_marg_m ≤ (n:ℝ)*Im)
      (h_cleanup_b …) (h_cleanup_m …) :
      R ≤ relayCutsetBound (Ib + ε) (Im + ε)
  ```
- [ ] **New lemmas** (new `Common2026/Shannon/RelayCutsetL1Discharge.lean`):
  `RelayBcastCutFano`, `RelayMacCutFano` structural Props (each `n·R ≤ I_marg + 1 +
  Pe·log M`, same shape as `MACSingleFanoBound`); per-cut body lemmas deriving `R ≤
  Ib+ε` / `R ≤ Im+ε`; headline body = `relay_cutset_combine` on the two.
- [ ] **Genuine attempt**: the broadcast cut `R ≤ I(X,X₁;Y)` is single-user Fano
  (message W → output Y^n) → genuinely dischargeable via
  `fano_inequality_measure_theoretic` exactly like MAC. Provide
  `relay_cutset_outer_bound_of_measure` building `h_fano_b` genuinely. The MAC cut
  needs Csiszár's sum identity (not a project lemma) → stays honest structural.
- [ ] **Retreat line**: if even the entropy-level structural Props are awkward to
  thread, fall back to two non-circular *scalar* Fano hyps `n·R ≤ n·Ib + 1 + Pe·log
  M` etc. supplied directly (still non-circular: log-M/Pe form, not `R ≤
  relayCutsetBound`), body does the `/n` + `le_min` algebra.
- [ ] Drop `_h_csiszar/_h_chain : True` and `h_rate_bound`. Re-point `_two_cuts`/`_log_rate`
  (RelayCutset.lean:360/374). Verify + olean refresh (`RelayInnerBound.lean:603/623`
  two-side combine callers).

### C.2 — Relay DF inner bound
Target `relay_df_inner_bound` (RelayInnerBound.lean:419),
`RelayDFInnerBoundExistence` (:305). Pattern of A.4 with single rate `R`:
- [ ] Redefine `RelayDFInnerBoundExistence` to carry `averageErrorProb < ofReal ε`
  (∀ε>0). Update its `anti_mono` (:334) proof (extra error conjunct passes through;
  error bound is rate-independent so survives the `exp` monotone step).
- [ ] New headline consumes non-circular `RelayDFAchievable W R … : Prop`
  (= `InRelayDFRate R … → RelayDFInnerBoundExistence … R`, the honest open hyp);
  derives the conclusion. Drop `_h_block_markov/_h_sliding_window : True`. Note the
  consumed `InRelayDFRate` is *already a genuine `Prop`* — keep it as a real gating
  hypothesis, but the body must now go through the achievable-implication, not `:=
  h_existence`.
- [ ] Re-point `_min_form`/`_two_bounds`/`_log_rate` (:441/457/472).

### C.3 — Relay CF inner bound
Target `relay_cf_inner_bound` (RelayInnerBound.lean:531),
`RelayCFInnerBoundExistence` (:322). Identical to C.2:
- [ ] Redefine `RelayCFInnerBoundExistence` with error bound; fix `anti_mono` (:354).
- [ ] New headline consumes non-circular `RelayCFAchievable W R … : Prop`
  (= `InRelayCFRate R … → RelayCFInnerBoundExistence … R`); derives conclusion. Drop
  `_h_wz_binning/_h_si_decode : True`.
- [ ] Re-point `_two_conditions`/`_log_rate` (:545/569). Verify
  `RelayInnerBound.lean` single-file + `RelayCFBinningBody.lean` olean refresh.

---

## Phase D — caller migration + flaw-review update 📋

- [ ] **Blast radius** (callers of the 7 headlines, from grep):
  - `MACRandomCodebookAveraging.lean:595` (outer+inner two-side combine)
  - `MACBodyDischarge.lean:620/638` (inner/outer discharge wrappers)
  - `MACL1Discharge.lean:537` (inner partial-discharge)
  - `MACL2Discharge.lean:462` (outer full-fano-body wrapper)
  - `BroadcastChannel.lean:644/645` (two-side combine)
  - `BroadcastChannelSuperposition.lean:548` (inner partial-discharge)
  - `MultipleAccessChannel.lean:631/632` (own two-side combine)
  - `RelayInnerBound.lean:603/604/623/624` (two-side combine, both outer + DF/CF)
  - `RelayCFBinningBody.lean:59` (CF placeholder upgrade)
  Each currently passes `trivial trivial h_rate_bound` / `… h_existence`. After the
  signature changes, every call site must supply the new (Fano/chain/error) args.
  Most are themselves discharge wrappers that *already have* the Fano/chain bodies in
  scope (MACL2Discharge, MACFanoConverseBody) — re-thread, do not re-prove.
- [ ] For each touched file, `lake env lean <file>` clean (0 sorry / minimal warn),
  then one `lake build Common2026.Shannon.<Module>` per upstream-renamed module to
  refresh dependents' oleans.
- [ ] Update `docs/shannon/flaw-vacuous-review-2026-05-20.md`: the LOW/BY-DESIGN MAC/
  BC/Relay entry (§:189-200) — record the 7 headlines as **de-circularized** with
  their new genuine/honest-🟢ʰ classification, mirroring the ShannonHartley
  "RESOLVED" entry style. (append-only spirit: add a dated follow-up note, do not
  rewrite the original finding.)
- [ ] proof-log: record per-headline before/after body, the genuine-vs-honest
  verdict, and the loogle provenance for the IT gap.

---

## Blast radius (summary)

- **Direct code callers**: 13 call sites across 8 files (listed in Phase D). All are
  in-tree discharge/combine wrappers — no external API consumers.
- **olean refresh required** after renaming headlines in MultipleAccessChannel /
  BroadcastChannel / RelayCutset / RelayInnerBound: every dependent module that
  `#check`s or applies the headline by name (MACL1/L2/Body/Fano discharge,
  BroadcastChannelSuperposition, RelayCFBinningBody).
- **Predicate-redefinition fan-out**: the 4 inner-bound existence redefinitions add a
  `W` channel parameter + error conjunct → every reference to
  `MAC/BC/RelayDF/RelayCFInnerBoundExistence` (incl. the `anti_mono` lemmas and the
  two-side `…_region` combiners) takes the new shape. Grep
  `rg "InnerBoundExistence"` before editing to enumerate.

## 撤退ライン (retreat lines)

1. **Genuine outer stalls** (per-letter chain rule / Csiszár sum not extractable as a
   project lemma within budget) → fall back to the **honest non-circular Fano
   hypothesis** form: consume entropy-level `MACSingleFanoBound`-shaped structural
   Props (`n·R ≤ I_marg + 1 + Pe·log M`) + scalar per-letter chain `I_marg ≤ n·I`,
   body derives `R ≤ I + ε`. This is still a *de-circularization* (hypothesis ≠
   conclusion; body does real algebra) even with zero new genuine Fano discharge,
   because the per-user MAC genuine feeder already exists and BC R₂ / relay broadcast
   cut reuse it verbatim.
2. **Headline rename breaks too many dependents at once** → keep the headline name,
   swap only its *signature* to the honest non-circular form (A.3), and add
   genuineness as a separate `_of_measure` corollary; migrate callers incrementally.
3. **`averageErrorProb` for `MACCode`/`BroadcastCode`/`RelayCode` is heavier than a
   thin copy** → define the error conjunct of the redefined existence predicate
   abstractly as `Pe : ℝ` with `0 ≤ Pe` and `∀ε>0 …, Pe < ε` over the code's own
   `errorEvent` measure, rather than reusing `Code.averageErrorProb`. The point is
   the predicate must be *unsatisfiable by arbitrary codes at arbitrary rates* — any
   genuine vanishing-error conjunct achieves that.
4. **Conditional/joint Fano structural Props feel like re-introducing `True`** →
   they are NOT `True`-equivalent: each is a real `≤` inequality on entropies/MI
   that the body *consumes to derive the conclusion*. The line in the sand: the
   consumed hypothesis must not be `InMACCapacityRegion`/`R ≤ relayCutsetBound`/the
   bare existence — it must be the entropy-level Fano/chain step. If a slot cannot be
   made entropy-level, leave it as an explicit named open hypothesis (ShannonHartley
   `h_two_w` precedent), never `: True`.

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **当初仮定の修正 (起草時)**: 監査は MAC outer も完全に circular と整理していたが、
   `MACFanoConverseBody.lean:205/294` で per-user Fano は既に
   `MeasureFano.fano_inequality_measure_theoretic` 経由で genuine に discharge 済み、
   `mac_capacity_region_outer_bound_with_fano_body` (MACL2Discharge.lean:379) が
   非循環な landing を既に型検査している。よって MAC outer の修復は「既存 companion を
   headline に昇格」が主作業であり、新規 genuine Fano 証明は不要。BC R₂ / relay 放送カットも
   この per-user genuine 経路を流用可能と判断。

import InformationTheory.Shannon.ChannelCoding.Achievability.Core
import InformationTheory.Shannon.ChannelCoding.Achievability.RandomCodebook
import InformationTheory.Shannon.ChannelCoding.Achievability.Main

/-!
# Channel coding achievability theorem (B-3'')

[B-3'' Phase C+D plan](../../../docs/shannon/channel-coding-phase-cd-plan.md).

Phase A+B are completed in `InformationTheory/Shannon/ChannelCoding.lean` (659 行).
This file adds:

* **Phase C** (random codebook + averaging argument): Codebook + joint typical
  decoder definition; per-codeword error decomposition; random-codebook average
  bound; pigeonhole `∃ codebook, P_err ≤ avg`.
* **Phase D** (main theorem): `R < I(p; W) ⟹ ∃ N, ∀ n ≥ N, ∃ M ≥ exp(nR), ∃ code,
  averageErrorProb < ε`.

Skeleton phase: every lemma/theorem body is `:= by sorry` (or `:= sorry` for
non-`Prop` definitions that are sorry-placeheld). The next agent fills.

## Design choices

* Codebook is `Fin M → (Fin n → α)` (abbrev).
* The **codebook average** is taken over the `p`-i.i.d. law
  `codebookMeasure p M n := Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))`
  on the finite space `Codebook M n α`. The earlier-drafted uniform-on-codebook form
  is **inconsistent** with the Phase B bounds unless `p` is uniform on `α`; the
  probabilistic-method form (this file) matches Cover-Thomas Theorem 7.7.3-4.
* Decoder = `Classical.dec`-based "unique joint-typical `m`, else fallback `⟨0, hM⟩`".
* i.i.d. extension `Ω := Fin n → α × β`, `μ := Measure.pi (fun _ => jointDistribution p W)`
  is captured by `iidJointMeasure p W n` below; Phase D-(b) will use the infinite
  version `Measure.infinitePi (jointDistribution p W)` once that plumbing is in.
* Rate slack `ε := (I - R) / 6`; `M := Nat.ceil (Real.exp (n · R))`.

## Module structure (longFile split)

This file is an **umbrella** re-exporting the three parts under
`Achievability/`:

* `Achievability.Core` — Phase 0 / C-(a) / C-(b) / C-(c) definitions.
* `Achievability.RandomCodebook` — Fubini swap helpers + `random_codebook_average_le`.
* `Achievability.Main` — pigeonhole + `channel_coding_achievability`.
-/

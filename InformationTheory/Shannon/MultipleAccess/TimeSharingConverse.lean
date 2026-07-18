import InformationTheory.Shannon.MultipleAccess.TimeSharingConverse.Bridge
import InformationTheory.Shannon.MultipleAccess.TimeSharingConverse.Assembly

/-!
# Multiple access channel — time-sharing converse (convex-geometry gateway)

The pure convex-geometry core of the two-user MAC time-sharing converse.  An achievable rate
pair `(R₁, R₂)` bounded, coordinate-wise, by the time averages of a family of per-letter
pentagons lies in the convex hull of the union of those pentagons.

This file currently provides only the geometric gateway lemma
`mac_avgPentagon_mem_convexHull`; the measure-theoretic gaps (code→ambient bridge, weak-converse
limit extraction, per-letter identification) are handled elsewhere.

## Note on hypotheses

The gateway lemma requires **both** `a i ≤ c i` and `b i ≤ c i`.  These are the two single-user
mutual-information bounds `I(X₁;Y|X₂) ≤ I(X₁,X₂;Y)` and `I(X₂;Y|X₁) ≤ I(X₁,X₂;Y)` in the MAC
application.  Without `b i ≤ c i` the statement is false: with `n = 2`, `a = (0,4)`, `b = (4,0)`,
`c = (0,4)`, the point `(0,2)` satisfies every remaining hypothesis yet the union of pentagons
collapses onto the `x`-axis, so `(0,2)` is not in the hull.

## Module structure

Umbrella of the `Shannon/MultipleAccess/TimeSharingConverse/` family, re-exporting:

* `TimeSharingConverse.Bridge` — the convex-geometry gateway `mac_avgPentagon_mem_convexHull`,
  pentagon well-formedness, the code → ambient bridge, rate extraction, and per-letter
  information transport.
* `TimeSharingConverse.Assembly` — the converse headline `mac_timesharing_converse`, assembled
  from the Fano → 0 limit, the rate-point construction, and the axis casework.
-/

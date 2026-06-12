# Chernoff converse 完全 discharge (Sanov 経由) サブ計画 🌙 (T1-B)

**Status**: CLOSED ✅ — Chernoff converse headline を regularity-only (無条件、標準B) で genuine discharge。当初の per-tilt predicate は一般に偽と判明し、ε-relaxed 形 (vanishing prefactor を `exp(-n·ε)` で吸収) に pivot して着地。
**SoT**: `docs/shannon/cramer-facts.md` + `docs/textbook-roadmap.md` Ch.11。詳細履歴は git。
> **Parent**: [`chernoff-converse-moonshot-plan.md`](chernoff-converse-moonshot-plan.md)

## 要点 (≤5 行)
- tilted mediator measure を ambient に据えた log-ratio band 上の change-of-measure (逆 Hölder per-point + band 確率→1) で構成。
- band 確率→1 は Stein の Ω-RV 形ではなく `Measure.infinitePi Q` 上の SLLN 直接適用 (interior optimality で Q-mean = 0) で discharge。
- 旧 per-tilt predicate (`IsBayesErrorPerTiltLowerBound` / `IsChernoffNLetterRN`) は一般に偽 (Cramér local-limit prefactor のため定数 C が存在しない)。これらを経由した死コードは後継 file で superseded。

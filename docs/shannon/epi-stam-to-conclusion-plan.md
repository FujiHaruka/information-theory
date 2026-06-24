# EPI Stam → EPI conclusion — B-wire honest discharge plan

**Status**: CLOSED ✅ — 一般 EPI は親 moonshot が無条件 dispatch + route T で別ルート closure 済 (`entropyPowerExt_add_ge_unconditional`)。本 plan の Phase B (legacy 実数 `entropy_power_inequality` の Stam-bridge 経由 closure) は textbook goal に不要となり SUPERSEDED。closure 対象だった legacy Stam-bridge + 露出 decl は物理削除済。Phase A (`entropy_power_inequality_of_density`、`EPIDensityForm.lean`) は CLOSED のまま生存。(Stam Step 2: re-scope candidate — see 要点)
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

- 親: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) (無条件 EPI moonshot、B-wire = 最終 wall)
- producer closure: [`epi-debruijn-pertime-closure-plan.md`](epi-debruijn-pertime-closure-plan.md)
- methodX wrapper: [`epi-case1-phaseC-methodx-wrapper-plan.md`](epi-case1-phaseC-methodx-wrapper-plan.md)

## 要点

**着地した Phase A route = 3-noise lift + two-time terminal** (旧 2-noise methodX route は sum-instance 𝒩(0,2) の uninhabitable 構造制約で RETRACTED)。再開時に再利用できる backbone:

```
base (Ω,P) ──[3-noise lift liftMeasure3]──→ (Ω×ℝ×ℝ×ℝ)
   3 独立 unit 雑音 Z_X/Z_Y/Z (sum も別個 unit noise Z で平滑化 → 𝒩(0,1) 前提が真)
   5-tuple iIndepFun は Measure.pi_eq + 座標射影 law で body 内 inline 供給
        ↓ two-time terminal entropyPower_add_ge_case1_of_regular_twotime
   de Bruijn group / endpoint group / h_stam_supply (inverse-Stam) / scale·rescale
        ↓ entropy_power_inequality_via_lift3 (measure-transport)
   base 上 EPI
```

honest precondition 16 本 (measurability / indep / a.c. / moment + (X/Y/sum)×(Fisher 有限 / `IsRegularDensityV2` / normalization / `IsBlachmanConvReady` / entropy 有限))。命名 `_of_density` は一般化されていないことを明示する honest 名。

**Phase B 真の analytic 壁 (再開時の核心)**: 完全一般形は一般 a.c. 密度に対し score-of-convolution Fisher monotonicity を genuine に解く必要 — Phase A が要求する `IsRegularDensityV2`/`IsBlachmanConvReady` は一般 a.c. 密度では出ない。これが density 枝の最深 gap。**Stam Step 2 re-scope candidate**: Rioul 2011 §II-C (score-conditional-mean identity + total variance decomposition) で ~100 行 density-level computation の見積りあり (従来 ~300 行 PR 級より小) → roadmap Ch.17 行参照。退化境界値 `differentialEntropy_dirac = 0` (`entropyPower (dirac)` は親 plan で旧値1→新値0 へ retype 移行中、設計は新定義側で)。

**Phase B feasibility verdict (L-PhB-stop 発動済)**: smoothing route は出発点で詰む (Gaussian 畳込みは裾を保存し有限分散/有限エントロピー precondition を剥がせない、循環)。truncate→smooth 二重近似 + entropy-power 弱収束 LSC は Mathlib 不在 → 別 moonshot 規模 (後継 = route β'、`epi-uncond-truncation-lsc-plan` で別途 closure 済)。

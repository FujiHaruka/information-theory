import InformationTheory.Shannon.EPI.Unconditional.Dispatch
import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit

/-!
# EPI 無条件化 — 完全無条件 dispatch (Phase 5 endgame)

`docs/shannon/epi-uncond-dispatch-endgame-plan.md` の Phase 1–3。既存の無条件 gateway 群
(method-Y、全て proof-done `@audit:ok`) を使い、`(hX hY : Measurable) (hXY : IndepFun X Y P)`
**のみ**を取る完全無条件 EPI dispatch `entropyPowerExt_add_ge_unconditional` を建立する。

既存 21-precondition dispatch (`EPIUncondDispatch.entropyPowerExt_add_ge_dispatch_skeleton`、
proof-done、consumer 0 leaf) は**改変せず残し**、gateway 経由の完全無条件版を本 file に別建て。

* 柱 A (Phase 1) — singular rewire: case 2 (X a.c. ∧ Y 特異) は `N(Y)=0` ゆえ RHS=`N(X)`、
  gateway 単調性 `entropyPowerExt_mono_add_unconditional` で `N(X+Y) ≥ N(X)` で closure。対称版も同型。
* 柱 B (Phase 2) — case-1 split: 両 a.c. を `h(X+Y)`/`h(X)`/`h(Y)` の ⊤/⊥/有限で by_cases split、
  各 sub-case を gateway 単調性 または bridge `differentialEntropyExt_integrable_of_finite` 経由で
  既存 genuine `entropyPowerExt_add_ge_finite_ac` (3 finite-entropy precondition) に落とす。
* 柱 C (Phase 3) — assembly: 4 枝 by_cases (X a.c. × Y a.c.) → 柱B/柱A/柱A対称/`entropyPowerExt_singular_add_ge`。

全 declaration は既存 proof-done gateway/bridge への delegation で own sorry 0 を目標
(新規 Mathlib 壁を作らない)。詰まるのは plumbing (order 補題 / EReal exp 展開 / `add_comm` reshape) のみ。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open InformationTheory.Shannon.EntropyPowerInequality
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **helper — `h = ⊥ ⟹ N = 0`** (a.c. だが負部発散で `h=⊥` の場合)。
`entropyPowerExt_singular` は `¬ a.c.` 専用で a.c. かつ `h=⊥` を覆わないため、`differentialEntropyExt`
の値が `⊥` であることだけから `entropyPowerExt = 0` を出す helper を別途立てる。
`EReal.exp_bot` + `EReal.mul_bot_of_pos` の 2 行 (`entropyPowerExt_singular` の証明末尾と同型)。

独立 honesty audit 2026-06-08 (fresh subagent, commit 34b8d37 → ok): 4-check 全 PASS。
(1) 非循環 — 結論 `N=0` は仮説 `h=⊥` と非同型、body は `entropyPowerExt=EReal.exp(2·h)` の genuine
2 行 rewrite (`:= h` でない)。(2) 非バンドル — 唯一の仮説 `h=⊥` は `differentialEntropyExt` の値で、
結論 (entropy power = 0) は body の EReal exp 計算が供給。(3) 非退化 — `exp(2·⊥)=exp(⊥)=0` は
EReal exp def の正しい値、vacuous/exfalso なし。(4) sufficiency — 含意 TRUE (`h=⊥⟹N=0` は def 直結)。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。@audit:ok -/
private theorem entropyPowerExt_eq_zero_of_diffEntExt_bot {μ : Measure ℝ}
    (h : differentialEntropyExt μ = ⊥) : entropyPowerExt μ = 0 := by
  unfold entropyPowerExt
  rw [h, EReal.mul_bot_of_pos (by norm_num), EReal.exp_bot]

/-- **柱 A (case 2) — X a.c. ∧ Y 特異**: `N(Y)=0` ゆえ RHS=`N(X)`、gateway 単調性で `N(X+Y) ≥ N(X)`。
仮説は `hX hY hXY hX_ac hY_sing` のみ (既存 dispatch の 8 integrability + 2 finite-entropy を全除去)。

独立 honesty audit 2026-06-08 (fresh subagent, commit 34b8d37 → ok): 4-check 全 PASS。
(1) 非循環 — 結論 `N(X+Y)≥N(X)+N(Y)` は仮説いずれとも非同型、body は `N(Y)=0` rewrite + gateway 単調。
(2) 非バンドル — `hX_ac` 絶対連続 / `hY_sing` 特異性 / `hX hY hXY` regularity、EPI 単調性 core は genuine
gateway `entropyPowerExt_mono_add_unconditional` (`@audit:ok`) の body 3 枝が供給 (仮説に encode せず)。
(3) 非退化 — `N(Y)=0` は特異測度のエントロピーパワーの真の値 (`entropyPowerExt_singular` genuine、sanity
gate `entropyPowerExt_dirac=0` 確認済)、退化定義悪用でない。(4) sufficiency (反例試行) — `hY_sing` を
落とすと N(Y)>0 が可能で `N(X+Y)≥N(X)` だけでは結論不成立、genuine に必要。under-hypothesized でない。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。@audit:ok -/
theorem entropyPowerExt_mixed_add_ge_uncond
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_sing : ¬ (P.map Y) ≪ volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  rw [entropyPowerExt_singular hY_sing, add_zero]
  exact entropyPowerExt_mono_add_unconditional X Y P hX hY hXY hX_ac

/-- **柱 A 対称 (case 2 対称) — Y a.c. ∧ X 特異**: `N(X)=0` ゆえ RHS=`N(Y)`、gateway 単調性
(W=Y, V=X) で `N(Y+X) ≥ N(Y)` を出し `add_comm` で `X+Y` に reshape。
仮説は `hX hY hXY hY_ac hX_sing` のみ。

独立 honesty audit 2026-06-08 (fresh subagent, commit 34b8d37 → ok): 4-check 全 PASS (#2 の mirror)。
(1) 非循環 — body は `add_comm` reshape + `N(X)=0` rewrite + gateway 単調 (W=Y,V=X、`hXY.symm`)。
(2) 非バンドル — `hY_ac`/`hX_sing`/regularity、EPI 単調性 core は gateway (`@audit:ok`) が供給。
(3) 非退化 — `N(X)=0` は特異測度の真の値 (sanity-gated)、退化悪用でない。(4) sufficiency — `hX_sing`
genuine に必要 (#2 と対称)。`add_comm` rewrite は genuine な measure 等式 (`congrArg`+`funext`)。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認)。@audit:ok -/
theorem entropyPowerExt_mixed_add_ge_symm_uncond
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hY_ac : (P.map Y) ≪ volume) (hX_sing : ¬ (P.map X) ≪ volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  have hcomm : P.map (fun ω => X ω + Y ω) = P.map (fun ω => Y ω + X ω) :=
    congrArg (P.map ·) (funext fun ω => add_comm _ _)
  rw [hcomm, entropyPowerExt_singular hX_sing, zero_add]
  exact entropyPowerExt_mono_add_unconditional Y X P hY hX hXY.symm hY_ac

/-- **柱 B (case 1) — 両 a.c.、finite-entropy 前提なし**。
`h(X+Y)`/`h(X)`/`h(Y)` の ⊤/⊥/有限で by_cases split。`N = EReal.exp(2·h)` ゆえ `h=⊤⟹N=⊤`、
`h=⊥⟹N=0`。⊤/⊥ 枝は gateway 単調性で RHS の一項を潰し、有限残枝は bridge
`differentialEntropyExt_integrable_of_finite` で 3 integrability を供給して既存 genuine
`entropyPowerExt_add_ge_finite_ac` に落とす。仮説は `hX hY hXY hX_ac hY_ac` のみ。

独立 honesty audit 2026-06-08 (fresh subagent, commit 34b8d37 → ok): 4-check 全 PASS。
(1) 非循環 — 6-way by_cases (h(X+Y)/h(X)/h(Y) の ⊤/⊥/有限)、各枝 genuine delegation で `:= h` でない。
⊤ 枝 = `entropyPowerExt_eq_top_of_diffEntExt_top` + gateway 単調 → `le_top`、⊥ 枝 = helper #1
(`entropyPowerExt_eq_zero_of_diffEntExt_bot`) + gateway 単調。`hWbot` 導出 (h(X)≠⊥ ∧ h(X)≤h(X+Y) ⟹
h(X+Y)≠⊥) は genuine 単調性 (exfalso 悪用でない)。(2) 非バンドル — `hX_ac`/`hY_ac` 絶対連続 regularity、
EPI 不等式 core は genuine `entropyPowerExt_add_ge_finite_ac` (`@audit:ok`、有限分散 smoothing / 無限分散
route T 両枝 sorryAx-free) が供給。bridge `differentialEntropyExt_integrable_of_finite` (`@audit:ok`) で
3 integrability を再構成 (仮説に encode せず)。(3) 非退化 — ⊤=`le_top`/⊥ 枝とも実値計算で genuine。
(4) sufficiency — 両 a.c. 仮説は case-1 regime に genuine 必要、finite_ac 呼出引数 verbatim 一致。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free 機械確認、transitive sorry 0)。@audit:ok -/
theorem entropyPowerExt_add_ge_case1_uncond
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  -- 1. h(X+Y) = ⊤ ⟹ N(X+Y) = ⊤ ≥ RHS。
  by_cases hWtop : differentialEntropyExt (P.map (fun ω => X ω + Y ω)) = ⊤
  · rw [entropyPowerExt_eq_top_of_diffEntExt_top hWtop]; exact le_top
  -- 2. h(X) = ⊤ ⟹ N(X) = ⊤、gateway 単調で N(X+Y) ≥ N(X) = ⊤ ⟹ N(X+Y) = ⊤。
  by_cases hXtop : differentialEntropyExt (P.map X) = ⊤
  · have hNX : entropyPowerExt (P.map X) = ⊤ := entropyPowerExt_eq_top_of_diffEntExt_top hXtop
    have hge : entropyPowerExt (P.map (fun ω => X ω + Y ω)) ≥ entropyPowerExt (P.map X) :=
      entropyPowerExt_mono_add_unconditional X Y P hX hY hXY hX_ac
    have hWval : entropyPowerExt (P.map (fun ω => X ω + Y ω)) = ⊤ :=
      top_le_iff.mp (hNX ▸ hge)
    rw [hWval]; exact le_top
  -- 3. h(Y) = ⊤ ⟹ 同上 (gateway 対称)。
  by_cases hYtop : differentialEntropyExt (P.map Y) = ⊤
  · have hcomm : P.map (fun ω => X ω + Y ω) = P.map (fun ω => Y ω + X ω) :=
      congrArg (P.map ·) (funext fun ω => add_comm _ _)
    have hNY : entropyPowerExt (P.map Y) = ⊤ := entropyPowerExt_eq_top_of_diffEntExt_top hYtop
    have hge : entropyPowerExt (P.map (fun ω => Y ω + X ω)) ≥ entropyPowerExt (P.map Y) :=
      entropyPowerExt_mono_add_unconditional Y X P hY hX hXY.symm hY_ac
    have hWval : entropyPowerExt (P.map (fun ω => X ω + Y ω)) = ⊤ := by
      rw [hcomm]; exact top_le_iff.mp (hNY ▸ hge)
    rw [hWval]; exact le_top
  -- 4. h(X) = ⊥ ⟹ N(X) = 0、RHS = N(Y)、gateway 対称で N(X+Y) ≥ N(Y)。
  by_cases hXbot : differentialEntropyExt (P.map X) = ⊥
  · have hcomm : P.map (fun ω => X ω + Y ω) = P.map (fun ω => Y ω + X ω) :=
      congrArg (P.map ·) (funext fun ω => add_comm _ _)
    rw [entropyPowerExt_eq_zero_of_diffEntExt_bot hXbot, zero_add, hcomm]
    exact entropyPowerExt_mono_add_unconditional Y X P hY hX hXY.symm hY_ac
  -- 5. h(Y) = ⊥ ⟹ N(Y) = 0、RHS = N(X)、gateway で N(X+Y) ≥ N(X)。
  by_cases hYbot : differentialEntropyExt (P.map Y) = ⊥
  · rw [entropyPowerExt_eq_zero_of_diffEntExt_bot hYbot, add_zero]
    exact entropyPowerExt_mono_add_unconditional X Y P hX hY hXY hX_ac
  -- 6. 残枝 (h(X)/h(Y)/h(X+Y) 全有限): bridge で 3 integrability 供給 → finite_ac 呼出。
  · -- h(X+Y) a.c. (両 a.c. + 独立 ⟹ convolution 保存)。
    have hW_ac : P.map (fun ω => X ω + Y ω) ≪ volume :=
      map_add_absolutelyContinuous X Y P hX hY hXY hX_ac
    -- h(X) ≤ h(X+Y) (gateway 単調)、h(X) ≠ ⊥ ゆえ h(X+Y) ≠ ⊥。
    have hmono : differentialEntropyExt (P.map X)
        ≤ differentialEntropyExt (P.map (fun ω => X ω + Y ω)) :=
      differentialEntropyExt_mono_add_unconditional X Y P hX hY hXY hX_ac
    have hWbot : differentialEntropyExt (P.map (fun ω => X ω + Y ω)) ≠ ⊥ := by
      intro hbot
      exact hXbot (le_bot_iff.mp (hbot ▸ hmono))
    -- bridge で 3 integrability 供給。
    have hX_ent := differentialEntropyExt_integrable_of_finite hX_ac hXtop hXbot
    have hY_ent := differentialEntropyExt_integrable_of_finite hY_ac hYtop hYbot
    have hW_ent := differentialEntropyExt_integrable_of_finite hW_ac hWtop hWbot
    exact entropyPowerExt_add_ge_finite_ac X Y P hX hY hXY hX_ac hY_ac hX_ent hY_ent hW_ent

/-- **柱 C (Phase 3) — 完全無条件 dispatch** (`hX hY hXY` のみ、precondition 21 → 0)。
4 枝 `by_cases (P.map X ≪ volume)` × `by_cases (P.map Y ≪ volume)`:
* 両 a.c. → 柱 B `entropyPowerExt_add_ge_case1_uncond`
* X a.c. ∧ Y 特異 → 柱 A `entropyPowerExt_mixed_add_ge_uncond`
* Y a.c. ∧ X 特異 → 柱 A 対称 `entropyPowerExt_mixed_add_ge_symm_uncond`
* 両特異 → `entropyPowerExt_singular_add_ge` (RHS=0、型自明)

真の無条件 EPI (ℝ≥0∞ 版)。`_unconditional` 命名は precondition 21→0 ゆえ name-laundering でない。

独立 honesty audit 2026-06-08 (fresh subagent, commit 34b8d37 → ok、moonshot headline 最重点):
4-check 全 PASS + name-laundering NOT laundering + case-3 非退化 を独立確認。
(1) 非循環 — 4 枝 by_cases ((P.map X≪vol)×(P.map Y≪vol))、各枝 proof-done 補題への genuine
delegation で `:= h` でない。(2) **非バンドル — 構造的に余地なし**: signature は `hX hY hXY`
(可測+独立) + instance `[IsProbabilityMeasure P]` のみ。`*Hypothesis` predicate も integrability/
finiteness/a.c. 仮説も無し ⇒ load-bearing bundling の余地が構造的に存在しない。
(3) **case-3 非退化** — 両特異枝 `entropyPowerExt_singular_add_ge` (RHS=0+0) は退化定義悪用でない:
特異測度の `differentialEntropyExt=⊥` ゆえ `entropyPowerExt=exp(2·⊥)=0` は **正しい値** (sanity gate
`entropyPowerExt_dirac=0` 確認済、旧 Real def の `exp 0=1` トラップは 2026-06-06 def-fix で除去)。
a.c. 判定は genuine Classical `by_cases` で「常時 false に倒して vacuous 達成」でない。
(4) sufficiency — 4 枝 exhaustive (clean compile 確認)、各枝 delegation 先と引数 verbatim 一致:
両 a.c.→柱B `entropyPowerExt_add_ge_case1_uncond` / X a.c.∧Y 特異→柱A `_mixed_add_ge_uncond` /
Y a.c.∧X 特異→柱A 対称 `_mixed_add_ge_symm_uncond` / 両特異→`entropyPowerExt_singular_add_ge`。
**name-laundering check — NOT laundering**: `_unconditional` = precondition 21→0 が genuine。
a.c./integrability/finiteness は型クラス/instance で密輸せず、body 内で `by_cases` + bridge
`differentialEntropyExt_integrable_of_finite` (`@audit:ok`) により内部再構成。`[IsProbabilityMeasure P]`
は正当な regularity instance (確率測度上の命題、密輸仮説でない)。全 delegation 先 (`mono_add_unconditional`/
`integrable_of_finite`/`add_ge_finite_ac`/`singular`/`singular_add_ge`、すべて既 `@audit:ok` 機械確認済)。
`#print axioms entropyPowerExt_add_ge_unconditional` = `[propext, Classical.choice, Quot.sound]`
(sorryAx-free 本監査機械再確認、`Classical.choice` は `by_cases (≪volume)` の Decidable 由来で許容)、
transitive sorry 0 = proof done。@audit:ok -/
@[entry_point]
theorem entropyPowerExt_add_ge_unconditional
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  by_cases hX_ac : (P.map X) ≪ volume
  · by_cases hY_ac : (P.map Y) ≪ volume
    · -- 両 a.c. → 柱 B (case 1)。
      exact entropyPowerExt_add_ge_case1_uncond X Y P hX hY hXY hX_ac hY_ac
    · -- X a.c. ∧ Y 特異 → 柱 A (case 2)。
      exact entropyPowerExt_mixed_add_ge_uncond X Y P hX hY hXY hX_ac hY_ac
  · by_cases hY_ac : (P.map Y) ≪ volume
    · -- Y a.c. ∧ X 特異 → 柱 A 対称 (case 2 対称)。
      exact entropyPowerExt_mixed_add_ge_symm_uncond X Y P hX hY hXY hY_ac hX_ac
    · -- 両特異 → case 3 (RHS=0)。
      exact entropyPowerExt_singular_add_ge X Y P hX_ac hY_ac

end InformationTheory.Shannon

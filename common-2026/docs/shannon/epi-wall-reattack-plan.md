# EPI 残り 2 壁 re-attack — gateway atom 起点の本気攻略 サブ計画

> **Parent**: [`epi-moonshot-plan.md`](epi-moonshot-plan.md) (Ch.17 一般 EPI)
> **関連 parent sub-plans**: [`epi-stam-discharge-plan.md`](epi-stam-discharge-plan.md) / [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md) / [`epi-stam-fisher-epi-integrated-sweep-plan.md`](epi-stam-fisher-epi-integrated-sweep-plan.md)
> **Inventory (Wave 1)**: [`epi-wall-reattack-inventory.md`](epi-wall-reattack-inventory.md)
> **Created**: 2026-05-30 (Wave 1 独立再評価 = proof-pivot-advisor + mathlib-inventory 収束結論を消費)

---

## ⚠ 最重要 — Phase 1 = go/no-go GATE

**本 plan の全体は Phase 1 (gateway atom `convDensity_add_differentiable`) の Done 判定に
gate される。** Phase 順序を取り違えて壁2 (Phase 4) を先に dispatch したり、Phase 1 を飛ばして
壁1 本体 (Phase 3) に着手すると **空回りする** (どちらも gateway が供給する density 微分可能性 +
score 表現を消費するため)。

- **Phase 1 GO** (gateway atom が type-check done で建つ) → Phase 2/3/4 へ進み 2 壁を直列 closure。
- **Phase 1 NO-GO** (`⋆ₗ` / convolution 密度の点ごと微分可能性が概念ごと組めない、または Gaussian
  tail dominated 充足が 1 セッション超過) → **真壁確定診断**として `@residual(wall:conv-score-smooth)` /
  `@residual(wall:debruijn-heat-eq)` の honest sorry 据置に戻し、診断を docstring 散文化して撤退。
  Phase 2 (cross-term orthogonality) のみ gateway 非依存なので独立に拾える。

go/no-go の決定的判定基準は §Phase 1 末尾「Done 条件 / go-no-go gate」参照。

## 進捗

- [x] Phase 0 — 在庫確定 + 壁 signature verbatim 照合 ✅
- [x] Phase 1 — **gateway atom `convDensity_add_differentiable` = GATE GO ✅** (genuine, 0 sorry, sorryAx-free, 独立監査 `@audit:ok`)
- [x] Phase 2 — cross-term orthogonality `score_cross_term_eq_zero` = genuine ✅ (0 sorry, `@audit:ok`)
- [ ] **Phase 3-pre — 🔴 BLOCKER: 3 述語 signature pivot (owner-task)** 📋 ← Phase 3 着手の前提、Wave 6 監査で判明
- [ ] Phase 3 — 壁1 本体 (条件付き Blachman → convex Fisher bound) 📋 (Phase 3-pre 完了後)
- [ ] Phase 4 — 壁2 (per-time de Bruijn + FTC 積分形) 📋

## ⚠ Phase 3-pre — 3 述語 signature pivot (Wave 6 監査で判明した真の blocker) 📋

**Phase 3 (壁1 本体) 着手で判明**: `stam_step2_density_wall` の真の blocker は Mathlib 解析壁ではなく
**消費先 predicate の signature defect (false-statement)**。Wave 6 独立監査が確定:

- `IsStamCauchySchwarzOptimal` (`EPIStamInequalityBody.lean:245`) が密度 `fX fY fXY : ℝ→ℝ` を
  **無制約に全称量化** + `fisherInfoOfMeasureV2` (`FisherInfoV2DeBruijn.lean:77`) が measure 引数
  `_μ` を無視 → `fXY = fX⋆fY` (畳み込み) 制約が欠落し命題が **FALSE** (反例: fX=fY=𝒩(0,1)/J=1,
  fXY=𝒩(0,1/100)/J_sum=100; `100 ≤ 1/2` 偽、closed-form `fisherInfoOfDensity(𝒩 m v).toReal=1/v` で検算)。
- 同型 defect が **計 3 述語**: `IsStamCauchySchwarzOptimal` + `IsStamCondExpCSHyp`
  (`EPIStamStep12Body.lean:200`) + `IsStamInequalityResidual` (`EntropyPowerInequality.lean:190`)。
  単独 pivot では残り 2 つが silent に残るため **3 述語一括設計が必須**。
- タグ是正済 (Wave 6): `@residual(wall:stam-step2-density)` → `@audit:defect(false-statement)
  @audit:closed-by-successor(epi-wall-reattack-plan)`。genuine 詐称 0 (FALSE 述語は sorry 経由で
  honest 隔離、headline `entropy_power_inequality` は本述語非経由)。

### pivot 設計 (owner-task)

3 述語の universal 量化部に **畳み込み制約 + 密度 regularity** を注入:
- `fXY =ᵐ[volume] convDensityAdd fX fY` (Phase 1 gateway の `convDensityAdd` を直接参照)。
- `fX`/`fY`/`fXY` が `P.map X`/`P.map Y`/`P.map (X+Y)` の density であること (`fisherInfoOfMeasureV2`
  が measure を無視するので、別途 density 同定 hyp が必要 — `fisherInfoOfMeasureV2_eq_of_pdf_ae_eq`
  系で接続)。

### ripple 先 (signature 変更が波及)

`entropy_power_inequality_via_body` / `stam_inequality_via_predicate_optimal` /
`stam_convex_fisher_bound_gaussian` + transitive consumer 3 件 (`isStamInequalityHyp_via_step3` /
`isStamInequalityHyp_of_primitives` / `entropy_power_inequality_via_stamDeBruijn`)。

### Done 条件 / 撤退ライン

- **Done**: 3 述語が畳み込み制約付き signature に pivot され、`lake env lean` 0 errors
  (ripple 先全て type-check done)。pivot 後 `stam_step2_density_wall` が **genuine に provable な形**
  になる (FALSE でなくなる) ことを反例消失で確認。
- 撤退ライン **L-EPIW-3pre-α**: ripple 影響範囲が予想超 (consumer が cross-file で多数) →
  pivot を段階化 (1 述語ずつ + adapter wrapper)、または当該 turn は `@audit:defect` タグ据置のまま報告。

pivot 完了 **後** に Phase 3 (Blachman attach、既存 gateway を consumer として消費) が着手可能になる。
proof-log: yes。

## Position / Motivation / Scope

### 対象 2 壁 (Wave 1 確定)

- **壁1 `wall:stam-step2-density`** — `Common2026/Shannon/EPIStamInequalityBody.lean:283`
  `stam_step2_density_wall`。独立 `X, Y` の条件付き Cauchy-Schwarz から convex Fisher bound
  `J(Z) ≤ J(X)·J(Y)/(J(X)+J(Y))` (`IsStamCauchySchwarzOptimal`)。regularity (measurability /
  independence / probability measure) は honest hyp として既に保持、analytic core が `sorry`。
- **壁2 `wall:debruijn-integration`** — `Common2026/Shannon/FisherInfoV2DeBruijn.lean:245`
  `debruijnIdentityV2_holds` (per-time 微分形) + `:310` `debruijnIntegrationIdentity_holds`
  (積分形)。de Bruijn 恒等式 `(d/dt) h(X+√t·Z) = (1/2)·J(X+√t·Z)`。

### 共通根 (Wave 1 決定 1)

両壁は同一の foundational apparatus に帰着する: **独立和の畳み込み密度 `p_Z = p_X ⋆ p_Y` を
点ごと微分可能にし、その score `logDeriv p_Z` を condExp `E[s_X | X+Y=z]` (Blachman 恒等式) /
Fisher info に接続する apparatus**。

- 壁1 は `s_Z(z) = E[s_X(X) | X+Y=z]` (Blachman) で convex Fisher bound を出す。
- 壁2 は per-time `p_t = p_X ⋆ heatKernel_t` の `logDeriv` を Fisher info に紐付け、heat eq
  IBP で `(d/dt)h = (1/2)J` を出す。

両方とも「畳み込み密度の点ごと微分可能性 + その logDeriv 表現」を gateway atom として消費する。

### scope-out からの差し戻し条件 (「本気で攻める」の意味)

過去 inventory は 2 壁を「Fisher/score/density 計算 Mathlib 全不在」で scope-out した。本 plan は
gateway atom `convDensity_add_differentiable` を起点に **直列攻略を試行**し、以下で分岐する:

- **gateway が建てば差し戻し**: scope-out を撤回し、Phase 2/3/4 で 2 壁を genuine closure に向かわせる。
- **`⋆ₗ` 微分可能性で詰まれば真壁確定**: scope-out 判断を確定として honest sorry 据置に戻す。
  この場合「なぜ tractable でなかったか」の診断 (どの dominated 仮定が Gaussian tail self-build で
  詰まったか) を当該 wall docstring に散文で残し、後続が同じ探索を繰り返さないようにする。

### Scope (新規 + 既存拡張)

| 対象 file | 役割 | Phase |
|---|---|---|
| `Common2026/Shannon/EPIConvDensity.lean` (新規) | gateway atom `convDensity_add_differentiable` + logDeriv 表現 | Phase 1 |
| `Common2026/Shannon/EPIScoreCrossTermOrth.lean` (新規) | cross-term orthogonality (inventory §着手 skeleton) | Phase 2 |
| `Common2026/Shannon/EPIStamInequalityBody.lean` (既存拡張) | `stam_step2_density_wall:283` 本体充足 | Phase 3 |
| `Common2026/Shannon/FisherInfoV2DeBruijn.lean` (既存拡張) | per-time `:245` + 積分形 `:310` 充足 + `_hX/_hZ/_hXZ` signature 復元 | Phase 4 |

`@residual` slug: gateway 失敗時は既存 wall slug (`wall:conv-score-smooth` / `wall:stam-blachman` /
`wall:debruijn-heat-eq`、register 既登録) に据置く。新規 plan slug は本 file stem
`epi-wall-reattack-plan` を `@residual(plan:epi-wall-reattack-plan)` で参照可。

## ゴール / Approach

**解の全体形**: 共通 density apparatus を gateway atom で建て、壁1 (条件付き Blachman → convex
Fisher bound) を先に閉じ、壁2 (per-time de Bruijn density witness → FTC 積分形は Gaussian テンプレ
一般化) を後に閉じる。**直列** shape (壁1 → 壁2、逆順不可)。

```
                  ┌──────────────────────────────────────────────────┐
   Phase 1 GATE   │ convDensity_add_differentiable                    │
   (DECISIVE)     │   p_Z(z) = ∫ p_X(x)·p_Y(z-x) dx を点ごと微分可能 │
                  │   + logDeriv p_Z 表現 (起点: ParametricIntegral   │
                  │     hasDerivAt_integral_of_dominated_loc...)      │
                  └───────────────┬──────────────────┬───────────────┘
                                  │                  │
              ┌───────────────────┘                  └───────────────────┐
              ▼ (density witness +                          ▼ (per-time density
                logDeriv → score)                              witness p_t)
   ┌──────────────────────────┐                   ┌──────────────────────────────┐
   │ 壁1 (Phase 3)            │                   │ 壁2 (Phase 4)                │
   │ 条件付き Blachman        │                   │ per-time de Bruijn           │
   │   s_Z = E[s_X|X+Y=z]     │                   │   (d/dt)h = (1/2)J            │
   │ + ConvexOn.map_condExp_le│                   │   ← heat eq IBP (真壁可能性高)│
   │ + integral_condExp       │                   │ + FTC 積分形                 │
   │ + cross-term (Phase 2)   │ ◀── 直列依存 ──   │   ← bounded_T_ftc_gaussian   │
   │ ⇒ convex Fisher bound    │     (壁2 の per-     │     一般化 (~60-100行)      │
   └──────────────────────────┘     time witness は  └──────────────────────────────┘
                                     壁1 apparatus を
   ┌──────────────────────────┐     消費)
   │ cross-term orth (Phase 2)│
   │   ∫ (s_X∘X)(s_Y∘Y)=0     │  ← gateway 非依存、Phase 1 と並行着手可
   │   condExp_indep_eq +     │
   │   IndepFun.integral_mul  │
   └──────────────────────────┘
```

**各壁が共通 apparatus のどこを消費するか**:

- 壁1 (Phase 3) = gateway の `logDeriv p_Z` 表現 + Phase 2 の cross-term + Mathlib 既存
  `ConvexOn.map_condExp_le` (条件付き Jensen) + `integral_condExp` (total expectation)。
- 壁2 (Phase 4) = gateway の per-time 特殊化 (`p_t = p_X ⋆ heatKernel_t`) の density witness +
  heat eq IBP (`integral_mul_deriv_eq_deriv_mul_of_integrable`、inventory §5) + Gaussian テンプレ
  `bounded_T_ftc_gaussian` (`EPIL3Integration.lean:937-985`、`@audit:ok`) の一般化。

**Wave 1 が確定した tractability の格下げ/格上げ** (Approach に効く):

- cross-term orthogonality は **真壁ではない** — `condExp_indep_eq`
  (`ConditionalExpectation.lean:42`) + `IndepFun.integral_mul_eq_mul_integral`
  (`Integration.lean:247`) + 既存 `integral_logDeriv_density_eq_zero` (`FisherInfoV2.lean:155`)
  で ~20-40 行。過去 inventory の `Found 0` は loogle bare-identifier query の false-negative。
- FTC 積分形は **Gaussian テンプレ同型が既に存在** — per-time de Bruijn さえ建てば ~60-100 行。
- genuine に不在で self-build 必須: (i) `⋆ₗ` 微分可能性 (`HasCompactSupport.*` 系 6 件は compact
  support 要求で Gaussian heat kernel 不適合)、(ii) heat eq density の IBP (`Mathlib.Analysis.PDE.*`
  不在)、(iii) 条件付き Blachman score 表現 (`condExp ∧ IndepFun` 同時 = loogle Found 0)。

**段階的 ship**: Phase 2 は gateway 非依存で単体 genuine 完成可 (atomic に ship)。Phase 1/3/4 は
gateway gate に従属、Phase 1 NO-GO 時は Phase 2 のみ回収して残りは sorry 据置のまま撤退。

## Phase 0 — 在庫確定 + 壁 signature verbatim 照合 📋

- [ ] Wave 1 inventory (`epi-wall-reattack-inventory.md`) の apparatus 1-10 テーブルを SoT として確認。
- [ ] gateway 起点 `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
      (`Mathlib/.../ParametricIntegral.lean:289`) の完全 signature を verbatim 照合
      (`[...]` type-class prereq + dominated 仮定の引数型を inventory に未収録なら追記依頼)。
- [ ] 壁 declaration の現 signature verbatim 確認 (済、本 plan 起草時):
      `stam_step2_density_wall:283` (regularity hyp `hX hY hXY` 保持済) /
      `debruijnIdentityV2_holds:245` (`X Z` + `IsRegularDeBruijnHypV2`、`_hX/_hZ/_hXZ` は **削除済**、
      forward-looking note `:234` 参照) / `debruijnIntegrationIdentity_holds:310` (存在形 `fPath`)。
- [ ] Gaussian テンプレ `bounded_T_ftc_gaussian` (`EPIL3Integration.lean:937-985`、`@audit:ok`) の
      結論 shape を verbatim 確認 (Phase 4 の一般化対象、shape contract を pin)。

proof-log: no (照合のみ)。

**Done 条件**: gateway 起点 lemma の dominated 仮定が inventory に verbatim 記録されている +
4 壁 declaration の現 signature を照合済。

## Phase 1 — gateway atom `convDensity_add_differentiable` (DECISIVE GATE) 📋

**この Phase の Done 判定が plan 全体の go/no-go gate。**

### 目標

独立 `X, Y` の和の pdf `p_Z(z) = ∫ x, p_X(x) · p_Y(z-x) ∂volume` が **点ごと微分可能** +
その `logDeriv p_Z` を condExp 接続可能な形で表現する gateway atom を建てる。両壁の唯一の共通
foundational helper。

### skeleton (sub-lemma を `:= by sorry` で列挙)

```lean
-- Common2026/Shannon/EPIConvDensity.lean (新規)
namespace InformationTheory.Shannon.EPIConvDensity

/-- 畳み込み密度の積分形 (sum density = ∫ p_X · p_Y(·-x))。Mathlib-shape-driven:
    結論を Bochner `∫` 形で述べ、ParametricIntegral lemma の結論形に合わせる。 -/
def convDensityAdd (pX pY : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ x, pX x * pY (z - x) ∂volume

/-- sub-1: 被積分関数の z 偏微分の dominated bound (Gaussian tail) — regularity hyp 群で pin。 -/
theorem convDensityAdd_dominated_deriv ... : ... := by sorry  -- @residual(wall:conv-score-smooth)

/-- sub-2: 点ごと HasDerivAt (起点: hasDerivAt_integral_of_dominated_loc_of_deriv_le)。 -/
theorem convDensityAdd_hasDerivAt ... : HasDerivAt (convDensityAdd pX pY) ... z := by
  sorry  -- @residual(wall:conv-score-smooth)

/-- sub-3: logDeriv 表現 (score of convolution の出発点、Blachman/Fisher 接続先)。 -/
theorem convDensityAdd_logDeriv ... : logDeriv (convDensityAdd pX pY) z = ... := by
  sorry  -- @residual(wall:conv-score-smooth)

/-- gateway atom: differentiable + logDeriv をまとめた公開 API。 -/
theorem convDensity_add_differentiable ... : ... := by sorry  -- @residual(...)
end ...
```

### dominated 仮定の pin 方法 (load-bearing bundling 禁止に注意)

`hasDerivAt_integral_of_dominated_loc_of_deriv_le` 適用には「z 近傍で被積分関数の z 偏微分が
可積分関数で上から押さえられる」dominated 仮定が要る。これを **regularity hyp として引数に pin**
する (Gaussian / 重テールでない密度クラスの precondition、honest hyp)。

- ✅ OK (regularity precondition): `pX pY` が Gaussian tail bound を満たす (`∃ C, |∂_z (pX x · pY (z-x))| ≤ g x ∧ Integrable g`)、`Measurable` / `Integrable pX` / `Integrable pY`。
- ❌ 禁止 (load-bearing): 「`convDensityAdd` が微分可能である」を `Is...Hyp` predicate として
  仮定に取って body を機械展開だけにする。これは結論の核を仮説に bundle する honesty defect
  (CLAUDE.md「検証の誠実性」)。詰まったら gateway atom body を `sorry` + `@residual` で残す。

### 撤退ライン

| slug | 内容 | 撤退口 |
|---|---|---|
| **L-EPIW-1-α** | Gaussian tail dominated 充足の自前構築 (`convDensityAdd_dominated_deriv`) が 1 セッション超過 | sub-lemma body `sorry` + `@residual(wall:conv-score-smooth)` 据置、Phase 全体 NO-GO 判定 |
| **L-EPIW-1-β** | `⋆ₗ` / convolution 密度の点ごと微分可能性が概念ごと組めない (`HasCompactSupport` 不適合の回避 = truncation + dominated convergence が PR 級) | gateway atom body `sorry` + `@residual(wall:conv-score-smooth)`、scope-out 確定診断を docstring 散文化、Phase 1 NO-GO |

### Done 条件 / go-no-go gate (★ plan 全体の判定点)

- **GO** = `convDensity_add_differentiable` (gateway atom) が **type-check done** で建つ
  (sub-1〜sub-3 のうち core の微分可能性 + logDeriv 表現が genuine、残るは regularity-only の
  dominated 仮定 pin のみ)。→ Phase 2/3/4 へ進む。
- **NO-GO** = L-EPIW-1-β 発火 (convolution 密度の点ごと微分可能性が truncation self-build で
  1 セッション超過 or 概念ごと組めない)。→ scope-out 確定、Phase 2 のみ独立回収、残り sorry 据置。

判定の決め手は **sub-2 `convDensityAdd_hasDerivAt` が genuine に閉じるか**。ここが
`HasCompactSupport` 不適合の壁 (inventory §3 ★) を truncation で迂回できるかの一点。dominated
仮定 (sub-1) は regularity pin で吸収できるので gate ではない。sub-2 が真壁なら NO-GO。

概算規模: 80-200 行 (sub-2 の truncation + dominated convergence が支配項)。

proof-log: yes。

## Phase 2 — cross-term orthogonality (self-buildable 確定部、gateway 非依存) 📋

honesty 補正部。**Phase 1 と独立に着手可能** (gateway 不要)。Wave 1 が「真壁ではない」と確定した部品。

### skeleton (inventory §着手 skeleton をそのまま使用)

```lean
-- Common2026/Shannon/EPIScoreCrossTermOrth.lean (新規)
/-- Score cross-term orthogonality (full-expectation version).
    独立 X,Y、mean-zero score。NOT a discharge of Blachman identity. -/
theorem score_cross_term_eq_zero
    {X Y : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {sX sY : ℝ → ℝ}
    (hXY : IndepFun X Y P)
    (hsX : AEStronglyMeasurable (fun ω => sX (X ω)) P)
    (hsY : AEStronglyMeasurable (fun ω => sY (Y ω)) P)
    (hmeanX : ∫ ω, sX (X ω) ∂P = 0) :
    ∫ ω, sX (X ω) * sY (Y ω) ∂P = 0 := by
  -- IndepFun.comp hXY → IndepFun.integral_fun_mul_eq_mul_integral → rw [hmeanX]; ring
  sorry  -- genuine に閉じる想定 (gateway 非依存)、詰まれば @residual(plan:epi-wall-reattack-plan)
```

### 組み方 (Mathlib 既存物)

1. `IndepFun X Y P` → `IndepFun (sX∘X) (sY∘Y) P` を `IndepFun.comp` で出す (plumbing 主)。
2. `IndepFun.integral_mul_eq_mul_integral` (`Integration.lean:247`、または姉妹
   `IndepFun.integral_fun_mul_eq_mul_integral:253`) で `∫ (sX∘X)(sY∘Y) = E[sX∘X]·E[sY∘Y]`。
3. `hmeanX : E[sX∘X] = 0` (repo `integral_logDeriv_density_eq_zero` (`FisherInfoV2.lean:155`) /
   `FisherInfoV2.n` / `n_pdf_eq_zero_gaussian` から供給) で `= 0`。

### false-negative 訂正 (同 commit)

過去 inventory (`epi-stam-condexp-score-discharge-mathlib-inventory.md:149`) の
`unknown identifier 'condExp_indep'` false-negative claim を docstring / inventory で訂正する
(`condExp_indep_eq` は `ConditionalExpectation.lean:42` に **実在**、loogle bare-identifier query の
失敗だった)。Wave 1 inventory §2 が SoT。

### Done 条件 / 撤退ライン

- **Done**: `score_cross_term_eq_zero` が 0 sorry / 0 residual (genuine 完成、独立 audit pass → `@audit:ok`)。
- 撤退ライン **L-EPIW-2-α**: `IndepFun.comp` の score 合成 measurability で予想外に詰まる場合のみ
  `sorry` + `@residual(plan:epi-wall-reattack-plan)`。確率低 (部品揃い確定)。

概算規模: 20-40 行。proof-log: yes。

## Phase 3 — 壁1 本体 (条件付き Blachman → convex Fisher bound) 📋

**Phase 1 GO + Phase 2 Done を前提**。`stam_step2_density_wall` (`EPIStamInequalityBody.lean:283`)
の `sorry` body を充足。

### 組み方

1. gateway (Phase 1) の `logDeriv (convDensityAdd pX pY)` 表現から条件付き score 表現
   `s_Z(z) = E[s_X(X) | X+Y=z]` (Blachman 恒等式) を導く。← ここが genuine に不在の核
   (`condExp ∧ IndepFun` 同時補題 = loogle Found 0)、disintegration 経由の self-build。
2. `ConvexOn.map_condExp_le` (条件付き Jensen、Mathlib 既存) で
   `s_Z(z)² ≤ E[(λ s_X + (1-λ) s_Y)² | X+Y=z]`。
3. `integral_condExp` (total expectation、Mathlib 既存) + Phase 2 cross-term で積分して
   `J(Z) ≤ λ²·J(X) + (1-λ)²·J(Y)`。
4. λ 最適化 (`λ = J(Y)/(J(X)+J(Y))`) で `J(Z) ≤ J(X)·J(Y)/(J(X)+J(Y))` =
   `IsStamCauchySchwarzOptimal` の結論。

### 撤退ライン

| slug | 内容 | 撤退口 |
|---|---|---|
| **L-EPIW-3-α** | Blachman 条件付き score 表現 (step 1) の disintegration self-build が PR 級 | `stam_step2_density_wall` body `sorry` + `@residual(wall:stam-blachman)` 据置 (regularity hyp は維持、honesty defect 化させない) |
| **L-EPIW-3-β** | λ 最適化の algebraic transform が `linarith` 吸収不可で >50 行 | step 4 のみ `sorry` + `@residual(plan:epi-wall-reattack-plan)`、step 1-3 は genuine 部分 ship |

**honesty 規律**: Blachman identity を `Is...Hyp` predicate に bundle して `:= h` 機械展開で
抜くのは禁止 (tier 5 load-bearing)。詰まれば必ず `sorry` + `@residual(wall:stam-blachman)`。

概算規模: 100-250 行 (step 1 Blachman 表現が支配項、L-EPIW-3-α 発火確率高)。proof-log: yes。

## Phase 4 — 壁2 (per-time de Bruijn + FTC 積分形) 📋

**Phase 1 GO を前提** (per-time density witness を消費)。`debruijnIdentityV2_holds`
(`FisherInfoV2DeBruijn.lean:245`) + `debruijnIntegrationIdentity_holds` (`:310`) の充足。

### 前提整備 — `_hX/_hZ/_hXZ` signature 復元 (forward-looking note `:234` の option a)

`debruijnIdentityV2_holds` は Phase 2.B で `Measurable X` / `Measurable Z` / `IndepFun X Z P` を
signature から syntactically 削除済 (`:234` forward-looking note 参照)。これらは heat eq IBP の
wall content に **semantic に必要な regularity hyp**。Phase 4 着手時の前提整備として:

- [ ] **option a 採用** (note 推奨、load-bearing bundling 観点): `_hX` / `_hZ` / `_hXZ` を
      underscore-prefixed args として signature に復元 + caller `csiszarGap1Source_hasDerivAt`
      ripple。option b (`IsRegularDeBruijnHypV2` に field bundle) は predicate に regularity を
      抱えさせる方向なので不採用。

### 組み方

1. **per-time 微分形** (`:245`): gateway (Phase 1) を `p_t = p_X ⋆ heatKernel_t` に特殊化した
   density witness で `logDeriv p_t` を Fisher info に紐付け、heat eq `∂_t p_t = (1/2)∂_xx p_t` +
   IBP (`integral_mul_deriv_eq_deriv_mul_of_integrable`、inventory §5) で
   `(d/dt)h = (1/2)·J`。← heat eq IBP が **真壁可能性高** (Mathlib.Analysis.PDE.* 不在)。
2. **FTC 積分形** (`:310`): per-time `HasDerivAt` を FTC で積分。Gaussian テンプレ
   `bounded_T_ftc_gaussian` (`EPIL3Integration.lean:937-985`、`@audit:ok`、同型完全閉) を
   一般 `X` に一般化。per-time (step 1) が建てば ~60-100 行。

### 撤退ライン

| slug | 内容 | 撤退口 |
|---|---|---|
| **L-EPIW-4-α** | heat eq density の IBP (step 1) が Mathlib PDE 不在で self-build PR 級 | `debruijnIdentityV2_holds` body `sorry` + `@residual(wall:debruijn-heat-eq)` 据置 (regularity hyp `_hX/_hZ/_hXZ` 復元済で維持) |
| **L-EPIW-4-β** | FTC 積分形 (step 2) の一般 `X` 積分可能性が Gaussian テンプレ一般化で carry されず | `debruijnIntegrationIdentity_holds` body `sorry` + `@residual(wall:debruijn-integration)` 据置、per-time (step 1) が建てば step 1 のみ genuine ship |

**honesty 規律**: heat eq / IBP を predicate に bundle 禁止。per-time が真壁なら honest sorry 据置。

概算規模: per-time (step 1) 100-200 行 (heat eq IBP self-build、L-EPIW-4-α 発火確率高) +
FTC 積分形 (step 2) 60-100 行 (テンプレ一般化、step 1 後)。proof-log: yes。

## 全 Phase 通じた honesty 規律

- 詰まれば **`sorry` + `@residual(<class>:<slug>)`** で抜く (tier 2、唯一の正規撤退口)。
- **禁止** (tier 5、CLAUDE.md「検証の誠実性」): `*Hypothesis` / `Is...Hyp` predicate に証明の核を
  bundle / `Prop := True` slot / 仮説型≡結論の `:= h` 循環 / 退化定義悪用 (`Y:=0` で trivially 成立)。
- regularity hyp (measurability / independence / `IsProbabilityMeasure` / Gaussian tail dominated)
  は **precondition なので引数保持 OK** (load-bearing ではない)。
- 新規 `sorry` + `@residual` 導入 commit が出たら orchestrator が独立 honesty audit subagent を起動
  (CLAUDE.md「Independent honesty audit」)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正時。append-only。

1. **2026-05-30 起草 (Wave 1 結論消費)**: proof-pivot-advisor + mathlib-inventory が独立収束した
   4 確定事項を plan に固定。
   - **両壁共通根**: 壁1 (stam-step2-density) / 壁2 (debruijn-integration) は同一 apparatus
     (独立和畳み込み密度の点ごと微分可能性 + score logDeriv 表現) に帰着。
   - **Phase 直列順 (壁1 → 壁2)**: 壁2 の per-time density witness は壁1 apparatus を消費するため
     逆順不可。並列は壁2 空回り。Phase 1 (gateway) が両壁の共通従属点。
   - **gateway atom = 決定的判定**: `convDensity_add_differentiable` が建つか `⋆ₗ` 微分可能性で
     詰まるかが tractable/真壁の go/no-go gate (sub-2 `convDensityAdd_hasDerivAt` が判定の決め手、
     `HasCompactSupport` 不適合を truncation 迂回できるか)。Phase 1 NO-GO なら scope-out 確定。
   - **cross-term false-negative 補正**: 過去 inventory が cross-term orthogonality を `Found 0` で
     壁認定していたのは loogle bare-identifier query の失敗。`condExp_indep_eq`
     (`ConditionalExpectation.lean:42`) + `IndepFun.integral_mul_eq_mul_integral`
     (`Integration.lean:247`) + `integral_logDeriv_density_eq_zero` (`FisherInfoV2.lean:155`) で
     ~20-40 行 self-buildable。Phase 2 として gateway 非依存に分離、同 commit で inventory 訂正。
   - 起草時 verbatim 確認: `stam_step2_density_wall:283` (regularity hyp 保持済) /
     `debruijnIdentityV2_holds:245` (`_hX/_hZ/_hXZ` 削除済 + forward-looking note `:234`) /
     `debruijnIntegrationIdentity_holds:310` (存在形 fPath)。Gaussian テンプレ
     `bounded_T_ftc_gaussian` (`EPIL3Integration.lean:937-985` `@audit:ok`) の存在は Wave 1 結論で
     確認 (Phase 4 step 2 の一般化対象)。

# EPI: Csiszár 1-source gap の log-ratio 再定義 サブ計画

> **Parent**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §Phase A-close G1
> **Successor of (defect closure)**: `csiszarGap1Source_deriv_le_zero`
> (`EPIStamToBridge.lean:682`, `@audit:defect(false-statement)
> @audit:closed-by-successor(epi-csiszar-ratio-reframe-plan)`)

<!--
このファイルの slug (`epi-csiszar-ratio-reframe-plan`) は当該 defect 行の
`@audit:closed-by-successor(...)` および新規 `@residual(plan:...)` の slug と
一致させてある。rename する場合はコード側タグも同時に書換えること。
-->

## 進捗

- [ ] M0 在庫調査 (`Real.log` / `Real.exp` 単調性 + 商微分 + weighted Stam algebra の API 照合) 📋
- [x] Phase R-1 — gap の log-ratio 再定義 (`csiszarLogRatioGap` 新 def) ✅ **genuine, proof-done** (`EPIL3Integration.lean:~1353`、`csiszarLogRatioGap_at_zero` `:1363` genuine)
- [x] Phase R-2 — ratio derivative lemma 再述 (chain rule → `r'(t)` form) ✅ **genuine, `@audit:ok`** (`EPIStamToBridge.lean:681`、独立 `#print axioms` で sorryAx-free)
- [x] Phase R-3 — genuine `r'(t) ≤ 0` 🚧 **type-check done (1 sorry)** (`EPIStamToBridge.lean:839`、arith core 配線 + 5 正値性 genuine、sufficiency 監査 PASS。残 sorry = `h_plain_stam` 抽出 `:892` のみ、`@residual(plan:epi-csiszar-ratio-reframe-plan)`)
- [x] ~~**Phase R-3′ — density-identification bridge**~~ ❌ **撤退済 (2026-06-01 Wave 3、L-Ratio-3′-α 発火)** — bridge 案 infeasible 判明。M0′ verbatim 照合でルート A・B 両 infeasible 確定 (実装着手前)。詳細 → §Phase R-3′
- [ ] **Phase R-3″ — `IsStamInequalityHyp` 結論形 pivot (predicate reshape)** 🎯 **NEXT** — R-3 残 sorry `h_plain_stam` の真の closure 路。bridge 構築ではなく predicate の witness ∀-量化結論形を measure-level 直接形に書換える def-pivot。**別 sub-plan へ委譲** (slug 案 `epi-stam-predicate-reshape-plan`)。当該 predicate を参照する全 producer/consumer の blast radius 精査が要る 📋
- [ ] Phase R-4 — endpoint `r(1) = 0` (Gaussian saturation) + `r(0) ≥ 0 ⟺ EPI` の橋渡し 📋
- [ ] Phase R-5 — `AntitoneOn` lift + 旧 difference-gap chain の再配線 (blast-radius 消化) 📋
- [ ] Phase R-6 — auditor doctrine に「sufficiency (hyp ⊢ concl)」check 追加の提案 (docs-only) 📋

## ゴール / Approach

**ゴール**: `csiszarGap1Source_deriv_le_zero` (現 `@audit:defect(false-statement)`) が証明しようと
していた「path 微分 ≤ 0 → endpoint 経由 EPI」を、**偽の difference-gap ではなく genuine な
log-ratio gap** で再構築し、最終的に headline `stamToEPIBridge_holds` に至る monotonicity
チェーンを honest に閉じる。

### なぜ difference 形が偽で ratio 形が genuine か (orchestrator + proof-pivot-advisor 確認済)

`csiszarGap1Source X Y Z_X Z_Y P t` (`EPIL3Integration.lean:1335`) は **差分**
`g(t) = N_sum − N_X − N_Y`、ここで `N_i = entropyPower (P.map path_i)`、
`path_sum = X+Y+√t·(Z_X+Z_Y)`, `path_X = X+√t·Z_X`, `path_Y = Y+√t·Z_Y`。

chain rule (genuine、`csiszarGap1Source_hasDerivAt` `:474` に既存):
`N = exp(2h)`、de Bruijn `h'=(1/2)J` より `d/dt N_i = N_i · J_i`。よって差分微分は
`g'(t) = N_sum·J_sum − N_X·J_X − N_Y·J_Y`。

- **difference 形は FALSE**: `N_sum·J_sum ≤ N_X·J_X + N_Y·J_Y` は plain harmonic Stam
  `1/J_sum ≥ 1/J_X + 1/J_Y` から従わない (`N_i` が無制約)。反例: `N_sum` 巨大 / `N_X,N_Y` 微小で
  全 hyp が成り立つのに結論が破れる。`g'≤0` は閉じられない (closure 不能)。
- **ratio 形は genuine**: `r(t) = log N_sum − log(N_X + N_Y)` とおくと
  `r'(t) = J_sum − (N_X·J_X + N_Y·J_Y)/(N_X+N_Y)`。`r'≤0` ⟺
  `J_sum·(N_X+N_Y) ≤ N_X·J_X + N_Y·J_Y`。重み `α = N_X/(N_X+N_Y)`, `β = N_Y/(N_X+N_Y)`
  (`α+β=1`, `α,β∈[0,1]`)。harmonic Stam `J_sum ≤ J_X·J_Y/(J_X+J_Y) = min_λ(λ²J_X+(1−λ)²J_Y)`
  より λ=α 特化で `J_sum ≤ α²J_X + β²J_Y`。`α²≤α`, `β²≤β` より
  `α²J_X+β²J_Y ≤ αJ_X+βJ_Y = (N_X·J_X+N_Y·J_Y)/(N_X+N_Y)`。**純 algebra、Mathlib 壁なし、
  isoperimetric 不要**。

### EPI 復元が difference 版と equivalent であること

`r(0) ≥ 0 ⟺ N_sum(0) ≥ N_X(0)+N_Y(0)` (`log` 単調) ⟺
`entropyPower(X+Y) ≥ entropyPower(X)+entropyPower(Y)` = EPI。endpoint `r(1) = log 1 = 0`
(Gaussian saturation)。よって `r'≤0` on `[0,1]` + `r(1)=0` ⇒ `r(0)≥0` ⇒ EPI。
**skeleton は difference 版と同型**、しかし monotonicity lemma だけが TRUE になる。

### 全体 shape

```
M0 在庫 ──▶ R-1 csiszarLogRatioGap 新 def ✅ genuine
                 │
                 ├──▶ R-2 ratio derivative (chain rule) ✅ @audit:ok sorryAx-free
                 │         │
                 │         └──▶ R-3 r'(t) ≤ 0  🚧 type-check done (arith core genuine, sufficiency PASS)
                 │                   │
                 │                   ├──▶ R-3′ density-identification bridge ❌ 撤退 (L-Ratio-3′-α、bridge 案 infeasible)
                 │                   │        (M0′ verbatim 照合: ルート A/B 両 infeasible、IsStamInequalityHyp witness ∀-量化結論形が赤フラグ)
                 │                   └──▶ R-3″ IsStamInequalityHyp 結論形 pivot 🎯 NEXT (別 sub-plan へ委譲)
                 │                            (predicate def 書換 = witness ∀-量化 → measure-level 直接形)
                 │
                 └──▶ R-4 endpoint r(1)=0 + r(0)≥0 ⟺ EPI 橋
                          │
                          └──▶ R-5 AntitoneOn lift + difference-chain 再配線 ──▶ W1/W0 headline
R-6 (docs-only): auditor doctrine 強化提案
```

R-1/R-2 genuine 完成、R-3 は arith core まで genuine (sufficiency 監査 PASS)。**残ボトルネック =
R-3 の唯一の sorry `h_plain_stam`**。当初これは「`IsStamInequalityHyp` consumer plumbing
(bridge) で閉じる」(= R-3′) と見込んだが、**2026-06-01 Wave 3 で R-3′ bridge 案は撤退**
(L-Ratio-3′-α 発火)。M0′ verbatim 照合でルート A (consumer plumbing) / ルート B (producer 直呼び)
**両方 infeasible** と確定 — `IsStamInequalityHyp` の **witness ∀-量化 結論形が赤フラグ**で、
consume するには 4 系統 (`IsRegularDensityV2`×2 / `∫=1`×2 / cross-source convolution 同定 /
Blachman 19-field) が consumer に再浮上し、うち 2 つ (一般 density Blachman = Gaussian 専用 producer のみ
≈Mathlib 壁級、cross-source convolution 同定 = single-source structure で原理的に表現不能) が
closure 不能。真の closure 路は **R-3″ = `IsStamInequalityHyp` の結論形を measure-level 直接形に
pivot する def 書換** (別 sub-plan へ委譲)。これが整えば ratio monotonicity atom が完成し R-4/R-5 が
unblock される。

## 設計判断: redefine vs new def

**推奨 = (b) 新 def `csiszarLogRatioGap` を導入し chain を移行** (旧 `csiszarGap1Source` は
difference-gap のまま残置 → R-5 で deprecate / 再配線)。理由:

1. **Mathlib-shape-driven**: ratio derivative lemma の結論形を、`Real.log`/`Real.exp` 単調性 +
   商微分 (`HasDerivAt.div` / `Real.hasDerivAt_log`) + plain Stam が hand する形に合わせる。
   差分 def を流用すると、既に difference 形 (`N_sum − N_X − N_Y`) を結論に焼き込んだ
   endpoint lemma 群 (下記 blast-radius) と型が衝突する。新 def なら旧 lemma を壊さず
   段階移行できる。
2. **honesty 上の安全**: 旧 `csiszarGap1Source` を ratio に **再定義 (in-place rewrite)** すると、
   それを `@audit:ok` で参照する `csiszarGap_eq_one_source_via_rescale` / `csiszarGap1Source_at_zero`
   の意味が黙って変わり、過去の audit pass が無効化されたことが grep で見えない。新 def なら
   旧 `@audit:ok` lemma は型が変わらないまま残り、ratio 側の新 lemma に対して fresh audit が走る。
3. **数値・型の verbatim 確認済前提**: `entropyPower μ = Real.exp (2·differentialEntropy μ) > 0`
   (`entropyPower_pos` `EntropyPowerInequality.lean:108`、`@audit:ok`) なので
   `log N_i` / `log (N_X+N_Y)` は well-defined (`N_X+N_Y > 0` は `add_pos (entropyPower_pos _)
   (entropyPower_pos _)`、`EPIPlumbing.lean:274` に既出 idiom)。`Real.log` の引数正値性が
   常に取れるため、商微分/log 微分の副条件が genuine に discharge できる。

**新 def の Mathlib-shape 案** (R-1 で確定):

```lean
/-- 1-source Csiszár **log-ratio** gap (genuine monotone object).
`r(t) = log (N_sum t) − log (N_X t + N_Y t)`、N_i = entropyPower (P.map path_i). -/
noncomputable def csiszarLogRatioGap {Ω : Type*} [MeasurableSpace Ω]
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) (t : ℝ) : ℝ :=
  Real.log (entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω))))
    - Real.log
        (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
          + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)))
```

R-2 で「ratio derivative の結論形」を loogle 照合し、必要なら `log (A/B)` 形か
`log A − log B` 形のどちらが `HasDerivAt.sub (Real.hasDerivAt_log ..) (...)` に乗りやすいかで
微調整する (差分形のほうが項別微分しやすい見込み)。

## Blast-radius table

各既存 declaration を verbatim 読み込み済。ratio 再frame 下での survive / re-derive / delete を記録。
**重要**: `csiszarGap1Source` (difference def) を残置する設計 (b) では、それを参照する `@audit:ok`
lemma 群は**型としては survive する** が、headline チェーン上 **load-bearing でなくなる** (ratio 側に
移行) ものがある。下表の「役割変化」列がそれ。

| # | declaration | file:line | 現状態 | 現結論形 (verbatim) | ratio 再frame 下 |
|---|---|---|---|---|---|
| D1 | `csiszarGap1Source` (def) | `EPIL3Integration.lean:1335` | `@audit:ok` (def) | `eP(P.map(X+Y+√t·(Z_X+Z_Y))) − eP(P.map(X+√t·Z_X)) − eP(P.map(Y+√t·Z_Y))` | **survive** (型変更なし)。新 `csiszarLogRatioGap` と併存。headline チェーン上は ratio 側へ役割移行 (difference は EPI endpoint の `≥0` 比較にのみ使用) |
| D2 | `csiszarGap1Source_hasDerivAt` | `EPIStamToBridge.lean:474` | genuine (transitive de Bruijn 壁、`@residual` 無し) | `HasDerivAt (csiszarGap1Source ..) (N_sum·J_sum − N_X·J_X − N_Y·J_Y) t` | **survive as-is** + **新規 `csiszarLogRatioGap_hasDerivAt` を R-2 で追加**。差分微分は genuine なので削除不要、ratio 微分は商/log 微分でこれを再利用 (`HasDerivAt.div`, `Real.hasDerivAt_log`) |
| D3 | `csiszarGap1Source_deriv_le_zero` | `EPIStamToBridge.lean:682` | `@audit:defect(false-statement)` | `N_sum·J_sum − N_X·J_X − N_Y·J_Y ≤ 0` (**FALSE**) | **delete / 置換**。後継 = R-3 `csiszarLogRatioGap_deriv_le_zero` : `J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y) ≤ 0` (genuine)。旧 signature は defect marker として一時残置可だが R-5 で削除 |
| D4 | `csiszarGap1Source_continuousOn` | `EPIStamToBridge.lean:782` | `sorry` `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` (G2、真 Mathlib 壁寄り) | `ContinuousOn (csiszarGap1Source ..) (Ici 0)` | **re-derive for ratio**: `csiszarLogRatioGap_continuousOn`。`log` は連続 (`Real.continuous_log` on `>0`)、内側 `N_i` 連続性は difference 版と同じ DCT 壁 (G2 と同根、新 wall name 不要・既存 `@residual` 流用)。ratio 化で連続性壁は悪化しない (log/加算/減算は連続写像合成) |
| D5 | `csiszarGap1Source_differentiableOn_interior` | `EPIStamToBridge.lean:795` | genuine (A-2-3 経由) | `DifferentiableOn (csiszarGap1Source ..) (Ioi 0)` | **re-derive for ratio**: D2-ratio (`csiszarLogRatioGap_hasDerivAt`) + `HasDerivAt.differentiableAt`。log/商の可微分性副条件 (`N_i ≠ 0`) は `entropyPower_pos` で genuine 供給 |
| D6 | `csiszarGap1Source_antitoneOn_Ici_zero` | `EPIStamToBridge.lean:827` | genuine assembly (D3 を呼ぶため transitive に偽を継承) | `AntitoneOn (csiszarGap1Source ..) (Ici 0)` | **re-derive for ratio**: `csiszarLogRatioGap_antitoneOn_Ici_zero`。`antitoneOn_of_deriv_nonpos` + R-3 (genuine `r'≤0`) + D4-ratio + D5-ratio。**現 D6 は偽の D3 を呼ぶので transitive に偽を継承していた** (`@audit:ok` 誤付与でないか R-5 で要確認、現状 `@audit:ok` タグ無し) |
| D7 | `csiszarGap_eq_one_source_via_rescale` | `EPIL3Integration.lean:1365` | `@audit:ok` | `csiszarGap X Y Z_X Z_Y P s = (1-s)·csiszarGap1Source X Y Z_X Z_Y P (s/(1-s))` | **要精査**。`(1-s)` scalar pull-out は `entropyPower_map_mul_const` (`eP(μ.map(·*c)) = c²·eP μ`) に依存。**ratio 形では `c²` 因子が log の中で相殺する**: `log(c²·N_sum) − log(c²·(N_X+N_Y)) = log N_sum − log(N_X+N_Y)` (`c² > 0` で `log` 加法分解、`c²` 項がキャンセル)。→ rescale が ratio では **(1-s) 因子無しの不変量** `csiszarLogRatioGap(s) = csiszarLogRatioGap1Source(s/(1-s))` になる可能性大 (scale 不変)。この相殺は ratio 設計の **追加利点** (difference 版の `(1-s)` 因子 bookkeeping が消える)。R-2/R-5 で verbatim 確認必須 |
| D8 | `csiszarGap_at_one_eq_zero_of_gaussian_pair` | `EPIL3Integration.lean:1154` | `@audit:ok` | `csiszarGap X Y Z_X Z_Y P 1 = 0` (difference 形 endpoint) | **survive + ratio endpoint 追加**。ratio endpoint は `csiszarLogRatioGap .. 1 = log N_sum(1) − log(N_X(1)+N_Y(1)) = log 1 = 0` を要する。Gaussian saturation `entropyPower_gaussian_additivity` (D8 が既に使用、`N_sum(1) = N_X(1)+N_Y(1)`) → `log(A) − log(A) = 0`。D8 の Gaussian 加法性は **そのまま再利用可能** (difference=0 ⟺ ratio=0 が `N_sum=N_X+N_Y` から両立) |
| D9 | `csiszarGap1Source_at_zero` | `EPIL3Integration.lean:1544` | `@audit:ok` | `csiszarGap1Source .. 0 = eP(P.map(X+Y)) − eP(P.map X) − eP(P.map Y)` | **survive + ratio t=0 追加**: `csiszarLogRatioGap .. 0 = log eP(X+Y) − log(eP X + eP Y)`。EPI ⟺ `r(0) ≥ 0` の橋 (R-4) はこの形を使う。`√0=0` simp は同型 |
| D10 | `isStamToEPIScalingHyp_of_stam_debruijn` | `EPIStamToBridge.lean:919` | genuine assembly + 1 `sorry` (G4 joint indep `@residual(plan:epi-stam-to-conclusion-phaseA-plan)`) | `IsStamToEPIScalingHyp X Y P` | **re-wire**: 内部で D6 (`csiszarGap1Source_antitoneOn_Ici_zero`) を呼ぶ箇所を ratio 版 D6-ratio に差替え。G4 joint-indep `sorry` は ratio 無関係 (richness gap、別 plan 所有) なので残置 |
| D11 | `csiszarGap_antitoneOn_Icc_zero_one` | `EPIStamToBridge.lean:887` | `sorry` `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` (G3 rescale) | `AntitoneOn (fun s => eP(heatFlowPath2 sum) − eP(X path) − eP(Y path)) (Icc 0 1)` | **要精査 (D7 連動)**: 現結論は difference 形 (2-source `csiszarGap` 展開)。ratio rescale が scale 不変 (D7) なら、`AntitoneOn (csiszarLogRatioGap ..) (Icc 0 1)` を経由して difference の `AntitoneOn` に戻すか、headline が ratio monotonicity で足りるか R-5 で判定。最悪 difference monotonicity を ratio + `N_sum ≥ N_X+N_Y` から導出 |
| D12 | `isStamToEPIBridgeHyp_of_scaling` / `stamToEPIScaling_holds` / `stamToEPIBridge_holds` | `EPIStamToBridge.lean:211` / `EntropyPowerInequality.lean:249` | shared sorry / assembly (W1/W0) | `IsStamInequalityResidual → IsEntropyPowerInequalityHypothesis` | **survive**: ratio チェーンが D10 まで genuine 化すれば、W1/W0 集約点は ratio に非依存 (型は `IsStamToEPIScalingHyp` で不変)。R-5 完了後に W1/W0 が transitive sorryAx-free になるか `#print axioms` で確認 |

### Blast-radius verdict (集計)

- **re-derive 必要な `@audit:ok` / genuine lemma**: D4, D5, D6 (3 件、ratio 版を新規作成)。
  D2 は survive + ratio 版を**追加** (削除不要)。
- **delete / 置換**: D3 (偽の deriv_le_zero) 1 件。
- **要精査 (型衝突 / scale 相殺の verbatim 確認)**: D7, D11 (2 件、rescale チェーン)。
- **survive そのまま**: D1, D8, D9, D12 (4 件、ratio endpoint/t=0 lemma を**追加**するが既存型は不変)。
- **downgrade 候補の `@audit:ok` tag**: D6 は偽の D3 を transitive に呼んでいたため、もし
  `@audit:ok` が付いていれば誤付与 (現状 D6 にタグ無し、念のため R-5 で再確認)。D1/D7/D8/D9 の
  `@audit:ok` は difference 形に対する正当な pass なので **downgrade 不要** (型不変、ratio 側は
  fresh audit)。

## Phase 詳細

### M0 — 在庫調査 (前提工程)

proof-log: no (調査のみ)

1. **商微分 / log 微分 API**: loogle で `Real.hasDerivAt_log`, `HasDerivAt.div`, `HasDerivAt.log`,
   `Real.hasDerivAt_log` の signature + 副条件 (`x ≠ 0` / `0 < x`) を verbatim 確認。
   `log A − log B` 形と `log (A/B)` 形のどちらが乗りやすいか判定。
2. **weighted Stam algebra**: `J_sum ≤ α²J_X + β²J_Y` (λ=α 特化) を plain Stam から取り出す補題が
   in-house にあるか確認。無ければ R-3 で `IsStamInequalityHyp` から `nlinarith` で導出。
   `α²≤α` (`0≤α≤1`) は `sq_le_self'` / `mul_le_one` 系で照合。
3. **D7 scale 相殺の verbatim 確認**: `entropyPower_map_mul_const` (`EPIPlumbing.lean:130`) の結論
   `eP(μ.map(·*c)) = c²·eP μ` を読み、`log(c²·A) − log(c²·B) = log A − log B` が `Real.log_mul`
   (`c²>0`, `A,B>0`) で成立することを確認。`c² = 1-s > 0` (`s∈Ico 0 1`)。

### Phase R-1 — `csiszarLogRatioGap` 新 def ✅ DONE (genuine, proof-done)

proof-log: no (def のみ)

- `EPIL3Integration.lean:~1353` に `csiszarLogRatioGap` 新 def 追加済 (上記 Mathlib-shape 案通り)。
- `csiszarLogRatioGap_at_zero` (`:1363`) genuine, proof-done。
- def 自体は `Prop` でも `inductive` でもないので **`sorry` 不要** — 型チェック済。
- **状態**: 0 sorry / 0 residual。

### Phase R-2 — ratio derivative lemma ✅ DONE (genuine, `@audit:ok`)

proof-log: yes

- **完了** (2026-06-01 Wave 1, commit 55cb7e6): `csiszarLogRatioGap_hasDerivAt`
  (`EPIStamToBridge.lean:681`)。独立 `#print axioms` で **sorryAx-free** 確認。
  結論 deriv = `J_sum − (N_X·J_X + N_Y·J_Y)/(N_X+N_Y)` (intended signature 通り)。
- skeleton で予測した「D2 を項ごと再利用 + `Real.hasDerivAt_log` + 商微分」は genuine に通った。
- 以下は起草時の skeleton (履歴として残置):

**intended signature** (skeleton):
```lean
theorem csiszarLogRatioGap_hasDerivAt
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (hY : Measurable Y) (hZY : Measurable Z_Y) (hYZY : IndepFun Y Z_Y P)
    (hXYZXY : IndepFun (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_sum : …IsDeBruijnRegularityHyp (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X : …IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : …IsDeBruijnRegularityHyp Y Z_Y P)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => csiszarLogRatioGap X Y Z_X Z_Y P s)
      (J_sum
        - (N_X * J_X + N_Y * J_Y) / (N_X + N_Y)) t   -- N_i = entropyPower (P.map path_i t)
```
- body: D2 (`csiszarGap1Source_hasDerivAt` の `d/dt N_i = N_i·J_i` 形) を **項ごとに** 再利用。
  `r = log N_sum − log(N_X+N_Y)`。
  - `d/dt log N_sum = (N_sum·J_sum)/N_sum = J_sum` (`Real.hasDerivAt_log` + `N_sum>0`)。
  - `d/dt log(N_X+N_Y) = (N_X·J_X + N_Y·J_Y)/(N_X+N_Y)`。
- D2 は差分 def に対する `HasDerivAt` なので、各 `N_i` の `HasDerivAt N_i (N_i·J_i)` は D2 内部の
  `h_eP_X` / `h_eP_Y` / `h_eP_sum` を切り出すか、`entropyPower_hasDerivAt_of_diffEnt_hasDerivAt`
  (`EPIStamToBridge.lean:443`) を直接呼ぶ (こちらが clean)。
- **honesty**: `h_reg_*` は regularity precondition、de Bruijn 壁は transitive (D2 と同じく
  `@residual` 不要、wall 補題が sorry を保持)。

### Phase R-3 — genuine `r'(t) ≤ 0` 🚧 type-check done (1 sorry)

proof-log: yes

**完了状況 (2026-06-01 Wave 1, commit 55cb7e6)**: `csiszarLogRatioGap_deriv_le_zero`
(`EPIStamToBridge.lean:839`)。
- arith core `csiszar_ratio_deriv_le_zero_arith` (`:639`) への配線 + 5 正値性 (`hNX_pos`/
  `hNY_pos` は `entropyPower_pos`、`hJ*_pos` は引数) は **genuine**。
- 独立 honesty 監査で **sufficiency PASS**: ratio 形 `J_sum·(N_X+N_Y) ≤ N_X·J_X+N_Y·J_Y` は
  plain Stam `1/J_sum ≥ 1/J_X+1/J_Y` + 正値性から閉じ反例なし (slack `N_X·J_X²+N_Y·J_Y²≥0`)。
  前任者 difference 版 (`csiszarGap1Source_deriv_le_zero`, false-as-framed) と決定的に異なる。
  classification `@residual(plan:epi-csiszar-ratio-reframe-plan)` + `@audit:residual-ok
  (sufficiency-checked)` 是認。
- **唯一の残 sorry** = `h_plain_stam : 1/J_sum ≥ 1/J_X + 1/J_Y` の抽出 (`:892`)。
  weighted-λ 核 (旧 step 3-5) は arith core に吸収され genuine 化済。残ったのは
  `IsStamInequalityHyp` consumer plumbing のみ → **R-3′ に分離**。

起草時 skeleton (履歴):

**intended signature**:
```lean
theorem csiszarLogRatioGap_deriv_le_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_reg_sum : …IsDeBruijnRegularityHyp (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X : …IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : …IsDeBruijnRegularityHyp Y Z_Y P)
    {t : ℝ} (ht : 0 < t)
    (hJX_pos : 0 < J_X) (hJY_pos : 0 < J_Y) (hJsum_pos : 0 < J_sum)
    (h_stam : …IsStamInequalityHyp (fun ω => X ω + √t * Z_X ω)
                                   (fun ω => Y ω + √t * Z_Y ω) P) :
    J_sum - (N_X * J_X + N_Y * J_Y) / (N_X + N_Y) ≤ 0
```
ここで `N_i = entropyPower (P.map path_i)`, `J_i = fisherInfoOfDensityReal ((h_reg_*.reg_at t ht).density_t)`。

**closure 手順 (純 algebra、Mathlib 壁なし)**:
1. `N_X+N_Y > 0` (`add_pos (entropyPower_pos _) (entropyPower_pos _)`)。`r'≤0` ⟺
   `J_sum·(N_X+N_Y) ≤ N_X·J_X + N_Y·J_Y` に clear-denominators (`div_le_iff` / `le_div_iff`)。
2. `h_stam` から plain harmonic Stam `1/J_sum ≥ 1/J_X + 1/J_Y` を取り出す
   (D3 旧手順 step 1 と同じ: `(fisherInfoOfMeasureV2 _ f).toReal = fisherInfoOfDensityReal f` は `rfl`、
   pointwise sum 同定は `funext + ring`)。正値性で `J_sum ≤ J_X·J_Y/(J_X+J_Y)` に変形。
3. **weighted-λ step (genuine 核)**: `α = N_X/(N_X+N_Y)`, `β = N_Y/(N_X+N_Y)`。
   `J_X·J_Y/(J_X+J_Y) = min_λ (λ²J_X+(1−λ)²J_Y) ≤ α²J_X+β²J_Y` (λ=α 特化、harmonic mean は
   最小値)。`α+β=1` なので `(1−α)=β`。
4. `α²≤α`, `β²≤β` (`0≤α,β≤1`、`sq_le_self'`) より `α²J_X+β²J_Y ≤ αJ_X+βJ_Y`。
5. `αJ_X+βJ_Y = (N_X·J_X+N_Y·J_Y)/(N_X+N_Y)` (`α,β` 定義代入)。`J_sum·(N_X+N_Y) ≤ N_X·J_X+N_Y·J_Y`
   が `nlinarith` または手動連鎖で閉じる。
- **honesty**: `h_stam` は EPI 結論と別 Prop の genuine residual (Stam 壁)、`h_reg_*` は regularity。
  load-bearing predicate bundling **なし**。`Y:=0`/`Z_Y:=0` 退化悪用 **禁止**
  (`entropyPower(dirac 0)=1` で degenerate 罠、parent 判断ログ参照)。

**撤退ライン L-Ratio-3-α (発火済、2026-06-01)**: 起草時の予測 (<10%、weighted-λ 核が in-house
補題不在) とは **別の root cause** で発火した。weighted-λ 核は arith core に吸収され genuine 化
したが、`h_stam : IsStamInequalityHyp (path_X) (path_Y) P` から plain Stam を取り出す
**consumer plumbing** (density witness 供給) が R-3 予算を超過し、`h_plain_stam` が `sorry` +
`@residual(plan:epi-csiszar-ratio-reframe-plan)` で残置。**これは genuine な未完成であって偽の
statement ではない** (difference 版と決定的に異なる、sufficiency 監査 PASS)。新規 predicate
bundle なし。詳細な root cause + 閉じ方は **Phase R-3′** に scope。

### Phase R-3′ — density-identification bridge 🎯 NEXT (R-3 closure の真のボトルネック)

> R-3 残 sorry `h_plain_stam` (`EPIStamToBridge.lean:892`) を genuine に閉じる。
> これが整えば ratio チェーンの monotonicity atom が完成し、R-4/R-5 が unblock される。

proof-log: yes

#### 1. ボトルネックの正体

R-3 の body は `csiszar_ratio_deriv_le_zero_arith` (genuine) を呼ぶために
`h_plain_stam : 1/J_sum ≥ 1/J_X + 1/J_Y` を必要とする。ここで `J_i =
fisherInfoOfDensityReal ((h_reg_*.reg_at t ht).density_t)`、path は
`path_X = X + √t·Z_X`, `path_Y = Y + √t·Z_Y`, `path_sum = (X+Y) + √t·(Z_X+Z_Y)`。

唯一の供給元は仮説 `h_stam : IsStamInequalityHyp path_X path_Y P`。これを **consume** して
`1/J_sum ≥ 1/J_X + 1/J_Y` を取り出すには、consumer が `IsStamInequalityHyp` def の
全 binder (density witness `fX fY fXY` + 各 regularity 入力) を供給せねばならない。
その入力が `IsDeBruijnRegularityHyp` バンドルに **含まれていない** のが root cause。

#### 2. `IsStamInequalityHyp` の verbatim 定義 (consumer が供給すべき入力)

`Common2026/Shannon/EPIStamDischarge.lean:126`、`@audit:ok` (sound non-vacuous Prop):

```lean
def IsStamInequalityHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
    J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
    J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
    J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Y ω)) fXY).toReal →
    Common2026.Shannon.FisherInfoV2.IsRegularDensityV2 fX →
    Common2026.Shannon.FisherInfoV2.IsRegularDensityV2 fY →
    (∫ x, fX x ∂MeasureTheory.volume = 1) →
    (∫ x, fY x ∂MeasureTheory.volume = 1) →
    (∀ x, fXY x =
      InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY x) →
    InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady fX fY →
    1 / J_sum ≥ 1 / J_X + 1 / J_Y
```

consumer (= R-3 の `h_plain_stam`) が `h_stam` を applied するために供給すべき入力:

- `J_X J_Y J_sum : ℝ` (R-3 では `fisherInfoOfDensityReal (.density_t)` の 3 値)
- 正値性 `0 < J_X`, `0 < J_Y`, `0 < J_sum` (R-3 では `hJX_pos`/`hJY_pos`/`hJsum_pos` 引数)
- 同定 `J_i = (fisherInfoOfMeasureV2 (P.map path_i) f_i).toReal` (3 本、density witness と紐付け)
- `IsRegularDensityV2 fX`, `IsRegularDensityV2 fY` (smoothness バンドル)
- 正規化 `∫ fX = 1`, `∫ fY = 1`
- pointwise convolution `∀ x, fXY x = convDensityAdd fX fY x`
- `IsBlachmanConvReady fX fY` (Blachman 19-field バンドル)

#### 3. `IsDeBruijnRegularityHyp` の verbatim 定義 (何を提供するか)

`Common2026/Shannon/EPIStamDischarge.lean:250`、`@audit:retract-candidate(load-bearing-predicate)`:

```lean
structure IsDeBruijnRegularityHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] where
  density_path : ℝ → ℝ → ℝ
  reg_at : ∀ t : ℝ, 0 < t → Common2026.Shannon.FisherInfoV2.IsRegularDeBruijnHypV2 X Z P t
  density_t_eq : ∀ t : ℝ, ∀ ht : 0 < t,
    (reg_at t ht).density_t = density_path t
  integrable_deriv :
    ∀ T : ℝ, 0 < T →
      IntervalIntegrable
        (fun t : ℝ => (1/2)
          * (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Real.sqrt t * Z ω)) (density_path t)).toReal)
        volume 0 T
```

提供するもの: `density_path` (path ごとの density witness)、`reg_at t ht` (V2 de Bruijn 正則性、
内部 `density_t` を持つ)、`density_t_eq` (内部 witness を `density_path t` に pin)、
`integrable_deriv` (bounded-T 区間可積分)。**`IsBlachmanConvReady` も `∫=1` 制約も pointwise
convolution 同定も含まない** (verbatim 確認: 上記 4 field のみ、density は `density_t` / `density_path`
系のみで Blachman バンドル不在)。

#### 4. Gap table (consumer 要求 × DeBruijn 提供 × 不足分の供給)

| `IsStamInequalityHyp` 要求入力 | `IsDeBruijnRegularityHyp` が提供? | 不足分の供給方法 |
|---|---|---|
| `J_X J_Y J_sum` 数値 | ✅ `fisherInfoOfDensityReal (.density_t)` で R-3 が既に `set` | (R-3 既存) |
| `0 < J_*` 正値性 | △ (DeBruijn には無いが R-3 引数 `hJ*_pos` で供給済) | (R-3 既存引数) |
| `J_i = (fisherInfoOfMeasureV2 (P.map path_i) f_i).toReal` | △ `fisherInfoOfDensityReal f = (fisherInfoOfMeasureV2 _ f).toReal` は `rfl` (R-3 docstring 記載)、ただし `P.map path_i` 上の **どの** witness `f_i` を選ぶかが要決定 | `.density_t` を witness に取れば同定は `rfl` 近傍。`P.map path_i` の measure と density の整合は `reg_at` 内部の `IsRegularDeBruijnHypV2` が持つ density の意味から導く |
| `IsRegularDensityV2 fX`, `fY` | ❌ DeBruijn は `IsRegularDeBruijnHypV2` (別 predicate) を持つ。`density_t` が `IsRegularDensityV2` を満たすかは要 bridge | `IsRegularDeBruijnHypV2 → IsRegularDensityV2 (density_t)` の射影/bridge を確認 (in-house、§5 参照) |
| `∫ fX = 1`, `∫ fY = 1` | ❌ DeBruijn は正規化を持たない | path density が probability density (`P.map path` は probability measure、`P` が `IsProbabilityMeasure`) であることから `∫ density_t = 1` を導く bridge。`density_t` が `P.map path` の density である事実が要 |
| `∀ x, fXY x = convDensityAdd fX fY x` | ❌ DeBruijn は convolution 同定を持たない | **これが核**: path_sum の density が path_X / path_Y の density の畳み込みであること。独立性 `IndepFun path_X path_Y P` (R-3 では `Z_X, Z_Y` 独立 + X,Y 構造) から `convDensityAdd` 表示を出す |
| `IsBlachmanConvReady fX fY` | ❌ DeBruijn は Blachman バンドルを持たない | Blachman 19-field を density から構成 (in-house、`isBlachmanConvReady_*` 系 producer があるか §5 で照合) |

#### 5. ★ 省略経路 (当初の楽観) — 既存 producer `isStamInequalityHyp_via_step3`

> **⚠️ 検証結果で訂正 (2026-06-01 Wave 3、L-Ratio-3′-α)**: 本節は起草時、producer 直呼び
> (ルート B) が consumer 側の density 入力供給 (gap table ❌ 行) を **回避できる**という楽観を
> 述べていた。M0′ verbatim 照合の結果 **この楽観は誤り** — `isStamInequalityHyp_via_step3` /
> `isStamInequalityHyp_via_body` は `IsStamInequalityHyp X Y P` という **∀-量化 Prop を返すだけ**で、
> producer を呼んでも `1/J_sum ≥ 1/J_X+1/J_Y` を取り出す **apply step は同一**。apply 時に
> witness `(J_X J_Y J_sum fX fY fXY)` + 4 系統 antecedent (`IsRegularDensityV2`×2 / `∫=1`×2 /
> convolution 同定 / Blachman) が consumer (R-3) に **再浮上する** (= ルート A と同じ ❌ 行)。
> producer 内部は regularity 入力を `intro` してから使う設計だが、それらの入力はどこでも
> discharge されず最終 consumer (R-3) 任せ。**ルート B もルート A と同じ apply 問題に帰着、
> 回避不能**。詳細な root cause は §8 撤退ライン参照。
>
> **致命傷 2 点 (closure 不能)**:
> 1. **cross-source convolution 同定** `density(path_sum) = convDensityAdd (density path_X) (density path_Y)`:
>    該当 in-house 補題が **不在** (`EPIConvDensity*.lean` は Gaussian 微分系のみ)。さらに
>    `IndepFun path_X path_Y P` を要するが **R-3 の仮説に存在しない** (上流 `_antitoneOn_Ici_zero`
>    にはあるが R-3 まで thread されていない)。`IsDeBruijnRegularityHyp X Z P` は **single-source
>    structure** なので、path_X と path_Y の独立性を要する cross-source convolution は field 追加でも
>    **原理的に表現不能**。
> 2. **一般 density `IsBlachmanConvReady`**: producer は `isBlachmanConvReady_gaussianPDFReal`
>    (**Gaussian 専用**、`EPIBlachmanGaussianWitness.lean:335`) + `_symm` のみ。一般 path density 用
>    producer は **不在**、>>60 行で実質 **Mathlib 壁相当**。
>
> `IsRegularDensityV2` / `∫=1` は `IsRegularDeBruijnHypV2.density_t` (+ `density_t_eq`) から導出余地
> ありだが、上記 2 つが closure 不能なため bridge 案全体が頓挫。

**(以下は起草時の楽観記述、履歴として残置)** in-tree に `IsStamInequalityHyp` の genuine producer が既にある:

```lean
-- Common2026/Shannon/EPIStamStep3Body.lean:119  (@audit:ok, sorryAx-free)
theorem isStamInequalityHyp_via_step3 {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    IsStamInequalityHyp X Y P :=
  isStamInequalityHyp_via_body (stam_step2_density_wall P X Y hX hY hXY)
```

これは `IsStamInequalityHyp X Y P` を **`Measurable X` + `Measurable Y` + `IndepFun X Y P` だけ**から
genuine に生成する (density bundle / Blachman / 正規化 / convolution 同定はすべて producer 内部の
`stam_step2_density_wall` → `isStamInequalityHyp_via_body` で閉じている、3 補題とも `@audit:ok`
sorryAx-free)。in-tree の `IsStamInequalityHyp` consumer が 0 件 (全 use-site が producer side) で
R-3 が初の consumer、という brief の観察と整合する: **consumer が density 入力を組む必要が無い設計**
であり、producer を呼べば良い。

**従って R-3′ の真の作業は density bridge 組立ではなく**:

1. **producer の path への適用**: `h_stam : IsStamInequalityHyp path_X path_Y P` は R-3 では引数で
   渡されているが、`isStamInequalityHyp_via_step3 P path_X path_Y (h_meas_X) (h_meas_Y) (h_indep)`
   で **構成可能**かもしれない (引数 `h_stam` を消して producer 呼出に置換)。
2. **R-3 consumer 側で `h_stam.apply`**: `h_plain_stam` を埋めるには `h_stam` を 3 Fisher 値 +
   density witness で apply して `1/J_sum ≥ 1/J_X + 1/J_Y` を取り出す。ここで witness を
   `.density_t` に取り、`IsRegularDensityV2` / `∫=1` / convolution / `IsBlachmanConvReady` を
   供給する必要が残る。**この供給こそが gap table の ❌ 行**。

→ **2 つのルート**:
- **ルート A (consumer plumbing)**: `h_stam` を apply するため gap table の ❌ 入力を
  `IsDeBruijnRegularityHyp` + 独立性 + `P` の probability 性から in-house 補題で供給。density
  bridge を実際に組む。
- **ルート B (producer 直呼び、軽量)**: R-3 の `h_stam` 引数自体を不要にし、body 内で
  `isStamInequalityHyp_via_step3` を呼んで `IsStamInequalityHyp path_X path_Y P` を構成
  → さらに同 producer chain が `1/J_sum ≥ ...` を出す形に再配線。`EPIStamToBridge.lean` は現状
  `EPIStamStep3Body` を import していない (verbatim 確認: imports L1-16 に無し) が、`EPIStamStep3Body`
  は `EPIStamToBridge` を import しない (cycle 無し、verbatim 確認) ので import 追加で解決可。

**M0′ で両ルートのコストを比較し軽い方を採る** (ルート B が有望: producer が既に `@audit:ok`、
consumer の `h_stam.apply` で残る ❌ 入力供給を回避できる可能性)。ただし `_via_step3` は
`IsStamInequalityHyp X Y P` (= ∀-quantified Prop) を返すのみで、それを 3 つの具体 Fisher 値で
apply する段で結局 ❌ 入力が再浮上しうる — apply 時の witness 選択と regularity 供給が
producer 内に隠れているか consumer に出てくるかを M0′ で verbatim 判定する。

#### 6. Mathlib 壁か in-house plumbing か (判定)

> **⚠️ 注釈追加 (2026-06-01 Wave 3、L-Ratio-3′-α)**: 本節の「純 in-house plumbing、Mathlib 壁
> ではない」判定は **partial に訂正**。M0′ verbatim 照合で、plumbing が closure 不能な 2 つの gap に
> 接続していると判明: (a) **一般 density Blachman** (Gaussian 専用 producer のみ、一般 path density 用
> producer 不在 → ~Mathlib 壁級)、(b) **cross-source convolution 同定** (single-source
> `IsDeBruijnRegularityHyp` structure では path_X/path_Y 独立性を要する convolution が原理的に
> 表現不能 + 該当 in-house 補題不在)。よって R-3′ は **純 plumbing ではなく**、`IsStamInequalityHyp`
> の **結論形 def-pivot** が本筋 (R-3″ = 別 sub-plan)。R-3 の `@residual` 分類は **`plan:` のままで
> 良い** (closure は def 書換 = plan 作業であり Mathlib 壁の新規追加ではない) が、接続先に壁級 gap が
> あること + 真の closure 路が bridge ではなく predicate reshape であることを明記。

**(以下は起草時判定、上記注釈で訂正)** in-house density-identification plumbing、Mathlib 不在の壁ではない (独立 auditor 評価と一致)。
根拠:
- `IsStamInequalityHyp` の core 不等式 `1/J_sum ≥ 1/J_X+1/J_Y` は既に `stam_step2_density_wall`
  経由で genuine 閉 (`@audit:ok`、Stam 壁 `stam-step2-density` は CLOSED 相当)。
- 残るのは「`IsDeBruijnRegularityHyp` の `density_t` を `IsStamInequalityHyp` consumer が要求する
  density 入力形 (`IsRegularDensityV2` / `∫=1` / convolution / Blachman) に変換する」配管のみ。
  これは Mathlib API の不在ではなく、2 つの in-house predicate 間の射影/同定。
- → classification `@residual(plan:epi-csiszar-ratio-reframe-plan)` が **正しい** (`wall:` ではない)。
  本 plan が closure 担当。

#### 7. Phase 詳細 (step) — ❌ 全 step 撤退 (M0′ で bridge infeasible 確定、R-3′-1/2/3 着手せず)

> M0′ 在庫照合の結果ルート A・B 両 infeasible (§5 訂正 + §8 参照)。実装 step R-3′-1/2/3 は
> **着手せず撤退**。後継は R-3″ (predicate reshape、別 sub-plan)。

- [x] **M0′** — 在庫照合 (proof-log: no) ✅ **完了 → bridge infeasible 確定**:
  - `IsRegularDeBruijnHypV2` (`FisherInfoV2*`) を Read し、`.density_t` が `IsRegularDensityV2` を
    満たすか / `P.map path` の density である保証を持つかを verbatim 確認。
  - `isStamInequalityHyp_via_step3` / `_via_body` / `stam_step2_density_wall` の signature を Read し、
    path に適用するための前提 (`Measurable path_X` / `IndepFun path_X path_Y P`) を列挙。
  - `IsStamInequalityHyp` を apply する既存パターン (producer 内部の `intro` 後の使い方) を読み、
    consumer 側 apply で残る ❌ 入力を確定。
  - ルート A / B のコスト比較 → どちらを採るか決定。
  - **結果 (2026-06-01 Wave 3)**: ルート A・B **両 infeasible**。ルート B (producer 直呼び) も
    apply step で ❌ 入力が再浮上し、ルート A と同じ gap に帰着 (§5 訂正参照)。bridge 案全体が頓挫。
- [ ] ~~**R-3′-1** (ルート B)~~ — ❌ 撤退 (producer 直呼びでも apply 問題回避不能)。
- [ ] ~~**R-3′-2** (ルート A)~~ — ❌ 撤退 (cross-source convolution が single-source structure で
    表現不能 + 一般 density Blachman producer 不在で gap 補題が組めない)。
- [ ] ~~**R-3′-3** sorry 除去~~ — ❌ 撤退 (上記により `h_plain_stam` の `sorry` 据え置き継続)。

#### 8. 撤退ライン L-Ratio-3′-α — ★ **発火済 (2026-06-01 Wave 3)**

**発火**: M0′ verbatim 照合の結果、bridge 案 (R-3′) は **ルート A・B 両 infeasible** と確定し撤退。
当初の「bridge を組めば in-house plumbing で閉じる」前提が **誤り**と判明。

- **root cause**: `IsStamInequalityHyp` の **witness ∀-量化 結論形** (`∀ J_X J_Y J_sum fX fY fXY,
  (正値性) → (3 Fisher 同定) → IsRegularDensityV2 fX → IsRegularDensityV2 fY → ∫fX=1 → ∫fY=1 →
  (∀x, fXY x = convDensityAdd fX fY x) → IsBlachmanConvReady fX fY → 1/J_sum ≥ 1/J_X+1/J_Y`)。
  consume するには consumer (R-3) が全 witness 引数を供給せねばならず、4 系統
  (`IsRegularDensityV2`×2 / `∫=1`×2 / cross-source convolution 同定 / Blachman 19-field) が
  consumer に **再浮上**。producer 直呼び (ルート B) も apply step は同一で回避不能。
- **closure 不能な 2 致命傷**: (a) cross-source convolution 同定 = single-source
  `IsDeBruijnRegularityHyp` structure では path_X/path_Y 独立性を要する convolution が **原理的に
  表現不能** + 該当 in-house 補題不在 + `IndepFun path_X path_Y P` が R-3 仮説に存在しない。
  (b) 一般 density `IsBlachmanConvReady` = producer が Gaussian 専用 (`isBlachmanConvReady_gaussianPDFReal`)
  のみで一般 path density 用 producer 不在 (≈Mathlib 壁級)。
- **`IsDeBruijnRegularityHyp` field 追加では不十分**: convolution 同定は cross-source (2 source の
  独立性) を要するため、single-source structure `IsDeBruijnRegularityHyp X Z P` の field では
  原理的に表現不能。よって「structure 拡張で bridge を救う」起草時の代替案も無効。

**撤退の帰結 (戦略転換)**: 真の closure 路は **bridge 構築ではなく `IsStamInequalityHyp` の結論形を
measure-level 直接形に pivot する def 書換** (= R-3″、別 sub-plan)。詳細 → 次の §Phase R-3″。

- **現状維持の honesty**: R-3 の `h_plain_stam` は `sorry` + `@residual(plan:epi-csiszar-ratio-reframe-plan)`
  のまま据え置き (type-check done、honest)。R-3″ 着地までこの residual を保持。新規 `*Hypothesis`
  predicate で core を bundle する撤退は **禁止**。

### Phase R-3″ — `IsStamInequalityHyp` 結論形 pivot (predicate reshape) 🎯 NEXT (別 sub-plan へ委譲)

> R-3′ bridge 案撤退 (L-Ratio-3′-α) の後継。R-3 残 sorry `h_plain_stam` の **真の closure 路**。
> 実装は本 plan の scope を超えるため **別 sub-plan に委譲** (slug 案 `epi-stam-predicate-reshape-plan`)。

proof-log: yes (別 sub-plan 側で)

#### 戦略転換の核心

当初 R-3′ は「2 predicate (`IsStamInequalityHyp` / `IsDeBruijnRegularityHyp`) 間の
density-identification bridge を組めば in-house plumbing で閉じる」前提だった。これは **誤り**
(L-Ratio-3′-α)。本筋は CLAUDE.md「Mathlib-shape-driven Definitions」赤フラグと整合する:

- `IsStamInequalityHyp` の **witness ∀-量化 結論形が赤フラグ** — consumer に measure-level 結論を
  density-witness 越しに量化した reshaping bridge を強いる shape。CLAUDE.md の「`f (compProd ...)` を
  `∫⁻ ...` に変える bridge を探し始めたら redefine が筋」と同型の兆候。
- honest closure の本筋は bridge 構築ではなく **`IsStamInequalityHyp` の結論形を measure-level
  直接形 (`1/J_sum ≥ 1/J_X+1/J_Y` を witness 量化なしで `P.map path_i` の Fisher 情報に直接述べる形)
  に pivot** すること。producer 側 (`stam_step2_density_wall`) は既に core 不等式を genuine に出して
  いるので (`@audit:ok` sorryAx-free)、predicate の「出口形」を consumer が使える形に変える def 書換が筋。

#### 委譲先 sub-plan に渡す要件 (blast radius 精査が必須)

- `IsStamInequalityHyp` の def を touch するため、当該 predicate を **参照する全 producer / consumer の
  blast radius** を精査する: producer (`isStamInequalityHyp_via_step3` / `_via_body` /
  `stam_step2_density_wall` / `isStamInequalityHyp_symm`)、consumer (R-3
  `csiszarLogRatioGap_deriv_le_zero` の `h_stam` 引数)、defeq pass-through (docstring 記載の
  `EPIStamToBridge` / `EPIL3Integration`、および `IsStamInequalityResidual` との pivot defeq 整合)。
- **honesty 制約**: reshape 後の結論形は **load-bearing predicate にならないこと** — measure-level
  Fisher 情報 (`fisherInfoOfMeasureV2 (P.map path_i)`) を直接述べる genuine な不等式 Prop であり、
  証明の核 (Stam 不等式) は引き続き producer (`stam_step2_density_wall`) の sorryAx-free body が持つ。
  consumer は reshape された predicate を `regularity precondition` のみで apply できる形にする。
- `@residual` slug: R-3 の `h_plain_stam` を新 sub-plan slug に書換 (`@residual(plan:epi-stam-predicate-reshape-plan)`)、
  または bridge 撤退まで現 slug 継続 + 委譲を docstring 散文で明示 (orchestrator 判断)。

### Phase R-4 — endpoint + EPI 橋

proof-log: yes

- `csiszarLogRatioGap_at_one_eq_zero`: `r(1)=0`。D8 (`csiszarGap_at_one_eq_zero_of_gaussian_pair`)
  の Gaussian saturation (`N_sum(1)=N_X(1)+N_Y(1)`) を再利用 → `log A − log A = 0`
  (`Real.log` の引数同値、`sub_self`)。
- `csiszarLogRatioGap_at_zero`: `r(0) = log eP(X+Y) − log(eP X + eP Y)` (D9 t=0 形 + log)。
- `epi_of_csiszarLogRatioGap_zero_nonneg`: `r(0)≥0 → entropyPower(X+Y) ≥ entropyPower(X)+entropyPower(Y)`。
  `Real.log_le_log_iff` (両辺正値) で `log A ≥ log B ⟺ A ≥ B`。

### Phase R-5 — `AntitoneOn` lift + difference-chain 再配線

proof-log: yes

- `csiszarLogRatioGap_continuousOn` (D4-ratio) / `_differentiableOn_interior` (D5-ratio) /
  `_antitoneOn_Ici_zero` (D6-ratio): D6 と同型の `antitoneOn_of_deriv_nonpos` 組立、R-2/R-3/D4-ratio
  /D5-ratio を呼ぶ。
- D7/D11 の scale 相殺を verbatim 確認 (M0-3 の結果) し、rescale チェーンを ratio で再配線。
  scale 不変なら `csiszarLogRatioGap` の `AntitoneOn (Icc 0 1)` が `(1-s)` 因子なしで通る。
- D10 (`isStamToEPIScalingHyp_of_stam_debruijn`) 内部の D6 呼出を D6-ratio に差替え。G4 joint-indep
  `sorry` は残置 (別 plan 所有)。
- D3 (偽 lemma) を削除し、`@audit:closed-by-successor` の参照を解消。
- 完了後 `#print axioms stamToEPIBridge_holds` で「ratio チェーン由来の偽残骸が無い」ことを確認。

**撤退ライン L-Ratio-5-α**: D7 scale 相殺が log 分解で通らない (e.g. `c²` が負/0 になる退化) →
difference monotonicity を ratio + `N_sum≥N_X+N_Y` から間接導出に切替。`@residual` 継続。

### Phase R-6 — auditor doctrine 強化提案 (docs-only)

proof-log: no

`docs/audit/audit-tags.md` の honesty-auditor 監査スコープに **「sufficiency (hypotheses ⊢
conclusion) check」が欠落**していたため、本 defect (D3) は `audit:PASS 2026-05-27` を通過した
(非循環 + 非 bundling のみ検証、含意の真偽は未検証)。提案:

- `audit-tags.md` の「監査スコープ」(または `.claude/agents/honesty-auditor.md` の CORE doctrine) に
  4 つ目の check を追加: **sufficiency** — 「仮説群から結論が semantic に follow するか
  (少なくとも 1 つの反例構成を試みて棄却できるか)」。非循環/非 bundling は **必要条件であって
  十分条件ではない**。
- cross-ref: 本 plan + D3 docstring の「false negative」記述。
- 本 Phase は **提案のみ** (実際の doctrine 編集は orchestrator / auditor owner の判断、
  本 planner は `docs/<family>/*.md` のみ編集権限)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-06-01, plan 起草) difference→ratio 再frame の採用**: D3 `csiszarGap1Source_deriv_le_zero`
   が difference-gap `N_sum·J_sum ≤ N_X·J_X+N_Y·J_Y` で FALSE-as-framed (orchestrator +
   proof-pivot-advisor 独立確認、反例: `N_sum` 巨大/`N_X,N_Y` 微小)。log-ratio `r=log N_sum −
   log(N_X+N_Y)` の monotonicity が genuine (weighted-λ Stam algebra、Mathlib 壁なし) であり
   EPI 復元も equivalent。
2. **(2026-06-01) redefine ではなく new def (`csiszarLogRatioGap`) を選択**: difference 形を
   結論に焼き込んだ endpoint lemma 群 (D8/D9) との型衝突回避 + 過去の `@audit:ok` を黙って
   無効化しないため。旧 `csiszarGap1Source` は survive、headline チェーン上の役割のみ ratio へ移行。
3. **(2026-06-01) D7/D11 rescale の scale 相殺予測 (要 verbatim 確認)**: ratio では
   `entropyPower_map_mul_const` の `c²` 因子が `log(c²A)−log(c²B)=log A−log B` で相殺し、
   difference 版の `(1-s)` 因子 bookkeeping が消える可能性大。M0-3 で `Real.log_mul` + `c²>0`
   を verbatim 確認するまで確定しない (CLAUDE.md「具体的数値・型予測の verbatim 確認」)。
4. **(2026-06-01) auditor doctrine の sufficiency 欠落を R-6 で提起**: D3 が `audit:PASS` を
   通過した root cause = 監査が非循環+非bundling のみで含意の真偽 (sufficiency) を見ていなかった。
5. **(2026-06-01 Wave 1 完了, commit 55cb7e6) R-1/R-2 genuine 完成、R-3 sufficiency PASS、残 gap を
   R-3′ density-identification bridge に局所化**: R-1 (`csiszarLogRatioGap` def + `_at_zero`) proof-done、
   R-2 (`csiszarLogRatioGap_hasDerivAt`) `@audit:ok` sorryAx-free。R-3
   (`csiszarLogRatioGap_deriv_le_zero`) は arith core 配線 + 5 正値性 genuine、独立監査で **sufficiency
   PASS** (ratio 形は反例なし、前任者 difference 版 `csiszarGap1Source_deriv_le_zero` が
   false-as-framed だったのと**対照的に genuine**)。唯一の残 sorry = plain Stam 抽出
   `h_plain_stam : 1/J_sum ≥ 1/J_X+1/J_Y` (`EPIStamToBridge.lean:892`) に隔離。closure は
   `IsStamInequalityHyp` consumer plumbing 1 本に帰着 (= **density-identification bridge**)。
   起草時の撤退ライン予測 (weighted-λ 核の補題不在) ではなく、consumer 側 density 入力供給が真の
   ボトルネックと判明 (`IsDeBruijnRegularityHyp` が `IsBlachmanConvReady` / `∫=1` / convolution 同定を
   提供しないため)。
6. **(2026-06-01) R-3′ は Mathlib 壁ではなく in-house plumbing と判定 (独立 auditor 一致)**: Stam core
   不等式は `stam_step2_density_wall` で既に genuine 閉 (`@audit:ok`)、残るは 2 predicate 間の density
   射影のみ → `@residual(plan:...)` classification 正当。**追加発見**: in-tree producer
   `isStamInequalityHyp_via_step3` (`EPIStamStep3Body.lean:119`, `@audit:ok` sorryAx-free) が
   `IsStamInequalityHyp X Y P` を `Measurable X/Y` + `IndepFun X Y P` のみから生成する。`EPIStamToBridge`
   は同 module を未 import だが cycle 無し (verbatim 確認) ので import 追加で producer 直呼びルート B が
   開ける可能性 → M0′ でルート A (consumer plumbing) と cost 比較し軽い方を採る。
7. **(2026-06-01 Wave 3, 無編集撤退) R-3′ bridge 案撤退 (L-Ratio-3′-α 発火)、当初「bridge で閉じる」
   前提が誤りと判明**: M0′ verbatim 照合で**ルート A (consumer plumbing) / ルート B (producer 直呼び)
   両方 infeasible** と確定 (実装着手前の構造判定、commit なし)。判断ログ #6 の楽観 (producer 直呼びで
   gap 回避) は誤り — `isStamInequalityHyp_via_step3` / `_via_body` は `IsStamInequalityHyp X Y P` という
   **∀-量化 Prop を返すだけ**で、`1/J_sum ≥ 1/J_X+1/J_Y` を取り出す apply step は producer/consumer 共通。
   apply 時に witness `(J_X J_Y J_sum fX fY fXY)` + 4 系統 antecedent が consumer (R-3) に再浮上。
   **closure 不能な 2 致命傷**: (a) cross-source convolution 同定 = single-source
   `IsDeBruijnRegularityHyp X Z P` structure では path_X/path_Y 独立性を要する convolution が原理的に
   表現不能 + 在house 補題不在 + `IndepFun path_X path_Y P` が R-3 仮説に存在しない。(b) 一般 density
   `IsBlachmanConvReady` producer が Gaussian 専用 (`isBlachmanConvReady_gaussianPDFReal`,
   `EPIBlachmanGaussianWitness.lean:335`) のみ、一般 path density 用 producer 不在 (≈Mathlib 壁級)。
   `IsDeBruijnRegularityHyp` field 追加でも cross-source convolution は救えない (single-source structure)。
   **戦略転換**: `IsStamInequalityHyp` の **witness ∀-量化 結論形が赤フラグ** (CLAUDE.md
   「Mathlib-shape-driven Definitions」の reshaping-bridge 兆候と同型)。本筋は bridge 構築ではなく
   **`IsStamInequalityHyp` の結論形を measure-level 直接形に pivot する def 書換** = R-3″。
   `IsStamInequalityHyp` を参照する全 producer/consumer/defeq pass-through の blast radius 精査を要する
   ため **別 sub-plan に委譲** (slug 案 `epi-stam-predicate-reshape-plan`)。R-3 の `h_plain_stam` は
   `sorry` + `@residual` 据え置き (type-check done、honest)。

# Shannon EPI: case-1 sum closure two-time object 再構成サブ計画

> **Parent**: [`epi-case1-debruijn-producer-plan.md`](epi-case1-debruijn-producer-plan.md) §PB-4 / L-Sum-struct
> **Predecessor (superseded)**: [`epi-case1-debruijn-genvar-struct-plan.md`](epi-case1-debruijn-genvar-struct-plan.md) — ⛔ GS-A3' GATE REFUTED (全 single-t route が variance-2 非対称で blocked)
> **Status**: 📋 着手前 (解析核 arith gate は PASS 済、formulation gate が次 session の最初の probe)
> **Scope**: docs-only (本 plan)。実装 file は per-Phase 節に列挙。
> **proof-log**: yes (`docs/shannon/proof-log-epi-case1-genvar-struct.md` §GS-A3' probe + §Two-time object に機械実証記録済。本 restructure 用の新 proof-log は Phase 1 formulation probe で開始)
> **撤退口 slug**: `@residual(plan:epi-case1-twotime-restructure-plan)`

---

## 進捗

- [x] Phase 0 — formulation Mathlib asset 在庫調査 ✅
- [x] Phase 1 — **formulation 確定 gate** (probe) ✅ **PASS = formulation (b) GO** (2026-06-06、`ProbeF1.lean` EXIT=0、proof-log §Two-time formulation gate)
- [x] Phase 2 — two-time object declaration skeleton ✅ (9 decls、0 errors、2026-06-06。8 honest + `_hasDerivAt` は
  tier-5 `@audit:defect(false-statement)` 残置 = Phase 3 entry gate で J_S pin 解消)
- [x] Phase 3 — **`_hasDerivAt` J_S pin (entry gate) 解消** ✅ + deriv_le_zero arith 結線 ✅ (2026-06-06。
  J_S 直接埋込 body genuine、`#print axioms` sorryAx-free、独立監査 `@audit:ok`。defect 構造的解消)
- [x] Phase 4 — endpoint + antitone + epi_of_* 結線 **9/9 done = 両端封じ完了** (2026-06-06)。
  `matchedTimePath_exists` / `_at_zero` / `_continuousWithinAt_zero` / `_antitoneOn_Ici_zero` / `epi_of_*`×2 /
  `matchedSum_law_eq` / `_hasDerivAt` / **`_tendsto_zero_atTop`** すべて genuine + `@audit:ok` (独立 fresh-subagent
  監査 PASS)。`EPICase1TwoTime.lean` = **0 sorry / 0 @residual / proof-done**、headline `_tendsto_zero_atTop` は
  `#print axioms` sorryAx-free。
  - **§2 saturation core の closure (実装済ルート)**: §1 reduction (`R t = log(A t/B t)`) は既 genuine。§2 は
    単一限論 `A t/eᵗ → N(X)+N(Y)` に帰着して解いた: `matchedSum_law_eq` (@audit:ok) で `A t` を τ=s t+r t の単一-noise
    heat flow に → `entropyPower_path_scaling` で `A t = τ·NSr(τ)` (NSr→ν) → 成分漸近
    `s t/eᵗ → N(X)/ν`, `r t/eᵗ → N(Y)/ν` (matched_growth × scaling × §3 envelope `entropyPower_rescaled_path_tendsto`
    を `s,r→∞` に compose) → 3 noise 共通 ν=N(𝒩(0,1)) が cancel。
  - **signature に追加した regularity** (監査: 全 non-load-bearing): noise `Z`+laws+independences+ac、path 発散
    `hs_atTop/hr_atTop`、path positivity、per-σ scaling regularity `h_scale_*`、squeeze bundle `h_reg_X/Y/S`
    (`IsRescaledPathRegular`)。手本 `csiszarLogRatioGap_tendsto_zero_atTop` と同型の precondition 構成。
- [x] Phase 5 — **terminal `entropyPower_add_ge_case1_of_regular_twotime` 1 本** ✅ (2026-06-06、proof-done
  sorryAx-free、独立 `honesty-auditor` PASS = `@audit:ok`)。J_X/J_Y Fisher-pin pointwise-honest (`density_t_eq`)、
  load-bearing なし (core-reconstruction PASS)、harmonic Stam = `isStamInequalityHyp_via_step3` genuine。副産物:
  `matchedTimePath_exists` を `∃ s, IsMatchedTimePath … ∧ (∀ t>0,0<s t) ∧ Tendsto s atTop atTop` に強化
  (案 2、sorry-free 維持、再監査 PASS)。public-API impact ゼロ確認。
- [ ] Phase 6 — consumer 削除 (`csiszarLogRatioGap` 83 occ / sister `csiszarGap1Source` 74 occ) + `Z_law` defect park 解消 📋

---

## ゴール / Approach

### ゴール

EPI case-1 sum frontier (`X+Y` の entropy power 不等式) を **two-time object** で genuine に閉じる。
現行 single-time object `csiszarLogRatioGap X Y Z_X Z_Y P t` (`EPIL3Integration.lean:1380`) は X と Y を
**同一時刻 t** で摂動するため `s=r=t` を強制し、sum 微分が variance-2 由来の `2·J_sum` になって harmonic
Stam から閉じない (GS-A3' で機械実証 REFUTE、`ProbeGSA3.lean` constructive counterexample)。本 plan は X を
時刻 s、Y を時刻 r で**独立**摂動する two-time object に restructure し、FII-matched path で解析核を
**既存 harmonic Stam から直接**閉じる。

### Approach (全体戦略)

**全体形**: X を時刻 s で `X_s = X + √s·Z_X`、Y を時刻 r で `Y_r = Y + √r·Z_Y` (`Z_X, Z_Y ∼ 𝒩(0,1)` 独立)
で摂動する。gap を 2 変数関数として
`R̂(s,r) = log N(s,r) − log(N_X(s) + N_Y(r))`、`N(s,r) = entropyPower (P.map (X_s + Y_r))` と定義し、
1 次元の単調 object は `R(t) = R̂(s(t), r(t))` を **FII-matched path** `(s(t), r(t))` に沿って取る。

**single-t との差** (核心): single-t は path velocity が `s' = r' = 1` 強制で、sum 項に variance-2 由来の
factor-2 が乗る。two-time は path velocity を `s' = 1/J_X(s)`、`r' = 1/J_Y(r)` に**自由に選べる** (FII-matched)。
この選択で
```
R'(t) = J_S·(s' + r') − (J_X·N_X·s' + J_Y·N_Y·r')/(N_X + N_Y)
      = J_S·(1/J_X + 1/J_Y) − (N_X + N_Y)/(N_X + N_Y)
      = J_S·(1/J_X + 1/J_Y) − 1
```
となり、harmonic Stam `1/J_S ≥ 1/J_X + 1/J_Y` ⟺ `J_S·(1/J_X + 1/J_Y) ≤ 1` (J_S>0) から `R'(t) ≤ 0`。

**解析核 gate は PASS 済** (これは確定、再検証不要): proof-log §Two-time object の probe `twotime_reduced` /
`twotime_full` が `lake env lean` EXIT=0 で機械確認。`twotime_full` が証明したのは consumer lemma が実際に
要求する完全形
`J_S·(1/J_X+1/J_Y) − (J_X·N_X·(1/J_X)+J_Y·N_Y·(1/J_Y))/(N_X+N_Y) ≤ 0` で、weighted 項が
`(N_X+N_Y)/(N_X+N_Y)=1` に collapse して同 Stam で閉じる。**factor-2 も co-monotonicity も新規 wall も不要**。
GS-A3' で REFUTE された single-t と two-time は解析入力 (harmonic Stam) が**同一**で、差は純粋に path
geometry (`s'=r'=1` 強制 vs `s'=1/J_X, r'=1/J_Y` 自由) のみ。

**de Bruijn building block も流用可** (確定): 既存 `deBruijn_identity_v2` (`(1/2)·J` per-variable) はそのまま
使える。各変数 s/r は unit-noise Z_X/Z_Y (variance-1) で摂動されるので `∂/∂s h(X_s+Y_r) = (1/2)·J_S` 等、
factor が健全。variance-2 問題は「sum を単一 noise で見た」 artifact で two-time では発生しない (proof-log
§Two-time object に明記)。

**したがって最大の残 risk は解析核ではなく formulation 選択** (= path `(s(t),r(t))` の Lean 形式化) と
consumer 移行の blast radius。本 plan の中心はこの 2 点。

---

## Phase 0 - formulation Mathlib asset 在庫調査 📋

各 formulation 候補が要求する Mathlib asset の in-tree 有無を **実 grep / loogle で裏取り** (本節は確認済の
結果のみ記載。予測で書かない、CLAUDE.md「数値・型予測の verbatim 確認」)。

- [ ] 候補 (a) raw ODE asset 確認 — **済**: `Mathlib/Analysis/ODE/PicardLindelof.lean` に
  `IsPicardLindelof` structure (`:83`) + `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`
  (`:40` 存在定理) が in-tree。ただし RHS が Fisher info `J_X(s)` であり **Lipschitz 性 (`IsPicardLindelof`
  の `L`/`K` field) を Fisher info に対して立てる asset は不在** (heat-flow 沿いの `J_X` regularity を
  Mathlib で組む手段なし) → 形式化困難の根拠。
- [ ] 候補 (b) entropy-power 再パラメータ化 asset 確認 — **済**: chain rule `HasDerivAt.comp` は Mathlib
  既存。matched path 上で `d(log N_X)/dt = 1` ⟹ `log N_X(s(t)) = log N_X(0) + t` という閉形が `s(t)` を
  陽に解かずに済む (下記 ⭐ 参照)。antitone test `antitoneOn_of_deriv_nonpos` 系は
  `Mathlib/Analysis/Calculus/DerivativeTest.lean` に in-tree (現 single-t 版 `l_antitoneOn_Ici_zero` が
  既に消費)。
- [ ] 候補 (c) 2 変数 region monotonicity asset 確認 — **済**: implicit function theorem
  (`Mathlib/Analysis/Calculus/ImplicitFunction/Bivariate.lean` + `Implicit.lean`) は in-tree。ただし
  quadrant `s,r≥0` 上の 2 変数 `R̂(s,r)` monotonicity を直接使うには「level set に沿う path」を陽に
  構成する必要があり (b) に合流する。region 全体の偏微分単調性だけでは EPI (= 原点での `R̂(0,0)≥0`) に
  直結しない (path が要る)。
- [ ] 候補 (d) Rioul 正規化摂動 asset 確認 — **済**: 正規化摂動は (b) の reparametrization の別表現で、
  追加 Mathlib asset を要求しない。形式化負荷は (b) と同等以上。

**在庫調査の結論 (Phase 0 verdict)**: 候補 (b) が唯一 ODE solver / Lipschitz-Fisher を回避でき、既存
`HasDerivAt.comp` + `DerivativeTest` 資産で閉じる見込み。候補 (a) は `IsPicardLindelof` の Lipschitz field を
Fisher info で立てる asset 不在で **NO-GO 寄り**。詳細比較は次節。

---

## ⭐ formulation を tractable にする鍵 (設計の軸)

matched path 上で `d(log N_X)/dt = J_X·s' = J_X·(1/J_X) = 1`、同様に `d(log N_Y)/dt = 1`。
∴ **両 component entropy power が共に `e^t` で増大**: `N_X(s(t)) = N_X(0)·e^t`、`N_Y(r(t)) = N_Y(0)·e^t`。
これは matched path が **`N_X/N_Y` 比一定の level set** であることを意味する。

この特徴づけが decisive: 1 次元 object の微分を組むのに **path `(s(t),r(t))` を陽に解く必要がない**。
two-time gap を直接 `t` の関数として
```
R(t) = log N(s(t),r(t)) − log(N_X(0)·e^t + N_Y(0)·e^t)
     = log N(s(t),r(t)) − log((N_X(0)+N_Y(0))·e^t)
     = log N(s(t),r(t)) − log(N_X(0)+N_Y(0)) − t
```
と書ける。第 2・第 3 項は `t` の閉形 (定数 − t) で微分自明、残るは `d/dt log N(s(t),r(t))` のみ。これを
de Bruijn (per-variable `(1/2)·J_S`) + chain rule (`s'=1/J_X, r'=1/J_Y`) で
`J_S·(1/J_X + 1/J_Y)` と評価すれば `R'(t) = J_S·(1/J_X+1/J_Y) − 1` が直接出て、ODE 解の存在/一意を
**一切経由しない**。これが候補 (b) を推奨にする根拠。

> **設計上の注意 (formulation gate で機械検証すべき点)**: 上記 `e^t` 閉形は「matched path が存在する」
> ことを前提にする。path velocity `s'=1/J_X(s)` 自体は ODE だが、object の def を `e^t` 閉形
> (`N_X(s(t)) := N_X(0)·e^t` を **定義として課す**) で書けば、ODE 解の存在は `s(t)` を `N_X` の逆関数で
> 陽に与える形に転化できる (`N_X` が `s` の連続単調増加なら `N_X(0)·e^t` を達成する `s(t)` が一意存在)。
> この転化が Lean で genuine に組めるか (= `N_X(s)` の `s`-単調性 + 連続性 + 値域被覆) が formulation gate
> の真の probe 対象。**planner は候補提示まで、確定は次 session の実機械 probe**。

---

## Phase 1 - formulation 確定 gate (probe、次 session の最初) 📋

GS-A3' の risk-ordering 教訓 (plumbing 投資前に解析核 gate) を formulation にも適用する。解析核 gate は
PASS 済なので、次の最大 risk = **path の Lean 形式化が genuine に組めるか**。これを skeleton 投資前に
最小 probe で gate する。

### 候補比較サマリ (Phase 0 在庫を踏まえた優先順位)

| 候補 | path 表現 | 要求 Mathlib asset | in-tree | 判定 |
|---|---|---|---|---|
| **(b) entropy-power 再パラメータ化** ⭐推奨 | `N_X(s(t))=N_X(0)·e^t` 閉形、`s(t)` は `N_X` 逆関数 | `HasDerivAt.comp` + `DerivativeTest` + `N_X(s)` 単調連続性 | ✅ (単調連続性は de Bruijn から導出見込み) | 推奨候補 |
| (a) raw ODE `s'=1/J_X(s)` | Picard-Lindelöf 解 | `IsPicardLindelof` + **Lipschitz-on-Fisher** | △ (structure 有、Lipschitz field 不在) | NO-GO 寄り |
| (c) 2 変数 region monotonicity | quadrant `s,r≥0` 偏微分単調 | implicit function + path 構成 | △ (path で (b) に合流) | (b) に吸収 |
| (d) Rioul 正規化摂動 | 正規化 reparam | (b) と同型 | △ | (b) と同等以上負荷 |

### Phase 1 probe (gate 内容、scratch file で機械検証 → 削除、結果は proof-log)

- [ ] **probe-F1 — `N_X(s)` の `s`-単調連続性**: `s ↦ entropyPower (P.map (X + √s·Z_X))` が `s ∈ Ici 0`
  で連続かつ (狭義) 単調増加であることを既存 de Bruijn 資産 (`csiszarLogRatioGap_hasDerivAt` の per-component
  building block `entropyPower(X_s)·J_X` with `J_X > 0`) から導けるか。これが言えれば `e^t` を達成する
  `s(t)` の一意存在 (逆関数) が `StrictMonoOn.orderIsoOfSurjective` 系で組める。
- [ ] **probe-F2 — 1 次元 object の HasDerivAt**: `R(t) = log N(s(t),r(t)) − log(N_X(0)+N_Y(0)) − t` の
  derivative が `J_S·(1/J_X+1/J_Y) − 1` になることを、`d/dt log N(s(t),r(t))` = `J_S·(s'+r')` (de Bruijn
  per-variable + chain rule) で組めるか。
- [ ] **gate verdict**: probe-F1/F2 が両方 PASS なら formulation (b) 確定 → Phase 2 へ。F1 が NG (単調連続性が
  de Bruijn から出ない) なら候補 (a) Picard-Lindelöf に戻り Lipschitz-Fisher の壁を再評価、それも NG なら
  撤退ライン (下記 L-TT-form) 発火。

### ✅ gate verdict (2026-06-06、機械実証) — **formulation (b) GO、hard wall ゼロ**

`ProbeF1.lean` (scratch、EXIT=0、proof-log §Two-time formulation gate に asset map + verbatim)。
全 required asset を in-tree / Mathlib に**名前確認** (proof-log の表)、最も誤りが隠れやすい逆関数微分 glue
(`of_local_left_inverse` + `comp` で `s'(t)=1/J(s(t))` に相殺) を機械検証 PASS。

**probe で判明した実態 (plan ⭐ の楽観を refine)**:
- `e^t` 閉形が回避できるのは ODE *solver* (Picard-Lindelöf) のみ。matched path の**逆関数構成
  `s(t)=N_X⁻¹(C·e^t)` は依然必要**で、(strictMonoOn ← `J_X>0` を hyp で thread) + (連続 on Ici 0、端点は
  heat-flow CLOSED) + (surjectivity `N_X→∞`、`entropyPower_path_scaling`×`entropyPower_rescaled_path_tendsto`
  で組立) + (連続逆関数 `StrictMonoOn.orderIso`) + (`of_local_left_inverse`) を組む **~200-300 行サブ
  プロジェクト** = Phase 2 の最大塊。**壁ではないが trivial でもない** → Phase 2 sizing をこれに合わせる。
- `0 < fisherInfoOfDensityReal` は in-tree 定理が無く (`_nonneg` のみ)、既存 consumer 同様 `hJX_pos` precondition
  として thread する (genuine regularity、load-bearing でない)。

---

## Phase 2 - two-time object declaration skeleton 📋

実装 file: 新規 `InformationTheory/Shannon/EPICase1TwoTime.lean` (現 single-t 群と並走させ、Phase 5 で
consumer を切替えてから旧 object を削除)。signature のみ列挙、body は別 session (skeleton-driven、各 sorry に
`@residual(plan:epi-case1-twotime-restructure-plan)`)。

- [ ] **TT-path `matchedTimeX` / `matchedTimeY`** (= Phase 1 gate で確定した逆関数サブプロジェクト、Phase 2 の
  最大塊 ~200-300 行) — `s : ℝ → ℝ` with `N_X(s(t)) = N_X(0)·e^t` の構成 + `HasDerivAt s (1/J_X(s(t))) t`。
  ピース: (i) `N_X(s)=entropyPower(P.map(X+√s Z_X))` の `StrictMonoOn (Ici 0)` (`strictMonoOn_of_deriv_pos`
  + 導関数 `N_X·J_X>0`、`J_X>0` は precondition)、(ii) 連続 on Ici 0 (内部 HasDerivAt + 端点 heat-flow CLOSED)、
  (iii) `Tendsto N_X atTop atTop` (`entropyPower_path_scaling`×`entropyPower_rescaled_path_tendsto`)、
  (iv) IVT `intermediate_value_Ici` + `StrictMonoOn.orderIso` で連続逆関数、(v) `HasDerivAt.of_local_left_inverse`
  + `comp` (gate verbatim 移植)。各 sorry に `@residual(plan:epi-case1-twotime-restructure-plan)`。
- [ ] **TT-def `twoTimeLogRatioGap`** — `X Y Z_X Z_Y : Ω → ℝ` (P : Measure Ω) (t : ℝ) : ℝ。formulation (b)
  の `e^t` 閉形か、`s(t)/r(t)` を field に持つ structure かは Phase 1 gate verdict で確定。
  再利用: 現 `csiszarLogRatioGap` def 本体 (`EPIL3Integration.lean:1380`) の `entropyPower (P.map ...)` 構造。
- [ ] **TT-`_at_zero`** — `t=0` で `log(eP(X+Y)) − log(eP X + eP Y)` に reduce (EPI 橋)。再利用: 現
  `csiszarLogRatioGap_at_zero` (`:1391`) を two-time path の `s(0)=r(0)=0` 版に書換。
- [ ] **TT-`_hasDerivAt`** — matched path で `R'(t) = J_S·(1/J_X+1/J_Y) − 1`。再利用: 現
  `csiszarLogRatioGap_hasDerivAt` (`EPIStamToBridge.lean:744`) の per-component de Bruijn building block
  (`entropyPower(X_s)·J_X` 形、L755-766) + chain rule `HasDerivAt.comp` で `s'=1/J_X` を合成。precondition は
  現行の `IsDeBruijnRegularityHyp X Z_X P` / `IsDeBruijnRegularityHyp Y Z_Y P` (sum 側は X_s, Y_r が独立なので
  `h_reg_sum` の取り方が変わる — Phase 1 で確認)。
- [ ] **TT-`_deriv_le_zero`** (= 解析核、gate PASS 済) — `R'(t) ≤ 0`。再利用: proof-log §Two-time object の
  `twotime_full` body を verbatim 移植 (`twotime_reduced` の `mul_le_mul_of_nonneg_left` + `div_self`)。
  harmonic Stam producer `isStamInequalityHyp_via_step3` / `isStamInequalityHyp_via_body`
  (`EPIStamDeBruijnConclusion.lean`、genuine sorryAx-free) を `1/J_S ≥ 1/J_X+1/J_Y` の供給に使う。
  **新規 wall ゼロ**。
- [ ] **TT-`_antitoneOn_Ici_zero`** — `AntitoneOn (Set.Ici 0)`。再利用: 現 `l_antitoneOn_Ici_zero`
  (`EPIStamToBridge.lean:1085`) の `antitoneOn_of_deriv_nonpos` パターン + 端点連続性
  (`csiszarLogRatioGap_continuousWithinAt_zero`、下記 endpoint 流用)。
- [ ] **TT-`_at_one_eq_zero` / `_tendsto_zero_atTop`** — Gaussian 飽和端点。再利用: 現
  `csiszarLogRatioGap_at_one_eq_zero` (`EPIL3Integration.lean:1426`、`entropyPower_gaussian_additivity` 経由)
  + `l_tendsto_zero_atTop` (`EPICase1RatioLimit.lean`)。two-time path では `s,r→∞` で X_s, Y_r が共に
  Gaussian に収束する点を確認 (matched path の `e^t→∞` 端点)。
- [ ] **TT-`epi_of_*`** — `R(0) ≥ 0 ⟹ EPI`。再利用: 現 `epi_of_l_zero_nonneg` (`EPIStamToBridge.lean:985`)
  + `epi_of_l_tendsto` (`EPICase1RatioLimit.lean`) の order-limit bridge。

---

## Phase 3 - deriv_le_zero arith core 結線 + **`_hasDerivAt` J_S pin 設計 (最優先 entry gate)** 📋

解析核 arith gate は PASS 済 (proof-log §Two-time object)。ただし Phase 2 skeleton の独立 honesty 監査 (2-pass)
で `twoTimeLogRatioGap_hasDerivAt` が **tier-5 `@audit:defect(false-statement)`** と判明 (`J_S` の a.e.-pin が
representative-dependent な `fisherInfoOfDensityReal` に不十分、skeptic が non-differentiable representative で
`J_S=0` に落とせる)。**Phase 3 の最初 = この J_S pin を proper に解消する設計**。

### ⭐ Phase 3 entry design gate — `_hasDerivAt` の J_S pointwise-smooth pin

**key insight (2026-06-06、defect 解消の決定的 lead)**: 単一時刻 `t` で matched sum
`X_{s t}+Y_{r t} = (X+Y) + (√(s t)·Z_X + √(r t)·Z_Y)`、noise `√(s t)·Z_X + √(r t)·Z_Y` の law は
`𝒩(0, s t + r t)` で `X+Y` と独立 → matched-sum law = `(X+Y) + √τ·Z` (τ = s t + r t、Z unit Gaussian) の law
= **`X+Y` の単一-noise heat-flow at time τ**。∴ `J_S` を free 変数にせず、既存 `IsDeBruijnRegularityHyp
(fun ω => X ω + Y ω) Z P` を τ で評価して **結論に直接埋込**: `J_S :=
fisherInfoOfDensityReal ((h_reg_sum.reg_at (s t + r t) hτ).density_t)`。`density_t_eq` が smooth conv-
representative の pointwise pin を供給 (a.e. でなく pointwise) → representative escape が構造的に消える
(honest single-t 版 `csiszarLogRatioGap_hasDerivAt` と同一機構)。**新規 regularity 抽象は不要**。

- [x] **3-0a (entry gate)** ✅ (2026-06-06): `_hasDerivAt` rewrite 済 — free `J_S`/`d_S`/`hd_S`/`hJS_eq` 削除、
  `h_reg_sum : IsDeBruijnRegularityHyp (X+Y) Z P` (Z unit + law/indep/meas) + `hτ` thread、結論 J_S を
  `fisherInfoOfDensityReal ((h_reg_sum.reg_at (s t+r t) hτ).density_t)` 直接埋込。X/Y pin 維持。
- [x] **3-0b** ✅ (2026-06-06): `matchedSum_law_eq` を **genuine closure** (sorryAx-free `[propext, Classical.choice,
  Quot.sound]`)。`gaussianReal_map_const_mul` + `gaussianReal_add_gaussianReal_of_indepFun` +
  `IndepFun.map_add_eq_map_conv_map` で両辺を `(P.map (X+Y)) ∗ 𝒩(0,s+r)` に分解。独立性仮説を joint-pair
  `IndepFun (X+Y) (Z_X,Z_Y)` に honest 強化 (scaled noise の独立に必要)。
- [x] **3-0c (再監査)** ✅ (2026-06-06、3-pass): fresh `honesty-auditor` PASS — J_S escape 構造的解消確認
  (conv-pin 直接埋込 = X/Y と同一機構)、`matchedSum_law_eq` true math fact、bundling/under-hyp なし。
  `@audit:defect` 除去済。**Phase 3 entry gate CLOSED**。
- [ ] proof-log の `twotime_full` body を `TT-_deriv_le_zero` に移植 (arith は PASS 済)。
- [ ] harmonic Stam の供給を `isStamInequalityHyp_via_step3` から取る (matched-sum `(X+Y)+√τ·Z` 用の Stam
  instance、unit-noise heat-flow なので Stam 前提 `IndepFun` が満たされることを確認)。
- [ ] `TT-_hasDerivAt` (pin 済) と結合して `deriv R t ≤ 0` を出す。

proof-log: yes (§Two-time formulation gate / 新 §Two-time honesty audit に結線結果を記録)。

---

## Phase 4 - endpoint + antitone + epi_of_* 結線 📋

- [ ] 端点連続性: `IsHeatFlowEndpointRegular` (`EPIG2HeatFlowContinuity.lean:488`、全 field regularity の
  precondition structure) が two-time の各 component (X_s, Y_r) の `s,r→0⁺` 端点に流用できることを確認。
  現 single-t 版 `heatFlowEntropyPower_continuousWithinAt_zero` (CLOSED 2026-06-05、genuine) を 2 instance
  (X 側 / Y 側) で適用。sum 側 N(s,r) の端点は X_s+Y_r が `s,r→0` で X+Y に収束する点。
- [ ] `TT-_antitoneOn_Ici_zero` + `TT-_tendsto_zero_atTop` を `epi_of_*` order-limit bridge に結線。
- [ ] 最終 EPI 結論が現 `entropy_power_inequality` 主定理 (`EntropyPowerInequality.lean` の `ln`、
  `EPIPlumbing.lean` 経由) に届くことを確認。

---

## Phase 5 - terminal `entropyPower_add_ge_case1_of_regular_twotime` (1 本) 📋

実装 file: `InformationTheory/Shannon/EPICase1TwoTime.lean` (末尾、`epi_of_twoTimeLogRatioGap_tendsto`
の直後に追加)。

### 再 framing (本 session の reconnaissance で確定、当初の「consumer 移行」枠を狭める)

**Phase 5 の直接成果物は新規定理 1 本** = `entropyPower_add_ge_case1_of_regular_twotime`、single-t terminal
`entropyPower_add_ge_case1_of_regular` (`EPICase1RatioLimit.lean:1343`) の two-time 版。**同一結論**
`entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)` を、**genuine な two-time
pillar 群**から組み立てる (single-t の GS-A3' variance-2 blockage を回避、honest harmonic Stam から閉じる)。

- **public-API impact ゼロ**: headline `entropy_power_inequality` (`EntropyPowerInequality.lean:289`) は EPI を
  `stamToEPIBridge_holds X Y P h_stam` 経由で出し (Stam-residual wall = 別 plan `epi-stam-to-conclusion-plan`)、
  `csiszarLogRatioGap` を一切参照しない。よって Phase 5 は headline に届かない self-contained な case-1 EPI 端点を
  two-time 化するだけ。
- **`csiszarLogRatioGap` 83 occ / sister `csiszarGap1Source` 74 occ の移行は Phase 5 ではなく Phase 6 の
  eventual deletion scope** (本定理が single-t terminal を置換できることを確認した後)。Phase 5 は新定理を書いて
  `lake env lean` 0 errors + `#print axioms` sorryAx-free を達成するところまで。

### Approach (本定理の組立形)

3 つの genuine two-time pillar (全て `@audit:ok`、`EPICase1TwoTime.lean` 内で proof-done) を seam に流し込む:

- **Pillar A (seam)** `epi_of_twoTimeLogRatioGap_tendsto` (`:1493`): `h_anti` + `h_lim` → EPI。
- **Pillar B (h_anti)** `twoTimeLogRatioGap_antitoneOn_Ici_zero` (`:1083`): `AntitoneOn (Set.Ici 0)`。
- **Pillar C (h_lim)** `twoTimeLogRatioGap_tendsto_zero_atTop` (`:1228`): `Tendsto … atTop (nhds 0)`。

path producer **`matchedTimePath_exists`** (`:425`、genuine no-sorry) で matched path `s` (X 側) / `r` (Y 側) を
構成し、pillar の `{J_X J_Y}` implicit binder に **同じ** `J_X`/`J_Y` を渡す (= matchedTimePath に渡した `J_A`)。
body は (1) `s` 構成 → (2) `r` 構成 → (3) path 発散/正値 導出 → (4) Pillar B で `h_anti` → (5) Pillar C で
`h_lim` → (6) `exact epi_of_twoTimeLogRatioGap_tendsto …`。

### (c) J_X / J_Y Fisher-pin 機構 (honesty-load-bearing — goal でなく mechanism を渡す)

**`J_X` / `J_Y` は free 変数でなく `fisherInfoOfDensityReal (density_t)` に固定する** (CLAUDE.md brief checklist
項目 4)。a.e.-pin は false-as-framed (skeptic が non-smooth representative で `J=0` に落とす) なので
**pointwise-smooth pin のみ honest**。供給機構は実コード verbatim 確認済 (予測でない):

| 役割 | 供給 lemma (`file:line`) | 結論 verbatim |
|---|---|---|
| de Bruijn HasDerivAt (entropy 側) | `deBruijn_identity_v2` (`FisherInfoV2DeBruijnGenuine.lean:51`) | `HasDerivAt (fun s => differentialEntropy (P.map (gaussianConvolution X Z s))) ((1/2)·fisherInfoOfDensityReal h_reg.density_t) t` |
| entropy → entropy-power lift | `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` (`EPIStamToBridge.lean:461`) | `HasDerivAt (fun s => entropyPower (P.map (gaussianConvolution X Z s))) (entropyPower(…)·(2·(1/2)·J)) t` |
| density pointwise pin | `IsDeBruijnRegularityHyp.density_t_eq` (`EPIStamDischarge.lean:273`) | `∀ t ht, (reg_at t ht).density_t = density_path t` (a.e. でなく `∀ x` pointwise) |

**決定的事実 (mechanism、機械確認済)**: 同一の量

```
J_A(s) := fisherInfoOfDensityReal ((h_reg_A.reg_at s hs).density_t)
```

が **両方** を供給する:

- **(a) `matchedTimePath_exists` の `hJ_deriv`**: `HasDerivAt (fun u => heatFlowEP A B P u)
  (heatFlowEP A B P s · J_A s) s`。`heatFlowEP A B P s = entropyPower (P.map (gaussianConvolution A B s))`
  (∵ `gaussianConvolution A B s = fun ω => A ω + √s·B ω`、`FisherInfoV2DeBruijn.lean:127`、definitional)
  なので、`deBruijn_identity_v2` → `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` で出る (`EPICase1TwoTime.lean:787-805`
  の `h_log_sum` ブロックが sum 側で**既にこの組立を verbatim 実証済**、X/Y 側は同型で base を差し替えるだけ)。
- **(b) Pillar B の `h_per_t` Fisher pin**: `J_X (s t) = fisherInfoOfDensityReal ((h_reg_X.reg_at (s t) hst).density_t)`。
  これは (a) と**同じ `fisherInfoOfDensityReal (density_t)` 量**なので、`J_X := fun σ => fisherInfoOfDensityReal
  ((h_reg_X.reg_at σ _).density_t)` と取れば `hJX_eq` は `rfl` 近傍で閉じる (positivity dependent な `σ>0`
  argument の扱いだけ整える)。`density_t_eq` が `∀ x` pointwise pin を供給するので representative escape は
  構造的に消える (single-t honest 版 `csiszarLogRatioGap_hasDerivAt` と同一機構、`twoTimeLogRatioGap_hasDerivAt`
  L686-708 docstring に同機構が明記)。

**implementer への指示はこの mechanism を front-load する** ("J_X を honest 化せよ" の goal で投げない):
(i) in-tree honest sibling = `twoTimeLogRatioGap_hasDerivAt` (`EPICase1TwoTime.lean:727`) の `J_X`/`J_Y`/`J_S`
pin、(ii)「`J_A := fun σ => fisherInfoOfDensityReal ((h_reg_A.reg_at σ hσ).density_t)` を直接埋込、free 変数を
作らない」、(iii)「a.e.-pin は不十分、`density_t_eq` の pointwise pin のみ honest」の 3 点を転写する。

> **⚠ open risk R-5a (probe 必須)**: `J_A` を `σ` の全域関数として定義する際、`fisherInfoOfDensityReal
> ((h_reg_A.reg_at σ hσ).density_t)` は `hσ : 0 < σ` を引数に取る (`reg_at : ∀ t, 0 < t → …`)。`J_A : ℝ → ℝ`
> は全域なので `σ ≤ 0` の分岐 (`if 0 < σ then … else 0` 等) が要る。matchedTimePath / pillar はいずれも `J_A` を
> `s t > 0` / `r t > 0` でのみ評価するので分岐値は無害だが、`hJ_deriv`/`hJX_eq` の `rfl` が `if` を挟むと崩れる
> 可能性がある。**Phase 5 着手の最初に `J_A` の well-typed 定義 + `hJX_eq` 閉じを 5-10 行 probe で確認**
> (`twoTimeLogRatioGap_hasDerivAt` は `J_X` を implicit `{J_X : ℝ → ℝ}` で受け取り `hJX_eq` を hyp で thread
> しているので、terminal 側では `J_X` を**具体定義**して `hJX_eq` を `rfl`/`dif_pos` で discharge する必要が
> ある — ここが pin の実装上の唯一の非自明点)。

### (d) path property: 導出 vs threading

Pillar / path-producer が要求する path 系前提の供給元 (verbatim 確認済):

| 前提 | 要求元 | 導出可能か | 供給法 |
|---|---|---|---|
| `IsMatchedTimePath X Z_X P J_X s` | Pillar A/B/C 全部 | — | `matchedTimePath_exists` の `∃ s, …` を `obtain` |
| `h_pos : ∀ t>0, 0 < s t ∧ 0 < r t` (Pillar B) / `hs_pos`/`hr_pos` (Pillar C) | B, C | **導出**: matched path の `matched_growth` (`N_A(s t)=N_A(0)·eᵗ`、`eᵗ>1` for `t>0`) + `N_A` strict-mono ⟹ `s t > s 0 = 0` | `IsMatchedTimePath` は strict-mono を**露出しない** (fields = `start_zero`/`matched_growth`/`cont`/`deriv_at`)。matched_growth 単独からは `N_A(s t) > N_A(0)` まで (値の大小) しか出ず、`s t > 0` は `N_A` 単射性が要る。→ **小 helper を新規に書く** (下記 R-5b) か `matchedTimePath_exists` の戻りを `∃ s, IsMatchedTimePath … ∧ (∀ t>0, 0<s t)` に強化 |
| `hs_atTop`/`hr_atTop : Tendsto s atTop atTop` (Pillar C) | C | **導出**: `N_A(s t)=N_A(0)·eᵗ→∞` + `N_A` 上界連続 ⟹ `s t→∞` | 同上、`IsMatchedTimePath` 露出フィールド外。helper or 戻り強化が要る (R-5b) |
| `hJ_deriv` (matchedTimePath_exists) | path producer | — | 上記 (c) の de Bruijn 組立 (X/Y base) |
| `hN_tendsto : Tendsto (heatFlowEP A B P) atTop atTop` (matchedTimePath_exists) | path producer | **導出**: `entropyPower_path_scaling × entropyPower_rescaled_path_tendsto` (`matchedTimePath_exists` docstring L392-398 に組立記載) | terminal で組み立てて thread |

> **⚠ open risk R-5b (設計判断 + probe)**: `h_pos`/`hs_atTop`/`hr_atTop` は path の**真の性質**だが
> `IsMatchedTimePath` 構造が strict-mono / surjectivity を露出しないため、`matched_growth` フィールド単独からは
> 直接出ない。2 案: **(案 1)** terminal 内で小 helper `matchedTimePath_pos` / `matchedTimePath_atTop` を書く
> (`N_A` strict-mono を再証明する必要があり、これは `matchedTimePath_exists` の private (i) を再実行 = 重複)。
> **(案 2)** `matchedTimePath_exists` の結論を `∃ s, IsMatchedTimePath A B P J_A s ∧ (∀ t, 0<t→0<s t) ∧
> Tendsto s atTop atTop` に**強化** (内部で既に strict-mono `g`/`hN_mono` を持っているので追加コストは数十行、
> §1 を touch する)。**案 2 推奨** (重複を避け、性質を構成元に集約)。これは Phase 5 着手時の最初の設計判断。
> 案 2 を取る場合 `matchedTimePath_exists` の `@audit:ok` 再監査が要る (signature 変更 = honesty 関連 re-audit
> 起動条件、CLAUDE.md「Independent honesty audit」)。

### (b) 新定理の precondition 表 (full signature)

`matchedTimePath_exists` (X 側 / Y 側) + Pillar B + Pillar C の union を取った precondition。各前提は
**genuine-regularity** (load-bearing なし — 結論 EPI を encode する前提はゼロ、見つけたら flag)。Pillar 別
verbatim 型は本 plan の Approach 直上 (呼出元 brief) + 実コード (`EPICase1TwoTime.lean:1083/1228/1493`、
`:425`) を SoT とする。重複前提 (両 pillar 共通の `hX`/`hZX_law` 等) は 1 回供給して使い回す。

| # | hypothesis (型) | 消費する pillar / producer | 種別 |
|---|---|---|---|
| 1 | `[IsProbabilityMeasure P]` | B, C, path-producer | precondition |
| 2 | `hX hY hZX hZY hZ : Measurable …` | B, C, path-producer | regularity |
| 3 | `hXZX : IndepFun X Z_X P` / `hYZY : IndepFun Y Z_Y P` | path-producer (X/Y), B | regularity |
| 4 | `hZX_law hZY_law hZ_law : P.map · = gaussianReal 0 1` | B, C | regularity (unit-noise law) |
| 5 | `hXYZ : IndepFun (X+Y) Z P` | B (`h_log_sum` de Bruijn) | regularity |
| 6 | `hXY_ZXZY_pair : IndepFun (X+Y) (Z_X,Z_Y) P` | B, C (matched-sum law) | regularity |
| 7 | `hZX_ZY : IndepFun Z_X Z_Y P` | B, C | regularity |
| 8 | `hZX_ac hZY_ac hZ_ac : P.map · ≪ volume` | C | regularity |
| 9 | `h_reg_X h_reg_Y h_reg_sum : IsDeBruijnRegularityHyp …` | B, path-producer (`hJ_deriv` 構成), J pin | regularity bundle |
| 10 | `h_endpt_X h_endpt_Y h_endpt_sum : IsHeatFlowEndpointRegular …` | path-producer (X/Y 端点連続性) + B (`h_endpt_sum`) | regularity bundle |
| 11 | `h_per_t` harmonic-Stam bundle (Pillar B 形、`J_X`/`J_Y` density-pin + positivity + `1/J_S ≥ 1/J_X+1/J_Y`) | B | regularity 供給 (harmonic Stam は `isStamInequalityHyp_via_step3` genuine から、bundling でない) |
| 12 | `h_scale_X h_scale_Y h_scale_sum` (per-σ ac+integrable bundle) | C (`entropyPower_path_scaling`) | regularity bundle |
| 13 | `varX varY varS : ℝ` + `h_varX_nn …` + `h_reg_X/Y/S : IsRescaledPathRegular · · P var· 1` | C (squeeze) | regularity bundle |

**load-bearing チェック**: 結論 `N(X+Y) ≥ N(X)+N(Y)` も `R'(t)≤0` も `A/B→1` も**どの前提にも encode されない**
(single-t terminal `entropyPower_add_ge_case1_of_regular` が `@audit:ok` で同型の union を持つことが先例、
`EPICase1RatioLimit.lean:1336-1342` の非 load-bearing 監査記録を参照)。`h_per_t` の harmonic Stam も genuine
producer 由来であり predicate bundling でない。**flag 対象ゼロ** の見込み。

### (e) body 手順 (ordered steps)

1. **`s` 構成**: `obtain ⟨s, h_path_X⟩ := matchedTimePath_exists X Z_X P J_X hX hZX hXZX hJX_pos hJ_deriv_X
   h_endpt_X hN_tendsto_X`。`J_X := fun σ => fisherInfoOfDensityReal ((h_reg_X.reg_at σ _).density_t)` (R-5a 形)、
   `hJ_deriv_X` = (c) の de Bruijn 組立 (X base)、`hN_tendsto_X` = `entropyPower_path_scaling ×
   entropyPower_rescaled_path_tendsto` (path-producer docstring 記載の組立)。
2. **`r` 構成**: 同型で Y / Z_Y 側。
3. **path 発散/正値**: R-5b の案 2 を取ったなら `matchedTimePath_exists` 強化戻りから `hs_pos`/`hr_pos`/
   `hs_atTop`/`hr_atTop` を `obtain`。案 1 なら helper を呼ぶ。`h_pos := fun t ht => ⟨hs_pos t ht, hr_pos t ht⟩`。
4. **`h_anti` (Pillar B)**: `twoTimeLogRatioGap_antitoneOn_Ici_zero X Y Z_X Z_Y Z P hX hZX hXZX hY hZY hYZY hZ
   hZ_law hXYZ hZX_law hZY_law hXY_ZXZY_pair hZX_ZY h_path_X h_path_Y h_reg_X h_reg_Y h_reg_sum h_endpt_sum
   h_pos h_per_t`。`h_per_t` の各成分は (c) の `J_X`/`J_Y` 定義から `hJX_eq`/`hJY_eq` が `rfl`-近傍、`J_S` positivity
   は `fisherInfoOfDensityReal_pos` 系 / precondition、harmonic Stam は `isStamInequalityHyp_via_step3`。
5. **`h_lim` (Pillar C)**: `twoTimeLogRatioGap_tendsto_zero_atTop X Y Z_X Z_Y P h_path_X h_path_Y Z hX hY hZX hZY
   hZ hZX_law hZY_law hZ_law hXY_ZXZY_pair hXY_Z hZX_ZY hZX_ac hZY_ac hZ_ac hs_atTop hr_atTop hs_pos hr_pos
   h_scale_X h_scale_Y h_scale_sum varX varY varS h_varX_nn h_varY_nn h_varS_nn h_reg_X h_reg_Y h_reg_S`。
6. **seam**: `exact epi_of_twoTimeLogRatioGap_tendsto X Y Z_X Z_Y P h_path_X h_path_Y h_anti h_lim`。

> **obligation mismatch 注意 (step 1/4/5)**: `matchedTimePath_exists` が返す `IsMatchedTimePath … J_X s` の `J_X`
> implicit と、Pillar B/C の `{J_X J_Y}` implicit binder は **同一 `J_X` で unify されねばならない** (path に
> 渡した `J_A` = pillar が pin する `J_X`)。step 1 で `J_X` を具体定義してから両方に渡すことで保証する。
> mismatch すると Pillar B の `hJX_eq : J_X (s t) = fisherInfoOfDensityReal …` が型不一致になる (LSP 第 1 戻りで
> 検出可能)。

### (f) Phase 5 着手前の probe (full 実装前に gate)

- **probe-5a (R-5a)**: `J_X` の well-typed 全域定義 (`if 0 < σ then fisherInfoOfDensityReal ((h_reg_X.reg_at σ
  ‹0<σ›).density_t) else 0` 等) + `hJX_eq` が `s t > 0` 仮定下で `dif_pos`/`rfl` で閉じることを 5-10 行で確認。
- **probe-5b (R-5b)**: `h_pos`/`hs_atTop` を `IsMatchedTimePath` の露出フィールドだけから出せるか確認 → 出ないと
  確定したら案 2 (`matchedTimePath_exists` 戻り強化) の signature を決め、§1 touch の re-audit 要否を判断。
- 両 probe PASS で full body 実装着手。NG なら撤退ライン (下記 L-TT-pin / L-TT-pathprop、Phase 5 用に追記)。

---

## Phase 6 - consumer 削除 (single-t terminal 退役) + sister 削除 + Z_law defect park 解消 📋

> **Phase 5 で確定する前提**: terminal `entropyPower_add_ge_case1_of_regular_twotime` が single-t terminal
> `entropyPower_add_ge_case1_of_regular` (`EPICase1RatioLimit.lean:1343`) を置換できる (= 同一結論を genuine な
> two-time pillar から出す) ことが Phase 5 で機械確認されたら、Phase 6 で single-t object 群 (`csiszarLogRatioGap`
> 83 occ / 4 file、sister `csiszarGap1Source` 74 occ / 3 file) を削除する。本 Phase が **83-occ migration の
> eventual deletion scope** (Phase 5 ではない)。public-API headline は `csiszarLogRatioGap` 非依存なので削除の
> blast は self-contained case-1 端点に局在する。

### single-t `csiszarLogRatioGap` 群 (83 occ / 4 file) の退役

`csiszarLogRatioGap` (alias `l`、`EPIL3Integration` namespace 内 open、**実 grep 確定: 83 occ / 4 file**):

| file | `csiszarLogRatioGap` occ | 役割 |
|---|---|---|
| `InformationTheory/Shannon/EPIStamToBridge.lean` | 40 | hasDerivAt / deriv_le_zero / antitone / epi_of_* / continuousWithinAt |
| `InformationTheory/Shannon/EPICase1RatioLimit.lean` | 31 | tendsto + EPI 最終組立 (epi_of_l_tendsto 系) + terminal |
| `InformationTheory/Shannon/EPIL3Integration.lean` | 7 | def 本体 + `_at_zero` / `_at_one_eq_zero` 端点 |
| `InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean` | 5 | 端点連続性 docstring 言及 + continuousOn 結線 |
| **計** | **83** | (4 file) |

- [ ] live consumer 確認: `entropyPower_add_ge_case1_of_regular` (single-t terminal) を呼ぶ live consumer が
  ゼロ (= two-time terminal に切替済 or もともと headline 非依存) であることを実 grep で裏取りしてから削除。
- [ ] 削除 or `@audit:superseded-by(epi-case1-twotime-restructure-plan)` bookkeeping 格下げ。`_at_zero` 等の
  端点 lemma が two-time 版で同名再利用できる構造なら def 差替えで温存する手もある (signature 同型性は Phase 2 で
  確認済 — two-time は別 def `twoTimeLogRatioGap` なので基本は削除が clean)。

### sister `csiszarGap1Source` (差分版、dead) の削除

`csiszarGap1Source` は **実 grep 確定: 74 occ / 3 file** の difference-version sister。現状すでに
`csiszarGap1Source_deriv_le_zero` が `@audit:defect(false-statement)` (差分形 gap derivative が plain Stam
から出ない false-as-framed) で、ratio 版 `csiszarLogRatioGap` がこれを置換した経緯がある。two-time restructure
完了後は ratio 版自体も two-time に置換されるので、dead な difference 版は削除候補。

| file | `csiszarGap1Source` occ |
|---|---|
| `InformationTheory/Shannon/EPIStamToBridge.lean` | 45 |
| `InformationTheory/Shannon/EPIL3Integration.lean` | 27 |
| `InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean` | 2 |
| **計** | **74** (3 file) |

- [ ] difference 版 `csiszarGap1Source` 群 (def + `_deriv_le_zero` defect + 関連 lemma) を削除。consumer が
  ratio 版経由のみであることを確認してから (live consumer ゼロを実 grep で裏取り)。

### `Z_law` defect park の解消 (two-time で不要化)

sum producer `EPICase1SumProducer.lean` の `Z_law` field defect park
(`@audit:defect(false-statement)`、`EPICase1SumProducer.lean:166`) は **single-t object が sum を
単一 noise `Z_X+Z_Y` (variance-2) で見る**ことに起因する。`IsRegularDeBruijnHypV2.Z_law` が
`gaussianReal 0 1` (unit) を hardcode する一方、`Z_X+Z_Y` の law は `gaussianReal 0 2` で `1≠2`
(`gaussianReal_ext_iff` で機械確認済、proof-log §Z_law) なので uninhabitable。

**two-time restructure はこの defect を構造的に不要化する**: two-time は sum N(s,r) を X_s+Y_r で見て、
`∂/∂s` は Z_X 追加 (variance-1)、`∂/∂r` は Z_Y 追加 (variance-1) と**別々に**摂動するので、各 partial が
unit-noise の de Bruijn `(1/2)·J_S` で health。variance-2 を見る場面が発生しないので `Z_law` の
`gaussianReal 0 2` 矛盾が消える。

- [ ] **park 解消の段取り**: two-time object 結線完了 (Phase 4) 後、sum producer の `Z_law` defect park が
  consumer から外れることを確認。旧 sum producer (`EPICase1SumProducer.lean`) が two-time 経路で参照されなく
  なったら、`@audit:defect(false-statement)` declaration を削除 (または `@audit:superseded-by` で
  two-time object を指す bookkeeping に格下げ)。
- [ ] 関連 plan の status 更新: `epi-case1-sum-producer-plan.md` / `epi-case1-debruijn-genvar-struct-plan.md`
  に「two-time restructure で sum frontier closure、Z_law park は構造的に不要化」を判断ログ追記。

---

## 撤退ライン

honest park の段取り (sorry + `@residual`、signature は本来形保持)。`*Hypothesis` predicate に核を
bundling する撤退は**禁止** (CLAUDE.md「検証の誠実性」)。

- **L-TT-form (formulation gate 全候補 NG)**: Phase 1 probe-F1 (`N_X(s)` 単調連続性) が de Bruijn から
  出ず、かつ候補 (a) Picard-Lindelöf の Lipschitz-Fisher 壁も超えられない場合。**この時点では skeleton 投資
  ゼロ** (gate を skeleton 前に置く設計のため)。撤退 = two-time object を導入せず、現 single-t object の
  `csiszarLogRatioGap_deriv_le_zero` を `sorry` + `@residual(wall:<新規 wall name>)` で park し
  (`<新規 wall name>` は「two-time path formalization」系を register 追加)、sum frontier を「解析核は閉じる
  が path 形式化が Mathlib 壁」として正直に文書化。GS-A3' の旧 plan が放置した「単一-t では原理的に閉じない」
  状態より一歩進む (= 解析核 PASS は確定したので、残壁は path 形式化に局在化)。
- **L-TT-blast (consumer 移行が想定大幅超過)**: Phase 5 で 83 occ の移行が想定 (4 file 局在) を大幅に
  超える依存 (例: `EntropyPowerInequality.ln` 主定理側まで signature 変更が波及) が判明した場合。撤退 =
  two-time object と single-t object を**並走**させ (新 file で two-time を完成、旧 consumer は段階移行)、
  完全切替を後続 plan `@residual(plan:epi-case1-twotime-consumer-migration-plan)` に分離。解析核 + 新 object
  自体は完成させた上で、consumer 切替だけ別 wave 化する (= proof done は新 object 側で達成、旧 object 削除は
  bookkeeping)。
- **L-TT-pin (Phase 5 probe-5a NG)**: terminal で `J_X`/`J_Y` を具体定義して `hJX_eq`/`hJY_eq` を閉じる際、
  `reg_at` の `0 < σ` 引数依存 (`if`-分岐) が `rfl`/`dif_pos` で discharge できず pin が組めない場合。撤退 =
  terminal `entropyPower_add_ge_case1_of_regular_twotime` の body を `sorry` + `@residual(plan:epi-case1-twotime-restructure-plan)`
  で残し、signature (結論 `N(X+Y) ≥ N(X)+N(Y)` + precondition 表) は本来形を保持する。**禁止**: `J_X`/`J_Y` を
  free `{J_X J_Y}` のまま結論側に漏らして a.e.-pin に退化させる (false-as-framed、pillar B が要求する pointwise
  pin を満たさない)。pin は実装上の唯一の非自明点なので、撤退時もここを sorry で正直に park する。
- **L-TT-pathprop (Phase 5 probe-5b で案 2 が大波及)**: `matchedTimePath_exists` 戻り強化 (案 2) が §1 の
  `@audit:ok` 群に想定外の波及をして re-audit が大規模化した場合。撤退 = 案 1 (terminal 内 helper で `N_A`
  strict-mono 再証明) に倒すか、`h_pos`/`hs_atTop`/`hr_atTop` を terminal の precondition として**新規 thread**
  する (genuine path 性質なので precondition 化は honest、load-bearing でない)。pillar 結論を bundling する撤退
  ではないので signature 規律違反にならない。
- **撤退時の signature 規律**: いずれの撤退でも terminal の結論型 (`N(X+Y) ≥ N(X)+N(Y)`) は本来形を保持し、
  body を `sorry` で残す。harmonic Stam / EPI 結論を仮説に bundling して `sorry` を消す
  (`IsTwoTimeStamHypothesis` / `IsTwoTimeEPIHypothesis` predicate 等) のは禁止。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **本 plan の起点 (2026-06-06)**: predecessor `epi-case1-debruijn-genvar-struct-plan.md` が GS-A3' GATE
   で REFUTED (全 single-t route が variance-2 非対称で blocked、`ProbeGSA3.lean` constructive counterexample)。
   user 判断で two-time restructure に着手決定。着手前に解析核 arith gate を機械実証 → PASS
   (proof-log §Two-time object、`twotime_reduced`/`twotime_full`、`lake env lean` EXIT=0)。本 plan は
   その PASS を foundation とし、残 risk を formulation 選択 + consumer 移行に局在化する。
2. **formulation 推奨 = 候補 (b) entropy-power 再パラメータ化 (Phase 0 在庫の結論)**: matched path の `e^t`
   特徴づけ (両 component が `N_i(0)·e^t`) を使えば ODE 解の存在/一意 (`IsPicardLindelof` の Lipschitz-Fisher
   壁) を回避でき、既存 `HasDerivAt.comp` + `DerivativeTest` 資産で閉じる見込み。候補 (a) は
   `IsPicardLindelof` structure は in-tree だが Lipschitz field を Fisher info に立てる asset 不在で NO-GO 寄り。
   **確定は次 session の Phase 1 probe (実機械)** — planner は候補提示まで。
3. **occ 確定 (実 grep)**: `csiszarLogRatioGap` = 83 occ / 4 file (EPIStamToBridge 40 / EPICase1RatioLimit 31
   / EPIL3Integration 7 / EPIG2HeatFlowContinuity 5)。`csiszarGap1Source` (difference 版 sister、dead) = 74 occ
   / 3 file (EPIStamToBridge 45 / EPIL3Integration 27 / EPIG2HeatFlowContinuity 2)。記憶でなく実値。
4. **Phase 5 再 framing (2026-06-06、reconnaissance 確定 + 実コード verbatim 確認)**: 当初「consumer 移行
   (83 occ)」枠だった Phase 5 を **terminal 定理 1 本 (`entropyPower_add_ge_case1_of_regular_twotime`)** に狭めた。
   根拠 3 点を実コード verbatim で確認: (a) headline `entropy_power_inequality` (`EntropyPowerInequality.lean:289`)
   は `stamToEPIBridge_holds` 経由で EPI を出し `csiszarLogRatioGap` 非参照 → Phase 5 は public-API impact ゼロ、
   (b) single-t terminal `entropyPower_add_ge_case1_of_regular` (`EPICase1RatioLimit.lean:1343`) が 3 pillar +
   seam で組まれており two-time 版は同型で組める、(c) 3 つの two-time pillar (`twoTimeLogRatioGap_antitoneOn_Ici_zero`
   `:1083` / `_tendsto_zero_atTop` `:1228` / `epi_of_twoTimeLogRatioGap_tendsto` `:1493`) と path producer
   `matchedTimePath_exists` (`:425`) が全て genuine `@audit:ok`。83-occ migration は Phase 6 の eventual deletion
   scope に移管。
5. **J_X/J_Y Fisher-pin 機構の供給元 = in-tree (壁なし、verbatim 確認)**: `matchedTimePath_exists` の `hJ_deriv`
   と Pillar B の `h_per_t` Fisher pin は**同一の `fisherInfoOfDensityReal ((reg_at σ hσ).density_t)` 量**で、
   `deBruijn_identity_v2` (`FisherInfoV2DeBruijnGenuine.lean:51`) + `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt`
   (`EPIStamToBridge.lean:461`) + `density_t_eq` pointwise pin (`EPIStamDischarge.lean:273`) が両方を供給する。
   sum 側の同組立は `twoTimeLogRatioGap_hasDerivAt` (`EPICase1TwoTime.lean:787-805`) で既に verbatim 実証済 ⟹
   X/Y 側は base 差替えのみ。pin が hand-wave でなく in-tree closeable と確定。残 risk は (R-5a) `J_X` 全域定義の
   `hJX_eq` 閉じ、(R-5b) `h_pos`/`hs_atTop` が `IsMatchedTimePath` 露出フィールド外なので案 2 (`matchedTimePath_exists`
   戻り強化) が要る点の 2 つに局在化。両方 Phase 5 着手最初の probe で gate。
6. **Phase 5 完了 + single-t 系の honesty 再確認 (2026-06-06)**: terminal `entropyPower_add_ge_case1_of_regular_twotime`
   を proof-done (sorryAx-free、独立監査 PASS) で実装。probe-5a/5b 共に PASS、`matchedTimePath_exists` は案 2 で
   sorry-free 強化、再監査 PASS。**Phase 6 の削除判定を変える reconnaissance 所見**: single-t **ratio** pillar
   `csiszarLogRatioGap_deriv_le_zero` (`EPIStamToBridge.lean:940`) は **genuine `@audit:ok`** で、docstring point 4 が
   「ratio 形は plain harmonic Stam から `csiszar_ratio_deriv_le_zero_arith` (`α²≤α` weights) で閉じる」と明記。
   GS-A3' REFUTE は **difference 形** `csiszarGap1Source_deriv_le_zero` (既 `@audit:defect(false-statement)`) に
   局在しており、ratio 形ではない。⟹ 単一-t terminal `entropyPower_add_ge_case1_of_regular` も ratio のみ使用で
   **genuine な case-1 EPI 証明 (`@audit:ok`)**。よって two-time terminal は「初の closure」でなく **parallel な
   genuine 証明**。two-time の真の差別化は **前提の充足可能性**: single-t は sum を単一 noise `Z_X+Z_Y` (variance-2)
   で見るため `h_pos_stam` の Stam supply が `Z_law` `gaussianReal 0 2` defect park (`EPICase1SumProducer.lean:166`)
   に entangle。two-time は Z_X/Z_Y/Z を分離摂動するので variance-2 view を発生させず、前提が genuinely 充足可能。
   **Phase 6 含意**: difference sister (dead `@audit:defect`) の削除は無条件 clean。だが single-t **ratio** line
   (`csiszarLogRatioGap` 群 + terminal) は **genuine `@audit:ok`** なので削除は「working 証明の破棄」= user 判断要
   (plan の「完全置換後削除が clean」は ratio line が defect/dead でない事実と mild に矛盾 → 削除前に surface)。

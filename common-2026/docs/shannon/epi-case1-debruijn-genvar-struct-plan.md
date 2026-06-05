# Shannon EPI: case-1 sum-noise N(0,2) 構造改変 successor サブ計画

> **Parent**: [`epi-case1-debruijn-producer-plan.md`](epi-case1-debruijn-producer-plan.md) §PB-4 / L-Sum-struct
> **Predecessor**: [`epi-case1-sum-producer-plan.md`](epi-case1-sum-producer-plan.md) (sum producer、`Z_law` を `@audit:defect(false-statement)` で park)
> **Status**: 📋 draft (起草のみ、実装は別 session で `lean-implementer` dispatch)。**2026-06-06 訂正改訂: route (B-τ) を GS-1 probe で REFUTE、route (b-2) general-variance surgery が唯一 surviving honest path に確定**。
> **Scope**: docs-only (本 plan); 触る予定の実装 file は per-step 節に列挙
> **proof-log**: yes (`docs/shannon/proof-log-epi-case1-genvar-struct.md`、GS-1 probe 結果記録済)
> **撤退口 slug**: `@residual(plan:epi-case1-debruijn-genvar-struct-plan)`
> (sum producer `EPICase1SumProducer.lean:87` の `@audit:closed-by-successor(epi-case1-debruijn-genvar-struct-plan)` が指す先)

## 現状要約 (handoff、2026-06-06 改訂後)

**現状 = route (B-τ) refuted、route (b-2) が唯一の honest path。** GS-1 probe
(machine-verified、`example` skeleton で型確認、実行後 revert 済、詳細
`proof-log-epi-case1-genvar-struct.md`) が「unit-noise `W := (Z_X+Z_Y)/√2 ∼ 𝒩(0,1)` を de Bruijn
structure に渡し時間 `τ=2t` で reparam する」route (B-τ) を **NO-GO** と確定した:
W 置換に必要な reparam `τ=2t` が sum 項の de Bruijn 微分 (carrier 2t) を X/Y 項 (time t) から
**desync** させ、antitone 証明が要求する **単一共有 t** の 3 成分結合を壊す (probe item 4d、後述)。
wrapper-W 化 (route c) も antitone target `csiszarLogRatioGap` が単一-t signature で sum noise を
hardcode するため不可。**唯一生き残る path = route (b-2)**: `IsRegularDeBruijnHypV2.Z_law` を
`gaussianReal 0 v_Z` + carrier `t·v_Z` に開き、**factor-2 ratio-Stam bound を sum 項込みで再導出**する
13-file / 50+ site の multi-session structural wave。

**解析核 = factor-2 ratio-Stam 再導出** (plumbing ではない、真の EPI 数学だが genuine 証明を要する)。
これが naive 値据置一般化 (fork-sizing 確定で偽) と区別される「正しい factor での再導出」(EPI は真の
定理なので真であるはず) であることは §解析核判定 で実コード verbatim 裏取り済。

**次手 = `proof-pivot-advisor` gate** (GS-A0): 13-file surgery に着手する前に「factor-2 ratio-Stam が
現有資産 (Stam/Blachman 補題群) から genuine に再導出できるか」を在庫横断確認する。解析核が真と
機械確認できてから plumbing に投資する risk 順序。defect park (`Z_law` の
`@audit:defect(false-statement)` + `@audit:closed-by-successor(...)`、`EPICase1SumProducer.lean:166`)
は本 wave 進行中**維持** (本 plan が closure owner、slug 正当)。

## 進捗

- [x] Q-CORE 結線決着 (v_Z が de Bruijn 微分値→ratio core arith に到達するか実コード verbatim) — 本 plan 内で完了
- [x] ~~GS-0 在庫 (reparam ルート資産 verbatim 確認)~~ — GS-1 probe inventory で完了 (proof-log §Inventory) ✅
- [x] ~~GS-1 採用ルート確定 (B-τ vs b-2 vs c)~~ — 🔄 **B-τ/c REFUTED、b-2 が唯一 path に確定** (probe machine-verified、判断ログ 5/6/7) ✅
- [ ] GS-A0 `proof-pivot-advisor` gate: factor-2 ratio-Stam 再導出が現有資産で genuine に閉じるか在庫横断確認 (**着手前 gate**、wall なら全体 park 恒久化 + textbook 別 phase 送り) 📋
- [ ] GS-A1 `IsRegularDeBruijnHypV2` の `v_Z` field 追加 + `density_t_eq` carrier `t·v_Z` 化 (structure surgery、13-file consumer の v_Z:=1 補完 breakage 実測) 📋
- [ ] GS-A2 `_entropy_eq`/`_fisher_match` の general-variance 化 (`pPath_eq_convDensityAdd` general v_Z 経由) 📋
- [ ] GS-A3 **factor-2 ratio-Stam 再導出** (load-bearing 解析核、`csiszarLogRatioGap_deriv_le_zero` の general-variance 版を genuine 証明) 📋
- [ ] GS-A4 sum producer `Z_law` defect→genuine 差し替え (他 field 再利用)、残1 (integrable_deriv t-可測性) park との関係確定 📋
- [ ] GS-A5 PB-6 wrapper `_full` 結線 + GS-V verify (`lake env lean`) + 独立 honesty audit (`honesty-auditor`) PASS 📋

---

## 文脈 (確定背景)

### 何が blocker か

case-1 EPI の解析核は完全 genuine (handoff)。残る headline blocker は
**sum noise `Z_X+Z_Y ∼ 𝒩(0,2)`** (独立標準正規 2 つの和、variance 2) を de Bruijn
regularity structure が受容できないこと。

sum producer (`EPICase1SumProducer.lean`) は他 field
(pX_sum series / density / `integrable_deriv` の bound 部) を genuine に埋めたが、
`reg_at .Z_law` field のみ `@audit:defect(false-statement)` で park 中。`Z_law` field は
unit-hardcode `P.map (Z_X+Z_Y) = gaussianReal 0 1` を要求し、真の law は
`gaussianReal 0 2` (`EPICase1SumProducer.lean:155-161` で `hZXZY_law` として導出)。
**`gaussianReal 0 1 ≠ gaussianReal 0 2`** なので、producer の真の (充足可能な) 仮説下で
`Z_law` obligation は **uninhabitable** (独立監査 2026-06-06 機械確認)。これは plan-residual
ではなく false-statement defect であり、本 plan が **structure 改変で genuine 化**する対象。

### 予測でなく実コードで確定済の事実 (前提とせよ)

1. **de Bruijn identity は `Z_law` の値を消費する** (Q-CORE 決着、§Q-CORE 詳細)。
   `debruijnIdentityV2_holds_assembled` (`FisherInfoV2DeBruijnAssembly.lean:3543`) は
   `_entropy_eq` (`:3437`) と `_fisher_match` (`:3485`) の 2 sub-lemma が
   `hZ_law : P.map Z = gaussianReal 0 1` を **hardcode 引数で取り**、内部で
   `pPath_eq_convDensityAdd ... (1 : ℝ≥0) ... hZ_law` (`:3452`) を呼んで「path
   `X+√s·Z` の真の density (variance carrier `s·v_Z`)」を「`_chain` (`:3397`) が解析する
   density (variance carrier `s`)」に同定する。**v_Z=1 だからこそ `s·v_Z = s` で carrier が
   一致**する (`:3460` `hwit1 : s·1 = s`)。
2. **`_chain` は density-level・v_Z-agnostic** (`:3397-3414`、`pX` のみ引数、noise 不参照、
   density carrier `s` を自前で持つ純解析)。残2 plan の「`_chain` が v_Z-agnostic」主張は **正しい**。
3. **しかし `Z_law` を `gaussianReal 0 2` に開くと carrier が drift する**:
   `_entropy_eq` の `pPath_eq_convDensityAdd` 呼出が `s·v_Z = s·2 ≠ s` を返し、path の真の
   density (carrier `s·2`) と `_chain` が消費する density (carrier `s`) が **一致しなくなる**。
   整合させるには general-variance 版 `_entropy_eq_genvar` を作るしかなく、そこで de Bruijn
   微分値が `(1/2)·J(convDensityAdd pX g_{s·v_Z})` (carrier `s·v_Z`) になり、fork-sizing
   `(v_Z/2)·J` 偽化と **同一機構** で ratio core を壊す。
4. **prior art `IsHeatFlowEndpointRegular` は ratio core を偽化していない理由**:
   この structure (`EPIG2HeatFlowContinuity.lean:488`、general `v_Z` field +
   `hZ_law : gaussianReal 0 v_Z`) は sum に `v_Z := 2` を渡して構成済
   (`EPIStamToBridge.lean:1447-1452`)。だが `csiszarLogRatioGap_antitoneOn_Ici_zero`
   (`EPIStamToBridge.lean:1085`) はこれを **端点連続性専用** (`heatFlowEntropyPower_continuousWithinAt_zero`、
   t=0⁺ への収束) としてのみ消費し、**Fisher 微分値 (ratio core arith) には到達させない**。
   ratio core が消費するのは `IsDeBruijnRegularityHyp` の `(h_reg_*.reg_at t ht).density_t` の
   Fisher 値 (`EPIStamToBridge.lean:712-721`) であって、`IsHeatFlowEndpointRegular` の v_Z は
   連続性 (値ではなく収束) にしか使われない。**両 structure が同一 consumer に共存できるのは、
   v_Z 一般を許す方 (`IsHeatFlowEndpointRegular`) が arith に到達しないから**。
   → `IsRegularDeBruijnHypV2` の v_Z 一般化は `IsHeatFlowEndpointRegular` の v_Z 一般化と
   **異なる** (前者は arith に到達、後者は到達しない)。prior art は v_Z 一般化が安全な証拠には
   **ならない** — 安全なのは「連続性 structure の v_Z」だけで「微分値 structure の v_Z」ではない。

### Q-CORE の結論 (本 plan の設計を決める)

**残2 plan の「Z_law を一般化しても微分値を触らず density を unit-W pin すれば偽化回避」は
`_entropy_eq` の hardcode `(1:ℝ≥0)` を見落としている**。`density_t` を unit-W 形に pin しても、
`_entropy_eq`/`_fisher_match` が `Z_law` の値で「path の真の density」を同定する以上、
`Z_law = gaussianReal 0 2` と「density_t が carrier `s` (unit-W)」は **型整合しない**
(path の真の density は carrier `s·2`、`_fisher_match` の `density_t_eq` 等式が `s` carrier の
convDensityAdd を要求するので矛盾)。

→ (起草時の結論) **正しい道は値一般化 (案A / b-2 naive) でも density-pin だけ (残2 plan) でもなく、
time-reparam で carrier を unit に戻すこと** (fork-sizing 案C / 案B+τ reparam)、本 plan のルート (B-τ)。

> **⚠ 2026-06-06 訂正 (判断ログ 5/6/7)**: この Q-CORE 起草時の B-τ 結論は GS-1 probe で **REFUTE**。
> time-reparam `τ=2t` は sum 項の de Bruijn 微分を X/Y 項から **desync** させ、antitone 証明の単一共有 t
> 結合を壊す (B-τ NO-GO)。Q-CORE が正しく示したのは「v_Z は ratio core arith に到達する」「density-pin
> だけでは救えない」までで、**救済策が reparam (B-τ) という結論が誤り**だった。variance-2 は coupling に
> intrinsic で回避不能 (§解析核判定 (i))、唯一の道は general-variance 正面受容 (b-2) + factor-2
> ratio-Stam 再導出。本節以降の B-τ 記述は歴史的経緯として残置 (§候補ルートで B-τ/c を取消線化済)。

---

## ゴール / Approach

### ゴール

sum producer `isDeBruijnRegularityHyp_sum_of_methodX_unitnoise`
(`EPICase1SumProducer.lean:88`) の `Z_law` field の `@audit:defect(false-statement)` park を
**genuine 化**し、`IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` を sum noise N(0,2) で本物に供給する。
これにより case-1 final wrapper `_full` (PB-6) が de Bruijn group を前提から消し、headline EPI
case-1 が proof done (残1 integrable_deriv t-可測性 closure と協調すれば
`[propext, Classical.choice, Quot.sound]`) に届く。

### Approach (全体形、2026-06-06 改訂 — route b-2 確定後)

**訂正の経緯**: 旧 Approach は route (B-τ) (unit-noise W + 時間 τ=2t reparam) を本命としていたが、
GS-1 probe (machine-verified) で **B-τ NO-GO** が確定した (判断ログ 5)。W 置換の reparam `τ=2t` が
sum 項の de Bruijn 微分 (carrier 2t) を X/Y 項 (time t) から **desync** させ、antitone 証明
`csiszarLogRatioGap_hasDerivAt` (`EPIStamToBridge.lean:699`) が要求する **単一共有 t** の 3 成分結合を
表現不能にする。wrapper-W 化 (route c) も antitone target `csiszarLogRatioGap`
(`EPIL3Integration.lean:1380`) が sum noise を `Z_X+Z_Y` + 単一 t で hardcode するため不可。
→ **唯一 surviving honest path = route (b-2) general-variance de Bruijn surgery**。

**核心 (b-2)** = sum noise の variance 2 を **回避しようとせず** (B-τ/c はこれを試みて desync で失敗)、
de Bruijn structure を **general-variance 化して factor-2 を正面から受容**する:
1. `IsRegularDeBruijnHypV2.Z_law` を `gaussianReal 0 v_Z` (+ `v_Z` field) に開き、`density_t_eq` の
   carrier を `⟨t·v_Z,_⟩` に開く。
2. `_entropy_eq`/`_fisher_match` を general-variance 化 (`pPath_eq_convDensityAdd` general v_Z 経由)
   して de Bruijn 微分値を `(v_Z/2)·J(convDensityAdd pX g_{t·v_Z})` にする。
3. **factor-2 ratio-Stam bound を sum 項込みで再導出** (sum→v_sum=2、X/Y→v=1 の非一律 factor で
   harmonic Stam を再構成)。**これが load-bearing 解析核**。
4. X/Y instance は v_Z:=1 補完で 13-file / 50+ consumer site を patch。

**何が genuine に閉じるか / 何が解析核 (壁候補) か**:
- de Bruijn identity の density-level core (`_chain`) は **v_Z-agnostic で既に genuine**
  (Q-CORE 事実 2)。新規解析は不要。
- structure surgery (GS-A1/A2、v_Z field 追加 + carrier 一般化) は **plumbing** (型レベル + carrier の
  一般化、`pPath_eq_convDensityAdd` general v_Z が既存資産)。
- **真の解析核 = factor-2 ratio-Stam 再導出** (GS-A3)。これは plumbing でなく EPI の数学そのもの
  (harmonic-Stam `1/J(X+Y) ≥ 1/J(X)+1/J(Y)` 系を factor-2 sum 項で正しく再構成)。**genuine 証明を
  要する**。naive 値据置一般化 (fork-sizing 確定で偽) との区別は §解析核判定 で実コード裏取り済。

**risk 順序 (最重要)**: 解析核 (GS-A3) が真と確認できてから plumbing (GS-A1/A2) に投資する。具体的には
**GS-A0 で `proof-pivot-advisor` gate** を最初に置き、「factor-2 ratio-Stam が現有資産
(Stam/Blachman 補題群) から genuine に再導出できるか」を在庫横断確認する。advisor が「現有資産で
閉じる」と判定し、かつ独立機械検証で裏取りできてから 13-file structure surgery に着手する。
advisor が wall 判定したら全体 park を恒久化し textbook 別 phase に送る (plumbing に投資しない)。

**段階構成**:
- **GS-A0** `proof-pivot-advisor` gate (着手前、wall なら撤退)。
- **GS-A1** structure surgery (v_Z field + carrier 一般化、consumer breakage 実測)。
- **GS-A2** `_entropy_eq`/`_fisher_match` general-variance 化。
- **GS-A3** factor-2 ratio-Stam 再導出 (解析核)。
- **GS-A4** sum producer `Z_law` defect→genuine 差し替え + 残1 park 整理。
- **GS-A5** PB-6 wrapper 結線 + verify/監査。

**撤退口**: GS-A0 で wall 判定なら全体 park 維持 (defect 形を保つ)。GS-A3 (解析核) が詰まれば当該
phase を `sorry` + `@residual(plan:epi-case1-debruijn-genvar-struct-plan)` で park (signature は本来
証明したい形を保つ)。`*Hypothesis` predicate に核を bundling する撤退は禁止 (CLAUDE.md「検証の誠実性」)。

---

## Q-CORE 詳細 — v_Z が ratio core arith に到達するか (実コード結線、本 plan の価値の中心)

### (1) `IsRegularDeBruijnHypV2` の各 field の v_Z 依存 (verbatim、`FisherInfoV2DeBruijn.lean:205-268`)

| field | 型 | v_Z 依存 |
|---|---|---|
| `Z_law` | `P.map Z = gaussianReal 0 1` (`:210`) | **unit hardcode** (v_Z=1 固定) |
| `density_t` | `ℝ → ℝ` (`:212`) | 値は構成側が決める (carrier は `density_t_eq` で pin) |
| `pX` series (`pX`/`pX_nn`/`pX_meas`/`pX_law`) (`:227-234`) | X 自身の Lebesgue 密度 witness | v_Z 非依存 (noise 不参照) |
| `density_t_eq` | `density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x` (`:260-261`) | **carrier `t` hardcode** (v_Z=1 を前提に `s·1=s` で carrier=t) |
| `pX_mom` | `Integrable (y²·pX)` (`:268`) | v_Z 非依存 |

**結論**: `Z_law` と `density_t_eq` の **2 field が v_Z=1 を hardcode**。`density_t_eq` の RHS は
`gaussianPDFReal 0 ⟨t,_⟩` (carrier `t`)。これは「path `X+√t·Z` の真の density は carrier `t·v_Z`」と
**v_Z=1 のときだけ一致**する。

### (2) de Bruijn identity (`_chain`/`_entropy_eq`/`_fisher_match`) の v_Z 結線

- **`_chain`** (`FisherInfoV2DeBruijnAssembly.lean:3397-3414`): 引数は `pX` 系のみ、**noise 不参照**。
  結論の density carrier は `gaussianPDFReal 0 ⟨max s 0,_⟩` (= variance `s`、自前)。**v_Z-agnostic**。
- **`_entropy_eq`** (`:3437-3473`): `hZ_law : P.map Z = gaussianReal 0 1` を **hardcode 引数で取り**
  (`:3440`)、内部 `pPath_eq_convDensityAdd X Z ... (1 : ℝ≥0) one_pos hZ_law ...` (`:3452`) で
  path の真の density を carrier `s·1 = s` に同定 (`:3460-3462` `hwit1`)。**v_Z=1 hardcode**。
- **`_fisher_match`** (`:3485-3500`): `_hZ_law : gaussianReal 0 1` を取る (`:3488`、underscore)。
  `density_t_eq` の carrier `⟨t, ht.le⟩` (= `t`) で `density_t` を convDensityAdd と同定。**v_Z=1 hardcode**。
- **`_assembled`** (`:3543-3587`): 上記 3 つを `h_reg.Z_law` (= unit) で叩いて
  `(1/2)·fisherInfoOfDensityReal h_reg.density_t` を返す。

`pPath_eq_convDensityAdd` 自身 (`FisherInfoV2DeBruijnPerTime.lean:215-224`) は **general v_Z 受容**
(`v_Z : ℝ≥0` 引数、結論 density carrier `s·v_Z`)。だが `_entropy_eq` が **v_Z:=1 を hardcode で
instantiate** しているため、`_assembled` 全体は v_Z=1 でしか genuine に組まない。

### (3) consumer が何の微分値を見るか (ratio core への到達、`EPIStamToBridge.lean:699-838`)

`csiszarLogRatioGap_hasDerivAt` (`:699`) は X/Y/sum 3 成分で `deBruijn_identity_v2` を呼び
(`:730/738/747`)、各 `(1/2)·J((h_reg_*.reg_at t ht).density_t)` を得る (`:728/736/745`)。lift で
`2·(1/2)=1` で `(1/2)` が一律 cancel (`:773/785/799`)、ratio-gap 微分値は
`J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y)` (`:712-721`)。`csiszarLogRatioGap_deriv_le_zero` (`:895`) が
plain harmonic Stam から ≤0 を出す (`:843-848`、weights `α²≤α`)。

**到達結線**: ratio core arith が消費するのは `density_t` の **Fisher 値**。`density_t` の値は
`density_t_eq` (carrier `t·v_Z`) と `_fisher_match` で決まる。よって **`Z_law` の v_Z は
`_entropy_eq`/`density_t_eq` の carrier 経由で `density_t` の Fisher 値を決め、ratio core arith に
到達する**。v_Z≠1 にすると carrier が `t·v_Z` に drift し、`J(convDensityAdd pX g_{t·v_Z})` が
各成分で非一律 factor を持ち、harmonic Stam (項毎 factor 非不変) を偽化する (fork-sizing Q1)。

→ **Q-CORE 答え: v_Z は ratio core arith に到達する**。残2 plan の「微分値を触らず density-pin で
偽化回避」は不可 (`_entropy_eq` hardcode が `Z_law` 値と density carrier を結びつけている)。
~~唯一の道は path/time の reparam で carrier を unit に戻すこと (ルート B-τ)~~ — **2026-06-06 訂正: この
reparam (B-τ) 結論は probe で REFUTE (上記 ⚠ 注 / 判断ログ 5)。v_Z が arith 到達するのは正しいが、
救済は reparam でなく general-variance 正面受容 (b-2) + factor-2 ratio-Stam 再導出**。

### prior art の機械検証 — 共存が v_Z 安全の証拠にならない理由

`IsHeatFlowEndpointRegular` (general v_Z) と `IsDeBruijnRegularityHyp` (unit、ratio core 経由) は
`csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1085-1098`) で **同時に受け取られ、
sum は前者に v_Z=2 を渡して共存**している (`:1447-1452`)。だがこの共存は v_Z 一般化が「安全」な
証拠に **ならない**: `IsHeatFlowEndpointRegular` の v_Z は **端点連続性専用**
(`heatFlowEntropyPower_continuousWithinAt_zero`、収束) で **ratio core arith (Fisher 微分値) に
到達しない**。一方 `IsDeBruijnRegularityHyp` の v_Z は (3) のとおり arith に到達する。
2 structure の v_Z は **役割が別** (連続性 vs 微分値) なので、前者の v_Z=2 共存は後者の v_Z 一般化を
正当化しない。残2 plan の M0' 観察 (prior art = ルート b 根拠) は **この役割差を見落としている**。

---

## 解析核判定 — variance-2 intrinsic + factor-2 ratio-Stam の真偽 (本 plan の中心価値、次 session risk 順序を規定)

### (i) variance-2 は proof に intrinsic (回避不能、実コード verbatim 裏取り)

標準 de Bruijn EPI の coupling
`(X+Y)+√t·(Z_X+Z_Y) = (X+√t·Z_X)+(Y+√t·Z_Y) = X_t+Y_t` が成立するには、sum noise が
**必ず `Z_X+Z_Y` (variance 2)** でなければならない。fresh unit `Z_S ∼ 𝒩(0,1)` を sum 項に使うと
この coupling が壊れ、X_t と Y_t の Fisher 比較 (ratio-Stam) ができない。

**実コード裏取り** (verbatim):
- `csiszarLogRatioGap` (`EPIL3Integration.lean:1382`) の sum path は
  `fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)` — sum noise が **literal に `Z_X+Z_Y`**
  (variance 2)、X/Y path は `X+√t·Z_X` / `Y+√t·Z_Y` で **同一の単一 t**。これが coupling
  `X_t+Y_t` そのもの。
- `csiszarLogRatioGap_deriv_le_zero` の `h_conv_id` (`EPIStamToBridge.lean:919-922`) は sum density
  `(h_reg_sum.reg_at t ht).density_t` を **carrier-t の X-density と Y-density の `convDensityAdd`** に
  同定する: `density_t x = convDensityAdd ((h_reg_X.reg_at t ht).density_t) ((h_reg_Y.reg_at t ht).density_t) x`。
  carrier-t の 2 密度の convolution は **carrier-2t** — これは coupling
  `(X+√t·Z_X)+(Y+√t·Z_Y)` の density で、sum noise が `Z_X+Z_Y` (variance 2) でなければ成立しない。

→ **variance-2 は回避不能**。だからこそ B-τ/c (variance-2 を unit W に置換して回避しようとする route)
が desync で失敗した (W は coupling を壊す)。**variance-2 を正面から受容する general-variance
structure (b-2) が本質的に必要**。

### (ii) factor-2 ratio-Stam 再導出は真の EPI 数学か、それとも wall か (next session の判定対象)

GS-A3 の解析核は **factor-2 ratio-Stam bound の再導出**。これが「真の EPI 数学 (genuine 証明可能)」か
「wall」かの区別が次 session の risk 順序を決める。**結論: naive 値据置一般化と正しい factor 再導出は
別物で、後者は真であるはず (EPI は真の定理)、ただし genuine 証明を要する**。

**fork-sizing の偽化主張がどちらを指すか — 実コード verbatim 再確認**:
fork-sizing doc (`epi-case1-debruijn-producer-fork-sizing.md` Q1、`:32-40`) は「案A-corrected =
値据置で `(1/2)·J_i → (v_Z_i/2)·J_i` に変える」と各成分に **非一律 factor** (X→v_X, Y→v_Y,
sum→v_X+v_Y、v_X≠v_Y) が乗り、`csiszarLogRatioGap_deriv_le_zero` (`EPIStamToBridge.lean:895`) の
arith core (`csiszar_ratio_deriv_le_zero_arith`、α²≤α weights) が **破れる**と判定した。

**この偽化主張が指すのは「naive 値据置一般化」**: fork-sizing は `(1/2)·J` の値をそのまま
`(v_Z/2)·J` に **据え置き換える**だけで、ratio core の **harmonic-Stam weights を再導出しない**場合を
評価している。現コード `csiszarLogRatioGap_deriv_le_zero` (`EPIStamToBridge.lean:895`) は全成分 unit
(`(1/2)·J`) 前提の harmonic-Stam (`h_blachman : IsBlachmanConvReady`、`α²≤α` weights) で、これに
factor だけ後付けすると weight が合わず偽になる、というのが fork-sizing Q1。

**b-2 が指すのは「正しい factor で再導出した harmonic-Stam」**: sum 項が variance-2 noise
(`d/dt h((X+Y)+√t·(Z_X+Z_Y))` で carrier `t·2`) のとき、**正しい微分値**は `(2/2)·J_sum = J_sum`
(carrier scale 2)。これを weight に正しく織り込んで harmonic-Stam を再構成すれば、得られるのは
**真の EPI の Stam 不等式** (`1/J(X+Y) ≥ 1/J(X)+1/J(Y)` 系、Blachman score-of-convolution) であり、
**EPI は真の定理なので真であるはず**。fork-sizing が偽化したのは「値据置のまま weight 据置」した naive
版であって、「正しい factor で weight ごと再導出」した版ではない。

**判定の一言**:
- **naive 値据置一般化 = 偽** (fork-sizing Q1 確定、値だけ `(v_Z/2)·J` にして weight 据置)。
- **正しい factor で再導出した harmonic-Stam = 真** (EPI 数学、`J_sum ≥ harmonic(J_X,J_Y)`、ただし
  GS-A3 で genuine 証明を要する)。

**risk 順序 (next session GATE)**: 上記「真であるはず」は **EPI が真の定理である**という一般論からの
推定であって、現有資産 (Stam/Blachman 補題群、`IsBlachmanConvReady`、既証 `convex_fisher_bound` 系)
から factor-2 版が **genuine に再導出できるか**はまだ機械確認していない。よって **GS-A0 で
`proof-pivot-advisor` を起動し、factor-2 ratio-Stam が現有資産から genuine に閉じるかを在庫横断
確認してから 13-file surgery に着手する**。advisor が「閉じる」と判定し独立機械検証で裏取りできれば
GS-A1 以降に進む。advisor が wall 判定したら plumbing に投資せず全体 park を恒久化し textbook 別
phase に送る。**解析核が真と確認できてから plumbing に投資する**のが本 plan の risk 規律。

## 候補ルートの列挙と sizing (2026-06-06 改訂 — B-τ/c REFUTED 後)

### ~~ルート (B-τ) — unit-noise W + 時間 reparam τ=t·v_Z~~ — **REFUTED (GS-1 probe machine-verified)**

**REFUTE 理由** (probe item 4d、`proof-log-epi-case1-genvar-struct.md` §Machine-verified):
W 置換に必要な reparam `τ = 2t` が、sum path `X+Y+√t·(Z_X+Z_Y)` を W-path の time `2t`
(`X+Y+√(2t)·W`) として再表現する。その de Bruijn 微分は `h_reg_W.reg_at (2t)` に座り、
`(1/2)·J(density_t @ 2t)` を **time 2t で評価**する。一方 X/Y 項の微分は time t (`h_reg.reg_at t`)。
antitone 証明 `csiszarLogRatioGap_hasDerivAt` (`EPIStamToBridge.lean:699`) は **3 成分すべてを単一
共有 t** で取るため、sum だけ別 time (2t) にできない (**desync**)。W-producer の `reg_at-at-2t` を
shared-t 結合に入れるには consumer の `(1/2)·J` arithmetic が持たない `2·` chain factor が要る。
probe item 4d がこの desync を型レベルで確認。

**producer 側は genuine だった**: W-law `P.map ((Z_X+Z_Y)/√2) = gaussianReal 0 1` は
`gaussianReal_add_gaussianReal_of_indepFun` → `gaussianReal_map_div_const` で ~15 行で閉じる
(probe item 1)、W-producer も clean に構成 (item 2)、`reg_at .Z_law` obligation も W で genuine 充足
(item 3a)。だが **consumer 側が W を受容できない** (item 4d desync) ため producer が genuine でも全体が
通らない。**`Z_law=unit` の false は consumer の微分 arithmetic に load-bearing** (probe で
`EPIStamToBridge.lean:747` → `debruijnIdentityV2_holds_assembled` が false unit `Z_law` を消費して
variance-2 sum 項の `(1/2)` factor を得ると trace 確定)。W はこの false を time-desync に移すだけで
除去しない。

### ~~ルート (c) — wrapper を unit-noise W で restate~~ — **不可 (antitone object の単一-t signature で表現不能)**

**不可理由** (probe Blast radius 節): antitone target `csiszarLogRatioGap`
(`EPIL3Integration.lean:1380`) は sum noise を `Z_X+Z_Y` + 単一 t で **hardcode**。W 化は sum 項に
別 time (2t) を要求するが、`csiszarLogRatioGap` の単一-t signature では「sum 項だけ別 time」を表現
できない。mechanical noise rename でなく、antitone object の **時間変数 restructuring** (sum path の
time を X/Y path から分離) が必要で、これは ~93 sum-path sites (3 consumer file + endpoint lemmas
+ saturation pillar) に伝播する。**tractable な wrapper rename ではない**。

### ルート (b-2) — `IsRegularDeBruijnHypV2` general-variance surgery — **唯一 surviving honest path** ✓

**内容**: §Approach 核心 (b-2) のとおり。`Z_law` を `gaussianReal 0 v_Z` (+ v_Z field) に開き、
`density_t_eq` の carrier を `⟨t·v_Z,_⟩` に開き、`_entropy_eq`/`_fisher_match` を
`pPath_eq_convDensityAdd` general v_Z 経由で一般化し、**factor-2 ratio-Stam を sum 項込みで再導出**。
X/Y instance は v_Z:=1 補完。

**B-τ/c との違い**: B-τ/c は variance-2 を unit W に **置換して回避**しようとして desync で失敗した。
b-2 は variance-2 を **回避せず正面から受容**する (general-variance structure)。§解析核判定 (i) のとおり
variance-2 は coupling に intrinsic なので、回避は原理的に不可能、受容が唯一の道。

**load-bearing 解析核 = factor-2 ratio-Stam 再導出** (§解析核判定 (ii))。これが plumbing でなく真の EPI
数学。GS-A0 advisor gate で genuine 再導出可能性を確認してから surgery に着手。

**blast radius (実測済、`EPICase1SumProducer.lean:18` header / proof-log §What genuine closure)**:
`IsRegularDeBruijnHypV2` consumer = **13 file / 50+ 件** (`rg -c IsRegularDeBruijnHypV2`)。
`Z_law` + `density_t_eq` の carrier を general-variance 化すると全 consumer に v_Z:=1 補完 patch が
要る。consumer patch が機械的に済むか各証明が carrier `t` に load-bearing 依存して書換要かは GS-A1 で
`lake env lean` 実測 (撤退ライン L-GS-blast)。

**prior art `pPath_eq_convDensityAdd`**: general v_Z 版 (`FisherInfoV2DeBruijnPerTime.lean:215`、
`(v_Z:ℝ≥0)` 引数、carrier `s·v_Z`) が **既に in-tree** — これが b-2 の唯一の real asset
(GS-A2 で `_entropy_eq`/`_fisher_match` から呼ぶ)。`IsHeatFlowEndpointRegular` の general-v_Z 共存は
**役割別** (端点連続性専用で arith 非到達、Q-CORE prior art 節) なので b-2 の安全証拠にはならない。

### ルート比較表 (改訂後)

| 観点 | (b-2) genvar surgery ✓ | ~~(B-τ) W + τ reparam~~ REFUTED | ~~(c) wrapper-W~~ 不可 |
|---|---|---|---|
| 状態 | **唯一 surviving honest path** | **REFUTED** (probe item 4d desync) | **不可** (単一-t signature) |
| variance-2 の扱い | **正面受容** (general-variance) | unit W に置換 (回避) → desync | unit W に置換 → 単一-t 不能 |
| `Z_law` 型整合 | carrier `t·v_Z` で一般化、genuine | W で genuine だが consumer 不受容 | — |
| ratio core | **factor-2 ratio-Stam 再導出 (解析核)** | reparam で carrier 2t、desync | sum 項別 time、表現不能 |
| structure 改変 | `Z_law`+`density_t_eq` general-var (大) | なし (producer 側のみ) | なし |
| 影響範囲 | **13 file / 50+ consumer** | producer ~15 行だが consumer 不受容 | ~93 sum-path sites の time 再構成 |
| de Bruijn core | `_entropy_eq`/`_fisher_match` 一般化要 | `_assembled` 無改変だが消費不能 | — |
| prior art | `pPath_eq_convDensityAdd` general v_Z 既存 | PB-2 path-id (item 4d で desync 露呈) | — |
| 推奨 | **唯一 path** | 廃止 | 廃止 |

**推奨 = (b-2)**: variance-2 が coupling に intrinsic (§解析核判定 (i)) なので回避不能、general-variance
受容が唯一の道。解析核 = factor-2 ratio-Stam 再導出 (真の EPI 数学、GS-A3 で genuine 証明)。**着手前に
GS-A0 で `proof-pivot-advisor` gate を通す** (解析核が現有資産で閉じるか確認してから 13-file surgery)。

---

## Phase 詳細 (2026-06-06 改訂 — route b-2 用)

> 旧 GS-0〜GS-V (B-τ 前提) は probe で REFUTE。在庫 (GS-0) は probe inventory で完了済
> (proof-log §Inventory)。以下は b-2 (general-variance surgery) 用の再構成。

### GS-A0 — `proof-pivot-advisor` gate (着手前、factor-2 ratio-Stam 再導出の tractability 確認)

**スコープ**: 13-file structure surgery に着手する **前** に、解析核 (factor-2 ratio-Stam 再導出、
GS-A3) が **現有資産で genuine に閉じるか**を在庫横断で確認する。これが GATE — 解析核が真と確認
できてから plumbing に投資する risk 規律 (§解析核判定 (ii))。

- [ ] `proof-pivot-advisor` を起動: 「sum 項が variance-2 noise (carrier `t·2`、微分値 `J_sum`) の
  とき、harmonic-Stam ratio bound `J_sum ≥ (N_X·J_X+N_Y·J_Y)/(N_X+N_Y)` を、現有資産
  (`IsBlachmanConvReady` / `convex_fisher_bound` 系 / `IsStamInequalityHyp` / `csiszar_ratio_deriv_le_zero_arith`)
  から genuine に再導出できるか」を在庫横断確認 (CLAUDE.md「Mathlib 壁判定は独立 pivot で再確認」)
- [ ] advisor verdict を独立機械検証で裏取り (loogle で関連 Stam/Blachman lemma の有無、
  factor-2 版が `α²≤α` weights の自然な一般化で出るか skeleton 試算)

**Done 条件 / 分岐**:
- **tractable (advisor + 機械検証で「閉じる」)** → GS-A1 に進む (structure surgery 着手)。
- **wall (factor-2 版が現有資産で閉じない)** → **全体 park 恒久化**: `Z_law` defect park 維持、
  本 plan を textbook 別 phase (EPI 解析核の Mathlib 整備待ち) に送り、判断ログに wall 判定を記録。
  plumbing (13-file surgery) には **投資しない** (解析核が壁なら surgery は無駄)。

### GS-A1 — `IsRegularDeBruijnHypV2` structure surgery (v_Z field + carrier 一般化)

**スコープ** (GS-A0 が tractable 判定後): `IsRegularDeBruijnHypV2`
(`FisherInfoV2DeBruijn.lean:205-268`) に `v_Z` field を追加し、`Z_law` を `gaussianReal 0 v_Z`
(`:210` の unit hardcode を開く)、`density_t_eq` の carrier を `⟨t·v_Z,_⟩` (`:260-261` の carrier `t`
hardcode を開く) に一般化。13-file / 50+ consumer site の breakage を実測。

- [ ] skeleton: `v_Z` field 追加 + `Z_law`/`density_t_eq` carrier 一般化 (`:= by sorry` で型枠)
- [ ] 13 file / 50+ consumer (`rg -c IsRegularDeBruijnHypV2`) の v_Z:=1 補完 breakage を
  `lake env lean` で実測 — 機械的補完 (X/Y instance に `v_Z := 1`) で通るか、各証明が carrier `t` /
  `gaussianReal 0 1` に load-bearing 依存して書換要かを per-file 記録
- [ ] consumer patch (v_Z:=1 補完) を機械的に適用、breakage が機械的補完で吸収される範囲を確定

**撤退ライン (L-GS-blast)**: consumer 各証明が carrier に load-bearing 依存して機械的補完が効かず
breakage が想定 (13 file / 50+) を大幅に超える → surgery を分割するか、structure 拡張でなく
**新 general-variance structure を別途定義** (既存 unit structure を残し新旧並存) する route に escalate
(判断ログに記録)。

**Done 条件**: structure 一般化 type-check done、consumer breakage が v_Z:=1 補完で吸収される範囲を確定。

### GS-A2 — `_entropy_eq`/`_fisher_match` の general-variance 化

**スコープ**: `debruijnIdentityV2_holds_assembled_entropy_eq` (`FisherInfoV2DeBruijnAssembly.lean:3437`、
`hZ_law : gaussianReal 0 1` hardcode + 内部 `pPath_eq_convDensityAdd ... (1:ℝ≥0) ...` `:3452`) と
`_fisher_match` (`:3485`) を general-variance 化し、`pPath_eq_convDensityAdd` の general v_Z 版
(`FisherInfoV2DeBruijnPerTime.lean:215`、既存資産) を `v_Z` 引数で呼ぶ。de Bruijn 微分値が
`(v_Z/2)·J(convDensityAdd pX g_{t·v_Z})` (carrier `t·v_Z`) になる。

- [ ] `_entropy_eq` general-variance 版: 内部 `pPath_eq_convDensityAdd ... v_Z ...` を呼び carrier
  `s·v_Z` に同定 (`:3452` の `(1:ℝ≥0)` を `v_Z` に開く)
- [ ] `_fisher_match` general-variance 版: `density_t_eq` carrier `⟨t·v_Z,_⟩` で `density_t` を
  convDensityAdd と同定 (`:3485-3500`)
- [ ] `_chain` (`:3397-3414`、v_Z-agnostic、無改変) との結線確認 (`_chain` は noise 不参照なので
  general-variance 化不要、Q-CORE 事実 2)
- [ ] `debruijnIdentityV2_holds_assembled` (`:3543`) が general-variance 3 sub を組んで
  `(v_Z/2)·J` を返す形に更新、X/Y consumer は v_Z=1 で `(1/2)·J` に縮退することを確認

**Done 条件**: de Bruijn identity が general v_Z で type-check done、X/Y は v_Z=1 で従来形に縮退、
sum は v_Z=2 で `J_sum` (carrier `t·2`) を返す。

### GS-A3 — factor-2 ratio-Stam 再導出 (load-bearing 解析核)

**スコープ**: `csiszarLogRatioGap_deriv_le_zero` (`EPIStamToBridge.lean:895`) を general-variance 版に
書き換え、**factor-2 sum 項込みで harmonic-Stam ratio bound を genuine に再導出**する。これが本 plan の
load-bearing 解析核 (§解析核判定 (ii))。

**何を証明するか**: 現コードは全成分 unit (`(1/2)·J`) 前提の harmonic-Stam (`α²≤α` weights、
`csiszar_ratio_deriv_le_zero_arith`)。general-variance では sum 項が `J_sum` (factor 2、carrier
`t·2`)、X/Y が `J_X`/`J_Y` (factor 1) で、ratio-gap 微分値が
`J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y) ≤ 0` を **factor-2 sum 項で正しく weight 再導出**して示す。
これは真の EPI の Stam 不等式 (`1/J(X+Y) ≥ 1/J(X)+1/J(Y)`、Blachman) なので真であるはず (genuine 証明)。

**honesty 判定**: 「naive 値据置一般化 (`(1/2)·J → (v_Z/2)·J` で weight 据置) = 偽」(fork-sizing Q1)
を **避け**、「正しい factor で weight ごと再導出 = 真」を genuine に証明する。`α²≤α` weights を
factor-2 sum 項に対応する形で再導出し、`IsBlachmanConvReady` / `convex_fisher_bound` 系から閉じる。
`*Hypothesis` predicate に核を bundling しない (factor-2 bound を仮説に抱えさせず genuine 証明)。

**撤退ライン (L-GS-A3-core)**: factor-2 ratio-Stam 再導出が現有資産で閉じない (GS-A0 advisor が
tractable と判定したが実装で詰まる) → 当該 phase を `sorry` +
`@residual(plan:epi-case1-debruijn-genvar-struct-plan)` で park (signature は本来の
`csiszarLogRatioGap_deriv_le_zero` general-variance 形を保つ)。`*Hypothesis` bundling 撤退は禁止。
解析核が park されると headline は closure しないので、closure を次 wave に繰り越し判断ログに記録。

**Done 条件**: factor-2 ratio-Stam が general-variance で type-check done、genuine に閉じれば
解析核 closure (proof done 候補)。

### GS-A4 — sum producer `Z_law` defect→genuine 差し替え + 残1 park 整理

**スコープ**: GS-A1〜A3 で general-variance de Bruijn が genuine になったら、sum producer
`isDeBruijnRegularityHyp_sum_of_methodX_unitnoise` (`EPICase1SumProducer.lean:88`) の `Z_law` field
park (`:151-168`、`@audit:defect(false-statement)`) を genuine に差し替え (sum noise `Z_X+Z_Y` の
真の law `gaussianReal 0 2` を v_Z=2 field で受容、§解析核判定 (i) のとおり variance-2 を正面受容)。

**最小コスト経路 (auditor 指摘踏襲)**: sum producer の他 field (pX_sum series `:110-148` / density
`:137-148` / `density_t_eq` `:169-174` / `integrable_deriv` bound `:175-219`) は **genuine で保持
価値あり**。本 plan は `Z_law` field を defect park から genuine に差し替え + v_Z field 充足、他 field
は無改変再利用。

- [ ] sum producer 返り値を general-variance structure (v_Z:=2) に整合させ、`Z_law` を
  `P.map (Z_X+Z_Y) = gaussianReal 0 2` で genuine に閉じる (`hZXZY_law` `:155-161` を直接使用)
- [ ] docstring の `@audit:defect(false-statement)` + `@audit:closed-by-successor(...)` を除去
- [ ] 他 field (pX_sum series / density / density_t_eq / integrable_deriv bound) の再利用結線確認

**残1 (integrable_deriv t-可測性) park との関係**: sum producer `integrable_deriv` (`:200-219`) は
bound 部 (PB-2b Fisher 単調性) genuine、唯一 **t-可測性** (`logDeriv (convDensityAdd …)` lintegral の
parameter measurability、`:206-210`) が `sorry` + `@residual(...)` で park。これは X/Y producer 残1
(`EPICase1RatioLimit.lean:2041` 付近) と **同型障害** (Mathlib parameter-measurability gap)、本 plan
scope 外。`Z_law` closure 後も残る別障害。

- [ ] t-可測性 sorry の `@residual` を整理: `Z_law` closure 後の状態に合わせ、compound から
  defect 由来の `plan:epi-case1-sum-producer-plan` を外し t-可測性 owner に揃える
- [ ] 残1 (X/Y producer t-可測性) と sum の t-可測性が同一 closure に乗るか (同型なら共有補題候補)

**Done 条件**: `Z_law` genuine (defect 除去)、他 field 無改変再利用、t-可測性 park の residual
classification を `Z_law` closure 後の状態に更新。

### GS-A5 — PB-6 wrapper `_full` 結線 + verify/監査

**スコープ**: PB-6 最終 wrapper (`entropyPower_add_ge_case1_of_methodX_unitnoise` or `_full`、未作成、
Phase C wrapper `EPICase1RatioLimit.lean:1498` の後継) への結線順序を general-variance surgery 反映で
更新し、verify + 独立 honesty audit。

**結線順序 (残1 + 本 plan 解決後)**:
1. **残1** (X/Y producer t-可測性、別 plan) → X/Y producer genuine
2. **本 plan** (sum producer `Z_law` genuine、general-variance v_Z=2) → sum producer genuine
   (t-可測性は残1 依存)
3. **PB-5** `h_pos_stam` producer (Stam/Blachman genuine 既存配線、sum がここに刺さる)
4. **PB-6** 最終 wrapper `_full`: X/Y producer (v_Z=1) + sum producer (本 plan、v_Z=2) +
   `IsHeatFlowEndpointRegular` 3 本 (既存 general v=1/v=1/v=2、`EPIStamToBridge.lean:1435-1452`) +
   `h_pos_stam` (PB-5) を注入。general-variance de Bruijn group と `IsHeatFlowEndpointRegular` の
   v_Z 役割 (微分値 vs 連続性) が整合することを確認 (Q-CORE prior art 節)
5. **PB-7** `IsIBPHypothesis` (`FisherInfoV2DeBruijnBody.lean:209`、死 alias) retract

**verify + 独立 honesty audit**:
- [ ] touched file 全件 `lake env lean` silent
- [ ] sum producer + general-variance de Bruijn + 最終 wrapper を `#print axioms` で確認
  (残1 t-可測性 park があれば `sorryAx` 残存 = type-check done、`Z_law` genuine 化で defect 消滅)
- [ ] **独立 honesty audit** (`honesty-auditor` subagent) 起動 (`Z_law` defect → genuine の signature
  意味変化 + general-variance structure surgery で honesty 意味が変わる → CLAUDE.md「Independent
  honesty audit」起動条件)
- [ ] audit verdict 確認:
  - `Z_law : P.map (Z_X+Z_Y) = gaussianReal 0 2` が genuine (v_Z=2 で真の law 受容、defect 解消)
  - **factor-2 ratio-Stam 再導出が genuine** (naive 値据置でなく正しい factor で weight 再導出、
    `*Hypothesis` bundling していない — §解析核判定 (ii) の逆検証)
  - general-variance structure の v_Z field が load-bearing でなく regularity 一般化として正当
  - wrapper の結論 `N(X+Y)≥N(X)+N(Y)` が不変
  - sum producer の他 field が regularity precondition のまま
  - 残1 (t-可測性) park の residual classification が正しい

**Done 条件**: 全 silent + audit verdict 全 OK (or questionable-resolved-inline)。headline proof done
条件 (残1 + 本 plan の解析核 GS-A3 両方 genuine) を明示。

---

## 撤退ライン (2026-06-06 改訂 — b-2 用)

- **L-GS-A0-wall (GS-A0 GATE)**: `proof-pivot-advisor` + 機械検証で factor-2 ratio-Stam 再導出が
  現有資産 (Stam/Blachman 補題群) で **閉じない (wall)** と判定 → **全体 park 恒久化**。`Z_law` defect
  park 維持、本 plan を textbook 別 phase (EPI 解析核 Mathlib 整備待ち) に送り、13-file surgery には
  着手しない (解析核が壁なら plumbing は無駄)。判断ログに wall 判定を記録。
- **L-GS-blast (GS-A1 段階)**: structure surgery の consumer breakage (13 file / 50+ site) が機械的
  v_Z:=1 補完で吸収されず、各証明が carrier `t` / `gaussianReal 0 1` に load-bearing 依存して大幅に
  書換要 → surgery を分割するか、既存 unit structure を残し **新 general-variance structure を別途
  定義** (新旧並存) する route に escalate (判断ログに記録)。
- **L-GS-A3-core (GS-A3 段階)**: factor-2 ratio-Stam 再導出が (GS-A0 で tractable 判定したが) 実装で
  詰まる → 当該 phase を `sorry` + `@residual(plan:epi-case1-debruijn-genvar-struct-plan)` で park
  (signature は `csiszarLogRatioGap_deriv_le_zero` general-variance 形を保つ、honest tier-2 residual)。
  解析核 park で headline closure せず、次 wave 繰り越し。**`*Hypothesis` predicate に核を bundling
  する撤退は禁止** (CLAUDE.md「検証の誠実性」)。factor-2 bound を仮説に抱えさせない。
- **L-GS-integrable (GS-A4 段階)**: 残1 (integrable_deriv t-可測性) は本 plan scope 外。`Z_law`
  closure 後も sum producer は t-可測性 park を残す → headline proof done は残1 closure と協調が必要。
  本 plan 単独では sum producer type-check done (Z_law genuine + t-可測性 park) 止まり。

## genuine closure 可能な範囲 / 別 phase 送りの境界

- **genuine closure 可能 (本 plan scope、GS-A0 tractable 前提)**: sum noise N(0,2) の `Z_law` 型不充足を
  (b-2) general-variance surgery で解消 (`Z_law : P.map (Z_X+Z_Y) = gaussianReal 0 2` を v_Z=2 で受容)、
  かつ **factor-2 ratio-Stam を genuine に再導出** (GS-A3 解析核)。variance-2 は coupling に intrinsic
  (§解析核判定 (i)) なので回避せず正面受容。
- **GS-A0 で wall なら別 phase 送り (本 plan では閉じない)**: factor-2 ratio-Stam 再導出が現有資産で
  閉じなければ、textbook 別 phase (EPI 解析核の Mathlib/in-tree 整備待ち) に送る。plumbing には投資せず
  `Z_law` defect park を恒久維持。
- **残1 依存 (本 plan では閉じない、別 plan へ)**: sum/X/Y producer の `integrable_deriv` t-可測性
  (`logDeriv (convDensityAdd …)` lintegral の parameter measurability)。Mathlib gap、別 owner。
  `Z_law` closure 後も残る別障害。
- **別 phase / textbook 最終版送り**: X/Y producer の `integrable_deriv` bound (PB-2b Fisher 単調性) が
  依存する regular-density + bounded-deriv precondition の general L¹ への緩和 (approximation)。残2 plan
  §境界と同じく textbook 最終版で別 phase。

---

## 参考 file (verbatim file:line)

- `InformationTheory/Shannon/EPICase1SumProducer.lean:88` — sum producer
  `isDeBruijnRegularityHyp_sum_of_methodX_unitnoise` (`Z_law` field を `@audit:defect(false-statement)`
  `:151-168` で park、本 plan が genuine 化する対象)
- `InformationTheory/Shannon/EPICase1SumProducer.lean:110-219` — 再利用可能 genuine field
  (pX_sum series / density / density_t_eq / integrable_deriv bound、`Z_law` 以外保持)
- `InformationTheory/Shannon/EPICase1SumProducer.lean:200-219` — `integrable_deriv` (bound genuine、
  t-可測性 `:206-210` park、残1 同型、GS-A4 で classification 整理)
- `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:205-268` — `IsRegularDeBruijnHypV2`
  structure (`Z_law : gaussianReal 0 1` `:210` + `density_t_eq` carrier `t` `:260-261` が
  v_Z=1 hardcode、Q-CORE field 表)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3437-3473` —
  `debruijnIdentityV2_holds_assembled_entropy_eq` (`hZ_law : gaussianReal 0 1` hardcode `:3440`、
  内部 `pPath_eq_convDensityAdd ... (1:ℝ≥0) ...` `:3452`、carrier `s·1=s` `:3460`、**v_Z 結線の核心**)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3485-3500` —
  `debruijnIdentityV2_holds_assembled_fisher_match` (`density_t_eq` carrier `⟨t,_⟩` で同定、v_Z=1 hardcode)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3397-3414` —
  `debruijnIdentityV2_holds_assembled_chain` (density-level、**v_Z-agnostic**、noise 不参照、
  残2 plan の「_chain は v_Z-agnostic」主張は正しい)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3543-3587` —
  `debruijnIdentityV2_holds_assembled` (3 sub を `h_reg.Z_law` で叩く、v_Z=1 でのみ genuine)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:215-224` —
  `pPath_eq_convDensityAdd` (**general v_Z 受容**、carrier `s·v_Z`、reparam τ=s·v_Z の基盤)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnGenuine.lean:51-61` — `deBruijn_identity_v2`
  (consumer、`(1/2)·J(h_reg.density_t)` を返す)
- `InformationTheory/Shannon/EPIStamToBridge.lean:699-838` — `csiszarLogRatioGap_hasDerivAt`
  (X/Y/sum 3 成分の `density_t` Fisher を消費、`(1/2)` cancel `:773/785/799`、ratio-gap 微分値
  `:712-721`、**v_Z が arith に到達する結線**)
- `InformationTheory/Shannon/EPIStamToBridge.lean:895` — `csiszarLogRatioGap_deriv_le_zero`
  (harmonic Stam ratio core、carrier drift で偽化する地点)
- `InformationTheory/Shannon/EPIStamToBridge.lean:1085-1098` —
  `csiszarLogRatioGap_antitoneOn_Ici_zero` (`IsDeBruijnRegularityHyp` 3本 + `IsHeatFlowEndpointRegular`
  3本を同時消費、prior art 共存点)
- `InformationTheory/Shannon/EPIStamToBridge.lean:1435-1452` — `IsHeatFlowEndpointRegular` producer
  (X→v_Z=1 / Y→v_Z=1 / **sum→v_Z=2 を直接渡す** prior art、端点連続性専用で arith 非到達)
- `InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:488-503` — `IsHeatFlowEndpointRegular`
  structure (`v_Z : ℝ≥0` field + `hZ_law : gaussianReal 0 v_Z`、general-variance だが連続性専用)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1769` 付近 — PB-2 path-id
  `gaussianConvolution_rescale_eq` + `map_gaussianConvolution_rescale_eq` (`v:=2` で W 同定、@audit:ok)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1498` — Phase C wrapper
  `entropyPower_add_ge_case1_of_methodX` (PB-6 `_full`/`_unitnoise` の前身)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1913` —
  `isDeBruijnRegularityHyp_of_methodX_unitnoise` (X/Y producer、pX series plumbing を W=sum noise に流用)
- `InformationTheory/Shannon/EPIL3Integration.lean:1380-1385` — antitone target `csiszarLogRatioGap`
  (sum path `X+Y+√t·(Z_X+Z_Y)` literal `Z_X+Z_Y`、X/Y と単一共有 t — **variance-2 が coupling に
  intrinsic な証拠**、§解析核判定 (i))
- `InformationTheory/Shannon/EPIStamToBridge.lean:919-922` — `csiszarLogRatioGap_deriv_le_zero` の
  `h_conv_id` (sum density を carrier-t の X/Y density の `convDensityAdd` = carrier-2t に同定、
  **variance-2 intrinsic の決定的裏取り**)
- `docs/shannon/proof-log-epi-case1-genvar-struct.md` — **GS-1 probe 結果** (B-τ NO-GO machine-verified、
  item 4d desync、`Z_law` load-bearing trace、b-2 = surviving path、GS-0 inventory)
- `docs/shannon/epi-case1-sum-producer-plan.md` — predecessor plan (sum producer、`Z_law` defect park、
  ルート (a)/(b)/(c) sizing、§問題の核心)
- `docs/shannon/epi-case1-debruijn-producer-fork-sizing.md` — 案A OUT (Q1 ratio 偽化 = **naive 値据置
  一般化が偽**、§解析核判定 (ii) で b-2 の「正しい factor 再導出」と区別) / 案C (reparam) は B-τ で
  REFUTE 済
- `docs/shannon/epi-case1-debruijn-producer-plan.md` — 親 plan (PB-1〜PB-7、残1 設計)
- `docs/audit/audit-tags.md` — `@residual` 語彙 (compound syntax) / `@audit:defect` / `@audit:closed-by-successor`

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-06-06 起草時 — Q-CORE を実コード結線で決着 (本 plan の中心価値)**: 残2 plan の主張
   「Z_law を一般化しても微分値を触らず density を unit-W pin すれば ratio core 偽化を回避」を実機械で
   検証し **不可** と確定。決め手は `debruijnIdentityV2_holds_assembled_entropy_eq`
   (`FisherInfoV2DeBruijnAssembly.lean:3437`) が `hZ_law : gaussianReal 0 1` を **hardcode 引数で取り**、
   内部 `pPath_eq_convDensityAdd ... (1:ℝ≥0) ...` (`:3452`) で path の真の density (carrier `s·v_Z`) を
   `_chain` が解析する density (carrier `s`) に同定していること (`:3460` `hwit1 : s·1=s`)。
   `Z_law = gaussianReal 0 2` にすると carrier `s·2 ≠ s` で drift し、de Bruijn 微分値が
   `(1/2)·J(convDensityAdd pX g_{s·2})` になって ratio core (`:895`、harmonic Stam 項毎 factor 非不変) を
   偽化する。`_chain` 自身は v_Z-agnostic (`:3397`、noise 不参照) なので残2 plan の「_chain は
   density-level」主張は正しいが、`_entropy_eq`/`_fisher_match` の hardcode が `Z_law` 値と density
   carrier を結びつけており、density-pin だけでは救えない。→ **v_Z は ratio core arith に到達する**
   (Q-CORE 答え)。

2. **2026-06-06 — prior art `IsHeatFlowEndpointRegular` 共存は v_Z 安全の証拠にならないと判定**: 残2 plan
   は `IsHeatFlowEndpointRegular` (general v_Z、sum に v_Z=2、`EPIStamToBridge.lean:1447`) の共存を
   ルート (b) の根拠としたが、`csiszarLogRatioGap_antitoneOn_Ici_zero` (`:1085`) はこの structure を
   **端点連続性専用** (`heatFlowEntropyPower_continuousWithinAt_zero`、収束) としてのみ消費し、Fisher
   微分値 (ratio core arith) に到達させない。`IsDeBruijnRegularityHyp` の v_Z は (判断ログ 1 のとおり)
   arith に到達する。2 structure の v_Z は **役割が別** (連続性 vs 微分値) なので、前者の v_Z=2 共存は
   後者の v_Z 一般化を正当化しない。残2 plan の M0' 観察はこの役割差を見落としている。

3. **2026-06-06 — ルート (B-τ) を本命に (fork-sizing 案C と一致)**: Q-CORE 結線で値一般化 (案A/b-2 naive)
   が数学的に通らないことが確定したので、唯一の honest route は **W unit reparam + 時間 τ=t·v_Z で
   chain factor 打消し** (fork-sizing `:67-88` 案C / 案B+τ)。残2 plan が (a) を「path-id は noise law
   救えないので OUT」と判定したのは **wrapper が `Z_X+Z_Y` を thread する形を固定したまま**の判定で、
   (B-τ) は **wrapper noise-W 化** (ルート c を内包) で `Z_law : P.map W = gaussianReal 0 1` を
   genuine に閉じる。W は真に unit なので de Bruijn core (`_assembled`) を無改変で使え、carrier τ で
   ratio core を偽化させない。代償は wrapper noise-W 化 (結論不変、noise は補助変数)。**最終確定は
   GS-1 skeleton で reparam bridge が `Z_law` の noise law 主張を W に切り替えられるか実機械裏取り必須**。

4. **2026-06-06 — sum producer は `Z_law` field 1 個差し替えが最小コスト (auditor 指摘踏襲)**: 他 field
   (pX_sum series / density / density_t_eq / integrable_deriv bound) は genuine で保持価値あり。本 plan は
   `Z_law` defect park (`@audit:defect(false-statement)`) を genuine に差し替えるだけで、他 field 無改変
   再利用。`integrable_deriv` t-可測性 park (残1 同型) は本 plan scope 外で、`Z_law` closure 後も残る
   別障害として GS-A4 で classification を整理。

5. **2026-06-06 — GS-1 probe で route (B-τ) を REFUTE (machine-verified、本改訂の核心)**: B-τ
   (unit-noise `W := (Z_X+Z_Y)/√2 ∼ 𝒩(0,1)` を de Bruijn structure に渡し時間 `τ=2t` reparam) を
   `example` skeleton 6 本で型確認 (実行後 revert、詳細 `proof-log-epi-case1-genvar-struct.md`)。
   **producer 側は genuine** (W-law `P.map W = gaussianReal 0 1` が `gaussianReal_add_gaussianReal_of_indepFun`
   → `gaussianReal_map_div_const` で ~15 行、item 1; W-producer clean 構成 item 2; `reg_at .Z_law`
   obligation も W で genuine 充足 item 3a) だが、**consumer 側が W を受容できない** (item 4d desync)。
   決め手 = W 置換の reparam `τ=2t` が sum path を W-path の time 2t として再表現し、その de Bruijn 微分が
   `h_reg_W.reg_at (2t)` に座って **time 2t で評価**される一方、X/Y 項は time t (`h_reg.reg_at t`)。
   antitone 証明 `csiszarLogRatioGap_hasDerivAt` (`EPIStamToBridge.lean:699`) は 3 成分を **単一共有 t** で
   取るため sum だけ別 time にできず、`reg_at-at-2t` を shared-t 結合に入れるには consumer の `(1/2)·J`
   arithmetic が持たない `2·` chain factor が要る (item 4d、型レベル確認)。さらに probe trace で
   `Z_law=unit` の false が **consumer の微分 arithmetic に load-bearing** と確定 (`:747` →
   `debruijnIdentityV2_holds_assembled` が false unit `Z_law` を消費して variance-2 sum 項の `(1/2)`
   factor を得る)。W はこの false を除去せず time-desync に移すだけ。→ **B-τ NO-GO**、旧 Approach の
   B-τ 本命判定を撤回。

6. **2026-06-06 — route (c) wrapper-W 化も不可 (単一-t signature)**: antitone target `csiszarLogRatioGap`
   (`EPIL3Integration.lean:1380`) は sum path を `X+Y+√t·(Z_X+Z_Y)` (sum noise literal `Z_X+Z_Y`、X/Y と
   同一の単一 t) で **hardcode**。W 化は sum 項に別 time (2t) を要求するが、単一-t signature では「sum
   項だけ別 time」を表現できない。mechanical noise rename でなく antitone object の時間変数 restructuring
   が要り ~93 sum-path sites (3 consumer file + endpoint lemmas + saturation pillar) に伝播。tractable な
   wrapper rename ではないので route c も廃止。

7. **2026-06-06 — route (b-2) general-variance surgery が唯一 surviving honest path に確定 + 解析核の
   wall-vs-tractable 判定を crisp 化**: variance-2 は coupling `(X+Y)+√t·(Z_X+Z_Y) = X_t+Y_t` に
   **intrinsic** (実コード裏取り: `csiszarLogRatioGap` sum path `:1382` が literal `Z_X+Z_Y`、
   `csiszarLogRatioGap_deriv_le_zero` の `h_conv_id` `EPIStamToBridge.lean:919-922` が sum density を
   carrier-t の X/Y density の `convDensityAdd` = carrier-2t に同定)。fresh unit `Z_S` では coupling が
   壊れ Fisher 比較不能 → variance-2 回避は原理的に不可、**正面受容する general-variance structure (b-2)
   が本質的に必要**。解析核 = **factor-2 ratio-Stam 再導出**。fork-sizing Q1 (`:32-40`) の偽化主張は
   「naive 値据置一般化」(値 `(1/2)·J → (v_Z/2)·J` のみ変えて harmonic-Stam weight 据置) を指すと実コード
   再確認 (`csiszarLogRatioGap_deriv_le_zero` `:895` は全成分 unit 前提の `α²≤α` weights)。b-2 が指すのは
   「正しい factor で weight ごと再導出した harmonic-Stam」= 真の EPI の Stam 不等式
   (`1/J(X+Y) ≥ 1/J(X)+1/J(Y)`、Blachman) で **真であるはず**だが genuine 証明を要する。両者を §解析核判定
   (ii) に明記。ただし「真であるはず」は EPI 一般論からの推定で現有資産から factor-2 版が genuine に
   再導出できるかは未確認 → **GS-A0 で `proof-pivot-advisor` gate を最初に置き、解析核が現有資産で閉じるか
   在庫横断確認 + 機械検証で裏取りしてから 13-file surgery に着手する** risk 順序を採用 (解析核が真と
   確認できてから plumbing に投資)。GS phase を GS-A0〜A5 に再構成。`Z_law` defect park
   (`EPICase1SumProducer.lean:166`) は本 wave 進行中維持 (本 plan が closure owner、slug 正当)。

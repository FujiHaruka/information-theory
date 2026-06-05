# Shannon EPI: case-1 sum-noise N(0,2) 構造改変 successor サブ計画

> **Parent**: [`epi-case1-debruijn-producer-plan.md`](epi-case1-debruijn-producer-plan.md) §PB-4 / L-Sum-struct
> **Predecessor**: [`epi-case1-sum-producer-plan.md`](epi-case1-sum-producer-plan.md) (sum producer、`Z_law` を `@audit:defect(false-statement)` で park)
> **Status**: 📋 draft (起草のみ、実装は別 session で `lean-implementer` dispatch)
> **Scope**: docs-only (本 plan); 触る予定の実装 file は per-step 節に列挙
> **proof-log**: yes (実装 session で `docs/shannon/proof-log-epi-case1-genvar-struct.md`)
> **撤退口 slug**: `@residual(plan:epi-case1-debruijn-genvar-struct-plan)`
> (sum producer `EPICase1SumProducer.lean:87` の `@audit:closed-by-successor(epi-case1-debruijn-genvar-struct-plan)` が指す先)

## 進捗

- [x] Q-CORE 結線決着 (v_Z が de Bruijn 微分値→ratio core arith に到達するか実コード verbatim) — 本 plan 内で完了
- [ ] GS-0 在庫: reparam ルートに使う既存資産 (path-id / pPath general-v_Z / FTC reparam lemma) の Mathlib + in-tree verbatim 確認 📋
- [ ] GS-1 採用ルート確定 (B-τ reparam vs b-2 genvar-struct vs c wrapper-W) skeleton 型確認 📋
- [ ] GS-2 採用ルート core: de Bruijn identity を sum noise N(0,2) で genuine に供給する構成 📋
- [ ] GS-3 sum producer の `Z_law` field 差し替え (defect → genuine)、他 field 再利用結線 📋
- [ ] GS-4 残1 (integrable_deriv t-可測性) park との関係確定 + compound residual 整理 📋
- [ ] GS-5 PB-6 最終 wrapper `_full` への結線順序更新 📋
- [ ] GS-V verify (`lake env lean`) + 独立 honesty audit (`honesty-auditor`) PASS 📋

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

→ **正しい道は値一般化 (案A / b-2 naive) でも density-pin だけ (残2 plan) でもなく、
time-reparam で carrier を unit に戻すこと** (fork-sizing 案C / 案B+τ reparam)。これが本 plan の
ルート (B-τ)。詳細は §候補ルート。

---

## ゴール / Approach

### ゴール

sum producer `isDeBruijnRegularityHyp_sum_of_methodX_unitnoise`
(`EPICase1SumProducer.lean:88`) の `Z_law` field の `@audit:defect(false-statement)` park を
**genuine 化**し、`IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` を sum noise N(0,2) で本物に供給する。
これにより case-1 final wrapper `_full` (PB-6) が de Bruijn group を前提から消し、headline EPI
case-1 が proof done (残1 integrable_deriv t-可測性 closure と協調すれば
`[propext, Classical.choice, Quot.sound]`) に届く。

### Approach (全体形)

**核心** = 「sum noise の variance 2 が de Bruijn 微分値 `(1/2)·J` の density carrier に drift して
ratio core を偽化する」問題を、**noise を unit に標準化し時間変数を `τ = t·v_Z` で reparam して
chain factor `v_Z` を打ち消す** (fork-sizing 案C / advisor 推奨) ことで解く。値据置 (案A) でも
density-pin だけ (残2 plan) でもなく、**reparam で carrier を unit に戻す**のが唯一 ratio core を
壊さない道、という Q-CORE 結線の結論に従う。

**何が genuine に閉じるか / 何が壁か**:
- de Bruijn identity の density-level core (`_chain`) は **v_Z-agnostic で既に genuine**
  (Q-CORE 事実 2)。新規解析は不要。
- 障害は純粋に **型レベル + carrier の reparam** (variance 2 を unit `s·2 = τ` で吸収する構成)。
- ただし `_entropy_eq`/`_fisher_match` が `gaussianReal 0 1` hardcode なので、これらを sum で
  使うには **general-variance 版の entropy_eq / fisher_match (v_Z 引数化)** を新規に書くか、
  **path reparam `X+√t·(Z_X+Z_Y) = X+√(2t)·W` (`W := (Z_X+Z_Y)/√2 ∼ 𝒩(0,1)`) で unit-noise
  W を de Bruijn structure に渡し、時間 τ=2t で `density_t` を構成** する。後者が reparam ルート。

3 候補ルート (詳細 §候補ルート):

- **(B-τ)** unit-noise `W := (Z_X+Z_Y)/√2` を de Bruijn structure に渡し、時間変数 `τ = t·v_Z` の
  reparam で chain factor を吸収 (advisor 推奨、fork-sizing 案C)。**本命**。`Z_law` は
  `P.map W = gaussianReal 0 1` で genuine に閉じ (W は真に unit)、path-id (PB-2,
  `gaussianConvolution_rescale_eq`) で `X+√t·(Z_X+Z_Y)` を `X+√(2t)·W` に同定。
- **(b-2)** 既存 `IsRegularDeBruijnHypV2` の `Z_law` を `gaussianReal 0 v_Z` に開き
  (v_Z field 追加)、`_entropy_eq`/`_fisher_match` を general-variance 化。X/Y は v_Z:=1 補完。
  → ratio core 偽化リスク (carrier drift)。**Q-CORE 事実 3 で偽化が確定**するので、
  reparam なしの naive v_Z 開放は OUT。general-variance 版 entropy_eq の microsurgery で
  carrier を `density_t` の reparam に押し込めれば救えるか要検証 (= 実質 (B-τ) に帰着)。
- **(c)** wrapper signature `h_reg_sum : IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` を
  `IsDeBruijnRegularityHyp (X+Y) W P` (unit-W) に書き換え。ratio antitone sum path
  `X+Y+√t·(Z_X+Z_Y)` (`EPIL3Integration.lean`) も W 化。**wrapper 全面改変**。

**第 1 段 (GS-1)**: 3 ルートを skeleton で型確認。(B-τ) の reparam が `density_t` / de Bruijn 微分値 /
ratio core への伝播を壊さないか実機械で確定。

**第 2 段 (GS-2)**: 採用ルートで de Bruijn identity を sum noise で供給する core を構成。

**第 3 段 (GS-3)**: sum producer の `Z_law` field の defect park を genuine に差し替え、他 field
(pX_sum series / density / integrable_deriv bound) を再利用。

**第 4 段 (GS-4/5)**: 残1 (integrable_deriv t-可測性) park との関係を整理し、PB-6 最終 wrapper
`_full` への結線順序を更新。

**撤退口**: 採用ルートで de Bruijn identity が sum noise で genuine に閉じなければ、`Z_law` field の
defect park を維持 (signature は producer 形を保つ) し、closure を次 wave に繰り越す。
`*Hypothesis` predicate に核を bundling する撤退は禁止。

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
**唯一の道は path/time の reparam で carrier を unit に戻すこと** (ルート B-τ)。

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

## 候補ルートの列挙と sizing

### ルート (B-τ) — unit-noise W + 時間 reparam τ=t·v_Z (advisor 推奨 / fork-sizing 案C) — **本命**

**内容**: `W := (Z_X+Z_Y)/√2` (`W ∼ 𝒩(0,1)`、真に unit)。de Bruijn structure には W を渡し、
`Z_law : P.map W = gaussianReal 0 1` を **genuine に閉じる** (W は本当に unit variance なので
defect ではない)。path-id (PB-2 `gaussianConvolution_rescale_eq`,
`EPICase1RatioLimit.lean:1769` 付近、@audit:ok) を `v := 2` で適用し、path
`gaussianConvolution (X+Y) (Z_X+Z_Y) t = gaussianConvolution (X+Y) W (t·2)` (点ごと厳密恒等式) で
sum path を unit-W 形に同定。

**reparam が chain factor を打ち消す機構** (fork-sizing 案C `:81-88` verbatim):
de Bruijn 微分値 `(1/2)·J` は kernel-variance=time の unit reparam 上でのみ genuine。
時間変数を `τ := t·v_Z` に取り替えると `dτ/dt = v_Z` と `(v_Z/2)` が打ち消し合い `(1/2)·J(τ)` に
戻る。W が unit なので `_entropy_eq`/`_fisher_match` の `gaussianReal 0 1` hardcode を **無改変で
使える** (W の law が真に unit、carrier `τ·1 = τ`)。

**何を構成するか**:
- `IsDeBruijnRegularityHyp (X+Y) W P` を X/Y producer 機械
  (`isDeBruijnRegularityHyp_of_methodX_unitnoise`, `EPICase1RatioLimit.lean:1913`) の流用で構成
  (S := X+Y、noise := W、pX_sum series は EPICase1SumProducer の既存 plumbing 再利用)。`Z_law` は
  `P.map W = gaussianReal 0 1` を `W = (Z_X+Z_Y)/√2` の law から genuine に導く。
- これを `IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` (wrapper が要求する形) に橋渡しする
  reparam bridge を 1 本。**ここが本 plan の core 障害**: bridge は path-id (PB-2) で path を
  同一視するが、`reg_at .Z_law` field は依然 `P.map (Z_X+Z_Y) = gaussianReal 0 1` を主張する
  (残2 plan §問題の核心と同じ)。

**(B-τ) が残2 plan の (a) と違う点 — 決定的**: 残2 plan は (a) を「path-id は path のみ、noise law
救えないので OUT」と判定したが、これは **wrapper が `Z_X+Z_Y` を thread する形を固定したまま**の
判定。(B-τ) は **wrapper の noise thread 自体を W に書き換える** (= 実質ルート (c) と融合) ことで
`Z_law : P.map W = gaussianReal 0 1` を genuine に閉じる。つまり (B-τ) = **W reparam + wrapper
noise-W 化**。これなら `Z_law` の type 整合 (W は真に unit) と ratio core 非偽化 (carrier τ で
unit) を **両立**できる。残2 plan が (a) を OUT にしたのは wrapper noise 固定の制約下であり、
wrapper 改変を許せば (B-τ) は生きる。→ **(B-τ) は (c) wrapper-W 化を内包する本命**。

**sizing**: wrapper signature `:1517-1518` の `(fun ω => Z_X ω + Z_Y ω)` を `W` 化。ratio antitone
sum path (`EPIL3Integration.lean` の `csiszarLogRatioGap` body) の `X+Y+√t·(Z_X+Z_Y)` も W 化。
書換範囲は GS-1 で実 grep sizing。**結論には影響なし** (noise は `N(X+Y)≥N(X)+N(Y)` に現れない
補助変数、handoff)。

### ルート (b-2) — `IsRegularDeBruijnHypV2.Z_law` を general-variance 化 — **要 microsurgery、単独 OUT**

**内容**: 既存 structure の `Z_law` を `gaussianReal 0 v_Z` に開き (v_Z field 追加)、
`density_t_eq` の carrier も `⟨t·v_Z,_⟩` に開く。`_entropy_eq`/`_fisher_match` を general-variance
版に書き換え (v_Z 引数化、`pPath_eq_convDensityAdd ... v_Z ...` を呼ぶ)。X/Y は v_Z:=1 補完。

**blast radius (実測済、`EPICase1SumProducer.lean:16-25` header)**:
`IsRegularDeBruijnHypV2` consumer = **13 file / 50+ 件** (`rg -c IsRegularDeBruijnHypV2`)。
`Z_law` + `density_t_eq` の carrier を general-variance 化すると全 consumer の breakage が深刻。
consumer patch が「v_Z:=1 補完」で機械的に済むか、各証明が `Z_law = gaussianReal 0 1` /
`density_t_eq` carrier `t` に依存して書換要かを GS-1 で実機械 sizing。

**ratio core 偽化 (Q-CORE 事実 3 で確定)**: naive に v_Z を開くと carrier drift で de Bruijn
微分値が `(v_Z/2)·J` になり ratio core 偽化。**reparam なしの b-2 は OUT**。救うには
general-variance 版 `_entropy_eq` で carrier を「`density_t` に対する τ reparam」に押し込めるが、
それは実質 (B-τ) に帰着 (carrier を unit τ に戻す)。→ **b-2 単独は OUT、(B-τ) に吸収**。

### ルート (c) — wrapper を unit-noise W で restate — **(B-τ) に内包**

**内容**: §Approach のとおり wrapper signature の noise を W に restate。**(B-τ) が既にこれを
内包**している (B-τ = W reparam + wrapper noise-W 化)。独立ルートとしてではなく (B-τ) の
wrapper 側書換部分として扱う。

### ルート比較表

| 観点 | (B-τ) W + τ reparam ✓ | (b-2) genvar struct | (c) wrapper-W restate |
|---|---|---|---|
| `Z_law` 型整合 | **genuine** (W 真に unit、`gaussianReal 0 1` 無改変) | 可だが carrier drift で ratio 偽化 | (B-τ) に内包 |
| ratio core 偽化 | **回避** (carrier τ で unit、chain factor 打消し) | **偽化** (reparam なし) / 救うと B-τ 帰着 | 回避 (B-τ と同) |
| structure 改変 | なし (既存 unit structure を W で使う) | `Z_law`+`density_t_eq` general-var (大) | なし |
| 影響範囲 | wrapper noise-W 化 + ratio antitone path W 化 | **13 file / 50+ consumer** | wrapper + ratio antitone |
| de Bruijn core 再利用 | `_assembled` 無改変 (W unit) | `_entropy_eq`/`_fisher_match` 書換要 | `_assembled` 無改変 |
| prior art | PB-2 path-id 既存 | `IsHeatFlowEndpointRegular` (但し役割別、Q-CORE) | — |
| 推奨 | **本命** | 単独 OUT (B-τ 帰着) | (B-τ) の wrapper 部分 |

**推奨 = (B-τ)**: de Bruijn core (`_assembled`) を **無改変**で使え (W が真に unit)、ratio core を
carrier τ reparam で偽化させず、structure 改変ゼロ。代償は wrapper noise-W 化 (結論不変)。
**Q-CORE 結線で「v_Z は arith に到達する」が確定したので、値一般化 (b-2 naive) は数学的に通らず、
reparam (B-τ) が唯一の honest route**。fork-sizing advisor の推奨 (案C / 案B+τ reparam) と一致。
**ただし最終確定は GS-1 skeleton 型確認で実機械決着** (reparam bridge が `reg_at .Z_law` field の
noise law 主張を救えるか — wrapper noise-W 化後に `Z_law` 対象が W になるか実機械で裏取り必須)。

---

## Phase 詳細

### GS-0 — reparam ルート在庫 (read-only verbatim 確認)

**スコープ**: (B-τ) に使う既存資産を verbatim 確認 (新規 sorry なし)。`docs/shannon/` の
`mathlib-inventory` 慣行に従い structured per-lemma 出力。

- [ ] PB-2 path-id `gaussianConvolution_rescale_eq` + `map_gaussianConvolution_rescale_eq`
  (`EPICase1RatioLimit.lean:1769` 付近) の `v := 2` 適用での結論形 verbatim
- [ ] `pPath_eq_convDensityAdd` general v_Z 版 (`FisherInfoV2DeBruijnPerTime.lean:215`) の
  v_Z 引数 + carrier `s·v_Z` 結論 verbatim (reparam で τ=s·v_Z に使う)
- [ ] `W := (Z_X+Z_Y)/√2` の law `P.map W = gaussianReal 0 1` を導く Mathlib lemma 在庫
  (loogle `gaussianReal`, scaling/`Measure.map` const-mul) — `gaussianReal 0 2` を `/√2` で unit 化
- [ ] FTC reparam (時間 affine `τ=t·v_Z` の `HasDerivAt` chain) の Mathlib lemma 在庫
  (loogle `HasDerivAt` + `comp` / affine、`dτ/dt=v_Z` factor)
- [ ] sum producer の再利用可能 genuine field (pX_sum series / density / integrable_deriv bound)
  の verbatim 位置 (`EPICase1SumProducer.lean:110-219`)

**Done 条件**: 各資産の `file:line` + verbatim signature ([...] type-class verbatim) を
`docs/shannon/epi-case1-genvar-struct-inventory.md` に記録 (mathlib-inventory dispatch、本 plan は
docs-only なので inventory file 書込みは `mathlib-inventory` agent に委譲)。

### GS-1 — 採用ルート確定 (skeleton 型確認)

**スコープ**: (B-τ)/(b-2)/(c) を skeleton (`:= by sorry`) で型枠だけ書き、reparam bridge が
`reg_at .Z_law` の noise law 主張を救えるかを LSP / `lake env lean` で実機械確認。

- [ ] (B-τ) wrapper noise-W 化後の `h_reg_sum` 型が `IsDeBruijnRegularityHyp (X+Y) W P` になり、
  `reg_at .Z_law` obligation が `P.map W = gaussianReal 0 1` (genuine 充足可能) に変わることを
  `show` で実機械確認
- [ ] (B-τ) reparam bridge: `IsDeBruijnRegularityHyp (X+Y) W P` から path-id で
  `IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` を構成しようとして `Z_law` が `Z_X+Z_Y` law
  (= `gaussianReal 0 2`) に戻る型不充足が **残るか消えるか** を確認 (wrapper を W thread に
  書き換えれば消える、`Z_X+Z_Y` thread のままなら残る)
- [ ] (b-2) `IsRegularDeBruijnHypV2.Z_law` を `gaussianReal 0 v_Z` に開いたときの 13 file / 50+
  consumer breakage を `lake env lean` で実測 (v_Z:=1 補完で通るか)
- [ ] (c) wrapper signature noise-W 化の grep sizing (`csiszarLogRatioGap` body の `Z_X+Z_Y`
  出現箇所、`EPIL3Integration.lean` + `EPIStamToBridge.lean`)

**Done 条件**: (B-τ)/(b-2)/(c) のどれが breakage 最小かつ ratio core 非偽化かを実測した上で採用
ルート確定、判断ログに記録。`Z_law` が genuine に閉じるルートを 1 本確定。

### GS-2 — 採用ルート core (de Bruijn identity を sum noise で供給)

**スコープ**: 採用ルート ((B-τ) 想定) で de Bruijn identity を sum noise N(0,2) 経路で genuine に
供給する構成を実装。

(B-τ) 採用想定の構成:
- `W := (Z_X+Z_Y)/√2` の measurability + `P.map W = gaussianReal 0 1` (GS-0 在庫の scaling lemma)
- `IsDeBruijnRegularityHyp (X+Y) W P` を `isDeBruijnRegularityHyp_of_methodX_unitnoise`
  (S=X+Y, noise=W) で構成 (pX_sum series 再利用)
- wrapper noise-W 化後、ratio core / de Bruijn identity が W path 上で動くことを確認
  (`_assembled` は W unit なので無改変)

**honesty 判定**: `Z_law : P.map W = gaussianReal 0 1` は **genuine** (W は真に unit、defect 解消)。
reparam は path-id (点ごと厳密恒等式、PB-2 @audit:ok) で局所化し ratio core に到達させない
(carrier τ で unit)。`*Hypothesis` predicate に核を bundling しない。

**撤退ライン**: reparam bridge が genuine に閉じなければ `Z_law` を `sorry` +
`@residual(plan:epi-case1-debruijn-genvar-struct-plan)` で park (signature は producer 形を保つ)。
defect 形 (`@audit:defect(false-statement)`) ではなく honest tier-2 residual に格上げ
(本 plan が closure owner なので slug が closure を約束できる、`@residual(plan:...)` が正当)。

**Done 条件**: de Bruijn identity が sum noise 経路で type-check done。genuine に閉じれば
`Z_law` defect 解消 (proof done 候補)。

### GS-3 — sum producer `Z_law` 差し替え + 他 field 再利用結線

**スコープ**: `EPICase1SumProducer.lean` の sum producer の `Z_law` field park
(`:151-168`、`@audit:defect(false-statement)`) を GS-2 の genuine 構成に差し替え。

**最小コスト経路 (auditor 指摘)**: sum producer の他 field
(pX_sum series `:110-148` / density `:137-148` / `density_t_eq` `:169-174` /
`integrable_deriv` bound `:175-219`) は **genuine で保持価値あり** (auditor 曰く field 1 個
差し替えが最小コスト)。本 plan は `Z_law` field **1 個のみ** を defect park から genuine に
差し替え、他 field は無改変で再利用。

- [ ] (B-τ) 採用時: producer 返り値型が wrapper の noise-W 化と整合する形に (W thread)。
  `Z_law` を `P.map W = gaussianReal 0 1` で genuine に閉じる
- [ ] docstring の `@audit:defect(false-statement)` + `@audit:closed-by-successor(...)` を除去
  (defect 解消)、genuine 化を反映
- [ ] 他 field (pX_sum series / density / density_t_eq / integrable_deriv bound) の再利用結線確認

**Done 条件**: sum producer の `Z_law` が genuine (or honest tier-2 residual)、他 field 無改変
再利用、`@audit:defect` 除去。

### GS-4 — 残1 (integrable_deriv t-可測性) park との関係確定

**スコープ**: 本 plan が `Z_law` を closure しても、`integrable_deriv` の **t-可測性** が別障害として
残るかを確定。

**残1 との関係 (handoff + sum producer 実コード)**: sum producer の `integrable_deriv`
(`EPICase1SumProducer.lean:200-219`) は **bound 部 (PB-2b Fisher 単調性 `fisherInfoOfDensityReal_convDensityAdd_le`)
は genuine** で、唯一 **`t`-可測性** (`logDeriv (convDensityAdd …)` lintegral の parameter
measurability、`:206-210`) が `sorry` + `@residual(plan:epi-case1-sum-producer-plan,plan:epi-case1-debruijn-producer-plan)`
で park 中。これは X/Y producer 残1 (`EPICase1RatioLimit.lean:2041` 付近) と **同型障害**
(Mathlib に `logDeriv (convDensityAdd …)` の parameter-measurability lemma 不在)。

**確定すべきこと**: 本 plan (`Z_law` closure) は **integrable_deriv の t-可測性を closure しない**。
これは sum/X/Y 共通の別障害 (残1) で、別 owner (`epi-case1-debruijn-producer-plan` の残1 設計 or
Mathlib parameter-measurability 壁)。本 plan が `Z_law` を genuine 化しても、headline proof done
には残1 (t-可測性) closure が **別途必要**。

- [ ] sum producer `integrable_deriv` の t-可測性 sorry の `@residual` を整理:
  `Z_law` closure 後も残るので、compound から `plan:epi-case1-sum-producer-plan` (defect 由来)
  を外し、t-可測性が指す owner (残1 plan or 新 measurability wall) に揃える
- [ ] 残1 (X/Y producer t-可測性) と sum の t-可測性が同一 closure に乗るか確認 (同型なら共有
  closure 補題候補)

**Done 条件**: 残1 (t-可測性) が本 plan scope 外であることを明示、`integrable_deriv` の residual
classification を `Z_law` closure 後の状態に更新。

### GS-5 — PB-6 最終 wrapper `_full` への結線順序更新

**スコープ**: PB-6 最終 wrapper (`entropyPower_add_ge_case1_of_methodX_unitnoise` or `_full`、
**未作成**、Phase C wrapper `entropyPower_add_ge_case1_of_methodX` `EPICase1RatioLimit.lean:1498` の
unitnoise 版) への結線順序を本 plan の sum producer genuine 化を反映して更新。

**結線順序 (残1 + 本 plan 解決後)**:
1. **残1** (X/Y producer t-可測性、別 plan) → X/Y producer genuine
2. **本 plan** (sum producer `Z_law` genuine、reparam B-τ) → sum producer genuine (t-可測性は残1 依存)
3. **PB-5** `h_pos_stam` producer (Stam/Blachman genuine 既存配線)。sum がここに刺さる
   (`h_pos_stam` sum conjunct が sum producer の density 形を参照)
4. **PB-6** 最終 wrapper `_full`: X/Y producer + sum producer (本 plan、W reparam 後の noise-W 形) +
   `IsHeatFlowEndpointRegular` 3 本 (既存 general variance v=1/v=1/v=2、`EPIStamToBridge.lean:1435-1452`) +
   `h_pos_stam` (PB-5) を注入。**(B-τ) で wrapper noise を W 化した場合、`IsHeatFlowEndpointRegular`
   sum (v_Z=2) と de Bruijn group (W unit) の noise が別になる**ことを確認 (連続性は元 noise
   `Z_X+Z_Y` の v_Z=2、微分値は W unit — 役割別なので両立、Q-CORE prior art 節)
5. **PB-7** `IsIBPHypothesis` (`FisherInfoV2DeBruijnBody.lean:209`、死 alias) retract

**Done 条件**: PB-6 結線順序が本 plan の sum producer genuine 化 + (B-τ) wrapper noise-W 化を
反映した形に更新。headline proof done 条件 (残1 + 本 plan 両方 genuine) を明示。

### GS-V — verify + 独立 honesty audit

- [ ] touched file 全件 `lake env lean` silent
- [ ] sum producer + (B-τ) reparam + 最終 wrapper を `#print axioms` で確認 (残1 t-可測性 park が
  あれば `sorryAx` 残存 = type-check done、`Z_law` genuine 化で defect 消滅)
- [ ] **独立 honesty audit** (`honesty-auditor` subagent) 起動 (`Z_law` defect → genuine の signature
  意味変化 + (B-τ) structure/wrapper 改変で honesty 意味が変わる → CLAUDE.md「Independent honesty
  audit」起動条件)
- [ ] audit verdict 確認:
  - `Z_law : P.map W = gaussianReal 0 1` が genuine (W が真に unit、defect 解消、`@audit:defect`
    除去が正当)
  - (B-τ) reparam が ratio core を偽化しない (carrier τ で unit、`density_t` の Fisher が arith に
    入る値が unit 形のまま — Q-CORE 結線の逆検証)
  - wrapper noise-W 化が結論 `N(X+Y)≥N(X)+N(Y)` を変えない (noise は補助変数)
  - sum producer の他 field が load-bearing bundling でない regularity precondition のまま
  - 残1 (t-可測性) park の residual classification が正しい (本 plan closure 後の状態)

**Done 条件**: 全 silent + audit verdict 全 OK (or questionable-resolved-inline)。

---

## 撤退ライン

- **L-GS-route (GS-1 段階)**: (B-τ) wrapper noise-W 化でも `reg_at .Z_law` の noise law 主張が
  W に切り替わらない (path-id が `Z_law` field の主張対象を救えない) と skeleton で判明 → (b-2)
  general-variance microsurgery に escalate。(b-2) も ratio core 偽化が reparam なしで避けられない
  なら、`Z_law` defect park を維持し closure を次 wave に繰り越す (判断ログに記録)。
- **L-GS-reparam (GS-2 段階)**: (B-τ) の reparam bridge (W → Z_X+Z_Y path-id) が `density_t` の
  carrier 整合 / de Bruijn 微分値 / ratio core への伝播を skeleton で壊すと判明 → `Z_law` を
  `sorry` + `@residual(plan:epi-case1-debruijn-genvar-struct-plan)` で park (defect 形から honest
  tier-2 residual に格上げ、本 plan が closure owner なので slug が正当)。**`*Hypothesis` predicate
  に核を bundling する撤退は禁止** (CLAUDE.md「検証の誠実性」)。
- **L-GS-blast (GS-1 段階)**: (b-2) の blast radius が想定 (13 file / 50+ consumer) を超えて深刻
  (consumer 各証明が `Z_law`/`density_t_eq` carrier に load-bearing 依存して機械的補完が効かない)
  → (B-τ) に戻す (structure 無改変ルート)。(B-τ) ↔ (b-2) escalate は wrapper 改変量 vs consumer
  breakage のトレードオフで判断。
- **L-GS-integrable (GS-4 段階)**: 残1 (integrable_deriv t-可測性) は本 plan scope 外。`Z_law`
  closure 後も sum producer は t-可測性 park を残す → headline proof done は残1 closure と協調が必要。
  本 plan 単独では sum producer type-check done (Z_law genuine + t-可測性 park) 止まり。

## genuine closure 可能な範囲 / 別 phase 送りの境界

- **genuine closure 可能 (本 plan scope)**: sum noise N(0,2) の `Z_law` 型不充足を (B-τ) (W unit
  reparam + wrapper noise-W 化) で解消し、`Z_law : P.map W = gaussianReal 0 1` を genuine に閉じる
  部分。de Bruijn core (`_assembled`) は W unit で無改変、reparam は path-id (PB-2 @audit:ok) で
  局所化。
- **残1 依存 (本 plan では閉じない、別 plan へ)**: sum/X/Y producer の `integrable_deriv` t-可測性
  (`logDeriv (convDensityAdd …)` lintegral の parameter measurability)。Mathlib gap、別 owner。
  `Z_law` closure 後も残る別障害。
- **別 phase / textbook 最終版送り**: (B-τ) で X/Y producer の `integrable_deriv` bound (PB-2b
  Fisher 単調性) が依存する regular-density + bounded-deriv precondition の general L¹ への緩和
  (approximation)。残2 plan §境界と同じく textbook 最終版で別 phase。

---

## 参考 file (verbatim file:line)

- `InformationTheory/Shannon/EPICase1SumProducer.lean:88` — sum producer
  `isDeBruijnRegularityHyp_sum_of_methodX_unitnoise` (`Z_law` field を `@audit:defect(false-statement)`
  `:151-168` で park、本 plan が genuine 化する対象)
- `InformationTheory/Shannon/EPICase1SumProducer.lean:110-219` — 再利用可能 genuine field
  (pX_sum series / density / density_t_eq / integrable_deriv bound、`Z_law` 以外保持)
- `InformationTheory/Shannon/EPICase1SumProducer.lean:200-219` — `integrable_deriv` (bound genuine、
  t-可測性 `:206-210` park、残1 同型、GS-4 で classification 整理)
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
- `docs/shannon/epi-case1-sum-producer-plan.md` — predecessor plan (sum producer、`Z_law` defect park、
  ルート (a)/(b)/(c) sizing、§問題の核心)
- `docs/shannon/epi-case1-debruijn-producer-fork-sizing.md` — 案A OUT (Q1 ratio 偽化) / 案C 推奨
  (`:67-88` reparam τ=t·v_X で chain factor 打消し、本 plan B-τ の数学的根拠)
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
   別障害として GS-4 で classification を整理。

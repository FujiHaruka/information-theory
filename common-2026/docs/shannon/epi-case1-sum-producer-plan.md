# Shannon EPI: case-1 sum-instance de Bruijn producer サブ計画 (L-Sum-struct closure)

> **Parent**: [`epi-case1-debruijn-producer-plan.md`](epi-case1-debruijn-producer-plan.md) §PB-4 / L-Sum-struct
> **Status**: ✅ CLOSED (2026-06-06、superseded by `epi-case1-twotime-restructure-plan`、producer dead 削除、判断ログ #5)
> **Scope**: docs-only (本 plan); 触る予定の実装 file は per-step 節に列挙
> **proof-log**: yes (実装 session で `docs/shannon/proof-log-epi-case1-sum-producer.md`)
> **撤退口 slug**: `@residual(plan:epi-case1-sum-producer-plan)`

## 進捗

- [x] M0 verbatim 型不一致確認 (`Z_law` unit-hardcode vs sum N(0,2)) — 本 plan 内で完了
- [x] M0' 隣接 structure (`IsHeatFlowEndpointRegular`) の general-variance 形 verbatim 確認 — 本 plan 内で完了
- [ ] M1 候補ルート (a)/(b)/(c) の skeleton 型確認 (どれが型整合するか実機械で確定) 📋
- [ ] PS-1 sum producer skeleton: `isDeBruijnRegularityHyp_sum_of_methodX_unitnoise` 型枠 📋
- [ ] PS-2 採用ルートで `reg_at` を構成 (genuine or park 判定) 📋
- [ ] PS-3 `density_t_eq` / `integrable_deriv` 結線 (残1 と同型障害か検証) 📋
- [ ] PS-4 PB-6 最終 wrapper への結線確認 (sum 引数が刺さる位置) 📋
- [ ] PS-V verify (`lake env lean`) + 独立 honesty audit (`honesty-auditor`) PASS 📋

## 文脈 (確定背景)

親 plan `epi-case1-debruijn-producer-plan.md` の **残2 = L-Sum-struct**。
case-1 final wrapper `entropyPower_add_ge_case1_of_methodX`
(`EPICase1RatioLimit.lean:1498`、PB-1 restate 済) は X/Y producer に加え
**sum producer** `h_reg_sum : IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` を要求する
(`EPICase1RatioLimit.lean:1517-1518`、verbatim)。

unit noise (`Z_X, Z_Y ∼ 𝒩(0,1)`、PB-1 で確定) でも、独立 Gaussian の和は
**`Z_X+Z_Y ∼ gaussianReal 0 2`** (variance 2)。これは wrapper body 内で
`hZXZY_law : P.map (fun ω => Z_X ω + Z_Y ω) = gaussianReal 0 (v_X + v_Y)`
(`EPICase1RatioLimit.lean:1595`、`v_X = v_Y = 1` で `1+1=2`、verbatim 確認済) として
実際に導出されている。

X/Y producer (`isDeBruijnRegularityHyp_of_methodX_unitnoise`、`EPICase1RatioLimit.lean:1913`)
は PB-3 で landed (`integrable_deriv` のみ残1 park)。sum はこの producer 機械を
**そのまま流用できない** — noise law が unit でないため (下記 §「問題の核心」)。

### 残1 との依存関係 (handoff 指摘)

handoff `.claude/handoff.md` の指摘: 「残1 (`integrable_deriv` 設計(b)) が閉じても
**sum がこれなので headline 未完**」。本 plan が L-Sum-struct を閉じない限り、最終 wrapper
`_full` (PB-6) は de Bruijn group 前提を残し proof done に届かない。残1 + 残2 の
**両方** が headline EPI case-1 genuine closure の blocker。

**検証項目 (本 plan で確定すべき)**: sum producer も残1 と **同じ `integrable_deriv` 障害を
持つか**。sum の density は `convDensityAdd pX_sum g_{s·2}` (variance 2) で、X/Y の
`convDensityAdd pX g_s` (variance 1) と **構造同型**だが variance carrier が `2`。
`integrable_deriv` 障害 (general L¹ `pX` の Fisher 単調性 gap / t=0 近傍非有界) は
variance 2 でも同じ root cause で残るはず。→ PS-3 で実機械確認 (予測でなく skeleton で裏取り)。

---

## 問題の核心 — 正確な型不一致 (verbatim)

### `IsRegularDeBruijnHypV2.Z_law` の unit hardcode

```lean
-- FisherInfoV2DeBruijn.lean:205-210 (verbatim)
structure IsRegularDeBruijnHypV2 {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P]
    (t : ℝ) where
  /-- `Z` is standard normal. -/
  Z_law : P.map Z = gaussianReal 0 1     -- ← unit variance ハードコード (:210)
  …
```

### `IsDeBruijnRegularityHyp.reg_at` が unit を継承

```lean
-- EPIStamDischarge.lean:262 (verbatim)
reg_at : ∀ t : ℝ, 0 < t →
  InformationTheory.Shannon.FisherInfoV2.IsRegularDeBruijnHypV2 X Z P t
```

`IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` を構成するには、各 `t>0` で
`reg_at t ht : IsRegularDeBruijnHypV2 (X+Y) (Z_X+Z_Y) P t` を埋める必要があり、
その `Z_law` field は **`P.map (Z_X+Z_Y) = gaussianReal 0 1`** を主張する。

### 衝突

sum noise の実際の law は `P.map (Z_X+Z_Y) = gaussianReal 0 2`
(`EPICase1RatioLimit.lean:1595`、`gaussianReal_add_gaussianReal_of_indepFun` 経由、verbatim)。
`gaussianReal 0 1 ≠ gaussianReal 0 2` (variance 1 ≠ 2)。よって sum producer の `Z_law`
field を埋めようとすると **`gaussianReal 0 1 = gaussianReal 0 2` を証明せよ** という
型不充足が出る (FALSE、`gaussianReal` は variance で区別される)。

### path-identification (PB-2) が救えない理由

PB-2 `gaussianConvolution_rescale_eq` (`EPICase1RatioLimit.lean:1769` 付近、@audit:ok 済) は
`gaussianConvolution X Z' (t·v) = gaussianConvolution X Z t` (`Z' = Z/√v`、点ごと厳密恒等式)
として **path (関数) を同一視**する。だが `Z_law` field は path ではなく
**noise `Z_X+Z_Y` の law を直接主張**する (`P.map (Z_X+Z_Y) = …`)。path-identification は
`X+Y+√t·(Z_X+Z_Y)` を `X+Y+√(2t)·W` (`W = (Z_X+Z_Y)/√2 ∼ 𝒩(0,1)`) に書き換えられるが、
`Z_law` が要求するのは **元の noise `Z_X+Z_Y` の law** であって、reparam した `W` の law では
ない。よって path を unit-W 形にしても `Z_law : P.map (Z_X+Z_Y) = gaussianReal 0 1` の
型不充足は残る (親 plan B-0 末尾の系、verbatim 再確認済)。

### 案A (structure の Z_law 値一般化) が不可な理由 — 再掲 (親 fork-sizing doc)

`Z_law` を `gaussianReal 0 v_Z` に一般化すると、de Bruijn 微分値が chain rule で
`(1/2)·J → (v_Z/2)·J` になり、ratio core `csiszarLogRatioGap_deriv_le_zero`
(`EPIStamToBridge.lean:895`) の harmonic-Stam arith が項毎 factor 非一律
(X→v_X, Y→v_Y, sum→v_X+v_Y) で **偽化** する
(`epi-case1-debruijn-producer-fork-sizing.md` Q1、verbatim)。
→ **structure 全体の Z_law 値一般化は OUT** (X/Y/sum 共通 structure を触ると ratio core が壊れる)。

---

## ゴール / Approach

### ゴール

case-1 final wrapper が thread する `h_reg_sum : IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` を
方針X (unit-noise) の前提から **sum producer 補題として供給**する。X/Y producer
(PB-3、genuine 化見込み + integrable_deriv park) に sum producer を加え、最終 wrapper
`_full` の前提から de Bruijn group を消す道を完成させる (残1 と協調)。

### Approach (全体形)

**核心** = sum noise `Z_X+Z_Y ∼ 𝒩(0,2)` が `IsRegularDeBruijnHypV2.Z_law` の
unit-hardcode と型不充足である問題を、**3 候補ルートの skeleton 型確認で実機械決着**させ、
**最も honest かつ structure を局所改変で済むルート** を採る、という 1 点に尽きる。

問題は純粋に **型レベル** (`gaussianReal 0 1` vs `gaussianReal 0 2`) であり、解析核 (de Bruijn
identity の density-level core) は親 M0 で **v_Z-agnostic** と確認済み
(`FisherInfoV2DeBruijnAssembly.lean:3397` `_chain` は density-level、Z_law を chain に
渡さない)。よって sum を閉じる障害は「**型を整合させる構成の選び方**」のみで、新規解析は
原則不要 (integrable_deriv の残1 障害を除く)。

**重要な構造的観察 (M0' で verbatim 確認)**: 隣接 structure `IsHeatFlowEndpointRegular`
(`EPIG2HeatFlowContinuity.lean:352`) は **general `v_Z : ℝ≥0` field + `hZ_law : P.map Z =
gaussianReal 0 v_Z`** を持ち、既存 producer pattern (`EPIStamToBridge.lean:1447`) が
sum に **`v_Z := 2` を直接渡して** 構成している。つまり「sum noise N(0,2) を受容する
general-variance structure 形」は de Bruijn line に **既に prior art が存在**する。
`IsRegularDeBruijnHypV2` だけが unit-hardcode で取り残されている。これがルート (b) の根拠。

3 候補ルート (詳細は次節):

- **(a)** unit-normalized noise `W := (Z_X+Z_Y)/√2` + time-reparam で sum 項を再構成
  (handoff 候補)。→ 型不充足は救えない見込み (path-id は path を同一視するが Z_law は noise
  law 直接、§問題の核心)。skeleton で確認して棄却 or 限定採用。
- **(b)** sum 専用の `Z_law` general-variance 版 structure を別途定義 (案A を **sum singleton に
  限定**)。X/Y は unit structure に触らず sum だけ general-variance instance を作る。
  ratio core 偽化を避けられるか (sum 単独では項毎 factor が無いので偽化しないか) を検証。
  → **本命候補**。`IsHeatFlowEndpointRegular` の prior art と整合。
- **(c)** X+Y を直接「a.c.+finite-var input」として X/Y producer 機械を再利用し、noise を
  補助変数として吸収 (sum を 1 つの input `S := X+Y` と見なし、その上の unit-noise producer)。

**第 1 段 (M1/PS-1)**: 3 ルートを skeleton で型確認。`Z_law` field が型整合するのは
(b)/(c) のどちらか、(a) は救えないことを実機械で確定。

**第 2 段 (PS-2)**: 採用ルートで `reg_at` を構成。(b) なら sum 専用 general-variance
structure (`IsRegularDeBruijnHypV2Sum` 等、新規 or 既存 `Z_law` field のみ開く) を定義し、
**微分値 `(1/2)·J` は触らない** (chain factor は producer 内 `density_t` の variance carrier
`s·2` に閉じ込め、ratio core に到達させない — 親 B-0 系)。(c) なら `S := X+Y` の unit-noise
producer を `isDeBruijnRegularityHyp_of_methodX_unitnoise` に委譲。

**第 3 段 (PS-3)**: `density_t_eq` + `integrable_deriv` を結線。**残1 と同型障害の検証**:
sum の `integrable_deriv` も general L¹ `pX_sum` の Fisher 単調性 gap を持つはず
(variance 2 でも root cause 同一) → 残1 の closure 設計 (b) (regular density + bounded-deriv
precondition 強化) が sum にも必要。残1 が閉じる設計を sum にも適用する。

**第 4 段 (PS-4/PB-6)**: 最終 wrapper `_full` で sum producer を `h_reg_sum` 位置に注入。

**撤退口**: 採用ルートで sum の `reg_at` が genuine に閉じなければ、`reg_at` を `sorry` +
`@residual(plan:epi-case1-sum-producer-plan)` で park (signature は producer 形を保つ)。
`*Hypothesis` predicate に核を bundling する撤退は禁止。

---

## 候補ルートの列挙と sizing

### ルート (a) — unit-normalized noise + time-reparam (handoff 候補) — **見込み薄**

**内容**: `W := (Z_X+Z_Y)/√2` (`W ∼ 𝒩(0,1)`)。path-identification
`gaussianConvolution (X+Y) W (t·2) = gaussianConvolution (X+Y) (Z_X+Z_Y) t`
(PB-2 を `v := 2` で適用、点ごと厳密恒等式) で sum path を unit-W 形に書き換える。

**ratio-core 偽化回避の検証軸**:
- path-identification は **点ごと厳密恒等式** (親 B-0、`Real.sqrt_mul` + `√v≠0`)。これ自体は
  壁ゼロ・偽化しない。
- だが reparam factor `t→t·2` が `HasDerivAt` に chain factor `2` を持ち込む懸念
  (fork-sizing Q2)。**ただし** consumer `deBruijn_identity_v2 (X+Y) (Z_X+Z_Y)` は元 noise
  `Z_X+Z_Y` の時間 `s` に対する `(1/2)·J(density_t)` を要求し、producer の `reg_at` が返す
  `density_t` がその `s` の conv density に一致していれば chain factor は producer 内 density に
  局所化される (親 B-0 系)。

**OUT 判定 (型不充足、救えない)**: § 問題の核心で確定したとおり、`reg_at t ht` の
`Z_law` field は **`P.map (Z_X+Z_Y) = gaussianReal 0 1`** を主張する。path を `W` 形に
書き換えても `Z_law` field の主張対象は **元 noise `Z_X+Z_Y` の law** (= `gaussianReal 0 2`)
であって `W` の law ではない。path-identification は **path (関数) のみ** 同一視し、`Z_law` の
**noise law 主張** は救えない。→ ルート (a) 単独では `Z_law` 型不充足が残る。

**限定採用の余地**: ルート (a) の path-id は **ルート (b)/(c) の internal で使う**
(general-variance structure の density を unit-W core に乗せる / `S := X+Y` の conv density 構成)。
よって (a) は「単独 closure ルートとしては OUT、(b)/(c) の補助具としては有用」。

### ルート (b) — sum 専用 general-variance structure (案A の sum singleton 限定) — **本命**

**内容**: `IsRegularDeBruijnHypV2.Z_law` を sum だけ general-variance 化する。具体的には
2 つの sub-form を skeleton で評価:

- **(b-1)** 新規 structure `IsRegularDeBruijnHypV2Sum` (or `…GenVar`) を sum 専用に定義し、
  `Z_law : P.map Z = gaussianReal 0 v_Z` (v_Z field 付き) とする。`IsDeBruijnRegularityHyp` の
  sum 版 `IsDeBruijnRegularityHypSum` を作り wrapper の `h_reg_sum` 型をそれに差し替え。
- **(b-2)** 既存 `IsRegularDeBruijnHypV2` の `Z_law` field **だけ** を `gaussianReal 0 v_Z` に
  開き (v_Z field 追加)、X/Y は `v_Z := 1` で渡して既存 consumer を不変に保つ。

**ratio core 偽化を避けられるか — 検証軸 (決定的)**:
案A 全体一般化が偽化したのは、ratio core `csiszarLogRatioGap_deriv_le_zero`
(`EPIStamToBridge.lean:895`) が **X/Y/sum 3 成分の微分値を同時に** harmonic-Stam arith に
入れ、各成分の v_Z factor が **非一律** (v_X/v_Y/v_X+v_Y) だと α²≤α weights が破れるため
(fork-sizing Q1)。

ルート (b) の鍵: **X/Y は unit (v_Z=1) のまま、sum だけ v_Z=2**。だが ratio core が見るのは
**`(1/2)·J` の cancellation 後の `J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y)`**
(`(1/2)` は `2·(1/2)=1` で消える、fork-sizing Q1)。ここで:
- **微分値 `(1/2)·J` を触らなければ偽化しない**。ルート (b) は `Z_law` field のみ開き、
  **conv-pin variance (`density_t` の `s·v_Z`) と微分値 `(1/2)·J` は触らない**。sum の
  `density_t` を **path-identification (ルート a) で unit-W 形** (`convDensityAdd pX_sum g_s`、
  variance carrier を `s` に保つ) に pin すれば、consumer が見る微分値は `(1/2)·J(density_t)`
  のまま。これは親 B-0 系・撤退ライン L-Sum-struct の「`Z_law` field のみ general-variance 化し
  微分値 `(1/2)·J` を保つ」設計と一致。
- **検証必須**: sum の `density_t` を unit-W 形に pin したとき、`Z_law : gaussianReal 0 2` を
  field に持ちつつ density は variance-`s` 形 (W 側) になる — この **field 値と density 形の
  分離** が型整合し、かつ consumer `deBruijn_identity_v2 (X+Y) (Z_X+Z_Y)` が要求する微分値と
  一致するかを skeleton で確認。

**sizing**: (b-2) は structure 1 field 追加 + consumer 全件に `v_Z := 1` 補完。consumer 件数は
親 M1 (`IsRegularDeBruijnHypV2` consumer、git 履歴) で実測。X/Y unit 渡しで既存証明が
defeq に通れば blast radius は小。(b-1) は新規 structure で blast radius ゼロだが sum 専用
wrapper 配線が要る。**skeleton 型確認で (b-1)/(b-2) のどちらが breakage 少ないか実測**。

**prior art (M0' verbatim)**: `IsHeatFlowEndpointRegular` (`EPIG2HeatFlowContinuity.lean:352`)
が既に `v_Z` field + `hZ_law : gaussianReal 0 v_Z` を持ち、sum に `v_Z := 2` を渡して
構成済 (`EPIStamToBridge.lean:1447`)。de Bruijn line の隣接 structure が general-variance を
既に採用しているので、`IsRegularDeBruijnHypV2` の `Z_law` field general-variance 化は
**設計上の整合性が高い** (取り残された unit-hardcode の是正)。

### ルート (c) — X+Y を単一 input として X/Y producer 機械を再利用 — **副本命**

**内容**: sum を 1 つの input `S := X+Y` と見なし、その上の unit-noise producer を
`isDeBruijnRegularityHyp_of_methodX_unitnoise` (`EPICase1RatioLimit.lean:1913`) に委譲する。
noise を補助変数 `W := (Z_X+Z_Y)/√2` (unit) として導入し、`IsDeBruijnRegularityHyp S W P` を
producer から得て、path-identification で `IsDeBruijnRegularityHyp S (Z_X+Z_Y) P` に橋渡し。

**OUT 判定の懸念 (a と同根)**: `IsDeBruijnRegularityHyp S (Z_X+Z_Y) P` の `reg_at` の
`Z_law` は依然 `P.map (Z_X+Z_Y) = gaussianReal 0 1` を要求し、`W` の law では救えない
(§問題の核心と同じ)。よって (c) も **wrapper が `Z_X+Z_Y` を thread する限り、最終的に
`Z_law` 型不充足に当たる**。

**(c) が生きる条件**: 最終 wrapper `_full` の `h_reg_sum` 型を `IsDeBruijnRegularityHyp S W P`
(unit-W noise) に **書き換えられる** なら、(c) は X/Y producer の素直な再利用で閉じる。だが
wrapper signature (`EPICase1RatioLimit.lean:1517-1518`) は `(fun ω => Z_X ω + Z_Y ω)` を
名指しており、`h_pos_stam` bundle (`:1525-1547`) も `(h_reg_sum.reg_at t ht).density_t` を
参照する。wrapper の noise thread を `W` 化するのは PB-1 restate を超える signature 改変で、
ratio antitone (`csiszarLogRatioGap` body、`EPIL3Integration.lean`) の sum path
`X+Y+√t·(Z_X+Z_Y)` も `W` 化が要る (親 B-0' 案 (b) と同じ広範囲書換)。

→ **(c) は wrapper 全面 noise-W 化を伴う**。(b) より影響範囲大。ただし「`S := X+Y` を
input とみなし unit-noise producer 再利用」のアイデアは (b) の `density_t` 構成
(sum の conv density `convDensityAdd pX_sum g_s`) に流用可能 (X/Y producer の pX series
plumbing が `pX_sum := (P.map (X+Y)).rnDeriv volume` で再利用できる)。

### ルート比較表

| 観点 | (a) unit-W + reparam | (b) sum 専用 general-var structure ✓ | (c) S=X+Y を input 再利用 |
|---|---|---|---|
| `Z_law` 型整合 | **不可** (path-id は path のみ、noise law 救えない) | **可** (`v_Z` field で N(0,2) 受容) | wrapper noise-W 化が前提 (大改変) |
| ratio core 偽化 | — (単独 OUT) | 回避可 (sum 単独、`(1/2)·J` 不変、density は unit-W pin) | 回避可 (但し wrapper 改変) |
| structure 改変 | なし | sum 専用 field 追加 (`Z_law` のみ、prior art `IsHeatFlowEndpointRegular`) | なし (but wrapper signature 改変) |
| 影響範囲 | (b)/(c) の補助 | sum 局所 + consumer に `v_Z:=1` 補完 (b-2) / 新 structure (b-1) | wrapper + ratio antitone 全面 |
| prior art | PB-2 既存 | **`IsHeatFlowEndpointRegular` が同型 (M0')** | X/Y producer 既存 |
| 推奨 | 補助具 | **本命** | 副本命 (wrapper 改変なら) |

**推奨 = (b)**: `IsHeatFlowEndpointRegular` の general-variance prior art と整合し、sum 局所で
ratio core を壊さず (微分値 `(1/2)·J` 不変 + density を unit-W pin)、structure 改変は
`Z_law` field の general-variance 化のみ。(a) は (b) の density 構成補助、(c) は wrapper 改変を
許す場合の代替。**ただし最終確定は M1 skeleton 型確認で実機械決着** (予測で確定しない、CLAUDE.md
verbatim 義務 — 「sum density を unit-W pin したとき field 値と density 形の分離が型整合するか」は
skeleton で裏取り必須)。

---

## Phase 詳細

### M1 — 3 ルート skeleton 型確認 (~read-only + skeleton sorry)

**スコープ**: (a)/(b)/(c) を skeleton (`:= by sorry`) で型枠だけ書き、`Z_law` field が
どのルートで型整合するかを LSP / `lake env lean` で実機械確認。

- [ ] (a) `IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` の `reg_at .Z_law` を path-id 経由で
  埋めようとして型不充足を確認 (`gaussianReal 0 1 = gaussianReal 0 2` 要求が出ることを実機械で)
- [ ] (b-1) 新規 sum structure `IsRegularDeBruijnHypV2Sum` (v_Z field 付き) の skeleton 型枠
- [ ] (b-2) 既存 `IsRegularDeBruijnHypV2.Z_law` を `gaussianReal 0 v_Z` に開いたときの consumer
  breakage を `lake env lean` で実測 (X/Y consumer に `v_Z:=1` 補完で通るか)
- [ ] (c) `S := X+Y` を input とした `isDeBruijnRegularityHyp_of_methodX_unitnoise` 委譲が
  `h_reg_sum` 型 (`Z_X+Z_Y` noise) と整合しないことを確認

**Done 条件**: (b-1)/(b-2)/(c) のどれが breakage 最小かを実測した上で採用ルート確定、
判断ログに記録。

### PS-1 — sum producer skeleton (~20-40 行)

**スコープ**: 採用ルートで sum producer 補題の signature を確定 (skeleton)。case-1 file に置く。

スケッチ (ルート (b) 採用想定):

```lean
/-- **PS-1/2 sum producer**: case-1 方針X (unit-noise) の前提から
sum-instance `IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` を供給。
`Z_X+Z_Y ∼ 𝒩(0,2)` は unit-hardcode `Z_law` と型不充足なので、
sum 専用 general-variance structure (ルート b) で `Z_law` field のみ N(0,2) 受容形に開き、
`density_t` は path-identification (PB-2, v:=2) で unit-W 形に pin して微分値 `(1/2)·J` を保つ。
@residual(plan:epi-case1-sum-producer-plan) -/
theorem isDeBruijnRegularityHyp_sum_of_methodX_unitnoise
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    (hZXZY_indep : IndepFun Z_X Z_Y P)
    (hZX_law : P.map Z_X = gaussianReal 0 1) (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (hXY_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume)
    (h_mom_S : Integrable (fun ω => (X ω + Y ω) ^ 2) P)
    (h_fisher_S : … ≠ ∞)  -- 残1 と同型の finite-Fisher precondition
    (hSW_indep : IndepFun (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P) :
    InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp
      (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P := by
  sorry
```

**注意 (sum noise law の供給)**: body 内で `hZXZY_law : P.map (Z_X+Z_Y) = gaussianReal 0 2` を
`gaussianReal_add_gaussianReal_of_indepFun hZXZY_indep hZX_law hZY_law` で導く
(wrapper body `EPICase1RatioLimit.lean:1595-1598` の verbatim パターンを流用、ただし
`v_X+v_Y = 1+1 = 2`)。

**Done 条件**: signature が type-check done (skeleton)、`Z_law` field が採用ルートで型整合する
ことを確認。

### PS-2 — `reg_at` 構成 (genuine or park 判定) (~60-120 行)

**スコープ**: 採用ルートで `reg_at t ht` の各 field を方針X 入力から埋める。

各 field の供給元 (ルート (b) 採用想定、X/Y producer `:1947-1959` の pX series plumbing を
sum に流用):

| field | 供給元 |
|---|---|
| `reg_at .Z_law` | general-variance form で `hZXZY_law` (N(0,2)) 直接 (ルート b の本質) |
| `reg_at .density_t` | `convDensityAdd pX_sum (gaussianPDFReal 0 …)`、path-id で unit-W 形に pin |
| `reg_at .pX` series | `pX_sum := (P.map (X+Y)).rnDeriv volume |>.toReal`、X/Y producer `:1923-1959` の plumbing を S=X+Y で再利用 (`hXY_ac` ⇒ rnDeriv、`h_mom_S` ⇒ pX_mom) |
| `density_t_eq` | conv-pin = density_path、X/Y producer `:1962-1966` 同型 |

**honesty 判定**: `pX_sum` series は load-bearing でない regularity precondition
(「X+Y が Lebesgue 密度を持つ」、X/Y と同じ判定)。ルート (b) の general-variance structure は
**`Z_law` field のみ** 一般化で **微分値 `(1/2)·J` は触らない** ので ratio core 偽化を起こさない
(fork-sizing Q1 の偽化原因 = conv-pin variance まで一般化して `(v_Z/2)·J` になること、を回避)。

**撤退ライン**: 採用ルートでも `Z_law` field と `density_t` の unit-W pin が型整合しない、または
ratio core への波及が skeleton で判明したら、`reg_at` を `sorry` +
`@residual(plan:epi-case1-sum-producer-plan)` で park (signature は producer 形を保つ)。

**Done 条件**: `reg_at` が type-check done。genuine に閉じれば proof done 候補、park なら
`@residual` 付き sorry + 判断ログに park 理由。

### PS-3 — `density_t_eq` + `integrable_deriv` 結線 (残1 同型障害の検証) (~30-60 行)

**スコープ**: sum の `density_t_eq` (conv-pin) + `integrable_deriv` を結線。

**残1 同型障害の検証 (本 plan の検証項目)**: sum の `integrable_deriv`
(`∀T>0, IntervalIntegrable ((1/2)·J(density_t)) volume 0 T`) も、X/Y 残1 と **同じ root cause**
(general L¹ `pX_sum` の Fisher 単調性 gap + t=0 近傍非有界) を持つはず。variance carrier が
`2` でも `gaussianConv_fisher_le_inv_var` (`FisherConvBound.lean:385`、`J ≤ 1/(t·v)`) は t=0 で
発散するので同型。

- [ ] sum の `integrable_deriv` が残1 と同型障害であることを skeleton で確認 (予測でなく実機械)
- [ ] 残1 の closure 設計 (親 plan 残1: regular density + bounded-deriv precondition 強化、
  `fisherInfoOfDensity_convDensityAdd_le` `:1820` 適用) を sum にも適用
- [ ] 残1 が未解決の段階では sum `integrable_deriv` も `sorry` +
  `@residual(plan:epi-case1-sum-producer-plan,plan:epi-case1-debruijn-producer-plan)`
  (compound、残1 closure に依存する transitive) で park

**Done 条件**: sum `integrable_deriv` が残1 と同型障害か判定確定。残1 が閉じれば sum も同設計で
閉じる、未解決なら compound `@residual` で park (残1 依存を明示)。

### PS-4 — PB-6 最終 wrapper `_full` への結線確認 (~10-20 行)

**スコープ**: 最終 wrapper `entropyPower_add_ge_case1_of_methodX_unitnoise` (PB-6) の
`h_reg_sum` 位置に sum producer を注入する結線を確認。

**sum が刺さる位置 (verbatim)**: wrapper signature
`h_reg_sum : IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` (`EPICase1RatioLimit.lean:1517-1518`)。
最終 wrapper body で:

```lean
  have h_reg_sum := isDeBruijnRegularityHyp_sum_of_methodX_unitnoise X Y Z_X Z_Y P …
```

として X/Y producer (`h_reg_X'` / `h_reg_Y'`、PB-3) と並べて注入。`h_pos_stam` bundle
(`:1525-1547`) は `(h_reg_sum.reg_at t ht).density_t` を参照するので、sum producer が返す
instance の conv-pin density (PS-2 で `convDensityAdd pX_sum g_s` に pin) と **同一**である
ことを確認 (PS-2 の density 形が `h_pos_stam` の sum conjunct `:1541-1544` (sum conv-pin
`density_t(sum) = convDensityAdd (density_t X) (density_t Y)`) と整合するか)。

**Done 条件**: sum producer が `h_reg_sum` 位置に型整合して注入できることを確認。`h_pos_stam` の
sum conjunct (Fisher>0 sum / sum conv-pin) が sum producer の density 形と整合。

### PS-V — verify + 独立 honesty audit (~5 行)

- [ ] touched file 全件 `lake env lean` silent
- [ ] sum producer + 最終 wrapper を `#print axioms` で確認 (park があれば `sorryAx` 残存 =
  type-check done、全閉なら `[propext, Classical.choice, Quot.sound]`)
- [ ] **独立 honesty audit** (`honesty-auditor` subagent) 起動 (新規 sorry 導入 + ルート (b)
  採用時の structure 改変で honesty 意味が変わる → CLAUDE.md「Independent honesty audit」起動条件)
- [ ] audit verdict 確認:
  - ルート (b) の sum 専用 general-variance structure が **案A の全体一般化と別物** であること
    (sum 単独で微分値 `(1/2)·J` を触らず ratio core 偽化を起こさない、`Z_law` field のみ開く)
  - `pX_sum` series が load-bearing bundling でない regularity precondition か
  - sum producer の前提に `*Hypothesis` predicate が含まれないか (`rg` 確認)
  - park (`@residual`) の classification (compound `plan:…,plan:…` の AND semantic が正しいか、
    残1 依存を正しく表しているか)

**Done 条件**: 全 silent + audit verdict 全 OK (or questionable-resolved-inline)。

---

## PB-6 への結線順序 (残1 + 残2 解決後)

親 plan PB-1〜PB-7 の中で本 plan (残2 = L-Sum-struct) が刺さる位置と、残1 + 残2 解決後の
最終結線順序 (handoff Next step より):

1. **残1** (`isDeBruijnRegularityHyp_of_methodX_unitnoise` の `integrable_deriv`、設計(b)) を
   閉じる → X/Y producer genuine。
2. **残2** (本 plan、sum producer L-Sum-struct) を閉じる → sum producer genuine
   (or compound `@residual` park)。
3. **PB-5** `h_pos_stam` producer (Stam/Blachman genuine 既存配線、`isStamInequalityHyp_via_step3`
   `EPIStamStep3Body.lean:119` + `isBlachmanConvReady_convDensityAdd_gaussian`)。
   **sum がここに刺さる**: `h_pos_stam` の sum conjunct (Fisher>0 sum `:1531` / sum conv-pin
   `:1541-1544`) が sum producer の density 形を参照するので、本 plan PS-2 の density pin が
   PB-5 の sum conjunct と整合する必要がある。
4. **PB-6** 最終 wrapper `entropyPower_add_ge_case1_of_methodX_unitnoise`: X/Y producer (残1) +
   sum producer (残2、本 plan) + `IsHeatFlowEndpointRegular` 3 本 (既存一般 variance、
   `EPIStamToBridge.lean:1435-1452` パターンで v=1/v=1/v=2) + `h_pos_stam` (PB-5) を注入し
   de Bruijn group を前提から消す。
5. **PB-7** `IsIBPHypothesis` (`FisherInfoV2DeBruijnBody.lean:209`、死 alias) retract。
6. **PB-V** verify + 独立 honesty audit。

**headline 到達条件**: 残1 + 残2 が **両方** genuine に閉じて初めて、PB-6 wrapper が
`[propext, Classical.choice, Quot.sound]` (proof done) に届く。どちらかが park なら
type-check done 止まり (handoff 指摘: 残1 を閉じても sum がこれなので headline 未完)。

---

## 撤退ライン

- **L-Sum-route-a** (M1 段階): ルート (a) unit-W + reparam 単独では `Z_law` 型不充足が救えない
  (path-id は path のみ同一視、noise law 主張は救えない) → (a) を単独 closure から除外し
  (b)/(c) の density 構成補助に格下げ。判断ログに記録。
- **L-Sum-route-b-revert** (PS-2 段階): ルート (b) の sum 専用 general-variance structure を
  作ったが、`Z_law` field general-variance + `density_t` unit-W pin の分離が型整合しない、または
  ratio core への波及が skeleton で判明 → (c) (wrapper noise-W 化) に escalate、または `reg_at` を
  `sorry` + `@residual(plan:epi-case1-sum-producer-plan)` で park。
- **L-Sum-integrable** (PS-3 段階): sum `integrable_deriv` が残1 と同型障害で、残1 が未解決 →
  sum `integrable_deriv` を `sorry` +
  `@residual(plan:epi-case1-sum-producer-plan,plan:epi-case1-debruijn-producer-plan)`
  (compound、残1 依存) で park。残1 が閉じれば sum も同設計で閉じる。
- **L-Sum-struct-park** (PS-2/3 全体): どのルートでも sum を genuine に閉じられないと判明 →
  sum producer を `sorry` + `@residual(plan:epi-case1-sum-producer-plan)` で park し、X/Y 系
  proof done + sum type-check done で commit。structure 改変 (ルート b の確定形) を次 wave に
  繰り越す closure 計画を判断ログに記録。**`*Hypothesis` predicate に核を bundling する撤退は
  禁止** (CLAUDE.md「検証の誠実性」)。

## genuine closure 可能な範囲 / 別 phase 送りの境界

- **genuine closure 可能 (本 plan scope)**: sum noise N(0,2) の型不充足を ルート (b)
  (sum 専用 `Z_law` general-variance structure) で解消し、`reg_at` の Z_law / density_t / pX_sum
  series を方針X 入力から埋める部分。`IsHeatFlowEndpointRegular` の prior art が示すとおり、
  general-variance structure 化自体は壁ゼロ (型設計)。
- **残1 依存 (本 plan では閉じない、親 plan へ)**: sum `integrable_deriv` の general L¹ Fisher
  単調性 gap。これは残1 と同 root cause で、親 plan 残1 の closure 設計 (regular density +
  bounded-deriv precondition 強化) に依存。compound `@residual` で park。
- **別 phase / textbook 最終版送り (Mathlib 壁)**: general L¹ `pX` (regular density 仮定なし) の
  score-of-convolution Fisher 単調性は genuine 解析 (Mathlib gap)。残1 の設計(a) ルート
  (general-pX Fisher 単調性新規証明) を選ぶ場合の重い解析で、textbook 最終版の general-L¹ 緩和
  (approximation で regular density に帰着) を別 phase に切り出す。本 plan は残1 の設計(b)
  (precondition 強化) 前提で sum も同設計で閉じる方針。

---

## 参考 file (verbatim file:line)

- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1498` — case-1 wrapper
  `entropyPower_add_ge_case1_of_methodX` (PB-1 restate 済、sum producer の consumer)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1517-1518` — `h_reg_sum`
  `IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` (本 plan が供給する対象)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1525-1547` — `h_pos_stam` bundle
  (sum conjunct `:1531` Fisher>0 sum / `:1541-1544` sum conv-pin、PS-4 で整合確認)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1595-1598` — `hZXZY_law`
  `P.map (Z_X+Z_Y) = gaussianReal 0 (v_X+v_Y)` (sum N(0,2) の verbatim 供給パターン)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1769` 付近 —
  `gaussianConvolution_rescale_eq` + `map_gaussianConvolution_rescale_eq` (PB-2 path-id、
  ルート (a)/(b) の density unit-W 構成に v:=2 で適用、@audit:ok)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1820` —
  `fisherInfoOfDensity_convDensityAdd_le` (Fisher 単調性 lemma、残1 + sum integrable_deriv の
  regular-case closure 入力、genuine sorryAx-free)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1913-1966` —
  `isDeBruijnRegularityHyp_of_methodX_unitnoise` (X/Y producer、pX series plumbing を sum に
  流用、`integrable_deriv` 残1 park)
- `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:205-210` — `IsRegularDeBruijnHypV2`
  structure (`Z_law : gaussianReal 0 1` が :210、**unit-hardcode、本 plan ルート (b) で
  general-variance 化対象**)
- `InformationTheory/Shannon/EPIStamDischarge.lean:251-288` — `IsDeBruijnRegularityHyp`
  structure (`reg_at` :262 が unit `Z_law` 継承、`integrable_deriv` field :282-288)
- `InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:352` — `IsHeatFlowEndpointRegular`
  structure (`v_Z : ℝ≥0` field + `hZ_law : gaussianReal 0 v_Z`、**general-variance prior art =
  ルート (b) の設計根拠**、@audit:ok)
- `InformationTheory/Shannon/EPIStamToBridge.lean:1435-1452` — `IsHeatFlowEndpointRegular`
  producer 既存 pattern (X→v_Z=1 / Y→v_Z=1 / **sum→v_Z=2 を直接渡す** prior art、pX series は
  `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` park)
- `InformationTheory/Shannon/EPIStamToBridge.lean:895` — `csiszarLogRatioGap_deriv_le_zero`
  (harmonic-Stam ratio core、案A 全体一般化が偽化する地点、ルート (b) が微分値を触らず回避)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3397` — de Bruijn `_chain`
  (density-level core、v_Z-agnostic、ルート (b) の density unit-W pin が乗る基盤)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:215` — Phase 1b
  `pPath_eq_convDensityAdd` (一般 v_Z、sum の conv-pin density 整合先)
- `InformationTheory/Shannon/FisherConvBound.lean:385` — `gaussianConv_fisher_le_inv_var`
  (`J ≤ 1/(t·v)`、sum integrable_deriv も t=0 で発散 = 残1 同型障害の根拠)
- `docs/shannon/epi-case1-debruijn-producer-plan.md` — 親 plan (PB-1〜PB-7、残1 設計、
  L-Sum-struct 撤退ライン :578-586)
- `docs/shannon/epi-case1-debruijn-producer-fork-sizing.md` — 案A OUT (ratio core 偽化 Q1) /
  案B chain factor 解析の advisor verdict
- `docs/shannon/epi-stam-to-conclusion-phaseA-plan.md` — EPI 一般 line 側 density witness park の
  owner plan (sum pX series の入力 precondition と同 owner)
- `docs/audit/audit-tags.md` — `@residual` 語彙 (compound syntax `:198-243`) / Wall register

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-06-05 起草時 — 残2 (L-Sum-struct) を独立 plan に切り出し**: 親 plan
   `epi-case1-debruijn-producer-plan.md` の PB-4 / L-Sum-struct を、deeper restructuring を
   要する独立 frontier として本 plan に分離 (handoff Next step 2)。型不一致の核心
   (`Z_law : gaussianReal 0 1` unit-hardcode vs sum `gaussianReal 0 2`) を verbatim 確認
   (`FisherInfoV2DeBruijn.lean:210` / `EPICase1RatioLimit.lean:1595`)。

2. **2026-06-05 — M0' 隣接 structure prior art 発見でルート (b) を本命に**: `IsHeatFlowEndpointRegular`
   (`EPIG2HeatFlowContinuity.lean:352`) が **既に `v_Z` field + `hZ_law : gaussianReal 0 v_Z`**
   を持ち、既存 producer (`EPIStamToBridge.lean:1447`) が **sum に `v_Z := 2` を直接渡して**
   構成済であることを verbatim 確認。de Bruijn line の隣接 structure が general-variance を
   既に採用しており、`IsRegularDeBruijnHypV2` だけが unit-hardcode で取り残されている。
   → ルート (b) (sum 専用 `Z_law` general-variance 化) を本命候補に。案A の全体一般化との違い:
   sum 単独で微分値 `(1/2)·J` を触らず (density は path-id で unit-W pin)、ratio core 偽化を
   回避できる見込み (fork-sizing Q1 の偽化原因を回避)。**ただし「field 値 N(0,2) と density 形
   unit-W の分離が型整合するか」は M1 skeleton で実機械決着が必須** (予測で確定しない)。

3. **2026-06-05 — ルート (a) を単独 closure から除外**: handoff 候補のルート (a)
   (unit-W + time-reparam) は path-identification (PB-2) が path (関数) のみ同一視し、
   `Z_law` field の noise law 主張 (`P.map (Z_X+Z_Y) = …`) は救えない (親 B-0 末尾の系を
   verbatim 再確認)。→ (a) は単独 closure ルート OUT、(b)/(c) の density unit-W 構成補助に格下げ。

4. **2026-06-05 — 残1 同型障害の検証項目を明示 (PS-3)**: handoff 指摘「残1 が閉じても sum が
   これなので headline 未完」を受け、sum `integrable_deriv` が残1 と同 root cause (general L¹
   `pX_sum` の Fisher 単調性 gap + t=0 近傍非有界、variance 2 でも `gaussianConv_fisher_le_inv_var`
   が t=0 で発散) かを PS-3 で実機械確認する検証項目を設定。残1 の closure 設計 (b)
   (precondition 強化) が sum にも必要で、未解決段階では compound `@residual(plan:epi-case1-sum-producer-plan,plan:epi-case1-debruijn-producer-plan)` で park。

5. **2026-06-06 — CLOSED: sum frontier は two-time restructure で closure、本 plan の producer は dead 削除**:
   `epi-case1-twotime-restructure-plan` の two-time route (`EPICase1TwoTime.lean`,
   `entropyPower_add_ge_case1_of_regular_twotime`, `@audit:ok`) が X/Y を分離 unit-noise で摂動し variance-2
   view を発生させずに sum EPI を genuine closure。本 plan の sum producer
   `isDeBruijnRegularityHyp_sum_of_methodX_unitnoise` (`Z_law` `@audit:defect(false-statement)` 保持) は
   **0 consumer の構造的 dead orphan** と確認され `EPICase1SumProducer.lean` ごと削除 (2026-06-06)。
   ⟹ `Z_law` general-variance structure surgery (ルート b/c) は **不要化**、本 plan は superseded で CLOSED。

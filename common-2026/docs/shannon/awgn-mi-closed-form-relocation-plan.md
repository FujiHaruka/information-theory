# AWGN: `mutualInfoOfChannel_gaussianInput_closed_form` の `h_bridge` 解消 (relocation plan)

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §Phase A (MI closed-form bridge)
> **Follow-up of**: [`awgn-mi-bridge-plan.md`](awgn-mi-bridge-plan.md) TODO L64
> 「`mutualInfoOfChannel_gaussianInput_closed_form` の `h_bridge` load-bearing 解消
> (incidental-migration follow-up)」。本 plan がその incidental-migration を crystallize する。
> **Sibling**: [`awgn-mi-decomp-plan.md`](awgn-mi-decomp-plan.md) (MI 分解の genuine discharge 側、
> `ContChannelMIDecomp.lean` を produce 済)。
>
> **Status (2026-05-28)**: 起草のみ。実装未着手。

<!--
記法は awgn-m5-sorry-migration-plan / subplan-template に揃える:
状態絵文字 📋未着手 / 🚧進行中 / ✅完了 / 🔄方針変更 (判断ログ参照)、取り消し線、append-only 判断ログ。
-->

## 進捗

- [ ] Phase 0 — 在庫 + 依存方向 verbatim 再確認 📋
- [ ] Phase 1 — relocation 先 file 確定 + closed-form 移設 📋
- [ ] Phase 2 — AWGN.lean leave-behind 処理 (削除 + docstring 更新) 📋
- [ ] Phase 3 — consumer cascade 解消 (`_of_primitives` / `_F2_discharged`) 📋
- [ ] Phase 4 — honesty audit + 親 plan / wall docstring 同期 📋

## ゴール / Approach

**ゴール**: `InformationTheory/Shannon/AWGN.lean:125`
`mutualInfoOfChannel_gaussianInput_closed_form` から **opaque load-bearing 仮説
`h_bridge`** (= textbook identity `I.toReal = h(P+N) − h(N)`) を削除し、定理の residual
を **既存 shared wall `contChannelMIDecomp_holds` (`AwgnWalls.lean:92`,
`@residual(wall:awgn-mi-decomp)`) への transitive 依存 1 本だけ**にする。
honesty audit (commit `5c5d94d`) が「まだ load-bearing」と flag した tier-4
`@audit:closed-by-successor(awgn-mi-bridge-plan)` を解消する。

**なぜ移設が要るか (blocker)**: `h_bridge` を埋める 3 ピースは **全て AWGN.lean の
downstream** にある (import DAG、Phase 0 で verbatim 確認):

1. **MI 分解 (唯一の genuine residual)** — `contChannelMIDecomp_holds`
   (`AwgnWalls.lean:92`, shared sorry, `@residual(wall:awgn-mi-decomp)`)。
2. **output law (genuine, 0 sorry)** — `isAwgnMIDecomp_of_densitySplit`
   (`ContChannelMIDecomp.lean:546`) が `h_out : IsAwgnOutputGaussian` から
   `IsAwgnMIDecomp` を genuine 化。`h_out` 自身は
   `isAwgnBindEqConv_discharged` (`AWGNBindConvBody.lean:103`、genuine) +
   `awgn_output_gaussian_of_bind_eq_conv` (`AWGNMIBridgeDischarge.lean:100`) で genuine。
3. **cond-entropy collapse (genuine)** —
   `awgn_cond_entropy_eq_noise_entropy_of_const` (`AWGNMIBridge.lean:166`) /
   `differentialEntropy_awgnChannel_apply_eq_noise` (`AWGNMIBridge.lean:108`)。

`AWGN.lean` は `{ChannelCoding, DifferentialEntropy}` しか import しない (DAG の AWGN
subtree の頂点) ので、上記 discharge 補題を呼ぶと **import cycle**。よって closed-form は
downstream に **relocate** するしかない。

**Approach (解の形)**: 既に sibling plan (`awgn-mi-decomp-plan`) が
`ContChannelMIDecomp.lean` に **`awgn_mi_gaussian_closed_form_of_out`**
(`ContChannelMIDecomp.lean:559`) を produce 済 — これは「`h_out` だけ honest、MI-decomp は
genuine 化済」の縮減形で、`(mutualInfoOfChannel …).toReal = (1/2) log(1 + P/N)` という
**closed-form と全く同じ結論**を出す。残る唯一の honest 引数 `h_out` は
`AWGNBindConvBody.isAwgnBindEqConv_discharged` で genuine に閉じられる。

したがって本 relocation は「closed-form の log-algebra 本体を物理的にコピーする」のではなく、
**`h_out` も genuine 化した hypothesis-free 版を、両方の genuine producer
(`ContChannelMIDecomp` 側 + `AWGNBindConvBody` 側) を import できる最下流 file に置く**形を取る。
`AWGNBindConvBody` と `ContChannelMIDecomp` は **兄弟** (両者 `AWGNMIBridgeDischarge` の直下、
互いに非 import) なので、両者を見られる file が現状存在しない → **NEW file を 1 本立てる**
(下記 Phase 1 で 2 案比較、新規 file 案を第一候補とする)。

移設後の closed-form 定理は **body 内に sorry を一切持たない**。residual は型検査が
transitive に追跡する `contChannelMIDecomp_holds` (wall, `AwgnWalls.lean`) 1 本のみ。
よって移設先定理は `@residual` タグ不要 (Lean が transitive 追跡)、tag は単に
`@audit:closed-by-successor(awgn-mi-bridge-plan)` を **drop** する (opaque hypothesis が
消えるため bookkeeping 不要)。

## Phase 0 - 在庫 + 依存方向 verbatim 再確認 📋

実装着手前に以下を `rg`/Read で verbatim 確認 (本 plan 起草時 2026-05-28 の値、
実装時に drift がないか再点検)。

- [ ] **import DAG** (`rg -n '^import InformationTheory' InformationTheory/Shannon/AWGN*.lean
      InformationTheory/Draft/Shannon/ContChannelMIDecomp.lean`):

```
AWGN              → {ChannelCoding, DifferentialEntropy}          ← closed-form 現在地 (頂点)
AwgnWalls         → AWGN                                          ← wall contChannelMIDecomp_holds:92
AWGNMain          → {AWGN, AWGNAchievability, AWGNConverse}
AWGNF1Discharge   → AWGNMain
AWGNMIBridge      → AWGNF1Discharge        ← cond-entropy:108/166 + 旧 consumer:260/295
AWGNMIBridgeDischarge → AWGNMIBridge       ← awgn_output_gaussian_of_bind_eq_conv:100
AWGNBindConvBody  → AWGNMIBridgeDischarge  ← isAwgnBindEqConv_discharged:103 (genuine h_out 源)
AWGNMIDecompBody  → AWGNMIBridgeDischarge  ← (AWGNBindConvBody の兄弟)
ContChannelMIDecomp (Draft) → {AWGNMIDecompBody, AwgnWalls, …}    ← awgn_mi_gaussian_closed_form_of_out:559
```

  - 兄弟関係の核心: `AWGNBindConvBody` と `ContChannelMIDecomp` は **どちらも import
    していない** (`rg -rln 'AWGNBindConvBody' InformationTheory/` → 0 件、
    `ContChannelMIDecomp` を import するのは `ParallelGaussianPerCoordRegularity` /
    Draft `ParallelGaussianPerCoord` の 2 件のみ)。
- [ ] **closed-form signature** (`AWGN.lean:125-135`、verbatim):
      `(P N : ℝ≥0) (hP : (↑P:ℝ) ≠ 0) (hN : (↑N:ℝ) ≠ 0)
      (h_meas : IsAwgnChannelMeasurable N)
      (h_bridge : (mutualInfoOfChannel (gaussianReal 0 P) (awgnChannel N h_meas)).toReal
        = differentialEntropy (gaussianReal 0 (P+N)) − differentialEntropy (gaussianReal 0 N))
      : (… ).toReal = (1/2) * Real.log (1 + (↑P)/(↑N))`。
      body (AWGN.lean 137-177) は `rw [h_bridge]` 後の純 log-algebra。
- [ ] **genuine producer の結論形 verbatim** (`ContChannelMIDecomp.lean:559-573`):
      `awgn_mi_gaussian_closed_form_of_out (P : ℝ) (hP_pos : 0 < P) (N : ℝ≥0)
      (hN : (↑N:ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
      (h_out : IsAwgnOutputGaussian P N h_meas)
      : (mutualInfoOfChannel (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
        = (1/2) * Real.log (1 + P / (↑N))`。
      → **closed-form と RHS 同形**。差は (a) `P : ℝ` vs `ℝ≥0`、
      `gaussianReal 0 P.toNNReal` vs `gaussianReal 0 P`、(b) `h_out` が genuine 化可能な唯一の honest 引数。
- [ ] **coercion bridge** `Real.toNNReal_coe : (↑r).toNNReal = r`
      (Mathlib.Data.NNReal.Defs、loogle で存在確認済) + `Real.coe_toNNReal`
      (`ContChannelMIDecomp.lean:573` で既に使用)。
      producer は `P : ℝ` / `gaussianReal 0 P.toNNReal`、closed-form の旧 statement は
      `P : ℝ≥0` / `gaussianReal 0 P`。移設後どちらの parameter 形を採るか Phase 1 で決定
      (下記、`ℝ` 形を推奨)。

## Phase 1 - relocation 先 file 確定 + closed-form 移設 📋

### 決定 1: relocation target

移設先は **両方の genuine producer を import できる最下流 file**:

- `h_out` の genuine 化 → `AWGNBindConvBody.isAwgnBindEqConv_discharged` +
  `AWGNMIBridgeDischarge.awgn_output_gaussian_of_bind_eq_conv`
  (chain: `isAwgnBindEqConv_discharged P N h_meas : IsAwgnBindEqConv` →
  `awgn_output_gaussian_of_bind_eq_conv P N h_meas (…) : IsAwgnOutputGaussian`)。
- MI-decomp genuine + cond-entropy genuine + 旧 consumer →
  `ContChannelMIDecomp.awgn_mi_gaussian_closed_form_of_out` (これ自身が transitively
  `AwgnWalls` の wall + `AWGNMIBridge` の cond-entropy を内包)。

`AWGNBindConvBody` と `ContChannelMIDecomp` は互いに非 import の兄弟なので、両者を同時に
見られる既存 file は **無い**。2 案:

- **案 A (第一候補) — NEW file `InformationTheory/Shannon/AWGNMIClosedForm.lean`**:
  `import InformationTheory.Shannon.AWGNBindConvBody` +
  `import InformationTheory.Draft.Shannon.ContChannelMIDecomp`。
  `InformationTheory.lean` の import 順は **`AWGNMIDecompBody` (line 172) と
  `ContChannelMIDecomp` (line 173) の直後** に置く (両 producer より下流)。
  利点: AWGN.lean / 既存 producer file の責務を汚さない、import 追加 1 file で完結。
- **案 B — `ContChannelMIDecomp.lean` に `import AWGNBindConvBody` を 1 行足して、
  同 file 内に移設**: cycle 無し (`AWGNBindConvBody` は `AWGNMIBridgeDischarge` までしか
  遡らず `ContChannelMIDecomp` を見ない)。利点: file 数増えない。
  欠点: Draft file に AWGN.lean 由来の公開 API を混ぜると由来が追いにくく、
  `ContChannelMIDecomp` の現 import (`ParallelGaussian*` 2 件) に余計な transitive 依存。

**第一候補 = 案 A (NEW file)**。Phase 0 の import 確認で `ContChannelMIDecomp` の
consumer (`ParallelGaussian*`) が closed-form を必要としないことを確認済なので、
責務分離の利得が file 数より勝る。最終判断は Phase 1 着手時に行い、判断ログに記録。

- [ ] (案 A 採用時) `InformationTheory/Shannon/AWGNMIClosedForm.lean` を skeleton で作成
      (namespace `InformationTheory.Shannon.AWGN`、import 2 本、定理 1 本 `:= by sorry`)。
- [ ] `InformationTheory.lean` に import 行 1 本追記 (line 173 `ContChannelMIDecomp` の直後)。

### 決定 2: 移設定理の signature + body sketch

新 signature (hypothesis-free、`hP/hN/h_meas` のみ; `P : ℝ` 形を採る — producer に揃える):

```lean
/-- AWGN channel mutual information, Gaussian input, closed form
`I = (1/2) log(1 + P/N)`. h_bridge を一切取らない hypothesis-free 版。
唯一の residual は MI 分解 wall `contChannelMIDecomp_holds`
(`AwgnWalls.lean`, `@residual(wall:awgn-mi-decomp)`) への transitive 依存のみ
(本定理の body は 0 sorry)。 -/
theorem mutualInfoOfChannel_gaussianInput_closed_form'
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N) :
    (mutualInfoOfChannel (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  -- h_out を genuine 化 (bind/conv bridge 経由)
  have h_bridge_conv := isAwgnBindEqConv_discharged P N h_meas
  have h_out : IsAwgnOutputGaussian P N h_meas :=
    awgn_output_gaussian_of_bind_eq_conv P N h_meas h_bridge_conv
  -- producer に委譲 (MI-decomp genuine + cond-entropy genuine + log-algebra 内包)
  exact awgn_mi_gaussian_closed_form_of_out P hP N hN h_meas h_out
```

  注意: 旧 `h_bridge` RHS (`h_decomp` + `h_out` + `h_cond` を `awgn_mi_bridge_of_primitives`
  で組み上げる手順) を本 file で **再実装しない**。`awgn_mi_gaussian_closed_form_of_out` が
  既にその assembly + log-algebra を内包する (`ContChannelMIDecomp.lean:559-573` で
  `isAwgnMIDecomp_of_densitySplit` → `awgn_mi_gaussian_closed_form_of_primitives` を chain)。
  本定理は薄い genuine wrapper。

- [ ] 上記 body を埋める (skeleton-driven、1 step ずつ LSP 確認)。
- [ ] `lake env lean InformationTheory/Shannon/AWGNMIClosedForm.lean` で 0 errors
      (sorry 0、warning 0)。

### 決定 3: 移設定理の tag

- 旧 `@audit:closed-by-successor(awgn-mi-bridge-plan)` は **drop**
  (opaque hypothesis が消えたので bookkeeping 不要)。
- 新定理は body 0 sorry なので `@residual` 不要 (residual は依存先 wall に存在、
  Lean が transitive 追跡 — `共有 Mathlib 壁: shared sorry 補題パターン` の建付け通り、
  consumer 側は `@residual` を持たず proof done 判定可)。
- docstring に「residual = `contChannelMIDecomp_holds` (wall:awgn-mi-decomp) への
  transitive 依存」と散文で 1 行明記 (grep 補助)。

## Phase 2 - AWGN.lean leave-behind 処理 📋

旧 `mutualInfoOfChannel_gaussianInput_closed_form` (AWGN.lean:124-177、`h_bridge` 形) は
**削除する** (後継 hypothesis-free 版が別 file に立つため `@audit:superseded-by` で
残す価値が薄い; ただし consumer cascade=Phase 3 で旧 consumer の付替えが済むまで削除を
待つ — Phase 3 を Phase 2 より先に着手しても可、依存ログで順序を確定)。

- [ ] AWGN.lean:124-177 の旧 closed-form 定理を削除 (Phase 3 で consumer 付替え後)。
- [ ] **docstring 更新フラグ (AWGN.lean)**:
  - L27-29 撤退ライン F-2: 「`h_bridge` 引数として外出し」の記述を「後続
    `awgn-mi-closed-form-relocation-plan` で hypothesis-free 化、
    `AWGNMIClosedForm.lean` に移設」に更新。
  - L111-123 D.3 section header + 旧定理 docstring (F-2 hypothesis form の説明全体)
    を削除 or 移設先への参照に置換。
- [ ] **docstring 更新フラグ (AwgnWalls.lean:84-89)**: honesty-audit note
      「`mutualInfoOfChannel_gaussianInput_closed_form` (`AWGN.lean:125`) does NOT yet
      delegate here — it still carries the chain rule as a load-bearing `h_bridge`」を、
      「relocation で hypothesis-free 化済、`AWGNMIClosedForm.lean` が
      `awgn_mi_gaussian_closed_form_of_out` 経由で本 wall に transitive delegate」に更新。
      L85 の literal `AWGN.lean:125` 行番号参照を新 file 参照に書換。

## Phase 3 - consumer cascade 解消 📋

旧 closed-form の consumer は **AWGNMIBridge.lean 内の 2 件のみ** (Phase 0 で verbatim 確認、
InformationTheory 本体内; Draft `ContChannelMIDecomp` 側は既に `_of_out` 経由で独立):

| consumer | file:line | 旧 closed-form の使い方 |
|---|---|---|
| `awgn_mi_gaussian_closed_form_of_primitives` | `AWGNMIBridge.lean:260` (call L281) | `h_mi_bridge` を組んで `mutualInfoOfChannel_gaussianInput_closed_form P.toNNReal N … h_mi_bridge` を呼ぶ |
| `awgn_capacity_closed_form_F2_discharged` | `AWGNMIBridge.lean:295` (call L312) | `awgn_mi_gaussian_closed_form_of_primitives` を呼ぶ (closed-form を間接消費) |

**cascade の難所 (要調査)**: 両 consumer は `AWGNMIBridge.lean` に住む。`AWGNMIBridge` は
**`AWGNF1Discharge` の直下** = 移設先 (`AWGNMIClosedForm` / `ContChannelMIDecomp`) の
**上流**。よって両 consumer は移設後の hypothesis-free 定理を **import できない**
(逆方向 cycle)。3 択を Phase 3 着手時に判定:

- **案 i (推奨、最小波及)**: 両 consumer を **据え置き**、旧 closed-form を
  **削除しない代わりに AWGNMIBridge.lean 内に keep**。
  → ただし本 plan のゴールは「opaque h_bridge 解消」なので、旧定理を残すと
  honesty defect が残置。**却下** (ゴール不達)。
- **案 ii (第一候補)**: 両 consumer も移設先 file (`AWGNMIClosedForm.lean`) へ relocate。
  `awgn_mi_gaussian_closed_form_of_primitives` は **既に
  `ContChannelMIDecomp.awgn_mi_gaussian_closed_form_of_out` で hypothesis-free 上位互換が
  存在** (`h_decomp` 引数が genuine 化済)。`awgn_capacity_closed_form_F2_discharged` も
  同様に `ContChannelMIDecomp.awgn_capacity_closed_form_of_out` (`:583`、ただし現状
  `sorry` + `@residual(plan:awgn-mi-decomp-plan)`) が後継。→ **AWGNMIBridge.lean の
  2 consumer は新規 hypothesis-free 後継に置換済 (Draft 側) なので、AWGNMIBridge の旧
  consumer は削除 or `@audit:superseded-by` 化**。closed-form の直接 import は不要になる。
- **案 iii**: closed-form を AWGNMIBridge **より上流** (= AWGNF1Discharge 以前) に置く案。
  → producer (`AWGNBindConvBody` / `ContChannelMIDecomp`) より上流になり discharge 不能。**却下**。

**Phase 3 の確定タスク** (案 ii ベース、ただし `awgn_capacity_closed_form_of_out:583` が
`sorry` 残置である点に注意):

- [ ] `awgn_mi_gaussian_closed_form_of_primitives` (AWGNMIBridge:260) の body 内
      `mutualInfoOfChannel_gaussianInput_closed_form` 呼出 (L281) が、旧定理削除で
      壊れる。後継: 同 file から呼べないため、**この consumer 自体を
      `ContChannelMIDecomp.awgn_mi_gaussian_closed_form_of_out` が上位互換として replace
      しているか verbatim 確認**。replace 済なら AWGNMIBridge の `_of_primitives` を
      `@audit:superseded-by(awgn-mi-gaussian-closed-form-of-out)` 化 (history record)。
- [ ] `awgn_capacity_closed_form_F2_discharged` (AWGNMIBridge:295) 同様に
      `ContChannelMIDecomp.awgn_capacity_closed_form_of_out:583` を後継とするが、
      **後者は現状 `sorry` (`@residual(plan:awgn-mi-decomp-plan)`)** なので「genuine な
      後継が未完成」。この場合 AWGNMIBridge:295 を superseded 扱いにすると closure が
      後退する恐れ → **撤退ライン (下記) を適用し、capacity 側の付替えは本 plan scope 外に
      切り出す**。
- [ ] 旧 closed-form 削除後、`lake env lean` で AWGNMIBridge.lean / AWGNMIDecompBody.lean /
      AWGNBindConvBody.lean / ContChannelMIDecomp.lean / AWGNMIClosedForm.lean を個別再検証
      (olean refresh 必要、`lake build InformationTheory.Shannon.AWGN` 1 回)。

proof-log: yes (consumer cascade の付替え順序 + 旧定理削除タイミングが微妙なので
`docs/shannon/proof-log-awgn-mi-closed-form-relocation.md` に記録)。

## Phase 4 - honesty audit + 親 plan / wall docstring 同期 📋

- [ ] **独立 honesty audit** (`honesty-auditor` subagent) を起動。対象:
      移設後の `mutualInfoOfChannel_gaussianInput_closed_form'` (新 file) の signature
      honesty (h_bridge 完全除去確認 / residual classification = wall:awgn-mi-decomp への
      transitive 依存が正しいか) + 削除した旧定理の consumer 付替えが defect を残していないか。
      (新規に signature を変更し honesty 関連の意味が変わるため、Independent honesty audit
      起動条件に該当)。
- [ ] `awgn-mi-bridge-plan.md` TODO L64 にチェック (`[x]` 化) + 本 plan で closure した旨を追記。
- [ ] `awgn-moonshot-plan.md` §Phase A の MI bridge 進捗を更新。

## 撤退ライン / scope boundary

future implementer が cascade を過剰展開しないための境界:

1. **scope = closed-form 1 定理 + その 2 consumer の付替えのみ**。
   `IsAwgnMIDecomp` / `IsAwgnOutputGaussian` 等の predicate 群の追加 genuine 化や、
   `AWGNMain` / achievability / converse 側 (`awgn_channel_coding_theorem` 等) の
   F-1/F-3 撤退ラインには **手を出さない** (別 plan の所掌)。
2. **`awgn_capacity_closed_form_of_out:583` の sorry は本 plan で埋めない**。
   capacity 側 (`awgn_capacity_closed_form_F2_discharged` の付替え) が
   `awgn-mi-decomp-plan` の未完成 sorry に依存する場合、その capacity 付替えは
   `awgn-mi-decomp-plan` 側の closure を待つ別タスクに切り出す。本 plan の必達は
   **MI closed-form (capacity ではない) の `h_bridge` 除去**まで。
3. **per-letter bridge `h_mi_bridge_per_letter`** (`AWGNConverse.lean`、
   `@residual(plan:awgn-mi-bridge-plan)`) は本 plan の対象 **外** —
   `awgn-mi-bridge-plan.md` の別 TODO (mixture→compProd 因子分解 plumbing) で、
   本 closed-form の relocation とは独立かつより hard なタスク。
4. **shared wall `contChannelMIDecomp_holds` の sorry は埋めない**。
   本 plan のゴールは「opaque hypothesis を wall への透明な transitive 依存に置換」であり、
   wall そのものの closure (≈200-300 行の klDiv/Fubini) は対象外。
5. **既存 Draft `ContChannelMIDecomp.lean` の dead-code (`h_llr_split`/`h_int_*` ブロック、
   L510-523 で「inline documentation として保持」と明記済) には触れない**。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 例 (実装時に追記):
1. **relocation target 案 A→案 B 変更**: NEW file 案で … のため ContChannelMIDecomp 直編集に変更。
2. **capacity consumer 付替えを scope 外に切出し**: awgn_capacity_closed_form_of_out:583 が
   sorry 残置のため、capacity 側付替えは awgn-mi-decomp-plan closure 待ちに defer。
-->

# EPI 無条件化: downstream re-port サブ計画 (S2)

> **Parent**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) §Phase 2 / §Sub-plan 一覧 S2
> **slug**: `epi-downstream-report-plan` (`@residual(plan:epi-downstream-report-plan)` と一致)

<!--
記法は傘 plan に揃える: 状態絵文字 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更(判断ログ参照)。
取り消し線 = 廃止。判断ログ append-only。rg "^- \[ \]" で残タスク横断 grep。
-->

## 進捗

- [ ] M0 在庫確認: 旧/新 entropyPower consumer の grep 実値照合 (本 plan §Approach で完了済) 📋
- [ ] Phase A — headline bridge `entropyPowerExt_eq_old_of_ac` (a.c. 1 本、re-port 不要を成立させる核) 📋
- [ ] Phase B — 層 0 不変確認 (Fisher / de Bruijn / AWGN / Real workhorse 群、`lake env lean` no-op 検証) 📋
- [ ] Phase C — naming 統一 cleanup (entropyPowerExt → entropyPower 昇格 + 旧 Real consumer 移行、**後回し可**) 📋
- [ ] Phase D — import 順序 DAG 固定 + olean refresh 順 📋

proof-log: Phase A=yes (bridge lemma 1 本)、Phase B=no (検証のみ)、Phase C=yes (rename batch)、Phase D=no (DAG 記述のみ)。

---

## ゴール / Approach

傘 plan §Phase 2 を受け、`differentialEntropy`/`entropyPower` 参照 file 群を **(a) Real 不変 / (b) ℝ≥0∞ shim 要** に分類し、headline 無条件主定理が要求する最小限の re-port のみを実施する。

### Approach 冒頭の verdict — **rename 不要 (S2 は「naming cleanup」に格下げ)**

**最重要の設計問い「headline 無条件主定理は 36-file の re-port (旧 entropyPower rename) を本当に必要とするか?」の答えは No。** 根拠は実コード verbatim:

1. **S3 (`EPIUncondMixedCase.lean`、commit 9a25df9) は既に新型 `entropyPowerExt : Measure ℝ → ℝ≥0∞` 上で 3-case dispatch を完成させている** (`entropyPowerExt_add_ge_dispatch_skeleton` `:234`)。結論型は `entropyPowerExt (P.map (X+Y)) ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)` (`:283-284`)。case 2/3 は genuine、case 1 のみ `sorry` + `@residual(plan:epi-stam-to-conclusion-plan)` で park。**旧 `entropyPower` (Real) を一切参照しない** (grep 実値: `EPIUncondMixedCase.lean` の `entropyPowerExt` 11 件 / 旧 `entropyPower` 0 件)。
2. **新型 `entropyPowerExt` は完全自立**: `EntropyPowerExt.lean` (S1) は `differentialEntropy` (Real workhorse、不変) のみを import し (`:1`)、旧 `entropyPower` (Real) に依存しない。a.c. 枝 `entropyPowerExt_of_ac` (`:56`) は `ENNReal.ofReal (Real.exp (2 * differentialEntropy μ))` を直接構成、特異枝 `entropyPowerExt_singular` (`:64`) は `0`。退化トラップ除去 (`entropyPowerExt_dirac = 0` `:71`、`entropyPowerExt_gaussianReal = ofReal(2πe v)` `:81`) も S1 内で genuine 完結。
3. **headline は `entropyPowerExt` を新名のまま使って直接 state できる**。傘 Phase 5 の `entropy_power_inequality_unconditional` (新型版) は S3 dispatch をそのまま body にすればよく、case 1 枝のみ既存 case1 core (`EPIStamToBridge.entropy_power_inequality_unconditional` `:1624`、結論型 = **旧 Real** `entropyPower ... ≥ ...`) を **a.c. 1 本の bridge lemma `entropyPowerExt_eq_old_of_ac` 経由で coerce** すれば閉じる。

⇒ **S2 は「headline を立てるための前提」ではなく「naming 統一 cleanup + headline bridge 1 本」に格下げされる。**

格下げの帰結 (傘 plan dep DAG への訂正提案、§判断ログ 1):
- **headline bridge (Phase A) は S2 の真の load-bearing 部** = a.c. 枝で `entropyPowerExt μ = ENNReal.ofReal (entropyPower μ)` (旧 Real) を繋ぐ 1 lemma。これは傘 Phase 5 が case1 を呼ぶ唯一の接点。**Phase 5 はこの 1 本だけ S2 (Phase A) に依存**し、残り (Phase C naming cleanup) には依存しない。
- **naming cleanup (Phase C) は後回し可能**。entropyPowerExt → entropyPower 昇格 + 旧 Real consumer 10-file 移行は headline 完成と独立。傘 Phase 5 (headline assembly) は Phase C を待たず着手できる。
- 傘 plan の `S1→S2→{S3,case1}→Phase5` は **`S1→{S2-PhaseA, S3, case1}→Phase5`、S2-PhaseC は Phase5 と並行 (依存無し)** に訂正すべき。

### (a) Real 不変 file 群 vs (b) ℝ≥0∞ shim 要 file 群 (grep 実値分類)

`rg -l '\bentropyPower\b'` = **11 file** (うち新型 `entropyPowerExt` を持つのは S1 `EntropyPowerExt.lean` + S3 `EPIUncondMixedCase.lean` の 2 file)。旧 Real `entropyPower` consumer = **10 file**:

| file | 旧 entropyPower 件数 | 分類 | 扱い |
|---|---|---|---|
| `EntropyPowerInequality.lean` | 42 (定義 `:102` + 主定理 + corollary) | (a) Real 温存 | **不変**。旧 Real `entropyPower` を温存 (傘 L-Uncond-1-β: 消さず別名共存)。新型 headline は別 statement |
| `EPIStamToBridge.lean` | 91 | (a) Real 温存 | **不変**。case1 core `entropy_power_inequality_unconditional` (`:1624`、旧 Real 結論) は headline bridge の被呼出先 |
| `EPIL3Integration.lean` | 74 | (a) Real 温存 | **不変** (Real EPI integration 中核) |
| `EPIPlumbing.lean` | 55 | (a) Real 温存 | **不変** (4-arg 等 Real plumbing) |
| `EPIStamDischarge.lean` | 27 | (a) Real 温存 | **不変** |
| `EPINoiseExtension.lean` | 9 | (a) Real 温存 | **不変** |
| `EPIG2HeatFlowContinuity.lean` | 8 | (a) Real 温存 | **不変** (heat-flow 端点、Real workhorse 経由) |
| `EPIStamDeBruijnConclusion.lean` | 4 | (a) Real 温存 | **不変** |
| `EPIStamInequalityBody.lean` | 4 | (a) Real 温存 | **不変** |
| `EPIStamStep3Body.lean` | 2 | (a) Real 温存 | **不変** |

**分類の結論**: 旧 `entropyPower` consumer 10-file は **全て (a) Real 不変**。理由 = de Bruijn `HasDerivAt` / Stam / heat-flow の解析中核は normed field (ℝ) を要求するため (傘 plan 設計制約) 旧 Real `entropyPower` のまま動かす必要があり、かつ動かせる (S1 二層構造で新型は別 statement)。**(b) ℝ≥0∞ shim を要するのは headline 主定理 1 箇所のみ**で、それは新規 `entropyPowerExt` statement として S3 が既に構築済 → 旧 file の書換は発生しない。

`differentialEntropy` consumer = **38 file** (`rg -l`、傘 plan 見積 ~36 を verbatim 照合 → 実値 38。AWGN/Fisher/EPI 全 family が Real workhorse を共有)。これらは **全て (a) Real 不変** (`differentialEntropy : Measure ℝ → ℝ` は S1 で温存、改名しない第一候補)。re-port 不要、Phase B で no-op を `lake env lean` 確認するのみ。

### import DAG の葉→根順序 + 旧 Real `entropyPower` 退避戦略

- **葉**: `DifferentialEntropy.lean` (Real workhorse、不変) → `EntropyPowerExt.lean` (S1 新型、`differentialEntropy` のみ依存) → `EPIUncondMixedCase.lean` (S3、`EntropyPowerExt` + `EPIG2ConvEntropyMonotone` 依存)。
- **根**: 傘 Phase 5 headline file (新型 statement、S3 dispatch + Phase A bridge を呼ぶ)。
- **旧 Real `entropyPower` の退避 (L-Uncond-1-β)**: **消さず温存**。新型を `entropyPowerExt` の名のまま使う第一候補では rename 衝突が起きないため退避不要 (傘 L-Uncond-1-β の「旧を `entropyPowerReal` に退避」は **発火しない**のが本 verdict の帰結)。Phase C (後回し) で entropyPowerExt → entropyPower 昇格を選ぶ場合に限り、旧 Real `entropyPower` を `entropyPowerReal` へ rename + 10-file consumer 同期が発生する。

---

## Phase 詳細

### Phase A — headline bridge lemma (S2 の唯一の load-bearing 部) 📋

proof-log: yes。傘 Phase 5 が case1 を呼ぶ唯一の接点。

- [ ] **`entropyPowerExt_eq_old_of_ac`**: `μ ≪ volume → entropyPowerExt μ = ENNReal.ofReal (entropyPower μ)` (旧 Real `entropyPower`)。a.c. 枝で `entropyPowerExt_of_ac` (`EntropyPowerExt.lean:56`、`= ENNReal.ofReal (Real.exp (2 * differentialEntropy μ))`) と旧 `entropyPower μ = Real.exp (2 * differentialEntropy μ)` (`EntropyPowerInequality.lean:102` 定義) を `rfl`/`unfold` で繋ぐ。genuine、~5-10 行見込み。
- [ ] **headline case1 接続補題** `entropyPowerExt_add_ge_of_ac_both`: 両 a.c. のとき `entropyPowerExt` EPI を旧 Real EPI (`EPIStamToBridge.entropy_power_inequality_unconditional`、`h_stam` 付き) から導出。`entropyPowerExt_eq_old_of_ac` を 3 項に適用 + `ENNReal.ofReal_add` (両 nonneg) + `ENNReal.ofReal_le_ofReal`。**`h_stam` は a.c. case 内部前提として残ってよい** (傘 Approach 柱 3 の honest 化、case1 内部 sorry は既存 plan 群が closure)。
- [ ] **`map_add_absolutelyContinuous` 流用確認** (S3 `:55`): case1 で X+Y a.c. を供給する補題が S3 に既存 (両 a.c. ⟹ X a.c. ⟹ X+Y a.c.) を verbatim 確認。

**verbatim 確認義務 (予測禁止)**: 旧 `entropyPower μ = Real.exp (2 * differentialEntropy μ)` (`EntropyPowerInequality.lean:102`) と新 `entropyPowerExt_of_ac` (`EntropyPowerExt.lean:56-57`) の RHS が `ENNReal.ofReal (Real.exp (...))` で literally 一致することを Read で照合してから bridge を書く。

#### Phase A 撤退ライン

- **L-DR-A-α**: `entropyPowerExt_eq_old_of_ac` が `irreducible_def differentialEntropyExt` (`EntropyPowerExt.lean:35`) の unfold で詰まる → `differentialEntropyExt_of_ac` (`:44`、展開 lemma) 経由で `rw`、`unfold entropyPowerExt` は使わず S1 の公開 bridge lemma のみで組む。
- **L-DR-A-β**: case1 内部 `h_stam` の supply 形 (`IsStamInequalityResidual` vs `IsStamInequalityHyp`、defeq via `fisherInfoOfMeasureV2_def`、`EPIStamToBridge.lean:1618-1620`) が新型 headline の呼出側で型不一致 → S3 の case1 `sorry` をそのまま温存し、headline は S3 dispatch を**無改変で**呼ぶ (bridge は傘 Phase 5 側で case1 枝を埋める形に分離)。本 plan は bridge lemma の提供までに留め、headline body 組立は傘 Phase 5 の責務。

### Phase B — 層 0 不変確認 (Real 不変 file 群) 📋

proof-log: no (検証のみ、no-op)。

- [ ] **(a) Real 不変 38-file 群**: `differentialEntropy` consumer (AWGN 系 ~10 / Fisher・de Bruijn 系 ~9 / EPI Real 系 ~15 / Draft ~4) を `lake env lean` で **変更不要 (no-op)** を確認。改名しない第一候補では literally 0 edit。
- [ ] **旧 `entropyPower` consumer 10-file** も同様に no-op 確認。新型 `entropyPowerExt` の導入 (S1 既済) が旧 Real consumer の olean を壊さないことを確認 (別 declaration なので壊れないが、import 追加が無いことを verbatim 確認)。
- [ ] AWGN/Fisher/de Bruijn が (b) ℝ≥0∞ 上位型を**要求していない**ことの再確認 (傘 L-Uncond-2-α の早期検出)。grep 実値では AWGN/Fisher file の `entropyPower` 参照 = 0 (旧 Real `entropyPower` consumer 10-file は全て EPI family)、よって AWGN/Fisher は `differentialEntropy` (Real) のみ → (a) 確定。

#### Phase B 撤退ライン

- **L-DR-B-α** (傘 L-Uncond-2-α 同型): 万一 AWGN/Fisher 系が (b) 上位型を要求する箇所が見つかる → 当該箇所だけ (a)→(b) coercion を局所挿入。grep 実値 (`entropyPower` 参照 0 in AWGN/Fisher) からは**発火しない見込み**だが、`differentialEntropyExt` (EReal) を要求する箇所が将来出たら本ラインで対応。

### Phase C — naming 統一 cleanup (後回し可、headline 非依存) 📋

proof-log: yes (rename batch)。**傘 Phase 5 と並行可能、依存無し**。

- [ ] entropyPowerExt → entropyPower 昇格を行うか判断 (UX vs blast radius)。**昇格する場合のみ**: 旧 Real `entropyPower` を `entropyPowerReal` に rename (L-Uncond-1-β)、10-file consumer を `entropyPowerReal` に同期、新型 `entropyPowerExt` を `entropyPower` に rename、S3 + headline を同期。
- [ ] **昇格しない第一候補** (推奨): 新型は `entropyPowerExt` の名のまま、旧 Real は `entropyPower` のまま共存。`entropyPowerExt` が ℝ≥0∞ 主役、`entropyPower` (Real) は a.c. workhorse という二層命名を docstring で明示。rename 0、blast radius 0。
- [ ] family batch 分割 commit (傘 L-Uncond-2-β): 昇格を選ぶ場合、10-file を 2-3 batch に割り各 batch `lake env lean` clean で commit。

#### Phase C 撤退ライン

- **L-DR-C-α** (傘 L-Uncond-2-β): rename batch が 1 session で終わらない → batch 分割 type-check done 単位 commit。**そもそも昇格しない第一候補なら本ライン不発**。
- **L-DR-C-β**: 昇格 rename が AWGN/Fisher の `differentialEntropy` 参照名と衝突しない (entropyPower のみ rename、differentialEntropy は不変) を確認。

### Phase D — import 順序 DAG + olean refresh 順 📋

proof-log: no。

- [ ] 葉→根 DAG を表で固定: `DifferentialEntropy` (Real workhorse) → `EntropyPowerExt` (S1) → `EPIUncondMixedCase` (S3) → 傘 Phase 5 headline file。`EntropyPowerInequality` (旧 Real) は独立枝 (新型と並行、循環なし)。
- [ ] olean refresh 順 (CLAUDE.md「upstream edits 後 olean refresh」): Phase C で rename した場合のみ `lake build InformationTheory.Shannon.<rename した file>` を上流→下流順に実行し phantom unknown identifier を解消。
- [ ] `InformationTheory.lean` の import 行: S1 `EntropyPowerExt` / S3 `EPIUncondMixedCase` の import 行が既に存在するか確認 (S1/S3 commit で追加済の見込み、verbatim grep)。

#### Phase D 撤退ライン

- **L-DR-D-α**: import cycle が検出される (新型 headline file が旧 Real `EPIStamToBridge` を import し、かつ `EPIStamToBridge` が新型を import する逆方向が生じる) → headline bridge lemma (Phase A) を新型側 file に置き、`EPIStamToBridge` (旧 Real) は新型を import しない一方向 DAG を維持。S3 が既に `EntropyPowerExt` のみ import (旧 `EPIStamToBridge` を import しない) ことから cycle は構造的に発生しない見込み、verbatim 確認で gate。

---

## 撤退ライン共通規律

全 Phase 共通禁止 (CLAUDE.md 検証の誠実性): `Prop := True` placeholder / 結論型≡仮説型 `:= h` 循環 / load-bearing `*Hypothesis` predicate に核を bundle / 退化定義悪用。headline bridge (Phase A) は **a.c. 枝で旧 Real EPI を coerce するだけ**で、`h_stam` を新規に bundle しない (case1 内部 `h_stam` は既存 plan 群が SoT、本 plan は coerce 経路のみ提供)。新規 `sorry` + `@residual` 導入時は独立 honesty-auditor 起動。

honest 撤退口: 詰まったら `sorry` + `@residual(plan:epi-downstream-report-plan)` (def RHS が詰まったら CLAUDE.md「sorry を書けない箇所」第一選択 = 定義書換、第二選択 = `@audit:defect` + `@audit:closed-by-successor(epi-unconditional-moonshot-plan)`)。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-06-05 起草 — rename 不要 verdict 確定 (S2 格下げ + 傘 dep DAG 訂正提案)**: 最重要の設計問い「headline は 36-file re-port を要するか」を実コード verbatim で **No** と判定。根拠 (3 点、全て Read で照合):
   - S3 `EPIUncondMixedCase.lean` (commit 9a25df9) の `entropyPowerExt_add_ge_dispatch_skeleton` (`:234`) が既に新型 `entropyPowerExt : Measure ℝ → ℝ≥0∞` で 3-case dispatch を実現、結論型 `entropyPowerExt (P.map (X+Y)) ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)` (`:283-284`)、case 2/3 genuine + case 1 park。旧 `entropyPower` (Real) 参照 0 件 (grep 実値)。
   - S1 `EntropyPowerExt.lean` は `differentialEntropy` (Real workhorse) のみ依存し旧 `entropyPower` に非依存、a.c./特異 枝とも自立。
   - case1 core `EPIStamToBridge.entropy_power_inequality_unconditional` (`:1624-1630`) は**旧 Real** `entropyPower` を結論に持つが、a.c. 枝の bridge lemma `entropyPowerExt_eq_old_of_ac` 1 本 (`ENNReal.ofReal (entropyPower μ)` 経由) で新型 headline と coerce 接続できる。
   - **grep 実値照合**: 傘 plan 見積「`differentialEntropy` 36 file + `entropyPower` 11 file」に対し実値 = `differentialEntropy` **38 file** / `entropyPower` **11 file (うち新型 entropyPowerExt 2 file、旧 Real consumer 10 file)**。旧 Real consumer 10-file は **全て (a) Real 不変** (EPI family のみ、AWGN/Fisher は `entropyPower` 参照 0)。`differentialEntropy` 38-file も全て (a) Real 不変。
   - **⇒ S2 格下げ**: S2 は「headline 前提」でなく「headline bridge 1 本 (Phase A) + naming cleanup (Phase C、後回し可)」。**傘 dep DAG `S1→S2→{S3,case1}→Phase5` を `S1→{S2-PhaseA, S3, case1}→Phase5` (S2-PhaseC は Phase5 と並行・依存無し) に訂正提案**。傘 Phase 5 (headline assembly) は S2-PhaseC を待たず着手可能。
   - **退避戦略の更新**: 傘 L-Uncond-1-β (旧 Real を `entropyPowerReal` に退避) は **第一候補 (新型を `entropyPowerExt` の名のまま使う共存) では発火しない**。Phase C で昇格 rename を選んだ場合に限り発火。

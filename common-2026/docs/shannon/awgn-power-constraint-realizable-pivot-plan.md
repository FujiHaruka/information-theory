# AWGN — `IsAwgnPowerConstraintRealizable` predicate pivot サブ計画

> **Parent / Sibling**: [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md)
> §「判断ログ #6」(Phase D で `IsAwgnPowerConstraintRealizable` を追加 staging、 後段で false-statement defect 発覚)。
>
> **位置づけ**: 親 plan は「Phase A-E 完走 (1485 行 / 0 sorry / silent)」 状態だが、predicate `IsAwgnPowerConstraintRealizable P N` (`AWGNAchievabilityDischarge.lean:735`) に **false-statement defect** (chi-square mass の unsatisfiable bound) が後から発覚し、2026-05-24 に code 上で `@audit:defect(false-statement)` タグ付与 + 3 consumers (`isAwgnTypicalityHypothesis` / `awgn_achievability_F1_via_staged_hyps` / `awgn_theorem_F4_discharged_F1_via_staged`) の docstring に **UPSTREAM DEFECT** ブロックを記入済 (commit `4d7e67e`)。本 sibling plan で **predicate を P' < P スラック付きの honest staged 形に reshape** し、consumer 側の最小書換で再封止する。**親 plan に積み上げる pivot session**、scope は「predicate 書換 + consumer 整合修正」のみ、achievability core (Phase A-D の本物 plumbing 580 行) は維持する。
>
> **Goal**: `IsAwgnPowerConstraintRealizable` を「**satisfiable** な honest staged hyp」 (parallel-gaussian / EPI と同型の Mathlib-壁 (b) staged) に reshape し、consumer 3 つを依存型整合させた上で `lake env lean Common2026/Shannon/AWGNAchievabilityDischarge.lean` を再 silent 化、`@audit:defect(false-statement)` タグを `@audit:staged(awgn-power-constraint-realizable-v2)` 等の honest staging に降格する。
>
> **撤退ライン (本 plan 内)**: [P-1] predicate 内部に ∃ P' を入れる素朴版で consumer の `gaussianCodebook M n P.toNNReal` (現在 20 箇所超) を全部 P' 書換が必要になり 200 行超 → [P-2] 3 predicate を 1 bundle hyp に統合し consumer signature を縮約 / [P-3] consumer の Phase A 補題 (`gaussianCodebook_codeword_law` / `gaussianCodebook_indepFun_codewords` 等) が σsq parametric なので P' 書換は機械的、ただし `h_aep` / `h_rand` の signature 内 `P.toNNReal` も P' に動かす必要 / [P-4] 全部詰まったら honest staged のまま「predicate 内部の `n · P` を `n · (P − δ)` に弱める」非破壊 minimal fix のみで止める。**詳細 §撤退ライン**。
>
> **honesty 規律**: 本 plan の目的は false-statement defect を honest staged hyp に変換すること。完了後の predicate は 4 条件 (a) 型 ≠ `IsAwgnTypicalityHypothesis` 結論 / (b) docstring で「Mathlib 壁 (b)、NOT load-bearing for achievability core」明示 / (c) consumer が genuine consume (退化スロットでない) / (d) `@audit:staged(<slug>)` タグ — を満たすこと。Cover-Thomas 9.2 の標準解 (P' < P 生成 + SLLN) を Lean の hyp 側に押し付けるだけで、achievability core の expurgation + worst-half + reindex (~580 行) は何も変えない。

## 進捗

- [x] Phase 0 — 既存コード読み込み + consumer body の P-flow 棚卸し ✅ (planner 起草段階で棚卸し済、影響範囲リストとして本 plan の §影響範囲リストに reflect)
- [x] Phase 1 — predicate signature 確定 = **Option C bundled** ✅ (2026-05-24 user 判断、判断ログ #1)
- [x] Phase 2 — skeleton write (predicate 改修 + consumer signature 改修、本体は sorry) ✅ (2026-05-24、判断ログ #2、独立 audit clean)
- [x] Phase 3 — consumer body の P' threading (本体 fill) ✅ (2026-05-24、判断ログ #3、`2ace40b` 1641 行 / 0 sorry / silent)
- [ ] Phase 4 — verify + 独立 honesty audit + tag 降格 📋

## ゴール / Approach

### Approach (overall strategy / shape of solution)

**戦略**: Cover-Thomas 9.2 「codeword を variance `P' < P` で生成 → SLLN で `(1/n)∑Xᵢ² → P' < P` a.s. → `P(∑Xᵢ² ≤ nP) → 1`」を **predicate 側に押し付ける**。すなわち `IsAwgnPowerConstraintRealizable` は「適切な `P' < P` の存在 + その `P'` のもとでの mass bound」を主張する predicate になり、consumer は `obtain ⟨P', hP'_pos, hP'_lt_P, hN₀, h_mass⟩ := h_power ...` で P' を取り出して以降の random codebook law を `gaussianCodebook M n P'.toNNReal` に切り替える。

**最小侵襲の核**: 3 staged hyp (`h_aep` / `h_rand` / `h_power`) のうち、**`h_power` が「適切な P' を供給する witness」になり、他 2 つ (`h_aep` / `h_rand`) もその同じ P' のもとで bound を主張する**。これを実装する形として 3 案を比較し、Phase 1 で確定する。

```
3 hyp 並列 (現状、defect)        →    P' bundled (本 plan ゴール)
─────────────────────────         ─────────────────────────────
h_aep   : ...(P)...                h_aep'  : ∀ P' ∈ (0, P], ...(P')...
h_rand  : ...(P)...                h_rand' : ∀ P' ∈ (0, P], ...(P')...
h_power : (false, ...(P)...)       h_power': ∃ P' ∈ (0, P], ...(P')...

isAwgnTypicalityHypothesis P N h_meas h_aep h_rand h_power
  consumer body: gaussianCodebook M n P.toNNReal を直接 reference (20+ 箇所)
  → P を P' に書き換え + Phase A 補題 (σsq parametric) を P' で再起動
```

**3 案比較** (Phase 1 で確定、現時点の暫定推し: **Option C bundled**):

| Option | predicate 改修 | consumer signature 改修 | consumer body 改修 | 規模 |
|---|---|---|---|---|
| **A**: 各 predicate に `(P' : ℝ) (hP' : P' < P)` を **explicit** 引数追加、`h_power` が P' を選ぶ | 3 predicate × +2 引数 | 3 hyp すべて `∀ P' < P, predicate P' N` 形に lift | `obtain ⟨P', hP'⟩ := h_power ...` 後、`h_aep P' hP' ...` / `h_rand P' hP' ...` を invoke | 中〜大 |
| **B**: `h_power` のみ `∃ P' < P, (mass bound at P')` 形、`h_aep` / `h_rand` は **そのまま `P` で書き、内部の `gaussianCodebook M n P.toNNReal` を `Measure.pi (gaussianReal 0 P'.toNNReal)` に置換しない**。consumer 側で `h_aep` / `h_rand` の P 形 bound を P' 形に **measure-tilt** で乗り換え | h_power 1 個のみ +∃ | h_power のみ | tilt bridge が新規 (重)、却下候補 | 大 |
| **C** (推し): **3 hyp を 1 bundle hyp に統合**。新 predicate `IsAwgnRandomCodingFeasible P N h_meas` が `∃ P' ∈ (0, P], (3 bound 全部 at P')` を主張。consumer signature は `(h_feasible : IsAwgnRandomCodingFeasible P N h_meas)` 1 本に縮約 | 3 → 1 統合 + 旧 3 predicate は thin alias 化 or deprecate | 3 → 1 hyp | `obtain ⟨P', hP'_pos, hP'_lt_P, h_aep_at_P', h_rand_at_P', h_power_at_P'⟩` 後は body 既存 plumbing をそのまま回す (内部 `gaussianCodebook M n P.toNNReal` を `gaussianCodebook M n P'.toNNReal` に sed 置換するだけ) | 中 |

**Option C の優位性**:

- consumer の Phase A 補題は `(σsq : ℝ≥0)` を引数に取る (`Common2026/Shannon/AWGNAchievabilityDischarge.lean:50-93`)。`σsq := P.toNNReal` → `σsq := P'.toNNReal` 入れ替えは型整合する。
- `awgn_exists_codebook_le_avg` (`:622`) も `σsq` 抽象、Phase D の expurgation chain は P 非依存。
- consumer body の P-flow 改修点は `gaussianCodebook M n P.toNNReal` の 20+ 箇所を `P'.toNNReal` に置換、`PowSet` の target `n · P` は **`n · P` のまま** (codebook は P' で生成、constraint target は P で評価、ここに SLLN slack が乗る形)。
- 3 hyp → 1 hyp に統合することで「3 つの P' が独立に選ばれて整合しない」というリスクを構造的に排除。
- 旧 3 predicate は `@audit:staged(...)` タグ付きで残置 (alias)、新 bundle が SoT。

**Option C の劣位性**:

- bundle predicate は 3 sub-bound を ∧ で持つ「fat predicate」で読みづらい。
- 旧 3 predicate との関係を docstring + audit-tag で明示する必要 (deprecate or alias)。
- 万一 (a) 型独立 / (b) docstring honesty が崩れたら独立 audit で reject されるリスク。

### Mathlib-shape-driven definition check (CLAUDE.md)

新 predicate の主役は `gaussianCodebook M n P'.toNNReal` の mass on `{c | ∀ m, ∑(c m i)² ≤ n · P}`。これを支える Mathlib lemma:

- `MeasureTheory.measurePreserving_eval` (既に Phase A で消費、変更不要)
- `iIndepFun_pi` (同上、Phase A で消費)
- `ProbabilityTheory.strong_law_ae_real` (predicate 自体の discharge で必要、本 plan の **後段**)

bundle predicate の結論形は「3 sub-mass bound の ∧」で、consumer の `obtain ⟨P', hP'_pos, hP'_lt_P, h_aep', h_rand', h_power'⟩` パターンが直接 fire できる shape。`f (compProd ...)` reshape bridge は不要 (sub-bound は既存 `IsContinuousAEPGaussian` / `IsAwgnRandomCodingBound` と同形)。

### 規模見積もり

| Phase | 内容 | 行数 | session |
|---|---|---|---|
| Phase 0 | consumer body の P-flow 棚卸し (.md 内のみ) | 0 (md) | 0.25 |
| Phase 1 | predicate signature 確定 + 判断ログ | 0 (md) | 0.25 |
| Phase 2 | skeleton write (predicate + consumer signature) | +30〜50 (Lean) | 0.5 |
| Phase 3 | consumer body の P' threading (本体 fill) | sed 系 ~80, 新規 ~20-50 | 1 |
| Phase 4 | verify + audit + tag 降格 | 0 (Lean), tag 1 + audit md +20 | 0.25 |
| **合計** | | **~+100〜+130 行 net** | **2-2.5 session** |

現状 `AWGNAchievabilityDischarge.lean` 1563 行 → pivot 後 **~1620-1700 行**想定 (Option C で predicate 統合 + 旧 3 hyp alias 化分が増、body diff は sed 主体)。Option A だと 200+ 行膨らむ。

## 影響範囲リスト

### Code-side (touch 必要、`Common2026/Shannon/AWGNAchievabilityDischarge.lean`)

**predicate 改修 (主):**

- `:735-743` `def IsAwgnPowerConstraintRealizable` — Option C 採用なら **bundle predicate 新設** `def IsAwgnRandomCodingFeasible (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop`、旧 `IsAwgnPowerConstraintRealizable` は honest alias 化 (旧 false-statement は `@audit:defect(...)` から `@audit:staged(awgn-power-constraint-realizable-v2)` に降格、内部に `n · P` でなく `n · P` のまま、ただし codebook を P' で生成する形で書き換え)
- 旧 `IsContinuousAEPGaussian` (`:140`) — Option C なら bundle 内部に inline 取り込み or P' 引数開放、Option A なら `(P' : ℝ) (hP' : 0 < P') (hP'_lt : P' ≤ P)` を追加
- 旧 `IsAwgnRandomCodingBound` (`:543`) — 同上

**consumer 改修 (本体):**

- `:904-1478` `theorem isAwgnTypicalityHypothesis` (~575 行)
  - `:907-909` signature の 3 hyp を 1 bundle hyp に
  - `:938-940` `obtain ⟨N_aep, ...⟩ := h_aep ...` / `:= h_rand ...` / `:= h_power ...` を **`obtain ⟨P', hP'_pos, hP'_lt_P, h_aep', h_rand', h_power'⟩ := h_feasible ...` に置換**、以後 P' を let-bind
  - `:1024, :1033, :1036, :1039, :1042, :1084, :1116, :1118, :1127, :1130, :1131, :1134, :1146, :1157, :1162, :1169, :1189, :1194` `gaussianCodebook M n P.toNNReal` (合計 ~15 箇所) を `gaussianCodebook M n P'.toNNReal` に sed 置換
  - `:1041` `h_power_mass` の `≥ ENNReal.ofReal (1 - ε_pow)` 形は不変 (bundle 内に内包)
  - `:1295, :1298` `h_sub_power : ∀ j : Fin M_target, (∑ i, (subcodebook j i)^2) ≤ (n : ℝ) * P` (現状 `n · P` のまま、codebook は P' 生成だが constraint は P) — **ここが SLLN slack の本質**、変更不要
  - `:1470-1471` `awgn_extract_AwgnCode` 呼び出しは `P` のまま (`AwgnCode M_target n P` の型)
- `:1502-1514` `theorem awgn_achievability_F1_via_staged_hyps`
  - signature の 3 hyp を 1 bundle に
  - body の `isAwgnTypicalityHypothesis P hP N hN h_meas h_aep h_rand h_power` を `h_feasible` 1 本に
- `:1539-1561` `theorem awgn_theorem_F4_discharged_F1_via_staged`
  - signature の 3 hyp を 1 bundle に
  - body 同様

**docstring 改修 (defect → staged 降格):**

- `:696-734` `IsAwgnPowerConstraintRealizable` の docstring (38 行) — 全面書き換え、`@audit:defect(false-statement)` を `@audit:staged(awgn-power-constraint-realizable-v2)` に
- `:878-903` `isAwgnTypicalityHypothesis` docstring の "UPSTREAM DEFECT" ブロック削除、honest 3 staged (or 1 bundled) に書き戻す
- `:1483-1500` `awgn_achievability_F1_via_staged_hyps` docstring 同様
- `:1516-1538` `awgn_theorem_F4_discharged_F1_via_staged` docstring 同様

### Plan-side (touch 必要)

- `docs/shannon/awgn-achievability-typicality-plan.md` — 判断ログ #7 を append (本 pivot plan へのリンク + closure 状態)
- `docs/audit/awgn-achievability-typicality-staged-audit.md` — 必要なら independent re-audit の record 追記 (本 plan の Phase 4 で fresh `honesty-auditor` 起動結果)

### Plan-side (touch 不要)

- 親 `awgn-moonshot-plan.md` — F-1 撤退ライン entry は変更なし
- 兄弟 `awgn-f1-discharge-moonshot-plan.md` — 独立 (F-4 scope)
- inventory 5 axis 群 — Phase 0 で既に確定、再調査不要

## Phase 詳細

### Phase 0 — Consumer body P-flow 棚卸し 📋

- [ ] `isAwgnTypicalityHypothesis` (`:904-1478`) を section ごとに読み、`gaussianCodebook M n P.toNNReal` の **各 use site で「P を P' に変えても整合するか」** を line:context で列挙
- [ ] `PowSet := {c | ∀ m, ∑(c m i)² ≤ n · P}` の definition で `n · P` の `P` は **constraint target なので不変**、`gaussianCodebook` の `σsq` が `P'.toNNReal` に変わる、という分離を docstring で明示する文案を起草
- [ ] Phase A 補題 (`gaussianCodebook_codeword_law` / `gaussianCodebook_indepFun_codewords` / `gaussianCodebook_isProbabilityMeasure`) が `σsq` 抽象であることを再確認、call site が `P'.toNNReal` でも `infer_instance` が通るかを check (Phase A コード変更なしで通る想定)
- [ ] proof-log: no (棚卸しは plan md 内のみ)

### Phase 1 — Predicate signature 確定 📋

- [ ] Option A / B / C を docstring レベルで仮起草し、honesty 4 条件 (a-d) の各々を 1 行で評価
- [ ] **判断 #1 確定**: Option C bundle predicate を採用する根拠を判断ログに記録 (consumer signature 縮約 + P' 整合性の構造的保証)
- [ ] bundle predicate の name 決定 (暫定: `IsAwgnRandomCodingFeasible`)、slug 決定 (暫定: `awgn-random-coding-feasible`)
- [ ] 旧 3 predicate の扱い確定: (i) 残置 + audit-tag 降格 / (ii) deprecate alias / (iii) 削除して bundle 内に inline 取り込み — のいずれか
- [ ] proof-log: no

### Phase 2 — Skeleton write (predicate + consumer signature 改修) 📋

- [ ] **predicate 改修**: `IsAwgnRandomCodingFeasible` を新規 def、bundle 内に `∃ P' ∈ (0, P]` + 3 sub-bound (旧 IsContinuousAEPGaussian / IsAwgnRandomCodingBound / IsAwgnPowerConstraintRealizable に対応する形) を ∧ で並べる。`@audit:staged(awgn-random-coding-feasible)` タグ付与
- [ ] 旧 `IsAwgnPowerConstraintRealizable` の docstring を defect → staged-v2 に降格、bundle predicate との関係を 1 段で示す
- [ ] consumer 3 つ (`isAwgnTypicalityHypothesis` / `awgn_achievability_F1_via_staged_hyps` / `awgn_theorem_F4_discharged_F1_via_staged`) の signature を 3 hyp → 1 hyp に変更、body は **`sorry` 暫定** (Phase 3 で fill)
- [ ] `lake env lean Common2026/Shannon/AWGNAchievabilityDischarge.lean` で skeleton が type-check (3 sorry warning が出る想定、error 0)
- [ ] proof-log: yes (`proof-log-awgn-power-constraint-realizable-pivot-phase2.md`)

### Phase 3 — Consumer body の P' threading 📋

- [ ] `isAwgnTypicalityHypothesis` body 内の `obtain` 3 行を `obtain ⟨P', hP'_pos, hP'_lt_P, h_aep', h_rand', h_power'⟩ := h_feasible ...` に置換
- [ ] body 内 `gaussianCodebook M n P.toNNReal` の 15+ 箇所を `gaussianCodebook M n P'.toNNReal` に sed 置換、`P'` を let-bind して scope に乗せる
- [ ] `PowSet` の `n · P` (constraint target) は P で保持、`gaussianCodebook` の `σsq` だけ P' に切り替え、両者の **slack** で chi-square mass が ≥ 1 - ε_pow に乗ることを bundle predicate の `h_power'` から供給
- [ ] `awgn_extract_AwgnCode` 呼び出し時の `AwgnCode M_target n P` 型は **P のまま** (codebook は P'-generated だが、AwgnCode の power_constraint field が `∀ m, ∑(c m i)² ≤ n · P` で評価されるので合う)
- [ ] `awgn_achievability_F1_via_staged_hyps` / `awgn_theorem_F4_discharged_F1_via_staged` の body を 1 行 wrapper に書き直し
- [ ] `lake env lean ...` clean (0 sorry / 0 error / minimal warning)
- [ ] proof-log: yes (`proof-log-awgn-power-constraint-realizable-pivot-phase3.md`)

### Phase 4 — Verify + 独立 honesty audit + tag 降格 📋

- [ ] **独立 honesty-auditor 起動** (CLAUDE.md「Independent honesty audit」必須条件): `subagent_type: "honesty-auditor"` で fresh subagent を回し、新 bundle predicate `IsAwgnRandomCodingFeasible` を honesty 4 条件で verify。verdict が `OK` なら closure、`questionable` なら docstring refine、`DEFECT` なら predicate 再構成
- [ ] `scripts/audit_db.ts build` → `scan --check-db` で SoT-DB 整合確認
- [ ] 親 plan `awgn-achievability-typicality-plan.md` の判断ログ #7 append、進捗ブロックを「✅ Phase E 完走 (predicate pivot 後)」に更新
- [ ] `Common2026.lean` は既に編入済 (本 pivot で import 増減なし) なので変更なし
- [ ] proof-log: no

## 撤退ライン

### Scope 縮小ライン

- **P-1 (Option A 採用時): consumer body の P → P' 書換が 200+ 行膨張**
  - 縮退案: Option C bundled に切替、3 hyp 統合で書換規模を ~80 行に圧縮
  - 判定: Phase 3 着手時に体感 +100 行を超えたら

- **P-2 (Option B 採用時): tilt bridge が新規 ~150 行**
  - 縮退案: Option B 即時却下、Option A or C へ pivot
  - 判定: Phase 1 の初期評価で却下済とする

- **P-3 (Option C 採用時): bundle predicate が 4 条件 (a) 型独立を満たさない可能性**
  - 縮退案: bundle 中の 1 sub-bound が `IsAwgnTypicalityHypothesis` 結論型に類似していたら、その sub-bound を取り出して別 staged hyp に分離 (1 → 2 hyp)
  - 判定: Phase 4 独立 audit で reject されたら

- **P-4 (全部詰まったら): predicate を「`n · P` を `n · (P − δ)` に弱める」minimal fix のみ**
  - 縮退案: codebook 生成は P のまま、constraint target を `n · (P − δ)` に弱める (defect は残らないが、AwgnCode の `power_constraint : ∀ m, ∑ ≤ n · P` field との接続で `n · (P − δ) ≤ n · P` の自明 chain が必要)
  - 判定: Phase 3 が 1 session 超えたら検討

### honesty 撤退ライン (常時)

- ❌ name laundering: 新 bundle predicate を `IsAwgnAchievabilityHypothesis_bundled` 等の **結論型と同型な名前** にする
- ❌ 新 predicate の中で `∃ codebook (c : AwgnCode M n P), ∀ m, errorProbAt < ε` を含む (これは結論型直書き、4 条件 (a) 違反)
- ❌ 旧 `IsAwgnPowerConstraintRealizable` を **`Prop := True`** で穴埋め (CLAUDE.md「検証の誠実性」tells 違反、即拒否)
- ❌ 旧 predicate を残したまま **`@audit:defect(...)` タグだけ消す** (defect tells の隠蔽)
- ❌ Phase 4 independent audit を skip する (CLAUDE.md「Independent honesty audit」workflow 違反)

## Definition of Done

完了後の状態:

- `Common2026/Shannon/AWGNAchievabilityDischarge.lean` が `lake env lean` で silent
- `IsAwgnRandomCodingFeasible P N h_meas` (新 bundle predicate) が **honest staged** (4 条件遵守、`@audit:staged(awgn-random-coding-feasible)` タグ)
- 旧 `IsAwgnPowerConstraintRealizable` は (i) 削除 / (ii) bundle alias / (iii) `@audit:staged(awgn-power-constraint-realizable-v2)` 降格、のいずれかで closure
- `isAwgnTypicalityHypothesis` body が新 bundle hyp 1 本を consume する形 (旧 3 hyp 並列形は廃止)
- `awgn_achievability_F1_via_staged_hyps` / `awgn_theorem_F4_discharged_F1_via_staged` の `_via_staged` 命名は honest (1 hyp wrapper 化、name laundering 無し)
- 独立 `honesty-auditor` subagent の verdict が **`OK`**
- 親 plan 判断ログ #7 + 本 plan 判断ログに pivot 結果 append

**Genuine discharge ではなく honest staged**: 完了後の predicate は **依然 staged**。本 plan の goal は「false-statement defect を honest staged hyp に変換」までで、`IsAwgnRandomCodingFeasible` 自体の genuine discharge (n-d Gaussian SLLN + continuous SMB の Mathlib gap) は別 session (より大規模、Mathlib PR 視野) で扱う。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-24 — Phase 1 で Option C bundled を確定** (本 session, user 判断)。
   planner は 3 案比較の上 Option C 推奨、orchestrator は Option A (構造保存) を対抗案として提示、user が Option C 採用を判断。
   理由: (i) consumer signature を 3 hyp → 1 hyp に縮約することで P' 整合性を構造的に保証できる、(ii) consumer body の P→P' 書換は `gaussianCodebook M n P.toNNReal` (20+ use site) の sed 主体に圧縮可、(iii) Option A は 3 hyp 全部の signature lift が必要で全体改修コストが ~200 行と試算され大規模。
   コスト受容: bundle predicate は 3 sub-bound を ∧ で持つ「fat shape」で読みづらい点、3 staged hyp の独立 discharge が将来直交できなくなる点 (兄弟 staged plan が個別に走れない) は受容。Phase 4 の独立 honesty-auditor が 4 条件 (a) 型独立を verify する。
   実装は次 session で Phase 2 skeleton 起こしから着手 (predicate 改修 + consumer signature 改修、body は sorry 暫定)。

2. **2026-05-24 — Phase 2 skeleton write 完了 + 独立 honesty audit clean** (本 session)。
   実装結果 (`Common2026/Shannon/AWGNAchievabilityDischarge.lean` 989 行、−574 行 vs pivot 前、Phase 3 で body 復元予定):
   - 新規 `IsAwgnPowerConstraintHonest (P_cb P_target : ℝ) (N : ℝ≥0)` (line 815, `@audit:staged(awgn-power-constraint-honest)`) — codebook 生成 / constraint target 分離形
   - 新規 `IsAwgnRandomCodingFeasible (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)` (line 860, `@audit:staged(awgn-random-coding-feasible)`) — bundle、`∀ R, ∃ P' ∈ (0, P]` + rate margin + AEP + RandomCodingBound + PowerConstraintHonest
   - 旧 `IsAwgnPowerConstraintRealizable` (line 735) は **削除せず** orphan 化、`@audit:defect(false-statement)` タグ・body 完全不変で残置 (honesty record)。alias 化を試みたが honest predicate に degenerate instance を作ると依然 unsatisfiable で audit-tags rule に抵触するため放棄
   - consumer 3 件 signature を 3 hyp → 1 bundle hyp に縮約 (`isAwgnTypicalityHypothesis` @:961 body sorry、wrapper 2 件 term-mode で transitively 継承)
   - **R quantifier の位置**: bundle 起草時に最初 `∃ P' : ℝ, 0 < P' ∧ P' ≤ P ∧ (3 sub-bound at P')` (R 非依存) を試したが、`IsAwgnRandomCodingBound P' N h_meas` が `R < (1/2) log(1+P'/N)` を内部要求するため bundle 中で R を消費できないと判明。`∀ R, R-conds → ∃ P', R < (1/2)log(1+P'/N) ∧ ...` の R-outer 形に修正
   - **`P' ≤ P` (non-strict) soft caveat**: 独立 audit が指摘。`P' = P` を選ぶと `IsAwgnPowerConstraintHonest P P N` が v1 と同型に縮退する。Phase 2 closure blocker ではない (docstring が "intended use P_cb < P_target" を明示) が、Phase 3 で discharge する際は strict `<` に upgrade or 別途 warning 検討
   - 独立 audit (general-purpose fresh subagent、CORE doctrine inline) verdict: 両 predicate とも `load_bearing_hyp / honest 🟢ʰ`、defect なし、name laundering なし。Mathlib gap (continuous SMB / n-d differentialEntropy / chi-square SLLN) loogle 裏取り済。タグ `@audit:suspect(awgn-power-constraint-realizable-pivot)` を `@audit:staged(...)` と併記 (lines 783, 860)
   - proof-log: `docs/proof-logs/proof-log-awgn-power-constraint-realizable-pivot-phase2.md`
   - **Phase 3 着手準備**: bundle destructure `obtain ⟨P', hP'_pos, hP'_lt_P, hR_lt_P'C, h_aep', h_rand', h_power'⟩ := h_feasible hR_pos hR` を body 先頭に置き、580 行 assembly の `gaussianCodebook M n P.toNNReal` → `gaussianCodebook M n P'.toNNReal` を 15+ 箇所 sed、`PowSet` の `n · P` constraint target は不変

3. **2026-05-24 — Phase 3 body fill 完了** (本 session, lean-implementer worktree isolation)。
   実装結果 (`Common2026/Shannon/AWGNAchievabilityDischarge.lean` 1641 行 / 0 sorry / silent, commit `2ace40b`):
   - 旧 body (`4d7e67e^:892-1483`) を git history から抽出、bundle 形に 4 変換を施して復元: (a) `obtain ⟨P', hP'_pos, hP'_lt_P, hR_lt_P'C, h_aep', h_rand', h_power'⟩ := h_feasible hR_pos hR` を `classical` 直後に挿入、(b) `set C := (1/2) log(1 + P/N)` → `P'` 側、(c) hyp 名 `h_aep` / `h_rand` / `h_power` → `h_*'`、(d) `gaussianCodebook M n P.toNNReal` → `P'.toNNReal` 14 箇所 + `awgn_exists_codebook_le_avg (σsq := P.toNNReal)` 呼出 1 箇所 = 計 15 sed
   - `PowSet := {c | ∀ m, ∑(c m i)² ≤ n · P}` の `n · P` constraint target、`awgn_extract_AwgnCode (P := P)` 呼出、`AwgnCode M_target n P` 型はすべて P 不変 (codebook 生成側のみ P' に切替、SLLN slack `P − P'` が constraint mass bound に乗る形)
   - **計画外の派生 (1 turn)**: `IsAwgnPowerConstraintHonest P' P N` (`:784`) の rate-bound 行 (`:786`) が `R < (1/2) log(1 + P_target/N)` (= P 側 capacity) を要求するが、bundle destructure で得られる `hR_lt_P'C` (= `hR_lt_C` after `set C`) は P' 側 capacity。`P' ≤ P` (bundle 自身が供給) + `Real.log_le_log` (もしくは `Real.log_le_log_iff`) で `(1/2) log(1+P'/N) ≤ (1/2) log(1+P/N)` を派生 → `hR''_lt_PC := lt_of_lt_of_le hR''_lt_C h_log_le` を作って `h_power' hε_pow_pos hR''_pos hR''_lt_PC` に渡す 20 行の追加。計画書 §Phase 3 詳細は mechanical 4 変換のみ列挙、本派生は LSP 第 1 戻りで即発覚
   - **honest plumbing 判定**: 上記 20 行は新規 staged predicate ではなく既存 `hP'_lt_P` (bundle) + `Real.log_le_log` (Mathlib) からの bridge。独立 honesty audit 起動条件 (新規 staged / 既存 staged signature 変更) いずれにも非該当
   - **proof-log 主要観察**: (1) bundle predicate は body 復元時の sed-friendliness にも効く (3 hyp 名 → 3 hyp' 名の 1 文字置換のみ) — Cover-Thomas 9.x 系の他の load-bearing hyp 候補に応用可、(2) 「P_cb / P_target 分離」型 predicate は consumer 側で sub-bound 毎の rate-bound 引数の P_cb 側 / P_target 側を追跡する必要、pivot plan に「sub-bound 引数表」を 1 枚追加すると本件のような型 mismatch を事前検出可能
   - proof-log: `docs/proof-logs/proof-log-awgn-power-constraint-realizable-pivot-phase3.md`
   - **soft caveat 再掲**: `P' ≤ P` (non-strict) のため `P' = P` 退化を許容、その場合 `IsAwgnPowerConstraintHonest P P N` が v1 unsatisfiable に戻る。本 Phase 3 body 自体は `P' < P` を必要としない (`P'.toNNReal` variance + `n · P` target は `P' = P` でも形式的に通る) ため defect ではないが、bundle の discharger 側 (Phase 4 以降の genuine fill or Mathlib PR) で `P' < P` を必ず選ばせる責務が残る
   - **Phase 4 着手準備**: 0 sorry 達成。Phase 4 は (i) 独立 `honesty-auditor` subagent 起動 (bundle predicate `IsAwgnRandomCodingFeasible` + `IsAwgnPowerConstraintHonest` を 4 条件 verify、Phase 2 で 1 度 audit 済だが Phase 3 body fill 後に再 audit すべきか judge)、(ii) 親 plan `awgn-achievability-typicality-plan.md` 判断ログ #7 append、(iii) audit-tag `@audit:suspect(awgn-power-constraint-realizable-pivot)` の closure (Phase 2 で並記したが Phase 3 完了で pivot 完成のため `suspect` → 解除)

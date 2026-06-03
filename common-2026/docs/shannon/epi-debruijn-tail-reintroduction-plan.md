# EPI de Bruijn: `IsDeBruijnTailHyp` honest re-introduction mini-plan

> **Parent**: [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md) §Phase C-5
> **Sister**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §Phase A
> (`g(∞) = 0` Gaussian limit discharge は本 mini-plan の `tail_limit` field を消費)
> **Status**: 未着手 (2026-05-25 起草)、inventory 待ち
> **Created**: 2026-05-25 (Wave 3 third batch retract 後の honest re-introduction track)

<!--
雛形メモ:
- 記法は moonshot-plan-template と同じ（状態絵文字、取り消し線、判断ログ）
- Parent ヘッダは必須。ナビゲーション + 親更新時の同期点として使う
- 本 mini-plan は親 plan Phase C-5 の sub-plan として位置付ける
- 完了報告 / 完成判定は親 plan 側 Phase C-5 checkbox + sister sub-plan Phase A 入口 unblock
-->

## Position

- 親 moonshot: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md)
  (L-EPI2 de Bruijn integration の Phase D 出力に紐付く tail externalization 部)
- 親 sub-plan: [`epi-debruijn-integration-plan.md`](./epi-debruijn-integration-plan.md)
  Phase C-5 (line 363 付近、checkbox 1 件)
- sister 入口: [`epi-stam-to-conclusion-plan.md`](./epi-stam-to-conclusion-plan.md)
  Phase A (Csiszár scaling argument、`g(∞) = 0` discharge の入口、本 mini-plan の
  `tail_limit` field がここに供給される)
- 関連 inventory (作成中、sister agent 並走): [`epi-debruijn-tail-mathlib-inventory.md`](./epi-debruijn-tail-mathlib-inventory.md)
  (EReal / ℝ≥0∞ の `Tendsto _ atTop (𝓝 ⊤)` 結論形 API 棚卸し)

## Motivation

`epi-debruijn-integration-plan` Phase C は bounded `T` 区間で de Bruijn integration を
genuine 化済だが、`(0, T) → (0, ∞)` の tail-analysis は externalize の必要があり、
当初 `IsDeBruijnTailHyp X Z P` honest hypothesis として外出ししていた。
**Wave 3 third batch (commit `823e150`, 2026-05-25)** で当該 predicate を独立 honesty
audit が **DEFECT verdict** `defect(epi-debruijn-tail-vacuous-and-empty)` で
**retract**。

honest 再導入が必要な理由:

1. **sister sub-plan の合流 Phase A unblock**: `epi-stam-to-conclusion-plan` Phase A の
   `g(∞) = 0` Gaussian limit discharge は heat-flow path tail (`T → ∞`) を必要とする。
   bounded `T` だけでは合流定理が組めない (`g(0) ≤ g(∞) = 0` の `∞` endpoint が無い)。
2. **親 plan Phase D 着手前提**: 親 plan の Phase D は `IsStamToEPIBridgeHyp` への
   入口形式整形、ここでも tail externalization が必須 (親 plan 撤退ライン
   L-DB-D-α 参照 `epi-debruijn-integration-plan.md:444`)。
3. **predicate 自身の honest closure**: retracted state のまま放置すると、Phase C-5
   checkbox が永久に未着手で、親 plan の closure 不能。retract コメントは保存しつつ
   honest re-introduction を試みる。

## Defect history (retract 経緯)

### 第一次 retract (Wave 3 third batch, 2026-05-25, commit `823e150`)

- **対象**: 旧 `IsDeBruijnTailHyp X Z P` (元 `InformationTheory/Shannon/EPIL3Integration.lean:589`)
- **試作品 signature** (要約):
  ```lean
  structure IsDeBruijnTailHyp (X Z : Ω → ℝ) (P : Measure Ω) where
    h_inf : ℝ
    tail_limit :
      Tendsto (fun T : ℝ => differentialEntropy
                              (P.map (gaussianConvolution X Z T)))
              atTop (𝓝 h_inf)
  ```
- **独立 audit verdict**: `defect(epi-debruijn-tail-vacuous-and-empty)`
  (Wave 3 third batch closure audit、2026-05-25)
- **DEFECT 根拠 (2 重)**:
  1. **Vacuous-bypass channel survive**: structure に
     `Z_law : P.map Z = gaussianReal 0 1` 不在 → `Z := fun _ ↦ 0` を選ぶと
     `gaussianConvolution X Z T = X` pointwise → tail entropy は定数 →
     `tail_limit` は `tendsto_const_nhds` で trivially 充足。
  2. **Semantically empty even after `Z_law`**: `Z ∼ 𝒩(0,1)` 仮定下では
     `h(X+√T·Z) → +∞` (Gaussian sub-entropy 下界
     `(1/2) log (2πe · T)`) → `Tendsto _ atTop (𝓝 h_inf)` for `h_inf : ℝ` は
     essentially uninhabited (predicate ≡ `False`) → 任意 consumer が vacuously
     OK で discharge content ゼロ。
- **retract コメント保存場所**:
  `InformationTheory/Shannon/EPIL3Integration.lean:595-613` (retraction notice)
- **consumer 影響**: 0 件 (Phase D は sister-plan pending、§12 docstring 言及のみ)
- **詳細記録**: 親 plan `epi-debruijn-integration-plan.md` §Upstream defects
  Defect #3 (line 508 付近)

### honest 再導入の必須条件

retract verdict から導かれる 2 条件:

| condition | 内容 | 根拠 |
|---|---|---|
| **EReal lift** | `h_inf : ℝ` → `h_inf : EReal` (or `ℝ≥0∞`) で `+∞` 極限を表現可能化 | Gaussian sub-entropy `(1/2) log (2πe T) → +∞` を表現可能にする |
| **`Z_law` field** | `Z_law : P.map Z = gaussianReal 0 1` 追加で `Z = 0` bypass 封鎖 | vacuous-bypass channel を構造的に閉じる |

両方揃ったら独立 audit 再受検 (`honesty-auditor` subagent 必須起動)。
片方だけでは insufficient (例: `Z_law` だけ追加して `h_inf : ℝ` のままだと
predicate `≡ False`、`+∞` lift だけだと `Z = 0` bypass survive)。

---

## ゴール / Approach

### 全体戦略 (Mathlib-shape-driven)

新 `IsDeBruijnTailHyp X Z P` を以下 2 案で設計、**inventory (sister agent) 出力待ちで案 1 / 案 2 確定**:

- **案 1: `h_inf : EReal`** — Gaussian sub-entropy `(1/2) log (2πe T)` は `Tendsto _ atTop
  (𝓝 (⊤ : EReal))` の結論形に乗る。EReal は `OrderTopology` / `T2Space` を持ち、
  `Tendsto` 標準 API が広い。`h_inf = ⊤` で `+∞` 極限を表現。
- **案 2: `h_inf : ℝ≥0∞`** — Gaussian sub-entropy が `(0, ∞)` で正値域 (`T ≥ 1` から
  positive) なので `ℝ≥0∞` 上で表現できなくはないが、`differentialEntropy : ℝ` (signed)
  であり tail で negative 領域を排除しきれない可能性 → 退化型 `+∞` を表現するためだけに
  全 entropy 値を `ℝ≥0∞` に lift するのは shape ミスマッチが大きい。

**Mathlib-shape-driven 規律** (CLAUDE.md §「Mathlib-shape-driven Definitions」):

支配補題候補 (3 件):

1. `Filter.Tendsto.tendsto_atTop_of_isLUB` 系 (monotone limit → `⊤` 収束)
2. `EReal.tendsto_nhds_top_iff_real` 系 (`Tendsto f l (𝓝 ⊤) ↔ ∀ x, ∀ᶠ y in l, x < f y`)
3. `Tendsto.comp` 系 (`Tendsto` の composition 規則、`coe_real_ereal` lift 経由)

これらの **結論形をそのまま採用できる signature** を選ぶ。具体的 verbatim conclusion
form は sister inventory agent (`epi-debruijn-tail-mathlib-inventory.md` 並走起草中)
の出力待ち。**signature 確定は本 plan Phase T-1 で行う** (inventory 確認後)。

### 案 1 (EReal lift) 暫定 skeleton

```lean
-- inventory 確認後に確定。現状 sketch (Phase T-1 で書き直し):
structure IsDeBruijnTailHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : Type where
  /-- `Z` is the standard normal driving the heat flow (vacuous-bypass 封鎖). -/
  Z_law : P.map Z = gaussianReal 0 1
  /-- The tail limit value, allowed to be `⊤` for divergent cases. -/
  h_inf : EReal
  /-- `(0, ∞)` 上の tail-analysis convergence、EReal lift で `+∞` も表現可能。 -/
  tail_limit :
    Tendsto
      (fun T : ℝ => ((InformationTheory.Shannon.differentialEntropy
                        (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
                          X Z T))) : EReal))
      atTop (𝓝 h_inf)
```

### Approach 図

```
[retract notice EPIL3Integration.lean:595-613]
            (history record、保存)
                  ▼
       [inventory: epi-debruijn-tail-mathlib-inventory.md]
       (sister agent 並走、EReal vs ℝ≥0∞ API 棚卸し)
                  ▼
        Phase T-1 — signature 確定 (案 1 / 案 2)
                  ▼
        Phase T-2 — 新 def 書き直し (EPIL3Integration.lean、retract コメント保存)
                  ▼
        Phase T-3 — Gaussian discharge `isDeBruijnTailHyp_of_gaussian`
                    (h_inf = ⊤、Gaussian sub-entropy `(1/2) log (2πe T) → ⊤`)
                  ▼
        Phase T-4 — Audit tag 確定 (`@audit:staged(epi-debruijn-tail-reintroduction)`)
                  ▼
        Phase T-5 — export + 親 plan Phase C-5 checkbox 更新 (orchestrator)
                  ▼
        Phase T-V — verify (`lake env lean EPIL3Integration.lean` silent)
                  ▼
        [独立 honesty audit (`honesty-auditor` subagent) PASS]
                  ▼
        親 plan Phase C-5 closure → Phase D 着手可能 →
        sister Phase A の `g(∞) = 0` 入口 unblock
```

### 規模見積もり

| Phase | 自作要素 | 想定行数 | 依存 |
|---|---|---|---|
| T-1 | signature 確定 (inventory 参照) | ~10 (検討メモのみ、def 本体は T-2) | inventory 待ち |
| T-2 | 新 def 書き直し (Z_law + EReal lift) | ~30-50 | T-1 |
| T-3 | Gaussian discharge (`isDeBruijnTailHyp_of_gaussian`) | ~40-80 | T-2 |
| T-4 | audit tag 確定 | ~3-5 | T-3 |
| T-5 | export + 親 plan checkbox | ~5 (orchestrator) | T-4 |
| T-V | verify | ~5 (検証 only) | T-5 |
| **合計** | | **~80-150** | |

中央予測 **~120 行**、`EPIL3Integration.lean` 内に追加 (retract コメント直下、約 line
613 以下に挿入)、新規 file 作成は不要。

---

## 進捗

- [ ] Phase T-1 — signature 確定 (inventory 参照) 📋
- [ ] Phase T-2 — 新 `IsDeBruijnTailHyp` def 書き直し 📋
- [ ] Phase T-3 — Gaussian discharge `isDeBruijnTailHyp_of_gaussian` 📋
- [ ] Phase T-4 — Audit tag 確定 (`@audit:staged(epi-debruijn-tail-reintroduction)`) 📋
- [ ] Phase T-5 — export + 親 plan Phase C-5 checkbox 更新 📋
- [ ] Phase T-V — verify (`lake env lean InformationTheory/Shannon/EPIL3Integration.lean` silent) 📋

proof-log: no (mini-plan 規模 ~120 行で proof-log を作るほどの session 規模に
ならない見込み、判断ログのみで十分。`@audit:staged(epi-debruijn-tail-reintroduction)`
を新規導入する場合は **independent honesty audit (`honesty-auditor` subagent)**
が orchestrator 必須起動)

---

## 代替案併記 (低コスト退避)

### 案 1 (推奨): EReal lift + Z_law field 追加

上記 Approach 図の通り。**inventory 確認待ち**。

- **長所**: 完全な honest re-introduction、independent audit PASS が見込める、Phase A
  入口 unblock 達成
- **短所**: EReal API ripple (~30-60 行)、`Tendsto _ atTop (𝓝 (⊤ : EReal))` 結論形が
  Mathlib に直接 lemma で書かれているか要確認 (inventory 出力次第)

### 案 2: `h_inf : ℝ≥0∞` (退避案 1)

- **長所**: `ℝ≥0∞` は Mathlib API 豊富 (`MeasureTheory` 系で多用)、`Tendsto _ atTop
  (𝓝 ∞)` 形が標準
- **短所**: `differentialEntropy : ℝ` (signed) を `ℝ≥0∞` に lift する際の負値処理が
  shape ミスマッチ (tail で `T → ∞` なら正値だが、`T → 0⁺` 側で `(1/2) log (2πe T)
  → -∞` の領域は表現不能、`(0, ∞)` 全域 lift には不向き)
- **発動条件**: EReal lift で Mathlib API が不足し ~100 行超の plumbing が必要と
  判明した場合、または inventory で `Tendsto _ atTop (𝓝 (⊤ : EReal))` 結論形の
  Mathlib lemma が皆無で `ℝ≥0∞` のほうが豊富と判明した場合

### 案 3 (skip / 押し出し): Phase D 内で `(0, T) bounded` のまま展開、tail は plan-level pending

`IsDeBruijnTailHyp` 自体を再導入せず、親 plan Phase D / sister sub-plan Phase A が
**bounded `T` のまま** Csiszár scaling argument を組み、`g(∞) = 0` discharge を
Cover-Thomas tail bound 経由 (Mathlib 上流貢献 task) で迂回。本 mini-plan 自体を
skip する選択。

- **長所**: 本 mini-plan の作業をゼロ化、`@audit:staged` 新規導入を回避
- **短所**: sister Phase A `g(∞) = 0` discharge の honest 化が大幅に複雑化、
  partial publish しかできない (Gaussian 限定 closure に下がる)
- **発動条件**: 案 1 / 案 2 ともに大規模化 (>200 行)、または inventory で
  EReal / ℝ≥0∞ 両 API ともに不足と判明した場合

**inventory 出力待ちで案 1 / 案 2 / 案 3 を確定** (Phase T-1)。

---

## Phase 詳細

### Phase T-1 — signature 確定 (inventory 参照) 📋

- [ ] **T-1.1**: sister inventory agent 出力 `docs/shannon/epi-debruijn-tail-mathlib-inventory.md`
      を Read で確認
- [ ] **T-1.2**: `Tendsto _ atTop (𝓝 (⊤ : EReal))` / `Tendsto _ atTop (𝓝 (∞ : ℝ≥0∞))`
      結論形 API 在庫を比較 (1-3 候補)
- [ ] **T-1.3**: Gaussian sub-entropy `(1/2) log (2πe T) → ⊤` の発散 lemma
      存在確認 (`Real.tendsto_log_atTop` + scaling、または既存 Gaussian entropy
      asymptotics)
- [ ] **T-1.4**: 案 1 / 案 2 / 案 3 のいずれかを確定、判断ログに記録
      (発動条件は §代替案併記 参照)

依存: sister inventory agent (`epi-debruijn-tail-mathlib-inventory.md`) の出力。
sister 並走中なら待つ。本 phase で確定するまで T-2 着手不可。

規模: ~10 行 (検討メモのみ、def 本体は T-2)。

### Phase T-2 — 新 `IsDeBruijnTailHyp` def 書き直し 📋

- [ ] **T-2.1**: `InformationTheory/Shannon/EPIL3Integration.lean:613` 以下、retract コメント
      (`:595-613`) **保存しつつ** その直下に新 def 挿入
- [ ] **T-2.2**: 案 1 (EReal lift + Z_law field) signature を verbatim 書き出し
      (sister inventory の結論形に厳密整合)
- [ ] **T-2.3**: docstring に下記を明記:
      - Wave 3 third batch retract 経緯への参照
        (`InformationTheory/Shannon/EPIL3Integration.lean:595-613` retract notice)
      - 新 signature の honest 化根拠 (`Z_law` field で vacuous-bypass 封鎖、`EReal`
        lift で `+∞` 極限表現可能)
      - **NOT a discharge / load-bearing on `Z_law` + tail-limit**
      - `@audit:staged(epi-debruijn-tail-reintroduction)` 追加 (Phase T-4)
- [ ] **T-2.4**: 関連 import 追加 (`Mathlib.Topology.Instances.EReal` or
      `Mathlib.Analysis.SpecialFunctions.Log.Basic` 等、pinpoint import 規律遵守)

retract コメント `(retracted 2026-05-25, Wave 3 third batch independent audit)` は
削除せず history record として保存 (将来の audit / handoff 時に retract 経緯が
1 grep で復元できる)。

規模: ~30-50 行 (def + docstring + import)。

### Phase T-3 — Gaussian discharge `isDeBruijnTailHyp_of_gaussian` 📋

- [ ] **T-3.1**: 対象 lemma シグネチャ (案 1 採用時):
      ```lean
      theorem isDeBruijnTailHyp_of_gaussian
          {Ω : Type*} [MeasurableSpace Ω]
          (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
          (hX_gauss : ∃ m v, P.map X = gaussianReal m v)
          (hZ_law : P.map Z = gaussianReal 0 1)
          (hIndep : IndepFun X Z P) :
          IsDeBruijnTailHyp X Z P
      ```
- [ ] **T-3.2**: `h_inf := ⊤` を構成 (発散 case)
- [ ] **T-3.3**: `Z_law` field は `hZ_law` 仮定で直接充足
- [ ] **T-3.4**: `tail_limit` field の証明:
      - Gaussian + independent Gaussian の `gaussianConvolution X Z T` は
        `gaussianReal m (v + T)` (分散加法、既存
        `gaussianReal_add_gaussianReal_of_indepFun` 経由)
      - `differentialEntropy (gaussianReal m (v + T)) = (1/2) log (2πe (v + T))`
        (既存 Gaussian entropy 閉形、`EntropyPowerInequality.lean:226` 周辺)
      - `Tendsto (fun T => (1/2) log (2πe (v + T))) atTop (𝓝 (⊤ : EReal))`
        を `Real.tendsto_log_atTop` + EReal coe lift で証明
- [ ] **T-3.5**: 必要なら補助 lemma を 1-2 件追加
      (e.g. `Real.tendsto_log_coe_ereal_atTop_top` が無ければ)

規模: ~40-80 行。inventory 出力次第で `Tendsto _ atTop (𝓝 ⊤)` の coe lift が
直接 1 行 lemma なら下振れ、自作 5-10 行で済まなければ補助 lemma 必要で上振れ。

### Phase T-4 — Audit tag 確定 📋

- [ ] **T-4.1**: 新 def docstring 末尾に
      `@audit:staged(epi-debruijn-tail-reintroduction)` 追加
- [ ] **T-4.2**: `docs/audit/audit-tags.md` §語彙 §`staged(WALL)` 行を確認、
      SLUG が新規追加で語彙整合確認 (extensible なので追加自体は OK、
      ただし `staged(WALL)` の WALL は Mathlib 壁名彙 (e.g. `stam`, `csiszar`,
      `n-dim-gaussian-aep`) に倣う命名規約があり、本 SLUG は plan slug 形式
      `epi-debruijn-tail-reintroduction` だが、内容としては `csiszar` 系の
      tail-analysis 壁を含意。**SLUG 命名の最終判定は audit-tags.md vocabulary
      keeper に確認、語彙不整合なら `suspect(epi-debruijn-tail-reintroduction)`
      に書き換え検討**)
- [ ] **T-4.3**: 親 plan `epi-debruijn-integration-plan.md` §Upstream defects
      Defect #3 に「2026-05-25 Phase C-5 honest re-introduction 完了、新 SLUG
      `@audit:staged(epi-debruijn-tail-reintroduction)`」を追記 (orchestrator
      担当)

規模: ~3-5 行 (tag 1 行 + audit-tags.md vocabulary 整合確認)。

### Phase T-5 — export + 親 plan Phase C-5 checkbox 更新 📋

- [ ] **T-5.1**: 親 plan `epi-debruijn-integration-plan.md` Phase C-5 checkbox を
      `[x]` に更新 (**orchestrator 担当**、本 mini-plan は触らない)
- [ ] **T-5.2**: 親 plan Phase D 着手可能を判断ログに記録 (本 mini-plan + sister
      Phase A の双方が unblock された旨を明示)
- [ ] **T-5.3**: sister sub-plan `epi-stam-to-conclusion-plan.md` Phase A の
      入口 lemma 要件と整合確認 (`tail_limit` field の consumer が sister Phase
      A のどこか確認)

規模: ~5 行 (orchestrator 経由の plan 更新のみ、本 mini-plan は touch せず)。

### Phase T-V — verify 📋

- [ ] **T-V.1**: `lake env lean InformationTheory/Shannon/EPIL3Integration.lean` silent
      (0 sorry / 0 warning)
- [ ] **T-V.2**: 必要なら `lake build InformationTheory.Shannon.EPIL3Integration` で
      olean 再生成 (dependent file の phantom unknown identifier 防止)
- [ ] **T-V.3**: 関連 file の silent 確認:
      - `InformationTheory/Shannon/EPIStamDischarge.lean` (de Bruijn integration 出力)
      - `InformationTheory/Shannon/FisherInfoV2.lean` (`gaussianConvolution` 経由)
- [ ] **T-V.4**: **Independent honesty audit (`honesty-auditor` subagent)**:
      orchestrator が `subagent_type: "honesty-auditor"` で fresh subagent を
      起動、新規 `@audit:staged(epi-debruijn-tail-reintroduction)` predicate に
      対し audit。verdict が:
      - 全 OK → 本 mini-plan closure
      - questionable → docstring refine
      - DEFECT → predicate 撤回 or 修正、再 audit

規模: 検証 only ~5 行 (時間: 数分)。

---

## Done 条件

- 新 `IsDeBruijnTailHyp` が `@audit:staged(epi-debruijn-tail-reintroduction)` で
  honest hypothesis (型 ≠ 結論、`Z_law` field で vacuous-bypass 封鎖、`h_inf : EReal`
  or `ℝ≥0∞` で `+∞` 極限表現)
- Gaussian instance 成立 (`isDeBruijnTailHyp_of_gaussian` で genuine discharge、
  Gaussian limit `(1/2) log (2πe T) → ⊤`)
- `lake env lean InformationTheory/Shannon/EPIL3Integration.lean` silent (0 sorry / 0
  warning)
- **Independent honesty audit (`honesty-auditor` subagent) PASS verdict**
- 親 plan `epi-debruijn-integration-plan.md` Phase C-5 checkbox `[x]` 更新済
  (orchestrator 経由)
- sister sub-plan `epi-stam-to-conclusion-plan.md` Phase A 入口 (`tail_limit`
  field 受け渡し) と integration 確認

---

## 撤退ライン (honest 限定)

| slug | Phase | 内容 | hypothesis / 退避先 | 解除条件 |
|---|---|---|---|---|
| **L-Tail-α** | T-1 | EReal API が不足 (`Tendsto _ atTop (𝓝 (⊤ : EReal))` 結論形 Mathlib lemma 皆無) | `ℝ≥0∞` 案 2 に退避、または案 3 (skip) | Mathlib 上流貢献で EReal Tendsto API 整備、または ℝ≥0∞ で十分と判明 |
| **L-Tail-β** | T-3 | Gaussian sub-entropy `(1/2) log (2πe T) → ⊤` の Mathlib bridge が無く自作 ~50 行超 | tail discharge も staged 化 (`@audit:staged(epi-debruijn-tail-gaussian-divergence)`)、`isDeBruijnTailHyp_of_gaussian` を honest hypothesis に置換 | Mathlib `Real.tendsto_log_atTop` + EReal coe lift API 整備 |
| **L-Tail-γ** | T-2 | `Z_law` 追加が他 consumer (FisherInfoV2.lean 等) に rippling 巨大化 (>100 行) | 案 3 (skip) に退避、Phase D 内 bounded T closure に押し出し | consumer ripple を局所化する補助 wrapper lemma を別 sub-plan で導入 |

**全撤退ライン共通規律** (CLAUDE.md §「検証の誠実性」):

- **`Prop := True` placeholder 禁止**
- **結論型 ≡ 仮説型 + `body := h` (循環) 禁止**
- **退化定義の悪用禁止** (Wave 3 third batch retract の DEFECT 根拠そのもの、
  Z = 0 で vacuous bypass する形は **2 度目はない**)
- **name laundering 禁止** (本 mini-plan は `*_discharged` / `*_full` 命名は
  使わない、`isDeBruijnTailHyp_of_gaussian` のような Gaussian 限定 instance は OK)
- 撤退ライン発動時は docstring で「NOT a discharge / load-bearing on <Mathlib
  wall>」を必ず明示

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 起草 (Wave 3 third batch retract 後の honest re-introduction
   track)**: 親 plan `epi-debruijn-integration-plan` Phase C-5 の sub-plan として
   位置付け、Wave 3 third batch (commit `823e150`) で retract された
   `IsDeBruijnTailHyp X Z P` の honest 再導入計画を起草。retract verdict
   `defect(epi-debruijn-tail-vacuous-and-empty)` の 2 重 DEFECT 根拠
   (vacuous-bypass via `Z = 0` + `h_inf : ℝ` で semantic empty) から honest 再
   導入の必須条件として **(a) EReal (or ℝ≥0∞) lift** + **(b) `Z_law : P.map Z =
   gaussianReal 0 1` field 追加** を導出。Phase T-1 (signature 確定、inventory
   待ち) → T-2 (def 書き直し、retract コメント保存) → T-3 (Gaussian discharge
   `h_inf = ⊤`) → T-4 (audit tag) → T-5 (export) → T-V (verify + independent
   audit) の 6 phase 構成、規模 ~80-150 行中央 ~120 行。代替案 3 件併記 (案 1
   EReal、案 2 ℝ≥0∞、案 3 skip)、撤退ライン L-Tail-α/β/γ 3 件設定。**inventory
   待ち** (`epi-debruijn-tail-mathlib-inventory.md` sister agent 並走起草中) で
   案 1 / 案 2 / 案 3 確定は Phase T-1 で行う。

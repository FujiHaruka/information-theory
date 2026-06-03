# Shannon: `IsDeBruijnRegularityHyp` honest refactor サブ計画

> **Parent**: [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md) §「Upstream defects / caveats」
> **Status**: 📋 draft (Wave 3 third batch caveat 対応、未着手)
> **Scope**: docs-only (本 plan); 実装は別 session で `lean-implementer` に dispatch
> **proof-log**: yes (実装 session で `docs/shannon/proof-log-epi-debruijn-regularity-refactor.md`)

## 進捗

- [ ] M0 V2 sub-predicate inventory (mini scope, ~10 行) 📋
- [ ] R-1 `IsDeBruijnRegularityHyp` 構造体 signature 変更 (`density_path` top-level field 化) 📋
- [ ] R-2 `reg_at` を共有 witness 形に書き直し 📋
- [ ] R-3 Gaussian instance (もし存在すれば) 新 signature 追従 📋
- [ ] R-4 Audit tag 整理 (`caveat` 削除、`staged(epi-debruijn-regularity)` のみ残す) 📋
- [ ] R-V verify (`lake env lean ...`) + 独立 honesty audit (`honesty-auditor` subagent) PASS 📋

## ゴール / Approach

### ゴール

`InformationTheory/Shannon/EPIStamDischarge.lean:163-175` の caveat
`@audit:caveat(epi-debruijn-regularity-integrable-deriv-decoupled)` を **構造的に解消** する。
すなわち `IsDeBruijnRegularityHyp X Z P` 構造体を、`integrable_deriv` 単独で
`density_path := fun _ _ ↦ 0` 由来の trivial 充足が **不可能** な signature に refactor する。
構造体は依然 load-bearing (`reg_at` が genuine `HasDerivAt` content を保有)、refactor 後も
`@audit:staged(epi-debruijn-regularity)` は残る。Caveat タグのみ削除。

### Caveat 経緯 (短く)

- Wave 3 third batch (commit `78cf2ec` 前後) で `IsDeBruijnRegularityHyp` の
  `integrable_deriv` field を旧 `Integrable ... (volume.restrict (Set.Ioi 0))` から
  `∀ T > 0, IntervalIntegrable ... volume 0 T` (bounded-T 形) に refactor。
  Gaussian `density_path t := gaussianPDFReal m (v + ⟨t,_⟩)` で genuine 充足可能になり
  `@audit:staged(epi-debruijn-regularity)` で landing。
- 同 Wave 3 third batch の独立 honesty audit が **caveat 追記** (`EPIStamDischarge.lean:163-175`)。
  指摘: `integrable_deriv : ∃ density_path, ...` と `reg_at : ∀ t > 0, IsRegularDeBruijnHypV2 X Z P t`
  (内蔵 `density_t : ℝ → ℝ` 持ち) は **互いに独立な existential**。
  → `integrable_deriv` 単独は `density_path := fun _ _ ↦ 0` で **trivially 充足**
  (`fisherInfoOfDensity 0 = 0` (defeq、`FisherInfoV2.lean:100`)、`intervalIntegrable_const`)。
- **判定は defect ではなく caveat**: `reg_at` 単独で genuine `HasDerivAt` を保有しており、
  predicate 全体は load-bearing 維持。ただし `integrable_deriv` は downstream discharge content
  ゼロ — 「2 field のうち 1 つは飾り」状態。Honest 化は将来作業として明示化。

### Approach (全体戦略)

**狙い**: `density_path` を `IsDeBruijnRegularityHyp` の top-level field に昇格し、
`reg_at` と `integrable_deriv` の両方が **同一 witness** を使う形にする。
こうすれば `density_path := 0` を選んだ瞬間に `reg_at` 側で
`fisherInfoOfDensityReal 0 = 0` が `HasDerivAt (fun s => h(...)) 0 t` を要求し、
Gaussian の真の derivative `1/(2(v+t))` と矛盾する → `density_path := 0` は **`reg_at` 側で fail**。
これが本 plan の honest 化の核心。

**Prior art**: `EPIL3Integration.lean:580-593` の `IsHeatFlowFamilyHyp` は
**同じパターンを既に採用**している (`fPath : ℝ → ℝ → ℝ` を top-level、
`reg_at : ∀ t > 0, HasDerivAt ... ((1/2) * fisherInfoOfDensityReal (fPath t)) t`)。
本 plan は `IsDeBruijnRegularityHyp` を `IsHeatFlowFamilyHyp` 系の paradigm に合わせる。

**Mathlib-shape-driven**: `deBruijn_identity_v2` (`FisherInfoV2DeBruijn.lean:262-272`) の
結論形は `HasDerivAt (...) ((1/2) * fisherInfoOfDensityReal h_reg.density_t) t` で
`h_reg : IsRegularDeBruijnHypV2 X Z P t` から **`density_t` を取り出す**形になっている。
案 1 を取る場合、外から強制する `density_path t` と `IsRegularDeBruijnHypV2` 内蔵
`density_t` の **一致を別途要求** する必要がある (詳細は R-2)。

### 案の比較

| 案 | 内容 | 規模 | Caveat 解消 | Risk |
|---|---|---|---|---|
| **案 1** | `density_path` を `IsDeBruijnRegularityHyp` の top-level field に昇格し、`reg_at` と `integrable_deriv` を同 witness で要求 | ~30-50 行 | ✅ 構造的に解消 | `IsRegularDeBruijnHypV2.density_t` と外部 `density_path t` の一致強制 (中) |
| 案 2 | `IsRegularDeBruijnHypV2` 自体の signature を変更し `density_t` を外挿 parameter に (= `IsRegularDeBruijnHypV2 X Z P t (density : ℝ → ℝ)`) | ~80-120 行 | ✅ 完全 | V2 family lift / Gaussian instance 全件 ripple、`deBruijn_identity_v2` consumer 全件追従 (高) |
| 案 3 | caveat 放置、`@audit:caveat(...)` 維持 | 0 行 | ❌ 残置 | `reg_at` のみで load-bearing 維持なので Phase D 着手 blocker ではない (低)、ただし honesty grade が "load-bearing with caveat" のまま |

**推奨は案 1**。Prior art (`IsHeatFlowFamilyHyp`) と同型で、`IsRegularDeBruijnHypV2` の
public signature を変えないので ripple 最小。R-2 で出る `density_t ≡ density_path t`
一致強制は新 field `density_t_eq : ∀ t > 0, (reg_at t ht).density_t = density_path t`
追加で済む (詳細 R-2)。

撤退ライン L-Reg-α が発火したとき (= R-2 で一致強制が技術的に厄介と判明したとき) は
案 2 にエスカレート、それでも厄介なら案 3 (caveat 許容) で plan ごと撤退。

---

## Phase 詳細

### M0 — V2 sub-predicate inventory (~10 行)

**スコープ**: 案 1 / 案 2 の選択を確定するため、`IsRegularDeBruijnHypV2` の現行 signature
(`FisherInfoV2DeBruijn.lean:236-249`) を 1 ページ要約して plan に追記する。

- [ ] 既存 def の `[...]` typeclass 前提・field 構成を verbatim で抜き出し
- [ ] `density_t` が **structure data field** か **外挿 parameter** か明示
- [ ] V2 family lift 既存 instance (`isRegularDeBruijnHypV2_gaussian_heatFlow` 等) の
  output 形を確認、案 1 / 案 2 で何が破壊されるか列挙

**Done 条件**: 「`density_t` は data field である」が明示的に書かれている。
案 1 vs 案 2 vs 案 3 の選択根拠が plan 内で参照可能。

**現時点での既知 (planner 調査済)**: `density_t : ℝ → ℝ` は **structure data field**
(`FisherInfoV2DeBruijn.lean:243`)。`reg_at` の field 引数として外挿可能な形にはなっていない。
よって案 1 では `density_t ≡ density_path t` の一致を **別 field の方程式** として要求するのが筋。

### R-1 — `IsDeBruijnRegularityHyp` 構造体 signature 変更 (~15-25 行)

**スコープ**: `EPIStamDischarge.lean:176-196` を書き換え、`density_path` を top-level field に昇格。

新 signature のスケッチ:

```lean
structure IsDeBruijnRegularityHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- 共有密度 witness。`fPath t` is intended to be the density of
  `P.map (X + √t · Z)`. 同一 witness が `reg_at` の V2 regularity と
  `integrable_deriv` の interval-integrability を **同時に** 駆動する。 -/
  density_path : ℝ → ℝ → ℝ
  /-- For each `t > 0`, V2 regularity holds with `density_t = density_path t`. -/
  reg_at : ∀ t : ℝ, 0 < t →
    IsRegularDeBruijnHypV2 X Z P t
  /-- `reg_at` の内蔵 `density_t` と top-level `density_path t` の一致強制。
  これがあるため `density_path := fun _ _ ↦ 0` を選ぶと
  `(reg_at t ht).density_t = 0` が成立し、`(reg_at t ht).derivAt_entropy_eq_half_fisher_v2`
  の RHS `(1/2) * fisherInfoOfDensityReal 0 = 0` が Gaussian の真の
  `HasDerivAt` content `1/(2(v+t))` と矛盾する → 退化 witness は **`reg_at` 側で fail**。 -/
  density_t_eq : ∀ t : ℝ, ∀ ht : 0 < t,
    (reg_at t ht).density_t = density_path t
  /-- Bounded-T interval integrability (旧 `integrable_deriv` から
  existential を抜き、`density_path` を共有). -/
  integrable_deriv :
    ∀ T : ℝ, 0 < T →
      IntervalIntegrable
        (fun t : ℝ => (1/2)
          * (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Real.sqrt t * Z ω)) (density_path t)).toReal)
        volume 0 T
```

**変更点 vs 現行**:
- 旧 `integrable_deriv : ∃ density_path : ℝ → ℝ → ℝ, ∀ T > 0, ...` (内側 existential) を
  廃止 → top-level `density_path` field + 内側を `∀ T > 0` のみに簡素化
- 新 field `density_t_eq` で `reg_at` 側 `density_t` と top-level `density_path t` を pin
- `reg_at` の signature は不変 (`∀ t > 0, IsRegularDeBruijnHypV2 X Z P t`)

**Done 条件**:
- `lake env lean InformationTheory/Shannon/EPIStamDischarge.lean` が silent (skeleton 段階)
- `rg "@audit:caveat\(epi-debruijn-regularity-integrable-deriv-decoupled\)" InformationTheory/`
  が 0 hit (caveat docstring 削除)

### R-2 — `reg_at` 連携の確認 (~5-15 行)

**スコープ**: R-1 の新 signature が R-2 自身では追加コードを要求しない (`reg_at` の
signature は不変、`density_t_eq` の追加のみ)。本 phase は **作業ではなく audit step**:
新 signature が caveat を構造的に解消することを Gaussian の trivial-zero 反証で確認する。

**確認手順** (実装 session で実施、本 plan では sketch のみ):

1. `density_path := fun _ _ ↦ 0` を仮置きする (R-V verify の前)
2. `(reg_at t ht).density_t = 0` (= `density_t_eq` 経由) が成立
3. `(reg_at t ht).derivAt_entropy_eq_half_fisher_v2` の RHS は
   `(1/2) * fisherInfoOfDensityReal 0 = 0`
4. Gaussian instance では LHS `HasDerivAt (fun s => h(𝒩(m, v+s))) (1/(2(v+t))) t`、
   `1/(2(v+t)) ≠ 0` for `v + t > 0` で矛盾
5. よって Gaussian で `density_path := 0` を選ぶと構造体は構成不能

これが docstring に caveat 解消の reasoning として書かれていれば honest 化完了。

**Done 条件**: R-1 の docstring に上記 4 行を要約として書き込まれている (caveat タグなし)。

### R-3 — Gaussian instance 追従 (~10-30 行、存在すれば)

**スコープ**: `IsDeBruijnRegularityHyp` の Gaussian discharge instance が **既に存在するか**
を実装 session 冒頭で確認 (現時点で planner では grep で 0 hit、本構造体自体は predicate-only
で `_of_gaussian` instance は未作成の見込み)。存在すれば新 signature に追従、存在しなければ
**R-3 は skip**。

**確認 grep** (実装 session で):
```bash
rg -n "isDeBruijnRegularityHyp_of_gaussian|IsDeBruijnRegularityHyp\.of" InformationTheory/
```

存在した場合の対応:
- 旧 instance の `density_path` 構成式 (Gaussian は
  `fun t => gaussianPDFReal m (v + ⟨t,_⟩)`) を top-level field の値に転記
- `density_t_eq` field の証明は、`IsRegularDeBruijnHypV2` の Gaussian witness
  (`isRegularDeBruijnHypV2_gaussian_heatFlow`、`FisherDeBruijnGaussianWitness.lean:158-166`)
  が同じ density を内蔵していれば `rfl` または短い `simp`

**Done 条件**: 存在する instance がすべて新 signature で silent compile、または存在しない
ことを確認 (skip)。

### R-4 — Audit tag 整理 (~3-5 行)

**スコープ**: `EPIStamDischarge.lean:163-175` の caveat タグを削除し、main docstring の
`@audit:staged(epi-debruijn-regularity)` のみ残す。

- [ ] `@audit:caveat(epi-debruijn-regularity-integrable-deriv-decoupled)` 行 + 解説段落を削除
- [ ] 必要なら main docstring に「2026-05-25+α: caveat resolved by sharing density witness」
  の 1-2 行を追記 (経緯保全)
- [ ] `docs/audit/audit-tags.md` の語彙表に caveat SLUG が登録されていれば削除 (= 個別
  SLUG なので語彙表登録は不要のはず、確認のみ)

**Done 条件**: `rg "epi-debruijn-regularity-integrable-deriv-decoupled" InformationTheory/ docs/`
が 0 hit。

### R-V — verify (~5 行)

**スコープ**: `lake env lean` で touched file + 主要 dependents を確認。

- [ ] `lake env lean InformationTheory/Shannon/EPIStamDischarge.lean` silent
- [ ] `lake env lean InformationTheory/Shannon/EPIL3Integration.lean` silent
  (`IsDeBruijnRegularityHyp` を参照する section header docstring が 532 行付近にあるが、
  実際に predicate を消費する body は現時点で見当たらない — silent compile 期待)
- [ ] `lake env lean InformationTheory/Shannon/FisherDeBruijnGaussianWitness.lean` silent
  (V2 family lift Gaussian witness、`IsRegularDeBruijnHypV2.density_t` の Gaussian 値を提供)
- [ ] 独立 honesty audit (`honesty-auditor` subagent) を起動 → PASS (caveat 解消の reasoning
  が構造的に妥当か、`density_t_eq` が「飾り field」を持ち込んでいないか確認)

**Done 条件**:
- 全 `lake env lean` silent
- 独立 honesty audit verdict が 全 OK or questionable-resolved-inline

---

## 撤退ライン

- **L-Reg-α** (R-2 段階で発火): `IsRegularDeBruijnHypV2` の `density_t` が data field である
  ことに起因し、`density_t_eq` 経由の一致強制が **R-2 で技術的に厄介** と判明
  (例: `reg_at` の type が `IsRegularDeBruijnHypV2 X Z P t` で `density_t` は instance ごと
  独立に選ばれているため、外から `density_t = density_path t` を要求すると `IsRegularDeBruijnHypV2`
  の universal interface を壊してしまう)。→ **案 2 へエスカレート** (`IsRegularDeBruijnHypV2`
  の signature を `density_t` を外挿 parameter にする refactor)、それも厄介なら **案 3** (caveat
  許容、本 plan 撤退) で plan body を `RETIRED — caveat accepted` に書き換え。
- **L-Reg-β** (R-V 段階で発火): 下流 consumer の ripple が想定外に巨大 (新 `density_t_eq`
  field が `EPIL3Integration.lean` / `FisherDeBruijnGaussianWitness.lean` で
  `density_path` を pin する要求を満たせず連鎖破綻)。→ **案 3** (caveat 許容)、`R-1` を revert。

## Done 条件 (本 plan 全体)

- 新 signature で `integrable_deriv` の trivial discharge (`density_path := fun _ _ ↦ 0`) が
  **structurally 不可能** (`density_path = 0` は `density_t_eq` 経由で `reg_at` 側の
  `derivAt_entropy_eq_half_fisher_v2` の RHS を `0` に固定し、Gaussian の真の derivative と
  矛盾するため `reg_at` 全体が構成不能)
- `@audit:caveat(epi-debruijn-regularity-integrable-deriv-decoupled)` 削除済
- `@audit:staged(epi-debruijn-regularity)` のみ残存 (predicate 全体は依然 load-bearing)
- `lake env lean InformationTheory/Shannon/EPIStamDischarge.lean` silent
- 既存 Gaussian discharge / 下流 consumer 全件 silent (`EPIL3Integration.lean`,
  `FisherDeBruijnGaussianWitness.lean`)
- 独立 honesty audit (`honesty-auditor` subagent) verdict が 全 OK

## 参考 file

- `InformationTheory/Shannon/EPIStamDischarge.lean:176-196` — refactor 対象の現行 structure
- `InformationTheory/Shannon/EPIStamDischarge.lean:163-175` — caveat docstring (R-4 で削除)
- `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:236-249` — `IsRegularDeBruijnHypV2` (V2 sub-predicate)
- `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:262-272` — `deBruijn_identity_v2` (V2 sub-predicate consumer)
- `InformationTheory/Shannon/FisherDeBruijnGaussianWitness.lean:158-166` — `isRegularDeBruijnHypV2_gaussian_heatFlow` (V2 Gaussian witness)
- `InformationTheory/Shannon/EPIL3Integration.lean:580-593` — `IsHeatFlowFamilyHyp` (案 1 の prior art、同型 paradigm)
- `InformationTheory/Shannon/EPIL3Integration.lean:520-561` — 親 plan の "Upstream defects" コメント、本 caveat 含む現状記述
- `docs/shannon/epi-debruijn-integration-plan.md` — 親 plan (本 refactor は親 plan の honest 化作業の延長)
- `docs/audit/audit-tags.md` — caveat タグ語彙

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 例:
1. **R-2 で L-Reg-α 発火**: `density_t_eq` の追加が `IsRegularDeBruijnHypV2` の universal
   interface (instance ごと `density_t` 自由選択) と衝突。案 2 にエスカレートを判断。
2. ...
-->
